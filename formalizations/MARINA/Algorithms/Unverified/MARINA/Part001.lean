import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SOptLib.Model.BlockSampling
import SOptLib.Model.BlockSampling.infinitePi_prefix_current_map_eq_prod
import SOptLib.Model.Iterates
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Model.ParameterChoices.PositiveRealParameter
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Objective.finiteAverageGradient_lipschitz_of_average_sq_smoothness
import SOptLib.Glue.Algebra.inner_neg_smul_eq_neg_half_eta_norm_sq_sub_step_sq_add_error_sq

/-!
# MARINA family: source-facing object model

This file models Algorithms 1--4 of Gorbunov--Burlachenko--Li--Richtárik.
The estimator and iterate processes below are generated definitions, rather
than witness processes constrained by theorem hypotheses.
-/

open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace MARINA

/-- A source-level positive finite count (dimension, workers, or batch size). -/
abbrev Count := {q : ℕ // 0 < q}

/-- The paper's Euclidean parameter space `ℝ^d`. -/
abbrev Point (d : Count) := EuclideanSpace ℝ (Fin d.1)

abbrev Worker (n : Count) := Fin n.1
abbrev Component (m : Count) := Fin m.1

/-- The canonical gradient is measurable.  Mathlib's totalized `fderiv` is
measurable, and the Riesz identification from the dual to the Euclidean space
is continuous. -/
@[fun_prop] theorem measurable_gradient {d : Count} (f : Point d → ℝ) :
    Measurable (gradient f) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

/-- A strictly positive stepsize.  The paper writes an unrestricted input
`stepsize γ`, but every convergence conclusion divides by `γ K`.  The source
does not state `0 < γ`; this subtype is the explicit B-track domain correction
which prevents Lean's `γ = 0` division convention from changing those bounds. -/
abbrev PositiveStepsize := SOptLib.PositiveRealParameter

/-- Positive PŁ parameter used by every theorem whose rate divides by `μ`.
The paper calls `μ` the PŁ parameter but does not separately print `0 < μ`;
this is the explicit B-track domain boundary preventing totalized division by
zero in the PŁ complexity formulas. -/
abbrev PositivePLParameter := SOptLib.PositiveRealParameter

/-- The finite uniform average used for workers, components, and minibatches. -/
noncomputable def average {ι : Type*} [Fintype ι]
    {V : Type*} [AddCommMonoid V] [Module ℝ V] (v : ι → V) : V :=
  SOptLib.finiteUniformAverage v

/-- `book/MARINA/MARINA.json#/setup/problem`:
"`min_{x∈ℝ^d} f(x)=n⁻¹∑ᵢ f_i(x)`".  The fields are exactly the workers'
local losses; the global objective is derived below. -/
structure LocalProblem (d n : Count) where
  localLoss : Worker n → Point d → ℝ

/-- `book/MARINA/MARINA.json#/setup/definitions/0`:
"`f(x)=n⁻¹∑ᵢ f_i(x)`". -/
noncomputable def globalObjective {d n : Count} (P : LocalProblem d n) : Point d → ℝ :=
  fun x => average (fun i : Worker n => P.localLoss i x)

/-- `book/MARINA/MARINA.json#/assumptions/1`:
"`‖∇f_i(x)-∇f_i(y)‖≤L_i‖x-y‖`".  This is the canonical gradient of a
worker's local loss. -/
noncomputable def localGradient {d n : Count} (P : LocalProblem d n)
    (i : Worker n) (x : Point d) : Point d :=
  gradient (P.localLoss i) x

@[fun_prop] theorem measurable_localGradient {d n : Count}
    (P : LocalProblem d n) (i : Worker n) : Measurable (localGradient P i) := by
  unfold localGradient
  exact measurable_gradient _

/-- `book/MARINA/MARINA.json#/assumptions/3`:
"`‖∇f(x)‖²≥2μ(f(x)-f(x*))`".  This is the canonical gradient of the
global objective from `book/MARINA/MARINA.json#/setup/problem`. -/
noncomputable def globalGradient {d n : Count} (P : LocalProblem d n)
    (x : Point d) : Point d :=
  gradient (globalObjective P) x

/-- `book/MARINA/MARINA.json#/setup/definitions/0`:
"`f(x)=n⁻¹∑ᵢ f_i(x)`".  This internal averaging object is the average of
the canonical local gradients; its equality with `globalGradient` is proved
below rather than assumed. -/
noncomputable def averageLocalGradient {d n : Count} (P : LocalProblem d n)
    (x : Point d) : Point d :=
  average (fun i : Worker n => localGradient P i x)

@[simp] theorem globalObjective_eq_average {d n : Count} (P : LocalProblem d n)
    (x : Point d) :
    globalObjective P x = average (fun i : Worker n => P.localLoss i x) := by
  rfl

/-- Eq. (1) commutes with differentiation under the paper's smoothness assumption. -/
theorem globalGradient_eq_averageLocalGradient {d n : Count} (P : LocalProblem d n)
    (hDiff : ∀ i, Differentiable ℝ (P.localLoss i)) (x : Point d) :
    globalGradient P x = averageLocalGradient P x := by
  classical
  unfold globalGradient averageLocalGradient average localGradient
  have hObj :
      globalObjective P =
        SOptLib.finiteUniformAverage (fun i : Worker n => P.localLoss i) := by
    funext z
    simp [globalObjective, average, SOptLib.finiteUniformAverage]
  rw [hObj]
  have hF : ∀ i : Worker n,
      HasGradientAt (P.localLoss i) (gradient (P.localLoss i) x) x := by
    intro i
    exact (hDiff i x).hasGradientAt
  have hsum : HasFDerivAt
      (fun z : Point d =>
        Finset.sum Finset.univ (fun i : Worker n => P.localLoss i z))
      (Finset.sum Finset.univ
        (fun i : Worker n =>
          InnerProductSpace.toDual ℝ (Point d) (gradient (P.localLoss i) x))) x := by
    refine HasFDerivAt.fun_sum ?_
    intro i _hi
    exact (hF i).hasFDerivAt
  have hscaled := hsum.const_smul ((Fintype.card (Worker n) : ℝ)⁻¹)
  have hAvg :
      HasGradientAt
        (SOptLib.finiteUniformAverage (fun i : Worker n => P.localLoss i))
        (SOptLib.finiteUniformAverage
          (fun i : Worker n => gradient (P.localLoss i) x)) x := by
    rw [show SOptLib.finiteUniformAverage (fun i : Worker n => P.localLoss i) =
        (fun z : Point d => (Fintype.card (Worker n) : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : Worker n => P.localLoss i z)) by
      funext z
      simp [SOptLib.finiteUniformAverage]]
    simpa [SOptLib.finiteUniformAverage, map_smul, map_sum] using
      hscaled.hasGradientAt
  exact hAvg.gradient

/-- `book/MARINA/MARINA.json#/assumptions/0`:
"`∃ f_*∈ℝ, f(x)≥f_* for all x∈ℝ^d`".  Assumption 1.1 is kept as a
predicate on the canonical global objective. -/
def HasUniformLowerBound {d n : Count} (P : LocalProblem d n) (fStar : ℝ) : Prop :=
  ∀ x, fStar ≤ globalObjective P x

/-- `book/MARINA/MARINA.json#/assumptions/1`:
"`‖∇f_i(x)-∇f_i(y)‖≤L_i‖x-y‖, ∀x,y∈ℝ^d, ∀i∈[n]`".
Assumption 1.2; differentiability is made explicit as part of `L`-smoothness. -/
def IsLocallySmooth {d n : Count} (P : LocalProblem d n)
    (L : Worker n → ℝ) : Prop :=
  (∀ i, Differentiable ℝ (P.localLoss i)) ∧
    ∀ i x y, ‖localGradient P i x - localGradient P i y‖ ≤ L i * ‖x - y‖

/-- `book/MARINA/MARINA.json#/assumptions/3`:
"`x^*=argmin_x f(x)`".  This is the optimizer part of Assumption 2.1. -/
def IsGlobalMinimizer {d n : Count} (P : LocalProblem d n) (xStar : Point d) : Prop :=
  ∀ x, globalObjective P xStar ≤ globalObjective P x

/-- `book/MARINA/MARINA.json#/assumptions/3`:
"`‖∇f(x)‖²≥2μ(f(x)-f(x*)), x*=argmin_x f(x)`".
The optimizer and its attainment property are retained instead of replacing
`f(x*)` by an unrelated scalar lower bound. -/
def SatisfiesPL {d n : Count} (P : LocalProblem d n) (μ : PositivePLParameter)
    (xStar : Point d) : Prop :=
  IsGlobalMinimizer P xStar ∧
    ∀ x, 2 * μ * (globalObjective P x - globalObjective P xStar) ≤
      ‖globalGradient P x‖ ^ 2

/-- A bundled jointly measurable curried kernel.  This is the measurable-space
analogue of a bundled continuous map: it prevents stochastic algorithms from
storing a plain function whose composition with an adapted random query need
not be measurable. -/
structure JointlyMeasurableKernel (X S Y : Type*)
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace Y] where
  toFun : X → S → Y
  measurable_uncurry : Measurable (Function.uncurry toFun)

instance {X S Y : Type*} [MeasurableSpace X] [MeasurableSpace S]
    [MeasurableSpace Y] : CoeFun (JointlyMeasurableKernel X S Y) (fun _ => X → S → Y) :=
  ⟨JointlyMeasurableKernel.toFun⟩

/-- A stochastic quantization kernel. Randomness is an explicit argument, so
each worker and round can receive a distinct compression sample.  The paper's
random operator `Q(x)` is represented by its jointly measurable evaluation
kernel, which is the structural well-posedness needed for adaptive inputs. -/
structure Quantizer (d : Count) (Ξ : Type*) [MeasurableSpace Ξ] where
  apply : JointlyMeasurableKernel (Point d) Ξ (Point d)
  law : Measure Ξ
  law_isProbability : IsProbabilityMeasure law

@[fun_prop] theorem Quantizer.measurable_apply_uncurry
    {d : Count} {Ξ : Type*} [MeasurableSpace Ξ] (Q : Quantizer d Ξ) :
    Measurable (fun p : Point d × Ξ => Q.apply p.1 p.2) :=
  Q.apply.measurable_uncurry

/-- `book/MARINA/MARINA.json#/assumptions/2`:
"`E[Q(x)]=x, E[‖Q(x)-x‖²]≤ω‖x‖²`".  Integrability is bundled into
the moment assertion so the displayed relations cannot hold through the
totalized Bochner-integral fallback. -/
def IsUnbiasedQuantizer {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ) (ω : ℝ) : Prop :=
  0 < ω ∧ ∀ v : Point d,
    Integrable (Q.apply v) Q.law ∧
    Integrable (fun ξ => ‖Q.apply v ξ - v‖ ^ 2) Q.law ∧
    (∫ ξ, Q.apply v ξ ∂Q.law) = v ∧
    (∫ ξ, ‖Q.apply v ξ - v‖ ^ 2 ∂Q.law) ≤ ω * ‖v‖ ^ 2

/-- Nonfallback first-moment bridge derived from Definition 1.1. -/
theorem quantizer_integrable {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Quantizer d Ξ} {ω : ℝ} (hQ : IsUnbiasedQuantizer Q ω)
    (v : Point d) : Integrable (Q.apply v) Q.law :=
  (hQ.2 v).1

/-- Nonfallback second-moment bridge derived from Definition 1.1. -/
theorem quantizer_error_sq_integrable {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Quantizer d Ξ} {ω : ℝ} (hQ : IsUnbiasedQuantizer Q ω)
    (v : Point d) : Integrable (fun ξ => ‖Q.apply v ξ - v‖ ^ 2) Q.law :=
  (hQ.2 v).2.1

/-- `book/MARINA/MARINA.json#/setup/definitions/4`:
"`ζ_Q=sup_{x∈ℝ^d} E[‖Q(x)‖_0]`".  This is the pointwise support count
`‖Q(x)‖₀` appearing inside Definition 1.1's expected density. -/
noncomputable def quantizerNonzeroCount {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ) (v : Point d) (ξ : Ξ) : ℝ :=
  ((Finset.univ.filter fun j : Fin d.1 => Q.apply v ξ j ≠ 0).card : ℝ)

/-- `book/MARINA/MARINA.json#/setup/definitions/4`:
"`ζ_Q=sup_{x∈ℝ^d} E[‖Q(x)‖_0]`". -/
noncomputable def expectedDensity {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ) : ℝ :=
  sSup (Set.range fun v : Point d => ∫ ξ, quantizerNonzeroCount Q v ξ ∂Q.law)

/-- `book/MARINA/MARINA.json#/key_lemmas/9`, Definition 1.1.  Stable
registered-name theorem for the canonical expected-density object. -/
theorem ExpectedDensity_Definition {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ) :
    expectedDensity Q =
      sSup (Set.range fun v : Point d =>
        ∫ ξ, quantizerNonzeroCount Q v ξ ∂Q.law) := by
  rfl

/-- The finite-density expectation has nonfallback semantics.  This is a
derived semantic obligation, not an extra paper assumption. -/
def ExpectedDensitySemantics {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ) : Prop :=
  ∀ v : Point d, Integrable (quantizerNonzeroCount Q v) Q.law

/-- Definition 1.1's density expectation is well-defined for an unbiased
quantizer; this is derived from its strongly measurable first moment and the
finite-dimensional coordinate support count. -/
theorem expectedDensitySemantics_of_unbiased {d : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] {Q : Quantizer d Ξ} {ω : ℝ}
    (hQ : IsUnbiasedQuantizer Q ω) : ExpectedDensitySemantics Q := by
  intro v
  letI : IsProbabilityMeasure Q.law := Q.law_isProbability
  apply integrable_of_measurable_bounded_real (C := (d.1 : ℝ))
  · rw [show quantizerNonzeroCount Q v =
        fun ξ => ∑ j : Fin d.1, if Q.apply v ξ j ≠ 0 then (1 : ℝ) else 0 by
      funext ξ
      unfold quantizerNonzeroCount
      exact Finset.natCast_card_filter
        (fun j : Fin d.1 => Q.apply v ξ j ≠ 0) Finset.univ]
    have happly : Measurable (fun ξ => Q.apply v ξ) := by
      exact Q.apply.measurable_uncurry.comp measurable_prodMk_left
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun ξ => Q.apply v ξ j) :=
      (EuclideanSpace.proj j).continuous.measurable.comp happly
    have hzero : MeasurableSet {ξ | Q.apply v ξ j = 0} :=
      hj (measurableSet_singleton 0)
    exact Measurable.ite hzero.compl measurable_const measurable_const
  · intro ξ
    have hcard :
        (Finset.univ.filter fun j : Fin d.1 => Q.apply v ξ j ≠ 0).card ≤ d.1 := by
      simpa using
        (Finset.card_filter_le Finset.univ
          (fun j : Fin d.1 => Q.apply v ξ j ≠ 0))
    have hnonneg : 0 ≤ quantizerNonzeroCount Q v ξ := by
      unfold quantizerNonzeroCount
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    unfold quantizerNonzeroCount
    exact_mod_cast hcard

/-- `book/MARINA/MARINA.json#/setup/definitions/3`:
"`Δ_i^k=∇f_i(x^{k+1})-∇f_i(x^k)`". -/
noncomputable def localGradientDifference {d n : Count} (P : LocalProblem d n)
    (i : Worker n) (xNext x : Point d) : Point d :=
  localGradient P i xNext - localGradient P i x

/-- Mean-square aggregate used for both `L²=n⁻¹∑Lᵢ²` and
`ℒ²=n⁻¹∑ℒᵢ²`; see `book/MARINA/MARINA.json#/setup/definitions/5`. -/
noncomputable def meanSquare {n : Count} (c : Worker n → ℝ) : ℝ :=
  average (fun i : Worker n => (c i) ^ 2)

/-- Canonical nonnegative representative of the paper's aggregate constant
`L` (or `ℒ`) from its defining squared average. -/
noncomputable def rootMeanSquare {n : Count} (c : Worker n → ℝ) : ℝ :=
  Real.sqrt (meanSquare c)

/-- `book/MARINA/MARINA.json#/setup/definitions/6`:
"`σ²=n⁻¹∑σ_i²`". -/
noncomputable def varianceAggregateSq {n : Count} (σ : Worker n → ℝ) : ℝ :=
  meanSquare σ

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0` and `/steps/2`:
"`x^{k+1}=x^k-γg^k`" and "`g^{k+1}=n⁻¹∑ᵢg_i^{k+1}`".  This is the
minimal recursive state carrying those two paper quantities. -/
structure State (d : Count) where
  x : Point d
  g : Point d

/-- The recursive state carries exactly the measurable pair `(x,g)`. -/
def stateEquivPair (d : Count) : State d ≃ Point d × Point d where
  toFun s := (s.x, s.g)
  invFun p := ⟨p.1, p.2⟩
  left_inv s := by cases s; rfl
  right_inv p := by cases p; rfl

instance stateMeasurableSpace (d : Count) : MeasurableSpace (State d) :=
  MeasurableSpace.comap (stateEquivPair d) inferInstance

@[fun_prop] theorem measurable_stateEquivPair (d : Count) :
    Measurable (stateEquivPair d) := by
  rw [measurable_iff_comap_le]
  rfl

@[fun_prop] theorem measurable_stateEquivPair_symm (d : Count) :
    Measurable (stateEquivPair d).symm := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (⇑(stateEquivPair d).symm)
      (MeasurableSpace.comap (⇑(stateEquivPair d))
        (inferInstance : MeasurableSpace (Point d × Point d))) ≤ _
  rw [MeasurableSpace.comap_comp]
  have hfun : (⇑(stateEquivPair d) ∘ ⇑(stateEquivPair d).symm) =
      (id : Point d × Point d → Point d × Point d) := by
    funext p
    exact (stateEquivPair d).apply_symm_apply p
  rw [hfun, MeasurableSpace.comap_id]

@[fun_prop] theorem measurable_state_x (d : Count) :
    Measurable (fun s : State d => s.x) :=
  measurable_fst.comp (measurable_stateEquivPair d)

@[fun_prop] theorem measurable_state_g (d : Count) :
    Measurable (fun s : State d => s.g) :=
  measurable_snd.comp (measurable_stateEquivPair d)

@[fun_prop] theorem measurable_state_mk (d : Count) :
    Measurable (fun p : Point d × Point d => (State.mk p.1 p.2 : State d)) :=
  measurable_stateEquivPair_symm d

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0`:
"`x^{k+1}=x^k-γg^k`". -/
noncomputable def primalStep {d : Count} (γ : ℝ) (s : State d) : Point d :=
  SOptLib.gradientStep γ s.x s.g

@[simp] theorem primalStep_eq {d : Count} (γ : ℝ) (s : State d) :
    primalStep γ s = s.x - γ • s.g := by
  rfl

@[fun_prop] theorem measurable_primalStep {d : Count} (γ : ℝ) :
    Measurable (primalStep (d := d) γ) := by
  unfold primalStep SOptLib.gradientStep
  exact (measurable_state_x d).sub ((measurable_state_g d).const_smul γ)

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/0`:
"`p∈(0,1]`". -/
def RefreshProbabilityAdmissible (p : ℝ) : Prop := 0 < p ∧ p ≤ 1

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/0` and
`#/algorithm_spec/variants/0`: "`p∈(0,1]`" and MARINA uses full local-gradient
refreshes with quantized full-gradient differences.  `stepSize`, `problem`,
and `quantizer` are the remaining source inputs shared with PP-MARINA. -/
structure BasicData (d n : Count) (Ξ : Type*) [MeasurableSpace Ξ] where
  problem : LocalProblem d n
  quantizer : Quantizer d Ξ
  stepSize : PositiveStepsize
  refreshProbability : ℝ
  refresh_admissible : RefreshProbabilityAdmissible refreshProbability

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0`:
"`c_k∼Be(p)`".  This is the canonical Bernoulli law, rather than a free
Boolean driver coordinate. -/
noncomputable def refreshLaw (p : ℝ) (hp : RefreshProbabilityAdmissible p) :
    Measure Bool :=
  (PMF.bernoulli ⟨p, le_of_lt hp.1⟩ (by exact_mod_cast hp.2)).toMeasure

/-- The canonical independent workerwise compressor-sample law. -/
noncomputable def workerCompressionLaw {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (Q : Quantizer d Ξ) : Measure (Worker n → Ξ) :=
  Measure.infinitePi (fun _ : Worker n => Q.law)

/-- Every worker coordinate of the canonical compression product has the
quantizer's one-sample law. -/
theorem workerCompressionLaw_component_marginal {d n : Count}
    {Ξ : Type*} [MeasurableSpace Ξ] (Q : Quantizer d Ξ) (i : Worker n) :
    Measure.map (fun samples : Worker n → Ξ => samples i)
      (workerCompressionLaw (n := n) Q) = Q.law := by
  letI : IsProbabilityMeasure Q.law := Q.law_isProbability
  unfold workerCompressionLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun _ : Worker n => Q.law) i)

/-- Internal recursion carrier for the source coordinates cited at
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/1`,
and `#/algorithm_spec/steps/2`; it adds no paper datum. -/
structure BasicDriver (n : Count) (Ξ : Type*) where
  refresh : Bool
  compressionSample : Worker n → Ξ

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/1`, and `#/algorithm_spec/steps/2`:
the Bernoulli refresh coin and worker compressor samples realizing the quoted
MARINA worker-update and aggregation formulas. -/
abbrev BasicRoundNoise (n : Count) (Ξ : Type*) := Bool × (Worker n → Ξ)

/-- Canonical probability realization of
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/1`,
and `#/algorithm_spec/steps/2`: the quoted Bernoulli
refresh and worker updates use distinct independent coordinates. -/
noncomputable def basicRoundLaw {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) : Measure (BasicRoundNoise n Ξ) :=
  (refreshLaw A.refreshProbability A.refresh_admissible).prod
    (workerCompressionLaw A.quantizer)

/-- Path-law realization of the repeated rounds in
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/1`,
and `#/algorithm_spec/steps/2`; iid repetition is
realization machinery for the source's repeated sampling instructions. -/
noncomputable def basicPathLaw {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) : Measure (ℕ → BasicRoundNoise n Ξ) :=
  SOptLib.iidStreamLaw (basicRoundLaw A)

/-- Every time coordinate of the canonical iid path has the one-round law. -/
theorem basicPathLaw_round_marginal {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (k : ℕ) :
    Measure.map (fun path : ℕ → BasicRoundNoise n Ξ => path k)
      (basicPathLaw A) = basicRoundLaw A := by
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  unfold basicPathLaw SOptLib.iidStreamLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun _ : ℕ => basicRoundLaw A) k)

/-- Internal conversion from canonical source noise to the pathwise recursion carrier. -/
def basicDriverOfNoise {n : Count} {Ξ : Type*}
    (z : BasicRoundNoise n Ξ) : BasicDriver n Ξ :=
  { refresh := z.1, compressionSample := z.2 }

/-- Bernoulli marginal of every Algorithm 1 refresh coordinate. -/
theorem basicPathLaw_refresh_marginal {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (k : ℕ) :
    Measure.map (fun path : ℕ → BasicRoundNoise n Ξ => (path k).1)
      (basicPathLaw A) = refreshLaw A.refreshProbability A.refresh_admissible := by
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  calc
    Measure.map (fun path : ℕ → BasicRoundNoise n Ξ => (path k).1)
        (basicPathLaw A) =
        Measure.map Prod.fst
          (Measure.map (fun path : ℕ → BasicRoundNoise n Ξ => path k)
            (basicPathLaw A)) := by
      rw [MeasureTheory.Measure.map_map measurable_fst (measurable_pi_apply k)]
      rfl
    _ = Measure.map Prod.fst (basicRoundLaw A) := by
      rw [basicPathLaw_round_marginal A k]
    _ = refreshLaw A.refreshProbability A.refresh_admissible := by
      simp [basicRoundLaw]

/-- Compressor marginal of every worker and round in Algorithm 1. -/
theorem basicPathLaw_compression_marginal {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (k : ℕ) (i : Worker n) :
    Measure.map (fun path : ℕ → BasicRoundNoise n Ξ => (path k).2 i)
      (basicPathLaw A) = A.quantizer.law := by
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  have hsnd :
      Measure.map Prod.snd (basicRoundLaw A) =
        workerCompressionLaw (n := n) A.quantizer := by
    unfold basicRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map (fun path : ℕ → BasicRoundNoise n Ξ => (path k).2 i)
        (basicPathLaw A) =
        Measure.map (fun z : BasicRoundNoise n Ξ => z.2 i)
          (Measure.map (fun path : ℕ → BasicRoundNoise n Ξ => path k)
            (basicPathLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          ((measurable_pi_apply i).comp measurable_snd)
          (measurable_pi_apply k) (μ := basicPathLaw A)).symm
    _ = Measure.map (fun z : BasicRoundNoise n Ξ => z.2 i)
        (basicRoundLaw A) := by
      rw [basicPathLaw_round_marginal A k]
    _ = Measure.map (fun samples : Worker n → Ξ => samples i)
        (Measure.map Prod.snd (basicRoundLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map (measurable_pi_apply i) measurable_snd
          (μ := basicRoundLaw A)).symm
    _ = Measure.map (fun samples : Worker n → Ξ => samples i)
        (workerCompressionLaw (n := n) A.quantizer) := by
      rw [hsnd]
    _ = A.quantizer.law :=
      workerCompressionLaw_component_marginal A.quantizer i

/-- The refresh and worker compressor coordinates are independent consequences
of the canonical product law, not algorithm inputs. -/
theorem basicRoundLaw_independent {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) :
    ProbabilityTheory.IndepFun Prod.fst Prod.snd (basicRoundLaw A) := by
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  unfold basicRoundLaw
  exact ProbabilityTheory.indepFun_prod measurable_id measurable_id

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/1`:
"`g_i^{k+1}=∇f_i(x^{k+1})` if `c_k=1`, otherwise
`g^k+Q(∇f_i(x^{k+1})-∇f_i(x^k))`". -/
noncomputable def marinaWorkerEstimator {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (z : BasicDriver n Ξ) (s : State d)
    (i : Worker n) : Point d :=
  let xNext := primalStep A.stepSize s
  if z.refresh then
    localGradient A.problem i xNext
  else
    s.g + A.quantizer.apply
      (localGradient A.problem i xNext - localGradient A.problem i s.x)
      (z.compressionSample i)

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0` and
`#/algorithm_spec/steps/2`: combines
"`x^{k+1}=x^k-γg^k`" with "`g^{k+1}=n⁻¹∑ᵢg_i^{k+1}`". -/
noncomputable def marinaStep {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (z : BasicDriver n Ξ) (s : State d) : State d :=
  let xNext := primalStep A.stepSize s
  { x := xNext
    g := average (marinaWorkerEstimator A z s) }

/-- `book/MARINA/MARINA.json#/algorithm_spec/initialization/facts/0`:
"`g^0=∇f(x^0)`". -/
noncomputable def marinaInitialState {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) : State d :=
  { x := x0, g := globalGradient A.problem x0 }

/-- Generated recursion for `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/1`, and `#/algorithm_spec/steps/2`
from the exact initialization quoted at `#/algorithm_spec/initialization/facts/0`;
no iterate is supplied as a witness. -/
noncomputable def marinaRun {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) :
    ℕ → (ℕ → BasicDriver n Ξ) → State d :=
  SOptLib.recursiveIterateProcess (marinaInitialState A x0)
    (fun k s path => marinaStep A (path k) s)

/-- Random-process realization of `book/MARINA/MARINA.json#/algorithm_spec/variants/0`
and `#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/1`, and
`#/algorithm_spec/steps/2`.  The pathwise recursion `marinaRun` is
retained only as its deterministic realization. -/
noncomputable def marinaProcess {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (x0 : Point d) :
    ℕ → (ℕ → BasicRoundNoise n Ξ) → State d :=
  fun k path => marinaRun A x0 k (fun t => basicDriverOfNoise (path t))

@[simp] theorem marinaRun_zero {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (path : ℕ → BasicDriver n Ξ) :
    marinaRun A x0 0 path = marinaInitialState A x0 := by
  rfl

@[simp] theorem marinaRun_succ {d n : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (k : ℕ)
    (path : ℕ → BasicDriver n Ξ) :
    marinaRun A x0 (k + 1) path = marinaStep A (path k) (marinaRun A x0 k path) := by
  rfl

/-! ## Finite-sum VR-MARINA (Algorithm 2) -/

/-- `book/MARINA/MARINA.json#/setup/definitions/1`:
"`f_i(x)=m⁻¹∑_j f_{ij}(x)`".  Only component losses are primitive; local
losses are derived below. -/
structure FiniteSumProblem (d n m : Count) where
  componentLoss : Worker n → Component m → Point d → ℝ

/-- `book/MARINA/MARINA.json#/setup/definitions/1`:
"`f_i(x)=m⁻¹∑_j f_{ij}(x)`". -/
noncomputable def finiteSumLocalProblem {d n m : Count}
    (P : FiniteSumProblem d n m) : LocalProblem d n where
  localLoss i x := average (fun j : Component m => P.componentLoss i j x)

/-- `book/MARINA/MARINA.json#/assumptions/4`:
"`∇f_{ij}(x^{k+1})-∇f_{ij}(x^k)`".  This is the canonical gradient of
the component loss `f_{ij}` from `book/MARINA/MARINA.json#/setup/definitions/1`. -/
noncomputable def componentGradient {d n m : Count}
    (P : FiniteSumProblem d n m) (i : Worker n) (j : Component m)
    (x : Point d) : Point d :=
  gradient (P.componentLoss i j) x

@[fun_prop] theorem measurable_componentGradient {d n m : Count}
    (P : FiniteSumProblem d n m) (i : Worker n) (j : Component m) :
    Measurable (componentGradient P i j) := by
  unfold componentGradient
  exact measurable_gradient _

/-- `book/MARINA/MARINA.json#/algorithm_spec/variants/1` and
`#/algorithm_spec/parameters/0` and `#/algorithm_spec/parameters/1`:
finite-sum VR-MARINA uses full local
refreshes, quantized component-minibatch differences, `p∈(0,1]`, and
"`|I⁰_{i,k}|=b⁰`". -/
structure FiniteSumData (d n m : Count) (Ξ : Type*) [MeasurableSpace Ξ] where
  problem : FiniteSumProblem d n m
  quantizer : Quantizer d Ξ
  stepSize : PositiveStepsize
  refreshProbability : ℝ
  refresh_admissible : RefreshProbabilityAdmissible refreshProbability

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/1`:
"`|I⁰_{i,k}|=b⁰`".  An enumerated batch also represents the iid-uniform
with-replacement example stated after Assumption 3.1; repetitions therefore
cannot be excluded at the common source boundary. -/
abbrev FiniteSumBatch (n m b0 : Count) :=
  Worker n → Fin b0.1 → Component m

/-- One worker's ordered realization of the size-`b⁰` minibatch in Algorithm 2. -/
abbrev FiniteSumWorkerBatch (m b0 : Count) :=
  Fin b0.1 → Component m

/-- A possibly time-inhomogeneous family of worker minibatch laws for
Algorithm 2.  The worker index is outside `Measure`: the paper's independent
worker draws are assembled below with `Measure.infinitePi`.  Assumption 3.1 is
stated separately for every `k`, so no stationary law is imposed across rounds. -/
abbrev FiniteSumBatchLaw (n m b0 : Count) :=
  ℕ → Worker n → Measure (FiniteSumWorkerBatch m b0)

/-- The joint worker minibatch law at round `k`.  This is the canonical product
realization of the source proof's statement that the worker minibatch/quantizer
outputs are independent for fixed iterates. -/
noncomputable def finiteSumBatchJointLaw {n m b0 : Count}
    (batchLaw : FiniteSumBatchLaw n m b0) (k : ℕ) :
    Measure (FiniteSumBatch n m b0) :=
  Measure.infinitePi (batchLaw k)

/-- Probability-law boundary for each worker's Assumption 3.1 minibatch law.
Injectivity is deliberately not required: the source explicitly lists `b⁰`
iid uniform draws as an example.  Workerwise independence is structural in
`finiteSumBatchJointLaw`, rather than stored as an additional proposition. -/
def FiniteSumBatchLawAdmissible {n m b0 : Count}
    (batchLaw : FiniteSumBatchLaw n m b0) : Prop :=
  ∀ k i, IsProbabilityMeasure (batchLaw k i)

/-- The worker product assembled from admissible minibatch laws is itself a
probability measure. -/
theorem finiteSumBatchJointLaw_isProbability {n m b0 : Count}
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw k) := by
  letI (i : Worker n) : IsProbabilityMeasure (batchLaw k i) := hBatchLaw k i
  unfold finiteSumBatchJointLaw
  infer_instance

/-- Each worker projection of the canonical joint minibatch law recovers that
worker's declared Assumption 3.1 law. -/
theorem finiteSumBatchJointLaw_worker_marginal {n m b0 : Count}
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) (i : Worker n) :
    Measure.map (fun batch : FiniteSumBatch n m b0 => batch i)
      (finiteSumBatchJointLaw batchLaw k) = batchLaw k i := by
  letI (j : Worker n) : IsProbabilityMeasure (batchLaw k j) := hBatchLaw k j
  unfold finiteSumBatchJointLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval (μ := batchLaw k) i)

/-- Internal pathwise carrier for the coordinates in
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/3`,
and `#/algorithm_spec/steps/5`; it is not extra source data. -/
structure FiniteSumDriver (n m b0 : Count) (Ξ : Type*) where
  refresh : Bool
  batch : FiniteSumBatch n m b0
  compressionSample : Worker n → Ξ

/-- Uniform component law used by the within-worker finite-sum minibatches. -/
noncomputable def componentLaw (m : Count) : Measure (Component m) :=
  letI : Nonempty (Component m) := ⟨⟨0, m.2⟩⟩
  (PMF.uniformOfFintype (Component m)).toMeasure

/-- The iid-uniform realization mentioned after Assumption 3.1.  This is one
derived realization, not the source-facing Algorithm 2 sampling boundary. -/
noncomputable def iidUniformFiniteSumBatchLaw (n m b0 : Count) :
    FiniteSumBatchLaw n m b0 :=
  fun _ _ => Measure.infinitePi (fun _ : Fin b0.1 => componentLaw m)

/-- Source-facing product noise for one Algorithm 2 round. -/
abbrev FiniteSumRoundNoise (n m b0 : Count) (Ξ : Type*) :=
  Bool × ((Worker n → Fin b0.1 → Component m) × (Worker n → Ξ))

/-- Canonical probability realization of
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/3`,
and `#/algorithm_spec/steps/5`, separating the quoted
refresh, component-minibatch, and compressor coordinates. -/
noncomputable def finiteSumRoundLaw {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (batchLaw : Measure (FiniteSumBatch n m b0)) :
    Measure (FiniteSumRoundNoise n m b0 Ξ) :=
  (refreshLaw A.refreshProbability A.refresh_admissible).prod
    (batchLaw.prod (workerCompressionLaw A.quantizer))

/-- Joint path-law realization of
`book/MARINA/MARINA.json#/algorithm_spec/variants/1` and
`#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/3`, and
`#/algorithm_spec/steps/5`; Assumption 3.1 permits round-indexed batch laws. -/
noncomputable def finiteSumPathLaw {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0) :
    Measure (ℕ → FiniteSumRoundNoise n m b0 Ξ) :=
  Measure.infinitePi (fun k => finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k))

def finiteSumDriverOfNoise {n m b0 : Count} {Ξ : Type*}
    (z : FiniteSumRoundNoise n m b0 Ξ) : FiniteSumDriver n m b0 Ξ :=
  { refresh := z.1, batch := z.2.1, compressionSample := z.2.2 }

/-- The minibatch approximation `\widetilde Δ_i` from Assumption 3.1. -/
noncomputable def finiteSumBatchDifference {d n m b0 : Count}
    (P : FiniteSumProblem d n m)
    (batch : Worker n → Fin b0.1 → Component m)
    (i : Worker n) (xNext x : Point d) : Point d :=
  average (fun j : Fin b0.1 =>
    componentGradient P i (batch i j) xNext -
      componentGradient P i (batch i j) x)

/-- The same Assumption 3.1 estimator as a function of worker `i`'s own
minibatch coordinate. -/
noncomputable def finiteSumWorkerBatchDifference {d n m b0 : Count}
    (P : FiniteSumProblem d n m)
    (batch : FiniteSumWorkerBatch m b0)
    (i : Worker n) (xNext x : Point d) : Point d :=
  average (fun j : Fin b0.1 =>
    componentGradient P i (batch j) xNext -
      componentGradient P i (batch j) x)

/-- The Assumption 3.1 minibatch-difference kernel is jointly measurable in
the two query points and the worker's finite batch.  Component selection is a
finite measurable dispatch, while every canonical component gradient is
measurable by `measurable_gradient`. -/
theorem finiteSumWorkerBatchDifference_joint_measurable {d n m b0 : Count}
    (P : FiniteSumProblem d n m) (i : Worker n) :
    Measurable (fun p : (Point d × Point d) × FiniteSumWorkerBatch m b0 =>
      finiteSumWorkerBatchDifference P p.2 i p.1.1 p.1.2) := by
  classical
  have hterm (j : Fin b0.1) :
      Measurable (fun p : (Point d × Point d) × FiniteSumWorkerBatch m b0 =>
        componentGradient P i (p.2 j) p.1.1 -
          componentGradient P i (p.2 j) p.1.2) := by
    have hjoint : Measurable (fun q :
        (((Point d × Point d) × FiniteSumWorkerBatch m b0) × Component m) =>
        componentGradient P i q.2 q.1.1.1 -
          componentGradient P i q.2 q.1.1.2) := by
      exact measurable_from_prod_countable_left (fun c =>
        ((measurable_componentGradient P i c).comp
          (measurable_fst.comp measurable_fst)).sub
        ((measurable_componentGradient P i c).comp
          (measurable_snd.comp measurable_fst)))
    have hidx : Measurable (fun p :
        (Point d × Point d) × FiniteSumWorkerBatch m b0 => p.2 j) :=
      (measurable_pi_apply j).comp measurable_snd
    simpa only [Function.comp_apply] using hjoint.comp (measurable_id.prodMk hidx)
  unfold finiteSumWorkerBatchDifference average SOptLib.finiteUniformAverage
  exact (Finset.measurable_sum Finset.univ (fun j _ => hterm j)).const_smul
    ((Fintype.card (Fin b0.1) : ℝ)⁻¹)

theorem finiteSumBatchDifference_joint_measurable {d n m b0 : Count}
    (P : FiniteSumProblem d n m) (i : Worker n) :
    Measurable (fun p : (Point d × Point d) × FiniteSumBatch n m b0 =>
      finiteSumBatchDifference P p.2 i p.1.1 p.1.2) := by
  have hworker := finiteSumWorkerBatchDifference_joint_measurable
    (b0 := b0) P i
  have hselect : Measurable (fun p :
      (Point d × Point d) × FiniteSumBatch n m b0 => (p.1, p.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  simpa only [finiteSumBatchDifference, finiteSumWorkerBatchDifference,
    Function.comp_apply] using hworker.comp hselect

/-- `book/MARINA/MARINA.json#/assumptions/4`, Assumption 3.1 / Eq. (7):
"`E[Δ̃_i^k|x^k,x^{k+1}]=Δ_i^k`" and
"`E[‖Δ̃_i^k-Δ_i^k‖²|…]≤ℒ_i²/b⁰ ‖x^{k+1}-x^k‖²`".
The contract is parameterized by the paper's minibatch law.  In particular,
iid uniform sampling is not silently made the only admissible algorithm. -/
def FiniteSumAverageSmoothness {d n m b0 : Count}
    {Ω : Type*} (P : FiniteSumProblem d n m)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧ ∀ k i (path : Ω),
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    Integrable (fun batch => finiteSumWorkerBatchDifference P batch i xNext x)
      (batchLaw k i) ∧
    Integrable (fun batch =>
      ‖finiteSumWorkerBatchDifference P batch i xNext x -
        localGradientDifference (finiteSumLocalProblem P) i xNext x‖ ^ 2)
      (batchLaw k i) ∧
    (∫ batch, finiteSumWorkerBatchDifference P batch i xNext x
        ∂batchLaw k i) =
      localGradientDifference (finiteSumLocalProblem P) i xNext x ∧
    (∫ batch,
        ‖finiteSumWorkerBatchDifference P batch i xNext x -
          localGradientDifference (finiteSumLocalProblem P) i xNext x‖ ^ 2
        ∂batchLaw k i) ≤
      (ℒ i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2

/-- Assumption 3.1 specialized to the paper's iid-uniform example. -/
def IidUniformFiniteSumAverageSmoothness {d n m b0 : Count}
    {Ω : Type*} (P : FiniteSumProblem d n m) (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ) : Prop :=
  FiniteSumAverageSmoothness P (iidUniformFiniteSumBatchLaw n m b0) run ℒ

/-- Every component draw in the iid-uniform realization has the uniform
component marginal. -/
theorem finiteSumPathLaw_component_marginal {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (k : ℕ) (i : Worker n) (j : Fin b0.1) :
    Measure.map (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).2.1 i j)
      (finiteSumPathLaw A (iidUniformFiniteSumBatchLaw n m b0)) = componentLaw m := by
  haveI : IsProbabilityMeasure (componentLaw m) := by
    unfold componentLaw
    infer_instance
  letI (t : ℕ) (w : Worker n) :
      IsProbabilityMeasure ((iidUniformFiniteSumBatchLaw n m b0) t w) := by
    unfold iidUniformFiniteSumBatchLaw
    infer_instance
  letI (t : ℕ) :
      IsProbabilityMeasure
        (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) t) := by
    unfold finiteSumBatchJointLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) :
      IsProbabilityMeasure
        (finiteSumRoundLaw A
          (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  have hround :
      Measure.map (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k)
          (finiteSumPathLaw A (iidUniformFiniteSumBatchLaw n m b0)) =
        finiteSumRoundLaw A
          (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k) := by
    unfold finiteSumPathLaw
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun t : ℕ =>
          finiteSumRoundLaw A
            (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) t)) k)
  have hbatch :
      Measure.map (fun batch : FiniteSumBatch n m b0 => batch i j)
          (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k) =
        componentLaw m := by
    unfold finiteSumBatchJointLaw iidUniformFiniteSumBatchLaw
    change Measure.map
        ((fun batch : Fin b0.1 → Component m => batch j) ∘
          (fun batch : FiniteSumBatch n m b0 => batch i))
        (Measure.infinitePi fun _ : Worker n =>
          Measure.infinitePi fun _ : Fin b0.1 => componentLaw m) = componentLaw m
    rw [← MeasureTheory.Measure.map_map]
    · have houter :
          Measure.map (fun batch : FiniteSumBatch n m b0 => batch i)
              (Measure.infinitePi fun _ : Worker n =>
                Measure.infinitePi fun _ : Fin b0.1 => componentLaw m) =
            Measure.infinitePi (fun _ : Fin b0.1 => componentLaw m) := by
        simpa using
          (MeasureTheory.Measure.infinitePi_map_eval
            (μ := fun _ : Worker n =>
              Measure.infinitePi fun _ : Fin b0.1 => componentLaw m) i)
      rw [houter]
      simpa using
        (MeasureTheory.Measure.infinitePi_map_eval
          (μ := fun _ : Fin b0.1 => componentLaw m) j)
    · exact measurable_pi_apply j
    · exact measurable_pi_apply i
  have hroundBatch :
      Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2.1)
          (finiteSumRoundLaw A
            (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k)) =
        finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k := by
    calc
      Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2.1)
          (finiteSumRoundLaw A
            (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k)) =
          Measure.map Prod.fst
            (Measure.map Prod.snd
              (finiteSumRoundLaw A
                (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k))) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.map_map measurable_fst measurable_snd
            (μ := finiteSumRoundLaw A
              (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k))).symm
      _ = Measure.map Prod.fst
          ((finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k).prod
            (workerCompressionLaw A.quantizer)) := by
        unfold finiteSumRoundLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      _ = finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k := by
        rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  calc
    Measure.map
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).2.1 i j)
        (finiteSumPathLaw A (iidUniformFiniteSumBatchLaw n m b0)) =
        Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2.1 i j)
          (Measure.map (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k)
            (finiteSumPathLaw A (iidUniformFiniteSumBatchLaw n m b0))) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          ((measurable_pi_apply j).comp
            ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
          (measurable_pi_apply k)
          (μ := finiteSumPathLaw A (iidUniformFiniteSumBatchLaw n m b0))).symm
    _ = Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2.1 i j)
        (finiteSumRoundLaw A
          (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k)) := by
      rw [hround]
    _ = Measure.map (fun batch : FiniteSumBatch n m b0 => batch i j)
        (Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2.1)
          (finiteSumRoundLaw A
            (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k))) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          ((measurable_pi_apply j).comp (measurable_pi_apply i))
          (measurable_fst.comp measurable_snd)
          (μ := finiteSumRoundLaw A
            (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k))).symm
    _ = Measure.map (fun batch : FiniteSumBatch n m b0 => batch i j)
        (finiteSumBatchJointLaw (iidUniformFiniteSumBatchLaw n m b0) k) := by
      rw [hroundBatch]
    _ = componentLaw m := hbatch

/-- Under the probability-law boundary for Algorithm 2 minibatches, the
component minibatch and compressor coordinates are independent by the round
product law. -/
theorem finiteSumRoundLaw_batch_compression_independent
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2.1)
      (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2.2)
      (finiteSumRoundLaw (b0 := b0) A (finiteSumBatchJointLaw batchLaw k)) := by
  letI (i : Worker n) : IsProbabilityMeasure (batchLaw k i) := hBatchLaw k i
  haveI : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw k) := by
    unfold finiteSumBatchJointLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  have hPairLaw :
      Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ => z.2)
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) =
        (finiteSumBatchJointLaw batchLaw k).prod
          (workerCompressionLaw A.quantizer) := by
    unfold finiteSumRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  exact indepFun_of_map_prod_eq_prod_laws measurable_snd.aemeasurable hPairLaw

/-- For fixed iterates, the complete minibatch/compressor noise pairs of
distinct workers are independent.  This is the law-level realization of the
independence observation used in the source proof of Eq. (33). -/
theorem finiteSumRoundLaw_worker_noise_iIndep
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i (z : FiniteSumRoundNoise n m b0 Ξ) => (z.2.1 i, z.2.2 i))
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) := by
  letI (i : Worker n) : IsProbabilityMeasure (batchLaw k i) := hBatchLaw k i
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw k) := by
    unfold finiteSumBatchJointLaw
    infer_instance
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) := by
    unfold finiteSumRoundLaw
    infer_instance
  have hInner :
      Measure.map
          (fun z : FiniteSumBatch n m b0 × (Worker n → Ξ) =>
            fun i => (z.1 i, z.2 i))
          ((finiteSumBatchJointLaw batchLaw k).prod
            (workerCompressionLaw A.quantizer)) =
        Measure.infinitePi (fun i : Worker n =>
          (batchLaw k i).prod A.quantizer.law) := by
    unfold finiteSumBatchJointLaw workerCompressionLaw
    rw [MeasureTheory.Measure.infinitePi_eq_pi,
      MeasureTheory.Measure.infinitePi_eq_pi,
      MeasureTheory.Measure.infinitePi_eq_pi]
    simpa using
      (MeasureTheory.measurePreserving_arrowProdEquivProdArrow
        (FiniteSumWorkerBatch m b0) Ξ (Worker n)
        (batchLaw k) (fun _ : Worker n => A.quantizer.law)).symm.map_eq
  have hWhole :
      Measure.map
          (fun z : FiniteSumRoundNoise n m b0 Ξ =>
            fun i => (z.2.1 i, z.2.2 i))
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) =
        Measure.infinitePi (fun i : Worker n =>
          (batchLaw k i).prod A.quantizer.law) := by
    calc
      Measure.map
          (fun z : FiniteSumRoundNoise n m b0 Ξ =>
            fun i => (z.2.1 i, z.2.2 i))
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) =
          Measure.map
            (fun z : FiniteSumBatch n m b0 × (Worker n → Ξ) =>
              fun i => (z.1 i, z.2 i))
            (Measure.map Prod.snd
              (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k))) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · fun_prop
        · exact measurable_snd
      _ = Measure.map
            (fun z : FiniteSumBatch n m b0 × (Worker n → Ξ) =>
              fun i => (z.1 i, z.2 i))
            ((finiteSumBatchJointLaw batchLaw k).prod
              (workerCompressionLaw A.quantizer)) := by
        unfold finiteSumRoundLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      _ = Measure.infinitePi (fun i : Worker n =>
          (batchLaw k i).prod A.quantizer.law) := hInner
  have hcoord (i : Worker n) :
      Measure.map
          (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i))
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) =
        (batchLaw k i).prod A.quantizer.law := by
    calc
      Measure.map
          (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i))
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) =
          Measure.map (fun w : Worker n →
              (FiniteSumWorkerBatch m b0 × Ξ) => w i)
            (Measure.map
              (fun z : FiniteSumRoundNoise n m b0 Ξ =>
                fun j => (z.2.1 j, z.2.2 j))
              (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k))) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact measurable_pi_apply i
        · fun_prop
      _ = Measure.map (fun w : Worker n →
              (FiniteSumWorkerBatch m b0 × Ξ) => w i)
            (Measure.infinitePi (fun j : Worker n =>
              (batchLaw k j).prod A.quantizer.law)) := by rw [hWhole]
      _ = (batchLaw k i).prod A.quantizer.law := by
        simpa using
          (MeasureTheory.Measure.infinitePi_map_eval
            (μ := fun j : Worker n =>
              (batchLaw k j).prod A.quantizer.law) i)
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map (by
    intro i
    fun_prop)).2
  calc
    Measure.map
        (fun z : FiniteSumRoundNoise n m b0 Ξ =>
          fun i => (z.2.1 i, z.2.2 i))
        (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) =
        Measure.infinitePi (fun i : Worker n =>
          (batchLaw k i).prod A.quantizer.law) := hWhole
    _ = Measure.infinitePi (fun i : Worker n =>
        Measure.map
          (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i))
          (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k))) := by
      congr 1
      funext i
      exact (hcoord i).symm

/-- Pairwise form consumed by worker-average variance reductions. -/
theorem finiteSumRoundLaw_worker_noise_pairwise_independent
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ)
    {i j : Worker n} (hij : i ≠ j) :
    ProbabilityTheory.IndepFun
      (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 i, z.2.2 i))
      (fun z : FiniteSumRoundNoise n m b0 Ξ => (z.2.1 j, z.2.2 j))
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) := by
  exact (finiteSumRoundLaw_worker_noise_iIndep A batchLaw hBatchLaw k).indepFun hij

/-- Every time coordinate of the Algorithm 2 path has its canonical round law. -/
theorem finiteSumPathLaw_round_marginal
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    Measure.map (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k)
      (finiteSumPathLaw A batchLaw) =
        finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k) := by
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) :
      IsProbabilityMeasure
        (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  unfold finiteSumPathLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun t : ℕ =>
        finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) k)

/-- Worker noise pairs remain jointly independent when read from round `k` of
the full Algorithm 2 path law. -/
theorem finiteSumPathLaw_worker_noise_iIndep
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) =>
        ((path k).2.1 i, (path k).2.2 i))
      (finiteSumPathLaw A batchLaw) := by
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) :
      IsProbabilityMeasure
        (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure (finiteSumPathLaw A batchLaw) := by
    unfold finiteSumPathLaw
    infer_instance
  let roundLaw := finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)
  let roundNoise := fun i (z : FiniteSumRoundNoise n m b0 Ξ) =>
    (z.2.1 i, z.2.2 i)
  have hRound : ProbabilityTheory.iIndepFun roundNoise roundLaw :=
    finiteSumRoundLaw_worker_noise_iIndep A batchLaw hBatchLaw k
  have hRoundLaw :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map (by
      intro i
      fun_prop)).1 hRound
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map (by
    intro i
    fun_prop)).2
  calc
    Measure.map
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
          fun i => ((path k).2.1 i, (path k).2.2 i))
        (finiteSumPathLaw A batchLaw) =
        Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ =>
          fun i => (z.2.1 i, z.2.2 i))
          (Measure.map (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k)
            (finiteSumPathLaw A batchLaw)) := by
      rw [MeasureTheory.Measure.map_map]
      · rfl
      · fun_prop
      · exact measurable_pi_apply k
    _ = Measure.map (fun z : FiniteSumRoundNoise n m b0 Ξ =>
          fun i => (z.2.1 i, z.2.2 i)) roundLaw := by
      rw [finiteSumPathLaw_round_marginal A batchLaw hBatchLaw k]
    _ = Measure.infinitePi (fun i => Measure.map (roundNoise i) roundLaw) := hRoundLaw
    _ = Measure.infinitePi (fun i =>
        Measure.map
          (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
            ((path k).2.1 i, (path k).2.2 i))
          (finiteSumPathLaw A batchLaw)) := by
      congr 1
      funext i
      calc
        Measure.map (roundNoise i) roundLaw =
            Measure.map (roundNoise i)
              (Measure.map
                (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k)
                (finiteSumPathLaw A batchLaw)) := by
          rw [finiteSumPathLaw_round_marginal A batchLaw hBatchLaw k]
        _ = Measure.map
            (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
              ((path k).2.1 i, (path k).2.2 i))
            (finiteSumPathLaw A batchLaw) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · fun_prop
          · exact measurable_pi_apply k

noncomputable def finiteSumDifference {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (z : FiniteSumDriver n m b0 Ξ)
    (i : Worker n) (xNext x : Point d) : Point d :=
  finiteSumBatchDifference A.problem z.batch i xNext x

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/3`: the quoted
finite-sum VR refresh/difference worker update. -/
noncomputable def finiteSumWorkerEstimator {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (z : FiniteSumDriver n m b0 Ξ)
    (s : State d) (i : Worker n) : Point d :=
  let P := finiteSumLocalProblem A.problem
  let xNext := primalStep A.stepSize s
  if z.refresh then localGradient P i xNext
  else s.g + A.quantizer.apply (finiteSumDifference A z i xNext s.x)
    (z.compressionSample i)

/-- The Algorithm 2 worker update is jointly measurable in the previous state
and the current canonical round noise. -/
theorem finiteSumWorkerEstimator_round_joint_measurable
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (i : Worker n) :
    Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      finiteSumWorkerEstimator A (finiteSumDriverOfNoise p.2) p.1 i) := by
  classical
  let P := finiteSumLocalProblem A.problem
  have hxNext : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hx : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      p.1.x) := (measurable_state_x d).comp measurable_fst
  have hbatch : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      p.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hqueries : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      ((primalStep A.stepSize p.1, p.1.x), p.2.2.1)) :=
    (hxNext.prodMk hx).prodMk hbatch
  have hdiff : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      finiteSumBatchDifference A.problem p.2.2.1 i
        (primalStep A.stepSize p.1) p.1.x) := by
    simpa only [Function.comp_apply] using
      (finiteSumBatchDifference_joint_measurable (b0 := b0) A.problem i).comp hqueries
  have hsample : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      p.2.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hquantized : Measurable
      (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
        A.quantizer.apply
          (finiteSumBatchDifference A.problem p.2.2.1 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    A.quantizer.measurable_apply_uncurry.comp (hdiff.prodMk hsample)
  have hrefresh : Measurable
      (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
        localGradient P i (primalStep A.stepSize p.1)) :=
    (measurable_localGradient P i).comp hxNext
  have hcarry : Measurable
      (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
        p.1.g + A.quantizer.apply
          (finiteSumBatchDifference A.problem p.2.2.1 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    ((measurable_state_g d).comp measurable_fst).add hquantized
  have hrefreshSet : MeasurableSet
      {p : State d × FiniteSumRoundNoise n m b0 Ξ | p.2.1 = true} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
  have hif : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      if p.2.1 = true then
        localGradient P i (primalStep A.stepSize p.1)
      else p.1.g + A.quantizer.apply
        (finiteSumBatchDifference A.problem p.2.2.1 i
          (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    @Measurable.ite _ _ _ _ _ _
      (fun p : State d × FiniteSumRoundNoise n m b0 Ξ => p.2.1 = true)
      (fun p => Bool.decEq p.2.1 true)
      hrefreshSet hrefresh hcarry
  simpa [finiteSumWorkerEstimator, finiteSumDriverOfNoise, finiteSumDifference, P] using
    hif

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/3`, and `#/algorithm_spec/steps/5`: canonical
finite-sum VR transition and worker averaging. -/
noncomputable def finiteSumStep {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (z : FiniteSumDriver n m b0 Ξ)
    (s : State d) : State d :=
  { x := primalStep A.stepSize s
    g := average (finiteSumWorkerEstimator A z s) }

/-- The canonical Algorithm 2 transition is measurable in state/current-round
noise.  This is the transition premise consumed by strict-past recursion. -/
theorem finiteSumStep_round_joint_measurable
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) :
    Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      finiteSumStep A (finiteSumDriverOfNoise p.2) p.1) := by
  classical
  have hxNext : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hg : Measurable (fun p : State d × FiniteSumRoundNoise n m b0 Ξ =>
      average (fun i : Worker n =>
        finiteSumWorkerEstimator A (finiteSumDriverOfNoise p.2) p.1 i)) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ (fun i _ =>
      finiteSumWorkerEstimator_round_joint_measurable A i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
  simpa [finiteSumStep] using
    (measurable_state_mk d).comp (hxNext.prodMk hg)

/-- `book/MARINA/MARINA.json#/algorithm_spec/initialization/facts/1`:
"`g^0=∇f(x^0)`". -/
noncomputable def finiteSumInitialState {d n m : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) : State d :=
  { x := x0, g := globalGradient (finiteSumLocalProblem A.problem) x0 }

/-- Generated recursion for `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/3`, and `#/algorithm_spec/steps/5`
from the exact initialization at `#/algorithm_spec/initialization/facts/1`. -/
noncomputable def finiteSumRun {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) :
    ℕ → (ℕ → FiniteSumDriver n m b0 Ξ) → State d :=
  SOptLib.recursiveIterateProcess (finiteSumInitialState A x0)
    (fun k s path => finiteSumStep A (path k) s)

/-- Random-process realization of `book/MARINA/MARINA.json#/algorithm_spec/variants/1`
and the quoted transition at `#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/3`, and `#/algorithm_spec/steps/5`. -/
noncomputable def finiteSumProcess {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d) :
    ℕ → (ℕ → FiniteSumRoundNoise n m b0 Ξ) → State d :=
  fun k path => finiteSumRun A x0 k (fun t => finiteSumDriverOfNoise (path t))

/-- The sigma-algebra generated by the Algorithm 2 round coordinates strictly
before `k`. -/
@[reducible] def finiteSumStrictPast {n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (k : ℕ) : MeasurableSpace (ℕ → FiniteSumRoundNoise n m b0 Ξ) :=
  ⨆ j : Fin k, MeasurableSpace.comap
    (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path j) inferInstance

theorem finiteSumStrictPast_coordinate_measurable
    {n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    {j k : ℕ} (hjk : j < k) :
    Measurable[finiteSumStrictPast (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path j) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le ⟨j, hjk⟩ (by rfl)

theorem finiteSumStrictPast_le
    {n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ] (k : ℕ) :
    finiteSumStrictPast (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
      (inferInstance : MeasurableSpace (ℕ → FiniteSumRoundNoise n m b0 Ξ)) := by
  refine iSup_le fun j => ?_
  exact (measurable_pi_apply (j : ℕ)).comap_le

/-- The generated Algorithm 2 state at time `k` is measurable from precisely
the strict-past round coordinates.  The proof consumes the compiled measurable
transition rather than postulating adaptedness. -/
theorem finiteSumProcess_strictPast_measurable
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (k : ℕ) :
    Measurable[finiteSumStrictPast (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k]
      (finiteSumProcess (b0 := b0) A x0 k) := by
  let past : Unit → MeasurableSpace (ℕ → FiniteSumRoundNoise n m b0 Ξ) :=
    fun _ => finiteSumStrictPast (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k
  let driver : ℕ → (ℕ → FiniteSumRoundNoise n m b0 Ξ) →
      FiniteSumRoundNoise n m b0 Ξ := fun t path => path t
  let step : ℕ → State d → FiniteSumRoundNoise n m b0 Ξ → State d :=
    fun _ s z => finiteSumStep A (finiteSumDriverOfNoise z) s
  apply SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := past) (process := finiteSumProcess (b0 := b0) A x0)
      (driver := driver) (step := step) (k := ()) (N := k)
  · change Measurable[past ()]
      (fun _ : ℕ → FiniteSumRoundNoise n m b0 Ξ => finiteSumInitialState A x0)
    exact measurable_const
  · intro t ht _hprocess
    exact finiteSumStrictPast_coordinate_measurable (Nat.lt_of_succ_le ht)
  · intro _t _ht
    exact finiteSumStep_round_joint_measurable A
  · intro t _ht
    rfl
  · exact le_rfl

/-- The centered, state-dependent worker innovation in the non-refresh branch
of Algorithm 2. -/
noncomputable def finiteSumWorkerInnovation
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (k : ℕ) (i : Worker n)
    (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) : Point d :=
  let s := finiteSumProcess (b0 := b0) A x0 k path
  let xNext := primalStep A.stepSize s
  A.quantizer.apply
      (finiteSumWorkerBatchDifference A.problem ((path k).2.1 i) i xNext s.x)
      ((path k).2.2 i) -
    localGradientDifference (finiteSumLocalProblem A.problem) i xNext s.x

/-- The sigma-algebra containing the strict past and worker `i`'s fresh
minibatch/compressor coordinate at round `k`. -/
@[reducible] def finiteSumWorkerHistory
    {n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ] (k : ℕ) (i : Worker n) :
    MeasurableSpace (ℕ → FiniteSumRoundNoise n m b0 Ξ) :=
  finiteSumStrictPast (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ⊔
    MeasurableSpace.comap
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i)) inferInstance

theorem finiteSumWorkerInnovation_measurable_wrt_history
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (k : ℕ) (i : Worker n) :
    Measurable[finiteSumWorkerHistory (m := m) (b0 := b0) (Ξ := Ξ) k i]
      (finiteSumWorkerInnovation A x0 k i) := by
  let hist := finiteSumWorkerHistory (m := m) (b0 := b0) (Ξ := Ξ) k i
  have hstate : Measurable[hist] (finiteSumProcess (b0 := b0) A x0 k) :=
    (finiteSumProcess_strictPast_measurable A x0 k).mono le_sup_left le_rfl
  have hcurrent : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i)) := by
    rw [measurable_iff_comap_le]
    exact le_sup_right
  have hxNext : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path)) :=
    (measurable_primalStep A.stepSize).comp hstate
  have hx : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        (finiteSumProcess (b0 := b0) A x0 k path).x) :=
    (measurable_state_x d).comp hstate
  have hbatch : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).2.1 i) :=
    measurable_fst.comp hcurrent
  have hsample : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).2.2 i) :=
    measurable_snd.comp hcurrent
  have hquery : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path),
          (finiteSumProcess (b0 := b0) A x0 k path).x), (path k).2.1 i)) :=
    (hxNext.prodMk hx).prodMk hbatch
  have hdiff : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        finiteSumWorkerBatchDifference A.problem ((path k).2.1 i) i
          (primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path))
          (finiteSumProcess (b0 := b0) A x0 k path).x) := by
    simpa only [Function.comp_apply] using
      (finiteSumWorkerBatchDifference_joint_measurable (b0 := b0) A.problem i).comp hquery
  have hquantized : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        A.quantizer.apply
          (finiteSumWorkerBatchDifference A.problem ((path k).2.1 i) i
            (primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path))
            (finiteSumProcess (b0 := b0) A x0 k path).x)
          ((path k).2.2 i)) :=
    A.quantizer.measurable_apply_uncurry.comp (hdiff.prodMk hsample)
  have hmean : Measurable[hist]
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        localGradientDifference (finiteSumLocalProblem A.problem) i
          (primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path))
          (finiteSumProcess (b0 := b0) A x0 k path).x) := by
    unfold localGradientDifference
    exact ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp hxNext).sub
      ((measurable_localGradient (finiteSumLocalProblem A.problem) i).comp hx)
  exact hquantized.sub hmean

/-- The state-dependent Algorithm 2 innovation has genuine measurable
semantics under the path law.  Its past-dependent query is measurable by
`finiteSumProcess_strictPast_measurable`; its batch and compressor inputs are
the measurable current-round coordinates; joint compressor measurability then
closes the composition. -/
theorem finiteSumWorkerInnovation_aestronglyMeasurable
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0) (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable (finiteSumWorkerInnovation A x0 k i)
      (finiteSumPathLaw A batchLaw) := by
  have hcurrent : Measurable
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i)) := by fun_prop
  have hhist : finiteSumWorkerHistory (m := m) (b0 := b0) (Ξ := Ξ) k i ≤
      (inferInstance : MeasurableSpace (ℕ → FiniteSumRoundNoise n m b0 Ξ)) :=
    sup_le (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
      hcurrent.comap_le
  exact ((finiteSumWorkerInnovation_measurable_wrt_history A x0 k i).mono
    hhist le_rfl).aestronglyMeasurable

@[simp] theorem finiteSumRun_succ {d n m b0 : Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (k : ℕ)
    (path : ℕ → FiniteSumDriver n m b0 Ξ) :
    finiteSumRun A x0 (k + 1) path =
      finiteSumStep A (path k) (finiteSumRun A x0 k path) := by
  rfl

/-! ## Online VR-MARINA (Algorithm 3) -/

/-- Raw online-oracle data before imposing the well-definedness semantics of
Eq. (6).  This carrier is deliberately not used by Algorithm 3 or its
source-facing theorems; it is retained only for countermodels showing that
gradient moments do not imply integrability of the sampled losses. -/
structure RawOnlineProblem (d n : Count) (Sample : Worker n → Type*)
    [∀ i, MeasurableSpace (Sample i)] where
  sampleLoss : (i : Worker n) → Sample i → Point d → ℝ
  sampleLaw : (i : Worker n) → Measure (Sample i)
  sampleLaw_isProbability : ∀ i, IsProbabilityMeasure (sampleLaw i)

/-- `book/MARINA/MARINA.json#/setup/definitions/2`, Eq. (6):
"`f_i(x)=E_{ξ_i∼D_i}[f_{ξ_i}(x)]`".  The paper's online problem
therefore consists of sampled losses whose displayed expectations are genuine
Bochner expectations, not Mathlib's totalized value for a nonintegrable
function.  No independent `localProblem` witness is stored. -/
structure OnlineProblem (d n : Count) (Sample : Worker n → Type*)
    [∀ i, MeasurableSpace (Sample i)] extends RawOnlineProblem d n Sample where
  sampleLoss_integrable : ∀ i x,
    Integrable (fun ξ ↦ sampleLoss i ξ x) (sampleLaw i)

/-- `book/MARINA/MARINA.json#/setup/definitions/2`:
"`f_i(x)=E_{ξ_i∼D_i}[f_{ξ_i}(x)]`".  This is the expectation in Eq. (6),
as a named canonical object. -/
noncomputable def expectedSampleLoss {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)] (P : OnlineProblem d n Sample)
    (i : Worker n) (x : Point d) : ℝ :=
  ∫ ξ, P.sampleLoss i ξ x ∂P.sampleLaw i

/-- The canonical local problem of Eq. (6), computed from the online sample
losses and their laws. -/
noncomputable def onlineLocalProblem {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)] (P : OnlineProblem d n Sample) :
    LocalProblem d n where
  localLoss i x := expectedSampleLoss P i x

/-- Eq. (6)'s defining expectation is integrable for every source-facing
online problem. -/
theorem onlineLocalProblem_integrable {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) (x : Point d) :
    Integrable (fun ξ ↦ P.sampleLoss i ξ x) (P.sampleLaw i) := by
  exact P.sampleLoss_integrable i x

/-- Compatibility predicate for the former conditional B-track.  For the
source-facing `OnlineProblem`, this is now derived from Eq. (6)'s intrinsic
well-definedness datum rather than supplied separately by a theorem. -/
def OnlineExpectationRealization {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)] (P : OnlineProblem d n Sample) : Prop :=
  ∀ i x, Integrable (fun ξ => P.sampleLoss i ξ x) (P.sampleLaw i)

theorem onlineExpectationRealization {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) : OnlineExpectationRealization P := by
  exact P.sampleLoss_integrable

/-- A distinctly named B-track carrier for an online problem whose Eq. (6)
expectations have nonfallback Bochner semantics. -/
abbrev RealizedOnlineProblem (d n : Count) (Sample : Worker n → Type*)
    [∀ i, MeasurableSpace (Sample i)] :=
  {P : OnlineProblem d n Sample // OnlineExpectationRealization P}

/-- Legacy corrected spelling of Eq. (6).  Since the source-facing
`OnlineProblem` now carries the well-definedness of its expectation, this is
definitionally the same canonical local problem rather than a parallel
conditional construction. -/
noncomputable def onlineLocalProblemCorrected {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) : LocalProblem d n where
  localLoss i x := ∫ ξ, P.1.sampleLoss i ξ x ∂P.1.sampleLaw i

/-- The defining expectation in the corrected B-track has genuine integral
semantics rather than Mathlib's nonintegrable fallback. -/
theorem onlineLocalProblemCorrected_integrable {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) (i : Worker n) (x : Point d) :
    Integrable (fun ξ => P.1.sampleLoss i ξ x) (P.1.sampleLaw i) := by
  exact onlineLocalProblem_integrable P.1 i x

theorem onlineLocalProblemCorrected_eq_onlineLocalProblem {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) :
    onlineLocalProblemCorrected P = onlineLocalProblem P.1 := by
  rfl

@[simp] theorem onlineLocalProblemCorrected_apply {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) (i : Worker n) (x : Point d) :
    (onlineLocalProblemCorrected P).localLoss i x =
      ∫ ξ, P.1.sampleLoss i ξ x ∂P.1.sampleLaw i := by
  rfl

/-- `book/MARINA/MARINA.json#/setup/definitions/2`, Eq. (6):
"`f_i(x)=E_{ξ_i∼D_i}[f_{ξ_i}(x)]`".  This is the literal source
expression.  Its sample-loss integrability is intrinsic `OnlineProblem` data;
joint sample-gradient measurability is not, because it is not stated by the
paper and is strictly stronger than the fixed-query moments. -/
theorem onlineLocalProblem_apply {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) (x : Point d) :
    (onlineLocalProblem P).localLoss i x =
      ∫ ξ, P.sampleLoss i ξ x ∂P.sampleLaw i := by
  rfl

/-- `book/MARINA/MARINA.json#/assumptions/6`:
"`E_{ξ_i∼D_i}[∇f_{ξ_i}(x)]=∇f_i(x)`".  This is the canonical gradient of
the sampled loss appearing in Assumption 3.3. -/
noncomputable def stochasticGradient {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) (ξ : Sample i)
    (x : Point d) : Point d :=
  gradient (P.sampleLoss i ξ) x

/-- The law-a.e. differentiability realization used by the corrected online
track.  It is the weakest sampled-loss condition used by the finite-difference
construction below and deliberately ignores null sample values.  The paper's
Assumption 3.3 writes sampled gradients but does not state this regularity as a
separate assumption, so this predicate marks a conditional realization rather
than silently strengthening the literal source boundary. -/
def OnlineSampleLossDifferentiable {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) : Prop :=
  ∀ i, ∀ᵐ ξ ∂P.sampleLaw i, Differentiable ℝ (P.sampleLoss i ξ)

/-- Forward coordinate differences of a sampled loss.  They are used only to
derive probability regularity of the canonical gradient, not as an oracle
replacement. -/
noncomputable def stochasticGradientForwardApprox
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) (m : ℕ)
    (p : Point d × Sample i) : Point d :=
  (EuclideanSpace.equiv (Fin d.1) ℝ).symm fun j ↦
      let t : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹
      t⁻¹ * (P.sampleLoss i p.2 (p.1 + t • EuclideanSpace.single j 1) -
        P.sampleLoss i p.2 p.1)

/-- Assumption 3.3's everywhere-defined sampled gradients, together with
Eq. (6)'s fixed-query integrability, imply the exact product-law random
variable needed at an arbitrary query law.  The proof does not assume a
jointly measurable oracle: it constructs the gradient as the pointwise limit
of forward differences.  Each difference is product-law measurable by the
law-scoped Carathéodory theorem because sampled losses are continuous in the
query and a.e. strongly measurable in the sample at every fixed query. -/
theorem stochasticGradient_product_aestronglyMeasurable_of_differentiable
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (hDiff : OnlineSampleLossDifferentiable P)
    (i : Worker n) (nu : Measure (Point d)) :
    AEStronglyMeasurable
      (fun p : Point d × Sample i ↦ stochasticGradient P i p.2 p.1)
      (nu.prod (P.sampleLaw i)) := by
  letI : IsProbabilityMeasure (P.sampleLaw i) := P.sampleLaw_isProbability i
  have happrox (m : ℕ) : AEStronglyMeasurable
      (stochasticGradientForwardApprox P i m)
      (nu.prod (P.sampleLaw i)) := by
    have hcoord (j : Fin d.1) : AEStronglyMeasurable
        (fun p : Point d × Sample i ↦
          stochasticGradientForwardApprox P i m p j)
        (nu.prod (P.sampleLaw i)) := by
      let t : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹
      let e : Point d := EuclideanSpace.single j 1
      have hshift : AEStronglyMeasurable
          (fun p : Point d × Sample i ↦ P.sampleLoss i p.2 (p.1 + t • e))
          (nu.prod (P.sampleLaw i)) := by
        exact aestronglyMeasurable_prod_of_continuous_ae_of_fiber
          nu (P.sampleLaw i) (fun x ξ ↦ P.sampleLoss i ξ x)
          (fun x : Point d ↦ x + t • e)
          (by fun_prop)
          ((hDiff i).mono fun ξ hξ ↦ hξ.continuous)
          (fun x ↦ (P.sampleLoss_integrable i x).aestronglyMeasurable)
      have hbase : AEStronglyMeasurable
          (fun p : Point d × Sample i ↦ P.sampleLoss i p.2 p.1)
          (nu.prod (P.sampleLaw i)) := by
        exact aestronglyMeasurable_prod_of_continuous_ae_of_fiber
          nu (P.sampleLaw i) (fun x ξ ↦ P.sampleLoss i ξ x)
          (fun x : Point d ↦ x)
          stronglyMeasurable_id
          ((hDiff i).mono fun ξ hξ ↦ hξ.continuous)
          (fun x ↦ (P.sampleLoss_integrable i x).aestronglyMeasurable)
      simpa [stochasticGradientForwardApprox, t, e] using
        (hshift.sub hbase).const_mul t⁻¹
    have hraw : AEMeasurable
        (fun p : Point d × Sample i ↦
          fun j ↦ stochasticGradientForwardApprox P i m p j)
        (nu.prod (P.sampleLaw i)) :=
      aemeasurable_pi_lambda _ fun j ↦ (hcoord j).aemeasurable
    have hassembled : AEMeasurable
        (fun p ↦ (EuclideanSpace.equiv (Fin d.1) ℝ).symm
          (fun j ↦ stochasticGradientForwardApprox P i m p j))
        (nu.prod (P.sampleLaw i)) :=
      (EuclideanSpace.equiv (Fin d.1) ℝ).symm.continuous.measurable.comp_aemeasurable hraw
    simpa only [stochasticGradientForwardApprox] using
      hassembled.aestronglyMeasurable
  apply aestronglyMeasurable_of_tendsto_ae Filter.atTop happrox
  have hdiffProd : ∀ᵐ p ∂nu.prod (P.sampleLaw i),
      Differentiable ℝ (P.sampleLoss i p.2) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd
      (μ := nu) (ν := P.sampleLaw i)).tendsto_ae (hDiff i)
  filter_upwards [hdiffProd] with p hp
  rw [← (EuclideanSpace.equiv (Fin d.1) ℝ).symm_apply_apply
    (stochasticGradient P i p.2 p.1)]
  apply (EuclideanSpace.equiv (Fin d.1) ℝ).symm.continuous.continuousAt.tendsto.comp
  apply tendsto_pi_nhds.2
  intro j
  let t : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  let e : Point d := EuclideanSpace.single j 1
  have ht0 : Filter.Tendsto t Filter.atTop (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa [t] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1))
            Filter.atTop (nhds 0))
    · filter_upwards with m
      dsimp [t]
      exact one_div_ne_zero (by positivity)
  have hline :=
    ((hp p.1).hasGradientAt.hasFDerivAt.hasLineDerivAt e).tendsto_slope_zero
  have hlimit := hline.comp ht0
  have hcoordDual :
      ((InnerProductSpace.toDual ℝ (Point d)).symm
        (fderiv ℝ (P.sampleLoss i p.2) p.1)) j =
        fderiv ℝ (P.sampleLoss i p.2) p.1 e := by
    calc
      _ = ⟪(InnerProductSpace.toDual ℝ (Point d)).symm
          (fderiv ℝ (P.sampleLoss i p.2) p.1), e⟫_ℝ := by
        exact (by
          simpa only [e, one_mul, conj_trivial] using
            (EuclideanSpace.inner_single_right j (1 : ℝ)
              ((InnerProductSpace.toDual ℝ (Point d)).symm
                (fderiv ℝ (P.sampleLoss i p.2) p.1))).symm)
      _ = _ := InnerProductSpace.toDual_symm_apply
  simpa [stochasticGradientForwardApprox, stochasticGradient, gradient, t, e,
    Function.comp_def, Nat.cast_add, one_div, hcoordDual] using hlimit

/-- Random-query and reindexed-sample form of
`stochasticGradient_product_aestronglyMeasurable_of_differentiable`.  This is
the form used by an adaptive iterate paired with a fresh minibatch coordinate. -/
theorem stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
    {d n : Count} {Sample : Worker n → Type*} {Q S : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Q] [MeasurableSpace S]
    (P : OnlineProblem d n Sample) (i : Worker n)
    (nuQ : Measure Q) (nuS : Measure S) [SFinite nuS]
    (query : Q → Point d) (sample : S → Sample i)
    (hquery : AEStronglyMeasurable query nuQ)
    (hSampleDiff : ∀ᵐ s ∂nuS, Differentiable ℝ (P.sampleLoss i (sample s)))
    (hIntegrable : ∀ x, Integrable (fun s ↦ P.sampleLoss i (sample s) x) nuS) :
    AEStronglyMeasurable
      (fun p : Q × S ↦ stochasticGradient P i (sample p.2) (query p.1))
      (nuQ.prod nuS) := by
  apply aestronglyMeasurable_prod_of_continuous_ae_of_fiber_of_aestronglyMeasurable
    nuQ nuS (fun x s ↦ stochasticGradient P i (sample s) x) query hquery
  intro query' hquery'
  let approx : ℕ → Q × S → Point d := fun m p ↦
    stochasticGradientForwardApprox P i m (query' p.1, sample p.2)
  have happrox (m : ℕ) : AEStronglyMeasurable (approx m) (nuQ.prod nuS) := by
    have hcoord (j : Fin d.1) : AEStronglyMeasurable
        (fun p : Q × S ↦ approx m p j) (nuQ.prod nuS) := by
      let t : ℝ := ((m + 1 : ℕ) : ℝ)⁻¹
      let e : Point d := EuclideanSpace.single j 1
      have hshift : AEStronglyMeasurable
          (fun p : Q × S ↦ P.sampleLoss i (sample p.2) (query' p.1 + t • e))
          (nuQ.prod nuS) := by
        exact aestronglyMeasurable_prod_of_continuous_ae_of_fiber
          nuQ nuS (fun x s ↦ P.sampleLoss i (sample s) x)
          (fun q ↦ query' q + t • e) (hquery'.add stronglyMeasurable_const)
          (hSampleDiff.mono fun s hs ↦ hs.continuous)
          (fun x ↦ (hIntegrable x).aestronglyMeasurable)
      have hbase : AEStronglyMeasurable
          (fun p : Q × S ↦ P.sampleLoss i (sample p.2) (query' p.1))
          (nuQ.prod nuS) := by
        exact aestronglyMeasurable_prod_of_continuous_ae_of_fiber
          nuQ nuS (fun x s ↦ P.sampleLoss i (sample s) x) query' hquery'
          (hSampleDiff.mono fun s hs ↦ hs.continuous)
          (fun x ↦ (hIntegrable x).aestronglyMeasurable)
      simpa [approx, stochasticGradientForwardApprox, t, e] using
        (hshift.sub hbase).const_mul t⁻¹
    have hraw : AEMeasurable
        (fun p : Q × S ↦ fun j ↦ approx m p j) (nuQ.prod nuS) :=
      aemeasurable_pi_lambda _ fun j ↦ (hcoord j).aemeasurable
    have hassembled : AEMeasurable
        (fun p ↦ (EuclideanSpace.equiv (Fin d.1) ℝ).symm
          (fun j ↦ approx m p j)) (nuQ.prod nuS) :=
      (EuclideanSpace.equiv (Fin d.1) ℝ).symm.continuous.measurable.comp_aemeasurable hraw
    simpa only [approx, stochasticGradientForwardApprox] using
      hassembled.aestronglyMeasurable
  apply aestronglyMeasurable_of_tendsto_ae Filter.atTop happrox
  have hdiffProd : ∀ᵐ p ∂nuQ.prod nuS,
      Differentiable ℝ (P.sampleLoss i (sample p.2)) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd
      (μ := nuQ) (ν := nuS)).tendsto_ae hSampleDiff
  filter_upwards [hdiffProd] with p hp
  rw [← (EuclideanSpace.equiv (Fin d.1) ℝ).symm_apply_apply
    (stochasticGradient P i (sample p.2) (query' p.1))]
  apply (EuclideanSpace.equiv (Fin d.1) ℝ).symm.continuous.continuousAt.tendsto.comp
  apply tendsto_pi_nhds.2
  intro j
  let t : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  let e : Point d := EuclideanSpace.single j 1
  have ht0 : Filter.Tendsto t Filter.atTop (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa [t] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1))
            Filter.atTop (nhds 0))
    · filter_upwards with m
      dsimp [t]
      exact one_div_ne_zero (by positivity)
  have hline :=
    ((hp (query' p.1)).hasGradientAt.hasFDerivAt.hasLineDerivAt e).tendsto_slope_zero
  have hlimit := hline.comp ht0
  have hcoordDual :
      ((InnerProductSpace.toDual ℝ (Point d)).symm
        (fderiv ℝ (P.sampleLoss i (sample p.2)) (query' p.1))) j =
        fderiv ℝ (P.sampleLoss i (sample p.2)) (query' p.1) e := by
    calc
      _ = ⟪(InnerProductSpace.toDual ℝ (Point d)).symm
          (fderiv ℝ (P.sampleLoss i (sample p.2)) (query' p.1)), e⟫_ℝ := by
        exact (by
          simpa only [e, one_mul, conj_trivial] using
            (EuclideanSpace.inner_single_right j (1 : ℝ)
              ((InnerProductSpace.toDual ℝ (Point d)).symm
                (fderiv ℝ (P.sampleLoss i (sample p.2)) (query' p.1)))).symm)
      _ = _ := InnerProductSpace.toDual_symm_apply
  simpa [approx, stochasticGradientForwardApprox, stochasticGradient, gradient, t, e,
    Function.comp_def, Nat.cast_add, one_div, hcoordDual] using hlimit

/-- For a fixed online sample, the stochastic gradient is a measurable
function of the query.  This is not an oracle regularity assumption:
Mathlib proves measurability of the totalized Fréchet derivative of an
arbitrary function on a finite-dimensional Euclidean space. -/
@[fun_prop] theorem stochasticGradient_query_measurable
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) (ξ : Sample i) :
    Measurable (fun x : Point d ↦ stochasticGradient P i ξ x) := by
  exact measurable_gradient (P.sampleLoss i ξ)

/-! Assumptions 3.2--3.3 constrain gradients and do not imply Eq. (6)'s
sample-loss integrability.  The following raw Cauchy model records that
separation without inhabiting the source-facing `OnlineProblem`. -/

lemma identity_not_integrable_cauchy :
    ¬ Integrable (fun ξ : ℝ ↦ ξ) (ProbabilityTheory.cauchyMeasure 0 1) := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero (x₀ := 0) (by norm_num)]
  intro h
  have hweighted : Integrable
      (fun x : ℝ ↦ x * (ProbabilityTheory.cauchyPDF 0 1 x).toReal) :=
    (integrable_withDensity_iff
      (ProbabilityTheory.measurable_cauchyPDF 0 1)
      (Filter.Eventually.of_forall fun x ↦ ENNReal.coe_lt_top)).1 h
  have hweightedOn : IntegrableOn
      (fun x : ℝ ↦ (2 * Real.pi) *
        (x * (ProbabilityTheory.cauchyPDF 0 1 x).toReal)) (Set.Ioi 1) :=
    hweighted.const_mul (2 * Real.pi) |>.integrableOn
  apply not_integrableOn_Ioi_inv (a := (1 : ℝ))
  change Integrable (fun x : ℝ ↦ x⁻¹) (volume.restrict (Set.Ioi 1))
  refine MeasureTheory.Integrable.mono hweightedOn ?_ ?_
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [ProbabilityTheory.cauchyPDF_def,
      ENNReal.toReal_ofReal
        (ProbabilityTheory.cauchyPDF_pos 0 (by norm_num) x).le,
      ProbabilityTheory.cauchyPDFReal_def]
    norm_num only [NNReal.smul_def, NNReal.coe_one, sub_zero, one_pow]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos), Real.norm_eq_abs]
    rw [abs_of_pos (by positivity :
      0 < 2 * Real.pi * (x * (Real.pi⁻¹ * 1 * (x ^ 2 + 1)⁻¹)))]
    have hsq : 1 < x ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hx) (by linarith : 0 < x + 1)]
    field_simp
    linarith

abbrev onlineCauchyCount : Count := ⟨1, by decide⟩

noncomputable def onlineCauchyProblem :
    RawOnlineProblem onlineCauchyCount onlineCauchyCount (fun _ ↦ ℝ) where
  sampleLoss _ ξ _ := ξ
  sampleLaw _ := ProbabilityTheory.cauchyMeasure 0 1
  sampleLaw_isProbability _ := inferInstance

noncomputable def rawStochasticGradient {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : RawOnlineProblem d n Sample) (i : Worker n) (ξ : Sample i)
    (x : Point d) : Point d :=
  gradient (P.sampleLoss i ξ) x

@[simp] theorem onlineCauchy_rawStochasticGradient
    (i : Worker onlineCauchyCount) (ξ : ℝ) (x : Point onlineCauchyCount) :
    rawStochasticGradient onlineCauchyProblem i ξ x = 0 := by
  unfold rawStochasticGradient onlineCauchyProblem gradient
  simp

/-- Explicit regularity boundary for treating the online stochastic gradient
as a random kernel at an adaptive query.  Assumptions 3.2--3.3 only state
fixed-query expectations, so this predicate is deliberately not a field of
`OnlineProblem` and is not silently folded into either source-facing Eq. (46)
theorem.  The conditional transition lemmas below identify exactly where a
separate realization of this source-unstated regularity would be consumed. -/
def OnlineGradientKernelRealization {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) : Prop :=
  ∀ i, Measurable (fun p : Point d × Sample i =>
    stochasticGradient P i p.2 p.1)

/-! The following finite countermodel records why the global predicate above
cannot be reconstructed from the paper's law-scoped moment assumptions.  The
sample law is concentrated at `support`, while the measurable space deliberately
does not distinguish `left` from `right`.  The sampled loss is zero on the
support and at `right`, but is a nonzero linear functional at `left`.  Thus all
expectations and gradient-difference moments in Assumptions 3.2--3.3 are zero,
for every query and even for every process, whereas global product
measurability would have to distinguish the two null sample values. -/

inductive OnlineKernelCounterSample
  | support
  | left
  | right
  deriving DecidableEq

def onlineKernelCounterPartition : OnlineKernelCounterSample → Bool
  | .support => false
  | .left => true
  | .right => true

instance : MeasurableSpace OnlineKernelCounterSample :=
  MeasurableSpace.comap onlineKernelCounterPartition ⊤

abbrev onlineKernelCounterCount : Count := ⟨1, by decide⟩

noncomputable def onlineKernelCounterDirection : Point onlineKernelCounterCount :=
  EuclideanSpace.single 0 1

noncomputable def onlineKernelCounterLoss
    (s : OnlineKernelCounterSample) (x : Point onlineKernelCounterCount) : ℝ :=
  if s = .left then
    (InnerProductSpace.toDual ℝ (Point onlineKernelCounterCount)
      onlineKernelCounterDirection) x
  else 0

theorem onlineKernelCounter_measurableSet_support :
    MeasurableSet ({OnlineKernelCounterSample.support} :
      Set OnlineKernelCounterSample) := by
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{false}, by simp, ?_⟩
  ext s
  cases s <;> simp [onlineKernelCounterPartition]

theorem onlineKernelCounter_ae_support :
    ∀ᵐ s ∂(Measure.dirac OnlineKernelCounterSample.support),
      s = OnlineKernelCounterSample.support := by
  rw [MeasureTheory.ae_dirac_iff]
  exact onlineKernelCounter_measurableSet_support

theorem onlineKernelCounter_integrable_of_support_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OnlineKernelCounterSample → E)
    (hf : f .support = 0) :
    Integrable f (Measure.dirac OnlineKernelCounterSample.support) := by
  have hzero : f =ᵐ[Measure.dirac OnlineKernelCounterSample.support]
      fun _ => 0 := by
    filter_upwards [onlineKernelCounter_ae_support] with s hs
    simpa [hs] using hf
  exact (integrable_const (c := (0 : E))).congr hzero.symm

theorem onlineKernelCounter_integral_eq_zero_of_support_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OnlineKernelCounterSample → E)
    (hf : f .support = 0) :
    (∫ s, f s ∂Measure.dirac OnlineKernelCounterSample.support) = 0 := by
  have hzero : f =ᵐ[Measure.dirac OnlineKernelCounterSample.support]
      fun _ => 0 := by
    filter_upwards [onlineKernelCounter_ae_support] with s hs
    simpa [hs] using hf
  rw [integral_congr_ae hzero]
  simp

noncomputable def onlineKernelCounterProblem :
    OnlineProblem onlineKernelCounterCount onlineKernelCounterCount
      (fun _ => OnlineKernelCounterSample) where
  sampleLoss _ := onlineKernelCounterLoss
  sampleLaw _ := Measure.dirac .support
  sampleLaw_isProbability _ := inferInstance
  sampleLoss_integrable i x := by
    apply onlineKernelCounter_integrable_of_support_zero
    simp [onlineKernelCounterLoss]

theorem onlineKernelCounter_gradient_left
    (x : Point onlineKernelCounterCount) :
    gradient (onlineKernelCounterLoss .left) x =
      onlineKernelCounterDirection := by
  have hgrad : HasGradientAt
      (fun y : Point onlineKernelCounterCount =>
        (InnerProductSpace.toDual ℝ (Point onlineKernelCounterCount)
          onlineKernelCounterDirection) y)
      onlineKernelCounterDirection x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (InnerProductSpace.toDual ℝ (Point onlineKernelCounterCount)
      onlineKernelCounterDirection).hasFDerivAt
  simpa [onlineKernelCounterLoss] using hgrad.gradient

theorem onlineKernelCounter_gradient_support
    (x : Point onlineKernelCounterCount) :
    gradient (onlineKernelCounterLoss .support) x = 0 := by
  rw [show onlineKernelCounterLoss .support = fun _ => 0 by
    funext y
    simp [onlineKernelCounterLoss]]
  exact gradient_fun_const x 0

theorem onlineKernelCounter_gradient_right
    (x : Point onlineKernelCounterCount) :
    gradient (onlineKernelCounterLoss .right) x = 0 := by
  rw [show onlineKernelCounterLoss .right = fun _ => 0 by
    funext y
    simp [onlineKernelCounterLoss]]
  exact gradient_fun_const x 0

/-- The existing global-kernel countermodel cannot also be the requested
law-scoped countermodel: its only nonmeasurable values are null under the
canonical sample law, and every fixed-query stochastic gradient is therefore
a genuine random variable under that law. -/
theorem onlineKernelCounter_stochasticGradient_aestronglyMeasurable
    (i : Worker onlineKernelCounterCount)
    (x : Point onlineKernelCounterCount) :
    AEStronglyMeasurable
      (fun s ↦ stochasticGradient onlineKernelCounterProblem i s x)
      (onlineKernelCounterProblem.sampleLaw i) := by
  have hzero :
      (fun s ↦ stochasticGradient onlineKernelCounterProblem i s x) =ᵐ[
        onlineKernelCounterProblem.sampleLaw i] fun _ ↦ 0 := by
    change (fun s ↦ stochasticGradient onlineKernelCounterProblem i s x) =ᵐ[
      Measure.dirac OnlineKernelCounterSample.support] fun _ ↦ 0
    filter_upwards [onlineKernelCounter_ae_support] with s hs
    subst s
    simpa [onlineKernelCounterProblem, stochasticGradient] using
      onlineKernelCounter_gradient_support x
  exact aestronglyMeasurable_const.congr hzero.symm


/-- `book/MARINA/MARINA.json#/algorithm_spec/variants/2` and
`#/algorithm_spec/parameters/0` and `#/algorithm_spec/parameters/2`:
online VR-MARINA uses stochastic-gradient
refresh minibatches, quantized stochastic-gradient-difference minibatches,
`p∈(0,1]`, and "`|I_{i,k}|=b, |I⁰_{i,k}|=b⁰<b`". -/
structure OnlineData (d n : Count) (Sample : Worker n → Type*) (Ξ : Type*)
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ] where
  problem : OnlineProblem d n Sample
  quantizer : Quantizer d Ξ
  stepSize : PositiveStepsize
  refreshProbability : ℝ
  refresh_admissible : RefreshProbabilityAdmissible refreshProbability

/-- `book/MARINA/MARINA.json#/key_lemmas/21` and `#/key_lemmas/23`:
"`p=min{ζ_Q/d,b⁰/(b+b⁰)}`", with respectively
"`b=Θ(σ²/(nε²))`" and "`b=Θ(σ²/(nμε))`", followed in each corollary by
an admissible bound on `γ`.  Rebuild Algorithm 3 data at both accuracy-
dependent parameters without changing its problem or quantizer. -/
def onlineDataWithParameters {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (γ : PositiveStepsize) (p : ℝ)
    (hp : RefreshProbabilityAdmissible p) : OnlineData d n Sample Ξ :=
  { problem := A.problem
    quantizer := A.quantizer
    stepSize := γ
    refreshProbability := p
    refresh_admissible := hp }

/-- Internal carrier for the printed initialization samples at
`book/MARINA/MARINA.json#/algorithm_spec/initialization/facts/2`. -/
structure OnlineInitialSamples (n b : Count) (Sample : Worker n → Type*) where
  sample : (i : Worker n) → Fin b.1 → Sample i

/-- Internal recursion carrier for the coordinates in
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/4`,
and `#/algorithm_spec/steps/5`; it adds no paper datum. -/
structure OnlineDriver (n b b0 : Count) (Sample : Worker n → Type*) (Ξ : Type*) where
  refresh : Bool
  refreshSample : (i : Worker n) → Fin b.1 → Sample i
  differenceSample : (i : Worker n) → Fin b0.1 → Sample i
  compressionSample : Worker n → Ξ

/-- Internal path carrier pairing the printed initialization at
`#/algorithm_spec/initialization/facts/2` with rounds from
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/4`,
and `#/algorithm_spec/steps/5`. -/
structure OnlinePath (n b b0 : Count) (Sample : Worker n → Type*) (Ξ : Type*) where
  initial : OnlineInitialSamples n b Sample
  round : ℕ → OnlineDriver n b b0 Sample Ξ

/-- Probability realization of the independently sampled `ξ_{ij}^k∼𝒟_i`
quoted at `book/MARINA/MARINA.json#/assumptions/10`. -/
noncomputable def onlineBatchLaw {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)] (P : OnlineProblem d n Sample)
    (batchSize : Count) : Measure ((i : Worker n) → Fin batchSize.1 → Sample i) :=
  Measure.infinitePi (fun i : Worker n =>
    Measure.infinitePi (fun _ : Fin batchSize.1 => P.sampleLaw i))

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/4`, and `#/algorithm_spec/steps/5`: distinct refresh
coin, refresh minibatch, difference minibatch, and compressor coordinates
realizing the quoted online VR transition. -/
abbrev OnlineRoundNoise (n b b0 : Count) (Sample : Worker n → Type*) (Ξ : Type*) :=
  Bool × ((((i : Worker n) → Fin b.1 → Sample i) ×
    ((i : Worker n) → Fin b0.1 → Sample i)) × (Worker n → Ξ))

/-- Canonical probability realization of
`book/MARINA/MARINA.json#/algorithm_spec/steps/0`, `#/algorithm_spec/steps/4`,
and `#/algorithm_spec/steps/5`.  Refresh samples,
difference samples, and compressor samples are distinct coordinates. -/
noncomputable def onlineRoundLaw {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) : Measure (OnlineRoundNoise n b b0 Sample Ξ) :=
  (refreshLaw A.refreshProbability A.refresh_admissible).prod
    (((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw A.quantizer))

/-- Joint-law realization of the printed initialization at
`book/MARINA/MARINA.json#/algorithm_spec/initialization/facts/2` and the
repeated online transition at `#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/4`, and `#/algorithm_spec/steps/5`. -/
noncomputable def onlinePathLaw {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure (((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) :=
  (onlineBatchLaw A.problem b).prod (SOptLib.iidStreamLaw (onlineRoundLaw A))

/-- Canonical round-only path law for the proof-exact Algorithm 3
interpretation, whose initialization has no sampling coordinate. -/
noncomputable def onlineProofExactPathLaw {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure (ℕ → OnlineRoundNoise n b b0 Sample Ξ) :=
  SOptLib.iidStreamLaw (onlineRoundLaw A)

def onlineDriverOfRoundNoise {n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    (z : OnlineRoundNoise n b b0 Sample Ξ) : OnlineDriver n b b0 Sample Ξ :=
  { refresh := z.1
    refreshSample := z.2.1.1
    differenceSample := z.2.1.2
    compressionSample := z.2.2 }

def onlinePathOfNoise {n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    (z : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) : OnlinePath n b b0 Sample Ξ :=
  { initial := { sample := z.1 }
    round := fun k => onlineDriverOfRoundNoise (z.2 k) }

/-- Each Algorithm 3 stochastic sample has its stated worker law `𝒟ᵢ`. -/
theorem onlinePathLaw_difference_marginal {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) (i : Worker n) (j : Fin b0.1) :
    Measure.map
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).2.1.2 i j)
      (onlinePathLaw A) = A.problem.sampleLaw i := by
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI :
      IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  have hbatch :
      Measure.map
          (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j)
          (onlineBatchLaw A.problem b0) = A.problem.sampleLaw i := by
    unfold onlineBatchLaw
    change Measure.map
        ((fun batch : Fin b0.1 → Sample i => batch j) ∘
          (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i))
        (Measure.infinitePi fun w : Worker n =>
          Measure.infinitePi fun _ : Fin b0.1 => A.problem.sampleLaw w) =
        A.problem.sampleLaw i
    rw [← MeasureTheory.Measure.map_map]
    · have houter :
          Measure.map
              (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i)
              (Measure.infinitePi fun w : Worker n =>
                Measure.infinitePi fun _ : Fin b0.1 => A.problem.sampleLaw w) =
            Measure.infinitePi (fun _ : Fin b0.1 => A.problem.sampleLaw i) := by
        simpa using
          (MeasureTheory.Measure.infinitePi_map_eval
            (μ := fun w : Worker n =>
              Measure.infinitePi fun _ : Fin b0.1 => A.problem.sampleLaw w) i)
      rw [houter]
      simpa using
        (MeasureTheory.Measure.infinitePi_map_eval
          (μ := fun _ : Fin b0.1 => A.problem.sampleLaw i) j)
    · exact measurable_pi_apply j
    · exact measurable_pi_apply i
  have hpathRound :
      Measure.map
          (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k)
          (onlinePathLaw A) = onlineRoundLaw A := by
    calc
      Measure.map
          (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k)
          (onlinePathLaw A) =
          Measure.map (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
              stream k) (Measure.map Prod.snd (onlinePathLaw A)) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.map_map (measurable_pi_apply k) measurable_snd
            (μ := onlinePathLaw A)).symm
      _ = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ => stream k)
          (SOptLib.iidStreamLaw (onlineRoundLaw A)) := by
        unfold onlinePathLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      _ = onlineRoundLaw A := SOptLib.iidStreamLaw_map_eval (onlineRoundLaw A) k
  have hPairLaw :
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1)
          (onlineRoundLaw A) =
        (onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0) := by
    calc
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1)
          (onlineRoundLaw A) =
          Measure.map Prod.fst (Measure.map Prod.snd (onlineRoundLaw A)) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.map_map measurable_fst measurable_snd
            (μ := onlineRoundLaw A)).symm
      _ = Measure.map Prod.fst
          (((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
            (workerCompressionLaw A.quantizer)) := by
        unfold onlineRoundLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      _ = (onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0) := by
        rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  have hroundBatch :
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
          (onlineRoundLaw A) = onlineBatchLaw A.problem b0 := by
    calc
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
          (onlineRoundLaw A) =
          Measure.map Prod.snd
            (Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1)
              (onlineRoundLaw A)) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.map_map measurable_snd
            (measurable_fst.comp measurable_snd) (μ := onlineRoundLaw A)).symm
      _ = Measure.map Prod.snd
          ((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)) := by
        rw [hPairLaw]
      _ = onlineBatchLaw A.problem b0 := by
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map
        (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).2.1.2 i j)
        (onlinePathLaw A) =
        Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2 i j)
          (Measure.map
            (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
                (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k)
            (onlinePathLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          ((measurable_pi_apply j).comp
            ((measurable_pi_apply i).comp
              (measurable_snd.comp (measurable_fst.comp measurable_snd))))
          ((measurable_pi_apply k).comp measurable_snd)
          (μ := onlinePathLaw A)).symm
    _ = Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2 i j)
        (onlineRoundLaw A) := by
      rw [hpathRound]
    _ = Measure.map
        (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j)
        (Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
          (onlineRoundLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          ((measurable_pi_apply j).comp (measurable_pi_apply i))
          (measurable_snd.comp (measurable_fst.comp measurable_snd))
          (μ := onlineRoundLaw A)).symm
    _ = Measure.map
        (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j)
        (onlineBatchLaw A.problem b0) := by
      rw [hroundBatch]
    _ = A.problem.sampleLaw i := hbatch

/-- The two Algorithm 3 minibatches are independent under the canonical round law. -/
theorem onlineRoundLaw_batches_independent {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    ProbabilityTheory.IndepFun
      (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
      (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
      (onlineRoundLaw A) := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI :
      IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  have hPairLaw :
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1)
        (onlineRoundLaw A) =
          (onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0) := by
    calc
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1)
          (onlineRoundLaw A) =
          Measure.map Prod.fst (Measure.map Prod.snd (onlineRoundLaw A)) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.map_map measurable_fst measurable_snd
            (μ := onlineRoundLaw A)).symm
      _ = Measure.map Prod.fst
          (((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
            (workerCompressionLaw A.quantizer)) := by
        unfold onlineRoundLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      _ = (onlineBatchLaw A.problem b).prod
          (onlineBatchLaw A.problem b0) := by
        rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  exact indepFun_of_map_prod_eq_prod_laws
    ((measurable_fst.comp measurable_snd).aemeasurable) hPairLaw

/-- A complete Algorithm 3 refresh minibatch has the canonical product law.
This law-level projection is used below to separate the genuine fixed-query
random-variable facts in Assumption 3.3 from the still-missing adaptive
product-measurability step. -/
theorem onlineRoundLaw_refreshBatch_marginal {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
        (onlineRoundLaw A) = onlineBatchLaw A.problem b := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  have hsnd :
      Measure.map Prod.snd (onlineRoundLaw A) =
        ((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
          (workerCompressionLaw A.quantizer) := by
    unfold onlineRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
        (onlineRoundLaw A) =
        Measure.map (fun q => q.1.1) (Measure.map Prod.snd (onlineRoundLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          (measurable_fst.comp measurable_fst) measurable_snd
          (μ := onlineRoundLaw A)).symm
    _ = Measure.map (fun q => q.1.1)
        (((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
          (workerCompressionLaw A.quantizer)) := by rw [hsnd]
    _ = Measure.map Prod.fst
        (Measure.map Prod.fst
          (((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
            (workerCompressionLaw A.quantizer))) := by
      rw [MeasureTheory.Measure.map_map measurable_fst measurable_fst]
      rfl
    _ = Measure.map Prod.fst
        ((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)) := by
      rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
    _ = onlineBatchLaw A.problem b := by
      rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]

/-- A complete Algorithm 3 difference minibatch has the canonical product
law, independently of the refresh coin and the other round coordinates. -/
theorem onlineRoundLaw_differenceBatch_marginal {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
        (onlineRoundLaw A) = onlineBatchLaw A.problem b0 := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  have hsnd :
      Measure.map Prod.snd (onlineRoundLaw A) =
        ((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
          (workerCompressionLaw A.quantizer) := by
    unfold onlineRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
        (onlineRoundLaw A) =
        Measure.map (fun q => q.1.2) (Measure.map Prod.snd (onlineRoundLaw A)) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.map_map
          (measurable_snd.comp measurable_fst) measurable_snd
          (μ := onlineRoundLaw A)).symm
    _ = Measure.map (fun q => q.1.2)
        (((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
          (workerCompressionLaw A.quantizer)) := by rw [hsnd]
    _ = Measure.map Prod.snd
        (Measure.map Prod.fst
          (((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)).prod
            (workerCompressionLaw A.quantizer))) := by
      rw [MeasureTheory.Measure.map_map measurable_snd measurable_fst]
      rfl
    _ = Measure.map Prod.snd
        ((onlineBatchLaw A.problem b).prod (onlineBatchLaw A.problem b0)) := by
      rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
    _ = onlineBatchLaw A.problem b0 := by
      rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]

/-- One coordinate of a canonical online minibatch has the worker law `𝒟ᵢ`.
This is the finite-product marginal used to lift the fixed-query
integrability in Assumption 3.3 to a complete refresh minibatch. -/
theorem onlineBatchLaw_coordinate_marginal {d n b : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) (j : Fin b.1) :
    Measure.map
        (fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j)
        (onlineBatchLaw P b) = P.sampleLaw i := by
  letI (w : Worker n) : IsProbabilityMeasure (P.sampleLaw w) :=
    P.sampleLaw_isProbability w
  unfold onlineBatchLaw
  change Measure.map
      ((fun row : Fin b.1 → Sample i => row j) ∘
        (fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i))
      (Measure.infinitePi fun w : Worker n =>
        Measure.infinitePi fun _ : Fin b.1 => P.sampleLaw w) = P.sampleLaw i
  rw [← MeasureTheory.Measure.map_map (measurable_pi_apply j)
    (measurable_pi_apply i)]
  rw [MeasureTheory.Measure.infinitePi_map_eval]
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun _ : Fin b.1 => P.sampleLaw i) j)

/-- The complete minibatch row of one worker has its canonical finite product
law.  This is the worker-level marginal used in the covariance calculation
for the nonrefresh branch of Eq. (46). -/
theorem onlineBatchLaw_worker_marginal {d n b : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) :
    Measure.map
        (fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i)
        (onlineBatchLaw P b) =
      Measure.infinitePi (fun _ : Fin b.1 => P.sampleLaw i) := by
  letI (w : Worker n) : IsProbabilityMeasure (P.sampleLaw w) :=
    P.sampleLaw_isProbability w
  unfold onlineBatchLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun w : Worker n =>
        Measure.infinitePi (fun _ : Fin b.1 => P.sampleLaw w)) i)

/-- `book/MARINA/MARINA.json#/algorithm_spec/parameters/2`:
"`|I_{i,k}|=b, |I⁰_{i,k}|=b⁰<b`". -/
def OnlineBatchAdmissible (b b0 : Count) : Prop := b0.1 < b.1

/-- The formula printed on Algorithm 3 line 2, made well-scoped by exposing
its otherwise-unbound evaluation point as an explicit argument. -/
noncomputable def onlinePrintedInitialEstimatorAt
    {d n b : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (z : OnlineInitialSamples n b Sample)
    (xEval : Point d) : Point d :=
  average (fun i : Worker n => average (fun j : Fin b.1 =>
    stochasticGradient A.problem i (z.sample i j) xEval))

/-- Well-scoped executable initialization obtained by evaluating Algorithm 3's
initial minibatch at the input point `x⁰`. This is deliberately distinct from
the malformed printed expression and from the proof's exact-gradient claim. -/
noncomputable def onlineInitialState {d n b : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (z : OnlineInitialSamples n b Sample)
    (x0 : Point d) : State d :=
  { x := x0, g := onlinePrintedInitialEstimatorAt A z x0 }

/-- `book/MARINA/MARINA.json#/algorithm_spec/initialization/facts/3`:
"`g^0=∇f(x^0)`" in the proof of Theorem 3.2.  This is deliberately separate
from both the malformed printed initialization and the corrected executable
minibatch-at-`x⁰` interpretation. -/
noncomputable def onlineProofExactInitialState {d n : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) : State d :=
  { x := x0, g := globalGradient (onlineLocalProblem A.problem) x0 }

/-- Explicit source-boundary tags for the three non-identical Algorithm 3
initialization interpretations. -/
inductive OnlineInitializationInterpretation
  | printedLiteral
  | proofExact
  | correctedExecutable

/-- The active executable process uses `correctedExecutable`; theorem heads
claiming the proof's `g⁰=∇f(x⁰)` must instead name `proofExact`. -/
def onlineExecutableInitialization : OnlineInitializationInterpretation :=
  .correctedExecutable

/-- `book/MARINA/MARINA.json#/assumptions/5`: the stochastic minibatch
approximation "`Δ̃_i^k=b⁰⁻¹∑_j(∇f_{ξ_{ij}^k}(x^{k+1})-
∇f_{ξ_{ij}^k}(x^k))`" from Assumption 3.2. -/
noncomputable def onlineBatchDifference {d n b0 : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample)
    (batch : (i : Worker n) → Fin b0.1 → Sample i)
    (i : Worker n) (xNext x : Point d) : Point d :=
  average (fun j : Fin b0.1 =>
    stochasticGradient P i (batch i j) xNext -
      stochasticGradient P i (batch i j) x)

/-- With the minibatch fixed, Assumption 3.2's stochastic-gradient
difference is measurable in its two queries.  The proof bottoms out in
Mathlib's `measurable_fderiv`; it therefore removes query-section
measurability from the Eq. (46) reconstruction gap without postulating a
joint stochastic-oracle kernel. -/
theorem onlineBatchDifference_queryPair_measurable
    {d n b0 : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample)
    (batch : (w : Worker n) → Fin b0.1 → Sample w)
    (i : Worker n) :
    Measurable (fun q : Point d × Point d ↦
      onlineBatchDifference P batch i q.1 q.2) := by
  classical
  unfold onlineBatchDifference average SOptLib.finiteUniformAverage
  exact (Finset.measurable_sum Finset.univ (fun j _ =>
    ((stochasticGradient_query_measurable P i (batch i j)).comp measurable_fst).sub
      ((stochasticGradient_query_measurable P i (batch i j)).comp
        measurable_snd))).const_smul
    ((Fintype.card (Fin b0.1) : ℝ)⁻¹)

/-- Conditional Algorithm 3 analogue of
`finiteSumBatchDifference_joint_measurable`.  Unlike the finite component
index, an arbitrary online sample space does not permit finite measurable
dispatch, so the proof consumes the explicit kernel-realization boundary. -/
theorem onlineBatchDifference_joint_measurable_of_kernel
    {d n b0 : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (hKernel : OnlineGradientKernelRealization P)
    (i : Worker n) :
    Measurable (fun p : (Point d × Point d) ×
        ((w : Worker n) → Fin b0.1 → Sample w) =>
      onlineBatchDifference P p.2 i p.1.1 p.1.2) := by
  classical
  have hterm (j : Fin b0.1) :
      Measurable (fun p : (Point d × Point d) ×
          ((w : Worker n) → Fin b0.1 → Sample w) =>
        stochasticGradient P i (p.2 i j) p.1.1 -
          stochasticGradient P i (p.2 i j) p.1.2) := by
    have hsample : Measurable (fun p : (Point d × Point d) ×
        ((w : Worker n) → Fin b0.1 → Sample w) => p.2 i j) :=
      (measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp measurable_snd)
    exact (hKernel i).comp
        ((measurable_fst.comp measurable_fst).prodMk hsample) |>.sub
      ((hKernel i).comp
        ((measurable_snd.comp measurable_fst).prodMk hsample))
  unfold onlineBatchDifference average SOptLib.finiteUniformAverage
  exact (Finset.measurable_sum Finset.univ (fun j _ => hterm j)).const_smul
    ((Fintype.card (Fin b0.1) : ℝ)⁻¹)

/-- `book/MARINA/MARINA.json#/assumptions/5`, Assumption 3.2 / Eq. (8),
scoped to the canonical `𝒟ᵢ` minibatch law with nonfallback moments. -/
def OnlineAverageSmoothness {d n b0 : Count}
    {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k i (path : Ω),
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      Integrable (fun batch => onlineBatchDifference P batch i xNext x)
        (onlineBatchLaw P b0) ∧
      Integrable (fun batch =>
        ‖onlineBatchDifference P batch i xNext x -
          localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2)
        (onlineBatchLaw P b0) ∧
      (∫ batch, onlineBatchDifference P batch i xNext x ∂onlineBatchLaw P b0) =
        localGradientDifference (onlineLocalProblem P) i xNext x ∧
      (∫ batch,
          ‖onlineBatchDifference P batch i xNext x -
            localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2
          ∂onlineBatchLaw P b0) ≤
        (ℒ i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)

/-- The fixed-query moment equations underlying Assumption 3.3, isolated as a
legacy diagnostic boundary.  On its own this predicate permits Mathlib's
totalized gradient at nondifferentiability points and is therefore not the
paper-facing interpretation of the displayed random variables `∇f_{ξᵢ}(x)`. -/
def LegacyOnlineFixedQueryUnbiasedBoundedVariance {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (σ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ σ i) ∧
    (∀ i x,
      Integrable (fun ξ => stochasticGradient P i ξ x) (P.sampleLaw i) ∧
      Integrable (fun ξ =>
        ‖stochasticGradient P i ξ x - localGradient (onlineLocalProblem P) i x‖ ^ 2)
        (P.sampleLaw i) ∧
      (∫ ξ, stochasticGradient P i ξ x ∂P.sampleLaw i) =
        localGradient (onlineLocalProblem P) i x ∧
      (∫ ξ,
          ‖stochasticGradient P i ξ x - localGradient (onlineLocalProblem P) i x‖ ^ 2
        ∂P.sampleLaw i) ≤ (σ i) ^ 2)

/-- `book/MARINA/MARINA.json#/assumptions/6`, Assumption 3.3 / Eqs. (9)-(10).
The paper quantifies the random variables `∇f_{ξᵢ}(x)` themselves, so their
sample losses must genuinely possess those gradients (up to the sampling
law's null sets).  The first conjunct records the displayed fixed-query
moments; the second rules out Lean's totalized-gradient fallback and derives
the law-scoped adaptive-query measurability needed by Algorithm 3. -/
def OnlineUnbiasedBoundedVariance {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (σ : Worker n → ℝ) : Prop :=
  LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ ∧
    OnlineSampleLossDifferentiable P

/-- Assumption 3.3 projected to its fixed-query moment equations. -/
theorem legacyOnlineFixedQueryVariance_of_variance {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {σ : Worker n → ℝ}
    (h : OnlineUnbiasedBoundedVariance P σ) :
    LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ :=
  h.1

/-- Assumption 3.3 projected to the genuine sampled-gradient semantics of its
displayed random variables. -/
theorem onlineSampleLossDifferentiable_of_variance {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {σ : Worker n → ℝ}
    (h : OnlineUnbiasedBoundedVariance P σ) :
    OnlineSampleLossDifferentiable P :=
  h.2

/-- B-track Assumption 3.2 over the nonfallback Eq. (6) realization. -/
def OnlineAverageSmoothnessCorrected {d n b0 : Count}
    {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k i (path : Ω),
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      Integrable (fun batch => onlineBatchDifference P.1 batch i xNext x)
        (onlineBatchLaw P.1 b0) ∧
      Integrable (fun batch =>
        ‖onlineBatchDifference P.1 batch i xNext x -
          localGradientDifference (onlineLocalProblemCorrected P) i xNext x‖ ^ 2)
        (onlineBatchLaw P.1 b0) ∧
      (∫ batch, onlineBatchDifference P.1 batch i xNext x
          ∂onlineBatchLaw P.1 b0) =
        localGradientDifference (onlineLocalProblemCorrected P) i xNext x ∧
      (∫ batch,
          ‖onlineBatchDifference P.1 batch i xNext x -
            localGradientDifference (onlineLocalProblemCorrected P) i xNext x‖ ^ 2
          ∂onlineBatchLaw P.1 b0) ≤
        (ℒ i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)

/-- Compatibility spelling for the former corrected B-track.  The canonical
Assumption 3.3 boundary now already includes genuine sampled-gradient
semantics, so this alias adds no assumption. -/
abbrev OnlineUnbiasedBoundedVarianceCorrected {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) (σ : Worker n → ℝ) : Prop :=
  OnlineUnbiasedBoundedVariance P.1 σ

/-- The corrected spelling is definitionally the canonical Assumption 3.3
predicate on the underlying online problem. -/
theorem onlineUnbiasedBoundedVarianceCorrected_iff {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) (σ : Worker n → ℝ) :
    OnlineUnbiasedBoundedVarianceCorrected P σ ↔
      OnlineUnbiasedBoundedVariance P.1 σ := by
  rfl

/-- Compatibility projection of the intrinsic law-a.e. differentiability
realization from the corrected spelling of the variance predicate. -/
theorem onlineSampleLossDifferentiable_of_varianceCorrected
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) (σ : Worker n → ℝ)
    (h : OnlineUnbiasedBoundedVarianceCorrected P σ) :
    OnlineSampleLossDifferentiable P.1 :=
  onlineSampleLossDifferentiable_of_variance h

/-- Fixed generated-pair fibers projected from Assumption 3.2's conditional
interface. -/
theorem onlineAverageSmoothnessCorrected_fixed
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : RealizedOnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ)
    (h : OnlineAverageSmoothnessCorrected (b0 := b0) P run ℒ) :
    ∀ k i (path : Ω),
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      Integrable (fun batch => onlineBatchDifference P.1 batch i xNext x)
          (onlineBatchLaw P.1 b0) ∧
        Integrable (fun batch =>
          ‖onlineBatchDifference P.1 batch i xNext x -
            localGradientDifference (onlineLocalProblemCorrected P) i xNext x‖ ^ 2)
          (onlineBatchLaw P.1 b0) ∧
        (∫ batch, onlineBatchDifference P.1 batch i xNext x
            ∂onlineBatchLaw P.1 b0) =
          localGradientDifference (onlineLocalProblemCorrected P) i xNext x ∧
        (∫ batch,
            ‖onlineBatchDifference P.1 batch i xNext x -
              localGradientDifference (onlineLocalProblemCorrected P) i xNext x‖ ^ 2
            ∂onlineBatchLaw P.1 b0) ≤
          (ℒ i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2 := by
  exact h.2

/-- The raw sample-loss and probability-law data do not by themselves imply
the Eq. (6) realization required by `OnlineProblem`.  With a standard Cauchy
sample and the constant-in-query loss `f_ξ(x)=ξ`, all sampled gradients are
zero while the sampled loss is not integrable.  This witness intentionally
lives at `RawOnlineProblem`, outside Algorithm 3's source-facing carrier. -/
theorem onlineExpectationRealization_cauchy_not_derivable :
    ∃ (P : RawOnlineProblem onlineCauchyCount onlineCauchyCount (fun _ ↦ ℝ)),
      (∀ i ξ x, rawStochasticGradient P i ξ x = 0) ∧
      ¬ (∀ i x, Integrable (fun ξ ↦ P.sampleLoss i ξ x) (P.sampleLaw i)) := by
  refine ⟨onlineCauchyProblem, ?_, ?_⟩
  · exact onlineCauchy_rawStochasticGradient
  · intro hE
    exact identity_not_integrable_cauchy (hE 0 0)

/-- Fixed-query and fixed-run moment assumptions do not imply the global
stochastic-gradient kernel realization.  This finite countermodel satisfies
the corrected Eq. (6), local smoothness, Assumption 3.3, and Assumption 3.2
for every generated process, but differs on two sample values that its law
never observes and its measurable space cannot distinguish.  Hence the
global premise proposed for online Eq. (46) is strictly stronger than the
source assumptions; a faithful completion must instead use a law-scoped
measurability theorem or record the missing probability regularity. -/
theorem onlineGradientKernelRealization_not_derivable_from_source_moments :
    ∃ (P : OnlineProblem onlineKernelCounterCount onlineKernelCounterCount
        (fun _ => OnlineKernelCounterSample))
      (hE : OnlineExpectationRealization P),
      IsLocallySmooth (onlineLocalProblemCorrected ⟨P, hE⟩) (fun _ => 0) ∧
      OnlineUnbiasedBoundedVarianceCorrected ⟨P, hE⟩ (fun _ => 0) ∧
      (∀ {b0 : Count} {Omega : Type*} [MeasurableSpace Omega]
        (run : ℕ → Omega → State onlineKernelCounterCount),
        (∀ k, Measurable (run k)) →
        OnlineAverageSmoothnessCorrected (b0 := b0) ⟨P, hE⟩ run
          (fun _ => 0)) ∧
      ¬ OnlineGradientKernelRealization P := by
  let P := onlineKernelCounterProblem
  have hE : OnlineExpectationRealization P := by
    intro i x
    apply onlineKernelCounter_integrable_of_support_zero
    simp [P, onlineKernelCounterProblem, onlineKernelCounterLoss]
  refine ⟨P, hE, ?_, ?_, ?_, ?_⟩
  · have hlocal : ∀ i,
        (onlineLocalProblemCorrected ⟨P, hE⟩).localLoss i = fun _ => 0 := by
      intro i
      funext x
      apply onlineKernelCounter_integral_eq_zero_of_support_zero
      simp [P, onlineKernelCounterProblem, onlineKernelCounterLoss]
    constructor
    · intro i
      rw [hlocal i]
      fun_prop
    · intro i x y
      simp [localGradient, hlocal i]
  · constructor
    · constructor
      · intro i
        exact le_rfl
      · intro i x
        have hlocal :
            localGradient (onlineLocalProblemCorrected ⟨P, hE⟩) i x = 0 := by
          unfold localGradient onlineLocalProblemCorrected
          simp only
          have hfun : (fun x : Point onlineKernelCounterCount =>
              ∫ s, P.sampleLoss i s x ∂P.sampleLaw i) = fun _ => 0 := by
            funext y
            apply onlineKernelCounter_integral_eq_zero_of_support_zero
            simp [P, onlineKernelCounterProblem, onlineKernelCounterLoss]
          rw [hfun]
          simp
        have hsample : stochasticGradient P i .support x = 0 := by
          simpa [P, onlineKernelCounterProblem, stochasticGradient] using
            onlineKernelCounter_gradient_support x
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact onlineKernelCounter_integrable_of_support_zero
            (fun s => stochasticGradient P i s x) hsample
        · exact onlineKernelCounter_integrable_of_support_zero
            (fun s =>
              ‖stochasticGradient P i s x -
                localGradient (onlineLocalProblemCorrected ⟨P, hE⟩) i x‖ ^ 2)
            (by simp [hsample, hlocal])
        · change (∫ s, stochasticGradient P i s x
            ∂Measure.dirac OnlineKernelCounterSample.support) =
          localGradient (onlineLocalProblemCorrected ⟨P, hE⟩) i x
          rw [onlineKernelCounter_integral_eq_zero_of_support_zero
            (fun s => stochasticGradient P i s x) hsample]
          exact hlocal.symm
        · change (∫ s,
            ‖stochasticGradient P i s x -
              localGradient (onlineLocalProblemCorrected ⟨P, hE⟩) i x‖ ^ 2
            ∂Measure.dirac OnlineKernelCounterSample.support) ≤ 0 ^ 2
          rw [onlineKernelCounter_integral_eq_zero_of_support_zero
            (fun s =>
              ‖stochasticGradient P i s x -
                localGradient (onlineLocalProblemCorrected ⟨P, hE⟩) i x‖ ^ 2)
            (by simp [hsample, hlocal])]
          norm_num
    · intro i
      apply Filter.Eventually.of_forall
      intro s
      change Differentiable ℝ (onlineKernelCounterLoss s)
      cases s with
      | support =>
          have hzero : onlineKernelCounterLoss .support = fun _ => 0 := by
            funext x
            simp [onlineKernelCounterLoss]
          rw [hzero]
          fun_prop
      | left =>
          simpa [onlineKernelCounterLoss] using
            (innerSL ℝ onlineKernelCounterDirection).differentiable
      | right =>
          have hzero : onlineKernelCounterLoss .right = fun _ => 0 := by
            funext x
            simp [onlineKernelCounterLoss]
          rw [hzero]
          fun_prop
  · intro b0 Omega _ run hrun
    constructor
    · intro i
      exact le_rfl
    · intro k i path
      dsimp
      have hgrad (s : OnlineKernelCounterSample)
          (x y : Point onlineKernelCounterCount) :
          stochasticGradient P i s x = stochasticGradient P i s y := by
          cases s with
          | support =>
              simpa [P, onlineKernelCounterProblem, stochasticGradient] using
                (onlineKernelCounter_gradient_support x).trans
                  (onlineKernelCounter_gradient_support y).symm
          | left =>
              simpa [P, onlineKernelCounterProblem, stochasticGradient] using
                (onlineKernelCounter_gradient_left x).trans
                  (onlineKernelCounter_gradient_left y).symm
          | right =>
              simpa [P, onlineKernelCounterProblem, stochasticGradient] using
                (onlineKernelCounter_gradient_right x).trans
                  (onlineKernelCounter_gradient_right y).symm
      have hbatch : ∀ (batch : (w : Worker onlineKernelCounterCount) →
            Fin b0.1 → OnlineKernelCounterSample),
            onlineBatchDifference P batch i (run (k + 1) path).x
                (run k path).x = 0 := by
          intro batch
          unfold onlineBatchDifference
          have hzero : (fun j : Fin b0.1 =>
              stochasticGradient P i (batch i j) (run (k + 1) path).x -
                stochasticGradient P i (batch i j) (run k path).x) =
              fun _ => 0 := by
            funext j
            exact sub_eq_zero.mpr (hgrad (batch i j) _ _)
          rw [hzero]
          simp [average, SOptLib.finiteUniformAverage]
      have hlocalDiff :
            localGradientDifference (onlineLocalProblemCorrected ⟨P, hE⟩) i
                (run (k + 1) path).x (run k path).x = 0 := by
          unfold localGradientDifference localGradient onlineLocalProblemCorrected
          simp only
          have hfun : (fun x : Point onlineKernelCounterCount =>
              ∫ s, P.sampleLoss i s x ∂P.sampleLaw i) = fun _ => 0 := by
            funext y
            apply onlineKernelCounter_integral_eq_zero_of_support_zero
            simp [P, onlineKernelCounterProblem, onlineKernelCounterLoss]
          rw [hfun]
          simp
      simp [hbatch, hlocalDiff]
  · intro hKernel
    let x : Point onlineKernelCounterCount := 0
    let i : Worker onlineKernelCounterCount := 0
    have hslice : Measurable
        (fun s : OnlineKernelCounterSample => stochasticGradient P i s x) :=
      (hKernel i).comp ((measurable_const : Measurable fun _ => x).prodMk measurable_id)
    let v := onlineKernelCounterDirection
    have hpre : MeasurableSet
        ((fun s : OnlineKernelCounterSample => stochasticGradient P i s x) ⁻¹'
          ({v} : Set (Point onlineKernelCounterCount))) :=
      hslice (measurableSet_singleton v)
    rcases MeasurableSpace.measurableSet_comap.mp hpre with ⟨t, _ht, ht⟩
    have hsame :
        OnlineKernelCounterSample.left ∈
            ((fun s : OnlineKernelCounterSample => stochasticGradient P i s x) ⁻¹'
              ({v} : Set (Point onlineKernelCounterCount))) ↔
          OnlineKernelCounterSample.right ∈
            ((fun s : OnlineKernelCounterSample => stochasticGradient P i s x) ⁻¹'
              ({v} : Set (Point onlineKernelCounterCount))) := by
      rw [← ht]
      simp [onlineKernelCounterPartition]
    have hvne : onlineKernelCounterDirection ≠ 0 := by
      intro hv
      have hz := congrArg (fun z : Point onlineKernelCounterCount => z 0) hv
      simpa [onlineKernelCounterDirection] using hz
    have hleft : stochasticGradient P i .left x = v := by
      simpa [P, onlineKernelCounterProblem, stochasticGradient, v] using
        onlineKernelCounter_gradient_left x
    have hright : stochasticGradient P i .right x = 0 := by
      simpa [P, onlineKernelCounterProblem, stochasticGradient] using
        onlineKernelCounter_gradient_right x
    have hrmem := hsame.mp (by simp [hleft])
    have hzeroeq : (0 : Point onlineKernelCounterCount) = v := by
      simpa [hright] using hrmem
    exact hvne hzeroeq.symm

/-- `book/MARINA/MARINA.json#/key_lemmas/15`, Remark D.1's replacement
`n⁻¹∑ᵢ ℒᵢ²/b⁰ᵢ` for heterogeneous finite-sum batches. -/
noncomputable def heterogeneousFiniteBatchSmoothnessTerm {n : Count}
    (ℒ : Worker n → ℝ) (b0 : Worker n → Count) : ℝ :=
  average (fun i : Worker n => (ℒ i) ^ 2 / (b0 i).1)

/-- `book/MARINA/MARINA.json#/key_lemmas/15`: Remark D.1 uses
"different batchsizes `b⁰_1,…,b⁰_n` on different workers". -/
abbrev HeterogeneousFiniteSumBatch (n m : Count) (b0 : Worker n → Count) :=
  (i : Worker n) → Fin (b0 i).1 → Component m

/-- A round-indexed law for Remark D.1's worker-dependent minibatches. -/
abbrev HeterogeneousFiniteSumBatchLaw (n m : Count) (b0 : Worker n → Count) :=
  ℕ → Measure (HeterogeneousFiniteSumBatch n m b0)

/-- Remark D.1's worker-`i` minibatch gradient difference. -/
noncomputable def heterogeneousFiniteSumBatchDifference {d n m : Count}
    (P : FiniteSumProblem d n m) (b0 : Worker n → Count)
    (batch : HeterogeneousFiniteSumBatch n m b0) (i : Worker n)
    (xNext x : Point d) : Point d :=
  average (fun j : Fin (b0 i).1 =>
    componentGradient P i (batch i j) xNext - componentGradient P i (batch i j) x)

/-- The iterate-conditional Assumption 3.1 contract for Remark D.1's
heterogeneous batches. -/
def HeterogeneousFiniteSumAverageSmoothness {d n m : Count} {Ω : Type*}
    (P : FiniteSumProblem d n m) (b0 : Worker n → Count)
    (batchLaw : HeterogeneousFiniteSumBatchLaw n m b0)
    (run : ℕ → Ω → State d) (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧ ∀ k i (path : Ω),
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    Integrable (fun batch => heterogeneousFiniteSumBatchDifference P b0 batch i xNext x)
      (batchLaw k) ∧
    Integrable (fun batch =>
      ‖heterogeneousFiniteSumBatchDifference P b0 batch i xNext x -
        localGradientDifference (finiteSumLocalProblem P) i xNext x‖ ^ 2)
      (batchLaw k) ∧
    (∫ batch, heterogeneousFiniteSumBatchDifference P b0 batch i xNext x
      ∂batchLaw k) = localGradientDifference (finiteSumLocalProblem P) i xNext x ∧
    (∫ batch, ‖heterogeneousFiniteSumBatchDifference P b0 batch i xNext x -
        localGradientDifference (finiteSumLocalProblem P) i xNext x‖ ^ 2
      ∂batchLaw k) ≤ (ℒ i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2

theorem average_le_average_of_pointwise {n : Count}
    {f g : Worker n → ℝ} (h : ∀ i, f i ≤ g i) :
    average f ≤ average g := by
  unfold average
  simp only [SOptLib.finiteUniformAverage_def, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _hi => h i)) (by positivity)

/-- `book/MARINA/MARINA.json#/key_lemmas/15`, Remark D.1: the
worker-averaged conditional variance uses `n⁻¹∑ᵢ ℒᵢ²/b⁰ᵢ`. -/
theorem heterogeneousFiniteSum_average_secondMoment_le
    {d n m : Count} {Ω : Type*} (P : FiniteSumProblem d n m)
    (b0 : Worker n → Count) (batchLaw : HeterogeneousFiniteSumBatchLaw n m b0)
    (run : ℕ → Ω → State d) (ℒ : Worker n → ℝ)
    (h : HeterogeneousFiniteSumAverageSmoothness P b0 batchLaw run ℒ)
    (k : ℕ) (path : Ω) :
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    average (fun i : Worker n =>
      ∫ batch, ‖heterogeneousFiniteSumBatchDifference P b0 batch i xNext x -
        localGradientDifference (finiteSumLocalProblem P) i xNext x‖ ^ 2
      ∂batchLaw k) ≤
      heterogeneousFiniteBatchSmoothnessTerm ℒ b0 * ‖xNext - x‖ ^ 2 := by
  dsimp
  have hAverage := average_le_average_of_pointwise
    (fun i => (h.2 k i path).2.2.2)
  calc
    average (fun i : Worker n =>
        ∫ batch, ‖heterogeneousFiniteSumBatchDifference P b0 batch i
          (run (k + 1) path).x (run k path).x -
          localGradientDifference (finiteSumLocalProblem P) i
            (run (k + 1) path).x (run k path).x‖ ^ 2 ∂batchLaw k) ≤
        average (fun i : Worker n =>
          (ℒ i) ^ 2 / (b0 i).1 *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) := hAverage
    _ = heterogeneousFiniteBatchSmoothnessTerm ℒ b0 *
          ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 := by
      unfold heterogeneousFiniteBatchSmoothnessTerm average
      simp only [SOptLib.finiteUniformAverage_def, smul_eq_mul]
      rw [← Finset.sum_mul]
      ring

/-- `book/MARINA/MARINA.json#/key_lemmas/20`, Remark D.2's heterogeneous
online variance term `n⁻²∑ᵢ σᵢ²/bᵢ`. -/
noncomputable def heterogeneousOnlineVarianceTerm {n : Count}
    (σ : Worker n → ℝ) (b : Worker n → Count) : ℝ :=
  average (fun i : Worker n => (σ i) ^ 2 / (b i).1) / n.1

/-- `book/MARINA/MARINA.json#/key_lemmas/20`: Remark D.2 uses
worker-dependent "`b_1,…,b_n` and `b⁰_1,…,b⁰_n`". -/
abbrev HeterogeneousOnlineBatch (n : Count) (Sample : Worker n → Type*)
    (size : Worker n → Count) :=
  (i : Worker n) → Fin (size i).1 → Sample i

/-- Remark D.2's conditional difference minibatch. -/
noncomputable def heterogeneousOnlineBatchDifference {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (b0 : Worker n → Count)
    (batch : HeterogeneousOnlineBatch n Sample b0) (i : Worker n)
    (xNext x : Point d) : Point d :=
  average (fun j : Fin (b0 i).1 =>
    stochasticGradient P i (batch i j) xNext - stochasticGradient P i (batch i j) x)

/-- Internal scalar aggregation helper for the two expressions quoted at
`book/MARINA/MARINA.json#/key_lemmas/20`.  Its free moment functions are proof
inputs only here and do not occur in the source-facing Remark D.2 theorem. -/
theorem heterogeneousOnline_average_secondMoments_le {n : Count}
    (ℒ σ : Worker n → ℝ) (b0 b : Worker n → Count)
    (differenceSecondMoment refreshSecondMoment : Worker n → ℝ)
    (hDifference : ∀ i, differenceSecondMoment i ≤ (ℒ i) ^ 2 / (b0 i).1)
    (hRefresh : ∀ i, refreshSecondMoment i ≤ (σ i) ^ 2 / (b i).1) :
    average differenceSecondMoment ≤ heterogeneousFiniteBatchSmoothnessTerm ℒ b0 ∧
      average refreshSecondMoment / n.1 ≤ heterogeneousOnlineVarianceTerm σ b := by
  constructor
  · simpa [heterogeneousFiniteBatchSmoothnessTerm] using
      (average_le_average_of_pointwise hDifference)
  · have hAverage : average refreshSecondMoment ≤
        average (fun i : Worker n => (σ i) ^ 2 / (b i).1) :=
      average_le_average_of_pointwise hRefresh
    have hDiv := div_le_div_of_nonneg_right hAverage
      (by positivity : (0 : ℝ) ≤ n.1)
    simpa [heterogeneousOnlineVarianceTerm] using hDiv

/-- `book/MARINA/MARINA.json#/key_lemmas/15`, Remark D.1: a complete
worker-dependent Algorithm 2 round, not merely its aggregated variance term. -/
abbrev HeterogeneousFiniteSumRoundNoise (n m : Count)
    (b0 : Worker n → Count) (Ξ : Type*) :=
  Bool × (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ))

/-- Canonical product-law realization of the heterogeneous Algorithm 2 round
described at `book/MARINA/MARINA.json#/key_lemmas/15`; independence is
realization machinery, not an additional source field. -/
noncomputable def heterogeneousFiniteSumRoundLaw
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (batchLaw : Measure (HeterogeneousFiniteSumBatch n m b0)) :
    Measure (HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :=
  (refreshLaw A.refreshProbability A.refresh_admissible).prod
    (batchLaw.prod (workerCompressionLaw A.quantizer))

noncomputable def heterogeneousFiniteSumPathLaw
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (batchLaw : HeterogeneousFiniteSumBatchLaw n m b0) :
    Measure (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :=
  Measure.infinitePi (fun k => heterogeneousFiniteSumRoundLaw A (batchLaw k))

noncomputable def heterogeneousFiniteSumWorkerEstimator
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ)
    (s : State d) (i : Worker n) : Point d :=
  let xNext := primalStep A.stepSize s
  if z.1 then localGradient (finiteSumLocalProblem A.problem) i xNext
  else s.g + A.quantizer.apply
    (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i xNext s.x)
    (z.2.2 i)

noncomputable def heterogeneousFiniteSumStep
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ) (s : State d) : State d :=
  { x := primalStep A.stepSize s
    g := average (heterogeneousFiniteSumWorkerEstimator A z s) }

/-- Generated heterogeneous Algorithm 2 process for
`book/MARINA/MARINA.json#/key_lemmas/15`, whose quote says "the statement of
Theorem 3.1 remains the same" after replacing the batch aggregate. -/
noncomputable def heterogeneousFiniteSumProcess
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d) :
    ℕ → (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) → State d :=
  SOptLib.recursiveIterateProcess (finiteSumInitialState A x0)
    (fun k s path => heterogeneousFiniteSumStep A (path k) s)

/-- Product law for the worker-dependent batches in Remark D.2. -/
noncomputable def heterogeneousOnlineBatchLaw {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (size : Worker n → Count) :
    Measure (HeterogeneousOnlineBatch n Sample size) :=
  Measure.infinitePi (fun i : Worker n =>
    Measure.infinitePi (fun _ : Fin (size i).1 => P.sampleLaw i))

/-- Remark D.2's complete heterogeneous Algorithm 3 round. -/
abbrev HeterogeneousOnlineRoundNoise (n : Count)
    (Sample : Worker n → Type*) (b b0 : Worker n → Count) (Ξ : Type*) :=
  Bool × ((HeterogeneousOnlineBatch n Sample b ×
    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ))

/-- Canonical product-law realization of the worker-dependent online round in
`book/MARINA/MARINA.json#/key_lemmas/20`; it adds no paper-level moment witness. -/
noncomputable def heterogeneousOnlineRoundLaw {d n : Count}
    {Sample : Worker n → Type*} {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure (HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) :=
  (refreshLaw A.refreshProbability A.refresh_admissible).prod
    (((heterogeneousOnlineBatchLaw A.problem b).prod
      (heterogeneousOnlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw A.quantizer))

noncomputable def heterogeneousOnlinePathLaw {d n : Count}
    {Sample : Worker n → Type*} {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure (HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) :=
  (heterogeneousOnlineBatchLaw A.problem b).prod
    (SOptLib.iidStreamLaw (heterogeneousOnlineRoundLaw A))

noncomputable def heterogeneousOnlineInitialEstimator
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (batch : HeterogeneousOnlineBatch n Sample b) (x0 : Point d) : Point d :=
  average (fun i : Worker n => average (fun j : Fin (b i).1 =>
    stochasticGradient A.problem i (batch i j) x0))

noncomputable def heterogeneousOnlineStep
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) (s : State d) : State d :=
  let xNext := primalStep A.stepSize s
  { x := xNext
    g := average (fun i : Worker n =>
      if z.1 then average (fun j : Fin (b i).1 =>
        stochasticGradient A.problem i (z.2.1.1 i j) xNext)
      else s.g + A.quantizer.apply
        (heterogeneousOnlineBatchDifference A.problem b0 z.2.1.2 i xNext s.x)
        (z.2.2 i)) }

/-- Generated executable heterogeneous Algorithm 3 process for
`book/MARINA/MARINA.json#/key_lemmas/20`, including the source's
worker-dependent `b_i` and `b⁰_i` minibatches. -/
noncomputable def heterogeneousOnlineProcess
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) :
    ℕ → (HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) → State d :=
  SOptLib.recursive_process_from_random_initial
    (fun path => { x := x0, g := heterogeneousOnlineInitialEstimator A path.1 x0 })
    (fun k s path => heterogeneousOnlineStep A (path.2 k) s)

/-- Proof-exact heterogeneous online process, separated from Algorithm 3's
stochastic initialization in the same way as the homogeneous source boundary. -/
noncomputable def heterogeneousOnlineCorrectedProofExactProcess
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) :
    ℕ → (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) → State d :=
  SOptLib.recursiveIterateProcess
    { x := x0
      g := globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 }
    (fun k s path => heterogeneousOnlineStep A (path k) s)

noncomputable def heterogeneousOnlineProofExactPathLaw
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) :=
  SOptLib.iidStreamLaw (heterogeneousOnlineRoundLaw A)

/-- A worker row under the heterogeneous online batch law has its canonical
finite iid product law. -/
theorem heterogeneous_online_batch_law_worker_marginal
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)] (P : OnlineProblem d n Sample)
    (b : Worker n → Count) (i : Worker n) :
    Measure.map
        (fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
        (heterogeneousOnlineBatchLaw P b) =
      Measure.infinitePi (fun _ : Fin (b i).1 => P.sampleLaw i) := by
  classical
  letI (w : Worker n) : IsProbabilityMeasure (P.sampleLaw w) :=
    P.sampleLaw_isProbability w
  letI (w : Worker n) :
      IsProbabilityMeasure
        (Measure.infinitePi (fun _ : Fin (b w).1 => P.sampleLaw w)) := by
    infer_instance
  unfold heterogeneousOnlineBatchLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun w : Worker n =>
        Measure.infinitePi (fun _ : Fin (b w).1 => P.sampleLaw w)) i)

/-- The squared norm of a centered iid finite-batch average is integrable and
has the usual inverse-cardinality second-moment bound. -/
theorem iid_finite_batch_centered_average_sq_integrable_and_le
    {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (nu : Measure S) [IsProbabilityMeasure nu] (m : Count)
    (r : S → E) (V : ℝ)
    (hr : Integrable r nu)
    (hr2 : Integrable (fun xi => ‖r xi‖ ^ 2) nu)
    (hmean : (∫ xi, r xi ∂nu) = 0)
    (hsecond : (∫ xi, ‖r xi‖ ^ 2 ∂nu) ≤ V) :
    Integrable
        (fun row : Fin m.1 → S => ‖average (fun j => r (row j))‖ ^ 2)
        (Measure.infinitePi (fun _ : Fin m.1 => nu)) ∧
      (∫ row : Fin m.1 → S, ‖average (fun j => r (row j))‖ ^ 2
        ∂Measure.infinitePi (fun _ : Fin m.1 => nu)) ≤ V / m.1 := by
  classical
  let mu : Measure (Fin m.1 → S) :=
    Measure.infinitePi (fun _ : Fin m.1 => nu)
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hcoord (j : Fin m.1) :
      Measure.map (fun row : Fin m.1 → S => row j) mu = nu := by
    dsimp [mu]
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin m.1 => nu) j)
  have hrow_int (j : Fin m.1) :
      Integrable (fun row : Fin m.1 → S => r (row j)) mu := by
    have hr_map :
        AEStronglyMeasurable r
          (Measure.map (fun row : Fin m.1 → S => row j) mu) := by
      rw [hcoord j]
      exact hr.aestronglyMeasurable
    have hmap :
        Integrable r
          (Measure.map (fun row : Fin m.1 → S => row j) mu) := by
      rwa [hcoord j]
    exact
      (MeasureTheory.integrable_map_measure hr_map
        (measurable_pi_apply j).aemeasurable).mp hmap
  have hrow_sq (j : Fin m.1) :
      Integrable (fun row : Fin m.1 → S => ‖r (row j)‖ ^ 2) mu := by
    have hr2_map :
        AEStronglyMeasurable (fun xi => ‖r xi‖ ^ 2)
          (Measure.map (fun row : Fin m.1 → S => row j) mu) := by
      rw [hcoord j]
      exact hr2.aestronglyMeasurable
    have hmap :
        Integrable (fun xi => ‖r xi‖ ^ 2)
          (Measure.map (fun row : Fin m.1 → S => row j) mu) := by
      rwa [hcoord j]
    exact
      (MeasureTheory.integrable_map_measure hr2_map
        (measurable_pi_apply j).aemeasurable).mp hmap
  have hdiag (j : Fin m.1) :
      (∫ row : Fin m.1 → S, ‖r (row j)‖ ^ 2 ∂mu) ≤ V := by
    have hr2_map :
        AEStronglyMeasurable (fun xi => ‖r xi‖ ^ 2)
          (Measure.map (fun row : Fin m.1 → S => row j) mu) := by
      rw [hcoord j]
      exact hr2.aestronglyMeasurable
    have hmap := MeasureTheory.integral_map
      (μ := mu) (φ := fun row : Fin m.1 → S => row j)
      (measurable_pi_apply j).aemeasurable hr2_map
    rw [hcoord j] at hmap
    exact hmap.symm.trans_le hsecond
  have hiIndep :
      ProbabilityTheory.iIndepFun
        (fun j (row : Fin m.1 → S) => row j) mu := by
    dsimp [mu]
    exact ProbabilityTheory.iIndepFun_infinitePi
      (fun _ : Fin m.1 => measurable_id)
  have hcross (j k : Fin m.1) (hjk : j ≠ k) :
      (∫ row : Fin m.1 → S, ⟪r (row j), r (row k)⟫_ℝ ∂mu) = 0 := by
    have hr_map :
        AEStronglyMeasurable r
          (Measure.map (fun row : Fin m.1 → S => row j) mu) := by
      rw [hcoord j]
      exact hr.aestronglyMeasurable
    have hkernel :
        AEStronglyMeasurable
          (fun p : S × S => ⟪r p.1, r p.2⟫_ℝ)
          ((Measure.map (fun row : Fin m.1 → S => row j) mu).prod nu) :=
      hr_map.comp_fst.inner hr.aestronglyMeasurable.comp_snd
    have hinner :
        Integrable
          (fun row : Fin m.1 → S => ⟪r (row j), r (row k)⟫_ℝ) mu :=
      integrable_inner_of_integrable_sq_norm
        (hrow_int j).aestronglyMeasurable (hrow_int k).aestronglyMeasurable
        (hrow_sq j) (hrow_sq k)
    have hfixed : ∀ a : S, (∫ z, ⟪r a, r z⟫_ℝ ∂nu) = 0 := by
      intro a
      have hlin :=
        ContinuousLinearMap.integral_comp_comm (L := (innerSL ℝ) (r a)) hr
      exact hlin.trans (by rw [hmean]; simp)
    exact
      integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
        (P := mu) (ν := nu)
        (φ := fun a z => ⟪r a, r z⟫_ℝ)
        (X := fun row : Fin m.1 → S => row j)
        (Y := fun row : Fin m.1 → S => row k)
        hkernel (measurable_pi_apply j).aemeasurable
        (measurable_pi_apply k).aemeasurable (hiIndep.indepFun hjk)
        (hcoord k) hinner hfixed
  have havg_eq :
      (fun row : Fin m.1 → S => average (fun j => r (row j))) =
        fun row => ((m.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun j : Fin m.1 => r (row j)) := by
    funext row
    simp [average, SOptLib.finiteUniformAverage]
  have havg_int :
      Integrable
        (fun row : Fin m.1 → S => ‖average (fun j => r (row j))‖ ^ 2) mu :=
    integrable_sq_norm_centeredMiniBatchAverage
      mu Finset.univ m.1 (fun j row => r (row j))
      (fun row => average (fun j => r (row j)))
      (fun j _ => (hrow_int j).aestronglyMeasurable)
      (fun j _ => hrow_sq j) havg_eq
  have havg_bound :
      (∫ row : Fin m.1 → S, ‖average (fun j => r (row j))‖ ^ 2 ∂mu) ≤
        V / m.1 := by
    have h :=
      centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero
        mu Finset.univ m.1 (fun j row => r (row j)) V m.2
        (by simp) (fun j _ => (hrow_int j).aestronglyMeasurable)
        (fun j _ => ⟨hrow_sq j, hdiag j⟩)
        (fun j _ k _ hjk => hcross j k hjk)
    calc
      (∫ row : Fin m.1 → S, ‖average (fun j => r (row j))‖ ^ 2 ∂mu) =
          ∫ row : Fin m.1 → S,
            ‖((m.1 : ℝ)⁻¹) •
              Finset.sum Finset.univ (fun j : Fin m.1 => r (row j))‖ ^ 2 ∂mu := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro row
        change ‖average (fun j => r (row j))‖ ^ 2 =
          ‖((m.1 : ℝ)⁻¹) •
            Finset.sum Finset.univ (fun j : Fin m.1 => r (row j))‖ ^ 2
        rw [congrFun havg_eq row]
      _ ≤ V / m.1 := h
  simpa [mu] using And.intro havg_int havg_bound

/-- Assumption 3.2 for the generated heterogeneous online process. -/
def HeterogeneousOnlineAverageSmoothness {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    {b b0 : Worker n → Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧ ∀ k i path,
    let x := (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path).x
    let xNext :=
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 (k + 1) path).x
    Integrable (fun batch => heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x)
      (heterogeneousOnlineBatchLaw A.problem b0) ∧
    Integrable (fun batch =>
      ‖heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x‖ ^ 2)
      (heterogeneousOnlineBatchLaw A.problem b0) ∧
    (∫ batch, heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x
      ∂heterogeneousOnlineBatchLaw A.problem b0) =
        localGradientDifference (onlineLocalProblem A.problem) i xNext x ∧
    (∫ batch, ‖heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x‖ ^ 2
      ∂heterogeneousOnlineBatchLaw A.problem b0) ≤
        (ℒ i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2

/-- Corrected Eq. (6) version of Remark D.2's worker-dependent Assumption
3.2, tied to the generated heterogeneous online process. -/
def HeterogeneousOnlineAverageSmoothnessCorrected {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    {b0 : Worker n → Count} {Ω : Type*}
    (P : RealizedOnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧ ∀ k i path,
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    Integrable (fun batch => heterogeneousOnlineBatchDifference P.1 b0 batch i xNext x)
      (heterogeneousOnlineBatchLaw P.1 b0) ∧
    Integrable (fun batch =>
      ‖heterogeneousOnlineBatchDifference P.1 b0 batch i xNext x -
        localGradientDifference (onlineLocalProblemCorrected P) i xNext x‖ ^ 2)
      (heterogeneousOnlineBatchLaw P.1 b0) ∧
    (∫ batch, heterogeneousOnlineBatchDifference P.1 b0 batch i xNext x
      ∂heterogeneousOnlineBatchLaw P.1 b0) =
        localGradientDifference (onlineLocalProblemCorrected P) i xNext x ∧
    (∫ batch, ‖heterogeneousOnlineBatchDifference P.1 b0 batch i xNext x -
        localGradientDifference (onlineLocalProblemCorrected P)
          i xNext x‖ ^ 2
      ∂heterogeneousOnlineBatchLaw P.1 b0) ≤
        (ℒ i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2

/-- Assumption 3.3 directly yields workerwise refresh-batch moments; no free
moment surrogate appears in the public heterogeneous theorem boundary. -/
theorem heterogeneousOnline_refresh_secondMoment_le_of_legacy
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)] (P : OnlineProblem d n Sample)
    (σ : Worker n → ℝ) (b : Worker n → Count)
    (hVariance : LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ)
    (i : Worker n) (x : Point d) :
    Integrable (fun batch =>
      ‖average (fun j : Fin (b i).1 => stochasticGradient P i (batch i j) x) -
        localGradient (onlineLocalProblem P) i x‖ ^ 2)
      (heterogeneousOnlineBatchLaw P b) ∧
    (∫ batch,
      ‖average (fun j : Fin (b i).1 => stochasticGradient P i (batch i j) x) -
        localGradient (onlineLocalProblem P) i x‖ ^ 2
      ∂heterogeneousOnlineBatchLaw P b) ≤ (σ i) ^ 2 / (b i).1 := by
  classical
  let nu : Measure (Sample i) := P.sampleLaw i
  let target : Point d := localGradient (onlineLocalProblem P) i x
  let r : Sample i → Point d :=
    fun xi => stochasticGradient P i xi x - target
  let mu : Measure (Fin (b i).1 → Sample i) :=
    Measure.infinitePi (fun _ : Fin (b i).1 => nu)
  letI : IsProbabilityMeasure nu := P.sampleLaw_isProbability i
  rcases hVariance.2 i x with ⟨hg_int, hr2, hg_mean, hsecond⟩
  have hr : Integrable r nu := by
    dsimp [r, nu, target]
    exact hg_int.sub (integrable_const (c := localGradient (onlineLocalProblem P) i x))
  have hr2' : Integrable (fun xi => ‖r xi‖ ^ 2) nu := by
    simpa [r, nu, target] using hr2
  have hr_mean : (∫ xi, r xi ∂nu) = 0 := by
    dsimp [r, nu, target]
    calc
      (∫ xi, stochasticGradient P i xi x -
          localGradient (onlineLocalProblem P) i x ∂P.sampleLaw i) =
          (∫ xi, stochasticGradient P i xi x ∂P.sampleLaw i) -
            ∫ _xi : Sample i, localGradient (onlineLocalProblem P) i x
              ∂P.sampleLaw i := by
        exact integral_sub hg_int
          (integrable_const (c := localGradient (onlineLocalProblem P) i x))
      _ = 0 := by simp [hg_mean]
  have hsecond' : (∫ xi, ‖r xi‖ ^ 2 ∂nu) ≤ (σ i) ^ 2 := by
    simpa [r, nu, target] using hsecond
  have hiid :
      Integrable
          (fun row : Fin (b i).1 → Sample i =>
            ‖average (fun j => r (row j))‖ ^ 2) mu ∧
        (∫ row : Fin (b i).1 → Sample i,
          ‖average (fun j => r (row j))‖ ^ 2 ∂mu) ≤
            (σ i) ^ 2 / (b i).1 := by
    simpa [mu] using
      (iid_finite_batch_centered_average_sq_integrable_and_le
        nu (b i) r ((σ i) ^ 2) hr hr2' hr_mean hsecond')
  have hcenter (row : Fin (b i).1 → Sample i) :
      average (fun j => stochasticGradient P i (row j) x) - target =
        average (fun j => r (row j)) := by
    unfold average
    simpa [r, SOptLib.finiteUniformAverage] using
      (miniBatchAverage_sub_target_eq_average_residual
        (Finset.univ : Finset (Fin (b i).1)) (b i).1 (by simp) (b i).2
        (fun j => stochasticGradient P i (row j) x) target)
  have hworker := heterogeneous_online_batch_law_worker_marginal P b i
  have hworker' :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
          (heterogeneousOnlineBatchLaw P b) = mu := by
    simpa [mu, nu] using hworker
  let phi : (Fin (b i).1 → Sample i) → ℝ :=
    fun row => ‖average (fun j => r (row j))‖ ^ 2
  have hphi_map_aesm :
      AEStronglyMeasurable phi
        (Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
          (heterogeneousOnlineBatchLaw P b)) := by
    rw [hworker']
    exact hiid.1.aestronglyMeasurable
  have hphi_map_int :
      Integrable phi
        (Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
          (heterogeneousOnlineBatchLaw P b)) := by
    rw [hworker']
    exact hiid.1
  have hphi_comp_int :
      Integrable
        (fun batch : HeterogeneousOnlineBatch n Sample b => phi (batch i))
        (heterogeneousOnlineBatchLaw P b) := by
    exact
      (MeasureTheory.integrable_map_measure hphi_map_aesm
        (measurable_pi_apply i).aemeasurable).mp hphi_map_int
  constructor
  · apply hphi_comp_int.congr
    filter_upwards [] with batch
    dsimp [phi]
    rw [hcenter]
  · have hmap_integral := MeasureTheory.integral_map
      (μ := heterogeneousOnlineBatchLaw P b)
      (φ := fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
      (measurable_pi_apply i).aemeasurable hphi_map_aesm
    rw [hworker'] at hmap_integral
    calc
      (∫ batch,
        ‖average (fun j : Fin (b i).1 => stochasticGradient P i (batch i j) x) -
          localGradient (onlineLocalProblem P) i x‖ ^ 2
        ∂heterogeneousOnlineBatchLaw P b) =
          ∫ batch : HeterogeneousOnlineBatch n Sample b, phi (batch i)
            ∂heterogeneousOnlineBatchLaw P b := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro batch
        dsimp [phi]
        change
          ‖average (fun j => stochasticGradient P i (batch i j) x) - target‖ ^ 2 =
            ‖average (fun j => r (batch i j))‖ ^ 2
        rw [hcenter]
      _ = ∫ row : Fin (b i).1 → Sample i, phi row ∂mu :=
        hmap_integral.symm
      _ ≤ (σ i) ^ 2 / (b i).1 := by
        simpa [phi] using hiid.2

/-- Compatibility wrapper for callers using the formerly bundled online
variance predicate.  The underlying refresh-minibatch proof consumes only its
literal fixed-query moment component. -/
theorem heterogeneousOnline_refresh_secondMoment_le
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)] (P : OnlineProblem d n Sample)
    (σ : Worker n → ℝ) (b : Worker n → Count)
    (hVariance : OnlineUnbiasedBoundedVariance P σ) (i : Worker n) (x : Point d) :
    Integrable (fun batch ↦
      ‖average (fun j : Fin (b i).1 ↦ stochasticGradient P i (batch i j) x) -
        localGradient (onlineLocalProblem P) i x‖ ^ 2)
      (heterogeneousOnlineBatchLaw P b) ∧
    (∫ batch,
      ‖average (fun j : Fin (b i).1 ↦ stochasticGradient P i (batch i j) x) -
        localGradient (onlineLocalProblem P) i x‖ ^ 2
      ∂heterogeneousOnlineBatchLaw P b) ≤ (σ i) ^ 2 / (b i).1 := by
  exact heterogeneousOnline_refresh_secondMoment_le_of_legacy
    P σ b hVariance.1 i x

noncomputable def onlineDifference {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (z : OnlineDriver n b b0 Sample Ξ)
    (i : Worker n) (xNext x : Point d) : Point d :=
  onlineBatchDifference A.problem z.differenceSample i xNext x

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/4`: the quoted online VR
refresh/difference worker update. -/
noncomputable def onlineWorkerEstimator {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (z : OnlineDriver n b b0 Sample Ξ)
    (s : State d) (i : Worker n) : Point d :=
  let xNext := primalStep A.stepSize s
  if z.refresh then
    average (fun j : Fin b.1 =>
      stochasticGradient A.problem i (z.refreshSample i j) xNext)
  else
    s.g + A.quantizer.apply (onlineDifference A z i xNext s.x)
      (z.compressionSample i)

/-- `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/4`, and `#/algorithm_spec/steps/5`: canonical online
VR transition and worker averaging. -/
noncomputable def onlineStep {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (z : OnlineDriver n b b0 Sample Ξ)
    (s : State d) : State d :=
  { x := primalStep A.stepSize s
    g := average (onlineWorkerEstimator A z s) }

/-- Under an explicit measurable realization of the stochastic-gradient
kernel, one Algorithm 3 worker update is jointly measurable in the previous
state and all current-round coordinates. -/
theorem onlineWorkerEstimator_round_joint_measurable_of_kernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem) (i : Worker n) :
    Measurable (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
      onlineWorkerEstimator A (onlineDriverOfRoundNoise p.2) p.1 i) := by
  classical
  have hxNext : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hx : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ => p.1.x) :=
    (measurable_state_x d).comp measurable_fst
  have hdifferenceBatch : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ => p.2.2.1.2) :=
    measurable_snd.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hqueries : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        ((primalStep A.stepSize p.1, p.1.x), p.2.2.1.2)) :=
    (hxNext.prodMk hx).prodMk hdifferenceBatch
  have hdiff : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        onlineBatchDifference A.problem p.2.2.1.2 i
          (primalStep A.stepSize p.1) p.1.x) := by
    simpa only [Function.comp_apply] using
      (onlineBatchDifference_joint_measurable_of_kernel (b0 := b0)
        A.problem hKernel i).comp hqueries
  have hcompressionSample : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ => p.2.2.2 i) :=
    (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hquantized : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        A.quantizer.apply
          (onlineBatchDifference A.problem p.2.2.1.2 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    A.quantizer.measurable_apply_uncurry.comp
      (hdiff.prodMk hcompressionSample)
  have hrefreshTerm (j : Fin b.1) : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        stochasticGradient A.problem i (p.2.2.1.1 i j)
          (primalStep A.stepSize p.1)) := by
    have hsample : Measurable
        (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
          p.2.2.1.1 i j) :=
      (measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp
          (measurable_fst.comp
            (measurable_fst.comp (measurable_snd.comp measurable_snd))))
    exact (hKernel i).comp (hxNext.prodMk hsample)
  have hrefresh : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        average (fun j : Fin b.1 =>
          stochasticGradient A.problem i (p.2.2.1.1 i j)
            (primalStep A.stepSize p.1))) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ (fun j _ => hrefreshTerm j)).const_smul
      ((Fintype.card (Fin b.1) : ℝ)⁻¹)
  have hcarry : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        p.1.g + A.quantizer.apply
          (onlineBatchDifference A.problem p.2.2.1.2 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    ((measurable_state_g d).comp measurable_fst).add hquantized
  have hrefreshSet : MeasurableSet
      {p : State d × OnlineRoundNoise n b b0 Sample Ξ | p.2.1 = true} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
  have hif : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        if p.2.1 = true then
          average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (p.2.2.1.1 i j)
              (primalStep A.stepSize p.1))
        else p.1.g + A.quantizer.apply
          (onlineBatchDifference A.problem p.2.2.1.2 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    @Measurable.ite _ _ _ _ _ _
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ => p.2.1 = true)
      (fun p => Bool.decEq p.2.1 true) hrefreshSet hrefresh hcarry
  simpa [onlineWorkerEstimator, onlineDriverOfRoundNoise, onlineDifference] using hif

/-- The complete Algorithm 3 transition is jointly measurable whenever its
canonical stochastic-gradient kernel has an explicit measurable realization. -/
theorem onlineStep_round_joint_measurable_of_kernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem) :
    Measurable (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
      onlineStep A (onlineDriverOfRoundNoise p.2) p.1) := by
  classical
  have hxNext : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hg : Measurable
      (fun p : State d × OnlineRoundNoise n b b0 Sample Ξ =>
        average (fun i : Worker n =>
          onlineWorkerEstimator A (onlineDriverOfRoundNoise p.2) p.1 i)) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ (fun i _ =>
      onlineWorkerEstimator_round_joint_measurable_of_kernel A hKernel i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
  simpa [onlineStep] using
    (measurable_state_mk d).comp (hxNext.prodMk hg)

/-- Generated recursion for `book/MARINA/MARINA.json#/algorithm_spec/steps/0`,
`#/algorithm_spec/steps/4`, and `#/algorithm_spec/steps/5`,
including the printed stochastic initialization at
`#/algorithm_spec/initialization/facts/2`. -/
noncomputable def onlineRun {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (_hBatch : OnlineBatchAdmissible b b0) :
    ℕ → OnlinePath n b b0 Sample Ξ → State d :=
  SOptLib.recursive_process_from_random_initial
    (fun path => onlineInitialState A path.initial x0)
    (fun k s path => onlineStep A (path.round k) s)

/-- Executable random-process realization of
`book/MARINA/MARINA.json#/algorithm_spec/variants/2`, using the well-scoped
minibatch-at-`x⁰` correction to `#/algorithm_spec/initialization/facts/2`. -/
noncomputable def onlineProcess {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) :
    ℕ → (((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) → State d :=
  fun k path => onlineRun A x0 hBatch k (onlinePathOfNoise path)

/-- Generated Algorithm 3 process for the proof's source interpretation
`g⁰=∇f(x⁰)` (`book/MARINA/MARINA.json#/algorithm_spec/initialization/facts/3`).
It uses the same Algorithm 3 transition and canonical path law, but ignores
the printed initialization minibatch. -/
noncomputable def onlineProofExactRun {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (_hBatch : OnlineBatchAdmissible b b0) :
    ℕ → (ℕ → OnlineDriver n b b0 Sample Ξ) → State d :=
  SOptLib.recursiveIterateProcess (onlineProofExactInitialState A x0)
    (fun k s path => onlineStep A (path k) s)

/-- The proof-exact Algorithm 3 process on the canonical joint path law. -/
noncomputable def onlineProofExactProcess {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) :
    ℕ → (ℕ → OnlineRoundNoise n b b0 Sample Ξ) → State d :=
  fun k path => onlineProofExactRun A x0 hBatch k
    (fun t => onlineDriverOfRoundNoise (path t))

/-- B-track proof-exact initialization using the nonfallback realization of
Eq. (6), rather than the literal totalized integral. -/
noncomputable def onlineCorrectedExactInitialState {d n : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) : State d :=
  { x := x0
    g := globalGradient (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 }

/-- Generated proof-exact Algorithm 3 process on the corrected Eq. (6)
B-track. -/
noncomputable def onlineCorrectedProofExactProcess {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (_hBatch : OnlineBatchAdmissible b b0) :
    ℕ → (ℕ → OnlineRoundNoise n b b0 Sample Ξ) → State d :=
  SOptLib.recursiveIterateProcess (onlineCorrectedExactInitialState A hE x0)
    (fun k s path => onlineStep A (onlineDriverOfRoundNoise (path k)) s)

/-- Eq. (6)'s intrinsic integrability makes the former corrected exact
initialization definitionally equal to the canonical proof-exact one. -/
theorem onlineCorrectedExactInitialState_eq_onlineProofExactInitialState
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) :
    onlineCorrectedExactInitialState A hE x0 =
      onlineProofExactInitialState A x0 := by
  rfl

/-- Definitional bridge retiring the former corrected process from the public
Eq. (46) dependency cone.  Both processes use the same canonical initial
gradient and exactly the same Algorithm 3 transition. -/
theorem onlineCorrectedProofExactProcess_eq_onlineProofExactProcess
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0) :
    onlineCorrectedProofExactProcess A hE x0 hBatch =
      onlineProofExactProcess A x0 hBatch := by
  funext k path
  induction k with
  | zero =>
      exact onlineCorrectedExactInitialState_eq_onlineProofExactInitialState
        A hE x0
  | succ k ih =>
      change onlineStep A (onlineDriverOfRoundNoise (path k))
          (onlineCorrectedProofExactProcess A hE x0 hBatch k path) =
        onlineStep A (onlineDriverOfRoundNoise (path k))
          (onlineProofExactProcess A x0 hBatch k path)
      rw [ih]

@[simp] theorem onlineProofExactProcess_succ {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (path : ℕ → OnlineRoundNoise n b b0 Sample Ξ) :
    onlineProofExactProcess A x0 hBatch (k + 1) path =
      onlineStep A (onlineDriverOfRoundNoise (path k))
        (onlineProofExactProcess A x0 hBatch k path) := by
  rfl

@[simp] theorem onlineCorrectedProofExactProcess_succ {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (path : ℕ → OnlineRoundNoise n b b0 Sample Ξ) :
    onlineCorrectedProofExactProcess A hE x0 hBatch (k + 1) path =
      onlineStep A (onlineDriverOfRoundNoise (path k))
        (onlineCorrectedProofExactProcess A hE x0 hBatch k path) := by
  rfl

set_option maxHeartbeats 1600000 in
/-- A law-scoped Algorithm 3 transition.  Sampled-loss differentiability and
the fixed-query Eq. (6) integrability construct every stochastic-gradient
coordinate on the product of an arbitrary state law and the fresh round law.
This is the a.e.-measurable replacement for the stronger global-kernel
transition theorem. -/
theorem onlineStep_product_aemeasurable_of_state
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    [MeasurableSpace Q]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected
      ⟨A.problem, hE⟩ sigma)
    (nu : Measure Q) [SFinite nu] (state : Q → State d)
    (hstate : AEMeasurable state nu) :
    AEMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
        onlineStep A (onlineDriverOfRoundNoise p.2) (state p.1))
      (nu.prod (onlineRoundLaw A)) := by
  classical
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  have hx : AEStronglyMeasurable (fun q => (state q).x) nu :=
    ((measurable_state_x d).comp_aemeasurable hstate).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun q => (state q).g) nu :=
    ((measurable_state_g d).comp_aemeasurable hstate).aestronglyMeasurable
  have hxNext : AEStronglyMeasurable
      (fun q => primalStep A.stepSize (state q)) nu :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable
      hstate).aestronglyMeasurable
  have hsample_integrable
      (i : Worker n) (sample : OnlineRoundNoise n b b0 Sample Ξ → Sample i)
      (hsample : Measurable sample)
      (hmap : Measure.map sample roundLaw = A.problem.sampleLaw i)
      (x : Point d) :
      Integrable (fun z => A.problem.sampleLoss i (sample z) x) roundLaw := by
    have hm : Integrable (fun xi => A.problem.sampleLoss i xi x)
        (Measure.map sample roundLaw) := by
      rw [hmap]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      hsample.aemeasurable).mp hm
  have hsample_differentiable
      (i : Worker n) (sample : OnlineRoundNoise n b b0 Sample Ξ → Sample i)
      (hsample : Measurable sample)
      (hmap : Measure.map sample roundLaw = A.problem.sampleLaw i) :
      ∀ᵐ z ∂roundLaw, Differentiable ℝ (A.problem.sampleLoss i (sample z)) := by
    have hqmp : Measure.QuasiMeasurePreserving sample roundLaw
        (A.problem.sampleLaw i) :=
      ⟨hsample, by rw [hmap]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hrefresh_sample_map (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1 i j) roundLaw =
        A.problem.sampleLaw i := by
    calc
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1 i j)
          roundLaw =
          Measure.map (fun batch : (w : Worker n) → Fin b.1 → Sample w =>
              batch i j)
            (Measure.map
              (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
              roundLaw) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · fun_prop
      _ = Measure.map (fun batch : (w : Worker n) → Fin b.1 → Sample w =>
              batch i j) (onlineBatchLaw A.problem b) := by
            rw [onlineRoundLaw_refreshBatch_marginal]
      _ = A.problem.sampleLaw i := onlineBatchLaw_coordinate_marginal A.problem i j
  have hdifference_sample_map (i : Worker n) (j : Fin b0.1) :
      Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2 i j) roundLaw =
        A.problem.sampleLaw i := by
    calc
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2 i j)
          roundLaw =
          Measure.map (fun batch : (w : Worker n) → Fin b0.1 → Sample w =>
              batch i j)
            (Measure.map
              (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
              roundLaw) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · fun_prop
      _ = Measure.map (fun batch : (w : Worker n) → Fin b0.1 → Sample w =>
              batch i j) (onlineBatchLaw A.problem b0) := by
            rw [onlineRoundLaw_differenceBatch_marginal]
      _ = A.problem.sampleLaw i := onlineBatchLaw_coordinate_marginal A.problem i j
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
        onlineWorkerEstimator A (onlineDriverOfRoundNoise p.2) (state p.1) i)
      (nu.prod roundLaw) := by
    have hrefreshTerm (j : Fin b.1) : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
          stochasticGradient A.problem i (p.2.2.1.1 i j)
            (primalStep A.stepSize (state p.1)))
        (nu.prod roundLaw) := by
      exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
        A.problem i nu roundLaw
          (fun q => primalStep A.stepSize (state q))
          (fun z => z.2.1.1 i j) hxNext
          (hsample_differentiable i (fun z => z.2.1.1 i j) (by fun_prop)
            (hrefresh_sample_map i j))
          (hsample_integrable i (fun z => z.2.1.1 i j) (by fun_prop)
            (hrefresh_sample_map i j))
    have hrefresh : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
          average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (p.2.2.1.1 i j)
              (primalStep A.stepSize (state p.1))))
        (nu.prod roundLaw) := by
      unfold average SOptLib.finiteUniformAverage
      have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => hrefreshTerm j)).const_smul
          ((Fintype.card (Fin b.1) : ℝ)⁻¹)
      refine hsum.congr (Filter.Eventually.of_forall ?_)
      intro p
      simp [Finset.sum_apply]
    have hnextTerm (j : Fin b0.1) : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
          stochasticGradient A.problem i (p.2.2.1.2 i j)
            (primalStep A.stepSize (state p.1)))
        (nu.prod roundLaw) := by
      exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
        A.problem i nu roundLaw
          (fun q => primalStep A.stepSize (state q))
          (fun z => z.2.1.2 i j) hxNext
          (hsample_differentiable i (fun z => z.2.1.2 i j) (by fun_prop)
            (hdifference_sample_map i j))
          (hsample_integrable i (fun z => z.2.1.2 i j) (by fun_prop)
            (hdifference_sample_map i j))
    have hcurrentTerm (j : Fin b0.1) : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
          stochasticGradient A.problem i (p.2.2.1.2 i j) (state p.1).x)
        (nu.prod roundLaw) := by
      exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
        A.problem i nu roundLaw (fun q => (state q).x)
          (fun z => z.2.1.2 i j) hx
          (hsample_differentiable i (fun z => z.2.1.2 i j) (by fun_prop)
            (hdifference_sample_map i j))
          (hsample_integrable i (fun z => z.2.1.2 i j) (by fun_prop)
            (hdifference_sample_map i j))
    have hdiff : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
          onlineBatchDifference A.problem p.2.2.1.2 i
            (primalStep A.stepSize (state p.1)) (state p.1).x)
        (nu.prod roundLaw) := by
      unfold onlineBatchDifference average SOptLib.finiteUniformAverage
      have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => (hnextTerm j).sub (hcurrentTerm j))).const_smul
          ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
      refine hsum.congr (Filter.Eventually.of_forall ?_)
      intro p
      simp [Finset.sum_apply, Finset.sum_sub_distrib]
    have hcompression : Measurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ => p.2.2.2 i) := by
      fun_prop
    have hquantized : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
          A.quantizer.apply
            (onlineBatchDifference A.problem p.2.2.1.2 i
              (primalStep A.stepSize (state p.1)) (state p.1).x)
            (p.2.2.2 i)) (nu.prod roundLaw) :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hdiff.aemeasurable.prodMk hcompression.aemeasurable)).aestronglyMeasurable
    have hcarry : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
          (state p.1).g + A.quantizer.apply
            (onlineBatchDifference A.problem p.2.2.1.2 i
              (primalStep A.stepSize (state p.1)) (state p.1).x)
            (p.2.2.2 i)) (nu.prod roundLaw) :=
      hg.comp_fst.add hquantized
    have hrefreshSet : MeasurableSet
        {p : Q × OnlineRoundNoise n b b0 Sample Ξ | p.2.1 = true} := by
      exact (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
    have hpiece := AEStronglyMeasurable.piecewise hrefreshSet
      hrefresh.restrict hcarry.restrict
    simpa [onlineWorkerEstimator, onlineDriverOfRoundNoise, onlineDifference,
      Set.piecewise] using hpiece
  have hnext : AEStronglyMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
        primalStep A.stepSize (state p.1)) (nu.prod roundLaw) := hxNext.comp_fst
  have haverage : AEStronglyMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ =>
        average (fun i : Worker n =>
          onlineWorkerEstimator A (onlineDriverOfRoundNoise p.2) (state p.1) i))
      (nu.prod roundLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  exact (measurable_state_mk d).comp_aemeasurable
    (hnext.aemeasurable.prodMk haverage.aemeasurable)

def onlineRoundPrefix {n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    (k : ℕ) (path : ℕ → OnlineRoundNoise n b b0 Sample Ξ) :
    Fin k → OnlineRoundNoise n b b0 Sample Ξ :=
  fun j => path j.1

def onlineExtendRoundPrefix {n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    {k : ℕ} (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ)
    (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ) :
    ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
  fun t => if ht : t < k then pref ⟨t, ht⟩ else fallback t

noncomputable def onlineRoundPrefixLaw
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) :
    Measure (Fin k → OnlineRoundNoise n b b0 Sample Ξ) :=
  Measure.map (onlineRoundPrefix k)
    (onlineProofExactPathLaw (b := b) (b0 := b0) A)

noncomputable def onlineProofExactPrefixState
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ)
    (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ) : State d :=
  onlineProofExactProcess A x0 hBatch k
    (onlineExtendRoundPrefix fallback pref)

theorem onlineProofExactProcess_congr_prefix
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    {path path' : ℕ → OnlineRoundNoise n b b0 Sample Ξ}
    (hpath : ∀ t < k, path t = path' t) :
    onlineProofExactProcess A x0 hBatch k path =
      onlineProofExactProcess A x0 hBatch k path' := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [onlineProofExactProcess_succ, onlineProofExactProcess_succ]
      have hprev : ∀ t < k, path t = path' t :=
        fun t ht => hpath t (Nat.lt_trans ht (Nat.lt_succ_self k))
      rw [ih hprev, hpath k (Nat.lt_succ_self k)]

theorem onlineProofExactPrefixState_succ
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ)
    (pref : Fin (k + 1) → OnlineRoundNoise n b b0 Sample Ξ) :
    onlineProofExactPrefixState A x0 hBatch fallback (k + 1) pref =
      onlineStep A (onlineDriverOfRoundNoise (pref (Fin.last k)))
        (onlineProofExactPrefixState A x0 hBatch fallback k
          (fun j => pref j.castSucc)) := by
  unfold onlineProofExactPrefixState
  rw [onlineProofExactProcess_succ]
  have hprev := onlineProofExactProcess_congr_prefix
    A x0 hBatch k
    (path := onlineExtendRoundPrefix fallback pref)
    (path' := onlineExtendRoundPrefix fallback (fun j => pref j.castSucc))
    (fun t ht => by
      simp [onlineExtendRoundPrefix, ht, Nat.le_of_lt ht])
  rw [hprev]
  have hlast : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := by
    apply Fin.ext
    rfl
  simp [onlineExtendRoundPrefix, hlast]

noncomputable def onlineCorrectedPrefixState
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ)
    (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ) : State d :=
  onlineCorrectedProofExactProcess A hE x0 hBatch k
    (onlineExtendRoundPrefix fallback pref)

theorem onlineCorrectedProofExactProcess_congr_prefix
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    {path path' : ℕ → OnlineRoundNoise n b b0 Sample Ξ}
    (hpath : ∀ t < k, path t = path' t) :
    onlineCorrectedProofExactProcess A hE x0 hBatch k path =
      onlineCorrectedProofExactProcess A hE x0 hBatch k path' := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [onlineCorrectedProofExactProcess_succ,
        onlineCorrectedProofExactProcess_succ]
      have hprev : ∀ t < k, path t = path' t :=
        fun t ht => hpath t (Nat.lt_trans ht (Nat.lt_succ_self k))
      rw [ih hprev, hpath k (Nat.lt_succ_self k)]

theorem onlineCorrectedPrefixState_succ
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ)
    (pref : Fin (k + 1) → OnlineRoundNoise n b b0 Sample Ξ) :
    onlineCorrectedPrefixState A hE x0 hBatch fallback (k + 1) pref =
      onlineStep A (onlineDriverOfRoundNoise (pref (Fin.last k)))
        (onlineCorrectedPrefixState A hE x0 hBatch fallback k
          (fun j => pref j.castSucc)) := by
  unfold onlineCorrectedPrefixState
  rw [onlineCorrectedProofExactProcess_succ]
  have hprev := onlineCorrectedProofExactProcess_congr_prefix
    A hE x0 hBatch k
    (path := onlineExtendRoundPrefix fallback pref)
    (path' := onlineExtendRoundPrefix fallback (fun j => pref j.castSucc))
    (fun t ht => by
      simp [onlineExtendRoundPrefix, ht, Nat.le_of_lt ht])
  rw [hprev]
  have hlast : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := by
    apply Fin.ext
    rfl
  simp [onlineExtendRoundPrefix, hlast]

theorem onlineRoundPrefixLaw_split_succ
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) :
    Measure.map
        (fun pref : Fin (k + 1) → OnlineRoundNoise n b b0 Sample Ξ =>
          ((fun j : Fin k => pref j.castSucc), pref (Fin.last k)))
        (onlineRoundPrefixLaw A (k + 1)) =
      (onlineRoundPrefixLaw A k).prod (onlineRoundLaw A) := by
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  unfold onlineRoundPrefixLaw onlineProofExactPathLaw SOptLib.iidStreamLaw
  rw [MeasureTheory.Measure.map_map]
  · simpa [onlineRoundPrefix, Function.comp_def] using
      (infinitePi_prefix_current_map_eq_prod
        (fun _ : ℕ => onlineRoundLaw (b := b) (b0 := b0) A) k)
  · fun_prop
  · exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1

set_option maxHeartbeats 1600000 in
theorem onlineCorrectedPrefixState_all_aemeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) :
    ∀ k, AEMeasurable
      (onlineCorrectedPrefixState A hE x0 hBatch fallback k)
      (onlineRoundPrefixLaw A k) := by
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
    unfold onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix_meas (t : ℕ) : Measurable
      (onlineRoundPrefix (n := n) (b := b) (b0 := b0)
        (Sample := Sample) (Ξ := Ξ) t) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  haveI (t : ℕ) : IsProbabilityMeasure (onlineRoundPrefixLaw A t) := by
    unfold onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map (hprefix_meas t).aemeasurable
  intro k
  induction k with
  | zero =>
      have hconst : onlineCorrectedPrefixState A hE x0 hBatch fallback 0 =
          fun _ => onlineCorrectedExactInitialState A hE x0 := by
        funext pref
        rfl
      rw [hconst]
      exact measurable_const.aemeasurable
  | succ k ih =>
      let split : (Fin (k + 1) → OnlineRoundNoise n b b0 Sample Ξ) →
          (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
            OnlineRoundNoise n b b0 Sample Ξ :=
        fun pref => ((fun j => pref j.castSucc), pref (Fin.last k))
      have hsplit : Measurable split := by
        dsimp [split]
        fun_prop
      have hstep : AEMeasurable
          (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
              OnlineRoundNoise n b b0 Sample Ξ =>
            onlineStep A (onlineDriverOfRoundNoise p.2)
              (onlineCorrectedPrefixState A hE x0 hBatch fallback k p.1))
          ((onlineRoundPrefixLaw A k).prod (onlineRoundLaw A)) :=
        onlineStep_product_aemeasurable_of_state A hE sigma hVariance
          (onlineRoundPrefixLaw A k)
          (onlineCorrectedPrefixState A hE x0 hBatch fallback k) ih
      have honMap : AEMeasurable
          (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
              OnlineRoundNoise n b b0 Sample Ξ =>
            onlineStep A (onlineDriverOfRoundNoise p.2)
              (onlineCorrectedPrefixState A hE x0 hBatch fallback k p.1))
          (Measure.map split (onlineRoundPrefixLaw A (k + 1))) := by
        rw [show Measure.map split (onlineRoundPrefixLaw A (k + 1)) =
            (onlineRoundPrefixLaw A k).prod (onlineRoundLaw A) by
          simpa [split] using onlineRoundPrefixLaw_split_succ A k]
        exact hstep
      have hpull := honMap.comp_aemeasurable hsplit.aemeasurable
      refine hpull.congr (Filter.Eventually.of_forall ?_)
      intro pref
      simpa [split, Function.comp_def] using
        (onlineCorrectedPrefixState_succ A hE x0 hBatch fallback k pref).symm

/-- Every corrected proof-exact Algorithm 3 state is a random variable under
the canonical iid round law.  The proof factors the recursion through its
finite strict prefix, uses `infinitePi_prefix_current_map_eq_prod` to adjoin
the fresh current round, and applies the law-scoped transition theorem. -/
theorem onlineCorrectedProofExactProcess_all_aemeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (k : ℕ) :
    AEMeasurable
      (onlineCorrectedProofExactProcess A hE x0 hBatch k)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  have hpref : AEMeasurable
      (onlineCorrectedPrefixState A hE x0 hBatch fallback k)
      (onlineRoundPrefixLaw A k) :=
    onlineCorrectedPrefixState_all_aemeasurable
      A hE x0 hBatch sigma hVariance fallback k
  have hprefix : Measurable
      (onlineRoundPrefix (n := n) (b := b) (b0 := b0)
        (Sample := Sample) (Ξ := Ξ) k) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hpull := hpref.comp_aemeasurable hprefix.aemeasurable
  change AEMeasurable
    (onlineCorrectedProofExactProcess A hE x0 hBatch k) law
  refine hpull.congr (Filter.Eventually.of_forall ?_)
  intro path
  apply onlineCorrectedProofExactProcess_congr_prefix A hE x0 hBatch k
  intro t ht
  simp [onlineRoundPrefix, onlineExtendRoundPrefix, ht]

set_option maxHeartbeats 1600000 in
/-- Assumptions 3.2--3.3 construct the complete vector-valued Algorithm 3
direction for every fixed generated prefix.  Both refresh and non-refresh
branches are included, and the latter is composed with the canonical jointly
measurable compressor.  This is deliberately a fixed-prefix statement: the
separate step needed to recurse at a random prefix is product-law
measurability in `(prefix,currentRound)`, which does not follow merely by
renaming these fiberwise integrability hypotheses. -/
theorem onlineCorrectedRoundDirection_fixedPrefix_aestronglyMeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (k : ℕ) (path : ℕ → OnlineRoundNoise n b b0 Sample Ξ) :
    AEStronglyMeasurable
      (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
        (onlineStep A (onlineDriverOfRoundNoise z)
          (onlineCorrectedProofExactProcess A hE x0 hBatch k path)).g)
      (onlineRoundLaw A) := by
  classical
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let s := run k path
  let q := primalStep A.stepSize s
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
        onlineWorkerEstimator A (onlineDriverOfRoundNoise z) s i)
      (onlineRoundLaw A) := by
    have hrefreshTerm (j : Fin b.1) : AEStronglyMeasurable
        (fun batch : (w : Worker n) → Fin b.1 → Sample w =>
          stochasticGradient A.problem i (batch i j) q)
        (onlineBatchLaw A.problem b) := by
      have honMap : AEStronglyMeasurable
          (fun xi : Sample i => stochasticGradient A.problem i xi q)
          (Measure.map
            (fun batch : (w : Worker n) → Fin b.1 → Sample w => batch i j)
            (onlineBatchLaw A.problem b)) := by
        rw [onlineBatchLaw_coordinate_marginal]
        exact (hVariance.1.2 i q).1.aestronglyMeasurable
      simpa only [Function.comp_apply] using
        honMap.comp_aemeasurable
          (((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable)
    have hrefreshBatch : AEStronglyMeasurable
        (fun batch : (w : Worker n) → Fin b.1 → Sample w =>
          average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (batch i j) q))
        (onlineBatchLaw A.problem b) := by
      unfold average SOptLib.finiteUniformAverage
      have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => hrefreshTerm j)).const_smul
          ((Fintype.card (Fin b.1) : ℝ)⁻¹)
      refine hsum.congr (Filter.Eventually.of_forall ?_)
      intro batch
      simp [Finset.sum_apply]
    have hrefresh : AEStronglyMeasurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (z.2.1.1 i j) q))
        (onlineRoundLaw A) := by
      have honMap : AEStronglyMeasurable
          (fun batch : (w : Worker n) → Fin b.1 → Sample w =>
            average (fun j : Fin b.1 =>
              stochasticGradient A.problem i (batch i j) q))
          (Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.1)
            (onlineRoundLaw A)) := by
        rw [onlineRoundLaw_refreshBatch_marginal]
        exact hrefreshBatch
      simpa only [Function.comp_apply] using
        honMap.comp_aemeasurable
          ((measurable_fst.comp (measurable_fst.comp measurable_snd)).aemeasurable)
    have hdiffIntegrable : Integrable
        (fun batch => onlineBatchDifference A.problem batch i q s.x)
        (onlineBatchLaw A.problem b0) := by
      have h :=
        (onlineAverageSmoothnessCorrected_fixed
          ⟨A.problem, hE⟩ run ell hAverageSmooth k i path).1
      change Integrable
        (fun batch => onlineBatchDifference A.problem batch i
          (run (k + 1) path).x (run k path).x)
        (onlineBatchLaw A.problem b0) at h
      simpa [run, s, q, onlineStep] using h
    have hdiff : AEStronglyMeasurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          onlineBatchDifference A.problem z.2.1.2 i q s.x)
        (onlineRoundLaw A) := by
      have honMap : AEStronglyMeasurable
          (fun batch => onlineBatchDifference A.problem batch i q s.x)
          (Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.1.2)
            (onlineRoundLaw A)) := by
        rw [onlineRoundLaw_differenceBatch_marginal]
        exact hdiffIntegrable.aestronglyMeasurable
      simpa only [Function.comp_apply] using
        honMap.comp_aemeasurable
          ((measurable_snd.comp (measurable_fst.comp measurable_snd)).aemeasurable)
    have hcompression : Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.2 i) :=
      (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd))
    have hquantized : AEStronglyMeasurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          A.quantizer.apply
            (onlineBatchDifference A.problem z.2.1.2 i q s.x) (z.2.2 i))
        (onlineRoundLaw A) := by
      exact (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hdiff.aemeasurable.prodMk hcompression.aemeasurable)).aestronglyMeasurable
    have hcarry : AEStronglyMeasurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => s.g +
          A.quantizer.apply
            (onlineBatchDifference A.problem z.2.1.2 i q s.x) (z.2.2 i))
        (onlineRoundLaw A) :=
      aestronglyMeasurable_const.add hquantized
    let refreshSet : Set (OnlineRoundNoise n b b0 Sample Ξ) :=
      {z | z.1 = true}
    have hrefreshSet : MeasurableSet refreshSet := by
      exact measurable_fst (measurableSet_singleton true)
    have hpiece := AEStronglyMeasurable.piecewise hrefreshSet
      hrefresh.restrict hcarry.restrict
    simpa [onlineWorkerEstimator, onlineDriverOfRoundNoise, onlineDifference,
      q, s, refreshSet, Set.piecewise] using hpiece
  change AEStronglyMeasurable
    (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
      average (fun i : Worker n =>
        onlineWorkerEstimator A (onlineDriverOfRoundNoise z) s i))
    (onlineRoundLaw A)
  unfold average SOptLib.finiteUniformAverage
  have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ => hworker i)).const_smul
      ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hsum.congr (Filter.Eventually.of_forall ?_)
  intro z
  simp [Finset.sum_apply]

/-- The exact stagewise vector regularity needed to combine a generated
strict-prefix state with an independent current Algorithm 3 round.  Unlike
`OnlineGradientKernelRealization`, this predicate is scoped to the canonical
path and round laws and to one recursion stage.  It is not a source
assumption; it names the remaining product-law gluing obligation after the
fixed-prefix theorem above has discharged both branch fibers. -/
def OnlineCorrectedRoundDirectionLawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0) (k : ℕ) : Prop :=
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  AEStronglyMeasurable
    (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ =>
      (onlineStep A (onlineDriverOfRoundNoise p.2) (run k p.1)).g)
    (law.prod (onlineRoundLaw A))

/-- Concrete `k=1` test requested by the reconstruction audit: under the
source moments, every fixed generated prefix supplies an a.e.-measurable full
vector direction for the independent second round.  Thus the remaining
`OnlineCorrectedRoundDirectionLawRegularity ... 1` gap is exactly promotion
from all fixed-prefix fibers to the prefix-law product, not either Algorithm 3
branch or compressor composition in isolation. -/
theorem onlineCorrectedRoundDirection_fixedPrefix_aestronglyMeasurable_one
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (path : ℕ → OnlineRoundNoise n b b0 Sample Ξ) :
    AEStronglyMeasurable
      (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
        (onlineStep A (onlineDriverOfRoundNoise z)
          (onlineCorrectedProofExactProcess A hE x0 hBatch 1 path)).g)
      (onlineRoundLaw A) := by
  exact onlineCorrectedRoundDirection_fixedPrefix_aestronglyMeasurable
    A hE x0 hBatch sigma ell hVariance hAverageSmooth 1 path

/-- The exact stage-law regularity at `k = 1` is sufficient to construct the
two components of the second corrected Algorithm 3 state on an independent
prefix/current-round product.  This is the first recursive consumer of
`OnlineCorrectedRoundDirectionLawRegularity` that does not pass through the
globally measurable-kernel boundary.

The first-round estimator is obtained from the fixed-prefix theorem at the
deterministic initial state and transported along the zeroth iid coordinate.
The second primal point is then a measurable affine function of that
estimator, while the supplied stage-law regularity is exactly the second
estimator component. -/
theorem onlineCorrectedSecondState_components_aestronglyMeasurable_of_stage_one
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (hStage : OnlineCorrectedRoundDirectionLawRegularity A hE x0 hBatch 1) :
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable
        (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
            OnlineRoundNoise n b b0 Sample Ξ ↦
          (onlineStep A (onlineDriverOfRoundNoise p.2) (run 1 p.1)).x)
        (law.prod (onlineRoundLaw A)) ∧
      AEStronglyMeasurable
        (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
            OnlineRoundNoise n b b0 Sample Ξ ↦
          (onlineStep A (onlineDriverOfRoundNoise p.2) (run 1 p.1)).g)
        (law.prod (onlineRoundLaw A)) := by
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw
    infer_instance
  let path0 : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let initial := onlineCorrectedExactInitialState A hE x0
  have hround0 : AEStronglyMeasurable
      (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
        (onlineStep A (onlineDriverOfRoundNoise z) initial).g)
      (onlineRoundLaw A) := by
    simpa [initial, run] using
      (onlineCorrectedRoundDirection_fixedPrefix_aestronglyMeasurable
        A hE x0 hBatch sigma ell hVariance hAverageSmooth 0 path0)
  have hmap0 : Measure.map
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path 0) law =
      onlineRoundLaw A := by
    unfold law onlineProofExactPathLaw
    exact SOptLib.iidStreamLaw_map_eval (onlineRoundLaw A) 0
  have hg1 : AEStronglyMeasurable (fun path ↦ (run 1 path).g) law := by
    have honMap : AEStronglyMeasurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
          (onlineStep A (onlineDriverOfRoundNoise z) initial).g)
        (Measure.map
          (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path 0) law) := by
      rw [hmap0]
      exact hround0
    have hpull := honMap.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
    simpa [run, initial] using hpull
  have hx1 : AEStronglyMeasurable (fun path ↦ (run 1 path).x) law := by
    have hconst : (fun path ↦ (run 1 path).x) =
        fun _ ↦ primalStep A.stepSize initial := by
      funext path
      rfl
    rw [hconst]
    exact aestronglyMeasurable_const
  have hx2 : AEStronglyMeasurable
      (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ ↦
        (onlineStep A (onlineDriverOfRoundNoise p.2) (run 1 p.1)).x)
      (law.prod (onlineRoundLaw A)) := by
    have hx1prod : AEStronglyMeasurable
        (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
            OnlineRoundNoise n b b0 Sample Ξ ↦ (run 1 p.1).x)
        (law.prod (onlineRoundLaw A)) := hx1.comp_fst
    have hg1prod : AEStronglyMeasurable
        (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
            OnlineRoundNoise n b b0 Sample Ξ ↦ (run 1 p.1).g)
        (law.prod (onlineRoundLaw A)) := hg1.comp_fst
    simpa [onlineStep, primalStep_eq] using
      hx1prod.sub (hg1prod.const_smul (A.stepSize : ℝ))
  exact ⟨hx2, hStage⟩

/-- The sigma-algebra generated by Algorithm 3 round coordinates strictly
before `k`. -/
@[reducible] def onlineStrictPast {n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (k : ℕ) : MeasurableSpace (ℕ → OnlineRoundNoise n b b0 Sample Ξ) :=
  ⨆ j : Fin k, MeasurableSpace.comap
    (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path j) inferInstance

theorem onlineStrictPast_coordinate_measurable
    {n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    {j k : ℕ} (hjk : j < k) :
    Measurable[onlineStrictPast (n := n) (b := b) (b0 := b0)
      (Sample := Sample) (Ξ := Ξ) k]
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path j) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le ⟨j, hjk⟩ (by rfl)

theorem onlineStrictPast_le
    {n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ] (k : ℕ) :
    onlineStrictPast (n := n) (b := b) (b0 := b0)
        (Sample := Sample) (Ξ := Ξ) k ≤
      (inferInstance :
        MeasurableSpace (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) := by
  refine iSup_le fun j => ?_
  exact (measurable_pi_apply (j : ℕ)).comap_le

/-- Conditional adaptedness theorem for the corrected proof-exact Algorithm 3
process.  This proves the entire minibatch/worker/transition/recursion chain;
the only additional input is the explicitly named, source-unstated kernel
realization rather than a postulated adaptedness assertion. -/
theorem onlineCorrectedProofExactProcess_strictPast_measurable_of_kernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (hE : OnlineExpectationRealization A.problem) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ) :
    Measurable[onlineStrictPast (n := n) (b := b) (b0 := b0)
      (Sample := Sample) (Ξ := Ξ) k]
      (onlineCorrectedProofExactProcess A hE x0 hBatch k) := by
  let past : Unit →
      MeasurableSpace (ℕ → OnlineRoundNoise n b b0 Sample Ξ) :=
    fun _ => onlineStrictPast (n := n) (b := b) (b0 := b0)
      (Sample := Sample) (Ξ := Ξ) k
  let driver : ℕ → (ℕ → OnlineRoundNoise n b b0 Sample Ξ) →
      OnlineRoundNoise n b b0 Sample Ξ := fun t path => path t
  let step : ℕ → State d → OnlineRoundNoise n b b0 Sample Ξ → State d :=
    fun _ s z => onlineStep A (onlineDriverOfRoundNoise z) s
  apply SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := past)
      (process := onlineCorrectedProofExactProcess A hE x0 hBatch)
      (driver := driver) (step := step) (k := ()) (N := k)
  · change Measurable[past ()]
      (fun _ : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        onlineCorrectedExactInitialState A hE x0)
    exact measurable_const
  · intro t ht _hprocess
    exact onlineStrictPast_coordinate_measurable (Nat.lt_of_succ_le ht)
  · intro _t _ht
    exact onlineStep_round_joint_measurable_of_kernel A hKernel
  · intro t _ht
    rfl
  · exact le_rfl

/-- The exact law-scoped regularity needed to evaluate an Assumption 3.3
refresh sample at the adaptive Algorithm 3 query `x^{k+1}`.  This is strictly
weaker than `OnlineGradientKernelRealization`: it asks only for the generated
query to be a random variable and for the locally centered squared residual to
be a.e. strongly measurable under that query law times the one fresh worker
sample law.  It is kept separate from `OnlineProblem` and from Eq. (46)'s
theorem head because Assumptions 3.2--3.3 state the fixed-query moments but do
not state this probability-regularity premise. -/
def OnlineAdaptiveRefreshResidualLawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (k : ℕ) (i : Worker n) : Prop :=
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  let query := fun path => (run (k + 1) path).x
  AEMeasurable query law ∧
    AEStronglyMeasurable
      (fun p : Point d × Sample i =>
        ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2)
      ((Measure.map query law).prod (A.problem.sampleLaw i))

/-- Exact-law random-variable obligation for Assumption 3.2's centered
fresh-batch difference at the generated pair `(x^{k+1},x^k)`.  It is an
internal proof obligation, not an additional clause of the paper's average
smoothness assumption. -/
def OnlineGeneratedDifferenceLawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (k : ℕ) (i : Worker n) : Prop :=
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  AEStronglyMeasurable
    (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((w : Worker n) → Fin b0.1 → Sample w) =>
      onlineBatchDifference A.problem p.2 i
          (run (k + 1) p.1).x (run k p.1).x -
        localGradientDifference P i
          (run (k + 1) p.1).x (run k p.1).x)
    (law.prod (onlineBatchLaw A.problem b0))

/-- At the first genuinely adaptive pair `(x²,x¹)`, the source moment
assumptions prove every section needed by the desired product-law random
variable.  For each fixed minibatch the path section is a.e. strongly
measurable, using Mathlib measurability of the totalized derivative; for each
fixed path the minibatch section is integrable by Assumption 3.2.

This theorem deliberately stops short of claiming that the two section
families are jointly a.e. strongly measurable.  Separate measurability is not
a product-measurability API, and identifying that exact promotion is the
purpose of the iteration-10 successor attempt below. -/
theorem onlineGeneratedDifference_one_separate_sections
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (i : Worker n) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
    let queryPair := fun path ↦ ((run 2 path).x, (run 1 path).x)
    let centered := fun
        (path : ℕ → OnlineRoundNoise n b b0 Sample Ξ)
        (batch : (w : Worker n) → Fin b0.1 → Sample w) ↦
      onlineBatchDifference A.problem batch i (run 2 path).x (run 1 path).x -
        localGradientDifference P i (run 2 path).x (run 1 path).x
    AEMeasurable queryPair law ∧
      (∀ batch, AEStronglyMeasurable (fun path ↦ centered path batch) law) ∧
      (∀ path, AEStronglyMeasurable (centered path)
        (onlineBatchLaw A.problem b0)) := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  let queryPair := fun path ↦ ((run 2 path).x, (run 1 path).x)
  let centered := fun
      (path : ℕ → OnlineRoundNoise n b b0 Sample Ξ)
      (batch : (w : Worker n) → Fin b0.1 → Sample w) ↦
    onlineBatchDifference A.problem batch i (run 2 path).x (run 1 path).x -
      localGradientDifference P i (run 2 path).x (run 1 path).x
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate1 : AEMeasurable (run 1) law := by
    let initial := onlineCorrectedExactInitialState A hE x0
    let path0 : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
      Classical.choice (nonempty_of_isProbabilityMeasure law)
    have hround0 : AEStronglyMeasurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
          (onlineStep A (onlineDriverOfRoundNoise z) initial).g)
        (onlineRoundLaw A) := by
      simpa [initial, run] using
        (onlineCorrectedRoundDirection_fixedPrefix_aestronglyMeasurable
          A hE x0 hBatch sigma ell hVariance hAverageSmooth 0 path0)
    have hmap0 : Measure.map
        (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path 0) law =
        onlineRoundLaw A := by
      unfold law onlineProofExactPathLaw
      exact SOptLib.iidStreamLaw_map_eval (onlineRoundLaw A) 0
    have hg1 : AEStronglyMeasurable (fun path ↦ (run 1 path).g) law := by
      have honMap : AEStronglyMeasurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
            (onlineStep A (onlineDriverOfRoundNoise z) initial).g)
          (Measure.map
            (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path 0) law) := by
        rw [hmap0]
        exact hround0
      simpa [run, initial] using
        honMap.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
    have hx1' : AEStronglyMeasurable (fun path ↦ (run 1 path).x) law := by
      have hconst : (fun path ↦ (run 1 path).x) =
          fun _ ↦ primalStep A.stepSize initial := by
        funext path
        rfl
      rw [hconst]
      exact aestronglyMeasurable_const
    have hpair' : AEMeasurable
        (fun path ↦ ((run 1 path).x, (run 1 path).g)) law :=
      hx1'.aemeasurable.prodMk hg1.aemeasurable
    change AEMeasurable (run 1) law
    exact (measurable_state_mk d).comp_aemeasurable hpair'
  have hx1 : AEMeasurable (fun path ↦ (run 1 path).x) law :=
    (measurable_state_x d).comp_aemeasurable hstate1
  have hx2 : AEMeasurable (fun path ↦ (run 2 path).x) law := by
    have hstep : AEMeasurable (fun path ↦ primalStep A.stepSize (run 1 path)) law :=
      (measurable_primalStep A.stepSize).comp_aemeasurable hstate1
    simpa [run, onlineStep] using hstep
  have hpair : AEMeasurable queryPair law := hx2.prodMk hx1
  refine ⟨hpair, ?_, ?_⟩
  · intro batch
    have hlocal : Measurable (fun q : Point d × Point d ↦
        localGradientDifference P i q.1 q.2) := by
      exact ((measurable_localGradient P i).comp measurable_fst).sub
        ((measurable_localGradient P i).comp measurable_snd)
    have hkernel : Measurable (fun q : Point d × Point d ↦
        onlineBatchDifference A.problem batch i q.1 q.2 -
          localGradientDifference P i q.1 q.2) :=
      (onlineBatchDifference_queryPair_measurable A.problem batch i).sub hlocal
    exact (hkernel.comp_aemeasurable hpair).aestronglyMeasurable
  · intro path
    have hdiff : Integrable (fun batch ↦
        onlineBatchDifference A.problem batch i (run 2 path).x (run 1 path).x)
        (onlineBatchLaw A.problem b0) :=
      (hAverageSmooth.2 1 i path).1
    exact (hdiff.sub (integrable_const (c :=
      localGradientDifference P i (run 2 path).x (run 1 path).x))).aestronglyMeasurable

/-- Separate path sections are sufficient for product-law a.e. strong
measurability when the fresh coordinate is countable with measurable
singletons.  This is a genuine product promotion, not a fixed-section
restatement: the countable law is decomposed into its Dirac atoms and the
section representatives are assembled through `Measure.sum`.

The result also isolates why a law-scoped countermodel for the online MARINA
interface cannot reuse a finite or countable sample space: any such example
automatically satisfies the missing product regularity. -/
theorem aestronglyMeasurable_prod_of_countable_right_sections
    {Omega S E : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S]
    [NormedAddCommGroup E]
    (mu : Measure Omega) (nu : Measure S) [SFinite mu]
    (f : Omega × S → E)
    (hsections : ∀ s, AEStronglyMeasurable (fun omega ↦ f (omega, s)) mu) :
    AEStronglyMeasurable f (mu.prod nu) := by
  rw [← nu.sum_smul_dirac, Measure.prod_sum_right]
  apply AEStronglyMeasurable.sum_measure
  intro s
  rw [Measure.prod_smul_right, Measure.prod_dirac]
  apply AEStronglyMeasurable.smul_measure
  exact (measurableEmbedding_prod_mk_right s).aestronglyMeasurable_map_iff.mpr
    (by simpa only [Function.comp_apply] using hsections s)

/-- At the first adaptive successor, the source moment assumptions do imply
the exact generated-difference law regularity for countable online sample
spaces.  The theorem consumes the complete separate-section result above and
promotes it to the product law; hence any failure of the unrestricted source
interface must be essentially uncountable rather than a finite-support
artifact. -/
theorem onlineGeneratedDifferenceLawRegularity_one_of_countable_samples
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    [∀ i, Countable (Sample i)]
    [∀ i, MeasurableSingletonClass (Sample i)]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (i : Worker n) :
    OnlineGeneratedDifferenceLawRegularity A hE x0 hBatch 1 i := by
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsections := onlineGeneratedDifference_one_separate_sections
    A hE x0 hBatch sigma ell hVariance hAverageSmooth i
  change AEStronglyMeasurable
    (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((w : Worker n) → Fin b0.1 → Sample w) ↦
      onlineBatchDifference A.problem p.2 i
          (onlineCorrectedProofExactProcess A hE x0 hBatch 2 p.1).x
          (onlineCorrectedProofExactProcess A hE x0 hBatch 1 p.1).x -
        localGradientDifference (onlineLocalProblemCorrected ⟨A.problem, hE⟩) i
          (onlineCorrectedProofExactProcess A hE x0 hBatch 2 p.1).x
          (onlineCorrectedProofExactProcess A hE x0 hBatch 1 p.1).x)
    (law.prod (onlineBatchLaw A.problem b0))
  exact aestronglyMeasurable_prod_of_countable_right_sections
    law (onlineBatchLaw A.problem b0) _ hsections.2.1

/-- Any a.e.-measurable generated query pair has the exact fresh-minibatch
product-law regularity required by Assumption 3.2.  The stochastic gradients
are constructed as finite-difference limits, so this works for arbitrary
sample spaces without a global kernel-measurability premise. -/
theorem onlineGeneratedDifferenceLawRegularity_of_queryPair_aemeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (k : ℕ) (i : Worker n)
    (hpair : AEMeasurable
      (fun path ↦
        ((onlineCorrectedProofExactProcess A hE x0 hBatch (k + 1) path).x,
          (onlineCorrectedProofExactProcess A hE x0 hBatch k path).x))
      (onlineProofExactPathLaw (b := b) (b0 := b0) A)) :
    OnlineGeneratedDifferenceLawRegularity A hE x0 hBatch k i := by
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let batchLaw := onlineBatchLaw A.problem b0
  let queryPair := fun path ↦ ((run (k + 1) path).x, (run k path).x)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  have hpair' : AEMeasurable queryPair law := by
    simpa [queryPair, run, law] using hpair
  have hnext : AEStronglyMeasurable (fun path ↦ (run (k + 1) path).x) law :=
    ((measurable_fst.comp_aemeasurable hpair').aestronglyMeasurable)
  have hcurrent : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    ((measurable_snd.comp_aemeasurable hpair').aestronglyMeasurable)
  have hcoord_integrable (j : Fin b0.1) (x : Point d) :
      Integrable
        (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦
          A.problem.sampleLoss i (batch i j) x) batchLaw := by
    let coord := fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i j
    have hm : Integrable (fun xi ↦ A.problem.sampleLoss i xi x)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.problem.sampleLaw i by
        simpa [coord, batchLaw] using onlineBatchLaw_coordinate_marginal
          A.problem i j]
      exact A.problem.sampleLoss_integrable i x
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable)).mp hm
  have hcoord_differentiable (j : Fin b0.1) :
      ∀ᵐ batch ∂batchLaw,
        Differentiable ℝ (A.problem.sampleLoss i (batch i j)) := by
    let coord := fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i j
    have hmap : Measure.map coord batchLaw = A.problem.sampleLaw i := by
      simpa [coord, batchLaw] using onlineBatchLaw_coordinate_marginal
        A.problem i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
        (A.problem.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop), by rw [hmap]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hgradient_next (j : Fin b0.1) : AEStronglyMeasurable
      (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b0.1 → Sample w) ↦
        stochasticGradient A.problem i (p.2 i j) (run (k + 1) p.1).x)
      (law.prod batchLaw) := by
    exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A.problem i law batchLaw (fun path ↦ (run (k + 1) path).x)
        (fun batch ↦ batch i j) hnext (hcoord_differentiable j)
        (hcoord_integrable j)
  have hgradient_current (j : Fin b0.1) : AEStronglyMeasurable
      (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b0.1 → Sample w) ↦
        stochasticGradient A.problem i (p.2 i j) (run k p.1).x)
      (law.prod batchLaw) := by
    exact stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A.problem i law batchLaw (fun path ↦ (run k path).x)
        (fun batch ↦ batch i j) hcurrent (hcoord_differentiable j)
        (hcoord_integrable j)
  have hbatch : AEStronglyMeasurable
      (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b0.1 → Sample w) ↦
        onlineBatchDifference A.problem p.2 i
          (run (k + 1) p.1).x (run k p.1).x)
      (law.prod batchLaw) := by
    unfold onlineBatchDifference average SOptLib.finiteUniformAverage
    have hsum := Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ (hgradient_next j).sub (hgradient_current j))
    refine (hsum.const_smul ((Fintype.card (Fin b0.1) : ℝ)⁻¹)).congr
      (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, Finset.sum_sub_distrib]
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  have hlocalKernel : Measurable
      (fun q : Point d × Point d ↦ localGradientDifference P i q.1 q.2) := by
    unfold localGradientDifference localGradient
    exact ((measurable_gradient (P.localLoss i)).comp measurable_fst).sub
      ((measurable_gradient (P.localLoss i)).comp measurable_snd)
  have hlocalPath : AEStronglyMeasurable
      (fun path ↦ localGradientDifference P i
        (run (k + 1) path).x (run k path).x)
      law := by
    exact (hlocalKernel.comp_aemeasurable hpair').aestronglyMeasurable
  change AEStronglyMeasurable
    (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((w : Worker n) → Fin b0.1 → Sample w) ↦
      onlineBatchDifference A.problem p.2 i
          (run (k + 1) p.1).x (run k p.1).x -
        localGradientDifference P i (run (k + 1) p.1).x (run k p.1).x)
    (law.prod batchLaw)
  exact hbatch.sub hlocalPath.comp_fst

/-- The first adaptive generated-difference regularity, now without the
countability restriction of the earlier diagnostic specialization. -/
theorem onlineGeneratedDifferenceLawRegularity_one
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (i : Worker n) :
    OnlineGeneratedDifferenceLawRegularity A hE x0 hBatch 1 i := by
  have hsections := onlineGeneratedDifference_one_separate_sections
    A hE x0 hBatch sigma ell hVariance hAverageSmooth i
  apply onlineGeneratedDifferenceLawRegularity_of_queryPair_aemeasurable
    A hE x0 hBatch sigma hVariance 1 i
  simpa using hsections.1

/-- At `k=0` the proof-exact generated pair is deterministic, so the fixed
Assumption 3.2 fiber supplies the exact product-law random variable without
any joint stochastic-gradient-kernel hypothesis. -/
theorem onlineGeneratedDifferenceLawRegularity_zero
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (ell : Worker n → ℝ)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (i : Worker n) :
    OnlineGeneratedDifferenceLawRegularity A hE x0 hBatch 0 i := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let path0 : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  have hdiff : Integrable
      (fun batch => onlineBatchDifference A.problem batch i
          (run 1 path0).x (run 0 path0).x)
      (onlineBatchLaw A.problem b0) :=
    (hAverageSmooth.2 0 i path0).1
  have hcenter : Integrable
      (fun batch => onlineBatchDifference A.problem batch i
          (run 1 path0).x (run 0 path0).x -
        localGradientDifference P i (run 1 path0).x (run 0 path0).x)
      (onlineBatchLaw A.problem b0) :=
    hdiff.sub (integrable_const (c :=
      localGradientDifference P i (run 1 path0).x (run 0 path0).x))
  have hprod := hcenter.aestronglyMeasurable.comp_snd (μ := law)
  change AEStronglyMeasurable
    (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((w : Worker n) → Fin b0.1 → Sample w) =>
      onlineBatchDifference A.problem p.2 i (run 1 p.1).x (run 0 p.1).x -
        localGradientDifference P i (run 1 p.1).x (run 0 p.1).x)
    (law.prod (onlineBatchLaw A.problem b0))
  exact hprod.congr (Filter.Eventually.of_forall fun p => by rfl)

/-- The first proof-exact Algorithm 3 state is an exact-law random variable
under the original fixed moment assumptions.  This is the largest recursive
base case available without promoting separate fixed-query measurability to a
joint stochastic-gradient kernel. -/
theorem onlineCorrectedProofExactProcess_aemeasurable_one
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell) :
    AEMeasurable
      (onlineCorrectedProofExactProcess A hE x0 hBatch 1)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let initial := onlineCorrectedExactInitialState A hE x0
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let path0 : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  have hround0 : AEStronglyMeasurable
      (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
        (onlineStep A (onlineDriverOfRoundNoise z) initial).g)
      (onlineRoundLaw A) := by
    simpa [initial, run] using
      (onlineCorrectedRoundDirection_fixedPrefix_aestronglyMeasurable
        A hE x0 hBatch sigma ell hVariance hAverageSmooth 0 path0)
  have hmap0 : Measure.map
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path 0) law =
      onlineRoundLaw A := by
    unfold law onlineProofExactPathLaw
    exact SOptLib.iidStreamLaw_map_eval (onlineRoundLaw A) 0
  have hg1 : AEStronglyMeasurable (fun path => (run 1 path).g) law := by
    have honMap : AEStronglyMeasurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
          (onlineStep A (onlineDriverOfRoundNoise z) initial).g)
        (Measure.map
          (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path 0) law) := by
      rw [hmap0]
      exact hround0
    simpa [run, initial] using
      honMap.comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  have hx1 : AEStronglyMeasurable (fun path => (run 1 path).x) law := by
    have hconst : (fun path => (run 1 path).x) =
        fun _ => primalStep A.stepSize initial := by
      funext path
      rfl
    rw [hconst]
    exact aestronglyMeasurable_const
  have hpair : AEMeasurable
      (fun path => ((run 1 path).x, (run 1 path).g)) law :=
    hx1.aemeasurable.prodMk hg1.aemeasurable
  change AEMeasurable (run 1) law
  exact (measurable_state_mk d).comp_aemeasurable hpair

/-- Once the generated refresh query is a random variable, Assumption 3.3's
sampled-loss differentiability derives the exact residual product-law
regularity at every iteration. -/
theorem onlineAdaptiveRefreshResidualLawRegularity_of_query_aemeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (k : ℕ) (i : Worker n)
    (hquery : AEMeasurable
      (fun path ↦
        (onlineCorrectedProofExactProcess A hE x0 hBatch (k + 1) path).x)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A)) :
    OnlineAdaptiveRefreshResidualLawRegularity A hE x0 hBatch k i := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let query := fun path ↦ (run (k + 1) path).x
  have hquery' : AEMeasurable query law := by
    simpa [query, run, law] using hquery
  change AEMeasurable query law ∧
    AEStronglyMeasurable
      (fun p : Point d × Sample i ↦
        ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2)
      ((Measure.map query law).prod (A.problem.sampleLaw i))
  refine ⟨hquery', ?_⟩
  have hgradient :=
    stochasticGradient_product_aestronglyMeasurable_of_differentiable
      A.problem hVariance.2 i (Measure.map query law)
  have hlocal : AEStronglyMeasurable
      (fun p : Point d × Sample i ↦ localGradient P i p.1)
      ((Measure.map query law).prod (A.problem.sampleLaw i)) := by
    exact ((measurable_gradient (P.localLoss i)).comp measurable_fst).aestronglyMeasurable
  have hnorm := (hgradient.sub hlocal).norm
  simpa [pow_two] using hnorm.mul hnorm

/-- Arbitrary-iteration Eq. (46) regularity bundle.  This is the compiled
consumer of the finite-prefix process induction and both adaptive
fresh-sample suppliers; no global stochastic-gradient kernel or postulated
adaptedness is used. -/
theorem onlineEq46_all_exactLaw_regularities
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (k : ℕ) (i : Worker n) :
    OnlineGeneratedDifferenceLawRegularity A hE x0 hBatch k i ∧
      OnlineAdaptiveRefreshResidualLawRegularity A hE x0 hBatch k i ∧
      AEMeasurable
        (onlineCorrectedProofExactProcess A hE x0 hBatch k)
        (onlineProofExactPathLaw (b := b) (b0 := b0) A) ∧
      AEMeasurable
        (onlineCorrectedProofExactProcess A hE x0 hBatch (k + 1))
        (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  have hk : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineCorrectedProofExactProcess_all_aemeasurable
        A hE x0 hBatch sigma hVariance k
  have hsucc : AEMeasurable (run (k + 1)) law := by
    simpa [run, law] using
      onlineCorrectedProofExactProcess_all_aemeasurable
        A hE x0 hBatch sigma hVariance (k + 1)
  have hxk : AEMeasurable (fun path => (run k path).x) law :=
    (measurable_state_x d).comp_aemeasurable hk
  have hxsucc : AEMeasurable (fun path => (run (k + 1) path).x) law :=
    (measurable_state_x d).comp_aemeasurable hsucc
  have hdifference :=
    onlineGeneratedDifferenceLawRegularity_of_queryPair_aemeasurable
      A hE x0 hBatch sigma hVariance k i (hxsucc.prodMk hxk)
  have hrefresh :=
    onlineAdaptiveRefreshResidualLawRegularity_of_query_aemeasurable
      A hE x0 hBatch sigma hVariance k i hxsucc
  exact ⟨hdifference, hrefresh, hk, hsucc⟩

/-- The exact law-scoped refresh regularity is derivable at the first update
without a global kernel hypothesis: `x¹` is deterministic under the proof-exact
initialization, so Assumption 3.3's fixed-query integrability supplies the
sample fiber and the first product coordinate is almost surely constant.  This
is the base case of any faithful law-scoped induction; the unresolved issue is
the genuinely adaptive successor step. -/
theorem onlineAdaptiveRefreshResidualLawRegularity_zero
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (i : Worker n) :
    OnlineAdaptiveRefreshResidualLawRegularity A hE x0 hBatch 0 i := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  let q := primalStep A.stepSize (onlineCorrectedExactInitialState A hE x0)
  have hquery : (fun path => (run 1 path).x) = fun _ => q := by
    funext path
    rfl
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  change AEMeasurable (fun path => (run 1 path).x) law ∧
    AEStronglyMeasurable
      (fun p : Point d × Sample i =>
        ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2)
      ((Measure.map (fun path => (run 1 path).x) law).prod
        (A.problem.sampleLaw i))
  constructor
  · rw [hquery]
    exact measurable_const.aemeasurable
  · rw [hquery, Measure.map_const, measure_univ, one_smul]
    have hfiber : AEStronglyMeasurable
        (fun xi : Sample i =>
          ‖stochasticGradient A.problem i xi q - localGradient P i q‖ ^ 2)
        (A.problem.sampleLaw i) :=
      (hVariance.1.2 i q).2.1.aestronglyMeasurable
    have hbase : AEStronglyMeasurable
        (fun p : Point d × Sample i =>
          ‖stochasticGradient A.problem i p.2 q - localGradient P i q‖ ^ 2)
        ((Measure.dirac q).prod (A.problem.sampleLaw i)) :=
      hfiber.comp_snd
    have hfirst :
        (fun x : Point d => x) =ᵐ[Measure.dirac q] fun _ => q := by
      change ∀ᵐ x ∂Measure.dirac q, x = q
      exact (MeasureTheory.ae_dirac_iff (measurableSet_singleton q)).2 rfl
    have hfirstProd :
        (fun p : Point d × Sample i => p.1) =ᵐ[
            (Measure.dirac q).prod (A.problem.sampleLaw i)] fun _ => q :=
      (Measure.quasiMeasurePreserving_fst
        (μ := Measure.dirac q) (ν := A.problem.sampleLaw i)).ae_eq_comp hfirst
    exact hbase.congr (hfirstProd.mono fun p hp => by simp [hp])

/-- Compiled Eq. (46) dependency-cone consumer for the first transition.  It
combines the exact fresh-difference law, the exact refresh-residual law, and
measurability of the generated successor state using only the restored source
moment assumptions. -/
theorem onlineEq46_base_exactLaw_regularities
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma ell : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ell)
    (i : Worker n) :
    OnlineGeneratedDifferenceLawRegularity A hE x0 hBatch 0 i ∧
      OnlineAdaptiveRefreshResidualLawRegularity A hE x0 hBatch 0 i ∧
      AEMeasurable
        (onlineCorrectedProofExactProcess A hE x0 hBatch 1)
        (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
  exact ⟨onlineGeneratedDifferenceLawRegularity_zero
      A hE x0 hBatch ell hAverageSmooth i,
    onlineAdaptiveRefreshResidualLawRegularity_zero
      A hE x0 hBatch sigma hVariance i,
    onlineCorrectedProofExactProcess_aemeasurable_one
      A hE x0 hBatch sigma ell hVariance hAverageSmooth⟩

/-- The former global-kernel route really does imply the exact law-scoped
refresh regularity.  This theorem is diagnostic: its converse is neither used
nor claimed, and the source-facing Eq. (46) assumptions do not provide
`hKernel`. -/
theorem onlineAdaptiveRefreshResidualLawRegularity_of_kernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (hE : OnlineExpectationRealization A.problem) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ) (i : Worker n) :
    OnlineAdaptiveRefreshResidualLawRegularity A hE x0 hBatch k i := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  let query := fun path => (run (k + 1) path).x
  have hstatePast :=
    onlineCorrectedProofExactProcess_strictPast_measurable_of_kernel
      A hKernel hE x0 hBatch (k + 1)
  have hstate : Measurable (run (k + 1)) :=
    hstatePast.mono
      (onlineStrictPast_le (n := n) (b := b) (b0 := b0)
        (Sample := Sample) (Ξ := Ξ) (k + 1)) le_rfl
  have hquery : Measurable query :=
    (measurable_state_x d).comp hstate
  have hsample : Measurable (fun p : Point d × Sample i =>
      stochasticGradient A.problem i p.2 p.1) := hKernel i
  have htarget : Measurable (fun p : Point d × Sample i =>
      localGradient P i p.1) :=
    (measurable_localGradient P i).comp measurable_fst
  change AEMeasurable query law ∧
    AEStronglyMeasurable
      (fun p : Point d × Sample i =>
        ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2)
      ((Measure.map query law).prod (A.problem.sampleLaw i))
  exact ⟨hquery.aemeasurable,
    (hsample.sub htarget).norm.pow_const 2 |>.aestronglyMeasurable⟩

/-- Assumption 3.3 transfers to the adaptive refresh query once the exact
law-scoped regularity above is available.  Unlike the earlier conditional
transition chain, this declaration reaches the reusable random-query variance
API and exposes precisely the still-missing source/interface fact rather than
requiring global measurability on null sample values. -/
theorem onlineAdaptiveRefreshResidual_product_secondMoment_le
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (k : ℕ) (i : Worker n)
    (hRegularity :
      OnlineAdaptiveRefreshResidualLawRegularity A hE x0 hBatch k i) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
    let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
      (run (k + 1) path).x
    Integrable
        (fun p : Point d × Sample i =>
          ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2)
        ((Measure.map query law).prod (A.problem.sampleLaw i)) ∧
      (∫ p : Point d × Sample i,
          ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2
          ∂((Measure.map query law).prod (A.problem.sampleLaw i))) ≤
        (sigma i) ^ 2 := by
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run (k + 1) path).x
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure (Measure.map query law) :=
    Measure.isProbabilityMeasure_map hRegularity.1
  have htransfer :=
    randomQuery_oracleResidual_sq_integrable_and_integral_le_of_indep_fixed
      (P := (Measure.map query law).prod (A.problem.sampleLaw i))
      (query := Prod.fst) (sample := Prod.snd)
      (G := fun x xi => stochasticGradient A.problem i xi x)
      (target := localGradient P i) (sigma i ^ 2)
      (by
        simpa only [Measure.map_fst_prod, Measure.map_snd_prod,
          measure_univ, one_smul] using hRegularity.2)
      measurable_fst.aemeasurable measurable_snd.aemeasurable
      (ProbabilityTheory.indepFun_prod measurable_id measurable_id)
      (by
        intro x
        simpa only [Measure.map_snd_prod, measure_univ, one_smul] using
          ⟨(hVariance.1.2 i x).2.1, (hVariance.1.2 i x).2.2.2⟩)
  simpa only [Measure.map_fst_prod, Measure.map_snd_prod,
    measure_univ, one_smul] using htransfer

/-- At the first Algorithm 3 refresh query, Assumption 3.3 alone therefore
gives the nonfallback adaptive second-moment statement.  This declaration
immediately consumes the law-scoped base supplier above; no kernel-realization
premise is present. -/
theorem onlineAdaptiveRefreshResidual_product_secondMoment_le_zero
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ sigma)
    (i : Worker n) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) (A := A)
    let query := fun path => (run 1 path).x
    Integrable
        (fun p : Point d × Sample i =>
          ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2)
        ((Measure.map query law).prod (A.problem.sampleLaw i)) ∧
      (∫ p : Point d × Sample i,
          ‖stochasticGradient A.problem i p.2 p.1 - localGradient P i p.1‖ ^ 2
          ∂((Measure.map query law).prod (A.problem.sampleLaw i))) ≤
        (sigma i) ^ 2 := by
  exact onlineAdaptiveRefreshResidual_product_secondMoment_le
    A hE x0 hBatch sigma hVariance 0 i
      (onlineAdaptiveRefreshResidualLawRegularity_zero
        A hE x0 hBatch sigma hVariance i)

/-- Squared estimator error of the well-scoped minibatch-at-`x⁰`
initialization. -/
noncomputable def onlineInitialEstimatorErrorSq {d n b : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (z : OnlineInitialSamples n b Sample) : ℝ :=
  ‖(onlineInitialState A z x0).g -
    globalGradient (onlineLocalProblem A.problem) x0‖ ^ 2

/-- Expected initial estimator error of the corrected executable process. -/
noncomputable def expectedOnlineInitialEstimatorErrorSq {d n b : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) : ℝ :=
  ∫ z, onlineInitialEstimatorErrorSq A x0 { sample := z }
    ∂onlineBatchLaw A.problem b

/-- The corrected minibatch initialization has the usual `σ²/(nb)` error.
This is derived from Assumption 3.3, the differentiability part of Assumption
1.2, and the canonical independent minibatch law; neither condition is made
primitive `OnlineProblem` data. -/
theorem expectedOnlineInitialEstimatorErrorSq_le {d n b : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ) (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ ((onlineLocalProblem A.problem).localLoss i)) :
    expectedOnlineInitialEstimatorErrorSq (b := b) A x0 ≤
      varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  let P := A.problem
  let rowLaw (i : Worker n) : Measure (Fin b.1 → Sample i) :=
    Measure.infinitePi (fun _ : Fin b.1 => P.sampleLaw i)
  let μ : Measure ((i : Worker n) → Fin b.1 → Sample i) :=
    onlineBatchLaw P b
  let target (i : Worker n) : Point d :=
    localGradient (onlineLocalProblem P) i x0
  let residual (i : Worker n) (xi : Sample i) : Point d :=
    stochasticGradient P i xi x0 - target i
  let rowResidual (i : Worker n) (row : Fin b.1 → Sample i) : Point d :=
    average (fun j : Fin b.1 => residual i (row j))
  let workerResidual (i : Worker n)
      (batch : (i : Worker n) → Fin b.1 → Sample i) : Point d :=
    rowResidual i (batch i)
  letI (i : Worker n) : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  letI (i : Worker n) : IsProbabilityMeasure (rowLaw i) := by
    dsimp [rowLaw]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, onlineBatchLaw]
    infer_instance
  have hcoord (i : Worker n) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i) μ =
        rowLaw i := by
    dsimp [μ, rowLaw, onlineBatchLaw]
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun i : Worker n =>
          Measure.infinitePi (fun _ : Fin b.1 => P.sampleLaw i)) i)
  have hsample (i : Worker n) (j : Fin b.1) :
      Measure.map (fun row : Fin b.1 → Sample i => row j) (rowLaw i) =
        P.sampleLaw i := by
    dsimp [rowLaw]
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin b.1 => P.sampleLaw i) j)
  have hresidual_int (i : Worker n) :
      Integrable (residual i) (P.sampleLaw i) := by
    rcases hVariance.1.2 i x0 with ⟨hgrad, _hres2, _hmean, _hsecond⟩
    exact hgrad.sub (integrable_const (c := target i))
  have hresidual_mean (i : Worker n) :
      (∫ xi, residual i xi ∂P.sampleLaw i) = 0 := by
    rcases hVariance.1.2 i x0 with ⟨hgrad, _hres2, hmean, _hsecond⟩
    dsimp [residual, target, P]
    calc
      (∫ xi, stochasticGradient A.problem i xi x0 -
          localGradient (onlineLocalProblem A.problem) i x0
          ∂A.problem.sampleLaw i) =
          (∫ xi, stochasticGradient A.problem i xi x0
            ∂A.problem.sampleLaw i) -
            ∫ _xi : Sample i,
              localGradient (onlineLocalProblem A.problem) i x0
              ∂A.problem.sampleLaw i := by
                exact integral_sub hgrad
                  (integrable_const
                    (c := localGradient (onlineLocalProblem A.problem) i x0))
      _ = 0 := by simp [hmean]
  have hrow_term_int (i : Worker n) (j : Fin b.1) :
      Integrable (fun row : Fin b.1 → Sample i => residual i (row j))
        (rowLaw i) := by
    have hmap_int : Integrable (residual i)
        (Measure.map (fun row : Fin b.1 → Sample i => row j) (rowLaw i)) := by
      rw [hsample i j]
      exact hresidual_int i
    have hmap_aesm : AEStronglyMeasurable (residual i)
        (Measure.map (fun row : Fin b.1 → Sample i => row j) (rowLaw i)) :=
      hmap_int.aestronglyMeasurable
    exact
      (MeasureTheory.integrable_map_measure hmap_aesm
        (measurable_pi_apply j).aemeasurable).mp hmap_int
  have hrow_term_mean (i : Worker n) (j : Fin b.1) :
      (∫ row : Fin b.1 → Sample i, residual i (row j) ∂rowLaw i) = 0 := by
    have hmap_aesm : AEStronglyMeasurable (residual i)
        (Measure.map (fun row : Fin b.1 → Sample i => row j) (rowLaw i)) := by
      rw [hsample i j]
      exact (hresidual_int i).aestronglyMeasurable
    have hmap := MeasureTheory.integral_map
      (μ := rowLaw i) (φ := fun row : Fin b.1 → Sample i => row j)
      (measurable_pi_apply j).aemeasurable hmap_aesm
    rw [hsample i j, hresidual_mean i] at hmap
    exact hmap.symm
  have hrowResidual_int (i : Worker n) :
      Integrable (rowResidual i) (rowLaw i) := by
    dsimp [rowResidual, average, SOptLib.finiteUniformAverage]
    have hsum := MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _ => hrow_term_int i j)
    simpa [Pi.smul_apply] using hsum.smul ((b.1 : ℝ)⁻¹)
  have hrowResidual_mean (i : Worker n) :
      (∫ row, rowResidual i row ∂rowLaw i) = 0 := by
    dsimp [rowResidual, average, SOptLib.finiteUniformAverage]
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun j _ => hrow_term_int i j)]
    simp [hrow_term_mean]
  have hcenter (i : Worker n) (row : Fin b.1 → Sample i) :
      average (fun j : Fin b.1 => stochasticGradient P i (row j) x0) - target i =
        rowResidual i row := by
    dsimp [rowResidual, residual]
    unfold average
    simpa [SOptLib.finiteUniformAverage] using
      (miniBatchAverage_sub_target_eq_average_residual
        (Finset.univ : Finset (Fin b.1)) b.1 (by simp) b.2
        (fun j => stochasticGradient P i (row j) x0) (target i))
  have hdiag (i : Worker n) :
      Integrable (fun batch => ‖workerResidual i batch‖ ^ 2) μ ∧
        (∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) ≤ (σ i) ^ 2 / b.1 := by
    have h := heterogeneousOnline_refresh_secondMoment_le
      P σ (fun _ : Worker n => b) hVariance i x0
    have hsquare (batch : (i : Worker n) → Fin b.1 → Sample i) :
        ‖workerResidual i batch‖ ^ 2 =
          ‖average (fun j : Fin b.1 => stochasticGradient P i (batch i j) x0) -
            localGradient (onlineLocalProblem P) i x0‖ ^ 2 := by
      dsimp [workerResidual, target]
      rw [hcenter]
    constructor
    · apply h.1.congr
      exact Filter.Eventually.of_forall (fun batch => (hsquare batch).symm)
    · calc
        (∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) =
            ∫ batch,
              ‖average (fun j : Fin b.1 => stochasticGradient P i (batch i j) x0) -
                localGradient (onlineLocalProblem P) i x0‖ ^ 2 ∂μ := by
          exact integral_congr_ae (Filter.Eventually.of_forall hsquare)
        _ ≤ (σ i) ^ 2 / b.1 := by
          simpa [μ, P, heterogeneousOnlineBatchLaw, onlineBatchLaw] using h.2
  have hworker_int (i : Worker n) : Integrable (workerResidual i) μ := by
    have hmeas : AEStronglyMeasurable (workerResidual i) μ := by
      have hrow_map : Integrable (rowResidual i)
          (Measure.map
            (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i) μ) := by
        rw [hcoord i]
        exact hrowResidual_int i
      exact ((MeasureTheory.integrable_map_measure
        hrow_map.aestronglyMeasurable
        (measurable_pi_apply i).aemeasurable).mp hrow_map).aestronglyMeasurable
    exact integrable_of_integrable_norm_sq hmeas (hdiag i).1
  have hiIndep :
      ProbabilityTheory.iIndepFun
        (fun i (batch : (i : Worker n) → Fin b.1 → Sample i) => batch i) μ := by
    dsimp [μ, onlineBatchLaw]
    exact ProbabilityTheory.iIndepFun_infinitePi
      (fun _ : Worker n => measurable_id)
  have hcross (i j : Worker n) (hij : i ≠ j) :
      (∫ batch, ⟪workerResidual i batch, workerResidual j batch⟫_ℝ ∂μ) = 0 := by
    have hkernel :
        AEStronglyMeasurable
          (fun p : (Fin b.1 → Sample i) × (Fin b.1 → Sample j) =>
            ⟪rowResidual i p.1, rowResidual j p.2⟫_ℝ)
          ((Measure.map
            (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i) μ).prod
            (rowLaw j)) := by
      rw [hcoord i]
      exact (hrowResidual_int i).aestronglyMeasurable.comp_fst.inner
        (hrowResidual_int j).aestronglyMeasurable.comp_snd
    have hinner : Integrable
        (fun batch => ⟪workerResidual i batch, workerResidual j batch⟫_ℝ) μ :=
      integrable_inner_of_integrable_sq_norm
        (hworker_int i).aestronglyMeasurable
        (hworker_int j).aestronglyMeasurable (hdiag i).1 (hdiag j).1
    have hfixed : ∀ a : Fin b.1 → Sample i,
        (∫ z, ⟪rowResidual i a, rowResidual j z⟫_ℝ ∂rowLaw j) = 0 := by
      intro a
      have hlin := ContinuousLinearMap.integral_comp_comm
        (L := (innerSL ℝ) (rowResidual i a)) (hrowResidual_int j)
      exact hlin.trans (by rw [hrowResidual_mean j]; simp)
    exact
      integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
        (P := μ) (ν := rowLaw j)
        (φ := fun a z => ⟪rowResidual i a, rowResidual j z⟫_ℝ)
        (X := fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i)
        (Y := fun batch : (i : Worker n) → Fin b.1 → Sample i => batch j)
        hkernel (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable (hiIndep.indepFun hij)
        (hcoord j) hinner hfixed
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    μ (Finset.univ : Finset (Worker n)) workerResidual
    (fun i _ => (hworker_int i).aestronglyMeasurable)
    (fun i _ => (hdiag i).1)
    (fun i _ j _ hij => hcross i j hij)
  have hglobal := globalGradient_eq_averageLocalGradient
    (onlineLocalProblem P) hDiff x0
  have hpointwise
      (batch : (i : Worker n) → Fin b.1 → Sample i) :
      onlineInitialEstimatorErrorSq A x0 { sample := batch } =
        ‖((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n => workerResidual i batch)‖ ^ 2 := by
    unfold onlineInitialEstimatorErrorSq onlineInitialState
      onlinePrintedInitialEstimatorAt
    rw [hglobal]
    apply congrArg (fun v : Point d => ‖v‖ ^ 2)
    unfold averageLocalGradient
    change
      average (fun i : Worker n =>
          average (fun j : Fin b.1 => stochasticGradient P i (batch i j) x0)) -
        average (fun i : Worker n => localGradient (onlineLocalProblem P) i x0) =
      ((n.1 : ℝ)⁻¹) •
        Finset.sum Finset.univ (fun i : Worker n => workerResidual i batch)
    calc
      _ = average (fun i : Worker n =>
          average (fun j : Fin b.1 => stochasticGradient P i (batch i j) x0) -
            localGradient (onlineLocalProblem P) i x0) := by
        unfold average SOptLib.finiteUniformAverage
        rw [Finset.sum_sub_distrib, smul_sub]
      _ = average (fun i : Worker n => workerResidual i batch) := by
        apply congrArg average
        funext i
        dsimp [workerResidual, target, P]
        exact hcenter i (batch i)
      _ = ((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n => workerResidual i batch) := by
        simp [average, SOptLib.finiteUniformAverage]
  rw [show expectedOnlineInitialEstimatorErrorSq (b := b) A x0 =
      ∫ batch, onlineInitialEstimatorErrorSq A x0 { sample := batch } ∂μ by
        rfl]
  calc
    (∫ batch, onlineInitialEstimatorErrorSq A x0 { sample := batch } ∂μ) =
        ∫ batch, ‖((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n => workerResidual i batch)‖ ^ 2 ∂μ := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        ∫ batch, ‖Finset.sum Finset.univ
          (fun i : Worker n => workerResidual i batch)‖ ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro batch
      change ‖((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n => workerResidual i batch)‖ ^ 2 =
        ((n.1 : ℝ)⁻¹) ^ 2 *
          ‖Finset.sum Finset.univ (fun i : Worker n => workerResidual i batch)‖ ^ 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        Finset.sum Finset.univ
          (fun i : Worker n => ∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) := by
      rw [hsum]
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        Finset.sum Finset.univ (fun i : Worker n => (σ i) ^ 2 / b.1) := by
      gcongr with i
      exact (hdiag i).2
    _ = varianceAggregateSq σ / (n.1 * b.1) := by
      unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
      have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
      have hb : (b.1 : ℝ) ≠ 0 := by exact_mod_cast b.2.ne'
      simp only [Fintype.card_fin]
      simp only [smul_eq_mul]
      field_simp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      field_simp [hb]

set_option maxHeartbeats 1600000 in
/-- Fixed-query form of the complete locally centered Algorithm 3 refresh
average.  This packages both the nonfallback `L²` fact and the exact
`σ²/(n b)` coefficient before the query is transported to a generated
iterate. -/
theorem online_fixed_refresh_average_second_moment
    {d n b : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x : Point d)
    (σ : Worker n → ℝ) (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ ((onlineLocalProblem A.problem).localLoss i)) :
    Integrable (fun batch =>
        ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (batch i j) x)) -
          globalGradient (onlineLocalProblem A.problem) x‖ ^ 2)
        (onlineBatchLaw A.problem b) ∧
      (∫ batch,
        ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
            stochasticGradient A.problem i (batch i j) x)) -
          globalGradient (onlineLocalProblem A.problem) x‖ ^ 2
        ∂onlineBatchLaw A.problem b) ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  let P := A.problem
  let μ := onlineBatchLaw P b
  let workerResidual := fun (i : Worker n)
      (batch : (i : Worker n) → Fin b.1 → Sample i) =>
    average (fun j : Fin b.1 => stochasticGradient P i (batch i j) x) -
      localGradient (onlineLocalProblem P) i x
  letI (i : Worker n) : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, onlineBatchLaw]
    infer_instance
  have hcoord (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j) μ =
        P.sampleLaw i := by
    simpa [μ] using onlineBatchLaw_coordinate_marginal P i j
  have hgrad (i : Worker n) (j : Fin b.1) :
      Integrable (fun batch : (i : Worker n) → Fin b.1 → Sample i =>
        stochasticGradient P i (batch i j) x) μ := by
    have hm : Integrable (fun xi => stochasticGradient P i xi x)
        (Measure.map
          (fun batch : (i : Worker n) → Fin b.1 → Sample i => batch i j) μ) := by
      rw [hcoord i j]
      exact (hVariance.1.2 i x).1
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable)).mp hm
  have hworker_meas (i : Worker n) :
      AEStronglyMeasurable (workerResidual i) μ := by
    dsimp [workerResidual]
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ => (hgrad i j).aestronglyMeasurable)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine (hs.sub (aestronglyMeasurable_const : AEStronglyMeasurable
      (fun _ : ((i : Worker n) → Fin b.1 → Sample i) =>
        localGradient (onlineLocalProblem P) i x) μ)).congr ?_
    exact Filter.Eventually.of_forall (fun batch => by
      simp [Pi.smul_apply, Finset.sum_apply])
  have hworker_sq (i : Worker n) :
      Integrable (fun batch => ‖workerResidual i batch‖ ^ 2) μ := by
    have h := heterogeneousOnline_refresh_secondMoment_le
      P σ (fun _ : Worker n => b) hVariance i x
    simpa [workerResidual, μ, heterogeneousOnlineBatchLaw] using h.1
  have havg : Integrable
      (fun batch => ‖average (fun i : Worker n => workerResidual i batch)‖ ^ 2) μ := by
    apply integrable_sq_norm_centeredMiniBatchAverage μ Finset.univ n.1
      (fun i batch => workerResidual i batch)
      (fun batch => average (fun i : Worker n => workerResidual i batch))
    · intro i _
      exact hworker_meas i
    · intro i _
      exact hworker_sq i
    · funext batch
      simp [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
  have hglobal := globalGradient_eq_averageLocalGradient
    (onlineLocalProblem P) hDiff x
  have hpointwise (batch : (i : Worker n) → Fin b.1 → Sample i) :
      ‖average (fun i : Worker n => average (fun j : Fin b.1 =>
          stochasticGradient P i (batch i j) x)) -
        globalGradient (onlineLocalProblem P) x‖ ^ 2 =
      ‖average (fun i : Worker n => workerResidual i batch)‖ ^ 2 := by
    apply congrArg (fun v : Point d => ‖v‖ ^ 2)
    rw [hglobal]
    unfold averageLocalGradient
    dsimp [workerResidual]
    unfold average SOptLib.finiteUniformAverage
    rw [Finset.sum_sub_distrib, smul_sub]
  constructor
  · apply havg.congr
    exact Filter.Eventually.of_forall (fun batch => (hpointwise batch).symm)
  · simpa [expectedOnlineInitialEstimatorErrorSq, onlineInitialEstimatorErrorSq,
      onlineInitialState, onlinePrintedInitialEstimatorAt, P, μ] using
      (expectedOnlineInitialEstimatorErrorSq_le (b := b) A x σ hVariance hDiff)

/-! The following concrete model records why the preceding differentiability
premise is necessary.  It instantiates the former premise-free theorem head,
not a weaker auxiliary gradient identity. -/

abbrev oldInitialBoundCounterexampleDimension : Count :=
  ⟨1, by omega⟩

abbrev oldInitialBoundCounterexampleWorkers : Count :=
  ⟨2, by omega⟩

abbrev oldInitialBoundCounterexampleBatch : Count :=
  ⟨1, by omega⟩

abbrev OldInitialBoundCounterexampleSample
    (_ : Worker oldInitialBoundCounterexampleWorkers) := Unit

noncomputable def oldInitialBoundCounterexampleDirection :
    Point oldInitialBoundCounterexampleDimension :=
  EuclideanSpace.single 0 1

noncomputable def oldInitialBoundCounterexampleProblem :
    OnlineProblem oldInitialBoundCounterexampleDimension
      oldInitialBoundCounterexampleWorkers OldInitialBoundCounterexampleSample where
  sampleLoss i _ x :=
    if (i : ℕ) = 0 then ‖x‖
    else ⟪oldInitialBoundCounterexampleDirection, x⟫_ℝ - ‖x‖
  sampleLaw _ := Measure.dirac ()
  sampleLaw_isProbability _ := by infer_instance
  sampleLoss_integrable i x := by simp

noncomputable def oldInitialBoundCounterexampleQuantizer :
    Quantizer oldInitialBoundCounterexampleDimension Unit where
  apply :=
    { toFun := fun _ _ => 0
      measurable_uncurry := measurable_const }
  law := Measure.dirac ()
  law_isProbability := by infer_instance

noncomputable def oldInitialBoundCounterexampleData :
    OnlineData oldInitialBoundCounterexampleDimension
      oldInitialBoundCounterexampleWorkers OldInitialBoundCounterexampleSample Unit where
  problem := oldInitialBoundCounterexampleProblem
  quantizer := oldInitialBoundCounterexampleQuantizer
  stepSize := ⟨1, by norm_num⟩
  refreshProbability := 1
  refresh_admissible := by constructor <;> norm_num

/-- The former version of `expectedOnlineInitialEstimatorErrorSq_le`, which
assumed only `LegacyOnlineFixedQueryUnbiasedBoundedVariance`, is false.  This is the Planner's
two-worker deterministic countermodel: the two local losses are `‖x‖` and
`⟦e,x⟧-‖x‖` at the origin.  Their totalized gradients vanish separately,
whereas their average is the differentiable function `⟦e,x⟧/2`. -/
theorem expectedOnlineInitialEstimatorErrorSq_le_without_differentiability_false :
    let d : Count := ⟨1, by omega⟩
    let n : Count := ⟨2, by omega⟩
    let b : Count := ⟨1, by omega⟩
    let Sample : Worker n → Type := fun _ => Unit
    ∃ (A : OnlineData d n Sample Unit) (x0 : Point d) (σ : Worker n → ℝ),
      LegacyOnlineFixedQueryUnbiasedBoundedVariance A.problem σ ∧
        ¬ expectedOnlineInitialEstimatorErrorSq (b := b) A x0 ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
  dsimp only
  refine ⟨oldInitialBoundCounterexampleData, 0, fun _ => 0, ?_, ?_⟩
  · change LegacyOnlineFixedQueryUnbiasedBoundedVariance
      oldInitialBoundCounterexampleProblem (fun _ => 0)
    constructor
    · intro i
      exact le_rfl
    · intro i x
      have hsame (xi : Unit) :
          stochasticGradient oldInitialBoundCounterexampleProblem i xi x =
            localGradient
              (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x := by
        rcases xi with ⟨⟩
        simp [stochasticGradient, localGradient, onlineLocalProblem,
          expectedSampleLoss, oldInitialBoundCounterexampleProblem]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change Integrable
          (fun xi : Unit =>
            stochasticGradient oldInitialBoundCounterexampleProblem i xi x)
          (Measure.dirac ())
        exact integrable_dirac (by simp)
      · change Integrable
          (fun xi : Unit =>
            ‖stochasticGradient oldInitialBoundCounterexampleProblem i xi x -
              localGradient
                (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x‖ ^ 2)
          (Measure.dirac ())
        exact integrable_dirac (by simp)
      · change
          (∫ xi : Unit,
            stochasticGradient oldInitialBoundCounterexampleProblem i xi x
              ∂Measure.dirac ()) =
            localGradient
              (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x
        rw [integral_dirac]
        exact hsame ()
      · change
          (∫ xi : Unit,
            ‖stochasticGradient oldInitialBoundCounterexampleProblem i xi x -
              localGradient
                (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x‖ ^ 2
              ∂Measure.dirac ()) ≤ 0 ^ 2
        rw [integral_dirac, hsame]
        simp
  · let e := oldInitialBoundCounterexampleDirection
    have hlocal_zero (i : Worker oldInitialBoundCounterexampleWorkers) :
        localGradient
          (onlineLocalProblem oldInitialBoundCounterexampleProblem) i 0 = 0 := by
      fin_cases i
      · unfold localGradient
        apply gradient_eq_zero_of_not_differentiableAt
        simpa [onlineLocalProblem, expectedSampleLoss,
          oldInitialBoundCounterexampleProblem] using
            (not_differentiableAt_norm_zero
              (Point oldInitialBoundCounterexampleDimension))
      · unfold localGradient
        apply gradient_eq_zero_of_not_differentiableAt
        intro hbad
        have hlinear : DifferentiableAt ℝ
            (fun x : Point oldInitialBoundCounterexampleDimension =>
              ⟪e, x⟫_ℝ) 0 :=
          (innerSL ℝ e).hasFDerivAt.differentiableAt
        have hnorm : DifferentiableAt ℝ
            (fun x : Point oldInitialBoundCounterexampleDimension => ‖x‖) 0 := by
          have hsub := hlinear.sub hbad
          have hfun :
              (fun x : Point oldInitialBoundCounterexampleDimension => ‖x‖) =
                (fun x => ⟪e, x⟫_ℝ) -
                  (fun x => ⟪e, x⟫_ℝ - ‖x‖) := by
            funext y
            simp
          rw [hfun]
          simpa [e, onlineLocalProblem, expectedSampleLoss,
            oldInitialBoundCounterexampleProblem] using hsub
        exact (not_differentiableAt_norm_zero
          (Point oldInitialBoundCounterexampleDimension)) hnorm
    have hstochastic_zero
        (i : Worker oldInitialBoundCounterexampleWorkers) (xi : Unit) :
        stochasticGradient oldInitialBoundCounterexampleProblem i xi 0 = 0 := by
      rcases xi with ⟨⟩
      simpa [stochasticGradient, localGradient, onlineLocalProblem,
        expectedSampleLoss, oldInitialBoundCounterexampleProblem] using
          hlocal_zero i
    have hobjective :
        globalObjective
            (onlineLocalProblem oldInitialBoundCounterexampleProblem) =
          (fun x : Point oldInitialBoundCounterexampleDimension =>
            (2 : ℝ)⁻¹ * ⟪e, x⟫_ℝ) := by
      funext x
      simp [globalObjective, average, SOptLib.finiteUniformAverage, e,
        onlineLocalProblem, expectedSampleLoss,
        oldInitialBoundCounterexampleProblem]
      change (2 : ℝ)⁻¹ *
          (∑ i : Fin 2, if (i : ℕ) = 0 then ‖x‖
            else ⟪oldInitialBoundCounterexampleDirection, x⟫_ℝ - ‖x‖) =
        (2 : ℝ)⁻¹ * ⟪oldInitialBoundCounterexampleDirection, x⟫_ℝ
      rw [Fin.sum_univ_two]
      simp
    have hlinearGradient : HasGradientAt
        (fun x : Point oldInitialBoundCounterexampleDimension =>
          (2 : ℝ)⁻¹ * ⟪e, x⟫_ℝ)
        ((2 : ℝ)⁻¹ • e) 0 := by
      rw [hasGradientAt_iff_hasFDerivAt]
      simpa [map_smul] using
        ((innerSL ℝ e).hasFDerivAt.const_mul ((2 : ℝ)⁻¹))
    have hglobal :
        globalGradient
            (onlineLocalProblem oldInitialBoundCounterexampleProblem) 0 =
          (2 : ℝ)⁻¹ • e := by
      unfold globalGradient
      rw [hobjective]
      exact hlinearGradient.gradient
    have herror
        (batch : (i : Worker oldInitialBoundCounterexampleWorkers) →
          Fin oldInitialBoundCounterexampleBatch.1 →
            OldInitialBoundCounterexampleSample i) :
        onlineInitialEstimatorErrorSq oldInitialBoundCounterexampleData 0
            { sample := batch } =
          ‖(2 : ℝ)⁻¹ • e‖ ^ 2 := by
      unfold onlineInitialEstimatorErrorSq onlineInitialState
        onlinePrintedInitialEstimatorAt
      dsimp [oldInitialBoundCounterexampleData]
      rw [hglobal]
      simp_rw [hstochastic_zero]
      simp [average, SOptLib.finiteUniformAverage]
    letI (i : Worker oldInitialBoundCounterexampleWorkers) :
        IsProbabilityMeasure
          (oldInitialBoundCounterexampleProblem.sampleLaw i) := by
      exact oldInitialBoundCounterexampleProblem.sampleLaw_isProbability i
    haveI : IsProbabilityMeasure
        (onlineBatchLaw oldInitialBoundCounterexampleProblem
          oldInitialBoundCounterexampleBatch) := by
      unfold onlineBatchLaw
      infer_instance
    have hexpected :
        expectedOnlineInitialEstimatorErrorSq
            (b := oldInitialBoundCounterexampleBatch)
              oldInitialBoundCounterexampleData 0 =
          ‖(2 : ℝ)⁻¹ • e‖ ^ 2 := by
      unfold expectedOnlineInitialEstimatorErrorSq
      calc
        (∫ z, onlineInitialEstimatorErrorSq
              oldInitialBoundCounterexampleData 0 { sample := z }
            ∂onlineBatchLaw oldInitialBoundCounterexampleProblem
              oldInitialBoundCounterexampleBatch) =
            ∫ _z, ‖(2 : ℝ)⁻¹ • e‖ ^ 2
              ∂onlineBatchLaw oldInitialBoundCounterexampleProblem
                oldInitialBoundCounterexampleBatch := by
          exact integral_congr_ae (Filter.Eventually.of_forall herror)
        _ = ‖(2 : ℝ)⁻¹ • e‖ ^ 2 := by simp
    have he_ne : e ≠ 0 := by
      intro he
      have hcoordinate := congrArg
        (fun v : Point oldInitialBoundCounterexampleDimension => v 0) he
      simpa [e, oldInitialBoundCounterexampleDirection] using hcoordinate
    have hscaled_ne : (2 : ℝ)⁻¹ • e ≠ 0 :=
      smul_ne_zero (by norm_num) he_ne
    have hvalue : ‖(2 : ℝ)⁻¹ • e‖ ^ 2 = (1 : ℝ) / 4 := by
      rw [norm_smul]
      simp [e, oldInitialBoundCounterexampleDirection]
      norm_num
    have hpositive : 0 < ‖(2 : ℝ)⁻¹ • e‖ ^ 2 := by
      rw [hvalue]
      norm_num
    intro hle
    have hnonpos :
        expectedOnlineInitialEstimatorErrorSq
            (b := oldInitialBoundCounterexampleBatch)
              oldInitialBoundCounterexampleData 0 ≤ 0 := by
      simpa [varianceAggregateSq, meanSquare, average,
        SOptLib.finiteUniformAverage] using hle
    rw [hexpected] at hnonpos
    exact (not_lt_of_ge hnonpos) hpositive

/-- The literal fixed-query moment content of Assumption 3.3 does not imply
law-a.e. differentiability of the sampled losses.  In this deterministic
two-worker model each sample gradient is definitionally the corresponding
local gradient, so the variance is zero, while the first sampled loss is the
Euclidean norm and is not differentiable at the origin.

This is a countermodel to the proposed literal-to-corrected premise transfer,
not a counterexample to Eq. (46): it identifies why the finite-difference
regularity route cannot be silently supplied from
`LegacyOnlineFixedQueryUnbiasedBoundedVariance`.
-/
theorem onlineSampleLossDifferentiable_not_derivable_from_literal_variance :
    ∃ (P : OnlineProblem oldInitialBoundCounterexampleDimension
        oldInitialBoundCounterexampleWorkers OldInitialBoundCounterexampleSample)
      (sigma : Worker oldInitialBoundCounterexampleWorkers → ℝ),
      LegacyOnlineFixedQueryUnbiasedBoundedVariance P sigma ∧
        (∀ {b0 : Count} {Omega : Type} [MeasurableSpace Omega]
          (run : ℕ → Omega → State oldInitialBoundCounterexampleDimension),
          OnlineAverageSmoothness (b0 := b0) P run (fun _ ↦ 0)) ∧
        ¬ OnlineSampleLossDifferentiable P := by
  refine ⟨oldInitialBoundCounterexampleProblem, fun _ ↦ 0, ?_, ?_, ?_⟩
  · constructor
    · intro i
      exact le_rfl
    · intro i x
      have hsame (xi : Unit) :
          stochasticGradient oldInitialBoundCounterexampleProblem i xi x =
            localGradient
              (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x := by
        rcases xi with ⟨⟩
        simp [stochasticGradient, localGradient, onlineLocalProblem,
          expectedSampleLoss, oldInitialBoundCounterexampleProblem]
      refine ⟨?_, ?_, ?_, ?_⟩
      · change Integrable
          (fun xi : Unit ↦
            stochasticGradient oldInitialBoundCounterexampleProblem i xi x)
          (Measure.dirac ())
        exact integrable_dirac (by simp)
      · change Integrable
          (fun xi : Unit ↦
            ‖stochasticGradient oldInitialBoundCounterexampleProblem i xi x -
              localGradient
                (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x‖ ^ 2)
          (Measure.dirac ())
        exact integrable_dirac (by simp)
      · change
          (∫ xi : Unit,
            stochasticGradient oldInitialBoundCounterexampleProblem i xi x
              ∂Measure.dirac ()) =
            localGradient
              (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x
        rw [integral_dirac]
        exact hsame ()
      · change
          (∫ xi : Unit,
            ‖stochasticGradient oldInitialBoundCounterexampleProblem i xi x -
              localGradient
                (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x‖ ^ 2
              ∂Measure.dirac ()) ≤ 0 ^ 2
        rw [integral_dirac, hsame]
        simp
  · intro b0 Omega _ run
    letI : Nonempty (Fin b0.1) := ⟨⟨0, b0.2⟩⟩
    letI (w : Worker oldInitialBoundCounterexampleWorkers) :
        IsProbabilityMeasure
          (oldInitialBoundCounterexampleProblem.sampleLaw w) :=
      oldInitialBoundCounterexampleProblem.sampleLaw_isProbability w
    haveI : IsProbabilityMeasure
        (onlineBatchLaw oldInitialBoundCounterexampleProblem b0) := by
      unfold onlineBatchLaw
      infer_instance
    constructor
    · intro i
      exact le_rfl
    · intro k i path
      dsimp
      have hsame (xi : Unit) (x : Point oldInitialBoundCounterexampleDimension) :
          stochasticGradient oldInitialBoundCounterexampleProblem i xi x =
            localGradient
              (onlineLocalProblem oldInitialBoundCounterexampleProblem) i x := by
        rcases xi with ⟨⟩
        simp [stochasticGradient, localGradient, onlineLocalProblem,
          expectedSampleLoss, oldInitialBoundCounterexampleProblem]
      have hbatch
          (batch : (w : Worker oldInitialBoundCounterexampleWorkers) →
            Fin b0.1 → OldInitialBoundCounterexampleSample w) :
          onlineBatchDifference oldInitialBoundCounterexampleProblem batch i
              (run (k + 1) path).x (run k path).x =
            localGradientDifference
              (onlineLocalProblem oldInitialBoundCounterexampleProblem) i
              (run (k + 1) path).x (run k path).x := by
        unfold onlineBatchDifference localGradientDifference average
        simp_rw [hsame]
        exact SOptLib.finiteUniformAverage_const _
      simp_rw [hbatch]
      simp
  · intro hDiff
    have hnorm : Differentiable ℝ
        (oldInitialBoundCounterexampleProblem.sampleLoss 0 ()) := by
      have hae := hDiff 0
      simpa [oldInitialBoundCounterexampleProblem] using hae
    exact (not_differentiableAt_norm_zero
      (Point oldInitialBoundCounterexampleDimension)) (hnorm 0)

/-- Consequently there is no assumption-free adapter from the literal
Assumption 3.3 predicate to the corrected finite-difference boundary.  This is
the exact failed edge between the unqualified Eq. (46) theorem and the proved
all-iteration corrected regularity chain. -/
theorem onlineLiteralVariance_to_corrected_not_derivable :
    ¬ (∀
        (P : OnlineProblem oldInitialBoundCounterexampleDimension
          oldInitialBoundCounterexampleWorkers OldInitialBoundCounterexampleSample)
        (σ : Worker oldInitialBoundCounterexampleWorkers → ℝ),
        LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ →
          OnlineUnbiasedBoundedVarianceCorrected
            ⟨P, onlineExpectationRealization P⟩ σ) := by
  intro htransfer
  rcases onlineSampleLossDifferentiable_not_derivable_from_literal_variance with
    ⟨P, σ, hVariance, _hAverageSmooth, hnotDiff⟩
  exact hnotDiff
    (onlineSampleLossDifferentiable_of_varianceCorrected
      ⟨P, onlineExpectationRealization P⟩ σ (htransfer P σ hVariance))

/-! ### An atomless separately measurable diagonal obstruction

The deterministic countermodel above refutes the differentiability adapter,
but its law cannot refute the adaptive product-law boundary.  The following
countable--cocountable coordinate isolates the genuinely law-scoped
obstruction.  Every singleton is measurable and null, while the diagonal
against an atomless standard-Borel query law is not even measurable modulo
the product measure.  Pairing this coordinate with any atomless probability
coordinate gives the non-null atomless sample law required by a theorem-level
Algorithm 3 countermodel.
-/

/-- A copy of `ℝ` carrying the countable--cocountable sigma algebra. -/
structure OnlineCoarseReal where
  val : ℝ

instance : MeasurableSpace OnlineCoarseReal where
  MeasurableSet' s := s.Countable ∨ sᶜ.Countable
  measurableSet_empty := Or.inl Set.countable_empty
  measurableSet_compl := by
    intro s hs
    rcases hs with hs | hs
    · exact Or.inr (by simpa using hs)
    · exact Or.inl hs
  measurableSet_iUnion := by
    intro f hf
    by_cases hco : ∃ i, (f i)ᶜ.Countable
    · rcases hco with ⟨i, hi⟩
      exact Or.inr (hi.mono (by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hx ⊢
        exact hx i))
    · left
      exact Set.countable_iUnion (fun i => by
        rcases hf i with hi | hi
        · exact hi
        · exact False.elim (hco ⟨i, hi⟩))

theorem onlineCoarseReal_measurableSet_iff (s : Set OnlineCoarseReal) :
    MeasurableSet s ↔ s.Countable ∨ sᶜ.Countable := by
  rfl

def onlineCoarseWrap (x : ℝ) : OnlineCoarseReal := ⟨x⟩

theorem onlineCoarseWrap_injective : Function.Injective onlineCoarseWrap := by
  intro x y h
  exact congrArg OnlineCoarseReal.val h

theorem onlineCoarseWrap_measurable : Measurable onlineCoarseWrap := by
  intro s hs
  rw [onlineCoarseReal_measurableSet_iff] at hs
  rcases hs with hs | hs
  · exact (hs.preimage onlineCoarseWrap_injective).measurableSet
  · apply MeasurableSet.compl_iff.mp
    simpa only [Set.preimage_compl] using
      (hs.preimage onlineCoarseWrap_injective).measurableSet

/-- The countable--cocountable probability law, realized as the pushforward
of a non-atomic Cauchy probability. -/
noncomputable def onlineCoarseLaw : Measure OnlineCoarseReal :=
  Measure.map onlineCoarseWrap (ProbabilityTheory.cauchyMeasure 0 1)

theorem onlineCauchy_one_noAtoms :
    NoAtoms (ProbabilityTheory.cauchyMeasure 0 1) := by
  have hscale : (1 : NNReal) ≠ 0 := by norm_num
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero (0 : ℝ)
    (γ := (1 : NNReal)) hscale]
  infer_instance

instance : IsProbabilityMeasure onlineCoarseLaw := by
  constructor
  unfold onlineCoarseLaw
  rw [Measure.map_apply onlineCoarseWrap_measurable MeasurableSet.univ]
  simp

theorem onlineCoarseLaw_apply_countable
    (s : Set OnlineCoarseReal) (hs : s.Countable) :
    onlineCoarseLaw s = 0 := by
  letI : NoAtoms (ProbabilityTheory.cauchyMeasure 0 1) :=
    onlineCauchy_one_noAtoms
  rw [onlineCoarseLaw, Measure.map_apply onlineCoarseWrap_measurable
    (onlineCoarseReal_measurableSet_iff s |>.2 (Or.inl hs))]
  exact (hs.preimage onlineCoarseWrap_injective).measure_zero _

instance : NoAtoms onlineCoarseLaw where
  measure_singleton x :=
    onlineCoarseLaw_apply_countable {x} (Set.countable_singleton x)

theorem onlineCoarseLaw_apply_cocountable
    (s : Set OnlineCoarseReal) (hs : sᶜ.Countable) :
    onlineCoarseLaw s = 1 := by
  have hsm : MeasurableSet s :=
    onlineCoarseReal_measurableSet_iff s |>.2 (Or.inr hs)
  have hcompl := measure_compl (μ := onlineCoarseLaw)
    hsm.compl (measure_ne_top _ _)
  simpa [onlineCoarseLaw_apply_countable sᶜ hs] using hcompl

/-- Every product-measurable set on the coarse coordinate and an arbitrary
second coordinate has eventually constant second-coordinate sections. -/
theorem onlineCoarse_product_sections_eventually_constant
    {Q : Type*} [MeasurableSpace Q] (s : Set (OnlineCoarseReal × Q))
    (hs : MeasurableSet s) :
    ∃ C : Set OnlineCoarseReal, C.Countable ∧
      ∀ a ∉ C, ∀ b ∉ C,
        Prod.mk a ⁻¹' s = Prod.mk b ⁻¹' s := by
  induction s, hs using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
  | empty =>
      exact ⟨∅, Set.countable_empty, by simp⟩
  | basic s hs =>
      rcases hs with ⟨u, hu, v, hv, rfl⟩
      change MeasurableSet u at hu
      rw [onlineCoarseReal_measurableSet_iff] at hu
      rcases hu with hu | hu
      · refine ⟨u, hu, ?_⟩
        intro a ha b hb
        ext q
        simp [ha, hb]
      · refine ⟨uᶜ, hu, ?_⟩
        intro a ha b hb
        ext q
        simp only [Set.mem_compl_iff, not_not] at ha hb
        simp [ha, hb]
  | compl s hs hconst =>
      rcases hconst with ⟨C, hC, hsections⟩
      refine ⟨C, hC, ?_⟩
      intro a ha b hb
      simpa only [Set.preimage_compl] using congrArg Set.compl (hsections a ha b hb)
  | iUnion f hdisj hfm hconst =>
      choose C hC hsections using hconst
      refine ⟨⋃ i, C i, Set.countable_iUnion hC, ?_⟩
      intro a ha b hb
      have ha' : ∀ i, a ∉ C i := by
        intro i hai
        exact ha (Set.mem_iUnion.2 ⟨i, hai⟩)
      have hb' : ∀ i, b ∉ C i := by
        intro i hbi
        exact hb (Set.mem_iUnion.2 ⟨i, hbi⟩)
      ext q
      simp only [Set.mem_preimage, Set.mem_iUnion]
      constructor <;> rintro ⟨i, hi⟩
      · exact ⟨i, by
          have := Set.ext_iff.mp (hsections i a (ha' i) b (hb' i)) q
          exact this.mp hi⟩
      · exact ⟨i, by
          have := Set.ext_iff.mp (hsections i a (ha' i) b (hb' i)) q
          exact this.mpr hi⟩

def onlineCoarseDiagonal (Q : Type*) [Coe Q ℝ] :
    Set (OnlineCoarseReal × Q) :=
  {p | p.1.val = (p.2 : ℝ)}

/-- The equality diagonal between the countable--cocountable coordinate and
an atomless real query law is not measurable even after completion.  This is
the exact product-law pathology that deterministic and countable sample laws
cannot exhibit. -/
theorem onlineCoarseDiagonal_not_nullMeasurable
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    ¬ NullMeasurableSet
      ({p : OnlineCoarseReal × ℝ | p.1.val = p.2})
      (onlineCoarseLaw.prod ν) := by
  let D : Set (OnlineCoarseReal × ℝ) :=
    {p | p.1.val = p.2}
  have hsuperset (s : Set (OnlineCoarseReal × ℝ))
      (hs : MeasurableSet s) (hDs : D ⊆ s) :
      onlineCoarseLaw.prod ν s = 1 := by
    rcases onlineCoarse_product_sections_eventually_constant s hs with
      ⟨C, hC, hsections⟩
    have hsection_one : ∀ a ∉ C, ν (Prod.mk a ⁻¹' s) = 1 := by
      intro a ha
      have hcontains : {x : ℝ | onlineCoarseWrap x ∉ C} ⊆
          Prod.mk a ⁻¹' s := by
        intro x hx
        have hdiag : (onlineCoarseWrap x, x) ∈ D := by
          simp [D, onlineCoarseWrap]
        have hmem : (onlineCoarseWrap x, x) ∈ s := hDs hdiag
        have heq := Set.ext_iff.mp
          (hsections (onlineCoarseWrap x) hx a ha) x
        exact heq.mp hmem
      have hcompl_countable :
          ({x : ℝ | onlineCoarseWrap x ∉ C} : Set ℝ)ᶜ.Countable := by
        have hpre : (onlineCoarseWrap ⁻¹' C).Countable :=
          hC.preimage onlineCoarseWrap_injective
        simpa only [Set.compl_setOf, not_not] using hpre
      have hbase : ν {x : ℝ | onlineCoarseWrap x ∉ C} = 1 := by
        have hmcompl : MeasurableSet
            ({x : ℝ | onlineCoarseWrap x ∉ C} : Set ℝ)ᶜ :=
          hcompl_countable.measurableSet
        have hcompl := measure_compl (μ := ν) hmcompl (measure_ne_top _ _)
        simpa [hcompl_countable.measure_zero ν] using hcompl
      have hlower : ν {x : ℝ | onlineCoarseWrap x ∉ C} ≤
          ν (Prod.mk a ⁻¹' s) := measure_mono hcontains
      rw [hbase] at hlower
      exact le_antisymm prob_le_one hlower
    rw [MeasureTheory.Measure.prod_apply hs]
    have hnotC : ∀ᵐ a ∂onlineCoarseLaw, a ∉ C := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using
        onlineCoarseLaw_apply_countable C hC
    have hae : (fun a => ν (Prod.mk a ⁻¹' s)) =ᵐ[onlineCoarseLaw]
        (fun _ => 1) := hnotC.mono fun a ha => hsection_one a ha
    rw [lintegral_congr_ae hae]
    simp
  have hD_one : onlineCoarseLaw.prod ν D = 1 := by
    rcases exists_measurable_superset (onlineCoarseLaw.prod ν) D with
      ⟨s, hDs, hs, hmeasure⟩
    rw [← hmeasure]
    exact hsuperset s hs hDs
  intro hnull
  rcases hnull.exists_measurable_subset_ae_eq with ⟨t, htD, ht, hteq⟩
  have ht_zero : onlineCoarseLaw.prod ν t = 0 := by
    rcases onlineCoarse_product_sections_eventually_constant t ht with
      ⟨C, hC, hsections⟩
    have hsection_zero : ∀ a ∉ C, ν (Prod.mk a ⁻¹' t) = 0 := by
      intro a ha
      obtain ⟨b, hbC, hba⟩ : ∃ b : OnlineCoarseReal, b ∉ C ∧ b ≠ a := by
        by_contra h
        push Not at h
        have hsub : Set.univ ⊆ insert a C := by
          intro b _
          by_cases hb : b ∈ C
          · exact Set.mem_insert_iff.mpr (Or.inr hb)
          · exact Set.mem_insert_iff.mpr (Or.inl (h b hb))
        have huniv : (Set.univ : Set OnlineCoarseReal).Countable :=
          (hC.insert a).mono hsub
        haveI : Countable OnlineCoarseReal := Set.countable_univ_iff.mp huniv
        haveI : Countable ℝ := onlineCoarseWrap_injective.countable
        exact Cardinal.not_countable_real
          (Set.countable_univ_iff.mpr inferInstance)
      have hsubempty : Prod.mk a ⁻¹' t ⊆ (∅ : Set ℝ) := by
        intro x hx
        have hxa : x = a.val := by
          have := htD hx
          simpa [D] using this.symm
        have hxbmem : x ∈ Prod.mk b ⁻¹' t := by
          have heq := Set.ext_iff.mp (hsections a ha b hbC) x
          exact heq.mp hx
        have hxb : x = b.val := by
          have := htD hxbmem
          simpa [D] using this.symm
        apply hba
        cases a
        cases b
        simp_all
      exact measure_mono_null hsubempty measure_empty
    rw [MeasureTheory.Measure.prod_apply ht]
    have hnotC : ∀ᵐ a ∂onlineCoarseLaw, a ∉ C := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using
        onlineCoarseLaw_apply_countable C hC
    have hae : (fun a => ν (Prod.mk a ⁻¹' t)) =ᵐ[onlineCoarseLaw]
        (fun _ => 0) := hnotC.mono fun a ha => hsection_zero a ha
    rw [lintegral_congr_ae hae]
    simp
  have hD_zero : onlineCoarseLaw.prod ν D = 0 := by
    rw [← ht_zero]
    exact measure_congr hteq.symm
  exact zero_ne_one (hD_zero.symm.trans hD_one)

theorem onlineCoarseDiagonal_swapped_not_nullMeasurable
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    ¬ NullMeasurableSet
      ({p : ℝ × OnlineCoarseReal | p.1 = p.2.val})
      (ν.prod onlineCoarseLaw) := by
  intro h
  have hpre := h.preimage
    (Measure.measurePreserving_swap (μ := onlineCoarseLaw) (ν := ν)).quasiMeasurePreserving
  exact onlineCoarseDiagonal_not_nullMeasurable ν (by
    simpa only [Prod.swap, Set.preimage_setOf_eq, eq_comm] using hpre)

/-- The union of two fresh coarse equality diagonals is still nonmeasurable
after completion.  This is the exact scalar event produced by a refresh
minibatch of size two in the generated proof-exact process below. -/
theorem onlineCoarseUnionDiagonals_not_nullMeasurable
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    ¬ NullMeasurableSet
      ({p : OnlineCoarseReal × (ℝ × OnlineCoarseReal) |
        p.1.val = p.2.1 ∨ p.2.1 = p.2.2.val})
      (onlineCoarseLaw.prod (ν.prod onlineCoarseLaw)) := by
  let D : Set (OnlineCoarseReal × (ℝ × OnlineCoarseReal)) :=
    {p | p.1.val = p.2.1 ∨ p.2.1 = p.2.2.val}
  have hdiag_inner_zero
      (t : Set (ℝ × OnlineCoarseReal)) (ht : MeasurableSet t)
      (htD : t ⊆ {p : ℝ × OnlineCoarseReal | p.1 = p.2.val}) :
      (ν.prod onlineCoarseLaw) t = 0 := by
    rw [MeasureTheory.Measure.prod_apply ht]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with q
    apply measure_mono_null
      (show Prod.mk q ⁻¹' t ⊆ {onlineCoarseWrap q} by
        intro c hc
        have hqc := htD hc
        cases c
        simpa [onlineCoarseWrap] using hqc.symm)
    exact measure_singleton _
  have hsuperset (s : Set (OnlineCoarseReal × (ℝ × OnlineCoarseReal)))
      (hs : MeasurableSet s) (hDs : D ⊆ s) :
      onlineCoarseLaw.prod (ν.prod onlineCoarseLaw) s = 1 := by
    rcases onlineCoarse_product_sections_eventually_constant s hs with
      ⟨C, hC, hsections⟩
    have hsection_one : ∀ a ∉ C, (ν.prod onlineCoarseLaw) (Prod.mk a ⁻¹' s) = 1 := by
      intro a ha
      let A : Set ℝ := {q | onlineCoarseWrap q ∉ C}
      have hAcompl : Aᶜ.Countable := by
        have hpre : (onlineCoarseWrap ⁻¹' C).Countable :=
          hC.preimage onlineCoarseWrap_injective
        apply hpre.mono
        intro q hq
        simpa [A] using hq
      have hAmeas : MeasurableSet A := by
        rw [← compl_compl A]
        exact hAcompl.measurableSet.compl
      have hAone : ν A = 1 := by
        have hcompl := measure_compl hAcompl.measurableSet (measure_ne_top ν Aᶜ)
        simpa [hAcompl.measure_zero ν] using hcompl
      have hcontains : A ×ˢ (Set.univ : Set OnlineCoarseReal) ⊆
          Prod.mk a ⁻¹' s := by
        rintro ⟨q, c⟩ ⟨hq, -⟩
        have hdiag : (onlineCoarseWrap q, (q, c)) ∈ D := by
          simp [D, onlineCoarseWrap]
        have hmem : (onlineCoarseWrap q, (q, c)) ∈ s := hDs hdiag
        have heq := Set.ext_iff.mp
          (hsections (onlineCoarseWrap q) hq a ha) (q, c)
        exact heq.mp hmem
      have hlower : (ν.prod onlineCoarseLaw)
            (A ×ˢ (Set.univ : Set OnlineCoarseReal)) ≤
          (ν.prod onlineCoarseLaw) (Prod.mk a ⁻¹' s) :=
        measure_mono hcontains
      rw [Measure.prod_prod, hAone, measure_univ,
        mul_one] at hlower
      exact le_antisymm prob_le_one hlower
    rw [MeasureTheory.Measure.prod_apply hs]
    have hnotC : ∀ᵐ a ∂onlineCoarseLaw, a ∉ C := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using
        onlineCoarseLaw_apply_countable C hC
    have hae : (fun a => (ν.prod onlineCoarseLaw) (Prod.mk a ⁻¹' s))
        =ᵐ[onlineCoarseLaw] (fun _ => 1) :=
      hnotC.mono fun a ha => hsection_one a ha
    rw [lintegral_congr_ae hae]
    simp
  have hD_one : onlineCoarseLaw.prod (ν.prod onlineCoarseLaw) D = 1 := by
    rcases exists_measurable_superset
        (onlineCoarseLaw.prod (ν.prod onlineCoarseLaw)) D with
      ⟨s, hDs, hs, hmeasure⟩
    rw [← hmeasure]
    exact hsuperset s hs hDs
  intro hnull
  rcases hnull.exists_measurable_subset_ae_eq with ⟨t, htD, ht, hteq⟩
  have ht_zero : onlineCoarseLaw.prod (ν.prod onlineCoarseLaw) t = 0 := by
    rcases onlineCoarse_product_sections_eventually_constant t ht with
      ⟨C, hC, hsections⟩
    have hsection_zero : ∀ a ∉ C,
        (ν.prod onlineCoarseLaw) (Prod.mk a ⁻¹' t) = 0 := by
      intro a ha
      obtain ⟨b, hbC, hba⟩ : ∃ b : OnlineCoarseReal, b ∉ C ∧ b ≠ a := by
        by_contra h
        push Not at h
        have hsub : Set.univ ⊆ insert a C := by
          intro b _
          by_cases hb : b ∈ C
          · exact Set.mem_insert_iff.mpr (Or.inr hb)
          · exact Set.mem_insert_iff.mpr (Or.inl (h b hb))
        have huniv : (Set.univ : Set OnlineCoarseReal).Countable :=
          (hC.insert a).mono hsub
        haveI : Countable OnlineCoarseReal := Set.countable_univ_iff.mp huniv
        haveI : Countable ℝ := onlineCoarseWrap_injective.countable
        exact Cardinal.not_countable_real
          (Set.countable_univ_iff.mpr inferInstance)
      have hsubdiag : Prod.mk a ⁻¹' t ⊆
          {p : ℝ × OnlineCoarseReal | p.1 = p.2.val} := by
        rintro ⟨q, c⟩ hmem
        have hmemB : (q, c) ∈ Prod.mk b ⁻¹' t := by
          have heq := Set.ext_iff.mp (hsections a ha b hbC) (q, c)
          exact heq.mp hmem
        have haD := htD hmem
        have hbD := htD hmemB
        by_contra hqc
        rcases haD with haq | hqc' <;> rcases hbD with hbq | hqc''
        · apply hba
          cases a
          cases b
          congr
          exact hbq.trans haq.symm
        · exact hqc hqc''
        · exact hqc hqc'
        · exact hqc hqc'
      exact hdiag_inner_zero _ (measurable_prodMk_left ht) hsubdiag
    rw [MeasureTheory.Measure.prod_apply ht]
    have hnotC : ∀ᵐ a ∂onlineCoarseLaw, a ∉ C := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using
        onlineCoarseLaw_apply_countable C hC
    have hae : (fun a => (ν.prod onlineCoarseLaw) (Prod.mk a ⁻¹' t))
        =ᵐ[onlineCoarseLaw] (fun _ => 0) :=
      hnotC.mono fun a ha => hsection_zero a ha
    rw [lintegral_congr_ae hae]
    simp
  have hD_zero : onlineCoarseLaw.prod (ν.prod onlineCoarseLaw) D = 0 := by
    rw [← ht_zero]
    exact measure_congr hteq.symm
  exact zero_ne_one (hD_zero.symm.trans hD_one)

/-- Law-parametric form of the preceding union-of-diagonals obstruction.
The query and the second coarse coordinate may retain all of their ambient
round data; only their displayed pushforward laws are used. -/
theorem onlineCoarseUnionDiagonals_of_maps_not_nullMeasurable
    {Q R : Type*} [MeasurableSpace Q] [MeasurableSpace R]
    (mu : Measure Q) (rho : Measure R) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure rho] (query : Q → ℝ) (coarse : R → OnlineCoarseReal)
    (hquery : Measurable query) (hcoarse : Measurable coarse)
    (hcoarseMap : Measure.map coarse rho = onlineCoarseLaw)
    [NoAtoms (Measure.map query mu)] :
    ¬ NullMeasurableSet
      ({p : OnlineCoarseReal × (Q × R) |
        p.1.val = query p.2.1 ∨ query p.2.1 = (coarse p.2.2).val})
      (onlineCoarseLaw.prod (mu.prod rho)) := by
  let D : Set (OnlineCoarseReal × (Q × R)) :=
    {p | p.1.val = query p.2.1 ∨ query p.2.1 = (coarse p.2.2).val}
  have hdiag_inner_zero (t : Set (Q × R)) (ht : MeasurableSet t)
      (htD : t ⊆ {p : Q × R | query p.1 = (coarse p.2).val}) :
      (mu.prod rho) t = 0 := by
    rw [MeasureTheory.Measure.prod_apply ht]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [] with z
    apply measure_mono_null
      (show Prod.mk z ⁻¹' t ⊆ coarse ⁻¹' {onlineCoarseWrap (query z)} by
        intro r hr
        have hzr := htD hr
        change query z = (coarse r).val at hzr
        change coarse r = onlineCoarseWrap (query z)
        cases hc : coarse r with
        | mk v =>
            rw [hc] at hzr
            congr
            exact hzr.symm)
    have hsingleton : MeasurableSet {onlineCoarseWrap (query z)} := by
      rw [onlineCoarseReal_measurableSet_iff]
      exact Or.inl (Set.countable_singleton _)
    calc
      rho (coarse ⁻¹' {onlineCoarseWrap (query z)}) =
          Measure.map coarse rho {onlineCoarseWrap (query z)} := by
        rw [Measure.map_apply hcoarse hsingleton]
      _ = onlineCoarseLaw {onlineCoarseWrap (query z)} := by rw [hcoarseMap]
      _ = 0 := measure_singleton _
  have hsuperset (s : Set (OnlineCoarseReal × (Q × R)))
      (hs : MeasurableSet s) (hDs : D ⊆ s) :
      onlineCoarseLaw.prod (mu.prod rho) s = 1 := by
    rcases onlineCoarse_product_sections_eventually_constant s hs with
      ⟨C, hC, hsections⟩
    have hsection_one : ∀ a ∉ C, (mu.prod rho) (Prod.mk a ⁻¹' s) = 1 := by
      intro a ha
      let U : Set ℝ := onlineCoarseWrap ⁻¹' C
      let A : Set Q := query ⁻¹' Uᶜ
      have hUcount : U.Countable := hC.preimage onlineCoarseWrap_injective
      have hUmeas : MeasurableSet U := hUcount.measurableSet
      have hAmeas : MeasurableSet A := hquery hUmeas.compl
      have hUzero : Measure.map query mu U = 0 := hUcount.measure_zero _
      have hAone : mu A = 1 := by
        have hprezero : mu (query ⁻¹' U) = 0 := by
          rw [← Measure.map_apply hquery hUmeas]
          exact hUzero
        have hcompl := measure_compl (hquery hUmeas)
          (measure_ne_top mu (query ⁻¹' U))
        simpa [A, hprezero] using hcompl
      have hcontains : A ×ˢ (Set.univ : Set R) ⊆ Prod.mk a ⁻¹' s := by
        rintro ⟨z, r⟩ ⟨hz, -⟩
        have hzC : onlineCoarseWrap (query z) ∉ C := hz
        have hdiag : (onlineCoarseWrap (query z), (z, r)) ∈ D := by
          simp [D, onlineCoarseWrap]
        have hmem : (onlineCoarseWrap (query z), (z, r)) ∈ s := hDs hdiag
        have heq := Set.ext_iff.mp
          (hsections (onlineCoarseWrap (query z)) hzC a ha) (z, r)
        exact heq.mp hmem
      have hlower : (mu.prod rho) (A ×ˢ (Set.univ : Set R)) ≤
          (mu.prod rho) (Prod.mk a ⁻¹' s) := measure_mono hcontains
      rw [Measure.prod_prod, hAone, measure_univ, mul_one] at hlower
      exact le_antisymm prob_le_one hlower
    rw [MeasureTheory.Measure.prod_apply hs]
    have hnotC : ∀ᵐ a ∂onlineCoarseLaw, a ∉ C := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using
        onlineCoarseLaw_apply_countable C hC
    have hae : (fun a => (mu.prod rho) (Prod.mk a ⁻¹' s))
        =ᵐ[onlineCoarseLaw] (fun _ => 1) :=
      hnotC.mono fun a ha => hsection_one a ha
    rw [lintegral_congr_ae hae]
    simp
  have hD_one : onlineCoarseLaw.prod (mu.prod rho) D = 1 := by
    rcases exists_measurable_superset (onlineCoarseLaw.prod (mu.prod rho)) D with
      ⟨s, hDs, hs, hmeasure⟩
    rw [← hmeasure]
    exact hsuperset s hs hDs
  intro hnull
  rcases hnull.exists_measurable_subset_ae_eq with ⟨t, htD, ht, hteq⟩
  have ht_zero : onlineCoarseLaw.prod (mu.prod rho) t = 0 := by
    rcases onlineCoarse_product_sections_eventually_constant t ht with
      ⟨C, hC, hsections⟩
    have hsection_zero : ∀ a ∉ C, (mu.prod rho) (Prod.mk a ⁻¹' t) = 0 := by
      intro a ha
      obtain ⟨b, hbC, hba⟩ : ∃ b : OnlineCoarseReal, b ∉ C ∧ b ≠ a := by
        by_contra h
        push Not at h
        have hsub : Set.univ ⊆ insert a C := by
          intro b _
          by_cases hb : b ∈ C
          · exact Set.mem_insert_iff.mpr (Or.inr hb)
          · exact Set.mem_insert_iff.mpr (Or.inl (h b hb))
        have huniv : (Set.univ : Set OnlineCoarseReal).Countable :=
          (hC.insert a).mono hsub
        haveI : Countable OnlineCoarseReal := Set.countable_univ_iff.mp huniv
        haveI : Countable ℝ := onlineCoarseWrap_injective.countable
        exact Cardinal.not_countable_real
          (Set.countable_univ_iff.mpr inferInstance)
      have hsubdiag : Prod.mk a ⁻¹' t ⊆
          {p : Q × R | query p.1 = (coarse p.2).val} := by
        rintro ⟨z, r⟩ hmem
        have hmemB : (z, r) ∈ Prod.mk b ⁻¹' t := by
          have heq := Set.ext_iff.mp (hsections a ha b hbC) (z, r)
          exact heq.mp hmem
        have haD := htD hmem
        have hbD := htD hmemB
        by_contra hzr
        rcases haD with haq | hzr' <;> rcases hbD with hbq | hzr''
        · apply hba
          cases a
          cases b
          congr
          exact hbq.trans haq.symm
        · exact hzr hzr''
        · exact hzr hzr'
        · exact hzr hzr'
      exact hdiag_inner_zero _ (measurable_prodMk_left ht) hsubdiag
    rw [MeasureTheory.Measure.prod_apply ht]
    have hnotC : ∀ᵐ a ∂onlineCoarseLaw, a ∉ C := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using
        onlineCoarseLaw_apply_countable C hC
    have hae : (fun a => (mu.prod rho) (Prod.mk a ⁻¹' t))
        =ᵐ[onlineCoarseLaw] (fun _ => 0) :=
      hnotC.mono fun a ha => hsection_zero a ha
    rw [lintegral_congr_ae hae]
    simp
  have hD_zero : onlineCoarseLaw.prod (mu.prod rho) D = 0 := by
    rw [← ht_zero]
    exact measure_congr hteq.symm
  exact zero_ne_one (hD_zero.symm.trans hD_one)

/-- A bounded separately measurable kernel with genuine fixed-query moments
but no random-variable semantics under an independent atomless query law.
Unlike the earlier `Unit` witness, the sample law here is a nonzero
probability with Mathlib's `NoAtoms` property, and the failure is exact
product-law a.e. measurability rather than global pointwise measurability. -/
theorem onlineAtomless_fixedQueryMoments_not_productRegular
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    (IsProbabilityMeasure onlineCoarseLaw ∧ NoAtoms onlineCoarseLaw) ∧
      (∀ q : ℝ, Integrable
        (fun s : OnlineCoarseReal => if q = s.val then (0 : ℝ) else 1)
        onlineCoarseLaw) ∧
      ¬ AEStronglyMeasurable
        (fun p : ℝ × OnlineCoarseReal =>
          if p.1 = p.2.val then (0 : ℝ) else 1)
        (ν.prod onlineCoarseLaw) := by
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro q
    have heq : {s : OnlineCoarseReal | q = s.val} = {onlineCoarseWrap q} := by
      ext s
      cases s with
      | mk x => simp [onlineCoarseWrap, eq_comm]
    have hset : MeasurableSet {s : OnlineCoarseReal | q = s.val} := by
      rw [heq, onlineCoarseReal_measurableSet_iff]
      exact Or.inl (Set.countable_singleton _)
    have hmeas : Measurable
        (fun s : OnlineCoarseReal => if q = s.val then (0 : ℝ) else 1) :=
      measurable_const.ite hset measurable_const
    have hsetCompl : MeasurableSet {s : OnlineCoarseReal | q = s.val}ᶜ :=
      MeasurableSet.compl hset
    have hint : Integrable
        (({s : OnlineCoarseReal | q = s.val}ᶜ).indicator
          (fun _ : OnlineCoarseReal => (1 : ℝ)))
        onlineCoarseLaw :=
      (integrable_const (μ := onlineCoarseLaw) (c := (1 : ℝ))).indicator hsetCompl
    apply hint.congr
    filter_upwards [] with s
    by_cases h : q = s.val <;> simp [h, Set.indicator]
  · intro hprod
    have hnull := hprod.aemeasurable.nullMeasurableSet_preimage
      (measurableSet_singleton (0 : ℝ))
    have hpre :
        (fun p : ℝ × OnlineCoarseReal =>
          if p.1 = p.2.val then (0 : ℝ) else 1) ⁻¹' ({0} : Set ℝ) =
          {p : ℝ × OnlineCoarseReal | p.1 = p.2.val} := by
      ext p
      by_cases h : p.1 = p.2.val <;> simp [h]
    rw [hpre] at hnull
    exact onlineCoarseDiagonal_swapped_not_nullMeasurable ν hnull

/-- A sampled loss realizing the preceding bounded kernel as an actual
Mathlib gradient.  It is the identity loss away from the sample-selected
point and has a unit jump at that point. -/
noncomputable def onlineCoarsePointJumpLoss
    (s : OnlineCoarseReal) : ℝ → ℝ :=
  Function.update id s.val (s.val + 1)

theorem onlineCoarsePointJumpLoss_gradient
    (s : OnlineCoarseReal) (x : ℝ) :
    gradient (onlineCoarsePointJumpLoss s) x =
      if x = s.val then 0 else 1 := by
  by_cases hx : x = s.val
  · subst x
    rw [if_pos rfl, gradient_eq_zero_of_not_differentiableAt]
    intro hdiff
    have hcont : ContinuousAt (onlineCoarsePointJumpLoss s) s.val :=
      hdiff.continuousAt
    have hjump : Filter.Tendsto id (nhdsWithin s.val {s.val}ᶜ)
        (nhds (s.val + 1)) := by
      simpa [onlineCoarsePointJumpLoss] using
        (continuousAt_update_same.mp hcont)
    have hid : Filter.Tendsto id (nhdsWithin s.val {s.val}ᶜ) (nhds s.val) :=
      continuousAt_id.mono_left inf_le_left
    have heq : s.val = s.val + 1 := tendsto_nhds_unique hid hjump
    linarith
  · rw [if_neg hx]
    have hevent : onlineCoarsePointJumpLoss s =ᶠ[nhds x] id := by
      filter_upwards [eventually_ne_nhds hx] with y hy
      simp [onlineCoarsePointJumpLoss, Function.update_of_ne hy]
    rw [hevent.gradient_eq]
    unfold gradient
    rw [fderiv_id]
    apply (InnerProductSpace.toDual ℝ ℝ).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    apply ContinuousLinearMap.ext
    intro y
    simp only [InnerProductSpace.toDual_apply_apply]
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
    simp

/-- The atomless product-law obstruction is gradient-realizable: it is not
an arbitrary oracle kernel.  Every fixed query has an integrable stochastic
gradient, while evaluating the very same gradients at an independent
atomless query destroys a.e. strong measurability. -/
theorem onlineAtomless_sampledGradient_not_productRegular
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    (∀ q : ℝ, Integrable
      (fun s : OnlineCoarseReal ↦ gradient (onlineCoarsePointJumpLoss s) q)
      onlineCoarseLaw) ∧
      ¬ AEStronglyMeasurable
        (fun p : ℝ × OnlineCoarseReal ↦
          gradient (onlineCoarsePointJumpLoss p.2) p.1)
        (ν.prod onlineCoarseLaw) := by
  rcases onlineAtomless_fixedQueryMoments_not_productRegular ν with
    ⟨_, hfixed, hproduct⟩
  constructor
  · intro q
    simpa only [onlineCoarsePointJumpLoss_gradient] using hfixed q
  · simpa only [onlineCoarsePointJumpLoss_gradient] using hproduct

abbrev onlineCoarseCounterexampleWorkers : Count :=
  ⟨1, by omega⟩

abbrev OnlineCoarseCounterexampleSample
    (_ : Worker onlineCoarseCounterexampleWorkers) := OnlineCoarseReal

noncomputable def onlineCoarseCounterexamplePoint (r : ℝ) :
    Point oldInitialBoundCounterexampleDimension :=
  r • oldInitialBoundCounterexampleDirection

theorem onlineCoarseCounterexamplePoint_injective :
    Function.Injective onlineCoarseCounterexamplePoint := by
  intro r t h
  have hcoordinate := congrArg
    (fun x : Point oldInitialBoundCounterexampleDimension ↦ x 0) h
  simpa [onlineCoarseCounterexamplePoint,
    oldInitialBoundCounterexampleDirection] using hcoordinate

noncomputable def onlineCoarseCounterexampleLoss
    (s : OnlineCoarseReal) : Point oldInitialBoundCounterexampleDimension → ℝ :=
  Function.update
    (innerSL ℝ oldInitialBoundCounterexampleDirection)
    (onlineCoarseCounterexamplePoint s.val) (s.val + 1)

theorem onlineCoarseCounterexampleLoss_gradient_at_query
    (s : OnlineCoarseReal) (q : ℝ) :
    gradient (onlineCoarseCounterexampleLoss s)
        (onlineCoarseCounterexamplePoint q) =
      if q = s.val then 0 else oldInitialBoundCounterexampleDirection := by
  by_cases hq : q = s.val
  · subst q
    rw [if_pos rfl, gradient_eq_zero_of_not_differentiableAt]
    intro hdiff
    have hcont : ContinuousAt (onlineCoarseCounterexampleLoss s)
        (onlineCoarseCounterexamplePoint s.val) := hdiff.continuousAt
    have hjump : Filter.Tendsto
        (innerSL ℝ oldInitialBoundCounterexampleDirection)
        (nhdsWithin (onlineCoarseCounterexamplePoint s.val)
          {onlineCoarseCounterexamplePoint s.val}ᶜ)
        (nhds (s.val + 1)) := by
      simpa [onlineCoarseCounterexampleLoss] using
        (continuousAt_update_same.mp hcont)
    have hbase : ContinuousAt
        (innerSL ℝ oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint s.val) :=
      (innerSL ℝ oldInitialBoundCounterexampleDirection).continuous.continuousAt
    have hlimit : Filter.Tendsto
        (innerSL ℝ oldInitialBoundCounterexampleDirection)
        (nhdsWithin (onlineCoarseCounterexamplePoint s.val)
          {onlineCoarseCounterexamplePoint s.val}ᶜ)
        (nhds s.val) := by
      have hlimit' : Filter.Tendsto
          (innerSL ℝ oldInitialBoundCounterexampleDirection)
          (nhdsWithin (onlineCoarseCounterexamplePoint s.val)
            {onlineCoarseCounterexamplePoint s.val}ᶜ)
          (nhds ((innerSL ℝ oldInitialBoundCounterexampleDirection)
            (onlineCoarseCounterexamplePoint s.val))) :=
        hbase.mono_left inf_le_left
      simpa [onlineCoarseCounterexamplePoint,
        oldInitialBoundCounterexampleDirection] using hlimit'
    have heq : s.val = s.val + 1 := tendsto_nhds_unique hlimit hjump
    linarith
  · rw [if_neg hq]
    have hpoint_ne : onlineCoarseCounterexamplePoint q ≠
        onlineCoarseCounterexamplePoint s.val :=
      fun h ↦ hq (onlineCoarseCounterexamplePoint_injective h)
    have hevent : onlineCoarseCounterexampleLoss s =ᶠ[
        nhds (onlineCoarseCounterexamplePoint q)]
        (innerSL ℝ oldInitialBoundCounterexampleDirection) := by
      filter_upwards [eventually_ne_nhds hpoint_ne] with y hy
      simp [onlineCoarseCounterexampleLoss, Function.update_of_ne hy]
    rw [hevent.gradient_eq]
    have hgradient : HasGradientAt
        (innerSL ℝ oldInitialBoundCounterexampleDirection)
        oldInitialBoundCounterexampleDirection
        (onlineCoarseCounterexamplePoint q) := by
      rw [hasGradientAt_iff_hasFDerivAt]
      exact (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt
    exact hgradient.gradient

theorem onlineCoarseCounterexampleLoss_ae_eq_base
    (x : Point oldInitialBoundCounterexampleDimension) :
    (fun s ↦ onlineCoarseCounterexampleLoss s x) =ᵐ[onlineCoarseLaw]
      (fun _ ↦ (innerSL ℝ oldInitialBoundCounterexampleDirection) x) := by
  let exceptional : Set OnlineCoarseReal :=
    {s | onlineCoarseCounterexamplePoint s.val = x}
  have hexceptional_subsingleton : exceptional.Subsingleton := by
    intro a ha b hb
    have hab : a.val = b.val := onlineCoarseCounterexamplePoint_injective
      (ha.trans hb.symm)
    cases a
    cases b
    simp_all
  have hexceptional_countable : exceptional.Countable :=
    hexceptional_subsingleton.countable
  have hnot_exceptional : ∀ᵐ s ∂onlineCoarseLaw, s ∉ exceptional := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      onlineCoarseLaw_apply_countable exceptional hexceptional_countable
  exact hnot_exceptional.mono fun s hs ↦ by
    have hne : x ≠ onlineCoarseCounterexamplePoint s.val := by
      intro h
      exact hs h.symm
    exact Function.update_of_ne hne _ _

noncomputable def onlineCoarseCounterexampleProblem :
    OnlineProblem oldInitialBoundCounterexampleDimension
      onlineCoarseCounterexampleWorkers OnlineCoarseCounterexampleSample where
  sampleLoss _ s := onlineCoarseCounterexampleLoss s
  sampleLaw _ := onlineCoarseLaw
  sampleLaw_isProbability _ := by infer_instance
  sampleLoss_integrable i x := by
    exact (integrable_const
      (c := (innerSL ℝ oldInitialBoundCounterexampleDirection) x)).congr
        (onlineCoarseCounterexampleLoss_ae_eq_base x).symm

theorem onlineCoarseCounterexample_expectedSampleLoss
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    expectedSampleLoss onlineCoarseCounterexampleProblem i x =
      (innerSL ℝ oldInitialBoundCounterexampleDirection) x := by
  fin_cases i
  unfold expectedSampleLoss
  change (∫ s, onlineCoarseCounterexampleLoss s x ∂onlineCoarseLaw) = _
  rw [integral_congr_ae (onlineCoarseCounterexampleLoss_ae_eq_base x)]
  simp

theorem onlineCoarseCounterexample_localGradient
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    localGradient (onlineLocalProblem onlineCoarseCounterexampleProblem) i x =
      oldInitialBoundCounterexampleDirection := by
  have hfun :
      (onlineLocalProblem onlineCoarseCounterexampleProblem).localLoss i =
        innerSL ℝ oldInitialBoundCounterexampleDirection := by
    funext y
    exact onlineCoarseCounterexample_expectedSampleLoss i y
  unfold localGradient
  rw [hfun]
  have hgradient : HasGradientAt
      (innerSL ℝ oldInitialBoundCounterexampleDirection)
      oldInitialBoundCounterexampleDirection x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt
  exact hgradient.gradient

theorem onlineCoarseCounterexamplePoint_coordinate
    (x : Point oldInitialBoundCounterexampleDimension) :
    onlineCoarseCounterexamplePoint (x 0) = x := by
  ext j
  fin_cases j
  simp [onlineCoarseCounterexamplePoint,
    oldInitialBoundCounterexampleDirection]

theorem onlineCoarseCounterexample_stochasticGradient_ae
    (x : Point oldInitialBoundCounterexampleDimension) :
    (fun s ↦ stochasticGradient onlineCoarseCounterexampleProblem 0 s x) =ᵐ[
      onlineCoarseLaw] (fun _ ↦ oldInitialBoundCounterexampleDirection) := by
  have hnot : ∀ᵐ s ∂onlineCoarseLaw, s ≠ onlineCoarseWrap (x 0) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      onlineCoarseLaw_apply_countable {onlineCoarseWrap (x 0)}
        (Set.countable_singleton _)
  filter_upwards [hnot] with s hs
  have hne : x 0 ≠ s.val := by
    intro h
    apply hs
    cases s
    simp_all [onlineCoarseWrap]
  rw [← onlineCoarseCounterexamplePoint_coordinate x]
  simpa [stochasticGradient, onlineCoarseCounterexampleProblem, hne] using
    onlineCoarseCounterexampleLoss_gradient_at_query s (x 0)

/-- The concrete atomless online problem satisfies the literal fixed-query
unbiasedness and bounded-variance assumption with zero variance. -/
theorem onlineCoarseCounterexample_literal_variance :
    LegacyOnlineFixedQueryUnbiasedBoundedVariance onlineCoarseCounterexampleProblem
      (fun _ ↦ 0) := by
  constructor
  · intro i
    exact le_rfl
  · intro i x
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    letI : IsProbabilityMeasure
        (onlineCoarseCounterexampleProblem.sampleLaw 0) :=
      onlineCoarseCounterexampleProblem.sampleLaw_isProbability 0
    let e := oldInitialBoundCounterexampleDirection
    have hae := onlineCoarseCounterexample_stochasticGradient_ae x
    have hlocal := onlineCoarseCounterexample_localGradient 0 x
    have hint : Integrable
        (fun s ↦ stochasticGradient onlineCoarseCounterexampleProblem 0 s x)
        onlineCoarseLaw :=
      (integrable_const (c := e)).congr hae.symm
    have hresidual_ae :
        (fun s ↦ ‖stochasticGradient onlineCoarseCounterexampleProblem 0 s x -
          localGradient (onlineLocalProblem onlineCoarseCounterexampleProblem) 0 x‖ ^ 2)
          =ᵐ[onlineCoarseLaw] (fun _ ↦ 0) :=
      hae.mono fun s hs ↦ by simp [hs, hlocal, e]
    refine ⟨hint, ?_, ?_, ?_⟩
    · exact (integrable_const (c := (0 : ℝ))).congr hresidual_ae.symm
    · change (∫ s : OnlineCoarseReal,
          stochasticGradient onlineCoarseCounterexampleProblem 0 s x
          ∂onlineCoarseLaw) = _
      rw [integral_congr_ae hae]
      simpa [hlocal, e]
    · change (∫ s : OnlineCoarseReal,
          ‖stochasticGradient onlineCoarseCounterexampleProblem 0 s x -
            localGradient (onlineLocalProblem onlineCoarseCounterexampleProblem) 0 x‖ ^ 2
          ∂onlineCoarseLaw) ≤ 0 ^ 2
      rw [integral_congr_ae hresidual_ae]
      simp

/-- The diagonal obstruction is realized by the canonical `stochasticGradient`
of an actual `OnlineProblem`, not by a free oracle witness.  Thus fixed-query
sample-loss integrability does not by itself make adaptive stochastic-gradient
evaluation a random variable. -/
theorem onlineAtomless_onlineProblemGradient_not_productRegular
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NoAtoms ν] :
    ¬ AEStronglyMeasurable
      (fun p : ℝ × OnlineCoarseReal ↦
        stochasticGradient onlineCoarseCounterexampleProblem 0 p.2
          (onlineCoarseCounterexamplePoint p.1))
      (ν.prod onlineCoarseLaw) := by
  intro hgradient
  let projection : Point oldInitialBoundCounterexampleDimension →L[ℝ] ℝ :=
    innerSL ℝ oldInitialBoundCounterexampleDirection
  have hcoordinate : AEStronglyMeasurable
      (fun p : ℝ × OnlineCoarseReal ↦
        projection
          (stochasticGradient onlineCoarseCounterexampleProblem 0 p.2
            (onlineCoarseCounterexamplePoint p.1)))
      (ν.prod onlineCoarseLaw) :=
    projection.continuous.comp_aestronglyMeasurable hgradient
  have hbad :=
    (onlineAtomless_fixedQueryMoments_not_productRegular ν).2.2
  apply hbad
  apply hcoordinate.congr
  filter_upwards [] with p
  have hsg : stochasticGradient onlineCoarseCounterexampleProblem 0 p.2
      (onlineCoarseCounterexamplePoint p.1) =
        if p.1 = p.2.val then 0 else oldInitialBoundCounterexampleDirection := by
    simpa [stochasticGradient, onlineCoarseCounterexampleProblem] using
      onlineCoarseCounterexampleLoss_gradient_at_query p.2 p.1
  rw [hsg]
  by_cases hp : p.1 = p.2.val
  · simp [hp]
  · simp [hp, projection, oldInitialBoundCounterexampleDirection,
      real_inner_eq_re_inner ℝ, RCLike.inner_apply]

/-! ### Generated proof-exact refresh counterexample candidate

The preceding theorem uses a free atomless query law.  The following concrete
data are the source-level candidate requested by the Eq. (46) audit.  The
Gaussian coordinate makes the first proof-exact refresh generate an atomless
next query, while the coarse coordinate retains the diagonal obstruction for
the following fresh refresh batch.  The sampled loss is linear away from one
sample-selected point, so every fixed-query exceptional set is null. -/

abbrev OnlineGeneratedRefreshSample
    (_ : Worker onlineCoarseCounterexampleWorkers) := OnlineCoarseReal × ℝ

abbrev onlineGeneratedRefreshBatch : Count := ⟨2, by omega⟩

abbrev onlineGeneratedDifferenceBatch : Count := ⟨1, by omega⟩

noncomputable def onlineGeneratedRefreshCenteredCoordinate (u : ℝ) : ℝ :=
  u / (1 + |u|)

theorem onlineGeneratedRefreshCenteredCoordinate_integrable :
    Integrable onlineGeneratedRefreshCenteredCoordinate
      (ProbabilityTheory.gaussianReal 0 1) := by
  apply integrable_of_measurable_bounded_real (C := 1)
  · unfold onlineGeneratedRefreshCenteredCoordinate
    fun_prop
  · intro u
    have hden : 0 < 1 + |u| := by positivity
    rw [onlineGeneratedRefreshCenteredCoordinate, Real.norm_eq_abs, abs_div,
      abs_of_pos hden]
    exact (div_le_one hden).2 (by linarith [abs_nonneg u])

theorem onlineGeneratedRefreshCenteredCoordinate_integral :
    (∫ u, onlineGeneratedRefreshCenteredCoordinate u
      ∂ProbabilityTheory.gaussianReal 0 1) = 0 := by
  let ν := ProbabilityTheory.gaussianReal 0 1
  have hmap : Measure.map (fun u : ℝ ↦ -u) ν = ν := by
    simpa [ν] using
      (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have hneg : (∫ u, onlineGeneratedRefreshCenteredCoordinate (-u) ∂ν) =
      ∫ u, onlineGeneratedRefreshCenteredCoordinate u ∂Measure.map (fun u : ℝ ↦ -u) ν := by
    symm
    exact MeasureTheory.integral_map (by fun_prop)
      (by simpa [hmap] using
        onlineGeneratedRefreshCenteredCoordinate_integrable.aestronglyMeasurable)
  have hodd : (∫ u, onlineGeneratedRefreshCenteredCoordinate (-u) ∂ν) =
      -∫ u, onlineGeneratedRefreshCenteredCoordinate u ∂ν := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with u
    simp [onlineGeneratedRefreshCenteredCoordinate, abs_neg, neg_div]
  have hneg' : (∫ u, onlineGeneratedRefreshCenteredCoordinate (-u) ∂ν) =
      ∫ u, onlineGeneratedRefreshCenteredCoordinate u ∂ν := by
    rw [hneg, hmap]
  linarith [hneg', hodd]

noncomputable def onlineGeneratedRefreshSlope
    (s : OnlineGeneratedRefreshSample 0) : ℝ :=
  10 + onlineGeneratedRefreshCenteredCoordinate s.2

noncomputable def onlineGeneratedRefreshLoss
    (s : OnlineGeneratedRefreshSample 0) :
    Point oldInitialBoundCounterexampleDimension → ℝ :=
  let base := onlineGeneratedRefreshSlope s •
    innerSL ℝ oldInitialBoundCounterexampleDirection
  Function.update base (onlineCoarseCounterexamplePoint s.1.val)
    (base (onlineCoarseCounterexamplePoint s.1.val) + 1)

theorem onlineGeneratedRefreshLoss_ae_eq_base
    (x : Point oldInitialBoundCounterexampleDimension) :
    (fun s : OnlineGeneratedRefreshSample 0 ↦
      onlineGeneratedRefreshLoss s x) =ᵐ[
        onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)]
      (fun s ↦ onlineGeneratedRefreshSlope s •
        (innerSL ℝ oldInitialBoundCounterexampleDirection) x) := by
  have hcoarse : ∀ᵐ c ∂onlineCoarseLaw,
      c ≠ onlineCoarseWrap (x 0) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      onlineCoarseLaw_apply_countable {onlineCoarseWrap (x 0)}
        (Set.countable_singleton _)
  have hprod : ∀ᵐ s ∂onlineCoarseLaw.prod
      (ProbabilityTheory.gaussianReal 0 1),
      s.1 ≠ onlineCoarseWrap (x 0) :=
    MeasureTheory.Measure.quasiMeasurePreserving_fst.tendsto_ae hcoarse
  filter_upwards [hprod] with s hs
  have hpoint : x ≠ onlineCoarseCounterexamplePoint s.1.val := by
    intro hx
    apply hs
    cases hsc : s.1 with
    | mk v =>
        have hcoord := congrArg
          (fun y : Point oldInitialBoundCounterexampleDimension ↦ y 0) hx.symm
        simp [onlineCoarseWrap, onlineCoarseCounterexamplePoint,
          oldInitialBoundCounterexampleDirection, hsc] at hcoord ⊢
        exact hcoord
  simp [onlineGeneratedRefreshLoss, Function.update_of_ne hpoint]

noncomputable def onlineGeneratedRefreshProblem :
    OnlineProblem oldInitialBoundCounterexampleDimension
      onlineCoarseCounterexampleWorkers OnlineGeneratedRefreshSample where
  sampleLoss _ s := onlineGeneratedRefreshLoss s
  sampleLaw _ := onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)
  sampleLaw_isProbability _ := by infer_instance
  sampleLoss_integrable i x := by
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let μ := onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)
    have hbase : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 ↦
          onlineGeneratedRefreshSlope s •
            (innerSL ℝ oldInitialBoundCounterexampleDirection) x) μ := by
      apply integrable_of_measurable_bounded_real
        (C := 11 * ‖(innerSL ℝ oldInitialBoundCounterexampleDirection) x‖)
      · unfold onlineGeneratedRefreshSlope onlineGeneratedRefreshCenteredCoordinate
        fun_prop
      · intro s
        have hs : |onlineGeneratedRefreshSlope s| ≤ 11 := by
          dsimp [onlineGeneratedRefreshSlope,
            onlineGeneratedRefreshCenteredCoordinate]
          have hden : 0 < 1 + |s.2| := by positivity
          have hfrac : |s.2 / (1 + |s.2|)| < 1 := by
            rw [abs_div, abs_of_pos hden]
            exact (div_lt_one hden).2 (by linarith [abs_nonneg s.2])
          have hbounds := (abs_lt.mp hfrac)
          rw [abs_of_pos (by linarith [hbounds.1])]
          linarith [hbounds.2]
        simpa [Real.norm_eq_abs] using
          (mul_le_mul_of_nonneg_right hs
            (norm_nonneg ((innerSL ℝ oldInitialBoundCounterexampleDirection) x)))
    exact hbase.congr
      (onlineGeneratedRefreshLoss_ae_eq_base x).symm

theorem onlineGeneratedRefresh_expectedSampleLoss
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    expectedSampleLoss onlineGeneratedRefreshProblem i x =
      10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) x := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  unfold expectedSampleLoss
  change (∫ s : OnlineGeneratedRefreshSample 0,
    onlineGeneratedRefreshLoss s x
      ∂onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) = _
  rw [integral_congr_ae (onlineGeneratedRefreshLoss_ae_eq_base x)]
  have hslopeGaussian : Integrable
      (fun u : ℝ ↦ 10 + onlineGeneratedRefreshCenteredCoordinate u)
      (ProbabilityTheory.gaussianReal 0 1) :=
    (integrable_const (c := (10 : ℝ))).add
      onlineGeneratedRefreshCenteredCoordinate_integrable
  have hslopeProduct : Integrable
      (fun s : OnlineGeneratedRefreshSample 0 ↦ onlineGeneratedRefreshSlope s)
      (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) := by
    have hm : Integrable
        (fun u : ℝ ↦ 10 + onlineGeneratedRefreshCenteredCoordinate u)
        (Measure.map Prod.snd
          (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1))) := by
      rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      exact hslopeGaussian
    simpa [onlineGeneratedRefreshSlope, Function.comp_def] using
      hm.comp_aemeasurable measurable_snd.aemeasurable
  rw [integral_smul_const]
  have hslopeIntegral :
      (∫ s : OnlineGeneratedRefreshSample 0, onlineGeneratedRefreshSlope s
        ∂onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) = 10 := by
    calc
      (∫ s : OnlineGeneratedRefreshSample 0, onlineGeneratedRefreshSlope s
          ∂onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)) =
          ∫ u : ℝ, 10 + onlineGeneratedRefreshCenteredCoordinate u
            ∂ProbabilityTheory.gaussianReal 0 1 := by
              have hslopeMap : AEStronglyMeasurable
                  (fun u : ℝ ↦ 10 + onlineGeneratedRefreshCenteredCoordinate u)
                  (Measure.map Prod.snd
                    (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1))) := by
                rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
                exact hslopeGaussian.aestronglyMeasurable
              have hmap := MeasureTheory.integral_map
                (μ := onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1))
                (φ := Prod.snd) measurable_snd.aemeasurable hslopeMap
              rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul] at hmap
              simpa [onlineGeneratedRefreshSlope, Function.comp_def] using hmap.symm
      _ = 10 := by
        rw [integral_add (integrable_const (c := (10 : ℝ)))
          onlineGeneratedRefreshCenteredCoordinate_integrable,
          onlineGeneratedRefreshCenteredCoordinate_integral]
        simp
  rw [hslopeIntegral]
  rfl

theorem onlineGeneratedRefresh_localGradient
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    localGradient (onlineLocalProblem onlineGeneratedRefreshProblem) i x =
      10 • oldInitialBoundCounterexampleDirection := by
  have hfun :
      (onlineLocalProblem onlineGeneratedRefreshProblem).localLoss i =
        fun y ↦ 10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) y := by
    funext y
    exact onlineGeneratedRefresh_expectedSampleLoss i y
  unfold localGradient
  rw [hfun]
  have hg : HasGradientAt
      (fun y : Point oldInitialBoundCounterexampleDimension ↦
        10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) y)
      (10 • oldInitialBoundCounterexampleDirection) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt.const_mul 10
      using 1
    ext z
    simp [InnerProductSpace.toDual_apply_apply]
  exact hg.gradient

theorem onlineGeneratedRefresh_isLocallySmooth :
    IsLocallySmooth (onlineLocalProblem onlineGeneratedRefreshProblem)
      (fun _ ↦ 0) := by
  constructor
  · intro i
    have hfun :
        (onlineLocalProblem onlineGeneratedRefreshProblem).localLoss i =
          fun y ↦ 10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) y := by
      funext y
      exact onlineGeneratedRefresh_expectedSampleLoss i y
    rw [hfun]
    fun_prop
  · intro i x y
    rw [onlineGeneratedRefresh_localGradient i x,
      onlineGeneratedRefresh_localGradient i y]
    simp

theorem onlineGeneratedRefresh_globalGradient
    (x : Point oldInitialBoundCounterexampleDimension) :
    globalGradient (onlineLocalProblem onlineGeneratedRefreshProblem) x =
      10 • oldInitialBoundCounterexampleDirection := by
  rw [globalGradient_eq_averageLocalGradient
    (onlineLocalProblem onlineGeneratedRefreshProblem)
    onlineGeneratedRefresh_isLocallySmooth.1 x]
  unfold averageLocalGradient average SOptLib.finiteUniformAverage
  norm_num [onlineGeneratedRefresh_localGradient,
    onlineCoarseCounterexampleWorkers]

theorem onlineGeneratedRefreshLoss_gradient_at_query
    (s : OnlineGeneratedRefreshSample 0) (q : ℝ) :
    gradient (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint q) =
      if q = s.1.val then 0
      else onlineGeneratedRefreshSlope s •
        oldInitialBoundCounterexampleDirection := by
  by_cases hq : q = s.1.val
  · subst q
    rw [if_pos rfl, gradient_eq_zero_of_not_differentiableAt]
    intro hdiff
    have hcont : ContinuousAt (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint s.1.val) := hdiff.continuousAt
    let base := onlineGeneratedRefreshSlope s •
      innerSL ℝ oldInitialBoundCounterexampleDirection
    have hjump : Filter.Tendsto base
        (nhdsWithin (onlineCoarseCounterexamplePoint s.1.val)
          {onlineCoarseCounterexamplePoint s.1.val}ᶜ)
        (nhds (base (onlineCoarseCounterexamplePoint s.1.val) + 1)) := by
      simpa [onlineGeneratedRefreshLoss, base] using
        (continuousAt_update_same.mp hcont)
    have hbase : ContinuousAt base
        (onlineCoarseCounterexamplePoint s.1.val) :=
      (onlineGeneratedRefreshSlope s •
        innerSL ℝ oldInitialBoundCounterexampleDirection).continuous.continuousAt
    have hlimit : Filter.Tendsto base
        (nhdsWithin (onlineCoarseCounterexamplePoint s.1.val)
          {onlineCoarseCounterexamplePoint s.1.val}ᶜ)
        (nhds (base (onlineCoarseCounterexamplePoint s.1.val))) :=
      hbase.mono_left inf_le_left
    have heq := tendsto_nhds_unique hlimit hjump
    linarith
  · rw [if_neg hq]
    have hpoint_ne : onlineCoarseCounterexamplePoint q ≠
        onlineCoarseCounterexamplePoint s.1.val :=
      fun h ↦ hq (onlineCoarseCounterexamplePoint_injective h)
    let base := onlineGeneratedRefreshSlope s •
      innerSL ℝ oldInitialBoundCounterexampleDirection
    have hevent : onlineGeneratedRefreshLoss s =ᶠ[
        nhds (onlineCoarseCounterexamplePoint q)] base := by
      filter_upwards [eventually_ne_nhds hpoint_ne] with y hy
      simp [onlineGeneratedRefreshLoss, base, Function.update_of_ne hy]
    rw [hevent.gradient_eq]
    have hgradient : HasGradientAt base
        (onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint q) := by
      rw [hasGradientAt_iff_hasFDerivAt]
      convert (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt.const_smul
        (onlineGeneratedRefreshSlope s) using 1
      ext z
      simp [base, InnerProductSpace.toDual_apply_apply]
    exact hgradient.gradient

theorem onlineGeneratedRefresh_stochasticGradient_ae
    (x : Point oldInitialBoundCounterexampleDimension) :
    (fun s : OnlineGeneratedRefreshSample 0 ↦
      stochasticGradient onlineGeneratedRefreshProblem 0 s x) =ᵐ[
        onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)]
      (fun s ↦ onlineGeneratedRefreshSlope s •
        oldInitialBoundCounterexampleDirection) := by
  have hcoarse : ∀ᵐ c ∂onlineCoarseLaw,
      c ≠ onlineCoarseWrap (x 0) := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using
      onlineCoarseLaw_apply_countable {onlineCoarseWrap (x 0)}
        (Set.countable_singleton _)
  have hprod : ∀ᵐ s ∂onlineCoarseLaw.prod
      (ProbabilityTheory.gaussianReal 0 1),
      s.1 ≠ onlineCoarseWrap (x 0) :=
    MeasureTheory.Measure.quasiMeasurePreserving_fst.tendsto_ae hcoarse
  filter_upwards [hprod] with s hs
  have hne : x 0 ≠ s.1.val := by
    intro h
    apply hs
    cases hsc : s.1 with
    | mk v =>
        simp [onlineCoarseWrap, hsc] at h ⊢
        exact h.symm
  rw [← onlineCoarseCounterexamplePoint_coordinate x]
  simpa [stochasticGradient, onlineGeneratedRefreshProblem, hne] using
    onlineGeneratedRefreshLoss_gradient_at_query s (x 0)

theorem onlineGeneratedRefresh_literalVariance :
    LegacyOnlineFixedQueryUnbiasedBoundedVariance onlineGeneratedRefreshProblem
      (fun _ ↦ 1) := by
  constructor
  · intro i
    norm_num
  · intro i x
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let μ := onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)
    let e := oldInitialBoundCounterexampleDirection
    have hcenteredGaussian : Integrable
        onlineGeneratedRefreshCenteredCoordinate
        (ProbabilityTheory.gaussianReal 0 1) :=
      onlineGeneratedRefreshCenteredCoordinate_integrable
    have hcenteredMap : Integrable onlineGeneratedRefreshCenteredCoordinate
        (Measure.map Prod.snd μ) := by
      change Integrable onlineGeneratedRefreshCenteredCoordinate
        (Measure.map Prod.snd
          (onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)))
      rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      exact hcenteredGaussian
    have hcentered : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 ↦
          onlineGeneratedRefreshCenteredCoordinate s.2) μ := by
      simpa [Function.comp_def] using
        hcenteredMap.comp_aemeasurable measurable_snd.aemeasurable
    have hslope : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 ↦ onlineGeneratedRefreshSlope s) μ := by
      simpa [onlineGeneratedRefreshSlope] using
        (integrable_const (c := (10 : ℝ))).add hcentered
    have hslopeVec : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 ↦
          onlineGeneratedRefreshSlope s • e) μ :=
      hslope.smul_const e
    have hae := onlineGeneratedRefresh_stochasticGradient_ae x
    have hlocal := onlineGeneratedRefresh_localGradient 0 x
    have hgrad : Integrable
        (fun s ↦ stochasticGradient onlineGeneratedRefreshProblem 0 s x) μ :=
      hslopeVec.congr hae.symm
    let residualSq := fun s : OnlineGeneratedRefreshSample 0 ↦
      ‖onlineGeneratedRefreshCenteredCoordinate s.2 • e‖ ^ 2
    have hresidualSq : Integrable residualSq μ := by
      apply integrable_of_measurable_bounded_real (C := 1)
      · unfold residualSq onlineGeneratedRefreshCenteredCoordinate
        fun_prop
      · intro s
        have hden : 0 < 1 + |s.2| := by positivity
        have hf : |onlineGeneratedRefreshCenteredCoordinate s.2| ≤ 1 := by
          rw [onlineGeneratedRefreshCenteredCoordinate, abs_div, abs_of_pos hden]
          exact (div_le_one hden).2 (by linarith [abs_nonneg s.2])
        have he : ‖e‖ = 1 := by
          simp [e, oldInitialBoundCounterexampleDirection]
        simp only [residualSq, norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
        rw [abs_of_nonneg (sq_nonneg _)]
        have hcUpper : onlineGeneratedRefreshCenteredCoordinate s.2 ≤ 1 :=
          (le_abs_self _).trans hf
        have hcLower : -1 ≤ onlineGeneratedRefreshCenteredCoordinate s.2 :=
          neg_le_of_abs_le hf
        nlinarith
    have hresidualAE :
        (fun s ↦ ‖stochasticGradient onlineGeneratedRefreshProblem 0 s x -
          localGradient (onlineLocalProblem onlineGeneratedRefreshProblem) 0 x‖ ^ 2)
          =ᵐ[μ] residualSq := by
      filter_upwards [hae] with s hs
      rw [hs, hlocal]
      change ‖(10 + onlineGeneratedRefreshCenteredCoordinate s.2) • e -
        10 • e‖ ^ 2 = ‖onlineGeneratedRefreshCenteredCoordinate s.2 • e‖ ^ 2
      congr 2
      module
    refine ⟨hgrad, hresidualSq.congr hresidualAE.symm, ?_, ?_⟩
    · change (∫ s : OnlineGeneratedRefreshSample 0,
          stochasticGradient onlineGeneratedRefreshProblem 0 s x ∂μ) = _
      rw [integral_congr_ae hae]
      have hscalar : (∫ s : OnlineGeneratedRefreshSample 0,
          onlineGeneratedRefreshSlope s ∂μ) = 10 := by
        rw [show (∫ s : OnlineGeneratedRefreshSample 0,
            onlineGeneratedRefreshSlope s ∂μ) =
            ∫ s : OnlineGeneratedRefreshSample 0,
              10 + onlineGeneratedRefreshCenteredCoordinate s.2 ∂μ by rfl,
          integral_add (integrable_const (c := (10 : ℝ))) hcentered]
        have hmap := MeasureTheory.integral_map
          (μ := μ) (φ := Prod.snd) measurable_snd.aemeasurable
          hcenteredMap.aestronglyMeasurable
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul] at hmap
        rw [← hmap, onlineGeneratedRefreshCenteredCoordinate_integral]
        simp [μ]
      rw [integral_smul_const, hscalar, hlocal]
      ext j
      fin_cases j
      simp [oldInitialBoundCounterexampleDirection]
    · change (∫ s : OnlineGeneratedRefreshSample 0,
          ‖stochasticGradient onlineGeneratedRefreshProblem 0 s x -
            localGradient (onlineLocalProblem onlineGeneratedRefreshProblem) 0 x‖ ^ 2
          ∂μ) ≤ 1 ^ 2
      rw [integral_congr_ae hresidualAE]
      calc
        (∫ s, residualSq s ∂μ) ≤ ∫ _s, (1 : ℝ) ∂μ := by
          apply integral_mono hresidualSq (integrable_const (c := (1 : ℝ)))
          intro s
          have hden : 0 < 1 + |s.2| := by positivity
          have hf : |onlineGeneratedRefreshCenteredCoordinate s.2| ≤ 1 := by
            rw [onlineGeneratedRefreshCenteredCoordinate, abs_div, abs_of_pos hden]
            exact (div_le_one hden).2 (by linarith [abs_nonneg s.2])
          have he : ‖e‖ = 1 := by
            simp [e, oldInitialBoundCounterexampleDirection]
          simp only [residualSq, norm_smul, he, mul_one]
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (onlineGeneratedRefreshCenteredCoordinate s.2)]
        _ = 1 := by simp [μ]
        _ = (1 : ℝ) ^ 2 := by norm_num

theorem onlineGeneratedDifference_ae_zero
    (x y : Point oldInitialBoundCounterexampleDimension) :
    (fun batch => onlineBatchDifference onlineGeneratedRefreshProblem batch 0 x y)
      =ᵐ[onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch]
      (fun _ ↦ 0) := by
  let coord := fun batch : (w : Worker onlineCoarseCounterexampleWorkers) →
      Fin onlineGeneratedDifferenceBatch.1 → OnlineGeneratedRefreshSample w ↦
    batch 0 0
  have hcoord : Measurable coord := by
    dsimp [coord]
    fun_prop
  have hmap : Measure.map coord
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch) =
      onlineGeneratedRefreshProblem.sampleLaw 0 := by
    simpa [coord] using
      (onlineBatchLaw_coordinate_marginal onlineGeneratedRefreshProblem
        (b := onlineGeneratedDifferenceBatch) 0 0)
  have hqmp : Measure.QuasiMeasurePreserving coord
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch)
      (onlineGeneratedRefreshProblem.sampleLaw 0) :=
    ⟨hcoord, by rw [hmap]⟩
  have hx := hqmp.tendsto_ae (onlineGeneratedRefresh_stochasticGradient_ae x)
  have hy := hqmp.tendsto_ae (onlineGeneratedRefresh_stochasticGradient_ae y)
  filter_upwards [hx, hy] with batch hx hy
  change stochasticGradient onlineGeneratedRefreshProblem 0 (batch 0 0) x =
    onlineGeneratedRefreshSlope (batch 0 0) •
      oldInitialBoundCounterexampleDirection at hx
  change stochasticGradient onlineGeneratedRefreshProblem 0 (batch 0 0) y =
    onlineGeneratedRefreshSlope (batch 0 0) •
      oldInitialBoundCounterexampleDirection at hy
  unfold onlineBatchDifference average SOptLib.finiteUniformAverage
  rw [Fin.sum_univ_one, hx, hy]
  simp

theorem onlineGeneratedRefresh_averageSmoothness
    {Ω : Type*} [MeasurableSpace Ω]
    (run : ℕ → Ω → State oldInitialBoundCounterexampleDimension) :
    OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
      onlineGeneratedRefreshProblem run (fun _ ↦ 0) := by
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedRefreshProblem.sampleLaw w) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedRefreshProblem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  constructor
  · intro i
    exact le_rfl
  · intro k i path
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    have hdiff := onlineGeneratedDifference_ae_zero xNext x
    have hlocal : localGradientDifference
        (onlineLocalProblem onlineGeneratedRefreshProblem) 0 xNext x = 0 := by
      unfold localGradientDifference
      rw [onlineGeneratedRefresh_localGradient 0 xNext,
        onlineGeneratedRefresh_localGradient 0 x]
      simp
    have hint : Integrable
        (fun batch => onlineBatchDifference onlineGeneratedRefreshProblem batch
          0 xNext x)
        (onlineBatchLaw onlineGeneratedRefreshProblem
          onlineGeneratedDifferenceBatch) :=
      (integrable_const (c := (0 : Point oldInitialBoundCounterexampleDimension))).congr
        hdiff.symm
    have hsqAE :
        (fun batch =>
          ‖onlineBatchDifference onlineGeneratedRefreshProblem batch 0 xNext x -
            localGradientDifference (onlineLocalProblem onlineGeneratedRefreshProblem)
              0 xNext x‖ ^ 2) =ᵐ[
          onlineBatchLaw onlineGeneratedRefreshProblem onlineGeneratedDifferenceBatch]
          (fun _ ↦ 0) := by
      filter_upwards [hdiff] with batch hb
      simp [hb, hlocal]
    have hsq : Integrable
        (fun batch =>
          ‖onlineBatchDifference onlineGeneratedRefreshProblem batch 0 xNext x -
            localGradientDifference (onlineLocalProblem onlineGeneratedRefreshProblem)
              0 xNext x‖ ^ 2)
        (onlineBatchLaw onlineGeneratedRefreshProblem
          onlineGeneratedDifferenceBatch) :=
      (integrable_const (c := (0 : ℝ))).congr hsqAE.symm
    refine ⟨hint, hsq, ?_, ?_⟩
    · rw [integral_congr_ae hdiff, hlocal]
      simp
    · rw [integral_congr_ae hsqAE]
      simp

noncomputable def onlineGeneratedIdentityQuantizer :
    Quantizer oldInitialBoundCounterexampleDimension Unit where
  apply :=
    { toFun := fun v _ ↦ v
      measurable_uncurry := measurable_fst }
  law := Measure.dirac ()
  law_isProbability := by infer_instance

theorem onlineGeneratedIdentityQuantizer_unbiased :
    IsUnbiasedQuantizer onlineGeneratedIdentityQuantizer 1 := by
  refine ⟨by norm_num, ?_⟩
  intro v
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [onlineGeneratedIdentityQuantizer] using
      (integrable_const (c := v) (Measure.dirac ()))
  · simpa [onlineGeneratedIdentityQuantizer] using
      (integrable_const (c := (0 : ℝ)) (Measure.dirac ()))
  · simp [onlineGeneratedIdentityQuantizer]
  · simp [onlineGeneratedIdentityQuantizer]

noncomputable def onlineGeneratedRefreshData :
    OnlineData oldInitialBoundCounterexampleDimension
      onlineCoarseCounterexampleWorkers OnlineGeneratedRefreshSample Unit where
  problem := onlineGeneratedRefreshProblem
  quantizer := onlineGeneratedIdentityQuantizer
  stepSize := ⟨1, by norm_num⟩
  refreshProbability := 1
  refresh_admissible := by constructor <;> norm_num

theorem onlineGeneratedRefresh_batchAdmissible :
    OnlineBatchAdmissible onlineGeneratedRefreshBatch
      onlineGeneratedDifferenceBatch := by
  norm_num [OnlineBatchAdmissible, onlineGeneratedRefreshBatch,
    onlineGeneratedDifferenceBatch]

noncomputable def onlineGeneratedRefreshInitialPoint :
    Point oldInitialBoundCounterexampleDimension :=
  (10 : ℝ) • oldInitialBoundCounterexampleDirection

@[simp] theorem onlineRun_zero {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (path : OnlinePath n b b0 Sample Ξ) :
    onlineRun A x0 hBatch 0 path = onlineInitialState A path.initial x0 := by
  rfl

@[simp] theorem onlineRun_succ {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (hBatch : OnlineBatchAdmissible b b0)
    (path : OnlinePath n b b0 Sample Ξ) :
    onlineRun A x0 hBatch (k + 1) path =
      onlineStep A (path.round k) (onlineRun A x0 hBatch k path) := by
  rfl

@[simp] theorem onlineProofExactRun_zero {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (path : ℕ → OnlineDriver n b b0 Sample Ξ) :
    onlineProofExactRun A x0 hBatch 0 path = onlineProofExactInitialState A x0 := by
  rfl

@[simp] theorem onlineProofExactRun_succ {d n b b0 : Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (hBatch : OnlineBatchAdmissible b b0)
    (path : ℕ → OnlineDriver n b b0 Sample Ξ) :
    onlineProofExactRun A x0 hBatch (k + 1) path =
      onlineStep A (path k) (onlineProofExactRun A x0 hBatch k path) := by
  rfl

theorem onlineGeneratedRefresh_proofExact_x_one
    (path : ℕ → OnlineRoundNoise onlineCoarseCounterexampleWorkers
      onlineGeneratedRefreshBatch onlineGeneratedDifferenceBatch
      OnlineGeneratedRefreshSample Unit) :
    (onlineProofExactProcess onlineGeneratedRefreshData
      onlineGeneratedRefreshInitialPoint
      onlineGeneratedRefresh_batchAdmissible 1 path).x = 0 := by
  change (onlineStep onlineGeneratedRefreshData
    (onlineDriverOfRoundNoise (path 0))
    (onlineProofExactInitialState onlineGeneratedRefreshData
      onlineGeneratedRefreshInitialPoint)).x = 0
  change onlineGeneratedRefreshInitialPoint -
      (onlineGeneratedRefreshData.stepSize : ℝ) •
        globalGradient (onlineLocalProblem onlineGeneratedRefreshData.problem)
          onlineGeneratedRefreshInitialPoint = 0
  rw [show globalGradient
      (onlineLocalProblem onlineGeneratedRefreshData.problem)
      onlineGeneratedRefreshInitialPoint =
        10 • oldInitialBoundCounterexampleDirection by
      exact onlineGeneratedRefresh_globalGradient _]
  dsimp [onlineGeneratedRefreshData, onlineGeneratedRefreshInitialPoint]
  module

/-- Legacy diagnostic package for the former fixed-query-only reading of
Assumption 3.3.  It is intentionally not a package of the reconstructed
paper-facing hypotheses: the generated sampled loss fails genuine
sampled-gradient semantics. -/
theorem onlineGeneratedRefresh_literal_assumptions :
    IsLocallySmooth
        (onlineLocalProblem onlineGeneratedRefreshData.problem) (fun _ ↦ 0) ∧
      LegacyOnlineFixedQueryUnbiasedBoundedVariance onlineGeneratedRefreshData.problem
        (fun _ ↦ 1) ∧
      IsUnbiasedQuantizer onlineGeneratedRefreshData.quantizer 1 ∧
      OnlineBatchAdmissible onlineGeneratedRefreshBatch
        onlineGeneratedDifferenceBatch ∧
      OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedRefreshData.problem
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedRefreshData onlineGeneratedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (fun _ ↦ 0) := by
  exact ⟨onlineGeneratedRefresh_isLocallySmooth,
    onlineGeneratedRefresh_literalVariance,
    onlineGeneratedIdentityQuantizer_unbiased,
    onlineGeneratedRefresh_batchAdmissible,
    onlineGeneratedRefresh_averageSmoothness _⟩

/-- Splitting an iid stream after a finite prefix preserves the canonical
product law.  The converse direction for completed measurability below is why
the generated counterexample works on the actual infinite Algorithm 3 path,
rather than only on an auxiliary two-round space. -/
theorem iidStream_prefix_tail_map_eq_prod
    {A : Type*} [MeasurableSpace A] (mu : Measure A)
    [IsProbabilityMeasure mu] (N : ℕ) :
    Measure.map
        (fun x : ℕ → A => ((fun i : Fin N => x i.1), fun k => x (N + k)))
        (SOptLib.iidStreamLaw mu) =
      (Measure.infinitePi (fun _ : Fin N => mu)).prod
        (SOptLib.iidStreamLaw mu) := by
  let P := SOptLib.iidStreamLaw mu
  let X : (ℕ → A) → (Fin N → A) := fun x i => x i.1
  let Y : (ℕ → A) → (ℕ → A) := fun x k => x (N + k)
  have hcoord : ProbabilityTheory.iIndepFun
      (fun n (x : ℕ → A) => x n) P := by
    dsimp [P, SOptLib.iidStreamLaw]
    exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
  have hX : Measurable X := by
    dsimp [X]
    fun_prop
  have hY : Measurable Y := by
    dsimp [Y]
    fun_prop
  have hXIndep : ProbabilityTheory.iIndepFun
      (fun i : Fin N => fun x : ℕ → A => x i.1) P :=
    hcoord.precomp Fin.val_injective
  have hYIndep : ProbabilityTheory.iIndepFun
      (fun k : ℕ => fun x : ℕ → A => x (N + k)) P :=
    hcoord.precomp (fun _ _ h => Nat.add_left_cancel h)
  have hXMap : Measure.map X P = Measure.infinitePi (fun _ : Fin N => mu) := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      (P := P) (X := fun i : Fin N => fun x : ℕ → A => x i.1)
      (fun _ => by fun_prop)).1 hXIndep
    simpa [X, P, SOptLib.iidStreamLaw,
      Measure.infinitePi_map_eval] using h
  have hYMap : Measure.map Y P = SOptLib.iidStreamLaw mu := by
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      (P := P) (X := fun k : ℕ => fun x : ℕ → A => x (N + k))
      (fun _ => by fun_prop)).1 hYIndep
    simpa [Y, P, SOptLib.iidStreamLaw,
      Measure.infinitePi_map_eval] using h
  let m : ℕ → MeasurableSpace (ℕ → A) := fun n =>
    MeasurableSpace.comap (fun x : ℕ → A => x n) inferInstance
  have hm_le : ∀ n, m n ≤ (inferInstance : MeasurableSpace (ℕ → A)) := by
    intro n
    exact (measurable_pi_apply n).comap_le
  have hm_indep : ProbabilityTheory.iIndep m P := by
    simpa [ProbabilityTheory.iIndepFun, ProbabilityTheory.Kernel.iIndepFun,
      m] using hcoord
  let S : Set ℕ := {n | n < N}
  have hST : Disjoint S Sᶜ := disjoint_compl_right
  have hspaces := ProbabilityTheory.indep_iSup_of_disjoint hm_le hm_indep hST
  have hX_rel : @Measurable (ℕ → A) (Fin N → A)
      (⨆ n ∈ S, m n) inferInstance X := by
    letI : MeasurableSpace (ℕ → A) := ⨆ n ∈ S, m n
    apply measurable_pi_lambda
    intro i
    rw [measurable_iff_comap_le]
    exact le_iSup_of_le i.1 (le_iSup_of_le (by simpa [S] using i.2) le_rfl)
  have hY_rel : @Measurable (ℕ → A) (ℕ → A)
      (⨆ n ∈ Sᶜ, m n) inferInstance Y := by
    letI : MeasurableSpace (ℕ → A) := ⨆ n ∈ Sᶜ, m n
    apply measurable_pi_lambda
    intro k
    rw [measurable_iff_comap_le]
    have hk : N + k ∈ Sᶜ := by simp [S]
    exact le_iSup_of_le (N + k) (le_iSup_of_le hk le_rfl)
  have hXY : ProbabilityTheory.IndepFun X Y P := by
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hspaces hX_rel.comap_le)
      hY_rel.comap_le
  have hjoint := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    hX.aemeasurable hY.aemeasurable).1 hXY
  simpa [P, X, Y, hXMap, hYMap] using hjoint

end MARINA
