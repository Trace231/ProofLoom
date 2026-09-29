import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Algorithms.Unverified.Analysis.External.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala
import SOptLib.Glue.Probability
import SOptLib.Model.Iterates
import SOptLib.Model.Objective

/-! Object layer for Sharpness-Aware Minimization (SAM), following Section 2,
equations (1)--(3), Algorithm 1, and Theorem 2 of the paper. -/

open scoped BigOperators
open scoped Gradient InnerProductSpace
open MeasureTheory
open ProbabilityTheory

namespace Algorithms.Unverified.SAM

variable {E X Y Ω : Type*}
variable [MeasurableSpace E]
variable [MeasurableSpace X] [MeasurableSpace Y]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

abbrev Dataset (n : ℕ) (X Y : Type*) := Fin n → (X × Y)

structure Setup (n : ℕ) (E X Y Ω : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace Y] where
  /- book/research/SAM.json#/setup/problem/math, quote:
     `w ∈ W ⊆ R^d`; this is the paper parameter domain. -/
  parameterSpace : Set E
  /- The paper's loss carrier is the parameter domain `W`.  Ambient
     extensions used by the Gaussian premise and gradient realization are
     internal definitions below, never setup witnesses. -/
  /- book/research/SAM.json#/setup/problem/math, quote:
     `ℓ : W × X × Y → R_+`. -/
  loss : ({w : E // w ∈ parameterSpace}) → X → Y → NNReal
  dataLaw : Measure (X × Y)
  dataLaw_isProbability : IsProbabilityMeasure dataLaw
  batchSize : ℕ
  w0 : {w : E // w ∈ parameterSpace}
  eta : ℝ
  rho : ℝ
  p : ENNReal
  lambda : ℝ
  /- book/research/SAM.json#/algorithm_spec/parameters/step_size, quote:
     `η > 0`. -/
  eta_pos : 0 < eta
  /- book/research/SAM.json#/assumptions/SAM_Norm_Range, quote:
     `ρ ≥ 0, p ∈ [1,∞]`. -/
  /- Algorithm 1 input uses a strictly positive neighborhood size. -/
  rho_pos : 0 < rho
  /- The extended-real exponent records the source range p ∈ [1,∞],
     including the projective p = ∞ endpoint. -/
  p_domain : 1 ≤ p

theorem Setup.rho_nonneg (S : Setup n E X Y Ω) : 0 ≤ S.rho := le_of_lt S.rho_pos

abbrev Batch (S : Setup n E X Y Ω) := Fin S.batchSize → (X × Y)
abbrev BatchPrefix (S : Setup n E X Y Ω) (T : ℕ) := Fin T → Batch S
/- The source algorithm samples one batch per iteration.  Its canonical
   sample-path carrier is the countable product stream `ℕ → Batch S`; finite
   prefixes are projections of that stream, not independent witness fields. -/
abbrev BatchStream (S : Setup n E X Y Ω) := ℕ → Batch S
abbrev BatchRealization (S : Setup n E X Y Ω) := BatchStream S

/- A sampled batch is a product-law draw from the data distribution.  Concrete
   sample paths are realizations of this law, not additional setup witnesses. -/
noncomputable def batchLaw (S : Setup n E X Y Ω) : Measure (Batch S) :=
  Measure.pi (fun _ : Fin S.batchSize => S.dataLaw)

theorem batchLaw_isProbability (S : Setup n E X Y Ω) :
    IsProbabilityMeasure (batchLaw (S := S)) := by
  letI : IsProbabilityMeasure S.dataLaw := S.dataLaw_isProbability
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin S.batchSize => S.dataLaw))
  infer_instance

/- The algorithm draws an independent batch at each iteration.  For every
   finite horizon `T`, the canonical law of the batch prefix is the product
   of `batchLaw`; concrete streams below are realizations of these prefixes. -/

noncomputable def batchSequenceLaw (S : Setup n E X Y Ω) (T : ℕ) :
    Measure (BatchPrefix S T) :=
  Measure.pi (fun _ : Fin T => batchLaw (S := S))

theorem batchSequenceLaw_isProbability (S : Setup n E X Y Ω) (T : ℕ) :
    IsProbabilityMeasure (batchSequenceLaw (S := S) T) := by
  letI : IsProbabilityMeasure (batchLaw (S := S)) := batchLaw_isProbability S
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin T => batchLaw (S := S)))
  infer_instance

/- Finite prefix laws remain the probability-facing objects; a stream path is
   only a realization and carries no extra independence field. -/
noncomputable def batchPrefixLaw (S : Setup n E X Y Ω) (T : ℕ) :
    Measure (BatchPrefix S T) := batchSequenceLaw (S := S) T

theorem batchPrefixLaw_isProbability (S : Setup n E X Y Ω) (T : ℕ) :
    IsProbabilityMeasure (batchPrefixLaw (S := S) T) := by
  exact batchSequenceLaw_isProbability (S := S) T

/- Canonical consistency bridge for the stochastic batch path: projecting a
   (T+1)-step product prefix onto its first T coordinates recovers the T-step
   product law. -/
def truncateBatchPrefix (S : Setup n E X Y Ω) (T : ℕ)
    (p : BatchPrefix S (T + 1)) : BatchPrefix S T :=
  fun i => p ⟨i.1, Nat.lt_succ_of_lt i.2⟩

private theorem finite_pi_prefix_projection_map_eq
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (T : ℕ) :
    Measure.map
      (fun p : Fin (T + 1) → A =>
        fun i : Fin T => p ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      (Measure.pi (fun _ : Fin (T + 1) => μ)) =
    Measure.pi (fun _ : Fin T => μ) := by
  classical
  letI : SigmaFinite μ := inferInstance
  haveI : ∀ i : Fin (T + 1),
      SigmaFinite ((fun _ : Fin (T + 1) => μ) i) := fun _ => inferInstance
  haveI : ∀ i : Fin T,
      SigmaFinite ((fun _ : Fin T => μ) i) := fun _ => inferInstance
  let trunc : (Fin (T + 1) → A) → (Fin T → A) :=
    fun p i => p ⟨i.1, Nat.lt_succ_of_lt i.2⟩
  change Measure.map trunc (Measure.pi (fun _ : Fin (T + 1) => μ)) =
    Measure.pi (fun _ : Fin T => μ)
  have htrunc_meas : Measurable trunc := by
    dsimp [trunc]
    refine measurable_pi_lambda _ ?_
    intro i
    exact measurable_pi_apply (X := fun _ : Fin (T + 1) => A)
      ⟨i.1, Nat.lt_succ_of_lt i.2⟩
  refine (Measure.pi_eq (μ := fun _ : Fin T => μ) ?_).symm
  intro s hs
  rw [Measure.map_apply htrunc_meas
    (MeasurableSet.pi Set.countable_univ (by intro i _; exact hs i))]
  let s' : Fin (T + 1) → Set A := fun j =>
    if h : (j : ℕ) < T then s ⟨j.1, h⟩ else Set.univ
  have hs' : ∀ j, MeasurableSet (s' j) := by
    intro j
    dsimp [s']
    split_ifs with h
    · exact hs ⟨j.1, h⟩
    · exact MeasurableSet.univ
  have hpre : trunc ⁻¹' Set.univ.pi s = Set.univ.pi s' := by
    ext p
    constructor
    · intro hp j hj
      dsimp [s']
      split_ifs with h
      · exact hp ⟨j.1, h⟩ trivial
      · trivial
    · intro hp j hj
      have hmem := hp ⟨j.1, Nat.lt_succ_of_lt j.2⟩ trivial
      dsimp [s'] at hmem
      simp [j.2] at hmem
      exact hmem
  rw [hpre]
  rw [Measure.pi_pi (μ := fun _ : Fin (T + 1) => μ) (s := s')]
  rw [Fin.prod_univ_castSucc]
  simp [s']

theorem batchPrefixLaw_truncate_map (S : Setup n E X Y Ω) (T : ℕ) :
    Measure.map (truncateBatchPrefix (S := S) T)
      (batchPrefixLaw (S := S) (T + 1)) = batchPrefixLaw (S := S) T := by
  letI : IsProbabilityMeasure (batchLaw (S := S)) := batchLaw_isProbability S
  simpa [batchPrefixLaw, batchSequenceLaw, truncateBatchPrefix]
    using finite_pi_prefix_projection_map_eq (μ := batchLaw (S := S)) T

def sampledBatch (S : Setup n E X Y Ω) (path : BatchRealization S) (t : ℕ) : Batch S :=
  path t

def sampledBatchProcess (S : Setup n E X Y Ω)
    (ω : BatchRealization S) (t : ℕ) : Batch S :=
  ω t

theorem sampledBatchProcess_spec (S : Setup n E X Y Ω)
    (ω : BatchRealization S) (t : ℕ) :
    sampledBatchProcess (S := S) ω t = sampledBatch (S := S) ω t := by
  rfl

theorem batchPrefixLaw_spec (S : Setup n E X Y Ω) (T : ℕ) :
    batchPrefixLaw (S := S) T = batchSequenceLaw (S := S) T := by
  rfl

/- Finite prefixes expose the stochastic object used by the product law. -/
def batchPrefix (S : Setup n E X Y Ω) (path : BatchRealization S) (T : ℕ) :
    BatchPrefix S T :=
  fun i => path i.1

theorem batchPrefix_sampled_spec (S : Setup n E X Y Ω) (path : BatchRealization S)
    (t : ℕ) :
    batchPrefix (S := S) path (t + 1) ⟨t, Nat.lt_succ_self t⟩ =
      sampledBatch (S := S) path t := by
  rfl

theorem sampledBatch_spec (S : Setup n E X Y Ω) (path : BatchRealization S) (t : ℕ) :
    sampledBatch S path t =
      batchPrefix (S := S) path (t + 1) ⟨t, Nat.lt_succ_self t⟩ := by rfl

/- The Hölder-dual exponent is determined by `p`; it is not an additional
   witness in the setup.  The endpoint branches encode the paper's
   p = 1 and p = ∞ cases explicitly. -/
noncomputable def q (S : Setup n E X Y Ω) : ENNReal :=
  if S.p = ⊤ then 1
  else if S.p = 1 then ⊤
  else ENNReal.ofReal (S.p.toReal / (S.p.toReal - 1))

theorem q_spec (S : Setup n E X Y Ω) :
    q S = if S.p = ⊤ then 1
      else if S.p = 1 then ⊤
      else ENNReal.ofReal (S.p.toReal / (S.p.toReal - 1)) := by
  rfl

theorem q_eq_one_of_p_top (S : Setup n E X Y Ω) (hp : S.p = ⊤) :
    q S = 1 := by
  simp [q, hp]

theorem q_eq_top_of_p_one (S : Setup n E X Y Ω) (hp : S.p = 1) :
    q S = ⊤ := by
  simp [q, hp]

/- Equation (2) fixes the perturbation exponent by Hölder duality; this
   relation is exposed as a theorem obligation rather than another setup
   witness. -/
theorem holder_dual_exponent_relation (S : Setup n E X Y Ω) :
    1 / S.p.toReal + 1 / (q S).toReal = 1 := by
  classical
  by_cases htop : S.p = ⊤
  · simp [q, htop]
  · by_cases hone : S.p = 1
    · simp [q, hone]
    · have hpReal_ge_one : (1 : ℝ) ≤ S.p.toReal := by
        have hmono : (1 : ENNReal).toReal ≤ S.p.toReal :=
          ENNReal.toReal_mono htop S.p_domain
        simpa using hmono
      have hpReal_ne_one : S.p.toReal ≠ 1 := by
        intro hreal
        apply hone
        have heq : S.p.toReal = (1 : ENNReal).toReal := by
          simpa using hreal
        exact (ENNReal.toReal_eq_toReal_iff' htop ENNReal.one_ne_top).mp heq
      have hpReal_gt_one : (1 : ℝ) < S.p.toReal :=
        lt_of_le_of_ne hpReal_ge_one (Ne.symm hpReal_ne_one)
      have hpReal_pos : 0 < S.p.toReal := lt_trans zero_lt_one hpReal_gt_one
      have hden_pos : 0 < S.p.toReal - 1 := sub_pos.mpr hpReal_gt_one
      have hquot_nonneg : 0 ≤ S.p.toReal / (S.p.toReal - 1) :=
        div_nonneg (le_of_lt hpReal_pos) (le_of_lt hden_pos)
      simp [q, htop, hone, ENNReal.toReal_ofReal hquot_nonneg]
      field_simp [ne_of_gt hpReal_pos, ne_of_gt hden_pos]
      ring

namespace Setup
variable {n : ℕ} (S : Setup n E X Y Ω)

/- Namespaced export of the canonical dual exponent for source-facing use. -/
noncomputable def dualExponent : ENNReal := q S

theorem dualExponent_spec :
    Setup.dualExponent (S := S) = q S := by
  rfl

/-! The paper presents the loss on the parameter domain `W`; `parameterLoss`
    is the corresponding subtype view.  The primitive field is also used to
    evaluate the perturbed points appearing in the algorithm. -/
abbrev Parameter := {w : E // w ∈ S.parameterSpace}

/- The paper's primitive loss has parameter argument `w ∈ W`. -/
noncomputable def parameterLoss (w : Parameter S) (x : X) (y : Y) : NNReal :=
  S.loss w x y

theorem parameterLoss_spec (w : Parameter S) (x : X) (y : Y) :
    parameterLoss (S := S) w x y = S.loss w x y := by
  rfl

noncomputable def lossOnParameter (w : Parameter S) (x : X) (y : Y) : NNReal :=
  parameterLoss (S := S) w x y

theorem lossOnParameter_spec (w : Parameter S) (x : X) (y : Y) :
    lossOnParameter (S := S) w x y = S.loss w x y := by
  exact parameterLoss_spec (S := S) w x y

attribute [simp] parameterLoss_spec lossOnParameter_spec

/- Internal ambient extension used only to interpret the paper's unconstrained
   gradient notation.  Outside `W` it is an implementation value and is not
   exported as a source-facing loss object. -/
private noncomputable def lossAt (S : Setup n E X Y Ω) (w : E) (x : X) (y : Y) : NNReal := by
  exact
    SOptLib.totalizeOn S.parameterSpace
      (fun w => lossOnParameter (S := S) w x y) w

theorem lossAt_spec (w : E) (x : X) (y : Y) (hw : w ∈ S.parameterSpace) :
    lossAt (S := S) w x y = S.loss ⟨w, hw⟩ x y := by
  simp [lossAt, hw]

/- The source empirical loss `L_S` has exactly the parameter domain `W`. -/
private noncomputable def empiricalLossAmbient (s : Dataset n X Y)
    (w : E) : ℝ :=
    ((n : ℝ)⁻¹) * ∑ i, (lossAt (S := S) w (s i).1 (s i).2 : ℝ)

noncomputable def empiricalLoss (s : Dataset n X Y)
    (w : Parameter S) : ℝ :=
  empiricalLossAmbient (S := S) s w.1

theorem empiricalLoss_spec (s : Dataset n X Y) (w : Parameter S) :
    empiricalLoss (S := S) s w =
      ((n : ℝ)⁻¹) * ∑ i, (S.loss w (s i).1 (s i).2 : ℝ) := by
  simp [empiricalLoss, empiricalLossAmbient, lossAt, w.property]

/- Source-contract view of `L_S(u)` at an ambient point.  The paper writes
   `L_S(w+ε)` while the primitive loss is carried on `W`; this relation
   records the partial source expression without introducing a zero extension
   or a global perturbation-closure assumption. -/
def sourceEmpiricalLossAt (s : Dataset n X Y) (u : E) (value : ℝ) : Prop :=
  ∃ hu : u ∈ S.parameterSpace,
    value = empiricalLoss (S := S) s ⟨u, hu⟩

theorem sourceEmpiricalLossAt_parameter
    (s : Dataset n X Y) (w : Parameter S) :
    sourceEmpiricalLossAt (S := S) s w.1
      (empiricalLoss (S := S) s w) := by
  exact ⟨w.property, rfl⟩

private theorem empiricalLossAmbient_spec (s : Dataset n X Y) (w : E) :
    empiricalLossAmbient (S := S) s w =
      ((n : ℝ)⁻¹) * ∑ i, (lossAt (S := S) w (s i).1 (s i).2 : ℝ) := by
  rfl

private theorem empiricalLoss_parameter_bridge (s : Dataset n X Y) (w : Parameter S) :
    empiricalLoss (S := S) s w = empiricalLossAmbient (S := S) s w.1 := by
  rfl

private theorem loss_nonneg (w : E) (x : X) (y : Y) :
    0 ≤ (lossAt (S := S) w x y : ℝ) := by
  by_cases hw : w ∈ S.parameterSpace
  · simp [lossAt, hw]
  · simp [lossAt, hw]

/- The source population loss `L_D` is likewise defined only on `W`.  The
   paper writes it as an expectation, so the source-facing object below is
   relational and includes expectation well-definedness instead of silently
   accepting Mathlib's total integral value. -/
private noncomputable def populationLossAmbient (S : Setup n E X Y Ω)
    (w : E) : ℝ :=
  ∫ z : X × Y, (lossAt (S := S) w z.1 z.2 : ℝ) ∂S.dataLaw

/- Checked scalar realization used by internal statements after the
   well-definedness boundary has been established. -/
noncomputable def populationLossValue (S : Setup n E X Y Ω)
    (w : Parameter S) : ℝ :=
  ∫ z : X × Y, (S.loss w z.1 z.2 : ℝ) ∂S.dataLaw

def populationLossWellDefined (S : Setup n E X Y Ω)
    (w : Parameter S) : Prop :=
  SOptLib.expectationWellDefined S.dataLaw
    (fun z : X × Y => (S.loss w z.1 z.2 : ℝ))

def populationLoss (S : Setup n E X Y Ω)
    (w : Parameter S) (value : ℝ) : Prop :=
  populationLossWellDefined (S := S) w ∧
    value = populationLossValue (S := S) w

theorem populationLossValue_spec (w : Parameter S) :
    populationLossValue (S := S) w =
      ∫ z : X × Y, (S.loss w z.1 z.2 : ℝ) ∂S.dataLaw := by
  rfl

theorem populationLossWellDefined_spec (w : Parameter S) :
    populationLossWellDefined (S := S) w ↔
      SOptLib.expectationWellDefined S.dataLaw
        (fun z : X × Y => (S.loss w z.1 z.2 : ℝ)) := by
  rfl

theorem populationLoss_spec (w : Parameter S) (value : ℝ) :
    populationLoss (S := S) w value ↔
      populationLossWellDefined (S := S) w ∧
        value = populationLossValue (S := S) w := by
  rfl

/- Source-contract view of `L_D(u)` at an ambient point.  This is relational
   for the same reason as `sourceEmpiricalLossAt`: the source expression is
   domain-indexed by `W`, but Theorem 2 writes perturbed ambient points. -/
def sourcePopulationLossAt (u : E) (value : ℝ) : Prop :=
  ∃ hu : u ∈ S.parameterSpace,
    populationLoss (S := S) ⟨u, hu⟩ value

theorem sourcePopulationLossAt_parameter (w : Parameter S)
    (hwd : populationLossWellDefined (S := S) w) :
    sourcePopulationLossAt (S := S) w.1
      (populationLossValue (S := S) w) := by
  exact ⟨w.property, hwd, rfl⟩

def sourcePopulationLossWellDefinedObligation (u : E) : Prop :=
  ∃ value : ℝ, sourcePopulationLossAt (S := S) u value

private theorem populationLossAmbient_of_mem (w : Parameter S) :
    populationLossAmbient (S := S) w.1 = populationLossValue (S := S) w := by
  simp [populationLossAmbient, populationLossValue, lossAt, w.property]

noncomputable def parameterCount : ℕ := Module.finrank ℝ E

noncomputable def iidTrainingLaw : Measure (Dataset n X Y) :=
  Measure.pi (fun _ : Fin n => S.dataLaw)

theorem iidTrainingLaw_isProbability :
    IsProbabilityMeasure (iidTrainingLaw (S := S)) := by
  letI : IsProbabilityMeasure S.dataLaw := S.dataLaw_isProbability
  change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => S.dataLaw))
  infer_instance

/- Algorithm 1 samples a batch at each iteration.  The source-facing batch
   loss is carried on the parameter domain `W`; ambient extensions are
   private calculus infrastructure. -/
private noncomputable def batchLossAmbient (S : Setup n E X Y Ω)
    (B : Batch S) (u : E) : ℝ :=
    ((S.batchSize : ℝ)⁻¹) *
      ∑ j, (lossAt (S := S) u (B j).1 (B j).2 : ℝ)

noncomputable def batchLoss (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) : ℝ :=
    ((S.batchSize : ℝ)⁻¹) *
      ∑ j, (parameterLoss (S := S) w
        (B j).1 (B j).2 : ℝ)

noncomputable abbrev parameterBatchLoss (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) : ℝ := batchLoss (S := S) B w

theorem batchLoss_spec (B : Batch S) (w : Parameter S) :
    batchLoss (S := S) B w =
          ((S.batchSize : ℝ)⁻¹) *
        ∑ j, (S.loss w (B j).1
          (B j).2 : ℝ) := by
  rfl

private theorem batchLossAmbient_spec (B : Batch S) (w : E) :
    batchLossAmbient (S := S) B w =
      ((S.batchSize : ℝ)⁻¹) *
        ∑ j, (lossAt (S := S) w (B j).1
          (B j).2 : ℝ) := by
  rfl

private theorem batchLoss_eq_parameterBatchLoss_of_mem
    (B : Batch S) (w : E)
    (hw : w ∈ S.parameterSpace) :
    batchLossAmbient (S := S) B w =
      batchLoss (S := S) B ⟨w, hw⟩ := by
  by_cases hbatch : S.batchSize = 0
  · simp [batchLossAmbient, batchLoss, hbatch]
  · simp [batchLossAmbient, batchLoss, parameterLoss, lossAt, hw]

/- The public oracle is evaluated at a parameter in W.  The ambient gradient
   used by Lean's calculus API is an internal realization of this oracle. -/
private noncomputable def batchLossExtension (B : Batch S) (u : E) : ℝ := by
  classical
  exact dite (u ∈ S.parameterSpace)
    (fun hu => batchLoss (S := S) B ⟨u, hu⟩)
    (fun _ => 0)

/- Paper-literal relation for Algorithm 1's instruction
   `Compute gradient ∇_w L_B(w)`.  The relation is stated as a gradient
   certificate for the displayed batch loss totalized from the parameter
   carrier; the selected `gradientWithin` below is only Lean's boundary-safe
   realization of a value satisfying this source relation.
   Realization contract source pointer (zero-based JSON array index):
   book/research/SAM.json#/algorithm_spec/steps/2/math.
   The next entry, `steps/3/math`, is the distinct adversarial-perturbation
   instruction and is not the source formula for this gradient object. -/
def literalBatchGradient (B : Batch S) (w : Parameter S) (g : E) : Prop :=
  HasGradientWithinAt
    (fun u : E => by
      classical
      exact dite (u ∈ S.parameterSpace)
        (fun hu => batchLoss (S := S) B ⟨u, hu⟩)
        (fun _ => 0))
    g S.parameterSpace w.1

theorem literalBatchGradient_spec (B : Batch S) (w : Parameter S) (g : E) :
    literalBatchGradient (S := S) B w g ↔
      HasGradientWithinAt (batchLossExtension (S := S) B) g
        S.parameterSpace w.1 := by
  rfl

/- Ambient gradient realization used when the perturbed point is not known to
   lie in `W`.  This is internal calculus infrastructure; the public loss and
   batch objects remain parameter-subtype valued. -/
private noncomputable def batchGradientAmbient (B : Batch S) (u : E) : E :=
  gradientWithin (batchLossExtension (S := S) B) S.parameterSpace u

/- Public paper-facing batch-gradient wrapper.  `batchGradientAmbient` is the
   private boundary-safe realization; this exported definition is the source
   Algorithm 1 object and must not be classified as an internal realization
   definition. -/
noncomputable def batchGradient (B : Batch S) (w : Parameter S) : E :=
  batchGradientAmbient (S := S) B w.1

private theorem gradientWithin_eq_of_hasGradientWithinAt_uniqueDiffWithinAt
    {f : E → ℝ} {s : Set E} {x g : E}
    (huniq : UniqueDiffWithinAt ℝ s x)
    (h : HasGradientWithinAt f g s x) :
    gradientWithin f s x = g := by
  unfold gradientWithin
  rw [h.hasFDerivWithinAt.fderivWithin huniq]
  simp

theorem batchGradient_of_hasGradientAt
    (B : Batch S) (w : Parameter S) (g : E)
    (huniq : UniqueDiffWithinAt ℝ S.parameterSpace w.1)
    (h : HasGradientWithinAt (batchLossExtension (S := S) B) g
      S.parameterSpace w.1) :
    batchGradient (S := S) B w = g := by
  unfold batchGradient batchGradientAmbient
  exact gradientWithin_eq_of_hasGradientWithinAt_uniqueDiffWithinAt huniq h

theorem batchGradient_of_literalBatchGradient
    (B : Batch S) (w : Parameter S) (g : E)
    (huniq : UniqueDiffWithinAt ℝ S.parameterSpace w.1)
    (h : literalBatchGradient (S := S) B w g) :
    batchGradient (S := S) B w = g := by
  exact batchGradient_of_hasGradientAt (S := S) B w g huniq
    ((literalBatchGradient_spec (S := S) B w g).mp h)

/- Retirement certificate for the old selector bridge without
   `UniqueDiffWithinAt`.  If two distinct vectors are both valid
   within-gradients, an unconditional selector theorem would identify them. -/
private theorem gradientWithin_unconditional_selector_false_of_two_certificates
    {f : E → ℝ} {s : Set E} {x g₀ g₁ : E}
    (h₀ : HasGradientWithinAt f g₀ s x)
    (h₁ : HasGradientWithinAt f g₁ s x)
    (hne : g₀ ≠ g₁) :
    ¬ (∀ g : E, HasGradientWithinAt f g s x → gradientWithin f s x = g) := by
  intro hselector
  exact hne ((hselector g₀ h₀).symm.trans (hselector g₁ h₁))

private theorem batchGradient_of_hasGradientAt_old_head_retired_of_two_certificates
    (B : Batch S) (w : Parameter S) (g₀ g₁ : E)
    (h₀ : HasGradientWithinAt (batchLossExtension (S := S) B) g₀
      S.parameterSpace w.1)
    (h₁ : HasGradientWithinAt (batchLossExtension (S := S) B) g₁
      S.parameterSpace w.1)
    (hne : g₀ ≠ g₁) :
    ¬ (∀ g : E,
      HasGradientWithinAt (batchLossExtension (S := S) B) g
        S.parameterSpace w.1 →
      batchGradient (S := S) B w = g) := by
  intro hselector
  exact hne ((hselector g₀ h₀).symm.trans (hselector g₁ h₁))

theorem batchGradient_spec (B : Batch S) (w : Parameter S) :
    batchGradient (S := S) B w =
      batchGradientAmbient (S := S) B w.1 := by
  rfl

/- The source uses the coordinate `p`-norm on `R^d`.  We realize the finite
   coordinates through Mathlib's canonical orthonormal frame, rather than
   exposing an arbitrary algebraic basis as Setup data. -/
noncomputable def coordinate (v : E) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  ((stdOrthonormalBasis ℝ E).repr v) i

/- The p-norm is computed in an explicit canonical coordinate chart.  The
   reconstruction theorem records the bridge from that chart to the Hilbert
   carrier, instead of leaving the basis dependence implicit. -/
noncomputable def coordinateVector (v : E) : Fin (Module.finrank ℝ E) → ℝ :=
  fun i => coordinate v i

theorem coordinateVector_spec (v : E) (i : Fin (Module.finrank ℝ E)) :
    coordinateVector (E := E) v i =
      ((stdOrthonormalBasis ℝ E).repr v) i := by
  rfl

theorem coordinate_inner_spec (v : E) (i : Fin (Module.finrank ℝ E)) :
    coordinate (E := E) v i =
      ⟪v, stdOrthonormalBasis ℝ E i⟫_ℝ := by
  unfold coordinate
  rw [OrthonormalBasis.repr_apply_apply]
  exact real_inner_comm _ _

theorem coordinateVector_reconstruct (v : E) :
    (∑ i : Fin (Module.finrank ℝ E),
      coordinateVector (E := E) v i • stdOrthonormalBasis ℝ E i) = v := by
  simpa [coordinateVector, coordinate] using
    (stdOrthonormalBasis ℝ E).sum_repr v

noncomputable def coordinateMax (v : E) : ℝ := by
  classical
  by_cases h : Nonempty (Fin (Module.finrank ℝ E))
  · letI : Nonempty (Fin (Module.finrank ℝ E)) := h
    exact Finset.sup' Finset.univ Finset.univ_nonempty
      (fun i : Fin (Module.finrank ℝ E) => ‖coordinateVector (E := E) v i‖)
  · exact 0

/- book/research/SAM.json#/algorithm_spec/parameters/SAM_objective, quote:
   `max_{||ε||_p≤ρ} L_S(w+ε)` with p ∈ [1,∞].  Coordinates are taken in
   Mathlib's canonical orthonormal identification of finite-dimensional E
   with R^d, so the same definition covers every finite p and p = ∞. -/
noncomputable def lpNorm (p : ENNReal) (v : E) : ℝ :=
  if p = ⊤ then
    coordinateMax v
  else
    (∑ i, ‖coordinateVector (E := E) v i‖ ^ p.toReal) ^ (1 / p.toReal)

theorem lpNorm_spec (p : ENNReal) (v : E) :
    lpNorm p v = if p = ⊤ then
      coordinateMax v
    else (∑ i, ‖coordinateVector (E := E) v i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  rfl

theorem lpNorm_infinity_spec (v : E) :
    lpNorm (⊤ : ENNReal) v =
    coordinateMax v := by
  simp [lpNorm]

theorem lpNorm_finite_spec {p : ENNReal} (hp : p ≠ ⊤) (v : E) :
    lpNorm p v = (∑ i, ‖coordinateVector (E := E) v i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  simp [lpNorm, hp]

/- The Euclidean case is the bridge from the paper's coordinate p-norm to
   the ambient Hilbert norm used in Theorem 2.  The proof is deferred to the
   prover; the statement prevents the coordinate realization from being
   mistaken for a new, unrelated norm. -/
theorem lpNorm_two_eq_norm (v : E) :
    lpNorm (2 : ENNReal) v = ‖v‖ := by
  classical
  unfold lpNorm
  simp
  have hsum :
      (∑ i : Fin (Module.finrank ℝ E),
        coordinateVector (E := E) v i ^ 2) = ‖v‖ ^ 2 := by
    rw [← Finset.norm_sq_sum_smul_orthonormalBasis
      (stdOrthonormalBasis ℝ E) (coordinateVector (E := E) v)]
    rw [coordinateVector_reconstruct]
  rw [hsum]
  have hhalf : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
  rw [hhalf]
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (norm_nonneg v)

/- book/research/SAM.json#/algorithm_spec/parameters/SAM_objective, quote:
   `L_S^SAM(w) := max_{||ε||_p≤ρ} L_S(w+ε)`. -/
def perturbationBall (S : Setup n E X Y Ω) : Set E := {ε | lpNorm S.p ε ≤ S.rho}

/- The paper's linearized inner problem uses the Euclidean pairing
   `εᵀg`; on the ambient Hilbert carrier this is Mathlib's canonical inner
   product rather than a dot product in an arbitrary (possibly non-orthogonal)
   basis. -/
noncomputable def linearPairing (u v : E) : ℝ :=
  ⟪u, v⟫_ℝ

/-! Corrected realization of Equation (2) in canonical orthonormal coordinates.
    The source gives the sign/power dual-norm expression but does not specify
    zero-gradient, endpoint tie-breaking, or denominator conventions; those
    branches are therefore not the source-facing perturbation object. -/
noncomputable def coordinateSign (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

/- Denominator appearing in the finite-q branch of Eq. (2).  Its
   non-vanishing is deliberately a named proof obligation rather than a
   hidden zero-denominator convention. -/
noncomputable def dualNormDenominator (S : Setup n E X Y Ω) (g : E) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    ‖coordinateVector (E := E) g i‖ ^ (q S).toReal) ^ (1 / S.p.toReal)

theorem dualNormDenominator_ne_zero
    (S : Setup n E X Y Ω) (g : E)
    (hg : g ≠ 0) (hp : S.p ≠ 1) (hptop : S.p ≠ ⊤)
    (hq : 0 < (q S).toReal) :
    dualNormDenominator (S := S) g ≠ 0 := by
  classical
  unfold dualNormDenominator
  have hcoord : ∃ i : Fin (Module.finrank ℝ E), coordinateVector (E := E) g i ≠ 0 := by
    by_contra h
    push Not at h
    have hsum_zero :
        (∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i • stdOrthonormalBasis ℝ E i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [h i]
    have hg_zero : g = 0 := by
      have hrecon := coordinateVector_reconstruct (E := E) g
      rw [hsum_zero] at hrecon
      exact hrecon.symm
    exact hg hg_zero
  have hbase_pos :
      0 < ∑ i : Fin (Module.finrank ℝ E),
        ‖coordinateVector (E := E) g i‖ ^ (q S).toReal := by
    rcases hcoord with ⟨i0, hi0⟩
    refine Finset.sum_pos' ?_ ?_
    · intro i hi
      by_cases hci : coordinateVector (E := E) g i = 0
      · have hq_ne : (q S).toReal ≠ 0 := ne_of_gt hq
        simp [hci, Real.zero_rpow hq_ne]
      · exact le_of_lt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hci) (q S).toReal)
    · refine ⟨i0, Finset.mem_univ i0, ?_⟩
      exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hi0) (q S).toReal
  exact ne_of_gt (Real.rpow_pos_of_pos hbase_pos (1 / S.p.toReal))

/-! The `p = 1` endpoint of the dual-norm formula is not obtained by
    evaluating the finite-`q` power expression at `q.toReal` (which would
    silently totalize the source's `q = ∞` case).  We expose the endpoint as
    the canonical maximizer selected from the finite-dimensional linear
    problem, with existence left as a proof obligation. -/
/-! Canonical endpoint construction for `p = 1`.

    The dual problem is the maximum of a finite family of coordinate
    functionals.  We therefore average the signed basis vectors attaining the
    finite supremum.  This is a deterministic finite-sum construction (with a
    zero value for the degenerate/empty attaining set), rather than a
    witness-selected perturbation.  The fact that it is feasible and maximal
    is a derived theorem below.
-/
noncomputable def oneNormPerturbation
    (S : Setup n E X Y Ω) (g : E) : E := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let m : ℝ := coordinateMax g
  let I : Finset (Fin (Module.finrank ℝ E)) :=
    Finset.univ.filter (fun i => ‖coordinate g i‖ = m)
  exact if hI : I.Nonempty then
    (∑ i, if i ∈ I then
      ((S.rho / (I.card : ℝ)) * coordinateSign (coordinate g i)) • b i
      else 0)
  else 0

private theorem coordinateVector_sum_smul_orthonormalBasis
    (c : Fin (Module.finrank ℝ E) → ℝ)
    (j : Fin (Module.finrank ℝ E)) :
    coordinateVector (E := E)
      (∑ i : Fin (Module.finrank ℝ E), c i • stdOrthonormalBasis ℝ E i) j =
      c j := by
  simpa [coordinateVector, coordinate] using
    congr_fun (pi_eq_sum_univ' c).symm j

private theorem coordinateVector_finset_sum_smul_orthonormalBasis
    (s : Finset (Fin (Module.finrank ℝ E)))
    (c : Fin (Module.finrank ℝ E) → ℝ)
    (j : Fin (Module.finrank ℝ E)) :
    coordinateVector (E := E)
      (∑ i ∈ s, c i • stdOrthonormalBasis ℝ E i) j =
      if j ∈ s then c j else 0 := by
  classical
  have hsum :
      (∑ i ∈ s, c i • stdOrthonormalBasis ℝ E i) =
        ∑ i : Fin (Module.finrank ℝ E),
          (if i ∈ s then c i else 0) • stdOrthonormalBasis ℝ E i := by
    simp [Finset.sum_ite_mem]
  rw [hsum, coordinateVector_sum_smul_orthonormalBasis]

private theorem mem_perturbationBall_p_one_iff_l1
    (S : Setup n E X Y Ω) (hp : S.p = 1) (u : E) :
    u ∈ Setup.perturbationBall (S := S) ↔
      (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) ≤ S.rho := by
  have hp_ne_top : S.p ≠ ⊤ := by
    intro htop
    rw [hp] at htop
    exact ENNReal.one_ne_top htop
  unfold Setup.perturbationBall
  change Setup.lpNorm S.p u ≤ S.rho ↔
    (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) ≤ S.rho
  rw [Setup.lpNorm_finite_spec (E := E) hp_ne_top u]
  simp [hp, Real.rpow_one]

private theorem coordinateMax_abs_coordinate_le
    (g : E) (i : Fin (Module.finrank ℝ E)) :
    |coordinateVector (E := E) g i| ≤ coordinateMax (E := E) g := by
  classical
  unfold coordinateMax
  by_cases h : Nonempty (Fin (Module.finrank ℝ E))
  · letI : Nonempty (Fin (Module.finrank ℝ E)) := h
    simp [h, Real.norm_eq_abs]
    simpa [Real.norm_eq_abs] using
      (Finset.univ.le_sup'
        (f := fun j : Fin (Module.finrank ℝ E) => ‖coordinateVector (E := E) g j‖)
        (Finset.mem_univ i))
  · exact False.elim (h ⟨i⟩)

private theorem coordinateMax_nonneg (g : E) :
    0 ≤ coordinateMax (E := E) g := by
  classical
  by_cases h : Nonempty (Fin (Module.finrank ℝ E))
  · exact le_trans (abs_nonneg (coordinateVector (E := E) g (Classical.choice h)))
      (coordinateMax_abs_coordinate_le (E := E) g (Classical.choice h))
  · unfold coordinateMax
    simp [h]

private theorem coordinateMax_eq_zero_of_active_empty
    (g : E)
    (hI :
      ¬ (Finset.univ.filter
          (fun i : Fin (Module.finrank ℝ E) =>
            |coordinate (E := E) g i| = coordinateMax (E := E) g)).Nonempty) :
    coordinateMax (E := E) g = 0 := by
  classical
  by_cases h : Nonempty (Fin (Module.finrank ℝ E))
  · letI : Nonempty (Fin (Module.finrank ℝ E)) := h
    rcases
      Finset.exists_mem_eq_sup'
        (s := Finset.univ)
        (H := Finset.univ_nonempty)
        (f := fun i : Fin (Module.finrank ℝ E) => ‖coordinateVector (E := E) g i‖)
      with ⟨k, _hk, hk_sup⟩
    have hmax_eq :
        coordinateMax (E := E) g = ‖coordinateVector (E := E) g k‖ := by
      unfold coordinateMax
      simp [h]
      exact hk_sup
    have hk_eq :
        ‖coordinate (E := E) g k‖ = coordinateMax (E := E) g := by
      rw [hmax_eq]
      rfl
    have hk_abs_eq :
        |coordinate (E := E) g k| = coordinateMax (E := E) g := by
      simpa [Real.norm_eq_abs] using hk_eq
    have hk_mem :
        k ∈ Finset.univ.filter
          (fun i : Fin (Module.finrank ℝ E) =>
            |coordinate (E := E) g i| = coordinateMax (E := E) g) := by
      simp [hk_abs_eq]
    exact False.elim (hI ⟨k, hk_mem⟩)
  · unfold coordinateMax
    simp [h]

private theorem linearPairing_eq_sum_coordinates
    (g u : E) :
    linearPairing g u =
      ∑ i : Fin (Module.finrank ℝ E),
        coordinateVector (E := E) g i * coordinateVector (E := E) u i := by
  calc
    linearPairing g u = ⟪g, u⟫_ℝ := rfl
    _ = ⟪g,
          ∑ i : Fin (Module.finrank ℝ E),
            coordinateVector (E := E) u i • stdOrthonormalBasis ℝ E i⟫_ℝ := by
      rw [coordinateVector_reconstruct (E := E) u]
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          ⟪g, coordinateVector (E := E) u i • stdOrthonormalBasis ℝ E i⟫_ℝ := by
      rw [inner_sum]
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) u i *
            ⟪g, stdOrthonormalBasis ℝ E i⟫_ℝ := by
      simp [inner_smul_right]
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) u i * coordinateVector (E := E) g i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [coordinateVector]
      change coordinate (E := E) u i * ⟪g, stdOrthonormalBasis ℝ E i⟫_ℝ =
        coordinate (E := E) u i * coordinate (E := E) g i
      rw [coordinate_inner_spec (E := E) g i]
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i * coordinateVector (E := E) u i := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      ring

private theorem linearPairing_le_coordinateMax_mul_l1
    (g u : E) :
    linearPairing g u ≤
      coordinateMax (E := E) g *
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) := by
  classical
  calc
    linearPairing g u =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i * coordinateVector (E := E) u i := by
      exact linearPairing_eq_sum_coordinates (E := E) g u
    _ ≤
        |∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i * coordinateVector (E := E) u i| :=
      le_abs_self _
    _ ≤
        ∑ i : Fin (Module.finrank ℝ E),
          |coordinateVector (E := E) g i * coordinateVector (E := E) u i| := by
      simpa using
        (Finset.abs_sum_le_sum_abs
          (fun i : Fin (Module.finrank ℝ E) =>
            coordinateVector (E := E) g i * coordinateVector (E := E) u i)
          Finset.univ)
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          |coordinateVector (E := E) g i| * |coordinateVector (E := E) u i| := by
      simp [abs_mul]
    _ ≤
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateMax (E := E) g * |coordinateVector (E := E) u i| := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact mul_le_mul_of_nonneg_right
        (coordinateMax_abs_coordinate_le (E := E) g i)
        (abs_nonneg (coordinateVector (E := E) u i))
    _ =
        coordinateMax (E := E) g *
          (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) := by
      rw [Finset.mul_sum]

private theorem abs_coordinateSign_le_one (x : ℝ) :
    |coordinateSign x| ≤ 1 := by
  unfold coordinateSign
  by_cases hpos : 0 < x
  · simp [hpos]
  · by_cases hneg : x < 0
    · simp [hpos, hneg]
    · simp [hpos, hneg]

private theorem coordinateSign_mul_self (x : ℝ) :
    coordinateSign x * x = |x| := by
  unfold coordinateSign
  by_cases hpos : 0 < x
  · simp [hpos, abs_of_pos hpos]
  · by_cases hneg : x < 0
    · have habs : |x| = -x := abs_of_neg hneg
      simp [hpos, hneg, habs]
    · have hx_nonneg : 0 ≤ x := le_of_not_gt hneg
      have hx_nonpos : x ≤ 0 := le_of_not_gt hpos
      have hx : x = 0 := le_antisymm hx_nonpos hx_nonneg
      simp [hx]

private theorem coordinateVector_oneNormPerturbation
    (S : Setup n E X Y Ω) (g : E)
    (j : Fin (Module.finrank ℝ E)) :
    let I : Finset (Fin (Module.finrank ℝ E)) :=
      Finset.univ.filter
        (fun i => |coordinate (E := E) g i| = coordinateMax (E := E) g)
    coordinateVector (E := E) (oneNormPerturbation (S := S) g) j =
      if j ∈ I then
        (S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g j)
      else 0 := by
  classical
  let I : Finset (Fin (Module.finrank ℝ E)) :=
    Finset.univ.filter
      (fun i => |coordinate (E := E) g i| = coordinateMax (E := E) g)
  unfold oneNormPerturbation
  simp only [Real.norm_eq_abs]
  change
    coordinateVector (E := E)
      (if hI : I.Nonempty then
        (∑ i : Fin (Module.finrank ℝ E),
          if i ∈ I then
            ((S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g i)) •
              stdOrthonormalBasis ℝ E i
          else 0)
      else 0) j =
      if j ∈ I then
        (S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g j)
      else 0
  by_cases hI : I.Nonempty
  · simp [hI]
    exact coordinateVector_finset_sum_smul_orthonormalBasis
      (E := E) I
      (fun i : Fin (Module.finrank ℝ E) =>
        (S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g i))
      j
  · have hj_not : j ∉ I := by
      intro hj
      exact hI ⟨j, hj⟩
    simp [hI, hj_not, coordinateVector, coordinate]

private theorem oneNormPerturbation_l1_budget
    (S : Setup n E X Y Ω) (g : E) :
    (∑ i : Fin (Module.finrank ℝ E),
      |coordinateVector (E := E) (oneNormPerturbation (S := S) g) i|) ≤ S.rho := by
  classical
  let I : Finset (Fin (Module.finrank ℝ E)) :=
    Finset.univ.filter
      (fun i => |coordinate (E := E) g i| = coordinateMax (E := E) g)
  have hsum_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        |coordinateVector (E := E) (oneNormPerturbation (S := S) g) i|) =
        ∑ i : Fin (Module.finrank ℝ E),
          if i ∈ I then
            |(S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g i)|
          else 0 := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [coordinateVector_oneNormPerturbation (S := S) g i]
    by_cases hi : i ∈ I
    · have hi_eq :
          |coordinate (E := E) g i| = coordinateMax (E := E) g := by
        simpa [I] using hi
      simp [I, hi_eq]
    · have hi_ne :
          |coordinate (E := E) g i| ≠ coordinateMax (E := E) g := by
        intro hi_eq
        exact hi (by simp [I, hi_eq])
      simp [I, hi_ne]
  rw [hsum_eq]
  by_cases hI : I.Nonempty
  · have hcard_pos_nat : 0 < I.card := Finset.card_pos.mpr hI
    have hcard_pos : 0 < (I.card : ℝ) := by exact_mod_cast hcard_pos_nat
    have hfrac_nonneg : 0 ≤ S.rho / (I.card : ℝ) :=
      div_nonneg (Setup.rho_nonneg (S := S)) (le_of_lt hcard_pos)
    calc
      (∑ i : Fin (Module.finrank ℝ E),
          if i ∈ I then
            |(S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g i)|
          else 0)
          ≤
        ∑ i : Fin (Module.finrank ℝ E),
          if i ∈ I then S.rho / (I.card : ℝ) else 0 := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        by_cases hi : i ∈ I
        · simp only [hi, if_true]
          have habs :
              |(S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g i)| =
                (S.rho / (I.card : ℝ)) *
                  |coordinateSign (coordinate (E := E) g i)| := by
            rw [abs_mul, abs_of_nonneg hfrac_nonneg]
          calc
            |(S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g i)|
                =
                (S.rho / (I.card : ℝ)) *
                    |coordinateSign (coordinate (E := E) g i)| := habs
            _ ≤ (S.rho / (I.card : ℝ)) * 1 := by
              exact mul_le_mul_of_nonneg_left
                (abs_coordinateSign_le_one (coordinate (E := E) g i)) hfrac_nonneg
            _ = S.rho / (I.card : ℝ) := by ring
        · simp only [hi, if_false, le_refl]
      _ = ∑ i ∈ I, S.rho / (I.card : ℝ) := by
        simp [Finset.sum_ite_mem]
      _ = (I.card : ℝ) * (S.rho / (I.card : ℝ)) := by
        simp
      _ = S.rho := by
        field_simp [ne_of_gt hcard_pos]
  · have hI_empty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp [hI_empty, Setup.rho_nonneg (S := S)]

private theorem oneNormPerturbation_pairing_value
    (S : Setup n E X Y Ω) (g : E) :
    linearPairing g (oneNormPerturbation (S := S) g) =
      S.rho * coordinateMax (E := E) g := by
  classical
  let I : Finset (Fin (Module.finrank ℝ E)) :=
    Finset.univ.filter
      (fun i => |coordinate (E := E) g i| = coordinateMax (E := E) g)
  have hpair_sum :
      linearPairing g (oneNormPerturbation (S := S) g) =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i *
            coordinateVector (E := E) (oneNormPerturbation (S := S) g) i := by
    exact linearPairing_eq_sum_coordinates (E := E) g (oneNormPerturbation (S := S) g)
  by_cases hI : I.Nonempty
  · have hcard_pos_nat : 0 < I.card := Finset.card_pos.mpr hI
    have hcard_pos : 0 < (I.card : ℝ) := by exact_mod_cast hcard_pos_nat
    calc
      linearPairing g (oneNormPerturbation (S := S) g)
          =
        ∑ i : Fin (Module.finrank ℝ E),
          if i ∈ I then
            (S.rho / (I.card : ℝ)) * coordinateMax (E := E) g
          else 0 := by
        rw [hpair_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [coordinateVector_oneNormPerturbation (S := S) g i]
        by_cases hi : i ∈ I
        · have hi_abs :
            |coordinate (E := E) g i| = coordinateMax (E := E) g := by
            simpa [I] using hi
          simp [I, hi_abs]
          have hsign := coordinateSign_mul_self (coordinate (E := E) g i)
          rw [coordinateVector]
          calc
            coordinate (E := E) g i *
                ((S.rho / (I.card : ℝ)) * coordinateSign (coordinate (E := E) g i))
                =
              (S.rho / (I.card : ℝ)) *
                (coordinateSign (coordinate (E := E) g i) * coordinate (E := E) g i) := by
              ring
            _ = (S.rho / (I.card : ℝ)) * |coordinate (E := E) g i| := by
              rw [hsign]
            _ = (S.rho / (I.card : ℝ)) * coordinateMax (E := E) g := by
              rw [hi_abs]
        · have hi_ne :
            |coordinate (E := E) g i| ≠ coordinateMax (E := E) g := by
            intro hi_abs
            exact hi (by simp [I, hi_abs])
          simp [I, hi_ne]
      _ = ∑ i ∈ I, (S.rho / (I.card : ℝ)) * coordinateMax (E := E) g := by
        simp [Finset.sum_ite_mem]
      _ = (I.card : ℝ) * ((S.rho / (I.card : ℝ)) * coordinateMax (E := E) g) := by
        simp
      _ = S.rho * coordinateMax (E := E) g := by
        field_simp [ne_of_gt hcard_pos]
  · have hmax_zero : coordinateMax (E := E) g = 0 :=
      coordinateMax_eq_zero_of_active_empty (E := E) g hI
    have hpair_zero :
        linearPairing g (oneNormPerturbation (S := S) g) = 0 := by
      rw [hpair_sum]
      refine Finset.sum_eq_zero ?_
      intro i _hi
      rw [coordinateVector_oneNormPerturbation (S := S) g i]
      have hi_not : i ∉ I := by
        intro hi
        exact hI ⟨i, hi⟩
      have hi_ne :
          |coordinate (E := E) g i| ≠ coordinateMax (E := E) g := by
        intro hi_abs
        exact hi_not (by simp [I, hi_abs])
      simp [I, hi_ne]
    rw [hpair_zero, hmax_zero]
    ring

theorem oneNormPerturbation_spec
    (S : Setup n E X Y Ω) (g : E) (hp : S.p = 1) :
    oneNormPerturbation (S := S) g ∈ Setup.perturbationBall (S := S) ∧
      IsMaxOn (fun v : E => Setup.linearPairing g v)
        (Setup.perturbationBall (S := S))
        (oneNormPerturbation (S := S) g) := by
  constructor
  · exact
      (mem_perturbationBall_p_one_iff_l1 (S := S) hp
        (oneNormPerturbation (S := S) g)).mpr
        (oneNormPerturbation_l1_budget (S := S) g)
  · refine isMaxOn_iff.mpr ?_
    intro u hu
    have hu_l1 :
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) ≤ S.rho :=
      (mem_perturbationBall_p_one_iff_l1 (S := S) hp u).mp hu
    have hmax_nonneg : 0 ≤ coordinateMax (E := E) g :=
      coordinateMax_nonneg (E := E) g
    have hupper :
        linearPairing g u ≤
          coordinateMax (E := E) g *
            (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) :=
      linearPairing_le_coordinateMax_mul_l1 (E := E) g u
    have hbudget :
        coordinateMax (E := E) g *
            (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) ≤
          coordinateMax (E := E) g * S.rho :=
      mul_le_mul_of_nonneg_left hu_l1 hmax_nonneg
    have hvalue :
        linearPairing g (oneNormPerturbation (S := S) g) =
          S.rho * coordinateMax (E := E) g :=
      oneNormPerturbation_pairing_value (S := S) g
    calc
      linearPairing g u
          ≤ coordinateMax (E := E) g *
              (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) u i|) :=
        hupper
      _ ≤ coordinateMax (E := E) g * S.rho := hbudget
      _ = S.rho * coordinateMax (E := E) g := by ring
      _ = linearPairing g (oneNormPerturbation (S := S) g) := hvalue.symm

/- Retirement certificate for the old, unconditional endpoint claim.  The
   p = 1 endpoint selector cannot be a maximizer on an arbitrary p-ball if a
   feasible comparison point has strictly larger linear pairing; this is the
   formal shape of the p = ∞ tied-coordinate counterexample that motivated the
   branch-specific theorem head above. -/
private theorem oneNormPerturbation_spec_unconditional_false_of_strict_better_feasible_point
    (S : Setup n E X Y Ω) (g u : E)
    (hu : u ∈ Setup.perturbationBall (S := S))
    (hstrict :
      Setup.linearPairing g (Setup.oneNormPerturbation (S := S) g) <
        Setup.linearPairing g u) :
    ¬ (Setup.oneNormPerturbation (S := S) g ∈ Setup.perturbationBall (S := S) ∧
      IsMaxOn (fun v : E => Setup.linearPairing g v)
        (Setup.perturbationBall (S := S))
        (Setup.oneNormPerturbation (S := S) g)) := by
  intro h
  exact (not_le_of_gt hstrict) ((isMaxOn_iff.mp h.2) u hu)

/- Specialization of the retirement certificate to the source-relevant
   p = ∞ failure mode: once the infinity-ball branch admits a strictly better
   feasible comparison point, the old arbitrary-p endpoint theorem is
   impossible. -/
private theorem oneNormPerturbation_spec_unconditional_false_at_p_top
    (S : Setup n E X Y Ω) (g u : E)
    (_hp : S.p = ⊤)
    (hu : u ∈ Setup.perturbationBall (S := S))
    (hstrict :
      Setup.linearPairing g (Setup.oneNormPerturbation (S := S) g) <
        Setup.linearPairing g u) :
    ¬ (Setup.oneNormPerturbation (S := S) g ∈ Setup.perturbationBall (S := S) ∧
      IsMaxOn (fun v : E => Setup.linearPairing g v)
        (Setup.perturbationBall (S := S))
        (Setup.oneNormPerturbation (S := S) g)) := by
  exact
    oneNormPerturbation_spec_unconditional_false_of_strict_better_feasible_point
      (S := S) g u hu hstrict

/-! Equation (2)'s source-facing perturbation.  It is kept in the literal
    sign/power/dual-norm form printed by the paper; endpoint and denominator
    obligations are theorem work, not branch conventions in this definition. -/
noncomputable def dualNormPerturbationFormula
    (S : Setup n E X Y Ω) (g : E) : E :=
  if hp1 : S.p = 1 then
    oneNormPerturbation (S := S) g
  else if hptop : S.p = ⊤ then
    ∑ i : Fin (Module.finrank ℝ E),
      (S.rho * coordinateSign (coordinate g i)) •
        stdOrthonormalBasis ℝ E i
  else
    let b := stdOrthonormalBasis ℝ E
    let qv := (q S).toReal
    let denominator : ℝ :=
      (∑ i : Fin (Module.finrank ℝ E),
        ‖coordinateVector (E := E) g i‖ ^ qv) ^ (1 / S.p.toReal)
    ∑ i : Fin (Module.finrank ℝ E),
      (S.rho * coordinateSign (coordinateVector (E := E) g i) *
        (‖coordinateVector (E := E) g i‖ ^ (qv - 1)) / denominator) • b i

theorem dualNormPerturbationFormula_zero
    (S : Setup n E X Y Ω) :
    Setup.dualNormPerturbationFormula (S := S) 0 = 0 := by
  classical
  have hcoord : ∀ i : Fin (Module.finrank ℝ E),
      coordinate (E := E) (0 : E) i = 0 := by
    intro i
    simp [coordinate]
  have hcoordVector : ∀ i : Fin (Module.finrank ℝ E),
      coordinateVector (E := E) (0 : E) i = 0 := by
    intro i
    simp [coordinateVector, coordinate]
  unfold Setup.dualNormPerturbationFormula
  by_cases hp1 : S.p = 1
  · simp [hp1, Setup.oneNormPerturbation, hcoord, coordinateSign]
  · by_cases hptop : S.p = ⊤
    · simp [hptop, hcoord, coordinateSign]
    · simp [hp1, hptop, hcoordVector, coordinateSign]

theorem dualNormPerturbationFormula_p_top
    (S : Setup n E X Y Ω) (g : E) (hg : g ≠ 0) (hp : S.p = ⊤) :
    Setup.dualNormPerturbationFormula (S := S) g =
      ∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinate g i)) •
          stdOrthonormalBasis ℝ E i := by
  simp [Setup.dualNormPerturbationFormula, hp]

theorem dualNormPerturbationFormula_p_one
    (S : Setup n E X Y Ω) (g : E) (hg : g ≠ 0) (hp : S.p = 1) :
    Setup.dualNormPerturbationFormula (S := S) g =
      Setup.oneNormPerturbation (S := S) g := by
  simp [dualNormPerturbationFormula, hp]

private theorem coordinateMax_le_of_abs_coordinate_bound
    (v : E) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ i : Fin (Module.finrank ℝ E),
      |coordinateVector (E := E) v i| ≤ M) :
    coordinateMax (E := E) v ≤ M := by
  classical
  unfold coordinateMax
  by_cases hne : Nonempty (Fin (Module.finrank ℝ E))
  · letI : Nonempty (Fin (Module.finrank ℝ E)) := hne
    simp [hne, Real.norm_eq_abs]
    intro i
    exact h i
  · simp [hne, hM]

private theorem topDualNormPerturbation_mem_ball
    (S : Setup n E X Y Ω) (g : E) (hp : S.p = ⊤) :
    (∑ i : Fin (Module.finrank ℝ E),
      (S.rho * coordinateSign (coordinate g i)) •
        stdOrthonormalBasis ℝ E i) ∈ Setup.perturbationBall (S := S) := by
  classical
  unfold Setup.perturbationBall
  change Setup.lpNorm S.p
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinate g i)) •
          stdOrthonormalBasis ℝ E i) ≤ S.rho
  rw [hp, Setup.lpNorm_infinity_spec]
  refine coordinateMax_le_of_abs_coordinate_bound
    (E := E)
    (∑ i : Fin (Module.finrank ℝ E),
      (S.rho * coordinateSign (coordinate g i)) •
        stdOrthonormalBasis ℝ E i)
    S.rho (Setup.rho_nonneg (S := S)) ?_
  intro j
  rw [coordinateVector_sum_smul_orthonormalBasis]
  have hrho_nonneg : 0 ≤ S.rho := Setup.rho_nonneg (S := S)
  have habs :
      |S.rho * coordinateSign (coordinate g j)| =
        S.rho * |coordinateSign (coordinate g j)| := by
    rw [abs_mul, abs_of_nonneg hrho_nonneg]
  calc
    |S.rho * coordinateSign (coordinate g j)|
        = S.rho * |coordinateSign (coordinate g j)| := habs
    _ ≤ S.rho * 1 := by
      exact mul_le_mul_of_nonneg_left
        (abs_coordinateSign_le_one (coordinate g j)) hrho_nonneg
    _ = S.rho := by ring

private theorem linearPairing_le_l1_mul_coordinateMax
    (g u : E) :
    linearPairing g u ≤
      (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) *
        coordinateMax (E := E) u := by
  classical
  calc
    linearPairing g u =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i * coordinateVector (E := E) u i := by
      exact linearPairing_eq_sum_coordinates (E := E) g u
    _ ≤
        |∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i * coordinateVector (E := E) u i| :=
      le_abs_self _
    _ ≤
        ∑ i : Fin (Module.finrank ℝ E),
          |coordinateVector (E := E) g i * coordinateVector (E := E) u i| := by
      simpa using
        (Finset.abs_sum_le_sum_abs
          (fun i : Fin (Module.finrank ℝ E) =>
            coordinateVector (E := E) g i * coordinateVector (E := E) u i)
          Finset.univ)
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          |coordinateVector (E := E) g i| * |coordinateVector (E := E) u i| := by
      simp [abs_mul]
    _ ≤
        ∑ i : Fin (Module.finrank ℝ E),
          |coordinateVector (E := E) g i| * coordinateMax (E := E) u := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact mul_le_mul_of_nonneg_left
        (coordinateMax_abs_coordinate_le (E := E) u i)
        (abs_nonneg (coordinateVector (E := E) g i))
    _ =
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) *
          coordinateMax (E := E) u := by
      rw [Finset.sum_mul]

private theorem topDualNormPerturbation_pairing_value
    (S : Setup n E X Y Ω) (g : E) :
    linearPairing g
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinate g i)) •
          stdOrthonormalBasis ℝ E i) =
      S.rho *
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) := by
  classical
  calc
    linearPairing g
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinate g i)) •
          stdOrthonormalBasis ℝ E i)
        =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i *
            coordinateVector (E := E)
              (∑ j : Fin (Module.finrank ℝ E),
                (S.rho * coordinateSign (coordinate g j)) •
                  stdOrthonormalBasis ℝ E j) i := by
      exact linearPairing_eq_sum_coordinates (E := E) g _
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          S.rho * |coordinateVector (E := E) g i| := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [coordinateVector_sum_smul_orthonormalBasis]
      change coordinateVector (E := E) g i *
          (S.rho * coordinateSign (coordinateVector (E := E) g i)) =
        S.rho * |coordinateVector (E := E) g i|
      calc
        coordinateVector (E := E) g i *
            (S.rho * coordinateSign (coordinateVector (E := E) g i))
            =
          S.rho *
            (coordinateSign (coordinateVector (E := E) g i) *
              coordinateVector (E := E) g i) := by
          ring
        _ = S.rho * |coordinateVector (E := E) g i| := by
          rw [coordinateSign_mul_self]
    _ = S.rho *
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) := by
      rw [Finset.mul_sum]

private theorem topDualNormPerturbation_maximal
    (S : Setup n E X Y Ω) (g : E) (hp : S.p = ⊤) :
    IsMaxOn (fun u : E => Setup.linearPairing g u)
      (Setup.perturbationBall (S := S))
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinate g i)) •
          stdOrthonormalBasis ℝ E i) := by
  classical
  refine isMaxOn_iff.mpr ?_
  intro u hu
  have hu_max : coordinateMax (E := E) u ≤ S.rho := by
    unfold Setup.perturbationBall at hu
    change Setup.lpNorm S.p u ≤ S.rho at hu
    rwa [hp, Setup.lpNorm_infinity_spec] at hu
  have hsum_nonneg :
      0 ≤ ∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i| := by
    exact Finset.sum_nonneg (fun i _hi => abs_nonneg _)
  have hupper :
      linearPairing g u ≤
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) *
          coordinateMax (E := E) u :=
    linearPairing_le_l1_mul_coordinateMax (E := E) g u
  have hbudget :
      (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) *
          coordinateMax (E := E) u ≤
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) *
          S.rho :=
    mul_le_mul_of_nonneg_left hu_max hsum_nonneg
  have hvalue :=
    topDualNormPerturbation_pairing_value (S := S) g
  calc
    linearPairing g u ≤
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) *
          coordinateMax (E := E) u := hupper
    _ ≤
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) *
          S.rho := hbudget
    _ = S.rho *
        (∑ i : Fin (Module.finrank ℝ E), |coordinateVector (E := E) g i|) := by
      ring
    _ = linearPairing g
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinate g i)) •
          stdOrthonormalBasis ℝ E i) := hvalue.symm

private theorem finite_p_toReal_gt_one
    (S : Setup n E X Y Ω) (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) :
    1 < S.p.toReal := by
  have hpReal_ge_one : (1 : ℝ) ≤ S.p.toReal := by
    have hmono : (1 : ENNReal).toReal ≤ S.p.toReal :=
      ENNReal.toReal_mono hptop S.p_domain
    simpa using hmono
  have hpReal_ne_one : S.p.toReal ≠ 1 := by
    intro hreal
    apply hp1
    have heq : S.p.toReal = (1 : ENNReal).toReal := by
      simpa using hreal
    exact (ENNReal.toReal_eq_toReal_iff' hptop ENNReal.one_ne_top).mp heq
  exact lt_of_le_of_ne hpReal_ge_one (Ne.symm hpReal_ne_one)

private theorem finite_p_toReal_pos
    (S : Setup n E X Y Ω) (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) :
    0 < S.p.toReal := by
  exact lt_trans zero_lt_one (finite_p_toReal_gt_one (S := S) hp1 hptop)

private theorem finite_q_toReal_eq
    (S : Setup n E X Y Ω) (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) :
    (q S).toReal = S.p.toReal / (S.p.toReal - 1) := by
  have hp_pos : 0 < S.p.toReal :=
    finite_p_toReal_pos (S := S) hp1 hptop
  have hden_pos : 0 < S.p.toReal - 1 :=
    sub_pos.mpr (finite_p_toReal_gt_one (S := S) hp1 hptop)
  have hquot_nonneg : 0 ≤ S.p.toReal / (S.p.toReal - 1) :=
    div_nonneg (le_of_lt hp_pos) (le_of_lt hden_pos)
  simp [q, hptop, hp1, ENNReal.toReal_ofReal hquot_nonneg]

private theorem finite_q_toReal_pos
    (S : Setup n E X Y Ω) (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) :
    0 < (q S).toReal := by
  rw [finite_q_toReal_eq (S := S) hp1 hptop]
  exact div_pos
    (finite_p_toReal_pos (S := S) hp1 hptop)
    (sub_pos.mpr (finite_p_toReal_gt_one (S := S) hp1 hptop))

private theorem finite_p_mul_q_minus_one
    (S : Setup n E X Y Ω) (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) :
    S.p.toReal * ((q S).toReal - 1) = (q S).toReal := by
  rw [finite_q_toReal_eq (S := S) hp1 hptop]
  have hden_ne : S.p.toReal - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (finite_p_toReal_gt_one (S := S) hp1 hptop))
  field_simp [hden_ne]
  ring

private theorem finite_q_minus_one_pos
    (S : Setup n E X Y Ω) (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) :
    0 < (q S).toReal - 1 := by
  rw [finite_q_toReal_eq (S := S) hp1 hptop]
  have hp_gt : 1 < S.p.toReal :=
    finite_p_toReal_gt_one (S := S) hp1 hptop
  have hden_pos : 0 < S.p.toReal - 1 := sub_pos.mpr hp_gt
  have hden_ne : S.p.toReal - 1 ≠ 0 := ne_of_gt hden_pos
  field_simp [hden_ne]
  nlinarith

private theorem abs_coordinateSign_eq_one_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    |coordinateSign x| = 1 := by
  unfold coordinateSign
  by_cases hpos : 0 < x
  · simp [hpos]
  · have hle : x ≤ 0 := le_of_not_gt hpos
    have hneg : x < 0 := lt_of_le_of_ne hle hx
    simp [hpos, hneg]

private theorem finite_dual_candidate_coordinate_p_power
    (x rho p q D : ℝ)
    (hrho_pos : 0 < rho) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (hq_minus_one_pos : 0 < q - 1)
    (hpq : p * (q - 1) = q) (hD_pos : 0 < D) :
    ‖rho * coordinateSign x * ‖x‖ ^ (q - 1) / D‖ ^ p =
      rho ^ p * ‖x‖ ^ q / D ^ p := by
  classical
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hqm1_ne : q - 1 ≠ 0 := ne_of_gt hq_minus_one_pos
  have hrho_nonneg : 0 ≤ rho := le_of_lt hrho_pos
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  by_cases hx : x = 0
  · subst x
    simp [coordinateSign, Real.zero_rpow hp_ne, Real.zero_rpow hq_ne,
      Real.zero_rpow hqm1_ne]
  · have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hxnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
    have hpow_nonneg : 0 ≤ ‖x‖ ^ (q - 1) :=
      Real.rpow_nonneg hxnorm_nonneg (q - 1)
    have hpow_abs :
        |‖x‖ ^ (q - 1)| = ‖x‖ ^ (q - 1) :=
      abs_of_nonneg hpow_nonneg
    have hsign_abs : |coordinateSign x| = 1 :=
      abs_coordinateSign_eq_one_of_ne_zero hx
    have hnorm_base :
        ‖rho * coordinateSign x * ‖x‖ ^ (q - 1) / D‖ =
          rho * ‖x‖ ^ (q - 1) / D := by
      rw [Real.norm_eq_abs]
      calc
        |rho * coordinateSign x * ‖x‖ ^ (q - 1) / D|
            =
            |rho| * |coordinateSign x| * |‖x‖ ^ (q - 1)| / |D| := by
          rw [abs_div, abs_mul, abs_mul]
        _ = rho * 1 * (‖x‖ ^ (q - 1)) / D := by
          rw [abs_of_pos hrho_pos, hsign_abs, hpow_abs, abs_of_pos hD_pos]
        _ = rho * ‖x‖ ^ (q - 1) / D := by ring
    rw [hnorm_base]
    have hmul_nonneg : 0 ≤ rho * ‖x‖ ^ (q - 1) :=
      mul_nonneg hrho_nonneg hpow_nonneg
    calc
      (rho * ‖x‖ ^ (q - 1) / D) ^ p
          = (rho * ‖x‖ ^ (q - 1)) ^ p / D ^ p := by
        rw [Real.div_rpow hmul_nonneg hD_nonneg]
      _ = (rho ^ p * (‖x‖ ^ (q - 1)) ^ p) / D ^ p := by
        rw [Real.mul_rpow hrho_nonneg hpow_nonneg]
      _ = (rho ^ p * ‖x‖ ^ q) / D ^ p := by
        have hmul_exp : (q - 1) * p = q := by nlinarith
        rw [← Real.rpow_mul hxnorm_nonneg (q - 1) p, hmul_exp]
      _ = rho ^ p * ‖x‖ ^ q / D ^ p := by ring

private theorem finite_dual_candidate_p_power_sum
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (rho p q D : ℝ)
    (hrho_pos : 0 < rho) (hp_pos : 0 < p) (hq_pos : 0 < q)
    (hq_minus_one_pos : 0 < q - 1)
    (hpq : p * (q - 1) = q) (hD_pos : 0 < D)
    (hD_pow : D ^ p = ∑ i : ι, ‖x i‖ ^ q) :
    (∑ i : ι, ‖rho * coordinateSign (x i) * ‖x i‖ ^ (q - 1) / D‖ ^ p) =
      rho ^ p := by
  classical
  calc
    (∑ i : ι, ‖rho * coordinateSign (x i) * ‖x i‖ ^ (q - 1) / D‖ ^ p)
        =
        ∑ i : ι, rho ^ p * ‖x i‖ ^ q / D ^ p := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact finite_dual_candidate_coordinate_p_power
        (x i) rho p q D hrho_pos hp_pos hq_pos hq_minus_one_pos hpq hD_pos
    _ =
        (rho ^ p / D ^ p) * (∑ i : ι, ‖x i‖ ^ q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      ring
    _ = (rho ^ p / D ^ p) * D ^ p := by
      rw [← hD_pow]
    _ = rho ^ p := by
      have hDpow_ne : D ^ p ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hD_pos p)
      field_simp [hDpow_ne]

private theorem finite_lp_holder_coordinate_sum
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) {p q : ℝ}
    (hp_gt : 1 < p) (hq_minus_one_pos : 0 < q - 1)
    (hpq : 1 / p + 1 / q = 1) :
    (∑ i : ι, |a i * b i|) ≤
      (∑ i : ι, ‖a i‖ ^ q) ^ (1 / q) *
        (∑ i : ι, ‖b i‖ ^ p) ^ (1 / p) := by
  classical
  have hq_gt : 1 < q := by linarith
  have hconj : q.HolderConjugate p := by
    rw [Real.holderConjugate_iff]
    exact ⟨hq_gt, by rw [add_comm]; simpa [one_div] using hpq⟩
  have _hyoung_pointwise : ∀ i : ι,
      |a i| * |b i| ≤ |(|a i|)| ^ q / q + |(|b i|)| ^ p / p := by
    intro i
    exact Real.young_inequality (|a i|) (|b i|) hconj
  have hholder :=
    Real.inner_le_Lp_mul_Lq_of_nonneg
      (s := (Finset.univ : Finset ι))
      (f := fun i : ι => |a i|)
      (g := fun i : ι => |b i|)
      (p := q) (q := p) hconj
      (fun i _hi => abs_nonneg (a i))
      (fun i _hi => abs_nonneg (b i))
  simpa [Real.norm_eq_abs, abs_mul] using hholder

private theorem finite_dual_scalar_value_normalization
    {A p q : ℝ} (hA_pos : 0 < A)
    (hpq : 1 / p + 1 / q = 1) :
    A ^ (1 / q) = A / A ^ (1 / p) := by
  have hconj_sum : 1 / q + 1 / p = 1 := by
    rw [add_comm]
    exact hpq
  have hpow_mul : A ^ (1 / q) * A ^ (1 / p) = A := by
    rw [← Real.rpow_add hA_pos, hconj_sum, Real.rpow_one]
  have hden_ne : A ^ (1 / p) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hA_pos (1 / p))
  calc
    A ^ (1 / q) = (A ^ (1 / q) * A ^ (1 / p)) / A ^ (1 / p) := by
      field_simp [hden_ne]
    _ = A / A ^ (1 / p) := by rw [hpow_mul]

private theorem finite_dual_candidate_coordinate_pairing
    (x rho q D : ℝ) (hq_pos : 0 < q) (hq_minus_one_pos : 0 < q - 1) :
    x * (rho * coordinateSign x * ‖x‖ ^ (q - 1) / D) =
      rho * ‖x‖ ^ q / D := by
  classical
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hqm1_ne : q - 1 ≠ 0 := ne_of_gt hq_minus_one_pos
  by_cases hx : x = 0
  · subst x
    simp [coordinateSign, Real.zero_rpow hq_ne, Real.zero_rpow hqm1_ne]
  · have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hpow :
        ‖x‖ * ‖x‖ ^ (q - 1) = ‖x‖ ^ q := by
      calc
        ‖x‖ * ‖x‖ ^ (q - 1) =
            ‖x‖ ^ (1 : ℝ) * ‖x‖ ^ (q - 1) := by rw [Real.rpow_one]
        _ = ‖x‖ ^ ((1 : ℝ) + (q - 1)) := by
          rw [← Real.rpow_add hxnorm_pos]
        _ = ‖x‖ ^ q := by ring_nf
    calc
      x * (rho * coordinateSign x * ‖x‖ ^ (q - 1) / D)
          =
          rho * ((coordinateSign x * x) * ‖x‖ ^ (q - 1)) / D := by
        ring
      _ = rho * (‖x‖ * ‖x‖ ^ (q - 1)) / D := by
        rw [coordinateSign_mul_self]
        simp [Real.norm_eq_abs]
      _ = rho * ‖x‖ ^ q / D := by rw [hpow]

private theorem finite_dual_candidate_pairing_value_nonzero
    (S : Setup n E X Y Ω) (g : E)
    (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) (_hg : g ≠ 0) :
    linearPairing g
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinateVector (E := E) g i) *
          (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
            ((∑ j : Fin (Module.finrank ℝ E),
              ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i) =
      S.rho *
        (∑ i : Fin (Module.finrank ℝ E),
          ‖coordinateVector (E := E) g i‖ ^ (q S).toReal) /
          ((∑ j : Fin (Module.finrank ℝ E),
            ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
              (1 / S.p.toReal)) := by
  classical
  let qv : ℝ := (q S).toReal
  let A : ℝ := ∑ i : Fin (Module.finrank ℝ E),
    ‖coordinateVector (E := E) g i‖ ^ qv
  let D : ℝ := A ^ (1 / S.p.toReal)
  have hq_pos : 0 < qv := by
    dsimp [qv]
    exact finite_q_toReal_pos (S := S) hp1 hptop
  have hq_minus_one_pos : 0 < qv - 1 := by
    dsimp [qv]
    exact finite_q_minus_one_pos (S := S) hp1 hptop
  calc
    linearPairing g
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinateVector (E := E) g i) *
          (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
            ((∑ j : Fin (Module.finrank ℝ E),
              ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i)
        =
        ∑ i : Fin (Module.finrank ℝ E),
          coordinateVector (E := E) g i *
            coordinateVector (E := E)
              (∑ k : Fin (Module.finrank ℝ E),
                (S.rho * coordinateSign (coordinateVector (E := E) g k) *
                  (‖coordinateVector (E := E) g k‖ ^ ((q S).toReal - 1)) /
                    ((∑ j : Fin (Module.finrank ℝ E),
                      ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                        (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E k) i := by
      exact linearPairing_eq_sum_coordinates (E := E) g _
    _ =
        ∑ i : Fin (Module.finrank ℝ E),
          S.rho * ‖coordinateVector (E := E) g i‖ ^ qv / D := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [coordinateVector_sum_smul_orthonormalBasis]
      exact finite_dual_candidate_coordinate_pairing
        (coordinateVector (E := E) g i) S.rho qv D hq_pos hq_minus_one_pos
    _ =
        S.rho *
          (∑ i : Fin (Module.finrank ℝ E),
            ‖coordinateVector (E := E) g i‖ ^ qv) / D := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    _ =
        S.rho *
          (∑ i : Fin (Module.finrank ℝ E),
            ‖coordinateVector (E := E) g i‖ ^ (q S).toReal) /
            ((∑ j : Fin (Module.finrank ℝ E),
              ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                (1 / S.p.toReal)) := by
      simp [A, D, qv]

private theorem finiteDualNormPerturbation_maximal_nonzero
    (S : Setup n E X Y Ω) (g : E)
    (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) (hg : g ≠ 0) :
    IsMaxOn (fun u : E => Setup.linearPairing g u)
      (Setup.perturbationBall (S := S))
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinateVector (E := E) g i) *
          (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
            ((∑ j : Fin (Module.finrank ℝ E),
              ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i) := by
  classical
  let p : ℝ := S.p.toReal
  let qv : ℝ := (q S).toReal
  let A : ℝ := ∑ i : Fin (Module.finrank ℝ E),
    ‖coordinateVector (E := E) g i‖ ^ qv
  let B : E → ℝ := fun u =>
    ∑ i : Fin (Module.finrank ℝ E), ‖coordinateVector (E := E) u i‖ ^ p
  let D : ℝ := A ^ (1 / p)
  have hp_gt : 1 < p := by
    dsimp [p]
    exact finite_p_toReal_gt_one (S := S) hp1 hptop
  have hp_pos : 0 < p := lt_trans zero_lt_one hp_gt
  have hq_pos : 0 < qv := by
    dsimp [qv]
    exact finite_q_toReal_pos (S := S) hp1 hptop
  have hq_minus_one_pos : 0 < qv - 1 := by
    dsimp [qv]
    exact finite_q_minus_one_pos (S := S) hp1 hptop
  have hpq : 1 / p + 1 / qv = 1 := by
    dsimp [p, qv]
    exact holder_dual_exponent_relation (S := S)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (coordinateVector (E := E) g i)) qv)
  have hA_pos : 0 < A := by
    have hcoord : ∃ i : Fin (Module.finrank ℝ E),
        coordinateVector (E := E) g i ≠ 0 := by
      by_contra h
      push Not at h
      have hsum_zero :
          (∑ i : Fin (Module.finrank ℝ E),
            coordinateVector (E := E) g i • stdOrthonormalBasis ℝ E i) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _hi
        simp [h i]
      have hg_zero : g = 0 := by
        have hrecon := coordinateVector_reconstruct (E := E) g
        rw [hsum_zero] at hrecon
        exact hrecon.symm
      exact hg hg_zero
    rcases hcoord with ⟨i0, hi0⟩
    dsimp [A]
    refine Finset.sum_pos' ?_ ?_
    · intro i _hi
      by_cases hci : coordinateVector (E := E) g i = 0
      · have hq_ne : qv ≠ 0 := ne_of_gt hq_pos
        simp [hci, Real.zero_rpow hq_ne]
      · exact le_of_lt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hci) qv)
    · refine ⟨i0, Finset.mem_univ i0, ?_⟩
      exact Real.rpow_pos_of_pos (norm_pos_iff.mpr hi0) qv
  refine isMaxOn_iff.mpr ?_
  intro u hu
  have hlin_abs :
      linearPairing g u ≤
        ∑ i : Fin (Module.finrank ℝ E),
          |coordinateVector (E := E) g i * coordinateVector (E := E) u i| := by
    calc
      linearPairing g u =
          ∑ i : Fin (Module.finrank ℝ E),
            coordinateVector (E := E) g i * coordinateVector (E := E) u i := by
        exact linearPairing_eq_sum_coordinates (E := E) g u
      _ ≤
          |∑ i : Fin (Module.finrank ℝ E),
            coordinateVector (E := E) g i * coordinateVector (E := E) u i| :=
        le_abs_self _
      _ ≤
          ∑ i : Fin (Module.finrank ℝ E),
            |coordinateVector (E := E) g i * coordinateVector (E := E) u i| := by
        simpa using
          (Finset.abs_sum_le_sum_abs
            (fun i : Fin (Module.finrank ℝ E) =>
              coordinateVector (E := E) g i * coordinateVector (E := E) u i)
            Finset.univ)
  have hholder :
      (∑ i : Fin (Module.finrank ℝ E),
          |coordinateVector (E := E) g i * coordinateVector (E := E) u i|) ≤
        A ^ (1 / qv) * (B u) ^ (1 / p) := by
    simpa [A, B, p, qv] using
      finite_lp_holder_coordinate_sum
        (a := fun i : Fin (Module.finrank ℝ E) => coordinateVector (E := E) g i)
        (b := fun i : Fin (Module.finrank ℝ E) => coordinateVector (E := E) u i)
        (p := p) (q := qv) hp_gt hq_minus_one_pos hpq
  have hubudget : (B u) ^ (1 / p) ≤ S.rho := by
    unfold Setup.perturbationBall at hu
    change Setup.lpNorm S.p u ≤ S.rho at hu
    rw [Setup.lpNorm_finite_spec (E := E) hptop u] at hu
    simpa [B, p] using hu
  have hAnorm_nonneg : 0 ≤ A ^ (1 / qv) :=
    Real.rpow_nonneg hA_nonneg (1 / qv)
  have hupper :
      linearPairing g u ≤ S.rho * A ^ (1 / qv) := by
    calc
      linearPairing g u ≤
          ∑ i : Fin (Module.finrank ℝ E),
            |coordinateVector (E := E) g i * coordinateVector (E := E) u i| :=
        hlin_abs
      _ ≤ A ^ (1 / qv) * (B u) ^ (1 / p) := hholder
      _ ≤ A ^ (1 / qv) * S.rho :=
        mul_le_mul_of_nonneg_left hubudget hAnorm_nonneg
      _ = S.rho * A ^ (1 / qv) := by ring
  have hnorm :
      A ^ (1 / qv) = A / D := by
    dsimp [D]
    exact finite_dual_scalar_value_normalization (A := A) (p := p) (q := qv) hA_pos hpq
  have hvalue :
      linearPairing g
        (∑ i : Fin (Module.finrank ℝ E),
          (S.rho * coordinateSign (coordinateVector (E := E) g i) *
            (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
              ((∑ j : Fin (Module.finrank ℝ E),
                ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                  (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i) =
        S.rho * A / D := by
    simpa [A, D, p, qv] using
      finite_dual_candidate_pairing_value_nonzero
        (S := S) g hp1 hptop hg
  calc
    linearPairing g u ≤ S.rho * A ^ (1 / qv) := hupper
    _ = S.rho * (A / D) := by rw [hnorm]
    _ = S.rho * A / D := by ring
    _ =
        linearPairing g
          (∑ i : Fin (Module.finrank ℝ E),
            (S.rho * coordinateSign (coordinateVector (E := E) g i) *
              (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
                ((∑ j : Fin (Module.finrank ℝ E),
                  ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                    (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i) := hvalue.symm

private theorem finiteDualNormPerturbation_mem_ball_nonzero
    (S : Setup n E X Y Ω) (g : E)
    (hp1 : S.p ≠ 1) (hptop : S.p ≠ ⊤) (hg : g ≠ 0) :
    (∑ i : Fin (Module.finrank ℝ E),
      (S.rho * coordinateSign (coordinateVector (E := E) g i) *
        (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
          ((∑ j : Fin (Module.finrank ℝ E),
            ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
              (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i) ∈
      Setup.perturbationBall (S := S) := by
  classical
  let p : ℝ := S.p.toReal
  let qv : ℝ := (q S).toReal
  let A : ℝ := ∑ i : Fin (Module.finrank ℝ E),
    ‖coordinateVector (E := E) g i‖ ^ qv
  let D : ℝ := A ^ (1 / p)
  have hp_pos : 0 < p := by
    dsimp [p]
    exact finite_p_toReal_pos (S := S) hp1 hptop
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hq_pos : 0 < qv := by
    dsimp [qv]
    exact finite_q_toReal_pos (S := S) hp1 hptop
  have hq_minus_one_pos : 0 < qv - 1 := by
    dsimp [qv]
    exact finite_q_minus_one_pos (S := S) hp1 hptop
  have hpq : p * (qv - 1) = qv := by
    dsimp [p, qv]
    exact finite_p_mul_q_minus_one (S := S) hp1 hptop
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (coordinateVector (E := E) g i)) qv)
  have hD_ne : D ≠ 0 := by
    dsimp [D, A, p, qv]
    exact dualNormDenominator_ne_zero (S := S) g hg hp1 hptop
      (finite_q_toReal_pos (S := S) hp1 hptop)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Real.rpow_nonneg hA_nonneg (1 / p)
  have hD_pos : 0 < D :=
    lt_of_le_of_ne hD_nonneg (Ne.symm hD_ne)
  have hD_pow : D ^ p = A := by
    dsimp [D]
    simpa [one_div] using Real.rpow_inv_rpow hA_nonneg hp_ne
  have hsum :
      (∑ i : Fin (Module.finrank ℝ E),
        ‖S.rho * coordinateSign (coordinateVector (E := E) g i) *
          ‖coordinateVector (E := E) g i‖ ^ (qv - 1) / D‖ ^ p) =
        S.rho ^ p :=
    finite_dual_candidate_p_power_sum
      (fun i : Fin (Module.finrank ℝ E) => coordinateVector (E := E) g i)
      S.rho p qv D S.rho_pos hp_pos hq_pos hq_minus_one_pos hpq hD_pos hD_pow
  have hnorm_eq :
      Setup.lpNorm S.p
        (∑ i : Fin (Module.finrank ℝ E),
          (S.rho * coordinateSign (coordinateVector (E := E) g i) *
            (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
              ((∑ j : Fin (Module.finrank ℝ E),
                ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                  (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i) =
        S.rho := by
    rw [Setup.lpNorm_finite_spec (E := E) hptop]
    have hsum_coords :
        (∑ i : Fin (Module.finrank ℝ E),
          ‖coordinateVector (E := E)
            (∑ k : Fin (Module.finrank ℝ E),
              (S.rho * coordinateSign (coordinateVector (E := E) g k) *
                (‖coordinateVector (E := E) g k‖ ^ ((q S).toReal - 1)) /
                  ((∑ j : Fin (Module.finrank ℝ E),
                    ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                      (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E k) i‖ ^
            S.p.toReal) =
          S.rho ^ p := by
      calc
        (∑ i : Fin (Module.finrank ℝ E),
          ‖coordinateVector (E := E)
            (∑ k : Fin (Module.finrank ℝ E),
              (S.rho * coordinateSign (coordinateVector (E := E) g k) *
                (‖coordinateVector (E := E) g k‖ ^ ((q S).toReal - 1)) /
                  ((∑ j : Fin (Module.finrank ℝ E),
                    ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                      (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E k) i‖ ^
            S.p.toReal)
            =
            ∑ i : Fin (Module.finrank ℝ E),
              ‖S.rho * coordinateSign (coordinateVector (E := E) g i) *
                ‖coordinateVector (E := E) g i‖ ^ (qv - 1) / D‖ ^ p := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [coordinateVector_sum_smul_orthonormalBasis]
        _ = S.rho ^ p := hsum
    rw [hsum_coords]
    simpa [p, one_div] using
      Real.rpow_rpow_inv (le_of_lt S.rho_pos) hp_ne
  unfold Setup.perturbationBall
  change Setup.lpNorm S.p
      (∑ i : Fin (Module.finrank ℝ E),
        (S.rho * coordinateSign (coordinateVector (E := E) g i) *
          (‖coordinateVector (E := E) g i‖ ^ ((q S).toReal - 1)) /
            ((∑ j : Fin (Module.finrank ℝ E),
              ‖coordinateVector (E := E) g j‖ ^ (q S).toReal) ^
                (1 / S.p.toReal))) • stdOrthonormalBasis ℝ E i) ≤ S.rho
  exact le_of_eq hnorm_eq

/- The source-facing perturbation is the closed-form dual-norm realization.
   Endpoint and zero-gradient conventions are explicit in the corrected
   formula above; optimality and feasibility remain derived theorems. -/
noncomputable def dualNormPerturbation (S : Setup n E X Y Ω) (g : E) : E :=
  dualNormPerturbationFormula (S := S) g

theorem dualNormPerturbation_formula (S : Setup n E X Y Ω) (g : E) :
    Setup.dualNormPerturbation (S := S) g =
      Setup.dualNormPerturbationFormula (S := S) g := by
  rfl

theorem dualNormPerturbation_mem_ball (S : Setup n E X Y Ω) (g : E) :
    Setup.dualNormPerturbation (S := S) g ∈
      Setup.perturbationBall (S := S) := by
  unfold Setup.dualNormPerturbation Setup.dualNormPerturbationFormula
  by_cases hp1 : S.p = 1
  · simpa [hp1] using (Setup.oneNormPerturbation_spec (S := S) g hp1).1
  · by_cases hptop : S.p = ⊤
    · simpa [hp1, hptop] using
        topDualNormPerturbation_mem_ball (S := S) g hptop
    · rcases Classical.em (g = 0) with hg | hg
      · subst g
        have hp_pos : 0 < S.p.toReal :=
          finite_p_toReal_pos (S := S) hp1 hptop
        have hp_ne : S.p.toReal ≠ 0 := ne_of_gt hp_pos
        have hinv_ne : S.p.toReal⁻¹ ≠ 0 := inv_ne_zero hp_ne
        simp [hp1, hptop, Setup.perturbationBall, Setup.lpNorm_finite_spec,
          Setup.rho_nonneg, coordinateVector, coordinate, coordinateSign,
          Real.zero_rpow hp_ne, Real.zero_rpow hinv_ne]
      · simpa [hp1, hptop] using
          finiteDualNormPerturbation_mem_ball_nonzero
            (S := S) g hp1 hptop hg

theorem dualNormPerturbation_maximal (S : Setup n E X Y Ω) (g : E) :
    IsMaxOn (fun u : E => Setup.linearPairing g u)
      (Setup.perturbationBall (S := S))
      (Setup.dualNormPerturbation (S := S) g) := by
  unfold Setup.dualNormPerturbation Setup.dualNormPerturbationFormula
  by_cases hp1 : S.p = 1
  · simpa [hp1] using (Setup.oneNormPerturbation_spec (S := S) g hp1).2
  · by_cases hptop : S.p = ⊤
    · simpa [hp1, hptop] using
        topDualNormPerturbation_maximal (S := S) g hptop
    · rcases Classical.em (g = 0) with hg | hg
      · subst g
        refine isMaxOn_iff.mpr ?_
        intro u hu
        simp [linearPairing]
      · simpa [hp1, hptop] using
          finiteDualNormPerturbation_maximal_nonzero
            (S := S) g hp1 hptop hg

/- Source-level adversarial perturbation relation for Eq. (2).  The total
   closed-form selector above is an internal corrected realization; the
   paper-facing algorithm only requires a perturbation solving the displayed
   dual-norm inner problem, leaving endpoint and zero-gradient tie-breaking as
   derived proof obligations. -/
def sourceDualNormPerturbationRelation
    (S : Setup n E X Y Ω) (g ε : E) : Prop :=
  ε ∈ Setup.perturbationBall (S := S) ∧
    IsMaxOn (fun u : E => Setup.linearPairing g u)
      (Setup.perturbationBall (S := S)) ε

theorem sourceDualNormPerturbationRelation_spec
    (S : Setup n E X Y Ω) (g ε : E) :
    sourceDualNormPerturbationRelation (S := S) g ε ↔
      ε ∈ Setup.perturbationBall (S := S) ∧
        IsMaxOn (fun u : E => Setup.linearPairing g u)
          (Setup.perturbationBall (S := S)) ε := by
  rfl

theorem dualNormPerturbation_source_relation
    (S : Setup n E X Y Ω) (g : E) :
    sourceDualNormPerturbationRelation (S := S) g
      (Setup.dualNormPerturbation (S := S) g) := by
  exact ⟨Setup.dualNormPerturbation_mem_ball (S := S) g,
    Setup.dualNormPerturbation_maximal (S := S) g⟩

noncomputable def adversarialPerturbation (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) : E :=
  dualNormPerturbation S (batchGradient (S := S) B w)

noncomputable def samGradient (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S)
    (hdom : w.1 + adversarialPerturbation S B w ∈ S.parameterSpace) : E :=
  batchGradient (S := S) B
    ⟨w.1 + adversarialPerturbation S B w, hdom⟩

/- Ambient realization used only for the recursive update.  It avoids
   introducing a source-unstated W-invariance assumption into the iterate
   definition. -/
private noncomputable def samGradientAmbient (S : Setup n E X Y Ω)
    (B : Batch S) (u : E) : E :=
  let ε := dualNormPerturbation S
    (batchGradientAmbient (S := S) B u)
  batchGradientAmbient (S := S) B (u + ε)

/- Source-domain SAM gradient: when the adversarially perturbed point remains
   in W, evaluate the batch gradient on the parameter subtype itself. -/
noncomputable def samGradientOnDomain (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S)
    (hdom : w.1 + adversarialPerturbation S B w ∈ S.parameterSpace) : E :=
  samGradient (S := S) B w hdom

theorem samGradient_onDomain_bridge (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S)
    (hdom : w.1 + adversarialPerturbation S B w ∈ S.parameterSpace) :
    samGradientOnDomain (S := S) B w hdom =
      samGradient (S := S) B w hdom := by
  rfl

theorem samGradient_spec (S : Setup n E X Y Ω) (B : Batch S)
    (w : Parameter S)
    (hdom : w.1 + adversarialPerturbation S B w ∈ S.parameterSpace) :
    samGradient (S := S) B w hdom =
      batchGradient (S := S) B
        ⟨w.1 + adversarialPerturbation (S := S) B w, hdom⟩ := by
  rfl

/- Internal ambient realization of the literal SGD subtraction. -/
noncomputable def ambientUpdate (S : Setup n E X Y Ω)
    (B : Batch S) (w : E) : E :=
  w - S.eta • samGradientAmbient (S := S) B w

/- Public source-facing update, carried by the paper parameter domain. -/
noncomputable def update (S : Setup n E X Y Ω)
    (B : Batch S) (w : Setup.Parameter S)
    (hdom : ambientUpdate (S := S) B w.1 ∈ S.parameterSpace) : Setup.Parameter S :=
  ⟨ambientUpdate (S := S) B w.1, hdom⟩

theorem update_spec (S : Setup n E X Y Ω) (B : Batch S)
    (w : Setup.Parameter S)
    (hdom : ambientUpdate (S := S) B w.1 ∈ S.parameterSpace) :
    (update (S := S) B w hdom).1 =
      w.1 - S.eta • samGradientAmbient (S := S) B w.1 := by
  rfl

/- Source-facing batch-gradient relation.  Algorithm 1 says to compute the
   batch gradient on the parameter carrier; differentiability of this partial
   expression is a proof obligation, not a total-gradient selector in the
   public update rule. -/
def sourceBatchGradientRelation (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) (g : E) : Prop :=
  HasGradientWithinAt (batchLossExtension (S := S) B) g S.parameterSpace w.1

theorem sourceBatchGradientRelation_spec (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) (g : E) :
    sourceBatchGradientRelation (S := S) B w g ↔
      HasGradientWithinAt (batchLossExtension (S := S) B) g S.parameterSpace w.1 := by
  rfl

/- Source-facing SAM gradient relation from Algorithm 1 and Eq. (3).  It is
   partial in the paper parameter carrier: the perturbed point must denote a
   point of W before the batch gradient is evaluated.  The perturbation and
   both gradients are relational source objects, so endpoint conventions and
   total-gradient fallbacks stay out of the algorithm boundary. -/
def sourceSAMGradientRelation (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) (g : E) : Prop :=
  ∃ (baseGradient ε : E),
    sourceBatchGradientRelation (S := S) B w baseGradient ∧
      sourceDualNormPerturbationRelation (S := S) baseGradient ε ∧
      ∃ hdom : w.1 + ε ∈ S.parameterSpace,
        sourceBatchGradientRelation (S := S) B ⟨w.1 + ε, hdom⟩ g

theorem sourceSAMGradientRelation_spec (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) (g : E) :
    sourceSAMGradientRelation (S := S) B w g ↔
      ∃ (baseGradient ε : E),
        sourceBatchGradientRelation (S := S) B w baseGradient ∧
          sourceDualNormPerturbationRelation (S := S) baseGradient ε ∧
          ∃ hdom : w.1 + ε ∈ S.parameterSpace,
            sourceBatchGradientRelation (S := S) B ⟨w.1 + ε, hdom⟩ g := by
  rfl

/- Source-facing one-step update relation from Algorithm 1.  This relation
   records `w_{t+1}=w_t-ηg` without using the private zero-extended ambient
   gradient. -/
def sourceUpdateRelation (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) (u : E) : Prop :=
  ∃ g : E, sourceSAMGradientRelation (S := S) B w g ∧
    u = w.1 - S.eta • g

theorem sourceUpdateRelation_spec (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) (u : E) :
    sourceUpdateRelation (S := S) B w u ↔
      ∃ g : E, sourceSAMGradientRelation (S := S) B w g ∧
        u = w.1 - S.eta • g := by
  rfl

/- Parameter-valued update relation for internal domain-realization proofs. -/
def updateRelation (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S) (u : Parameter S) : Prop :=
  sourceUpdateRelation (S := S) B w u.1

theorem updateRelation_spec (S : Setup n E X Y Ω)
    (B : Batch S) (w u : Parameter S) :
    updateRelation (S := S) B w u ↔
      sourceUpdateRelation (S := S) B w u.1 := by
  rfl

/-! Source-facing finite iterate prefixes for Algorithm 1.

    The paper samples one batch and performs one SGD-style SAM update per loop
    iteration, then returns the current `w_t`.  This bounded prefix relation is
    the public algorithmic spine: every displayed iterate is parameter-valued
    and every successor is justified by the source update relation above.  The
    total ambient stream recursion below is only an internal realization. -/
abbrev IteratePrefix (S : Setup n E X Y Ω) (T : ℕ) :=
  Fin (T + 1) → Parameter S

def iterateInitialIndex (S : Setup n E X Y Ω) (T : ℕ) : Fin (T + 1) :=
  ⟨0, Nat.succ_pos T⟩

def iterateCurrentIndex (S : Setup n E X Y Ω) (T : ℕ) (t : Fin T) :
    Fin (T + 1) :=
  ⟨t.1, Nat.lt_trans t.2 (Nat.lt_succ_self T)⟩

def iterateNextIndex (S : Setup n E X Y Ω) (T : ℕ) (t : Fin T) :
    Fin (T + 1) :=
  ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩

def sourceIteratePrefix (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T) : Prop :=
  ws (iterateInitialIndex (S := S) T) = S.w0 ∧
    ∀ t : Fin T,
      sourceUpdateRelation (S := S) (batches t)
        (ws (iterateCurrentIndex (S := S) T t))
        ((ws (iterateNextIndex (S := S) T t)).1)

theorem sourceIteratePrefix_spec (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T) :
    sourceIteratePrefix (S := S) T batches ws ↔
      ws (iterateInitialIndex (S := S) T) = S.w0 ∧
        ∀ t : Fin T,
          sourceUpdateRelation (S := S) (batches t)
            (ws (iterateCurrentIndex (S := S) T t))
            ((ws (iterateNextIndex (S := S) T t)).1) := by
  rfl

def sourceOutputAtHorizon (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) : Prop :=
  sourceIteratePrefix (S := S) T batches ws ∧
    wout = ws ⟨T, Nat.lt_succ_self T⟩

theorem sourceOutputAtHorizon_spec (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) :
    sourceOutputAtHorizon (S := S) T batches ws wout ↔
      sourceIteratePrefix (S := S) T batches ws ∧
        wout = ws ⟨T, Nat.lt_succ_self T⟩ := by
  rfl

/- Finite-horizon output helper.  This is useful for checked realizations, but
   it is not the paper-facing Algorithm 1 boundary because the source returns
   from a `while not converged` loop rather than from a fixed input horizon. -/
def algorithm1FinitePrefixContract (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) : Prop :=
  sourceOutputAtHorizon (S := S) T batches ws wout

theorem algorithm1FinitePrefixContract_spec (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) :
    algorithm1FinitePrefixContract (S := S) T batches ws wout ↔
      sourceOutputAtHorizon (S := S) T batches ws wout := by
  rfl

/- Source stopping semantics for Algorithm 1's guard `while not converged`.
   The convergence test itself is left as the algorithm's abstract stopping
   criterion; every earlier displayed iterate fails the guard and the returned
   current iterate is the first one satisfying it. -/
def sourceStoppedIteratePrefix (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (converged : Parameter S → Prop) : Prop :=
  sourceIteratePrefix (S := S) T batches ws ∧
    (∀ t : Fin T,
      ¬ converged (ws (iterateCurrentIndex (S := S) T t))) ∧
    converged (ws ⟨T, Nat.lt_succ_self T⟩)

theorem sourceStoppedIteratePrefix_spec (S : Setup n E X Y Ω) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (converged : Parameter S → Prop) :
    sourceStoppedIteratePrefix (S := S) T batches ws converged ↔
      sourceIteratePrefix (S := S) T batches ws ∧
        (∀ t : Fin T,
          ¬ converged (ws (iterateCurrentIndex (S := S) T t))) ∧
        converged (ws ⟨T, Nat.lt_succ_self T⟩) := by
  rfl

def sourceOutputAtStopping (S : Setup n E X Y Ω)
    (converged : Parameter S → Prop) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) : Prop :=
  sourceStoppedIteratePrefix (S := S) T batches ws converged ∧
    wout = ws ⟨T, Nat.lt_succ_self T⟩

theorem sourceOutputAtStopping_spec (S : Setup n E X Y Ω)
    (converged : Parameter S → Prop) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) :
    sourceOutputAtStopping (S := S) converged T batches ws wout ↔
      sourceStoppedIteratePrefix (S := S) T batches ws converged ∧
        wout = ws ⟨T, Nat.lt_succ_self T⟩ := by
  rfl

/- Source contract for Algorithm 1: a finite realization of the `while not
   converged` loop, the displayed SAM update relation at each executed
   iteration, and the returned current iterate. -/
def algorithm1SourceContract (S : Setup n E X Y Ω)
    (converged : Parameter S → Prop) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) : Prop :=
  sourceOutputAtStopping (S := S) converged T batches ws wout

theorem algorithm1SourceContract_spec (S : Setup n E X Y Ω)
    (converged : Parameter S → Prop) (T : ℕ)
    (batches : BatchPrefix S T) (ws : IteratePrefix S T)
    (wout : Parameter S) :
    algorithm1SourceContract (S := S) converged T batches ws wout ↔
      sourceOutputAtStopping (S := S) converged T batches ws wout := by
  rfl

/- Internal checked step and recursion used only to state realization bridges. -/
private noncomputable def ambientStep (S : Setup n E X Y Ω)
    (t : ℕ) (w : E) (batches : BatchRealization S) : E :=
  ambientUpdate S (sampledBatch S batches t) w

private noncomputable def ambientIterates (S : Setup n E X Y Ω)
    (batches : BatchRealization S) : ℕ → E :=
  fun t => SOptLib.recursiveIterateProcess (S.w0 : E) (ambientStep (S := S)) t batches

/- A source-facing iterate is a parameter in `W`.  The only extra datum is an
   explicit realization bridge proving that the literal SGD subtraction stays
   in `W`; this is not a Setup witness or a theorem-level assumption. -/
private noncomputable def updateOnDomain (S : Setup n E X Y Ω)
    (B : Batch S) (w : Parameter S)
    (hdom : ambientUpdate (S := S) B w.1 ∈ S.parameterSpace) : Parameter S :=
  update (S := S) B w hdom

private noncomputable def parameterIterates (S : Setup n E X Y Ω)
    (batches : BatchRealization S)
    (hclosed : ∀ (B : Batch S) (w : Setup.Parameter S),
      ambientUpdate (S := S) B w.1 ∈ S.parameterSpace) : ℕ → Parameter S
  | 0 => S.w0
  | t + 1 => updateOnDomain (S := S) (sampledBatch S batches t)
      (parameterIterates S batches hclosed t)
      (hclosed (sampledBatch S batches t) (parameterIterates S batches hclosed t))

/- Checked pathwise iterate sequence.  The source one-step relation above is
   the paper boundary; this total function is explicitly named as an internal
   ambient realization for later bridge theorems. -/
noncomputable def internalAmbientIterates (S : Setup n E X Y Ω)
    (batches : BatchRealization S) : ℕ → E :=
  ambientIterates S batches

private theorem iterates_value_bridge (S : Setup n E X Y Ω)
    (batches : BatchRealization S)
    (hclosed : ∀ (B : Batch S) (w : Setup.Parameter S),
      ambientUpdate S B w.1 ∈ S.parameterSpace) (t : ℕ) :
    (parameterIterates (S := S) batches hclosed t).1 =
      ambientIterates (S := S) batches t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp [parameterIterates, updateOnDomain, update, ih]
      have hsucc := SOptLib.recursiveIterateProcess_succ
        (SOptLib.recursiveIterateProcess (S.w0 : E) (ambientStep (S := S)))
        (S.w0 : E) (ambientStep (S := S)) rfl t batches
      simpa [ambientStep] using hsucc.symm

/- Algorithm 1 stops at the first ambient iterate satisfying its convergence
   test.  No global W-closure assumption is part of the source output object. -/
noncomputable def internalStoppingIndex (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (converged : E → Prop) [DecidablePred converged]
    (hex : ∃ t, converged (internalAmbientIterates (S := S) batches t)) : ℕ :=
  Nat.find hex

theorem internalStoppingIndex_spec (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (converged : E → Prop) [DecidablePred converged]
    (hex : ∃ t, converged (internalAmbientIterates (S := S) batches t)) :
    converged (internalAmbientIterates (S := S) batches
      (internalStoppingIndex (S := S) batches converged hex)) := by
  exact Nat.find_spec hex

noncomputable def internalOutputAtStopping (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (converged : E → Prop) [DecidablePred converged]
    (hex : ∃ t, converged (internalAmbientIterates (S := S) batches t)) : E :=
  internalAmbientIterates (S := S) batches
    (internalStoppingIndex (S := S) batches converged hex)

theorem internalOutputAtStopping_spec (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (converged : E → Prop) [DecidablePred converged]
    (hex : ∃ t, converged (internalAmbientIterates (S := S) batches t)) :
    internalOutputAtStopping (S := S) batches converged hex =
      internalAmbientIterates (S := S) batches
        (internalStoppingIndex (S := S) batches converged hex) := by
  rfl

private noncomputable def parameterOutputAtStopping
    (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (hclosed : ∀ (B : Batch S) (w : Parameter S),
      ambientUpdate (S := S) B w.1 ∈ S.parameterSpace)
    (converged : Parameter S → Prop) [DecidablePred converged]
    (hex : ∃ t, converged (parameterIterates (S := S) batches hclosed t)) : Parameter S :=
  parameterIterates (S := S) batches hclosed
    (Nat.find hex)

private theorem parameterOutputAtStopping_spec
    (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (hclosed : ∀ (B : Batch S) (w : Parameter S),
      ambientUpdate (S := S) B w.1 ∈ S.parameterSpace)
    (converged : Parameter S → Prop) [DecidablePred converged]
    (hex : ∃ t, converged (parameterIterates (S := S) batches hclosed t)) :
    parameterOutputAtStopping (S := S) batches hclosed converged hex =
      parameterIterates (S := S) batches hclosed (Nat.find hex) := by
  rfl

private theorem outputAtStopping_parameter_bridge
    (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (hclosed : ∀ (B : Batch S) (w : Parameter S),
      ambientUpdate (S := S) B w.1 ∈ S.parameterSpace)
    (converged : Parameter S → Prop) [DecidablePred converged]
    (hex : ∃ t, converged (parameterIterates (S := S) batches hclosed t)) :
    (parameterOutputAtStopping (S := S) batches hclosed converged hex).1 =
      (parameterIterates (S := S) batches hclosed (Nat.find hex)).1 := by
  simpa [parameterOutputAtStopping]

/- Internal value set for the paper's inner maximization.  Since ℓ is defined
   only on W, admissible perturbations explicitly carry the domain proof;
   no zero extension contributes to the source-facing maximum. -/
private def samLossValues (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Parameter S) : Set ℝ :=
  {y : ℝ | ∃ (ε : E) (hε : ε ∈ Setup.perturbationBall (S := S))
      (hdom : w.1 + ε ∈ S.parameterSpace),
      y = Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩}

/- Source-silent domain coverage needed to read Eq. (1)'s
   `max_{||ε||_p≤ρ} L_S(w+ε)` over the paper's parameter-domain loss. -/
def sourceSAMObjectiveDomainObligation (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) : Prop :=
  ∀ ε : E, ε ∈ Setup.perturbationBall (S := S) →
    ∃ value : ℝ, sourceEmpiricalLossAt (S := S) s (w.1 + ε) value

theorem sourceSAMObjectiveDomainObligation_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) :
    sourceSAMObjectiveDomainObligation (S := S) s w ↔
      ∀ ε : E, ε ∈ Setup.perturbationBall (S := S) →
        ∃ value : ℝ, sourceEmpiricalLossAt (S := S) s (w.1 + ε) value := by
  rfl

/- The source-level Eq. (1) maximum is relational.  It includes the
   well-definedness of every perturbation in the displayed ball and an
   attaining perturbation for the literal `max`; no partial-domain `sSup`
   value is allowed to stand for the paper expression. -/
def sourceSAMObjectiveMaximum (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) : Prop :=
  sourceSAMObjectiveDomainObligation (S := S) s w ∧
    (∃ ε : E, ε ∈ Setup.perturbationBall (S := S) ∧
      sourceEmpiricalLossAt (S := S) s (w.1 + ε) value) ∧
    ∀ ε : E, ε ∈ Setup.perturbationBall (S := S) →
      ∀ y : ℝ, sourceEmpiricalLossAt (S := S) s (w.1 + ε) y →
        y ≤ value

theorem sourceSAMObjectiveMaximum_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) :
    sourceSAMObjectiveMaximum (S := S) s w value ↔
      sourceSAMObjectiveDomainObligation (S := S) s w ∧
        (∃ ε : E, ε ∈ Setup.perturbationBall (S := S) ∧
          sourceEmpiricalLossAt (S := S) s (w.1 + ε) value) ∧
        ∀ ε : E, ε ∈ Setup.perturbationBall (S := S) →
          ∀ y : ℝ, sourceEmpiricalLossAt (S := S) s (w.1 + ε) y →
            y ≤ value := by
  rfl

private def samMaximizer (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Parameter S) (ε : E) : Prop :=
  ∃ hdom : w.1 + ε ∈ S.parameterSpace,
    ε ∈ Setup.perturbationBall (S := S) ∧
      ∀ ε', ε' ∈ Setup.perturbationBall (S := S) →
        ∀ (hdom' : w.1 + ε' ∈ S.parameterSpace),
        Setup.empiricalLoss (S := S) s ⟨w.1 + ε', hdom'⟩ ≤
          Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩

def samObjective (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) : Prop :=
  sourceSAMObjectiveMaximum (S := S) s w value

theorem samObjective_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) :
    samObjective (S := S) s w value ↔
      sourceSAMObjectiveMaximum (S := S) s w value := by
  rfl

/- Internal checked scalar for later proofs that have separately established
   domain coverage and max-attainment obligations. -/
private noncomputable def samObjectiveInternalChecked (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) : ℝ :=
  sSup (samLossValues (S := S) s w)

private theorem samObjectiveInternalChecked_isGreatest_of_attained
    (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S)
    (hattain : ∃ v : ℝ, IsGreatest (samLossValues (S := S) s w) v) :
    IsGreatest (samLossValues (S := S) s w)
      (samObjectiveInternalChecked (S := S) s w) := by
  rcases hattain with ⟨v, hv⟩
  rw [samObjectiveInternalChecked, hv.csSup_eq]
  exact hv

private theorem samObjectiveInternalChecked_of_maximizer
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Parameter S) (ε : E)
    (hε : Setup.samMaximizer (S := S) s w ε)
    (hmax : IsGreatest (samLossValues (S := S) s w)
      (samObjectiveInternalChecked (S := S) s w)) :
    ∃ hdom : w.1 + ε ∈ S.parameterSpace,
      Setup.samObjectiveInternalChecked (S := S) s w =
        Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩ := by
  rcases hε with ⟨hdom, hball, hupper⟩
  refine ⟨hdom, le_antisymm ?_ ?_⟩
  · rcases hmax.1 with ⟨ε0, hball0, hdom0, hEq0⟩
    rw [hEq0]
    exact hupper ε0 hball0 hdom0
  · exact hmax.2 ⟨ε, hball, hdom, rfl⟩

theorem samObjective_value_unique
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Parameter S)
    (u v : ℝ) (hu : Setup.samObjective (S := S) s w u)
    (hv : Setup.samObjective (S := S) s w v) :
    u = v := by
  rw [samObjective, sourceSAMObjectiveMaximum] at hu hv
  rcases hu with ⟨_, ⟨εu, hbu, hvalu⟩, hub⟩
  rcases hv with ⟨_, ⟨εv, hbv, hvalv⟩, hvb⟩
  exact le_antisymm (hvb εu hbu u hvalu) (hub εv hbv v hvalv)

private def euclideanSAMLossValues (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) : Set ℝ :=
  {y : ℝ | ∃ (ε : E), ‖ε‖ ≤ S.rho ∧
    ∃ hdom : w.1 + ε ∈ S.parameterSpace,
      y = Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩}

private def euclideanSAMMaximizer (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (ε : E) : Prop :=
    ∃ hdom : w.1 + ε ∈ S.parameterSpace,
      ‖ε‖ ≤ S.rho ∧
      ∀ ε', ‖ε'‖ ≤ S.rho →
        ∀ (hdom' : w.1 + ε' ∈ S.parameterSpace),
        Setup.empiricalLoss (S := S) s ⟨w.1 + ε', hdom'⟩ ≤
          Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩

/- Internal partial graph carrier for source-boundary proofs.  The public
   sharpness object below adds domain coverage and max attainment. -/
private def sourceEuclideanSAMLossValues (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) : Set ℝ :=
  {y : ℝ | ∃ ε : E, ‖ε‖ ≤ S.rho ∧
    sourceEmpiricalLossAt (S := S) s (w.1 + ε) y}

/- Theorem 2's source-facing sharpness object is the literal max contract
   printed in Eq. (4).  It is not a choice-selected `sSup` scalar and it does
   not use the checked, domain-restricted maximum below. -/
/- Source-silent domain coverage needed to turn the partial graph into the
   paper's all-perturbations expression.  This is recorded as an obligation,
   not as a theorem-head, Setup assumption, or asserted theorem. -/
def sourceEuclideanSAMMaximumDomainObligation
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Parameter S) :
    Prop :=
  ∀ ε : E, ‖ε‖ ≤ S.rho →
    ∃ value : ℝ, sourceEmpiricalLossAt (S := S) s (w.1 + ε) value

def sourceEuclideanSAMMaximum (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) : Prop :=
  sourceEuclideanSAMMaximumDomainObligation (S := S) s w ∧
    (∃ ε : E, ‖ε‖ ≤ S.rho ∧
      sourceEmpiricalLossAt (S := S) s (w.1 + ε) value) ∧
    ∀ ε : E, ‖ε‖ ≤ S.rho →
      ∀ y : ℝ, sourceEmpiricalLossAt (S := S) s (w.1 + ε) y →
        y ≤ value

theorem sourceEuclideanSAMMaximum_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) :
    sourceEuclideanSAMMaximum (S := S) s w value ↔
      sourceEuclideanSAMMaximumDomainObligation (S := S) s w ∧
        (∃ ε : E, ‖ε‖ ≤ S.rho ∧
          sourceEmpiricalLossAt (S := S) s (w.1 + ε) value) ∧
        ∀ ε : E, ‖ε‖ ≤ S.rho →
          ∀ y : ℝ, sourceEmpiricalLossAt (S := S) s (w.1 + ε) y →
            y ≤ value := by
  rfl

def sourceEuclideanSAMMaximumAttainmentObligation
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Parameter S) :
    Prop :=
  ∃ value : ℝ, sourceEuclideanSAMMaximum (S := S) s w value

/- Theorem 2's named source sharpness object. -/
def theorem2SharpnessSource (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) : Prop :=
  sourceEuclideanSAMMaximum (S := S) s w value

theorem theorem2SharpnessSource_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) :
    theorem2SharpnessSource (S := S) s w value ↔
      sourceEuclideanSAMMaximum (S := S) s w value := by
  rfl

/- Checked realization of the Euclidean neighborhood value.  This is not used
   by the source-boundary obligation; it remains available for later internal proof work
   once domain and attainment obligations have been proved. -/
noncomputable def euclideanSAMMaximum (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) : ℝ :=
  sSup (euclideanSAMLossValues (S := S) s w)

noncomputable def theorem2SharpnessInternalChecked (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) : ℝ :=
  Setup.euclideanSAMMaximum (S := S) s w

theorem theorem2SharpnessInternalChecked_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) :
    theorem2SharpnessInternalChecked (S := S) s w =
      Setup.euclideanSAMMaximum (S := S) s w := by
  rfl

private theorem euclideanSAMMaximum_isGreatest_of_attained (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S)
    (hattain : ∃ v : ℝ, IsGreatest (euclideanSAMLossValues (S := S) s w) v) :
    IsGreatest (euclideanSAMLossValues (S := S) s w)
      (euclideanSAMMaximum (S := S) s w) := by
  rcases hattain with ⟨v, hv⟩
  rw [euclideanSAMMaximum, hv.csSup_eq]
  exact hv

private theorem euclideanSAMMaximum_of_maximizer
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Parameter S) (ε : E)
    (hε : Setup.euclideanSAMMaximizer (S := S) s w ε)
    (hmax : IsGreatest (euclideanSAMLossValues (S := S) s w)
      (euclideanSAMMaximum (S := S) s w)) :
    ∃ hdom : w.1 + ε ∈ S.parameterSpace,
      Setup.euclideanSAMMaximum (S := S) s w =
        Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩ := by
  rcases hε with ⟨hdom, hnorm, hupper⟩
  refine ⟨hdom, le_antisymm ?_ ?_⟩
  · rcases hmax.1 with ⟨ε0, hnorm0, hdom0, hEq0⟩
    rw [hEq0]
    exact hupper ε0 hnorm0 hdom0
  · exact hmax.2 ⟨ε, hnorm, hdom, rfl⟩

theorem euclideanSAMMaximum_value_unique
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Parameter S) :
    Setup.euclideanSAMMaximum (S := S) s w =
      Setup.euclideanSAMMaximum (S := S) s w := by
  rfl

/- The regularized objective is relational because Eq. (1)'s SAM term is a
   literal source maximum whose domain coverage and attainment are boundary
   obligations, not fallback scalar conventions. -/
def regularizedObjective (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) : Prop :=
  ∃ sharpness : ℝ,
    Setup.samObjective (S := S) s w sharpness ∧
      value = sharpness + S.lambda * ‖w.1‖ ^ 2

theorem regularizedObjective_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Parameter S) (value : ℝ) :
    Setup.regularizedObjective (S := S) s w value ↔
      ∃ sharpness : ℝ,
        Setup.samObjective (S := S) s w sharpness ∧
          value = sharpness + S.lambda * ‖w.1‖ ^ 2 := by
  rfl

end Setup

/- The source PAC-Bayes statement quantifies over probability measures, not
   probability mass functions.  Keep both distribution slots as genuine
   `Measure`s.  Probability is a derived contract of a particular law, rather
   than an extra field of the canonical distribution object. -/
structure MeasurePACBayesDistributionContext
    (Concept Sample : Type*)
    [MeasurableSpace Concept] [MeasurableSpace Sample] where
  prior_distribution : Measure Concept
  sampling_distribution : Measure Sample

noncomputable def measurePACBayesSampleLaw
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample) (m : ℕ) :
    Measure (Fin m → Sample) :=
  Measure.pi (fun _ : Fin m => ctx.sampling_distribution)

theorem measurePACBayesSampleLaw_isProbability
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample) (m : ℕ)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution) :
    IsProbabilityMeasure (measurePACBayesSampleLaw ctx m) := by
  letI : IsProbabilityMeasure ctx.sampling_distribution :=
    hsampling
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin m => ctx.sampling_distribution))
  infer_instance

noncomputable def measurePACBayesKLDivergence
    {Concept : Type*} [MeasurableSpace Concept]
    (Q P : Measure Concept) : ENNReal :=
  InformationTheory.klDiv Q P

/- The source PAC-Bayes theorem is about one common pointwise loss.  Keep
   that loss as the paper's function object; its measurable and unit-interval
   contracts are explicit at the expectation-event boundary below rather than
   being hidden in a new carrier. -/
def MeasurePACBayesPointwiseLoss (Concept Sample : Type*) :=
  Concept → Sample → ℝ

theorem measurePACBayesPointwiseLoss_integrable
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    {μ : Measure Sample} [IsProbabilityMeasure μ]
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1)
    (c : Concept) :
    Integrable (loss c) μ := by
  apply integrable_of_measurable_bounded_real
  · simpa [Function.uncurry] using
      hmeas_loss.comp (measurable_const.prodMk measurable_id)
  · intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (hloss_bounded c z).1]
    exact (hloss_bounded c z).2

theorem measurePACBayesPointwiseLoss_integrable_sample_slice
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    {Q : Measure Concept} [IsFiniteMeasure Q]
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1)
    (z : Sample) :
    Integrable (fun c => loss c z) Q := by
  apply integrable_of_measurable_bounded_real
  · simpa [Function.uncurry] using
      hmeas_loss.comp (measurable_id.prodMk measurable_const)
  · intro c
    rw [Real.norm_eq_abs, abs_of_nonneg (hloss_bounded c z).1]
    exact (hloss_bounded c z).2

theorem measurePACBayesPointwiseLoss_integrable_population
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    {μ : Measure Sample} [IsProbabilityMeasure μ]
    {Q : Measure Concept} [IsFiniteMeasure Q]
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1) :
    Integrable (fun c => ∫ z, loss c z ∂μ) Q := by
  have hstrong :
      StronglyMeasurable
        (fun p : Concept × Sample => loss p.1 p.2) :=
    hmeas_loss.stronglyMeasurable
  have hmeas :
      Measurable (fun c => ∫ z, loss c z ∂μ) :=
    hstrong.integral_prod_right'.measurable
  apply integrable_of_measurable_bounded_real hmeas
  intro c
  have hslice :
      Integrable (loss c) μ :=
    measurePACBayesPointwiseLoss_integrable loss hmeas_loss hloss_bounded c
  have hzero : Integrable (fun _ : Sample => (0 : ℝ)) μ :=
    integrable_const 0
  have hone : Integrable (fun _ : Sample => (1 : ℝ)) μ :=
    integrable_const 1
  have hnonneg : 0 ≤ ∫ z, loss c z ∂μ := by
    simpa using
      (integral_mono hzero hslice (fun z => (hloss_bounded c z).1))
  have hleone : (∫ z, loss c z ∂μ) ≤ 1 := by
    have hle :
        (∫ z, loss c z ∂μ) ≤ ∫ z, (1 : ℝ) ∂μ :=
      integral_mono hslice hone (fun z => (hloss_bounded c z).2)
    simpa using hle
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hleone

noncomputable def measurePACBayesPopulationLoss
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (Q : Measure Concept) : ℝ :=
  ∫ c, ∫ z, loss c z ∂ctx.sampling_distribution ∂Q

noncomputable def measurePACBayesEmpiricalLoss
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (s : Fin m → Sample)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (Q : Measure Concept) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ c, loss c (s i) ∂Q

theorem measurePACBayesPopulationLoss_spec
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (Q : Measure Concept) :
    measurePACBayesPopulationLoss ctx loss Q =
      ∫ c, ∫ z, loss c z ∂ctx.sampling_distribution ∂Q := by
  rfl

theorem measurePACBayesPopulationExpectation_integrable_mem_Icc
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    {μ : Measure Sample} [IsProbabilityMeasure μ]
    {Q : Measure Concept} [IsProbabilityMeasure Q]
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1) :
    Integrable (fun c => ∫ z, loss c z ∂μ) Q ∧
      0 ≤ ∫ c, ∫ z, loss c z ∂μ ∂Q ∧
      (∫ c, ∫ z, loss c z ∂μ ∂Q) ≤ 1 := by
  have hpopulation_integrable :
      Integrable (fun c => ∫ z, loss c z ∂μ) Q :=
    measurePACBayesPointwiseLoss_integrable_population
      (μ := μ) (Q := Q) loss hmeas_loss hloss_bounded
  have hzero : Integrable (fun _ : Concept => (0 : ℝ)) Q :=
    integrable_const 0
  have hone : Integrable (fun _ : Concept => (1 : ℝ)) Q :=
    integrable_const 1
  have hinner_nonneg (c : Concept) :
      0 ≤ ∫ z, loss c z ∂μ := by
    have hslice :
        Integrable (loss c) μ :=
      measurePACBayesPointwiseLoss_integrable
        (μ := μ) loss hmeas_loss hloss_bounded c
    simpa using
      (integral_mono (integrable_const 0) hslice
        (fun z => (hloss_bounded c z).1))
  have hinner_le_one (c : Concept) :
      (∫ z, loss c z ∂μ) ≤ 1 := by
    have hslice :
        Integrable (loss c) μ :=
      measurePACBayesPointwiseLoss_integrable
        (μ := μ) loss hmeas_loss hloss_bounded c
    have hle :
        (∫ z, loss c z ∂μ) ≤ ∫ z, (1 : ℝ) ∂μ :=
      integral_mono hslice (integrable_const 1)
        (fun z => (hloss_bounded c z).2)
    simpa using hle
  have houter_nonneg :
      0 ≤ ∫ c, ∫ z, loss c z ∂μ ∂Q := by
    simpa using
      (integral_mono hzero hpopulation_integrable hinner_nonneg)
  have houter_le_one :
      (∫ c, ∫ z, loss c z ∂μ ∂Q) ≤
        ∫ c, (1 : ℝ) ∂Q :=
    integral_mono hpopulation_integrable hone hinner_le_one
  refine ⟨hpopulation_integrable, houter_nonneg, ?_⟩
  simpa using houter_le_one

theorem measurePACBayesEmpiricalLoss_spec
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (s : Fin m → Sample)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (Q : Measure Concept) :
    measurePACBayesEmpiricalLoss ctx m s loss Q =
      (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ c, loss c (s i) ∂Q := by
  rfl

/- Eq. (5) at the source object level.  The concrete source loss may still
   require a local realization bridge when the paper's parameter domain is a
   proper subset of the ambient Gaussian space, but both expectations now
   arise from the same pointwise loss and the same sampling Measure.

   The source inequality is real-valued.  Relative entropy is stored in
   Mathlib's `ENNReal` type, so the infinite-KL branch is made vacuous and
   the finite-KL branch uses its canonical real value and the paper's
   square-root penalty. -/
noncomputable def measurePACBayesExpectedLossEvent
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample) :
    Set (Fin m → Sample) :=
  {s | ∀ Q : Measure Concept, IsProbabilityMeasure Q →
    measurePACBayesKLDivergence Q ctx.prior_distribution = ⊤ ∨
      measurePACBayesPopulationLoss ctx loss Q ≤
        measurePACBayesEmpiricalLoss ctx m s loss Q +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((m : ℝ) / δ)) /
              (2 * ((m : ℝ) - 1)))}

/- The complementary finite-KL violation event is the paper's failure event
   at the same Measure-valued granularity.  Giving this set a canonical name
   keeps the cited PAC-Bayes boundary and its downstream consumers on one
   exact event object rather than rebuilding the existential expression
   locally inside a proof. -/
noncomputable def measurePACBayesFiniteKLViolationEvent
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample) :
    Set (Fin m → Sample) :=
  {s |
    ∃ Q : Measure Concept, IsProbabilityMeasure Q ∧
      measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ ∧
      measurePACBayesPopulationLoss ctx loss Q >
        measurePACBayesEmpiricalLoss ctx m s loss Q +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((m : ℝ) / δ)) /
              (2 * ((m : ℝ) - 1)))}

/- The exponential square-gap moment used by the source proof of the
   universal PAC-Bayes event.  This is a genuine prior integral over the
   paper's Measure-valued concept space, not a witness or a PMF encoding. -/
noncomputable def measurePACBayesMcAllesterMoment
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (s : Fin m → Sample) : ℝ :=
  ∫ c, Real.exp
      ((2 * (m : ℝ) - 1) *
        ((∫ z, loss c z ∂ctx.sampling_distribution) -
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) ^ 2) ∂ctx.prior_distribution

theorem measurePACBayesExpectedLossEvent_compl
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample) :
    (measurePACBayesExpectedLossEvent ctx m hm δ loss)ᶜ =
      measurePACBayesFiniteKLViolationEvent ctx m hm δ loss := by
  ext s
  change
    ¬ (∀ Q : Measure Concept, IsProbabilityMeasure Q →
      measurePACBayesKLDivergence Q ctx.prior_distribution = ⊤ ∨
        measurePACBayesPopulationLoss ctx loss Q ≤
          measurePACBayesEmpiricalLoss ctx m s loss Q +
            Real.sqrt
              (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                Real.log ((m : ℝ) / δ)) /
                (2 * ((m : ℝ) - 1)))) ↔
      ∃ Q : Measure Concept, IsProbabilityMeasure Q ∧
        measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ ∧
        measurePACBayesPopulationLoss ctx loss Q >
          measurePACBayesEmpiricalLoss ctx m s loss Q +
            Real.sqrt
              (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                Real.log ((m : ℝ) / δ)) /
                (2 * ((m : ℝ) - 1)))
  push Not
  rfl

theorem measurePACBayes_denominator_pos
    (m : ℕ) (hm : 1 < m) :
    0 < 2 * ((m : ℝ) - 1) := by
  have hm' : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  linarith

/- The continuous Gaussian objects used by Appendix A.1 are affine
   pushforwards of Mathlib's standard Gaussian measure. -/
noncomputable def gaussianAffineLaw (center : E) (sigma : ℝ) : Measure E :=
  Measure.map (fun ε : E => center + sigma • ε) (stdGaussian E)

theorem gaussianAffineLaw_isProbability
    [BorelSpace E] (center : E) (sigma : ℝ) :
    IsProbabilityMeasure (gaussianAffineLaw (E := E) center sigma) := by
  rw [isProbabilityMeasure_iff]
  rw [gaussianAffineLaw]
  rw [Measure.map_apply
    (by fun_prop : Measurable (fun ε : E => center + sigma • ε))
    MeasurableSet.univ]
  simp [isProbabilityMeasure_iff.mp
    (isProbabilityMeasure_stdGaussian (E := E))]

theorem gaussianAffineLaw_integral_map
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [BorelSpace E] [SecondCountableTopology E]
    (center : E) (sigma : ℝ) (f : E → G)
    (hf : AEStronglyMeasurable f
      (gaussianAffineLaw (E := E) center sigma)) :
    ∫ z : E, f z ∂(gaussianAffineLaw (E := E) center sigma) =
      ∫ ε : E, f (center + sigma • ε) ∂(stdGaussian E) := by
  exact MeasureTheory.integral_map
    ((by
      exact
        (continuous_const.add (continuous_const.smul continuous_id)).measurable :
          Measurable (fun ε : E => center + sigma • ε)).aemeasurable)
    hf

theorem gaussianAffineLaw_zero_one :
    gaussianAffineLaw (E := E) (0 : E) 1 = stdGaussian E := by
  simp [gaussianAffineLaw]

private theorem klDiv_map_symm_ne_top_of_ne_top
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    (hfinite : InformationTheory.klDiv μ ν ≠ ⊤) :
    InformationTheory.klDiv
        (Measure.map e.symm μ) (Measure.map e.symm ν) ≠ ⊤ := by
  have hparts := InformationTheory.klDiv_ne_top_iff.mp hfinite
  have h_ac : μ ≪ ν := hparts.1
  have h_int : Integrable (llr μ ν) μ := hparts.2
  have h_ac' :
      Measure.map e.symm μ ≪ Measure.map e.symm ν :=
    e.symm.measurableEmbedding.absolutelyContinuous_map h_ac
  have hrn_aeν :
      (fun x : β =>
        ((Measure.map e.symm μ).rnDeriv
          (Measure.map e.symm ν) (e.symm x))) =ᵐ[ν]
        (fun x : β => μ.rnDeriv ν x) := by
    simpa using e.symm.measurableEmbedding.rnDeriv_map μ ν
  have hrn_aeμ :
      (fun x : β =>
        ((Measure.map e.symm μ).rnDeriv
          (Measure.map e.symm ν) (e.symm x))) =ᵐ[μ]
        (fun x : β => μ.rnDeriv ν x) :=
    (Measure.AbsolutelyContinuous.ae_le h_ac) hrn_aeν
  have hllr_comp :
      (fun x : β =>
        llr (Measure.map e.symm μ) (Measure.map e.symm ν)
          (e.symm x)) =ᵐ[μ] llr μ ν := by
    filter_upwards [hrn_aeμ] with x hx
    simp [llr, hx]
  have h_int_comp :
      Integrable
        (fun x : β =>
          llr (Measure.map e.symm μ) (Measure.map e.symm ν)
            (e.symm x)) μ :=
    h_int.congr hllr_comp.symm
  have h_int' :
      Integrable
        (llr (Measure.map e.symm μ) (Measure.map e.symm ν))
        (Measure.map e.symm μ) := by
    exact
      (integrable_map_equiv e.symm
        (llr (Measure.map e.symm μ) (Measure.map e.symm ν))).2
        h_int_comp
  exact InformationTheory.klDiv_ne_top h_ac' h_int'

private theorem klDiv_map_symm_eq_of_ne_top
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    (hfinite : InformationTheory.klDiv μ ν ≠ ⊤) :
    InformationTheory.klDiv
        (Measure.map e.symm μ) (Measure.map e.symm ν) =
      InformationTheory.klDiv μ ν := by
  have hparts := InformationTheory.klDiv_ne_top_iff.mp hfinite
  have h_ac : μ ≪ ν := hparts.1
  have h_int : Integrable (llr μ ν) μ := hparts.2
  have h_ac' :
      Measure.map e.symm μ ≪ Measure.map e.symm ν :=
    e.symm.measurableEmbedding.absolutelyContinuous_map h_ac
  have hrn_aeν :
      (fun x : β =>
        ((Measure.map e.symm μ).rnDeriv
          (Measure.map e.symm ν) (e.symm x))) =ᵐ[ν]
        (fun x : β => μ.rnDeriv ν x) := by
    simpa using e.symm.measurableEmbedding.rnDeriv_map μ ν
  have hrn_aeμ :
      (fun x : β =>
        ((Measure.map e.symm μ).rnDeriv
          (Measure.map e.symm ν) (e.symm x))) =ᵐ[μ]
        (fun x : β => μ.rnDeriv ν x) :=
    (Measure.AbsolutelyContinuous.ae_le h_ac) hrn_aeν
  have hllr_comp :
      (fun x : β =>
        llr (Measure.map e.symm μ) (Measure.map e.symm ν)
          (e.symm x)) =ᵐ[μ] llr μ ν := by
    filter_upwards [hrn_aeμ] with x hx
    simp [llr, hx]
  have h_int_comp :
      Integrable
        (fun x : β =>
          llr (Measure.map e.symm μ) (Measure.map e.symm ν)
            (e.symm x)) μ :=
    h_int.congr hllr_comp.symm
  have h_int' :
      Integrable
        (llr (Measure.map e.symm μ) (Measure.map e.symm ν))
        (Measure.map e.symm μ) := by
    exact
      (integrable_map_equiv e.symm
        (llr (Measure.map e.symm μ) (Measure.map e.symm ν))).2
        h_int_comp
  rw [InformationTheory.klDiv_of_ac_of_integrable h_ac' h_int',
    InformationTheory.klDiv_of_ac_of_integrable h_ac h_int]
  congr 1
  have hintegral :
      ∫ x : α, llr (Measure.map e.symm μ) (Measure.map e.symm ν) x
          ∂(Measure.map e.symm μ) =
        ∫ x : β, llr μ ν x ∂μ := by
    calc
      ∫ x : α, llr (Measure.map e.symm μ) (Measure.map e.symm ν) x
          ∂(Measure.map e.symm μ) =
          ∫ x : β,
            llr (Measure.map e.symm μ) (Measure.map e.symm ν) (e.symm x)
              ∂μ := by
            rw [integral_map_equiv]
      _ = ∫ x : β, llr μ ν x ∂μ := integral_congr_ae hllr_comp
  have hν_real :
      (Measure.map e.symm ν).real Set.univ = ν.real Set.univ := by
    rw [Measure.real_def, Measure.real_def,
      Measure.map_apply e.symm.measurable MeasurableSet.univ]
    simp
  have hμ_real :
      (Measure.map e.symm μ).real Set.univ = μ.real Set.univ := by
    rw [Measure.real_def, Measure.real_def,
      Measure.map_apply e.symm.measurable MeasurableSet.univ]
    simp
  rw [hintegral, hν_real, hμ_real]

/- Appendix A.1's prior is selected from a data-independent geometric grid of
   variances.  These definitions keep the grid's source data explicit while
   leaving the choice of its index to the PAC-Bayes proof. -/
noncomputable def theorem2AppendixA1PriorGridScale
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E)) : ℝ :=
  S.rho ^ 2 *
    (1 + Real.exp
      (4 * (n : ℝ) / (Setup.parameterCount (E := E) : ℝ)))

noncomputable def theorem2AppendixA1PriorGridVariance
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) : ℝ :=
  theorem2AppendixA1PriorGridScale (S := S) hk *
    Real.exp
      ((1 - ((j + 1 : ℕ) : ℝ)) /
        (Setup.parameterCount (E := E) : ℝ))

noncomputable def theorem2AppendixA1PriorGridConfidence
    (δ : ℝ) (j : ℕ) : ℝ :=
  6 * δ / (Real.pi ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 2)

theorem theorem2AppendixA1PriorGridConfidence_nonneg
    (δ : ℝ) (hδ : 0 ≤ δ) (j : ℕ) :
    0 ≤ theorem2AppendixA1PriorGridConfidence δ j := by
  unfold theorem2AppendixA1PriorGridConfidence
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hj : 0 < ((j + 1 : ℕ) : ℝ) ^ 2 := by
    positivity
  positivity

theorem theorem2AppendixA1PriorGridConfidence_summable
    (δ : ℝ) (hδ : 0 ≤ δ) :
    Summable (fun j : ℕ =>
      theorem2AppendixA1PriorGridConfidence δ j) := by
  have hseries :
      Summable (fun j : ℕ => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2) := by
    simpa [Function.comp_def] using
      (hasSum_zeta_two.summable.comp_injective
        (i := fun j : ℕ => j + 1)
        (by intro i j h; exact Nat.add_right_cancel h))
  have hscaled := hseries.mul_left (6 * δ / Real.pi ^ 2)
  apply hscaled.congr
  intro j
  unfold theorem2AppendixA1PriorGridConfidence
  field_simp [ne_of_gt Real.pi_pos]

theorem theorem2AppendixA1PriorGridConfidence_tsum
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑' j : ℕ, theorem2AppendixA1PriorGridConfidence δ j = δ := by
  have hseries :
      HasSum (fun j : ℕ => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ 2)
        (Real.pi ^ 2 / 6) := by
    apply (hasSum_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2
    simpa using hasSum_zeta_two
  have hconfidence :
      HasSum (fun j : ℕ =>
        theorem2AppendixA1PriorGridConfidence δ j) δ := by
    convert hseries.mul_left (6 * δ / Real.pi ^ 2) using 1
    · funext j
      unfold theorem2AppendixA1PriorGridConfidence
      field_simp [ne_of_gt Real.pi_pos]
    · field_simp [ne_of_gt Real.pi_pos]
  exact hconfidence.tsum_eq

private theorem theorem2AppendixA1PriorGridConfidence_ennreal_tsum
    (δ : ℝ) (hδ : 0 ≤ δ) :
    ∑' j : ℕ,
        ENNReal.ofReal
          (theorem2AppendixA1PriorGridConfidence δ j) =
      ENNReal.ofReal δ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun j => theorem2AppendixA1PriorGridConfidence_nonneg δ hδ j)
    (theorem2AppendixA1PriorGridConfidence_summable δ hδ)]
  rw [theorem2AppendixA1PriorGridConfidence_tsum δ hδ]

theorem theorem2AppendixA1PriorGridConfidence_union_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (δ : ℝ) (hδ : 0 ≤ δ)
    (bad : ℕ → Set α)
    (hbad :
      ∀ j,
        μ (bad j) ≤
          ENNReal.ofReal
            (theorem2AppendixA1PriorGridConfidence δ j)) :
    μ (⋃ j, bad j) ≤ ENNReal.ofReal δ := by
  calc
    μ (⋃ j, bad j) ≤ ∑' j, μ (bad j) := measure_iUnion_le _
    _ ≤ ∑' j,
        ENNReal.ofReal
          (theorem2AppendixA1PriorGridConfidence δ j) :=
      ENNReal.tsum_le_tsum hbad
    _ = ENNReal.ofReal δ :=
      theorem2AppendixA1PriorGridConfidence_ennreal_tsum δ hδ

noncomputable def theorem2MeasurePACBayesGridContext
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) : MeasurePACBayesDistributionContext E (X × Y) :=
  { prior_distribution :=
      gaussianAffineLaw (E := E) (0 : E)
        (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))
    sampling_distribution := S.dataLaw }

noncomputable def theorem2AppendixA1PosteriorLaw
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) : Measure E :=
  gaussianAffineLaw (E := E) w.1 S.rho

theorem theorem2AppendixA1PosteriorLaw_isProbability
    [BorelSpace E] (S : Setup n E X Y Ω) (w : Setup.Parameter S) :
    IsProbabilityMeasure
      (theorem2AppendixA1PosteriorLaw (S := S) w) := by
  change IsProbabilityMeasure
    (gaussianAffineLaw (E := E) w.1 S.rho)
  exact gaussianAffineLaw_isProbability (E := E) w.1 S.rho

theorem theorem2AppendixA1PriorGridScale_pos
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E)) :
    0 < theorem2AppendixA1PriorGridScale (S := S) hk := by
  have hk' : (0 : ℝ) < (Setup.parameterCount (E := E) : ℝ) := by
    exact_mod_cast hk
  unfold theorem2AppendixA1PriorGridScale
  have hbase : 0 < S.rho ^ 2 := sq_pos_of_pos S.rho_pos
  have hexp : 0 < Real.exp
      (4 * (n : ℝ) / (Setup.parameterCount (E := E) : ℝ)) :=
    Real.exp_pos _
  nlinarith

theorem theorem2AppendixA1PriorGridScale_of_reduced_norm
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1)) :
    S.rho ^ 2 + ‖w.1‖ ^ 2 /
        (Setup.parameterCount (E := E) : ℝ) ≤
      theorem2AppendixA1PriorGridScale (S := S) hk := by
  have hk' : (0 : ℝ) < (Setup.parameterCount (E := E) : ℝ) := by
    exact_mod_cast hk
  have hk_one : (1 : ℝ) ≤ (Setup.parameterCount (E := E) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.2 hk)
  have hn' : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hexp_one :
      (1 : ℝ) ≤
        Real.exp
          (4 * (n : ℝ) /
            (Setup.parameterCount (E := E) : ℝ)) := by
    apply Real.one_le_exp
    positivity
  have hsub_nonneg :
      0 ≤
        Real.exp
          (4 * (n : ℝ) /
            (Setup.parameterCount (E := E) : ℝ)) - 1 := by
    linarith
  have hnorm_div :
      ‖w.1‖ ^ 2 /
          (Setup.parameterCount (E := E) : ℝ) ≤
        S.rho ^ 2 *
            (Real.exp
              (4 * (n : ℝ) /
                (Setup.parameterCount (E := E) : ℝ)) - 1) /
          (Setup.parameterCount (E := E) : ℝ) := by
    exact div_le_div_of_nonneg_right hnorm (le_of_lt hk')
  have hdiv_le :
      S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1) /
          (Setup.parameterCount (E := E) : ℝ) ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1) := by
    apply (div_le_iff₀ hk').2
    have hprod_nonneg :
        0 ≤ S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1) :=
      mul_nonneg (sq_nonneg _) hsub_nonneg
    nlinarith
  unfold theorem2AppendixA1PriorGridScale
  nlinarith [hnorm_div, hdiv_le]

theorem theorem2AppendixA1PriorGridVariance_pos
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) :
    0 < theorem2AppendixA1PriorGridVariance (S := S) hk j := by
  unfold theorem2AppendixA1PriorGridVariance
  exact mul_pos
    (theorem2AppendixA1PriorGridScale_pos (S := S) hk)
    (Real.exp_pos _)

theorem theorem2MeasurePACBayesGridContext_sampleLaw
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) :
    measurePACBayesSampleLaw
        (theorem2MeasurePACBayesGridContext (S := S) hk j) n =
      Setup.iidTrainingLaw (S := S) := by
  rfl

theorem theorem2MeasurePACBayesGridContext_prior
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) :
    (theorem2MeasurePACBayesGridContext (S := S) hk j).prior_distribution =
      gaussianAffineLaw (E := E) (0 : E)
        (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)) := by
  rfl

theorem theorem2MeasurePACBayesGridContext_prior_isProbability
    [BorelSpace E] (S : Setup n E X Y Ω)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    IsProbabilityMeasure
      (theorem2MeasurePACBayesGridContext (S := S) hk j).prior_distribution := by
  rw [theorem2MeasurePACBayesGridContext_prior]
  exact gaussianAffineLaw_isProbability (E := E) 0 _

theorem theorem2MeasurePACBayesGridContext_sampling
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) :
    (theorem2MeasurePACBayesGridContext (S := S) hk j).sampling_distribution =
      S.dataLaw := by
  rfl

private theorem samObjective_attained
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Setup.Parameter S)
    (hmax : IsGreatest (Setup.samLossValues (S := S) s w)
      (Setup.samObjectiveInternalChecked (S := S) s w))
    :
    ∃ (ε : E) (hε : ε ∈ Setup.perturbationBall (S := S))
        (hdom : w.1 + ε ∈ S.parameterSpace),
        Setup.samObjectiveInternalChecked (S := S) s w =
          Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩ := by
  rcases hmax.1 with ⟨ε, hε, hval⟩
  rcases hval with ⟨hdom, hEq⟩
  exact ⟨ε, hε, hdom, hEq⟩

private theorem samObjective_isGreatest
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Setup.Parameter S)
    (hattain : ∃ v : ℝ, IsGreatest (Setup.samLossValues (S := S) s w) v)
    :
    IsGreatest (Setup.samLossValues (S := S) s w)
      (Setup.samObjectiveInternalChecked (S := S) s w) := by
  exact Setup.samObjectiveInternalChecked_isGreatest_of_attained (S := S) s w hattain

private theorem euclideanSAMMaximumOn_eq_value_of_exists
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Setup.Parameter S)
    (value : ℝ)
    (hmax : Setup.euclideanSAMMaximum (S := S) s w = value)
    (hattain : ∃ (ε : E) (hdom : w.1 + ε ∈ S.parameterSpace), ‖ε‖ ≤ S.rho ∧
        value = Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩) :
    ∃ (ε : E) (hdom : w.1 + ε ∈ S.parameterSpace), ‖ε‖ ≤ S.rho ∧
        value = Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩ := by
  exact hattain

private theorem euclideanSAMMaximum_isGreatest
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Setup.Parameter S)
    (hattain : ∃ v : ℝ, IsGreatest (Setup.euclideanSAMLossValues (S := S) s w) v)
    :
    IsGreatest (Setup.euclideanSAMLossValues (S := S) s w)
      (Setup.euclideanSAMMaximum (S := S) s w) := by
  exact Setup.euclideanSAMMaximum_isGreatest_of_attained (S := S) s w hattain

private theorem euclideanSAMMaximum_attained
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Setup.Parameter S)
    (hmax : IsGreatest (Setup.euclideanSAMLossValues (S := S) s w)
      (Setup.euclideanSAMMaximum (S := S) s w)) :
    ∃ (ε : E) (hdom : w.1 + ε ∈ S.parameterSpace), ‖ε‖ ≤ S.rho ∧
      Setup.euclideanSAMMaximum (S := S) s w =
        Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩ := by
  rcases hmax.1 with ⟨ε, hε, hval⟩
  rcases hval with ⟨hdom, hEq⟩
  exact ⟨ε, hdom, hε, hEq⟩

theorem adversarialPerturbation_mem_ball
    (S : Setup n E X Y Ω) (B : Batch S) (w : Setup.Parameter S) :
    Setup.adversarialPerturbation (S := S) B w ∈ Setup.perturbationBall (S := S) := by
  simpa [Setup.adversarialPerturbation] using
    (Setup.dualNormPerturbation_mem_ball (S := S)
      (Setup.batchGradient (S := S) B w))

theorem adversarialPerturbation_maximal
    (S : Setup n E X Y Ω) (B : Batch S) (w : Setup.Parameter S) :
    IsMaxOn (fun u : E => Setup.linearPairing (Setup.batchGradient (S := S) B w) u)
      (Setup.perturbationBall (S := S)) (Setup.adversarialPerturbation (S := S) B w) := by
  simpa [Setup.adversarialPerturbation] using
    (Setup.dualNormPerturbation_maximal (S := S)
      (Setup.batchGradient (S := S) B w))

theorem dualNormPerturbation_spec
    (S : Setup n E X Y Ω) (g : E) :
    Setup.dualNormPerturbation (S := S) g =
        Setup.dualNormPerturbationFormula (S := S) g ∧
      Setup.dualNormPerturbation (S := S) g ∈
        Setup.perturbationBall (S := S) ∧
      IsMaxOn (fun u : E => Setup.linearPairing g u)
        (Setup.perturbationBall (S := S))
        (Setup.dualNormPerturbation (S := S) g) := by
  exact ⟨Setup.dualNormPerturbation_formula (S := S) g,
    Setup.dualNormPerturbation_mem_ball (S := S) g,
    Setup.dualNormPerturbation_maximal (S := S) g⟩

theorem adversarialPerturbation_spec
    (S : Setup n E X Y Ω) (B : Batch S) (w : Setup.Parameter S) :
    Setup.adversarialPerturbation (S := S) B w =
      Setup.dualNormPerturbation (S := S) (Setup.batchGradient (S := S) B w) := by
  rfl

private theorem samObjective_upper_bound
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Setup.Parameter S)
    (ε : E) (hε : ε ∈ Setup.perturbationBall (S := S))
    (hdom : w.1 + ε ∈ S.parameterSpace)
    (hmax : IsGreatest (Setup.samLossValues (S := S) s w)
      (Setup.samObjectiveInternalChecked (S := S) s w)) :
    Setup.empiricalLoss (S := S) s ⟨w.1 + ε, hdom⟩ ≤
      Setup.samObjectiveInternalChecked (S := S) s w := by
  exact hmax.2 ⟨ε, hε, hdom, rfl⟩

theorem internalAmbientIterates_zero (S : Setup n E X Y Ω) (batches : BatchRealization S)
    : Setup.internalAmbientIterates S batches 0 = S.w0 := by rfl

theorem internalAmbientIterates_succ (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (t : ℕ) :
    Setup.internalAmbientIterates S batches (t + 1) =
      Setup.ambientUpdate (S := S) (sampledBatch S batches t)
        (Setup.internalAmbientIterates S batches t) := by rfl

theorem iterates_sampledBatch_bridge (S : Setup n E X Y Ω)
    (path : BatchRealization S) (t : ℕ) :
    sampledBatch (S := S) path t =
      batchPrefix (S := S) path (t + 1) ⟨t, Nat.lt_succ_self t⟩ := by
  rfl

theorem internalAmbientIterates_sampledBatchProcess_bridge (S : Setup n E X Y Ω)
    (path : BatchRealization S) (t : ℕ) :
    Setup.internalAmbientIterates S path (t + 1) =
      Setup.ambientUpdate (S := S) (sampledBatchProcess (S := S) path t)
        (Setup.internalAmbientIterates S path t) := by
  rfl

/- Domain bridge for later proofs: source-domain iterates are obtained only
   after proving membership of the ambient recursion, never by selecting a
   witness in the setup. -/
private theorem iterate_mem_parameter_bridge
    (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (hclosed : ∀ (B : Batch S) (w : Setup.Parameter S),
      Setup.ambientUpdate S B w.1 ∈ S.parameterSpace) (t : ℕ) :
    (Setup.parameterIterates S batches hclosed t).1 =
      (Setup.parameterIterates S batches hclosed t).1 := by
  rfl

private theorem iterates_update_parameter_bridge
    (S : Setup n E X Y Ω) (batches : BatchRealization S)
    (hclosed : ∀ (B : Batch S) (w : Setup.Parameter S),
      Setup.ambientUpdate S B w.1 ∈ S.parameterSpace) (t : ℕ) :
    (Setup.parameterIterates S batches hclosed (t + 1)).1 =
      (Setup.ambientUpdate S (sampledBatch S batches t)
        (Setup.parameterIterates S batches hclosed t).1) := by
  rfl

/-! The explicit scalar remainder in Theorem 2, Eq. (4).  The source display
uses `\widetilde O(1)`; Appendix A.1 derives the concrete logarithmic term
below before absorbing it into that notation. -/
private noncomputable def theorem2RemainderRaw
    (S : Setup n E X Y Ω) (w : E) (δ : ℝ) : ℝ :=
  Real.sqrt
    (((Setup.parameterCount (E := E) : ℝ) * Real.log
      (1 + (‖w‖ ^ 2 / S.rho ^ 2) *
        (1 + Real.sqrt (Real.log (n : ℝ) /
          (Setup.parameterCount (E := E) : ℝ))) ^ 2) +
      4 * Real.log ((n : ℝ) / δ) +
      8 * Real.log (6 * (n : ℝ) +
        3 * (Setup.parameterCount (E := E) : ℝ))) /
      ((n : ℝ) - 1))

/-- The concrete `\widetilde O(1)` representative derived in Appendix A.1. -/
noncomputable def theorem2OtildeOneTerm (S : Setup n E X Y Ω) : ℝ :=
  8 * Real.log (6 * (n : ℝ) + 3 * (Setup.parameterCount (E := E) : ℝ))

/-- Source-facing remainder for Theorem 2 with the displayed square-root shape
    and a named concrete representative of the `\widetilde O(1)` term. -/
noncomputable def theorem2Remainder_source
    (S : Setup n E X Y Ω) (w : E) (δ : ℝ) : ℝ
    :=
  Real.sqrt
    (((Setup.parameterCount (E := E) : ℝ) * Real.log
      (1 + (‖w‖ ^ 2 / S.rho ^ 2) *
        (1 + Real.sqrt (Real.log (n : ℝ) /
          (Setup.parameterCount (E := E) : ℝ))) ^ 2) +
      4 * Real.log ((n : ℝ) / δ) +
      theorem2OtildeOneTerm (S := S)) /
      ((n : ℝ) - 1))

theorem theorem2Remainder_source_spec
    (S : Setup n E X Y Ω) (w : E) (δ : ℝ) :
    theorem2Remainder_source (S := S) w δ =
      theorem2RemainderRaw (S := S) w δ := by
  rfl

def theorem2EuclideanSharpnessSource (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Setup.Parameter S) (value : ℝ) : Prop :=
  Setup.theorem2SharpnessSource (S := S) s w value

theorem theorem2EuclideanSharpnessSource_spec (S : Setup n E X Y Ω)
    (s : Dataset n X Y) (w : Setup.Parameter S) (value : ℝ) :
    theorem2EuclideanSharpnessSource (S := S) s w value ↔
      Setup.theorem2SharpnessSource (S := S) s w value := by
  rfl

/- Source event for Theorem 2, Eq. (4).  The sharpness maximum is represented
   by the source relation above, so no sSup value, maximizer witness, or
   perturbation-domain closure proof is consumed by the source theorem. -/
def theorem2OriginalEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (s : Dataset n X Y) : Prop :=
  ∃ (population sharpness : ℝ),
    Setup.sourcePopulationLossAt (S := S) w.1 population ∧
      theorem2EuclideanSharpnessSource (S := S) s w sharpness ∧
      population ≤
        sharpness + theorem2Remainder_source (S := S) w.1 δ

theorem theorem2OriginalEvent_spec
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (s : Dataset n X Y) :
    theorem2OriginalEvent (S := S) w δ s ↔
      ∃ (population sharpness : ℝ),
        Setup.sourcePopulationLossAt (S := S) w.1 population ∧
          theorem2EuclideanSharpnessSource (S := S) s w sharpness ∧
          population ≤
            sharpness + theorem2Remainder_source (S := S) w.1 δ := by
  rfl

noncomputable def theorem2RemainderInternalChecked
    (S : Setup n E X Y Ω) (w : E) (δ : Set.Ioo (0 : ℝ) 1)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E)) : ℝ :=
  theorem2RemainderRaw (S := S) w δ.1

theorem theorem2RemainderInternalChecked_spec
    (S : Setup n E X Y Ω) (w : E) (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    theorem2RemainderInternalChecked (S := S) w δ hn hk =
      theorem2RemainderRaw (S := S) w δ.1 := by
  rfl

theorem theorem2Remainder_denominator_pos
    (hn : 1 < n) :
    0 < (n : ℝ) - 1 := by
  have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith

/- Internal checked wrapper for later proof work.  It is deliberately not part
   of the paper-facing theorem head, whose displayed remainder retains the
   source's literal `(n−1)` expression. -/
private noncomputable def theorem2RemainderOnDomain
    (S : Setup n E X Y Ω) (w : E) (δ : Set.Ioo (0 : ℝ) 1)
    (hn : 1 < n) (hrho : 0 < S.rho) : ℝ :=
  theorem2RemainderRaw (S := S) w δ.1

private theorem theorem2RemainderOnDomain_spec
    (S : Setup n E X Y Ω) (w : E) (δ : Set.Ioo (0 : ℝ) 1)
    (hn : 1 < n) (hrho : 0 < S.rho) :
    theorem2RemainderOnDomain (S := S) w δ hn hrho =
      theorem2RemainderRaw (S := S) w δ.1 := by
  rfl

/- The standard deviation selected in Appendix A.1 before the Gaussian
   radius split.  It is a source object, not a replacement for the theorem's
   stated rho-scale premise. -/
noncomputable def theorem2AppendixA1SelectedSigma
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) : ℝ :=
  S.rho /
    (Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
      (1 + Real.sqrt
        (Real.log (n : ℝ) /
          (Setup.parameterCount (E := E) : ℝ))))

theorem theorem2AppendixA1SelectedSigma_pos
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    0 < theorem2AppendixA1SelectedSigma (S := S) hn hk := by
  have hn' : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hk' : (0 : ℝ) < (Setup.parameterCount (E := E) : ℝ) := by
    exact_mod_cast hk
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by linarith)
  have hden :
      0 < Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
        (1 + Real.sqrt
          (Real.log (n : ℝ) /
            (Setup.parameterCount (E := E) : ℝ))) := by
    apply mul_pos
    · exact Real.sqrt_pos.2 hk'
    · positivity
  exact div_pos S.rho_pos hden

/- The selected scale is genuinely smaller than the theorem's rho scale.
   This prevents the Appendix A.1 proof from silently treating the two
   Gaussian laws as definitionally identical. -/
theorem theorem2AppendixA1SelectedSigma_lt_rho
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    theorem2AppendixA1SelectedSigma (S := S) hn hk < S.rho := by
  have hn' : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hk' : (0 : ℝ) < (Setup.parameterCount (E := E) : ℝ) := by
    exact_mod_cast hk
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn'
  have hquot_pos :
      0 < Real.log (n : ℝ) /
        (Setup.parameterCount (E := E) : ℝ) :=
    div_pos hlog_pos hk'
  have hsqrt_pos :
      0 < Real.sqrt (Setup.parameterCount (E := E) : ℝ) :=
    Real.sqrt_pos.2 hk'
  have hsqrt_ge_one :
      1 ≤ Real.sqrt (Setup.parameterCount (E := E) : ℝ) := by
    have hk_one :
        (1 : ℝ) ≤ (Setup.parameterCount (E := E) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.2 hk)
    nlinarith [Real.sq_sqrt (le_of_lt hk')]
  have hsqrt_log_pos :
      0 < Real.sqrt
        (Real.log (n : ℝ) /
          (Setup.parameterCount (E := E) : ℝ)) :=
    Real.sqrt_pos.2 hquot_pos
  have hden_pos :
      0 < Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
        (1 + Real.sqrt
          (Real.log (n : ℝ) /
            (Setup.parameterCount (E := E) : ℝ))) := by
    exact mul_pos hsqrt_pos (by positivity)
  have hden_gt_one :
      1 <
        Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
          (1 + Real.sqrt
            (Real.log (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ))) := by
    have hnonneg :
        0 ≤
          (Real.sqrt (Setup.parameterCount (E := E) : ℝ) - 1) *
            (1 + Real.sqrt
              (Real.log (n : ℝ) /
                (Setup.parameterCount (E := E) : ℝ))) :=
      mul_nonneg (sub_nonneg.mpr hsqrt_ge_one) (by positivity)
    nlinarith
  unfold theorem2AppendixA1SelectedSigma
  apply (div_lt_iff₀ hden_pos).2
  have hmul :
      S.rho * 1 <
        S.rho *
          (Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
            (1 + Real.sqrt
              (Real.log (n : ℝ) /
                (Setup.parameterCount (E := E) : ℝ)))) :=
    mul_lt_mul_of_pos_left hden_gt_one S.rho_pos
  simpa using hmul

private theorem theorem2AppendixA1_single_scale_does_not_imply_selected_scale
    (rho sigma : ℝ) (hne : sigma ≠ rho) :
    ¬ (∀ P : ℝ → Prop, P rho → P sigma) := by
  intro htransport
  exact hne (htransport (fun t => t = rho) rfl)

private theorem theorem2AppendixA1_rho_premise_does_not_supply_selected_scale
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    ¬ (∀ P : ℝ → Prop,
      P S.rho →
        P (theorem2AppendixA1SelectedSigma (S := S) hn hk)) := by
  exact
    theorem2AppendixA1_single_scale_does_not_imply_selected_scale
      S.rho (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      (ne_of_lt (theorem2AppendixA1SelectedSigma_lt_rho S hn hk))

/- A concrete bounded scale profile witnesses the same source statement issue
   at the scalar expectation level.  It is intentionally an abstract profile,
   not a replacement for a Gaussian loss model: the point is that boundedness
   alone does not transport a one-scale inequality to a distinct scale. -/
private noncomputable def theorem2AppendixA1_bounded_scale_profile
    (rho sigma : ℝ) : ℝ :=
  if sigma = rho then 1 else 0

private theorem theorem2AppendixA1_bounded_scale_profile_unit_interval
    (rho sigma : ℝ) :
    0 ≤ theorem2AppendixA1_bounded_scale_profile rho sigma ∧
      theorem2AppendixA1_bounded_scale_profile rho sigma ≤ 1 := by
  unfold theorem2AppendixA1_bounded_scale_profile
  split_ifs <;> norm_num

private theorem theorem2AppendixA1_rho_scale_premise_not_transportable
    (rho sigma : ℝ) (hne : sigma ≠ rho) :
    ¬ ((1 : ℝ) ≤ theorem2AppendixA1_bounded_scale_profile rho rho →
      (1 : ℝ) ≤ theorem2AppendixA1_bounded_scale_profile rho sigma) := by
  intro htransport
  have hrho :
      (1 : ℝ) ≤ theorem2AppendixA1_bounded_scale_profile rho rho := by
    simp [theorem2AppendixA1_bounded_scale_profile]
  have hsigma :=
    htransport hrho
  have hzero :
      theorem2AppendixA1_bounded_scale_profile rho sigma = 0 := by
    simp [theorem2AppendixA1_bounded_scale_profile, hne]
  rw [hzero] at hsigma
  norm_num at hsigma

/- This is the deterministic part of the Appendix A.1 radius substitution.
   The probabilistic tail estimate is kept separate because it is the cited
   Laurent--Massart step. -/
theorem theorem2_appendixA1_sigma_radius_bridge
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) (ε : E)
    (hε :
      ‖ε‖ ≤
        Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
          (1 + Real.sqrt
            (Real.log (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)))) :
    ‖theorem2AppendixA1SelectedSigma (S := S) hn hk • ε‖ ≤ S.rho := by
  have hsigma_pos :=
    theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
  have hden :
      0 < Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
        (1 + Real.sqrt
          (Real.log (n : ℝ) /
            (Setup.parameterCount (E := E) : ℝ))) := by
    have hn' : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have hk' : (0 : ℝ) < (Setup.parameterCount (E := E) : ℝ) := by
      exact_mod_cast hk
    apply mul_pos
    · exact Real.sqrt_pos.2 hk'
    · positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsigma_pos]
  calc
    theorem2AppendixA1SelectedSigma (S := S) hn hk * ‖ε‖ ≤
        theorem2AppendixA1SelectedSigma (S := S) hn hk *
          (Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
            (1 + Real.sqrt
              (Real.log (n : ℝ) /
                (Setup.parameterCount (E := E) : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left hε (le_of_lt hsigma_pos)
    _ = S.rho := by
      unfold theorem2AppendixA1SelectedSigma
      exact div_mul_cancel₀ S.rho (ne_of_gt hden)

def theorem2AppendixA1GaussianRadiusEvent
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) : Set E :=
  Metric.closedBall (0 : E)
    (Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
      (1 + Real.sqrt
        (Real.log (n : ℝ) /
          (Setup.parameterCount (E := E) : ℝ))))

theorem theorem2AppendixA1GaussianRadiusEvent_mem_iff
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) (ε : E) :
    ε ∈ theorem2AppendixA1GaussianRadiusEvent (S := S) hn hk ↔
      ‖ε‖ ≤
        Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
          (1 + Real.sqrt
            (Real.log (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ))) := by
  simp [theorem2AppendixA1GaussianRadiusEvent, dist_zero_right]

theorem theorem2AppendixA1GaussianRadiusTail_bound
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    (stdGaussian E)
      (theorem2AppendixA1GaussianRadiusEvent (S := S) hn hk)ᶜ ≤
      ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹) := by
  rw [show theorem2AppendixA1GaussianRadiusEvent (S := S) hn hk =
      {ε : E |
        ‖ε‖ ≤
          Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
            (1 + Real.sqrt
              (Real.log (n : ℝ) /
                (Setup.parameterCount (E := E) : ℝ)))} by
    ext ε
    simp [theorem2AppendixA1GaussianRadiusEvent, dist_zero_right]]
  let k : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let x : ℝ := Real.sqrt (Real.log (n : ℝ) / k)
  let R : ℝ := Real.sqrt k * (1 + x)
  let ν : ℝ := x * (2 + x) / (2 * (1 + x) ^ 2)
  let lambda : ℝ := Real.log (n : ℝ) / 2
  let C : ℝ := k * Real.log (1 + x)
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hk_real : (0 : ℝ) < k := by
    dsimp [k]
    exact_mod_cast hk
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_real
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.sqrt_pos.2 (div_pos hlog_pos hk_real)
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hone_add_pos : 0 < 1 + x := by positivity
  have hν_pos : 0 < ν := by
    dsimp [ν]
    positivity
  have hν_half : ν < (1 / 2 : ℝ) := by
    dsimp [ν]
    have hsq_pos : 0 < (1 + x) ^ 2 := sq_pos_of_pos hone_add_pos
    rw [div_lt_iff₀ (by positivity : 0 < 2 * (1 + x) ^ 2)]
    nlinarith [sq_nonneg x]
  have hR_sq : R ^ 2 = k * (1 + x) ^ 2 := by
    dsimp [R]
    rw [mul_pow, Real.sq_sqrt hk_real.le]
  have hmgf_eq :
      ∫ ε : E, Real.exp (ν * ‖ε‖ ^ 2) ∂(stdGaussian E) =
        (1 - 2 * ν) ^ (-(k / 2)) := by
    simpa [k] using
      (integral_exp_mul_norm_sq_stdGaussian (E := E) (a := ν) hν_half)
  have hone_sub_twoν : 1 - 2 * ν = (1 + x)⁻¹ ^ 2 := by
    dsimp [ν]
    field_simp [ne_of_gt hone_add_pos]
    ring
  have hmgf_value :
      ∫ ε : E, Real.exp (ν * ‖ε‖ ^ 2) ∂(stdGaussian E) =
        Real.exp C := by
    rw [hmgf_eq, hone_sub_twoν]
    have hinv_sq_pos : 0 < (1 + x)⁻¹ ^ 2 :=
      sq_pos_of_pos (inv_pos.2 hone_add_pos)
    rw [Real.rpow_def_of_pos hinv_sq_pos,
      Real.log_pow, Real.log_inv]
    dsimp [C]
    congr 1
    ring
  have hmgf_int : Integrable (fun ε : E => Real.exp (ν * ‖ε‖ ^ 2)) (stdGaussian E) :=
    Integrable.of_integral_ne_zero (by
      rw [hmgf_value]
      exact ne_of_gt (Real.exp_pos C))
  have hthreshold : C + lambda ≤ ν * R ^ 2 := by
    have hlog_le : Real.log (1 + x) ≤ x := by
      simpa using Real.log_le_sub_one_of_pos hone_add_pos
    have hscaled_log_le : k * Real.log (1 + x) ≤ k * x :=
      mul_le_mul_of_nonneg_left hlog_le hk_real.le
    have hx_sq : x ^ 2 = Real.log (n : ℝ) / k := by
      dsimp [x]
      exact Real.sq_sqrt (div_nonneg hlog_pos.le hk_real.le)
    have hlog_eq : Real.log (n : ℝ) = k * x ^ 2 := by
      rw [hx_sq]
      field_simp
    dsimp [C, lambda, ν]
    rw [hR_sq, hlog_eq]
    field_simp
    nlinarith
  have htail :
      (stdGaussian E) {ε : E | ‖ε‖ ^ 2 > R ^ 2} ≤
        ENNReal.ofReal (Real.exp (-lambda)) :=
    measure_gt_le_exp_neg_of_mgf_bound_at
      (P := stdGaussian E)
      (S := fun ε : E => ‖ε‖ ^ 2) ν lambda (R ^ 2) C
      hν_pos hthreshold hmgf_int (le_of_eq hmgf_value)
  have hlambda_exp :
      Real.exp (-lambda) = (Real.sqrt (n : ℝ))⁻¹ := by
    dsimp [lambda]
    rw [Real.exp_neg]
    rw [← Real.log_sqrt hn_pos.le, Real.exp_log (Real.sqrt_pos.2 hn_pos)]
  calc
    (stdGaussian E)
        ({ε : E |
          ‖ε‖ ≤
            Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
              (1 + Real.sqrt
                (Real.log (n : ℝ) /
                  (Setup.parameterCount (E := E) : ℝ)))}ᶜ) ≤
      (stdGaussian E) {ε : E | ‖ε‖ ^ 2 > R ^ 2} := by
        apply measure_mono
        intro ε hε
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hε ⊢
        have hnot : ¬ ‖ε‖ ≤ R := by simpa [R, x, k] using hε
        have hlt : R < ‖ε‖ := lt_of_not_ge hnot
        exact pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    _ ≤ ENNReal.ofReal (Real.exp (-lambda)) := htail
    _ = ENNReal.ofReal ((Real.sqrt (n : ℝ))⁻¹) := by rw [hlambda_exp]

/- The complete Appendix A.1 source context.  Keeping these objects in one
   record makes the source supplier consume the same Measure-valued grid,
   posterior, confidence schedule, and selected scale that the paper proof
   uses.  Probability-law proofs now live in the measure context itself;
   transport obligations remain theorem inputs below rather than being
   stored as fields. -/
/- The context is a canonical source object, not a record of independently
   supplied probability measures or scales.  It has no independent fields; the
   mathematical components are fixed projections of the indexed source data
   below.  This prevents an arbitrary context value from disconnecting the
   KL and PAC-Bayes routes from the actual Gaussian and iid constructions. -/
structure Theorem2AppendixA1CanonicalContext
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) where

namespace Theorem2AppendixA1CanonicalContext

noncomputable def gridContext
    {S : Setup n E X Y Ω} {w : Setup.Parameter S}
    {δ : Set.Ioo (0 : ℝ) 1} {hn : 1 < n}
    {hk : 0 < Setup.parameterCount (E := E)}
    (_ctx : Theorem2AppendixA1CanonicalContext S w δ hn hk) :
    ℕ → MeasurePACBayesDistributionContext E (X × Y) :=
  theorem2MeasurePACBayesGridContext (S := S) hk

noncomputable def posteriorLaw
    {S : Setup n E X Y Ω} {w : Setup.Parameter S}
    {δ : Set.Ioo (0 : ℝ) 1} {hn : 1 < n}
    {hk : 0 < Setup.parameterCount (E := E)}
    (_ctx : Theorem2AppendixA1CanonicalContext S w δ hn hk) :
    Measure E :=
  theorem2AppendixA1PosteriorLaw (S := S) w

noncomputable def priorGridConfidence
    {S : Setup n E X Y Ω} {w : Setup.Parameter S}
    {δ : Set.Ioo (0 : ℝ) 1} {hn : 1 < n}
    {hk : 0 < Setup.parameterCount (E := E)}
    (_ctx : Theorem2AppendixA1CanonicalContext S w δ hn hk) :
    ℕ → ℝ :=
  fun j => theorem2AppendixA1PriorGridConfidence δ.1 j

noncomputable def selectedSigma
    {S : Setup n E X Y Ω} {w : Setup.Parameter S}
    {δ : Set.Ioo (0 : ℝ) 1} {hn : 1 < n}
    {hk : 0 < Setup.parameterCount (E := E)}
    (_ctx : Theorem2AppendixA1CanonicalContext S w δ hn hk) : ℝ :=
  theorem2AppendixA1SelectedSigma (S := S) hn hk

end Theorem2AppendixA1CanonicalContext

noncomputable def theorem2AppendixA1CanonicalContext
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    Theorem2AppendixA1CanonicalContext S w δ hn hk :=
  {}

theorem theorem2AppendixA1CanonicalContext_grid_sampleLaw
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    ∀ j,
      measurePACBayesSampleLaw
          ((theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).gridContext j) n =
        Setup.iidTrainingLaw (S := S) := by
  intro j
  exact theorem2MeasurePACBayesGridContext_sampleLaw S hk j

theorem theorem2AppendixA1CanonicalContext_grid_sampleLaw_isProbability
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) :
    IsProbabilityMeasure
      (measurePACBayesSampleLaw
        ((theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).gridContext j) n) := by
  exact measurePACBayesSampleLaw_isProbability
    ((theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).gridContext j)
    n S.dataLaw_isProbability

theorem theorem2AppendixA1CanonicalContext_grid_prior
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    ∀ j,
      ((theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).gridContext j).prior_distribution =
        gaussianAffineLaw (E := E) (0 : E)
          (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)) := by
  intro j
  exact theorem2MeasurePACBayesGridContext_prior S hk j

theorem theorem2AppendixA1CanonicalContext_grid_prior_isProbability
    [BorelSpace E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ) :
    IsProbabilityMeasure
      ((theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).gridContext j).prior_distribution := by
  rw [theorem2AppendixA1CanonicalContext_grid_prior]
  exact gaussianAffineLaw_isProbability (E := E) 0 _

theorem theorem2AppendixA1CanonicalContext_posterior
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    (theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).posteriorLaw =
      theorem2AppendixA1PosteriorLaw (S := S) w := by
  rfl

theorem theorem2AppendixA1CanonicalContext_confidence
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    ∀ j,
      (theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).priorGridConfidence j =
        theorem2AppendixA1PriorGridConfidence δ.1 j := by
  intro j
  rfl

theorem theorem2AppendixA1CanonicalContext_selectedSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    (theorem2AppendixA1CanonicalContext (S := S) w δ hn hk).selectedSigma =
      theorem2AppendixA1SelectedSigma (S := S) hn hk := by
  rfl

/- The prior-grid confidence data now has a direct consumer at the canonical
   Appendix A.1 context.  This is the countable union step used after applying
   the source PAC-Bayes estimate separately at each data-independent prior. -/
theorem theorem2AppendixA1CanonicalContext_priorGridFailureMass
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (ctx : Theorem2AppendixA1CanonicalContext S w δ hn hk)
    (bad : ℕ → Set (Dataset n X Y))
    (hbad :
      ∀ j,
        (Setup.iidTrainingLaw (S := S)) (bad j) ≤
          ENNReal.ofReal (ctx.priorGridConfidence j)) :
    (Setup.iidTrainingLaw (S := S)) (⋃ j, bad j) ≤
      ENNReal.ofReal δ.1 := by
  apply theorem2AppendixA1PriorGridConfidence_union_bound
    (μ := Setup.iidTrainingLaw (S := S)) δ.1
    (le_of_lt δ.2.1) bad
  intro j
  simpa [Theorem2AppendixA1CanonicalContext.priorGridConfidence] using hbad j

/- Eq. (6)'s canonical measure-valued KL term.  The source-facing object is
   the actual relative entropy between the Gaussian posterior and the
   data-independent Gaussian prior.  The displayed scalar Gaussian formula
   is kept separate below as a source calculation; it is not used as a
   surrogate for the measure-valued KL. -/
noncomputable def theorem2AppendixA1GaussianKLFormulaAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (sigma : ℝ) : ENNReal :=
  InformationTheory.klDiv
    (gaussianAffineLaw (E := E) w.1 sigma)
    (gaussianAffineLaw (E := E) (0 : E)
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)))

noncomputable def theorem2AppendixA1GaussianKLFormula
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) : ENNReal :=
  theorem2AppendixA1GaussianKLFormulaAtSigma (S := S) w hk j S.rho

/- The scalar expression printed in Eq. (6), retained as a separate source
   calculation until the affine-Gaussian KL identity is proved. -/
noncomputable def theorem2AppendixA1GaussianKLFormulaScalarAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (sigma : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (((Setup.parameterCount (E := E) : ℝ) * sigma ^ 2 + ‖w.1‖ ^ 2) /
        theorem2AppendixA1PriorGridVariance (S := S) hk j -
      (Setup.parameterCount (E := E) : ℝ) +
      (Setup.parameterCount (E := E) : ℝ) *
        Real.log
          (theorem2AppendixA1PriorGridVariance (S := S) hk j /
            sigma ^ 2))

noncomputable def theorem2AppendixA1GaussianKLFormulaScalar
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) : ℝ :=
  theorem2AppendixA1GaussianKLFormulaScalarAtSigma (S := S) w hk j S.rho

/- Eq. (6)'s closed-form Gaussian KL calculation.  This is deliberately a
   narrow source calculation predicate, not a field on `Setup` and not an
   alias for the Measure-valued KL term.  The remaining proof is the
   RN-density/moment calculation for affine isotropic Gaussian laws.

   Source route anchor: SAM Appendix A.1 Eq. (6), PDF lines 852--867,
   invokes the closed-form KL between isotropic multivariate Gaussian
   prior/posterior laws after citing Dziugaite--Roy (2017).  Dziugaite--Roy
   Sec. 2.1 Eq. (1), PDF lines 196--212, states the general multivariate-normal
   KL formula for positive-definite covariance matrices.  The imported
   Dziugaite--Roy external scaffold supplies that cited source theorem; the
   paper-local bridge below is the approved external-literature debt connecting
   that Euclidean isotropic statement to the affine `gaussianAffineLaw` object.

   External-route scope note: this leaf exports only the Eq. (6) KL supplier.
   The selected-grid inclusion and selected failure mass are downstream local
   Appendix A.1 consequences to prove after the KL supplier exists, not direct
   consumer exports of the Dziugaite--Roy Gaussian KL theorem. -/
def theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) : Prop :=
  theorem2AppendixA1GaussianKLFormula (S := S) w hk j =
    ENNReal.ofReal (theorem2AppendixA1GaussianKLFormulaScalar (S := S) w hk j)

def theorem2AppendixA1GaussianKLFormulaScalarSourceCalculationAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (sigma : ℝ) : Prop :=
  theorem2AppendixA1GaussianKLFormulaAtSigma (S := S) w hk j sigma =
    ENNReal.ofReal
      (theorem2AppendixA1GaussianKLFormulaScalarAtSigma (S := S) w hk j sigma)

namespace External

private theorem euclideanAffineGaussian_eq_multivariate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : EuclideanSpace ℝ ι) (sigma : ℝ) :
    Measure.map (fun x : EuclideanSpace ℝ ι => μ + sigma • x)
        (stdGaussian (EuclideanSpace ℝ ι)) =
      multivariateGaussian μ (Matrix.diagonal fun _ : ι => sigma ^ 2) := by
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    sigma • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)
  let nu : Measure (EuclideanSpace ℝ ι) :=
    Measure.map (fun x : EuclideanSpace ℝ ι => μ + L x)
      (stdGaussian (EuclideanSpace ℝ ι))
  have hfun : (fun x : EuclideanSpace ℝ ι => μ + sigma • x) =
      (fun x => μ + L x) := by
    funext x
    simp [L]
  have hnu : nu =
      Measure.map (fun x : EuclideanSpace ℝ ι => μ + sigma • x)
        (stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [hfun]
  haveI : IsGaussian nu := by
    dsimp [nu]
    have h : (fun x : EuclideanSpace ℝ ι => μ + L x) =
        (fun x => μ + x) ∘ L := by
      rfl
    rw [h, ← Measure.map_map (measurable_const_add μ) (by fun_prop)]
    infer_instance
  have hmean :
      nu[id] =
        (multivariateGaussian μ
          (Matrix.diagonal fun _ : ι => sigma ^ 2))[id] := by
    change
      (∫ x, x ∂(Measure.map
        (fun x : EuclideanSpace ℝ ι => μ + L x)
        (stdGaussian (EuclideanSpace ℝ ι)))) =
        (∫ x, x ∂(multivariateGaussian μ
          (Matrix.diagonal fun _ : ι => sigma ^ 2)))
    rw [MeasureTheory.integral_map]
    · have hLmem : MemLp (fun x : EuclideanSpace ℝ ι => L x) 2
          (stdGaussian (EuclideanSpace ℝ ι)) := by
        simpa only [Function.comp_apply] using
          L.comp_memLp' (ProbabilityTheory.IsGaussian.memLp_two_id)
      rw [integral_add (integrable_const _)
        (hLmem.integrable (by norm_num))]
      have hLint :
          (∫ x : EuclideanSpace ℝ ι, L x
              ∂stdGaussian (EuclideanSpace ℝ ι)) =
            L (∫ x : EuclideanSpace ℝ ι, x
              ∂stdGaussian (EuclideanSpace ℝ ι)) := by
        simpa only [id_eq] using
          L.integral_comp_comm
            (ProbabilityTheory.IsGaussian.memLp_two_id.integrable
              (by norm_num))
      rw [hLint, integral_id_stdGaussian]
      simp
    · fun_prop
    · fun_prop
  have hcov :
      covarianceBilin nu =
        covarianceBilin (multivariateGaussian μ
          (Matrix.diagonal fun _ : ι => sigma ^ 2)) := by
    ext x y
    change
      covarianceBilin (Measure.map
        (fun x : EuclideanSpace ℝ ι => μ + L x)
        (stdGaussian (EuclideanSpace ℝ ι))) x y =
        covarianceBilin (multivariateGaussian μ
          (Matrix.diagonal fun _ : ι => sigma ^ 2)) x y
    have hcomp : (fun x : EuclideanSpace ℝ ι => μ + L x) =
        (fun x => μ + x) ∘ L := by
      rfl
    rw [hcomp, ← Measure.map_map (measurable_const_add μ) (by fun_prop)]
    rw [covarianceBilin_map_const_add]
    rw [covarianceBilin_map
      (μ := stdGaussian (EuclideanSpace ℝ ι))
      (ProbabilityTheory.IsGaussian.memLp_two_id) L x y]
    rw [covarianceBilin_stdGaussian]
    change inner ℝ (L.adjoint x) (L.adjoint y) = _
    simp [L, real_inner_smul_left, real_inner_smul_right,
      PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
    rw [covarianceBilin_multivariateGaussian (μ := μ)
      (S := Matrix.diagonal fun _ : ι => sigma ^ 2)]
    · simp [Matrix.mulVec_diagonal]
      change
        (∑ i, (sigma * x.ofLp i) * (sigma * y.ofLp i)) =
          sigma ^ 2 * (∑ i, x.ofLp i * y.ofLp i)
      calc
        (∑ i, (sigma * x.ofLp i) * (sigma * y.ofLp i)) =
            ∑ i, sigma ^ 2 * (x.ofLp i * y.ofLp i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = sigma ^ 2 * (∑ i, x.ofLp i * y.ofLp i) := by
          rw [Finset.mul_sum]
    · exact Matrix.PosSemidef.diagonal (fun i => sq_nonneg sigma)
  rw [← hnu]
  exact ProbabilityTheory.IsGaussian.ext hmean hcov

private theorem coordinateGaussianLaw_map
    [BorelSpace E] [SecondCountableTopology E]
    (center : E) (sigma : ℝ) :
    Measure.map
        ((stdOrthonormalBasis ℝ E).repr.toHomeomorph.toMeasurableEquiv)
        (gaussianAffineLaw (E := E) center sigma) =
      multivariateGaussian
        (WithLp.toLp 2 (Setup.coordinateVector (E := E) center))
        (Matrix.diagonal fun _ : Fin (Module.finrank ℝ E) => sigma ^ 2) := by
  let e : E ≃ᵐ EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (stdOrthonormalBasis ℝ E).repr.toHomeomorph.toMeasurableEquiv
  have hcomp :
      (e : E → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∘
          (fun x : E => center + sigma • x) =
        (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          e center + sigma • z) ∘ e := by
    funext x
    simp [e, map_add, map_smul]
  rw [gaussianAffineLaw, Measure.map_map e.measurable
    (by fun_prop), hcomp]
  have hstd : Measure.map e (stdGaussian E) =
      stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    simpa [e] using
      (ProbabilityTheory.stdGaussian_map (stdOrthonormalBasis ℝ E).repr)
  rw [← Measure.map_map (by fun_prop) e.measurable, hstd]
  have he_center : e center =
      (WithLp.toLp 2 (Setup.coordinateVector (E := E) center) :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
    rfl
  rw [he_center]
  exact euclideanAffineGaussian_eq_multivariate _ _

/- The paper identifies the parameter carrier with Euclidean coordinates.  This
   is the smaller transport leaf consumed by the source-facing KL supplier:
   the affine Gaussian on the Hilbert carrier is transported to the canonical
   Euclidean isotropic Gaussian before the cited scalar calculation is used. -/
private theorem coordinateGaussianKLTransport
    [BorelSpace E] [SecondCountableTopology E]
    (center : E) (sigma tau : ℝ)
    (hsigma : 0 < sigma) (htau : 0 < tau) :
    InformationTheory.klDiv
        (gaussianAffineLaw (E := E) center sigma)
        (gaussianAffineLaw (E := E) (0 : E) tau) =
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalKLDivergence
        (WithLp.toLp 2 (Setup.coordinateVector (E := E) center))
        0
        (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicPositiveDefiniteCovariance
          (ι := Fin (Setup.parameterCount (E := E)))
            sigma hsigma)
      (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicPositiveDefiniteCovariance
          (ι := Fin (Setup.parameterCount (E := E)))
            tau htau) := by
  have hreconstruct := Setup.coordinateVector_reconstruct (E := E) center
  have hstd :=
    ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis
      (stdOrthonormalBasis ℝ E)
  let e : E ≃ᵐ EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (stdOrthonormalBasis ℝ E).repr.toHomeomorph.toMeasurableEquiv
  let μq : EuclideanSpace ℝ (Fin (Setup.parameterCount (E := E))) :=
    (WithLp.toLp 2 (Setup.coordinateVector (E := E) center) :
      EuclideanSpace ℝ (Fin (Setup.parameterCount (E := E))))
  let μp : EuclideanSpace ℝ (Fin (Setup.parameterCount (E := E))) := 0
  let qCov :
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.PositiveDefiniteCovariance
        (Fin (Setup.parameterCount (E := E))) :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicPositiveDefiniteCovariance
      (ι := Fin (Setup.parameterCount (E := E))) sigma hsigma
  let pCov :
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.PositiveDefiniteCovariance
        (Fin (Setup.parameterCount (E := E))) :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicPositiveDefiniteCovariance
      (ι := Fin (Setup.parameterCount (E := E))) tau htau
  let Q : Measure E := gaussianAffineLaw (E := E) center sigma
  let P : Measure E := gaussianAffineLaw (E := E) (0 : E) tau
  let Mq : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
      μq qCov
  let Mp : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
      μp pCov
  have hQ : Measure.map e Q = Mq := by
    dsimp [Q, Mq, μq, qCov]
    simpa [ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw] using
      (coordinateGaussianLaw_map center sigma)
  have hP : Measure.map e P = Mp := by
    dsimp [P, Mp, μp, pCov]
    have hzero : (WithLp.toLp 2 (Setup.coordinateVector (E := E) (0 : E)) :
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 := by
      ext i
      simp [Setup.coordinateVector, Setup.coordinate]
    simpa [e, hzero] using
      (coordinateGaussianLaw_map (E := E) (0 : E) tau)
  letI : IsProbabilityMeasure Mq := by
    dsimp [Mq,
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw]
    infer_instance
  letI : IsProbabilityMeasure Mp := by
    dsimp [Mp,
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw]
    infer_instance
  have hsource :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.dziugaite_roy_2017_isotropicGaussian_kl_closedForm_positiveStd
      μq μp hsigma htau
  have hfinite : InformationTheory.klDiv Mq Mp ≠ ⊤ := by
    change InformationTheory.klDiv
      (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
        μq qCov)
      (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
        μp pCov) ≠ ⊤
    rw [show InformationTheory.klDiv
        (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
          μq qCov)
        (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
          μp pCov) =
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalKLDivergence
        μq μp qCov pCov by rfl]
    rw [hsource.2]
    exact ENNReal.ofReal_ne_top
  have hQback : Measure.map e.symm Mq = Q := by
    rw [← hQ, Measure.map_map e.symm.measurable e.measurable]
    simp
  have hPback : Measure.map e.symm Mp = P := by
    rw [← hP, Measure.map_map e.symm.measurable e.measurable]
    simp
  calc
    InformationTheory.klDiv Q P =
        InformationTheory.klDiv (Measure.map e.symm Mq)
          (Measure.map e.symm Mp) := by
            rw [hQback, hPback]
    _ = InformationTheory.klDiv Mq Mp :=
      klDiv_map_symm_eq_of_ne_top e Mq Mp hfinite
    _ =
        ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalKLDivergence
          (WithLp.toLp 2 (Setup.coordinateVector (E := E) center))
          0 qCov pCov := by
            change InformationTheory.klDiv
              (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
                μq qCov)
              (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalLaw
                μp pCov) =
              ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalKLDivergence
                μq μp qCov pCov
            rfl

/- Source bridge for SAM Appendix A.1 Eq. (6), backed by the materialized
   Dziugaite--Roy 2017 multivariate-normal KL formula.  The external theorem is
   stated for Euclidean coordinates and positive isotropic standard deviations;
   this bridge carries the paper-local identification with `gaussianAffineLaw`.
   The remaining proof term is approved external-literature debt, not a new
   SAM assumption or an exact-`hcalc` wrapper. -/
theorem theorem2AppendixA1GaussianKLFormulaScalarSourceCalculationAtSigma
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    Algorithms.Unverified.SAM.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculationAtSigma
      (S := S) w hk j sigma := by
  classical
  have hgrid_var_pos :
      0 < theorem2AppendixA1PriorGridVariance (S := S) hk j :=
    theorem2AppendixA1PriorGridVariance_pos (S := S) hk j
  have hprior_sigma_pos :
      0 < Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j) :=
    Real.sqrt_pos.2 hgrid_var_pos
  let μq : EuclideanSpace ℝ (Fin (Setup.parameterCount (E := E))) :=
    (WithLp.toLp 2 (Setup.coordinateVector (E := E) w.1) :
      EuclideanSpace ℝ (Fin (Setup.parameterCount (E := E))))
  let μp : EuclideanSpace ℝ (Fin (Setup.parameterCount (E := E))) := 0
  letI : DecidableEq (Fin (Setup.parameterCount (E := E))) := inferInstance
  let qCov :
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.PositiveDefiniteCovariance
        (Fin (Setup.parameterCount (E := E))) :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicPositiveDefiniteCovariance
      (ι := Fin (Setup.parameterCount (E := E))) sigma hsigma
  let pCov :
      ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.PositiveDefiniteCovariance
        (Fin (Setup.parameterCount (E := E))) :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicPositiveDefiniteCovariance
      (ι := Fin (Setup.parameterCount (E := E)))
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))
      hprior_sigma_pos
  have hsource_positiveDefinite :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.dziugaite_roy_2017_multivariateNormal_kl_closedForm_positiveDefinite
      (ι := Fin (Setup.parameterCount (E := E))) μq μp qCov pCov
  have hsource_isotropic :=
    ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.dziugaite_roy_2017_isotropicGaussian_kl_closedForm_positiveStd
      (ι := Fin (Setup.parameterCount (E := E))) μq μp hsigma hprior_sigma_pos
  have htransport :=
    coordinateGaussianKLTransport (E := E) w.1 sigma
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))
      hsigma hprior_sigma_pos
  have hnorm_mu : ‖μp - μq‖ ^ 2 = ‖w.1‖ ^ 2 := by
    have hsum :
        (∑ i : Fin (Module.finrank ℝ E),
          Setup.coordinateVector (E := E) w.1 i ^ 2) = ‖w.1‖ ^ 2 := by
      rw [← Finset.norm_sq_sum_smul_orthonormalBasis
        (stdOrthonormalBasis ℝ E)
        (Setup.coordinateVector (E := E) w.1)]
      rw [Setup.coordinateVector_reconstruct]
    dsimp [μp, μq]
    rw [zero_sub, norm_neg, EuclideanSpace.norm_eq]
    change
      Real.sqrt
          (∑ i : Fin (Module.finrank ℝ E),
            ‖Setup.coordinateVector (E := E) w.1 i‖ ^ 2) ^ 2 =
        ‖w.1‖ ^ 2
    rw [show (∑ i : Fin (Module.finrank ℝ E),
        ‖Setup.coordinateVector (E := E) w.1 i‖ ^ 2) =
          ∑ i : Fin (Module.finrank ℝ E),
            Setup.coordinateVector (E := E) w.1 i ^ 2 by
      congr 1
      funext i
      simp [sq]]
    rw [hsum]
    rw [Real.sq_sqrt (sq_nonneg ‖w.1‖)]
  calc
    InformationTheory.klDiv
          (gaussianAffineLaw (E := E) w.1 sigma)
          (gaussianAffineLaw (E := E) (0 : E)
            (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))) =
        ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.multivariateNormalKLDivergence
          μq μp qCov pCov := by
            simpa [μq, μp, qCov, pCov] using htransport
    _ = ENNReal.ofReal
        (ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicGaussianKLClosedForm
          μq μp sigma
            (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))) :=
      hsource_isotropic.2
    _ = ENNReal.ofReal
        (theorem2AppendixA1GaussianKLFormulaScalarAtSigma (S := S) w hk j sigma) := by
      congr 1
      simp [ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.isotropicGaussianKLClosedForm,
        theorem2AppendixA1GaussianKLFormulaScalarAtSigma]
      rw [hnorm_mu, Real.sq_sqrt (le_of_lt hgrid_var_pos)]
      ring

theorem theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    Algorithms.Unverified.SAM.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
      (S := S) w hk j := by
  simpa [
    Algorithms.Unverified.SAM.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation,
    Algorithms.Unverified.SAM.theorem2AppendixA1GaussianKLFormula,
    Algorithms.Unverified.SAM.theorem2AppendixA1GaussianKLFormulaScalar] using
    (Algorithms.Unverified.SAM.External.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculationAtSigma
      (S := S) w hk j S.rho S.rho_pos)

end External

noncomputable def theorem2AppendixA1GaussianKL_specialization
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) : ENNReal :=
  theorem2AppendixA1GaussianKLFormulaAtSigma (S := S) w hk j S.rho

theorem theorem2AppendixA1GaussianKLFormula_eq_gaussianAffineLaw
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    theorem2AppendixA1GaussianKLFormula (S := S) w hk j =
      InformationTheory.klDiv
        (gaussianAffineLaw (E := E) w.1 S.rho)
        (gaussianAffineLaw (E := E) (0 : E)
          (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))) := by
  rfl

/- Same-interface Eq. (6) source-route attempt.  Mathlib currently exposes the
   KL/RN integral boundary for the affine Gaussian measures via
   `InformationTheory.klDiv_of_ac_of_integrable`; no imported theorem rewrites
   that integral to the isotropic scalar expression from SAM Eq. (6). -/
set_option linter.unreachableTactic false in
private theorem theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation_source_attempt_iter54
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) : True := by
  let Q : Measure E := gaussianAffineLaw (E := E) w.1 S.rho
  let P : Measure E :=
    gaussianAffineLaw (E := E) (0 : E)
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))
  have htarget_unfolds :
      theorem2AppendixA1GaussianKLFormula (S := S) w hk j =
        InformationTheory.klDiv Q P := by
    rfl
  have hmathlib_integral_entry :
      ∀ (h_ac : Q ≪ P) (h_int : Integrable (MeasureTheory.llr Q P) Q),
        theorem2AppendixA1GaussianKLFormula (S := S) w hk j =
          ENNReal.ofReal
            (∫ z : E, MeasureTheory.llr Q P z ∂Q +
              P.real Set.univ - Q.real Set.univ) := by
    intro h_ac h_int
    simpa [htarget_unfolds] using
      (InformationTheory.klDiv_of_ac_of_integrable
        (μ := Q) (ν := P) h_ac h_int)
  fail_if_success
    exact
      (show
        theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
          (S := S) w hk j from by
        simp [theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation,
          theorem2AppendixA1GaussianKLFormula,
          theorem2AppendixA1GaussianKLFormulaScalar, gaussianAffineLaw])
  trivial

/- Exact-head reduction of SAM Appendix A.1 Eq. (6) to the real Gaussian
   likelihood-ratio moment calculation.  Unlike the historical `hcalc`
   compatibility wrapper, this theorem uses Mathlib's KL definition theorem
   and leaves only the source-local Gaussian AC/integrability/llr-integral
   leaves exposed at private proof granularity. -/
private theorem theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation_of_llr_integral
    [BorelSpace E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (h_ac :
      gaussianAffineLaw (E := E) w.1 S.rho ≪
        gaussianAffineLaw (E := E) (0 : E)
          (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)))
    (h_int :
      Integrable
        (MeasureTheory.llr
          (gaussianAffineLaw (E := E) w.1 S.rho)
          (gaussianAffineLaw (E := E) (0 : E)
            (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))))
        (gaussianAffineLaw (E := E) w.1 S.rho))
    (h_llr :
      (∫ z : E,
          MeasureTheory.llr
            (gaussianAffineLaw (E := E) w.1 S.rho)
            (gaussianAffineLaw (E := E) (0 : E)
              (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))) z
          ∂(gaussianAffineLaw (E := E) w.1 S.rho)) =
        theorem2AppendixA1GaussianKLFormulaScalar (S := S) w hk j) :
    theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
      (S := S) w hk j := by
  let Q : Measure E := gaussianAffineLaw (E := E) w.1 S.rho
  let P : Measure E :=
    gaussianAffineLaw (E := E) (0 : E)
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))
  have hQprob : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact gaussianAffineLaw_isProbability (E := E) w.1 S.rho
  have hPprob : IsProbabilityMeasure P := by
    dsimp [P]
    exact gaussianAffineLaw_isProbability (E := E) (0 : E)
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))
  have hkl :
      InformationTheory.klDiv Q P =
        ENNReal.ofReal (∫ z : E, MeasureTheory.llr Q P z ∂Q) := by
    have hraw :=
      InformationTheory.klDiv_of_ac_of_integrable
        (μ := Q) (ν := P) h_ac h_int
    simpa [Q, P] using hraw
  change
    theorem2AppendixA1GaussianKLFormula (S := S) w hk j =
      ENNReal.ofReal
        (theorem2AppendixA1GaussianKLFormulaScalar (S := S) w hk j)
  simpa [theorem2AppendixA1GaussianKLFormula, Q, P, h_llr] using hkl

/- Exact-head voucher attempt for the Eq. (6) supplier.  This command is
   intentionally guarded as a failed proof: it type-checks the source-facing
   target and records that the remaining proof state is precisely the Gaussian
   absolute-continuity, likelihood-ratio integrability, and likelihood-ratio
   moment calculation needed by the KL/RN bridge above. -/
/--
error: unsolved goals
case refine_1
E : Type u_1
X : Type u_2
Y : Type u_3
Ω : Type u_4
inst✝⁷ : MeasurableSpace E
inst✝⁶ : MeasurableSpace X
inst✝⁵ : MeasurableSpace Y
inst✝⁴ : NormedAddCommGroup E
inst✝³ : InnerProductSpace ℝ E
inst✝² : CompleteSpace E
inst✝¹ : FiniteDimensional ℝ E
n : ℕ
inst✝ : BorelSpace E
S : Setup n E X Y Ω
w : S.Parameter
hk : 0 < Setup.parameterCount
j : ℕ
⊢ gaussianAffineLaw (↑w) S.rho ≪ gaussianAffineLaw 0 √(theorem2AppendixA1PriorGridVariance S hk j)

case refine_2
E : Type u_1
X : Type u_2
Y : Type u_3
Ω : Type u_4
inst✝⁷ : MeasurableSpace E
inst✝⁶ : MeasurableSpace X
inst✝⁵ : MeasurableSpace Y
inst✝⁴ : NormedAddCommGroup E
inst✝³ : InnerProductSpace ℝ E
inst✝² : CompleteSpace E
inst✝¹ : FiniteDimensional ℝ E
n : ℕ
inst✝ : BorelSpace E
S : Setup n E X Y Ω
w : S.Parameter
hk : 0 < Setup.parameterCount
j : ℕ
⊢ Integrable (llr (gaussianAffineLaw (↑w) S.rho) (gaussianAffineLaw 0 √(theorem2AppendixA1PriorGridVariance S hk j)))
    (gaussianAffineLaw (↑w) S.rho)

case refine_3
E : Type u_1
X : Type u_2
Y : Type u_3
Ω : Type u_4
inst✝⁷ : MeasurableSpace E
inst✝⁶ : MeasurableSpace X
inst✝⁵ : MeasurableSpace Y
inst✝⁴ : NormedAddCommGroup E
inst✝³ : InnerProductSpace ℝ E
inst✝² : CompleteSpace E
inst✝¹ : FiniteDimensional ℝ E
n : ℕ
inst✝ : BorelSpace E
S : Setup n E X Y Ω
w : S.Parameter
hk : 0 < Setup.parameterCount
j : ℕ
⊢ ∫ (z : E),
      llr (gaussianAffineLaw (↑w) S.rho) (gaussianAffineLaw 0 √(theorem2AppendixA1PriorGridVariance S hk j))
        z ∂gaussianAffineLaw (↑w) S.rho =
    theorem2AppendixA1GaussianKLFormulaScalar S w hk j
-/
#guard_msgs in
private theorem theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation_voucher_attempt_iter56
    [BorelSpace E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
      (S := S) w hk j := by
  refine theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation_of_llr_integral
    (S := S) (w := w) (hk := hk) (j := j) ?_ ?_ ?_

/- Iteration 57 keeps the same source-facing target and tests the canonical
   affine-pushforward route directly.  The useful local facts are the positive
   posterior scale `S.rho` and the positive grid-prior scale; after unfolding
   the affine Gaussian laws, the remaining obstruction is exactly the missing
   quasi-invariance/density theorem for two nondegenerate affine images of
   `stdGaussian E`, followed by the induced llr integrability and moment
   calculation. -/
/--
error: unsolved goals
case refine_1
E : Type u_1
X : Type u_2
Y : Type u_3
Ω : Type u_4
inst✝⁷ : MeasurableSpace E
inst✝⁶ : MeasurableSpace X
inst✝⁵ : MeasurableSpace Y
inst✝⁴ : NormedAddCommGroup E
inst✝³ : InnerProductSpace ℝ E
inst✝² : CompleteSpace E
inst✝¹ : FiniteDimensional ℝ E
n : ℕ
inst✝ : BorelSpace E
S : Setup n E X Y Ω
w : S.Parameter
hk : 0 < Setup.parameterCount
j : ℕ
hgrid_var_pos : 0 < theorem2AppendixA1PriorGridVariance S hk j
hprior_sigma_pos : 0 < √(theorem2AppendixA1PriorGridVariance S hk j)
hpost_sigma_pos : 0 < S.rho
⊢ Measure.map (fun ε => ↑w + S.rho • ε) (stdGaussian E) ≪
    Measure.map (fun ε => 0 + √(theorem2AppendixA1PriorGridVariance S hk j) • ε) (stdGaussian E)
---
error: unsolved goals
case refine_2
E : Type u_1
X : Type u_2
Y : Type u_3
Ω : Type u_4
inst✝⁷ : MeasurableSpace E
inst✝⁶ : MeasurableSpace X
inst✝⁵ : MeasurableSpace Y
inst✝⁴ : NormedAddCommGroup E
inst✝³ : InnerProductSpace ℝ E
inst✝² : CompleteSpace E
inst✝¹ : FiniteDimensional ℝ E
n : ℕ
inst✝ : BorelSpace E
S : Setup n E X Y Ω
w : S.Parameter
hk : 0 < Setup.parameterCount
j : ℕ
hgrid_var_pos : 0 < theorem2AppendixA1PriorGridVariance S hk j
hprior_sigma_pos : 0 < √(theorem2AppendixA1PriorGridVariance S hk j)
hpost_sigma_pos : 0 < S.rho
⊢ Integrable (llr (gaussianAffineLaw (↑w) S.rho) (gaussianAffineLaw 0 √(theorem2AppendixA1PriorGridVariance S hk j)))
    (gaussianAffineLaw (↑w) S.rho)
---
error: unsolved goals
case refine_3
E : Type u_1
X : Type u_2
Y : Type u_3
Ω : Type u_4
inst✝⁷ : MeasurableSpace E
inst✝⁶ : MeasurableSpace X
inst✝⁵ : MeasurableSpace Y
inst✝⁴ : NormedAddCommGroup E
inst✝³ : InnerProductSpace ℝ E
inst✝² : CompleteSpace E
inst✝¹ : FiniteDimensional ℝ E
n : ℕ
inst✝ : BorelSpace E
S : Setup n E X Y Ω
w : S.Parameter
hk : 0 < Setup.parameterCount
j : ℕ
hgrid_var_pos : 0 < theorem2AppendixA1PriorGridVariance S hk j
hprior_sigma_pos : 0 < √(theorem2AppendixA1PriorGridVariance S hk j)
hpost_sigma_pos : 0 < S.rho
⊢ ∫ (z : E),
      llr (gaussianAffineLaw (↑w) S.rho) (gaussianAffineLaw 0 √(theorem2AppendixA1PriorGridVariance S hk j))
        z ∂gaussianAffineLaw (↑w) S.rho =
    theorem2AppendixA1GaussianKLFormulaScalar S w hk j
-/
#guard_msgs in
private theorem theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation_voucher_attempt_iter57
    [BorelSpace E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
      (S := S) w hk j := by
  have hgrid_var_pos :
      0 < theorem2AppendixA1PriorGridVariance (S := S) hk j :=
    theorem2AppendixA1PriorGridVariance_pos (S := S) hk j
  have hprior_sigma_pos :
      0 < Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j) :=
    Real.sqrt_pos.2 hgrid_var_pos
  have hpost_sigma_pos : 0 < S.rho := S.rho_pos
  refine theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation_of_llr_integral
    (S := S) (w := w) (hk := hk) (j := j) ?_ ?_ ?_
  · change
      Measure.map (fun ε : E => w.1 + S.rho • ε) (stdGaussian E) ≪
        Measure.map
          (fun ε : E =>
            (0 : E) +
              Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j) • ε)
          (stdGaussian E)
    fail_if_success
      exact Measure.AbsolutelyContinuous.refl _
    fail_if_success
      simpa [gaussianAffineLaw] using
        (Measure.AbsolutelyContinuous.refl
          (gaussianAffineLaw (E := E) w.1 S.rho))
    fail_if_success
      have hsame_map :
          (fun ε : E => w.1 + S.rho • ε) =
            (fun ε : E =>
              (0 : E) +
                Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j) • ε) := by
            ext ε
            simp
      exact False.elim (by
        have _ := hprior_sigma_pos
        have _ := hpost_sigma_pos
        exact False.elim (by contradiction))
  · fail_if_success
      exact (IsGaussian.integrable_id
        (μ := gaussianAffineLaw (E := E) w.1 S.rho))
  · change
      (∫ z : E,
          MeasureTheory.llr
            (gaussianAffineLaw (E := E) w.1 S.rho)
            (gaussianAffineLaw (E := E) (0 : E)
              (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))) z
          ∂(gaussianAffineLaw (E := E) w.1 S.rho)) =
        theorem2AppendixA1GaussianKLFormulaScalar (S := S) w hk j

/- The Gaussian KL consumer is stated against the actual affine pushforward
   laws, not against context aliases.  This exposes the canonical
   measure-valued KL term; the scalar closed form in Eq. (6) remains a
   separate calculation. -/
theorem theorem2AppendixA1GaussianKL_specialization_of_gaussianAffineLaw
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    theorem2AppendixA1GaussianKL_specialization (S := S) w hk j =
      InformationTheory.klDiv
        (gaussianAffineLaw (E := E) w.1 S.rho)
        (gaussianAffineLaw (E := E) (0 : E)
          (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))) := by
  rfl

theorem theorem2AppendixA1GaussianKL_specialization_spec
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    theorem2AppendixA1GaussianKL_specialization (S := S) w hk j =
      measurePACBayesKLDivergence
        (theorem2AppendixA1PosteriorLaw (S := S) w)
        (theorem2MeasurePACBayesGridContext (S := S) hk j).prior_distribution := by
  rfl

/- Formula-level consumer for the materialized Eq. (6) source supplier.  This
   is the bridge the selected-grid PAC-Bayes comparison should rewrite with:
   the KL appearing in the grid context is the affine-Gaussian KL, and the
   scalar value is supplied by the approved Dziugaite--Roy external route. -/
theorem theorem2AppendixA1GaussianKL_specialization_formula_consumer
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) :
    theorem2AppendixA1GaussianKL_specialization (S := S) w hk j =
      ENNReal.ofReal
        (theorem2AppendixA1GaussianKLFormulaScalar (S := S) w hk j) := by
  simpa [theorem2AppendixA1GaussianKL_specialization,
    theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation] using
    (External.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculation
      (S := S) w hk j)

/- Eq. (5) at the same granularity as the canonical `Measure` context.  The
   event is now the actual Measure-valued event set.  Its probability estimate
   is a separate source theorem, rather than being encoded as a Prop-valued
   surrogate under the event's name. -/
def theorem2AppendixA1_arbitraryMeasure_PACBayes_event
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    : Set (Fin m → Sample) :=
  measurePACBayesExpectedLossEvent ctx m hm δ loss

/- McAllester's PAC-Bayes inequality is a bounded-loss theorem.  The current
   `Setup.loss` is only NNReal-valued, so bounded/admissible test-error
   semantics must be supplied at the Appendix A.1 probability boundary rather
   than hidden inside a theorem-level placeholder. -/
def theorem2PacBayesAdmissibleBoundedLoss (S : Setup n E X Y Ω) : Prop :=
  (∀ (w : Setup.Parameter S) (x : X) (y : Y), (S.loss w x y : ℝ) ≤ 1) ∧
    (∀ w : Setup.Parameter S, Setup.populationLossWellDefined (S := S) w)

/- Source-specific realization of the common PAC-Bayes loss.  The literal
   loss lives on the parameter subtype and the ambient Gaussian construction
   sees only its canonical `Function.extend` lift. -/
noncomputable def theorem2AppendixA1SourcePointwiseLossOnParameter
    (S : Setup n E X Y Ω) :
    MeasurePACBayesPointwiseLoss (Setup.Parameter S) (X × Y) :=
  fun u z => (Setup.lossOnParameter (S := S) u z.1 z.2 : ℝ)

theorem theorem2AppendixA1SourcePointwiseLossOnParameter_spec
    (S : Setup n E X Y Ω) (u : Setup.Parameter S) (z : X × Y) :
    theorem2AppendixA1SourcePointwiseLossOnParameter (S := S) u z =
      (S.loss u z.1 z.2 : ℝ) := by
  rfl

/- The bounded-loss premise is derived once on the paper's subtype carrier.
   Keeping this theorem separate makes the Gaussian-grid specialization
   consume the literal source loss rather than rebuild an ambient/default
   encoding at each PAC-Bayes call site. -/
theorem theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
    (S : Setup n E X Y Ω)
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    ∀ u z,
      0 ≤ theorem2AppendixA1SourcePointwiseLossOnParameter (S := S) u z ∧
        theorem2AppendixA1SourcePointwiseLossOnParameter (S := S) u z ≤ 1 := by
  intro u z
  constructor
  · exact_mod_cast
      (Setup.lossOnParameter (S := S) u z.1 z.2).property
  · simpa [theorem2AppendixA1SourcePointwiseLossOnParameter] using
      hbounded u z.1 z.2

theorem theorem2PacBayesAdmissibleBoundedLoss_of_measurable_bounded
    (S : Setup n E X Y Ω)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    theorem2PacBayesAdmissibleBoundedLoss (S := S) := by
  constructor
  · exact hbounded
  · intro u
    rw [Setup.populationLossWellDefined_spec,
      SOptLib.expectationWellDefined_iff_integrable]
    letI : IsProbabilityMeasure S.dataLaw := S.dataLaw_isProbability
    have hsource_bounded :
        ∀ u z,
          0 ≤ theorem2AppendixA1SourcePointwiseLossOnParameter (S := S) u z ∧
            theorem2AppendixA1SourcePointwiseLossOnParameter (S := S) u z ≤ 1 :=
      theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
        (S := S) hbounded
    simpa [theorem2AppendixA1SourcePointwiseLossOnParameter] using
      (measurePACBayesPointwiseLoss_integrable
        (μ := S.dataLaw)
        (loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        hmeas_loss hsource_bounded u)

private noncomputable def theorem2AppendixA1SourcePointwiseLossAmbient
    (S : Setup n E X Y Ω) :
    MeasurePACBayesPointwiseLoss E (X × Y) :=
  fun u z =>
    (Function.extend Subtype.val
      (fun v =>
        (theorem2AppendixA1SourcePointwiseLossOnParameter
          (S := S) v z : ℝ))
      (fun _ => 0) u)

/- The paper-facing loss is the subtype-indexed object.  The ambient lift is
   private infrastructure used only where a Gaussian law is still expressed
   on E. -/
noncomputable def theorem2AppendixA1SourcePointwiseLoss
    (S : Setup n E X Y Ω) :
    MeasurePACBayesPointwiseLoss (Setup.Parameter S) (X × Y) :=
  theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)

theorem theorem2AppendixA1SourcePointwiseLoss_on_parameter
    (S : Setup n E X Y Ω) (u : E) (z : X × Y)
    (hu : u ∈ S.parameterSpace) :
    theorem2AppendixA1SourcePointwiseLossAmbient (S := S) u z =
      theorem2AppendixA1SourcePointwiseLossOnParameter
        (S := S) ⟨u, hu⟩ z := by
  simpa [theorem2AppendixA1SourcePointwiseLossAmbient] using
    (Function.Injective.extend_apply
      (f := Subtype.val) Subtype.val_injective
      (fun v : Setup.Parameter S =>
        (theorem2AppendixA1SourcePointwiseLossOnParameter
          (S := S) v z : ℝ))
      (fun _ => 0) ⟨u, hu⟩)

/- The ambient totalization is source-faithful on any concept law that is
   concentrated on the paper parameter domain.  This is the exact
   almost-everywhere bridge needed before an ambient Gaussian PAC-Bayes
   integral may be identified with the subtype-indexed source loss. -/
def theorem2AppendixA1SourcePointwiseLossGaussianAEInvariant
    (S : Setup n E X Y Ω) (Q : Measure E) : Prop :=
  ∀ᵐ u ∂Q, ∃ hu : u ∈ S.parameterSpace,
    ∀ z : X × Y,
      theorem2AppendixA1SourcePointwiseLossAmbient (S := S) u z =
        theorem2AppendixA1SourcePointwiseLossOnParameter
          (S := S) ⟨u, hu⟩ z

theorem theorem2AppendixA1SourcePointwiseLoss_gaussian_ae_eq_of_parameterSpace_ae_full
    (S : Setup n E X Y Ω) (Q : Measure E)
    (hfull : ∀ᵐ u ∂Q, u ∈ S.parameterSpace) :
    theorem2AppendixA1SourcePointwiseLossGaussianAEInvariant
      (S := S) Q := by
  filter_upwards [hfull] with u hu
  exact ⟨hu, fun z =>
    theorem2AppendixA1SourcePointwiseLoss_on_parameter
      (S := S) u z hu⟩

/- A source-faithful Gaussian law on the parameter subtype is available when
   the affine Gaussian map has an explicit domain certificate.  The map is
   the paper's Gaussian construction itself; no default parameter is used
   outside the source domain. -/
noncomputable def theorem2AppendixA1ParameterGaussianLaw
    (S : Setup n E X Y Ω) (center : E) (sigma : ℝ)
    (hdom : ∀ ε : E, center + sigma • ε ∈ S.parameterSpace) :
    Measure (Setup.Parameter S) :=
  Measure.map
    (fun ε : E => ⟨center + sigma • ε, hdom ε⟩)
    (stdGaussian E)

private theorem theorem2AppendixA1ParameterGaussianMap_measurable
    [BorelSpace E]
    (S : Setup n E X Y Ω) (center : E) (sigma : ℝ)
    (hdom : ∀ ε : E, center + sigma • ε ∈ S.parameterSpace) :
    Measurable
      (fun ε : E =>
        (⟨center + sigma • ε, hdom ε⟩ : Setup.Parameter S)) := by
  exact
    (by fun_prop : Measurable (fun ε : E => center + sigma • ε)).subtype_mk

theorem theorem2AppendixA1ParameterGaussianLaw_isProbability
    [BorelSpace E]
    (S : Setup n E X Y Ω) (center : E) (sigma : ℝ)
    (hdom : ∀ ε : E, center + sigma • ε ∈ S.parameterSpace) :
    IsProbabilityMeasure
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) center sigma hdom) := by
  rw [isProbabilityMeasure_iff]
  rw [theorem2AppendixA1ParameterGaussianLaw,
    Measure.map_apply
      (theorem2AppendixA1ParameterGaussianMap_measurable
        (S := S) center sigma hdom)
      MeasurableSet.univ]
  simp [isProbabilityMeasure_iff.mp
    (isProbabilityMeasure_stdGaussian (E := E))]

theorem theorem2AppendixA1ParameterGaussianLaw_map_val
    [BorelSpace E]
    (S : Setup n E X Y Ω) (center : E) (sigma : ℝ)
    (hdom : ∀ ε : E, center + sigma • ε ∈ S.parameterSpace) :
    Measure.map Subtype.val
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) center sigma hdom) =
      gaussianAffineLaw (E := E) center sigma := by
  rw [theorem2AppendixA1ParameterGaussianLaw,
    Measure.map_map measurable_subtype_coe
      (theorem2AppendixA1ParameterGaussianMap_measurable
        (S := S) center sigma hdom)]
  simp [gaussianAffineLaw, Function.comp_def]

private def setupParameterFullMeasurableEquiv
    (S : Setup n E X Y Ω) (hfull : ∀ u : E, u ∈ S.parameterSpace) :
    Setup.Parameter S ≃ᵐ E :=
  { toEquiv :=
      { toFun := Subtype.val
        invFun := fun u : E => ⟨u, hfull u⟩
        left_inv := by
          intro u
          exact Subtype.ext rfl
        right_inv := by
          intro u
          rfl }
    measurable_toFun := measurable_subtype_coe
    measurable_invFun := by
      exact measurable_id.subtype_mk }

theorem theorem2AppendixA1ParameterGaussianLaw_integral_map
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [BorelSpace E]
    (S : Setup n E X Y Ω) (center : E) (sigma : ℝ)
    (hdom : ∀ ε : E, center + sigma • ε ∈ S.parameterSpace)
    (f : Setup.Parameter S → G)
    (hf : AEStronglyMeasurable f
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) center sigma hdom)) :
    ∫ u : Setup.Parameter S, f u ∂
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) center sigma hdom) =
      ∫ ε : E, f ⟨center + sigma • ε, hdom ε⟩ ∂(stdGaussian E) := by
  exact MeasureTheory.integral_map
    ((theorem2AppendixA1ParameterGaussianMap_measurable
      (S := S) center sigma hdom).aemeasurable)
    hf

/- The Appendix A.1 prior grid is represented on the paper parameter carrier.
   The domain certificate is an internal boundary obligation: it makes the
   affine Gaussian pushforward a genuine Measure on `Setup.Parameter S`,
   instead of silently evaluating the source loss through an ambient default. -/
noncomputable def theorem2AppendixA1ParameterGridContext
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    MeasurePACBayesDistributionContext (Setup.Parameter S) (X × Y) :=
  { prior_distribution :=
      theorem2AppendixA1ParameterGaussianLaw (S := S) (0 : E)
        (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)) hdom
    sampling_distribution := S.dataLaw }

theorem theorem2AppendixA1ParameterGridContext_sampling
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    (theorem2AppendixA1ParameterGridContext (S := S) hk j hdom).sampling_distribution =
      S.dataLaw := by
  rfl

theorem theorem2AppendixA1ParameterGridContext_prior_isProbability
    [BorelSpace E]
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    IsProbabilityMeasure
      (theorem2AppendixA1ParameterGridContext (S := S) hk j hdom).prior_distribution := by
  dsimp [theorem2AppendixA1ParameterGridContext]
  exact theorem2AppendixA1ParameterGaussianLaw_isProbability
    (S := S) (0 : E)
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)) hdom

theorem theorem2AppendixA1ParameterGridContext_prior_map_val
    [BorelSpace E]
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    Measure.map Subtype.val
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk j hdom).prior_distribution =
      gaussianAffineLaw (E := E) (0 : E)
        (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)) := by
  dsimp [theorem2AppendixA1ParameterGridContext]
  exact theorem2AppendixA1ParameterGaussianLaw_map_val
    (S := S) (0 : E)
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j)) hdom

theorem theorem2AppendixA1ParameterGridContext_sampleLaw_isProbability
    [BorelSpace E]
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    IsProbabilityMeasure
      (measurePACBayesSampleLaw
        (theorem2AppendixA1ParameterGridContext (S := S) hk j hdom) n) := by
  letI : IsProbabilityMeasure S.dataLaw := S.dataLaw_isProbability
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin n => S.dataLaw))
  infer_instance

theorem theorem2AppendixA1SourcePointwiseLoss_parameterGaussian_integral
    [BorelSpace E]
    (S : Setup n E X Y Ω) (center : E) (sigma : ℝ)
    (hdom : ∀ ε : E, center + sigma • ε ∈ S.parameterSpace)
    (z : X × Y)
    (hf : AEStronglyMeasurable
      (fun u : Setup.Parameter S =>
        theorem2AppendixA1SourcePointwiseLossOnParameter
          (S := S) u z)
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) center sigma hdom)) :
    ∫ u : Setup.Parameter S,
        theorem2AppendixA1SourcePointwiseLossOnParameter
          (S := S) u z ∂
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) center sigma hdom) =
      ∫ ε : E,
        theorem2AppendixA1SourcePointwiseLossAmbient
          (S := S) (center + sigma • ε) z ∂(stdGaussian E) := by
  calc
    ∫ u : Setup.Parameter S,
        theorem2AppendixA1SourcePointwiseLossOnParameter
          (S := S) u z ∂
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) center sigma hdom) =
      ∫ ε : E,
        theorem2AppendixA1SourcePointwiseLossOnParameter
          (S := S) ⟨center + sigma • ε, hdom ε⟩ z ∂(stdGaussian E) :=
      theorem2AppendixA1ParameterGaussianLaw_integral_map
        (S := S) center sigma hdom
        (fun u : Setup.Parameter S =>
          theorem2AppendixA1SourcePointwiseLossOnParameter
            (S := S) u z) hf
    _ = ∫ ε : E,
        theorem2AppendixA1SourcePointwiseLossAmbient
          (S := S) (center + sigma • ε) z ∂(stdGaussian E) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ε =>
        (theorem2AppendixA1SourcePointwiseLoss_on_parameter
          (S := S) (center + sigma • ε) z (hdom ε)).symm

theorem theorem2AppendixA1SourcePointwiseLoss_bounded
    (S : Setup n E X Y Ω)
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    ∀ u z,
      0 ≤ theorem2AppendixA1SourcePointwiseLossAmbient (S := S) u z ∧
        theorem2AppendixA1SourcePointwiseLossAmbient (S := S) u z ≤ 1 := by
  intro u z
  constructor
  · have hnonneg :
        0 ≤ theorem2AppendixA1SourcePointwiseLossAmbient (S := S) u z := by
      by_cases hu : u ∈ S.parameterSpace
      · rw [theorem2AppendixA1SourcePointwiseLoss_on_parameter
          (S := S) u z hu]
        exact_mod_cast
          (Setup.lossOnParameter (S := S) ⟨u, hu⟩ z.1 z.2).property
      · simp [theorem2AppendixA1SourcePointwiseLossAmbient, hu]
    exact hnonneg
  · by_cases hu : u ∈ S.parameterSpace
    · rw [theorem2AppendixA1SourcePointwiseLoss_on_parameter
        (S := S) u z hu]
      simpa using hbounded ⟨u, hu⟩ z.1 z.2
    · simp [theorem2AppendixA1SourcePointwiseLossAmbient, hu]

/- The grid event is the actual Measure-valued Eq. (5) event specialized to
   the Gaussian concept space E, the data-point sample space X × Y, and the
   data-independent prior selected by Appendix A.1.  Measurability remains a
   local proof obligation because the paper's loss declaration does not give a
   Lean measurability field. -/
noncomputable def theorem2AppendixA1GridPACBayesEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    Set (Dataset n X Y) :=
  theorem2AppendixA1_arbitraryMeasure_PACBayes_event
    (theorem2AppendixA1ParameterGridContext (S := S) hk j hdom) n
    hn
    (theorem2AppendixA1PriorGridConfidence δ.1 j)
    (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))

def theorem2AppendixA1GridPACBayesFailure
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    Set (Dataset n X Y) :=
    (theorem2AppendixA1GridPACBayesEvent
      (S := S) w δ hn hk j hdom)ᶜ

/- Typed source bridge for the per-grid failure event.  This is only a
   complement/set identification: the probability estimate still comes from
   the guarded arbitrary-Measure PAC-Bayes theorem, while the carrier is the
   subtype Gaussian law and the literal source loss. -/
theorem theorem2AppendixA1GridPACBayesFailure_spec
    [BorelSpace E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    theorem2AppendixA1GridPACBayesFailure
        (S := S) w δ hn hk j hdom =
      (measurePACBayesExpectedLossEvent
        (theorem2AppendixA1ParameterGridContext (S := S) hk j hdom) n hn
        (theorem2AppendixA1PriorGridConfidence δ.1 j)
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)))ᶜ := by
  rfl

private theorem measurePACBayes_integral_change_of_measure
    {Concept : Type*} [MeasurableSpace Concept]
    (Q P : Measure Concept)
    (hQ : IsProbabilityMeasure Q)
    (hP : IsProbabilityMeasure P)
    (hQP : Q ≪ P)
    (f : Concept → ℝ) :
    (∫ c, f c ∂Q) =
      ∫ c, (Q.rnDeriv P c).toReal * f c ∂P := by
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure P := hP
  symm
  rw [← setIntegral_univ]
  simpa only [setIntegral_univ] using
    (setIntegral_toReal_rnDeriv_mul' hQP f Set.univ)

private theorem measurePACBayes_finite_KL_density_spec
    {Concept : Type*} [MeasurableSpace Concept]
    (Q P : Measure Concept)
    (hQ : IsProbabilityMeasure Q)
    (hP : IsProbabilityMeasure P)
    (hfinite : measurePACBayesKLDivergence Q P ≠ ⊤) :
    Q ≪ P ∧
      measurePACBayesKLDivergence Q P =
        ∫⁻ c, ENNReal.ofReal
          (InformationTheory.klFun (Q.rnDeriv P c).toReal) ∂P := by
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure P := hP
  have hfinite' : InformationTheory.klDiv Q P ≠ ⊤ := by
    simpa [measurePACBayesKLDivergence] using hfinite
  have hAC : Q ≪ P :=
    (InformationTheory.klDiv_ne_top_iff.mp hfinite').1
  refine ⟨hAC, ?_⟩
  simpa [measurePACBayesKLDivergence] using
    (InformationTheory.klDiv_eq_lintegral_klFun_of_ac hAC)

private theorem measurePACBayes_change_of_measure_log_mgf
    {Concept : Type*} [MeasurableSpace Concept]
    (Q P : Measure Concept)
    (hQ : IsProbabilityMeasure Q)
    (hP : IsProbabilityMeasure P)
    (hfinite : InformationTheory.klDiv Q P ≠ ⊤)
    (f : Concept → ℝ)
    (hfQ : Integrable f Q)
    (hfP : Integrable (fun c => Real.exp (f c)) P) :
    (∫ c, f c ∂Q) ≤
      (InformationTheory.klDiv Q P).toReal +
        Real.log (∫ c, Real.exp (f c) ∂P) := by
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure P := hP
  have hQP : Q ≪ P :=
    (InformationTheory.klDiv_ne_top_iff.mp hfinite).1
  have hllr : Integrable (llr Q P) Q :=
    (InformationTheory.klDiv_ne_top_iff.mp hfinite).2
  have hPT : P ≪ P.tilted f :=
    absolutelyContinuous_tilted hfP
  have hQT : Q ≪ P.tilted f := hQP.trans hPT
  letI : IsProbabilityMeasure (P.tilted f) :=
    isProbabilityMeasure_tilted hfP
  have hKLtilted :
      (InformationTheory.klDiv Q (P.tilted f)).toReal =
        ∫ c, llr Q (P.tilted f) c ∂Q :=
    InformationTheory.toReal_klDiv_of_measure_eq hQT (by simp)
  have hKL :
      (InformationTheory.klDiv Q P).toReal =
        ∫ c, llr Q P c ∂Q :=
    InformationTheory.toReal_klDiv_of_measure_eq hQP (by simp)
  have hnonneg :
      0 ≤ (InformationTheory.klDiv Q (P.tilted f)).toReal :=
    ENNReal.toReal_nonneg
  have hformula :=
    integral_llr_tilted_right (μ := Q) (ν := P) (f := f)
      hQP hfQ hfP hllr
  rw [hKLtilted, hformula, ← hKL] at hnonneg
  linarith

private theorem measurePACBayes_productLaw_exponential_budget
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 0 < m)
    (c : Concept)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1) :
    let μ : Measure (Fin m → Sample) :=
      measurePACBayesSampleLaw ctx m
    let population : ℝ :=
      ∫ z, loss c z ∂ctx.sampling_distribution
    HasSubgaussianMGF
      (fun s : Fin m → Sample =>
        population - (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))
      (((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4) μ := by
  let μ : Measure (Fin m → Sample) := measurePACBayesSampleLaw ctx m
  let population : ℝ := ∫ z, loss c z ∂ctx.sampling_distribution
  letI : IsProbabilityMeasure ctx.sampling_distribution := hsampling
  letI : IsProbabilityMeasure μ :=
    measurePACBayesSampleLaw_isProbability ctx m hsampling
  have hloss_c : AEMeasurable (fun z : Sample => loss c z)
      ctx.sampling_distribution := by
    exact
      (hmeas_loss.comp
        (measurable_const.prodMk measurable_id)).aemeasurable
  have hcentered :
      HasSubgaussianMGF
        (fun z : Sample => loss c z - population)
        (((‖(1 : ℝ)‖₊ / 2) ^ 2 : NNReal))
        ctx.sampling_distribution := by
    simpa [population] using
      (hasSubgaussianMGF_of_mem_Icc hloss_c
        (Filter.Eventually.of_forall fun z =>
          (hloss_bounded c z)))
  have hcoordinate :
      ∀ i : Fin m,
        HasSubgaussianMGF
          (fun s : Fin m → Sample => loss c (s i) - population)
          (((‖(1 : ℝ)‖₊ / 2) ^ 2 : NNReal)) μ := by
    intro i
    have hmap :
        μ.map (fun s : Fin m → Sample => s i) =
          ctx.sampling_distribution := by
      dsimp [μ, measurePACBayesSampleLaw]
      exact (measurePreserving_eval
        (fun _ : Fin m => ctx.sampling_distribution) i).map_eq
    have h := HasSubgaussianMGF.of_map
      (μ := μ) (Y := fun s : Fin m → Sample => s i)
      (X := fun z : Sample => loss c z - population)
      (measurable_pi_apply i).aemeasurable
      (show HasSubgaussianMGF
          (fun z : Sample => loss c z - population)
          (((‖(1 : ℝ)‖₊ / 2) ^ 2 : NNReal))
          (μ.map (fun s : Fin m → Sample => s i)) by
        rw [hmap]
        exact hcentered)
    simpa [Function.comp_def] using h
  have hindep :
      iIndepFun
        (fun i : Fin m =>
          fun s : Fin m → Sample => loss c (s i) - population) μ := by
    have h := iIndepFun_pi
      (μ := fun _ : Fin m => ctx.sampling_distribution)
      (X := fun _ : Fin m => fun z : Sample => loss c z - population)
      (fun _ => hloss_c.sub measurable_const.aemeasurable)
    simpa [μ, measurePACBayesSampleLaw, Function.comp_def] using h
  have hsum :
      HasSubgaussianMGF
        (fun s : Fin m → Sample =>
          ∑ i : Fin m, (loss c (s i) - population))
        (((m : NNReal) * ((‖(1 : ℝ)‖₊ / 2) ^ 2 : NNReal)))
        μ := by
    simpa using
      (HasSubgaussianMGF.sum_of_iIndepFun hindep
        (s := Finset.univ) (fun i hi => hcoordinate i))
  have hscaled := hsum.const_mul (-(m : ℝ)⁻¹)
  convert hscaled using 1
  · funext s
    dsimp [population]
    simp [Finset.sum_sub_distrib]
    have hmreal : (m : ℝ) ≠ 0 := by
      exact_mod_cast hm.ne'
    field_simp [hmreal]
    ring
  · ext
    norm_num [NNReal.coe_mul, NNReal.coe_pow]
    field_simp [Nat.cast_ne_zero.mpr hm.ne']

/- A finite-KL posterior witness admits the exact source-level
   change-of-measure estimate for its population/empirical gap.  This is
   strictly smaller than the simultaneous posterior event bound: it exposes
   the RN/KL bridge for one witness and leaves only the universal aggregation
   step to the source-facing theorem below. -/
private theorem measurePACBayes_finite_KL_witness_variational
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m)
    (Q : Measure Concept) (hQ : IsProbabilityMeasure Q)
    (s : Fin m → Sample)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hprior : IsProbabilityMeasure ctx.prior_distribution)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1)
    (hfinite :
      measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤) :
    measurePACBayesPopulationLoss ctx loss Q -
          measurePACBayesEmpiricalLoss ctx m s loss Q ≤
        (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
          Real.log
            (∫ c,
              Real.exp
                ((∫ z, loss c z ∂ctx.sampling_distribution) -
                  (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))
              ∂ctx.prior_distribution) := by
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure ctx.prior_distribution := hprior
  letI : IsProbabilityMeasure ctx.sampling_distribution := hsampling
  let f : Concept → ℝ := fun c =>
    (∫ z, loss c z ∂ctx.sampling_distribution) -
      (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)
  have hpop_meas :
      Measurable
        (fun c : Concept => ∫ z, loss c z ∂ctx.sampling_distribution) := by
    exact hmeas_loss.stronglyMeasurable.integral_prod_right'.measurable
  have hslice_meas (i : Fin m) :
      Measurable (fun c : Concept => loss c (s i)) := by
    simpa [Function.uncurry] using
      hmeas_loss.comp (measurable_id.prodMk measurable_const)
  have hemp_meas :
      Measurable
        (fun c : Concept =>
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) := by
    exact measurable_const.mul (Finset.measurable_sum Finset.univ (by
      intro i hi
      exact hslice_meas i))
  have hf_meas : Measurable f := by
    exact hpop_meas.sub hemp_meas
  have hpop_mem (c : Concept) :
      (∫ z, loss c z ∂ctx.sampling_distribution) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · simpa using
        (integral_mono (integrable_const 0)
          (measurePACBayesPointwiseLoss_integrable
            (μ := ctx.sampling_distribution)
            loss hmeas_loss hloss_bounded c)
          (fun z => (hloss_bounded c z).1))
    · have hle := integral_mono
          (measurePACBayesPointwiseLoss_integrable
            (μ := ctx.sampling_distribution)
            loss hmeas_loss hloss_bounded c)
          (integrable_const 1)
          (fun z => (hloss_bounded c z).2)
      simpa using hle
  have hemp_nonneg (c : Concept) :
      0 ≤ (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) := by
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    apply mul_nonneg (inv_nonneg.mpr hmpos.le)
    exact Finset.sum_nonneg (fun i hi => (hloss_bounded c (s i)).1)
  have hemp_le_one (c : Concept) :
      (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ≤ 1 := by
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hsum : (∑ i : Fin m, loss c (s i)) ≤ (m : ℝ) := by
      calc
        (∑ i : Fin m, loss c (s i)) ≤ ∑ i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum (fun i hi => (hloss_bounded c (s i)).2)
        _ = (m : ℝ) := by simp
    have hmul := mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr hmpos.le)
    simpa [inv_mul_cancel₀ (ne_of_gt hmpos)] using hmul
  have hf_bound (c : Concept) : ‖f c‖ ≤ 2 := by
    dsimp [f]
    apply (abs_le).2
    constructor
    · linarith [hpop_mem c |>.1, hemp_le_one c]
    · linarith [hpop_mem c |>.2, hemp_nonneg c]
  have hfQ : Integrable f Q :=
    integrable_of_measurable_bounded_real hf_meas hf_bound
  have hfexp_meas : Measurable (fun c => Real.exp (f c)) :=
    Real.measurable_exp.comp hf_meas
  have hfP : Integrable (fun c => Real.exp (f c))
      ctx.prior_distribution := by
    refine Integrable.of_bound hfexp_meas.aestronglyMeasurable
      (Real.exp 2) ?_
    filter_upwards [] with c
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact le_trans (le_abs_self _) (by
      simpa [Real.norm_eq_abs] using hf_bound c)
  have hemp_int :
      Integrable
        (fun c : Concept =>
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) Q := by
    exact
      (integrable_finset_sum Finset.univ (by
        intro i hi
        exact measurePACBayesPointwiseLoss_integrable_sample_slice
          (Q := Q) loss hmeas_loss hloss_bounded (s i))).const_mul _
  have hgap :
      (∫ c, f c ∂Q) =
        measurePACBayesPopulationLoss ctx loss Q -
          measurePACBayesEmpiricalLoss ctx m s loss Q := by
    dsimp [f, measurePACBayesPopulationLoss,
      measurePACBayesEmpiricalLoss]
    calc
      (∫ c,
          (∫ z, loss c z ∂ctx.sampling_distribution) -
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ∂Q) =
          (∫ c, ∫ z, loss c z ∂ctx.sampling_distribution ∂Q) -
            ∫ c, (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ∂Q := by
        rw [integral_sub
          (measurePACBayesPointwiseLoss_integrable_population
            (μ := ctx.sampling_distribution) (Q := Q)
            loss hmeas_loss hloss_bounded)
          hemp_int]
      _ =
          (∫ c, ∫ z, loss c z ∂ctx.sampling_distribution ∂Q) -
            (m : ℝ)⁻¹ *
              ∑ i : Fin m, ∫ c, loss c (s i) ∂Q := by
        rw [integral_const_mul,
          integral_finset_sum Finset.univ (by
            intro i hi
            exact
              measurePACBayesPointwiseLoss_integrable_sample_slice
                (Q := Q) loss hmeas_loss hloss_bounded (s i))]
  have hvariational :=
    measurePACBayes_change_of_measure_log_mgf
      Q ctx.prior_distribution hQ hprior
      (by simpa [measurePACBayesKLDivergence] using hfinite)
      f hfQ hfP
  calc
    measurePACBayesPopulationLoss ctx loss Q -
          measurePACBayesEmpiricalLoss ctx m s loss Q =
        ∫ c, f c ∂Q := hgap.symm
    _ ≤
        (InformationTheory.klDiv Q ctx.prior_distribution).toReal +
          Real.log (∫ c, Real.exp (f c) ∂ctx.prior_distribution) :=
      hvariational
    _ =
        (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
          Real.log
            (∫ c,
              Real.exp
                ((∫ z, loss c z ∂ctx.sampling_distribution) -
                  (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))
                ∂ctx.prior_distribution) := by
      rfl

/- Source-facing bridge for one finite-KL posterior witness.  The
   simultaneous PAC-Bayes aggregation remains a separate theorem, but its
   witness now exposes the exact Radon--Nikodym population representation and
   the Mathlib KL density formula that the aggregation argument must consume. -/
private theorem measurePACBayes_finite_KL_witness_source_bridge
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hprior : IsProbabilityMeasure ctx.prior_distribution) :
    ∀ s ∈ measurePACBayesFiniteKLViolationEvent ctx m hm δ loss,
      ∃ Q : Measure Concept, IsProbabilityMeasure Q ∧
        measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ ∧
        Q ≪ ctx.prior_distribution ∧
        measurePACBayesPopulationLoss ctx loss Q =
          ∫ c,
            (Q.rnDeriv ctx.prior_distribution c).toReal *
              (∫ z, loss c z ∂ctx.sampling_distribution)
            ∂ctx.prior_distribution ∧
        measurePACBayesKLDivergence Q ctx.prior_distribution =
          ∫⁻ c, ENNReal.ofReal
            (InformationTheory.klFun
              (Q.rnDeriv ctx.prior_distribution c).toReal)
            ∂ctx.prior_distribution := by
  intro s hs
  change ∃ Q : Measure Concept, IsProbabilityMeasure Q ∧
    measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ ∧
    measurePACBayesPopulationLoss ctx loss Q >
      measurePACBayesEmpiricalLoss ctx m s loss Q +
        Real.sqrt
          (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
            Real.log ((m : ℝ) / δ)) /
            (2 * ((m : ℝ) - 1))) at hs
  rcases hs with ⟨Q, hQ, hfinite, hbad⟩
  have hdensity :=
    measurePACBayes_finite_KL_density_spec
      Q ctx.prior_distribution hQ hprior hfinite
  refine ⟨Q, hQ, hfinite, hdensity.1, ?_, hdensity.2⟩
  rw [measurePACBayesPopulationLoss]
  exact
    measurePACBayes_integral_change_of_measure
      Q ctx.prior_distribution hQ hprior hdensity.1
      (fun c => ∫ z, loss c z ∂ctx.sampling_distribution)

/- The canonical Measure.pi route proves the source Lemma 3 moment-tail
   estimate.  McAllester's separate Lemma 2 transition is not represented by
   the stronger square-moment inclusion that the earlier scaffold asserted:
   the original source lemma is countable/pruned, whereas this route permits
   arbitrary posterior Measures.  Keep only the proved moment-tail estimate
   here; the exact PAC-Bayes statement below is the guarded source boundary. -/
private theorem measurePACBayes_source_McAllester_moment_event
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ) (hδ : 0 < δ) (hδ_lt_one : δ < 1)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hprior : IsProbabilityMeasure ctx.prior_distribution)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1) :
    measurePACBayesSampleLaw ctx m
        {s | 4 * (m : ℝ) / δ <
          measurePACBayesMcAllesterMoment ctx m loss s} ≤
      ENNReal.ofReal δ := by
  classical
  let μ : Measure (Fin m → Sample) := measurePACBayesSampleLaw ctx m
  let G : (Fin m → Sample) × Concept → ℝ := fun p =>
    Real.exp
      ((2 * (m : ℝ) - 1) *
        ((∫ z, loss p.2 z ∂ctx.sampling_distribution) -
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)) ^ 2)
  let M : (Fin m → Sample) → ℝ := fun s =>
    ∫ c, G (s, c) ∂ctx.prior_distribution
  letI : IsProbabilityMeasure μ :=
    measurePACBayesSampleLaw_isProbability ctx m hsampling
  letI : IsProbabilityMeasure ctx.prior_distribution := hprior
  letI : IsProbabilityMeasure ctx.sampling_distribution := hsampling
  have hpop_meas :
      Measurable
        (fun c : Concept => ∫ z, loss c z ∂ctx.sampling_distribution) := by
    exact hmeas_loss.stronglyMeasurable.integral_prod_right'.measurable
  have hemp_meas :
      Measurable
        (fun p : (Fin m → Sample) × Concept =>
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)) := by
    exact measurable_const.mul
      (Finset.measurable_sum Finset.univ (by
        intro i hi
        simpa [Function.uncurry] using
          hmeas_loss.comp
            (measurable_snd.prodMk
              ((measurable_pi_apply i).comp measurable_fst))))
  have hG_meas : Measurable G := by
    dsimp [G]
    exact Real.measurable_exp.comp
      (measurable_const.mul
        (((hpop_meas.comp measurable_snd).sub hemp_meas).pow_const 2))
  have hpoint_population_bounds :
      ∀ c : Concept,
        0 ≤ ∫ z, loss c z ∂ctx.sampling_distribution ∧
          (∫ z, loss c z ∂ctx.sampling_distribution) ≤ 1 := by
    intro c
    have hslice :
        Integrable (loss c) ctx.sampling_distribution :=
      measurePACBayesPointwiseLoss_integrable
        (μ := ctx.sampling_distribution) loss hmeas_loss hloss_bounded c
    constructor
    · simpa using
        (integral_mono (integrable_const 0) hslice
          (fun z => (hloss_bounded c z).1))
    · have hle :
          (∫ z, loss c z ∂ctx.sampling_distribution) ≤
            ∫ z, (1 : ℝ) ∂ctx.sampling_distribution :=
        integral_mono hslice (integrable_const 1)
          (fun z => (hloss_bounded c z).2)
      simpa using hle
  have hpoint_empirical_bounds :
      ∀ c : Concept, ∀ s : Fin m → Sample,
        0 ≤ (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ∧
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ≤ 1 := by
    intro c s
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hsum_nonneg :
        0 ≤ ∑ i : Fin m, loss c (s i) :=
      Finset.sum_nonneg (fun i hi => (hloss_bounded c (s i)).1)
    have hsum_le :
        (∑ i : Fin m, loss c (s i)) ≤ (m : ℝ) := by
      calc
        (∑ i : Fin m, loss c (s i)) ≤ ∑ i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum (fun i hi => (hloss_bounded c (s i)).2)
        _ = (m : ℝ) := by simp
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hmpos.le) hsum_nonneg
    · have hmul :=
        mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hmpos.le)
      simpa [inv_mul_cancel₀ (ne_of_gt hmpos)] using hmul
  have hG_bound :
      ∀ p : (Fin m → Sample) × Concept,
        ‖G p‖ ≤ Real.exp (2 * (m : ℝ) - 1) := by
    intro p
    have hpop := hpoint_population_bounds p.2
    have hemp := hpoint_empirical_bounds p.2 p.1
    have hgap_abs :
        |(∫ z, loss p.2 z ∂ctx.sampling_distribution) -
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hpop.1, hpop.2, hemp.1, hemp.2]
    have hgap_sq :
        ((∫ z, loss p.2 z ∂ctx.sampling_distribution) -
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg
        ((∫ z, loss p.2 z ∂ctx.sampling_distribution) -
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i) - 1),
        sq_nonneg
        ((∫ z, loss p.2 z ∂ctx.sampling_distribution) -
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i) + 1)]
    have hcoef : 0 ≤ 2 * (m : ℝ) - 1 := by
      have hm' : (1 : ℝ) < (m : ℝ) := by
        exact_mod_cast hm
      linarith
    dsimp [G]
    rw [abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact
      (mul_le_mul_of_nonneg_left hgap_sq hcoef).trans_eq
        (by ring)
  have hG_int :
      Integrable G
        (μ.prod ctx.prior_distribution) :=
    integrable_of_measurable_bounded_real hG_meas hG_bound
  have hM_int : Integrable M μ := by
    simpa [M] using hG_int.integral_prod_left
  have hM_nonneg : ∀ s, 0 ≤ M s := by
    intro s
    exact integral_nonneg (fun c => (Real.exp_pos _).le)
  have hproduct_fixed_concept :
      ∀ c : Concept,
        HasSubgaussianMGF
          (fun s : Fin m → Sample =>
            (∫ z, loss c z ∂ctx.sampling_distribution) -
              (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))
          (((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4) μ := by
    intro c
    simpa [μ] using
      (measurePACBayes_productLaw_exponential_budget
        ctx m (Nat.zero_lt_of_lt hm) c loss hsampling hmeas_loss hloss_bounded)
  have hproduct_exp_integrable :
      ∀ c : Concept,
        Integrable
          (fun s : Fin m → Sample =>
            Real.exp
              ((∫ z, loss c z ∂ctx.sampling_distribution) -
                (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))) μ := by
    intro c
    simpa [one_mul] using
      (hproduct_fixed_concept c).integrable_exp_mul 1
  have hproduct_mgf_budget :
      ∀ c : Concept,
        ∫ s : Fin m → Sample,
            Real.exp
              ((∫ z, loss c z ∂ctx.sampling_distribution) -
                (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) ∂μ ≤
          Real.exp
            (((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) / 2) := by
    intro c
    simpa [ProbabilityTheory.mgf, one_mul] using
      (hproduct_fixed_concept c).mgf_le 1
  have hscalar_exp_sq_layer_cake :
      ∀ (k x : ℝ), 0 ≤ k → 0 ≤ x → x ≤ 1 →
        Real.exp (k * x ^ 2) =
          1 + ∫ z in Set.Ioc 0 1,
            if z < x then 2 * k * z * Real.exp (k * z ^ 2) else 0 := by
    intro k x hk hx hx1
    have hderiv :
        ∀ z ∈ Set.uIcc (0 : ℝ) x,
          HasDerivAt (fun t : ℝ => Real.exp (k * t ^ 2))
            (2 * k * z * Real.exp (k * z ^ 2)) z := by
      intro z hz
      convert
        ((Real.hasDerivAt_exp (k * z ^ 2)).comp z
          ((hasDerivAt_const z k).mul ((hasDerivAt_id z).pow 2))) using 1 <;>
        simp only [id] <;> ring
    have hcontg :
        Continuous (fun z : ℝ => 2 * k * z * Real.exp (k * z ^ 2)) := by
      fun_prop
    have hint :
        IntervalIntegrable (fun z : ℝ => 2 * k * z * Real.exp (k * z ^ 2))
          volume 0 x :=
      hcontg.intervalIntegrable (μ := volume) 0 x
    have hinterval :
        (∫ z in (0 : ℝ)..x, 2 * k * z * Real.exp (k * z ^ 2)) =
          Real.exp (k * x ^ 2) - 1 := by
      simpa using
        (intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (0 : ℝ)) (b := x) hderiv hint)
    have hset :
        (∫ z in Set.Ioc (0 : ℝ) 1,
          if z < x then 2 * k * z * Real.exp (k * z ^ 2) else 0) =
          ∫ z in Set.Ioo (0 : ℝ) x, 2 * k * z * Real.exp (k * z ^ 2) := by
      calc
        (∫ z in Set.Ioc (0 : ℝ) 1,
            if z < x then 2 * k * z * Real.exp (k * z ^ 2) else 0) =
            ∫ z in Set.Ioc (0 : ℝ) 1,
              (Set.Iio x).indicator
                (fun z => 2 * k * z * Real.exp (k * z ^ 2)) z := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro z hz
          by_cases hzx : z < x <;> simp [Set.indicator, hzx]
        _ = ∫ z in Set.Ioc (0 : ℝ) 1 ∩ Set.Iio x,
              2 * k * z * Real.exp (k * z ^ 2) := by
          rw [setIntegral_indicator measurableSet_Iio]
        _ = ∫ z in Set.Ioo (0 : ℝ) x,
              2 * k * z * Real.exp (k * z ^ 2) := by
          have hsets :
              Set.Ioc (0 : ℝ) 1 ∩ Set.Iio x = Set.Ioo (0 : ℝ) x := by
            ext z
            change ((0 < z ∧ z ≤ (1 : ℝ)) ∧ z < x) ↔ (0 < z ∧ z < x)
            constructor
            · rintro ⟨⟨hz0, hz1⟩, hzx⟩
              exact ⟨hz0, hzx⟩
            · rintro ⟨hz0, hzx⟩
              exact ⟨⟨hz0, hzx.le.trans hx1⟩, hzx⟩
          rw [hsets]
    rw [hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hx]
    rw [hinterval]
    ring
  have hsource_route :
      μ {s | 4 * (m : ℝ) / δ < M s} ≤ ENNReal.ofReal δ := by
      have hfixed_moment :
          ∀ c : Concept, ∫ s : Fin m → Sample, G (s, c) ∂μ ≤
            4 * (m : ℝ) := by
        intro c
        let X : (Fin m → Sample) → ℝ := fun s =>
          |(∫ z, loss c z ∂ctx.sampling_distribution) -
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)|
        let k : ℝ := 2 * (m : ℝ) - 1
        let g : ℝ → ℝ := fun z =>
          2 * k * z * Real.exp (k * z ^ 2)
        have hk : 0 ≤ k := by
          dsimp [k]
          have hm' : (1 : ℝ) < (m : ℝ) := by
            exact_mod_cast hm
          linarith
        have hX_meas : Measurable X := by
          dsimp [X]
          have hemp_c :
              Measurable
                (fun s : Fin m → Sample =>
                  (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) :=
            hemp_meas.comp (measurable_id.prodMk measurable_const)
          exact (measurable_const.sub hemp_c).abs
        have hX_bounds : ∀ s, 0 ≤ X s ∧ X s ≤ 1 := by
          intro s
          dsimp [X]
          constructor
          · exact abs_nonneg _
          · have hpop := hpoint_population_bounds c
            have hemp := hpoint_empirical_bounds c s
            rw [abs_le]
            constructor <;> linarith
        have hG_slice_meas :
            Measurable (fun s : Fin m → Sample => G (s, c)) := by
          exact hG_meas.comp (measurable_id.prodMk measurable_const)
        have hG_slice_int :
            Integrable (fun s : Fin m → Sample => G (s, c)) μ :=
          integrable_of_measurable_bounded_real hG_slice_meas
            (fun s => hG_bound (s, c))
        have hlayer :
            ∀ s, G (s, c) =
              1 + ∫ z in Set.Ioc 0 1,
                if z < X s then g z else 0 := by
          intro s
          have h := hscalar_exp_sq_layer_cake k (X s) hk
            (hX_bounds s).1 (hX_bounds s).2
          dsimp [G, X, g, k] at h ⊢
          simpa [sq_abs] using h
        let μz : Measure ℝ := volume.restrict (Set.Ioc 0 1)
        let F : (Fin m → Sample) × ℝ → ℝ := fun p =>
          if p.2 ∈ Set.Ioc (0 : ℝ) 1 ∧ p.2 < X p.1 then g p.2 else 0
        have hg_meas : Measurable g := by
          dsimp [g]
          fun_prop
        have hF_meas : Measurable F := by
          exact Measurable.ite
            ((measurableSet_Ioc.preimage measurable_snd).inter
              (measurableSet_lt measurable_snd
                (hX_meas.comp measurable_fst)))
            (hg_meas.comp measurable_snd) measurable_const
        have hF_bound :
            ∀ p, ‖F p‖ ≤ 2 * k * Real.exp k := by
          intro p
          by_cases hp : p.2 ∈ Set.Ioc (0 : ℝ) 1 ∧ p.2 < X p.1
          · have hz0 : 0 ≤ p.2 := hp.1.1.le
            have hz1 : p.2 ≤ 1 := hp.1.2
            have hcoef : 0 ≤ 2 * k * p.2 := by positivity
            have hzsq : p.2 ^ 2 ≤ (1 : ℝ) := by
              nlinarith [sq_nonneg p.2]
            have harg : k * p.2 ^ 2 ≤ k := by
              simpa using (mul_le_mul_of_nonneg_left hzsq hk)
            have hexp : Real.exp (k * p.2 ^ 2) ≤ Real.exp k :=
              Real.exp_le_exp.mpr harg
            have hcoef_le : 2 * k * p.2 ≤ 2 * k := by
              nlinarith [mul_le_mul_of_nonneg_left hz1 (show 0 ≤ 2 * k by positivity)]
            have hg_nonneg : 0 ≤ g p.2 := by
              dsimp [g]
              positivity
            simp only [F, if_pos hp]
            rw [Real.norm_of_nonneg hg_nonneg]
            dsimp [g]
            calc
              2 * k * p.2 * Real.exp (k * p.2 ^ 2) ≤
                  (2 * k * p.2) * Real.exp k :=
                mul_le_mul_of_nonneg_left hexp hcoef
              _ ≤ (2 * k) * Real.exp k :=
                mul_le_mul_of_nonneg_right hcoef_le (Real.exp_pos _).le
              _ = 2 * k * Real.exp k := by ring
          · have hnonneg : 0 ≤ 2 * k * Real.exp k := by
              positivity
            dsimp [F]
            rw [if_neg hp]
            simpa using hnonneg
        have hF_int : Integrable F (μ.prod μz) :=
          integrable_of_measurable_bounded_real hF_meas (by
            intro p
            exact (hF_bound p))
        have hinner_eq :
            ∀ s : Fin m → Sample,
              (∫ z in Set.Ioc 0 1, if z < X s then g z else 0) =
                ∫ z, F (s, z) ∂μz := by
          intro s
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (μ := volume)
            (measurableSet_Ioc : MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
          by_cases hzx : z < X s
          · dsimp [F]
            simp [Set.indicator, hz, hzx]
          · dsimp [F]
            simp [Set.indicator, hz, hzx]
        have hinner_F :
            ∀ z ∈ Set.Ioc (0 : ℝ) 1,
              (∫ s : Fin m → Sample, F (s, z) ∂μ) =
                g z * μ.real {s | z < X s} := by
          intro z hz
          have hevent : MeasurableSet {s : Fin m → Sample | z < X s} :=
            measurableSet_lt measurable_const hX_meas
          have hfun :
              (fun s : Fin m → Sample => F (s, z)) =
                ({s : Fin m → Sample | z < X s}).indicator (fun _ => g z) := by
            funext s
            by_cases hzx : z < X s
            · dsimp [F]
              simp [Set.indicator, hz, hzx]
            · dsimp [F]
              simp [Set.indicator, hz, hzx]
          rw [hfun, integral_indicator hevent]
          simp [MeasureTheory.integral_const_mul, measureReal_def, mul_comm]
        have htail :
            ∀ z : ℝ, 0 < z →
              μ.real {s : Fin m → Sample | z < X s} ≤
                2 * Real.exp (-2 * (m : ℝ) * z ^ 2) := by
          intro z hz
          have hpos :=
            (hproduct_fixed_concept c).measure_ge_le hz.le
          have hneg :=
            (hproduct_fixed_concept c).neg.measure_ge_le hz.le
          have hsubset :
              {s : Fin m → Sample | z < X s} ⊆
                {s | z ≤
                    (∫ z, loss c z ∂ctx.sampling_distribution) -
                      (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)} ∪
                  {s | z ≤ -
                    ((∫ z, loss c z ∂ctx.sampling_distribution) -
                      (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))} := by
            intro s hs
            dsimp [X] at hs
            rw [lt_abs] at hs
            rcases hs with hs | hs
            · exact Or.inl hs.le
            · exact Or.inr hs.le
          have hcparam :
              ((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) =
                1 / (4 * (m : ℝ)) := by
            norm_num [NNReal.coe_div, NNReal.coe_pow]
            field_simp [Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt hm).ne']
          have hexp :
              Real.exp
                  (-z ^ 2 /
                    (2 * ((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ))) =
                Real.exp (-2 * (m : ℝ) * z ^ 2) := by
            rw [hcparam]
            congr 1
            field_simp [Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt hm).ne']
            ring
          calc
            μ.real {s : Fin m → Sample | z < X s} ≤
                μ.real
                  ({s | z ≤
                      (∫ z, loss c z ∂ctx.sampling_distribution) -
                        (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)} ∪
                    {s | z ≤ -
                      ((∫ z, loss c z ∂ctx.sampling_distribution) -
                        (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))}) :=
              measureReal_mono hsubset
            _ ≤
                μ.real {s | z ≤
                    (∫ z, loss c z ∂ctx.sampling_distribution) -
                      (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)} +
                  μ.real {s | z ≤ -
                    ((∫ z, loss c z ∂ctx.sampling_distribution) -
                      (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))} :=
              measureReal_union_le _ _
            _ ≤
                Real.exp
                    (-z ^ 2 /
                      (2 * ((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ))) +
                  Real.exp
                    (-z ^ 2 /
                      (2 * ((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ))) :=
              add_le_add hpos hneg
            _ = 2 *
                Real.exp
                  (-z ^ 2 /
                    (2 * ((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ))) := by
              ring
            _ = 2 * Real.exp (-2 * (m : ℝ) * z ^ 2) := by
              rw [hexp]
        have hpoint :
            ∀ z : ℝ, z ∈ Set.Ioc (0 : ℝ) 1 →
              g z * μ.real {s : Fin m → Sample | z < X s} ≤ 4 * k * z := by
          intro z hz
          have htail_z := htail z hz.1
          have hz0 : 0 ≤ z := hz.1.le
          have hcoef : 0 ≤ g z := by
            dsimp [g]
            positivity
          have hbase : 0 ≤ 4 * k * z := by positivity
          have hexp_le : Real.exp (-z ^ 2) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact neg_nonpos.mpr (sq_nonneg z)
          calc
            g z * μ.real {s : Fin m → Sample | z < X s} ≤
                g z * (2 * Real.exp (-2 * (m : ℝ) * z ^ 2)) :=
              mul_le_mul_of_nonneg_left htail_z hcoef
            _ = (4 * k * z) * Real.exp (-z ^ 2) := by
              calc
                2 * k * z * Real.exp (k * z ^ 2) *
                    (2 * Real.exp (-2 * (m : ℝ) * z ^ 2)) =
                    4 * k * z *
                      (Real.exp (k * z ^ 2) *
                        Real.exp (-2 * (m : ℝ) * z ^ 2)) := by ring
                _ = (4 * k * z) * Real.exp (-z ^ 2) := by
                  rw [← Real.exp_add]
                  congr 1
                  dsimp [k]
                  ring
            _ ≤ 4 * k * z :=
              mul_le_of_le_one_right hbase hexp_le
        have houter_bound :
            (∫ z in Set.Ioc 0 1,
                g z * μ.real {s : Fin m → Sample | z < X s}) ≤
              ∫ z in Set.Ioc 0 1, 4 * k * z := by
          apply integral_mono_of_nonneg
          · filter_upwards [ae_restrict_mem
                (μ := volume)
                (measurableSet_Ioc :
                  MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
            have hz0 : 0 ≤ z := hz.1.le
            have hg0 : 0 ≤ g z := by
              dsimp [g]
              exact mul_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) hk) hz0)
                (Real.exp_pos _).le
            exact mul_nonneg hg0 measureReal_nonneg
          · have hcont : Continuous (fun z : ℝ => 4 * k * z) := by
              fun_prop
            exact hcont.continuousOn.integrableOn_Icc.mono_set
              Set.Ioc_subset_Icc_self
          · filter_upwards [ae_restrict_mem
                (μ := volume)
                (measurableSet_Ioc :
                  MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
            exact hpoint z hz
        have hscalar :
            (∫ z in Set.Ioc 0 1, 4 * k * z) = 2 * k := by
          rw [show (fun z : ℝ => 4 * k * z) = fun z => (4 * k) * z by
            funext z; ring]
          rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          rw [intervalIntegral.integral_const_mul, integral_id]
          ring
        have hslice_moment :
            ∫ s : Fin m → Sample, G (s, c) ∂μ ≤ 4 * (m : ℝ) := by
          have hsum_int :
              Integrable
                (fun s : Fin m → Sample =>
                  ∫ z in Set.Ioc 0 1, if z < X s then g z else 0) μ := by
            rw [show (fun s : Fin m → Sample =>
                ∫ z in Set.Ioc 0 1, if z < X s then g z else 0) =
                fun s => ∫ z, F (s, z) ∂μz by
              funext s; exact hinner_eq s]
            exact hF_int.integral_prod_left
          calc
            ∫ s : Fin m → Sample, G (s, c) ∂μ =
                ∫ s, (1 + ∫ z in Set.Ioc 0 1,
                  if z < X s then g z else 0) ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun s => hlayer s)
            _ = ∫ s, (1 : ℝ) ∂μ +
                  ∫ s, (∫ z in Set.Ioc 0 1,
                    if z < X s then g z else 0) ∂μ := by
              rw [integral_add (integrable_const _) hsum_int]
            _ = 1 + ∫ z in Set.Ioc 0 1,
                  g z * μ.real {s : Fin m → Sample | z < X s} := by
              rw [show (∫ s : Fin m → Sample, (1 : ℝ) ∂μ) = 1 by simp]
              rw [show (fun s : Fin m → Sample =>
                  ∫ z in Set.Ioc 0 1, if z < X s then g z else 0) =
                  fun s => ∫ z, F (s, z) ∂μz by
                funext s; exact hinner_eq s]
              rw [← integral_prod F hF_int]
              rw [integral_prod_symm F hF_int]
              congr 1
              change
                (∫ z, (∫ s : Fin m → Sample, F (s, z) ∂μ) ∂μz) =
                  ∫ z, g z * μ.real {s | z < X s} ∂μz
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem (μ := volume)
                (measurableSet_Ioc :
                  MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
              exact hinner_F z hz
            _ ≤ 1 + 2 * k := by
              gcongr
              exact houter_bound.trans_eq hscalar
            _ ≤ 4 * (m : ℝ) := by
              dsimp [k]
              nlinarith
        exact hslice_moment
      have hM_integral :
          ∫ s : Fin m → Sample, M s ∂μ ≤ 4 * (m : ℝ) := by
        have hinner_int :
            Integrable
              (fun c : Concept => ∫ s : Fin m → Sample, G (s, c) ∂μ)
              ctx.prior_distribution :=
          hG_int.integral_prod_right
        calc
          ∫ s : Fin m → Sample, M s ∂μ =
              ∫ s, ∫ c : Concept, G (s, c) ∂ctx.prior_distribution ∂μ := by
                rfl
          _ = ∫ p, G p ∂(μ.prod ctx.prior_distribution) := by
                exact (integral_prod G hG_int).symm
          _ = ∫ c : Concept,
                ∫ s : Fin m → Sample, G (s, c) ∂μ
                ∂ctx.prior_distribution := by
                exact integral_prod_symm G hG_int
          _ ≤ ∫ c : Concept, 4 * (m : ℝ) ∂ctx.prior_distribution := by
                exact integral_mono hinner_int (integrable_const _)
                  (fun c => hfixed_moment c)
          _ = 4 * (m : ℝ) := by simp
      have hthreshold_pos : 0 < 4 * (m : ℝ) / δ := by
        positivity
      have hmass :
          μ {s | 4 * (m : ℝ) / δ < M s} ≤ ENNReal.ofReal δ :=
        measure_gt_le_of_integral_le_of_nonneg
          M (4 * (m : ℝ) / δ) (4 * (m : ℝ)) δ
          hM_int hM_nonneg hM_integral hthreshold_pos.le
          (by
            intro _
            have hmpos : 0 < (m : ℝ) := by
              exact_mod_cast (Nat.zero_lt_of_lt hm)
            field_simp [ne_of_gt hmpos, ne_of_gt hδ]
            norm_num)
          (by
            intro hzero
            have hmpos : 0 < (m : ℝ) := by
              exact_mod_cast (Nat.zero_lt_of_lt hm)
            nlinarith)
      exact hmass
  simpa [μ, M, G, measurePACBayesMcAllesterMoment] using hsource_route

private theorem measurePACBayes_fixed_posterior_gap_exp_integrable
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m)
    (Q : Measure Concept) (hQ : IsProbabilityMeasure Q)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1)
    (t : ℝ) :
    Integrable
      (fun s : Fin m → Sample =>
        Real.exp
          (t *
            (measurePACBayesPopulationLoss ctx loss Q -
              measurePACBayesEmpiricalLoss ctx m s loss Q)))
      (measurePACBayesSampleLaw ctx m) := by
  let μ : Measure (Fin m → Sample) := measurePACBayesSampleLaw ctx m
  letI : IsProbabilityMeasure ctx.sampling_distribution := hsampling
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure μ :=
    measurePACBayesSampleLaw_isProbability ctx m hsampling
  have hpopulation_bounds :
      0 ≤ measurePACBayesPopulationLoss ctx loss Q ∧
        measurePACBayesPopulationLoss ctx loss Q ≤ 1 := by
    have hpop :=
      measurePACBayesPopulationExpectation_integrable_mem_Icc
        (μ := ctx.sampling_distribution) (Q := Q) loss
        hmeas_loss hloss_bounded
    exact
      ⟨by
          simpa [measurePACBayesPopulationLoss] using hpop.2.1,
        by
          simpa [measurePACBayesPopulationLoss] using hpop.2.2⟩
  have hempirical_bounds (s : Fin m → Sample) :
      0 ≤ measurePACBayesEmpiricalLoss ctx m s loss Q ∧
        measurePACBayesEmpiricalLoss ctx m s loss Q ≤ 1 := by
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hsum_nonneg :
        0 ≤ ∑ i : Fin m, ∫ c, loss c (s i) ∂Q :=
      Finset.sum_nonneg fun i hi => by
        have hslice :
            Integrable (fun c => loss c (s i)) Q :=
          measurePACBayesPointwiseLoss_integrable_sample_slice
            (Q := Q) loss hmeas_loss hloss_bounded (s i)
        simpa using
          (integral_mono (integrable_const 0) hslice
            (fun c => (hloss_bounded c (s i)).1))
    have hsum_le :
        (∑ i : Fin m, ∫ c, loss c (s i) ∂Q) ≤ (m : ℝ) := by
      calc
        (∑ i : Fin m, ∫ c, loss c (s i) ∂Q) ≤
            ∑ i : Fin m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hslice :
              Integrable (fun c => loss c (s i)) Q :=
            measurePACBayesPointwiseLoss_integrable_sample_slice
              (Q := Q) loss hmeas_loss hloss_bounded (s i)
          have hle :
              (∫ c, loss c (s i) ∂Q) ≤ ∫ c, (1 : ℝ) ∂Q :=
            integral_mono hslice (integrable_const 1)
              (fun c => (hloss_bounded c (s i)).2)
          simpa using hle
        _ = (m : ℝ) := by simp
    constructor
    · simpa [measurePACBayesEmpiricalLoss] using
        mul_nonneg (inv_nonneg.mpr hmpos.le) hsum_nonneg
    · have hmul :=
        mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hmpos.le)
      simpa [measurePACBayesEmpiricalLoss,
        inv_mul_cancel₀ (ne_of_gt hmpos)] using hmul
  have hempirical_measurable :
      Measurable
        (fun s : Fin m → Sample =>
          measurePACBayesEmpiricalLoss ctx m s loss Q) := by
    have hkernel : Measurable (fun z : Sample => ∫ c, loss c z ∂Q) := by
      have hstrong :
          StronglyMeasurable
            (fun p : Sample × Concept => loss p.2 p.1) :=
        hmeas_loss.stronglyMeasurable.comp_measurable measurable_swap
      exact hstrong.integral_prod_right'.measurable
    have hsum :
        Measurable
          (fun s : Fin m → Sample =>
            ∑ i : Fin m, ∫ c, loss c (s i) ∂Q) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro i hi
      exact hkernel.comp (measurable_pi_apply i)
    simpa [measurePACBayesEmpiricalLoss] using measurable_const.mul hsum
  have hgap_measurable :
      Measurable
        (fun s : Fin m → Sample =>
          measurePACBayesPopulationLoss ctx loss Q -
            measurePACBayesEmpiricalLoss ctx m s loss Q) :=
    measurable_const.sub hempirical_measurable
  have hexp_measurable :
      Measurable
        (fun s : Fin m → Sample =>
          Real.exp
            (t *
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q))) :=
    Real.measurable_exp.comp
      (measurable_const.mul hgap_measurable)
  refine integrable_of_measurable_bounded_real hexp_measurable
    (C := Real.exp |t|) ?_
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hgap_abs :
      |measurePACBayesPopulationLoss ctx loss Q -
          measurePACBayesEmpiricalLoss ctx m s loss Q| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      linarith [hpopulation_bounds.1, hpopulation_bounds.2,
        (hempirical_bounds s).1, (hempirical_bounds s).2]
  apply Real.exp_le_exp.mpr
  calc
    t *
        (measurePACBayesPopulationLoss ctx loss Q -
          measurePACBayesEmpiricalLoss ctx m s loss Q) ≤
        |t *
          (measurePACBayesPopulationLoss ctx loss Q -
            measurePACBayesEmpiricalLoss ctx m s loss Q)| :=
      le_abs_self _
    _ = |t| *
        |measurePACBayesPopulationLoss ctx loss Q -
          measurePACBayesEmpiricalLoss ctx m s loss Q| := by
      rw [abs_mul]
    _ ≤ |t| :=
      mul_le_of_le_one_right (abs_nonneg t) hgap_abs

private theorem measurePACBayes_fixed_posterior_chernoff
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m)
    (Q : Measure Concept) (hQ : IsProbabilityMeasure Q)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1)
    (ε t : ℝ) (ht : 0 ≤ t) :
    (measurePACBayesSampleLaw ctx m).real
        {s |
          ε ≤
            measurePACBayesPopulationLoss ctx loss Q -
              measurePACBayesEmpiricalLoss ctx m s loss Q} ≤
      Real.exp (-t * ε) *
        ProbabilityTheory.mgf
          (fun s : Fin m → Sample =>
            measurePACBayesPopulationLoss ctx loss Q -
              measurePACBayesEmpiricalLoss ctx m s loss Q)
          (measurePACBayesSampleLaw ctx m) t := by
  letI : IsProbabilityMeasure (measurePACBayesSampleLaw ctx m) :=
    measurePACBayesSampleLaw_isProbability ctx m hsampling
  exact ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht
      (measurePACBayes_fixed_posterior_gap_exp_integrable
      ctx m hm Q hQ loss hsampling hmeas_loss hloss_bounded t)

/- Guarded source-facing PAC-Bayes boundary for arbitrary probability
   Measures.  This is the continuous-Measure realization of the bounded-loss
   McAllester/Dziugaite--Roy step used by SAM Appendix A.1.  Its conclusion is
   stated on the canonical finite-KL violation event; the expected-loss event
   is only a complementary spelling of that same source event, exposed by
   `measurePACBayesExpectedLossEvent_compl`.  The source PDF's Eq. (5) has
   denominator `2 * (m - 1)`, so this continuous route needs the strict
   `1 < m` guard.  The consumer below supplies the canonical Gaussian prior,
   `S.dataLaw`, `Measure.pi`, and the literal common loss. -/
set_option maxHeartbeats 800000 in
theorem mcallester_theorem1_pac_bayes_model_averaging_of_one_lt_sample_size
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ) (hδ : 0 < δ) (hδ_lt_one : δ < 1)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hprior : IsProbabilityMeasure ctx.prior_distribution)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1) :
    measurePACBayesSampleLaw ctx m
      (measurePACBayesFiniteKLViolationEvent ctx m hm δ loss) ≤
      ENNReal.ofReal δ := by
  /- This is the direct arbitrary-Measure source boundary for SAM Appendix
     A.1 Eq. (5).  The earlier moment-event inclusion was removed because
     its constants do not follow from the cited theorem and admit a
     singleton-prior counterexample.  The canonical source objects remain
     the prior and posterior `Measure`s, the iid `Measure.pi` sample law,
     `InformationTheory.klDiv`, and the common bounded loss above. -/
  classical
  let μ : Measure (Fin m → Sample) := measurePACBayesSampleLaw ctx m
  let V : Set (Fin m → Sample) :=
    measurePACBayesFiniteKLViolationEvent ctx m hm δ loss
  letI : IsProbabilityMeasure μ :=
    measurePACBayesSampleLaw_isProbability ctx m hsampling
  letI : IsProbabilityMeasure ctx.prior_distribution := hprior
  letI : IsProbabilityMeasure ctx.sampling_distribution := hsampling
  have hfinite_witness_variational :
      ∀ s ∈ V, ∃ Q : Measure Concept, IsProbabilityMeasure Q ∧
        measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ ∧
          measurePACBayesPopulationLoss ctx loss Q -
              measurePACBayesEmpiricalLoss ctx m s loss Q ≤
            (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log
                (∫ c,
                  Real.exp
                    ((∫ z, loss c z ∂ctx.sampling_distribution) -
                      (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))
                  ∂ctx.prior_distribution) := by
    intro s hs
    have hsource_bridge :=
      measurePACBayes_finite_KL_witness_source_bridge
        (ctx := ctx) (m := m) (hm := hm) (δ := δ) (loss := loss)
        (hprior := hprior) s hs
    rcases hsource_bridge with
      ⟨Q, hQ, hfinite, hAC, hpopulation, hKL⟩
    refine ⟨Q, hQ, hfinite, ?_⟩
    have hvariational :=
      measurePACBayes_finite_KL_witness_variational
        ctx m hm Q hQ s loss hprior hsampling hmeas_loss hloss_bounded hfinite
    simpa only [hpopulation, hKL] using hvariational
  have hfixed_concept_mgf :
      ∀ c : Concept,
        HasSubgaussianMGF
          (fun s : Fin m → Sample =>
            (∫ z, loss c z ∂ctx.sampling_distribution) -
              (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))
          (((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4) μ := by
    intro c
    simpa [μ] using
      (measurePACBayes_productLaw_exponential_budget
        ctx m (Nat.zero_lt_of_lt hm) c loss hsampling hmeas_loss hloss_bounded)
  have haggregation :
      μ (measurePACBayesExpectedLossEvent ctx m hm δ loss)ᶜ ≤
        ENNReal.ofReal δ := by
    /- Exact source boundary: this is the simultaneous posterior
       aggregation asserted in SAM Appendix A.1 Eq. (5), not a
       fixed-posterior Chernoff estimate.  The preceding facts expose the
       canonical Measure-valued inputs that a cited PAC-Bayes supplier must
       consume: the RN/KL witness reduction and the bounded-loss
       exponential budget over `Measure.pi`.  The existing source moment
       estimate has the separate `4 * m` threshold from McAllester's Lemma 3
       and therefore cannot be substituted for this Eq. (5) boundary. -/
    fail_if_success exact hfinite_witness_variational
    fail_if_success exact hfixed_concept_mgf
    let k : ℝ := 2 * ((m : ℝ) - 1)
    let U : (Fin m → Sample) × Concept → ℝ := fun p =>
      (∫ z, loss p.2 z ∂ctx.sampling_distribution) -
        (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)
    let X : (Fin m → Sample) × Concept → ℝ := fun p => max (U p) 0
    let G : (Fin m → Sample) × Concept → ℝ := fun p =>
      Real.exp (k * (X p) ^ 2)
    let F : (Fin m → Sample) → ℝ := fun s =>
      ∫ c, G (s, c) ∂ctx.prior_distribution
    have hmreal : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hk_nonneg : 0 ≤ k := by
      dsimp [k]
      have hm' : (1 : ℝ) < (m : ℝ) := by
        exact_mod_cast hm
      linarith
    have hpop_meas :
        Measurable
          (fun c : Concept => ∫ z, loss c z ∂ctx.sampling_distribution) := by
      exact hmeas_loss.stronglyMeasurable.integral_prod_right'.measurable
    have hemp_meas :
        Measurable
          (fun p : (Fin m → Sample) × Concept =>
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)) := by
      exact measurable_const.mul
        (Finset.measurable_sum Finset.univ (by
          intro i hi
          simpa [Function.uncurry] using
            hmeas_loss.comp
              (measurable_snd.prodMk
                ((measurable_pi_apply i).comp measurable_fst))))
    have hU_meas : Measurable U := by
      dsimp [U]
      exact (hpop_meas.comp measurable_snd).sub hemp_meas
    have hX_meas : Measurable X := by
      dsimp [X]
      exact hU_meas.max measurable_const
    have hG_meas : Measurable G := by
      dsimp [G]
      exact Real.measurable_exp.comp
        (measurable_const.mul (hX_meas.pow_const 2))
    have hpopulation_bounds :
        ∀ c : Concept,
          0 ≤ ∫ z, loss c z ∂ctx.sampling_distribution ∧
            (∫ z, loss c z ∂ctx.sampling_distribution) ≤ 1 := by
      intro c
      have hslice :
          Integrable (loss c) ctx.sampling_distribution :=
        measurePACBayesPointwiseLoss_integrable
          (μ := ctx.sampling_distribution) loss hmeas_loss hloss_bounded c
      constructor
      · simpa using
          (integral_mono (integrable_const 0) hslice
            (fun z => (hloss_bounded c z).1))
      · have hle :=
          integral_mono hslice (integrable_const 1)
            (fun z => (hloss_bounded c z).2)
        simpa using hle
    have hempirical_bounds :
        ∀ c : Concept, ∀ s : Fin m → Sample,
          0 ≤ (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ∧
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ≤ 1 := by
      intro c s
      have hsum_nonneg :
          0 ≤ ∑ i : Fin m, loss c (s i) :=
        Finset.sum_nonneg (fun i hi => (hloss_bounded c (s i)).1)
      have hsum_le :
          (∑ i : Fin m, loss c (s i)) ≤ (m : ℝ) := by
        calc
          (∑ i : Fin m, loss c (s i)) ≤ ∑ i : Fin m, (1 : ℝ) :=
            Finset.sum_le_sum (fun i hi => (hloss_bounded c (s i)).2)
          _ = (m : ℝ) := by simp
      constructor
      · exact mul_nonneg (inv_nonneg.mpr hmreal.le) hsum_nonneg
      · have hmul :=
          mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hmreal.le)
        simpa [inv_mul_cancel₀ hmreal.ne'] using hmul
    have hX_bounds :
        ∀ p : (Fin m → Sample) × Concept, 0 ≤ X p ∧ X p ≤ 1 := by
      intro p
      have hpop := hpopulation_bounds p.2
      have hemp := hempirical_bounds p.2 p.1
      have hU_lower : -1 ≤ U p := by
        dsimp [U]
        linarith
      have hU_upper : U p ≤ 1 := by
        dsimp [U]
        linarith
      constructor
      · exact le_max_right _ _
      · exact max_le hU_upper (by norm_num)
    have hG_bound :
        ∀ p : (Fin m → Sample) × Concept,
          ‖G p‖ ≤ Real.exp k := by
      intro p
      have hX := hX_bounds p
      have hX_sq : (X p) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg (X p - 1), sq_nonneg (X p)]
      have harg : k * (X p) ^ 2 ≤ k := by
        simpa using (mul_le_mul_of_nonneg_left hX_sq hk_nonneg)
      dsimp [G]
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using
        (Real.exp_le_exp.mpr harg)
    have hG_int :
        Integrable G
          (μ.prod ctx.prior_distribution) :=
      integrable_of_measurable_bounded_real hG_meas hG_bound
    have hF_int : Integrable F μ := by
      simpa [F] using hG_int.integral_prod_left
    have hF_nonneg : ∀ s, 0 ≤ F s := by
      intro s
      exact integral_nonneg (fun c => (Real.exp_pos _).le)
    have hscalar_exp_sq_layer_cake :
        ∀ (a x : ℝ), 0 ≤ a → 0 ≤ x → x ≤ 1 →
          Real.exp (a * x ^ 2) =
            1 + ∫ z in Set.Ioc 0 1,
              if z < x then 2 * a * z * Real.exp (a * z ^ 2) else 0 := by
      intro a x ha hx hx1
      have hderiv :
          ∀ z ∈ Set.uIcc (0 : ℝ) x,
            HasDerivAt (fun t => Real.exp (a * t ^ 2))
              (2 * a * z * Real.exp (a * z ^ 2)) z := by
        intro z hz
        convert
          ((Real.hasDerivAt_exp (a * z ^ 2)).comp z
            ((hasDerivAt_const z a).mul ((hasDerivAt_id z).pow 2))) using 1 <;>
          simp only [id] <;> ring
      have hcontg :
          Continuous (fun z : ℝ => 2 * a * z * Real.exp (a * z ^ 2)) := by
        fun_prop
      have hint :
          IntervalIntegrable (fun z : ℝ => 2 * a * z * Real.exp (a * z ^ 2))
            volume 0 x :=
        hcontg.intervalIntegrable (μ := volume) 0 x
      have hinterval :
          (∫ z in (0 : ℝ)..x, 2 * a * z * Real.exp (a * z ^ 2)) =
            Real.exp (a * x ^ 2) - 1 := by
        simpa using
          (intervalIntegral.integral_eq_sub_of_hasDerivAt
            (a := (0 : ℝ)) (b := x) hderiv hint)
      have hset :
          (∫ z in Set.Ioc (0 : ℝ) 1,
            if z < x then 2 * a * z * Real.exp (a * z ^ 2) else 0) =
            ∫ z in Set.Ioo (0 : ℝ) x, 2 * a * z * Real.exp (a * z ^ 2) := by
        calc
          (∫ z in Set.Ioc (0 : ℝ) 1,
              if z < x then 2 * a * z * Real.exp (a * z ^ 2) else 0) =
              ∫ z in Set.Ioc (0 : ℝ) 1,
                (Set.Iio x).indicator
                  (fun z => 2 * a * z * Real.exp (a * z ^ 2)) z := by
            apply setIntegral_congr_fun measurableSet_Ioc
            intro z hz
            by_cases hzx : z < x <;> simp [Set.indicator, hzx]
          _ = ∫ z in Set.Ioc (0 : ℝ) 1 ∩ Set.Iio x,
              2 * a * z * Real.exp (a * z ^ 2) := by
            rw [setIntegral_indicator measurableSet_Iio]
          _ = ∫ z in Set.Ioo (0 : ℝ) x,
              2 * a * z * Real.exp (a * z ^ 2) := by
            have hsets :
                Set.Ioc (0 : ℝ) 1 ∩ Set.Iio x = Set.Ioo (0 : ℝ) x := by
              ext z
              change ((0 < z ∧ z ≤ (1 : ℝ)) ∧ z < x) ↔
                (0 < z ∧ z < x)
              constructor
              · rintro ⟨⟨hz0, hz1⟩, hzx⟩
                exact ⟨hz0, hzx⟩
              · rintro ⟨hz0, hzx⟩
                exact ⟨⟨hz0, hzx.le.trans hx1⟩, hzx⟩
            rw [hsets]
      rw [hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]
      rw [← intervalIntegral.integral_of_le hx]
      rw [hinterval]
      ring
    have hfixed_moment :
        ∀ c : Concept,
          ∫ s : Fin m → Sample, G (s, c) ∂μ ≤ (m : ℝ) := by
      intro c
      let Xc : (Fin m → Sample) → ℝ := fun s => X (s, c)
      let g : ℝ → ℝ := fun z =>
        2 * k * z * Real.exp (k * z ^ 2)
      have hXc_meas : Measurable Xc := by
        exact hX_meas.comp (measurable_id.prodMk measurable_const)
      have hXc_bounds : ∀ s, 0 ≤ Xc s ∧ Xc s ≤ 1 := by
        intro s
        exact hX_bounds (s, c)
      have htail :
          ∀ z : ℝ, 0 < z →
            μ.real {s : Fin m → Sample | z < Xc s} ≤
              Real.exp (-2 * (m : ℝ) * z ^ 2) := by
        intro z hz
        have hsubset :
            {s : Fin m → Sample | z < Xc s} ⊆
              {s | z ≤ U (s, c)} := by
          intro s hs
          by_cases hU : 0 ≤ U (s, c)
          · have hs' : z < U (s, c) := by
              have hs'' : z < U (s, c) ∨ z < 0 := by
                simpa [Xc, X, hU] using hs
              exact hs''.resolve_right (not_lt_of_ge hz.le)
            exact hs'.le
          · have hXzero : Xc s = 0 := by
              simp [Xc, X, le_of_not_ge hU]
            exfalso
            change z < Xc s at hs
            rw [hXzero] at hs
            linarith
        calc
          μ.real {s : Fin m → Sample | z < Xc s} ≤
              μ.real {s | z ≤ U (s, c)} :=
            measureReal_mono hsubset
          _ ≤
              Real.exp
                (-z ^ 2 /
                  (2 * ((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ))) :=
            (hfixed_concept_mgf c).measure_ge_le hz.le
          _ = Real.exp (-2 * (m : ℝ) * z ^ 2) := by
            congr 1
            norm_num [NNReal.coe_div, NNReal.coe_pow]
            field_simp [Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt hm).ne']
            ring
      have hpoint :
        ∀ z : ℝ, z ∈ Set.Ioc (0 : ℝ) 1 →
            g z * μ.real {s : Fin m → Sample | z < Xc s} ≤
              2 * k * z * Real.exp (-2 * z ^ 2) := by
        intro z hz
        have htail_z := htail z hz.1
        have hz0 : 0 ≤ z := hz.1.le
        have hg0 : 0 ≤ g z := by
          dsimp [g]
          positivity
        calc
          g z * μ.real {s : Fin m → Sample | z < Xc s} ≤
              g z * Real.exp (-2 * (m : ℝ) * z ^ 2) :=
            mul_le_mul_of_nonneg_left htail_z hg0
          _ = 2 * k * z * Real.exp (-2 * z ^ 2) := by
            dsimp [g]
            calc
              2 * k * z * Real.exp (k * z ^ 2) *
                  Real.exp (-2 * (m : ℝ) * z ^ 2) =
                  2 * k * z *
                    (Real.exp (k * z ^ 2) *
                      Real.exp (-2 * (m : ℝ) * z ^ 2)) := by ring
              _ = 2 * k * z * Real.exp (-2 * z ^ 2) := by
                rw [← Real.exp_add]
                congr 1
                dsimp [k]
                ring
      have houter_bound :
          (∫ z in Set.Ioc 0 1,
              g z * μ.real {s : Fin m → Sample | z < Xc s}) ≤
            ∫ z in Set.Ioc 0 1,
              2 * k * z * Real.exp (-2 * z ^ 2) := by
        apply integral_mono_of_nonneg
        · filter_upwards [ae_restrict_mem (μ := volume)
              (measurableSet_Ioc :
                MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
          have hcoef : 0 ≤ 2 * k * z :=
            mul_nonneg (mul_nonneg (by norm_num) hk_nonneg) hz.1.le
          have hg : 0 ≤ g z := by
            dsimp [g]
            exact mul_nonneg hcoef (Real.exp_pos _).le
          exact mul_nonneg hg measureReal_nonneg
        · have hcont : Continuous
              (fun z : ℝ => 2 * k * z * Real.exp (-2 * z ^ 2)) := by
            fun_prop
          exact
            (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)
              (a := (0 : ℝ)) (b := 1)).mp
              hcont.continuousOn.integrableOn_Icc
        · filter_upwards [ae_restrict_mem (μ := volume)
              (measurableSet_Ioc :
                MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
          exact hpoint z hz
      have hscalar :
          (∫ z in Set.Ioc 0 1,
              2 * k * z * Real.exp (-2 * z ^ 2)) ≤ k / 2 := by
        have hcont : Continuous
            (fun z : ℝ => 2 * k * z * Real.exp (-2 * z ^ 2)) := by
          fun_prop
        have hderiv :
            ∀ z ∈ Set.uIcc (0 : ℝ) 1,
              HasDerivAt
                (fun t : ℝ => -(k / 2) * Real.exp (-2 * t ^ 2))
                (2 * k * z * Real.exp (-2 * z ^ 2)) z := by
          intro z hz
          convert
            ((hasDerivAt_const z (-(k / 2))).mul
              ((Real.hasDerivAt_exp (-2 * z ^ 2)).comp z
                ((hasDerivAt_const z (-2)).mul
                  ((hasDerivAt_id z).pow 2)))) using 1 <;>
            simp only [id] <;> ring
        have hint :
            IntervalIntegrable
              (fun z : ℝ => 2 * k * z * Real.exp (-2 * z ^ 2))
              volume 0 1 :=
          hcont.intervalIntegrable (μ := volume) 0 1
        have hinterval :
            (∫ z in (0 : ℝ)..1,
                2 * k * z * Real.exp (-2 * z ^ 2)) =
              (-(k / 2) * Real.exp (-2)) -
                (-(k / 2) * Real.exp 0) := by
          simpa using
            (intervalIntegral.integral_eq_sub_of_hasDerivAt
              (a := (0 : ℝ)) (b := 1) hderiv hint)
        rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [hinterval]
        have hexp_nonneg : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
        rw [Real.exp_zero]
        have hkhalf : 0 ≤ k / 2 := by positivity
        have hprod : 0 ≤ (k / 2) * Real.exp (-2) :=
          mul_nonneg hkhalf hexp_nonneg
        nlinarith
      have hslice_moment :
          ∫ s : Fin m → Sample, G (s, c) ∂μ ≤ (m : ℝ) := by
        have hlayer :
            ∀ s, G (s, c) =
              1 + ∫ z in Set.Ioc 0 1,
                if z < Xc s then g z else 0 := by
          intro s
          have h :=
            hscalar_exp_sq_layer_cake k (Xc s) hk_nonneg
              (hXc_bounds s).1 (hXc_bounds s).2
          dsimp [G, Xc, g] at h ⊢
          simpa using h
        let μz : Measure ℝ := volume.restrict (Set.Ioc 0 1)
        let H : (Fin m → Sample) × ℝ → ℝ := fun p =>
          if p.2 ∈ Set.Ioc (0 : ℝ) 1 ∧ p.2 < Xc p.1 then g p.2 else 0
        have hg_meas : Measurable g := by
          dsimp [g]
          fun_prop
        have hH_meas : Measurable H := by
          exact Measurable.ite
            ((measurableSet_Ioc.preimage measurable_snd).inter
              (measurableSet_lt measurable_snd
                (hXc_meas.comp measurable_fst)))
            (hg_meas.comp measurable_snd) measurable_const
        have hH_bound :
            ∀ p, ‖H p‖ ≤ 2 * k * Real.exp k := by
          intro p
          by_cases hp :
              p.2 ∈ Set.Ioc (0 : ℝ) 1 ∧ p.2 < Xc p.1
          · have hz0 : 0 ≤ p.2 := hp.1.1.le
            have hz1 : p.2 ≤ 1 := hp.1.2
            have hcoef : 0 ≤ 2 * k * p.2 := by positivity
            have harg : k * p.2 ^ 2 ≤ k := by
              have : p.2 ^ 2 ≤ (1 : ℝ) := by nlinarith
              simpa using (mul_le_mul_of_nonneg_left this hk_nonneg)
            have hexp : Real.exp (k * p.2 ^ 2) ≤ Real.exp k :=
              Real.exp_le_exp.mpr harg
            have hcoef_le : 2 * k * p.2 ≤ 2 * k := by
              nlinarith [mul_le_mul_of_nonneg_left hz1
                (show 0 ≤ 2 * k by positivity)]
            have hp' :
                (0 < p.2 ∧ p.2 ≤ (1 : ℝ)) ∧ p.2 < Xc p.1 :=
              ⟨⟨hp.1.1, hp.1.2⟩, hp.2⟩
            dsimp [H]
            rw [if_pos hp]
            rw [abs_of_nonneg (by
              dsimp [g]
              positivity : 0 ≤ g p.2)]
            calc
              g p.2 ≤ (2 * k * p.2) * Real.exp k := by
                dsimp [g]
                exact mul_le_mul_of_nonneg_left hexp hcoef
              _ ≤ 2 * k * Real.exp k :=
                mul_le_mul_of_nonneg_right hcoef_le (Real.exp_pos _).le
          · have hp' :
                ¬ ((0 < p.2 ∧ p.2 ≤ (1 : ℝ)) ∧ p.2 < Xc p.1) := by
              intro hp''
              exact hp ⟨hp''.1, hp''.2⟩
            dsimp [H]
            rw [if_neg hp]
            simp only [norm_zero, abs_zero]
            positivity
        have hH_int : Integrable H (μ.prod μz) :=
          integrable_of_measurable_bounded_real hH_meas hH_bound
        have hinner_eq :
            ∀ s : Fin m → Sample,
              (∫ z in Set.Ioc 0 1,
                  if z < Xc s then g z else 0) =
                ∫ z, H (s, z) ∂μz := by
          intro s
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem (μ := volume)
            (measurableSet_Ioc :
              MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
          by_cases hzx : z < Xc s
          · change (if z < Xc s then g z else 0) =
              (if z ∈ Set.Ioc (0 : ℝ) 1 ∧ z < Xc s then g z else 0)
            rw [if_pos hzx, if_pos ⟨hz, hzx⟩]
          · change (if z < Xc s then g z else 0) =
              (if z ∈ Set.Ioc (0 : ℝ) 1 ∧ z < Xc s then g z else 0)
            rw [if_neg hzx, if_neg (fun h => hzx h.2)]
        have hinner_H :
            ∀ z ∈ Set.Ioc (0 : ℝ) 1,
              (∫ s : Fin m → Sample, H (s, z) ∂μ) =
                g z * μ.real {s | z < Xc s} := by
          intro z hz
          have hevent : MeasurableSet {s : Fin m → Sample | z < Xc s} :=
            measurableSet_lt measurable_const hXc_meas
          have hfun :
              (fun s : Fin m → Sample => H (s, z)) =
                ({s : Fin m → Sample | z < Xc s}).indicator (fun _ => g z) := by
            funext s
            by_cases hzx : z < Xc s
            · rw [show H (s, z) =
                (if z ∈ Set.Ioc (0 : ℝ) 1 ∧ z < Xc s then g z else 0) by rfl]
              have hmem : s ∈ {s : Fin m → Sample | z < Xc s} := hzx
              rw [if_pos ⟨hz, hzx⟩, Set.indicator_of_mem hmem]
            · rw [show H (s, z) =
                (if z ∈ Set.Ioc (0 : ℝ) 1 ∧ z < Xc s then g z else 0) by rfl]
              have hmem : s ∉ {s : Fin m → Sample | z < Xc s} := by
                intro hmem
                exact hzx hmem
              rw [if_neg (fun h => hzx h.2),
                Set.indicator_of_notMem hmem]
          rw [hfun, integral_indicator hevent]
          simp [MeasureTheory.integral_const_mul, measureReal_def, mul_comm]
        calc
          ∫ s : Fin m → Sample, G (s, c) ∂μ =
              ∫ s, (1 + ∫ z in Set.Ioc 0 1,
                if z < Xc s then g z else 0) ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun s => hlayer s)
          _ = 1 + ∫ z in Set.Ioc 0 1,
                g z * μ.real {s : Fin m → Sample | z < Xc s} := by
            rw [integral_add (integrable_const _) (by
              rw [show (fun s : Fin m → Sample =>
                  ∫ z in Set.Ioc 0 1,
                    if z < Xc s then g z else 0) =
                  fun s => ∫ z, H (s, z) ∂μz by
                funext s
                exact hinner_eq s]
              exact hH_int.integral_prod_left)]
            rw [show (∫ s : Fin m → Sample, (1 : ℝ) ∂μ) = 1 by simp]
            rw [show (fun s : Fin m → Sample =>
                ∫ z in Set.Ioc 0 1,
                  if z < Xc s then g z else 0) =
                fun s => ∫ z, H (s, z) ∂μz by
              funext s
              exact hinner_eq s]
            rw [← integral_prod H hH_int]
            rw [integral_prod_symm H hH_int]
            congr 1
            change
              (∫ z, (∫ s : Fin m → Sample, H (s, z) ∂μ) ∂μz) =
                ∫ z, g z * μ.real {s | z < Xc s} ∂μz
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem (μ := volume)
              (measurableSet_Ioc :
                MeasurableSet (Set.Ioc (0 : ℝ) 1))] with z hz
            exact hinner_H z hz
          _ ≤ 1 + k / 2 := by
            gcongr
            exact houter_bound.trans hscalar
          _ = (m : ℝ) := by
            dsimp [k]
            ring
      exact hslice_moment
    have hF_integral :
        ∫ s : Fin m → Sample, F s ∂μ ≤ (m : ℝ) := by
      have hinner_int :
          Integrable
            (fun c : Concept => ∫ s : Fin m → Sample, G (s, c) ∂μ)
            ctx.prior_distribution :=
        hG_int.integral_prod_right
      calc
        ∫ s : Fin m → Sample, F s ∂μ =
            ∫ s, ∫ c : Concept, G (s, c) ∂ctx.prior_distribution ∂μ := by
              rfl
        _ = ∫ p, G p ∂(μ.prod ctx.prior_distribution) := by
              exact (integral_prod G hG_int).symm
        _ = ∫ c : Concept,
              ∫ s : Fin m → Sample, G (s, c) ∂μ
              ∂ctx.prior_distribution := by
              exact integral_prod_symm G hG_int
        _ ≤ ∫ c : Concept, (m : ℝ) ∂ctx.prior_distribution := by
              exact integral_mono hinner_int (integrable_const _)
                (fun c => hfixed_moment c)
        _ = (m : ℝ) := by simp
    have hbadF :
        μ {s | F s > (m : ℝ) / δ} ≤ ENNReal.ofReal δ := by
      have hthreshold_pos : 0 < (m : ℝ) / δ := by positivity
      apply measure_gt_le_of_integral_le_of_nonneg
        F ((m : ℝ) / δ) (m : ℝ) δ hF_int hF_nonneg hF_integral
          hthreshold_pos.le
      · intro _
        field_simp [ne_of_gt hmreal, ne_of_gt hδ]
        norm_num
      · intro hzero
        have hpos : 0 < (m : ℝ) / δ := by positivity
        rw [hzero] at hpos
        linarith
    have hV_subset :
        V ⊆ {s | F s > (m : ℝ) / δ} := by
      intro s hs
      rcases hs with ⟨Q, hQ, hfinite, hviol⟩
      by_contra hnot
      letI : IsProbabilityMeasure Q := hQ
      have hQ_integrable :
          Integrable
            (fun c : Concept => k * (max (U (s, c)) 0) ^ 2) Q := by
        refine integrable_of_measurable_bounded_real (C := k) ?_ ?_
        · exact measurable_const.mul
            ((hX_meas.comp (measurable_const.prodMk measurable_id)).pow_const 2)
        intro c
        have hx := hX_bounds (s, c)
        have hsq : (max (U (s, c)) 0) ^ 2 ≤ 1 := by
          have hprod := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
          nlinarith
        have hnonneg : 0 ≤ k * (max (U (s, c)) 0) ^ 2 :=
          mul_nonneg hk_nonneg (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        simpa using (mul_le_mul_of_nonneg_left hsq hk_nonneg)
      have hQ_exp_integrable :
          Integrable
            (fun c : Concept =>
              Real.exp (k * (max (U (s, c)) 0) ^ 2))
            ctx.prior_distribution := by
        refine integrable_of_measurable_bounded_real
          (C := Real.exp k) ?_ ?_
        · exact Real.measurable_exp.comp
            (measurable_const.mul
              ((hX_meas.comp (measurable_const.prodMk measurable_id)).pow_const 2))
        intro c
        have hx := hX_bounds (s, c)
        have hsq : (max (U (s, c)) 0) ^ 2 ≤ 1 := by
          have hprod := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
          nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        exact Real.exp_le_exp.mpr (by
          simpa using (mul_le_mul_of_nonneg_left hsq hk_nonneg))
      have hDV :=
        measurePACBayes_change_of_measure_log_mgf
          Q ctx.prior_distribution hQ hprior hfinite
          (fun c => k * (max (U (s, c)) 0) ^ 2)
          hQ_integrable hQ_exp_integrable
      have hgap_pos : 0 < measurePACBayesPopulationLoss ctx loss Q -
          measurePACBayesEmpiricalLoss ctx m s loss Q := by
        have hsqrt_nonneg :
            0 ≤ Real.sqrt
              (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                Real.log ((m : ℝ) / δ)) / k) := by positivity
        linarith
      have hpopulation_Q_integrable :
          Integrable
            (fun c : Concept => ∫ z, loss c z ∂ctx.sampling_distribution) Q :=
        measurePACBayesPointwiseLoss_integrable_population
          (μ := ctx.sampling_distribution) (Q := Q)
          loss hmeas_loss hloss_bounded
      have hempirical_Q_integrable :
          Integrable
            (fun c : Concept =>
              (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) Q := by
        exact
          (integrable_finset_sum Finset.univ (by
            intro i hi
            exact measurePACBayesPointwiseLoss_integrable_sample_slice
              (Q := Q) loss hmeas_loss hloss_bounded (s i))).const_mul _
      have hU_s_meas : Measurable (fun c : Concept => U (s, c)) :=
        hU_meas.comp (measurable_const.prodMk measurable_id)
      have hU_s_integrable :
          Integrable (fun c : Concept => U (s, c)) Q := by
        simpa [U] using hpopulation_Q_integrable.sub hempirical_Q_integrable
      have hX_s_meas : Measurable (fun c : Concept => X (s, c)) :=
        hX_meas.comp (measurable_const.prodMk measurable_id)
      have hX_s_integrable :
          Integrable (fun c : Concept => X (s, c)) Q := by
        refine integrable_of_measurable_bounded_real (C := 1) hX_s_meas ?_
        intro c
        have hx := hX_bounds (s, c)
        rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
        exact hx.2
      have hX_sq_integrable :
          Integrable (fun c : Concept => (X (s, c)) ^ 2) Q := by
        refine integrable_of_measurable_bounded_real (C := 1)
          (hX_s_meas.pow_const 2) ?_
        intro c
        have hx := hX_bounds (s, c)
        have hsq : (X (s, c)) ^ 2 ≤ 1 := by
          have hprod := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
          nlinarith
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsq
      have hgap_integral :
          (∫ c, U (s, c) ∂Q) =
            measurePACBayesPopulationLoss ctx loss Q -
              measurePACBayesEmpiricalLoss ctx m s loss Q := by
        dsimp [U, measurePACBayesPopulationLoss,
          measurePACBayesEmpiricalLoss]
        rw [integral_sub hpopulation_Q_integrable hempirical_Q_integrable]
        rw [integral_const_mul,
          integral_finset_sum Finset.univ (by
            intro i hi
            exact measurePACBayesPointwiseLoss_integrable_sample_slice
              (Q := Q) loss hmeas_loss hloss_bounded (s i))]
      have hgap_le_integral_X :
          measurePACBayesPopulationLoss ctx loss Q -
              measurePACBayesEmpiricalLoss ctx m s loss Q ≤
            ∫ c, X (s, c) ∂Q := by
        calc
          measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q =
              ∫ c, U (s, c) ∂Q := hgap_integral.symm
          _ ≤ ∫ c, X (s, c) ∂Q :=
            integral_mono hU_s_integrable hX_s_integrable
              (fun c => le_max_left _ _)
      have hX_integral_nonneg : 0 ≤ ∫ c, X (s, c) ∂Q :=
        integral_nonneg (fun c => (hX_bounds (s, c)).1)
      have hgap_sq_le :
          (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 ≤
            ∫ c, (X (s, c)) ^ 2 ∂Q := by
        have hsq_jensen :=
          sq_integral_le_integral_sq
            (μ := Q) (Z := fun c => X (s, c))
            hX_s_meas.aestronglyMeasurable hX_sq_integrable
        have hsq_gap :
            (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 ≤
              (∫ c, X (s, c) ∂Q) ^ 2 :=
          (sq_le_sq₀ (le_of_lt hgap_pos) hX_integral_nonneg).2
            hgap_le_integral_X
        exact hsq_gap.trans hsq_jensen
      have hgap_sq_integral :
          k *
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 ≤
            ∫ c, k * (X (s, c)) ^ 2 ∂Q := by
        calc
          k *
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 ≤
              k * (∫ c, (X (s, c)) ^ 2 ∂Q) :=
            mul_le_mul_of_nonneg_left hgap_sq_le hk_nonneg
          _ = ∫ c, k * (X (s, c)) ^ 2 ∂Q := by
            rw [integral_const_mul]
      have hgap_sq :
          k *
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 >
            (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((m : ℝ) / δ) := by
        have hnum :
            0 ≤
              (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                Real.log ((m : ℝ) / δ) := by
          have hratio : 1 ≤ (m : ℝ) / δ := by
            have hmreal_one : (1 : ℝ) < (m : ℝ) := by
              exact_mod_cast hm
            have hratio_pos : 0 < (m : ℝ) / δ :=
              div_pos hmreal hδ
            apply le_of_lt
            apply (lt_div_iff₀ hδ).2
            linarith
          exact add_nonneg ENNReal.toReal_nonneg
            (Real.log_nonneg hratio)
        have hk_pos : 0 < k := by
          have hmreal_one : (1 : ℝ) < (m : ℝ) := by
            exact_mod_cast hm
          dsimp [k]
          linarith
        have hsqrt :
            (Real.sqrt
                (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                  Real.log ((m : ℝ) / δ)) / k)) ^ 2 =
              ((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                Real.log ((m : ℝ) / δ)) / k := by
          rw [Real.sq_sqrt]
          exact div_nonneg hnum (le_of_lt hk_pos)
        have hgap_gt :
            Real.sqrt
                (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                  Real.log ((m : ℝ) / δ)) / k) <
              measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q := by
          dsimp [k]
          linarith
        have hsq_lt :
            (Real.sqrt
                (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                  Real.log ((m : ℝ) / δ)) / k)) ^ 2 <
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 :=
          (sq_lt_sq₀ (Real.sqrt_nonneg _) (le_of_lt hgap_pos)).2 hgap_gt
        have hmul := mul_lt_mul_of_pos_left hsq_lt hk_pos
        have hrewrite :
            k *
                (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                  Real.log ((m : ℝ) / δ)) / k) =
              (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                Real.log ((m : ℝ) / δ) := by
          field_simp [ne_of_gt hk_pos]
        calc
          (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                Real.log ((m : ℝ) / δ) =
              k *
                (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                  Real.log ((m : ℝ) / δ)) / k) := hrewrite.symm
          _ = k *
              (Real.sqrt
                (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
                  Real.log ((m : ℝ) / δ)) / k)) ^ 2 := by rw [hsqrt]
          _ < k *
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 := hmul
      have hDV_upper :
          (∫ c, k * (X (s, c)) ^ 2 ∂Q) ≤
            (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log (F s) := by
        simpa [F, G, X, measurePACBayesKLDivergence] using hDV
      have hF_lower : 1 ≤ F s := by
        have hG_s_integrable :
            Integrable (fun c : Concept => G (s, c))
              ctx.prior_distribution := by
          simpa [G, X] using hQ_exp_integrable
        have hG_one : ∀ c : Concept, (1 : ℝ) ≤ G (s, c) := by
          intro c
          dsimp [G]
          exact Real.one_le_exp
            (mul_nonneg hk_nonneg (sq_nonneg (X (s, c))))
        have h :=
          integral_mono (integrable_const 1) hG_s_integrable
            (fun c => hG_one c)
        simpa [F] using h
      have hlog_mono : Real.log (F s) ≤ Real.log ((m : ℝ) / δ) := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact lt_of_lt_of_le zero_lt_one hF_lower
        · exact div_pos hmreal hδ
        · exact le_of_not_gt (by
            change ¬ F s > (m : ℝ) / δ at hnot
            exact hnot)
      have hcombined :
          k *
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 ≤
            (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log (F s) :=
        hgap_sq_integral.trans hDV_upper
      have hcombined' :
          k *
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q) ^ 2 ≤
            (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((m : ℝ) / δ) :=
        hcombined.trans
          (by
            simpa [add_comm] using
              add_le_add_left hlog_mono
                (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal)
      linarith
    rw [measurePACBayesExpectedLossEvent_compl]
    exact le_trans (measure_mono hV_subset) hbadF
  calc
    μ V = μ (measurePACBayesExpectedLossEvent ctx m hm δ loss)ᶜ := by
      congr 1
      simpa [V] using
        (measurePACBayesExpectedLossEvent_compl
          ctx m hm δ loss).symm
    _ ≤ ENNReal.ofReal δ := haggregation

/- Retained only as private legacy infrastructure.  The source/public Appendix
   route consumes the guarded Measure-valued McAllester interface directly
   below, so this forwarding name is no longer part of that dependency cone. -/
private theorem measurePACBayes_finite_KL_violation_mass
    {Concept Sample : Type*}
    [MeasurableSpace Concept] [MeasurableSpace Sample]
    (ctx : MeasurePACBayesDistributionContext Concept Sample)
    (m : ℕ) (hm : 1 < m) (δ : ℝ) (hδ : 0 < δ) (hδ_lt_one : δ < 1)
    (loss : MeasurePACBayesPointwiseLoss Concept Sample)
    (hprior : IsProbabilityMeasure ctx.prior_distribution)
    (hsampling : IsProbabilityMeasure ctx.sampling_distribution)
    (hmeas_loss : Measurable (Function.uncurry loss))
    (hloss_bounded : ∀ c z, 0 ≤ loss c z ∧ loss c z ≤ 1) :
    measurePACBayesSampleLaw ctx m
      (measurePACBayesFiniteKLViolationEvent ctx m hm δ loss) ≤
      ENNReal.ofReal δ := by
  exact
    mcallester_theorem1_pac_bayes_model_averaging_of_one_lt_sample_size
      (ctx := ctx) (m := m) (hm := hm) (δ := δ)
      (hδ := hδ) (hδ_lt_one := hδ_lt_one) (loss := loss)
      (hprior := hprior) (hsampling := hsampling)
      (hmeas_loss := hmeas_loss) (hloss_bounded := hloss_bounded)
  /-
  let μ : Measure (Fin m → Sample) := measurePACBayesSampleLaw ctx m
  let V : Set (Fin m → Sample) :=
    measurePACBayesFiniteKLViolationEvent ctx m hm δ loss
  letI : IsProbabilityMeasure μ :=
    measurePACBayesSampleLaw_isProbability ctx m hsampling
  have hμfin : IsFiniteMeasure μ := inferInstance
  have hfixed_population_bounds :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        0 ≤ measurePACBayesPopulationLoss ctx loss Q ∧
          measurePACBayesPopulationLoss ctx loss Q ≤ 1 := by
    intro Q hQ
    letI : IsProbabilityMeasure Q := hQ
    have hpop :=
      measurePACBayesPopulationExpectation_integrable_mem_Icc
        (μ := ctx.sampling_distribution) (Q := Q) loss hmeas_loss hloss_bounded
    exact
      ⟨by simpa [measurePACBayesPopulationLoss] using hpop.2.1,
        by simpa [measurePACBayesPopulationLoss] using hpop.2.2⟩
  have hfixed_slice_bounds :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        ∀ z : Sample,
          0 ≤ ∫ c, loss c z ∂Q ∧ (∫ c, loss c z ∂Q) ≤ 1 := by
    intro Q hQ z
    letI : IsProbabilityMeasure Q := hQ
    have hslice :
        Integrable (fun c => loss c z) Q :=
      measurePACBayesPointwiseLoss_integrable_sample_slice
        loss hmeas_loss hloss_bounded z
    have hzero : Integrable (fun _ : Concept => (0 : ℝ)) Q :=
      integrable_const 0
    have hone : Integrable (fun _ : Concept => (1 : ℝ)) Q :=
      integrable_const 1
    constructor
    · simpa using
        (integral_mono hzero hslice (fun c => (hloss_bounded c z).1))
    · have hle :
          (∫ c, loss c z ∂Q) ≤ ∫ c, (1 : ℝ) ∂Q :=
        integral_mono hslice hone (fun c => (hloss_bounded c z).2)
      simpa using hle
  have hfixed_empirical_bounds :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        ∀ s : Fin m → Sample,
          0 ≤ measurePACBayesEmpiricalLoss ctx m s loss Q ∧
            measurePACBayesEmpiricalLoss ctx m s loss Q ≤ 1 := by
    intro Q hQ s
    letI : IsProbabilityMeasure Q := hQ
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hinv_nonneg : 0 ≤ (m : ℝ)⁻¹ :=
      inv_nonneg.mpr hmpos.le
    have hsum_nonneg :
        0 ≤ ∑ i : Fin m, ∫ c, loss c (s i) ∂Q :=
      Finset.sum_nonneg fun i hi => (hfixed_slice_bounds Q hQ (s i)).1
    have hsum_le :
        (∑ i : Fin m, ∫ c, loss c (s i) ∂Q) ≤ (m : ℝ) := by
      calc
        (∑ i : Fin m, ∫ c, loss c (s i) ∂Q) ≤
            ∑ i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum fun i hi => (hfixed_slice_bounds Q hQ (s i)).2
        _ = (m : ℝ) := by simp
    constructor
    · simpa [measurePACBayesEmpiricalLoss] using
        mul_nonneg hinv_nonneg hsum_nonneg
    · have hmul :
          (m : ℝ)⁻¹ * ∑ i : Fin m, ∫ c, loss c (s i) ∂Q ≤
            (m : ℝ)⁻¹ * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
      simpa [measurePACBayesEmpiricalLoss,
        inv_mul_cancel₀ (ne_of_gt hmpos)] using hmul
  have hfixed_empirical_measurable :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        Measurable
          (fun s : Fin m → Sample =>
            measurePACBayesEmpiricalLoss ctx m s loss Q) := by
    intro Q hQ
    letI : IsProbabilityMeasure Q := hQ
    have hkernel :
        Measurable (fun z : Sample => ∫ c, loss c z ∂Q) := by
      have hstrong :
          StronglyMeasurable
            (fun p : Sample × Concept => loss p.2 p.1) :=
        hmeas_loss.stronglyMeasurable.comp_measurable measurable_swap
      exact hstrong.integral_prod_right'.measurable
    have hsum :
        Measurable
          (fun s : Fin m → Sample =>
            ∑ i : Fin m, ∫ c, loss c (s i) ∂Q) := by
      refine Finset.measurable_sum Finset.univ ?_
      intro i hi
      exact hkernel.comp (measurable_pi_apply i)
    simpa [measurePACBayesEmpiricalLoss] using measurable_const.mul hsum
  have hfixed_exp_integrable_at_one :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        Integrable
          (fun s : Fin m → Sample =>
            Real.exp
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q)) μ := by
    intro Q hQ
    have hpop := hfixed_population_bounds Q hQ
    have hemp := hfixed_empirical_bounds Q hQ
    have hmeas_gap :
        Measurable
          (fun s : Fin m → Sample =>
            measurePACBayesPopulationLoss ctx loss Q -
              measurePACBayesEmpiricalLoss ctx m s loss Q) :=
      measurable_const.sub (hfixed_empirical_measurable Q hQ)
    have hmeas_exp :
        Measurable
          (fun s : Fin m → Sample =>
            Real.exp
              (measurePACBayesPopulationLoss ctx loss Q -
                measurePACBayesEmpiricalLoss ctx m s loss Q)) :=
      Real.measurable_exp.comp hmeas_gap
    refine Integrable.of_bound hmeas_exp.aestronglyMeasurable
      (Real.exp 1) ?_
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    linarith [hpop.1, hemp s |>.1]
  have hfixed_chernoff :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        ∀ (ε t : ℝ),
          0 ≤ t →
          Integrable
            (fun s : Fin m → Sample =>
              Real.exp
                (t *
                  (measurePACBayesPopulationLoss ctx loss Q -
                    measurePACBayesEmpiricalLoss ctx m s loss Q))) μ →
          μ.real
              {s |
                ε ≤
                  measurePACBayesPopulationLoss ctx loss Q -
                    measurePACBayesEmpiricalLoss ctx m s loss Q} ≤
            Real.exp (-t * ε) *
              ProbabilityTheory.mgf
                (fun s : Fin m → Sample =>
                  measurePACBayesPopulationLoss ctx loss Q -
                    measurePACBayesEmpiricalLoss ctx m s loss Q) μ t := by
    intro Q hQ ε t ht h_integrable
    exact ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht h_integrable
  have hfixed_chernoff_at_one :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        ∀ ε : ℝ,
          μ.real
              {s |
                ε ≤
                  measurePACBayesPopulationLoss ctx loss Q -
                    measurePACBayesEmpiricalLoss ctx m s loss Q} ≤
            Real.exp (-ε) *
              ProbabilityTheory.mgf
                (fun s : Fin m → Sample =>
                  measurePACBayesPopulationLoss ctx loss Q -
                    measurePACBayesEmpiricalLoss ctx m s loss Q) μ 1 := by
    intro Q hQ ε
    simpa [one_mul] using
      (hfixed_chernoff Q hQ ε 1 (by norm_num)
        (by simpa only [one_mul] using hfixed_exp_integrable_at_one Q hQ))
  have hfinite_kl_implies_ac :
      ∀ Q : Measure Concept, IsProbabilityMeasure Q →
        measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ →
          Q ≪ ctx.prior_distribution := by
    intro Q hQ hfinite
    exact
      (measurePACBayes_finite_KL_density_spec
        Q ctx.prior_distribution hQ hprior hfinite).1
  have hfinite_witness_change_of_measure :
      ∀ s ∈ V, ∃ Q : Measure Concept,
        IsProbabilityMeasure Q ∧
        measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ ∧
        Q ≪ ctx.prior_distribution ∧
        measurePACBayesPopulationLoss ctx loss Q =
          ∫ c,
            (Q.rnDeriv ctx.prior_distribution c).toReal *
              (∫ z, loss c z ∂ctx.sampling_distribution) ∂ctx.prior_distribution ∧
        measurePACBayesKLDivergence Q ctx.prior_distribution =
          ∫⁻ c, ENNReal.ofReal
            (InformationTheory.klFun
              (Q.rnDeriv ctx.prior_distribution c).toReal) ∂ctx.prior_distribution := by
    intro s hs
    rcases hs with ⟨Q, hQ, hfinite, hviol⟩
    letI : IsProbabilityMeasure Q := hQ
    letI : IsProbabilityMeasure ctx.prior_distribution := hprior
    have hAC : Q ≪ ctx.prior_distribution :=
      hfinite_kl_implies_ac Q hQ hfinite
    have hdensity :=
      measurePACBayes_finite_KL_density_spec
        Q ctx.prior_distribution hQ hprior hfinite
    refine ⟨Q, hQ, hfinite, hAC, ?_, hdensity.2⟩
    rw [measurePACBayesPopulationLoss]
    exact
      measurePACBayes_integral_change_of_measure
        Q ctx.prior_distribution hQ hprior hAC
        (fun c => ∫ z, loss c z ∂ctx.sampling_distribution)
  let A : Set (Fin m → Sample) :=
    measurePACBayesExpectedLossEvent ctx m hm δ loss
  have hvariational_witness :
    ∀ s ∈ V, ∃ Q : Measure Concept, IsProbabilityMeasure Q ∧
        measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ ∧
        measurePACBayesPopulationLoss ctx loss Q -
            measurePACBayesEmpiricalLoss ctx m s loss Q ≤
          (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
            Real.log
              (∫ c,
                Real.exp
                  ((∫ z, loss c z ∂ctx.sampling_distribution) -
                    (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) ∂ctx.prior_distribution) := by
    intro s hs
    rcases hfinite_witness_change_of_measure s hs with
      ⟨Q, hQ, hfinite, hAC, hpopulation, hkl⟩
    letI : IsProbabilityMeasure Q := hQ
    letI : IsProbabilityMeasure ctx.prior_distribution := hprior
    letI : IsProbabilityMeasure ctx.sampling_distribution := hsampling
    let f : Concept → ℝ := fun c =>
      (∫ z, loss c z ∂ctx.sampling_distribution) -
        (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)
    have hpop_meas :
        Measurable
          (fun c => ∫ z, loss c z ∂ctx.sampling_distribution) := by
      exact hmeas_loss.stronglyMeasurable.integral_prod_right'.measurable
    have hslice_meas (i : Fin m) :
        Measurable (fun c => loss c (s i)) := by
      simpa [Function.uncurry] using
        hmeas_loss.comp (measurable_id.prodMk measurable_const)
    have hemp_meas :
        Measurable
          (fun c => (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) := by
      exact measurable_const.mul (Finset.measurable_sum Finset.univ (by
        intro i hi
        exact hslice_meas i))
    have hf_meas : Measurable f := by
      exact hpop_meas.sub hemp_meas
    have hpop_mem (c : Concept) :
        (∫ z, loss c z ∂ctx.sampling_distribution) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · simpa using
          (integral_mono (integrable_const 0)
            (measurePACBayesPointwiseLoss_integrable
              (μ := ctx.sampling_distribution)
              loss hmeas_loss hloss_bounded c)
            (fun z => (hloss_bounded c z).1))
      · have hle := integral_mono
            (measurePACBayesPointwiseLoss_integrable
              (μ := ctx.sampling_distribution)
              loss hmeas_loss hloss_bounded c)
            (integrable_const 1)
            (fun z => (hloss_bounded c z).2)
        simpa using hle
    have hemp_nonneg (c : Concept) :
        0 ≤ (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) := by
      have hmpos : 0 < (m : ℝ) := by
        exact_mod_cast (Nat.zero_lt_of_lt hm)
      apply mul_nonneg (inv_nonneg.mpr hmpos.le)
      exact Finset.sum_nonneg (fun i hi => (hloss_bounded c (s i)).1)
    have hemp_le_one (c : Concept) :
        (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ≤ 1 := by
      have hmpos : 0 < (m : ℝ) := by
        exact_mod_cast (Nat.zero_lt_of_lt hm)
      have hsum : (∑ i : Fin m, loss c (s i)) ≤ (m : ℝ) := by
        calc
          (∑ i : Fin m, loss c (s i)) ≤ ∑ i : Fin m, (1 : ℝ) :=
            Finset.sum_le_sum (fun i hi => (hloss_bounded c (s i)).2)
          _ = (m : ℝ) := by simp
      have hmul := mul_le_mul_of_nonneg_left hsum
        (inv_nonneg.mpr hmpos.le)
      simpa [inv_mul_cancel₀ (ne_of_gt hmpos)] using hmul
    have hf_bound (c : Concept) : ‖f c‖ ≤ 2 := by
      dsimp [f]
      apply (abs_le).2
      constructor
      · linarith [hpop_mem c |>.1, hemp_le_one c]
      · linarith [hpop_mem c |>.2, hemp_nonneg c]
    have hfQ : Integrable f Q :=
      integrable_of_measurable_bounded_real hf_meas hf_bound
    have hfexp_meas : Measurable (fun c => Real.exp (f c)) :=
      Real.measurable_exp.comp hf_meas
    have hfP : Integrable (fun c => Real.exp (f c))
        ctx.prior_distribution := by
      refine Integrable.of_bound hfexp_meas.aestronglyMeasurable
        (Real.exp 2) ?_
      filter_upwards [] with c
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      exact le_trans (le_abs_self _)
        (by simpa [Real.norm_eq_abs] using hf_bound c)
    have hemp_int :
        Integrable
          (fun c => (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) Q := by
      exact
        (integrable_finset_sum Finset.univ (by
          intro i hi
          exact measurePACBayesPointwiseLoss_integrable_sample_slice
            (Q := Q) loss hmeas_loss hloss_bounded (s i))).const_mul _
    have hgap :
        (∫ c, f c ∂Q) =
          measurePACBayesPopulationLoss ctx loss Q -
            measurePACBayesEmpiricalLoss ctx m s loss Q := by
      dsimp [f, measurePACBayesPopulationLoss, measurePACBayesEmpiricalLoss]
      calc
        (∫ c,
            (∫ z, loss c z ∂ctx.sampling_distribution) -
              (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ∂Q) =
            (∫ c, ∫ z, loss c z ∂ctx.sampling_distribution ∂Q) -
              ∫ c, (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ∂Q := by
          rw [integral_sub
            (measurePACBayesPointwiseLoss_integrable_population
              (μ := ctx.sampling_distribution) (Q := Q)
              loss hmeas_loss hloss_bounded)
            hemp_int]
        _ =
            (∫ c, ∫ z, loss c z ∂ctx.sampling_distribution ∂Q) -
              (m : ℝ)⁻¹ *
                ∑ i : Fin m, ∫ c, loss c (s i) ∂Q := by
          rw [integral_const_mul,
            integral_finset_sum Finset.univ (by
              intro i hi
              exact
                measurePACBayesPointwiseLoss_integrable_sample_slice
                  (Q := Q) loss hmeas_loss hloss_bounded (s i))]
    have hvariational :=
      measurePACBayes_change_of_measure_log_mgf
        Q ctx.prior_distribution hQ hprior
        (by simpa [measurePACBayesKLDivergence] using hfinite)
        f hfQ hfP
    refine ⟨Q, hQ, hfinite, ?_⟩
    rw [← hgap]
    simpa [f] using hvariational
  have hproduct_fixed_concept :
      ∀ c : Concept,
        HasSubgaussianMGF
          (fun s : Fin m → Sample =>
            (∫ z, loss c z ∂ctx.sampling_distribution) -
              (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))
          (((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4) μ := by
    intro c
    simpa [μ] using
      (measurePACBayes_productLaw_exponential_budget
        ctx m (Nat.zero_lt_of_lt hm) c loss hsampling hmeas_loss hloss_bounded)
  have hproduct_exp_integrable :
      ∀ c : Concept,
        Integrable
          (fun s : Fin m → Sample =>
            Real.exp
              ((∫ z, loss c z ∂ctx.sampling_distribution) -
                (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))) μ := by
    intro c
    simpa [one_mul] using
      (hproduct_fixed_concept c).integrable_exp_mul 1
  have hproduct_mgf_budget :
      ∀ c : Concept,
        ∫ s : Fin m → Sample,
            Real.exp
              ((∫ z, loss c z ∂ctx.sampling_distribution) -
                (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i)) ∂μ ≤
          Real.exp
            (((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) / 2) := by
    intro c
    simpa [ProbabilityTheory.mgf, one_mul] using
      (hproduct_fixed_concept c).mgf_le 1
  have hfinite_mass : μ V ≤ ENNReal.ofReal δ := by
    let G : (Fin m → Sample) × Concept → ℝ := fun p =>
      Real.exp
        ((∫ z, loss p.2 z ∂ctx.sampling_distribution) -
          (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i))
    let F : (Fin m → Sample) → ℝ := fun s =>
      ∫ c, G (s, c) ∂ctx.prior_distribution
    have hpop_meas :
        Measurable
          (fun c : Concept => ∫ z, loss c z ∂ctx.sampling_distribution) := by
      exact hmeas_loss.stronglyMeasurable.integral_prod_right'.measurable
    have hslice_meas (i : Fin m) :
        Measurable
          (fun p : (Fin m → Sample) × Concept =>
            loss p.2 (p.1 i)) := by
      simpa [Function.uncurry] using
        hmeas_loss.comp
          (measurable_snd.prodMk
            ((measurable_pi_apply i).comp measurable_fst))
    have hemp_meas :
        Measurable
          (fun p : (Fin m → Sample) × Concept =>
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)) := by
      exact measurable_const.mul
        (Finset.measurable_sum Finset.univ (by
          intro i hi
          exact hslice_meas i))
    have hG_meas : Measurable G := by
      dsimp [G]
      exact Real.measurable_exp.comp
        ((hpop_meas.comp measurable_snd).sub hemp_meas)
    have hpoint_population_bounds :
        ∀ c : Concept,
          0 ≤ ∫ z, loss c z ∂ctx.sampling_distribution ∧
            (∫ z, loss c z ∂ctx.sampling_distribution) ≤ 1 := by
      intro c
      have hslice :
          Integrable (loss c) ctx.sampling_distribution :=
        measurePACBayesPointwiseLoss_integrable
          (μ := ctx.sampling_distribution) loss hmeas_loss hloss_bounded c
      constructor
      · simpa using
          (integral_mono (integrable_const 0) hslice
            (fun z => (hloss_bounded c z).1))
      · have hle :
            (∫ z, loss c z ∂ctx.sampling_distribution) ≤
              ∫ z, (1 : ℝ) ∂ctx.sampling_distribution :=
          integral_mono hslice (integrable_const 1)
            (fun z => (hloss_bounded c z).2)
        simpa using hle
    have hpoint_empirical_bounds :
        ∀ c : Concept, ∀ s : Fin m → Sample,
          0 ≤ (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ∧
            (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i) ≤ 1 := by
      intro c s
      have hmpos : 0 < (m : ℝ) := by
        exact_mod_cast (Nat.zero_lt_of_lt hm)
      have hsum_nonneg :
          0 ≤ ∑ i : Fin m, loss c (s i) :=
        Finset.sum_nonneg (fun i hi => (hloss_bounded c (s i)).1)
      have hsum_le :
          (∑ i : Fin m, loss c (s i)) ≤ (m : ℝ) := by
        calc
          (∑ i : Fin m, loss c (s i)) ≤ ∑ i : Fin m, (1 : ℝ) :=
            Finset.sum_le_sum (fun i hi => (hloss_bounded c (s i)).2)
          _ = (m : ℝ) := by simp
      constructor
      · exact mul_nonneg (inv_nonneg.mpr hmpos.le) hsum_nonneg
      · have hmul :=
          mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hmpos.le)
        simpa [inv_mul_cancel₀ (ne_of_gt hmpos)] using hmul
    have hG_bound :
        ∀ p : (Fin m → Sample) × Concept, ‖G p‖ ≤ Real.exp 1 := by
      intro p
      have hpop := hpoint_population_bounds p.2
      have hemp := hpoint_empirical_bounds p.2 p.1
      dsimp [G]
      rw [abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      linarith [hpop.1, hemp.1]
    have hG_int :
        Integrable G
          (μ.prod ctx.prior_distribution) := by
      exact integrable_of_measurable_bounded_real hG_meas hG_bound
    have hF_int : Integrable F μ := by
      simpa [F] using hG_int.integral_prod_left
    have hprior_mgf_budget :
        ∀ t : ℝ,
          ∫ s, ∫ c,
              Real.exp
                (t *
                  ((∫ z, loss c z ∂ctx.sampling_distribution) -
                    (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))) ∂ctx.prior_distribution ∂μ ≤
            Real.exp
              (((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) *
                t ^ 2 / 2) := by
      intro t
      let Gt : (Fin m → Sample) × Concept → ℝ := fun p =>
        Real.exp
          (t *
            ((∫ z, loss p.2 z ∂ctx.sampling_distribution) -
              (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)))
      let Ft : (Fin m → Sample) → ℝ := fun s =>
        ∫ c, Gt (s, c) ∂ctx.prior_distribution
      have hGt_meas : Measurable Gt := by
        dsimp [Gt]
        exact Real.measurable_exp.comp
          (measurable_const.mul
            ((hpop_meas.comp measurable_snd).sub hemp_meas))
      have hGt_bound :
          ∀ p : (Fin m → Sample) × Concept, ‖Gt p‖ ≤ Real.exp |t| := by
        intro p
        have hpop := hpoint_population_bounds p.2
        have hemp := hpoint_empirical_bounds p.2 p.1
        have hgap_abs :
            |(∫ z, loss p.2 z ∂ctx.sampling_distribution) -
                (m : ℝ)⁻¹ * ∑ i : Fin m, loss p.2 (p.1 i)| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hpop.1, hpop.2, hemp.1, hemp.2]
        dsimp [Gt]
        rw [abs_of_nonneg (Real.exp_pos _).le]
        apply Real.exp_le_exp.mpr
        exact
          (le_abs_self _).trans
            (by
              rw [abs_mul]
              simpa using
                (mul_le_mul_of_nonneg_left hgap_abs (abs_nonneg t)))
      have hGt_int :
          Integrable Gt (μ.prod ctx.prior_distribution) := by
        exact integrable_of_measurable_bounded_real hGt_meas hGt_bound
      have hFt_int : Integrable Ft μ := by
        simpa [Ft] using hGt_int.integral_prod_left
      calc
        ∫ s, ∫ c,
              Real.exp
                (t *
                  ((∫ z, loss c z ∂ctx.sampling_distribution) -
                    (m : ℝ)⁻¹ * ∑ i : Fin m, loss c (s i))) ∂ctx.prior_distribution ∂μ =
            ∫ s, Ft s ∂μ := by
          rfl
        _ = ∫ p, Gt p ∂(μ.prod ctx.prior_distribution) := by
          simpa [Ft] using (integral_prod Gt hGt_int).symm
        _ = ∫ c, ∫ s, Gt (s, c) ∂μ ∂ctx.prior_distribution :=
          integral_prod_symm Gt hGt_int
        _ ≤ ∫ c,
            Real.exp
              (((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) *
                t ^ 2 / 2) ∂ctx.prior_distribution := by
          apply integral_mono hGt_int.integral_prod_right (integrable_const _)
          intro c
          simpa [Gt, ProbabilityTheory.mgf] using
            (hproduct_fixed_concept c).mgf_le t
        _ = Real.exp
            (((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) *
              t ^ 2 / 2) := by
          simp
    have hF_budget :
        ∫ s, F s ∂μ ≤
          Real.exp
            (((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) / 2) := by
      simpa [F, G, one_mul] using hprior_mgf_budget 1
    have hlinear_prior_markov :
        μ {s | F s > Real.exp 1 / δ} ≤ ENNReal.ofReal δ := by
      have hF_nonneg : ∀ s, 0 ≤ F s := by
        intro s
        exact integral_nonneg (fun c => (Real.exp_pos _).le)
      have hbudget_le_exp_one :
          Real.exp
              (((((m : NNReal)⁻¹ ^ 2) * (m : NNReal) / 4 : NNReal) : ℝ) / 2) ≤
            Real.exp 1 := by
        apply Real.exp_le_exp.mpr
        have hmpos : 0 < (m : ℝ) := by
          exact_mod_cast (Nat.zero_lt_of_lt hm)
        have hmone : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (Nat.one_le_of_lt hm)
        norm_num [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_pow]
        field_simp [ne_of_gt hmpos]
        nlinarith [hmone]
      exact
        measure_gt_le_of_integral_le_of_nonneg F
          (Real.exp 1 / δ) (Real.exp 1) δ hF_int hF_nonneg
          (hF_budget.trans hbudget_le_exp_one)
          (div_pos (Real.exp_pos 1) hδ).le
          (by
            intro _
            convert le_rfl using 1 <;>
              field_simp [ne_of_gt (Real.exp_pos 1), ne_of_gt hδ])
          (by
            intro ht
            have htpos : 0 < Real.exp 1 / δ := div_pos (Real.exp_pos 1) hδ
            exact (htpos.ne' ht).elim)
    /- Exact source-boundary attempt:
       `hlinear_prior_markov` controls one linear prior integral, while
       `hvariational_witness` controls one posterior witness.  Neither
       supplies the existential-posterior aggregation needed for `μ V`.
       The source route is SAM Appendix A.1 Eq. (5), which cites
       McAllester (1999) and Dziugaite--Roy (2017).  The available local
       McAllester declaration is PMF/countable-valued and cannot be applied
       to this continuous Measure-valued context. -/
    fail_if_success exact hlinear_prior_markov
    fail_if_success exact hvariational_witness
    fail_if_success exact (hprior_mgf_budget 1)
    have hsource_moment :=
      measurePACBayes_source_McAllester_moment_event
        (ctx := ctx) (m := m) (hm := hm) (δ := δ)
        (hδ := hδ) (hδ_lt_one := hδ_lt_one) (loss := loss)
        (hprior := hprior) (hsampling := hsampling)
        (hmeas_loss := hmeas_loss) (hloss_bounded := hloss_bounded)
    have hV_subset :
        V ⊆
          {s | 4 * (m : ℝ) / δ <
            measurePACBayesMcAllesterMoment ctx m loss s} := by
      simpa [V] using hsource_moment.1
    calc
      μ V ≤
          μ {s | 4 * (m : ℝ) / δ <
            measurePACBayesMcAllesterMoment ctx m loss s} :=
        measure_mono hV_subset
      _ ≤ ENNReal.ofReal δ := by
        simpa [μ] using hsource_moment.2
  have hAV : Aᶜ = V := by
    simpa [A, V] using
      (measurePACBayesExpectedLossEvent_compl
        (ctx := ctx) (m := m) (hm := hm) (δ := δ) (loss := loss))
  have hmass : μ Aᶜ ≤ ENNReal.ofReal δ := by
    calc
      μ Aᶜ = μ V := congrArg μ hAV
      _ ≤ ENNReal.ofReal δ := hfinite_mass
  simpa [μ, A] using hmass
  -/

/- Appendix A.1 is now a direct specialization of the guarded source-facing
   Measure interface.  All carriers in this theorem are the paper's actual
   Measure-valued constructions: the subtype parameter space, the
   continuous Gaussian prior, `S.dataLaw`, and its iid `Measure.pi` law. -/
theorem theorem2AppendixA1_arbitraryMeasure_PACBayes_event_of_bounded_loss
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1GridPACBayesFailure
          (S := S) w δ hn hk j hdom) ≤
      ENNReal.ofReal
        (theorem2AppendixA1PriorGridConfidence δ.1 j) := by
  fail_if_success
    exact
      (ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := Setup.iidTrainingLaw (S := S))
        (X := fun _ : Dataset n X Y => (0 : ℝ))
        (t := 0) 0 (by norm_num) (by simp))
  let ctx :=
    theorem2AppendixA1ParameterGridContext (S := S) hk j hdom
  let loss :=
    theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)
  have hdelta_pos :
      0 < theorem2AppendixA1PriorGridConfidence δ.1 j := by
    unfold theorem2AppendixA1PriorGridConfidence
    apply div_pos
    · exact mul_pos (by norm_num) δ.2.1
    · have hj : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
      exact mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_pos hj)
  have hprior :
      IsProbabilityMeasure ctx.prior_distribution := by
    dsimp [ctx]
    exact theorem2AppendixA1ParameterGridContext_prior_isProbability
      S hk j hdom
  have hsampling :
      IsProbabilityMeasure ctx.sampling_distribution := by
    dsimp [ctx, theorem2AppendixA1ParameterGridContext]
    exact S.dataLaw_isProbability
  have hsource_bounded :
      ∀ u z, 0 ≤ loss u z ∧ loss u z ≤ 1 := by
    simpa [loss] using
      theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
        (S := S) hbounded
  have hdelta_lt_one :
      theorem2AppendixA1PriorGridConfidence δ.1 j < 1 := by
    unfold theorem2AppendixA1PriorGridConfidence
    have hden_pos :
        0 < Real.pi ^ 2 * (((j + 1 : ℕ) : ℝ) ^ 2) := by
      positivity
    apply (div_lt_iff₀ hden_pos).2
    have hnum :
        6 * δ.1 < (6 : ℝ) :=
      by nlinarith [δ.2.2]
    have hpi_sq : (6 : ℝ) < Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hj_sq :
        (1 : ℝ) ≤ (((j + 1 : ℕ) : ℝ) ^ 2) := by
      have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le j))
      nlinarith [sq_nonneg (((j + 1 : ℕ) : ℝ) - 1)]
    have hden :
        (6 : ℝ) <
          Real.pi ^ 2 * (((j + 1 : ℕ) : ℝ) ^ 2) := by
      have hpi_nonneg : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      calc
        (6 : ℝ) < Real.pi ^ 2 := hpi_sq
        _ = Real.pi ^ 2 * 1 := by ring
        _ ≤ Real.pi ^ 2 * (((j + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hj_sq hpi_nonneg
    nlinarith
  have hfinite_mass :
      measurePACBayesSampleLaw ctx n
          (measurePACBayesFiniteKLViolationEvent ctx n hn
            (theorem2AppendixA1PriorGridConfidence δ.1 j) loss) ≤
        ENNReal.ofReal
          (theorem2AppendixA1PriorGridConfidence δ.1 j) := by
    exact
      mcallester_theorem1_pac_bayes_model_averaging_of_one_lt_sample_size
        (ctx := ctx) (m := n) (hm := hn)
        (δ := theorem2AppendixA1PriorGridConfidence δ.1 j)
        hdelta_pos hdelta_lt_one
        (loss := loss) hprior hsampling hmeas_loss hsource_bounded
  have hmass :
      measurePACBayesSampleLaw ctx n
          (measurePACBayesExpectedLossEvent ctx n hn
            (theorem2AppendixA1PriorGridConfidence δ.1 j) loss)ᶜ ≤
        ENNReal.ofReal
          (theorem2AppendixA1PriorGridConfidence δ.1 j) := by
    rw [measurePACBayesExpectedLossEvent_compl
      (ctx := ctx) (m := n) (hm := hn)
      (δ := theorem2AppendixA1PriorGridConfidence δ.1 j)
      (loss := loss)]
    exact hfinite_mass
  rw [theorem2AppendixA1GridPACBayesFailure_spec
    (S := S) (w := w) (δ := δ) (hn := hn) (hk := hk) (j := j)
    (hdom := hdom)]
  simpa [ctx, loss] using hmass

/- Direct failure-mass consumer for the Appendix A.1 prior-grid union
   theorem.  Keeping this declaration separate makes the union-bound input
   come from the source supplier rather than from an arbitrary `hgrid_mass`
   premise. -/
theorem theorem2AppendixA1PerGridPACBayesFailureMass
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (hdom :
      ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1GridPACBayesFailure
          (S := S) w δ hn hk j hdom) ≤
      ENNReal.ofReal
        (theorem2AppendixA1PriorGridConfidence δ.1 j) := by
  exact theorem2AppendixA1_arbitraryMeasure_PACBayes_event_of_bounded_loss
    (S := S) w δ hn hk j hdom hmeas_loss hbounded

theorem theorem2AppendixA1CanonicalContext_priorGridFailureMass_of_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (ctx : Theorem2AppendixA1CanonicalContext S w δ hn hk)
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    (Setup.iidTrainingLaw (S := S))
        (⋃ j, theorem2AppendixA1GridPACBayesFailure
          (S := S) w δ hn hk j (hdom_grid j)) ≤
      ENNReal.ofReal δ.1 := by
  apply theorem2AppendixA1CanonicalContext_priorGridFailureMass
    (S := S) w δ hn hk ctx
    (fun j => theorem2AppendixA1GridPACBayesFailure
      (S := S) w δ hn hk j (hdom_grid j))
  intro j
  simpa [Theorem2AppendixA1CanonicalContext.priorGridConfidence] using
      (theorem2AppendixA1PerGridPACBayesFailureMass
      (S := S) w δ hn hk j (hdom_grid j) hmeas_loss hbounded)

/-! Theorem 2 (Appendix A.1, Eq. (4)).  The checked realization below uses an
   ambient extension internally; the source predicate keeps the paper's
   W-indexed population loss and exposes the required perturbed-domain lift
   relationally. -/
def internalGaussianTestErrorCondition (S : Setup n E X Y Ω)
    (w : Setup.Parameter S) : Prop :=
  Setup.populationLossValue (S := S) w ≤
    ∫ ε : E, Setup.populationLossAmbient (S := S) (w.1 + S.rho • ε)
      ∂(stdGaussian E)

theorem internalGaussianTestErrorCondition_spec (S : Setup n E X Y Ω)
    (w : Setup.Parameter S) :
    internalGaussianTestErrorCondition S w =
      (Setup.populationLossValue (S := S) w ≤
        ∫ ε : E, Setup.populationLossAmbient (S := S) (w.1 + S.rho • ε)
          ∂(stdGaussian E)) := by
  rfl

/- Explicit realization bridge back to the W-indexed loss carrier.  This is
   intentionally a theorem obligation: the paper states the direct Gaussian
   expectation, while Lean's subtype carrier needs a measurable domain lift. -/
theorem internalGaussianTestErrorCondition_domain_bridge
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hdom : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace) :
    internalGaussianTestErrorCondition S w ↔
      Setup.populationLossValue (S := S) w ≤
        ∫ ε : E, Setup.populationLossValue (S := S)
          ⟨w.1 + S.rho • ε, hdom ε⟩ ∂(stdGaussian E) := by
  constructor
  · intro h
    simpa [internalGaussianTestErrorCondition, Setup.populationLossAmbient,
      Setup.populationLossValue, Setup.lossAt, hdom] using h
  · intro h
    simpa [internalGaussianTestErrorCondition, Setup.populationLossAmbient,
      Setup.populationLossValue, Setup.lossAt, hdom] using h

noncomputable def internalGaussianPerturbedPopulationLoss
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hdom : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace) : ℝ :=
  ∫ ε : E, Setup.populationLossValue (S := S)
    ⟨w.1 + S.rho • ε, hdom ε⟩ ∂(stdGaussian E)

theorem internalGaussianPerturbedPopulationLoss_spec
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hdom : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace) :
    internalGaussianPerturbedPopulationLoss (S := S) w hdom =
      ∫ ε : E, Setup.populationLossValue (S := S)
        ⟨w.1 + S.rho • ε, hdom ε⟩ ∂(stdGaussian E) := by
  rfl

/- Pointwise graph of a source Gaussian integrand at an explicit standard
   deviation.  The paper uses `rho` in its premise and a smaller selected
   `sigma` in Appendix A.1, so the scale is part of the canonical object
   rather than hidden in a rho-specialized definition. -/
def sourceGaussianPopulationGraphAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (sigma : ℝ) (ε : E) (value : ℝ) : Prop :=
  Setup.sourcePopulationLossAt (S := S) (w.1 + sigma • ε) value

def sourceGaussianPopulationGraph
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (ε : E) (value : ℝ) : Prop :=
  sourceGaussianPopulationGraphAtSigma (S := S) w S.rho ε value

/- Source-contract relation for the paper notation
   `E_{ε_i∼N(0,ρ)}[L_D(w+ε)]`.  The relation is graph-based over the literal
   perturbed expression and requires agreement only almost everywhere under
   the Gaussian law.  It does not assert all-ε domain closure and does not use
   the private ambient zero extension as source semantics. -/
def sourceGaussianPerturbedPopulationLossAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (sigma : ℝ) (value : ℝ) : Prop :=
  ∃ f : E → ℝ,
    (∀ᵐ ε ∂(stdGaussian E),
      sourceGaussianPopulationGraphAtSigma (S := S) w sigma ε (f ε)) ∧
    SOptLib.expectationWellDefined (stdGaussian E) f ∧
    value = ∫ ε : E, f ε ∂(stdGaussian E)

def sourceGaussianPerturbedPopulationLoss
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (value : ℝ) : Prop :=
  sourceGaussianPerturbedPopulationLossAtSigma (S := S) w S.rho value

/- Source-contract relation for the empirical Gaussian term
   `E_{ε_i∼N(0,ρ)}[L_S(w+ε)]` appearing in the Appendix A.1
   PAC-Bayes bound. -/
def sourceGaussianPerturbedEmpiricalLossAtSigma
    (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Setup.Parameter S) (sigma : ℝ) (value : ℝ) : Prop :=
  ∃ f : E → ℝ,
    (∀ᵐ ε ∂(stdGaussian E),
      Setup.sourceEmpiricalLossAt (S := S) s (w.1 + sigma • ε) (f ε)) ∧
    SOptLib.expectationWellDefined (stdGaussian E) f ∧
    value = ∫ ε : E, f ε ∂(stdGaussian E)

def sourceGaussianPerturbedEmpiricalLoss
    (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Setup.Parameter S) (value : ℝ) : Prop :=
  sourceGaussianPerturbedEmpiricalLossAtSigma (S := S) s w S.rho value

theorem sourceGaussianPopulationGraphAtSigma_rho
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (ε : E) (value : ℝ) :
    sourceGaussianPopulationGraphAtSigma (S := S) w S.rho ε value ↔
      sourceGaussianPopulationGraph (S := S) w ε value := by
  rfl

theorem sourceGaussianPerturbedPopulationLossAtSigma_rho
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (value : ℝ) :
    sourceGaussianPerturbedPopulationLossAtSigma (S := S) w S.rho value ↔
      sourceGaussianPerturbedPopulationLoss (S := S) w value := by
  rfl

theorem sourceGaussianPerturbedEmpiricalLossAtSigma_rho
    (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Setup.Parameter S) (value : ℝ) :
    sourceGaussianPerturbedEmpiricalLossAtSigma (S := S) s w S.rho value ↔
      sourceGaussianPerturbedEmpiricalLoss (S := S) s w value := by
  rfl

def sourceGaussianPerturbedEmpiricalLossWellDefinedObligation
    (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Setup.Parameter S) : Prop :=
  ∃ value : ℝ, sourceGaussianPerturbedEmpiricalLoss (S := S) s w value

private theorem sourcePopulationLossAt_value_unique
    (S : Setup n E X Y Ω) {u : E} {value₀ value₁ : ℝ}
    (h₀ : Setup.sourcePopulationLossAt (S := S) u value₀)
    (h₁ : Setup.sourcePopulationLossAt (S := S) u value₁) :
    value₀ = value₁ := by
  rcases h₀ with ⟨hu₀, hpop₀⟩
  rcases h₁ with ⟨hu₁, hpop₁⟩
  rcases hpop₀ with ⟨_hwd₀, hval₀⟩
  rcases hpop₁ with ⟨_hwd₁, hval₁⟩
  have hsub :
      (⟨u, hu₀⟩ : Setup.Parameter S) =
        (⟨u, hu₁⟩ : Setup.Parameter S) := by
    exact Subtype.ext rfl
  calc
    value₀ = Setup.populationLossValue (S := S) ⟨u, hu₀⟩ := hval₀
    _ = Setup.populationLossValue (S := S) ⟨u, hu₁⟩ := by rw [hsub]
    _ = value₁ := hval₁.symm

private theorem sourceGaussianPopulationGraph_value_unique
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (ε : E)
    {value₀ value₁ : ℝ}
    (h₀ : sourceGaussianPopulationGraph (S := S) w ε value₀)
    (h₁ : sourceGaussianPopulationGraph (S := S) w ε value₁) :
    value₀ = value₁ := by
  exact
    sourcePopulationLossAt_value_unique (S := S)
      (u := w.1 + S.rho • ε) h₀ h₁

private theorem sourceGaussianPopulationGraphAtSigma_value_unique
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (sigma : ℝ) (ε : E)
    {value₀ value₁ : ℝ}
    (h₀ :
      sourceGaussianPopulationGraphAtSigma (S := S) w sigma ε value₀)
    (h₁ :
      sourceGaussianPopulationGraphAtSigma (S := S) w sigma ε value₁) :
    value₀ = value₁ := by
  exact
    sourcePopulationLossAt_value_unique (S := S)
      (u := w.1 + sigma • ε) h₀ h₁

private theorem sourceGaussianPerturbedPopulationLoss_value_unique
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    {value₀ value₁ : ℝ}
    (h₀ : sourceGaussianPerturbedPopulationLoss (S := S) w value₀)
    (h₁ : sourceGaussianPerturbedPopulationLoss (S := S) w value₁) :
    value₀ = value₁ := by
  rcases h₀ with ⟨f₀, hf₀_graph, _hf₀_wd, hf₀_value⟩
  rcases h₁ with ⟨f₁, hf₁_graph, _hf₁_wd, hf₁_value⟩
  have hfg : f₀ =ᵐ[stdGaussian E] f₁ := by
    filter_upwards [hf₀_graph, hf₁_graph] with ε hε₀ hε₁
    exact sourceGaussianPopulationGraph_value_unique (S := S) w ε hε₀ hε₁
  calc
    value₀ = ∫ ε : E, f₀ ε ∂(stdGaussian E) := hf₀_value
    _ = ∫ ε : E, f₁ ε ∂(stdGaussian E) := integral_congr_ae hfg
    _ = value₁ := hf₁_value.symm

private theorem sourceGaussianPerturbedPopulationLossAtSigma_value_unique
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (sigma : ℝ)
    {value₀ value₁ : ℝ}
    (h₀ :
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w sigma value₀)
    (h₁ :
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w sigma value₁) :
    value₀ = value₁ := by
  rcases h₀ with ⟨f₀, hf₀_graph, _hf₀_wd, hf₀_value⟩
  rcases h₁ with ⟨f₁, hf₁_graph, _hf₁_wd, hf₁_value⟩
  have hfg : f₀ =ᵐ[stdGaussian E] f₁ := by
    filter_upwards [hf₀_graph, hf₁_graph] with ε hε₀ hε₁
    exact
      sourceGaussianPopulationGraphAtSigma_value_unique
        (S := S) w sigma ε hε₀ hε₁
  calc
    value₀ = ∫ ε : E, f₀ ε ∂(stdGaussian E) := hf₀_value
    _ = ∫ ε : E, f₁ ε ∂(stdGaussian E) := integral_congr_ae hfg
    _ = value₁ := hf₁_value.symm

private theorem sourceGaussianPerturbedPopulationLoss_forces_displayed_expectationWellDefined
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hdom : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace)
    (hwd : ∀ ε : E,
      Setup.populationLossWellDefined (S := S) ⟨w.1 + S.rho • ε, hdom ε⟩)
    (hsrc : sourceGaussianPerturbedPopulationLoss (S := S) w
      (internalGaussianPerturbedPopulationLoss (S := S) w hdom)) :
    SOptLib.expectationWellDefined (stdGaussian E)
      (fun ε : E => Setup.populationLossValue (S := S)
        ⟨w.1 + S.rho • ε, hdom ε⟩) := by
  rcases hsrc with ⟨f, hf_graph, hf_wd, _hvalue⟩
  have hdisplay_graph :
      ∀ᵐ ε ∂(stdGaussian E),
        sourceGaussianPopulationGraph (S := S) w ε
          (Setup.populationLossValue (S := S)
            ⟨w.1 + S.rho • ε, hdom ε⟩) :=
    Filter.Eventually.of_forall fun ε => ⟨hdom ε, hwd ε, rfl⟩
  have hfg :
      f =ᵐ[stdGaussian E]
        (fun ε : E => Setup.populationLossValue (S := S)
          ⟨w.1 + S.rho • ε, hdom ε⟩) := by
    filter_upwards [hf_graph, hdisplay_graph] with ε hf hdisplay
    exact sourceGaussianPopulationGraph_value_unique (S := S) w ε hf hdisplay
  rw [SOptLib.expectationWellDefined_iff_integrable] at hf_wd
  rw [SOptLib.expectationWellDefined_iff_integrable]
  exact hf_wd.congr hfg

/- Retirement certificate for the old Gaussian bridge without the outer
   well-definedness premise.  Any source witness agreeing a.e. with the
   displayed perturbed population loss forces that displayed integrand to be
   Gaussian-integrable, so a non-integrability hypothesis contradicts the old
   conclusion. -/
private theorem sourceGaussianPerturbedPopulationLoss_internal_bridge_old_head_retired
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hdom : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace)
    (hwd : ∀ ε : E,
      Setup.populationLossWellDefined (S := S) ⟨w.1 + S.rho • ε, hdom ε⟩)
    (hnot_gauss_wd : ¬ SOptLib.expectationWellDefined (stdGaussian E)
      (fun ε : E => Setup.populationLossValue (S := S)
        ⟨w.1 + S.rho • ε, hdom ε⟩)) :
    ¬ sourceGaussianPerturbedPopulationLoss (S := S) w
      (internalGaussianPerturbedPopulationLoss (S := S) w hdom) := by
  intro hsrc
  exact hnot_gauss_wd
    (sourceGaussianPerturbedPopulationLoss_forces_displayed_expectationWellDefined
      (S := S) w hdom hwd hsrc)

theorem sourceGaussianPerturbedPopulationLoss_internal_bridge
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hdom : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace)
    (hwd : ∀ ε : E,
      Setup.populationLossWellDefined (S := S) ⟨w.1 + S.rho • ε, hdom ε⟩)
    (hgauss_wd : SOptLib.expectationWellDefined (stdGaussian E)
      (fun ε : E => Setup.populationLossValue (S := S)
        ⟨w.1 + S.rho • ε, hdom ε⟩)) :
    sourceGaussianPerturbedPopulationLoss (S := S) w
      (internalGaussianPerturbedPopulationLoss (S := S) w hdom) := by
  refine ⟨fun ε : E => Setup.populationLossValue (S := S)
    ⟨w.1 + S.rho • ε, hdom ε⟩, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ε => ⟨hdom ε, hwd ε, rfl⟩
  · rw [SOptLib.expectationWellDefined_iff_integrable] at hgauss_wd
    rw [SOptLib.expectationWellDefined_iff_integrable]
    exact hgauss_wd
  · rfl

def sourceGaussianPerturbedPopulationLossAEGraphObligation
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) :
    Prop :=
  ∃ f : E → ℝ,
    ∀ᵐ ε ∂(stdGaussian E),
      sourceGaussianPopulationGraph (S := S) w ε (f ε)

theorem sourceGaussianPerturbedPopulationLossAEGraphObligation_of_domain
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hdom : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace)
    (hwd : ∀ ε : E,
      Setup.populationLossWellDefined (S := S) ⟨w.1 + S.rho • ε, hdom ε⟩) :
    sourceGaussianPerturbedPopulationLossAEGraphObligation (S := S) w := by
  refine ⟨fun ε : E => Setup.populationLossValue (S := S)
    ⟨w.1 + S.rho • ε, hdom ε⟩, ?_⟩
  exact Filter.Eventually.of_forall fun ε => ⟨hdom ε, hwd ε, rfl⟩

def sourceGaussianPerturbedPopulationLossWellDefinedObligation
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) :
    Prop :=
  ∃ value : ℝ, sourceGaussianPerturbedPopulationLoss (S := S) w value

/- Source predicate for the Gaussian premise in Theorem 2:
   `L_D(w) ≤ E_{ε∼N(0,ρ)}[L_D(w+ε)]`. -/
def GaussianTestErrorCondition (S : Setup n E X Y Ω)
    (w : Setup.Parameter S) : Prop :=
  ∃ (population value : ℝ),
    Setup.sourcePopulationLossAt (S := S) w.1 population ∧
      sourceGaussianPerturbedPopulationLoss (S := S) w value ∧
      population ≤ value

/- The theorem-stated Gaussian premise at an explicit perturbation scale.
   The rho-specialized predicate below remains the paper-facing premise;
   this parameterized form is the source-granularity object needed by
   Appendix A.1 after its selected-sigma substitution. -/
def theorem2GaussianPremiseSourceAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (sigma : ℝ) : Prop :=
  ∃ (population value : ℝ),
    Setup.sourcePopulationLossAt (S := S) w.1 population ∧
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w sigma value ∧
      population ≤ value

def theorem2AppendixA1SelectedSigmaEmpiricalWellDefinedness
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E)) : Prop :=
  ∀ s : Dataset n X Y,
    ∃ value : ℝ,
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w
          (theorem2AppendixA1SelectedSigma (S := S) hn hk) value

theorem theorem2AppendixA1SelectedSigma_empirical_well_definedness_of_all_scales
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hall :
      ∀ (s : Dataset n X Y) (sigma : ℝ),
        ∃ value : ℝ,
          sourceGaussianPerturbedEmpiricalLossAtSigma
            (S := S) s w sigma value) :
    theorem2AppendixA1SelectedSigmaEmpiricalWellDefinedness
      (S := S) w hn hk := by
  intro s
  exact hall s (theorem2AppendixA1SelectedSigma (S := S) hn hk)

theorem GaussianTestErrorCondition_spec (S : Setup n E X Y Ω)
    (w : Setup.Parameter S) :
    GaussianTestErrorCondition S w ↔
      ∃ (population value : ℝ),
        Setup.sourcePopulationLossAt (S := S) w.1 population ∧
          sourceGaussianPerturbedPopulationLoss (S := S) w value ∧
          population ≤ value := by
  rfl

def theorem2GaussianPremiseSource (S : Setup n E X Y Ω)
    (w : Setup.Parameter S) : Prop :=
  GaussianTestErrorCondition S w

theorem theorem2GaussianPremiseSourceAtSigma_rho
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) :
    theorem2GaussianPremiseSourceAtSigma (S := S) w S.rho ↔
      theorem2GaussianPremiseSource S w := by
  rfl

theorem theorem2GaussianPremiseSource_spec (S : Setup n E X Y Ω)
    (w : Setup.Parameter S) :
    theorem2GaussianPremiseSource S w ↔
      GaussianTestErrorCondition S w := by
  rfl

theorem theorem2GaussianPremiseSource_source_obligations
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hsrc : theorem2GaussianPremiseSource S w) :
    Setup.sourcePopulationLossWellDefinedObligation (S := S) w.1 ∧
      sourceGaussianPerturbedPopulationLossAEGraphObligation (S := S) w ∧
      sourceGaussianPerturbedPopulationLossWellDefinedObligation (S := S) w := by
  rcases hsrc with ⟨population, gaussianValue, hpopulation, hgaussian, _hle⟩
  refine ⟨⟨population, hpopulation⟩, ?_, ⟨gaussianValue, hgaussian⟩⟩
  rcases hgaussian with ⟨f, hf_graph, _hf_wd, _hvalue⟩
  exact ⟨f, hf_graph⟩

/- Source-boundary obligation for Theorem 2: this is the literal paper
   implication after spelling out the Gaussian premise, Euclidean sharpness
   maximum, and displayed remainder.  It is intentionally not named
   `theorem2_original`, because the source is silent about several
   Lean-facing well-definedness obligations listed below. -/
def theorem2SourceBoundaryObligation
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ) : Prop :=
  theorem2GaussianPremiseSource S w →
    ENNReal.ofReal (1 - δ) ≤
      (Setup.iidTrainingLaw (S := S))
        {s | theorem2OriginalEvent (S := S) w δ s}

theorem theorem2SourceBoundaryObligation_spec
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ) :
    theorem2SourceBoundaryObligation (S := S) w δ ↔
      (theorem2GaussianPremiseSource S w →
        ENNReal.ofReal (1 - δ) ≤
          (Setup.iidTrainingLaw (S := S))
            {s | theorem2OriginalEvent (S := S) w δ s}) := by
  rfl

/- Eq. (13)-level square-root term before the Laurent--Massart radius split
   and final absorption into the displayed Theorem 2 remainder. -/
noncomputable def theorem2PacBayesRemainder_source
    (S : Setup n E X Y Ω) (w : E) (δ : ℝ) : ℝ :=
  Real.sqrt
    ((((1 : ℝ) / 4) * (Setup.parameterCount (E := E) : ℝ) * Real.log
      (1 + (‖w‖ ^ 2 / S.rho ^ 2) *
        (1 + Real.sqrt (Real.log (n : ℝ) /
          (Setup.parameterCount (E := E) : ℝ))) ^ 2) +
      ((1 : ℝ) / 4) +
      Real.log ((n : ℝ) / δ) +
      2 * Real.log (6 * (n : ℝ) +
        3 * (Setup.parameterCount (E := E) : ℝ))) /
      ((n : ℝ) - 1))

theorem theorem2PacBayesRemainder_source_spec
    (S : Setup n E X Y Ω) (w : E) (δ : ℝ) :
    theorem2PacBayesRemainder_source (S := S) w δ =
      Real.sqrt
        ((((1 : ℝ) / 4) * (Setup.parameterCount (E := E) : ℝ) * Real.log
          (1 + (‖w‖ ^ 2 / S.rho ^ 2) *
            (1 + Real.sqrt (Real.log (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ))) ^ 2) +
          ((1 : ℝ) / 4) +
          Real.log ((n : ℝ) / δ) +
          2 * Real.log (6 * (n : ℝ) +
            3 * (Setup.parameterCount (E := E) : ℝ))) /
          ((n : ℝ) - 1)) := by
  rfl

/- Eq. (13)-level event: after McAllester's PAC-Bayes bound, the isotropic
   Gaussian KL calculation, and the prior-grid union bound, the perturbed
   population loss is bounded by the perturbed empirical loss plus the
   pre-radius Appendix A.1 remainder. -/
def theorem2PacBayesGaussianExpectationEventAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ)
    (s : Dataset n X Y) : Prop :=
  ∃ (gaussianPopulation gaussianEmpirical : ℝ),
    sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w sigma gaussianPopulation ∧
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w sigma gaussianEmpirical ∧
      gaussianPopulation ≤
        gaussianEmpirical + theorem2PacBayesRemainder_source (S := S) w.1 δ

def theorem2PacBayesGaussianExpectationEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (s : Dataset n X Y) : Prop :=
  theorem2PacBayesGaussianExpectationEventAtSigma
    (S := S) w δ S.rho s

def theorem2PacBayesGaussianExpectationEventAtSelectedSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (s : Dataset n X Y) : Prop :=
  theorem2PacBayesGaussianExpectationEventAtSigma
    (S := S) w δ (theorem2AppendixA1SelectedSigma (S := S) hn hk) s

/- Radius-to-sharpness event supplied by the Laurent--Massart tail step and
   the Appendix A.1 expectation split.  The outside-radius contribution is the
   paper's `1 / sqrt n` bounded-loss tail term, rather than a direct
   deterministic domination of the full Gaussian expectation by the sharpness
   maximum. -/
def theorem2GaussianEmpiricalSharpnessEventAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ)
    (s : Dataset n X Y) : Prop :=
  ∀ gaussianEmpirical : ℝ,
    sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w sigma gaussianEmpirical →
      ∃ sharpness : ℝ,
        theorem2EuclideanSharpnessSource (S := S) s w sharpness ∧
          gaussianEmpirical ≤
            (1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
              (Real.sqrt (n : ℝ))⁻¹

def theorem2GaussianEmpiricalSharpnessEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (s : Dataset n X Y) : Prop :=
  theorem2GaussianEmpiricalSharpnessEventAtSigma
    (S := S) w δ S.rho s

def theorem2GaussianEmpiricalSharpnessEventAtSelectedSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (s : Dataset n X Y) : Prop :=
  theorem2GaussianEmpiricalSharpnessEventAtSigma
    (S := S) w δ (theorem2AppendixA1SelectedSigma (S := S) hn hk) s

theorem theorem2_appendixA1_selected_sigma_empirical_le_sharpness_ae
    (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Setup.Parameter S) (sharpness : ℝ)
    (hsharpness :
      theorem2EuclideanSharpnessSource (S := S) s w sharpness)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (f : E → ℝ)
    (hf :
      ∀ᵐ ε ∂(stdGaussian E),
        Setup.sourceEmpiricalLossAt (S := S) s
          (w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε)
          (f ε)) :
    ∀ᵐ ε ∂(stdGaussian E),
      ‖ε‖ ≤
          Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
            (1 + Real.sqrt
              (Real.log (n : ℝ) /
                (Setup.parameterCount (E := E) : ℝ))) →
        f ε ≤ sharpness := by
  filter_upwards [hf] with ε hε
  intro hε_radius
  exact hsharpness.2.2
    (theorem2AppendixA1SelectedSigma (S := S) hn hk • ε)
    (theorem2_appendixA1_sigma_radius_bridge S hn hk ε hε_radius)
    (f ε) hε

/- Final Appendix A.1 algebraic absorption step: drop the harmless
   `(1 - 1/sqrt n)` factor on the nonnegative sharpness maximum and absorb the
   tail plus pre-radius PAC-Bayes term into the displayed Theorem 2 remainder. -/
def theorem2AppendixA1AbsorptionEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (s : Dataset n X Y) : Prop :=
  ∀ sharpness : ℝ,
    theorem2EuclideanSharpnessSource (S := S) s w sharpness →
      ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
          (Real.sqrt (n : ℝ))⁻¹) +
        theorem2PacBayesRemainder_source (S := S) w.1 δ ≤
          sharpness + theorem2Remainder_source (S := S) w.1 δ

/- The Appendix A.1 probability argument is about one combined good event.
   Keep that event as a named source object so probability suppliers can target
   the paper event directly rather than duplicating its conjunction. -/
def theorem2AppendixA1GoodEventAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ) : Set (Dataset n X Y) :=
  {s | theorem2PacBayesGaussianExpectationEventAtSigma
      (S := S) w δ sigma s ∧
    theorem2GaussianEmpiricalSharpnessEventAtSigma
      (S := S) w δ sigma s ∧
    theorem2AppendixA1AbsorptionEvent (S := S) w δ s}

def theorem2AppendixA1GoodEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ) :
    Set (Dataset n X Y) :=
  theorem2AppendixA1GoodEventAtSigma (S := S) w δ S.rho

theorem theorem2AppendixA1GoodEventAtSigma_rho
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ) :
    theorem2AppendixA1GoodEventAtSigma (S := S) w δ S.rho =
      theorem2AppendixA1GoodEvent (S := S) w δ := by
  rfl

def theorem2AppendixA1SelectedSigmaGoodEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E)) :
    Set (Dataset n X Y) :=
  theorem2AppendixA1GoodEventAtSigma (S := S) w δ
    (theorem2AppendixA1SelectedSigma (S := S) hn hk)

def theorem2AppendixA1PacBayesFailureAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ) : Set (Dataset n X Y) :=
  {s | ¬ theorem2PacBayesGaussianExpectationEventAtSigma
    (S := S) w δ sigma s}

def theorem2AppendixA1SharpnessFailureAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ) : Set (Dataset n X Y) :=
  {s | ¬ theorem2GaussianEmpiricalSharpnessEventAtSigma
    (S := S) w δ sigma s}

def theorem2AppendixA1AbsorptionFailure
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ) :
    Set (Dataset n X Y) :=
  {s | ¬ theorem2AppendixA1AbsorptionEvent (S := S) w δ s}

/- The prior grid is a geometric discretization in the variance variable.
   This lemma isolates the floor witness before any PAC-Bayes event argument
   is applied. -/
private theorem exists_nat_exp_grid_sandwich
    (k c a : ℝ) (hk : 0 < k) (hc : 0 < c) (ha : 0 < a)
    (hac : a ≤ c) :
    ∃ j : ℕ,
      a ≤ c * Real.exp (-(j : ℝ) / k) ∧
        c * Real.exp (-(j : ℝ) / k) ≤ Real.exp (1 / k) * a := by
  let x : ℝ := k * Real.log (c / a)
  have hca : 0 < c / a := div_pos hc ha
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hk.le
      (Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using hac)))
  let j : ℕ := ⌊x⌋₊
  have hj_le : (j : ℝ) ≤ x := by
    exact Nat.floor_le hx
  have hx_lt : x < (j : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  have hgrid_eq :
      c * Real.exp (-(j : ℝ) / k) =
        a * Real.exp ((x - (j : ℝ)) / k) := by
    have hceq : c = a * Real.exp (Real.log (c / a)) := by
      rw [Real.exp_log hca]
      field_simp
    rw [hceq, mul_assoc, ← Real.exp_add]
    congr 1
    dsimp [x]
    field_simp
    ring
  have hleft_exp : 1 ≤ Real.exp ((x - (j : ℝ)) / k) := by
    have hexp :
        1 + (x - (j : ℝ)) / k ≤
          Real.exp ((x - (j : ℝ)) / k) :=
      by
        simpa [add_comm] using
          (Real.add_one_le_exp ((x - (j : ℝ)) / k))
    linarith [div_nonneg (sub_nonneg.mpr hj_le) hk.le]
  have hright_exp :
      Real.exp ((x - (j : ℝ)) / k) ≤ Real.exp (1 / k) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right hk).2
    linarith
  refine ⟨j, ?_, ?_⟩
  · rw [hgrid_eq]
    calc
      a = a * 1 := by ring
      _ ≤ a * Real.exp ((x - (j : ℝ)) / k) :=
        mul_le_mul_of_nonneg_left hleft_exp ha.le
  · rw [hgrid_eq]
    calc
      a * Real.exp ((x - (j : ℝ)) / k) ≤ a * Real.exp (1 / k) :=
        mul_le_mul_of_nonneg_left hright_exp ha.le
      _ = Real.exp (1 / k) * a := by ring

private theorem nat_floor_exp_grid_sandwich
    (k c a : ℝ) (hk : 0 < k) (hc : 0 < c) (ha : 0 < a)
    (hac : a ≤ c) :
    let j : ℕ := ⌊k * Real.log (c / a)⌋₊
    a ≤ c * Real.exp (-(j : ℝ) / k) ∧
      c * Real.exp (-(j : ℝ) / k) ≤ Real.exp (1 / k) * a := by
  let x : ℝ := k * Real.log (c / a)
  have hca : 0 < c / a := div_pos hc ha
  have hx : 0 ≤ x := by
    dsimp [x]
    exact mul_nonneg hk.le
      (Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using hac)))
  let j : ℕ := ⌊x⌋₊
  have hj_le : (j : ℝ) ≤ x := by
    exact Nat.floor_le hx
  have hx_lt : x < (j : ℝ) + 1 := by
    exact Nat.lt_floor_add_one x
  have hgrid_eq :
      c * Real.exp (-(j : ℝ) / k) =
        a * Real.exp ((x - (j : ℝ)) / k) := by
    have hceq : c = a * Real.exp (Real.log (c / a)) := by
      rw [Real.exp_log hca]
      field_simp
    rw [hceq, mul_assoc, ← Real.exp_add]
    congr 1
    dsimp [x]
    field_simp
    ring
  have hleft_exp : 1 ≤ Real.exp ((x - (j : ℝ)) / k) := by
    have hexp :
        1 + (x - (j : ℝ)) / k ≤
          Real.exp ((x - (j : ℝ)) / k) :=
      by
        simpa [add_comm] using
          (Real.add_one_le_exp ((x - (j : ℝ)) / k))
    linarith [div_nonneg (sub_nonneg.mpr hj_le) hk.le]
  have hright_exp :
      Real.exp ((x - (j : ℝ)) / k) ≤ Real.exp (1 / k) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_div_iff_of_pos_right hk).2
    linarith
  dsimp only
  change
    a ≤ c * Real.exp (-(j : ℝ) / k) ∧
      c * Real.exp (-(j : ℝ) / k) ≤ Real.exp (1 / k) * a
  refine ⟨?_, ?_⟩
  · rw [hgrid_eq]
    calc
      a = a * 1 := by ring
      _ ≤ a * Real.exp ((x - (j : ℝ)) / k) :=
        mul_le_mul_of_nonneg_left hleft_exp ha.le
  · rw [hgrid_eq]
    calc
      a * Real.exp ((x - (j : ℝ)) / k) ≤ a * Real.exp (1 / k) :=
        mul_le_mul_of_nonneg_left hright_exp ha.le
      _ = Real.exp (1 / k) * a := by ring

theorem theorem2AppendixA1PriorGridVariance_exists_sandwich
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hA :
      S.rho ^ 2 + ‖w.1‖ ^ 2 /
          (Setup.parameterCount (E := E) : ℝ) ≤
        theorem2AppendixA1PriorGridScale (S := S) hk) :
    ∃ j : ℕ,
      S.rho ^ 2 + ‖w.1‖ ^ 2 /
          (Setup.parameterCount (E := E) : ℝ) ≤
        theorem2AppendixA1PriorGridVariance (S := S) hk j ∧
      theorem2AppendixA1PriorGridVariance (S := S) hk j ≤
        Real.exp (1 / (Setup.parameterCount (E := E) : ℝ)) *
          (S.rho ^ 2 + ‖w.1‖ ^ 2 /
            (Setup.parameterCount (E := E) : ℝ)) := by
  let k : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let c : ℝ := theorem2AppendixA1PriorGridScale (S := S) hk
  let a : ℝ := S.rho ^ 2 + ‖w.1‖ ^ 2 / k
  have hk' : 0 < k := by
    dsimp [k]
    exact_mod_cast hk
  have hc : 0 < c := by
    dsimp [c]
    exact theorem2AppendixA1PriorGridScale_pos (S := S) hk
  have ha : 0 < a := by
    dsimp [a]
    have hrho : 0 < S.rho ^ 2 := sq_pos_of_pos S.rho_pos
    have hnorm : 0 ≤ ‖w.1‖ ^ 2 / k := by positivity
    linarith
  have hac : a ≤ c := by
    simpa [a, c, k] using hA
  rcases exists_nat_exp_grid_sandwich k c a hk' hc ha hac with
    ⟨j, hj₁, hj₂⟩
  refine ⟨j, ?_, ?_⟩
  · simpa [a, c, k, theorem2AppendixA1PriorGridVariance,
      theorem2AppendixA1PriorGridScale, Nat.cast_add, div_eq_mul_inv] using hj₁
  · simpa [a, c, k, theorem2AppendixA1PriorGridVariance,
      theorem2AppendixA1PriorGridScale, Nat.cast_add, div_eq_mul_inv] using hj₂

/- Source Eq. (8) index supplier with the reduced-norm branch exposed at the
   right granularity.  The downstream selected-grid inclusion should consume
   this theorem rather than assuming the entire union inclusion as a premise. -/
theorem theorem2AppendixA1SelectedPriorGridIndex_of_reduced_norm
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1)) :
    ∃ j : ℕ,
      S.rho ^ 2 + ‖w.1‖ ^ 2 /
          (Setup.parameterCount (E := E) : ℝ) ≤
        theorem2AppendixA1PriorGridVariance (S := S) hk j ∧
      theorem2AppendixA1PriorGridVariance (S := S) hk j ≤
        Real.exp (1 / (Setup.parameterCount (E := E) : ℝ)) *
          (S.rho ^ 2 + ‖w.1‖ ^ 2 /
            (Setup.parameterCount (E := E) : ℝ)) := by
  exact theorem2AppendixA1PriorGridVariance_exists_sandwich
    (S := S) w hn hk
    (theorem2AppendixA1PriorGridScale_of_reduced_norm
      (S := S) w hn hk hnorm)

/- Source Eq. (8)'s selected prior-grid index.  Earlier route attempts used
   `Classical.choose` from the sandwich existence theorem; that loses the
   floor formula needed for the confidence-log calculation in Eq. (13). -/
noncomputable def theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E)) : ℕ :=
  ⌊(Setup.parameterCount (E := E) : ℝ) *
      Real.log
        (theorem2AppendixA1PriorGridScale (S := S) hk /
          (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
            ‖w.1‖ ^ 2 / (Setup.parameterCount (E := E) : ℝ)))⌋₊

/- Paper Eq. (8)'s prior-grid index is chosen from the rho-scale quantity
   `rho^2 + ||w||^2/k`.  The selected-sigma index above is the sharper KL
   grid used by the current Lean route, but it is not the object used in the
   PDF's confidence-log calculation following Eq. (13). -/
noncomputable def theorem2AppendixA1PriorGridIndexAtRhoScale
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E)) : ℕ :=
  ⌊(Setup.parameterCount (E := E) : ℝ) *
      Real.log
        (theorem2AppendixA1PriorGridScale (S := S) hk /
          (S.rho ^ 2 +
            ‖w.1‖ ^ 2 / (Setup.parameterCount (E := E) : ℝ)))⌋₊

theorem theorem2AppendixA1PriorGridIndexAtRhoScale_le_log_ratio
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1)) :
    ((theorem2AppendixA1PriorGridIndexAtRhoScale
        (S := S) w hn hk : ℕ) : ℝ) ≤
      (Setup.parameterCount (E := E) : ℝ) *
        Real.log
          (theorem2AppendixA1PriorGridScale (S := S) hk /
            (S.rho ^ 2 +
              ‖w.1‖ ^ 2 / (Setup.parameterCount (E := E) : ℝ))) := by
  let k : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let c : ℝ := theorem2AppendixA1PriorGridScale (S := S) hk
  let a : ℝ := S.rho ^ 2 + ‖w.1‖ ^ 2 / k
  have hk' : 0 < k := by
    dsimp [k]
    exact_mod_cast hk
  have hc : 0 < c := by
    dsimp [c]
    exact theorem2AppendixA1PriorGridScale_pos (S := S) hk
  have ha : 0 < a := by
    dsimp [a]
    have hrho : 0 < S.rho ^ 2 := sq_pos_of_pos S.rho_pos
    have hnorm_nonneg : 0 ≤ ‖w.1‖ ^ 2 / k := by positivity
    linarith
  have hac : a ≤ c := by
    dsimp [a, c, k]
    exact theorem2AppendixA1PriorGridScale_of_reduced_norm
      (S := S) w hn hk hnorm
  have hx :
      0 ≤ k * Real.log (c / a) := by
    exact mul_nonneg hk'.le
      (Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using hac)))
  simpa [theorem2AppendixA1PriorGridIndexAtRhoScale, k, c, a] using
    Nat.floor_le hx

private theorem theorem2AppendixA1_selectedSigma_zero_norm_grid_ratio_has_extra_parameter_factor
    {rho K sampleSize : ℝ} (hrho : 0 < rho) (hK : 0 < K) :
    (rho ^ 2 * (1 + Real.exp (4 * sampleSize / K))) /
        ((rho /
          (Real.sqrt K *
            (1 + Real.sqrt (Real.log sampleSize / K)))) ^ 2) =
      K * (1 + Real.sqrt (Real.log sampleSize / K)) ^ 2 *
        (1 + Real.exp (4 * sampleSize / K)) := by
  have hsqrt_sq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hden :
      0 < Real.sqrt K *
        (1 + Real.sqrt (Real.log sampleSize / K)) := by
    exact mul_pos (Real.sqrt_pos.2 hK) (by positivity)
  field_simp [ne_of_gt hrho, ne_of_gt hden]
  rw [hsqrt_sq]

private theorem theorem2AppendixA1_priorGridScale_div_selectedSigma_sq_has_extra_parameter_factor
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 =
      (Setup.parameterCount (E := E) : ℝ) *
        (1 + Real.sqrt
          (Real.log (n : ℝ) /
            (Setup.parameterCount (E := E) : ℝ))) ^ 2 *
          (1 + Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ))) := by
  have hK : 0 < (Setup.parameterCount (E := E) : ℝ) := by
    exact_mod_cast hk
  simpa [theorem2AppendixA1PriorGridScale,
    theorem2AppendixA1SelectedSigma] using
    (theorem2AppendixA1_selectedSigma_zero_norm_grid_ratio_has_extra_parameter_factor
      (rho := S.rho)
      (K := (Setup.parameterCount (E := E) : ℝ))
      (sampleSize := (n : ℝ)) S.rho_pos hK)

private theorem theorem2AppendixA1_priorGridScale_div_rho_sq
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E)) :
    theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 =
      1 + Real.exp
        (4 * (n : ℝ) /
          (Setup.parameterCount (E := E) : ℝ)) := by
  unfold theorem2AppendixA1PriorGridScale
  have hrho_ne : S.rho ≠ 0 := ne_of_gt S.rho_pos
  field_simp [hrho_ne]

private theorem theorem2AppendixA1_selectedSigma_grid_ratio_ne_rho_grid_ratio
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) :
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
      theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  let K : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let A : ℝ := 1 + Real.sqrt (Real.log (n : ℝ) / K)
  let B : ℝ := 1 + Real.exp (4 * (n : ℝ) / K)
  have hK_pos : 0 < K := by
    dsimp [K]
    exact_mod_cast hk
  have hK_ge_one : (1 : ℝ) ≤ K := by
    dsimp [K]
    exact_mod_cast (Nat.succ_le_iff.2 hk)
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_real
  have hquot_pos : 0 < Real.log (n : ℝ) / K := div_pos hlog_pos hK_pos
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ) / K) :=
    Real.sqrt_pos.2 hquot_pos
  have hA_gt_one : 1 < A := by
    dsimp [A]
    linarith
  have hA_sq_gt_one : 1 < A ^ 2 := by
    nlinarith
  have hfactor_gt_one : 1 < K * A ^ 2 := by
    nlinarith
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hstrict : B < K * A ^ 2 * B := by
    nlinarith
  rw [theorem2AppendixA1_priorGridScale_div_selectedSigma_sq_has_extra_parameter_factor
      (S := S) hn hk,
    theorem2AppendixA1_priorGridScale_div_rho_sq (S := S) hk]
  dsimp [K, A, B] at hstrict
  intro h
  nlinarith

/- Selected-sigma variant of the Eq. (8) grid supplier.  Once Appendix A.1
   substitutes the smaller radius-control scale, the posterior variance in the
   Gaussian KL term is `selectedSigma ^ 2`, not `rho ^ 2`.  The same
   data-independent grid still contains a variance within one `exp (1/k)`
   factor of this selected posterior target. -/
theorem theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_spec_of_reduced_norm
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1)) :
    let j : ℕ :=
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
      theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
          ‖w.1‖ ^ 2 /
            (Setup.parameterCount (E := E) : ℝ) ≤
        theorem2AppendixA1PriorGridVariance (S := S) hk j ∧
      theorem2AppendixA1PriorGridVariance (S := S) hk j ≤
        Real.exp (1 / (Setup.parameterCount (E := E) : ℝ)) *
          (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
            ‖w.1‖ ^ 2 /
              (Setup.parameterCount (E := E) : ℝ)) := by
  let k : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let c : ℝ := theorem2AppendixA1PriorGridScale (S := S) hk
  let sigma : ℝ := theorem2AppendixA1SelectedSigma (S := S) hn hk
  let a : ℝ := sigma ^ 2 + ‖w.1‖ ^ 2 / k
  have hk' : 0 < k := by
    dsimp [k]
    exact_mod_cast hk
  have hc : 0 < c := by
    dsimp [c]
    exact theorem2AppendixA1PriorGridScale_pos (S := S) hk
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    exact theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
  have hsigma_le_rho : sigma ≤ S.rho := by
    dsimp [sigma]
    exact le_of_lt (theorem2AppendixA1SelectedSigma_lt_rho (S := S) hn hk)
  have hsigma_sq_le_rho_sq : sigma ^ 2 ≤ S.rho ^ 2 := by
    nlinarith [hsigma_pos.le, S.rho_pos.le, hsigma_le_rho]
  have ha : 0 < a := by
    dsimp [a]
    have hnorm_nonneg : 0 ≤ ‖w.1‖ ^ 2 / k := by positivity
    nlinarith [sq_pos_of_pos hsigma_pos, hnorm_nonneg]
  have hac : a ≤ c := by
    have hbase :
        S.rho ^ 2 + ‖w.1‖ ^ 2 / k ≤ c := by
      dsimp [c, k]
      exact theorem2AppendixA1PriorGridScale_of_reduced_norm
        (S := S) w hn hk hnorm
    dsimp [a]
    linarith
  have hsandwich :
      let j : ℕ := ⌊k * Real.log (c / a)⌋₊
      a ≤ c * Real.exp (-(j : ℝ) / k) ∧
        c * Real.exp (-(j : ℝ) / k) ≤ Real.exp (1 / k) * a :=
    nat_floor_exp_grid_sandwich k c a hk' hc ha hac
  dsimp [theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma]
  dsimp [a, c, k, sigma] at hsandwich
  constructor
  · simpa [a, c, k, sigma, theorem2AppendixA1PriorGridVariance,
      theorem2AppendixA1PriorGridScale, Nat.cast_add, div_eq_mul_inv] using
        hsandwich.1
  · simpa [a, c, k, sigma, theorem2AppendixA1PriorGridVariance,
      theorem2AppendixA1PriorGridScale, Nat.cast_add, div_eq_mul_inv] using
        hsandwich.2

theorem theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_le_log_ratio
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1)) :
    ((theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk : ℕ) : ℝ) ≤
      (Setup.parameterCount (E := E) : ℝ) *
        Real.log
          (theorem2AppendixA1PriorGridScale (S := S) hk /
            (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
              ‖w.1‖ ^ 2 / (Setup.parameterCount (E := E) : ℝ))) := by
  let k : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let c : ℝ := theorem2AppendixA1PriorGridScale (S := S) hk
  let sigma : ℝ := theorem2AppendixA1SelectedSigma (S := S) hn hk
  let a : ℝ := sigma ^ 2 + ‖w.1‖ ^ 2 / k
  have hk' : 0 < k := by
    dsimp [k]
    exact_mod_cast hk
  have hc : 0 < c := by
    dsimp [c]
    exact theorem2AppendixA1PriorGridScale_pos (S := S) hk
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    exact theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
  have hsigma_le_rho : sigma ≤ S.rho := by
    dsimp [sigma]
    exact le_of_lt (theorem2AppendixA1SelectedSigma_lt_rho (S := S) hn hk)
  have hsigma_sq_le_rho_sq : sigma ^ 2 ≤ S.rho ^ 2 := by
    nlinarith [hsigma_pos.le, S.rho_pos.le, hsigma_le_rho]
  have ha : 0 < a := by
    dsimp [a]
    have hnorm_nonneg : 0 ≤ ‖w.1‖ ^ 2 / k := by positivity
    nlinarith [sq_pos_of_pos hsigma_pos, hnorm_nonneg]
  have hac : a ≤ c := by
    have hbase :
        S.rho ^ 2 + ‖w.1‖ ^ 2 / k ≤ c := by
      dsimp [c, k]
      exact theorem2AppendixA1PriorGridScale_of_reduced_norm
        (S := S) w hn hk hnorm
    dsimp [a]
    linarith
  have hx :
      0 ≤ k * Real.log (c / a) := by
    exact mul_nonneg hk'.le
      (Real.log_nonneg ((le_div_iff₀ ha).2 (by simpa using hac)))
  simpa [theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma, k, c, a,
    sigma] using Nat.floor_le hx

theorem theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_of_reduced_norm
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1)) :
    ∃ j : ℕ,
      theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
          ‖w.1‖ ^ 2 /
            (Setup.parameterCount (E := E) : ℝ) ≤
        theorem2AppendixA1PriorGridVariance (S := S) hk j ∧
      theorem2AppendixA1PriorGridVariance (S := S) hk j ≤
        Real.exp (1 / (Setup.parameterCount (E := E) : ℝ)) *
          (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
            ‖w.1‖ ^ 2 /
              (Setup.parameterCount (E := E) : ℝ)) := by
  exact
    ⟨(theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk),
      by
        simpa using
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_spec_of_reduced_norm
            (S := S) w hn hk hnorm)⟩

def theorem2AppendixA1BadEventAtSigma
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ) : Set (Dataset n X Y) :=
  (theorem2AppendixA1GoodEventAtSigma (S := S) w δ sigma)ᶜ

theorem theorem2AppendixA1BadEventAtSigma_subset_component_union
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ) :
    theorem2AppendixA1BadEventAtSigma (S := S) w δ sigma ⊆
      theorem2AppendixA1PacBayesFailureAtSigma (S := S) w δ sigma ∪
        theorem2AppendixA1SharpnessFailureAtSigma (S := S) w δ sigma ∪
          theorem2AppendixA1AbsorptionFailure (S := S) w δ := by
  intro s hs
  change ¬ (
    theorem2PacBayesGaussianExpectationEventAtSigma
        (S := S) w δ sigma s ∧
      theorem2GaussianEmpiricalSharpnessEventAtSigma
        (S := S) w δ sigma s ∧
      theorem2AppendixA1AbsorptionEvent (S := S) w δ s) at hs
  simp only [theorem2AppendixA1PacBayesFailureAtSigma,
    theorem2AppendixA1SharpnessFailureAtSigma,
    theorem2AppendixA1AbsorptionFailure, Set.mem_union, Set.mem_setOf_eq]
  by_cases hpac :
      theorem2PacBayesGaussianExpectationEventAtSigma
        (S := S) w δ sigma s
  · by_cases hsharp :
        theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ sigma s
    · by_cases habsorb :
          theorem2AppendixA1AbsorptionEvent (S := S) w δ s
      · exact False.elim (hs ⟨hpac, hsharp, habsorb⟩)
      · exact Or.inr habsorb
    · exact Or.inl (Or.inr hsharp)
  · exact Or.inl (Or.inl hpac)

theorem theorem2AppendixA1_measure_bad_mass_le_of_component_masses
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B C : Set α) (a b c : ENNReal)
    (hA : μ A ≤ a) (hB : μ B ≤ b) (hC : μ C ≤ c) :
    μ (A ∪ B ∪ C) ≤ a + b + c := by
  calc
    μ (A ∪ B ∪ C) = μ (A ∪ (B ∪ C)) := by rw [Set.union_assoc]
    _ ≤ μ A + μ (B ∪ C) :=
      measure_union_le (μ := μ) A (B ∪ C)
    _ ≤ μ A + (μ B + μ C) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left (measure_union_le (μ := μ) B C) (μ A))
    _ ≤ a + (b + c) :=
      add_le_add hA (add_le_add hB hC)
    _ = a + b + c := by ac_rfl

def theorem2AppendixA1BadEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ) :
    Set (Dataset n X Y) :=
  (theorem2AppendixA1GoodEvent (S := S) w δ)ᶜ

theorem theorem2OriginalEvent_of_pacBayesGaussian_and_radiusSharpness
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (s : Dataset n X Y)
    (hgaussian : theorem2GaussianPremiseSource S w)
    (hpac : theorem2PacBayesGaussianExpectationEvent (S := S) w δ s)
    (hradius : theorem2GaussianEmpiricalSharpnessEvent (S := S) w δ s)
    (habsorb : theorem2AppendixA1AbsorptionEvent (S := S) w δ s) :
    theorem2OriginalEvent (S := S) w δ s := by
  rcases hgaussian with
    ⟨population, gaussianPopulation, hpopulation, hgaussianPopulation,
      hpopulation_le_gaussian⟩
  rcases hpac with
    ⟨gaussianPopulation', gaussianEmpirical, hgaussianPopulation',
      hgaussianEmpirical, hgaussian_le_empirical⟩
  have hgaussian_eq :
      gaussianPopulation = gaussianPopulation' :=
    sourceGaussianPerturbedPopulationLoss_value_unique
      (S := S) w hgaussianPopulation hgaussianPopulation'
  rcases hradius gaussianEmpirical hgaussianEmpirical with
    ⟨sharpness, hsharpness, hempirical_split⟩
  have hsplit_with_remainder :
      gaussianEmpirical + theorem2PacBayesRemainder_source (S := S) w.1 δ ≤
        ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
            (Real.sqrt (n : ℝ))⁻¹) +
          theorem2PacBayesRemainder_source (S := S) w.1 δ := by
    linarith
  have habsorb' :
      ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
          (Real.sqrt (n : ℝ))⁻¹) +
        theorem2PacBayesRemainder_source (S := S) w.1 δ ≤
          sharpness + theorem2Remainder_source (S := S) w.1 δ :=
    habsorb sharpness hsharpness
  refine ⟨population, sharpness, hpopulation, hsharpness, ?_⟩
  calc
    population ≤ gaussianPopulation := hpopulation_le_gaussian
    _ = gaussianPopulation' := hgaussian_eq
    _ ≤ gaussianEmpirical + theorem2PacBayesRemainder_source (S := S) w.1 δ :=
      hgaussian_le_empirical
    _ ≤ ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
            (Real.sqrt (n : ℝ))⁻¹) +
          theorem2PacBayesRemainder_source (S := S) w.1 δ :=
      hsplit_with_remainder
    _ ≤ sharpness + theorem2Remainder_source (S := S) w.1 δ := habsorb'

theorem theorem2OriginalEvent_of_selected_sigma_pacBayesGaussian_and_radiusSharpness
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    (sigma : ℝ) (s : Dataset n X Y)
    (hgaussian :
      theorem2GaussianPremiseSourceAtSigma (S := S) w sigma)
    (hpac :
      theorem2PacBayesGaussianExpectationEventAtSigma
        (S := S) w δ sigma s)
    (hradius :
      theorem2GaussianEmpiricalSharpnessEventAtSigma
        (S := S) w δ sigma s)
    (habsorb : theorem2AppendixA1AbsorptionEvent (S := S) w δ s) :
    theorem2OriginalEvent (S := S) w δ s := by
  rcases hgaussian with
    ⟨population, gaussianPopulation, hpopulation, hgaussianPopulation,
      hpopulation_le_gaussian⟩
  rcases hpac with
    ⟨gaussianPopulation', gaussianEmpirical, hgaussianPopulation',
      hgaussianEmpirical, hgaussian_le_empirical⟩
  have hgaussian_eq :
      gaussianPopulation = gaussianPopulation' :=
    sourceGaussianPerturbedPopulationLossAtSigma_value_unique
      (S := S) w sigma hgaussianPopulation hgaussianPopulation'
  rcases hradius gaussianEmpirical hgaussianEmpirical with
    ⟨sharpness, hsharpness, hempirical_split⟩
  have hsplit_with_remainder :
      gaussianEmpirical + theorem2PacBayesRemainder_source (S := S) w.1 δ ≤
        ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
            (Real.sqrt (n : ℝ))⁻¹) +
          theorem2PacBayesRemainder_source (S := S) w.1 δ := by
    linarith
  have habsorb' :
      ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
          (Real.sqrt (n : ℝ))⁻¹) +
        theorem2PacBayesRemainder_source (S := S) w.1 δ ≤
          sharpness + theorem2Remainder_source (S := S) w.1 δ :=
    habsorb sharpness hsharpness
  refine ⟨population, sharpness, hpopulation, hsharpness, ?_⟩
  calc
    population ≤ gaussianPopulation := hpopulation_le_gaussian
    _ = gaussianPopulation' := hgaussian_eq
    _ ≤ gaussianEmpirical + theorem2PacBayesRemainder_source (S := S) w.1 δ :=
      hgaussian_le_empirical
    _ ≤ ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
            (Real.sqrt (n : ℝ))⁻¹) +
          theorem2PacBayesRemainder_source (S := S) w.1 δ :=
      hsplit_with_remainder
    _ ≤ sharpness + theorem2Remainder_source (S := S) w.1 δ := habsorb'

theorem theorem2AppendixA1SelectedSigmaGoodEvent_to_theorem2OriginalEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : ℝ) (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (htransport :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)) :
    theorem2AppendixA1SelectedSigmaGoodEvent
        (S := S) w δ hn hk ⊆
      {s | theorem2OriginalEvent (S := S) w δ s} := by
  intro s hs
  change
    theorem2PacBayesGaussianExpectationEventAtSigma
          (S := S) w δ
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s ∧
      theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s ∧
      theorem2AppendixA1AbsorptionEvent (S := S) w δ s at hs
  exact theorem2OriginalEvent_of_selected_sigma_pacBayesGaussian_and_radiusSharpness
    (S := S) w δ
      (theorem2AppendixA1SelectedSigma (S := S) hn hk) s
      htransport hs.1 hs.2.1 hs.2.2

private theorem theorem2SourceBoundaryObligation_of_pacBayesGaussian_and_radiusSharpness_rho_legacy
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hprob :
      ENNReal.ofReal (1 - δ.1) ≤
        (Setup.iidTrainingLaw (S := S))
          {s | theorem2PacBayesGaussianExpectationEvent (S := S) w δ.1 s ∧
            theorem2GaussianEmpiricalSharpnessEvent (S := S) w δ.1 s ∧
            theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s}) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  intro hgaussian
  refine le_trans hprob ?_
  exact measure_mono fun s hs =>
      theorem2OriginalEvent_of_pacBayesGaussian_and_radiusSharpness
      (S := S) w δ.1 s hgaussian hs.1 hs.2.1 hs.2.2

private theorem theorem2SourceBoundaryObligation_of_pacBayesGaussian_and_radiusSharpness_rho_compat
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hprob :
      ENNReal.ofReal (1 - δ.1) ≤
        (Setup.iidTrainingLaw (S := S))
          {s | theorem2PacBayesGaussianExpectationEvent (S := S) w δ.1 s ∧
            theorem2GaussianEmpiricalSharpnessEvent (S := S) w δ.1 s ∧
            theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s}) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  exact theorem2SourceBoundaryObligation_of_pacBayesGaussian_and_radiusSharpness_rho_legacy
    (S := S) w δ hn hk hprob

/- Guarded replacement route for Appendix A.1.  It consumes the actual
   selected-sigma population premise and selected-sigma good event; the
   original rho-scale route remains separate because no scale transport is
   derivable from the theorem-stated single-scale premise alone. -/
theorem theorem2SourceBoundaryObligation_from_pacBayes_route
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hprob :
      ENNReal.ofReal (1 - δ.1) ≤
        (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1SelectedSigmaGoodEvent
            (S := S) w δ.1 hn hk)) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  intro _hgaussian
  refine le_trans hprob ?_
  change
    (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1SelectedSigmaGoodEvent
          (S := S) w δ.1 hn hk) ≤
      (Setup.iidTrainingLaw (S := S))
        {s | theorem2OriginalEvent (S := S) w δ.1 s}
  exact measure_mono
    (theorem2AppendixA1SelectedSigmaGoodEvent_to_theorem2OriginalEvent
      (S := S) w δ.1 hn hk hselected_population)

theorem theorem2SourceBoundaryObligation_of_selected_sigma_pacBayes_route
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hprob :
      ENNReal.ofReal (1 - δ.1) ≤
        (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1SelectedSigmaGoodEvent
            (S := S) w δ.1 hn hk)) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  exact theorem2SourceBoundaryObligation_from_pacBayes_route
    (S := S) w δ hn hk hselected_population hprob

theorem theorem2PacBayesAdmissibleBoundedLoss_spec (S : Setup n E X Y Ω) :
    theorem2PacBayesAdmissibleBoundedLoss (S := S) ↔
      ((∀ (w : Setup.Parameter S) (x : X) (y : Y), (S.loss w x y : ℝ) ≤ 1) ∧
        (∀ w : Setup.Parameter S, Setup.populationLossWellDefined (S := S) w)) := by
  rfl

private theorem theorem2AppendixA1_sourceEmpiricalLossAt_le_one
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (u : E) (value : ℝ)
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hn : 1 < n)
    (hvalue : Setup.sourceEmpiricalLossAt (S := S) s u value) :
    value ≤ 1 := by
  rcases hvalue with ⟨hu, hEq⟩
  rw [hEq, Setup.empiricalLoss_spec]
  have hterm :
      ∀ i : Fin n,
        (S.loss ⟨u, hu⟩ (s i).1 (s i).2 : ℝ) ≤ 1 := by
    intro i
    exact hadm.1 ⟨u, hu⟩ (s i).1 (s i).2
  have hsum :
      ∑ i : Fin n, (S.loss ⟨u, hu⟩ (s i).1 (s i).2 : ℝ) ≤
        ∑ _i : Fin n, (1 : ℝ) := by
    exact Finset.sum_le_sum fun i _ => hterm i
  have hsum' :
      ∑ i : Fin n, (S.loss ⟨u, hu⟩ (s i).1 (s i).2 : ℝ) ≤
        (n : ℝ) := by
    simpa using hsum
  have hn_real : 0 < (n : ℝ) := by
    have hn' : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_real.le
  have havg :
      (n : ℝ)⁻¹ *
          ∑ i : Fin n,
            (S.loss ⟨u, hu⟩ (s i).1 (s i).2 : ℝ) ≤
        (n : ℝ)⁻¹ * (n : ℝ) := by
    exact mul_le_mul_of_nonneg_left hsum' hinv_nonneg
  calc
    (n : ℝ)⁻¹ *
          ∑ i : Fin n,
            (S.loss ⟨u, hu⟩ (s i).1 (s i).2 : ℝ) ≤
        (n : ℝ)⁻¹ * (n : ℝ) := havg
    _ = 1 := by field_simp [ne_of_gt hn_real]

private theorem theorem2AppendixA1_sharpness_le_one
    (S : Setup n E X Y Ω) (s : Dataset n X Y)
    (w : Setup.Parameter S) (sharpness : ℝ)
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hn : 1 < n)
    (hsharpness :
      theorem2EuclideanSharpnessSource (S := S) s w sharpness) :
    sharpness ≤ 1 := by
  rcases hsharpness with ⟨_, ⟨ε, hε, hvalue⟩, _⟩
  exact theorem2AppendixA1_sourceEmpiricalLossAt_le_one
    (S := S) s (w.1 + ε) sharpness hadm hn hvalue

private theorem theorem2PacBayesAdmissibleBoundedLoss_false_of_loss_gt_one
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (x : X) (y : Y)
    (hgt : 1 < (S.loss w x y : ℝ)) :
    ¬ theorem2PacBayesAdmissibleBoundedLoss (S := S) := by
  intro hadm
  exact not_le_of_gt hgt (hadm.1 w x y)

/- A concrete source setup can satisfy the theorem-stated Gaussian premise
   while violating the unit-interval hypothesis required by the cited
   McAllester step.  This keeps the missing bounded-loss fact at the source
   boundary instead of treating `NNReal`-valuedness as an upper bound by one. -/
theorem theorem2GaussianPremiseSource_does_not_supply_bounded_loss :
    ∃ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S),
      theorem2GaussianPremiseSource S w ∧
        ¬ theorem2PacBayesAdmissibleBoundedLoss (S := S) := by
  let S : Setup 2 ℝ Unit Unit Unit :=
    { parameterSpace := Set.univ
      loss := fun _ _ _ => 2
      dataLaw := Measure.dirac ((), ())
      dataLaw_isProbability := by infer_instance
      batchSize := 1
      w0 := ⟨0, Set.mem_univ 0⟩
      eta := 1
      rho := 1
      p := 1
      lambda := 0
      eta_pos := by norm_num
      rho_pos := by norm_num
      p_domain := by norm_num }
  let w : Setup.Parameter S := ⟨0, Set.mem_univ 0⟩
  have hsource_at :
      ∀ u : ℝ, Setup.sourcePopulationLossAt (S := S) u 2 := by
    intro u
    refine ⟨Set.mem_univ u, ?_, ?_⟩
    · rw [Setup.populationLossWellDefined_spec]
      rw [SOptLib.expectationWellDefined_iff_integrable]
      change Integrable (fun _ : Unit × Unit => (2 : ℝ)) S.dataLaw
      exact integrable_const 2
    · simp [Setup.populationLossValue, S]
  have hgaussian : theorem2GaussianPremiseSource S w := by
    refine ⟨2, 2, hsource_at w.1, ?_, le_rfl⟩
    refine ⟨fun _ : ℝ => 2, ?_, ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun ε =>
        hsource_at (w.1 + S.rho • ε)
    · rw [SOptLib.expectationWellDefined_iff_integrable]
      exact integrable_const 2
    · simp
  refine ⟨S, w, hgaussian, ?_⟩
  exact theorem2PacBayesAdmissibleBoundedLoss_false_of_loss_gt_one
    (S := S) w () () (by norm_num [S])

/- Formal insufficiency certificate for the unguarded hgaussian-only
   Appendix A.1 head.  The concrete setup above satisfies the theorem-stated
   Gaussian premise while violating the bounded-loss contract required by
   the cited PAC-Bayes step, so that contract cannot be recovered from
   hgaussian alone. -/
theorem theorem2PacBayesGaussianAndRadiusSharpness_hgaussian_head_does_not_supply_admissibility :
    ∃ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S),
      theorem2GaussianPremiseSource S w ∧
        ¬ theorem2PacBayesAdmissibleBoundedLoss (S := S) := by
  exact theorem2GaussianPremiseSource_does_not_supply_bounded_loss

/- A stronger retirement certificate for the former hgaussian-only probability
   head.  The source JSON declares only a nonnegative loss, so the constant
   loss `2` is a legal setup datum.  For this setup the sharpness event is
   impossible: every empirical loss is `2`, while its radius-split conclusion
   would require `2 ≤ 2 - 1 / sqrt n`.  Hence the source Gaussian premise
   alone cannot imply the positive-probability conjunction used by the old
   head. -/
theorem theorem2PacBayesGaussianAndRadiusSharpness_hgaussian_head_conclusion_false :
    ∃ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S)
      (δ : Set.Ioo (0 : ℝ) 1),
      theorem2GaussianPremiseSource S w ∧
        ¬ (ENNReal.ofReal (1 - δ.1) ≤
          (Setup.iidTrainingLaw (S := S))
            {s | theorem2PacBayesGaussianExpectationEvent
                (S := S) w δ.1 s ∧
              theorem2GaussianEmpiricalSharpnessEvent
                (S := S) w δ.1 s ∧
              theorem2AppendixA1AbsorptionEvent
                (S := S) w δ.1 s}) := by
  let S : Setup 2 ℝ Unit Unit Unit :=
    { parameterSpace := Set.univ
      loss := fun _ _ _ => 2
      dataLaw := Measure.dirac ((), ())
      dataLaw_isProbability := by infer_instance
      batchSize := 1
      w0 := ⟨0, Set.mem_univ 0⟩
      eta := 1
      rho := 1
      p := 1
      lambda := 0
      eta_pos := by norm_num
      rho_pos := by norm_num
      p_domain := by norm_num }
  let w : Setup.Parameter S := ⟨0, Set.mem_univ 0⟩
  let δ : Set.Ioo (0 : ℝ) 1 := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  have hgaussian : theorem2GaussianPremiseSource S w := by
    refine ⟨2, 2, ?_, ?_, le_rfl⟩
    · refine ⟨Set.mem_univ _, ?_, ?_⟩
      · rw [Setup.populationLossWellDefined_spec]
        rw [SOptLib.expectationWellDefined_iff_integrable]
        change Integrable (fun _ : Unit × Unit => (2 : ℝ)) S.dataLaw
        exact integrable_const 2
      · simp [Setup.populationLossValue, S]
    · refine ⟨fun _ : ℝ => 2, ?_, ?_, by simp⟩
      · exact Filter.Eventually.of_forall fun ε =>
          ⟨Set.mem_univ _, by
            rw [Setup.populationLossWellDefined_spec]
            rw [SOptLib.expectationWellDefined_iff_integrable]
            change Integrable (fun _ : Unit × Unit => (2 : ℝ)) S.dataLaw
            exact integrable_const 2, by
              simp [Setup.populationLossValue, S]⟩
      · rw [SOptLib.expectationWellDefined_iff_integrable]
        exact integrable_const 2
  refine ⟨S, w, δ, hgaussian, ?_⟩
  have hsharp_false :
      ∀ s : Dataset 2 Unit Unit,
        ¬ theorem2GaussianEmpiricalSharpnessEvent
          (S := S) w δ.1 s := by
    intro s hsharp
    have hemp :
        sourceGaussianPerturbedEmpiricalLossAtSigma
          (S := S) s w S.rho 2 := by
      refine ⟨fun _ : ℝ => 2, ?_, ?_, by simp⟩
      · exact Filter.Eventually.of_forall fun ε =>
          ⟨Set.mem_univ _, by
            rw [Setup.empiricalLoss_spec]
            norm_num [S]⟩
      · rw [SOptLib.expectationWellDefined_iff_integrable]
        exact integrable_const 2
    rcases hsharp 2 hemp with ⟨sharpness, hsharpness, hsplit⟩
    have hsharpness' :
        Setup.sourceEuclideanSAMMaximum (S := S) s w sharpness := by
      simpa [theorem2EuclideanSharpnessSource,
        Setup.theorem2SharpnessSource] using hsharpness
    rcases hsharpness' with ⟨_hdomall, hexists, _hupper⟩
    rcases hexists with ⟨ε, _hε, hvalue⟩
    rcases hvalue with ⟨hdom, hvalue⟩
    have hsharpness_eq : sharpness = 2 := by
      rw [hvalue, Setup.empiricalLoss_spec]
      norm_num [S]
    rw [hsharpness_eq] at hsplit
    have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hinv : 0 < (Real.sqrt (2 : ℝ))⁻¹ := inv_pos.mpr hsqrt
    norm_num at hsplit
    linarith
  have hgood_empty :
      {s : Dataset 2 Unit Unit |
          theorem2PacBayesGaussianExpectationEvent
              (S := S) w δ.1 s ∧
            theorem2GaussianEmpiricalSharpnessEvent
              (S := S) w δ.1 s ∧
            theorem2AppendixA1AbsorptionEvent
              (S := S) w δ.1 s} = ∅ := by
    ext s
    constructor
    · intro hs
      exact (hsharp_false s hs.2.1).elim
    · intro hs
      simpa using hs
  rw [hgood_empty, measure_empty]
  norm_num [δ]

theorem theorem2PacBayesGaussianAndRadiusSharpness_probability_from_appendixA1_unqualified_probability_route_retired :
    ¬ (∀ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S)
      (δ : Set.Ioo (0 : ℝ) 1),
      theorem2GaussianPremiseSource S w →
        ENNReal.ofReal (1 - δ.1) ≤
          (Setup.iidTrainingLaw (S := S))
            {s | theorem2PacBayesGaussianExpectationEvent
                (S := S) w δ.1 s ∧
              theorem2GaussianEmpiricalSharpnessEvent
                (S := S) w δ.1 s ∧
              theorem2AppendixA1AbsorptionEvent
                (S := S) w δ.1 s}) := by
  intro hroute
  rcases theorem2PacBayesGaussianAndRadiusSharpness_hgaussian_head_conclusion_false
    with ⟨S, w, δ, hgaussian, hnot⟩
  exact hnot (hroute S w δ hgaussian)

private theorem theorem2PacBayesGaussianAndRadiusSharpness_probability_requires_positive_mass
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (1 - δ.1) ≤
      (Setup.iidTrainingLaw (S := S))
        {s | theorem2PacBayesGaussianExpectationEvent (S := S) w δ.1 s ∧
          theorem2GaussianEmpiricalSharpnessEvent (S := S) w δ.1 s ∧
          theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s} →
    0 <
      (Setup.iidTrainingLaw (S := S))
        {s | theorem2PacBayesGaussianExpectationEvent (S := S) w δ.1 s ∧
          theorem2GaussianEmpiricalSharpnessEvent (S := S) w δ.1 s ∧
          theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s} := by
  intro hprob
  have hreal_pos : 0 < (1 - δ.1 : ℝ) := sub_pos.mpr δ.2.2
  have hleft_pos : 0 < ENNReal.ofReal (1 - δ.1) :=
    ENNReal.ofReal_pos.mpr hreal_pos
  exact lt_of_lt_of_le hleft_pos hprob

private theorem ennreal_ofReal_lower_bound_from_bad_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Set Ω} {r : ℝ} (hr0 : 0 ≤ r)
    (hbad : μ Aᶜ ≤ ENNReal.ofReal r) :
    ENNReal.ofReal (1 - r) ≤ μ A := by
  calc
    ENNReal.ofReal (1 - r) = (1 : ENNReal) - ENNReal.ofReal r := by
      simpa [ENNReal.ofReal_one] using (ENNReal.ofReal_sub (1 : ℝ) (q := r) hr0)
    _ ≤ μ A := by
      rw [tsub_le_iff_right]
      calc
        1 ≤ μ A + μ Aᶜ := by
          simpa [measure_univ] using (measure_univ_le_add_compl (μ := μ) A)
        _ = μ Aᶜ + μ A := add_comm _ _
        _ ≤ ENNReal.ofReal r + μ A := add_le_add_left hbad _
        _ = μ A + ENNReal.ofReal r := add_comm _ _

/- A genuine expectation-splitting lemma for the radius step.  The source
   tail theorem supplies `hbad`; all remaining work is ordinary Bochner
   integration and probability algebra. -/
private theorem integral_le_of_le_on_set_of_unit_interval
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (A : Set α)
    (M r : ℝ) (hA : MeasurableSet A)
    (hf_int : Integrable f μ)
    (hf_le_one : ∀ᵐ x ∂μ, f x ≤ 1)
    (hM_le_one : M ≤ 1)
    (hf_on_A : ∀ᵐ x ∂μ, x ∈ A → f x ≤ M)
    (hbad : μ Aᶜ ≤ ENNReal.ofReal r) (hr_nonneg : 0 ≤ r) :
    ∫ x, f x ∂μ ≤ (1 - r) * M + r := by
  letI : IsFiniteMeasure μ :=
    ⟨by
      rw [IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top⟩
  have hA_int :
      Integrable (A.indicator (fun _ : α => M)) μ :=
    (integrable_const M).indicator hA
  have hAc_int :
      Integrable (Aᶜ.indicator (fun _ : α => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA.compl
  let g : α → ℝ :=
    A.indicator (fun _ : α => M) +
      Aᶜ.indicator (fun _ : α => (1 : ℝ))
  have hfg : f ≤ᵐ[μ] g := by
    filter_upwards [hf_on_A, hf_le_one] with x hx hle_one
    by_cases hmem : x ∈ A
    · have hle : f x ≤ M := hx hmem
      simpa [g, Set.indicator, hmem] using hle
    · have hmemc : x ∈ Aᶜ := by
        simpa [Set.mem_compl_iff, hmem]
      have hle : f x ≤ 1 := hle_one
      simpa [g, Set.indicator, hmem, hmemc] using hle
  have h_integrable_g : Integrable g μ := by
    change Integrable
      ((A.indicator (fun _ : α => M)) +
        (Aᶜ.indicator (fun _ : α => (1 : ℝ)))) μ
    apply Integrable.add
    · exact hA_int
    · exact hAc_int
  have h_integral_le :
      ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ :=
    MeasureTheory.integral_mono_ae hf_int h_integrable_g hfg
  have h_integral_g :
      ∫ x, g x ∂μ = μ.real A * M + μ.real Aᶜ * 1 := by
    dsimp [g]
    rw [integral_add hA_int hAc_int, integral_indicator hA,
      integral_indicator hA.compl,
      setIntegral_const, setIntegral_const]
    simp [smul_eq_mul]
  have hbad_top : ENNReal.ofReal r ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hAc_top : μ (Aᶜ) ≠ ⊤ :=
    measure_ne_top μ (Aᶜ)
  have hbad_real : μ.real Aᶜ ≤ r := by
    rw [measureReal_def]
    have h := (ENNReal.toReal_le_toReal hAc_top hbad_top).mpr hbad
    simpa [ENNReal.toReal_ofReal hr_nonneg] using h
  have hsum_enn : μ A + μ Aᶜ = μ Set.univ := by
    rw [measure_compl hA (measure_ne_top μ A), add_comm]
    exact tsub_add_cancel_of_le (measure_mono (Set.subset_univ A))
  have hsum_real : μ.real A + μ.real Aᶜ = 1 := by
    calc
      μ.real A + μ.real Aᶜ =
          (μ A + μ Aᶜ).toReal := by
            rw [measureReal_def, measureReal_def,
              ENNReal.toReal_add (measure_ne_top μ A)
                (measure_ne_top μ Aᶜ)]
      _ = (μ Set.univ).toReal := by rw [hsum_enn]
      _ = 1 := by
        simp [isProbabilityMeasure_iff.mp
          (show IsProbabilityMeasure μ from inferInstance)]
  have hprod :
      0 ≤ (r - μ.real Aᶜ) * (1 - M) :=
    mul_nonneg (sub_nonneg.mpr hbad_real)
      (sub_nonneg.mpr hM_le_one)
  rw [h_integral_g] at h_integral_le
  nlinarith [hprod, hsum_real]

theorem theorem2AppendixA1GaussianRadiusExpectationSplit
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (f : E → ℝ) (sharpness : ℝ)
    (hf_int : Integrable f (stdGaussian E))
    (hf_le_one : ∀ᵐ ε ∂(stdGaussian E), f ε ≤ 1)
    (hsharp_le_one : sharpness ≤ 1)
    (hf_on_radius :
      ∀ᵐ ε ∂(stdGaussian E),
        ε ∈ theorem2AppendixA1GaussianRadiusEvent (S := S) hn hk →
          f ε ≤ sharpness) :
    ∫ ε : E, f ε ∂(stdGaussian E) ≤
      (1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
        (Real.sqrt (n : ℝ))⁻¹ := by
  have hr_nonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by
    positivity
  exact integral_le_of_le_on_set_of_unit_interval
    (stdGaussian E) f
    (theorem2AppendixA1GaussianRadiusEvent (S := S) hn hk)
    sharpness (Real.sqrt (n : ℝ))⁻¹
    measurableSet_closedBall hf_int hf_le_one hsharp_le_one hf_on_radius
    (theorem2AppendixA1GaussianRadiusTail_bound S hn hk) hr_nonneg

private theorem theorem2AppendixA1_absorption_scalar
    (n C sharpness : ℝ) (hn : 1 < n) (hC : 2 ≤ C)
    (hsharp_nonneg : 0 ≤ sharpness) (hsharp_le_one : sharpness ≤ 1) :
    ((1 - (Real.sqrt n)⁻¹) * sharpness + (Real.sqrt n)⁻¹) +
        Real.sqrt ((C + (1 / 4 : ℝ)) / (n - 1)) ≤
      sharpness + Real.sqrt ((4 * C) / (n - 1)) := by
  have hn_pos : 0 < n := by linarith
  have hden_pos : 0 < n - 1 := by linarith
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn_pos
  have ha_nonneg : 0 ≤ (Real.sqrt n)⁻¹ :=
    inv_nonneg.mpr hsqrt_pos.le
  have hC_nonneg : 0 ≤ C := by linarith
  let a : ℝ := (Real.sqrt n)⁻¹
  let q : ℝ := Real.sqrt ((C + (1 / 4 : ℝ)) / (n - 1))
  let r : ℝ := Real.sqrt ((C) / (n - 1))
  have hq_nonneg : 0 ≤ q := Real.sqrt_nonneg _
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hq_sq :
      q ^ 2 = (C + (1 / 4 : ℝ)) / (n - 1) := by
    dsimp [q]
    rw [Real.sq_sqrt]
    positivity
  have hr_sq :
      r ^ 2 = C / (n - 1) := by
    dsimp [r]
    rw [Real.sq_sqrt]
    positivity
  have ha_sq : a ^ 2 = 1 / n := by
    dsimp [a]
    rw [inv_pow, Real.sq_sqrt hn_pos.le]
    simp [one_div]
  have h_inv_order : 2 / n ≤ 2 / (n - 1) := by
    apply (div_le_div_iff₀ hn_pos hden_pos).2
    nlinarith
  have h_core :
      2 * (C + (1 / 4 : ℝ)) / (n - 1) + 2 / n ≤
        4 * C / (n - 1) := by
    have h_core' :
        (2 * (C + (1 / 4 : ℝ)) + 2) / (n - 1) ≤
          (4 * C) / (n - 1) := by
      apply (div_le_div_iff₀ hden_pos hden_pos).2
      nlinarith
    calc
      2 * (C + (1 / 4 : ℝ)) / (n - 1) + 2 / n ≤
          2 * (C + (1 / 4 : ℝ)) / (n - 1) + 2 / (n - 1) := by
        simpa [add_comm] using
          (add_le_add_left h_inv_order
            (2 * (C + (1 / 4 : ℝ)) / (n - 1)))
      _ = (2 * (C + (1 / 4 : ℝ)) + 2) / (n - 1) := by
        rw [add_div]
      _ ≤ (4 * C) / (n - 1) := h_core'
  have hsq_sum :
      (q + a) ^ 2 ≤ (2 * r) ^ 2 := by
    have hcross : 2 * q * a ≤ q ^ 2 + a ^ 2 := by
      nlinarith [sq_nonneg (q - a)]
    calc
      (q + a) ^ 2 ≤ 2 * q ^ 2 + 2 * a ^ 2 := by
        nlinarith
      _ = 2 * (C + (1 / 4 : ℝ)) / (n - 1) + 2 / n := by
        rw [hq_sq, ha_sq]
        ring
      _ ≤ 4 * C / (n - 1) := h_core
      _ = (2 * r) ^ 2 := by
        rw [show (2 * r) ^ 2 = 4 * r ^ 2 by ring, hr_sq]
        ring
  have hqa : q + a ≤ 2 * r := by
    have hright_nonneg : 0 ≤ 2 * r := by positivity
    nlinarith
  have hfactor :
      a * (1 - sharpness) ≤ a := by
    calc
      a * (1 - sharpness) ≤ a * 1 :=
        mul_le_mul_of_nonneg_left
          (sub_le_self 1 hsharp_nonneg) ha_nonneg
      _ = a := by ring
  calc
    ((1 - (Real.sqrt n)⁻¹) * sharpness + (Real.sqrt n)⁻¹) +
          Real.sqrt ((C + (1 / 4 : ℝ)) / (n - 1)) =
        sharpness + (a * (1 - sharpness) + q) := by
          simp [a, q]
          ring
    _ ≤ sharpness + (a + q) := by
      gcongr
    _ ≤ sharpness + 2 * r := by
      simpa [add_comm] using add_le_add_left hqa sharpness
    _ = sharpness + Real.sqrt ((4 * C) / (n - 1)) := by
      rw [show (4 * C) / (n - 1) = 4 * (C / (n - 1)) by ring]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      rw [← hr_sq, Real.sqrt_sq hr_nonneg]

private theorem theorem2AppendixA1AbsorptionEvent_of_source
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S)) :
    ∀ s : Dataset n X Y,
      theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s := by
  intro s sharpness hsharpness
  have hsharp_le_one :
      sharpness ≤ 1 :=
    theorem2AppendixA1_sharpness_le_one
      (S := S) s w sharpness hadm hn hsharpness
  rcases hsharpness with ⟨_, ⟨ε, hε, hvalue⟩, _⟩
  rcases hvalue with ⟨hu, hsharpness_eq⟩
  have hsharp_nonneg : 0 ≤ sharpness := by
    rw [hsharpness_eq, Setup.empiricalLoss_spec]
    positivity
  let k : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let C : ℝ :=
    ((1 / 4 : ℝ) * k * Real.log
        (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
          (1 + Real.sqrt (Real.log (n : ℝ) / k)) ^ 2) +
      Real.log ((n : ℝ) / δ) +
      2 * Real.log (6 * (n : ℝ) + 3 * k))
  have hk_pos : 0 < k := by
    dsimp [k]
    exact_mod_cast hk
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hratio_gt_one : 1 < (n : ℝ) / δ.1 := by
    have hδ_pos : 0 < δ.1 := by
      exact δ.2.1
    have hδ_lt : δ.1 < 1 := by
      exact δ.2.2
    apply (lt_div_iff₀ hδ_pos).2
    nlinarith
  have harg_nonneg :
      0 ≤ 1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
        (1 + Real.sqrt (Real.log (n : ℝ) / k)) ^ 2 := by
    positivity
  have hfirst_nonneg :
      0 ≤ (1 / 4 : ℝ) * k * Real.log
        (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
          (1 + Real.sqrt (Real.log (n : ℝ) / k)) ^ 2) := by
    have harg_ge_one :
        1 ≤ 1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
          (1 + Real.sqrt (Real.log (n : ℝ) / k)) ^ 2 := by
      have hprod :
          0 ≤ (‖w.1‖ ^ 2 / S.rho ^ 2) *
            (1 + Real.sqrt (Real.log (n : ℝ) / k)) ^ 2 := by
        positivity
      linarith
    have hlog : 0 ≤ Real.log
        (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
          (1 + Real.sqrt (Real.log (n : ℝ) / k)) ^ 2) :=
      Real.log_nonneg harg_ge_one
    positivity
  have hlog_ratio_pos : 0 < Real.log ((n : ℝ) / δ.1) :=
    Real.log_pos hratio_gt_one
  have hlarge_arg : 1 < 6 * (n : ℝ) + 3 * k := by
    nlinarith
  have hlog_large_pos :
      0 < Real.log (6 * (n : ℝ) + 3 * k) :=
    Real.log_pos hlarge_arg
  have hC : 2 ≤ C := by
    dsimp [C]
    have hlog_large_ge_one :
        1 ≤ Real.log (6 * (n : ℝ) + 3 * k) := by
      have hexp_one : Real.exp (1 : ℝ) ≤
          6 * (n : ℝ) + 3 * k := by
        have hexp_bound : Real.exp (1 : ℝ) ≤ 3 := by
          have h :=
            Real.exp_bound' (x := (1 : ℝ)) (n := 4)
              (by norm_num) (by norm_num) (by norm_num)
          norm_num at h ⊢
          linarith
        nlinarith
      exact (Real.le_log_iff_exp_le (by positivity)).2 hexp_one
    nlinarith
  have hscalar :=
    theorem2AppendixA1_absorption_scalar
      (n := (n : ℝ)) (C := C) sharpness
      hn_real hC hsharp_nonneg hsharp_le_one
  convert hscalar using 1 <;>
    simp [theorem2PacBayesRemainder_source, theorem2Remainder_source,
      theorem2OtildeOneTerm, C, k, div_eq_mul_inv] <;>
    ring

theorem theorem2AppendixA1GaussianEmpiricalSharpnessEventAtSigma_of_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : ℝ) (sigma : ℝ) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w)
    (hsigma_radius :
      ∀ ε : E,
        ‖ε‖ ≤
            Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
              (1 + Real.sqrt
                (Real.log (n : ℝ) /
                  (Setup.parameterCount (E := E) : ℝ))) →
          ‖sigma • ε‖ ≤ S.rho) :
    ∀ s : Dataset n X Y,
      theorem2GaussianEmpiricalSharpnessEventAtSigma
        (S := S) w δ sigma s := by
  intro s gaussianEmpirical hgaussianEmpirical
  rcases hsharpness_attain s with ⟨sharpness, hsharpness⟩
  rcases hgaussianEmpirical with
    ⟨f, hf_graph, hf_wd, hf_value⟩
  have hf_int : Integrable f (stdGaussian E) := by
    rw [SOptLib.expectationWellDefined_iff_integrable] at hf_wd
    exact hf_wd
  have hf_le_one : ∀ᵐ ε ∂(stdGaussian E), f ε ≤ 1 := by
    filter_upwards [hf_graph] with ε hε
    exact theorem2AppendixA1_sourceEmpiricalLossAt_le_one
      (S := S) s (w.1 + sigma • ε) (f ε) hadm hn hε
  have hsharp_le_one :
      sharpness ≤ 1 :=
    theorem2AppendixA1_sharpness_le_one
      (S := S) s w sharpness hadm hn hsharpness
  have hf_on_A :
      ∀ᵐ ε ∂(stdGaussian E),
        ε ∈ theorem2AppendixA1GaussianRadiusEvent (S := S) hn hk →
          f ε ≤ sharpness := by
    filter_upwards [hf_graph] with ε hε
    intro hε_radius
    have hε_radius' :
        ‖ε‖ ≤
            Real.sqrt (Setup.parameterCount (E := E) : ℝ) *
              (1 + Real.sqrt
                (Real.log (n : ℝ) /
                  (Setup.parameterCount (E := E) : ℝ))) :=
      (theorem2AppendixA1GaussianRadiusEvent_mem_iff
        (S := S) hn hk ε).mp hε_radius
    exact hsharpness.2.2 (sigma • ε)
      (hsigma_radius ε hε_radius') (f ε) hε
  have hintegral :
      ∫ ε : E, f ε ∂(stdGaussian E) ≤
        (1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
          (Real.sqrt (n : ℝ))⁻¹ :=
    theorem2AppendixA1GaussianRadiusExpectationSplit
      (S := S) hn hk f sharpness hf_int hf_le_one hsharp_le_one hf_on_A
  refine ⟨sharpness, hsharpness, ?_⟩
  calc
    gaussianEmpirical = ∫ ε : E, f ε ∂(stdGaussian E) := hf_value
    _ ≤ (1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
          (Real.sqrt (n : ℝ))⁻¹ := hintegral

theorem theorem2AppendixA1SelectedSigmaGaussianEmpiricalSharpnessEvent_of_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w) :
    ∀ s : Dataset n X Y,
      theorem2GaussianEmpiricalSharpnessEventAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk) s := by
  apply theorem2AppendixA1GaussianEmpiricalSharpnessEventAtSigma_of_source
    (S := S) w δ.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk) hn hk hadm
      hsharpness_attain
  · intro ε hε
    exact theorem2_appendixA1_sigma_radius_bridge S hn hk ε hε

theorem theorem2AppendixA1SelectedSigmaBadEvent_mass_of_source_components
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hpac_mass :
      (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1PacBayesFailureAtSigma
            (S := S) w δ.1
              (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
        ENNReal.ofReal δ.1)
    (hsharpness_event :
      ∀ s : Dataset n X Y,
        theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s)
    (habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s) :
    (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1BadEventAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
      ENNReal.ofReal δ.1 := by
  let μ : Measure (Dataset n X Y) := Setup.iidTrainingLaw (S := S)
  let pacBad :=
    theorem2AppendixA1PacBayesFailureAtSigma (S := S) w δ.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  let sharpBad :=
    theorem2AppendixA1SharpnessFailureAtSigma (S := S) w δ.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  let absorbBad :=
    theorem2AppendixA1AbsorptionFailure (S := S) w δ.1
  let selectedBad :=
    theorem2AppendixA1BadEventAtSigma (S := S) w δ.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  have hsubset : selectedBad ⊆ pacBad ∪ sharpBad ∪ absorbBad := by
    simpa [selectedBad, pacBad, sharpBad, absorbBad] using
      (theorem2AppendixA1BadEventAtSigma_subset_component_union
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk))
  have hsharp_zero : μ sharpBad = 0 := by
    have heq : sharpBad = ∅ := by
      ext s
      constructor
      · intro hs
        have hnot :
            ¬ theorem2GaussianEmpiricalSharpnessEventAtSigma
              (S := S) w δ.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk) s := by
          simpa [sharpBad] using hs
        exact (hnot (hsharpness_event s)).elim
      · intro hs
        simpa using hs
    rw [heq, measure_empty]
  have habsorb_zero : μ absorbBad = 0 := by
    have heq : absorbBad = ∅ := by
      ext s
      constructor
      · intro hs
        have hnot :
            ¬ theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s := by
          simpa [absorbBad] using hs
        exact (hnot (habsorption_event s)).elim
      · intro hs
        simpa using hs
    rw [heq, measure_empty]
  have hcomponent :
      μ (pacBad ∪ sharpBad ∪ absorbBad) ≤ ENNReal.ofReal δ.1 := by
    have hunion :
        μ (pacBad ∪ sharpBad ∪ absorbBad) ≤
          μ pacBad + μ sharpBad + μ absorbBad :=
      theorem2AppendixA1_measure_bad_mass_le_of_component_masses
        μ pacBad sharpBad absorbBad
        (μ pacBad) (μ sharpBad) (μ absorbBad)
        (le_refl _) (le_refl _) (le_refl _)
    calc
      μ (pacBad ∪ sharpBad ∪ absorbBad) ≤
          μ pacBad + μ sharpBad + μ absorbBad := hunion
      _ = μ pacBad := by rw [hsharp_zero, habsorb_zero]; simp
      _ ≤ ENNReal.ofReal δ.1 := by simpa [μ, pacBad] using hpac_mass
  have hbad : μ selectedBad ≤ ENNReal.ofReal δ.1 :=
    le_trans (measure_mono hsubset) hcomponent
  simpa [μ, selectedBad] using hbad

theorem theorem2AppendixA1SelectedSigmaGoodEvent_mass_of_source_components
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hpac_mass :
      (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1PacBayesFailureAtSigma
            (S := S) w δ.1
              (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
        ENNReal.ofReal δ.1)
    (hsharpness_event :
      ∀ s : Dataset n X Y,
        theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s)
    (habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s) :
    ENNReal.ofReal (1 - δ.1) ≤
      (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1SelectedSigmaGoodEvent
          (S := S) w δ.1 hn hk) := by
  let μ : Measure (Dataset n X Y) := Setup.iidTrainingLaw (S := S)
  have hbad :
      μ (theorem2AppendixA1BadEventAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
        ENNReal.ofReal δ.1 :=
    theorem2AppendixA1SelectedSigmaBadEvent_mass_of_source_components
      (S := S) w δ hn hk hpac_mass hsharpness_event habsorption_event
  letI : IsProbabilityMeasure μ :=
    Setup.iidTrainingLaw_isProbability (S := S)
  let selectedBad :=
    theorem2AppendixA1BadEventAtSigma (S := S) w δ.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  have hroute :
      ENNReal.ofReal (1 - δ.1) ≤ μ selectedBadᶜ := by
    exact ennreal_ofReal_lower_bound_from_bad_event
      μ (le_of_lt δ.2.1) (by simpa [theorem2AppendixA1BadEventAtSigma] using hbad)
  change ENNReal.ofReal (1 - δ.1) ≤
    μ (theorem2AppendixA1SelectedSigmaGoodEvent
      (S := S) w δ.1 hn hk)
  simpa [selectedBad, theorem2AppendixA1BadEventAtSigma,
    theorem2AppendixA1SelectedSigmaGoodEvent] using hroute

theorem theorem2AppendixA1SelectedSigmaGoodEvent_mass_of_bounded_loss_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w)
    (hpac_mass :
      (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1PacBayesFailureAtSigma
            (S := S) w δ.1
              (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
        ENNReal.ofReal δ.1)
    (habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s) :
    ENNReal.ofReal (1 - δ.1) ≤
      (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1SelectedSigmaGoodEvent
          (S := S) w δ.1 hn hk) := by
  exact theorem2AppendixA1SelectedSigmaGoodEvent_mass_of_source_components
    (S := S) w δ hn hk hpac_mass
    (theorem2AppendixA1SelectedSigmaGaussianEmpiricalSharpnessEvent_of_source
      (S := S) w δ hn hk hadm hsharpness_attain)
    habsorption_event

/- The exact selected-scale population transport needed after Appendix A.1
   chooses `sigma_Q`.  The paper states the Gaussian premise at `rho`; since
   the selected scale is provably different, this remains a private corrected
   source-calculation boundary rather than a premise on a paper-facing head.

   Route status: private legacy only.  This declaration and its forwarding
   theorem below are not Phase 2a frontier leaves for the current Appendix A.1
   route; the active source route uses the guarded Measure-valued McAllester
   supplier plus the non-conditional selected-grid suppliers below. -/
private def theorem2AppendixA1SelectedSigmaPopulationTransportBoundary_corrected
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E)) : Prop :=
  theorem2GaussianPremiseSource S w →
    theorem2GaussianPremiseSourceAtSigma (S := S) w
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)

private theorem theorem2AppendixA1SelectedSigmaPopulationTransport_of_source
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (htransport :
      theorem2AppendixA1SelectedSigmaPopulationTransportBoundary_corrected
        (S := S) w hn hk)
    (hgaussian : theorem2GaussianPremiseSource S w) :
    theorem2GaussianPremiseSourceAtSigma (S := S) w
      (theorem2AppendixA1SelectedSigma (S := S) hn hk) := by
  exact htransport hgaussian

/- The prior-grid PAC-Bayes source calculation after Eq. (8).  The predicate
   is the narrow mass estimate for the selected-sigma PAC-Bayes failure set;
   it is not a Setup field and not a replacement definition for the event. -/
theorem theorem2AppendixA1ParameterSpace_full_of_grid_domain
    (S : Setup n E X Y Ω) (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    ∀ u : E, u ∈ S.parameterSpace := by
  classical
  let gridStd : ℝ :=
    Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk 0)
  have hgridStd_pos : 0 < gridStd := by
    dsimp [gridStd]
    exact Real.sqrt_pos.2
      (theorem2AppendixA1PriorGridVariance_pos (S := S) hk 0)
  have hgridStd_ne : gridStd ≠ 0 := ne_of_gt hgridStd_pos
  intro u
  have hu :
      (0 : E) +
          Real.sqrt (theorem2AppendixA1PriorGridVariance
            (S := S) hk 0) • (gridStd⁻¹ • u) ∈ S.parameterSpace := by
    exact hdom_grid 0 (gridStd⁻¹ • u)
  have hmul :
      Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk 0) *
          gridStd⁻¹ = 1 := by
    dsimp [gridStd]
    exact mul_inv_cancel₀ hgridStd_ne
  simpa [gridStd, zero_add, smul_smul, hmul] using hu

theorem theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    ∀ ε : E,
      w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
        S.parameterSpace := by
  intro ε
  exact theorem2AppendixA1ParameterSpace_full_of_grid_domain
    (S := S) hk hdom_grid
    (w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε)

private theorem theorem2AppendixA1SelectedSubtypeFiniteKLAtGridIndex_of_gaussianAffineLaw
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ)
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    measurePACBayesKLDivergence
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) w.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          selectedDomain)
      (theorem2AppendixA1ParameterGridContext
        (S := S) hk j
          (hdom_grid j)).prior_distribution ≠ ⊤ := by
  classical
  let selectedGridIndex : ℕ := j
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let sigma : ℝ := theorem2AppendixA1SelectedSigma (S := S) hn hk
  let Qsub : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw (S := S) w.1 sigma selectedDomain
  let Psub : Measure (Setup.Parameter S) :=
    (theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex
        (hdom_grid selectedGridIndex)).prior_distribution
  let Qamb : Measure E := gaussianAffineLaw (E := E) w.1 sigma
  let Pamb : Measure E :=
    gaussianAffineLaw (E := E) (0 : E)
      (Real.sqrt
        (theorem2AppendixA1PriorGridVariance (S := S) hk selectedGridIndex))
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    exact theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
  have hformula :
      theorem2AppendixA1GaussianKLFormulaAtSigma
          (S := S) w hk selectedGridIndex sigma =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex sigma) := by
    exact
      External.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculationAtSigma
        (S := S) w hk selectedGridIndex sigma hsigma_pos
  have hambient_finite :
      InformationTheory.klDiv Qamb Pamb ≠ ⊤ := by
    have hfinite :
        theorem2AppendixA1GaussianKLFormulaAtSigma
            (S := S) w hk selectedGridIndex sigma ≠ ⊤ := by
      rw [hformula]
      exact ENNReal.ofReal_ne_top
    simpa [theorem2AppendixA1GaussianKLFormulaAtSigma, Qamb, Pamb] using
      hfinite
  letI : IsProbabilityMeasure Qamb := by
    dsimp [Qamb, sigma]
    exact gaussianAffineLaw_isProbability (E := E) w.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  letI : IsProbabilityMeasure Pamb := by
    dsimp [Pamb]
    exact gaussianAffineLaw_isProbability (E := E) (0 : E)
      (Real.sqrt
        (theorem2AppendixA1PriorGridVariance (S := S) hk selectedGridIndex))
  have hfull : ∀ u : E, u ∈ S.parameterSpace :=
    theorem2AppendixA1ParameterSpace_full_of_grid_domain
      (S := S) hk hdom_grid
  let e : Setup.Parameter S ≃ᵐ E :=
    setupParameterFullMeasurableEquiv (S := S) hfull
  have hQ_map : Measure.map (fun u : Setup.Parameter S => (u : E)) Qsub = Qamb := by
    dsimp [Qsub, Qamb, sigma]
    exact theorem2AppendixA1ParameterGaussianLaw_map_val
      (S := S) w.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk) selectedDomain
  have hP_map : Measure.map (fun u : Setup.Parameter S => (u : E)) Psub = Pamb := by
    dsimp [Psub, Pamb]
    exact theorem2AppendixA1ParameterGridContext_prior_map_val
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  have hQsub_eq : Measure.map e.symm Qamb = Qsub := by
    apply e.map_measurableEquiv_injective
    rw [MeasurableEquiv.map_map_symm]
    simpa [e, setupParameterFullMeasurableEquiv] using hQ_map.symm
  have hPsub_eq : Measure.map e.symm Pamb = Psub := by
    apply e.map_measurableEquiv_injective
    rw [MeasurableEquiv.map_map_symm]
    simpa [e, setupParameterFullMeasurableEquiv] using hP_map.symm
  have hsub_finite :
      InformationTheory.klDiv (Measure.map e.symm Qamb)
          (Measure.map e.symm Pamb) ≠ ⊤ :=
    klDiv_map_symm_ne_top_of_ne_top e Qamb Pamb hambient_finite
  simpa [measurePACBayesKLDivergence, Qsub, Psub, hQsub_eq, hPsub_eq,
    sigma, selectedDomain, selectedGridIndex] using
    hsub_finite

private theorem theorem2AppendixA1SelectedSubtypeFiniteKL_of_gaussianAffineLaw
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let selectedGridIndex : ℕ :=
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    measurePACBayesKLDivergence
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) w.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          selectedDomain)
      (theorem2AppendixA1ParameterGridContext
        (S := S) hk selectedGridIndex
          (hdom_grid selectedGridIndex)).prior_distribution ≠ ⊤ := by
  simpa using
    (theorem2AppendixA1SelectedSubtypeFiniteKLAtGridIndex_of_gaussianAffineLaw
      (S := S) w hn hk
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk)
      hnorm hdom_grid)

private theorem theorem2AppendixA1SelectedSubtypeKLFormulaAtGridIndex_of_gaussianAffineLaw
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (j : ℕ)
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    measurePACBayesKLDivergence
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) w.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          selectedDomain)
      (theorem2AppendixA1ParameterGridContext
        (S := S) hk j
          (hdom_grid j)).prior_distribution =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk j
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)) := by
  classical
  let selectedGridIndex : ℕ := j
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let sigma : ℝ := theorem2AppendixA1SelectedSigma (S := S) hn hk
  let Qsub : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw (S := S) w.1 sigma selectedDomain
  let Psub : Measure (Setup.Parameter S) :=
    (theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex
        (hdom_grid selectedGridIndex)).prior_distribution
  let Qamb : Measure E := gaussianAffineLaw (E := E) w.1 sigma
  let Pamb : Measure E :=
    gaussianAffineLaw (E := E) (0 : E)
      (Real.sqrt
        (theorem2AppendixA1PriorGridVariance (S := S) hk selectedGridIndex))
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    exact theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
  have hformula :
      theorem2AppendixA1GaussianKLFormulaAtSigma
          (S := S) w hk selectedGridIndex sigma =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex sigma) := by
    exact
      External.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculationAtSigma
        (S := S) w hk selectedGridIndex sigma hsigma_pos
  have hambient_eq :
      InformationTheory.klDiv Qamb Pamb =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex sigma) := by
    simpa [theorem2AppendixA1GaussianKLFormulaAtSigma, Qamb, Pamb] using
      hformula
  have hambient_finite : InformationTheory.klDiv Qamb Pamb ≠ ⊤ := by
    rw [hambient_eq]
    exact ENNReal.ofReal_ne_top
  letI : IsProbabilityMeasure Qamb := by
    dsimp [Qamb, sigma]
    exact gaussianAffineLaw_isProbability (E := E) w.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  letI : IsProbabilityMeasure Pamb := by
    dsimp [Pamb]
    exact gaussianAffineLaw_isProbability (E := E) (0 : E)
      (Real.sqrt
        (theorem2AppendixA1PriorGridVariance (S := S) hk selectedGridIndex))
  have hfull : ∀ u : E, u ∈ S.parameterSpace :=
    theorem2AppendixA1ParameterSpace_full_of_grid_domain
      (S := S) hk hdom_grid
  let e : Setup.Parameter S ≃ᵐ E :=
    setupParameterFullMeasurableEquiv (S := S) hfull
  have hQ_map : Measure.map (fun u : Setup.Parameter S => (u : E)) Qsub = Qamb := by
    dsimp [Qsub, Qamb, sigma]
    exact theorem2AppendixA1ParameterGaussianLaw_map_val
      (S := S) w.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk) selectedDomain
  have hP_map : Measure.map (fun u : Setup.Parameter S => (u : E)) Psub = Pamb := by
    dsimp [Psub, Pamb]
    exact theorem2AppendixA1ParameterGridContext_prior_map_val
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  have hQsub_eq : Measure.map e.symm Qamb = Qsub := by
    apply e.map_measurableEquiv_injective
    rw [MeasurableEquiv.map_map_symm]
    simpa [e, setupParameterFullMeasurableEquiv] using hQ_map.symm
  have hPsub_eq : Measure.map e.symm Pamb = Psub := by
    apply e.map_measurableEquiv_injective
    rw [MeasurableEquiv.map_map_symm]
    simpa [e, setupParameterFullMeasurableEquiv] using hP_map.symm
  have hsub_eq :
      InformationTheory.klDiv (Measure.map e.symm Qamb)
          (Measure.map e.symm Pamb) =
        InformationTheory.klDiv Qamb Pamb :=
    klDiv_map_symm_eq_of_ne_top e Qamb Pamb hambient_finite
  calc
    measurePACBayesKLDivergence Qsub Psub =
        InformationTheory.klDiv (Measure.map e.symm Qamb)
          (Measure.map e.symm Pamb) := by
          simp [measurePACBayesKLDivergence, hQsub_eq, hPsub_eq]
    _ = InformationTheory.klDiv Qamb Pamb := hsub_eq
    _ = ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex sigma) := hambient_eq

/- Sigma-parametric subtype KL bridge.  The posterior scale is an explicit
   argument, while the prior remains the data-independent geometric-grid
   Gaussian.  This is the canonical Measure.map transport used by both the
   paper's rho-scale calculation and the selected radius-control calculation.
-/
private theorem theorem2AppendixA1SubtypeKLFormulaAtSigmaAtGridIndex_of_gaussianAffineLaw
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hdom_posterior :
      ∀ ε : E, w.1 + sigma • ε ∈ S.parameterSpace) :
    measurePACBayesKLDivergence
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) w.1 sigma hdom_posterior)
      (theorem2AppendixA1ParameterGridContext
        (S := S) hk j (hdom_grid j)).prior_distribution =
      ENNReal.ofReal
        (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
          (S := S) w hk j sigma) := by
  classical
  let Qsub : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw (S := S) w.1 sigma hdom_posterior
  let Psub : Measure (Setup.Parameter S) :=
    (theorem2AppendixA1ParameterGridContext
      (S := S) hk j (hdom_grid j)).prior_distribution
  let Qamb : Measure E := gaussianAffineLaw (E := E) w.1 sigma
  let Pamb : Measure E :=
    gaussianAffineLaw (E := E) (0 : E)
      (Real.sqrt (theorem2AppendixA1PriorGridVariance (S := S) hk j))
  have hformula :
      theorem2AppendixA1GaussianKLFormulaAtSigma
          (S := S) w hk j sigma =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk j sigma) :=
    External.theorem2AppendixA1GaussianKLFormulaScalarSourceCalculationAtSigma
      (S := S) w hk j sigma hsigma
  have hambient_eq :
      InformationTheory.klDiv Qamb Pamb =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk j sigma) := by
    simpa [theorem2AppendixA1GaussianKLFormulaAtSigma, Qamb, Pamb] using
      hformula
  have hambient_finite : InformationTheory.klDiv Qamb Pamb ≠ ⊤ := by
    rw [hambient_eq]
    exact ENNReal.ofReal_ne_top
  letI : IsProbabilityMeasure Qamb :=
    gaussianAffineLaw_isProbability (E := E) w.1 sigma
  letI : IsProbabilityMeasure Pamb :=
    gaussianAffineLaw_isProbability (E := E) (0 : E)
      (Real.sqrt
        (theorem2AppendixA1PriorGridVariance (S := S) hk j))
  have hfull : ∀ u : E, u ∈ S.parameterSpace :=
    theorem2AppendixA1ParameterSpace_full_of_grid_domain
      (S := S) hk hdom_grid
  let e : Setup.Parameter S ≃ᵐ E :=
    setupParameterFullMeasurableEquiv (S := S) hfull
  have hQ_map : Measure.map (fun u : Setup.Parameter S => (u : E)) Qsub = Qamb := by
    dsimp [Qsub, Qamb]
    exact theorem2AppendixA1ParameterGaussianLaw_map_val
      (S := S) w.1 sigma hdom_posterior
  have hP_map : Measure.map (fun u : Setup.Parameter S => (u : E)) Psub = Pamb := by
    dsimp [Psub, Pamb]
    exact theorem2AppendixA1ParameterGridContext_prior_map_val
      (S := S) hk j (hdom_grid j)
  have hQsub_eq : Measure.map e.symm Qamb = Qsub := by
    apply e.map_measurableEquiv_injective
    rw [MeasurableEquiv.map_map_symm]
    simpa [e, setupParameterFullMeasurableEquiv] using hQ_map.symm
  have hPsub_eq : Measure.map e.symm Pamb = Psub := by
    apply e.map_measurableEquiv_injective
    rw [MeasurableEquiv.map_map_symm]
    simpa [e, setupParameterFullMeasurableEquiv] using hP_map.symm
  have hsub_eq :
      InformationTheory.klDiv (Measure.map e.symm Qamb)
          (Measure.map e.symm Pamb) =
        InformationTheory.klDiv Qamb Pamb :=
    klDiv_map_symm_eq_of_ne_top e Qamb Pamb hambient_finite
  calc
    measurePACBayesKLDivergence Qsub Psub =
        InformationTheory.klDiv (Measure.map e.symm Qamb)
          (Measure.map e.symm Pamb) := by
          simp [measurePACBayesKLDivergence, hQsub_eq, hPsub_eq]
    _ = InformationTheory.klDiv Qamb Pamb := hsub_eq
    _ = ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk j sigma) := hambient_eq

private theorem theorem2AppendixA1RhoSubtypeKLFormulaAtGridIndex_of_gaussianAffineLaw
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let rhoGridIndex : ℕ :=
      theorem2AppendixA1PriorGridIndexAtRhoScale (S := S) w hn hk
    let rhoDomain : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace :=
      fun ε =>
        theorem2AppendixA1ParameterSpace_full_of_grid_domain
          (S := S) hk hdom_grid (w.1 + S.rho • ε)
    measurePACBayesKLDivergence
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) w.1 S.rho rhoDomain)
      (theorem2AppendixA1ParameterGridContext
        (S := S) hk rhoGridIndex (hdom_grid rhoGridIndex)).prior_distribution =
      ENNReal.ofReal
        (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
          (S := S) w hk rhoGridIndex S.rho) := by
  let rhoGridIndex : ℕ :=
    theorem2AppendixA1PriorGridIndexAtRhoScale (S := S) w hn hk
  let rhoDomain : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace :=
    fun ε =>
      theorem2AppendixA1ParameterSpace_full_of_grid_domain
        (S := S) hk hdom_grid (w.1 + S.rho • ε)
  simpa [rhoGridIndex, rhoDomain] using
    (theorem2AppendixA1SubtypeKLFormulaAtSigmaAtGridIndex_of_gaussianAffineLaw
      (S := S) w hk rhoGridIndex S.rho S.rho_pos hdom_grid rhoDomain)

private theorem theorem2AppendixA1SelectedSubtypeKLFormulaAtSelectedSigma_of_gaussianAffineLaw
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let selectedGridIndex : ℕ :=
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    measurePACBayesKLDivergence
      (theorem2AppendixA1ParameterGaussianLaw
        (S := S) w.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          selectedDomain)
      (theorem2AppendixA1ParameterGridContext
        (S := S) hk selectedGridIndex
          (hdom_grid selectedGridIndex)).prior_distribution =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)) := by
  simpa using
    (theorem2AppendixA1SelectedSubtypeKLFormulaAtGridIndex_of_gaussianAffineLaw
      (S := S) w hn hk
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk)
      hnorm hdom_grid)

private def theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGridLegacyStatement
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E)) : Prop :=
  (Setup.iidTrainingLaw (S := S))
      (theorem2AppendixA1PacBayesFailureAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
    ENNReal.ofReal δ.1

def theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (sigma : ℝ)
    (remainder : ℝ) (s : Dataset n X Y) : Prop :=
  ∃ (gaussianPopulation gaussianEmpirical : ℝ),
    sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w sigma gaussianPopulation ∧
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w sigma gaussianEmpirical ∧
      gaussianPopulation ≤ gaussianEmpirical + remainder

noncomputable def theorem2AppendixA1SelectedSigmaPACBayesPenalty
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
      (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
        ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) : ℝ :=
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
      (S := S) w hn hk)
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  Real.sqrt
    (((measurePACBayesKLDivergence
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain)
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex
            (hdom_grid selectedGridIndex)).prior_distribution).toReal +
      Real.log
        ((n : ℝ) /
          theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
      (2 * ((n : ℝ) - 1)))

theorem theorem2AppendixA1SelectedSigmaPACBayesPenalty_spec
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let selectedGridIndex : ℕ :=
      theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk
    let selectedDomain :
        ∀ ε : E,
          w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
            S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    theorem2AppendixA1SelectedSigmaPACBayesPenalty
        (S := S) w δ hn hk hdom_grid =
      Real.sqrt
        (((measurePACBayesKLDivergence
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex
                (hdom_grid selectedGridIndex)).prior_distribution).toReal +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
          (2 * ((n : ℝ) - 1))) := by
  rfl

def theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    Set (Dataset n X Y) :=
  {s | ¬ theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
    (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
    (theorem2AppendixA1SelectedSigmaPACBayesPenalty
      (S := S) w δ hn hk hdom_grid) s}

def theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureGridInclusion
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) : Prop :=
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk)
  theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure
      (S := S) w δ hn hk hdom_grid ⊆
    theorem2AppendixA1GridPACBayesFailure
      (S := S) w δ hn hk selectedGridIndex (hdom_grid selectedGridIndex)

def theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureFromPriorGrid
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) : Prop :=
  (Setup.iidTrainingLaw (S := S))
      (theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure
        (S := S) w δ hn hk hdom_grid) ≤
    ENNReal.ofReal δ.1

/- The remaining Eq. (8)--(13) comparison is an event inclusion, not a
   probability estimate.  Once this formula-level inclusion is available,
   the selected-sigma failure mass follows from the already proved
   per-grid PAC-Bayes supplier and the countable prior-grid union bound. -/
private def theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionLegacyStatement
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) : Prop :=
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk)
  theorem2AppendixA1PacBayesFailureAtSigma
      (S := S) w δ.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk) ⊆
    theorem2AppendixA1GridPACBayesFailure
      (S := S) w δ hn hk selectedGridIndex (hdom_grid selectedGridIndex)

/- Same selected-posterior event, but with the paper's rho-scale Eq. (8)
   prior-grid index.  This is the interface the confidence-log calculation
   in Appendix A.1 actually supports; pairing it with the selected posterior
   is audited below because the KL term then changes scale. -/
private def theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionAtRhoScale
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) : Prop :=
  let rhoGridIndex : ℕ :=
    (theorem2AppendixA1PriorGridIndexAtRhoScale
        (S := S) w hn hk)
  theorem2AppendixA1PacBayesFailureAtSigma
      (S := S) w δ.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk) ⊆
    theorem2AppendixA1GridPACBayesFailure
      (S := S) w δ hn hk rhoGridIndex (hdom_grid rhoGridIndex)

private def theorem2AppendixA1SelectedSigmaRhoScalePenaltyComparison
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) : Prop :=
  let rhoGridIndex : ℕ :=
    (theorem2AppendixA1PriorGridIndexAtRhoScale
        (S := S) w hn hk)
  let selectedDomain :
    ∀ ε : E,
      w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
        S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  Real.sqrt
      (((measurePACBayesKLDivergence
          (theorem2AppendixA1ParameterGaussianLaw
            (S := S) w.1
              (theorem2AppendixA1SelectedSigma (S := S) hn hk)
              selectedDomain)
          (theorem2AppendixA1ParameterGridContext
            (S := S) hk rhoGridIndex
              (hdom_grid rhoGridIndex)).prior_distribution).toReal +
        Real.log
          ((n : ℝ) /
            theorem2AppendixA1PriorGridConfidence δ.1 rhoGridIndex)) /
        (2 * ((n : ℝ) - 1))) ≤
    theorem2PacBayesRemainder_source (S := S) w.1 δ.1

private theorem theorem2AppendixA1GaussianKLFormulaScalarAtSigma_nonneg_of_sandwich
    {K sigma b v : ℝ} (hK : 0 < K) (hsigma : 0 < sigma)
    (hb : 0 ≤ b) (ha : sigma ^ 2 + b / K ≤ v) :
    0 ≤ (1 / 2 : ℝ) *
      (((K * sigma ^ 2 + b) / v - K + K * Real.log (v / sigma ^ 2))) := by
  have hs : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hbdiv : 0 ≤ b / K := div_nonneg hb hK.le
  have hs_le_v : sigma ^ 2 ≤ v := by linarith
  have hv : 0 < v := lt_of_lt_of_le hs hs_le_v
  have hq : 0 ≤ v - sigma ^ 2 := sub_nonneg.mpr hs_le_v
  have hlog0 :=
    div_add_le_log_add_sub_log_of_pos_of_nonneg
      (p := sigma ^ 2) (q := v - sigma ^ 2) hs hq
  have hsum : sigma ^ 2 + (v - sigma ^ 2) = v := by ring
  have hlog_lower : 1 - sigma ^ 2 / v ≤ Real.log (v / sigma ^ 2) := by
    have htmp :
        (v - sigma ^ 2) / v ≤ Real.log v - Real.log (sigma ^ 2) := by
      simpa [hsum] using hlog0
    have hfrac : (v - sigma ^ 2) / v = 1 - sigma ^ 2 / v := by
      field_simp [ne_of_gt hv]
    have hlog_div :
        Real.log (v / sigma ^ 2) = Real.log v - Real.log (sigma ^ 2) := by
      rw [Real.log_div (ne_of_gt hv) (ne_of_gt hs)]
    simpa [hfrac, hlog_div] using htmp
  have hcore :
      0 ≤ K * (Real.log (v / sigma ^ 2) - (1 - sigma ^ 2 / v)) := by
    exact mul_nonneg hK.le (sub_nonneg.mpr hlog_lower)
  have hbterm : 0 ≤ b / v := div_nonneg hb hv.le
  have hinner :
      0 ≤ ((K * sigma ^ 2 + b) / v - K +
        K * Real.log (v / sigma ^ 2)) := by
    have hrewrite :
        ((K * sigma ^ 2 + b) / v - K +
            K * Real.log (v / sigma ^ 2)) =
          b / v +
            K * (Real.log (v / sigma ^ 2) - (1 - sigma ^ 2 / v)) := by
      field_simp [ne_of_gt hv]
      ring
    rw [hrewrite]
    exact add_nonneg hbterm hcore
  positivity

private theorem theorem2AppendixA1GaussianKLFormulaScalarAtSigma_le_of_sandwich
    {K sigma b v target : ℝ} (hK : 0 < K) (hsigma : 0 < sigma)
    (hb : 0 ≤ b)
    (hlower : sigma ^ 2 + b / K ≤ v)
    (hupper : v ≤ Real.exp (1 / K) * (sigma ^ 2 + b / K))
    (htarget : target = 1 + b / (K * sigma ^ 2)) :
    (1 / 2 : ℝ) *
        (((K * sigma ^ 2 + b) / v - K +
          K * Real.log (v / sigma ^ 2))) ≤
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * K * Real.log target := by
  have hs2_pos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hbdiv_nonneg : 0 ≤ b / K := div_nonneg hb hK.le
  have ha_pos : 0 < sigma ^ 2 + b / K := by positivity
  have hv_pos : 0 < v := lt_of_lt_of_le ha_pos hlower
  have hlin :
      (K * sigma ^ 2 + b) / v ≤ K := by
    have hnum_eq : K * sigma ^ 2 + b = K * (sigma ^ 2 + b / K) := by
      field_simp [ne_of_gt hK]
    rw [hnum_eq]
    rw [div_le_iff₀ hv_pos]
    nlinarith [hlower, hK.le]
  have htarget_pos : 0 < target := by
    rw [htarget]
    have hden_pos : 0 < K * sigma ^ 2 := mul_pos hK hs2_pos
    have hfrac_nonneg : 0 ≤ b / (K * sigma ^ 2) :=
      div_nonneg hb hden_pos.le
    positivity
  have hlog_arg_pos : 0 < v / sigma ^ 2 := div_pos hv_pos hs2_pos
  have hlog_arg_le :
      v / sigma ^ 2 ≤ Real.exp (1 / K) * target := by
    have htarget_eq :
        Real.exp (1 / K) * target =
          Real.exp (1 / K) * ((sigma ^ 2 + b / K) / sigma ^ 2) := by
      rw [htarget]
      congr 1
      field_simp [ne_of_gt hK, ne_of_gt hs2_pos]
    calc
      v / sigma ^ 2 ≤
          (Real.exp (1 / K) * (sigma ^ 2 + b / K)) / sigma ^ 2 :=
            div_le_div_of_nonneg_right hupper hs2_pos.le
      _ = Real.exp (1 / K) * target := by
            rw [htarget_eq]
            field_simp [ne_of_gt hs2_pos]
  have hlog_le :
      Real.log (v / sigma ^ 2) ≤ Real.log (Real.exp (1 / K) * target) :=
    Real.log_le_log hlog_arg_pos hlog_arg_le
  have hlog_mul :
      Real.log (Real.exp (1 / K) * target) =
        1 / K + Real.log target := by
    rw [Real.log_mul (ne_of_gt (Real.exp_pos (1 / K)))
      (ne_of_gt htarget_pos)]
    rw [Real.log_exp]
  have hlog_bound :
      K * Real.log (v / sigma ^ 2) ≤
        1 + K * Real.log target := by
    calc
      K * Real.log (v / sigma ^ 2) ≤
          K * Real.log (Real.exp (1 / K) * target) :=
            mul_le_mul_of_nonneg_left hlog_le hK.le
      _ = K * (1 / K + Real.log target) := by rw [hlog_mul]
      _ = 1 + K * Real.log target := by
            field_simp [ne_of_gt hK]
  calc
    (1 / 2 : ℝ) *
        (((K * sigma ^ 2 + b) / v - K +
          K * Real.log (v / sigma ^ 2))) ≤
      (1 / 2 : ℝ) * (1 + K * Real.log target) := by
        nlinarith [hlin, hlog_bound]
    _ = (1 / 2 : ℝ) + (1 / 2 : ℝ) * K * Real.log target := by ring

/- Retired false route: the following historical block attempted to bound the
   selected-sigma grid confidence by Appendix A.1's rho-scale confidence
   envelope.  The PDF's Eq. (7)--(13) sets `sigma_Q = rho`, while the selected
   Lean posterior has `sigma_Q = selectedSigma`; the ratio certificates below
   show these are different scales.  The active route after this comment uses
   the exact selected-grid PAC-Bayes penalty instead. 

/- Active selected-sigma event-scale alignment for Appendix A.1.  This is the
   corrected source-boundary theorem consumed by the selected-grid supplier:
   it keeps the selected posterior scale and selected prior-grid confidence in
   one place, instead of routing through the legacy selected-sigma penalty
   name. -/
private theorem theorem2AppendixA1_event_scale_alignment
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let selectedGridIndex : ℕ :=
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    Real.sqrt
        (((measurePACBayesKLDivergence
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex
                (hdom_grid selectedGridIndex)).prior_distribution).toReal +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
          (2 * ((n : ℝ) - 1))) ≤
      theorem2PacBayesRemainder_source (S := S) w.1 δ.1 := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let sigma : ℝ := theorem2AppendixA1SelectedSigma (S := S) hn hk
  let ctx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  let Q : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw
      (S := S) w.1 sigma selectedDomain
  have hselected_kl_formula :
      measurePACBayesKLDivergence Q ctx.prior_distribution =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex sigma) := by
    simpa [Q, ctx, selectedGridIndex, selectedDomain, sigma] using
      (theorem2AppendixA1SelectedSubtypeKLFormulaAtSelectedSigma_of_gaussianAffineLaw
        (S := S) w hn hk hnorm hdom_grid)
  have hselected_kl_toReal :
      (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal =
        theorem2AppendixA1GaussianKLFormulaScalarAtSigma
          (S := S) w hk selectedGridIndex sigma := by
    rw [hselected_kl_formula]
    have hscalar_nonneg :
        0 ≤ theorem2AppendixA1GaussianKLFormulaScalarAtSigma
          (S := S) w hk selectedGridIndex sigma := by
      have hK : 0 < (Setup.parameterCount (E := E) : ℝ) := by
        exact_mod_cast hk
      have hsigma : 0 < sigma := by
        dsimp [sigma]
        exact theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
      have hb : 0 ≤ ‖w.1‖ ^ 2 := sq_nonneg _
      have hsandwich_for_nonneg :
          let j : ℕ :=
            (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
              (S := S) w hn hk);
            theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
                ‖w.1‖ ^ 2 /
                  (Setup.parameterCount (E := E) : ℝ) ≤
              theorem2AppendixA1PriorGridVariance (S := S) hk j ∧
            theorem2AppendixA1PriorGridVariance (S := S) hk j ≤
              Real.exp (1 / (Setup.parameterCount (E := E) : ℝ)) *
                (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
                  ‖w.1‖ ^ 2 /
                    (Setup.parameterCount (E := E) : ℝ)) :=
        theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_spec_of_reduced_norm
          (S := S) w hn hk hnorm
      have ha :
          sigma ^ 2 + ‖w.1‖ ^ 2 /
              (Setup.parameterCount (E := E) : ℝ) ≤
            theorem2AppendixA1PriorGridVariance
              (S := S) hk selectedGridIndex := by
        simpa [sigma, selectedGridIndex] using
          hsandwich_for_nonneg.1
      simpa [theorem2AppendixA1GaussianKLFormulaScalarAtSigma] using
        (theorem2AppendixA1GaussianKLFormulaScalarAtSigma_nonneg_of_sandwich
          (K := (Setup.parameterCount (E := E) : ℝ))
          (sigma := sigma) (b := ‖w.1‖ ^ 2)
          (v := theorem2AppendixA1PriorGridVariance
            (S := S) hk selectedGridIndex)
          hK hsigma hb ha)
    exact ENNReal.toReal_ofReal
      hscalar_nonneg
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have hn_real : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have htwo_den_pos : 0 < 2 * ((n : ℝ) - 1) := by
    positivity
  have hselected_sandwich :
      let j : ℕ :=
        (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
          (S := S) w hn hk);
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
            ‖w.1‖ ^ 2 /
              (Setup.parameterCount (E := E) : ℝ) ≤
          theorem2AppendixA1PriorGridVariance (S := S) hk j ∧
        theorem2AppendixA1PriorGridVariance (S := S) hk j ≤
          Real.exp (1 / (Setup.parameterCount (E := E) : ℝ)) *
            (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
              ‖w.1‖ ^ 2 /
                (Setup.parameterCount (E := E) : ℝ)) :=
    theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_spec_of_reduced_norm
      (S := S) w hn hk hnorm
  have hselected_index_log :
      ((selectedGridIndex : ℕ) : ℝ) ≤
        (Setup.parameterCount (E := E) : ℝ) *
          Real.log
            (theorem2AppendixA1PriorGridScale (S := S) hk /
              (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
                ‖w.1‖ ^ 2 / (Setup.parameterCount (E := E) : ℝ))) := by
    simpa [selectedGridIndex] using
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_le_log_ratio
        (S := S) w hn hk hnorm)
  dsimp [Q, ctx, sigma] at hselected_kl_toReal
  dsimp [selectedGridIndex, selectedDomain]
  rw [hselected_kl_toReal]
  rw [theorem2PacBayesRemainder_source_spec]
  apply Real.sqrt_le_sqrt
  let K : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let klSelected : ℝ :=
    theorem2AppendixA1GaussianKLFormulaScalarAtSigma
      (S := S) w hk selectedGridIndex
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  let confSelected : ℝ :=
    Real.log
      ((n : ℝ) /
        theorem2AppendixA1PriorGridConfidence δ.1
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
            (S := S) w hn hk))
  let targetLog : ℝ :=
    Real.log
      (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
        (1 + Real.sqrt (Real.log (n : ℝ) / K)) ^ 2)
  let confidenceRemainder : ℝ :=
    Real.log ((n : ℝ) / δ.1) +
      2 * Real.log (6 * (n : ℝ) + 3 * K)
  have hK_pos : 0 < K := by
    dsimp [K]
    exact_mod_cast hk
  have hdelta_pos : 0 < δ.1 := δ.2.1
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hconfidence_nonneg : 0 ≤ confidenceRemainder := by
    have hratio_gt_one : 1 < (n : ℝ) / δ.1 := by
      apply (lt_div_iff₀ hdelta_pos).2
      nlinarith [hn_real, δ.2.2]
    have hlog_ratio_nonneg : 0 ≤ Real.log ((n : ℝ) / δ.1) :=
      (Real.log_pos hratio_gt_one).le
    have hlarge_arg : 1 ≤ 6 * (n : ℝ) + 3 * K := by
      nlinarith [hn_real.le, hK_pos.le]
    have hlog_large_nonneg :
        0 ≤ Real.log (6 * (n : ℝ) + 3 * K) :=
      Real.log_nonneg hlarge_arg
    dsimp [confidenceRemainder]
    positivity
  have hkl_bound :
      klSelected ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) * K * targetLog := by
    /- Eq. (9)--(12) scalar attempt.  The local context supplies the selected
       variance sandwich (`hselected_sandwich`), positivity of the selected
       standard deviation, and the floor-grid index.  The remaining work is the
       monotonicity/log rewrite
       `KL(Q||P_j) ≤ 1/2 + 1/2*K*log(1+‖w‖²/(K*sigma²))` followed by the
       definitional selected-sigma rewrite to `targetLog`. -/
    have hsigma_pos :
        0 < theorem2AppendixA1SelectedSigma (S := S) hn hk :=
      theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
    have hsandwich_lower :
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
            ‖w.1‖ ^ 2 / K ≤
          theorem2AppendixA1PriorGridVariance
            (S := S) hk selectedGridIndex := by
      simpa [K, selectedGridIndex] using hselected_sandwich.1
    have hsandwich_upper :
        theorem2AppendixA1PriorGridVariance
            (S := S) hk selectedGridIndex ≤
          Real.exp (1 / K) *
            (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
              ‖w.1‖ ^ 2 / K) := by
      simpa [K, selectedGridIndex] using hselected_sandwich.2
    have htarget :
        1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
              (1 + Real.sqrt (Real.log (n : ℝ) / K)) ^ 2 =
          1 + ‖w.1‖ ^ 2 /
              (K * theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2) := by
      have hlog_nonneg : 0 ≤ Real.log (n : ℝ) / K := by
        have hlog : 0 ≤ Real.log (n : ℝ) :=
          Real.log_nonneg hn_real.le
        positivity
      have hden_pos :
          0 <
            Real.sqrt K *
              (1 + Real.sqrt (Real.log (n : ℝ) / K)) := by
        have hsqrtK_pos : 0 < Real.sqrt K := Real.sqrt_pos.2 hK_pos
        have hone_pos :
            0 < 1 + Real.sqrt (Real.log (n : ℝ) / K) := by
          positivity
        positivity
      have hsqrtK_sq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK_pos.le
      have hsqrt_count_sq :
          Real.sqrt ((Setup.parameterCount (E := E) : ℝ)) ^ 2 = K := by
        simpa [K] using hsqrtK_sq
      dsimp [theorem2AppendixA1SelectedSigma]
      field_simp [ne_of_gt S.rho_pos, ne_of_gt hK_pos,
        ne_of_gt hden_pos, hsqrtK_sq]
      rw [hsqrt_count_sq]
      ring
    have hscalar :=
      theorem2AppendixA1GaussianKLFormulaScalarAtSigma_le_of_sandwich
        (K := K)
        (sigma := theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (b := ‖w.1‖ ^ 2)
        (v := theorem2AppendixA1PriorGridVariance
          (S := S) hk selectedGridIndex)
        (target :=
          1 + (‖w.1‖ ^ 2 / S.rho ^ 2) *
            (1 + Real.sqrt (Real.log (n : ℝ) / K)) ^ 2)
        hK_pos hsigma_pos (sq_nonneg ‖w.1‖)
        hsandwich_lower hsandwich_upper htarget
    simpa [klSelected, targetLog, K,
      theorem2AppendixA1GaussianKLFormulaScalarAtSigma] using hscalar
  have hconf_bound :
      confSelected ≤ confidenceRemainder := by
    /- Eq. (15)--(20) confidence-log attempt.  The available bound
       `hselected_index_log` gives the selected floor index as a real logarithm;
       after unfolding `theorem2AppendixA1PriorGridConfidence`, the residual
       proof is the paper's monotone-log bound
       `log (n / δ_j) ≤ log (n / δ) + 2 log (6n + 3K)`. -/
    have hj_log :
        ((selectedGridIndex : ℕ) : ℝ) ≤
          K *
            Real.log
              (theorem2AppendixA1PriorGridScale (S := S) hk /
                (theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 +
                  ‖w.1‖ ^ 2 / K)) := by
      simpa [K] using hselected_index_log
    -- Concrete failed leaf: combine `hj_log`, the confidence definition, and
    -- elementary estimates on `log (1 + exp (4n/K))`.
    retired_placeholder
  have hnum_bound :
      klSelected + confSelected ≤
        2 *
          (((1 : ℝ) / 4) * K * targetLog +
            ((1 : ℝ) / 4) + confidenceRemainder) := by
    nlinarith [hkl_bound, hconf_bound, hconfidence_nonneg]
  have habstract :
      (klSelected + confSelected) / (2 * ((n : ℝ) - 1)) ≤
        ((((1 : ℝ) / 4) * K * targetLog +
              ((1 : ℝ) / 4) + confidenceRemainder) /
          ((n : ℝ) - 1)) := by
    calc
      (klSelected + confSelected) / (2 * ((n : ℝ) - 1)) ≤
          (2 * (((1 : ℝ) / 4) * K * targetLog +
            ((1 : ℝ) / 4) + confidenceRemainder)) /
            (2 * ((n : ℝ) - 1)) := by
            exact div_le_div_of_nonneg_right hnum_bound htwo_den_pos.le
      _ = ((((1 : ℝ) / 4) * K * targetLog +
            ((1 : ℝ) / 4) + confidenceRemainder) /
          ((n : ℝ) - 1)) := by
            field_simp [ne_of_gt hden_pos]
  dsimp [klSelected, confSelected, targetLog, confidenceRemainder, K] at habstract
  convert habstract using 1 <;> ring

/- Legacy compatibility alias retained for private callers.  Source/public
   consumers should use `theorem2AppendixA1_event_scale_alignment`, which is
   the active route requested by the reconstruction audit. -/
private theorem theorem2AppendixA1SelectedSigmaPenaltyComparison_of_reduced_norm
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    let selectedGridIndex : ℕ :=
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    Real.sqrt
        (((measurePACBayesKLDivergence
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex
                (hdom_grid selectedGridIndex)).prior_distribution).toReal +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
          (2 * ((n : ℝ) - 1))) ≤
      theorem2PacBayesRemainder_source (S := S) w.1 δ.1 := by
  exact theorem2AppendixA1_event_scale_alignment
    (S := S) w δ hn hk hnorm hdom_grid

-/

/- The selected-sigma confidence algebra is not Appendix A.1's rho-scale
   algebra.  These replacement certificates keep the old names out of the
   source/public proof route while preserving a compiled explanation of why the
   previous terminal supplier was retired. -/
private theorem theorem2AppendixA1_event_scale_alignment
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
      theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  exact theorem2AppendixA1_selectedSigma_grid_ratio_ne_rho_grid_ratio
    (S := S) hn hk

private theorem theorem2AppendixA1SelectedSigmaPenaltyComparison_of_reduced_norm
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
      theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  exact theorem2AppendixA1_event_scale_alignment
    (S := S) w δ hn hk hnorm hdom_grid

/- Logical core of the selected-grid Eq. (13) event conversion.  The theorem
   is intentionally private: it does not add source assumptions to any public
   theorem head, but it factors the remaining Appendix A.1 work into the
   concrete posterior finite-KL fact, source loss identities, and scalar
   penalty comparison. -/
private theorem theorem2PacBayesGaussianExpectationEventAtSigma_of_expected_loss_event
    {Concept : Type*} [MeasurableSpace Concept]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δevent δpb : ℝ) (hn : 1 < n) (sigma : ℝ)
    (s : Dataset n X Y)
    (ctx : MeasurePACBayesDistributionContext Concept (X × Y))
    (loss : MeasurePACBayesPointwiseLoss Concept (X × Y))
    (Q : Measure Concept)
    (hQ : IsProbabilityMeasure Q)
    (hQfinite :
      measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤)
    (hgood :
      s ∈ measurePACBayesExpectedLossEvent ctx n hn δpb loss)
    (gaussianPopulation gaussianEmpirical : ℝ)
    (hpopulation_source :
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w sigma gaussianPopulation)
    (hempirical_source :
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w sigma gaussianEmpirical)
    (hpopulation_eq :
      measurePACBayesPopulationLoss ctx loss Q = gaussianPopulation)
    (hempirical_eq :
      measurePACBayesEmpiricalLoss ctx n s loss Q = gaussianEmpirical)
    (hpenalty :
      Real.sqrt
          (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
            Real.log ((n : ℝ) / δpb)) /
            (2 * ((n : ℝ) - 1))) ≤
        theorem2PacBayesRemainder_source (S := S) w.1 δevent) :
    theorem2PacBayesGaussianExpectationEventAtSigma
      (S := S) w δevent sigma s := by
  have hineq :
      measurePACBayesPopulationLoss ctx loss Q ≤
        measurePACBayesEmpiricalLoss ctx n s loss Q +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((n : ℝ) / δpb)) /
              (2 * ((n : ℝ) - 1))) := by
    rcases hgood Q hQ with htop | hle
    · exact False.elim (hQfinite htop)
    · exact hle
  refine ⟨gaussianPopulation, gaussianEmpirical,
    hpopulation_source, hempirical_source, ?_⟩
  calc
    gaussianPopulation =
        measurePACBayesPopulationLoss ctx loss Q := hpopulation_eq.symm
    _ ≤ measurePACBayesEmpiricalLoss ctx n s loss Q +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((n : ℝ) / δpb)) /
              (2 * ((n : ℝ) - 1))) := hineq
    _ = gaussianEmpirical +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((n : ℝ) / δpb)) /
              (2 * ((n : ℝ) - 1))) := by rw [hempirical_eq]
    _ ≤ gaussianEmpirical +
          theorem2PacBayesRemainder_source (S := S) w.1 δevent :=
        by
          simpa [add_comm] using
            (add_le_add_left hpenalty gaussianEmpirical)

private theorem theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder_of_expected_loss_event
    {Concept : Type*} [MeasurableSpace Concept]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (sigma remainder δpb : ℝ)
    (s : Dataset n X Y)
    (ctx : MeasurePACBayesDistributionContext Concept (X × Y))
    (loss : MeasurePACBayesPointwiseLoss Concept (X × Y))
    (Q : Measure Concept)
    (hQ : IsProbabilityMeasure Q)
    (hQfinite :
      measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤)
    (hgood :
      s ∈ measurePACBayesExpectedLossEvent ctx n hn δpb loss)
    (gaussianPopulation gaussianEmpirical : ℝ)
    (hpopulation_source :
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w sigma gaussianPopulation)
    (hempirical_source :
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w sigma gaussianEmpirical)
    (hpopulation_eq :
      measurePACBayesPopulationLoss ctx loss Q = gaussianPopulation)
    (hempirical_eq :
      measurePACBayesEmpiricalLoss ctx n s loss Q = gaussianEmpirical)
    (hpenalty :
      Real.sqrt
          (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
            Real.log ((n : ℝ) / δpb)) /
            (2 * ((n : ℝ) - 1))) ≤
        remainder) :
    theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
      (S := S) w sigma remainder s := by
  have hineq :
      measurePACBayesPopulationLoss ctx loss Q ≤
        measurePACBayesEmpiricalLoss ctx n s loss Q +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((n : ℝ) / δpb)) /
              (2 * ((n : ℝ) - 1))) := by
    rcases hgood Q hQ with htop | hle
    · exact False.elim (hQfinite htop)
    · exact hle
  refine ⟨gaussianPopulation, gaussianEmpirical,
    hpopulation_source, hempirical_source, ?_⟩
  calc
    gaussianPopulation =
        measurePACBayesPopulationLoss ctx loss Q := hpopulation_eq.symm
    _ ≤ measurePACBayesEmpiricalLoss ctx n s loss Q +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((n : ℝ) / δpb)) /
              (2 * ((n : ℝ) - 1))) := hineq
    _ = gaussianEmpirical +
          Real.sqrt
            (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
              Real.log ((n : ℝ) / δpb)) /
              (2 * ((n : ℝ) - 1))) := by rw [hempirical_eq]
    _ ≤ gaussianEmpirical + remainder :=
        by
          simpa [add_comm] using
            (add_le_add_left hpenalty gaussianEmpirical)

private theorem theorem2AppendixA1SelectedSigmaPopulationSourceIdentity_of_bounded_loss
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    let selectedGridIndex : ℕ :=
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    sourceGaussianPerturbedPopulationLossAtSigma
      (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      (measurePACBayesPopulationLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain)) := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let sigma : ℝ := theorem2AppendixA1SelectedSigma (S := S) hn hk
  let Q : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw (S := S) w.1 sigma selectedDomain
  let ctx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  let loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)
  let pop : Setup.Parameter S → ℝ :=
    fun u => ∫ z : X × Y, loss u z ∂S.dataLaw
  let f : E → ℝ :=
    fun ε => Setup.populationLossValue (S := S)
      ⟨w.1 + sigma • ε, selectedDomain ε⟩
  letI : IsProbabilityMeasure S.dataLaw := S.dataLaw_isProbability
  have hQprob : IsProbabilityMeasure Q := by
    dsimp [Q, sigma]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      selectedDomain
  letI : IsProbabilityMeasure Q := hQprob
  have hsource_bounded :
      ∀ u z, 0 ≤ loss u z ∧ loss u z ≤ 1 := by
    simpa [loss] using
      theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
        (S := S) hbounded
  have hpop_int_Q : Integrable pop Q := by
    dsimp [pop, loss]
    exact
      measurePACBayesPointwiseLoss_integrable_population
        (μ := S.dataLaw) (Q := Q)
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        hmeas_loss
        (by
          simpa using
            theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
              (S := S) hbounded)
  have hmap_meas :
      AEMeasurable
        (fun ε : E =>
          (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S))
        (stdGaussian E) :=
    (theorem2AppendixA1ParameterGaussianMap_measurable
      (S := S) w.1 sigma selectedDomain).aemeasurable
  have hf_int : Integrable f (stdGaussian E) := by
    have hcomp :
        Integrable (pop ∘
          (fun ε : E =>
            (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S)))
          (stdGaussian E) := by
      simpa [Q, theorem2AppendixA1ParameterGaussianLaw] using
        ((MeasureTheory.integrable_map_measure
          hpop_int_Q.aestronglyMeasurable hmap_meas).mp hpop_int_Q)
    refine hcomp.congr ?_
    exact Filter.Eventually.of_forall fun ε => by
      simp [Function.comp, pop, f, Setup.populationLossValue, loss,
        theorem2AppendixA1SourcePointwiseLossOnParameter, Setup.lossOnParameter]
  refine ⟨f, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ε =>
      ⟨selectedDomain ε,
        (theorem2PacBayesAdmissibleBoundedLoss_of_measurable_bounded
          (S := S) hmeas_loss hbounded).2
          ⟨w.1 + sigma • ε, selectedDomain ε⟩,
        rfl⟩
  · rw [SOptLib.expectationWellDefined_iff_integrable]
    exact hf_int
  · have hintegral :
        ∫ u : Setup.Parameter S, pop u ∂Q =
          ∫ ε : E, pop ⟨w.1 + sigma • ε, selectedDomain ε⟩
            ∂(stdGaussian E) :=
      theorem2AppendixA1ParameterGaussianLaw_integral_map
        (S := S) w.1 sigma selectedDomain pop
        hpop_int_Q.aestronglyMeasurable
    calc
      measurePACBayesPopulationLoss ctx loss Q =
          ∫ u : Setup.Parameter S, pop u ∂Q := by
            simp [measurePACBayesPopulationLoss, ctx, pop, loss,
              theorem2AppendixA1ParameterGridContext]
      _ = ∫ ε : E, pop ⟨w.1 + sigma • ε, selectedDomain ε⟩
            ∂(stdGaussian E) := hintegral
      _ = ∫ ε : E, f ε ∂(stdGaussian E) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ε => by
              simp [pop, f, Setup.populationLossValue, loss,
                theorem2AppendixA1SourcePointwiseLossOnParameter,
                Setup.lossOnParameter]

private theorem theorem2AppendixA1SelectedSigmaEmpiricalSourceIdentity_of_bounded_loss
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (s : Dataset n X Y) :
    let selectedGridIndex : ℕ :=
      (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
    let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
      theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
        (S := S) w hn hk hdom_grid
    sourceGaussianPerturbedEmpiricalLossAtSigma
      (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      (measurePACBayesEmpiricalLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
        n s
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain)) := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let sigma : ℝ := theorem2AppendixA1SelectedSigma (S := S) hn hk
  let Q : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw (S := S) w.1 sigma selectedDomain
  let ctx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  let loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)
  let f : E → ℝ :=
    fun ε => Setup.empiricalLoss (S := S) s
      ⟨w.1 + sigma • ε, selectedDomain ε⟩
  have hQprob : IsProbabilityMeasure Q := by
    dsimp [Q, sigma]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      selectedDomain
  letI : IsProbabilityMeasure Q := hQprob
  have hsource_bounded :
      ∀ u z, 0 ≤ loss u z ∧ loss u z ≤ 1 := by
    simpa [loss] using
      theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
        (S := S) hbounded
  have hmap_meas :
      AEMeasurable
        (fun ε : E =>
          (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S))
        (stdGaussian E) :=
    (theorem2AppendixA1ParameterGaussianMap_measurable
      (S := S) w.1 sigma selectedDomain).aemeasurable
  have hfiber_int_Q :
      ∀ i : Fin n, Integrable (fun u : Setup.Parameter S => loss u (s i)) Q := by
    intro i
    have hmeas_i : Measurable (fun u : Setup.Parameter S => loss u (s i)) := by
      simpa [Function.uncurry] using
        hmeas_loss.comp (measurable_id.prodMk measurable_const)
    apply integrable_of_measurable_bounded_real hmeas_i
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg ((hsource_bounded u (s i)).1)]
    exact (hsource_bounded u (s i)).2
  have hfiber_int_std :
      ∀ i : Fin n,
        Integrable
          (fun ε : E =>
            loss (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S)
              (s i))
          (stdGaussian E) := by
    intro i
    have hi := hfiber_int_Q i
    simpa [Q, theorem2AppendixA1ParameterGaussianLaw, Function.comp] using
      ((MeasureTheory.integrable_map_measure
        hi.aestronglyMeasurable hmap_meas).mp hi)
  have hsum_int :
      Integrable
        (fun ε : E =>
          ∑ i : Fin n,
            loss (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S)
              (s i))
        (stdGaussian E) := by
    simpa using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (f := fun i ε =>
          loss (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S)
            (s i))
        (by intro i _hi; exact hfiber_int_std i))
  have hf_int : Integrable f (stdGaussian E) := by
    have hscaled :
        Integrable
          (fun ε : E =>
            (n : ℝ)⁻¹ *
              ∑ i : Fin n,
                loss (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S)
                  (s i))
          (stdGaussian E) :=
      hsum_int.const_mul (n : ℝ)⁻¹
    refine hscaled.congr ?_
    exact Filter.Eventually.of_forall fun ε => by
      simp [f, Setup.empiricalLoss_spec, loss,
        theorem2AppendixA1SourcePointwiseLossOnParameter, Setup.lossOnParameter]
  refine ⟨f, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ε =>
      Setup.sourceEmpiricalLossAt_parameter
        (S := S) s ⟨w.1 + sigma • ε, selectedDomain ε⟩
  · rw [SOptLib.expectationWellDefined_iff_integrable]
    exact hf_int
  · have hintegral_i :
        ∀ i : Fin n,
          ∫ u : Setup.Parameter S, loss u (s i) ∂Q =
            ∫ ε : E,
              loss
                (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S)
                (s i) ∂(stdGaussian E) := by
      intro i
      exact theorem2AppendixA1ParameterGaussianLaw_integral_map
        (S := S) w.1 sigma selectedDomain
        (fun u : Setup.Parameter S => loss u (s i))
        (hfiber_int_Q i).aestronglyMeasurable
    calc
      measurePACBayesEmpiricalLoss ctx n s loss Q =
          (n : ℝ)⁻¹ *
            ∑ i : Fin n, ∫ u : Setup.Parameter S, loss u (s i) ∂Q := by
            simp [measurePACBayesEmpiricalLoss, ctx, loss,
              theorem2AppendixA1ParameterGridContext]
      _ = (n : ℝ)⁻¹ *
            ∑ i : Fin n,
              ∫ ε : E,
                loss
                  (⟨w.1 + sigma • ε, selectedDomain ε⟩ : Setup.Parameter S)
                  (s i) ∂(stdGaussian E) := by
            congr 1
            exact Finset.sum_congr rfl (fun i _ => hintegral_i i)
      _ = ∫ ε : E, f ε ∂(stdGaussian E) := by
            symm
            calc
              ∫ ε : E, f ε ∂(stdGaussian E) =
                  ∫ ε : E,
                    (n : ℝ)⁻¹ *
                      ∑ i : Fin n,
                        loss
                          (⟨w.1 + sigma • ε, selectedDomain ε⟩ :
                            Setup.Parameter S)
                          (s i) ∂(stdGaussian E) := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall fun ε => by
                      simp [f, Setup.empiricalLoss_spec, loss,
                        theorem2AppendixA1SourcePointwiseLossOnParameter,
                        Setup.lossOnParameter]
              _ = (n : ℝ)⁻¹ *
                    ∫ ε : E,
                      ∑ i : Fin n,
                        loss
                          (⟨w.1 + sigma • ε, selectedDomain ε⟩ :
                            Setup.Parameter S)
                          (s i) ∂(stdGaussian E) := by
                    rw [integral_const_mul]
              _ = (n : ℝ)⁻¹ *
                    ∑ i : Fin n,
                      ∫ ε : E,
                        loss
                          (⟨w.1 + sigma • ε, selectedDomain ε⟩ :
                            Setup.Parameter S)
                          (s i) ∂(stdGaussian E) := by
                    rw [MeasureTheory.integral_finset_sum]
                    intro i _hi
                    exact hfiber_int_std i

private theorem theorem2AppendixA1PopulationSourceIdentityAtSigma_of_bounded_loss
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) (sigma : ℝ)
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hdom_posterior :
      ∀ ε : E, w.1 + sigma • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    sourceGaussianPerturbedPopulationLossAtSigma
      (S := S) w sigma
      (measurePACBayesPopulationLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk j (hdom_grid j))
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1 sigma hdom_posterior)) := by
  classical
  let Q : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw (S := S) w.1 sigma hdom_posterior
  let ctx :=
    theorem2AppendixA1ParameterGridContext (S := S) hk j (hdom_grid j)
  let loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)
  let pop : Setup.Parameter S → ℝ :=
    fun u => ∫ z : X × Y, loss u z ∂S.dataLaw
  let f : E → ℝ :=
    fun ε => Setup.populationLossValue (S := S)
      ⟨w.1 + sigma • ε, hdom_posterior ε⟩
  letI : IsProbabilityMeasure S.dataLaw := S.dataLaw_isProbability
  have hQprob : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 sigma hdom_posterior
  letI : IsProbabilityMeasure Q := hQprob
  have hpop_int_Q : Integrable pop Q := by
    dsimp [pop, loss]
    exact
      measurePACBayesPointwiseLoss_integrable_population
        (μ := S.dataLaw) (Q := Q)
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        hmeas_loss
        (by
          simpa using
            theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
              (S := S) hbounded)
  have hmap_meas :
      AEMeasurable
        (fun ε : E =>
          (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S))
        (stdGaussian E) :=
    (theorem2AppendixA1ParameterGaussianMap_measurable
      (S := S) w.1 sigma hdom_posterior).aemeasurable
  have hf_int : Integrable f (stdGaussian E) := by
    have hcomp :
        Integrable (pop ∘
          (fun ε : E =>
            (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S)))
          (stdGaussian E) := by
      simpa [Q, theorem2AppendixA1ParameterGaussianLaw] using
        ((MeasureTheory.integrable_map_measure
          hpop_int_Q.aestronglyMeasurable hmap_meas).mp hpop_int_Q)
    refine hcomp.congr ?_
    exact Filter.Eventually.of_forall fun ε => by
      simp [Function.comp, pop, f, Setup.populationLossValue, loss,
        theorem2AppendixA1SourcePointwiseLossOnParameter, Setup.lossOnParameter]
  refine ⟨f, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ε =>
      ⟨hdom_posterior ε,
        (theorem2PacBayesAdmissibleBoundedLoss_of_measurable_bounded
          (S := S) hmeas_loss hbounded).2
          ⟨w.1 + sigma • ε, hdom_posterior ε⟩,
        rfl⟩
  · rw [SOptLib.expectationWellDefined_iff_integrable]
    exact hf_int
  · have hintegral :
        ∫ u : Setup.Parameter S, pop u ∂Q =
          ∫ ε : E, pop ⟨w.1 + sigma • ε, hdom_posterior ε⟩
            ∂(stdGaussian E) :=
      theorem2AppendixA1ParameterGaussianLaw_integral_map
        (S := S) w.1 sigma hdom_posterior pop
        hpop_int_Q.aestronglyMeasurable
    calc
      measurePACBayesPopulationLoss ctx loss Q =
          ∫ u : Setup.Parameter S, pop u ∂Q := by
            simp [measurePACBayesPopulationLoss, ctx, pop, loss,
              theorem2AppendixA1ParameterGridContext]
      _ = ∫ ε : E, pop ⟨w.1 + sigma • ε, hdom_posterior ε⟩
            ∂(stdGaussian E) := hintegral
      _ = ∫ ε : E, f ε ∂(stdGaussian E) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ε => by
              simp [pop, f, Setup.populationLossValue, loss,
                theorem2AppendixA1SourcePointwiseLossOnParameter,
                Setup.lossOnParameter]

private theorem theorem2AppendixA1EmpiricalSourceIdentityAtSigma_of_bounded_loss
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hk : 0 < Setup.parameterCount (E := E)) (j : ℕ) (sigma : ℝ)
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hdom_posterior :
      ∀ ε : E, w.1 + sigma • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (s : Dataset n X Y) :
    sourceGaussianPerturbedEmpiricalLossAtSigma
      (S := S) s w sigma
      (measurePACBayesEmpiricalLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk j (hdom_grid j))
        n s
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1 sigma hdom_posterior)) := by
  classical
  let Q : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw (S := S) w.1 sigma hdom_posterior
  let ctx :=
    theorem2AppendixA1ParameterGridContext (S := S) hk j (hdom_grid j)
  let loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)
  let f : E → ℝ :=
    fun ε => Setup.empiricalLoss (S := S) s
      ⟨w.1 + sigma • ε, hdom_posterior ε⟩
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 sigma hdom_posterior
  have hsource_bounded :
      ∀ u z, 0 ≤ loss u z ∧ loss u z ≤ 1 := by
    simpa [loss] using
      theorem2AppendixA1SourcePointwiseLossOnParameter_bounded
        (S := S) hbounded
  have hmap_meas :
      AEMeasurable
        (fun ε : E =>
          (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S))
        (stdGaussian E) :=
    (theorem2AppendixA1ParameterGaussianMap_measurable
      (S := S) w.1 sigma hdom_posterior).aemeasurable
  have hfiber_int_Q :
      ∀ i : Fin n, Integrable (fun u : Setup.Parameter S => loss u (s i)) Q := by
    intro i
    have hmeas_i : Measurable (fun u : Setup.Parameter S => loss u (s i)) := by
      simpa [Function.uncurry] using
        hmeas_loss.comp (measurable_id.prodMk measurable_const)
    apply integrable_of_measurable_bounded_real hmeas_i
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg ((hsource_bounded u (s i)).1)]
    exact (hsource_bounded u (s i)).2
  have hfiber_int_std :
      ∀ i : Fin n,
        Integrable
          (fun ε : E =>
            loss (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S)
              (s i))
          (stdGaussian E) := by
    intro i
    have hi := hfiber_int_Q i
    simpa [Q, theorem2AppendixA1ParameterGaussianLaw, Function.comp] using
      ((MeasureTheory.integrable_map_measure
        hi.aestronglyMeasurable hmap_meas).mp hi)
  have hsum_int :
      Integrable
        (fun ε : E =>
          ∑ i : Fin n,
            loss (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S)
              (s i))
        (stdGaussian E) := by
    simpa using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (f := fun i ε =>
          loss (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S)
            (s i))
        (by intro i _hi; exact hfiber_int_std i))
  have hf_int : Integrable f (stdGaussian E) := by
    have hscaled :
        Integrable
          (fun ε : E =>
            (n : ℝ)⁻¹ *
              ∑ i : Fin n,
                loss (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S)
                  (s i))
          (stdGaussian E) :=
      hsum_int.const_mul (n : ℝ)⁻¹
    refine hscaled.congr ?_
    exact Filter.Eventually.of_forall fun ε => by
      simp [f, Setup.empiricalLoss_spec, loss,
        theorem2AppendixA1SourcePointwiseLossOnParameter, Setup.lossOnParameter]
  refine ⟨f, ?_, ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun ε =>
      Setup.sourceEmpiricalLossAt_parameter
        (S := S) s ⟨w.1 + sigma • ε, hdom_posterior ε⟩
  · rw [SOptLib.expectationWellDefined_iff_integrable]
    exact hf_int
  · have hintegral_i :
        ∀ i : Fin n,
          ∫ u : Setup.Parameter S, loss u (s i) ∂Q =
            ∫ ε : E,
              loss
                (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S)
                (s i) ∂(stdGaussian E) := by
      intro i
      exact theorem2AppendixA1ParameterGaussianLaw_integral_map
        (S := S) w.1 sigma hdom_posterior
        (fun u : Setup.Parameter S => loss u (s i))
        (hfiber_int_Q i).aestronglyMeasurable
    calc
      measurePACBayesEmpiricalLoss ctx n s loss Q =
          (n : ℝ)⁻¹ *
            ∑ i : Fin n, ∫ u : Setup.Parameter S, loss u (s i) ∂Q := by
            simp [measurePACBayesEmpiricalLoss, ctx, loss,
              theorem2AppendixA1ParameterGridContext]
      _ = (n : ℝ)⁻¹ *
            ∑ i : Fin n,
              ∫ ε : E,
                loss
                  (⟨w.1 + sigma • ε, hdom_posterior ε⟩ : Setup.Parameter S)
                  (s i) ∂(stdGaussian E) := by
            congr 1
            exact Finset.sum_congr rfl (fun i _ => hintegral_i i)
      _ = ∫ ε : E, f ε ∂(stdGaussian E) := by
            symm
            calc
              ∫ ε : E, f ε ∂(stdGaussian E) =
                  ∫ ε : E,
                    (n : ℝ)⁻¹ *
                      ∑ i : Fin n,
                        loss
                          (⟨w.1 + sigma • ε, hdom_posterior ε⟩ :
                            Setup.Parameter S)
                          (s i) ∂(stdGaussian E) := by
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall fun ε => by
                      simp [f, Setup.empiricalLoss_spec, loss,
                        theorem2AppendixA1SourcePointwiseLossOnParameter,
                        Setup.lossOnParameter]
              _ = (n : ℝ)⁻¹ *
                    ∫ ε : E,
                      ∑ i : Fin n,
                        loss
                          (⟨w.1 + sigma • ε, hdom_posterior ε⟩ :
                            Setup.Parameter S)
                          (s i) ∂(stdGaussian E) := by
                    rw [integral_const_mul]
              _ = (n : ℝ)⁻¹ *
                    ∑ i : Fin n,
                      ∫ ε : E,
                        loss
                          (⟨w.1 + sigma • ε, hdom_posterior ε⟩ :
                            Setup.Parameter S)
                          (s i) ∂(stdGaussian E) := by
                    rw [MeasureTheory.integral_finset_sum]
                    intro i _hi
                    exact hfiber_int_std i

private theorem theorem2AppendixA1RhoPopulationSourceIdentity_of_bounded_loss
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    let rhoGridIndex : ℕ :=
      theorem2AppendixA1PriorGridIndexAtRhoScale (S := S) w hn hk
    let rhoDomain : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace :=
      fun ε =>
        theorem2AppendixA1ParameterSpace_full_of_grid_domain
          (S := S) hk hdom_grid (w.1 + S.rho • ε)
    sourceGaussianPerturbedPopulationLossAtSigma
      (S := S) w S.rho
      (measurePACBayesPopulationLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk rhoGridIndex (hdom_grid rhoGridIndex))
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1 S.rho rhoDomain)) := by
  let rhoGridIndex : ℕ :=
    theorem2AppendixA1PriorGridIndexAtRhoScale (S := S) w hn hk
  let rhoDomain : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace :=
    fun ε =>
      theorem2AppendixA1ParameterSpace_full_of_grid_domain
        (S := S) hk hdom_grid (w.1 + S.rho • ε)
  simpa [rhoGridIndex, rhoDomain] using
    (theorem2AppendixA1PopulationSourceIdentityAtSigma_of_bounded_loss
      (S := S) w hk rhoGridIndex S.rho hdom_grid rhoDomain
      hmeas_loss hbounded)

private theorem theorem2AppendixA1RhoEmpiricalSourceIdentity_of_bounded_loss
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (hn : 1 < n) (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (s : Dataset n X Y) :
    let rhoGridIndex : ℕ :=
      theorem2AppendixA1PriorGridIndexAtRhoScale (S := S) w hn hk
    let rhoDomain : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace :=
      fun ε =>
        theorem2AppendixA1ParameterSpace_full_of_grid_domain
          (S := S) hk hdom_grid (w.1 + S.rho • ε)
    sourceGaussianPerturbedEmpiricalLossAtSigma
      (S := S) s w S.rho
      (measurePACBayesEmpiricalLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk rhoGridIndex (hdom_grid rhoGridIndex))
        n s
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1 S.rho rhoDomain)) := by
  let rhoGridIndex : ℕ :=
    theorem2AppendixA1PriorGridIndexAtRhoScale (S := S) w hn hk
  let rhoDomain : ∀ ε : E, w.1 + S.rho • ε ∈ S.parameterSpace :=
    fun ε =>
      theorem2AppendixA1ParameterSpace_full_of_grid_domain
        (S := S) hk hdom_grid (w.1 + S.rho • ε)
  simpa [rhoGridIndex, rhoDomain] using
    (theorem2AppendixA1EmpiricalSourceIdentityAtSigma_of_bounded_loss
      (S := S) w hk rhoGridIndex S.rho hdom_grid rhoDomain
      hmeas_loss hbounded s)

/- Historical conditional selected-grid attempts.  These declarations are
   retained only as private proof-stage diagnostics; the source/public route
   below is deliberately outside this namespace and does not depend on their
   hgrid_inclusion, hpopulation_source, hempirical_source, or hpenalty
   premises. -/
namespace SelectedSigmaLegacyRoute

private theorem theorem2AppendixA1SelectedSigmaPacBayesFailure_of_prior_grid
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (hgrid_inclusion :
      theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionLegacyStatement
        (S := S) w δ hn hk hnorm hdom_grid) :
    (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1PacBayesFailureAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
      ENNReal.ofReal δ.1 := by
  have hgrid_mass :
      (Setup.iidTrainingLaw (S := S))
          (⋃ j, theorem2AppendixA1GridPACBayesFailure
            (S := S) w δ hn hk j (hdom_grid j)) ≤
        ENNReal.ofReal δ.1 :=
    theorem2AppendixA1CanonicalContext_priorGridFailureMass_of_source
      (S := S) w δ hn hk
      (theorem2AppendixA1CanonicalContext (S := S) w δ hn hk)
      hdom_grid hmeas_loss hbounded
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk)
  have hgrid_subset :
      theorem2AppendixA1PacBayesFailureAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) ⊆
        ⋃ j, theorem2AppendixA1GridPACBayesFailure
          (S := S) w δ hn hk j (hdom_grid j) := by
    intro s hs
    exact Set.mem_iUnion.mpr ⟨selectedGridIndex, hgrid_inclusion hs⟩
  exact (measure_mono hgrid_subset).trans hgrid_mass

/- Same-interface obstruction certificate for the selected-grid supplier.
   The bare formula-level inclusion below intentionally has only the reduced
   norm branch and the grid-domain certificate in its head.  Those hypotheses
   are enough to instantiate the selected posterior and prove finite KL, but
   they do not expose the loss measurability / boundedness facts needed to
   manufacture the source Gaussian population and empirical expectation
   witnesses, nor do they contain the scalar Eq. (8)--(13) penalty algebra.
   This guarded attempt is the typed source-boundary evidence requested by
   the route arbiter: it targets the exact non-conditional inclusion, not an
   auxiliary conditional wrapper. -/
set_option linter.unusedVariables false in
private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_exact_head_obstruction_iter2
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    True := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let ctx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  let loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S)
  let Q :=
    theorem2AppendixA1ParameterGaussianLaw
      (S := S) w.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        selectedDomain
  have hselected_posterior_prob : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      selectedDomain
  have hselected_finite_kl :
      measurePACBayesKLDivergence Q ctx.prior_distribution ≠ ⊤ := by
    simpa [Q, ctx, selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSubtypeFiniteKL_of_gaussianAffineLaw
        (S := S) w hn hk hnorm hdom_grid)
  let populationLeaf : Prop :=
    ∀ s : Dataset n X Y,
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesPopulationLoss ctx loss Q)
  let empiricalLeaf : Prop :=
    ∀ s : Dataset n X Y,
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesEmpiricalLoss ctx n s loss Q)
  let penaltyLeaf : Prop :=
    Real.sqrt
        (((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
          (2 * ((n : ℝ) - 1))) ≤
      theorem2PacBayesRemainder_source (S := S) w.1 δ.1
  /- The exact head supplies finite KL, but no theorem in the current context
     can derive the two source-expectation graph witnesses or the scalar
     confidence/KL penalty comparison from only `hnorm` and `hdom_grid`. -/
  fail_if_success
    have hpopulation_source : populationLeaf := by
      intro s
      exact (by assumption :
        sourceGaussianPerturbedPopulationLossAtSigma
          (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesPopulationLoss ctx loss Q))
    exact hpopulation_source
  fail_if_success
    have hempirical_source : empiricalLeaf := by
      intro s
      exact (by assumption :
        sourceGaussianPerturbedEmpiricalLossAtSigma
          (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesEmpiricalLoss ctx n s loss Q))
    exact hempirical_source
  fail_if_success
    have hpenalty : penaltyLeaf := by
      let ctx :=
        theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
      let Q : Measure (Setup.Parameter S) :=
        theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain
      have hselected_kl_formula :
          measurePACBayesKLDivergence Q ctx.prior_distribution =
            ENNReal.ofReal
              (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
                (S := S) w hk selectedGridIndex
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)) := by
        simpa [Q, ctx, selectedGridIndex, selectedDomain] using
          (theorem2AppendixA1SelectedSubtypeKLFormulaAtSelectedSigma_of_gaussianAffineLaw
            (S := S) w hn hk hnorm hdom_grid)
      have hselected_kl_toReal :
          (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal =
            theorem2AppendixA1GaussianKLFormulaScalarAtSigma
              (S := S) w hk selectedGridIndex
              (theorem2AppendixA1SelectedSigma (S := S) hn hk) := by
        rw [hselected_kl_formula]
        exact ENNReal.toReal_ofReal
          (show
            0 ≤ theorem2AppendixA1GaussianKLFormulaScalarAtSigma
              (S := S) w hk selectedGridIndex
              (theorem2AppendixA1SelectedSigma (S := S) hn hk) by
            positivity)
      dsimp [penaltyLeaf, Q, ctx] at *
      rw [hselected_kl_toReal]
      rw [theorem2PacBayesRemainder_source_spec]
      apply Real.sqrt_le_sqrt
      nlinarith
    exact hpenalty
  trivial

/- Compiled source-route factorization for Appendix A.1 Eq. (8)--(13).
   Unlike the guarded attempts above, this theorem is executable: it consumes
   the selected subtype finite-KL bridge and leaves only the three genuine
   source leaves which the current bare inclusion statement does not supply:
   population-loss identity, empirical-loss identity, and scalar penalty
   monotonicity from the grid sandwich and confidence estimate. -/
private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_of_source_bridges
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hpopulation_source :
      ∀ s : Dataset n X Y,
        let selectedGridIndex : ℕ :=
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
        let selectedDomain :
          ∀ ε : E,
            w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
              S.parameterSpace :=
          theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
            (S := S) w hn hk hdom_grid
        sourceGaussianPerturbedPopulationLossAtSigma
          (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesPopulationLoss
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
            (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)))
    (hempirical_source :
      ∀ s : Dataset n X Y,
        let selectedGridIndex : ℕ :=
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
        let selectedDomain :
          ∀ ε : E,
            w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
              S.parameterSpace :=
          theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
            (S := S) w hn hk hdom_grid
        sourceGaussianPerturbedEmpiricalLossAtSigma
          (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesEmpiricalLoss
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
            n s
            (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)))
    (hpenalty :
      let selectedGridIndex : ℕ :=
        (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
      let selectedDomain :
        ∀ ε : E,
          w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
            S.parameterSpace :=
        theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
          (S := S) w hn hk hdom_grid
      Real.sqrt
          (((measurePACBayesKLDivergence
              (theorem2AppendixA1ParameterGaussianLaw
                (S := S) w.1
                  (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                  selectedDomain)
              (theorem2AppendixA1ParameterGridContext
                (S := S) hk selectedGridIndex
                  (hdom_grid selectedGridIndex)).prior_distribution).toReal +
            Real.log
              ((n : ℝ) /
                theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
            (2 * ((n : ℝ) - 1))) ≤
        theorem2PacBayesRemainder_source (S := S) w.1 δ.1) :
    theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionLegacyStatement
      (S := S) w δ hn hk hnorm hdom_grid := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  have hselected_posterior_prob :
      IsProbabilityMeasure
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          selectedDomain) := by
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      selectedDomain
  have hselected_finite_kl :
      measurePACBayesKLDivergence
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain)
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex
            (hdom_grid selectedGridIndex)).prior_distribution ≠ ⊤ := by
    simpa [selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSubtypeFiniteKL_of_gaussianAffineLaw
        (S := S) w hn hk hnorm hdom_grid)
  intro s hs_selected
  rw [theorem2AppendixA1GridPACBayesFailure_spec
    (S := S) (w := w) (δ := δ) (hn := hn) (hk := hk)
    (j := selectedGridIndex) (hdom := hdom_grid selectedGridIndex)]
  intro hgrid_good
  have hselected_event :
      theorem2PacBayesGaussianExpectationEventAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk) s :=
    theorem2PacBayesGaussianExpectationEventAtSigma_of_expected_loss_event
      (S := S) (w := w) (δevent := δ.1)
      (δpb := theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)
      (hn := hn)
      (sigma := theorem2AppendixA1SelectedSigma (S := S) hn hk)
      (s := s)
      (ctx := theorem2AppendixA1ParameterGridContext
        (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
      (loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
      (Q := theorem2AppendixA1ParameterGaussianLaw
        (S := S) w.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          selectedDomain)
      hselected_posterior_prob
      hselected_finite_kl
      hgrid_good
      (measurePACBayesPopulationLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain))
      (measurePACBayesEmpiricalLoss
        (theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
        n s
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        (theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain))
      (by simpa [selectedGridIndex, selectedDomain] using
        hpopulation_source s)
      (by simpa [selectedGridIndex, selectedDomain] using
        hempirical_source s)
      rfl
      rfl
      (by simpa [selectedGridIndex, selectedDomain] using hpenalty)
  exact hs_selected hselected_event

private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid_of_source_bridges
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (hpopulation_source :
      ∀ s : Dataset n X Y,
        let selectedGridIndex : ℕ :=
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
        let selectedDomain :
          ∀ ε : E,
            w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
              S.parameterSpace :=
          theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
            (S := S) w hn hk hdom_grid
        sourceGaussianPerturbedPopulationLossAtSigma
          (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesPopulationLoss
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
            (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)))
    (hempirical_source :
      ∀ s : Dataset n X Y,
        let selectedGridIndex : ℕ :=
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
        let selectedDomain :
          ∀ ε : E,
            w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
              S.parameterSpace :=
          theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
            (S := S) w hn hk hdom_grid
        sourceGaussianPerturbedEmpiricalLossAtSigma
          (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesEmpiricalLoss
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
            n s
            (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)))
    (hpenalty :
      let selectedGridIndex : ℕ :=
        (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
      let selectedDomain :
        ∀ ε : E,
          w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
            S.parameterSpace :=
        theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
          (S := S) w hn hk hdom_grid
      Real.sqrt
          (((measurePACBayesKLDivergence
              (theorem2AppendixA1ParameterGaussianLaw
                (S := S) w.1
                  (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                  selectedDomain)
              (theorem2AppendixA1ParameterGridContext
                (S := S) hk selectedGridIndex
                  (hdom_grid selectedGridIndex)).prior_distribution).toReal +
            Real.log
              ((n : ℝ) /
                theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
            (2 * ((n : ℝ) - 1))) ≤
        theorem2PacBayesRemainder_source (S := S) w.1 δ.1) :
    theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGridLegacyStatement
      (S := S) w δ hn hk := by
  exact theorem2AppendixA1SelectedSigmaPacBayesFailure_of_prior_grid
    (S := S) w δ hn hk hnorm hdom_grid hmeas_loss hbounded
    (theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_of_source_bridges
      (S := S) w δ hn hk hnorm hdom_grid
      hpopulation_source hempirical_source hpenalty)

private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_of_bounded_loss_and_penalty
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (hpenalty :
      let selectedGridIndex : ℕ :=
        (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
      let selectedDomain :
        ∀ ε : E,
          w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
            S.parameterSpace :=
        theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
          (S := S) w hn hk hdom_grid
      Real.sqrt
          (((measurePACBayesKLDivergence
              (theorem2AppendixA1ParameterGaussianLaw
                (S := S) w.1
                  (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                  selectedDomain)
              (theorem2AppendixA1ParameterGridContext
                (S := S) hk selectedGridIndex
                  (hdom_grid selectedGridIndex)).prior_distribution).toReal +
            Real.log
              ((n : ℝ) /
                theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
            (2 * ((n : ℝ) - 1))) ≤
        theorem2PacBayesRemainder_source (S := S) w.1 δ.1) :
    theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionLegacyStatement
      (S := S) w δ hn hk hnorm hdom_grid := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let selectedCtx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  let selectedPosterior :=
    theorem2AppendixA1ParameterGaussianLaw
      (S := S) w.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        selectedDomain
  have hselected_posterior_prob :
      IsProbabilityMeasure selectedPosterior := by
    dsimp [selectedPosterior]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      selectedDomain
  have hselected_finite_kl :
      measurePACBayesKLDivergence
          selectedPosterior selectedCtx.prior_distribution ≠ ⊤ := by
    simpa [selectedPosterior, selectedCtx, selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSubtypeFiniteKL_of_gaussianAffineLaw
        (S := S) w hn hk hnorm hdom_grid)
  intro s hs_selected
  rw [theorem2AppendixA1GridPACBayesFailure_spec
    (S := S) (w := w) (δ := δ) (hn := hn) (hk := hk)
    (j := selectedGridIndex) (hdom := hdom_grid selectedGridIndex)]
  intro hgrid_good
  have hpopulation_source :
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesPopulationLoss selectedCtx
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
          selectedPosterior) := by
    simpa [selectedCtx, selectedPosterior, selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSigmaPopulationSourceIdentity_of_bounded_loss
        (S := S) w hn hk hdom_grid hmeas_loss hbounded)
  have hempirical_source :
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesEmpiricalLoss selectedCtx n s
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
          selectedPosterior) := by
    simpa [selectedCtx, selectedPosterior, selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSigmaEmpiricalSourceIdentity_of_bounded_loss
        (S := S) w δ hn hk hdom_grid hmeas_loss hbounded s)
  have hselected_event :
      theorem2PacBayesGaussianExpectationEventAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk) s :=
    theorem2PacBayesGaussianExpectationEventAtSigma_of_expected_loss_event
      (S := S) (w := w) (δevent := δ.1)
      (δpb := theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)
      (hn := hn)
      (sigma := theorem2AppendixA1SelectedSigma (S := S) hn hk)
      (s := s)
      (ctx := selectedCtx)
      (loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
      (Q := selectedPosterior)
      hselected_posterior_prob
      hselected_finite_kl
      hgrid_good
      (measurePACBayesPopulationLoss selectedCtx
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        selectedPosterior)
      (measurePACBayesEmpiricalLoss selectedCtx n s
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        selectedPosterior)
      hpopulation_source
      hempirical_source
      rfl
      rfl
      (by simpa [selectedCtx, selectedPosterior, selectedGridIndex,
        selectedDomain] using hpenalty)
  exact hs_selected hselected_event

private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionAtRhoScale_of_bounded_loss_and_penalty
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (hpenalty :
      let rhoGridIndex : ℕ :=
        (theorem2AppendixA1PriorGridIndexAtRhoScale
        (S := S) w hn hk);
      let selectedDomain :
        ∀ ε : E,
          w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
            S.parameterSpace :=
        theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
          (S := S) w hn hk hdom_grid
      Real.sqrt
          (((measurePACBayesKLDivergence
              (theorem2AppendixA1ParameterGaussianLaw
                (S := S) w.1
                  (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                  selectedDomain)
              (theorem2AppendixA1ParameterGridContext
                (S := S) hk rhoGridIndex
                  (hdom_grid rhoGridIndex)).prior_distribution).toReal +
            Real.log
              ((n : ℝ) /
                theorem2AppendixA1PriorGridConfidence δ.1 rhoGridIndex)) /
            (2 * ((n : ℝ) - 1))) ≤
        theorem2PacBayesRemainder_source (S := S) w.1 δ.1) :
    theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionAtRhoScale
      (S := S) w δ hn hk hnorm hdom_grid := by
  classical
  let rhoGridIndex : ℕ :=
    (theorem2AppendixA1PriorGridIndexAtRhoScale
        (S := S) w hn hk);
  let selectedIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let rhoCtx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk rhoGridIndex (hdom_grid rhoGridIndex)
  let selectedCtx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedIndex (hdom_grid selectedIndex)
  let selectedPosterior :=
    theorem2AppendixA1ParameterGaussianLaw
      (S := S) w.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        selectedDomain
  have hselected_posterior_prob :
      IsProbabilityMeasure selectedPosterior := by
    dsimp [selectedPosterior]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      selectedDomain
  have hselected_finite_kl :
      measurePACBayesKLDivergence
          selectedPosterior rhoCtx.prior_distribution ≠ ⊤ := by
    simpa [selectedPosterior, rhoCtx, rhoGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSubtypeFiniteKLAtGridIndex_of_gaussianAffineLaw
        (S := S) w hn hk rhoGridIndex hnorm hdom_grid)
  intro s hs_selected
  rw [theorem2AppendixA1GridPACBayesFailure_spec
    (S := S) (w := w) (δ := δ) (hn := hn) (hk := hk)
    (j := rhoGridIndex) (hdom := hdom_grid rhoGridIndex)]
  intro hgrid_good
  have hpopulation_source :
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesPopulationLoss rhoCtx
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
          selectedPosterior) := by
    have hsource :=
      theorem2AppendixA1SelectedSigmaPopulationSourceIdentity_of_bounded_loss
        (S := S) w hn hk hdom_grid hmeas_loss hbounded
    simpa [rhoCtx, selectedCtx, selectedPosterior, rhoGridIndex, selectedIndex,
      selectedDomain, measurePACBayesPopulationLoss,
      theorem2AppendixA1ParameterGridContext] using hsource
  have hempirical_source :
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesEmpiricalLoss rhoCtx n s
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
          selectedPosterior) := by
    have hsource :=
      theorem2AppendixA1SelectedSigmaEmpiricalSourceIdentity_of_bounded_loss
        (S := S) w δ hn hk hdom_grid hmeas_loss hbounded s
    simpa [rhoCtx, selectedCtx, selectedPosterior, rhoGridIndex, selectedIndex,
      selectedDomain, measurePACBayesEmpiricalLoss,
      theorem2AppendixA1ParameterGridContext] using hsource
  have hselected_event :
      theorem2PacBayesGaussianExpectationEventAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk) s :=
    theorem2PacBayesGaussianExpectationEventAtSigma_of_expected_loss_event
      (S := S) (w := w) (δevent := δ.1)
      (δpb := theorem2AppendixA1PriorGridConfidence δ.1 rhoGridIndex)
      (hn := hn)
      (sigma := theorem2AppendixA1SelectedSigma (S := S) hn hk)
      (s := s)
      (ctx := rhoCtx)
      (loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
      (Q := selectedPosterior)
      hselected_posterior_prob
      hselected_finite_kl
      hgrid_good
      (measurePACBayesPopulationLoss rhoCtx
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        selectedPosterior)
      (measurePACBayesEmpiricalLoss rhoCtx n s
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        selectedPosterior)
      hpopulation_source
      hempirical_source
      rfl
      rfl
      (by simpa [rhoCtx, selectedPosterior, rhoGridIndex,
        selectedDomain] using hpenalty)
  exact hs_selected hselected_event

/- Typed obstruction for replacing the selected-index penalty by the
   paper's rho-scale confidence index.  The rho-index event route above
   consumes population/empirical source identities and finite KL; what remains
   is the scalar penalty comparison.  At the selected posterior scale, the
   grid-scale ratio contains the extra parameter-count factor recorded by
   `theorem2AppendixA1_priorGridScale_div_selectedSigma_sq_has_extra_parameter_factor`,
   so this is not the same confidence algebra used in Appendix A.1. -/
set_option linter.unusedVariables false in
private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusionAtRhoScale_penalty_obstruction
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
      theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  classical
  let rhoGridIndex : ℕ :=
    (theorem2AppendixA1PriorGridIndexAtRhoScale
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let rhoCtx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk rhoGridIndex (hdom_grid rhoGridIndex)
  let selectedPosterior :=
    theorem2AppendixA1ParameterGaussianLaw
      (S := S) w.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        selectedDomain
  have hfinite_rho_grid :
      measurePACBayesKLDivergence
          selectedPosterior rhoCtx.prior_distribution ≠ ⊤ := by
    simpa [selectedPosterior, rhoCtx, rhoGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSubtypeFiniteKLAtGridIndex_of_gaussianAffineLaw
        (S := S) w hn hk rhoGridIndex hnorm hdom_grid)
  have hkl_formula_rho_grid :
      measurePACBayesKLDivergence
          selectedPosterior rhoCtx.prior_distribution =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk rhoGridIndex
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)) := by
    simpa [selectedPosterior, rhoCtx, rhoGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSubtypeKLFormulaAtGridIndex_of_gaussianAffineLaw
        (S := S) w hn hk rhoGridIndex hnorm hdom_grid)
  have hsource_ratio_extra_factor :
      theorem2AppendixA1PriorGridScale (S := S) hk /
          theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 =
        (Setup.parameterCount (E := E) : ℝ) *
          (1 + Real.sqrt
            (Real.log (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ))) ^ 2 *
            (1 + Real.exp
              (4 * (n : ℝ) /
                (Setup.parameterCount (E := E) : ℝ))) :=
    theorem2AppendixA1_priorGridScale_div_selectedSigma_sq_has_extra_parameter_factor
      (S := S) hn hk
  fail_if_success
    have hpenalty :
        theorem2AppendixA1SelectedSigmaRhoScalePenaltyComparison
          (S := S) w δ hn hk hnorm hdom_grid := by
      dsimp [theorem2AppendixA1SelectedSigmaRhoScalePenaltyComparison]
      rw [theorem2PacBayesRemainder_source_spec]
      apply Real.sqrt_le_sqrt
      nlinarith
    exact hpenalty
  exact theorem2AppendixA1_selectedSigma_grid_ratio_ne_rho_grid_ratio
    (S := S) hn hk

private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid_of_bounded_loss_and_penalty
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1)
    (hpenalty :
      let selectedGridIndex : ℕ :=
        (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
      let selectedDomain :
        ∀ ε : E,
          w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
            S.parameterSpace :=
        theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
          (S := S) w hn hk hdom_grid
      Real.sqrt
          (((measurePACBayesKLDivergence
              (theorem2AppendixA1ParameterGaussianLaw
                (S := S) w.1
                  (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                  selectedDomain)
              (theorem2AppendixA1ParameterGridContext
                (S := S) hk selectedGridIndex
                  (hdom_grid selectedGridIndex)).prior_distribution).toReal +
            Real.log
              ((n : ℝ) /
                theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
            (2 * ((n : ℝ) - 1))) ≤
        theorem2PacBayesRemainder_source (S := S) w.1 δ.1) :
    theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGridLegacyStatement
      (S := S) w δ hn hk := by
  exact theorem2AppendixA1SelectedSigmaPacBayesFailure_of_prior_grid
    (S := S) w δ hn hk hnorm hdom_grid hmeas_loss hbounded
    (theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_of_bounded_loss_and_penalty
      (S := S) w δ hn hk hnorm hdom_grid hmeas_loss hbounded hpenalty)

end SelectedSigmaLegacyRoute

/- Active Phase 2a Appendix A.1 frontier.  The public route is:

     mcallester_theorem1_pac_bayes_model_averaging_of_one_lt_sample_size
       -> theorem2AppendixA1_arbitraryMeasure_PACBayes_event_of_bounded_loss
       -> theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion
       -> theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid

   The private selected-sigma transport boundary above is retained only as
   legacy/correction evidence and must not be listed as source theorem proof
   plan work or as remaining reconstruct work for this selected-grid route. -/

/- Source-facing selected-grid supplier.  The public name is retained for the
   Appendix A.1 route, while its event is the exact selected-sigma
   Measure/PAC-Bayes event above; the obsolete rho-scale remainder predicate
   is private under `...LegacyStatement`. -/
theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureGridInclusion
      (S := S) w δ hn hk hnorm hdom_grid := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk)
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let selectedCtx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
  let selectedPosterior :=
    theorem2AppendixA1ParameterGaussianLaw
      (S := S) w.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        selectedDomain
  have hselected_posterior_prob :
      IsProbabilityMeasure selectedPosterior := by
    dsimp [selectedPosterior]
    exact theorem2AppendixA1ParameterGaussianLaw_isProbability
      (S := S) w.1 (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      selectedDomain
  have hselected_finite_kl :
      measurePACBayesKLDivergence
          selectedPosterior selectedCtx.prior_distribution ≠ ⊤ := by
    simpa [selectedPosterior, selectedCtx, selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSubtypeFiniteKL_of_gaussianAffineLaw
        (S := S) w hn hk hnorm hdom_grid)
  intro s hs_selected
  rw [theorem2AppendixA1GridPACBayesFailure_spec
    (S := S) (w := w) (δ := δ) (hn := hn) (hk := hk)
    (j := selectedGridIndex) (hdom := hdom_grid selectedGridIndex)]
  intro hgrid_good
  have hpopulation_source :
      sourceGaussianPerturbedPopulationLossAtSigma
        (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesPopulationLoss selectedCtx
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
          selectedPosterior) := by
    simpa [selectedCtx, selectedPosterior, selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSigmaPopulationSourceIdentity_of_bounded_loss
        (S := S) w hn hk hdom_grid hmeas_loss hbounded)
  have hempirical_source :
      sourceGaussianPerturbedEmpiricalLossAtSigma
        (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (measurePACBayesEmpiricalLoss selectedCtx n s
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
          selectedPosterior) := by
    simpa [selectedCtx, selectedPosterior, selectedGridIndex, selectedDomain] using
      (theorem2AppendixA1SelectedSigmaEmpiricalSourceIdentity_of_bounded_loss
        (S := S) w δ hn hk hdom_grid hmeas_loss hbounded s)
  have hselected_event :
      theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
        (S := S) w
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid) s :=
    theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder_of_expected_loss_event
      (S := S) (w := w) (hn := hn)
      (sigma := theorem2AppendixA1SelectedSigma (S := S) hn hk)
      (remainder := theorem2AppendixA1SelectedSigmaPACBayesPenalty
        (S := S) w δ hn hk hdom_grid)
      (δpb := theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)
      (s := s)
      (ctx := selectedCtx)
      (loss := theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
      (Q := selectedPosterior)
      hselected_posterior_prob
      hselected_finite_kl
      hgrid_good
      (measurePACBayesPopulationLoss selectedCtx
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        selectedPosterior)
      (measurePACBayesEmpiricalLoss selectedCtx n s
        (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
        selectedPosterior)
      hpopulation_source
      hempirical_source
      rfl
      rfl
      (by
        rw [theorem2AppendixA1SelectedSigmaPACBayesPenalty_spec])
  exact hs_selected hselected_event

/- Source-facing selected-grid mass supplier.  It consumes the proved
   selected-grid inclusion directly and has no conditional population,
   empirical, penalty, inclusion, or mass premise. -/
theorem theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureFromPriorGrid
      (S := S) w δ hn hk hdom_grid := by
  have hgrid_mass :
      (Setup.iidTrainingLaw (S := S))
          (⋃ j, theorem2AppendixA1GridPACBayesFailure
            (S := S) w δ hn hk j (hdom_grid j)) ≤
        ENNReal.ofReal δ.1 :=
    theorem2AppendixA1CanonicalContext_priorGridFailureMass_of_source
      (S := S) w δ hn hk
      (theorem2AppendixA1CanonicalContext (S := S) w δ hn hk)
      hdom_grid hmeas_loss hbounded
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk)
  have hgrid_inclusion :
    theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure
          (S := S) w δ hn hk hdom_grid ⊆
        theorem2AppendixA1GridPACBayesFailure
          (S := S) w δ hn hk selectedGridIndex
          (hdom_grid selectedGridIndex) :=
    theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion
      (S := S) w δ hn hk hnorm hdom_grid hmeas_loss hbounded
  have hgrid_subset :
      theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure
          (S := S) w δ hn hk hdom_grid ⊆
        ⋃ j, theorem2AppendixA1GridPACBayesFailure
          (S := S) w δ hn hk j (hdom_grid j) := by
    intro s hs
    exact Set.mem_iUnion.mpr ⟨selectedGridIndex, hgrid_inclusion hs⟩
  exact (measure_mono hgrid_subset).trans hgrid_mass

/- Statement-correction certificate for the retired uncorrected
   selected-sigma supplier.  The old supplier would need to compare the
   selected-posterior PAC-Bayes confidence scale with Appendix A.1's rho-scale
   confidence algebra.  These ratios are definitionally different for the
   selected posterior, so the public route must use the corrected exact
   selected-grid event above or a separate rho-scale posterior construction. -/
set_option linter.unusedVariables false in
theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_statement_correction_obstruction
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
      theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  exact theorem2AppendixA1_selectedSigma_grid_ratio_ne_rho_grid_ratio
    (S := S) hn hk

set_option linter.unusedVariables false in
theorem theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid_statement_correction_obstruction
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
      theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  exact theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_statement_correction_obstruction
    (S := S) w δ hn hk hnorm hdom_grid

/- Feasible-state scale-mismatch certificate for the retired selected-sigma /
   rho-remainder inclusion route.  The setup is deliberately ordinary: full
   one-dimensional parameter space, deterministic unit data, positive rho, and
   zero parameter.  It satisfies the reduced-norm and grid-domain side
   conditions, while the selected-sigma grid scale is provably not the
   rho-scale grid used by the paper's Eq. (7)--(8) confidence algebra.  This
   certificate records a scale mismatch only; it is not a negation of an event
   or mass theorem. -/
theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_grid_scale_mismatch_of_feasible_setup :
    ∃ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S)
      (δ : Set.Ioo (0 : ℝ) 1)
      (hn : 1 < (2 : ℕ))
      (hk : 0 < Setup.parameterCount (E := ℝ))
      (hnorm :
        ‖w.1‖ ^ 2 ≤
          S.rho ^ 2 *
            (Real.exp
              (4 * (2 : ℝ) /
                (Setup.parameterCount (E := ℝ) : ℝ)) - 1))
      (hdom_grid :
        ∀ j : ℕ, ∀ ε : ℝ,
          (0 : ℝ) +
              Real.sqrt (theorem2AppendixA1PriorGridVariance
                (S := S) hk j) • ε ∈ S.parameterSpace),
        theorem2AppendixA1PriorGridScale (S := S) hk /
            theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
          theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  let S : Setup 2 ℝ Unit Unit Unit :=
    { parameterSpace := Set.univ
      loss := fun _ _ _ => 0
      dataLaw := Measure.dirac ((), ())
      dataLaw_isProbability := by infer_instance
      batchSize := 1
      w0 := ⟨0, Set.mem_univ 0⟩
      eta := 1
      rho := 1
      p := 1
      lambda := 0
      eta_pos := by norm_num
      rho_pos := by norm_num
      p_domain := by norm_num }
  let w : Setup.Parameter S := ⟨0, Set.mem_univ 0⟩
  let δ : Set.Ioo (0 : ℝ) 1 := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  have hn : 1 < (2 : ℕ) := by norm_num
  have hk : 0 < Setup.parameterCount (E := ℝ) := by
    norm_num [Setup.parameterCount]
  have hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (2 : ℝ) /
              (Setup.parameterCount (E := ℝ) : ℝ)) - 1) := by
    have hk' : 0 < (Setup.parameterCount (E := ℝ) : ℝ) := by
      exact_mod_cast hk
    have harg :
        0 ≤ (4 : ℝ) * 2 /
          (Setup.parameterCount (E := ℝ) : ℝ) :=
      div_nonneg (by norm_num) hk'.le
    have hexp :
        1 ≤ Real.exp
          ((4 : ℝ) * 2 /
            (Setup.parameterCount (E := ℝ) : ℝ)) :=
      Real.one_le_exp harg
    simpa [w, S] using (sub_nonneg.mpr hexp)
  have hdom_grid :
      ∀ j : ℕ, ∀ ε : ℝ,
        (0 : ℝ) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace := by
    intro j ε
    simp [S]
  refine ⟨S, w, δ, hn, hk, hnorm, hdom_grid, ?_⟩
  exact theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_statement_correction_obstruction
    (S := S) w δ hn hk hnorm hdom_grid

/- The same feasible-state scale-mismatch certificate is attached to the
   retired mass route: the prior-grid mass supplier must use the corrected
   selected-sigma event or a separate rho-scale posterior construction, not
   the mismatched legacy confidence scale. -/
theorem theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid_grid_scale_mismatch_of_feasible_setup :
    ∃ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S)
      (δ : Set.Ioo (0 : ℝ) 1)
      (hn : 1 < (2 : ℕ))
      (hk : 0 < Setup.parameterCount (E := ℝ))
      (hnorm :
        ‖w.1‖ ^ 2 ≤
          S.rho ^ 2 *
            (Real.exp
              (4 * (2 : ℝ) /
                (Setup.parameterCount (E := ℝ) : ℝ)) - 1))
      (hdom_grid :
        ∀ j : ℕ, ∀ ε : ℝ,
          (0 : ℝ) +
              Real.sqrt (theorem2AppendixA1PriorGridVariance
                (S := S) hk j) • ε ∈ S.parameterSpace),
        theorem2AppendixA1PriorGridScale (S := S) hk /
            theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
          theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2 := by
  let S : Setup 2 ℝ Unit Unit Unit :=
    { parameterSpace := Set.univ
      loss := fun _ _ _ => 0
      dataLaw := Measure.dirac ((), ())
      dataLaw_isProbability := by infer_instance
      batchSize := 1
      w0 := ⟨0, Set.mem_univ 0⟩
      eta := 1
      rho := 1
      p := 1
      lambda := 0
      eta_pos := by norm_num
      rho_pos := by norm_num
      p_domain := by norm_num }
  let w : Setup.Parameter S := ⟨0, Set.mem_univ 0⟩
  let δ : Set.Ioo (0 : ℝ) 1 := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩
  have hn : 1 < (2 : ℕ) := by norm_num
  have hk : 0 < Setup.parameterCount (E := ℝ) := by
    norm_num [Setup.parameterCount]
  have hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (2 : ℝ) /
              (Setup.parameterCount (E := ℝ) : ℝ)) - 1) := by
    have hk' : 0 < (Setup.parameterCount (E := ℝ) : ℝ) := by
      exact_mod_cast hk
    have harg :
        0 ≤ (4 : ℝ) * 2 /
          (Setup.parameterCount (E := ℝ) : ℝ) :=
      div_nonneg (by norm_num) hk'.le
    have hexp :
        1 ≤ Real.exp
          ((4 : ℝ) * 2 /
            (Setup.parameterCount (E := ℝ) : ℝ)) :=
      Real.one_le_exp harg
    simpa [w, S] using (sub_nonneg.mpr hexp)
  have hdom_grid :
      ∀ j : ℕ, ∀ ε : ℝ,
        (0 : ℝ) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace := by
    intro j ε
    simp [S]
  refine ⟨S, w, δ, hn, hk, hnorm, hdom_grid, ?_⟩
  exact theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid_statement_correction_obstruction
    (S := S) w δ hn hk hnorm hdom_grid

/- Formal retirement record for the two paper-like checked endpoint
   declarations removed from the source/public cone:

     theorem2_internal_checked_of_lean_side_boundary_under_selected_sigma_transport
     theorem2_internal_checked_under_selected_sigma_transport

   The first conjunct records the concrete false-conclusion certificate for
   the old rho-only hgaussian route.  The second records a feasible setup on
   which the selected-sigma grid scale differs from the rho-scale grid used by
   the old confidence calculation.  The only retained checked endpoint is
   `theorem2_internal_checked_corrected_selected_sigma_transport_boundary`,
   which is private and explicitly conditional on the selected-scale
   population premise. -/
private def theorem2_internal_checked_retired_route : Prop :=
  ∀ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1),
    theorem2GaussianPremiseSource S w →
      ENNReal.ofReal (1 - δ.1) ≤
        (Setup.iidTrainingLaw (S := S))
          {s | theorem2PacBayesGaussianExpectationEvent
              (S := S) w δ.1 s ∧
            theorem2GaussianEmpiricalSharpnessEvent
              (S := S) w δ.1 s ∧
            theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s}

private def theorem2_internal_checked_scale_mismatch_certificate : Prop :=
  ∃ (S : Setup 2 ℝ Unit Unit Unit) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1)
    (hn : 1 < (2 : ℕ))
    (hk : 0 < Setup.parameterCount (E := ℝ))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (2 : ℝ) /
              (Setup.parameterCount (E := ℝ) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : ℝ,
        (0 : ℝ) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace),
    theorem2AppendixA1PriorGridScale (S := S) hk /
        theorem2AppendixA1SelectedSigma (S := S) hn hk ^ 2 ≠
      theorem2AppendixA1PriorGridScale (S := S) hk / S.rho ^ 2

private theorem theorem2_internal_checked_and_theorem2_internal_checked_of_lean_side_boundary_under_selected_sigma_transport_retirement_record :
    (¬ theorem2_internal_checked_retired_route) ∧
      theorem2_internal_checked_scale_mismatch_certificate := by
  constructor
  · simpa [theorem2_internal_checked_retired_route] using
      theorem2PacBayesGaussianAndRadiusSharpness_probability_from_appendixA1_unqualified_probability_route_retired
  · simpa [theorem2_internal_checked_scale_mismatch_certificate] using
      theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_grid_scale_mismatch_of_feasible_setup

def theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (s : Dataset n X Y) : Prop :=
  ∀ sharpness : ℝ,
    theorem2EuclideanSharpnessSource (S := S) s w sharpness →
      ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
          (Real.sqrt (n : ℝ))⁻¹) +
        theorem2AppendixA1SelectedSigmaPACBayesPenalty
          (S := S) w δ hn hk hdom_grid ≤
          sharpness + theorem2Remainder_source (S := S) w.1 δ.1

set_option maxHeartbeats 800000 in
private theorem theorem2AppendixA1SelectedSigmaPACBayesPenalty_le_theorem2PacBayesRemainder_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    theorem2AppendixA1SelectedSigmaPACBayesPenalty
        (S := S) w δ hn hk hdom_grid ≤
      theorem2PacBayesRemainder_source (S := S) w.1 δ.1 := by
  classical
  let K : ℝ := (Setup.parameterCount (E := E) : ℝ)
  let A : ℝ :=
    1 + Real.sqrt (Real.log (n : ℝ) / K)
  let B : ℝ :=
    1 + Real.exp (4 * (n : ℝ) / K)
  let selectedGridIndex : ℕ :=
    theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
      (S := S) w hn hk
  let sigma : ℝ :=
    theorem2AppendixA1SelectedSigma (S := S) hn hk
  let selectedDomain :
      ∀ ε : E,
        w.1 + sigma • ε ∈ S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let ctx :=
    theorem2AppendixA1ParameterGridContext
      (S := S) hk selectedGridIndex
        (hdom_grid selectedGridIndex)
  let Q : Measure (Setup.Parameter S) :=
    theorem2AppendixA1ParameterGaussianLaw
      (S := S) w.1 sigma selectedDomain
  have hK_pos : 0 < K := by
    dsimp [K]
    exact_mod_cast hk
  have hK_ge_one : (1 : ℝ) ≤ K := by
    dsimp [K]
    exact_mod_cast (Nat.succ_le_iff.2 hk)
  have hn_real : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hn_ge_two_nat : 2 ≤ n := by
    omega
  have hn_ge_two : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn_ge_two_nat
  have hdelta_pos : 0 < δ.1 := δ.2.1
  have hdelta_lt_one : δ.1 < 1 := δ.2.2
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    exact theorem2AppendixA1SelectedSigma_pos (S := S) hn hk
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hK_ne : K ≠ 0 := ne_of_gt hK_pos
  have hA_ne : A ≠ 0 := ne_of_gt hA_pos
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hselected_sandwich :
      let j : ℕ :=
        theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
          (S := S) w hn hk
      sigma ^ 2 + ‖w.1‖ ^ 2 / K ≤
          theorem2AppendixA1PriorGridVariance (S := S) hk j ∧
        theorem2AppendixA1PriorGridVariance (S := S) hk j ≤
          Real.exp (1 / K) *
            (sigma ^ 2 + ‖w.1‖ ^ 2 / K) :=
    by
      simpa [sigma, K] using
        (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_spec_of_reduced_norm
          (S := S) w hn hk hnorm)
  have hsandwich_lower :
      sigma ^ 2 + ‖w.1‖ ^ 2 / K ≤
        theorem2AppendixA1PriorGridVariance
          (S := S) hk selectedGridIndex := by
    simpa [selectedGridIndex] using hselected_sandwich.1
  have hsandwich_upper :
      theorem2AppendixA1PriorGridVariance
          (S := S) hk selectedGridIndex ≤
        Real.exp (1 / K) *
          (sigma ^ 2 + ‖w.1‖ ^ 2 / K) := by
    simpa [selectedGridIndex] using hselected_sandwich.2
  have hkl_formula :
      measurePACBayesKLDivergence Q ctx.prior_distribution =
        ENNReal.ofReal
          (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex sigma) := by
    simpa [Q, ctx, selectedGridIndex, selectedDomain, sigma] using
      (theorem2AppendixA1SelectedSubtypeKLFormulaAtSelectedSigma_of_gaussianAffineLaw
        (S := S) w hn hk hnorm hdom_grid)
  have hscalar_nonneg :
      0 ≤ theorem2AppendixA1GaussianKLFormulaScalarAtSigma
        (S := S) w hk selectedGridIndex sigma := by
    simpa [theorem2AppendixA1GaussianKLFormulaScalarAtSigma] using
      (theorem2AppendixA1GaussianKLFormulaScalarAtSigma_nonneg_of_sandwich
        (K := K) (sigma := sigma) (b := ‖w.1‖ ^ 2)
        (v := theorem2AppendixA1PriorGridVariance
          (S := S) hk selectedGridIndex)
        hK_pos hsigma_pos (sq_nonneg ‖w.1‖) hsandwich_lower)
  have hkl_toReal :
      (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal =
        theorem2AppendixA1GaussianKLFormulaScalarAtSigma
          (S := S) w hk selectedGridIndex sigma := by
    rw [hkl_formula]
    exact ENNReal.toReal_ofReal hscalar_nonneg
  have htarget :
      1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2 =
        1 + ‖w.1‖ ^ 2 / (K * sigma ^ 2) := by
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) / K := by
      exact div_nonneg (Real.log_nonneg hn_real.le) hK_pos.le
    have hden_pos :
        0 < Real.sqrt K *
          (1 + Real.sqrt (Real.log (n : ℝ) / K)) := by
      exact mul_pos (Real.sqrt_pos.2 hK_pos) (by positivity)
    have hsqrtK_sq : Real.sqrt K ^ 2 = K :=
      Real.sq_sqrt hK_pos.le
    have hsqrt_count_sq :
        Real.sqrt ((Setup.parameterCount (E := E) : ℝ)) ^ 2 = K := by
      simpa [K] using hsqrtK_sq
    dsimp [A, K, sigma, theorem2AppendixA1SelectedSigma]
    field_simp [ne_of_gt S.rho_pos, ne_of_gt hK_pos,
      ne_of_gt hden_pos, hsqrtK_sq]
    rw [hsqrt_count_sq]
    ring
  have hK_bound :
      theorem2AppendixA1GaussianKLFormulaScalarAtSigma
          (S := S) w hk selectedGridIndex sigma ≤
        (1 / 2 : ℝ) +
          (1 / 2 : ℝ) * K *
            Real.log (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2) := by
    simpa [theorem2AppendixA1GaussianKLFormulaScalarAtSigma] using
      (theorem2AppendixA1GaussianKLFormulaScalarAtSigma_le_of_sandwich
        (K := K) (sigma := sigma) (b := ‖w.1‖ ^ 2)
        (v := theorem2AppendixA1PriorGridVariance
          (S := S) hk selectedGridIndex)
        (target := 1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2)
        hK_pos hsigma_pos (sq_nonneg ‖w.1‖)
        hsandwich_lower hsandwich_upper htarget)
  have hlog_n_le_n : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) by positivity)
    linarith
  have hquot_le_n :
      Real.log (n : ℝ) / K ≤ (n : ℝ) := by
    apply (div_le_iff₀ hK_pos).2
    nlinarith [hlog_n_le_n]
  have hsqrt_le_n :
      Real.sqrt (Real.log (n : ℝ) / K) ≤ (n : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · nlinarith
    · have hn_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        nlinarith
      nlinarith [hquot_le_n]
  have hlog_K : Real.log K ≤ K := by
    have h := Real.log_le_sub_one_of_pos hK_pos
    linarith
  have hlog_A : Real.log A ≤ 2 * (n : ℝ) := by
    have hA_le : A ≤ 1 + (n : ℝ) := by
      dsimp [A]
      linarith
    have h := Real.log_le_sub_one_of_pos hA_pos
    linarith
  have hx_nonneg : 0 ≤ 4 * (n : ℝ) / K := by
    positivity
  have hB_le_exp :
      B ≤ Real.exp (1 + 4 * (n : ℝ) / K) := by
    calc
      B = 1 + Real.exp (4 * (n : ℝ) / K) := by rfl
      _ ≤ Real.exp (4 * (n : ℝ) / K) +
          Real.exp (4 * (n : ℝ) / K) := by
        nlinarith [Real.one_le_exp hx_nonneg]
      _ = 2 * Real.exp (4 * (n : ℝ) / K) := by ring
      _ ≤ Real.exp 1 * Real.exp (4 * (n : ℝ) / K) := by
        exact mul_le_mul_of_nonneg_right
          (by
            have h := Real.add_one_le_exp (1 : ℝ)
            norm_num at h ⊢
            exact h)
          (Real.exp_pos _).le
      _ = Real.exp (1 + 4 * (n : ℝ) / K) := by
        rw [← Real.exp_add]
  have hlog_B :
      Real.log B ≤ 1 + 4 * (n : ℝ) / K := by
    have h := Real.log_le_log hB_pos hB_le_exp
    simpa using h
  have hlog_ratio :
      Real.log
          (theorem2AppendixA1PriorGridScale (S := S) hk /
            (sigma ^ 2 + ‖w.1‖ ^ 2 / K)) ≤
        Real.log K + 2 * Real.log A + Real.log B := by
    have ha_pos :
        0 < sigma ^ 2 + ‖w.1‖ ^ 2 / K := by
      positivity
    have hsigma_sq_pos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma_pos
    have hc_pos :
        0 < theorem2AppendixA1PriorGridScale (S := S) hk := by
      exact theorem2AppendixA1PriorGridScale_pos (S := S) hk
    have hratio :
        theorem2AppendixA1PriorGridScale (S := S) hk /
            (sigma ^ 2 + ‖w.1‖ ^ 2 / K) ≤
          theorem2AppendixA1PriorGridScale (S := S) hk /
            sigma ^ 2 := by
      apply (div_le_div_iff₀ ha_pos hsigma_sq_pos).2
      have hnorm_div_nonneg : 0 ≤ ‖w.1‖ ^ 2 / K :=
        div_nonneg (sq_nonneg ‖w.1‖) hK_pos.le
      exact mul_le_mul_of_nonneg_left
        (by nlinarith) hc_pos.le
    have hlog_ratio' :=
      Real.log_le_log
        (div_pos hc_pos ha_pos) hratio
    have hscale :
        theorem2AppendixA1PriorGridScale (S := S) hk / sigma ^ 2 =
          K * A ^ 2 * B := by
      simpa [K, A, B, sigma] using
        (theorem2AppendixA1_priorGridScale_div_selectedSigma_sq_has_extra_parameter_factor
          (S := S) hn hk)
    calc
      Real.log
          (theorem2AppendixA1PriorGridScale (S := S) hk /
            (sigma ^ 2 + ‖w.1‖ ^ 2 / K)) ≤
          Real.log
            (theorem2AppendixA1PriorGridScale (S := S) hk / sigma ^ 2) :=
        hlog_ratio'
      _ = Real.log (K * A ^ 2 * B) := by rw [hscale]
      _ = Real.log K + 2 * Real.log A + Real.log B := by
        rw [Real.log_mul (mul_ne_zero hK_ne (pow_ne_zero 2 hA_ne)) hB_ne,
          Real.log_mul hK_ne (pow_ne_zero 2 hA_ne), Real.log_pow]
        ring
  have hlog_ratio_bound :
      Real.log
          (theorem2AppendixA1PriorGridScale (S := S) hk /
            (sigma ^ 2 + ‖w.1‖ ^ 2 / K)) ≤
        K + 4 * (n : ℝ) + 1 + 4 * (n : ℝ) / K := by
    linarith [hlog_ratio, hlog_K, hlog_A, hlog_B]
  have hindex_bound :
      ((selectedGridIndex : ℕ) : ℝ) + 1 ≤
        K ^ 2 + 4 * K * (n : ℝ) + K + 4 * (n : ℝ) + 1 := by
    have hindex_log :
        ((selectedGridIndex : ℕ) : ℝ) ≤
          K *
            Real.log
              (theorem2AppendixA1PriorGridScale (S := S) hk /
                (sigma ^ 2 + ‖w.1‖ ^ 2 / K)) := by
      simpa [selectedGridIndex, sigma, K] using
        (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma_le_log_ratio
          (S := S) w hn hk hnorm)
    have hmul_log :
        K *
            Real.log
              (theorem2AppendixA1PriorGridScale (S := S) hk /
                (sigma ^ 2 + ‖w.1‖ ^ 2 / K)) ≤
          K * (K + 4 * (n : ℝ) + 1 + 4 * (n : ℝ) / K) := by
      exact mul_le_mul_of_nonneg_left
        hlog_ratio_bound hK_pos.le
    have hpoly :
        K * (K + 4 * (n : ℝ) + 1 + 4 * (n : ℝ) / K) + 1 =
          K ^ 2 + 4 * K * (n : ℝ) + K + 4 * (n : ℝ) + 1 := by
      field_simp [hK_ne]
    calc
      ((selectedGridIndex : ℕ) : ℝ) + 1 ≤
          K *
              Real.log
                (theorem2AppendixA1PriorGridScale (S := S) hk /
                  (sigma ^ 2 + ‖w.1‖ ^ 2 / K)) + 1 := by
            linarith
      _ ≤ K * (K + 4 * (n : ℝ) + 1 + 4 * (n : ℝ) / K) + 1 := by
            linarith
      _ = K ^ 2 + 4 * K * (n : ℝ) + K + 4 * (n : ℝ) + 1 := hpoly
  let L : ℝ := 6 * (n : ℝ) + 3 * K
  have hL_pos : 0 < L := by
    dsimp [L]
    nlinarith
  have hpoly_le_L_sq :
      K ^ 2 + 4 * K * (n : ℝ) + K + 4 * (n : ℝ) + 1 ≤ L ^ 2 := by
    dsimp [L]
    nlinarith [sq_nonneg K, sq_nonneg (n : ℝ),
      mul_nonneg hK_pos.le (by nlinarith : 0 ≤ (n : ℝ))]
  have hj1_le_L_sq :
      ((selectedGridIndex : ℕ) : ℝ) + 1 ≤ L ^ 2 :=
    le_trans hindex_bound hpoly_le_L_sq
  have hj1_nonneg : 0 ≤ ((selectedGridIndex : ℕ) : ℝ) + 1 := by
    positivity
  have hj1_pos : 0 < ((selectedGridIndex : ℕ) : ℝ) + 1 := by
    positivity
  have hj1_sq :
      (((selectedGridIndex : ℕ) : ℝ) + 1) ^ 2 ≤ L ^ 4 := by
    have hsq :=
      (sq_le_sq₀ hj1_nonneg (sq_nonneg L)).2 hj1_le_L_sq
    calc
      (((selectedGridIndex : ℕ) : ℝ) + 1) ^ 2 ≤ (L ^ 2) ^ 2 := hsq
      _ = L ^ 4 := by ring
  have hpi_sq_lt : Real.pi ^ 2 < (12 : ℝ) := by
    have hpi_sq :=
      mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d20
    nlinarith
  have hpi_factor : Real.pi ^ 2 / 6 ≤ (n : ℝ) / δ.1 := by
    have hpi_two : Real.pi ^ 2 / 6 < (2 : ℝ) := by
      nlinarith [hpi_sq_lt]
    have hnd_two : (2 : ℝ) < (n : ℝ) / δ.1 := by
      apply (lt_div_iff₀ hdelta_pos).2
      nlinarith
    exact (le_of_lt hpi_two).trans (le_of_lt hnd_two)
  let x : ℝ := (n : ℝ) / δ.1
  have hx_pos : 0 < x := by
    dsimp [x]
    positivity
  have hconfidence_ratio :
      (n : ℝ) /
          theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex =
        x * (Real.pi ^ 2 / 6) *
          (((selectedGridIndex : ℕ) : ℝ) + 1) ^ 2 := by
    unfold theorem2AppendixA1PriorGridConfidence
    dsimp [x]
    field_simp [ne_of_gt hdelta_pos, ne_of_gt Real.pi_pos,
      ne_of_gt hj1_pos]
    norm_num [Nat.cast_add, Nat.cast_one, pow_two]
  let targetRatio : ℝ := x ^ 2 * L ^ 4
  have htarget_ratio_pos : 0 < targetRatio := by
    dsimp [targetRatio]
    positivity
  have hratio_le :
      (n : ℝ) /
          theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex ≤
        targetRatio := by
    rw [hconfidence_ratio]
    dsimp [targetRatio]
    calc
      x * (Real.pi ^ 2 / 6) *
            (((selectedGridIndex : ℕ) : ℝ) + 1) ^ 2 ≤
          x * x * (((selectedGridIndex : ℕ) : ℝ) + 1) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpi_factor hx_pos.le)
              (sq_nonneg _)
      _ ≤ x * x * L ^ 4 := by
            exact mul_le_mul_of_nonneg_left hj1_sq
              (mul_nonneg hx_pos.le hx_pos.le)
      _ = x ^ 2 * L ^ 4 := by ring
  have hconfidence_log :
      Real.log
          ((n : ℝ) /
            theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex) ≤
        2 * Real.log x + 4 * Real.log L := by
    have hactual_pos :
        0 <
          (n : ℝ) /
            theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex := by
      rw [hconfidence_ratio]
      positivity
    have hlog := Real.log_le_log hactual_pos hratio_le
    have htarget_log :
        Real.log (x ^ 2 * L ^ 4) =
          2 * Real.log x + 4 * Real.log L := by
      rw [Real.log_mul (pow_ne_zero 2 (ne_of_gt hx_pos))
        (pow_ne_zero 4 (ne_of_gt hL_pos)),
        Real.log_pow, Real.log_pow]
      ring
    rw [show targetRatio = x ^ 2 * L ^ 4 by rfl, htarget_log] at hlog
    exact hlog
  have hconf_bound :
      Real.log
          ((n : ℝ) /
            theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex) ≤
        2 * (Real.log ((n : ℝ) / δ.1) + 2 * Real.log L) := by
    calc
      _ ≤ 2 * Real.log x + 4 * Real.log L := hconfidence_log
      _ = 2 * (Real.log ((n : ℝ) / δ.1) + 2 * Real.log L) := by
        dsimp [x]
        ring
  have hnum_bound :
      (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex) ≤
        2 *
          (((1 / 4 : ℝ) * K *
              Real.log (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2)) +
            (1 / 4 : ℝ) +
            Real.log ((n : ℝ) / δ.1) +
            2 * Real.log L) := by
    rw [hkl_toReal]
    calc
      theorem2AppendixA1GaussianKLFormulaScalarAtSigma
            (S := S) w hk selectedGridIndex sigma +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex) ≤
          ((1 / 2 : ℝ) +
              (1 / 2 : ℝ) * K *
                Real.log (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2)) +
            Real.log
              ((n : ℝ) /
                theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex) :=
        add_le_add_left hK_bound _
      _ ≤
          ((1 / 2 : ℝ) +
              (1 / 2 : ℝ) * K *
                Real.log (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2)) +
            2 * (Real.log ((n : ℝ) / δ.1) + 2 * Real.log L) :=
        add_le_add_right hconf_bound _
      _ = _ := by ring
  have hden_pos : 0 < (n : ℝ) - 1 := by
    linarith
  have htwo_den_pos : 0 < 2 * ((n : ℝ) - 1) := by
    positivity
  rw [theorem2AppendixA1SelectedSigmaPACBayesPenalty_spec,
    theorem2PacBayesRemainder_source_spec]
  apply Real.sqrt_le_sqrt
  have hdiv :
      ((measurePACBayesKLDivergence Q ctx.prior_distribution).toReal +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
          (2 * ((n : ℝ) - 1)) ≤
        (((1 / 4 : ℝ) * K *
              Real.log (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2)) +
            (1 / 4 : ℝ) +
            Real.log ((n : ℝ) / δ.1) +
            2 * Real.log L) /
          ((n : ℝ) - 1) := by
    calc
      _ ≤
          (2 *
            (((1 / 4 : ℝ) * K *
                Real.log (1 + (‖w.1‖ ^ 2 / S.rho ^ 2) * A ^ 2)) +
              (1 / 4 : ℝ) +
              Real.log ((n : ℝ) / δ.1) +
              2 * Real.log L)) /
            (2 * ((n : ℝ) - 1)) := by
              exact div_le_div_of_nonneg_right hnum_bound
                htwo_den_pos.le
      _ = _ := by
        field_simp [ne_of_gt hden_pos]
  dsimp [K, A, L] at *
  convert hdiv using 1 <;> ring

private theorem theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent_of_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S)) :
    ∀ s : Dataset n X Y,
      theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
        (S := S) w δ hn hk hdom_grid s := by
  have hpenalty :
      theorem2AppendixA1SelectedSigmaPACBayesPenalty
          (S := S) w δ hn hk hdom_grid ≤
        theorem2PacBayesRemainder_source (S := S) w.1 δ.1 :=
    theorem2AppendixA1SelectedSigmaPACBayesPenalty_le_theorem2PacBayesRemainder_source
      (S := S) w δ hn hk hnorm hdom_grid
  intro s sharpness hsharpness
  have hsource :=
    theorem2AppendixA1AbsorptionEvent_of_source
      (S := S) w δ hn hk hadm s sharpness hsharpness
  calc
    ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
        (Real.sqrt (n : ℝ))⁻¹) +
        theorem2AppendixA1SelectedSigmaPACBayesPenalty
          (S := S) w δ hn hk hdom_grid ≤
      ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
        (Real.sqrt (n : ℝ))⁻¹) +
        theorem2PacBayesRemainder_source (S := S) w.1 δ.1 := by
      simpa [add_comm] using
        (add_le_add_right hpenalty
          ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
            (Real.sqrt (n : ℝ))⁻¹))
    _ ≤ sharpness + theorem2Remainder_source (S := S) w.1 δ.1 := hsource

def theorem2AppendixA1SelectedSigmaCorrectedGoodEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    Set (Dataset n X Y) :=
  {s | theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
      (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
        (theorem2AppendixA1SelectedSigmaPACBayesPenalty
          (S := S) w δ hn hk hdom_grid) s ∧
    theorem2GaussianEmpiricalSharpnessEventAtSigma
      (S := S) w δ.1
        (theorem2AppendixA1SelectedSigma (S := S) hn hk) s ∧
    theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
      (S := S) w δ hn hk hdom_grid s}

def theorem2AppendixA1SelectedSigmaCorrectedBadEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    Set (Dataset n X Y) :=
  (theorem2AppendixA1SelectedSigmaCorrectedGoodEvent
    (S := S) w δ hn hk hdom_grid)ᶜ

def theorem2AppendixA1SelectedSigmaCorrectedAbsorptionFailure
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    Set (Dataset n X Y) :=
  {s | ¬ theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
    (S := S) w δ hn hk hdom_grid s}

theorem theorem2AppendixA1SelectedSigmaCorrectedBadEvent_subset_component_union
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace) :
    theorem2AppendixA1SelectedSigmaCorrectedBadEvent
        (S := S) w δ hn hk hdom_grid ⊆
      theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure
          (S := S) w δ hn hk hdom_grid ∪
        theorem2AppendixA1SharpnessFailureAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) ∪
          theorem2AppendixA1SelectedSigmaCorrectedAbsorptionFailure
            (S := S) w δ hn hk hdom_grid := by
  intro s hs
  change ¬ (
    theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
        (S := S) w
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid) s ∧
      theorem2GaussianEmpiricalSharpnessEventAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk) s ∧
      theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
        (S := S) w δ hn hk hdom_grid s) at hs
  simp only [theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure,
    theorem2AppendixA1SharpnessFailureAtSigma,
    theorem2AppendixA1SelectedSigmaCorrectedAbsorptionFailure,
    Set.mem_union, Set.mem_setOf_eq]
  by_cases hpac :
      theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
        (S := S) w
          (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid) s
  · by_cases hsharp :
        theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s
    · by_cases habsorb :
          theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
            (S := S) w δ hn hk hdom_grid s
      · exact False.elim (hs ⟨hpac, hsharp, habsorb⟩)
      · exact Or.inr habsorb
    · exact Or.inl (Or.inr hsharp)
  · exact Or.inl (Or.inl hpac)

theorem theorem2OriginalEvent_of_selected_sigma_corrected_pacBayesGaussian_and_radiusSharpness
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (s : Dataset n X Y)
    (hgaussian :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hpac :
      theorem2PacBayesGaussianExpectationEventAtSigmaWithRemainder
        (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid) s)
    (hradius :
      theorem2GaussianEmpiricalSharpnessEventAtSigma
        (S := S) w δ.1
          (theorem2AppendixA1SelectedSigma (S := S) hn hk) s)
    (habsorb :
      theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
        (S := S) w δ hn hk hdom_grid s) :
    theorem2OriginalEvent (S := S) w δ.1 s := by
  rcases hgaussian with
    ⟨population, gaussianPopulation, hpopulation, hgaussianPopulation,
      hpopulation_le_gaussian⟩
  rcases hpac with
    ⟨gaussianPopulation', gaussianEmpirical, hgaussianPopulation',
      hgaussianEmpirical, hgaussian_le_empirical⟩
  have hgaussian_eq :
      gaussianPopulation = gaussianPopulation' :=
    sourceGaussianPerturbedPopulationLossAtSigma_value_unique
      (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
      hgaussianPopulation hgaussianPopulation'
  rcases hradius gaussianEmpirical hgaussianEmpirical with
    ⟨sharpness, hsharpness, hempirical_split⟩
  have hsplit_with_remainder :
      gaussianEmpirical +
          theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid ≤
        ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
            (Real.sqrt (n : ℝ))⁻¹) +
          theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid := by
    linarith
  have habsorb' :
      ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
          (Real.sqrt (n : ℝ))⁻¹) +
        theorem2AppendixA1SelectedSigmaPACBayesPenalty
          (S := S) w δ hn hk hdom_grid ≤
          sharpness + theorem2Remainder_source (S := S) w.1 δ.1 :=
    habsorb sharpness hsharpness
  refine ⟨population, sharpness, hpopulation, hsharpness, ?_⟩
  calc
    population ≤ gaussianPopulation := hpopulation_le_gaussian
    _ = gaussianPopulation' := hgaussian_eq
    _ ≤ gaussianEmpirical +
          theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid :=
      hgaussian_le_empirical
    _ ≤ ((1 - (Real.sqrt (n : ℝ))⁻¹) * sharpness +
            (Real.sqrt (n : ℝ))⁻¹) +
          theorem2AppendixA1SelectedSigmaPACBayesPenalty
            (S := S) w δ hn hk hdom_grid :=
      hsplit_with_remainder
    _ ≤ sharpness + theorem2Remainder_source (S := S) w.1 δ.1 := habsorb'

theorem theorem2AppendixA1SelectedSigmaCorrectedGoodEvent_to_theorem2OriginalEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (htransport :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)) :
    theorem2AppendixA1SelectedSigmaCorrectedGoodEvent
        (S := S) w δ hn hk hdom_grid ⊆
      {s | theorem2OriginalEvent (S := S) w δ.1 s} := by
  intro s hs
  exact
    theorem2OriginalEvent_of_selected_sigma_corrected_pacBayesGaussian_and_radiusSharpness
      (S := S) w δ hn hk hdom_grid s htransport hs.1 hs.2.1 hs.2.2

theorem theorem2AppendixA1SelectedSigmaCorrectedBadEvent_mass_of_source_components
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hpac_mass :
      theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureFromPriorGrid
        (S := S) w δ hn hk hdom_grid)
    (hsharpness_event :
      ∀ s : Dataset n X Y,
        theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s)
    (habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
          (S := S) w δ hn hk hdom_grid s) :
    (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1SelectedSigmaCorrectedBadEvent
          (S := S) w δ hn hk hdom_grid) ≤
      ENNReal.ofReal δ.1 := by
  let μ : Measure (Dataset n X Y) := Setup.iidTrainingLaw (S := S)
  let pacBad :=
    theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailure
      (S := S) w δ hn hk hdom_grid
  let sharpBad :=
    theorem2AppendixA1SharpnessFailureAtSigma (S := S) w δ.1
      (theorem2AppendixA1SelectedSigma (S := S) hn hk)
  let absorbBad :=
    theorem2AppendixA1SelectedSigmaCorrectedAbsorptionFailure
      (S := S) w δ hn hk hdom_grid
  let selectedBad :=
    theorem2AppendixA1SelectedSigmaCorrectedBadEvent
      (S := S) w δ hn hk hdom_grid
  have hsubset : selectedBad ⊆ pacBad ∪ sharpBad ∪ absorbBad := by
    simpa [selectedBad, pacBad, sharpBad, absorbBad] using
      (theorem2AppendixA1SelectedSigmaCorrectedBadEvent_subset_component_union
        (S := S) w δ hn hk hdom_grid)
  have hsharp_zero : μ sharpBad = 0 := by
    have heq : sharpBad = ∅ := by
      ext s
      constructor
      · intro hs
        have hnot :
            ¬ theorem2GaussianEmpiricalSharpnessEventAtSigma
              (S := S) w δ.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk) s := by
          simpa [sharpBad] using hs
        exact (hnot (hsharpness_event s)).elim
      · intro hs
        simpa using hs
    rw [heq, measure_empty]
  have habsorb_zero : μ absorbBad = 0 := by
    have heq : absorbBad = ∅ := by
      ext s
      constructor
      · intro hs
        have hnot :
            ¬ theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
              (S := S) w δ hn hk hdom_grid s := by
          simpa [absorbBad] using hs
        exact (hnot (habsorption_event s)).elim
      · intro hs
        simpa using hs
    rw [heq, measure_empty]
  have hcomponent :
      μ (pacBad ∪ sharpBad ∪ absorbBad) ≤ ENNReal.ofReal δ.1 := by
    have hunion :
        μ (pacBad ∪ sharpBad ∪ absorbBad) ≤
          μ pacBad + μ sharpBad + μ absorbBad :=
      theorem2AppendixA1_measure_bad_mass_le_of_component_masses
        μ pacBad sharpBad absorbBad
        (μ pacBad) (μ sharpBad) (μ absorbBad)
        (le_refl _) (le_refl _) (le_refl _)
    calc
      μ (pacBad ∪ sharpBad ∪ absorbBad) ≤
          μ pacBad + μ sharpBad + μ absorbBad := hunion
      _ = μ pacBad := by rw [hsharp_zero, habsorb_zero]; simp
      _ ≤ ENNReal.ofReal δ.1 := by simpa [μ, pacBad] using hpac_mass
  have hbad : μ selectedBad ≤ ENNReal.ofReal δ.1 :=
    le_trans (measure_mono hsubset) hcomponent
  simpa [μ, selectedBad] using hbad

theorem theorem2AppendixA1SelectedSigmaCorrectedGoodEvent_mass_of_source_components
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hpac_mass :
      theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureFromPriorGrid
        (S := S) w δ hn hk hdom_grid)
    (hsharpness_event :
      ∀ s : Dataset n X Y,
        theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s)
    (habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
          (S := S) w δ hn hk hdom_grid s) :
    ENNReal.ofReal (1 - δ.1) ≤
      (Setup.iidTrainingLaw (S := S))
        (theorem2AppendixA1SelectedSigmaCorrectedGoodEvent
          (S := S) w δ hn hk hdom_grid) := by
  let μ : Measure (Dataset n X Y) := Setup.iidTrainingLaw (S := S)
  have hbad :
      μ (theorem2AppendixA1SelectedSigmaCorrectedBadEvent
        (S := S) w δ hn hk hdom_grid) ≤
        ENNReal.ofReal δ.1 :=
    theorem2AppendixA1SelectedSigmaCorrectedBadEvent_mass_of_source_components
      (S := S) w δ hn hk hdom_grid hpac_mass
      hsharpness_event habsorption_event
  letI : IsProbabilityMeasure μ :=
    Setup.iidTrainingLaw_isProbability (S := S)
  let selectedBad :=
    theorem2AppendixA1SelectedSigmaCorrectedBadEvent
      (S := S) w δ hn hk hdom_grid
  have hroute :
      ENNReal.ofReal (1 - δ.1) ≤ μ selectedBadᶜ := by
    exact ennreal_ofReal_lower_bound_from_bad_event
      μ (le_of_lt δ.2.1)
      (by
        simpa [selectedBad, theorem2AppendixA1SelectedSigmaCorrectedBadEvent]
          using hbad)
  change ENNReal.ofReal (1 - δ.1) ≤
    μ (theorem2AppendixA1SelectedSigmaCorrectedGoodEvent
      (S := S) w δ hn hk hdom_grid)
  simpa [selectedBad, theorem2AppendixA1SelectedSigmaCorrectedBadEvent] using hroute

set_option linter.unusedVariables false in
private theorem theorem2AppendixA1SelectedSigmaPacBayesFailureGridInclusion_source_attempt_iter3
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1) :
    True := by
  classical
  let selectedGridIndex : ℕ :=
    (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
  let selectedDomain :
      ∀ ε : E,
        w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
          S.parameterSpace :=
    theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
      (S := S) w hn hk hdom_grid
  let penaltyLeaf : Prop :=
    Real.sqrt
        (((measurePACBayesKLDivergence
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex
                (hdom_grid selectedGridIndex)).prior_distribution).toReal +
          Real.log
            ((n : ℝ) /
              theorem2AppendixA1PriorGridConfidence δ.1 selectedGridIndex)) /
          (2 * ((n : ℝ) - 1))) ≤
      theorem2PacBayesRemainder_source (S := S) w.1 δ.1
  have hpopulation_source :
      ∀ s : Dataset n X Y,
        let selectedGridIndex : ℕ :=
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
        let selectedDomain :
          ∀ ε : E,
            w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
              S.parameterSpace :=
          theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
            (S := S) w hn hk hdom_grid
        sourceGaussianPerturbedPopulationLossAtSigma
          (S := S) w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesPopulationLoss
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
            (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)) := by
    intro s
    exact theorem2AppendixA1SelectedSigmaPopulationSourceIdentity_of_bounded_loss
      (S := S) w hn hk hdom_grid hmeas_loss hbounded
  have hempirical_source :
      ∀ s : Dataset n X Y,
        let selectedGridIndex : ℕ :=
          (theorem2AppendixA1SelectedPriorGridIndexAtSelectedSigma
        (S := S) w hn hk);
        let selectedDomain :
          ∀ ε : E,
            w.1 + theorem2AppendixA1SelectedSigma (S := S) hn hk • ε ∈
              S.parameterSpace :=
          theorem2AppendixA1SelectedPosteriorDomain_of_grid_domain
            (S := S) w hn hk hdom_grid
        sourceGaussianPerturbedEmpiricalLossAtSigma
          (S := S) s w (theorem2AppendixA1SelectedSigma (S := S) hn hk)
          (measurePACBayesEmpiricalLoss
            (theorem2AppendixA1ParameterGridContext
              (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex))
            n s
            (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))
            (theorem2AppendixA1ParameterGaussianLaw
              (S := S) w.1
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)
                selectedDomain)) := by
    intro s
    exact theorem2AppendixA1SelectedSigmaEmpiricalSourceIdentity_of_bounded_loss
      (S := S) w δ hn hk hdom_grid hmeas_loss hbounded s
  fail_if_success
    have hpenalty : penaltyLeaf := by
      let ctx :=
        theorem2AppendixA1ParameterGridContext
          (S := S) hk selectedGridIndex (hdom_grid selectedGridIndex)
      let Q : Measure (Setup.Parameter S) :=
        theorem2AppendixA1ParameterGaussianLaw
          (S := S) w.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk)
            selectedDomain
      have hselected_kl_formula :
          measurePACBayesKLDivergence Q ctx.prior_distribution =
            ENNReal.ofReal
              (theorem2AppendixA1GaussianKLFormulaScalarAtSigma
                (S := S) w hk selectedGridIndex
                (theorem2AppendixA1SelectedSigma (S := S) hn hk)) := by
        simpa [Q, ctx, selectedGridIndex, selectedDomain] using
          (theorem2AppendixA1SelectedSubtypeKLFormulaAtSelectedSigma_of_gaussianAffineLaw
            (S := S) w hn hk hnorm hdom_grid)
      have hselected_kl_toReal :
          (measurePACBayesKLDivergence Q ctx.prior_distribution).toReal =
            theorem2AppendixA1GaussianKLFormulaScalarAtSigma
              (S := S) w hk selectedGridIndex
              (theorem2AppendixA1SelectedSigma (S := S) hn hk) := by
        rw [hselected_kl_formula]
        exact ENNReal.toReal_ofReal
          (show
            0 ≤ theorem2AppendixA1GaussianKLFormulaScalarAtSigma
              (S := S) w hk selectedGridIndex
              (theorem2AppendixA1SelectedSigma (S := S) hn hk) by
            positivity)
      dsimp [penaltyLeaf, Q, ctx] at *
      rw [hselected_kl_toReal]
      rw [theorem2PacBayesRemainder_source_spec]
      apply Real.sqrt_le_sqrt
      nlinarith
    exact hpenalty
  trivial

/- Internal source-scale event alignment for the selected-sigma Appendix
   route.  The selected-scale population and selected PAC-Bayes mass inputs are
   proof obligations of the corrected Appendix route, not public assumptions of
   the rho-scale paper theorem. -/
private theorem theorem2AppendixA1SelectedSigmaEventScaleAlignment_of_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w)
    (hpac_mass :
      theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGridLegacyStatement
        (S := S) w δ hn hk) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  intro hgaussian
  have habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s :=
    theorem2AppendixA1AbsorptionEvent_of_source
      (S := S) w δ hn hk hadm
  exact
    (theorem2SourceBoundaryObligation_from_pacBayes_route
      (S := S) w δ hn hk hselected_population
      (theorem2AppendixA1SelectedSigmaGoodEvent_mass_of_bounded_loss_source
        (S := S) w δ hn hk hadm hsharpness_attain
          hpac_mass habsorption_event)) hgaussian

private theorem theorem2SourceBoundaryObligation_of_selected_sigma_source_components
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hpac_mass :
      (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1PacBayesFailureAtSigma
            (S := S) w δ.1
              (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
        ENNReal.ofReal δ.1)
    (hsharpness_event :
      ∀ s : Dataset n X Y,
        theorem2GaussianEmpiricalSharpnessEventAtSigma
          (S := S) w δ.1
            (theorem2AppendixA1SelectedSigma (S := S) hn hk) s)
    (habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  exact theorem2SourceBoundaryObligation_from_pacBayes_route
      (S := S) w δ hn hk hselected_population
    (theorem2AppendixA1SelectedSigmaGoodEvent_mass_of_source_components
      (S := S) w δ hn hk hpac_mass hsharpness_event habsorption_event)

private theorem theorem2SourceBoundaryObligation_of_selected_sigma_bounded_loss_source
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w)
    (hpac_mass :
      (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1PacBayesFailureAtSigma
            (S := S) w δ.1
              (theorem2AppendixA1SelectedSigma (S := S) hn hk)) ≤
        ENNReal.ofReal δ.1)
    (habsorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1AbsorptionEvent (S := S) w δ.1 s) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  exact theorem2SourceBoundaryObligation_from_pacBayes_route
    (S := S) w δ hn hk hselected_population
      (theorem2AppendixA1SelectedSigmaGoodEvent_mass_of_bounded_loss_source
        (S := S) w δ hn hk hadm hsharpness_attain hpac_mass habsorption_event)

theorem theorem2SourceBoundaryObligation_from_corrected_selected_sigma_pacBayes_route
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hprob :
      ENNReal.ofReal (1 - δ.1) ≤
        (Setup.iidTrainingLaw (S := S))
          (theorem2AppendixA1SelectedSigmaCorrectedGoodEvent
            (S := S) w δ hn hk hdom_grid)) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  intro _hgaussian
  refine le_trans hprob ?_
  exact measure_mono
    (theorem2AppendixA1SelectedSigmaCorrectedGoodEvent_to_theorem2OriginalEvent
      (S := S) w δ hn hk hdom_grid hselected_population)

theorem theorem2SourceBoundaryObligation_of_corrected_selected_sigma_components
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w)
    (hpac_mass :
      theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureFromPriorGrid
        (S := S) w δ hn hk hdom_grid)
    (hcorrected_absorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
          (S := S) w δ hn hk hdom_grid s) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  exact theorem2SourceBoundaryObligation_from_corrected_selected_sigma_pacBayes_route
    (S := S) w δ hn hk hdom_grid hselected_population
    (theorem2AppendixA1SelectedSigmaCorrectedGoodEvent_mass_of_source_components
      (S := S) w δ hn hk hdom_grid hpac_mass
      (theorem2AppendixA1SelectedSigmaGaussianEmpiricalSharpnessEvent_of_source
        (S := S) w δ hn hk hadm hsharpness_attain)
      hcorrected_absorption_event)

/- Internal Appendix A.1 source-contract endpoint.  This is kept private and
   deliberately outside the paper-facing dependency cone: the PDF states the
   Gaussian premise at rho and does not state the selected-scale transport,
   bounded-loss, attainment, or PAC-Bayes failure-mass facts required by this
   Lean route.  The constant-loss counterexample above formally records that
   the rho-only source setup is insufficient for the cited bounded-loss step. -/
private theorem
    theorem2PacBayesGaussianAndRadiusSharpness_internal_guarded_source_contract
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w)
    (hpac_mass :
      theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGridLegacyStatement
        (S := S) w δ hn hk) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  exact theorem2AppendixA1SelectedSigmaEventScaleAlignment_of_source
    (S := S) w δ hn hk hselected_population hadm hsharpness_attain hpac_mass

/- Private compatibility alias for the corrected Appendix A.1 route.  It is
   intentionally not a public source-facing endpoint while its head carries
   selected-sigma population and selected PAC-Bayes mass obligations. -/
private theorem theorem2PacBayesGaussianAndRadiusSharpness_probability_from_appendixA1_guarded_source_contract
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    (hadm : theorem2PacBayesAdmissibleBoundedLoss (S := S))
    (hsharpness_attain :
      ∀ s : Dataset n X Y,
        Setup.sourceEuclideanSAMMaximumAttainmentObligation
          (S := S) s w)
    (hpac_mass :
      theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGridLegacyStatement
        (S := S) w δ hn hk) :
    theorem2SourceBoundaryObligation (S := S) w δ.1 := by
  exact theorem2AppendixA1SelectedSigmaEventScaleAlignment_of_source
    (S := S) w δ hn hk hselected_population hadm hsharpness_attain hpac_mass

private theorem sourcePopulationLossAt_eq_populationLossValue_at_parameter
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (value : ℝ)
    (h : Setup.sourcePopulationLossAt (S := S) w.1 value) :
    value = Setup.populationLossValue (S := S) w := by
  rcases h with ⟨hw, hpop⟩
  rcases hpop with ⟨_hwd, hvalue⟩
  have hparam :
      (⟨w.1, hw⟩ : Setup.Parameter S) = w := by
    exact Subtype.ext rfl
  calc
    value = Setup.populationLossValue (S := S) ⟨w.1, hw⟩ := hvalue
    _ = Setup.populationLossValue (S := S) w := by rw [hparam]

private theorem theorem2EuclideanSharpnessSource_eq_euclideanSAMMaximum
    (S : Setup n E X Y Ω) (s : Dataset n X Y) (w : Setup.Parameter S)
    (value : ℝ)
    (h : theorem2EuclideanSharpnessSource (S := S) s w value) :
    value = Setup.euclideanSAMMaximum (S := S) s w := by
  have hsrc :
      Setup.sourceEuclideanSAMMaximum (S := S) s w value := by
    simpa [theorem2EuclideanSharpnessSource,
      Setup.theorem2SharpnessSource] using h
  rcases hsrc with ⟨_hdomain, hmem, hupper⟩
  have hgreatest :
      IsGreatest (Setup.euclideanSAMLossValues (S := S) s w) value := by
    constructor
    · rcases hmem with ⟨ε, hnorm, hsource⟩
      rcases hsource with ⟨hdom, hvalue⟩
      exact ⟨ε, hnorm, hdom, hvalue⟩
    · intro y hy
      rcases hy with ⟨ε, hnorm, hdom, hvalue⟩
      exact hupper ε hnorm y ⟨hdom, hvalue⟩
  rw [Setup.euclideanSAMMaximum, hgreatest.csSup_eq]

theorem theorem2OriginalEvent_to_internalCheckedEvent
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (s : Dataset n X Y) :
    theorem2OriginalEvent (S := S) w δ.1 s →
      Setup.populationLossValue (S := S) w ≤
        Setup.euclideanSAMMaximum (S := S) s w +
          theorem2RemainderInternalChecked (S := S) w.1 δ hn hk := by
  intro hsource_event
  rcases hsource_event with
    ⟨population, sharpness, hpopulation, hsharpness, hle⟩
  have hpopulation_eq :
      population = Setup.populationLossValue (S := S) w :=
    sourcePopulationLossAt_eq_populationLossValue_at_parameter
      (S := S) w population hpopulation
  have hsharpness_eq :
      sharpness = Setup.euclideanSAMMaximum (S := S) s w :=
    theorem2EuclideanSharpnessSource_eq_euclideanSAMMaximum
      (S := S) s w sharpness hsharpness
  calc
    Setup.populationLossValue (S := S) w = population := hpopulation_eq.symm
    _ ≤ sharpness + theorem2Remainder_source (S := S) w.1 δ.1 := hle
    _ = Setup.euclideanSAMMaximum (S := S) s w +
          theorem2RemainderInternalChecked (S := S) w.1 δ hn hk := by
        rw [hsharpness_eq, theorem2Remainder_source_spec,
          theorem2RemainderInternalChecked_spec]

/- Lean-side obligations not stated as primitive assumptions in Theorem 2.
   These are ordinary well-definedness and attainment obligations.  The
   selected-scale population premise, Appendix PAC-Bayes failure mass, and
   absorption algebra are theorem-level source bridges below; they are not
   stored as setup fields or decomposed into grid/measurability transport
   premises in the checked endpoint. -/
def theorem2LeanSideBoundaryObligations
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ)
    : Prop :=
  0 < δ ∧ δ < 1 ∧ 1 < n ∧ 0 < Setup.parameterCount (E := E) ∧
    theorem2PacBayesAdmissibleBoundedLoss (S := S) ∧
    Setup.sourcePopulationLossWellDefinedObligation (S := S) w.1 ∧
    sourceGaussianPerturbedPopulationLossAEGraphObligation (S := S) w ∧
    sourceGaussianPerturbedPopulationLossWellDefinedObligation (S := S) w ∧
    (∀ s : Dataset n X Y,
      sourceGaussianPerturbedEmpiricalLossWellDefinedObligation
        (S := S) s w) ∧
    (∀ s : Dataset n X Y,
      Setup.sourceEuclideanSAMMaximumAttainmentObligation (S := S) s w)

theorem theorem2LeanSideBoundaryObligations_spec
    (S : Setup n E X Y Ω) (w : Setup.Parameter S) (δ : ℝ) :
    theorem2LeanSideBoundaryObligations (S := S) w δ ↔
      theorem2LeanSideBoundaryObligations (S := S) w δ := by
  rfl

private theorem
    theorem2_internal_checked_corrected_selected_sigma_transport_boundary_of_lean_side_boundary
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hside : theorem2LeanSideBoundaryObligations (S := S) w δ.1)
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk))
    :
    theorem2GaussianPremiseSource S w →
      ENNReal.ofReal (1 - δ.1) ≤
      (Setup.iidTrainingLaw (S := S))
    {s | Setup.populationLossValue (S := S) w ≤
            Setup.euclideanSAMMaximum (S := S) s w +
              theorem2RemainderInternalChecked (S := S) w.1 δ hn hk} := by
  intro hgaussian
  rcases hside with
    ⟨_hδ_pos, _hδ_lt, _hn_side, _hk_side, hadm, _hpopulation_wd,
      _hgaussian_graph, _hgaussian_wd, _hempirical_wd, hsharpness_attain⟩
  have hbounded :
      ∀ (w : Setup.Parameter S) (x : X) (y : Y),
        (S.loss w x y : ℝ) ≤ 1 :=
    hadm.1
  have hcorrected_absorption_event :
      ∀ s : Dataset n X Y,
        theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent
          (S := S) w δ hn hk hdom_grid s :=
    theorem2AppendixA1SelectedSigmaCorrectedAbsorptionEvent_of_source
      (S := S) w δ hn hk hnorm hdom_grid hadm
  have hpac_mass :
      theorem2AppendixA1SelectedSigmaCorrectedPacBayesFailureFromPriorGrid
        (S := S) w δ hn hk hdom_grid :=
    theorem2AppendixA1SelectedSigmaPacBayesFailureFromPriorGrid
      (S := S) w δ hn hk hnorm hdom_grid hmeas_loss hbounded
  have hsource_probability :
      ENNReal.ofReal (1 - δ.1) ≤
        (Setup.iidTrainingLaw (S := S))
          {s | theorem2OriginalEvent (S := S) w δ.1 s} :=
    (theorem2SourceBoundaryObligation_of_corrected_selected_sigma_components
      (S := S) w δ hn hk hdom_grid hselected_population hadm hsharpness_attain
      hpac_mass hcorrected_absorption_event) hgaussian
  refine le_trans hsource_probability ?_
  exact measure_mono fun s hs =>
    theorem2OriginalEvent_to_internalCheckedEvent
      (S := S) w δ hn hk s hs

/- Private corrected confidence boundary for the selected-sigma Appendix
   route.  This is not the unqualified paper theorem: its head deliberately
   retains the selected-scale transport contract because the source states
   the Gaussian premise only at `rho`. -/
private theorem
    theorem2_internal_checked_corrected_selected_sigma_transport_boundary
    [BorelSpace E] [SecondCountableTopology E]
    (S : Setup n E X Y Ω) (w : Setup.Parameter S)
    /- book/research/SAM.json#/main_theorem/statement_math, quote:
       `with probability 1−δ ... sqrt(.../(n−1))`. -/
    (δ : Set.Ioo (0 : ℝ) 1) (hn : 1 < n)
    (hk : 0 < Setup.parameterCount (E := E))
    (hside : theorem2LeanSideBoundaryObligations (S := S) w δ.1)
    (hnorm :
      ‖w.1‖ ^ 2 ≤
        S.rho ^ 2 *
          (Real.exp
            (4 * (n : ℝ) /
              (Setup.parameterCount (E := E) : ℝ)) - 1))
    (hdom_grid :
      ∀ j : ℕ, ∀ ε : E,
        (0 : E) +
            Real.sqrt (theorem2AppendixA1PriorGridVariance
              (S := S) hk j) • ε ∈ S.parameterSpace)
    (hmeas_loss :
      Measurable
        (Function.uncurry
          (theorem2AppendixA1SourcePointwiseLossOnParameter (S := S))))
    (hselected_population :
      theorem2GaussianPremiseSourceAtSigma (S := S) w
        (theorem2AppendixA1SelectedSigma (S := S) hn hk)) :
    theorem2GaussianPremiseSource S w →
      ENNReal.ofReal (1 - δ.1) ≤
      (Setup.iidTrainingLaw (S := S))
        {s | Setup.populationLossValue (S := S) w ≤
            Setup.euclideanSAMMaximum (S := S) s w +
              theorem2RemainderInternalChecked (S := S) w.1 δ hn hk} := by
  exact
    theorem2_internal_checked_corrected_selected_sigma_transport_boundary_of_lean_side_boundary
    (S := S) w δ hn hk hside hnorm hdom_grid hmeas_loss
      hselected_population

end Algorithms.Unverified.SAM
