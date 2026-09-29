import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Independence.Basic
import SOptLib.Model.Budget
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Model.Selection
import SOptLib.Model.Stationarity
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Descent

/-!
# STORM

Object-layer reconstruction of Cutkosky--Orabona STOchastic Recursive Momentum.
-/

noncomputable section

set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.nameCheck false

namespace Algorithms.Unverified.StochasticRecursiveMomentum

/-- Paper-facing Euclidean decision space `ℝ^d`. -/
abbrev DecisionSpace (d : ℕ) : Type :=
  EuclideanSpace ℝ (Fin d)

variable {Ω Sample E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open MeasureTheory
open scoped BigOperators
open scoped InnerProductSpace
open scoped Topology

/-- Paper-facing data for Algorithm 1.

The sample stream is zero-based: `sample 0` represents the paper's `ξ₁`, and
`sample n` represents `ξ_{n+1}`.  The iterates and directions are not fields of
this setup; they are generated below by the canonical STORM recursion.

Source: `book/STORM/StochasticRecursiveMomentum.json#/setup`, which states
`F : ℝ^d → ℝ` and `x ∈ ℝ^d, ξ₁, ..., ξ_T ∈ Ξ`; Algorithm 1 input/initialization
is at `#/algorithm_spec/initialization`. -/
structure Setup (Ω Sample E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- Initial point `x₁` in Algorithm 1. -/
  x₁ : E
  /-- Sample stream `ξ₁, ξ₂, ...`; internally `sample n = ξ_{n+1}`. -/
  sample : ℕ → Ω → Sample
  /-- Sample loss `(x, ξ) ↦ f(x, ξ)`. -/
  sampleLoss : E → Sample → ℝ
  /-- Objective value `F : ℝ^d → ℝ`. -/
  objectiveValue : E → ℝ
  /-- Algorithm parameter `k`. -/
  k : ℝ
  /-- Algorithm parameter `w`. -/
  w : ℝ
  /-- Algorithm parameter `c`. -/
  c : ℝ

namespace Setup

/-- Stochastic-gradient oracle `(x, ξ) ↦ ∇ f(x, ξ)`, computed from the sample loss. -/
def stochasticGradient (S : Setup Ω Sample E) (x : E) (ξ : Sample) : E :=
  gradient (fun y : E => S.sampleLoss y ξ) x

/-- Objective gradient `x ↦ ∇ F(x)`, computed from the paper objective value. -/
def objectiveGradient (S : Setup Ω Sample E) (x : E) : E :=
  gradient S.objectiveValue x

/-- Source-facing expectation value of a real random variable.

This is the Section 3 boundary between the paper notation `𝔼[Z]` and
Mathlib's total Bochner integral: the source expectation exists only when the
integrand is integrable. -/
noncomputable def sourceRealExpectationValue
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) : Option ℝ :=
  by
    classical
    exact if h : Integrable Z μ then some (∫ ω, Z ω ∂μ) else none

/-- Source-facing upper bound for a real expectation. -/
def sourceRealExpectationLE
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) (bound : ℝ) : Prop :=
  ∃ value, sourceRealExpectationValue μ Z = some value ∧ value ≤ bound

/-- Real-valued source expectation spec for route-local proof work. -/
private theorem sourceRealExpectationValue_eq_some_iff
    [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) (v : ℝ) :
    sourceRealExpectationValue μ Z = some v ↔
      Integrable Z μ ∧ v = ∫ ω, Z ω ∂μ := by
  classical
  unfold sourceRealExpectationValue
  by_cases h : Integrable Z μ
  · constructor
    · intro hsome
      have hval : (∫ ω, Z ω ∂μ) = v := by
        simpa [h] using hsome
      exact ⟨h, hval.symm⟩
    · intro hpack
      have hval : (∫ ω, Z ω ∂μ) = v := hpack.2.symm
      simpa [h, hval]
  · constructor
    · intro hsome
      simp [h] at hsome
    · intro hpack
      exact (h hpack.1).elim

/-- Source-facing expected sample-loss objective at stream coordinate `n`. -/
noncomputable def sourceExpectedLossObjectiveAtTimeValue
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (n : ℕ) (x : E) :
    Option ℝ :=
  sourceRealExpectationValue μ (fun ω => S.sampleLoss x (S.sample n ω))

/-- Source-facing second moment of the centered stochastic gradient. -/
noncomputable def sourceGradientNoiseSecondMomentValue
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (n : ℕ) (x : E) :
    Option ℝ :=
  sourceRealExpectationValue μ
    (fun ω => ‖stochasticGradient S x (S.sample n ω) - objectiveGradient S x‖ ^ 2)

/-- Source-facing gradient-noise second-moment bound.

The displayed Section 3 assumption is an expectation of the squared norm of a
centered stochastic-gradient random variable.  In Lean, that source expression
must expose both the scalar expectation bound and the Bochner measurability of
the centered vector random variable it is formed from.  This is still scoped to
the sampled coordinate law; it does not assert any off-stream joint
measurability of `(x, ξ) ↦ ∇f(x, ξ)`. -/
def sourceGradientNoiseSecondMomentLE
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) (n : ℕ) (x : E) (bound : ℝ) : Prop :=
  AEStronglyMeasurable
      (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ ∧
    AEStronglyMeasurable
      (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
      (Measure.map (S.sample n) μ) ∧
    sourceRealExpectationLE μ
      (fun ω => ‖stochasticGradient S x (S.sample n ω) - objectiveGradient S x‖ ^ 2)
      bound

/-- Expected sample-loss objective at stream coordinate `n`. -/
noncomputable def expectedLossObjectiveAtTime
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (n : ℕ) : E → ℝ :=
  SOptLib.paperObjective μ S.sampleLoss (S.sample n)

section Section3Oracle

variable [MeasurableSpace E]

/-- Section 3 source assumptions for STORM.

This package records only assumptions stated in the paper: independent samples,
the function-value oracle, bounded gradient noise, finite lower bound,
almost-sure differentiability/smoothness, and the G-Lipschitz sample-loss
condition used by the adaptive analysis.

Source: `book/STORM/StochasticRecursiveMomentum.json#/assumptions`, entries
`independent_samples`, `function_oracle`, `gradient_noise_bound`,
`finite_lower_bound`, `differentiable_losses`, `L_smooth_losses`, and
`G_lipschitz_losses`.  The law-scoped `L_smooth_sample_law` field is the same
source a.s. smoothness statement read under the distribution of the random
variable `ξ_t`; it is intentionally much narrower than a full off-stream joint
measurability assumption on `(x, ξ) ↦ ∇ f(x, ξ)`. -/
structure Section3Assumptions
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L G σ fStar : ℝ) : Prop where
  /-- `ξ₁, …, ξ_T` are independent; encoded for the full stream. -/
  independent_samples : ProbabilityTheory.iIndepFun S.sample μ
  /-- Each `ξ_t` is a random variable. This is the measurability part of the
  source phrase "independent random variables" and is needed by the generated
  sample-prefix filtration APIs. -/
  sample_measurable : ∀ n, Measurable (S.sample n)
  /-- `𝔼[f(x, ξ_t) | x] = F(x)`, represented as the expected-loss objective at each
  stream coordinate. -/
  function_oracle :
    ∀ n x, sourceExpectedLossObjectiveAtTimeValue S μ n x = some (S.objectiveValue x)
  /-- `𝔼[‖∇f(x, ξ_t) - ∇F(x)‖²] ≤ σ²`. -/
  gradient_noise_bound :
    ∀ n x, sourceGradientNoiseSecondMomentLE S μ n x (σ ^ 2)
  /-- `F* = inf_x F(x)`, encoded as the greatest lower bound of objective values. -/
  finite_lower_bound : IsGLB (Set.range S.objectiveValue) fStar
  /-- Sample losses are differentiable as functions of `x` with probability one. -/
  differentiable_losses :
    ∀ n, ∀ᵐ ω ∂μ, ∀ x, HasGradientAt (fun y : E => S.sampleLoss y (S.sample n ω))
      (stochasticGradient S x (S.sample n ω)) x
  /-- Sample losses are `L`-smooth as functions of `x` with probability one. -/
  L_smooth_losses :
    ∀ n, ∀ᵐ ω ∂μ, ∀ x y,
      ‖stochasticGradient S x (S.sample n ω) -
          stochasticGradient S y (S.sample n ω)‖ ≤ L * ‖x - y‖
  /-- The same `L`-smoothness assumption, read under the sample-coordinate law.
  This is the paper's "with probability 1" statement for the random variable
  `ξ_t`, and supplies law-scoped regularity without asserting off-stream joint
  kernel measurability. -/
  L_smooth_sample_law :
    ∀ n, ∀ᵐ ξ ∂Measure.map (S.sample n) μ, ∀ x y,
      ‖stochasticGradient S x ξ - stochasticGradient S y ξ‖ ≤ L * ‖x - y‖
  /-- Sample losses are `G`-Lipschitz for the adaptive analysis. -/
  G_lipschitz_losses :
    ∀ n, ∀ᵐ ω ∂μ, ∀ x, ‖stochasticGradient S x (S.sample n ω)‖ ≤ G

/-- The function-value oracle identifies every stream-coordinate expected loss
with the paper objective `F`. -/
theorem sourceExpectedLossObjectiveAtTimeValue_eq_objectiveValue
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    sourceExpectedLossObjectiveAtTimeValue S μ n x = some (S.objectiveValue x) :=
  hsec3.function_oracle n x

/-- Section 3's "random variables" sample-stream assumption exposes coordinate
measurability. -/
theorem section3_sample_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    Measurable (S.sample n) :=
  hsec3.sample_measurable n

/-!
The next counterexample is deliberately private and theorem-local evidence for
the reconstruction boundary.  The current Section 3 record constrains the
sampled stream and the gradient-noise expressions only along the law of that
stream.  It does not constrain off-stream sample points.  Therefore full joint
measurability of `(x, ξ) ↦ ∇f(x, ξ)` is not derivable from the record in this
generic object model.
-/

private inductive TwoPointSample
  | off
  | on
  | hidden
  deriving DecidableEq

private instance twoPointSampleMeasurableSpace : MeasurableSpace TwoPointSample :=
  MeasurableSpace.generateFrom ({({TwoPointSample.off} : Set TwoPointSample)} : Set (Set TwoPointSample))

private def offStreamNonmeasurableGradientSetup :
    Setup Unit TwoPointSample ℝ :=
  { x₁ := 0
    sample := fun _ _ => TwoPointSample.off
    sampleLoss := fun x ξ => if ξ = TwoPointSample.on then x else 0
    objectiveValue := fun _ => 0
    k := 1
    w := 1
    c := 1 }

private theorem offStreamNonmeasurableGradientSetup_stochasticGradient_off
    (x : ℝ) :
    stochasticGradient offStreamNonmeasurableGradientSetup x TwoPointSample.off = 0 := by
  simp [stochasticGradient, offStreamNonmeasurableGradientSetup]

private theorem offStreamNonmeasurableGradientSetup_stochasticGradient_hidden
    (x : ℝ) :
    stochasticGradient offStreamNonmeasurableGradientSetup x TwoPointSample.hidden = 0 := by
  simp [stochasticGradient, offStreamNonmeasurableGradientSetup]

private theorem offStreamNonmeasurableGradientSetup_stochasticGradient_on
    (x : ℝ) :
    stochasticGradient offStreamNonmeasurableGradientSetup x TwoPointSample.on = 1 := by
  have hgrad : HasGradientAt (fun y : ℝ => y) 1 x := by
    simpa using (hasDerivAt_id x).hasGradientAt
  exact hgrad.gradient

private theorem twoPointSample_on_indicator_not_measurable :
    ¬ Measurable
      (fun ξ : TwoPointSample => if ξ = TwoPointSample.on then (1 : ℝ) else 0) := by
  intro h
  have hset :
      MeasurableSet
        ((fun ξ : TwoPointSample => if ξ = TwoPointSample.on then (1 : ℝ) else 0) ⁻¹'
          ({1} : Set ℝ)) :=
    h (measurableSet_singleton (1 : ℝ))
  have hpre :
      ((fun ξ : TwoPointSample => if ξ = TwoPointSample.on then (1 : ℝ) else 0) ⁻¹'
          ({1} : Set ℝ)) = {TwoPointSample.on} := by
    ext ξ
    cases ξ <;> simp
  rw [hpre] at hset
  have hgen := (MeasureTheory.measurableSet_generateFrom_singleton_iff
    (s := ({TwoPointSample.off} : Set TwoPointSample))
    (t := ({TwoPointSample.on} : Set TwoPointSample))).1 hset
  rcases hgen with h | h | h | h
  · have : TwoPointSample.on ∈ ({TwoPointSample.on} : Set TwoPointSample) := by simp
    rw [h] at this
    exact this
  · have : TwoPointSample.on ∈ ({TwoPointSample.off} : Set TwoPointSample) := by
      rw [← h]
      simp
    simp at this
  · have : TwoPointSample.hidden ∈ ({TwoPointSample.off}ᶜ : Set TwoPointSample) := by simp
    have hnot : TwoPointSample.hidden ∉ ({TwoPointSample.on} : Set TwoPointSample) := by simp
    rw [← h] at this
    exact hnot this
  · have : TwoPointSample.hidden ∈ ({TwoPointSample.on} : Set TwoPointSample) := by
      rw [h]
      simp
    simp at this

private theorem iIndepFun_const_unit_twoPointSample_off :
    ProbabilityTheory.iIndepFun
      (fun _ : ℕ => fun _ : Unit => TwoPointSample.off) (Measure.dirac ()) := by
  rw [ProbabilityTheory.iIndepFun_iff_iIndep]
  rw [ProbabilityTheory.iIndep_iff]
  intro s f _hf
  simp only [Measure.dirac_apply]
  by_cases hmem : () ∈ ⋂ i ∈ s, f i
  · have hall : ∀ i ∈ s, () ∈ f i := by
      intro i hi
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hmem i) hi)
    simp only [hmem, Set.indicator_of_mem]
    exact (Finset.prod_eq_one fun i hi => by simp [hall i hi]).symm
  · have hnot : ∃ i ∈ s, () ∉ f i := by
      by_contra h
      push Not at h
      exact hmem (by
        simp only [Set.mem_iInter]
        intro i
        exact h i)
    rcases hnot with ⟨i, hi, hif⟩
    have hprod0 :
        ∏ x ∈ s, (f x).indicator (fun _ : Unit => (1 : ENNReal)) () = 0 := by
      refine Finset.prod_eq_zero hi ?_
      simp [hif]
    simpa [hmem] using hprod0.symm

private theorem offStreamNonmeasurableGradientSetup_section3Assumptions :
    Section3Assumptions offStreamNonmeasurableGradientSetup
      (Measure.dirac ()) 0 0 0 0 := by
  refine
    { independent_samples := ?_
      sample_measurable := ?_
      function_oracle := ?_
      gradient_noise_bound := ?_
      finite_lower_bound := ?_
      differentiable_losses := ?_
      L_smooth_losses := ?_
      L_smooth_sample_law := ?_
      G_lipschitz_losses := ?_ }
  · simpa [offStreamNonmeasurableGradientSetup] using
      iIndepFun_const_unit_twoPointSample_off
  · intro n
    exact measurable_const
  · intro n x
    simp [sourceExpectedLossObjectiveAtTimeValue, sourceRealExpectationValue,
      offStreamNonmeasurableGradientSetup]
  · intro n x
    refine ⟨?_, ?_, 0, ?_, by norm_num⟩
    · simp [offStreamNonmeasurableGradientSetup, stochasticGradient, objectiveGradient]
    ·
      refine
        aestronglyMeasurable_map_of_measurable_on_ae_support
          (P := Measure.dirac ()) (wt := fun _ : Unit => TwoPointSample.off)
          (A := ({TwoPointSample.off} : Set TwoPointSample))
          (φ := fun ξ => stochasticGradient offStreamNonmeasurableGradientSetup x ξ -
            objectiveGradient offStreamNonmeasurableGradientSetup x) ?_ ?_ ?_
      · exact MeasurableSpace.measurableSet_generateFrom (by simp)
      · have hzero :
            (fun z : {ξ : TwoPointSample // ξ ∈ ({TwoPointSample.off} : Set TwoPointSample)} =>
              stochasticGradient offStreamNonmeasurableGradientSetup x z -
                objectiveGradient offStreamNonmeasurableGradientSetup x) =
              fun _ => (0 : ℝ) := by
          ext z
          have hz : (z : TwoPointSample) = TwoPointSample.off := by
            change (z : TwoPointSample) = TwoPointSample.off
            exact z.2
          rw [hz, offStreamNonmeasurableGradientSetup_stochasticGradient_off]
          simp [objectiveGradient, offStreamNonmeasurableGradientSetup]
        rw [hzero]
        exact stronglyMeasurable_const
      · rw [Measure.map_const]
        have hAtom : MeasurableSet ({z : TwoPointSample | z = TwoPointSample.off}) := by
          simpa using MeasurableSpace.measurableSet_generateFrom
            (show ({TwoPointSample.off} : Set TwoPointSample) ∈
              ({({TwoPointSample.off} : Set TwoPointSample)} : Set (Set TwoPointSample)) by
                simp)
        simpa using (MeasureTheory.ae_dirac_iff hAtom).2 rfl
    · simp [sourceRealExpectationValue, offStreamNonmeasurableGradientSetup,
        stochasticGradient, objectiveGradient]
  · simpa [offStreamNonmeasurableGradientSetup] using
      (isGLB_singleton : IsGLB ({0} : Set ℝ) 0)
  · intro n
    exact Filter.Eventually.of_forall fun ω x => by
      change HasGradientAt (fun _ : ℝ => 0)
        (stochasticGradient offStreamNonmeasurableGradientSetup x TwoPointSample.off) x
      rw [offStreamNonmeasurableGradientSetup_stochasticGradient_off]
      exact hasGradientAt_const (𝕜 := ℝ) (F := ℝ) x (0 : ℝ)
  · intro n
    exact Filter.Eventually.of_forall fun ω x y => by
      change ‖stochasticGradient offStreamNonmeasurableGradientSetup x TwoPointSample.off -
          stochasticGradient offStreamNonmeasurableGradientSetup y TwoPointSample.off‖ ≤ 0 * ‖x - y‖
      simp [offStreamNonmeasurableGradientSetup_stochasticGradient_off]
  · intro n
    exact Filter.Eventually.of_forall fun ξ x y => by
      cases ξ
      · simp [offStreamNonmeasurableGradientSetup_stochasticGradient_off]
      · simp [offStreamNonmeasurableGradientSetup_stochasticGradient_on]
      · simp [offStreamNonmeasurableGradientSetup_stochasticGradient_hidden]
  · intro n
    exact Filter.Eventually.of_forall fun ω x => by
      change ‖stochasticGradient offStreamNonmeasurableGradientSetup x TwoPointSample.off‖ ≤ 0
      simp [offStreamNonmeasurableGradientSetup_stochasticGradient_off]

private theorem section3_assumptions_do_not_imply_joint_stochasticGradient_measurable :
    Section3Assumptions offStreamNonmeasurableGradientSetup
        (Measure.dirac ()) 0 0 0 0 ∧
      ¬ Measurable
        (fun p : ℝ × TwoPointSample =>
          stochasticGradient offStreamNonmeasurableGradientSetup p.1 p.2) := by
  refine ⟨offStreamNonmeasurableGradientSetup_section3Assumptions, ?_⟩
  intro hjoint
  have hfiber :
      Measurable
        (fun ξ : TwoPointSample =>
          stochasticGradient offStreamNonmeasurableGradientSetup (0 : ℝ) ξ) :=
    SOptLib.measurable_fiber_of_prod_measurable hjoint (0 : ℝ)
  have hfiber_eq :
      (fun ξ : TwoPointSample =>
          stochasticGradient offStreamNonmeasurableGradientSetup (0 : ℝ) ξ) =
        (fun ξ : TwoPointSample => if ξ = TwoPointSample.on then (1 : ℝ) else 0) := by
    ext ξ
    cases ξ
    · simp [offStreamNonmeasurableGradientSetup_stochasticGradient_off]
    · simp [offStreamNonmeasurableGradientSetup_stochasticGradient_on]
    · simp [offStreamNonmeasurableGradientSetup_stochasticGradient_hidden]
  exact twoPointSample_on_indicator_not_measurable (hfiber_eq ▸ hfiber)

/-- The all-fiber measurability supplier needed by the global Carathéodory
terminal is not a consequence of the current Section 3 source record.

This is a same-interface obstruction for the tempting route through
`sampled_product_residual_aestronglyMeasurable_of_caratheodory`: its
`∀ x, Measurable (residual x)` premise would again require off-stream sample
regularity that Section 3 does not state.  The active Lemma 3 route must
therefore stay law-scoped, using sampled/product-law representatives rather
than a global stochastic-gradient kernel. -/
private theorem section3_assumptions_do_not_imply_global_residual_fiber_measurable :
    Section3Assumptions offStreamNonmeasurableGradientSetup
        (Measure.dirac ()) 0 0 0 0 ∧
      ¬ (∀ x : ℝ,
        Measurable
          (fun ξ : TwoPointSample =>
            stochasticGradient offStreamNonmeasurableGradientSetup x ξ -
              objectiveGradient offStreamNonmeasurableGradientSetup x)) := by
  refine ⟨offStreamNonmeasurableGradientSetup_section3Assumptions, ?_⟩
  intro hfiber_all
  have hfiber := hfiber_all 0
  have hfiber_eq :
      (fun ξ : TwoPointSample =>
          stochasticGradient offStreamNonmeasurableGradientSetup (0 : ℝ) ξ -
            objectiveGradient offStreamNonmeasurableGradientSetup (0 : ℝ)) =
        (fun ξ : TwoPointSample => if ξ = TwoPointSample.on then (1 : ℝ) else 0) := by
    ext ξ
    cases ξ
    · rw [offStreamNonmeasurableGradientSetup_stochasticGradient_off]
      simp [objectiveGradient, offStreamNonmeasurableGradientSetup]
    · rw [offStreamNonmeasurableGradientSetup_stochasticGradient_on]
      simp [objectiveGradient, offStreamNonmeasurableGradientSetup]
    · rw [offStreamNonmeasurableGradientSetup_stochasticGradient_hidden]
      simp [objectiveGradient, offStreamNonmeasurableGradientSetup]
  exact twoPointSample_on_indicator_not_measurable (hfiber_eq ▸ hfiber)

/-- If a regular stochastic-gradient oracle is available, its fixed fibers are
measurable.  The counterexample above shows that the joint regularity premise
is not derivable from the current generic Section 3 record alone. -/
private theorem section3_stochasticGradient_fiber_measurable_of_joint
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (hjoint : Measurable (fun p : E × Sample => stochasticGradient S p.1 p.2)) (x : E) :
    Measurable (fun ξ => stochasticGradient S x ξ) := by
  exact SOptLib.measurable_fiber_of_prod_measurable hjoint x

/-- Random-query stochastic gradients are measurable once the query and fresh
sample are measurable and the oracle kernel is regular. -/
private theorem section3_stochasticGradient_random_query_measurable_of_joint
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (hjoint : Measurable (fun p : E × Sample => stochasticGradient S p.1 p.2))
    {query : Ω → E} {sample : Ω → Sample}
    (hquery : Measurable query) (hsample : Measurable sample) :
    Measurable (fun ω => stochasticGradient S (query ω) (sample ω)) := by
  simpa [Function.comp_def] using hjoint.comp (hquery.prodMk hsample)

/-- Any sample-prefix-measurable quantity is independent of a future sample
under the Section 3 independent-random-variable stream assumption. -/
private theorem section3_indepFun_prefixMeasurable_future
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace β]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    {wt : Ω → β} {n i : ℕ}
    (hwt : Measurable[(⨆ j < n, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))] wt)
    (hni : n ≤ i) :
    ProbabilityTheory.IndepFun wt (S.sample i) μ :=
  ProbabilityTheory.iIndepFun.indepFun_prefixMeasurable_future
    S.sample hsec3.sample_measurable hsec3.independent_samples hwt hni

/-- A.e. measurability with respect to a chosen source sigma algebra. -/
private def prefixAEMeasurable
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    (m : MeasurableSpace Ω) (wt : Ω → β) (μ : @Measure Ω mΩ) : Prop :=
  ∃ wt' : Ω → β, Measurable[m] wt' ∧ wt =ᵐ[μ] wt'

private theorem prefixAEMeasurable_of_measurable
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {m : MeasurableSpace Ω} {wt : Ω → β} {μ : @Measure Ω mΩ}
    (hwt : Measurable[m] wt) :
    @prefixAEMeasurable Ω β mΩ _ m wt μ :=
  ⟨wt, hwt, Filter.EventuallyEq.rfl⟩

private theorem prefixAEMeasurable_of_aestronglyMeasurable
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] [BorelSpace β]
    {m : MeasurableSpace Ω} {wt : Ω → β} {μ : @Measure Ω mΩ}
    (hwt : AEStronglyMeasurable[m] wt μ) :
    @prefixAEMeasurable Ω β mΩ _ m wt μ :=
  ⟨hwt.mk wt, hwt.stronglyMeasurable_mk.measurable, hwt.ae_eq_mk⟩

private theorem prefixAEMeasurable_comp_of_map_aestronglyMeasurable
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace β]
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] [BorelSpace β]
    {sample : Ω → Sample} {φ : Sample → β}
    {μ : @Measure Ω mΩ}
    (hφ : AEStronglyMeasurable φ (Measure.map sample μ))
    (hsample : AEMeasurable sample μ) :
    @prefixAEMeasurable Ω β mΩ _
      (MeasurableSpace.comap sample (by infer_instance : MeasurableSpace Sample))
      (fun ω => φ (sample ω)) μ := by
  exact
    prefixAEMeasurable_of_aestronglyMeasurable
      (by
        simpa [Function.comp_def] using
          (hφ.comp_ae_measurable' hsample))

private theorem prefixAEMeasurable.mono
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {m m' : MeasurableSpace Ω} {wt : Ω → β} {μ : @Measure Ω mΩ}
    (hwt : @prefixAEMeasurable Ω β mΩ _ m wt μ) (hm : m ≤ m') :
    @prefixAEMeasurable Ω β mΩ _ m' wt μ := by
  rcases hwt with ⟨wt', hwt', h_eq⟩
  exact ⟨wt', hwt'.mono hm le_rfl, h_eq⟩

private theorem prefixAEMeasurable.congr
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {m : MeasurableSpace Ω} {f g : Ω → β} {μ : @Measure Ω mΩ}
    (hf : @prefixAEMeasurable Ω β mΩ _ m f μ) (hfg : f =ᵐ[μ] g) :
    @prefixAEMeasurable Ω β mΩ _ m g μ := by
  rcases hf with ⟨f', hf', hfeq⟩
  exact ⟨f', hf', hfg.symm.trans hfeq⟩

private theorem prefixAEMeasurable.aemeasurable
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace β]
    (S : Setup Ω Sample E) (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ]
    {L G σ fStar : ℝ} (hsec3 : Section3Assumptions S μ L G σ fStar)
    {wt : Ω → β} {n : ℕ}
    (hwt : @prefixAEMeasurable Ω β mΩ _ (⨆ j < n, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample)) wt μ) :
    AEMeasurable wt μ := by
  rcases hwt with ⟨wt', hwt', h_eq⟩
  have hwt'_ambient : Measurable wt' :=
    hwt'.mono (iSup₂_le fun j _hj => (hsec3.sample_measurable j).comap_le) le_rfl
  exact hwt'_ambient.aemeasurable.congr h_eq.symm

/-- Product closure for a.e.-prefix-measurable representatives. -/
private theorem prefixAEMeasurable.prod
    [mΩ : MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {m : MeasurableSpace Ω} {f : Ω → α} {g : Ω → β} {μ : @Measure Ω mΩ}
    (hf : @prefixAEMeasurable Ω α mΩ _ m f μ)
    (hg : @prefixAEMeasurable Ω β mΩ _ m g μ) :
    @prefixAEMeasurable Ω (α × β) mΩ _ m (fun ω => (f ω, g ω)) μ := by
  rcases hf with ⟨f', hf', hfeq⟩
  rcases hg with ⟨g', hg', hgeq⟩
  refine ⟨fun ω => (f' ω, g' ω), hf'.prod hg', ?_⟩
  filter_upwards [hfeq, hgeq] with ω hfω hgω
  simp [hfω, hgω]

private theorem prefixAEMeasurable.comp_measurable
    [mΩ : MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {m : MeasurableSpace Ω} {f : Ω → α} {g : α → β} {μ : @Measure Ω mΩ}
    (hf : @prefixAEMeasurable Ω α mΩ _ m f μ)
    (hg : Measurable g) :
    @prefixAEMeasurable Ω β mΩ _ m (fun ω => g (f ω)) μ := by
  rcases hf with ⟨f', hf', hfeq⟩
  refine ⟨fun ω => g (f' ω), hg.comp hf', ?_⟩
  filter_upwards [hfeq] with ω hfω
  simp [hfω]

private theorem prefixAEMeasurable.add
    [mΩ : MeasurableSpace Ω]
    {d : ℕ} {m : MeasurableSpace Ω} {f g : Ω → DecisionSpace d}
    {μ : @Measure Ω mΩ}
    (hf : @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m f μ)
    (hg : @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m g μ) :
    @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m (fun ω => f ω + g ω) μ := by
  rcases hf with ⟨f', hf', hfeq⟩
  rcases hg with ⟨g', hg', hgeq⟩
  refine ⟨fun ω => f' ω + g' ω, hf'.add hg', ?_⟩
  filter_upwards [hfeq, hgeq] with ω hfω hgω
  simp [hfω, hgω]

private theorem prefixAEMeasurable.real_add
    [mΩ : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} {f g : Ω → ℝ}
    {μ : @Measure Ω mΩ}
    (hf : @prefixAEMeasurable Ω ℝ mΩ _ m f μ)
    (hg : @prefixAEMeasurable Ω ℝ mΩ _ m g μ) :
    @prefixAEMeasurable Ω ℝ mΩ _ m (fun ω => f ω + g ω) μ := by
  rcases hf with ⟨f', hf', hfeq⟩
  rcases hg with ⟨g', hg', hgeq⟩
  refine ⟨fun ω => f' ω + g' ω, hf'.add hg', ?_⟩
  filter_upwards [hfeq, hgeq] with ω hfω hgω
  simp [hfω, hgω]

private theorem prefixAEMeasurable.sub
    [mΩ : MeasurableSpace Ω]
    {d : ℕ} {m : MeasurableSpace Ω} {f g : Ω → DecisionSpace d}
    {μ : @Measure Ω mΩ}
    (hf : @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m f μ)
    (hg : @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m g μ) :
    @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m (fun ω => f ω - g ω) μ := by
  rcases hf with ⟨f', hf', hfeq⟩
  rcases hg with ⟨g', hg', hgeq⟩
  refine ⟨fun ω => f' ω - g' ω, hf'.sub hg', ?_⟩
  filter_upwards [hfeq, hgeq] with ω hfω hgω
  simp [hfω, hgω]

/-- Real scalar multiplication closure for a.e.-prefix-measurable
representatives. -/
private theorem prefixAEMeasurable.real_smul
    [mΩ : MeasurableSpace Ω]
    {d : ℕ} {m : MeasurableSpace Ω} {a : Ω → ℝ}
    {v : Ω → DecisionSpace d} {μ : @Measure Ω mΩ}
    (ha : @prefixAEMeasurable Ω ℝ mΩ _ m a μ)
    (hv : @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m v μ) :
    @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m (fun ω => a ω • v ω) μ := by
  rcases ha with ⟨a', ha', haeq⟩
  rcases hv with ⟨v', hv', hveq⟩
  refine ⟨fun ω => a' ω • v' ω, ha'.smul hv', ?_⟩
  filter_upwards [haeq, hveq] with ω haω hvω
  simp [haω, hvω]

private theorem prefixAEMeasurable.norm_sq
    [mΩ : MeasurableSpace Ω]
    {d : ℕ} {m : MeasurableSpace Ω} {v : Ω → DecisionSpace d}
    {μ : @Measure Ω mΩ}
    (hv : @prefixAEMeasurable Ω (DecisionSpace d) mΩ _ m v μ) :
    @prefixAEMeasurable Ω ℝ mΩ _ m (fun ω => ‖v ω‖ ^ 2) μ := by
  exact
    @prefixAEMeasurable.comp_measurable Ω (DecisionSpace d) ℝ mΩ _ _ m
      v (fun x : DecisionSpace d => ‖x‖ ^ 2) μ hv
      ((continuous_norm.pow 2).measurable)

private theorem prefixAEMeasurable.const
    [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {m : MeasurableSpace Ω} (b : β) {μ : @Measure Ω mΩ} :
    @prefixAEMeasurable Ω β mΩ _ m (fun _ω => b) μ :=
  @prefixAEMeasurable_of_measurable Ω β mΩ _ m (fun _ω => b) μ measurable_const

/-- A sample-prefix-a.e.-measurable quantity is independent of a future sample.

This is the law-level version of `section3_indepFun_prefixMeasurable_future`.
It is the right regularity level for Lemma 3 after the Section 3 gradient-noise
boundary has exposed a.e. strong measurability under sampled laws rather than
full off-stream kernel measurability. -/
private theorem section3_indepFun_prefixAEMeasurable_future
    [mΩ : MeasurableSpace Ω] [mSample : MeasurableSpace Sample] [mβ : MeasurableSpace β]
    (S : Setup Ω Sample E) (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    {wt : Ω → β} {n i : ℕ} (m : MeasurableSpace Ω)
    (hm : m = (⨆ j < n, MeasurableSpace.comap (S.sample j) mSample))
    (hwt : @prefixAEMeasurable Ω β mΩ mβ m wt μ)
    (hni : n ≤ i) :
    ProbabilityTheory.IndepFun wt (S.sample i) μ := by
  subst m
  rcases hwt with ⟨wt', hrep, hwt_ae⟩
  have hindep_rep :
      ProbabilityTheory.IndepFun wt' (S.sample i) μ :=
    section3_indepFun_prefixMeasurable_future
      (S := S) (μ := μ) (hsec3 := hsec3) (n := n) (i := i)
      (wt := wt') hrep hni
  exact hindep_rep.congr hwt_ae.symm (by
    filter_upwards with ω
    rfl)

/-- Concrete form of the a.e.-prefix/future independence bridge for the sample
prefix sigma algebra.  This avoids repeatedly elaborating the equality witness
for the prefix sigma algebra at Lemma 3 call sites. -/
private theorem section3_indepFun_sample_prefixAEMeasurable_future
    [mΩ : MeasurableSpace Ω] [mSample : MeasurableSpace Sample] [mβ : MeasurableSpace β]
    (S : Setup Ω Sample E) (μ : @Measure Ω mΩ) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    {wt : Ω → β} {n i : ℕ}
    (hwt : @prefixAEMeasurable Ω β mΩ mβ
      (⨆ j < n, MeasurableSpace.comap (S.sample j) mSample) wt μ)
    (hni : n ≤ i) :
    ProbabilityTheory.IndepFun wt (S.sample i) μ := by
  exact
    section3_indepFun_prefixAEMeasurable_future
      S μ hsec3
      (m := (⨆ j < n, MeasurableSpace.comap (S.sample j) mSample))
      rfl hwt hni

/-- The Section 3 function-value oracle exposes integrability of each fixed
sample-loss fiber. -/
private theorem section3_expected_loss_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    Integrable (fun ω => S.sampleLoss x (S.sample n ω)) μ := by
  have hsource := sourceExpectedLossObjectiveAtTimeValue_eq_objectiveValue
    S μ hsec3 n x
  exact
    ((sourceRealExpectationValue_eq_some_iff μ
      (fun ω => S.sampleLoss x (S.sample n ω)) (S.objectiveValue x)).1 hsource).1

/-- The Section 3 function-value oracle identifies each fixed sample-loss
integral with the objective value. -/
private theorem section3_expected_loss_integral_eq_objectiveValue
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    (∫ ω, S.sampleLoss x (S.sample n ω) ∂μ) = S.objectiveValue x := by
  have hsource := sourceExpectedLossObjectiveAtTimeValue_eq_objectiveValue
    S μ hsec3 n x
  exact
    (((sourceRealExpectationValue_eq_some_iff μ
      (fun ω => S.sampleLoss x (S.sample n ω)) (S.objectiveValue x)).1 hsource).2).symm

/-- Section 3's gradient-noise assumption includes the source-definedness of
the displayed second moment. -/
theorem sourceGradientNoiseSecondMomentValue_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    sourceRealExpectationLE μ
      (fun ω => ‖stochasticGradient S x (S.sample n ω) - objectiveGradient S x‖ ^ 2)
      (σ ^ 2) :=
  (hsec3.gradient_noise_bound n x).2.2

/-- The Section 3 gradient-noise assumption exposes the centered stochastic
gradient as a sampled-coordinate vector random variable. -/
theorem sourceGradientNoiseSecondMoment_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    AEStronglyMeasurable
      (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ :=
  (hsec3.gradient_noise_bound n x).1

/-- The Section 3 gradient-noise source expression is also well-defined when
read under the pushed-forward sample-coordinate law.  This is still fixed-query
regularity and does not assert full joint measurability of the off-stream
oracle kernel. -/
theorem sourceGradientNoiseSecondMoment_map_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    AEStronglyMeasurable
      (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
      (Measure.map (S.sample n) μ) :=
  (hsec3.gradient_noise_bound n x).2.1

/-- The Section 3 gradient-noise bound exposes fixed-query square
integrability of the centered stochastic gradient. -/
private theorem section3_gradient_noise_sq_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    Integrable
      (fun ω => ‖stochasticGradient S x (S.sample n ω) - objectiveGradient S x‖ ^ 2)
      μ := by
  rcases sourceGradientNoiseSecondMomentValue_le S μ hsec3 n x with ⟨value, hvalue, _hle⟩
  exact
    ((sourceRealExpectationValue_eq_some_iff μ
      (fun ω => ‖stochasticGradient S x (S.sample n ω) - objectiveGradient S x‖ ^ 2)
      value).1 hvalue).1

/-- Fixed-query residual second moments transported to the pushed-forward
sample-coordinate law.

This is the Section 3 variance assumption at the law used by the Lemma 3
conditioning step.  It is intentionally fixed-query: the rejected stronger
route would assert a globally measurable residual kernel before proving the
sample-product bridge. -/
private theorem section3_sample_law_gradient_residual_sq_integrable_and_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    Integrable
        (fun ξ => ‖stochasticGradient S x ξ - objectiveGradient S x‖ ^ 2)
        (Measure.map (S.sample n) μ) ∧
      ∫ ξ, ‖stochasticGradient S x ξ - objectiveGradient S x‖ ^ 2
        ∂Measure.map (S.sample n) μ ≤ σ ^ 2 := by
  exact integrable_map_measure_and_integral_le_of_comp
    (P := μ) (Y := S.sample n)
    (φ := fun ξ => ‖stochasticGradient S x ξ - objectiveGradient S x‖ ^ 2)
    (bound := σ ^ 2)
    (by
      have hresidual :=
        sourceGradientNoiseSecondMoment_map_aestronglyMeasurable S μ hsec3 n x
      simpa [pow_two] using hresidual.norm.mul hresidual.norm)
    (hsec3.sample_measurable n).aemeasurable
    (section3_gradient_noise_sq_integrable S μ hsec3 n x)
    (by
      rcases sourceGradientNoiseSecondMomentValue_le S μ hsec3 n x with
        ⟨value, hvalue, hle⟩
      have hspec :=
        (sourceRealExpectationValue_eq_some_iff μ
          (fun ω =>
            ‖stochasticGradient S x (S.sample n ω) - objectiveGradient S x‖ ^ 2)
          value).1 hvalue
      simpa only [hspec.2] using hle)

/-- The Section 3 gradient-noise source bound gives fixed-query Bochner
integrability once the vector-valued centered-gradient fiber is known to be
a.e. strongly measurable. -/
private theorem section3_fixed_gradient_residual_integrable_of_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E)
    (hmeas :
      AEStronglyMeasurable
        (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ) :
    Integrable
      (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ := by
  exact
    integrable_of_integrable_norm_sq (μ := μ) hmeas
      (section3_gradient_noise_sq_integrable S μ hsec3 n x)

/-- The Mathlib gradient selector used for `∇F` is the source gradient whenever
the objective is differentiable at the queried point. -/
theorem objectiveGradient_eq_of_hasGradientAt
    (S : Setup Ω Sample E) {x g : E} (hgrad : HasGradientAt S.objectiveValue g x) :
    objectiveGradient S x = g := by
  exact hgrad.gradient

/-- The Mathlib gradient selector used for `∇f(x, ξ)` is the source gradient
whenever the sample loss is differentiable at the queried point. -/
theorem stochasticGradient_eq_of_hasGradientAt
    (S : Setup Ω Sample E) {x g : E} {ξ : Sample}
    (hgrad : HasGradientAt (fun y : E => S.sampleLoss y ξ) g x) :
    stochasticGradient S x ξ = g := by
  exact hgrad.gradient

/-- A fixed stochastic-gradient fiber is centered if the objective-gradient
selector is justified by differentiating the expected-loss identity. -/
private theorem section3_fixed_gradient_residual_mean_zero_of_integral_gradient
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E)
    (hmeas :
      AEStronglyMeasurable
        (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ)
    (hgrad :
      HasGradientAt S.objectiveValue
        (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) x) :
    Integrable
        (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ ∧
      ∫ ω, stochasticGradient S x (S.sample n ω) - objectiveGradient S x ∂μ = 0 := by
  have hres_int :
      Integrable
        (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ :=
    section3_fixed_gradient_residual_integrable_of_aestronglyMeasurable
      S μ hsec3 n x hmeas
  have hstoch_int :
      Integrable (fun ω => stochasticGradient S x (S.sample n ω)) μ := by
    have hsum := hres_int.add (integrable_const (c := objectiveGradient S x))
    convert hsum using 1
    ext ω
    simp
  have hobj :
      objectiveGradient S x =
        ∫ ω, stochasticGradient S x (S.sample n ω) ∂μ :=
    objectiveGradient_eq_of_hasGradientAt S hgrad
  refine ⟨hres_int, ?_⟩
  calc
    ∫ ω, stochasticGradient S x (S.sample n ω) - objectiveGradient S x ∂μ
        = (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) -
            ∫ _ω, objectiveGradient S x ∂μ := by
          exact integral_sub hstoch_int (integrable_const (c := objectiveGradient S x))
    _ = (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) - objectiveGradient S x := by
          simp
    _ = 0 := by
          rw [← hobj]
          simp

/-- Source-derived differentiating-under-the-integral bridge for the Section 3
function oracle.

The function oracle states `∫ f(x, ξ_n) = F x` at each fixed `x`.  Together
with a.s. differentiability and L-smoothness of the sample losses, the paper's
Lemma 3 proof differentiates this identity to identify `∇F x` with the mean
stochastic gradient.  This declaration isolates that analytic step without
promoting it to a primitive assumption. -/
private theorem section3_objective_hasGradientAt_integral_stochasticGradient
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    HasGradientAt S.objectiveValue
      (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) x := by
  simpa only [section3_expected_loss_integral_eq_objectiveValue S μ hsec3 n] using
    hasGradientAt_integral_of_dominated_of_gradient_le
      μ (fun z ω => S.sampleLoss z (S.sample n ω))
      (fun z ω => stochasticGradient S z (S.sample n ω)) x
      (Set.univ : Set E) (fun _ω => G)
      (Filter.univ_mem : (Set.univ : Set E) ∈ 𝓝 x)
      (Filter.Eventually.of_forall fun z =>
        (section3_expected_loss_integrable S μ hsec3 n z).aestronglyMeasurable)
      (section3_expected_loss_integrable S μ hsec3 n x)
      (by
        have hsum :=
          (sourceGradientNoiseSecondMoment_aestronglyMeasurable S μ hsec3 n x).add
            (aestronglyMeasurable_const :
              AEStronglyMeasurable (fun _ω : Ω => objectiveGradient S x) μ)
        convert hsum using 1
        ext ω
        simp)
      (by simpa using hsec3.G_lipschitz_losses n)
      (integrable_const (c := G))
      (by simpa using hsec3.differentiable_losses n)

/-- Voucher step V1: the function-value oracle gives the exact objective
identity that the differentiation-under-integral route must rewrite. -/
private theorem _voucher_step_section3_expected_loss_identity
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    (fun z : E => ∫ ω, S.sampleLoss z (S.sample n ω) ∂μ) =
      S.objectiveValue := by
  funext z
  exact section3_expected_loss_integral_eq_objectiveValue S μ hsec3 n z

/-- Voucher step V2: the source oracle already supplies neighborhood
a.e.-strong measurability of fixed sample-loss fibers through integrability of
the expected-loss expression. -/
private theorem _voucher_step_section3_expected_loss_neighborhood_aesm
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    ∀ᶠ z in 𝓝 x,
      AEStronglyMeasurable (fun ω => S.sampleLoss z (S.sample n ω)) μ := by
  exact Filter.Eventually.of_forall fun z =>
    (section3_expected_loss_integrable S μ hsec3 n z).aestronglyMeasurable

/-- Voucher step V3: a.s. differentiability of sample losses gives the
Fréchet derivative field needed by Mathlib's parametric-integral theorem. -/
private theorem _voucher_step_section3_sample_loss_fderiv_ae
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ z ∈ (Set.univ : Set E),
      HasFDerivAt (fun y : E => S.sampleLoss y (S.sample n ω))
        (InnerProductSpace.toDual ℝ E (stochasticGradient S z (S.sample n ω))) z := by
  exact (hsec3.differentiable_losses n).mono fun _ω hω z _hz =>
    (hω z).hasFDerivAt

/-- Voucher step V4: the adaptive-analysis Lipschitz assumption gives the
operator-norm domination premise for the derivative kernel. -/
private theorem _voucher_step_section3_sample_loss_fderiv_bound_ae
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ z ∈ (Set.univ : Set E),
      ‖InnerProductSpace.toDual ℝ E (stochasticGradient S z (S.sample n ω))‖ ≤
        (fun _ω : Ω => G) ω := by
  exact (hsec3.G_lipschitz_losses n).mono fun _ω hω z _hz => by
    simpa using hω z

/-- Checked terminal route for
`section3_objective_hasGradientAt_integral_stochasticGradient`.

This is not a new source assumption.  It records the exact Mathlib API path:
once the derivative kernel
`ω ↦ toDual (∇f(x, ξ_n(ω)))` is a.e.-strongly measurable, Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le` differentiates the
function-value oracle identity and produces the required objective gradient. -/
private theorem _voucher_step_section3_objective_hasGradientAt_from_parametric_integral
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E)
    (hdual_aesm :
      AEStronglyMeasurable
        (fun ω => InnerProductSpace.toDual ℝ E
          (stochasticGradient S x (S.sample n ω))) μ) :
    HasGradientAt S.objectiveValue
      (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) x := by
  let F : E → Ω → ℝ := fun z ω => S.sampleLoss z (S.sample n ω)
  let F' : E → Ω → E →L[ℝ] ℝ := fun z ω =>
    InnerProductSpace.toDual ℝ E (stochasticGradient S z (S.sample n ω))
  have hF_id :
      (fun z : E => ∫ ω, F z ω ∂μ) = S.objectiveValue := by
    simpa [F] using _voucher_step_section3_expected_loss_identity S μ hsec3 n
  have hF_meas :
      ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) μ := by
    simpa [F] using
      _voucher_step_section3_expected_loss_neighborhood_aesm S μ hsec3 n x
  have hF_int : Integrable (F x) μ := by
    simpa [F] using section3_expected_loss_integrable S μ hsec3 n x
  have hF'_meas : AEStronglyMeasurable (F' x) μ := by
    simpa [F'] using hdual_aesm
  have hbound :
      ∀ᵐ ω ∂μ, ∀ z ∈ (Set.univ : Set E), ‖F' z ω‖ ≤ (fun _ω : Ω => G) ω := by
    simpa [F'] using
      _voucher_step_section3_sample_loss_fderiv_bound_ae S μ hsec3 n
  have hdiff :
      ∀ᵐ ω ∂μ, ∀ z ∈ (Set.univ : Set E),
        HasFDerivAt (F · ω) (F' z ω) z := by
    simpa [F, F'] using
      _voucher_step_section3_sample_loss_fderiv_ae S μ hsec3 n
  have hderiv :
      HasFDerivAt (fun z : E => ∫ ω, F z ω ∂μ)
        (∫ ω, F' x ω ∂μ) x :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := μ) (F := F) (F' := F') (x₀ := x)
      (bound := fun _ω : Ω => G) (s := Set.univ)
      (Filter.univ_mem : (Set.univ : Set E) ∈ 𝓝 x)
      hF_meas hF_int hF'_meas hbound (integrable_const (c := G)) hdiff
  have hdual_integral :
      (∫ ω, F' x ω ∂μ) =
        InnerProductSpace.toDual ℝ E
          (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) := by
    simpa [F'] using
      (InnerProductSpace.toDual ℝ E).toLinearIsometry.integral_comp_comm
        (fun ω => stochasticGradient S x (S.sample n ω))
  have hderiv_obj :
      HasFDerivAt S.objectiveValue
        (InnerProductSpace.toDual ℝ E
          (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ)) x := by
    simpa [hF_id, hdual_integral] using hderiv
  simpa using hderiv_obj.hasGradientAt

/-- Voucher attempt V0-V4 for the exact repeated hard leaf.

The body is intentionally expanded to the checked terminal theorem above.  The
remaining hole is no longer the full centering statement; it is the exact
a.e.-strong measurability of the derivative kernel needed by Mathlib's
parametric-integral API. -/
private theorem _voucher_attempt_section3_objective_hasGradientAt_integral_stochasticGradient_6
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    (S : Setup Ω Sample E)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : E) :
    HasGradientAt S.objectiveValue
      (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) x := by
  have hdual_aesm :
      AEStronglyMeasurable
        (fun ω => InnerProductSpace.toDual ℝ E
          (stochasticGradient S x (S.sample n ω))) μ := by
    have hres_aesm :
        AEStronglyMeasurable
          (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ :=
      sourceGradientNoiseSecondMoment_aestronglyMeasurable S μ hsec3 n x
    have hgrad_aesm :
        AEStronglyMeasurable (fun ω => stochasticGradient S x (S.sample n ω)) μ := by
      have hsum := hres_aesm.add (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ω : Ω => objectiveGradient S x) μ)
      convert hsum using 1
      ext ω
      simp
    exact (InnerProductSpace.toDual ℝ E).continuous.comp_aestronglyMeasurable hgrad_aesm
  exact
    _voucher_step_section3_objective_hasGradientAt_from_parametric_integral
      S μ hsec3 n x hdual_aesm

/-- Sampled-law regularity of the fixed centered stochastic-gradient residual
along a concrete sample coordinate.

This is the theorem-local regularity needed to read the Section 3 gradient
noise bound as a Bochner-integrable vector residual.  It is intentionally not a
`Section3Assumptions` field: the source states expectations of sampled
gradients, while the off-stream counterexample above shows that full kernel
measurability is not a consequence of the present generic record. -/
private theorem section3_sampled_gradient_residual_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    AEStronglyMeasurable
      (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ := by
  exact sourceGradientNoiseSecondMoment_aestronglyMeasurable S μ hsec3 n x

/-- Sample-law regularity of the fixed centered residual under
`Measure.map (S.sample n) μ`.

This is the mapped-law counterpart of
`section3_sampled_gradient_residual_aestronglyMeasurable`; it is kept separate
because the full off-stream sample-fiber measurability route is false in the
current object model. -/
private theorem section3_sample_law_gradient_residual_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    AEStronglyMeasurable
      (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
      (Measure.map (S.sample n) μ) := by
  exact sourceGradientNoiseSecondMoment_map_aestronglyMeasurable S μ hsec3 n x

/-- Along an actual stream coordinate, Section 3's a.s. `L`-smoothness makes
the stochastic-gradient selector continuous in the query variable.

This is a source-derived theorem-local regularity fact.  It deliberately stays
under the base sample-path law instead of asserting full off-stream joint
measurability of `(x, ξ) ↦ ∇f(x, ξ)`. -/
private theorem section3_sampled_stochasticGradient_continuous_ae
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      Continuous fun x : DecisionSpace d => stochasticGradient S x (S.sample n ω) := by
  filter_upwards [hsec3.L_smooth_losses n] with ω hsmooth
  have hLip :
      LipschitzWith (Real.toNNReal L)
        (fun x : DecisionSpace d => stochasticGradient S x (S.sample n ω)) := by
    refine lipschitzWith_of_norm_sub_le_mul
      (fun x : DecisionSpace d => stochasticGradient S x (S.sample n ω)) L ?_
    intro x y
    rw [dist_eq_norm]
    exact hsmooth x y
  exact hLip.continuous

/-- Pull back the fixed-query residual representative supplied by the Section
3 gradient-noise source expression to the sigma algebra generated by the
corresponding sample coordinate. -/
private theorem section3_sampled_residual_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (MeasurableSpace.comap (S.sample n) (by infer_instance : MeasurableSpace Sample))
      (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ := by
  exact
    prefixAEMeasurable_comp_of_map_aestronglyMeasurable
      (section3_sample_law_gradient_residual_aestronglyMeasurable S μ hsec3 n x)
      (hsec3.sample_measurable n).aemeasurable

/-- Fixed-query sampled stochastic gradients are a.e.-measurable with respect
to the sigma algebra generated by their sample coordinate.  This is a
law-scoped initialization/transition input, not full off-stream joint kernel
measurability. -/
private theorem section3_sampled_gradient_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (MeasurableSpace.comap (S.sample n) (by infer_instance : MeasurableSpace Sample))
      (fun ω => stochasticGradient S x (S.sample n ω)) μ := by
  have hres :=
    section3_sampled_residual_prefixAEMeasurable S μ hsec3 n x
  have hconst :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (MeasurableSpace.comap (S.sample n) (by infer_instance : MeasurableSpace Sample))
        (fun _ω => objectiveGradient S x) μ :=
    prefixAEMeasurable.const (objectiveGradient S x)
  exact (hres.add hconst).congr (by
    filter_upwards with ω
    simp)

/-- Bochner integral transport from a sampled residual under the base law to
the same residual under the pushed-forward sample law. -/
private theorem section3_fixed_gradient_residual_integral_map_eq_integral_sampled
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (n : ℕ) (x : DecisionSpace d)
    (hsample : Measurable (S.sample n))
    (hfiber_residual_aesm :
      AEStronglyMeasurable
        (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
        (Measure.map (S.sample n) μ)) :
    (∫ ω, stochasticGradient S x (S.sample n ω) - objectiveGradient S x ∂μ) =
      ∫ ξ, stochasticGradient S x ξ - objectiveGradient S x
        ∂Measure.map (S.sample n) μ := by
  exact
    integral_comp_eq_integral_of_map_eq
      (P := μ) (Y := S.sample n)
      (nu := Measure.map (S.sample n) μ)
      (phi := fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
      hsample.aemeasurable hfiber_residual_aesm rfl

/-- Source-derived fixed-fiber centering under the sample-coordinate law. -/
private theorem section3_fixed_gradient_residual_mean_zero_under_sample_law
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    Integrable
        (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
        (Measure.map (S.sample n) μ) ∧
  ∫ ξ, stochasticGradient S x ξ - objectiveGradient S x
        ∂Measure.map (S.sample n) μ = 0 := by
  have hsample : Measurable (S.sample n) := hsec3.sample_measurable n
  have hresidual_aesm :
      AEStronglyMeasurable
        (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ :=
    section3_sampled_gradient_residual_aestronglyMeasurable S μ hsec3 n x
  have hgrad :
      HasGradientAt S.objectiveValue
        (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) x :=
    section3_objective_hasGradientAt_integral_stochasticGradient S μ hsec3 n x
  have hbase :=
    section3_fixed_gradient_residual_mean_zero_of_integral_gradient
      S μ hsec3 n x hresidual_aesm hgrad
  have hfiber_residual_aesm :
      AEStronglyMeasurable
        (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
        (Measure.map (S.sample n) μ) :=
    section3_sample_law_gradient_residual_aestronglyMeasurable S μ hsec3 n x
  refine ⟨?_, ?_⟩
  · exact
      integrable_map_measure_of_integrable_comp hfiber_residual_aesm
        hsample.aemeasurable (by simpa [Function.comp_def] using hbase.1)
  ·
      have htransport :=
        section3_fixed_gradient_residual_integral_map_eq_integral_sampled
          S μ n x hsample hfiber_residual_aesm
      rw [← htransport]
      exact hbase.2

/-- The sampled stochastic-gradient fiber is Bochner-integrable under the base
law. -/
private theorem section3_sampled_stochasticGradient_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    Integrable (fun ω => stochasticGradient S x (S.sample n ω)) μ := by
  have hres_int :
      Integrable
        (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ :=
    section3_fixed_gradient_residual_integrable_of_aestronglyMeasurable
      S μ hsec3 n x
      (section3_sampled_gradient_residual_aestronglyMeasurable S μ hsec3 n x)
  have hsum := hres_int.add (integrable_const (c := objectiveGradient S x))
  convert hsum using 1
  ext ω
  simp

/-- The objective gradient is the mean of the sampled stochastic-gradient
oracle at each fixed query.  This is the source-derived unbiased-gradient
identity used in Lemma 3, obtained from the function-value oracle rather than
stored as a Section 3 assumption. -/
private theorem section3_objectiveGradient_eq_oracleMean
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    SOptLib.oracleMean μ
      (fun z ω => stochasticGradient S z (S.sample n ω)) (fun ω : Ω => ω) x =
        objectiveGradient S x := by
  have hres_aesm :
      AEStronglyMeasurable
        (fun ω => stochasticGradient S x (S.sample n ω) - objectiveGradient S x) μ :=
    section3_sampled_gradient_residual_aestronglyMeasurable S μ hsec3 n x
  have hgrad :
      HasGradientAt S.objectiveValue
        (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) x :=
    section3_objective_hasGradientAt_integral_stochasticGradient S μ hsec3 n x
  have hbase :=
    section3_fixed_gradient_residual_mean_zero_of_integral_gradient
      S μ hsec3 n x hres_aesm hgrad
  have hstoch_int :
      Integrable (fun ω => stochasticGradient S x (S.sample n ω)) μ :=
    section3_sampled_stochasticGradient_integrable S μ hsec3 n x
  have hmean :
      (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) = objectiveGradient S x := by
    have hsub :
        (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) -
            objectiveGradient S x = 0 := by
      have hsplit :
          (∫ ω, stochasticGradient S x (S.sample n ω) -
                objectiveGradient S x ∂μ) =
            (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) -
              ∫ _ω, objectiveGradient S x ∂μ :=
        integral_sub hstoch_int (integrable_const (c := objectiveGradient S x))
      simpa [hsplit] using hbase.2
    exact sub_eq_zero.mp hsub
  simpa [SOptLib.oracleMean_def, hmean]

/-- The adaptive-analysis `G`-Lipschitz sample-gradient assumption bounds the
deterministic objective gradient as its source-derived oracle mean.

This is a theorem-local consequence, not a Section 3 field: it combines the
already proved fixed-fiber mean identity with Mathlib's Bochner integral norm
bound. -/
private theorem section3_objectiveGradient_norm_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) (x : DecisionSpace d) :
    ‖objectiveGradient S x‖ ≤ G := by
  have hmean_integral :
      (∫ ω, stochasticGradient S x (S.sample n ω) ∂μ) =
        objectiveGradient S x := by
    simpa [SOptLib.oracleMean_def] using
      section3_objectiveGradient_eq_oracleMean S μ hsec3 n x
  have hstoch_int :
      Integrable (fun ω => stochasticGradient S x (S.sample n ω)) μ :=
    section3_sampled_stochasticGradient_integrable S μ hsec3 n x
  calc
    ‖objectiveGradient S x‖
        = ‖∫ ω, stochasticGradient S x (S.sample n ω) ∂μ‖ := by
          rw [hmean_integral]
    _ ≤ ∫ ω, ‖stochasticGradient S x (S.sample n ω)‖ ∂μ :=
          norm_integral_le_integral_norm
            (fun ω => stochasticGradient S x (S.sample n ω))
    _ ≤ ∫ _ω, G ∂μ :=
          integral_mono_ae hstoch_int.norm (integrable_const G)
            ((hsec3.G_lipschitz_losses n).mono fun _ω hω => hω x)
    _ = G := by
          simp [integral_const, probReal_univ]

/-- Section 3's samplewise `L`-smoothness transfers to the deterministic
objective-gradient selector through the source-derived oracle-mean identity. -/
private theorem section3_objectiveGradient_lipschitz
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ)
    (x y : DecisionSpace d) :
    ‖objectiveGradient S x - objectiveGradient S y‖ ≤ L * ‖x - y‖ := by
  exact
    oracleMean_lipschitz_of_ae_lipschitz
      (μ := μ)
      (G := fun z ω => stochasticGradient S z (S.sample n ω))
      (g := objectiveGradient S) (L := L) (x := x) (y := y)
      (section3_sampled_stochasticGradient_integrable S μ hsec3 n x)
      (section3_sampled_stochasticGradient_integrable S μ hsec3 n y)
      (section3_objectiveGradient_eq_oracleMean S μ hsec3 n x)
      (section3_objectiveGradient_eq_oracleMean S μ hsec3 n y)
      ((hsec3.L_smooth_losses n).mono fun _ω hω => hω x y)

/-- The source-derived objective-gradient selector is continuous. -/
private theorem section3_objectiveGradient_continuous
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    Continuous (objectiveGradient S) := by
  have hLip : LipschitzWith (Real.toNNReal L) (objectiveGradient S) := by
    refine lipschitzWith_of_norm_sub_le_mul (objectiveGradient S) L ?_
    intro x y
    rw [dist_eq_norm]
    exact section3_objectiveGradient_lipschitz S μ hsec3 n x y
  exact hLip.continuous

/-- Section 3's `G`-Lipschitz stochastic-loss assumption makes the
deterministic objective value `G`-Lipschitz.

This is a derived theorem, not a primitive assumption: combine the
differentiating-under-the-integral objective-gradient bridge with Mathlib's
mean-value theorem and the already-derived bound `‖∇F(x)‖ ≤ G`. -/
private theorem section3_objectiveValue_norm_sub_le_mul
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ)
    (x y : DecisionSpace d) :
    ‖S.objectiveValue y - S.objectiveValue x‖ ≤ G * ‖y - x‖ := by
  classical
  have hgrad :
      ∀ z ∈ (Set.univ : Set (DecisionSpace d)),
        HasFDerivWithinAt S.objectiveValue
          (InnerProductSpace.toDual ℝ (DecisionSpace d) (objectiveGradient S z))
          Set.univ z := by
    intro z _hz
    have hgrad_int :=
      section3_objective_hasGradientAt_integral_stochasticGradient
        S μ hsec3 n z
    have hmean :
        (∫ ω, stochasticGradient S z (S.sample n ω) ∂μ) =
          objectiveGradient S z := by
      simpa [SOptLib.oracleMean_def] using
        section3_objectiveGradient_eq_oracleMean S μ hsec3 n z
    have hgrad_obj :
        HasGradientAt S.objectiveValue (objectiveGradient S z) z := by
      simpa [hmean] using hgrad_int
    exact hgrad_obj.hasFDerivAt.hasFDerivWithinAt
  have hbound :
      ∀ z ∈ (Set.univ : Set (DecisionSpace d)),
        ‖InnerProductSpace.toDual ℝ (DecisionSpace d) (objectiveGradient S z)‖ ≤ G := by
    intro z _hz
    simpa using section3_objectiveGradient_norm_le S μ hsec3 n z
  simpa using
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := Set.univ)
      (f := S.objectiveValue)
      (f' := fun z : DecisionSpace d =>
        InnerProductSpace.toDual ℝ (DecisionSpace d) (objectiveGradient S z))
      (C := G)
      hgrad hbound
      (by simpa using (convex_univ : Convex ℝ (Set.univ : Set (DecisionSpace d))))
      (by simp : x ∈ (Set.univ : Set (DecisionSpace d)))
      (by simp : y ∈ (Set.univ : Set (DecisionSpace d)))

/-- The deterministic objective value is measurable along generated iterates. -/
private theorem section3_objectiveValue_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    Measurable S.objectiveValue := by
  classical
  have hLip : LipschitzWith (Real.toNNReal G) S.objectiveValue := by
    refine lipschitzWith_of_norm_sub_le_mul S.objectiveValue G ?_
    intro x y
    simpa [dist_eq_norm] using
      section3_objectiveValue_norm_sub_le_mul S μ hsec3 n y x
  exact hLip.continuous.measurable

/-- Along an actual stream coordinate, the centered residual kernel is
continuous in the query variable almost surely. -/
private theorem section3_sampled_gradient_residual_continuous_ae
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      Continuous fun x : DecisionSpace d =>
        stochasticGradient S x (S.sample n ω) - objectiveGradient S x := by
  filter_upwards [section3_sampled_stochasticGradient_continuous_ae S μ hsec3 n] with
    ω hstoch_cont
  exact hstoch_cont.sub (section3_objectiveGradient_continuous S μ hsec3 n)

end Section3Oracle

/-- Internal totalized form of the Theorem 1 choice `k = bG^{2/3}/L`.

Use `theorem1KSourceValue` at the paper-expression boundary. -/
def theorem1K (b G L : ℝ) : ℝ :=
  b * Real.rpow G ((2 : ℝ) / 3) / L

/-- Internal totalized form of the Theorem 1 choice `c = L²(28 + 1/(7b³))`.

The paper displays this as equal to `28L² + G²/(7Lk³)`.  The totalized
arithmetic form uses the equivalent `b`-formula; source-level definedness is
tracked separately by `theorem1CSourceValue`. -/
def theorem1C (b L : ℝ) : ℝ :=
  L ^ 2 * (28 + 1 / (7 * b ^ 3))

/-- Internal totalized form of the Theorem 1 choice
`w = G² max((4b)³, 2, (28b + 1/(7b²))³/64)`.

The paper displays this equivalent closed form after the `k,c,L` expression;
using it here keeps the source-facing selector inside the stated scalar
domain and avoids a hidden `1/L` totalization in the `w` formula. -/
def theorem1W (b G : ℝ) : ℝ :=
  G ^ 2 * max ((4 * b) ^ 3) (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64))

/-- Internal totalized algorithm setup with the Theorem 1 parameter choices.

Use `withTheorem1ParametersSourceValue` at the paper-expression boundary. -/
def withTheorem1Parameters
    (S : Setup Ω Sample E) (b G L : ℝ) :
    Setup Ω Sample E :=
  let k := theorem1K b G L
  let c := theorem1C b L
  { S with
    k := k
    c := c
    w := theorem1W b G }

theorem withTheorem1Parameters_k
    (S : Setup Ω Sample E) (b G L : ℝ) :
    (withTheorem1Parameters S b G L).k = theorem1K b G L := by
  rfl

theorem withTheorem1Parameters_c
    (S : Setup Ω Sample E) (b G L : ℝ) :
    (withTheorem1Parameters S b G L).c = theorem1C b L := by
  rfl

theorem withTheorem1Parameters_w
    (S : Setup Ω Sample E) (b G L : ℝ) :
    (withTheorem1Parameters S b G L).w = theorem1W b G := by
  rfl

/-- Theorem 1's scalar parameter substitution changes only Algorithm 1 scalar
parameters.  The Section 3 oracle and sample-stream assumptions are therefore
transported definitionally to the parameterized STORM setup. -/
theorem section3Assumptions_withTheorem1Parameters
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L G σ fStar : ℝ} (hsec3 : Section3Assumptions S μ L G σ fStar)
    (b : ℝ) :
    Section3Assumptions (withTheorem1Parameters S b G L) μ L G σ fStar := by
  refine
    { independent_samples := ?_
      sample_measurable := ?_
      function_oracle := ?_
      gradient_noise_bound := ?_
      finite_lower_bound := ?_
      differentiable_losses := ?_
      L_smooth_losses := ?_
      L_smooth_sample_law := ?_
      G_lipschitz_losses := ?_ }
  · simpa [withTheorem1Parameters] using hsec3.independent_samples
  · intro n
    simpa [withTheorem1Parameters] using hsec3.sample_measurable n
  · intro n x
    simpa [withTheorem1Parameters] using hsec3.function_oracle n x
  · intro n x
    simpa [withTheorem1Parameters] using hsec3.gradient_noise_bound n x
  · simpa [withTheorem1Parameters] using hsec3.finite_lower_bound
  · intro n
    simpa [withTheorem1Parameters] using hsec3.differentiable_losses n
  · intro n
    simpa [withTheorem1Parameters] using hsec3.L_smooth_losses n
  · intro n
    simpa [withTheorem1Parameters] using hsec3.L_smooth_sample_law n
  · intro n
    simpa [withTheorem1Parameters] using hsec3.G_lipschitz_losses n

/-- Totalized Lean arithmetic form of the displayed scalar formula for `M`.

This is an internal arithmetic realization.  The source-facing displayed
expression is modeled below by `theorem1MSourceValue`, which can be undefined
at scalar boundaries where the paper does not state denominator or
nonnegative-radicand side conditions. -/
def theorem1MFormula (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : ℝ :=
  (8 / S.k) * (S.objectiveValue S.x₁ - fStar) +
    Real.rpow S.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * S.k ^ 2) +
      S.k ^ 2 * S.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ)

/-- Totalized Lean arithmetic form of the scalar `M` appearing in Theorem 1.

Use `theorem1MSourceValue` at the paper-expression boundary. -/
def theorem1M
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : ℝ :=
  theorem1MFormula S T L σ fStar

/-- Totalized Lean arithmetic form of the Theorem 1 convergence bound printed
in the paper.

**Source correction notice (arXiv:1905.10018, p. 8, lines 556--563).**  The
last comparison in the paper is not a valid consequence of
`(a + b)^(1/3) ≤ a^(1/3) + b^(1/3)`: splitting the stochastic term leaves the
coefficient `2^(2/3) * sqrt M`, which the printed expression replaces by `2`
without an assumption that justifies this replacement.  This definition is
retained verbatim for source auditing; it is not the RHS of the corrected Lean
theorem below.  See `theorem1CorrectedRHS`.

Use `theorem1RHSSourceValue` at the paper-expression boundary. -/
def theorem1RHS (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : ℝ :=
  let M := theorem1M S T L σ fStar
  (Real.rpow S.w ((1 : ℝ) / 6) * Real.sqrt (2 * M) +
      2 * Real.rpow M ((3 : ℝ) / 4)) / Real.sqrt T +
    2 * Real.rpow σ ((1 : ℝ) / 3) / Real.rpow T ((1 : ℝ) / 3)

/-- Corrected Theorem 1 bound verified in Lean.

This is the penultimate displayed quantity on p. 8 of arXiv:1905.10018,
before the paper's invalid final simplification.  Keeping the stochastic term
unsplit avoids dropping the required `sqrt M` factor and follows directly from
the two scalar alternatives proved in lines 551--554. -/
def theorem1CorrectedRHS
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : ℝ :=
  let M := theorem1M S T L σ fStar
  (Real.sqrt (2 * M) *
        Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6) +
      2 * Real.rpow M ((3 : ℝ) / 4)) /
    Real.sqrt (T : ℝ)

/-- Nonnegativity of the Lipschitz constant is a proof obligation from the
Section 3 `G`-Lipschitz sample-loss assumption, not an extra theorem-head input.

The analogous sign convention for `σ` is deliberately not asserted here: the
source states the variance bound with `σ²`, and Theorem 1 prints `σ^{1/3}`, but
does not state `0 ≤ σ` as a primitive assumption. -/
theorem section3_lipschitz_constant_nonneg_obligation
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    (S : Setup Ω Sample E) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar) :
    0 ≤ G := by
  exact nonneg_of_ae_norm_le μ (fun ω => stochasticGradient S S.x₁ (S.sample 0 ω)) G
    ((_hsec3.G_lipschitz_losses 0).mono fun _ hω => hω S.x₁)

theorem theorem1K_eq (b G L : ℝ) :
    theorem1K b G L = b * Real.rpow G ((2 : ℝ) / 3) / L := by
  rfl

theorem theorem1C_eq (b L : ℝ) :
    theorem1C b L = L ^ 2 * (28 + 1 / (7 * b ^ 3)) := by
  rfl

theorem theorem1W_eq (b G : ℝ) :
    theorem1W b G =
      G ^ 2 * max ((4 * b) ^ 3) (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) := by
  rfl

/-- The displayed Theorem 1 selector gives `w = 0` at the degenerate boundary
`G = 0`, so positivity of `w` cannot be exposed as a paper-facing assumption or
derived theorem without an additional source-backed restriction. -/
theorem theorem1W_eq_zero_of_G_eq_zero (b : ℝ) :
    theorem1W b 0 = 0 := by
  simp [theorem1W]

/-- A displayed paper quotient represented without hiding its denominator.

`sourceQuotientSpec numerator denominator value` says that `value` denotes the
paper expression `numerator / denominator`: the denominator is nonzero and the
displayed quotient equation holds after clearing that denominator. -/
def sourceQuotientSpec (numerator denominator value : ℝ) : Prop :=
  SOptLib.checked_quotient_spec numerator denominator value

/-- Partial source value of a displayed quotient.  Unlike Lean division, this
does not assign a paper meaning when the denominator is zero. -/
def sourceQuotientValue (numerator denominator : ℝ) : Option ℝ :=
  SOptLib.checked_quotient numerator denominator

/-- Partial source value of a displayed nonnegative real power.  This prevents
`Real.rpow`'s total fallback on negative bases from becoming the paper meaning. -/
def sourceNonnegativeRpowValue (base exponent : ℝ) : Option ℝ :=
  if 0 ≤ base then some (Real.rpow base exponent) else none

/-- Partial source value of a displayed positive real power used as a
denominator. -/
def sourcePositiveRpowValue (base exponent : ℝ) : Option ℝ :=
  if 0 < base then some (Real.rpow base exponent) else none

/-- Partial source value of a displayed square root. -/
def sourceSqrtValue (radicand : ℝ) : Option ℝ :=
  if 0 ≤ radicand then some (Real.sqrt radicand) else none

/-- Source-facing Theorem 1 selector `k = bG^{2/3}/L`, undefined when the
displayed denominator or power boundary is unavailable.

Source: `book/STORM/StochasticRecursiveMomentum.json#/main_theorem` and
`#/assumptions/6/math` display `b > 0, k = bG^{2/3}/L`; the source does not
state `L ≠ 0` or `G ≥ 0`, so this source value is partial. -/
def theorem1KSourceValue (b G L : ℝ) : Option ℝ :=
  match sourceNonnegativeRpowValue G ((2 : ℝ) / 3) with
  | some Gpow => sourceQuotientValue (b * Gpow) L
  | none => none

/-- Source-facing Theorem 1 selector
`c = L²(28 + 1/(7b³))`, undefined when the displayed quotient is singular.

Source: `book/STORM/StochasticRecursiveMomentum.json#/main_theorem` and
`#/algorithm_spec/parameters/1/math` display
`c = 28L^2 + G^2/(7Lk^3) = L^2(28 + 1/(7b^3))`; the paper states `b > 0`,
which later bridges this source value to the totalized formula. -/
def theorem1CSourceValue (b L : ℝ) : Option ℝ :=
  match sourceQuotientValue 1 (7 * b ^ 3) with
  | some invTerm => some (L ^ 2 * (28 + invTerm))
  | none => none

/-- Source-facing Theorem 1 selector
`w = G² max((4b)³, 2, (28b + 1/(7b²))³/64)`, with the displayed `1/(7b²)`
kept partial.

Source: `book/STORM/StochasticRecursiveMomentum.json#/main_theorem` and
`#/algorithm_spec/parameters/2/math` display both `w = max((4Lk)^3, 2G^2,
(ck/(4L))^3)` and the equivalent `G^2 max(...)` form; this gives `w = 0`
when `G = 0`, so `w > 0` is not a paper assumption. -/
def theorem1WSourceValue (b G : ℝ) : Option ℝ :=
  match sourceQuotientValue 1 (7 * b ^ 2) with
  | some invTerm =>
      some (G ^ 2 * max ((4 * b) ^ 3) (max 2 (((28 * b + invTerm) ^ 3) / 64)))
  | none => none

/-- Source-facing setup with the Theorem 1 parameter choices.  It is undefined
when one of the displayed scalar selectors is undefined. -/
def withTheorem1ParametersSourceValue
    (S : Setup Ω Sample E) (b G L : ℝ) : Option (Setup Ω Sample E) :=
  match theorem1KSourceValue b G L, theorem1CSourceValue b L, theorem1WSourceValue b G with
  | some k, some c, some w => some { S with k := k, c := c, w := w }
  | _, _, _ => none

/-- Source-facing displayed value of `M` in Theorem 1, with every quotient and
non-integer power boundary exposed by `Option`. -/
def theorem1MSourceValue
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : Option ℝ :=
  match sourceQuotientValue 8 S.k,
      sourceNonnegativeRpowValue S.w ((1 : ℝ) / 3),
      sourceQuotientValue (S.k ^ 2 * S.c ^ 2) (2 * L ^ 2) with
  | some invK8, some wThird, some lastCoeff =>
      match sourceQuotientValue (wThird * σ ^ 2) (4 * L ^ 2 * S.k ^ 2) with
      | some noiseCoeff =>
          some (invK8 * (S.objectiveValue S.x₁ - fStar) +
            noiseCoeff + lastCoeff * Real.log (T + 2 : ℝ))
      | none => none
  | _, _, _ => none

/-- Source-facing displayed right-hand side in Theorem 1, with denominator,
square-root, and non-integer-power boundaries exposed by `Option`. -/
def theorem1RHSSourceValue
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : Option ℝ :=
  match theorem1MSourceValue S T L σ fStar,
      sourceNonnegativeRpowValue S.w ((1 : ℝ) / 6),
      sourceSqrtValue (T : ℝ),
      sourcePositiveRpowValue (T : ℝ) ((1 : ℝ) / 3),
      sourceNonnegativeRpowValue σ ((1 : ℝ) / 3) with
  | some M, some wSixth, some sqrtT, some TThird, some sigmaThird =>
      match sourceSqrtValue (2 * M),
          sourceNonnegativeRpowValue M ((3 : ℝ) / 4) with
      | some sqrt2M, some MThreeFourths =>
          match sourceQuotientValue (wSixth * sqrt2M + 2 * MThreeFourths) sqrtT,
              sourceQuotientValue (2 * sigmaThird) TThird with
          | some deterministicTerm, some stochasticTerm =>
              some (deterministicTerm + stochasticTerm)
          | _, _ => none
      | _, _ => none
  | _, _, _, _, _ => none

/-- The partial source quotient agrees with the quotient specification whenever
it returns a value. -/
theorem sourceQuotientValue_spec
    {numerator denominator value : ℝ}
    (hvalue : sourceQuotientValue numerator denominator = some value) :
    sourceQuotientSpec numerator denominator value := by
  by_cases hden : denominator = 0
  · unfold sourceQuotientValue at hvalue
    simp [hden] at hvalue
  · unfold sourceQuotientValue at hvalue
    unfold sourceQuotientSpec
    simp [hden] at hvalue
    constructor
    · exact hden
    · rw [← hvalue]
      exact div_mul_cancel₀ numerator hden

/-- A nonzero displayed denominator selects the ordinary quotient branch of the
partial source-value rendering. -/
theorem sourceQuotientValue_eq_some_of_den_ne
    {numerator denominator : ℝ} (hden : denominator ≠ 0) :
    sourceQuotientValue numerator denominator = some (numerator / denominator) := by
  simp [sourceQuotientValue, hden]

/-- Source expression bridge for the Theorem 1 `k` selector. -/
theorem theorem1KSourceValue_eq_some_of_boundary
    {b G L : ℝ} (hG : 0 ≤ G) (hL : L ≠ 0) :
    theorem1KSourceValue b G L = some (theorem1K b G L) := by
  simp [theorem1KSourceValue, sourceNonnegativeRpowValue, sourceQuotientValue, theorem1K, hG, hL]

/-- Source expression bridge for the Theorem 1 `c` selector. -/
theorem theorem1CSourceValue_eq_some_of_b_pos
    {b L : ℝ} (hb : 0 < b) :
    theorem1CSourceValue b L = some (theorem1C b L) := by
  have hden : 7 * b ^ 3 ≠ 0 := by
    have hb3 : 0 < b ^ 3 := pow_pos hb 3
    have h7 : (0 : ℝ) < 7 := by norm_num
    exact ne_of_gt (mul_pos h7 hb3)
  simp [theorem1CSourceValue, sourceQuotientValue, theorem1C, hden]

/-- Source expression bridge for the Theorem 1 `w` selector. -/
theorem theorem1WSourceValue_eq_some_of_b_pos
    {b G : ℝ} (hb : 0 < b) :
    theorem1WSourceValue b G = some (theorem1W b G) := by
  have hden : 7 * b ^ 2 ≠ 0 := by
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    have h7 : (0 : ℝ) < 7 := by norm_num
    exact ne_of_gt (mul_pos h7 hb2)
  simp [theorem1WSourceValue, sourceQuotientValue, theorem1W, hden]

/-- Source-expression bridge for the Theorem 1 parameterized setup. -/
theorem withTheorem1ParametersSourceValue_eq_some_of_boundary
    (S : Setup Ω Sample E) {b G L : ℝ}
    (hG : 0 ≤ G) (hL : L ≠ 0) (hb : 0 < b) :
    withTheorem1ParametersSourceValue S b G L =
      some (withTheorem1Parameters S b G L) := by
  simp [withTheorem1ParametersSourceValue, withTheorem1Parameters,
    theorem1KSourceValue_eq_some_of_boundary hG hL,
    theorem1CSourceValue_eq_some_of_b_pos hb,
    theorem1WSourceValue_eq_some_of_b_pos hb]

/-- Internal scalar boundary for the Theorem 1 parameter display.

This is not a source-facing theorem contract.  The paper states only `b > 0` in
Theorem 1; in particular it does not exclude the displayed singular cases
`G = 0` or `L = 0`. -/
def theorem1ParameterScalarBoundary (b G L : ℝ) : Prop :=
  0 ≤ G ∧
    0 < L ∧
      theorem1K b G L ≠ 0 ∧
        sourceQuotientSpec (b * Real.rpow G ((2 : ℝ) / 3)) L (theorem1K b G L) ∧
          sourceQuotientSpec (G ^ 2) (7 * L * theorem1K b G L ^ 3)
            (theorem1C b L - 28 * L ^ 2) ∧
            0 ≤ theorem1W b G

theorem theorem1M_eq
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ)
    :
    theorem1M S T L σ fStar =
      (8 / S.k) * (S.objectiveValue S.x₁ - fStar) +
        Real.rpow S.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * S.k ^ 2) +
          S.k ^ 2 * S.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) := by
  rfl

/-- The sampled stochastic-gradient value at a deterministic query and time. -/
def sampledGradientAt (S : Setup Ω Sample E) (x : E) (n : ℕ) : Ω → E :=
  fun ω => S.stochasticGradient x (S.sample n ω)

/-- The sampled stochastic-gradient process along a random query process. -/
def sampledGradientProcess (S : Setup Ω Sample E) (x : ℕ → Ω → E) : ℕ → Ω → E :=
  fun n ω => S.stochasticGradient (x n ω) (S.sample n ω)

/-- The sampled-gradient process is the stochastic oracle evaluated at the
current iterate and current sample. -/
theorem sampledGradientProcess_eq
    (S : Setup Ω Sample E)
    (x : ℕ → Ω → E) (n : ℕ) :
    sampledGradientProcess S x n =
      fun ω => S.stochasticGradient (x n ω) (S.sample n ω) := by
  exact
    SOptLib.sampledOracleProcess S.stochasticGradient x S.sample
      (sampledGradientProcess S x) (by intro t; rfl) n

/-- The sampled gradient norm `G_{n+1}` at a deterministic query. -/
def sampledGradientNormAt (S : Setup Ω Sample E) (x : E) (n : ℕ) : Ω → ℝ :=
  fun ω => ‖S.stochasticGradient x (S.sample n ω)‖

/-- The positive base under a paper stepsize denominator. -/
def stepsizeBase (S : Setup Ω Sample E) (sumSq : ℝ) : ℝ :=
  S.w + sumSq

/-- Displayed one-third-power adaptive denominator formula. -/
def stepsizeDenominator (S : Setup Ω Sample E) (sumSq : ℝ) : ℝ :=
  Real.rpow (stepsizeBase S sumSq) ((1 : ℝ) / 3)

/-- Partial source value of the displayed adaptive stepsize
`k / (w + ∑ G_i²)^{1/3}`.

This is the paper-facing scalar object for Algorithm 1.  It is undefined when
the denominator base is not strictly positive, instead of using Lean's total
`Real.rpow` and division fallbacks.

Source: `book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps/1/math`
displays `η_t <- k/(w+sum G_i^2)^(1/3)` with no denominator-domain input. -/
def adaptiveStepsizeSourceValue (S : Setup Ω Sample E) (sumSq : ℝ) : Option ℝ :=
  SOptLib.checked_inverse_rpow_step_size S.k S.w sumSq ((1 : ℝ) / 3)

/-- Internal totalized adaptive stepsize
`η_t = k / (w + ∑_{i=1}^t G_i^2)^{1/3}`.

The paper-facing scalar object is `adaptiveStepsizeSourceValue`; this totalized
version is retained for arithmetic proof obligations and is bridged to the
source value only under explicit scalar-boundary theorems. -/
def adaptiveStepsize (S : Setup Ω Sample E) (sumSq : ℝ) : ℝ :=
  SOptLib.inverse_rpow_step_size S.k S.w sumSq ((1 : ℝ) / 3)

theorem adaptiveStepsize_eq
    (S : Setup Ω Sample E) (sumSq : ℝ) :
    adaptiveStepsize S sumSq =
      S.k / Real.rpow (S.w + sumSq) ((1 : ℝ) / 3) := by
  rfl

/-- Partial source value of the displayed initialization `η₀ = k / w^{1/3}`. -/
def initialStepsizeSourceValue (S : Setup Ω Sample E) : Option ℝ :=
  match sourcePositiveRpowValue S.w ((1 : ℝ) / 3) with
  | some denominator => sourceQuotientValue S.k denominator
  | none => none

/-- Internal totalized initial stepsize `η₀ = k / w^{1/3}` from Algorithm 1.

The source-facing scalar object is `initialStepsizeSourceValue`. -/
def initialStepsize (S : Setup Ω Sample E) : ℝ :=
  S.k / Real.rpow S.w ((1 : ℝ) / 3)

theorem initialStepsize_eq (S : Setup Ω Sample E) :
    initialStepsize S = S.k / Real.rpow S.w ((1 : ℝ) / 3) := by
  rfl


/-- Checked source semantics for the displayed initialization
`η₀ = k / w^{1/3}`. -/
def initialStepsizeSourceSpec (S : Setup Ω Sample E) : Prop :=
  0 < S.w ∧ sourceQuotientSpec S.k (Real.rpow S.w ((1 : ℝ) / 3)) (initialStepsize S)

/-- A positive base for a displayed adaptive stepsize gives the quotient
boundary expected by the source formula. -/
theorem adaptiveStepsize_source_spec_of_base_pos
    (S : Setup Ω Sample E) {sumSq : ℝ}
    (hbase : 0 < stepsizeBase S sumSq) :
    0 < S.w + sumSq ∧
      SOptLib.checked_quotient_spec S.k
        (Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) (adaptiveStepsize S sumSq) := by
  exact SOptLib.inverseRpowStepSizeSpec_of_base_pos
    S.k S.w sumSq ((1 : ℝ) / 3) hbase

/-- A positive `w` gives the quotient boundary for Algorithm 1's initial
stepsize. -/
theorem initialStepsize_source_spec_of_w_pos
    (S : Setup Ω Sample E) (hw : 0 < S.w) :
    initialStepsizeSourceSpec S := by
  refine ⟨hw, ?_⟩
  have hden_ne : Real.rpow S.w ((1 : ℝ) / 3) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hw ((1 : ℝ) / 3))
  unfold sourceQuotientSpec initialStepsize
  exact ⟨hden_ne, div_mul_cancel₀ S.k hden_ne⟩

/-- Source-value bridge for Algorithm 1's displayed adaptive stepsize. -/
theorem adaptiveStepsizeSourceValue_eq_some_of_base_pos
    (S : Setup Ω Sample E) {sumSq : ℝ}
    (hbase : 0 < stepsizeBase S sumSq) :
    adaptiveStepsizeSourceValue S sumSq = some (adaptiveStepsize S sumSq) := by
  simpa [adaptiveStepsizeSourceValue, adaptiveStepsize, stepsizeBase] using
    SOptLib.checked_inverse_rpow_step_size_eq_some_of_base_pos
      S.k S.w sumSq ((1 : ℝ) / 3) hbase

/-- Source-value bridge for Algorithm 1's displayed initial stepsize. -/
theorem initialStepsizeSourceValue_eq_some_of_w_pos
    (S : Setup Ω Sample E) (hw : 0 < S.w) :
    initialStepsizeSourceValue S = some (initialStepsize S) := by
  have hden_ne : Real.rpow S.w ((1 : ℝ) / 3) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hw ((1 : ℝ) / 3))
  unfold initialStepsizeSourceValue sourcePositiveRpowValue
  simp only [if_pos hw]
  change sourceQuotientValue S.k (Real.rpow S.w ((1 : ℝ) / 3)) =
    some (initialStepsize S)
  unfold sourceQuotientValue initialStepsize
  simp only [SOptLib.checkedQuotientValue_def, if_neg hden_ne]

/-- Momentum coefficient generated after a step, `a_{t+1} = c η_t^2`. -/
def momentumWeight (S : Setup Ω Sample E) (η : ℝ) : ℝ :=
  SOptLib.quadraticMomentumWeight S.c η

/-- Canonical STORM state after paper time `n+1`: iterate `x`, direction `d`,
and cumulative sampled-gradient square sum `∑_{i=1}^{n+1} G_i^2`. -/
abbrev State (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  SOptLib.RecursiveMomentumState E ℝ

/-- Measurable structure on the canonical STORM state record, generated by the
three algorithmic coordinates. -/
instance stateMeasurableSpace [MeasurableSpace E] :
    MeasurableSpace (State E) :=
  MeasurableSpace.comap (fun s : State E => s.x) inferInstance ⊔
    MeasurableSpace.comap (fun s : State E => s.direction) inferInstance ⊔
      MeasurableSpace.comap (fun s : State E => s.gradNormSqSum) inferInstance

private theorem measurable_state_x [MeasurableSpace E] :
    Measurable (fun s : State E => s.x) := by
  exact Measurable.of_comap_le (le_sup_left.trans le_sup_left)

private theorem measurable_state_direction [MeasurableSpace E] :
    Measurable (fun s : State E => s.direction) := by
  exact Measurable.of_comap_le (le_sup_right.trans le_sup_left)

private theorem measurable_state_gradNormSqSum [MeasurableSpace E] :
    Measurable (fun s : State E => s.gradNormSqSum) := by
  exact Measurable.of_comap_le le_sup_right

/-- Algorithm 1 initialization:
`G₁ = ‖∇f(x₁, ξ₁)‖` and `d₁ = ∇f(x₁, ξ₁)`. -/
def initialState (S : Setup Ω Sample E) : Ω → State E :=
  SOptLib.recursiveMomentumInitialState S.x₁ S.stochasticGradient (S.sample 0)

/-- Sample-driven STORM transition from paper time `t = n+1` to `t+1 = n+2`.

It computes `η_t`, updates `x_{t+1}`, samples `ξ_{t+1}`, records
`G_{t+1}`, sets `a_{t+1} = cη_t^2`, and applies the recursive momentum
direction update. -/
def stateStepFromSample
    (S : Setup Ω Sample E) (_n : ℕ) (state : State E) (ξNext : Sample) : State E :=
  SOptLib.recursive_momentum_step_from_sample S.stochasticGradient
    (adaptiveStepsize S) (momentumWeight S) state ξNext

/-- One STORM transition along a concrete sample path. -/
def stateStep
    (S : Setup Ω Sample E) (n : ℕ) (state : State E) (ω : Ω) : State E :=
  stateStepFromSample S n state (S.sample (n + 1) ω)

/-- The pathwise transition factors through the fresh sample coordinate. -/
theorem stateStep_eq_stateStepFromSample
    (S : Setup Ω Sample E) (n : ℕ) (state : State E) (ω : Ω) :
    stateStep S n state ω =
      stateStepFromSample S n state (S.sample (n + 1) ω) := by
  rfl

/-- Source-facing one-step STORM transition generated by Algorithm 1.

It is undefined exactly when the displayed adaptive stepsize quotient is
undefined at the current cumulative gradient-norm square sum.

Source: `book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps`,
steps `adaptive_stepsize`, `iterate_update`, `momentum_weight`,
`next_sample_and_gradient_norm`, and `recursive_momentum_direction`. -/
def sourceStateStep
    (S : Setup Ω Sample E) (n : ℕ) (state : State E) (ω : Ω) : Option (State E) :=
  match adaptiveStepsizeSourceValue S state.gradNormSqSum with
  | none => none
  | some η =>
      let xNext := state.x - η • state.direction
      let ξNext := S.sample (n + 1) ω
      let gNext := S.stochasticGradient xNext ξNext
      let correction := S.stochasticGradient state.x ξNext
      let aNext := momentumWeight S η
      some
        { x := xNext
          direction := gNext + (1 - aNext) • (state.direction - correction)
          gradNormSqSum := state.gradNormSqSum + ‖gNext‖ ^ 2 }

/-- Internal totalized sample-path STORM state process.

The paper-facing run is `sourceStateProcess`; this totalized process is kept as
the arithmetic realization used by existing proof obligations. -/
def stateProcess (S : Setup Ω Sample E) : ℕ → Ω → State E
  := SOptLib.recursive_process_from_random_initial (initialState S) (stateStep S)

/-- Source-facing sample-path STORM state process generated by Algorithm 1.

Source: `book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec`, which
initializes `G₁,d₁,η₀` and then runs the displayed loop from `t = 1` to `T`. -/
def sourceStateProcess (S : Setup Ω Sample E) : ℕ → Ω → Option (State E)
  | 0 => fun ω => some (initialState S ω)
  | n + 1 => fun ω =>
      match sourceStateProcess S n ω with
      | some state => sourceStateStep S n state ω
      | none => none

/-- Generated STORM iterates `x_{n+1}` for the internal totalized run. -/
def iterate (S : Setup Ω Sample E) (n : ℕ) : Ω → E :=
  fun ω => (stateProcess S n ω).x

/-- Generated STORM iterates `x_{n+1}` for the source-facing partial run. -/
def sourceIterate (S : Setup Ω Sample E) (n : ℕ) : Ω → Option E :=
  fun ω =>
    match sourceStateProcess S n ω with
    | some state => some state.x
    | none => none

/-- Generated STORM directions `d_{n+1}` for the internal totalized run. -/
def direction (S : Setup Ω Sample E) (n : ℕ) : Ω → E :=
  fun ω => (stateProcess S n ω).direction

/-- Generated STORM directions `d_{n+1}` for the source-facing partial run. -/
def sourceDirection (S : Setup Ω Sample E) (n : ℕ) : Ω → Option E :=
  fun ω =>
    match sourceStateProcess S n ω with
    | some state => some state.direction
    | none => none

/-- Generated cumulative square sum `∑_{i=1}^{n+1} G_i^2` for the internal
totalized run. -/
def cumulativeGradientNormSq
    (S : Setup Ω Sample E) (n : ℕ) : Ω → ℝ :=
  fun ω => (stateProcess S n ω).gradNormSqSum

/-- Generated cumulative square sum `∑_{i=1}^{n+1} G_i^2` for the
source-facing partial run. -/
def sourceCumulativeGradientNormSq
    (S : Setup Ω Sample E) (n : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceStateProcess S n ω with
    | some state => some state.gradNormSqSum
    | none => none

/-- The adaptive stepsize `η_{n+1}` generated from the current
cumulative norm sum. -/
def stepsize (S : Setup Ω Sample E) (n : ℕ) : Ω → ℝ :=
  fun ω => adaptiveStepsize S (cumulativeGradientNormSq S n ω)

/-- The momentum coefficient used to pass from `n` to `n+1`, corresponding to
the paper's `a_{t+1}`. -/
def nextMomentumWeight (S : Setup Ω Sample E) (n : ℕ) : Ω → ℝ :=
  fun ω => momentumWeight S (stepsize S n ω)

/-- The paper's error variable `ε_t := d_t - ∇F(x_t)`, zero-based internally. -/
def error (S : Setup Ω Sample E) (n : ℕ) : Ω → E :=
  fun ω => direction S n ω - S.objectiveGradient (iterate S n ω)

/-- Source-facing adaptive stepsize generated by the partial Algorithm 1 run. -/
def sourceStepsize (S : Setup Ω Sample E) (n : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceCumulativeGradientNormSq S n ω with
    | some sumSq => adaptiveStepsizeSourceValue S sumSq
    | none => none

/-- Source-facing momentum coefficient generated by the partial Algorithm 1 run. -/
def sourceNextMomentumWeight (S : Setup Ω Sample E) (n : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceStepsize S n ω with
    | some η => some (momentumWeight S η)
    | none => none

/-- Source-facing error variable `ε_t := d_t - ∇F(x_t)` from the partial run. -/
def sourceError (S : Setup Ω Sample E) (n : ℕ) : Ω → Option E :=
  fun ω =>
    match sourceDirection S n ω, sourceIterate S n ω with
    | some d, some x => some (d - S.objectiveGradient x)
    | _, _ => none

theorem iterate_zero (S : Setup Ω Sample E) (ω : Ω) :
    iterate S 0 ω = S.x₁ := by
  rfl

theorem direction_zero
    (S : Setup Ω Sample E) (ω : Ω) :
    direction S 0 ω = S.stochasticGradient S.x₁ (S.sample 0 ω) := by
  rfl

theorem cumulativeGradientNormSq_zero
    (S : Setup Ω Sample E) (ω : Ω) :
    cumulativeGradientNormSq S 0 ω =
      ‖S.stochasticGradient S.x₁ (S.sample 0 ω)‖ ^ 2 := by
  rfl

/-- Defining equation for the generated iterate update
`x_{t+1} = x_t - η_t d_t`. -/
theorem iterate_succ
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) :
    iterate S (n + 1) ω =
      iterate S n ω - stepsize S n ω • direction S n ω := by
  exact SOptLib.recursive_momentum_iterate_succ S.stochasticGradient S.sample
    (adaptiveStepsize S) (momentumWeight S) (initialState S) n ω

/-- Defining equation for the generated recursive momentum direction. -/
theorem direction_succ
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) :
    direction S (n + 1) ω =
      S.stochasticGradient (iterate S (n + 1) ω) (S.sample (n + 1) ω) +
        (1 - nextMomentumWeight S n ω) •
          (direction S n ω -
            S.stochasticGradient (iterate S n ω) (S.sample (n + 1) ω)) := by
  rfl

/-- Defining equation for the cumulative sampled-gradient norm square sum. -/
theorem cumulativeGradientNormSq_succ
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) :
    cumulativeGradientNormSq S (n + 1) ω =
      cumulativeGradientNormSq S n ω +
        ‖S.stochasticGradient (iterate S (n + 1) ω) (S.sample (n + 1) ω)‖ ^ 2 := by
  rfl

theorem sourceStateProcess_zero (S : Setup Ω Sample E) (ω : Ω) :
    sourceStateProcess S 0 ω = some (initialState S ω) := by
  rfl

/-- Defining equation for the source-facing partial generated iterate. -/
theorem sourceIterate_eq
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) :
    sourceIterate S n ω =
      match sourceStateProcess S n ω with
      | some state => some state.x
      | none => none := by
  rfl

/-- Defining equation for a successful source-facing one-step transition. -/
theorem sourceStateStep_eq_some_of_stepsize
    (S : Setup Ω Sample E) (n : ℕ) (state : State E) (ω : Ω) {η : ℝ}
    (hη : adaptiveStepsizeSourceValue S state.gradNormSqSum = some η) :
    sourceStateStep S n state ω =
      some
        { x := state.x - η • state.direction
          direction :=
            S.stochasticGradient (state.x - η • state.direction) (S.sample (n + 1) ω) +
              (1 - momentumWeight S η) •
                (state.direction -
                  S.stochasticGradient state.x (S.sample (n + 1) ω))
          gradNormSqSum :=
            state.gradNormSqSum +
              ‖S.stochasticGradient (state.x - η • state.direction)
                (S.sample (n + 1) ω)‖ ^ 2 } := by
  simp [sourceStateStep, hη]

/-- Defining equation for the generated adaptive stepsize. -/
theorem stepsize_eq
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) :
    stepsize S n ω =
      S.k / Real.rpow (S.w + cumulativeGradientNormSq S n ω) ((1 : ℝ) / 3) := by
  rfl

/-- Internal scalar boundary for the generated Algorithm 1 stepsizes along the
canonical run.

This records the Lean-side well-definedness needed to read the displayed
quotients literally.  It is intentionally not part of the paper-facing theorem,
because Algorithm 1 does not list `w > 0` as an input condition. -/
def generatedStepsizeScalarBoundary (S : Setup Ω Sample E) : Prop :=
  initialStepsizeSourceSpec S ∧
    ∀ n ω, 0 < S.w + (cumulativeGradientNormSq S n ω) ∧
      SOptLib.checked_quotient_spec S.k
        (Real.rpow (S.w + (cumulativeGradientNormSq S n ω)) ((1 : ℝ) / 3)) (stepsize S n ω)

/-- Source boundary for paper expressions that use both generated stepsizes and
their displayed reciprocals.

Algorithm 1's generated stepsizes are source-defined by
`generatedStepsizeScalarBoundary`; Lemma 2 also uses the positivity of
`η_t^3` and `η_t^{-1}(1-a_t)^2` when dropping centered-square terms.  Since
the displayed quotient defining `η_t` has a positive denominator under the
scalar boundary, this is recorded by the paper's positive stepsize numerator
condition `0 < S.k`. -/
def generatedStepsizeQuotientBoundary (S : Setup Ω Sample E) : Prop :=
  generatedStepsizeScalarBoundary S ∧ 0 < S.k

/-- The source-facing run agrees with the internal totalized run when all
generated displayed stepsizes have source semantics. -/
theorem sourceStateProcess_eq_some_stateProcess_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) :
    ∀ n ω, sourceStateProcess S n ω = some (stateProcess S n ω) := by
  refine SOptLib.partialRecursiveProcess_eq_some_of_step_eq_some
    (partialProcess := sourceStateProcess S) (total := stateProcess S)
    (partialStep := sourceStateStep S) (totalStep := stateStep S)
    (initial := initialState S) ?_ ?_ ?_ ?_ ?_
  · intro ω
    rfl
  · intro ω
    rfl
  · intro n ω
    cases h : sourceStateProcess S n ω <;> simp [sourceStateProcess, h]
  · intro n ω
    rfl
  · intro n ω
    have hη : adaptiveStepsizeSourceValue S ((stateProcess S n ω).gradNormSqSum) =
        some (adaptiveStepsize S ((stateProcess S n ω).gradNormSqSum)) := by
      simpa [cumulativeGradientNormSq] using
        adaptiveStepsizeSourceValue_eq_some_of_base_pos S ((hboundary.2 n ω).1)
    simpa [stateStep, stateStepFromSample] using
      sourceStateStep_eq_some_of_stepsize S n (stateProcess S n ω) ω hη

/-- The source-facing iterate agrees with the internal totalized iterate under
the generated scalar boundary. -/
theorem sourceIterate_eq_some_iterate_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) (n : ℕ) (ω : Ω) :
    sourceIterate S n ω = some (iterate S n ω) := by
  have hstate := sourceStateProcess_eq_some_stateProcess_of_generated_boundary S hboundary n ω
  simpa [sourceIterate, iterate, hstate]

/-- The source-facing direction agrees with the internal totalized direction
under the generated scalar boundary. -/
theorem sourceDirection_eq_some_direction_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) (n : ℕ) (ω : Ω) :
    sourceDirection S n ω = some (direction S n ω) := by
  have hstate := sourceStateProcess_eq_some_stateProcess_of_generated_boundary S hboundary n ω
  simpa [sourceDirection, direction, hstate]

/-- The source-facing cumulative gradient-norm square sum agrees with the
internal totalized sum under the generated scalar boundary. -/
theorem sourceCumulativeGradientNormSq_eq_some_cumulativeGradientNormSq_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) (n : ℕ) (ω : Ω) :
    sourceCumulativeGradientNormSq S n ω = some (cumulativeGradientNormSq S n ω) := by
  have hstate := sourceStateProcess_eq_some_stateProcess_of_generated_boundary S hboundary n ω
  simpa [sourceCumulativeGradientNormSq, cumulativeGradientNormSq, hstate]

/-- The generated source stepsize agrees with the internal totalized stepsize
under the generated scalar boundary. -/
theorem sourceStepsize_eq_some_stepsize_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) (n : ℕ) (ω : Ω) :
    sourceStepsize S n ω = some (stepsize S n ω) := by
  have hsum :=
    sourceCumulativeGradientNormSq_eq_some_cumulativeGradientNormSq_of_generated_boundary S hboundary n ω
  have hη : adaptiveStepsizeSourceValue S (cumulativeGradientNormSq S n ω) =
      some (adaptiveStepsize S (cumulativeGradientNormSq S n ω)) := by
    exact adaptiveStepsizeSourceValue_eq_some_of_base_pos S ((hboundary.2 n ω).1)
  simpa [sourceStepsize, stepsize, hsum] using hη

/-- The generated source momentum weight agrees with the internal totalized
momentum weight under the generated scalar boundary. -/
theorem sourceNextMomentumWeight_eq_some_nextMomentumWeight_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) (n : ℕ) (ω : Ω) :
    sourceNextMomentumWeight S n ω = some (nextMomentumWeight S n ω) := by
  have hη := sourceStepsize_eq_some_stepsize_of_generated_boundary S hboundary n ω
  simpa [sourceNextMomentumWeight, nextMomentumWeight, hη]

/-- The source-facing error variable agrees with the internal totalized error
under the generated scalar boundary. -/
theorem sourceError_eq_some_error_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) (n : ℕ) (ω : Ω) :
    sourceError S n ω = some (error S n ω) := by
  have hd := sourceDirection_eq_some_direction_of_generated_boundary S hboundary n ω
  have hx := sourceIterate_eq_some_iterate_of_generated_boundary S hboundary n ω
  simpa [sourceError, error, hd, hx]

/-- Positive `k` makes each source-defined generated stepsize positive, because
the displayed adaptive stepsize quotient has a positive denominator. -/
theorem stepsize_pos_of_generated_quotient_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) (n : ℕ) (ω : Ω) :
    0 < stepsize S n ω := by
  have hbase : 0 < stepsizeBase S (cumulativeGradientNormSq S n ω) :=
    (hboundary.1.2 n ω).1
  have hden_pos :
      0 < stepsizeDenominator S (cumulativeGradientNormSq S n ω) :=
    Real.rpow_pos_of_pos hbase ((1 : ℝ) / 3)
  simpa [stepsize_eq, stepsizeDenominator, stepsizeBase] using
    div_pos hboundary.2 hden_pos

/-- Nonzero generated stepsizes follow from the positive generated quotient
boundary. -/
theorem stepsize_ne_zero_of_generated_quotient_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) (n : ℕ) (ω : Ω) :
    stepsize S n ω ≠ 0 :=
  ne_of_gt (stepsize_pos_of_generated_quotient_boundary S hboundary n ω)

/-- The reciprocal of a generated stepsize is source-defined under the quotient
boundary used by Lemmas 2 and 3. -/
theorem sourceStepsizeInverseValue_eq_some_of_generated_quotient_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) (n : ℕ) (ω : Ω) :
    sourceQuotientValue 1 (stepsize S n ω) =
      some (1 / stepsize S n ω) := by
  exact sourceQuotientValue_eq_some_of_den_ne
    (stepsize_ne_zero_of_generated_quotient_boundary S hboundary n ω)

/-- Scalar boundary for the displayed definition of `M` in Theorem 1. -/
def theorem1MScalarBoundary (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : Prop :=
  S.k ≠ 0 ∧
    4 * L ^ 2 * S.k ^ 2 ≠ 0 ∧
      2 * L ^ 2 ≠ 0 ∧
        0 ≤ S.w ∧
          0 ≤ theorem1M S T L σ fStar

/-- Scalar boundary for the displayed Theorem 1 rate expression. -/
def theorem1RHSScalarBoundary (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : Prop :=
  0 ≤ 2 * theorem1M S T L σ fStar ∧
    Real.sqrt (T : ℝ) ≠ 0 ∧
      Real.rpow (T : ℝ) ((1 : ℝ) / 3) ≠ 0 ∧
        0 ≤ σ

/-- Source-expression bridge for the displayed Theorem 1 scalar `M`. -/
theorem theorem1MSourceValue_eq_some_of_boundary
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ)
    (hboundary : theorem1MScalarBoundary S T L σ fStar) :
    theorem1MSourceValue S T L σ fStar = some (theorem1M S T L σ fStar) := by
  rcases hboundary with ⟨hk, h4, h2, hw, _⟩
  have hq8 : sourceQuotientValue 8 S.k = some (8 / S.k) := by
    simp [sourceQuotientValue, hk]
  have hw13 : sourceNonnegativeRpowValue S.w ((3 : ℝ)⁻¹) =
      some (S.w ^ ((3 : ℝ)⁻¹)) := by
    simp [sourceNonnegativeRpowValue, hw]
  have hnoise : sourceQuotientValue (S.w ^ ((3 : ℝ)⁻¹) * σ ^ 2)
        (4 * L ^ 2 * S.k ^ 2) =
      some ((S.w ^ ((3 : ℝ)⁻¹) * σ ^ 2) / (4 * L ^ 2 * S.k ^ 2)) := by
    simp [sourceQuotientValue, h4]
  have hlast : sourceQuotientValue (S.k ^ 2 * S.c ^ 2) (2 * L ^ 2) =
      some ((S.k ^ 2 * S.c ^ 2) / (2 * L ^ 2)) := by
    simp [sourceQuotientValue, h2]
  simp [theorem1MSourceValue, theorem1M, theorem1MFormula, hq8, hw13, hnoise, hlast]

/-- Source-expression bridge for the displayed Theorem 1 right-hand side. -/
theorem theorem1RHSSourceValue_eq_some_of_boundary
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ)
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hRHS : theorem1RHSScalarBoundary S T L σ fStar) :
    theorem1RHSSourceValue S T L σ fStar = some (theorem1RHS S T L σ fStar) := by
  have hMsrc := theorem1MSourceValue_eq_some_of_boundary S T L σ fStar hM
  rcases hM with ⟨_, _, _, hw, hMnonneg⟩
  rcases hRHS with ⟨h2M, hsqrtT_ne, hTthird_ne, hsigma⟩
  have hTnonneg : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have hTpos : 0 < (T : ℝ) := by
    by_contra hnot
    have hle : (T : ℝ) ≤ 0 := le_of_not_gt hnot
    have hzero : (T : ℝ) = 0 := le_antisymm hle hTnonneg
    apply hTthird_ne
    simp [hzero]
  have hTthird_den_ne : ((T : ℝ) ^ ((3 : ℝ)⁻¹)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hTpos ((3 : ℝ)⁻¹))
  have hw16 : sourceNonnegativeRpowValue S.w ((6 : ℝ)⁻¹) =
      some (S.w ^ ((6 : ℝ)⁻¹)) := by
    simp [sourceNonnegativeRpowValue, hw]
  have hsqrtT : sourceSqrtValue (T : ℝ) = some (Real.sqrt (T : ℝ)) := by
    simp [sourceSqrtValue, hTnonneg]
  have hTthird : sourcePositiveRpowValue (T : ℝ) ((3 : ℝ)⁻¹) =
      some ((T : ℝ) ^ ((3 : ℝ)⁻¹)) := by
    simp [sourcePositiveRpowValue, hTpos]
  have hsigmaThird : sourceNonnegativeRpowValue σ ((3 : ℝ)⁻¹) =
      some (σ ^ ((3 : ℝ)⁻¹)) := by
    simp [sourceNonnegativeRpowValue, hsigma]
  have hsqrt2M : sourceSqrtValue (2 * theorem1M S T L σ fStar) =
      some (Real.sqrt (2 * theorem1M S T L σ fStar)) := by
    simp [sourceSqrtValue, h2M]
  have hM34 : sourceNonnegativeRpowValue (theorem1M S T L σ fStar) ((3 : ℝ) / 4) =
      some ((theorem1M S T L σ fStar) ^ ((3 : ℝ) / 4)) := by
    simp [sourceNonnegativeRpowValue, hMnonneg]
  have hdet : sourceQuotientValue
        (S.w ^ ((6 : ℝ)⁻¹) * (Real.sqrt 2 * Real.sqrt (theorem1M S T L σ fStar)) +
          2 * (theorem1M S T L σ fStar) ^ ((3 : ℝ) / 4))
        (Real.sqrt (T : ℝ)) =
      some ((S.w ^ ((6 : ℝ)⁻¹) *
          (Real.sqrt 2 * Real.sqrt (theorem1M S T L σ fStar)) +
            2 * (theorem1M S T L σ fStar) ^ ((3 : ℝ) / 4)) /
          Real.sqrt (T : ℝ)) := by
    simp [sourceQuotientValue, hsqrtT_ne]
  have hstoch : sourceQuotientValue (2 * σ ^ ((3 : ℝ)⁻¹)) ((T : ℝ) ^ ((3 : ℝ)⁻¹)) =
      some ((2 * σ ^ ((3 : ℝ)⁻¹)) / ((T : ℝ) ^ ((3 : ℝ)⁻¹))) := by
    simp [sourceQuotientValue, hTthird_den_ne]
  simp [theorem1RHSSourceValue, theorem1RHS, hMsrc, hw16, hsqrtT, hTthird, hsigmaThird,
    hsqrt2M, hM34, hdet, hstoch]

/-- Internal scalar/source boundary package for the displayed Theorem 1 and
Algorithm 1 formulas.

This package documents quotient and non-integer-power side conditions, but it
is not asserted as a consequence of the source assumptions: the paper's
Theorem 1 does not include the extra exclusions that would make this boundary
valid in all degenerate scalar cases. -/
def theorem1ScalarBoundary
    (S : Setup Ω Sample E) (T : ℕ) (b L G σ fStar : ℝ) : Prop :=
  let ST := withTheorem1Parameters S b G L
  theorem1ParameterScalarBoundary b G L ∧
    generatedStepsizeScalarBoundary ST ∧
      theorem1MScalarBoundary ST T L σ fStar ∧
        theorem1RHSScalarBoundary ST T L σ fStar

/-- The Theorem 1 scalar parameter boundary supplies the positive generated
stepsize numerator `k` for the parameterized setup. -/
theorem theorem1_parameterized_k_pos
    (S : Setup Ω Sample E) (T : ℕ) {b L G σ fStar : ℝ}
    (hb : 0 < b)
    (hscalar : theorem1ScalarBoundary S T b L G σ fStar) :
    0 < (withTheorem1Parameters S b G L).k := by
  have hG_nonneg : 0 ≤ G := hscalar.1.1
  have hL_pos : 0 < L := hscalar.1.2.1
  have hk_ne : theorem1K b G L ≠ 0 := hscalar.1.2.2.1
  have hk_nonneg : 0 ≤ theorem1K b G L := by
    unfold theorem1K
    exact div_nonneg
      (mul_nonneg (le_of_lt hb) (Real.rpow_nonneg hG_nonneg _))
      (le_of_lt hL_pos)
  have hk_pos : 0 < theorem1K b G L := by
    by_cases hzero : theorem1K b G L = 0
    · exact False.elim (hk_ne hzero)
    · exact lt_of_le_of_ne hk_nonneg (Ne.symm hzero)
  simpa [withTheorem1Parameters] using hk_pos

/-- Early scalar access to nonnegativity of the generated sampled-gradient
square sum.  A later Lemma 3 section has the same mathematical fact with a
local name; this version is placed before Theorem 1's scalar route. -/
private theorem theorem1_cumulativeGradientNormSq_nonneg
    (S : Setup Ω Sample E) (t : ℕ) (ω : Ω) :
    0 ≤ cumulativeGradientNormSq S t ω := by
  induction t with
  | zero =>
      simpa [cumulativeGradientNormSq, stateProcess, initialState] using
        sq_nonneg ‖S.stochasticGradient S.x₁ (S.sample 0 ω)‖
  | succ t ih =>
      rw [cumulativeGradientNormSq_succ]
      exact add_nonneg ih (sq_nonneg _)

/-- Transparent positivity of the Theorem 1 parameterized stepsize numerator. -/
private theorem theorem1_parameterized_k_pos_of_positive
    (S : Setup Ω Sample E) {b L G : ℝ}
    (hb : 0 < b) (hGpos : 0 < G) (hLpos : 0 < L) :
    0 < (withTheorem1Parameters S b G L).k := by
  have hG23_pos : 0 < Real.rpow G ((2 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hGpos ((2 : ℝ) / 3)
  have hnum_pos : 0 < b * Real.rpow G ((2 : ℝ) / 3) :=
    mul_pos hb hG23_pos
  simpa [withTheorem1Parameters, theorem1K] using
    div_pos hnum_pos hLpos

/-- The displayed Theorem 1 `w` is nonnegative under the source-derived
nonnegativity of `G`. -/
private theorem theorem1W_nonneg_of_G_nonneg
    {b G : ℝ} (hG : 0 ≤ G) :
    0 ≤ theorem1W b G := by
  let q : ℝ := ((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64
  have hmax_nonneg :
      0 ≤ max ((4 * b) ^ 3) (max 2 q) := by
    have htwo_le : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    exact le_trans htwo_le
      (le_trans (le_max_left (2 : ℝ) q)
        (le_max_right ((4 * b) ^ 3) (max 2 q)))
  exact mul_nonneg (sq_nonneg G) (by simpa [theorem1W, q] using hmax_nonneg)

/-- The corrected positive-`G` boundary makes the Theorem 1 `w` selector
strictly positive, so the generated source stepsizes are defined. -/
private theorem theorem1W_pos_of_G_pos
    {b G : ℝ} (hGpos : 0 < G) :
    0 < theorem1W b G := by
  let q : ℝ := ((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64
  have hmax_pos :
      0 < max ((4 * b) ^ 3) (max 2 q) := by
    have htwo_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le htwo_pos
      (le_trans (le_max_left (2 : ℝ) q)
        (le_max_right ((4 * b) ^ 3) (max 2 q)))
  exact mul_pos (sq_pos_of_pos hGpos) (by simpa [theorem1W, q] using hmax_pos)

/-- Transparent derivation of the displayed Theorem 1 parameter source
boundary from the minimal corrected scalar assumptions. -/
private theorem theorem1_parameter_scalar_boundary_of_positive
    {b L G : ℝ} (hb : 0 < b) (hGpos : 0 < G) (hLpos : 0 < L) :
    theorem1ParameterScalarBoundary b G L := by
  have hG_nonneg : 0 ≤ G := le_of_lt hGpos
  have hL_ne : L ≠ 0 := ne_of_gt hLpos
  have hk_pos : 0 < theorem1K b G L := by
    have hG23_pos : 0 < Real.rpow G ((2 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hGpos ((2 : ℝ) / 3)
    have hnum_pos : 0 < b * Real.rpow G ((2 : ℝ) / 3) :=
      mul_pos hb hG23_pos
    simpa [theorem1K] using div_pos hnum_pos hLpos
  have hk_ne : theorem1K b G L ≠ 0 := ne_of_gt hk_pos
  have hk_source :
      sourceQuotientSpec (b * Real.rpow G ((2 : ℝ) / 3)) L
        (theorem1K b G L) := by
    refine ⟨hL_ne, ?_⟩
    simp [theorem1K, div_mul_cancel₀ _ hL_ne]
  have hc_source :
      sourceQuotientSpec (G ^ 2) (7 * L * theorem1K b G L ^ 3)
        (theorem1C b L - 28 * L ^ 2) := by
    have hb_ne : b ≠ 0 := ne_of_gt hb
    have hG23_pos : 0 < Real.rpow G ((2 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hGpos ((2 : ℝ) / 3)
    have hden_ne : 7 * L * theorem1K b G L ^ 3 ≠ 0 := by
      have hden_pos : 0 < 7 * L * theorem1K b G L ^ 3 := by
        positivity
      exact ne_of_gt hden_pos
    refine ⟨hden_ne, ?_⟩
    have hGpow :
        (Real.rpow G ((2 : ℝ) / 3)) ^ 3 = G ^ 2 := by
      exact real_rpow_two_thirds_pow_three hG_nonneg
    unfold theorem1C theorem1K
    field_simp [hb_ne, hL_ne]
    rw [hGpow]
    ring
  exact
    ⟨hG_nonneg, hLpos, hk_ne, hk_source, hc_source,
      theorem1W_nonneg_of_G_nonneg hG_nonneg⟩

/-- Transparent generated-step source boundary for the Theorem 1 parameterized
Algorithm 1 run. -/
private theorem theorem1_generated_stepsize_scalar_boundary_of_positive
    (S : Setup Ω Sample E) {b L G : ℝ}
    (_hb : 0 < b) (hGpos : 0 < G) (_hLpos : 0 < L) :
    generatedStepsizeScalarBoundary (withTheorem1Parameters S b G L) := by
  let ST := withTheorem1Parameters S b G L
  have hw_pos : 0 < ST.w := by
    simpa [ST, withTheorem1Parameters] using theorem1W_pos_of_G_pos (b := b) hGpos
  refine ⟨initialStepsize_source_spec_of_w_pos ST hw_pos, ?_⟩
  intro n ω
  have hsum_nonneg : 0 ≤ cumulativeGradientNormSq ST n ω :=
    theorem1_cumulativeGradientNormSq_nonneg ST n ω
  have hbase_pos :
      0 < stepsizeBase ST (cumulativeGradientNormSq ST n ω) := by
    dsimp [stepsizeBase]
    linarith
  simpa [ST] using adaptiveStepsize_source_spec_of_base_pos ST hbase_pos

/-- Reindex a zero-based finite horizon as the paper's one-based window
`1, ..., T`. -/
private theorem fin_sum_successor_eq_sum_Icc_one
    {M : Type*} [AddCommMonoid M] (T : ℕ) (F : ℕ → M) :
    Finset.sum Finset.univ (fun i : Fin T => F (i.val + 1)) =
      (Finset.Icc 1 T).sum F := by
  rw [Finset.sum_fin_eq_sum_range, sum_Icc_one_eq_sum_range_succ]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxlt : x < T := Finset.mem_range.mp hx
  simp [hxlt]

/-- Secant bound for the real cube-root branch used in Theorem 1.

For positive `a ≤ b`, factor `b - a` as the difference of cubes of the
one-third powers.  This gives the same `1 / (3 a^(2/3))` denominator as the
paper's concavity step, but uses only `Real.rpow` identities and ordered-ring
algebra. -/
private theorem real_rpow_one_third_sub_le_div_three_rpow_two_thirds
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ ((1 : ℝ) / 3) - a ^ ((1 : ℝ) / 3) ≤
      (b - a) / (3 * a ^ ((2 : ℝ) / 3)) := by
  exact _root_.real_rpow_one_third_sub_le_div_three_rpow_two_thirds ha hab

/-- Cubing the generated one-third-power stepsize recovers the Algorithm 1
denominator. -/
private theorem theorem1_stepsize_cube_eq
    (S : Setup Ω Sample E)
    (hgenerated : generatedStepsizeQuotientBoundary S) (t : ℕ) (ω : Ω) :
    stepsize S t ω ^ 3 =
      S.k ^ 3 / (S.w + cumulativeGradientNormSq S t ω) := by
  simpa [stepsize, adaptiveStepsize] using SOptLib.inverse_rpow_step_size_cube
    S.k S.w (cumulativeGradientNormSq S t ω)
      (hgenerated.1.2 t ω).1.le

/-- The generated cumulative sampled-gradient square sum contains the
one-based source window used in the proof of Theorem 1.

Internally the totalized run also carries the initialization sample at index
`0`; dropping that nonnegative term leaves the paper's one-based window
`1, ..., t`. -/
private theorem theorem1_sum_Icc_one_le_cumulativeGradientNormSq
    (S : Setup Ω Sample E) (t : ℕ) (ω : Ω) :
    (Finset.Icc 1 t).sum
        (fun i => ‖S.stochasticGradient (iterate S i ω) (S.sample i ω)‖ ^ 2) ≤
      cumulativeGradientNormSq S t ω := by
  exact
    sum_Icc_one_le_accumulator_of_nonneg_init_of_succ
      (fun n => cumulativeGradientNormSq S n ω)
      (fun i => ‖S.stochasticGradient (iterate S i ω) (S.sample i ω)‖ ^ 2) t
      (theorem1_cumulativeGradientNormSq_nonneg S 0 ω)
      (fun n => cumulativeGradientNormSq_succ S n ω)

/-- Denominator comparison for the shifted `A_t` summand in Theorem 1
equation (4).

The paper uses `w ≥ 2G²` and `G_{t+1}² ≤ G²` to replace the generated
denominator by the Lemma 4 denominator with the shifted one-based sampled
gradient window. -/
private theorem theorem1_equation4_shifted_log_denominator_le_generated
    (S : Setup Ω Sample E) {G : ℝ} (t : ℕ) (ω : Ω)
    (hw_ge_two : 2 * G ^ 2 ≤ S.w)
    (hG_next :
      ‖S.stochasticGradient (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ≤ G) :
    G ^ 2 +
        (Finset.Icc 1 (t + 1)).sum
          (fun i => ‖S.stochasticGradient (iterate S i ω) (S.sample i ω)‖ ^ 2) ≤
      S.w + cumulativeGradientNormSq S t ω := by
  exact sq_add_sum_Icc_succ_le_offset_add_accumulator
    (fun i => ‖S.stochasticGradient (iterate S i ω) (S.sample i ω)‖ ^ 2)
    (fun n => cumulativeGradientNormSq S n ω) G S.w t
    (theorem1_sum_Icc_one_le_cumulativeGradientNormSq S t ω)
    (pow_le_pow_left₀ (norm_nonneg _) hG_next 2) hw_ge_two

/-- Scalar identity behind the first max branch in Theorem 1's displayed
choice of `w`: after substituting `k = bG^(2/3)/L`, the branch
`(4Lk)^3` is the closed-form branch `G²(4b)^3`. -/
private theorem theorem1_four_L_k_cube_eq_w_first_branch
    {b L G : ℝ} (hb : 0 < b) (hL : 0 < L) (hG : 0 ≤ G) :
    (4 * L * theorem1K b G L) ^ 3 = G ^ 2 * (4 * b) ^ 3 := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hGpow :
      (Real.rpow G ((2 : ℝ) / 3)) ^ 3 = G ^ 2 := by
    have hmul := (Real.rpow_mul hG ((2 : ℝ) / 3) (3 : ℝ)).symm
    simpa [show ((2 : ℝ) / 3) * 3 = 2 by norm_num, Real.rpow_two] using hmul
  rw [theorem1K]
  field_simp [hL_ne]
  rw [hGpow]

/-- Scalar identity behind the third max branch in Theorem 1's displayed
choice of `w`: after substituting `k` and `c`, the branch `(ck/(4L))^3`
is the closed-form branch `G²(28b + 1/(7b²))³/64`. -/
private theorem theorem1_c_mul_k_div_four_L_cube_eq_w_third_branch
    {b L G : ℝ} (hb : 0 < b) (hL : 0 < L) (hG : 0 ≤ G) :
    (theorem1C b L * theorem1K b G L / (4 * L)) ^ 3 =
      G ^ 2 * (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64) := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hb2_ne : b ^ 2 ≠ 0 := pow_ne_zero 2 hb_ne
  have hb3_ne : b ^ 3 ≠ 0 := pow_ne_zero 3 hb_ne
  have hGpow :
      (Real.rpow G ((2 : ℝ) / 3)) ^ 3 = G ^ 2 := by
    have hmul := (Real.rpow_mul hG ((2 : ℝ) / 3) (3 : ℝ)).symm
    simpa [show ((2 : ℝ) / 3) * 3 = 2 by norm_num, Real.rpow_two] using hmul
  rw [theorem1C, theorem1K]
  field_simp [hb_ne, hb2_ne, hb3_ne, hL_ne]
  rw [hGpow]
  ring

/-- The generated adaptive stepsizes satisfy the Theorem 1 proof's
`η_t ≤ 1/(4L)` side condition whenever the generated denominator is
source-defined and the first `w` max branch holds. -/
private theorem theorem1_generated_stepsize_le_one_over_fourL
    (S : Setup Ω Sample E)
    (hgenerated : generatedStepsizeScalarBoundary S)
    (hk_pos : 0 < S.k) {L : ℝ} (hL_pos : 0 < L)
    (hw_ge_four : (4 * L * S.k) ^ 3 ≤ S.w) :
    ∀ t ω, stepsize S t ω ≤ (1 : ℝ) / (4 * L) := by
  intro t ω
  exact SOptLib.inverse_rpow_step_size_one_third_le_one_div_four_mul
    S.k S.w (cumulativeGradientNormSq S t ω) L (le_of_lt hk_pos) hL_pos
    (le_trans hw_ge_four
      (le_add_of_nonneg_right (theorem1_cumulativeGradientNormSq_nonneg S t ω)))

/-- The generated momentum coefficients satisfy `a_{t+1} ≤ 1` from the two
Theorem 1 max branches `(4Lk)^3 ≤ w` and `(ck/(4L))^3 ≤ w`. -/
private theorem theorem1_generated_nextMomentumWeight_le_one
    (S : Setup Ω Sample E)
    (hgenerated : generatedStepsizeScalarBoundary S)
    (hk_pos : 0 < S.k) {L : ℝ} (hL_pos : 0 < L)
    (hc_pos : 0 < S.c)
    (hw_ge_four : (4 * L * S.k) ^ 3 ≤ S.w)
    (hw_ge_ck : (S.c * S.k / (4 * L)) ^ 3 ≤ S.w) :
    ∀ t ω, nextMomentumWeight S t ω ≤ 1 := by
  intro t ω
  simpa [nextMomentumWeight, momentumWeight, stepsize, adaptiveStepsize] using
    SOptLib.quadraticMomentumWeight_inverseRpowStepSize_le_one
      S.c S.k S.w (cumulativeGradientNormSq S t ω) L hc_pos hk_pos hL_pos
      (theorem1_cumulativeGradientNormSq_nonneg S t ω) hw_ge_four hw_ge_ck

/-- Private scalar consequences used by equation (4) in the proof of
Theorem 1.

These are not Section 3 assumptions and not part of the paper-facing theorem
head.  They are the scalar consequences of the displayed Theorem 1 parameter
choice that the proof uses when turning the generated Lemma 2 recurrence into
equation (4): `w` dominates the adaptive denominators, `c` has the printed
quotient relation, and the resulting generated stepsizes/momentum coefficients
have the bounds used in the cancellation of the `B_t` terms. -/
private structure theorem1Equation4ScalarBoundary
    (S : Setup Ω Sample E) (L G : ℝ) : Prop where
  k_pos : 0 < S.k
  L_pos : 0 < L
  w_nonneg : 0 ≤ S.w
  c_source_quotient :
    sourceQuotientSpec (G ^ 2) (7 * L * S.k ^ 3) (S.c - 28 * L ^ 2)
  w_ge_two_G_sq : 2 * G ^ 2 ≤ S.w
  w_ge_four_L_k_cube : (4 * L * S.k) ^ 3 ≤ S.w
  stepsize_le_one_over_fourL :
    ∀ t ω, stepsize S t ω ≤ (1 : ℝ) / (4 * L)
  nextMomentumWeight_le_one :
    ∀ t ω, nextMomentumWeight S t ω ≤ 1

/-- The scalar boundary's source quotient for `c` recovers the printed
Theorem 1 identity `c = 28L² + G²/(7Lk³)`.

This is a proved algebraic bridge, not a new scalar assumption: it unfolds the
paper-facing quotient specification already stored in
`theorem1Equation4ScalarBoundary`. -/
private theorem theorem1_equation4_c_eq_of_scalar_boundary
    (S : Setup Ω Sample E) (L G : ℝ)
    (hboundary : theorem1Equation4ScalarBoundary S L G) :
    S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3) := by
  rcases hboundary.c_source_quotient with ⟨hden_ne, hmul⟩
  have hsub_eq : S.c - 28 * L ^ 2 = G ^ 2 / (7 * L * S.k ^ 3) := by
    rw [eq_div_iff hden_ne]
    exact hmul
  linarith

/-- The existing internal Theorem 1 scalar boundary supplies the scalar
consequences needed by equation (4) for the parameterized STORM setup.

The remaining proof obligations are exactly the source scalar side calculations
from Theorem 1 proof lines 308-388: `w ≥ (4Lk)^3`, `w ≥ 2G²`, the adaptive
stepsize upper bound, and the momentum upper bound.  They are kept here rather
than smuggled into `Section3Assumptions` or the public theorem head. -/
private theorem theorem1_equation4_scalar_boundary_of_theorem1_scalar_boundary
    (S : Setup Ω Sample E) (T : ℕ) {b L G σ fStar : ℝ}
    (hb : 0 < b)
    (hscalar : theorem1ScalarBoundary S T b L G σ fStar) :
    theorem1Equation4ScalarBoundary (withTheorem1Parameters S b G L) L G := by
  classical
  refine
    { k_pos := theorem1_parameterized_k_pos S T hb hscalar
      L_pos := hscalar.1.2.1
      w_nonneg := ?_
      c_source_quotient := ?_
      w_ge_two_G_sq := ?_
      w_ge_four_L_k_cube := ?_
      stepsize_le_one_over_fourL := ?_
      nextMomentumWeight_le_one := ?_ }
  · simpa [withTheorem1Parameters] using hscalar.1.2.2.2.2.2
  · simpa [withTheorem1Parameters] using hscalar.1.2.2.2.2.1
  ·
    -- Source proof line 343: the displayed `w` satisfies `w ≥ 2G²`.
    let q : ℝ := ((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64
    have hmax_ge_two : (2 : ℝ) ≤ max ((4 * b) ^ 3) (max 2 q) :=
      le_trans (le_max_left (2 : ℝ) q) (le_max_right ((4 * b) ^ 3) (max 2 q))
    have hmul :
        G ^ 2 * 2 ≤ G ^ 2 * max ((4 * b) ^ 3) (max 2 q) :=
      mul_le_mul_of_nonneg_left hmax_ge_two (sq_nonneg G)
    have hcomm :
        2 * G ^ 2 ≤ G ^ 2 * max ((4 * b) ^ 3) (max 2 q) := by
      nlinarith
    simpa [withTheorem1Parameters, theorem1W, q] using hcomm
  ·
    -- Source proof lines 310-311: the displayed `w` satisfies
    -- `w ≥ (4Lk)^3`.
    have hbranch :
        (4 * L * theorem1K b G L) ^ 3 = G ^ 2 * (4 * b) ^ 3 :=
      theorem1_four_L_k_cube_eq_w_first_branch hb hscalar.1.2.1 hscalar.1.1
    have hmax_ge_branch :
        (4 * b) ^ 3 ≤
          max ((4 * b) ^ 3)
            (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
      le_max_left _ _
    have hmul :
        G ^ 2 * (4 * b) ^ 3 ≤
          G ^ 2 *
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
      mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
    simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
  ·
    -- Source proof line 310: `w ≥ (4Lk)^3` gives `η_t ≤ 1/(4L)` for the
    -- generated adaptive denominator.
    have hw_ge_four :
        (4 * L * (withTheorem1Parameters S b G L).k) ^ 3 ≤
          (withTheorem1Parameters S b G L).w := by
      have hbranch :
          (4 * L * theorem1K b G L) ^ 3 = G ^ 2 * (4 * b) ^ 3 :=
        theorem1_four_L_k_cube_eq_w_first_branch hb hscalar.1.2.1 hscalar.1.1
      have hmax_ge_branch :
          (4 * b) ^ 3 ≤
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        le_max_left _ _
      have hmul :
          G ^ 2 * (4 * b) ^ 3 ≤
            G ^ 2 *
              max ((4 * b) ^ 3)
                (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
      simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
    exact
      theorem1_generated_stepsize_le_one_over_fourL
        (withTheorem1Parameters S b G L) hscalar.2.1
        (theorem1_parameterized_k_pos S T hb hscalar) hscalar.1.2.1 hw_ge_four
  ·
    -- Source proof line 311: the displayed `c` and `w` choices give
    -- `a_{t+1}=cη_t²≤1`.
    have hw_ge_four :
        (4 * L * (withTheorem1Parameters S b G L).k) ^ 3 ≤
          (withTheorem1Parameters S b G L).w := by
      have hbranch :
          (4 * L * theorem1K b G L) ^ 3 = G ^ 2 * (4 * b) ^ 3 :=
        theorem1_four_L_k_cube_eq_w_first_branch hb hscalar.1.2.1 hscalar.1.1
      have hmax_ge_branch :
          (4 * b) ^ 3 ≤
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        le_max_left _ _
      have hmul :
          G ^ 2 * (4 * b) ^ 3 ≤
            G ^ 2 *
              max ((4 * b) ^ 3)
                (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
      simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
    have hw_ge_ck :
        ((withTheorem1Parameters S b G L).c *
            (withTheorem1Parameters S b G L).k / (4 * L)) ^ 3 ≤
          (withTheorem1Parameters S b G L).w := by
      have hbranch :
          (theorem1C b L * theorem1K b G L / (4 * L)) ^ 3 =
            G ^ 2 * (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64) :=
        theorem1_c_mul_k_div_four_L_cube_eq_w_third_branch
          hb hscalar.1.2.1 hscalar.1.1
      have hmax_ge_branch :
          (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64) ≤
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        le_trans (le_max_right _ _)
          (le_max_right ((4 * b) ^ 3)
            (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)))
      have hmul :
          G ^ 2 * (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64) ≤
            G ^ 2 *
              max ((4 * b) ^ 3)
                (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
      simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
    have hc_pos : 0 < (withTheorem1Parameters S b G L).c := by
      have hb3_pos : 0 < b ^ 3 := pow_pos hb 3
      have hden_pos : 0 < 7 * b ^ 3 := by positivity
      have hterm_pos : 0 < (1 : ℝ) / (7 * b ^ 3) := by positivity
      have hsum_pos : 0 < 28 + 1 / (7 * b ^ 3) := by positivity
      simpa [withTheorem1Parameters, theorem1C] using
        mul_pos (sq_pos_of_pos hscalar.1.2.1) hsum_pos
    exact
      theorem1_generated_nextMomentumWeight_le_one
        (withTheorem1Parameters S b G L) hscalar.2.1
        (theorem1_parameterized_k_pos S T hb hscalar) hscalar.1.2.1
        hc_pos hw_ge_four hw_ge_ck

/-- Transparent replacement for the equation (4) scalar boundary bridge.

All generated-step and scalar-domain facts are derived from the corrected
minimal scalar assumptions, rather than bundled in `theorem1ScalarBoundary`. -/
private theorem theorem1_equation4_scalar_boundary_of_positive
    (S : Setup Ω Sample E) {b L G : ℝ}
    (hb : 0 < b) (hGpos : 0 < G) (hLpos : 0 < L) :
    theorem1Equation4ScalarBoundary (withTheorem1Parameters S b G L) L G := by
  classical
  have hG_nonneg : 0 ≤ G := le_of_lt hGpos
  have hgenerated :
      generatedStepsizeScalarBoundary (withTheorem1Parameters S b G L) :=
    theorem1_generated_stepsize_scalar_boundary_of_positive S hb hGpos hLpos
  have hk_pos :
      0 < (withTheorem1Parameters S b G L).k :=
    theorem1_parameterized_k_pos_of_positive S hb hGpos hLpos
  refine
    { k_pos := hk_pos
      L_pos := hLpos
      w_nonneg := ?_
      c_source_quotient := ?_
      w_ge_two_G_sq := ?_
      w_ge_four_L_k_cube := ?_
      stepsize_le_one_over_fourL := ?_
      nextMomentumWeight_le_one := ?_ }
  ·
    simpa [withTheorem1Parameters] using
      theorem1W_nonneg_of_G_nonneg (b := b) hG_nonneg
  ·
    simpa [withTheorem1Parameters] using
      (theorem1_parameter_scalar_boundary_of_positive hb hGpos hLpos).2.2.2.2.1
  ·
    let q : ℝ := ((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64
    have hmax_ge_two : (2 : ℝ) ≤ max ((4 * b) ^ 3) (max 2 q) :=
      le_trans (le_max_left (2 : ℝ) q) (le_max_right ((4 * b) ^ 3) (max 2 q))
    have hmul :
        G ^ 2 * 2 ≤ G ^ 2 * max ((4 * b) ^ 3) (max 2 q) :=
      mul_le_mul_of_nonneg_left hmax_ge_two (sq_nonneg G)
    have hcomm :
        2 * G ^ 2 ≤ G ^ 2 * max ((4 * b) ^ 3) (max 2 q) := by
      nlinarith
    simpa [withTheorem1Parameters, theorem1W, q] using hcomm
  ·
    have hbranch :
        (4 * L * theorem1K b G L) ^ 3 = G ^ 2 * (4 * b) ^ 3 :=
      theorem1_four_L_k_cube_eq_w_first_branch hb hLpos hG_nonneg
    have hmax_ge_branch :
        (4 * b) ^ 3 ≤
          max ((4 * b) ^ 3)
            (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
      le_max_left _ _
    have hmul :
        G ^ 2 * (4 * b) ^ 3 ≤
          G ^ 2 *
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
      mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
    simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
  ·
    have hw_ge_four :
        (4 * L * (withTheorem1Parameters S b G L).k) ^ 3 ≤
          (withTheorem1Parameters S b G L).w := by
      have hbranch :
          (4 * L * theorem1K b G L) ^ 3 = G ^ 2 * (4 * b) ^ 3 :=
        theorem1_four_L_k_cube_eq_w_first_branch hb hLpos hG_nonneg
      have hmax_ge_branch :
          (4 * b) ^ 3 ≤
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        le_max_left _ _
      have hmul :
          G ^ 2 * (4 * b) ^ 3 ≤
            G ^ 2 *
              max ((4 * b) ^ 3)
                (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
      simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
    exact
      theorem1_generated_stepsize_le_one_over_fourL
        (withTheorem1Parameters S b G L) hgenerated hk_pos hLpos hw_ge_four
  ·
    have hw_ge_four :
        (4 * L * (withTheorem1Parameters S b G L).k) ^ 3 ≤
          (withTheorem1Parameters S b G L).w := by
      have hbranch :
          (4 * L * theorem1K b G L) ^ 3 = G ^ 2 * (4 * b) ^ 3 :=
        theorem1_four_L_k_cube_eq_w_first_branch hb hLpos hG_nonneg
      have hmax_ge_branch :
          (4 * b) ^ 3 ≤
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        le_max_left _ _
      have hmul :
          G ^ 2 * (4 * b) ^ 3 ≤
            G ^ 2 *
              max ((4 * b) ^ 3)
                (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
      simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
    have hw_ge_ck :
        ((withTheorem1Parameters S b G L).c *
            (withTheorem1Parameters S b G L).k / (4 * L)) ^ 3 ≤
          (withTheorem1Parameters S b G L).w := by
      have hbranch :
          (theorem1C b L * theorem1K b G L / (4 * L)) ^ 3 =
            G ^ 2 * (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64) :=
        theorem1_c_mul_k_div_four_L_cube_eq_w_third_branch hb hLpos hG_nonneg
      have hmax_ge_branch :
          (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64) ≤
            max ((4 * b) ^ 3)
              (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        le_trans (le_max_right _ _)
          (le_max_right ((4 * b) ^ 3)
            (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)))
      have hmul :
          G ^ 2 * (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64) ≤
            G ^ 2 *
              max ((4 * b) ^ 3)
                (max 2 (((28 * b + 1 / (7 * b ^ 2)) ^ 3) / 64)) :=
        mul_le_mul_of_nonneg_left hmax_ge_branch (sq_nonneg G)
      simpa [withTheorem1Parameters, theorem1W, hbranch] using hmul
    have hc_pos : 0 < (withTheorem1Parameters S b G L).c := by
      have hb3_pos : 0 < b ^ 3 := pow_pos hb 3
      have hden_pos : 0 < 7 * b ^ 3 := by positivity
      have hterm_pos : 0 < (1 : ℝ) / (7 * b ^ 3) := by positivity
      have hsum_pos : 0 < 28 + 1 / (7 * b ^ 3) := by positivity
      simpa [withTheorem1Parameters, theorem1C] using
        mul_pos (sq_pos_of_pos hLpos) hsum_pos
    exact
      theorem1_generated_nextMomentumWeight_le_one
        (withTheorem1Parameters S b G L) hgenerated hk_pos hLpos
        hc_pos hw_ge_four hw_ge_ck

/-- Source-boundary gap: at the printed Theorem 1 boundary `G = 0`, the
equivalent displayed selector gives `w = 0`, so Algorithm 1's initial
stepsize quotient cannot satisfy the stronger internal `w > 0` interpretation.

This records why the scalar boundary package above is not a source-facing
Theorem 1 conclusion. -/
theorem generatedStepsizeScalarBoundary_not_for_theorem1_G_zero
    (S : Setup Ω Sample E) (b L : ℝ) :
    ¬ generatedStepsizeScalarBoundary (withTheorem1Parameters S b 0 L) := by
  intro hboundary
  rcases hboundary with ⟨hinit, _⟩
  rcases hinit with ⟨hw, _⟩
  simpa [withTheorem1Parameters, theorem1W] using hw

/-- Defining equation for `ε_t = d_t - ∇F(x_t)`. -/
theorem error_eq
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) :
    error S n ω =
      direction S n ω - S.objectiveGradient (iterate S n ω) := by
  rfl

/-- Source-facing output window `x₁, ..., x_T`, encoded over `Fin T` as
zero-based iterates of the partial Algorithm 1 run.

Source: `book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/output/math`
states that `x̂` is chosen uniformly from `x₁, ..., x_T`. -/
def sourceOutputWindow (S : Setup Ω Sample E) (T : ℕ) : Fin T → Ω → Option E :=
  fun i => sourceIterate S i.val

/-- Internal totalized output window over `x₁, ..., x_T`.

This is an arithmetic realization only; the paper-facing output window is
`sourceOutputWindow`. -/
def totalizedOutputWindow (S : Setup Ω Sample E) (T : ℕ) : Fin T → Ω → E :=
  fun i => iterate S i.val

/-- The paper's one-based output index set `{1, ..., T}`. -/
def outputTimes (T : ℕ) : Finset ℕ :=
  Finset.Icc 1 T

/-- Positivity of the horizon makes the paper output set nonempty. -/
theorem outputTimes_nonempty {T : ℕ} (hT : 0 < T) :
    (outputTimes T).Nonempty := by
  exact ⟨1, by simp [outputTimes, Nat.succ_le_of_lt hT]⟩

/-- Uniform law for the paper's random output index. -/
noncomputable def outputIndexPMF (T : ℕ) (hT : 0 < T) :
    PMF {t : ℕ // t ∈ outputTimes T} :=
  SOptLib.uniformFiniteWindowPMF (outputTimes T) (outputTimes_nonempty hT)

/-- Source-facing randomized output view `x̂ = x_R` for `R` uniform on
`{1, ..., T}`.

The subtype index is one-based paper time, so it is converted to the zero-based
internal iterate by subtracting one.

Source: `book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/output/math`
states `Choose xhat uniformly at random from x1, ..., xT`. -/
def sourceRandomOutput
    (S : Setup Ω Sample E) (T : ℕ) (_hT : 0 < T) :
    {t : ℕ // t ∈ outputTimes T} → Ω → Option E :=
  fun R => sourceIterate S (R.1 - 1)

/-- Internal totalized randomized output view.

This is not the paper-facing output object; it is retained only for arithmetic
bridges that explicitly work with the totalized run. -/
def totalizedRandomOutput
    (S : Setup Ω Sample E) (T : ℕ) (_hT : 0 < T) :
    {t : ℕ // t ∈ outputTimes T} → Ω → E :=
  fun R => iterate S (R.1 - 1)

theorem outputIndexPMF_spec (T : ℕ) (hT : 0 < T) :
    SOptLib.FiniteWindowPMFSpec (outputTimes T) (fun _ : ℕ => (1 : ℝ))
      (outputIndexPMF T hT) := by
  exact SOptLib.uniformFiniteWindowPMF_spec (outputTimes T) (outputTimes_nonempty hT)

theorem sourceRandomOutput_apply
    (S : Setup Ω Sample E) (T : ℕ) (hT : 0 < T)
    (R : {t : ℕ // t ∈ outputTimes T}) (ω : Ω) :
    sourceRandomOutput S T hT R ω = sourceIterate S (R.1 - 1) ω := by
  rfl

theorem totalizedRandomOutput_apply
    (S : Setup Ω Sample E) (T : ℕ) (hT : 0 < T)
    (R : {t : ℕ // t ∈ outputTimes T}) (ω : Ω) :
    totalizedRandomOutput S T hT R ω = iterate S (R.1 - 1) ω := by
  rfl

/-- Internal totalized uniform finite average of gradient norms.

The source-facing average printed in Theorem 1 is `sourceAverageGradientNorm`. -/
def totalizedAverageGradientNorm (S : Setup Ω Sample E) (T : ℕ) : Ω → ℝ :=
  fun ω =>
    SOptLib.finiteUniformAverage
      (fun i : Fin T => ‖S.objectiveGradient (iterate S i.val ω)‖)

theorem totalizedAverageGradientNorm_eq
    (S : Setup Ω Sample E) (T : ℕ) (ω : Ω) :
    totalizedAverageGradientNorm S T ω =
      SOptLib.finiteUniformAverage
        (fun i : Fin T => ‖S.objectiveGradient (iterate S i.val ω)‖) := by
  rfl

/-- Source-facing finite average printed in Theorem 1.

It is undefined on sample paths where some displayed Algorithm 1 iterate in
`x₁, ..., x_T` is undefined.

Source: `book/STORM/StochasticRecursiveMomentum.json#/main_theorem` displays
the rate for the uniformly random output; by the output definition this is the
uniform finite average over `x₁, ..., x_T`. -/
noncomputable def sourceAverageGradientNorm
    (S : Setup Ω Sample E) (T : ℕ) : Ω → Option ℝ :=
  fun ω =>
    if hdefined : ∀ i : Fin T, (sourceIterate S i.val ω).isSome = true then
      some
        (SOptLib.finiteUniformAverage
          (fun i : Fin T =>
            ‖S.objectiveGradient ((sourceIterate S i.val ω).get (hdefined i))‖))
    else
      none

/-- Source-facing selected-output gradient norm for the paper output law. -/
def sourceRandomOutputGradientNorm
    (S : Setup Ω Sample E) (T : ℕ) (hT : 0 < T) :
    {t : ℕ // t ∈ outputTimes T} × Ω → Option ℝ :=
  fun q =>
    match sourceRandomOutput S T hT q.1 q.2 with
    | some x => some ‖objectiveGradient S x‖
    | none => none

/-- Source-facing expectation of a partial real expression.

This is the boundary between paper expectation notation and Mathlib's total
Bochner integral: a source expectation exists only when the expression is
defined almost everywhere and the realized integrand is integrable. -/
noncomputable def sourceExpectationValue
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Option ℝ) : Option ℝ :=
  by
    classical
    exact
      if h :
          (∀ᵐ ω ∂μ, (X ω).isSome = true) ∧
            Integrable (fun ω => (X ω).getD 0) μ then
        some (∫ ω, (X ω).getD 0 ∂μ)
      else
        none

/-- Source-facing expectation comparison. -/
def sourceExpectationLE
    [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → Option ℝ) : Prop :=
  ∃ x y,
    sourceExpectationValue μ X = some x ∧
      sourceExpectationValue μ Y = some y ∧
        x ≤ y

/-- Source-facing statement that an expected partial expression is zero. -/
def sourceExpectationEqZero
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Option ℝ) : Prop :=
  sourceExpectationValue μ X = some 0

/-- Source-facing existence of an expected value for a partial expression. -/
def sourceExpectationDefined
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Option ℝ) : Prop :=
  ∃ value, sourceExpectationValue μ X = some value

/-- Source expectation spec for later proof work. -/
theorem sourceExpectationValue_eq_some_iff
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Option ℝ) (v : ℝ) :
    sourceExpectationValue μ X = some v ↔
      (∀ᵐ ω ∂μ, (X ω).isSome = true) ∧
        Integrable (fun ω => (X ω).getD 0) μ ∧
          v = ∫ ω, (X ω).getD 0 ∂μ := by
  classical
  unfold sourceExpectationValue
  by_cases h :
      (∀ᵐ ω ∂μ, (X ω).isSome = true) ∧
        Integrable (fun ω => (X ω).getD 0) μ
  · have hdef := h.1
    have hint := h.2
    constructor
    · intro hsome
      have hval :
          (∫ ω, (X ω).getD 0 ∂μ) = v := by
        simpa [h] using hsome
      exact ⟨hdef, hint, hval.symm⟩
    · intro hpack
      have hval :
          (∫ ω, (X ω).getD 0 ∂μ) = v := hpack.2.2.symm
      simpa [h, hval]
  · constructor
    · intro hsome
      simp [h] at hsome
    · intro hpack
      exact (h ⟨hpack.1, hpack.2.1⟩).elim

/-- If a source expression is undefined everywhere, its source expectation is
undefined.  This is the formal correction hook for old unguarded source-Option
statements: they cannot prove an expectation before the displayed expression
has source semantics. -/
theorem sourceExpectationValue_eq_none_of_forall_none
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Option ℝ)
    (hnone : ∀ ω, X ω = none) :
    sourceExpectationValue μ X = none := by
  classical
  unfold sourceExpectationValue
  by_cases h :
      (∀ᵐ ω ∂μ, (X ω).isSome = true) ∧
        Integrable (fun ω => (X ω).getD 0) μ
  · have hfalse : ∀ᵐ _ω ∂μ, False := by
      filter_upwards [h.1] with ω hω
      simpa [hnone ω] using hω
    rw [ae_iff] at hfalse
    simp at hfalse
  · simp [h]

/-- An everywhere-undefined source expression cannot satisfy an expectation
comparison as its left-hand side. -/
theorem not_sourceExpectationLE_left_of_forall_none
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → Option ℝ)
    (hnone : ∀ ω, X ω = none) :
    ¬ sourceExpectationLE μ X Y := by
  intro hle
  rcases hle with ⟨x, _y, hx, _hy, _hxy⟩
  have hxnone := sourceExpectationValue_eq_none_of_forall_none μ X hnone
  rw [hxnone] at hx
  cases hx

/-- An everywhere-undefined source expression cannot satisfy an expectation
comparison as its right-hand side. -/
theorem not_sourceExpectationLE_right_of_forall_none
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → Option ℝ)
    (hnone : ∀ ω, Y ω = none) :
    ¬ sourceExpectationLE μ X Y := by
  intro hle
  rcases hle with ⟨_x, y, _hx, hy, _hxy⟩
  have hynone := sourceExpectationValue_eq_none_of_forall_none μ Y hnone
  rw [hynone] at hy
  cases hy

/-- An everywhere-undefined source expression cannot have zero source
expectation. -/
theorem not_sourceExpectationEqZero_of_forall_none
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Option ℝ)
    (hnone : ∀ ω, X ω = none) :
    ¬ sourceExpectationEqZero μ X := by
  intro hzero
  have hxnone := sourceExpectationValue_eq_none_of_forall_none μ X hnone
  unfold sourceExpectationEqZero at hzero
  rw [hxnone] at hzero
  cases hzero

/-- Internal totalized expected selected-output certificate corresponding to
`𝔼[‖∇F(x̂)‖]`.

The source-facing value is `sourceRandomOutputGradientNormExpectationValue`. -/
noncomputable def totalizedRandomOutputGradientNormExpectation
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω)
    (T : ℕ) (hT : 0 < T) : ℝ :=
  ∫ q : {t : ℕ // t ∈ outputTimes T} × Ω,
      ‖objectiveGradient S (totalizedRandomOutput S T hT q.1 q.2)‖ ∂
        (SOptLib.selected_joint_measure (outputIndexPMF T hT) μ)

/-- Internal totalized deterministic average-gradient expression.

The paper-facing source value is `sourceExpectedAverageGradientNormValue`. -/
noncomputable def totalizedExpectedAverageGradientNorm
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) : ℝ :=
  ∫ ω, totalizedAverageGradientNorm S T ω ∂μ

/-- Source-facing value of `𝔼[‖∇F(x̂)‖]`. -/
noncomputable def sourceRandomOutputGradientNormExpectationValue
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω)
    (T : ℕ) (hT : 0 < T) : Option ℝ :=
  sourceExpectationValue
    (SOptLib.selected_joint_measure (outputIndexPMF T hT) μ)
    (sourceRandomOutputGradientNorm S T hT)

/-- Source-facing value of
`𝔼[(1/T)∑_{t=1}^T ‖∇F(x_t)‖]`. -/
noncomputable def sourceExpectedAverageGradientNormValue
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) : Option ℝ :=
  by
    classical
    exact
      if h :
          (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
            Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
              (∀ i : Fin T,
                Integrable
                  (fun ω =>
                    ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ) then
        some (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ)
      else
        none

/-- The source-defined finite average exposes integrability of every displayed
gradient-norm fiber once the generated source run is identified with the
totalized STORM recursion. -/
theorem sourceExpectedAverageGradientNormValue_some_to_fiber_integrable
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ)
    (hboundary : generatedStepsizeScalarBoundary S) {lhs : ℝ}
    (havg : sourceExpectedAverageGradientNormValue S μ T = some lhs) :
    ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ := by
  classical
  unfold sourceExpectedAverageGradientNormValue at havg
  by_cases h :
      (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
        Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
          (∀ i : Fin T,
            Integrable
              (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ)
  · intro i
    have hsrc := h.2.2 i
    have heq :
        (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) =
          fun ω => ‖objectiveGradient S (iterate S i.val ω)‖ := by
      funext ω
      rw [sourceIterate_eq_some_iterate_of_generated_boundary S hboundary i.val ω]
      rfl
    simpa [heq] using hsrc
  · simp [h] at havg

/-- Uniform selected-output integrals over the paper output window equal the
corresponding zero-based finite average.

This is the route-local bridge from the one-based output law
`R ∈ {1, ..., T}` to the zero-based finite window `Fin T`, in the
fiber-integrable branch where the product expansion API applies. -/
private theorem uniform_outputTimes_selected_integral_eq_finiteUniformAverage_of_integrable
    [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (T : ℕ) (hT : 0 < T)
    (Y : ℕ → Ω → ℝ)
    (hfib : ∀ i : Fin T, Integrable (fun ω => Y i.val ω) μ) :
    ∫ q : {t : ℕ // t ∈ outputTimes T} × Ω,
        Y (q.1.1 - 1) q.2 ∂
          SOptLib.selected_joint_measure (outputIndexPMF T hT) μ =
      ∫ ω, SOptLib.finiteUniformAverage (fun i : Fin T => Y i.val ω) ∂ μ := by
  simpa [outputTimes, outputIndexPMF] using
    SOptLib.integral_uniform_Icc_one_selected_output_eq_integral_finiteUniformAverage
      (mu := μ) (T := T) (hT := hT) (Y := Y) hfib

/-- A finite selector/sample product is integrable when each selected fiber is
integrable. -/
private theorem integrable_finite_index_first_prod_of_fiber_integrable
    {ι Ω : Type*} [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Ω] (ν : Measure ι) [IsFiniteMeasure ν] (μ : Measure Ω)
    [SFinite μ] (F : ι → Ω → ℝ)
    (hF_int : ∀ i, Integrable (F i) μ) :
    Integrable (fun q : ι × Ω => F q.1 q.2) (ν.prod μ) := by
  exact _root_.integrable_finite_index_first_prod_of_fiber_integrable ν μ F hF_int

/-- Under the generated scalar boundary, the partial source average agrees
pointwise with the generated finite average. -/
private theorem sourceAverageGradientNorm_eq_some_generated_average_of_boundary
    (S : Setup Ω Sample E) (T : ℕ)
    (hboundary : generatedStepsizeScalarBoundary S) (ω : Ω) :
    sourceAverageGradientNorm S T ω =
      some
        (SOptLib.finiteUniformAverage
          (fun i : Fin T => ‖S.objectiveGradient (iterate S i.val ω)‖)) := by
  classical
  simp [sourceAverageGradientNorm,
    sourceIterate_eq_some_iterate_of_generated_boundary S hboundary]

/-- Source-definedness bridge for the expected finite average in Theorem 1.

This is the converse direction needed by the source-facing theorem: generated
Algorithm 1 definedness plus finite-window gradient-norm integrability
constructs the source `Option` value represented by the generated average. -/
private theorem sourceExpectedAverageGradientNormValue_eq_some_generated_average_of_boundary
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ)
    (hboundary : generatedStepsizeScalarBoundary S)
    (hgrad_int :
      ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ) :
    sourceExpectedAverageGradientNormValue S μ T =
      some
        (∫ ω,
          SOptLib.finiteUniformAverage
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) ∂μ) := by
  classical
  have havg_getD :
      (fun ω => (sourceAverageGradientNorm S T ω).getD 0) =
        fun ω =>
          SOptLib.finiteUniformAverage
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) := by
    funext ω
    rw [sourceAverageGradientNorm_eq_some_generated_average_of_boundary S T hboundary ω]
    rfl
  have havg_int :
      Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ := by
    have hsum :
        Integrable
          (fun ω => Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖)) μ := by
      exact MeasureTheory.integrable_finset_sum (s := Finset.univ) (μ := μ)
        (fun i _hi => hgrad_int i)
    have hgenerated_avg : Integrable
        (fun ω =>
          SOptLib.finiteUniformAverage
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖)) μ := by
      simpa [SOptLib.finiteUniformAverage_def, smul_eq_mul]
        using hsum.const_mul ((Fintype.card (Fin T) : ℝ)⁻¹)
    simpa [havg_getD] using hgenerated_avg
  have hdef :
      ∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true :=
    ae_of_all _ (fun ω =>
      by
        rw [sourceAverageGradientNorm_eq_some_generated_average_of_boundary
          S T hboundary ω]
        rfl)
  have hsrc_fib :
      ∀ i : Fin T,
        Integrable
          (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ := by
    intro i
    have heq :
        (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) =
          fun ω => ‖objectiveGradient S (iterate S i.val ω)‖ := by
      funext ω
      rw [sourceIterate_eq_some_iterate_of_generated_boundary S hboundary i.val ω]
      rfl
    simpa [heq] using hgrad_int i
  have hpack :
      (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
        Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
          (∀ i : Fin T,
            Integrable
              (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ) :=
    ⟨hdef, havg_int, hsrc_fib⟩
  unfold sourceExpectedAverageGradientNormValue
  change
    (if h :
        (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
          Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
            (∀ i : Fin T,
              Integrable
                (fun ω =>
                  ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ) then
      some (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ)
    else
      none) =
        some
          (∫ ω,
            SOptLib.finiteUniformAverage
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) ∂μ)
  rw [show
    (if h :
        (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
          Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
            (∀ i : Fin T,
              Integrable
                (fun ω =>
                  ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ) then
      some (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ)
    else
      none) = some (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ) from if_pos hpack]
  congr 1
  change (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ) =
    ∫ ω,
      SOptLib.finiteUniformAverage
        (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) ∂μ
  rw [havg_getD]

/-- Under the generated scalar boundary, the partial source random output
agrees pointwise with the corresponding generated selected output. -/
private theorem sourceRandomOutputGradientNorm_eq_some_generated_output_of_boundary
    (S : Setup Ω Sample E) (T : ℕ) (hT : 0 < T)
    (hboundary : generatedStepsizeScalarBoundary S)
    (q : {t : ℕ // t ∈ outputTimes T} × Ω) :
    sourceRandomOutputGradientNorm S T hT q =
      some ‖objectiveGradient S (iterate S (q.1.1 - 1) q.2)‖ := by
  simp [sourceRandomOutputGradientNorm, sourceRandomOutput,
    sourceIterate_eq_some_iterate_of_generated_boundary S hboundary]

/-- Internal totalized equality between selected-output expectation and
finite-window average.  The source-facing output equality is
`sourceRandomOutputGradientNormExpectationValue_eq_sourceExpectedAverage`. -/
private theorem totalizedRandomOutputGradientNormExpectation_eq_totalizedExpectedAverageGradientNorm
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) [SFinite μ]
    (T : ℕ) (hT : 0 < T)
    (hgrad_int :
      ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ) :
    totalizedRandomOutputGradientNormExpectation S μ T hT =
      totalizedExpectedAverageGradientNorm S μ T := by
  simpa [totalizedRandomOutputGradientNormExpectation,
    totalizedExpectedAverageGradientNorm, totalizedAverageGradientNorm,
    totalizedRandomOutput] using
    uniform_outputTimes_selected_integral_eq_finiteUniformAverage_of_integrable
      (μ := μ) (T := T) (hT := hT)
      (Y := fun n ω => ‖objectiveGradient S (iterate S n ω)‖) hgrad_int

/-- Source-facing equality between the random-output expectation and the
finite-window average, with expectation well-definedness exposed by `Option`. -/
theorem sourceRandomOutputGradientNormExpectationValue_eq_sourceExpectedAverage
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) [SFinite μ]
    (T : ℕ) (hT : 0 < T)
    (hboundary : generatedStepsizeScalarBoundary S)
    (hgrad_int :
      ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ) :
    sourceRandomOutputGradientNormExpectationValue S μ T hT =
      sourceExpectedAverageGradientNormValue S μ T := by
  classical
  let Y : ℕ → Ω → ℝ := fun n ω => ‖objectiveGradient S (iterate S n ω)‖
  have hsel_getD :
      (fun q : {t : ℕ // t ∈ outputTimes T} × Ω =>
          (sourceRandomOutputGradientNorm S T hT q).getD 0) =
        fun q => Y (q.1.1 - 1) q.2 := by
    funext q
    rw [sourceRandomOutputGradientNorm_eq_some_generated_output_of_boundary
      S T hT hboundary q]
    rfl
  have hsel_int :
      Integrable
        (fun q : {t : ℕ // t ∈ outputTimes T} × Ω =>
          (sourceRandomOutputGradientNorm S T hT q).getD 0)
        (SOptLib.selected_joint_measure (outputIndexPMF T hT) μ) := by
    have hfib :
        ∀ R : {t : ℕ // t ∈ outputTimes T}, Integrable (fun ω => Y (R.1 - 1) ω) μ := by
      intro R
      have hmem : R.1 ∈ Finset.Icc 1 T := by
        simpa [outputTimes] using R.2
      have hlt : R.1 - 1 < T := by
        have hbounds := Finset.mem_Icc.mp hmem
        omega
      simpa [Y] using hgrad_int ⟨R.1 - 1, hlt⟩
    have hprod :
        Integrable (fun q : {t : ℕ // t ∈ outputTimes T} × Ω => Y (q.1.1 - 1) q.2)
          ((outputIndexPMF T hT).toMeasure.prod μ) :=
      integrable_finite_index_first_prod_of_fiber_integrable
        (ν := (outputIndexPMF T hT).toMeasure) (μ := μ)
        (F := fun R : {t : ℕ // t ∈ outputTimes T} => fun ω => Y (R.1 - 1) ω)
        hfib
    simpa [hsel_getD, SOptLib.selected_joint_measure] using hprod
  have havg_getD :
      (fun ω => (sourceAverageGradientNorm S T ω).getD 0) =
        fun ω =>
          SOptLib.finiteUniformAverage
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) := by
    funext ω
    rw [sourceAverageGradientNorm_eq_some_generated_average_of_boundary S T hboundary ω]
    rfl
  have havg_int :
      Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ := by
    have hsum :
        Integrable
          (fun ω => Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖)) μ := by
      exact MeasureTheory.integrable_finset_sum (s := Finset.univ) (μ := μ)
        (fun i _hi => hgrad_int i)
    have hgenerated_avg : Integrable
        (fun ω =>
          SOptLib.finiteUniformAverage
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖)) μ := by
      simpa [SOptLib.finiteUniformAverage_def, smul_eq_mul]
        using hsum.const_mul ((Fintype.card (Fin T) : ℝ)⁻¹)
    simpa [havg_getD] using hgenerated_avg
  have hsel_some :
      sourceRandomOutputGradientNormExpectationValue S μ T hT =
        some
          (∫ q : {t : ℕ // t ∈ outputTimes T} × Ω,
            Y (q.1.1 - 1) q.2 ∂
              SOptLib.selected_joint_measure (outputIndexPMF T hT) μ) := by
    rw [sourceRandomOutputGradientNormExpectationValue, sourceExpectationValue_eq_some_iff]
    refine ⟨?_, hsel_int, ?_⟩
    · exact ae_of_all _ (fun q =>
        by
          rw [sourceRandomOutputGradientNorm_eq_some_generated_output_of_boundary
            S T hT hboundary q]
          rfl)
    · simp [hsel_getD]
  have havg_some :
      sourceExpectedAverageGradientNormValue S μ T =
        some
          (∫ ω,
            SOptLib.finiteUniformAverage
              (fun i : Fin T => Y i.val ω) ∂μ) := by
    have hdef :
        ∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true :=
      ae_of_all _ (fun ω =>
        by
          rw [sourceAverageGradientNorm_eq_some_generated_average_of_boundary
            S T hboundary ω]
          rfl)
    have hsrc_fib :
        ∀ i : Fin T,
          Integrable
            (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ := by
      intro i
      have heq :
          (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) =
            fun ω => ‖objectiveGradient S (iterate S i.val ω)‖ := by
        funext ω
        rw [sourceIterate_eq_some_iterate_of_generated_boundary S hboundary i.val ω]
        rfl
      simpa [heq] using hgrad_int i
    have hpack :
        (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
          Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
            (∀ i : Fin T,
              Integrable
                (fun ω => ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ) :=
      ⟨hdef, havg_int, hsrc_fib⟩
    unfold sourceExpectedAverageGradientNormValue
    change
      (if h :
          (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
            Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
              (∀ i : Fin T,
                Integrable
                  (fun ω =>
                    ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ) then
        some (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ)
      else
        none) =
          some
            (∫ ω,
              SOptLib.finiteUniformAverage
                (fun i : Fin T => Y i.val ω) ∂μ)
    rw [show
      (if h :
          (∀ᵐ ω ∂μ, (sourceAverageGradientNorm S T ω).isSome = true) ∧
            Integrable (fun ω => (sourceAverageGradientNorm S T ω).getD 0) μ ∧
              (∀ i : Fin T,
                Integrable
                  (fun ω =>
                    ‖objectiveGradient S ((sourceIterate S i.val ω).getD S.x₁)‖) μ) then
        some (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ)
      else
        none) = some (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ) from if_pos hpack]
    congr 1
    change (∫ ω, (sourceAverageGradientNorm S T ω).getD 0 ∂μ) =
      ∫ ω, SOptLib.finiteUniformAverage (fun i : Fin T => Y i.val ω) ∂μ
    rw [havg_getD]
  rw [hsel_some, havg_some]
  congr 1
  exact
    uniform_outputTimes_selected_integral_eq_finiteUniformAverage_of_integrable
      (μ := μ) (T := T) (hT := hT) (Y := Y) hgrad_int

/-- Source expression for Lemma 1's left-hand side. -/
def lemma1LHSExpr (S : Setup Ω Sample E) (t : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceIterate S (t + 1) ω, sourceIterate S t ω with
    | some xNext, some x => some (S.objectiveValue xNext - S.objectiveValue x)
    | _, _ => none

/-- Source expression for Lemma 1's right-hand side. -/
def lemma1RHSExpr (S : Setup Ω Sample E) (t : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceStepsize S t ω, sourceIterate S t ω, sourceError S t ω with
    | some η, some x, some ε =>
        some ((-η / 4) * ‖objectiveGradient S x‖ ^ 2 + (3 * η / 4) * ‖ε‖ ^ 2)
    | _, _, _ => none

/-- Source expression for Lemma 3's first cross term. -/
def lemma3FirstCrossTermExpr (S : Setup Ω Sample E) (t : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceIterate S (t + 1) ω, sourceStepsize S t ω,
        sourceNextMomentumWeight S t ω, sourceError S t ω with
    | some xNext, some η, some aNext, some ε =>
        match sourceQuotientValue 1 η with
        | some ηInv =>
            some
              (inner ℝ
                (stochasticGradient S xNext (S.sample (t + 1) ω) -
                  objectiveGradient S xNext)
                ((ηInv * (1 - aNext) ^ 2) • ε))
        | none => none
    | _, _, _, _ => none

/-- Source expression for Lemma 3's second cross term. -/
def lemma3SecondCrossTermExpr (S : Setup Ω Sample E) (t : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceIterate S (t + 1) ω, sourceIterate S t ω, sourceStepsize S t ω,
        sourceNextMomentumWeight S t ω, sourceError S t ω with
    | some xNext, some x, some η, some aNext, some ε =>
        match sourceQuotientValue 1 η with
        | some ηInv =>
            some
              (inner ℝ
                (stochasticGradient S xNext (S.sample (t + 1) ω) -
                  stochasticGradient S x (S.sample (t + 1) ω) -
                  objectiveGradient S xNext +
                  objectiveGradient S x)
                ((ηInv * (1 - aNext) ^ 2) • ε))
        | none => none
    | _, _, _, _, _ => none

/-- Source expression for Lemma 2's left-hand side. -/
def lemma2LHSExpr (S : Setup Ω Sample E) (t : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceError S (t + 1) ω, sourceStepsize S t ω with
    | some εNext, some η => sourceQuotientValue (‖εNext‖ ^ 2) η
    | _, _ => none

/-- Source expression for Lemma 2's right-hand side. -/
def lemma2RHSExpr (S : Setup Ω Sample E) (L : ℝ) (t : ℕ) : Ω → Option ℝ :=
  fun ω =>
    match sourceStepsize S t ω, sourceNextMomentumWeight S t ω, sourceError S t ω,
        sourceIterate S t ω, sourceIterate S (t + 1) ω with
    | some η, some aNext, some ε, some x, some xNext =>
        match sourceQuotientValue
            ((1 - aNext) ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * ‖ε‖ ^ 2) η with
        | some weightedError =>
            some
              (2 * S.c ^ 2 * η ^ 3 *
                  ‖stochasticGradient S xNext (S.sample (t + 1) ω)‖ ^ 2 +
                weightedError +
                4 * (1 - aNext) ^ 2 * L ^ 2 * η * ‖objectiveGradient S x‖ ^ 2)
        | none => none
    | _, _, _, _, _ => none

/-- Exact local source-definedness boundary for Lemma 1's two source
expressions at the displayed time `t`.

This is intentionally weaker than a global generated-run boundary: it records
only the Algorithm 1 source variables that `lemma1LHSExpr` and `lemma1RHSExpr`
consume at this index. -/
def lemma1LocalSourceBoundary (S : Setup Ω Sample E) (t : ℕ) : Prop :=
  ∀ ω,
    sourceIterate S t ω = some (iterate S t ω) ∧
      sourceIterate S (t + 1) ω = some (iterate S (t + 1) ω) ∧
        sourceStepsize S t ω = some (stepsize S t ω) ∧
          sourceError S t ω = some (error S t ω)

/-- Source-definedness and reciprocal-stepsize boundary for Lemma 3's two
cross-term source expressions.

The expectation in Lemma 3 uses the generated reciprocal stepsize as a random
multiplier.  Pointwise quotient success is not enough for the Mathlib
integrability route: the totalized reciprocal can be unbounded when the
adaptive denominator has no source-level positive floor.  We therefore route
Lemma 3 through the generated quotient boundary, which is the source-facing
Algorithm 1 stepsize boundary plus `0 < k`, rather than through a weaker
pointwise-only local predicate. -/
def lemma3LocalQuotientBoundary (S : Setup Ω Sample E) (_t : ℕ) : Prop :=
  generatedStepsizeQuotientBoundary S

/-- Lemma 3's quotient boundary exposes the positive adaptive-denominator
floor inherited from Algorithm 1's source-defined initial stepsize. -/
theorem lemma3LocalQuotientBoundary_w_pos
    (S : Setup Ω Sample E) {t : ℕ}
    (hboundary : lemma3LocalQuotientBoundary S t) :
    0 < S.w :=
  hboundary.1.1.1

/-- Lemma 3's quotient boundary exposes the nonzero numerator of the generated
stepsize quotient, which is needed for the displayed reciprocal `η_t⁻¹`. -/
theorem lemma3LocalQuotientBoundary_k_ne
    (S : Setup Ω Sample E) {t : ℕ}
    (hboundary : lemma3LocalQuotientBoundary S t) :
    S.k ≠ 0 :=
  ne_of_gt hboundary.2

/-- Exact local source-definedness and quotient boundary for Lemma 2's
recurrence source expressions at the displayed time `t`. -/
def lemma2LocalQuotientBoundary (S : Setup Ω Sample E) (L : ℝ) (t : ℕ) : Prop :=
  ∀ ω,
    sourceError S (t + 1) ω = some (error S (t + 1) ω) ∧
      sourceStepsize S t ω = some (stepsize S t ω) ∧
        sourceQuotientValue (‖error S (t + 1) ω‖ ^ 2) (stepsize S t ω) =
          some (‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω) ∧
          sourceNextMomentumWeight S t ω = some (nextMomentumWeight S t ω) ∧
            sourceError S t ω = some (error S t ω) ∧
              sourceIterate S t ω = some (iterate S t ω) ∧
                sourceIterate S (t + 1) ω = some (iterate S (t + 1) ω) ∧
                  sourceQuotientValue
                    ((1 - nextMomentumWeight S t ω) ^ 2 *
                      (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                        ‖error S t ω‖ ^ 2)
                    (stepsize S t ω) =
                    some
                      (((1 - nextMomentumWeight S t ω) ^ 2 *
                        (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                          ‖error S t ω‖ ^ 2) / stepsize S t ω)

/-- The global generated-run boundary implies Lemma 1's exact local source
boundary at every index. -/
theorem lemma1LocalSourceBoundary_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeScalarBoundary S) (t : ℕ) :
    lemma1LocalSourceBoundary S t := by
  intro ω
  exact
    ⟨sourceIterate_eq_some_iterate_of_generated_boundary S hboundary t ω,
      sourceIterate_eq_some_iterate_of_generated_boundary S hboundary (t + 1) ω,
      sourceStepsize_eq_some_stepsize_of_generated_boundary S hboundary t ω,
      sourceError_eq_some_error_of_generated_boundary S hboundary t ω⟩

/-- The global generated quotient boundary implies Lemma 3's exact local
source and reciprocal boundary at every index. -/
theorem lemma3LocalQuotientBoundary_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) (t : ℕ) :
    lemma3LocalQuotientBoundary S t := by
  exact hboundary

/-- The scalar boundary used by the Theorem 1 source-facing parameterization
supplies Lemma 3's generated quotient boundary for the parameterized STORM
setup. -/
theorem lemma3LocalQuotientBoundary_of_theorem1ScalarBoundary
    (S : Setup Ω Sample E) (T : ℕ) (b L G σ fStar : ℝ)
    (hb : 0 < b)
    (hscalar : theorem1ScalarBoundary S T b L G σ fStar) (t : ℕ) :
    lemma3LocalQuotientBoundary (withTheorem1Parameters S b G L) t := by
  exact ⟨hscalar.2.1, theorem1_parameterized_k_pos S T hb hscalar⟩

/-- The global generated quotient boundary implies Lemma 2's exact local
source and quotient boundary at every index. -/
theorem lemma2LocalQuotientBoundary_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) (L : ℝ) (t : ℕ) :
    lemma2LocalQuotientBoundary S L t := by
  intro ω
  have hden : stepsize S t ω ≠ 0 :=
    stepsize_ne_zero_of_generated_quotient_boundary S hboundary t ω
  exact
    ⟨sourceError_eq_some_error_of_generated_boundary S hboundary.1 (t + 1) ω,
      sourceStepsize_eq_some_stepsize_of_generated_boundary S hboundary.1 t ω,
      sourceQuotientValue_eq_some_of_den_ne hden,
      sourceNextMomentumWeight_eq_some_nextMomentumWeight_of_generated_boundary
        S hboundary.1 t ω,
      sourceError_eq_some_error_of_generated_boundary S hboundary.1 t ω,
      sourceIterate_eq_some_iterate_of_generated_boundary S hboundary.1 t ω,
      sourceIterate_eq_some_iterate_of_generated_boundary S hboundary.1 (t + 1) ω,
      sourceQuotientValue_eq_some_of_den_ne hden⟩

/-- Typed route certificate for the source/coarser Lemma 2 boundary.

Lemma 2 is stated with Algorithm 1's generated notation.  This certificate
packages the exact local source-expression boundary together with the
positivity and reciprocal source-definedness facts supplied by the generated
quotient boundary, so the active Lemma 2 proof consumes the generated route
rather than the obsolete local-only compatibility route. -/
private theorem lemma2_generated_boundary_source_route_certificate
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) (L : ℝ) (t : ℕ) :
    lemma2LocalQuotientBoundary S L t ∧
      (∀ ω, 0 < stepsize S t ω) ∧
        (∀ ω, sourceStepsize S t ω = some (stepsize S t ω)) ∧
          (∀ ω, sourceQuotientValue 1 (stepsize S t ω) =
            some (1 / stepsize S t ω)) := by
  refine ⟨lemma2LocalQuotientBoundary_of_generated_boundary S hboundary L t, ?_, ?_, ?_⟩
  · intro ω
    exact stepsize_pos_of_generated_quotient_boundary S hboundary t ω
  · intro ω
    exact sourceStepsize_eq_some_stepsize_of_generated_boundary S hboundary.1 t ω
  · intro ω
    exact sourceStepsizeInverseValue_eq_some_of_generated_quotient_boundary S hboundary t ω

/-- Private audit packet for the active Lemma 2 generated-boundary route.

This is not a replacement theorem for Lemma 2.  It records the source-facing
facts supplied by Algorithm 1's generated quotient boundary before the proof
enters the long totalized integral recurrence: local source expression
definedness, positive generated stepsizes, and source-defined reciprocals. -/
private structure Lemma2GeneratedBoundaryRouteEvidence
    (S : Setup Ω Sample E) (L : ℝ) (t : ℕ) : Prop where
  source_local_boundary : lemma2LocalQuotientBoundary S L t
  stepsize_positive : ∀ ω, 0 < stepsize S t ω
  source_stepsize : ∀ ω, sourceStepsize S t ω = some (stepsize S t ω)
  source_stepsize_inverse :
    ∀ ω, sourceQuotientValue 1 (stepsize S t ω) =
      some (1 / stepsize S t ω)

/-- Compiled source-route evidence for Lemma 2 under the generated quotient
boundary.  The active recurrence proof consumes this packet instead of routing
through the older local-only compatibility predicate. -/
private theorem lemma2_generated_boundary_route_evidence
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) (L : ℝ) (t : ℕ) :
    Lemma2GeneratedBoundaryRouteEvidence S L t := by
  rcases lemma2_generated_boundary_source_route_certificate S hboundary L t with
    ⟨hlocal, hη_pos, hη_source, hη_inv_source⟩
  exact
    { source_local_boundary := hlocal
      stepsize_positive := hη_pos
      source_stepsize := hη_source
      source_stepsize_inverse := hη_inv_source }

/-- Lemma 1's local boundary identifies its left source expression with the
corresponding totalized expression. -/
theorem lemma1LHSExpr_eq_some_of_local_boundary
    (S : Setup Ω Sample E) {t : ℕ}
    (hboundary : lemma1LocalSourceBoundary S t) (ω : Ω) :
    lemma1LHSExpr S t ω =
      some (S.objectiveValue (iterate S (t + 1) ω) -
        S.objectiveValue (iterate S t ω)) := by
  rcases hboundary ω with ⟨hx, hxNext, _hη, _hε⟩
  simp [lemma1LHSExpr, hx, hxNext]

/-- Lemma 1's local boundary identifies its right source expression with the
corresponding totalized expression. -/
theorem lemma1RHSExpr_eq_some_of_local_boundary
    (S : Setup Ω Sample E) {t : ℕ}
    (hboundary : lemma1LocalSourceBoundary S t) (ω : Ω) :
    lemma1RHSExpr S t ω =
      some ((-stepsize S t ω / 4) * ‖objectiveGradient S (iterate S t ω)‖ ^ 2 +
        (3 * stepsize S t ω / 4) * ‖error S t ω‖ ^ 2) := by
  rcases hboundary ω with ⟨hx, _hxNext, hη, hε⟩
  simp [lemma1RHSExpr, hη, hx, hε]

/-- Lemma 3's local boundary identifies its first cross-term source expression
with the corresponding totalized expression. -/
theorem lemma3FirstCrossTermExpr_eq_some_of_local_boundary
    (S : Setup Ω Sample E) {t : ℕ}
    (hboundary : lemma3LocalQuotientBoundary S t) (ω : Ω) :
    lemma3FirstCrossTermExpr S t ω =
      some
        (inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) := by
  have hxNext :=
    sourceIterate_eq_some_iterate_of_generated_boundary S hboundary.1 (t + 1) ω
  have hη := sourceStepsize_eq_some_stepsize_of_generated_boundary S hboundary.1 t ω
  have ha :=
    sourceNextMomentumWeight_eq_some_nextMomentumWeight_of_generated_boundary
      S hboundary.1 t ω
  have hε := sourceError_eq_some_error_of_generated_boundary S hboundary.1 t ω
  have hηInv := sourceStepsizeInverseValue_eq_some_of_generated_quotient_boundary
    S hboundary t ω
  simp [lemma3FirstCrossTermExpr, hxNext, hη, ha, hε, hηInv]

/-- Lemma 3's local boundary identifies its second cross-term source expression
with the corresponding totalized expression. -/
theorem lemma3SecondCrossTermExpr_eq_some_of_local_boundary
    (S : Setup Ω Sample E) {t : ℕ}
    (hboundary : lemma3LocalQuotientBoundary S t) (ω : Ω) :
    lemma3SecondCrossTermExpr S t ω =
      some
        (inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) := by
  have hx :=
    sourceIterate_eq_some_iterate_of_generated_boundary S hboundary.1 t ω
  have hxNext :=
    sourceIterate_eq_some_iterate_of_generated_boundary S hboundary.1 (t + 1) ω
  have hη := sourceStepsize_eq_some_stepsize_of_generated_boundary S hboundary.1 t ω
  have ha :=
    sourceNextMomentumWeight_eq_some_nextMomentumWeight_of_generated_boundary
      S hboundary.1 t ω
  have hε := sourceError_eq_some_error_of_generated_boundary S hboundary.1 t ω
  have hηInv := sourceStepsizeInverseValue_eq_some_of_generated_quotient_boundary
    S hboundary t ω
  simp [lemma3SecondCrossTermExpr, hxNext, hx, hη, ha, hε, hηInv]

/-- Lemma 2's local boundary identifies its left recurrence source expression
with the corresponding totalized quotient. -/
theorem lemma2LHSExpr_eq_some_of_local_boundary
    (S : Setup Ω Sample E) {L : ℝ} {t : ℕ}
    (hboundary : lemma2LocalQuotientBoundary S L t) (ω : Ω) :
    lemma2LHSExpr S t ω =
      some (‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω) := by
  rcases hboundary ω with ⟨hεNext, hη, hq, _ha, _hε, _hx, _hxNext, _hqRHS⟩
  simp [lemma2LHSExpr, hεNext, hη, hq]

/-- Lemma 2's local boundary identifies its right recurrence source expression
with the corresponding totalized expression. -/
theorem lemma2RHSExpr_eq_some_of_local_boundary
    (S : Setup Ω Sample E) {L : ℝ} {t : ℕ}
    (hboundary : lemma2LocalQuotientBoundary S L t) (ω : Ω) :
    lemma2RHSExpr S L t ω =
      some
        (2 * S.c ^ 2 * stepsize S t ω ^ 3 *
            ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
          (((1 - nextMomentumWeight S t ω) ^ 2 *
              (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                ‖error S t ω‖ ^ 2) / stepsize S t ω) +
          4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 * stepsize S t ω *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2) := by
  rcases hboundary ω with ⟨_hεNext, hη, _hqLHS, ha, hε, hx, hxNext, hqRHS⟩
  simp [lemma2RHSExpr, hη, ha, hε, hx, hxNext, hqRHS]

/-- Source expectation closure from a pointwise totalized representative.

This is a proof-boundary helper: callers still have to prove integrability and
the actual zero integral of the totalized representative. -/
private theorem sourceExpectationEqZero_of_forall_eq_some
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Option ℝ) (Z : Ω → ℝ)
    (hX : ∀ ω, X ω = some (Z ω))
    (hZint : Integrable Z μ)
    (hZzero : ∫ ω, Z ω ∂μ = 0) :
    sourceExpectationEqZero μ X := by
  unfold sourceExpectationEqZero
  rw [sourceExpectationValue_eq_some_iff]
  have hget : (fun ω => (X ω).getD 0) = Z := by
    funext ω
    simp [hX ω]
  exact
    ⟨ae_of_all _ (fun ω => by simp [hX ω]),
      by simpa [hget] using hZint,
      by simpa [hget, hZzero]⟩

/-- Source expectation comparison from pointwise totalized representatives.

This is a proof-boundary helper: callers still have to prove integrability and
the displayed integral inequality for the totalized representatives. -/
private theorem sourceExpectationLE_of_forall_eq_some
    [MeasurableSpace Ω] (μ : Measure Ω) (X Y : Ω → Option ℝ) (Z W : Ω → ℝ)
    (hX : ∀ ω, X ω = some (Z ω))
    (hY : ∀ ω, Y ω = some (W ω))
    (hZint : Integrable Z μ)
    (hWint : Integrable W μ)
    (hle : ∫ ω, Z ω ∂μ ≤ ∫ ω, W ω ∂μ) :
    sourceExpectationLE μ X Y := by
  unfold sourceExpectationLE
  refine ⟨∫ ω, Z ω ∂μ, ∫ ω, W ω ∂μ, ?_, ?_, hle⟩
  · rw [sourceExpectationValue_eq_some_iff]
    have hget : (fun ω => (X ω).getD 0) = Z := by
      funext ω
      simp [hX ω]
    exact
      ⟨ae_of_all _ (fun ω => by simp [hX ω]),
        by simpa [hget] using hZint,
        by simpa [hget]⟩
  · rw [sourceExpectationValue_eq_some_iff]
    have hget : (fun ω => (Y ω).getD 0) = W := by
      funext ω
      simp [hY ω]
    exact
      ⟨ae_of_all _ (fun ω => by simp [hY ω]),
        by simpa [hget] using hWint,
        by simpa [hget]⟩

/-- Lemma 2 source comparison reduced to its totalized integrability and
integral inequality obligations under the local quotient boundary. -/
private theorem lemma2_sourceExpectationLE_of_generated_integral_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (L : ℝ) (t : ℕ)
    (hboundary : lemma2LocalQuotientBoundary S L t)
    (hlhs_int :
      Integrable
        (fun ω => ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω) μ)
    (hrhs_int :
      Integrable
        (fun ω =>
          2 * S.c ^ 2 * stepsize S t ω ^ 3 *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
            (((1 - nextMomentumWeight S t ω) ^ 2 *
                (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                  ‖error S t ω‖ ^ 2) / stepsize S t ω) +
            4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 * stepsize S t ω *
              ‖objectiveGradient S (iterate S t ω)‖ ^ 2) μ)
    (hle :
      ∫ ω, ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω ∂μ ≤
        ∫ ω,
          2 * S.c ^ 2 * stepsize S t ω ^ 3 *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
            (((1 - nextMomentumWeight S t ω) ^ 2 *
                (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                  ‖error S t ω‖ ^ 2) / stepsize S t ω) +
            4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 * stepsize S t ω *
              ‖objectiveGradient S (iterate S t ω)‖ ^ 2 ∂μ) :
    sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t) := by
  exact
    sourceExpectationLE_of_forall_eq_some μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t)
      (fun ω => ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω)
      (fun ω =>
        2 * S.c ^ 2 * stepsize S t ω ^ 3 *
            ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
          (((1 - nextMomentumWeight S t ω) ^ 2 *
              (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                ‖error S t ω‖ ^ 2) / stepsize S t ω) +
          4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 * stepsize S t ω *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2)
      (lemma2LHSExpr_eq_some_of_local_boundary S hboundary)
      (lemma2RHSExpr_eq_some_of_local_boundary S hboundary)
      hlhs_int hrhs_int hle

/-- First Lemma 3 totalized cross-term cancellation, specialized to the STORM
expression, once the oracle-cancellation side conditions have been supplied. -/
private theorem lemma3_first_cross_term_integral_eq_zero_of_oracle_premises
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hquery :
      Measurable
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)))
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hres_meas :
      Measurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1))
    (hfixed_int :
      ∀ q : DecisionSpace d × DecisionSpace d,
        Integrable
          (fun ξ => stochasticGradient S q.1 ξ - objectiveGradient S q.1)
          (Measure.map (S.sample (t + 1)) μ))
    (hfixed_zero :
      ∀ q : DecisionSpace d × DecisionSpace d,
        ∫ ξ, stochasticGradient S q.1 ξ - objectiveGradient S q.1
          ∂Measure.map (S.sample (t + 1)) μ = 0) :
    ∫ ω,
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω) ∂μ = 0 := by
  let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
    (iterate S (t + 1) ω,
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let residual : DecisionSpace d × DecisionSpace d → Sample → DecisionSpace d :=
    fun q ξ => stochasticGradient S q.1 ξ - objectiveGradient S q.1
  let direction : DecisionSpace d × DecisionSpace d → DecisionSpace d := Prod.snd
  have hzero :=
    randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      (P := μ) (ν := Measure.map sample μ) (query := query) (sample := sample)
      (residual := residual) (d := direction)
      (by simpa [residual] using hres_meas)
      (by simpa [direction] using (measurable_snd :
        Measurable (fun q : DecisionSpace d × DecisionSpace d => q.2)))
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample)
      (by simpa [query, sample] using hindep)
      rfl
      (by simpa [residual, sample] using hfixed_int)
      (by simpa [residual, sample] using hfixed_zero)
  simpa [query, sample, residual, direction, real_inner_comm] using hzero

/-- Product-law/a.e. version of `integral_comp_eq_zero_of_indep_fixed_integral_zero`.

This is the same independence-and-fixed-centering transfer, but it requires only
a.e. strong measurability of the scalar kernel under the product law actually
generated by the random query and fresh sample.  It avoids strengthening the
STORM Section 3 interface to a full off-stream measurable stochastic-gradient
kernel. -/
private theorem integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
    {Ω W S V : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure P] [SFinite ν]
    {φ : W → S → V} {X : Ω → W} {Y : Ω → S}
    (hφ_prod :
      AEStronglyMeasurable
        (fun p : W × S => φ p.1 p.2) ((Measure.map X P).prod ν))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h_indep : ProbabilityTheory.IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hfixed_zero : ∀ w, ∫ s, φ w s ∂ν = 0) :
    ∫ ω, φ (X ω) (Y ω) ∂P = 0 := by
  exact _root_.integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
    hφ_prod hX hY h_indep h_dist h_int hfixed_zero

/-- A.e.-product-law version of SOptLib's independent fixed-fiber
integrability transfer.

This is the regularity shape produced by the law-scoped Lemma 3 route: the
kernel is a.e. strongly measurable under the product law generated by the
adapted query and the fresh sample, but the source record does not give a full
off-stream measurable stochastic-gradient kernel. -/
private theorem integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure P]
    {φ : W → S → ℝ} {X : Ω → W} {Y : Ω → S} {C : ℝ}
    (hφ_prod :
      AEStronglyMeasurable
        (fun p : W × S => φ p.1 p.2) ((Measure.map X P).prod ν))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h_indep : ProbabilityTheory.IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (hφ_nonneg : ∀ w s, 0 ≤ φ w s)
    (hC_nonneg : 0 ≤ C)
    (hfixed_int : ∀ w, Integrable (fun s => φ w s) ν)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ C) :
    Integrable (fun ω => φ (X ω) (Y ω)) P := by
  exact _root_.integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable hφ_prod hX hY h_indep h_dist hφ_nonneg hfixed_int hfixed_bound

/-- A.e.-product-law version of the independent fixed-fiber integral-bound
transfer.

This is the bound counterpart of
`integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable`.  It is
the faithful interface for Section 3's law-scoped stochastic-gradient residual:
the kernel is known under the generated product law, not as a globally
measurable off-stream function. -/
private theorem integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → S → ℝ} {X : Ω → W} {Y : Ω → S} {C : ℝ}
    (hφ_prod :
      AEStronglyMeasurable
        (fun p : W × S => φ p.1 p.2) ((Measure.map X P).prod ν))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h_indep : ProbabilityTheory.IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ C) :
    ∫ ω, φ (X ω) (Y ω) ∂P ≤ C := by
  exact _root_.integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
    (P := P) (ν := ν) (φ := φ) (X := X) (Y := Y) (C := C)
    hφ_prod hX hY h_indep h_dist h_int hfixed_bound

/-- First Lemma 3 totalized cross-term cancellation using only scalar
regularity under the sampled product law.

Compared with `lemma3_first_cross_term_integral_eq_zero_of_oracle_premises`,
this helper does not require full vector-valued residual-kernel measurability
on `((x, d), ξ)`.  The remaining regularity premise is exactly the scalar
kernel appearing in the conditioning proof, under the product law generated by
the adapted query and the fresh sample. -/
private theorem lemma3_first_cross_term_integral_eq_zero_of_sampled_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hquery :
      AEMeasurable
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hscalar_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          inner ℝ p.1.2
            (stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1))
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)))
    (hinner_int :
      Integrable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hfixed_int :
      ∀ q : DecisionSpace d × DecisionSpace d,
        Integrable
          (fun ξ => stochasticGradient S q.1 ξ - objectiveGradient S q.1)
          (Measure.map (S.sample (t + 1)) μ))
    (hfixed_zero :
      ∀ q : DecisionSpace d × DecisionSpace d,
        ∫ ξ, stochasticGradient S q.1 ξ - objectiveGradient S q.1
          ∂Measure.map (S.sample (t + 1)) μ = 0) :
    ∫ ω,
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω) ∂μ = 0 := by
  let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
    (iterate S (t + 1) ω,
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let φ : DecisionSpace d × DecisionSpace d → Sample → ℝ := fun q ξ =>
    inner ℝ q.2 (stochasticGradient S q.1 ξ - objectiveGradient S q.1)
  have hfixed_scalar_zero :
      ∀ q : DecisionSpace d × DecisionSpace d,
        ∫ ξ, φ q ξ ∂Measure.map sample μ = 0 := by
    intro q
    have hzero :=
      inner_integral_oracle_residual_eq_zero_of_integral_eq_zero
        (μ := Measure.map sample μ) (G := stochasticGradient S)
        (target := objectiveGradient S) q.1 q.2
        (by simpa [sample] using hfixed_int q)
        (by simpa [sample] using hfixed_zero q)
    simpa [φ, real_inner_comm] using hzero
  have hzero :=
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := μ) (ν := Measure.map sample μ) (φ := φ) (X := query) (Y := sample)
      (by simpa [query, sample, φ] using hscalar_prod)
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample] using hindep)
      rfl
      (by simpa [query, sample, φ, real_inner_comm] using hinner_int)
      hfixed_scalar_zero
  calc
    ∫ ω,
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω) ∂μ
        = ∫ ω, φ (query ω) (sample ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simp [query, sample, φ, real_inner_comm]
    _ = 0 := hzero

/-- Second Lemma 3 totalized cross-term cancellation using only scalar
regularity under the sampled product law.

This is the paired-gradient analogue of
`lemma3_first_cross_term_integral_eq_zero_of_sampled_product`: the fixed-fiber
mean-zero residual identities at both endpoints make the fixed scalar paired
difference integrate to zero, and independence transfers that cancellation to
the adapted random query. -/
private theorem lemma3_second_cross_term_integral_eq_zero_of_sampled_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hquery :
      AEMeasurable
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hscalar_prod :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          inner ℝ p.1.2
            ((stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1) -
              (stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)))
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)))
    (hinner_int :
      Integrable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω) +
              objectiveGradient S (iterate S t ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hfixed_int :
      ∀ x : DecisionSpace d,
        Integrable
          (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
          (Measure.map (S.sample (t + 1)) μ))
    (hfixed_zero :
      ∀ x : DecisionSpace d,
        ∫ ξ, stochasticGradient S x ξ - objectiveGradient S x
          ∂Measure.map (S.sample (t + 1)) μ = 0) :
    ∫ ω,
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω) ∂μ = 0 := by
  let query : Ω → (DecisionSpace d × DecisionSpace d) × DecisionSpace d := fun ω =>
    ((iterate S (t + 1) ω, iterate S t ω),
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let φ : (DecisionSpace d × DecisionSpace d) × DecisionSpace d → Sample → ℝ :=
    fun q ξ =>
      inner ℝ q.2
        ((stochasticGradient S q.1.1 ξ - objectiveGradient S q.1.1) -
          (stochasticGradient S q.1.2 ξ - objectiveGradient S q.1.2))
  have hfixed_scalar_zero :
      ∀ q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d,
        ∫ ξ, φ q ξ ∂Measure.map sample μ = 0 := by
    intro q
    have hx_int : Integrable
        (fun ξ => stochasticGradient S q.1.1 ξ - objectiveGradient S q.1.1)
        (Measure.map sample μ) := by
      simpa [sample] using hfixed_int q.1.1
    have hy_int : Integrable
        (fun ξ => stochasticGradient S q.1.2 ξ - objectiveGradient S q.1.2)
        (Measure.map sample μ) := by
      simpa [sample] using hfixed_int q.1.2
    have hx_zero :
        ∫ ξ, stochasticGradient S q.1.1 ξ - objectiveGradient S q.1.1
          ∂Measure.map sample μ = 0 := by
      simpa [sample] using hfixed_zero q.1.1
    have hy_zero :
        ∫ ξ, stochasticGradient S q.1.2 ξ - objectiveGradient S q.1.2
          ∂Measure.map sample μ = 0 := by
      simpa [sample] using hfixed_zero q.1.2
    have hx_scalar_zero :=
      inner_integral_oracle_residual_eq_zero_of_integral_eq_zero
        (μ := Measure.map sample μ) (G := stochasticGradient S)
        (target := objectiveGradient S) q.1.1 q.2 hx_int hx_zero
    have hy_scalar_zero :=
      inner_integral_oracle_residual_eq_zero_of_integral_eq_zero
        (μ := Measure.map sample μ) (G := stochasticGradient S)
        (target := objectiveGradient S) q.1.2 q.2 hy_int hy_zero
    have hx_scalar_int :
        Integrable
          (fun ξ => inner ℝ q.2
            (stochasticGradient S q.1.1 ξ - objectiveGradient S q.1.1))
          (Measure.map sample μ) :=
      (ContinuousLinearMap.integrable_comp (L := (innerSL ℝ) q.2) hx_int)
    have hy_scalar_int :
        Integrable
          (fun ξ => inner ℝ q.2
            (stochasticGradient S q.1.2 ξ - objectiveGradient S q.1.2))
          (Measure.map sample μ) :=
      (ContinuousLinearMap.integrable_comp (L := (innerSL ℝ) q.2) hy_int)
    calc
      ∫ ξ, φ q ξ ∂Measure.map sample μ
          = ∫ ξ,
              inner ℝ q.2
                (stochasticGradient S q.1.1 ξ - objectiveGradient S q.1.1) -
              inner ℝ q.2
                (stochasticGradient S q.1.2 ξ - objectiveGradient S q.1.2)
              ∂Measure.map sample μ := by
            apply integral_congr_ae
            filter_upwards with ξ
            simp [φ, inner_sub_right]
      _ = (∫ ξ,
              inner ℝ q.2
                (stochasticGradient S q.1.1 ξ - objectiveGradient S q.1.1)
              ∂Measure.map sample μ) -
            ∫ ξ,
              inner ℝ q.2
                (stochasticGradient S q.1.2 ξ - objectiveGradient S q.1.2)
              ∂Measure.map sample μ := by
            exact integral_sub hx_scalar_int hy_scalar_int
      _ = 0 := by
            rw [hx_scalar_zero, hy_scalar_zero]
            norm_num
  have hzero :=
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := μ) (ν := Measure.map sample μ) (φ := φ) (X := query) (Y := sample)
      (by simpa [query, sample, φ] using hscalar_prod)
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample] using hindep)
      rfl
      (by
        simpa [query, sample, φ, real_inner_comm, inner_sub_right, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hinner_int)
      hfixed_scalar_zero
  calc
    ∫ ω,
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω) ∂μ
        = ∫ ω, φ (query ω) (sample ω) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simp [query, sample, φ, real_inner_comm, sub_eq_add_neg, add_assoc,
            add_comm, add_left_comm]
    _ = 0 := hzero

/-- First Lemma 3 totalized cross-term integrability, specialized to the STORM
expression, from the random-query residual and multiplier L2 side conditions. -/
private theorem lemma3_first_cross_term_integrable_of_l2_premises
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hquery : Measurable (iterate S (t + 1)))
    (hsample : Measurable (S.sample (t + 1)))
    (hres_meas :
      Measurable
        (fun p : DecisionSpace d × Sample =>
          stochasticGradient S p.1 p.2 - objectiveGradient S p.1))
    (hmult_meas :
      AEStronglyMeasurable
        (fun ω =>
          ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω) μ)
    (hres_sq :
      Integrable
        (fun ω =>
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2) μ)
    (hmult_sq :
      Integrable
        (fun ω =>
          ‖((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω‖ ^ 2) μ) :
    Integrable
      (fun ω =>
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  exact
    integrable_oracle_residual_inner_of_l2_multiplier
      (P := μ) (query := iterate S (t + 1)) (sample := S.sample (t + 1))
      (G := stochasticGradient S) (target := objectiveGradient S)
      (multiplier := fun ω =>
        ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
      hquery hsample hres_meas hmult_meas hres_sq hmult_sq

/-- Residual-kernel measurability consumed by Lemma 3's oracle cancellation
when the stochastic oracle and objective-gradient selectors are already regular.
The current Section 3 record alone does not imply this full off-stream kernel
regularity; see the private counterexample above. -/
private theorem lemma3_first_residual_kernel_measurable_of_regular_oracle
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (hres_meas :
      Measurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)) :
    Measurable
      (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
        stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1) :=
  hres_meas

/-- Promotion from the strict sample-prefix sigma algebra to the ambient
measurable space. -/
private theorem section3_prefix_measurable_to_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace β]
    (S : Setup Ω Sample E) {L G σ fStar : ℝ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hsec3 : Section3Assumptions S μ L G σ fStar) {N : ℕ} {wt : Ω → β}
    (hwt :
      Measurable[(⨆ j < N, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))] wt) :
    Measurable wt := by
  exact hwt.mono (iSup₂_le fun j _hj => (hsec3.sample_measurable j).comap_le) le_rfl

/-- Compiled consumer for the generic SOptLib recursive-prefix theorem.

This deliberately exposes the exact obstruction in the full-state route: one
would have to prove measurability of the off-stream state/sample transition
`stateStepFromSample`, whose direction and gradient-norm coordinates contain
random-query stochastic gradients.  The Lemma 3 proof below therefore uses
coordinate-level pre-fresh-sample packaging instead of claiming this premise
from Section 3. -/
private theorem stateProcess_prefix_measurable_of_stateStepFromSample_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (N n : ℕ) (hn : n ≤ N)
    (h_init :
      Measurable[(⨆ j < N + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))]
        (stateProcess S 0))
    (h_step :
      ∀ j, j + 1 ≤ N →
        Measurable (fun p : State (DecisionSpace d) × Sample =>
          stateStepFromSample S j p.1 p.2)) :
    Measurable[(⨆ j < N + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))]
      (stateProcess S n) := by
  classical
  let past : ℕ → MeasurableSpace Ω := fun N =>
    ⨆ j < N, MeasurableSpace.comap (S.sample j)
      (by infer_instance : MeasurableSpace Sample)
  have hpast_mono : ∀ {a b : ℕ}, a ≤ b → past a ≤ past b := by
    intro a b hab
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (lt_of_lt_of_le hj hab) le_rfl)
  exact
    SOptLib.recursive_process_measurable_wrt_sample_prefix
      (past := past)
      (process := stateProcess S)
      (driver := fun j ω => S.sample (j + 1) ω)
      (step := fun j prev ξ => stateStepFromSample S j prev ξ)
      N n hpast_mono h_init
      (by
        intro j _hj
        exact Measurable.of_comap_le
          (le_iSup_of_le (j + 1) (le_iSup_of_le (by omega) le_rfl)))
      h_step
      (by
        intro j _hj
        funext ω
        simp [stateProcess, stateStep, stateStepFromSample])
      hn

private theorem lemma3_adaptiveStepsize_measurable
    (S : Setup Ω Sample E) :
    Measurable (fun sumSq : ℝ => adaptiveStepsize S sumSq) := by
  have hrpow :
      Measurable
        (fun sumSq : ℝ =>
          Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) := by
    exact
      (Real.continuous_rpow_const
        (by norm_num : 0 ≤ ((1 : ℝ) / 3))).measurable.comp
        (measurable_const.add measurable_id)
  exact measurable_const.div hrpow

private theorem lemma3_one_sub_momentumWeight_of_sumSq_measurable
    (S : Setup Ω Sample E) :
    Measurable
      (fun sumSq : ℝ =>
        1 - momentumWeight S (adaptiveStepsize S sumSq)) := by
  have hη := lemma3_adaptiveStepsize_measurable S
  have hηsq :
      Measurable (fun sumSq : ℝ => adaptiveStepsize S sumSq ^ 2) := by
    convert hη.mul hη using 1
    ext sumSq
    ring
  simpa [momentumWeight] using measurable_const.sub (measurable_const.mul hηsq)

/-- A.e. Carathéodory product regularity from fixed sample-law fibers.

This is the law-scoped variant needed by Lemma 3.  It avoids a global
off-stream stochastic-gradient kernel: fixed fibers are only required to be
a.e.-strongly measurable under the sample law, while continuity in the query
variable is required only sample-law almost surely. -/
private theorem sampled_product_aestronglyMeasurable_of_continuous_ae_of_fiber
    {ι Sample Q V : Type*}
    [PseudoMetricSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    [SecondCountableTopology ι]
    [MeasurableSpace Sample] [MeasurableSpace Q]
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (νQ : Measure Q) (νSample : Measure Sample) [SFinite νSample]
    (kernel : ι → Sample → V) (queryPoint : Q → ι)
    (hqueryPoint : Measurable queryPoint)
    (hcontinuous_ae : ∀ᵐ ξ ∂νSample, Continuous fun x : ι => kernel x ξ)
    (hfiber_aesm : ∀ x : ι, AEStronglyMeasurable (kernel x) νSample) :
    AEStronglyMeasurable
      (fun p : Q × Sample => kernel (queryPoint p.1) p.2)
      (νQ.prod νSample) := by
  exact aestronglyMeasurable_prod_of_continuous_ae_of_fiber νQ νSample kernel queryPoint
    hqueryPoint.stronglyMeasurable hcontinuous_ae hfiber_aesm

/-- Transfer the source a.e. residual continuity along the sample stream to the
pushed-forward sample-coordinate law.

This is the exact remaining law-scoped continuity supplier for the product
Carathéodory route.  It is intentionally narrower than global off-stream
continuity or joint stochastic-gradient measurability. -/
private theorem section3_sample_law_gradient_residual_continuous_ae
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ}
    (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (n : ℕ) :
    ∀ᵐ ξ ∂Measure.map (S.sample n) μ,
      Continuous fun x : DecisionSpace d =>
        stochasticGradient S x ξ - objectiveGradient S x := by
  have hobj : Continuous (objectiveGradient S) :=
    section3_objectiveGradient_continuous S μ hsec3 n
  filter_upwards [hsec3.L_smooth_sample_law n] with ξ hsmooth
  have hLip :
      LipschitzWith (Real.toNNReal L)
        (fun x : DecisionSpace d => stochasticGradient S x ξ) := by
    refine lipschitzWith_of_norm_sub_le_mul
      (fun x : DecisionSpace d => stochasticGradient S x ξ) L ?_
    intro x y
    rw [dist_eq_norm]
    exact hsmooth x y
  exact hLip.continuous.sub hobj

/-- Source-scale product-law regularity bridge for the centered stochastic
gradient residual at a random query.

The source assumptions give fixed-query sample-law residual regularity and
a.e. smoothness of sampled losses.  The missing theorem is the standard
Carathéodory measurability step turning those fixed fibers plus a measurable
query projection into a residual random variable under the exact product law
used for conditioning.  Keeping this bridge product-law-scoped avoids the
previously rejected full off-stream joint-kernel assumption. -/
private theorem section3_sampled_product_residual_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} {Q : Type*} [MeasurableSpace Q]
    (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (n : ℕ) (νQ : Measure Q) (queryPoint : Q → DecisionSpace d)
    (hqueryPoint : Measurable queryPoint) :
    AEStronglyMeasurable
      (fun p : Q × Sample =>
        stochasticGradient S (queryPoint p.1) p.2 -
          objectiveGradient S (queryPoint p.1))
      (νQ.prod (Measure.map (S.sample n) μ)) := by
  have hfixed_aesm :
      ∀ x : DecisionSpace d,
        AEStronglyMeasurable
          (fun ξ =>
            stochasticGradient S x ξ -
              objectiveGradient S x)
          (Measure.map (S.sample n) μ) := by
    intro x
    exact section3_sample_law_gradient_residual_aestronglyMeasurable
      S μ hsec3 n x
  have hcontinuous_sample_law :
      ∀ᵐ ξ ∂Measure.map (S.sample n) μ,
        Continuous fun x : DecisionSpace d =>
          stochasticGradient S x ξ - objectiveGradient S x :=
    section3_sample_law_gradient_residual_continuous_ae S μ hsec3 n
  exact
    sampled_product_aestronglyMeasurable_of_continuous_ae_of_fiber
      (νQ := νQ) (νSample := Measure.map (S.sample n) μ)
      (kernel := fun x ξ =>
        stochasticGradient S x ξ - objectiveGradient S x)
      (queryPoint := queryPoint)
      hqueryPoint hcontinuous_sample_law hfixed_aesm

/-- Pull a law-scoped product residual representative back to the sample prefix
that contains the adapted query and the fresh sample.

This is the source-scale bridge needed by the generated-history induction:
it consumes a prefix-a.e. representative for the query, obtains product-law
regularity from `section3_sampled_product_residual_aestronglyMeasurable`, and
then composes the product representative with the measurable query
representative and the sample coordinate.  No global off-stream oracle-kernel
measurability is used. -/
private theorem section3_random_query_residual_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    {query : Ω → DecisionSpace d} {n i : ℕ}
    (hquery :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < n, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        query μ)
    (hni : n ≤ i) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < i + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        stochasticGradient S (query ω) (S.sample i ω) -
          objectiveGradient S (query ω)) μ := by
  classical
  rcases hquery with ⟨queryRep, hqueryRep, hquery_ae⟩
  have hindep : ProbabilityTheory.IndepFun queryRep (S.sample i) μ :=
    section3_indepFun_sample_prefixAEMeasurable_future S μ hsec3
      (hwt := ⟨queryRep, hqueryRep, Filter.EventuallyEq.rfl⟩) hni
  have hkernel :
      AEStronglyMeasurable
        (Function.uncurry fun x ξ =>
          stochasticGradient S x ξ - objectiveGradient S x)
        ((Measure.map queryRep μ).prod (Measure.map (S.sample i) μ)) := by
    exact section3_sampled_product_residual_aestronglyMeasurable S μ hsec3 i
      (Measure.map queryRep μ) (fun x : DecisionSpace d => x) measurable_id
  let mAmbient : MeasurableSpace Ω := by infer_instance
  have hsample_ambient (j : ℕ) :
      @Measurable Ω Sample mAmbient _ (S.sample j) :=
    hsec3.sample_measurable j
  let mTarget : MeasurableSpace Ω :=
    ⨆ j < i + 1, MeasurableSpace.comap (S.sample j)
      (by infer_instance : MeasurableSpace Sample)
  have hsource_target :
      (⨆ j < n, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample)) ≤ mTarget :=
    iSup₂_le fun j hj => le_iSup_of_le j
      (le_iSup_of_le (Nat.lt_succ_of_lt (lt_of_lt_of_le hj hni)) le_rfl)
  have htarget_ambient : mTarget ≤ mAmbient :=
    iSup₂_le fun j _hj =>
      @Measurable.comap_le Ω Sample mAmbient _ (S.sample j) (hsample_ambient j)
  have hqueryRep_target : @Measurable Ω (DecisionSpace d) mTarget _ queryRep :=
    hqueryRep.mono hsource_target le_rfl
  have hsample_target : @Measurable Ω Sample mTarget _ (S.sample i) :=
    Measurable.of_comap_le
      (le_iSup_of_le i (le_iSup_of_le (Nat.lt_succ_self i) le_rfl))
  rcases ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
    (mΩ := mAmbient) (mTarget := mTarget)
    (query := query) (queryRep := queryRep)
    (sample := S.sample i)
    (kernel := fun x ξ => stochasticGradient S x ξ - objectiveGradient S x)
    (μ := μ)
    (by infer_instance) (by infer_instance)
    htarget_ambient hqueryRep_target hsample_target
    hquery_ae hindep hkernel with ⟨resultRep, hresultRep, hresult_ae⟩
  change ∃ resultRep : Ω → DecisionSpace d,
    @Measurable Ω (DecisionSpace d) mTarget _ resultRep ∧
      (fun ω => stochasticGradient S (query ω) (S.sample i ω) -
        objectiveGradient S (query ω)) =ᵐ[μ] resultRep
  exact ⟨resultRep, hresultRep.measurable, hresult_ae⟩

/-- Generated-history adaptedness at the exact prefix used in Lemma 3.

At paper time `t`, `x_t`, `x_{t+1}`, `d_t`, and the cumulative gradient norm
sum defining `η_t` are functions of `ξ_1, ..., ξ_t`.  The successor case uses
`section3_random_query_residual_prefixAEMeasurable` for the two stochastic
gradient calls with the next sample, instead of the tombstoned off-stream
transition-measurability route. -/
private theorem lemma3_generated_history_prefixAEMeasurable_early
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ ∧
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ ∧
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (direction S t) μ ∧
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ := by
  classical
  have hgen := by
    refine
      SOptLib.recursive_momentum_process_prefix_aestronglyMeasurable
        (μ := μ) (sample := S.sample) (hsample := hsec3.sample_measurable)
        (oracle := stochasticGradient S) (x0 := S.x₁)
        (stepSize := adaptiveStepsize S) (momentumWeight := momentumWeight S)
        (lemma3_adaptiveStepsize_measurable S) ?_ ?_ t
    · have hsq : Measurable fun η : ℝ => η ^ 2 := by
        simpa [pow_two] using
          (measurable_id.mul measurable_id : Measurable fun η : ℝ => η * η)
      simpa [momentumWeight] using measurable_const.mul hsq
    · intro n query hquery
      have hqueryPrefix :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (⨆ j < n, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          query μ := by
        simpa [SOptLib.filtration_seq] using
          (prefixAEMeasurable_of_aestronglyMeasurable hquery)
      have hres :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (⨆ j < n + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          (fun ω =>
            stochasticGradient S (query ω) (S.sample n ω) -
              objectiveGradient S (query ω)) μ := by
        exact
          section3_random_query_residual_prefixAEMeasurable
            S μ hsec3 (query := query) (n := n) (i := n)
            hqueryPrefix (Nat.le_refl n)
      have hquery' :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (⨆ j < n + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          query μ := by
        rcases hqueryPrefix with ⟨queryRep, hqueryRep, hquery_ae⟩
        exact ⟨queryRep,
          hqueryRep.mono
            ((SOptLib.filtration S.sample hsec3.sample_measurable).mono (Nat.le_succ n))
            le_rfl,
          hquery_ae⟩
      have hobj :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (⨆ j < n + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          (fun ω => objectiveGradient S (query ω)) μ :=
        hquery'.comp_measurable
          (section3_objectiveGradient_continuous S μ hsec3 n).measurable
      have horaclePrefix :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (⨆ j < n + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          (fun ω => stochasticGradient S (query ω) (S.sample n ω)) μ :=
        (hres.add hobj).congr (by
          filter_upwards with ω
          simp)
      rcases horaclePrefix with ⟨oracleRep, horacleRep, horacle_ae⟩
      refine ⟨oracleRep, ?_, ?_⟩
      · exact horacleRep.stronglyMeasurable
      · simpa [SOptLib.filtration_seq] using horacle_ae
  exact ⟨
    by
      simpa [SOptLib.filtration_seq, stateProcess, initialState, stateStep,
        stateStepFromSample, iterate] using
          (prefixAEMeasurable_of_aestronglyMeasurable hgen.1),
    by
      simpa [SOptLib.filtration_seq, stateProcess, initialState, stateStep,
        stateStepFromSample, iterate] using
          (prefixAEMeasurable_of_aestronglyMeasurable hgen.2.1),
    by
      simpa [SOptLib.filtration_seq, stateProcess, initialState, stateStep,
        stateStepFromSample, direction] using
          (prefixAEMeasurable_of_aestronglyMeasurable hgen.2.2.1),
    by
      simpa [SOptLib.filtration_seq, stateProcess, initialState, stateStep,
        stateStepFromSample, cumulativeGradientNormSq] using
          (prefixAEMeasurable_of_aestronglyMeasurable hgen.2.2.2)⟩

/-- Source-shaped a.e.-prefix adaptedness leaf for the pre-fresh-sample iterate
`x_{t+1}` used in Lemma 3.

This is the direct law-level replacement for the old exact-prefix coordinate
route: it is proved from Algorithm 1 generated-history semantics and the
sample-product regularity interface, not from full off-stream transition
measurability. -/
private theorem lemma3_iterate_succ_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (iterate S (t + 1)) μ := by
  exact (lemma3_generated_history_prefixAEMeasurable_early S μ hsec3 t).2.1

/-- Source-shaped a.e.-prefix adaptedness leaf for the current iterate `x_t`
under the prefix available before `ξ_{t+1}`. -/
private theorem lemma3_iterate_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (iterate S t) μ := by
  cases t with
  | zero =>
      refine ⟨fun _ω : Ω => S.x₁, ?_, Filter.EventuallyEq.rfl⟩
      exact measurable_const
  | succ t =>
      exact
        (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t).mono
          (iSup₂_le fun j hj =>
            le_iSup_of_le j (le_iSup_of_le (Nat.lt_succ_of_lt hj) le_rfl))

/-- Source-shaped a.e.-prefix adaptedness leaf for the generated cumulative
sampled-gradient square sum before the fresh sample `ξ_{t+1}`.

This is the smaller generated-history fact actually needed by the scalar
multiplier.  It should be proved by induction on the canonical STORM state
recursion, using the fixed-query sampled-gradient prefix bridge at
initialization and the law-scoped random-query sampled-gradient bridge at
successor steps. -/
private theorem lemma3_cumulativeGradientNormSq_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (cumulativeGradientNormSq S t) μ := by
  exact (lemma3_generated_history_prefixAEMeasurable_early S μ hsec3 t).2.2.2

/-- Measurability of the real scalar transformation turning the generated
cumulative gradient-norm square sum into Lemma 3's multiplier
`η_t^{-1}(1-a_{t+1})²`. -/
private theorem lemma3_scalar_multiplier_of_sumSq_measurable
    (S : Setup Ω Sample E) :
    Measurable
      (fun sumSq : ℝ =>
        (1 / adaptiveStepsize S sumSq) *
          (1 - momentumWeight S (adaptiveStepsize S sumSq)) ^ 2) := by
  have hrpow :
      Measurable
        (fun sumSq : ℝ =>
          Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) := by
    exact
      (Real.continuous_rpow_const
        (by norm_num : 0 ≤ ((1 : ℝ) / 3))).measurable.comp
        (measurable_const.add measurable_id)
  have hη :
      Measurable
        (fun sumSq : ℝ =>
          S.k / Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) := by
    exact measurable_const.div hrpow
  have hηsq :
      Measurable
        (fun sumSq : ℝ =>
          (S.k / Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) ^ 2) := by
    convert hη.mul hη using 1
    ext sumSq
    ring
  have ha :
      Measurable
        (fun sumSq : ℝ =>
          1 - S.c *
            (S.k / Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) ^ 2) :=
    measurable_const.sub (measurable_const.mul hηsq)
  have hasq :
      Measurable
        (fun sumSq : ℝ =>
          (1 - S.c *
            (S.k / Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) ^ 2) ^ 2) := by
    convert ha.mul ha using 1
    ext sumSq
    ring
  have hηinv :
      Measurable
        (fun sumSq : ℝ =>
          Real.rpow (S.w + sumSq) ((1 : ℝ) / 3) / S.k) :=
    hrpow.div_const S.k
  simpa [adaptiveStepsize, stepsizeDenominator, stepsizeBase, momentumWeight]
    using hηinv.mul hasq

/-- Source-shaped a.e.-prefix adaptedness leaf for Lemma 3's scalar multiplier
`η_t^{-1}(1-a_{t+1})²`. -/
private theorem lemma3_scalar_multiplier_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω => (1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) μ := by
  have hsum :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ :=
    lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ _hsec3 t
  refine
    (hsum.comp_measurable
      (lemma3_scalar_multiplier_of_sumSq_measurable S)).congr ?_
  filter_upwards with ω
  rfl

/-- Source-shaped a.e.-prefix adaptedness leaf for the generated error
`ε_t = d_t - ∇F(x_t)`. -/
private theorem lemma3_error_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (error S t) μ := by
  have hgen := lemma3_generated_history_prefixAEMeasurable_early S μ hsec3 t
  have hobj :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S t ω)) μ :=
    hgen.1.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 t).measurable
  exact (hgen.2.2.1.sub hobj).congr (by
    filter_upwards with ω
    rfl)

/-- Iteration-18 same-head attempt for the remaining generated-history
adaptedness leaf `x_{t+1}`.

The compiled prefix monotonicity and the closed `x_t` leaf below show that the
only nontrivial case is the successor construction of the generated STORM
state before reading the fresh sample.  That construction still needs a
law-scoped random-query oracle regularity theorem for the sampled gradients in
`stateStepFromSample`; adding full off-stream joint measurability here would
reactivate the rejected route. -/
private theorem _voucher_attempt_lemma3_iterate_succ_prefixAEMeasurable_18
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (iterate S (t + 1)) μ := by
  classical
  have hprev :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    lemma3_iterate_prefixAEMeasurable S μ hsec3 t
  have hsample0 : Measurable (S.sample 0) :=
    hsec3.sample_measurable 0
  have hfixed0 :
      AEStronglyMeasurable
        (fun ξ => stochasticGradient S S.x₁ ξ - objectiveGradient S S.x₁)
        (Measure.map (S.sample 0) μ) :=
    section3_sample_law_gradient_residual_aestronglyMeasurable S μ hsec3 0 S.x₁
  have hinit_gradient_prefix0 :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (MeasurableSpace.comap (S.sample 0) (by infer_instance : MeasurableSpace Sample))
        (fun ω => stochasticGradient S S.x₁ (S.sample 0 ω)) μ :=
    section3_sampled_gradient_prefixAEMeasurable S μ hsec3 0 S.x₁
  have hinit_direction_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (direction S 0) μ := by
    have hdir0 :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (MeasurableSpace.comap (S.sample 0)
            (by infer_instance : MeasurableSpace Sample))
          (direction S 0) μ :=
      hinit_gradient_prefix0.congr (by
        filter_upwards with ω
        simp [direction, stateProcess, initialState])
    exact hdir0.mono
      (le_iSup_of_le 0 (le_iSup_of_le (Nat.succ_pos t) le_rfl))
  -- V3 remainder: construct an a.e.-prefix representative for the successor
  -- state update from the law-scoped sampled-gradient regularity above.
  have _ := hprev
  have _ := hsample0
  have _ := hfixed0
  have _ := hinit_direction_prefix
  exact lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t

/-- Iteration-18 same-head attempt for the scalar multiplier prefix leaf.

The scalar is generated from the cumulative gradient-norm square sum through
continuous real operations.  The remaining obstruction is therefore exactly the
prefix-a.e. measurability of that cumulative sum, which depends on the same
sampled-gradient regularity needed for the successor state. -/
private theorem _voucher_attempt_lemma3_scalar_multiplier_prefixAEMeasurable_18
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω => (1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) μ := by
  classical
  have hx :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    lemma3_iterate_prefixAEMeasurable S μ hsec3 t
  -- V3 remainder: prove prefix-a.e. measurability of
  -- `cumulativeGradientNormSq S t`, then close by measurable real algebra for
  -- `adaptiveStepsize`, `momentumWeight`, reciprocal, multiplication and pow.
  have _ := hx
  exact lemma3_scalar_multiplier_prefixAEMeasurable S μ hsec3 t

/-- Iteration-18 same-head attempt for generated-error prefix adaptedness.

The direction part follows the generated STORM recursion; the objective
gradient part additionally needs measurability of `∇F` at a prefix-measurable
iterate, derived from the source oracle/smoothness bridge rather than asserted
as a Section 3 field. -/
private theorem _voucher_attempt_lemma3_error_prefixAEMeasurable_18
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (error S t) μ := by
  classical
  have hx :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    lemma3_iterate_prefixAEMeasurable S μ hsec3 t
  have hcenter :
      ∀ x : DecisionSpace d,
        Integrable
            (fun ξ => stochasticGradient S x ξ - objectiveGradient S x)
            (Measure.map (S.sample t) μ) ∧
          ∫ ξ, stochasticGradient S x ξ - objectiveGradient S x
            ∂Measure.map (S.sample t) μ = 0 := by
    intro x
    exact section3_fixed_gradient_residual_mean_zero_under_sample_law S μ hsec3 t x
  -- V3 remainder: combine generated-direction prefix adaptedness with the
  -- source-derived objective-gradient measurability at `iterate S t`.
  have _ := hx
  have _ := hcenter
  exact lemma3_error_prefixAEMeasurable S μ hsec3 t

/-- A.e.-prefix coordinate packaging for Lemma 3's first adapted random query.

This consumes law-level coordinate representatives directly and therefore does
not depend on the obsolete exact-prefix route. -/
private theorem lemma3_first_query_multiplier_prefixAEMeasurable_of_coordinates
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d)) (μ : Measure Ω) (t : ℕ)
    (hxNext :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ)
    (hscalar :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => (1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) μ)
    (herror :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (error S t) μ) :
    @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        (iterate S (t + 1) ω,
          ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  exact hxNext.prod (hscalar.real_smul herror)

/-- A.e.-prefix coordinate packaging for Lemma 3's paired adapted random
query. -/
private theorem lemma3_second_query_multiplier_prefixAEMeasurable_of_coordinates
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d)) (μ : Measure Ω) (t : ℕ)
    (hxNext :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ)
    (hx :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ)
    (hscalar :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => (1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) μ)
    (herror :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (error S t) μ) :
    @prefixAEMeasurable Ω ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        ((iterate S (t + 1) ω, iterate S t ω),
          ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  exact (hxNext.prod hx).prod (hscalar.real_smul herror)

/-- First Lemma 3 query/multiplier package at the law-level regularity needed
for conditioning.  It is deliberately private and does not add adaptedness to
the source Section 3 record. -/
private theorem lemma3_first_query_multiplier_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        (iterate S (t + 1) ω,
          ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  exact
    lemma3_first_query_multiplier_prefixAEMeasurable_of_coordinates S μ t
      (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t)
      (lemma3_scalar_multiplier_prefixAEMeasurable S μ hsec3 t)
      (lemma3_error_prefixAEMeasurable S μ hsec3 t)

/-- Paired Lemma 3 query/multiplier package at the law-level regularity needed
for conditioning. -/
private theorem lemma3_second_query_multiplier_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        ((iterate S (t + 1) ω, iterate S t ω),
          ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  exact
    lemma3_second_query_multiplier_prefixAEMeasurable_of_coordinates S μ t
      (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t)
      (lemma3_iterate_prefixAEMeasurable S μ hsec3 t)
      (lemma3_scalar_multiplier_prefixAEMeasurable S μ hsec3 t)
      (lemma3_error_prefixAEMeasurable S μ hsec3 t)

/-- Fixed-fiber second-moment facts for a measured query projection under the
fresh sample-coordinate law.

This is the part of the product-law residual route that is already supplied by
the Section 3 gradient-noise bound.  The remaining product-law leaf below is
therefore only the Carathéodory/random-parameter measurability step, not the
variance transport. -/
private theorem section3_sampled_product_residual_fixed_variance_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} {Q : Type*} [MeasurableSpace Q]
    (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (n : ℕ) (queryPoint : Q → DecisionSpace d) :
    ∀ q : Q,
      Integrable
          (fun ξ =>
            ‖stochasticGradient S (queryPoint q) ξ -
              objectiveGradient S (queryPoint q)‖ ^ 2)
          (Measure.map (S.sample n) μ) ∧
        ∫ ξ,
            ‖stochasticGradient S (queryPoint q) ξ -
              objectiveGradient S (queryPoint q)‖ ^ 2
          ∂Measure.map (S.sample n) μ ≤ σ ^ 2 := by
  intro q
  exact
    section3_sample_law_gradient_residual_sq_integrable_and_le
      S μ hsec3 n (queryPoint q)

/-- Carathéodory product-measurability bridge for a sampled residual kernel.

This is the exact Mathlib terminal API needed by the source-scale product-law
route: continuity in the query variable plus measurable sample fibers gives
measurability on the query/sample product, which is stronger than the
product-law a.e.-strong measurability consumed by Lemma 3. -/
private theorem sampled_product_residual_aestronglyMeasurable_of_caratheodory
    [MeasurableSpace Sample]
    {d : ℕ} {Q : Type*} [MeasurableSpace Q]
    (νQ : Measure Q) (νSample : Measure Sample)
    (residual : DecisionSpace d → Sample → DecisionSpace d)
    (queryPoint : Q → DecisionSpace d)
    (hqueryPoint : Measurable queryPoint)
    (hcontinuous : ∀ ξ : Sample, Continuous fun x : DecisionSpace d => residual x ξ)
    (hfiber_meas : ∀ x : DecisionSpace d, Measurable fun ξ : Sample => residual x ξ) :
    AEStronglyMeasurable
      (fun p : Q × Sample => residual (queryPoint p.1) p.2)
      (νQ.prod νSample) := by
  have huncurry :
      Measurable (Function.uncurry residual) :=
    MeasureTheory.measurable_uncurry_of_continuous_of_measurable
      hcontinuous hfiber_meas
  have hpair :
      Measurable (fun p : Q × Sample => (queryPoint p.1, p.2)) :=
    (hqueryPoint.comp measurable_fst).prod measurable_snd
  exact (huncurry.comp hpair).aestronglyMeasurable

/-- Exact map-law transport for the source-scale residual product route in the
special case where the actual query/sample pairing is a measurable embedding.

This is deliberately not a new Section 3 assumption.  It records the precise
Mathlib API boundary discovered by the source-route audit: base-law regularity
of `(q, ω) ↦ residual (queryPoint q) (ξ_n ω)` transports to the sampled product
law only through a map-measure equivalence/embedding argument, not from the
paper's fixed-fiber assumptions alone. -/
private theorem section3_sampled_product_residual_aestronglyMeasurable_of_base_product_embedding
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} {Q : Type*} [MeasurableSpace Q]
    (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (n : ℕ) (νQ : Measure Q) [SFinite νQ] (queryPoint : Q → DecisionSpace d)
    (hpair :
      MeasurableEmbedding
        (fun p : Q × Ω => (p.1, S.sample n p.2)))
    (hbase :
      AEStronglyMeasurable
        (fun p : Q × Ω =>
          stochasticGradient S (queryPoint p.1) (S.sample n p.2) -
            objectiveGradient S (queryPoint p.1))
        (νQ.prod μ)) :
    AEStronglyMeasurable
      (fun p : Q × Sample =>
        stochasticGradient S (queryPoint p.1) p.2 -
          objectiveGradient S (queryPoint p.1))
      (νQ.prod (Measure.map (S.sample n) μ)) := by
  let pair : Q × Ω → Q × Sample := fun p => (p.1, S.sample n p.2)
  let φ : Q × Sample → DecisionSpace d := fun p =>
    stochasticGradient S (queryPoint p.1) p.2 - objectiveGradient S (queryPoint p.1)
  have hmap :
      Measure.map pair (νQ.prod μ) =
        νQ.prod (Measure.map (S.sample n) μ) := by
    change Measure.map (Prod.map id (S.sample n)) (νQ.prod μ) =
      νQ.prod (Measure.map (S.sample n) μ)
    rw [← Measure.map_prod_map νQ μ measurable_id (hsec3.sample_measurable n)]
    simp
  have hφ_map : AEStronglyMeasurable φ (Measure.map pair (νQ.prod μ)) := by
    exact
      (show MeasurableEmbedding pair from hpair).aestronglyMeasurable_map_iff.2
        (by simpa [pair, φ] using hbase)
  simpa [hmap, φ] using hφ_map

/-- First Lemma 3 query/multiplier package supplied by the generated-history
induction that consumes the law-scoped random-query residual bridge. -/
private theorem lemma3_first_query_multiplier_prefixAEMeasurable_via_generated_history
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        (iterate S (t + 1) ω,
          ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  have hgen := lemma3_generated_history_prefixAEMeasurable_early S μ hsec3 t
  have hscalar :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => (1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) μ := by
    refine
      (hgen.2.2.2.comp_measurable
        (lemma3_scalar_multiplier_of_sumSq_measurable S)).congr ?_
    filter_upwards with ω
    rfl
  have hobj :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S t ω)) μ :=
    hgen.1.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 t).measurable
  have herr :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (error S t) μ :=
    (hgen.2.2.1.sub hobj).congr (by
      filter_upwards with ω
      rfl)
  exact
    lemma3_first_query_multiplier_prefixAEMeasurable_of_coordinates S μ t
      hgen.2.1 hscalar herr

/-- Paired Lemma 3 query/multiplier package supplied by the generated-history
induction that consumes the law-scoped random-query residual bridge. -/
private theorem lemma3_second_query_multiplier_prefixAEMeasurable_via_generated_history
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        ((iterate S (t + 1) ω, iterate S t ω),
          ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  have hgen := lemma3_generated_history_prefixAEMeasurable_early S μ hsec3 t
  have hscalar :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => (1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) μ := by
    refine
      (hgen.2.2.2.comp_measurable
        (lemma3_scalar_multiplier_of_sumSq_measurable S)).congr ?_
    filter_upwards with ω
    rfl
  have hobj :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S t ω)) μ :=
    hgen.1.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 t).measurable
  have herr :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (error S t) μ :=
    (hgen.2.2.1.sub hobj).congr (by
      filter_upwards with ω
      rfl)
  exact
    lemma3_second_query_multiplier_prefixAEMeasurable_of_coordinates S μ t
      hgen.2.1 hgen.1 hscalar herr

/-- Iteration-18 same-head attempt for the source-scale product residual
regularity bridge.

This expands the bridge to the exact data already supplied by the Section 3
record: fixed-fiber sampled-law a.e. strong measurability and fixed-fiber
second-moment bounds.  The final remaining leaf is the missing
measurable-parameter/product-measure theorem that turns those source-law fibers
and a measurable query projection into a product-law residual representative. -/
private theorem _voucher_attempt_section3_sampled_product_residual_aestronglyMeasurable_18
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} {Q : Type*} [MeasurableSpace Q]
    (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (n : ℕ) (νQ : Measure Q) (queryPoint : Q → DecisionSpace d)
    (hqueryPoint : Measurable queryPoint) :
    AEStronglyMeasurable
      (fun p : Q × Sample =>
        stochasticGradient S (queryPoint p.1) p.2 -
          objectiveGradient S (queryPoint p.1))
      (νQ.prod (Measure.map (S.sample n) μ)) := by
  exact section3_sampled_product_residual_aestronglyMeasurable
    S μ hsec3 n νQ queryPoint hqueryPoint

/-- Scalarization of the first Lemma 3 product-law residual by the generated
multiplier coordinate is a standard a.e.-strong-measurability closure. -/
private theorem lemma3_first_scalar_kernel_aestronglyMeasurable_of_residual_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hresidual_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ))) :
    AEStronglyMeasurable
      (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
        inner ℝ p.1.2
          (stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1))
      ((Measure.map
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) := by
  have hdir :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample => p.1.2)
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
    (measurable_snd.comp measurable_fst).aestronglyMeasurable
  simpa using hdir.inner hresidual_prod

/-- Scalarization of the paired Lemma 3 product-law residual is a standard
a.e.-strong-measurability closure from the two endpoint residual kernels. -/
private theorem lemma3_second_scalar_kernel_aestronglyMeasurable_of_residual_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hresidual_left :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1)
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)))
    (hresidual_right :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ))) :
    AEStronglyMeasurable
      (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
        inner ℝ p.1.2
          ((stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1) -
            (stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)))
      ((Measure.map
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) := by
  have hdir :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          p.1.2)
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
    (measurable_snd.comp measurable_fst).aestronglyMeasurable
  simpa using hdir.inner (hresidual_left.sub hresidual_right)

/-- First Lemma 3 scalar kernel is a.e. strongly measurable under the sampled
product law used by the conditioning argument. -/
private theorem lemma3_first_scalar_kernel_aestronglyMeasurable_sampled_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    AEStronglyMeasurable
      (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
        inner ℝ p.1.2
          (stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1))
      ((Measure.map
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) := by
  exact
    lemma3_first_scalar_kernel_aestronglyMeasurable_of_residual_product
      S μ t
      (section3_sampled_product_residual_aestronglyMeasurable
        S μ hsec3 (t + 1)
        (Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ)
        (fun q : DecisionSpace d × DecisionSpace d => q.1)
        measurable_fst)

/-- Second Lemma 3 paired scalar kernel is a.e. strongly measurable under the
sampled product law used by the conditioning argument. -/
private theorem lemma3_second_scalar_kernel_aestronglyMeasurable_sampled_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    AEStronglyMeasurable
      (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
        inner ℝ p.1.2
          ((stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1) -
            (stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)))
      ((Measure.map
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) := by
  exact
    lemma3_second_scalar_kernel_aestronglyMeasurable_of_residual_product
      S μ t
      (section3_sampled_product_residual_aestronglyMeasurable
        S μ hsec3 (t + 1)
        (Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ)
        (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.1)
        (measurable_fst.comp measurable_fst))
      (section3_sampled_product_residual_aestronglyMeasurable
        S μ hsec3 (t + 1)
        (Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ)
        (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.2)
        (measurable_snd.comp measurable_fst))

/-- Product-law a.e.-strong measurability transfers to the actual
random-query/sample composition once the query and sample are independent.

This is the source-scale bridge used by Lemma 3 after the active route moved
from exact prefix measurability to law-level prefix representatives. -/
private theorem aestronglyMeasurable_comp_of_indep_product_law
    {A B R : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace R] [TopologicalSpace R]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → A} {Y : Ω → B} {φ : A × B → R}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hindep : ProbabilityTheory.IndepFun X Y P)
    (hφ :
      AEStronglyMeasurable φ ((Measure.map X P).prod (Measure.map Y P))) :
    AEStronglyMeasurable (fun ω => φ (X ω, Y ω)) P := by
  exact _root_.aestronglyMeasurable_comp_of_indep_product_law hX hY
    (by infer_instance) (by infer_instance) hindep hφ

/-- First Lemma 3 scalar cross-term integrability from sampled-product scalar
regularity plus the exact scalar L2 leaf. -/
private theorem lemma3_first_cross_term_integrable_of_scalar_l2
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hquery :
      AEMeasurable
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hscalar_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          inner ℝ p.1.2
            (stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1))
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)))
    (hscalar_sq :
      Integrable
        (fun ω =>
          ‖inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)‖ ^ 2) μ) :
    Integrable
      (fun ω =>
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
    (iterate S (t + 1) ω,
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let φ : (DecisionSpace d × DecisionSpace d) × Sample → ℝ := fun p =>
    inner ℝ p.1.2
      (stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
  have h_joint : AEMeasurable (fun ω => (query ω, sample ω)) μ :=
    hquery.prodMk hsample.aemeasurable
  have h_prod_eq :
      Measure.map (fun ω => (query ω, sample ω)) μ =
        (Measure.map query μ).prod (Measure.map sample μ) := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hquery hsample.aemeasurable).mp (by simpa [query, sample] using hindep)
  have hφ_joint :
      AEStronglyMeasurable φ (Measure.map (fun ω => (query ω, sample ω)) μ) := by
    rw [h_prod_eq]
    simpa [query, sample, φ] using hscalar_prod
  have htarget_aesm :
      AEStronglyMeasurable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ := by
    simpa [query, sample, φ, real_inner_comm] using hφ_joint.comp_aemeasurable h_joint
  exact integrable_of_integrable_norm_sq (μ := μ) htarget_aesm hscalar_sq

/-- Paired Lemma 3 scalar cross-term integrability from sampled-product scalar
regularity plus the exact scalar L2 leaf. -/
private theorem lemma3_second_cross_term_integrable_of_scalar_l2
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : ℕ)
    (hquery :
      AEMeasurable
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hscalar_prod :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          inner ℝ p.1.2
            ((stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1) -
              (stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)))
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)))
    (hscalar_sq :
      Integrable
        (fun ω =>
          ‖inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω) +
              objectiveGradient S (iterate S t ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)‖ ^ 2) μ) :
    Integrable
      (fun ω =>
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  let query : Ω → (DecisionSpace d × DecisionSpace d) × DecisionSpace d := fun ω =>
    ((iterate S (t + 1) ω, iterate S t ω),
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let φ : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample → ℝ :=
    fun p =>
      inner ℝ p.1.2
        ((stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1) -
          (stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2))
  have h_joint : AEMeasurable (fun ω => (query ω, sample ω)) μ :=
    hquery.prodMk hsample.aemeasurable
  have h_prod_eq :
      Measure.map (fun ω => (query ω, sample ω)) μ =
        (Measure.map query μ).prod (Measure.map sample μ) := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hquery hsample.aemeasurable).mp (by simpa [query, sample] using hindep)
  have hφ_joint :
      AEStronglyMeasurable φ (Measure.map (fun ω => (query ω, sample ω)) μ) := by
    rw [h_prod_eq]
    simpa [query, sample, φ] using hscalar_prod
  have htarget_aesm :
      AEStronglyMeasurable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω) +
              objectiveGradient S (iterate S t ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ := by
    refine (hφ_joint.comp_aemeasurable h_joint).congr ?_
    filter_upwards with ω
    simp [query, sample, φ, real_inner_comm]
    abel
  exact integrable_of_integrable_norm_sq (μ := μ) htarget_aesm hscalar_sq

/-- Random-query residual square-integrability for Lemma 3 from the
law-scoped product residual regularity and Section 3's fixed-fiber variance
bound. -/
private theorem lemma3_first_residual_sq_integrable_of_sampled_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hquery :
      AEMeasurable
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hresidual_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ))) :
    Integrable
      (fun ω =>
        ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
          objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2) μ := by
  let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
    (iterate S (t + 1) ω,
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let φ : (DecisionSpace d × DecisionSpace d) → Sample → ℝ := fun q ξ =>
    ‖stochasticGradient S q.1 ξ - objectiveGradient S q.1‖ ^ 2
  have hφ_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample => φ p.1 p.2)
        ((Measure.map query μ).prod (Measure.map sample μ)) := by
    convert hresidual_prod.norm.mul hresidual_prod.norm using 1
    ext p
    simp [φ, pow_two]
  have hfixed :
      ∀ q : DecisionSpace d × DecisionSpace d,
        Integrable (fun ξ => φ q ξ) (Measure.map sample μ) ∧
          ∫ ξ, φ q ξ ∂Measure.map sample μ ≤ σ ^ 2 := by
    intro q
    simpa [sample, φ] using
      section3_sampled_product_residual_fixed_variance_bound
        S μ hsec3 (t + 1)
        (fun q : DecisionSpace d × DecisionSpace d => q.1) q
  simpa [query, sample, φ] using
    integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := μ) (ν := Measure.map sample μ)
      (φ := φ) (X := query) (Y := sample) (C := σ ^ 2)
      hφ_prod
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample] using hindep)
      rfl
      (by intro q ξ; exact sq_nonneg _)
      (sq_nonneg σ)
      (fun q => (hfixed q).1)
      (fun q => (hfixed q).2)

/-- Paired random-query centered residual-difference square-integrability for
Lemma 3, reduced to the two Section 3 fixed-fiber variance bounds. -/
private theorem lemma3_second_residual_difference_sq_integrable_of_sampled_product
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hquery :
      AEMeasurable
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hresidual_left :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1)
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)))
    (hresidual_right :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ))) :
    Integrable
      (fun ω =>
        ‖(stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)) -
          (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S t ω))‖ ^ 2) μ := by
  let query : Ω → (DecisionSpace d × DecisionSpace d) × DecisionSpace d := fun ω =>
    ((iterate S (t + 1) ω, iterate S t ω),
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  have hleft_sq :
      Integrable
        (fun ω =>
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2) μ := by
    let φ : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) → Sample → ℝ :=
      fun q ξ => ‖stochasticGradient S q.1.1 ξ - objectiveGradient S q.1.1‖ ^ 2
    have hφ_prod :
        AEStronglyMeasurable
          (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
            φ p.1 p.2)
          ((Measure.map query μ).prod (Measure.map sample μ)) := by
      convert hresidual_left.norm.mul hresidual_left.norm using 1
      ext p
      simp [φ, pow_two]
    have hfixed :
        ∀ q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d,
          Integrable (fun ξ => φ q ξ) (Measure.map sample μ) ∧
            ∫ ξ, φ q ξ ∂Measure.map sample μ ≤ σ ^ 2 := by
      intro q
      simpa [sample, φ] using
        section3_sampled_product_residual_fixed_variance_bound
          S μ hsec3 (t + 1)
          (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.1) q
    simpa [sample, φ] using
      integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
        (P := μ) (ν := Measure.map sample μ)
        (φ := φ) (X := query) (Y := sample) (C := σ ^ 2)
        hφ_prod
        (by simpa [query] using hquery)
        (by simpa [sample] using hsample.aemeasurable)
        (by simpa [query, sample] using hindep)
        rfl
        (by intro q ξ; exact sq_nonneg _)
        (sq_nonneg σ)
        (fun q => (hfixed q).1)
        (fun q => (hfixed q).2)
  have hright_sq :
      Integrable
        (fun ω =>
          ‖stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S t ω)‖ ^ 2) μ := by
    let φ : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) → Sample → ℝ :=
      fun q ξ => ‖stochasticGradient S q.1.2 ξ - objectiveGradient S q.1.2‖ ^ 2
    have hφ_prod :
        AEStronglyMeasurable
          (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
            φ p.1 p.2)
          ((Measure.map query μ).prod (Measure.map sample μ)) := by
      convert hresidual_right.norm.mul hresidual_right.norm using 1
      ext p
      simp [φ, pow_two]
    have hfixed :
        ∀ q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d,
          Integrable (fun ξ => φ q ξ) (Measure.map sample μ) ∧
            ∫ ξ, φ q ξ ∂Measure.map sample μ ≤ σ ^ 2 := by
      intro q
      simpa [sample, φ] using
        section3_sampled_product_residual_fixed_variance_bound
          S μ hsec3 (t + 1)
          (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.2) q
    simpa [sample, φ] using
      integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
        (P := μ) (ν := Measure.map sample μ)
        (φ := φ) (X := query) (Y := sample) (C := σ ^ 2)
        hφ_prod
        (by simpa [query] using hquery)
        (by simpa [sample] using hsample.aemeasurable)
        (by simpa [query, sample] using hindep)
        rfl
        (by intro q ξ; exact sq_nonneg _)
        (sq_nonneg σ)
        (fun q => (hfixed q).1)
        (fun q => (hfixed q).2)
  have hleft_aesm :
      AEStronglyMeasurable
        (fun ω =>
          stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)) μ :=
    aestronglyMeasurable_comp_of_indep_product_law
      (A := (DecisionSpace d × DecisionSpace d) × DecisionSpace d)
      (B := Sample)
      (X := query) (Y := sample)
      (φ := fun p =>
        stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1)
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample] using hindep)
      (by simpa [query, sample] using hresidual_left)
  have hright_aesm :
      AEStronglyMeasurable
        (fun ω =>
          stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S t ω)) μ :=
    aestronglyMeasurable_comp_of_indep_product_law
      (A := (DecisionSpace d × DecisionSpace d) × DecisionSpace d)
      (B := Sample)
      (X := query) (Y := sample)
      (φ := fun p =>
        stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample] using hindep)
      (by simpa [query, sample] using hresidual_right)
  exact integrable_sq_norm_sub hleft_aesm hright_aesm hleft_sq hright_sq

/-- Finite generated-history bound for the cumulative sampled-gradient square
sum.  This is the source `G_t ≤ G` argument from Algorithm 1, specialized to a
fixed finite time and kept private to Lemma 3's integrability route. -/
private theorem lemma3_cumulativeGradientNormSq_eventually_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ ω ∂μ, cumulativeGradientNormSq S t ω ≤ R := by
  exact exists_nonneg_ae_bound_accumulator_of_ae_bounded_increments μ
    (cumulativeGradientNormSq S)
    (fun n ω => ‖stochasticGradient S (iterate S n ω) (S.sample n ω)‖ ^ 2)
    (G ^ 2) t (sq_nonneg G)
    ((hsec3.G_lipschitz_losses 0).mono fun ω hω => by
      rw [cumulativeGradientNormSq_zero]
      exact pow_le_pow_left₀ (norm_nonneg _) (hω S.x₁) 2)
    (fun n _hn => Filter.Eventually.of_forall fun ω => by
      rw [cumulativeGradientNormSq_succ])
    (fun n _hn => (hsec3.G_lipschitz_losses (n + 1)).mono fun ω hω =>
      pow_le_pow_left₀ (norm_nonneg _) (hω (iterate S (n + 1) ω)) 2)

/-- The generated cumulative sampled-gradient square sum is pointwise
nonnegative. -/
private theorem cumulativeGradientNormSq_nonneg
    (S : Setup Ω Sample E) (t : ℕ) (ω : Ω) :
    0 ≤ cumulativeGradientNormSq S t ω := by
  induction t with
  | zero =>
      simpa [cumulativeGradientNormSq, stateProcess, initialState] using
        sq_nonneg ‖S.stochasticGradient S.x₁ (S.sample 0 ω)‖
  | succ t ih =>
      rw [cumulativeGradientNormSq_succ]
      exact add_nonneg ih (sq_nonneg _)

/-- Continuity on the generated compact scalar range of Lemma 3's multiplier
coefficient as a function of the cumulative sampled-gradient square sum. -/
private theorem lemma3_scalar_multiplier_of_sumSq_continuousOn_Icc
    (S : Setup Ω Sample E) {R : ℝ}
    (hw_pos : 0 < S.w) (hk_ne : S.k ≠ 0) :
    ContinuousOn
      (fun sumSq : ℝ =>
        (1 / adaptiveStepsize S sumSq) *
          (1 - momentumWeight S (adaptiveStepsize S sumSq)) ^ 2)
      (Set.Icc 0 R) := by
  simpa [adaptiveStepsize, momentumWeight] using
    SOptLib.inverse_rpow_step_size_complementary_quadratic_momentum_multiplier_continuousOn_Icc
      S.k S.w ((1 : ℝ) / 3) S.c R hw_pos

/-- Continuity on the generated compact scalar range of the momentum factor
`1-a_{t+1}` as a function of the cumulative sampled-gradient square sum. -/
private theorem lemma3_one_sub_momentum_of_sumSq_continuousOn_Icc
    (S : Setup Ω Sample E) {R : ℝ}
    (hw_pos : 0 < S.w) :
    ContinuousOn
      (fun sumSq : ℝ => 1 - momentumWeight S (adaptiveStepsize S sumSq))
      (Set.Icc 0 R) := by
  simpa [momentumWeight, adaptiveStepsize] using
    SOptLib.one_sub_quadraticMomentumWeight_inverseRpowStepSize_continuousOn_Icc
      S.k S.w ((1 : ℝ) / 3) S.c R hw_pos

/-- Compact-range bound for Lemma 3's scalar multiplier
`η_t⁻¹(1-a_{t+1})²` along the generated history. -/
private theorem lemma3_generated_scalar_multiplier_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᵐ ω ∂μ,
        ‖(1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2‖ ≤ A := by
  classical
  rcases lemma3_cumulativeGradientNormSq_eventually_le S μ hsec3 t with
    ⟨R, hR_nonneg, hR⟩
  have hw_pos : 0 < S.w := lemma3LocalQuotientBoundary_w_pos S hboundary
  have hk_ne : S.k ≠ 0 := lemma3LocalQuotientBoundary_k_ne S hboundary
  let scalarOfSumSq : ℝ → ℝ := fun sumSq =>
    (1 / adaptiveStepsize S sumSq) *
      (1 - momentumWeight S (adaptiveStepsize S sumSq)) ^ 2
  have hcompact : IsCompact (Set.Icc (0 : ℝ) R) := isCompact_Icc
  have hcont : ContinuousOn scalarOfSumSq (Set.Icc (0 : ℝ) R) := by
    simpa [scalarOfSumSq] using
      lemma3_scalar_multiplier_of_sumSq_continuousOn_Icc S hw_pos hk_ne
  have hmem : ∀ᵐ ω ∂μ, cumulativeGradientNormSq S t ω ∈ Set.Icc (0 : ℝ) R := by
    filter_upwards [hR] with ω hωR
    exact ⟨cumulativeGradientNormSq_nonneg S t ω, hωR⟩
  simpa [scalarOfSumSq, stepsize, nextMomentumWeight] using
    exists_nonneg_ae_norm_bound_comp_of_eventually_mem_compact_of_continuousOn
      μ (Set.Icc (0 : ℝ) R) (cumulativeGradientNormSq S t) scalarOfSumSq
      hmem hcompact hcont

/-- Compact-range bound for the generated momentum factor `1-a_{t+1}`. -/
private theorem lemma3_generated_one_sub_momentum_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᵐ ω ∂μ, ‖1 - nextMomentumWeight S t ω‖ ≤ A := by
  classical
  rcases lemma3_cumulativeGradientNormSq_eventually_le S μ hsec3 t with
    ⟨R, hR_nonneg, hR⟩
  have hw_pos : 0 < S.w := lemma3LocalQuotientBoundary_w_pos S hboundary
  let coeffOfSumSq : ℝ → ℝ := fun sumSq =>
    1 - momentumWeight S (adaptiveStepsize S sumSq)
  have hcompact : IsCompact (Set.Icc (0 : ℝ) R) := isCompact_Icc
  have hcont : ContinuousOn coeffOfSumSq (Set.Icc (0 : ℝ) R) := by
    simpa [coeffOfSumSq] using
      lemma3_one_sub_momentum_of_sumSq_continuousOn_Icc S hw_pos
  rcases exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      coeffOfSumSq hcompact hcont with ⟨A, hA_nonneg, hA⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hR] with ω hωR
  have hmem : cumulativeGradientNormSq S t ω ∈ Set.Icc (0 : ℝ) R :=
    ⟨cumulativeGradientNormSq_nonneg S t ω, hωR⟩
  simpa [coeffOfSumSq, stepsize, nextMomentumWeight] using
    hA (cumulativeGradientNormSq S t ω) hmem

/-- Finite generated-history bound for the STORM direction coordinate. -/
private theorem lemma3_generated_direction_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᵐ ω ∂μ, ‖direction S t ω‖ ≤ D := by
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  apply exists_nonneg_ae_norm_bound_of_recursive_affine_correction
    (μ := μ)
    (direction := direction S)
    (gNext := fun n ω =>
      stochasticGradient S (iterate S (n + 1) ω) (S.sample (n + 1) ω))
    (gCorr := fun n ω =>
      stochasticGradient S (iterate S n ω) (S.sample (n + 1) ω))
    (coeff := fun n ω => 1 - nextMomentumWeight S n ω)
    (G := G) hG_nonneg (t := t)
  · filter_upwards [hsec3.G_lipschitz_losses 0] with ω hω
    simpa only [direction_zero] using hω S.x₁
  · intro n
    filter_upwards [hsec3.G_lipschitz_losses (n + 1)] with ω hω
    exact hω (iterate S (n + 1) ω)
  · intro n
    filter_upwards [hsec3.G_lipschitz_losses (n + 1)] with ω hω
    exact hω (iterate S n ω)
  · intro n
    apply lemma3_generated_one_sub_momentum_eventually_bound S μ hsec3 n
    simpa [lemma3LocalQuotientBoundary] using hboundary
  · intro n ω
    exact direction_succ S n ω

/-- Finite generated-history bound for the STORM error coordinate
`ε_t = d_t - ∇F(x_t)`. -/
private theorem lemma3_generated_error_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂μ, ‖error S t ω‖ ≤ B := by
  classical
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  rcases lemma3_generated_direction_eventually_bound S μ hsec3 t hboundary with
    ⟨D, hD_nonneg, hD⟩
  have hobj_bound : ∀ x : DecisionSpace d, ‖objectiveGradient S x‖ ≤ G := by
    intro x
    exact section3_objectiveGradient_norm_le S μ hsec3 0 x
  refine ⟨D + G, add_nonneg hD_nonneg hG_nonneg, ?_⟩
  filter_upwards [hD] with ω hDω
  have hobj : ‖objectiveGradient S (iterate S t ω)‖ ≤ G :=
    hobj_bound (iterate S t ω)
  calc
    ‖error S t ω‖ =
        ‖direction S t ω - objectiveGradient S (iterate S t ω)‖ := rfl
    _ ≤ ‖direction S t ω‖ + ‖objectiveGradient S (iterate S t ω)‖ :=
      norm_sub_le _ _
    _ ≤ D + G := add_le_add hDω hobj

/-- Iteration-32 voucher step: the scalar coefficient
`η_t⁻¹(1-a_{t+1})²` is eventually bounded along the generated finite STORM
history.

The intended proof is deterministic: first show the finite cumulative
sample-gradient square sum is eventually bounded using `G_lipschitz_losses`,
then use continuity of
`sumSq ↦ (1 / adaptiveStepsize S sumSq) *
  (1 - momentumWeight S (adaptiveStepsize S sumSq)) ^ 2`
on the resulting compact interval. -/
private theorem _voucher_attempt__voucher_step_lemma3_scalar_multiplier_eventually_norm_bound_32_35
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᵐ ω ∂μ,
        ‖(1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2‖ ≤ A := by
  exact lemma3_generated_scalar_multiplier_eventually_bound S μ hsec3 t hboundary

/-- Iteration-35 same-head attempt artifact for
`_voucher_step_lemma3_scalar_multiplier_eventually_norm_bound_32`.

The active supplier is routed through this declaration so the public Lemma 3
cone consumes the source/coarser generated-stepsize boundary evidence instead
of depending directly on the older unexpanded private leaf. -/
private theorem _voucher_step_lemma3_scalar_multiplier_eventually_norm_bound_32
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᵐ ω ∂μ,
        ‖(1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2‖ ≤ A := by
  exact
    _voucher_attempt__voucher_step_lemma3_scalar_multiplier_eventually_norm_bound_32_35
      S μ hsec3 t hboundary

/-- Iteration-32 voucher step: the generated error `ε_t` is eventually bounded
under Section 3's `G`-Lipschitz sample-gradient assumption.

The source-derived objective-gradient bound is included explicitly because it
is the non-sample part of `ε_t = d_t - ∇F(x_t)`.  The remaining proof is a
finite induction through `stateProcess`: initialization uses
`G_lipschitz_losses 0`; the successor step uses the scalar bound for
`1-a_{s+1}` and the two sampled-gradient bounds supplied by
`G_lipschitz_losses (s+1)`. -/
private theorem _voucher_attempt__voucher_step_lemma3_error_eventually_norm_bound_32_35
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂μ, ‖error S t ω‖ ≤ B := by
  exact lemma3_generated_error_eventually_bound S μ hsec3 t hboundary

/-- Iteration-35 same-head attempt artifact for
`_voucher_step_lemma3_error_eventually_norm_bound_32`.

The body of the attempt above expands the corrected generated quotient boundary
and scalar-prefix inputs down to the finite generated-direction norm estimate;
this wrapper keeps the previous supplier name stable for existing consumers. -/
private theorem _voucher_step_lemma3_error_eventually_norm_bound_32
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂μ, ‖error S t ω‖ ≤ B := by
  exact
    _voucher_attempt__voucher_step_lemma3_error_eventually_norm_bound_32_35
      S μ hsec3 t hboundary

/-- Iteration-32 voucher step: bounded scalar and bounded generated error give
the exact a.e. multiplier bound needed by `integrable_sq_norm_of_ae_bound`. -/
private theorem _voucher_step_lemma3_multiplier_bound_from_scalar_and_error_bounds_32
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (t : ℕ)
    (hscalar :
      ∃ A : ℝ, 0 ≤ A ∧
        ∀ᵐ ω ∂μ,
          ‖(1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2‖ ≤ A)
    (herr : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂μ, ‖error S t ω‖ ≤ B) :
    ∃ C : ℝ, ∀ᵐ ω ∂μ,
      ‖((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
        error S t ω‖ ≤ C := by
  rcases hscalar with ⟨A, hA_nonneg, hA⟩
  rcases herr with ⟨B, _hB_nonneg, hB⟩
  refine ⟨A * B, ?_⟩
  filter_upwards [hA, hB] with ω hAω hBω
  rw [norm_smul]
  exact mul_le_mul hAω hBω (norm_nonneg _) hA_nonneg

/-- Iteration-32 same-head voucher attempt for the generated Lemma 3
multiplier square-integrability leaf.

The proof reaches the exact deterministic `hbounded` boundary through named
scalar and generated-error bound suppliers, then discharges integrability with
the already accepted `SOptLib.integrable_sq_norm_of_ae_bound` terminal API. -/
private theorem _voucher_attempt_lemma3_multiplier_sq_integrable_32
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    Integrable
      (fun ω =>
        ‖((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
          error S t ω‖ ^ 2) μ := by
  classical
  let multiplier : Ω → DecisionSpace d := fun ω =>
    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω
  let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
    (iterate S (t + 1) ω, multiplier ω)
  have hquery_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        query μ := by
    simpa [query, multiplier] using
      lemma3_first_query_multiplier_prefixAEMeasurable_via_generated_history
        S μ hsec3 t
  have hquery_aemeas : AEMeasurable query μ :=
    prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
  have hmult_aesm : AEStronglyMeasurable multiplier μ := by
    have htmp :=
      (measurable_snd.aestronglyMeasurable).comp_aemeasurable hquery_aemeas
    simpa [Function.comp_def, query, multiplier] using htmp
  have hscalar :=
    _voucher_step_lemma3_scalar_multiplier_eventually_norm_bound_32
      S μ hsec3 t hboundary
  have herr :=
    _voucher_step_lemma3_error_eventually_norm_bound_32
      S μ hsec3 t hboundary
  have hbounded :
      ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖multiplier ω‖ ≤ C := by
    simpa [multiplier] using
      _voucher_step_lemma3_multiplier_bound_from_scalar_and_error_bounds_32
        S μ t hscalar herr
  rcases hbounded with ⟨C, hC⟩
  exact (SOptLib.integrable_sq_norm_of_ae_bound hmult_aesm hC).1

/-- Source/coarser generated-history supplier for Lemma 3's multiplier
square-integrability.

This is the active replacement for the retired private scalar/error supplier
chain.  It starts from the paper-level generated quotient boundary, the
Algorithm 1 finite generated-history facts, and the Section 3 `G`-Lipschitz
oracle bounds.  The remaining local leaves are the two source-history estimates:
boundedness of the displayed scalar `η_t⁻¹(1-a_{t+1})²` on the generated
cumulative-gradient range, and boundedness of the generated error recursion. -/
private theorem lemma3_multiplier_sq_integrable_of_generated_quotient_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    Integrable
      (fun ω =>
        ‖((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
          error S t ω‖ ^ 2) μ := by
  classical
  let scalar : Ω → ℝ := fun ω =>
    (1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2
  let multiplier : Ω → DecisionSpace d := fun ω => scalar ω • error S t ω
  have hscalar_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        scalar μ := by
    simpa [scalar] using lemma3_scalar_multiplier_prefixAEMeasurable S μ hsec3 t
  have herror_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (error S t) μ :=
    lemma3_error_prefixAEMeasurable S μ hsec3 t
  have hmult_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        multiplier μ := by
    simpa [scalar, multiplier] using
      prefixAEMeasurable.real_smul hscalar_prefix herror_prefix
  have hmult_aemeas : AEMeasurable multiplier μ :=
    prefixAEMeasurable.aemeasurable S μ hsec3 hmult_prefix
  have hmult_aesm : AEStronglyMeasurable multiplier μ :=
    hmult_aemeas.aestronglyMeasurable
  have hsum_bound :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ ω ∂μ, cumulativeGradientNormSq S t ω ≤ R :=
    lemma3_cumulativeGradientNormSq_eventually_le S μ hsec3 t
  have hw_pos : 0 < S.w := lemma3LocalQuotientBoundary_w_pos S hboundary
  have hk_ne : S.k ≠ 0 := lemma3LocalQuotientBoundary_k_ne S hboundary
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  have hobj_bound : ∀ x : DecisionSpace d, ‖objectiveGradient S x‖ ≤ G := by
    intro x
    exact section3_objectiveGradient_norm_le S μ hsec3 0 x
  have hgenerated_boundary : generatedStepsizeQuotientBoundary S := by
    simpa [lemma3LocalQuotientBoundary] using hboundary
  have hscalar_bound :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ω ∂μ, ‖scalar ω‖ ≤ A := by
    simpa [scalar] using
      lemma3_generated_scalar_multiplier_eventually_bound S μ hsec3 t hboundary
  have herror_bound :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂μ, ‖error S t ω‖ ≤ B := by
    exact lemma3_generated_error_eventually_bound S μ hsec3 t hboundary
  rcases hscalar_bound with ⟨A, hA_nonneg, hA⟩
  rcases herror_bound with ⟨B, _hB_nonneg, hB⟩
  have hbounded : ∃ C : ℝ, ∀ᵐ ω ∂μ, ‖multiplier ω‖ ≤ C := by
    refine ⟨A * B, ?_⟩
    filter_upwards [hA, hB] with ω hAω hBω
    simpa [multiplier, norm_smul] using
      mul_le_mul hAω hBω (norm_nonneg _) hA_nonneg
  rcases hbounded with ⟨C, hC⟩
  simpa [multiplier, scalar] using
    (SOptLib.integrable_sq_norm_of_ae_bound hmult_aesm hC).1

/-- Generated Lemma 3 multiplier square-integrability.  This is the exact
source-scale L2 side condition needed for inner-product integrability; it is
strictly weaker than the retired scalar-inner square-integrability leaves. -/
private theorem lemma3_multiplier_sq_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    Integrable
      (fun ω =>
        ‖((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
          error S t ω‖ ^ 2) μ := by
  exact lemma3_multiplier_sq_integrable_of_generated_quotient_boundary S μ hsec3 t hboundary

/-- First Lemma 3 cross-term integrability through the source-faithful L2
route: residual L2 from Section 3 variance, multiplier L2 from the generated
history estimate, and Cauchy-Schwarz/Hölder for the inner product. -/
private theorem lemma3_first_cross_term_integrable_of_l2
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t)
    (hquery :
      AEMeasurable
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          (iterate S (t + 1) ω,
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hresidual_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ))) :
    Integrable
      (fun ω =>
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
    (iterate S (t + 1) ω,
      ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let residual : Ω → DecisionSpace d := fun ω =>
    stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
      objectiveGradient S (iterate S (t + 1) ω)
  let multiplier : Ω → DecisionSpace d := fun ω =>
    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω
  have hres_aesm : AEStronglyMeasurable residual μ :=
    aestronglyMeasurable_comp_of_indep_product_law
      (A := DecisionSpace d × DecisionSpace d) (B := Sample)
      (X := query) (Y := sample)
      (φ := fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
        stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample] using hindep)
      (by simpa [query, sample] using hresidual_prod)
  have hmult_aesm : AEStronglyMeasurable multiplier μ :=
    by
      have htmp :=
        (measurable_snd.aestronglyMeasurable).comp_aemeasurable
          (by simpa [query] using hquery)
      simpa [Function.comp_def, query, multiplier] using htmp
  have hres_sq :
      Integrable (fun ω => ‖residual ω‖ ^ 2) μ := by
    simpa [residual] using
      lemma3_first_residual_sq_integrable_of_sampled_product
        S μ hsec3 t hquery hsample hindep hresidual_prod
  have hmult_sq : Integrable (fun ω => ‖multiplier ω‖ ^ 2) μ := by
    simpa [multiplier] using lemma3_multiplier_sq_integrable S μ hsec3 t hboundary
  simpa [residual, multiplier] using
    integrable_inner_of_integrable_sq_norm hres_aesm hmult_aesm hres_sq hmult_sq

/-- Paired Lemma 3 cross-term integrability through the same L2 route as the
first term, with residual-difference L2 obtained from the two fixed-fiber
variance bounds. -/
private theorem lemma3_second_cross_term_integrable_of_l2
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t)
    (hquery :
      AEMeasurable
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) μ)
    (hsample : Measurable (S.sample (t + 1)))
    (hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          ((iterate S (t + 1) ω, iterate S t ω),
            ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω))
        (S.sample (t + 1)) μ)
    (hresidual_left :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1)
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)))
    (hresidual_right :
      AEStronglyMeasurable
        (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)
        ((Measure.map
          (fun ω =>
            ((iterate S (t + 1) ω, iterate S t ω),
              ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ))) :
    Integrable
      (fun ω =>
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) μ := by
  let residual : Ω → DecisionSpace d := fun ω =>
    (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
      objectiveGradient S (iterate S (t + 1) ω)) -
      (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
        objectiveGradient S (iterate S t ω))
  let multiplier : Ω → DecisionSpace d := fun ω =>
    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) • error S t ω
  let query : Ω → (DecisionSpace d × DecisionSpace d) × DecisionSpace d := fun ω =>
    ((iterate S (t + 1) ω, iterate S t ω), multiplier ω)
  let sample : Ω → Sample := S.sample (t + 1)
  have hleft_aesm :
      AEStronglyMeasurable
        (fun ω =>
          stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)) μ :=
    aestronglyMeasurable_comp_of_indep_product_law
      (A := (DecisionSpace d × DecisionSpace d) × DecisionSpace d)
      (B := Sample) (X := query) (Y := sample)
      (φ := fun p =>
        stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1)
      (by simpa [query, multiplier] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample, multiplier] using hindep)
      (by simpa [query, sample, multiplier] using hresidual_left)
  have hright_aesm :
      AEStronglyMeasurable
        (fun ω =>
          stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S t ω)) μ :=
    aestronglyMeasurable_comp_of_indep_product_law
      (A := (DecisionSpace d × DecisionSpace d) × DecisionSpace d)
      (B := Sample) (X := query) (Y := sample)
      (φ := fun p =>
        stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)
      (by simpa [query, multiplier] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample, multiplier] using hindep)
      (by simpa [query, sample, multiplier] using hresidual_right)
  have hres_aesm : AEStronglyMeasurable residual μ := by
    simpa [residual] using hleft_aesm.sub hright_aesm
  have hmult_aesm : AEStronglyMeasurable multiplier μ :=
    by
      have htmp :=
        (measurable_snd.aestronglyMeasurable).comp_aemeasurable
          (by simpa [query] using hquery)
      simpa [Function.comp_def, query, multiplier] using htmp
  have hres_sq : Integrable (fun ω => ‖residual ω‖ ^ 2) μ := by
    simpa [residual] using
      lemma3_second_residual_difference_sq_integrable_of_sampled_product
        S μ hsec3 t hquery hsample hindep hresidual_left hresidual_right
  have hmult_sq : Integrable (fun ω => ‖multiplier ω‖ ^ 2) μ := by
    simpa [multiplier] using lemma3_multiplier_sq_integrable S μ hsec3 t hboundary
  have hinner :=
    integrable_inner_of_integrable_sq_norm hres_aesm hmult_aesm hres_sq hmult_sq
  simpa [residual, multiplier, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using hinner

/-- Source-facing rendering of Lemma 1's hypothesis `η_t ≤ 1/(4L)`.

It constrains only displayed source stepsizes that are defined by Algorithm 1;
it does not read a totalized fallback value as the paper's `η_t`. -/
def sourceStepsizeLE (S : Setup Ω Sample E) (n : ℕ) (bound : ℝ) : Prop :=
  ∀ ω η, sourceStepsize S n ω = some η → η ≤ bound

/-- The one-point zero-loss model used to witness the old unguarded source
lemma heads as false at the displayed scalar boundary `k = w = c = 0`. -/
def degenerateZeroSetup (d : ℕ) :
    Setup (ℕ → Unit) Unit (DecisionSpace d) :=
  { x₁ := 0
    sample := fun n ω => ω n
    sampleLoss := fun _ _ => 0
    objectiveValue := fun _ => 0
    k := 0
    w := 0
    c := 0 }

/-- In the zero-loss degenerate model, every stochastic gradient is zero. -/
theorem degenerateZeroSetup_stochasticGradient
    (d : ℕ) (x : DecisionSpace d) (ξ : Unit) :
    stochasticGradient (degenerateZeroSetup d) x ξ = 0 := by
  simp [stochasticGradient, degenerateZeroSetup]

/-- The zero-loss degenerate model satisfies exactly the Section 3 assumptions;
the failure below is therefore a source-definedness boundary issue, not an
assumption failure. -/
theorem degenerateZeroSetup_section3Assumptions (d : ℕ) :
    Section3Assumptions (degenerateZeroSetup d)
      (SOptLib.iidStreamLaw (Measure.dirac ())) 0 0 0 0 := by
  classical
  refine
    { independent_samples := ?_
      sample_measurable := ?_
      function_oracle := ?_
      gradient_noise_bound := ?_
      finite_lower_bound := ?_
      differentiable_losses := ?_
      L_smooth_losses := ?_
      L_smooth_sample_law := ?_
      G_lipschitz_losses := ?_ }
  · simpa [degenerateZeroSetup] using
      SOptLib.iidStreamLaw_iIndepFun_eval (Measure.dirac (()))
  · intro n
    simpa [degenerateZeroSetup] using
      (measurable_pi_apply n : Measurable (fun ω : ℕ → Unit => ω n))
  · intro n x
    simp [sourceExpectedLossObjectiveAtTimeValue, sourceRealExpectationValue,
      degenerateZeroSetup]
  · intro n x
    refine ⟨?_, ?_, 0, ?_, by norm_num⟩
    · simp [degenerateZeroSetup, stochasticGradient, objectiveGradient]
    · simp [degenerateZeroSetup, stochasticGradient, objectiveGradient]
    · simp [sourceRealExpectationValue, degenerateZeroSetup, stochasticGradient,
        objectiveGradient]
  · simpa [degenerateZeroSetup] using (isGLB_singleton : IsGLB ({0} : Set ℝ) 0)
  · intro n
    exact Filter.Eventually.of_forall fun ω x => by
      rw [degenerateZeroSetup_stochasticGradient]
      simpa [degenerateZeroSetup] using
        (hasGradientAt_const (𝕜 := ℝ) (F := DecisionSpace d) x (0 : ℝ))
  · intro n
    exact Filter.Eventually.of_forall fun ω x y => by
      simp [degenerateZeroSetup_stochasticGradient]
  · intro n
    exact Filter.Eventually.of_forall fun ξ x y => by
      simp [degenerateZeroSetup_stochasticGradient]
  · intro n
    exact Filter.Eventually.of_forall fun ω x => by
      simp [degenerateZeroSetup_stochasticGradient]

/-- At `k = w = 0` with zero gradients, the displayed adaptive stepsize
quotient at `t = 0` is not a source value. -/
theorem degenerateZeroSetup_sourceStepsize_zero_eq_none
    (d : ℕ) (ω : ℕ → Unit) :
    sourceStepsize (degenerateZeroSetup d) 0 ω = none := by
  simp [sourceStepsize, sourceCumulativeGradientNormSq, sourceStateProcess,
    initialState, adaptiveStepsizeSourceValue, sourcePositiveRpowValue,
    stepsizeBase, degenerateZeroSetup, stochasticGradient]

/-- Once the first displayed adaptive stepsize is undefined in the degenerate
model, the next source iterate is undefined. -/
theorem degenerateZeroSetup_sourceIterate_one_eq_none
    (d : ℕ) (ω : ℕ → Unit) :
    sourceIterate (degenerateZeroSetup d) 1 ω = none := by
  simp [sourceIterate, sourceStateProcess, sourceStateStep, initialState,
    adaptiveStepsizeSourceValue, sourcePositiveRpowValue, stepsizeBase,
    degenerateZeroSetup, stochasticGradient]

/-- In the degenerate model the partial source run stops after initialization. -/
theorem degenerateZeroSetup_sourceStateProcess_succ_eq_none
    (d : ℕ) (n : ℕ) (ω : ℕ → Unit) :
    sourceStateProcess (degenerateZeroSetup d) (n + 1) ω = none := by
  induction n with
  | zero =>
      simp [sourceStateProcess, sourceStateStep, initialState,
        adaptiveStepsizeSourceValue, sourcePositiveRpowValue, stepsizeBase,
        degenerateZeroSetup, stochasticGradient]
  | succ n ih =>
      rw [sourceStateProcess]
      simp [ih]

/-- Every displayed adaptive source stepsize is undefined in the degenerate
model, so Lemma 1's old source stepsize condition is vacuous there. -/
theorem degenerateZeroSetup_sourceStepsize_eq_none
    (d : ℕ) (n : ℕ) (ω : ℕ → Unit) :
    sourceStepsize (degenerateZeroSetup d) n ω = none := by
  cases n with
  | zero =>
      exact degenerateZeroSetup_sourceStepsize_zero_eq_none d ω
  | succ n =>
      simp [sourceStepsize, sourceCumulativeGradientNormSq,
        degenerateZeroSetup_sourceStateProcess_succ_eq_none]

/-- The old Lemma 1 stepsize hypothesis is vacuous in the concrete
degenerate model because no source stepsize is defined. -/
theorem degenerateZeroSetup_sourceStepsizeLE (d : ℕ) (bound : ℝ) :
    ∀ s, sourceStepsizeLE (degenerateZeroSetup d) s bound := by
  intro s ω η hη
  rw [degenerateZeroSetup_sourceStepsize_eq_none d s ω] at hη
  cases hη

/-- The old unguarded Lemma 1 conclusion is formally impossible in the
Section-3-valid zero-loss model, because its source left-hand side is
undefined at `t = 0`. -/
theorem old_unguarded_lemma1_biased_sgd_descent_false_degenerate (d : ℕ) :
    ¬ sourceExpectationLE (SOptLib.iidStreamLaw (Measure.dirac ()))
      (lemma1LHSExpr (degenerateZeroSetup d) 0)
      (lemma1RHSExpr (degenerateZeroSetup d) 0) := by
  refine not_sourceExpectationLE_left_of_forall_none
    (SOptLib.iidStreamLaw (Measure.dirac ()))
    (lemma1LHSExpr (degenerateZeroSetup d) 0)
    (lemma1RHSExpr (degenerateZeroSetup d) 0) ?_
  intro ω
  simp [lemma1LHSExpr, degenerateZeroSetup_sourceIterate_one_eq_none]

/-- Full old-head counterexample contract for Lemma 1: the Section 3
assumptions and old source stepsize premise hold, but the unguarded source
expectation comparison does not. -/
theorem old_unguarded_lemma1_counterexample_degenerate (d : ℕ) :
    Section3Assumptions (degenerateZeroSetup d)
        (SOptLib.iidStreamLaw (Measure.dirac ())) 0 0 0 0 ∧
      (∀ s, sourceStepsizeLE (degenerateZeroSetup d) s ((1 : ℝ) / (4 * 0))) ∧
        ¬ sourceExpectationLE (SOptLib.iidStreamLaw (Measure.dirac ()))
          (lemma1LHSExpr (degenerateZeroSetup d) 0)
          (lemma1RHSExpr (degenerateZeroSetup d) 0) := by
  exact
    ⟨degenerateZeroSetup_section3Assumptions d,
      degenerateZeroSetup_sourceStepsizeLE d ((1 : ℝ) / (4 * 0)),
      old_unguarded_lemma1_biased_sgd_descent_false_degenerate d⟩

/-- The old unguarded Lemma 3 conclusion is formally impossible in the same
degenerate model: both source cross-term expressions are undefined at `t = 0`. -/
theorem old_unguarded_lemma3_cross_terms_zero_false_degenerate (d : ℕ) :
    ¬ (sourceExpectationEqZero (SOptLib.iidStreamLaw (Measure.dirac ()))
          (lemma3FirstCrossTermExpr (degenerateZeroSetup d) 0) ∧
        sourceExpectationEqZero (SOptLib.iidStreamLaw (Measure.dirac ()))
          (lemma3SecondCrossTermExpr (degenerateZeroSetup d) 0)) := by
  intro hcross
  exact
    not_sourceExpectationEqZero_of_forall_none
      (SOptLib.iidStreamLaw (Measure.dirac ()))
      (lemma3FirstCrossTermExpr (degenerateZeroSetup d) 0)
      (by
        intro ω
        simp [lemma3FirstCrossTermExpr,
          degenerateZeroSetup_sourceIterate_one_eq_none])
      hcross.1

/-- The old unguarded Lemma 2 conclusion is formally impossible in the same
degenerate model, because the displayed `‖ε₁‖² / η₀` left-hand source
expression has no denominator source value. -/
theorem old_unguarded_lemma2_error_recurrence_false_degenerate (d : ℕ) :
    ¬ sourceExpectationLE (SOptLib.iidStreamLaw (Measure.dirac ()))
      (lemma2LHSExpr (degenerateZeroSetup d) 0)
      (lemma2RHSExpr (degenerateZeroSetup d) 0 0) := by
  refine not_sourceExpectationLE_left_of_forall_none
    (SOptLib.iidStreamLaw (Measure.dirac ()))
    (lemma2LHSExpr (degenerateZeroSetup d) 0)
    (lemma2RHSExpr (degenerateZeroSetup d) 0 0) ?_
  intro ω
  simp [lemma2LHSExpr, sourceError, degenerateZeroSetup_sourceStepsize_zero_eq_none,
    degenerateZeroSetup_sourceIterate_one_eq_none]

/-- Boundary-only witness for the Lemma 2 refactor: local source-expression
definedness at one displayed index does not imply the generated Algorithm 1
quotient boundary.

Here the first generated gradient norm is `1`, so the local adaptive base
`w + G₁² = -1/2 + 1` is positive and all Lemma 2 source expressions at `t = 0`
are defined.  The generated boundary nevertheless fails because it also
contains the source initialization boundary `0 < w`, which is false here. -/
private def localLemma2BoundaryButNotGeneratedSetup :
    Setup Unit Unit ℝ :=
  { x₁ := 0
    sample := fun _ _ => ()
    sampleLoss := fun x _ => x
    objectiveValue := fun x => x
    k := 1
    w := -((1 : ℝ) / 2)
    c := 0 }

private theorem localLemma2BoundaryButNotGeneratedSetup_stochasticGradient
    (x : ℝ) (ξ : Unit) :
    stochasticGradient localLemma2BoundaryButNotGeneratedSetup x ξ = 1 := by
  have hgrad : HasGradientAt (fun y : ℝ => y) 1 x := by
    simpa using (hasDerivAt_id x).hasGradientAt
  exact hgrad.gradient

private theorem localLemma2BoundaryButNotGeneratedSetup_base_zero_pos :
    0 < stepsizeBase localLemma2BoundaryButNotGeneratedSetup
      (cumulativeGradientNormSq localLemma2BoundaryButNotGeneratedSetup 0 ()) := by
  change
    0 <
      -((1 : ℝ) / 2) +
        ‖stochasticGradient localLemma2BoundaryButNotGeneratedSetup 0 ()‖ ^ 2
  rw [localLemma2BoundaryButNotGeneratedSetup_stochasticGradient]
  norm_num

private theorem localLemma2BoundaryButNotGeneratedSetup_sourceStateProcess_one :
    sourceStateProcess localLemma2BoundaryButNotGeneratedSetup 1 () =
      some (stateProcess localLemma2BoundaryButNotGeneratedSetup 1 ()) := by
  have hη :
      adaptiveStepsizeSourceValue localLemma2BoundaryButNotGeneratedSetup
          (cumulativeGradientNormSq localLemma2BoundaryButNotGeneratedSetup 0 ()) =
        some (adaptiveStepsize localLemma2BoundaryButNotGeneratedSetup
          (cumulativeGradientNormSq localLemma2BoundaryButNotGeneratedSetup 0 ())) :=
    adaptiveStepsizeSourceValue_eq_some_of_base_pos
      localLemma2BoundaryButNotGeneratedSetup
      localLemma2BoundaryButNotGeneratedSetup_base_zero_pos
  change
    sourceStateStep localLemma2BoundaryButNotGeneratedSetup 0
        (initialState localLemma2BoundaryButNotGeneratedSetup ()) () =
      some
        (stateStep localLemma2BoundaryButNotGeneratedSetup 0
          (initialState localLemma2BoundaryButNotGeneratedSetup ()) ())
  have hη' :
      adaptiveStepsizeSourceValue localLemma2BoundaryButNotGeneratedSetup
          (initialState localLemma2BoundaryButNotGeneratedSetup ()).gradNormSqSum =
        some (adaptiveStepsize localLemma2BoundaryButNotGeneratedSetup
          (initialState localLemma2BoundaryButNotGeneratedSetup ()).gradNormSqSum) := by
    simpa [cumulativeGradientNormSq, stateProcess] using hη
  simp [sourceStateStep, stateStep, stateStepFromSample, hη']

private theorem localLemma2BoundaryButNotGeneratedSetup_sourceIterate_one :
    sourceIterate localLemma2BoundaryButNotGeneratedSetup 1 () =
      some (iterate localLemma2BoundaryButNotGeneratedSetup 1 ()) := by
  simpa [sourceIterate, iterate,
    localLemma2BoundaryButNotGeneratedSetup_sourceStateProcess_one]

private theorem localLemma2BoundaryButNotGeneratedSetup_sourceStepsize_zero :
    sourceStepsize localLemma2BoundaryButNotGeneratedSetup 0 () =
      some (stepsize localLemma2BoundaryButNotGeneratedSetup 0 ()) := by
  have hη :
      adaptiveStepsizeSourceValue localLemma2BoundaryButNotGeneratedSetup
          (cumulativeGradientNormSq localLemma2BoundaryButNotGeneratedSetup 0 ()) =
        some (adaptiveStepsize localLemma2BoundaryButNotGeneratedSetup
          (cumulativeGradientNormSq localLemma2BoundaryButNotGeneratedSetup 0 ())) :=
    adaptiveStepsizeSourceValue_eq_some_of_base_pos
      localLemma2BoundaryButNotGeneratedSetup
      localLemma2BoundaryButNotGeneratedSetup_base_zero_pos
  simpa [sourceStepsize, sourceCumulativeGradientNormSq, stepsize, hη]

private theorem localLemma2BoundaryButNotGeneratedSetup_sourceNextMomentumWeight_zero :
    sourceNextMomentumWeight localLemma2BoundaryButNotGeneratedSetup 0 () =
      some (nextMomentumWeight localLemma2BoundaryButNotGeneratedSetup 0 ()) := by
  simp [sourceNextMomentumWeight, nextMomentumWeight,
    localLemma2BoundaryButNotGeneratedSetup_sourceStepsize_zero]

private theorem localLemma2BoundaryButNotGeneratedSetup_sourceError_zero :
    sourceError localLemma2BoundaryButNotGeneratedSetup 0 () =
      some (error localLemma2BoundaryButNotGeneratedSetup 0 ()) := by
  simp [sourceError, sourceDirection, sourceIterate, sourceStateProcess, error,
    direction, iterate, stateProcess]

private theorem localLemma2BoundaryButNotGeneratedSetup_sourceError_one :
    sourceError localLemma2BoundaryButNotGeneratedSetup 1 () =
      some (error localLemma2BoundaryButNotGeneratedSetup 1 ()) := by
  simpa [sourceError, sourceDirection, sourceIterate, error, direction, iterate,
    localLemma2BoundaryButNotGeneratedSetup_sourceStateProcess_one]

theorem lemma2LocalQuotientBoundary_not_implies_generatedStepsizeQuotientBoundary :
    ¬ (∀ S : Setup Unit Unit ℝ,
        lemma2LocalQuotientBoundary S 0 0 → generatedStepsizeQuotientBoundary S) := by
  intro himp
  have hlocal : lemma2LocalQuotientBoundary localLemma2BoundaryButNotGeneratedSetup 0 0 := by
    intro ω
    cases ω
    have hη_ne : stepsize localLemma2BoundaryButNotGeneratedSetup 0 () ≠ 0 := by
      change
        adaptiveStepsize localLemma2BoundaryButNotGeneratedSetup
          (cumulativeGradientNormSq localLemma2BoundaryButNotGeneratedSetup 0 ()) ≠ 0
      unfold adaptiveStepsize SOptLib.inverse_rpow_step_size
      exact div_ne_zero one_ne_zero
        (ne_of_gt
          (Real.rpow_pos_of_pos
            localLemma2BoundaryButNotGeneratedSetup_base_zero_pos ((1 : ℝ) / 3)))
    exact
      ⟨localLemma2BoundaryButNotGeneratedSetup_sourceError_one,
        localLemma2BoundaryButNotGeneratedSetup_sourceStepsize_zero,
        sourceQuotientValue_eq_some_of_den_ne hη_ne,
        localLemma2BoundaryButNotGeneratedSetup_sourceNextMomentumWeight_zero,
        localLemma2BoundaryButNotGeneratedSetup_sourceError_zero,
        by simp [sourceIterate, iterate, sourceStateProcess, stateProcess],
        localLemma2BoundaryButNotGeneratedSetup_sourceIterate_one,
        sourceQuotientValue_eq_some_of_den_ne hη_ne⟩
  have hgenerated := himp localLemma2BoundaryButNotGeneratedSetup hlocal
  have hw : 0 < localLemma2BoundaryButNotGeneratedSetup.w := hgenerated.1.1.1
  norm_num [localLemma2BoundaryButNotGeneratedSetup] at hw

/-- Private legacy route certificate for the older local-only Lemma 2 boundary.

This replaces the stale compatibility proof obligation.  The local predicate
only says the displayed expressions at one index are defined; it does not
supply Algorithm 1's generated quotient boundary, as witnessed by
`lemma2LocalQuotientBoundary_not_implies_generatedStepsizeQuotientBoundary`.
It is retained only as internal tombstone evidence for the old route and is not
part of the source/public dependency cone. -/
private theorem lemma2_error_recurrence_local_boundary_compat
    : ¬ (∀ S : Setup Unit Unit ℝ,
        lemma2LocalQuotientBoundary S 0 0 → generatedStepsizeQuotientBoundary S) :=
  lemma2LocalQuotientBoundary_not_implies_generatedStepsizeQuotientBoundary

/-- Private retirement packet for the obsolete local-only Lemma 2 route.

This is deliberately separated from the public Lemma 2 proof path: it records
that the old local boundary is not a supplier of the generated Algorithm 1
quotient boundary, rather than adapting it into a new wrapper route. -/
private theorem lemma2_obsolete_local_route_retirement_evidence :
    (¬ (∀ S : Setup Unit Unit ℝ,
        lemma2LocalQuotientBoundary S 0 0 → generatedStepsizeQuotientBoundary S)) ∧
      (¬ (∀ S : Setup Unit Unit ℝ,
        lemma2LocalQuotientBoundary S 0 0 → generatedStepsizeQuotientBoundary S)) := by
  exact
    ⟨lemma2LocalQuotientBoundary_not_implies_generatedStepsizeQuotientBoundary,
      lemma2_error_recurrence_local_boundary_compat⟩

/-- Affine STORM update identity in the variational form needed by the
smooth-descent API.

For `y = x - η d`, the estimator inner product is exactly the negative
reciprocal-stepsize quadratic displacement term.  This is source update
algebra from Algorithm 1, not an additional assumption. -/
private theorem storm_update_inner_direction_le_inv_stepsize_norm_sq
    (x d : E) (η : ℝ) :
    inner ℝ d ((x - η • d) - x) ≤
      0 - η⁻¹ * ‖(x - η • d) - x‖ ^ 2 := by
  by_cases hη : η = 0
  · simp [hη]
  · have hdiff : (x - η • d) - x = -η • d := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hdiff]
    have hnorm : ‖-η • d‖ ^ 2 = η ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_smul]
      have hsq_abs : ‖(-η : ℝ)‖ ^ 2 = η ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
        ring
      rw [mul_pow, hsq_abs]
    have hinner : inner ℝ d (-η • d) = -η * ‖d‖ ^ 2 := by
      simp [inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hinner, hnorm]
    field_simp [hη]
    nlinarith

/-- Deterministic coefficient collection used in Lemma 1.

This is the Hilbert-space algebra from Appendix A lines 719-736 after the
smoothness step has exposed `η`, `d`, `∇F(x)`, and `ε = d - ∇F(x)`.  It is
private because the source-facing burden is still to derive the stepsize
positivity from the generated Algorithm 1 boundary; the algebra itself is no
longer a stochastic-object-model issue. -/
private theorem lemma1_pointwise_descent_scalar_collection
    (g d ε : E) {L η : ℝ}
    (hL_pos : 0 < L)
    (hη_nonneg : 0 ≤ η)
    (hη_le : η ≤ (1 : ℝ) / (4 * L))
    (hε : ε = d - g) :
    inner ℝ g (-η • d) + (L / 2) * ‖-η • d‖ ^ 2 ≤
      (-η / 4) * ‖g‖ ^ 2 + (3 * η / 4) * ‖ε‖ ^ 2 := by
  exact inner_neg_smul_add_half_mul_norm_sq_le_of_le_inv_four_mul
    g d ε hL_pos hη_nonneg hη_le hε

/-- Generated-boundary Lemma 1 pointwise smooth-descent supplier.

This is the source/coarser replacement for the stale local-boundary pointwise
leaf above.  The paper's proof uses Algorithm 1's generated stepsizes together
with the Theorem 1 scalar side condition `0 < L`; the weak
`lemma1LocalSourceBoundary` records only source definedness and therefore cannot
provide either `0 < L` or nonnegativity of `η_t`. -/
private theorem lemma1_pointwise_descent_bound_of_generated_quotient_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hL_pos : 0 < L)
    (t : ℕ)
    (heta : ∀ s, sourceStepsizeLE S s ((1 : ℝ) / (4 * L))) :
    ∀ᵐ ω ∂μ,
      S.objectiveValue (iterate S (t + 1) ω) -
          S.objectiveValue (iterate S t ω) ≤
        (-stepsize S t ω / 4) *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2 +
          (3 * stepsize S t ω / 4) * ‖error S t ω‖ ^ 2 := by
  classical
  have hF_smooth :
      ∀ x y : DecisionSpace d,
        S.objectiveValue y ≤
          S.objectiveValue x +
            inner ℝ (objectiveGradient S x) (y - x) +
              (L / 2) * ‖y - x‖ ^ 2 := by
    intro x y
    exact
      _root_.smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
        (X := Set.univ)
        (f := S.objectiveValue)
        (grad := objectiveGradient S)
        (L := L)
        (by simpa using (convex_univ : Convex ℝ (Set.univ : Set (DecisionSpace d))))
        (by
          intro z _hz
          have hgrad_int :=
            section3_objective_hasGradientAt_integral_stochasticGradient
              S μ hsec3 0 z
          have hmean :
              (∫ ω, stochasticGradient S z (S.sample 0 ω) ∂μ) =
                objectiveGradient S z := by
            simpa [SOptLib.oracleMean_def] using
              section3_objectiveGradient_eq_oracleMean S μ hsec3 0 z
          simpa [hmean] using hgrad_int)
        (by
          intro z _hz w _hw
          exact section3_objectiveGradient_lipschitz S μ hsec3 0 z w)
        (by simp) (by simp)
  filter_upwards with ω
  have hupdate :
      iterate S (t + 1) ω = iterate S t ω - stepsize S t ω • direction S t ω := by
    rw [iterate_succ]
  have herr : error S t ω = direction S t ω - objectiveGradient S (iterate S t ω) :=
    error_eq S t ω
  have hη_src : sourceStepsize S t ω = some (stepsize S t ω) :=
    sourceStepsize_eq_some_stepsize_of_generated_boundary S hgenerated.1 t ω
  have hη_le : stepsize S t ω ≤ (1 : ℝ) / (4 * L) :=
    heta t ω (stepsize S t ω) hη_src
  have hη_nonneg : 0 ≤ stepsize S t ω :=
    le_of_lt (stepsize_pos_of_generated_quotient_boundary S hgenerated t ω)
  have hsmooth :=
    hF_smooth (iterate S t ω) (iterate S (t + 1) ω)
  exact smooth_descent_affine_update_with_direction_error
    S.objectiveValue (objectiveGradient S) (iterate S t ω)
    (iterate S (t + 1) ω) (direction S t ω) (error S t ω) L
    (stepsize S t ω) hsmooth hupdate herr hL_pos hη_nonneg hη_le

set_option maxHeartbeats 800000 in
/-- Lemma 3: the two centered fresh-sample cross terms vanish after expectation. -/
theorem lemma3_cross_terms_zero
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (t : ℕ)
    (hboundary : lemma3LocalQuotientBoundary S t) :
    sourceExpectationEqZero μ (lemma3FirstCrossTermExpr S t) ∧
      sourceExpectationEqZero μ (lemma3SecondCrossTermExpr S t) := by
  classical
  have hfresh_of_prefix_ae :
      ∀ {β : Type} [MeasurableSpace β] {wt : Ω → β},
        @prefixAEMeasurable Ω β _ _
          (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample)) wt μ →
          ProbabilityTheory.IndepFun wt (S.sample (t + 1)) μ := by
    intro β _ wt hwt
    exact
      section3_indepFun_sample_prefixAEMeasurable_future
        S μ hsec3 hwt (Nat.le_refl (t + 1))
  constructor
  · refine
      sourceExpectationEqZero_of_forall_eq_some μ (lemma3FirstCrossTermExpr S t)
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) ?_ ?_ ?_
    · intro ω
      exact lemma3FirstCrossTermExpr_eq_some_of_local_boundary S hboundary ω
    · have hquery_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
            (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              (iterate S (t + 1) ω,
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ := by
        exact
          lemma3_first_query_multiplier_prefixAEMeasurable_via_generated_history
            S μ hsec3 t
      have hquery :
          AEMeasurable
            (fun ω =>
              (iterate S (t + 1) ω,
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ :=
        prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
      have hsample : Measurable (S.sample (t + 1)) :=
        hsec3.sample_measurable (t + 1)
      have hindep :
          ProbabilityTheory.IndepFun
            (fun ω =>
              (iterate S (t + 1) ω,
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω))
            (S.sample (t + 1)) μ :=
        hfresh_of_prefix_ae hquery_prefix
      have hresidual_prod :
          AEStronglyMeasurable
            (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
              stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
            ((Measure.map
              (fun ω =>
                (iterate S (t + 1) ω,
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact
            section3_sampled_product_residual_aestronglyMeasurable
              S μ hsec3 (t + 1)
              (Measure.map
                (fun ω =>
                  (iterate S (t + 1) ω,
                    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                      error S t ω)) μ)
              (fun q : DecisionSpace d × DecisionSpace d => q.1)
              measurable_fst
      exact
        lemma3_first_cross_term_integrable_of_l2 S μ hsec3 t hboundary hquery hsample hindep
          hresidual_prod
    · have hquery_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
            (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              (iterate S (t + 1) ω,
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ := by
        exact
          lemma3_first_query_multiplier_prefixAEMeasurable_via_generated_history
            S μ hsec3 t
      have hquery :
          AEMeasurable
            (fun ω =>
              (iterate S (t + 1) ω,
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ := by
        exact prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
      have hsample : Measurable (S.sample (t + 1)) :=
        hsec3.sample_measurable (t + 1)
      have hindep :
          ProbabilityTheory.IndepFun
            (fun ω =>
              (iterate S (t + 1) ω,
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω))
            (S.sample (t + 1)) μ :=
        hfresh_of_prefix_ae hquery_prefix
      have hscalar_prod :
          AEStronglyMeasurable
            (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
              inner ℝ p.1.2
                (stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1))
            ((Measure.map
              (fun ω =>
                (iterate S (t + 1) ω,
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact lemma3_first_scalar_kernel_aestronglyMeasurable_sampled_product
            S μ hsec3 t
      have hresidual_prod :
          AEStronglyMeasurable
            (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
              stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
            ((Measure.map
              (fun ω =>
                (iterate S (t + 1) ω,
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact
            section3_sampled_product_residual_aestronglyMeasurable
              S μ hsec3 (t + 1)
              (Measure.map
                (fun ω =>
                  (iterate S (t + 1) ω,
                    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                      error S t ω)) μ)
              (fun q : DecisionSpace d × DecisionSpace d => q.1)
              measurable_fst
      have hinner_int :
          Integrable
            (fun ω =>
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω))
                (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ :=
        lemma3_first_cross_term_integrable_of_l2 S μ hsec3 t hboundary hquery hsample hindep
          hresidual_prod
      exact
        lemma3_first_cross_term_integral_eq_zero_of_sampled_product
          S μ t hquery hsample hindep hscalar_prod hinner_int
          (fun q =>
            (section3_fixed_gradient_residual_mean_zero_under_sample_law
              S μ hsec3 (t + 1) q.1).1)
          (fun q =>
            (section3_fixed_gradient_residual_mean_zero_under_sample_law
              S μ hsec3 (t + 1) q.1).2)
  · refine
      sourceExpectationEqZero_of_forall_eq_some μ (lemma3SecondCrossTermExpr S t)
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω) +
              objectiveGradient S (iterate S t ω))
            (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
              error S t ω)) ?_ ?_ ?_
    · intro ω
      exact lemma3SecondCrossTermExpr_eq_some_of_local_boundary S hboundary ω
    · have hquery_prefix :
          @prefixAEMeasurable Ω ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) _ _
            (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              ((iterate S (t + 1) ω, iterate S t ω),
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ := by
        exact
          lemma3_second_query_multiplier_prefixAEMeasurable_via_generated_history
            S μ hsec3 t
      have hquery :
          AEMeasurable
            (fun ω =>
              ((iterate S (t + 1) ω, iterate S t ω),
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ :=
        prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
      have hsample : Measurable (S.sample (t + 1)) :=
        hsec3.sample_measurable (t + 1)
      have hindep :
          ProbabilityTheory.IndepFun
            (fun ω =>
              ((iterate S (t + 1) ω, iterate S t ω),
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω))
            (S.sample (t + 1)) μ :=
        hfresh_of_prefix_ae hquery_prefix
      have hresidual_left :
          AEStronglyMeasurable
            (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
              stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1)
            ((Measure.map
              (fun ω =>
                ((iterate S (t + 1) ω, iterate S t ω),
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact
            section3_sampled_product_residual_aestronglyMeasurable
              S μ hsec3 (t + 1)
              (Measure.map
                (fun ω =>
                  ((iterate S (t + 1) ω, iterate S t ω),
                    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                      error S t ω)) μ)
              (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.1)
              (measurable_fst.comp measurable_fst)
      have hresidual_right :
          AEStronglyMeasurable
            (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
              stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)
            ((Measure.map
              (fun ω =>
                ((iterate S (t + 1) ω, iterate S t ω),
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact
            section3_sampled_product_residual_aestronglyMeasurable
              S μ hsec3 (t + 1)
              (Measure.map
                (fun ω =>
                  ((iterate S (t + 1) ω, iterate S t ω),
                    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                      error S t ω)) μ)
              (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.2)
              (measurable_snd.comp measurable_fst)
      exact
        lemma3_second_cross_term_integrable_of_l2 S μ hsec3 t hboundary hquery hsample hindep
          hresidual_left hresidual_right
    · have hquery_prefix :
          @prefixAEMeasurable Ω ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) _ _
            (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              ((iterate S (t + 1) ω, iterate S t ω),
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ := by
        exact
          lemma3_second_query_multiplier_prefixAEMeasurable_via_generated_history
            S μ hsec3 t
      have hquery :
          AEMeasurable
            (fun ω =>
              ((iterate S (t + 1) ω, iterate S t ω),
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ := by
        exact prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
      have hsample : Measurable (S.sample (t + 1)) :=
        hsec3.sample_measurable (t + 1)
      have hindep :
          ProbabilityTheory.IndepFun
            (fun ω =>
              ((iterate S (t + 1) ω, iterate S t ω),
                ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω))
            (S.sample (t + 1)) μ :=
        hfresh_of_prefix_ae hquery_prefix
      have hscalar_prod :
          AEStronglyMeasurable
            (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
              inner ℝ p.1.2
                ((stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1) -
                  (stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)))
            ((Measure.map
              (fun ω =>
                ((iterate S (t + 1) ω, iterate S t ω),
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact lemma3_second_scalar_kernel_aestronglyMeasurable_sampled_product
            S μ hsec3 t
      have hresidual_left :
          AEStronglyMeasurable
            (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
              stochasticGradient S p.1.1.1 p.2 - objectiveGradient S p.1.1.1)
            ((Measure.map
              (fun ω =>
                ((iterate S (t + 1) ω, iterate S t ω),
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact
            section3_sampled_product_residual_aestronglyMeasurable
              S μ hsec3 (t + 1)
              (Measure.map
                (fun ω =>
                  ((iterate S (t + 1) ω, iterate S t ω),
                    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                      error S t ω)) μ)
              (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.1)
              (measurable_fst.comp measurable_fst)
      have hresidual_right :
          AEStronglyMeasurable
            (fun p : ((DecisionSpace d × DecisionSpace d) × DecisionSpace d) × Sample =>
              stochasticGradient S p.1.1.2 p.2 - objectiveGradient S p.1.1.2)
            ((Measure.map
              (fun ω =>
                ((iterate S (t + 1) ω, iterate S t ω),
                  ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ).prod (Measure.map (S.sample (t + 1)) μ)) :=
        by
          exact
            section3_sampled_product_residual_aestronglyMeasurable
              S μ hsec3 (t + 1)
              (Measure.map
                (fun ω =>
                  ((iterate S (t + 1) ω, iterate S t ω),
                    ((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                      error S t ω)) μ)
              (fun q : (DecisionSpace d × DecisionSpace d) × DecisionSpace d => q.1.2)
              (measurable_snd.comp measurable_fst)
      have hinner_int :
          Integrable
            (fun ω =>
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω))
                (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) μ :=
        lemma3_second_cross_term_integrable_of_l2 S μ hsec3 t hboundary hquery hsample hindep
          hresidual_left hresidual_right
      exact
        lemma3_second_cross_term_integral_eq_zero_of_sampled_product
          S μ t hquery hsample hindep hscalar_prod hinner_int
          (fun x =>
            (section3_fixed_gradient_residual_mean_zero_under_sample_law
              S μ hsec3 (t + 1) x).1)
          (fun x =>
            (section3_fixed_gradient_residual_mean_zero_under_sample_law
              S μ hsec3 (t + 1) x).2)

/-- Lemma 2 pointwise error recursion: Algorithm 1 rewrites the next error as
the fresh residual, the fresh two-point residual difference, and the previous
error contribution. -/
private theorem lemma2_error_succ_three_term_decomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Setup Ω Sample E) (t : ℕ) (ω : Ω) :
    error S (t + 1) ω =
      nextMomentumWeight S t ω •
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)) +
        (1 - nextMomentumWeight S t ω) •
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω)) +
        (1 - nextMomentumWeight S t ω) • error S t ω := by
  exact recursive_momentum_residual_eq_three_term_of_update
    (direction S t ω) (direction S (t + 1) ω)
    (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω))
    (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω))
    (objectiveGradient S (iterate S (t + 1) ω))
    (objectiveGradient S (iterate S t ω)) (nextMomentumWeight S t ω)
    (direction_succ S t ω)

/-- Lemma 2's local quotient boundary makes the displayed stepsize denominator
nonzero at the selected time. -/
private theorem lemma2LocalQuotientBoundary_stepsize_ne_zero
    (S : Setup Ω Sample E) {L : ℝ} {t : ℕ}
    (hboundary : lemma2LocalQuotientBoundary S L t) (ω : Ω) :
    stepsize S t ω ≠ 0 := by
  rcases hboundary ω with ⟨_hεNext, _hη, hq, _ha, _hε, _hx, _hxNext, _hqRHS⟩
  exact (sourceQuotientValue_spec hq).1

private theorem nonempty_of_isProbabilityMeasure
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Nonempty Ω := by
  classical
  by_contra hempty
  have hEmpty : IsEmpty Ω := not_nonempty_iff.mp hempty
  have huniv_empty : (Set.univ : Set Ω) = ∅ := by
    ext ω
    exact False.elim (IsEmpty.false ω)
  have hμ_univ_zero : μ Set.univ = 0 := by
    rw [huniv_empty, measure_empty]
  have hμ_univ_one : μ Set.univ = 1 := measure_univ
  rw [hμ_univ_one] at hμ_univ_zero
  norm_num at hμ_univ_zero

/-- Lemma 2's local quotient boundary forces the displayed numerator `k` in
the adaptive stepsize quotient to be nonzero. -/
private theorem lemma2LocalQuotientBoundary_k_ne
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {L : ℝ} {t : ℕ}
    (hboundary : lemma2LocalQuotientBoundary S L t) :
    S.k ≠ 0 := by
  classical
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure μ
  have hη_ne : stepsize S t ω ≠ 0 :=
    lemma2LocalQuotientBoundary_stepsize_ne_zero S hboundary ω
  intro hk
  apply hη_ne
  simp [stepsize, adaptiveStepsize, hk]

/-- The reciprocal of the totalized adaptive stepsize is continuous on any
compact cumulative-gradient range once Lemma 2's local boundary has ruled out
`k = 0`. -/
private theorem lemma2_reciprocal_stepsize_of_sumSq_continuousOn_Icc
    (S : Setup Ω Sample E) {R : ℝ} (hk_ne : S.k ≠ 0) :
    ContinuousOn
      (fun sumSq : ℝ => 1 / adaptiveStepsize S sumSq)
      (Set.Icc 0 R) := by
  simpa [adaptiveStepsize] using
    SOptLib.inverse_rpow_step_size_reciprocal_continuousOn_Icc
      S.k S.w ((1 : ℝ) / 3) R (by norm_num)

private theorem lemma2_reciprocal_stepsize_of_sumSq_measurable
    (S : Setup Ω Sample E) :
    Measurable (fun sumSq : ℝ => 1 / adaptiveStepsize S sumSq) := by
  have hden :
      Measurable
        (fun sumSq : ℝ =>
          Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) := by
    exact
      (Real.continuous_rpow_const
        (by norm_num : 0 ≤ ((1 : ℝ) / 3))).measurable.comp
        (measurable_const.add measurable_id)
  have hη :
      Measurable
        (fun sumSq : ℝ =>
          S.k / Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)) :=
    measurable_const.div hden
  change
    Measurable
      (fun sumSq : ℝ =>
        (1 : ℝ) / (S.k / Real.rpow (S.w + sumSq) ((1 : ℝ) / 3)))
  exact (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).div hη

private theorem lemma2_reciprocal_stepsize_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω => 1 / stepsize S t ω) μ := by
  have hsum :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ :=
    lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ hsec3 t
  refine
    (hsum.comp_measurable
      (lemma2_reciprocal_stepsize_of_sumSq_measurable S)).congr ?_
  filter_upwards with ω
  rfl

/-- Lemma 2's local quotient boundary supplies the reciprocal-stepsize
boundedness needed by the local integrability route, without upgrading to the
global generated quotient boundary. -/
private theorem lemma2_local_reciprocal_stepsize_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : lemma2LocalQuotientBoundary S L t) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ω ∂μ, ‖1 / stepsize S t ω‖ ≤ A := by
  classical
  rcases lemma3_cumulativeGradientNormSq_eventually_le S μ hsec3 t with
    ⟨R, _hR_nonneg, hR⟩
  have hk_ne : S.k ≠ 0 :=
    lemma2LocalQuotientBoundary_k_ne S μ hboundary
  let recipOfSumSq : ℝ → ℝ := fun sumSq => 1 / adaptiveStepsize S sumSq
  have hcompact : IsCompact (Set.Icc (0 : ℝ) R) := isCompact_Icc
  have hcont : ContinuousOn recipOfSumSq (Set.Icc (0 : ℝ) R) := by
    simpa [recipOfSumSq] using
      lemma2_reciprocal_stepsize_of_sumSq_continuousOn_Icc S hk_ne
  rcases exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      recipOfSumSq hcompact hcont with ⟨A, hA_nonneg, hA⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hR] with ω hωR
  have hmem : cumulativeGradientNormSq S t ω ∈ Set.Icc (0 : ℝ) R :=
    ⟨cumulativeGradientNormSq_nonneg S t ω, hωR⟩
  simpa [recipOfSumSq, stepsize] using
    hA (cumulativeGradientNormSq S t ω) hmem

/-- Generated-boundary reciprocal bound for Lemma 2.

This is the source/coarser supplier used by the active Lemma 2 route.  The
local-only reciprocal helper above is retained as legacy route-local evidence,
but source-facing Lemma 2 now starts from Algorithm 1's generated quotient
boundary. -/
private theorem lemma2_generated_reciprocal_stepsize_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ω ∂μ, ‖1 / stepsize S t ω‖ ≤ A := by
  classical
  rcases lemma3_cumulativeGradientNormSq_eventually_le S μ hsec3 t with
    ⟨R, _hR_nonneg, hR⟩
  let recipOfSumSq : ℝ → ℝ := fun sumSq => 1 / adaptiveStepsize S sumSq
  have hcompact : IsCompact (Set.Icc (0 : ℝ) R) := isCompact_Icc
  have hcont : ContinuousOn recipOfSumSq (Set.Icc (0 : ℝ) R) := by
    simpa [recipOfSumSq] using
      lemma2_reciprocal_stepsize_of_sumSq_continuousOn_Icc S (ne_of_gt hboundary.2)
  rcases exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      recipOfSumSq hcompact hcont with ⟨A, hA_nonneg, hA⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hR] with ω hωR
  have hmem : cumulativeGradientNormSq S t ω ∈ Set.Icc (0 : ℝ) R :=
    ⟨cumulativeGradientNormSq_nonneg S t ω, hωR⟩
  simpa [recipOfSumSq, stepsize] using
    hA (cumulativeGradientNormSq S t ω) hmem

/-- LHS integrability for Lemma 2 reduces to the two local boundedness facts:
bounded next error and bounded reciprocal stepsize. -/
private theorem lemma2_lhs_integrable_of_error_and_reciprocal_bounds
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (herr :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂μ, ‖error S (t + 1) ω‖ ≤ B)
    (hrecip :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ω ∂μ, ‖1 / stepsize S t ω‖ ≤ A) :
    Integrable (fun ω => ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω) μ := by
  classical
  rcases herr with ⟨B, _hB_nonneg, hB⟩
  rcases hrecip with ⟨A, hA_nonneg, hA⟩
  have herr_sq_aesm :
      AEStronglyMeasurable (fun ω => ‖error S (t + 1) ω‖ ^ 2) μ := by
    have herror_prefix :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          (error S (t + 1)) μ :=
      lemma3_error_prefixAEMeasurable S μ hsec3 (t + 1)
    exact
      (prefixAEMeasurable.aemeasurable S μ hsec3
        (prefixAEMeasurable.norm_sq herror_prefix)).aestronglyMeasurable
  have hrecip_aesm :
      AEStronglyMeasurable (fun ω => 1 / stepsize S t ω) μ := by
    have hrecip_prefix :=
      lemma2_reciprocal_stepsize_prefixAEMeasurable S μ hsec3 t
    exact
      (prefixAEMeasurable.aemeasurable S μ hsec3 hrecip_prefix).aestronglyMeasurable
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω => ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω) μ := by
    refine (herr_sq_aesm.mul hrecip_aesm).congr ?_
    filter_upwards with ω
    simp [Pi.mul_apply, div_eq_mul_inv]
  refine Integrable.of_bound hZ_aesm (C := B ^ 2 * A) ?_
  filter_upwards [hB, hA] with ω hBω hAω
  rw [div_eq_mul_one_div, norm_mul]
  have hsquare :
      ‖‖error S (t + 1) ω‖ ^ 2‖ ≤ B ^ 2 := by
    have hsquare' : ‖error S (t + 1) ω‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hBω 2
    simpa [Real.norm_of_nonneg (sq_nonneg ‖error S (t + 1) ω‖)] using hsquare'
  exact mul_le_mul hsquare hAω (norm_nonneg _) (sq_nonneg B)

/-- Generated finite-history bound for the next Lemma 2 error term.

This is the concrete replacement for the failed local-only subgoal
`∃ B, ‖ε_{t+1}‖ ≤ B`: it is obtained from the generated STORM history and
Section 3's `G`-Lipschitz loss assumption, not from pointwise source quotient
success. -/
private theorem lemma2_generated_next_error_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ ω ∂μ, ‖error S (t + 1) ω‖ ≤ B := by
  have hlemma3 : lemma3LocalQuotientBoundary S (t + 1) := by
    exact lemma3LocalQuotientBoundary_of_generated_boundary S hboundary (t + 1)
  exact lemma3_generated_error_eventually_bound S μ hsec3 (t + 1) hlemma3

/-- Generated finite-history bound for the displayed Lemma 2 stepsize. -/
private theorem lemma2_generated_stepsize_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ω ∂μ, ‖stepsize S t ω‖ ≤ A := by
  classical
  rcases lemma3_cumulativeGradientNormSq_eventually_le S μ hsec3 t with
    ⟨R, _hR_nonneg, hR⟩
  let etaOfSumSq : ℝ → ℝ := fun sumSq => adaptiveStepsize S sumSq
  have hw_pos : 0 < S.w := hboundary.1.1.1
  have hcompact : IsCompact (Set.Icc (0 : ℝ) R) := isCompact_Icc
  have hcont : ContinuousOn etaOfSumSq (Set.Icc (0 : ℝ) R) := by
    have hbase_pos :
        ∀ x ∈ Set.Icc (0 : ℝ) R, 0 < stepsizeBase S x := by
      intro x hx
      exact add_pos_of_pos_of_nonneg hw_pos hx.1
    have hden_ne :
        ∀ x ∈ Set.Icc (0 : ℝ) R, stepsizeDenominator S x ≠ 0 := by
      intro x hx
      exact ne_of_gt (Real.rpow_pos_of_pos (hbase_pos x hx) ((1 : ℝ) / 3))
    have hden_cont :
        ContinuousOn (fun x : ℝ => stepsizeDenominator S x) (Set.Icc 0 R) := by
      simpa [stepsizeDenominator, stepsizeBase] using
        ((Real.continuous_rpow_const
          (by norm_num : 0 ≤ ((1 : ℝ) / 3))).comp
            (continuous_const.add continuous_id)).continuousOn
    simpa [etaOfSumSq, adaptiveStepsize, SOptLib.inverse_rpow_step_size,
      stepsizeDenominator, stepsizeBase, div_eq_mul_inv] using
      continuousOn_const.mul (hden_cont.inv₀ hden_ne)
  rcases exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      etaOfSumSq hcompact hcont with ⟨A, hA_nonneg, hA⟩
  refine ⟨A, hA_nonneg, ?_⟩
  filter_upwards [hR] with ω hωR
  have hmem : cumulativeGradientNormSq S t ω ∈ Set.Icc (0 : ℝ) R :=
    ⟨cumulativeGradientNormSq_nonneg S t ω, hωR⟩
  simpa [etaOfSumSq, stepsize] using
    hA (cumulativeGradientNormSq S t ω) hmem

/-- Generated-run integrability of Lemma 1's totalized left representative.

This is the generated-boundary replacement for the old local-boundary
well-definedness leaf.  It is proved from generated iterate measurability,
generated stepsize/direction boundedness, and Section 3's derived
`G`-Lipschitz objective-value control. -/
private theorem lemma1_lhs_integrable_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (t : ℕ) :
    Integrable
      (fun ω =>
        S.objectiveValue (iterate S (t + 1) ω) -
          S.objectiveValue (iterate S t ω)) μ := by
  classical
  have hF_meas : Measurable S.objectiveValue :=
    section3_objectiveValue_measurable S μ hsec3 0
  have hnext_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => S.objectiveValue (iterate S (t + 1) ω)) μ :=
    (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t).comp_measurable hF_meas
  have hcur_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => S.objectiveValue (iterate S t ω)) μ :=
    (lemma3_iterate_prefixAEMeasurable S μ hsec3 t).comp_measurable hF_meas
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω =>
          S.objectiveValue (iterate S (t + 1) ω) -
            S.objectiveValue (iterate S t ω)) μ :=
    ((prefixAEMeasurable.aemeasurable S μ hsec3 hnext_prefix).aestronglyMeasurable).sub
      ((prefixAEMeasurable.aemeasurable S μ hsec3 hcur_prefix).aestronglyMeasurable)
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 t hgenerated with
    ⟨Aη, hAη_nonneg, hAη⟩
  have hloc3 : lemma3LocalQuotientBoundary S t :=
    lemma3LocalQuotientBoundary_of_generated_boundary S hgenerated t
  rcases lemma3_generated_direction_eventually_bound S μ hsec3 t hloc3 with
    ⟨D, _hD_nonneg, hD⟩
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  refine Integrable.of_bound hZ_aesm (C := G * (Aη * D)) ?_
  filter_upwards [hAη, hD] with ω hηω hDω
  have hdiff :
      iterate S (t + 1) ω - iterate S t ω =
        -stepsize S t ω • direction S t ω := by
    rw [iterate_succ]
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have hdist_bound :
      ‖iterate S (t + 1) ω - iterate S t ω‖ ≤ Aη * D := by
    rw [hdiff, norm_smul, norm_neg]
    exact mul_le_mul hηω hDω (norm_nonneg _) hAη_nonneg
  have hobj_bound :
      ‖S.objectiveValue (iterate S (t + 1) ω) -
          S.objectiveValue (iterate S t ω)‖ ≤
        G * ‖iterate S (t + 1) ω - iterate S t ω‖ :=
    section3_objectiveValue_norm_sub_le_mul S μ hsec3 0
      (iterate S t ω) (iterate S (t + 1) ω)
  exact le_trans hobj_bound
    (by
      nlinarith [mul_le_mul_of_nonneg_left hdist_bound hG_nonneg])

/-- Source-shaped a.e.-prefix adaptedness for the Lemma 2 displayed stepsize. -/
private theorem lemma2_stepsize_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (stepsize S t) μ := by
  have hsum :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ :=
    lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ hsec3 t
  refine (hsum.comp_measurable (lemma3_adaptiveStepsize_measurable S)).congr ?_
  filter_upwards with ω
  rfl

/-- Source-shaped a.e.-prefix adaptedness for the Lemma 2 factor `1-a_{t+1}`. -/
private theorem lemma2_one_sub_momentum_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω => 1 - nextMomentumWeight S t ω) μ := by
  have hsum :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ :=
    lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ hsec3 t
  refine
    (hsum.comp_measurable
      (lemma3_one_sub_momentumWeight_of_sumSq_measurable S)).congr ?_
  filter_upwards with ω
  rfl

/-- Measurability of the scalar coefficient that appears in Lemma 2's first
fresh-residual/previous-error cross term after expanding the square. -/
private theorem lemma2_first_cross_scalar_of_sumSq_measurable
    (S : Setup Ω Sample E) :
    Measurable
      (fun sumSq : ℝ =>
        2 * momentumWeight S (adaptiveStepsize S sumSq) *
          (1 - momentumWeight S (adaptiveStepsize S sumSq)) /
            adaptiveStepsize S sumSq) := by
  have hη := lemma3_adaptiveStepsize_measurable S
  have hηsq :
      Measurable (fun sumSq : ℝ => adaptiveStepsize S sumSq ^ 2) := by
    convert hη.mul hη using 1
    ext sumSq
    ring
  have ha : Measurable (fun sumSq : ℝ => momentumWeight S (adaptiveStepsize S sumSq)) := by
    simpa [momentumWeight] using measurable_const.mul hηsq
  exact (((measurable_const.mul ha).mul (measurable_const.sub ha)).div hη)

/-- Source-shaped a.e.-prefix adaptedness for Lemma 2's first-cross
coefficient `2 a_t (1-a_t) / η_t`. -/
private theorem lemma2_first_cross_scalar_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
          stepsize S t ω) μ := by
  have hsum :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ :=
    lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ hsec3 t
  refine
    (hsum.comp_measurable
      (lemma2_first_cross_scalar_of_sumSq_measurable S)).congr ?_
  filter_upwards with ω
  rfl

/-- A.e.-prefix adapted random query for Lemma 2's coefficient-specific first
cross term. -/
private theorem lemma2_first_cross_query_multiplier_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        (iterate S (t + 1) ω,
          (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
            stepsize S t ω) • error S t ω)) μ := by
  exact
    (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t).prod
      ((lemma2_first_cross_scalar_prefixAEMeasurable S μ hsec3 t).real_smul
        (lemma3_error_prefixAEMeasurable S μ hsec3 t))

/-- Compact-range bound for Lemma 2's first-cross scalar coefficient
`2 a_t (1-a_t) / η_t`. -/
private theorem lemma2_first_cross_scalar_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᵐ ω ∂μ,
        ‖2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
          stepsize S t ω‖ ≤ A := by
  classical
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 t hboundary with
    ⟨Aη, hAη_nonneg, hAη⟩
  rcases lemma2_generated_reciprocal_stepsize_eventually_bound S μ hsec3 t hboundary with
    ⟨Aηinv, hAηinv_nonneg, hAηinv⟩
  have hloc3 : lemma3LocalQuotientBoundary S t :=
    lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t
  rcases lemma3_generated_one_sub_momentum_eventually_bound S μ hsec3 t hloc3 with
    ⟨Aa, hAa_nonneg, hAa⟩
  refine ⟨2 * ‖S.c‖ * Aη ^ 2 * Aa * Aηinv, by positivity, ?_⟩
  filter_upwards [hAη, hAηinv, hAa] with ω hηω hηinvω haω
  set η : ℝ := stepsize S t ω
  set a : ℝ := 1 - nextMomentumWeight S t ω
  have hη_bound : ‖η‖ ≤ Aη := by simpa [η] using hηω
  have hηinv_bound : ‖1 / η‖ ≤ Aηinv := by simpa [η] using hηinvω
  have ha_bound : ‖a‖ ≤ Aa := by simpa [a] using haω
  have hnext_bound : ‖nextMomentumWeight S t ω‖ ≤ ‖S.c‖ * Aη ^ 2 := by
    have hη_sq : ‖η‖ ^ 2 ≤ Aη ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg η) hη_bound 2
    calc
      ‖nextMomentumWeight S t ω‖
          = ‖S.c‖ * ‖η‖ ^ 2 := by
            simp [nextMomentumWeight, momentumWeight, η, norm_mul, norm_pow]
      _ ≤ ‖S.c‖ * Aη ^ 2 :=
          mul_le_mul_of_nonneg_left hη_sq (norm_nonneg S.c)
  calc
    ‖2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
        stepsize S t ω‖
        = ‖2 * nextMomentumWeight S t ω * a * (1 / η)‖ := by
          exact congrArg norm (by
            dsimp [a, η]
            rw [div_eq_mul_one_div])
    _ = 2 * ‖nextMomentumWeight S t ω‖ * ‖a‖ * ‖1 / η‖ := by
          simp [norm_mul]
    _ ≤ 2 * (‖S.c‖ * Aη ^ 2) * Aa * Aηinv := by
          exact mul_le_mul
            (mul_le_mul
              (mul_le_mul_of_nonneg_left hnext_bound (by norm_num : (0 : ℝ) ≤ 2))
              ha_bound (norm_nonneg a)
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
                (mul_nonneg (norm_nonneg S.c) (pow_nonneg hAη_nonneg 2))))
            hηinv_bound (norm_nonneg _)
            (mul_nonneg
              (mul_nonneg (by positivity)
                (mul_nonneg (norm_nonneg S.c) (pow_nonneg hAη_nonneg 2)))
              hAa_nonneg)
    _ = 2 * ‖S.c‖ * Aη ^ 2 * Aa * Aηinv := by ring

/-- Lemma 2 first-cross multiplier square-integrability for the actual
coefficient produced by the norm expansion. -/
private theorem lemma2_first_cross_multiplier_sq_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    Integrable
      (fun ω =>
        ‖(2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
          stepsize S t ω) • error S t ω‖ ^ 2) μ := by
  have hmult_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
            stepsize S t ω) • error S t ω) μ :=
    (lemma2_first_cross_scalar_prefixAEMeasurable S μ hsec3 t).real_smul
      (lemma3_error_prefixAEMeasurable S μ hsec3 t)
  have hmult_aesm :
      AEStronglyMeasurable
        (fun ω =>
          (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
            stepsize S t ω) • error S t ω) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3 hmult_prefix).aestronglyMeasurable
  rcases lemma2_first_cross_scalar_eventually_bound S μ hsec3 t hboundary with
    ⟨A, hA_nonneg, hA⟩
  have hloc3 : lemma3LocalQuotientBoundary S t :=
    lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t
  rcases lemma3_generated_error_eventually_bound S μ hsec3 t hloc3 with
    ⟨B, _hB_nonneg, hB⟩
  have hbounded : ∃ C : ℝ, ∀ᵐ ω ∂μ,
      ‖(2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
        stepsize S t ω) • error S t ω‖ ≤ C := by
    refine ⟨A * B, ?_⟩
    filter_upwards [hA, hB] with ω hAω hBω
    simpa [norm_smul] using
      mul_le_mul hAω hBω (norm_nonneg _) hA_nonneg
  rcases hbounded with ⟨C, hC⟩
  exact (SOptLib.integrable_sq_norm_of_ae_bound hmult_aesm hC).1

/-- Coefficient-specific first fresh-residual cross cancellation used by the
Lemma 2 norm expansion.  Lemma 3's printed statement has multiplier
`η_t⁻¹(1-a_t)^2 ε_t`; this helper proves the same adapted/fresh cancellation
for the actual expansion coefficient `2 a_t(1-a_t)η_t⁻¹ ε_t`. -/
private theorem lemma2_adapted_weighted_first_cross_integral_eq_zero
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    Integrable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
              stepsize S t ω) • error S t ω)) μ ∧
      ∫ ω,
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
              stepsize S t ω) • error S t ω) ∂μ = 0 := by
  classical
  have hquery_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          (iterate S (t + 1) ω,
            (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
              stepsize S t ω) • error S t ω)) μ :=
    lemma2_first_cross_query_multiplier_prefixAEMeasurable S μ hsec3 t
  have hquery :
      AEMeasurable
        (fun ω =>
          (iterate S (t + 1) ω,
            (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
              stepsize S t ω) • error S t ω)) μ :=
    prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
  have hsample : Measurable (S.sample (t + 1)) :=
    hsec3.sample_measurable (t + 1)
  have hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          (iterate S (t + 1) ω,
            (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
              stepsize S t ω) • error S t ω))
        (S.sample (t + 1)) μ :=
    section3_indepFun_sample_prefixAEMeasurable_future
      S μ hsec3 hquery_prefix (Nat.le_refl (t + 1))
  have hresidual_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
                stepsize S t ω) • error S t ω)) μ).prod
          (Measure.map (S.sample (t + 1)) μ)) :=
    section3_sampled_product_residual_aestronglyMeasurable
      S μ hsec3 (t + 1)
      (Measure.map
        (fun ω =>
          (iterate S (t + 1) ω,
            (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
              stepsize S t ω) • error S t ω)) μ)
      (fun q : DecisionSpace d × DecisionSpace d => q.1)
      measurable_fst
  have hres_aesm : AEStronglyMeasurable
      (fun ω =>
        stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
          objectiveGradient S (iterate S (t + 1) ω)) μ :=
    aestronglyMeasurable_comp_of_indep_product_law
      (A := DecisionSpace d × DecisionSpace d) (B := Sample)
      (X := fun ω =>
        (iterate S (t + 1) ω,
          (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
            stepsize S t ω) • error S t ω))
      (Y := S.sample (t + 1))
      (φ := fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
        stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1)
      hquery hsample.aemeasurable hindep hresidual_prod
  have hmult_aesm : AEStronglyMeasurable
      (fun ω =>
        (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
          stepsize S t ω) • error S t ω) μ := by
    have htmp :=
      (measurable_snd.aestronglyMeasurable).comp_aemeasurable hquery
    simpa [Function.comp_def] using htmp
  have hres_sq :
      Integrable
        (fun ω =>
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2) μ := by
    let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
      (iterate S (t + 1) ω,
        (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
          stepsize S t ω) • error S t ω)
    let sample : Ω → Sample := S.sample (t + 1)
    let φ : (DecisionSpace d × DecisionSpace d) → Sample → ℝ := fun q ξ =>
      ‖stochasticGradient S q.1 ξ - objectiveGradient S q.1‖ ^ 2
    have hφ_prod :
        AEStronglyMeasurable
          (fun p : (DecisionSpace d × DecisionSpace d) × Sample => φ p.1 p.2)
          ((Measure.map query μ).prod (Measure.map sample μ)) := by
      convert hresidual_prod.norm.mul hresidual_prod.norm using 1
      ext p
      simp [φ, pow_two]
    have hfixed :
        ∀ q : DecisionSpace d × DecisionSpace d,
          Integrable (fun ξ => φ q ξ) (Measure.map sample μ) ∧
            ∫ ξ, φ q ξ ∂Measure.map sample μ ≤ σ ^ 2 := by
      intro q
      simpa [sample, φ] using
        section3_sampled_product_residual_fixed_variance_bound
          S μ hsec3 (t + 1)
          (fun q : DecisionSpace d × DecisionSpace d => q.1) q
    simpa [sample, φ] using
      integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
        (P := μ) (ν := Measure.map sample μ)
        (φ := φ) (X := query) (Y := sample) (C := σ ^ 2)
        hφ_prod
        (by simpa [query] using hquery)
        (by simpa [sample] using hsample.aemeasurable)
        (by simpa [query, sample] using hindep)
        rfl
        (by intro q ξ; exact sq_nonneg _)
        (sq_nonneg σ)
        (fun q => (hfixed q).1)
        (fun q => (hfixed q).2)
  have hmult_sq :
      Integrable
        (fun ω =>
          ‖(2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
            stepsize S t ω) • error S t ω‖ ^ 2) μ :=
    lemma2_first_cross_multiplier_sq_integrable S μ hsec3 t hboundary
  have hinner_int :
      Integrable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
              stepsize S t ω) • error S t ω)) μ :=
    integrable_inner_of_integrable_sq_norm hres_aesm hmult_aesm hres_sq hmult_sq
  have hscalar_prod :
      AEStronglyMeasurable
        (fun p : (DecisionSpace d × DecisionSpace d) × Sample =>
          inner ℝ p.1.2
            (stochasticGradient S p.1.1 p.2 - objectiveGradient S p.1.1))
        ((Measure.map
          (fun ω =>
            (iterate S (t + 1) ω,
              (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
                stepsize S t ω) • error S t ω)) μ).prod
          (Measure.map (S.sample (t + 1)) μ)) :=
    by
      have hdir :
          AEStronglyMeasurable
            (fun p : (DecisionSpace d × DecisionSpace d) × Sample => p.1.2)
            ((Measure.map
              (fun ω =>
                (iterate S (t + 1) ω,
                  (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
                    stepsize S t ω) • error S t ω)) μ).prod
              (Measure.map (S.sample (t + 1)) μ)) :=
        (measurable_snd.comp measurable_fst).aestronglyMeasurable
      exact hdir.inner hresidual_prod
  let query : Ω → DecisionSpace d × DecisionSpace d := fun ω =>
    (iterate S (t + 1) ω,
      (2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
        stepsize S t ω) • error S t ω)
  let sample : Ω → Sample := S.sample (t + 1)
  let φ : DecisionSpace d × DecisionSpace d → Sample → ℝ := fun q ξ =>
    inner ℝ q.2 (stochasticGradient S q.1 ξ - objectiveGradient S q.1)
  have hfixed_scalar_zero :
      ∀ q : DecisionSpace d × DecisionSpace d,
        ∫ ξ, φ q ξ ∂Measure.map sample μ = 0 := by
    intro q
    have hzero :=
      inner_integral_oracle_residual_eq_zero_of_integral_eq_zero
        (μ := Measure.map sample μ) (G := stochasticGradient S)
        (target := objectiveGradient S) q.1 q.2
        (by
          simpa [sample] using
            (section3_fixed_gradient_residual_mean_zero_under_sample_law
              S μ hsec3 (t + 1) q.1).1)
        (by
          simpa [sample] using
            (section3_fixed_gradient_residual_mean_zero_under_sample_law
              S μ hsec3 (t + 1) q.1).2)
    simpa [φ, real_inner_comm] using hzero
  have hzero :=
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := μ) (ν := Measure.map sample μ) (φ := φ) (X := query) (Y := sample)
      (by simpa [query, sample, φ] using hscalar_prod)
      (by simpa [query] using hquery)
      (by simpa [sample] using hsample.aemeasurable)
      (by simpa [query, sample] using hindep)
      rfl
      (by simpa [query, sample, φ, real_inner_comm] using hinner_int)
      hfixed_scalar_zero
  exact ⟨hinner_int, by simpa [query, sample, φ, real_inner_comm] using hzero⟩

/-- Weighted Hilbert centering contraction for the Lemma 2 source-square
replacements.  The stochastic content is isolated in the weighted centered
cross identity; this lemma only expands the square and drops the nonnegative
center norm. -/
private theorem integral_weighted_norm_sq_sub_le_integral_weighted_norm_sq_of_inner_sub_zero
    [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) {w : Ω → ℝ} {g m : Ω → E}
    (hw_nonneg : ∀ᵐ ω ∂μ, 0 ≤ w ω)
    (hwg_sq : Integrable (fun ω => w ω * ‖g ω‖ ^ 2) μ)
    (hwm_sq : Integrable (fun ω => w ω * ‖m ω‖ ^ 2) μ)
    (hcenter_int :
      Integrable (fun ω => w ω * inner ℝ (m ω) (g ω - m ω)) μ)
    (hcenter_zero :
      ∫ ω, w ω * inner ℝ (m ω) (g ω - m ω) ∂μ = 0) :
    ∫ ω, w ω * ‖g ω - m ω‖ ^ 2 ∂μ ≤
      ∫ ω, w ω * ‖g ω‖ ^ 2 ∂μ := by
  exact integral_weighted_norm_sq_sub_le_of_centered_inner_eq_zero
    μ hw_nonneg hwg_sq hwm_sq hcenter_int hcenter_zero

/-- Measurability of Lemma 2's fresh centered-square weight
`2 c^2 η_t^3` as a function of the generated cumulative square sum. -/
private theorem lemma2_fresh_square_weight_of_sumSq_measurable
    (S : Setup Ω Sample E) :
    Measurable
      (fun sumSq : ℝ => 2 * S.c ^ 2 * adaptiveStepsize S sumSq ^ 3) := by
  have hη := lemma3_adaptiveStepsize_measurable S
  have hη3 : Measurable (fun sumSq : ℝ => adaptiveStepsize S sumSq ^ 3) := by
    convert hη.mul (hη.mul hη) using 1
    ext sumSq
    ring
  exact measurable_const.mul hη3

/-- Source-shaped a.e.-prefix adaptedness for the equation (5) fresh
centered-square weight `2 c^2 η_t^3`. -/
private theorem lemma2_fresh_square_weight_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω => 2 * S.c ^ 2 * stepsize S t ω ^ 3) μ := by
  have hsum :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ :=
    lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ hsec3 t
  refine
    (hsum.comp_measurable
      (lemma2_fresh_square_weight_of_sumSq_measurable S)).congr ?_
  filter_upwards with ω
  rfl

/-- A.e.-prefix adapted random query for equation (5)'s weighted fresh
residual/objective-gradient cross identity. -/
private theorem lemma2_fresh_square_objective_query_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d × DecisionSpace d) _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        (iterate S (t + 1) ω,
          (2 * S.c ^ 2 * stepsize S t ω ^ 3) •
            objectiveGradient S (iterate S (t + 1) ω))) μ := by
  have hx :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ :=
    lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t
  have hobj :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S (t + 1) ω)) μ :=
    hx.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  exact
    hx.prod
      ((lemma2_fresh_square_weight_prefixAEMeasurable S μ hsec3 t).real_smul hobj)

/-- Generic adapted/fresh residual cross cancellation for Lemma 2 square
replacements.  The random query packages the adapted evaluation point and the
adapted direction against which the fresh residual is scalarized. -/
private theorem lemma2_adapted_fresh_residual_inner_integral_eq_zero_of_query_l2
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (n : ℕ)
    {query : Ω → DecisionSpace d × DecisionSpace d}
    (hquery : AEMeasurable query μ)
    (hsample : Measurable (S.sample n))
    (hindep : ProbabilityTheory.IndepFun query (S.sample n) μ)
    (hdir_sq : Integrable (fun ω => ‖(query ω).2‖ ^ 2) μ) :
    Integrable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (query ω).1 (S.sample n ω) -
              objectiveGradient S (query ω).1)
            (query ω).2) μ ∧
      ∫ ω,
          inner ℝ
            (stochasticGradient S (query ω).1 (S.sample n ω) -
              objectiveGradient S (query ω).1)
            (query ω).2 ∂μ = 0 := by
  exact
    randomQuery_inner_oracleResidual_integrable_and_integral_eq_zero_of_l2
      (P := μ) (ν := Measure.map (S.sample n) μ)
      (query := query) (sample := S.sample n)
      (G := stochasticGradient S) (target := objectiveGradient S)
      (varianceBudget := σ ^ 2)
      (section3_sampled_product_residual_aestronglyMeasurable
        S μ hsec3 n (Measure.map query μ)
        (fun q : DecisionSpace d × DecisionSpace d => q.1) measurable_fst)
      hquery hsample.aemeasurable hindep rfl
      (fun x =>
        (section3_fixed_gradient_residual_mean_zero_under_sample_law
          S μ hsec3 n x).1)
      (fun x =>
        (section3_fixed_gradient_residual_mean_zero_under_sample_law
          S μ hsec3 n x).2)
      (fun x =>
        (section3_sample_law_gradient_residual_sq_integrable_and_le
          S μ hsec3 n x).1)
      (fun x =>
        (section3_sample_law_gradient_residual_sq_integrable_and_le
          S μ hsec3 n x).2)
      hdir_sq

/-- Square-integrability of equation (5)'s adapted weighted objective-gradient
direction. -/
private theorem lemma2_fresh_square_objective_multiplier_sq_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    Integrable
      (fun ω =>
        ‖(2 * S.c ^ 2 * stepsize S t ω ^ 3) •
          objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2) μ := by
  have hquery_prefix :=
    lemma2_fresh_square_objective_query_prefixAEMeasurable S μ hsec3 t
  have hquery :
      AEMeasurable
        (fun ω =>
          (iterate S (t + 1) ω,
            (2 * S.c ^ 2 * stepsize S t ω ^ 3) •
              objectiveGradient S (iterate S (t + 1) ω))) μ :=
    prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
  have hmult_aesm :
      AEStronglyMeasurable
        (fun ω =>
          (2 * S.c ^ 2 * stepsize S t ω ^ 3) •
            objectiveGradient S (iterate S (t + 1) ω)) μ :=
    (measurable_snd.aestronglyMeasurable).comp_aemeasurable hquery
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 t hboundary with
    ⟨Aη, hAη_nonneg, hAη⟩
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  have hbounded :
      ∀ᵐ ω ∂μ,
        ‖(2 * S.c ^ 2 * stepsize S t ω ^ 3) •
          objectiveGradient S (iterate S (t + 1) ω)‖ ≤
            2 * S.c ^ 2 * Aη ^ 3 * G := by
    filter_upwards [hAη] with ω hηω
    have hη_bound : ‖stepsize S t ω‖ ≤ Aη := hηω
    have hη3_bound : ‖stepsize S t ω‖ ^ 3 ≤ Aη ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hη_bound 3
    have hobj :
        ‖objectiveGradient S (iterate S (t + 1) ω)‖ ≤ G :=
      section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S (t + 1) ω)
    have hcoef :
        ‖2 * S.c ^ 2 * stepsize S t ω ^ 3‖ ≤
          2 * S.c ^ 2 * Aη ^ 3 := by
      calc
        ‖2 * S.c ^ 2 * stepsize S t ω ^ 3‖
            = 2 * S.c ^ 2 * ‖stepsize S t ω‖ ^ 3 := by
              simp [norm_mul, norm_pow,
                Real.norm_of_nonneg
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S.c))]
        _ ≤ 2 * S.c ^ 2 * Aη ^ 3 := by
              exact mul_le_mul_of_nonneg_left hη3_bound
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S.c))
    simpa [norm_smul] using
          mul_le_mul hcoef hobj (norm_nonneg _) (by positivity)
  exact (SOptLib.integrable_sq_norm_of_ae_bound hmult_aesm hbounded).1

/-- Integrability of the fresh equation (5) weight times a bounded
prefix-measurable squared norm. -/
private theorem lemma2_fresh_square_weighted_norm_sq_integrable_of_ae_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S)
    {v : Ω → DecisionSpace d}
    (hv_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        v μ)
    (hv_bound : ∀ᵐ ω ∂μ, ‖v ω‖ ≤ G) :
    Integrable
      (fun ω => 2 * S.c ^ 2 * stepsize S t ω ^ 3 * ‖v ω‖ ^ 2) μ := by
  have hmono :
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hw_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => 2 * S.c ^ 2 * stepsize S t ω ^ 3) μ :=
    (lemma2_fresh_square_weight_prefixAEMeasurable S μ hsec3 t).mono hmono
  have hw_aesm :
      AEStronglyMeasurable
        (fun ω => 2 * S.c ^ 2 * stepsize S t ω ^ 3) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3 hw_prefix).aestronglyMeasurable
  have hv_aesm : AEStronglyMeasurable v μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3 hv_prefix).aestronglyMeasurable
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 t hboundary with
    ⟨Aη, _hAη_nonneg, hAη⟩
  have hw_bound :
      ∀ᵐ ω ∂μ, ‖2 * S.c ^ 2 * stepsize S t ω ^ 3‖ ≤ 2 * S.c ^ 2 * Aη ^ 3 := by
    filter_upwards [hAη] with ω hηω
    calc
      ‖2 * S.c ^ 2 * stepsize S t ω ^ 3‖
          = 2 * S.c ^ 2 * ‖stepsize S t ω‖ ^ 3 := by
              simp [norm_mul, norm_pow,
                Real.norm_of_nonneg
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S.c))]
      _ ≤ 2 * S.c ^ 2 * Aη ^ 3 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hηω 3)
          (mul_nonneg (by norm_num) (sq_nonneg S.c))
  exact integrable_mul_sq_norm_of_ae_bounds hw_aesm hv_aesm hw_bound hv_bound

/-- A.e.-prefix measurability of the fresh sampled gradient appearing in the
Lemma 2 RHS.  This is obtained through the same product-law random-query
residual bridge used by Lemma 3. -/
private theorem lemma2_sampled_gradient_succ_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)) μ := by
  have hx :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ :=
    lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t
  have hres :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)) μ := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      section3_random_query_residual_prefixAEMeasurable
        S μ hsec3 (query := iterate S (t + 1)) (n := t + 1) (i := t + 1)
        hx (Nat.le_refl (t + 1))
  have hmono :
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hx' :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ :=
    hx.mono hmono
  have hobj :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S (t + 1) ω)) μ :=
    hx'.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  exact (hres.add hobj).congr (by
    filter_upwards with ω
    simp)

/-- Lemma 2 equation (5): the adapted fresh residual centered-square term is
bounded by the corresponding uncentered stochastic-gradient square under the
source weight `2 c^2 η_t^3`. -/
private theorem lemma2_weighted_fresh_residual_centered_square_integral_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∫ ω,
        2 * S.c ^ 2 * stepsize S t ω ^ 3 *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2 ∂μ ≤
      ∫ ω,
        2 * S.c ^ 2 * stepsize S t ω ^ 3 *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 ∂μ := by
  classical
  let w : Ω → ℝ := fun ω => 2 * S.c ^ 2 * stepsize S t ω ^ 3
  let g : Ω → DecisionSpace d := fun ω =>
    stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)
  let m : Ω → DecisionSpace d := fun ω =>
    objectiveGradient S (iterate S (t + 1) ω)
  have hquery_prefix :=
    lemma2_fresh_square_objective_query_prefixAEMeasurable S μ hsec3 t
  have hquery :
      AEMeasurable
        (fun ω =>
          (iterate S (t + 1) ω,
            (2 * S.c ^ 2 * stepsize S t ω ^ 3) •
              objectiveGradient S (iterate S (t + 1) ω))) μ :=
    prefixAEMeasurable.aemeasurable S μ hsec3 hquery_prefix
  have hsample : Measurable (S.sample (t + 1)) :=
    hsec3.sample_measurable (t + 1)
  have hindep :
      ProbabilityTheory.IndepFun
        (fun ω =>
          (iterate S (t + 1) ω,
            (2 * S.c ^ 2 * stepsize S t ω ^ 3) •
              objectiveGradient S (iterate S (t + 1) ω)))
        (S.sample (t + 1)) μ :=
    section3_indepFun_sample_prefixAEMeasurable_future
      S μ hsec3 hquery_prefix (Nat.le_refl (t + 1))
  have hdir_sq :
      Integrable
        (fun ω =>
          ‖(2 * S.c ^ 2 * stepsize S t ω ^ 3) •
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2) μ :=
    lemma2_fresh_square_objective_multiplier_sq_integrable S μ hsec3 t hboundary
  have hcross :=
    lemma2_adapted_fresh_residual_inner_integral_eq_zero_of_query_l2
      S μ hsec3 (t + 1) hquery hsample hindep hdir_sq
  have hcenter_int :
      Integrable (fun ω => w ω * inner ℝ (m ω) (g ω - m ω)) μ := by
    refine hcross.1.congr ?_
    filter_upwards with ω
    rw [inner_smul_right]
    simp [w, g, m, real_inner_comm]
  have hcenter_zero :
      ∫ ω, w ω * inner ℝ (m ω) (g ω - m ω) ∂μ = 0 := by
    have hcongr :
        (fun ω => w ω * inner ℝ (m ω) (g ω - m ω)) =ᵐ[μ]
          (fun ω =>
            inner ℝ
              (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                objectiveGradient S (iterate S (t + 1) ω))
              ((2 * S.c ^ 2 * stepsize S t ω ^ 3) •
                objectiveGradient S (iterate S (t + 1) ω))) := by
      filter_upwards with ω
      rw [inner_smul_right]
      simp [w, g, m, real_inner_comm]
    rw [integral_congr_ae hcongr]
    exact hcross.2
  have hw_nonneg : ∀ᵐ ω ∂μ, 0 ≤ w ω := by
    filter_upwards with ω
    have hη_pos : 0 < stepsize S t ω :=
      stepsize_pos_of_generated_quotient_boundary S hboundary t ω
    simp [w]
    positivity
  have hg_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        g μ := by
    simpa [g] using lemma2_sampled_gradient_succ_prefixAEMeasurable S μ hsec3 t
  have hg_bound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ G := by
    filter_upwards [hsec3.G_lipschitz_losses (t + 1)] with ω hω
    exact hω (iterate S (t + 1) ω)
  have hwg_sq : Integrable (fun ω => w ω * ‖g ω‖ ^ 2) μ := by
    simpa [w, g] using
      lemma2_fresh_square_weighted_norm_sq_integrable_of_ae_bound
        S μ hsec3 t hboundary hg_prefix hg_bound
  have hmono :
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hx :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ :=
    (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t).mono hmono
  have hm_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        m μ := by
    simpa [m] using
      hx.comp_measurable
        (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  have hm_bound : ∀ᵐ ω ∂μ, ‖m ω‖ ≤ G := by
    filter_upwards with ω
    exact section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S (t + 1) ω)
  have hwm_sq : Integrable (fun ω => w ω * ‖m ω‖ ^ 2) μ := by
    simpa [w, m] using
      lemma2_fresh_square_weighted_norm_sq_integrable_of_ae_bound
        S μ hsec3 t hboundary hm_prefix hm_bound
  simpa [w, g, m] using
    integral_weighted_norm_sq_sub_le_integral_weighted_norm_sq_of_inner_sub_zero
      (μ := μ) (w := w) (g := g) (m := m)
      hw_nonneg hwg_sq hwm_sq hcenter_int hcenter_zero

/-- Measurability of Lemma 2 equation (6)'s source weight
`2 (1 - a_t)^2 / eta_t` as a function of the generated cumulative square
sum. -/
private theorem lemma2_gradient_difference_square_weight_of_sumSq_measurable
    (S : Setup Ω Sample E) :
    Measurable
      (fun sumSq : ℝ =>
        2 * (1 - momentumWeight S (adaptiveStepsize S sumSq)) ^ 2 /
          adaptiveStepsize S sumSq) := by
  have hη := lemma3_adaptiveStepsize_measurable S
  have ha := lemma3_one_sub_momentumWeight_of_sumSq_measurable S
  have hasq :
      Measurable
        (fun sumSq : ℝ =>
          (1 - momentumWeight S (adaptiveStepsize S sumSq)) ^ 2) := by
    convert ha.mul ha using 1
    ext sumSq
    ring
  exact (measurable_const.mul hasq).div hη

/-- Source-shaped a.e.-prefix adaptedness for Lemma 2 equation (6)'s weight
`2 (1-a_t)^2 / eta_t`. -/
private theorem lemma2_gradient_difference_square_weight_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω ℝ _ _
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) μ := by
  have hsum :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (cumulativeGradientNormSq S t) μ :=
    lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ hsec3 t
  refine
    (hsum.comp_measurable
      (lemma2_gradient_difference_square_weight_of_sumSq_measurable S)).congr ?_
  filter_upwards with ω
  rfl

/-- Compact-range bound for Lemma 2 equation (6)'s weight
`2 (1-a_t)^2 / eta_t`. -/
private theorem lemma2_gradient_difference_square_weight_eventually_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᵐ ω ∂μ,
        ‖2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω‖ ≤ A := by
  classical
  rcases lemma2_generated_reciprocal_stepsize_eventually_bound S μ hsec3 t hboundary with
    ⟨Aηinv, hAηinv_nonneg, hAηinv⟩
  have hloc3 : lemma3LocalQuotientBoundary S t :=
    lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t
  rcases lemma3_generated_one_sub_momentum_eventually_bound S μ hsec3 t hloc3 with
    ⟨Aa, hAa_nonneg, hAa⟩
  refine ⟨2 * Aa ^ 2 * Aηinv, by positivity, ?_⟩
  filter_upwards [hAηinv, hAa] with ω hηinvω haω
  set η : ℝ := stepsize S t ω
  set a : ℝ := 1 - nextMomentumWeight S t ω
  have hηinv_bound : ‖1 / η‖ ≤ Aηinv := by simpa [η] using hηinvω
  have ha_bound : ‖a‖ ≤ Aa := by simpa [a] using haω
  have ha_sq : ‖a‖ ^ 2 ≤ Aa ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg a) ha_bound 2
  calc
    ‖2 * a ^ 2 / η‖
        = 2 * ‖a‖ ^ 2 * ‖1 / η‖ := by
          rw [div_eq_mul_one_div]
          simp [norm_mul, norm_pow]
    _ ≤ 2 * Aa ^ 2 * Aηinv := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left ha_sq (by norm_num : (0 : ℝ) ≤ 2))
            hηinv_bound (norm_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg Aa))

/-- Integrability of equation (6)'s weight times a bounded squared norm. -/
private theorem lemma2_gradient_difference_square_weighted_norm_sq_integrable_of_ae_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S)
    {v : Ω → DecisionSpace d} {B : ℝ}
    (hv_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        v μ)
    (hB_nonneg : 0 ≤ B)
    (hv_bound : ∀ᵐ ω ∂μ, ‖v ω‖ ≤ B) :
    Integrable
      (fun ω =>
        2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
          ‖v ω‖ ^ 2) μ := by
  have hmono :
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hw_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => 2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) μ :=
    (lemma2_gradient_difference_square_weight_prefixAEMeasurable S μ hsec3 t).mono hmono
  have htuple :
      @prefixAEMeasurable Ω (ℝ × ℝ) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          (2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω,
            ‖v ω‖ ^ 2)) μ :=
    hw_prefix.prod hv_prefix.norm_sq
  let mulPair : ℝ × ℝ → ℝ := fun p => p.1 * p.2
  have hmulPair_meas : Measurable mulPair := by
    dsimp [mulPair]
    measurability
  have hZ_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
            ‖v ω‖ ^ 2) μ := by
    refine (htuple.comp_measurable hmulPair_meas).congr ?_
    filter_upwards with ω
    rfl
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω =>
          2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
            ‖v ω‖ ^ 2) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3 hZ_prefix).aestronglyMeasurable
  rcases lemma2_gradient_difference_square_weight_eventually_bound
      S μ hsec3 t hboundary with
    ⟨A, hA_nonneg, hA⟩
  refine Integrable.of_bound hZ_aesm (C := A * B ^ 2) ?_
  filter_upwards [hA, hv_bound] with ω hAω hvω
  have hv_sq : ‖v ω‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hvω 2
  calc
    ‖(2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) *
        ‖v ω‖ ^ 2‖
        = ‖2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω‖ *
            ‖v ω‖ ^ 2 := by
          simp [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    _ ≤ A * B ^ 2 :=
          mul_le_mul hAω hv_sq (sq_nonneg _) hA_nonneg

/-- A.e.-prefix measurability of the current iterate sampled with the next
fresh sample. -/
private theorem lemma2_sampled_gradient_current_succ_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (fun ω =>
        stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)) μ := by
  have hx :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    lemma3_iterate_prefixAEMeasurable S μ hsec3 t
  have hres :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S t ω)) μ := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      section3_random_query_residual_prefixAEMeasurable
        S μ hsec3 (query := iterate S t) (n := t + 1) (i := t + 1)
        hx (Nat.le_refl (t + 1))
  have hmono :
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hx' :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    hx.mono hmono
  have hobj :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S t ω)) μ :=
    hx'.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  exact (hres.add hobj).congr (by
    filter_upwards with ω
    simp)

/-- Pointwise Hilbert algebra for equation (6)'s centered cross term. -/
private theorem lemma2_weighted_gradient_difference_center_cross_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (w : ℝ) (sgNext sgPrev objNext objPrev : F) :
    w * inner ℝ (objNext - objPrev)
        ((sgNext - sgPrev) - (objNext - objPrev)) =
      inner ℝ (sgNext - objNext) (w • (objNext - objPrev)) -
        inner ℝ (sgPrev - objPrev) (w • (objNext - objPrev)) := by
  exact weighted_inner_centered_difference_eq_residual_inner_sub w sgNext sgPrev objNext objPrev

/-- Lemma 2 equation (6): centering the two-point stochastic-gradient
difference does not increase the weighted square under the source weight
`2 (1-a_t)^2 / eta_t`. -/
private theorem lemma2_weighted_gradient_difference_centered_square_integral_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∫ ω,
        2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            (objectiveGradient S (iterate S (t + 1) ω) -
              objectiveGradient S (iterate S t ω))‖ ^ 2 ∂μ ≤
      ∫ ω,
        2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ^ 2 ∂μ := by
  classical
  let w : Ω → ℝ := fun ω =>
    2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω
  let g : Ω → DecisionSpace d := fun ω =>
    stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
      stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)
  let m : Ω → DecisionSpace d := fun ω =>
    objectiveGradient S (iterate S (t + 1) ω) - objectiveGradient S (iterate S t ω)
  have hxNextPast :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ :=
    lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t
  have hxPrevPast :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    lemma3_iterate_prefixAEMeasurable S μ hsec3 t
  have hmono :
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hxNext :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S (t + 1)) μ :=
    hxNextPast.mono hmono
  have hxPrev :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    hxPrevPast.mono hmono
  have hobjNextPast :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S (t + 1) ω)) μ :=
    hxNextPast.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  have hobjPrevPast :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S t ω)) μ :=
    hxPrevPast.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  have hm_prefix_past :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        m μ := by
    simpa [m] using hobjNextPast.sub hobjPrevPast
  have hobjNext :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S (t + 1) ω)) μ :=
    hxNext.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  have hobjPrev :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S t ω)) μ :=
    hxPrev.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
  have hm_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        m μ := by
    simpa [m] using hobjNext.sub hobjPrev
  have hg_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        g μ := by
    simpa [g] using
      (lemma2_sampled_gradient_succ_prefixAEMeasurable S μ hsec3 t).sub
        (lemma2_sampled_gradient_current_succ_prefixAEMeasurable S μ hsec3 t)
  have hw_nonneg : ∀ᵐ ω ∂μ, 0 ≤ w ω := by
    filter_upwards with ω
    have hη_pos : 0 < stepsize S t ω :=
      stepsize_pos_of_generated_quotient_boundary S hboundary t ω
    simp [w]
    positivity
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  have hg_bound : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 2 * G := by
    filter_upwards [hsec3.G_lipschitz_losses (t + 1)] with ω hGω
    have hnext :
        ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ≤ G :=
      hGω (iterate S (t + 1) ω)
    have hprev :
        ‖stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ≤ G :=
      hGω (iterate S t ω)
    calc
      ‖g ω‖
          ≤ ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ +
              ‖stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ := by
            simpa [g] using norm_sub_le
              (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω))
              (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω))
      _ ≤ 2 * G := by linarith
  have hm_bound : ∀ᵐ ω ∂μ, ‖m ω‖ ≤ 2 * G := by
    filter_upwards with ω
    have hnext :
        ‖objectiveGradient S (iterate S (t + 1) ω)‖ ≤ G :=
      section3_objectiveGradient_norm_le S μ hsec3 (t + 1) (iterate S (t + 1) ω)
    have hprev :
        ‖objectiveGradient S (iterate S t ω)‖ ≤ G :=
      section3_objectiveGradient_norm_le S μ hsec3 (t + 1) (iterate S t ω)
    calc
      ‖m ω‖
          ≤ ‖objectiveGradient S (iterate S (t + 1) ω)‖ +
              ‖objectiveGradient S (iterate S t ω)‖ := by
            simpa [m] using norm_sub_le
              (objectiveGradient S (iterate S (t + 1) ω))
              (objectiveGradient S (iterate S t ω))
      _ ≤ 2 * G := by linarith
  have htwoG_nonneg : 0 ≤ 2 * G := by positivity
  have hwg_sq : Integrable (fun ω => w ω * ‖g ω‖ ^ 2) μ := by
    simpa [w, g] using
      lemma2_gradient_difference_square_weighted_norm_sq_integrable_of_ae_bound
        S μ hsec3 t hboundary hg_prefix htwoG_nonneg hg_bound
  have hwm_sq : Integrable (fun ω => w ω * ‖m ω‖ ^ 2) μ := by
    simpa [w, m] using
      lemma2_gradient_difference_square_weighted_norm_sq_integrable_of_ae_bound
        S μ hsec3 t hboundary hm_prefix htwoG_nonneg hm_bound
  have hw_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        w μ := by
    simpa [w] using
      (lemma2_gradient_difference_square_weight_prefixAEMeasurable S μ hsec3 t).mono hmono
  have hw_prefix_past :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        w μ := by
    simpa [w] using
      lemma2_gradient_difference_square_weight_prefixAEMeasurable S μ hsec3 t
  have hdir_prefix_past :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => w ω • m ω) μ :=
    hw_prefix_past.real_smul hm_prefix_past
  have hdir_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => w ω • m ω) μ :=
    hdir_prefix_past.mono hmono
  have hdir_aesm :
      AEStronglyMeasurable (fun ω => w ω • m ω) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3 hdir_prefix_past).aestronglyMeasurable
  have hdir_sq : Integrable (fun ω => ‖w ω • m ω‖ ^ 2) μ := by
    rcases lemma2_gradient_difference_square_weight_eventually_bound
        S μ hsec3 t hboundary with
      ⟨A, hA_nonneg, hA⟩
    have hbounded : ∀ᵐ ω ∂μ, ‖w ω • m ω‖ ≤ A * (2 * G) := by
      filter_upwards [hA, hm_bound] with ω hAω hmω
      have hwω : ‖w ω‖ ≤ A := by
        simpa [w] using hAω
      rw [norm_smul]
      exact mul_le_mul hwω hmω (norm_nonneg _) hA_nonneg
    exact (SOptLib.integrable_sq_norm_of_ae_bound hdir_aesm hbounded).1
  have hqueryNext :
      AEMeasurable (fun ω => (iterate S (t + 1) ω, w ω • m ω)) μ :=
    prefixAEMeasurable.aemeasurable S μ hsec3 (hxNextPast.prod hdir_prefix_past)
  have hqueryPrev :
      AEMeasurable (fun ω => (iterate S t ω, w ω • m ω)) μ :=
    prefixAEMeasurable.aemeasurable S μ hsec3 (hxPrevPast.prod hdir_prefix_past)
  have hsample : Measurable (S.sample (t + 1)) :=
    hsec3.sample_measurable (t + 1)
  have hindepNext :
      ProbabilityTheory.IndepFun
        (fun ω => (iterate S (t + 1) ω, w ω • m ω))
    (S.sample (t + 1)) μ :=
    section3_indepFun_sample_prefixAEMeasurable_future
      S μ hsec3 (hxNextPast.prod hdir_prefix_past) (Nat.le_refl (t + 1))
  have hindepPrev :
      ProbabilityTheory.IndepFun
        (fun ω => (iterate S t ω, w ω • m ω))
    (S.sample (t + 1)) μ :=
    section3_indepFun_sample_prefixAEMeasurable_future
      S μ hsec3 (hxPrevPast.prod hdir_prefix_past) (Nat.le_refl (t + 1))
  have hcrossNext :=
    lemma2_adapted_fresh_residual_inner_integral_eq_zero_of_query_l2
      S μ hsec3 (t + 1) hqueryNext hsample hindepNext hdir_sq
  have hcrossPrev :=
    lemma2_adapted_fresh_residual_inner_integral_eq_zero_of_query_l2
      S μ hsec3 (t + 1) hqueryPrev hsample hindepPrev hdir_sq
  have hcenter_int :
      Integrable (fun ω => w ω * inner ℝ (m ω) (g ω - m ω)) μ := by
    have hsub_int : Integrable
        (fun ω =>
          inner ℝ
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω))
            (w ω • m ω) -
          inner ℝ
            (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S t ω))
            (w ω • m ω)) μ :=
      hcrossNext.1.sub hcrossPrev.1
    refine hsub_int.congr ?_
    filter_upwards with ω
    simpa [g, m] using
      (lemma2_weighted_gradient_difference_center_cross_eq
        (w ω)
        (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω))
        (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω))
        (objectiveGradient S (iterate S (t + 1) ω))
        (objectiveGradient S (iterate S t ω))).symm
  have hcenter_zero :
      ∫ ω, w ω * inner ℝ (m ω) (g ω - m ω) ∂μ = 0 := by
    have hcongr :
        (fun ω => w ω * inner ℝ (m ω) (g ω - m ω)) =ᵐ[μ]
          (fun ω =>
            inner ℝ
              (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                objectiveGradient S (iterate S (t + 1) ω))
              (w ω • m ω) -
            inner ℝ
              (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                objectiveGradient S (iterate S t ω))
              (w ω • m ω)) := by
      filter_upwards with ω
      simpa [g, m] using
        lemma2_weighted_gradient_difference_center_cross_eq
          (w ω)
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω))
          (stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω))
          (objectiveGradient S (iterate S (t + 1) ω))
          (objectiveGradient S (iterate S t ω))
    rw [integral_congr_ae hcongr]
    rw [integral_sub hcrossNext.1 hcrossPrev.1]
    rw [hcrossNext.2, hcrossPrev.2]
    norm_num
  simpa [w, g, m] using
    integral_weighted_norm_sq_sub_le_integral_weighted_norm_sq_of_inner_sub_zero
      (μ := μ) (w := w) (g := g) (m := m)
      hw_nonneg hwg_sq hwm_sq hcenter_int hcenter_zero

/-- Lemma 2's local boundary identifies Lemma 3's first cross-term source
expression pointwise; the remaining zero-expectation proof still needs the
totalized integrability and cancellation route. -/
private theorem lemma3FirstCrossTermExpr_eq_some_of_lemma2_local_boundary
    (S : Setup Ω Sample E) {L : ℝ} {t : ℕ}
    (hboundary : lemma2LocalQuotientBoundary S L t) (ω : Ω) :
    lemma3FirstCrossTermExpr S t ω =
      some
        (inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) := by
  rcases hboundary ω with ⟨_hεNext, hη, _hqLHS, ha, hε, _hx, hxNext, _hqRHS⟩
  have hηInv :
      sourceQuotientValue 1 (stepsize S t ω) =
        some (1 / stepsize S t ω) :=
    sourceQuotientValue_eq_some_of_den_ne
      (lemma2LocalQuotientBoundary_stepsize_ne_zero S hboundary ω)
  simp [lemma3FirstCrossTermExpr, hxNext, hη, ha, hε, hηInv]

/-- Lemma 2's local boundary identifies Lemma 3's second cross-term source
expression pointwise; the remaining zero-expectation proof still needs the
totalized integrability and cancellation route. -/
private theorem lemma3SecondCrossTermExpr_eq_some_of_lemma2_local_boundary
    (S : Setup Ω Sample E) {L : ℝ} {t : ℕ}
    (hboundary : lemma2LocalQuotientBoundary S L t) (ω : Ω) :
    lemma3SecondCrossTermExpr S t ω =
      some
        (inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)) := by
  rcases hboundary ω with ⟨_hεNext, hη, _hqLHS, ha, hε, hx, hxNext, _hqRHS⟩
  have hηInv :
      sourceQuotientValue 1 (stepsize S t ω) =
        some (1 / stepsize S t ω) :=
    sourceQuotientValue_eq_some_of_den_ne
      (lemma2LocalQuotientBoundary_stepsize_ne_zero S hboundary ω)
  simp [lemma3SecondCrossTermExpr, hxNext, hx, hη, ha, hε, hηInv]

/-- Generated-boundary integrability of the totalized Lemma 2 RHS.

This is a Lean well-posedness bridge for the paper's displayed expectation:
all scalar coefficients and generated error/objective-gradient/sample-gradient
norms are a.e. measurable and a.e. bounded on the finite generated history. -/
private theorem lemma2_generated_rhs_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    Integrable
      (fun ω =>
        2 * S.c ^ 2 * stepsize S t ω ^ 3 *
            ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
          (1 - nextMomentumWeight S t ω) ^ 2 *
              (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
              ‖error S t ω‖ ^ 2 / stepsize S t ω +
            4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 *
              stepsize S t ω * ‖objectiveGradient S (iterate S t ω)‖ ^ 2) μ := by
  classical
  have hloc3 : lemma3LocalQuotientBoundary S t :=
    lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 t hboundary with
    ⟨Aη, hAη_nonneg, hAη⟩
  rcases lemma2_generated_reciprocal_stepsize_eventually_bound S μ hsec3 t hboundary with
    ⟨Aηinv, hAηinv_nonneg, hAηinv⟩
  rcases lemma3_generated_one_sub_momentum_eventually_bound S μ hsec3 t hloc3 with
    ⟨Aa, hAa_nonneg, hAa⟩
  rcases lemma3_generated_error_eventually_bound S μ hsec3 t hloc3 with
    ⟨Bε, hBε_nonneg, hBε⟩
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  have hmono_prefix :
      (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hη_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (stepsize S t) μ :=
    (lemma2_stepsize_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
  have ha_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => 1 - nextMomentumWeight S t ω) μ :=
    (lemma2_one_sub_momentum_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
  have hg_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2) μ :=
    (lemma2_sampled_gradient_succ_prefixAEMeasurable S μ hsec3 t).norm_sq
  have hε_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => ‖error S t ω‖ ^ 2) μ :=
    (lemma3_error_prefixAEMeasurable S μ hsec3 t).norm_sq.mono hmono_prefix
  have hx_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S t) μ :=
    (lemma3_iterate_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
  have hobj_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => ‖objectiveGradient S (iterate S t ω)‖ ^ 2) μ :=
    (hx_prefix.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 t).measurable).norm_sq
  have htuple :
      @prefixAEMeasurable Ω ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          ((((stepsize S t ω, 1 - nextMomentumWeight S t ω),
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2),
            ‖error S t ω‖ ^ 2),
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2)) μ :=
    (((hη_prefix.prod ha_prefix).prod hg_prefix).prod hε_prefix).prod hobj_prefix
  let rhsOfTuple : ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) → ℝ := fun p =>
    2 * S.c ^ 2 * p.1.1.1.1 ^ 3 * p.1.1.2 +
      p.1.1.1.2 ^ 2 * (1 + 4 * L ^ 2 * p.1.1.1.1 ^ 2) * p.1.2 / p.1.1.1.1 +
        4 * p.1.1.1.2 ^ 2 * L ^ 2 * p.1.1.1.1 * p.2
  have hrhsOfTuple_meas : Measurable rhsOfTuple := by
    dsimp [rhsOfTuple]
    measurability
  have hZ_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          2 * S.c ^ 2 * stepsize S t ω ^ 3 *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
            (1 - nextMomentumWeight S t ω) ^ 2 *
                (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                ‖error S t ω‖ ^ 2 / stepsize S t ω +
              4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 *
                stepsize S t ω * ‖objectiveGradient S (iterate S t ω)‖ ^ 2) μ := by
    refine (htuple.comp_measurable hrhsOfTuple_meas).congr ?_
    filter_upwards with ω
    rfl
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω =>
          2 * S.c ^ 2 * stepsize S t ω ^ 3 *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
            (1 - nextMomentumWeight S t ω) ^ 2 *
                (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                ‖error S t ω‖ ^ 2 / stepsize S t ω +
              4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 *
                stepsize S t ω * ‖objectiveGradient S (iterate S t ω)‖ ^ 2) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3 hZ_prefix).aestronglyMeasurable
  refine Integrable.of_bound hZ_aesm
    (C :=
      2 * S.c ^ 2 * Aη ^ 3 * G ^ 2 +
        Aa ^ 2 * (1 + 4 * L ^ 2 * Aη ^ 2) * Bε ^ 2 * Aηinv +
          4 * L ^ 2 * Aa ^ 2 * Aη * G ^ 2) ?_
  filter_upwards [hAη, hAηinv, hAa, hBε, hsec3.G_lipschitz_losses (t + 1)] with
    ω hηω hηinvω haω hεω hGω
  have hgω :
      ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ≤ G :=
    hGω (iterate S (t + 1) ω)
  have hobjω :
      ‖objectiveGradient S (iterate S t ω)‖ ≤ G :=
    section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S t ω)
  set η : ℝ := stepsize S t ω
  set a : ℝ := 1 - nextMomentumWeight S t ω
  set gNorm : ℝ :=
    ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖
  set eNorm : ℝ := ‖error S t ω‖
  set objNorm : ℝ := ‖objectiveGradient S (iterate S t ω)‖
  have hη_bound : ‖η‖ ≤ Aη := by simpa [η] using hηω
  have hηinv_bound : ‖1 / η‖ ≤ Aηinv := by simpa [η] using hηinvω
  have ha_bound : ‖a‖ ≤ Aa := by simpa [a] using haω
  have heNorm_nonneg : 0 ≤ eNorm := by
    simp [eNorm]
  have he_bound : eNorm ≤ Bε := by simpa [eNorm] using hεω
  have hg_bound : gNorm ≤ G := by simpa [gNorm] using hgω
  have hobj_bound : objNorm ≤ G := by simpa [objNorm] using hobjω
  have hη_pow2 : ‖η‖ ^ 2 ≤ Aη ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg η) hη_bound 2
  have hη_pow3 : ‖η‖ ^ 3 ≤ Aη ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg η) hη_bound 3
  have ha_pow2 : ‖a‖ ^ 2 ≤ Aa ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg a) ha_bound 2
  have hg_pow2 : gNorm ^ 2 ≤ G ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hg_bound 2
  have he_pow2 : eNorm ^ 2 ≤ Bε ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) he_bound 2
  have hobj_pow2 : objNorm ^ 2 ≤ G ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hobj_bound 2
  have hfactor_nonneg : 0 ≤ 1 + 4 * L ^ 2 * Aη ^ 2 := by
    positivity
  have hfactor :
      ‖1 + 4 * L ^ 2 * η ^ 2‖ ≤ 1 + 4 * L ^ 2 * Aη ^ 2 := by
    calc
      ‖1 + 4 * L ^ 2 * η ^ 2‖
          ≤ ‖(1 : ℝ)‖ + ‖4 * L ^ 2 * η ^ 2‖ := norm_add_le _ _
      _ = 1 + 4 * L ^ 2 * ‖η‖ ^ 2 := by
          simp [norm_mul, norm_pow,
            Real.norm_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg L))]
      _ ≤ 1 + 4 * L ^ 2 * Aη ^ 2 := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hη_pow2
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg L))) _
  have hterm1 :
      ‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2‖ ≤
        2 * S.c ^ 2 * Aη ^ 3 * G ^ 2 := by
    calc
      ‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2‖
          = 2 * S.c ^ 2 * ‖η‖ ^ 3 * gNorm ^ 2 := by
            simp [norm_mul, norm_pow, Real.norm_of_nonneg (sq_nonneg gNorm),
              Real.norm_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S.c))]
      _ ≤ 2 * S.c ^ 2 * Aη ^ 3 * G ^ 2 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hη_pow3
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S.c)))
            hg_pow2 (sq_nonneg gNorm)
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S.c))
              (pow_nonneg hAη_nonneg 3))
  have hterm2 :
      ‖a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η‖ ≤
        Aa ^ 2 * (1 + 4 * L ^ 2 * Aη ^ 2) * Bε ^ 2 * Aηinv := by
    calc
      ‖a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η‖
          = ‖a‖ ^ 2 * ‖1 + 4 * L ^ 2 * η ^ 2‖ * eNorm ^ 2 * ‖1 / η‖ := by
            rw [div_eq_mul_one_div]
            simp_rw [norm_mul, norm_pow]
            rw [Real.norm_of_nonneg heNorm_nonneg]
      _ ≤ Aa ^ 2 * (1 + 4 * L ^ 2 * Aη ^ 2) * Bε ^ 2 * Aηinv := by
          have hleft_nonneg :
              0 ≤ ‖a‖ ^ 2 * ‖1 + 4 * L ^ 2 * η ^ 2‖ * eNorm ^ 2 := by
            positivity
          have hmid_nonneg : 0 ≤ Aa ^ 2 * (1 + 4 * L ^ 2 * Aη ^ 2) := by
            positivity
          have hfirst :
              ‖a‖ ^ 2 * ‖1 + 4 * L ^ 2 * η ^ 2‖ * eNorm ^ 2 ≤
                Aa ^ 2 * (1 + 4 * L ^ 2 * Aη ^ 2) * Bε ^ 2 := by
            exact mul_le_mul
              (mul_le_mul ha_pow2 hfactor (norm_nonneg _) (sq_nonneg Aa))
              he_pow2 (sq_nonneg eNorm)
              (mul_nonneg (sq_nonneg Aa) hfactor_nonneg)
          exact mul_le_mul hfirst hηinv_bound (norm_nonneg _) 
            (mul_nonneg hmid_nonneg (sq_nonneg Bε))
  have hterm3 :
      ‖4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖ ≤
        4 * L ^ 2 * Aa ^ 2 * Aη * G ^ 2 := by
    calc
      ‖4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖
          = 4 * L ^ 2 * ‖a‖ ^ 2 * ‖η‖ * objNorm ^ 2 := by
            ring_nf
            simp [norm_mul, norm_pow, Real.norm_of_nonneg (sq_nonneg objNorm),
              Real.norm_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg L)),
              mul_assoc, mul_left_comm, mul_comm]
      _ ≤ 4 * L ^ 2 * Aa ^ 2 * Aη * G ^ 2 := by
          have hleft_nonneg : 0 ≤ 4 * L ^ 2 * ‖a‖ ^ 2 * ‖η‖ := by
            positivity
          have hfirst :
              4 * L ^ 2 * ‖a‖ ^ 2 * ‖η‖ ≤
                4 * L ^ 2 * Aa ^ 2 * Aη := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left ha_pow2
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg L)))
              hη_bound (norm_nonneg η)
              (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg L)) (sq_nonneg Aa))
          exact mul_le_mul hfirst hobj_pow2 (sq_nonneg objNorm)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg L))
              (sq_nonneg Aa)) hAη_nonneg)
  have htri :
      ‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2 +
          a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η +
        4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖ ≤
        ‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2‖ +
          ‖a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η‖ +
            ‖4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖ := by
    calc
      ‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2 +
          a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η +
        4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖
          ≤ ‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2 +
              a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η‖ +
            ‖4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖ := norm_add_le _ _
      _ ≤ (‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2‖ +
              ‖a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η‖) +
            ‖4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖ := by
          exact add_le_add (norm_add_le _ _) le_rfl
      _ =
          ‖2 * S.c ^ 2 * η ^ 3 * gNorm ^ 2‖ +
            ‖a ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * eNorm ^ 2 / η‖ +
              ‖4 * a ^ 2 * L ^ 2 * η * objNorm ^ 2‖ := by
          ring
  simpa [η, a, gNorm, eNorm, objNorm] using
    (htri.trans (by linarith [hterm1, hterm2, hterm3]))

/-- Abstract pointwise Hilbert algebra for Lemma 2's three-term expansion.
The first two fresh terms are bounded by Young's inequality; the crosses with
the third term are kept explicit for later expectation cancellation. -/
private theorem three_term_young_cross_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {η a b c : ℝ} (hη_pos : 0 < η) (ha : a = c * η ^ 2)
    (N D ε : E) :
    ‖(a • N + b • D) + b • ε‖ ^ 2 / η ≤
      2 * c ^ 2 * η ^ 3 * ‖N‖ ^ 2 +
        2 * b ^ 2 / η * ‖D‖ ^ 2 +
        b ^ 2 * ‖ε‖ ^ 2 / η +
        inner ℝ N ((2 * a * b / η) • ε) +
        inner ℝ D ((2 * b ^ 2 / η) • ε) := by
  exact norm_three_term_sq_div_le_of_first_coeff_eq hη_pos ha N D ε

/-- Integrate a pointwise upper bound and cancel two zero-integral cross
terms.  This is the measure-theoretic shell for Lemma 2 step 10. -/
private theorem integral_le_integral_three_terms_of_pointwise_le_add_crosses
    [MeasurableSpace Ω] {μ : Measure Ω}
    {lhs A B C X Y : Ω → ℝ}
    (hlhs_int : Integrable lhs μ)
    (hA_int : Integrable A μ) (hB_int : Integrable B μ)
    (hC_int : Integrable C μ) (hX_int : Integrable X μ)
    (hY_int : Integrable Y μ)
    (hpoint :
      ∀ᵐ ω ∂μ, lhs ω ≤ A ω + B ω + C ω + X ω + Y ω)
    (hX_zero : ∫ ω, X ω ∂μ = 0)
    (hY_zero : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, lhs ω ∂μ ≤ ∫ ω, A ω + B ω + C ω ∂μ := by
  refine integral_le_integral_of_ae_le_add_of_integral_eq_zero
    hlhs_int ((hA_int.add hB_int).add hC_int) (hX_int.add hY_int) ?_ ?_
  · filter_upwards [hpoint] with ω hω
    simpa only [Pi.add_apply, add_assoc] using hω
  · change (∫ ω, X ω + Y ω ∂μ) = 0
    rw [integral_add hX_int hY_int, hX_zero, hY_zero, add_zero]

private theorem sub_sub_add_eq_sub_sub
    {E : Type*} [AddCommGroup E] (x y z w : E) :
    x - y - z + w = x - y - (z - w) := by
  abel

private theorem eq_add_of_eq_sub
    {E : Type*} [AddCommGroup E] {e d m : E} (h : e = d - m) :
    d = e + m := by
  rw [h]
  abel

/-- Pointwise deterministic square-term assembly for Lemma 2 after the cross
terms have been removed.

This is the source proof's steps 12-16 in local form: smoothness bounds the
sampled two-point gradient difference by the iterate displacement, the update
identifies that displacement with `η_t d_t`, and `d_t = ε_t + ∇F(x_t)` is
split by the two-term squared-norm Young inequality. -/
private theorem lemma2_uncentered_gradient_difference_plus_error_pointwise_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η a L : ℝ} {g xNext xPrev dir ε m : E}
    (hη_pos : 0 < η)
    (hgrad : ‖g‖ ≤ L * ‖xNext - xPrev‖)
    (hdisp : xNext - xPrev = -η • dir)
    (hdir : dir = ε + m) :
    2 * (1 - a) ^ 2 / η * ‖g‖ ^ 2 +
        (1 - a) ^ 2 * ‖ε‖ ^ 2 / η ≤
      (1 - a) ^ 2 * (1 + 4 * L ^ 2 * η ^ 2) * ‖ε‖ ^ 2 / η +
        4 * (1 - a) ^ 2 * L ^ 2 * η * ‖m‖ ^ 2 := by
  exact weighted_smooth_difference_add_error_sq_le_of_affine_update
    (eta := η) (a := a) (L := L) (g := g) (xNext := xNext) (xPrev := xPrev)
    (dir := dir) (err := ε) (target := m) hη_pos hgrad hdisp hdir

/-- Pointwise deterministic expansion used in Lemma 2 after rewriting
`epsilon_{t+1}` into the fresh residual, centered gradient difference, and
previous-error terms.  The two displayed inner products are exactly the cross
terms later canceled by Lemma 3. -/
private theorem lemma2_three_term_pointwise_cross_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (S : Setup Ω Sample E) (t : ℕ) (hboundary : generatedStepsizeQuotientBoundary S)
    (ω : Ω)
    (hdecomp :
      error S (t + 1) ω =
        nextMomentumWeight S t ω •
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω)) +
          (1 - nextMomentumWeight S t ω) •
            (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω) +
              objectiveGradient S (iterate S t ω)) +
          (1 - nextMomentumWeight S t ω) • error S t ω) :
    ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω ≤
      2 * S.c ^ 2 * stepsize S t ω ^ 3 *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2 +
        2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω)‖ ^ 2 +
        (1 - nextMomentumWeight S t ω) ^ 2 * ‖error S t ω‖ ^ 2 /
          stepsize S t ω +
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
            stepsize S t ω) • error S t ω) +
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          ((2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) •
            error S t ω) := by
  set η : ℝ := stepsize S t ω
  set a : ℝ := nextMomentumWeight S t ω
  set b : ℝ := 1 - nextMomentumWeight S t ω
  set N : E :=
    stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
      objectiveGradient S (iterate S (t + 1) ω)
  set D : E :=
    stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
      stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
      objectiveGradient S (iterate S (t + 1) ω) +
      objectiveGradient S (iterate S t ω)
  set ε : E := error S t ω
  have hη_pos : 0 < η := by
    simpa [η] using stepsize_pos_of_generated_quotient_boundary S hboundary t ω
  have ha : a = S.c * η ^ 2 := by
    simp [a, η, nextMomentumWeight, momentumWeight]
  have hbase :
      ‖(a • N + b • D) + b • ε‖ ^ 2 / η ≤
        2 * S.c ^ 2 * η ^ 3 * ‖N‖ ^ 2 +
          2 * b ^ 2 / η * ‖D‖ ^ 2 +
          b ^ 2 * ‖ε‖ ^ 2 / η +
          inner ℝ N ((2 * a * b / η) • ε) +
          inner ℝ D ((2 * b ^ 2 / η) • ε) :=
    three_term_young_cross_bound hη_pos ha N D ε
  calc
    ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω
        = ‖(a • N + b • D) + b • ε‖ ^ 2 / η := by
          simpa [η, a, b, N, D, ε] using
            congrArg (fun z => ‖z‖ ^ 2 / stepsize S t ω) hdecomp
    _ ≤ 2 * S.c ^ 2 * η ^ 3 * ‖N‖ ^ 2 +
          2 * b ^ 2 / η * ‖D‖ ^ 2 +
          b ^ 2 * ‖ε‖ ^ 2 / η +
          inner ℝ N ((2 * a * b / η) • ε) +
          inner ℝ D ((2 * b ^ 2 / η) • ε) := hbase
    _ = 2 * S.c ^ 2 * stepsize S t ω ^ 3 *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2 +
        2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω)‖ ^ 2 +
        (1 - nextMomentumWeight S t ω) ^ 2 * ‖error S t ω‖ ^ 2 /
          stepsize S t ω +
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω))
          ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
            stepsize S t ω) • error S t ω) +
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          ((2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) •
            error S t ω) := by
          simp [η, a, b, N, D, ε]

set_option maxHeartbeats 800000

/-- Lemma 2 source/coarser generated-boundary route.

The paper states Lemma 2 "with the notation in Algorithm 1"; in Lean this
means the displayed generated stepsizes and reciprocals must be source-defined
for the generated run.  The exact local source expression boundary is derived
from this generated boundary before reducing to totalized integrability and
the integral recurrence. -/
private theorem lemma2_error_recurrence_of_generated_quotient_boundary_via_integral_recurrence
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t) := by
  have hroute : Lemma2GeneratedBoundaryRouteEvidence S L t :=
    lemma2_generated_boundary_route_evidence S hboundary L t
  have hlocal : lemma2LocalQuotientBoundary S L t := hroute.source_local_boundary
  refine
    lemma2_sourceExpectationLE_of_generated_integral_bound S μ L t hlocal ?_ ?_ ?_
  · have hrecip :=
      lemma2_generated_reciprocal_stepsize_eventually_bound S μ hsec3 t hboundary
    have herr :=
      lemma2_generated_next_error_eventually_bound S μ hsec3 t hboundary
    exact lemma2_lhs_integrable_of_error_and_reciprocal_bounds S μ hsec3 t herr hrecip
  · exact lemma2_generated_rhs_integrable S μ hsec3 t hboundary
  · have hdecomp :
        ∀ ω,
          error S (t + 1) ω =
            nextMomentumWeight S t ω •
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω)) +
              (1 - nextMomentumWeight S t ω) •
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω)) +
              (1 - nextMomentumWeight S t ω) • error S t ω := by
      intro ω
      exact lemma2_error_succ_three_term_decomposition S t ω
    have hfirst_source :
        ∀ ω,
          lemma3FirstCrossTermExpr S t ω =
            some
              (inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω))
                (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) := by
      intro ω
      exact lemma3FirstCrossTermExpr_eq_some_of_local_boundary
        S (lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t) ω
    have hsecond_source :
        ∀ ω,
          lemma3SecondCrossTermExpr S t ω =
            some
              (inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω))
                (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                  error S t ω)) := by
      intro ω
      exact lemma3SecondCrossTermExpr_eq_some_of_local_boundary
        S (lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t) ω
    have hcross :
        sourceExpectationEqZero μ (lemma3FirstCrossTermExpr S t) ∧
          sourceExpectationEqZero μ (lemma3SecondCrossTermExpr S t) :=
      lemma3_cross_terms_zero S μ hsec3 t
        (lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t)
    have hfirst_expansion_cross :
        Integrable
            (fun ω =>
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω))
                ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
                  stepsize S t ω) • error S t ω)) μ ∧
          ∫ ω,
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω))
                ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
                  stepsize S t ω) • error S t ω) ∂μ = 0 :=
      lemma2_adapted_weighted_first_cross_integral_eq_zero S μ hsec3 t hboundary
    have hfresh_centered_square :
        ∫ ω,
            2 * S.c ^ 2 * stepsize S t ω ^ 3 *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2 ∂μ ≤
          ∫ ω,
            2 * S.c ^ 2 * stepsize S t ω ^ 3 *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 ∂μ :=
      lemma2_weighted_fresh_residual_centered_square_integral_le S μ hsec3 t hboundary
    have hdiff_centered_square :
        ∫ ω,
            2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                (objectiveGradient S (iterate S (t + 1) ω) -
                  objectiveGradient S (iterate S t ω))‖ ^ 2 ∂μ ≤
          ∫ ω,
            2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
              ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ^ 2 ∂μ :=
      lemma2_weighted_gradient_difference_centered_square_integral_le S μ hsec3 t hboundary
    have hsecond_expansion_cross :
        Integrable
            (fun ω =>
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω))
                ((2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) •
                  error S t ω)) μ ∧
          ∫ ω,
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω))
                ((2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) •
                  error S t ω) ∂μ = 0 := by
      have hsrc := hcross.2
      unfold sourceExpectationEqZero at hsrc
      rw [sourceExpectationValue_eq_some_iff] at hsrc
      rcases hsrc with ⟨_hdefined, hsrc_int, hsrc_zero⟩
      let Z : Ω → ℝ := fun ω =>
        inner ℝ
          (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω))
          (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
            error S t ω)
      have hZ_get :
          (fun ω => (lemma3SecondCrossTermExpr S t ω).getD 0) = Z := by
        funext ω
        rw [hsecond_source ω]
        rfl
      have hZ_int : Integrable Z μ := by
        simpa [hZ_get] using hsrc_int
      have hZ_zero : ∫ ω, Z ω ∂μ = 0 := by
        have h0 : (0 : ℝ) = ∫ ω, Z ω ∂μ := by
          simpa [hZ_get] using hsrc_zero
        exact h0.symm
      have hscaled_int :
          Integrable
            (fun ω =>
              2 *
                inner ℝ
                  (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                    stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                    objectiveGradient S (iterate S (t + 1) ω) +
                    objectiveGradient S (iterate S t ω))
                  (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) μ := by
        simpa [Z] using hZ_int.const_mul 2
      have hscaled_eq :
          (fun ω =>
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω))
                ((2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) •
                  error S t ω)) =ᵐ[μ]
            (fun ω =>
              2 *
                inner ℝ
                  (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                    stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                    objectiveGradient S (iterate S (t + 1) ω) +
                    objectiveGradient S (iterate S t ω))
                  (((1 / stepsize S t ω) * (1 - nextMomentumWeight S t ω) ^ 2) •
                    error S t ω)) := by
        filter_upwards with ω
        rw [inner_smul_right, inner_smul_right]
        ring
      refine ⟨hscaled_int.congr hscaled_eq.symm, ?_⟩
      rw [integral_congr_ae hscaled_eq]
      rw [integral_const_mul, hZ_zero]
      norm_num
    have hgradient_difference_lipschitz :
        ∀ᵐ ω ∂μ,
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ≤
            L * ‖iterate S (t + 1) ω - iterate S t ω‖ := by
      filter_upwards [hsec3.L_smooth_losses (t + 1)] with ω hsmooth
      exact hsmooth (iterate S (t + 1) ω) (iterate S t ω)
    have hiterate_displacement :
        ∀ ω,
          iterate S (t + 1) ω - iterate S t ω =
            -(stepsize S t ω) • direction S t ω := by
      intro ω
      rw [iterate_succ]
      module
    have hpointwise_cross_bound :
        ∀ᵐ ω ∂μ,
          ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω ≤
            2 * S.c ^ 2 * stepsize S t ω ^ 3 *
                ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2 +
              2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
                ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω)‖ ^ 2 +
              (1 - nextMomentumWeight S t ω) ^ 2 * ‖error S t ω‖ ^ 2 /
                stepsize S t ω +
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω))
                ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
                  stepsize S t ω) • error S t ω) +
              inner ℝ
                (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω) +
                  objectiveGradient S (iterate S t ω))
                ((2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) •
                  error S t ω) := by
      filter_upwards with ω
      exact lemma2_three_term_pointwise_cross_bound S t hboundary ω (hdecomp ω)
    let lhs : Ω → ℝ := fun ω =>
      ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω
    let A_center : Ω → ℝ := fun ω =>
      2 * S.c ^ 2 * stepsize S t ω ^ 3 *
        ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
          objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2
    let B_center : Ω → ℝ := fun ω =>
      2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
        ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
          stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
          objectiveGradient S (iterate S (t + 1) ω) +
          objectiveGradient S (iterate S t ω)‖ ^ 2
    let C_prev : Ω → ℝ := fun ω =>
      (1 - nextMomentumWeight S t ω) ^ 2 * ‖error S t ω‖ ^ 2 /
        stepsize S t ω
    let X_cross : Ω → ℝ := fun ω =>
      inner ℝ
        (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
          objectiveGradient S (iterate S (t + 1) ω))
        ((2 * nextMomentumWeight S t ω * (1 - nextMomentumWeight S t ω) /
          stepsize S t ω) • error S t ω)
    let Y_cross : Ω → ℝ := fun ω =>
      inner ℝ
        (stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
          stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
          objectiveGradient S (iterate S (t + 1) ω) +
          objectiveGradient S (iterate S t ω))
        ((2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω) •
          error S t ω)
    let A_uncentered : Ω → ℝ := fun ω =>
      2 * S.c ^ 2 * stepsize S t ω ^ 3 *
        ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2
    let B_uncentered : Ω → ℝ := fun ω =>
      2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
        ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
          stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ^ 2
    let RHS_final : Ω → ℝ := fun ω =>
      2 * S.c ^ 2 * stepsize S t ω ^ 3 *
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
        (1 - nextMomentumWeight S t ω) ^ 2 *
            (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
            ‖error S t ω‖ ^ 2 / stepsize S t ω +
          4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 *
            stepsize S t ω * ‖objectiveGradient S (iterate S t ω)‖ ^ 2
    have hmono_prefix :
        (⨆ j < t + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample)) ≤
          (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample)) := by
      exact iSup₂_le fun j hj =>
        le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
    have hG_nonneg : 0 ≤ G :=
      section3_lipschitz_constant_nonneg_obligation S μ hsec3
    have hA_int : Integrable A_center μ := by
      have hw_prefix :
          @prefixAEMeasurable Ω ℝ _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω => 2 * S.c ^ 2 * stepsize S t ω ^ 3) μ :=
        (lemma2_fresh_square_weight_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
      have hg_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)) μ :=
        lemma2_sampled_gradient_succ_prefixAEMeasurable S μ hsec3 t
      have hx_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (iterate S (t + 1)) μ :=
        (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
      have hm_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω => objectiveGradient S (iterate S (t + 1) ω)) μ :=
        hx_prefix.comp_measurable
          (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
      have hv_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                objectiveGradient S (iterate S (t + 1) ω)) μ :=
        hg_prefix.sub hm_prefix
      have htuple :
          @prefixAEMeasurable Ω (ℝ × ℝ) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              (2 * S.c ^ 2 * stepsize S t ω ^ 3,
                ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2)) μ :=
        hw_prefix.prod hv_prefix.norm_sq
      let mulPair : ℝ × ℝ → ℝ := fun p => p.1 * p.2
      have hmulPair_meas : Measurable mulPair := by
        dsimp [mulPair]
        measurability
      have hA_aesm : AEStronglyMeasurable A_center μ := by
        have hZ_prefix :
            @prefixAEMeasurable Ω ℝ _ _
              (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
                (by infer_instance : MeasurableSpace Sample))
              A_center μ := by
          refine (htuple.comp_measurable hmulPair_meas).congr ?_
          filter_upwards with ω
          rfl
        exact (prefixAEMeasurable.aemeasurable S μ hsec3 hZ_prefix).aestronglyMeasurable
      rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 t hboundary with
        ⟨Aη, _hAη_nonneg, hAη⟩
      have hv_bound : ∀ᵐ ω ∂μ,
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ≤ 2 * G := by
        filter_upwards [hsec3.G_lipschitz_losses (t + 1)] with ω hGω
        have hg :
            ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ≤ G :=
          hGω (iterate S (t + 1) ω)
        have hm :
            ‖objectiveGradient S (iterate S (t + 1) ω)‖ ≤ G :=
          section3_objectiveGradient_norm_le S μ hsec3 (t + 1) (iterate S (t + 1) ω)
        calc
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω)‖
              ≤ ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ +
                  ‖objectiveGradient S (iterate S (t + 1) ω)‖ := norm_sub_le _ _
          _ ≤ 2 * G := by linarith
      refine Integrable.of_bound hA_aesm
        (C := 2 * S.c ^ 2 * Aη ^ 3 * (2 * G) ^ 2) ?_
      filter_upwards [hAη, hv_bound] with ω hηω hvω
      have hη_pos : 0 < stepsize S t ω :=
        stepsize_pos_of_generated_quotient_boundary S hboundary t ω
      have hη_nonneg : 0 ≤ stepsize S t ω := le_of_lt hη_pos
      have hη_le : stepsize S t ω ≤ Aη := by
        simpa [Real.norm_of_nonneg hη_nonneg] using hηω
      have hη3_le : stepsize S t ω ^ 3 ≤ Aη ^ 3 :=
        pow_le_pow_left₀ hη_nonneg hη_le 3
      have hv2_le :
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2 ≤ (2 * G) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hvω 2
      have hweight_nonneg : 0 ≤ 2 * S.c ^ 2 * stepsize S t ω ^ 3 := by
        positivity
      calc
        ‖A_center ω‖
            = 2 * S.c ^ 2 * stepsize S t ω ^ 3 *
                ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                  objectiveGradient S (iterate S (t + 1) ω)‖ ^ 2 := by
              exact Real.norm_of_nonneg (by
                dsimp [A_center]
                exact mul_nonneg hweight_nonneg (sq_nonneg _))
        _ ≤ 2 * S.c ^ 2 * Aη ^ 3 * (2 * G) ^ 2 := by
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left hη3_le
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg S.c)))
                hv2_le (sq_nonneg _) (by positivity)
    have hB_int : Integrable B_center μ := by
      have hg_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)) μ :=
        lemma2_sampled_gradient_succ_prefixAEMeasurable S μ hsec3 t
      have hgprev_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)) μ :=
        lemma2_sampled_gradient_current_succ_prefixAEMeasurable S μ hsec3 t
      have hxNext_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (iterate S (t + 1)) μ :=
        (lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
      have hxPrev_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (iterate S t) μ :=
        (lemma3_iterate_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
      have hobjNext_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω => objectiveGradient S (iterate S (t + 1) ω)) μ :=
        hxNext_prefix.comp_measurable
          (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
      have hobjPrev_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω => objectiveGradient S (iterate S t ω)) μ :=
        hxPrev_prefix.comp_measurable
          (section3_objectiveGradient_continuous S μ hsec3 (t + 1)).measurable
      have hv_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
                objectiveGradient S (iterate S (t + 1) ω) +
                objectiveGradient S (iterate S t ω)) μ := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          ((hg_prefix.sub hgprev_prefix).sub hobjNext_prefix).add hobjPrev_prefix
      have hv_bound : ∀ᵐ ω ∂μ,
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
            objectiveGradient S (iterate S (t + 1) ω) +
            objectiveGradient S (iterate S t ω)‖ ≤ 4 * G := by
        filter_upwards [hsec3.G_lipschitz_losses (t + 1)] with ω hGω
        have hgNext :
            ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ≤ G :=
          hGω (iterate S (t + 1) ω)
        have hgPrev :
            ‖stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ≤ G :=
          hGω (iterate S t ω)
        have hobjNext :
            ‖objectiveGradient S (iterate S (t + 1) ω)‖ ≤ G :=
          section3_objectiveGradient_norm_le S μ hsec3 (t + 1) (iterate S (t + 1) ω)
        have hobjPrev :
            ‖objectiveGradient S (iterate S t ω)‖ ≤ G :=
          section3_objectiveGradient_norm_le S μ hsec3 (t + 1) (iterate S t ω)
        let gNext : DecisionSpace d :=
          stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)
        let gPrev : DecisionSpace d :=
          stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)
        let mNext : DecisionSpace d := objectiveGradient S (iterate S (t + 1) ω)
        let mPrev : DecisionSpace d := objectiveGradient S (iterate S t ω)
        have htri₁ : ‖(gNext - gPrev - mNext) + mPrev‖ ≤
            ‖gNext - gPrev - mNext‖ + ‖mPrev‖ :=
          norm_add_le _ _
        have htri₂ : ‖gNext - gPrev - mNext‖ ≤
            ‖gNext - gPrev‖ + ‖mNext‖ :=
          norm_sub_le _ _
        have htri₃ : ‖gNext - gPrev‖ ≤ ‖gNext‖ + ‖gPrev‖ :=
          norm_sub_le _ _
        have htri :
            ‖gNext - gPrev - mNext + mPrev‖ ≤
              ‖gNext‖ + ‖gPrev‖ + ‖mNext‖ + ‖mPrev‖ := by
          linarith
        calc
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω) -
              objectiveGradient S (iterate S (t + 1) ω) +
              objectiveGradient S (iterate S t ω)‖
              ≤ ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ +
                  ‖stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ +
                  ‖objectiveGradient S (iterate S (t + 1) ω)‖ +
                  ‖objectiveGradient S (iterate S t ω)‖ := by
                simpa [gNext, gPrev, mNext, mPrev] using htri
          _ ≤ 4 * G := by linarith
      have hfourG_nonneg : 0 ≤ 4 * G := by positivity
      simpa [B_center] using
        lemma2_gradient_difference_square_weighted_norm_sq_integrable_of_ae_bound
          S μ hsec3 t hboundary hv_prefix hfourG_nonneg hv_bound
    have hC_int : Integrable C_prev μ := by
      have hloc3 : lemma3LocalQuotientBoundary S t :=
        lemma3LocalQuotientBoundary_of_generated_boundary S hboundary t
      rcases lemma3_generated_error_eventually_bound S μ hsec3 t hloc3 with
        ⟨Bε, hBε_nonneg, hBε⟩
      have hε_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (error S t) μ :=
        (lemma3_error_prefixAEMeasurable S μ hsec3 t).mono hmono_prefix
      have htwice :
          Integrable
            (fun ω =>
              2 * (1 - nextMomentumWeight S t ω) ^ 2 / stepsize S t ω *
                ‖error S t ω‖ ^ 2) μ :=
        lemma2_gradient_difference_square_weighted_norm_sq_integrable_of_ae_bound
          S μ hsec3 t hboundary hε_prefix hBε_nonneg hBε
      refine (htwice.const_mul ((1 : ℝ) / 2)).congr ?_
      filter_upwards with ω
      dsimp [C_prev]
      ring
    have hA_uncentered_int : Integrable A_uncentered μ := by
      have hg_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)) μ :=
        lemma2_sampled_gradient_succ_prefixAEMeasurable S μ hsec3 t
      have hg_bound : ∀ᵐ ω ∂μ,
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ≤ G := by
        filter_upwards [hsec3.G_lipschitz_losses (t + 1)] with ω hGω
        exact hGω (iterate S (t + 1) ω)
      simpa [A_uncentered] using
        lemma2_fresh_square_weighted_norm_sq_integrable_of_ae_bound
          S μ hsec3 t hboundary hg_prefix hg_bound
    have hB_uncentered_int : Integrable B_uncentered μ := by
      have hg_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < t + 2, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (fun ω =>
              stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
                stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)) μ :=
        (lemma2_sampled_gradient_succ_prefixAEMeasurable S μ hsec3 t).sub
          (lemma2_sampled_gradient_current_succ_prefixAEMeasurable S μ hsec3 t)
      have hg_bound : ∀ᵐ ω ∂μ,
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
            stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ≤ 2 * G := by
        filter_upwards [hsec3.G_lipschitz_losses (t + 1)] with ω hGω
        have hnext :
            ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ≤ G :=
          hGω (iterate S (t + 1) ω)
        have hprev :
            ‖stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ ≤ G :=
          hGω (iterate S t ω)
        calc
          ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω) -
              stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖
              ≤ ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ +
                  ‖stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω)‖ := norm_sub_le _ _
          _ ≤ 2 * G := by linarith
      have htwoG_nonneg : 0 ≤ 2 * G := by positivity
      simpa [B_uncentered] using
        lemma2_gradient_difference_square_weighted_norm_sq_integrable_of_ae_bound
          S μ hsec3 t hboundary hg_prefix htwoG_nonneg hg_bound
    have hlhs_int :
        Integrable lhs μ := by
      have hrecip :=
        lemma2_generated_reciprocal_stepsize_eventually_bound S μ hsec3 t hboundary
      have herr :=
        lemma2_generated_next_error_eventually_bound S μ hsec3 t hboundary
      simpa [lhs] using
        lemma2_lhs_integrable_of_error_and_reciprocal_bounds S μ hsec3 t herr hrecip
    have hRHS_int : Integrable RHS_final μ := by
      simpa [RHS_final] using lemma2_generated_rhs_integrable S μ hsec3 t hboundary
    exact recursive_momentum_error_integral_recurrence
      (μ := μ)
      (x := iterate S t) (xNext := iterate S (t + 1))
      (err := error S t) (errNext := error S (t + 1))
      (sampleGradNext := fun ω =>
        stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω))
      (sampleGradPrev := fun ω =>
        stochasticGradient S (iterate S t ω) (S.sample (t + 1) ω))
      (targetNext := fun ω => objectiveGradient S (iterate S (t + 1) ω))
      (targetPrev := fun ω => objectiveGradient S (iterate S t ω))
      (dir := direction S t) (eta := stepsize S t)
      (momentum := nextMomentumWeight S t) (c := S.c) (L := L)
      (stepsize_pos_of_generated_quotient_boundary S hboundary t)
      (by intro ω; simp [nextMomentumWeight, momentumWeight])
      hdecomp hiterate_displacement
      (by intro ω; exact eq_add_of_eq_sub (error_eq S t ω))
      hgradient_difference_lipschitz
      (by simpa [lhs] using hlhs_int)
      (by simpa [A_center] using hA_int)
      (by simpa [B_center] using hB_int)
      (by simpa [C_prev] using hC_int)
      (by simpa [A_uncentered] using hA_uncentered_int)
      (by simpa [B_uncentered] using hB_uncentered_int)
      (by simpa [RHS_final] using hRHS_int)
      hfirst_expansion_cross hsecond_expansion_cross
      hfresh_centered_square hdiff_centered_square

/-- Lemma 2 source/coarser generated-boundary route, discharged through the
general recursive-momentum integral recurrence. -/
private theorem lemma2_error_recurrence_of_generated_quotient_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t) := by
  exact lemma2_error_recurrence_of_generated_quotient_boundary_via_integral_recurrence
    S μ hsec3 t hboundary

set_option maxHeartbeats 200000

/-- Dependency-closure certificate for the source/coarser Lemma 2 route.

The public Lemma 2 statement consumes this certificate.  Its supplier is the
generated Algorithm 1 quotient boundary, which constructs
`Lemma2GeneratedBoundaryRouteEvidence`; the exact local source boundary is only
the generated route's projection and is not an independent source supplier. -/
private theorem lemma2_generated_route_dependency_closure_certificate
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    lemma2LocalQuotientBoundary S L t ∧
      (∀ ω, 0 < stepsize S t ω) ∧
        (∀ ω, sourceStepsize S t ω = some (stepsize S t ω)) ∧
          (∀ ω, sourceQuotientValue 1 (stepsize S t ω) =
            some (1 / stepsize S t ω)) ∧
            sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t) := by
  let hroute : Lemma2GeneratedBoundaryRouteEvidence S L t :=
    lemma2_generated_boundary_route_evidence S hboundary L t
  exact
    ⟨hroute.source_local_boundary,
      hroute.stepsize_positive,
      hroute.source_stepsize,
      hroute.source_stepsize_inverse,
      lemma2_error_recurrence_of_generated_quotient_boundary S μ hsec3 t hboundary⟩

/-- Lemma 2: recursive error estimate for STORM's momentum direction.

The paper states this recurrence "with the notation in Algorithm 1".  In the
source-Option realization, that notation is represented by the generated
quotient boundary: the generated adaptive stepsizes are source-defined and
positive, so both the displayed reciprocal terms and the positive-weight
centered-square inequalities are meaningful.  The exact local Lemma 2 source
expressions are derived internally by
`lemma2LocalQuotientBoundary_of_generated_boundary`. -/
theorem lemma2_error_recurrence
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (t : ℕ)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t) := by
  exact
    (lemma2_generated_route_dependency_closure_certificate
      S μ hsec3 t hboundary).2.2.2.2

private theorem log_increment_ratio_bound_of_pos_of_nonneg
    {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    q / (p + q) ≤ Real.log (p + q) - Real.log p := by
  exact div_add_le_log_add_sub_log_of_pos_of_nonneg hp hq

private theorem sum_Icc_prefix_nonneg_of_Icc_nonneg
    (a : ℕ → ℝ) {T t : ℕ}
    (ht : t ≤ T)
    (ha_nonneg : ∀ i, i ∈ Finset.Icc 1 T → 0 ≤ a i) :
    0 ≤ (Finset.Icc 1 t).sum a := by
  refine Finset.sum_nonneg ?_
  intro i hi
  exact ha_nonneg i (by
    rw [Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, le_trans hi.2 ht⟩)

private theorem prefix_denominator_pos_of_Icc_nonneg
    {a₀ : ℝ} (a : ℕ → ℝ) {T t : ℕ}
    (ha₀ : 0 < a₀)
    (ht : t ≤ T)
    (ha_nonneg : ∀ i, i ∈ Finset.Icc 1 T → 0 ≤ a i) :
    0 < a₀ + (Finset.Icc 1 t).sum a := by
  exact add_pos_of_pos_of_nonneg ha₀
    (sum_Icc_prefix_nonneg_of_Icc_nonneg a ht ha_nonneg)

private theorem log_one_add_div_eq_log_sub_log_of_pos_of_nonneg
    {a₀ s : ℝ} (ha₀ : 0 < a₀) (hs : 0 ≤ s) :
    Real.log (1 + s / a₀) = Real.log (a₀ + s) - Real.log a₀ := by
  have hnum : a₀ + s ≠ 0 := by positivity
  have hratio : 1 + s / a₀ = (a₀ + s) / a₀ := by
    field_simp [ha₀.ne']
  rw [hratio, Real.log_div hnum ha₀.ne']

/-- Lemma 4: logarithmic bound for a nonnegative adaptive denominator sum. -/
theorem lemma4_log_sum_bound
    (a₀ : ℝ) (a : ℕ → ℝ) (T : ℕ)
    (ha₀ : 0 < a₀) (ha_nonneg : ∀ t, t ∈ Finset.Icc 1 T → 0 ≤ a t) :
    (Finset.sum (Finset.Icc 1 T)
      (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
        Real.log (1 + Finset.sum (Finset.Icc 1 T) a / a₀) := by
  exact sum_div_add_prefix_sum_le_log_one_add_sum_div_of_pos_of_nonneg
    a₀ a T ha₀ ha_nonneg

/-- Theorem 1 output-integrability supplier from the Section 3 `G`-Lipschitz
route.

The objective-gradient norm is source-derived bounded by `G`; generated
iterates are a.e. measurable from the Algorithm 1 sample-prefix semantics.
Together these make every finite output-window gradient norm integrable. -/
private theorem theorem1_output_window_integrability_from_G_lipschitz
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (T : ℕ) :
    ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ := by
  intro i
  have hiter_prefix := lemma3_iterate_prefixAEMeasurable S μ hsec3 i.val
  have hobj_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < i.val + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => objectiveGradient S (iterate S i.val ω)) μ :=
    hiter_prefix.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 0).measurable
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3
      (prefixAEMeasurable.comp_measurable hobj_prefix continuous_norm.measurable)).aestronglyMeasurable
  refine Integrable.of_bound hZ_aesm (C := G) ?_
  filter_upwards with ω
  simpa [Real.norm_of_nonneg (norm_nonneg _)] using
    section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S i.val ω)

/-- Totalized finite-window form of the weighted gradient-square sum appearing
in Theorem 1 proof lines 421-434.  This is the paper's
`𝔼[∑ η_t ‖∇F(x_t)‖²]`, with one-based paper times represented by `Fin T`. -/
noncomputable def theorem1WeightedGradientNormSqSum
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) : ℝ :=
  SOptLib.expected_weighted_certificate_energy Finset.univ μ
    (fun i : Fin T => fun ω => stepsize S i.val ω)
    (fun i : Fin T => fun ω => objectiveGradient S (iterate S i.val ω))

/-- Finite telescope with a random initial potential.

SOptLib's deterministic-initial telescope lemmas do not fit STORM's Theorem 1
Lyapunov potential directly, because the initial potential contains the random
initial error `ε₁`.  This private bridge is the exact Mathlib/Bochner
bookkeeping shape needed by proof steps 13-16: commute a finite sum through the
integral, telescope pointwise, and use a pointwise lower bound on the terminal
potential. -/
private theorem integral_sum_telescope_bound_of_random_initial_lower_bound
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (times : Finset ι) (drop : ι → Ω → ℝ)
    (initial terminal : Ω → ℝ) (lower : ℝ)
    (hdrop_int : ∀ i ∈ times, Integrable (drop i) P)
    (hinitial_int : Integrable initial P)
    (hpoint : ∀ ω, Finset.sum times (fun i => drop i ω) = initial ω - terminal ω)
    (hlower : ∀ ω, lower ≤ terminal ω) :
    Finset.sum times (fun i => ∫ ω, drop i ω ∂P) ≤
      (∫ ω, initial ω ∂P) - lower := by
  classical
  have hsum_int :
      Integrable (fun ω => Finset.sum times (fun i => drop i ω)) P :=
    MeasureTheory.integrable_finset_sum times hdrop_int
  have hright_int : Integrable (fun ω => initial ω - lower) P :=
    hinitial_int.sub (integrable_const (c := lower))
  have hsum_eq :
      Finset.sum times (fun i => ∫ ω, drop i ω ∂P) =
        ∫ ω, Finset.sum times (fun i => drop i ω) ∂P := by
    rw [MeasureTheory.integral_finset_sum times hdrop_int]
  have hbound :
      ∫ ω, Finset.sum times (fun i => drop i ω) ∂P ≤
        ∫ ω, initial ω - lower ∂P := by
    refine integral_mono hsum_int hright_int ?_
    intro ω
    calc
      Finset.sum times (fun i => drop i ω) = initial ω - terminal ω := hpoint ω
      _ ≤ initial ω - lower := sub_le_sub_left (hlower ω) (initial ω)
  have hright_eval :
      (∫ ω, initial ω - lower ∂P) = (∫ ω, initial ω ∂P) - lower := by
    rw [MeasureTheory.integral_sub hinitial_int (integrable_const (c := lower))]
    simp [integral_const, probReal_univ]
  calc
    Finset.sum times (fun i => ∫ ω, drop i ω ∂P)
        = ∫ ω, Finset.sum times (fun i => drop i ω) ∂P := hsum_eq
    _ ≤ ∫ ω, initial ω - lower ∂P := hbound
    _ = (∫ ω, initial ω ∂P) - lower := hright_eval

/-- Exact finite telescope for a random initial and random terminal potential.

This is the equality form needed before the paper's Lemma 1 and equation (4)
terms cancel; the lower-bound variant above is only for endpoint estimates. -/
private theorem integral_sum_telescope_eq_of_random_endpoints
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (times : Finset ι) (drop : ι → Ω → ℝ)
    (initial terminal : Ω → ℝ)
    (hdrop_int : ∀ i ∈ times, Integrable (drop i) P)
    (hinitial_int : Integrable initial P)
    (hpoint : ∀ ω, Finset.sum times (fun i => drop i ω) = initial ω - terminal ω) :
    Finset.sum times (fun i => ∫ ω, drop i ω ∂P) =
      (∫ ω, initial ω ∂P) - (∫ ω, terminal ω ∂P) := by
  exact _root_.integral_sum_telescope_eq_of_random_endpoints
    (μ := P) times drop initial terminal hdrop_int hinitial_int
    (Filter.Eventually.of_forall hpoint)

/-- Adjacent finite differences over `Fin T` telescope to the endpoint gap.

This is the Mathlib-facing reindexing bridge used by STORM's Lyapunov
potential: the paper sums over one finite time window, while Mathlib's
standard telescope lemma is stated over `Finset.range`. -/
private theorem fin_univ_adjacent_sub_telescope
    {G : Type*} [AddCommGroup G] (T : ℕ) (f : ℕ → G) :
    Finset.sum Finset.univ (fun i : Fin T => f i.val - f (i.val + 1)) =
      f 0 - f T := by
  exact sum_fin_adjacent_sub_eq_sub T f

/-- Denominator used by the previous-error part of the paper potential:
`η₀` at the initial index and `η_{t-1}` afterwards. -/
def theorem1PreviousErrorDenominator
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) : ℝ :=
  if n = 0 then initialStepsize S else stepsize S (n - 1) ω

/-- Positivity of the previous-error denominator in the shifted Lyapunov
potential under the generated quotient boundary. -/
private theorem theorem1PreviousErrorDenominator_pos_of_generated_boundary
    (S : Setup Ω Sample E)
    (hboundary : generatedStepsizeQuotientBoundary S) :
    ∀ n ω, 0 < theorem1PreviousErrorDenominator S n ω := by
  intro n ω
  unfold theorem1PreviousErrorDenominator
  by_cases hn : n = 0
  · have hw_pos : 0 < S.w := hboundary.1.1.1
    have hden_pos : 0 < Real.rpow S.w ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hw_pos ((1 : ℝ) / 3)
    simpa [hn, initialStepsize_eq, one_div] using
      div_pos hboundary.2 hden_pos
  · have hpred_pos :
        0 < stepsize S (n - 1) ω :=
      stepsize_pos_of_generated_quotient_boundary S hboundary (n - 1) ω
    simp [hn, hpred_pos]

/-- The shifted Lyapunov potential used in Theorem 1 proof steps 13-16.

This is the paper potential with `F*` subtracted:
`F(x_t)-F* + ‖ε_t‖²/(32 L² η_{t-1})`.  The shift makes the terminal lower
bound exactly `0`, while retaining the random initial-error term that appears
in the paper's step 16. -/
noncomputable def theorem1ShiftedLyapunovPotential
    (S : Setup Ω Sample E) (L fStar : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  SOptLib.objectiveGapScaledErrorPotential S.objectiveValue (iterate S)
    (error S) (theorem1PreviousErrorDenominator S) fStar (1 / (32 * L ^ 2)) n ω

/-- Adjacent-difference expansion of the shifted Lyapunov potential. -/
private theorem theorem1ShiftedLyapunovPotential_succ_sub
    (S : Setup Ω Sample E) (L fStar : ℝ) (n : ℕ) (ω : Ω) :
    theorem1ShiftedLyapunovPotential S L fStar (n + 1) ω -
        theorem1ShiftedLyapunovPotential S L fStar n ω =
      (S.objectiveValue (iterate S (n + 1) ω) -
          S.objectiveValue (iterate S n ω)) +
        (1 / (32 * L ^ 2)) *
          (‖error S (n + 1) ω‖ ^ 2 / stepsize S n ω -
            ‖error S n ω‖ ^ 2 / theorem1PreviousErrorDenominator S n ω) := by
  classical
  have hden_succ :
      theorem1PreviousErrorDenominator S (n + 1) ω = stepsize S n ω := by
    simp [theorem1PreviousErrorDenominator]
  simp [theorem1ShiftedLyapunovPotential, hden_succ]
  ring

/-- The shifted Lyapunov potential is nonnegative at every generated state. -/
private theorem theorem1ShiftedLyapunovPotential_nonneg
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G) :
    ∀ n ω, 0 ≤ theorem1ShiftedLyapunovPotential S L fStar n ω := by
  intro n ω
  have hobj_lower :
      fStar ≤ S.objectiveValue (iterate S n ω) :=
    hsec3.finite_lower_bound.1 ⟨iterate S n ω, rfl⟩
  have hgap_nonneg :
      0 ≤ S.objectiveValue (iterate S n ω) - fStar :=
    sub_nonneg.mpr hobj_lower
  have hden_pos :
      0 < theorem1PreviousErrorDenominator S n ω :=
    theorem1PreviousErrorDenominator_pos_of_generated_boundary S hgenerated n ω
  have herror_term_nonneg :
      0 ≤
        (1 / (32 * L ^ 2)) *
          (‖error S n ω‖ ^ 2 / theorem1PreviousErrorDenominator S n ω) := by
    have hscale_nonneg : 0 ≤ (1 : ℝ) / (32 * L ^ 2) := by
      positivity
    exact mul_nonneg hscale_nonneg
      (div_nonneg (sq_nonneg _) (le_of_lt hden_pos))
  simpa [theorem1ShiftedLyapunovPotential] using
    add_nonneg hgap_nonneg herror_term_nonneg

/-- Pointwise finite-window telescope for the shifted Lyapunov potential used
in Theorem 1 proof steps 13-16. -/
private theorem theorem1_shifted_lyapunov_potential_fin_telescope
    (S : Setup Ω Sample E) (L fStar : ℝ) (T : ℕ) :
    ∀ ω,
      Finset.sum Finset.univ
          (fun i : Fin T =>
            theorem1ShiftedLyapunovPotential S L fStar i.val ω -
              theorem1ShiftedLyapunovPotential S L fStar (i.val + 1) ω) =
        theorem1ShiftedLyapunovPotential S L fStar 0 ω -
          theorem1ShiftedLyapunovPotential S L fStar T ω := by
  intro ω
  exact fin_univ_adjacent_sub_telescope T
    (fun n => theorem1ShiftedLyapunovPotential S L fStar n ω)

/-- Error-increment side of equation (4) in the Theorem 1 proof. -/
noncomputable def theorem1Equation4ErrorIncrementLHS
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) (L : ℝ) : ℝ :=
  ∫ ω, (1 / (32 * L ^ 2)) *
    Finset.sum Finset.univ
      (fun i : Fin T =>
        ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω -
          ‖error S i.val ω‖ ^ 2 / theorem1PreviousErrorDenominator S i.val ω) ∂μ

/-- Right-hand side of equation (4): the logarithmic `A_t` budget plus the
gradient/error terms that cancel against Lemma 1 in the Lyapunov telescope. -/
noncomputable def theorem1Equation4RHS
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) (L : ℝ) : ℝ :=
  S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) +
    ∫ ω, Finset.sum Finset.univ
      (fun i : Fin T =>
        stepsize S i.val ω / 8 *
            ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
          3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) ∂μ

/-- The finite-window integral of the Lemma 2 RHS before equation (4)'s
`B_t` cancellation and logarithmic `A_t` estimate. -/
noncomputable def theorem1Equation4Lemma2RHSWindowIntegral
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) (L : ℝ) : ℝ :=
  Finset.sum Finset.univ
    (fun i : Fin T =>
      ∫ ω,
        2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
            ‖stochasticGradient S (iterate S (i.val + 1) ω)
              (S.sample (i.val + 1) ω)‖ ^ 2 +
          (((1 - nextMomentumWeight S i.val ω) ^ 2 *
              (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
          4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
            stepsize S i.val ω *
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ)

/-- The finite-window integral of the previous-error denominator term
`‖ε_t‖² / η_{t-1}` appearing on equation (4)'s left-hand side. -/
noncomputable def theorem1Equation4PreviousErrorWindowIntegral
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) : ℝ :=
  Finset.sum Finset.univ
    (fun i : Fin T =>
      ∫ ω,
        ‖error S i.val ω‖ ^ 2 /
          theorem1PreviousErrorDenominator S i.val ω ∂μ)

/-- The finite-window integral of the gradient/error summand on the right side
of equation (4). -/
noncomputable def theorem1Equation4GradientErrorWindowIntegral
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) : ℝ :=
  ∫ ω, Finset.sum Finset.univ
    (fun i : Fin T =>
      stepsize S i.val ω / 8 *
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
        3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) ∂μ

/-- Component form of equation (4)'s right-hand side. -/
theorem theorem1Equation4RHS_eq_logBudget_add_gradientErrorWindowIntegral
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) (L : ℝ) :
    theorem1Equation4RHS S μ T L =
      S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) +
        theorem1Equation4GradientErrorWindowIntegral S μ T := by
  rfl

/-- Expected root-sum quantity `𝔼[sqrt(∑ ‖∇F(x_t)‖²)]` used in Theorem 1
proof steps 20-31. -/
noncomputable def theorem1ExpectedRootGradientNormSqSum
    [MeasurableSpace Ω] (S : Setup Ω Sample E) (μ : Measure Ω) (T : ℕ) : ℝ :=
  SOptLib.expectedRootSumSqNorm Finset.univ μ
    (fun i : Fin T => fun ω => objectiveGradient S (iterate S i.val ω))

/-- Source proof-step RHS for Theorem 1's expected root-sum estimate. -/
def theorem1ExpectedRootGradientNormSqSumRHS
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) : ℝ :=
  Real.sqrt (2 * theorem1M S T L σ fStar) *
      Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6) +
    2 * Real.rpow (theorem1M S T L σ fStar) ((3 : ℝ) / 4)

/-- A generated Lemma 2 source comparison exposes the totalized one-step
integral recurrence used in the source proof of Theorem 1.

This is the executable source/totalized bridge missing from the previous
equation (4) handoff: `sourceExpectationLE` supplies only `Option`
expectation witnesses, while equation (4) is stated with the generated
totalized Algorithm 1 quantities.  The generated quotient boundary supplies
the exact source-expression equalities. -/
private theorem theorem1_lemma2_route_generated_integral_bound_of_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (L : ℝ) (t : ℕ)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hlemma2 :
      sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t)) :
    ∫ ω, ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω ∂μ ≤
      ∫ ω,
        2 * S.c ^ 2 * stepsize S t ω ^ 3 *
            ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
          (((1 - nextMomentumWeight S t ω) ^ 2 *
              (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
                ‖error S t ω‖ ^ 2) / stepsize S t ω) +
          4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 * stepsize S t ω *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2 ∂μ := by
  classical
  rcases hlemma2 with ⟨lhs, rhs, hlhs, hrhs, hle⟩
  rw [sourceExpectationValue_eq_some_iff] at hlhs
  rw [sourceExpectationValue_eq_some_iff] at hrhs
  rcases hlhs with ⟨_hlhs_def, _hlhs_int, hlhs_val⟩
  rcases hrhs with ⟨_hrhs_def, _hrhs_int, hrhs_val⟩
  let Z : Ω → ℝ := fun ω => ‖error S (t + 1) ω‖ ^ 2 / stepsize S t ω
  let W : Ω → ℝ := fun ω =>
    2 * S.c ^ 2 * stepsize S t ω ^ 3 *
        ‖stochasticGradient S (iterate S (t + 1) ω) (S.sample (t + 1) ω)‖ ^ 2 +
      (((1 - nextMomentumWeight S t ω) ^ 2 *
          (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
            ‖error S t ω‖ ^ 2) / stepsize S t ω) +
      4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 * stepsize S t ω *
        ‖objectiveGradient S (iterate S t ω)‖ ^ 2
  have hlocal : lemma2LocalQuotientBoundary S L t :=
    lemma2LocalQuotientBoundary_of_generated_boundary S hgenerated L t
  have hZ_get :
      (fun ω => (lemma2LHSExpr S t ω).getD 0) = Z := by
    funext ω
    rw [lemma2LHSExpr_eq_some_of_local_boundary S hlocal ω]
    rfl
  have hW_get :
      (fun ω => (lemma2RHSExpr S L t ω).getD 0) = W := by
    funext ω
    rw [lemma2RHSExpr_eq_some_of_local_boundary S hlocal ω]
    rfl
  have hlhs_total : lhs = ∫ ω, Z ω ∂μ := by
    simpa [hZ_get] using hlhs_val
  have hrhs_total : rhs = ∫ ω, W ω ∂μ := by
    simpa [hW_get] using hrhs_val
  simpa [Z, W, hlhs_total, hrhs_total] using hle

/-- Finite-window aggregation of the generated Lemma 2 recurrence in the
integral form consumed by equation (4). -/
private theorem theorem1_lemma2_route_finset_integral_bound_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (L : ℝ) (T : ℕ)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hlemma2_route :
      ∀ t, sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t)) :
    Finset.sum Finset.univ
        (fun i : Fin T =>
          ∫ ω, ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω ∂μ) ≤
      Finset.sum Finset.univ
        (fun i : Fin T =>
          ∫ ω,
            2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
                ‖stochasticGradient S (iterate S (i.val + 1) ω)
                  (S.sample (i.val + 1) ω)‖ ^ 2 +
              (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                  (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                    ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
              4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
                stepsize S i.val ω *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ) := by
  classical
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact
    theorem1_lemma2_route_generated_integral_bound_of_boundary
      S μ L i.val hgenerated (hlemma2_route i.val)

/-- Remaining scalar/integral-window form of equation (4) after the source
Lemma 2 route has already been converted into generated totalized integrals.

This is now the first genuine equation (4) proof leaf: it no longer has to
unpack source `Option` expectations or justify the generated-boundary route.
It keeps the generated and Section 3 inputs that the paper uses in this
equation: the adaptive denominator has to be the Algorithm 1 denominator, and
the final logarithmic term uses the sampled-gradient window from Lemma 4. -/
private theorem theorem1_log_window_bound_from_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (T : ℕ) (ω : Ω)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀)) :
    (Finset.sum (Finset.Icc 1 T)
      (fun t =>
        ‖stochasticGradient S (iterate S t ω) (S.sample t ω)‖ ^ 2 /
          (S.w + Finset.sum (Finset.Icc 1 t)
            (fun i => ‖stochasticGradient S (iterate S i ω) (S.sample i ω)‖ ^ 2)))) ≤
        Real.log
          (1 +
            Finset.sum (Finset.Icc 1 T)
              (fun i => ‖stochasticGradient S (iterate S i ω) (S.sample i ω)‖ ^ 2) /
                S.w) := by
  classical
  exact
    hlemma4_route S.w
      (fun i => ‖stochasticGradient S (iterate S i ω) (S.sample i ω)‖ ^ 2) T
      hgenerated.1.1.1
      (by
        intro t _ht
        positivity)

/-- Integrability of equation (4)'s left finite-window summands under the
generated Algorithm 1 quotient boundary.

This is a named version of the first local Mathlib linearity obligation in
equation (4): finite-sum integral rewriting needs each displayed
`‖ε_{t+1}‖² / η_t` quotient to be integrable.  The proof reuses the generated
Lemma 2 bounded-error and reciprocal-stepsize suppliers, not the retired
local-only Lemma 2 route. -/
private theorem theorem1_equation4_lhsStep_integrable_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    ∀ i : Fin T, i ∈ Finset.univ →
      Integrable
        (fun ω => ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω) μ := by
  intro i _hi
  have hrecip :=
    lemma2_generated_reciprocal_stepsize_eventually_bound
      S μ hsec3 i.val hgenerated
  have herr :=
    lemma2_generated_next_error_eventually_bound
      S μ hsec3 i.val hgenerated
  exact
    lemma2_lhs_integrable_of_error_and_reciprocal_bounds
      S μ hsec3 i.val herr hrecip

/-- Integrability of equation (4)'s right finite-window Lemma 2 summands under
the generated Algorithm 1 quotient boundary.

This names the second local Mathlib linearity obligation in equation (4).  It
is the already-proved generated-boundary Lemma 2 RHS integrability specialized
to the finite Theorem 1 window. -/
private theorem theorem1_equation4_rhsStep_integrable_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    ∀ i : Fin T, i ∈ Finset.univ →
      Integrable
        (fun ω =>
          2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
              ‖stochasticGradient S (iterate S (i.val + 1) ω)
                (S.sample (i.val + 1) ω)‖ ^ 2 +
            (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                  ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
            4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
              stepsize S i.val ω *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) μ := by
  intro i _hi
  have hrhs :=
    lemma2_generated_rhs_integrable S μ hsec3 i.val hgenerated
  refine hrhs.congr ?_
  filter_upwards with ω
  rfl

/-- Integrability of equation (4)'s previous-error denominator summand under
the generated Algorithm 1 quotient boundary.

This exposes the quotient-window well-definedness used both by equation (4)
and by the shifted Lyapunov telescope.  It is derived from the generated
reciprocal-stepsize and error bounds, not from the retired local-only Lemma 2
route. -/
private theorem theorem1_equation4_prevStep_integrable_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    ∀ i : Fin T, i ∈ Finset.univ →
      Integrable
        (fun ω =>
          ‖error S i.val ω‖ ^ 2 /
            theorem1PreviousErrorDenominator S i.val ω) μ := by
  intro i _hi
  by_cases hi : i.val = 0
  · have hloc3 : lemma3LocalQuotientBoundary S 0 := by
      simpa [lemma3LocalQuotientBoundary] using hgenerated
    rcases lemma3_generated_error_eventually_bound S μ hsec3 0 hloc3 with
      ⟨B, _hB_nonneg, hB⟩
    have herror_prefix :
        @prefixAEMeasurable Ω (DecisionSpace d) _ _
          (⨆ j < 0 + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          (error S 0) μ :=
      lemma3_error_prefixAEMeasurable S μ hsec3 0
    have herror_aesm : AEStronglyMeasurable (error S 0) μ :=
      (prefixAEMeasurable.aemeasurable S μ hsec3 herror_prefix).aestronglyMeasurable
    have hsq_int : Integrable (fun ω => ‖error S 0 ω‖ ^ 2) μ :=
      (SOptLib.integrable_sq_norm_of_ae_bound herror_aesm hB).1
    have hconst :
        Integrable
          (fun ω => (1 / initialStepsize S) * ‖error S 0 ω‖ ^ 2) μ :=
      hsq_int.const_mul (1 / initialStepsize S)
    simpa [theorem1PreviousErrorDenominator, hi, div_eq_mul_inv, one_div,
      mul_comm, mul_left_comm, mul_assoc] using hconst
  · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
    have herr :=
      lemma2_generated_next_error_eventually_bound
        S μ hsec3 (i.val - 1) hgenerated
    have hrecip :=
      lemma2_generated_reciprocal_stepsize_eventually_bound
        S μ hsec3 (i.val - 1) hgenerated
    have hbase :
        Integrable
          (fun ω =>
            ‖error S ((i.val - 1) + 1) ω‖ ^ 2 /
              stepsize S (i.val - 1) ω) μ :=
      lemma2_lhs_integrable_of_error_and_reciprocal_bounds
        S μ hsec3 (i.val - 1) herr hrecip
    have hsucc : (i.val - 1) + 1 = i.val :=
      Nat.succ_pred_eq_of_pos hpos
    rw [hsucc] at hbase
    simpa [theorem1PreviousErrorDenominator, hi, hsucc] using hbase

/-- Equation (4) integral-lift leaf after the generated Lemma 2 recurrence has
been scaled.

This is a finite-window Bochner-integral bookkeeping step: commute the left
window through the integral, subtract the previous-error window, and use the
already-scaled Lemma 2 comparison.  It deliberately contains no scalar
`A_t/B_t/C_t` normalization burden. -/
private theorem theorem1_equation4_lift_lhs_from_scaled_lemma2_window
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hlemma2_window_scaled :
      (1 / (32 * L ^ 2)) *
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ∫ ω, ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω ∂μ) ≤
        (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L) :
    theorem1Equation4ErrorIncrementLHS S μ T L ≤
      (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
        (1 / (32 * L ^ 2)) *
          theorem1Equation4PreviousErrorWindowIntegral S μ T := by
  classical
  let scale : ℝ := 1 / (32 * L ^ 2)
  let lhsStep : Fin T → Ω → ℝ := fun i ω =>
    ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω
  let prevStep : Fin T → Ω → ℝ := fun i ω =>
    ‖error S i.val ω‖ ^ 2 / theorem1PreviousErrorDenominator S i.val ω
  have hlhs_int : ∀ i ∈ Finset.univ, Integrable (lhsStep i) μ := by
    simpa [lhsStep] using
      theorem1_equation4_lhsStep_integrable_of_generated_boundary
        S μ T hsec3 hgenerated
  have hprev_int : ∀ i ∈ Finset.univ, Integrable (prevStep i) μ := by
    intro i _hi
    by_cases hi : i.val = 0
    · have hloc3 : lemma3LocalQuotientBoundary S 0 := by
        simpa [lemma3LocalQuotientBoundary] using hgenerated
      rcases lemma3_generated_error_eventually_bound S μ hsec3 0 hloc3 with
        ⟨B, _hB_nonneg, hB⟩
      have herror_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < 0 + 1, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (error S 0) μ :=
        lemma3_error_prefixAEMeasurable S μ hsec3 0
      have herror_aesm : AEStronglyMeasurable (error S 0) μ :=
        (prefixAEMeasurable.aemeasurable S μ hsec3 herror_prefix).aestronglyMeasurable
      have hsq_int : Integrable (fun ω => ‖error S 0 ω‖ ^ 2) μ :=
        (SOptLib.integrable_sq_norm_of_ae_bound herror_aesm hB).1
      have hconst :
          Integrable
            (fun ω => (1 / initialStepsize S) * ‖error S 0 ω‖ ^ 2) μ :=
        hsq_int.const_mul (1 / initialStepsize S)
      simpa [prevStep, theorem1PreviousErrorDenominator, hi, div_eq_mul_inv,
        one_div, mul_comm, mul_left_comm, mul_assoc] using hconst
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
      have herr :=
        lemma2_generated_next_error_eventually_bound
          S μ hsec3 (i.val - 1) hgenerated
      have hrecip :=
        lemma2_generated_reciprocal_stepsize_eventually_bound
          S μ hsec3 (i.val - 1) hgenerated
      have hbase :
          Integrable
            (fun ω =>
              ‖error S ((i.val - 1) + 1) ω‖ ^ 2 /
                stepsize S (i.val - 1) ω) μ :=
        lemma2_lhs_integrable_of_error_and_reciprocal_bounds
          S μ hsec3 (i.val - 1) herr hrecip
      have hsucc : (i.val - 1) + 1 = i.val :=
        Nat.succ_pred_eq_of_pos hpos
      rw [hsucc] at hbase
      simpa [prevStep, theorem1PreviousErrorDenominator, hi,
        hsucc] using hbase
  have hdiff_int :
      ∀ i ∈ Finset.univ, Integrable (fun ω => lhsStep i ω - prevStep i ω) μ := by
    intro i hi
    exact (hlhs_int i hi).sub (hprev_int i hi)
  have hdiff_sum :
      (∫ ω, Finset.sum Finset.univ
        (fun i : Fin T => lhsStep i ω - prevStep i ω) ∂μ) =
        Finset.sum Finset.univ
          (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) -
            Finset.sum Finset.univ
              (fun i : Fin T => ∫ ω, prevStep i ω ∂μ) := by
    calc
      (∫ ω, Finset.sum Finset.univ
          (fun i : Fin T => lhsStep i ω - prevStep i ω) ∂μ) =
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, lhsStep i ω - prevStep i ω ∂μ) := by
            rw [MeasureTheory.integral_finset_sum Finset.univ hdiff_int]
      _ = Finset.sum Finset.univ
            (fun i : Fin T => (∫ ω, lhsStep i ω ∂μ) -
              (∫ ω, prevStep i ω ∂μ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [MeasureTheory.integral_sub (hlhs_int i hi) (hprev_int i hi)]
      _ = Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) -
            Finset.sum Finset.univ
              (fun i : Fin T => ∫ ω, prevStep i ω ∂μ) := by
            rw [Finset.sum_sub_distrib]
  have hlhs_eq :
      theorem1Equation4ErrorIncrementLHS S μ T L =
        scale *
          (Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) -
            Finset.sum Finset.univ
              (fun i : Fin T => ∫ ω, prevStep i ω ∂μ)) := by
    calc
      theorem1Equation4ErrorIncrementLHS S μ T L =
          ∫ ω, scale *
            Finset.sum Finset.univ
              (fun i : Fin T => lhsStep i ω - prevStep i ω) ∂μ := by
            simp [theorem1Equation4ErrorIncrementLHS, scale, lhsStep, prevStep,
              theorem1PreviousErrorDenominator]
      _ = scale *
          (∫ ω, Finset.sum Finset.univ
            (fun i : Fin T => lhsStep i ω - prevStep i ω) ∂μ) := by
            rw [MeasureTheory.integral_const_mul]
      _ = scale *
          (Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) -
            Finset.sum Finset.univ
              (fun i : Fin T => ∫ ω, prevStep i ω ∂μ)) := by
            rw [hdiff_sum]
  have hscaled :
      scale *
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) ≤
        scale * theorem1Equation4Lemma2RHSWindowIntegral S μ T L := by
    simpa [scale, lhsStep] using hlemma2_window_scaled
  have hmain :
      scale *
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) -
          scale *
            Finset.sum Finset.univ
              (fun i : Fin T => ∫ ω, prevStep i ω ∂μ) ≤
        scale * theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
          scale * theorem1Equation4PreviousErrorWindowIntegral S μ T := by
    simpa [theorem1Equation4PreviousErrorWindowIntegral, prevStep] using
      sub_le_sub_right hscaled
        (scale *
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, prevStep i ω ∂μ))
  simpa [hlhs_eq, scale, sub_eq_add_neg, mul_add, mul_sub] using hmain

/-- The `C_t` coefficient reduction in equation (4).

After scaling the Lemma 2 `C_t` contribution by `1/(32L²)`, the paper uses
`a_{t+1} ≤ 1` to replace `(1-a_{t+1})²` by `1`, giving the displayed
`η_t/8 * ‖∇F(x_t)‖²` term.  The nonnegativity of `a_{t+1}` is derived from the
printed `c` relation and generated positive stepsizes. -/
private theorem theorem1_equation4_scaled_C_term_le_gradient_step
    (S : Setup Ω Sample E) {L G : ℝ}
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hc_eq : S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3))
    (t : ℕ) (ω : Ω) :
    (1 / (32 * L ^ 2)) *
        (4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 *
          stepsize S t ω *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2) ≤
      stepsize S t ω / 8 *
        ‖objectiveGradient S (iterate S t ω)‖ ^ 2 := by
  classical
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hk_pos : 0 < S.k := hEq4Scalar.k_pos
  have hη_pos : 0 < stepsize S t ω :=
    stepsize_pos_of_generated_quotient_boundary S hgenerated t ω
  have hη_nonneg : 0 ≤ stepsize S t ω := le_of_lt hη_pos
  have hden_pos : 0 < 7 * L * S.k ^ 3 := by
    positivity
  have hc_nonneg : 0 ≤ S.c := by
    rw [hc_eq]
    exact add_nonneg (by positivity) (div_nonneg (sq_nonneg G) (le_of_lt hden_pos))
  have ha_nonneg : 0 ≤ nextMomentumWeight S t ω := by
    simpa [nextMomentumWeight, momentumWeight] using
      mul_nonneg hc_nonneg (sq_nonneg (stepsize S t ω))
  have ha_le_one : nextMomentumWeight S t ω ≤ 1 :=
    hEq4Scalar.nextMomentumWeight_le_one t ω
  have hone_sub_sq_le_one :
      (1 - nextMomentumWeight S t ω) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (nextMomentumWeight S t ω),
      sq_nonneg (1 - nextMomentumWeight S t ω), ha_nonneg, ha_le_one]
  have htarget_nonneg :
      0 ≤ stepsize S t ω / 8 *
        ‖objectiveGradient S (iterate S t ω)‖ ^ 2 := by
    exact mul_nonneg (div_nonneg hη_nonneg (by norm_num)) (sq_nonneg _)
  have hscaled_eq :
      (1 / (32 * L ^ 2)) *
          (4 * (1 - nextMomentumWeight S t ω) ^ 2 * L ^ 2 *
            stepsize S t ω *
              ‖objectiveGradient S (iterate S t ω)‖ ^ 2) =
        (1 - nextMomentumWeight S t ω) ^ 2 *
          (stepsize S t ω / 8 *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2) := by
    field_simp [ne_of_gt hL_pos]
    ring
  rw [hscaled_eq]
  simpa using
    mul_le_mul_of_nonneg_right hone_sub_sq_le_one htarget_nonneg

/-- The `c`-coefficient identity used in the `B_t` part of equation (4).

This is Theorem 1 proof lines 386-388 after substituting the printed
`c = 28L² + G²/(7Lk³)`: the coefficient `η_t(4L²-c)` is exactly
`(-24L² - G²/(7Lk³))η_t`. -/
private theorem theorem1_equation4_B_c_coefficient_identity
    (S : Setup Ω Sample E) {L G : ℝ}
    (hc_eq : S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3))
    (t : ℕ) (ω : Ω) :
    stepsize S t ω * (4 * L ^ 2 - S.c) =
      (-24 * L ^ 2 - G ^ 2 / (7 * L * S.k ^ 3)) *
        stepsize S t ω := by
  rw [hc_eq]
  ring

/-- Error-weighted form of `theorem1_equation4_B_c_coefficient_identity`.

This is the source proof's negative `c` contribution to the `B_t`
coefficient, before it is combined with the reciprocal-stepsize difference. -/
private theorem theorem1_equation4_B_c_error_term_identity
    (S : Setup Ω Sample E) {L G : ℝ}
    (hc_eq : S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3))
    (t : ℕ) (ω : Ω) :
    (stepsize S t ω * (4 * L ^ 2 - S.c)) *
        ‖error S t ω‖ ^ 2 =
      ((-24 * L ^ 2 - G ^ 2 / (7 * L * S.k ^ 3)) *
        stepsize S t ω) * ‖error S t ω‖ ^ 2 := by
  rw [theorem1_equation4_B_c_coefficient_identity S hc_eq t ω]

/-- The first `B_t` simplification: because `0 ≤ a_{t+1} ≤ 1`, the factor
`(1-a_{t+1})²` is bounded by `1-a_{t+1}`.

This is the pointwise scalar part of Theorem 1 proof lines 327-360, before the
reciprocal-stepsize difference and the `c`-coefficient identity are combined. -/
private theorem theorem1_equation4_B_square_factor_le_unsquared
    (S : Setup Ω Sample E) {L G : ℝ}
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hc_eq : S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3))
    (t : ℕ) (ω : Ω) :
    (((1 - nextMomentumWeight S t ω) ^ 2 *
        (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
          ‖error S t ω‖ ^ 2) / stepsize S t ω) ≤
      (((1 - nextMomentumWeight S t ω) *
        (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
          ‖error S t ω‖ ^ 2) / stepsize S t ω) := by
  classical
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hk_pos : 0 < S.k := hEq4Scalar.k_pos
  have hη_pos : 0 < stepsize S t ω :=
    stepsize_pos_of_generated_quotient_boundary S hgenerated t ω
  have hden_pos : 0 < 7 * L * S.k ^ 3 := by
    positivity
  have hc_nonneg : 0 ≤ S.c := by
    rw [hc_eq]
    exact add_nonneg (by positivity) (div_nonneg (sq_nonneg G) (le_of_lt hden_pos))
  have ha_nonneg : 0 ≤ nextMomentumWeight S t ω := by
    simpa [nextMomentumWeight, momentumWeight] using
      mul_nonneg hc_nonneg (sq_nonneg (stepsize S t ω))
  have ha_le_one : nextMomentumWeight S t ω ≤ 1 :=
    hEq4Scalar.nextMomentumWeight_le_one t ω
  have hone_sub_nonneg : 0 ≤ 1 - nextMomentumWeight S t ω :=
    sub_nonneg.mpr ha_le_one
  have hone_sub_le_one : 1 - nextMomentumWeight S t ω ≤ 1 := by
    linarith
  have hsquare_le :
      (1 - nextMomentumWeight S t ω) ^ 2 ≤
        1 - nextMomentumWeight S t ω := by
    nlinarith [sq_nonneg (1 - nextMomentumWeight S t ω),
      hone_sub_nonneg, hone_sub_le_one]
  have hfactor_nonneg :
      0 ≤
        (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
          ‖error S t ω‖ ^ 2 / stepsize S t ω := by
    exact div_nonneg
      (mul_nonneg (by positivity) (sq_nonneg _))
      (le_of_lt hη_pos)
  have hmul :=
    mul_le_mul_of_nonneg_right hsquare_le hfactor_nonneg
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Pointwise `B_t` cancellation once the reciprocal-stepsize estimate has
been supplied.

This is Theorem 1 proof lines 354-390 at the exact scalar granularity used by
equation (4): the only non-algebraic premise is the paper's reciprocal
adaptive-stepsize estimate
`η_t⁻¹ - η_{t-1}⁻¹ ≤ G² η_t/(7 L k³)`.  The rest is the printed
substitution `a_{t+1}=cη_t²` and
`c = 28L² + G²/(7Lk³)`. -/
private theorem theorem1_equation4_B_pointwise_cancel_of_reciprocal_bound
    (S : Setup Ω Sample E) {L G : ℝ}
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hc_eq : S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3))
    (t : ℕ) (ω : Ω)
    (hrecip :
      (1 / stepsize S t ω -
          1 / theorem1PreviousErrorDenominator S t ω) ≤
        (G ^ 2 / (7 * L * S.k ^ 3)) * stepsize S t ω) :
    (((1 - nextMomentumWeight S t ω) ^ 2 *
        (1 + 4 * L ^ 2 * stepsize S t ω ^ 2) *
          ‖error S t ω‖ ^ 2) / stepsize S t ω) -
      ‖error S t ω‖ ^ 2 / theorem1PreviousErrorDenominator S t ω ≤
        -24 * L ^ 2 * stepsize S t ω * ‖error S t ω‖ ^ 2 := by
  simpa [nextMomentumWeight, momentumWeight] using
    (SOptLib.complementary_quadratic_weight_reciprocal_increment_absorb
      (stepsize S t ω) (theorem1PreviousErrorDenominator S t ω) S.c
      (4 * L ^ 2) (24 * L ^ 2) (G ^ 2 / (7 * L * S.k ^ 3))
      (‖error S t ω‖ ^ 2)
      (stepsize_pos_of_generated_quotient_boundary S hgenerated t ω)
      (by
        rw [hc_eq]
        exact add_nonneg (by positivity)
          (div_nonneg (sq_nonneg G) (by positivity [hEq4Scalar.L_pos, hEq4Scalar.k_pos])))
      (by positivity) (by simpa [nextMomentumWeight, momentumWeight] using
        hEq4Scalar.nextMomentumWeight_le_one t ω)
      (by positivity) (by rw [hc_eq]; ring_nf; exact le_rfl)
      hrecip)

/-- Finite-window `B_t` cancellation from the pointwise reciprocal-stepsize
estimate.

This consumes the exact B-term bridge above and returns the scaled negative
error budget used by equation (4). -/
private theorem theorem1_equation4_B_budget_of_reciprocal_bound
    {T : ℕ} (S : Setup Ω Sample E) {L G : ℝ}
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hc_eq : S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3))
    (ω : Ω)
    (hrecip :
      ∀ i : Fin T,
        (1 / stepsize S i.val ω -
            1 / theorem1PreviousErrorDenominator S i.val ω) ≤
          (G ^ 2 / (7 * L * S.k ^ 3)) * stepsize S i.val ω) :
    (1 / (32 * L ^ 2)) *
        Finset.sum Finset.univ
          (fun i : Fin T =>
            (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                  ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω)) -
      (1 / (32 * L ^ 2)) *
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ‖error S i.val ω‖ ^ 2 /
              theorem1PreviousErrorDenominator S i.val ω) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            -(3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)) := by
  classical
  let scale : ℝ := 1 / (32 * L ^ 2)
  let B : Fin T → ℝ := fun i =>
    (((1 - nextMomentumWeight S i.val ω) ^ 2 *
        (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
          ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω)
  let Prev : Fin T → ℝ := fun i =>
    ‖error S i.val ω‖ ^ 2 / theorem1PreviousErrorDenominator S i.val ω
  let Neg : Fin T → ℝ := fun i =>
    -24 * L ^ 2 * stepsize S i.val ω * ‖error S i.val ω‖ ^ 2
  have hpoint :
      ∀ i : Fin T, B i - Prev i ≤ Neg i := by
    intro i
    simpa [B, Prev, Neg] using
      theorem1_equation4_B_pointwise_cancel_of_reciprocal_bound
        S hgenerated hEq4Scalar hc_eq i.val ω (hrecip i)
  have hsum :
      Finset.sum Finset.univ (fun i : Fin T => B i - Prev i) ≤
        Finset.sum Finset.univ Neg :=
    Finset.sum_le_sum (fun i _hi => hpoint i)
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hscaled :
      scale * Finset.sum Finset.univ (fun i : Fin T => B i - Prev i) ≤
        scale * Finset.sum Finset.univ Neg :=
    mul_le_mul_of_nonneg_left hsum hscale_nonneg
  have hleft :
      scale * Finset.sum Finset.univ B -
          scale * Finset.sum Finset.univ Prev =
        scale * Finset.sum Finset.univ (fun i : Fin T => B i - Prev i) := by
    rw [Finset.sum_sub_distrib]
    ring
  have hright :
      scale * Finset.sum Finset.univ Neg =
        Finset.sum Finset.univ
          (fun i : Fin T =>
            -(3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    dsimp [scale, Neg]
    field_simp [ne_of_gt hEq4Scalar.L_pos]
    ring
  change
    scale * Finset.sum Finset.univ B -
        scale * Finset.sum Finset.univ Prev ≤
      Finset.sum Finset.univ
        (fun i : Fin T =>
          -(3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2))
  rw [hleft, ← hright]
  exact hscaled

/-- The reciprocal adaptive-stepsize estimate used in Theorem 1 equation (4).

This is the source proof's lines 364-382 in the generated Lean model.  The
one-third-power increment is bounded by the cube-root secant estimate above;
`w ≥ 2G²` compares the previous and current adaptive denominators, and
`η_t ≤ 1/(4L)` converts the resulting `η_t²` estimate to the printed
`η_t/(7L)` form. -/
private theorem theorem1_reciprocal_stepsize_increment_bound
    (S : Setup Ω Sample E) {L G : ℝ}
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (t : ℕ) (ω : Ω)
    (hG_curr :
      ‖S.stochasticGradient (iterate S t ω) (S.sample t ω)‖ ≤ G) :
    (1 / stepsize S t ω -
        1 / theorem1PreviousErrorDenominator S t ω) ≤
      (G ^ 2 / (7 * L * S.k ^ 3)) * stepsize S t ω := by
  let currBase : ℝ := S.w + cumulativeGradientNormSq S t ω
  let prevBase : ℝ := if t = 0 then S.w else S.w + cumulativeGradientNormSq S (t - 1) ω
  let inc : ℝ := ‖S.stochasticGradient (iterate S t ω) (S.sample t ω)‖ ^ 2
  have hprev_pos : 0 < prevBase := by
    dsimp [prevBase]
    by_cases ht : t = 0
    · simpa [ht] using hgenerated.1.1.1
    · simpa [ht] using (hgenerated.1.2 (t - 1) ω).1
  have hcurr_eq_prev_add : currBase = prevBase + inc := by
    dsimp [currBase, prevBase, inc]
    cases t with
    | zero =>
        simp [cumulativeGradientNormSq_zero, iterate_zero]
    | succ n =>
        have hsucc := cumulativeGradientNormSq_succ S n ω
        simp [Nat.succ_ne_zero, hsucc, add_comm, add_left_comm, add_assoc]
  have hinc_le_Gsq : inc ≤ G ^ 2 := by
    dsimp [inc]
    exact pow_le_pow_left₀ (norm_nonneg _) hG_curr 2
  have hprev_ge_w : S.w ≤ prevBase := by
    dsimp [prevBase]
    by_cases ht : t = 0
    · simp [ht]
    · have hsum_nonneg :
          0 ≤ cumulativeGradientNormSq S (t - 1) ω :=
        theorem1_cumulativeGradientNormSq_nonneg S (t - 1) ω
      simp [ht, hsum_nonneg]
  have hinc_half_prev : 2 * inc ≤ prevBase := by
    nlinarith [hEq4Scalar.w_ge_two_G_sq]
  have hstep :
      stepsize S t ω = S.k / Real.rpow currBase ((1 : ℝ) / 3) := by
    simpa [currBase] using stepsize_eq S t ω
  have hprev :
      theorem1PreviousErrorDenominator S t ω =
        S.k / Real.rpow prevBase ((1 : ℝ) / 3) := by
    dsimp [prevBase, theorem1PreviousErrorDenominator]
    by_cases ht : t = 0
    · simp [ht, initialStepsize_eq]
    · simp [ht, stepsize_eq]
  rw [hstep, hprev]
  exact reciprocal_inverse_cube_root_step_increment_le
    prevBase currBase inc S.k L (G ^ 2)
    hprev_pos hcurr_eq_prev_add (sq_nonneg _)
    hinc_le_Gsq hinc_half_prev hgenerated.2 hEq4Scalar.L_pos
    (by simpa [hstep] using hEq4Scalar.stepsize_le_one_over_fourL t ω)

/-- Finite-sum combiner for equation (4)'s pointwise scalar budget.

Once the `A_t+B_t` part has been bounded by the logarithmic budget and the
negative error term, and the `C_t` part has been bounded by the positive
gradient term, the exact displayed equation (4) pointwise inequality is only
finite-sum algebra.  This helper keeps that bookkeeping out of the remaining
source scalar leaf. -/
private theorem theorem1_equation4_pointwise_budget_of_AB_and_C_bounds
    {ι : Type*} [Fintype ι]
    (scale logBudget : ℝ)
    (A B C Prev Grad Err : ι → ℝ)
    (hAB :
      scale * Finset.sum Finset.univ (fun i => A i + B i) -
          scale * Finset.sum Finset.univ Prev ≤
        logBudget + Finset.sum Finset.univ Err)
    (hC :
      Finset.sum Finset.univ (fun i => scale * C i) ≤
        Finset.sum Finset.univ Grad) :
    scale * Finset.sum Finset.univ (fun i => A i + B i + C i) -
        scale * Finset.sum Finset.univ Prev ≤
      logBudget + Finset.sum Finset.univ (fun i => Grad i + Err i) := by
  classical
  have hC' :
      scale * Finset.sum Finset.univ C ≤
        Finset.sum Finset.univ Grad := by
    simpa [Finset.mul_sum] using hC
  calc
    scale * Finset.sum Finset.univ (fun i => A i + B i + C i) -
        scale * Finset.sum Finset.univ Prev
        =
      (scale * Finset.sum Finset.univ (fun i => A i + B i) -
          scale * Finset.sum Finset.univ Prev) +
        scale * Finset.sum Finset.univ C := by
          rw [Finset.sum_add_distrib]
          ring
    _ ≤ (logBudget + Finset.sum Finset.univ Err) +
        Finset.sum Finset.univ Grad := by
          exact add_le_add hAB hC'
    _ = logBudget + Finset.sum Finset.univ (fun i => Grad i + Err i) := by
          rw [Finset.sum_add_distrib]
          ring

/-- Pointwise scalar budget behind equation (4)'s `A_t/B_t/C_t` estimates.

This is the first surviving compiler-grounded proof target after the generated
Lemma 2 window has already been lifted to integrals.  It is intentionally
pointwise: the remaining work is the paper's scalar algebra in proof lines
354-397, not another `sourceExpectationLE` or integral-routing wrapper. -/
private theorem _voucher_step_theorem1_equation4_pointwise_scalar_budget_12
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀)) :
    ∀ᵐ ω ∂μ,
      (1 / (32 * L ^ 2)) *
            Finset.sum Finset.univ
              (fun i : Fin T =>
                2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
                    ‖stochasticGradient S (iterate S (i.val + 1) ω)
                      (S.sample (i.val + 1) ω)‖ ^ 2 +
                  (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                      (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                        ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
                  4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
                    stepsize S i.val ω *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) -
          (1 / (32 * L ^ 2)) *
            Finset.sum Finset.univ
              (fun i : Fin T =>
                ‖error S i.val ω‖ ^ 2 /
                  theorem1PreviousErrorDenominator S i.val ω) ≤
        S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) +
          Finset.sum Finset.univ
            (fun i : Fin T =>
              stepsize S i.val ω / 8 *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) := by
  classical
  have hc_eq :
      S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3) :=
    theorem1_equation4_c_eq_of_scalar_boundary S L G hEq4Scalar
  have hη_le : ∀ t ω, stepsize S t ω ≤ (1 : ℝ) / (4 * L) :=
    hEq4Scalar.stepsize_le_one_over_fourL
  have ha_le : ∀ t ω, nextMomentumWeight S t ω ≤ 1 :=
    hEq4Scalar.nextMomentumWeight_le_one
  have hw_ge_two : 2 * G ^ 2 ≤ S.w :=
    hEq4Scalar.w_ge_two_G_sq
  have hw_ge_four : (4 * L * S.k) ^ 3 ≤ S.w :=
    hEq4Scalar.w_ge_four_L_k_cube
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hk_pos : 0 < S.k := hEq4Scalar.k_pos
  have hgeneratedScalar : generatedStepsizeScalarBoundary S := hgenerated.1
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  have hG_window :
      ∀ i : Fin T,
        ∀ᵐ ω ∂μ,
          ‖stochasticGradient S (iterate S (i.val + 1) ω)
            (S.sample (i.val + 1) ω)‖ ≤ G := by
    intro i
    filter_upwards [hsec3.G_lipschitz_losses (i.val + 1)] with ω hω
    exact hω (iterate S (i.val + 1) ω)
  have hG_window_ae :
      ∀ᵐ ω ∂μ, ∀ i : Fin T,
        ‖stochasticGradient S (iterate S (i.val + 1) ω)
          (S.sample (i.val + 1) ω)‖ ≤ G := by
    exact (Filter.eventually_all).2 hG_window
  have hG_current_window :
      ∀ i : Fin T,
        ∀ᵐ ω ∂μ,
          ‖stochasticGradient S (iterate S i.val ω)
            (S.sample i.val ω)‖ ≤ G := by
    intro i
    filter_upwards [hsec3.G_lipschitz_losses i.val] with ω hω
    exact hω (iterate S i.val ω)
  have hG_current_window_ae :
      ∀ᵐ ω ∂μ, ∀ i : Fin T,
        ‖stochasticGradient S (iterate S i.val ω)
          (S.sample i.val ω)‖ ≤ G := by
    exact (Filter.eventually_all).2 hG_current_window
  filter_upwards [hG_window_ae, hG_current_window_ae] with
    ω hG_at_ω hG_current_at_ω
  have hη_at_ω : ∀ t, stepsize S t ω ≤ (1 : ℝ) / (4 * L) := by
    intro t
    exact hη_le t ω
  have ha_at_ω : ∀ t, nextMomentumWeight S t ω ≤ 1 := by
    intro t
    exact ha_le t ω
  have hA_shifted_den :
      ∀ i : Fin T,
        G ^ 2 +
            (Finset.Icc 1 (i.val + 1)).sum
              (fun j =>
                ‖S.stochasticGradient (iterate S j ω) (S.sample j ω)‖ ^ 2) ≤
          S.w + cumulativeGradientNormSq S i.val ω := by
    intro i
    exact
      theorem1_equation4_shifted_log_denominator_le_generated
        S i.val ω hw_ge_two (hG_at_ω i)
  have hA_source_log_or_G_zero :
      ((Finset.Icc 1 T).sum
        (fun t =>
          ‖S.stochasticGradient (iterate S t ω) (S.sample t ω)‖ ^ 2 /
            (G ^ 2 + (Finset.Icc 1 t).sum
              (fun j =>
                ‖S.stochasticGradient (iterate S j ω) (S.sample j ω)‖ ^ 2)))) ≤
          Real.log
            (1 +
              (Finset.Icc 1 T).sum
                (fun j =>
                  ‖S.stochasticGradient (iterate S j ω) (S.sample j ω)‖ ^ 2) /
                G ^ 2) ∨
        G = 0 := by
    by_cases hG_pos : 0 < G
    · left
      have hG_sq_pos : 0 < G ^ 2 := by positivity
      exact
        hlemma4_route (G ^ 2)
          (fun t =>
            ‖S.stochasticGradient (iterate S t ω) (S.sample t ω)‖ ^ 2) T
          hG_sq_pos
          (by
            intro t _ht
            positivity)
    · right
      exact le_antisymm (not_lt.mp hG_pos) hG_nonneg
  have hC_step :
      ∀ i : Fin T,
        (1 / (32 * L ^ 2)) *
            (4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
              stepsize S i.val ω *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ≤
          stepsize S i.val ω / 8 *
            ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 := by
    intro i
    exact
      theorem1_equation4_scaled_C_term_le_gradient_step
        S hgenerated hEq4Scalar hc_eq i.val ω
  have hC_sum :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            (1 / (32 * L ^ 2)) *
              (4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
                stepsize S i.val ω *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            stepsize S i.val ω / 8 *
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
    exact Finset.sum_le_sum (fun i _hi => hC_step i)
  have hB_c_step :
      ∀ i : Fin T,
        (stepsize S i.val ω * (4 * L ^ 2 - S.c)) *
            ‖error S i.val ω‖ ^ 2 =
          ((-24 * L ^ 2 - G ^ 2 / (7 * L * S.k ^ 3)) *
            stepsize S i.val ω) * ‖error S i.val ω‖ ^ 2 := by
    intro i
    exact theorem1_equation4_B_c_error_term_identity S hc_eq i.val ω
  have hB_c_sum :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            (stepsize S i.val ω * (4 * L ^ 2 - S.c)) *
              ‖error S i.val ω‖ ^ 2) =
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ((-24 * L ^ 2 - G ^ 2 / (7 * L * S.k ^ 3)) *
              stepsize S i.val ω) * ‖error S i.val ω‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact hB_c_step i
  have hB_square_step :
      ∀ i : Fin T,
        (((1 - nextMomentumWeight S i.val ω) ^ 2 *
            (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
              ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) ≤
          (((1 - nextMomentumWeight S i.val ω) *
            (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
              ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) := by
    intro i
    exact
      theorem1_equation4_B_square_factor_le_unsquared
        S hgenerated hEq4Scalar hc_eq i.val ω
  have hB_square_sum :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                  ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω)) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            (((1 - nextMomentumWeight S i.val ω) *
                (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                  ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω)) := by
    exact Finset.sum_le_sum (fun i _hi => hB_square_step i)
  let scale : ℝ := 1 / (32 * L ^ 2)
  let logBudget : ℝ :=
    S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ)
  let AStep : Fin T → ℝ := fun i =>
    2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
      ‖stochasticGradient S (iterate S (i.val + 1) ω)
        (S.sample (i.val + 1) ω)‖ ^ 2
  let BStep : Fin T → ℝ := fun i =>
    (((1 - nextMomentumWeight S i.val ω) ^ 2 *
        (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
          ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω)
  let CStep : Fin T → ℝ := fun i =>
    4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
      stepsize S i.val ω *
        ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2
  let PrevStep : Fin T → ℝ := fun i =>
    ‖error S i.val ω‖ ^ 2 / theorem1PreviousErrorDenominator S i.val ω
  let GradStep : Fin T → ℝ := fun i =>
    stepsize S i.val ω / 8 *
      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2
  let ErrStep : Fin T → ℝ := fun i =>
    -(3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)
  have hAB_budget :
      scale * Finset.sum Finset.univ (fun i : Fin T => AStep i + BStep i) -
          scale * Finset.sum Finset.univ PrevStep ≤
        logBudget + Finset.sum Finset.univ ErrStep := by
    have hA_budget :
        scale * Finset.sum Finset.univ AStep ≤ logBudget := by
      let coeff : ℝ := S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2)
      have hcoeff_nonneg : 0 ≤ coeff := by
        dsimp [coeff]
        positivity
      by_cases hG_zero : G = 0
      · have hA_zero : ∀ i : Fin T, AStep i = 0 := by
          intro i
          have hnorm_zero :
              ‖stochasticGradient S (iterate S (i.val + 1) ω)
                  (S.sample (i.val + 1) ω)‖ = 0 := by
            exact le_antisymm (by simpa [hG_zero] using hG_at_ω i) (norm_nonneg _)
          simp [AStep, hnorm_zero]
        have hsum_zero : Finset.sum Finset.univ AStep = 0 := by
          simp [hA_zero]
        have hlog_nonneg : 0 ≤ Real.log (T + 2 : ℝ) := by
          exact Real.log_nonneg (by
            have hT_nonneg : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
            linarith)
        have hlogBudget_nonneg : 0 ≤ logBudget := by
          dsimp [logBudget]
          positivity
        simpa [hsum_zero] using hlogBudget_nonneg
      · have hG_pos : 0 < G :=
          lt_of_le_of_ne hG_nonneg (Ne.symm hG_zero)
        have hG_sq_pos : 0 < G ^ 2 := by
          positivity
        have hG_sq_nonneg : 0 ≤ G ^ 2 := le_of_lt hG_sq_pos
        rcases hA_source_log_or_G_zero with hlog_source | hG_contra
        · let gSq : ℕ → ℝ := fun t =>
            ‖S.stochasticGradient (iterate S t ω) (S.sample t ω)‖ ^ 2
          let ratioGenerated : Fin T → ℝ := fun i =>
            gSq (i.val + 1) / (S.w + cumulativeGradientNormSq S i.val ω)
          let ratioSource : Fin T → ℝ := fun i =>
            gSq (i.val + 1) /
              (G ^ 2 + (Finset.Icc 1 (i.val + 1)).sum gSq)
          let ratioIcc : ℕ → ℝ := fun t =>
            gSq t / (G ^ 2 + (Finset.Icc 1 t).sum gSq)
          have hA_step_eq :
              ∀ i : Fin T, scale * AStep i = coeff * ratioGenerated i := by
            intro i
            have hcube :=
              theorem1_stepsize_cube_eq S hgenerated i.val ω
            dsimp [AStep, ratioGenerated, gSq, coeff, scale]
            rw [hcube]
            ring
          have hA_sum_eq :
              scale * Finset.sum Finset.univ AStep =
                coeff * Finset.sum Finset.univ ratioGenerated := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _hi => hA_step_eq i)
          have hratio_step :
              ∀ i : Fin T, ratioGenerated i ≤ ratioSource i := by
            intro i
            have hsrc_pos :
                0 < G ^ 2 + (Finset.Icc 1 (i.val + 1)).sum gSq := by
              have hsum_nonneg :
                  0 ≤ (Finset.Icc 1 (i.val + 1)).sum gSq := by
                exact Finset.sum_nonneg (fun j _hj => by positivity)
              exact add_pos_of_pos_of_nonneg hG_sq_pos hsum_nonneg
            have hnum_nonneg : 0 ≤ gSq (i.val + 1) := by
              dsimp [gSq]
              positivity
            exact
              div_le_div_of_nonneg_left hnum_nonneg hsrc_pos
                (by simpa [ratioGenerated, ratioSource, gSq] using hA_shifted_den i)
          have hratio_sum :
              Finset.sum Finset.univ ratioGenerated ≤
                Finset.sum Finset.univ ratioSource := by
            exact Finset.sum_le_sum (fun i _hi => hratio_step i)
          have hsource_fin_eq :
              Finset.sum Finset.univ ratioSource =
                (Finset.Icc 1 T).sum ratioIcc := by
            simpa [ratioSource, ratioIcc] using
              (fin_sum_successor_eq_sum_Icc_one T ratioIcc)
          have hsource_le_logT :
              (Finset.Icc 1 T).sum ratioIcc ≤ Real.log (T + 2 : ℝ) := by
            exact
              sum_div_add_prefix_sum_le_log_nat_add_two_of_le
                gSq (G ^ 2) T hG_sq_pos
                (by
                  intro t _ht
                  dsimp [gSq]
                  positivity)
                (by
                  intro t ht
                  have ht_pos : 1 ≤ t := (Finset.mem_Icc.mp ht).1
                  have ht_le : t ≤ T := (Finset.mem_Icc.mp ht).2
                  let i : Fin T := ⟨t - 1, by omega⟩
                  have ht_eq : t = i.val + 1 := by
                    dsimp [i]
                    omega
                  have hnorm_le :
                      ‖S.stochasticGradient (iterate S t ω) (S.sample t ω)‖ ≤ G := by
                    simpa [ht_eq] using hG_at_ω i
                  exact pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2)
          calc
            scale * Finset.sum Finset.univ AStep =
                coeff * Finset.sum Finset.univ ratioGenerated := hA_sum_eq
            _ ≤ coeff * Finset.sum Finset.univ ratioSource :=
                mul_le_mul_of_nonneg_left hratio_sum hcoeff_nonneg
            _ = coeff * (Finset.Icc 1 T).sum ratioIcc := by
                rw [hsource_fin_eq]
            _ ≤ coeff * Real.log (T + 2 : ℝ) :=
                mul_le_mul_of_nonneg_left hsource_le_logT hcoeff_nonneg
            _ = logBudget := by
                rfl
        · exact (hG_zero hG_contra).elim
    have hB_budget :
        scale * Finset.sum Finset.univ BStep -
            scale * Finset.sum Finset.univ PrevStep ≤
          Finset.sum Finset.univ ErrStep := by
      have hrecip :
          ∀ i : Fin T,
            (1 / stepsize S i.val ω -
                1 / theorem1PreviousErrorDenominator S i.val ω) ≤
              (G ^ 2 / (7 * L * S.k ^ 3)) * stepsize S i.val ω := by
        intro i
        exact
          theorem1_reciprocal_stepsize_increment_bound
            S hgenerated hEq4Scalar i.val ω (hG_current_at_ω i)
      simpa [scale, BStep, PrevStep, ErrStep] using
        theorem1_equation4_B_budget_of_reciprocal_bound
          S hgenerated hEq4Scalar hc_eq ω hrecip
    calc
      scale * Finset.sum Finset.univ (fun i : Fin T => AStep i + BStep i) -
          scale * Finset.sum Finset.univ PrevStep
          =
        scale * Finset.sum Finset.univ AStep +
          (scale * Finset.sum Finset.univ BStep -
            scale * Finset.sum Finset.univ PrevStep) := by
            rw [Finset.sum_add_distrib]
            ring
      _ ≤ logBudget + Finset.sum Finset.univ ErrStep := by
            exact add_le_add hA_budget hB_budget
  have hC_budget :
      Finset.sum Finset.univ (fun i : Fin T => scale * CStep i) ≤
        Finset.sum Finset.univ GradStep := by
    simpa [scale, CStep, GradStep] using hC_sum
  have hbudget :=
    theorem1_equation4_pointwise_budget_of_AB_and_C_bounds
      (scale := scale) (logBudget := logBudget)
      (A := AStep) (B := BStep) (C := CStep)
      (Prev := PrevStep) (Grad := GradStep) (Err := ErrStep)
      hAB_budget hC_budget
  simpa [scale, logBudget, AStep, BStep, CStep, PrevStep, GradStep, ErrStep,
    sub_eq_add_neg] using hbudget

/-- Integrability of equation (4)'s gradient/error RHS summand.

This is a local well-definedness bridge for the source-chain equation (4)
route.  It uses only generated Algorithm 1 boundedness and the Section 3
`G`-Lipschitz-derived objective-gradient bound. -/
private theorem theorem1_equation4_gradient_error_step_integrable_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    ∀ i : Fin T, i ∈ Finset.univ →
      Integrable
        (fun ω =>
          stepsize S i.val ω / 8 *
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
            3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) μ := by
  classical
  intro i _hi
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  have hmono_prefix :
      (⨆ j < i.val + 1, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) ≤
        (⨆ j < i.val + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample)) := by
    exact iSup₂_le fun j hj =>
      le_iSup_of_le j (le_iSup_of_le (Nat.lt_of_lt_of_le hj (by omega)) le_rfl)
  have hη_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < i.val + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (stepsize S i.val) μ :=
    (lemma2_stepsize_prefixAEMeasurable S μ hsec3 i.val).mono hmono_prefix
  have hx_prefix :
      @prefixAEMeasurable Ω (DecisionSpace d) _ _
        (⨆ j < i.val + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (iterate S i.val) μ :=
    (lemma3_iterate_prefixAEMeasurable S μ hsec3 i.val).mono hmono_prefix
  have hobj_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < i.val + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) μ :=
    (hx_prefix.comp_measurable
      (section3_objectiveGradient_continuous S μ hsec3 0).measurable).norm_sq
  have herror_prefix :
      @prefixAEMeasurable Ω ℝ _ _
        (⨆ j < i.val + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω => ‖error S i.val ω‖ ^ 2) μ :=
    (lemma3_error_prefixAEMeasurable S μ hsec3 i.val).norm_sq.mono hmono_prefix
  have htuple :
      @prefixAEMeasurable Ω ((ℝ × ℝ) × ℝ) _ _
        (⨆ j < i.val + 2, MeasurableSpace.comap (S.sample j)
          (by infer_instance : MeasurableSpace Sample))
        (fun ω =>
          ((stepsize S i.val ω,
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2),
            ‖error S i.val ω‖ ^ 2)) μ :=
    (hη_prefix.prod hobj_prefix).prod herror_prefix
  let gradientErrorOfTuple : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    p.1.1 / 8 * p.1.2 - 3 * p.1.1 / 4 * p.2
  have hgradientErrorOfTuple_meas : Measurable gradientErrorOfTuple := by
    dsimp [gradientErrorOfTuple]
    measurability
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω =>
          stepsize S i.val ω / 8 *
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
            3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) μ := by
    have hZ_prefix :
        @prefixAEMeasurable Ω ℝ _ _
          (⨆ j < i.val + 2, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          (fun ω =>
            stepsize S i.val ω / 8 *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
              3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) μ := by
      refine (htuple.comp_measurable hgradientErrorOfTuple_meas).congr ?_
      filter_upwards with ω
      rfl
    exact (prefixAEMeasurable.aemeasurable S μ hsec3 hZ_prefix).aestronglyMeasurable
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 i.val hgenerated with
    ⟨Aη, hAη_nonneg, hAη⟩
  have hloc3 : lemma3LocalQuotientBoundary S i.val := by
    exact lemma3LocalQuotientBoundary_of_generated_boundary S hgenerated i.val
  rcases lemma3_generated_error_eventually_bound S μ hsec3 i.val hloc3 with
    ⟨Bε, hBε_nonneg, hBε⟩
  refine Integrable.of_bound hZ_aesm
    (C := Aη * G ^ 2 / 8 + 3 * Aη * Bε ^ 2 / 4) ?_
  filter_upwards [hAη, hBε] with ω hηω hεω
  have hobjω :
      ‖objectiveGradient S (iterate S i.val ω)‖ ≤ G :=
    section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S i.val ω)
  have hobj_sq :
      ‖‖objectiveGradient S (iterate S i.val ω)‖ ^ 2‖ ≤ G ^ 2 := by
    have hsq :
        ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 ≤ G ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hobjω 2
    simpa [Real.norm_of_nonneg (sq_nonneg _)] using hsq
  have hε_sq : ‖‖error S i.val ω‖ ^ 2‖ ≤ Bε ^ 2 := by
    have hsq : ‖error S i.val ω‖ ^ 2 ≤ Bε ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hεω 2
    simpa [Real.norm_of_nonneg (sq_nonneg _)] using hsq
  have hη_div : ‖stepsize S i.val ω / 8‖ ≤ Aη / 8 := by
    calc
      ‖stepsize S i.val ω / 8‖ = ‖stepsize S i.val ω‖ / 8 := by
        simp [norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
      _ ≤ Aη / 8 := div_le_div_of_nonneg_right hηω (by norm_num)
  have hη_three_div : ‖3 * stepsize S i.val ω / 4‖ ≤ 3 * Aη / 4 := by
    calc
      ‖3 * stepsize S i.val ω / 4‖ = 3 * ‖stepsize S i.val ω‖ / 4 := by
        simp [norm_div, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), mul_comm, mul_left_comm,
          mul_assoc]
      _ ≤ 3 * Aη / 4 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hηω (by norm_num))
          (by norm_num)
  have hfirst :
      ‖stepsize S i.val ω / 8 *
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2‖ ≤
        Aη * G ^ 2 / 8 := by
    calc
      ‖stepsize S i.val ω / 8 *
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2‖ =
          ‖stepsize S i.val ω / 8‖ *
            ‖‖objectiveGradient S (iterate S i.val ω)‖ ^ 2‖ := by
            rw [norm_mul]
      _ ≤ (Aη / 8) * G ^ 2 :=
          mul_le_mul hη_div hobj_sq (norm_nonneg _) (div_nonneg hAη_nonneg (by norm_num))
      _ = Aη * G ^ 2 / 8 := by ring
  have hsecond :
      ‖3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2‖ ≤
        3 * Aη * Bε ^ 2 / 4 := by
    calc
      ‖3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2‖ =
          ‖3 * stepsize S i.val ω / 4‖ * ‖‖error S i.val ω‖ ^ 2‖ := by
            rw [norm_mul]
      _ ≤ (3 * Aη / 4) * Bε ^ 2 :=
          mul_le_mul hη_three_div hε_sq (norm_nonneg _)
            (div_nonneg (mul_nonneg (by norm_num) hAη_nonneg) (by norm_num))
      _ = 3 * Aη * Bε ^ 2 / 4 := by ring
  calc
    ‖stepsize S i.val ω / 8 *
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
        3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2‖
        ≤
          ‖stepsize S i.val ω / 8 *
            ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2‖ +
          ‖3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2‖ :=
          norm_sub_le _ _
    _ ≤ Aη * G ^ 2 / 8 + 3 * Aη * Bε ^ 2 / 4 :=
          add_le_add hfirst hsecond

/-- Integral lift for equation (4) once the pointwise scalar budget is known.

This is the source/coarser semantic-dependency bridge requested by the audit:
all finite-window integral rewriting and integrability API work is proved here,
and the only non-local mathematical premise is the exact pointwise scalar
budget from Theorem 1 proof lines 354-397. -/
private theorem theorem1_equation4_scalar_integral_budget_of_pointwise_budget
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    (∀ᵐ ω ∂μ,
      (1 / (32 * L ^ 2)) *
            Finset.sum Finset.univ
              (fun i : Fin T =>
                2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
                    ‖stochasticGradient S (iterate S (i.val + 1) ω)
                      (S.sample (i.val + 1) ω)‖ ^ 2 +
                  (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                      (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                        ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
                  4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
                    stepsize S i.val ω *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) -
          (1 / (32 * L ^ 2)) *
            Finset.sum Finset.univ
              (fun i : Fin T =>
                ‖error S i.val ω‖ ^ 2 /
                  theorem1PreviousErrorDenominator S i.val ω) ≤
        S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) +
          Finset.sum Finset.univ
            (fun i : Fin T =>
              stepsize S i.val ω / 8 *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)) →
    (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
        (1 / (32 * L ^ 2)) *
          theorem1Equation4PreviousErrorWindowIntegral S μ T ≤
      theorem1Equation4RHS S μ T L := by
  classical
  let scale : ℝ := 1 / (32 * L ^ 2)
  let rhsStep : Fin T → Ω → ℝ := fun i ω =>
    2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
        ‖stochasticGradient S (iterate S (i.val + 1) ω)
          (S.sample (i.val + 1) ω)‖ ^ 2 +
      (((1 - nextMomentumWeight S i.val ω) ^ 2 *
          (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
            ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
      4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
        stepsize S i.val ω *
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2
  let prevStep : Fin T → Ω → ℝ := fun i ω =>
    ‖error S i.val ω‖ ^ 2 / theorem1PreviousErrorDenominator S i.val ω
  let gradientErrorStep : Fin T → Ω → ℝ := fun i ω =>
    stepsize S i.val ω / 8 *
        ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
      3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2
  let logBudget : ℝ :=
    S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ)
  intro hpoint_raw
  have hpoint :
      ∀ᵐ ω ∂μ,
        scale * Finset.sum Finset.univ (fun i : Fin T => rhsStep i ω) -
            scale * Finset.sum Finset.univ (fun i : Fin T => prevStep i ω) ≤
          logBudget +
            Finset.sum Finset.univ (fun i : Fin T => gradientErrorStep i ω) := by
    simpa [scale, rhsStep, prevStep, gradientErrorStep, logBudget] using hpoint_raw
  have hrhsStep_int :
      ∀ i ∈ Finset.univ, Integrable (rhsStep i) μ := by
    simpa [rhsStep] using
      theorem1_equation4_rhsStep_integrable_of_generated_boundary
        S μ T hsec3 hgenerated
  have hprevStep_int :
      ∀ i ∈ Finset.univ, Integrable (prevStep i) μ := by
    intro i _hi
    by_cases hi : i.val = 0
    · have hloc3 : lemma3LocalQuotientBoundary S 0 := by
        simpa [lemma3LocalQuotientBoundary] using hgenerated
      rcases lemma3_generated_error_eventually_bound S μ hsec3 0 hloc3 with
        ⟨B, _hB_nonneg, hB⟩
      have herror_prefix :
          @prefixAEMeasurable Ω (DecisionSpace d) _ _
            (⨆ j < 0 + 1, MeasurableSpace.comap (S.sample j)
              (by infer_instance : MeasurableSpace Sample))
            (error S 0) μ :=
        lemma3_error_prefixAEMeasurable S μ hsec3 0
      have herror_aesm : AEStronglyMeasurable (error S 0) μ :=
        (prefixAEMeasurable.aemeasurable S μ hsec3 herror_prefix).aestronglyMeasurable
      have hsq_int : Integrable (fun ω => ‖error S 0 ω‖ ^ 2) μ :=
        (SOptLib.integrable_sq_norm_of_ae_bound herror_aesm hB).1
      have hconst :
          Integrable
            (fun ω => (1 / initialStepsize S) * ‖error S 0 ω‖ ^ 2) μ :=
        hsq_int.const_mul (1 / initialStepsize S)
      simpa [prevStep, theorem1PreviousErrorDenominator, hi, div_eq_mul_inv,
        one_div, mul_comm, mul_left_comm, mul_assoc] using hconst
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero hi
      have herr :=
        lemma2_generated_next_error_eventually_bound
          S μ hsec3 (i.val - 1) hgenerated
      have hrecip :=
        lemma2_generated_reciprocal_stepsize_eventually_bound
          S μ hsec3 (i.val - 1) hgenerated
      have hbase :
          Integrable
            (fun ω =>
              ‖error S ((i.val - 1) + 1) ω‖ ^ 2 /
                stepsize S (i.val - 1) ω) μ :=
        lemma2_lhs_integrable_of_error_and_reciprocal_bounds
          S μ hsec3 (i.val - 1) herr hrecip
      have hsucc : (i.val - 1) + 1 = i.val :=
        Nat.succ_pred_eq_of_pos hpos
      rw [hsucc] at hbase
      simpa [prevStep, theorem1PreviousErrorDenominator, hi, hsucc] using hbase
  have hdiffStep_int :
      ∀ i ∈ Finset.univ, Integrable (fun ω => scale * rhsStep i ω - scale * prevStep i ω) μ := by
    intro i hi
    exact ((hrhsStep_int i hi).const_mul scale).sub ((hprevStep_int i hi).const_mul scale)
  have hgradientErrorStep_int :
      ∀ i ∈ Finset.univ, Integrable (gradientErrorStep i) μ := by
    simpa [gradientErrorStep] using
      theorem1_equation4_gradient_error_step_integrable_of_generated_boundary
        S μ T hsec3 hgenerated
  have hlift :
      Finset.sum Finset.univ
          (fun i : Fin T => ∫ ω, scale * rhsStep i ω - scale * prevStep i ω ∂μ) ≤
        logBudget +
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, gradientErrorStep i ω ∂μ) := by
    have hpoint' :
        ∀ᵐ ω ∂μ,
          Finset.sum Finset.univ
              (fun i : Fin T => scale * rhsStep i ω - scale * prevStep i ω) ≤
            logBudget +
              Finset.sum Finset.univ (fun i : Fin T => gradientErrorStep i ω) := by
      filter_upwards [hpoint] with ω hω
      simpa [Finset.mul_sum, Finset.sum_sub_distrib, mul_comm, mul_left_comm, mul_assoc]
        using hω
    simpa [one_smul] using
      integral_finset_sum_le_of_pointwise_finset_sum_le
        (mu := μ) (s := Finset.univ)
        (A := fun i ω => scale * rhsStep i ω - scale * prevStep i ω)
        (C := gradientErrorStep) (c := (1 : ℝ)) (gap := logBudget)
        hdiffStep_int hgradientErrorStep_int (by simpa [one_smul] using hpoint')
  have hleft_eval :
      (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
        (1 / (32 * L ^ 2)) *
          theorem1Equation4PreviousErrorWindowIntegral S μ T =
        Finset.sum Finset.univ
          (fun i : Fin T => ∫ ω, scale * rhsStep i ω - scale * prevStep i ω ∂μ) := by
    calc
      (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
        (1 / (32 * L ^ 2)) *
          theorem1Equation4PreviousErrorWindowIntegral S μ T =
          scale *
              Finset.sum Finset.univ (fun i : Fin T => ∫ ω, rhsStep i ω ∂μ) -
            scale *
              Finset.sum Finset.univ (fun i : Fin T => ∫ ω, prevStep i ω ∂μ) := by
            simp [scale, rhsStep, prevStep, theorem1Equation4Lemma2RHSWindowIntegral,
              theorem1Equation4PreviousErrorWindowIntegral]
      _ = Finset.sum Finset.univ
          (fun i : Fin T => ∫ ω, scale * rhsStep i ω - scale * prevStep i ω ∂μ) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [MeasureTheory.integral_sub
              ((hrhsStep_int i hi).const_mul scale)
              ((hprevStep_int i hi).const_mul scale)]
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hright_eval :
      logBudget +
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, gradientErrorStep i ω ∂μ) =
        theorem1Equation4RHS S μ T L := by
    have hGE :
        theorem1Equation4GradientErrorWindowIntegral S μ T =
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, gradientErrorStep i ω ∂μ) := by
      unfold theorem1Equation4GradientErrorWindowIntegral
      rw [MeasureTheory.integral_finset_sum Finset.univ hgradientErrorStep_int]
    rw [theorem1Equation4RHS_eq_logBudget_add_gradientErrorWindowIntegral]
    simp [hGE, logBudget]
  rw [hleft_eval]
  rw [← hright_eval]
  exact hlift

/-- Exact-head Lean attempt for
`theorem1_equation4_scalar_integral_budget_of_generated_boundary`.

This source/coarser artifact now has an explicit dependency boundary: the
finite-window integral/API part is fully proved by
`theorem1_equation4_scalar_integral_budget_of_pointwise_budget`, and the only
remaining equation (4) proof burden is the pointwise scalar budget below. -/
private theorem _voucher_attempt_theorem1_equation4_scalar_integral_budget_of_generated_boundary_12
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀)) :
    (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
        (1 / (32 * L ^ 2)) *
          theorem1Equation4PreviousErrorWindowIntegral S μ T ≤
      theorem1Equation4RHS S μ T L := by
  classical
  exact
    theorem1_equation4_scalar_integral_budget_of_pointwise_budget
      S μ T hsec3 hgenerated
      (_voucher_step_theorem1_equation4_pointwise_scalar_budget_12
        S μ T hsec3 hgenerated hEq4Scalar hlemma4_route)

/-- Equation (4) scalar/log budget leaf.

This is the paper's lines 335-397 after Lemma 2 has already been lifted to
totalized integrals: the `A_t` sampled-gradient contribution is bounded by
Lemma 4 and the `G`-Lipschitz loss bound, while the `B_t` coefficient is
nonpositive after using `a_{t+1} ≤ 1`, `η_t ≤ 1/(4L)`,
`w ≥ 2G²`, `w ≥ (4Lk)³`, and
`c = 28L² + G²/(7Lk³)`. -/
private theorem theorem1_equation4_scalar_integral_budget_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀)) :
    (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
        (1 / (32 * L ^ 2)) *
          theorem1Equation4PreviousErrorWindowIntegral S μ T ≤
      theorem1Equation4RHS S μ T L := by
  exact
    _voucher_attempt_theorem1_equation4_scalar_integral_budget_of_generated_boundary_12
      S μ T hsec3 hgenerated hEq4Scalar hlemma4_route

/-- Exact scalar/integral normalization leaf for Theorem 1 equation (4).

At this interface the generated Lemma 2 recurrence has already been aggregated
over the finite window and scaled by `1/(32L²)`, and Lemma 4 has already been
specialized to the generated sampled-gradient denominator.  What remains is
precisely the paper's source proof lines 354-397: normalize the adaptive
denominators, use `a_{t+1} ≤ 1`, `η_t ≤ 1/(4L)`, `w ≥ 2G²`, and
`c = 28L² + G²/(7Lk³)`, then collect the `A_t`, `B_t`, and `C_t`
coefficients into the displayed equation (4). -/
private theorem theorem1_equation4_scalar_normalization_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma2_window_scaled :
      (1 / (32 * L ^ 2)) *
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ∫ ω, ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω ∂μ) ≤
        (1 / (32 * L ^ 2)) *
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ∫ ω,
                2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
                    ‖stochasticGradient S (iterate S (i.val + 1) ω)
                      (S.sample (i.val + 1) ω)‖ ^ 2 +
                  (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                      (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                        ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
                  4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
                    stepsize S i.val ω *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ))
    (hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀)) :
    theorem1Equation4ErrorIncrementLHS S μ T L ≤ theorem1Equation4RHS S μ T L := by
  classical
  have hc_eq :
      S.c = 28 * L ^ 2 + G ^ 2 / (7 * L * S.k ^ 3) :=
    theorem1_equation4_c_eq_of_scalar_boundary S L G hEq4Scalar
  have hη_le : ∀ t ω, stepsize S t ω ≤ (1 : ℝ) / (4 * L) :=
    hEq4Scalar.stepsize_le_one_over_fourL
  have ha_le : ∀ t ω, nextMomentumWeight S t ω ≤ 1 :=
    hEq4Scalar.nextMomentumWeight_le_one
  have hw_ge_two : 2 * G ^ 2 ≤ S.w :=
    hEq4Scalar.w_ge_two_G_sq
  have hw_ge_four : (4 * L * S.k) ^ 3 ≤ S.w :=
    hEq4Scalar.w_ge_four_L_k_cube
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hk_pos : 0 < S.k := hEq4Scalar.k_pos
  have hgeneratedScalar : generatedStepsizeScalarBoundary S := hgenerated.1
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hk_ne : S.k ≠ 0 := ne_of_gt hk_pos
  have hscale_pos : 0 < (1 : ℝ) / (32 * L ^ 2) := by
    positivity
  have hscale_nonneg : 0 ≤ (1 : ℝ) / (32 * L ^ 2) := le_of_lt hscale_pos
  have hprevDen_pos :
      ∀ t ω, 0 < theorem1PreviousErrorDenominator S t ω := by
    intro t ω
    unfold theorem1PreviousErrorDenominator
    by_cases ht : t = 0
    · have hw_pos : 0 < S.w := hgeneratedScalar.1.1
      have hden_pos : 0 < Real.rpow S.w ((1 : ℝ) / 3) :=
        Real.rpow_pos_of_pos hw_pos ((1 : ℝ) / 3)
      simpa [ht, initialStepsize_eq, one_div] using div_pos hk_pos hden_pos
    · have hpred_pos :
          0 < stepsize S (t - 1) ω :=
        stepsize_pos_of_generated_quotient_boundary S hgenerated (t - 1) ω
      simp [ht, hpred_pos]
  have hprevDen_ne :
      ∀ t ω, theorem1PreviousErrorDenominator S t ω ≠ 0 := by
    intro t ω
    exact ne_of_gt (hprevDen_pos t ω)
  have hc_coeff_bound :
      4 * L ^ 2 - S.c ≤
        -24 * L ^ 2 - G ^ 2 / (7 * L * S.k ^ 3) := by
    rw [hc_eq]
    ring_nf
    exact le_rfl
  have hden_ck_ne : 7 * L * S.k ^ 3 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hL_ne) (pow_ne_zero 3 hk_ne)
  have hc_coeff_identity :
      4 * L ^ 2 - S.c =
        -24 * L ^ 2 - G ^ 2 / (7 * L * S.k ^ 3) := by
    rw [hc_eq]
    ring_nf
  have hstepsize_pos : ∀ t ω, 0 < stepsize S t ω := by
    intro t ω
    exact stepsize_pos_of_generated_quotient_boundary S hgenerated t ω
  have hstepsize_ne : ∀ t ω, stepsize S t ω ≠ 0 := by
    intro t ω
    exact ne_of_gt (hstepsize_pos t ω)
  have hlemma2_window_scaled' :
      (1 / (32 * L ^ 2)) *
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ∫ ω, ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω ∂μ) ≤
        (1 / (32 * L ^ 2)) *
          theorem1Equation4Lemma2RHSWindowIntegral S μ T L := by
    simpa [theorem1Equation4Lemma2RHSWindowIntegral] using hlemma2_window_scaled
  have hlift :
      theorem1Equation4ErrorIncrementLHS S μ T L ≤
        (1 / (32 * L ^ 2)) *
            theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
          (1 / (32 * L ^ 2)) *
            theorem1Equation4PreviousErrorWindowIntegral S μ T :=
    theorem1_equation4_lift_lhs_from_scaled_lemma2_window
      S μ T _hsec3 hgenerated hlemma2_window_scaled'
  have hbudget :
      (1 / (32 * L ^ 2)) *
            theorem1Equation4Lemma2RHSWindowIntegral S μ T L -
          (1 / (32 * L ^ 2)) *
            theorem1Equation4PreviousErrorWindowIntegral S μ T ≤
        theorem1Equation4RHS S μ T L :=
    theorem1_equation4_scalar_integral_budget_of_generated_boundary
      S μ T _hsec3 hgenerated hEq4Scalar hlemma4_route
  exact le_trans hlift hbudget

/-- Exact-head Lean attempt artifact for the first remaining equation (4)
aggregation leaf.

The proof now performs the finite-window integral rewrites, scales the already
proved Lemma 2 integral-window inequality, and applies Lemma 4 to the actual
generated sampled-gradient denominator.  The unresolved part of the old attempt
was scalar normalization/cancellation for equation (4), not the whole source route. -/
private theorem theorem1_equation4_error_increment_bound_from_integral_window
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma2_integral_window :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω, ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω ∂μ) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
                  ‖stochasticGradient S (iterate S (i.val + 1) ω)
                    (S.sample (i.val + 1) ω)‖ ^ 2 +
                (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                    (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                      ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
                4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
                  stepsize S i.val ω *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ))
    (hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀)) :
    theorem1Equation4ErrorIncrementLHS S μ T L ≤ theorem1Equation4RHS S μ T L := by
  classical
  let lhsStep : Fin T → Ω → ℝ := fun i ω =>
    ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω
  let rhsStep : Fin T → Ω → ℝ := fun i ω =>
    2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
        ‖stochasticGradient S (iterate S (i.val + 1) ω)
          (S.sample (i.val + 1) ω)‖ ^ 2 +
      (((1 - nextMomentumWeight S i.val ω) ^ 2 *
          (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
            ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
      4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
        stepsize S i.val ω *
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2
  have hlhsStep_int : ∀ i ∈ Finset.univ, Integrable (lhsStep i) μ := by
    simpa [lhsStep] using
      theorem1_equation4_lhsStep_integrable_of_generated_boundary
        S μ T _hsec3 hgenerated
  have hrhsStep_int : ∀ i ∈ Finset.univ, Integrable (rhsStep i) μ := by
    simpa [rhsStep] using
      theorem1_equation4_rhsStep_integrable_of_generated_boundary
        S μ T _hsec3 hgenerated
  have hlhs_integral_sum :
      (∫ ω, Finset.sum Finset.univ (fun i : Fin T => lhsStep i ω) ∂μ) =
        Finset.sum Finset.univ (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) := by
    rw [MeasureTheory.integral_finset_sum Finset.univ hlhsStep_int]
  have hrhs_integral_sum :
      (∫ ω, Finset.sum Finset.univ (fun i : Fin T => rhsStep i ω) ∂μ) =
        Finset.sum Finset.univ (fun i : Fin T => ∫ ω, rhsStep i ω ∂μ) := by
    rw [MeasureTheory.integral_finset_sum Finset.univ hrhsStep_int]
  have hlemma2_window' :
      Finset.sum Finset.univ (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) ≤
        Finset.sum Finset.univ (fun i : Fin T => ∫ ω, rhsStep i ω ∂μ) := by
    simpa [lhsStep, rhsStep] using hlemma2_integral_window
  have hscale_nonneg : 0 ≤ (1 : ℝ) / (32 * L ^ 2) := by
    positivity
  have hlemma2_window_scaled :
      (1 / (32 * L ^ 2)) *
          Finset.sum Finset.univ (fun i : Fin T => ∫ ω, lhsStep i ω ∂μ) ≤
        (1 / (32 * L ^ 2)) *
          Finset.sum Finset.univ (fun i : Fin T => ∫ ω, rhsStep i ω ∂μ) :=
    mul_le_mul_of_nonneg_left hlemma2_window' hscale_nonneg
  have hη_le : ∀ t ω, stepsize S t ω ≤ (1 : ℝ) / (4 * L) :=
    hEq4Scalar.stepsize_le_one_over_fourL
  have ha_le : ∀ t ω, nextMomentumWeight S t ω ≤ 1 :=
    hEq4Scalar.nextMomentumWeight_le_one
  have hw_ge_two : 2 * G ^ 2 ≤ S.w :=
    hEq4Scalar.w_ge_two_G_sq
  have hw_ge_four : (4 * L * S.k) ^ 3 ≤ S.w :=
    hEq4Scalar.w_ge_four_L_k_cube
  have hc_source :
      sourceQuotientSpec (G ^ 2) (7 * L * S.k ^ 3) (S.c - 28 * L ^ 2) :=
    hEq4Scalar.c_source_quotient
  exact
    theorem1_equation4_scalar_normalization_of_generated_boundary
      S μ T _hsec3 hgenerated hEq4Scalar hlemma2_window_scaled hlemma4_route

/-- Equation (4) from the Theorem 1 proof, stated at the source/coarser
interface.  Its inputs are exactly the generated-boundary Lemma 2 route and
the logarithmic Lemma 4 route, rather than the retired local-only Lemma 2
compatibility branch. -/
private theorem theorem1_equation4_error_increment_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (T : ℕ)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma2_route :
      ∀ t, sourceExpectationLE μ (lemma2LHSExpr S t) (lemma2RHSExpr S L t))
    (hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀)) :
    theorem1Equation4ErrorIncrementLHS S μ T L ≤ theorem1Equation4RHS S μ T L := by
  classical
  have hlemma2_integral_window :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω, ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω ∂μ) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              2 * S.c ^ 2 * stepsize S i.val ω ^ 3 *
                  ‖stochasticGradient S (iterate S (i.val + 1) ω)
                    (S.sample (i.val + 1) ω)‖ ^ 2 +
                (((1 - nextMomentumWeight S i.val ω) ^ 2 *
                    (1 + 4 * L ^ 2 * stepsize S i.val ω ^ 2) *
                      ‖error S i.val ω‖ ^ 2) / stepsize S i.val ω) +
                4 * (1 - nextMomentumWeight S i.val ω) ^ 2 * L ^ 2 *
                  stepsize S i.val ω *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ) :=
    theorem1_lemma2_route_finset_integral_bound_of_generated_boundary
      S μ L T hgenerated hlemma2_route
  exact
    theorem1_equation4_error_increment_bound_from_integral_window
      S μ T _hsec3 hgenerated hEq4Scalar hlemma2_integral_window hlemma4_route

/-- The Theorem 1 scalar boundary supplies the Lemma 1 stepsize side condition
uniformly over the finite proof window.

This is a source-route bridge, not a new assumption: it specializes the
equation (4) scalar consequences already derived from the displayed Theorem 1
parameter choice and immediately feeds the public Lemma 1 route. -/
private theorem theorem1_lemma1_window_source_route
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (T : ℕ) {L G : ℝ}
    (hgenerated : generatedStepsizeScalarBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma1_route :
      ∀ t,
        (∀ s, sourceStepsizeLE S s ((1 : ℝ) / (4 * L))) →
          sourceExpectationLE μ (lemma1LHSExpr S t) (lemma1RHSExpr S t)) :
    ∀ i : Fin T, sourceExpectationLE μ (lemma1LHSExpr S i.val) (lemma1RHSExpr S i.val) := by
  intro i
  have heta : ∀ s, sourceStepsizeLE S s ((1 : ℝ) / (4 * L)) := by
    intro s
    intro ω η hη
    have hη_src := sourceStepsize_eq_some_stepsize_of_generated_boundary S hgenerated s ω
    rw [hη_src] at hη
    cases hη
    exact hEq4Scalar.stepsize_le_one_over_fourL s ω
  exact hlemma1_route i.val heta

/-- A generated Lemma 1 source comparison exposes the totalized one-step
integral descent used in the Theorem 1 Lyapunov window.

This is the Lemma 1 analogue of the generated Lemma 2 integral bridge above:
`sourceExpectationLE` supplies source `Option` expectation witnesses, while the
Theorem 1 telescope is stated with the totalized generated Algorithm 1
quantities.  The generated source boundary supplies the exact pointwise
source-expression equalities. -/
private theorem theorem1_lemma1_route_generated_integral_bound_of_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (t : ℕ)
    (hgenerated : generatedStepsizeScalarBoundary S)
    (hlemma1 :
      sourceExpectationLE μ (lemma1LHSExpr S t) (lemma1RHSExpr S t)) :
    ∫ ω,
        S.objectiveValue (iterate S (t + 1) ω) -
          S.objectiveValue (iterate S t ω) ∂μ ≤
      ∫ ω,
        (-stepsize S t ω / 4) *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2 +
          (3 * stepsize S t ω / 4) * ‖error S t ω‖ ^ 2 ∂μ := by
  classical
  rcases hlemma1 with ⟨lhs, rhs, hlhs, hrhs, hle⟩
  rw [sourceExpectationValue_eq_some_iff] at hlhs
  rw [sourceExpectationValue_eq_some_iff] at hrhs
  rcases hlhs with ⟨_hlhs_def, _hlhs_int, hlhs_val⟩
  rcases hrhs with ⟨_hrhs_def, _hrhs_int, hrhs_val⟩
  let Z : Ω → ℝ := fun ω =>
    S.objectiveValue (iterate S (t + 1) ω) -
      S.objectiveValue (iterate S t ω)
  let W : Ω → ℝ := fun ω =>
    (-stepsize S t ω / 4) *
        ‖objectiveGradient S (iterate S t ω)‖ ^ 2 +
      (3 * stepsize S t ω / 4) * ‖error S t ω‖ ^ 2
  have hlocal : lemma1LocalSourceBoundary S t :=
    lemma1LocalSourceBoundary_of_generated_boundary S hgenerated t
  have hZ_get :
      (fun ω => (lemma1LHSExpr S t ω).getD 0) = Z := by
    funext ω
    rw [lemma1LHSExpr_eq_some_of_local_boundary S hlocal ω]
    rfl
  have hW_get :
      (fun ω => (lemma1RHSExpr S t ω).getD 0) = W := by
    funext ω
    rw [lemma1RHSExpr_eq_some_of_local_boundary S hlocal ω]
    rfl
  have hlhs_total : lhs = ∫ ω, Z ω ∂μ := by
    simpa [hZ_get] using hlhs_val
  have hrhs_total : rhs = ∫ ω, W ω ∂μ := by
    simpa [hW_get] using hrhs_val
  simpa [Z, W, hlhs_total, hrhs_total] using hle

/-- Finite-window aggregation of the generated Lemma 1 descent inequalities in
the integral form consumed by the Theorem 1 Lyapunov telescope. -/
private theorem theorem1_lemma1_finite_sum_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (T : ℕ)
    (hgenerated : generatedStepsizeScalarBoundary S)
    (hlemma1_window :
      ∀ i : Fin T, sourceExpectationLE μ (lemma1LHSExpr S i.val)
        (lemma1RHSExpr S i.val)) :
    Finset.sum Finset.univ
        (fun i : Fin T =>
          ∫ ω,
            S.objectiveValue (iterate S (i.val + 1) ω) -
              S.objectiveValue (iterate S i.val ω) ∂μ) ≤
      Finset.sum Finset.univ
        (fun i : Fin T =>
          ∫ ω,
            (-stepsize S i.val ω / 4) *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
              (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2 ∂μ) := by
  classical
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact
    theorem1_lemma1_route_generated_integral_bound_of_boundary
      S μ i.val hgenerated (hlemma1_window i)

/-- The source Lemma 1 window also carries the totalized integrability
witnesses needed by the later Lyapunov telescope.

This repairs the private Theorem 1 route boundary: `sourceExpectationLE`
contains both source `Option` definedness and Mathlib integrability, while the
numeric finite-sum inequality alone loses that information. -/
private theorem theorem1_lemma1_window_generated_integrable_of_source_route
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) (T : ℕ)
    (hgenerated : generatedStepsizeScalarBoundary S)
    (hlemma1_window :
      ∀ i : Fin T, sourceExpectationLE μ (lemma1LHSExpr S i.val)
        (lemma1RHSExpr S i.val)) :
    (∀ i : Fin T, i ∈ Finset.univ →
      Integrable
        (fun ω =>
          S.objectiveValue (iterate S (i.val + 1) ω) -
            S.objectiveValue (iterate S i.val ω)) μ) ∧
      (∀ i : Fin T, i ∈ Finset.univ →
        Integrable
          (fun ω =>
            (-stepsize S i.val ω / 4) *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
              (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2) μ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro i _hi
    rcases hlemma1_window i with ⟨lhs, _rhs, hlhs, _hrhs, _hle⟩
    have hlhs_pack :=
      (sourceExpectationValue_eq_some_iff μ (lemma1LHSExpr S i.val) lhs).1 hlhs
    have hlocal : lemma1LocalSourceBoundary S i.val :=
      lemma1LocalSourceBoundary_of_generated_boundary S hgenerated i.val
    let Z : Ω → ℝ := fun ω =>
      S.objectiveValue (iterate S (i.val + 1) ω) -
        S.objectiveValue (iterate S i.val ω)
    have hZ_get :
        (fun ω => (lemma1LHSExpr S i.val ω).getD 0) = Z := by
      funext ω
      rw [lemma1LHSExpr_eq_some_of_local_boundary S hlocal ω]
      rfl
    simpa [Z, hZ_get] using hlhs_pack.2.1
  · intro i _hi
    rcases hlemma1_window i with ⟨_lhs, rhs, _hlhs, hrhs, _hle⟩
    have hrhs_pack :=
      (sourceExpectationValue_eq_some_iff μ (lemma1RHSExpr S i.val) rhs).1 hrhs
    have hlocal : lemma1LocalSourceBoundary S i.val :=
      lemma1LocalSourceBoundary_of_generated_boundary S hgenerated i.val
    let W : Ω → ℝ := fun ω =>
      (-stepsize S i.val ω / 4) *
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
        (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2
    have hW_get :
        (fun ω => (lemma1RHSExpr S i.val ω).getD 0) = W := by
      funext ω
      rw [lemma1RHSExpr_eq_some_of_local_boundary S hlocal ω]
      rfl
    simpa [W, hW_get] using hrhs_pack.2.1

/-- The initial STORM error is the centered stochastic gradient at `x₁`, so
Section 3's gradient-noise second-moment bound controls it.

This is Theorem 1 proof step 17's source bridge for the term
`𝔼[‖ε₁‖²]`: it is derived from the paper's gradient-noise assumption and
Algorithm 1 initialization, not introduced as a primitive hypothesis. -/
private theorem theorem1_initial_error_second_moment_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) :
    (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) ≤ σ ^ 2 := by
  classical
  rcases sourceGradientNoiseSecondMomentValue_le S μ hsec3 0 S.x₁ with
    ⟨value, hvalue, hle⟩
  have hvalue' :
      Integrable
          (fun ω =>
            ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
              objectiveGradient S S.x₁‖ ^ 2) μ ∧
        value =
          ∫ ω,
            ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
              objectiveGradient S S.x₁‖ ^ 2 ∂μ :=
    (sourceRealExpectationValue_eq_some_iff μ
      (fun ω =>
        ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
          objectiveGradient S S.x₁‖ ^ 2) value).1 hvalue
  have herr_eq :
      (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) =
        ∫ ω,
          ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
            objectiveGradient S S.x₁‖ ^ 2 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    simp [error, direction_zero, iterate_zero]
  rw [herr_eq]
  simpa [hvalue'.2] using hle

/-- The scaled initial-error contribution appearing after the Lyapunov
telescope is bounded by the displayed Theorem 1 noise term. -/
private theorem theorem1_initial_error_term_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G) :
    (1 / (4 * L ^ 2 * initialStepsize S)) *
        (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) ≤
      Real.rpow S.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * S.k) := by
  classical
  have hinit_second :
      (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) ≤ σ ^ 2 :=
    theorem1_initial_error_second_moment_bound S μ hsec3
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hk_pos : 0 < S.k := hgenerated.2
  have hw_pos : 0 < S.w := hgenerated.1.1.1
  have hden_w_pos :
      0 < Real.rpow S.w ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hw_pos ((1 : ℝ) / 3)
  have hη0_pos : 0 < initialStepsize S := by
    rw [initialStepsize_eq]
    exact div_pos hk_pos hden_w_pos
  have hcoeff_nonneg : 0 ≤ 1 / (4 * L ^ 2 * initialStepsize S) := by
    positivity
  have hscaled :
      (1 / (4 * L ^ 2 * initialStepsize S)) *
          (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) ≤
        (1 / (4 * L ^ 2 * initialStepsize S)) * σ ^ 2 :=
    mul_le_mul_of_nonneg_left hinit_second hcoeff_nonneg
  have hcoeff_eq :
      (1 / (4 * L ^ 2 * initialStepsize S)) * σ ^ 2 =
        Real.rpow S.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * S.k) := by
    rw [initialStepsize_eq]
    field_simp [ne_of_gt hL_pos, ne_of_gt hk_pos, ne_of_gt hden_w_pos]
  exact hscaled.trans_eq hcoeff_eq

/-- Integrability of the initial shifted Lyapunov potential in Theorem 1.

The only random part of `Φ₀` is the initial centered stochastic-gradient error,
whose second moment is supplied by Section 3's gradient-noise assumption. -/
private theorem theorem1_shifted_lyapunov_initial_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G) :
    Integrable (fun ω => theorem1ShiftedLyapunovPotential S L fStar 0 ω) μ := by
  classical
  have herror0_int : Integrable (fun ω => ‖error S 0 ω‖ ^ 2) μ := by
    rcases sourceGradientNoiseSecondMomentValue_le S μ hsec3 0 S.x₁ with
      ⟨value, hvalue, _hle⟩
    have hvalue' :
        Integrable
            (fun ω =>
              ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
                objectiveGradient S S.x₁‖ ^ 2) μ ∧
          value =
            ∫ ω,
              ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
                objectiveGradient S S.x₁‖ ^ 2 ∂μ :=
      (sourceRealExpectationValue_eq_some_iff μ
        (fun ω =>
          ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
            objectiveGradient S S.x₁‖ ^ 2) value).1 hvalue
    exact hvalue'.1.congr (by
      filter_upwards with ω
      simp [error, direction_zero, iterate_zero])
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hη0_pos : 0 < initialStepsize S := by
    have hw_pos : 0 < S.w := hgenerated.1.1.1
    have hden_pos : 0 < Real.rpow S.w ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hw_pos ((1 : ℝ) / 3)
    rw [initialStepsize_eq]
    exact div_pos hgenerated.2 hden_pos
  have hη0_ne : initialStepsize S ≠ 0 := ne_of_gt hη0_pos
  have hbase :
      Integrable
        (fun ω =>
          (S.objectiveValue S.x₁ - fStar) +
            (1 / (32 * L ^ 2 * initialStepsize S)) *
              ‖error S 0 ω‖ ^ 2) μ :=
    (integrable_const (c := S.objectiveValue S.x₁ - fStar)).add
      (herror0_int.const_mul (1 / (32 * L ^ 2 * initialStepsize S)))
  refine hbase.congr ?_
  filter_upwards with ω
  simp [theorem1ShiftedLyapunovPotential, theorem1PreviousErrorDenominator,
    iterate_zero]
  field_simp [hL_ne, hη0_ne]

/-- Integrability of adjacent shifted-Lyapunov drops over a finite Theorem 1
window.

This is the exact well-definedness bridge requested by the Lyapunov route:
the objective-value difference comes from the Lemma 1 source window, while the
error quotient increment comes from the generated equation (4) windows. -/
private theorem theorem1_shifted_lyapunov_drop_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hlemma1_window :
      ∀ i : Fin T, sourceExpectationLE μ (lemma1LHSExpr S i.val)
        (lemma1RHSExpr S i.val)) :
    ∀ i : Fin T, i ∈ Finset.univ →
      Integrable
        (fun ω =>
          theorem1ShiftedLyapunovPotential S L fStar i.val ω -
            theorem1ShiftedLyapunovPotential S L fStar (i.val + 1) ω) μ := by
  classical
  intro i hi
  let scale : ℝ := 1 / (32 * L ^ 2)
  let objStep : Ω → ℝ := fun ω =>
    S.objectiveValue (iterate S (i.val + 1) ω) -
      S.objectiveValue (iterate S i.val ω)
  let lhsStep : Ω → ℝ := fun ω =>
    ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω
  let prevStep : Ω → ℝ := fun ω =>
    ‖error S i.val ω‖ ^ 2 /
      theorem1PreviousErrorDenominator S i.val ω
  have hlemma1_int :=
    theorem1_lemma1_window_generated_integrable_of_source_route
      S μ T hgenerated.1 hlemma1_window
  have hobj_int : Integrable objStep μ := by
    simpa [objStep] using hlemma1_int.1 i hi
  have hlhs_int : Integrable lhsStep μ := by
    simpa [lhsStep] using
      theorem1_equation4_lhsStep_integrable_of_generated_boundary
        S μ T hsec3 hgenerated i hi
  have hprev_int : Integrable prevStep μ := by
    simpa [prevStep] using
      theorem1_equation4_prevStep_integrable_of_generated_boundary
        S μ T hsec3 hgenerated i hi
  have hsum_int :
      Integrable
        (fun ω => objStep ω + scale * (lhsStep ω - prevStep ω)) μ :=
    hobj_int.add ((hlhs_int.sub hprev_int).const_mul scale)
  have hneg_int :
      Integrable
        (fun ω => - (objStep ω + scale * (lhsStep ω - prevStep ω))) μ :=
    hsum_int.neg
  refine hneg_int.congr ?_
  filter_upwards with ω
  have hsucc :=
    theorem1ShiftedLyapunovPotential_succ_sub S L fStar i.val ω
  calc
    - (objStep ω + scale * (lhsStep ω - prevStep ω)) =
        - (theorem1ShiftedLyapunovPotential S L fStar (i.val + 1) ω -
          theorem1ShiftedLyapunovPotential S L fStar i.val ω) := by
      rw [hsucc]
    _ = theorem1ShiftedLyapunovPotential S L fStar i.val ω -
        theorem1ShiftedLyapunovPotential S L fStar (i.val + 1) ω := by ring

/-- Integral form of the shifted-potential drop expansion.

This is the exact algebraic bridge used in the Theorem 1 Lyapunov cancellation:
the finite sum of shifted-potential drops is the negative objective-change
window minus the scaled error-increment window from equation (4). -/
private theorem theorem1_shifted_lyapunov_drop_integral_eq
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hlemma1_window :
      ∀ i : Fin T, sourceExpectationLE μ (lemma1LHSExpr S i.val)
        (lemma1RHSExpr S i.val)) :
    Finset.sum Finset.univ
        (fun i : Fin T =>
          ∫ ω,
            theorem1ShiftedLyapunovPotential S L fStar i.val ω -
              theorem1ShiftedLyapunovPotential S L fStar (i.val + 1) ω ∂μ) =
      - Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              S.objectiveValue (iterate S (i.val + 1) ω) -
                S.objectiveValue (iterate S i.val ω) ∂μ) -
        theorem1Equation4ErrorIncrementLHS S μ T L := by
  classical
  let scale : ℝ := 1 / (32 * L ^ 2)
  let objStep : Fin T → Ω → ℝ := fun i ω =>
    S.objectiveValue (iterate S (i.val + 1) ω) -
      S.objectiveValue (iterate S i.val ω)
  let lhsStep : Fin T → Ω → ℝ := fun i ω =>
    ‖error S (i.val + 1) ω‖ ^ 2 / stepsize S i.val ω
  let prevStep : Fin T → Ω → ℝ := fun i ω =>
    ‖error S i.val ω‖ ^ 2 /
      theorem1PreviousErrorDenominator S i.val ω
  let incStep : Fin T → Ω → ℝ := fun i ω => scale * (lhsStep i ω - prevStep i ω)
  let dropStep : Fin T → Ω → ℝ := fun i ω =>
    theorem1ShiftedLyapunovPotential S L fStar i.val ω -
      theorem1ShiftedLyapunovPotential S L fStar (i.val + 1) ω
  have hlemma1_int :=
    theorem1_lemma1_window_generated_integrable_of_source_route
      S μ T hgenerated.1 hlemma1_window
  have hobj_int : ∀ i ∈ Finset.univ, Integrable (objStep i) μ := by
    intro i hi
    simpa [objStep] using hlemma1_int.1 i hi
  have hlhs_int : ∀ i ∈ Finset.univ, Integrable (lhsStep i) μ := by
    simpa [lhsStep] using
      theorem1_equation4_lhsStep_integrable_of_generated_boundary
        S μ T hsec3 hgenerated
  have hprev_int : ∀ i ∈ Finset.univ, Integrable (prevStep i) μ := by
    simpa [prevStep] using
      theorem1_equation4_prevStep_integrable_of_generated_boundary
        S μ T hsec3 hgenerated
  have hinc_int : ∀ i ∈ Finset.univ, Integrable (incStep i) μ := by
    intro i hi
    exact ((hlhs_int i hi).sub (hprev_int i hi)).const_mul scale
  have hdrop_int : ∀ i ∈ Finset.univ, Integrable (dropStep i) μ := by
    simpa [dropStep] using
      theorem1_shifted_lyapunov_drop_integrable
        S μ T hsec3 hgenerated hlemma1_window
  have hdrop_point : ∀ i ω, dropStep i ω = - objStep i ω - incStep i ω := by
    intro i ω
    have hsucc :=
      theorem1ShiftedLyapunovPotential_succ_sub S L fStar i.val ω
    dsimp [dropStep, objStep, incStep, lhsStep, prevStep, scale]
    linarith
  have hdrop_sum :
      Finset.sum Finset.univ (fun i : Fin T => ∫ ω, dropStep i ω ∂μ) =
        - Finset.sum Finset.univ (fun i : Fin T => ∫ ω, objStep i ω ∂μ) -
          Finset.sum Finset.univ (fun i : Fin T => ∫ ω, incStep i ω ∂μ) := by
    calc
      Finset.sum Finset.univ (fun i : Fin T => ∫ ω, dropStep i ω ∂μ)
          =
        Finset.sum Finset.univ
          (fun i : Fin T => ∫ ω, (- objStep i ω - incStep i ω) ∂μ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact integral_congr_ae (by
            filter_upwards with ω
            exact hdrop_point i ω)
      _ =
        Finset.sum Finset.univ
          (fun i : Fin T => - ∫ ω, objStep i ω ∂μ - ∫ ω, incStep i ω ∂μ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have h :=
            MeasureTheory.integral_add (μ := μ)
              (f := fun ω => -objStep i ω) (g := fun ω => -incStep i ω)
              (hobj_int i hi).neg (hinc_int i hi).neg
          rw [MeasureTheory.integral_neg, MeasureTheory.integral_neg] at h
          simpa [sub_eq_add_neg] using h
      _ =
        - Finset.sum Finset.univ (fun i : Fin T => ∫ ω, objStep i ω ∂μ) -
          Finset.sum Finset.univ (fun i : Fin T => ∫ ω, incStep i ω ∂μ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hinc_sum :
      Finset.sum Finset.univ (fun i : Fin T => ∫ ω, incStep i ω ∂μ) =
        theorem1Equation4ErrorIncrementLHS S μ T L := by
    have hdiff_int :
        ∀ i ∈ Finset.univ,
          Integrable (fun ω => lhsStep i ω - prevStep i ω) μ := by
      intro i hi
      exact (hlhs_int i hi).sub (hprev_int i hi)
    calc
      Finset.sum Finset.univ (fun i : Fin T => ∫ ω, incStep i ω ∂μ)
          =
        Finset.sum Finset.univ
          (fun i : Fin T => ∫ ω, scale * (lhsStep i ω - prevStep i ω) ∂μ) := by
          rfl
      _ =
        Finset.sum Finset.univ
          (fun i : Fin T => scale * ∫ ω, lhsStep i ω - prevStep i ω ∂μ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [MeasureTheory.integral_const_mul]
      _ =
        scale *
          Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, lhsStep i ω - prevStep i ω ∂μ) := by
          rw [Finset.mul_sum]
      _ =
        scale *
          (∫ ω, Finset.sum Finset.univ
            (fun i : Fin T => lhsStep i ω - prevStep i ω) ∂μ) := by
          rw [MeasureTheory.integral_finset_sum Finset.univ hdiff_int]
      _ =
        ∫ ω, scale * Finset.sum Finset.univ
          (fun i : Fin T => lhsStep i ω - prevStep i ω) ∂μ := by
          rw [MeasureTheory.integral_const_mul]
      _ = theorem1Equation4ErrorIncrementLHS S μ T L := by
          simp [theorem1Equation4ErrorIncrementLHS, scale, lhsStep, prevStep]
  simpa [dropStep, objStep, hinc_sum] using hdrop_sum

/-- Formula-level Lyapunov telescope bridge for Theorem 1 proof steps 13-16.

This is the source/coarser interface requested by the audit gate: it names the
shifted paper potential explicitly and consumes the two source-derived window
inputs, Lemma 1 and equation (4).  The proof body now reaches the exact generic
random-initial telescope API; the remaining leaves are the potential-drop
integrability/identity and the algebraic composition with Lemma 1 plus
equation (4), not another broad Theorem 1 supplier. -/
private theorem theorem1_lyapunov_potential_telescope_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma1_window :
      ∀ i : Fin T, sourceExpectationLE μ (lemma1LHSExpr S i.val)
        (lemma1RHSExpr S i.val))
    (hlemma1_finite_sum :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              S.objectiveValue (iterate S (i.val + 1) ω) -
                S.objectiveValue (iterate S i.val ω) ∂μ) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              (-stepsize S i.val ω / 4) *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2 ∂μ))
    (hEquation4 :
      theorem1Equation4ErrorIncrementLHS S μ T L ≤ theorem1Equation4RHS S μ T L) :
    theorem1WeightedGradientNormSqSum S μ T / 8 ≤
      (∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ) -
        (∫ ω, theorem1ShiftedLyapunovPotential S L fStar T ω ∂μ) +
          S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) := by
  classical
  let Φ : ℕ → Ω → ℝ := theorem1ShiftedLyapunovPotential S L fStar
  let drop : Fin T → Ω → ℝ := fun i ω => Φ i.val ω - Φ (i.val + 1) ω
  have hterminal_nonneg : ∀ ω, 0 ≤ Φ T ω := by
    intro ω
    exact theorem1ShiftedLyapunovPotential_nonneg
      S μ hsec3 hgenerated hEq4Scalar T ω
  have hdrop_int : ∀ i ∈ Finset.univ, Integrable (drop i) μ := by
    simpa [drop, Φ] using
      theorem1_shifted_lyapunov_drop_integrable
        S μ T hsec3 hgenerated hlemma1_window
  have hinitial_int : Integrable (Φ 0) μ := by
    simpa [Φ] using
      theorem1_shifted_lyapunov_initial_integrable
        S μ hsec3 hgenerated hEq4Scalar
  have hdrop_telescope_eq :
      Finset.sum Finset.univ (fun i : Fin T => ∫ ω, drop i ω ∂μ) =
        (∫ ω, Φ 0 ω ∂μ) - (∫ ω, Φ T ω ∂μ) := by
    exact
      integral_sum_telescope_eq_of_random_endpoints
        (P := μ) (times := Finset.univ) (drop := drop)
        (initial := Φ 0) (terminal := Φ T)
        hdrop_int hinitial_int
        (by
          intro ω
          simpa [drop, Φ] using
            theorem1_shifted_lyapunov_potential_fin_telescope S L fStar T ω)
  have hrandom_telescope_api :
      Finset.sum Finset.univ (fun i : Fin T => ∫ ω, drop i ω ∂μ) ≤
        (∫ ω, Φ 0 ω ∂μ) := by
    have hterminal_integral_nonneg : 0 ≤ ∫ ω, Φ T ω ∂μ :=
      integral_nonneg hterminal_nonneg
    rw [hdrop_telescope_eq]
    linarith
  have hlemma1_int :=
    theorem1_lemma1_window_generated_integrable_of_source_route
      S μ T hgenerated.1 hlemma1_window
  let objWindow : ℝ :=
    Finset.sum Finset.univ
      (fun i : Fin T =>
        ∫ ω,
          S.objectiveValue (iterate S (i.val + 1) ω) -
            S.objectiveValue (iterate S i.val ω) ∂μ)
  let lemma1RHSWindow : ℝ :=
    Finset.sum Finset.univ
      (fun i : Fin T =>
        ∫ ω,
          (-stepsize S i.val ω / 4) *
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
            (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2 ∂μ)
  let logBudget : ℝ :=
    S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ)
  let gradientErrorWindow : ℝ := theorem1Equation4GradientErrorWindowIntegral S μ T
  have hdrop_eval :
      (∫ ω, Φ 0 ω ∂μ) - (∫ ω, Φ T ω ∂μ) =
        - objWindow - theorem1Equation4ErrorIncrementLHS S μ T L := by
    have hdrop_formula :
        Finset.sum Finset.univ
            (fun i : Fin T => ∫ ω, drop i ω ∂μ) =
          - objWindow - theorem1Equation4ErrorIncrementLHS S μ T L := by
      simpa [drop, Φ, objWindow] using
        theorem1_shifted_lyapunov_drop_integral_eq
          S μ T hsec3 hgenerated hlemma1_window
    rw [← hdrop_telescope_eq]
    exact hdrop_formula
  have hlemma1_window_le : objWindow ≤ lemma1RHSWindow := by
    simpa [objWindow, lemma1RHSWindow] using hlemma1_finite_sum
  have hEquation4_window_le :
      theorem1Equation4ErrorIncrementLHS S μ T L ≤ logBudget + gradientErrorWindow := by
    simpa [logBudget, gradientErrorWindow,
      theorem1Equation4RHS_eq_logBudget_add_gradientErrorWindowIntegral]
      using hEquation4
  have hcombined :
      objWindow + theorem1Equation4ErrorIncrementLHS S μ T L ≤
        logBudget - theorem1WeightedGradientNormSqSum S μ T / 8 := by
    have hsum_le :
        objWindow + theorem1Equation4ErrorIncrementLHS S μ T L ≤
          lemma1RHSWindow + (logBudget + gradientErrorWindow) := by
      linarith
    have hcancel :
        lemma1RHSWindow + (logBudget + gradientErrorWindow) =
          logBudget - theorem1WeightedGradientNormSqSum S μ T / 8 := by
      unfold lemma1RHSWindow gradientErrorWindow theorem1WeightedGradientNormSqSum
        SOptLib.expected_weighted_certificate_energy theorem1Equation4GradientErrorWindowIntegral
      have hlemma1_rhs_integral :
          Finset.sum Finset.univ
              (fun i : Fin T =>
                ∫ ω,
                  (-stepsize S i.val ω / 4) *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                    (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2 ∂μ) =
            ∫ ω, Finset.sum Finset.univ
              (fun i : Fin T =>
                (-stepsize S i.val ω / 4) *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                  (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2) ∂μ := by
        rw [MeasureTheory.integral_finset_sum Finset.univ hlemma1_int.2]
      have hgrad_error_int :
          (∫ ω, Finset.sum Finset.univ
            (fun i : Fin T =>
              stepsize S i.val ω / 8 *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) ∂μ) =
            Finset.sum Finset.univ
              (fun i : Fin T =>
                ∫ ω,
                  stepsize S i.val ω / 8 *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                    3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2 ∂μ) := by
        rw [MeasureTheory.integral_finset_sum Finset.univ
          (by
            simpa [theorem1Equation4GradientErrorWindowIntegral] using
              theorem1_equation4_gradient_error_step_integrable_of_generated_boundary
                S μ T hsec3 hgenerated)]
      rw [hlemma1_rhs_integral, hgrad_error_int]
      have hpoint :
          (fun ω =>
              Finset.sum Finset.univ
                (fun i : Fin T =>
                  (-stepsize S i.val ω / 4) *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                    (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2) +
                Finset.sum Finset.univ
                  (fun i : Fin T =>
                    stepsize S i.val ω / 8 *
                        ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                      3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)) =
            (fun ω =>
              - Finset.sum Finset.univ
                (fun i : Fin T =>
                  stepsize S i.val ω *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) / 8) := by
        funext ω
        calc
          Finset.sum Finset.univ
                (fun i : Fin T =>
                  (-stepsize S i.val ω / 4) *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                    (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2) +
              Finset.sum Finset.univ
                (fun i : Fin T =>
                  stepsize S i.val ω / 8 *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                    3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)
              =
            Finset.sum Finset.univ
              (fun i : Fin T =>
                (-stepsize S i.val ω / 4) *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                  (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2 +
                (stepsize S i.val ω / 8 *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                  3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)) := by
              rw [← Finset.sum_add_distrib]
          _ =
            Finset.sum Finset.univ
              (fun i : Fin T =>
                -(stepsize S i.val ω *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) / 8) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
          _ =
            - Finset.sum Finset.univ
                (fun i : Fin T =>
                  stepsize S i.val ω *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) / 8 := by
              calc
                Finset.sum Finset.univ
                    (fun i : Fin T =>
                      -(stepsize S i.val ω *
                        ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) / 8)
                    =
                  Finset.sum Finset.univ
                    (fun i : Fin T =>
                      ((-1 : ℝ) / 8) *
                        (stepsize S i.val ω *
                          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
                _ =
                  ((-1 : ℝ) / 8) *
                    Finset.sum Finset.univ
                      (fun i : Fin T =>
                        stepsize S i.val ω *
                          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
                    rw [Finset.mul_sum]
                _ =
                  - Finset.sum Finset.univ
                      (fun i : Fin T =>
                        stepsize S i.val ω *
                          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) / 8 := by
                    ring
      have hsum_integral :
          (∫ ω, Finset.sum Finset.univ
              (fun i : Fin T =>
                (-stepsize S i.val ω / 4) *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                  (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2) ∂μ) +
            (∫ ω, Finset.sum Finset.univ
              (fun i : Fin T =>
                stepsize S i.val ω / 8 *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                  3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2) ∂μ) =
            ∫ ω, - Finset.sum Finset.univ
              (fun i : Fin T =>
                stepsize S i.val ω *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) / 8 ∂μ := by
        have hleft_int :
            Integrable
              (fun ω =>
                Finset.sum Finset.univ
                  (fun i : Fin T =>
                    (-stepsize S i.val ω / 4) *
                        ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                      (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2)) μ :=
          MeasureTheory.integrable_finset_sum Finset.univ hlemma1_int.2
        have hright_int :
            Integrable
              (fun ω =>
                Finset.sum Finset.univ
                  (fun i : Fin T =>
                    stepsize S i.val ω / 8 *
                        ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                      3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2)) μ := by
          exact
            MeasureTheory.integrable_finset_sum Finset.univ
              (by
                simpa [theorem1Equation4GradientErrorWindowIntegral] using
                  theorem1_equation4_gradient_error_step_integrable_of_generated_boundary
                    S μ T hsec3 hgenerated)
        rw [← MeasureTheory.integral_add hleft_int hright_int]
        exact integral_congr_ae (by
          filter_upwards with ω
          exact congrFun hpoint ω)
      have hsum_pair :
          (∫ ω, Finset.sum Finset.univ
              (fun i : Fin T =>
                (-stepsize S i.val ω / 4) *
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                  (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2) ∂μ) +
            Finset.sum Finset.univ
              (fun i : Fin T =>
                ∫ ω,
                  stepsize S i.val ω / 8 *
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 -
                    3 * stepsize S i.val ω / 4 * ‖error S i.val ω‖ ^ 2 ∂μ) =
            - theorem1WeightedGradientNormSqSum S μ T / 8 := by
        rw [← hgrad_error_int]
        rw [hsum_integral]
        unfold theorem1WeightedGradientNormSqSum SOptLib.expected_weighted_certificate_energy
        rw [MeasureTheory.integral_div, MeasureTheory.integral_neg]
      unfold theorem1WeightedGradientNormSqSum SOptLib.expected_weighted_certificate_energy at hsum_pair
      ring_nf at hsum_pair ⊢
      linarith
    linarith
  rw [hdrop_eval]
  linarith

/-- Endpoint bound for the shifted Lyapunov potential in Theorem 1 step 16.

The terminal potential is nonnegative by the finite lower bound `F* ≤ F(x)` and
the positive generated denominator; the initial potential is exactly
`F(x₁)-F*` plus the scaled random initial-error term. -/
private theorem theorem1_shifted_lyapunov_endpoint_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G) :
    (∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ) -
        (∫ ω, theorem1ShiftedLyapunovPotential S L fStar T ω ∂μ) ≤
      S.objectiveValue S.x₁ - fStar +
        (1 / (32 * L ^ 2 * initialStepsize S)) *
          (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) := by
  classical
  have hterminal_nonneg :
      ∀ ω, 0 ≤ theorem1ShiftedLyapunovPotential S L fStar T ω := by
    intro ω
    exact theorem1ShiftedLyapunovPotential_nonneg
      S μ hsec3 hgenerated hEq4Scalar T ω
  have hterminal_integral_nonneg :
      0 ≤ ∫ ω, theorem1ShiftedLyapunovPotential S L fStar T ω ∂μ :=
    integral_nonneg hterminal_nonneg
  have herror0_int : Integrable (fun ω => ‖error S 0 ω‖ ^ 2) μ := by
    rcases sourceGradientNoiseSecondMomentValue_le S μ hsec3 0 S.x₁ with
      ⟨value, hvalue, _hle⟩
    have hvalue' :
        Integrable
            (fun ω =>
              ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
                objectiveGradient S S.x₁‖ ^ 2) μ ∧
          value =
            ∫ ω,
              ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
                objectiveGradient S S.x₁‖ ^ 2 ∂μ :=
      (sourceRealExpectationValue_eq_some_iff μ
        (fun ω =>
          ‖stochasticGradient S S.x₁ (S.sample 0 ω) -
            objectiveGradient S S.x₁‖ ^ 2) value).1 hvalue
    exact hvalue'.1.congr (by
      filter_upwards with ω
      simp [error, direction_zero, iterate_zero])
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hη0_pos : 0 < initialStepsize S := by
    have hw_pos : 0 < S.w := hgenerated.1.1.1
    have hden_pos : 0 < Real.rpow S.w ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hw_pos ((1 : ℝ) / 3)
    rw [initialStepsize_eq]
    exact div_pos hgenerated.2 hden_pos
  have hη0_ne : initialStepsize S ≠ 0 := ne_of_gt hη0_pos
  have hPhi0_eval :
      (∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ) =
        S.objectiveValue S.x₁ - fStar +
          (1 / (32 * L ^ 2 * initialStepsize S)) *
            (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) := by
    have hpoint :
        (fun ω => theorem1ShiftedLyapunovPotential S L fStar 0 ω) =
          (fun ω =>
            (S.objectiveValue S.x₁ - fStar) +
              (1 / (32 * L ^ 2 * initialStepsize S)) *
                ‖error S 0 ω‖ ^ 2) := by
      funext ω
      simp [theorem1ShiftedLyapunovPotential, theorem1PreviousErrorDenominator,
        iterate_zero]
      field_simp [hL_ne, hη0_ne]
    rw [hpoint]
    rw [integral_add]
    · rw [integral_const, probReal_univ, smul_eq_mul]
      rw [integral_const_mul]
      ring
    · exact integrable_const (c := S.objectiveValue S.x₁ - fStar)
    · exact herror0_int.const_mul (1 / (32 * L ^ 2 * initialStepsize S))
  calc
    (∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ) -
        (∫ ω, theorem1ShiftedLyapunovPotential S L fStar T ω ∂μ)
        ≤ ∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ := by
          linarith
    _ =
      S.objectiveValue S.x₁ - fStar +
        (1 / (32 * L ^ 2 * initialStepsize S)) *
          (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) := hPhi0_eval

/-- The Lyapunov telescope part of Theorem 1 proof steps 13-16.

The hypotheses are the two source-derived finite-window inputs already
available on the live Theorem 1 route: Lemma 1 in totalized finite-sum form and
equation (4).  The remaining proof work is the potential telescope and finite
lower-bound algebra, strictly before the initial-error noise estimate. -/
private theorem theorem1_lyapunov_telescope_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (_hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma1_window :
      ∀ i : Fin T, sourceExpectationLE μ (lemma1LHSExpr S i.val)
        (lemma1RHSExpr S i.val))
    (_hlemma1_finite_sum :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              S.objectiveValue (iterate S (i.val + 1) ω) -
                S.objectiveValue (iterate S i.val ω) ∂μ) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              (-stepsize S i.val ω / 4) *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2 ∂μ))
    (_hEquation4 :
      theorem1Equation4ErrorIncrementLHS S μ T L ≤ theorem1Equation4RHS S μ T L) :
    theorem1WeightedGradientNormSqSum S μ T ≤
      8 * (S.objectiveValue S.x₁ - fStar) +
        (1 / (4 * L ^ 2 * initialStepsize S)) *
          (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) +
        S.k ^ 3 * S.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) := by
  classical
  have hpotential :
      theorem1WeightedGradientNormSqSum S μ T / 8 ≤
        (∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ) -
          (∫ ω, theorem1ShiftedLyapunovPotential S L fStar T ω ∂μ) +
            S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) :=
    theorem1_lyapunov_potential_telescope_bound
      S μ T _hsec3 hgenerated _hEq4Scalar hlemma1_window
      _hlemma1_finite_sum _hEquation4
  have hendpoint :
      (∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ) -
          (∫ ω, theorem1ShiftedLyapunovPotential S L fStar T ω ∂μ) ≤
        S.objectiveValue S.x₁ - fStar +
          (1 / (32 * L ^ 2 * initialStepsize S)) *
            (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) :=
    theorem1_shifted_lyapunov_endpoint_bound
      S μ T _hsec3 hgenerated _hEq4Scalar
  have hcombined :
      theorem1WeightedGradientNormSqSum S μ T / 8 ≤
        S.objectiveValue S.x₁ - fStar +
          (1 / (32 * L ^ 2 * initialStepsize S)) *
            (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) +
          S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) := by
    have hendpoint_add :
        (∫ ω, theorem1ShiftedLyapunovPotential S L fStar 0 ω ∂μ) -
            (∫ ω, theorem1ShiftedLyapunovPotential S L fStar T ω ∂μ) +
            S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) ≤
          S.objectiveValue S.x₁ - fStar +
            (1 / (32 * L ^ 2 * initialStepsize S)) *
              (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) +
            S.k ^ 3 * S.c ^ 2 / (16 * L ^ 2) * Real.log (T + 2 : ℝ) := by
      linarith
    exact hpotential.trans hendpoint_add
  ring_nf at hcombined ⊢
  nlinarith

/-- The Lyapunov telescope and initial-error estimate from Theorem 1 proof
steps 13-17, isolated from the later Cauchy-Schwarz/root-sum argument. -/
private theorem theorem1_weighted_gradient_bound_final
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (_hgenerated : generatedStepsizeQuotientBoundary S)
    (hEq4Scalar : theorem1Equation4ScalarBoundary S L G)
    (hlemma1_route :
      ∀ t,
        (∀ s, sourceStepsizeLE S s ((1 : ℝ) / (4 * L))) →
          sourceExpectationLE μ (lemma1LHSExpr S t) (lemma1RHSExpr S t))
    (hEquation4 :
      theorem1Equation4ErrorIncrementLHS S μ T L ≤ theorem1Equation4RHS S μ T L) :
    theorem1WeightedGradientNormSqSum S μ T ≤ S.k * theorem1M S T L σ fStar := by
  classical
  have hEquation4' := hEquation4
  have hlemma1_window :
      ∀ i : Fin T,
        sourceExpectationLE μ (lemma1LHSExpr S i.val) (lemma1RHSExpr S i.val) :=
    theorem1_lemma1_window_source_route S μ T _hgenerated.1 hEq4Scalar hlemma1_route
  have hlemma1_finite_sum :
      Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              S.objectiveValue (iterate S (i.val + 1) ω) -
                S.objectiveValue (iterate S i.val ω) ∂μ) ≤
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              (-stepsize S i.val ω / 4) *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                (3 * stepsize S i.val ω / 4) * ‖error S i.val ω‖ ^ 2 ∂μ) :=
    theorem1_lemma1_finite_sum_bound S μ T _hgenerated.1 hlemma1_window
  -- Remaining work: convert the finite-window Lemma 1 source comparisons into
  -- the summed potential descent with `hlemma1_finite_sum`, telescope `Φ_t`,
  -- use the finite lower bound, and rewrite the initial error term.
  have hlyap :
      theorem1WeightedGradientNormSqSum S μ T ≤
        8 * (S.objectiveValue S.x₁ - fStar) +
          (1 / (4 * L ^ 2 * initialStepsize S)) *
            (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) +
          S.k ^ 3 * S.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) :=
    theorem1_lyapunov_telescope_bound
      S μ T _hsec3 _hgenerated hEq4Scalar hlemma1_window hlemma1_finite_sum hEquation4'
  have hinitial :
      (1 / (4 * L ^ 2 * initialStepsize S)) *
          (∫ ω, ‖error S 0 ω‖ ^ 2 ∂μ) ≤
        Real.rpow S.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * S.k) :=
    theorem1_initial_error_term_bound S μ _hsec3 _hgenerated hEq4Scalar
  have hsource_bound :
      theorem1WeightedGradientNormSqSum S μ T ≤
        8 * (S.objectiveValue S.x₁ - fStar) +
          Real.rpow S.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * S.k) +
          S.k ^ 3 * S.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) := by
    linarith
  have hL_pos : 0 < L := hEq4Scalar.L_pos
  have hk_pos : 0 < S.k := _hgenerated.2
  have hM_scaled :
      S.k * theorem1M S T L σ fStar =
        8 * (S.objectiveValue S.x₁ - fStar) +
          Real.rpow S.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * S.k) +
          S.k ^ 3 * S.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) := by
    rw [theorem1M_eq]
    field_simp [ne_of_gt hk_pos, ne_of_gt hL_pos]
  simpa [hM_scaled] using hsource_bound

/- Theorem 1 proof steps 18-31, kept in the scalar case-split form used by
the source proof.

Earlier route attempts compressed this into the additive root-sum bound
`sqrt(2M) * (w + 2Tσ²)^(1/6) + 2M^(3/4)`.  That additive bound is useful as an
intermediate displayed estimate, but it is too coarse for the final printed
RHS normalization when consumed as a standalone scalar inequality.  The paper
derives the last line from the two scalar alternatives; this interface exposes
those alternatives directly so the final average step does not route through
the disproved additive-normalization helper below. -/
/-- Theorem 1 proof step 19: decreasing adaptive stepsizes lower-bound the
weighted gradient-square sum by the terminal stepsize times the unweighted
square sum. -/
private def theorem1TerminalGradientIndex (T : ℕ) : ℕ :=
  T - 1

/-- Canonical generated sampled-gradient denominator for the paper's Theorem 1
window `G_1, ..., G_T`.

The file's generated state index `n` denotes paper time `n+1`, so the paper's
terminal denominator in `η_T = k / (w + ∑_{i=1}^T G_i^2)^(1/3)` is represented
by `cumulativeGradientNormSq S (T - 1)` when `0 < T`. -/
def theorem1TerminalCumulativeGradientNormSq
    (S : Setup Ω Sample E) (T : ℕ) : Ω → ℝ :=
  cumulativeGradientNormSq S (theorem1TerminalGradientIndex T)

private theorem cumulativeGradientNormSq_eq_sum_range
    (S : Setup Ω Sample E) (n : ℕ) (ω : Ω) :
    cumulativeGradientNormSq S n ω =
      (Finset.range (n + 1)).sum
        (fun i => ‖S.stochasticGradient (iterate S i ω) (S.sample i ω)‖ ^ 2) := by
  induction n with
  | zero =>
      simp [cumulativeGradientNormSq_zero, iterate_zero]
  | succ n ih =>
      rw [cumulativeGradientNormSq_succ, ih]
      conv_rhs => rw [Finset.sum_range_succ]

private theorem theorem1TerminalCumulativeGradientNormSq_eq_fin_sum
    (S : Setup Ω Sample E) (T : ℕ) (hT : 0 < T) (ω : Ω) :
    theorem1TerminalCumulativeGradientNormSq S T ω =
      Finset.sum Finset.univ
        (fun i : Fin T =>
          ‖S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω)‖ ^ 2) := by
  classical
  have hsub : theorem1TerminalGradientIndex T + 1 = T := by
    dsimp [theorem1TerminalGradientIndex]
    exact Nat.sub_add_cancel hT
  rw [theorem1TerminalCumulativeGradientNormSq,
    cumulativeGradientNormSq_eq_sum_range, hsub, Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [Finset.mem_range.mp hi]

private theorem theorem1TerminalCumulativeGradientNormSq_pointwise_noise_split
    (S : Setup Ω Sample E) (T : ℕ) (hT : 0 < T) (ω : Ω) :
    theorem1TerminalCumulativeGradientNormSq S T ω ≤
      2 *
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ‖S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω) -
                objectiveGradient S (iterate S i.val ω)‖ ^ 2) +
        2 *
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
  classical
  rw [theorem1TerminalCumulativeGradientNormSq_eq_fin_sum S T hT ω]
  calc
    Finset.sum Finset.univ
        (fun i : Fin T =>
          ‖S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω)‖ ^ 2)
        ≤ Finset.sum Finset.univ
            (fun i : Fin T =>
              2 *
                  ‖S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω) -
                    objectiveGradient S (iterate S i.val ω)‖ ^ 2 +
                2 * ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          have hdecomp :
              S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω) =
                (S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω) -
                    objectiveGradient S (iterate S i.val ω)) +
                  objectiveGradient S (iterate S i.val ω) := by
            abel
          have h :=
            SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
              (S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω) -
                objectiveGradient S (iterate S i.val ω))
              (objectiveGradient S (iterate S i.val ω))
          simpa [← hdecomp] using h
    _ =
        2 *
            Finset.sum Finset.univ
              (fun i : Fin T =>
                ‖S.stochasticGradient (iterate S i.val ω) (S.sample i.val ω) -
                  objectiveGradient S (iterate S i.val ω)‖ ^ 2) +
          2 *
            Finset.sum Finset.univ
              (fun i : Fin T =>
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
          rw [Finset.sum_add_distrib]
          simp [Finset.mul_sum]

/-- Pointwise cube-root split used in Theorem 1 proof step 24.

After the sampled-gradient denominator is split into a noise window and an
objective-gradient window, this scalar bridge applies the subadditive branch of
`x ↦ x^(1/3)` without any stochastic assumptions.  The stochastic work is
therefore isolated in the finite-window variance and Jensen leaves. -/
private theorem theorem1_terminal_rpow_pointwise_noise_grad_split
    {w terminal noise grad : ℝ}
    (hw : 0 ≤ w) (hterminal_nonneg : 0 ≤ terminal)
    (hnoise_nonneg : 0 ≤ noise) (hgrad_nonneg : 0 ≤ grad)
    (hterminal_le : terminal ≤ 2 * noise + 2 * grad) :
    Real.rpow (w + terminal) ((1 : ℝ) / 3) ≤
      Real.rpow (w + 2 * noise) ((1 : ℝ) / 3) +
        Real.rpow 2 ((1 : ℝ) / 3) * Real.rpow grad ((1 : ℝ) / 3) := by
  exact rpow_add_split_of_le_weighted_add
    (add_nonneg hw hterminal_nonneg)
    (add_nonneg hw (mul_nonneg (by norm_num) hnoise_nonneg))
    hgrad_nonneg (by norm_num) (by norm_num) hterminal_le

private theorem theorem1_cumulativeGradientNormSq_mono
    (S : Setup Ω Sample E) (ω : Ω) :
    Monotone (fun n => cumulativeGradientNormSq S n ω) := by
  intro m n hmn
  rcases Nat.exists_eq_add_of_le hmn with ⟨r, rfl⟩
  induction r with
  | zero =>
      simp
  | succ r ih =>
      calc
        cumulativeGradientNormSq S m ω ≤ cumulativeGradientNormSq S (m + r) ω :=
          ih (by omega)
        _ ≤ cumulativeGradientNormSq S (m + (r + 1)) ω := by
          rw [show m + (r + 1) = (m + r) + 1 by omega,
            cumulativeGradientNormSq_succ]
          exact le_add_of_nonneg_right (sq_nonneg _)

private theorem theorem1_generated_stepsize_antitone
    (S : Setup Ω Sample E)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    Antitone (fun n : ℕ => stepsize S n ω) := by
  simpa [stepsize_eq] using
    (SOptLib.inverse_rpow_step_size_antitone_of_monotone
      S.k S.w ((1 : ℝ) / 3)
      (fun n => cumulativeGradientNormSq S n ω)
      (theorem1_cumulativeGradientNormSq_mono S ω)
      (fun n => (hgenerated.1.2 n ω).1)
      (le_of_lt hgenerated.2) (by norm_num))

private theorem theorem1_terminal_stepsize_mul_sum_le_weighted_sum
    (S : Setup Ω Sample E) (T : ℕ) (ω : Ω)
    (hη_mono : ∀ i : Fin T,
      stepsize S (theorem1TerminalGradientIndex T) ω ≤ stepsize S i.val ω) :
    stepsize S (theorem1TerminalGradientIndex T) ω *
        Finset.sum Finset.univ
          (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ≤
      Finset.sum Finset.univ
        (fun i : Fin T =>
          stepsize S i.val ω * ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _hi
  exact mul_le_mul_of_nonneg_right (hη_mono i) (sq_nonneg _)

private theorem theorem1_stepsize_mul_objectiveGradient_norm_sq_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (ηIndex gradIndex : ℕ)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    Integrable
      (fun ω =>
        stepsize S ηIndex ω *
          ‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2) μ := by
  classical
  have hη_aesm :
      AEStronglyMeasurable (stepsize S ηIndex) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3
      (lemma2_stepsize_prefixAEMeasurable S μ hsec3 ηIndex)).aestronglyMeasurable
  have hgrad_sq_aesm :
      AEStronglyMeasurable
        (fun ω => ‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2) μ := by
    have hiter_prefix := lemma3_iterate_prefixAEMeasurable S μ hsec3 gradIndex
    have hobj_prefix :
        @prefixAEMeasurable Ω ℝ _ _
          (⨆ j < gradIndex + 1, MeasurableSpace.comap (S.sample j)
            (by infer_instance : MeasurableSpace Sample))
          (fun ω => ‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2) μ :=
      (hiter_prefix.comp_measurable
        (section3_objectiveGradient_continuous S μ hsec3 0).measurable).norm_sq
    exact
      (prefixAEMeasurable.aemeasurable S μ hsec3 hobj_prefix).aestronglyMeasurable
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω =>
          stepsize S ηIndex ω *
            ‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2) μ :=
    hη_aesm.mul hgrad_sq_aesm
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 ηIndex hgenerated with
    ⟨Aη, hAη_nonneg, hAη⟩
  refine Integrable.of_bound hZ_aesm (C := Aη * G ^ 2) ?_
  filter_upwards [hAη] with ω hηω
  have hobjω :
      ‖objectiveGradient S (iterate S gradIndex ω)‖ ≤ G :=
    section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S gradIndex ω)
  have hobj_sq :
      ‖‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2‖ ≤ G ^ 2 := by
    have hsq :
        ‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2 ≤ G ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hobjω 2
    simpa [Real.norm_of_nonneg (sq_nonneg _)] using hsq
  calc
    ‖stepsize S ηIndex ω *
        ‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2‖ =
        ‖stepsize S ηIndex ω‖ *
          ‖‖objectiveGradient S (iterate S gradIndex ω)‖ ^ 2‖ := by
          rw [norm_mul]
    _ ≤ Aη * G ^ 2 :=
        mul_le_mul hηω hobj_sq (norm_nonneg _) hAη_nonneg

/-- Generated-boundary integrability for `η_t * ‖ε_t‖²`.

This is the missing generated-run RHS component for Lemma 1.  It is proved
from the generated stepsize bound, the generated error bound, and prefix
measurability of the Algorithm 1 history, not from the stale local source
definedness wrapper. -/
private theorem lemma1_stepsize_mul_error_norm_sq_integrable_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (t : ℕ) :
    Integrable (fun ω => stepsize S t ω * ‖error S t ω‖ ^ 2) μ := by
  classical
  have hη_aesm :
      AEStronglyMeasurable (stepsize S t) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3
      (lemma2_stepsize_prefixAEMeasurable S μ hsec3 t)).aestronglyMeasurable
  have herror_sq_aesm :
      AEStronglyMeasurable (fun ω => ‖error S t ω‖ ^ 2) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3
      (lemma3_error_prefixAEMeasurable S μ hsec3 t).norm_sq).aestronglyMeasurable
  have hZ_aesm :
      AEStronglyMeasurable
        (fun ω => stepsize S t ω * ‖error S t ω‖ ^ 2) μ :=
    hη_aesm.mul herror_sq_aesm
  rcases lemma2_generated_stepsize_eventually_bound S μ hsec3 t hgenerated with
    ⟨Aη, hAη_nonneg, hAη⟩
  have hloc3 : lemma3LocalQuotientBoundary S t :=
    lemma3LocalQuotientBoundary_of_generated_boundary S hgenerated t
  rcases lemma3_generated_error_eventually_bound S μ hsec3 t hloc3 with
    ⟨Bε, hBε_nonneg, hBε⟩
  refine Integrable.of_bound hZ_aesm (C := Aη * Bε ^ 2) ?_
  filter_upwards [hAη, hBε] with ω hηω hεω
  have hε_sq :
      ‖‖error S t ω‖ ^ 2‖ ≤ Bε ^ 2 := by
    have hsq : ‖error S t ω‖ ^ 2 ≤ Bε ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hεω 2
    simpa [Real.norm_of_nonneg (sq_nonneg _)] using hsq
  calc
    ‖stepsize S t ω * ‖error S t ω‖ ^ 2‖ =
        ‖stepsize S t ω‖ * ‖‖error S t ω‖ ^ 2‖ := by
          rw [norm_mul]
    _ ≤ Aη * Bε ^ 2 :=
        mul_le_mul hηω hε_sq (norm_nonneg _) hAη_nonneg

/-- Generated-run integrability of Lemma 1's totalized right representative. -/
private theorem lemma1_rhs_integrable_of_generated_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (t : ℕ) :
    Integrable
      (fun ω =>
        (-stepsize S t ω / 4) *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2 +
          (3 * stepsize S t ω / 4) * ‖error S t ω‖ ^ 2) μ := by
  classical
  have hgrad :
      Integrable
        (fun ω =>
          stepsize S t ω *
            ‖objectiveGradient S (iterate S t ω)‖ ^ 2) μ :=
    theorem1_stepsize_mul_objectiveGradient_norm_sq_integrable
      S μ hsec3 t t hgenerated
  have herr :
      Integrable (fun ω => stepsize S t ω * ‖error S t ω‖ ^ 2) μ :=
    lemma1_stepsize_mul_error_norm_sq_integrable_of_generated_boundary
      S μ hsec3 hgenerated t
  have hcombined :
      Integrable
        (fun ω =>
          (-1 / 4) *
              (stepsize S t ω *
                ‖objectiveGradient S (iterate S t ω)‖ ^ 2) +
            (3 / 4) * (stepsize S t ω * ‖error S t ω‖ ^ 2)) μ :=
    (hgrad.const_mul ((-1 : ℝ) / 4)).add (herr.const_mul ((3 : ℝ) / 4))
  refine hcombined.congr ?_
  filter_upwards with ω
  ring

/-- Lemma 1 source comparison at the generated Algorithm 1 boundary.

This is the active source/coarser supplier for Theorem 1.  It derives the local
source expression equalities from `generatedStepsizeScalarBoundary`, derives
stepsize positivity from `generatedStepsizeQuotientBoundary`, and consumes the
generated-run RHS integrability bridge above. -/
private theorem lemma1_biased_sgd_descent_of_generated_quotient_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hL_pos : 0 < L)
    (t : ℕ)
    (heta : ∀ s, sourceStepsizeLE S s ((1 : ℝ) / (4 * L))) :
    sourceExpectationLE μ (lemma1LHSExpr S t) (lemma1RHSExpr S t) := by
  classical
  let Z : Ω → ℝ := fun ω =>
    S.objectiveValue (iterate S (t + 1) ω) -
      S.objectiveValue (iterate S t ω)
  let W : Ω → ℝ := fun ω =>
    (-stepsize S t ω / 4) *
        ‖objectiveGradient S (iterate S t ω)‖ ^ 2 +
      (3 * stepsize S t ω / 4) * ‖error S t ω‖ ^ 2
  have hlocal : lemma1LocalSourceBoundary S t :=
    lemma1LocalSourceBoundary_of_generated_boundary S hgenerated.1 t
  have hZ_some : ∀ ω, lemma1LHSExpr S t ω = some (Z ω) := by
    intro ω
    simpa [Z] using lemma1LHSExpr_eq_some_of_local_boundary S hlocal ω
  have hW_some : ∀ ω, lemma1RHSExpr S t ω = some (W ω) := by
    intro ω
    simpa [W] using lemma1RHSExpr_eq_some_of_local_boundary S hlocal ω
  have hZ_int : Integrable Z μ := by
    simpa [Z] using
      lemma1_lhs_integrable_of_generated_boundary S μ hsec3 hgenerated t
  have hW_int : Integrable W μ := by
    simpa [W] using
      lemma1_rhs_integrable_of_generated_boundary S μ hsec3 hgenerated t
  have hpoint : ∀ᵐ ω ∂μ, Z ω ≤ W ω := by
    simpa [Z, W] using
      lemma1_pointwise_descent_bound_of_generated_quotient_boundary
        S μ hsec3 hgenerated hL_pos t heta
  have hle : ∫ ω, Z ω ∂μ ≤ ∫ ω, W ω ∂μ :=
    integral_mono_ae hZ_int hW_int hpoint
  exact sourceExpectationLE_of_forall_eq_some μ (lemma1LHSExpr S t)
    (lemma1RHSExpr S t) Z W hZ_some hW_some hZ_int hW_int hle

/-- Corrected generated-run boundary for Lemma 1.

The unguarded local-boundary formulation is false in the Lean realization:
`old_unguarded_lemma1_counterexample_degenerate` shows that source
definedness alone can make the partial expectation statement vacuous/undefined.
The source route used by Theorem 1 is the generated Algorithm 1 run, where the
quotient boundary supplies positive stepsizes and the theorem scalar boundary
supplies `0 < L`.  This public theorem exposes that corrected boundary while
delegating the proof to the route-local generated supplier above. -/
theorem lemma1_biased_sgd_descent_generated_run_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hL_pos : 0 < L)
    (t : ℕ)
    (heta : ∀ s, sourceStepsizeLE S s ((1 : ℝ) / (4 * L))) :
    sourceExpectationLE μ (lemma1LHSExpr S t) (lemma1RHSExpr S t) :=
  lemma1_biased_sgd_descent_of_generated_quotient_boundary
    S μ hsec3 hgenerated hL_pos t heta

/-- Integrability of the reciprocal terminal stepsize used in Theorem 1's
weighted Cauchy-Schwarz step. -/
private theorem theorem1_reciprocal_stepsize_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (t : ℕ)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    Integrable (fun ω => 1 / stepsize S t ω) μ := by
  classical
  have hrec_aesm :
      AEStronglyMeasurable (fun ω => 1 / stepsize S t ω) μ :=
    (prefixAEMeasurable.aemeasurable S μ hsec3
      (lemma2_reciprocal_stepsize_prefixAEMeasurable S μ hsec3 t)).aestronglyMeasurable
  rcases lemma2_generated_reciprocal_stepsize_eventually_bound
      S μ hsec3 t hgenerated with
    ⟨A, _hA_nonneg, hA⟩
  exact Integrable.of_bound hrec_aesm (C := A) hA

/-- Integrability of Theorem 1's expected root-sum representative.  This is the
finite-window well-definedness bridge used before both the weighted
Cauchy-Schwarz step and the final average-gradient comparison. -/
private theorem theorem1_expected_root_gradient_norm_sq_sum_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) :
    Integrable
      (fun ω =>
        Real.sqrt
          (Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))) μ := by
  exact integrable_sqrt_sum_sq_norm_of_ae_bound μ
    (fun i : Fin T => fun ω => objectiveGradient S (iterate S i.val ω)) G
    (fun i =>
      (theorem1_output_window_integrability_from_G_lipschitz S μ hsec3 T i).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω i =>
      section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S i.val ω))

/-- Source-specific root-sum bound from Section 3's `G`-Lipschitz losses.

This is the scalar invariant missing from the failed arbitrary-`X` route:
Theorem 1's `X` is not an arbitrary nonnegative real, but the expectation of
the generated finite root-sum of objective-gradient norms.  Since Section 3
derives `‖∇F(x)‖ ≤ G`, the root-sum random variable is bounded by
`sqrt(T * G^2)` throughout the finite window. -/
private theorem theorem1_expected_root_gradient_norm_sq_sum_le_sqrt_T_mul_G_sq
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) :
    theorem1ExpectedRootGradientNormSqSum S μ T ≤ Real.sqrt ((T : ℝ) * G ^ 2) := by
  simpa [theorem1ExpectedRootGradientNormSqSum] using
    integral_sqrt_sum_sq_norm_le_sqrt_card_mul_sq_of_ae_bound μ
      (fun i : Fin T => fun ω => objectiveGradient S (iterate S i.val ω)) G
      (fun i =>
        (theorem1_output_window_integrability_from_G_lipschitz S μ hsec3 T i).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω i =>
        section3_objectiveGradient_norm_le S μ hsec3 0 (iterate S i.val ω))

private theorem integral_sqrt_sum_sq_weighted_cauchy_bound
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {η sumSq : Ω → ℝ} {B : ℝ}
    (hη_pos : ∀ᵐ ω ∂μ, 0 < η ω)
    (hroot_int : Integrable (fun ω => Real.sqrt (sumSq ω)) μ)
    (hrec_int : Integrable (fun ω => 1 / η ω) μ)
    (hweighted_int : Integrable (fun ω => η ω * sumSq ω) μ)
    (hsumSq_nonneg : ∀ᵐ ω ∂μ, 0 ≤ sumSq ω)
    (hweighted_le : ∫ ω, η ω * sumSq ω ∂μ ≤ B) :
    (∫ ω, Real.sqrt (sumSq ω) ∂μ) ^ 2 ≤
      (∫ ω, 1 / η ω ∂μ) * B := by
  exact sq_integral_sqrt_le_integral_inv_mul_weighted_bound
    μ η sumSq B hη_pos hrec_int hweighted_int hsumSq_nonneg hweighted_le

private theorem theorem1_eta_T_weighted_lower_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hT : 0 < T)
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S) :
    ∫ ω,
        stepsize S (theorem1TerminalGradientIndex T) ω *
          Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ∂μ ≤
      theorem1WeightedGradientNormSqSum S μ T := by
  classical
  have hη_pos : ∀ n ω, 0 < stepsize S n ω := by
    intro n ω
    exact stepsize_pos_of_generated_quotient_boundary S hgenerated n ω
  have hη_decreasing :
      ∀ i : Fin T, ∀ᵐ ω ∂μ,
        stepsize S (theorem1TerminalGradientIndex T) ω ≤ stepsize S i.val ω := by
    intro i
    filter_upwards with ω
    exact theorem1_generated_stepsize_antitone S hgenerated (by
      dsimp [theorem1TerminalGradientIndex]
      omega)
  have hpoint :
      ∀ᵐ ω ∂μ,
        stepsize S (theorem1TerminalGradientIndex T) ω *
            Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ≤
          Finset.sum Finset.univ
            (fun i : Fin T =>
              stepsize S i.val ω *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
    have hη_all :
        ∀ᵐ ω ∂μ, ∀ i : Fin T,
          stepsize S (theorem1TerminalGradientIndex T) ω ≤ stepsize S i.val ω :=
      (Filter.eventually_all).2 hη_decreasing
    filter_upwards [hη_all] with ω hηω
    exact theorem1_terminal_stepsize_mul_sum_le_weighted_sum S T ω hηω
  have hleft_sum_int :
      Integrable
        (fun ω =>
          Finset.sum Finset.univ
            (fun i : Fin T =>
              stepsize S (theorem1TerminalGradientIndex T) ω *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) μ := by
    refine MeasureTheory.integrable_finset_sum (s := Finset.univ) ?_
    intro i _hi
    exact
      theorem1_stepsize_mul_objectiveGradient_norm_sq_integrable
        S μ hsec3 (theorem1TerminalGradientIndex T) i.val hgenerated
  have hleft_int :
      Integrable
        (fun ω =>
          stepsize S (theorem1TerminalGradientIndex T) ω *
            Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) μ := by
    refine hleft_sum_int.congr ?_
    filter_upwards with ω
    rw [Finset.mul_sum]
  have hright_int :
      Integrable
        (fun ω =>
          Finset.sum Finset.univ
            (fun i : Fin T =>
              stepsize S i.val ω *
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) μ := by
    refine MeasureTheory.integrable_finset_sum (s := Finset.univ) ?_
    intro i _hi
    exact
      theorem1_stepsize_mul_objectiveGradient_norm_sq_integrable
        S μ hsec3 i.val i.val hgenerated
  simpa [theorem1WeightedGradientNormSqSum] using
    integral_mono_ae hleft_int hright_int hpoint

/-- Theorem 1 proof step 20: Cauchy-Schwarz converts the weighted
gradient-square control into a bound on the squared expected root-sum. -/
private theorem theorem1_cauchy_schwarz_root_sum_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hT : 0 < T)
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hetaT_lower :
      ∫ ω,
          stepsize S (theorem1TerminalGradientIndex T) ω *
            Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ∂μ ≤
        theorem1WeightedGradientNormSqSum S μ T)
    (hweighted :
      theorem1WeightedGradientNormSqSum S μ T ≤ S.k * theorem1M S T L σ fStar) :
    theorem1ExpectedRootGradientNormSqSum S μ T ^ 2 ≤
      (∫ ω, (1 / stepsize S (theorem1TerminalGradientIndex T) ω) ∂μ) *
        (S.k * theorem1M S T L σ fStar) := by
  classical
  have hweighted_terminal :
      ∫ ω,
          stepsize S (theorem1TerminalGradientIndex T) ω *
            Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ∂μ ≤
        S.k * theorem1M S T L σ fStar :=
    le_trans hetaT_lower hweighted
  have hroot_int :
      Integrable
        (fun ω =>
          Real.sqrt
            (Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))) μ :=
    theorem1_expected_root_gradient_norm_sq_sum_integrable S μ T hsec3
  have hrec_int :
      Integrable
        (fun ω => 1 / stepsize S (theorem1TerminalGradientIndex T) ω) μ :=
    theorem1_reciprocal_stepsize_integrable S μ hsec3
      (theorem1TerminalGradientIndex T) hgenerated
  have hweighted_int :
      Integrable
        (fun ω =>
          stepsize S (theorem1TerminalGradientIndex T) ω *
            Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) μ := by
    have hsum_int :
        Integrable
          (fun ω =>
            Finset.sum Finset.univ
              (fun i : Fin T =>
                stepsize S (theorem1TerminalGradientIndex T) ω *
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) μ := by
      refine MeasureTheory.integrable_finset_sum (s := Finset.univ) ?_
      intro i _hi
      exact theorem1_stepsize_mul_objectiveGradient_norm_sq_integrable
        S μ hsec3 (theorem1TerminalGradientIndex T) i.val hgenerated
    refine hsum_int.congr ?_
    filter_upwards with ω
    rw [Finset.mul_sum]
  have hη_pos :
      ∀ᵐ ω ∂μ, 0 < stepsize S (theorem1TerminalGradientIndex T) ω := by
    filter_upwards with ω
    exact stepsize_pos_of_generated_quotient_boundary S hgenerated
      (theorem1TerminalGradientIndex T) ω
  have hsumSq_nonneg :
      ∀ᵐ ω ∂μ,
        0 ≤
          Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
    filter_upwards with ω
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
  simpa [theorem1ExpectedRootGradientNormSqSum] using
    integral_sqrt_sum_sq_weighted_cauchy_bound
      (μ := μ)
      (η := fun ω => stepsize S (theorem1TerminalGradientIndex T) ω)
      (sumSq := fun ω =>
        Finset.sum Finset.univ
          (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
      (B := S.k * theorem1M S T L σ fStar)
      hη_pos hroot_int hrec_int hweighted_int hsumSq_nonneg hweighted_terminal

/-- Theorem 1 proof steps 21-22: rewrite `1/η_T` through the adaptive
stepsize identity and the scalar `M` definition. -/
private theorem theorem1_root_sum_bound_with_sampled_gradients
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hT : 0 < T)
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hroot_cauchy :
      theorem1ExpectedRootGradientNormSqSum S μ T ^ 2 ≤
        (∫ ω, (1 / stepsize S (theorem1TerminalGradientIndex T) ω) ∂μ) *
          (S.k * theorem1M S T L σ fStar)) :
    theorem1ExpectedRootGradientNormSqSum S μ T ^ 2 ≤
      ∫ ω,
        theorem1M S T L σ fStar *
          Real.rpow
            (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
            ((1 : ℝ) / 3) ∂μ := by
  exact le_integral_mul_rpow_of_le_reciprocal_inverse_rpow_stepsize μ
    (stepsize S (theorem1TerminalGradientIndex T))
    (fun ω => S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
    S.k (theorem1M S T L σ fStar) ((1 : ℝ) / 3)
    (theorem1ExpectedRootGradientNormSqSum S μ T ^ 2)
    (Filter.Eventually.of_forall fun ω => by
      simp [stepsize_eq, theorem1TerminalCumulativeGradientNormSq,
        SOptLib.inverse_rpow_step_size_def])
    (Filter.Eventually.of_forall fun ω => by
      simpa [theorem1TerminalCumulativeGradientNormSq] using
        (hgenerated.1.2 (theorem1TerminalGradientIndex T) ω).1)
    hM.1 hroot_cauchy

/-- The generated iterate `x_i` is adapted to the strict sample prefix before
the sample `ξ_i` used in `G_i`.

This is the exact random-iterate boundary needed for Theorem 1 proof step 23:
`x_i` is fixed before the fresh sample whose stochastic gradient is recorded in
the cumulative generated denominator. -/
private theorem theorem1_iterate_strict_prefixAEMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (i : ℕ) :
    @prefixAEMeasurable Ω (DecisionSpace d) _ _
      (⨆ j < i, MeasurableSpace.comap (S.sample j)
        (by infer_instance : MeasurableSpace Sample))
      (iterate S i) μ := by
  cases i with
  | zero =>
      refine ⟨fun _ω : Ω => S.x₁, measurable_const, ?_⟩
      filter_upwards with ω
      simp [iterate, stateProcess, initialState]
  | succ i =>
      exact lemma3_iterate_succ_prefixAEMeasurable S μ hsec3 i

/-- Section 3's fixed-query variance bound transferred to the generated
random iterate at the matching fresh sample, including the finite second-moment
integrability needed for finite-window summation.

This is Theorem 1 proof step 25's variance-transport ingredient for
`ζ_i = ∇f(x_i, ξ_i) - ∇F(x_i)`.  The proof uses the law-scoped product
regularity route rather than the rejected full off-stream oracle-kernel
measurability assumption. -/
private theorem theorem1_random_iterate_noise_second_moment_integrable_and_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (i : ℕ) :
    Integrable
        (fun ω =>
          ‖stochasticGradient S (iterate S i ω) (S.sample i ω) -
            objectiveGradient S (iterate S i ω)‖ ^ 2) μ ∧
      ∫ ω,
          ‖stochasticGradient S (iterate S i ω) (S.sample i ω) -
            objectiveGradient S (iterate S i ω)‖ ^ 2 ∂μ ≤ σ ^ 2 := by
  exact randomQuery_oracleResidual_sq_integrable_and_integral_le_of_indep_fixed
    μ (iterate S i) (S.sample i) (stochasticGradient S) (objectiveGradient S) (σ ^ 2)
    (by
      have hres := section3_sampled_product_residual_aestronglyMeasurable
        S μ hsec3 i (Measure.map (iterate S i) μ)
          (fun x : DecisionSpace d => x) measurable_id
      simpa [pow_two] using hres.norm.mul hres.norm)
    (prefixAEMeasurable.aemeasurable S μ hsec3
      (theorem1_iterate_strict_prefixAEMeasurable S μ hsec3 i))
    (hsec3.sample_measurable i).aemeasurable
    (section3_indepFun_sample_prefixAEMeasurable_future S μ hsec3
      (theorem1_iterate_strict_prefixAEMeasurable S μ hsec3 i) (Nat.le_refl i))
    (section3_sampled_product_residual_fixed_variance_bound
      S μ hsec3 i (fun x : DecisionSpace d => x))

/-- The scalar inequality projection of
`theorem1_random_iterate_noise_second_moment_integrable_and_le`. -/
private theorem theorem1_random_iterate_noise_second_moment_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) (i : ℕ) :
    ∫ ω,
        ‖stochasticGradient S (iterate S i ω) (S.sample i ω) -
          objectiveGradient S (iterate S i ω)‖ ^ 2 ∂μ ≤ σ ^ 2 :=
  (theorem1_random_iterate_noise_second_moment_integrable_and_le
    S μ hsec3 i).2

/-- Finite-window form of Theorem 1 proof step 25's noise variance bound.

This consumes the random-iterate variance transfer at exactly the paper's
output window `x_1, ..., x_T`, matching `theorem1TerminalCumulativeGradientNormSq`
rather than the old one-step-too-late generated denominator. -/
private theorem theorem1_noise_second_moment_window_integrable_and_le
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) :
    (∀ i : Fin T,
      Integrable
        (fun ω =>
          ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
            objectiveGradient S (iterate S i.val ω)‖ ^ 2) μ) ∧
      Finset.sum Finset.univ
        (fun i : Fin T =>
          ∫ ω,
            ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
              objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ) ≤
        (T : ℝ) * σ ^ 2 := by
  classical
  constructor
  · intro i
    exact
      (theorem1_random_iterate_noise_second_moment_integrable_and_le
        S μ hsec3 i.val).1
  · calc
      Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ)
          ≤ Finset.sum Finset.univ (fun _i : Fin T => σ ^ 2) := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              exact theorem1_random_iterate_noise_second_moment_le
                S μ hsec3 i.val
      _ = (T : ℝ) * σ ^ 2 := by
              simp

/-- For the nonnegative branch used by Theorem 1 Jensen steps, `x^(1/3)` is
dominated by the integrable affine majorant `x + 1`. -/
private theorem theorem1_rpow_one_third_le_self_add_one_of_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    Real.rpow x ((1 : ℝ) / 3) ≤ x + 1 := by
  exact rpow_le_self_add_one_of_nonneg_of_mem_Icc hx (by norm_num)

/-- Noise Jensen bridge for Theorem 1 proof step 25.

This is the exact source subgoal after the finite-window variance bridge:
`x ↦ x^(1/3)` is the paper's concave map on `[0,∞)`, and Mathlib's integral
Jensen terminal is `ConcaveOn.le_map_integral`. -/
private theorem _voucher_step_theorem1_noise_rpow_jensen_bound_48
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hnoise_window :
      (∀ i : Fin T,
        Integrable
          (fun ω =>
            ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
              objectiveGradient S (iterate S i.val ω)‖ ^ 2) μ) ∧
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ) ≤
          (T : ℝ) * σ ^ 2) :
    ∫ ω,
        theorem1M S T L σ fStar *
          Real.rpow
            (S.w +
              2 *
                Finset.sum Finset.univ
                  (fun i : Fin T =>
                    ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                      objectiveGradient S (iterate S i.val ω)‖ ^ 2))
            ((1 : ℝ) / 3) ∂μ ≤
      theorem1M S T L σ fStar *
        Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) := by
  classical
  let noiseSq : Ω → ℝ := fun ω =>
    Finset.sum Finset.univ
      (fun i : Fin T =>
        ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
          objectiveGradient S (iterate S i.val ω)‖ ^ 2)
  let base : Ω → ℝ := fun ω => S.w + 2 * noiseSq ω
  have hnoiseSq_int : Integrable noiseSq μ := by
    dsimp [noiseSq]
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun i _hi => hnoise_window.1 i)
  have hbase_int : Integrable base μ := by
    dsimp [base]
    exact (integrable_const (c := S.w)).add (hnoiseSq_int.const_mul 2)
  have hbase_nonneg : ∀ᵐ ω ∂μ, 0 ≤ base ω := by
    filter_upwards with ω
    have hnoise_nonneg : 0 ≤ noiseSq ω := by
      dsimp [noiseSq]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    dsimp [base]
    nlinarith [hM.2.2.2.1, hnoise_nonneg]
  have hbase_integral_le :
      ∫ ω, base ω ∂μ ≤ S.w + 2 * (T : ℝ) * σ ^ 2 := by
    have hsum_integral :
        ∫ ω, noiseSq ω ∂μ =
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ∫ ω,
                ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                  objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ) := by
      dsimp [noiseSq]
      exact MeasureTheory.integral_finset_sum Finset.univ
        (fun i _hi => hnoise_window.1 i)
    calc
      ∫ ω, base ω ∂μ = S.w + 2 * ∫ ω, noiseSq ω ∂μ := by
        dsimp [base]
        rw [MeasureTheory.integral_add
          (integrable_const (c := S.w)) (hnoiseSq_int.const_mul 2)]
        rw [MeasureTheory.integral_const_mul]
        simp [MeasureTheory.integral_const, probReal_univ]
      _ ≤ S.w + 2 * ((T : ℝ) * σ ^ 2) := by
        nlinarith [hnoise_window.2, hsum_integral]
      _ = S.w + 2 * (T : ℝ) * σ ^ 2 := by ring
  have hJensen :=
    integral_rpow_le_rpow_of_integrable_nonneg_of_integral_le
      μ hbase_int hbase_nonneg (by norm_num : ((1 : ℝ) / 3) ∈ Set.Icc 0 1)
      hbase_integral_le
  calc
    ∫ ω,
        theorem1M S T L σ fStar *
          Real.rpow
            (S.w +
              2 *
                Finset.sum Finset.univ
                  (fun i : Fin T =>
                    ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                      objectiveGradient S (iterate S i.val ω)‖ ^ 2))
            ((1 : ℝ) / 3) ∂μ =
        theorem1M S T L σ fStar *
          ∫ ω, Real.rpow (base ω) ((1 : ℝ) / 3) ∂μ := by
            dsimp [base, noiseSq]
            rw [MeasureTheory.integral_const_mul]
    _ ≤ theorem1M S T L σ fStar *
          Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left hJensen hM.2.2.2.2

/-- Square-root/rpow normalization used in Theorem 1 proof step 26.

For a nonnegative square-sum `x`, the paper's
`(sqrt x)^(2/3)` is exactly `x^(1/3)`.  This is a Mathlib-real-power
normalization bridge, not a new scalar assumption. -/
private theorem theorem1_sqrt_rpow_two_thirds_eq_rpow_one_third
    {x : ℝ} (hx : 0 ≤ x) :
    Real.rpow (Real.sqrt x) ((2 : ℝ) / 3) =
      Real.rpow x ((1 : ℝ) / 3) := by
  rw [Real.sqrt_eq_rpow]
  convert (Real.rpow_mul hx ((1 : ℝ) / 2) ((2 : ℝ) / 3)).symm using 2
  norm_num

/-- Deterministic-gradient Jensen bridge for Theorem 1 proof step 26.

This is the exact source subgoal moving the exponent `2/3` outside the
expectation of `sqrt(∑ ‖∇F(x_t)‖²)`.  The checked terminal APIs are
`Real.concaveOn_rpow` and `ConcaveOn.le_map_integral`. -/
private theorem _voucher_step_theorem1_gradient_rpow_jensen_bound_48
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hM : theorem1MScalarBoundary S T L σ fStar) :
    ∫ ω,
        Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
          Real.rpow
            (Finset.sum Finset.univ
              (fun i : Fin T =>
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
            ((1 : ℝ) / 3) ∂μ ≤
      Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
        Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) := by
  classical
  have hconc :
      ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => Real.rpow x ((2 : ℝ) / 3)) := by
    simpa using
      (Real.concaveOn_rpow
        (p := ((2 : ℝ) / 3)) (by norm_num) (by norm_num))
  have hcont :
      ContinuousOn (fun x : ℝ => Real.rpow x ((2 : ℝ) / 3)) (Set.Ici (0 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 3)).continuousOn
  have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
  have hroot_int :
      Integrable
        (fun ω =>
          Real.sqrt
            (Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))) μ :=
    theorem1_expected_root_gradient_norm_sq_sum_integrable S μ T hsec3
  have hJensenAPI :=
    ConcaveOn.le_map_integral
      (μ := μ)
      (s := Set.Ici (0 : ℝ))
      (f := fun ω : Ω =>
        Real.sqrt
          (Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)))
      (g := fun x : ℝ => Real.rpow x ((2 : ℝ) / 3))
      hconc hcont hclosed
  -- Remaining exact Jensen leaf: rewrite
  -- `(sqrt gradSum)^(2/3)` to `gradSum^(1/3)`, then apply `hJensenAPI`
  -- and multiply by the nonnegative scalar `2^(1/3) * M`.
  have hM_nonneg : 0 ≤ theorem1M S T L σ fStar := hM.2.2.2.2
  have hsumsq_nonneg :
      ∀ ω,
        0 ≤
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
    intro ω
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
  have hroot_pow_rewrite :
      (fun ω =>
          Real.rpow
            (Real.sqrt
              (Finset.sum Finset.univ
                (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)))
            ((2 : ℝ) / 3)) =
        (fun ω =>
          Real.rpow
            (Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
            ((1 : ℝ) / 3)) := by
    funext ω
    exact theorem1_sqrt_rpow_two_thirds_eq_rpow_one_third (hsumsq_nonneg ω)
  have hroot_mem :
      ∀ᵐ ω ∂μ,
        Real.sqrt
            (Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) ∈
          Set.Ici (0 : ℝ) := by
    filter_upwards with ω
    exact Real.sqrt_nonneg _
  have hroot_rpow_int :
      Integrable
        (fun ω =>
          Real.rpow
            (Real.sqrt
              (Finset.sum Finset.univ
                (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)))
            ((2 : ℝ) / 3)) μ := by
    have hroot_rpow_aesm :
        AEStronglyMeasurable
          (fun ω =>
            Real.rpow
              (Real.sqrt
                (Finset.sum Finset.univ
                  (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)))
              ((2 : ℝ) / 3)) μ :=
      (Real.continuous_rpow_const
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 3)).comp_aestronglyMeasurable
          hroot_int.aestronglyMeasurable
    refine Integrable.of_bound hroot_rpow_aesm
      (C :=
        Real.rpow (Real.sqrt ((T : ℝ) * G ^ 2)) ((2 : ℝ) / 3)) ?_
    filter_upwards with ω
    have hsum_bound :
        Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ≤
          (T : ℝ) * G ^ 2 := by
      calc
        Finset.sum Finset.univ
            (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) ≤
            Finset.sum Finset.univ (fun _i : Fin T => G ^ 2) := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              exact
                pow_le_pow_left₀ (norm_nonneg _)
                  (section3_objectiveGradient_norm_le S μ hsec3 0
                    (iterate S i.val ω)) 2
        _ = (T : ℝ) * G ^ 2 := by
              simp
    have hroot_le :
        Real.sqrt
            (Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)) ≤
          Real.sqrt ((T : ℝ) * G ^ 2) :=
      Real.sqrt_le_sqrt hsum_bound
    have hpow_le :
        Real.rpow
            (Real.sqrt
              (Finset.sum Finset.univ
                (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)))
            ((2 : ℝ) / 3) ≤
          Real.rpow (Real.sqrt ((T : ℝ) * G ^ 2)) ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) hroot_le (by norm_num)
    simpa [Real.norm_of_nonneg
      (Real.rpow_nonneg (Real.sqrt_nonneg _) ((2 : ℝ) / 3))] using hpow_le
  have hJensen :
      ∫ ω,
          Real.rpow
            (Real.sqrt
              (Finset.sum Finset.univ
                (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)))
            ((2 : ℝ) / 3) ∂μ ≤
        Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) := by
    simpa [Function.comp_def, theorem1ExpectedRootGradientNormSqSum] using
      hJensenAPI hroot_mem hroot_int hroot_rpow_int
  have hroot_rpow_one_third_int :
      Integrable
        (fun ω =>
          Real.rpow
            (Finset.sum Finset.univ
              (fun i : Fin T =>
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
            ((1 : ℝ) / 3)) μ := by
    exact hroot_rpow_int.congr (Filter.Eventually.of_forall fun ω => by
      exact congrFun hroot_pow_rewrite ω)
  let C := Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((1 : ℝ) / 3))
      hM_nonneg
  calc
    ∫ ω,
        Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
          Real.rpow
            (Finset.sum Finset.univ
              (fun i : Fin T =>
                ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
            ((1 : ℝ) / 3) ∂μ
        = C *
            ∫ ω,
              Real.rpow
                (Finset.sum Finset.univ
                  (fun i : Fin T =>
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
                ((1 : ℝ) / 3) ∂μ := by
          dsimp [C]
          rw [MeasureTheory.integral_const_mul]
    _ = C *
            ∫ ω,
              Real.rpow
                (Real.sqrt
                  (Finset.sum Finset.univ
                    (fun i : Fin T =>
                      ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)))
                ((2 : ℝ) / 3) ∂μ := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
            exact (congrFun hroot_pow_rewrite ω).symm)
    _ ≤ C *
          Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left hJensen hC_nonneg
    _ =
        Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
          Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) := by
          simp [C, mul_assoc]

/-- Exact-head compiler-grounded attempt for Theorem 1 proof steps 23-26.

The proof exposes the finite-window pointwise split, applies it through
integral monotonicity, and delegates only the two source Jensen transports to
the named `_voucher_step_*_48` leaves above. -/
private theorem _voucher_attempt_theorem1_root_sum_noise_split_48
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hT : 0 < T)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hwith_sampled :
      theorem1ExpectedRootGradientNormSqSum S μ T ^ 2 ≤
        ∫ ω,
          theorem1M S T L σ fStar *
            Real.rpow
              (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
              ((1 : ℝ) / 3) ∂μ) :
    theorem1ExpectedRootGradientNormSqSum S μ T ^ 2 ≤
      theorem1M S T L σ fStar *
          Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) +
        Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
          Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) := by
  classical
  have hM_nonneg : 0 ≤ theorem1M S T L σ fStar := hM.2.2.2.2
  have hnoise_window :
      (∀ i : Fin T,
        Integrable
          (fun ω =>
            ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
              objectiveGradient S (iterate S i.val ω)‖ ^ 2) μ) ∧
        Finset.sum Finset.univ
          (fun i : Fin T =>
            ∫ ω,
              ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                objectiveGradient S (iterate S i.val ω)‖ ^ 2 ∂μ) ≤
          (T : ℝ) * σ ^ 2 :=
    theorem1_noise_second_moment_window_integrable_and_le S μ T hsec3
  have hpoint_split :
      ∀ᵐ ω ∂μ,
        theorem1TerminalCumulativeGradientNormSq S T ω ≤
          2 *
              Finset.sum Finset.univ
                (fun i : Fin T =>
                  ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                    objectiveGradient S (iterate S i.val ω)‖ ^ 2) +
            2 *
              Finset.sum Finset.univ
                (fun i : Fin T =>
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) := by
    filter_upwards with ω
    exact theorem1TerminalCumulativeGradientNormSq_pointwise_noise_split S T hT ω
  have hpoint_rpow_split :
      ∀ᵐ ω ∂μ,
        Real.rpow
            (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
            ((1 : ℝ) / 3) ≤
          Real.rpow
              (S.w +
                2 *
                  Finset.sum Finset.univ
                    (fun i : Fin T =>
                      ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                        objectiveGradient S (iterate S i.val ω)‖ ^ 2))
              ((1 : ℝ) / 3) +
            Real.rpow 2 ((1 : ℝ) / 3) *
              Real.rpow
                (Finset.sum Finset.univ
                  (fun i : Fin T =>
                    ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
                ((1 : ℝ) / 3) := by
    filter_upwards [hpoint_split] with ω hsplitω
    have hterminal_nonneg :
        0 ≤ theorem1TerminalCumulativeGradientNormSq S T ω := by
      simp [theorem1TerminalCumulativeGradientNormSq]
      exact cumulativeGradientNormSq_nonneg S
        (theorem1TerminalGradientIndex T) ω
    have hnoise_nonneg :
        0 ≤
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                objectiveGradient S (iterate S i.val ω)‖ ^ 2) :=
      Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    have hgrad_nonneg :
        0 ≤
          Finset.sum Finset.univ
            (fun i : Fin T =>
              ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) :=
      Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    exact
      theorem1_terminal_rpow_pointwise_noise_grad_split
        hM.2.2.2.1 hterminal_nonneg hnoise_nonneg hgrad_nonneg hsplitω
  -- Remaining source-route leaf: conditional noise control at random iterates
  -- has now been consumed in finite-window form, and the pointwise cube-root
  -- split above is proved against the canonical terminal denominator.  The
  -- remaining exact leaf is Jensen/integrability transport from
  -- `hpoint_rpow_split` and `hnoise_window` to the displayed expectation bound.
  have hnoise_jensen :
      ∫ ω,
          theorem1M S T L σ fStar *
            Real.rpow
              (S.w +
                2 *
                  Finset.sum Finset.univ
                    (fun i : Fin T =>
                      ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
                        objectiveGradient S (iterate S i.val ω)‖ ^ 2))
              ((1 : ℝ) / 3) ∂μ ≤
        theorem1M S T L σ fStar *
          Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) :=
    _voucher_step_theorem1_noise_rpow_jensen_bound_48 S μ T hsec3 hM hnoise_window
  have hgrad_jensen :
      ∫ ω,
          Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
            Real.rpow
              (Finset.sum Finset.univ
                (fun i : Fin T =>
                  ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2))
              ((1 : ℝ) / 3) ∂μ ≤
        Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
          Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) :=
    _voucher_step_theorem1_gradient_rpow_jensen_bound_48 S μ T hsec3 hM
  let M : ℝ := theorem1M S T L σ fStar
  let terminalIntegrand : Ω → ℝ := fun ω =>
    M *
      Real.rpow
        (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
        ((1 : ℝ) / 3)
  let noiseSq : Ω → ℝ := fun ω =>
    Finset.sum Finset.univ
      (fun i : Fin T =>
        ‖stochasticGradient S (iterate S i.val ω) (S.sample i.val ω) -
          objectiveGradient S (iterate S i.val ω)‖ ^ 2)
  let gradSq : Ω → ℝ := fun ω =>
    Finset.sum Finset.univ
      (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2)
  let noiseIntegrand : Ω → ℝ := fun ω =>
    M * Real.rpow (S.w + 2 * noiseSq ω) ((1 : ℝ) / 3)
  let gradIntegrand : Ω → ℝ := fun ω =>
    Real.rpow 2 ((1 : ℝ) / 3) * M *
      Real.rpow (gradSq ω) ((1 : ℝ) / 3)
  have hterminal_int : Integrable terminalIntegrand μ := by
    have hcum_prefix :=
      lemma3_cumulativeGradientNormSq_prefixAEMeasurable S μ hsec3
        (theorem1TerminalGradientIndex T)
    have hcum_aesm :
        AEStronglyMeasurable
          (theorem1TerminalCumulativeGradientNormSq S T) μ := by
      simpa [theorem1TerminalCumulativeGradientNormSq] using
        (prefixAEMeasurable.aemeasurable S μ hsec3 hcum_prefix).aestronglyMeasurable
    have hbase_aesm :
        AEStronglyMeasurable
          (fun ω => S.w + theorem1TerminalCumulativeGradientNormSq S T ω) μ :=
      (aestronglyMeasurable_const.add hcum_aesm)
    have hrpow_aesm :
        AEStronglyMeasurable
          (fun ω =>
            Real.rpow
              (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
              ((1 : ℝ) / 3)) μ :=
      (Real.continuous_rpow_const
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)).comp_aestronglyMeasurable
          hbase_aesm
    rcases lemma3_cumulativeGradientNormSq_eventually_le
        S μ hsec3 (theorem1TerminalGradientIndex T) with
      ⟨R, hR_nonneg, hR_bound⟩
    have hbound :
        ∀ᵐ ω ∂μ,
          ‖terminalIntegrand ω‖ ≤
            M * Real.rpow (S.w + R) ((1 : ℝ) / 3) := by
      filter_upwards [hR_bound] with ω hRω
      have hbase_nonneg :
          0 ≤ S.w + theorem1TerminalCumulativeGradientNormSq S T ω := by
        exact add_nonneg hM.2.2.2.1
          (by
            simpa [theorem1TerminalCumulativeGradientNormSq] using
              cumulativeGradientNormSq_nonneg S (theorem1TerminalGradientIndex T) ω)
      have hbase_le :
          S.w + theorem1TerminalCumulativeGradientNormSq S T ω ≤ S.w + R := by
        simpa [theorem1TerminalCumulativeGradientNormSq] using
          add_le_add_left hRω S.w
      have htarget_nonneg : 0 ≤ S.w + R :=
        add_nonneg hM.2.2.2.1 hR_nonneg
      have hpow_le :
          Real.rpow
              (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
              ((1 : ℝ) / 3) ≤
            Real.rpow (S.w + R) ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow hbase_nonneg hbase_le (by norm_num)
      have hpow_nonneg :
          0 ≤
            Real.rpow
              (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
              ((1 : ℝ) / 3) :=
        Real.rpow_nonneg hbase_nonneg ((1 : ℝ) / 3)
      have htarget_pow_nonneg :
          0 ≤ Real.rpow (S.w + R) ((1 : ℝ) / 3) :=
        Real.rpow_nonneg htarget_nonneg ((1 : ℝ) / 3)
      have hmul_le :
          M *
              Real.rpow
                (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
                ((1 : ℝ) / 3) ≤
            M * Real.rpow (S.w + R) ((1 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left hpow_le (by simpa [M] using hM_nonneg)
      calc
        ‖terminalIntegrand ω‖ =
            M *
              Real.rpow
                (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
                ((1 : ℝ) / 3) := by
          change ‖M *
              Real.rpow
                (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
                ((1 : ℝ) / 3)‖ =
            M *
              Real.rpow
                (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
                ((1 : ℝ) / 3)
          rw [norm_mul, Real.norm_of_nonneg (by simpa [M] using hM_nonneg),
            Real.norm_of_nonneg hpow_nonneg]
        _ ≤ M * Real.rpow (S.w + R) ((1 : ℝ) / 3) := hmul_le
    exact Integrable.of_bound
      ((aestronglyMeasurable_const.mul hrpow_aesm))
      (C := M * Real.rpow (S.w + R) ((1 : ℝ) / 3)) hbound
  have hnoise_int : Integrable noiseIntegrand μ := by
    have hnoiseSq_int : Integrable noiseSq μ := by
      dsimp [noiseSq]
      exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _hi => hnoise_window.1 i)
    have hbase_int : Integrable (fun ω => S.w + 2 * noiseSq ω) μ := by
      exact (integrable_const (c := S.w)).add (hnoiseSq_int.const_mul 2)
    have hbase_nonneg : ∀ᵐ ω ∂μ, 0 ≤ S.w + 2 * noiseSq ω := by
      filter_upwards with ω
      have hnoise_nonneg : 0 ≤ noiseSq ω := by
        dsimp [noiseSq]
        exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
      nlinarith [hM.2.2.2.1, hnoise_nonneg]
    have hrpow_aesm :
        AEStronglyMeasurable
          (fun ω => Real.rpow (S.w + 2 * noiseSq ω) ((1 : ℝ) / 3)) μ :=
      (Real.continuous_rpow_const
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)).comp_aestronglyMeasurable
          hbase_int.aestronglyMeasurable
    have hrpow_int :
        Integrable
          (fun ω => Real.rpow (S.w + 2 * noiseSq ω) ((1 : ℝ) / 3)) μ := by
      have hmajorant_int :
          Integrable (fun ω => S.w + 2 * noiseSq ω + 1) μ :=
        hbase_int.add (integrable_const (c := (1 : ℝ)))
      refine hmajorant_int.mono' hrpow_aesm ?_
      filter_upwards [hbase_nonneg] with ω hbaseω
      have hpow_nonneg :
          0 ≤ Real.rpow (S.w + 2 * noiseSq ω) ((1 : ℝ) / 3) :=
        Real.rpow_nonneg hbaseω ((1 : ℝ) / 3)
      have hpow_le :
          Real.rpow (S.w + 2 * noiseSq ω) ((1 : ℝ) / 3) ≤
            S.w + 2 * noiseSq ω + 1 :=
        theorem1_rpow_one_third_le_self_add_one_of_nonneg hbaseω
      rwa [Real.norm_of_nonneg hpow_nonneg]
    simpa [noiseIntegrand, M] using hrpow_int.const_mul M
  have hgrad_int : Integrable gradIntegrand μ := by
    have hgrad_norm_int :
        ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ :=
      theorem1_output_window_integrability_from_G_lipschitz S μ hsec3 T
    have hgradSq_int : Integrable gradSq μ := by
      dsimp [gradSq]
      refine MeasureTheory.integrable_finset_sum Finset.univ ?_
      intro i _hi
      have hsq_aesm :
          AEStronglyMeasurable
            (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2) μ :=
        (hgrad_norm_int i).aestronglyMeasurable.pow 2
      refine Integrable.of_bound hsq_aesm (C := G ^ 2) ?_
      filter_upwards with ω
      have hnorm_le :
          ‖objectiveGradient S (iterate S i.val ω)‖ ≤ G :=
        section3_objectiveGradient_norm_le S μ hsec3 0
          (iterate S i.val ω)
      have hsq_le :
          ‖objectiveGradient S (iterate S i.val ω)‖ ^ 2 ≤ G ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
      simpa [Real.norm_of_nonneg (sq_nonneg _)] using hsq_le
    have hgradSq_nonneg : ∀ᵐ ω ∂μ, 0 ≤ gradSq ω := by
      filter_upwards with ω
      dsimp [gradSq]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    have hrpow_aesm :
        AEStronglyMeasurable
          (fun ω => Real.rpow (gradSq ω) ((1 : ℝ) / 3)) μ :=
      (Real.continuous_rpow_const
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)).comp_aestronglyMeasurable
          hgradSq_int.aestronglyMeasurable
    have hrpow_int :
        Integrable (fun ω => Real.rpow (gradSq ω) ((1 : ℝ) / 3)) μ := by
      have hmajorant_int : Integrable (fun ω => gradSq ω + 1) μ :=
        hgradSq_int.add (integrable_const (c := (1 : ℝ)))
      refine hmajorant_int.mono' hrpow_aesm ?_
      filter_upwards [hgradSq_nonneg] with ω hgradω
      have hpow_nonneg :
          0 ≤ Real.rpow (gradSq ω) ((1 : ℝ) / 3) :=
        Real.rpow_nonneg hgradω ((1 : ℝ) / 3)
      have hpow_le :
          Real.rpow (gradSq ω) ((1 : ℝ) / 3) ≤ gradSq ω + 1 :=
        theorem1_rpow_one_third_le_self_add_one_of_nonneg hgradω
      rwa [Real.norm_of_nonneg hpow_nonneg]
    simpa [gradIntegrand, M, mul_assoc] using
      hrpow_int.const_mul (Real.rpow 2 ((1 : ℝ) / 3) * M)
  have hright_int : Integrable (fun ω => noiseIntegrand ω + gradIntegrand ω) μ :=
    hnoise_int.add hgrad_int
  have hpoint_integrand_split :
      ∀ᵐ ω ∂μ,
        terminalIntegrand ω ≤ noiseIntegrand ω + gradIntegrand ω := by
    filter_upwards [hpoint_rpow_split] with ω hsplitω
    have hmul :=
      mul_le_mul_of_nonneg_left hsplitω (by simpa [M] using hM_nonneg)
    simpa [terminalIntegrand, noiseIntegrand, gradIntegrand, noiseSq, gradSq,
      M, mul_add, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsplit_integral :
      ∫ ω, terminalIntegrand ω ∂μ ≤
        ∫ ω, noiseIntegrand ω + gradIntegrand ω ∂μ :=
    integral_mono_ae hterminal_int hright_int hpoint_integrand_split
  have hsplit_integral' :
      ∫ ω, terminalIntegrand ω ∂μ ≤
        ∫ ω, noiseIntegrand ω ∂μ + ∫ ω, gradIntegrand ω ∂μ := by
    calc
      ∫ ω, terminalIntegrand ω ∂μ ≤
          ∫ ω, noiseIntegrand ω + gradIntegrand ω ∂μ := hsplit_integral
      _ = ∫ ω, noiseIntegrand ω ∂μ + ∫ ω, gradIntegrand ω ∂μ := by
          rw [MeasureTheory.integral_add hnoise_int hgrad_int]
  have hterminal_bound :
      ∫ ω, terminalIntegrand ω ∂μ ≤
        M * Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) +
          Real.rpow 2 ((1 : ℝ) / 3) * M *
            Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) := by
    have hnoise_jensen' :
        ∫ ω, noiseIntegrand ω ∂μ ≤
          M * Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) := by
      simpa [noiseIntegrand, noiseSq, M] using hnoise_jensen
    have hgrad_jensen' :
        ∫ ω, gradIntegrand ω ∂μ ≤
          Real.rpow 2 ((1 : ℝ) / 3) * M *
            Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) := by
      simpa [gradIntegrand, gradSq, M] using hgrad_jensen
    exact le_trans hsplit_integral' (add_le_add hnoise_jensen' hgrad_jensen')
  exact le_trans hwith_sampled (by
    simpa [terminalIntegrand, M] using hterminal_bound)

/-- Theorem 1 proof steps 23-26: split sampled gradients into objective-gradient
and noise parts, use the variance bound, and move fractional powers through
expectations by concavity. -/
private theorem theorem1_root_sum_noise_split
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hT : 0 < T)
    (hgenerated : generatedStepsizeQuotientBoundary S)
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hwith_sampled :
      theorem1ExpectedRootGradientNormSqSum S μ T ^ 2 ≤
        ∫ ω,
          theorem1M S T L σ fStar *
            Real.rpow
              (S.w + theorem1TerminalCumulativeGradientNormSq S T ω)
              ((1 : ℝ) / 3) ∂μ) :
    theorem1ExpectedRootGradientNormSqSum S μ T ^ 2 ≤
      theorem1M S T L σ fStar *
          Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) +
        Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
          Real.rpow (theorem1ExpectedRootGradientNormSqSum S μ T) ((2 : ℝ) / 3) := by
  exact
    _voucher_attempt_theorem1_root_sum_noise_split_48
      S μ T hsec3 hT hgenerated hM hwith_sampled

/-- Theorem 1 proof steps 27-31: solve the scalar inequality for
`X = 𝔼[sqrt(∑ ‖∇F(x_t)‖²)]` and expose the two source alternatives consumed by
the final average-gradient step. -/
private theorem theorem1_scalar_X_raw_case_split
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ)
    {X : ℝ}
    (hscalar :
      X ^ 2 ≤
        theorem1M S T L σ fStar *
            Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) +
          Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
            Real.rpow X ((2 : ℝ) / 3)) :
    X ^ 2 ≤
        2 * (theorem1M S T L σ fStar *
          Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3)) ∨
      X ^ 2 ≤
        2 * (Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
          Real.rpow X ((2 : ℝ) / 3)) := by
  classical
  let A :=
    theorem1M S T L σ fStar *
      Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3)
  let B :=
    Real.rpow 2 ((1 : ℝ) / 3) * theorem1M S T L σ fStar *
      Real.rpow X ((2 : ℝ) / 3)
  have hscalar' : X ^ 2 ≤ A + B := by
    simpa [A, B] using hscalar
  by_cases hA : X ^ 2 ≤ 2 * A
  · exact Or.inl (by simpa [A] using hA)
  · have hAlt : X ^ 2 ≤ 2 * B := by
      have hA_lt : 2 * A < X ^ 2 := lt_of_not_ge hA
      linarith
    exact Or.inr (by simpa [B] using hAlt)

/-- Theorem 1 scalar proof steps 28-30, second raw alternative.

The raw second branch
`X² ≤ 2 * (2^(1/3) * M * X^(2/3))` algebraically solves to
`X ≤ 2M^(3/4)` on the nonnegative branch.  This is the paper's second
case in lines 551-554 and is independent of the final `√T` normalization. -/
private theorem theorem1_scalar_X_second_case_bound
    {M X : ℝ} (hM_nonneg : 0 ≤ M) (hX_nonneg : 0 ≤ X)
    (hsecond :
      X ^ 2 ≤
        2 * (Real.rpow 2 ((1 : ℝ) / 3) * M *
          Real.rpow X ((2 : ℝ) / 3))) :
    X ≤ 2 * Real.rpow M ((3 : ℝ) / 4) := by
  have hA_nonneg :
      0 ≤ 2 * (Real.rpow 2 ((1 : ℝ) / 3) * M) :=
    mul_nonneg (by norm_num)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hM_nonneg)
  have hbound :
      X ^ 2 ≤
        (2 * (Real.rpow 2 ((1 : ℝ) / 3) * M)) *
          Real.rpow X ((2 : ℝ) / 3) := by
    simpa only [mul_assoc] using hsecond
  have hgeneral := le_rpow_three_fourths_of_sq_le_mul_rpow_two_thirds
    hA_nonneg hX_nonneg hbound
  have hcoef :
      Real.rpow (2 * (Real.rpow 2 ((1 : ℝ) / 3) * M))
          ((3 : ℝ) / 4) =
        2 * Real.rpow M ((3 : ℝ) / 4) := by
    calc
      Real.rpow (2 * (Real.rpow 2 ((1 : ℝ) / 3) * M))
            ((3 : ℝ) / 4) =
          Real.rpow 2 ((3 : ℝ) / 4) *
            Real.rpow (Real.rpow 2 ((1 : ℝ) / 3) * M)
              ((3 : ℝ) / 4) := by
        simpa using Real.mul_rpow (z := (3 : ℝ) / 4)
          (by norm_num : (0 : ℝ) ≤ 2)
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hM_nonneg)
      _ = Real.rpow 2 ((3 : ℝ) / 4) *
            (Real.rpow (Real.rpow 2 ((1 : ℝ) / 3)) ((3 : ℝ) / 4) *
              Real.rpow M ((3 : ℝ) / 4)) := by
        congr 1
        simpa using Real.mul_rpow (z := (3 : ℝ) / 4)
          (Real.rpow_nonneg (by norm_num) _) hM_nonneg
      _ = (Real.rpow 2 ((3 : ℝ) / 4) *
              Real.rpow 2 (((1 : ℝ) / 3) * ((3 : ℝ) / 4))) *
            Real.rpow M ((3 : ℝ) / 4) := by
        rw [show
          Real.rpow (Real.rpow 2 ((1 : ℝ) / 3)) ((3 : ℝ) / 4) =
              Real.rpow 2 (((1 : ℝ) / 3) * ((3 : ℝ) / 4)) by
            simpa using (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
              ((1 : ℝ) / 3) ((3 : ℝ) / 4)).symm]
        ring
      _ = 2 * Real.rpow M ((3 : ℝ) / 4) := by
        congr 1
        have htwoadd := Real.rpow_add (by norm_num : (0 : ℝ) < 2)
          ((3 : ℝ) / 4) (((1 : ℝ) / 3) * ((3 : ℝ) / 4))
        norm_num at htwoadd ⊢
        exact htwoadd.symm
  simpa only [hcoef] using hgeneral

/-- The source-derived lower bound on the scalar `M` used in Theorem 1.

This is the missing invariant exposed by the parameterized source route: after
unfolding the displayed `M`, the initial objective gap is nonnegative by the
Section 3 finite lower bound, and the logarithmic term is nonnegative.  Hence
`M` dominates the stochastic-noise coefficient term. -/
private theorem theorem1M_noise_term_le_of_source_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (b L G σ fStar : ℝ)
    (hb : 0 < b)
    (hsec3 : Section3Assumptions (withTheorem1Parameters S b G L) μ L G σ fStar)
    (hscalarBoundary : theorem1ScalarBoundary S T b L G σ fStar) :
    let ST := withTheorem1Parameters S b G L
    Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * ST.k ^ 2) ≤
      theorem1M ST T L σ fStar := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hk_pos : 0 < ST.k := by
    simpa [ST] using theorem1_parameterized_k_pos S T hb hscalarBoundary
  have hL_pos : 0 < L := hscalarBoundary.1.2.1
  have hgap_nonneg : 0 ≤ ST.objectiveValue ST.x₁ - fStar := by
    have hlower : fStar ≤ ST.objectiveValue ST.x₁ := by
      exact hsec3.finite_lower_bound.1 ⟨ST.x₁, rfl⟩
    linarith
  have hfirst_nonneg :
      0 ≤ (8 / ST.k) * (ST.objectiveValue ST.x₁ - fStar) := by
    exact mul_nonneg (div_nonneg (by norm_num) (le_of_lt hk_pos)) hgap_nonneg
  have hnoise_nonneg :
      0 ≤ Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * ST.k ^ 2) := by
    have hw_nonneg : 0 ≤ ST.w := by
      simpa [ST] using hscalarBoundary.2.2.1.2.2.2.1
    have hnum_nonneg :
        0 ≤ Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hw_nonneg _) (sq_nonneg σ)
    have hden_nonneg : 0 ≤ 4 * L ^ 2 * ST.k ^ 2 := by
      positivity
    exact div_nonneg hnum_nonneg hden_nonneg
  have hlog_nonneg : 0 ≤ Real.log (T + 2 : ℝ) := by
    have hT_nonneg : (0 : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast Nat.zero_le T
    exact Real.log_nonneg (by nlinarith)
  have hlast_nonneg :
      0 ≤ ST.k ^ 2 * ST.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) := by
    have hcoeff_nonneg : 0 ≤ ST.k ^ 2 * ST.c ^ 2 / (2 * L ^ 2) := by
      have hnum_nonneg : 0 ≤ ST.k ^ 2 * ST.c ^ 2 :=
        mul_nonneg (sq_nonneg ST.k) (sq_nonneg ST.c)
      have hden_nonneg : 0 ≤ 2 * L ^ 2 := by positivity
      exact div_nonneg hnum_nonneg hden_nonneg
    exact mul_nonneg hcoeff_nonneg hlog_nonneg
  change
    Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * ST.k ^ 2) ≤
      theorem1M ST T L σ fStar
  rw [theorem1M_eq]
  linarith

/-- The source-derived lower bound on `M` retaining both non-initial terms of
the displayed Theorem 1 formula.

This is stronger than the noise-only invariant above and is the exact scalar
information lost by the false coarse bridges: after unfolding `M`, the initial
objective gap is nonnegative by the Section 3 finite lower bound, while the
noise and logarithmic terms remain in their paper formula shape. -/
private theorem theorem1M_noise_log_terms_le_of_source_boundary
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (b L G σ fStar : ℝ)
    (hb : 0 < b)
    (hsec3 : Section3Assumptions (withTheorem1Parameters S b G L) μ L G σ fStar)
    (hscalarBoundary : theorem1ScalarBoundary S T b L G σ fStar) :
    let ST := withTheorem1Parameters S b G L
    Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * ST.k ^ 2) +
        ST.k ^ 2 * ST.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) ≤
      theorem1M ST T L σ fStar := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hk_pos : 0 < ST.k := by
    simpa [ST] using theorem1_parameterized_k_pos S T hb hscalarBoundary
  have hgap_nonneg : 0 ≤ ST.objectiveValue ST.x₁ - fStar := by
    have hlower : fStar ≤ ST.objectiveValue ST.x₁ := by
      exact hsec3.finite_lower_bound.1 ⟨ST.x₁, rfl⟩
    linarith
  have hfirst_nonneg :
      0 ≤ (8 / ST.k) * (ST.objectiveValue ST.x₁ - fStar) := by
    exact mul_nonneg (div_nonneg (by norm_num) (le_of_lt hk_pos)) hgap_nonneg
  change
    Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * ST.k ^ 2) +
        ST.k ^ 2 * ST.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) ≤
      theorem1M ST T L σ fStar
  rw [theorem1M_eq]
  linarith

/-- Transparent derivation of the displayed `M` scalar boundary for the
Theorem 1 parameterized setup. -/
private theorem theorem1M_scalar_boundary_of_positive
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (b L G σ fStar : ℝ)
    (hb : 0 < b) (hGpos : 0 < G) (hLpos : 0 < L)
    (hsec3 : Section3Assumptions (withTheorem1Parameters S b G L) μ L G σ fStar) :
    theorem1MScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hk_pos : 0 < ST.k := by
    simpa [ST] using theorem1_parameterized_k_pos_of_positive S hb hGpos hLpos
  have hk_ne : ST.k ≠ 0 := ne_of_gt hk_pos
  have h4_ne : 4 * L ^ 2 * ST.k ^ 2 ≠ 0 := by
    have h4_pos : 0 < 4 * L ^ 2 * ST.k ^ 2 := by positivity
    exact ne_of_gt h4_pos
  have h2_ne : 2 * L ^ 2 ≠ 0 := by
    have h2_pos : 0 < 2 * L ^ 2 := by positivity
    exact ne_of_gt h2_pos
  have hw_nonneg : 0 ≤ ST.w := by
    simpa [ST, withTheorem1Parameters] using
      theorem1W_nonneg_of_G_nonneg (b := b) (le_of_lt hGpos)
  have hgap_nonneg : 0 ≤ ST.objectiveValue ST.x₁ - fStar := by
    have hlower : fStar ≤ ST.objectiveValue ST.x₁ :=
      hsec3.finite_lower_bound.1 ⟨ST.x₁, rfl⟩
    linarith
  have hfirst_nonneg :
      0 ≤ (8 / ST.k) * (ST.objectiveValue ST.x₁ - fStar) := by
    exact mul_nonneg (div_nonneg (by norm_num) (le_of_lt hk_pos)) hgap_nonneg
  have hnoise_nonneg :
      0 ≤ Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * ST.k ^ 2) := by
    have hnum_nonneg :
        0 ≤ Real.rpow ST.w ((1 : ℝ) / 3) * σ ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hw_nonneg _) (sq_nonneg σ)
    have hden_nonneg : 0 ≤ 4 * L ^ 2 * ST.k ^ 2 := by positivity
    exact div_nonneg hnum_nonneg hden_nonneg
  have hlog_nonneg : 0 ≤ Real.log (T + 2 : ℝ) := by
    have hT_nonneg : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    exact Real.log_nonneg (by nlinarith)
  have hlast_nonneg :
      0 ≤ ST.k ^ 2 * ST.c ^ 2 / (2 * L ^ 2) * Real.log (T + 2 : ℝ) := by
    have hcoeff_nonneg : 0 ≤ ST.k ^ 2 * ST.c ^ 2 / (2 * L ^ 2) := by
      have hnum_nonneg : 0 ≤ ST.k ^ 2 * ST.c ^ 2 :=
        mul_nonneg (sq_nonneg ST.k) (sq_nonneg ST.c)
      have hden_nonneg : 0 ≤ 2 * L ^ 2 := by positivity
      exact div_nonneg hnum_nonneg hden_nonneg
    exact mul_nonneg hcoeff_nonneg hlog_nonneg
  have hM_nonneg : 0 ≤ theorem1M ST T L σ fStar := by
    rw [theorem1M_eq]
    linarith
  exact ⟨hk_ne, h4_ne, h2_ne, hw_nonneg, hM_nonneg⟩

/-- Transparent derivation of the displayed corrected RHS scalar boundary for
the Theorem 1 parameterized setup. -/
private theorem theorem1RHS_scalar_boundary_of_positive
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (b L G σ fStar : ℝ)
    (hT : 0 < T) (hb : 0 < b) (hGpos : 0 < G) (hLpos : 0 < L)
    (hsigma : 0 ≤ σ)
    (hsec3 : Section3Assumptions (withTheorem1Parameters S b G L) μ L G σ fStar) :
    theorem1RHSScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar := by
  let ST := withTheorem1Parameters S b G L
  have hM :
      theorem1MScalarBoundary ST T L σ fStar := by
    simpa [ST] using
      theorem1M_scalar_boundary_of_positive
        S μ T b L G σ fStar hb hGpos hLpos hsec3
  have hT_real_pos : 0 < (T : ℝ) := by exact_mod_cast hT
  have h2M_nonneg : 0 ≤ 2 * theorem1M ST T L σ fStar := by
    exact mul_nonneg (by norm_num) hM.2.2.2.2
  have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hT_real_pos)
  have hTthird_ne : Real.rpow (T : ℝ) ((1 : ℝ) / 3) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hT_real_pos ((1 : ℝ) / 3))
  exact ⟨h2M_nonneg, hsqrtT_ne, hTthird_ne, hsigma⟩

/-- Scalar obstruction for the current source-root-sum first-case interface.

The live first-case theorem below has more source context than an arbitrary
`X`, but the scalar facts it currently exposes to the final normalization
(`X ≤ √(T G²)`, `w ≥ 2G²`, the raw first alternative, and the second-branch
exclusion) still do not imply the printed RHS.  The concrete values
`T = 100`, `G = 5`, `w = 50`, `M = 10`, `σ = 50`, and `X = 37` satisfy those
facts while violating the normalized conclusion.  This is same-granularity
route evidence that the first-case leaf needs an additional source-derived
scalar invariant, not another wrapper around the same premises. -/
private theorem theorem1_expected_root_sum_first_case_scalar_interface_false :
    ¬ (∀ X M w G σ : ℝ,
      0 ≤ X →
      0 ≤ M →
      0 ≤ w →
      0 ≤ σ →
      2 * G ^ 2 ≤ w →
      X ≤ Real.sqrt ((100 : ℝ) * G ^ 2) →
      ¬ X ≤ 2 * Real.rpow M ((3 : ℝ) / 4) →
      X ^ 2 ≤ 2 * (M * Real.rpow (w + 2 * (100 : ℝ) * σ ^ 2) ((1 : ℝ) / 3)) →
      X / Real.sqrt (100 : ℝ) ≤
        (Real.rpow w ((1 : ℝ) / 6) * Real.sqrt (2 * M) +
            2 * Real.rpow M ((3 : ℝ) / 4)) / Real.sqrt (100 : ℝ) +
          2 * Real.rpow σ ((1 : ℝ) / 3) /
            Real.rpow (100 : ℝ) ((1 : ℝ) / 3)) := by
  intro hsolver
  have h50_sixth_lt :
      Real.rpow (50 : ℝ) ((1 : ℝ) / 6) < (31 : ℝ) / 16 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (50 : ℝ) ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 6)
    have hright_nonneg : 0 ≤ (31 : ℝ) / 16 := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (50 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (50 : ℝ))
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (50 : ℝ) := hpow
      _ < Real.rpow ((31 : ℝ) / 16) (6 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hsqrt20_lt : Real.sqrt (20 : ℝ) < (9 : ℝ) / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (9 : ℝ) / 2)]
    norm_num
  have h10_34_lt :
      Real.rpow (10 : ℝ) ((3 : ℝ) / 4) < (45 : ℝ) / 8 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (10 : ℝ) ((3 : ℝ) / 4) :=
      Real.rpow_nonneg (by norm_num) ((3 : ℝ) / 4)
    have hright_nonneg : 0 ≤ (45 : ℝ) / 8 := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 4)]
    have hpow :
        Real.rpow (Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (10 : ℝ) ^ 3 := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ))
          ((3 : ℝ) / 4) (4 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (10 : ℝ) ^ 3 := hpow
      _ < Real.rpow ((45 : ℝ) / 8) (4 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h50_third_lt :
      Real.rpow (50 : ℝ) ((1 : ℝ) / 3) < (37 : ℝ) / 10 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (50 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    have hright_nonneg : 0 ≤ (37 : ℝ) / 10 := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (50 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (50 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (50 : ℝ) := hpow
      _ < Real.rpow ((37 : ℝ) / 10) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h100_third_gt :
      (37 : ℝ) / 8 < Real.rpow (100 : ℝ) ((1 : ℝ) / 3) := by
    have hleft_nonneg : 0 ≤ (37 : ℝ) / 8 := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (100 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (100 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (100 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (100 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow ((37 : ℝ) / 8) (3 : ℝ) < (100 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (100 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
        hpow.symm
  have h500050_third_gt :
      (69 : ℝ) < Real.rpow (500050 : ℝ) ((1 : ℝ) / 3) := by
    have hleft_nonneg : 0 ≤ (69 : ℝ) := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (500050 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (500050 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (500050 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (500050 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (69 : ℝ) (3 : ℝ) < (500050 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (500050 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
        hpow.symm
  have hfirst :
      (37 : ℝ) ^ 2 ≤
        2 * ((10 : ℝ) *
          Real.rpow ((50 : ℝ) + 2 * (100 : ℝ) * (50 : ℝ) ^ 2)
            ((1 : ℝ) / 3)) := by
    norm_num
    have hprod :
        (1369 : ℝ) <
          2 * (10 * Real.rpow (500050 : ℝ) ((1 : ℝ) / 3)) := by
      nlinarith [h500050_third_gt]
    exact le_of_lt hprod
  have hnot_second :
      ¬ (37 : ℝ) ≤ 2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4) := by
    intro hle
    nlinarith [h10_34_lt]
  have hbad :=
    hsolver 37 10 50 5 50
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2500)])
      hnot_second hfirst
  have hdet_lt :
      Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) /
          Real.sqrt (100 : ℝ) <
        (279 : ℝ) / 320 := by
    have hsqrt100 : Real.sqrt (100 : ℝ) = 10 := by norm_num
    have hmul :
        Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) <
          ((31 : ℝ) / 16) * ((9 : ℝ) / 2) := by
      have hsqrt20' : Real.sqrt (2 * (10 : ℝ)) < (9 : ℝ) / 2 := by
        norm_num
        exact hsqrt20_lt
      calc
        Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ))
            < ((31 : ℝ) / 16) * Real.sqrt (2 * (10 : ℝ)) := by
              exact mul_lt_mul_of_pos_right h50_sixth_lt
                (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * (10 : ℝ)))
        _ < ((31 : ℝ) / 16) * ((9 : ℝ) / 2) := by
              exact mul_lt_mul_of_pos_left hsqrt20' (by norm_num)
    rw [hsqrt100]
    nlinarith
  have hMterm_lt :
      (2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (100 : ℝ) <
        (9 : ℝ) / 8 := by
    have hsqrt100 : Real.sqrt (100 : ℝ) = 10 := by norm_num
    rw [hsqrt100]
    nlinarith [h10_34_lt]
  have hnoise_lt :
      2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3) /
          Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
        (8 : ℝ) / 5 := by
    have hden_pos :
        0 < Real.rpow (100 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < (100 : ℝ)) ((1 : ℝ) / 3)
    have hnum_lt : 2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3) < (37 : ℝ) / 5 := by
      nlinarith [h50_third_lt]
    have hratio_lt :
        (2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) /
            Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
          ((37 : ℝ) / 5) / ((37 : ℝ) / 8) := by
      have hstep1 :
          (2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) /
              Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
            ((37 : ℝ) / 5) /
              Real.rpow (100 : ℝ) ((1 : ℝ) / 3) :=
        div_lt_div_of_pos_right hnum_lt hden_pos
      have hstep2 :
          ((37 : ℝ) / 5) /
              Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
            ((37 : ℝ) / 5) / ((37 : ℝ) / 8) :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) h100_third_gt
      exact lt_trans hstep1 hstep2
    norm_num at hratio_lt ⊢
    exact hratio_lt
  have hRHS_lt :
      (Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) +
          2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) / Real.sqrt (100 : ℝ) +
        2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3) /
          Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
        (37 : ℝ) / 10 := by
    have hsplit :
        (Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) +
            2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) / Real.sqrt (100 : ℝ) =
          Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) /
              Real.sqrt (100 : ℝ) +
            (2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) /
              Real.sqrt (100 : ℝ) := by
      ring
    rw [hsplit]
    nlinarith [hdet_lt, hMterm_lt, hnoise_lt]
  have hRHS_lt' := hRHS_lt
  norm_num at hbad hRHS_lt'
  exact (not_le_of_gt hRHS_lt') hbad

/-- Same-target obstruction for the current average-level final interface.

The live Theorem 1 source frontier has the actual theorem output `A` together
with `A ≤ X / √T` from Cauchy-Schwarz and `A ≤ G` from the finite-average
`G`-bound.  These two average-level facts still do not imply the printed RHS
from the first root-sum branch alone.  The concrete values below satisfy the
same scalar shape at `T = 100`, with `A = 37/10`, while the printed RHS is
strictly smaller than `37/10`. -/
private theorem theorem1_average_level_first_case_scalar_interface_false :
    ¬ (∀ A X M w G σ : ℝ,
      0 ≤ A →
      A ≤ X / Real.sqrt (100 : ℝ) →
      A ≤ G →
      0 ≤ X →
      0 ≤ M →
      0 ≤ w →
      0 ≤ σ →
      2 * G ^ 2 ≤ w →
      X ≤ Real.sqrt ((100 : ℝ) * G ^ 2) →
      X / Real.sqrt (100 : ℝ) ≤
        (Real.sqrt (2 * M) *
            Real.rpow (w + 2 * (100 : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
          Real.sqrt (100 : ℝ) →
      A ≤
        (Real.rpow w ((1 : ℝ) / 6) * Real.sqrt (2 * M) +
            2 * Real.rpow M ((3 : ℝ) / 4)) / Real.sqrt (100 : ℝ) +
          2 * Real.rpow σ ((1 : ℝ) / 3) /
            Real.rpow (100 : ℝ) ((1 : ℝ) / 3)) := by
  intro hsolver
  have h50_sixth_lt :
      Real.rpow (50 : ℝ) ((1 : ℝ) / 6) < (31 : ℝ) / 16 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (50 : ℝ) ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 6)
    have hright_nonneg : 0 ≤ (31 : ℝ) / 16 := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (50 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (50 : ℝ))
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (50 : ℝ) := hpow
      _ < Real.rpow ((31 : ℝ) / 16) (6 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hsqrt20_lt : Real.sqrt (20 : ℝ) < (9 : ℝ) / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (9 : ℝ) / 2)]
    norm_num
  have h10_34_lt :
      Real.rpow (10 : ℝ) ((3 : ℝ) / 4) < (45 : ℝ) / 8 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (10 : ℝ) ((3 : ℝ) / 4) :=
      Real.rpow_nonneg (by norm_num) ((3 : ℝ) / 4)
    have hright_nonneg : 0 ≤ (45 : ℝ) / 8 := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 4)]
    have hpow :
        Real.rpow (Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (10 : ℝ) ^ 3 := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ))
          ((3 : ℝ) / 4) (4 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (10 : ℝ) ^ 3 := hpow
      _ < Real.rpow ((45 : ℝ) / 8) (4 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h50_third_lt :
      Real.rpow (50 : ℝ) ((1 : ℝ) / 3) < (37 : ℝ) / 10 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (50 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    have hright_nonneg : 0 ≤ (37 : ℝ) / 10 := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (50 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (50 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (50 : ℝ) := hpow
      _ < Real.rpow ((37 : ℝ) / 10) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h100_third_gt :
      (37 : ℝ) / 8 < Real.rpow (100 : ℝ) ((1 : ℝ) / 3) := by
    have hleft_nonneg : 0 ≤ (37 : ℝ) / 8 := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (100 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (100 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (100 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (100 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow ((37 : ℝ) / 8) (3 : ℝ) < (100 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (100 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
        hpow.symm
  have h500050_third_gt :
      (69 : ℝ) < Real.rpow (500050 : ℝ) ((1 : ℝ) / 3) := by
    have hleft_nonneg : 0 ≤ (69 : ℝ) := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (500050 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (500050 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (500050 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (500050 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (69 : ℝ) (3 : ℝ) < (500050 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (500050 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
        hpow.symm
  have hB_ge_37 :
      (37 : ℝ) ≤
        Real.sqrt (2 * (10 : ℝ)) *
          Real.rpow (500050 : ℝ) ((1 : ℝ) / 6) := by
    let B : ℝ :=
      Real.sqrt (2 * (10 : ℝ)) *
        Real.rpow (500050 : ℝ) ((1 : ℝ) / 6)
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg (Real.sqrt_nonneg _)
        (Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 6))
    have hB_sq :
        B ^ 2 =
          (2 * (10 : ℝ)) * Real.rpow (500050 : ℝ) ((1 : ℝ) / 3) := by
      have hpow_mul :
          Real.rpow (500050 : ℝ) ((1 : ℝ) / 6) *
              Real.rpow (500050 : ℝ) ((1 : ℝ) / 6) =
            Real.rpow (500050 : ℝ) ((1 : ℝ) / 3) := by
        have hmul :=
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (500050 : ℝ))
            ((1 : ℝ) / 6) (2 : ℝ)
        norm_num at hmul
        simpa [Real.rpow_natCast, pow_two] using hmul.symm
      calc
        B ^ 2 =
            (Real.sqrt (2 * (10 : ℝ)) * Real.sqrt (2 * (10 : ℝ))) *
              (Real.rpow (500050 : ℝ) ((1 : ℝ) / 6) *
                Real.rpow (500050 : ℝ) ((1 : ℝ) / 6)) := by
          simp [B, pow_two, mul_assoc, mul_comm, mul_left_comm]
        _ = (2 * (10 : ℝ)) * Real.rpow (500050 : ℝ) ((1 : ℝ) / 3) := by
          rw [hpow_mul]
          rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 * (10 : ℝ))]
    have hsq_lt :
        (37 : ℝ) ^ 2 < B ^ 2 := by
      rw [hB_sq]
      nlinarith [h500050_third_gt]
    have habs_lt : |(37 : ℝ)| < |B| := by
      exact sq_lt_sq.mp hsq_lt
    have h37_abs : |(37 : ℝ)| = 37 := by norm_num
    have hB_abs : |B| = B := abs_of_nonneg hB_nonneg
    have h37_lt_B : (37 : ℝ) < B := by
      simpa [h37_abs, hB_abs] using habs_lt
    exact le_of_lt h37_lt_B
  have hroot_branch :
      (37 : ℝ) / Real.sqrt (100 : ℝ) ≤
        (Real.sqrt (2 * (10 : ℝ)) *
            Real.rpow ((50 : ℝ) + 2 * (100 : ℝ) * (50 : ℝ) ^ 2)
              ((1 : ℝ) / 6)) / Real.sqrt (100 : ℝ) := by
    have hsqrt100 : Real.sqrt (100 : ℝ) = 10 := by norm_num
    rw [show (50 : ℝ) + 2 * (100 : ℝ) * (50 : ℝ) ^ 2 = 500050 by norm_num,
      hsqrt100]
    exact div_le_div_of_nonneg_right hB_ge_37 (by norm_num)
  have hbad :=
    hsolver ((37 : ℝ) / 10) 37 10 50 5 50
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
      (by norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2500)])
      hroot_branch
  have hdet_lt :
      Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) /
          Real.sqrt (100 : ℝ) <
        (279 : ℝ) / 320 := by
    have hsqrt100 : Real.sqrt (100 : ℝ) = 10 := by norm_num
    have hmul :
        Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) <
          ((31 : ℝ) / 16) * ((9 : ℝ) / 2) := by
      have hsqrt20' : Real.sqrt (2 * (10 : ℝ)) < (9 : ℝ) / 2 := by
        norm_num
        exact hsqrt20_lt
      calc
        Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ))
            < ((31 : ℝ) / 16) * Real.sqrt (2 * (10 : ℝ)) := by
              exact mul_lt_mul_of_pos_right h50_sixth_lt
                (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2 * (10 : ℝ)))
        _ < ((31 : ℝ) / 16) * ((9 : ℝ) / 2) := by
              exact mul_lt_mul_of_pos_left hsqrt20' (by norm_num)
    rw [hsqrt100]
    nlinarith
  have hMterm_lt :
      (2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (100 : ℝ) <
        (9 : ℝ) / 8 := by
    have hsqrt100 : Real.sqrt (100 : ℝ) = 10 := by norm_num
    rw [hsqrt100]
    nlinarith [h10_34_lt]
  have hnoise_lt :
      2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3) /
          Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
        (8 : ℝ) / 5 := by
    have hden_pos :
        0 < Real.rpow (100 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < (100 : ℝ)) ((1 : ℝ) / 3)
    have hnum_lt : 2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3) < (37 : ℝ) / 5 := by
      nlinarith [h50_third_lt]
    have hratio_lt :
        (2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) /
            Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
          ((37 : ℝ) / 5) / ((37 : ℝ) / 8) := by
      have hstep1 :
          (2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3)) /
              Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
            ((37 : ℝ) / 5) /
              Real.rpow (100 : ℝ) ((1 : ℝ) / 3) :=
        div_lt_div_of_pos_right hnum_lt hden_pos
      have hstep2 :
          ((37 : ℝ) / 5) /
              Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
            ((37 : ℝ) / 5) / ((37 : ℝ) / 8) :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) h100_third_gt
      exact lt_trans hstep1 hstep2
    norm_num at hratio_lt ⊢
    exact hratio_lt
  have hRHS_lt :
      (Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) +
          2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) / Real.sqrt (100 : ℝ) +
        2 * Real.rpow (50 : ℝ) ((1 : ℝ) / 3) /
          Real.rpow (100 : ℝ) ((1 : ℝ) / 3) <
        (37 : ℝ) / 10 := by
    have hsplit :
        (Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) +
            2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) / Real.sqrt (100 : ℝ) =
          Real.rpow (50 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (10 : ℝ)) /
              Real.sqrt (100 : ℝ) +
            (2 * Real.rpow (10 : ℝ) ((3 : ℝ) / 4)) /
              Real.sqrt (100 : ℝ) := by
      ring
    rw [hsplit]
    nlinarith [hdet_lt, hMterm_lt, hnoise_lt]
  have hRHS_lt' := hRHS_lt
  norm_num at hbad hRHS_lt'
  exact (not_le_of_gt hRHS_lt') hbad

/-- Same-granularity scalar obstruction for the current source-boundary final
normalization bridge.

Even after adding the source facts that the live bridge currently receives
(`w ≥ (4Lk)^3`, `w ≥ 2G²`, root-sum `G`-boundedness, second-branch exclusion,
and the proved noise-term lower bound on `M`), the displayed final
normalization need not follow.  The concrete scalar values below satisfy those
facts while violating the conclusion, so the bridge cannot be closed at its
current head by ordinary tactic search. -/
private theorem
    theorem1_intermediate_root_sum_source_boundary_scalar_interface_false :
    ¬ (∀ X M w G σ L k : ℝ,
      0 ≤ X →
      0 ≤ M →
      0 ≤ w →
      0 ≤ σ →
      0 < L →
      0 < k →
      (4 * L * k) ^ 3 ≤ w →
      2 * G ^ 2 ≤ w →
      X ≤ Real.sqrt ((64 : ℝ) * G ^ 2) →
      ¬ X ≤ 2 * Real.rpow M ((3 : ℝ) / 4) →
      Real.rpow w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * k ^ 2) ≤ M →
      (Real.sqrt (2 * M) *
            Real.rpow (w + 2 * (64 : ℝ) * σ ^ 2) ((1 : ℝ) / 6) +
          2 * Real.rpow M ((3 : ℝ) / 4)) / Real.sqrt (64 : ℝ) ≤
        (Real.rpow w ((1 : ℝ) / 6) * Real.sqrt (2 * M) +
            2 * Real.rpow M ((3 : ℝ) / 4)) / Real.sqrt (64 : ℝ) +
          2 * Real.rpow σ ((1 : ℝ) / 3) /
            Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) := by
  intro hsolver
  have hsqrt6400 : Real.sqrt (64 * (10 : ℝ) ^ 2) = 80 := by
    norm_num
  have h64_34_lt_23 :
      Real.rpow (64 : ℝ) ((3 : ℝ) / 4) < 23 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (64 : ℝ) ((3 : ℝ) / 4) :=
      Real.rpow_nonneg (by norm_num) ((3 : ℝ) / 4)
    have hright_nonneg : 0 ≤ (23 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 4)]
    have hpow :
        Real.rpow (Real.rpow (64 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (64 : ℝ) ^ 3 := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (64 : ℝ))
          ((3 : ℝ) / 4) (4 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (64 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (64 : ℝ) ^ 3 := hpow
      _ < Real.rpow (23 : ℝ) (4 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h729_third_lt_10 :
      Real.rpow (729 : ℝ) ((1 : ℝ) / 3) < 10 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (729 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    have hright_nonneg : 0 ≤ (10 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (729 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (729 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (729 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (729 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (729 : ℝ) := hpow
      _ < Real.rpow (10 : ℝ) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hnoise_lower :
      Real.rpow (729 : ℝ) ((1 : ℝ) / 3) * (10 : ℝ) ^ 2 /
          (4 * (1 : ℝ) ^ 2 * (2 : ℝ) ^ 2) ≤ 64 := by
    have hlt :
        Real.rpow (729 : ℝ) ((1 : ℝ) / 3) * (10 : ℝ) ^ 2 /
            (4 * (1 : ℝ) ^ 2 * (2 : ℝ) ^ 2) < 64 := by
      nlinarith [h729_third_lt_10]
    exact le_of_lt hlt
  have hnot_second :
      ¬ (46 : ℝ) ≤ 2 * Real.rpow (64 : ℝ) ((3 : ℝ) / 4) := by
    intro hle
    nlinarith [h64_34_lt_23, hle]
  have hbad :=
    hsolver 46 64 729 10 10 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hsqrt6400]) hnot_second hnoise_lower
  have h13529_sixth_gt_nine_halves :
      (9 : ℝ) / 2 < Real.rpow (13529 : ℝ) ((1 : ℝ) / 6) := by
    have hleft_nonneg : 0 ≤ (9 : ℝ) / 2 := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (13529 : ℝ) ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 6)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow (Real.rpow (13529 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (13529 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (13529 : ℝ))
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow ((9 : ℝ) / 2) (6 : ℝ) < (13529 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (13529 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) :=
        hpow.symm
  have h729_sixth_le_three :
      Real.rpow (729 : ℝ) ((1 : ℝ) / 6) ≤ 3 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (729 : ℝ) ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 6)
    have hright_nonneg : 0 ≤ (3 : ℝ) := by norm_num
    rw [← Real.rpow_le_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow (Real.rpow (729 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (729 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (729 : ℝ))
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (729 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (729 : ℝ) := hpow
      _ ≤ Real.rpow (3 : ℝ) (6 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h10_third_lt_three :
      Real.rpow (10 : ℝ) ((1 : ℝ) / 3) < 3 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (10 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    have hright_nonneg : 0 ≤ (3 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (10 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (10 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (10 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (10 : ℝ) := hpow
      _ < Real.rpow (3 : ℝ) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hleft_gt :
      (Real.sqrt (2 * (64 : ℝ)) *
            Real.rpow ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2)
              ((1 : ℝ) / 6) +
          2 * Real.rpow (64 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (64 : ℝ) >
        ((Real.rpow (729 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (64 : ℝ)) +
            2 * Real.rpow (64 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (64 : ℝ) +
          2 * Real.rpow (10 : ℝ) ((1 : ℝ) / 3) /
            Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) := by
    have hsqrt128_gt_eight : (8 : ℝ) < Real.sqrt (2 * (64 : ℝ)) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have hdiff_gt :
        (3 : ℝ) / 2 <
          Real.rpow ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2)
              ((1 : ℝ) / 6) -
            Real.rpow (729 : ℝ) ((1 : ℝ) / 6) := by
      have hsum_eq :
          ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2) = 13529 := by
        norm_num
      rw [hsum_eq]
      linarith
    have hdelta :
        (3 : ℝ) / 2 <
          (Real.sqrt (2 * (64 : ℝ)) *
              (Real.rpow ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2)
                ((1 : ℝ) / 6) -
                Real.rpow (729 : ℝ) ((1 : ℝ) / 6))) /
            Real.sqrt (64 : ℝ) := by
      have hprod_gt :
          (8 : ℝ) * ((3 : ℝ) / 2) <
            Real.sqrt (2 * (64 : ℝ)) *
              (Real.rpow ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2)
                  ((1 : ℝ) / 6) -
                Real.rpow (729 : ℝ) ((1 : ℝ) / 6)) := by
        exact mul_lt_mul hsqrt128_gt_eight (le_of_lt hdiff_gt)
          (by norm_num) (by norm_num)
      have hsqrt64 : Real.sqrt (64 : ℝ) = 8 := by norm_num
      rw [hsqrt64]
      nlinarith
    have hnoise_lt :
        2 * Real.rpow (10 : ℝ) ((1 : ℝ) / 3) /
            Real.rpow (64 : ℝ) ((1 : ℝ) / 3) < (3 : ℝ) / 2 := by
      have h10_third_lt :
          Real.rpow (10 : ℝ) ((1 : ℝ) / 3) < (11 : ℝ) / 5 := by
        have hleft_nonneg :
            0 ≤ Real.rpow (10 : ℝ) ((1 : ℝ) / 3) :=
          Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
        have hright_nonneg : 0 ≤ (11 : ℝ) / 5 := by norm_num
        rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
          (by norm_num : (0 : ℝ) < 3)]
        have hpow :
            Real.rpow (Real.rpow (10 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
              (10 : ℝ) := by
          simpa using
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10 : ℝ))
              ((1 : ℝ) / 3) (3 : ℝ)).symm
        calc
          Real.rpow (Real.rpow (10 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
              (10 : ℝ) := hpow
          _ < Real.rpow ((11 : ℝ) / 5) (3 : ℝ) := by
            norm_num [Real.rpow_natCast]
      have h64_third_gt_three :
          (3 : ℝ) < Real.rpow (64 : ℝ) ((1 : ℝ) / 3) := by
        have hleft_nonneg : 0 ≤ (3 : ℝ) := by norm_num
        have hright_nonneg :
            0 ≤ Real.rpow (64 : ℝ) ((1 : ℝ) / 3) :=
          Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
        rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
          (by norm_num : (0 : ℝ) < 3)]
        have hpow :
            Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
              (64 : ℝ) := by
          simpa using
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (64 : ℝ))
              ((1 : ℝ) / 3) (3 : ℝ)).symm
        calc
          Real.rpow (3 : ℝ) (3 : ℝ) < (64 : ℝ) := by
            norm_num [Real.rpow_natCast]
          _ = Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
            hpow.symm
      have hden_pos :
          0 < Real.rpow (64 : ℝ) ((1 : ℝ) / 3) :=
        lt_trans (by norm_num : (0 : ℝ) < 3) h64_third_gt_three
      have hnum_lt :
          2 * Real.rpow (10 : ℝ) ((1 : ℝ) / 3) < (22 : ℝ) / 5 := by
        nlinarith [h10_third_lt]
      have hstep1 :
          2 * Real.rpow (10 : ℝ) ((1 : ℝ) / 3) /
              Real.rpow (64 : ℝ) ((1 : ℝ) / 3) <
            ((22 : ℝ) / 5) / Real.rpow (64 : ℝ) ((1 : ℝ) / 3) :=
        div_lt_div_of_pos_right hnum_lt hden_pos
      have hstep2 :
          ((22 : ℝ) / 5) / Real.rpow (64 : ℝ) ((1 : ℝ) / 3) <
            ((22 : ℝ) / 5) / 3 :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) h64_third_gt_three
      have hratio_lt := lt_trans hstep1 hstep2
      norm_num at hratio_lt ⊢
      exact lt_trans hratio_lt (by norm_num : (22 : ℝ) / 15 < 3 / 2)
    have hgap :
        2 * Real.rpow (10 : ℝ) ((1 : ℝ) / 3) /
            Real.rpow (64 : ℝ) ((1 : ℝ) / 3) <
          (Real.sqrt (2 * (64 : ℝ)) *
              (Real.rpow ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2)
                ((1 : ℝ) / 6) -
                Real.rpow (729 : ℝ) ((1 : ℝ) / 6))) /
            Real.sqrt (64 : ℝ) :=
      lt_trans hnoise_lt hdelta
    have hrewrite :
        (Real.sqrt (2 * (64 : ℝ)) *
              Real.rpow ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2)
                ((1 : ℝ) / 6) +
            2 * Real.rpow (64 : ℝ) ((3 : ℝ) / 4)) /
            Real.sqrt (64 : ℝ) =
          (Real.rpow (729 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (64 : ℝ)) +
              2 * Real.rpow (64 : ℝ) ((3 : ℝ) / 4)) /
            Real.sqrt (64 : ℝ) +
          (Real.sqrt (2 * (64 : ℝ)) *
              (Real.rpow ((729 : ℝ) + 2 * (64 : ℝ) * (10 : ℝ) ^ 2)
                ((1 : ℝ) / 6) -
                Real.rpow (729 : ℝ) ((1 : ℝ) / 6))) /
            Real.sqrt (64 : ℝ) := by
      have hsqrt64_ne : Real.sqrt (64 : ℝ) ≠ 0 := by norm_num
      field_simp [hsqrt64_ne]
      ring
    rw [hrewrite]
    linarith
  exact (not_le_of_gt hleft_gt) hbad

/-- Same-granularity obstruction for the current first-case final split.

This targets the exact scalar shape left in
`theorem1_first_case_sqrt_term_div_sqrt_le_rhs_of_source_boundary`: even with
the non-second branch, the root-sum `G` bound, the Theorem 1 `w` lower bounds,
and a noise-plus-log lower-bound shape for `M`, the printed split of
`(w + 2Tσ²)^(1/6)` without an `M^(1/2)` stochastic factor is not a valid
scalar consequence.  Thus the remaining bridge is a source-boundary issue, not
a tactic leaf. -/
private theorem
    theorem1_first_case_sqrt_term_source_boundary_scalar_interface_false :
    ¬ (∀ X M w G σ L k : ℝ,
      0 ≤ X →
      0 ≤ M →
      0 ≤ w →
      0 ≤ σ →
      0 < L →
      0 < k →
      (4 * L * k) ^ 3 ≤ w →
      2 * G ^ 2 ≤ w →
      X ≤ Real.sqrt ((10000 : ℝ) * G ^ 2) →
      ¬ X ≤ 2 * Real.rpow M ((3 : ℝ) / 4) →
      Real.rpow w ((1 : ℝ) / 3) * σ ^ 2 / (4 * L ^ 2 * k ^ 2) +
          (0 : ℝ) ≤ M →
      (Real.sqrt (2 * M) *
            Real.rpow (w + 2 * (10000 : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
          Real.sqrt (10000 : ℝ) ≤
        (Real.rpow w ((1 : ℝ) / 6) * Real.sqrt (2 * M) +
            2 * Real.rpow M ((3 : ℝ) / 4)) / Real.sqrt (10000 : ℝ) +
          2 * Real.rpow σ ((1 : ℝ) / 3) /
            Real.rpow (10000 : ℝ) ((1 : ℝ) / 3)) := by
  intro hsolver
  have h64_sixth_le_two :
      Real.rpow (64 : ℝ) ((1 : ℝ) / 6) ≤ 2 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (64 : ℝ) ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 6)
    have hright_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    rw [← Real.rpow_le_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (64 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (64 : ℝ))
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (64 : ℝ) := hpow
      _ ≤ Real.rpow (2 : ℝ) (6 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h81_34_le_27 :
      Real.rpow (81 : ℝ) ((3 : ℝ) / 4) ≤ 27 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (81 : ℝ) ((3 : ℝ) / 4) :=
      Real.rpow_nonneg (by norm_num) ((3 : ℝ) / 4)
    have hright_nonneg : 0 ≤ (27 : ℝ) := by norm_num
    rw [← Real.rpow_le_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 4)]
    have hpow :
        Real.rpow (Real.rpow (81 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (81 : ℝ) ^ 3 := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (81 : ℝ))
          ((3 : ℝ) / 4) (4 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (81 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (81 : ℝ) ^ 3 := hpow
      _ ≤ Real.rpow (27 : ℝ) (4 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h8_third_le_two :
      Real.rpow (8 : ℝ) ((1 : ℝ) / 3) ≤ 2 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (8 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    have hright_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    rw [← Real.rpow_le_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (8 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (8 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (8 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (8 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (8 : ℝ) := hpow
      _ ≤ Real.rpow (2 : ℝ) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have h10000_third_gt_21 :
      (21 : ℝ) < Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) := by
    have hleft_nonneg : 0 ≤ (21 : ℝ) := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (10000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (10000 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (10000 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (21 : ℝ) (3 : ℝ) < (10000 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (10000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
        hpow.symm
  have hsqrt162_lt_13 : Real.sqrt (162 : ℝ) < 13 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (13 : ℝ))]
    norm_num
  have hsqrt162_gt_12 : (12 : ℝ) < Real.sqrt (162 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ (12 : ℝ))]
    norm_num
  have h1280064_sixth_gt_10 :
      (10 : ℝ) < Real.rpow (1280064 : ℝ) ((1 : ℝ) / 6) := by
    have hleft_nonneg : 0 ≤ (10 : ℝ) := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (1280064 : ℝ) ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 6)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow (Real.rpow (1280064 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) =
          (1280064 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (1280064 : ℝ))
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow (10 : ℝ) (6 : ℝ) < (1280064 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (1280064 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) :=
        hpow.symm
  have hnot_second :
      ¬ (60 : ℝ) ≤ 2 * Real.rpow (81 : ℝ) ((3 : ℝ) / 4) := by
    intro hle
    nlinarith [h81_34_le_27]
  have hsolver_bad :=
    hsolver 60 81 64 1 8 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hnot_second
      (by
        have h64_third_le_four :
            Real.rpow (64 : ℝ) ((1 : ℝ) / 3) ≤ 4 := by
          have hleft_nonneg :
              0 ≤ Real.rpow (64 : ℝ) ((1 : ℝ) / 3) :=
            Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
          have hright_nonneg : 0 ≤ (4 : ℝ) := by norm_num
          rw [← Real.rpow_le_rpow_iff hleft_nonneg hright_nonneg
            (by norm_num : (0 : ℝ) < 3)]
          have hpow :
              Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
                (64 : ℝ) := by
            simpa using
              (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (64 : ℝ))
                ((1 : ℝ) / 3) (3 : ℝ)).symm
          calc
            Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
                (64 : ℝ) := hpow
            _ ≤ Real.rpow (4 : ℝ) (3 : ℝ) := by
              norm_num [Real.rpow_natCast]
        nlinarith)
  have hleft_gt :
      (Real.sqrt (2 * (81 : ℝ)) *
            Real.rpow ((64 : ℝ) + 2 * (10000 : ℝ) * (8 : ℝ) ^ 2)
              ((1 : ℝ) / 6)) /
          Real.sqrt (10000 : ℝ) >
        (6 : ℝ) / 5 := by
    have hsqrt10000 : Real.sqrt (10000 : ℝ) = 100 := by norm_num
    have hprod_gt :
        (120 : ℝ) <
          Real.sqrt (2 * (81 : ℝ)) *
            Real.rpow ((64 : ℝ) + 2 * (10000 : ℝ) * (8 : ℝ) ^ 2)
              ((1 : ℝ) / 6) := by
      have hprod :
          (12 : ℝ) * (10 : ℝ) <
            Real.sqrt (162 : ℝ) *
              Real.rpow (1280064 : ℝ) ((1 : ℝ) / 6) :=
        mul_lt_mul hsqrt162_gt_12 (le_of_lt h1280064_sixth_gt_10)
          (by norm_num) (by norm_num)
      norm_num at hprod ⊢
      exact hprod
    rw [show 2 * (81 : ℝ) = 162 by norm_num,
      show (64 : ℝ) + 2 * (10000 : ℝ) * (8 : ℝ) ^ 2 = 1280064 by norm_num,
      hsqrt10000]
    nlinarith
  have hright_lt :
      (Real.rpow (64 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (81 : ℝ)) +
            2 * Real.rpow (81 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (10000 : ℝ) +
        2 * Real.rpow (8 : ℝ) ((1 : ℝ) / 3) /
          Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) <
        (6 : ℝ) / 5 := by
    have hsqrt10000 : Real.sqrt (10000 : ℝ) = 100 := by norm_num
    have hdet_le :
        Real.rpow (64 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (81 : ℝ)) ≤
          2 * 13 := by
      have hsqrt162_lt_13' : Real.sqrt (2 * (81 : ℝ)) < 13 := by
        norm_num
        exact hsqrt162_lt_13
      have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * (81 : ℝ)) :=
        Real.sqrt_nonneg _
      exact mul_le_mul h64_sixth_le_two (le_of_lt hsqrt162_lt_13')
        hsqrt_nonneg (by norm_num)
    have hsecond_le :
        2 * Real.rpow (81 : ℝ) ((3 : ℝ) / 4) ≤ 54 := by
      nlinarith [h81_34_le_27]
    have hquot_le :
        (Real.rpow (64 : ℝ) ((1 : ℝ) / 6) * Real.sqrt (2 * (81 : ℝ)) +
            2 * Real.rpow (81 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (10000 : ℝ) ≤ (80 : ℝ) / 100 := by
      rw [hsqrt10000]
      nlinarith
    have hnoise_lt :
        2 * Real.rpow (8 : ℝ) ((1 : ℝ) / 3) /
            Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) <
          (4 : ℝ) / 21 := by
      have hden_pos :
          0 < Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) :=
        lt_trans (by norm_num : (0 : ℝ) < 21) h10000_third_gt_21
      have hnum_le :
          2 * Real.rpow (8 : ℝ) ((1 : ℝ) / 3) ≤ (4 : ℝ) := by
        nlinarith [h8_third_le_two]
      have hstep1 :
          2 * Real.rpow (8 : ℝ) ((1 : ℝ) / 3) /
              Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) ≤
            (4 : ℝ) / Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) :=
        div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
      have hstep2 :
          (4 : ℝ) / Real.rpow (10000 : ℝ) ((1 : ℝ) / 3) <
            (4 : ℝ) / 21 :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) h10000_third_gt_21
      exact lt_of_le_of_lt hstep1 hstep2
    nlinarith
  exact (not_le_of_gt (lt_trans hright_lt hleft_gt)) hsolver_bad

/-- Source-root-sum first alternative solved to the paper's intermediate
root-sum RHS.

This is Theorem 1 proof step 29 at source granularity.  It is intentionally
specialized to the generated root-sum quantity, not an arbitrary scalar route:
the caller supplies `X = theorem1ExpectedRootGradientNormSqSum ST μ T`, its
nonnegativity, and the raw first alternative produced by the scalar split. -/
private theorem theorem1_expected_root_sum_le_intermediate_rhs_of_first_case
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ) {X : ℝ}
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hRHS : theorem1RHSScalarBoundary S T L σ fStar)
    (hX_nonneg : 0 ≤ X)
    (hfirst :
      X ^ 2 ≤
        2 * (theorem1M S T L σ fStar *
          Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3))) :
    X ≤ theorem1ExpectedRootGradientNormSqSumRHS S T L σ fStar := by
  classical
  let M := theorem1M S T L σ fStar
  let A := S.w + 2 * (T : ℝ) * σ ^ 2
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using hM.2.2.2.2
  have hA_nonneg : 0 ≤ A := by
    have hw_nonneg : 0 ≤ S.w := hM.2.2.2.1
    have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    have hsigma_sq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
    nlinarith [hw_nonneg, hT_nonneg, hsigma_sq_nonneg]
  have hA13_nonneg : 0 ≤ Real.rpow A ((1 : ℝ) / 3) :=
    Real.rpow_nonneg hA_nonneg ((1 : ℝ) / 3)
  have hrad_nonneg : 0 ≤ 2 * M * Real.rpow A ((1 : ℝ) / 3) := by
    nlinarith [hM_nonneg, hA13_nonneg]
  have hfirst' :
      X ^ 2 ≤ 2 * M * Real.rpow A ((1 : ℝ) / 3) := by
    simpa [M, A, mul_assoc] using hfirst
  have hX_le_sqrt :
      X ≤ Real.sqrt (2 * M * Real.rpow A ((1 : ℝ) / 3)) :=
    Real.le_sqrt_of_sq_le hfirst'
  have hsqrt_factor :
      Real.sqrt (2 * M * Real.rpow A ((1 : ℝ) / 3)) =
        Real.sqrt (2 * M) * Real.rpow A ((1 : ℝ) / 6) := by
    have h2M_nonneg : 0 ≤ 2 * M := by nlinarith [hM_nonneg]
    have hpow_sqrt :
        Real.sqrt (Real.rpow A ((1 : ℝ) / 3)) =
          Real.rpow A ((1 : ℝ) / 6) := by
      rw [Real.sqrt_eq_rpow]
      have hmul :=
        Real.rpow_mul hA_nonneg ((1 : ℝ) / 3) ((1 : ℝ) / 2)
      norm_num at hmul
      simpa [mul_comm] using hmul.symm
    calc
      Real.sqrt (2 * M * Real.rpow A ((1 : ℝ) / 3)) =
          Real.sqrt (2 * M) * Real.sqrt (Real.rpow A ((1 : ℝ) / 3)) := by
            rw [Real.sqrt_mul h2M_nonneg]
      _ = Real.sqrt (2 * M) * Real.rpow A ((1 : ℝ) / 6) := by
            rw [hpow_sqrt]
  have hmain :
      X ≤ Real.sqrt (2 * M) * Real.rpow A ((1 : ℝ) / 6) := by
    rw [hsqrt_factor] at hX_le_sqrt
    exact hX_le_sqrt
  have hsecond_nonneg :
      0 ≤ 2 * Real.rpow M ((3 : ℝ) / 4) := by
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hM_nonneg _)
  calc
    X ≤ Real.sqrt (2 * M) * Real.rpow A ((1 : ℝ) / 6) := hmain
    _ ≤ Real.sqrt (2 * M) * Real.rpow A ((1 : ℝ) / 6) +
        2 * Real.rpow M ((3 : ℝ) / 4) := by
          linarith
    _ = theorem1ExpectedRootGradientNormSqSumRHS S T L σ fStar := by
          simp [theorem1ExpectedRootGradientNormSqSumRHS, M, A, mul_comm]

/-- Source-root-sum-specific first scalar alternative for Theorem 1 proof
lines 551-563.

This is the provable part of the first branch: the scalar is fixed to
`theorem1ExpectedRootGradientNormSqSum ST μ T`, and the raw first alternative is
converted to the intermediate root-sum term.  The subsequent printed-RHS
normalization is not kept here because
`theorem1_first_case_sqrt_term_source_boundary_scalar_interface_false` shows
that the current scalar interface is too weak for that final step. -/
private theorem theorem1_expected_root_sum_first_case_div_sqrt_le_intermediate
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (b L G σ fStar : ℝ)
    (hsec3 : Section3Assumptions (withTheorem1Parameters S b G L) μ L G σ fStar)
    (hMboundary :
      theorem1MScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar)
    (hRHSboundary :
      theorem1RHSScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar)
    (hnot_second :
      let ST := withTheorem1Parameters S b G L
      ¬ theorem1ExpectedRootGradientNormSqSum ST μ T ≤
        2 * Real.rpow (theorem1M ST T L σ fStar) ((3 : ℝ) / 4))
    (hfirst :
      let ST := withTheorem1Parameters S b G L
      theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
        2 * (theorem1M ST T L σ fStar *
          Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3))) :
    let ST := withTheorem1Parameters S b G L
    theorem1ExpectedRootGradientNormSqSum ST μ T / Real.sqrt (T : ℝ) ≤
      (Real.sqrt (2 * theorem1M ST T L σ fStar) *
          Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
        Real.sqrt (T : ℝ) := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hM : theorem1MScalarBoundary ST T L σ fStar := by
    simpa [ST] using hMboundary
  have hRHS : theorem1RHSScalarBoundary ST T L σ fStar := by
    simpa [ST] using hRHSboundary
  have hroot_int :
      Integrable
        (fun ω =>
          Real.sqrt
            (Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖ ^ 2))) μ :=
    theorem1_expected_root_gradient_norm_sq_sum_integrable ST μ T hsec3
  have hroot_G_bound :
      theorem1ExpectedRootGradientNormSqSum ST μ T ≤ Real.sqrt ((T : ℝ) * G ^ 2) :=
    theorem1_expected_root_gradient_norm_sq_sum_le_sqrt_T_mul_G_sq ST μ T hsec3
  have hroot_nonneg :
      0 ≤ theorem1ExpectedRootGradientNormSqSum ST μ T := by
    rw [theorem1ExpectedRootGradientNormSqSum]
    exact integral_nonneg fun ω => Real.sqrt_nonneg _
  have hM_nonneg : 0 ≤ theorem1M ST T L σ fStar := hM.2.2.2.2
  have hw_nonneg : 0 ≤ ST.w := hM.2.2.2.1
  have hT_sqrt_ne : Real.sqrt (T : ℝ) ≠ 0 := hRHS.2.1
  have hT_pos_real : 0 < (T : ℝ) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast (Nat.zero_le T)
    exact (Real.sqrt_pos).1
      (lt_of_le_of_ne (Real.sqrt_nonneg (T : ℝ)) (Ne.symm hT_sqrt_ne))
  have hT_nonneg : 0 ≤ (T : ℝ) := le_of_lt hT_pos_real
  have hfirst_sqrt :
      theorem1ExpectedRootGradientNormSqSum ST μ T ≤
        Real.sqrt (2 * theorem1M ST T L σ fStar) *
          Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6) := by
    let M := theorem1M ST T L σ fStar
    let A := ST.w + 2 * (T : ℝ) * σ ^ 2
    have hM_nonneg' : 0 ≤ M := by
      simpa [M] using hM.2.2.2.2
    have hA_nonneg : 0 ≤ A := by
      have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
      have hsigma_sq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
      nlinarith [hw_nonneg, hT_nonneg, hsigma_sq_nonneg]
    have hfirst' :
        theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
          2 * M * Real.rpow A ((1 : ℝ) / 3) := by
      simpa [ST, M, A, mul_assoc] using hfirst
    have hX_le_sqrt :
        theorem1ExpectedRootGradientNormSqSum ST μ T ≤
          Real.sqrt (2 * M * Real.rpow A ((1 : ℝ) / 3)) :=
      Real.le_sqrt_of_sq_le hfirst'
    have hsqrt_factor :
        Real.sqrt (2 * M * Real.rpow A ((1 : ℝ) / 3)) =
          Real.sqrt (2 * M) * Real.rpow A ((1 : ℝ) / 6) := by
      have h2M_nonneg : 0 ≤ 2 * M := by nlinarith [hM_nonneg']
      have hpow_sqrt :
          Real.sqrt (Real.rpow A ((1 : ℝ) / 3)) =
            Real.rpow A ((1 : ℝ) / 6) := by
        rw [Real.sqrt_eq_rpow]
        have hmul :=
          Real.rpow_mul hA_nonneg ((1 : ℝ) / 3) ((1 : ℝ) / 2)
        norm_num at hmul
        simpa [mul_comm] using hmul.symm
      calc
        Real.sqrt (2 * M * Real.rpow A ((1 : ℝ) / 3)) =
            Real.sqrt (2 * M) * Real.sqrt (Real.rpow A ((1 : ℝ) / 3)) := by
              rw [Real.sqrt_mul h2M_nonneg]
        _ = Real.sqrt (2 * M) * Real.rpow A ((1 : ℝ) / 6) := by
              rw [hpow_sqrt]
    rw [hsqrt_factor] at hX_le_sqrt
    simpa [M, A] using hX_le_sqrt
  have hroot_div_le :
      theorem1ExpectedRootGradientNormSqSum ST μ T / Real.sqrt (T : ℝ) ≤
        (Real.sqrt (2 * theorem1M ST T L σ fStar) *
            Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
          Real.sqrt (T : ℝ) := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hfirst_sqrt
        (inv_nonneg.mpr (Real.sqrt_nonneg (T : ℝ)))
  exact hroot_div_le

/-- Theorem 1 proof steps 27-31 specialized to the paper's root-sum random
variable.

The arbitrary-`X` first-case route above is retained only as legacy route
evidence.  The live source proof instead keeps `X` fixed to
`𝔼[sqrt(∑ ‖∇F(x_t)‖²)]`, the object produced by the Cauchy-Schwarz and
Jensen steps, and performs the scalar case split at that same source
granularity.  The first branch is left at the paper's intermediate root-sum
term; the final printed-RHS normalization is handled only at the coarser source
boundary because the current lower-level scalar interface has a compiled
counterexample. -/
private theorem theorem1_expected_root_sum_source_scalar_case_split
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (b L G σ fStar : ℝ)
    (hsec3 : Section3Assumptions (withTheorem1Parameters S b G L) μ L G σ fStar)
    (hMboundary :
      theorem1MScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar)
    (hRHSboundary :
      theorem1RHSScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar)
    (hscalar :
      let ST := withTheorem1Parameters S b G L
      theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
        theorem1M ST T L σ fStar *
            Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) +
          Real.rpow 2 ((1 : ℝ) / 3) * theorem1M ST T L σ fStar *
            Real.rpow (theorem1ExpectedRootGradientNormSqSum ST μ T)
              ((2 : ℝ) / 3)) :
    let ST := withTheorem1Parameters S b G L
    theorem1ExpectedRootGradientNormSqSum ST μ T / Real.sqrt (T : ℝ) ≤
        (Real.sqrt (2 * theorem1M ST T L σ fStar) *
            Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
          Real.sqrt (T : ℝ) ∨
      theorem1ExpectedRootGradientNormSqSum ST μ T ≤
        2 * Real.rpow (theorem1M ST T L σ fStar) ((3 : ℝ) / 4) := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hM : theorem1MScalarBoundary ST T L σ fStar := by
    simpa [ST] using hMboundary
  have hRHS : theorem1RHSScalarBoundary ST T L σ fStar := by
    simpa [ST] using hRHSboundary
  have hX_nonneg :
      0 ≤ theorem1ExpectedRootGradientNormSqSum ST μ T := by
    rw [theorem1ExpectedRootGradientNormSqSum]
    exact integral_nonneg fun ω => Real.sqrt_nonneg _
  have hraw :
      theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
          2 * (theorem1M ST T L σ fStar *
            Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3)) ∨
        theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
          2 * (Real.rpow 2 ((1 : ℝ) / 3) *
            theorem1M ST T L σ fStar *
            Real.rpow (theorem1ExpectedRootGradientNormSqSum ST μ T)
              ((2 : ℝ) / 3)) := by
    exact theorem1_scalar_X_raw_case_split ST T L σ fStar (by
      simpa [ST] using hscalar)
  by_cases hsecond :
      theorem1ExpectedRootGradientNormSqSum ST μ T ≤
        2 * Real.rpow (theorem1M ST T L σ fStar) ((3 : ℝ) / 4)
  · exact Or.inr hsecond
  · rcases hraw with hfirst | hraw_second
    · exact Or.inl
        (theorem1_expected_root_sum_first_case_div_sqrt_le_intermediate
          S μ T b L G σ fStar hsec3 hMboundary hRHSboundary
          (by simpa [ST] using hsecond)
          (by simpa [ST] using hfirst))
    · exact Or.inr
        (theorem1_scalar_X_second_case_bound hM.2.2.2.2 hX_nonneg
          (by
            simpa [ST, mul_assoc, mul_left_comm, mul_comm] using hraw_second))

/-- The root-sum branch of Theorem 1 through the provable source scalar split.

The first disjunct is intentionally the intermediate root-sum term, not the
printed RHS.  The attempted lower-level final normalization was retired after
`theorem1_first_case_sqrt_term_source_boundary_scalar_interface_false` showed
that the exposed scalar facts do not imply it. -/
private theorem theorem1_expected_root_sum_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (b L G σ fStar : ℝ)
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hgeneratedScalar :
      generatedStepsizeScalarBoundary (withTheorem1Parameters S b G L))
    (hk_pos : 0 < (withTheorem1Parameters S b G L).k)
    (hMboundary :
      theorem1MScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar)
    (hRHSboundary :
      theorem1RHSScalarBoundary (withTheorem1Parameters S b G L) T L σ fStar)
    (hweighted :
      let ST := withTheorem1Parameters S b G L
      theorem1WeightedGradientNormSqSum ST μ T ≤
        ST.k * theorem1M ST T L σ fStar) :
    let ST := withTheorem1Parameters S b G L
    theorem1ExpectedRootGradientNormSqSum ST μ T / Real.sqrt (T : ℝ) ≤
        (Real.sqrt (2 * theorem1M ST T L σ fStar) *
            Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
          Real.sqrt (T : ℝ) ∨
      theorem1ExpectedRootGradientNormSqSum ST μ T ≤
        2 * Real.rpow (theorem1M ST T L σ fStar) ((3 : ℝ) / 4) := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hsec3ST : Section3Assumptions ST μ L G σ fStar := by
    simpa [ST] using section3Assumptions_withTheorem1Parameters S μ hsec3 b
  have hgeneratedScalarST : generatedStepsizeScalarBoundary ST := by
    simpa [ST] using hgeneratedScalar
  have hgenerated : generatedStepsizeQuotientBoundary ST := by
    exact ⟨hgeneratedScalarST, by simpa [ST] using hk_pos⟩
  have hM : theorem1MScalarBoundary ST T L σ fStar := by
    simpa [ST] using hMboundary
  have hRHS : theorem1RHSScalarBoundary ST T L σ fStar := by
    simpa [ST] using hRHSboundary
  have hweightedST :
      theorem1WeightedGradientNormSqSum ST μ T ≤
        ST.k * theorem1M ST T L σ fStar := by
    simpa [ST] using hweighted
  have hT_pos : 0 < T := by
    by_contra hnot
    have hTzero : T = 0 := Nat.eq_zero_of_not_pos hnot
    exact hRHS.2.1 (by simp [hTzero])
  have hetaT_lower :
      ∫ ω,
          stepsize ST (theorem1TerminalGradientIndex T) ω *
            Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖ ^ 2) ∂μ ≤
        theorem1WeightedGradientNormSqSum ST μ T :=
    theorem1_eta_T_weighted_lower_bound ST μ T hT_pos hsec3ST hgenerated
  have hroot_cauchy :
      theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
        (∫ ω, (1 / stepsize ST (theorem1TerminalGradientIndex T) ω) ∂μ) *
          (ST.k * theorem1M ST T L σ fStar) :=
    theorem1_cauchy_schwarz_root_sum_bound
      ST μ T hT_pos hsec3ST hgenerated hetaT_lower hweightedST
  have hwith_sampled :
      theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
        ∫ ω,
          theorem1M ST T L σ fStar *
            Real.rpow
              (ST.w + theorem1TerminalCumulativeGradientNormSq ST T ω)
              ((1 : ℝ) / 3) ∂μ :=
    theorem1_root_sum_bound_with_sampled_gradients
      ST μ T hT_pos hsec3ST hgenerated hM hroot_cauchy
  have hscalar :
      theorem1ExpectedRootGradientNormSqSum ST μ T ^ 2 ≤
        theorem1M ST T L σ fStar *
            Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 3) +
          Real.rpow 2 ((1 : ℝ) / 3) * theorem1M ST T L σ fStar *
            Real.rpow (theorem1ExpectedRootGradientNormSqSum ST μ T) ((2 : ℝ) / 3) :=
    theorem1_root_sum_noise_split ST μ T hsec3ST hT_pos hgenerated hM
      hwith_sampled
  have hX_nonneg : 0 ≤ theorem1ExpectedRootGradientNormSqSum ST μ T := by
    rw [theorem1ExpectedRootGradientNormSqSum]
    exact integral_nonneg fun ω => Real.sqrt_nonneg _
  exact
    theorem1_expected_root_sum_source_scalar_case_split S μ T b L G σ fStar
      hsec3ST hMboundary hRHSboundary hscalar

/-- Finite Cauchy-Schwarz step used in the last line of Theorem 1.

For nonnegative scalar components, their uniform finite average is bounded by
the square-root of the sum of squares divided by the square-root of the window
size.  This is the paper's final `∑‖∇F(x_t)‖ / T ≤ X / √T` step, stated over
an arbitrary finite type so the STORM specialization is not a local wrapper. -/
private theorem finiteUniformAverage_nonneg_le_root_sum_sq_div_sqrt_card
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    (ha_nonneg : ∀ i, 0 ≤ a i) :
    SOptLib.finiteUniformAverage a ≤
      Real.sqrt (Finset.sum Finset.univ (fun i => a i ^ 2)) /
        Real.sqrt (Fintype.card ι : ℝ) := by
  simpa [SOptLib.finiteUniformAverage_def, smul_eq_mul] using
    (inv_card_mul_sum_le_sqrt_sum_sq_div_sqrt_card a)

/-- Integral form of the final finite Cauchy-Schwarz step in Theorem 1. -/
private theorem theorem1_generated_average_le_expected_root_sum_div_sqrt
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar)
    (hRHS : theorem1RHSScalarBoundary S T L σ fStar) :
    (∫ ω,
      SOptLib.finiteUniformAverage
        (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) ∂μ) ≤
      theorem1ExpectedRootGradientNormSqSum S μ T / Real.sqrt (T : ℝ) := by
  simpa [SOptLib.finiteUniformAverage_def, smul_eq_mul,
    theorem1ExpectedRootGradientNormSqSum] using
    (integral_inv_card_sum_le_integral_sqrt_sum_sq_div_sqrt_card μ
      (fun i : Fin T => fun ω => ‖objectiveGradient S (iterate S i.val ω)‖)
      (theorem1_output_window_integrability_from_G_lipschitz S μ hsec3 T)
      (theorem1_expected_root_gradient_norm_sq_sum_integrable S μ T hsec3))

/-- The paper's actual finite-average output is uniformly bounded by the
Section 3 `G`-Lipschitz gradient bound.

This is deliberately stated for `totalizedExpectedAverageGradientNorm`, not for
the auxiliary root-sum scalar `X`.  The failed lower-level route tried to prove
the final printed RHS from `X / sqrt T`; the source object in the theorem
statement is the average itself, which also carries this direct `G` bound. -/
private theorem theorem1_totalized_expected_average_gradient_norm_le_G
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (hsec3 : Section3Assumptions S μ L G σ fStar) :
    totalizedExpectedAverageGradientNorm S μ T ≤ G := by
  classical
  have hG_nonneg : 0 ≤ G :=
    section3_lipschitz_constant_nonneg_obligation S μ hsec3
  have hgrad_int :
      ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient S (iterate S i.val ω)‖) μ :=
    theorem1_output_window_integrability_from_G_lipschitz S μ hsec3 T
  have havg_int :
      Integrable (totalizedAverageGradientNorm S T) μ := by
    have hsum :
        Integrable
          (fun ω =>
            Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖)) μ :=
      MeasureTheory.integrable_finset_sum (s := Finset.univ) (μ := μ)
        (fun i _hi => hgrad_int i)
    change Integrable
      (fun ω =>
        SOptLib.finiteUniformAverage
          (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖)) μ
    simpa [SOptLib.finiteUniformAverage_def, smul_eq_mul]
      using hsum.const_mul ((Fintype.card (Fin T) : ℝ)⁻¹)
  have hpoint :
      ∀ᵐ ω ∂μ, totalizedAverageGradientNorm S T ω ≤ G := by
    filter_upwards with ω
    by_cases hT : T = 0
    · simp [totalizedAverageGradientNorm, SOptLib.finiteUniformAverage_def, hT,
        hG_nonneg]
    · have hT_pos : 0 < T := Nat.pos_of_ne_zero hT
      have hcard_pos : 0 < (Fintype.card (Fin T) : ℝ) := by
        simp [Fintype.card_fin, hT_pos]
      have hcard_nonneg : 0 ≤ (Fintype.card (Fin T) : ℝ) := le_of_lt hcard_pos
      have hsum_le :
          Finset.sum Finset.univ
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) ≤
            Finset.sum Finset.univ (fun _i : Fin T => G) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        exact section3_objectiveGradient_norm_le S μ hsec3 0
          (iterate S i.val ω)
      have hscaled :=
        mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hcard_nonneg)
      calc
        totalizedAverageGradientNorm S T ω =
            (Fintype.card (Fin T) : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) := by
          simp [totalizedAverageGradientNorm, SOptLib.finiteUniformAverage_def,
            smul_eq_mul]
        _ ≤ (Fintype.card (Fin T) : ℝ)⁻¹ *
              Finset.sum Finset.univ (fun _i : Fin T => G) := hscaled
        _ = G := by
          simp [Fintype.card_fin]
          field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hT_pos)]
  have hconst_int : Integrable (fun _ω : Ω => G) μ :=
    integrable_const (c := G)
  simpa [totalizedExpectedAverageGradientNorm] using
    integral_mono_ae havg_int hconst_int hpoint

/-- Concrete scalar model showing that the current final RHS-normalization
boundary is too weak.

The obstruction is at the exact private scalar interface below: with `T = 1`,
`w = 0`, `σ = 1`, and a large admissible `M`, the root-sum RHS still contains
`sqrt(2M) * (2Tσ²)^(1/6)`, but the printed RHS keeps only `2σ^(1/3)/T^(1/3)`.
This is not a new assumption or a public dependency; it is route evidence that
the scalar helper below needs a stronger source-derived scalar input or a
different source-level normalization route. -/
private def theorem1ScalarNormalizationCounterexampleSetup :
    Setup Unit Unit ℝ :=
  { x₁ := 0
    sample := fun _ _ => ()
    sampleLoss := fun _ _ => 0
    objectiveValue := fun _ => (25 : ℝ) / 2
    k := 1
    w := 0
    c := 0 }

private theorem theorem1ScalarNormalizationCounterexample_M :
    theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1 0 = 100 := by
  have h13 : ((1 : ℝ) / 3) ≠ 0 := by norm_num
  norm_num [theorem1M, theorem1MFormula,
    theorem1ScalarNormalizationCounterexampleSetup, Real.zero_rpow h13]

private theorem theorem1ScalarNormalizationCounterexample_M_sigma
    (σ : ℝ) :
    theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 σ 0 = 100 := by
  have h13 : ((1 : ℝ) / 3) ≠ 0 := by norm_num
  norm_num [theorem1M, theorem1MFormula,
    theorem1ScalarNormalizationCounterexampleSetup, Real.zero_rpow h13]

private theorem theorem1ScalarNormalizationCounterexample_M_boundary :
    theorem1MScalarBoundary theorem1ScalarNormalizationCounterexampleSetup 1 1 1 0 := by
  have h13 : ((1 : ℝ) / 3) ≠ 0 := by norm_num
  norm_num [theorem1MScalarBoundary, theorem1M, theorem1MFormula,
    theorem1ScalarNormalizationCounterexampleSetup, Real.zero_rpow h13]

private theorem theorem1ScalarNormalizationCounterexample_M_boundary_sigma1000 :
    theorem1MScalarBoundary theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 := by
  have h13 : ((1 : ℝ) / 3) ≠ 0 := by norm_num
  norm_num [theorem1MScalarBoundary, theorem1M, theorem1MFormula,
    theorem1ScalarNormalizationCounterexampleSetup, Real.zero_rpow h13]

private theorem theorem1ScalarNormalizationCounterexample_RHS_boundary :
    theorem1RHSScalarBoundary theorem1ScalarNormalizationCounterexampleSetup 1 1 1 0 := by
  norm_num [theorem1RHSScalarBoundary, theorem1ScalarNormalizationCounterexample_M]

private theorem theorem1ScalarNormalizationCounterexample_RHS_boundary_sigma1000 :
    theorem1RHSScalarBoundary theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 := by
  norm_num [theorem1RHSScalarBoundary,
    theorem1ScalarNormalizationCounterexample_M_sigma]

private theorem theorem1_root_sum_rhs_div_sqrt_le_rhs_current_boundary_false :
    ¬ (theorem1ExpectedRootGradientNormSqSumRHS
          theorem1ScalarNormalizationCounterexampleSetup 1 1 1 0 /
        Real.sqrt (1 : ℝ) ≤
          theorem1RHS theorem1ScalarNormalizationCounterexampleSetup 1 1 1 0) := by
  intro hle
  have h2pow_ge_one :
      (1 : ℝ) ≤ Real.rpow 2 ((1 : ℝ) / 6) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have h2pow_pos :
      0 < Real.rpow 2 ((1 : ℝ) / 6) :=
    Real.rpow_pos_of_pos (by norm_num) ((1 : ℝ) / 6)
  have hsqrt200_gt_two : (2 : ℝ) < Real.sqrt 200 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hbig :
      (2 : ℝ) < Real.sqrt 200 * Real.rpow 2 ((1 : ℝ) / 6) := by
    have hle_two : (2 : ℝ) ≤ 2 * Real.rpow 2 ((1 : ℝ) / 6) := by
      nlinarith
    have hlt_mul :
        2 * Real.rpow 2 ((1 : ℝ) / 6) <
          Real.sqrt 200 * Real.rpow 2 ((1 : ℝ) / 6) :=
      mul_lt_mul_of_pos_right hsqrt200_gt_two h2pow_pos
    exact lt_of_le_of_lt hle_two hlt_mul
  have hle_simp := hle
  simp only [theorem1ExpectedRootGradientNormSqSumRHS, theorem1RHS] at hle_simp
  rw [theorem1ScalarNormalizationCounterexample_M] at hle_simp
  have h16 : ((1 : ℝ) / 6) ≠ 0 := by norm_num
  norm_num [theorem1ScalarNormalizationCounterexampleSetup, Real.zero_rpow h16] at hle_simp
  have hxle :
      Real.sqrt 200 * Real.rpow 2 ((1 : ℝ) / 6) ≤ 2 := by
    have htmp := sub_le_sub_right hle_simp (2 * 100 ^ ((3 : ℝ) / 4))
    ring_nf at htmp ⊢
    exact htmp
  exact (not_le_of_gt hbig) hxle

/-- The current exact scalar case-normalization interface is also too weak if
it only receives `theorem1MScalarBoundary` and `theorem1RHSScalarBoundary`.

This is same-target obstruction evidence for
`theorem1_scalar_X_cases_div_sqrt_le_rhs`: the raw first alternative can hold
while neither normalized disjunct follows.  A source-faithful replacement must
therefore consume stronger parameter-choice information from
`theorem1ScalarBoundary` or another proved source scalar bridge, rather than
trying to prove this weak private head. -/
private theorem theorem1_scalar_X_cases_div_sqrt_le_rhs_current_boundary_false :
    ¬ (∀ X : ℝ,
      0 ≤ X →
      (X ^ 2 ≤
          2 * (theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 *
            Real.rpow
              (theorem1ScalarNormalizationCounterexampleSetup.w +
                2 * (1 : ℝ) * (1000 : ℝ) ^ 2)
              ((1 : ℝ) / 3)) ∨
        X ^ 2 ≤
          2 * (Real.rpow 2 ((1 : ℝ) / 3) *
            theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 *
              Real.rpow X ((2 : ℝ) / 3))) →
      X / Real.sqrt (1 : ℝ) ≤
          theorem1RHS theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 ∨
        X ≤
          2 * Real.rpow
            (theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0)
            ((3 : ℝ) / 4)) := by
  intro h
  have hcube_lower :
      (120 : ℝ) < Real.rpow (2000000 : ℝ) ((1 : ℝ) / 3) := by
    have hleft_nonneg : 0 ≤ (120 : ℝ) := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (2000000 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (2000000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (2000000 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2000000 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (120 : ℝ) (3 : ℝ) < (2000000 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (2000000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
        hpow.symm
  have hfirst :
      (150 : ℝ) ^ 2 ≤
          2 * (theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 *
            Real.rpow
              (theorem1ScalarNormalizationCounterexampleSetup.w +
                2 * (1 : ℝ) * (1000 : ℝ) ^ 2)
              ((1 : ℝ) / 3)) := by
    rw [theorem1ScalarNormalizationCounterexample_M_sigma]
    norm_num [theorem1ScalarNormalizationCounterexampleSetup] at hcube_lower ⊢
    nlinarith
  have hcases := h 150 (by norm_num) (Or.inl hfirst)
  have hM34_lt :
      Real.rpow (100 : ℝ) ((3 : ℝ) / 4) < 32 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (100 : ℝ) ((3 : ℝ) / 4) :=
      Real.rpow_nonneg (by norm_num) ((3 : ℝ) / 4)
    have hright_nonneg : 0 ≤ (32 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 4)]
    have hpow :
        Real.rpow (Real.rpow (100 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (100 : ℝ) ^ 3 := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (100 : ℝ))
          ((3 : ℝ) / 4) (4 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (100 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (100 : ℝ) ^ 3 := hpow
      _ < Real.rpow (32 : ℝ) (4 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hsigma_third_lt :
      Real.rpow (1000 : ℝ) ((1 : ℝ) / 3) < 11 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (1000 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    have hright_nonneg : 0 ≤ (11 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (1000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (1000 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (1000 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (1000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (1000 : ℝ) := hpow
      _ < Real.rpow (11 : ℝ) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hRHS_lt :
      theorem1RHS theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 < 150 := by
    have h16 : ((1 : ℝ) / 6) ≠ 0 := by norm_num
    have hRHS_eq :
        theorem1RHS theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 =
          2 * Real.rpow (100 : ℝ) ((3 : ℝ) / 4) +
            2 * Real.rpow (1000 : ℝ) ((1 : ℝ) / 3) := by
      norm_num [theorem1RHS, theorem1M, theorem1MFormula,
        theorem1ScalarNormalizationCounterexampleSetup, Real.zero_rpow h16]
    rw [hRHS_eq]
    nlinarith [hM34_lt, hsigma_third_lt]
  have hsecond_bound_lt :
      2 * Real.rpow
            (theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0)
            ((3 : ℝ) / 4) < 150 := by
    rw [theorem1ScalarNormalizationCounterexample_M_sigma]
    nlinarith [hM34_lt]
  rcases hcases with hdiv | hsecond
  · norm_num at hdiv
    exact (not_le_of_gt hRHS_lt) hdiv
  · exact (not_le_of_gt hsecond_bound_lt) hsecond

/-- Same-interface obstruction for the remaining first-case scalar leaf.

The raw first alternative is not, by itself, a valid supplier of the normalized
first disjunct for an arbitrary scalar `X`.  If such a first-case solver were
available at the scalar facts exposed by the current route, combining it with
the already-proved second-case solver would prove
`theorem1_scalar_X_cases_div_sqrt_le_rhs_current_boundary_false`, a compiled
counterexample.  The live Theorem 1 route must therefore carry the source
relation tying `X` to the actual expected root-sum quantity, or another
source-derived scalar invariant; another arbitrary-`X` wrapper is not a
provable replacement. -/
private theorem theorem1_scalar_X_first_case_arbitrary_X_boundary_false :
    ¬ (∀ X : ℝ,
      0 ≤ X →
      ¬ X ≤
        2 * Real.rpow
          (theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0)
          ((3 : ℝ) / 4) →
      X ^ 2 ≤
        2 * (theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0 *
          Real.rpow
            (theorem1ScalarNormalizationCounterexampleSetup.w +
              2 * (1 : ℝ) * (1000 : ℝ) ^ 2)
            ((1 : ℝ) / 3)) →
      X / Real.sqrt (1 : ℝ) ≤
        theorem1RHS theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0) := by
  intro hfirst_solver
  exact theorem1_scalar_X_cases_div_sqrt_le_rhs_current_boundary_false (by
    intro X hX_nonneg hcases
    by_cases hsecond :
        X ≤
          2 * Real.rpow
            (theorem1M theorem1ScalarNormalizationCounterexampleSetup 1 1 1000 0)
            ((3 : ℝ) / 4)
    · exact Or.inr hsecond
    · rcases hcases with hfirst | hraw_second
      · exact Or.inl (hfirst_solver X hX_nonneg hsecond hfirst)
      · exact Or.inr
          (theorem1_scalar_X_second_case_bound
            theorem1ScalarNormalizationCounterexample_M_boundary_sigma1000.2.2.2.2
            hX_nonneg hraw_second))

/-- Source-faithful scalar final step for Theorem 1.

This consumes the normalized first branch produced by proof step 32 or the
second scalar alternative from proof steps 27-31. Keeping the disjunction in
the interface is essential; the additive root-sum RHS has a compiled
counterexample at the weaker standalone boundary above. -/
private theorem theorem1_root_sum_case_bound_div_sqrt_le_rhs
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ)
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hRHS : theorem1RHSScalarBoundary S T L σ fStar)
    {X : ℝ}
    (hcases :
      X / Real.sqrt (T : ℝ) ≤
          theorem1RHS S T L σ fStar ∨
        X ≤
          2 * Real.rpow (theorem1M S T L σ fStar) ((3 : ℝ) / 4)) :
    X / Real.sqrt (T : ℝ) ≤ theorem1RHS S T L σ fStar := by
  classical
  rcases hcases with hfirst | hsecond
  · exact hfirst
  · -- Second scalar alternative from the paper: it is exactly the
    -- `2M^(3/4)/sqrt(T)` term already present in the printed RHS.
    let M := theorem1M S T L σ fStar
    let rootT := Real.sqrt (T : ℝ)
    let deterministicTerm :=
      Real.rpow S.w ((1 : ℝ) / 6) * Real.sqrt (2 * M)
    let secondTerm := 2 * Real.rpow M ((3 : ℝ) / 4)
    let noiseTerm :=
      2 * Real.rpow σ ((1 : ℝ) / 3) /
        Real.rpow (T : ℝ) ((1 : ℝ) / 3)
    have hrootT_nonneg : 0 ≤ rootT := by
      simp [rootT]
    have hrootT_inv_nonneg : 0 ≤ rootT⁻¹ :=
      inv_nonneg.mpr hrootT_nonneg
    have hX_div :
        X / rootT ≤ secondTerm / rootT := by
      simpa [div_eq_mul_inv, secondTerm, M, rootT] using
        mul_le_mul_of_nonneg_right hsecond hrootT_inv_nonneg
    have hM_nonneg : 0 ≤ M := by
      simpa [M] using hM.2.2.2.2
    have hw_nonneg : 0 ≤ S.w := hM.2.2.2.1
    have hdet_nonneg : 0 ≤ deterministicTerm := by
      dsimp [deterministicTerm, M]
      exact mul_nonneg
        (Real.rpow_nonneg hw_nonneg ((1 : ℝ) / 6))
        (Real.sqrt_nonneg (2 * theorem1M S T L σ fStar))
    have hsecond_le_sum :
        secondTerm / rootT ≤
          (deterministicTerm + secondTerm) / rootT := by
      have hbase : secondTerm ≤ deterministicTerm + secondTerm := by
        linarith
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hbase hrootT_inv_nonneg
    have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast (Nat.zero_le T)
    have hT_pos : 0 < (T : ℝ) := by
      have hsqrt_pos : 0 < Real.sqrt (T : ℝ) := by
        exact lt_of_le_of_ne (Real.sqrt_nonneg (T : ℝ)) (Ne.symm hRHS.2.1)
      exact (Real.sqrt_pos).1 hsqrt_pos
    have hT_rpow_pos :
        0 < Real.rpow (T : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hT_pos ((1 : ℝ) / 3)
    have hnoise_nonneg : 0 ≤ noiseTerm := by
      have hsigma_nonneg : 0 ≤ σ := hRHS.2.2.2
      have hsigma_rpow_nonneg :
          0 ≤ Real.rpow σ ((1 : ℝ) / 3) :=
        Real.rpow_nonneg hsigma_nonneg ((1 : ℝ) / 3)
      have hnum_nonneg :
          0 ≤ 2 * Real.rpow σ ((1 : ℝ) / 3) := by
        positivity
      dsimp [noiseTerm]
      exact div_nonneg hnum_nonneg (le_of_lt hT_rpow_pos)
    have hsum_le_rhs :
        (deterministicTerm + secondTerm) / rootT ≤
          (deterministicTerm + secondTerm) / rootT + noiseTerm := by
      linarith
    have hmain :
        X / rootT ≤
          (deterministicTerm + secondTerm) / rootT + noiseTerm :=
      le_trans hX_div (le_trans hsecond_le_sum hsum_le_rhs)
    simpa [theorem1RHS, M, rootT, deterministicTerm, secondTerm, noiseTerm]
      using hmain

/-- Final Theorem 1 conversion step: average-gradient norm is controlled by
the root-sum case alternatives and the displayed scalar RHS. -/
private theorem theorem1_average_gradient_bound_from_root_sum
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) {L G σ fStar : ℝ}
    (_hsec3 : Section3Assumptions S μ L G σ fStar)
    (_hM : theorem1MScalarBoundary S T L σ fStar)
    (_hRHS : theorem1RHSScalarBoundary S T L σ fStar)
    (hroot_cases :
      theorem1ExpectedRootGradientNormSqSum S μ T / Real.sqrt (T : ℝ) ≤
          theorem1RHS S T L σ fStar ∨
        theorem1ExpectedRootGradientNormSqSum S μ T ≤
          2 * Real.rpow (theorem1M S T L σ fStar) ((3 : ℝ) / 4)) :
    totalizedExpectedAverageGradientNorm S μ T ≤ theorem1RHS S T L σ fStar := by
  classical
  have havg_root :
      totalizedExpectedAverageGradientNorm S μ T ≤
        theorem1ExpectedRootGradientNormSqSum S μ T / Real.sqrt (T : ℝ) :=
    by
      have hgenerated_avg :
          (∫ ω,
            SOptLib.finiteUniformAverage
              (fun i : Fin T => ‖objectiveGradient S (iterate S i.val ω)‖) ∂μ) ≤
            theorem1ExpectedRootGradientNormSqSum S μ T / Real.sqrt (T : ℝ) :=
        theorem1_generated_average_le_expected_root_sum_div_sqrt
          S μ T _hsec3 _hRHS
      simpa [totalizedExpectedAverageGradientNorm, totalizedAverageGradientNorm]
        using hgenerated_avg
  have hscalar :
      theorem1ExpectedRootGradientNormSqSum S μ T / Real.sqrt (T : ℝ) ≤
        theorem1RHS S T L σ fStar :=
    theorem1_root_sum_case_bound_div_sqrt_le_rhs
      S T L σ fStar _hM _hRHS hroot_cases
  exact le_trans havg_root hscalar

/-- Same-target obstruction for the live final average-level interface.

This is the exact scalar shape exposed at
`theorem1_generated_average_bound_from_source_chain.hsource_final`: the theorem output
`A` is bounded both by `X / √T` and by `G`, while the root-sum branch is still
the intermediate first-case term or the second scalar alternative.  The first
branch of this interface is already refuted by
`theorem1_average_level_first_case_scalar_interface_false`; adding the second
alternative as a disjunction does not repair the first-branch counterexample.

Therefore the remaining Theorem 1 leaf cannot be a tactic handoff at this
interface.  It needs either a stronger source-derived invariant than the
currently exposed final-step facts, or a source correction for the printed
last inequality in paper lines 551-563. -/
private theorem theorem1_final_average_rhs_source_invariant_current_interface_false :
    ¬ (∀ A X M w G σ : ℝ,
      0 ≤ A →
      A ≤ X / Real.sqrt (100 : ℝ) →
      A ≤ G →
      0 ≤ X →
      0 ≤ M →
      0 ≤ w →
      0 ≤ σ →
      2 * G ^ 2 ≤ w →
      X ≤ Real.sqrt ((100 : ℝ) * G ^ 2) →
      (X / Real.sqrt (100 : ℝ) ≤
          (Real.sqrt (2 * M) *
              Real.rpow (w + 2 * (100 : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
            Real.sqrt (100 : ℝ) ∨
        X ≤ 2 * Real.rpow M ((3 : ℝ) / 4)) →
      A ≤
        (Real.rpow w ((1 : ℝ) / 6) * Real.sqrt (2 * M) +
            2 * Real.rpow M ((3 : ℝ) / 4)) / Real.sqrt (100 : ℝ) +
          2 * Real.rpow σ ((1 : ℝ) / 3) /
            Real.rpow (100 : ℝ) ((1 : ℝ) / 3)) := by
  intro hsolver
  exact theorem1_average_level_first_case_scalar_interface_false (by
    intro A X M w G σ hA_nonneg hA_root hA_G hX_nonneg hM_nonneg hw_nonneg
      hσ_nonneg hw_ge_two hX_G hfirst
    exact hsolver A X M w G σ hA_nonneg hA_root hA_G hX_nonneg hM_nonneg
      hw_nonneg hσ_nonneg hw_ge_two hX_G (Or.inl hfirst))

/-- Parameterized first-branch obstruction at the actual Theorem 1 `w` formula.

The values `b = 1/4` and `G = 8` give the displayed parameter branch
`w = G² * (28b + 1/(7b²))³ / 64 = (65/7)³`.  Even at this parameterized
shape, the average-level facts currently exposed to the final source step
(`A ≤ X/√T`, `A ≤ G`, and the normalized first branch) do not imply the
printed RHS.  This rules out repairing `hsource_final` by merely unfolding the
closed-form `w` selector; an additional source invariant or a correction of
the paper's last displayed comparison is still needed. -/
private theorem theorem1_parameterized_first_branch_average_interface_false :
    ¬ (∀ A X : ℝ,
      0 ≤ A →
      A ≤ X / Real.sqrt (1000000 : ℝ) →
      A ≤ 8 →
      X / Real.sqrt (1000000 : ℝ) ≤
        (Real.sqrt (2 * (19000 : ℝ)) *
            Real.rpow (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
              ((1 : ℝ) / 6)) /
          Real.sqrt (1000000 : ℝ) →
      A ≤
        (Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) *
            Real.sqrt (2 * (19000 : ℝ)) +
            2 * Real.rpow (19000 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (1000000 : ℝ) +
          2 * Real.rpow (64 : ℝ) ((1 : ℝ) / 3) /
            Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3)) := by
  intro hsolver
  have hsqrtT : Real.sqrt (1000000 : ℝ) = 1000 := by norm_num
  have hTthird_pos :
      0 < Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < (1000000 : ℝ)) ((1 : ℝ) / 3)
  have hTthird_gt : (99 : ℝ) < Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) := by
    have hleft_nonneg : 0 ≤ (99 : ℝ) := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (1000000 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (1000000 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (99 : ℝ) (3 : ℝ) < (1000000 : ℝ) := by
        norm_num [Real.rpow_natCast]
      _ = Real.rpow (Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) :=
        hpow.symm
  have h64_third_lt : Real.rpow (64 : ℝ) ((1 : ℝ) / 3) < (5 : ℝ) := by
    have hleft_nonneg :
        0 ≤ Real.rpow (64 : ℝ) ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by norm_num) ((1 : ℝ) / 3)
    have hright_nonneg : 0 ≤ (5 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 3)]
    have hpow :
        Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (64 : ℝ) := by
      simpa using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (64 : ℝ))
          ((1 : ℝ) / 3) (3 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (64 : ℝ) ((1 : ℝ) / 3)) (3 : ℝ) =
          (64 : ℝ) := hpow
      _ < Real.rpow (5 : ℝ) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hw_sixth_lt :
      Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) < 4 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by positivity) ((1 : ℝ) / 6)
    have hright_nonneg : 0 ≤ (4 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow
            (Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6)) (6 : ℝ) =
          ((65 : ℝ) / 7) ^ 3 := by
      simpa using
        (Real.rpow_mul (by positivity : 0 ≤ (((65 : ℝ) / 7) ^ 3))
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow
          (Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6)) (6 : ℝ) =
          ((65 : ℝ) / 7) ^ 3 := hpow
      _ < Real.rpow (4 : ℝ) (6 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hsqrt38000_lt : Real.sqrt (38000 : ℝ) < 200 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (200 : ℝ))]
    norm_num
  have hM34_lt :
      Real.rpow (19000 : ℝ) ((3 : ℝ) / 4) < 2000 := by
    have hleft_nonneg :
        0 ≤ Real.rpow (19000 : ℝ) ((3 : ℝ) / 4) :=
      Real.rpow_nonneg (by norm_num) ((3 : ℝ) / 4)
    have hright_nonneg : 0 ≤ (2000 : ℝ) := by norm_num
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 4)]
    have hpow :
        Real.rpow (Real.rpow (19000 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (19000 : ℝ) ^ 3 := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (19000 : ℝ))
          ((3 : ℝ) / 4) (4 : ℝ)).symm
    calc
      Real.rpow (Real.rpow (19000 : ℝ) ((3 : ℝ) / 4)) (4 : ℝ) =
          (19000 : ℝ) ^ 3 := hpow
      _ < Real.rpow (2000 : ℝ) (4 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hbase_sixth_gt :
      (42 : ℝ) <
        Real.rpow
          (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
          ((1 : ℝ) / 6) := by
    have hleft_nonneg : 0 ≤ (42 : ℝ) := by norm_num
    have hright_nonneg :
        0 ≤ Real.rpow
          (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
          ((1 : ℝ) / 6) :=
      Real.rpow_nonneg (by positivity) ((1 : ℝ) / 6)
    rw [← Real.rpow_lt_rpow_iff hleft_nonneg hright_nonneg
      (by norm_num : (0 : ℝ) < 6)]
    have hpow :
        Real.rpow
            (Real.rpow
              (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
              ((1 : ℝ) / 6)) (6 : ℝ) =
          ((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2 := by
      simpa using
        (Real.rpow_mul
          (by positivity :
            0 ≤ ((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
          ((1 : ℝ) / 6) (6 : ℝ)).symm
    calc
      Real.rpow (42 : ℝ) (6 : ℝ) <
          ((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2 := by
        norm_num [Real.rpow_natCast]
      _ =
          Real.rpow
            (Real.rpow
              (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
              ((1 : ℝ) / 6)) (6 : ℝ) := hpow.symm
  have hsqrt38000_gt : (191 : ℝ) < Real.sqrt (38000 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ (191 : ℝ))]
    norm_num
  have hroot_branch :
      (8000 : ℝ) / Real.sqrt (1000000 : ℝ) ≤
        (Real.sqrt (2 * (19000 : ℝ)) *
            Real.rpow (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
              ((1 : ℝ) / 6)) /
          Real.sqrt (1000000 : ℝ) := by
    rw [show 2 * (19000 : ℝ) = 38000 by norm_num, hsqrtT]
    have hprod_gt :
        (8000 : ℝ) <
          Real.sqrt (38000 : ℝ) *
            Real.rpow
              (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
              ((1 : ℝ) / 6) := by
      have hmul :
          (191 : ℝ) * 42 <
            Real.sqrt (38000 : ℝ) *
              Real.rpow
                (((65 : ℝ) / 7) ^ 3 + 2 * (1000000 : ℝ) * (64 : ℝ) ^ 2)
                ((1 : ℝ) / 6) :=
        mul_lt_mul hsqrt38000_gt (le_of_lt hbase_sixth_gt)
          (by norm_num) (by norm_num)
      norm_num at hmul ⊢
      nlinarith
    nlinarith
  have hbad :=
    hsolver 6 8000 (by norm_num) (by rw [hsqrtT]; norm_num) (by norm_num)
      hroot_branch
  have hdet_lt :
      Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) *
          Real.sqrt (2 * (19000 : ℝ)) / Real.sqrt (1000000 : ℝ) <
        (4 : ℝ) / 5 := by
    rw [show 2 * (19000 : ℝ) = 38000 by norm_num, hsqrtT]
    have hprod_lt :
        Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) *
            Real.sqrt (38000 : ℝ) <
          (4 : ℝ) * 200 := by
      calc
        Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) *
            Real.sqrt (38000 : ℝ) <
          4 * Real.sqrt (38000 : ℝ) := by
            exact mul_lt_mul_of_pos_right hw_sixth_lt
              (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 38000))
        _ < 4 * 200 := by
            exact mul_lt_mul_of_pos_left hsqrt38000_lt (by norm_num)
    nlinarith
  have hMterm_lt :
      (2 * Real.rpow (19000 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (1000000 : ℝ) < 4 := by
    rw [hsqrtT]
    nlinarith [hM34_lt]
  have hnoise_lt :
      2 * Real.rpow (64 : ℝ) ((1 : ℝ) / 3) /
          Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) <
        (1 : ℝ) / 8 := by
    have hnum_lt : 2 * Real.rpow (64 : ℝ) ((1 : ℝ) / 3) < 10 := by
      nlinarith [h64_third_lt]
    have hstep1 :
        2 * Real.rpow (64 : ℝ) ((1 : ℝ) / 3) /
            Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) <
          10 / Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) :=
      div_lt_div_of_pos_right hnum_lt hTthird_pos
    have hstep2 :
        10 / Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) <
          10 / 99 := by
      exact div_lt_div_of_pos_left (by norm_num) (by norm_num) hTthird_gt
    have hratio_lt := lt_trans hstep1 hstep2
    have hten99_lt : (10 : ℝ) / 99 < 1 / 8 := by norm_num
    exact lt_trans hratio_lt hten99_lt
  have hRHS_lt :
      (Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) *
            Real.sqrt (2 * (19000 : ℝ)) +
            2 * Real.rpow (19000 : ℝ) ((3 : ℝ) / 4)) /
          Real.sqrt (1000000 : ℝ) +
          2 * Real.rpow (64 : ℝ) ((1 : ℝ) / 3) /
            Real.rpow (1000000 : ℝ) ((1 : ℝ) / 3) <
        (6 : ℝ) := by
    have hsplit :
        (Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) *
              Real.sqrt (2 * (19000 : ℝ)) +
              2 * Real.rpow (19000 : ℝ) ((3 : ℝ) / 4)) /
            Real.sqrt (1000000 : ℝ) =
          Real.rpow (((65 : ℝ) / 7) ^ 3) ((1 : ℝ) / 6) *
              Real.sqrt (2 * (19000 : ℝ)) /
            Real.sqrt (1000000 : ℝ) +
          (2 * Real.rpow (19000 : ℝ) ((3 : ℝ) / 4)) /
            Real.sqrt (1000000 : ℝ) := by
      ring
    rw [hsplit]
    nlinarith [hdet_lt, hMterm_lt, hnoise_lt]
  exact (not_le_of_gt hRHS_lt) hbad

/-- Corrected scalar final step for Theorem 1.

The paper's two alternatives imply the unsplit penultimate RHS directly.  In
the first branch the nonnegative `2M^(3/4)` term is slack; in the second branch
the nonnegative square-root term is slack.  No invalid replacement of
`2^(2/3) * sqrt M` by `2` is made here. -/
private theorem theorem1_root_sum_case_bound_div_sqrt_le_corrected_rhs
    (S : Setup Ω Sample E) (T : ℕ) (L σ fStar : ℝ)
    (hM : theorem1MScalarBoundary S T L σ fStar)
    (hRHS : theorem1RHSScalarBoundary S T L σ fStar)
    {X : ℝ}
    (hcases :
      X / Real.sqrt (T : ℝ) ≤
          (Real.sqrt (2 * theorem1M S T L σ fStar) *
              Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
            Real.sqrt (T : ℝ) ∨
        X ≤ 2 * Real.rpow (theorem1M S T L σ fStar) ((3 : ℝ) / 4)) :
    X / Real.sqrt (T : ℝ) ≤ theorem1CorrectedRHS S T L σ fStar := by
  let M := theorem1M S T L σ fStar
  let rootT := Real.sqrt (T : ℝ)
  let firstTerm :=
    Real.sqrt (2 * M) *
      Real.rpow (S.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6)
  let secondTerm := 2 * Real.rpow M ((3 : ℝ) / 4)
  have hroot_inv_nonneg : 0 ≤ rootT⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg (T : ℝ))
  have hM_nonneg : 0 ≤ M := by
    simpa [M] using hM.2.2.2.2
  have hsecond_nonneg : 0 ≤ secondTerm := by
    dsimp [secondTerm]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hM_nonneg _)
  have hfirst_nonneg : 0 ≤ firstTerm := by
    have hw_nonneg : 0 ≤ S.w := hM.2.2.2.1
    have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    have hsigma_sq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
    have hbase_nonneg : 0 ≤ S.w + 2 * (T : ℝ) * σ ^ 2 := by
      positivity
    dsimp [firstTerm]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg hbase_nonneg ((1 : ℝ) / 6))
  rcases hcases with hfirst | hsecond
  · have hfirst' : X / rootT ≤ firstTerm / rootT := by
      simpa [M, rootT, firstTerm] using hfirst
    have hslack : firstTerm / rootT ≤ (firstTerm + secondTerm) / rootT := by
      have hbase : firstTerm ≤ firstTerm + secondTerm := by linarith
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hbase hroot_inv_nonneg
    have hmain := le_trans hfirst' hslack
    simpa [theorem1CorrectedRHS, M, rootT, firstTerm, secondTerm] using hmain
  · have hsecond' : X ≤ secondTerm := by
      simpa [M, secondTerm] using hsecond
    have hdiv : X / rootT ≤ secondTerm / rootT := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hsecond' hroot_inv_nonneg
    have hslack : secondTerm / rootT ≤ (firstTerm + secondTerm) / rootT := by
      have hbase : secondTerm ≤ firstTerm + secondTerm := by linarith
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hbase hroot_inv_nonneg
    have hmain := le_trans hdiv hslack
    simpa [theorem1CorrectedRHS, M, rootT, firstTerm, secondTerm] using hmain

/-- Source/coarser supplier for Theorem 1's totalized scalar inequality.

This is the replacement interface for the long paper proof chain in
`book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/12-31`.
It sits above the retired local-only Lemma 2 route: Lemma 2 is consumed through
the generated Algorithm 1 quotient boundary, Lemma 1 through the generated
source boundary, and Lemma 4 through the displayed logarithmic sum theorem. -/
private theorem theorem1_generated_average_bound_from_source_chain
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (hT : 0 < T) (b L G σ fStar : ℝ)
    (hb : 0 < b) (hGpos : 0 < G) (hLpos : 0 < L) (hsigma : 0 ≤ σ)
    (hsec3 : Section3Assumptions S μ L G σ fStar) :
    let ST := withTheorem1Parameters S b G L
    (∫ ω,
      SOptLib.finiteUniformAverage
        (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖) ∂μ) ≤
      theorem1CorrectedRHS ST T L σ fStar := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hsec3ST : Section3Assumptions ST μ L G σ fStar := by
    simpa [ST] using section3Assumptions_withTheorem1Parameters S μ hsec3 b
  have hgeneratedScalar : generatedStepsizeScalarBoundary ST := by
    simpa [ST] using
      theorem1_generated_stepsize_scalar_boundary_of_positive S hb hGpos hLpos
  have hk_pos : 0 < ST.k := by
    simpa [ST] using theorem1_parameterized_k_pos_of_positive S hb hGpos hLpos
  have hgeneratedQuot : generatedStepsizeQuotientBoundary ST := by
    exact ⟨hgeneratedScalar, hk_pos⟩
  have hM : theorem1MScalarBoundary ST T L σ fStar := by
    simpa [ST] using
      theorem1M_scalar_boundary_of_positive
        S μ T b L G σ fStar hb hGpos hLpos hsec3ST
  have hRHS : theorem1RHSScalarBoundary ST T L σ fStar := by
    simpa [ST] using
      theorem1RHS_scalar_boundary_of_positive
        S μ T b L G σ fStar hT hb hGpos hLpos hsigma hsec3ST
  have hEq4Scalar : theorem1Equation4ScalarBoundary ST L G := by
    simpa [ST] using theorem1_equation4_scalar_boundary_of_positive S hb hGpos hLpos
  have hlemma2_route :
      ∀ t, sourceExpectationLE μ (lemma2LHSExpr ST t) (lemma2RHSExpr ST L t) := by
    intro t
    exact lemma2_error_recurrence ST μ hsec3ST t hgeneratedQuot
  have hlemma4_route :
      ∀ (a₀ : ℝ) (a : ℕ → ℝ) (N : ℕ),
        0 < a₀ →
          (∀ t, t ∈ Finset.Icc 1 N → 0 ≤ a t) →
            (Finset.sum (Finset.Icc 1 N)
              (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
                Real.log (1 + Finset.sum (Finset.Icc 1 N) a / a₀) := by
    intro a₀ a N ha₀ ha_nonneg
    exact lemma4_log_sum_bound a₀ a N ha₀ ha_nonneg
  have hlemma1_route :
      ∀ t,
        (∀ s, sourceStepsizeLE ST s ((1 : ℝ) / (4 * L))) →
          sourceExpectationLE μ (lemma1LHSExpr ST t) (lemma1RHSExpr ST t) := by
    intro t heta
    exact
      lemma1_biased_sgd_descent_of_generated_quotient_boundary
        ST μ hsec3ST hgeneratedQuot hLpos t heta
  have hEquation4 :
      theorem1Equation4ErrorIncrementLHS ST μ T L ≤ theorem1Equation4RHS ST μ T L :=
    theorem1_equation4_error_increment_bound
      ST μ hsec3ST T hgeneratedQuot hEq4Scalar hlemma2_route hlemma4_route
  have hweighted :
      theorem1WeightedGradientNormSqSum ST μ T ≤
        ST.k * theorem1M ST T L σ fStar :=
    theorem1_weighted_gradient_bound_final
      ST μ T hsec3ST hgeneratedQuot hEq4Scalar
      hlemma1_route hEquation4
  have hroot_cases :
      theorem1ExpectedRootGradientNormSqSum ST μ T / Real.sqrt (T : ℝ) ≤
          (Real.sqrt (2 * theorem1M ST T L σ fStar) *
              Real.rpow (ST.w + 2 * (T : ℝ) * σ ^ 2) ((1 : ℝ) / 6)) /
            Real.sqrt (T : ℝ) ∨
        theorem1ExpectedRootGradientNormSqSum ST μ T ≤
          2 * Real.rpow (theorem1M ST T L σ fStar) ((3 : ℝ) / 4) :=
    theorem1_expected_root_sum_bound S μ T b L G σ fStar hsec3
      (by simpa [ST] using hgeneratedScalar)
      (by simpa [ST] using hk_pos)
      (by simpa [ST] using hM)
      (by simpa [ST] using hRHS)
      hweighted
  have havg_root :
      (∫ ω,
        SOptLib.finiteUniformAverage
          (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖) ∂μ) ≤
        theorem1ExpectedRootGradientNormSqSum ST μ T / Real.sqrt (T : ℝ) :=
    theorem1_generated_average_le_expected_root_sum_div_sqrt
      ST μ T hsec3ST hRHS
  have hsource_final :
      (∫ ω,
        SOptLib.finiteUniformAverage
          (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖) ∂μ) ≤
        theorem1CorrectedRHS ST T L σ fStar := by
    have hroot_corrected :
        theorem1ExpectedRootGradientNormSqSum ST μ T / Real.sqrt (T : ℝ) ≤
          theorem1CorrectedRHS ST T L σ fStar :=
      theorem1_root_sum_case_bound_div_sqrt_le_corrected_rhs
        ST T L σ fStar hM hRHS hroot_cases
    exact le_trans havg_root hroot_corrected
  exact hsource_final

/-- The Theorem 1 source average value supplies the exact finite-horizon
integrability needed by the selected-output expectation bridge. -/
theorem theorem1_selected_output_equality_of_expected_average_value
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d)) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (T : ℕ) (hT : 0 < T) (b L G σ fStar : ℝ)
    (hgenerated :
      generatedStepsizeScalarBoundary (withTheorem1Parameters S b G L)) {lhs : ℝ}
    (havg : sourceExpectedAverageGradientNormValue (withTheorem1Parameters S b G L) μ T =
      some lhs) :
    sourceRandomOutputGradientNormExpectationValue (withTheorem1Parameters S b G L) μ T hT =
      sourceExpectedAverageGradientNormValue (withTheorem1Parameters S b G L) μ T := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hboundary : generatedStepsizeScalarBoundary ST := by
    simpa [ST] using hgenerated
  have hgrad_int :
      ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient ST (iterate ST i.val ω)‖) μ :=
    sourceExpectedAverageGradientNormValue_some_to_fiber_integrable
      ST μ T hboundary havg
  exact
    sourceRandomOutputGradientNormExpectationValue_eq_sourceExpectedAverage
      ST μ T hT hboundary hgrad_int

/-- Corrected Theorem 1 under transparent scalar-domain corrections.

This theorem deliberately concludes with `theorem1CorrectedRHS`, the valid
penultimate bound on p. 8, rather than `theorem1RHS`, whose final printed
simplification drops a `sqrt M` factor.  The source-facing run is related to
the generated finite-average integral, and the corrected RHS is stated directly
so it cannot be confused with the paper's erroneous `theorem1RHSSourceValue`.

Source: `book/STORM/StochasticRecursiveMomentum.json#/main_theorem` states only
Section 3 assumptions and `b > 0` before the displayed scalar formulas; the
displayed formulas contain quotients, non-integer powers, square roots, and the
generated adaptive stepsizes.  The extra `0 < G`, `0 < L`, and `0 ≤ σ`
premises are the transparent B-track domain corrections needed for those
source expressions. -/
theorem theorem1_expected_gradient_norm_bound_admissible_scalar_corrected
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    {d : ℕ} (S : Setup Ω Sample (DecisionSpace d)) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (hT : 0 < T) (b L G σ fStar : ℝ)
    (hb : 0 < b) (hGpos : 0 < G) (hLpos : 0 < L) (hsigma : 0 ≤ σ)
    (hsec3 : Section3Assumptions S μ L G σ fStar) :
    let ST := withTheorem1Parameters S b G L
    sourceRandomOutputGradientNormExpectationValue ST μ T hT =
      sourceExpectedAverageGradientNormValue ST μ T ∧
      ∃ lhs,
        sourceExpectedAverageGradientNormValue ST μ T = some lhs ∧
          lhs ≤ theorem1CorrectedRHS ST T L σ fStar := by
  classical
  let ST := withTheorem1Parameters S b G L
  have hsec3ST : Section3Assumptions ST μ L G σ fStar := by
    simpa [ST] using section3Assumptions_withTheorem1Parameters S μ hsec3 b
  have hgenerated : generatedStepsizeScalarBoundary ST := by
    simpa [ST] using
      theorem1_generated_stepsize_scalar_boundary_of_positive S hb hGpos hLpos
  have hgrad_int :
      ∀ i : Fin T, Integrable (fun ω => ‖objectiveGradient ST (iterate ST i.val ω)‖) μ :=
    theorem1_output_window_integrability_from_G_lipschitz ST μ hsec3ST T
  have havg :
      sourceExpectedAverageGradientNormValue ST μ T =
        some
          (∫ ω,
            SOptLib.finiteUniformAverage
              (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖) ∂μ) :=
    sourceExpectedAverageGradientNormValue_eq_some_generated_average_of_boundary
      ST μ T hgenerated hgrad_int
  have hle :
      (∫ ω,
        SOptLib.finiteUniformAverage
          (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖) ∂μ) ≤
        theorem1CorrectedRHS ST T L σ fStar :=
    theorem1_generated_average_bound_from_source_chain
      S μ T hT b L G σ fStar hb hGpos hLpos hsigma hsec3
  have hbound :
      ∃ lhs,
        sourceExpectedAverageGradientNormValue ST μ T = some lhs ∧
          lhs ≤ theorem1CorrectedRHS ST T L σ fStar := by
    exact
      ⟨∫ ω,
          SOptLib.finiteUniformAverage
            (fun i : Fin T => ‖objectiveGradient ST (iterate ST i.val ω)‖) ∂μ,
        havg, hle⟩
  refine ⟨?_, hbound⟩
  exact
    theorem1_selected_output_equality_of_expected_average_value
      S μ T hT b L G σ fStar
      (by simpa [ST] using hgenerated) havg

end Setup

end Algorithms.Unverified.StochasticRecursiveMomentum
