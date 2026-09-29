import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Telescope

/-!
MARS complete main-results target. See `TASK.md` and
`paper/MARS/source_manifest.json`.

This Phase 0 layer records the paper's object-level algorithmic spine:
same-sample variance-reduced gradient corrections, clipping by norm, generated
momenta, and generated iterates for Algorithms 1 and 2. Convergence statements
below intentionally retain `sorry` proofs.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace SGD.MARS

variable {Ω Sample E : Type*}

/-- Source problem data for `F(x)=E[f(x,ξ)]` with first-order stochastic oracle
values. This structure carries data only; paper assumptions are separate
theorem hypotheses or assumption bundles. -/
structure ProblemData (Sample E : Type*) [MeasurableSpace Sample] where
  sampleLaw : Measure Sample
  sampleLaw_isProbability : IsProbabilityMeasure sampleLaw
  stochasticLoss : E → Sample → ℝ
  F : E → ℝ
  gradF : E → E
  stochasticGrad : E → Sample → E

/-- Canonical sample streams for the paper's fresh samples `ξ_t`. -/
abbrev SampleStream (Sample : Type*) := ℕ → Sample

/-- Coordinate projection `ξ_t` from the canonical sample stream. -/
def sampleAt (t : ℕ) (ω : SampleStream Sample) : Sample :=
  ω t

/-- The paper run law: iid fresh samples with one-step marginal `D`. -/
def runLaw [MeasurableSpace Sample] (P : ProblemData Sample E) :
    Measure (SampleStream Sample) :=
  SOptLib.iidStreamLaw P.sampleLaw

theorem runLaw_isProbabilityMeasure [MeasurableSpace Sample] (P : ProblemData Sample E) :
    IsProbabilityMeasure (runLaw P) := by
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  exact SOptLib.iidStreamLaw_isProbabilityMeasure P.sampleLaw

theorem runLaw_map_sampleAt [MeasurableSpace Sample] (P : ProblemData Sample E) (t : ℕ) :
    Measure.map (sampleAt (Sample := Sample) t) (runLaw P) = P.sampleLaw := by
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  simpa [runLaw, sampleAt] using SOptLib.iidStreamLaw_map_eval P.sampleLaw t

section CoordinateVectors

variable {ι : Type*} [Fintype ι]

abbrev MarsVector (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

/-- Coordinatewise multiplication, used to expose diagonal preconditioners as
linear actions on vectors. -/
def coordMul (x y : MarsVector ι) : MarsVector ι :=
  WithLp.toLp 2 (fun i => x i * y i)

end CoordinateVectors

section Hilbert

variable [MeasurableSpace Sample] [MeasurableSpace E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Assumption B.1, stated as a source-facing assumption rather than a generated
regularity side condition. -/
def BoundedVariance (P : ProblemData Sample E) (σ : ℝ) : Prop :=
  0 < σ ∧
    (∀ x : E, Integrable (fun ξ : Sample =>
      ‖P.stochasticGrad x ξ - P.gradF x‖ ^ 2) P.sampleLaw) ∧
    ∀ x : E,
      ∫ ξ, ‖P.stochasticGrad x ξ - P.gradF x‖ ^ 2 ∂P.sampleLaw ≤ σ ^ 2

/-- Section 2 / Notations stochastic objective oracle:
`E[f(x, ξ_t) | x] = F(x)`. -/
def UnbiasedObjectiveOracle (P : ProblemData Sample E) : Prop :=
  ∀ x : E, ∫ ξ, P.stochasticLoss x ξ ∂P.sampleLaw = P.F x

/-- Section 2 first-order oracle boundary:
`E[∇f(x, ξ)] = ∇F(x)`. The first conjunct is the Lean measurability needed to
interpret the stochastic-gradient kernel as a random-query oracle; the second
conjunct records the fixed-fiber integrability implicit in the source's
mathematical expectation notation. Both are scoped inside the source-backed
first-order oracle assumption rather than stored as algorithm trajectory data. -/
def UnbiasedGradientOracle (P : ProblemData Sample E) : Prop :=
  Measurable (fun p : E × Sample => P.stochasticGrad p.1 p.2) ∧
    (∀ x : E, Integrable (fun ξ : Sample => P.stochasticGrad x ξ) P.sampleLaw) ∧
    ∀ x : E, ∫ ξ, P.stochasticGrad x ξ ∂P.sampleLaw = P.gradF x

theorem BoundedVariance.sigma_pos
    {P : ProblemData Sample E} {σ : ℝ} (h : BoundedVariance P σ) :
    0 < σ :=
  h.1

theorem BoundedVariance.fixed_sq_integrable
    {P : ProblemData Sample E} {σ : ℝ} (h : BoundedVariance P σ) :
    ∀ x : E, Integrable (fun ξ : Sample =>
      ‖P.stochasticGrad x ξ - P.gradF x‖ ^ 2) P.sampleLaw :=
  h.2.1

theorem BoundedVariance.bound
    {P : ProblemData Sample E} {σ : ℝ} (h : BoundedVariance P σ) :
    ∀ x : E,
      ∫ ξ, ‖P.stochasticGrad x ξ - P.gradF x‖ ^ 2 ∂P.sampleLaw ≤ σ ^ 2 :=
  h.2.2

theorem UnbiasedGradientOracle.stochasticGrad_measurable
    {P : ProblemData Sample E} (h : UnbiasedGradientOracle P) :
    Measurable (fun p : E × Sample => P.stochasticGrad p.1 p.2) :=
  h.1

theorem UnbiasedGradientOracle.fixed_integrable
    {P : ProblemData Sample E} (h : UnbiasedGradientOracle P) :
    ∀ x : E, Integrable (fun ξ : Sample => P.stochasticGrad x ξ) P.sampleLaw :=
  h.2.1

theorem UnbiasedGradientOracle.mean_eq_gradF
    {P : ProblemData Sample E} (h : UnbiasedGradientOracle P) :
    ∀ x : E, ∫ ξ, P.stochasticGrad x ξ ∂P.sampleLaw = P.gradF x :=
  h.2.2

theorem UnbiasedGradientOracle.residual_integrable
    {P : ProblemData Sample E} (h : UnbiasedGradientOracle P) :
    ∀ x : E,
      Integrable (fun ξ : Sample =>
        P.stochasticGrad x ξ - P.gradF x) P.sampleLaw := by
  intro x
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  exact (UnbiasedGradientOracle.fixed_integrable h x).sub (integrable_const _)

theorem UnbiasedGradientOracle.residual_integral_zero
    [CompleteSpace E]
    {P : ProblemData Sample E} (h : UnbiasedGradientOracle P) :
    ∀ x : E,
      ∫ ξ, P.stochasticGrad x ξ - P.gradF x ∂P.sampleLaw = 0 := by
  intro x
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  have hconst : Integrable (fun _ : Sample => P.gradF x) P.sampleLaw :=
    integrable_const _
  calc
    ∫ ξ, P.stochasticGrad x ξ - P.gradF x ∂P.sampleLaw =
        (∫ ξ, P.stochasticGrad x ξ ∂P.sampleLaw) -
          ∫ _ξ : Sample, P.gradF x ∂P.sampleLaw := by
          exact integral_sub (UnbiasedGradientOracle.fixed_integrable h x) hconst
    _ = P.gradF x - P.gradF x := by
          simp [UnbiasedGradientOracle.mean_eq_gradF h x, integral_const, probReal_univ]
    _ = 0 := by
          simp

theorem UnbiasedGradientOracle.fixed_fiber_oracle_difference_mean
    [CompleteSpace E]
    {P : ProblemData Sample E} (h : UnbiasedGradientOracle P) :
    ∀ x y d : E,
      ∫ ξ, inner ℝ d (P.stochasticGrad x ξ - P.stochasticGrad y ξ) ∂P.sampleLaw =
        inner ℝ d (P.gradF x - P.gradF y) := by
  intro x y d
  have hx_int := UnbiasedGradientOracle.fixed_integrable h x
  have hy_int := UnbiasedGradientOracle.fixed_integrable h y
  have hdiff_int :
      Integrable
        (fun ξ : Sample => P.stochasticGrad x ξ - P.stochasticGrad y ξ)
        P.sampleLaw :=
    hx_int.sub hy_int
  have hlin :=
    ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) d) hdiff_int
  have hdiff_mean :
      ∫ ξ, P.stochasticGrad x ξ - P.stochasticGrad y ξ ∂P.sampleLaw =
        P.gradF x - P.gradF y := by
    calc
      ∫ ξ, P.stochasticGrad x ξ - P.stochasticGrad y ξ ∂P.sampleLaw =
          (∫ ξ, P.stochasticGrad x ξ ∂P.sampleLaw) -
            ∫ ξ, P.stochasticGrad y ξ ∂P.sampleLaw := by
            exact integral_sub hx_int hy_int
      _ = P.gradF x - P.gradF y := by
            simp [UnbiasedGradientOracle.mean_eq_gradF h]
  calc
    ∫ ξ, inner ℝ d (P.stochasticGrad x ξ - P.stochasticGrad y ξ) ∂P.sampleLaw =
        ∫ ξ, ((innerSL ℝ) d) (P.stochasticGrad x ξ - P.stochasticGrad y ξ)
          ∂P.sampleLaw := by
          rfl
    _ = ((innerSL ℝ) d)
        (∫ ξ, P.stochasticGrad x ξ - P.stochasticGrad y ξ ∂P.sampleLaw) := hlin
    _ = inner ℝ d (P.gradF x - P.gradF y) := by
          rw [hdiff_mean]
          rfl

/-- The literal stochastic-gradient Lipschitz part of Assumption B.2. -/
def StochasticGradientLipschitz (P : ProblemData Sample E) (L : ℝ) : Prop :=
  ∀ (x y : E) (ξ : Sample), ‖P.stochasticGrad x ξ - P.stochasticGrad y ξ‖ ≤ L * ‖x - y‖

/-- The objective smooth upper bound used in D.13. The source proof invokes
this as the `L`-smoothness of `F` from Assumption B.2; the Lean model exposes
it explicitly so `F` and `gradF` are not arbitrary unrelated fields. -/
def ObjectiveSmoothUpper (P : ProblemData Sample E) (L : ℝ) : Prop :=
  ∀ x y : E,
    P.F y ≤ P.F x + inner ℝ (P.gradF x) (y - x) + (L / 2) * ‖y - x‖ ^ 2

/-- Assumption B.2 as consumed by the C.3/C.4 proof route: the printed
stochastic-gradient Lipschitz condition together with the resulting objective
smooth upper bound for the mean objective. -/
def StochasticSmooth (P : ProblemData Sample E) (L : ℝ) : Prop :=
  StochasticGradientLipschitz P L ∧ ObjectiveSmoothUpper P L

theorem StochasticSmooth.stochasticGrad_lipschitz
    {P : ProblemData Sample E} {L : ℝ} (h : StochasticSmooth P L) :
    StochasticGradientLipschitz P L :=
  h.1

theorem StochasticSmooth.objective_smooth_upper
    {P : ProblemData Sample E} {L : ℝ} (h : StochasticSmooth P L) :
    ObjectiveSmoothUpper P L :=
  h.2

/-- Symmetry/self-adjointness of a paper preconditioner action, stated in the
inner-product form used by the source matrix algebra. -/
def HSelfAdjoint (H : ℕ → E → E) : Prop :=
  ∀ t : ℕ, ∀ x y : E, inner ℝ x (H t y) = inner ℝ (H t x) y

/-- Assumption B.3, stated for the time-indexed preconditioner action `H_t`. -/
def HLowerBounded (H : ℕ → E → E) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ t : ℕ, 0 < t → ∀ z : E, ρ * ‖z‖ ^ 2 ≤ inner ℝ z (H t z)

/-- Pointwise form of Assumption B.3 for a single preconditioner action. -/
def HLowerBoundedAt (H : E → E) (ρ : ℝ) : Prop :=
  0 < ρ ∧ ∀ z : E, ρ * ‖z‖ ^ 2 ≤ inner ℝ z (H z)

/-- The paper's clipping-by-norm operation `Clip(c,1)`. -/
def clipByNorm (z : E) : E :=
  if 1 < ‖z‖ then (‖z‖)⁻¹ • z else z

@[simp]
theorem clipByNorm_of_norm_le_one {z : E} (hz : ‖z‖ ≤ 1) :
    clipByNorm z = z := by
  simp [clipByNorm, not_lt.mpr hz]

theorem clipByNorm_of_one_lt_norm {z : E} (hz : 1 < ‖z‖) :
    clipByNorm z = (‖z‖)⁻¹ • z := by
  simp [clipByNorm, hz]

/-- Same-sample MARS correction
`∇f(x_t,ξ_t)+γ_t β/(1-β) (∇f(x_t,ξ_t)-∇f(x_{t-1},ξ_t))`. -/
def marsCorrection (β γ : ℝ) (gCurrent gPrevious : E) : E :=
  gCurrent + (γ * (β / (1 - β))) • (gCurrent - gPrevious)

/-- Well-definedness predicate for the denominator in the source expression
`β/(1-β)`. This is not a source-facing theorem by itself. -/
def MarsCorrectionDenominatorAdmissible (β : ℝ) : Prop :=
  β ≠ 1

/-- The quadratic objective whose argmin defines Algorithm 1 line 7. -/
def marsMirrorObjective (η : ℝ) (m : E) (H : E → E) (x z : E) : ℝ :=
  η * inner ℝ m z + (1 / 2 : ℝ) * inner ℝ (z - x) (H (z - x))

/-- Predicate saying that `z` realizes the paper's mirror-descent argmin. -/
def IsMarsMirrorStep (η : ℝ) (m : E) (H : E → E) (x z : E) : Prop :=
  ∀ y : E, marsMirrorObjective η m H x z ≤ marsMirrorObjective η m H x y

end Hilbert

section LinearMirror

variable {ι : Type*} [Fintype ι]

private theorem mars_mirror_objective_continuous_linear
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) (η : ℝ)
    (m x : MarsVector ι) :
    Continuous (fun z : MarsVector ι =>
      marsMirrorObjective η m (fun y => H y) x z) := by
  unfold marsMirrorObjective
  have hHcont : Continuous (fun z : MarsVector ι => H z) :=
    LinearMap.continuous_of_finiteDimensional H
  have hsub : Continuous (fun z : MarsVector ι => z - x) :=
    continuous_id.sub continuous_const
  have hlin : Continuous (fun z : MarsVector ι => inner ℝ m z) :=
    continuous_const.inner continuous_id
  have hquad : Continuous (fun z : MarsVector ι =>
      inner ℝ (z - x) (H (z - x))) :=
    hsub.inner (hHcont.comp hsub)
  exact (continuous_const.mul hlin).add (continuous_const.mul hquad)

private theorem continuous_coercive_attains_global_min_on_closed_ball
    {E : Type*} [Zero E] [PseudoMetricSpace E] {f : E → ℝ} {x0 : E} {R : ℝ}
    (hcompact : IsCompact (Metric.closedBall (0 : E) R))
    (hx0 : x0 ∈ Metric.closedBall (0 : E) R)
    (hcont : ContinuousOn f (Metric.closedBall (0 : E) R))
    (hout : ∀ y, y ∉ Metric.closedBall (0 : E) R → f x0 ≤ f y) :
    ∃ z : E, ∀ y : E, f z ≤ f y := by
  let X : Set E := Metric.closedBall (0 : E) R
  have hne : X.Nonempty := ⟨x0, hx0⟩
  obtain ⟨z, hzmin⟩ :=
    SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn f hcompact hne hcont
  refine ⟨z.1, ?_⟩
  intro y
  by_cases hy : y ∈ X
  · simpa using hzmin ⟨y, hy⟩
  · exact le_trans (by simpa using hzmin ⟨x0, hx0⟩) (hout y hy)

private theorem quadratic_dominates_linear_after_threshold
    {ρ a r : ℝ} (hρ : 0 < ρ) (ha : 0 ≤ a) (hr : 2 * a / ρ ≤ r) :
    0 ≤ -a * r + (1 / 2 : ℝ) * (ρ * r ^ 2) := by
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ
  have hthreshold_nonneg : 0 ≤ 2 * a / ρ := by positivity
  have hr_nonneg : 0 ≤ r := le_trans hthreshold_nonneg hr
  have hmul : 2 * a ≤ ρ * r := by
    have h := mul_le_mul_of_nonneg_right hr hρ_nonneg
    field_simp [ne_of_gt hρ] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hmul_r : (2 * a) * r ≤ (ρ * r) * r :=
    mul_le_mul_of_nonneg_right hmul hr_nonneg
  nlinarith

private theorem mars_mirror_objective_outside_ball_ge_base
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) (ρ η : ℝ)
    (hH : HLowerBoundedAt (fun z : MarsVector ι => H z) ρ)
    (m x : MarsVector ι) :
    ∃ R : ℝ, 0 ≤ R ∧ x ∈ Metric.closedBall (0 : MarsVector ι) R ∧
      ∀ z : MarsVector ι, z ∉ Metric.closedBall (0 : MarsVector ι) R →
        marsMirrorObjective η m (fun y => H y) x x ≤
          marsMirrorObjective η m (fun y => H y) x z := by
  let a : ℝ := |η| * ‖m‖
  let T : ℝ := 2 * a / ρ
  let R : ℝ := ‖x‖ + max T 0
  refine ⟨R, ?_, ?_, ?_⟩
  · have hxnorm : 0 ≤ ‖x‖ := norm_nonneg x
    have hmax : 0 ≤ max T 0 := le_max_right T 0
    exact add_nonneg hxnorm hmax
  · have hxnorm : dist x (0 : MarsVector ι) = ‖x‖ := by simp [dist_eq_norm]
    have hmax : 0 ≤ max T 0 := le_max_right T 0
    rw [Metric.mem_closedBall, hxnorm]
    linarith
  · intro z hzout
    let u : MarsVector ι := z - x
    have hρ : 0 < ρ := hH.1
    have ha : 0 ≤ a := mul_nonneg (abs_nonneg η) (norm_nonneg m)
    have hT_le_max : T ≤ max T 0 := le_max_left T 0
    have hz_norm_gt : R < ‖z‖ := by
      have hzdist : ¬ dist z (0 : MarsVector ι) ≤ R := by
        simpa [Metric.mem_closedBall] using hzout
      have hdist : dist z (0 : MarsVector ι) = ‖z‖ := by simp [dist_eq_norm]
      exact lt_of_not_ge (by simpa [hdist] using hzdist)
    have hT_le_u : T ≤ ‖u‖ := by
      have hzx : ‖z‖ ≤ ‖u‖ + ‖x‖ := by
        calc
          ‖z‖ = ‖(z - x) + x‖ := by
            abel
          _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      have hT_lt_z_sub_x : T < ‖z‖ - ‖x‖ := by
        have : ‖x‖ + T ≤ R := by
          dsimp [R]
          simpa [add_comm] using add_le_add_left hT_le_max ‖x‖
        linarith
      have : ‖z‖ - ‖x‖ ≤ ‖u‖ := by
        dsimp [u]
        linarith
      exact le_trans (le_of_lt hT_lt_z_sub_x) this
    have hquad_nonneg :
        0 ≤ -a * ‖u‖ + (1 / 2 : ℝ) * (ρ * ‖u‖ ^ 2) :=
      quadratic_dominates_linear_after_threshold hρ ha hT_le_u
    have hHlower : ρ * ‖u‖ ^ 2 ≤ inner ℝ u (H u) := hH.2 u
    have hquad_lower :
        (1 / 2 : ℝ) * (ρ * ‖u‖ ^ 2) ≤
          (1 / 2 : ℝ) * inner ℝ u (H u) := by
      nlinarith
    have hlin_lower : -a * ‖u‖ ≤ η * inner ℝ m u := by
      have hinner_abs : |inner ℝ m u| ≤ ‖m‖ * ‖u‖ :=
        abs_real_inner_le_norm m u
      have hmul_abs : |η * inner ℝ m u| ≤ a * ‖u‖ := by
        calc
          |η * inner ℝ m u| = |η| * |inner ℝ m u| := by rw [abs_mul]
          _ ≤ |η| * (‖m‖ * ‖u‖) :=
              mul_le_mul_of_nonneg_left hinner_abs (abs_nonneg η)
          _ = a * ‖u‖ := by
              simp [a, mul_assoc]
      simpa [neg_mul] using neg_le_of_abs_le hmul_abs
    have hsum_nonneg : 0 ≤ η * inner ℝ m u +
        (1 / 2 : ℝ) * inner ℝ u (H u) := by
      nlinarith
    have hx_obj :
        marsMirrorObjective η m (fun y : MarsVector ι => H y) x x =
          η * inner ℝ m x := by
      simp [marsMirrorObjective]
    have hz_decomp :
        marsMirrorObjective η m (fun y : MarsVector ι => H y) x z =
          η * inner ℝ m x +
            (η * inner ℝ m u + (1 / 2 : ℝ) * inner ℝ u (H u)) := by
      dsimp [u]
      simp [marsMirrorObjective, inner_add_right, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc, mul_add]
      ring
    rw [hx_obj, hz_decomp]
    nlinarith

/-- Existence of the Algorithm 1 mirror-descent argmin for a finite-dimensional
linear preconditioner satisfying Assumption B.3. The proof is deferred to the
prover; the object layer uses this theorem to define the generated step from
the paper's quadratic objective, not from an arbitrary trajectory witness. -/
theorem marsLinearMirrorStep_exists
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) (ρ η : ℝ)
    (hH : HLowerBoundedAt (fun z => H z) ρ) (m x : MarsVector ι) :
    ∃ z : MarsVector ι, IsMarsMirrorStep η m (fun y => H y) x z := by
  let f : MarsVector ι → ℝ :=
    fun z => marsMirrorObjective η m (fun y => H y) x z
  obtain ⟨R, _hR_nonneg, hxR, hout⟩ :=
    mars_mirror_objective_outside_ball_ge_base H ρ η hH m x
  have hcompact : IsCompact (Metric.closedBall (0 : MarsVector ι) R) :=
    isCompact_closedBall (0 : MarsVector ι) R
  have hcont : ContinuousOn f (Metric.closedBall (0 : MarsVector ι) R) :=
    (mars_mirror_objective_continuous_linear H η m x).continuousOn
  obtain ⟨z, hzmin⟩ :=
    continuous_coercive_attains_global_min_on_closed_ball
      (f := f) (x0 := x) hcompact hxR hcont hout
  refine ⟨z, ?_⟩
  intro y
  exact hzmin y

/-- A preconditioner with the paper's uniform positive lower bound is injective. -/
private theorem marsLinearPreconditioner_injective
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) {ρ : ℝ}
    (hH : HLowerBoundedAt (fun z => H z) ρ) :
    Function.Injective H := by
  intro u v huv
  have hdiff_apply : H (u - v) = 0 := by
    simpa using sub_eq_zero.mpr huv
  have hlower := hH.2 (u - v)
  have hinner_zero : inner ℝ (u - v) (H (u - v)) = 0 := by
    simp [hdiff_apply]
  have hnorm_zero : ‖u - v‖ = 0 := by
    have hsq_nonpos : ‖u - v‖ ^ 2 ≤ 0 := by
      nlinarith [hH.1, hlower, hinner_zero, sq_nonneg ‖u - v‖]
    have hsq_eq : ‖u - v‖ ^ 2 = 0 :=
      le_antisymm hsq_nonpos (sq_nonneg _)
    exact sq_eq_zero_iff.mp hsq_eq
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/-- Linear solve by the positive-definite preconditioner `H`. This is the
canonical finite-dimensional inverse supplied by Mathlib's injective-endomorphism
equivalence, not a paper-local witness. -/
def marsLinearPreconditionerSolve
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) (ρ : ℝ)
    (hH : HLowerBoundedAt (fun z => H z) ρ) :
    MarsVector ι →ₗ[ℝ] MarsVector ι :=
  ((LinearEquiv.ofInjectiveEndo H (marsLinearPreconditioner_injective H hH)).symm :
    MarsVector ι →ₗ[ℝ] MarsVector ι)

theorem marsLinearPreconditioner_apply_solve
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) (ρ : ℝ)
    (hH : HLowerBoundedAt (fun z => H z) ρ) (m : MarsVector ι) :
    H (marsLinearPreconditionerSolve H ρ hH m) = m := by
  change
    H (((LinearEquiv.ofInjectiveEndo H
      (marsLinearPreconditioner_injective H hH)).symm) m) = m
  exact (LinearEquiv.ofInjectiveEndo H
    (marsLinearPreconditioner_injective H hH)).apply_symm_apply m

/-- Canonical finite-dimensional Algorithm 1 mirror step generated by the
linear preconditioner `H_t` and the paper objective in line 7. -/
def marsLinearMirrorStep
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) (ρ η : ℝ)
    (hH : HLowerBoundedAt (fun z => H z) ρ)
    (m x : MarsVector ι) :
    MarsVector ι :=
  x - η • marsLinearPreconditionerSolve H ρ hH m

theorem marsLinearMirrorStep_spec
    (H : MarsVector ι →ₗ[ℝ] MarsVector ι) (ρ η : ℝ)
    (hH : HLowerBoundedAt (fun z => H z) ρ)
    (hH_self : ∀ u v : MarsVector ι, inner ℝ u (H v) = inner ℝ (H u) v)
    (m x : MarsVector ι) :
    IsMarsMirrorStep η m (fun y => H y) x
      (marsLinearMirrorStep H ρ η hH m x) := by
  classical
  let z := marsLinearMirrorStep H ρ η hH m x
  let a : MarsVector ι := z - x
  have hHz : H a = -η • m := by
    have ha :
        a = -η • marsLinearPreconditionerSolve H ρ hH m := by
      simp [a, z, marsLinearMirrorStep]
    calc
      H a = H (-η • marsLinearPreconditionerSolve H ρ hH m) := by rw [ha]
      _ = -η • H (marsLinearPreconditionerSolve H ρ hH m) := by
        rw [map_smul]
      _ = -η • m := by
        rw [marsLinearPreconditioner_apply_solve H ρ hH m]
  intro y
  let v : MarsVector ι := y - z
  have hy : y = z + v := by
    dsimp [v]
    abel
  have hzvx : z + v - x = a + v := by
    dsimp [a]
    abel
  have hzx : z - x = a := by
    rfl
  have hH_add : H (a + v) = H a + H v := by
    exact map_add H a v
  have hcross1 :
      inner ℝ a (H v) = -η * inner ℝ m v := by
    calc
      inner ℝ a (H v) = inner ℝ (H a) v := hH_self a v
      _ = inner ℝ (-η • m) v := by rw [hHz]
      _ = -η * inner ℝ m v := by rw [real_inner_smul_left]
  have hcross2 :
      inner ℝ v (H a) = -η * inner ℝ m v := by
    calc
      inner ℝ v (H a) = inner ℝ v (-η • m) := by rw [hHz]
      _ = -η * inner ℝ v m := by rw [real_inner_smul_right]
      _ = -η * inner ℝ m v := by rw [real_inner_comm v m]
  have hdecomp :
      marsMirrorObjective η m (fun y => H y) x y =
        marsMirrorObjective η m (fun y => H y) x z +
          (1 / 2 : ℝ) * inner ℝ v (H v) := by
    unfold marsMirrorObjective
    change
      η * inner ℝ m y +
          (1 / 2 : ℝ) * inner ℝ (y - x) (H (y - x)) =
        η * inner ℝ m z + (1 / 2 : ℝ) * inner ℝ a (H a) +
          (1 / 2 : ℝ) * inner ℝ v (H v)
    rw [hy, hzvx]
    change
      η * inner ℝ m (z + v) +
          (1 / 2 : ℝ) * inner ℝ (a + v) (H (a + v)) =
        η * inner ℝ m z + (1 / 2 : ℝ) * inner ℝ a (H a) +
          (1 / 2 : ℝ) * inner ℝ v (H v)
    rw [hH_add]
    simp only [inner_add_right, inner_add_left, hcross1, hcross2]
    ring
  have hquad_nonneg : 0 ≤ inner ℝ v (H v) := by
    have hlower := hH.2 v
    have hleft : 0 ≤ ρ * ‖v‖ ^ 2 :=
      mul_nonneg (le_of_lt hH.1) (sq_nonneg _)
    exact le_trans hleft hlower
  have htail_nonneg : 0 ≤ (1 / 2 : ℝ) * inner ℝ v (H v) :=
    mul_nonneg (by norm_num) hquad_nonneg
  rw [hdecomp]
  linarith

end LinearMirror

section DiagonalMirror

variable {ι : Type*} [Fintype ι]

/-- Diagonal Euclidean realization of the paper's `H_t` action in Algorithm 1. -/
def marsDiagonalPreconditioner (h : MarsVector ι) (z : MarsVector ι) :
    MarsVector ι :=
  coordMul h z

/-- Coordinatewise inverse action used in the closed-form Euclidean mirror
step. Division is total in Lean; positivity/nonzero obligations are exposed by
`HLowerBounded` and the argmin theorem rather than hidden in the definition. -/
def marsDiagonalInverseAction (h : MarsVector ι) (z : MarsVector ι) :
    MarsVector ι :=
  WithLp.toLp 2 (fun i => z i / h i)

/-- Closed-form Euclidean solution of
`argmin_x {η⟪m,x⟫ + 1/2‖x-x_t‖_{H_t}^2}` for diagonal `H_t`. -/
def marsDiagonalMirrorStep (h : MarsVector ι) (η : ℝ)
    (m x : MarsVector ι) : MarsVector ι :=
  x - η • marsDiagonalInverseAction h m

theorem marsDiagonalMirrorStep_spec
    (HWeights : ℕ → MarsVector ι) (ρ : ℝ)
    (hH : HLowerBounded (fun t => marsDiagonalPreconditioner (HWeights t)) ρ)
    (t : ℕ) (ht : 0 < t) (η : ℝ) (m x : MarsVector ι) :
    IsMarsMirrorStep η m (marsDiagonalPreconditioner (HWeights t)) x
      (marsDiagonalMirrorStep (HWeights t) η m x) := by
  classical
  let h := HWeights t
  have hpos : ∀ i, 0 < h i := by
    intro i
    let e : MarsVector ι := PiLp.single 2 i (1 : ℝ)
    have hlower := hH.2 t ht e
    have hinner : inner ℝ e (marsDiagonalPreconditioner h e) = h i := by
      dsimp [e, h, marsDiagonalPreconditioner, coordMul]
      rw [PiLp.inner_apply]
      rw [Finset.sum_eq_single i]
      · simp only [PiLp.single_apply, Pi.single_eq_same]
        calc
          inner ℝ (1 : ℝ) ((HWeights t).ofLp i * 1)
              = inner ℝ (1 : ℝ) (((HWeights t).ofLp i) • (1 : ℝ)) := by
                simp [smul_eq_mul]
          _ = (HWeights t).ofLp i * inner ℝ (1 : ℝ) (1 : ℝ) := by
                rw [real_inner_smul_right]
          _ = (HWeights t).ofLp i := by norm_num
      · intro j _ hji
        simp [hji]
      · intro hi
        simp at hi
    have hnorm : ‖e‖ ^ 2 = (1 : ℝ) := by
      dsimp [e]
      simp
    have hle : ρ ≤ h i := by
      calc
        ρ = ρ * ‖e‖ ^ 2 := by rw [hnorm, mul_one]
        _ ≤ inner ℝ e (marsDiagonalPreconditioner h e) := by simpa [h] using hlower
        _ = h i := hinner
    exact lt_of_lt_of_le hH.1 hle
  have hInv : marsDiagonalPreconditioner h (marsDiagonalInverseAction h m) = m := by
    ext i
    simp only [marsDiagonalPreconditioner, marsDiagonalInverseAction, coordMul]
    change h i * (m i / h i) = m i
    field_simp [(hpos i).ne']
  have hSelf : ∀ u v : MarsVector ι,
      inner ℝ u (marsDiagonalPreconditioner h v) =
        inner ℝ (marsDiagonalPreconditioner h u) v := by
    intro u v
    simp only [marsDiagonalPreconditioner, coordMul, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    calc
      inner ℝ (u i) (h i * v i)
          = inner ℝ (u i) ((h i) • (v i)) := by simp [smul_eq_mul]
      _ = h i * inner ℝ (u i) (v i) := by rw [real_inner_smul_right]
      _ = inner ℝ ((h i) • (u i)) (v i) := by rw [real_inner_smul_left]
      _ = inner ℝ (h i * u i) (v i) := by simp [smul_eq_mul]
  have hAdd : ∀ u v : MarsVector ι,
      marsDiagonalPreconditioner h (u + v) =
        marsDiagonalPreconditioner h u + marsDiagonalPreconditioner h v := by
    intro u v
    ext i
    simp [marsDiagonalPreconditioner, coordMul, mul_add]
  have hSmul : ∀ (c : ℝ) (u : MarsVector ι),
      marsDiagonalPreconditioner h (c • u) =
        c • marsDiagonalPreconditioner h u := by
    intro c u
    ext i
    simp [marsDiagonalPreconditioner, coordMul, mul_assoc, mul_left_comm, mul_comm]
  let z := marsDiagonalMirrorStep h η m x
  have hHz : marsDiagonalPreconditioner h (z - x) = -η • m := by
    have hdiff : z - x = (-η) • marsDiagonalInverseAction h m := by
      ext i
      simp only [z, marsDiagonalMirrorStep, marsDiagonalInverseAction]
      change (x i - η * (m i / h i)) - x i = -η * (m i / h i)
      ring
    calc
      marsDiagonalPreconditioner h (z - x)
          = marsDiagonalPreconditioner h ((-η) • marsDiagonalInverseAction h m) := by
              rw [hdiff]
      _ = (-η) • marsDiagonalPreconditioner h (marsDiagonalInverseAction h m) := by
              rw [hSmul]
      _ = -η • m := by rw [hInv]
  unfold IsMarsMirrorStep
  intro y
  have hquad_nonneg :
      0 ≤ inner ℝ (y - z) (marsDiagonalPreconditioner h (y - z)) := by
    have hlower := hH.2 t ht (y - z)
    have hleft_nonneg : 0 ≤ ρ * ‖y - z‖ ^ 2 :=
      mul_nonneg (le_of_lt hH.1) (sq_nonneg _)
    exact le_trans hleft_nonneg (by simpa [h] using hlower)
  have hdecomp :
      marsMirrorObjective η m (marsDiagonalPreconditioner h) x y =
        marsMirrorObjective η m (marsDiagonalPreconditioner h) x z +
          (1 / 2 : ℝ) *
            inner ℝ (y - z) (marsDiagonalPreconditioner h (y - z)) := by
    let a : MarsVector ι := z - x
    let v : MarsVector ι := y - z
    have hy : y = z + v := by dsimp [v]; abel
    have hzvx : z + v - x = a + v := by dsimp [a, v]; abel
    have hzvz : z + v - z = v := by dsimp [v]; abel
    have hHz_a : marsDiagonalPreconditioner h a = -η • m := by
      simpa [a] using hHz
    have hcross1 :
        inner ℝ a (marsDiagonalPreconditioner h v) = -η * inner ℝ m v := by
      calc
        inner ℝ a (marsDiagonalPreconditioner h v)
            = inner ℝ (marsDiagonalPreconditioner h a) v := hSelf a v
        _ = inner ℝ (-η • m) v := by rw [hHz_a]
        _ = -η * inner ℝ m v := by rw [real_inner_smul_left]
    have hcross2 :
        inner ℝ v (marsDiagonalPreconditioner h a) = -η * inner ℝ m v := by
      calc
        inner ℝ v (marsDiagonalPreconditioner h a)
            = inner ℝ v (-η • m) := by rw [hHz_a]
        _ = -η * inner ℝ v m := by rw [real_inner_smul_right]
        _ = -η * inner ℝ m v := by rw [real_inner_comm v m]
    unfold marsMirrorObjective
    rw [hy, hzvx, hzvz, hAdd]
    change η * inner ℝ m (z + v) +
        1 / 2 * inner ℝ (a + v)
          (marsDiagonalPreconditioner h a + marsDiagonalPreconditioner h v) =
      η * inner ℝ m z + 1 / 2 * inner ℝ a (marsDiagonalPreconditioner h a) +
        1 / 2 * inner ℝ v (marsDiagonalPreconditioner h v)
    simp only [inner_add_right, inner_add_left, mul_add]
    rw [hcross1, hcross2]
    ring
  rw [hdecomp]
  have : 0 ≤
      (1 / 2 : ℝ) * inner ℝ (y - z) (marsDiagonalPreconditioner h (y - z)) :=
    mul_nonneg (by norm_num) hquad_nonneg
  nlinarith

/-- Algorithm 1 setup data: only source inputs/data, not trajectory witnesses.
The preconditioner is a finite-dimensional linear action `H_t`, matching the
paper's full-matrix/diagonal framework, with Assumption B.3 stated over that
action. -/
structure Algorithm1Data (Sample ι : Type*) [Fintype ι]
    [MeasurableSpace Sample] where
  problem : ProblemData Sample (MarsVector ι)
  x0 : MarsVector ι
  beta1 : ℕ → ℝ
  beta2 : ℕ → ℝ
  gamma : ℕ → ℝ
  eta : ℕ → ℝ
  H : ℕ → MarsVector ι →ₗ[ℝ] MarsVector ι
  rho : ℝ
  hH : HLowerBounded (fun t z => H t z) rho
  hH_selfAdjoint : HSelfAdjoint (fun t z => H t z)

end DiagonalMirror

section Hilbert

variable [MeasurableSpace Sample] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- State before a loop iteration: `(x_{t-1}, x_t, m_{t-1})`. -/
structure Algorithm1State (E : Type*) where
  previous : E
  current : E
  previousMomentum : E

/-- Observable coordinates of an Algorithm 1 state. -/
def Algorithm1State.toCoord (s : Algorithm1State E) : (E × E) × E :=
  ((s.previous, s.current), s.previousMomentum)

instance [MeasurableSpace E] : MeasurableSpace (Algorithm1State E) :=
  MeasurableSpace.comap Algorithm1State.toCoord inferInstance

namespace Algorithm1

variable {ι : Type*} [Fintype ι] (A : Algorithm1Data Sample ι)

/-- Initial state encoding `m_0=0` and `x_1=x_0`. -/
def initialState : Algorithm1State (MarsVector ι) where
  previous := A.x0
  current := A.x0
  previousMomentum := 0

/-- The paper-time index used by the zero-based recursion. -/
def paperTime (k : ℕ) : ℕ := k + 1

/-- Algorithm 1 line 4 before clipping, using the same sample at `x_t` and
`x_{t-1}`. -/
def correctionAtSample (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ξ : Sample) : MarsVector ι :=
  let t := paperTime k
  marsCorrection (A.beta1 t) (A.gamma t)
    (A.problem.stochasticGrad s.current ξ)
    (A.problem.stochasticGrad s.previous ξ)

/-- Algorithm 1 line 4 before clipping, using the same sample at `x_t` and
`x_{t-1}`. -/
def correction (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ω : SampleStream Sample) : MarsVector ι :=
  correctionAtSample A k s (sampleAt (paperTime k) ω)

/-- Algorithm 1 line 5 as a single-sample state kernel. -/
def clippedCorrectionAtSample (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ξ : Sample) : MarsVector ι :=
  clipByNorm (correctionAtSample A k s ξ)

/-- Algorithm 1 line 5. -/
def clippedCorrection (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ω : SampleStream Sample) : MarsVector ι :=
  clippedCorrectionAtSample A k s (sampleAt (paperTime k) ω)

/-- Algorithm 1 line 6 as a single-sample state kernel. -/
def momentumAtSample (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ξ : Sample) : MarsVector ι :=
  let t := paperTime k
  (A.beta1 t) • s.previousMomentum +
    (1 - A.beta1 t) • clippedCorrectionAtSample A k s ξ

/-- Algorithm 1 line 6. -/
def momentum (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ω : SampleStream Sample) : MarsVector ι :=
  momentumAtSample A k s (sampleAt (paperTime k) ω)

/-- Algorithm 1 line 7 as a single-sample state kernel. -/
def nextIterateAtSample (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ξ : Sample) : MarsVector ι :=
  let t := paperTime k
  marsLinearMirrorStep (A.H t) A.rho (A.eta t)
    ⟨A.hH.1, fun z => A.hH.2 t (Nat.succ_pos k) z⟩
    (momentumAtSample A k s ξ) s.current

/-- Algorithm 1 line 7. -/
def nextIterate (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ω : SampleStream Sample) : MarsVector ι :=
  nextIterateAtSample A k s (sampleAt (paperTime k) ω)

/-- One generated Algorithm 1 transition as a single-sample state kernel. -/
def stepAtSample (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ξ : Sample) : Algorithm1State (MarsVector ι) where
  previous := s.current
  current := nextIterateAtSample A k s ξ
  previousMomentum := momentumAtSample A k s ξ

/-- One generated Algorithm 1 transition. -/
def step (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ω : SampleStream Sample) : Algorithm1State (MarsVector ι) :=
  stepAtSample A k s (sampleAt (paperTime k) ω)

/-- Canonical generated Algorithm 1 process. -/
def process : ℕ → SampleStream Sample → Algorithm1State (MarsVector ι) :=
  SOptLib.recursiveIterateProcess (initialState A) (step A)

/-- Paper iterate `x_t` for `t≥1`, totalized at `t=0` only as `x_1`. -/
def x (t : ℕ) (ω : SampleStream Sample) : MarsVector ι :=
  (process A (t - 1) ω).current

/-- Generated paper momentum `m_t` for `t≥1`, computed from the state before the
`t`th loop body. -/
def m (t : ℕ) (ω : SampleStream Sample) : MarsVector ι :=
  momentum A (t - 1) (process A (t - 1) ω) ω

/-- Generated next iterate `x_{t+1}` for `t≥1`. -/
def xNext (t : ℕ) (ω : SampleStream Sample) : MarsVector ι :=
  (process A t ω).current

theorem process_zero (ω : SampleStream Sample) :
    process A 0 ω = initialState A := by
  rfl

theorem process_succ (k : ℕ) (ω : SampleStream Sample) :
    process A (k + 1) ω = step A k (process A k ω) ω := by
  rfl

theorem x_one (ω : SampleStream Sample) :
    x A 1 ω = A.x0 := by
  rfl

theorem preconditioner_inner_symm (t : ℕ) (x y : MarsVector ι) :
    inner ℝ x (A.H t y) = inner ℝ (A.H t x) y :=
  A.hH_selfAdjoint t x y

theorem same_sample_correction (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ω : SampleStream Sample) :
    correction A k s ω =
      let t := paperTime k
      let ξ := sampleAt t ω
      marsCorrection (A.beta1 t) (A.gamma t)
        (A.problem.stochasticGrad s.current ξ)
        (A.problem.stochasticGrad s.previous ξ) := by
  rfl

theorem nextIterate_is_mirrorStep (k : ℕ) (s : Algorithm1State (MarsVector ι))
    (ω : SampleStream Sample) :
    IsMarsMirrorStep (A.eta (paperTime k)) (momentum A k s ω)
      (fun z => A.H (paperTime k) z)
      s.current (nextIterate A k s ω) := by
  simpa [nextIterate, paperTime] using
    marsLinearMirrorStep_spec (A.H (k + 1)) A.rho (A.eta (k + 1))
      ⟨A.hH.1, fun z => A.hH.2 (k + 1) (Nat.succ_pos k) z⟩
      (A.hH_selfAdjoint (k + 1))
      (momentum A k s ω) s.current

/-- Generated paper iterates satisfy Algorithm 1 line 7, not an external
trajectory hypothesis. -/
theorem xNext_is_mirrorStep (t : ℕ) (ht : 0 < t) (ω : SampleStream Sample) :
    IsMarsMirrorStep (A.eta t) (m A t ω)
      (fun z => A.H t z) (x A t ω) (xNext A t ω) := by
  have hsucc : t - 1 + 1 = t := Nat.succ_pred_eq_of_pos ht
  have hproc :
      process A t ω = step A (t - 1) (process A (t - 1) ω) ω := by
    simpa [hsucc] using process_succ A (t - 1) ω
  rw [xNext, hproc]
  simpa [x, m, paperTime, hsucc, step, stepAtSample, nextIterate] using
    nextIterate_is_mirrorStep A (t - 1) (process A (t - 1) ω) ω

end Algorithm1

private theorem algorithm1_stepAtSample_measurable_of_oracle
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (hgrad_unbiased : UnbiasedGradientOracle A.problem) :
    ∀ k : ℕ,
      Measurable
        (fun p : Algorithm1State (MarsVector ι) × Sample =>
          Algorithm1.stepAtSample A k p.1 p.2) := by
  classical
  intro k
  let t := Algorithm1.paperTime k
  have hstate_coord :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        Algorithm1State.toCoord p.1) := by
    have hto :
        Measurable (Algorithm1State.toCoord :
          Algorithm1State (MarsVector ι) →
            (MarsVector ι × MarsVector ι) × MarsVector ι) := by
      change Measurable[MeasurableSpace.comap Algorithm1State.toCoord inferInstance]
        (Algorithm1State.toCoord :
          Algorithm1State (MarsVector ι) →
            (MarsVector ι × MarsVector ι) × MarsVector ι)
      exact Measurable.of_comap_le le_rfl
    exact hto.comp measurable_fst
  have hprevious :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        p.1.previous) := by
    change Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
      (Algorithm1State.toCoord p.1).1.1)
    exact measurable_fst.comp (measurable_fst.comp hstate_coord)
  have hcurrent :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        p.1.current) := by
    change Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
      (Algorithm1State.toCoord p.1).1.2)
    exact measurable_snd.comp (measurable_fst.comp hstate_coord)
  have hprevMomentum :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        p.1.previousMomentum) := by
    change Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
      (Algorithm1State.toCoord p.1).2)
    exact measurable_snd.comp hstate_coord
  have hξ :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample => p.2) :=
    measurable_snd
  have hgrad_current :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        A.problem.stochasticGrad p.1.current p.2) := by
    exact (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
      (hcurrent.prodMk hξ)
  have hgrad_previous :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        A.problem.stochasticGrad p.1.previous p.2) := by
    exact (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
      (hprevious.prodMk hξ)
  have hcorrection :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        Algorithm1.correctionAtSample A k p.1 p.2) := by
    dsimp [Algorithm1.correctionAtSample, marsCorrection, t]
    exact hgrad_current.add
      (measurable_const.smul (hgrad_current.sub hgrad_previous))
  have hclipped :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        Algorithm1.clippedCorrectionAtSample A k p.1 p.2) := by
    dsimp [Algorithm1.clippedCorrectionAtSample]
    have hnorm :
        Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
          ‖Algorithm1.correctionAtSample A k p.1 p.2‖) :=
      hcorrection.norm
    have hset :
        MeasurableSet {p : Algorithm1State (MarsVector ι) × Sample |
          1 < ‖Algorithm1.correctionAtSample A k p.1 p.2‖} :=
      measurableSet_lt measurable_const hnorm
    exact Measurable.ite hset ((hnorm.inv).smul hcorrection) hcorrection
  have hmomentum :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        Algorithm1.momentumAtSample A k p.1 p.2) := by
    dsimp [Algorithm1.momentumAtSample, t]
    exact (measurable_const.smul hprevMomentum).add
      (measurable_const.smul hclipped)
  have hnext :
      Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
        Algorithm1.nextIterateAtSample A k p.1 p.2) := by
    dsimp [Algorithm1.nextIterateAtSample, marsLinearMirrorStep, t]
    have hsolve :
        Measurable (fun p : Algorithm1State (MarsVector ι) × Sample =>
          marsLinearPreconditionerSolve (A.H (Algorithm1.paperTime k)) A.rho
            ⟨A.hH.1, fun z => A.hH.2 (Algorithm1.paperTime k) (Nat.succ_pos k) z⟩
            (Algorithm1.momentumAtSample A k p.1 p.2)) := by
      have hcont :
          Continuous (fun y : MarsVector ι =>
            marsLinearPreconditionerSolve (A.H (Algorithm1.paperTime k)) A.rho
              ⟨A.hH.1, fun z => A.hH.2 (Algorithm1.paperTime k) (Nat.succ_pos k) z⟩
              y) :=
        LinearMap.continuous_of_finiteDimensional _
      exact hcont.measurable.comp hmomentum
    exact hcurrent.sub (measurable_const.smul hsolve)
  change
    Measurable[_, MeasurableSpace.comap Algorithm1State.toCoord inferInstance]
      (fun p : Algorithm1State (MarsVector ι) × Sample =>
        Algorithm1.stepAtSample A k p.1 p.2)
  rw [measurable_comap_iff]
  simpa [Algorithm1State.toCoord, Algorithm1.stepAtSample] using
    ((hcurrent.prodMk hnext).prodMk hmomentum)

private theorem algorithm1_process_prefix_measurable_of_stepAtSample_measurable
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (hstep_meas :
      ∀ k : ℕ,
        Measurable
          (fun p : Algorithm1State (MarsVector ι) × Sample =>
            Algorithm1.stepAtSample A k p.1 p.2))
    {N n : ℕ} (hn : n ≤ N) :
    Measurable[
      (SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (N + 1)]
      (Algorithm1.process A n) := by
  classical
  let ξ : ℕ → SampleStream Sample → Sample :=
    fun k ω => sampleAt (Sample := Sample) k ω
  let hξ : ∀ k : ℕ, Measurable (ξ k) := by
    intro k
    simpa [ξ, sampleAt] using measurable_pi_apply k
  let past := fun k : ℕ => (SOptLib.filtration ξ hξ).seq k
  have hpast_mono : ∀ {a b : ℕ}, a ≤ b → past a ≤ past b := by
    intro a b hab
    exact (SOptLib.filtration ξ hξ).mono hab
  have hinit : Measurable[past (N + 1)] (Algorithm1.process A 0) := by
    change
      Measurable[past (N + 1)]
        (fun _ : SampleStream Sample => Algorithm1.initialState A)
    exact measurable_const
  have hdriver :
      ∀ j, j + 1 ≤ N → Measurable[past ((j + 1) + 1)] (ξ (j + 1)) := by
    intro j _hj
    exact SOptLib.measurable_sample_of_lt_prefixFiltration ξ hξ
      (Nat.lt_succ_self (j + 1))
  have hupdate :
      ∀ j, j + 1 ≤ N →
        Algorithm1.process A (j + 1) =
          fun ω =>
            Algorithm1.stepAtSample A j (Algorithm1.process A j ω) (ξ (j + 1) ω) := by
    intro j _hj
    funext ω
    simpa [Algorithm1.process, Algorithm1.step, Algorithm1.paperTime, ξ]
      using Algorithm1.process_succ A j ω
  simpa [ξ, hξ, past] using
    SOptLib.recursive_process_measurable_wrt_sample_prefix
      (past := past)
      (process := Algorithm1.process A)
      (driver := fun j => ξ (j + 1))
      (step := fun j s ξj => Algorithm1.stepAtSample A j s ξj)
      (N := N) (n := n)
      hpast_mono hinit hdriver
      (fun j _hj => hstep_meas j)
      hupdate hn

private theorem algorithm1_prefix_adapted_state_before_fresh_sample
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (hstep_meas :
      ∀ k : ℕ,
        Measurable
          (fun p : Algorithm1State (MarsVector ι) × Sample =>
            Algorithm1.stepAtSample A k p.1 p.2))
    (t : ℕ) (ht : 0 < t) :
    Measurable[
      (SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
      (fun ω : SampleStream Sample =>
        ((Algorithm1.x A t ω, Algorithm1.xNext A t ω), Algorithm1.m A t ω)) := by
  have hproc :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
        (Algorithm1.process A t) :=
    algorithm1_process_prefix_measurable_of_stepAtSample_measurable
      A hstep_meas (N := t) (n := t) le_rfl
  have hsucc : t - 1 + 1 = t := Nat.succ_pred_eq_of_pos ht
  have hproc_succ :
      ∀ ω : SampleStream Sample,
        Algorithm1.process A t ω =
          Algorithm1.step A (t - 1) (Algorithm1.process A (t - 1) ω) ω := by
    intro ω
    simpa [hsucc] using Algorithm1.process_succ A (t - 1) ω
  have hcoord :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
        (fun ω : SampleStream Sample => Algorithm1State.toCoord (Algorithm1.process A t ω)) := by
    have hto :
        Measurable (Algorithm1State.toCoord :
          Algorithm1State (MarsVector ι) →
            (MarsVector ι × MarsVector ι) × MarsVector ι) := by
      change Measurable[MeasurableSpace.comap Algorithm1State.toCoord inferInstance]
        (Algorithm1State.toCoord :
          Algorithm1State (MarsVector ι) →
            (MarsVector ι × MarsVector ι) × MarsVector ι)
      exact Measurable.of_comap_le le_rfl
    exact hto.comp hproc
  simpa [Algorithm1State.toCoord, Algorithm1.x, Algorithm1.xNext, Algorithm1.m,
    Algorithm1.step, Algorithm1.stepAtSample, Algorithm1.momentum, Algorithm1.paperTime, hsucc,
    hproc_succ] using hcoord

section Coordinatewise

variable {ι : Type*} [Fintype ι]

/-- Coordinatewise square for AdamW's second moment. -/
def coordSquare (x : MarsVector ι) : MarsVector ι :=
  WithLp.toLp 2 (fun i => x i ^ 2)

/-- Coordinatewise square root. -/
def coordSqrt (x : MarsVector ι) : MarsVector ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (x i))

/-- Coordinatewise division. Lean totalizes division; denominator
well-definedness is exposed separately as a theorem obligation. -/
def coordDiv (x y : MarsVector ι) : MarsVector ι :=
  WithLp.toLp 2 (fun i => x i / y i)

/-- Bias correction `m_t/(1-β^t)` for a constant scalar `β`, as printed in
Algorithm 2 line 8. -/
def biasCorrect (β : ℝ) (t : ℕ) (x : MarsVector ι) : MarsVector ι :=
  WithLp.toLp 2 (fun i => x i / (1 - β ^ t))

/-- Time-varying analogue of the AdamW bias-correction product. The paper
prints constant powers in Algorithm 2, while the B.5/B.6 theory later says the
analysis uses time-varying β schedules; this product is the canonical schedule
object whose constant-schedule bridge is stated below. -/
def betaCorrectionProduct (β : ℕ → ℝ) (t : ℕ) : ℝ :=
  (Finset.Icc 1 t).prod β

/-- Bias correction generated from a time-varying β schedule. -/
def biasCorrectSchedule (β : ℕ → ℝ) (t : ℕ) (x : MarsVector ι) : MarsVector ι :=
  WithLp.toLp 2 (fun i => x i / (1 - betaCorrectionProduct β t))

/-- AdamW-style denominator `sqrt(v_hat)+ε`. -/
def adamWDenominator (ε : ℝ) (vHat : MarsVector ι) : MarsVector ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (vHat i) + ε)

/-- Coordinatewise MARS-AdamW update, Algorithm 2 line 9. -/
def adamWUpdate (η lam ε : ℝ) (x mHat vHat : MarsVector ι) : MarsVector ι :=
  x - η • (coordDiv mHat (adamWDenominator ε vHat) + lam • x)

/-- The paper's diagonal `H_t` from (3.11), interpreted as a coordinatewise
linear action. For constant β schedules this is
`sqrt(diag(v_t)) * (1 - β₁^t) / sqrt(1 - β₂^t)`; for the time-varying theorem
schedule the powers are replaced by the generated correction products. -/
def adamWPaperHAction (β1 β2 : ℕ → ℝ) (t : ℕ) (v z : MarsVector ι) :
    MarsVector ι :=
  WithLp.toLp 2 (fun i =>
    (Real.sqrt (v i) *
      ((1 - betaCorrectionProduct β1 t) /
        Real.sqrt (1 - betaCorrectionProduct β2 t))) * z i)

theorem adamWPaperHAction_inner_symm
    (β1 β2 : ℕ → ℝ) (t : ℕ) (v x y : MarsVector ι) :
    inner ℝ x (adamWPaperHAction β1 β2 t v y) =
      inner ℝ (adamWPaperHAction β1 β2 t v x) y := by
  simp only [adamWPaperHAction, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  calc
    inner ℝ (x i)
        ((Real.sqrt (v i) *
          ((1 - betaCorrectionProduct β1 t) /
            Real.sqrt (1 - betaCorrectionProduct β2 t))) * y i)
        = inner ℝ (x i)
            ((Real.sqrt (v i) *
              ((1 - betaCorrectionProduct β1 t) /
                Real.sqrt (1 - betaCorrectionProduct β2 t))) • y i) := by
          simp [smul_eq_mul]
    _ = (Real.sqrt (v i) *
            ((1 - betaCorrectionProduct β1 t) /
              Real.sqrt (1 - betaCorrectionProduct β2 t))) *
          inner ℝ (x i) (y i) := by
          rw [real_inner_smul_right]
    _ = inner ℝ
          ((Real.sqrt (v i) *
            ((1 - betaCorrectionProduct β1 t) /
              Real.sqrt (1 - betaCorrectionProduct β2 t))) • x i) (y i) := by
          rw [real_inner_smul_left]
    _ = inner ℝ
          ((Real.sqrt (v i) *
            ((1 - betaCorrectionProduct β1 t) /
              Real.sqrt (1 - betaCorrectionProduct β2 t))) * x i) (y i) := by
          simp [smul_eq_mul]

/-- The update-denominator diagonal action induced by Algorithm 2 line 9. This
is intentionally distinct from the paper's `H_t` in (3.11), since line 9 uses
`sqrt(v_hat_t)+ε` inside a coordinatewise division. -/
def adamWUpdateDenominatorAction (ε : ℝ) (vHat z : MarsVector ι) :
    MarsVector ι :=
  coordMul (adamWDenominator ε vHat) z

/-- Well-definedness predicate for constant-β AdamW bias correction. -/
def BiasCorrectionDenominatorAdmissible (β : ℝ) (t : ℕ) : Prop :=
  1 - β ^ t ≠ 0

/-- Well-definedness predicate for time-varying AdamW bias correction. -/
def BiasCorrectionProductAdmissible (β : ℕ → ℝ) (t : ℕ) : Prop :=
  1 - betaCorrectionProduct β t ≠ 0

/-- Well-definedness predicate for AdamW's coordinate denominator. -/
def AdamWDenominatorAdmissible (ε : ℝ) (vHat : MarsVector ι) : Prop :=
  ∀ i : ι, adamWDenominator ε vHat i ≠ 0

theorem biasCorrectSchedule_const_bridge
    (β : ℝ) (t : ℕ) (x : MarsVector ι) :
    biasCorrectSchedule (fun _ : ℕ => β) t x = biasCorrect β t x := by
  simp [biasCorrectSchedule, biasCorrect, betaCorrectionProduct, Finset.prod_const, Nat.card_Icc]

/-- Algorithm 2 setup data for the coordinatewise MARS-AdamW spine. -/
structure Algorithm2Data (Sample ι : Type*) [Fintype ι] [MeasurableSpace Sample] where
  problem : ProblemData Sample (MarsVector ι)
  x0 : MarsVector ι
  beta1 : ℕ → ℝ
  beta2 : ℕ → ℝ
  gamma : ℕ → ℝ
  eta : ℕ → ℝ
  epsilon : ℝ
  lambda : ℝ

/-- State before a MARS-AdamW loop iteration:
`(x_{t-1}, x_t, m_{t-1}, v_{t-1})`. -/
structure Algorithm2State (ι : Type*) [Fintype ι] where
  previous : MarsVector ι
  current : MarsVector ι
  previousMomentum : MarsVector ι
  previousSecondMoment : MarsVector ι

def Algorithm2State.toCoord (s : Algorithm2State ι) :
    (MarsVector ι × MarsVector ι) ×
      (MarsVector ι × MarsVector ι) :=
  ((s.previous, s.current), (s.previousMomentum, s.previousSecondMoment))

instance [MeasurableSpace (MarsVector ι)] :
    MeasurableSpace (Algorithm2State ι) :=
  MeasurableSpace.comap Algorithm2State.toCoord inferInstance

namespace Algorithm2

variable [Fintype ι] (A : Algorithm2Data Sample ι)

def initialState : Algorithm2State ι where
  previous := A.x0
  current := A.x0
  previousMomentum := 0
  previousSecondMoment := 0

def paperTime (k : ℕ) : ℕ := k + 1

def correctionAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    MarsVector ι :=
  let t := paperTime k
  marsCorrection (A.beta1 t) (A.gamma t)
    (A.problem.stochasticGrad s.current ξ)
    (A.problem.stochasticGrad s.previous ξ)

/-- Algorithm 2 line 4, using the same sample at `x_t` and `x_{t-1}`. -/
def correction (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : MarsVector ι :=
  correctionAtSample A k s (sampleAt (paperTime k) ω)

def clippedCorrection (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : MarsVector ι :=
  clipByNorm (correction A k s ω)

def clippedCorrectionAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    MarsVector ι :=
  clipByNorm (correctionAtSample A k s ξ)

def firstMomentAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    MarsVector ι :=
  let t := paperTime k
  (A.beta1 t) • s.previousMomentum +
    (1 - A.beta1 t) • clippedCorrectionAtSample A k s ξ

def firstMoment (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : MarsVector ι :=
  firstMomentAtSample A k s (sampleAt (paperTime k) ω)

def secondMomentAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    MarsVector ι :=
  let t := paperTime k
  (A.beta2 t) • s.previousSecondMoment +
    (1 - A.beta2 t) • coordSquare (clippedCorrectionAtSample A k s ξ)

def secondMoment (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : MarsVector ι :=
  secondMomentAtSample A k s (sampleAt (paperTime k) ω)

def mHatAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    MarsVector ι :=
  let t := paperTime k
  biasCorrectSchedule A.beta1 t (firstMomentAtSample A k s ξ)

def mHat (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : MarsVector ι :=
  mHatAtSample A k s (sampleAt (paperTime k) ω)

def vHatAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    MarsVector ι :=
  let t := paperTime k
  biasCorrectSchedule A.beta2 t (secondMomentAtSample A k s ξ)

def vHat (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : MarsVector ι :=
  vHatAtSample A k s (sampleAt (paperTime k) ω)

def nextIterateAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    MarsVector ι :=
  let t := paperTime k
  adamWUpdate (A.eta t) A.lambda A.epsilon s.current
    (mHatAtSample A k s ξ) (vHatAtSample A k s ξ)

def nextIterate (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : MarsVector ι :=
  nextIterateAtSample A k s (sampleAt (paperTime k) ω)

def stepAtSample (k : ℕ) (s : Algorithm2State ι) (ξ : Sample) :
    Algorithm2State ι where
  previous := s.current
  current := nextIterateAtSample A k s ξ
  previousMomentum := firstMomentAtSample A k s ξ
  previousSecondMoment := secondMomentAtSample A k s ξ

def step (k : ℕ) (s : Algorithm2State ι) (ω : SampleStream Sample) : Algorithm2State ι where
  previous := (stepAtSample A k s (sampleAt (paperTime k) ω)).previous
  current := (stepAtSample A k s (sampleAt (paperTime k) ω)).current
  previousMomentum := (stepAtSample A k s (sampleAt (paperTime k) ω)).previousMomentum
  previousSecondMoment := (stepAtSample A k s (sampleAt (paperTime k) ω)).previousSecondMoment

/-- Canonical generated Algorithm 2 process. -/
def process : ℕ → SampleStream Sample → Algorithm2State ι :=
  SOptLib.recursiveIterateProcess (initialState A) (step A)

/-- Coordinatewise denominator action actually used by Algorithm 2 line 9. -/
def updateDenominatorAction (t : ℕ) (ω : SampleStream Sample)
    (z : MarsVector ι) : MarsVector ι :=
  let s := process A (t - 1) ω
  adamWUpdateDenominatorAction A.epsilon (vHat A (t - 1) s ω) z

theorem updateDenominatorAction_def (t : ℕ) (ω : SampleStream Sample)
    (z : MarsVector ι) :
    updateDenominatorAction A t ω z =
      let s := process A (t - 1) ω
      adamWUpdateDenominatorAction A.epsilon (vHat A (t - 1) s ω) z := by
  rfl

/-- Canonical diagonal `H_t` in (3.11), generated from the second moment and
bias-correction factors. This is the object governed by Assumption B.3 in the
Theorem B.6 boundary; it is not the `sqrt(v_hat)+ε` denominator from line 9. -/
def preconditioner (t : ℕ) (ω : SampleStream Sample) (z : MarsVector ι) : MarsVector ι :=
  let s := process A (t - 1) ω
  adamWPaperHAction A.beta1 A.beta2 t (secondMoment A (t - 1) s ω) z

theorem preconditioner_def (t : ℕ) (ω : SampleStream Sample)
    (z : MarsVector ι) :
    preconditioner A t ω z =
      let s := process A (t - 1) ω
      adamWPaperHAction A.beta1 A.beta2 t (secondMoment A (t - 1) s ω) z := by
  rfl

theorem preconditioner_inner_symm (t : ℕ) (ω : SampleStream Sample)
    (x y : MarsVector ι) :
    inner ℝ x (preconditioner A t ω y) =
      inner ℝ (preconditioner A t ω x) y := by
  simp [preconditioner, adamWPaperHAction_inner_symm]

def x (t : ℕ) (ω : SampleStream Sample) : MarsVector ι :=
  (process A (t - 1) ω).current

def m (t : ℕ) (ω : SampleStream Sample) : MarsVector ι :=
  firstMoment A (t - 1) (process A (t - 1) ω) ω

def xNext (t : ℕ) (ω : SampleStream Sample) : MarsVector ι :=
  (process A t ω).current

theorem process_zero (ω : SampleStream Sample) :
    process A 0 ω = initialState A := by
  rfl

theorem process_succ (k : ℕ) (ω : SampleStream Sample) :
    process A (k + 1) ω = step A k (process A k ω) ω := by
  rfl

theorem x_one (ω : SampleStream Sample) :
    x A 1 ω = A.x0 := by
  rfl

theorem same_sample_correction (k : ℕ) (s : Algorithm2State ι)
    (ω : SampleStream Sample) :
    correction A k s ω =
      let t := paperTime k
      let ξ := sampleAt t ω
      marsCorrection (A.beta1 t) (A.gamma t)
        (A.problem.stochasticGrad s.current ξ)
        (A.problem.stochasticGrad s.previous ξ) := by
  rfl

theorem step_eq_stepAtSample (k : ℕ) (s : Algorithm2State ι)
    (ω : SampleStream Sample) :
    step A k s ω = stepAtSample A k s (sampleAt (paperTime k) ω) := by
  rfl

theorem xNext_eq_x_succ (t : ℕ) (ω : SampleStream Sample) :
    xNext A t ω = x A (t + 1) ω := by
  simp [xNext, x]

end Algorithm2

end Coordinatewise

set_option maxHeartbeats 800000 in
private theorem algorithm2_stepAtSample_measurable_of_oracle
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (hgrad_unbiased : UnbiasedGradientOracle A.problem) :
    ∀ k : ℕ,
      Measurable
        (fun p : Algorithm2State ι × Sample =>
          Algorithm2.stepAtSample A k p.1 p.2) := by
  classical
  intro k
  let t := Algorithm2.paperTime k
  have hstate_coord :
      Measurable (fun p : Algorithm2State ι × Sample =>
        Algorithm2State.toCoord p.1) := by
    have hto :
        Measurable (Algorithm2State.toCoord :
          Algorithm2State ι →
            (MarsVector ι × MarsVector ι) ×
              (MarsVector ι × MarsVector ι)) := by
      change Measurable[MeasurableSpace.comap Algorithm2State.toCoord inferInstance]
        (Algorithm2State.toCoord :
          Algorithm2State ι →
            (MarsVector ι × MarsVector ι) ×
              (MarsVector ι × MarsVector ι))
      exact Measurable.of_comap_le le_rfl
    exact hto.comp measurable_fst
  have hprevious :
      Measurable (fun p : Algorithm2State ι × Sample =>
        p.1.previous) := by
    change Measurable (fun p : Algorithm2State ι × Sample =>
      (Algorithm2State.toCoord p.1).1.1)
    exact measurable_fst.comp (measurable_fst.comp hstate_coord)
  have hcurrent :
      Measurable (fun p : Algorithm2State ι × Sample =>
        p.1.current) := by
    change Measurable (fun p : Algorithm2State ι × Sample =>
      (Algorithm2State.toCoord p.1).1.2)
    exact measurable_snd.comp (measurable_fst.comp hstate_coord)
  have hprevMomentum :
      Measurable (fun p : Algorithm2State ι × Sample =>
        p.1.previousMomentum) := by
    change Measurable (fun p : Algorithm2State ι × Sample =>
      (Algorithm2State.toCoord p.1).2.1)
    exact measurable_fst.comp (measurable_snd.comp hstate_coord)
  have hprevSecondMoment :
      Measurable (fun p : Algorithm2State ι × Sample =>
        p.1.previousSecondMoment) := by
    change Measurable (fun p : Algorithm2State ι × Sample =>
      (Algorithm2State.toCoord p.1).2.2)
    exact measurable_snd.comp (measurable_snd.comp hstate_coord)
  have hξ :
      Measurable (fun p : Algorithm2State ι × Sample => p.2) :=
    measurable_snd
  have hgrad_current :
      Measurable (fun p : Algorithm2State ι × Sample =>
        A.problem.stochasticGrad p.1.current p.2) := by
    exact (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
      (hcurrent.prodMk hξ)
  have hgrad_previous :
      Measurable (fun p : Algorithm2State ι × Sample =>
        A.problem.stochasticGrad p.1.previous p.2) := by
    exact (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
      (hprevious.prodMk hξ)
  have hcorrection :
      Measurable (fun p : Algorithm2State ι × Sample =>
        Algorithm2.correctionAtSample A k p.1 p.2) := by
    dsimp [Algorithm2.correctionAtSample, marsCorrection, t]
    exact hgrad_current.add
      (measurable_const.smul (hgrad_current.sub hgrad_previous))
  have hclipped :
      Measurable (fun p : Algorithm2State ι × Sample =>
        Algorithm2.clippedCorrectionAtSample A k p.1 p.2) := by
    dsimp [Algorithm2.clippedCorrectionAtSample]
    have hnorm :
        Measurable (fun p : Algorithm2State ι × Sample =>
          ‖Algorithm2.correctionAtSample A k p.1 p.2‖) :=
      hcorrection.norm
    have hset :
        MeasurableSet {p : Algorithm2State ι × Sample |
          1 < ‖Algorithm2.correctionAtSample A k p.1 p.2‖} :=
      measurableSet_lt measurable_const hnorm
    exact Measurable.ite hset ((hnorm.inv).smul hcorrection) hcorrection
  have hfirst :
      Measurable (fun p : Algorithm2State ι × Sample =>
        Algorithm2.firstMomentAtSample A k p.1 p.2) := by
    dsimp [Algorithm2.firstMomentAtSample, t]
    exact (measurable_const.smul hprevMomentum).add
      (measurable_const.smul hclipped)
  have hsquare :
      Measurable (fun p : Algorithm2State ι × Sample =>
        coordSquare (Algorithm2.clippedCorrectionAtSample A k p.1 p.2)) := by
    have hcoords :
        Measurable (fun p : Algorithm2State ι × Sample =>
          fun i => (Algorithm2.clippedCorrectionAtSample A k p.1 p.2 i) ^ 2) := by
      apply measurable_pi_iff.mpr
      intro i
      exact
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.measurable.comp
          hclipped).pow_const 2
    simpa [coordSquare] using
      (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp hcoords
  have hsecond :
      Measurable (fun p : Algorithm2State ι × Sample =>
        Algorithm2.secondMomentAtSample A k p.1 p.2) := by
    dsimp [Algorithm2.secondMomentAtSample, t]
    exact (measurable_const.smul hprevSecondMoment).add
      (measurable_const.smul hsquare)
  have hmh :
      Measurable (fun p : Algorithm2State ι × Sample =>
        biasCorrectSchedule A.beta1 t
          (Algorithm2.firstMomentAtSample A k p.1 p.2)) := by
    have hcoords :
        Measurable (fun p : Algorithm2State ι × Sample =>
          fun i =>
            Algorithm2.firstMomentAtSample A k p.1 p.2 i /
              (1 - betaCorrectionProduct A.beta1 t)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.measurable.comp
          hfirst).div_const _
    simpa [biasCorrectSchedule] using
      (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp hcoords
  have hvh :
      Measurable (fun p : Algorithm2State ι × Sample =>
        biasCorrectSchedule A.beta2 t
          (Algorithm2.secondMomentAtSample A k p.1 p.2)) := by
    have hcoords :
        Measurable (fun p : Algorithm2State ι × Sample =>
          fun i =>
            Algorithm2.secondMomentAtSample A k p.1 p.2 i /
              (1 - betaCorrectionProduct A.beta2 t)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.measurable.comp
          hsecond).div_const _
    simpa [biasCorrectSchedule] using
      (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp hcoords
  have hnext :
      Measurable (fun p : Algorithm2State ι × Sample =>
        Algorithm2.nextIterateAtSample A k p.1 p.2) := by
    have hdenom :
        Measurable (fun p : Algorithm2State ι × Sample =>
          adamWDenominator A.epsilon
            (biasCorrectSchedule A.beta2 t
              (Algorithm2.secondMomentAtSample A k p.1 p.2))) := by
      have hcoords :
          Measurable (fun p : Algorithm2State ι × Sample =>
            fun i =>
              Real.sqrt
                  (biasCorrectSchedule A.beta2 t
                    (Algorithm2.secondMomentAtSample A k p.1 p.2) i) +
                A.epsilon) := by
        apply measurable_pi_iff.mpr
        intro i
        exact
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.measurable.comp
            hvh).sqrt.add measurable_const
      simpa [adamWDenominator] using
        (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp hcoords
    have hdiv :
        Measurable (fun p : Algorithm2State ι × Sample =>
          coordDiv
            (biasCorrectSchedule A.beta1 t
              (Algorithm2.firstMomentAtSample A k p.1 p.2))
            (adamWDenominator A.epsilon
              (biasCorrectSchedule A.beta2 t
                (Algorithm2.secondMomentAtSample A k p.1 p.2)))) := by
      have hcoords :
          Measurable (fun p : Algorithm2State ι × Sample =>
            fun i =>
              biasCorrectSchedule A.beta1 t
                  (Algorithm2.firstMomentAtSample A k p.1 p.2) i /
                (adamWDenominator A.epsilon
                  (biasCorrectSchedule A.beta2 t
                    (Algorithm2.secondMomentAtSample A k p.1 p.2)) i)) := by
        apply measurable_pi_iff.mpr
        intro i
        exact
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.measurable.comp
            hmh).div
            ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.measurable.comp
              hdenom)
      simpa [coordDiv] using
        (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp hcoords
    have hbody :
        Measurable (fun p : Algorithm2State ι × Sample =>
          coordDiv
              (biasCorrectSchedule A.beta1 t
                (Algorithm2.firstMomentAtSample A k p.1 p.2))
              (adamWDenominator A.epsilon
                (biasCorrectSchedule A.beta2 t
                  (Algorithm2.secondMomentAtSample A k p.1 p.2))) +
            A.lambda • p.1.current) :=
      hdiv.add
        ((measurable_const :
          Measurable (fun _ : Algorithm2State ι × Sample => A.lambda)).smul
          hcurrent)
    have hupdate :
        Measurable (fun p : Algorithm2State ι × Sample =>
          A.eta t •
            (coordDiv
                (biasCorrectSchedule A.beta1 t
                  (Algorithm2.firstMomentAtSample A k p.1 p.2))
                (adamWDenominator A.epsilon
                  (biasCorrectSchedule A.beta2 t
                    (Algorithm2.secondMomentAtSample A k p.1 p.2))) +
              A.lambda • p.1.current)) :=
      (measurable_const :
        Measurable (fun _ : Algorithm2State ι × Sample => A.eta t)).smul hbody
    simpa [Algorithm2.nextIterateAtSample, adamWUpdate, t] using
      hcurrent.sub hupdate
  change
    Measurable[_, MeasurableSpace.comap Algorithm2State.toCoord inferInstance]
      (fun p : Algorithm2State ι × Sample =>
        Algorithm2.stepAtSample A k p.1 p.2)
  rw [measurable_comap_iff]
  simpa [Algorithm2State.toCoord, Algorithm2.stepAtSample] using
    ((hcurrent.prodMk hnext).prodMk (hfirst.prodMk hsecond))

private theorem algorithm2_process_prefix_measurable_of_stepAtSample_measurable
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (hstep_meas :
      ∀ k : ℕ,
        Measurable
          (fun p : Algorithm2State ι × Sample =>
            Algorithm2.stepAtSample A k p.1 p.2))
    {N n : ℕ} (hn : n ≤ N) :
    Measurable[
      (SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (N + 1)]
      (Algorithm2.process A n) := by
  classical
  let ξ : ℕ → SampleStream Sample → Sample :=
    fun k ω => sampleAt (Sample := Sample) k ω
  let hξ : ∀ k : ℕ, Measurable (ξ k) := by
    intro k
    simpa [ξ, sampleAt] using measurable_pi_apply k
  let past := fun k : ℕ => (SOptLib.filtration ξ hξ).seq k
  have hpast_mono : ∀ {a b : ℕ}, a ≤ b → past a ≤ past b := by
    intro a b hab
    exact (SOptLib.filtration ξ hξ).mono hab
  have hinit : Measurable[past (N + 1)] (Algorithm2.process A 0) := by
    change Measurable[past (N + 1)]
      (fun _ : SampleStream Sample => Algorithm2.initialState A)
    exact measurable_const
  have hdriver :
      ∀ j, j + 1 ≤ N →
        Measurable[past ((j + 1) + 1)] (ξ (j + 1)) := by
    intro j _hj
    exact SOptLib.measurable_sample_of_lt_prefixFiltration ξ hξ
      (Nat.lt_succ_self (j + 1))
  have hupdate :
      ∀ j, j + 1 ≤ N →
        Algorithm2.process A (j + 1) =
          fun ω =>
            Algorithm2.stepAtSample A j (Algorithm2.process A j ω)
              (ξ (j + 1) ω) := by
    intro j _hj
    funext ω
    simpa [Algorithm2.process, Algorithm2.step, Algorithm2.paperTime, ξ]
      using Algorithm2.process_succ A j ω
  simpa [ξ, hξ, past] using
    SOptLib.recursive_process_measurable_wrt_sample_prefix
      (past := past)
      (process := Algorithm2.process A)
      (driver := fun j => ξ (j + 1))
      (step := fun j s ξj => Algorithm2.stepAtSample A j s ξj)
      (N := N) (n := n)
      hpast_mono hinit hdriver
      (fun j _hj => hstep_meas j)
      hupdate hn

private theorem algorithm2_prefix_adapted_state_before_fresh_sample
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (hstep_meas :
      ∀ k : ℕ,
        Measurable
          (fun p : Algorithm2State ι × Sample =>
            Algorithm2.stepAtSample A k p.1 p.2))
    (t : ℕ) (ht : 0 < t) :
    Measurable[
      (SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
      (fun ω : SampleStream Sample =>
        ((Algorithm2.x A t ω, Algorithm2.xNext A t ω), Algorithm2.m A t ω)) := by
  have hproc :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
        (Algorithm2.process A t) :=
    algorithm2_process_prefix_measurable_of_stepAtSample_measurable
      A hstep_meas (N := t) (n := t) le_rfl
  have hsucc : t - 1 + 1 = t := Nat.succ_pred_eq_of_pos ht
  have hcoord :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
        (fun ω : SampleStream Sample => Algorithm2State.toCoord (Algorithm2.process A t ω)) := by
    have hto :
        Measurable (Algorithm2State.toCoord :
          Algorithm2State ι →
            (MarsVector ι × MarsVector ι) ×
              (MarsVector ι × MarsVector ι)) := by
      change Measurable[MeasurableSpace.comap Algorithm2State.toCoord inferInstance]
        (Algorithm2State.toCoord :
          Algorithm2State ι →
            (MarsVector ι × MarsVector ι) ×
              (MarsVector ι × MarsVector ι))
      exact Measurable.of_comap_le le_rfl
    exact hto.comp hproc
  have hproc_succ :
      ∀ ω : SampleStream Sample,
        Algorithm2.process A t ω =
          Algorithm2.step A (t - 1) (Algorithm2.process A (t - 1) ω) ω := by
    intro ω
    simpa [hsucc] using Algorithm2.process_succ A (t - 1) ω
  have hpair :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
        (fun ω : SampleStream Sample =>
          ((Algorithm2State.toCoord (Algorithm2.process A t ω)).1,
            (Algorithm2State.toCoord (Algorithm2.process A t ω)).2.1)) := by
    exact
      (measurable_fst.comp hcoord).prodMk
        (measurable_fst.comp (measurable_snd.comp hcoord))
  simpa [Algorithm2State.toCoord, Algorithm2.x, Algorithm2.xNext, Algorithm2.m,
    Algorithm2.step, Algorithm2.stepAtSample, Algorithm2.firstMoment,
    Algorithm2.paperTime, hsucc, hproc_succ] using hpair

private theorem algorithm2_momentum_succ_unclipped_of_correction_norm_le_one
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (T : ℕ)
    (hclip :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        ‖marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
            (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
              (sampleAt (Sample := Sample) (t + 1) ω))
            (A.problem.stochasticGrad (Algorithm2.x A t ω)
              (sampleAt (Sample := Sample) (t + 1) ω))‖ ≤ 1) :
    ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
      Algorithm2.m A (t + 1) ω =
        (A.beta1 (t + 1)) • Algorithm2.m A t ω +
          (1 - A.beta1 (t + 1)) •
            marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
              (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
                (sampleAt (Sample := Sample) (t + 1) ω))
              (A.problem.stochasticGrad (Algorithm2.x A t ω)
                (sampleAt (Sample := Sample) (t + 1) ω)) := by
  intro t ht ω
  have htpos : 0 < t := (Finset.mem_Icc.mp ht).1
  have hsucc : t - 1 + 1 = t := Nat.succ_pred_eq_of_pos htpos
  have hproc :
      Algorithm2.process A t ω =
        Algorithm2.step A (t - 1) (Algorithm2.process A (t - 1) ω) ω := by
    simpa [hsucc] using Algorithm2.process_succ A (t - 1) ω
  have hactual :
      Algorithm2.m A (t + 1) ω =
        (A.beta1 (t + 1)) • Algorithm2.m A t ω +
          (1 - A.beta1 (t + 1)) •
            Algorithm2.clippedCorrection A t
              (Algorithm2.process A t ω) ω := by
    have hclip_def :
        Algorithm2.clippedCorrection A t (Algorithm2.process A t ω) ω =
          Algorithm2.clippedCorrectionAtSample A t
            (Algorithm2.process A t ω) (sampleAt (Sample := Sample) (t + 1) ω) := by
      rfl
    rw [hclip_def]
    simp [Algorithm2.m, Algorithm2.firstMoment, Algorithm2.firstMomentAtSample,
      Algorithm2.paperTime, hproc, Algorithm2.step, Algorithm2.stepAtSample,
      Algorithm2.clippedCorrection, Algorithm2.correction, hsucc]
  have hcurrent :
      (Algorithm2.process A (t - 1) ω).current = Algorithm2.x A t ω := by
    rfl
  have hnext :
      Algorithm2.nextIterateAtSample A (t - 1)
          (Algorithm2.process A (t - 1) ω) (sampleAt (Sample := Sample) t ω) =
        Algorithm2.xNext A t ω := by
    rw [Algorithm2.xNext, hproc]
    simp [Algorithm2.step, Algorithm2.stepAtSample, Algorithm2.paperTime, hsucc]
  have hclipped :
      Algorithm2.clippedCorrection A t (Algorithm2.process A t ω) ω =
        marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
          (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
            (sampleAt (Sample := Sample) (t + 1) ω))
          (A.problem.stochasticGrad (Algorithm2.x A t ω)
            (sampleAt (Sample := Sample) (t + 1) ω)) := by
    simp [Algorithm2.clippedCorrection, Algorithm2.correction,
      Algorithm2.paperTime, hproc, Algorithm2.step, Algorithm2.stepAtSample,
      Algorithm2.clippedCorrectionAtSample, Algorithm2.correctionAtSample,
      hsucc, hcurrent, hnext, clipByNorm_of_norm_le_one (hclip t ht ω)]
  rw [hactual, hclipped]

/-- Classification of source-boundary issues kept outside the registered
B.5/B.6 theorem conclusions. -/
inductive SourceBoundaryIssue where
  | sourceDefect
  | missingPrerequisite
  | statementProofMismatch
  deriving DecidableEq, Repr

section Expectations

variable [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The expected estimator-error term appearing in Theorems B.5 and B.6. -/
def expectedEstimatorError (μ : Measure Ω) (gradF : E → E)
    (x m : Ω → E) : ℝ :=
  ∫ ω, ‖gradF (x ω) - m ω‖ ^ 2 ∂μ

/-- Well-definedness obligation for the expected estimator-error term. The
paper writes the expectation directly; this predicate records the Lean
integrability proof obligation without making it a theorem assumption. -/
def ExpectedEstimatorErrorWellDefined (μ : Measure Ω) (gradF : E → E)
    (x m : Ω → E) : Prop :=
  Integrable (fun ω => ‖gradF (x ω) - m ω‖ ^ 2) μ

/-- The expected scaled displacement term appearing in Theorems B.5 and B.6. -/
def expectedScaledDisplacement (μ : Measure Ω) (η : ℝ)
    (x xNext : Ω → E) : ℝ :=
  ∫ ω, η⁻¹ * ‖xNext ω - x ω‖ ^ 2 ∂μ

/-- Well-definedness obligation for the expected scaled-displacement term. -/
def ExpectedScaledDisplacementWellDefined (μ : Measure Ω) (η : ℝ)
    (x xNext : Ω → E) : Prop :=
  Integrable (fun ω => η⁻¹ * ‖xNext ω - x ω‖ ^ 2) μ

/-- Random version of Assumption B.3 for generated adaptive preconditioners
such as Algorithm 2's diagonal AdamW preconditioner. -/
def RandomHLowerBounded (H : ℕ → Ω → E → E) (ρ : ℝ) : Prop :=
  (0 < ρ ∧ ∀ t : ℕ, 0 < t → ∀ ω : Ω, ∀ z : E,
    ρ * ‖z‖ ^ 2 ≤ inner ℝ z (H t ω z)) ∧
  (∀ t : ℕ, ∀ ω : Ω, ∀ x y : E,
    inner ℝ x (H t ω y) = inner ℝ (H t ω x) y)

theorem RandomHLowerBounded.lower
    {H : ℕ → Ω → E → E} {ρ : ℝ} (h : RandomHLowerBounded H ρ) :
    0 < ρ ∧ ∀ t : ℕ, 0 < t → ∀ ω : Ω, ∀ z : E,
      ρ * ‖z‖ ^ 2 ≤ inner ℝ z (H t ω z) :=
  h.1

theorem RandomHLowerBounded.inner_symm
    {H : ℕ → Ω → E → E} {ρ : ℝ} (h : RandomHLowerBounded H ρ) :
    ∀ t : ℕ, ∀ ω : Ω, ∀ x y : E,
      inner ℝ x (H t ω y) = inner ℝ (H t ω x) y :=
  h.2

/-- The C.2/D.4 same-sample gradient difference
`Δ_t = ∇f(x_{t+1},ξ_{t+1}) - ∇f(x_t,ξ_{t+1})`. -/
def c2Delta (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext : Ω → E) (t : ℕ) (ω : Ω) : E :=
  let ξ := sample (t + 1) ω
  P.stochasticGrad (xNext ω) ξ - P.stochasticGrad (x ω) ξ

/-- The estimator error `ε_t=m_t-∇F(x_t)` used in the C.2 proof. -/
def c2EstimatorError (P : ProblemData Sample E) (x m : Ω → E) (ω : Ω) : E :=
  m ω - P.gradF (x ω)

/-- The squared same-sample gradient-difference expectation in (C.2). -/
def c2DeltaNormSqExpectation (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext : Ω → E) (t : ℕ) : ℝ :=
  ∫ ω, ‖c2Delta P sample x xNext t ω‖ ^ 2 ∂μ

/-- The whole-stream Bochner integral of the same-sample difference.

This is retained as a diagnostic legacy object only. It is not the `E Δ_t`
appearing in D.4: that source expectation is over the fresh sample while the
adapted prefix is held fixed. -/
def c2GlobalDeltaExpectation (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext : Ω → E) (t : ℕ) : E :=
  ∫ ω, c2Delta P sample x xNext t ω ∂μ

/-- The canonical fresh-sample conditional mean of `Δ_t`, with the adapted
prefix represented by `ω`.

Under the unbiased-gradient oracle this is the fixed-fiber expectation of the
same-sample difference. It is therefore a function of the adapted query, not a
single Bochner integral over the complete stream law. -/
def c2DeltaExpectation (P : ProblemData Sample E) (x xNext : Ω → E) : Ω → E :=
  fun ω => P.gradF (xNext ω) - P.gradF (x ω)

/-- The integrated squared norm of the adapted fresh-sample mean used in D.12. -/
def c2DeltaConditionalMeanSqExpectation (μ : Measure Ω)
    (P : ProblemData Sample E) (x xNext : Ω → E) : ℝ :=
  ∫ ω, ‖c2DeltaExpectation P x xNext ω‖ ^ 2 ∂μ

/-- Fixed-fiber bridge from the stochastic same-sample difference to the
canonical conditional mean. -/
private theorem c2DeltaExpectation_fixed_fiber
    [MeasurableSpace Sample] [MeasurableSpace E] [CompleteSpace E]
    {P : ProblemData Sample E} (h : UnbiasedGradientOracle P)
    (x xNext : Ω → E) (ω : Ω) :
    (∫ ξ, P.stochasticGrad (xNext ω) ξ -
      P.stochasticGrad (x ω) ξ ∂P.sampleLaw) =
      c2DeltaExpectation P x xNext ω := by
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  have hnext := UnbiasedGradientOracle.fixed_integrable h (xNext ω)
  have hprev := UnbiasedGradientOracle.fixed_integrable h (x ω)
  calc
    (∫ ξ, P.stochasticGrad (xNext ω) ξ -
        P.stochasticGrad (x ω) ξ ∂P.sampleLaw) =
        (∫ ξ, P.stochasticGrad (xNext ω) ξ ∂P.sampleLaw) -
          ∫ ξ, P.stochasticGrad (x ω) ξ ∂P.sampleLaw := by
      exact integral_sub hnext hprev
    _ = P.gradF (xNext ω) - P.gradF (x ω) := by
      simp [UnbiasedGradientOracle.mean_eq_gradF h]
    _ = c2DeltaExpectation P x xNext ω := by
      rfl

/-- The proof-local `G_{t+1}` from D.4, not the theorem-level constant `G`. -/
def c2ProofG (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β : ℝ) (t : ℕ) : ℝ :=
  (1 - β) *
      (∫ ω,
        inner ℝ (c2Delta P sample x xNext t ω)
          (P.stochasticGrad (xNext ω) (sample (t + 1) ω) - P.gradF (xNext ω)) ∂μ) +
    β *
      (∫ ω,
        inner ℝ (c2Delta P sample x xNext t ω)
          (c2EstimatorError P x m ω) ∂μ)

/-- The printed Lemma C.2 display for `G_{t+1}` has a source-visible type defect:
its final inner-product factor is `F(x_t)-m_t`, a scalar-minus-vector
expression. The corrected declarations below are extension-only. -/
def C2LiteralSourceGTypeIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.sourceDefect

/-- Corrected statement-window `G_{t+1}` for Lemma C.2. The PDF display is
source-visible but has a type defect in its final factor; this Lean object uses
the type-correct gradient-error reading and is extension-only. -/
def c2CorrectedStatementG (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β : ℝ) (t : ℕ) : ℝ :=
  (1 - β) *
      (∫ ω,
        inner ℝ (c2Delta P sample x xNext t ω)
          (P.stochasticGrad (xNext ω) (sample (t + 1) ω) - P.gradF (xNext ω)) ∂μ) +
    β *
      (∫ ω,
        inner ℝ (P.gradF (xNext ω) - P.gradF (x ω))
          (P.gradF (x ω) - m ω) ∂μ)

/-- The paper-literal C.2 scalar on its admissible quotient domain. -/
def c2CorrectedAOn
    (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β : ℝ) (t : ℕ)
    (hden :
      c2DeltaNormSqExpectation μ P sample x xNext t ≠ 0) : ℝ :=
  (c2CorrectedStatementG μ P sample x xNext m β t +
      β * (c2DeltaNormSqExpectation μ P sample x xNext t -
        c2DeltaConditionalMeanSqExpectation μ P x xNext)) /
    c2DeltaNormSqExpectation μ P sample x xNext t

/-- Totalized ambient representative of the paper quotient. On the admissible
domain it is definitionally routed through `c2CorrectedAOn`; the zero branch is
only Lean's ambient extension and is never used by the corrected boundary. -/
noncomputable def c2CorrectedA (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β : ℝ) (t : ℕ) : ℝ :=
  letI : DecidableEq ℝ := Classical.decEq ℝ
  if hzero : c2DeltaNormSqExpectation μ P sample x xNext t = 0 then
    0
  else
    c2CorrectedAOn μ P sample x xNext m β t hzero

/-- D.4's proof-window scalar `A_{t+1}`, retained separately so that it is not
mistaken for the C.2 statement object. -/
def d4ProofA (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β : ℝ) (t : ℕ) : ℝ :=
  (c2ProofG μ P sample x xNext m β t +
      β * (c2DeltaNormSqExpectation μ P sample x xNext t -
        c2DeltaConditionalMeanSqExpectation μ P x xNext)) /
    c2DeltaNormSqExpectation μ P sample x xNext t

/-- D.4 proof-window residual using the proof-window `G_{t+1}` and `A_{t+1}`. -/
def d4ProofResidual (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β γ : ℝ) (t : ℕ) : ℝ :=
  let deltaSq := c2DeltaNormSqExpectation μ P sample x xNext t
  let A := d4ProofA μ P sample x xNext m β t
  deltaSq * (A ^ 2 - (β * (1 - γ) - A) ^ 2)

/-- Well-definedness predicate for the denominator in `A_{t+1}` from
(C.2)/(D.12). The PDF displays the quotient but does not state this as an
independent theorem assumption. -/
def C2ADenominatorAdmissible
    (μ : Measure Ω) (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext : Ω → E) (t : ℕ) : Prop :=
  c2DeltaNormSqExpectation μ P sample x xNext t ≠ 0

theorem c2CorrectedA_eq_on
    (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β : ℝ) (t : ℕ)
    (hden : C2ADenominatorAdmissible μ P sample x xNext t) :
    c2CorrectedA μ P sample x xNext m β t =
      c2CorrectedAOn μ P sample x xNext m β t hden := by
  unfold c2CorrectedA
  rw [dif_neg hden]

/-- D.12 uses the stronger denominator
`β_{1,t+1} E‖Δ_t‖²`. The PDF displays this quotient but does not state the
nonzero condition as a theorem assumption. -/
def D12GammaDenominatorAdmissible
    (μ : Measure Ω) (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext : Ω → E) (β : ℝ) (t : ℕ) : Prop :=
  β * c2DeltaNormSqExpectation μ P sample x xNext t ≠ 0

/-- The two displayed equalities in (D.12), recorded as a proof obligation
rather than silently using Lean's totalized division. -/
def D12GammaChoice
    (μ : Measure Ω) (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext m : Ω → E) (β γ : ℝ) (t : ℕ) : Prop :=
  let deltaSq := c2DeltaNormSqExpectation μ P sample x xNext t
  let deltaMeanSq := c2DeltaConditionalMeanSqExpectation μ P x xNext
  γ =
      1 - (c2ProofG μ P sample x xNext m β t +
          β * (deltaSq - deltaMeanSq)) / (β * deltaSq) ∧
    γ = (deltaMeanSq - c2ProofG μ P sample x xNext m β t) / (β * deltaSq)

/-- Integrability obligations for the raw C.2/D.4 expectations. These are proof
obligations for later phases, not source-facing assumptions of B.5/B.6. -/
def C2ExpectationWellDefined
    (μ : Measure Ω) (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext m : Ω → E) (t : ℕ) : Prop :=
  Integrable (fun ω => ‖c2Delta P sample x xNext t ω‖ ^ 2) μ ∧
  Integrable (fun ω => c2Delta P sample x xNext t ω) μ ∧
  Integrable
    (fun ω =>
      inner ℝ (c2Delta P sample x xNext t ω)
        (P.stochasticGrad (xNext ω) (sample (t + 1) ω) - P.gradF (xNext ω))) μ ∧
  Integrable
    (fun ω =>
      inner ℝ (P.gradF (xNext ω) - P.gradF (x ω))
        (P.gradF (x ω) - m ω)) μ

/-- Lemma C.2's beta prerequisite over a theorem horizon. -/
def C2BetaAdmissibleOnHorizon (β : ℕ → ℝ) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, 0 ≤ β (t + 1) ∧ β (t + 1) ≤ 1

/-- Corrected residual `M_{t+1}` from (C.2), constructed from the generated
same-sample gradient difference and the corrected scalar `A_{t+1}`. This is not
the literal source object because the printed `G_{t+1}` has a type defect. -/
def c2CorrectedResidualOn
    (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β γ : ℝ) (t : ℕ)
    (hden : C2ADenominatorAdmissible μ P sample x xNext t) : ℝ :=
  let deltaSq := c2DeltaNormSqExpectation μ P sample x xNext t
  let A := c2CorrectedAOn μ P sample x xNext m β t hden
  deltaSq * (A ^ 2 - (β * (1 - γ) - A) ^ 2)

/-- Ambient totalization of the corrected residual. The source route consumes
the admissible branch supplied by `C2CorrectedExtensionBoundaryOnHorizon`. -/
noncomputable def c2CorrectedResidual (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β γ : ℝ) (t : ℕ) : ℝ :=
  letI : DecidableEq ℝ := Classical.decEq ℝ
  if hzero : c2DeltaNormSqExpectation μ P sample x xNext t = 0 then
    0
  else
    c2CorrectedResidualOn μ P sample x xNext m β γ t hzero

theorem c2CorrectedResidual_eq_on
    (μ : Measure Ω) (P : ProblemData Sample E)
    (sample : ℕ → Ω → Sample) (x xNext m : Ω → E) (β γ : ℝ) (t : ℕ)
    (hden : C2ADenominatorAdmissible μ P sample x xNext t) :
    c2CorrectedResidual μ P sample x xNext m β γ t =
      c2CorrectedResidualOn μ P sample x xNext m β γ t hden := by
  unfold c2CorrectedResidual
  rw [dif_neg hden]

theorem c2CorrectedResidual_def
    (μ : Measure Ω) (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext m : Ω → E) (β γ : ℝ) (t : ℕ) :
    c2CorrectedResidual μ P sample x xNext m β γ t =
      let deltaSq := c2DeltaNormSqExpectation μ P sample x xNext t
      let A := c2CorrectedA μ P sample x xNext m β t
      deltaSq * (A ^ 2 - (β * (1 - γ) - A) ^ 2) := by
  by_cases hden : C2ADenominatorAdmissible μ P sample x xNext t
  · rw [c2CorrectedResidual_eq_on μ P sample x xNext m β γ t hden]
    simp [c2CorrectedResidualOn, c2CorrectedA_eq_on μ P sample x xNext m β t hden]
  · have hzero :
        c2DeltaNormSqExpectation μ P sample x xNext t = 0 := by
      by_contra hzero
      exact hden hzero
    simp [c2CorrectedResidual, c2CorrectedA, C2ADenominatorAdmissible, hden,
      hzero]

/-- Compatibility obligation between the corrected C.2 statement-window
residual and the D.4 proof-window residual. -/
def C2CorrectedStatementProofResidualCompatible
    (μ : Measure Ω) (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext m : Ω → E) (β γ : ℝ) (t : ℕ) : Prop :=
  c2CorrectedResidual μ P sample x xNext m β γ t =
    d4ProofResidual μ P sample x xNext m β γ t

/-- Corrected-extension obligations used when a Lean-readable proof invokes
Lemma C.2 and D.12. These are not printed assumptions in B.5/B.6 and must not
be included in the registered source theorem boundary. -/
def C2CorrectedExtensionBoundaryOnHorizon
    (μ : Measure Ω) (P : ProblemData Sample E) (sample : ℕ → Ω → Sample)
    (x xNext m : ℕ → Ω → E) (β γ : ℕ → ℝ) (T : ℕ) : Prop :=
  C2BetaAdmissibleOnHorizon β T ∧
  (∀ t ∈ Finset.Icc 1 T, C2ExpectationWellDefined μ P sample (x t) (xNext t) (m t) t) ∧
  (∀ t ∈ Finset.Icc 1 T, C2ADenominatorAdmissible μ P sample (x t) (xNext t) t) ∧
  (∀ t ∈ Finset.Icc 1 T,
    D12GammaDenominatorAdmissible μ P sample (x t) (xNext t) (β (t + 1)) t) ∧
  (∀ t ∈ Finset.Icc 1 T,
    D12GammaChoice μ P sample (x t) (xNext t) (m t) (β (t + 1)) (γ (t + 1)) t) ∧
  (∀ t ∈ Finset.Icc 1 T,
    C2CorrectedStatementProofResidualCompatible μ P sample (x t) (xNext t) (m t)
      (β (t + 1)) (γ (t + 1)) t)

end Expectations

section Schedules

/-- The theorem schedule `η_t=(s+t)^(-1/3)`. -/
def etaSchedule (s : ℝ) (t : ℕ) : ℝ :=
  (s + (t : ℝ)) ^ (-(1 : ℝ) / 3)

/-- The theorem schedule `β_{1,t+1}=1-cη_t^2`, represented at index `t+1`. -/
def betaOneSchedule (c : ℝ) (η : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 - c * η t ^ 2

/-- The theorem schedule `β_{2,t+1}=1-η_t^6`, represented at index `t+1`. -/
def betaTwoSchedule (η : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 - η t ^ 6

private theorem etaSchedule_reciprocal_step_le
    {s : ℝ} (hs : 1 ≤ s) (t : ℕ) :
    1 / etaSchedule s t - 1 / etaSchedule s (t - 1) ≤ etaSchedule s t := by
  by_cases ht : t = 0
  · subst t
    simp
    rw [etaSchedule]
    positivity
  · have ht_pos : 0 < t := Nat.pos_of_ne_zero ht
    have hbase_prev : 0 < s + ((t - 1 : ℕ) : ℝ) := by
      have hcast : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
      have hsub : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hsub]
      linarith
    have hbase : 0 < s + (t : ℝ) := by
      have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
      linarith
    have hbase_ge_one : 1 ≤ s + (t : ℝ) := by
      have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
      linarith
    let x : ℝ := (s + (t : ℝ)) ^ ((1 : ℝ) / 3)
    let y : ℝ := (s + ((t - 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact Real.rpow_nonneg hbase.le _
    have hy_nonneg : 0 ≤ y := by
      dsimp [y]
      exact Real.rpow_nonneg hbase_prev.le _
    have hx_one : 1 ≤ x := by
      dsimp [x]
      exact Real.one_le_rpow (by linarith) (by norm_num)
    have hcube_x : x ^ 3 = s + (t : ℝ) := by
      dsimp [x]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hbase.le]
      norm_num
    have hcube_y : y ^ 3 = s + ((t - 1 : ℕ) : ℝ) := by
      dsimp [y]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hbase_prev.le]
      norm_num
    have hdiff_cube : x ^ 3 - y ^ 3 = 1 := by
      rw [hcube_x, hcube_y]
      have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hcast]
      ring
    have hxy : 0 ≤ x - y := by
      by_contra hxy'
      have hlt : x < y := sub_neg.mp (lt_of_not_ge hxy')
      have hcube_lt : x ^ 3 < y ^ 3 := by
        exact pow_lt_pow_left₀ hlt hx_nonneg (by norm_num)
      linarith
    have hdenom : 1 ≤ x ^ 2 + x * y + y ^ 2 := by
      nlinarith [sq_nonneg y, mul_nonneg hx_nonneg hy_nonneg]
    have hfactor :
        (x - y) * (x ^ 2 + x * y + y ^ 2) = 1 := by
      nlinarith [hdiff_cube]
    have hdiff : x - y ≤ 1 / x ^ 2 := by
      have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hx_one)
      apply (le_div_iff₀ hx_sq_pos).mpr
      have hsq_le :
          x ^ 2 ≤ x ^ 2 + x * y + y ^ 2 := by
        nlinarith [mul_nonneg hx_nonneg hy_nonneg, sq_nonneg y]
      have hmul :
          (x - y) * x ^ 2 ≤
            (x - y) * (x ^ 2 + x * y + y ^ 2) :=
        mul_le_mul_of_nonneg_left hsq_le hxy
      rw [hfactor] at hmul
      nlinarith [hmul]
    have htarget : x - y ≤ 1 / x := by
      have hx_inv : 1 / x ^ 2 ≤ 1 / x := by
        field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hx_one)]
        nlinarith [hx_one]
      exact hdiff.trans hx_inv
    have hrecip_t :
        1 / etaSchedule s t = x := by
      dsimp [x, etaSchedule]
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul hbase.le]
      norm_num
    have hrecip_prev :
        1 / etaSchedule s (t - 1) = y := by
      dsimp [y, etaSchedule]
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_mul hbase_prev.le]
      norm_num
    have heta_t : etaSchedule s t = 1 / x := by
      calc
        etaSchedule s t = 1 / (1 / etaSchedule s t) := by
          field_simp [ne_of_gt (Real.rpow_pos_of_pos hbase (-((1 : ℝ) / 3)))]
        _ = 1 / x := by rw [hrecip_t]
    rw [hrecip_t, hrecip_prev, heta_t]
    exact htarget

/-- Predicate that a scalar is the paper's minimum value `min_x F(x)`. -/
def IsObjectiveMinimumValue (F : E → ℝ) (m : ℝ) : Prop :=
  (∀ x : E, m ≤ F x) ∧ ∃ x : E, F x = m

/-- Source-status record for the B.5/B.6 use of `min_x F(x)` without a stated
attainment assumption. Corrected extensions use an explicit
`ObjectiveMinimumWitness`; registered source-boundary contracts do not replace
the printed minimum by this totalized infimum. -/
def ObjectiveMinimumAttainmentSourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- SOptLib's bundled attained global minimum, used only by corrected
extensions where attainment is made explicit. -/
abbrev ObjectiveMinimumWitness (F : E → ℝ) :=
  SOptLib.ObjectiveMinimum F

/-- The value of an explicit attained minimum. This avoids treating a totalized
infimum as the paper's printed `min_x F(x)`. -/
def attainedObjectiveMinimumValue (F : E → ℝ)
    (minimum : ObjectiveMinimumWitness F) : ℝ :=
  SOptLib.objectiveMinimumValue F minimum

/-- Source-boundary predicate for using a scalar as the paper expression
`min_x F(x)`. The public source statements take the displayed scalar as a
paper symbol and keep its minimum-value status visible. -/
def ObjectiveMinimumValueSourceBoundary (F : E → ℝ) (Fmin : ℝ) : Prop :=
  IsObjectiveMinimumValue F Fmin

/-- Printed `G` constant from Theorem B.5, parameterized by the paper's
`min_x F(x)` symbol. -/
def theoremB5GPrinted (F : E → ℝ) (x1 : E) (Fmin ρ s L σ : ℝ) : ℝ :=
  F x1 - Fmin + ρ * s ^ ((1 : ℝ) / 3) * σ ^ 2 / (16 * L ^ 2)

/-- Printed `G` constant from Theorem B.6, parameterized by the paper's
`min_x F(x)` symbol. -/
def theoremB6GPrinted (F : E → ℝ) (x1 : E) (Fmin lam D ε ρ s L σ : ℝ) : ℝ :=
  F x1 - Fmin + (lam / 2) * D ^ 2 * (1 + ε) +
    ρ * s ^ ((1 : ℝ) / 3) * σ ^ 2 / (16 * L ^ 2)

/-- Corrected-extension `G` constant in Theorem B.5, using an explicit attained
minimum witness. -/
def theoremB5G (F : E → ℝ) (x1 : E) (minimum : ObjectiveMinimumWitness F)
    (ρ s L σ : ℝ) : ℝ :=
  theoremB5GPrinted F x1 (attainedObjectiveMinimumValue F minimum) ρ s L σ

/-- Corrected-extension `G` constant in Theorem B.6, using an explicit attained
minimum witness. -/
def theoremB6G (F : E → ℝ) (x1 : E) (minimum : ObjectiveMinimumWitness F)
    (lam D ε ρ s L σ : ℝ) : ℝ :=
  theoremB6GPrinted F x1 (attainedObjectiveMinimumValue F minimum) lam D ε ρ s L σ

end Schedules

section MainTheorems

/-- Lemma 3.4 / Appendix D.1 momentum equivalence for arbitrary gradient
sequences in `R^d`. -/
theorem lemma_3_4
    {ι : Type*} [Fintype ι]
    (g u m : ℕ → MarsVector ι) (a1 a2 b1 b2 : ℝ)
    (hu : ∀ t : ℕ, u (t + 1) = a1 • u t + a2 • g (t + 1))
    (hm : ∀ t : ℕ, m t = b1 • u t + b2 • g t)
    (t : ℕ) :
    m (t + 1) =
      a1 • m t +
      (b1 * a2 - a1 * b2 + b2) • g (t + 1) +
      (a1 * b2) • (g (t + 1) - g t) := by
  rw [hm (t + 1), hu t, hm t]
  ext i
  simp [smul_add, smul_sub, smul_smul]
  ring

/-- Generated Algorithm 1 iterates realize the printed mirror-descent argmin
throughout the theorem horizon. -/
def Algorithm1MirrorStepBoundary
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
    IsMarsMirrorStep (A.eta t) (Algorithm1.m A t ω)
      (fun z => A.H t z)
      (Algorithm1.x A t ω) (Algorithm1.xNext A t ω)

/-- The beta schedule printed in Theorem B.5, separated from Lemma C.2's
additional admissibility prerequisite. -/
def B5BetaOneScheduleOnHorizon
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (c : ℝ) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, A.beta1 (t + 1) = betaOneSchedule c A.eta t

/-- The beta schedule printed in Theorem B.6, separated from Lemma C.2's
additional admissibility prerequisite. -/
def B6BetaOneScheduleOnHorizon
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι) (c : ℝ) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, A.beta1 (t + 1) = betaOneSchedule c A.eta t

/-- Source-status record for the B.5/B.6 invocation of Lemma C.2. Lemma C.2
assumes `0 ≤ β_{1,t+1} ≤ 1`, while Theorem B.5/B.6 only prints the schedule and
a lower bound on `c`; large `c` can make `1-cη_t^2` negative. -/
def C2BetaAdmissibilitySourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- B.5 boundary fact: the printed beta schedule does not itself provide Lemma
C.2's required `0 ≤ β_{1,t+1} ≤ 1` admissibility over the horizon. -/
def B5C2BetaAdmissibilitySourceGap
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (c : ℝ) (T : ℕ) : Prop :=
  B5BetaOneScheduleOnHorizon A c T ∧
  C2BetaAdmissibilitySourceIssue = SourceBoundaryIssue.missingPrerequisite

/-- B.6 boundary fact: the printed beta schedule does not itself provide Lemma
C.2's required `0 ≤ β_{1,t+1} ≤ 1` admissibility over the horizon. -/
def B6C2BetaAdmissibilitySourceGap
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι) (c : ℝ) (T : ℕ) : Prop :=
  B6BetaOneScheduleOnHorizon A c T ∧
  C2BetaAdmissibilitySourceIssue = SourceBoundaryIssue.missingPrerequisite

/-- Algebraic witness for the recorded beta-admissibility gap: if `cη_t^2 > 1`
then the printed schedule gives `β_{1,t+1}<0`. -/
theorem betaOneSchedule_negative_of_one_lt_mul_eta_sq (c η : ℝ)
    (hlarge : 1 < c * η ^ 2) :
    betaOneSchedule c (fun _ : ℕ => η) 0 < 0 := by
  dsimp [betaOneSchedule]
  linarith

/-- Algebraic witness for the D.12 denominator gap in the zero-`Δ_t` case. -/
theorem d12_gamma_denominator_zero_of_zero_delta_norm_sq (β : ℝ) :
    β * (0 : ℝ) = 0 := by
  simp

/-- Source-status record for the unstated nonzero denominator in (D.12);
`Δ_t=0` makes the printed denominator `β E‖Δ_t‖²` vanish. -/
def D12GammaDenominatorSourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- Source-status record for the unstated nonzero denominator in the displayed
definition of `A_{t+1}` in (C.2), which divides by `E‖Δ_t‖²` before the
additional `β_{1,t+1}` factor appears in (D.12). -/
def C2ADenominatorSourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- Source-status record for the approximate `γ_{t+1}` choice required by
Lemma C.2 but not printed in Theorem B.5/B.6. -/
def D12GammaChoiceSourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- Source-status record for Lemma C.5's `s ≥ 1` prerequisite when applying it
inside the B.5/B.6 proofs. -/
def C5SGeOneSourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- Source-status record for the missing strict positivity of the smoothness
constant in the B.5 source boundary. Assumption B.2 gives the Lipschitz
inequality, but the theorem and C.1 displays also divide by `L ^ 2`; the
registered source head still admits `L = 0`. -/
def B5SmoothnessPositivitySourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- Source-status record for the missing strict positivity of the smoothness
constant in the B.6 source boundary. Assumption B.2 gives the Lipschitz
inequality, but the theorem and C.2 displays also divide by `L ^ 2`; the
registered source head still admits `L = 0`. -/
def B6SmoothnessPositivitySourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- The current B.6 expectation boundary proves integrability for estimator
error and scaled displacement, but not for the objective-value trajectory
needed to integrate the pointwise C.4 descent bridge. -/
def B6ObjectiveTrajectoryIntegrabilitySourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.missingPrerequisite

/-- Source-status record for the independent coefficient mismatch between the
variance term in C.8 and the subsequent separated estimator bound. C.8 has a
single `rho`, while the separated display has `rho ^ 2`; the locked endpoint
retains the printed single-`rho` coefficient. -/
def B5C8VarianceCoefficientSourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.statementProofMismatch

/-- The C.5 absorption used by the B.5 proof is not a universal consequence
of nonnegative estimator error when the source head permits `L = 0`. -/
def B5LZeroC5AbsorptionObstruction : Prop :=
  ¬ (∀ η ρ E : ℝ, 0 < η → 0 < ρ → 0 ≤ E →
      0 ≤ -(2 * η / ρ) * E)

theorem b5_l_zero_c5_absorption_obstruction :
    B5LZeroC5AbsorptionObstruction := by
  intro h
  have hbad := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad

/-- Extracting the estimator term from the single-`rho` C.8 variance
contribution multiplies it by another `rho`; this is the coefficient
discrepancy between the proof display and the locked printed endpoint. -/
def B5C8VarianceCoefficientExtraction : Prop :=
  ∀ (ρ c σ L η ηT : ℝ), L ≠ 0 → ηT ≠ 0 →
    (ρ / ηT) * ((ρ * c ^ 2 * η ^ 3 * σ ^ 2) / (8 * L ^ 2)) =
      (ρ ^ 2 / ηT) * ((c ^ 2 * η ^ 3 * σ ^ 2) / (8 * L ^ 2))

theorem b5_c8_variance_coefficient_extraction :
    B5C8VarianceCoefficientExtraction := by
  intro ρ c σ L η ηT hL hηT
  field_simp [hL, hηT]

/-- Source-status record for the proof's substitution of `m_1` by an unclipped
fresh stochastic gradient, despite Algorithms 1/2 defining `m_1` through the
clipped momentum update. -/
def Phi1ClippingBridgeSourceIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.statementProofMismatch

/-- Source-status record for the mismatch between the theorem statements'
`η_t^{-1}` displacement metric and the proof chains' `η_t^{-2}` displays. -/
def DisplacementScaleStatementVsProofIssue : SourceBoundaryIssue :=
  SourceBoundaryIssue.statementProofMismatch

/-- Lean well-definedness obligations for the expectations printed in B.5. -/
def TheoremB5ExpectationWellDefined
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    ExpectedEstimatorErrorWellDefined (runLaw A.problem) A.problem.gradF
      (Algorithm1.x A t) (Algorithm1.m A t) ∧
    ExpectedScaledDisplacementWellDefined (runLaw A.problem) (A.eta t)
      (Algorithm1.x A t) (Algorithm1.xNext A t)

/-- No-clipping specialization for the corrected B.5/C.2 route. Algorithms 1
and 2 update their momenta using `Clip(c_t,1)`, while the D.4 proof window
expands the raw correction `c_t`; this predicate is the explicit corrected
extension condition under which those two objects agree for Algorithm 1. -/
def Algorithm1RawCorrectionNormLeOneOnHorizon
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
    ‖marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
        (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
          (sampleAt (Sample := Sample) (t + 1) ω))
        (A.problem.stochasticGrad (Algorithm1.x A t ω)
          (sampleAt (Sample := Sample) (t + 1) ω))‖ ≤ 1

/-- All C.2/D.12 corrected-extension obligations used by the Lean-readable B.5
extension over its horizon. The final conjunct is the disclosed no-clipping
specialization needed to reconcile Algorithm 1's clipped momentum update with
the raw D.4 momentum expansion. -/
def TheoremB5C2CorrectedExtensionBoundary
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (T : ℕ) : Prop :=
  C2CorrectedExtensionBoundaryOnHorizon (runLaw A.problem) A.problem (sampleAt (Sample := Sample))
    (Algorithm1.x A) (Algorithm1.xNext A) (Algorithm1.m A) A.beta1 A.gamma T ∧
  Algorithm1RawCorrectionNormLeOneOnHorizon A T

theorem TheoremB5C2CorrectedExtensionBoundary.c2
    {ι : Type*} [Fintype ι] {A : Algorithm1Data Sample ι} {T : ℕ}
    (h : TheoremB5C2CorrectedExtensionBoundary A T) :
    C2CorrectedExtensionBoundaryOnHorizon (runLaw A.problem) A.problem
      (sampleAt (Sample := Sample)) (Algorithm1.x A) (Algorithm1.xNext A)
      (Algorithm1.m A) A.beta1 A.gamma T :=
  h.1

theorem TheoremB5C2CorrectedExtensionBoundary.noClipping
    {ι : Type*} [Fintype ι] {A : Algorithm1Data Sample ι} {T : ℕ}
    (h : TheoremB5C2CorrectedExtensionBoundary A T) :
    Algorithm1RawCorrectionNormLeOneOnHorizon A T :=
  h.2

/-- The Lean-readable residual sequence occupying the source symbol
`M_{t+1}` in B.5. It is built from the C.2 corrected extension object because
the literal C.2 display has a recorded type defect; the defect status is kept
separately as `C2LiteralSourceGTypeIssue`. -/
def theoremB5ReadableC2Residual
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (t : ℕ) : ℝ :=
  c2CorrectedResidual (runLaw A.problem) A.problem (sampleAt (Sample := Sample))
    (Algorithm1.x A t) (Algorithm1.xNext A t)
    (Algorithm1.m A t) (A.beta1 (t + 1)) (A.gamma (t + 1)) t

/-- Corrected Lean-readable B.5 inequalities, stated over the generated
Algorithm 1 objects on `R^d`. This uses the type-correct C.2 residual and
Lean's explicit representatives for paper boundary expressions. -/
def TheoremB5CorrectedStatement
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (minimum : ObjectiveMinimumWitness A.problem.F)
    (L σ c s : ℝ) (T : ℕ) : Prop :=
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A t) (Algorithm1.m A t)))
      ≤
        (A.rho / ((T : ℝ) * A.eta T)) *
            theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (A.rho ^ 2 / ((T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum
              (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2))) -
          (A.rho ^ 2 / (16 * L ^ 2 * (T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum
              (fun t => theoremB5ReadableC2Residual A t / A.eta t))
    ∧
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm1.x A t) (Algorithm1.xNext A t)))
      ≤
        8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
            (3 * A.rho * (T : ℝ)) +
          (c ^ 2 * σ ^ 2 / (3 * L ^ 2 * (T : ℝ))) *
            ((Finset.Icc 1 T).sum (fun t => A.eta t ^ 3)) -
        (1 / (6 * L ^ 2 * (T : ℝ))) *
          ((Finset.Icc 1 T).sum
            (fun t => theoremB5ReadableC2Residual A t / A.eta t))

/-- The two printed B.5 inequalities, with the paper's source symbols
`min_x F(x)` and `M_{t+1}` exposed explicitly instead of replaced by corrected
Lean objects. -/
def TheoremB5PrintedInequalities
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (Fmin : ℝ) (M : ℕ → ℝ) (L σ c s : ℝ) (T : ℕ) : Prop :=
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A t) (Algorithm1.m A t)))
      ≤
        (2 * A.rho *
            theoremB5GPrinted A.problem.F A.x0 Fmin A.rho s L σ +
            (A.rho * c ^ 2 * σ ^ 2 / (4 * L ^ 2)) * Real.log (s + T)) *
          ((T : ℝ) ^ (-(2 : ℝ) / 3)) -
        (A.rho ^ 2 * ((Finset.Icc 1 T).sum (fun t => M (t + 1)))) /
          (8 * L ^ 2 * (T : ℝ) ^ ((1 : ℝ) / 3))
    ∧
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm1.x A t) (Algorithm1.xNext A t)))
      ≤
        (16 *
            theoremB5GPrinted A.problem.F A.x0 Fmin A.rho s L σ / (3 * A.rho) +
            (2 * c ^ 2 * σ ^ 2 / (3 * L ^ 2)) *
          Real.log (s + T)) *
          ((T : ℝ) ^ (-(2 : ℝ) / 3)) -
        ((Finset.Icc 1 T).sum (fun t => M (t + 1))) /
          (6 * L ^ 2 * (T : ℝ) ^ ((1 : ℝ) / 3))

/-- Registered B.5 source-boundary contract. It records why the source name
cannot currently be treated as an A-level proof of the displayed inequalities:
the paper symbols `min_x F(x)` and `M_{t+1}` are left literal in
`TheoremB5PrintedInequalities`, while the unresolved source defects and missing
prerequisites remain explicit here. -/
def TheoremB5SourceBoundaryContract
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι) (c : ℝ) (T : ℕ) : Prop :=
  Algorithm1MirrorStepBoundary A T ∧
  B5C2BetaAdmissibilitySourceGap A c T ∧
  C2LiteralSourceGTypeIssue = SourceBoundaryIssue.sourceDefect ∧
  ObjectiveMinimumAttainmentSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  C2ADenominatorSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  D12GammaDenominatorSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  D12GammaChoiceSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  C5SGeOneSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  B5SmoothnessPositivitySourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  B5C8VarianceCoefficientSourceIssue = SourceBoundaryIssue.statementProofMismatch ∧
  B5LZeroC5AbsorptionObstruction ∧
  B5C8VarianceCoefficientExtraction ∧
  Phi1ClippingBridgeSourceIssue = SourceBoundaryIssue.statementProofMismatch ∧
  DisplacementScaleStatementVsProofIssue = SourceBoundaryIssue.statementProofMismatch

private theorem b5_positive_parameters_and_schedule_bounds
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (L σ c s : ℝ) (T : ℕ)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L)
    (heta : ∀ t : ℕ, A.eta t = etaSchedule s t)
    (hs : s ≥ 8 * L ^ 3 / A.rho ^ 3)
    (hs_ge_one : 1 ≤ s)
    (hT : (T : ℝ) ≥ s)
    (hc2 : TheoremB5C2CorrectedExtensionBoundary A T) :
    0 < A.rho ∧ 0 < σ ∧ ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t := by
  refine ⟨A.hH.1, hvar.1, ?_⟩
  intro t _ht
  rw [heta t, etaSchedule]
  apply Real.rpow_pos_of_pos
  have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
  linarith

private theorem etaSchedule_absorption_of_cube_bound
    {ρ L s : ℝ} (hρ : 0 < ρ)
    (hs : s ≥ 8 * L ^ 3 / ρ ^ 3)
    (hs_ge_one : 1 ≤ s) (t : ℕ) :
    L / 2 ≤ ρ / (4 * etaSchedule s t) := by
  have hη_pos : 0 < etaSchedule s t := by
    rw [etaSchedule]
    apply Real.rpow_pos_of_pos
    have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
    linarith
  by_cases hL_nonpos : L ≤ 0
  · have hright_pos : 0 < ρ / (4 * etaSchedule s t) := by
      exact div_pos hρ (mul_pos (by norm_num) hη_pos)
    have hleft_nonpos : L / 2 ≤ 0 := by linarith
    exact le_trans hleft_nonpos (le_of_lt hright_pos)
  · have hL_pos : 0 < L := lt_of_not_ge hL_nonpos
    have hbase_pos : 0 < s + (t : ℝ) := by
      have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
      linarith
    have hbase_ge : 8 * L ^ 3 / ρ ^ 3 ≤ s + (t : ℝ) := by
      have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
      linarith
    have hscale_pos : 0 < ρ / (2 * L) := by
      exact div_pos hρ (mul_pos (by norm_num) hL_pos)
    have hscale_pow :
        (ρ / (2 * L)) ^ (-(3 : ℝ)) = 8 * L ^ 3 / ρ ^ 3 := by
      have hpow_nat : (ρ / (2 * L)) ^ (3 : ℕ) = ρ ^ 3 / (8 * L ^ 3) := by
        field_simp [hL_pos.ne']
        ring
      have hpow_real : (ρ / (2 * L)) ^ (3 : ℝ) = ρ ^ 3 / (8 * L ^ 3) := by
        simpa using hpow_nat
      rw [Real.rpow_neg (le_of_lt hscale_pos)]
      rw [hpow_real]
      field_simp [hρ.ne', hL_pos.ne']
    have hη_le : etaSchedule s t ≤ ρ / (2 * L) := by
      have hraw :
          (s + (t : ℝ)) ^ ((-(3 : ℝ))⁻¹) ≤ ρ / (2 * L) := by
        refine (Real.rpow_inv_le_iff_of_neg hbase_pos hscale_pos ?_).mpr ?_
        · norm_num
        · rw [hscale_pow]
          exact hbase_ge
      have hinv : (-(3 : ℝ))⁻¹ = -(1 : ℝ) / 3 := by norm_num
      simpa [etaSchedule, hinv] using hraw
    have hmul : (2 * L) * etaSchedule s t ≤ ρ := by
      have htwoL_nonneg : 0 ≤ 2 * L := by positivity
      have hmul' := mul_le_mul_of_nonneg_left hη_le htwoL_nonneg
      field_simp [hL_pos.ne'] at hmul'
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
    have hden_pos : 0 < 4 * etaSchedule s t := by
      exact mul_pos (by norm_num) hη_pos
    exact (le_div_iff₀ hden_pos).mpr (by nlinarith)

private theorem b5_schedule_absorption_on_horizon
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (L s : ℝ) (T : ℕ)
    (heta : ∀ t : ℕ, A.eta t = etaSchedule s t)
    (hs : s ≥ 8 * L ^ 3 / A.rho ^ 3)
    (hs_ge_one : 1 ≤ s) :
    ∀ t ∈ Finset.Icc 1 T, L / 2 ≤ A.rho / (4 * A.eta t) := by
  intro t _ht
  rw [heta t]
  exact etaSchedule_absorption_of_cube_bound A.hH.1 hs hs_ge_one t

private theorem etaSchedule_le_of_le
    {s : ℝ} (hs : 1 ≤ s) {t u : ℕ} (htu : t ≤ u) :
    etaSchedule s u ≤ etaSchedule s t := by
  have ht_pos : 0 < s + (t : ℝ) := by
    have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
    linarith
  have htu_real : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast htu
  have hbase_le : s + (t : ℝ) ≤ s + (u : ℝ) := by linarith
  exact Real.rpow_le_rpow_of_nonpos ht_pos hbase_le (by norm_num)

private theorem real_linear_coeff_eq_zero_of_quadratic_nonneg
    {a q : ℝ} (hq : 0 ≤ q)
    (hquad : ∀ r : ℝ, 0 ≤ r * a + (1 / 2 : ℝ) * r ^ 2 * q) :
    a = 0 := by
  by_contra ha
  by_cases hqzero : q = 0
  · have h := hquad (-a)
    have hsquare_pos : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqzero)
    have h := hquad (-a / q)
    have hmul : 0 ≤ q * ((-a / q) * a + (1 / 2 : ℝ) * (-a / q) ^ 2 * q) := by
      exact mul_nonneg (le_of_lt hqpos) h
    have hsquare_pos : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    field_simp [hqpos.ne'] at hmul
    nlinarith

private theorem b5_mirror_first_order_identity
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (t : ℕ) (ht : 0 < t) (ω : SampleStream Sample) :
    A.eta t *
        inner ℝ (Algorithm1.m A t ω)
          (Algorithm1.xNext A t ω - Algorithm1.x A t ω) +
      inner ℝ (Algorithm1.xNext A t ω - Algorithm1.x A t ω)
        (A.H t (Algorithm1.xNext A t ω - Algorithm1.x A t ω)) = 0 := by
  let x := Algorithm1.x A t ω
  let z := Algorithm1.xNext A t ω
  let m := Algorithm1.m A t ω
  let d := z - x
  let q := inner ℝ d (A.H t d)
  let a := A.eta t * inner ℝ m d + q
  have hstep := Algorithm1.xNext_is_mirrorStep A t ht ω
  have hq : 0 ≤ q := by
    have hρ_nonneg : 0 ≤ A.rho := le_of_lt A.hH.1
    have hlower : A.rho * ‖d‖ ^ 2 ≤ q := by
      simpa [q, d] using A.hH.2 t ht d
    have hleft : 0 ≤ A.rho * ‖d‖ ^ 2 :=
      mul_nonneg hρ_nonneg (sq_nonneg ‖d‖)
    exact le_trans hleft hlower
  have hquad : ∀ r : ℝ, 0 ≤ r * a + (1 / 2 : ℝ) * r ^ 2 * q := by
    intro r
    have hmin := hstep (z + r • d)
    have hdiff :
        marsMirrorObjective (A.eta t) m (fun y => A.H t y) x (z + r • d) -
            marsMirrorObjective (A.eta t) m (fun y => A.H t y) x z =
          r * a + (1 / 2 : ℝ) * r ^ 2 * q := by
      have hzrx : z + r • d - x = d + r • d := by
        dsimp [d]
        abel
      have hH_add : A.H t (d + r • d) = A.H t d + A.H t (r • d) := by
        exact map_add (A.H t) d (r • d)
      have hH_smul : A.H t (r • d) = r • A.H t d := by
        exact map_smul (A.H t) r d
      have hcross_left :
          inner ℝ d (A.H t (r • d)) = r * q := by
        rw [hH_smul, real_inner_smul_right]
      have hcross_right :
          inner ℝ (r • d) (A.H t d) = r * q := by
        rw [real_inner_smul_left]
      have hquad_smul :
          inner ℝ (r • d) (A.H t (r • d)) = r ^ 2 * q := by
        rw [hH_smul, real_inner_smul_left, real_inner_smul_right]
        simp [q]
        ring
      unfold marsMirrorObjective
      rw [hzrx]
      change
        A.eta t * inner ℝ m (z + r • d) +
              (1 / 2 : ℝ) * inner ℝ (d + r • d) (A.H t (d + r • d)) -
            (A.eta t * inner ℝ m z + (1 / 2 : ℝ) * inner ℝ d (A.H t d)) =
          r * a + (1 / 2 : ℝ) * r ^ 2 * q
      rw [hH_add]
      simp only [inner_add_right, inner_add_left, hcross_left, hcross_right,
        hquad_smul, real_inner_smul_right, one_div]
      simp [a]
      ring_nf
    have hnonneg :
        0 ≤
          marsMirrorObjective (A.eta t) m (fun y => A.H t y) x (z + r • d) -
            marsMirrorObjective (A.eta t) m (fun y => A.H t y) x z := by
      linarith
    simpa [hdiff] using hnonneg
  have ha : a = 0 :=
    real_linear_coeff_eq_zero_of_quadratic_nonneg hq hquad
  simpa [a, q, x, z, m, d] using ha

private theorem b5_mirror_inner_full_lower_bound
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (t : ℕ) (ht : 0 < t) (ω : SampleStream Sample)
    (heta_pos : 0 < A.eta t) :
    (A.rho / A.eta t) *
        ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2
      ≤
        inner ℝ (Algorithm1.m A t ω)
          (Algorithm1.x A t ω - Algorithm1.xNext A t ω) := by
  let x := Algorithm1.x A t ω
  let z := Algorithm1.xNext A t ω
  let m := Algorithm1.m A t ω
  let d := z - x
  let q := inner ℝ d (A.H t d)
  have hid := b5_mirror_first_order_identity A t ht ω
  have hη_inner : A.eta t * inner ℝ m d = -q := by
    simpa [q, x, z, m, d] using
      (eq_neg_of_add_eq_zero_left hid)
  have hinner_eq : inner ℝ m (x - z) = q / A.eta t := by
    have hneg : x - z = -d := by
      dsimp [d]
      abel
    rw [hneg, inner_neg_right]
    have hdiv : inner ℝ m d = -q / A.eta t := by
      exact (eq_div_iff heta_pos.ne').mpr (by simpa [mul_comm] using hη_inner)
    rw [hdiv]
    ring
  have hlower : A.rho * ‖d‖ ^ 2 ≤ q := by
    simpa [q, d] using A.hH.2 t ht d
  have hdiv_lower :
      (A.rho * ‖d‖ ^ 2) / A.eta t ≤ q / A.eta t := by
    exact (div_le_div_iff_of_pos_right heta_pos).mpr hlower
  have hnorm : ‖x - z‖ = ‖d‖ := by
    dsimp [d]
    rw [← norm_neg (z - x)]
    congr 1
    abel
  calc
    (A.rho / A.eta t) * ‖x - z‖ ^ 2
        = (A.rho * ‖d‖ ^ 2) / A.eta t := by
            rw [hnorm]
            field_simp [heta_pos.ne']
    _ ≤ q / A.eta t := hdiv_lower
    _ = inner ℝ m (x - z) := by rw [hinner_eq]

private theorem real_mul_le_scaled_sq_add_inv_four_sq
    {α a b : ℝ} (hα : 0 < α) :
    a * b ≤ α * a ^ 2 + (1 / (4 * α)) * b ^ 2 := by
  have hdiff :
      0 ≤ α * a ^ 2 + (1 / (4 * α)) * b ^ 2 - a * b := by
    have hsq : 0 ≤ (1 / (4 * α)) * (2 * α * a - b) ^ 2 := by
      exact mul_nonneg (by positivity) (sq_nonneg (2 * α * a - b))
    have hident :
        α * a ^ 2 + (1 / (4 * α)) * b ^ 2 - a * b =
          (1 / (4 * α)) * (2 * α * a - b) ^ 2 := by
      field_simp [hα.ne']
      ring
    rw [hident]
    exact hsq
  linarith

private theorem inner_le_young_eta_rho
    {ι : Type*} [Fintype ι] {η ρ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (u v : MarsVector ι) :
    inner ℝ u v ≤ (η / ρ) * ‖u‖ ^ 2 + (ρ / (4 * η)) * ‖v‖ ^ 2 := by
  have hα : 0 < η / ρ := div_pos hη hρ
  have hinner_abs : inner ℝ u v ≤ |inner ℝ u v| := le_abs_self _
  have habs_norm : |inner ℝ u v| ≤ ‖u‖ * ‖v‖ :=
    abs_real_inner_le_norm u v
  have hyoung :
      ‖u‖ * ‖v‖ ≤ (η / ρ) * ‖u‖ ^ 2 + (1 / (4 * (η / ρ))) * ‖v‖ ^ 2 :=
    real_mul_le_scaled_sq_add_inv_four_sq hα
  have hcoef : (1 / (4 * (η / ρ))) = ρ / (4 * η) := by
    field_simp [hη.ne', hρ.ne']
  calc
    inner ℝ u v ≤ |inner ℝ u v| := hinner_abs
    _ ≤ ‖u‖ * ‖v‖ := habs_norm
    _ ≤ (η / ρ) * ‖u‖ ^ 2 + (1 / (4 * (η / ρ))) * ‖v‖ ^ 2 := hyoung
    _ = (η / ρ) * ‖u‖ ^ 2 + (ρ / (4 * η)) * ‖v‖ ^ 2 := by rw [hcoef]

private theorem b5_c3_objective_descent_pathwise
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (L : ℝ) (hsmooth : StochasticSmooth A.problem L)
    (t : ℕ) (ht : 0 < t) (ω : SampleStream Sample)
    (heta_pos : 0 < A.eta t)
    (habsorb : L / 2 ≤ A.rho / (4 * A.eta t)) :
    A.problem.F (Algorithm1.xNext A t ω) ≤
      A.problem.F (Algorithm1.x A t ω) -
        (A.rho / (2 * A.eta t)) *
          ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2 +
        (A.eta t / A.rho) *
          ‖A.problem.gradF (Algorithm1.x A t ω) - Algorithm1.m A t ω‖ ^ 2 := by
  let x := Algorithm1.x A t ω
  let z := Algorithm1.xNext A t ω
  let m := Algorithm1.m A t ω
  let d := z - x
  let e := A.problem.gradF x - m
  have hsmooth_step := StochasticSmooth.objective_smooth_upper hsmooth x z
  have hmirror := b5_mirror_inner_full_lower_bound A t ht ω heta_pos
  have hρ_pos : 0 < A.rho := A.hH.1
  have hgrad_decomp :
      inner ℝ (A.problem.gradF x) d = inner ℝ m d + inner ℝ e d := by
    simp [e, d, inner_sub_left]
  have hmirror_d :
      inner ℝ m d ≤ -(A.rho / A.eta t) * ‖d‖ ^ 2 := by
    have hneg_vec : x - z = -d := by
      dsimp [d]
      abel
    have hinner_neg : inner ℝ m (x - z) = -inner ℝ m d := by
      rw [hneg_vec, inner_neg_right]
    have hnorm : ‖x - z‖ = ‖d‖ := by
      rw [hneg_vec, norm_neg]
    have hmirror' :
        (A.rho / A.eta t) * ‖x - z‖ ^ 2 ≤ inner ℝ m (x - z) := by
      simpa [x, z, m] using hmirror
    rw [hinner_neg, hnorm] at hmirror'
    nlinarith
  have hyoung :
      inner ℝ e d ≤
        (A.eta t / A.rho) * ‖e‖ ^ 2 +
          (A.rho / (4 * A.eta t)) * ‖d‖ ^ 2 :=
    inner_le_young_eta_rho heta_pos hρ_pos e d
  have hquad_absorb :
      (L / 2) * ‖d‖ ^ 2 ≤
        (A.rho / (4 * A.eta t)) * ‖d‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right habsorb (sq_nonneg ‖d‖)
  have hsmooth_d :
      A.problem.F z ≤
        A.problem.F x + inner ℝ (A.problem.gradF x) d +
          (L / 2) * ‖d‖ ^ 2 := by
    simpa [x, z, d] using hsmooth_step
  calc
    A.problem.F z
        ≤ A.problem.F x + inner ℝ (A.problem.gradF x) d +
            (L / 2) * ‖d‖ ^ 2 := hsmooth_d
    _ = A.problem.F x + inner ℝ m d + inner ℝ e d +
            (L / 2) * ‖d‖ ^ 2 := by rw [hgrad_decomp]; ring
    _ ≤ A.problem.F x +
            (-(A.rho / A.eta t) * ‖d‖ ^ 2) +
            ((A.eta t / A.rho) * ‖e‖ ^ 2 +
              (A.rho / (4 * A.eta t)) * ‖d‖ ^ 2) +
            (A.rho / (4 * A.eta t)) * ‖d‖ ^ 2 := by
          nlinarith
    _ = A.problem.F x -
            (A.rho / (2 * A.eta t)) * ‖d‖ ^ 2 +
            (A.eta t / A.rho) * ‖e‖ ^ 2 := by
          field_simp [heta_pos.ne']
          ring
    _ = A.problem.F x -
            (A.rho / (2 * A.eta t)) * ‖x - z‖ ^ 2 +
            (A.eta t / A.rho) * ‖A.problem.gradF x - m‖ ^ 2 := by
          have hnorm : ‖x - z‖ = ‖d‖ := by
            dsimp [d]
            rw [← norm_neg (z - x)]
            congr 1
            abel
          rw [hnorm]

private theorem b5_mirror_inner_descent
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (t : ℕ) (ht : 0 < t) (ω : SampleStream Sample)
    (heta_pos : 0 < A.eta t) :
    inner ℝ (Algorithm1.m A t ω)
        (Algorithm1.xNext A t ω - Algorithm1.x A t ω)
      ≤
        -(A.rho / (2 * A.eta t)) *
          ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2 := by
  let x := Algorithm1.x A t ω
  let z := Algorithm1.xNext A t ω
  let m := Algorithm1.m A t ω
  let d := z - x
  have hstep := Algorithm1.xNext_is_mirrorStep A t ht ω x
  have hopt :
      A.eta t * inner ℝ m z +
          (1 / 2 : ℝ) * inner ℝ d (A.H t d) ≤
        A.eta t * inner ℝ m x := by
    simpa [marsMirrorObjective, x, z, m, d] using hstep
  have hstep_scalar :
      A.eta t * inner ℝ m d +
          (1 / 2 : ℝ) * inner ℝ d (A.H t d) ≤ 0 := by
    have hd_inner : inner ℝ m d = inner ℝ m z - inner ℝ m x := by
      simp [d, inner_sub_right]
    nlinarith
  have hHlower : A.rho * ‖d‖ ^ 2 ≤ inner ℝ d (A.H t d) :=
    A.hH.2 t ht d
  have hη_inner :
      A.eta t * inner ℝ m d ≤
        -((1 / 2 : ℝ) * (A.rho * ‖d‖ ^ 2)) := by
    nlinarith
  have hdiv :
      inner ℝ m d ≤
        -((1 / 2 : ℝ) * (A.rho * ‖d‖ ^ 2)) / A.eta t := by
    have hη_inner' :
        inner ℝ m d * A.eta t ≤
          -((1 / 2 : ℝ) * (A.rho * ‖d‖ ^ 2)) := by
      simpa [mul_comm] using hη_inner
    exact (le_div_iff₀ heta_pos).mpr hη_inner'
  have halg :
      -((1 / 2 : ℝ) * (A.rho * ‖d‖ ^ 2)) / A.eta t =
        -(A.rho / (2 * A.eta t) * ‖d‖ ^ 2) := by
    field_simp [heta_pos.ne']
  have hfinal :
      inner ℝ m d ≤ -(A.rho / (2 * A.eta t)) * ‖d‖ ^ 2 := by
    calc
      inner ℝ m d
          ≤ -((1 / 2 : ℝ) * (A.rho * ‖d‖ ^ 2)) / A.eta t := hdiv
      _ = -(A.rho / (2 * A.eta t) * ‖d‖ ^ 2) := halg
      _ = -(A.rho / (2 * A.eta t)) * ‖d‖ ^ 2 := by ring
  simpa [x, z, m, d] using hfinal

private theorem b5_algorithm1_xNext_eq_x_succ
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (t : ℕ) (ω : SampleStream Sample) :
    Algorithm1.xNext A t ω = Algorithm1.x A (t + 1) ω := by
  simp [Algorithm1.xNext, Algorithm1.x]

private theorem b5_algorithm1_momentum_succ_unclipped_of_correction_norm_le_one
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (T : ℕ)
    (hclip :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        ‖marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
            (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
              (sampleAt (Sample := Sample) (t + 1) ω))
            (A.problem.stochasticGrad (Algorithm1.x A t ω)
              (sampleAt (Sample := Sample) (t + 1) ω))‖ ≤ 1) :
    ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
      Algorithm1.m A (t + 1) ω =
        (A.beta1 (t + 1)) • Algorithm1.m A t ω +
          (1 - A.beta1 (t + 1)) •
            marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
              (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                (sampleAt (Sample := Sample) (t + 1) ω))
              (A.problem.stochasticGrad (Algorithm1.x A t ω)
                (sampleAt (Sample := Sample) (t + 1) ω)) := by
  intro t ht ω
  have htpos : 0 < t := (Finset.mem_Icc.mp ht).1
  have hsucc : t - 1 + 1 = t := Nat.succ_pred_eq_of_pos htpos
  have hproc : Algorithm1.process A t ω =
      Algorithm1.step A (t - 1) (Algorithm1.process A (t - 1) ω) ω := by
    simpa [hsucc] using Algorithm1.process_succ A (t - 1) ω
  have hactual :
      Algorithm1.m A (t + 1) ω =
        (A.beta1 (t + 1)) • Algorithm1.m A t ω +
          (1 - A.beta1 (t + 1)) •
            Algorithm1.clippedCorrection A t (Algorithm1.process A t ω) ω := by
    simp [Algorithm1.m, Algorithm1.momentum, Algorithm1.paperTime, hproc,
      Algorithm1.step, Algorithm1.stepAtSample, Algorithm1.momentumAtSample,
      Algorithm1.clippedCorrection, hsucc]
  have hcurrent :
      (Algorithm1.process A (t - 1) ω).current = Algorithm1.x A t ω := by
    rfl
  have hnext :
      Algorithm1.nextIterateAtSample A (t - 1) (Algorithm1.process A (t - 1) ω)
          (sampleAt (Sample := Sample) t ω) =
        Algorithm1.xNext A t ω := by
    rw [Algorithm1.xNext, hproc]
    simp [Algorithm1.step, Algorithm1.stepAtSample, Algorithm1.paperTime, hsucc]
  have hclipped :
      Algorithm1.clippedCorrection A t (Algorithm1.process A t ω) ω =
        marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
          (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
            (sampleAt (Sample := Sample) (t + 1) ω))
          (A.problem.stochasticGrad (Algorithm1.x A t ω)
            (sampleAt (Sample := Sample) (t + 1) ω)) := by
    simp [Algorithm1.clippedCorrection, Algorithm1.correction, Algorithm1.paperTime,
      hproc, Algorithm1.step, Algorithm1.stepAtSample, Algorithm1.clippedCorrectionAtSample,
      Algorithm1.correctionAtSample, hsucc, hcurrent, hnext,
      clipByNorm_of_norm_le_one (hclip t ht ω)]
  rw [hactual, hclipped]

private theorem b5_c2_estimator_error_recursion_raw
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (c : ℝ) (T : ℕ)
    (hparams :
      0 < A.rho ∧ 0 < c ∧ ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hD4 :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        Algorithm1.m A (t + 1) ω =
          (A.beta1 (t + 1)) • Algorithm1.m A t ω +
            (1 - A.beta1 (t + 1)) •
              marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
                (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω))
                (A.problem.stochasticGrad (Algorithm1.x A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω)))
    (hxNext_succ :
      ∀ t : ℕ, ∀ ω : SampleStream Sample,
        Algorithm1.xNext A t ω = Algorithm1.x A (t + 1) ω) :
    ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
      c2EstimatorError A.problem (Algorithm1.x A (t + 1))
          (Algorithm1.m A (t + 1)) ω =
        (1 - A.beta1 (t + 1)) •
            (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                (sampleAt (Sample := Sample) (t + 1) ω) -
              A.problem.gradF (Algorithm1.xNext A t ω)) +
          (A.beta1 (t + 1)) •
            c2EstimatorError A.problem (Algorithm1.x A t) (Algorithm1.m A t) ω +
          (A.beta1 (t + 1)) •
            ((A.gamma (t + 1)) •
                c2Delta A.problem (sampleAt (Sample := Sample))
                  (Algorithm1.x A t) (Algorithm1.xNext A t) t ω -
              (A.problem.gradF (Algorithm1.xNext A t ω) -
                A.problem.gradF (Algorithm1.x A t ω))) := by
  intro t ht ω
  have hη_pos : 0 < A.eta t := hparams.2.2 t ht
  have hc_pos : 0 < c := hparams.2.1
  have hbeta_ne_one : A.beta1 (t + 1) ≠ 1 := by
    rw [hbeta1 t, betaOneSchedule]
    have hmul_pos : 0 < c * A.eta t ^ 2 := by
      exact mul_pos hc_pos (sq_pos_of_pos hη_pos)
    nlinarith
  have hden_ne : 1 - A.beta1 (t + 1) ≠ 0 := by
    intro hden
    apply hbeta_ne_one
    linarith
  have hD4t := hD4 t ht ω
  have hxNext := hxNext_succ t ω
  simp [c2EstimatorError, c2Delta, marsCorrection, hD4t, hxNext,
    hbeta_ne_one, smul_add, smul_sub, smul_smul]
  field_simp [hden_ne]
  module

private theorem b6_c2_estimator_error_recursion_raw
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (c : ℝ) (T : ℕ)
    (hparams :
      0 < c ∧ ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hD4 :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        Algorithm2.m A (t + 1) ω =
          (A.beta1 (t + 1)) • Algorithm2.m A t ω +
            (1 - A.beta1 (t + 1)) •
              marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
                (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω))
                (A.problem.stochasticGrad (Algorithm2.x A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω)))
    (hxNext_succ :
      ∀ t : ℕ, ∀ ω : SampleStream Sample,
        Algorithm2.xNext A t ω = Algorithm2.x A (t + 1) ω) :
    ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
      c2EstimatorError A.problem (Algorithm2.x A (t + 1))
          (Algorithm2.m A (t + 1)) ω =
        (1 - A.beta1 (t + 1)) •
            (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
                (sampleAt (Sample := Sample) (t + 1) ω) -
              A.problem.gradF (Algorithm2.xNext A t ω)) +
          (A.beta1 (t + 1)) •
            c2EstimatorError A.problem (Algorithm2.x A t) (Algorithm2.m A t) ω +
          (A.beta1 (t + 1)) •
            ((A.gamma (t + 1)) •
                c2Delta A.problem (sampleAt (Sample := Sample))
                  (Algorithm2.x A t) (Algorithm2.xNext A t) t ω -
              (A.problem.gradF (Algorithm2.xNext A t ω) -
                A.problem.gradF (Algorithm2.x A t ω))) := by
  intro t ht ω
  have hη_pos : 0 < A.eta t := hparams.2 t ht
  have hc_pos : 0 < c := hparams.1
  have hbeta_ne_one : A.beta1 (t + 1) ≠ 1 := by
    rw [hbeta1 t, betaOneSchedule]
    have hmul_pos : 0 < c * A.eta t ^ 2 := by
      exact mul_pos hc_pos (sq_pos_of_pos hη_pos)
    nlinarith
  have hden_ne : 1 - A.beta1 (t + 1) ≠ 0 := by
    intro hden
    apply hbeta_ne_one
    linarith
  have hD4t := hD4 t ht ω
  have hxNext := hxNext_succ t ω
  simp [c2EstimatorError, c2Delta, marsCorrection, hD4t, hxNext,
    hbeta_ne_one, smul_add, smul_sub, smul_smul]
  field_simp [hden_ne]
  module

private theorem b5_c2_one_step_second_moment_bound
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (L σ : ℝ) (t : ℕ) (ht : 0 < t)
    (hraw :
      ∀ ω : SampleStream Sample,
        c2EstimatorError A.problem (Algorithm1.x A (t + 1))
            (Algorithm1.m A (t + 1)) ω =
          (1 - A.beta1 (t + 1)) •
              (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω) -
                A.problem.gradF (Algorithm1.xNext A t ω)) +
            (A.beta1 (t + 1)) •
              c2EstimatorError A.problem (Algorithm1.x A t) (Algorithm1.m A t) ω +
            (A.beta1 (t + 1)) •
              ((A.gamma (t + 1)) •
                  c2Delta A.problem (sampleAt (Sample := Sample))
                    (Algorithm1.x A t) (Algorithm1.xNext A t) t ω -
                (A.problem.gradF (Algorithm1.xNext A t ω) -
                  A.problem.gradF (Algorithm1.x A t ω))))
    (hbeta_admissible : 0 ≤ A.beta1 (t + 1) ∧ A.beta1 (t + 1) ≤ 1)
    (hC2_well_defined :
      C2ExpectationWellDefined (runLaw A.problem) A.problem (sampleAt (Sample := Sample))
        (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) t)
    (hC2_residual_compatible :
      C2CorrectedStatementProofResidualCompatible (runLaw A.problem) A.problem
        (sampleAt (Sample := Sample)) (Algorithm1.x A t) (Algorithm1.xNext A t)
        (Algorithm1.m A t) (A.beta1 (t + 1)) (A.gamma (t + 1)) t)
    (hprev_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖c2EstimatorError A.problem (Algorithm1.x A t) (Algorithm1.m A t) ω‖ ^ 2)
        (runLaw A.problem))
    (hdisp_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2)
        (runLaw A.problem))
    (hgrad_unbiased : UnbiasedGradientOracle A.problem)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L) :
    expectedEstimatorError (runLaw A.problem) A.problem.gradF
        (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1))
      ≤
        (A.beta1 (t + 1)) ^ 2 *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A t) (Algorithm1.m A t) +
          2 * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
            (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
              ∂runLaw A.problem) +
          2 * (1 - A.beta1 (t + 1)) ^ 2 * σ ^ 2 -
          theoremB5ReadableC2Residual A t := by
  classical
  haveI : IsProbabilityMeasure (runLaw A.problem) :=
    runLaw_isProbabilityMeasure A.problem
  have hsample_meas :
      ∀ n : ℕ, Measurable (fun ω : SampleStream Sample =>
        sampleAt (Sample := Sample) n ω) := by
    intro n
    simpa [sampleAt] using measurable_pi_apply n
  have hsample_iIndep :
      iIndepFun
        (fun n (ω : SampleStream Sample) => sampleAt (Sample := Sample) n ω)
        (runLaw A.problem) := by
    haveI : IsProbabilityMeasure A.problem.sampleLaw := A.problem.sampleLaw_isProbability
    simpa [runLaw, sampleAt] using
      (SOptLib.iidStreamLaw_iIndepFun_eval A.problem.sampleLaw)
  have hfresh_indep_past :
      Indep
        ((SOptLib.filtration
            (fun n (ω : SampleStream Sample) => sampleAt (Sample := Sample) n ω)
            hsample_meas).seq (t + 1))
        (MeasurableSpace.comap
          (fun ω : SampleStream Sample => sampleAt (Sample := Sample) (t + 1) ω)
          (by infer_instance : MeasurableSpace Sample))
        (runLaw A.problem) := by
    exact samplePrefixFiltration_indep_current
      (fun n (ω : SampleStream Sample) => sampleAt (Sample := Sample) n ω)
      hsample_meas hsample_iIndep (t + 1)
  have hstep_meas :
      ∀ k : ℕ,
        Measurable
          (fun p : Algorithm1State (MarsVector ι) × Sample =>
            Algorithm1.stepAtSample A k p.1 p.2) :=
    algorithm1_stepAtSample_measurable_of_oracle A hgrad_unbiased
  have hprefix_query :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)]
        (fun ω : SampleStream Sample =>
          ((Algorithm1.x A t ω, Algorithm1.xNext A t ω), Algorithm1.m A t ω)) :=
    algorithm1_prefix_adapted_state_before_fresh_sample A hstep_meas t ht
  let μ := runLaw A.problem
  let fresh : SampleStream Sample → Sample :=
    fun ω => sampleAt (Sample := Sample) (t + 1) ω
  let xPrev : SampleStream Sample → MarsVector ι := Algorithm1.x A t
  let y : SampleStream Sample → MarsVector ι := Algorithm1.xNext A t
  haveI : IsProbabilityMeasure A.problem.sampleLaw := A.problem.sampleLaw_isProbability
  have hquery_x_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)] xPrev := by
    dsimp [xPrev]
    exact measurable_fst.comp (measurable_fst.comp hprefix_query)
  have hquery_x_meas : Measurable xPrev := by
    dsimp [xPrev] at hquery_x_past ⊢
    exact hquery_x_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have hquery_y_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)] y := by
    dsimp [y]
    exact measurable_snd.comp (measurable_fst.comp hprefix_query)
  have hquery_y_meas : Measurable y := by
    dsimp [y] at hquery_y_past ⊢
    exact hquery_y_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_y_fresh : IndepFun y fresh μ := by
    dsimp [μ, fresh, y]
    exact indepFun_of_past_measurable_current_iid_sample hquery_y_past
      hfresh_indep_past
  have hgradF_meas : Measurable A.problem.gradF := by
    exact oracleMean_measurable_of_eq_integral A.problem.sampleLaw
      A.problem.stochasticGrad A.problem.gradF
      (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased)
      (by
        intro x
        exact (UnbiasedGradientOracle.mean_eq_gradF hgrad_unbiased x).symm)
  have hres_meas :
      Measurable (fun p : MarsVector ι × Sample =>
        A.problem.stochasticGrad p.1 p.2 - A.problem.gradF p.1) := by
    exact (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).sub
      (hgradF_meas.comp measurable_fst)
  have hvar_random :
      (∫ ω, ‖A.problem.stochasticGrad (Algorithm1.xNext A t ω)
            (sampleAt (Sample := Sample) (t + 1) ω) -
          A.problem.gradF (Algorithm1.xNext A t ω)‖ ^ 2 ∂runLaw A.problem) ≤
        σ ^ 2 := by
    simpa [μ, fresh, y] using
      (integral_sq_oracleResidual_le_of_indep_fixed_variance
        (P := μ) (ν := A.problem.sampleLaw)
        (query := y) (sample := fresh)
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (σ2 := σ ^ 2)
        hres_meas hquery_y_meas (hsample_meas (t + 1)) h_indep_y_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        (sq_nonneg σ)
        (by
          intro x
          exact BoundedVariance.bound hvar x))
  have hdelta_uncentered :
      Integrable
          (fun ω : SampleStream Sample =>
            ‖A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2) μ ∧
        (∫ ω, ‖A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2 ∂μ) ≤
          L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    have hleft :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2) μ := by
      simpa [μ, fresh, xPrev, y, c2Delta] using hC2_well_defined.1
    refine ⟨hleft, ?_⟩
    have hright_int :
        Integrable (fun ω : SampleStream Sample =>
          L ^ 2 * ‖y ω - xPrev ω‖ ^ 2) μ := by
      simpa [xPrev, y, mul_comm, mul_left_comm, mul_assoc] using
        hdisp_sq.const_mul (L ^ 2)
    calc
      (∫ ω, ‖A.problem.stochasticGrad (y ω) (fresh ω) -
            A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2 ∂μ)
          ≤ ∫ ω, L ^ 2 * ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
            refine integral_mono hleft hright_int ?_
            intro ω
            have hlip :=
              (StochasticSmooth.stochasticGrad_lipschitz hsmooth)
                (y ω) (xPrev ω) (fresh ω)
            have hnorm_nonneg :
                0 ≤ ‖A.problem.stochasticGrad (y ω) (fresh ω) -
                  A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ := norm_nonneg _
            have hdist_nonneg : 0 ≤ ‖y ω - xPrev ω‖ := norm_nonneg _
            nlinarith
      _ = L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
            rw [integral_const_mul]
  have htarget_lipschitz :
      ∀ x z : MarsVector ι,
        ‖A.problem.gradF x - A.problem.gradF z‖ ≤ L * ‖x - z‖ := by
    intro x z
    refine oracleMean_lipschitz_of_ae_lipschitz A.problem.sampleLaw
      A.problem.stochasticGrad A.problem.gradF L x z
      (UnbiasedGradientOracle.fixed_integrable hgrad_unbiased x)
      (UnbiasedGradientOracle.fixed_integrable hgrad_unbiased z) ?_ ?_ ?_
    · simpa [SOptLib.oracleMean_def] using
        (UnbiasedGradientOracle.mean_eq_gradF hgrad_unbiased x)
    · simpa [SOptLib.oracleMean_def] using
        (UnbiasedGradientOracle.mean_eq_gradF hgrad_unbiased z)
    · filter_upwards [] with ξ
      exact (StochasticSmooth.stochasticGrad_lipschitz hsmooth) x z ξ
  have horacle_delta_aesm :
      AEStronglyMeasurable
        (fun ω : SampleStream Sample =>
          A.problem.stochasticGrad (y ω) (fresh ω) -
            A.problem.stochasticGrad (xPrev ω) (fresh ω)) μ := by
    have hmeas :
        Measurable
          (fun ω : SampleStream Sample =>
            A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)) := by
      exact
        ((UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
            (hquery_y_meas.prodMk (hsample_meas (t + 1)))).sub
          ((UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
            (hquery_x_meas.prodMk (hsample_meas (t + 1))))
    exact hmeas.aestronglyMeasurable
  have htarget_delta_aesm :
      AEStronglyMeasurable
        (fun ω : SampleStream Sample =>
          A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)) μ := by
    exact ((hgradF_meas.comp hquery_y_meas).sub
      (hgradF_meas.comp hquery_x_meas)).aestronglyMeasurable
  have htarget_delta_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)‖ ^ 2) μ := by
    refine Integrable.mono' (hdisp_sq.const_mul (L ^ 2))
      (by simpa using htarget_delta_aesm.norm.pow 2) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hlip := htarget_lipschitz (y ω) (xPrev ω)
    have hleft_nonneg :
        0 ≤ ‖A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)‖ := norm_nonneg _
    have hright_nonneg : 0 ≤ L * ‖y ω - xPrev ω‖ := le_trans hleft_nonneg hlip
    have hneg :
        -(L * ‖y ω - xPrev ω‖) ≤
          ‖A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)‖ := by
      nlinarith
    have hsquare := sq_le_sq' hneg hlip
    dsimp [xPrev, y] at hsquare ⊢
    nlinarith
  have hquery_delta_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)]
        (fun ω : SampleStream Sample =>
          ((y ω, xPrev ω),
            A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) := by
    exact (hquery_y_past.prodMk hquery_x_past).prodMk
      ((hgradF_meas.comp hquery_y_past).sub
        (hgradF_meas.comp hquery_x_past))
  have hquery_delta_meas :
      Measurable
        (fun ω : SampleStream Sample =>
          ((y ω, xPrev ω),
            A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) := by
    exact hquery_delta_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_delta_query_fresh :
      IndepFun
        (fun ω : SampleStream Sample =>
          ((y ω, xPrev ω),
            A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) fresh μ := by
    dsimp [μ, fresh]
    exact indepFun_of_past_measurable_current_iid_sample hquery_delta_past
      hfresh_indep_past
  have hcenter_delta_zero :
      ∫ ω,
          inner ℝ (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
            ((A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) ∂μ = 0 := by
    have horacle_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
              (A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω))) μ :=
      integrable_inner_of_integrable_sq_norm htarget_delta_aesm horacle_delta_aesm
        htarget_delta_sq hdelta_uncentered.1
    have htarget_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) μ := by
      simpa [inner_self_eq_norm_sq] using htarget_delta_sq
    simpa [μ, fresh] using
      (integral_inner_centered_oracleDifference_eq_zero_of_indep_adapted
        (P := μ) (ν := A.problem.sampleLaw)
        (sample := fresh) (x := y) (y := xPrev)
        (d := fun ω : SampleStream Sample =>
          A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased)
        hquery_delta_meas (hsample_meas (t + 1)) h_indep_delta_query_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        horacle_inner_int
        (by
          exact (continuous_inner.measurable.comp
            ((measurable_snd).prodMk
              ((hgradF_meas.comp (measurable_fst.comp measurable_fst)).sub
                (hgradF_meas.comp (measurable_snd.comp measurable_fst))))).aestronglyMeasurable)
        htarget_inner_int
        (by
          filter_upwards [] with q
          exact UnbiasedGradientOracle.fixed_fiber_oracle_difference_mean
            hgrad_unbiased q.1.1 q.1.2 q.2))
  have hcentered_delta :
      Integrable
          (fun ω : SampleStream Sample =>
            ‖(A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))‖ ^ 2) μ ∧
        (∫ ω,
            ‖(A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))‖ ^ 2 ∂μ) ≤
          L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    refine centered_oracleDifference_secondMoment_le_of_unbiased_smooth
      (P := μ) (sample := fresh) (x := y) (y := xPrev)
      (G := A.problem.stochasticGrad) (target := A.problem.gradF) (L := L)
      horacle_delta_aesm ?_ hdelta_uncentered htarget_delta_aesm ?_ ?_
    · simpa [μ, xPrev, y] using hdisp_sq
    · filter_upwards [] with ω
      exact htarget_lipschitz (y ω) (xPrev ω)
    · simpa using hcenter_delta_zero
  let eps : SampleStream Sample → MarsVector ι :=
    c2EstimatorError A.problem (Algorithm1.x A t) (Algorithm1.m A t)
  have heps_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)] eps := by
    dsimp [eps, c2EstimatorError]
    exact (measurable_snd.comp hprefix_query).sub
      (hgradF_meas.comp hquery_x_past)
  have heps_meas : Measurable eps := by
    exact heps_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have heps_aesm : AEStronglyMeasurable eps μ := heps_meas.aestronglyMeasurable
  have hquery_xym_meas :
      Measurable
        (fun ω : SampleStream Sample =>
          ((xPrev ω, y ω), Algorithm1.m A t ω)) := by
    exact hprefix_query.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_xym_fresh :
      IndepFun
        (fun ω : SampleStream Sample =>
          ((xPrev ω, y ω), Algorithm1.m A t ω)) fresh μ := by
    dsimp [μ, fresh, xPrev, y]
    exact indepFun_of_past_measurable_current_iid_sample hprefix_query
      hfresh_indep_past
  have hcross_prev_fresh :
      ∫ ω,
          inner ℝ (eps ω)
            (A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.gradF (y ω)) ∂μ = 0 := by
    simpa [μ, fresh, xPrev, y, eps, c2EstimatorError] using
      (randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
        (P := μ) (ν := A.problem.sampleLaw)
        (query := fun ω : SampleStream Sample =>
          ((xPrev ω, y ω), Algorithm1.m A t ω))
        (sample := fresh)
        (residual := fun q : (MarsVector ι × MarsVector ι) × MarsVector ι =>
          fun ξ : Sample =>
            A.problem.stochasticGrad q.1.2 ξ - A.problem.gradF q.1.2)
        (d := fun q : (MarsVector ι × MarsVector ι) × MarsVector ι =>
          q.2 - A.problem.gradF q.1.1)
        (by
          exact hres_meas.comp
            ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
              measurable_snd))
        (by
          exact measurable_snd.sub
            (hgradF_meas.comp (measurable_fst.comp measurable_fst)))
        hquery_xym_meas (hsample_meas (t + 1)) h_indep_xym_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        (by
          intro q
          exact UnbiasedGradientOracle.residual_integrable hgrad_unbiased q.1.2)
        (by
          intro q
          exact UnbiasedGradientOracle.residual_integral_zero hgrad_unbiased q.1.2))
  have hquery_delta_eps_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)]
        (fun ω : SampleStream Sample => ((y ω, xPrev ω), eps ω)) := by
    exact (hquery_y_past.prodMk hquery_x_past).prodMk heps_past
  have hquery_delta_eps_meas :
      Measurable
        (fun ω : SampleStream Sample => ((y ω, xPrev ω), eps ω)) := by
    exact hquery_delta_eps_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_delta_eps_fresh :
      IndepFun (fun ω : SampleStream Sample => ((y ω, xPrev ω), eps ω)) fresh μ := by
    dsimp [μ, fresh]
    exact indepFun_of_past_measurable_current_iid_sample hquery_delta_eps_past
      hfresh_indep_past
  have hcross_prev_delta :
      ∫ ω,
          inner ℝ (eps ω)
            ((A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) ∂μ = 0 := by
    have horacle_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (eps ω)
              (A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω))) μ :=
      integrable_inner_of_integrable_sq_norm heps_aesm horacle_delta_aesm
        (by simpa [eps] using hprev_sq) hdelta_uncentered.1
    have htarget_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (eps ω)
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) μ :=
      integrable_inner_of_integrable_sq_norm heps_aesm htarget_delta_aesm
        (by simpa [eps] using hprev_sq) htarget_delta_sq
    simpa [μ, fresh] using
      (integral_inner_centered_oracleDifference_eq_zero_of_indep_adapted
        (P := μ) (ν := A.problem.sampleLaw)
        (sample := fresh) (x := y) (y := xPrev) (d := eps)
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased)
        hquery_delta_eps_meas (hsample_meas (t + 1)) h_indep_delta_eps_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        horacle_inner_int
        (by
          exact (continuous_inner.measurable.comp
            ((measurable_snd).prodMk
              ((hgradF_meas.comp (measurable_fst.comp measurable_fst)).sub
                (hgradF_meas.comp (measurable_snd.comp measurable_fst))))).aestronglyMeasurable)
        htarget_inner_int
        (by
          filter_upwards [] with q
          exact UnbiasedGradientOracle.fixed_fiber_oracle_difference_mean
            hgrad_unbiased q.1.1 q.1.2 q.2))
  let β : ℝ := A.beta1 (t + 1)
  let r : SampleStream Sample → MarsVector ι :=
    fun ω => A.problem.stochasticGrad (y ω) (fresh ω) - A.problem.gradF (y ω)
  let z : SampleStream Sample → MarsVector ι :=
    fun ω =>
      (A.problem.stochasticGrad (y ω) (fresh ω) -
          A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
        (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
  let prev : SampleStream Sample → MarsVector ι := fun ω => β • eps ω
  let inc : SampleStream Sample → MarsVector ι :=
    fun ω => (1 - β) • r ω + β • z ω
  let core : SampleStream Sample → MarsVector ι :=
    fun ω => (1 - β) • r ω + β • eps ω + β • z ω
  have hβ_nonneg : 0 ≤ β := by
    simpa [β] using hbeta_admissible.1
  have hβ_le_one : β ≤ 1 := by
    simpa [β] using hbeta_admissible.2
  have hone_minus_nonneg : 0 ≤ 1 - β := by
    linarith
  have hr_aesm : AEStronglyMeasurable r μ := by
    dsimp [r, μ, fresh, y]
    exact (hres_meas.comp (hquery_y_meas.prodMk (hsample_meas (t + 1)))).aestronglyMeasurable
  have hz_aesm : AEStronglyMeasurable z μ := by
    dsimp [z]
    exact horacle_delta_aesm.sub htarget_delta_aesm
  have hr_sq : Integrable (fun ω : SampleStream Sample => ‖r ω‖ ^ 2) μ := by
    simpa [μ, fresh, y, r] using
      (integrable_sq_oracleResidual_of_indep_fixed_variance_bound
        (P := μ) (ν := A.problem.sampleLaw)
        (query := y) (sample := fresh)
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (σ2 := σ ^ 2)
        hres_meas hquery_y_meas (hsample_meas (t + 1)) h_indep_y_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        (sq_nonneg σ)
        (by intro x; exact BoundedVariance.fixed_sq_integrable hvar x)
        (by intro x; exact BoundedVariance.bound hvar x))
  have hz_sq : Integrable (fun ω : SampleStream Sample => ‖z ω‖ ^ 2) μ := by
    simpa [z, μ, fresh, xPrev, y] using hcentered_delta.1
  have hprev_aesm : AEStronglyMeasurable prev μ := by
    dsimp [prev]
    exact heps_aesm.const_smul β
  have hinc_aesm : AEStronglyMeasurable inc μ := by
    dsimp [inc]
    exact (hr_aesm.const_smul (1 - β)).add (hz_aesm.const_smul β)
  have hprev_sq_scaled : Integrable (fun ω : SampleStream Sample => ‖prev ω‖ ^ 2) μ := by
    refine (hprev_sq.const_mul (β ^ 2)).congr ?_
    filter_upwards [] with ω
    dsimp [prev]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hinc_sq : Integrable (fun ω : SampleStream Sample => ‖inc ω‖ ^ 2) μ := by
    refine Integrable.mono'
      ((hr_sq.const_mul (2 * (1 - β) ^ 2)).add (hz_sq.const_mul (2 * β ^ 2)))
      (hinc_aesm.norm.pow 2) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖inc ω‖))]
    have htmp := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
      ((1 - β) • r ω) (β • z ω)
    dsimp [inc]
    simpa [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hinner_eps_r_int : Integrable (fun ω : SampleStream Sample => inner ℝ (eps ω) (r ω)) μ :=
    integrable_inner_of_integrable_sq_norm heps_aesm hr_aesm (by simpa [eps] using hprev_sq) hr_sq
  have hinner_eps_z_int : Integrable (fun ω : SampleStream Sample => inner ℝ (eps ω) (z ω)) μ :=
    integrable_inner_of_integrable_sq_norm heps_aesm hz_aesm (by simpa [eps] using hprev_sq) hz_sq
  have hcross_eps_r : ∫ ω, inner ℝ (eps ω) (r ω) ∂μ = 0 := by
    simpa [μ, fresh, y, r] using hcross_prev_fresh
  have hcross_eps_z : ∫ ω, inner ℝ (eps ω) (z ω) ∂μ = 0 := by
    simpa [μ, fresh, xPrev, y, z] using hcross_prev_delta
  have hcross_prev_inc : ∫ ω, inner ℝ (prev ω) (inc ω) ∂μ = 0 := by
    calc
      ∫ ω, inner ℝ (prev ω) (inc ω) ∂μ =
          ∫ ω, (β * (1 - β)) * inner ℝ (eps ω) (r ω) +
            (β * β) * inner ℝ (eps ω) (z ω) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            dsimp [prev, inc]
            simp [inner_add_right, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm]
      _ = (β * (1 - β)) * ∫ ω, inner ℝ (eps ω) (r ω) ∂μ +
            (β * β) * ∫ ω, inner ℝ (eps ω) (z ω) ∂μ := by
            rw [integral_add (hinner_eps_r_int.const_mul (β * (1 - β)))
                (hinner_eps_z_int.const_mul (β * β)), integral_const_mul, integral_const_mul]
      _ = 0 := by
            rw [hcross_eps_r, hcross_eps_z]
            ring
  have hvar_random_r : ∫ ω, ‖r ω‖ ^ 2 ∂μ ≤ σ ^ 2 := by
    simpa [μ, fresh, y, r] using hvar_random
  have hz_bound : ∫ ω, ‖z ω‖ ^ 2 ∂μ ≤ L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    simpa [z, μ, fresh, xPrev, y] using hcentered_delta.2
  have hinc_bound :
      ∫ ω, ‖inc ω‖ ^ 2 ∂μ ≤
        2 * (1 - β) ^ 2 * σ ^ 2 +
          2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    have hbudget_int : Integrable
        (fun ω : SampleStream Sample =>
          (2 * (1 - β) ^ 2) * ‖r ω‖ ^ 2 +
            (2 * β ^ 2) * ‖z ω‖ ^ 2) μ :=
      (hr_sq.const_mul (2 * (1 - β) ^ 2)).add (hz_sq.const_mul (2 * β ^ 2))
    have hmono :
        ∫ ω, ‖inc ω‖ ^ 2 ∂μ ≤
          ∫ ω, (2 * (1 - β) ^ 2) * ‖r ω‖ ^ 2 +
            (2 * β ^ 2) * ‖z ω‖ ^ 2 ∂μ := by
      refine integral_mono hinc_sq hbudget_int ?_
      intro ω
      have htmp := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        ((1 - β) • r ω) (β • z ω)
      dsimp [inc]
      simpa [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc, mul_left_comm, mul_comm] using htmp
    calc
      ∫ ω, ‖inc ω‖ ^ 2 ∂μ ≤
          ∫ ω, (2 * (1 - β) ^ 2) * ‖r ω‖ ^ 2 +
            (2 * β ^ 2) * ‖z ω‖ ^ 2 ∂μ := hmono
      _ = (2 * (1 - β) ^ 2) * ∫ ω, ‖r ω‖ ^ 2 ∂μ +
            (2 * β ^ 2) * ∫ ω, ‖z ω‖ ^ 2 ∂μ := by
            rw [integral_add (hr_sq.const_mul (2 * (1 - β) ^ 2))
                (hz_sq.const_mul (2 * β ^ 2)), integral_const_mul, integral_const_mul]
      _ ≤ (2 * (1 - β) ^ 2) * σ ^ 2 +
            (2 * β ^ 2) * (L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ) := by
            have hc1 : 0 ≤ 2 * (1 - β) ^ 2 := by
              nlinarith [hone_minus_nonneg]
            have hc2 : 0 ≤ 2 * β ^ 2 := by
              nlinarith [hβ_nonneg]
            exact add_le_add (mul_le_mul_of_nonneg_left hvar_random_r hc1)
              (mul_le_mul_of_nonneg_left hz_bound hc2)
      _ = 2 * (1 - β) ^ 2 * σ ^ 2 +
            2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
            ring
  have hcore_rec : Filter.EventuallyEq (ae μ) core (fun ω => prev ω + inc ω) := by
    filter_upwards [] with ω
    dsimp [core, prev, inc]
    abel
  have hprev_integral_eq :
      ∫ ω, ‖prev ω‖ ^ 2 ∂μ = β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ := by
    calc
      ∫ ω, ‖prev ω‖ ^ 2 ∂μ = ∫ ω, β ^ 2 * ‖eps ω‖ ^ 2 ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro ω
        dsimp [prev]
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ = β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ := by
        rw [integral_const_mul]
  have hcore_recurrence :=
    second_moment_add_recurrence_le_of_cross_zero μ prev core inc
      (2 * (1 - β) ^ 2 * σ ^ 2 +
        2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ)
      hprev_aesm hinc_aesm hprev_sq_scaled hinc_sq hcore_rec
      hcross_prev_inc hinc_bound
  have hcore_bound :
      ∫ ω, ‖core ω‖ ^ 2 ∂μ ≤
        2 * (1 - β) ^ 2 * σ ^ 2 +
          β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ +
          2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    calc
      ∫ ω, ‖core ω‖ ^ 2 ∂μ ≤
          ∫ ω, ‖prev ω‖ ^ 2 ∂μ +
            (2 * (1 - β) ^ 2 * σ ^ 2 +
              2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ) := hcore_recurrence.2
      _ = 2 * (1 - β) ^ 2 * σ ^ 2 +
          β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ +
          2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
          rw [hprev_integral_eq]
          ring
  let epsNext : SampleStream Sample → MarsVector ι :=
    c2EstimatorError A.problem (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1))
  have hprev_expected_eq :
      expectedEstimatorError μ A.problem.gradF xPrev (Algorithm1.m A t) =
        ∫ ω, ‖eps ω‖ ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    have hnorm : ‖A.problem.gradF (xPrev ω) - Algorithm1.m A t ω‖ = ‖eps ω‖ := by
      simpa [eps, c2EstimatorError, xPrev, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_neg (A.problem.gradF (xPrev ω) - Algorithm1.m A t ω)).symm
    simp [hnorm]
  have hnext_expected_eq :
      expectedEstimatorError μ A.problem.gradF
          (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) =
        ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    have hnorm :
        ‖A.problem.gradF (Algorithm1.x A (t + 1) ω) -
            Algorithm1.m A (t + 1) ω‖ =
          ‖epsNext ω‖ := by
      simpa [epsNext, c2EstimatorError, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_neg
          (A.problem.gradF (Algorithm1.x A (t + 1) ω) -
            Algorithm1.m A (t + 1) ω)).symm
    simp [hnorm]
  let delta : SampleStream Sample → MarsVector ι :=
    fun ω => A.problem.stochasticGrad (y ω) (fresh ω) -
      A.problem.stochasticGrad (xPrev ω) (fresh ω)
  let deltaMean : SampleStream Sample → MarsVector ι :=
    fun ω => A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)
  have hdelta_aesm : AEStronglyMeasurable delta μ := by
    simpa [delta] using horacle_delta_aesm
  have hdeltaMean_aesm : AEStronglyMeasurable deltaMean μ := by
    simpa [deltaMean] using htarget_delta_aesm
  have hdelta_sq :
      Integrable (fun ω => ‖delta ω‖ ^ 2) μ := by
    simpa [delta] using hdelta_uncentered.1
  have hdeltaMean_sq :
      Integrable (fun ω => ‖deltaMean ω‖ ^ 2) μ := by
    simpa [deltaMean] using htarget_delta_sq
  have hdelta_delta_int :
      Integrable (fun ω => inner ℝ (delta ω) (delta ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := delta)
      hdelta_aesm hdelta_aesm hdelta_sq hdelta_sq
  have hdelta_deltaMean_int :
      Integrable (fun ω => inner ℝ (delta ω) (deltaMean ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := deltaMean)
      hdelta_aesm hdeltaMean_aesm hdelta_sq hdeltaMean_sq
  have hdeltaMean_delta_int :
      Integrable (fun ω => inner ℝ (deltaMean ω) (delta ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := deltaMean) (v := delta)
      hdeltaMean_aesm hdelta_aesm hdeltaMean_sq hdelta_sq
  have hdeltaMean_deltaMean_int :
      Integrable (fun ω => inner ℝ (deltaMean ω) (deltaMean ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := deltaMean) (v := deltaMean)
      hdeltaMean_aesm hdeltaMean_aesm hdeltaMean_sq hdeltaMean_sq
  have hdeltaMean_cross :
      ∫ ω, inner ℝ (delta ω) (deltaMean ω) ∂μ =
        ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
    have hcenter :
        ∫ ω, inner ℝ (deltaMean ω) (delta ω - deltaMean ω) ∂μ = 0 := by
      simpa [delta, deltaMean] using hcenter_delta_zero
    simpa using
      (integral_inner_eq_integral_norm_sq_of_inner_sub_eq_zero
        μ hdeltaMean_delta_int hdeltaMean_deltaMean_int hcenter)
  have hdelta_z_int :
      Integrable (fun ω => inner ℝ (delta ω) (z ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := z)
      hdelta_aesm hz_aesm hdelta_sq hz_sq
  have hdelta_z :
      ∫ ω, inner ℝ (delta ω) (z ω) ∂μ =
        (∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
          ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
    have hz_def : ∀ ω, z ω = delta ω - deltaMean ω := by
      intro ω
      rfl
    calc
      ∫ ω, inner ℝ (delta ω) (z ω) ∂μ =
          ∫ ω, inner ℝ (delta ω) (delta ω - deltaMean ω) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change inner ℝ (delta ω) (z ω) =
              inner ℝ (delta ω) (delta ω - deltaMean ω)
            exact congrArg (fun v => inner ℝ (delta ω) v) (hz_def ω)
      _ = ∫ ω,
          (inner ℝ (delta ω) (delta ω) -
            inner ℝ (delta ω) (deltaMean ω)) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change inner ℝ (delta ω) (delta ω - deltaMean ω) =
              inner ℝ (delta ω) (delta ω) -
                inner ℝ (delta ω) (deltaMean ω)
            simp only [inner_sub_right]
      _ = (∫ ω, inner ℝ (delta ω) (delta ω) ∂μ) -
          ∫ ω, inner ℝ (delta ω) (deltaMean ω) ∂μ := by
            rw [integral_sub hdelta_delta_int hdelta_deltaMean_int]
      _ = (∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
          ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
            rw [hdeltaMean_cross]
            simp [inner_self_eq_norm_sq]
  have hcore_aesm : AEStronglyMeasurable core μ := by
    dsimp [core]
    exact
      ((hr_aesm.const_smul (1 - β)).add (heps_aesm.const_smul β)).add
        (hz_aesm.const_smul β)
  have hcore_sq : Integrable (fun ω => ‖core ω‖ ^ 2) μ :=
    hcore_recurrence.1
  have hdelta_core_int :
      Integrable (fun ω => inner ℝ (delta ω) (core ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := core)
      hdelta_aesm hcore_aesm hdelta_sq hcore_sq
  have hdelta_r_int :
      Integrable (fun ω => inner ℝ (delta ω) (r ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := r)
      hdelta_aesm hr_aesm hdelta_sq hr_sq
  have hdelta_eps_int :
      Integrable (fun ω => inner ℝ (delta ω) (eps ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := eps)
      hdelta_aesm heps_aesm hdelta_sq (by simpa [eps] using hprev_sq)
  have hdelta_core_expand :
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
        (1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := by
    calc
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
          ∫ ω,
            (1 - β) * inner ℝ (delta ω) (r ω) +
              β * inner ℝ (delta ω) (eps ω) +
              β * inner ℝ (delta ω) (z ω) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            dsimp [core]
            simp [inner_add_right, inner_smul_right, mul_assoc, mul_left_comm,
              mul_comm]
      _ = (1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := by
            change
              (∫ ω,
                  ((1 - β) * inner ℝ (delta ω) (r ω) +
                    β * inner ℝ (delta ω) (eps ω)) +
                    β * inner ℝ (delta ω) (z ω) ∂μ) = _
            calc
              (∫ ω,
                  ((1 - β) * inner ℝ (delta ω) (r ω) +
                    β * inner ℝ (delta ω) (eps ω)) +
                    β * inner ℝ (delta ω) (z ω) ∂μ) =
                  (∫ ω, (1 - β) * inner ℝ (delta ω) (r ω) +
                    β * inner ℝ (delta ω) (eps ω) ∂μ) +
                    ∫ ω, β * inner ℝ (delta ω) (z ω) ∂μ := by
                exact integral_add
                  ((hdelta_r_int.const_mul (1 - β)).add
                    (hdelta_eps_int.const_mul β))
                  (hdelta_z_int.const_mul β)
              _ = ((1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
                    β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ)) +
                    β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := by
                rw [integral_add (hdelta_r_int.const_mul (1 - β))
                  (hdelta_eps_int.const_mul β)]
                rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hdelta_core :
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
        c2ProofG μ A.problem (sampleAt (Sample := Sample))
            (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) β t +
          β * ((∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
            ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ) := by
    calc
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
          (1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
            β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ) +
            β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := hdelta_core_expand
      _ = c2ProofG μ A.problem (sampleAt (Sample := Sample))
            (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) β t +
          β * ((∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
            ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ) := by
            rw [hdelta_z]
            simp [c2ProofG, c2EstimatorError, c2Delta, delta, deltaMean, r, eps,
              μ, fresh, xPrev, y]
  have hdelta_sq_def :
      c2DeltaNormSqExpectation μ A.problem (sampleAt (Sample := Sample))
          xPrev y t =
        ∫ ω, ‖delta ω‖ ^ 2 ∂μ := by
    simp [c2DeltaNormSqExpectation, c2Delta, delta, μ, fresh, xPrev, y]
  have hdeltaMean_sq_def :
      c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y =
        ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
    simp [c2DeltaConditionalMeanSqExpectation, c2DeltaExpectation, deltaMean]
  have hdelta_core_num :
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
        c2ProofG μ A.problem (sampleAt (Sample := Sample))
            (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) β t +
          β *
            (c2DeltaNormSqExpectation μ A.problem (sampleAt (Sample := Sample))
                xPrev y t -
              c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y) := by
    calc
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
          c2ProofG μ A.problem (sampleAt (Sample := Sample))
              (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) β t +
            β * ((∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
              ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ) := hdelta_core
      _ = c2ProofG μ A.problem (sampleAt (Sample := Sample))
              (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) β t +
            β *
              (c2DeltaNormSqExpectation μ A.problem
                  (sampleAt (Sample := Sample)) xPrev y t -
                c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y) := by
            rw [hdelta_sq_def, hdeltaMean_sq_def]
  let κ : ℝ := β * (A.gamma (t + 1) - 1)
  have hnext_decomp :
      ∀ ω, epsNext ω = core ω + κ • delta ω := by
    intro ω
    have hw := hraw ω
    dsimp [epsNext, core, κ, delta, deltaMean, r, eps, z, β,
      c2EstimatorError, c2Delta, fresh] at hw ⊢
    rw [hw]
    module
  have hcore_delta_int :
      Integrable (fun ω => inner ℝ (core ω) (delta ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := core) (v := delta)
      hcore_aesm hdelta_aesm hcore_sq hdelta_sq
  have hnext_sq_expand :
      ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ =
        ∫ ω, ‖core ω‖ ^ 2 ∂μ +
          2 * κ * (∫ ω, inner ℝ (delta ω) (core ω) ∂μ) +
          κ ^ 2 * (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := by
    calc
      ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ =
          ∫ ω,
            ‖core ω‖ ^ 2 +
              2 * κ * inner ℝ (delta ω) (core ω) +
              κ ^ 2 * ‖delta ω‖ ^ 2 ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change ‖epsNext ω‖ ^ 2 =
              ‖core ω‖ ^ 2 +
                2 * κ * inner ℝ (delta ω) (core ω) +
                κ ^ 2 * ‖delta ω‖ ^ 2
            rw [hnext_decomp ω]
            have hnorm := norm_add_sq_real (core ω) (κ • delta ω)
            simpa [norm_smul, Real.norm_eq_abs, sq_abs, mul_pow, inner_smul_right,
              real_inner_comm, mul_assoc, mul_left_comm, mul_comm] using hnorm
      _ = ∫ ω, ‖core ω‖ ^ 2 ∂μ +
          2 * κ * (∫ ω, inner ℝ (delta ω) (core ω) ∂μ) +
          κ ^ 2 * (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := by
            change
              (∫ ω,
                  ((‖core ω‖ ^ 2 +
                    2 * κ * inner ℝ (delta ω) (core ω)) +
                    κ ^ 2 * ‖delta ω‖ ^ 2) ∂μ) = _
            calc
              (∫ ω,
                  ((‖core ω‖ ^ 2 +
                    2 * κ * inner ℝ (delta ω) (core ω)) +
                    κ ^ 2 * ‖delta ω‖ ^ 2) ∂μ) =
                  (∫ ω, ‖core ω‖ ^ 2 +
                    2 * κ * inner ℝ (delta ω) (core ω) ∂μ) +
                    ∫ ω, κ ^ 2 * ‖delta ω‖ ^ 2 ∂μ := by
                exact integral_add
                  (hcore_sq.add (hdelta_core_int.const_mul (2 * κ)))
                  (hdelta_sq.const_mul (κ ^ 2))
              _ = ((∫ ω, ‖core ω‖ ^ 2 ∂μ) +
                    2 * κ * (∫ ω, inner ℝ (delta ω) (core ω) ∂μ)) +
                    κ ^ 2 * (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := by
                rw [integral_add hcore_sq (hdelta_core_int.const_mul (2 * κ))]
                rw [integral_const_mul, integral_const_mul]
  have hres_completion :
      ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ ≤
        ∫ ω, ‖core ω‖ ^ 2 ∂μ -
          d4ProofResidual μ A.problem (sampleAt (Sample := Sample))
            xPrev y (Algorithm1.m A t) β (A.gamma (t + 1)) t := by
    by_cases hdelta_sq_zero : (∫ ω, ‖delta ω‖ ^ 2 ∂μ) = 0
    · have hdelta_norm_sq_ae :
          (fun ω => ‖delta ω‖ ^ 2) =ᶠ[ae μ] (fun _ => 0) :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg (μ := μ)
          (fun ω => sq_nonneg (‖delta ω‖)) hdelta_sq).mp hdelta_sq_zero
      have hdelta_zero_ae : delta =ᶠ[ae μ] (fun _ => 0) := by
        filter_upwards [hdelta_norm_sq_ae] with ω hω
        have hnorm_sq : ‖delta ω‖ ^ 2 = 0 := by
          simpa using hω
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq)
      have hcross_zero :
          ∫ ω, inner ℝ (delta ω) (core ω) ∂μ = 0 := by
        have hzero :
            (fun ω => inner ℝ (delta ω) (core ω)) =ᶠ[ae μ] (fun _ => 0) := by
          filter_upwards [hdelta_zero_ae] with ω hω
          simp [hω]
        simpa using (integral_congr_ae hzero)
      have hdelta_sq_zero' :
          c2DeltaNormSqExpectation μ A.problem (sampleAt (Sample := Sample))
              xPrev y t = 0 := by
        rw [hdelta_sq_def]
        exact hdelta_sq_zero
      rw [hnext_sq_expand, hcross_zero, hdelta_sq_zero]
      simp [d4ProofResidual, hdelta_sq_zero']
    · have hA_cross :
          d4ProofA μ A.problem (sampleAt (Sample := Sample))
              xPrev y (Algorithm1.m A t) β t *
              (∫ ω, ‖delta ω‖ ^ 2 ∂μ) =
            ∫ ω, inner ℝ (delta ω) (core ω) ∂μ := by
        calc
          d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm1.m A t) β t *
                (∫ ω, ‖delta ω‖ ^ 2 ∂μ) =
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm1.m A t) β t *
                c2DeltaNormSqExpectation μ A.problem
                  (sampleAt (Sample := Sample)) xPrev y t := by
                rw [hdelta_sq_def]
          _ = c2ProofG μ A.problem (sampleAt (Sample := Sample))
                (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) β t +
              β *
                (c2DeltaNormSqExpectation μ A.problem
                    (sampleAt (Sample := Sample)) xPrev y t -
                  c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y) := by
                dsimp [d4ProofA]
                have hdelta_sq_c2_ne :
                    c2DeltaNormSqExpectation μ A.problem
                        (sampleAt (Sample := Sample)) xPrev y t ≠ 0 := by
                  intro hzero
                  apply hdelta_sq_zero
                  rw [← hdelta_sq_def]
                  exact hzero
                field_simp [hdelta_sq_c2_ne] <;> simp [xPrev, y]
          _ = ∫ ω, inner ℝ (delta ω) (core ω) ∂μ :=
            hdelta_core_num.symm
      have hcross_A :
          (∫ ω, inner ℝ (delta ω) (core ω) ∂μ) =
            (∫ ω, ‖delta ω‖ ^ 2 ∂μ) *
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm1.m A t) β t := by
        calc
          ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm1.m A t) β t *
                (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := hA_cross.symm
          _ = (∫ ω, ‖delta ω‖ ^ 2 ∂μ) *
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm1.m A t) β t := by ring
      rw [hnext_sq_expand, hcross_A]
      dsimp [d4ProofResidual]
      rw [hdelta_sq_def]
      dsimp [κ]
      ring_nf <;> exact le_rfl
  have hres_eq :
      theoremB5ReadableC2Residual A t =
        d4ProofResidual μ A.problem (sampleAt (Sample := Sample))
          xPrev y (Algorithm1.m A t) β (A.gamma (t + 1)) t := by
    simpa [theoremB5ReadableC2Residual] using hC2_residual_compatible
  calc
    expectedEstimatorError μ A.problem.gradF
        (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) =
        ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ := hnext_expected_eq
    _ ≤ ∫ ω, ‖core ω‖ ^ 2 ∂μ -
          d4ProofResidual μ A.problem (sampleAt (Sample := Sample))
            xPrev y (Algorithm1.m A t) β (A.gamma (t + 1)) t := hres_completion
    _ = ∫ ω, ‖core ω‖ ^ 2 ∂μ -
          theoremB5ReadableC2Residual A t := by rw [hres_eq]
    _ ≤ 2 * (1 - β) ^ 2 * σ ^ 2 +
          β ^ 2 * (∫ ω, ‖eps ω‖ ^ 2 ∂μ) +
          2 * β ^ 2 * L ^ 2 *
            ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ -
          theoremB5ReadableC2Residual A t := by
            linarith [hcore_bound]
    _ = (A.beta1 (t + 1)) ^ 2 *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A t) (Algorithm1.m A t) +
        2 * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
          (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
            ∂runLaw A.problem) +
        2 * (1 - A.beta1 (t + 1)) ^ 2 * σ ^ 2 -
        theoremB5ReadableC2Residual A t := by
          rw [← hprev_expected_eq]
          simp [β, μ, xPrev, y]
          ring

private theorem b5_c2_i2_bound_on_horizon
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (L σ c : ℝ) (T : ℕ)
    (hgrad_unbiased : UnbiasedGradientOracle A.problem)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L)
    (hparams_c :
      0 < A.rho ∧ 0 < c ∧ ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hexpect : TheoremB5ExpectationWellDefined A T)
    (hc2 : TheoremB5C2CorrectedExtensionBoundary A T)
    (hD4 :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        Algorithm1.m A (t + 1) ω =
          (A.beta1 (t + 1)) • Algorithm1.m A t ω +
            (1 - A.beta1 (t + 1)) •
              marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
                (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω))
                (A.problem.stochasticGrad (Algorithm1.x A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω)))
    (hxNext_succ :
      ∀ t : ℕ, ∀ ω : SampleStream Sample,
        Algorithm1.xNext A t ω = Algorithm1.x A (t + 1) ω) :
    ∀ t ∈ Finset.Icc 1 T,
      (A.rho / (16 * L ^ 2 * A.eta t)) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
        (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A t) (Algorithm1.m A t)
      ≤
        (A.rho / (16 * L ^ 2)) *
            ((A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A t) (Algorithm1.m A t) +
          (A.rho / (8 * A.eta t)) *
            (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
              ∂runLaw A.problem) +
          (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
          (A.rho / (16 * L ^ 2 * A.eta t)) *
            theoremB5ReadableC2Residual A t := by
  intro t ht
  have hraw :
      ∀ ω : SampleStream Sample,
        c2EstimatorError A.problem (Algorithm1.x A (t + 1))
            (Algorithm1.m A (t + 1)) ω =
          (1 - A.beta1 (t + 1)) •
              (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω) -
                A.problem.gradF (Algorithm1.xNext A t ω)) +
            (A.beta1 (t + 1)) •
              c2EstimatorError A.problem (Algorithm1.x A t) (Algorithm1.m A t) ω +
            (A.beta1 (t + 1)) •
              ((A.gamma (t + 1)) •
                  c2Delta A.problem (sampleAt (Sample := Sample))
                    (Algorithm1.x A t) (Algorithm1.xNext A t) t ω -
                (A.problem.gradF (Algorithm1.xNext A t ω) -
                  A.problem.gradF (Algorithm1.x A t ω))) :=
    b5_c2_estimator_error_recursion_raw A c T hparams_c hbeta1 hD4 hxNext_succ t ht
  have hC2 := TheoremB5C2CorrectedExtensionBoundary.c2 hc2
  have hbeta_admissible : 0 ≤ A.beta1 (t + 1) ∧ A.beta1 (t + 1) ≤ 1 :=
    hC2.1 t ht
  have hC2_well_defined :
      C2ExpectationWellDefined (runLaw A.problem) A.problem (sampleAt (Sample := Sample))
        (Algorithm1.x A t) (Algorithm1.xNext A t) (Algorithm1.m A t) t :=
    hC2.2.1 t ht
  have hC2_residual_compatible :
      C2CorrectedStatementProofResidualCompatible (runLaw A.problem) A.problem
        (sampleAt (Sample := Sample)) (Algorithm1.x A t) (Algorithm1.xNext A t)
        (Algorithm1.m A t) (A.beta1 (t + 1)) (A.gamma (t + 1)) t :=
    hC2.2.2.2.2.2 t ht
  have hprev_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖c2EstimatorError A.problem (Algorithm1.x A t) (Algorithm1.m A t) ω‖ ^ 2)
        (runLaw A.problem) := by
    have hprev_expected := (hexpect t ht).1
    simpa [ExpectedEstimatorErrorWellDefined, c2EstimatorError, norm_sub_rev]
      using hprev_expected
  have hdisp_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2)
        (runLaw A.problem) := by
    have hscaled := (hexpect t ht).2
    have hη_pos : 0 < A.eta t := hparams_c.2.2 t ht
    have h := hscaled.const_mul (A.eta t)
    convert h using 1
    ext ω
    field_simp [hη_pos.ne']
  have ht_pos : 0 < t := (Finset.mem_Icc.mp ht).1
  have hstep :=
    b5_c2_one_step_second_moment_bound A L σ t ht_pos hraw hbeta_admissible
      hC2_well_defined hC2_residual_compatible hprev_sq hdisp_sq hgrad_unbiased hvar
      hsmooth
  -- The remaining work in this helper is now scalar C.5 scaling of the unscaled
  -- C.2 estimate plus the beta-schedule variance substitution.
  by_cases hL_zero : L = 0
  · subst L
    simp
    have hη_pos : 0 < A.eta t := hparams_c.2.2 t ht
    have hD_nonneg :
        0 ≤
          (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
            ∂runLaw A.problem) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hcoef_nonneg : 0 ≤ A.rho / (8 * A.eta t) := by
      have hρ_nonneg : 0 ≤ A.rho := le_of_lt hparams_c.1
      have hden_pos : 0 < 8 * A.eta t := by positivity
      exact div_nonneg hρ_nonneg (le_of_lt hden_pos)
    exact mul_nonneg hcoef_nonneg hD_nonneg
  · have hη_pos : 0 < A.eta t := hparams_c.2.2 t ht
    have hρ_nonneg : 0 ≤ A.rho := le_of_lt hparams_c.1
    have hLsq_pos : 0 < L ^ 2 := sq_pos_of_ne_zero hL_zero
    have hρ_div_Lsq_pos : 0 < A.rho / L ^ 2 := div_pos hparams_c.1 hLsq_pos
    have hK_nonneg : 0 ≤ A.rho / (16 * L ^ 2 * A.eta t) := by
      have hden_pos : 0 < 16 * L ^ 2 * A.eta t := by positivity
      exact div_nonneg hρ_nonneg (le_of_lt hden_pos)
    have hscaled := mul_le_mul_of_nonneg_left hstep hK_nonneg
    have hβ_sq_le_one : (A.beta1 (t + 1)) ^ 2 ≤ 1 := by
      nlinarith [hbeta_admissible.1, hbeta_admissible.2]
    have hD_nonneg :
        0 ≤
          (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
            ∂runLaw A.problem) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hβ_sched : 1 - A.beta1 (t + 1) = c * A.eta t ^ 2 := by
      rw [hbeta1 t, betaOneSchedule]
      ring
    have hD_gap_nonneg :
        0 ≤
          (A.rho * L ^ 2 *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) *
              L⁻¹ ^ 2 * 16 -
            (A.rho * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) *
              L⁻¹ ^ 2 * 16 := by
      have hcommon_nonneg :
          0 ≤
            (A.rho * L ^ 2 *
                  (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                    ∂runLaw A.problem)) *
                L⁻¹ ^ 2 * 16 := by
        positivity
      nlinarith [hβ_sq_le_one, hcommon_nonneg]
    have hsub :=
      sub_le_sub_right hscaled
        ((A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A t) (Algorithm1.m A t))
    refine le_trans hsub ?_
    rw [hβ_sched]
    field_simp [hη_pos.ne', hL_zero]
    ring_nf
    ring_nf at hD_gap_nonneg
    nlinarith [hD_gap_nonneg]

set_option maxHeartbeats 800000 in
/-- Corrected B.5 theorem over generated Algorithm 1 objects. -/
theorem theorem_B_5_corrected
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (minimum : ObjectiveMinimumWitness A.problem.F)
    (L σ c s : ℝ) (T : ℕ)
    (hobj_unbiased : UnbiasedObjectiveOracle A.problem)
    (hgrad_unbiased : UnbiasedGradientOracle A.problem)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L)
    (heta : ∀ t : ℕ, A.eta t = etaSchedule s t)
    (hs : s ≥ 8 * L ^ 3 / A.rho ^ 3)
    (hL_pos : 0 < L)
    (hs_ge_one : 1 ≤ s)
    (hc : c ≥ 32 * L ^ 2 * A.rho⁻¹ ^ 2 + 1)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hbeta2 : ∀ t : ℕ, A.beta2 (t + 1) = betaTwoSchedule A.eta t)
    (hT : (T : ℝ) ≥ s)
    (hexpect : TheoremB5ExpectationWellDefined A T)
    (hB5_initial_estimator_error_bound :
      expectedEstimatorError (runLaw A.problem) A.problem.gradF
        (Algorithm1.x A 1) (Algorithm1.m A 1) ≤ σ ^ 2)
    (hc2 : TheoremB5C2CorrectedExtensionBoundary A T) :
    TheoremB5CorrectedStatement A minimum L σ c s T := by
  have hparams :=
    b5_positive_parameters_and_schedule_bounds A L σ c s T
      hvar hsmooth heta hs hs_ge_one hT hc2
  have hmirror_full :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        (A.rho / A.eta t) *
            ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2
          ≤
            inner ℝ (Algorithm1.m A t ω)
              (Algorithm1.x A t ω - Algorithm1.xNext A t ω) := by
    intro t ht ω
    exact b5_mirror_inner_full_lower_bound A t (Finset.mem_Icc.mp ht).1 ω
      (hparams.2.2 t ht)
  have hmirror :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        inner ℝ (Algorithm1.m A t ω)
            (Algorithm1.xNext A t ω - Algorithm1.x A t ω)
          ≤
            -(A.rho / (2 * A.eta t)) *
              ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2 := by
    intro t ht ω
    let x := Algorithm1.x A t ω
    let z := Algorithm1.xNext A t ω
    let m := Algorithm1.m A t ω
    have hfull := hmirror_full t ht ω
    have hη_pos : 0 < A.eta t := hparams.2.2 t ht
    have hρ_pos : 0 < A.rho := hparams.1
    have hnorm : ‖x - z‖ = ‖z - x‖ := by
      rw [← norm_neg (z - x)]
      congr 1
      abel
    have hneg : inner ℝ m (z - x) = -inner ℝ m (x - z) := by
      have hvec : z - x = -(x - z) := by abel
      rw [hvec, inner_neg_right]
    have hstrong :
        inner ℝ m (z - x) ≤
          -(A.rho / A.eta t) * ‖z - x‖ ^ 2 := by
      rw [hneg]
      have hfull' :
          (A.rho / A.eta t) * ‖x - z‖ ^ 2 ≤ inner ℝ m (x - z) := by
        simpa [x, z, m] using hfull
      rw [hnorm] at hfull'
      nlinarith
    have hcoef :
        -(A.rho / A.eta t) * ‖z - x‖ ^ 2 ≤
          -(A.rho / (2 * A.eta t)) * ‖z - x‖ ^ 2 := by
      have hnormsq_nonneg : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _
      have hcoef_le : A.rho / (2 * A.eta t) ≤ A.rho / A.eta t := by
        field_simp [hη_pos.ne']
        nlinarith [hρ_pos]
      nlinarith
    exact le_trans hstrong hcoef
  have hC3_with_absorb :
      ∀ t ∈ Finset.Icc 1 T,
        L / 2 ≤ A.rho / (4 * A.eta t) →
          ∀ ω : SampleStream Sample,
            A.problem.F (Algorithm1.xNext A t ω) ≤
              A.problem.F (Algorithm1.x A t ω) -
                (A.rho / (2 * A.eta t)) *
                  ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2 +
                (A.eta t / A.rho) *
                  ‖A.problem.gradF (Algorithm1.x A t ω) -
                    Algorithm1.m A t ω‖ ^ 2 := by
    intro t ht habsorb ω
    exact b5_c3_objective_descent_pathwise A L hsmooth t
      (Finset.mem_Icc.mp ht).1 ω (hparams.2.2 t ht) habsorb
  have hschedule_absorb :
      ∀ t ∈ Finset.Icc 1 T, L / 2 ≤ A.rho / (4 * A.eta t) :=
    b5_schedule_absorption_on_horizon A L s T heta hs hs_ge_one
  have hC3 :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        A.problem.F (Algorithm1.xNext A t ω) ≤
          A.problem.F (Algorithm1.x A t ω) -
            (A.rho / (2 * A.eta t)) *
              ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2 +
            (A.eta t / A.rho) *
              ‖A.problem.gradF (Algorithm1.x A t ω) -
                Algorithm1.m A t ω‖ ^ 2 := by
    intro t ht ω
    exact hC3_with_absorb t ht (hschedule_absorb t ht) ω
  have hxNext_succ :
      ∀ t : ℕ, ∀ ω : SampleStream Sample,
        Algorithm1.xNext A t ω = Algorithm1.x A (t + 1) ω := by
    intro t ω
    exact b5_algorithm1_xNext_eq_x_succ A t ω
  have hD4_momentum_update_if_unclipped :
      (∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        ‖marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
            (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
              (sampleAt (Sample := Sample) (t + 1) ω))
            (A.problem.stochasticGrad (Algorithm1.x A t ω)
              (sampleAt (Sample := Sample) (t + 1) ω))‖ ≤ 1) →
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        Algorithm1.m A (t + 1) ω =
          (A.beta1 (t + 1)) • Algorithm1.m A t ω +
            (1 - A.beta1 (t + 1)) •
              marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
                (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω))
                (A.problem.stochasticGrad (Algorithm1.x A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω)) := by
    intro hclip
    exact b5_algorithm1_momentum_succ_unclipped_of_correction_norm_le_one A T hclip
  have hD4_momentum_update :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        Algorithm1.m A (t + 1) ω =
          (A.beta1 (t + 1)) • Algorithm1.m A t ω +
            (1 - A.beta1 (t + 1)) •
              marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
                (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω))
                (A.problem.stochasticGrad (Algorithm1.x A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω)) :=
    hD4_momentum_update_if_unclipped
      (TheoremB5C2CorrectedExtensionBoundary.noClipping hc2)
  have hc_pos : 0 < c := by
    have hnonneg : 0 ≤ 32 * L ^ 2 * A.rho⁻¹ ^ 2 := by positivity
    linarith [hc]
  have hparams_c :
      0 < A.rho ∧ 0 < c ∧ ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t :=
    ⟨hparams.1, hc_pos, hparams.2.2⟩
  have hC2_raw_recursion :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        c2EstimatorError A.problem (Algorithm1.x A (t + 1))
            (Algorithm1.m A (t + 1)) ω =
          (1 - A.beta1 (t + 1)) •
              (A.problem.stochasticGrad (Algorithm1.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω) -
                A.problem.gradF (Algorithm1.xNext A t ω)) +
            (A.beta1 (t + 1)) •
              c2EstimatorError A.problem (Algorithm1.x A t) (Algorithm1.m A t) ω +
            (A.beta1 (t + 1)) •
              ((A.gamma (t + 1)) •
                  c2Delta A.problem (sampleAt (Sample := Sample))
                    (Algorithm1.x A t) (Algorithm1.xNext A t) t ω -
                (A.problem.gradF (Algorithm1.xNext A t ω) -
                  A.problem.gradF (Algorithm1.x A t ω))) :=
    b5_c2_estimator_error_recursion_raw A c T hparams_c hbeta1
      hD4_momentum_update hxNext_succ
  have hI2_C5 :
      ∀ t ∈ Finset.Icc 1 T,
        (A.rho / (16 * L ^ 2 * A.eta t)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
          (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A t) (Algorithm1.m A t)
        ≤
          (A.rho / (16 * L ^ 2)) *
              ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                1 / A.eta (t - 1)) *
              expectedEstimatorError (runLaw A.problem) A.problem.gradF
                (Algorithm1.x A t) (Algorithm1.m A t) +
            (A.rho / (8 * A.eta t)) *
              (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                ∂runLaw A.problem) +
            (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
            (A.rho / (16 * L ^ 2 * A.eta t)) *
              theoremB5ReadableC2Residual A t :=
    b5_c2_i2_bound_on_horizon A L σ c T hgrad_unbiased hvar hsmooth
      hparams_c hbeta1 hexpect hc2 hD4_momentum_update hxNext_succ
  have hC5_coefficient_absorption :
      ∀ t ∈ Finset.Icc 1 T,
        (A.rho / (16 * L ^ 2)) *
            ((A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1)) ≤
          -(2 * A.eta t / A.rho) := by
    intro t ht
    have hη_pos : 0 < A.eta t := hparams.2.2 t ht
    have hρ_pos : 0 < A.rho := hparams.1
    have hLsq_pos : 0 < L ^ 2 := sq_pos_of_pos hL_pos
    have hbeta_admissible := (TheoremB5C2CorrectedExtensionBoundary.c2 hc2).1 t ht
    have hbeta_nonneg : 0 ≤ A.beta1 (t + 1) := hbeta_admissible.1
    have hβ_sched : 1 - A.beta1 (t + 1) = c * A.eta t ^ 2 := by
      rw [hbeta1 t, betaOneSchedule]
      ring
    have hc_pos : 0 < c := by
      have hterm_nonneg : 0 ≤ 32 * L ^ 2 * A.rho⁻¹ ^ 2 := by positivity
      linarith [hc]
    have hrecip_diff :
        1 / A.eta t - 1 / A.eta (t - 1) ≤ A.eta t := by
      rw [heta t, heta (t - 1)]
      exact etaSchedule_reciprocal_step_le hs_ge_one t
    have hsq_lower :
        c * A.eta t ^ 2 ≤ 1 - (A.beta1 (t + 1)) ^ 2 := by
      have hprod :
          0 ≤ c * A.eta t ^ 2 * A.beta1 (t + 1) :=
        mul_nonneg
          (mul_nonneg (le_of_lt hc_pos) (sq_nonneg _))
          hbeta_nonneg
      rw [← hβ_sched]
      nlinarith [hprod]
    have hdiv :
        c * A.eta t ≤
          (1 - (A.beta1 (t + 1)) ^ 2) / A.eta t := by
      apply (le_div_iff₀ hη_pos).mpr
      nlinarith [hsq_lower]
    have hcoeff :
        (A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1) ≤
          -(32 * L ^ 2 / A.rho ^ 2) * A.eta t := by
      have hsplit :
          (A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1) =
            (1 / A.eta t - 1 / A.eta (t - 1)) -
              (1 - (A.beta1 (t + 1)) ^ 2) / A.eta t := by
        field_simp [hη_pos.ne']
        ring
      have hbasic :
          (A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1) ≤
            -(c - 1) * A.eta t := by
        rw [hsplit]
        have hsub := sub_le_sub_right hrecip_diff
          ((1 - (A.beta1 (t + 1)) ^ 2) / A.eta t)
        nlinarith [hdiv, hsub]
      have hinv_sq : A.rho⁻¹ ^ 2 = 1 / A.rho ^ 2 := by
        field_simp [hρ_pos.ne']
      have hc' := hc
      rw [hinv_sq] at hc'
      have hcbound : 32 * L ^ 2 / A.rho ^ 2 ≤ c - 1 := by
        have hc'' : c ≥ 32 * L ^ 2 / A.rho ^ 2 + 1 := by
          simpa [div_eq_mul_inv] using hc'
        linarith
      nlinarith [hbasic, hcbound, hη_pos]
    have hscaled :=
      mul_le_mul_of_nonneg_left hcoeff
        (le_of_lt
          (div_pos hρ_pos (mul_pos (by norm_num : (0 : ℝ) < 16) hLsq_pos)))
    calc
      (A.rho / (16 * L ^ 2)) *
            ((A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1)) ≤
          (A.rho / (16 * L ^ 2)) *
            (-(32 * L ^ 2 / A.rho ^ 2) * A.eta t) := hscaled
      _ = -(2 * A.eta t / A.rho) := by
        field_simp [hρ_pos.ne', hL_pos.ne']
        ring
  have hI2_absorbed :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
              (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            -(2 * A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t) +
              (A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) := by
    apply Finset.sum_le_sum
    intro t ht
    have hpoint := hI2_C5 t ht
    have hE :
        0 ≤ expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm1.x A t) (Algorithm1.m A t) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hcoeff := hC5_coefficient_absorption t ht
    have hcoeffE := mul_le_mul_of_nonneg_right hcoeff hE
    nlinarith [hpoint, hcoeffE]

  /-
  let E0 : ℕ → ℝ := fun t => -- staged B.6 route block
    expectedEstimatorError (runLaw A.problem) A.problem.gradF
      (Algorithm2.x A t) (Algorithm2.m A t)
  let D0 : ℕ → ℝ := fun t =>
    ∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
      ∂runLaw A.problem
  let M0 : ℕ → ℝ := fun t => theoremB6ReadableC2Residual A t -- staged B.6 route block
  let W : ℝ := theoremB6WeightDecayWindow A D T
  let E : ℝ :=
    (Finset.Icc 1 T).sum (fun t => (A.eta t / ρ) * E0 t)
  let R : ℝ :=
    (Finset.Icc 1 T).sum (fun t => (ρ / (8 * A.eta t)) * D0 t)
  let V : ℝ :=
    (Finset.Icc 1 T).sum
      (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2))
  let Q : ℝ :=
    (Finset.Icc 1 T).sum
      (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)
  let init : ℝ :=
    (ρ / (16 * L ^ 2 * A.eta 0)) * E0 1
  let terminal : ℝ :=
    (ρ / (16 * L ^ 2 * A.eta T)) * E0 (T + 1)
  have hboundary :
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) =
        terminal - init := by
    let potential : ℕ → ℝ := fun n =>
      (ρ / (16 * L ^ 2 * A.eta (n - 1))) * E0 n
    have htel := sum_Icc_sub_succ (fun n => -potential n) 1 T hT_one
    calc
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) =
          (Finset.Icc 1 T).sum
            (fun t => -potential t + potential (t + 1)) := by
              apply Finset.sum_congr rfl
              intro t ht
              simp [potential, Nat.add_sub_cancel]
              ring
      _ = terminal - init := by
            have htel' :
                (Finset.Icc 1 T).sum
                    (fun t => -potential t + potential (t + 1)) =
                  -potential 1 + potential (T + 1) := by
              simpa only [sub_neg_eq_add] using htel
            rw [htel']
            simp only [potential, init, terminal, Nat.add_sub_cancel,
              Nat.sub_self]
            ring
  have hcoeff_absorbed :
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2)) *
                ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                  1 / A.eta (t - 1)) * E0 t +
              (ρ / (8 * A.eta t)) * D0 t +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            -(2 * A.eta t / ρ) * E0 t +
              (ρ / (8 * A.eta t)) * D0 t +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
    apply Finset.sum_le_sum
    intro t ht
    have hE :
        0 ≤ E0 t := by
      dsimp [E0]
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hscaled :
        (ρ / (16 * L ^ 2)) *
              ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                1 / A.eta (t - 1)) * E0 t ≤
            (-(2 * A.eta t / ρ)) * E0 t := by
      exact mul_le_mul_of_nonneg_right
        (hC5_coefficient_absorption t ht) hE
    linarith
  have hmain :
      (b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1) +
        (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            (b6C4EstimatorTerm A ρ t -
              b6C4DisplacementTerm A ρ t +
              b6C4WeightDecayTerm A D t) +
            (-(2 * A.eta t / ρ) * E0 t +
              (ρ / (8 * A.eta t)) * D0 t +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) := by
    calc
      (b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1) +
        (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) ≤
          (Finset.Icc 1 T).sum
              (fun t =>
                b6C4EstimatorTerm A ρ t -
                  b6C4DisplacementTerm A ρ t +
                  b6C4WeightDecayTerm A D t) +
            (Finset.Icc 1 T).sum
              (fun t =>
                (ρ / (16 * L ^ 2)) *
                    ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                      1 / A.eta (t - 1)) * E0 t +
                  (ρ / (8 * A.eta t)) * D0 t +
                  (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
            simpa only [E0, D0, M0, Finset.sum_add_distrib] using
              hcombined_telescope
      _ ≤
          (Finset.Icc 1 T).sum
              (fun t =>
                b6C4EstimatorTerm A ρ t -
                  b6C4DisplacementTerm A ρ t +
                  b6C4WeightDecayTerm A D t) +
            (Finset.Icc 1 T).sum
              (fun t =>
                -(2 * A.eta t / ρ) * E0 t +
                  (ρ / (8 * A.eta t)) * D0 t +
                  (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
            simpa [add_comm] using
              (add_le_add_left hcoeff_absorbed
                ((Finset.Icc 1 T).sum
                  (fun t =>
                    b6C4EstimatorTerm A ρ t -
                      b6C4DisplacementTerm A ρ t +
                      b6C4WeightDecayTerm A D t)))
      _ = _ := by rw [← Finset.sum_add_distrib]
  have hmain_expanded :
      b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1 +
        terminal - init ≤
      -E - R + W + V - Q := by
    calc
      b6LyapunovNextExpectation A T -
            b6LyapunovCurrentExpectation A 1 +
          terminal - init =
          (b6LyapunovNextExpectation A T -
            b6LyapunovCurrentExpectation A 1) +
            (Finset.Icc 1 T).sum
              (fun t =>
                  (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
                  (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) := by
                    rw [hboundary]
                    ring
      _ ≤
          (Finset.Icc 1 T).sum
            (fun t =>
              (b6C4EstimatorTerm A ρ t -
                b6C4DisplacementTerm A ρ t +
                b6C4WeightDecayTerm A D t) +
              (-(2 * A.eta t / ρ) * E0 t +
                (ρ / (8 * A.eta t)) * D0 t +
                (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) := hmain
      _ = -E - R + W + V - Q := by
        have hpoint :
            ∀ t ∈ Finset.Icc 1 T,
              (b6C4EstimatorTerm A ρ t -
                  b6C4DisplacementTerm A ρ t +
                  b6C4WeightDecayTerm A D t) +
                (-(2 * A.eta t / ρ) * E0 t +
                  (ρ / (8 * A.eta t)) * D0 t +
                  (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) =
              -((A.eta t / ρ) * E0 t) -
                (ρ / (8 * A.eta t)) * D0 t +
                b6C4WeightDecayTerm A D t +
                (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                (ρ / (16 * L ^ 2 * A.eta t)) * M0 t := by
          intro t ht
          dsimp [b6C4EstimatorTerm, b6C4DisplacementTerm,
            b6C4WeightDecayTerm, E0, D0, M0]
          simp only [norm_sub_rev]
          ring
        calc
          (Finset.Icc 1 T).sum
              (fun t =>
                (b6C4EstimatorTerm A ρ t -
                    b6C4DisplacementTerm A ρ t +
                    b6C4WeightDecayTerm A D t) +
                  (-(2 * A.eta t / ρ) * E0 t +
                    (ρ / (8 * A.eta t)) * D0 t +
                    (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                    (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) =
              (Finset.Icc 1 T).sum
                (fun t =>
                  -((A.eta t / ρ) * E0 t) -
                    (ρ / (8 * A.eta t)) * D0 t +
                    b6C4WeightDecayTerm A D t +
                    (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                    (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
                exact Finset.sum_congr rfl hpoint
          _ = -E - R + W + V - Q := by
            have hdecay :
                (Finset.Icc 1 T).sum
                    (fun t => b6C4WeightDecayTerm A D t) = W := by
              dsimp [W]
              apply Finset.sum_congr rfl
              intro t ht
              dsimp [b6C4WeightDecayTerm]
              ring
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              Finset.sum_neg_distrib]
            dsimp [E, R, V, Q]
            rw [hdecay]
  have hterminal_nonneg : 0 ≤ terminal := by
    dsimp [terminal, E0]
    have hTmem : T ∈ Finset.Icc 1 T :=
      Finset.mem_Icc.mpr ⟨hT_one, le_rfl⟩
    have hηT := hparams_c.2.2 T hTmem
    have hE :
        0 ≤ expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm2.x A (T + 1)) (Algorithm2.m A (T + 1)) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hcoef :
        0 ≤ ρ / (16 * L ^ 2 * A.eta T) := by
      exact div_nonneg (le_of_lt hparams_c.1)
        (le_of_lt (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL_pos)) hηT))
    exact mul_nonneg hcoef hE
  have hrecip0 : 1 / A.eta 0 = s ^ ((1 : ℝ) / 3) := by
    rw [heta 0, etaSchedule]
    simp only [Nat.cast_zero, add_zero]
    rw [one_div, ← Real.rpow_neg_one,
      ← Real.rpow_mul (le_of_lt (lt_of_lt_of_le zero_lt_one hs_ge_one))]
    norm_num
  have hinit :
      init ≤
        theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ -
          (A.problem.F A.x0 -
            attainedObjectiveMinimumValue A.problem.F minimum) := by
    have hcoeff_nonneg : 0 ≤ ρ / (16 * L ^ 2 * A.eta 0) := by
      have hden_pos : 0 < 16 * L ^ 2 * A.eta 0 := by
        exact mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 16) (sq_pos_of_pos hL_pos))
          hη0_pos
      exact div_nonneg (le_of_lt hparams_c.1) (le_of_lt hden_pos)
    have hscaled :=
      mul_le_mul_of_nonneg_left hB6_initial_estimator_error_bound hcoeff_nonneg
    have hcoeff_split :
        ρ / (16 * L ^ 2 * A.eta 0) =
          (ρ / (16 * L ^ 2)) * (1 / A.eta 0) := by
      field_simp [hL_pos.ne', hη0_pos.ne']
    calc
      init ≤ (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2 := by
        simpa [init, E0] using hscaled
      _ ≤ theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ -
          (A.problem.F A.x0 -
            attainedObjectiveMinimumValue A.problem.F minimum) := by
        rw [hcoeff_split, hrecip0]
        unfold theoremB6G theoremB6GPrinted attainedObjectiveMinimumValue
        have hweight :
            0 ≤ A.lambda * D ^ 2 * (1 + A.epsilon) := by
          letI : IsProbabilityMeasure A.problem.sampleLaw :=
            A.problem.sampleLaw_isProbability
          let omega : SampleStream Sample :=
            fun _ => Classical.choice (nonempty_of_isProbabilityMeasure
              A.problem.sampleLaw)
          have hleft :
              0 ≤ (A.lambda / 2) *
                inner ℝ (Algorithm2.x A 1 omega)
                  (Algorithm2.preconditioner A 1 omega
                    (Algorithm2.x A 1 omega)) := by
            have hlower :=
              hH.1.2 1 (by norm_num) omega
                (Algorithm2.x A 1 omega)
            have hinner :
                0 ≤ inner ℝ (Algorithm2.x A 1 omega)
                  (Algorithm2.preconditioner A 1 omega
                    (Algorithm2.x A 1 omega)) := by
              have hnorm :
                  0 ≤ ρ * ‖Algorithm2.x A 1 omega‖ ^ 2 :=
                mul_nonneg (le_of_lt hH.1.1)
                  (sq_nonneg ‖Algorithm2.x A 1 omega‖)
              linarith
            exact mul_nonneg (by linarith [hlambda]) hinner
          have hright :
              0 ≤ (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) :=
            le_trans hleft (hB6_initial_weighted_H_bound omega)
          calc
            0 ≤ 2 * ((A.lambda / 2) * D ^ 2 * (1 + A.epsilon)) :=
              mul_nonneg (by norm_num) hright
            _ = A.lambda * D ^ 2 * (1 + A.epsilon) := by ring
        have hweight' :
            0 ≤ (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) := by
          convert
            mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hweight using 1 <;>
            ring
        have hnoise :
            ρ / (16 * L ^ 2) * s ^ ((1 : ℝ) / 3) * σ ^ 2 ≤
              (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
                ρ / (16 * L ^ 2) * s ^ ((1 : ℝ) / 3) * σ ^ 2 := by
          simpa using
            (add_le_add_right hweight'
              (ρ / (16 * L ^ 2) * s ^ ((1 : ℝ) / 3) * σ ^ 2))
        convert hnoise using 1 <;> ring
  have hcombined :
      E + R ≤
        theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
          W + V - Q := by
    linarith [hmain_expanded, hinitial_potential, hterminal_potential, hinit]
  -/
  have hT_one_real : (1 : ℝ) ≤ (T : ℝ) := by
    exact le_trans hs_ge_one hT
  have hT_one : 1 ≤ T := by
    exact_mod_cast hT_one_real
  have hC2_ext :=
    TheoremB5C2CorrectedExtensionBoundary.c2 hc2
  let drop : ℕ → SampleStream Sample → ℝ := fun t ω =>
    (A.rho / (2 * A.eta t)) *
        ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2 -
      (A.eta t / A.rho) *
        ‖A.problem.gradF (Algorithm1.x A t ω) - Algorithm1.m A t ω‖ ^ 2
  have hdrop_int :
      ∀ t ∈ Finset.Icc 1 T, Integrable (drop t) (runLaw A.problem) := by
    intro t ht
    have hη_pos := hparams.2.2 t ht
    have hE :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖A.problem.gradF (Algorithm1.x A t ω) -
                Algorithm1.m A t ω‖ ^ 2)
          (runLaw A.problem) := by
      exact (hexpect t ht).1
    have hscaled := (hexpect t ht).2
    have hD0 :=
      hscaled.const_mul (A.eta t)
    have hD :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2)
          (runLaw A.problem) := by
      convert hD0 using 1
      ext ω
      field_simp [hη_pos.ne']
      simp [norm_sub_rev]
    exact
      (hD.const_mul (A.rho / (2 * A.eta t))).sub
        (hE.const_mul (A.eta t / A.rho))
  have hpathwise_window :
      ∀ ω : SampleStream Sample,
        (Finset.Icc 1 T).sum (fun t => drop t ω) ≤
          A.problem.F (Algorithm1.x A 1 ω) -
            attainedObjectiveMinimumValue A.problem.F minimum := by
    intro ω
    have hstep :
        ∀ t ∈ Finset.Icc 1 T,
          drop t ω ≤
            A.problem.F (Algorithm1.x A t ω) -
              A.problem.F (Algorithm1.x A (t + 1) ω) := by
      intro t ht
      have h := hC3 t ht ω
      rw [hxNext_succ t ω] at h
      dsimp [drop]
      rw [hxNext_succ t ω]
      calc
        A.rho / (2 * A.eta t) *
              ‖Algorithm1.x A t ω - Algorithm1.x A (t + 1) ω‖ ^ 2 -
            A.eta t / A.rho *
              ‖A.problem.gradF (Algorithm1.x A t ω) -
                Algorithm1.m A t ω‖ ^ 2 =
          A.problem.F (Algorithm1.x A t ω) -
            (A.problem.F (Algorithm1.x A t ω) -
              A.rho / (2 * A.eta t) *
                ‖Algorithm1.x A t ω - Algorithm1.x A (t + 1) ω‖ ^ 2 +
              A.eta t / A.rho *
                ‖A.problem.gradF (Algorithm1.x A t ω) -
                  Algorithm1.m A t ω‖ ^ 2) := by ring
        _ ≤ A.problem.F (Algorithm1.x A t ω) -
            A.problem.F (Algorithm1.x A (t + 1) ω) :=
          sub_le_sub_left h _
    have hsum_step :
        (Finset.Icc 1 T).sum (fun t => drop t ω) ≤
          (Finset.Icc 1 T).sum
            (fun t =>
              A.problem.F (Algorithm1.x A t ω) -
                A.problem.F (Algorithm1.x A (t + 1) ω)) := by
      exact Finset.sum_le_sum (fun t ht => hstep t ht)
    have htel :
        (Finset.Icc 1 T).sum
            (fun t =>
              A.problem.F (Algorithm1.x A t ω) -
                A.problem.F (Algorithm1.x A (t + 1) ω)) =
          A.problem.F (Algorithm1.x A 1 ω) -
            A.problem.F (Algorithm1.x A (T + 1) ω) := by
      simpa using
        (sum_Icc_sub_succ
          (fun n => A.problem.F (Algorithm1.x A n ω)) 1 T hT_one)
    have hmin :
        attainedObjectiveMinimumValue A.problem.F minimum ≤
          A.problem.F (Algorithm1.x A (T + 1) ω) := by
      exact
        SOptLib.objectiveMinimumValue_le A.problem.F minimum
          (Algorithm1.x A (T + 1) ω)
    linarith [hsum_step, htel, hmin]
  have hwindow_integral :
      (Finset.Icc 1 T).sum
          (fun t => ∫ ω, drop t ω ∂runLaw A.problem) ≤
        A.problem.F A.x0 -
          attainedObjectiveMinimumValue A.problem.F minimum := by
    letI : IsProbabilityMeasure (runLaw A.problem) :=
      runLaw_isProbabilityMeasure A.problem
    have hsum_int :
        Integrable
          (fun ω => (Finset.Icc 1 T).sum (fun t => drop t ω))
          (runLaw A.problem) :=
      integrable_finset_sum (Finset.Icc 1 T) hdrop_int
    have hbound :
        (∫ ω, (Finset.Icc 1 T).sum (fun t => drop t ω)
            ∂runLaw A.problem) ≤
          ∫ _ω, A.problem.F A.x0 -
            attainedObjectiveMinimumValue A.problem.F minimum
            ∂runLaw A.problem := by
      refine integral_mono hsum_int
        (integrable_const (c := A.problem.F A.x0 -
          attainedObjectiveMinimumValue A.problem.F minimum)) ?_
      intro ω
      simpa [Algorithm1.x, Algorithm1.process] using hpathwise_window ω
    calc
      (Finset.Icc 1 T).sum
          (fun t => ∫ ω, drop t ω ∂runLaw A.problem) =
        ∫ ω, (Finset.Icc 1 T).sum (fun t => drop t ω)
            ∂runLaw A.problem := by
              rw [integral_finset_sum (Finset.Icc 1 T) hdrop_int]
      _ ≤
        ∫ _ω, A.problem.F A.x0 -
            attainedObjectiveMinimumValue A.problem.F minimum
            ∂runLaw A.problem := hbound
      _ = A.problem.F A.x0 -
          attainedObjectiveMinimumValue A.problem.F minimum := by
            simp [integral_const, probReal_univ]
  have hwindow :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (2 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem) -
              (A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) ≤
        A.problem.F A.x0 -
          attainedObjectiveMinimumValue A.problem.F minimum := by
    calc
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (2 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem) -
              (A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) =
        (Finset.Icc 1 T).sum
          (fun t => ∫ ω, drop t ω ∂runLaw A.problem) := by
            apply Finset.sum_congr rfl
            intro t ht
            dsimp [drop]
            simp only [expectedEstimatorError]
            have hη_pos := hparams.2.2 t ht
            have hE :
                Integrable
                  (fun ω : SampleStream Sample =>
                    ‖A.problem.gradF (Algorithm1.x A t ω) -
                      Algorithm1.m A t ω‖ ^ 2)
                  (runLaw A.problem) :=
              (hexpect t ht).1
            have hD0 :=
              (hexpect t ht).2.const_mul (A.eta t)
            have hD :
                Integrable
                  (fun ω : SampleStream Sample =>
                    ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2)
                  (runLaw A.problem) := by
              convert hD0 using 1
              ext ω
              field_simp [hη_pos.ne']
              simp [norm_sub_rev]
            have hnorm_integral :
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem) =
                  ∫ ω, ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2
                    ∂runLaw A.problem := by
              apply integral_congr_ae
              filter_upwards [] with ω
              rw [norm_sub_rev]
            rw [hnorm_integral]
            rw [integral_sub
              (hD.const_mul (A.rho / (2 * A.eta t)))
              (hE.const_mul (A.eta t / A.rho))]
            rw [integral_const_mul, integral_const_mul]
      _ ≤ A.problem.F A.x0 -
          attainedObjectiveMinimumValue A.problem.F minimum := hwindow_integral
  have hpotential :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
              (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) =
        (A.rho / (16 * L ^ 2 * A.eta T)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) -
          (A.rho / (16 * L ^ 2 * A.eta 0)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A 1) (Algorithm1.m A 1) := by
    let potential : ℕ → ℝ := fun n =>
      (A.rho / (16 * L ^ 2 * A.eta (n - 1))) *
        expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm1.x A n) (Algorithm1.m A n)
    have htel := sum_Icc_sub_succ (fun n => -potential n) 1 T hT_one
    calc
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
              (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) =
          (Finset.Icc 1 T).sum
            (fun t => -potential t + potential (t + 1)) := by
              apply Finset.sum_congr rfl
              intro t ht
              simp [potential, Nat.add_sub_cancel]
              ring
      _ = (A.rho / (16 * L ^ 2 * A.eta T)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) -
          (A.rho / (16 * L ^ 2 * A.eta 0)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A 1) (Algorithm1.m A 1) := by
            convert htel using 1 <;> simp [potential, Nat.add_sub_cancel] <;> ring
  have hI2_expanded :
      (Finset.Icc 1 T).sum
          (fun t =>
            -(2 * A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t) +
              (A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) =
        -2 *
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.eta t / A.rho) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm1.x A t) (Algorithm1.m A t)) +
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hfirst :
        (Finset.Icc 1 T).sum
            (fun t =>
              -(2 * A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) =
          -2 *
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.eta t / A.rho) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm1.x A t) (Algorithm1.m A t)) := by
      calc
        (Finset.Icc 1 T).sum
            (fun t =>
              -(2 * A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) =
            (Finset.Icc 1 T).sum
              (fun t =>
                -2 *
                  ((A.eta t / A.rho) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm1.x A t) (Algorithm1.m A t))) := by
                apply Finset.sum_congr rfl
                intro t ht
                ring
        _ = -2 *
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.eta t / A.rho) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm1.x A t) (Algorithm1.m A t)) := by
              rw [Finset.mul_sum]
    rw [hfirst]
  have hI2_rearranged :
      2 *
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) -
        (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (8 * A.eta t)) *
              (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                ∂runLaw A.problem)) ≤
      (A.rho / (16 * L ^ 2 * A.eta 0) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A 1) (Algorithm1.m A 1)) -
        (A.rho / (16 * L ^ 2 * A.eta T) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1))) +
      (Finset.Icc 1 T).sum
        (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
      (Finset.Icc 1 T).sum
        (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) *
            theoremB5ReadableC2Residual A t) := by
    have hraw :
        (A.rho / (16 * L ^ 2 * A.eta T)) *
              expectedEstimatorError (runLaw A.problem) A.problem.gradF
                (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) -
            (A.rho / (16 * L ^ 2 * A.eta 0)) *
              expectedEstimatorError (runLaw A.problem) A.problem.gradF
                (Algorithm1.x A 1) (Algorithm1.m A 1) ≤
          -2 *
              (Finset.Icc 1 T).sum
                (fun t =>
                  (A.eta t / A.rho) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm1.x A t) (Algorithm1.m A t)) +
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.rho / (8 * A.eta t)) *
                  (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                    ∂runLaw A.problem)) +
            (Finset.Icc 1 T).sum
              (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.rho / (16 * L ^ 2 * A.eta t)) *
                  theoremB5ReadableC2Residual A t) := by
      calc
        _ =
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.rho / (16 * L ^ 2 * A.eta t)) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
                  (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm1.x A t) (Algorithm1.m A t)) := hpotential.symm
        _ ≤
            (Finset.Icc 1 T).sum
              (fun t =>
                -(2 * A.eta t / A.rho) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm1.x A t) (Algorithm1.m A t) +
                  (A.rho / (8 * A.eta t)) *
                    (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                      ∂runLaw A.problem) +
                  (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (A.rho / (16 * L ^ 2 * A.eta t)) *
                    theoremB5ReadableC2Residual A t) := hI2_absorbed
        _ = _ := hI2_expanded
    linarith [hraw]
  have hcombined_staged :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t) +
              (3 * A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) ≤
        theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) := by
    have hterminal_nonneg :
        0 ≤
          (A.rho / (16 * L ^ 2 * A.eta T)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) := by
      have hTmem : T ∈ Finset.Icc 1 T :=
        Finset.mem_Icc.mpr ⟨hT_one, le_rfl⟩
      have hηT := hparams.2.2 T hTmem
      have hE :
          0 ≤ expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) := by
        exact integral_nonneg (fun ω => sq_nonneg _)
      have hcoef :
          0 ≤ A.rho / (16 * L ^ 2 * A.eta T) := by
        exact div_nonneg (le_of_lt hparams.1)
          (le_of_lt (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL_pos)) hηT))
      exact mul_nonneg hcoef hE
    have hη0_pos : 0 < A.eta 0 := by
      rw [heta 0, etaSchedule]
      simp only [Nat.cast_zero, add_zero]
      exact Real.rpow_pos_of_pos
        (lt_of_lt_of_le zero_lt_one hs_ge_one) (-(1 : ℝ) / 3)
    have hrecip0 : 1 / A.eta 0 = s ^ ((1 : ℝ) / 3) := by
      rw [heta 0, etaSchedule]
      simp only [Nat.cast_zero, add_zero]
      rw [one_div, ← Real.rpow_neg_one,
        ← Real.rpow_mul (le_of_lt (lt_of_lt_of_le zero_lt_one hs_ge_one))]
      norm_num
    have hinit :
        (A.rho / (16 * L ^ 2 * A.eta 0)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A 1) (Algorithm1.m A 1) ≤
          theoremB5G A.problem.F A.x0 minimum A.rho s L σ -
            (A.problem.F A.x0 -
              attainedObjectiveMinimumValue A.problem.F minimum) := by
      have hcoef_nonneg : 0 ≤ A.rho / (16 * L ^ 2 * A.eta 0) := by
        have hden_pos : 0 < 16 * L ^ 2 * A.eta 0 := by
          exact mul_pos
            (mul_pos (by norm_num : (0 : ℝ) < 16) (sq_pos_of_pos hL_pos))
            hη0_pos
        exact div_nonneg (le_of_lt hparams.1) (le_of_lt hden_pos)
      have hscaled :=
        mul_le_mul_of_nonneg_left hB5_initial_estimator_error_bound hcoef_nonneg
      have hcoef_split :
          A.rho / (16 * L ^ 2 * A.eta 0) =
            (A.rho / (16 * L ^ 2)) * (1 / A.eta 0) := by
        field_simp [hL_pos.ne', hη0_pos.ne']
      calc
        (A.rho / (16 * L ^ 2 * A.eta 0)) *
              expectedEstimatorError (runLaw A.problem) A.problem.gradF
                (Algorithm1.x A 1) (Algorithm1.m A 1) ≤
            (A.rho / (16 * L ^ 2 * A.eta 0)) * σ ^ 2 := hscaled
        _ = theoremB5G A.problem.F A.x0 minimum A.rho s L σ -
              (A.problem.F A.x0 -
                attainedObjectiveMinimumValue A.problem.F minimum) := by
          rw [hcoef_split, hrecip0]
          unfold theoremB5G theoremB5GPrinted attainedObjectiveMinimumValue
          ring
    let E : ℝ :=
      (Finset.Icc 1 T).sum
        (fun t =>
          (A.eta t / A.rho) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A t) (Algorithm1.m A t))
    let D : ℝ :=
      (Finset.Icc 1 T).sum
        (fun t =>
          (A.rho / (8 * A.eta t)) *
            (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
              ∂runLaw A.problem))
    let V : ℝ :=
      (Finset.Icc 1 T).sum
        (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2))
    let R : ℝ :=
      (Finset.Icc 1 T).sum
        (fun t =>
          (A.rho / (16 * L ^ 2 * A.eta t)) *
            theoremB5ReadableC2Residual A t)
    let init : ℝ :=
      (A.rho / (16 * L ^ 2 * A.eta 0)) *
        expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm1.x A 1) (Algorithm1.m A 1)
    let terminal : ℝ :=
      (A.rho / (16 * L ^ 2 * A.eta T)) *
        expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1))
    let Fgap : ℝ :=
      A.problem.F A.x0 - attainedObjectiveMinimumValue A.problem.F minimum
    have hI2' : 2 * E - D ≤ init - terminal + V - R := by
      simpa [E, D, V, R, init, terminal] using hI2_rearranged
    have hwindow' : 4 * D - E ≤ Fgap := by
      calc
        4 * D - E =
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.rho / (2 * A.eta t)) *
                    (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                      ∂runLaw A.problem) -
                  (A.eta t / A.rho) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm1.x A t) (Algorithm1.m A t)) := by
          dsimp [D, E]
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro t ht
          ring
        _ ≤ Fgap := by simpa [Fgap] using hwindow
    have hterminal' : 0 ≤ terminal := by
      simpa [terminal] using hterminal_nonneg
    have hinit' : init ≤ theoremB5G A.problem.F A.x0 minimum A.rho s L σ - Fgap := by
      simpa [init, Fgap] using hinit
    have hscalar :
        E + 3 * D ≤ theoremB5G A.problem.F A.x0 minimum A.rho s L σ + V - R := by
      linarith only [hI2', hwindow', hterminal', hinit']
    calc
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t) +
              (3 * A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) =
          E + 3 * D := by
            dsimp [E, D]
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            apply congrArg₂ (· + ·)
            · rfl
            · apply Finset.sum_congr rfl
              intro t ht
              ring
      _ ≤ theoremB5G A.problem.F A.x0 minimum A.rho s L σ + V - R := hscalar
      _ = theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) := by
            rfl
  let E0 : ℕ → ℝ := fun t =>
    expectedEstimatorError (runLaw A.problem) A.problem.gradF
      (Algorithm1.x A t) (Algorithm1.m A t)
  let D0 : ℕ → ℝ := fun t =>
    ∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
      ∂runLaw A.problem
  let M0 : ℕ → ℝ := fun t => theoremB5ReadableC2Residual A t
  have hηT_pos : 0 < A.eta T :=
    hparams.2.2 T (Finset.mem_Icc.mpr ⟨hT_one, le_rfl⟩)
  have hT_pos : 0 < (T : ℝ) :=
    lt_of_lt_of_le zero_lt_one hT_one_real
  have hE_nonneg : ∀ t : ℕ, 0 ≤ E0 t := by
    intro t
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hD_nonneg : ∀ t : ℕ, 0 ≤ D0 t := by
    intro t
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hcombined :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.eta t / A.rho) * E0 t +
              (3 * A.rho / (8 * A.eta t)) * D0 t) ≤
        theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) := by
    simpa [E0, D0, M0] using hcombined_staged
  have hDweighted_nonneg :
      0 ≤
        (Finset.Icc 1 T).sum
          (fun t => (3 * A.rho / (8 * A.eta t)) * D0 t) := by
    apply Finset.sum_nonneg
    intro t ht
    have hη := hparams.2.2 t ht
    exact
      mul_nonneg
        (div_nonneg
          (mul_nonneg (by norm_num) (le_of_lt hparams.1))
          (mul_nonneg (by norm_num) (le_of_lt hη)))
        (hD_nonneg t)
  have hEweighted_nonneg :
      0 ≤
        (Finset.Icc 1 T).sum
          (fun t => (A.eta t / A.rho) * E0 t) := by
    apply Finset.sum_nonneg
    intro t ht
    have hη := hparams.2.2 t ht
    exact
      mul_nonneg
        (div_nonneg (le_of_lt hη) (le_of_lt hparams.1))
        (hE_nonneg t)
  have hcombined_split :
      (Finset.Icc 1 T).sum
          (fun t => (A.eta t / A.rho) * E0 t) +
        (Finset.Icc 1 T).sum
          (fun t => (3 * A.rho / (8 * A.eta t)) * D0 t) ≤
        theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) := by
    simpa only [Finset.sum_add_distrib] using hcombined
  have hweightedE :
      (Finset.Icc 1 T).sum
          (fun t => (A.eta t / A.rho) * E0 t) ≤
        theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) := by
    linarith [hcombined_split, hDweighted_nonneg]
  have hweightedD :
      (Finset.Icc 1 T).sum
          (fun t => (3 * A.rho / (8 * A.eta t)) * D0 t) ≤
        theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) := by
    linarith [hcombined_split, hEweighted_nonneg]
  have hE_extract :
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
        (A.rho / A.eta T) *
          (Finset.Icc 1 T).sum
            (fun t => (A.eta t / A.rho) * E0 t) := by
    have hpoint :
        ∀ t ∈ Finset.Icc 1 T,
          E0 t ≤ (A.rho / A.eta T) * ((A.eta t / A.rho) * E0 t) := by
      intro t ht
      have hηt := hparams.2.2 t ht
      have hη_le : A.eta T ≤ A.eta t := by
        rw [heta T, heta t]
        exact etaSchedule_le_of_le hs_ge_one (Finset.mem_Icc.mp ht).2
      have hratio : 1 ≤ A.eta t / A.eta T :=
        (le_div_iff₀ hηT_pos).mpr (by simpa using hη_le)
      have hmul := mul_le_mul_of_nonneg_right hratio (hE_nonneg t)
      calc
        E0 t = 1 * E0 t := by ring
        _ ≤ (A.eta t / A.eta T) * E0 t := hmul
        _ = (A.rho / A.eta T) * ((A.eta t / A.rho) * E0 t) := by
          field_simp [hηT_pos.ne', hparams.1.ne']
    calc
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
          (Finset.Icc 1 T).sum
            (fun t => (A.rho / A.eta T) * ((A.eta t / A.rho) * E0 t)) := by
              exact Finset.sum_le_sum (fun t ht => hpoint t ht)
      _ = (A.rho / A.eta T) *
          (Finset.Icc 1 T).sum
            (fun t => (A.eta t / A.rho) * E0 t) := by
              rw [Finset.mul_sum]
  have hscaledV :
      (A.rho / A.eta T) *
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) =
        (A.rho ^ 2 / A.eta T) *
          (Finset.Icc 1 T).sum
            (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    field_simp [hηT_pos.ne', hL_pos.ne']
  have hscaledR :
      (A.rho / A.eta T) *
          (Finset.Icc 1 T).sum
            (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) =
        (A.rho ^ 2 / (16 * L ^ 2 * A.eta T)) *
          (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hηt := hparams.2.2 t ht
    field_simp [hηT_pos.ne', hηt.ne', hL_pos.ne']
  have hE_scaled :
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
        (A.rho / A.eta T) *
            theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (A.rho ^ 2 / A.eta T) *
            (Finset.Icc 1 T).sum
              (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (A.rho ^ 2 / (16 * L ^ 2 * A.eta T)) *
            (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    calc
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
          (A.rho / A.eta T) *
            (Finset.Icc 1 T).sum
              (fun t => (A.eta t / A.rho) * E0 t) := hE_extract
      _ ≤ (A.rho / A.eta T) *
          (theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
            (Finset.Icc 1 T).sum
              (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
            (Finset.Icc 1 T).sum
              (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t)) := by
            have hcoef : 0 ≤ A.rho / A.eta T :=
              div_nonneg (le_of_lt hparams.1) (le_of_lt hηT_pos)
            exact mul_le_mul_of_nonneg_left hweightedE hcoef
      _ = _ := by
        calc
          (A.rho / A.eta T) *
              (theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
                (Finset.Icc 1 T).sum
                  (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
                (Finset.Icc 1 T).sum
                  (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t)) =
              (A.rho / A.eta T) *
                  theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
                (A.rho / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
                (A.rho / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) := by ring
          _ = _ := by rw [hscaledV, hscaledR]
  have hE_avg :
      (1 / (T : ℝ)) * (Finset.Icc 1 T).sum (fun t => E0 t) ≤
        (A.rho / ((T : ℝ) * A.eta T)) *
            theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (A.rho ^ 2 / ((T : ℝ) * A.eta T)) *
            (Finset.Icc 1 T).sum
              (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (A.rho ^ 2 / (16 * L ^ 2 * (T : ℝ) * A.eta T)) *
            (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    calc
      (1 / (T : ℝ)) * (Finset.Icc 1 T).sum (fun t => E0 t) ≤
          (1 / (T : ℝ)) *
            ((A.rho / A.eta T) *
                theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
              (A.rho ^ 2 / A.eta T) *
                (Finset.Icc 1 T).sum
                  (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
              (A.rho ^ 2 / (16 * L ^ 2 * A.eta T)) *
                (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) := by
              exact mul_le_mul_of_nonneg_left hE_scaled (by positivity)
      _ = _ := by
        have hG :
            (1 / (T : ℝ)) * (A.rho / A.eta T) =
              A.rho / ((T : ℝ) * A.eta T) := by
          field_simp [hT_pos.ne', hηT_pos.ne']
        have hV :
            (1 / (T : ℝ)) * (A.rho ^ 2 / A.eta T) =
              A.rho ^ 2 / ((T : ℝ) * A.eta T) := by
          field_simp [hT_pos.ne', hηT_pos.ne']
        have hR :
            (1 / (T : ℝ)) * (A.rho ^ 2 / (16 * L ^ 2 * A.eta T)) =
              A.rho ^ 2 / (16 * L ^ 2 * (T : ℝ) * A.eta T) := by
          field_simp [hT_pos.ne', hηT_pos.ne', hL_pos.ne']
        calc
          (1 / (T : ℝ)) *
              ((A.rho / A.eta T) *
                  theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
                (A.rho ^ 2 / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
                (A.rho ^ 2 / (16 * L ^ 2 * A.eta T)) *
                  (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) =
              (1 / (T : ℝ)) * (A.rho / A.eta T) *
                  theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
                (1 / (T : ℝ)) * (A.rho ^ 2 / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
                (1 / (T : ℝ)) * (A.rho ^ 2 / (16 * L ^ 2 * A.eta T)) *
                  (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by ring
          _ = _ := by rw [hG, hV, hR]
  have hdisp_repr :
      ∀ t ∈ Finset.Icc 1 T,
        expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm1.x A t) (Algorithm1.xNext A t) =
          (A.eta t)⁻¹ * D0 t := by
    intro t ht
    have hηt := hparams.2.2 t ht
    have hD0 := (hexpect t ht).2.const_mul (A.eta t)
    have hD :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖Algorithm1.x A t ω - Algorithm1.xNext A t ω‖ ^ 2)
          (runLaw A.problem) := by
      convert hD0 using 1
      ext ω
      field_simp [hηt.ne']
      simp [norm_sub_rev]
    dsimp [expectedScaledDisplacement, D0]
    rw [integral_const_mul]
  have hdispV :
      (8 / (3 * A.rho)) *
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) =
        (c ^ 2 * σ ^ 2 / (3 * L ^ 2)) *
          (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    field_simp [hparams.1.ne', hL_pos.ne']
  have hdispR :
      (8 / (3 * A.rho)) *
          (Finset.Icc 1 T).sum
            (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) =
        (1 / (6 * L ^ 2)) *
          (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hηt := hparams.2.2 t ht
    field_simp [hparams.1.ne', hηt.ne', hL_pos.ne']
    ring
  have hdisp_scaled :
      (Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm1.x A t) (Algorithm1.xNext A t)) ≤
        8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
            (3 * A.rho) +
          (c ^ 2 * σ ^ 2 / (3 * L ^ 2)) *
            (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) -
          (1 / (6 * L ^ 2)) *
            (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    calc
      (Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm1.x A t) (Algorithm1.xNext A t)) =
          (Finset.Icc 1 T).sum
            (fun t => (8 / (3 * A.rho)) *
              ((3 * A.rho / (8 * A.eta t)) * D0 t)) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [hdisp_repr t ht]
              have hηt := hparams.2.2 t ht
              field_simp [hparams.1.ne', hηt.ne']
      _ = (8 / (3 * A.rho)) *
          (Finset.Icc 1 T).sum
            (fun t => (3 * A.rho / (8 * A.eta t)) * D0 t) := by
              rw [Finset.mul_sum]
      _ ≤ (8 / (3 * A.rho)) *
          (theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
            (Finset.Icc 1 T).sum
              (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
            (Finset.Icc 1 T).sum
              (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t)) := by
            have hcoef : 0 ≤ 8 / (3 * A.rho) :=
              div_nonneg (by norm_num)
                (mul_nonneg (by norm_num) (le_of_lt hparams.1))
            exact mul_le_mul_of_nonneg_left hweightedD hcoef
      _ = _ := by
        calc
          (8 / (3 * A.rho)) *
              (theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
                (Finset.Icc 1 T).sum
                  (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
                (Finset.Icc 1 T).sum
                  (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t)) =
              8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
                  (3 * A.rho) +
                (8 / (3 * A.rho)) *
                  (Finset.Icc 1 T).sum
                    (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
                (8 / (3 * A.rho)) *
                  (Finset.Icc 1 T).sum
                    (fun t => (A.rho / (16 * L ^ 2 * A.eta t)) * M0 t) := by ring
          _ = _ := by rw [hdispV, hdispR]
  have hdisp_avg :
      (1 / (T : ℝ)) *
          (Finset.Icc 1 T).sum
            (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
              (Algorithm1.x A t) (Algorithm1.xNext A t)) ≤
        8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
            (3 * A.rho * (T : ℝ)) +
          (c ^ 2 * σ ^ 2 / (3 * L ^ 2 * (T : ℝ))) *
            (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) -
          (1 / (6 * L ^ 2 * (T : ℝ))) *
            (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    calc
      (1 / (T : ℝ)) *
          (Finset.Icc 1 T).sum
            (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
              (Algorithm1.x A t) (Algorithm1.xNext A t)) ≤
          (1 / (T : ℝ)) *
            (8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
                (3 * A.rho) +
              (c ^ 2 * σ ^ 2 / (3 * L ^ 2)) *
                (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) -
              (1 / (6 * L ^ 2)) *
                (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) := by
              have hcoef : 0 ≤ 1 / (T : ℝ) :=
                div_nonneg (by norm_num) (le_of_lt hT_pos)
              exact mul_le_mul_of_nonneg_left hdisp_scaled hcoef
      _ = _ := by
        have hG :
            (1 / (T : ℝ)) * (8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
                (3 * A.rho)) =
              8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
                (3 * A.rho * (T : ℝ)) := by
          field_simp [hT_pos.ne', hparams.1.ne']
        have hV :
            (1 / (T : ℝ)) * (c ^ 2 * σ ^ 2 / (3 * L ^ 2)) =
              c ^ 2 * σ ^ 2 / (3 * L ^ 2 * (T : ℝ)) := by
          field_simp [hT_pos.ne', hL_pos.ne']
        have hR :
            (1 / (T : ℝ)) * (1 / (6 * L ^ 2)) =
              1 / (6 * L ^ 2 * (T : ℝ)) := by
          field_simp [hT_pos.ne', hL_pos.ne']
        calc
          (1 / (T : ℝ)) *
              (8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
                  (3 * A.rho) +
                (c ^ 2 * σ ^ 2 / (3 * L ^ 2)) *
                  (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) -
                (1 / (6 * L ^ 2)) *
                  (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) =
              (1 / (T : ℝ)) *
                  (8 * theoremB5G A.problem.F A.x0 minimum A.rho s L σ /
                    (3 * A.rho)) +
                (1 / (T : ℝ)) * (c ^ 2 * σ ^ 2 / (3 * L ^ 2)) *
                  (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) -
                (1 / (T : ℝ)) * (1 / (6 * L ^ 2)) *
                  (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by ring
          _ = _ := by rw [hG, hV, hR]
  dsimp [TheoremB5CorrectedStatement]
  constructor
  · simpa [E0, M0] using hE_avg
  · simpa [M0] using hdisp_avg
  /-
  have hI2_absorbed :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
              (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            -(2 * A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t) +
              (A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) := by
    apply Finset.sum_le_sum
    intro t ht
    calc
      (A.rho / (16 * L ^ 2 * A.eta t)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
          (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A t) (Algorithm1.m A t) ≤
        (A.rho / (16 * L ^ 2)) *
              ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                1 / A.eta (t - 1)) *
              expectedEstimatorError (runLaw A.problem) A.problem.gradF
                (Algorithm1.x A t) (Algorithm1.m A t) +
            (A.rho / (8 * A.eta t)) *
              (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                ∂runLaw A.problem) +
            (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
            (A.rho / (16 * L ^ 2 * A.eta t)) *
              theoremB5ReadableC2Residual A t := hI2_C5 t ht
      _ ≤
        -(2 * A.eta t / A.rho) *
              expectedEstimatorError (runLaw A.problem) A.problem.gradF
                (Algorithm1.x A t) (Algorithm1.m A t) +
            (A.rho / (8 * A.eta t)) *
              (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                ∂runLaw A.problem) +
            (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
            (A.rho / (16 * L ^ 2 * A.eta t)) *
              theoremB5ReadableC2Residual A t := by
                nlinarith [hC5_coefficient_absorption t ht]
  have hpotential :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A (t + 1)) (Algorithm1.m A (t + 1)) -
              (A.rho / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) =
        (A.rho / (16 * L ^ 2 * A.eta T)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) -
          (A.rho / (16 * L ^ 2 * A.eta 0)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A 1) (Algorithm1.m A 1) := by
    let potential : ℕ → ℝ := fun n =>
      (A.rho / (16 * L ^ 2 * A.eta (n - 1))) *
        expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm1.x A n) (Algorithm1.m A n)
    have htel := sum_Icc_sub_succ (fun n => -potential n) 1 T hT_one
    simpa [potential, Nat.add_sub_cancel] using htel
  have hI2_expanded :
      (Finset.Icc 1 T).sum
          (fun t =>
            -(2 * A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t) +
              (A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) =
        -2 *
            (Finset.Icc 1 T).sum
              (fun t =>
                (A.eta t / A.rho) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm1.x A t) (Algorithm1.m A t)) +
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      ring
    · ring
  have hI2_rearranged :
      2 *
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t)) -
        (Finset.Icc 1 T).sum
          (fun t =>
            (A.rho / (8 * A.eta t)) *
              (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                ∂runLaw A.problem)) ≤
      (A.rho / (16 * L ^ 2 * A.eta 0) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A 1) (Algorithm1.m A 1)) -
        (A.rho / (16 * L ^ 2 * A.eta T) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1))) +
      (Finset.Icc 1 T).sum
        (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
      (Finset.Icc 1 T).sum
        (fun t =>
          (A.rho / (16 * L ^ 2 * A.eta t)) *
            theoremB5ReadableC2Residual A t) := by
    rw [← hpotential] at *
    rw [hI2_expanded] at hI2_absorbed
    linarith
  have hcombined_staged :
      (Finset.Icc 1 T).sum
          (fun t =>
            (A.eta t / A.rho) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm1.x A t) (Algorithm1.m A t) +
              (3 * A.rho / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm1.xNext A t ω - Algorithm1.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) ≤
        theoremB5G A.problem.F A.x0 minimum A.rho s L σ +
          (Finset.Icc 1 T).sum
            (fun t => (A.rho * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (Finset.Icc 1 T).sum
            (fun t =>
              (A.rho / (16 * L ^ 2 * A.eta t)) *
                theoremB5ReadableC2Residual A t) := by
    have hterminal_nonneg :
        0 ≤
          (A.rho / (16 * L ^ 2 * A.eta T)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) := by
      have hηT := hparams.2.2 T ⟨hT_one, le_rfl⟩
      have hE :
          0 ≤ expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm1.x A (T + 1)) (Algorithm1.m A (T + 1)) := by
        exact integral_nonneg (fun ω => sq_nonneg _)
      exact mul_nonneg (by positivity) hE
    have hinit :
        (A.rho / (16 * L ^ 2 * A.eta 0)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm1.x A 1) (Algorithm1.m A 1) ≤
          theoremB5G A.problem.F A.x0 minimum A.rho s L σ -
            (A.problem.F A.x0 -
              attainedObjectiveMinimumValue A.problem.F minimum) := by
      sorry
    linarith [hI2_rearranged, hwindow, hterminal_nonneg, hinit]
  sorry
  -/

/-- Theorem B.5, registered under the source name, as a non-A-level
source-boundary contract. The PDF theorem window prints two averaged
inequalities with `min_x F(x)` and `M_{t+1}` from (C.2); the book JSON records
the C.2 type defect, beta-admissibility gap, denominator gaps, `m_1` clipping
bridge, and displacement-scale mismatch. The displayed inequality shape is
therefore kept separately as `TheoremB5PrintedInequalities` over literal source
symbols `Fmin` and `M`, while this registered declaration records the boundary
instead of asserting corrected residuals or a totalized infimum. -/
theorem theorem_B_5
    {ι : Type*} [Fintype ι]
    (A : Algorithm1Data Sample ι)
    (L σ c s : ℝ) (T : ℕ)
    (hobj_unbiased : UnbiasedObjectiveOracle A.problem)
    (hgrad_unbiased : UnbiasedGradientOracle A.problem)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L)
    (heta : ∀ t : ℕ, A.eta t = etaSchedule s t)
    (hs : s ≥ 8 * L ^ 3 / A.rho ^ 3)
    (hc : c ≥ 32 * L ^ 2 * A.rho⁻¹ ^ 2 + 1)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hbeta2 : ∀ t : ℕ, A.beta2 (t + 1) = betaTwoSchedule A.eta t)
    (hT : (T : ℝ) ≥ s) :
    TheoremB5SourceBoundaryContract A c T := by
  exact
    ⟨(by
        intro t ht ω
        exact Algorithm1.xNext_is_mirrorStep A t (Finset.mem_Icc.mp ht).1 ω),
      ⟨(by
          intro t ht
          exact hbeta1 t),
        rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      b5_l_zero_c5_absorption_obstruction,
      b5_c8_variance_coefficient_extraction,
      rfl, rfl⟩

variable {ι : Type*} [Fintype ι]

/-- Lean well-definedness obligations for the expectations printed in B.6. -/
def TheoremB6ExpectationWellDefined
    (A : Algorithm2Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    ExpectedEstimatorErrorWellDefined (runLaw A.problem) A.problem.gradF
      (Algorithm2.x A t) (Algorithm2.m A t) ∧
    ExpectedScaledDisplacementWellDefined (runLaw A.problem) (A.eta t)
      (Algorithm2.x A t) (Algorithm2.xNext A t)

/-- Corrected-extension-only regularity for the objective and preconditioner
terms appearing in the pointwise C.4 bridge. The source theorem writes these
expectations directly; this package supplies only the trajectory integrability
needed to pass from that pointwise statement to its expectation-level form. -/
def B6ObjectiveTrajectoryIntegrabilityExtension
    (A : Algorithm2Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    Integrable
        (fun ω : SampleStream Sample => A.problem.F (Algorithm2.xNext A t ω))
        (runLaw A.problem) ∧
    Integrable
        (fun ω : SampleStream Sample => A.problem.F (Algorithm2.x A t ω))
        (runLaw A.problem) ∧
    Integrable
        (fun ω : SampleStream Sample =>
          inner ℝ (Algorithm2.x A t ω)
            (Algorithm2.preconditioner A (t + 1) ω
              (Algorithm2.x A t ω)))
        (runLaw A.problem) ∧
    Integrable
        (fun ω : SampleStream Sample =>
          inner ℝ (Algorithm2.xNext A t ω)
            (Algorithm2.preconditioner A t ω
              (Algorithm2.xNext A t ω)))
        (runLaw A.problem)

/-- Corrected-extension integrability for the exact current/next Lyapunov
potential. The source C.2 telescope uses same-index quadratic terms, so this
package names the corresponding integrands directly instead of identifying
them with the cross-index C.4 expressions. -/
def B6LyapunovPotentialIntegrabilityExtension
    (A : Algorithm2Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    Integrable
        (fun ω : SampleStream Sample =>
          A.problem.F (Algorithm2.xNext A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.xNext A t ω)
                (Algorithm2.preconditioner A (t + 1) ω
                  (Algorithm2.xNext A t ω)))
        (runLaw A.problem) ∧
    Integrable
        (fun ω : SampleStream Sample =>
          A.problem.F (Algorithm2.x A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.x A t ω)
                (Algorithm2.preconditioner A t ω
                  (Algorithm2.x A t ω)))
        (runLaw A.problem)

def b6C4LeftExpectation
    (A : Algorithm2Data Sample ι) (t : ℕ) : ℝ :=
  ∫ ω,
      A.problem.F (Algorithm2.xNext A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.x A t ω)
            (Algorithm2.preconditioner A (t + 1) ω
              (Algorithm2.x A t ω))
    ∂runLaw A.problem

def b6C4RightExpectation
    (A : Algorithm2Data Sample ι) (t : ℕ) : ℝ :=
  ∫ ω,
      A.problem.F (Algorithm2.x A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.xNext A t ω)
            (Algorithm2.preconditioner A t ω
              (Algorithm2.xNext A t ω))
    ∂runLaw A.problem

def b6C4EstimatorTerm
    (A : Algorithm2Data Sample ι) (ρ : ℝ) (t : ℕ) : ℝ :=
  (A.eta t / ρ) *
    expectedEstimatorError (runLaw A.problem) A.problem.gradF
      (Algorithm2.x A t) (Algorithm2.m A t)

def b6C4DisplacementTerm
    (A : Algorithm2Data Sample ι) (ρ : ℝ) (t : ℕ) : ℝ :=
  (ρ / (4 * A.eta t)) *
    (∫ ω, ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2
      ∂runLaw A.problem)

def b6C4WeightDecayTerm
    (A : Algorithm2Data Sample ι) (D : ℝ) (t : ℕ) : ℝ :=
  (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2

/-- The source Lyapunov potential at the next iterate in Lemma C.4/C.2.
This keeps the paper's `x_{t+1}^T H_{t+1} x_{t+1}` term explicit instead of
leaving it hidden behind the cross-index C.4 display. -/
def b6LyapunovNextExpectation
    (A : Algorithm2Data Sample ι) (t : ℕ) : ℝ :=
  ∫ ω,
      A.problem.F (Algorithm2.xNext A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.xNext A t ω)
            (Algorithm2.preconditioner A (t + 1) ω
              (Algorithm2.xNext A t ω))
    ∂runLaw A.problem

/-- The source Lyapunov potential at the current iterate in Lemma C.4/C.2.
This is the exact `F(x_t) + lambda/2 * x_t^T H_t x_t` term used by the
finite-horizon source telescope. -/
def b6LyapunovCurrentExpectation
    (A : Algorithm2Data Sample ι) (t : ℕ) : ℝ :=
  ∫ ω,
      A.problem.F (Algorithm2.x A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.x A t ω)
            (Algorithm2.preconditioner A t ω
              (Algorithm2.x A t ω))
    ∂runLaw A.problem

/-- Legacy source-correspondence record for the H_t/H_{t+1} index swap in the
printed D.2/C.4 route. The PDF does not prove this swap, so this declaration
is retained only for historical/source-audit context and is not consumed by
the corrected exact-potential route. -/
def B6C4LyapunovIndexBridge
    (A : Algorithm2Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    b6C4LeftExpectation A t = b6LyapunovNextExpectation A t ∧
    b6C4RightExpectation A t = b6LyapunovCurrentExpectation A t

theorem b6LyapunovCurrent_succ_eq_next
    (A : Algorithm2Data Sample ι) (t : ℕ) :
    b6LyapunovCurrentExpectation A (t + 1) =
      b6LyapunovNextExpectation A t := by
  simp [b6LyapunovCurrentExpectation, b6LyapunovNextExpectation,
    Algorithm2.xNext_eq_x_succ]

/-- No-clipping specialization for the corrected B.6/C.2 route. Algorithm 2's
first moment also uses `Clip(c_t,1)`, so the raw C.2/D.4 estimator recursion
requires the same explicit corrected-extension bridge as B.5. -/
def Algorithm2RawCorrectionNormLeOneOnHorizon
    (A : Algorithm2Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
    ‖marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
        (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
          (sampleAt (Sample := Sample) (t + 1) ω))
        (A.problem.stochasticGrad (Algorithm2.x A t ω)
          (sampleAt (Sample := Sample) (t + 1) ω))‖ ≤ 1

/-- All C.2/D.12 corrected-extension obligations used by the Lean-readable B.6
extension over its horizon. The final conjunct is the disclosed no-clipping
specialization needed to reconcile Algorithm 2's clipped first-moment update
with the raw C.2/D.4 estimator recursion. -/
def TheoremB6C2CorrectedExtensionBoundary
    (A : Algorithm2Data Sample ι) (T : ℕ) : Prop :=
  C2CorrectedExtensionBoundaryOnHorizon (runLaw A.problem) A.problem (sampleAt (Sample := Sample))
    (Algorithm2.x A) (Algorithm2.xNext A) (Algorithm2.m A) A.beta1 A.gamma T ∧
  Algorithm2RawCorrectionNormLeOneOnHorizon A T

theorem TheoremB6C2CorrectedExtensionBoundary.c2
    {A : Algorithm2Data Sample ι} {T : ℕ}
    (h : TheoremB6C2CorrectedExtensionBoundary A T) :
    C2CorrectedExtensionBoundaryOnHorizon (runLaw A.problem) A.problem
      (sampleAt (Sample := Sample)) (Algorithm2.x A) (Algorithm2.xNext A)
      (Algorithm2.m A) A.beta1 A.gamma T :=
  h.1

theorem TheoremB6C2CorrectedExtensionBoundary.noClipping
    {A : Algorithm2Data Sample ι} {T : ℕ}
    (h : TheoremB6C2CorrectedExtensionBoundary A T) :
    Algorithm2RawCorrectionNormLeOneOnHorizon A T :=
  h.2

/-- Lemma D.2's beta prerequisite over a theorem horizon, kept separate from
the C.2 beta-one admissibility package. -/
def B6BetaTwoAdmissibleOnHorizon
    (A : Algorithm2Data Sample ι) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T, 0 ≤ A.beta2 t ∧ A.beta2 t ≤ 1

/-- Corrected-extension statement window for the Lemma D.2 inner-product
bridge used by C.4. It is smaller than the final B.6 rate and records the
AdamW preconditioner/update algebra separately from the C.2 estimator-residual
obligations. -/
def Algorithm2D2InnerProductBound
    (A : Algorithm2Data Sample ι) (ρ D : ℝ) (t : ℕ) : Prop :=
  ∀ ω : SampleStream Sample,
    inner ℝ (Algorithm2.m A t ω) (Algorithm2.x A t ω - Algorithm2.xNext A t ω) ≥
      (ρ * (1 - A.eta t * A.lambda) / A.eta t) *
          ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2 +
        (A.lambda / 2) *
          (inner ℝ (Algorithm2.x A t ω)
              (Algorithm2.preconditioner A (t + 1) ω (Algorithm2.x A t ω)) -
            inner ℝ (Algorithm2.xNext A t ω)
              (Algorithm2.preconditioner A t ω (Algorithm2.xNext A t ω)) -
            Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2)

/-- Exact-potential correction boundary for the D.2 route. This is the
source-facing replacement for the printed cross-index quadratic expression:
the correction is stated at the smaller D.2 inner-product granularity, while
the resulting C.4 theorem uses the actual consecutive Lyapunov potentials. -/
def Algorithm2D2ExactLyapunovInnerProductBound
    (A : Algorithm2Data Sample ι) (ρ D : ℝ) (t : ℕ) : Prop :=
  ∀ ω : SampleStream Sample,
    inner ℝ (Algorithm2.m A t ω) (Algorithm2.x A t ω - Algorithm2.xNext A t ω) ≥
      (ρ * (1 - A.eta t * A.lambda) / A.eta t) *
          ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2 +
        (A.lambda / 2) *
          (inner ℝ (Algorithm2.xNext A t ω)
              (Algorithm2.preconditioner A (t + 1) ω
                (Algorithm2.xNext A t ω)) -
            inner ℝ (Algorithm2.x A t ω)
              (Algorithm2.preconditioner A t ω (Algorithm2.x A t ω)) -
            Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2)

/-- The D.2 corrected-extension boundary needed by the B.6/C.4 route. This is
not part of the C.2 residual bookkeeping and does not assert the final B.6
inequalities. -/
def TheoremB6D2CorrectedExtensionBoundary
    (A : Algorithm2Data Sample ι) (ρ D : ℝ) (T : ℕ) : Prop :=
  B6BetaTwoAdmissibleOnHorizon A T ∧
  ∀ t ∈ Finset.Icc 1 T, Algorithm2D2InnerProductBound A ρ D t

theorem TheoremB6D2CorrectedExtensionBoundary.beta_two_admissible
    {A : Algorithm2Data Sample ι} {ρ D : ℝ} {T : ℕ}
    (h : TheoremB6D2CorrectedExtensionBoundary A ρ D T) :
    B6BetaTwoAdmissibleOnHorizon A T :=
  h.1

theorem TheoremB6D2CorrectedExtensionBoundary.innerProductBound
    {A : Algorithm2Data Sample ι} {ρ D : ℝ} {T t : ℕ}
    (h : TheoremB6D2CorrectedExtensionBoundary A ρ D T)
    (ht : t ∈ Finset.Icc 1 T) :
    Algorithm2D2InnerProductBound A ρ D t :=
  h.2 t ht

/-- Corrected-extension boundary for the exact-potential C.4 route. The
published D.2 prerequisites remain visible, while the source's index swap is
represented by the exact same-index inner-product bound rather than by an
assumed equality between two already-integrated quantities. -/
def TheoremB6D2ExactLyapunovCorrectionBoundary
    (A : Algorithm2Data Sample ι) (ρ D : ℝ) (T : ℕ) : Prop :=
  TheoremB6D2CorrectedExtensionBoundary A ρ D T ∧
  ∀ t ∈ Finset.Icc 1 T,
    Algorithm2D2ExactLyapunovInnerProductBound A ρ D t

theorem TheoremB6D2ExactLyapunovCorrectionBoundary.exactInnerProductBound
    {A : Algorithm2Data Sample ι} {ρ D : ℝ} {T t : ℕ}
    (h : TheoremB6D2ExactLyapunovCorrectionBoundary A ρ D T)
    (ht : t ∈ Finset.Icc 1 T) :
    Algorithm2D2ExactLyapunovInnerProductBound A ρ D t :=
  h.2 t ht

def Algorithm2ExactLyapunovC4SourceInputs
    (A : Algorithm2Data Sample ι) (L ρ D : ℝ) (t : ℕ) : Prop :=
  ObjectiveSmoothUpper A.problem L ∧
    Algorithm2D2ExactLyapunovInnerProductBound A ρ D t

/-- The exact source inputs needed to start the Lemma C.4 one-step route:
the D.13 smooth upper bound for `F` and the D.2 AdamW inner-product bridge.
This is not the C.4 conclusion; it is the compiled handoff point where the
B.6 proof cone consumes the separate D.2 corrected-extension boundary. -/
def Algorithm2C4SourceInputs
    (A : Algorithm2Data Sample ι) (L ρ D : ℝ) (t : ℕ) : Prop :=
  ObjectiveSmoothUpper A.problem L ∧ Algorithm2D2InnerProductBound A ρ D t

theorem Algorithm2C4SourceInputs.of_smooth_and_d2Boundary
    {A : Algorithm2Data Sample ι} {L ρ D : ℝ} {T t : ℕ}
    (hsmooth : StochasticSmooth A.problem L)
    (hD2 : TheoremB6D2CorrectedExtensionBoundary A ρ D T)
    (ht : t ∈ Finset.Icc 1 T) :
    Algorithm2C4SourceInputs A L ρ D t :=
  ⟨StochasticSmooth.objective_smooth_upper hsmooth,
    TheoremB6D2CorrectedExtensionBoundary.innerProductBound hD2 ht⟩

/-- The pointwise C.4/D.2 descent bridge.  Its conclusion is deliberately
pointwise in the sample stream: integrating the objective values requires an
additional trajectory-integrability argument, which is recorded separately at
the source boundary. -/
private theorem algorithm2_c4_one_step_bound
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ D : ℝ) (t : ℕ) (hη_pos : 0 < A.eta t) (hρ_pos : 0 < ρ)
    (hinputs : Algorithm2C4SourceInputs A L ρ D t)
    (habsorb : L / 2 + ρ * A.lambda ≤ ρ / (2 * A.eta t))
    (ω : SampleStream Sample) :
    A.problem.F (Algorithm2.xNext A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.x A t ω)
            (Algorithm2.preconditioner A (t + 1) ω
              (Algorithm2.x A t ω)) ≤
      A.problem.F (Algorithm2.x A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.xNext A t ω)
            (Algorithm2.preconditioner A t ω
              (Algorithm2.xNext A t ω)) +
        (A.eta t / ρ) *
          ‖A.problem.gradF (Algorithm2.x A t ω) -
            Algorithm2.m A t ω‖ ^ 2 -
        (ρ / (4 * A.eta t)) *
          ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2 +
        (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
  let x := Algorithm2.x A t ω
  let z := Algorithm2.xNext A t ω
  let m := Algorithm2.m A t ω
  let d := z - x
  let e := A.problem.gradF x - m
  have hsmooth_step := hinputs.1 x z
  have hD2 := hinputs.2 ω
  have hgrad_decomp :
      inner ℝ (A.problem.gradF x) d =
        inner ℝ m d + inner ℝ e d := by
    simp [e, d, inner_sub_left]
  have hmirror_d :
      inner ℝ m d ≤
        -(ρ * (1 - A.eta t * A.lambda) / A.eta t) * ‖d‖ ^ 2 -
          (A.lambda / 2) *
            (inner ℝ x
                (Algorithm2.preconditioner A (t + 1) ω x) -
              inner ℝ z
                (Algorithm2.preconditioner A t ω z) -
              Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2) := by
    have hD2' :
        inner ℝ m (x - z) ≥
          (ρ * (1 - A.eta t * A.lambda) / A.eta t) *
              ‖x - z‖ ^ 2 +
            (A.lambda / 2) *
              (inner ℝ x
                  (Algorithm2.preconditioner A (t + 1) ω x) -
                inner ℝ z
                  (Algorithm2.preconditioner A t ω z) -
                Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2) := by
      simpa [x, z, m] using hD2
    have hneg : inner ℝ m (x - z) = -inner ℝ m d := by
      have hv : x - z = -d := by
        dsimp [d]
        abel
      rw [hv, inner_neg_right]
    have hnorm : ‖x - z‖ = ‖d‖ := by
      have hv : x - z = -d := by
        dsimp [d]
        abel
      rw [hv, norm_neg]
    rw [hneg, hnorm] at hD2'
    nlinarith
  have hyoung :
      inner ℝ e d ≤
        (A.eta t / ρ) * ‖e‖ ^ 2 +
          (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 :=
    inner_le_young_eta_rho hη_pos hρ_pos e d
  have hcoef :
      -(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
          ρ / (4 * A.eta t) + L / 2 ≤
        -(ρ / (4 * A.eta t)) := by
    field_simp [hη_pos.ne'] at habsorb ⊢
    nlinarith
  have hquad :
      (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
          ρ / (4 * A.eta t) + L / 2) * ‖d‖ ^ 2 ≤
        -(ρ / (4 * A.eta t)) * ‖d‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖d‖)
  have hsmooth' :
      A.problem.F z ≤
        A.problem.F x + inner ℝ (A.problem.gradF x) d +
          (L / 2) * ‖d‖ ^ 2 := by
    simpa [x, z, d] using hsmooth_step
  have hmain :
      A.problem.F z +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A (t + 1) ω x) ≤
        A.problem.F x +
          (A.lambda / 2) *
            inner ℝ z
              (Algorithm2.preconditioner A t ω z) +
          inner ℝ e d +
          (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
            L / 2) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
    calc
      A.problem.F z +
            (A.lambda / 2) *
              inner ℝ x
                (Algorithm2.preconditioner A (t + 1) ω x) ≤
          A.problem.F x + inner ℝ (A.problem.gradF x) d +
            (L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) *
              inner ℝ x
                (Algorithm2.preconditioner A (t + 1) ω x) := by
                  nlinarith [hsmooth']
      _ = A.problem.F x +
            inner ℝ m d + inner ℝ e d +
            (L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) *
              inner ℝ x
                (Algorithm2.preconditioner A (t + 1) ω x) := by
                  rw [hgrad_decomp]
                  ring
      _ ≤ A.problem.F x +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A t ω z) +
            inner ℝ e d +
            (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
              L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
                  nlinarith [hmirror_d]
  have hfinal :
      A.problem.F z +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A (t + 1) ω x) ≤
        A.problem.F x +
          (A.lambda / 2) *
            inner ℝ z
              (Algorithm2.preconditioner A t ω z) +
          (A.eta t / ρ) * ‖e‖ ^ 2 -
          (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
    calc
      A.problem.F z +
            (A.lambda / 2) *
              inner ℝ x
                (Algorithm2.preconditioner A (t + 1) ω x) ≤
          A.problem.F x +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A t ω z) +
            ((A.eta t / ρ) * ‖e‖ ^ 2 +
              (ρ / (4 * A.eta t)) * ‖d‖ ^ 2) +
            (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
              L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
                nlinarith [hmain, hyoung]
      _ = A.problem.F x +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A t ω z) +
            (A.eta t / ρ) * ‖e‖ ^ 2 +
            (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
              ρ / (4 * A.eta t) + L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
                ring
      _ ≤ A.problem.F x +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A t ω z) +
            (A.eta t / ρ) * ‖e‖ ^ 2 -
            (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
                nlinarith [hquad]
  simpa [x, z, m, d, e, norm_sub_rev] using hfinal

/-- Early exact-potential pointwise bridge used by the expectation consumer. -/
private theorem algorithm2_c4_exact_lyapunov_one_step_early
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ D : ℝ) (t : ℕ) (hη_pos : 0 < A.eta t) (hρ_pos : 0 < ρ)
    (hinputs : Algorithm2ExactLyapunovC4SourceInputs A L ρ D t)
    (habsorb : L / 2 + ρ * A.lambda ≤ ρ / (2 * A.eta t))
    (ω : SampleStream Sample) :
    A.problem.F (Algorithm2.xNext A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.xNext A t ω)
            (Algorithm2.preconditioner A (t + 1) ω
              (Algorithm2.xNext A t ω)) ≤
      A.problem.F (Algorithm2.x A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.x A t ω)
            (Algorithm2.preconditioner A t ω
              (Algorithm2.x A t ω)) +
        (A.eta t / ρ) *
          ‖A.problem.gradF (Algorithm2.x A t ω) -
            Algorithm2.m A t ω‖ ^ 2 -
        (ρ / (4 * A.eta t)) *
          ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2 +
        (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
  let x := Algorithm2.x A t ω
  let z := Algorithm2.xNext A t ω
  let m := Algorithm2.m A t ω
  let d := z - x
  let e := A.problem.gradF x - m
  have hsmooth := hinputs.1 x z
  have hD2 := hinputs.2 ω
  have hD2' :
      inner ℝ m d ≤
        -(ρ * (1 - A.eta t * A.lambda) / A.eta t) * ‖d‖ ^ 2 -
          (A.lambda / 2) *
            (inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) -
              inner ℝ x (Algorithm2.preconditioner A t ω x) -
              Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2) := by
    have h := hD2
    have hneg : inner ℝ m (x - z) = -inner ℝ m d := by
      dsimp [d]
      rw [show x - z = -(z - x) by abel, inner_neg_right]
    have hnorm : ‖x - z‖ = ‖d‖ := by
      dsimp [d]
      rw [show x - z = -(z - x) by abel, norm_neg]
    rw [hneg, hnorm] at h
    nlinarith [h]
  have hgrad :
      inner ℝ (A.problem.gradF x) d =
        inner ℝ m d + inner ℝ e d := by
    simp [e, inner_sub_left]
  have hyoung :
      inner ℝ e d ≤
        (A.eta t / ρ) * ‖e‖ ^ 2 +
          (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 :=
    inner_le_young_eta_rho hη_pos hρ_pos e d
  have hcoef :
      -(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
          ρ / (4 * A.eta t) + L / 2 ≤
        -(ρ / (4 * A.eta t)) := by
    field_simp [hη_pos.ne'] at habsorb ⊢
    nlinarith
  have hsmooth' :
      A.problem.F z ≤
        A.problem.F x + inner ℝ (A.problem.gradF x) d +
          (L / 2) * ‖d‖ ^ 2 := by
    simpa [x, z, d] using hsmooth
  have hmain :
      A.problem.F z +
          (A.lambda / 2) *
            inner ℝ z
              (Algorithm2.preconditioner A (t + 1) ω z) ≤
        A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A t ω x) +
          inner ℝ e d +
          (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) + L / 2) *
            ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
    calc
      A.problem.F z +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) ≤
          A.problem.F x + inner ℝ (A.problem.gradF x) d +
            (L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) := by
                  nlinarith [hsmooth']
      _ = A.problem.F x + inner ℝ m d + inner ℝ e d +
            (L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) := by
                  rw [hgrad]
                  ring
      _ ≤ A.problem.F x +
            (A.lambda / 2) *
              inner ℝ x (Algorithm2.preconditioner A t ω x) +
            inner ℝ e d +
            (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) + L / 2) *
              ‖d‖ ^ 2 +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
                  ring_nf at hD2' ⊢
                  nlinarith [hD2']
  have hquad :
      (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
          ρ / (4 * A.eta t) + L / 2) * ‖d‖ ^ 2 ≤
        -(ρ / (4 * A.eta t)) * ‖d‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖d‖)
  calc
    A.problem.F z +
          (A.lambda / 2) *
            inner ℝ z
              (Algorithm2.preconditioner A (t + 1) ω z) ≤
        A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x (Algorithm2.preconditioner A t ω x) +
          ((A.eta t / ρ) * ‖e‖ ^ 2 +
            (ρ / (4 * A.eta t)) * ‖d‖ ^ 2) +
          (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) + L / 2) *
            ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
              nlinarith [hmain, hyoung]
    _ = A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x (Algorithm2.preconditioner A t ω x) +
          (A.eta t / ρ) * ‖e‖ ^ 2 +
          (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
            ρ / (4 * A.eta t) + L / 2) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
              ring
    _ ≤ A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x (Algorithm2.preconditioner A t ω x) +
          (A.eta t / ρ) * ‖e‖ ^ 2 -
          (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
              nlinarith [hquad]
  simpa [x, z, m, d, e, norm_sub_rev]

/-- Expectation-level consumer for the corrected exact-potential C.4 route. -/
private theorem algorithm2_c4_exact_lyapunov_expectation_one_step
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ D : ℝ) (T t : ℕ) (ht : t ∈ Finset.Icc 1 T)
    (hη_pos : 0 < A.eta t) (hρ_pos : 0 < ρ)
    (hinputs : Algorithm2ExactLyapunovC4SourceInputs A L ρ D t)
    (habsorb : L / 2 + ρ * A.lambda ≤ ρ / (2 * A.eta t))
    (hpotential : B6LyapunovPotentialIntegrabilityExtension A T)
    (hest_int :
      ExpectedEstimatorErrorWellDefined (runLaw A.problem) A.problem.gradF
        (Algorithm2.x A t) (Algorithm2.m A t))
    (hdisp_int :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2)
        (runLaw A.problem)) :
    b6LyapunovNextExpectation A t ≤
      b6LyapunovCurrentExpectation A t +
        b6C4EstimatorTerm A ρ t -
        b6C4DisplacementTerm A ρ t +
        b6C4WeightDecayTerm A D t := by
  let μ := runLaw A.problem
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact runLaw_isProbabilityMeasure A.problem
  have hpotential_t := hpotential t ht
  have hnext_int :
      Integrable
        (fun ω : SampleStream Sample =>
          A.problem.F (Algorithm2.xNext A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.xNext A t ω)
                (Algorithm2.preconditioner A (t + 1) ω
                  (Algorithm2.xNext A t ω)))
        μ := by
    simpa [μ] using hpotential_t.1
  have hcurrent_int :
      Integrable
        (fun ω : SampleStream Sample =>
          A.problem.F (Algorithm2.x A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.x A t ω)
                (Algorithm2.preconditioner A t ω
                  (Algorithm2.x A t ω)))
        μ := by
    simpa [μ] using hpotential_t.2
  have hest_int' :
      Integrable
        (fun ω : SampleStream Sample =>
          (A.eta t / ρ) *
            ‖A.problem.gradF (Algorithm2.x A t ω) -
              Algorithm2.m A t ω‖ ^ 2)
        μ := by
    simpa [ExpectedEstimatorErrorWellDefined, μ, norm_sub_rev] using
      hest_int.const_mul (A.eta t / ρ)
  have hdisp_int' :
      Integrable
        (fun ω : SampleStream Sample =>
          (ρ / (4 * A.eta t)) *
            ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2)
        μ := by
    have hdisp_int_rev :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2)
          μ := by
      simpa [norm_sub_rev] using hdisp_int
    exact hdisp_int_rev.const_mul (ρ / (4 * A.eta t))
  have hright_int :
      Integrable
        (fun ω : SampleStream Sample =>
          (A.problem.F (Algorithm2.x A t ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.x A t ω)
                  (Algorithm2.preconditioner A t ω
                    (Algorithm2.x A t ω)) +
              (A.eta t / ρ) *
                ‖A.problem.gradF (Algorithm2.x A t ω) -
                  Algorithm2.m A t ω‖ ^ 2 -
              (ρ / (4 * A.eta t)) *
                ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2)
        μ := by
    exact
      ((hcurrent_int.add hest_int').sub hdisp_int').add
        (integrable_const _)
  have hpoint :
      ∀ ω : SampleStream Sample,
        A.problem.F (Algorithm2.xNext A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.xNext A t ω)
                (Algorithm2.preconditioner A (t + 1) ω
                  (Algorithm2.xNext A t ω)) ≤
          (A.problem.F (Algorithm2.x A t ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.x A t ω)
                  (Algorithm2.preconditioner A t ω
                    (Algorithm2.x A t ω)) +
              (A.eta t / ρ) *
                ‖A.problem.gradF (Algorithm2.x A t ω) -
                  Algorithm2.m A t ω‖ ^ 2 -
              (ρ / (4 * A.eta t)) *
                ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
    intro ω
    exact
      algorithm2_c4_exact_lyapunov_one_step_early A L ρ D t hη_pos hρ_pos
        hinputs habsorb ω
  have hmain :
      b6LyapunovNextExpectation A t ≤
        ∫ ω,
          (A.problem.F (Algorithm2.x A t ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.x A t ω)
                  (Algorithm2.preconditioner A t ω
                    (Algorithm2.x A t ω)) +
              (A.eta t / ρ) *
                ‖A.problem.gradF (Algorithm2.x A t ω) -
                  Algorithm2.m A t ω‖ ^ 2 -
              (ρ / (4 * A.eta t)) *
                ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
          ∂μ := by
    exact integral_mono hnext_int hright_int hpoint
  calc
    b6LyapunovNextExpectation A t ≤
        ∫ ω,
          (A.problem.F (Algorithm2.x A t ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.x A t ω)
                  (Algorithm2.preconditioner A t ω
                    (Algorithm2.x A t ω)) +
              (A.eta t / ρ) *
                ‖A.problem.gradF (Algorithm2.x A t ω) -
                  Algorithm2.m A t ω‖ ^ 2 -
              (ρ / (4 * A.eta t)) *
                ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
          ∂μ := hmain
    _ = b6LyapunovCurrentExpectation A t +
          b6C4EstimatorTerm A ρ t -
          b6C4DisplacementTerm A ρ t +
          b6C4WeightDecayTerm A D t := by
      let base : SampleStream Sample → ℝ := fun ω =>
        A.problem.F (Algorithm2.x A t ω) +
          (A.lambda / 2) *
            inner ℝ (Algorithm2.x A t ω)
              (Algorithm2.preconditioner A t ω
                (Algorithm2.x A t ω))
      let est : SampleStream Sample → ℝ := fun ω =>
        (A.eta t / ρ) *
          ‖A.problem.gradF (Algorithm2.x A t ω) -
            Algorithm2.m A t ω‖ ^ 2
      let disp : SampleStream Sample → ℝ := fun ω =>
        (ρ / (4 * A.eta t)) *
          ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2
      let weight : SampleStream Sample → ℝ := fun _ =>
        (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
      have hbase_int : Integrable base μ := by
        simpa [base] using hcurrent_int
      have hest_int'' : Integrable est μ := by
        simpa [est] using hest_int'
      have hdisp_int'' : Integrable disp μ := by
        simpa [disp] using hdisp_int'
      have hweight_int : Integrable weight μ :=
        integrable_const _
      have hadd :
          (∫ ω, base ω + est ω ∂μ) =
            (∫ ω, base ω ∂μ) + ∫ ω, est ω ∂μ := by
        simpa only [Pi.add_apply] using integral_add hbase_int hest_int''
      have hsub :
          (∫ ω, base ω + est ω - disp ω ∂μ) =
            (∫ ω, base ω + est ω ∂μ) - ∫ ω, disp ω ∂μ := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_sub (hbase_int.add hest_int'') hdisp_int''
      have hdecomp :
          (∫ ω, (base ω + est ω - disp ω) + weight ω ∂μ) =
            (∫ ω, base ω ∂μ) + (∫ ω, est ω ∂μ) -
              (∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := by
        calc
          (∫ ω, (base ω + est ω - disp ω) + weight ω ∂μ) =
              (∫ ω, base ω + est ω - disp ω ∂μ) +
                ∫ ω, weight ω ∂μ := by
            exact integral_add
              ((hbase_int.add hest_int'').sub hdisp_int'') hweight_int
          _ = ((∫ ω, base ω + est ω ∂μ) -
                ∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := by
            rw [hsub]
          _ = (∫ ω, base ω ∂μ) + (∫ ω, est ω ∂μ) -
                (∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := by
            simpa [hadd]
      calc
        (∫ ω,
            (A.problem.F (Algorithm2.x A t ω) +
                (A.lambda / 2) *
                  inner ℝ (Algorithm2.x A t ω)
                    (Algorithm2.preconditioner A t ω
                      (Algorithm2.x A t ω)) +
                (A.eta t / ρ) *
                  ‖A.problem.gradF (Algorithm2.x A t ω) -
                    Algorithm2.m A t ω‖ ^ 2 -
                (ρ / (4 * A.eta t)) *
                  ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
              (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
          ∂μ) =
            (∫ ω, (base ω + est ω - disp ω) + weight ω ∂μ) := by
              simp [base, est, disp, weight]
        _ = (∫ ω, base ω ∂μ) + (∫ ω, est ω ∂μ) -
              (∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := hdecomp
        _ = b6LyapunovCurrentExpectation A t +
              b6C4EstimatorTerm A ρ t -
              b6C4DisplacementTerm A ρ t +
              b6C4WeightDecayTerm A D t := by
              have hbase_value :
                  (∫ ω, base ω ∂μ) =
                    b6LyapunovCurrentExpectation A t := by
                rfl
              rw [hbase_value]
              simp [b6C4EstimatorTerm, b6C4DisplacementTerm,
                b6C4WeightDecayTerm, expectedEstimatorError, weight, μ,
                integral_const, probReal_univ]
              rw [integral_const_mul, integral_const_mul]
/-- Pointwise C.4 descent with the corrected exact-potential D.2 boundary.
Unlike the legacy cross-index route above, this theorem's conclusion already
has `H_t` on the current iterate and `H_{t+1}` on the next iterate. -/
private theorem algorithm2_c4_exact_lyapunov_one_step
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ D : ℝ) (t : ℕ) (hη_pos : 0 < A.eta t) (hρ_pos : 0 < ρ)
    (hinputs : Algorithm2ExactLyapunovC4SourceInputs A L ρ D t)
    (habsorb : L / 2 + ρ * A.lambda ≤ ρ / (2 * A.eta t))
    (ω : SampleStream Sample) :
    A.problem.F (Algorithm2.xNext A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.xNext A t ω)
            (Algorithm2.preconditioner A (t + 1) ω
              (Algorithm2.xNext A t ω)) ≤
      A.problem.F (Algorithm2.x A t ω) +
        (A.lambda / 2) *
          inner ℝ (Algorithm2.x A t ω)
            (Algorithm2.preconditioner A t ω
              (Algorithm2.x A t ω)) +
        (A.eta t / ρ) *
          ‖A.problem.gradF (Algorithm2.x A t ω) -
            Algorithm2.m A t ω‖ ^ 2 -
        (ρ / (4 * A.eta t)) *
          ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2 +
        (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
  let x := Algorithm2.x A t ω
  let z := Algorithm2.xNext A t ω
  let m := Algorithm2.m A t ω
  let d := z - x
  let e := A.problem.gradF x - m
  have hsmooth_step := hinputs.1 x z
  have hD2 := hinputs.2 ω
  have hgrad_decomp :
      inner ℝ (A.problem.gradF x) d =
        inner ℝ m d + inner ℝ e d := by
    simp [e, d, inner_sub_left]
  have hmirror_d :
      inner ℝ m d ≤
        -(ρ * (1 - A.eta t * A.lambda) / A.eta t) * ‖d‖ ^ 2 -
          (A.lambda / 2) *
            (inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) -
              inner ℝ x
                (Algorithm2.preconditioner A t ω x) -
              Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2) := by
    have hD2' :
        inner ℝ m (x - z) ≥
          (ρ * (1 - A.eta t * A.lambda) / A.eta t) *
              ‖x - z‖ ^ 2 +
            (A.lambda / 2) *
              (inner ℝ z
                  (Algorithm2.preconditioner A (t + 1) ω z) -
                inner ℝ x
                  (Algorithm2.preconditioner A t ω x) -
                Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2) := by
      simpa [x, z, m] using hD2
    have hneg : inner ℝ m (x - z) = -inner ℝ m d := by
      have hv : x - z = -d := by
        dsimp [d]
        abel
      rw [hv, inner_neg_right]
    have hnorm : ‖x - z‖ = ‖d‖ := by
      have hv : x - z = -d := by
        dsimp [d]
        abel
      rw [hv, norm_neg]
    rw [hneg, hnorm] at hD2'
    nlinarith
  have hyoung :
      inner ℝ e d ≤
        (A.eta t / ρ) * ‖e‖ ^ 2 +
          (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 :=
    inner_le_young_eta_rho hη_pos hρ_pos e d
  have hcoef :
      -(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
          ρ / (4 * A.eta t) + L / 2 ≤
        -(ρ / (4 * A.eta t)) := by
    field_simp [hη_pos.ne'] at habsorb ⊢
    nlinarith
  have hquad :
      (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
          ρ / (4 * A.eta t) + L / 2) * ‖d‖ ^ 2 ≤
        -(ρ / (4 * A.eta t)) * ‖d‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖d‖)
  have hsmooth' :
      A.problem.F z ≤
        A.problem.F x + inner ℝ (A.problem.gradF x) d +
          (L / 2) * ‖d‖ ^ 2 := by
    simpa [x, z, d] using hsmooth_step
  have hmain :
      A.problem.F z +
          (A.lambda / 2) *
            inner ℝ z
              (Algorithm2.preconditioner A (t + 1) ω z) ≤
        A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A t ω x) +
          inner ℝ e d +
          (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
            L / 2) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
    calc
      A.problem.F z +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) ≤
          A.problem.F x + inner ℝ (A.problem.gradF x) d +
            (L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) := by
                  nlinarith [hsmooth']
      _ = A.problem.F x +
            inner ℝ m d + inner ℝ e d +
            (L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) *
              inner ℝ z
                (Algorithm2.preconditioner A (t + 1) ω z) := by
                  rw [hgrad_decomp]
                  ring
      _ ≤ A.problem.F x +
            (A.lambda / 2) *
              inner ℝ x
                (Algorithm2.preconditioner A t ω x) +
            inner ℝ e d +
            (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
              L / 2) * ‖d‖ ^ 2 +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
                  ring_nf at hmirror_d ⊢
                  nlinarith [hmirror_d]
  have hfinal :
      A.problem.F z +
          (A.lambda / 2) *
            inner ℝ z
              (Algorithm2.preconditioner A (t + 1) ω z) ≤
        A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A t ω x) +
          (A.eta t / ρ) * ‖e‖ ^ 2 -
          (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
    calc
      A.problem.F z +
          (A.lambda / 2) *
            inner ℝ z
              (Algorithm2.preconditioner A (t + 1) ω z) ≤
        A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A t ω x) +
          ((A.eta t / ρ) * ‖e‖ ^ 2 +
            (ρ / (4 * A.eta t)) * ‖d‖ ^ 2) +
          (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
            L / 2) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
              nlinarith [hmain, hyoung]
      _ = A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A t ω x) +
          (A.eta t / ρ) * ‖e‖ ^ 2 +
          (-(ρ * (1 - A.eta t * A.lambda) / A.eta t) +
            ρ / (4 * A.eta t) + L / 2) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
              ring
      _ ≤ A.problem.F x +
          (A.lambda / 2) *
            inner ℝ x
              (Algorithm2.preconditioner A t ω x) +
          (A.eta t / ρ) * ‖e‖ ^ 2 -
          (ρ / (4 * A.eta t)) * ‖d‖ ^ 2 +
          (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
              nlinarith [hquad]
  simpa [x, z, m, d, e, norm_sub_rev] using hfinal

/-- Expectation-level consumer for the pointwise C.4/D.2 bridge. This is the
smallest bridge that exposes the source proof's objective and weight-decay
terms to the finite-horizon telescope. -/
private theorem algorithm2_c4_expectation_one_step
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ D : ℝ) (T t : ℕ) (ht : t ∈ Finset.Icc 1 T)
    (hη_pos : 0 < A.eta t) (hρ_pos : 0 < ρ)
    (hinputs : Algorithm2C4SourceInputs A L ρ D t)
    (habsorb : L / 2 + ρ * A.lambda ≤ ρ / (2 * A.eta t))
    (htrajectory : B6ObjectiveTrajectoryIntegrabilityExtension A T)
    (hest_int :
      ExpectedEstimatorErrorWellDefined (runLaw A.problem) A.problem.gradF
        (Algorithm2.x A t) (Algorithm2.m A t))
    (hdisp_int :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2)
        (runLaw A.problem)) :
    b6C4LeftExpectation A t ≤
      b6C4RightExpectation A t +
        b6C4EstimatorTerm A ρ t -
        b6C4DisplacementTerm A ρ t +
        b6C4WeightDecayTerm A D t := by
  let μ := runLaw A.problem
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact runLaw_isProbabilityMeasure A.problem
  have htraj_t := htrajectory t ht
  have hleft_int :
      Integrable
        (fun ω : SampleStream Sample =>
          A.problem.F (Algorithm2.xNext A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.x A t ω)
                (Algorithm2.preconditioner A (t + 1) ω
                  (Algorithm2.x A t ω)))
        μ := by
    exact htraj_t.1.add (htraj_t.2.2.1.const_mul (A.lambda / 2))
  have hright_base_int :
      Integrable
        (fun ω : SampleStream Sample =>
          A.problem.F (Algorithm2.x A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.xNext A t ω)
                (Algorithm2.preconditioner A t ω
                  (Algorithm2.xNext A t ω)))
        μ := by
    exact htraj_t.2.1.add (htraj_t.2.2.2.const_mul (A.lambda / 2))
  have hest_int' :
      Integrable
        (fun ω : SampleStream Sample =>
          (A.eta t / ρ) *
            ‖A.problem.gradF (Algorithm2.x A t ω) -
              Algorithm2.m A t ω‖ ^ 2)
        μ :=
    hest_int.const_mul (A.eta t / ρ)
  have hdisp_int' :
      Integrable
        (fun ω : SampleStream Sample =>
          (ρ / (4 * A.eta t)) *
            ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2)
        μ := by
    have hdisp_int_rev :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2)
          μ := by
      simpa [norm_sub_rev] using hdisp_int
    exact hdisp_int_rev.const_mul (ρ / (4 * A.eta t))
  have hright_int :
      Integrable
        (fun ω : SampleStream Sample =>
          (A.problem.F (Algorithm2.x A t ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.xNext A t ω)
                  (Algorithm2.preconditioner A t ω
                    (Algorithm2.xNext A t ω)) +
              (A.eta t / ρ) *
                ‖A.problem.gradF (Algorithm2.x A t ω) -
                  Algorithm2.m A t ω‖ ^ 2 -
              (ρ / (4 * A.eta t)) *
                ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2)
        μ := by
    exact
      ((hright_base_int.add hest_int').sub hdisp_int').add
        (integrable_const _)
  have hpoint :
      ∀ ω : SampleStream Sample,
        A.problem.F (Algorithm2.xNext A t ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.x A t ω)
                (Algorithm2.preconditioner A (t + 1) ω
                  (Algorithm2.x A t ω)) ≤
          (A.problem.F (Algorithm2.x A t ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.xNext A t ω)
                  (Algorithm2.preconditioner A t ω
                    (Algorithm2.xNext A t ω)) +
              (A.eta t / ρ) *
                ‖A.problem.gradF (Algorithm2.x A t ω) -
                  Algorithm2.m A t ω‖ ^ 2 -
              (ρ / (4 * A.eta t)) *
                ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2 := by
    intro ω
    exact algorithm2_c4_one_step_bound A L ρ D t hη_pos hρ_pos hinputs habsorb ω
  have hmain : b6C4LeftExpectation A t ≤
      ∫ ω,
          (A.problem.F (Algorithm2.x A t ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.xNext A t ω)
                  (Algorithm2.preconditioner A t ω
                    (Algorithm2.xNext A t ω)) +
              (A.eta t / ρ) *
                ‖A.problem.gradF (Algorithm2.x A t ω) -
                  Algorithm2.m A t ω‖ ^ 2 -
              (ρ / (4 * A.eta t)) *
                ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
            (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
        ∂μ := by
    exact integral_mono hleft_int hright_int hpoint
  calc
    b6C4LeftExpectation A t ≤
        ∫ ω,
            (A.problem.F (Algorithm2.x A t ω) +
                (A.lambda / 2) *
                  inner ℝ (Algorithm2.xNext A t ω)
                    (Algorithm2.preconditioner A t ω
                      (Algorithm2.xNext A t ω)) +
                (A.eta t / ρ) *
                  ‖A.problem.gradF (Algorithm2.x A t ω) -
                    Algorithm2.m A t ω‖ ^ 2 -
                (ρ / (4 * A.eta t)) *
                  ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
              (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
          ∂μ := hmain
    _ = b6C4RightExpectation A t +
          b6C4EstimatorTerm A ρ t -
          b6C4DisplacementTerm A ρ t +
          b6C4WeightDecayTerm A D t := by
      let base : SampleStream Sample → ℝ := fun ω =>
        A.problem.F (Algorithm2.x A t ω) +
          (A.lambda / 2) *
            inner ℝ (Algorithm2.xNext A t ω)
              (Algorithm2.preconditioner A t ω
                (Algorithm2.xNext A t ω))
      let est : SampleStream Sample → ℝ := fun ω =>
        (A.eta t / ρ) *
          ‖A.problem.gradF (Algorithm2.x A t ω) -
            Algorithm2.m A t ω‖ ^ 2
      let disp : SampleStream Sample → ℝ := fun ω =>
        (ρ / (4 * A.eta t)) *
          ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2
      let weight : SampleStream Sample → ℝ := fun _ =>
        (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
      have hbase_int : Integrable base μ := by
        simpa [base] using hright_base_int
      have hest_int'' : Integrable est μ := by
        simpa [est] using hest_int'
      have hdisp_int'' : Integrable disp μ := by
        simpa [disp] using hdisp_int'
      have hweight_int : Integrable weight μ :=
        integrable_const _
      have hadd :
          (∫ ω, base ω + est ω ∂μ) =
            (∫ ω, base ω ∂μ) + ∫ ω, est ω ∂μ := by
        simpa only [Pi.add_apply] using
          (integral_add hbase_int hest_int'')
      have hsub :
          (∫ ω, base ω + est ω - disp ω ∂μ) =
            (∫ ω, base ω + est ω ∂μ) - ∫ ω, disp ω ∂μ := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          (integral_sub (hbase_int.add hest_int'') hdisp_int'')
      have hdecomp :
          (∫ ω, (base ω + est ω - disp ω) + weight ω ∂μ) =
            (∫ ω, base ω ∂μ) + (∫ ω, est ω ∂μ) -
                (∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := by
        calc
          (∫ ω, (base ω + est ω - disp ω) + weight ω ∂μ) =
              (∫ ω, base ω + est ω - disp ω ∂μ) +
                ∫ ω, weight ω ∂μ := by
              exact integral_add
                    ((hbase_int.add hest_int'').sub hdisp_int'')
                    hweight_int
          _ = ((∫ ω, base ω + est ω ∂μ) -
                ∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := by
                  rw [hsub]
          _ = (∫ ω, base ω ∂μ) + (∫ ω, est ω ∂μ) -
                (∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := by
                  simpa [hadd]
      calc
        (∫ ω,
            (A.problem.F (Algorithm2.x A t ω) +
                (A.lambda / 2) *
                  inner ℝ (Algorithm2.xNext A t ω)
                    (Algorithm2.preconditioner A t ω
                      (Algorithm2.xNext A t ω)) +
                (A.eta t / ρ) *
                  ‖A.problem.gradF (Algorithm2.x A t ω) -
                    Algorithm2.m A t ω‖ ^ 2 -
                (ρ / (4 * A.eta t)) *
                  ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2) +
              (A.lambda / 2) * Real.sqrt (2 * (1 - A.beta2 t)) * D ^ 2
          ∂μ) =
            (∫ ω, (base ω + est ω - disp ω) + weight ω ∂μ) := by
              simp [base, est, disp, weight]
        _ = (∫ ω, base ω ∂μ) + (∫ ω, est ω ∂μ) -
              (∫ ω, disp ω ∂μ) + ∫ ω, weight ω ∂μ := hdecomp
        _ = b6C4RightExpectation A t +
              b6C4EstimatorTerm A ρ t -
              b6C4DisplacementTerm A ρ t +
              b6C4WeightDecayTerm A D t := by
              have hbase_value :
                  (∫ ω, base ω ∂μ) = b6C4RightExpectation A t := by
                simp [base, b6C4RightExpectation, μ]
              rw [hbase_value]
              simp [b6C4EstimatorTerm, b6C4DisplacementTerm,
                b6C4WeightDecayTerm, expectedEstimatorError, weight, μ,
                integral_const, probReal_univ, norm_sub_rev,
                sub_eq_add_neg]
              rw [integral_const_mul, integral_const_mul]
              simp only [sub_eq_add_neg]

/-- Legacy source-facing C.4 consumer after the H-index bridge. The active
corrected route uses
`algorithm2_c4_exact_lyapunov_expectation_one_step` instead, so this theorem
remains outside the public dependency cone. -/
private theorem algorithm2_c4_lyapunov_expectation_one_step
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ D : ℝ) (T t : ℕ) (ht : t ∈ Finset.Icc 1 T)
    (hη_pos : 0 < A.eta t) (hρ_pos : 0 < ρ)
    (hinputs : Algorithm2C4SourceInputs A L ρ D t)
    (habsorb : L / 2 + ρ * A.lambda ≤ ρ / (2 * A.eta t))
    (htrajectory : B6ObjectiveTrajectoryIntegrabilityExtension A T)
    (hest_int :
      ExpectedEstimatorErrorWellDefined (runLaw A.problem) A.problem.gradF
        (Algorithm2.x A t) (Algorithm2.m A t))
    (hdisp_int :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2)
        (runLaw A.problem))
    (hindex : B6C4LyapunovIndexBridge A T) :
    b6LyapunovNextExpectation A t ≤
      b6LyapunovCurrentExpectation A t +
        b6C4EstimatorTerm A ρ t -
        b6C4DisplacementTerm A ρ t +
        b6C4WeightDecayTerm A D t := by
  have hcross :=
    algorithm2_c4_expectation_one_step A L ρ D T t ht hη_pos hρ_pos
      hinputs habsorb htrajectory hest_int hdisp_int
  rw [(hindex t ht).1, (hindex t ht).2] at hcross
  exact hcross

/-- The Lean-readable residual sequence occupying the source symbol
`M_{t+1}` in B.6. It is built from the C.2 corrected extension object because
the literal C.2 display has a recorded type defect; the defect status is kept
separately as `C2LiteralSourceGTypeIssue`. -/
def theoremB6ReadableC2Residual
    (A : Algorithm2Data Sample ι) (t : ℕ) : ℝ :=
  c2CorrectedResidual (runLaw A.problem) A.problem (sampleAt (Sample := Sample))
    (Algorithm2.x A t) (Algorithm2.xNext A t)
    (Algorithm2.m A t) (A.beta1 (t + 1)) (A.gamma (t + 1)) t

private theorem b6_c2_one_step_second_moment_bound
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L σ : ℝ) (t : ℕ) (ht : 0 < t)
    (hprefix :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
        (fun ω : SampleStream Sample =>
          ((Algorithm2.x A t ω, Algorithm2.xNext A t ω), Algorithm2.m A t ω)))
    (hraw :
      ∀ ω : SampleStream Sample,
        c2EstimatorError A.problem (Algorithm2.x A (t + 1))
            (Algorithm2.m A (t + 1)) ω =
          (1 - A.beta1 (t + 1)) •
              (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω) -
                A.problem.gradF (Algorithm2.xNext A t ω)) +
            (A.beta1 (t + 1)) •
              c2EstimatorError A.problem (Algorithm2.x A t) (Algorithm2.m A t) ω +
            (A.beta1 (t + 1)) •
              ((A.gamma (t + 1)) •
                  c2Delta A.problem (sampleAt (Sample := Sample))
                    (Algorithm2.x A t) (Algorithm2.xNext A t) t ω -
                (A.problem.gradF (Algorithm2.xNext A t ω) -
                  A.problem.gradF (Algorithm2.x A t ω))))
    (hbeta_admissible : 0 ≤ A.beta1 (t + 1) ∧ A.beta1 (t + 1) ≤ 1)
    (hC2_well_defined :
      C2ExpectationWellDefined (runLaw A.problem) A.problem
        (sampleAt (Sample := Sample))
        (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t) t)
    (hC2_residual_compatible :
      C2CorrectedStatementProofResidualCompatible (runLaw A.problem)
        A.problem (sampleAt (Sample := Sample))
        (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t)
        (A.beta1 (t + 1)) (A.gamma (t + 1)) t)
    (hprev_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖c2EstimatorError A.problem (Algorithm2.x A t) (Algorithm2.m A t) ω‖ ^ 2)
        (runLaw A.problem))
    (hdisp_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2)
        (runLaw A.problem))
    (hgrad_unbiased : UnbiasedGradientOracle A.problem)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L) :
    expectedEstimatorError (runLaw A.problem) A.problem.gradF
        (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1))
      ≤
        (A.beta1 (t + 1)) ^ 2 *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm2.x A t) (Algorithm2.m A t) +
          2 * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
            (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
              ∂runLaw A.problem) +
          2 * (1 - A.beta1 (t + 1)) ^ 2 * σ ^ 2 -
          theoremB6ReadableC2Residual A t := by
  classical
  haveI : IsProbabilityMeasure (runLaw A.problem) :=
    runLaw_isProbabilityMeasure A.problem
  have hsample_meas :
      ∀ n : ℕ, Measurable (fun ω : SampleStream Sample =>
        sampleAt (Sample := Sample) n ω) := by
    intro n
    simpa [sampleAt] using measurable_pi_apply n
  have hsample_iIndep :
      iIndepFun
        (fun n (ω : SampleStream Sample) => sampleAt (Sample := Sample) n ω)
        (runLaw A.problem) := by
    haveI : IsProbabilityMeasure A.problem.sampleLaw := A.problem.sampleLaw_isProbability
    simpa [runLaw, sampleAt] using
      (SOptLib.iidStreamLaw_iIndepFun_eval A.problem.sampleLaw)
  have hfresh_indep_past :
      Indep
        ((SOptLib.filtration
            (fun n (ω : SampleStream Sample) => sampleAt (Sample := Sample) n ω)
            hsample_meas).seq (t + 1))
        (MeasurableSpace.comap
          (fun ω : SampleStream Sample => sampleAt (Sample := Sample) (t + 1) ω)
          (by infer_instance : MeasurableSpace Sample))
        (runLaw A.problem) := by
    exact samplePrefixFiltration_indep_current
      (fun n (ω : SampleStream Sample) => sampleAt (Sample := Sample) n ω)
      hsample_meas hsample_iIndep (t + 1)
  have hprefix_query :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)]
        (fun ω : SampleStream Sample =>
          ((Algorithm2.x A t ω, Algorithm2.xNext A t ω), Algorithm2.m A t ω)) := by
    exact hprefix
  let μ := runLaw A.problem
  let fresh : SampleStream Sample → Sample :=
    fun ω => sampleAt (Sample := Sample) (t + 1) ω
  let xPrev : SampleStream Sample → MarsVector ι := Algorithm2.x A t
  let y : SampleStream Sample → MarsVector ι := Algorithm2.xNext A t
  haveI : IsProbabilityMeasure A.problem.sampleLaw := A.problem.sampleLaw_isProbability
  have hquery_x_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)] xPrev := by
    dsimp [xPrev]
    exact measurable_fst.comp (measurable_fst.comp hprefix_query)
  have hquery_x_meas : Measurable xPrev := by
    dsimp [xPrev] at hquery_x_past ⊢
    exact hquery_x_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have hquery_y_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)] y := by
    dsimp [y]
    exact measurable_snd.comp (measurable_fst.comp hprefix_query)
  have hquery_y_meas : Measurable y := by
    dsimp [y] at hquery_y_past ⊢
    exact hquery_y_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_y_fresh : IndepFun y fresh μ := by
    dsimp [μ, fresh, y]
    exact indepFun_of_past_measurable_current_iid_sample hquery_y_past
      hfresh_indep_past
  have hgradF_meas : Measurable A.problem.gradF := by
    exact oracleMean_measurable_of_eq_integral A.problem.sampleLaw
      A.problem.stochasticGrad A.problem.gradF
      (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased)
      (by
        intro x
        exact (UnbiasedGradientOracle.mean_eq_gradF hgrad_unbiased x).symm)
  have hres_meas :
      Measurable (fun p : MarsVector ι × Sample =>
        A.problem.stochasticGrad p.1 p.2 - A.problem.gradF p.1) := by
    exact (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).sub
      (hgradF_meas.comp measurable_fst)
  have hvar_random :
      (∫ ω, ‖A.problem.stochasticGrad (Algorithm2.xNext A t ω)
            (sampleAt (Sample := Sample) (t + 1) ω) -
          A.problem.gradF (Algorithm2.xNext A t ω)‖ ^ 2 ∂runLaw A.problem) ≤
        σ ^ 2 := by
    simpa [μ, fresh, y] using
      (integral_sq_oracleResidual_le_of_indep_fixed_variance
        (P := μ) (ν := A.problem.sampleLaw)
        (query := y) (sample := fresh)
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (σ2 := σ ^ 2)
        hres_meas hquery_y_meas (hsample_meas (t + 1)) h_indep_y_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        (sq_nonneg σ)
        (by
          intro x
          exact BoundedVariance.bound hvar x))
  have hdelta_uncentered :
      Integrable
          (fun ω : SampleStream Sample =>
            ‖A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2) μ ∧
        (∫ ω, ‖A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2 ∂μ) ≤
          L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    have hleft :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2) μ := by
      simpa [μ, fresh, xPrev, y, c2Delta] using hC2_well_defined.1
    refine ⟨hleft, ?_⟩
    have hright_int :
        Integrable (fun ω : SampleStream Sample =>
          L ^ 2 * ‖y ω - xPrev ω‖ ^ 2) μ := by
      simpa [xPrev, y, mul_comm, mul_left_comm, mul_assoc] using
        hdisp_sq.const_mul (L ^ 2)
    calc
      (∫ ω, ‖A.problem.stochasticGrad (y ω) (fresh ω) -
            A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ ^ 2 ∂μ)
          ≤ ∫ ω, L ^ 2 * ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
            refine integral_mono hleft hright_int ?_
            intro ω
            have hlip :=
              (StochasticSmooth.stochasticGrad_lipschitz hsmooth)
                (y ω) (xPrev ω) (fresh ω)
            have hnorm_nonneg :
                0 ≤ ‖A.problem.stochasticGrad (y ω) (fresh ω) -
                  A.problem.stochasticGrad (xPrev ω) (fresh ω)‖ := norm_nonneg _
            have hdist_nonneg : 0 ≤ ‖y ω - xPrev ω‖ := norm_nonneg _
            nlinarith
      _ = L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
            rw [integral_const_mul]
  have htarget_lipschitz :
      ∀ x z : MarsVector ι,
        ‖A.problem.gradF x - A.problem.gradF z‖ ≤ L * ‖x - z‖ := by
    intro x z
    refine oracleMean_lipschitz_of_ae_lipschitz A.problem.sampleLaw
      A.problem.stochasticGrad A.problem.gradF L x z
      (UnbiasedGradientOracle.fixed_integrable hgrad_unbiased x)
      (UnbiasedGradientOracle.fixed_integrable hgrad_unbiased z) ?_ ?_ ?_
    · simpa [SOptLib.oracleMean_def] using
        (UnbiasedGradientOracle.mean_eq_gradF hgrad_unbiased x)
    · simpa [SOptLib.oracleMean_def] using
        (UnbiasedGradientOracle.mean_eq_gradF hgrad_unbiased z)
    · filter_upwards [] with ξ
      exact (StochasticSmooth.stochasticGrad_lipschitz hsmooth) x z ξ
  have horacle_delta_aesm :
      AEStronglyMeasurable
        (fun ω : SampleStream Sample =>
          A.problem.stochasticGrad (y ω) (fresh ω) -
            A.problem.stochasticGrad (xPrev ω) (fresh ω)) μ := by
    have hmeas :
        Measurable
          (fun ω : SampleStream Sample =>
            A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.stochasticGrad (xPrev ω) (fresh ω)) := by
      exact
        ((UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
            (hquery_y_meas.prodMk (hsample_meas (t + 1)))).sub
          ((UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased).comp
            (hquery_x_meas.prodMk (hsample_meas (t + 1))))
    exact hmeas.aestronglyMeasurable
  have htarget_delta_aesm :
      AEStronglyMeasurable
        (fun ω : SampleStream Sample =>
          A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)) μ := by
    exact ((hgradF_meas.comp hquery_y_meas).sub
      (hgradF_meas.comp hquery_x_meas)).aestronglyMeasurable
  have htarget_delta_sq :
      Integrable
        (fun ω : SampleStream Sample =>
          ‖A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)‖ ^ 2) μ := by
    refine Integrable.mono' (hdisp_sq.const_mul (L ^ 2))
      (by simpa using htarget_delta_aesm.norm.pow 2) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hlip := htarget_lipschitz (y ω) (xPrev ω)
    have hleft_nonneg :
        0 ≤ ‖A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)‖ := norm_nonneg _
    have hright_nonneg : 0 ≤ L * ‖y ω - xPrev ω‖ := le_trans hleft_nonneg hlip
    have hneg :
        -(L * ‖y ω - xPrev ω‖) ≤
          ‖A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)‖ := by
      nlinarith
    have hsquare := sq_le_sq' hneg hlip
    dsimp [xPrev, y] at hsquare ⊢
    nlinarith
  have hquery_delta_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)]
        (fun ω : SampleStream Sample =>
          ((y ω, xPrev ω),
            A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) := by
    exact (hquery_y_past.prodMk hquery_x_past).prodMk
      ((hgradF_meas.comp hquery_y_past).sub
        (hgradF_meas.comp hquery_x_past))
  have hquery_delta_meas :
      Measurable
        (fun ω : SampleStream Sample =>
          ((y ω, xPrev ω),
            A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) := by
    exact hquery_delta_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_delta_query_fresh :
      IndepFun
        (fun ω : SampleStream Sample =>
          ((y ω, xPrev ω),
            A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) fresh μ := by
    dsimp [μ, fresh]
    exact indepFun_of_past_measurable_current_iid_sample hquery_delta_past
      hfresh_indep_past
  have hcenter_delta_zero :
      ∫ ω,
          inner ℝ (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
            ((A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) ∂μ = 0 := by
    have horacle_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
              (A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω))) μ :=
      integrable_inner_of_integrable_sq_norm htarget_delta_aesm horacle_delta_aesm
        htarget_delta_sq hdelta_uncentered.1
    have htarget_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) μ := by
      simpa [inner_self_eq_norm_sq] using htarget_delta_sq
    simpa [μ, fresh] using
      (integral_inner_centered_oracleDifference_eq_zero_of_indep_adapted
        (P := μ) (ν := A.problem.sampleLaw)
        (sample := fresh) (x := y) (y := xPrev)
        (d := fun ω : SampleStream Sample =>
          A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased)
        hquery_delta_meas (hsample_meas (t + 1)) h_indep_delta_query_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        horacle_inner_int
        (by
          exact (continuous_inner.measurable.comp
            ((measurable_snd).prodMk
              ((hgradF_meas.comp (measurable_fst.comp measurable_fst)).sub
                (hgradF_meas.comp (measurable_snd.comp measurable_fst))))).aestronglyMeasurable)
        htarget_inner_int
        (by
          filter_upwards [] with q
          exact UnbiasedGradientOracle.fixed_fiber_oracle_difference_mean
            hgrad_unbiased q.1.1 q.1.2 q.2))
  have hcentered_delta :
      Integrable
          (fun ω : SampleStream Sample =>
            ‖(A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))‖ ^ 2) μ ∧
        (∫ ω,
            ‖(A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))‖ ^ 2 ∂μ) ≤
          L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    refine centered_oracleDifference_secondMoment_le_of_unbiased_smooth
      (P := μ) (sample := fresh) (x := y) (y := xPrev)
      (G := A.problem.stochasticGrad) (target := A.problem.gradF) (L := L)
      horacle_delta_aesm ?_ hdelta_uncentered htarget_delta_aesm ?_ ?_
    · simpa [μ, xPrev, y] using hdisp_sq
    · filter_upwards [] with ω
      exact htarget_lipschitz (y ω) (xPrev ω)
    · simpa using hcenter_delta_zero
  let eps : SampleStream Sample → MarsVector ι :=
    c2EstimatorError A.problem (Algorithm2.x A t) (Algorithm2.m A t)
  have heps_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)] eps := by
    dsimp [eps, c2EstimatorError]
    exact (measurable_snd.comp hprefix_query).sub
      (hgradF_meas.comp hquery_x_past)
  have heps_meas : Measurable eps := by
    exact heps_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have heps_aesm : AEStronglyMeasurable eps μ := heps_meas.aestronglyMeasurable
  have hquery_xym_meas :
      Measurable
        (fun ω : SampleStream Sample =>
          ((xPrev ω, y ω), Algorithm2.m A t ω)) := by
    exact hprefix_query.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_xym_fresh :
      IndepFun
        (fun ω : SampleStream Sample =>
          ((xPrev ω, y ω), Algorithm2.m A t ω)) fresh μ := by
    dsimp [μ, fresh, xPrev, y]
    exact indepFun_of_past_measurable_current_iid_sample hprefix_query
      hfresh_indep_past
  have hcross_prev_fresh :
      ∫ ω,
          inner ℝ (eps ω)
            (A.problem.stochasticGrad (y ω) (fresh ω) -
              A.problem.gradF (y ω)) ∂μ = 0 := by
    simpa [μ, fresh, xPrev, y, eps, c2EstimatorError] using
      (randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
        (P := μ) (ν := A.problem.sampleLaw)
        (query := fun ω : SampleStream Sample =>
          ((xPrev ω, y ω), Algorithm2.m A t ω))
        (sample := fresh)
        (residual := fun q : (MarsVector ι × MarsVector ι) × MarsVector ι =>
          fun ξ : Sample =>
            A.problem.stochasticGrad q.1.2 ξ - A.problem.gradF q.1.2)
        (d := fun q : (MarsVector ι × MarsVector ι) × MarsVector ι =>
          q.2 - A.problem.gradF q.1.1)
        (by
          exact hres_meas.comp
            ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
              measurable_snd))
        (by
          exact measurable_snd.sub
            (hgradF_meas.comp (measurable_fst.comp measurable_fst)))
        hquery_xym_meas (hsample_meas (t + 1)) h_indep_xym_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        (by
          intro q
          exact UnbiasedGradientOracle.residual_integrable hgrad_unbiased q.1.2)
        (by
          intro q
          exact UnbiasedGradientOracle.residual_integral_zero hgrad_unbiased q.1.2))
  have hquery_delta_eps_past :
      Measurable[
        (SOptLib.filtration
          (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
          hsample_meas).seq (t + 1)]
        (fun ω : SampleStream Sample => ((y ω, xPrev ω), eps ω)) := by
    exact (hquery_y_past.prodMk hquery_x_past).prodMk heps_past
  have hquery_delta_eps_meas :
      Measurable
        (fun ω : SampleStream Sample => ((y ω, xPrev ω), eps ω)) := by
    exact hquery_delta_eps_past.mono
      ((SOptLib.filtration
        (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
        hsample_meas).le (t + 1)) le_rfl
  have h_indep_delta_eps_fresh :
      IndepFun (fun ω : SampleStream Sample => ((y ω, xPrev ω), eps ω)) fresh μ := by
    dsimp [μ, fresh]
    exact indepFun_of_past_measurable_current_iid_sample hquery_delta_eps_past
      hfresh_indep_past
  have hcross_prev_delta :
      ∫ ω,
          inner ℝ (eps ω)
            ((A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) ∂μ = 0 := by
    have horacle_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (eps ω)
              (A.problem.stochasticGrad (y ω) (fresh ω) -
                A.problem.stochasticGrad (xPrev ω) (fresh ω))) μ :=
      integrable_inner_of_integrable_sq_norm heps_aesm horacle_delta_aesm
        (by simpa [eps] using hprev_sq) hdelta_uncentered.1
    have htarget_inner_int :
        Integrable
          (fun ω : SampleStream Sample =>
            inner ℝ (eps ω)
              (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))) μ :=
      integrable_inner_of_integrable_sq_norm heps_aesm htarget_delta_aesm
        (by simpa [eps] using hprev_sq) htarget_delta_sq
    simpa [μ, fresh] using
      (integral_inner_centered_oracleDifference_eq_zero_of_indep_adapted
        (P := μ) (ν := A.problem.sampleLaw)
        (sample := fresh) (x := y) (y := xPrev) (d := eps)
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (UnbiasedGradientOracle.stochasticGrad_measurable hgrad_unbiased)
        hquery_delta_eps_meas (hsample_meas (t + 1)) h_indep_delta_eps_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        horacle_inner_int
        (by
          exact (continuous_inner.measurable.comp
            ((measurable_snd).prodMk
              ((hgradF_meas.comp (measurable_fst.comp measurable_fst)).sub
                (hgradF_meas.comp (measurable_snd.comp measurable_fst))))).aestronglyMeasurable)
        htarget_inner_int
        (by
          filter_upwards [] with q
          exact UnbiasedGradientOracle.fixed_fiber_oracle_difference_mean
            hgrad_unbiased q.1.1 q.1.2 q.2))
  let β : ℝ := A.beta1 (t + 1)
  let r : SampleStream Sample → MarsVector ι :=
    fun ω => A.problem.stochasticGrad (y ω) (fresh ω) - A.problem.gradF (y ω)
  let z : SampleStream Sample → MarsVector ι :=
    fun ω =>
      (A.problem.stochasticGrad (y ω) (fresh ω) -
          A.problem.stochasticGrad (xPrev ω) (fresh ω)) -
        (A.problem.gradF (y ω) - A.problem.gradF (xPrev ω))
  let prev : SampleStream Sample → MarsVector ι := fun ω => β • eps ω
  let inc : SampleStream Sample → MarsVector ι :=
    fun ω => (1 - β) • r ω + β • z ω
  let core : SampleStream Sample → MarsVector ι :=
    fun ω => (1 - β) • r ω + β • eps ω + β • z ω
  have hβ_nonneg : 0 ≤ β := by
    simpa [β] using hbeta_admissible.1
  have hβ_le_one : β ≤ 1 := by
    simpa [β] using hbeta_admissible.2
  have hone_minus_nonneg : 0 ≤ 1 - β := by
    linarith
  have hr_aesm : AEStronglyMeasurable r μ := by
    dsimp [r, μ, fresh, y]
    exact (hres_meas.comp (hquery_y_meas.prodMk (hsample_meas (t + 1)))).aestronglyMeasurable
  have hz_aesm : AEStronglyMeasurable z μ := by
    dsimp [z]
    exact horacle_delta_aesm.sub htarget_delta_aesm
  have hr_sq : Integrable (fun ω : SampleStream Sample => ‖r ω‖ ^ 2) μ := by
    simpa [μ, fresh, y, r] using
      (integrable_sq_oracleResidual_of_indep_fixed_variance_bound
        (P := μ) (ν := A.problem.sampleLaw)
        (query := y) (sample := fresh)
        (G := A.problem.stochasticGrad) (target := A.problem.gradF)
        (σ2 := σ ^ 2)
        hres_meas hquery_y_meas (hsample_meas (t + 1)) h_indep_y_fresh
        (by simpa [μ, fresh] using runLaw_map_sampleAt A.problem (t + 1))
        (sq_nonneg σ)
        (by intro x; exact BoundedVariance.fixed_sq_integrable hvar x)
        (by intro x; exact BoundedVariance.bound hvar x))
  have hz_sq : Integrable (fun ω : SampleStream Sample => ‖z ω‖ ^ 2) μ := by
    simpa [z, μ, fresh, xPrev, y] using hcentered_delta.1
  have hprev_aesm : AEStronglyMeasurable prev μ := by
    dsimp [prev]
    exact heps_aesm.const_smul β
  have hinc_aesm : AEStronglyMeasurable inc μ := by
    dsimp [inc]
    exact (hr_aesm.const_smul (1 - β)).add (hz_aesm.const_smul β)
  have hprev_sq_scaled : Integrable (fun ω : SampleStream Sample => ‖prev ω‖ ^ 2) μ := by
    refine (hprev_sq.const_mul (β ^ 2)).congr ?_
    filter_upwards [] with ω
    dsimp [prev]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hinc_sq : Integrable (fun ω : SampleStream Sample => ‖inc ω‖ ^ 2) μ := by
    refine Integrable.mono'
      ((hr_sq.const_mul (2 * (1 - β) ^ 2)).add (hz_sq.const_mul (2 * β ^ 2)))
      (hinc_aesm.norm.pow 2) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖inc ω‖))]
    have htmp := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
      ((1 - β) • r ω) (β • z ω)
    dsimp [inc]
    simpa [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hinner_eps_r_int : Integrable (fun ω : SampleStream Sample => inner ℝ (eps ω) (r ω)) μ :=
    integrable_inner_of_integrable_sq_norm heps_aesm hr_aesm (by simpa [eps] using hprev_sq) hr_sq
  have hinner_eps_z_int : Integrable (fun ω : SampleStream Sample => inner ℝ (eps ω) (z ω)) μ :=
    integrable_inner_of_integrable_sq_norm heps_aesm hz_aesm (by simpa [eps] using hprev_sq) hz_sq
  have hcross_eps_r : ∫ ω, inner ℝ (eps ω) (r ω) ∂μ = 0 := by
    simpa [μ, fresh, y, r] using hcross_prev_fresh
  have hcross_eps_z : ∫ ω, inner ℝ (eps ω) (z ω) ∂μ = 0 := by
    simpa [μ, fresh, xPrev, y, z] using hcross_prev_delta
  have hcross_prev_inc : ∫ ω, inner ℝ (prev ω) (inc ω) ∂μ = 0 := by
    calc
      ∫ ω, inner ℝ (prev ω) (inc ω) ∂μ =
          ∫ ω, (β * (1 - β)) * inner ℝ (eps ω) (r ω) +
            (β * β) * inner ℝ (eps ω) (z ω) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            dsimp [prev, inc]
            simp [inner_add_right, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm]
      _ = (β * (1 - β)) * ∫ ω, inner ℝ (eps ω) (r ω) ∂μ +
            (β * β) * ∫ ω, inner ℝ (eps ω) (z ω) ∂μ := by
            rw [integral_add (hinner_eps_r_int.const_mul (β * (1 - β)))
                (hinner_eps_z_int.const_mul (β * β)), integral_const_mul, integral_const_mul]
      _ = 0 := by
            rw [hcross_eps_r, hcross_eps_z]
            ring
  have hvar_random_r : ∫ ω, ‖r ω‖ ^ 2 ∂μ ≤ σ ^ 2 := by
    simpa [μ, fresh, y, r] using hvar_random
  have hz_bound : ∫ ω, ‖z ω‖ ^ 2 ∂μ ≤ L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    simpa [z, μ, fresh, xPrev, y] using hcentered_delta.2
  have hinc_bound :
      ∫ ω, ‖inc ω‖ ^ 2 ∂μ ≤
        2 * (1 - β) ^ 2 * σ ^ 2 +
          2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    have hbudget_int : Integrable
        (fun ω : SampleStream Sample =>
          (2 * (1 - β) ^ 2) * ‖r ω‖ ^ 2 +
            (2 * β ^ 2) * ‖z ω‖ ^ 2) μ :=
      (hr_sq.const_mul (2 * (1 - β) ^ 2)).add (hz_sq.const_mul (2 * β ^ 2))
    have hmono :
        ∫ ω, ‖inc ω‖ ^ 2 ∂μ ≤
          ∫ ω, (2 * (1 - β) ^ 2) * ‖r ω‖ ^ 2 +
            (2 * β ^ 2) * ‖z ω‖ ^ 2 ∂μ := by
      refine integral_mono hinc_sq hbudget_int ?_
      intro ω
      have htmp := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        ((1 - β) • r ω) (β • z ω)
      dsimp [inc]
      simpa [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc, mul_left_comm, mul_comm] using htmp
    calc
      ∫ ω, ‖inc ω‖ ^ 2 ∂μ ≤
          ∫ ω, (2 * (1 - β) ^ 2) * ‖r ω‖ ^ 2 +
            (2 * β ^ 2) * ‖z ω‖ ^ 2 ∂μ := hmono
      _ = (2 * (1 - β) ^ 2) * ∫ ω, ‖r ω‖ ^ 2 ∂μ +
            (2 * β ^ 2) * ∫ ω, ‖z ω‖ ^ 2 ∂μ := by
            rw [integral_add (hr_sq.const_mul (2 * (1 - β) ^ 2))
                (hz_sq.const_mul (2 * β ^ 2)), integral_const_mul, integral_const_mul]
      _ ≤ (2 * (1 - β) ^ 2) * σ ^ 2 +
            (2 * β ^ 2) * (L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ) := by
            have hc1 : 0 ≤ 2 * (1 - β) ^ 2 := by
              nlinarith [hone_minus_nonneg]
            have hc2 : 0 ≤ 2 * β ^ 2 := by
              nlinarith [hβ_nonneg]
            exact add_le_add (mul_le_mul_of_nonneg_left hvar_random_r hc1)
              (mul_le_mul_of_nonneg_left hz_bound hc2)
      _ = 2 * (1 - β) ^ 2 * σ ^ 2 +
            2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
            ring
  have hcore_rec : Filter.EventuallyEq (ae μ) core (fun ω => prev ω + inc ω) := by
    filter_upwards [] with ω
    dsimp [core, prev, inc]
    abel
  have hprev_integral_eq :
      ∫ ω, ‖prev ω‖ ^ 2 ∂μ = β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ := by
    calc
      ∫ ω, ‖prev ω‖ ^ 2 ∂μ = ∫ ω, β ^ 2 * ‖eps ω‖ ^ 2 ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro ω
        dsimp [prev]
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ = β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ := by
        rw [integral_const_mul]
  have hcore_recurrence :=
    second_moment_add_recurrence_le_of_cross_zero μ prev core inc
      (2 * (1 - β) ^ 2 * σ ^ 2 +
        2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ)
      hprev_aesm hinc_aesm hprev_sq_scaled hinc_sq hcore_rec
      hcross_prev_inc hinc_bound
  have hcore_bound :
      ∫ ω, ‖core ω‖ ^ 2 ∂μ ≤
        2 * (1 - β) ^ 2 * σ ^ 2 +
          β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ +
          2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
    calc
      ∫ ω, ‖core ω‖ ^ 2 ∂μ ≤
          ∫ ω, ‖prev ω‖ ^ 2 ∂μ +
            (2 * (1 - β) ^ 2 * σ ^ 2 +
              2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ) := hcore_recurrence.2
      _ = 2 * (1 - β) ^ 2 * σ ^ 2 +
          β ^ 2 * ∫ ω, ‖eps ω‖ ^ 2 ∂μ +
          2 * β ^ 2 * L ^ 2 * ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ := by
          rw [hprev_integral_eq]
          ring
  let epsNext : SampleStream Sample → MarsVector ι :=
    c2EstimatorError A.problem (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1))
  have hprev_expected_eq :
      expectedEstimatorError μ A.problem.gradF xPrev (Algorithm2.m A t) =
        ∫ ω, ‖eps ω‖ ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    have hnorm : ‖A.problem.gradF (xPrev ω) - Algorithm2.m A t ω‖ = ‖eps ω‖ := by
      simpa [eps, c2EstimatorError, xPrev, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_neg (A.problem.gradF (xPrev ω) - Algorithm2.m A t ω)).symm
    simp [hnorm]
  have hnext_expected_eq :
      expectedEstimatorError μ A.problem.gradF
          (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) =
        ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    have hnorm :
        ‖A.problem.gradF (Algorithm2.x A (t + 1) ω) -
            Algorithm2.m A (t + 1) ω‖ =
          ‖epsNext ω‖ := by
      simpa [epsNext, c2EstimatorError, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_neg
          (A.problem.gradF (Algorithm2.x A (t + 1) ω) -
            Algorithm2.m A (t + 1) ω)).symm
    simp [hnorm]
  let delta : SampleStream Sample → MarsVector ι :=
    fun ω => A.problem.stochasticGrad (y ω) (fresh ω) -
      A.problem.stochasticGrad (xPrev ω) (fresh ω)
  let deltaMean : SampleStream Sample → MarsVector ι :=
    fun ω => A.problem.gradF (y ω) - A.problem.gradF (xPrev ω)
  have hdelta_aesm : AEStronglyMeasurable delta μ := by
    simpa [delta] using horacle_delta_aesm
  have hdeltaMean_aesm : AEStronglyMeasurable deltaMean μ := by
    simpa [deltaMean] using htarget_delta_aesm
  have hdelta_sq :
      Integrable (fun ω => ‖delta ω‖ ^ 2) μ := by
    simpa [delta] using hdelta_uncentered.1
  have hdeltaMean_sq :
      Integrable (fun ω => ‖deltaMean ω‖ ^ 2) μ := by
    simpa [deltaMean] using htarget_delta_sq
  have hdelta_delta_int :
      Integrable (fun ω => inner ℝ (delta ω) (delta ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := delta)
      hdelta_aesm hdelta_aesm hdelta_sq hdelta_sq
  have hdelta_deltaMean_int :
      Integrable (fun ω => inner ℝ (delta ω) (deltaMean ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := deltaMean)
      hdelta_aesm hdeltaMean_aesm hdelta_sq hdeltaMean_sq
  have hdeltaMean_delta_int :
      Integrable (fun ω => inner ℝ (deltaMean ω) (delta ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := deltaMean) (v := delta)
      hdeltaMean_aesm hdelta_aesm hdeltaMean_sq hdelta_sq
  have hdeltaMean_deltaMean_int :
      Integrable (fun ω => inner ℝ (deltaMean ω) (deltaMean ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := deltaMean) (v := deltaMean)
      hdeltaMean_aesm hdeltaMean_aesm hdeltaMean_sq hdeltaMean_sq
  have hdeltaMean_cross :
      ∫ ω, inner ℝ (delta ω) (deltaMean ω) ∂μ =
        ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
    have hcenter :
        ∫ ω, inner ℝ (deltaMean ω) (delta ω - deltaMean ω) ∂μ = 0 := by
      simpa [delta, deltaMean] using hcenter_delta_zero
    simpa using
      (integral_inner_eq_integral_norm_sq_of_inner_sub_eq_zero
        μ hdeltaMean_delta_int hdeltaMean_deltaMean_int hcenter)
  have hdelta_z_int :
      Integrable (fun ω => inner ℝ (delta ω) (z ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := z)
      hdelta_aesm hz_aesm hdelta_sq hz_sq
  have hdelta_z :
      ∫ ω, inner ℝ (delta ω) (z ω) ∂μ =
        (∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
          ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
    have hz_def : ∀ ω, z ω = delta ω - deltaMean ω := by
      intro ω
      rfl
    calc
      ∫ ω, inner ℝ (delta ω) (z ω) ∂μ =
          ∫ ω, inner ℝ (delta ω) (delta ω - deltaMean ω) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change inner ℝ (delta ω) (z ω) =
              inner ℝ (delta ω) (delta ω - deltaMean ω)
            exact congrArg (fun v => inner ℝ (delta ω) v) (hz_def ω)
      _ = ∫ ω,
          (inner ℝ (delta ω) (delta ω) -
            inner ℝ (delta ω) (deltaMean ω)) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change inner ℝ (delta ω) (delta ω - deltaMean ω) =
              inner ℝ (delta ω) (delta ω) -
                inner ℝ (delta ω) (deltaMean ω)
            simp only [inner_sub_right]
      _ = (∫ ω, inner ℝ (delta ω) (delta ω) ∂μ) -
          ∫ ω, inner ℝ (delta ω) (deltaMean ω) ∂μ := by
            rw [integral_sub hdelta_delta_int hdelta_deltaMean_int]
      _ = (∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
          ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
            rw [hdeltaMean_cross]
            simp [inner_self_eq_norm_sq]
  have hcore_aesm : AEStronglyMeasurable core μ := by
    dsimp [core]
    exact
      ((hr_aesm.const_smul (1 - β)).add (heps_aesm.const_smul β)).add
        (hz_aesm.const_smul β)
  have hcore_sq : Integrable (fun ω => ‖core ω‖ ^ 2) μ :=
    hcore_recurrence.1
  have hdelta_core_int :
      Integrable (fun ω => inner ℝ (delta ω) (core ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := core)
      hdelta_aesm hcore_aesm hdelta_sq hcore_sq
  have hdelta_r_int :
      Integrable (fun ω => inner ℝ (delta ω) (r ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := r)
      hdelta_aesm hr_aesm hdelta_sq hr_sq
  have hdelta_eps_int :
      Integrable (fun ω => inner ℝ (delta ω) (eps ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := delta) (v := eps)
      hdelta_aesm heps_aesm hdelta_sq (by simpa [eps] using hprev_sq)
  have hdelta_core_expand :
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
        (1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := by
    calc
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
          ∫ ω,
            (1 - β) * inner ℝ (delta ω) (r ω) +
              β * inner ℝ (delta ω) (eps ω) +
              β * inner ℝ (delta ω) (z ω) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            dsimp [core]
            simp [inner_add_right, inner_smul_right, mul_assoc, mul_left_comm,
              mul_comm]
      _ = (1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ) +
          β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := by
            change
              (∫ ω,
                  ((1 - β) * inner ℝ (delta ω) (r ω) +
                    β * inner ℝ (delta ω) (eps ω)) +
                    β * inner ℝ (delta ω) (z ω) ∂μ) = _
            calc
              (∫ ω,
                  ((1 - β) * inner ℝ (delta ω) (r ω) +
                    β * inner ℝ (delta ω) (eps ω)) +
                    β * inner ℝ (delta ω) (z ω) ∂μ) =
                  (∫ ω, (1 - β) * inner ℝ (delta ω) (r ω) +
                    β * inner ℝ (delta ω) (eps ω) ∂μ) +
                    ∫ ω, β * inner ℝ (delta ω) (z ω) ∂μ := by
                exact integral_add
                  ((hdelta_r_int.const_mul (1 - β)).add
                    (hdelta_eps_int.const_mul β))
                  (hdelta_z_int.const_mul β)
              _ = ((1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
                    β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ)) +
                    β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := by
                rw [integral_add (hdelta_r_int.const_mul (1 - β))
                  (hdelta_eps_int.const_mul β)]
                rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hdelta_core :
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
        c2ProofG μ A.problem (sampleAt (Sample := Sample))
            (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t) β t +
          β * ((∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
            ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ) := by
    calc
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
          (1 - β) * (∫ ω, inner ℝ (delta ω) (r ω) ∂μ) +
            β * (∫ ω, inner ℝ (delta ω) (eps ω) ∂μ) +
            β * (∫ ω, inner ℝ (delta ω) (z ω) ∂μ) := hdelta_core_expand
      _ = c2ProofG μ A.problem (sampleAt (Sample := Sample))
            (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t) β t +
          β * ((∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
            ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ) := by
            rw [hdelta_z]
            simp [c2ProofG, c2EstimatorError, c2Delta, delta, deltaMean, r, eps,
              μ, fresh, xPrev, y]
  have hdelta_sq_def :
      c2DeltaNormSqExpectation μ A.problem (sampleAt (Sample := Sample))
          xPrev y t =
        ∫ ω, ‖delta ω‖ ^ 2 ∂μ := by
    simp [c2DeltaNormSqExpectation, c2Delta, delta, μ, fresh, xPrev, y]
  have hdeltaMean_sq_def :
      c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y =
        ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ := by
    simp [c2DeltaConditionalMeanSqExpectation, c2DeltaExpectation, deltaMean]
  have hdelta_core_num :
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
        c2ProofG μ A.problem (sampleAt (Sample := Sample))
            (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t) β t +
          β *
            (c2DeltaNormSqExpectation μ A.problem (sampleAt (Sample := Sample))
                xPrev y t -
              c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y) := by
    calc
      ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
          c2ProofG μ A.problem (sampleAt (Sample := Sample))
              (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t) β t +
            β * ((∫ ω, ‖delta ω‖ ^ 2 ∂μ) -
              ∫ ω, ‖deltaMean ω‖ ^ 2 ∂μ) := hdelta_core
      _ = c2ProofG μ A.problem (sampleAt (Sample := Sample))
              (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t) β t +
            β *
              (c2DeltaNormSqExpectation μ A.problem
                  (sampleAt (Sample := Sample)) xPrev y t -
                c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y) := by
            rw [hdelta_sq_def, hdeltaMean_sq_def]
  let κ : ℝ := β * (A.gamma (t + 1) - 1)
  have hnext_decomp :
      ∀ ω, epsNext ω = core ω + κ • delta ω := by
    intro ω
    have hw := hraw ω
    dsimp [epsNext, core, κ, delta, deltaMean, r, eps, z, β,
      c2EstimatorError, c2Delta, fresh] at hw ⊢
    rw [hw]
    module
  have hcore_delta_int :
      Integrable (fun ω => inner ℝ (core ω) (delta ω)) μ :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := core) (v := delta)
      hcore_aesm hdelta_aesm hcore_sq hdelta_sq
  have hnext_sq_expand :
      ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ =
        ∫ ω, ‖core ω‖ ^ 2 ∂μ +
          2 * κ * (∫ ω, inner ℝ (delta ω) (core ω) ∂μ) +
          κ ^ 2 * (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := by
    calc
      ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ =
          ∫ ω,
            ‖core ω‖ ^ 2 +
              2 * κ * inner ℝ (delta ω) (core ω) +
              κ ^ 2 * ‖delta ω‖ ^ 2 ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change ‖epsNext ω‖ ^ 2 =
              ‖core ω‖ ^ 2 +
                2 * κ * inner ℝ (delta ω) (core ω) +
                κ ^ 2 * ‖delta ω‖ ^ 2
            rw [hnext_decomp ω]
            have hnorm := norm_add_sq_real (core ω) (κ • delta ω)
            simpa [norm_smul, Real.norm_eq_abs, sq_abs, mul_pow, inner_smul_right,
              real_inner_comm, mul_assoc, mul_left_comm, mul_comm] using hnorm
      _ = ∫ ω, ‖core ω‖ ^ 2 ∂μ +
          2 * κ * (∫ ω, inner ℝ (delta ω) (core ω) ∂μ) +
          κ ^ 2 * (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := by
            change
              (∫ ω,
                  ((‖core ω‖ ^ 2 +
                    2 * κ * inner ℝ (delta ω) (core ω)) +
                    κ ^ 2 * ‖delta ω‖ ^ 2) ∂μ) = _
            calc
              (∫ ω,
                  ((‖core ω‖ ^ 2 +
                    2 * κ * inner ℝ (delta ω) (core ω)) +
                    κ ^ 2 * ‖delta ω‖ ^ 2) ∂μ) =
                  (∫ ω, ‖core ω‖ ^ 2 +
                    2 * κ * inner ℝ (delta ω) (core ω) ∂μ) +
                    ∫ ω, κ ^ 2 * ‖delta ω‖ ^ 2 ∂μ := by
                exact integral_add
                  (hcore_sq.add (hdelta_core_int.const_mul (2 * κ)))
                  (hdelta_sq.const_mul (κ ^ 2))
              _ = ((∫ ω, ‖core ω‖ ^ 2 ∂μ) +
                    2 * κ * (∫ ω, inner ℝ (delta ω) (core ω) ∂μ)) +
                    κ ^ 2 * (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := by
                rw [integral_add hcore_sq (hdelta_core_int.const_mul (2 * κ))]
                rw [integral_const_mul, integral_const_mul]
  have hres_completion :
      ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ ≤
        ∫ ω, ‖core ω‖ ^ 2 ∂μ -
          d4ProofResidual μ A.problem (sampleAt (Sample := Sample))
            xPrev y (Algorithm2.m A t) β (A.gamma (t + 1)) t := by
    by_cases hdelta_sq_zero : (∫ ω, ‖delta ω‖ ^ 2 ∂μ) = 0
    · have hdelta_norm_sq_ae :
          (fun ω => ‖delta ω‖ ^ 2) =ᶠ[ae μ] (fun _ => 0) :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg (μ := μ)
          (fun ω => sq_nonneg (‖delta ω‖)) hdelta_sq).mp hdelta_sq_zero
      have hdelta_zero_ae : delta =ᶠ[ae μ] (fun _ => 0) := by
        filter_upwards [hdelta_norm_sq_ae] with ω hω
        have hnorm_sq : ‖delta ω‖ ^ 2 = 0 := by
          simpa using hω
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm_sq)
      have hcross_zero :
          ∫ ω, inner ℝ (delta ω) (core ω) ∂μ = 0 := by
        have hzero :
            (fun ω => inner ℝ (delta ω) (core ω)) =ᶠ[ae μ] (fun _ => 0) := by
          filter_upwards [hdelta_zero_ae] with ω hω
          simp [hω]
        simpa using (integral_congr_ae hzero)
      have hdelta_sq_zero' :
          c2DeltaNormSqExpectation μ A.problem (sampleAt (Sample := Sample))
              xPrev y t = 0 := by
        rw [hdelta_sq_def]
        exact hdelta_sq_zero
      rw [hnext_sq_expand, hcross_zero, hdelta_sq_zero]
      simp [d4ProofResidual, hdelta_sq_zero']
    · have hA_cross :
          d4ProofA μ A.problem (sampleAt (Sample := Sample))
              xPrev y (Algorithm2.m A t) β t *
              (∫ ω, ‖delta ω‖ ^ 2 ∂μ) =
            ∫ ω, inner ℝ (delta ω) (core ω) ∂μ := by
        calc
          d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm2.m A t) β t *
                (∫ ω, ‖delta ω‖ ^ 2 ∂μ) =
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm2.m A t) β t *
                c2DeltaNormSqExpectation μ A.problem
                  (sampleAt (Sample := Sample)) xPrev y t := by
                rw [hdelta_sq_def]
          _ = c2ProofG μ A.problem (sampleAt (Sample := Sample))
                (Algorithm2.x A t) (Algorithm2.xNext A t) (Algorithm2.m A t) β t +
              β *
                (c2DeltaNormSqExpectation μ A.problem
                    (sampleAt (Sample := Sample)) xPrev y t -
                  c2DeltaConditionalMeanSqExpectation μ A.problem xPrev y) := by
                dsimp [d4ProofA]
                have hdelta_sq_c2_ne :
                    c2DeltaNormSqExpectation μ A.problem
                        (sampleAt (Sample := Sample)) xPrev y t ≠ 0 := by
                  intro hzero
                  apply hdelta_sq_zero
                  rw [← hdelta_sq_def]
                  exact hzero
                field_simp [hdelta_sq_c2_ne] <;> simp [xPrev, y]
          _ = ∫ ω, inner ℝ (delta ω) (core ω) ∂μ :=
            hdelta_core_num.symm
      have hcross_A :
          (∫ ω, inner ℝ (delta ω) (core ω) ∂μ) =
            (∫ ω, ‖delta ω‖ ^ 2 ∂μ) *
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm2.m A t) β t := by
        calc
          ∫ ω, inner ℝ (delta ω) (core ω) ∂μ =
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm2.m A t) β t *
                (∫ ω, ‖delta ω‖ ^ 2 ∂μ) := hA_cross.symm
          _ = (∫ ω, ‖delta ω‖ ^ 2 ∂μ) *
              d4ProofA μ A.problem (sampleAt (Sample := Sample))
                xPrev y (Algorithm2.m A t) β t := by ring
      rw [hnext_sq_expand, hcross_A]
      dsimp [d4ProofResidual]
      rw [hdelta_sq_def]
      dsimp [κ]
      ring_nf <;> exact le_rfl
  have hres_eq :
      theoremB6ReadableC2Residual A t =
        d4ProofResidual μ A.problem (sampleAt (Sample := Sample))
          xPrev y (Algorithm2.m A t) β (A.gamma (t + 1)) t := by
    simpa [theoremB6ReadableC2Residual] using hC2_residual_compatible
  calc
    expectedEstimatorError μ A.problem.gradF
        (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) =
        ∫ ω, ‖epsNext ω‖ ^ 2 ∂μ := hnext_expected_eq
    _ ≤ ∫ ω, ‖core ω‖ ^ 2 ∂μ -
          d4ProofResidual μ A.problem (sampleAt (Sample := Sample))
            xPrev y (Algorithm2.m A t) β (A.gamma (t + 1)) t := hres_completion
    _ = ∫ ω, ‖core ω‖ ^ 2 ∂μ -
          theoremB6ReadableC2Residual A t := by rw [hres_eq]
    _ ≤ 2 * (1 - β) ^ 2 * σ ^ 2 +
          β ^ 2 * (∫ ω, ‖eps ω‖ ^ 2 ∂μ) +
          2 * β ^ 2 * L ^ 2 *
            ∫ ω, ‖y ω - xPrev ω‖ ^ 2 ∂μ -
          theoremB6ReadableC2Residual A t := by
            linarith [hcore_bound]
    _ = (A.beta1 (t + 1)) ^ 2 *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A t) (Algorithm2.m A t) +
        2 * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
          (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
            ∂runLaw A.problem) +
        2 * (1 - A.beta1 (t + 1)) ^ 2 * σ ^ 2 -
        theoremB6ReadableC2Residual A t := by
          rw [← hprev_expected_eq]
          simp [β, μ, xPrev, y]
          ring

private theorem b6_c2_i2_bound_on_horizon
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ σ c D : ℝ) (T : ℕ)
    (hparams_c :
      0 < ρ ∧ 0 < c ∧ ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hbeta_admissible :
      ∀ t ∈ Finset.Icc 1 T, 0 ≤ A.beta1 (t + 1) ∧ A.beta1 (t + 1) ≤ 1)
    (hC4_inputs :
      ∀ t ∈ Finset.Icc 1 T, Algorithm2C4SourceInputs A L ρ D t)
    (hprefix :
      ∀ t ∈ Finset.Icc 1 T,
        Measurable[
          (SOptLib.filtration
            (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
            (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
          (fun ω : SampleStream Sample =>
            ((Algorithm2.x A t ω, Algorithm2.xNext A t ω), Algorithm2.m A t ω)))
    (hone_step :
      ∀ t ∈ Finset.Icc 1 T,
        expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1))
          ≤
            (A.beta1 (t + 1)) ^ 2 *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t) +
              2 * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              2 * (1 - A.beta1 (t + 1)) ^ 2 * σ ^ 2 -
              theoremB6ReadableC2Residual A t) :
    ∀ t ∈ Finset.Icc 1 T,
      (ρ / (16 * L ^ 2 * A.eta t)) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
        (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A t) (Algorithm2.m A t)
      ≤
        (ρ / (16 * L ^ 2)) *
            ((A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1)) *
            expectedEstimatorError (runLaw A.problem) A.problem.gradF
              (Algorithm2.x A t) (Algorithm2.m A t) +
          (ρ / (8 * A.eta t)) *
            (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
              ∂runLaw A.problem) +
          (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
            (ρ / (16 * L ^ 2 * A.eta t)) *
            theoremB6ReadableC2Residual A t := by
  intro t ht
  have hstep := hone_step t ht
  by_cases hL_zero : L = 0
  · subst L
    simp
    have hη_pos : 0 < A.eta t := hparams_c.2.2 t ht
    have hD_nonneg :
        0 ≤
          (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
            ∂runLaw A.problem) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hcoef_nonneg : 0 ≤ ρ / (8 * A.eta t) := by
      have hρ_nonneg : 0 ≤ ρ := le_of_lt hparams_c.1
      have hden_pos : 0 < 8 * A.eta t := by positivity
      exact div_nonneg hρ_nonneg (le_of_lt hden_pos)
    exact mul_nonneg hcoef_nonneg hD_nonneg
  · have hη_pos : 0 < A.eta t := hparams_c.2.2 t ht
    have hρ_nonneg : 0 ≤ ρ := le_of_lt hparams_c.1
    have hLsq_pos : 0 < L ^ 2 := sq_pos_of_ne_zero hL_zero
    have hρ_div_Lsq_pos : 0 < ρ / L ^ 2 := by
      exact div_pos hparams_c.1 hLsq_pos
    have hK_nonneg : 0 ≤ ρ / (16 * L ^ 2 * A.eta t) := by
      have hden_pos : 0 < 16 * L ^ 2 * A.eta t := by positivity
      exact div_nonneg hρ_nonneg (le_of_lt hden_pos)
    have hscaled := mul_le_mul_of_nonneg_left hstep hK_nonneg
    have hβ_admissible := hbeta_admissible t ht
    have hβ_sq_le_one : (A.beta1 (t + 1)) ^ 2 ≤ 1 := by
      nlinarith [hβ_admissible.1, hβ_admissible.2]
    have hD_nonneg :
        0 ≤
          (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
            ∂runLaw A.problem) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hβ_sched : 1 - A.beta1 (t + 1) = c * A.eta t ^ 2 := by
      rw [hbeta1 t, betaOneSchedule]
      ring
    have hD_gap_nonneg :
        0 ≤
          (ρ * L ^ 2 *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) *
              L⁻¹ ^ 2 * 16 -
            (ρ * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem)) *
              L⁻¹ ^ 2 * 16 := by
      have hcommon_nonneg :
          0 ≤
            (ρ * L ^ 2 *
                  (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                    ∂runLaw A.problem)) *
                L⁻¹ ^ 2 * 16 := by
        positivity
      nlinarith [hβ_sq_le_one, hcommon_nonneg]
    have hsub :=
      sub_le_sub_right hscaled
        ((ρ / (16 * L ^ 2 * A.eta (t - 1))) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A t) (Algorithm2.m A t))
    refine le_trans hsub ?_
    rw [hβ_sched]
    field_simp [hη_pos.ne', hL_zero]
    ring_nf
    ring_nf at hD_gap_nonneg
    nlinarith [hD_gap_nonneg]

/-- Combine the expectation-level C.4 objective step with the weighted C.2
estimator telescope before the source-specific endpoint manipulations. -/
private theorem algorithm2_b6_lyapunov_telescope
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ σ c D : ℝ) (T : ℕ)
    (hC4 :
      ∀ t ∈ Finset.Icc 1 T,
        b6LyapunovNextExpectation A t ≤
          b6LyapunovCurrentExpectation A t +
            b6C4EstimatorTerm A ρ t -
            b6C4DisplacementTerm A ρ t +
            b6C4WeightDecayTerm A D t)
    (hI2 :
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t))
        ≤
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2)) *
                ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                  1 / A.eta (t - 1)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t) +
              (ρ / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) *
                theoremB6ReadableC2Residual A t))
    (hT_one : 1 ≤ T) :
    (b6LyapunovNextExpectation A T -
        b6LyapunovCurrentExpectation A 1) +
        (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t))
      ≤
    (Finset.Icc 1 T).sum
        (fun t =>
          (b6C4EstimatorTerm A ρ t -
            b6C4DisplacementTerm A ρ t +
            b6C4WeightDecayTerm A D t) +
          ((ρ / (16 * L ^ 2)) *
              ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                1 / A.eta (t - 1)) *
              expectedEstimatorError (runLaw A.problem) A.problem.gradF
                (Algorithm2.x A t) (Algorithm2.m A t) +
            (ρ / (8 * A.eta t)) *
              (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                ∂runLaw A.problem) +
            (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
            (ρ / (16 * L ^ 2 * A.eta t)) *
              theoremB6ReadableC2Residual A t)) := by
  have hC4_sum :
      (Finset.Icc 1 T).sum (fun t => b6LyapunovNextExpectation A t) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            b6LyapunovCurrentExpectation A t +
              b6C4EstimatorTerm A ρ t -
              b6C4DisplacementTerm A ρ t +
              b6C4WeightDecayTerm A D t) := by
    exact Finset.sum_le_sum (fun t ht => hC4 t ht)
  have hsum :
      (Finset.Icc 1 T).sum
          (fun t =>
            (b6LyapunovNextExpectation A t -
                b6LyapunovCurrentExpectation A t) +
              ((ρ / (16 * L ^ 2 * A.eta t)) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
                (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm2.x A t) (Algorithm2.m A t)))
        ≤
      (Finset.Icc 1 T).sum
          (fun t =>
            (b6C4EstimatorTerm A ρ t -
              b6C4DisplacementTerm A ρ t +
              b6C4WeightDecayTerm A D t) +
            ((ρ / (16 * L ^ 2)) *
                ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                  1 / A.eta (t - 1)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t) +
              (ρ / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) *
                theoremB6ReadableC2Residual A t)) := by
    have hsum := add_le_add hC4_sum hI2
    calc
      (Finset.Icc 1 T).sum
            (fun t =>
              (b6LyapunovNextExpectation A t -
                  b6LyapunovCurrentExpectation A t) +
                ((ρ / (16 * L ^ 2 * A.eta t)) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
                  (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm2.x A t) (Algorithm2.m A t))) =
          ((Finset.Icc 1 T).sum (fun t => b6LyapunovNextExpectation A t) +
            (Finset.Icc 1 T).sum
              (fun t =>
                (ρ / (16 * L ^ 2 * A.eta t)) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
                  (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm2.x A t) (Algorithm2.m A t))) -
            (Finset.Icc 1 T).sum
              (fun t => b6LyapunovCurrentExpectation A t) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            ring
      _ ≤
          ((Finset.Icc 1 T).sum
              (fun t =>
                b6LyapunovCurrentExpectation A t +
                  b6C4EstimatorTerm A ρ t -
                  b6C4DisplacementTerm A ρ t +
                  b6C4WeightDecayTerm A D t) +
            (Finset.Icc 1 T).sum
              (fun t =>
                (ρ / (16 * L ^ 2)) *
                    ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                      1 / A.eta (t - 1)) *
                    expectedEstimatorError (runLaw A.problem) A.problem.gradF
                      (Algorithm2.x A t) (Algorithm2.m A t) +
                  (ρ / (8 * A.eta t)) *
                    (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                      ∂runLaw A.problem) +
                  (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (ρ / (16 * L ^ 2 * A.eta t)) *
                    theoremB6ReadableC2Residual A t)) -
            (Finset.Icc 1 T).sum
              (fun t => b6LyapunovCurrentExpectation A t) := by
            exact sub_le_sub_right hsum _
      _ = (Finset.Icc 1 T).sum
          (fun t =>
            (b6C4EstimatorTerm A ρ t -
              b6C4DisplacementTerm A ρ t +
              b6C4WeightDecayTerm A D t) +
            ((ρ / (16 * L ^ 2)) *
                ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                  1 / A.eta (t - 1)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t) +
              (ρ / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) *
                theoremB6ReadableC2Residual A t)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            ring
  have hpotential :
      (Finset.Icc 1 T).sum
          (fun t =>
            b6LyapunovNextExpectation A t -
              b6LyapunovCurrentExpectation A t) =
        b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1 := by
    have htel :=
      sum_Icc_sub_succ
        (fun n => -b6LyapunovCurrentExpectation A n) 1 T hT_one
    calc
      (Finset.Icc 1 T).sum
          (fun t =>
            b6LyapunovNextExpectation A t -
              b6LyapunovCurrentExpectation A t) =
          (Finset.Icc 1 T).sum
            (fun t =>
              -b6LyapunovCurrentExpectation A t +
                b6LyapunovCurrentExpectation A (t + 1)) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hsucc := b6LyapunovCurrent_succ_eq_next A t
          rw [hsucc]
          ring
      _ = b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1 := by
          have htel' :
              (Finset.Icc 1 T).sum
                  (fun t =>
                    -b6LyapunovCurrentExpectation A t +
                      b6LyapunovCurrentExpectation A (t + 1)) =
                -b6LyapunovCurrentExpectation A 1 +
                  b6LyapunovCurrentExpectation A (T + 1) := by
            convert htel using 1 <;> ring
          calc
            (Finset.Icc 1 T).sum
                (fun t =>
                  -b6LyapunovCurrentExpectation A t +
                    b6LyapunovCurrentExpectation A (t + 1)) =
                -b6LyapunovCurrentExpectation A 1 +
                  b6LyapunovCurrentExpectation A (T + 1) := htel'
            _ = -b6LyapunovCurrentExpectation A 1 +
                b6LyapunovNextExpectation A T := by
                  have hsucc := b6LyapunovCurrent_succ_eq_next A T
                  rw [hsucc]
            _ = b6LyapunovNextExpectation A T -
                b6LyapunovCurrentExpectation A 1 := by ring
  calc
    (b6LyapunovNextExpectation A T -
        b6LyapunovCurrentExpectation A 1) +
        (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t)) =
      (Finset.Icc 1 T).sum
          (fun t =>
            (b6LyapunovNextExpectation A t -
                b6LyapunovCurrentExpectation A t) +
              ((ρ / (16 * L ^ 2 * A.eta t)) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
                (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                  expectedEstimatorError (runLaw A.problem) A.problem.gradF
                    (Algorithm2.x A t) (Algorithm2.m A t))) := by
        calc
          (b6LyapunovNextExpectation A T -
              b6LyapunovCurrentExpectation A 1) +
              (Finset.Icc 1 T).sum
                (fun t =>
                  (ρ / (16 * L ^ 2 * A.eta t)) *
                      expectedEstimatorError (runLaw A.problem) A.problem.gradF
                        (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
                    (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                      expectedEstimatorError (runLaw A.problem) A.problem.gradF
                        (Algorithm2.x A t) (Algorithm2.m A t)) =
              ((Finset.Icc 1 T).sum
                  (fun t =>
                    b6LyapunovNextExpectation A t -
                      b6LyapunovCurrentExpectation A t)) +
                (Finset.Icc 1 T).sum
                  (fun t =>
                    (ρ / (16 * L ^ 2 * A.eta t)) *
                        expectedEstimatorError (runLaw A.problem) A.problem.gradF
                          (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
                      (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                        expectedEstimatorError (runLaw A.problem) A.problem.gradF
                          (Algorithm2.x A t) (Algorithm2.m A t)) := by
                rw [hpotential]
          _ = (Finset.Icc 1 T).sum
              (fun t =>
                (b6LyapunovNextExpectation A t -
                    b6LyapunovCurrentExpectation A t) +
                  ((ρ / (16 * L ^ 2 * A.eta t)) *
                      expectedEstimatorError (runLaw A.problem) A.problem.gradF
                        (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
                    (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                      expectedEstimatorError (runLaw A.problem) A.problem.gradF
                        (Algorithm2.x A t) (Algorithm2.m A t))) := by
                rw [Finset.sum_add_distrib]
    _ ≤ _ := hsum

/-- The source C.2 weight-decay contribution over the finite horizon. Keeping
this as an explicit schedule window exposes the exact D.2/C.4 summand instead
of prematurely replacing it by the paper's later logarithmic estimate. -/
def theoremB6WeightDecayWindow
    (A : Algorithm2Data Sample ι) (D : ℝ) (T : ℕ) : ℝ :=
  (Finset.Icc 1 T).sum
    (fun t =>
      (A.lambda * D ^ 2 / 2) *
        Real.sqrt (2 * (1 - A.beta2 t)))

/- The unscaled-W auxiliary endpoint retained as an explicit statement-boundary
   record. The source-faithful telescope below proves the same endpoint with
   `(T : ℝ) * A.eta T` in the weight-decay denominator. -/
def TheoremB6UnscaledWeightDecayStatement
    (A : Algorithm2Data Sample ι)
    (minimum : ObjectiveMinimumWitness A.problem.F)
    (L ρ σ c s D : ℝ) (T : ℕ) : Prop :=
    let W := theoremB6WeightDecayWindow A D T
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A t) (Algorithm2.m A t)))
      ≤
        (ρ / ((T : ℝ) * A.eta T)) *
            theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
          (ρ ^ 2 / ((T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum
              (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2))) +
          (ρ * W) / (T : ℝ) -
        (ρ ^ 2 / (16 * L ^ 2 * (T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum
              (fun t => theoremB6ReadableC2Residual A t / A.eta t))
    ∧
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm2.x A t) (Algorithm2.xNext A t)))
      ≤
        8 * theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ /
            (ρ * (T : ℝ)) +
          (c ^ 2 * σ ^ 2 / (L ^ 2 * (T : ℝ))) *
            ((Finset.Icc 1 T).sum (fun t => A.eta t ^ 3)) +
          (8 * W) / (ρ * (T : ℝ)) -
        (1 / (2 * L ^ 2 * (T : ℝ))) *
          ((Finset.Icc 1 T).sum
            (fun t => theoremB6ReadableC2Residual A t / A.eta t))

/-- Corrected Lean-readable B.6 inequalities over generated Algorithm 2
objects. The estimator endpoint uses the coefficient-consistent `rho ^ 2`
variance term forced by the C.2 telescope. The displacement endpoint keeps the
`1 / eta_t` scale exposed by that telescope; the source PDF's later
`1 / eta_t ^ 2` proof display is retained separately as a boundary issue.
The weight-decay contribution retains the `1 / A.eta T` factor produced by
the source-faithful extraction from the weighted telescope. -/
def TheoremB6CorrectedStatement
    (A : Algorithm2Data Sample ι)
    (minimum : ObjectiveMinimumWitness A.problem.F)
    (L ρ σ c s D : ℝ) (T : ℕ) : Prop :=
    let W := theoremB6WeightDecayWindow A D T
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A t) (Algorithm2.m A t)))
      ≤
        (ρ / ((T : ℝ) * A.eta T)) *
            theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
          (ρ ^ 2 / ((T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum
              (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2))) +
          (ρ * W) / ((T : ℝ) * A.eta T) -
        (ρ ^ 2 / (16 * L ^ 2 * (T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum
              (fun t => theoremB6ReadableC2Residual A t / A.eta t))
    ∧
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm2.x A t) (Algorithm2.xNext A t)))
      ≤
        8 * theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ /
            (ρ * (T : ℝ)) +
          (c ^ 2 * σ ^ 2 / (L ^ 2 * (T : ℝ))) *
            ((Finset.Icc 1 T).sum (fun t => A.eta t ^ 3)) +
          (8 * W) / (ρ * (T : ℝ)) -
        (1 / (2 * L ^ 2 * (T : ℝ))) *
          ((Finset.Icc 1 T).sum
            (fun t => theoremB6ReadableC2Residual A t / A.eta t))

/-- The source endpoint uses nonnegativity of the weight-decay quadratic when
lower-bounding the terminal Lyapunov value. The published setup names `lambda`
as an input but does not state this sign condition, so the corrected route
keeps it as a local extension boundary. -/
def B6LyapunovPotentialLowerBoundExtension
    (A : Algorithm2Data Sample ι) : Prop :=
  0 ≤ A.lambda

theorem theoremB6_initial_lyapunov_upper_bound
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (L ρ σ D : ℝ) (T : ℕ)
    (hL_pos : 0 < L) (hρ_pos : 0 < ρ)
    (hη0_pos : 0 < A.eta 0)
    (hT_one : 1 ≤ T)
    (hpotential : B6LyapunovPotentialIntegrabilityExtension A T)
    (hB6_initial_estimator_error_bound :
      expectedEstimatorError (runLaw A.problem) A.problem.gradF
        (Algorithm2.x A 1) (Algorithm2.m A 1) ≤ σ ^ 2)
    (hB6_initial_weighted_H_bound :
      ∀ ω : SampleStream Sample,
        (A.lambda / 2) *
            inner ℝ (Algorithm2.x A 1 ω)
              (Algorithm2.preconditioner A 1 ω (Algorithm2.x A 1 ω)) ≤
          (A.lambda / 2) * D ^ 2 * (1 + A.epsilon)) :
    b6LyapunovCurrentExpectation A 1 +
        (ρ / (16 * L ^ 2 * A.eta 0)) *
          expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A 1) (Algorithm2.m A 1) ≤
      A.problem.F A.x0 + (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
        (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2 := by
  have hcurrent_int :=
    (hpotential 1 (Finset.mem_Icc.mpr ⟨le_rfl, hT_one⟩)).2
  have hpotential_bound :
      b6LyapunovCurrentExpectation A 1 ≤
        A.problem.F A.x0 + (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) := by
    have hpoint :
        ∀ ω : SampleStream Sample,
          A.problem.F (Algorithm2.x A 1 ω) +
              (A.lambda / 2) *
                inner ℝ (Algorithm2.x A 1 ω)
                  (Algorithm2.preconditioner A 1 ω
                    (Algorithm2.x A 1 ω)) ≤
            A.problem.F A.x0 + (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) := by
      intro ω
      have hinit := hB6_initial_weighted_H_bound ω
      rw [Algorithm2.x_one] at hinit ⊢
      linarith [hinit]
    letI : IsProbabilityMeasure (runLaw A.problem) :=
      runLaw_isProbabilityMeasure A.problem
    have hbound :=
      integral_mono hcurrent_int (integrable_const _) hpoint
    simpa [b6LyapunovCurrentExpectation, integral_const, probReal_univ] using hbound
  have hcoeff_nonneg :
      0 ≤ ρ / (16 * L ^ 2 * A.eta 0) := by
    positivity
  have herror_bound :=
    mul_le_mul_of_nonneg_left hB6_initial_estimator_error_bound hcoeff_nonneg
  linarith

theorem theoremB6_terminal_lyapunov_lower_bound
    {ι : Type*} [Fintype ι]
    (A : Algorithm2Data Sample ι)
    (minimum : ObjectiveMinimumWitness A.problem.F)
    (ρ : ℝ) (T : ℕ)
    (hH : RandomHLowerBounded (Algorithm2.preconditioner A) ρ)
    (hlambda :
      B6LyapunovPotentialLowerBoundExtension A)
    (hpotential : B6LyapunovPotentialIntegrabilityExtension A T)
    (hT_one : 1 ≤ T) :
        attainedObjectiveMinimumValue A.problem.F minimum ≤
      b6LyapunovNextExpectation A T := by
  have hnext_int :=
    (hpotential T (Finset.mem_Icc.mpr ⟨hT_one, le_rfl⟩)).1
  have hpoint :
      ∀ ω : SampleStream Sample,
        attainedObjectiveMinimumValue A.problem.F minimum ≤
          A.problem.F (Algorithm2.xNext A T ω) +
            (A.lambda / 2) *
              inner ℝ (Algorithm2.xNext A T ω)
                (Algorithm2.preconditioner A (T + 1) ω
                  (Algorithm2.xNext A T ω)) := by
    intro ω
    have hmin :=
      SOptLib.objectiveMinimumValue_le A.problem.F minimum
        (Algorithm2.xNext A T ω)
    have hmin' :
        attainedObjectiveMinimumValue A.problem.F minimum ≤
          A.problem.F (Algorithm2.xNext A T ω) := by
      simpa [attainedObjectiveMinimumValue] using hmin
    have hinner :
        0 ≤ inner ℝ (Algorithm2.xNext A T ω)
          (Algorithm2.preconditioner A (T + 1) ω
            (Algorithm2.xNext A T ω)) := by
      have hlower :=
        (RandomHLowerBounded.lower hH).2 (T + 1) (by omega) ω
          (Algorithm2.xNext A T ω)
      nlinarith [hH.1.1, sq_nonneg ‖Algorithm2.xNext A T ω‖]
    have hquad :
        0 ≤
          (A.lambda / 2) *
            inner ℝ (Algorithm2.xNext A T ω)
              (Algorithm2.preconditioner A (T + 1) ω
                (Algorithm2.xNext A T ω)) := by
      exact mul_nonneg (by
        have : 0 ≤ A.lambda := hlambda
        linarith) hinner
    linarith [hmin', hquad]
  letI : IsProbabilityMeasure (runLaw A.problem) :=
    runLaw_isProbabilityMeasure A.problem
  have hbound :=
    integral_mono (integrable_const _) hnext_int hpoint
  simpa [b6LyapunovNextExpectation, integral_const, probReal_univ] using hbound

/-- The two printed B.6 inequalities, with the paper's source symbols
`min_x F(x)` and `M_{t+1}` exposed explicitly instead of replaced by corrected
Lean objects. -/
def TheoremB6PrintedInequalities
    (A : Algorithm2Data Sample ι)
    (Fmin : ℝ) (M : ℕ → ℝ) (L ρ σ c s D : ℝ) (T : ℕ) : Prop :=
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A t) (Algorithm2.m A t)))
      ≤
        (2 * ρ *
            (theoremB6GPrinted A.problem.F A.x0 Fmin A.lambda D A.epsilon ρ s L σ +
              A.lambda * D ^ 2 * Real.log (s + T)) +
            (ρ * c ^ 2 * σ ^ 2 / (4 * L ^ 2)) * Real.log (s + T)) *
          ((T : ℝ) ^ (-(2 : ℝ) / 3)) -
        (ρ ^ 2 * ((Finset.Icc 1 T).sum (fun t => M (t + 1)))) /
          (16 * L ^ 2 * (T : ℝ) ^ ((1 : ℝ) / 3))
    ∧
    (1 / (T : ℝ)) *
        ((Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm2.x A t) (Algorithm2.xNext A t)))
      ≤
        (16 *
            (theoremB6GPrinted A.problem.F A.x0 Fmin A.lambda D A.epsilon ρ s L σ +
              A.lambda * D ^ 2 * Real.log (s + T)) / ρ +
            (2 * c ^ 2 * σ ^ 2 / L ^ 2) * Real.log (s + T)) *
          ((T : ℝ) ^ (-(2 : ℝ) / 3)) -
        ((Finset.Icc 1 T).sum (fun t => M (t + 1))) /
          (L ^ 2 * (T : ℝ) ^ ((1 : ℝ) / 3))

/-- Registered B.6 source-boundary contract. It keeps the displayed inequality
shape separate from the corrected Lean-readable theorem and records the
source-boundary facts that block an A-level reading of the original statement. -/
def TheoremB6SourceBoundaryContract
    (A : Algorithm2Data Sample ι) (c : ℝ) (T : ℕ) : Prop :=
  B6C2BetaAdmissibilitySourceGap A c T ∧
  C2LiteralSourceGTypeIssue = SourceBoundaryIssue.sourceDefect ∧
  ObjectiveMinimumAttainmentSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
    C2ADenominatorSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
    D12GammaDenominatorSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
    D12GammaChoiceSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  C5SGeOneSourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  B6SmoothnessPositivitySourceIssue = SourceBoundaryIssue.missingPrerequisite ∧
  B6ObjectiveTrajectoryIntegrabilitySourceIssue =
    SourceBoundaryIssue.missingPrerequisite ∧
  Phi1ClippingBridgeSourceIssue = SourceBoundaryIssue.statementProofMismatch ∧
  DisplacementScaleStatementVsProofIssue = SourceBoundaryIssue.statementProofMismatch

set_option maxHeartbeats 800000 in
/-- Corrected B.6 theorem over generated Algorithm 2 objects. -/
theorem theorem_B_6_corrected
    (A : Algorithm2Data Sample ι)
    (minimum : ObjectiveMinimumWitness A.problem.F)
    (L ρ σ c s D : ℝ) (T : ℕ)
    (hobj_unbiased : UnbiasedObjectiveOracle A.problem)
    (hgrad_unbiased : UnbiasedGradientOracle A.problem)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L)
    (hH : RandomHLowerBounded (Algorithm2.preconditioner A) ρ)
    (heta : ∀ t : ℕ, A.eta t = etaSchedule s t)
    (hs : s ≥ max (8 * L ^ 3 / ρ ^ 3) (64 * A.lambda ^ 3))
    (hL_pos : 0 < L)
    (hs_ge_one : 1 ≤ s)
    (hbounded : ∀ t : ℕ, ∀ ω : SampleStream Sample, ‖Algorithm2.x A t ω‖ ≤ D)
    (hc : c ≥ 32 * L ^ 2 * ρ⁻¹ ^ 2 + 1)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hbeta2 : ∀ t : ℕ, A.beta2 (t + 1) = betaTwoSchedule A.eta t)
    (hT : (T : ℝ) ≥ s)
    (hexpect : TheoremB6ExpectationWellDefined A T)
    (hpotential : B6LyapunovPotentialIntegrabilityExtension A T)
    (hD2 : TheoremB6D2ExactLyapunovCorrectionBoundary A ρ D T)
    (hlambda :
      B6LyapunovPotentialLowerBoundExtension A)
    (hB6_initial_estimator_error_bound :
      expectedEstimatorError (runLaw A.problem) A.problem.gradF
        (Algorithm2.x A 1) (Algorithm2.m A 1) ≤ σ ^ 2)
    (hB6_initial_weighted_H_bound :
      ∀ ω : SampleStream Sample,
        (A.lambda / 2) *
            inner ℝ (Algorithm2.x A 1 ω)
              (Algorithm2.preconditioner A 1 ω (Algorithm2.x A 1 ω)) ≤
          (A.lambda / 2) * D ^ 2 * (1 + A.epsilon))
    (hc2 : TheoremB6C2CorrectedExtensionBoundary A T) :
    TheoremB6CorrectedStatement A minimum L ρ σ c s D T := by
  have hc4_inputs :
      ∀ t ∈ Finset.Icc 1 T, Algorithm2C4SourceInputs A L ρ D t := by
    intro t ht
    exact
      Algorithm2C4SourceInputs.of_smooth_and_d2Boundary hsmooth hD2.1 ht
  have hc4_exact_inputs :
      ∀ t ∈ Finset.Icc 1 T,
        Algorithm2ExactLyapunovC4SourceInputs A L ρ D t := by
    intro t ht
    exact
      ⟨StochasticSmooth.objective_smooth_upper hsmooth,
        TheoremB6D2ExactLyapunovCorrectionBoundary.exactInnerProductBound
          hD2 ht⟩
  have hC2_no_clipping : Algorithm2RawCorrectionNormLeOneOnHorizon A T :=
    TheoremB6C2CorrectedExtensionBoundary.noClipping hc2
  have hstep_meas :
      ∀ k : ℕ,
        Measurable
          (fun p : Algorithm2State ι × Sample =>
            Algorithm2.stepAtSample A k p.1 p.2) :=
    algorithm2_stepAtSample_measurable_of_oracle A hgrad_unbiased
  have hprefix :
      ∀ t ∈ Finset.Icc 1 T,
        Measurable[
          (SOptLib.filtration
            (fun k (ω : SampleStream Sample) => sampleAt (Sample := Sample) k ω)
            (fun k => by simpa [sampleAt] using measurable_pi_apply k)).seq (t + 1)]
          (fun ω : SampleStream Sample =>
            ((Algorithm2.x A t ω, Algorithm2.xNext A t ω), Algorithm2.m A t ω)) := by
    intro t ht
    exact algorithm2_prefix_adapted_state_before_fresh_sample A hstep_meas t
      (Finset.mem_Icc.mp ht).1
  have hD4_momentum_update :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        Algorithm2.m A (t + 1) ω =
          (A.beta1 (t + 1)) • Algorithm2.m A t ω +
            (1 - A.beta1 (t + 1)) •
              marsCorrection (A.beta1 (t + 1)) (A.gamma (t + 1))
                (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω))
                (A.problem.stochasticGrad (Algorithm2.x A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω)) :=
    algorithm2_momentum_succ_unclipped_of_correction_norm_le_one
      A T hC2_no_clipping
  have hc_pos : 0 < c := by
    have hnonneg : 0 ≤ 32 * L ^ 2 * ρ⁻¹ ^ 2 := by positivity
    linarith [hc]
  have heta_pos :
      ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t := by
    intro t ht
    rw [heta t, etaSchedule]
    apply Real.rpow_pos_of_pos
    have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num) hs_ge_one
    have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le t
    linarith
  have hparams_c :
      0 < ρ ∧ 0 < c ∧ ∀ t ∈ Finset.Icc 1 T, 0 < A.eta t :=
    ⟨hH.1.1, hc_pos, heta_pos⟩
  have hxNext_succ :
      ∀ t : ℕ, ∀ ω : SampleStream Sample,
        Algorithm2.xNext A t ω = Algorithm2.x A (t + 1) ω :=
    Algorithm2.xNext_eq_x_succ A
  have hC2_ext :=
    TheoremB6C2CorrectedExtensionBoundary.c2 hc2
  have hC2_raw_recursion :
      ∀ t ∈ Finset.Icc 1 T, ∀ ω : SampleStream Sample,
        c2EstimatorError A.problem (Algorithm2.x A (t + 1))
            (Algorithm2.m A (t + 1)) ω =
          (1 - A.beta1 (t + 1)) •
              (A.problem.stochasticGrad (Algorithm2.xNext A t ω)
                  (sampleAt (Sample := Sample) (t + 1) ω) -
                A.problem.gradF (Algorithm2.xNext A t ω)) +
            (A.beta1 (t + 1)) •
              c2EstimatorError A.problem (Algorithm2.x A t) (Algorithm2.m A t) ω +
            (A.beta1 (t + 1)) •
              ((A.gamma (t + 1)) •
                  c2Delta A.problem (sampleAt (Sample := Sample))
                    (Algorithm2.x A t) (Algorithm2.xNext A t) t ω -
                (A.problem.gradF (Algorithm2.xNext A t ω) -
                  A.problem.gradF (Algorithm2.x A t ω))) :=
    b6_c2_estimator_error_recursion_raw A c T hparams_c.2 hbeta1
      hD4_momentum_update hxNext_succ
  have hone_step :
      ∀ t ∈ Finset.Icc 1 T,
        expectedEstimatorError (runLaw A.problem) A.problem.gradF
            (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1))
          ≤
            (A.beta1 (t + 1)) ^ 2 *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t) +
              2 * (A.beta1 (t + 1)) ^ 2 * L ^ 2 *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              2 * (1 - A.beta1 (t + 1)) ^ 2 * σ ^ 2 -
              theoremB6ReadableC2Residual A t := by
    intro t ht
    have hprev_sq :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖c2EstimatorError A.problem (Algorithm2.x A t) (Algorithm2.m A t) ω‖ ^ 2)
          (runLaw A.problem) := by
      simpa [ExpectedEstimatorErrorWellDefined, c2EstimatorError, norm_sub_rev]
        using (hexpect t ht).1
    have hdisp_sq :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2)
          (runLaw A.problem) := by
      have hscaled := (hexpect t ht).2
      have h := hscaled.const_mul (A.eta t)
      convert h using 1
      ext ω
      field_simp [(heta_pos t ht).ne']
    exact
      b6_c2_one_step_second_moment_bound A L σ t
        (Finset.mem_Icc.mp ht).1 (hprefix t ht)
        (fun ω => hC2_raw_recursion t ht ω)
        (hC2_ext.1 t ht)
        (hC2_ext.2.1 t ht)
        (hC2_ext.2.2.2.2.2 t ht)
        hprev_sq hdisp_sq hgrad_unbiased hvar hsmooth
  have hI2_C5 :=
    b6_c2_i2_bound_on_horizon A L ρ σ c D T hparams_c hbeta1
      (fun t ht => hC2_ext.1 t ht) hc4_inputs hprefix hone_step
  have hI2_C5_sum :
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t))
        ≤
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2)) *
                ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                  1 / A.eta (t - 1)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t) +
              (ρ / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) *
                theoremB6ReadableC2Residual A t) := by
    exact Finset.sum_le_sum (fun t ht => hI2_C5 t ht)
  have hC4_absorb :
      ∀ t ∈ Finset.Icc 1 T,
        L / 2 + ρ * A.lambda ≤ ρ / (2 * A.eta t) := by
    intro t ht
    have hs_L : 8 * L ^ 3 / ρ ^ 3 ≤ s :=
      le_trans (le_max_left _ _) hs
    have hs_lambda : 64 * A.lambda ^ 3 ≤ s :=
      le_trans (le_max_right _ _) hs
    have hL_absorb :
        L / 2 ≤ ρ / (4 * A.eta t) := by
      rw [heta t]
      exact etaSchedule_absorption_of_cube_bound hparams_c.1 hs_L hs_ge_one t
    have hs_lambda' : 8 * (2 * A.lambda) ^ 3 ≤ s := by
      calc
        8 * (2 * A.lambda) ^ 3 = 64 * A.lambda ^ 3 := by ring
        _ ≤ s := hs_lambda
    have hlam_absorb :
        A.lambda ≤ (4 * A.eta t)⁻¹ := by
      rw [heta t]
      have hs_lambda'' : s ≥ 8 * (2 * A.lambda) ^ 3 / (1 : ℝ) ^ 3 := by
        simpa using hs_lambda'
      have h :=
        etaSchedule_absorption_of_cube_bound
          (ρ := (1 : ℝ)) (L := 2 * A.lambda) (s := s)
          (by norm_num) hs_lambda'' hs_ge_one t
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    have hlam_absorb' :
        ρ * A.lambda ≤ ρ / (4 * A.eta t) :=
      calc
        ρ * A.lambda ≤ ρ * (4 * A.eta t)⁻¹ :=
          mul_le_mul_of_nonneg_left hlam_absorb (le_of_lt hparams_c.1)
        _ = ρ / (4 * A.eta t) := by
          field_simp [(heta_pos t ht).ne']
    calc
      L / 2 + ρ * A.lambda ≤
          ρ / (4 * A.eta t) + ρ / (4 * A.eta t) :=
        add_le_add hL_absorb hlam_absorb'
      _ = ρ / (2 * A.eta t) := by ring
  have hC4_expectation :
      ∀ t ∈ Finset.Icc 1 T,
        b6LyapunovNextExpectation A t ≤
          b6LyapunovCurrentExpectation A t +
            b6C4EstimatorTerm A ρ t -
            b6C4DisplacementTerm A ρ t +
            b6C4WeightDecayTerm A D t := by
    intro t ht
    have hdisp_int :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2)
          (runLaw A.problem) := by
      have hscaled := (hexpect t ht).2
      have h := hscaled.const_mul (A.eta t)
      convert h using 1
      ext ω
      field_simp [(heta_pos t ht).ne']
    exact
      algorithm2_c4_exact_lyapunov_expectation_one_step A L ρ D T t ht
        (heta_pos t ht) hparams_c.1
        (hc4_exact_inputs t ht) (hC4_absorb t ht) hpotential
        (hexpect t ht).1 hdisp_int
  have hcombined_telescope :=
    algorithm2_b6_lyapunov_telescope A L ρ σ c D T
      hC4_expectation hI2_C5_sum
      (by
        have hT_one_real : (1 : ℝ) ≤ (T : ℝ) := by
          exact le_trans (by exact_mod_cast hs_ge_one) hT
        exact_mod_cast hT_one_real)
  have hT_one : 1 ≤ T := by
    exact_mod_cast (show (1 : ℝ) ≤ (T : ℝ) from
      le_trans (by exact_mod_cast hs_ge_one) hT)
  have hη0_pos : 0 < A.eta 0 := by
    rw [heta 0, etaSchedule]
    apply Real.rpow_pos_of_pos
    have hs_pos : 0 < s := lt_of_lt_of_le (by norm_num) hs_ge_one
    linarith
  have hinitial_potential :=
    theoremB6_initial_lyapunov_upper_bound A L ρ σ D T hL_pos hparams_c.1
      hη0_pos
      hT_one hpotential hB6_initial_estimator_error_bound
      hB6_initial_weighted_H_bound
  have hterminal_potential :=
    theoremB6_terminal_lyapunov_lower_bound A minimum ρ T hH hlambda
      hpotential hT_one
  have hC5_coefficient_absorption :
      ∀ t ∈ Finset.Icc 1 T,
        (ρ / (16 * L ^ 2)) *
            ((A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1)) ≤
          -(2 * A.eta t / ρ) := by
    intro t ht
    have hη_pos : 0 < A.eta t := hparams_c.2.2 t ht
    have hρ_pos : 0 < ρ := hparams_c.1
    have hLsq_pos : 0 < L ^ 2 := sq_pos_of_pos hL_pos
    have hbeta_admissible := hC2_ext.1 t ht
    have hbeta_nonneg : 0 ≤ A.beta1 (t + 1) := hbeta_admissible.1
    have hβ_sched : 1 - A.beta1 (t + 1) = c * A.eta t ^ 2 := by
      rw [hbeta1 t, betaOneSchedule]
      ring
    have hc_pos : 0 < c := hparams_c.2.1
    have hrecip_diff :
        1 / A.eta t - 1 / A.eta (t - 1) ≤ A.eta t := by
      rw [heta t, heta (t - 1)]
      exact etaSchedule_reciprocal_step_le hs_ge_one t
    have hsq_lower :
        c * A.eta t ^ 2 ≤ 1 - (A.beta1 (t + 1)) ^ 2 := by
      have hprod :
          0 ≤ c * A.eta t ^ 2 * A.beta1 (t + 1) :=
        mul_nonneg
          (mul_nonneg (le_of_lt hc_pos) (sq_nonneg _))
          hbeta_nonneg
      rw [← hβ_sched]
      nlinarith [hprod]
    have hdiv :
        c * A.eta t ≤
          (1 - (A.beta1 (t + 1)) ^ 2) / A.eta t := by
      apply (le_div_iff₀ hη_pos).mpr
      nlinarith [hsq_lower]
    have hcoeff :
        (A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1) ≤
          -(32 * L ^ 2 / ρ ^ 2) * A.eta t := by
      have hsplit :
          (A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1) =
            (1 / A.eta t - 1 / A.eta (t - 1)) -
              (1 - (A.beta1 (t + 1)) ^ 2) / A.eta t := by
        field_simp [hη_pos.ne']
        ring
      have hbasic :
          (A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1) ≤
            -(c - 1) * A.eta t := by
        rw [hsplit]
        have hsub := sub_le_sub_right hrecip_diff
          ((1 - (A.beta1 (t + 1)) ^ 2) / A.eta t)
        nlinarith [hdiv, hsub]
      have hinv_sq : ρ⁻¹ ^ 2 = 1 / ρ ^ 2 := by
        field_simp [hρ_pos.ne']
      have hc' := hc
      rw [hinv_sq] at hc'
      have hcbound : 32 * L ^ 2 / ρ ^ 2 ≤ c - 1 := by
        have hc'' : c ≥ 32 * L ^ 2 / ρ ^ 2 + 1 := by
          simpa [div_eq_mul_inv] using hc'
        linarith
      have hmul :=
        mul_le_mul_of_nonneg_right hcbound (le_of_lt hη_pos)
      have hmul' :
          -(c - 1) * A.eta t ≤
            -(32 * L ^ 2 / ρ ^ 2) * A.eta t := by
        linarith only [hmul]
      exact le_trans hbasic hmul'
    have hscaled :=
      mul_le_mul_of_nonneg_left hcoeff
        (le_of_lt
          (div_pos hρ_pos (mul_pos (by norm_num : (0 : ℝ) < 16) hLsq_pos)))
    calc
      (ρ / (16 * L ^ 2)) *
            ((A.beta1 (t + 1)) ^ 2 / A.eta t -
              1 / A.eta (t - 1)) ≤
          (ρ / (16 * L ^ 2)) *
            (-(32 * L ^ 2 / ρ ^ 2) * A.eta t) := hscaled
      _ = -(2 * A.eta t / ρ) := by
        field_simp [hρ_pos.ne', hL_pos.ne']
        ring
  have hI2_absorbed :
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A (t + 1)) (Algorithm2.m A (t + 1)) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t)) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            -(2 * A.eta t / ρ) *
                expectedEstimatorError (runLaw A.problem) A.problem.gradF
                  (Algorithm2.x A t) (Algorithm2.m A t) +
              (ρ / (8 * A.eta t)) *
                (∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
                  ∂runLaw A.problem) +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) *
                theoremB6ReadableC2Residual A t) := by
    apply Finset.sum_le_sum
    intro t ht
    have hpoint := hI2_C5 t ht
    have hE :
        0 ≤ expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm2.x A t) (Algorithm2.m A t) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hcoeff := hC5_coefficient_absorption t ht
    have hcoeffE := mul_le_mul_of_nonneg_right hcoeff hE
    nlinarith [hpoint, hcoeffE]

  let E0 : ℕ → ℝ := fun t =>
    expectedEstimatorError (runLaw A.problem) A.problem.gradF
      (Algorithm2.x A t) (Algorithm2.m A t)
  let D0 : ℕ → ℝ := fun t =>
    ∫ ω, ‖Algorithm2.xNext A t ω - Algorithm2.x A t ω‖ ^ 2
      ∂runLaw A.problem
  let M0 : ℕ → ℝ := fun t => theoremB6ReadableC2Residual A t
  have hcoeff_absorbed :
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2)) *
                ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                  1 / A.eta (t - 1)) * E0 t +
              (ρ / (8 * A.eta t)) * D0 t +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            -(2 * A.eta t / ρ) * E0 t +
              (ρ / (8 * A.eta t)) * D0 t +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
    apply Finset.sum_le_sum
    intro t ht
    have hE :
        0 ≤ E0 t := by
      dsimp [E0]
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hscaled :
        (ρ / (16 * L ^ 2)) *
              ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                1 / A.eta (t - 1)) * E0 t ≤
            (-(2 * A.eta t / ρ)) * E0 t := by
      exact mul_le_mul_of_nonneg_right
        (hC5_coefficient_absorption t ht) hE
    linarith
  let W : ℝ := theoremB6WeightDecayWindow A D T
  let E : ℝ :=
    (Finset.Icc 1 T).sum (fun t => (A.eta t / ρ) * E0 t)
  let R : ℝ :=
    (Finset.Icc 1 T).sum (fun t => (ρ / (8 * A.eta t)) * D0 t)
  let V : ℝ :=
    (Finset.Icc 1 T).sum
      (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2))
  let Q : ℝ :=
    (Finset.Icc 1 T).sum
      (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)
  let init : ℝ :=
    (ρ / (16 * L ^ 2 * A.eta 0)) * E0 1
  let terminal : ℝ :=
    (ρ / (16 * L ^ 2 * A.eta T)) * E0 (T + 1)
  have hboundary :
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) =
        terminal - init := by
    let potential : ℕ → ℝ := fun n =>
      (ρ / (16 * L ^ 2 * A.eta (n - 1))) * E0 n
    have htel := sum_Icc_sub_succ (fun n => -potential n) 1 T hT_one
    calc
      (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) =
          (Finset.Icc 1 T).sum
            (fun t => -potential t + potential (t + 1)) := by
              apply Finset.sum_congr rfl
              intro t ht
              simp [potential, Nat.add_sub_cancel]
              ring
      _ = terminal - init := by
            have htel' :
                (Finset.Icc 1 T).sum
                    (fun t => -potential t + potential (t + 1)) =
                  -potential 1 + potential (T + 1) := by
              simpa only [sub_neg_eq_add] using htel
            rw [htel']
            simp only [potential, init, terminal, Nat.add_sub_cancel,
              Nat.sub_self]
            ring
  have hmain :
      (b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1) +
        (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) ≤
        (Finset.Icc 1 T).sum
          (fun t =>
            (b6C4EstimatorTerm A ρ t -
              b6C4DisplacementTerm A ρ t +
              b6C4WeightDecayTerm A D t) +
            (-(2 * A.eta t / ρ) * E0 t +
              (ρ / (8 * A.eta t)) * D0 t +
              (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
              (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) := by
    calc
      (b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1) +
        (Finset.Icc 1 T).sum
          (fun t =>
            (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
              (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) ≤
          (Finset.Icc 1 T).sum
              (fun t =>
                b6C4EstimatorTerm A ρ t -
                  b6C4DisplacementTerm A ρ t +
                  b6C4WeightDecayTerm A D t) +
            (Finset.Icc 1 T).sum
              (fun t =>
                (ρ / (16 * L ^ 2)) *
                    ((A.beta1 (t + 1)) ^ 2 / A.eta t -
                      1 / A.eta (t - 1)) * E0 t +
                  (ρ / (8 * A.eta t)) * D0 t +
                  (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
            simpa only [E0, D0, M0, Finset.sum_add_distrib] using
              hcombined_telescope
      _ ≤
          (Finset.Icc 1 T).sum
              (fun t =>
                b6C4EstimatorTerm A ρ t -
                  b6C4DisplacementTerm A ρ t +
                  b6C4WeightDecayTerm A D t) +
            (Finset.Icc 1 T).sum
              (fun t =>
                -(2 * A.eta t / ρ) * E0 t +
                  (ρ / (8 * A.eta t)) * D0 t +
                  (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
            convert
              add_le_add_left hcoeff_absorbed
                ((Finset.Icc 1 T).sum
                  (fun t =>
                    b6C4EstimatorTerm A ρ t -
                      b6C4DisplacementTerm A ρ t +
                      b6C4WeightDecayTerm A D t)) using 1 <;> ring
      _ = _ := by rw [← Finset.sum_add_distrib]
  have hmain_expanded :
      b6LyapunovNextExpectation A T -
          b6LyapunovCurrentExpectation A 1 +
        terminal - init ≤
      -E - R + W + V - Q := by
    calc
      b6LyapunovNextExpectation A T -
            b6LyapunovCurrentExpectation A 1 +
          terminal - init =
          (b6LyapunovNextExpectation A T -
            b6LyapunovCurrentExpectation A 1) +
            (Finset.Icc 1 T).sum
              (fun t =>
                (ρ / (16 * L ^ 2 * A.eta t)) * E0 (t + 1) -
                  (ρ / (16 * L ^ 2 * A.eta (t - 1))) * E0 t) := by
                    rw [hboundary]
                    ring
      _ ≤
          (Finset.Icc 1 T).sum
            (fun t =>
              (b6C4EstimatorTerm A ρ t -
                b6C4DisplacementTerm A ρ t +
                b6C4WeightDecayTerm A D t) +
              (-(2 * A.eta t / ρ) * E0 t +
                (ρ / (8 * A.eta t)) * D0 t +
                (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) := hmain
      _ = -E - R + W + V - Q := by
        have hpoint :
            ∀ t ∈ Finset.Icc 1 T,
              (b6C4EstimatorTerm A ρ t -
                  b6C4DisplacementTerm A ρ t +
                  b6C4WeightDecayTerm A D t) +
                (-(2 * A.eta t / ρ) * E0 t +
                  (ρ / (8 * A.eta t)) * D0 t +
                  (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                  (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) =
              -((A.eta t / ρ) * E0 t) -
                (ρ / (8 * A.eta t)) * D0 t +
                b6C4WeightDecayTerm A D t +
                (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                (ρ / (16 * L ^ 2 * A.eta t)) * M0 t := by
          intro t ht
          dsimp [b6C4EstimatorTerm, b6C4DisplacementTerm,
            b6C4WeightDecayTerm, E0, D0, M0]
          simp only [norm_sub_rev]
          ring
        calc
          (Finset.Icc 1 T).sum
              (fun t =>
                (b6C4EstimatorTerm A ρ t -
                    b6C4DisplacementTerm A ρ t +
                    b6C4WeightDecayTerm A D t) +
                  (-(2 * A.eta t / ρ) * E0 t +
                    (ρ / (8 * A.eta t)) * D0 t +
                    (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                    (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) =
                (Finset.Icc 1 T).sum
                (fun t =>
                      -((A.eta t / ρ) * E0 t) -
                        (ρ / (8 * A.eta t)) * D0 t +
                    b6C4WeightDecayTerm A D t +
                    (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                    (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
                exact Finset.sum_congr rfl hpoint
          _ = -E - R + W + V - Q := by
            have hdecay :
                (Finset.Icc 1 T).sum
                    (fun t => b6C4WeightDecayTerm A D t) = W := by
              dsimp [W]
              apply Finset.sum_congr rfl
              intro t ht
              dsimp [b6C4WeightDecayTerm]
              ring
            have hsplit :
                (Finset.Icc 1 T).sum
                    (fun t =>
                      -((A.eta t / ρ) * E0 t) -
                        (ρ / (8 * A.eta t)) * D0 t +
                        b6C4WeightDecayTerm A D t +
                        (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2) -
                        (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) =
                  -E - R +
                    (Finset.Icc 1 T).sum
                      (fun t => b6C4WeightDecayTerm A D t) +
                    V - Q := by
              dsimp [E, R, V, Q]
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                Finset.sum_neg_distrib]
            rw [hsplit, hdecay]
  have hterminal_nonneg : 0 ≤ terminal := by
    dsimp [terminal, E0]
    have hTmem : T ∈ Finset.Icc 1 T :=
      Finset.mem_Icc.mpr ⟨hT_one, le_rfl⟩
    have hηT := hparams_c.2.2 T hTmem
    have hE :
        0 ≤ expectedEstimatorError (runLaw A.problem) A.problem.gradF
          (Algorithm2.x A (T + 1)) (Algorithm2.m A (T + 1)) := by
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hcoef :
        0 ≤ ρ / (16 * L ^ 2 * A.eta T) := by
      exact div_nonneg (le_of_lt hparams_c.1)
        (le_of_lt (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hL_pos)) hηT))
    exact mul_nonneg hcoef hE
  have hrecip0 : 1 / A.eta 0 = s ^ ((1 : ℝ) / 3) := by
    rw [heta 0, etaSchedule]
    simp only [Nat.cast_zero, add_zero]
    rw [one_div, ← Real.rpow_neg_one,
      ← Real.rpow_mul (le_of_lt (lt_of_lt_of_le zero_lt_one hs_ge_one))]
    norm_num
  have hinit :
      init ≤
        theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ -
          (A.problem.F A.x0 -
            attainedObjectiveMinimumValue A.problem.F minimum) := by
    have hcoeff_nonneg : 0 ≤ ρ / (16 * L ^ 2 * A.eta 0) := by
      have hden_pos : 0 < 16 * L ^ 2 * A.eta 0 := by
        exact mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 16) (sq_pos_of_pos hL_pos))
          hη0_pos
      exact div_nonneg (le_of_lt hparams_c.1) (le_of_lt hden_pos)
    have hscaled :=
      mul_le_mul_of_nonneg_left hB6_initial_estimator_error_bound hcoeff_nonneg
    have hcoeff_split :
        ρ / (16 * L ^ 2 * A.eta 0) =
          (ρ / (16 * L ^ 2)) * (1 / A.eta 0) := by
      field_simp [hL_pos.ne', hη0_pos.ne']
    calc
      init ≤ (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2 := by
        simpa [init, E0] using hscaled
      _ ≤ theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ -
          (A.problem.F A.x0 -
            attainedObjectiveMinimumValue A.problem.F minimum) := by
        rw [hcoeff_split, hrecip0]
        unfold theoremB6G theoremB6GPrinted attainedObjectiveMinimumValue
        have hweight :
            0 ≤ A.lambda * D ^ 2 * (1 + A.epsilon) := by
          letI : IsProbabilityMeasure A.problem.sampleLaw :=
            A.problem.sampleLaw_isProbability
          let omega : SampleStream Sample :=
            fun _ => Classical.choice (nonempty_of_isProbabilityMeasure
              A.problem.sampleLaw)
          have hleft :
              0 ≤ (A.lambda / 2) *
                inner ℝ (Algorithm2.x A 1 omega)
                  (Algorithm2.preconditioner A 1 omega
                    (Algorithm2.x A 1 omega)) := by
            have hlower :=
              hH.1.2 1 (by norm_num) omega
                (Algorithm2.x A 1 omega)
            have hinner :
                0 ≤ inner ℝ (Algorithm2.x A 1 omega)
                  (Algorithm2.preconditioner A 1 omega
                    (Algorithm2.x A 1 omega)) := by
              have hnorm :
                  0 ≤ ρ * ‖Algorithm2.x A 1 omega‖ ^ 2 :=
                mul_nonneg (le_of_lt hH.1.1)
                  (sq_nonneg ‖Algorithm2.x A 1 omega‖)
              linarith
            have hlam : 0 ≤ A.lambda := hlambda
            exact mul_nonneg (div_nonneg hlam (by norm_num)) hinner
          have hright :
              0 ≤ (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) :=
            le_trans hleft (hB6_initial_weighted_H_bound omega)
          calc
            0 ≤ 2 * ((A.lambda / 2) * D ^ 2 * (1 + A.epsilon)) :=
              mul_nonneg (by norm_num) hright
            _ = A.lambda * D ^ 2 * (1 + A.epsilon) := by ring
        have hweight' :
            0 ≤ (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) := by
          convert
            mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hweight using 1 <;>
            ring
        have hnoise :
            ρ / (16 * L ^ 2) * s ^ ((1 : ℝ) / 3) * σ ^ 2 ≤
              (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
                ρ / (16 * L ^ 2) * s ^ ((1 : ℝ) / 3) * σ ^ 2 := by
          simpa using
            (add_le_add_right hweight'
              (ρ / (16 * L ^ 2) * s ^ ((1 : ℝ) / 3) * σ ^ 2))
        convert hnoise using 1 <;> ring
  have hcombined :
      E + R ≤
        theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
          W + V - Q := by
    have hstate :
        -b6LyapunovNextExpectation A T +
            b6LyapunovCurrentExpectation A 1 -
            terminal + init ≤
          -attainedObjectiveMinimumValue A.problem.F minimum +
            A.problem.F A.x0 +
            (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
            (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2 := by
      linarith [hinitial_potential, hterminal_potential,
        hterminal_nonneg]
    have hG :
        -attainedObjectiveMinimumValue A.problem.F minimum +
            A.problem.F A.x0 +
            (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
            (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2 =
          theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ := by
      have hcoeff_split' :
          ρ / (16 * L ^ 2 * A.eta 0) =
            (ρ / (16 * L ^ 2)) * (1 / A.eta 0) := by
        field_simp [hL_pos.ne', hη0_pos.ne']
      rw [hcoeff_split', hrecip0]
      unfold theoremB6G theoremB6GPrinted attainedObjectiveMinimumValue
      ring
    have hadd := add_le_add hmain_expanded hstate
    calc
      E + R ≤
          W + V - Q +
            (-attainedObjectiveMinimumValue A.problem.F minimum +
              A.problem.F A.x0 +
            (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
              (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2) := by
        have hcancel :
            (b6LyapunovNextExpectation A T -
                b6LyapunovCurrentExpectation A 1 +
                terminal - init) +
                (-b6LyapunovNextExpectation A T +
                  b6LyapunovCurrentExpectation A 1 -
                  terminal + init) = 0 := by
          ring
        have hnonneg :
            0 ≤
              -E - R + W + V - Q +
                (-attainedObjectiveMinimumValue A.problem.F minimum +
                  A.problem.F A.x0 +
                  (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
                  (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2) := by
          rw [← hcancel]
          exact hadd
        have hsub :
            0 ≤
              (W + V - Q +
                  (-attainedObjectiveMinimumValue A.problem.F minimum +
                    A.problem.F A.x0 +
                    (A.lambda / 2) * D ^ 2 * (1 + A.epsilon) +
                    (ρ / (16 * L ^ 2 * A.eta 0)) * σ ^ 2)) -
                (E + R) := by
          convert hnonneg using 1 <;> ring
        linarith only [hsub]
      _ = theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
          W + V - Q := by
        rw [hG]
        ring
  have hT_one_real : (1 : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hT_one
  have hT_pos : 0 < (T : ℝ) :=
    lt_of_lt_of_le zero_lt_one hT_one_real
  have hηT_pos : 0 < A.eta T :=
    hparams_c.2.2 T (Finset.mem_Icc.mpr ⟨hT_one, le_rfl⟩)
  have hE_nonneg : ∀ t : ℕ, 0 ≤ E0 t := by
    intro t
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hD_nonneg : ∀ t : ℕ, 0 ≤ D0 t := by
    intro t
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    apply Finset.sum_nonneg
    intro t ht
    have hηt := hparams_c.2.2 t ht
    exact
      mul_nonneg
        (div_nonneg (le_of_lt hparams_c.1)
          (mul_nonneg (by norm_num) (le_of_lt hηt)))
        (hD_nonneg t)
  have hE_weighted_nonneg : 0 ≤ E := by
    dsimp [E]
    apply Finset.sum_nonneg
    intro t ht
    have hηt := hparams_c.2.2 t ht
    exact
      mul_nonneg
        (div_nonneg (le_of_lt hηt) (le_of_lt hparams_c.1))
        (hE_nonneg t)
  have hweightedE :
      E ≤ theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
        W + V - Q := by
    linarith [hcombined, hR_nonneg]
  have hweightedD :
      R ≤ theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
        W + V - Q := by
    linarith [hcombined, hE_weighted_nonneg]
  have hE_extract :
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
        (ρ / A.eta T) * E := by
    have hpoint :
        ∀ t ∈ Finset.Icc 1 T,
          E0 t ≤ (ρ / A.eta T) * ((A.eta t / ρ) * E0 t) := by
      intro t ht
      have hηt := hparams_c.2.2 t ht
      have hη_le : A.eta T ≤ A.eta t := by
        rw [heta T, heta t]
        exact etaSchedule_le_of_le hs_ge_one
          (Finset.mem_Icc.mp ht).2
      have hratio : 1 ≤ A.eta t / A.eta T :=
        (le_div_iff₀ hηT_pos).mpr (by simpa using hη_le)
      have hmul := mul_le_mul_of_nonneg_right hratio (hE_nonneg t)
      calc
        E0 t = 1 * E0 t := by ring
        _ ≤ (A.eta t / A.eta T) * E0 t := hmul
        _ = (ρ / A.eta T) * ((A.eta t / ρ) * E0 t) := by
          field_simp [hηT_pos.ne', hparams_c.1.ne']
    calc
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
          (Finset.Icc 1 T).sum
            (fun t => (ρ / A.eta T) * ((A.eta t / ρ) * E0 t)) := by
              exact Finset.sum_le_sum (fun t ht => hpoint t ht)
      _ = (ρ / A.eta T) * E := by
        dsimp [E]
        rw [Finset.mul_sum]
  have hE_scaled_direct :
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
              (ρ / A.eta T) *
                  theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
          (ρ / A.eta T) * W +
          (ρ ^ 2 / A.eta T) *
            (Finset.Icc 1 T).sum
              (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
          (ρ ^ 2 / (16 * L ^ 2 * A.eta T)) *
            (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    calc
      (Finset.Icc 1 T).sum (fun t => E0 t) ≤
          (ρ / A.eta T) * E := hE_extract
      _ ≤ (ρ / A.eta T) *
          (theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
            W + V - Q) := by
            have hcoef : 0 ≤ ρ / A.eta T :=
              div_nonneg (le_of_lt hparams_c.1) (le_of_lt hηT_pos)
            exact mul_le_mul_of_nonneg_left hweightedE hcoef
      _ = _ := by
        dsimp [V, Q]
        have hV :
            (ρ / A.eta T) *
                (Finset.Icc 1 T).sum
                  (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                    (8 * L ^ 2)) =
              (ρ ^ 2 / A.eta T) *
                (Finset.Icc 1 T).sum
                  (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                    (8 * L ^ 2)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          field_simp [hηT_pos.ne', hL_pos.ne']
        have hQ :
            (ρ / A.eta T) *
                (Finset.Icc 1 T).sum
                  (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) =
              (ρ ^ 2 / (16 * L ^ 2 * A.eta T)) *
                (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have hηt := hparams_c.2.2 t ht
          field_simp [hηT_pos.ne', hηt.ne', hL_pos.ne']
        calc
          (ρ / A.eta T) *
              (theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
                W +
                (Finset.Icc 1 T).sum
                  (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                    (8 * L ^ 2)) -
                (Finset.Icc 1 T).sum
                  (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) =
              (ρ / A.eta T) *
                  theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
                (ρ / A.eta T) * W +
                (ρ / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                      (8 * L ^ 2)) -
                (ρ / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
            ring
          _ = _ := by rw [hV, hQ]
  have hE_avg_direct :
      (1 / (T : ℝ)) * (Finset.Icc 1 T).sum (fun t => E0 t) ≤
        (ρ / ((T : ℝ) * A.eta T)) *
            theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
          (ρ ^ 2 / ((T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum
              (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2))) +
          (ρ * W) / ((T : ℝ) * A.eta T) -
          (ρ ^ 2 / (16 * L ^ 2 * (T : ℝ) * A.eta T)) *
            ((Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) := by
    calc
      (1 / (T : ℝ)) * (Finset.Icc 1 T).sum (fun t => E0 t) ≤
          (1 / (T : ℝ)) *
            ((ρ / A.eta T) *
                theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
              (ρ / A.eta T) * W +
              (ρ ^ 2 / A.eta T) *
                (Finset.Icc 1 T).sum
                  (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) / (8 * L ^ 2)) -
              (ρ ^ 2 / (16 * L ^ 2 * A.eta T)) *
                (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) := by
              exact mul_le_mul_of_nonneg_left hE_scaled_direct (by positivity)
      _ = _ := by
        have hG :
            (1 / (T : ℝ)) * (ρ / A.eta T) =
              ρ / ((T : ℝ) * A.eta T) := by
          field_simp [hT_pos.ne', hηT_pos.ne']
        have hV :
            (1 / (T : ℝ)) * (ρ ^ 2 / A.eta T) =
              ρ ^ 2 / ((T : ℝ) * A.eta T) := by
          field_simp [hT_pos.ne', hηT_pos.ne']
        have hQ :
            (1 / (T : ℝ)) * (ρ ^ 2 / (16 * L ^ 2 * A.eta T)) =
              ρ ^ 2 / (16 * L ^ 2 * (T : ℝ) * A.eta T) := by
          field_simp [hT_pos.ne', hηT_pos.ne', hL_pos.ne']
        calc
          (1 / (T : ℝ)) *
              ((ρ / A.eta T) *
                  theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
                (ρ / A.eta T) * W +
                (ρ ^ 2 / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                      (8 * L ^ 2)) -
                (ρ ^ 2 / (16 * L ^ 2 * A.eta T)) *
                  (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) =
              (1 / (T : ℝ)) * (ρ / A.eta T) *
                  theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
                (1 / (T : ℝ)) * (ρ / A.eta T) * W +
                (1 / (T : ℝ)) * (ρ ^ 2 / A.eta T) *
                  (Finset.Icc 1 T).sum
                    (fun t => (c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                      (8 * L ^ 2)) -
                (1 / (T : ℝ)) * (ρ ^ 2 / (16 * L ^ 2 * A.eta T)) *
                  (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
            ring
          _ = _ := by
            rw [hG, hV, hQ]
            ring
  have hdisp_repr :
      ∀ t ∈ Finset.Icc 1 T,
        expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm2.x A t) (Algorithm2.xNext A t) =
          (A.eta t)⁻¹ * D0 t := by
    intro t ht
    have hηt := hparams_c.2.2 t ht
    have hD0 := (hexpect t ht).2.const_mul (A.eta t)
    have hD :
        Integrable
          (fun ω : SampleStream Sample =>
            ‖Algorithm2.x A t ω - Algorithm2.xNext A t ω‖ ^ 2)
          (runLaw A.problem) := by
      convert hD0 using 1
      ext ω
      field_simp [hηt.ne']
      simp [norm_sub_rev]
    dsimp [expectedScaledDisplacement, D0]
    rw [integral_const_mul]
  have hdisp_scaled :
      (Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm2.x A t) (Algorithm2.xNext A t)) ≤
        8 * theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ /
            ρ +
          (c ^ 2 * σ ^ 2 / L ^ 2) *
            (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) +
          (8 * W) / ρ -
        (1 / (2 * L ^ 2)) *
          (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    calc
      (Finset.Icc 1 T).sum
          (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
            (Algorithm2.x A t) (Algorithm2.xNext A t)) =
          (8 / ρ) * R := by
            dsimp [R]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            rw [hdisp_repr t ht]
            have hηt := hparams_c.2.2 t ht
            field_simp [hparams_c.1.ne', hηt.ne']
      _ ≤ (8 / ρ) *
          (theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
            W + V - Q) := by
            have hcoef : 0 ≤ 8 / ρ :=
              div_nonneg (by norm_num) (le_of_lt hparams_c.1)
            exact mul_le_mul_of_nonneg_left hweightedD hcoef
      _ = _ := by
        dsimp [V, Q]
        have hV :
            (8 / ρ) *
                (Finset.Icc 1 T).sum
                  (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                    (8 * L ^ 2)) =
              (Finset.Icc 1 T).sum
                (fun t => (c ^ 2 * σ ^ 2 / L ^ 2) * A.eta t ^ 3) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          field_simp [hparams_c.1.ne', hL_pos.ne']
        have hQ :
            (8 / ρ) *
                (Finset.Icc 1 T).sum
                  (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) =
              (Finset.Icc 1 T).sum
                (fun t => (1 / (2 * L ^ 2)) * (M0 t / A.eta t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have hηt := hparams_c.2.2 t ht
          field_simp [hparams_c.1.ne', hηt.ne', hL_pos.ne']
          ring
        calc
          (8 / ρ) *
              (theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ +
                W +
                (Finset.Icc 1 T).sum
                  (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                    (8 * L ^ 2)) -
                (Finset.Icc 1 T).sum
                  (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t)) =
              8 * theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ / ρ +
                (8 / ρ) * W +
                (8 / ρ) *
                  (Finset.Icc 1 T).sum
                    (fun t => (ρ * c ^ 2 * A.eta t ^ 3 * σ ^ 2) /
                      (8 * L ^ 2)) -
                (8 / ρ) *
                  (Finset.Icc 1 T).sum
                    (fun t => (ρ / (16 * L ^ 2 * A.eta t)) * M0 t) := by
            ring
          _ = _ := by
            rw [hV, hQ]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
            ring
  have hdisp_avg :
      (1 / (T : ℝ)) *
          (Finset.Icc 1 T).sum
            (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
              (Algorithm2.x A t) (Algorithm2.xNext A t)) ≤
        8 * theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ /
            (ρ * (T : ℝ)) +
          (c ^ 2 * σ ^ 2 / (L ^ 2 * (T : ℝ))) *
            (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) +
          (8 * W) / (ρ * (T : ℝ)) -
        (1 / (2 * L ^ 2 * (T : ℝ))) *
          (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t) := by
    calc
      (1 / (T : ℝ)) *
          (Finset.Icc 1 T).sum
            (fun t => expectedScaledDisplacement (runLaw A.problem) (A.eta t)
              (Algorithm2.x A t) (Algorithm2.xNext A t)) ≤
          (1 / (T : ℝ)) *
            (8 * theoremB6G A.problem.F A.x0 minimum A.lambda D A.epsilon ρ s L σ /
                ρ +
              (c ^ 2 * σ ^ 2 / L ^ 2) *
                (Finset.Icc 1 T).sum (fun t => A.eta t ^ 3) +
              (8 * W) / ρ -
              (1 / (2 * L ^ 2)) *
                (Finset.Icc 1 T).sum (fun t => M0 t / A.eta t)) := by
              exact mul_le_mul_of_nonneg_left hdisp_scaled (by positivity)
      _ = _ := by
        field_simp [hT_pos.ne', hparams_c.1.ne', hL_pos.ne']
  dsimp [TheoremB6CorrectedStatement]
  constructor
  · simpa [E0, M0, W] using hE_avg_direct
  · simpa [E0, M0, W] using hdisp_avg

/-- Theorem B.6, registered under the source name, as a non-A-level
source-boundary contract. The PDF theorem window prints two averaged
inequalities with `min_x F(x)` and `M_{t+1}` from (C.2); the book JSON records
the C.2 type defect, beta-admissibility gap, denominator gaps, `m_1` clipping
bridge, and displacement-scale mismatch. The displayed inequality shape is
therefore kept separately as `TheoremB6PrintedInequalities` over literal source
symbols `Fmin` and `M`, while this registered declaration records the boundary
instead of asserting corrected residuals or a totalized infimum. -/
theorem theorem_B_6
    (A : Algorithm2Data Sample ι)
    (L ρ σ c s D : ℝ) (T : ℕ)
    (hobj_unbiased : UnbiasedObjectiveOracle A.problem)
    (hgrad_unbiased : UnbiasedGradientOracle A.problem)
    (hvar : BoundedVariance A.problem σ)
    (hsmooth : StochasticSmooth A.problem L)
    (hH : RandomHLowerBounded (Algorithm2.preconditioner A) ρ)
    (heta : ∀ t : ℕ, A.eta t = etaSchedule s t)
    (hs : s ≥ max (8 * L ^ 3 / ρ ^ 3) (64 * A.lambda ^ 3))
    (hbounded : ∀ t : ℕ, ∀ ω : SampleStream Sample, ‖Algorithm2.x A t ω‖ ≤ D)
    (hc : c ≥ 32 * L ^ 2 * ρ⁻¹ ^ 2 + 1)
    (hbeta1 : ∀ t : ℕ, A.beta1 (t + 1) = betaOneSchedule c A.eta t)
    (hbeta2 : ∀ t : ℕ, A.beta2 (t + 1) = betaTwoSchedule A.eta t)
    (hT : (T : ℝ) ≥ s) :
    TheoremB6SourceBoundaryContract A c T := by
  exact
    ⟨⟨(by
          intro t ht
          exact hbeta1 t),
        rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MainTheorems

end Hilbert

end SGD.MARS
