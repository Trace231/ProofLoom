import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import SOptLib.Model.Objective
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Martingale
import SOptLib.Glue.Probability
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope

/-!
# Stochastic Zeroth-Order RSGF Object Layer

This file models the randomized stochastic gradient-free method from FOML,
Section 6.1.  The algorithmic objects are definitions: the stochastic objective
is the expectation of the sample loss, the finite-difference oracle is computed
from two zeroth-order calls, and iterates are generated recursively from the
paper update.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators Gradient InnerProductSpace

namespace Algorithms.Unverified.StochasticZerothOrder

noncomputable section

/-- The paper's decision space `R^n`, represented as the Euclidean Hilbert space
indexed by `Fin n`. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The source regularity class `C_L^{1,1}(R^n)`: differentiability with
`L`-Lipschitz gradient. -/
def CL11 {n : ℕ} (f : Space n → ℝ) (L : ℝ) : Prop :=
  SOptLib.LipschitzGradientObjective f L

/-- The smooth-descent inequality displayed in (6.1.2), derived from
`C_L^{1,1}` in the source. -/
def SmoothDescentBound {n : ℕ} (f : Space n → ℝ) (L : ℝ) : Prop :=
  SOptLib.AbsTaylorRemainderBound f L

/-- Source-derived bridge from `C_L^{1,1}` to the descent inequality (6.1.2). -/
theorem smoothDescentBound_of_CL11 {n : ℕ} {f : Space n → ℝ} {L : ℝ}
    (hf : CL11 f L) :
    SmoothDescentBound f L := by
  rcases hf with ⟨hdiff, hlip⟩
  intro x y
  have hgrad : ∀ z ∈ (Set.univ : Set (Space n)), HasGradientAt f (∇ f z) z := by
    intro z hz
    simpa using (hdiff z).hasGradientAt
  have hgrad_lipschitz :
      ∀ z ∈ (Set.univ : Set (Space n)), ∀ w ∈ (Set.univ : Set (Space n)),
        ‖(fun t : Space n => ∇ f t) z - (fun t : Space n => ∇ f t) w‖ ≤
          L * ‖z - w‖ := by
    intro z hz w hw
    simpa using hlip w z
  exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
    (X := Set.univ) (f := f) (grad := fun z : Space n => ∇ f z) (L := L)
    (by simpa using (convex_univ : Convex ℝ (Set.univ : Set (Space n))))
    hgrad hgrad_lipschitz (by simp) (by simp)

/-- Assumption 13 for the stochastic first-order oracle, including the Borel and
finite-expectation content needed for the displayed expectations to denote the
paper's expectations rather than Lean's total fallback values. -/
def SFOAssumption13 {n : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) (f : Space n → ℝ) (G : Space n → Sample → Space n)
    (σ : ℝ) : Prop :=
  SOptLib.FixedQueryUnbiasedVarianceOracle P G (fun x => ∇ f x) σ


/-- Assumption 15 for the stochastic zeroth-order oracle: the sample function
values have finite expectation and realize the stochastic objective. -/
def SZOAssumption15 {n : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) (F : Space n → Sample → ℝ) (f : Space n → ℝ) :
    Prop :=
  SOptLib.StochasticObjectiveRealization P F f

/-- Source-level data and stated assumptions for the RSGF method.

The objective `f` and all RSGF algorithmic operations are deliberately not fields:
they are constructed below from `F`, `P`, the smoothing parameter, the stepsizes,
and the sample paths. -/
structure Setup (n : ℕ) (Sample : Type*) [MeasurableSpace Sample] where
  /-- The probability law `P` of the zeroth-order sample `ξ`. -/
  P : Measure Sample
  /-- The source calls `P` a probability law. -/
  P_isProbability : IsProbabilityMeasure P
  /-- Sample objective `F(x, ξ)`. -/
  F : Space n → Sample → ℝ
  /-- Initial point `x₁`. -/
  x₁ : Space n
  /-- Stepsizes `{γ_k}`.  The paper uses one-based time indices. -/
  γ : ℕ → ℝ
  /-- Smoothing parameter `μ > 0`. -/
  μ : ℝ
  /-- Smoothness constant `L`. -/
  L : ℝ
  /-- Source scalar domain for the Lipschitz-gradient constant.  The section
  treats `L` as a positive smoothness constant and Theorem 6.3 uses `1/L`. -/
  L_pos : 0 < L
  /-- Variance parameter `σ`. -/
  σ : ℝ
  /-- Source parameter condition `μ > 0`. -/
  μ_pos : 0 < μ
  /-- Assumption 13 states `σ ≥ 0`. -/
  σ_nonneg : 0 ≤ σ
  /-- The base problem assumes `f` is bounded from below. -/
  objective_bddBelow :
    BddBelow (Set.range (fun x : Space n => ∫ ξ, F x ξ ∂P))
  /-- Source `C_L^{1,1}` assumption for the expected objective. -/
  objective_CL11 :
    CL11 (fun x : Space n => ∫ ξ, F x ξ ∂P) L
  /-- Source a.s. sample `C_L^{1,1}` assumption before (6.1.48). -/
  sample_smooth_ae :
    ∀ᵐ ξ ∂P, CL11 (fun x : Space n => F x ξ) L
  /-- Assumption 13, stated for the canonical sample-gradient of `F` and the
  canonical expected objective. -/
  sfo_assumption13 :
    SFOAssumption13 P (fun x : Space n => ∫ ξ, F x ξ ∂P)
      (fun x ξ => gradient (fun y => F y ξ) x) σ
  /-- Assumption 15, stated against the canonical expected objective. -/
  szo_assumption15 :
    SZOAssumption15 P F (fun x : Space n => ∫ ξ, F x ξ ∂P)

variable {n : ℕ} {Sample : Type*} [MeasurableSpace Sample]

/-- Canonical stochastic objective `f(x) = E[F(x, ξ)]` from (6.1.47). -/
noncomputable def objective (S : Setup n Sample) : Space n → ℝ :=
  fun x => ∫ ξ, S.F x ξ ∂S.P

@[simp]
theorem objective_apply (S : Setup n Sample) (x : Space n) :
    objective S x = ∫ ξ, S.F x ξ ∂S.P := by
  rfl

/-- Well-definedness predicate for the source expectation defining `f(x)`. -/
def objectiveValueWellDefined (S : Setup n Sample) (x : Space n) : Prop :=
  Integrable (fun ξ => S.F x ξ) S.P

/-- The source expectation defining `f(x)` is well-defined by Assumption 15. -/
theorem objective_value_wellDefined (S : Setup n Sample) (x : Space n) :
    objectiveValueWellDefined S x := by
  exact S.szo_assumption15.2.1 x

/-- The canonical objective has the source `C_L^{1,1}` regularity. -/
theorem objective_CL11 (S : Setup n Sample) :
    CL11 (objective S) S.L := by
  simpa [objective] using S.objective_CL11

/-- The source smooth-descent inequality (6.1.2) for the canonical objective is
derived from the `C_L^{1,1}` assumption. -/
theorem objective_smoothDescentBound (S : Setup n Sample) :
    SmoothDescentBound (objective S) S.L :=
  smoothDescentBound_of_CL11 (objective_CL11 S)

/-- The canonical objective is bounded from below, as stated before (6.1.2). -/
theorem objective_bddBelow (S : Setup n Sample) :
    BddBelow (Set.range (objective S)) := by
  simpa [objective] using S.objective_bddBelow

/-- The source smoothness constant is positive, so expressions such as `1 / L`
and `D_f` do not rely on Lean's totalized division at zero. -/
theorem L_pos (S : Setup n Sample) : 0 < S.L :=
  S.L_pos

/-- Assumption 13 as it appears in the RSGF proof: the stochastic first-order
oracle is the sample gradient of the same `F` used by the zeroth-order oracle. -/
theorem sampleGradient_sfo_assumption13 (S : Setup n Sample) :
    SFOAssumption13 S.P (objective S)
      (fun x ξ => gradient (fun y => S.F y ξ) x) S.σ := by
  simpa [objective] using S.sfo_assumption13

/-- Assumption 13(a), projected from the source assumption bundle. -/
theorem sfo_unbiased (S : Setup n Sample) (x : Space n) :
    (∫ ξ, gradient (fun y => S.F y ξ) x ∂S.P) = ∇ (objective S) x := by
  exact (sampleGradient_sfo_assumption13 S).2.2.2.1 x

/-- Assumption 13(b), projected from the source assumption bundle. -/
theorem sfo_variance_bound (S : Setup n Sample) (x : Space n) :
    (∫ ξ, ‖gradient (fun y => S.F y ξ) x - ∇ (objective S) x‖ ^ (2 : ℕ) ∂S.P) ≤
      S.σ ^ (2 : ℕ) := by
  exact (sampleGradient_sfo_assumption13 S).2.2.2.2 x

/-- Assumption 13 measurability for the canonical sample-gradient oracle. -/
theorem sampleGradient_measurable (S : Setup n Sample) (x : Space n) :
    Measurable (fun ξ => gradient (fun y => S.F y ξ) x) :=
  (sampleGradient_sfo_assumption13 S).1 x

/-- Assumption 13 integrability for the canonical sample-gradient oracle. -/
theorem sampleGradient_integrable (S : Setup n Sample) (x : Space n) :
    Integrable (fun ξ => gradient (fun y => S.F y ξ) x) S.P :=
  (sampleGradient_sfo_assumption13 S).2.1 x

/-- Assumption 13 controls the second moment of the canonical sample-gradient
oracle.  This is the `E[‖G(x_k, ξ_k)‖²]` term used in (6.1.67), with
`G(x, ξ)` specialized to `∇ₓ F(x, ξ)`. -/
theorem sampleGradient_secondMoment_le (S : Setup n Sample) (x : Space n) :
    (∫ ξ, ‖gradient (fun y => S.F y ξ) x‖ ^ (2 : ℕ) ∂S.P) ≤
      ‖∇ (objective S) x‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  exact oracle_second_moment_le_norm_target_sq_add_variance
    S.P (fun ξ => gradient (fun y => S.F y ξ) x) (∇ (objective S) x) S.σ
    (sampleGradient_integrable S x)
    ((sampleGradient_sfo_assumption13 S).2.2.1 x)
    (sfo_unbiased S x)
    (sfo_variance_bound S x)

/-- Assumption 13 also gives the finite second moment of the canonical
sample-gradient oracle. -/
private theorem sampleGradient_norm_sq_integrable
    (S : Setup n Sample) (x : Space n) :
    Integrable (fun ξ => ‖gradient (fun y => S.F y ξ) x‖ ^ (2 : ℕ)) S.P := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  exact oracle_second_moment_integrable_of_centered_second_moment_integrable
    S.P (fun ξ => gradient (fun y => S.F y ξ) x) (∇ (objective S) x)
    (sampleGradient_integrable S x).aestronglyMeasurable
    ((sampleGradient_sfo_assumption13 S).2.2.1 x)

/-- Canonical optimal value `f* = inf_{x in R^n} f(x)` from (6.1.47). -/
noncomputable def fStar (S : Setup n Sample) : ℝ :=
  SOptLib.objectiveInfimumValue Set.univ (objective S)

@[simp]
theorem fStar_def (S : Setup n Sample) :
    fStar S = sInf ((objective S) '' (Set.univ : Set (Space n))) := by
  simp [fStar, SOptLib.objectiveInfimumValue_def]

/-- Canonical standard-Gaussian direction law for the paper's `u`. -/
noncomputable def gaussianDirectionLaw (n : ℕ) : Measure (Space n) :=
  stdGaussian (Space n)

@[simp]
theorem gaussianDirectionLaw_def (n : ℕ) :
    gaussianDirectionLaw n = stdGaussian (Space n) := by
  rfl

section GaussianRankOneMoment

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local notation "dimE" => (Module.finrank ℝ E : ℝ)

private theorem gaussianReal_second_moment :
    ∫ x : ℝ, x ^ (2 : ℕ) ∂(gaussianReal 0 1) = 1 := by
  exact integral_pow_two_four_six_gaussianReal_zero_one.1

private theorem gaussianReal_fourth_moment :
    ∫ x : ℝ, x ^ (4 : ℕ) ∂(gaussianReal 0 1) = 3 := by
  exact integral_pow_two_four_six_gaussianReal_zero_one.2.1

private theorem gaussianReal_sixth_moment :
    ∫ x : ℝ, x ^ (6 : ℕ) ∂(gaussianReal 0 1) = 15 := by
  exact integral_pow_two_four_six_gaussianReal_zero_one.2.2

private theorem gaussianReal_sq_sq_moment :
    ∫ x : ℝ, (x ^ (2 : ℕ)) * (x ^ (2 : ℕ)) ∂(gaussianReal 0 1) = 3 := by
  calc
    ∫ x : ℝ, (x ^ (2 : ℕ)) * (x ^ (2 : ℕ)) ∂(gaussianReal 0 1)
        = ∫ x : ℝ, x ^ (4 : ℕ) ∂(gaussianReal 0 1) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => by ring
    _ = 3 := gaussianReal_fourth_moment

private theorem pi_gaussian_sq_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    (∫ z : ι → ℝ, (z i) ^ (2 : ℕ)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) = 1 := by
  exact (integral_pi_gaussianReal_square_monomial_three
    (i := i) (j := i) (k := i)).1

private theorem gaussianReal_sq_sq_sq_moment :
    ∫ x : ℝ, (x ^ (2 : ℕ)) * (x ^ (2 : ℕ)) * (x ^ (2 : ℕ))
      ∂(gaussianReal 0 1) = 15 := by
  calc
    ∫ x : ℝ, (x ^ (2 : ℕ)) * (x ^ (2 : ℕ)) * (x ^ (2 : ℕ))
        ∂(gaussianReal 0 1)
        = ∫ x : ℝ, x ^ (6 : ℕ) ∂(gaussianReal 0 1) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => by ring
    _ = 15 := gaussianReal_sixth_moment

private theorem pi_gaussian_sq_sq_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    (∫ z : ι → ℝ, (z i) ^ (2 : ℕ) * (z j) ^ (2 : ℕ)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      if i = j then 3 else 1 := by
  exact (integral_pi_gaussianReal_square_monomial_three
    (i := i) (j := j) (k := i)).2.1

private theorem pi_gaussian_sq_sq_sq_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k : ι) :
    (∫ z : ι → ℝ, (z i) ^ (2 : ℕ) * (z j) ^ (2 : ℕ) * (z k) ^ (2 : ℕ)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
      if i = j then (if j = k then 15 else 3)
      else if i = k then 3 else if j = k then 3 else 1 := by
  exact (integral_pi_gaussianReal_square_monomial_three
    (i := i) (j := j) (k := k)).2.2

private lemma integrable_pi_gaussian_sq_sq_sq_monomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k : ι) :
    Integrable
      (fun z : ι → ℝ => (z i) ^ (2 : ℕ) * (z j) ^ (2 : ℕ) * (z k) ^ (2 : ℕ))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let f : (ι → ℝ) → ℝ :=
    fun z => (z i) ^ (2 : ℕ) * (z j) ^ (2 : ℕ) * (z k) ^ (2 : ℕ)
  have hf_meas : AEStronglyMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    exact ((((continuous_apply i).pow 2).mul ((continuous_apply j).pow 2)).mul
      ((continuous_apply k).pow 2)).aestronglyMeasurable
  have hf_nonneg : ∀ z : ι → ℝ, 0 ≤ f z := by
    intro z
    dsimp [f]
    positivity
  refine ⟨hf_meas, ?_⟩
  have hf_nonneg_ae : 0 ≤ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] f :=
    Filter.Eventually.of_forall hf_nonneg
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hf_nonneg_ae]
  refine lt_top_iff_ne_top.mpr ?_
  have h_toReal :
      ENNReal.toReal (∫⁻ z, ENNReal.ofReal (f z) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
        if i = j then (if j = k then 15 else 3)
        else if i = k then 3 else if j = k then 3 else 1 := by
    simpa [f, MeasureTheory.integral_eq_lintegral_of_nonneg_ae hf_nonneg_ae hf_meas] using
      (pi_gaussian_sq_sq_sq_moment (i := i) (j := j) (k := k))
  intro htop
  rw [htop, ENNReal.toReal_top] at h_toReal
  by_cases hij : i = j
  · by_cases hjk : j = k <;> simp [hij, hjk] at h_toReal
  · by_cases hik : i = k
    · have hkj : k ≠ j := by
        intro h
        exact hij (hik.trans h)
      simp [hij, hik, hkj] at h_toReal
    · by_cases hjk : j = k <;> simp [hij, hik, hjk] at h_toReal

private lemma pi_gaussian_sum_sq_cube_moment_eq (n_nat : ℕ) :
    (∫ z : Fin n_nat → ℝ, (∑ i, (z i) ^ (2 : ℕ)) ^ (3 : ℕ)
      ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1)) =
      (n_nat : ℝ) ^ (3 : ℕ) + 6 * (n_nat : ℝ) ^ (2 : ℕ) + 8 * (n_nat : ℝ) := by
  simpa using (integral_pi_gaussianReal_sum_sq_pow_three (ι := Fin n_nat))

private theorem pi_gaussian_mixed_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i k j : ι) (hik : i ≠ k) :
    (∫ z : ι → ℝ, z i * z k * (z j) ^ (2 : ℕ)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) = 0 := by
  exact integral_pi_gaussianReal_mul_mul_sq_eq_zero_of_ne i k j hik

private lemma integrable_pi_gaussian_sq_sq_monomial
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    Integrable (fun z : ι → ℝ => (z i) ^ (2 : ℕ) * (z j) ^ (2 : ℕ))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let f : (ι → ℝ) → ℝ := fun z => (z i) ^ (2 : ℕ) * (z j) ^ (2 : ℕ)
  have hf_meas : AEStronglyMeasurable f (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    exact (((continuous_apply i).pow 2).mul ((continuous_apply j).pow 2)).aestronglyMeasurable
  have hf_nonneg : ∀ z : ι → ℝ, 0 ≤ f z := by
    intro z
    dsimp [f]
    positivity
  refine ⟨hf_meas, ?_⟩
  have hf_nonneg_ae : 0 ≤ᵐ[Measure.pi fun _ : ι => gaussianReal 0 1] f :=
    Filter.Eventually.of_forall hf_nonneg
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hf_nonneg_ae]
  refine lt_top_iff_ne_top.mpr ?_
  have h_toReal :
      ENNReal.toReal (∫⁻ z, ENNReal.ofReal (f z) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) =
        if i = j then 3 else 1 := by
    simpa [f, MeasureTheory.integral_eq_lintegral_of_nonneg_ae hf_nonneg_ae hf_meas] using
      (pi_gaussian_sq_sq_moment (i := i) (j := j))
  intro htop
  rw [htop, ENNReal.toReal_top] at h_toReal
  by_cases hij : i = j <;> simp [hij] at h_toReal

private lemma integrable_pi_gaussian_cubic_monomial
    {n_nat : ℕ} (i k j : Fin n_nat) :
    Integrable (fun z : Fin n_nat → ℝ => z i * z k * (z j) ^ (2 : ℕ))
      (Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
  let f : (Fin n_nat → ℝ) → ℝ := fun z => z i * z k * (z j) ^ (2 : ℕ)
  let g : (Fin n_nat → ℝ) → ℝ := fun z =>
    (1 / 2 : ℝ) * (((z i) ^ (2 : ℕ) * (z j) ^ (2 : ℕ)) + ((z k) ^ (2 : ℕ) * (z j) ^ (2 : ℕ)))
  have hf_meas : AEStronglyMeasurable f (Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
    exact (((continuous_apply i).mul (continuous_apply k)).mul
      ((continuous_apply j).pow 2)).aestronglyMeasurable
  have hg_int : Integrable g (Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
    simpa [g] using
      ((integrable_pi_gaussian_sq_sq_monomial (i := i) (j := j)).add
        (integrable_pi_gaussian_sq_sq_monomial (i := k) (j := j))).const_mul (1 / 2 : ℝ)
  have hdom : ∀ z : Fin n_nat → ℝ, ‖f z‖ ≤ g z := by
    intro z
    have hj_nonneg : 0 ≤ z j ^ (2 : ℕ) := by positivity
    have habs :
        |z i * z k| ≤ ((z i) ^ (2 : ℕ) + (z k) ^ (2 : ℕ)) / 2 := by
      by_cases hnonneg : 0 ≤ z i * z k
      · rw [abs_of_nonneg hnonneg]
        nlinarith [sq_nonneg (z i - z k)]
      · rw [abs_of_nonpos (le_of_not_ge hnonneg)]
        nlinarith [sq_nonneg (z i + z k)]
    calc
      ‖f z‖ = |z i * z k| * (z j) ^ (2 : ℕ) := by
        simp [f, Real.norm_eq_abs, abs_mul, abs_of_nonneg hj_nonneg, mul_assoc]
      _ ≤ (((z i) ^ (2 : ℕ) + (z k) ^ (2 : ℕ)) / 2) * (z j) ^ (2 : ℕ) := by
        gcongr
      _ = g z := by
        dsimp [g]
        ring
  exact Integrable.mono' hg_int hf_meas (Filter.Eventually.of_forall hdom)

private lemma norm_sq_sum_smul_orthonormalBasis_bridge
    {n_nat : ℕ} (b : OrthonormalBasis (Fin n_nat) ℝ E) (z : Fin n_nat → ℝ) :
    ‖(∑ i, z i • (b i : E) : E)‖ ^ (2 : ℕ) = ∑ i, z i ^ (2 : ℕ) := by
  let y : E := ∑ i, z i • (b i : E)
  have hy_repr : b.repr y = z := by
    dsimp [y]
    rw [OrthonormalBasis.sum_repr_symm]
    simp
  have hcoeff_left : ∀ i : Fin n_nat, ⟪b i, y⟫_ℝ = z i := by
    intro i
    have hi := congrFun hy_repr i
    simpa [OrthonormalBasis.repr_apply_apply] using hi
  have hcoeff_right : ∀ i : Fin n_nat, ⟪y, b i⟫_ℝ = z i := by
    intro i
    rw [real_inner_comm]
    exact hcoeff_left i
  calc
    ‖(∑ i, z i • (b i : E) : E)‖ ^ (2 : ℕ)
        = ⟪y, y⟫_ℝ := by
            dsimp [y]
            simpa using (real_inner_self_eq_norm_sq (∑ i, z i • (b i : E) : E)).symm
    _ = ∑ i, ⟪y, b i⟫_ℝ * ⟪b i, y⟫_ℝ := by
          simpa using (b.sum_inner_mul_inner y y).symm
    _ = ∑ i, z i ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hcoeff_left i, hcoeff_right i]
          ring

private lemma stdGaussian_inner_smul_integrand_in_coordinates
    {n_nat : ℕ} (b : OrthonormalBasis (Fin n_nat) ℝ E) (v : E) :
    ∀ z : Fin n_nat → ℝ,
      ‖⟪v, (∑ i, z i • (b i : E) : E)⟫_ℝ • (∑ i, z i • (b i : E) : E)‖ ^ (2 : ℕ) =
        ((∑ i, ⟪v, b i⟫_ℝ * z i) ^ (2 : ℕ)) * (∑ j, (z j) ^ (2 : ℕ)) := by
  intro z
  have hinner :
      ⟪v, (∑ i, z i • (b i : E) : E)⟫_ℝ = ∑ i, ⟪v, b i⟫_ℝ * z i := by
    calc
      ⟪v, (∑ i, z i • (b i : E) : E)⟫_ℝ = ∑ i, ⟪v, z i • (b i : E)⟫_ℝ := by
        rw [inner_sum]
      _ = ∑ i, z i * ⟪v, b i⟫_ℝ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [inner_smul_right]
      _ = ∑ i, ⟪v, b i⟫_ℝ * z i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
  have hnorm :
      ‖(∑ i, z i • (b i : E) : E)‖ ^ (2 : ℕ) = ∑ j, (z j) ^ (2 : ℕ) := by
    simpa using (norm_sq_sum_smul_orthonormalBasis_bridge (b := b) z)
  have hnorm' :
      ‖(∑ i, z i • (b i : E) : E)‖ * ‖(∑ i, z i • (b i : E) : E)‖ =
        ∑ j, (z j) ^ (2 : ℕ) := by
    simpa [pow_two] using hnorm
  rw [norm_smul, pow_two, hinner]
  calc
    ‖∑ i, ⟪v, b i⟫_ℝ * z i‖ * ‖∑ i, z i • (b i : E)‖ *
        (‖∑ i, ⟪v, b i⟫_ℝ * z i‖ * ‖∑ i, z i • (b i : E)‖)
        =
        (‖∑ i, ⟪v, b i⟫_ℝ * z i‖ * ‖∑ i, ⟪v, b i⟫_ℝ * z i‖) *
          (‖∑ i, z i • (b i : E)‖ * ‖∑ i, z i • (b i : E)‖) := by
            ring
    _ = ((∑ i, ⟪v, b i⟫_ℝ * z i) ^ (2 : ℕ)) * (∑ j, (z j) ^ (2 : ℕ)) := by
          rw [hnorm']
          let s : ℝ := ∑ i, ⟪v, b i⟫_ℝ * z i
          have habs :
              |s| * |s| = s ^ (2 : ℕ) := by
            calc
              |s| * |s| = |s| ^ (2 : ℕ) := by simp [pow_two]
              _ = s ^ (2 : ℕ) := by
                    simpa [pow_two] using (sq_abs s)
          rw [Real.norm_eq_abs, habs]

private lemma pi_gaussian_rank_one_fourth_moment_collapse
    {n_nat : ℕ} (a : Fin n_nat → ℝ) :
    (∫ z : Fin n_nat → ℝ,
        ((∑ i, a i * z i) ^ (2 : ℕ)) * (∑ j, (z j) ^ (2 : ℕ))
        ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1)) =
      (((n_nat : ℝ) + 2) * ∑ i, (a i) ^ (2 : ℕ)) := by
  simpa using (integral_pi_gaussianReal_linear_sq_mul_sum_sq (ι := Fin n_nat) a)

private lemma orthonormal_basis_coeff_sq_sum_eq_norm_sq
    {n_nat : ℕ} (b : OrthonormalBasis (Fin n_nat) ℝ E) (v : E) :
    (∑ i, ⟪v, b i⟫_ℝ ^ (2 : ℕ)) = ‖v‖ ^ (2 : ℕ) := by
  calc
    ∑ i, ⟪v, b i⟫_ℝ ^ (2 : ℕ) = ∑ i, ⟪v, b i⟫_ℝ * ⟪b i, v⟫_ℝ := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [real_inner_comm]
      ring
    _ = ⟪v, v⟫_ℝ := by
          simpa using (b.sum_inner_mul_inner v v)
    _ = ‖v‖ ^ (2 : ℕ) := by
          simpa using (real_inner_self_eq_norm_sq v)

private theorem integral_norm_inner_smul_sq_stdGaussian_eq
    (v : E) :
    (∫ u : E, ‖⟪v, u⟫_ℝ • u‖ ^ (2 : ℕ) ∂(stdGaussian E)) =
      (dimE + 2) * ‖v‖ ^ (2 : ℕ) := by
  simpa using (integral_norm_inner_smul_sq_stdGaussian (E := E) v)

end GaussianRankOneMoment

/-- Gaussian smoothing `f^μ(x) = E_u[f(x + μu)]` from (6.1.49), applied to the
canonical stochastic objective. -/
noncomputable def gaussianSmoothing (S : Setup n Sample) : Space n → ℝ :=
  SOptLib.gaussianSmoothing (objective S) S.μ

@[simp]
theorem gaussianSmoothing_apply (S : Setup n Sample) (x : Space n) :
    gaussianSmoothing S x =
      ∫ u, objective S (x + S.μ • u) ∂gaussianDirectionLaw n := by
  rw [gaussianSmoothing, SOptLib.gaussianSmoothing_apply, gaussianDirectionLaw_def]

/-- Finite-difference zeroth-order oracle `G_μ` from (6.1.58). -/
def rsgfOracle (S : Setup n Sample) (x : Space n) (ξ : Sample) (u : Space n) :
    Space n :=
  SOptLib.forwardDifferenceOracle S.F S.μ x ξ u

@[simp]
theorem rsgfOracle_def (S : Setup n Sample) (x : Space n) (ξ : Sample) (u : Space n) :
    rsgfOracle S x ξ u =
      ((S.F (x + S.μ • u) ξ - S.F x ξ) / S.μ) • u := by
  rfl

/-- One RSGF update step from (6.1.59). -/
def rsgfStep (S : Setup n Sample) (k : ℕ) (x : Space n) (ξ : Sample) (u : Space n) :
    Space n :=
  x - S.γ k • rsgfOracle S x ξ u

@[simp]
theorem rsgfStep_def (S : Setup n Sample) (k : ℕ) (x : Space n) (ξ : Sample)
    (u : Space n) :
    rsgfStep S k x ξ u = x - S.γ k • rsgfOracle S x ξ u := by
  rfl


/-- Fixed-direction form of Assumption 15 for the RSGF finite-difference
oracle: after integrating over the sample coordinate, the stochastic function
values become the canonical objective values. -/
private theorem rsgfOracle_sample_integral_eq_objective_forward_difference
    (S : Setup n Sample) (x u : Space n) :
    (∫ ξ, rsgfOracle S x ξ u ∂S.P) =
      (((objective S (x + S.μ • u) - objective S x) / S.μ) • u) := by
  exact
    integral_forwardDifferenceOracle_eq_forwardDifference_objective_of_integral_eq
      (P := S.P) (F := S.F) (f := objective S) (μ := S.μ) (x := x) (u := u)
      (S.szo_assumption15.2.1 (x + S.μ • u))
      (S.szo_assumption15.2.1 x)
      (by simpa [objective] using S.szo_assumption15.2.2 (x + S.μ • u))
      (by simpa [objective] using S.szo_assumption15.2.2 x)

/-- Product-law version of the fixed-direction Assumption 15 bridge, isolated
from the integrability proof needed to justify Fubini for the RSGF oracle. -/
private theorem rsgfOracle_product_integral_eq_objective_forward_difference_of_integrable
    (S : Setup n Sample) (x : Space n)
    (h_int : Integrable
      (fun z : Sample × Space n => rsgfOracle S x z.1 z.2)
      (S.P.prod (gaussianDirectionLaw n))) :
    (∫ z : Sample × Space n,
        rsgfOracle S x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) =
      ∫ u : Space n,
          (((objective S (x + S.μ • u) - objective S x) / S.μ) • u)
          ∂gaussianDirectionLaw n := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  letI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  exact integral_prod_eq_integral_fiber_integral_of_integrable
    (muA := gaussianDirectionLaw n) (muB := S.P)
    (K := fun u ξ => rsgfOracle S x ξ u)
    (M := fun u => (((objective S (x + S.μ • u) - objective S x) / S.μ) • u))
    h_int
    (Filter.Eventually.of_forall fun u =>
      rsgfOracle_sample_integral_eq_objective_forward_difference S x u)

/-- Product-law a.e. strong measurability of the finite-difference oracle. -/
private theorem rsgfOracle_aestronglyMeasurable
    (S : Setup n Sample) (x : Space n) :
    AEStronglyMeasurable
      (fun z : Sample × Space n => rsgfOracle S x z.1 z.2)
      (S.P.prod (gaussianDirectionLaw n)) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  letI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  have hsample_smooth : ∀ᵐ ξ ∂S.P, CL11 (fun y : Space n => S.F y ξ) S.L :=
    S.sample_smooth_ae
  have hswap_aesm :
      AEStronglyMeasurable
        (fun p : Space n × Sample => rsgfOracle S x p.2 p.1)
        ((gaussianDirectionLaw n).prod S.P) := by
    refine aestronglyMeasurable_prod_of_continuous_ae_of_fiber
      (νQ := gaussianDirectionLaw n) (νSample := S.P)
      (kernel := fun u ξ => rsgfOracle S x ξ u)
      (queryPoint := fun u : Space n => u) ?_ ?_ ?_
    · exact continuous_id.stronglyMeasurable
    · filter_upwards [hsample_smooth] with ξ hξ
      unfold rsgfOracle
      have hcont1 : Continuous fun u : Space n => S.F (x + S.μ • u) ξ := by
        exact hξ.1.continuous.comp
          (continuous_const.add (continuous_const.smul continuous_id))
      have hcont0 : Continuous fun _u : Space n => S.F x ξ := continuous_const
      exact (((hcont1.sub hcont0).div_const S.μ).smul continuous_id)
    · intro u
      unfold rsgfOracle
      have hplus : Measurable fun ξ => S.F (x + S.μ • u) ξ :=
        S.szo_assumption15.1 (x + S.μ • u)
      have hx : Measurable fun ξ => S.F x ξ := S.szo_assumption15.1 x
      exact (((hplus.sub hx).div_const S.μ).smul_const u).aestronglyMeasurable
  simpa [Function.comp_def] using hswap_aesm.prod_swap

/-- Law-scoped random-query measurability for the RSGF oracle.  This avoids a
global joint-measurability assumption on `(x, ξ, u) ↦ G_μ(x, ξ, u)`; the query
is first represented as a strongly measurable map and the sample-wise `CL11`
assumption supplies continuity in the query variable for product-a.e. samples. -/
private theorem rsgfOracle_random_query_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (S : Setup n Sample) (X : Ω → Space n)
    (hX : StronglyMeasurable X) :
    AEStronglyMeasurable
      (fun p : Ω × (Sample × Space n) =>
        rsgfOracle S (X p.1) p.2.1 p.2.2)
      (ν.prod (S.P.prod (gaussianDirectionLaw n))) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : SFinite (S.P.prod (gaussianDirectionLaw n)) := inferInstance
  refine aestronglyMeasurable_prod_of_continuous_ae_of_fiber
    (νQ := ν) (νSample := S.P.prod (gaussianDirectionLaw n))
    (kernel := fun x z => rsgfOracle S x z.1 z.2)
    (queryPoint := X) hX ?_ ?_
  · have hsmooth_prod :
        ∀ᵐ z : Sample × Space n ∂(S.P.prod (gaussianDirectionLaw n)),
          CL11 (fun y : Space n => S.F y z.1) S.L := by
      rcases S.sample_smooth_ae.exists_measurable_mem with
        ⟨A, hA_ae, hA_meas, hA_sub⟩
      have hprod_A :
          ∀ᵐ z : Sample × Space n ∂(S.P.prod (gaussianDirectionLaw n)),
            z ∈ A ×ˢ (Set.univ : Set (Space n)) := by
        rw [Measure.ae_prod_mem_iff_ae_ae_mem
          (hA_meas.prod MeasurableSet.univ)]
        filter_upwards [hA_ae] with ξ hξ
        exact Filter.Eventually.of_forall fun _u : Space n => ⟨hξ, trivial⟩
      filter_upwards [hprod_A] with z hz
      exact hA_sub z.1 hz.1
    exact hsmooth_prod.mono (fun z hξ => by
      unfold rsgfOracle
      have hcont_shift :
          Continuous fun x : Space n => S.F (x + S.μ • z.2) z.1 := by
        exact hξ.1.continuous.comp (continuous_id.add continuous_const)
      have hcont_base : Continuous fun x : Space n => S.F x z.1 :=
        hξ.1.continuous
      exact (((hcont_shift.sub hcont_base).div_const S.μ).smul continuous_const))
  · intro x
    exact rsgfOracle_aestronglyMeasurable S x

/-- A.e.-strongly-measurable random-query variant of
`rsgfOracle_random_query_aestronglyMeasurable`, obtained by replacing the query
with a strongly measurable representative under the product law. -/
private theorem rsgfOracle_random_query_aestronglyMeasurable_of_aesm
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (S : Setup n Sample) (X : Ω → Space n)
    (hX : AEStronglyMeasurable X ν) :
    AEStronglyMeasurable
      (fun p : Ω × (Sample × Space n) =>
        rsgfOracle S (X p.1) p.2.1 p.2.2)
      (ν.prod (S.P.prod (gaussianDirectionLaw n))) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : SFinite (S.P.prod (gaussianDirectionLaw n)) := inferInstance
  exact aestronglyMeasurable_prod_of_continuous_ae_of_fiber_of_aestronglyMeasurable
    (νQ := ν) (νSample := S.P.prod (gaussianDirectionLaw n))
    (kernel := fun x z => rsgfOracle S x z.1 z.2)
    (queryPoint := X) hX
    (fun X' hX' => rsgfOracle_random_query_aestronglyMeasurable S X' hX')

/-- Pointwise CL11 Taylor-remainder split for Lemma 6.2(b)/(6.1.53). -/
private theorem gaussian_forward_oracle_norm_sq_pointwise_bound_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x : Space n)
    (hf : CL11 f L) (_hL : 0 < L) (hμ : 0 < μ) :
    ∀ u : Space n,
      ‖(((f (x + μ • u) - f x) / μ) • u : Space n)‖ ^ (2 : ℕ) ≤
        2 * ‖((⟪∇ f x, u⟫_ℝ) • u : Space n)‖ ^ (2 : ℕ) +
          (μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2) * ‖u‖ ^ (6 : ℕ) := by
  simpa [CL11] using
    (SOptLib.norm_sq_forward_difference_smul_le_of_lipschitz_gradient
      (E := Space n) (f := f) (L := L) (μ := μ) (x := x)
      (hf := by simpa [CL11] using hf)
      (hL := _hL.le) (hμ := hμ))

/-- Pointwise CL11 Taylor-remainder bound for the forward-difference vector
after subtracting the Gaussian linear term. -/
private theorem gaussian_forward_difference_linear_remainder_norm_le_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x u : Space n)
    (hf : CL11 f L) (_hL : 0 < L) (hμ : 0 < μ) :
    ‖(((f (x + μ • u) - f x) / μ) • u : Space n) -
        ((⟪∇ f x, u⟫_ℝ) • u : Space n)‖ ≤
      (μ * L / 2) * ‖u‖ ^ (3 : ℕ) := by
  let a : ℝ := (f (x + μ • u) - f x) / μ
  let b : ℝ := ⟪∇ f x, u⟫_ℝ
  let r : ℝ := a - b
  have hdes := (smoothDescentBound_of_CL11 hf) x (x + μ • u)
  have hsub : (x + μ • u) - x = μ • u := by
    abel
  have hdes' :
      |f (x + μ • u) - f x - μ * b| ≤
        L / 2 * (μ * ‖u‖) ^ (2 : ℕ) := by
    simpa [b, hsub, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hμ.le]
      using hdes
  have hr_abs : |r| ≤ (μ * L / 2) * ‖u‖ ^ (2 : ℕ) := by
    have ha :
        r = (f (x + μ • u) - f x - μ * b) / μ := by
      dsimp [r, a]
      field_simp [hμ.ne']
    rw [ha, abs_div]
    calc
      |f (x + μ • u) - f x - μ * b| / |μ|
          ≤ (L / 2 * (μ * ‖u‖) ^ (2 : ℕ)) / |μ| := by
              exact div_le_div_of_nonneg_right hdes' (abs_nonneg μ)
      _ = (μ * L / 2) * ‖u‖ ^ (2 : ℕ) := by
              rw [abs_of_pos hμ]
              field_simp [hμ.ne']
  have hdiff :
      (((f (x + μ • u) - f x) / μ) • u : Space n) -
          ((⟪∇ f x, u⟫_ℝ) • u : Space n) =
        r • u := by
    have ha : (f (x + μ • u) - f x) / μ - b = r := by
      dsimp [r, a]
    rw [← sub_smul, ha]
  calc
    ‖(((f (x + μ • u) - f x) / μ) • u : Space n) -
        ((⟪∇ f x, u⟫_ℝ) • u : Space n)‖
        = ‖r • u‖ := by rw [hdiff]
    _ = |r| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ((μ * L / 2) * ‖u‖ ^ (2 : ℕ)) * ‖u‖ := by
          exact mul_le_mul_of_nonneg_right hr_abs (norm_nonneg u)
    _ = (μ * L / 2) * ‖u‖ ^ (3 : ℕ) := by ring

/-- The linear Gaussian rank-one term has finite square moment. -/
private theorem gaussian_linear_oracle_norm_sq_integrable
    (g : Space n) :
    Integrable (fun u : Space n => ‖((⟪g, u⟫_ℝ) • u : Space n)‖ ^ (2 : ℕ))
      (gaussianDirectionLaw n) := by
  simpa [gaussianDirectionLaw_def] using
    (integrable_norm_inner_smul_sq_stdGaussian (E := Space n) g)

/-- The rank-one Gaussian fourth-moment term in Lemma 6.2(b), weakened from
the exact `(n + 2)` constant to the source's `(n + 4)` envelope. -/
private theorem gaussian_linear_oracle_norm_sq_integral_le
    (g : Space n) :
    (∫ u : Space n, ‖((⟪g, u⟫_ℝ) • u : Space n)‖ ^ (2 : ℕ)
      ∂gaussianDirectionLaw n) ≤
      ((n : ℝ) + 4) * ‖g‖ ^ (2 : ℕ) := by
  rw [gaussianDirectionLaw_def]
  have heq :
      (∫ u : Space n, ‖((⟪g, u⟫_ℝ) • u : Space n)‖ ^ (2 : ℕ)
        ∂stdGaussian (Space n)) =
        (((Module.finrank ℝ (Space n) : ℝ) + 2) * ‖g‖ ^ (2 : ℕ)) := by
    simpa using (integral_norm_inner_smul_sq_stdGaussian_eq (E := Space n) g)
  have hdim :
      ((Module.finrank ℝ (Space n) : ℝ) + 2) * ‖g‖ ^ (2 : ℕ) =
        ((n : ℝ) + 2) * ‖g‖ ^ (2 : ℕ) := by
    simp [Space]
  calc
    (∫ u : Space n, ‖((⟪g, u⟫_ℝ) • u : Space n)‖ ^ (2 : ℕ)
        ∂stdGaussian (Space n))
        = ((n : ℝ) + 2) * ‖g‖ ^ (2 : ℕ) := by
          rw [heq, hdim]
    _ ≤ ((n : ℝ) + 4) * ‖g‖ ^ (2 : ℕ) := by
          have hsq : 0 ≤ ‖g‖ ^ (2 : ℕ) := by positivity
          nlinarith

/-- Vector Stein identity for the standard Gaussian direction:
`E[⟪g,u⟫ u] = g`. -/
private theorem gaussian_inner_smul_integrable (g : Space n) :
    Integrable (fun u : Space n => ((⟪g, u⟫_ℝ) • u : Space n))
      (gaussianDirectionLaw n) := by
  rw [gaussianDirectionLaw_def]
  have hsq :
      Integrable
        (fun u : Space n => ‖((⟪g, u⟫_ℝ) • u : Space n)‖ ^ (2 : ℕ))
        (stdGaussian (Space n)) := by
    simpa [gaussianDirectionLaw_def] using gaussian_linear_oracle_norm_sq_integrable (n := n) g
  have hvec_int :
      Integrable (fun u : Space n => ((⟪g, u⟫_ℝ) • u : Space n))
        (stdGaussian (Space n)) := by
    have hmeas :
        AEStronglyMeasurable (fun u : Space n => ((⟪g, u⟫_ℝ) • u : Space n))
          (stdGaussian (Space n)) := by
      exact (((continuous_const.inner continuous_id).smul continuous_id)).aestronglyMeasurable
    exact integrable_of_integrable_norm_sq hmeas hsq
  exact hvec_int

/-- Vector Stein identity for the standard Gaussian direction:
`E[⟪g,u⟫ u] = g`. -/
private theorem gaussian_inner_smul_integral_eq (g : Space n) :
    (∫ u : Space n, ((⟪g, u⟫_ℝ) • u : Space n) ∂gaussianDirectionLaw n) = g := by
  rw [gaussianDirectionLaw_def]
  have hvec_int :
      Integrable (fun u : Space n => ((⟪g, u⟫_ℝ) • u : Space n))
        (stdGaussian (Space n)) := by
    simpa [gaussianDirectionLaw_def] using gaussian_inner_smul_integrable (n := n) g
  apply ext_inner_left ℝ
  intro v
  have hcomp :
      ⟪v, ∫ u : Space n, ((⟪g, u⟫_ℝ) • u : Space n) ∂stdGaussian (Space n)⟫_ℝ =
        ∫ u : Space n, ⟪g, u⟫_ℝ * ⟪v, u⟫_ℝ ∂stdGaussian (Space n) := by
    let Lmap : Space n →L[ℝ] ℝ := innerSL ℝ v
    simpa [Lmap, inner_smul_right] using
      (ContinuousLinearMap.integral_comp_comm Lmap hvec_int).symm
  rw [hcomp]
  simpa [mul_comm] using (integral_inner_mul_inner_stdGaussian (E := Space n) v g)

/-- The sixth norm moment of the standard Gaussian direction is finite. -/
private theorem gaussian_norm_six_integrable :
    Integrable (fun u : Space n => ‖u‖ ^ (6 : ℕ)) (gaussianDirectionLaw n) := by
  rw [gaussianDirectionLaw_def]
  have hmem : MemLp id 6 (stdGaussian (Space n)) :=
    IsGaussian.memLp_id (stdGaussian (Space n)) 6 (by norm_num)
  simpa [Real.rpow_natCast] using
    (hmem.integrable_norm_rpow (by norm_num) (by norm_num))

/-- The third norm moment of the standard Gaussian direction is finite. -/
private theorem gaussian_norm_three_integrable :
    Integrable (fun u : Space n => ‖u‖ ^ (3 : ℕ)) (gaussianDirectionLaw n) := by
  rw [gaussianDirectionLaw_def]
  have hmem : MemLp id 3 (stdGaussian (Space n)) :=
    IsGaussian.memLp_id (stdGaussian (Space n)) 3 (by norm_num)
  simpa [Real.rpow_natCast] using
    (hmem.integrable_norm_rpow (by norm_num) (by norm_num))

/-- The sixth norm moment bound in Lemma 6.2(b)/(6.1.53). -/
private theorem gaussian_norm_six_integral_le :
    (∫ u : Space n, ‖u‖ ^ (6 : ℕ) ∂gaussianDirectionLaw n) ≤
      ((n : ℝ) + 6) ^ (3 : ℕ) := by
  rw [gaussianDirectionLaw_def]
  classical
  let n_nat := Module.finrank ℝ (Space n)
  let b : OrthonormalBasis (Fin n_nat) ℝ (Space n) := stdOrthonormalBasis ℝ (Space n)
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [MeasureTheory.integral_map
    (Continuous.aemeasurable (by continuity :
      Continuous (fun x : Fin n_nat → ℝ => (∑ i, x i • (b i : Space n) : Space n))))
    (by
      simpa using (continuous_norm.pow 6).aestronglyMeasurable)]
  have hcoord :
      (∫ z : Fin n_nat → ℝ, (∑ i, (z i) ^ (2 : ℕ)) ^ (3 : ℕ)
        ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1)) ≤
        ((n : ℝ) + 6) ^ (3 : ℕ) := by
    rw [pi_gaussian_sum_sq_cube_moment_eq n_nat]
    have hdim : (n_nat : ℝ) = (n : ℝ) := by
      simp [n_nat, Space]
    rw [hdim]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]
  have hrewrite :
      (∫ x : Fin n_nat → ℝ,
          ‖(∑ i, x i • (b i : Space n) : Space n)‖ ^ (6 : ℕ)
          ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1)) =
        ∫ z : Fin n_nat → ℝ, (∑ i, (z i) ^ (2 : ℕ)) ^ (3 : ℕ)
          ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun z => by
      have hnorm : ‖(∑ i, z i • (b i : Space n) : Space n)‖ ^ (2 : ℕ) =
          ∑ i, (z i) ^ (2 : ℕ) := by
        simpa using (norm_sq_sum_smul_orthonormalBasis_bridge (E := Space n) (b := b) z)
      calc
        ‖(∑ i, z i • (b i : Space n) : Space n)‖ ^ (6 : ℕ)
            = (‖(∑ i, z i • (b i : Space n) : Space n)‖ ^ (2 : ℕ)) ^ (3 : ℕ) := by
                ring
        _ = (∑ i, (z i) ^ (2 : ℕ)) ^ (3 : ℕ) := by
              rw [hnorm]
  rw [hrewrite]
  exact hcoord

/-- The squared third norm moment bound used in the reverse smoothing-gradient
comparison, with the source constant `(n + 3)^3`. -/
private theorem gaussian_norm_three_integral_sq_le :
    (∫ u : Space n, ‖u‖ ^ (3 : ℕ) ∂gaussianDirectionLaw n) ^ (2 : ℕ) ≤
      ((n : ℝ) + 3) ^ (3 : ℕ) := by
  rw [gaussianDirectionLaw_def]
  have hmoment_real :
      (∫ u : Space n, ‖u‖ ^ (3 : ℝ) ∂stdGaussian (Space n)) ≤
        (3 + (Module.finrank ℝ (Space n) : ℝ)) ^ (3 / 2 : ℝ) := by
    simpa using
      (stdGaussianMoment_le_add_finrank_rpow_of_two_le (E := Space n)
        3 (by norm_num : (2 : ℝ) ≤ 3))
  have hmoment_nat :
      (∫ u : Space n, ‖u‖ ^ (3 : ℕ) ∂stdGaussian (Space n)) ≤
        ((n : ℝ) + 3) ^ (3 / 2 : ℝ) := by
    simpa [Space, add_comm, add_left_comm, add_assoc] using hmoment_real
  let A : ℝ := ∫ u : Space n, ‖u‖ ^ (3 : ℕ) ∂stdGaussian (Space n)
  let B : ℝ := ((n : ℝ) + 3) ^ (3 / 2 : ℝ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun u => by positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg (by positivity) _
  have hsq : A ^ (2 : ℕ) ≤ B ^ (2 : ℕ) := by
    nlinarith [hmoment_nat, hA_nonneg, hB_nonneg, sq_nonneg (A - B)]
  have hbase_pos : 0 < (n : ℝ) + 3 := by positivity
  have hBsq : B ^ (2 : ℕ) = ((n : ℝ) + 3) ^ (3 : ℕ) := by
    dsimp [B]
    rw [pow_two, ← Real.rpow_add hbase_pos]
    norm_num
  simpa [A, hBsq] using hsq

/-- The standard Gaussian direction has squared norm expectation equal to the
ambient dimension. -/
private theorem gaussian_norm_sq_integral_eq :
    (∫ u : Space n, ‖u‖ ^ (2 : ℕ) ∂gaussianDirectionLaw n) = (n : ℝ) := by
  rw [gaussianDirectionLaw_def]
  classical
  let n_nat := Module.finrank ℝ (Space n)
  let b : OrthonormalBasis (Fin n_nat) ℝ (Space n) :=
    stdOrthonormalBasis ℝ (Space n)
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [MeasureTheory.integral_map
    (Continuous.aemeasurable (by continuity :
      Continuous (fun x : Fin n_nat → ℝ => (∑ i, x i • (b i : Space n) : Space n))))
    (by
      simpa using (continuous_norm.pow 2).aestronglyMeasurable)]
  have hrewrite :
      (∫ x : Fin n_nat → ℝ,
          ‖(∑ i, x i • (b i : Space n) : Space n)‖ ^ (2 : ℕ)
          ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1)) =
        ∫ z : Fin n_nat → ℝ, ∑ i, (z i) ^ (2 : ℕ)
          ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun z => by
      simpa using (norm_sq_sum_smul_orthonormalBasis_bridge
        (E := Space n) (b := b) z)
  rw [hrewrite]
  have hterm_int :
      ∀ i ∈ (Finset.univ : Finset (Fin n_nat)),
        Integrable (fun z : Fin n_nat → ℝ => (z i) ^ (2 : ℕ))
          (Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
    intro i _hi
    have hfour :
        Integrable (fun z : Fin n_nat → ℝ =>
            (z i) ^ (2 : ℕ) * (z i) ^ (2 : ℕ))
          (Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) :=
      integrable_pi_gaussian_sq_sq_monomial (i := i) (j := i)
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hfour) ?_ ?_
    · exact ((continuous_apply i).pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => by
        have hsq_nonneg : 0 ≤ (z i) ^ (2 : ℕ) := by positivity
        have hle : (z i) ^ (2 : ℕ) ≤
            1 + (z i) ^ (2 : ℕ) * (z i) ^ (2 : ℕ) := by
          nlinarith [sq_nonneg ((z i) ^ (2 : ℕ) - 1)]
        simpa [Real.norm_of_nonneg hsq_nonneg] using hle
  calc
    (∫ z : Fin n_nat → ℝ, ∑ i, (z i) ^ (2 : ℕ)
        ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1))
        = ∑ i : Fin n_nat,
            ∫ z : Fin n_nat → ℝ, (z i) ^ (2 : ℕ)
              ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
            rw [MeasureTheory.integral_finset_sum]
            exact hterm_int
    _ = ∑ _i : Fin n_nat, (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact pi_gaussian_sq_moment i
    _ = (n : ℝ) := by
          simp [n_nat, Space]

/-- Deterministic CL11 Gaussian forward-oracle square-moment estimate, i.e.
Lemma 6.2(b)/(6.1.53) in the source. -/
private theorem gaussian_forward_oracle_norm_sq_integrable_and_integral_le_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x : Space n)
    (hf : CL11 f L) (hL : 0 < L) (hμ : 0 < μ) :
    Integrable
        (fun u : Space n => ‖(((f (x + μ • u) - f x) / μ) • u : Space n)‖ ^ (2 : ℕ))
        (gaussianDirectionLaw n) ∧
      (∫ u : Space n,
          ‖(((f (x + μ • u) - f x) / μ) • u : Space n)‖ ^ (2 : ℕ)
            ∂gaussianDirectionLaw n) ≤
        2 * ((n : ℝ) + 4) * ‖∇ f x‖ ^ (2 : ℕ) +
          μ ^ (2 : ℕ) * L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) := by
  simpa [gaussianDirectionLaw_def, CL11, Space] using
      (forward_difference_gaussian_norm_sq_integrable_and_integral_le_of_lipschitz_gradient
      (E := Space n) (f := f) (L := L) (μ := μ) (x := x) hf hL.le hμ)

/-- Source-granularity version of (6.1.67)'s first inequality, packaged with the
square-integrability needed for Bochner integrability of the RSGF oracle. -/
private theorem rsgfOracle_norm_sq_integrable_and_secondMoment_le_sampleGradient
    (S : Setup n Sample) (x : Space n) :
    Integrable
        (fun z : Sample × Space n => ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ))
        (S.P.prod (gaussianDirectionLaw n)) ∧
      (∫ z : Sample × Space n,
          ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ) ∂(S.P.prod (gaussianDirectionLaw n))) ≤
        2 * ((n : ℝ) + 4) *
            (∫ ξ, ‖gradient (fun y => S.F y ξ) x‖ ^ (2 : ℕ) ∂S.P) +
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  simpa [rsgfOracle, gaussianDirectionLaw_def, Space] using
    (forwardDifferenceOracle_norm_sq_integrable_and_integral_le_sampleGradient
      (E := Space n) (Sample := Sample) S.P S.F S.L S.μ x
      S.szo_assumption15.1 S.sample_smooth_ae
      (sampleGradient_norm_sq_integrable S x) S.L_pos S.μ_pos)

/-- The objective-gradient field remains integrable after the Gaussian shift
`u ↦ x + μ u`.  This is a local analytic ingredient for Lemma 6.2(a)'s
deterministic Gaussian-smoothing gradient formula. -/
private theorem objective_gradient_gaussian_shift_integrable
    (S : Setup n Sample) (x : Space n) :
    Integrable (fun u : Space n => ∇ (objective S) (x + S.μ • u))
      (gaussianDirectionLaw n) := by
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  rcases objective_CL11 S with ⟨hdiff, hlip⟩
  have hcont_grad : Continuous (fun y : Space n => ∇ (objective S) y) := by
    have hlip_with :
        LipschitzWith ⟨S.L, S.L_pos.le⟩ (fun y : Space n => ∇ (objective S) y) := by
      rw [lipschitzWith_iff_norm_sub_le]
      intro a b
      simpa using hlip b a
    exact hlip_with.continuous
  have hnorm1 :
      Integrable (fun u : Space n => ‖u‖) (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    simpa using (IsGaussian.integrable_id (μ := stdGaussian (Space n))).norm
  have hbound_int :
      Integrable
        (fun u : Space n => ‖∇ (objective S) x‖ + (S.L * S.μ) * ‖u‖)
        (gaussianDirectionLaw n) :=
    (integrable_const ‖∇ (objective S) x‖).add (hnorm1.const_mul (S.L * S.μ))
  refine Integrable.mono' hbound_int ?_ ?_
  · exact
      (hcont_grad.comp
        (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u => by
      have hsub : (x + S.μ • u) - x = S.μ • u := by
        abel
      calc
        ‖∇ (objective S) (x + S.μ • u)‖
            ≤ ‖∇ (objective S) (x + S.μ • u) - ∇ (objective S) x‖ +
                ‖∇ (objective S) x‖ := by
              simpa using
                norm_add_le
                  (∇ (objective S) (x + S.μ • u) - ∇ (objective S) x)
                  (∇ (objective S) x)
        _ ≤ S.L * ‖(x + S.μ • u) - x‖ + ‖∇ (objective S) x‖ := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (hlip x (x + S.μ • u)) ‖∇ (objective S) x‖
        _ = ‖∇ (objective S) x‖ + (S.L * S.μ) * ‖u‖ := by
              rw [hsub, norm_smul, Real.norm_of_nonneg S.μ_pos.le]
              ring

/-- A deterministic `CL11` gradient field remains integrable after a positive
Gaussian smoothing shift. -/
private theorem gaussian_gradient_shift_integrable_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x : Space n)
    (hf : CL11 f L) (hL : 0 < L) (hμ : 0 < μ) :
    Integrable (fun u : Space n => ∇ f (x + μ • u))
      (gaussianDirectionLaw n) := by
  simpa [gaussianDirectionLaw_def, CL11, Space] using
    (integrable_gradient_gaussianShift_of_lipschitzGradient f L μ x hf)

/-- The deterministic `CL11` forward finite-difference vector is Bochner
integrable under the standard Gaussian direction law. -/
private theorem gaussian_forward_oracle_integrable_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x : Space n)
    (hf : CL11 f L) (hL : 0 < L) (hμ : 0 < μ) :
    Integrable
      (fun u : Space n => (((f (x + μ • u) - f x) / μ) • u : Space n))
      (gaussianDirectionLaw n) := by
  simpa [gaussianDirectionLaw_def, CL11, Space] using
    (integrable_forwardDifference_gaussian_of_lipschitzGradient
      (E := Space n) (f := f) (L := L) (μ := μ) (x := x) hf hL.le hμ)

/-- One-dimensional standard-Gaussian Stein identity, reduced to Mathlib's
improper real-line integration by parts after rewriting the Gaussian law by
its density.  The derivative hypothesis is stated separately so the analytic
IBP contract is isolated from the elementary Gaussian-density calculus. -/
private theorem gaussianReal_stein_integral_of_density_ibp
    (g g' : ℝ → ℝ)
    (hg : ∀ t ∈ tsupport (gaussianPDFReal 0 1), HasDerivAt g (g' t) t)
    (hpdf :
      ∀ t ∈ tsupport g,
        HasDerivAt (gaussianPDFReal 0 1)
          (-t * gaussianPDFReal 0 1 t) t)
    (hgv' :
      Integrable (fun t : ℝ => g t * (-t * gaussianPDFReal 0 1 t)))
    (hg'v : Integrable (fun t : ℝ => g' t * gaussianPDFReal 0 1 t))
    (hgv : Integrable (fun t : ℝ => g t * gaussianPDFReal 0 1 t)) :
    (∫ t : ℝ, g t * t ∂gaussianReal 0 1) =
      ∫ t : ℝ, g' t ∂gaussianReal 0 1 := by
  exact integral_mul_id_gaussianReal_eq_integral_deriv_of_density_ibp
    g g' hg
    hpdf
    hgv' hg'v hgv

private theorem hasDerivAt_gaussianPDFReal_zero_one (t : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-t * gaussianPDFReal 0 1 t) t := by
  exact _root_.hasDerivAt_gaussianPDFReal_zero_one t

/-- One-dimensional standard-Gaussian Stein identity with the Gaussian-density
derivative discharged.  The remaining hypotheses are exactly the derivative of
the scalar test function and the density-weighted volume integrability facts
required by Mathlib's improper integration-by-parts theorem. -/
private theorem gaussianReal_stein_integral_of_hasDerivAt_density_integrable
    (g g' : ℝ → ℝ)
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t)
    (hgv' :
      Integrable (fun t : ℝ => g t * (-t * gaussianPDFReal 0 1 t)))
    (hg'v : Integrable (fun t : ℝ => g' t * gaussianPDFReal 0 1 t))
    (hgv : Integrable (fun t : ℝ => g t * gaussianPDFReal 0 1 t)) :
    (∫ t : ℝ, g t * t ∂gaussianReal 0 1) =
      ∫ t : ℝ, g' t ∂gaussianReal 0 1 := by
  exact integral_mul_id_gaussianReal_eq_integral_deriv g g' hg hgv' hg'v hgv

/-- Differentiating a `CL11` function along the affine line used by a Gaussian
coordinate fiber.  The factor `μ` from the line derivative cancels the
finite-difference denominator. -/
private theorem cl11_forward_line_hasDerivAt
    (f : Space n → ℝ) (L μ : ℝ) (x z d : Space n)
    (hf : CL11 f L) (hμ : 0 < μ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (f (x + μ • (z + s • d)) - f x) / μ)
      ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ t := by
  exact SOptLib.hasDerivAt_forwardDifference_affineLine_of_differentiableAt
    (f := f) (μ := μ) (x := x) (z := z) (d := d) (t := t)
    (SOptLib.LipschitzGradientObjective.differentiable hf
      (x + μ • (z + t • d))) hμ.ne'

/-- One-dimensional CL11 finite-difference Stein identity along a fixed affine
Gaussian coordinate fiber.  This consumes the proved Gaussian Stein lemma and
the CL11 line derivative; product-coordinate/Fubini assembly remains separate. -/
private theorem cl11_forward_line_gaussianReal_stein
    (f : Space n → ℝ) (L μ : ℝ) (x z d : Space n)
    (hf : CL11 f L) (hμ : 0 < μ)
    (hleft_density :
      Integrable
        (fun t : ℝ =>
          ((f (x + μ • (z + t • d)) - f x) / μ) *
            (-t * gaussianPDFReal 0 1 t)))
    (hright_density :
      Integrable
        (fun t : ℝ =>
          ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ *
            gaussianPDFReal 0 1 t))
    (hprod_density :
      Integrable
        (fun t : ℝ =>
          ((f (x + μ • (z + t • d)) - f x) / μ) *
            gaussianPDFReal 0 1 t)) :
    (∫ t : ℝ,
        ((f (x + μ • (z + t • d)) - f x) / μ) * t
          ∂gaussianReal 0 1) =
      ∫ t : ℝ, ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ
        ∂gaussianReal 0 1 := by
  exact
    gaussianReal_stein_integral_of_hasDerivAt_density_integrable
      (g := fun t : ℝ => (f (x + μ • (z + t • d)) - f x) / μ)
      (g' := fun t : ℝ => ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ)
      (fun t => cl11_forward_line_hasDerivAt
        (n := n) (f := f) (L := L) (μ := μ)
        (x := x) (z := z) (d := d) hf hμ t)
      hleft_density hright_density hprod_density

/-- Convert integrability under the standard real Gaussian law into the
corresponding volume integrability against `gaussianPDFReal 0 1`. -/
private theorem gaussianReal_density_mul_integrable_of_integrable
    (φ : ℝ → ℝ) (hφ : Integrable φ (gaussianReal 0 1)) :
    Integrable (fun t : ℝ => φ t * gaussianPDFReal 0 1 t) :=
  by
    simpa [smul_eq_mul, mul_comm] using
      integrable_mul_gaussianPDFReal_of_integrable_gaussianReal
        (mu := 0) (v := 1) (by norm_num : (1 : NNReal) ≠ 0) hφ

/-- Standard real Gaussian density integrability for the Stein left-density
term follows from Gaussian-law integrability of `φ t * t`. -/
private theorem gaussianReal_density_neg_mul_integrable_of_integrable_mul
    (φ : ℝ → ℝ)
    (hφt : Integrable (fun t : ℝ => φ t * t) (gaussianReal 0 1)) :
    Integrable (fun t : ℝ => φ t * (-t * gaussianPDFReal 0 1 t)) := by
  exact integrable_mul_neg_id_mul_gaussianPDFReal_of_integrable_mul_id_gaussianReal
    φ hφt

/-- One-dimensional CL11 finite-difference Stein identity with ordinary
Gaussian-law integrability hypotheses.  This keeps the density bookkeeping out
of product-coordinate fibers; the remaining task is to prove these Gaussian-law
fiber integrability facts from CL11 growth. -/
private theorem cl11_forward_line_gaussianReal_stein_of_integrable
    (f : Space n → ℝ) (L μ : ℝ) (x z d : Space n)
    (hf : CL11 f L) (hμ : 0 < μ)
    (hleft :
      Integrable
        (fun t : ℝ =>
          ((f (x + μ • (z + t • d)) - f x) / μ) * t)
        (gaussianReal 0 1))
    (hright :
      Integrable
        (fun t : ℝ =>
          ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ)
        (gaussianReal 0 1))
    (hprod :
      Integrable
        (fun t : ℝ =>
          (f (x + μ • (z + t • d)) - f x) / μ)
        (gaussianReal 0 1)) :
    (∫ t : ℝ,
        ((f (x + μ • (z + t • d)) - f x) / μ) * t
          ∂gaussianReal 0 1) =
      ∫ t : ℝ, ⟪d, ∇ f (x + μ • (z + t • d))⟫_ℝ
        ∂gaussianReal 0 1 := by
  exact SOptLib.integral_forwardDifference_line_mul_id_gaussianReal_eq_integral_inner_gradient_line
    (f := f) (μ := μ) (x := x) (z := z) (d := d)
    (fun t => SOptLib.LipschitzGradientObjective.differentiable hf
      (x + μ • (z + t • d))) hμ.ne' hleft hright hprod

/-- Finite-dimensional assembly from orthonormal-basis coordinate Stein
identities to an arbitrary scalar direction.  The analytic content is entirely
in `hcoord`; this lemma only expands `v` in the basis and commutes finite sums
through the Bochner integral. -/
private theorem gaussian_forward_difference_inner_from_basis_coordinates
    {n_nat : ℕ} (ν : Measure (Space n))
    (b : OrthonormalBasis (Fin n_nat) ℝ (Space n))
    (a : Space n → ℝ) (G : Space n → Space n) (v : Space n)
    (hforward_int : Integrable (fun u : Space n => (a u) • u) ν)
    (hgrad_int : Integrable G ν)
    (hcoord :
      ∀ i : Fin n_nat,
        (∫ u : Space n, a u * ⟪b i, u⟫_ℝ ∂ν) =
          ∫ u : Space n, ⟪b i, G u⟫_ℝ ∂ν) :
    (∫ u : Space n, a u * ⟪v, u⟫_ℝ ∂ν) =
      ∫ u : Space n, ⟪v, G u⟫_ℝ ∂ν := by
  exact
    _root_.integral_inner_identity_of_orthonormalBasis_coordinates
      (ν := ν) (b := b) (G := G) (a := a) (v := v)
      hforward_int hgrad_int hcoord

/-- Split a finite product of standard real Gaussian coordinates at one selected
`Fin (m+1)` coordinate, with the remaining coordinates integrated outside.
This is the product-coordinate Fubini transport used by the coordinate Stein
proof. -/
private theorem pi_gaussian_coordinate_split_integral_finSucc
    {m : ℕ} (i : Fin (m + 1)) (Φ : (Fin (m + 1) → ℝ) → ℝ)
    (hΦ :
      Integrable Φ
        (Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1)) :
    (∫ z : Fin (m + 1) → ℝ, Φ z
        ∂(Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1)) =
      ∫ η : Fin m → ℝ,
        ∫ t : ℝ,
          Φ ((MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (m + 1) => ℝ) i).symm (t, η))
            ∂(gaussianReal 0 1)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  exact
    _root_.integral_pi_eq_integral_coordinate_fiber_piFinSuccAbove
      (α := fun _ : Fin (m + 1) => ℝ)
      (μ := fun _ : Fin (m + 1) => gaussianReal 0 1)
      (i := i) (Φ := Φ) hΦ

/-- The affine Gaussian shift `x + μu` is square-integrable around its center. -/
private theorem gaussian_shift_centered_sq_integrable_const_smul
    (μ : ℝ) (x : Space n) :
    Integrable (fun u : Space n => ‖x - (x + μ • u)‖ ^ (2 : ℕ))
      (gaussianDirectionLaw n) := by
  simpa [gaussianDirectionLaw_def] using
    (integrable_norm_sub_self_add_const_smul_sq_stdGaussian
      (E := Space n) μ x)

/-- A deterministic `CL11` scalar value is integrable along the Gaussian
smoothing shift. -/
private theorem gaussian_value_shift_integrable_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x : Space n)
    (hf : CL11 f L) :
    Integrable (fun u : Space n => f (x + μ • u))
      (gaussianDirectionLaw n) := by
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  have hcont_f : Continuous f := hf.1.continuous
  refine SOptLib.integrable_smooth_value_of_centered_l2
    (f := f) (g := ∇ f x) (base := x) (L := L)
    (z := fun u : Space n => x + μ • u) ?_ ?_ ?_ ?_
  · exact (continuous_const.add (continuous_const.smul continuous_id)).aestronglyMeasurable
  · exact
      (hcont_f.comp
        (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  · exact gaussian_shift_centered_sq_integrable_const_smul (n := n) μ x
  · exact Filter.Eventually.of_forall fun u => by
      simpa using (smoothDescentBound_of_CL11 hf) x (x + μ • u)

/-- Product-coordinate form of the basis-coordinate Stein identity.  This is
the remaining finite-dimensional Gaussian/Fubini layer: after rewriting
`stdGaussian` through an orthonormal-basis coordinate map, it reduces each fixed
coordinate to the one-dimensional CL11 Stein identity. -/
private theorem gaussian_forward_difference_pi_coordinate_integral_eq_gradient_coordinate_CL11
    {n_nat : ℕ} (b : OrthonormalBasis (Fin n_nat) ℝ (Space n))
    (i : Fin n_nat) (f : Space n → ℝ) (L μ : ℝ) (x : Space n)
    (hf : CL11 f L) (hL : 0 < L) (hμ : 0 < μ) :
    (∫ z : Fin n_nat → ℝ,
        ((f (x + μ • (∑ j, z j • (b j : Space n))) - f x) / μ) * z i
          ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1)) =
      ∫ z : Fin n_nat → ℝ,
        ⟪b i, ∇ f (x + μ • (∑ j, z j • (b j : Space n)))⟫_ℝ
          ∂(Measure.pi fun _ : Fin n_nat => gaussianReal 0 1) := by
  exact SOptLib.integral_pi_gaussian_forwardDifference_basis_coord_eq_gradient_basis_coord_of_lipschitzGradient
    b i f L μ x hf hL.le hμ

/-- Scalarized deterministic Lemma 6.2(a) core.  This is the remaining
standard-Gaussian Stein integration-by-parts step after the CL11 growth and
Bochner-integrability obligations have been discharged. -/
private theorem gaussian_forward_difference_inner_integral_eq_gradient_inner_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x v : Space n)
    (hf : CL11 f L) (hL : 0 < L) (hμ : 0 < μ) :
    (∫ u : Space n,
        ((f (x + μ • u) - f x) / μ) * ⟪v, u⟫_ℝ
          ∂gaussianDirectionLaw n) =
      ∫ u : Space n, ⟪v, ∇ f (x + μ • u)⟫_ℝ
        ∂gaussianDirectionLaw n := by
  simpa [gaussianDirectionLaw_def] using
    SOptLib.integral_forwardDifference_mul_inner_stdGaussian_eq_integral_inner_gradient_shift_of_lipschitzGradient
      f L μ x v hf hL.le hμ

/-- Deterministic `CL11` Lemma 6.2(a): the Gaussian average of the forward
finite-difference vector equals the Gaussian average of shifted gradients. -/
private theorem gaussian_forward_difference_integral_eq_gradient_average_CL11
    (f : Space n → ℝ) (L μ : ℝ) (x : Space n)
    (hf : CL11 f L) (hL : 0 < L) (hμ : 0 < μ) :
    (∫ u : Space n, (((f (x + μ • u) - f x) / μ) • u : Space n)
        ∂gaussianDirectionLaw n) =
      ∫ u : Space n, ∇ f (x + μ • u) ∂gaussianDirectionLaw n := by
  simpa [gaussianDirectionLaw_def] using
    SOptLib.integral_forwardDifference_smul_stdGaussian_eq_integral_gradient_shift_of_lipschitzGradient
      f L μ x hf hL.le hμ

/-- The Gaussian shift `x + μu` is square-integrable around its center `x`. -/
private theorem gaussian_shift_centered_sq_integrable
    (S : Setup n Sample) (x : Space n) :
    Integrable (fun u : Space n => ‖x - (x + S.μ • u)‖ ^ (2 : ℕ))
      (gaussianDirectionLaw n) := by
  rw [gaussianDirectionLaw_def]
  have hmem :
      MemLp (fun u : Space n => S.μ • u) 2 (stdGaussian (Space n)) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian (Space n))).const_smul S.μ
  have hsq : Integrable
      (fun u : Space n => ‖S.μ • u‖ ^ (2 : ℕ)) (stdGaussian (Space n)) := by
    simpa using (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq

/-- The scalar objective value is integrable along the Gaussian smoothing shift. -/
private theorem objective_gaussian_shift_integrable
    (S : Setup n Sample) (x : Space n) :
    Integrable (fun u : Space n => objective S (x + S.μ • u))
      (gaussianDirectionLaw n) := by
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  have hcont_obj : Continuous (objective S) := (objective_CL11 S).1.continuous
  refine SOptLib.integrable_smooth_value_of_centered_l2
    (f := objective S) (g := ∇ (objective S) x) (base := x) (L := S.L)
    (z := fun u : Space n => x + S.μ • u) ?_ ?_ ?_ ?_
  · exact (continuous_const.add (continuous_const.smul continuous_id)).aestronglyMeasurable
  · exact
      (hcont_obj.comp
        (continuous_const.add (continuous_const.smul continuous_id))).aestronglyMeasurable
  · exact gaussian_shift_centered_sq_integrable S x
  · exact Filter.Eventually.of_forall fun u => by
      simpa using objective_smoothDescentBound S x (x + S.μ • u)

/-- Differentiating the Gaussian smoothing integral gives the Gaussian average
of shifted objective gradients.  This is the dominated-differentiation half of
Lemma 6.2(a), before the Stein/forward-difference identification. -/
private theorem gaussianSmoothing_hasGradientAt_average
    (S : Setup n Sample) (x : Space n) :
    HasGradientAt (gaussianSmoothing S)
      (∫ u : Space n, ∇ (objective S) (x + S.μ • u) ∂gaussianDirectionLaw n) x := by
  simpa [gaussianSmoothing, gaussianDirectionLaw_def] using
    (SOptLib.hasGradientAt_gaussianSmoothing_eq_integral_gradient_shift_of_lipschitzGradient
      (f := objective S) (L := S.L) (μ := S.μ) (x := x)
      (objective_CL11 S) S.L_pos.le S.μ_pos.le)

/-- Mathlib's total gradient selector for the Gaussian smoothing agrees with
the shifted-gradient Gaussian average. -/
private theorem gaussianSmoothing_gradient_eq_average
    (S : Setup n Sample) (x : Space n) :
    ∇ (gaussianSmoothing S) x =
      ∫ u : Space n, ∇ (objective S) (x + S.μ • u) ∂gaussianDirectionLaw n := by
  exact (gaussianSmoothing_hasGradientAt_average S x).gradient

/-- Lemma 6.2(a) supplies the same `L`-smooth descent inequality for the
Gaussian smoothing as for the original objective. -/
private theorem gaussianSmoothing_smoothDescentBound
    (S : Setup n Sample) :
    SmoothDescentBound (gaussianSmoothing S) S.L := by
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  refine smoothDescentBound_of_CL11 ?_
  refine ⟨?_, ?_⟩
  · intro x
    exact (gaussianSmoothing_hasGradientAt_average S x).differentiableAt
  · intro x y
    rcases objective_CL11 S with ⟨_hdiff, hlip⟩
    have hx_int :
        Integrable (fun u : Space n => ∇ (objective S) (x + S.μ • u))
          (gaussianDirectionLaw n) :=
      objective_gradient_gaussian_shift_integrable S x
    have hy_int :
        Integrable (fun u : Space n => ∇ (objective S) (y + S.μ • u))
          (gaussianDirectionLaw n) :=
      objective_gradient_gaussian_shift_integrable S y
    have hpoint :
        ∀ᵐ u : Space n ∂gaussianDirectionLaw n,
          ‖∇ (objective S) (y + S.μ • u) -
              ∇ (objective S) (x + S.μ • u)‖ ≤
            S.L * ‖y - x‖ := by
      refine Filter.Eventually.of_forall ?_
      intro u
      calc
        ‖∇ (objective S) (y + S.μ • u) -
            ∇ (objective S) (x + S.μ • u)‖
            ≤ S.L * ‖(y + S.μ • u) - (x + S.μ • u)‖ := by
              simpa using hlip (x + S.μ • u) (y + S.μ • u)
        _ = S.L * ‖y - x‖ := by
              congr 1
              congr 1
              abel
    calc
      ‖∇ (gaussianSmoothing S) y - ∇ (gaussianSmoothing S) x‖
          =
        ‖(∫ u : Space n, ∇ (objective S) (y + S.μ • u)
              ∂gaussianDirectionLaw n) -
          ∫ u : Space n, ∇ (objective S) (x + S.μ • u)
              ∂gaussianDirectionLaw n‖ := by
            rw [gaussianSmoothing_gradient_eq_average S y,
              gaussianSmoothing_gradient_eq_average S x]
      _ =
        ‖∫ u : Space n,
            ∇ (objective S) (y + S.μ • u) -
              ∇ (objective S) (x + S.μ • u)
            ∂gaussianDirectionLaw n‖ := by
            rw [integral_sub hy_int hx_int]
      _ ≤ (S.L * ‖y - x‖) * (gaussianDirectionLaw n).real Set.univ := by
            exact norm_integral_le_of_norm_le_const hpoint
      _ = S.L * ‖y - x‖ := by
            simp

/-- The gradient of the Gaussian smoothing inherits the objective's Lipschitz
constant. This exposes the Lipschitz half of Lemma 6.2(a) for later
integrability transport. -/
private theorem gaussianSmoothing_gradient_lipschitz
    (S : Setup n Sample) :
    ∀ x y : Space n,
      ‖∇ (gaussianSmoothing S) y - ∇ (gaussianSmoothing S) x‖ ≤
        S.L * ‖y - x‖ := by
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  intro x y
  rcases objective_CL11 S with ⟨_hdiff, hlip⟩
  have hx_int :
      Integrable (fun u : Space n => ∇ (objective S) (x + S.μ • u))
        (gaussianDirectionLaw n) :=
    objective_gradient_gaussian_shift_integrable S x
  have hy_int :
      Integrable (fun u : Space n => ∇ (objective S) (y + S.μ • u))
        (gaussianDirectionLaw n) :=
    objective_gradient_gaussian_shift_integrable S y
  have hpoint :
      ∀ᵐ u : Space n ∂gaussianDirectionLaw n,
        ‖∇ (objective S) (y + S.μ • u) -
            ∇ (objective S) (x + S.μ • u)‖ ≤
          S.L * ‖y - x‖ := by
    refine Filter.Eventually.of_forall ?_
    intro u
    calc
      ‖∇ (objective S) (y + S.μ • u) -
          ∇ (objective S) (x + S.μ • u)‖
          ≤ S.L * ‖(y + S.μ • u) - (x + S.μ • u)‖ := by
            simpa using hlip (x + S.μ • u) (y + S.μ • u)
      _ = S.L * ‖y - x‖ := by
            congr 1
            congr 1
            abel
  calc
    ‖∇ (gaussianSmoothing S) y - ∇ (gaussianSmoothing S) x‖
        =
      ‖(∫ u : Space n, ∇ (objective S) (y + S.μ • u)
            ∂gaussianDirectionLaw n) -
        ∫ u : Space n, ∇ (objective S) (x + S.μ • u)
            ∂gaussianDirectionLaw n‖ := by
          rw [gaussianSmoothing_gradient_eq_average S y,
            gaussianSmoothing_gradient_eq_average S x]
    _ =
      ‖∫ u : Space n,
          ∇ (objective S) (y + S.μ • u) -
            ∇ (objective S) (x + S.μ • u)
          ∂gaussianDirectionLaw n‖ := by
          rw [integral_sub hy_int hx_int]
    _ ≤ (S.L * ‖y - x‖) * (gaussianDirectionLaw n).real Set.univ := by
          exact norm_integral_le_of_norm_le_const hpoint
    _ = S.L * ‖y - x‖ := by
          simp

/-- Pointwise smoothing error bound (6.1.51), specialized to the canonical
objective and Gaussian direction law. -/
private theorem gaussianSmoothing_abs_sub_objective_le
    (S : Setup n Sample) (x : Space n) :
    |gaussianSmoothing S x - objective S x| ≤
      S.μ ^ (2 : ℕ) * S.L * (n : ℝ) / 2 := by
  simpa [gaussianSmoothing, gaussianDirectionLaw_def] using
    (abs_gaussianSmoothing_sub_self_le_of_smoothDescentBound
      (f := objective S) (L := S.L) (μ := S.μ) (x := x)
      (by simpa [gaussianDirectionLaw_def] using objective_gaussian_shift_integrable S x)
      (objective_smoothDescentBound S))

/-- Source smoothing comparison used at the ends of the nonconvex descent
telescope: the initial smoothed value minus any terminal smoothed value is
controlled by the original initial objective gap plus the two endpoint
smoothing errors. -/
private theorem gaussianSmoothing_initial_sub_terminal_le_gap_add_error
    (S : Setup n Sample) (x : Space n) :
    gaussianSmoothing S S.x₁ - gaussianSmoothing S x ≤
      objective S S.x₁ - fStar S + S.μ ^ (2 : ℕ) * S.L * (n : ℝ) := by
  let err : ℝ := S.μ ^ (2 : ℕ) * S.L * (n : ℝ) / 2
  have hinit_abs := gaussianSmoothing_abs_sub_objective_le S S.x₁
  have hterm_abs := gaussianSmoothing_abs_sub_objective_le S x
  have hinit : gaussianSmoothing S S.x₁ - objective S S.x₁ ≤ err := by
    have hinit_abs' :
        |gaussianSmoothing S S.x₁ - objective S S.x₁| ≤ err := by
      change |gaussianSmoothing S S.x₁ - objective S S.x₁| ≤
        S.μ ^ (2 : ℕ) * S.L * (n : ℝ) / 2
      exact hinit_abs
    exact (abs_le.mp hinit_abs').2
  have hterm : objective S x - gaussianSmoothing S x ≤ err := by
    have hterm_abs' :
        |gaussianSmoothing S x - objective S x| ≤ err := by
      change |gaussianSmoothing S x - objective S x| ≤
        S.μ ^ (2 : ℕ) * S.L * (n : ℝ) / 2
      exact hterm_abs
    have h := (abs_le.mp hterm_abs').1
    linarith
  have hbdd : BddBelow ((objective S) '' (Set.univ : Set (Space n))) := by
    simpa [Set.image_univ] using objective_bddBelow S
  have hfstar_le : fStar S ≤ objective S x := by
    simpa [fStar] using
      SOptLib.objectiveInfimumValue_le (X := (Set.univ : Set (Space n)))
        (f := objective S) hbdd (Set.mem_univ x)
  have herr : S.μ ^ (2 : ℕ) * S.L * (n : ℝ) = 2 * err := by
    dsimp [err]
    ring
  nlinarith [hinit, hterm, hfstar_le, herr]

/-- Gaussian smoothing is continuous as a consequence of the pointwise gradient
formula. -/
private theorem gaussianSmoothing_continuous (S : Setup n Sample) :
    Continuous (gaussianSmoothing S) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (gaussianSmoothing_hasGradientAt_average S x).continuousAt

/-- Random-query smoothed-objective integrability from objective-gap
integrability.  The proof uses the uniform smoothing approximation error to
transfer integrability from `f(X)` to `f^μ(X)`. -/
private theorem gaussianSmoothing_random_query_integrable_of_gap_integrable
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (S : Setup n Sample) (X : Ω → Space n)
    (hX : AEStronglyMeasurable X ν)
    (hgap_int :
      Integrable (fun ω : Ω => objective S (X ω) - fStar S) ν) :
    Integrable (fun ω : Ω => gaussianSmoothing S (X ω)) ν := by
  let diff : Ω → ℝ := fun ω => gaussianSmoothing S (X ω) - objective S (X ω)
  have hobj_int : Integrable (fun ω : Ω => objective S (X ω)) ν := by
    have hsum := hgap_int.add (integrable_const (fStar S))
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro ω
    simp
  have hdiff_aesm : AEStronglyMeasurable diff ν := by
    exact
      ((gaussianSmoothing_continuous S).comp_aestronglyMeasurable hX).sub
        ((objective_CL11 S).1.continuous.comp_aestronglyMeasurable hX)
  have hdiff_int : Integrable diff ν := by
    let err : ℝ := S.μ ^ (2 : ℕ) * S.L * (n : ℝ) / 2
    have herr_nonneg : 0 ≤ err := by
      dsimp [err]
      exact
        div_nonneg
          (mul_nonneg
            (mul_nonneg (sq_nonneg S.μ) S.L_pos.le)
            (Nat.cast_nonneg n))
          (by norm_num)
    refine Integrable.mono' (integrable_const err) hdiff_aesm ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hbound := gaussianSmoothing_abs_sub_objective_le S (X ω)
    simpa [diff, Real.norm_eq_abs, abs_of_nonneg herr_nonneg] using hbound
  have hsum := hobj_int.add hdiff_int
  refine hsum.congr (Filter.Eventually.of_forall ?_)
  intro ω
  dsimp [diff]
  ring

/-- Gaussian smoothing preserves convexity of the original objective. -/
private theorem gaussianSmoothing_convexOn_of_objective_convex
    (S : Setup n Sample)
    (hconvex : ConvexOn ℝ Set.univ (objective S)) :
    ConvexOn ℝ Set.univ (gaussianSmoothing S) := by
  simpa [gaussianSmoothing, gaussianDirectionLaw_def] using
    (SOptLib.convexOn_gaussianSmoothing_of_convexOn
      (nu := gaussianDirectionLaw n) (f := objective S) (mu := S.μ)
      hconvex (fun x => by
        simpa [gaussianDirectionLaw_def] using objective_gaussian_shift_integrable S x))

/-- Deterministic Lemma 6.2(a) bridge: the Gaussian average of the forward
finite-difference oracle for the objective equals the average shifted gradient. -/
private theorem gaussian_forward_difference_integral_eq_gradient_average
    (S : Setup n Sample) (x : Space n) :
    (∫ u : Space n,
        (((objective S (x + S.μ • u) - objective S x) / S.μ) • u)
          ∂gaussianDirectionLaw n) =
      ∫ u : Space n, ∇ (objective S) (x + S.μ • u)
        ∂gaussianDirectionLaw n := by
  exact
    gaussian_forward_difference_integral_eq_gradient_average_CL11
      (f := objective S) (L := S.L) (μ := S.μ) (x := x)
      (objective_CL11 S) S.L_pos S.μ_pos

/-- Source step (6.1.55) before squaring: the Gaussian smoothing gradient differs
from the original gradient by the integrated finite-difference Taylor remainder. -/
private theorem gaussianSmoothing_gradient_error_le
    (S : Setup n Sample) (x : Space n) :
    ‖∇ (gaussianSmoothing S) x - ∇ (objective S) x‖ ≤
      (S.μ * S.L / 2) *
        ∫ u : Space n, ‖u‖ ^ (3 : ℕ) ∂gaussianDirectionLaw n := by
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  let fd : Space n → Space n :=
    fun u => (((objective S (x + S.μ • u) - objective S x) / S.μ) • u)
  let lin : Space n → Space n :=
    fun u => ((⟪∇ (objective S) x, u⟫_ℝ) • u)
  have hfd_int : Integrable fd (gaussianDirectionLaw n) := by
    simpa [fd] using
      gaussian_forward_oracle_integrable_CL11
        (n := n) (f := objective S) (L := S.L) (μ := S.μ) (x := x)
        (objective_CL11 S) S.L_pos S.μ_pos
  have hlin_int : Integrable lin (gaussianDirectionLaw n) := by
    simpa [lin] using gaussian_inner_smul_integrable (n := n) (∇ (objective S) x)
  have hres_int : Integrable (fun u : Space n => fd u - lin u) (gaussianDirectionLaw n) :=
    hfd_int.sub hlin_int
  have hdom_int :
      Integrable
        (fun u : Space n => (S.μ * S.L / 2) * ‖u‖ ^ (3 : ℕ))
        (gaussianDirectionLaw n) :=
    (gaussian_norm_three_integrable (n := n)).const_mul (S.μ * S.L / 2)
  have hpoint :
      ∀ u : Space n,
        ‖fd u - lin u‖ ≤ (S.μ * S.L / 2) * ‖u‖ ^ (3 : ℕ) := by
    intro u
    simpa [fd, lin] using
      gaussian_forward_difference_linear_remainder_norm_le_CL11
        (n := n) (f := objective S) (L := S.L) (μ := S.μ) (x := x) (u := u)
        (objective_CL11 S) S.L_pos S.μ_pos
  have hrepr :
      ∇ (gaussianSmoothing S) x - ∇ (objective S) x =
        ∫ u : Space n, fd u - lin u ∂gaussianDirectionLaw n := by
    calc
      ∇ (gaussianSmoothing S) x - ∇ (objective S) x
          = (∫ u : Space n, fd u ∂gaussianDirectionLaw n) -
              ∫ u : Space n, lin u ∂gaussianDirectionLaw n := by
              rw [gaussianSmoothing_gradient_eq_average S x]
              rw [← gaussian_forward_difference_integral_eq_gradient_average S x]
              rw [gaussian_inner_smul_integral_eq (n := n) (∇ (objective S) x)]
      _ = ∫ u : Space n, fd u - lin u ∂gaussianDirectionLaw n := by
            rw [integral_sub hfd_int hlin_int]
  calc
    ‖∇ (gaussianSmoothing S) x - ∇ (objective S) x‖
        = ‖∫ u : Space n, fd u - lin u ∂gaussianDirectionLaw n‖ := by rw [hrepr]
    _ ≤ ∫ u : Space n, ‖fd u - lin u‖ ∂gaussianDirectionLaw n := by
          exact norm_integral_le_integral_norm (fun u => fd u - lin u)
    _ ≤ ∫ u : Space n, (S.μ * S.L / 2) * ‖u‖ ^ (3 : ℕ)
          ∂gaussianDirectionLaw n := by
          exact integral_mono_ae hres_int.norm hdom_int
            (Filter.Eventually.of_forall hpoint)
    _ = (S.μ * S.L / 2) *
          ∫ u : Space n, ‖u‖ ^ (3 : ℕ) ∂gaussianDirectionLaw n := by
          rw [integral_const_mul]

/-- Source comparison (6.1.55): the original gradient square is controlled by
the smoothed gradient square plus the Gaussian smoothing bias budget. -/
private theorem gaussianSmoothing_reverse_gradient_norm_sq_comparison
    (S : Setup n Sample) (x : Space n) :
    ‖∇ (objective S) x‖ ^ (2 : ℕ) ≤
      2 * ‖∇ (gaussianSmoothing S) x‖ ^ (2 : ℕ) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 3) ^ (3 : ℕ) := by
  let gs : Space n := ∇ (gaussianSmoothing S) x
  let g : Space n := ∇ (objective S) x
  let M : ℝ :=
    ∫ u : Space n, ‖u‖ ^ (3 : ℕ) ∂gaussianDirectionLaw n
  let C : ℝ := S.μ * S.L / 2
  have hsplit : g = gs + (g - gs) := by
    abel
  have hyoung :
      ‖g‖ ^ (2 : ℕ) ≤
        2 * ‖gs‖ ^ (2 : ℕ) + 2 * ‖g - gs‖ ^ (2 : ℕ) := by
    calc
      ‖g‖ ^ (2 : ℕ) = ‖gs + (g - gs)‖ ^ (2 : ℕ) := by
        exact congrArg (fun y : Space n => ‖y‖ ^ (2 : ℕ)) hsplit
      _ ≤ 2 * ‖gs‖ ^ (2 : ℕ) + 2 * ‖g - gs‖ ^ (2 : ℕ) := by
        exact SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
          gs (g - gs)
  have herr_norm : ‖g - gs‖ ≤ C * M := by
    simpa [g, gs, C, M, norm_sub_rev] using
      gaussianSmoothing_gradient_error_le S x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg fun u => by positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hμ_nonneg : 0 ≤ S.μ := le_of_lt S.μ_pos
    have hL_nonneg : 0 ≤ S.L := le_of_lt S.L_pos
    nlinarith [mul_nonneg hμ_nonneg hL_nonneg]
  have hCM_nonneg : 0 ≤ C * M := by
    exact mul_nonneg hC_nonneg hM_nonneg
  have herr_sq :
      ‖g - gs‖ ^ (2 : ℕ) ≤ (C * M) ^ (2 : ℕ) := by
    nlinarith [herr_norm, norm_nonneg (g - gs), hCM_nonneg]
  have hM_sq :
      M ^ (2 : ℕ) ≤ ((n : ℝ) + 3) ^ (3 : ℕ) := by
    simpa [M] using gaussian_norm_three_integral_sq_le (n := n)
  have hcoeff_nonneg : 0 ≤ S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 := by
    positivity
  have herr_budget :
      2 * ‖g - gs‖ ^ (2 : ℕ) ≤
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 3) ^ (3 : ℕ) := by
    calc
      2 * ‖g - gs‖ ^ (2 : ℕ)
          ≤ 2 * (C * M) ^ (2 : ℕ) := by
              exact mul_le_mul_of_nonneg_left herr_sq (by norm_num)
      _ = (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2) * M ^ (2 : ℕ) := by
              dsimp [C]
              ring
      _ ≤ S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 3) ^ (3 : ℕ) := by
              exact mul_le_mul_of_nonneg_left hM_sq hcoeff_nonneg
  calc
    ‖∇ (objective S) x‖ ^ (2 : ℕ)
        = ‖g‖ ^ (2 : ℕ) := by rfl
    _ ≤ 2 * ‖gs‖ ^ (2 : ℕ) + 2 * ‖g - gs‖ ^ (2 : ℕ) := hyoung
    _ ≤ 2 * ‖gs‖ ^ (2 : ℕ) +
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 3) ^ (3 : ℕ) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left herr_budget (2 * ‖gs‖ ^ (2 : ℕ))
    _ = 2 * ‖∇ (gaussianSmoothing S) x‖ ^ (2 : ℕ) +
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 3) ^ (3 : ℕ) := by
          rfl

/-- Source-derived unbiasedness of the finite-difference oracle for the smoothed
objective, equation (6.1.60). -/
theorem rsgfOracle_unbiased_smoothed (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        rsgfOracle S x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) =
      ∇ (gaussianSmoothing S) x := by
  haveI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  exact integral_forwardDifferenceOracle_eq_gradient_gaussianSmoothing_of_value_unbiased
    (P := S.P) (nu := gaussianDirectionLaw n) (F := S.F) (f := objective S)
    (mu := S.μ) (x := x)
    (by
      simpa [rsgfOracle] using
        integrable_of_integrable_norm_sq
          (rsgfOracle_aestronglyMeasurable S x)
          (rsgfOracle_norm_sq_integrable_and_secondMoment_le_sampleGradient S x).1)
    (S.szo_assumption15.2.1 x)
    (Filter.Eventually.of_forall fun u => S.szo_assumption15.2.1 (x + S.μ • u))
    (by simpa [objective] using S.szo_assumption15.2.2 x)
    (Filter.Eventually.of_forall fun u => by
      simpa [objective] using S.szo_assumption15.2.2 (x + S.μ • u))
    (by
      rw [gaussian_forward_difference_integral_eq_gradient_average S x]
      simpa [gaussianSmoothing, gaussianDirectionLaw_def] using
        gaussianSmoothing_hasGradientAt_average S x)

/-- The proof-level residual mean-zero fact displayed as (6.1.66). -/
theorem rsgfResidual_mean_zero (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) = 0 := by
  let μζ : Measure (Sample × Space n) := S.P.prod (gaussianDirectionLaw n)
  let G : Sample × Space n → Space n := fun z => rsgfOracle S x z.1 z.2
  let c : Space n := ∇ (gaussianSmoothing S) x
  haveI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure μζ := by
    dsimp [μζ]
    infer_instance
  have hmean : (∫ z, G z ∂μζ) = c := by
    simpa [G, c, μζ] using rsgfOracle_unbiased_smoothed S x
  have hcenter : (∫ z, G z - c ∂μζ) = 0 := by
    by_cases hG : Integrable G μζ
    · calc
        (∫ z, G z - c ∂μζ) =
            (∫ z, G z ∂μζ) - ∫ _z : Sample × Space n, c ∂μζ := by
          exact MeasureTheory.integral_sub hG (MeasureTheory.integrable_const (c := c))
        _ = c - c := by
          simp [hmean]
        _ = 0 := by
          simp
    · have hc : c = 0 := by
        calc
          c = (∫ z, G z ∂μζ) := hmean.symm
          _ = 0 := by
            simpa using (MeasureTheory.integral_undef hG)
      simpa [hc] using hmean
  simpa [SOptLib.oracleEstimatorError, G, c, μζ] using hcenter

/-- Scalarized version of the residual mean-zero identity, using the active
square-integrability route for the Bochner/Fubini side condition. -/
private theorem rsgfResidual_inner_integral_eq_zero
    (S : Setup n Sample) (x d : Space n) :
    (∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2, d⟫_ℝ
          ∂(S.P.prod (gaussianDirectionLaw n))) = 0 := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  letI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  have horacle_int :
      Integrable
        (fun z : Sample × Space n => rsgfOracle S x z.1 z.2)
        (S.P.prod (gaussianDirectionLaw n)) :=
    integrable_of_integrable_norm_sq
      (rsgfOracle_aestronglyMeasurable S x)
      (rsgfOracle_norm_sq_integrable_and_secondMoment_le_sampleGradient S x).1
  have hres_int :
      Integrable
        (fun z : Sample × Space n => (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2)
        (S.P.prod (gaussianDirectionLaw n)) := by
    simpa [SOptLib.oracleEstimatorError] using
      horacle_int.sub (integrable_const (c := ∇ (gaussianSmoothing S) x))
  have hlin :=
    ContinuousLinearMap.integral_comp_comm
      (L := (innerSLFlip ℝ d)) hres_int
  have hvec_zero :
      (∫ z : Sample × Space n,
        (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) = 0 :=
    rsgfResidual_mean_zero S x
  calc
    (∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2, d⟫_ℝ
          ∂(S.P.prod (gaussianDirectionLaw n)))
        = ∫ z : Sample × Space n,
            (innerSLFlip ℝ d) ((fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2)
              ∂(S.P.prod (gaussianDirectionLaw n)) := by
            simp only [innerSLFlip_apply_apply]
    _ = (innerSLFlip ℝ d)
          (∫ z : Sample × Space n,
            (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) := hlin
    _ = 0 := by
            rw [hvec_zero]
            simp

/-- Fixed-query scalar residual integrability.  This is the fiberwise L2
side-condition used before resampling a fresh prefix coordinate. -/
private theorem rsgfResidual_norm_sq_integrable
    (S : Setup n Sample) (x : Space n) :
    Integrable
      (fun z : Sample × Space n => ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2‖ ^ (2 : ℕ))
      (S.P.prod (gaussianDirectionLaw n)) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  letI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  have horacle_sq :
      Integrable
        (fun z : Sample × Space n => ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ))
        (S.P.prod (gaussianDirectionLaw n)) :=
    (rsgfOracle_norm_sq_integrable_and_secondMoment_le_sampleGradient S x).1
  have htarget_sq :
      Integrable
        (fun _z : Sample × Space n => ‖∇ (gaussianSmoothing S) x‖ ^ (2 : ℕ))
        (S.P.prod (gaussianDirectionLaw n)) :=
    integrable_const _
  simpa [SOptLib.oracleEstimatorError] using
    (integrable_sq_norm_sub
      (P := S.P.prod (gaussianDirectionLaw n))
      (u := fun z : Sample × Space n => rsgfOracle S x z.1 z.2)
      (v := fun _z : Sample × Space n => ∇ (gaussianSmoothing S) x)
      (rsgfOracle_aestronglyMeasurable S x)
      (aestronglyMeasurable_const)
      horacle_sq
      htarget_sq)

/-- Centering the RSGF oracle by its smoothed-gradient mean does not increase
the fixed-query second moment.  This is the variance-contraction bridge used
when building residual-inner budgets from oracle second-moment bounds. -/
private theorem rsgfResidual_secondMoment_le_oracle_secondMoment
    (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2‖ ^ (2 : ℕ)
          ∂(S.P.prod (gaussianDirectionLaw n))) ≤
      ∫ z : Sample × Space n,
        ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ)
          ∂(S.P.prod (gaussianDirectionLaw n)) := by
  let μζ : Measure (Sample × Space n) := S.P.prod (gaussianDirectionLaw n)
  let g : Sample × Space n → Space n := fun z => rsgfOracle S x z.1 z.2
  let m : Sample × Space n → Space n := fun _z => ∇ (gaussianSmoothing S) x
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  have hg_meas :
      AEStronglyMeasurable g μζ := by
    simpa [g, μζ] using rsgfOracle_aestronglyMeasurable S x
  have hm_meas :
      AEStronglyMeasurable m μζ := by
    exact aestronglyMeasurable_const
  have hg_sq :
      Integrable (fun z : Sample × Space n => ‖g z‖ ^ (2 : ℕ)) μζ := by
    simpa [g, μζ] using
      (rsgfOracle_norm_sq_integrable_and_secondMoment_le_sampleGradient S x).1
  have hm_sq :
      Integrable (fun z : Sample × Space n => ‖m z‖ ^ (2 : ℕ)) μζ := by
    simpa [m] using
      (integrable_const
        (c := ‖∇ (gaussianSmoothing S) x‖ ^ (2 : ℕ)) :
        Integrable
          (fun _z : Sample × Space n =>
            ‖∇ (gaussianSmoothing S) x‖ ^ (2 : ℕ)) μζ)
  have h_inner_gm :
      Integrable (fun z : Sample × Space n => ⟪g z, m z⟫_ℝ) μζ :=
    integrable_inner_of_integrable_sq_norm hg_meas hm_meas hg_sq hm_sq
  have h_inner_mm :
      Integrable (fun z : Sample × Space n => ⟪m z, m z⟫_ℝ) μζ := by
    simpa [real_inner_self_eq_norm_sq] using hm_sq
  have hzero :
      (∫ z : Sample × Space n, ⟪g z - m z, m z⟫_ℝ ∂μζ) = 0 := by
    simpa [g, m, μζ, SOptLib.oracleEstimatorError] using
      rsgfResidual_inner_integral_eq_zero S x (∇ (gaussianSmoothing S) x)
  have hcross_gm :
      (∫ z : Sample × Space n, ⟪g z, m z⟫_ℝ ∂μζ) =
        ∫ z : Sample × Space n, ‖m z‖ ^ (2 : ℕ) ∂μζ := by
    have hzero' :
        (∫ z : Sample × Space n,
          (⟪g z, m z⟫_ℝ - ⟪m z, m z⟫_ℝ) ∂μζ) = 0 := by
      simpa [inner_sub_left] using hzero
    have hsub :
        (∫ z : Sample × Space n,
          (⟪g z, m z⟫_ℝ - ⟪m z, m z⟫_ℝ) ∂μζ) =
          (∫ z : Sample × Space n, ⟪g z, m z⟫_ℝ ∂μζ) -
            ∫ z : Sample × Space n, ⟪m z, m z⟫_ℝ ∂μζ :=
      MeasureTheory.integral_sub h_inner_gm h_inner_mm
    rw [hsub] at hzero'
    have hmm :
        (∫ z : Sample × Space n, ⟪m z, m z⟫_ℝ ∂μζ) =
          ∫ z : Sample × Space n, ‖m z‖ ^ (2 : ℕ) ∂μζ := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro z
      simp [real_inner_self_eq_norm_sq]
    linarith
  have hcross_eq :
      (∫ z : Sample × Space n, ⟪m z, g z⟫_ℝ ∂μζ) =
        ∫ z : Sample × Space n, ‖m z‖ ^ (2 : ℕ) ∂μζ := by
    simpa [real_inner_comm] using hcross_gm
  have hcontract :=
    integral_norm_sq_sub_le_integral_norm_sq_of_inner_sub_zero
      μζ (g := g) (m := m) hg_meas hm_meas hg_sq hm_sq hcross_eq
  simpa [SOptLib.oracleEstimatorError, g, m, μζ] using hcontract

/-- Fixed-query version of the first inequality in (6.1.67).  Applying Lemma 6.2
to `F(·, ξ)` bounds the finite-difference oracle by the second moment of the
canonical sample gradient of the same sample function. -/
theorem rsgfOracle_secondMoment_le_sampleGradient
    (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ) ∂(S.P.prod (gaussianDirectionLaw n))) ≤
      2 * ((n : ℝ) + 4) *
          (∫ ξ, ‖gradient (fun y => S.F y ξ) x‖ ^ (2 : ℕ) ∂S.P) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) := by
  exact (rsgfOracle_norm_sq_integrable_and_secondMoment_le_sampleGradient S x).2

/-- Fixed-query version of the complete second-moment estimate in (6.1.67), after
Assumption 13 is applied to the canonical sample-gradient oracle. -/
theorem rsgfOracle_secondMoment_le_gradient_sigma
    (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ) ∂(S.P.prod (gaussianDirectionLaw n))) ≤
      2 * ((n : ℝ) + 4) *
          (‖∇ (objective S) x‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ)) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) := by
  have hbase := rsgfOracle_secondMoment_le_sampleGradient S x
  have hsg := sampleGradient_secondMoment_le S x
  have hc : 0 ≤ 2 * ((n : ℝ) + 4) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsg hc
  nlinarith [hbase, hmul]

/-- Numerator weight in the random-output mass formula (6.1.61). -/
def rsgfWeightNumerator (S : Setup n Sample) (k : ℕ) : ℝ :=
  S.γ k - 2 * S.L * ((n : ℝ) + 4) * S.γ k ^ (2 : ℕ)

/-- Denominator in the random-output mass formula (6.1.61). -/
def rsgfWeightDenominator (S : Setup n Sample) (N : ℕ) : ℝ :=
  Finset.sum (Icc 1 N) (fun k => rsgfWeightNumerator S k)

/-- The finite support `{1, ..., N}` of the RSGF output index `R`. -/
abbrev RsgfOutputIndex (N : ℕ) := {k : ℕ // k ∈ Icc 1 N}

/-- The combined fresh sample `ζ_k = (ξ_k, u_k)` used in the proof. -/
abbrev RsgfZeta (n : ℕ) (Sample : Type*) := Sample × Space n

/-- The finite prefix `ζ_[N] = (ζ_1, ..., ζ_N)` appearing in Theorem 6.3. -/
abbrev RsgfSamplePrefix (n : ℕ) (Sample : Type*) (N : ℕ) :=
  RsgfOutputIndex N → RsgfZeta n Sample

/-- Joint one-step law of `(ξ, u)`, with `ξ ~ P` and `u` standard Gaussian. -/
noncomputable def rsgfZetaLaw (S : Setup n Sample) : Measure (RsgfZeta n Sample) :=
  S.P.prod (gaussianDirectionLaw n)

/-- Canonical product law of the finite prefix `ζ_[N]`. -/
noncomputable def rsgfPrefixLaw (S : Setup n Sample) (N : ℕ) :
    Measure (RsgfSamplePrefix n Sample N) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  exact Measure.pi (fun _ : RsgfOutputIndex N => rsgfZetaLaw S)

/-- Replacing one finite-prefix coordinate by an independent fresh draw with
the same marginal preserves the iid finite prefix law. -/
private theorem rsgfPrefixLaw_replace_coordinate_measurePreserving
    (S : Setup n Sample) {N : ℕ} (R : RsgfOutputIndex N) :
    MeasurePreserving
      (fun q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample =>
        Function.update q.1 R q.2)
      ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))
      (rsgfPrefixLaw S N) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  simpa [rsgfPrefixLaw] using
    (measurePreserving_update_coordinate_prod_pi (ν := rsgfZetaLaw S) R)

/-- Admissibility of the real weights in the source PMF formula (6.1.61).
Theorem 6.3 states that `P_R` is a probability mass function with atoms
`(γ_k - 2L(n+4)γ_k^2) / ∑_{k=1}^N (γ_k - 2L(n+4)γ_k^2)`; this predicate is the
Lean real-weight boundary needed for that displayed formula to denote a PMF.
It is not derived from the printed upper bound alone, since the source does not
separately state positivity of each `γ_k`. -/
def RsgfOutputWeightsAdmissible (S : Setup n Sample) (N : ℕ) : Prop :=
  SOptLib.FiniteWindowWeightsAdmissible (Icc 1 N)
    (fun k => rsgfWeightNumerator S k)

/-- Positive source stepsizes below the Theorem 6.3 upper bound make the
displayed weights in (6.1.61) admissible for normalization.  The paper-facing
theorems below do not use this as an extra theorem-head assumption; they take
the PMF admissibility boundary directly from the source statement that `P_R` is
a probability mass function with these atoms. -/
theorem rsgfOutputWeights_admissible_of_positive_stepsizes
    (S : Setup n Sample) {N : ℕ} (hN : 1 ≤ N)
    (hγ_pos : ∀ k ∈ Icc 1 N, 0 < S.γ k)
    (hγ_upper : ∀ k ∈ Icc 1 N, S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹) :
    RsgfOutputWeightsAdmissible S N := by
  have hnum_pos : ∀ k, k ∈ Icc 1 N → 0 < rsgfWeightNumerator S k := by
    intro k hk
    let c : ℝ := 2 * ((n : ℝ) + 4) * S.L
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hn4_pos : 0 < (n : ℝ) + 4 := by nlinarith
    have hc_pos : 0 < c := by
      dsimp [c]
      exact mul_pos (mul_pos (by norm_num) hn4_pos) S.L_pos
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    have hmul_lt : c * S.γ k < 1 := by
      calc
        c * S.γ k < c * c⁻¹ := mul_lt_mul_of_pos_left (hγ_upper k hk) hc_pos
        _ = 1 := by
          field_simp [hc_ne]
    have hfactor_pos : 0 < 1 - c * S.γ k := sub_pos.mpr hmul_lt
    have hprod_pos : 0 < S.γ k * (1 - c * S.γ k) :=
      mul_pos (hγ_pos k hk) hfactor_pos
    have hrewrite : rsgfWeightNumerator S k = S.γ k * (1 - c * S.γ k) := by
      dsimp [rsgfWeightNumerator, c]
      ring
    simpa [hrewrite] using hprod_pos
  have h_nonneg : ∀ k, k ∈ Icc 1 N → 0 ≤ rsgfWeightNumerator S k := by
    intro k hk
    exact le_of_lt (hnum_pos k hk)
  have h_one_mem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, hN⟩
  have h_one_pos : 0 < rsgfWeightNumerator S 1 := hnum_pos 1 h_one_mem
  simpa [RsgfOutputWeightsAdmissible] using
    (SOptLib.FiniteWindowWeightsAdmissible.of_nonneg_of_pos
      (times := Icc 1 N)
      (weight := fun k => rsgfWeightNumerator S k)
      h_nonneg
      (k := 1)
      h_one_mem
      h_one_pos)

/-- The source PMF choice makes the normalizing denominator positive. -/
theorem rsgfWeightDenominator_pos (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N) :
    0 < rsgfWeightDenominator S N := by
  exact SOptLib.FiniteWindowWeightsAdmissible.sum_pos hPR

/-- Canonical paper PMF `P_R` from (6.1.61), constructed by normalizing the
source weights on `{1, ..., N}` after the source statement that the displayed
formula is a probability mass function supplies real-weight admissibility. -/
noncomputable def rsgfOutputPMF (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    PMF (RsgfOutputIndex N) :=
  SOptLib.normalizedFiniteWindowPMF (Icc 1 N)
    (fun k => rsgfWeightNumerator S k)
    (SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR)
    (SOptLib.FiniteWindowWeightsAdmissible.sum_pos hPR)

/-- The canonical RSGF output PMF satisfies the displayed atom formula (6.1.61). -/
theorem rsgfOutputPMF_apply (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N)
    (R : RsgfOutputIndex N) :
    rsgfOutputPMF S N hPR R =
      ENNReal.ofReal (rsgfWeightNumerator S R.1 / rsgfWeightDenominator S N) := by
  rfl

/-- The canonical RSGF output PMF realizes the finite-window normalized-weight
specification.  This is a derived property of the canonical `def`, not an input
contract for the paper theorem. -/
theorem rsgfOutputPMF_spec (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N) :
    SOptLib.FiniteWindowPMFSpec (Icc 1 N) (fun k => rsgfWeightNumerator S k)
      (rsgfOutputPMF S N hPR) := by
  exact SOptLib.finiteWindowPMFSpec_of_normalizedFiniteWindowPMF
    (Icc 1 N) (fun k => rsgfWeightNumerator S k)
    hPR

/-- Prefix recursion whose index `0` stores `x₁` and whose prefix law contains
exactly the finite samples `ζ_1, ..., ζ_N`. -/
def rsgfPrefixIterate0 (S : Setup n Sample) {N : ℕ}
    (ζ : RsgfSamplePrefix n Sample N) : (m : ℕ) → m ≤ N → Space n
  | 0, _ => S.x₁
  | k + 1, hk =>
      let hk_mem : k + 1 ∈ Icc 1 N := mem_Icc.mpr ⟨Nat.succ_pos k, hk⟩
      rsgfStep S (k + 1)
        (rsgfPrefixIterate0 S ζ k (Nat.le_of_succ_le hk))
        (ζ ⟨k + 1, hk_mem⟩).1
        (ζ ⟨k + 1, hk_mem⟩).2

/-- Paper iterate `x_R` evaluated from the finite prefix `ζ_[N]`. -/
def rsgfPrefixIterate (S : Setup n Sample) {N : ℕ}
    (ζ : RsgfSamplePrefix n Sample N) (R : RsgfOutputIndex N) : Space n :=
  rsgfPrefixIterate0 S ζ (R.1 - 1)
    (le_trans (Nat.sub_le R.1 1) (mem_Icc.mp R.2).2)

/-- The prefix iterate at time `m` only uses samples through time `m`.  In
particular, changing a later coordinate leaves it unchanged. -/
private theorem rsgfPrefixIterate0_update_of_lt
    (S : Setup n Sample) {N : ℕ}
    (ζ : RsgfSamplePrefix n Sample N)
    {i m : ℕ} (hi : i ∈ Icc 1 N) (hm : m ≤ N)
    (hmi : m < i) (z : RsgfZeta n Sample) :
    rsgfPrefixIterate0 S (Function.update ζ ⟨i, hi⟩ z) m hm =
      rsgfPrefixIterate0 S ζ m hm := by
  induction m with
  | zero =>
      simp [rsgfPrefixIterate0]
  | succ m ih =>
      have hprev_lt : m < i := by omega
      have hcoord_ne :
          (⟨m + 1, mem_Icc.mpr ⟨Nat.succ_pos m, hm⟩⟩ :
              RsgfOutputIndex N) ≠ ⟨i, hi⟩ := by
        intro h
        have hval : m + 1 = i := congrArg Subtype.val h
        omega
      simp [rsgfPrefixIterate0, ih (Nat.le_of_succ_le hm) hprev_lt,
        Function.update_of_ne hcoord_ne]

/-- The paper iterate `x_k` is adapted to the strict prefix: it does not depend
on the fresh coordinate `ζ_k` used by the update from `x_k` to `x_{k+1}`. -/
private theorem rsgf_prefix_iterate_current_coordinate_independent
    (S : Setup n Sample) {N k : ℕ}
    (ζ : RsgfSamplePrefix n Sample N) (hk : k ∈ Icc 1 N)
    (z : RsgfZeta n Sample) :
    rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩ =
      rsgfPrefixIterate S ζ ⟨k, hk⟩ := by
  have hlt : k - 1 < k := by
    have hk_pos : 0 < k := lt_of_lt_of_le zero_lt_one (mem_Icc.mp hk).1
    omega
  simpa [rsgfPrefixIterate] using
    rsgfPrefixIterate0_update_of_lt (S := S) ζ hk
      (le_trans (Nat.sub_le k 1) (mem_Icc.mp hk).2) hlt z

/-- The first prefix iterate is the deterministic initial point `x₁`. -/
private theorem rsgfPrefixIterate_first_eq
    (S : Setup n Sample) {N : ℕ} (h1 : 1 ∈ Icc 1 N)
    (ζ : RsgfSamplePrefix n Sample N) :
    rsgfPrefixIterate S ζ ⟨1, h1⟩ = S.x₁ := by
  simp [rsgfPrefixIterate, rsgfPrefixIterate0]

/-- Base case for the convex prefix budget induction: at output index `1`, the
prefix iterate is deterministic, so both the squared distance to `xStar` and
the objective gap are integrable under the prefix law. -/
private theorem rsgfPrefixIterate_first_l2_gap_integrable
    (S : Setup n Sample) {N : ℕ} (h1 : 1 ∈ Icc 1 N)
    (xStar : Space n)
    (hoptimal : ∀ y : Space n, objective S xStar ≤ objective S y) :
    Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfPrefixIterate S ζ ⟨1, h1⟩ - xStar‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) ∧
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨1, h1⟩) - fStar S)
        (rsgfPrefixLaw S N) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  have hl2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfPrefixIterate S ζ ⟨1, h1⟩ - xStar‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    refine (integrable_const
      (‖S.x₁ - xStar‖ ^ (2 : ℕ))).congr ?_
    exact Filter.Eventually.of_forall fun ζ => by
      simp [rsgfPrefixIterate_first_eq S h1 ζ]
  have hgap :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨1, h1⟩) - fStar S)
        (rsgfPrefixLaw S N) := by
    refine (integrable_const (objective S S.x₁ - fStar S)).congr ?_
    exact Filter.Eventually.of_forall fun ζ => by
      simp [rsgfPrefixIterate_first_eq S h1 ζ]
  exact ⟨hl2, hgap⟩

/-- Split-coordinate form of adaptedness: in the resampled representation, the
query `x_k` depends only on the rest prefix and not on the fresh selected
coordinate. -/
private theorem rsgfPrefixIterate_resampled_current_coordinate_independent
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (η : ({Q : RsgfOutputIndex N // Q ≠ ⟨k, hk⟩} → RsgfZeta n Sample))
    (z z' : RsgfZeta n Sample) :
    rsgfPrefixIterate S
        (fun Q : RsgfOutputIndex N =>
          if h : Q = ⟨k, hk⟩ then z else η ⟨Q, h⟩)
        ⟨k, hk⟩ =
      rsgfPrefixIterate S
        (fun Q : RsgfOutputIndex N =>
          if h : Q = ⟨k, hk⟩ then z' else η ⟨Q, h⟩)
        ⟨k, hk⟩ := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let ζ0 : RsgfSamplePrefix n Sample N := fun Q =>
    if h : Q = R then z' else η ⟨Q, h⟩
  have hζ :
      (fun Q : RsgfOutputIndex N =>
        if h : Q = R then z else η ⟨Q, h⟩) =
        Function.update ζ0 R z := by
    funext Q
    by_cases hQ : Q = R
    · subst hQ
      simp [ζ0]
    · simp [ζ0, hQ]
  calc
    rsgfPrefixIterate S
        (fun Q : RsgfOutputIndex N =>
          if h : Q = ⟨k, hk⟩ then z else η ⟨Q, h⟩)
        ⟨k, hk⟩
        = rsgfPrefixIterate S (Function.update ζ0 R z) R := by
            simp [R, hζ]
    _ = rsgfPrefixIterate S ζ0 R := by
            simpa [R] using
              rsgf_prefix_iterate_current_coordinate_independent
                S ζ0 hk z
    _ = rsgfPrefixIterate S
        (fun Q : RsgfOutputIndex N =>
          if h : Q = ⟨k, hk⟩ then z' else η ⟨Q, h⟩)
        ⟨k, hk⟩ := by
            simp [R, ζ0]

/-- Fiberwise integrability of the residual scalar after the fresh coordinate
is resampled.  Adaptedness reduces the query and multiplier to fixed vectors
inside the fresh-coordinate integral. -/
private theorem integrable_prod_of_nonneg_fiber_integral_le_integrable_bound
    {W Smp : Type*} [MeasurableSpace W] [MeasurableSpace Smp]
    {μ : Measure W} {ν : Measure Smp} [SFinite ν]
    {φ : W → Smp → ℝ} {B : W → ℝ}
    (hφ_prod :
      AEStronglyMeasurable
        (fun p : W × Smp => φ p.1 p.2) (μ.prod ν))
    (hφ_nonneg : ∀ w s, 0 ≤ φ w s)
    (hfixed_int : ∀ w, Integrable (fun s => φ w s) ν)
    (hB_int : Integrable B μ)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ B w) :
    Integrable (fun p : W × Smp => φ p.1 p.2) (μ.prod ν) := by
  exact _root_.integrable_prod_of_fiber_integral_norm_le_integrable_bound
    hφ_prod
    (Filter.Eventually.of_forall hfixed_int)
    hB_int
    (Filter.Eventually.of_forall fun w => by
      have h_norm_eq :
          (∫ s, ‖φ w s‖ ∂ν) = ∫ s, φ w s ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro s
        exact Real.norm_of_nonneg (hφ_nonneg w s)
      rw [h_norm_eq]
      exact hfixed_bound w)

/-- Signed product-space `L¹` majorant with a non-uniform outer bound.  This is
the same bridge as `integrable_prod_of_nonneg_fiber_integral_le_integrable_bound`,
applied to the pointwise norm of a signed observable and converted back through
`integrable_norm_iff`. -/
private theorem rsgf_prefix_residual_inner_fiber_integral_eq_zero
    (S : Setup n Sample) {N k : ℕ}
    (ζ : RsgfSamplePrefix n Sample N) (hk : k ∈ Icc 1 N)
    (xStar : Space n) :
    (∫ z : RsgfZeta n Sample,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩ -
            xStar⟫_ℝ ∂rsgfZetaLaw S) = 0 := by
  change
    (∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩ -
            xStar⟫_ℝ ∂(S.P.prod (gaussianDirectionLaw n))) = 0
  calc
    (∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩ -
            xStar⟫_ℝ ∂(S.P.prod (gaussianDirectionLaw n)))
        =
      ∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2,
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
          ∂(S.P.prod (gaussianDirectionLaw n)) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun z => by
              have hx :=
                rsgf_prefix_iterate_current_coordinate_independent S ζ hk z
              simp [hx]
    _ = 0 :=
        rsgfResidual_inner_integral_eq_zero S
          (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar)

/-- Split the finite prefix product law at one output coordinate.  The selected
coordinate is integrated as a fresh `rsgfZetaLaw` sample and the remaining
coordinates are integrated under their product law. -/
private theorem rsgfPrefixLaw_coordinate_resampling_integral
    (S : Setup n Sample) {N : ℕ} (R : RsgfOutputIndex N)
    (Φ : RsgfSamplePrefix n Sample N → ℝ)
    (hΦ : Integrable Φ (rsgfPrefixLaw S N)) :
    (∫ ζ : RsgfSamplePrefix n Sample N, Φ ζ ∂rsgfPrefixLaw S N) =
      ∫ η : ({Q : RsgfOutputIndex N // Q ≠ R} → RsgfZeta n Sample),
        ∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex N =>
            if h : Q = R then z else η ⟨Q, h⟩)
          ∂rsgfZetaLaw S
        ∂(Measure.pi
            (fun _ : {Q : RsgfOutputIndex N // Q ≠ R} => rsgfZetaLaw S)) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  simpa [rsgfPrefixLaw] using
    (integral_pi_eq_integral_subtype_compl_integral_coordinate
      (ν := rsgfZetaLaw S) R Φ hΦ)

/-- Integrability transport for the same finite-coordinate resampling
equivalence used by `rsgfPrefixLaw_coordinate_resampling_integral`. -/
private theorem rsgf_prefix_residual_inner_prefix_integral_eq_zero_of_integrable
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (xStar : Space n)
    (hΦ_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
        ∂rsgfPrefixLaw S N) = 0 := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
      rsgfPrefixIterate S ζ R - xStar⟫_ℝ
  have hresample :=
    rsgfPrefixLaw_coordinate_resampling_integral S R Φ hΦ_int
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  have hinner_zero :
      ∀ η : ({Q : RsgfOutputIndex N // Q ≠ R} → RsgfZeta n Sample),
        (∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex N =>
            if h : Q = R then z else η ⟨Q, h⟩) ∂rsgfZetaLaw S) = 0 := by
    intro η
    let z0 : RsgfZeta n Sample :=
      Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure (rsgfZetaLaw S))
    let ζ0 : RsgfSamplePrefix n Sample N := fun Q =>
      if h : Q = R then z0 else η ⟨Q, h⟩
    have hupdate :
        (fun z : RsgfZeta n Sample => fun Q : RsgfOutputIndex N =>
            if h : Q = R then z else η ⟨Q, h⟩) =
          fun z : RsgfZeta n Sample => Function.update ζ0 R z := by
      funext z Q
      by_cases hQ : Q = R
      · subst hQ
        simp [ζ0]
      · simp [ζ0, hQ]
    calc
      (∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex N =>
            if h : Q = R then z else η ⟨Q, h⟩) ∂rsgfZetaLaw S)
          = ∫ z : RsgfZeta n Sample, Φ (Function.update ζ0 R z) ∂rsgfZetaLaw S := by
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun z => by
                change Φ ((fun z : RsgfZeta n Sample =>
                  fun Q : RsgfOutputIndex N =>
                    if h : Q = R then z else η ⟨Q, h⟩) z) =
                  Φ (Function.update ζ0 R z)
                rw [hupdate]
      _ = 0 := by
              simpa [Φ, R] using
                rsgf_prefix_residual_inner_fiber_integral_eq_zero
                  S ζ0 hk xStar
  calc
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
        ∂rsgfPrefixLaw S N)
        = ∫ ζ : RsgfSamplePrefix n Sample N, Φ ζ ∂rsgfPrefixLaw S N := by
            rfl
    _ = ∫ η : ({Q : RsgfOutputIndex N // Q ≠ R} → RsgfZeta n Sample),
          ∫ z : RsgfZeta n Sample,
            Φ (fun Q : RsgfOutputIndex N =>
              if h : Q = R then z else η ⟨Q, h⟩)
            ∂rsgfZetaLaw S
          ∂(Measure.pi
              (fun _ : {Q : RsgfOutputIndex N // Q ≠ R} => rsgfZetaLaw S)) := hresample
    _ = ∫ _η : ({Q : RsgfOutputIndex N // Q ≠ R} → RsgfZeta n Sample),
          (0 : ℝ)
          ∂(Measure.pi
              (fun _ : {Q : RsgfOutputIndex N // Q ≠ R} => rsgfZetaLaw S)) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun η => hinner_zero η
    _ = 0 := by simp

/-- Fiberwise residual cancellation for the nonconvex descent residual
multiplied by the smoothed gradient at the adapted query. -/
private theorem rsgf_prefix_residual_smoothing_grad_inner_fiber_integral_eq_zero
    (S : Setup n Sample) {N k : ℕ}
    (ζ : RsgfSamplePrefix n Sample N) (hk : k ∈ Icc 1 N) :
    (∫ z : RsgfZeta n Sample,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          ∇ (gaussianSmoothing S)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)⟫_ℝ
        ∂rsgfZetaLaw S) = 0 := by
  change
    (∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          ∇ (gaussianSmoothing S)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)⟫_ℝ
        ∂(S.P.prod (gaussianDirectionLaw n))) = 0
  calc
    (∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          ∇ (gaussianSmoothing S)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)⟫_ℝ
        ∂(S.P.prod (gaussianDirectionLaw n)))
        =
      ∫ z : Sample × Space n,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2,
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
        ∂(S.P.prod (gaussianDirectionLaw n)) := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun z => by
            have hx :=
              rsgf_prefix_iterate_current_coordinate_independent S ζ hk z
            simp [hx]
    _ = 0 :=
        rsgfResidual_inner_integral_eq_zero S
          (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩))

/-- Prefix-law residual cancellation for the nonconvex descent residual once
the smoothed-gradient scalarization is known to be integrable. -/
private theorem rsgf_prefix_residual_smoothing_grad_inner_integral_eq_zero_of_integrable
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hΦ_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            ∇ (gaussianSmoothing S)
              (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ)
        (rsgfPrefixLaw S N)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
        ∂rsgfPrefixLaw S N) = 0 := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
      ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)⟫_ℝ
  have hresample :=
    rsgfPrefixLaw_coordinate_resampling_integral S R Φ hΦ_int
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  have hinner_zero :
      ∀ η : ({Q : RsgfOutputIndex N // Q ≠ R} → RsgfZeta n Sample),
        (∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex N =>
            if h : Q = R then z else η ⟨Q, h⟩) ∂rsgfZetaLaw S) = 0 := by
    intro η
    let z0 : RsgfZeta n Sample :=
      Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure (rsgfZetaLaw S))
    let ζ0 : RsgfSamplePrefix n Sample N := fun Q =>
      if h : Q = R then z0 else η ⟨Q, h⟩
    have hupdate :
        (fun z : RsgfZeta n Sample => fun Q : RsgfOutputIndex N =>
            if h : Q = R then z else η ⟨Q, h⟩) =
          fun z : RsgfZeta n Sample => Function.update ζ0 R z := by
      funext z Q
      by_cases hQ : Q = R
      · subst hQ
        simp [ζ0]
      · simp [ζ0, hQ]
    calc
      (∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex N =>
            if h : Q = R then z else η ⟨Q, h⟩) ∂rsgfZetaLaw S)
          = ∫ z : RsgfZeta n Sample, Φ (Function.update ζ0 R z) ∂rsgfZetaLaw S := by
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall fun z => by
                change Φ ((fun z : RsgfZeta n Sample =>
                  fun Q : RsgfOutputIndex N =>
                    if h : Q = R then z else η ⟨Q, h⟩) z) =
                  Φ (Function.update ζ0 R z)
                rw [hupdate]
      _ = 0 := by
              simpa [Φ, R] using
                rsgf_prefix_residual_smoothing_grad_inner_fiber_integral_eq_zero
                  S ζ0 hk
  calc
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
        ∂rsgfPrefixLaw S N)
        = ∫ ζ : RsgfSamplePrefix n Sample N, Φ ζ ∂rsgfPrefixLaw S N := by
            rfl
    _ = ∫ η : ({Q : RsgfOutputIndex N // Q ≠ R} → RsgfZeta n Sample),
          ∫ z : RsgfZeta n Sample,
            Φ (fun Q : RsgfOutputIndex N =>
              if h : Q = R then z else η ⟨Q, h⟩)
            ∂rsgfZetaLaw S
          ∂(Measure.pi
              (fun _ : {Q : RsgfOutputIndex N // Q ≠ R} => rsgfZetaLaw S)) := hresample
    _ = ∫ _η : ({Q : RsgfOutputIndex N // Q ≠ R} → RsgfZeta n Sample),
          (0 : ℝ)
          ∂(Measure.pi
              (fun _ : {Q : RsgfOutputIndex N // Q ≠ R} => rsgfZetaLaw S)) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun η => hinner_zero η
    _ = 0 := by simp

/-- Pointwise smoothed descent for one RSGF prefix update, with the oracle
split into the smoothed gradient plus the residual. -/
private theorem rsgf_prefix_smoothing_descent_step_pointwise
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N) (ζ : RsgfSamplePrefix n Sample N) :
    gaussianSmoothing S (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2) ≤
      gaussianSmoothing S (rsgfPrefixIterate S ζ ⟨k, hk⟩) -
        S.γ k *
          ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ) -
        S.γ k *
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2⟫_ℝ +
        (S.L / 2) * S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
  classical
  let x : Space n := rsgfPrefixIterate S ζ ⟨k, hk⟩
  let G : Space n :=
    rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2
  let Δ : Space n :=
    (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2
  let grad : Space n := ∇ (gaussianSmoothing S) x
  have hnext :
      rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 =
        x - S.γ k • G := by
    cases k with
    | zero =>
        have hk_pos : 1 ≤ 0 := (mem_Icc.mp hk).1
        omega
    | succ j =>
        simp [x, G, rsgfPrefixIterate, rsgfPrefixIterate0, rsgfStep_def]
  have hupper :
      gaussianSmoothing S (x - S.γ k • G) ≤
        gaussianSmoothing S x +
          ⟪grad, (x - S.γ k • G) - x⟫_ℝ +
          (S.L / 2) * ‖(x - S.γ k • G) - x‖ ^ (2 : ℕ) := by
    have hdes := gaussianSmoothing_smoothDescentBound S x (x - S.γ k • G)
    have hlin :
        gaussianSmoothing S (x - S.γ k • G) -
            gaussianSmoothing S x -
            ⟪∇ (gaussianSmoothing S) x, (x - S.γ k • G) - x⟫_ℝ ≤
          (S.L / 2) * ‖(x - S.γ k • G) - x‖ ^ (2 : ℕ) :=
      (le_abs_self _).trans hdes
    simpa [grad] using (by linarith : gaussianSmoothing S (x - S.γ k • G) ≤
      gaussianSmoothing S x +
        ⟪∇ (gaussianSmoothing S) x, (x - S.γ k • G) - x⟫_ℝ +
        (S.L / 2) * ‖(x - S.γ k • G) - x‖ ^ (2 : ℕ))
  have hG_split : G = grad + Δ := by
    simp [G, Δ, grad, x, SOptLib.oracleEstimatorError]
  have hinnerG :
      ⟪grad, G⟫_ℝ = ‖grad‖ ^ (2 : ℕ) + ⟪grad, Δ⟫_ℝ := by
    rw [hG_split]
    simp [inner_add_right, real_inner_self_eq_norm_sq]
  have hinner :
      ⟪grad, (x - S.γ k • G) - x⟫_ℝ =
        -S.γ k * ‖grad‖ ^ (2 : ℕ) - S.γ k * ⟪grad, Δ⟫_ℝ := by
    have hdisp : (x - S.γ k • G) - x = (-S.γ k) • G := by
      module
    calc
      ⟪grad, (x - S.γ k • G) - x⟫_ℝ
          = (-S.γ k) * ⟪grad, G⟫_ℝ := by
              rw [hdisp, inner_smul_right]
      _ = -S.γ k * ⟪grad, G⟫_ℝ := by
              ring
      _ = -S.γ k * ‖grad‖ ^ (2 : ℕ) - S.γ k * ⟪grad, Δ⟫_ℝ := by
              rw [hinnerG]
              ring
  have hnorm :
      ‖(x - S.γ k • G) - x‖ ^ (2 : ℕ) =
        S.γ k ^ (2 : ℕ) * ‖G‖ ^ (2 : ℕ) := by
    calc
      ‖(x - S.γ k • G) - x‖ ^ (2 : ℕ)
          = ‖S.γ k • G‖ ^ (2 : ℕ) := by
              congr 1
              rw [← norm_neg ((x - S.γ k • G) - x)]
              congr 1
              abel
      _ = S.γ k ^ (2 : ℕ) * ‖G‖ ^ (2 : ℕ) := by
              rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  calc
    gaussianSmoothing S (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2)
        = gaussianSmoothing S (x - S.γ k • G) := by
            rw [hnext]
    _ ≤ gaussianSmoothing S x +
          ⟪grad, (x - S.γ k • G) - x⟫_ℝ +
          (S.L / 2) * ‖(x - S.γ k • G) - x‖ ^ (2 : ℕ) := hupper
    _ = gaussianSmoothing S x -
          S.γ k * ‖grad‖ ^ (2 : ℕ) -
          S.γ k * ⟪grad, Δ⟫_ℝ +
          (S.L / 2) * S.γ k ^ (2 : ℕ) * ‖G‖ ^ (2 : ℕ) := by
            rw [hinner, hnorm]
            ring
    _ =
      gaussianSmoothing S (rsgfPrefixIterate S ζ ⟨k, hk⟩) -
        S.γ k *
          ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ) -
        S.γ k *
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2⟫_ℝ +
        (S.L / 2) * S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
        rfl

/-- Joint law of the selected output index and the full prefix randomness
`(R, ζ_[N])`, using the canonical paper PMF `P_R`. -/
noncomputable def rsgfSelectedRunLaw (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    Measure (RsgfOutputIndex N × RsgfSamplePrefix n Sample N) :=
  (rsgfOutputPMF S N hPR).toMeasure.prod (rsgfPrefixLaw S N)

/-- Selected-output expectation with respect to the paper's joint randomness
`R`, `ξ_[N]`, and `u_[N]`. -/
noncomputable def rsgfSelectedJointExpectation (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (φ : RsgfOutputIndex N → RsgfSamplePrefix n Sample N → ℝ) : ℝ :=
  ∫ q, φ q.1 q.2 ∂(rsgfSelectedRunLaw S N hPR)

/-- The `D_f` quantity from (6.1.13), specialized to the canonical objective. -/
def Df (S : Setup n Sample) : ℝ :=
  Real.sqrt (2 * (objective S S.x₁ - fStar S) / S.L)

/-- Well-definedness obligation for the square-root argument in `D_f`.  This is
not a theorem-head assumption; it follows from the source objective lower bound,
the definition of `f*`, and positivity of `L`. -/
theorem Df_radicand_nonneg (S : Setup n Sample) :
    0 ≤ 2 * (objective S S.x₁ - fStar S) / S.L := by
  have hbdd : BddBelow ((objective S) '' (Set.univ : Set (Space n))) := by
    simpa [Set.image_univ] using objective_bddBelow S
  have hstar : fStar S ≤ objective S S.x₁ := by
    simpa [fStar] using
      SOptLib.objectiveInfimumValue_le (X := (Set.univ : Set (Space n)))
        (f := objective S) hbdd (Set.mem_univ S.x₁)
  have hgap : 0 ≤ objective S S.x₁ - fStar S := sub_nonneg.mpr hstar
  exact div_nonneg (mul_nonneg (by norm_num) hgap) (le_of_lt S.L_pos)

/-- `D_f` squares to the source expression once its radicand is known
nonnegative. -/
theorem Df_sq_eq (S : Setup n Sample) :
    Df S ^ (2 : ℕ) = 2 * (objective S S.x₁ - fStar S) / S.L := by
  simpa [Df] using Real.sq_sqrt (Df_radicand_nonneg S)

/-- The `D_X` quantity from (6.1.15), used in the convex branch. -/
def DX (S : Setup n Sample) (xStar : Space n) : ℝ :=
  ‖S.x₁ - xStar‖

/-- Nonconvex numerator on the right side of Theorem 6.3(a). -/
def nonconvexRsgfBoundNumerator (S : Setup n Sample) (N : ℕ) : ℝ :=
  Df S ^ (2 : ℕ) +
    2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) *
      (1 + S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
        Finset.sum (Icc 1 N)
          (fun k => S.γ k / 4 + S.L * S.γ k ^ (2 : ℕ))) +
    2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) *
      Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ))

/-- Convex numerator on the right side of Theorem 6.3(b). -/
def convexRsgfBoundNumerator (S : Setup n Sample) (N : ℕ) (xStar : Space n) : ℝ :=
  DX S xStar ^ (2 : ℕ) +
    2 * S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) *
      Finset.sum (Icc 1 N)
        (fun k => S.γ k + S.L * ((n : ℝ) + 4) ^ (2 : ℕ) * S.γ k ^ (2 : ℕ)) +
    2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) *
      Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ))

/-- If the comparison point is globally optimal, the infimum value `f*` is
attained there. -/
private theorem fStar_eq_objective_of_global_optimal
    (S : Setup n Sample) (xStar : Space n)
    (hoptimal : ∀ x : Space n, objective S xStar ≤ objective S x) :
    fStar S = objective S xStar := by
  exact SOptLib.objectiveInfimumValue_eq_of_forall_le
    (X := (Set.univ : Set (Space n))) (f := objective S)
    (xStar := xStar) (Set.mem_univ xStar) (by
      intro x _hx
      exact hoptimal x)

/-- A globally optimal comparison point makes every objective gap to `f*`
nonnegative. -/
private theorem objective_gap_nonneg_of_global_optimal
    (S : Setup n Sample) (xStar x : Space n)
    (hoptimal : ∀ y : Space n, objective S xStar ≤ objective S y) :
    0 ≤ objective S x - fStar S := by
  exact SOptLib.sub_objectiveInfimumValue_nonneg_of_forall_le
    (X := (Set.univ : Set (Space n))) (f := objective S)
    (xStar := xStar) (x := x) (Set.mem_univ xStar) (Set.mem_univ x)
    (by intro y _hy; exact hoptimal y)

/-- Convex smoothed-gradient bridge used in Theorem 6.3(b): the smoothed
gradient inner product lower-bounds the original objective gap up to the
source smoothing error. -/
private theorem gaussianSmoothing_gradient_inner_ge_objective_gap_sub_error
    (S : Setup n Sample) (xStar x : Space n)
    (hconvex_smoothing : ConvexOn ℝ Set.univ (gaussianSmoothing S))
    (hoptimal : ∀ y : Space n, objective S xStar ≤ objective S y) :
    objective S x - fStar S - S.μ ^ (2 : ℕ) * S.L * (n : ℝ) ≤
      ⟪∇ (gaussianSmoothing S) x, x - xStar⟫_ℝ := by
  exact SOptLib.objective_gap_sub_error_le_inner_gradient_of_convex_approximation
    (f := objective S) (g := gaussianSmoothing S)
    (grad := fun y => ∇ (gaussianSmoothing S) y)
    (fStar := fStar S) (eps := S.μ ^ (2 : ℕ) * S.L * (n : ℝ))
    (xStar := xStar) (x := x) hconvex_smoothing
    (by
      have hbase := gaussianSmoothing_hasGradientAt_average S x
      rw [← gaussianSmoothing_gradient_eq_average S x] at hbase
      simpa [HasGradientAt] using hbase)
    (by simpa using gaussianSmoothing_abs_sub_objective_le S x)
    (by simpa using gaussianSmoothing_abs_sub_objective_le S xStar)
    (fStar_eq_objective_of_global_optimal S xStar hoptimal)

/-- A smooth objective with a global minimizer has objective gap controlled by
the squared distance to that minimizer.  This is the deterministic bridge used
to turn prefix L2 bounds into objective-gap integrability in the convex branch. -/
private theorem objective_gap_le_sq_distance_from_global_optimal
    (S : Setup n Sample) (xStar x : Space n)
    (hoptimal : ∀ y : Space n, objective S xStar ≤ objective S y) :
    objective S x - fStar S ≤ (S.L / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
  exact SOptLib.objective_gap_le_mul_sq_dist_of_global_minimizer
    (objective S) S.L (fStar S) xStar x (objective_CL11 S) hoptimal
    (fStar_eq_objective_of_global_optimal S xStar hoptimal)

/-- Objective-gap integrability follows from squared-distance integrability to a
global minimizer.  This is the measurability/domination half of the convex
prefix-budget induction. -/
private theorem objective_gap_integrable_of_sq_distance_integrable
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (S : Setup n Sample) (xStar : Space n) (X : Ω → Space n)
    (hoptimal : ∀ y : Space n, objective S xStar ≤ objective S y)
    (hX_aesm : AEStronglyMeasurable X ν)
    (hX_l2 : Integrable (fun ω : Ω => ‖X ω - xStar‖ ^ (2 : ℕ)) ν) :
    Integrable (fun ω : Ω => objective S (X ω) - fStar S) ν := by
  exact SOptLib.integrable_objective_gap_of_integrable_sq_dist_to_minimizer
    (objective S) S.L (fStar S) xStar X (objective_CL11 S) hoptimal
    (fStar_eq_objective_of_global_optimal S xStar hoptimal) hX_aesm hX_l2

/-- Nonconvex objective-gap integrability from squared-distance integrability
around an arbitrary deterministic base point.  Unlike the convex helper above,
this uses only the global lower bound defining `fStar` and the smooth upper
model at the base point, so it is available for Theorem 6.3(a). -/
private theorem objective_gap_integrable_of_sq_distance_integrable_from_base
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (S : Setup n Sample) (x0 : Space n) (X : Ω → Space n)
    (hX_aesm : AEStronglyMeasurable X ν)
    (hX_l2 : Integrable (fun ω : Ω => ‖X ω - x0‖ ^ (2 : ℕ)) ν) :
    Integrable (fun ω : Ω => objective S (X ω) - fStar S) ν := by
  let d : Ω → Space n := fun ω => X ω - x0
  let G : ℝ := ‖∇ (objective S) x0‖
  let C0 : ℝ := objective S x0 - fStar S
  have hd_aesm : AEStronglyMeasurable d ν :=
    hX_aesm.sub aestronglyMeasurable_const
  have hd_l1 : Integrable d ν :=
    integrable_of_integrable_norm_sq
      (μ := ν) hd_aesm (by simpa [d] using hX_l2)
  have hdist_l1 : Integrable (fun ω : Ω => ‖X ω - x0‖) ν := by
    simpa [d] using hd_l1.norm
  have hobj_cont : Continuous (objective S) :=
    (objective_CL11 S).1.continuous
  have hgap_aesm :
      AEStronglyMeasurable
        (fun ω : Ω => objective S (X ω) - fStar S) ν :=
    (hobj_cont.comp_aestronglyMeasurable hX_aesm).sub aestronglyMeasurable_const
  have hbound_int :
      Integrable
        (fun ω : Ω =>
          C0 + G * ‖X ω - x0‖ +
            (S.L / 2) * ‖X ω - x0‖ ^ (2 : ℕ)) ν := by
    have hconst : Integrable (fun _ω : Ω => C0) ν :=
      integrable_const _
    have hlinear : Integrable (fun ω : Ω => G * ‖X ω - x0‖) ν :=
      hdist_l1.const_mul G
    have hquad :
        Integrable
          (fun ω : Ω => (S.L / 2) * ‖X ω - x0‖ ^ (2 : ℕ)) ν :=
      hX_l2.const_mul (S.L / 2)
    simpa [add_assoc] using (hconst.add hlinear).add hquad
  refine Integrable.mono' hbound_int hgap_aesm ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hbdd : BddBelow ((objective S) '' (Set.univ : Set (Space n))) := by
    simpa [Set.image_univ] using objective_bddBelow S
  have hfstar_le : fStar S ≤ objective S (X ω) := by
    simpa [fStar] using
      SOptLib.objectiveInfimumValue_le (X := (Set.univ : Set (Space n)))
        (f := objective S) hbdd (Set.mem_univ (X ω))
  have hgap_nonneg : 0 ≤ objective S (X ω) - fStar S :=
    sub_nonneg.mpr hfstar_le
  have hdes := objective_smoothDescentBound S x0 (X ω)
  have hmodel :
      objective S (X ω) ≤
        objective S x0 + ⟪∇ (objective S) x0, X ω - x0⟫_ℝ +
          (S.L / 2) * ‖X ω - x0‖ ^ (2 : ℕ) := by
    have h :=
      (le_abs_self
        (objective S (X ω) - objective S x0 -
          ⟪∇ (objective S) x0, X ω - x0⟫_ℝ)).trans hdes
    linarith
  have hinner_le :
      ⟪∇ (objective S) x0, X ω - x0⟫_ℝ ≤
        G * ‖X ω - x0‖ := by
    simpa [G] using real_inner_le_norm (∇ (objective S) x0) (X ω - x0)
  have hgap_le :
      objective S (X ω) - fStar S ≤
        C0 + G * ‖X ω - x0‖ +
          (S.L / 2) * ‖X ω - x0‖ ^ (2 : ℕ) := by
    dsimp [C0]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg hgap_nonneg]
  exact hgap_le

/-- Centered L2 integrability is preserved by an affine stochastic-gradient
update when both the previous centered state and the update direction are L2. -/
private theorem integrable_sq_norm_affine_update_of_l2
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (x g : Ω → Space n) (xStar : Space n) (γ : ℝ)
    (hx_aesm : AEStronglyMeasurable x ν)
    (hg_aesm : AEStronglyMeasurable g ν)
    (hx_l2 : Integrable (fun ω : Ω => ‖x ω - xStar‖ ^ (2 : ℕ)) ν)
    (hg_l2 : Integrable (fun ω : Ω => ‖g ω‖ ^ (2 : ℕ)) ν) :
    Integrable
      (fun ω : Ω => ‖(x ω - γ • g ω) - xStar‖ ^ (2 : ℕ)) ν := by
  exact integrable_sq_norm_sub_smul_sub_const_of_l2
    x g xStar γ hx_aesm hg_aesm hx_l2 hg_l2

/-- Random-query squared-integrability of the RSGF oracle from a pointwise
second-moment budget.  This is the product-law step used in the convex prefix
budget induction once the current query has an objective-gap budget. -/
private theorem rsgfOracle_random_query_norm_sq_integrable_of_gap_integrable
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (S : Setup n Sample) (X : Ω → Space n)
    (hX : AEStronglyMeasurable X ν)
    (hgap_int :
      Integrable (fun ω : Ω => objective S (X ω) - fStar S) ν)
    (horacle_gap_bound :
      ∀ ω : Ω,
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (X ω) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L * (objective S (X ω) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    Integrable
      (fun p : Ω × RsgfZeta n Sample =>
        ‖rsgfOracle S (X p.1) p.2.1 p.2.2‖ ^ (2 : ℕ))
      (ν.prod (rsgfZetaLaw S)) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  let B : Ω → ℝ := fun ω =>
    4 * ((n : ℝ) + 4) * S.L * (objective S (X ω) - fStar S) +
      2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ)
  haveI : SFinite (rsgfZetaLaw S) := inferInstance
  have hφ_aesm :
      AEStronglyMeasurable
        (fun p : Ω × RsgfZeta n Sample =>
          ‖rsgfOracle S (X p.1) p.2.1 p.2.2‖ ^ (2 : ℕ))
        (ν.prod (rsgfZetaLaw S)) := by
    have hraw :
        AEStronglyMeasurable
          (fun p : Ω × (Sample × Space n) =>
            rsgfOracle S (X p.1) p.2.1 p.2.2)
          (ν.prod (S.P.prod (gaussianDirectionLaw n))) :=
      rsgfOracle_random_query_aestronglyMeasurable_of_aesm S X hX
    simpa [rsgfZetaLaw] using
      ((hraw.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  have hB_int : Integrable B ν := by
    have hgap_scaled :
        Integrable
          (fun ω : Ω =>
            (4 * ((n : ℝ) + 4) * S.L) *
              (objective S (X ω) - fStar S)) ν :=
      hgap_int.const_mul (4 * ((n : ℝ) + 4) * S.L)
    have hconst1 :
        Integrable
          (fun _ω : Ω => 2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) ν :=
      integrable_const _
    have hconst2 :
        Integrable
          (fun _ω : Ω =>
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) ν :=
      integrable_const _
    simpa [B, mul_assoc] using (hgap_scaled.add hconst1).add hconst2
  refine
    integrable_prod_of_nonneg_fiber_integral_le_integrable_bound
      (μ := ν) (ν := rsgfZetaLaw S)
      (φ := fun ω z => ‖rsgfOracle S (X ω) z.1 z.2‖ ^ (2 : ℕ))
      (B := B) hφ_aesm ?_ ?_ hB_int ?_
  · intro ω z
    positivity
  · intro ω
    simpa [rsgfZetaLaw] using
      (rsgfOracle_norm_sq_integrable_and_secondMoment_le_sampleGradient
        S (X ω)).1
  · intro ω
    simpa [B, rsgfZetaLaw] using horacle_gap_bound ω

/-- Prefix-law sampled oracle square integrability from the objective-gap
budget at the same prefix index.  The proof first samples an independent fresh
coordinate by the product-law moment theorem, then replaces the current prefix
coordinate by that fresh draw; the iid prefix law is invariant under this
replacement. -/
private theorem rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N))
    (hsample_oracle :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N))
    (hgap_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N))
    (horacle_gap_bound :
      ∀ ζ : RsgfSamplePrefix n Sample N,
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ))
      (rsgfPrefixLaw S N) := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^ (2 : ℕ)
  let Ψ : RsgfSamplePrefix n Sample N × RsgfZeta n Sample → ℝ := fun q =>
    ‖rsgfOracle S (rsgfPrefixIterate S q.1 R) q.2.1 q.2.2‖ ^ (2 : ℕ)
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  have hprod_int :
      Integrable Ψ ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
    simpa [Ψ, R] using
      rsgfOracle_random_query_norm_sq_integrable_of_gap_integrable
        (ν := rsgfPrefixLaw S N) S
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (by simpa [R] using hX)
        (by simpa [R] using hgap_int)
        (by simpa [R] using horacle_gap_bound)
  let replace : RsgfSamplePrefix n Sample N × RsgfZeta n Sample →
      RsgfSamplePrefix n Sample N := fun q => Function.update q.1 R q.2
  have hreplace :
      MeasurePreserving replace
        ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))
        (rsgfPrefixLaw S N) := by
    simpa [replace, R] using
      rsgfPrefixLaw_replace_coordinate_measurePreserving S R
  have hcomp_int :
      Integrable (fun q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample =>
        Φ (replace q)) ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
    refine hprod_int.congr (Filter.Eventually.of_forall ?_)
    intro q
    have hx :
        rsgfPrefixIterate S (replace q) R =
          rsgfPrefixIterate S q.1 R := by
      simpa [replace, R] using
        rsgf_prefix_iterate_current_coordinate_independent S q.1 hk q.2
    simp [Φ, Ψ, replace, R, hx]
  have hΦ_aesm :
      AEStronglyMeasurable Φ
        (Measure.map replace ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))) := by
    rw [hreplace.map_eq]
    simpa [Φ, R] using
      ((hsample_oracle.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  have hmap_int :
      Integrable Φ
        (Measure.map replace ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))) :=
    (MeasureTheory.integrable_map_measure hΦ_aesm hreplace.aemeasurable).mpr hcomp_int
  simpa [Φ, R, hreplace.map_eq] using hmap_int

/-- Prefix-law sampled oracle square expectation bound from the fixed-query
second-moment bound.  This is the expectation-level version of
`rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable`: replace the current
coordinate by an independent fresh draw, apply the fixed-prefix oracle budget,
then integrate the resulting objective-gap majorant. -/
private theorem rsgf_prefix_oracle_sq_integral_le_gap_integral
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N))
    (hsample_oracle :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N))
    (hgap_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N))
    (horacle_gap_bound :
      ∀ ζ : RsgfSamplePrefix n Sample N,
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N)) ≤
      4 * ((n : ℝ) + 4) * S.L *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
            ∂(rsgfPrefixLaw S N)) +
        (2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 6) ^ (3 : ℕ)) := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  let C : ℝ :=
    2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ)
  let B : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    4 * ((n : ℝ) + 4) * S.L *
        (objective S (rsgfPrefixIterate S ζ R) - fStar S) + C
  have hprod_int :
      Integrable
        (fun q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample =>
          ‖rsgfOracle S (rsgfPrefixIterate S q.1 R) q.2.1 q.2.2‖ ^ (2 : ℕ))
        ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
    simpa [R] using
      rsgfOracle_random_query_norm_sq_integrable_of_gap_integrable
        (ν := rsgfPrefixLaw S N) S
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (by simpa [R] using hX)
        (by simpa [R] using hgap_int)
        (by simpa [R] using horacle_gap_bound)
  have hB_int : Integrable B (rsgfPrefixLaw S N) := by
    have hgap_R :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ R) - fStar S)
          (rsgfPrefixLaw S N) := by
      simpa [R] using hgap_int
    have hscaled :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            (4 * ((n : ℝ) + 4) * S.L) *
              (objective S (rsgfPrefixIterate S ζ R) - fStar S))
          (rsgfPrefixLaw S N) :=
      hgap_R.const_mul (4 * ((n : ℝ) + 4) * S.L)
    have hconst :
        Integrable (fun _ζ : RsgfSamplePrefix n Sample N => C)
          (rsgfPrefixLaw S N) :=
      integrable_const _
    simpa [B, C, mul_assoc] using hscaled.add hconst
  have hB_eval :
      (∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N)) =
        4 * ((n : ℝ) + 4) * S.L *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ R) - fStar S
              ∂(rsgfPrefixLaw S N)) + C := by
    let c : ℝ := 4 * ((n : ℝ) + 4) * S.L
    have hgap_R :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ R) - fStar S)
          (rsgfPrefixLaw S N) := by
      simpa [R] using hgap_int
    have hscaled :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            c * (objective S (rsgfPrefixIterate S ζ R) - fStar S))
          (rsgfPrefixLaw S N) :=
      hgap_R.const_mul c
    have hconst :
        Integrable (fun _ζ : RsgfSamplePrefix n Sample N => C)
          (rsgfPrefixLaw S N) :=
      integrable_const _
    calc
      (∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N))
          =
        (∫ ζ : RsgfSamplePrefix n Sample N,
          c * (objective S (rsgfPrefixIterate S ζ R) - fStar S) + C
          ∂(rsgfPrefixLaw S N)) := by
            simp [B, C, c, R, mul_assoc]
      _ =
        (∫ ζ : RsgfSamplePrefix n Sample N,
          c * (objective S (rsgfPrefixIterate S ζ R) - fStar S)
          ∂(rsgfPrefixLaw S N)) +
          ∫ _ζ : RsgfSamplePrefix n Sample N, C ∂(rsgfPrefixLaw S N) := by
            exact integral_add hscaled hconst
      _ =
        c *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ R) - fStar S
              ∂(rsgfPrefixLaw S N)) + C := by
            simp [integral_const_mul, c]
      _ =
        4 * ((n : ℝ) + 4) * S.L *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ R) - fStar S
              ∂(rsgfPrefixLaw S N)) + C := by
            simp [c]
  have hmain :
      (∫ ζ : RsgfSamplePrefix n Sample N,
          ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N)) ≤
        ∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N) := by
    simpa [R, rsgfPrefixLaw, rsgfZetaLaw] using
      (integral_sampled_coordinate_kernel_le_of_fresh_fiber_bound
        (ν := rsgfZetaLaw S) (R := R)
        (X := fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (K := fun x z => ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ)) (B := B)
        (by
          simpa [R, rsgfPrefixLaw] using
            ((hsample_oracle.norm.aemeasurable.pow_const 2).aestronglyMeasurable))
        (by simpa [R, rsgfPrefixLaw] using hprod_int)
        (by simpa [B, rsgfPrefixLaw] using hB_int)
        (fun ζ z => by
          simpa [R] using
            rsgf_prefix_iterate_current_coordinate_independent S ζ hk z)
        (fun ζ => by
          simpa [B, C, R, rsgfZetaLaw, add_assoc] using horacle_gap_bound ζ))
  calc
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N))
        ≤ ∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N) := by
            simpa [R] using hmain
    _ =
      4 * ((n : ℝ) + 4) * S.L *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
            ∂(rsgfPrefixLaw S N)) +
        (2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 6) ^ (3 : ℕ)) := by
          simpa [B, C, R] using hB_eval

/-- Prefix-law sampled oracle square expectation bound in the nonconvex source
form (6.1.67).  The objective-gap oracle bound is retained only to supply
sampled-oracle square integrability; the numerical bound itself is the
gradient-sigma estimate. -/
private theorem rsgf_prefix_oracle_sq_integral_le_gradient_sigma_integral
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N))
    (hsample_oracle :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N))
    (hgap_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N))
    (hgrad_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N))
    (horacle_gap_bound :
      ∀ ζ : RsgfSamplePrefix n Sample N,
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N)) ≤
      2 * ((n : ℝ) + 4) *
          ((∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 6) ^ (3 : ℕ) := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^ (2 : ℕ)
  let Ψ : RsgfSamplePrefix n Sample N × RsgfZeta n Sample → ℝ := fun q =>
    ‖rsgfOracle S (rsgfPrefixIterate S q.1 R) q.2.1 q.2.2‖ ^ (2 : ℕ)
  let C : ℝ :=
    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ)
  let c : ℝ := 2 * ((n : ℝ) + 4)
  let B : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    c *
        (‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
          S.σ ^ (2 : ℕ)) + C
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : SFinite (rsgfZetaLaw S) := inferInstance
  have hprod_int :
      Integrable Ψ ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
    simpa [Ψ, R] using
      rsgfOracle_random_query_norm_sq_integrable_of_gap_integrable
        (ν := rsgfPrefixLaw S N) S
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (by simpa [R] using hX)
        (by simpa [R] using hgap_int)
        (by simpa [R] using horacle_gap_bound)
  have hB_int : Integrable B (rsgfPrefixLaw S N) := by
    have hgrad_R :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) := by
      simpa [R] using hgrad_int
    have hgrad_sigma :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
              S.σ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) :=
      hgrad_R.add (integrable_const _)
    exact (hgrad_sigma.const_mul c).add (integrable_const C)
  let replace : RsgfSamplePrefix n Sample N × RsgfZeta n Sample →
      RsgfSamplePrefix n Sample N := fun q => Function.update q.1 R q.2
  have hreplace :
      MeasurePreserving replace
        ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))
        (rsgfPrefixLaw S N) := by
    simpa [replace, R] using
      rsgfPrefixLaw_replace_coordinate_measurePreserving S R
  have hΦ_aesm :
      AEStronglyMeasurable Φ
        (Measure.map replace ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))) := by
    rw [hreplace.map_eq]
    simpa [Φ, R] using
      ((hsample_oracle.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  have hmap :
      (∫ ζ : RsgfSamplePrefix n Sample N, Φ ζ ∂(rsgfPrefixLaw S N)) =
        ∫ q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample,
          Φ (replace q) ∂((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
    calc
      (∫ ζ : RsgfSamplePrefix n Sample N, Φ ζ ∂(rsgfPrefixLaw S N))
          =
        ∫ ζ : RsgfSamplePrefix n Sample N, Φ ζ
          ∂Measure.map replace ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
            rw [hreplace.map_eq]
      _ =
        ∫ q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample,
          Φ (replace q) ∂((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
            exact
              MeasureTheory.integral_map hreplace.aemeasurable hΦ_aesm
  have hreplace_point :
      (fun q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample =>
        Φ (replace q)) =ᵐ[((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))] Ψ := by
    exact Filter.Eventually.of_forall fun q => by
      have hx :
          rsgfPrefixIterate S (replace q) R =
            rsgfPrefixIterate S q.1 R := by
        simpa [replace, R] using
          rsgf_prefix_iterate_current_coordinate_independent S q.1 hk q.2
      simp [Φ, Ψ, replace, R, hx]
  have hprod :
      (∫ q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample,
          Ψ q ∂((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))) =
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ∫ z : RsgfZeta n Sample, Ψ (ζ, z) ∂(rsgfZetaLaw S)
          ∂(rsgfPrefixLaw S N) := by
    exact MeasureTheory.integral_prod Ψ hprod_int
  have hinner_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ∫ z : RsgfZeta n Sample, Ψ (ζ, z) ∂(rsgfZetaLaw S))
        (rsgfPrefixLaw S N) :=
    hprod_int.integral_prod_left
  have hinner_le :
      (∫ ζ : RsgfSamplePrefix n Sample N,
          ∫ z : RsgfZeta n Sample, Ψ (ζ, z) ∂(rsgfZetaLaw S)
          ∂(rsgfPrefixLaw S N)) ≤
        ∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N) := by
    refine integral_mono_ae hinner_int hB_int ?_
    exact Filter.Eventually.of_forall fun ζ => by
      simpa [Ψ, B, C, c, R, rsgfZetaLaw, add_assoc] using
        rsgfOracle_secondMoment_le_gradient_sigma S
          (rsgfPrefixIterate S ζ R)
  have hB_eval :
      (∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N)) =
        c *
            ((∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) + C := by
    have hgrad_R :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) := by
      simpa [R] using hgrad_int
    have hconst_sigma :
        Integrable
          (fun _ζ : RsgfSamplePrefix n Sample N => S.σ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) :=
      integrable_const _
    have hsum :
        (∫ ζ : RsgfSamplePrefix n Sample N,
          ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
            S.σ ^ (2 : ℕ) ∂(rsgfPrefixLaw S N)) =
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ) := by
      rw [integral_add hgrad_R hconst_sigma]
      simp
    have hgrad_sigma_int :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
              S.σ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) :=
      hgrad_R.add hconst_sigma
    have hscaled :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            c *
              (‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
                S.σ ^ (2 : ℕ)))
          (rsgfPrefixLaw S N) :=
      hgrad_sigma_int.const_mul c
    have hconst_C :
        Integrable (fun _ζ : RsgfSamplePrefix n Sample N => C)
          (rsgfPrefixLaw S N) :=
      integrable_const _
    calc
      (∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N))
          =
        (∫ ζ : RsgfSamplePrefix n Sample N,
          c *
              (‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
                S.σ ^ (2 : ℕ)) + C ∂(rsgfPrefixLaw S N)) := by
            simp [B]
      _ =
        (∫ ζ : RsgfSamplePrefix n Sample N,
          c *
              (‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
                S.σ ^ (2 : ℕ)) ∂(rsgfPrefixLaw S N)) +
          ∫ _ζ : RsgfSamplePrefix n Sample N, C ∂(rsgfPrefixLaw S N) := by
            exact integral_add hscaled hconst_C
      _ =
        c *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) +
                S.σ ^ (2 : ℕ) ∂(rsgfPrefixLaw S N)) + C := by
            simp [integral_const_mul]
      _ =
        c *
            ((∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) + C := by
            rw [hsum]
  calc
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N))
        = ∫ ζ : RsgfSamplePrefix n Sample N, Φ ζ ∂(rsgfPrefixLaw S N) := by
            simp [Φ, R]
    _ = ∫ q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample,
          Φ (replace q) ∂((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := hmap
    _ = ∫ q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample,
          Ψ q ∂((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
            exact integral_congr_ae hreplace_point
    _ = ∫ ζ : RsgfSamplePrefix n Sample N,
          ∫ z : RsgfZeta n Sample, Ψ (ζ, z) ∂(rsgfZetaLaw S)
          ∂(rsgfPrefixLaw S N) := hprod
    _ ≤ ∫ ζ : RsgfSamplePrefix n Sample N, B ζ ∂(rsgfPrefixLaw S N) := hinner_le
    _ =
      2 * ((n : ℝ) + 4) *
          ((∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 6) ^ (3 : ℕ) := by
          simpa [B, C, c, R] using hB_eval

/-- Scalar finite-window aggregation of gamma-square oracle bounds.  Once each
sampled oracle-square expectation has been converted to an objective-gap and
constant budget, the same conversion holds after summing with `γ_k^2`. -/
private theorem sum_gamma_sq_oracle_le_gap_noise_of_pointwise
    (γ oracle gap : ℕ → ℝ) (N : ℕ) (coeff C : ℝ)
    (hpoint : ∀ k, k ∈ Icc 1 N → oracle k ≤ coeff * gap k + C) :
    Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * oracle k) ≤
      Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * (coeff * gap k + C)) := by
  refine Finset.sum_le_sum ?_
  intro k hk
  exact mul_le_mul_of_nonneg_left (hpoint k hk) (sq_nonneg (γ k))

/-- Scalar terminal-budget processor for the convex RSGF numerator.  A lower
bound on gradient-inner terms by objective gaps, together with an oracle-square
budget in the same gaps, isolates the retained finite-window weight
`γ_k - b γ_k^2`. -/
private theorem weighted_gap_sum_le_of_terminal_grad_oracle_budget
    (γ gap grad oracle : ℕ → ℝ) (N : ℕ) (dist b e C : ℝ)
    (hγ_nonneg : ∀ k, k ∈ Icc 1 N → 0 ≤ γ k)
    (hgrad : ∀ k, k ∈ Icc 1 N → gap k - e ≤ grad k)
    (hterminal :
      2 * Finset.sum (Icc 1 N) (fun k => γ k * grad k) ≤
        dist + Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * oracle k))
    (horacle :
      Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * oracle k) ≤
        Finset.sum (Icc 1 N)
          (fun k => γ k ^ (2 : ℕ) * (2 * b * gap k + C))) :
    2 * Finset.sum (Icc 1 N)
        (fun k => (γ k - b * γ k ^ (2 : ℕ)) * gap k) ≤
      dist + 2 * e * Finset.sum (Icc 1 N) γ +
        C * Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ)) := by
  exact weighted_gap_sum_le_of_terminal_inner_and_oracle_budget
    (Icc 1 N) γ gap grad oracle dist b e C hγ_nonneg hgrad hterminal horacle

/-- On the RSGF output window, admissibility of the printed output weights plus
the source upper bound on `γ_k` forces the underlying stepsize to be
nonnegative. -/
private theorem rsgf_stepsize_nonneg_of_weight_nonneg_of_upper
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hweight : 0 ≤ rsgfWeightNumerator S k)
    (hγ_upper : S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹) :
    0 ≤ S.γ k := by
  let c : ℝ := 2 * ((n : ℝ) + 4) * S.L
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hn4_pos : 0 < (n : ℝ) + 4 := by nlinarith
  have hc_pos : 0 < c := by
    dsimp [c]
    exact mul_pos (mul_pos (by norm_num) hn4_pos) S.L_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hmul_lt : c * S.γ k < 1 := by
    calc
      c * S.γ k < c * c⁻¹ := mul_lt_mul_of_pos_left hγ_upper hc_pos
      _ = 1 := by
        field_simp [hc_ne]
  have hfactor_pos : 0 < 1 - c * S.γ k := sub_pos.mpr hmul_lt
  have hrewrite : rsgfWeightNumerator S k = S.γ k * (1 - c * S.γ k) := by
    dsimp [rsgfWeightNumerator, c]
    ring
  have hprod_nonneg : 0 ≤ S.γ k * (1 - c * S.γ k) := by
    simpa [hrewrite] using hweight
  by_contra hnot
  have hγ_neg : S.γ k < 0 := lt_of_not_ge hnot
  have hprod_neg : S.γ k * (1 - c * S.γ k) < 0 :=
    mul_neg_of_neg_of_pos hγ_neg hfactor_pos
  linarith

/-- Prefix-specialized L2 propagation for the actual RSGF update.  Once the
current iterate and sampled oracle direction are a.e.-strongly measurable and
square-integrable, the next centered prefix iterate is square-integrable. -/
private theorem rsgf_prefix_step_l2_of_oracle_l2
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N) (hks : k + 1 ∈ Icc 1 N)
    (xStar : Space n)
    (hx_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N))
    (hg_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N))
    (hx_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N))
    (hg_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ‖rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ - xStar‖ ^ (2 : ℕ))
      (rsgfPrefixLaw S N) := by
  classical
  let x : RsgfSamplePrefix n Sample N → Space n := fun ζ =>
    rsgfPrefixIterate S ζ ⟨k, hk⟩
  let g : RsgfSamplePrefix n Sample N → Space n := fun ζ =>
    rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2
  have hupdate_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖(x ζ - S.γ k • g ζ) - xStar‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) :=
    integrable_sq_norm_affine_update_of_l2
      (n := n) x g xStar (S.γ k)
      (by simpa [x] using hx_aesm)
      (by simpa [g] using hg_aesm)
      (by simpa [x] using hx_l2)
      (by simpa [g] using hg_l2)
  refine hupdate_l2.congr (Filter.Eventually.of_forall ?_)
  intro ζ
  have hnext :
      rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ =
        rsgfPrefixIterate S ζ ⟨k, hk⟩ -
          S.γ k •
            rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2 := by
    cases k with
    | zero =>
        have hk_pos : 1 ≤ 0 := (mem_Icc.mp hk).1
        omega
    | succ j =>
        simp [rsgfPrefixIterate, rsgfPrefixIterate0, rsgfStep_def]
  simpa [x, g, hnext]

/-- Pathwise squared-distance identity for one actual prefix RSGF update.  This
is the executable form of source step 14 before taking expectations and
telescoping. -/
private theorem rsgf_prefix_step_sq_distance_identity
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N) (hks : k + 1 ∈ Icc 1 N)
    (xStar : Space n) (ζ : RsgfSamplePrefix n Sample N) :
    ‖rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ - xStar‖ ^ (2 : ℕ) =
      ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
        2 * S.γ k *
          ⟪rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
  classical
  let x : Space n := rsgfPrefixIterate S ζ ⟨k, hk⟩
  let g : Space n :=
    rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2
  have hnext :
      rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ =
        rsgfPrefixIterate S ζ ⟨k, hk⟩ -
          S.γ k •
            rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2 := by
    cases k with
    | zero =>
        have hk_pos : 1 ≤ 0 := (mem_Icc.mp hk).1
        omega
    | succ j =>
        simp [rsgfPrefixIterate, rsgfPrefixIterate0, rsgfStep_def]
  calc
    ‖rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ - xStar‖ ^ (2 : ℕ)
        = ‖(x - S.γ k • g) - xStar‖ ^ (2 : ℕ) := by
            simp [x, g, hnext]
    _ = ‖(x - xStar) - S.γ k • g‖ ^ (2 : ℕ) := by
            congr 1
            abel
    _ =
        ‖x - xStar‖ ^ (2 : ℕ) -
          2 * S.γ k * ⟪g, x - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) := by
          rw [norm_sub_sq_real, inner_smul_right, norm_smul,
            mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm (x - xStar) g]
          ring
    _ =
      ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
        2 * S.γ k *
          ⟪rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
        simp [x, g]

/-- Pathwise one-step squared-distance identity with the oracle inner product
split into the smoothed-gradient term and the centered residual.  This is the
local bridge from source step 14 to the residual-cancellation step 16. -/
private theorem rsgf_prefix_step_sq_distance_identity_residual
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N) (hks : k + 1 ∈ Icc 1 N)
    (xStar : Space n) (ζ : RsgfSamplePrefix n Sample N) :
    ‖rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ - xStar‖ ^ (2 : ℕ) =
      ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
        2 * S.γ k *
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
        2 * S.γ k *
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
  have hbase :=
    rsgf_prefix_step_sq_distance_identity S hk hks xStar ζ
  calc
    ‖rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ - xStar‖ ^ (2 : ℕ)
        =
      ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
        2 * S.γ k *
          ⟪rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := hbase
    _ =
      ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
        2 * S.γ k *
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
        2 * S.γ k *
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
        simp [SOptLib.oracleEstimatorError, inner_sub_left]
        ring

/-- Pathwise one-step squared-distance residual identity whose next iterate is
the terminal `rsgfPrefixIterate0` value.  This variant covers the final update
`k = N`, where `x_{N+1}` is available from the length-`N` prefix recursion but
is not an `RsgfOutputIndex N`. -/
private theorem rsgf_prefix_step_sq_distance_identity_residual_terminal
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N) (xStar : Space n)
    (ζ : RsgfSamplePrefix n Sample N) :
    ‖rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 - xStar‖ ^ (2 : ℕ) =
      ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
        2 * S.γ k *
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
        2 * S.γ k *
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
  classical
  let x : Space n := rsgfPrefixIterate S ζ ⟨k, hk⟩
  let g : Space n :=
    rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2
  have hnext :
      rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 =
        rsgfPrefixIterate S ζ ⟨k, hk⟩ -
          S.γ k •
            rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2 := by
    cases k with
    | zero =>
        have hk_pos : 1 ≤ 0 := (mem_Icc.mp hk).1
        omega
    | succ j =>
        simp [rsgfPrefixIterate, rsgfPrefixIterate0, rsgfStep_def]
  calc
    ‖rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 - xStar‖ ^ (2 : ℕ)
        = ‖(x - S.γ k • g) - xStar‖ ^ (2 : ℕ) := by
            simp [x, g, hnext]
    _ = ‖(x - xStar) - S.γ k • g‖ ^ (2 : ℕ) := by
            congr 1
            abel
    _ =
        ‖x - xStar‖ ^ (2 : ℕ) -
          2 * S.γ k * ⟪g, x - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) * ‖g‖ ^ (2 : ℕ) := by
          rw [norm_sub_sq_real, inner_smul_right, norm_smul,
            mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm (x - xStar) g]
          ring
    _ =
      ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
        2 * S.γ k *
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
        2 * S.γ k *
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
        S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
        simp [x, g, SOptLib.oracleEstimatorError, inner_sub_left]
        ring

/-- If the current prefix iterate is a.e.-strongly measurable, then the sampled
oracle direction at the same prefix coordinate is also a.e.-strongly measurable.
The proof splits the finite product law into the selected coordinate and the
remaining prefix, uses adaptedness to remove the selected coordinate from the
query, and then applies the random-query oracle measurability theorem. -/
private theorem rsgf_prefix_sampled_oracle_aestronglyMeasurable_of_iterate
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N)) :
    AEStronglyMeasurable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
      (rsgfPrefixLaw S N) := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  simpa [R, rsgfPrefixLaw] using
    (aestronglyMeasurable_sampled_coordinate_kernel_of_adapted_query
      (ν := rsgfZetaLaw S) (R := R)
      (query := fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
      (kernel := fun x z => rsgfOracle S x z.1 z.2)
      (hquery := by
        simpa [R, rsgfPrefixLaw] using hX)
      (hkernel := by
        intro Y hY
        simpa using
          rsgfOracle_random_query_aestronglyMeasurable_of_aesm
            (ν := Measure.pi
              (fun _ : {Q : RsgfOutputIndex N // Q ≠ R} => rsgfZetaLaw S))
            S Y hY)
      (hquery_update := by
        intro ζ z
        simpa [R] using
          rsgf_prefix_iterate_current_coordinate_independent S ζ hk z))

/-- Closed prefix-law adaptedness for the RSGF recursion: every prefix iterate
and the sampled oracle direction at that iterate are a.e.-strongly measurable
under the finite prefix law. -/
private theorem rsgfPrefixIterate_and_oracle_aestronglyMeasurable
    (S : Setup n Sample) {N : ℕ} :
    ∀ R : RsgfOutputIndex N,
      AEStronglyMeasurable
          (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
          (rsgfPrefixLaw S N) ∧
        AEStronglyMeasurable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
          (rsgfPrefixLaw S N) := by
  classical
  intro R
  have hrec :=
    recursive_prefix_iterate_and_sampled_direction_aestronglyMeasurable
      (μ := rsgfPrefixLaw S N) (N := N) (x0 := S.x₁)
      (sample := fun k ζ =>
        ζ ⟨k.1 + 1, mem_Icc.mpr ⟨Nat.succ_pos k.1, k.2⟩⟩)
      (kernel := fun x z => rsgfOracle S x z.1 z.2)
      (step := fun k x d => x - S.γ (k.1 + 1) • d)
      (process := fun k ζ =>
        rsgfPrefixIterate0 S ζ k.1 (Nat.le_of_lt_succ k.2))
      (h_zero := rfl)
      (h_kernel := by
        intro k hX
        let hk_mem : k.1 + 1 ∈ Icc 1 N :=
          mem_Icc.mpr ⟨Nat.succ_pos k.1, k.2⟩
        have hX' :
            AEStronglyMeasurable
              (fun ζ : RsgfSamplePrefix n Sample N =>
                rsgfPrefixIterate S ζ ⟨k.1 + 1, hk_mem⟩)
              (rsgfPrefixLaw S N) := by
          simpa [rsgfPrefixIterate] using hX
        simpa [hk_mem, rsgfPrefixIterate] using
          (rsgf_prefix_sampled_oracle_aestronglyMeasurable_of_iterate
            S hk_mem hX'))
      (h_step := by
        intro k X D hX hD
        exact hX.sub (hD.const_smul (S.γ (k.1 + 1))))
      (h_succ := by
        intro k
        funext ζ
        simp [rsgfPrefixIterate0, rsgfStep_def])
  have hRpred : R.1 - 1 < N := by
    have hR := mem_Icc.mp R.2
    omega
  have hcoord :
      (⟨R.1 - 1 + 1,
          mem_Icc.mpr ⟨Nat.succ_pos (R.1 - 1), hRpred⟩⟩ :
        RsgfOutputIndex N) = R := by
    ext
    exact Nat.sub_add_cancel (mem_Icc.mp R.2).1
  simpa [rsgfPrefixIterate, hcoord] using hrec ⟨R.1 - 1, hRpred⟩

/-- Standard smooth lower-bound consequence: for the canonical `L`-smooth
objective, the squared gradient is controlled by twice the smoothness constant
times the objective gap to the infimum. -/
private theorem objective_gradient_norm_sq_le_two_mul_L_gap
    (S : Setup n Sample) (x : Space n) :
    ‖∇ (objective S) x‖ ^ (2 : ℕ) ≤
      2 * S.L * (objective S x - fStar S) := by
  exact SOptLib.norm_sq_gradient_le_two_mul_smoothness_mul_sub_inf
    (objective S) S.L (fStar S) x S.L_pos
    (objective_smoothDescentBound S) (fun y => by
      have hbdd : BddBelow ((objective S) '' (Set.univ : Set (Space n))) := by
        simpa [Set.image_univ] using objective_bddBelow S
      simpa [fStar] using
        SOptLib.objectiveInfimumValue_le
          (X := (Set.univ : Set (Space n))) (f := objective S) hbdd
          (Set.mem_univ y))

/-- Fixed-query oracle second-moment estimate after converting the true-gradient
square to the objective gap.  This is the deterministic positive-term conversion
used inside the convex distance recursion. -/
private theorem rsgfOracle_secondMoment_le_objective_gap_sigma
    (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        ‖rsgfOracle S x z.1 z.2‖ ^ (2 : ℕ) ∂(S.P.prod (gaussianDirectionLaw n))) ≤
      4 * ((n : ℝ) + 4) * S.L * (objective S x - fStar S) +
        2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) := by
  exact forwardDifferenceOracle_secondMoment_le_objective_gap_sigma
    S.P (gaussianDirectionLaw n) (rsgfOracle S) (objective S) n (fStar S)
    S.L S.μ S.σ x (rsgfOracle_secondMoment_le_gradient_sigma S x)
    (objective_gradient_norm_sq_le_two_mul_L_gap S x)

/-- Fixed-query residual second-moment estimate obtained by centering the oracle
second-moment bound.  This is the residual-budget analogue of the first
inequality in (6.1.67). -/
private theorem rsgfResidual_secondMoment_le_objective_gap_sigma
    (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) x z.1 z.2‖ ^ (2 : ℕ)
          ∂(S.P.prod (gaussianDirectionLaw n))) ≤
      4 * ((n : ℝ) + 4) * S.L * (objective S x - fStar S) +
        2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) := by
  exact
    (rsgfResidual_secondMoment_le_oracle_secondMoment S x).trans
      (rsgfOracle_secondMoment_le_objective_gap_sigma S x)

/-- The smoothed-gradient random query is a.e.-strongly measurable whenever the
query is.  The proof exposes the smoothed gradient as the product-law mean of
the already measurable RSGF oracle via the unbiasedness identity. -/
private theorem rsgf_smoothing_gradient_random_query_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (S : Setup n Sample) (X : Ω → Space n)
    (hX : AEStronglyMeasurable X ν) :
    AEStronglyMeasurable
      (fun ω : Ω => ∇ (gaussianSmoothing S) (X ω)) ν := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  exact aestronglyMeasurable_target_of_integral_oracle_eq
    (muS := S.P.prod (gaussianDirectionLaw n)) X
    (fun x z => rsgfOracle S x z.1 z.2)
    (fun x => ∇ (gaussianSmoothing S) x)
    (rsgfOracle_random_query_aestronglyMeasurable_of_aesm S X hX)
    (fun ω => rsgfOracle_unbiased_smoothed S (X ω))

/-- Random-query residual measurability obtained by combining sampled-oracle
measurability with the smoothed-gradient mean measurability. -/
private theorem rsgfResidual_random_query_aestronglyMeasurable_of_aesm
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (S : Setup n Sample) (X : Ω → Space n)
    (hX : AEStronglyMeasurable X ν) :
    AEStronglyMeasurable
      (fun p : Ω × RsgfZeta n Sample =>
        (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (X p.1) p.2.1 p.2.2)
      (ν.prod (rsgfZetaLaw S)) := by
  let μζ : Measure (Sample × Space n) := S.P.prod (gaussianDirectionLaw n)
  have horacle :
      AEStronglyMeasurable
        (fun p : Ω × (Sample × Space n) =>
          rsgfOracle S (X p.1) p.2.1 p.2.2)
        (ν.prod μζ) := by
    simpa [μζ] using
      rsgfOracle_random_query_aestronglyMeasurable_of_aesm S X hX
  have hgrad :
      AEStronglyMeasurable
        (fun p : Ω × (Sample × Space n) =>
          ∇ (gaussianSmoothing S) (X p.1))
        (ν.prod μζ) := by
    simpa [Function.comp_def] using
      (rsgf_smoothing_gradient_random_query_aestronglyMeasurable
        S X hX).comp_fst
        (ν := μζ)
  simpa [SOptLib.oracleEstimatorError, μζ, rsgfZetaLaw] using horacle.sub hgrad

/-- Product-law square-integrability of the centered RSGF residual at a random
query, from the pointwise residual second-moment budget and objective-gap
integrability of the query. -/
private theorem rsgfResidual_random_query_norm_sq_integrable_of_gap_integrable
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    (S : Setup n Sample) (X : Ω → Space n)
    (hX : AEStronglyMeasurable X ν)
    (hgap_int :
      Integrable (fun ω : Ω => objective S (X ω) - fStar S) ν)
    (hresidual_gap_bound :
      ∀ ω : Ω,
        (∫ z : Sample × Space n,
            ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (X ω) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L * (objective S (X ω) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    Integrable
      (fun p : Ω × RsgfZeta n Sample =>
        ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (X p.1) p.2.1 p.2.2‖ ^ (2 : ℕ))
      (ν.prod (rsgfZetaLaw S)) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  let B : Ω → ℝ := fun ω =>
    4 * ((n : ℝ) + 4) * S.L * (objective S (X ω) - fStar S) +
      2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ)
  haveI : SFinite (rsgfZetaLaw S) := inferInstance
  have hφ_aesm :
      AEStronglyMeasurable
        (fun p : Ω × RsgfZeta n Sample =>
          ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (X p.1) p.2.1 p.2.2‖ ^ (2 : ℕ))
        (ν.prod (rsgfZetaLaw S)) := by
    have hraw :
        AEStronglyMeasurable
          (fun p : Ω × RsgfZeta n Sample =>
            (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (X p.1) p.2.1 p.2.2)
          (ν.prod (rsgfZetaLaw S)) :=
      rsgfResidual_random_query_aestronglyMeasurable_of_aesm S X hX
    exact (hraw.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hB_int : Integrable B ν := by
    have hgap_scaled :
        Integrable
          (fun ω : Ω =>
            (4 * ((n : ℝ) + 4) * S.L) *
              (objective S (X ω) - fStar S)) ν :=
      hgap_int.const_mul (4 * ((n : ℝ) + 4) * S.L)
    have hconst1 :
        Integrable
          (fun _ω : Ω => 2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) ν :=
      integrable_const _
    have hconst2 :
        Integrable
          (fun _ω : Ω =>
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) ν :=
      integrable_const _
    simpa [B, mul_assoc] using (hgap_scaled.add hconst1).add hconst2
  refine
    integrable_prod_of_nonneg_fiber_integral_le_integrable_bound
      (μ := ν) (ν := rsgfZetaLaw S)
      (φ := fun ω z => ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (X ω) z.1 z.2‖ ^ (2 : ℕ))
      (B := B) hφ_aesm ?_ ?_ hB_int ?_
  · intro ω z
    positivity
  · intro ω
    simpa [rsgfZetaLaw] using rsgfResidual_norm_sq_integrable S (X ω)
  · intro ω
    simpa [B, rsgfZetaLaw] using hresidual_gap_bound ω

/-- Prefix-law residual square integrability from the objective-gap budget at
the same prefix index.  This is the residual analogue of the oracle `L²`
prefix transfer, using the same fresh-coordinate replacement of the iid prefix
law. -/
private theorem rsgf_prefix_residual_norm_sq_integrable_of_gap_integrable
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N))
    (hresidual_sample :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N))
    (hgap_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N))
    (hresidual_gap_bound :
      ∀ ζ : RsgfSamplePrefix n Sample N,
        (∫ z : Sample × Space n,
            ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2‖ ^
                (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ))
      (rsgfPrefixLaw S N) := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^ (2 : ℕ)
  let Ψ : RsgfSamplePrefix n Sample N × RsgfZeta n Sample → ℝ := fun q =>
    ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S q.1 R) q.2.1 q.2.2‖ ^ (2 : ℕ)
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  have hprod_int :
      Integrable Ψ ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
    simpa [Ψ, R] using
      rsgfResidual_random_query_norm_sq_integrable_of_gap_integrable
        (ν := rsgfPrefixLaw S N) S
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (by simpa [R] using hX)
        (by simpa [R] using hgap_int)
        (by simpa [R] using hresidual_gap_bound)
  let replace : RsgfSamplePrefix n Sample N × RsgfZeta n Sample →
      RsgfSamplePrefix n Sample N := fun q => Function.update q.1 R q.2
  have hreplace :
      MeasurePreserving replace
        ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))
        (rsgfPrefixLaw S N) := by
    simpa [replace, R] using
      rsgfPrefixLaw_replace_coordinate_measurePreserving S R
  have hcomp_int :
      Integrable (fun q : RsgfSamplePrefix n Sample N × RsgfZeta n Sample =>
        Φ (replace q)) ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S)) := by
    refine hprod_int.congr (Filter.Eventually.of_forall ?_)
    intro q
    have hx :
        rsgfPrefixIterate S (replace q) R =
          rsgfPrefixIterate S q.1 R := by
      simpa [replace, R] using
        rsgf_prefix_iterate_current_coordinate_independent S q.1 hk q.2
    simp [Φ, Ψ, replace, R, hx]
  have hΦ_aesm :
      AEStronglyMeasurable Φ
        (Measure.map replace ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))) := by
    rw [hreplace.map_eq]
    simpa [Φ, R] using
      ((hresidual_sample.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  have hmap_int :
      Integrable Φ
        (Measure.map replace ((rsgfPrefixLaw S N).prod (rsgfZetaLaw S))) :=
    (MeasureTheory.integrable_map_measure hΦ_aesm hreplace.aemeasurable).mpr hcomp_int
  simpa [Φ, R, hreplace.map_eq] using hmap_int

/-- Prefix-law sampled residual measurability from prefix-iterate
measurability. -/
private theorem rsgf_prefix_sampled_residual_aestronglyMeasurable_of_iterate
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N)) :
    AEStronglyMeasurable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
      (rsgfPrefixLaw S N) := by
  have horacle :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N) :=
    rsgf_prefix_sampled_oracle_aestronglyMeasurable_of_iterate S hk hX
  have hgrad :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩))
        (rsgfPrefixLaw S N) :=
    rsgf_smoothing_gradient_random_query_aestronglyMeasurable
      S (fun ζ : RsgfSamplePrefix n Sample N =>
        rsgfPrefixIterate S ζ ⟨k, hk⟩) hX
  simpa [SOptLib.oracleEstimatorError] using horacle.sub hgrad

/-- Residual-inner integrability under the finite prefix law, derived from the
already established prefix L2/objective-gap budget.  This is the side condition
needed to invoke prefix residual cancellation in the convex recursion. -/
private theorem rsgf_residual_inner_budget_from_prefix_l2_gap
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N) (xStar : Space n)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - xStar‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
      (rsgfPrefixLaw S N) := by
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  have hprefix_oracle := rsgfPrefixIterate_and_oracle_aestronglyMeasurable S R
  have hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (rsgfPrefixLaw S N) := hprefix_oracle.1
  have hresidual_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_prefix_sampled_residual_aestronglyMeasurable_of_iterate S hk
        (by simpa [R] using hX)
  have hresidual_sq :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
            (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_prefix_residual_norm_sq_integrable_of_gap_integrable
        S hk
        (by simpa [R] using hX)
        (by simpa [R] using hresidual_aesm)
        (by simpa [R] using (hprefix_budget R).2)
        (by
          intro ζ
          simpa [R] using
            rsgfResidual_secondMoment_le_objective_gap_sigma S
              (rsgfPrefixIterate S ζ R))
  have hmult_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ R - xStar)
        (rsgfPrefixLaw S N) :=
    hX.sub aestronglyMeasurable_const
  exact
    integrable_inner_of_integrable_sq_norm
      hresidual_aesm hmult_aesm hresidual_sq (by simpa [R] using (hprefix_budget R).1)

/-- Convex prefix L2/objective-gap induction for the finite prefix law.  This
packages the one-based interval induction: once prefix iterates are measurable
and the real one-step argument propagates the centered squared-distance
integrability from `k` to `k + 1`, the objective-gap integrability at every
output index follows from the smooth global-minimizer distance domination. -/
private theorem rsgf_convex_prefix_l2_gap_budget_induction
    (S : Setup n Sample) {N : ℕ} (hN : 1 ≤ N) (xStar : Space n)
    (hoptimal : ∀ y : Space n, objective S xStar ≤ objective S y)
    (horacle_gap_bound :
      ∀ (R : RsgfOutputIndex N) (ζ : RsgfSamplePrefix n Sample N),
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ R) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ R) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    ∀ R : RsgfOutputIndex N,
      Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖rsgfPrefixIterate S ζ R - xStar‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) ∧
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ R) - fStar S)
      (rsgfPrefixLaw S N) := by
  classical
  have hprefix_oracle_aesm :
      ∀ R : RsgfOutputIndex N,
        AEStronglyMeasurable
            (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
            (rsgfPrefixLaw S N) ∧
          AEStronglyMeasurable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
            (rsgfPrefixLaw S N) :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable S
  have hprefix_aesm :
      ∀ R : RsgfOutputIndex N,
        AEStronglyMeasurable
          (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
          (rsgfPrefixLaw S N) := fun R => (hprefix_oracle_aesm R).1
  have horacle_aesm :
      ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
        AEStronglyMeasurable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
          (rsgfPrefixLaw S N) := fun k hk => (hprefix_oracle_aesm ⟨k, hk⟩).2
  let P : (k : ℕ) → k ∈ Icc 1 N → Prop := fun k hk =>
    Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) ∧
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N)
  have hbase : ∀ h1 : 1 ∈ Icc 1 N, P 1 h1 := by
    intro h1
    simpa [P] using
      rsgfPrefixIterate_first_l2_gap_integrable S h1 xStar hoptimal
  have hgap_of_l2 :
      ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) →
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
          (rsgfPrefixLaw S N) := by
    intro k hk hl2
    exact
      objective_gap_integrable_of_sq_distance_integrable
        S xStar
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ ⟨k, hk⟩)
        hoptimal (hprefix_aesm ⟨k, hk⟩) hl2
  have hmain :
      ∀ k (hk_lower : 1 ≤ k) (hk_upper : k ≤ N) (hk : k ∈ Icc 1 N),
        P k hk := by
    intro k hk_lower hk_upper hk
    let Q : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ =>
      ∀ (hj_upper : j ≤ N) (hj : j ∈ Icc 1 N), P j hj
    have hQbase : Q 1 le_rfl := by
      intro h1_upper h1
      exact hbase h1
    have hQstep :
        ∀ (j : ℕ) (hj_lower : 1 ≤ j),
          Q j hj_lower → Q (j + 1) (Nat.le_succ_of_le hj_lower) := by
      intro j hj_lower hQj hsucc_upper hsucc
      have hj_upper : j ≤ N := Nat.le_trans (Nat.le_succ j) hsucc_upper
      have hj : j ∈ Icc 1 N := mem_Icc.mpr ⟨hj_lower, hj_upper⟩
      have hprev : P j hj := hQj hj_upper hj
      have horacle_l2 :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨j, hj⟩)
                  (ζ ⟨j, hj⟩).1 (ζ ⟨j, hj⟩).2‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) :=
        rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
          S hj (hprefix_aesm ⟨j, hj⟩) (horacle_aesm j hj) hprev.2
          (by
            intro ζ
            simpa using horacle_gap_bound ⟨j, hj⟩ ζ)
      have hl2_succ :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ ⟨j + 1, hsucc⟩ - xStar‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) :=
        rsgf_prefix_step_l2_of_oracle_l2
          S hj hsucc xStar (hprefix_aesm ⟨j, hj⟩)
          (horacle_aesm j hj) hprev.1 horacle_l2
      exact ⟨hl2_succ, hgap_of_l2 (j + 1) hsucc hl2_succ⟩
    exact (Nat.le_induction (m := 1) (P := Q) hQbase hQstep k hk_lower) hk_upper hk
  intro R
  exact hmain R.1 (mem_Icc.mp R.2).1 (mem_Icc.mp R.2).2 R.2

/-- Nonconvex prefix L2/objective-gap induction for the finite prefix law,
centered at the deterministic starting point `S.x₁`.  This is the nonconvex
analogue of `rsgf_convex_prefix_l2_gap_budget_induction`: the objective gap is
made integrable from centered L2 by the smooth model at `S.x₁` and the lower
bound `fStar`, not by convexity or an attained minimizer. -/
private theorem rsgf_nonconvex_prefix_l2_gap_budget_induction
    (S : Setup n Sample) {N : ℕ} (hN : 1 ≤ N)
    (horacle_gap_bound :
      ∀ (R : RsgfOutputIndex N) (ζ : RsgfSamplePrefix n Sample N),
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ R) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ R) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    ∀ R : RsgfOutputIndex N,
      Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) ∧
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ R) - fStar S)
          (rsgfPrefixLaw S N) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  have hprefix_oracle_aesm :
      ∀ R : RsgfOutputIndex N,
        AEStronglyMeasurable
            (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
            (rsgfPrefixLaw S N) ∧
          AEStronglyMeasurable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
            (rsgfPrefixLaw S N) :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable S
  have hprefix_aesm :
      ∀ R : RsgfOutputIndex N,
        AEStronglyMeasurable
          (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
          (rsgfPrefixLaw S N) := fun R => (hprefix_oracle_aesm R).1
  have horacle_aesm :
      ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
        AEStronglyMeasurable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
          (rsgfPrefixLaw S N) := fun k hk => (hprefix_oracle_aesm ⟨k, hk⟩).2
  let P : (k : ℕ) → k ∈ Icc 1 N → Prop := fun k hk =>
    Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - S.x₁‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) ∧
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N)
  have hbase : ∀ h1 : 1 ∈ Icc 1 N, P 1 h1 := by
    intro h1
    have hl2 :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖rsgfPrefixIterate S ζ ⟨1, h1⟩ - S.x₁‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) := by
      refine (integrable_const (0 : ℝ)).congr ?_
      exact Filter.Eventually.of_forall fun ζ => by
        simp [rsgfPrefixIterate_first_eq S h1 ζ]
    have hgap :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ ⟨1, h1⟩) - fStar S)
          (rsgfPrefixLaw S N) := by
      refine (integrable_const (objective S S.x₁ - fStar S)).congr ?_
      exact Filter.Eventually.of_forall fun ζ => by
        simp [rsgfPrefixIterate_first_eq S h1 ζ]
    exact ⟨hl2, hgap⟩
  have hgap_of_l2 :
      ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - S.x₁‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) →
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
          (rsgfPrefixLaw S N) := by
    intro k hk hl2
    exact
      objective_gap_integrable_of_sq_distance_integrable_from_base
        S S.x₁
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (hprefix_aesm ⟨k, hk⟩) hl2
  have hmain :
      ∀ k (hk_lower : 1 ≤ k) (hk_upper : k ≤ N) (hk : k ∈ Icc 1 N),
        P k hk := by
    intro k hk_lower hk_upper hk
    let Q : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ =>
      ∀ (hj_upper : j ≤ N) (hj : j ∈ Icc 1 N), P j hj
    have hQbase : Q 1 le_rfl := by
      intro _h1_upper h1
      exact hbase h1
    have hQstep :
        ∀ (j : ℕ) (hj_lower : 1 ≤ j),
          Q j hj_lower → Q (j + 1) (Nat.le_succ_of_le hj_lower) := by
      intro j hj_lower hQj hsucc_upper hsucc
      have hj_upper : j ≤ N := Nat.le_trans (Nat.le_succ j) hsucc_upper
      have hj : j ∈ Icc 1 N := mem_Icc.mpr ⟨hj_lower, hj_upper⟩
      have hprev : P j hj := hQj hj_upper hj
      have horacle_l2 :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨j, hj⟩)
                  (ζ ⟨j, hj⟩).1 (ζ ⟨j, hj⟩).2‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) :=
        rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
          S hj (hprefix_aesm ⟨j, hj⟩) (horacle_aesm j hj) hprev.2
          (by
            intro ζ
            simpa using horacle_gap_bound ⟨j, hj⟩ ζ)
      have hl2_succ :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ ⟨j + 1, hsucc⟩ - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) :=
        rsgf_prefix_step_l2_of_oracle_l2
          S hj hsucc S.x₁ (hprefix_aesm ⟨j, hj⟩)
          (horacle_aesm j hj) hprev.1 horacle_l2
      exact ⟨hl2_succ, hgap_of_l2 (j + 1) hsucc hl2_succ⟩
    exact (Nat.le_induction (m := 1) (P := Q) hQbase hQstep k hk_lower) hk_upper hk
  intro R
  exact hmain R.1 (mem_Icc.mp R.2).1 (mem_Icc.mp R.2).2 R.2

/-- Finite-window gamma-square aggregation of the nonconvex oracle
second-moment estimate (6.1.67), retaining the original-gradient square rather
than converting it to an objective gap. -/
private theorem rsgf_nonconvex_gamma_sq_oracle_le_gradient_sigma_sum
    (S : Setup n Sample) (N : ℕ)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N))
    (hgrad_int :
      ∀ R : RsgfOutputIndex N,
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N)) :
    Finset.sum (Icc 1 N)
        (fun k =>
          S.γ k ^ (2 : ℕ) *
            ∫ ζ : RsgfSamplePrefix n Sample N,
              (if hk : k ∈ Icc 1 N then
                ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                    (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
              else
                0) ∂(rsgfPrefixLaw S N)) ≤
      Finset.sum (Icc 1 N)
        (fun k =>
          S.γ k ^ (2 : ℕ) *
            (2 * ((n : ℝ) + 4) *
                ((∫ ζ : RsgfSamplePrefix n Sample N,
                    (if hk : k ∈ Icc 1 N then
                      ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                        (2 : ℕ)
                    else
                      0) ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) +
              S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                ((n : ℝ) + 6) ^ (3 : ℕ))) := by
  classical
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  refine Finset.sum_le_sum ?_
  intro k hk
  have hpoint :=
    rsgf_prefix_oracle_sq_integral_le_gradient_sigma_integral
      S hk
      ((hprefix_oracle ⟨k, hk⟩).1)
      ((hprefix_oracle ⟨k, hk⟩).2)
      ((hprefix_budget ⟨k, hk⟩).2)
      (hgrad_int ⟨k, hk⟩)
      (by
        intro ζ
        simpa using
          rsgfOracle_secondMoment_le_objective_gap_sigma S
            (rsgfPrefixIterate S ζ ⟨k, hk⟩))
  have horacle_eq :
      (∫ ζ : RsgfSamplePrefix n Sample N,
          (if hk' : k ∈ Icc 1 N then
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk'⟩)
                (ζ ⟨k, hk'⟩).1 (ζ ⟨k, hk'⟩).2‖ ^ (2 : ℕ)
          else
            0) ∂(rsgfPrefixLaw S N)) =
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N) := by
    simp [hk]
  have hgrad_eq :
      (∫ ζ : RsgfSamplePrefix n Sample N,
          (if hk' : k ∈ Icc 1 N then
            ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk'⟩)‖ ^
              (2 : ℕ)
          else
            0) ∂(rsgfPrefixLaw S N)) =
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
            (2 : ℕ)
          ∂(rsgfPrefixLaw S N) := by
    simp [hk]
  have hle :
      (∫ ζ : RsgfSamplePrefix n Sample N,
          (if hk' : k ∈ Icc 1 N then
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk'⟩)
                (ζ ⟨k, hk'⟩).1 (ζ ⟨k, hk'⟩).2‖ ^ (2 : ℕ)
          else
            0) ∂(rsgfPrefixLaw S N)) ≤
        2 * ((n : ℝ) + 4) *
            ((∫ ζ : RsgfSamplePrefix n Sample N,
                (if hk' : k ∈ Icc 1 N then
                  ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk'⟩)‖ ^
                    (2 : ℕ)
                else
                  0) ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) +
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 6) ^ (3 : ℕ) := by
    rw [horacle_eq, hgrad_eq]
    exact hpoint
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg (S.γ k))

/-- Prefix-law original-gradient square integrability for the nonconvex branch,
obtained by transporting the `S.x₁`-centered L2 prefix budget through the
Lipschitz objective gradient. -/
private theorem rsgf_nonconvex_prefix_gradient_norm_sq_integrable
    (S : Setup n Sample) {N : ℕ}
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    ∀ R : RsgfOutputIndex N,
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  intro R
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  have hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (rsgfPrefixLaw S N) := (hprefix_oracle R).1
  have hcenter_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖S.x₁ - rsgfPrefixIterate S ζ R‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    refine (hprefix_budget R).1.congr (Filter.Eventually.of_forall ?_)
    intro ζ
    simpa [norm_sub_rev]
  exact
    SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      (μ := rsgfPrefixLaw S N)
      S.x₁ (fun x : Space n => ∇ (objective S) x) S.L
      (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
      hX hcenter_l2 (objective_CL11 S).2

/-- Prefix-law smoothed-gradient square integrability for the nonconvex branch,
obtained from the same centered L2 prefix budget and the inherited Lipschitz
gradient of the Gaussian smoothing. -/
private theorem rsgf_nonconvex_prefix_smoothing_gradient_norm_sq_integrable
    (S : Setup n Sample) {N : ℕ}
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    ∀ R : RsgfOutputIndex N,
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  intro R
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  have hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (rsgfPrefixLaw S N) := (hprefix_oracle R).1
  have hcenter_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖S.x₁ - rsgfPrefixIterate S ζ R‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    refine (hprefix_budget R).1.congr (Filter.Eventually.of_forall ?_)
    intro ζ
    simpa [norm_sub_rev]
  exact
    SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      (μ := rsgfPrefixLaw S N)
      S.x₁ (fun x : Space n => ∇ (gaussianSmoothing S) x) S.L
      (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
      hX hcenter_l2 (gaussianSmoothing_gradient_lipschitz S)

/-- Integrated prefix version of source comparison (6.1.55), specialized to one
output-window index. -/
private theorem rsgf_prefix_original_grad_sq_integral_le_reverse_smoothing
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
        ∂rsgfPrefixLaw S N) ≤
      2 *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
              (2 : ℕ)
            ∂rsgfPrefixLaw S N) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 3) ^ (3 : ℕ) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let orig : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)
  let smooth : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)
  let eps : ℝ :=
    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
      ((n : ℝ) + 3) ^ (3 : ℕ)
  have horig_int : Integrable orig (rsgfPrefixLaw S N) := by
    simpa [orig, R] using
      rsgf_nonconvex_prefix_gradient_norm_sq_integrable S hprefix_budget R
  have hsmooth_int : Integrable smooth (rsgfPrefixLaw S N) := by
    simpa [smooth, R] using
      rsgf_nonconvex_prefix_smoothing_gradient_norm_sq_integrable
        S hprefix_budget R
  have hrhs_int :
      Integrable (fun ζ : RsgfSamplePrefix n Sample N => 2 * smooth ζ + eps)
        (rsgfPrefixLaw S N) :=
    (hsmooth_int.const_mul 2).add (integrable_const eps)
  have hpoint :
      ∀ ζ : RsgfSamplePrefix n Sample N,
        orig ζ ≤ 2 * smooth ζ + eps := by
    intro ζ
    simpa [orig, smooth, eps, R] using
      gaussianSmoothing_reverse_gradient_norm_sq_comparison
        S (rsgfPrefixIterate S ζ R)
  have hmono :
      (∫ ζ : RsgfSamplePrefix n Sample N, orig ζ ∂rsgfPrefixLaw S N) ≤
        ∫ ζ : RsgfSamplePrefix n Sample N, 2 * smooth ζ + eps
          ∂rsgfPrefixLaw S N := by
    exact integral_mono_ae horig_int hrhs_int
      (Filter.Eventually.of_forall hpoint)
  calc
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
        ∂rsgfPrefixLaw S N)
        = ∫ ζ : RsgfSamplePrefix n Sample N, orig ζ ∂rsgfPrefixLaw S N := by
            rfl
    _ ≤ ∫ ζ : RsgfSamplePrefix n Sample N, 2 * smooth ζ + eps
          ∂rsgfPrefixLaw S N := hmono
    _ =
        2 * (∫ ζ : RsgfSamplePrefix n Sample N, smooth ζ
              ∂rsgfPrefixLaw S N) +
          eps := by
            rw [integral_add (hsmooth_int.const_mul 2) (integrable_const eps)]
            rw [integral_const_mul]
            simp
    _ =
        2 *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                (2 : ℕ)
              ∂rsgfPrefixLaw S N) +
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 3) ^ (3 : ℕ) := by
            rfl

/-- Weighted finite-window version of the integrated reverse smoothing
comparison. This is the source step that transfers original-gradient energy
to smoothed-gradient energy before the scalar descent budget is applied. -/
private theorem rsgf_weighted_original_grad_sq_sum_le_reverse_smoothing
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    Finset.sum (Icc 1 N)
        (fun k =>
          rsgfWeightNumerator S k *
            ∫ ζ : RsgfSamplePrefix n Sample N,
              (if hk : k ∈ Icc 1 N then
                ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                  (2 : ℕ)
              else
                0) ∂rsgfPrefixLaw S N) ≤
      2 *
          Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (gaussianSmoothing S)
                        (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂rsgfPrefixLaw S N) +
        (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 3) ^ (3 : ℕ)) *
          Finset.sum (Icc 1 N) (fun k => rsgfWeightNumerator S k) := by
  classical
  let eps : ℝ :=
    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
      ((n : ℝ) + 3) ^ (3 : ℕ)
  let origIntegral : ℕ → ℝ := fun k =>
    ∫ ζ : RsgfSamplePrefix n Sample N,
      (if hk : k ∈ Icc 1 N then
        ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
      else
        0) ∂rsgfPrefixLaw S N
  let smoothIntegral : ℕ → ℝ := fun k =>
    ∫ ζ : RsgfSamplePrefix n Sample N,
      (if hk : k ∈ Icc 1 N then
        ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
          (2 : ℕ)
      else
        0) ∂rsgfPrefixLaw S N
  have hterm :
      ∀ k ∈ Icc 1 N,
        rsgfWeightNumerator S k * origIntegral k ≤
          rsgfWeightNumerator S k * (2 * smoothIntegral k + eps) := by
    intro k hk
    have hplain :=
      rsgf_prefix_original_grad_sq_integral_le_reverse_smoothing
        S hk hprefix_budget
    have horig_eq :
        origIntegral k =
          ∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
              (2 : ℕ)
            ∂rsgfPrefixLaw S N := by
      dsimp [origIntegral]
      simp [hk]
    have hsmooth_eq :
        smoothIntegral k =
          ∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
              (2 : ℕ)
            ∂rsgfPrefixLaw S N := by
      dsimp [smoothIntegral]
      simp [hk]
    have hle : origIntegral k ≤ 2 * smoothIntegral k + eps := by
      simpa [horig_eq, hsmooth_eq, eps] using hplain
    exact mul_le_mul_of_nonneg_left hle
      (SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR k hk)
  calc
    Finset.sum (Icc 1 N)
        (fun k =>
          rsgfWeightNumerator S k *
            ∫ ζ : RsgfSamplePrefix n Sample N,
              (if hk : k ∈ Icc 1 N then
                ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                  (2 : ℕ)
              else
                0) ∂rsgfPrefixLaw S N)
        = Finset.sum (Icc 1 N)
            (fun k => rsgfWeightNumerator S k * origIntegral k) := by
            rfl
    _ ≤ Finset.sum (Icc 1 N)
          (fun k => rsgfWeightNumerator S k * (2 * smoothIntegral k + eps)) := by
          exact Finset.sum_le_sum hterm
    _ =
        2 * Finset.sum (Icc 1 N)
            (fun k => rsgfWeightNumerator S k * smoothIntegral k) +
          eps * Finset.sum (Icc 1 N) (fun k => rsgfWeightNumerator S k) := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          simp [mul_comm, mul_left_comm, mul_assoc]
    _ =
        2 *
            Finset.sum (Icc 1 N)
              (fun k =>
                rsgfWeightNumerator S k *
                  ∫ ζ : RsgfSamplePrefix n Sample N,
                    (if hk : k ∈ Icc 1 N then
                      ‖∇ (gaussianSmoothing S)
                          (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                        (2 : ℕ)
                    else
                      0) ∂rsgfPrefixLaw S N) +
          (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 3) ^ (3 : ℕ)) *
            Finset.sum (Icc 1 N) (fun k => rsgfWeightNumerator S k) := by
          rfl

/-- Raw-stepsize finite-window version of the integrated reverse smoothing
comparison.  This is the same source comparison as the output-weighted bridge,
but with the `γ_k` weights needed before the nonconvex scalar rearrangement. -/
private theorem rsgf_gamma_weighted_original_grad_sq_sum_le_reverse_smoothing
    (S : Setup n Sample) (N : ℕ)
    (hγ_upper : ∀ k ∈ Icc 1 N,
      S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    Finset.sum (Icc 1 N)
        (fun k =>
          S.γ k *
            ∫ ζ : RsgfSamplePrefix n Sample N,
              (if hk : k ∈ Icc 1 N then
                ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                  (2 : ℕ)
              else
                0) ∂rsgfPrefixLaw S N) ≤
      2 *
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (gaussianSmoothing S)
                        (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂rsgfPrefixLaw S N) +
        (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 3) ^ (3 : ℕ)) *
          Finset.sum (Icc 1 N) S.γ := by
  classical
  let eps : ℝ :=
    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
      ((n : ℝ) + 3) ^ (3 : ℕ)
  let origIntegral : ℕ → ℝ := fun k =>
    ∫ ζ : RsgfSamplePrefix n Sample N,
      (if hk : k ∈ Icc 1 N then
        ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
      else
        0) ∂rsgfPrefixLaw S N
  let smoothIntegral : ℕ → ℝ := fun k =>
    ∫ ζ : RsgfSamplePrefix n Sample N,
      (if hk : k ∈ Icc 1 N then
        ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
          (2 : ℕ)
      else
        0) ∂rsgfPrefixLaw S N
  have hγ_nonneg : ∀ k, k ∈ Icc 1 N → 0 ≤ S.γ k := by
    intro k hk
    exact
      rsgf_stepsize_nonneg_of_weight_nonneg_of_upper
        S hk
        (SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR k hk)
        (hγ_upper k hk)
  have hterm :
      ∀ k ∈ Icc 1 N,
        S.γ k * origIntegral k ≤
          S.γ k * (2 * smoothIntegral k + eps) := by
    intro k hk
    have hplain :=
      rsgf_prefix_original_grad_sq_integral_le_reverse_smoothing
        S hk hprefix_budget
    have horig_eq :
        origIntegral k =
          ∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
              (2 : ℕ)
            ∂rsgfPrefixLaw S N := by
      dsimp [origIntegral]
      simp [hk]
    have hsmooth_eq :
        smoothIntegral k =
          ∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
              (2 : ℕ)
            ∂rsgfPrefixLaw S N := by
      dsimp [smoothIntegral]
      simp [hk]
    have hle : origIntegral k ≤ 2 * smoothIntegral k + eps := by
      simpa [horig_eq, hsmooth_eq, eps] using hplain
    exact mul_le_mul_of_nonneg_left hle (hγ_nonneg k hk)
  calc
    Finset.sum (Icc 1 N)
        (fun k =>
          S.γ k *
            ∫ ζ : RsgfSamplePrefix n Sample N,
              (if hk : k ∈ Icc 1 N then
                ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                  (2 : ℕ)
              else
                0) ∂rsgfPrefixLaw S N)
        = Finset.sum (Icc 1 N) (fun k => S.γ k * origIntegral k) := by
            rfl
    _ ≤ Finset.sum (Icc 1 N)
          (fun k => S.γ k * (2 * smoothIntegral k + eps)) := by
          exact Finset.sum_le_sum hterm
    _ =
        2 * Finset.sum (Icc 1 N)
            (fun k => S.γ k * smoothIntegral k) +
          eps * Finset.sum (Icc 1 N) S.γ := by
          simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          simp [mul_comm, mul_left_comm, mul_assoc]
    _ =
        2 *
            Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k *
                  ∫ ζ : RsgfSamplePrefix n Sample N,
                    (if hk : k ∈ Icc 1 N then
                      ‖∇ (gaussianSmoothing S)
                          (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                        (2 : ℕ)
                    else
                      0) ∂rsgfPrefixLaw S N) +
          (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            ((n : ℝ) + 3) ^ (3 : ℕ)) *
            Finset.sum (Icc 1 N) S.γ := by
          rfl

/-- Nonconvex residual-cancellation side condition for the smoothed descent
recursion: the scalar product of the sampled residual with the smoothed
gradient is integrable under the finite prefix law. -/
private theorem rsgf_residual_smoothing_grad_inner_integrable_from_prefix_l2_gap
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ)
      (rsgfPrefixLaw S N) := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  have hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (rsgfPrefixLaw S N) := (hprefix_oracle R).1
  have horacle_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        (rsgfPrefixLaw S N) := (hprefix_oracle R).2
  have hresidual_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_prefix_sampled_residual_aestronglyMeasurable_of_iterate S hk
        (by simpa [R] using hX)
  have hgrad_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R))
        (rsgfPrefixLaw S N) :=
    rsgf_smoothing_gradient_random_query_aestronglyMeasurable
      S (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R) hX
  have horacle_sq :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
            (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
        S hk
        (by simpa [R] using hX)
        (by simpa [R] using horacle_aesm)
        (by simpa [R] using (hprefix_budget R).2)
        (by
          intro ζ
          simpa [R] using
            rsgfOracle_secondMoment_le_objective_gap_sigma S
              (rsgfPrefixIterate S ζ R))
  have hresidual_sq :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
            (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_prefix_residual_norm_sq_integrable_of_gap_integrable
        S hk
        (by simpa [R] using hX)
        (by simpa [R] using hresidual_aesm)
        (by simpa [R] using (hprefix_budget R).2)
        (by
          intro ζ
          simpa [R] using
            rsgfResidual_secondMoment_le_objective_gap_sigma S
              (rsgfPrefixIterate S ζ R))
  have hgrad_sq :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    have hdiff :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2 -
                (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
              (2 : ℕ))
          (rsgfPrefixLaw S N) :=
      integrable_sq_norm_sub
        (P := rsgfPrefixLaw S N)
        (u := fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        (v := fun ζ : RsgfSamplePrefix n Sample N =>
          (fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        horacle_aesm hresidual_aesm horacle_sq hresidual_sq
    refine hdiff.congr (Filter.Eventually.of_forall ?_)
    intro ζ
    simp [SOptLib.oracleEstimatorError]
  exact
    integrable_inner_of_integrable_sq_norm
      hresidual_aesm hgrad_aesm hresidual_sq hgrad_sq

/-- Terminal smoothed-objective integrability for one RSGF prefix update.  This
covers the endpoint `x_{k+1}` even when `k = N`, where the terminal value is not
an `RsgfOutputIndex N` but is still generated by the length-`N` prefix. -/
private theorem rsgf_prefix_terminal_gaussianSmoothing_integrable_from_prefix_l2_gap
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        gaussianSmoothing S (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2))
      (rsgfPrefixLaw S N) := by
  classical
  haveI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let X : RsgfSamplePrefix n Sample N → Space n := fun ζ =>
    rsgfPrefixIterate S ζ R
  let G : RsgfSamplePrefix n Sample N → Space n := fun ζ =>
    rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2
  let Xnext : RsgfSamplePrefix n Sample N → Space n := fun ζ =>
    rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  have hX : AEStronglyMeasurable X (rsgfPrefixLaw S N) := by
    simpa [X, R] using (hprefix_oracle R).1
  have hG : AEStronglyMeasurable G (rsgfPrefixLaw S N) := by
    simpa [G, R] using (hprefix_oracle R).2
  have hX_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N => ‖X ζ - S.x₁‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    simpa [X, R] using (hprefix_budget R).1
  have hgap_cur :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (X ζ) - fStar S)
        (rsgfPrefixLaw S N) := by
    simpa [X, R] using (hprefix_budget R).2
  have hG_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N => ‖G ζ‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    simpa [G, X, R] using
      rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
        S hk
        (by simpa [X, R] using hX)
        (by simpa [G, X, R] using hG)
        (by simpa [X, R] using hgap_cur)
        (by
          intro ζ
          simpa [X, R] using
            rsgfOracle_secondMoment_le_objective_gap_sigma S (X ζ))
  have hnext :
      ∀ ζ : RsgfSamplePrefix n Sample N, Xnext ζ = X ζ - S.γ k • G ζ := by
    intro ζ
    dsimp [Xnext, X, G, R]
    cases k with
    | zero =>
        have hk_pos : 1 ≤ 0 := (mem_Icc.mp hk).1
        omega
    | succ j =>
        simp [rsgfPrefixIterate, rsgfPrefixIterate0, rsgfStep_def]
  have hXnext_aesm : AEStronglyMeasurable Xnext (rsgfPrefixLaw S N) := by
    exact (hX.sub (hG.const_smul (S.γ k))).congr
      (Filter.Eventually.of_forall fun ζ => (hnext ζ).symm)
  have hXnext_l2 :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N => ‖Xnext ζ - S.x₁‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    have hupdate_l2 :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖(X ζ - S.γ k • G ζ) - S.x₁‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) :=
      integrable_sq_norm_affine_update_of_l2
        X G S.x₁ (S.γ k) hX hG hX_l2 hG_l2
    refine hupdate_l2.congr (Filter.Eventually.of_forall ?_)
    intro ζ
    dsimp
    rw [hnext ζ]
  have hgap_next :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (Xnext ζ) - fStar S)
        (rsgfPrefixLaw S N) :=
    objective_gap_integrable_of_sq_distance_integrable_from_base
      S S.x₁ Xnext hXnext_aesm hXnext_l2
  simpa [Xnext] using
    gaussianSmoothing_random_query_integrable_of_gap_integrable
      S Xnext hXnext_aesm hgap_next

/-- Bochner integral linearity for the scalar four-term expression used by the
integrated squared-distance recursion. -/
private theorem integral_sub_sub_add_const_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a b c d : Ω → ℝ) (α β δ : ℝ)
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hd : Integrable d μ) :
    (∫ ω, a ω - α * b ω - β * c ω + δ * d ω ∂μ) =
      (∫ ω, a ω ∂μ) - α * (∫ ω, b ω ∂μ) -
        β * (∫ ω, c ω ∂μ) + δ * (∫ ω, d ω ∂μ) := by
  simpa [smul_eq_mul] using
    (integral_sub_smul_sub_smul_add_smul (μ := μ)
      (a := a) (b := b) (c := c) (d := d) (α := α) (β := β) (δ := δ)
      ha hb hc hd)

/-- Integrated one-step smoothed descent under the finite prefix law.  This is
the expectation-level form of (6.1.64), including the final update `k = N`
through the terminal `rsgfPrefixIterate0` value. -/
private theorem rsgf_prefix_smoothing_descent_step_integral
    (S : Setup n Sample) {N k : ℕ} (hk : k ∈ Icc 1 N)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        gaussianSmoothing S (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2)
        ∂(rsgfPrefixLaw S N)) ≤
      (∫ ζ : RsgfSamplePrefix n Sample N,
          gaussianSmoothing S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          ∂(rsgfPrefixLaw S N)) -
        S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
              (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) -
        S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
              ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
            ∂(rsgfPrefixLaw S N)) +
        (S.L / 2) * S.γ k ^ (2 : ℕ) *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) := by
  classical
  haveI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  have hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
        (rsgfPrefixLaw S N) := (hprefix_oracle R).1
  have hG :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        (rsgfPrefixLaw S N) := (hprefix_oracle R).2
  have hcurrent_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          gaussianSmoothing S (rsgfPrefixIterate S ζ R))
        (rsgfPrefixLaw S N) :=
    gaussianSmoothing_random_query_integrable_of_gap_integrable
      S (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
      hX (by simpa [R] using (hprefix_budget R).2)
  have hterminal_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          gaussianSmoothing S (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2))
        (rsgfPrefixLaw S N) :=
    rsgf_prefix_terminal_gaussianSmoothing_integrable_from_prefix_l2_gap
      S hk hprefix_budget
  have hsmooth_grad_sq_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) :=
    rsgf_nonconvex_prefix_smoothing_gradient_norm_sq_integrable
      S hprefix_budget R
  have hresidual_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
            ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)⟫_ℝ)
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_residual_smoothing_grad_inner_integrable_from_prefix_l2_gap
        S hk hprefix_budget
  have horacle_sq_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
            (2 : ℕ))
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
        S hk
        (by simpa [R] using hX)
        (by simpa [R] using hG)
        (by simpa [R] using (hprefix_budget R).2)
        (by
          intro ζ
          simpa [R] using
            rsgfOracle_secondMoment_le_objective_gap_sigma S
              (rsgfPrefixIterate S ζ R))
  let rhs : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    gaussianSmoothing S (rsgfPrefixIterate S ζ R) -
      S.γ k *
        ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ) -
      S.γ k *
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)⟫_ℝ +
      (S.L / 2) * S.γ k ^ (2 : ℕ) *
        ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
          (2 : ℕ)
  have hrhs_int : Integrable rhs (rsgfPrefixLaw S N) := by
    simpa [rhs] using
      ((hcurrent_int.sub (hsmooth_grad_sq_int.const_mul (S.γ k))).sub
        (hresidual_int.const_mul (S.γ k))).add
        (horacle_sq_int.const_mul ((S.L / 2) * S.γ k ^ (2 : ℕ)))
  have hmono :
      (∫ ζ : RsgfSamplePrefix n Sample N,
          gaussianSmoothing S (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2)
          ∂(rsgfPrefixLaw S N)) ≤
        ∫ ζ : RsgfSamplePrefix n Sample N, rhs ζ ∂(rsgfPrefixLaw S N) := by
    refine integral_mono_ae hterminal_int hrhs_int ?_
    exact Filter.Eventually.of_forall fun ζ => by
      have hp := rsgf_prefix_smoothing_descent_step_pointwise S hk ζ
      simpa [rhs, R, real_inner_comm] using hp
  have hrhs_eval :
      (∫ ζ : RsgfSamplePrefix n Sample N, rhs ζ ∂(rsgfPrefixLaw S N)) =
        (∫ ζ : RsgfSamplePrefix n Sample N,
            gaussianSmoothing S (rsgfPrefixIterate S ζ R)
            ∂(rsgfPrefixLaw S N)) -
          S.γ k *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) -
          S.γ k *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
                ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)⟫_ℝ
              ∂(rsgfPrefixLaw S N)) +
          (S.L / 2) * S.γ k ^ (2 : ℕ) *
            (∫ ζ : RsgfSamplePrefix n Sample N,
              ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
                (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) := by
    simpa [rhs] using
      integral_sub_sub_add_const_mul
        (μ := rsgfPrefixLaw S N)
        (a := fun ζ : RsgfSamplePrefix n Sample N =>
          gaussianSmoothing S (rsgfPrefixIterate S ζ R))
        (b := fun ζ : RsgfSamplePrefix n Sample N =>
          ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
        (c := fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
            ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ R)⟫_ℝ)
        (d := fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
            (2 : ℕ))
        (α := S.γ k) (β := S.γ k)
        (δ := (S.L / 2) * S.γ k ^ (2 : ℕ))
        hcurrent_int hsmooth_grad_sq_int hresidual_int horacle_sq_int
  calc
    (∫ ζ : RsgfSamplePrefix n Sample N,
        gaussianSmoothing S (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2)
        ∂(rsgfPrefixLaw S N))
        ≤ ∫ ζ : RsgfSamplePrefix n Sample N, rhs ζ
            ∂(rsgfPrefixLaw S N) := hmono
    _ =
      (∫ ζ : RsgfSamplePrefix n Sample N,
          gaussianSmoothing S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          ∂(rsgfPrefixLaw S N)) -
        S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
              (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) -
        S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
              ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
            ∂(rsgfPrefixLaw S N)) +
        (S.L / 2) * S.γ k ^ (2 : ℕ) *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) := by
          simpa [R] using hrhs_eval

/-- Exact scalar telescope for the integrated RSGF squared-distance recursion.
It sums one-step identities on the one-based window and removes an already
cancelled residual sequence. -/
private theorem sum_Icc_one_step_terminal_eq_of_residual_zero
    (A grad residual oracle γ : ℕ → ℝ) :
    ∀ N : ℕ, 1 ≤ N →
      (∀ k, k ∈ Icc 1 N →
        A (k + 1) =
          A k - 2 * γ k * grad k - 2 * γ k * residual k +
            γ k ^ (2 : ℕ) * oracle k) →
      (∀ k, k ∈ Icc 1 N → residual k = 0) →
      A (N + 1) =
        A 1 -
          2 * Finset.sum (Icc 1 N) (fun k => γ k * grad k) +
          Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * oracle k) := by
  intro N hN hstep hresidual
  first
  | exact _root_.sum_Icc_one_step_terminal_eq_of_residual_zero
      A grad residual oracle γ N hstep hresidual
  | exact _root_.sum_Icc_one_step_terminal_eq_of_residual_zero
      A grad residual oracle γ N hN hstep hresidual

/-- Scalar isolation after the terminal distance recursion: a nonnegative
terminal term upper-bounds the retained gradient-inner budget by the initial
distance plus the oracle-square budget. -/
private theorem two_mul_sum_gamma_grad_le_of_terminal_recursion_nonneg
    (A grad oracle γ : ℕ → ℝ) (N : ℕ)
    (hrec :
      A (N + 1) =
        A 1 -
          2 * Finset.sum (Icc 1 N) (fun k => γ k * grad k) +
          Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * oracle k))
    (hterminal_nonneg : 0 ≤ A (N + 1)) :
    2 * Finset.sum (Icc 1 N) (fun k => γ k * grad k) ≤
      A 1 + Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * oracle k) := by
  nlinarith

/-- Scalar telescope for the integrated smoothed-descent inequality.  It sums
one-step descent inequalities on the one-based window and removes an already
cancelled residual sequence. -/
private theorem two_mul_sum_gamma_grad_le_of_descent_recursion
    (A grad residual oracle γ : ℕ → ℝ) (L : ℝ) :
    ∀ N : ℕ, 1 ≤ N →
      (∀ k, k ∈ Icc 1 N →
        A (k + 1) ≤
          A k - γ k * grad k - γ k * residual k +
            (L / 2) * γ k ^ (2 : ℕ) * oracle k) →
      (∀ k, k ∈ Icc 1 N → residual k = 0) →
      2 * Finset.sum (Icc 1 N) (fun k => γ k * grad k) ≤
        2 * A 1 - 2 * A (N + 1) +
          L * Finset.sum (Icc 1 N) (fun k => γ k ^ (2 : ℕ) * oracle k) := by
  classical
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hstep hresidual
      have htel :
          A (N + 1 + 1) ≤
            A 1 -
              Finset.sum (Icc 1 (N + 1)) (fun k => γ k * grad k) +
              (L / 2) *
                Finset.sum (Icc 1 (N + 1))
                  (fun k => γ k ^ (2 : ℕ) * oracle k) := by
        by_cases hN_zero : N = 0
        · subst N
          have hmem : 1 ∈ Icc 1 1 := by simp
          have hstep1 := hstep 1 hmem
          have hres1 := hresidual 1 hmem
          simp [hres1] at hstep1 ⊢
          nlinarith
        · have hN_pos : 1 ≤ N := by omega
          have hstep_prefix :
              ∀ k, k ∈ Icc 1 N →
                A (k + 1) ≤
                  A k - γ k * grad k - γ k * residual k +
                    (L / 2) * γ k ^ (2 : ℕ) * oracle k := by
            intro k hk
            exact hstep k (by
              exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
                Nat.le_trans (mem_Icc.mp hk).2 (Nat.le_succ N)⟩)
          have hresidual_prefix :
              ∀ k, k ∈ Icc 1 N → residual k = 0 := by
            intro k hk
            exact hresidual k (by
              exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
                Nat.le_trans (mem_Icc.mp hk).2 (Nat.le_succ N)⟩)
          have htel_prefix :=
            ih hN_pos hstep_prefix hresidual_prefix
          have htop_mem : N + 1 ∈ Icc 1 (N + 1) := by
            exact mem_Icc.mpr ⟨by omega, le_rfl⟩
          have hstep_top := hstep (N + 1) htop_mem
          have hres_top := hresidual (N + 1) htop_mem
          have htop_pos : 1 ≤ N + 1 := by omega
          rw [Finset.sum_Icc_succ_top htop_pos]
          rw [Finset.sum_Icc_succ_top htop_pos]
          simp [hres_top] at hstep_top
          nlinarith
      nlinarith [htel]

/-- Prefix-law integrability of the smoothed-gradient inner product.  The
proof reuses the oracle/residual split in the step identity, but exposes the
integrability fact needed to integrate the convex smoothing lower bound. -/
private theorem rsgf_prefix_grad_inner_integrable_from_prefix_l2_gap
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N)
    (xStar : Space n)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - xStar‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N))
    (hresidual_inner_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N))
    (horacle_gap_bound :
      ∀ (R : RsgfOutputIndex N) (ζ : RsgfSamplePrefix n Sample N),
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ R) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ R) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
      (rsgfPrefixLaw S N) := by
  classical
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  have hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N) := (hprefix_oracle ⟨k, hk⟩).1
  have hG_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N) := (hprefix_oracle ⟨k, hk⟩).2
  have hdist_cur :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := (hprefix_budget ⟨k, hk⟩).1
  have hgap_cur :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N) := (hprefix_budget ⟨k, hk⟩).2
  have horacle_sq :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) :=
    rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
      S hk hX hG_aesm hgap_cur
      (by
        intro ζ
        simpa using horacle_gap_bound ⟨k, hk⟩ ζ)
  have hdisp_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar)
        (rsgfPrefixLaw S N) :=
    hX.sub aestronglyMeasurable_const
  have horacle_inner_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N) :=
    integrable_inner_of_integrable_sq_norm
      hG_aesm hdisp_aesm horacle_sq hdist_cur
  refine (horacle_inner_int.sub hresidual_inner_int).congr
    (Filter.Eventually.of_forall ?_)
  intro ζ
  change
    ⟪rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
      rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
      ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
        rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ =
        ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
  simp [SOptLib.oracleEstimatorError, inner_sub_left]

/-- Integrated one-step squared-distance identity under the finite prefix law.
This is the expectation-level version of the pathwise residual split; it
derives every integrability side condition from the prefix L2/objective-gap
budget and the already constructed residual-inner budget. -/
private theorem rsgf_prefix_step_sq_distance_integral_identity_residual
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N) (hks : k + 1 ∈ Icc 1 N)
    (xStar : Space n)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - xStar‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N))
    (hresidual_inner_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N))
    (horacle_gap_bound :
      ∀ (R : RsgfOutputIndex N) (ζ : RsgfSamplePrefix n Sample N),
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ R) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ R) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ - xStar‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N)) =
      (∫ ζ : RsgfSamplePrefix n Sample N,
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N)) -
        2 * S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
            ∂(rsgfPrefixLaw S N)) -
        2 * S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
            ∂(rsgfPrefixLaw S N)) +
        S.γ k ^ (2 : ℕ) *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) := by
  classical
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  apply
    integral_sq_dist_update_eq_sq_dist_sub_inner_add_norm_sq_of_oracle_eq_target_add_residual
      (P := rsgfPrefixLaw S N)
      (x := fun ζ => rsgfPrefixIterate S ζ ⟨k, hk⟩)
      (xNext := fun ζ => rsgfPrefixIterate S ζ ⟨k + 1, hks⟩)
      (target := fun ζ =>
        ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩))
      (residual := fun ζ =>
        (fun x ξ u =>
          SOptLib.oracleEstimatorError
            (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x)
          (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
      (oracle := fun ζ =>
        rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
      (xStar := xStar) (eta := S.γ k)
  · intro ζ
    cases k with
    | zero =>
        have hk_pos : 1 ≤ 0 := (mem_Icc.mp hk).1
        omega
    | succ j =>
        simp [rsgfPrefixIterate, rsgfPrefixIterate0, rsgfStep_def]
  · intro ζ
    simp [SOptLib.oracleEstimatorError]
  · exact (hprefix_oracle ⟨k, hk⟩).1
  · exact (hprefix_oracle ⟨k, hk⟩).2
  · exact (hprefix_budget ⟨k, hk⟩).1
  · exact
      rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
        S hk (hprefix_oracle ⟨k, hk⟩).1 (hprefix_oracle ⟨k, hk⟩).2
        (hprefix_budget ⟨k, hk⟩).2
        (by
          intro ζ
          simpa using horacle_gap_bound ⟨k, hk⟩ ζ)
  · exact hresidual_inner_int

/-- Integrated terminal one-step squared-distance identity under the finite
prefix law.  Unlike `rsgf_prefix_step_sq_distance_integral_identity_residual`,
the next iterate is expressed as `rsgfPrefixIterate0 ... k`, so the identity
also covers the final update `k = N` needed by the source finite sum. -/
private theorem rsgf_prefix_terminal_sq_distance_integral_identity_residual
    (S : Setup n Sample) {N k : ℕ}
    (hk : k ∈ Icc 1 N)
    (xStar : Space n)
    (hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - xStar‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N))
    (hresidual_inner_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N))
    (horacle_gap_bound :
      ∀ (R : RsgfOutputIndex N) (ζ : RsgfSamplePrefix n Sample N),
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ R) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ R) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 - xStar‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N)) =
      (∫ ζ : RsgfSamplePrefix n Sample N,
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N)) -
        2 * S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
            ∂(rsgfPrefixLaw S N)) -
        2 * S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
            ∂(rsgfPrefixLaw S N)) +
        S.γ k ^ (2 : ℕ) *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) := by
  classical
  have hprefix_oracle :=
    rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
  have hX :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩)
        (rsgfPrefixLaw S N) := (hprefix_oracle ⟨k, hk⟩).1
  have hG_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2)
        (rsgfPrefixLaw S N) := (hprefix_oracle ⟨k, hk⟩).2
  have hdist_cur :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) := (hprefix_budget ⟨k, hk⟩).1
  have hgap_cur :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
        (rsgfPrefixLaw S N) := (hprefix_budget ⟨k, hk⟩).2
  have horacle_sq :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ))
        (rsgfPrefixLaw S N) :=
    rsgf_prefix_oracle_norm_sq_integrable_of_gap_integrable
      S hk hX hG_aesm hgap_cur
      (by
        intro ζ
        simpa using horacle_gap_bound ⟨k, hk⟩ ζ)
  have hdisp_aesm :
      AEStronglyMeasurable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar)
        (rsgfPrefixLaw S N) :=
    hX.sub aestronglyMeasurable_const
  have horacle_inner_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N) :=
    integrable_inner_of_integrable_sq_norm
      hG_aesm hdisp_aesm horacle_sq hdist_cur
  have hgrad_inner_int :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N) := by
    refine (horacle_inner_int.sub hresidual_inner_int).congr
      (Filter.Eventually.of_forall ?_)
    intro ζ
    change
      ⟪rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
        rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ =
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
    simp [SOptLib.oracleEstimatorError, inner_sub_left]
  have hpoint :
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ‖rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 - xStar‖ ^ (2 : ℕ)) =ᵐ[
          rsgfPrefixLaw S N]
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
          2 * S.γ k *
            ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
          2 * S.γ k *
            ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
          S.γ k ^ (2 : ℕ) *
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)) :=
    Filter.Eventually.of_forall fun ζ =>
      rsgf_prefix_step_sq_distance_identity_residual_terminal S hk xStar ζ
  calc
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 - xStar‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N))
        =
      ∫ ζ : RsgfSamplePrefix n Sample N,
        ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ) -
          2 * S.γ k *
            ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ -
          2 * S.γ k *
            ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ +
          S.γ k ^ (2 : ℕ) *
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
        ∂(rsgfPrefixLaw S N) := by
          exact integral_congr_ae hpoint
    _ =
      (∫ ζ : RsgfSamplePrefix n Sample N,
          ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N)) -
        2 * S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
            ∂(rsgfPrefixLaw S N)) -
        2 * S.γ k *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
            ∂(rsgfPrefixLaw S N)) +
        S.γ k ^ (2 : ℕ) *
          (∫ ζ : RsgfSamplePrefix n Sample N,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
            ∂(rsgfPrefixLaw S N)) := by
          exact
            integral_sub_sub_add_const_mul
              (μ := rsgfPrefixLaw S N)
              (a := fun ζ : RsgfSamplePrefix n Sample N =>
                ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ))
              (b := fun ζ : RsgfSamplePrefix n Sample N =>
                ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                  rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
              (c := fun ζ : RsgfSamplePrefix n Sample N =>
                ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                    (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                  rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
              (d := fun ζ : RsgfSamplePrefix n Sample N =>
                ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                    (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ))
              (α := 2 * S.γ k) (β := 2 * S.γ k)
              (δ := S.γ k ^ (2 : ℕ))
              hdist_cur hgrad_inner_int hresidual_inner_int horacle_sq

/-- The selected RSGF output expectation expands to the normalized finite
weighted sum of prefix-law expectations. -/
private theorem rsgf_selected_expectation_eq_weighted_prefix_sum
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hgap_int :
      ∀ R : RsgfOutputIndex N,
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ R) - fStar S)
          (rsgfPrefixLaw S N)) :
    rsgfSelectedJointExpectation S N hPR
        (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) =
      (rsgfWeightDenominator S N)⁻¹ *
        Finset.sum (Icc 1 N)
          (fun k =>
            rsgfWeightNumerator S k *
              ∫ ζ : RsgfSamplePrefix n Sample N,
                (if hk : k ∈ Icc 1 N then
                  objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                else
                  0) ∂(rsgfPrefixLaw S N)) := by
  classical
  let x : ℕ → RsgfSamplePrefix n Sample N → ℝ := fun k ζ =>
    if hk : k ∈ Icc 1 N then
      objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
    else
      0
  have hα_nonneg :
      ∀ k, k ∈ Icc 1 N → 0 ≤ rsgfWeightNumerator S k :=
    SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR
  have hden :
      0 < Finset.sum (Icc 1 N) (fun k => rsgfWeightNumerator S k) :=
    SOptLib.FiniteWindowWeightsAdmissible.sum_pos hPR
  have hgap_int' :
      ∀ R : {k : ℕ // k ∈ Icc 1 N},
        Integrable (fun ζ : RsgfSamplePrefix n Sample N => (fun y : ℝ => y) (x R.1 ζ))
          (rsgfPrefixLaw S N) := by
    intro R
    have hR : 1 ≤ R.1 ∧ R.1 ≤ N := by
      exact mem_Icc.mp R.2
    simpa [x, hR] using hgap_int R
  haveI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    unfold rsgfZetaLaw
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : SFinite (rsgfPrefixLaw S N) := inferInstance
  have hsel :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := Icc 1 N) (α := fun k => rsgfWeightNumerator S k)
      (P := rsgfPrefixLaw S N) (x := x) (gap := fun y : ℝ => y)
      hα_nonneg hden hgap_int'
  have hleft :
      rsgfSelectedJointExpectation S N hPR
          (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) =
        ∫ q : RsgfOutputIndex N × RsgfSamplePrefix n Sample N,
          (fun y : ℝ => y) (x q.1.1 q.2) ∂(rsgfSelectedRunLaw S N hPR) := by
    unfold rsgfSelectedJointExpectation
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro q
    have hq : 1 ≤ q.1.1 ∧ q.1.1 ≤ N := by
      exact mem_Icc.mp q.1.2
    simp [x, hq]
  calc
    rsgfSelectedJointExpectation S N hPR
        (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S)
        = ∫ q : RsgfOutputIndex N × RsgfSamplePrefix n Sample N,
            (fun y : ℝ => y) (x q.1.1 q.2) ∂(rsgfSelectedRunLaw S N hPR) := hleft
    _ = (rsgfWeightDenominator S N)⁻¹ *
        Finset.sum (Icc 1 N)
          (fun k =>
            rsgfWeightNumerator S k *
              ∫ ζ : RsgfSamplePrefix n Sample N,
                (if hk : k ∈ Icc 1 N then
                  objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                else
                  0) ∂(rsgfPrefixLaw S N)) := by
      simpa [rsgfSelectedRunLaw, rsgfOutputPMF, rsgfWeightDenominator, x] using hsel

/-- The selected RSGF gradient-norm expectation expands to the normalized
finite weighted sum of prefix-law gradient-norm expectations. -/
private theorem rsgf_selected_gradient_expectation_eq_weighted_prefix_sum
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hgrad_int :
      ∀ R : RsgfOutputIndex N,
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N)) :
    rsgfSelectedJointExpectation S N hPR
        (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) =
      (rsgfWeightDenominator S N)⁻¹ *
        Finset.sum (Icc 1 N)
          (fun k =>
            rsgfWeightNumerator S k *
              ∫ ζ : RsgfSamplePrefix n Sample N,
                (if hk : k ∈ Icc 1 N then
                  ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
                else
                  0) ∂(rsgfPrefixLaw S N)) := by
  classical
  let x : ℕ → RsgfSamplePrefix n Sample N → ℝ := fun k ζ =>
    if hk : k ∈ Icc 1 N then
      ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
    else
      0
  have hα_nonneg :
      ∀ k, k ∈ Icc 1 N → 0 ≤ rsgfWeightNumerator S k :=
    SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR
  have hden :
      0 < Finset.sum (Icc 1 N) (fun k => rsgfWeightNumerator S k) :=
    SOptLib.FiniteWindowWeightsAdmissible.sum_pos hPR
  have hgrad_int' :
      ∀ R : {k : ℕ // k ∈ Icc 1 N},
        Integrable (fun ζ : RsgfSamplePrefix n Sample N => (fun y : ℝ => y) (x R.1 ζ))
          (rsgfPrefixLaw S N) := by
    intro R
    have hR : 1 ≤ R.1 ∧ R.1 ≤ N := by
      exact mem_Icc.mp R.2
    simpa [x, hR] using hgrad_int R
  haveI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    unfold rsgfZetaLaw
    infer_instance
  haveI : ∀ _ : RsgfOutputIndex N, IsFiniteMeasure (rsgfZetaLaw S) := fun _ =>
    inferInstance
  haveI : IsFiniteMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : SFinite (rsgfPrefixLaw S N) := inferInstance
  have hsel :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := Icc 1 N) (α := fun k => rsgfWeightNumerator S k)
      (P := rsgfPrefixLaw S N) (x := x) (gap := fun y : ℝ => y)
      hα_nonneg hden hgrad_int'
  have hleft :
      rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) =
        ∫ q : RsgfOutputIndex N × RsgfSamplePrefix n Sample N,
          (fun y : ℝ => y) (x q.1.1 q.2) ∂(rsgfSelectedRunLaw S N hPR) := by
    unfold rsgfSelectedJointExpectation
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro q
    have hq : 1 ≤ q.1.1 ∧ q.1.1 ≤ N := by
      exact mem_Icc.mp q.1.2
    simp [x, hq]
  calc
    rsgfSelectedJointExpectation S N hPR
        (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
        = ∫ q : RsgfOutputIndex N × RsgfSamplePrefix n Sample N,
            (fun y : ℝ => y) (x q.1.1 q.2) ∂(rsgfSelectedRunLaw S N hPR) := hleft
    _ = (rsgfWeightDenominator S N)⁻¹ *
        Finset.sum (Icc 1 N)
          (fun k =>
            rsgfWeightNumerator S k *
              ∫ ζ : RsgfSamplePrefix n Sample N,
                (if hk : k ∈ Icc 1 N then
                  ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
                else
                  0) ∂(rsgfPrefixLaw S N)) := by
      simpa [rsgfSelectedRunLaw, rsgfOutputPMF, rsgfWeightDenominator, x] using hsel

/-- Scalar normalization step: once the weighted prefix objective-gap numerator
is bounded, the selected-output expectation has the displayed denominator. -/
private theorem rsgf_selected_expectation_le_of_weighted_gap_sum
    (S : Setup n Sample) (N : ℕ) (xStar : Space n)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hselected :
      rsgfSelectedJointExpectation S N hPR
          (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) =
        (rsgfWeightDenominator S N)⁻¹ *
          Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                  else
                    0) ∂(rsgfPrefixLaw S N)))
    (hweighted :
      2 *
          Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                  else
                    0) ∂(rsgfPrefixLaw S N)) ≤
        convexRsgfBoundNumerator S N xStar) :
    rsgfSelectedJointExpectation S N hPR
        (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) ≤
      convexRsgfBoundNumerator S N xStar /
        (2 * rsgfWeightDenominator S N) := by
  let A : ℝ :=
    Finset.sum (Icc 1 N)
      (fun k =>
        rsgfWeightNumerator S k *
          ∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk : k ∈ Icc 1 N then
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
            else
              0) ∂(rsgfPrefixLaw S N))
  let W : ℝ := rsgfWeightDenominator S N
  let C : ℝ := convexRsgfBoundNumerator S N xStar
  have hW_pos : 0 < W := by
    simpa [W] using rsgfWeightDenominator_pos S hPR
  have h2W_pos : 0 < 2 * W := mul_pos (by norm_num) hW_pos
  have hdiv : (2 * A) / (2 * W) ≤ C / (2 * W) := by
    exact div_le_div_of_nonneg_right (by simpa [A, C] using hweighted) h2W_pos.le
  calc
    rsgfSelectedJointExpectation S N hPR
        (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S)
        = W⁻¹ * A := by simpa [A, W] using hselected
    _ = (2 * A) / (2 * W) := by
      field_simp [ne_of_gt hW_pos]
    _ ≤ C / (2 * W) := hdiv
    _ = convexRsgfBoundNumerator S N xStar /
        (2 * rsgfWeightDenominator S N) := by
      simp [C, W]

/-- Scalar normalization for the nonconvex selected gradient bound.  After the
selected-output expansion has identified the selected expectation with the
weighted prefix sum divided by the positive denominator, this transports the
source-level weighted prefix bound to Theorem 6.3(a)'s displayed ratio. -/
private theorem rsgf_selected_gradient_expectation_le_of_weighted_prefix_sum
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hselected :
      rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) =
        (rsgfWeightDenominator S N)⁻¹ *
          Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂(rsgfPrefixLaw S N)))
    (hweighted :
      (1 / S.L) *
          Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂(rsgfPrefixLaw S N)) ≤
        nonconvexRsgfBoundNumerator S N) :
    (1 / S.L) *
        rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) ≤
      nonconvexRsgfBoundNumerator S N /
        rsgfWeightDenominator S N := by
  let A : ℝ :=
    Finset.sum (Icc 1 N)
      (fun k =>
        rsgfWeightNumerator S k *
          ∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk : k ∈ Icc 1 N then
              ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
            else
              0) ∂(rsgfPrefixLaw S N))
  let W : ℝ := rsgfWeightDenominator S N
  let C : ℝ := nonconvexRsgfBoundNumerator S N
  have hW_pos : 0 < W := by
    simpa [W] using rsgfWeightDenominator_pos S hPR
  have hdiv : ((1 / S.L) * A) / W ≤ C / W := by
    exact div_le_div_of_nonneg_right (by simpa [A, C] using hweighted) hW_pos.le
  calc
    (1 / S.L) *
        rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
        = (1 / S.L) * (W⁻¹ * A) := by
            rw [hselected]
    _ = ((1 / S.L) * A) / W := by
      field_simp [ne_of_gt hW_pos]
    _ ≤ C / W := hdiv
    _ = nonconvexRsgfBoundNumerator S N /
        rsgfWeightDenominator S N := by
      simp [C, W]

/-- Paper-facing nonconvex conclusion of Theorem 6.3(a), expressed with the
canonical generated iterates and joint output/prefix law.  The hypothesis `hPR`
is the source boundary that the displayed formula (6.1.61) is a probability
mass function; it prevents Lean's totalized real normalization from admitting
negative-weight schedules outside the paper object. -/
theorem theorem_6_3a_nonconvex
    (S : Setup n Sample) (N : ℕ)
    (hN : 1 ≤ N)
    (hγ_upper : ∀ k ∈ Icc 1 N, S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    (1 / S.L) *
        rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) ≤
      nonconvexRsgfBoundNumerator S N / rsgfWeightDenominator S N := by
  classical
  have horacle_gap_bound :
      ∀ (R : RsgfOutputIndex N) (ζ : RsgfSamplePrefix n Sample N),
        (∫ z : Sample × Space n,
            ‖rsgfOracle S (rsgfPrefixIterate S ζ R) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ R) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ) := by
    intro R ζ
    exact
      rsgfOracle_secondMoment_le_objective_gap_sigma S
        (rsgfPrefixIterate S ζ R)
  have hprefix_budget :
      ∀ R : RsgfOutputIndex N,
        Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ‖rsgfPrefixIterate S ζ R - S.x₁‖ ^ (2 : ℕ))
            (rsgfPrefixLaw S N) ∧
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N) :=
    rsgf_nonconvex_prefix_l2_gap_budget_induction
      S hN horacle_gap_bound
  have hgrad_int :
      ∀ R : RsgfOutputIndex N,
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
          (rsgfPrefixLaw S N) :=
    rsgf_nonconvex_prefix_gradient_norm_sq_integrable S hprefix_budget
  have hselected :=
    rsgf_selected_gradient_expectation_eq_weighted_prefix_sum S N hPR hgrad_int
  have hweighted :
      (1 / S.L) *
          Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂(rsgfPrefixLaw S N)) ≤
        nonconvexRsgfBoundNumerator S N := by
    have hresidual_smoothing_inner_int :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ)
            (rsgfPrefixLaw S N) := by
      intro k hk
      exact
        rsgf_residual_smoothing_grad_inner_integrable_from_prefix_l2_gap
          S hk hprefix_budget
    have hresidual_smoothing_cancel :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          (∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
              ∂rsgfPrefixLaw S N) = 0 := by
      intro k hk
      exact
        rsgf_prefix_residual_smoothing_grad_inner_integral_eq_zero_of_integrable
          S hk (hresidual_smoothing_inner_int k hk)
    have hsmoothed_descent_step :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          (∫ ζ : RsgfSamplePrefix n Sample N,
              gaussianSmoothing S
                (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2)
              ∂(rsgfPrefixLaw S N)) ≤
            (∫ ζ : RsgfSamplePrefix n Sample N,
                gaussianSmoothing S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                ∂(rsgfPrefixLaw S N)) -
              S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ‖∇ (gaussianSmoothing S)
                      (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                    (2 : ℕ)
                  ∂(rsgfPrefixLaw S N)) -
              S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                    ∇ (gaussianSmoothing S)
                      (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
                  ∂(rsgfPrefixLaw S N)) +
              (S.L / 2) * S.γ k ^ (2 : ℕ) *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                  ∂(rsgfPrefixLaw S N)) := by
      intro k hk
      exact rsgf_prefix_smoothing_descent_step_integral S hk hprefix_budget
    have hgamma_reverse :
        Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂rsgfPrefixLaw S N) ≤
          2 *
              Finset.sum (Icc 1 N)
                (fun k =>
                  S.γ k *
                    ∫ ζ : RsgfSamplePrefix n Sample N,
                      (if hk : k ∈ Icc 1 N then
                        ‖∇ (gaussianSmoothing S)
                            (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                          (2 : ℕ)
                      else
                        0) ∂rsgfPrefixLaw S N) +
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 3) ^ (3 : ℕ)) *
              Finset.sum (Icc 1 N) S.γ :=
      rsgf_gamma_weighted_original_grad_sq_sum_le_reverse_smoothing
        S N hγ_upper hPR hprefix_budget
    have hreverse_weighted :
        Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂rsgfPrefixLaw S N) ≤
          2 *
              Finset.sum (Icc 1 N)
                (fun k =>
                  rsgfWeightNumerator S k *
                    ∫ ζ : RsgfSamplePrefix n Sample N,
                      (if hk : k ∈ Icc 1 N then
                        ‖∇ (gaussianSmoothing S)
                            (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                          (2 : ℕ)
                      else
                        0) ∂rsgfPrefixLaw S N) +
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 3) ^ (3 : ℕ)) *
              Finset.sum (Icc 1 N) (fun k => rsgfWeightNumerator S k) :=
      rsgf_weighted_original_grad_sq_sum_le_reverse_smoothing
        S N hPR hprefix_budget
    have horacle_gradient_bound :
        Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                        (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                  else
                    0) ∂(rsgfPrefixLaw S N)) ≤
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) *
                (2 * ((n : ℝ) + 4) *
            ((∫ ζ : RsgfSamplePrefix n Sample N,
                        (if hk : k ∈ Icc 1 N then
                          ‖∇ (objective S)
                              (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                            (2 : ℕ)
                        else
                          0) ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) +
                  S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                    ((n : ℝ) + 6) ^ (3 : ℕ))) :=
      rsgf_nonconvex_gamma_sq_oracle_le_gradient_sigma_sum
        S N hprefix_budget hgrad_int
    let A : ℕ → ℝ := fun t =>
      if ht_pos : 1 ≤ t then
        if ht_le : t - 1 ≤ N then
          ∫ ζ : RsgfSamplePrefix n Sample N,
            gaussianSmoothing S (rsgfPrefixIterate0 S ζ (t - 1) ht_le)
            ∂(rsgfPrefixLaw S N)
        else
          0
      else
        0
    let smoothGradIntegral : ℕ → ℝ := fun k =>
      if hk : k ∈ Icc 1 N then
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ‖∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
            (2 : ℕ)
          ∂(rsgfPrefixLaw S N)
      else
        0
    let origGradIntegral : ℕ → ℝ := fun k =>
      if hk : k ∈ Icc 1 N then
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N)
      else
        0
    let residualSmoothIntegral : ℕ → ℝ := fun k =>
      if hk : k ∈ Icc 1 N then
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
          ∂(rsgfPrefixLaw S N)
      else
        0
    let oracleSqIntegral : ℕ → ℝ := fun k =>
      if hk : k ∈ Icc 1 N then
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N)
      else
        0
    have hsmoothed_descent_recursion :
        ∀ k, k ∈ Icc 1 N →
          A (k + 1) ≤
            A k - S.γ k * smoothGradIntegral k -
              S.γ k * residualSmoothIntegral k +
              (S.L / 2) * S.γ k ^ (2 : ℕ) * oracleSqIntegral k := by
      intro k hk
      have hk_upper : k ≤ N := (mem_Icc.mp hk).2
      have hk_pos : 1 ≤ k := (mem_Icc.mp hk).1
      have hk_succ_pos : 1 ≤ k + 1 := by omega
      have hA_succ :
          A (k + 1) =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              gaussianSmoothing S
                (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2)
              ∂(rsgfPrefixLaw S N) := by
        simp [A, hk_succ_pos, hk_upper]
      have hA_cur :
          A k =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              gaussianSmoothing S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              ∂(rsgfPrefixLaw S N) := by
        cases k with
        | zero =>
            omega
        | succ j =>
            have hj_le : j ≤ N := Nat.le_trans (Nat.le_succ j) hk_upper
            simp [A, rsgfPrefixIterate, hk_pos, hj_le]
      have hsmooth_eq :
          smoothGradIntegral k =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              ‖∇ (gaussianSmoothing S)
                  (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N) := by
        dsimp [smoothGradIntegral]
        rw [dif_pos hk]
      have hresidual_eq :
          residualSmoothIntegral k =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                ∇ (gaussianSmoothing S)
                  (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
              ∂(rsgfPrefixLaw S N) := by
        dsimp [residualSmoothIntegral]
        rw [dif_pos hk]
      have horacle_eq :
          oracleSqIntegral k =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N) := by
        dsimp [oracleSqIntegral]
        rw [dif_pos hk]
      calc
        A (k + 1)
            =
          (∫ ζ : RsgfSamplePrefix n Sample N,
              gaussianSmoothing S
                (rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2)
              ∂(rsgfPrefixLaw S N)) := hA_succ
        _ ≤
          (∫ ζ : RsgfSamplePrefix n Sample N,
              gaussianSmoothing S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              ∂(rsgfPrefixLaw S N)) -
            S.γ k *
              (∫ ζ : RsgfSamplePrefix n Sample N,
                ‖∇ (gaussianSmoothing S)
                    (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N)) -
            S.γ k *
              (∫ ζ : RsgfSamplePrefix n Sample N,
                ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                    (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                  ∇ (gaussianSmoothing S)
                    (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
                ∂(rsgfPrefixLaw S N)) +
            (S.L / 2) * S.γ k ^ (2 : ℕ) *
              (∫ ζ : RsgfSamplePrefix n Sample N,
                ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                    (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N)) := hsmoothed_descent_step k hk
        _ =
          A k - S.γ k * smoothGradIntegral k -
            S.γ k * residualSmoothIntegral k +
            (S.L / 2) * S.γ k ^ (2 : ℕ) * oracleSqIntegral k := by
              rw [hA_cur, hsmooth_eq, hresidual_eq, horacle_eq]
    have hresidual_smoothing_zero :
        ∀ k, k ∈ Icc 1 N → residualSmoothIntegral k = 0 := by
      intro k hk
      have hresidual_eq :
          residualSmoothIntegral k =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                ∇ (gaussianSmoothing S)
                  (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
              ∂(rsgfPrefixLaw S N) := by
        dsimp [residualSmoothIntegral]
        rw [dif_pos hk]
      rw [hresidual_eq, hresidual_smoothing_cancel k hk]
    have hsmoothed_descent_gamma_budget :
        2 * Finset.sum (Icc 1 N)
            (fun k => S.γ k * smoothGradIntegral k) ≤
          2 * A 1 - 2 * A (N + 1) +
            S.L * Finset.sum (Icc 1 N)
              (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) :=
      two_mul_sum_gamma_grad_le_of_descent_recursion
        A smoothGradIntegral residualSmoothIntegral oracleSqIntegral S.γ S.L
        N hN hsmoothed_descent_recursion hresidual_smoothing_zero
    haveI : IsProbabilityMeasure S.P := S.P_isProbability
    haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
      rw [gaussianDirectionLaw_def]
      infer_instance
    haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
      dsimp [rsgfZetaLaw]
      infer_instance
    haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
      unfold rsgfPrefixLaw
      infer_instance
    have hterminal_mem : N ∈ Icc 1 N := mem_Icc.mpr ⟨hN, le_rfl⟩
    have hterminal_smooth_int :
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            gaussianSmoothing S (rsgfPrefixIterate0 S ζ N le_rfl))
          (rsgfPrefixLaw S N) := by
      simpa using
        rsgf_prefix_terminal_gaussianSmoothing_integrable_from_prefix_l2_gap
          S hterminal_mem hprefix_budget
    have hA_one_int :
        A 1 =
          ∫ ζ : RsgfSamplePrefix n Sample N,
            gaussianSmoothing S S.x₁ ∂(rsgfPrefixLaw S N) := by
      simp [A, rsgfPrefixIterate0]
    have hA_terminal :
        A (N + 1) =
          ∫ ζ : RsgfSamplePrefix n Sample N,
            gaussianSmoothing S (rsgfPrefixIterate0 S ζ N le_rfl)
            ∂(rsgfPrefixLaw S N) := by
      have hNp : 1 ≤ N + 1 := by omega
      simp [A, hNp]
    have hendpoint_diff_le :
        A 1 - A (N + 1) ≤
          objective S S.x₁ - fStar S +
            S.μ ^ (2 : ℕ) * S.L * (n : ℝ) := by
      let C : ℝ :=
        objective S S.x₁ - fStar S + S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
      let terminal : RsgfSamplePrefix n Sample N → Space n := fun ζ =>
        rsgfPrefixIterate0 S ζ N le_rfl
      have hinit_int :
          Integrable
            (fun _ζ : RsgfSamplePrefix n Sample N =>
              gaussianSmoothing S S.x₁)
            (rsgfPrefixLaw S N) := integrable_const _
      have hdiff_int :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              gaussianSmoothing S S.x₁ - gaussianSmoothing S (terminal ζ))
            (rsgfPrefixLaw S N) := by
        exact hinit_int.sub (by simpa [terminal] using hterminal_smooth_int)
      have hmono :
          (∫ ζ : RsgfSamplePrefix n Sample N,
              gaussianSmoothing S S.x₁ - gaussianSmoothing S (terminal ζ)
              ∂(rsgfPrefixLaw S N)) ≤
            ∫ _ζ : RsgfSamplePrefix n Sample N, C ∂(rsgfPrefixLaw S N) := by
        refine integral_mono_ae hdiff_int (integrable_const C) ?_
        exact Filter.Eventually.of_forall fun ζ => by
          dsimp [C, terminal]
          exact
            gaussianSmoothing_initial_sub_terminal_le_gap_add_error
              S (rsgfPrefixIterate0 S ζ N le_rfl)
      have hdiff_eval :
          (∫ ζ : RsgfSamplePrefix n Sample N,
              gaussianSmoothing S S.x₁ - gaussianSmoothing S (terminal ζ)
              ∂(rsgfPrefixLaw S N)) =
            A 1 - A (N + 1) := by
        rw [integral_sub hinit_int hterminal_smooth_int]
        rw [← hA_one_int, ← hA_terminal]
      have hconst_eval :
          (∫ _ζ : RsgfSamplePrefix n Sample N, C ∂(rsgfPrefixLaw S N)) = C := by
        simp
      rw [hdiff_eval, hconst_eval] at hmono
      simpa [C] using hmono
    have hendpoint_budget :
        2 * A 1 - 2 * A (N + 1) ≤
          2 * (objective S S.x₁ - fStar S +
            S.μ ^ (2 : ℕ) * S.L * (n : ℝ)) := by
      nlinarith [hendpoint_diff_le]
    have hsmoothed_budget :
        2 * Finset.sum (Icc 1 N)
            (fun k => S.γ k * smoothGradIntegral k) ≤
          2 * (objective S S.x₁ - fStar S +
            S.μ ^ (2 : ℕ) * S.L * (n : ℝ)) +
            S.L * Finset.sum (Icc 1 N)
              (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) := by
      nlinarith [hsmoothed_descent_gamma_budget, hendpoint_budget]
    have horig_if_integral_eq :
        ∀ k, k ∈ Icc 1 N →
          (∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk : k ∈ Icc 1 N then
              ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
            else
              0) ∂(rsgfPrefixLaw S N)) =
            origGradIntegral k := by
      intro k hk
      dsimp [origGradIntegral]
      rw [dif_pos hk]
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro ζ
      simp [hk]
    have hsmooth_if_integral_eq :
        ∀ k, k ∈ Icc 1 N →
          (∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk : k ∈ Icc 1 N then
              ‖∇ (gaussianSmoothing S)
                  (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^ (2 : ℕ)
            else
              0) ∂(rsgfPrefixLaw S N)) =
            smoothGradIntegral k := by
      intro k hk
      dsimp [smoothGradIntegral]
      rw [dif_pos hk]
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro ζ
      simp [hk]
    have horacle_if_integral_eq :
        ∀ k, k ∈ Icc 1 N →
          (∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk : k ∈ Icc 1 N then
              ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
            else
              0) ∂(rsgfPrefixLaw S N)) =
            oracleSqIntegral k := by
      intro k hk
      dsimp [oracleSqIntegral]
      rw [dif_pos hk]
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro ζ
      simp [hk]
    have hgamma_reverse_scalar :
        Finset.sum (Icc 1 N) (fun k => S.γ k * origGradIntegral k) ≤
          2 * Finset.sum (Icc 1 N)
              (fun k => S.γ k * smoothGradIntegral k) +
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 3) ^ (3 : ℕ)) *
              Finset.sum (Icc 1 N) S.γ := by
      have hleft :
          Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k *
                  ∫ ζ : RsgfSamplePrefix n Sample N,
                    (if hk : k ∈ Icc 1 N then
                      ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                        (2 : ℕ)
                    else
                      0) ∂rsgfPrefixLaw S N) =
            Finset.sum (Icc 1 N) (fun k => S.γ k * origGradIntegral k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [horig_if_integral_eq k hk]
      have hright :
          Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k *
                  ∫ ζ : RsgfSamplePrefix n Sample N,
                    (if hk : k ∈ Icc 1 N then
                      ‖∇ (gaussianSmoothing S)
                          (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                        (2 : ℕ)
                    else
                      0) ∂rsgfPrefixLaw S N) =
            Finset.sum (Icc 1 N)
              (fun k => S.γ k * smoothGradIntegral k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [hsmooth_if_integral_eq k hk]
      rw [hleft, hright] at hgamma_reverse
      exact hgamma_reverse
    have horacle_gradient_scalar :
        Finset.sum (Icc 1 N)
            (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) ≤
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) *
                (2 * ((n : ℝ) + 4) *
                    (origGradIntegral k + S.σ ^ (2 : ℕ)) +
                  S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                    ((n : ℝ) + 6) ^ (3 : ℕ))) := by
      have hleft :
          Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k ^ (2 : ℕ) *
                  ∫ ζ : RsgfSamplePrefix n Sample N,
                    (if hk : k ∈ Icc 1 N then
                      ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                          (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                    else
                      0) ∂(rsgfPrefixLaw S N)) =
            Finset.sum (Icc 1 N)
              (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [horacle_if_integral_eq k hk]
      have hright :
          Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k ^ (2 : ℕ) *
                  (2 * ((n : ℝ) + 4) *
                      ((∫ ζ : RsgfSamplePrefix n Sample N,
                          (if hk : k ∈ Icc 1 N then
                            ‖∇ (objective S)
                                (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                              (2 : ℕ)
                          else
                            0) ∂(rsgfPrefixLaw S N)) + S.σ ^ (2 : ℕ)) +
                    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                      ((n : ℝ) + 6) ^ (3 : ℕ))) =
            Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k ^ (2 : ℕ) *
                  (2 * ((n : ℝ) + 4) *
                      (origGradIntegral k + S.σ ^ (2 : ℕ)) +
                    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                      ((n : ℝ) + 6) ^ (3 : ℕ))) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [horig_if_integral_eq k hk]
      rw [hleft, hright] at horacle_gradient_bound
      exact horacle_gradient_bound
    let B₃ : ℝ :=
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 3) ^ (3 : ℕ)
    let B₆ : ℝ :=
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ)
    let C : ℝ := 2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) + B₆
    have horacle_gradient_expanded :
        Finset.sum (Icc 1 N)
            (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) ≤
          2 * ((n : ℝ) + 4) *
              Finset.sum (Icc 1 N)
                (fun k => S.γ k ^ (2 : ℕ) * origGradIntegral k) +
            C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
      have hsplit :
          Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k ^ (2 : ℕ) *
                  (2 * ((n : ℝ) + 4) *
                      (origGradIntegral k + S.σ ^ (2 : ℕ)) +
                    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                      ((n : ℝ) + 6) ^ (3 : ℕ))) =
            2 * ((n : ℝ) + 4) *
                Finset.sum (Icc 1 N)
                  (fun k => S.γ k ^ (2 : ℕ) * origGradIntegral k) +
              C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
        calc
          Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k ^ (2 : ℕ) *
                  (2 * ((n : ℝ) + 4) *
                      (origGradIntegral k + S.σ ^ (2 : ℕ)) +
                    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                      ((n : ℝ) + 6) ^ (3 : ℕ))) =
            Finset.sum (Icc 1 N)
              (fun k =>
                2 * ((n : ℝ) + 4) *
                    (S.γ k ^ (2 : ℕ) * origGradIntegral k) +
                  C * S.γ k ^ (2 : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              dsimp [C, B₆]
              ring
          _ =
            2 * ((n : ℝ) + 4) *
                Finset.sum (Icc 1 N)
                  (fun k => S.γ k ^ (2 : ℕ) * origGradIntegral k) +
              C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      rw [hsplit] at horacle_gradient_scalar
      exact horacle_gradient_scalar
    have hsmoothed_orig_budget :
        Finset.sum (Icc 1 N) (fun k => S.γ k * origGradIntegral k) ≤
          2 * (objective S S.x₁ - fStar S +
            S.μ ^ (2 : ℕ) * S.L * (n : ℝ)) +
            S.L * (2 * ((n : ℝ) + 4) *
              Finset.sum (Icc 1 N)
                (fun k => S.γ k ^ (2 : ℕ) * origGradIntegral k) +
              C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ))) +
            B₃ * Finset.sum (Icc 1 N) S.γ := by
      have hL_oracle :=
        mul_le_mul_of_nonneg_left horacle_gradient_expanded (le_of_lt S.L_pos)
      have hgamma_reverse_scalar_B₃ :
          Finset.sum (Icc 1 N) (fun k => S.γ k * origGradIntegral k) ≤
            2 * Finset.sum (Icc 1 N)
                (fun k => S.γ k * smoothGradIntegral k) +
              B₃ * Finset.sum (Icc 1 N) S.γ := by
        simpa [B₃] using hgamma_reverse_scalar
      nlinarith [hgamma_reverse_scalar_B₃, hsmoothed_budget, hL_oracle]
    have hweighted_sum_eq :
        Finset.sum (Icc 1 N)
            (fun k => rsgfWeightNumerator S k * origGradIntegral k) =
          Finset.sum (Icc 1 N) (fun k => S.γ k * origGradIntegral k) -
            2 * S.L * ((n : ℝ) + 4) *
              Finset.sum (Icc 1 N)
                (fun k => S.γ k ^ (2 : ℕ) * origGradIntegral k) := by
      calc
        Finset.sum (Icc 1 N)
            (fun k => rsgfWeightNumerator S k * origGradIntegral k) =
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k * origGradIntegral k -
                (2 * S.L * ((n : ℝ) + 4)) *
                  (S.γ k ^ (2 : ℕ) * origGradIntegral k)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            dsimp [rsgfWeightNumerator]
            ring
        _ =
          Finset.sum (Icc 1 N) (fun k => S.γ k * origGradIntegral k) -
            2 * S.L * ((n : ℝ) + 4) *
              Finset.sum (Icc 1 N)
                (fun k => S.γ k ^ (2 : ℕ) * origGradIntegral k) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
    have hweighted_raw :
        Finset.sum (Icc 1 N)
            (fun k => rsgfWeightNumerator S k * origGradIntegral k) ≤
          2 * (objective S S.x₁ - fStar S +
            S.μ ^ (2 : ℕ) * S.L * (n : ℝ)) +
            S.L * C *
              Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
            B₃ * Finset.sum (Icc 1 N) S.γ := by
      rw [hweighted_sum_eq]
      nlinarith [hsmoothed_orig_budget]
    have hweighted_inline_eq :
        Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂(rsgfPrefixLaw S N)) =
          Finset.sum (Icc 1 N)
            (fun k => rsgfWeightNumerator S k * origGradIntegral k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      rw [horig_if_integral_eq k hk]
    have hweighted_inline_raw :
        Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                      (2 : ℕ)
                  else
                    0) ∂(rsgfPrefixLaw S N)) ≤
          2 * (objective S S.x₁ - fStar S +
            S.μ ^ (2 : ℕ) * S.L * (n : ℝ)) +
            S.L * C *
              Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
            B₃ * Finset.sum (Icc 1 N) S.γ := by
      rw [hweighted_inline_eq]
      exact hweighted_raw
    let rawBound : ℝ :=
      2 * (objective S S.x₁ - fStar S +
        S.μ ^ (2 : ℕ) * S.L * (n : ℝ)) +
        S.L * C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
        B₃ * Finset.sum (Icc 1 N) S.γ
    have hdiv_raw :
        (1 / S.L) *
            Finset.sum (Icc 1 N)
              (fun k =>
                rsgfWeightNumerator S k *
                  ∫ ζ : RsgfSamplePrefix n Sample N,
                    (if hk : k ∈ Icc 1 N then
                      ‖∇ (objective S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)‖ ^
                        (2 : ℕ)
                    else
                      0) ∂(rsgfPrefixLaw S N)) ≤
          (1 / S.L) * rawBound := by
      have hscale_nonneg : 0 ≤ 1 / S.L :=
        le_of_lt (one_div_pos.mpr S.L_pos)
      dsimp [rawBound]
      exact mul_le_mul_of_nonneg_left hweighted_inline_raw hscale_nonneg
    have hγ_nonneg :
        ∀ k, k ∈ Icc 1 N → 0 ≤ S.γ k := by
      intro k hk
      exact
        rsgf_stepsize_nonneg_of_weight_nonneg_of_upper
          S hk
          (SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR k hk)
          (hγ_upper k hk)
    have hsumγ_nonneg :
        0 ≤ Finset.sum (Icc 1 N) S.γ :=
      Finset.sum_nonneg hγ_nonneg
    have hsumγsq_nonneg :
        0 ≤ Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) :=
      Finset.sum_nonneg fun k hk => sq_nonneg (S.γ k)
    have hraw_div_eval :
        (1 / S.L) * rawBound =
          2 * (objective S S.x₁ - fStar S) / S.L +
            (2 * S.μ ^ (2 : ℕ) * (n : ℝ) +
              C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
              (S.μ ^ (2 : ℕ) * S.L / 2 *
                ((n : ℝ) + 3) ^ (3 : ℕ)) *
                Finset.sum (Icc 1 N) S.γ) := by
      dsimp [rawBound, B₃]
      field_simp [ne_of_gt S.L_pos]
      ring
    have hsum_split :
        Finset.sum (Icc 1 N)
            (fun k => S.γ k / 4 + S.L * S.γ k ^ (2 : ℕ)) =
          (1 / 4) * Finset.sum (Icc 1 N) S.γ +
            S.L * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
      have hdiv_sum :
          Finset.sum (Icc 1 N) (fun k => S.γ k / 4) =
            (1 / 4) * Finset.sum (Icc 1 N) S.γ := by
        calc
          Finset.sum (Icc 1 N) (fun k => S.γ k / 4) =
            Finset.sum (Icc 1 N) (fun k => S.γ k * (1 / 4)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
          _ = Finset.sum (Icc 1 N) S.γ * (1 / 4) := by
              rw [Finset.sum_mul]
          _ = (1 / 4) * Finset.sum (Icc 1 N) S.γ := by
              ring
      have hL_sum :
          Finset.sum (Icc 1 N) (fun k => S.L * S.γ k ^ (2 : ℕ)) =
            S.L * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
        rw [Finset.mul_sum]
      rw [Finset.sum_add_distrib, hdiv_sum, hL_sum]
    have hnum_expand :
        nonconvexRsgfBoundNumerator S N =
          2 * (objective S S.x₁ - fStar S) / S.L +
            (2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) +
              (2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                  ((n : ℝ) + 4) ^ (3 : ℕ) +
                2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) *
                Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
              (S.μ ^ (2 : ℕ) * S.L / 2 *
                ((n : ℝ) + 4) ^ (3 : ℕ)) *
                Finset.sum (Icc 1 N) S.γ) := by
      unfold nonconvexRsgfBoundNumerator
      rw [Df_sq_eq, hsum_split]
      ring
    have hlinear_coeff :
        2 * S.μ ^ (2 : ℕ) * (n : ℝ) ≤
          2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) := by
      have hn_le : (n : ℝ) ≤ (n : ℝ) + 4 :=
        le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 4)
      have hscale_nonneg : 0 ≤ 2 * S.μ ^ (2 : ℕ) := by positivity
      exact mul_le_mul_of_nonneg_left hn_le hscale_nonneg
    have hcube3 :
        ((n : ℝ) + 3) ^ (3 : ℕ) ≤ ((n : ℝ) + 4) ^ (3 : ℕ) := by
      have hbase_nonneg : 0 ≤ (n : ℝ) + 3 := by
        exact add_nonneg (Nat.cast_nonneg n) (by norm_num)
      have hbase_le : (n : ℝ) + 3 ≤ (n : ℝ) + 4 := by norm_num
      exact pow_le_pow_left₀ hbase_nonneg hbase_le 3
    have hgamma_coeff :
        S.μ ^ (2 : ℕ) * S.L / 2 * ((n : ℝ) + 3) ^ (3 : ℕ) ≤
          S.μ ^ (2 : ℕ) * S.L / 2 * ((n : ℝ) + 4) ^ (3 : ℕ) := by
      have hscale_nonneg : 0 ≤ S.μ ^ (2 : ℕ) * S.L / 2 :=
        div_nonneg
          (mul_nonneg (sq_nonneg S.μ) (le_of_lt S.L_pos))
          (by norm_num)
      exact mul_le_mul_of_nonneg_left hcube3 hscale_nonneg
    have hgamma_budget :
        (S.μ ^ (2 : ℕ) * S.L / 2 *
            ((n : ℝ) + 3) ^ (3 : ℕ)) *
            Finset.sum (Icc 1 N) S.γ ≤
          (S.μ ^ (2 : ℕ) * S.L / 2 *
            ((n : ℝ) + 4) ^ (3 : ℕ)) *
            Finset.sum (Icc 1 N) S.γ :=
      mul_le_mul_of_nonneg_right hgamma_coeff hsumγ_nonneg
    have hcube6 :
        ((n : ℝ) + 6) ^ (3 : ℕ) ≤
          4 * ((n : ℝ) + 4) ^ (3 : ℕ) := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have hn_sq_nonneg : 0 ≤ (n : ℝ) ^ (2 : ℕ) := sq_nonneg (n : ℝ)
      have hn_cube_nonneg : 0 ≤ (n : ℝ) ^ (3 : ℕ) :=
        pow_nonneg hn_nonneg 3
      have hdiff_nonneg :
          0 ≤
            3 * (n : ℝ) ^ (3 : ℕ) +
              30 * (n : ℝ) ^ (2 : ℕ) + 84 * (n : ℝ) + 40 := by
        nlinarith only [hn_nonneg, hn_sq_nonneg, hn_cube_nonneg]
      have hpoly :
          4 * ((n : ℝ) + 4) ^ (3 : ℕ) -
              ((n : ℝ) + 6) ^ (3 : ℕ) =
            3 * (n : ℝ) ^ (3 : ℕ) +
              30 * (n : ℝ) ^ (2 : ℕ) + 84 * (n : ℝ) + 40 := by
        ring
      nlinarith only [hdiff_nonneg, hpoly]
    have hquad_coeff :
        C ≤
          2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) := by
      have hscale_nonneg :
          0 ≤ S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 := by positivity
      have hmul :=
        mul_le_mul_of_nonneg_left hcube6 hscale_nonneg
      have hmul' :
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ) ≤
            2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) := by
        calc
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ) ≤
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              (4 * ((n : ℝ) + 4) ^ (3 : ℕ)) := hmul
          _ =
            2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) := by
              ring
      dsimp [C, B₆]
      linarith
    have hquad_budget :
        C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) ≤
          (2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) *
            Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hquad_coeff hsumγsq_nonneg
    have hraw_to_num :
        (1 / S.L) * rawBound ≤ nonconvexRsgfBoundNumerator S N := by
      have htail :
          (2 * S.μ ^ (2 : ℕ) * (n : ℝ) +
              C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
              (S.μ ^ (2 : ℕ) * S.L / 2 *
                ((n : ℝ) + 3) ^ (3 : ℕ)) *
                Finset.sum (Icc 1 N) S.γ) ≤
            (2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) +
              (2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                  ((n : ℝ) + 4) ^ (3 : ℕ) +
                2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) *
                Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
              (S.μ ^ (2 : ℕ) * S.L / 2 *
                ((n : ℝ) + 4) ^ (3 : ℕ)) *
                Finset.sum (Icc 1 N) S.γ) := by
        have hlin_quad :
            2 * S.μ ^ (2 : ℕ) * (n : ℝ) +
                C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) ≤
              2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) +
                (2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                    ((n : ℝ) + 4) ^ (3 : ℕ) +
                  2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) *
                  Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) :=
          add_le_add hlinear_coeff hquad_budget
        exact add_le_add hlin_quad hgamma_budget
      calc
        (1 / S.L) * rawBound =
          2 * (objective S S.x₁ - fStar S) / S.L +
            (2 * S.μ ^ (2 : ℕ) * (n : ℝ) +
              C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
              (S.μ ^ (2 : ℕ) * S.L / 2 *
                ((n : ℝ) + 3) ^ (3 : ℕ)) *
                Finset.sum (Icc 1 N) S.γ) := hraw_div_eval
        _ ≤
          2 * (objective S S.x₁ - fStar S) / S.L +
            (2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) +
              (2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                  ((n : ℝ) + 4) ^ (3 : ℕ) +
                2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) *
                Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) +
              (S.μ ^ (2 : ℕ) * S.L / 2 *
                ((n : ℝ) + 4) ^ (3 : ℕ)) *
                Finset.sum (Icc 1 N) S.γ) :=
            add_le_add le_rfl htail
        _ = nonconvexRsgfBoundNumerator S N := by
            exact hnum_expand.symm
    exact le_trans hdiv_raw hraw_to_num
  exact
    rsgf_selected_gradient_expectation_le_of_weighted_prefix_sum
      S N hPR hselected hweighted

/-- Paper-facing convex conclusion of Theorem 6.3(b), expressed with the canonical
generated iterates and joint output/prefix law.  The hypothesis `hPR` is the
source boundary that the displayed formula (6.1.61) is a probability mass
function; it prevents Lean's totalized real normalization from admitting
negative-weight schedules outside the paper object. -/
theorem theorem_6_3b_convex
    (S : Setup n Sample) (N : ℕ)
    (xStar : Space n)
    (hN : 1 ≤ N)
    (hγ_upper : ∀ k ∈ Icc 1 N, S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hconvex : ConvexOn ℝ Set.univ (objective S))
    (hoptimal : ∀ x : Space n, objective S xStar ≤ objective S x) :
    rsgfSelectedJointExpectation S N hPR
        (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) ≤
      convexRsgfBoundNumerator S N xStar /
        (2 * rsgfWeightDenominator S N) := by
  classical
  have hgap_nonneg : ∀ x : Space n, 0 ≤ objective S x - fStar S := by
    intro x
    exact objective_gap_nonneg_of_global_optimal S xStar x hoptimal
  have hcore :
      (∀ R : RsgfOutputIndex N,
        Integrable
          (fun ζ : RsgfSamplePrefix n Sample N =>
            objective S (rsgfPrefixIterate S ζ R) - fStar S)
          (rsgfPrefixLaw S N)) ∧
      2 *
          Finset.sum (Icc 1 N)
            (fun k =>
              rsgfWeightNumerator S k *
                ∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                  else
                    0) ∂(rsgfPrefixLaw S N)) ≤
        convexRsgfBoundNumerator S N xStar := by
    have horacle_gap_bound :
        ∀ (R : RsgfOutputIndex N) (ζ : RsgfSamplePrefix n Sample N),
          (∫ z : Sample × Space n,
              ‖rsgfOracle S (rsgfPrefixIterate S ζ R) z.1 z.2‖ ^ (2 : ℕ)
                ∂(S.P.prod (gaussianDirectionLaw n))) ≤
            4 * ((n : ℝ) + 4) * S.L *
                (objective S (rsgfPrefixIterate S ζ R) - fStar S) +
              2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
              S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                ((n : ℝ) + 6) ^ (3 : ℕ) := by
      intro R ζ
      exact
        rsgfOracle_secondMoment_le_objective_gap_sigma S
          (rsgfPrefixIterate S ζ R)
    have hresidual_cancel_of_integrable :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
            (rsgfPrefixLaw S N) →
          (∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
              ∂rsgfPrefixLaw S N) = 0 := by
      intro k hk hΦ_int
      exact
        rsgf_prefix_residual_inner_prefix_integral_eq_zero_of_integrable
          S hk xStar hΦ_int
    have hprefix_budget :
        ∀ R : RsgfOutputIndex N,
          Integrable
              (fun ζ : RsgfSamplePrefix n Sample N =>
                ‖rsgfPrefixIterate S ζ R - xStar‖ ^ (2 : ℕ))
              (rsgfPrefixLaw S N) ∧
            Integrable
              (fun ζ : RsgfSamplePrefix n Sample N =>
                objective S (rsgfPrefixIterate S ζ R) - fStar S)
              (rsgfPrefixLaw S N) :=
      rsgf_convex_prefix_l2_gap_budget_induction
        S hN xStar hoptimal horacle_gap_bound
    have hgap_int :
        ∀ R : RsgfOutputIndex N,
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ R) - fStar S)
            (rsgfPrefixLaw S N) := fun R => (hprefix_budget R).2
    have hresidual_inner_int :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
            (rsgfPrefixLaw S N) := by
      intro k hk
      exact
        rsgf_residual_inner_budget_from_prefix_l2_gap
          S hk xStar hprefix_budget
    have hresidual_cancel :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          (∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
              ∂rsgfPrefixLaw S N) = 0 := by
      intro k hk
      exact hresidual_cancel_of_integrable k hk (hresidual_inner_int k hk)
    have hstep_integral :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N) (hks : k + 1 ∈ Icc 1 N),
          (∫ ζ : RsgfSamplePrefix n Sample N,
              ‖rsgfPrefixIterate S ζ ⟨k + 1, hks⟩ - xStar‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) =
            (∫ ζ : RsgfSamplePrefix n Sample N,
                ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N)) -
              2 * S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                    rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                  ∂(rsgfPrefixLaw S N)) -
              2 * S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                    rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                  ∂(rsgfPrefixLaw S N)) +
              S.γ k ^ (2 : ℕ) *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                  ∂(rsgfPrefixLaw S N)) := by
      intro k hk hks
      exact
        rsgf_prefix_step_sq_distance_integral_identity_residual
          S hk hks xStar hprefix_budget (hresidual_inner_int k hk)
          horacle_gap_bound
    have hstep_terminal_integral :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          (∫ ζ : RsgfSamplePrefix n Sample N,
              ‖rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 - xStar‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N)) =
            (∫ ζ : RsgfSamplePrefix n Sample N,
                ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N)) -
              2 * S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                    rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                  ∂(rsgfPrefixLaw S N)) -
              2 * S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                    rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                  ∂(rsgfPrefixLaw S N)) +
              S.γ k ^ (2 : ℕ) *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                  ∂(rsgfPrefixLaw S N)) := by
      intro k hk
      exact
        rsgf_prefix_terminal_sq_distance_integral_identity_residual
          S hk xStar hprefix_budget (hresidual_inner_int k hk)
          horacle_gap_bound
    let distIntegral : ℕ → ℝ := fun t =>
      if ht_pos : 1 ≤ t then
        if ht_le : t - 1 ≤ N then
          ∫ ζ : RsgfSamplePrefix n Sample N,
            ‖rsgfPrefixIterate0 S ζ (t - 1) ht_le - xStar‖ ^ (2 : ℕ)
            ∂(rsgfPrefixLaw S N)
        else
          0
      else
        0
    let gradInnerIntegral : ℕ → ℝ := fun k =>
      if hk : k ∈ Icc 1 N then
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
          ∂(rsgfPrefixLaw S N)
      else
        0
    let residualInnerIntegral : ℕ → ℝ := fun k =>
      if hk : k ∈ Icc 1 N then
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
          ∂(rsgfPrefixLaw S N)
      else
        0
    let oracleSqIntegral : ℕ → ℝ := fun k =>
      if hk : k ∈ Icc 1 N then
        ∫ ζ : RsgfSamplePrefix n Sample N,
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
          ∂(rsgfPrefixLaw S N)
      else
        0
    have hterminal_recursion :
        distIntegral (N + 1) =
          distIntegral 1 -
            2 * Finset.sum (Icc 1 N)
              (fun k => S.γ k * gradInnerIntegral k) +
            Finset.sum (Icc 1 N)
              (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) := by
      refine
        sum_Icc_one_step_terminal_eq_of_residual_zero
          distIntegral gradInnerIntegral residualInnerIntegral oracleSqIntegral
          S.γ N hN ?_ ?_
      · intro k hk
        have hk_upper : k ≤ N := (mem_Icc.mp hk).2
        have hk_pos : 1 ≤ k := (mem_Icc.mp hk).1
        have hk_succ_pos : 1 ≤ k + 1 := by omega
        have hdist_succ :
            distIntegral (k + 1) =
              ∫ ζ : RsgfSamplePrefix n Sample N,
                ‖rsgfPrefixIterate0 S ζ k hk_upper - xStar‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N) := by
          simp [distIntegral, hk_succ_pos, hk_upper]
        have hdist_cur :
            distIntegral k =
              ∫ ζ : RsgfSamplePrefix n Sample N,
                ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N) := by
          cases k with
          | zero =>
              omega
          | succ j =>
              have hj_le : j ≤ N := Nat.le_trans (Nat.le_succ j) hk_upper
              simp [distIntegral, rsgfPrefixIterate, hk_pos, hj_le]
        calc
          distIntegral (k + 1)
              =
            (∫ ζ : RsgfSamplePrefix n Sample N,
                ‖rsgfPrefixIterate0 S ζ k (mem_Icc.mp hk).2 - xStar‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N)) := by
                simpa using hdist_succ
          _ =
            (∫ ζ : RsgfSamplePrefix n Sample N,
                ‖rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar‖ ^ (2 : ℕ)
                ∂(rsgfPrefixLaw S N)) -
              2 * S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                    rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                  ∂(rsgfPrefixLaw S N)) -
              2 * S.γ k *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                    rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                  ∂(rsgfPrefixLaw S N)) +
              S.γ k ^ (2 : ℕ) *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                      (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                  ∂(rsgfPrefixLaw S N)) := hstep_terminal_integral k hk
          _ =
            distIntegral k -
              2 * S.γ k * gradInnerIntegral k -
              2 * S.γ k * residualInnerIntegral k +
              S.γ k ^ (2 : ℕ) * oracleSqIntegral k := by
                have hgrad_eq :
                    gradInnerIntegral k =
                      ∫ ζ : RsgfSamplePrefix n Sample N,
                        ⟪∇ (gaussianSmoothing S)
                            (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                        ∂(rsgfPrefixLaw S N) := by
                  dsimp [gradInnerIntegral]
                  rw [dif_pos hk]
                have hres_eq :
                    residualInnerIntegral k =
                      ∫ ζ : RsgfSamplePrefix n Sample N,
                        ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                        ∂(rsgfPrefixLaw S N) := by
                  dsimp [residualInnerIntegral]
                  rw [dif_pos hk]
                have horacle_eq :
                    oracleSqIntegral k =
                      ∫ ζ : RsgfSamplePrefix n Sample N,
                        ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
                        ∂(rsgfPrefixLaw S N) := by
                  dsimp [oracleSqIntegral]
                  rw [dif_pos hk]
                rw [hdist_cur, hgrad_eq, hres_eq, horacle_eq]
      · intro k hk
        have hres_eq :
            residualInnerIntegral k =
              ∫ ζ : RsgfSamplePrefix n Sample N,
                ⟪(fun x ξ u => SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y) (rsgfOracle S x ξ u) x) (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                    (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                  rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
                ∂(rsgfPrefixLaw S N) := by
          dsimp [residualInnerIntegral]
          rw [dif_pos hk]
        rw [hres_eq, hresidual_cancel k hk]
    have hterminal_nonneg : 0 ≤ distIntegral (N + 1) := by
      have ht_pos : 1 ≤ N + 1 := by omega
      have ht_le : N ≤ N := le_rfl
      dsimp [distIntegral]
      rw [dif_pos ht_le]
      exact integral_nonneg fun ζ => by positivity
    have hterminal_grad_budget :
        2 * Finset.sum (Icc 1 N)
            (fun k => S.γ k * gradInnerIntegral k) ≤
          distIntegral 1 +
            Finset.sum (Icc 1 N)
              (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) :=
      two_mul_sum_gamma_grad_le_of_terminal_recursion_nonneg
        distIntegral gradInnerIntegral oracleSqIntegral S.γ N
        hterminal_recursion hterminal_nonneg
    have horacle_sq_weighted_budget_of_pointwise :
        (∀ k, k ∈ Icc 1 N →
          oracleSqIntegral k ≤
            4 * ((n : ℝ) + 4) * S.L *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                  else
                    0) ∂(rsgfPrefixLaw S N)) +
              (2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
                S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                  ((n : ℝ) + 6) ^ (3 : ℕ))) →
        Finset.sum (Icc 1 N)
            (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) ≤
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) *
                (4 * ((n : ℝ) + 4) * S.L *
                    (∫ ζ : RsgfSamplePrefix n Sample N,
                      (if hk : k ∈ Icc 1 N then
                        objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                      else
                        0) ∂(rsgfPrefixLaw S N)) +
                  (2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
                    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                      ((n : ℝ) + 6) ^ (3 : ℕ)))) := by
      intro hpoint
      exact
        sum_gamma_sq_oracle_le_gap_noise_of_pointwise
          S.γ oracleSqIntegral
          (fun k =>
            ∫ ζ : RsgfSamplePrefix n Sample N,
              (if hk : k ∈ Icc 1 N then
                objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
              else
                0) ∂(rsgfPrefixLaw S N))
          N (4 * ((n : ℝ) + 4) * S.L)
          (2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ))
          hpoint
    have horacle_sq_pointwise :
        ∀ k, k ∈ Icc 1 N →
          oracleSqIntegral k ≤
            4 * ((n : ℝ) + 4) * S.L *
                (∫ ζ : RsgfSamplePrefix n Sample N,
                  (if hk : k ∈ Icc 1 N then
                    objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                  else
                    0) ∂(rsgfPrefixLaw S N)) +
              (2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
                S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                  ((n : ℝ) + 6) ^ (3 : ℕ)) := by
      intro k hk
      have hprefix_oracle :=
        rsgfPrefixIterate_and_oracle_aestronglyMeasurable (N := N) S
      have hle :=
        rsgf_prefix_oracle_sq_integral_le_gap_integral
          S hk (hprefix_oracle ⟨k, hk⟩).1 (hprefix_oracle ⟨k, hk⟩).2
          (hgap_int ⟨k, hk⟩)
          (by
            intro ζ
            simpa using horacle_gap_bound ⟨k, hk⟩ ζ)
      have horacle_eq :
          oracleSqIntegral k =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ)
              ∂(rsgfPrefixLaw S N) := by
        dsimp [oracleSqIntegral]
        rw [dif_pos hk]
      have hgap_eq :
          (∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk' : k ∈ Icc 1 N then
              objective S (rsgfPrefixIterate S ζ ⟨k, hk'⟩) - fStar S
            else
              0) ∂(rsgfPrefixLaw S N)) =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
              ∂(rsgfPrefixLaw S N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro ζ
        simp [hk]
      rw [horacle_eq, hgap_eq]
      exact hle
    have horacle_sq_weighted_budget :
        Finset.sum (Icc 1 N)
            (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) ≤
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) *
                (4 * ((n : ℝ) + 4) * S.L *
                    (∫ ζ : RsgfSamplePrefix n Sample N,
                      (if hk : k ∈ Icc 1 N then
                        objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
                      else
                        0) ∂(rsgfPrefixLaw S N)) +
                  (2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
                    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
                      ((n : ℝ) + 6) ^ (3 : ℕ)))) :=
      horacle_sq_weighted_budget_of_pointwise horacle_sq_pointwise
    have hconvex_smoothing :
        ConvexOn ℝ Set.univ (gaussianSmoothing S) :=
      gaussianSmoothing_convexOn_of_objective_convex S hconvex
    have hgrad_gap_pointwise :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          ∀ ζ : RsgfSamplePrefix n Sample N,
            objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) -
                fStar S - S.μ ^ (2 : ℕ) * S.L * (n : ℝ) ≤
              ⟪∇ (gaussianSmoothing S)
                    (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ := by
      intro k hk ζ
      exact
        gaussianSmoothing_gradient_inner_ge_objective_gap_sub_error
          S xStar (rsgfPrefixIterate S ζ ⟨k, hk⟩)
          hconvex_smoothing hoptimal
    have hgrad_gap_integral :
        ∀ (k : ℕ) (hk : k ∈ Icc 1 N),
          (∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk' : k ∈ Icc 1 N then
              objective S (rsgfPrefixIterate S ζ ⟨k, hk'⟩) - fStar S
            else
              0) ∂(rsgfPrefixLaw S N)) -
              S.μ ^ (2 : ℕ) * S.L * (n : ℝ) ≤
            gradInnerIntegral k := by
      intro k hk
      letI : IsProbabilityMeasure S.P := S.P_isProbability
      haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
        rw [gaussianDirectionLaw_def]
        infer_instance
      haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
        dsimp [rsgfZetaLaw]
        infer_instance
      haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
        unfold rsgfPrefixLaw
        infer_instance
      have hgap_cur :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S)
            (rsgfPrefixLaw S N) := hgap_int ⟨k, hk⟩
      have hgrad_inner_int :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              ⟪∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
            (rsgfPrefixLaw S N) :=
        rsgf_prefix_grad_inner_integrable_from_prefix_l2_gap
          S hk xStar hprefix_budget (hresidual_inner_int k hk)
          horacle_gap_bound
      have hleft_int :
          Integrable
            (fun ζ : RsgfSamplePrefix n Sample N =>
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S -
                S.μ ^ (2 : ℕ) * S.L * (n : ℝ))
            (rsgfPrefixLaw S N) :=
        hgap_cur.sub (integrable_const _)
      have hmono :
          (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S -
                S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
              ∂(rsgfPrefixLaw S N)) ≤
            ∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪∇ (gaussianSmoothing S)
                  (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
              ∂(rsgfPrefixLaw S N) := by
        refine integral_mono_ae hleft_int hgrad_inner_int ?_
        exact Filter.Eventually.of_forall fun ζ => hgrad_gap_pointwise k hk ζ
      have hgap_if_eq :
          (∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk' : k ∈ Icc 1 N then
              objective S (rsgfPrefixIterate S ζ ⟨k, hk'⟩) - fStar S
            else
              0) ∂(rsgfPrefixLaw S N)) =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
              ∂(rsgfPrefixLaw S N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro ζ
        simp [hk]
      have hleft_eval :
          (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S -
                S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
              ∂(rsgfPrefixLaw S N)) =
            (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
              ∂(rsgfPrefixLaw S N)) -
              S.μ ^ (2 : ℕ) * S.L * (n : ℝ) := by
        calc
          (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S -
                S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
              ∂(rsgfPrefixLaw S N))
              =
            (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
              ∂(rsgfPrefixLaw S N)) -
              ∫ _ζ : RsgfSamplePrefix n Sample N,
                S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
                ∂(rsgfPrefixLaw S N) := by
                exact integral_sub hgap_cur (integrable_const _)
          _ =
            (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
              ∂(rsgfPrefixLaw S N)) -
              S.μ ^ (2 : ℕ) * S.L * (n : ℝ) := by
                simp
      have hgrad_eq :
          gradInnerIntegral k =
            ∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪∇ (gaussianSmoothing S)
                  (rsgfPrefixIterate S ζ ⟨k, hk⟩),
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
              ∂(rsgfPrefixLaw S N) := by
        dsimp [gradInnerIntegral]
        rw [dif_pos hk]
      calc
        (∫ ζ : RsgfSamplePrefix n Sample N,
            (if hk' : k ∈ Icc 1 N then
              objective S (rsgfPrefixIterate S ζ ⟨k, hk'⟩) - fStar S
            else
              0) ∂(rsgfPrefixLaw S N)) -
              S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
            =
          (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
              ∂(rsgfPrefixLaw S N)) -
              S.μ ^ (2 : ℕ) * S.L * (n : ℝ) := by
              rw [hgap_if_eq]
        _ =
          (∫ ζ : RsgfSamplePrefix n Sample N,
              objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S -
                S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
              ∂(rsgfPrefixLaw S N)) := by
              rw [hleft_eval]
        _ ≤
          ∫ ζ : RsgfSamplePrefix n Sample N,
            ⟪∇ (gaussianSmoothing S)
                (rsgfPrefixIterate S ζ ⟨k, hk⟩),
              rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
            ∂(rsgfPrefixLaw S N) := hmono
        _ = gradInnerIntegral k := by
              rw [hgrad_eq]
    refine ⟨hgap_int, ?_⟩
    -- Source steps 14-26: integrated distance recursion, residual cancellation,
    -- second-moment control, convex smoothing bridge, and coefficient comparison.
    let gapIntegral : ℕ → ℝ := fun k =>
      ∫ ζ : RsgfSamplePrefix n Sample N,
        (if hk : k ∈ Icc 1 N then
          objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S
        else
          0) ∂(rsgfPrefixLaw S N)
    let b : ℝ := 2 * ((n : ℝ) + 4) * S.L
    let e : ℝ := S.μ ^ (2 : ℕ) * S.L * (n : ℝ)
    let C : ℝ :=
      2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
          ((n : ℝ) + 6) ^ (3 : ℕ)
    have hγ_nonneg :
        ∀ k, k ∈ Icc 1 N → 0 ≤ S.γ k := by
      intro k hk
      exact
        rsgf_stepsize_nonneg_of_weight_nonneg_of_upper
          S hk
          (SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR k hk)
          (hγ_upper k hk)
    have horacle_for_scalar :
        Finset.sum (Icc 1 N)
            (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) ≤
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) * (2 * b * gapIntegral k + C)) := by
      calc
        Finset.sum (Icc 1 N)
            (fun k => S.γ k ^ (2 : ℕ) * oracleSqIntegral k) ≤
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) *
                (4 * ((n : ℝ) + 4) * S.L * gapIntegral k + C)) := by
              simpa [gapIntegral, C, mul_comm, mul_left_comm, mul_assoc] using
                horacle_sq_weighted_budget
        _ =
          Finset.sum (Icc 1 N)
            (fun k =>
              S.γ k ^ (2 : ℕ) * (2 * b * gapIntegral k + C)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              dsimp [b]
              ring
    have hweighted_budget :
        2 * Finset.sum (Icc 1 N)
            (fun k => rsgfWeightNumerator S k * gapIntegral k) ≤
          distIntegral 1 +
            2 * e * Finset.sum (Icc 1 N) S.γ +
            C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
      have hscalar :=
        weighted_gap_sum_le_of_terminal_grad_oracle_budget
          S.γ gapIntegral gradInnerIntegral oracleSqIntegral N
          (distIntegral 1) b e C hγ_nonneg
          (by
            intro k hk
            simpa [gapIntegral, e] using hgrad_gap_integral k hk)
          hterminal_grad_budget horacle_for_scalar
      simpa [gapIntegral, b, rsgfWeightNumerator, mul_comm, mul_left_comm,
        mul_assoc] using hscalar
    haveI : IsProbabilityMeasure S.P := S.P_isProbability
    haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
      rw [gaussianDirectionLaw_def]
      infer_instance
    haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
      unfold rsgfZetaLaw
      infer_instance
    haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
      unfold rsgfPrefixLaw
      infer_instance
    have hdist_one : distIntegral 1 = DX S xStar ^ (2 : ℕ) := by
      have hpos : 1 ≤ (1 : ℕ) := le_rfl
      have hle : (1 : ℕ) - 1 ≤ N := by omega
      dsimp [distIntegral, DX]
      simp [rsgfPrefixIterate0]
    have hsumγ_nonneg :
        0 ≤ Finset.sum (Icc 1 N) S.γ := by
      exact Finset.sum_nonneg hγ_nonneg
    have hsumγsq_nonneg :
        0 ≤ Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
      exact Finset.sum_nonneg fun k hk => sq_nonneg (S.γ k)
    have hlinear_coeff :
        2 * e ≤ 2 * S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) := by
      have hn_le : (n : ℝ) ≤ (n : ℝ) + 4 := by nlinarith
      have hscale_nonneg : 0 ≤ 2 * S.μ ^ (2 : ℕ) * S.L := by
        exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg S.μ))
          (le_of_lt S.L_pos)
      have hmul :=
        mul_le_mul_of_nonneg_left hn_le hscale_nonneg
      nlinarith [hmul]
    have hlinear_budget :
        2 * e * Finset.sum (Icc 1 N) S.γ ≤
          2 * S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) *
            Finset.sum (Icc 1 N) S.γ :=
      mul_le_mul_of_nonneg_right hlinear_coeff hsumγ_nonneg
    have hcube :
        ((n : ℝ) + 6) ^ (3 : ℕ) ≤
          4 * ((n : ℝ) + 4) ^ (3 : ℕ) := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      nlinarith [sq_nonneg ((n : ℝ) + 4), sq_nonneg ((n : ℝ) + 6)]
    have hquad_coeff :
        C ≤
          2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) := by
      have hscale_nonneg :
          0 ≤ S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 := by positivity
      have hmul :=
        mul_le_mul_of_nonneg_left hcube hscale_nonneg
      have hmul' :
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ) ≤
            2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) := by
        calc
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ) ≤
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              (4 * ((n : ℝ) + 4) ^ (3 : ℕ)) := hmul
          _ =
            2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) := by
              ring
      dsimp [C]
      linarith
    have hquad_budget :
        C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) ≤
          (2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (3 : ℕ) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) *
            Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hquad_coeff hsumγsq_nonneg
    have hnum_expand :
        convexRsgfBoundNumerator S N xStar =
          DX S xStar ^ (2 : ℕ) +
            2 * S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) *
              Finset.sum (Icc 1 N) S.γ +
            (2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                ((n : ℝ) + 4) ^ (3 : ℕ) +
              2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ)) *
              Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
      have hsum_split :
          Finset.sum (Icc 1 N)
              (fun k =>
                S.γ k +
                  S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
                    S.γ k ^ (2 : ℕ)) =
            Finset.sum (Icc 1 N) S.γ +
              S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
                Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      unfold convexRsgfBoundNumerator
      rw [hsum_split]
      ring
    have hbudget_to_num :
        distIntegral 1 +
            2 * e * Finset.sum (Icc 1 N) S.γ +
            C * Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) ≤
          convexRsgfBoundNumerator S N xStar := by
      rw [hnum_expand]
      nlinarith [hdist_one, hlinear_budget, hquad_budget]
    exact le_trans (by simpa [gapIntegral] using hweighted_budget) hbudget_to_num
  rcases hcore with ⟨hgap_int, hweighted⟩
  have hselected :=
    rsgf_selected_expectation_eq_weighted_prefix_sum S N hPR hgap_int
  exact
    rsgf_selected_expectation_le_of_weighted_gap_sum S N xStar hPR
      hselected hweighted

end

end Algorithms.Unverified.StochasticZerothOrder
