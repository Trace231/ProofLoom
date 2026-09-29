import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
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

/-- Paper-level assertion that a vector-valued mathematical expectation is
well-defined and has the displayed value.  This local predicate prevents the
source assumptions from degenerating into Lean's totalized Bochner-integral
equalities when the expectation is not defined. -/
def PaperVectorExpectationEq {n : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) (X : Sample → Space n) (m : Space n) : Prop :=
  Measurable X ∧ Integrable X P ∧ (∫ ξ, X ξ ∂P) = m

/-- Paper-level assertion that a real-valued mathematical expectation is
well-defined and bounded above by the displayed scalar. -/
def PaperRealExpectationLe {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) (X : Sample → ℝ) (c : ℝ) : Prop :=
  Integrable X P ∧ (∫ ξ, X ξ ∂P) ≤ c

/-- Paper-level assertion that a real-valued mathematical expectation is
well-defined and has the displayed value. -/
def PaperRealExpectationEq {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) (X : Sample → ℝ) (m : ℝ) : Prop :=
  Measurable X ∧ Integrable X P ∧ (∫ ξ, X ξ ∂P) = m

/-- Source Assumption 13 for the stochastic first-order oracle, specialized to
the paper's canonical sample-gradient oracle.  This records the displayed
mathematical expectation and variance assertions (6.1.5)-(6.1.6), including
well-definedness of those expectations, without aliasing the paper assumption
to the stronger SOptLib realization contract. -/
def SFOAssumption13 {n : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) (f : Space n → ℝ) (G : Space n → Sample → Space n)
    (σ : ℝ) : Prop :=
  ∀ x : Space n,
    PaperVectorExpectationEq P (fun ξ => G x ξ) (∇ f x) ∧
      PaperRealExpectationLe P (fun ξ => ‖G x ξ - ∇ f x‖ ^ (2 : ℕ))
        (σ ^ (2 : ℕ))


/-- Source Assumption 15 for the stochastic zeroth-order oracle.  Book JSON
`#/assumptions/5` states `E[F(x_k, ξ_k)] = f(x_k)`; the paper-level predicate
records fixed-query measurability, integrability, and the displayed value, so
this mathematical expectation is semantically defined. -/
def SZOAssumption15 {n : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    (P : Measure Sample) (F : Space n → Sample → ℝ) (f : Space n → ℝ) :
    Prop :=
  ∀ x : Space n, PaperRealExpectationEq P (fun ξ => F x ξ) (f x)

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
  /-- Source objective smoothness `f ∈ C_L^{1,1}(R^n)`, listed in book JSON
  `#/assumptions/1` and stated after (6.1.47) as the consequence of the
  almost-sure sample smoothness hypothesis. -/
  objective_CL11_source :
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

/-- Lean realization contract for the canonical objective, packaged from
Assumption 15's fixed-query expectation interface. -/
theorem objective_realization_assumption15 (S : Setup n Sample) :
    SOptLib.StochasticObjectiveRealization S.P S.F (objective S) := by
  constructor
  · intro x
    exact (S.szo_assumption15 x).1
  · constructor
    · intro x
      exact (S.szo_assumption15 x).2.1
    · intro x
      simpa [objective] using (S.szo_assumption15 x).2.2

/-- The source expectation defining `f(x)` is well-defined by Assumption 15. -/
theorem objective_value_wellDefined (S : Setup n Sample) (x : Space n) :
    objectiveValueWellDefined S x := by
  exact (S.szo_assumption15 x).2.1

/-- The canonical objective has the source `C_L^{1,1}` regularity, derived from
the a.s. sample smoothness statement and Assumption 15, as stated in book JSON
`#/setup/variable_space`: `F(x,ξ) ∈ C_L^{1,1}` a.s., "which clearly implies"
`f(x) ∈ C_L^{1,1}`. -/
theorem objective_CL11 (S : Setup n Sample) :
    CL11 (objective S) S.L := by
  simpa [objective] using S.objective_CL11_source

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
theorem sampleGradient_sfo_realization (S : Setup n Sample) :
    SOptLib.FixedQueryUnbiasedVarianceOracle S.P
      (fun x ξ => gradient (fun y => S.F y ξ) x) (fun x => ∇ (objective S) x) S.σ := by
  constructor
  · intro x
    exact (S.sfo_assumption13 x).1.1
  · constructor
    · intro x
      exact (S.sfo_assumption13 x).1.2.1
    · constructor
      · intro x
        exact (S.sfo_assumption13 x).2.1
      · constructor
        · intro x
          exact (S.sfo_assumption13 x).1.2.2
        · intro x
          exact (S.sfo_assumption13 x).2.2

/-- Assumption 13(a), projected from the source assumption bundle. -/
theorem sfo_unbiased (S : Setup n Sample) (x : Space n) :
    (∫ ξ, gradient (fun y => S.F y ξ) x ∂S.P) = ∇ (objective S) x := by
  exact (S.sfo_assumption13 x).1.2.2

/-- Assumption 13(b), projected from the source assumption bundle. -/
theorem sfo_variance_bound (S : Setup n Sample) (x : Space n) :
    (∫ ξ, ‖gradient (fun y => S.F y ξ) x - ∇ (objective S) x‖ ^ (2 : ℕ) ∂S.P) ≤
      S.σ ^ (2 : ℕ) := by
  exact (S.sfo_assumption13 x).2.2

/-- Fixed-query integrability needed to read Assumption 13(a) as a semantic
expectation.  This is derived from the source oracle realization, not a
primitive source assumption. -/
theorem sfo_integrable (S : Setup n Sample) (x : Space n) :
    Integrable (fun ξ => gradient (fun y => S.F y ξ) x) S.P :=
  (S.sfo_assumption13 x).1.2.1

/-- Fixed-query integrability needed to read Assumption 13(b) as a semantic
second-moment statement.  This is a proof obligation derived from the source
oracle realization, not a primitive source assumption. -/
theorem sfo_centered_norm_sq_integrable (S : Setup n Sample) (x : Space n) :
    Integrable
      (fun ξ => ‖gradient (fun y => S.F y ξ) x - ∇ (objective S) x‖ ^ (2 : ℕ))
      S.P :=
  (S.sfo_assumption13 x).2.1

/-- Fixed-query integrability needed to read Assumption 15 as a semantic
expectation.  This is derived from the source stochastic-objective realization,
not a primitive source assumption. -/
theorem szo_integrable (S : Setup n Sample) (x : Space n) :
    Integrable (fun ξ => S.F x ξ) S.P :=
  (S.szo_assumption15 x).2.1

/-- Assumption 15, projected from the source expectation statement. -/
theorem szo_unbiased (S : Setup n Sample) (x : Space n) :
    (∫ ξ, S.F x ξ ∂S.P) = objective S x := by
  exact (S.szo_assumption15 x).2.2

/-- Assumption 13 measurability for the canonical sample-gradient oracle. -/
theorem sampleGradient_measurable (S : Setup n Sample) (x : Space n) :
    Measurable (fun ξ => gradient (fun y => S.F y ξ) x) :=
  (sampleGradient_sfo_realization S).1 x

/-- Assumption 13 integrability for the canonical sample-gradient oracle. -/
theorem sampleGradient_integrable (S : Setup n Sample) (x : Space n) :
    Integrable (fun ξ => gradient (fun y => S.F y ξ) x) S.P :=
  (sampleGradient_sfo_realization S).2.1 x

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
    ((sampleGradient_sfo_realization S).2.2.1 x)
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
    ((sampleGradient_sfo_realization S).2.2.1 x)

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
      ((objective_realization_assumption15 S).2.1 (x + S.μ • u))
      ((objective_realization_assumption15 S).2.1 x)
      (by simpa [objective] using
        (objective_realization_assumption15 S).2.2 (x + S.μ • u))
      (by simpa [objective] using (objective_realization_assumption15 S).2.2 x)

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
        (objective_realization_assumption15 S).1 (x + S.μ • u)
      have hx : Measurable fun ξ => S.F x ξ :=
        (objective_realization_assumption15 S).1 x
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
      (objective_realization_assumption15 S).1
      S.sample_smooth_ae
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
    ((objective_realization_assumption15 S).2.1 x)
    (Filter.Eventually.of_forall fun u =>
      (objective_realization_assumption15 S).2.1 (x + S.μ • u))
    (by simpa [objective] using (objective_realization_assumption15 S).2.2 x)
    (Filter.Eventually.of_forall fun u => by
      simpa [objective] using
        (objective_realization_assumption15 S).2.2 (x + S.μ • u))
    (by
      rw [gaussian_forward_difference_integral_eq_gradient_average S x]
      simpa [gaussianSmoothing, gaussianDirectionLaw_def] using
        gaussianSmoothing_hasGradientAt_average S x)

/-- Canonical centered RSGF oracle residual
`Δ_μ(x, ξ, u) = G_μ(x, ξ, u) - ∇ f^μ(x)`, the proof object denoted by `Δ_k`
around (6.1.66)-(6.1.67). -/
def rsgfResidual (S : Setup n Sample) (x : Space n) (ξ : Sample) (u : Space n) :
    Space n :=
  SOptLib.oracleEstimatorError (fun y => ∇ (gaussianSmoothing S) y)
    (rsgfOracle S x ξ u) x

@[simp]
theorem rsgfResidual_def (S : Setup n Sample) (x : Space n) (ξ : Sample)
    (u : Space n) :
    rsgfResidual S x ξ u = rsgfOracle S x ξ u - ∇ (gaussianSmoothing S) x := by
  rfl

/-- The proof-level residual mean-zero fact displayed as (6.1.66). -/
theorem rsgfResidual_mean_zero (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        rsgfResidual S x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) = 0 := by
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
        ⟪rsgfResidual S x z.1 z.2, d⟫_ℝ
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
        (fun z : Sample × Space n => rsgfResidual S x z.1 z.2)
        (S.P.prod (gaussianDirectionLaw n)) := by
    simpa [SOptLib.oracleEstimatorError] using
      horacle_int.sub (integrable_const (c := ∇ (gaussianSmoothing S) x))
  have hlin :=
    ContinuousLinearMap.integral_comp_comm
      (L := (innerSLFlip ℝ d)) hres_int
  have hvec_zero :
      (∫ z : Sample × Space n,
        rsgfResidual S x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) = 0 :=
    rsgfResidual_mean_zero S x
  calc
    (∫ z : Sample × Space n,
        ⟪rsgfResidual S x z.1 z.2, d⟫_ℝ
          ∂(S.P.prod (gaussianDirectionLaw n)))
        = ∫ z : Sample × Space n,
            (innerSLFlip ℝ d) (rsgfResidual S x z.1 z.2)
              ∂(S.P.prod (gaussianDirectionLaw n)) := by
            simp only [innerSLFlip_apply_apply]
    _ = (innerSLFlip ℝ d)
          (∫ z : Sample × Space n,
            rsgfResidual S x z.1 z.2 ∂(S.P.prod (gaussianDirectionLaw n))) := hlin
    _ = 0 := by
            rw [hvec_zero]
            simp

/-- Fixed-query scalar residual integrability.  This is the fiberwise L2
side-condition used before resampling a fresh prefix coordinate. -/
private theorem rsgfResidual_norm_sq_integrable
    (S : Setup n Sample) (x : Space n) :
    Integrable
      (fun z : Sample × Space n => ‖rsgfResidual S x z.1 z.2‖ ^ (2 : ℕ))
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
        ‖rsgfResidual S x z.1 z.2‖ ^ (2 : ℕ)
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

/-- Fixed-query residual version of the gradient-plus-variance moment estimate
in (6.1.67).  This is the pointwise fiber bound used in the post-optimization
fresh-sample product law. -/
private theorem rsgfResidual_secondMoment_le_gradient_sigma
    (S : Setup n Sample) (x : Space n) :
    (∫ z : Sample × Space n,
        ‖rsgfResidual S x z.1 z.2‖ ^ (2 : ℕ)
          ∂(S.P.prod (gaussianDirectionLaw n))) ≤
      2 * ((n : ℝ) + 4) *
          (‖∇ (objective S) x‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ)) +
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) := by
  exact
    (rsgfResidual_secondMoment_le_oracle_secondMoment S x).trans
      (rsgfOracle_secondMoment_le_gradient_sigma S x)

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

/-- Source choice of the random-output probability mass function in (6.1.61):
an actual PMF whose atoms satisfy the displayed normalized formula, together
with the admissibility of the displayed real weights.  The proof of Theorem 6.3
divides by the positive weighted denominator, so this is the source-boundary
contract that the displayed formula denotes the paper's normalized PMF rather
than only an extensional atom equation. -/
abbrev RsgfOutputPMFSourceChoice (S : Setup n Sample) (N : ℕ) :=
  {p : PMF (RsgfOutputIndex N) //
    RsgfOutputWeightsAdmissible S N ∧
      SOptLib.FiniteWindowPMFSpec (Icc 1 N) (fun k => rsgfWeightNumerator S k) p}

/-- The source PMF boundary supplies admissible real weights for the displayed
normalization in (6.1.61). -/
theorem rsgfOutputPMFSourceChoice_admissible (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputPMFSourceChoice S N) :
    RsgfOutputWeightsAdmissible S N :=
  hPR.2.1

/-- Positive source stepsizes below the Theorem 6.3 upper bound make the
displayed weights in (6.1.61) admissible for normalization. -/
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

/-- Internal realization of the paper PMF after a proof of real-weight
admissibility has been supplied.  The proof parameter is deliberately kept
behind the source-facing PMF definition below. -/
private noncomputable def rsgfOutputPMF_of_admissible (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    PMF (RsgfOutputIndex N) :=
  SOptLib.normalizedFiniteWindowPMF (Icc 1 N)
    (fun k => rsgfWeightNumerator S k)
    (SOptLib.FiniteWindowWeightsAdmissible.nonneg hPR)
    (SOptLib.FiniteWindowWeightsAdmissible.sum_pos hPR)

/-- The canonical RSGF output PMF satisfies the displayed atom formula (6.1.61). -/
private theorem rsgfOutputPMF_of_admissible_apply (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N)
    (R : RsgfOutputIndex N) :
    rsgfOutputPMF_of_admissible S N hPR R =
      ENNReal.ofReal (rsgfWeightNumerator S R.1 / rsgfWeightDenominator S N) := by
  rfl

/-- The canonical RSGF output PMF realizes the finite-window normalized-weight
specification.  This is a derived property of the canonical `def`, not an input
contract for the paper theorem. -/
private theorem rsgfOutputPMF_of_admissible_spec (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N) :
    SOptLib.FiniteWindowPMFSpec (Icc 1 N) (fun k => rsgfWeightNumerator S k)
      (rsgfOutputPMF_of_admissible S N hPR) := by
  exact SOptLib.finiteWindowPMFSpec_of_normalizedFiniteWindowPMF
    (Icc 1 N) (fun k => rsgfWeightNumerator S k)
    hPR

/-- Canonical paper PMF `P_R` from (6.1.61), once the source boundary that it is
a probability mass function has supplied admissible real weights. -/
noncomputable def rsgfOutputPMF (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    PMF (RsgfOutputIndex N) :=
  rsgfOutputPMF_of_admissible S N hPR

/-- The canonical PMF has the normalized atom formula (6.1.61). -/
theorem rsgfOutputPMF_spec (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N) :
    SOptLib.FiniteWindowPMFSpec (Icc 1 N) (fun k => rsgfWeightNumerator S k)
      (rsgfOutputPMF S N hPR) := by
  exact rsgfOutputPMF_of_admissible_spec S hPR

/-- Atom formula for the source PMF. -/
theorem rsgfOutputPMF_apply (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N)
    (R : RsgfOutputIndex N) :
    rsgfOutputPMF S N hPR R =
      ENNReal.ofReal (rsgfWeightNumerator S R.1 / rsgfWeightDenominator S N) := by
  simpa [rsgfOutputPMF] using
    rsgfOutputPMF_of_admissible_apply S hPR R

/-- Output PMF from Theorem 6.3, using the source choice that the displayed
normalized weights define a probability mass function. -/
noncomputable def rsgfOutputPMFTheorem63 (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputPMFSourceChoice S N) :
    PMF (RsgfOutputIndex N) :=
  hPR.1

/-- The source-facing Theorem 6.3 PMF satisfies the displayed atom formula
(6.1.61). -/
theorem rsgfOutputPMFTheorem63_spec (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputPMFSourceChoice S N) :
    SOptLib.FiniteWindowPMFSpec (Icc 1 N) (fun k => rsgfWeightNumerator S k)
      (rsgfOutputPMFTheorem63 S N hPR) := by
  exact hPR.2.2

/-- The source-facing Theorem 6.3 PMF has the displayed atom formula (6.1.61). -/
theorem rsgfOutputPMFTheorem63_apply (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputPMFSourceChoice S N)
    (R : RsgfOutputIndex N) :
    rsgfOutputPMFTheorem63 S N hPR R =
      ENNReal.ofReal (rsgfWeightNumerator S R.1 / rsgfWeightDenominator S N) := by
  exact hPR.2.2 R

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

@[simp]
theorem rsgfPrefixIterate0_zero (S : Setup n Sample) {N : ℕ}
    (ζ : RsgfSamplePrefix n Sample N) (hN : 0 ≤ N) :
    rsgfPrefixIterate0 S ζ 0 hN = S.x₁ := by
  rfl

@[simp]
theorem rsgfPrefixIterate0_succ (S : Setup n Sample) {N k : ℕ}
    (ζ : RsgfSamplePrefix n Sample N) (hk : k + 1 ≤ N) :
    rsgfPrefixIterate0 S ζ (k + 1) hk =
      rsgfStep S (k + 1)
        (rsgfPrefixIterate0 S ζ k (Nat.le_of_succ_le hk))
        (ζ ⟨k + 1, mem_Icc.mpr ⟨Nat.succ_pos k, hk⟩⟩).1
        (ζ ⟨k + 1, mem_Icc.mpr ⟨Nat.succ_pos k, hk⟩⟩).2 := by
  rfl

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
        ⟪rsgfResidual S
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩ -
            xStar⟫_ℝ ∂rsgfZetaLaw S) = 0 := by
  change
    (∫ z : Sample × Space n,
        ⟪rsgfResidual S
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩ -
            xStar⟫_ℝ ∂(S.P.prod (gaussianDirectionLaw n))) = 0
  calc
    (∫ z : Sample × Space n,
        ⟪rsgfResidual S
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩ -
            xStar⟫_ℝ ∂(S.P.prod (gaussianDirectionLaw n)))
        =
      ∫ z : Sample × Space n,
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2,
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
        (rsgfPrefixLaw S N)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ
        ∂rsgfPrefixLaw S N) = 0 := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ⟪rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
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
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
        ⟪rsgfResidual S
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          ∇ (gaussianSmoothing S)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)⟫_ℝ
        ∂rsgfZetaLaw S) = 0 := by
  change
    (∫ z : Sample × Space n,
        ⟪rsgfResidual S
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          ∇ (gaussianSmoothing S)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)⟫_ℝ
        ∂(S.P.prod (gaussianDirectionLaw n))) = 0
  calc
    (∫ z : Sample × Space n,
        ⟪rsgfResidual S
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)
            z.1 z.2,
          ∇ (gaussianSmoothing S)
            (rsgfPrefixIterate S (Function.update ζ ⟨k, hk⟩ z) ⟨k, hk⟩)⟫_ℝ
        ∂(S.P.prod (gaussianDirectionLaw n)))
        =
      ∫ z : Sample × Space n,
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2,
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
            ∇ (gaussianSmoothing S)
              (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ)
        (rsgfPrefixLaw S N)) :
    (∫ ζ : RsgfSamplePrefix n Sample N,
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
          ∇ (gaussianSmoothing S) (rsgfPrefixIterate S ζ ⟨k, hk⟩)⟫_ℝ
        ∂rsgfPrefixLaw S N) = 0 := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ⟪rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
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
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
    rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2⟫_ℝ +
        (S.L / 2) * S.γ k ^ (2 : ℕ) *
          ‖rsgfOracle S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
              (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ) := by
        rfl

/-- Internal joint law of the selected output index and full prefix randomness
after a proof of PMF admissibility has been supplied. -/
private noncomputable def rsgfSelectedRunLaw (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    Measure (RsgfOutputIndex N × RsgfSamplePrefix n Sample N) :=
  (rsgfOutputPMF_of_admissible S N hPR).toMeasure.prod (rsgfPrefixLaw S N)

/-- Internal selected-output expectation using the admissible PMF realization. -/
private noncomputable def rsgfSelectedJointExpectation (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (φ : RsgfOutputIndex N → RsgfSamplePrefix n Sample N → ℝ) : ℝ :=
  ∫ q, φ q.1 q.2 ∂(rsgfSelectedRunLaw S N hPR)

/-- Canonical joint law of the one-run RSGF output index and its finite sample
prefix, using the source PMF boundary from (6.1.61). -/
noncomputable def rsgfSelectedRunLawCanonical (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    Measure (RsgfOutputIndex N × RsgfSamplePrefix n Sample N) :=
  (rsgfOutputPMF S N hPR).toMeasure.prod (rsgfPrefixLaw S N)

/-- Canonical selected-output expectation for one RSGF run. -/
noncomputable def rsgfSelectedJointExpectationCanonical
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (φ : RsgfOutputIndex N → RsgfSamplePrefix n Sample N → ℝ) : ℝ :=
  ∫ q, φ q.1 q.2 ∂(rsgfSelectedRunLawCanonical S N hPR)

/-- Source-facing selected-run law for Theorem 6.3, using the paper's displayed
PMF choice (6.1.61). -/
noncomputable def rsgfSelectedRunLawTheorem63
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputPMFSourceChoice S N) :
    Measure (RsgfOutputIndex N × RsgfSamplePrefix n Sample N) :=
  (rsgfOutputPMFTheorem63 S N hPR).toMeasure.prod (rsgfPrefixLaw S N)

/-- Source-facing selected-output expectation for Theorem 6.3. -/
noncomputable def rsgfSelectedJointExpectationTheorem63
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputPMFSourceChoice S N)
    (φ : RsgfOutputIndex N → RsgfSamplePrefix n Sample N → ℝ) : ℝ :=
  ∫ q, φ q.1 q.2 ∂(rsgfSelectedRunLawTheorem63 S N hPR)

/-- The source PMF witness in Theorem 6.3 and the canonical admissible-weight
PMF induce the same selected-output expectation whenever admissibility has been
proved separately. -/
private theorem rsgf_selected_joint_expectation_theorem63_eq_admissible
    (S : Setup n Sample) (N : ℕ)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hPR_source : RsgfOutputPMFSourceChoice S N)
    (φ : RsgfOutputIndex N → RsgfSamplePrefix n Sample N → ℝ) :
    rsgfSelectedJointExpectationTheorem63 S N hPR_source φ =
      rsgfSelectedJointExpectation S N hPR φ := by
  classical
  have hpmf :
      rsgfOutputPMFTheorem63 S N hPR_source =
        rsgfOutputPMF_of_admissible S N hPR := by
    ext R
    rw [rsgfOutputPMFTheorem63_apply, rsgfOutputPMF_of_admissible_apply]
  unfold rsgfSelectedJointExpectationTheorem63
    rsgfSelectedJointExpectation rsgfSelectedRunLawTheorem63 rsgfSelectedRunLaw
  rw [hpmf]

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

/-- Source-boundary obligation for the printed minimum
`f_mu^* := min_x f_mu(x)` in (6.1.56).  The JSON/PDF print a minimum but do not
state compactness, coercivity, or another attainment assumption, so this
obligation is not asserted as a theorem from `Setup`. -/
def FMuMinimumAttainmentObligation (S : Setup n Sample) : Prop :=
  ∃ x : Space n, ∀ y : Space n, gaussianSmoothing S x ≤ gaussianSmoothing S y

/-- Infimum-valued fallback for smoothed objective lower-bound arguments.  This
is intentionally not named `f_mu^*`, because the source definition (6.1.56)
prints a minimum. -/
noncomputable def fMuInfimum (S : Setup n Sample) : ℝ :=
  SOptLib.objectiveInfimumValue Set.univ (gaussianSmoothing S)

@[simp]
theorem fMuInfimum_def (S : Setup n Sample) :
    fMuInfimum S = sInf ((gaussianSmoothing S) '' (Set.univ : Set (Space n))) := by
  simp [fMuInfimum, SOptLib.objectiveInfimumValue_def]

/-- The smoothed objective is bounded below because the original objective is
bounded below and the Gaussian smoothing bias is uniformly bounded. -/
theorem fMu_bddBelow (S : Setup n Sample) :
    BddBelow ((gaussianSmoothing S) '' (Set.univ : Set (Space n))) := by
  classical
  let err : ℝ := S.μ ^ (2 : ℕ) * S.L * (n : ℝ) / 2
  rcases objective_bddBelow S with ⟨lb, hlb⟩
  refine ⟨lb - err, ?_⟩
  intro y hy
  rcases hy with ⟨x, _hx, rfl⟩
  have hobj : lb ≤ objective S x := hlb ⟨x, rfl⟩
  have habs : |gaussianSmoothing S x - objective S x| ≤ err := by
    simpa [err] using gaussianSmoothing_abs_sub_objective_le S x
  have hlow : -err ≤ gaussianSmoothing S x - objective S x := (abs_le.mp habs).1
  linarith

/-- The infimum-valued smoothed lower reference lower-bounds every smoothed
objective value. -/
theorem fMuInfimum_le (S : Setup n Sample) (x : Space n) :
    fMuInfimum S ≤ gaussianSmoothing S x := by
  simpa [fMuInfimum] using
    SOptLib.objectiveInfimumValue_le (X := (Set.univ : Set (Space n)))
      (f := gaussianSmoothing S) (fMu_bddBelow S) (Set.mem_univ x)

/-- Denominator well-definedness boundary for the quotient in the constant
stepsize display (6.1.70), whose second branch contains
`Dtilde / (sigma sqrt N)`.  This is not part of the original source policy
because the source does not separately state `sigma != 0`. -/
def RsgfConstantStepsizeWellDefined (S : Setup n Sample) (N : ℕ) : Prop :=
  S.σ * Real.sqrt (N : ℝ) ≠ 0

/-- Ordinary-real quotient value for the second branch
`Dtilde / (sigma sqrt N)` in (6.1.70).  It is relational rather than a Lean
division expression so the `sigma = 0` boundary cannot be hidden by totalized
division. -/
def RsgfConstantStepsizeQuotientValue
    (S : Setup n Sample) (N : ℕ) (Dtilde q : ℝ) : Prop :=
  S.σ * Real.sqrt (N : ℝ) ≠ 0 ∧
    q * (S.σ * Real.sqrt (N : ℝ)) = Dtilde

/-- Relational value of the literal scalar expression displayed in the constant
stepsize policy (6.1.70).  The second branch is represented by an ordinary
quotient witness, not by Lean's totalized division at denominator zero. -/
def RsgfConstantStepsizeValue
    (S : Setup n Sample) (N : ℕ) (Dtilde γval : ℝ) : Prop :=
  ∃ q : ℝ,
    RsgfConstantStepsizeQuotientValue S N Dtilde q ∧
      γval =
        (1 / Real.sqrt ((n : ℝ) + 4)) *
          min (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) q

/-- Source policy (6.1.70): the optimization-phase RSGF runs use the displayed
constant stepsize for `k = 1, ..., N`.  Since the source also allows
`sigma ≥ 0`, this Lean boundary is relational/corrected: it exposes the missing
ordinary-quotient denominator obligation instead of assigning a totalized value
when `sigma = 0`. -/
def RsgfConstantStepsizePolicy (S : Setup n Sample) (N : ℕ) (Dtilde : ℝ) : Prop :=
  ∀ k ∈ Icc 1 N, RsgfConstantStepsizeValue S N Dtilde (S.γ k)

/-- Corrected nonzero-denominator regime for using (6.1.70) as an ordinary real
quotient.  This is internal/corrected-boundary machinery, not the paper's
printed constant-stepsize policy. -/
def RsgfConstantStepsizeNonzeroRegime
    (S : Setup n Sample) (N : ℕ) (Dtilde : ℝ) : Prop :=
  RsgfConstantStepsizeWellDefined S N ∧
    RsgfConstantStepsizePolicy S N Dtilde

/-- In the corrected nonzero-denominator regime, the quotient in (6.1.70) is
meaningful as an ordinary real quotient. -/
theorem rsgfConstantStepsizeNonzeroRegime_wellDefined
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hsteps : RsgfConstantStepsizeNonzeroRegime S N Dtilde) :
    RsgfConstantStepsizeWellDefined S N :=
  hsteps.1

/-- The constant stepsize policy (6.1.70) supplies the Theorem 6.3 stepsize
upper bound needed by the canonical output PMF (6.1.61).  This is a derived
bridge from the paper's policy choices, not an additional theorem hypothesis. -/
theorem rsgfConstantStepsizePolicy_upper_bound
    (S : Setup n Sample) {N : ℕ} (Dtilde : ℝ)
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde) :
    ∀ k ∈ Icc 1 N, S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹ := by
  intro k hk
  rcases hsteps k hk with ⟨q, hq, hγeq⟩
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 4) :=
    Real.sqrt_pos_of_pos hn4_pos
  have hpref_nonneg : 0 ≤ (1 / Real.sqrt ((n : ℝ) + 4)) := by
    positivity
  have hfirst_le :
      S.γ k ≤
        (1 / Real.sqrt ((n : ℝ) + 4)) *
          (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) := by
    rw [hγeq]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) hpref_nonneg
  have hfirst_lt :
      (1 / Real.sqrt ((n : ℝ) + 4)) *
          (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) <
        (2 * ((n : ℝ) + 4) * S.L)⁻¹ := by
    have hsqrt_ne : Real.sqrt ((n : ℝ) + 4) ≠ 0 := ne_of_gt hsqrt_pos
    have hL_ne : S.L ≠ 0 := ne_of_gt S.L_pos
    have hn4_nonneg : 0 ≤ (n : ℝ) + 4 := le_of_lt hn4_pos
    have hbranch_eq :
        (1 / Real.sqrt ((n : ℝ) + 4)) *
            (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) =
          1 / (4 * S.L * ((n : ℝ) + 4)) := by
      field_simp [hsqrt_ne, hL_ne]
      exact (Real.sq_sqrt hn4_nonneg).symm
    have hscalar :
        1 / (4 * S.L * ((n : ℝ) + 4)) <
          1 / (2 * ((n : ℝ) + 4) * S.L) := by
      have hden2_pos : 0 < 2 * ((n : ℝ) + 4) * S.L := by
        exact mul_pos (mul_pos (by norm_num) hn4_pos) S.L_pos
      have hden2_lt_den1 :
          2 * ((n : ℝ) + 4) * S.L <
            4 * S.L * ((n : ℝ) + 4) := by
        nlinarith [hn4_pos, S.L_pos]
      exact one_div_lt_one_div_of_lt hden2_pos hden2_lt_den1
    rw [hbranch_eq]
    simpa [one_div] using hscalar
  exact lt_of_le_of_lt hfirst_le hfirst_lt

/-- Smoothing-parameter upper bound (6.1.71). -/
def rsgfSmoothingParameterBound (S : Setup n Sample) (N : ℕ) : ℝ :=
  Df S / (((n : ℝ) + 4) * Real.sqrt (2 * (N : ℝ)))

/-- Source smoothing policy (6.1.71) for the 2-RSGF optimization phase. -/
def RsgfSmoothingParameterPolicy (S : Setup n Sample) (N : ℕ) : Prop :=
  S.μ ≤ rsgfSmoothingParameterBound S N

/-- Confidence-dependent run count (6.1.32). -/
def rsgfConfidenceRunCount (Λ : ℝ) : ℕ :=
  SOptLib.runCountChoice Λ

/-- The 2-RSGF confidence run count is the reusable base-two confidence
selector. -/
theorem rsgfConfidenceRunCount_eq_runCountChoice (Λ : ℝ) :
    rsgfConfidenceRunCount Λ = SOptLib.runCountChoice Λ := rfl

/-- Unfolding form of the confidence-dependent run count (6.1.32). -/
theorem rsgfConfidenceRunCount_eq_ceil_log_div_log_two (Λ : ℝ) :
    rsgfConfidenceRunCount Λ =
      Nat.ceil (Real.log (2 / Λ) / Real.log 2) := by
  rfl

/-- The one-run bound `B̄_N` from (6.1.72). -/
def rsgfBbar (S : Setup n Sample) (N : ℕ) (Dtilde : ℝ) : ℝ :=
  12 * ((n : ℝ) + 4) * S.L * Df S ^ (2 : ℕ) / (N : ℝ) +
    (4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ)) *
      (Dtilde + Df S ^ (2 : ℕ) / Dtilde)

/-- Iteration-limit policy `N̂(ε)` from (6.1.82), represented as a real-valued
selector because the source display uses the real formula before choosing an
integer iteration count. -/
def rsgfIterationLimitPolicy (S : Setup n Sample) (ε Dtilde : ℝ) : ℝ :=
  max
    (12 * ((n : ℝ) + 4) * (6 * S.L * Df S) ^ (2 : ℕ) / ε)
    ((72 * S.L * Real.sqrt ((n : ℝ) + 4) *
        (Dtilde + Df S ^ (2 : ℕ) / Dtilde) * S.σ / ε) ^ (2 : ℕ))

/-- Post-optimization sample-size policy `T̂(ε,Λ)` from (6.1.83). -/
def rsgfPostOptimizationSamplePolicy (S : Setup n Sample)
    (ε Λ : ℝ) : ℝ :=
  24 * ((n : ℝ) + 4) * (rsgfConfidenceRunCount Λ + 1 : ℝ) / Λ *
    max 1 (6 * S.σ ^ (2 : ℕ) / ε)

/-- Exact two-calls-per-estimator SZO call count from (6.1.84). -/
def rsgfTwoPhaseCallCount (S : Setup n Sample) (ε Λ Dtilde : ℝ) : ℝ :=
  2 * (rsgfConfidenceRunCount Λ : ℝ) *
    (rsgfIterationLimitPolicy S ε Dtilde +
      rsgfPostOptimizationSamplePolicy S ε Λ)

/-- Source policy (6.1.82): the iteration limit is set to `Nhat(epsilon)`. -/
def RsgfIterationLimitPolicy (S : Setup n Sample) (N : ℕ) (ε Dtilde : ℝ) : Prop :=
  (N : ℝ) = rsgfIterationLimitPolicy S ε Dtilde

/-- Source policy (6.1.83): the post-optimization sample size is set to
`That(epsilon, Lambda)`. -/
def RsgfPostOptimizationSamplePolicy
    (S : Setup n Sample) (T : ℕ) (ε Λ : ℝ) : Prop :=
  (T : ℝ) = rsgfPostOptimizationSamplePolicy S ε Λ

/-- Source policy (6.1.32): the number of independent runs is
`S(Lambda) = ceil(log(2/Lambda))`. -/
def RsgfConfidenceRunPolicy (S_count : ℕ) (Λ : ℝ) : Prop :=
  S_count = rsgfConfidenceRunCount Λ

/-- The base-two confidence policy makes the geometric optimization-failure
term at most half of the target confidence level. -/
theorem rsgfConfidenceRunPolicy_geometric_tail
    {S_count : ℕ} {Λ : ℝ} (hΛ0 : 0 < Λ)
    (hS_policy : RsgfConfidenceRunPolicy S_count Λ) :
    (1 / 2 : ℝ) ^ S_count ≤ Λ / 2 := by
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ0
  have htwo_div_pos : 0 < 2 / Λ := by positivity
  have hceil_le :
      Real.log (2 / Λ) / Real.log 2 ≤ (S_count : ℝ) := by
    have hceil :
        Real.log (2 / Λ) / Real.log 2 ≤
          (Nat.ceil (Real.log (2 / Λ) / Real.log 2) : ℝ) :=
      Nat.le_ceil _
    have hS_eqceil :
        S_count = Nat.ceil (Real.log (2 / Λ) / Real.log 2) := by
      simpa [RsgfConfidenceRunPolicy, rsgfConfidenceRunCount,
        SOptLib.runCountChoice] using hS_policy
    simpa [hS_eqceil] using hceil
  have hlogb_eq :
      Real.log (2 / Λ) / Real.log 2 = Real.logb 2 (2 / Λ) := by
    rw [Real.log_div_log]
  have hlogb_le : Real.logb 2 (2 / Λ) ≤ (S_count : ℝ) := by
    simpa [hlogb_eq] using hceil_le
  have hpow_ge : 2 / Λ ≤ (2 : ℝ) ^ S_count := by
    have hraw :
        2 / Λ ≤ (2 : ℝ) ^ (S_count : ℝ) :=
      (Real.logb_le_iff_le_rpow (b := (2 : ℝ)) (by norm_num) htwo_div_pos).mp
        hlogb_le
    simpa [Real.rpow_natCast] using hraw
  have hrecip : 1 / ((2 : ℝ) ^ S_count) ≤ 1 / (2 / Λ) :=
    one_div_le_one_div_of_le htwo_div_pos hpow_ge
  calc
    (1 / 2 : ℝ) ^ S_count = 1 / ((2 : ℝ) ^ S_count) := by
      rw [one_div_pow]
    _ ≤ 1 / (2 / Λ) := hrecip
    _ = Λ / 2 := by
      field_simp [hΛ_ne]

/-- A single optimization-run outcome consists of its selected stopping index
and the finite sample prefix used to generate that output. -/
abbrev RsgfRunOutcome (n : ℕ) (Sample : Type*) (N : ℕ) :=
  RsgfOutputIndex N × RsgfSamplePrefix n Sample N

/-- The canonical candidate produced by one RSGF run. -/
def rsgfRunCandidate (S : Setup n Sample) {N : ℕ}
    (q : RsgfRunOutcome n Sample N) : Space n :=
  rsgfPrefixIterate S q.2 q.1

/-- A finite family of independent optimization-run outcomes. -/
abbrev RsgfOptimizationRuns (n : ℕ) (Sample : Type*) (S_count N : ℕ) :=
  Fin S_count → RsgfRunOutcome n Sample N

/-- Formalization-only independent product law for the optimization phase of
2-RSGF.  The book JSON marks this independence/product-law boundary as not
printed by the 2-RSGF algorithm; declarations using this law are helper-level
formalization variants, not source-facing theorem statements. -/
noncomputable def rsgfOptimizationPhaseLaw_independentProduct (S : Setup n Sample)
    (S_count N : ℕ) (hN : 1 ≤ N)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    Measure (RsgfOptimizationRuns n Sample S_count N) :=
  Measure.pi (fun _ : Fin S_count =>
    rsgfSelectedRunLaw S N hPR)

/-- A post-optimization evaluation prefix of length `T`, reusing the canonical
one-step sample object `ζ_k = (ξ_k,u_k)`. -/
abbrev RsgfEvaluationPrefix (n : ℕ) (Sample : Type*) (T : ℕ) :=
  RsgfSamplePrefix n Sample T

/-- Empirical zeroth-order gradient estimator in (6.1.80). -/
def rsgfEmpiricalGradient (S : Setup n Sample) (T : ℕ) (x : Space n)
    (η : RsgfEvaluationPrefix n Sample T) : Space n :=
  (1 / (T : ℝ)) •
    ∑ k : RsgfOutputIndex T, rsgfOracle S x (η k).1 (η k).2

/-- Empirical gradient evaluated at the candidate from run `s`. -/
def rsgfTwoPhaseEmpiricalGradient (S : Setup n Sample)
    {S_count N T : ℕ} (runs : RsgfOptimizationRuns n Sample S_count N)
    (η : RsgfEvaluationPrefix n Sample T) (s : Fin S_count) : Space n :=
  rsgfEmpiricalGradient S T (rsgfRunCandidate S (runs s)) η

/-- Minimum-empirical-norm selector for the post-optimization phase. -/
noncomputable def rsgfTwoPhaseSelector (S : Setup n Sample)
    {S_count N T : ℕ} (runs : RsgfOptimizationRuns n Sample S_count N)
    (η : RsgfEvaluationPrefix n Sample T) (hS : 0 < S_count) : Fin S_count :=
  letI : Nonempty (Fin S_count) := ⟨⟨0, hS⟩⟩
  Classical.choose
    (Finset.exists_min_image (Finset.univ : Finset (Fin S_count))
      (fun s => ‖rsgfTwoPhaseEmpiricalGradient S runs η s‖ ^ (2 : ℕ))
      Finset.univ_nonempty)

/-- The selected candidate `x̄*` of the two-phase method. -/
def rsgfTwoPhaseSelectedOutput (S : Setup n Sample)
    {S_count N T : ℕ} (runs : RsgfOptimizationRuns n Sample S_count N)
    (η : RsgfEvaluationPrefix n Sample T) (hS : 0 < S_count) : Space n :=
  rsgfRunCandidate S (runs (rsgfTwoPhaseSelector S runs η hS))

/-- The selector realizes the minimum empirical zeroth-order norm in
(6.1.80). -/
theorem rsgfTwoPhaseSelector_spec (S : Setup n Sample)
    {S_count N T : ℕ} (runs : RsgfOptimizationRuns n Sample S_count N)
    (η : RsgfEvaluationPrefix n Sample T) (hS : 0 < S_count)
    (s : Fin S_count) :
    ‖rsgfTwoPhaseEmpiricalGradient S runs η
        (rsgfTwoPhaseSelector S runs η hS)‖ ^ (2 : ℕ) ≤
      ‖rsgfTwoPhaseEmpiricalGradient S runs η s‖ ^ (2 : ℕ) := by
  classical
  letI : Nonempty (Fin S_count) := ⟨⟨0, hS⟩⟩
  let value : Fin S_count → ℝ :=
    fun s => ‖rsgfTwoPhaseEmpiricalGradient S runs η s‖ ^ (2 : ℕ)
  have hmin := Classical.choose_spec
    (Finset.exists_min_image (Finset.univ : Finset (Fin S_count))
      value Finset.univ_nonempty)
  change value (rsgfTwoPhaseSelector S runs η hS) ≤ value s
  change value
      (Classical.choose
        (Finset.exists_min_image (Finset.univ : Finset (Fin S_count))
          value Finset.univ_nonempty)) ≤
    value s
  exact hmin.2 s (by simp)

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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
        ‖rsgfResidual S x z.1 z.2‖ ^ (2 : ℕ)
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
        rsgfResidual S (X p.1) p.2.1 p.2.2)
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
            ‖rsgfResidual S (X ω) z.1 z.2‖ ^ (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L * (objective S (X ω) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    Integrable
      (fun p : Ω × RsgfZeta n Sample =>
        ‖rsgfResidual S (X p.1) p.2.1 p.2.2‖ ^ (2 : ℕ))
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
          ‖rsgfResidual S (X p.1) p.2.1 p.2.2‖ ^ (2 : ℕ))
        (ν.prod (rsgfZetaLaw S)) := by
    have hraw :
        AEStronglyMeasurable
          (fun p : Ω × RsgfZeta n Sample =>
            rsgfResidual S (X p.1) p.2.1 p.2.2)
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
      (φ := fun ω z => ‖rsgfResidual S (X ω) z.1 z.2‖ ^ (2 : ℕ))
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
          rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            ‖rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩) z.1 z.2‖ ^
                (2 : ℕ)
              ∂(S.P.prod (gaussianDirectionLaw n))) ≤
          4 * ((n : ℝ) + 4) * S.L *
              (objective S (rsgfPrefixIterate S ζ ⟨k, hk⟩) - fStar S) +
            2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) +
            S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
              ((n : ℝ) + 6) ^ (3 : ℕ)) :
    Integrable
      (fun ζ : RsgfSamplePrefix n Sample N =>
        ‖rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
            (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2‖ ^ (2 : ℕ))
      (rsgfPrefixLaw S N) := by
  classical
  let R : RsgfOutputIndex N := ⟨k, hk⟩
  let Φ : RsgfSamplePrefix n Sample N → ℝ := fun ζ =>
    ‖rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^ (2 : ℕ)
  let Ψ : RsgfSamplePrefix n Sample N × RsgfZeta n Sample → ℝ := fun q =>
    ‖rsgfResidual S (rsgfPrefixIterate S q.1 R) q.2.1 q.2.2‖ ^ (2 : ℕ)
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
        rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        (rsgfPrefixLaw S N) := by
    simpa [R] using
      rsgf_prefix_sampled_residual_aestronglyMeasurable_of_iterate S hk
        (by simpa [R] using hX)
  have hresidual_sq :
      Integrable
        (fun ζ : RsgfSamplePrefix n Sample N =>
          ‖rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
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
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
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
          ‖rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
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
                rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2‖ ^
              (2 : ℕ))
          (rsgfPrefixLaw S N) :=
      integrable_sq_norm_sub
        (P := rsgfPrefixLaw S N)
        (u := fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfOracle S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
        (v := fun ζ : RsgfSamplePrefix n Sample N =>
          rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2)
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
            ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
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
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ R) (ζ R).1 (ζ R).2,
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
            ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
      ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
            ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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

/-- Internal admissible-weight proof helper for Theorem 6.3(a). -/
private theorem theorem_6_3a_nonconvex_of_admissible
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                  ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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

/-- Source-facing nonconvex conclusion of Theorem 6.3(a), expressed with the
canonical generated iterates and the source PMF choice (6.1.61). -/
theorem theorem_6_3a_nonconvex
    (S : Setup n Sample) (N : ℕ)
    (hN : 1 ≤ N)
    (hγ_upper : ∀ k ∈ Icc 1 N, S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹)
    (hPR_source : RsgfOutputPMFSourceChoice S N) :
    (1 / S.L) *
        rsgfSelectedJointExpectationTheorem63 S N hPR_source
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) ≤
      nonconvexRsgfBoundNumerator S N / rsgfWeightDenominator S N := by
  classical
  let hPR : RsgfOutputWeightsAdmissible S N :=
    rsgfOutputPMFSourceChoice_admissible S hPR_source
  have htransport :
      rsgfSelectedJointExpectationTheorem63 S N hPR_source
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) =
        rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) :=
    rsgf_selected_joint_expectation_theorem63_eq_admissible
      S N hPR hPR_source
      (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
  rw [htransport]
  exact theorem_6_3a_nonconvex_of_admissible S N hN hγ_upper hPR

/-- Internal admissible-weight proof helper for Theorem 6.3(b). -/
private theorem theorem_6_3b_convex_of_admissible
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
                  (ζ ⟨k, hk⟩).1 (ζ ⟨k, hk⟩).2,
                rsgfPrefixIterate S ζ ⟨k, hk⟩ - xStar⟫_ℝ)
            (rsgfPrefixLaw S N) →
          (∫ ζ : RsgfSamplePrefix n Sample N,
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
              ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                  ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                  ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
          ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                  ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                        ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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
                ⟪rsgfResidual S (rsgfPrefixIterate S ζ ⟨k, hk⟩)
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

/-- Source-facing convex conclusion of Theorem 6.3(b), expressed with the
canonical generated iterates and canonical random-output law. -/
theorem theorem_6_3b_convex
    (S : Setup n Sample) (N : ℕ)
    (xStar : Space n)
    (hN : 1 ≤ N)
    (hγ_upper : ∀ k ∈ Icc 1 N, S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹)
    (hPR_source : RsgfOutputPMFSourceChoice S N)
    (hconvex : ConvexOn ℝ Set.univ (objective S))
    (hoptimal : ∀ x : Space n, objective S xStar ≤ objective S x) :
    rsgfSelectedJointExpectationTheorem63 S N hPR_source
      (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) ≤
    convexRsgfBoundNumerator S N xStar /
      (2 * rsgfWeightDenominator S N) := by
  classical
  let hPR : RsgfOutputWeightsAdmissible S N :=
    rsgfOutputPMFSourceChoice_admissible S hPR_source
  have htransport :
      rsgfSelectedJointExpectationTheorem63 S N hPR_source
          (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) =
        rsgfSelectedJointExpectation S N hPR
          (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S) :=
    rsgf_selected_joint_expectation_theorem63_eq_admissible
      S N hPR hPR_source
      (fun R ζ => objective S (rsgfPrefixIterate S ζ R) - fStar S)
  rw [htransport]
  exact
    theorem_6_3b_convex_of_admissible S N xStar hN hγ_upper hPR
      hconvex hoptimal

/-- Product law for the post-optimization empirical-gradient samples. -/
noncomputable def rsgfEvaluationLaw (S : Setup n Sample) (T : ℕ) :
    Measure (RsgfEvaluationPrefix n Sample T) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  exact Measure.pi (fun _ : RsgfOutputIndex T => rsgfZetaLaw S)

/-- Formalization-only full two-phase product law: optimization-run outcomes
and the post-optimization empirical-gradient sample prefix. -/
noncomputable def rsgfTwoPhaseJointLaw_independentProduct (S : Setup n Sample)
    (S_count N T : ℕ) (hN : 1 ≤ N)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    Measure (RsgfOptimizationRuns n Sample S_count N ×
      RsgfEvaluationPrefix n Sample T) :=
  (rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR).prod
    (rsgfEvaluationLaw S T)

/-- Helper-level optimization-phase product law.  The 2-RSGF proof uses a
product factorization across runs, but the book JSON marks this independence
interface as a formalization-only prerequisite rather than a printed source
assumption. -/
noncomputable def rsgfOptimizationPhaseLaw (S : Setup n Sample)
    (S_count N : ℕ) (hPR : RsgfOutputWeightsAdmissible S N) :
    Measure (RsgfOptimizationRuns n Sample S_count N) :=
  Measure.pi (fun _ : Fin S_count =>
    rsgfSelectedRunLawCanonical S N hPR)

/-- Helper-level two-phase product law: independent optimization runs followed
by an independent post-optimization empirical-gradient sample prefix.  This is
not presented as the paper's canonical law because the source does not print
the independence/product-law assumption for 2-RSGF. -/
noncomputable def rsgfTwoPhaseJointLaw (S : Setup n Sample)
    (S_count N T : ℕ) (hPR : RsgfOutputWeightsAdmissible S N) :
    Measure (RsgfOptimizationRuns n Sample S_count N ×
      RsgfEvaluationPrefix n Sample T) :=
  (rsgfOptimizationPhaseLaw S S_count N hPR).prod
    (rsgfEvaluationLaw S T)

/-- Product-law realization of the optimization phase used by the formalized
Theorem 6.4 helper.  This uses the source PMF choice from (6.1.61), but the
run-independence product structure is not printed as a paper assumption. -/
noncomputable def rsgfOptimizationPhaseLawProductRealization (S : Setup n Sample)
    (S_count N : ℕ) (Dtilde : ℝ) (hN : 1 ≤ N)
    (hPR_source : RsgfOutputPMFSourceChoice S N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde) :
    Measure (RsgfOptimizationRuns n Sample S_count N) :=
  Measure.pi (fun _ : Fin S_count =>
    rsgfSelectedRunLawTheorem63 S N hPR_source)

/-- Product-law realization of the two-phase 2-RSGF probability space.  This is
helper-level infrastructure, not the paper's printed theorem boundary. -/
noncomputable def rsgfTwoPhaseJointLawProductRealization (S : Setup n Sample)
    (S_count N T : ℕ) (Dtilde : ℝ) (hN : 1 ≤ N)
    (hPR_source : RsgfOutputPMFSourceChoice S N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde) :
    Measure (RsgfOptimizationRuns n Sample S_count N ×
      RsgfEvaluationPrefix n Sample T) :=
  (rsgfOptimizationPhaseLawProductRealization S S_count N Dtilde hN hPR_source hDtilde hsteps).prod
    (rsgfEvaluationLaw S T)

/-- Threshold displayed in Theorem 6.4(a), equation (6.1.81). -/
def rsgfTheorem64Threshold (S : Setup n Sample)
    (N T : ℕ) (Dtilde lambda : ℝ) : ℝ :=
  8 * S.L * rsgfBbar S N Dtilde +
    3 * ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) +
    (24 * ((n : ℝ) + 4) * lambda / (T : ℝ)) *
      (S.L * rsgfBbar S N Dtilde +
        ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
        S.σ ^ (2 : ℕ))

/-- Failure event in Theorem 6.4(a). -/
def rsgfTheorem64FailureEvent (S : Setup n Sample)
    (S_count N T : ℕ) (Dtilde lambda : ℝ) (hS : 0 < S_count) :
    Set (RsgfOptimizationRuns n Sample S_count N ×
      RsgfEvaluationPrefix n Sample T) :=
  {q |
    ‖∇ (objective S) (rsgfTwoPhaseSelectedOutput S q.1 q.2 hS)‖ ^ (2 : ℕ) ≥
      rsgfTheorem64Threshold S N T Dtilde lambda}

/-- Real-valued probability of the Theorem 6.4(a) failure event under the
formalization-only two-phase independent product law. -/
def rsgfTheorem64FailureProbability (S : Setup n Sample)
    (S_count N T : ℕ) (Dtilde lambda : ℝ) (hS : 0 < S_count)
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N) : ℝ :=
  (rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR).real
    (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS)

/-- Helper-level real-valued probability in Theorem 6.4(a), under the
formalization-only product-law realization and the source constant-stepsize
policy (6.1.70). -/
def rsgfTheorem64FailureProbabilityProductLaw (S : Setup n Sample)
    (S_count N T : ℕ) (Dtilde lambda : ℝ) (hS : 0 < S_count)
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N) : ℝ :=
  (rsgfTwoPhaseJointLaw S S_count N T hPR).real
    (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS)

/-- Real-valued probability in the product-law realization of Theorem 6.4(a). -/
def rsgfTheorem64FailureProbabilityProductRealization (S : Setup n Sample)
    (S_count N T : ℕ) (Dtilde lambda : ℝ) (hS : 0 < S_count)
    (hN : 1 ≤ N) (hPR_source : RsgfOutputPMFSourceChoice S N)
    (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde) : ℝ :=
  (rsgfTwoPhaseJointLawProductRealization S S_count N T Dtilde hN hPR_source hDtilde hsteps).real
    (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS)

/-- The Corollary 6.3 closed-form bound is nonnegative in the nonzero
constant-stepsize regime used by Theorem 6.4. -/
private theorem rsgfBbar_nonneg
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde) :
    0 ≤ rsgfBbar S N Dtilde := by
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  unfold rsgfBbar
  have hterm1 :
      0 ≤ 12 * ((n : ℝ) + 4) * S.L * Df S ^ (2 : ℕ) / (N : ℝ) := by
    have hnum_nonneg :
        0 ≤ 12 * ((n : ℝ) + 4) * S.L * Df S ^ (2 : ℕ) := by
      exact
        mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hn4_pos.le)
            S.L_pos.le)
          (sq_nonneg (Df S))
    exact div_nonneg hnum_nonneg hN_pos.le
  have hcoef_nonneg :
      0 ≤ 4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ) := by
    have hsqrt_n_nonneg : 0 ≤ Real.sqrt ((n : ℝ) + 4) :=
      Real.sqrt_nonneg _
    have hsqrt_N_nonneg : 0 ≤ Real.sqrt (N : ℝ) :=
      Real.sqrt_nonneg _
    have hnum_nonneg :
        0 ≤ 4 * S.σ * Real.sqrt ((n : ℝ) + 4) := by
      exact
        mul_nonneg
          (mul_nonneg (by norm_num) S.σ_nonneg)
          hsqrt_n_nonneg
    exact div_nonneg hnum_nonneg hsqrt_N_nonneg
  have hsum_nonneg :
      0 ≤ Dtilde + Df S ^ (2 : ℕ) / Dtilde := by
    have hfrac_nonneg : 0 ≤ Df S ^ (2 : ℕ) / Dtilde := by
      positivity
    nlinarith [hDtilde.le, hfrac_nonneg]
  have hterm2 :
      0 ≤
        (4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ)) *
          (Dtilde + Df S ^ (2 : ℕ) / Dtilde) :=
    mul_nonneg hcoef_nonneg hsum_nonneg
  nlinarith

/-- The smoothing policy and the source assumption `μ > 0` make the Corollary
6.3 closed-form bound strictly positive.  This supplies the positive threshold
needed by the non-strict Markov inequality in (6.1.78). -/
private theorem rsgfBbar_pos_of_smoothing
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    0 < rsgfBbar S N Dtilde := by
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  have hden_pos :
      0 < ((n : ℝ) + 4) * Real.sqrt (2 * (N : ℝ)) := by
    have htwoN_pos : 0 < 2 * (N : ℝ) := by positivity
    exact mul_pos hn4_pos (Real.sqrt_pos_of_pos htwoN_pos)
  have hDf_div_pos :
      0 < Df S / (((n : ℝ) + 4) * Real.sqrt (2 * (N : ℝ))) :=
    lt_of_lt_of_le S.μ_pos hsmooth
  have hDf_pos : 0 < Df S := by
    exact (div_pos_iff_of_pos_right hden_pos).mp hDf_div_pos
  unfold rsgfBbar
  have hterm1_pos :
      0 < 12 * ((n : ℝ) + 4) * S.L * Df S ^ (2 : ℕ) / (N : ℝ) := by
    have hnum_pos :
        0 < 12 * ((n : ℝ) + 4) * S.L * Df S ^ (2 : ℕ) := by
      exact
        mul_pos
          (mul_pos
            (mul_pos (by norm_num) hn4_pos)
            S.L_pos)
          (pow_pos hDf_pos 2)
    exact div_pos hnum_pos hN_pos
  have hterm2_nonneg :
      0 ≤
        (4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ)) *
          (Dtilde + Df S ^ (2 : ℕ) / Dtilde) := by
    have hsqrt_n_nonneg : 0 ≤ Real.sqrt ((n : ℝ) + 4) :=
      Real.sqrt_nonneg _
    have hsqrt_N_nonneg : 0 ≤ Real.sqrt (N : ℝ) :=
      Real.sqrt_nonneg _
    have hnum_nonneg :
        0 ≤ 4 * S.σ * Real.sqrt ((n : ℝ) + 4) := by
      exact
        mul_nonneg
          (mul_nonneg (by norm_num) S.σ_nonneg)
          hsqrt_n_nonneg
    have hcoef_nonneg :
        0 ≤ 4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ) :=
      div_nonneg hnum_nonneg hsqrt_N_nonneg
    have hfrac_nonneg : 0 ≤ Df S ^ (2 : ℕ) / Dtilde := by
      positivity
    have hsum_nonneg : 0 ≤ Dtilde + Df S ^ (2 : ℕ) / Dtilde := by
      nlinarith [hDtilde.le, hfrac_nonneg]
    exact mul_nonneg hcoef_nonneg hsum_nonneg
  nlinarith

/-- The one-run selected gradient-square observable is integrable under the
admissible selected-run law.  This exposes the integrability already built
inside the Theorem 6.3(a) proof so the Markov tail (6.1.78) can use it. -/
private theorem rsgf_selected_gradient_norm_sq_integrable_of_admissible
    (S : Setup n Sample) {N : ℕ}
    (hN : 1 ≤ N) (hPR : RsgfOutputWeightsAdmissible S N) :
    Integrable
      (fun q : RsgfRunOutcome n Sample N =>
        ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ))
      (rsgfSelectedRunLaw S N hPR) := by
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
  haveI : SFinite (rsgfPrefixLaw S N) := inferInstance
  have hprod_int :
      Integrable
        (fun q : RsgfOutputIndex N × RsgfSamplePrefix n Sample N =>
          ‖∇ (objective S) (rsgfPrefixIterate S q.2 q.1)‖ ^ (2 : ℕ))
        ((rsgfOutputPMF_of_admissible S N hPR).toMeasure.prod
          (rsgfPrefixLaw S N)) :=
    integrable_finite_index_first_prod_of_fiber_integrable
      ((rsgfOutputPMF_of_admissible S N hPR).toMeasure)
      (rsgfPrefixLaw S N)
      (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
      hgrad_int
  simpa [rsgfSelectedRunLaw, rsgfRunCandidate] using hprod_int

/-- Constant-stepsize policy (6.1.70) supplies one positive scalar value on the
whole one-based output window, together with the left-branch upper bound used in
the denominator estimate (6.1.75). -/
private theorem rsgf_constant_stepsize_policy_scalar_facts
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde) :
    ∃ γ0 : ℝ,
      0 < γ0 ∧
        (∀ k ∈ Icc 1 N, S.γ k = γ0) ∧
          γ0 ≤ 1 / (4 * S.L * ((n : ℝ) + 4)) := by
  classical
  have h_one_mem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, hN⟩
  rcases hsteps 1 h_one_mem with ⟨q0, hq0, hγ1⟩
  let den : ℝ := S.σ * Real.sqrt (N : ℝ)
  have hden_ne : den ≠ 0 := by
    simpa [den] using hq0.1
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    nlinarith
  have hn4_nonneg : 0 ≤ (n : ℝ) + 4 := le_of_lt hn4_pos
  have hsqrt_n4_pos : 0 < Real.sqrt ((n : ℝ) + 4) :=
    Real.sqrt_pos_of_pos hn4_pos
  have hsqrt_n4_ne : Real.sqrt ((n : ℝ) + 4) ≠ 0 :=
    ne_of_gt hsqrt_n4_pos
  have hden_nonneg : 0 ≤ den := by
    dsimp [den]
    exact mul_nonneg S.σ_nonneg (Real.sqrt_nonneg _)
  have hden_pos : 0 < den :=
    lt_of_le_of_ne hden_nonneg (Ne.symm hden_ne)
  have hq0_pos : 0 < q0 := by
    have hprod_pos : 0 < q0 * den := by
      simpa [den, hq0.2] using hDtilde
    by_contra hq_nonpos
    have hq_le : q0 ≤ 0 := le_of_not_gt hq_nonpos
    have hprod_le : q0 * den ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hq_le hden_pos.le
    linarith
  have hpref_pos : 0 < 1 / Real.sqrt ((n : ℝ) + 4) :=
    one_div_pos.mpr hsqrt_n4_pos
  have hleft_branch_pos :
      0 < 1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4)) := by
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) S.L_pos) hsqrt_n4_pos)
  have hmin_pos :
      0 < min (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) q0 :=
    lt_min hleft_branch_pos hq0_pos
  have hγ0_pos : 0 < S.γ 1 := by
    rw [hγ1]
    exact mul_pos hpref_pos hmin_pos
  have hconst : ∀ k ∈ Icc 1 N, S.γ k = S.γ 1 := by
    intro k hk
    rcases hsteps k hk with ⟨qk, hqk, hγk⟩
    have hq_eq : qk = q0 := by
      have hmul_eq : qk * den = q0 * den := by
        simpa [den] using hqk.2.trans hq0.2.symm
      exact mul_right_cancel₀ hden_ne hmul_eq
    rw [hγk, hγ1, hq_eq]
  have hupper : S.γ 1 ≤ 1 / (4 * S.L * ((n : ℝ) + 4)) := by
    have hpref_nonneg : 0 ≤ 1 / Real.sqrt ((n : ℝ) + 4) :=
      le_of_lt hpref_pos
    have hraw :
        S.γ 1 ≤
          (1 / Real.sqrt ((n : ℝ) + 4)) *
            (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) := by
      rw [hγ1]
      exact
        mul_le_mul_of_nonneg_left
          (min_le_left
            (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) q0)
          hpref_nonneg
    have hbranch_eq :
        (1 / Real.sqrt ((n : ℝ) + 4)) *
            (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) =
          1 / (4 * S.L * ((n : ℝ) + 4)) := by
      field_simp [hsqrt_n4_ne, ne_of_gt S.L_pos]
      exact (Real.sq_sqrt hn4_nonneg).symm
    calc
      S.γ 1 ≤
          (1 / Real.sqrt ((n : ℝ) + 4)) *
            (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) := hraw
      _ = 1 / (4 * S.L * ((n : ℝ) + 4)) := hbranch_eq
  exact ⟨S.γ 1, hγ0_pos, hconst, hupper⟩

/-- Finite-sum identities for a constant RSGF stepsize on the one-based output
window.  These are the sum rewrites used in the Corollary 6.3 specialization. -/
private theorem rsgf_constant_stepsize_sum_identities
    (S : Setup n Sample) {N : ℕ} {γ0 : ℝ}
    (hN : 1 ≤ N)
    (hγ_const : ∀ k ∈ Icc 1 N, S.γ k = γ0) :
    Finset.sum (Icc 1 N) S.γ = (N : ℝ) * γ0 ∧
      Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) =
        (N : ℝ) * γ0 ^ (2 : ℕ) ∧
      Finset.sum (Icc 1 N)
          (fun k => S.γ k / 4 + S.L * S.γ k ^ (2 : ℕ)) =
        (N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ)) := by
  classical
  have hcard : ((Icc 1 N).card : ℝ) = (N : ℝ) := by
    simp
  have hsumγ :
      Finset.sum (Icc 1 N) S.γ = (N : ℝ) * γ0 := by
    calc
      Finset.sum (Icc 1 N) S.γ =
          Finset.sum (Icc 1 N) (fun _ : ℕ => γ0) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hγ_const k hk
      _ = (N : ℝ) * γ0 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [hcard]
  have hsumγsq :
      Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) =
        (N : ℝ) * γ0 ^ (2 : ℕ) := by
    calc
      Finset.sum (Icc 1 N) (fun k => S.γ k ^ (2 : ℕ)) =
          Finset.sum (Icc 1 N) (fun _ : ℕ => γ0 ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hγ_const k hk]
      _ = (N : ℝ) * γ0 ^ (2 : ℕ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [hcard]
  have hsum_mix :
      Finset.sum (Icc 1 N)
          (fun k => S.γ k / 4 + S.L * S.γ k ^ (2 : ℕ)) =
        (N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ)) := by
    calc
      Finset.sum (Icc 1 N)
          (fun k => S.γ k / 4 + S.L * S.γ k ^ (2 : ℕ)) =
          Finset.sum (Icc 1 N)
            (fun _ : ℕ => γ0 / 4 + S.L * γ0 ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [hγ_const k hk]
      _ = (N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            rw [hcard]
  exact ⟨hsumγ, hsumγsq, hsum_mix⟩

/-- Denominator lower bound (6.1.75) for a positive constant stepsize satisfying
the left-branch Corollary 6.3 upper bound. -/
private theorem rsgf_constant_stepsize_weight_denominator_lower_bound
    (S : Setup n Sample) {N : ℕ} {γ0 : ℝ}
    (hN : 1 ≤ N)
    (hγ_pos : 0 < γ0)
    (hγ_const : ∀ k ∈ Icc 1 N, S.γ k = γ0)
    (hγ_upper : γ0 ≤ 1 / (4 * S.L * ((n : ℝ) + 4))) :
    (N : ℝ) * γ0 / 2 ≤ rsgfWeightDenominator S N := by
  classical
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    nlinarith
  have hscale_pos : 0 < 2 * S.L * ((n : ℝ) + 4) := by
    exact mul_pos (mul_pos (by norm_num) S.L_pos) hn4_pos
  have hscale_le_half :
      2 * S.L * ((n : ℝ) + 4) * γ0 ≤ 1 / 2 := by
    have hmul :=
      mul_le_mul_of_nonneg_left hγ_upper (le_of_lt hscale_pos)
    have hbranch :
        2 * S.L * ((n : ℝ) + 4) *
            (1 / (4 * S.L * ((n : ℝ) + 4))) =
          1 / 2 := by
      field_simp [ne_of_gt S.L_pos, ne_of_gt hn4_pos]
      ring
    calc
      2 * S.L * ((n : ℝ) + 4) * γ0 ≤
          2 * S.L * ((n : ℝ) + 4) *
            (1 / (4 * S.L * ((n : ℝ) + 4))) := hmul
      _ = 1 / 2 := hbranch
  have hweight_point :
      ∀ k ∈ Icc 1 N, γ0 / 2 ≤ rsgfWeightNumerator S k := by
    intro k hk
    have hfactor : 1 / 2 ≤
        1 - 2 * S.L * ((n : ℝ) + 4) * γ0 := by
      nlinarith
    have hmul :
        γ0 * (1 / 2) ≤
          γ0 * (1 - 2 * S.L * ((n : ℝ) + 4) * γ0) :=
      mul_le_mul_of_nonneg_left hfactor (le_of_lt hγ_pos)
    have hrewrite :
        rsgfWeightNumerator S k =
          γ0 * (1 - 2 * S.L * ((n : ℝ) + 4) * γ0) := by
      unfold rsgfWeightNumerator
      rw [hγ_const k hk]
      ring
    calc
      γ0 / 2 = γ0 * (1 / 2) := by ring
      _ ≤ γ0 * (1 - 2 * S.L * ((n : ℝ) + 4) * γ0) := hmul
      _ = rsgfWeightNumerator S k := hrewrite.symm
  have hsum_lower :
      Finset.sum (Icc 1 N) (fun _ : ℕ => γ0 / 2) ≤
        rsgfWeightDenominator S N := by
    unfold rsgfWeightDenominator
    exact Finset.sum_le_sum hweight_point
  have hconst_sum :
      Finset.sum (Icc 1 N) (fun _ : ℕ => γ0 / 2) =
        (N : ℝ) * γ0 / 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Icc 1 N).card : ℝ) = (N : ℝ) := by
      simp
    rw [hcard]
    ring
  calc
    (N : ℝ) * γ0 / 2 =
        Finset.sum (Icc 1 N) (fun _ : ℕ => γ0 / 2) := hconst_sum.symm
    _ ≤ rsgfWeightDenominator S N := hsum_lower

/-- Corollary 6.3 source step 3: after evaluating the constant-step finite sums
and using the denominator lower bound (6.1.75), the Theorem 6.3 numerator over
the actual output-weight denominator is bounded by the printed constant-γ
prebound. -/
private theorem rsgf_nonconvex_numerator_over_weight_constant_stepsize_prebound
    (S : Setup n Sample) {N : ℕ} {γ0 : ℝ}
    (hN : 1 ≤ N)
    (hγ_pos : 0 < γ0)
    (hγ_const : ∀ k ∈ Icc 1 N, S.γ k = γ0)
    (hden_lower : (N : ℝ) * γ0 / 2 ≤ rsgfWeightDenominator S N)
    (hPR : RsgfOutputWeightsAdmissible S N) :
    nonconvexRsgfBoundNumerator S N /
        rsgfWeightDenominator S N ≤
      (2 * Df S ^ (2 : ℕ) + 4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) /
          ((N : ℝ) * γ0) +
        S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (3 : ℕ) +
          4 * ((n : ℝ) + 4) *
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                ((n : ℝ) + 4) ^ (2 : ℕ) +
              S.σ ^ (2 : ℕ)) * γ0 := by
  classical
  rcases rsgf_constant_stepsize_sum_identities S hN hγ_const with
    ⟨_hsumγ, hsumγsq, hsum_mix⟩
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hhalf_den_pos : 0 < (N : ℝ) * γ0 / 2 := by
    positivity
  have hweight_den_pos : 0 < rsgfWeightDenominator S N :=
    rsgfWeightDenominator_pos S hPR
  have hnum_expand :
      nonconvexRsgfBoundNumerator S N =
        Df S ^ (2 : ℕ) +
          2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) *
            (1 + S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
              ((N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ)))) +
          2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) *
            ((N : ℝ) * γ0 ^ (2 : ℕ)) := by
    unfold nonconvexRsgfBoundNumerator
    rw [hsum_mix, hsumγsq]
  have hnum_nonneg : 0 ≤ nonconvexRsgfBoundNumerator S N := by
    rw [hnum_expand]
    have hn4_nonneg : 0 ≤ (n : ℝ) + 4 := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by
        exact_mod_cast Nat.zero_le n
      nlinarith
    have hmix_nonneg : 0 ≤ γ0 / 4 + S.L * γ0 ^ (2 : ℕ) := by
      have hγ_div_nonneg : 0 ≤ γ0 / 4 := by positivity
      have hγsq_nonneg : 0 ≤ S.L * γ0 ^ (2 : ℕ) :=
        mul_nonneg (le_of_lt S.L_pos) (sq_nonneg γ0)
      nlinarith
    have hinside_nonneg :
        0 ≤
          1 + S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
            ((N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ))) := by
      have htail_nonneg :
          0 ≤ S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
            ((N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ))) := by
        have hleft_nonneg :
            0 ≤ S.L * ((n : ℝ) + 4) ^ (2 : ℕ) :=
          mul_nonneg (le_of_lt S.L_pos) (sq_nonneg ((n : ℝ) + 4))
        have hright_nonneg :
            0 ≤ (N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ)) :=
          mul_nonneg (le_of_lt hN_pos) hmix_nonneg
        exact mul_nonneg hleft_nonneg hright_nonneg
      nlinarith
    have hterm2_nonneg :
        0 ≤ 2 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) *
          (1 + S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
            ((N : ℝ) * (γ0 / 4 + S.L * γ0 ^ (2 : ℕ)))) := by
      positivity
    have hterm3_nonneg :
        0 ≤ 2 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) *
          ((N : ℝ) * γ0 ^ (2 : ℕ)) := by
      positivity
    nlinarith [sq_nonneg (Df S), hterm2_nonneg, hterm3_nonneg]
  have hdiv_den :
      nonconvexRsgfBoundNumerator S N /
          rsgfWeightDenominator S N ≤
        nonconvexRsgfBoundNumerator S N / ((N : ℝ) * γ0 / 2) := by
    exact
      div_le_div_of_nonneg_left hnum_nonneg hhalf_den_pos hden_lower
  have hpre_eval :
      nonconvexRsgfBoundNumerator S N / ((N : ℝ) * γ0 / 2) =
        (2 * Df S ^ (2 : ℕ) + 4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) /
            ((N : ℝ) * γ0) +
          S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (3 : ℕ) +
            4 * ((n : ℝ) + 4) *
              (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                  ((n : ℝ) + 4) ^ (2 : ℕ) +
                S.σ ^ (2 : ℕ)) * γ0 := by
    rw [hnum_expand]
    field_simp [ne_of_gt hN_pos, ne_of_gt hγ_pos]
    ring
  exact le_trans hdiv_den (le_of_eq hpre_eval)

/-- Squared form of the smoothing restriction (6.1.71). -/
private theorem rsgf_smoothing_parameter_sq_bound
    (S : Setup n Sample) {N : ℕ}
    (hN : 1 ≤ N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    S.μ ^ (2 : ℕ) ≤
      Df S ^ (2 : ℕ) /
        (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ))) := by
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by
      exact_mod_cast Nat.zero_le n
    nlinarith
  let den : ℝ := ((n : ℝ) + 4) * Real.sqrt (2 * (N : ℝ))
  have hsqrt_pos : 0 < Real.sqrt (2 * (N : ℝ)) := by
    exact Real.sqrt_pos_of_pos (by positivity)
  have hden_pos : 0 < den := by
    dsimp [den]
    exact mul_pos hn4_pos hsqrt_pos
  have hsmooth_unfold : S.μ ≤ Df S / den := by
    simpa [RsgfSmoothingParameterPolicy, rsgfSmoothingParameterBound, den] using
      hsmooth
  have hbound_pos : 0 < Df S / den :=
    lt_of_lt_of_le S.μ_pos hsmooth_unfold
  have hsq_le : S.μ ^ (2 : ℕ) ≤ (Df S / den) ^ (2 : ℕ) := by
    nlinarith [hsmooth_unfold, S.μ_pos, hbound_pos]
  have hden_sq :
      den ^ (2 : ℕ) =
        ((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)) := by
    dsimp [den]
    have htwoN_nonneg : 0 ≤ 2 * (N : ℝ) := by positivity
    rw [mul_pow, Real.sq_sqrt htwoN_nonneg]
  have hbound_sq :
      (Df S / den) ^ (2 : ℕ) =
        Df S ^ (2 : ℕ) /
          (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ))) := by
    rw [div_pow, hden_sq]
  exact le_trans hsq_le (le_of_eq hbound_sq)

/-- Constant-stepsize policy branch controls from the explicit minimum in
(6.1.70).  The first inequality is the reciprocal replacement used in
Corollary 6.3 step 4; the second is the direct right-branch bound for the
`sigma^2 * gamma` term. -/
private theorem rsgf_constant_stepsize_policy_branch_bounds
    (S : Setup n Sample) {N : ℕ} {Dtilde γ0 : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hγ_const : ∀ k ∈ Icc 1 N, S.γ k = γ0) :
    1 / γ0 ≤
        4 * S.L * ((n : ℝ) + 4) +
          S.σ * Real.sqrt ((n : ℝ) + 4) * Real.sqrt (N : ℝ) / Dtilde ∧
      4 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) * γ0 ≤
        4 * S.σ * Real.sqrt ((n : ℝ) + 4) * Dtilde /
          Real.sqrt (N : ℝ) := by
  classical
  have h_one_mem : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl, hN⟩
  rcases hsteps 1 h_one_mem with ⟨q, hq, hγ1⟩
  have hγ0_eq :
      γ0 =
        (1 / Real.sqrt ((n : ℝ) + 4)) *
          min (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) q := by
    exact (hγ_const 1 h_one_mem).symm.trans hγ1
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have ha_pos : 0 < (n : ℝ) + 4 := by
    nlinarith
  have ha_nonneg : 0 ≤ (n : ℝ) + 4 := le_of_lt ha_pos
  have hsqrt_a_pos : 0 < Real.sqrt ((n : ℝ) + 4) :=
    Real.sqrt_pos_of_pos ha_pos
  have hsqrt_a_ne : Real.sqrt ((n : ℝ) + 4) ≠ 0 :=
    ne_of_gt hsqrt_a_pos
  have hsqrt_N_pos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos_of_pos hN_pos
  have hsqrt_N_ne : Real.sqrt (N : ℝ) ≠ 0 :=
    ne_of_gt hsqrt_N_pos
  have hden_ne : S.σ * Real.sqrt (N : ℝ) ≠ 0 := hq.1
  have hσ_ne : S.σ ≠ 0 := by
    intro hσ_zero
    apply hden_ne
    simp [hσ_zero]
  have hσ_pos : 0 < S.σ :=
    lt_of_le_of_ne S.σ_nonneg (Ne.symm hσ_ne)
  have hden_pos : 0 < S.σ * Real.sqrt (N : ℝ) :=
    mul_pos hσ_pos hsqrt_N_pos
  have hq_pos : 0 < q := by
    have hprod_pos : 0 < q * (S.σ * Real.sqrt (N : ℝ)) := by
      simpa [hq.2] using hDtilde
    by_contra hq_nonpos
    have hq_le : q ≤ 0 := le_of_not_gt hq_nonpos
    have hprod_le : q * (S.σ * Real.sqrt (N : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hq_le hden_pos.le
    linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hDtilde_ne : Dtilde ≠ 0 := ne_of_gt hDtilde
  have hpref_nonneg : 0 ≤ 1 / Real.sqrt ((n : ℝ) + 4) :=
    (one_div_pos.mpr hsqrt_a_pos).le
  have hleft_pos :
      0 < 1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4)) := by
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) S.L_pos) hsqrt_a_pos)
  have hleft_ne :
      1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4)) ≠ 0 :=
    ne_of_gt hleft_pos
  have hfourLa_nonneg :
      0 ≤ 4 * S.L * ((n : ℝ) + 4) := by
    exact mul_nonneg (mul_nonneg (by norm_num) S.L_pos.le) ha_pos.le
  have hsigma_branch_nonneg :
      0 ≤ S.σ * Real.sqrt ((n : ℝ) + 4) * Real.sqrt (N : ℝ) / Dtilde := by
    positivity
  have hrecip :
      1 / γ0 ≤
        4 * S.L * ((n : ℝ) + 4) +
          S.σ * Real.sqrt ((n : ℝ) + 4) * Real.sqrt (N : ℝ) / Dtilde := by
    by_cases hleft_le_q :
        1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4)) ≤ q
    · have hmin_eq :
          min (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) q =
            1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4)) :=
        min_eq_left hleft_le_q
      have hγ0_left :
          γ0 = 1 / (4 * S.L * ((n : ℝ) + 4)) := by
        rw [hγ0_eq, hmin_eq]
        field_simp [hsqrt_a_ne, ne_of_gt S.L_pos]
        exact (Real.sq_sqrt ha_nonneg).symm
      have hrecip_eq :
          1 / γ0 = 4 * S.L * ((n : ℝ) + 4) := by
        rw [hγ0_left]
        field_simp [ne_of_gt S.L_pos, ne_of_gt ha_pos]
      rw [hrecip_eq]
      nlinarith [hsigma_branch_nonneg]
    · have hq_le_left :
          q ≤ 1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4)) :=
        le_of_lt (lt_of_not_ge hleft_le_q)
      have hmin_eq :
          min (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) q = q :=
        min_eq_right hq_le_left
      have hγ0_right :
          γ0 = (1 / Real.sqrt ((n : ℝ) + 4)) * q := by
        rw [hγ0_eq, hmin_eq]
      have hrecip_eq :
          1 / γ0 =
            S.σ * Real.sqrt ((n : ℝ) + 4) * Real.sqrt (N : ℝ) /
              Dtilde := by
        rw [hγ0_right]
        field_simp [hsqrt_a_ne, hq_ne, hDtilde_ne]
        rw [← hq.2]
        ring
      rw [hrecip_eq]
      nlinarith [hfourLa_nonneg]
  have hγ0_le_right :
      γ0 ≤ (1 / Real.sqrt ((n : ℝ) + 4)) * q := by
    rw [hγ0_eq]
    exact
      mul_le_mul_of_nonneg_left
        (min_le_right
          (1 / (4 * S.L * Real.sqrt ((n : ℝ) + 4))) q)
        hpref_nonneg
  have hcoef_nonneg :
      0 ≤ 4 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) := by
    positivity
  have hright_mul_le :
      4 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) * γ0 ≤
        4 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) *
          ((1 / Real.sqrt ((n : ℝ) + 4)) * q) :=
    mul_le_mul_of_nonneg_left hγ0_le_right hcoef_nonneg
  have hright_eq :
      4 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) *
          ((1 / Real.sqrt ((n : ℝ) + 4)) * q) =
        4 * S.σ * Real.sqrt ((n : ℝ) + 4) * Dtilde /
          Real.sqrt (N : ℝ) := by
    field_simp [hsqrt_a_ne, hsqrt_N_ne]
    rw [← hq.2]
    rw [Real.sq_sqrt ha_nonneg]
    ring
  exact ⟨hrecip, le_trans hright_mul_le (le_of_eq hright_eq)⟩

/-- Pure real `L * D_f^2 / N` relaxation used in Corollary 6.3, proof
steps 6-7. -/
private theorem rsgf_corollary_63_final_L_terms
    {a N L F : ℝ} (ha : 4 ≤ a) (hN : 1 ≤ N) (hL : 0 ≤ L) (hF : 0 ≤ F) :
    2 * F * (1 + 1 / (a * N)) / N * (4 * L * a) +
        L * F * a / (2 * N) + L * F / (2 * N) ≤
      12 * a * L * F / N := by
  have ha_pos : 0 < a := by nlinarith
  have hN_pos : 0 < N := by nlinarith
  have hLF_nonneg : 0 ≤ L * F := mul_nonneg hL hF
  have hrecipN_le_one : 1 / N ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hN
    simpa using h
  have hbracket :
      8 * a + 8 / N + a / 2 + 1 / 2 ≤ 12 * a := by
    have h8N : 8 / N ≤ 8 := by
      have h :=
        mul_le_mul_of_nonneg_left hrecipN_le_one
          (by norm_num : (0 : ℝ) ≤ 8)
      simpa [div_eq_mul_inv] using h
    have h8_le : 8 ≤ 2 * a := by nlinarith
    have hhalf_le : 1 / 2 ≤ a / 2 := by nlinarith
    nlinarith
  calc
    2 * F * (1 + 1 / (a * N)) / N * (4 * L * a) +
        L * F * a / (2 * N) + L * F / (2 * N)
        = (L * F / N) * (8 * a + 8 / N + a / 2 + 1 / 2) := by
          field_simp [ne_of_gt ha_pos, ne_of_gt hN_pos]
          ring
    _ ≤ (L * F / N) * (12 * a) := by
          exact mul_le_mul_of_nonneg_left hbracket (div_nonneg hLF_nonneg hN_pos.le)
    _ = 12 * a * L * F / N := by ring

/-- Pure real sigma/square-root relaxation used in Corollary 6.3, proof
steps 6-7. -/
private theorem rsgf_corollary_63_final_sigma_terms
    {a N σ F D sqrtA sqrtN : ℝ}
    (ha : 1 ≤ a) (hN : 1 ≤ N) (hσ : 0 ≤ σ) (hF : 0 ≤ F)
    (hsqrtA : 0 ≤ sqrtA) (hD : 0 < D) (hsqrtN_pos : 0 < sqrtN)
    (hsqrtN_sq : sqrtN ^ (2 : ℕ) = N) :
    2 * F * (1 + 1 / (a * N)) / N * (σ * sqrtA * sqrtN / D) +
        4 * σ * sqrtA * D / sqrtN ≤
      (4 * σ * sqrtA / sqrtN) * (D + F / D) := by
  have ha_pos : 0 < a := by nlinarith
  have hN_pos : 0 < N := by nlinarith
  have haN_ge_one : 1 ≤ a * N := by
    simpa using
      mul_le_mul ha hN (by nlinarith : 0 ≤ (1 : ℝ)) (by nlinarith : 0 ≤ a)
  have hbracket : 1 + 1 / (a * N) ≤ 2 := by
    have hrecip : 1 / (a * N) ≤ 1 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) haN_ge_one
      simpa using h
    nlinarith
  have hcoef_nonneg :
      0 ≤ 2 * F / N * (σ * sqrtA * sqrtN / D) := by
    positivity
  have hfirst :
      2 * F * (1 + 1 / (a * N)) / N * (σ * sqrtA * sqrtN / D) ≤
        (4 * σ * sqrtA / sqrtN) * (F / D) := by
    calc
      2 * F * (1 + 1 / (a * N)) / N * (σ * sqrtA * sqrtN / D)
          = (1 + 1 / (a * N)) * (2 * F / N * (σ * sqrtA * sqrtN / D)) := by
            ring
      _ ≤ 2 * (2 * F / N * (σ * sqrtA * sqrtN / D)) := by
            exact mul_le_mul_of_nonneg_right hbracket hcoef_nonneg
      _ = (4 * σ * sqrtA / sqrtN) * (F / D) := by
            rw [← hsqrtN_sq]
            field_simp [ne_of_gt hD, ne_of_gt hsqrtN_pos]
            ring
  calc
    2 * F * (1 + 1 / (a * N)) / N * (σ * sqrtA * sqrtN / D) +
        4 * σ * sqrtA * D / sqrtN
        ≤ (4 * σ * sqrtA / sqrtN) * (F / D) +
            4 * σ * sqrtA * D / sqrtN := by
          exact add_le_add hfirst le_rfl
    _ = (4 * σ * sqrtA / sqrtN) * (D + F / D) := by ring

/-- Combines the two Corollary 6.3 final-relaxation branches after the source
proof's product expansion. -/
private theorem rsgf_corollary_63_final_terms_of_branches
    {a N L σ F D sqrtA sqrtN : ℝ}
    (hL_terms :
      2 * F * (1 + 1 / (a * N)) / N * (4 * L * a) +
          L * F * a / (2 * N) + L * F / (2 * N) ≤
        12 * a * L * F / N)
    (hSigma_terms :
      2 * F * (1 + 1 / (a * N)) / N * (σ * sqrtA * sqrtN / D) +
          4 * σ * sqrtA * D / sqrtN ≤
        (4 * σ * sqrtA / sqrtN) * (D + F / D)) :
    (2 * F * (1 + 1 / (a * N)) / N) *
        (4 * L * a + σ * sqrtA * sqrtN / D) +
      L * F * a / (2 * N) + L * F / (2 * N) +
        4 * σ * sqrtA * D / sqrtN ≤
      12 * a * L * F / N +
        (4 * σ * sqrtA / sqrtN) * (D + F / D) := by
  calc
    (2 * F * (1 + 1 / (a * N)) / N) *
        (4 * L * a + σ * sqrtA * sqrtN / D) +
      L * F * a / (2 * N) + L * F / (2 * N) +
        4 * σ * sqrtA * D / sqrtN
        =
      (2 * F * (1 + 1 / (a * N)) / N * (4 * L * a) +
          L * F * a / (2 * N) + L * F / (2 * N)) +
        (2 * F * (1 + 1 / (a * N)) / N *
            (σ * sqrtA * sqrtN / D) +
          4 * σ * sqrtA * D / sqrtN) := by ring
    _ ≤
      12 * a * L * F / N +
        (4 * σ * sqrtA / sqrtN) * (D + F / D) :=
      add_le_add hL_terms hSigma_terms

/-- Scalar specialization in Corollary 6.3, (6.1.70)-(6.1.72): under the
constant-stepsize and smoothing policies, the Theorem 6.3(a) numerator divided
by the output-weight denominator is bounded by the closed form `Bbar`. -/
private theorem rsgf_constant_stepsize_corollary_6_3_scalar_bound
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    nonconvexRsgfBoundNumerator S N /
        rsgfWeightDenominator S N ≤
      rsgfBbar S N Dtilde := by
  classical
  -- Source proof: Corollary 6.3, (6.1.70)-(6.1.72), specializes the
  -- Theorem 6.3 numerator/denominator using the constant stepsize minimum,
  -- the denominator lower bound (6.1.75), and the smoothing restriction (6.1.71).
  rcases rsgf_constant_stepsize_policy_scalar_facts S hN hDtilde hsteps with
    ⟨γ0, hγ0_pos, hγ_const, hγ_upper⟩
  have hden_lower :
      (N : ℝ) * γ0 / 2 ≤ rsgfWeightDenominator S N :=
    rsgf_constant_stepsize_weight_denominator_lower_bound
      S hN hγ0_pos hγ_const hγ_upper
  have hprebound :
      nonconvexRsgfBoundNumerator S N /
          rsgfWeightDenominator S N ≤
        (2 * Df S ^ (2 : ℕ) + 4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) /
            ((N : ℝ) * γ0) +
          S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (3 : ℕ) +
            4 * ((n : ℝ) + 4) *
              (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                  ((n : ℝ) + 4) ^ (2 : ℕ) +
                S.σ ^ (2 : ℕ)) * γ0 :=
    rsgf_nonconvex_numerator_over_weight_constant_stepsize_prebound
      S hN hγ0_pos hγ_const hden_lower hPR
  have hμsq :
      S.μ ^ (2 : ℕ) ≤
        Df S ^ (2 : ℕ) /
          (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ))) :=
    rsgf_smoothing_parameter_sq_bound S hN hsmooth
  rcases
      rsgf_constant_stepsize_policy_branch_bounds
        S hN hDtilde hsteps hγ_const with
    ⟨hγ_recip, hσ_branch⟩
  have hscalar :
      (2 * Df S ^ (2 : ℕ) + 4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) /
            ((N : ℝ) * γ0) +
          S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (3 : ℕ) +
            4 * ((n : ℝ) + 4) *
              (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                  ((n : ℝ) + 4) ^ (2 : ℕ) +
                S.σ ^ (2 : ℕ)) * γ0 ≤
        rsgfBbar S N Dtilde := by
    have hN_pos : 0 < (N : ℝ) := by
      exact_mod_cast hN
    have ha_pos : 0 < (n : ℝ) + 4 := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by
        exact_mod_cast Nat.zero_le n
      nlinarith
    have ha_nonneg : 0 ≤ (n : ℝ) + 4 := ha_pos.le
    have hmu_num :
        4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) ≤
          2 * Df S ^ (2 : ℕ) / (((n : ℝ) + 4) * (N : ℝ)) := by
      have hcoef_nonneg : 0 ≤ 4 * ((n : ℝ) + 4) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_left hμsq hcoef_nonneg
      calc
        4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) =
            4 * ((n : ℝ) + 4) * S.μ ^ (2 : ℕ) := by ring
        _ ≤
            4 * ((n : ℝ) + 4) *
              (Df S ^ (2 : ℕ) /
                (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) := hmul
        _ = 2 * Df S ^ (2 : ℕ) / (((n : ℝ) + 4) * (N : ℝ)) := by
            field_simp [ne_of_gt ha_pos, ne_of_gt hN_pos]
            ring
    have hnum_bound :
        2 * Df S ^ (2 : ℕ) + 4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) ≤
          2 * Df S ^ (2 : ℕ) *
            (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) := by
      calc
        2 * Df S ^ (2 : ℕ) + 4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) ≤
            2 * Df S ^ (2 : ℕ) +
              2 * Df S ^ (2 : ℕ) / (((n : ℝ) + 4) * (N : ℝ)) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hmu_num (2 * Df S ^ (2 : ℕ))
        _ =
            2 * Df S ^ (2 : ℕ) *
              (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) := by ring
    have hmu_L3 :
        S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (3 : ℕ) ≤
          S.L * Df S ^ (2 : ℕ) * ((n : ℝ) + 4) /
            (2 * (N : ℝ)) := by
      have hcoef_nonneg :
          0 ≤ S.L * ((n : ℝ) + 4) ^ (3 : ℕ) := by
        exact mul_nonneg S.L_pos.le (pow_nonneg ha_nonneg 3)
      have hmul := mul_le_mul_of_nonneg_left hμsq hcoef_nonneg
      calc
        S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (3 : ℕ) =
            S.L * ((n : ℝ) + 4) ^ (3 : ℕ) * S.μ ^ (2 : ℕ) := by ring
        _ ≤
            S.L * ((n : ℝ) + 4) ^ (3 : ℕ) *
              (Df S ^ (2 : ℕ) /
                (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) := hmul
        _ =
            S.L * Df S ^ (2 : ℕ) * ((n : ℝ) + 4) /
              (2 * (N : ℝ)) := by
            field_simp [ne_of_gt ha_pos, ne_of_gt hN_pos]
    have hmu_L2 :
        S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (2 : ℕ) ≤
          S.L * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) := by
      have hcoef_nonneg :
          0 ≤ S.L * ((n : ℝ) + 4) ^ (2 : ℕ) := by
        exact mul_nonneg S.L_pos.le (pow_nonneg ha_nonneg 2)
      have hmul := mul_le_mul_of_nonneg_left hμsq hcoef_nonneg
      calc
        S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (2 : ℕ) =
            S.L * ((n : ℝ) + 4) ^ (2 : ℕ) * S.μ ^ (2 : ℕ) := by ring
        _ ≤
            S.L * ((n : ℝ) + 4) ^ (2 : ℕ) *
              (Df S ^ (2 : ℕ) /
                (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) := hmul
        _ = S.L * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) := by
            field_simp [ne_of_gt ha_pos, ne_of_gt hN_pos]
    have hmu_gamma :
        4 * ((n : ℝ) + 4) *
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (2 : ℕ)) * γ0 ≤
          S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (2 : ℕ) := by
      have hcoef_nonneg :
          0 ≤
            4 * ((n : ℝ) + 4) *
              (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                ((n : ℝ) + 4) ^ (2 : ℕ)) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_left hγ_upper hcoef_nonneg
      calc
        4 * ((n : ℝ) + 4) *
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (2 : ℕ)) * γ0 ≤
            4 * ((n : ℝ) + 4) *
              (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                ((n : ℝ) + 4) ^ (2 : ℕ)) *
                (1 / (4 * S.L * ((n : ℝ) + 4))) := hmul
        _ =
            S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (2 : ℕ) := by
            field_simp [ne_of_gt S.L_pos, ne_of_gt ha_pos]
    have hmu_gamma_smooth :
        4 * ((n : ℝ) + 4) *
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
              ((n : ℝ) + 4) ^ (2 : ℕ)) * γ0 ≤
          S.L * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) :=
      le_trans hmu_gamma hmu_L2
    have hA_nonneg :
        0 ≤
          2 * Df S ^ (2 : ℕ) +
            4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4) := by
      have hF_nonneg : 0 ≤ Df S ^ (2 : ℕ) := sq_nonneg (Df S)
      have hmu_nonneg : 0 ≤ S.μ ^ (2 : ℕ) := sq_nonneg S.μ
      nlinarith
        [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hmu_nonneg)
          ha_nonneg]
    have hAoverN_le :
        (2 * Df S ^ (2 : ℕ) +
              4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) / (N : ℝ) ≤
          (2 * Df S ^ (2 : ℕ) *
              (1 + 1 / (((n : ℝ) + 4) * (N : ℝ)))) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right hnum_bound hN_pos.le
    have hAoverN_nonneg :
        0 ≤
          (2 * Df S ^ (2 : ℕ) +
              4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) / (N : ℝ) := by
      exact div_nonneg hA_nonneg hN_pos.le
    have hBoverN_nonneg :
        0 ≤
          (2 * Df S ^ (2 : ℕ) *
              (1 + 1 / (((n : ℝ) + 4) * (N : ℝ)))) / (N : ℝ) :=
      le_trans hAoverN_nonneg hAoverN_le
    have hrecip_nonneg : 0 ≤ 1 / γ0 := by
      positivity
    have hfirst_bound :
        (2 * Df S ^ (2 : ℕ) +
              4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) /
            ((N : ℝ) * γ0) ≤
          (2 * Df S ^ (2 : ℕ) *
              (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) / (N : ℝ)) *
            (4 * S.L * ((n : ℝ) + 4) +
              S.σ * Real.sqrt ((n : ℝ) + 4) * Real.sqrt (N : ℝ) /
                Dtilde) := by
      calc
        (2 * Df S ^ (2 : ℕ) +
              4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) /
            ((N : ℝ) * γ0) =
            ((2 * Df S ^ (2 : ℕ) +
                4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) / (N : ℝ)) *
              (1 / γ0) := by
            field_simp [ne_of_gt hN_pos, ne_of_gt hγ0_pos]
        _ ≤
            (2 * Df S ^ (2 : ℕ) *
                (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) / (N : ℝ)) *
              (4 * S.L * ((n : ℝ) + 4) +
                S.σ * Real.sqrt ((n : ℝ) + 4) * Real.sqrt (N : ℝ) /
                  Dtilde) := by
            exact
              mul_le_mul hAoverN_le hγ_recip hrecip_nonneg
                hBoverN_nonneg
    have hthird_split :
        4 * ((n : ℝ) + 4) *
            (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                ((n : ℝ) + 4) ^ (2 : ℕ) +
              S.σ ^ (2 : ℕ)) * γ0 =
          4 * ((n : ℝ) + 4) *
              (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                ((n : ℝ) + 4) ^ (2 : ℕ)) * γ0 +
            4 * ((n : ℝ) + 4) * S.σ ^ (2 : ℕ) * γ0 := by
      ring
    have hsource_step5 :
        (2 * Df S ^ (2 : ℕ) +
              4 * S.μ ^ (2 : ℕ) * ((n : ℝ) + 4)) /
              ((N : ℝ) * γ0) +
            S.μ ^ (2 : ℕ) * S.L * ((n : ℝ) + 4) ^ (3 : ℕ) +
              4 * ((n : ℝ) + 4) *
                (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
                    ((n : ℝ) + 4) ^ (2 : ℕ) +
                  S.σ ^ (2 : ℕ)) * γ0 ≤
          (2 * Df S ^ (2 : ℕ) *
              (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) /
              (N : ℝ)) *
              (4 * S.L * ((n : ℝ) + 4) +
                S.σ * Real.sqrt ((n : ℝ) + 4) *
                  Real.sqrt (N : ℝ) / Dtilde) +
            S.L * Df S ^ (2 : ℕ) * ((n : ℝ) + 4) /
                (2 * (N : ℝ)) +
              S.L * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) +
                4 * S.σ * Real.sqrt ((n : ℝ) + 4) * Dtilde /
                  Real.sqrt (N : ℝ) := by
      rw [hthird_split]
      nlinarith [hfirst_bound, hmu_L3, hmu_gamma_smooth, hσ_branch]
    have hfinal_relax :
        (2 * Df S ^ (2 : ℕ) *
            (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) /
            (N : ℝ)) *
            (4 * S.L * ((n : ℝ) + 4) +
              S.σ * Real.sqrt ((n : ℝ) + 4) *
                Real.sqrt (N : ℝ) / Dtilde) +
          S.L * Df S ^ (2 : ℕ) * ((n : ℝ) + 4) /
              (2 * (N : ℝ)) +
            S.L * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) +
              4 * S.σ * Real.sqrt ((n : ℝ) + 4) * Dtilde /
                Real.sqrt (N : ℝ) ≤
          rsgfBbar S N Dtilde := by
      -- Remaining source step 6-7 scalar relaxation: collect the
      -- `L * Df^2 / N` terms and use `1 + 1/(aN) ≤ 2` for the sigma branch.
      have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hN
      have ha_ge_four : (4 : ℝ) ≤ (n : ℝ) + 4 := by
        have hn_nonneg : 0 ≤ (n : ℝ) := by
          exact_mod_cast Nat.zero_le n
        linarith
      have ha_ge_one : (1 : ℝ) ≤ (n : ℝ) + 4 := by linarith
      have hF_nonneg : 0 ≤ Df S ^ (2 : ℕ) := sq_nonneg (Df S)
      have hsqrt_a_nonneg : 0 ≤ Real.sqrt ((n : ℝ) + 4) :=
        Real.sqrt_nonneg _
      have hsqrt_N_pos : 0 < Real.sqrt (N : ℝ) :=
        Real.sqrt_pos.mpr hN_pos
      have hsqrt_N_sq :
          Real.sqrt (N : ℝ) ^ (2 : ℕ) = (N : ℝ) :=
        Real.sq_sqrt hN_pos.le
      have hL_terms :
          2 * Df S ^ (2 : ℕ) *
              (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) /
              (N : ℝ) * (4 * S.L * ((n : ℝ) + 4)) +
              S.L * Df S ^ (2 : ℕ) * ((n : ℝ) + 4) /
                (2 * (N : ℝ)) +
            S.L * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) ≤
          12 * ((n : ℝ) + 4) * S.L * Df S ^ (2 : ℕ) /
            (N : ℝ) :=
        rsgf_corollary_63_final_L_terms
          (a := (n : ℝ) + 4) (N := (N : ℝ)) (L := S.L)
          (F := Df S ^ (2 : ℕ)) ha_ge_four hN_ge_one
          S.L_pos.le hF_nonneg
      have hSigma_terms :
          2 * Df S ^ (2 : ℕ) *
              (1 + 1 / (((n : ℝ) + 4) * (N : ℝ))) /
              (N : ℝ) *
              (S.σ * Real.sqrt ((n : ℝ) + 4) *
                Real.sqrt (N : ℝ) / Dtilde) +
            4 * S.σ * Real.sqrt ((n : ℝ) + 4) * Dtilde /
              Real.sqrt (N : ℝ) ≤
          (4 * S.σ * Real.sqrt ((n : ℝ) + 4) /
              Real.sqrt (N : ℝ)) *
            (Dtilde + Df S ^ (2 : ℕ) / Dtilde) :=
        rsgf_corollary_63_final_sigma_terms
          (a := (n : ℝ) + 4) (N := (N : ℝ)) (σ := S.σ)
          (F := Df S ^ (2 : ℕ)) (D := Dtilde)
          (sqrtA := Real.sqrt ((n : ℝ) + 4))
          (sqrtN := Real.sqrt (N : ℝ)) ha_ge_one hN_ge_one
          S.σ_nonneg hF_nonneg hsqrt_a_nonneg hDtilde hsqrt_N_pos
          hsqrt_N_sq
      change _ ≤
        12 * ((n : ℝ) + 4) * S.L * Df S ^ (2 : ℕ) / (N : ℝ) +
          (4 * S.σ * Real.sqrt ((n : ℝ) + 4) /
              Real.sqrt (N : ℝ)) *
            (Dtilde + Df S ^ (2 : ℕ) / Dtilde)
      exact
        rsgf_corollary_63_final_terms_of_branches
          (a := (n : ℝ) + 4) (N := (N : ℝ)) (L := S.L)
          (σ := S.σ) (F := Df S ^ (2 : ℕ)) (D := Dtilde)
          (sqrtA := Real.sqrt ((n : ℝ) + 4))
          (sqrtN := Real.sqrt (N : ℝ)) hL_terms hSigma_terms
    exact le_trans hsource_step5 hfinal_relax
  exact le_trans hprebound hscalar

/-- Source-level Corollary 6.3(a) specialized to the admissible PMF realization
used by the helper-level 2-RSGF product law.  This is the expectation input to
the Markov tail (6.1.78). -/
private theorem rsgf_constant_stepsize_corollary_6_3a_of_admissible
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    (1 / S.L) *
        rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) ≤
      rsgfBbar S N Dtilde := by
  classical
  have hγ_upper :
      ∀ k ∈ Icc 1 N, S.γ k < (2 * ((n : ℝ) + 4) * S.L)⁻¹ :=
    rsgfConstantStepsizePolicy_upper_bound S Dtilde hN hDtilde hsteps
  have h63 :
      (1 / S.L) *
          rsgfSelectedJointExpectation S N hPR
            (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) ≤
        nonconvexRsgfBoundNumerator S N /
          rsgfWeightDenominator S N :=
    theorem_6_3a_nonconvex_of_admissible S N hN hγ_upper hPR
  have hscalar :
      nonconvexRsgfBoundNumerator S N /
          rsgfWeightDenominator S N ≤
        rsgfBbar S N Dtilde := by
    exact
      rsgf_constant_stepsize_corollary_6_3_scalar_bound
        S hN hDtilde hsteps hPR hsmooth
  exact le_trans h63 hscalar

/-- The one-run non-strict Markov tail (6.1.78) at `lambda = 2`, under the
admissible selected-run law used by the independent-product 2-RSGF helper. -/
private theorem rsgf_single_run_markov_tail_6_1_78_lambda_two
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    (rsgfSelectedRunLaw S N hPR)
        {q : RsgfRunOutcome n Sample N |
          ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ) ≥
            2 * S.L * rsgfBbar S N Dtilde} ≤
      ENNReal.ofReal ((1 / 2 : ℝ)) := by
  classical
  have hcorr :=
    rsgf_constant_stepsize_corollary_6_3a_of_admissible
      S hN hDtilde hsteps hPR hsmooth
  have hInt :
      Integrable
        (fun q : RsgfRunOutcome n Sample N =>
          ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ))
        (rsgfSelectedRunLaw S N hPR) :=
    rsgf_selected_gradient_norm_sq_integrable_of_admissible S hN hPR
  have hBbar_nonneg : 0 ≤ rsgfBbar S N Dtilde :=
    rsgfBbar_nonneg S hN hDtilde
  have hBbar_pos : 0 < rsgfBbar S N Dtilde :=
    rsgfBbar_pos_of_smoothing S hN hDtilde hsmooth
  have hLBbar_pos : 0 < S.L * rsgfBbar S N Dtilde :=
    mul_pos S.L_pos hBbar_pos
  have hthreshold_pos :
      0 < 2 * S.L * rsgfBbar S N Dtilde := by
    nlinarith [hLBbar_pos]
  have hE_le :
      rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ)) ≤
        S.L * rsgfBbar S N Dtilde := by
    have hmul := mul_le_mul_of_nonneg_left hcorr S.L_pos.le
    calc
      rsgfSelectedJointExpectation S N hPR
          (fun R ζ => ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))
          =
        S.L *
          ((1 / S.L) *
            rsgfSelectedJointExpectation S N hPR
              (fun R ζ =>
                ‖∇ (objective S) (rsgfPrefixIterate S ζ R)‖ ^ (2 : ℕ))) := by
          field_simp [ne_of_gt S.L_pos]
      _ ≤ S.L * rsgfBbar S N Dtilde := hmul
  have hInt_le :
      (∫ q : RsgfRunOutcome n Sample N,
        ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ)
        ∂(rsgfSelectedRunLaw S N hPR)) ≤
        S.L * rsgfBbar S N Dtilde := by
    simpa [rsgfSelectedJointExpectation, rsgfRunCandidate] using hE_le
  refine
    measure_ge_le_of_integral_le_of_nonneg
      (μ := rsgfSelectedRunLaw S N hPR)
      (f := fun q : RsgfRunOutcome n Sample N =>
        ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ))
      (t := 2 * S.L * rsgfBbar S N Dtilde)
      (C := S.L * rsgfBbar S N Dtilde)
      (b := (1 / 2 : ℝ))
      hInt
      (fun q => sq_nonneg ‖∇ (objective S) (rsgfRunCandidate S q)‖)
      hInt_le hthreshold_pos ?_
  have hratio :
      (S.L * rsgfBbar S N Dtilde) /
          (2 * S.L * rsgfBbar S N Dtilde) =
        (1 / 2 : ℝ) := by
    field_simp [ne_of_gt S.L_pos, ne_of_gt hBbar_pos]
  exact le_of_eq hratio

/-- Finite iid product tail bound for the all-coordinate event.  This is the
measure-theoretic product step used in (6.1.87). -/
private theorem iid_product_all_coordinates_event_real_le_pow
    {ι A : Type*} [Fintype ι] [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (E : Set A) {c : ℝ}
    (hc : 0 ≤ c) (hE : ν E ≤ ENNReal.ofReal c) :
    (Measure.pi (fun _ : ι => ν)).real
        (Set.pi Set.univ (fun _ : ι => E)) ≤
      c ^ Fintype.card ι := by
  classical
  rw [Measure.real_def]
  have hmass :
      Measure.pi (fun _ : ι => ν) (Set.pi Set.univ (fun _ : ι => E)) ≤
        ENNReal.ofReal (c ^ Fintype.card ι) := by
    calc
      Measure.pi (fun _ : ι => ν) (Set.pi Set.univ (fun _ : ι => E))
          = ∏ _ : ι, ν E := by
            simpa using
              (Measure.pi_pi (μ := fun _ : ι => ν) (fun _ : ι => E))
      _ ≤ ∏ _ : ι, ENNReal.ofReal c := by
            exact Finset.prod_le_prod
              (fun _ _ => (bot_le : (0 : ENNReal) ≤ ν E))
              (fun _ _ => hE)
      _ = (ENNReal.ofReal c) ^ Fintype.card ι := by
            simp
      _ = ENNReal.ofReal (c ^ Fintype.card ι) := by
            rw [ENNReal.ofReal_pow hc]
  have hreal :=
    ENNReal.toReal_mono
      (ENNReal.ofReal_ne_top :
        ENNReal.ofReal (c ^ Fintype.card ι) ≠ ⊤)
      hmass
  simpa [ENNReal.toReal_ofReal (pow_nonneg hc _)] using hreal

/-- Optimization-phase product tail in the proof of Theorem 6.4(a), equation
(6.1.87): all independent RSGF runs fail the `2 L Bbar` true-gradient test with
probability at most `2^{-S}`. -/
private theorem rsgf_two_phase_optimization_min_tail_6_1_87
    (S : Setup n Sample) {S_count N : ℕ} {Dtilde : ℝ}
    (hS : 0 < S_count) (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    (rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR).real
        {runs : RsgfOptimizationRuns n Sample S_count N |
          ∀ s : Fin S_count,
            ‖∇ (objective S) (rsgfRunCandidate S (runs s))‖ ^ (2 : ℕ) ≥
              2 * S.L * rsgfBbar S N Dtilde} ≤
      (1 / 2 : ℝ) ^ S_count := by
  classical
  have hsingle :=
    rsgf_single_run_markov_tail_6_1_78_lambda_two
      S hN hDtilde hsteps hPR hsmooth
  let ν : Measure (RsgfRunOutcome n Sample N) := rsgfSelectedRunLaw S N hPR
  let E : Set (RsgfRunOutcome n Sample N) :=
    {q |
      ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ) ≥
        2 * S.L * rsgfBbar S N Dtilde}
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
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, rsgfSelectedRunLaw]
    infer_instance
  have hE : ν E ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    simpa [ν, E] using hsingle
  have hset :
      {runs : RsgfOptimizationRuns n Sample S_count N |
          ∀ s : Fin S_count,
            ‖∇ (objective S) (rsgfRunCandidate S (runs s))‖ ^ (2 : ℕ) ≥
              2 * S.L * rsgfBbar S N Dtilde} =
        Set.pi Set.univ (fun _ : Fin S_count => E) := by
    ext runs
    simp [E, RsgfOptimizationRuns]
  have hbound :=
    iid_product_all_coordinates_event_real_le_pow
      (ι := Fin S_count) (A := RsgfRunOutcome n Sample N)
      (ν := ν) (E := E) (c := (1 / 2 : ℝ)) (by norm_num) hE
  simpa [rsgfOptimizationPhaseLaw_independentProduct, ν, hset, Fintype.card_fin]
    using hbound

/-- Corollary 6.3(a) as the selected-run law bound on the true-gradient
square, after multiplying by `S.L`.  This is the outer expectation contribution
to the diagonal residual budget in (6.1.88). -/
private theorem rsgf_selected_gradient_norm_sq_integral_le_L_Bbar
    (S : Setup n Sample) {N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    (∫ q : RsgfRunOutcome n Sample N,
        ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ)
        ∂(rsgfSelectedRunLaw S N hPR)) ≤
      S.L * rsgfBbar S N Dtilde := by
  classical
  let E : ℝ :=
    ∫ q : RsgfRunOutcome n Sample N,
      ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ)
      ∂(rsgfSelectedRunLaw S N hPR)
  have hcor :
      (1 / S.L) * E ≤ rsgfBbar S N Dtilde := by
    simpa [E, rsgfSelectedJointExpectation, rsgfRunCandidate] using
      rsgf_constant_stepsize_corollary_6_3a_of_admissible
        S hN hDtilde hsteps hPR hsmooth
  have hmul := mul_le_mul_of_nonneg_left hcor S.L_pos.le
  have hleft : S.L * ((1 / S.L) * E) = E := by
    field_simp [ne_of_gt S.L_pos]
  calc
    (∫ q : RsgfRunOutcome n Sample N,
        ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ)
        ∂(rsgfSelectedRunLaw S N hPR)) = E := rfl
    _ = S.L * ((1 / S.L) * E) := hleft.symm
    _ ≤ S.L * rsgfBbar S N Dtilde := hmul

/-- The smoothing-dependent bias term in the RSGF oracle second-moment bound is
absorbed by the `L^2 D_f^2 /(2N)` part of the two-phase diagonal budget. -/
private theorem rsgf_smoothing_oracle_bias_second_moment_le_budget
    (S : Setup n Sample) {N : ℕ}
    (hN : 1 ≤ N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) ≤
      2 * ((n : ℝ) + 4) *
        (S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) := by
  classical
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    nlinarith
  have hn4_nonneg : 0 ≤ (n : ℝ) + 4 := hn4_pos.le
  have hn_sq_nonneg : 0 ≤ (n : ℝ) ^ (2 : ℕ) := sq_nonneg _
  have hn_cube_nonneg : 0 ≤ (n : ℝ) ^ (3 : ℕ) :=
    pow_nonneg hn_nonneg 3
  have hcube6 :
      ((n : ℝ) + 6) ^ (3 : ℕ) ≤
        4 * ((n : ℝ) + 4) ^ (3 : ℕ) := by
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
  have hμsq :
      S.μ ^ (2 : ℕ) ≤
        Df S ^ (2 : ℕ) /
          (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ))) :=
    rsgf_smoothing_parameter_sq_bound S hN hsmooth
  have hcoef_nonneg :
      0 ≤ S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 := by
    positivity
  have hcube_scaled :
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) ≤
        2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) * ((n : ℝ) + 4) ^ (3 : ℕ) := by
    calc
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ) ≤
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 *
            (4 * ((n : ℝ) + 4) ^ (3 : ℕ)) :=
            mul_le_mul_of_nonneg_left hcube6 hcoef_nonneg
      _ = 2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) *
            ((n : ℝ) + 4) ^ (3 : ℕ) := by ring
  have hcoef2_nonneg :
      0 ≤ 2 * S.L ^ (2 : ℕ) * ((n : ℝ) + 4) ^ (3 : ℕ) := by
    positivity
  have hμ_scaled :
      2 * S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) * ((n : ℝ) + 4) ^ (3 : ℕ) ≤
        2 *
          (Df S ^ (2 : ℕ) /
            (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) *
          S.L ^ (2 : ℕ) * ((n : ℝ) + 4) ^ (3 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_left hμsq hcoef2_nonneg
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hbudget_eval :
      2 *
          (Df S ^ (2 : ℕ) /
            (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) *
          S.L ^ (2 : ℕ) * ((n : ℝ) + 4) ^ (3 : ℕ) =
        2 * ((n : ℝ) + 4) *
          (S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) := by
    field_simp [ne_of_gt hn4_pos, ne_of_gt hN_pos]
  exact hcube_scaled.trans (hμ_scaled.trans (le_of_eq hbudget_eval))

/-- Finite-selector product measurability: if each fiber over the sample
coordinate is a.e.-strongly measurable, then selecting the fiber by the finite
first coordinate is a.e.-strongly measurable under the product law. -/
private theorem aestronglyMeasurable_finite_index_first_prod_of_fibers
    {ι Ω E : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    [TopologicalSpace E] [ContinuousAdd E]
    (ν : Measure ι) [SFinite ν] (μ : Measure Ω)
    (F : ι → Ω → E)
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) :
    AEStronglyMeasurable (fun q : ι × Ω => F q.1 q.2) (ν.prod μ) := by
  classical
  let G : ι × Ω → E :=
    Finset.univ.sum (fun i : ι =>
      Set.indicator {q : ι × Ω | q.1 = i} (fun q => F i q.2))
  have hG :
      AEStronglyMeasurable G (ν.prod μ) := by
    dsimp [G]
    exact
      Finset.aestronglyMeasurable_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i : ι =>
          Set.indicator {q : ι × Ω | q.1 = i} (fun q => F i q.2))
        (by
          intro i hi
          have hbase :
              AEStronglyMeasurable (fun q : ι × Ω => F i q.2) (ν.prod μ) :=
            (hF i).comp_snd
          exact hbase.indicator (measurableSet_singleton i |>.preimage measurable_fst))
  refine hG.congr (Filter.Eventually.of_forall ?_)
  intro q
  dsimp [G]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single q.1]
  · simp
  · intro b _ hb
    simp [Set.indicator_of_notMem, hb.symm]
  · intro hnot
    exact (hnot (Finset.mem_univ q.1)).elim

/-- The selected candidate of one RSGF run is a.e.-strongly measurable under
the internal selected-run law. -/
private theorem rsgfRunCandidate_aestronglyMeasurable_selectedRunLaw
    (S : Setup n Sample) {N : ℕ}
    (hPR : RsgfOutputWeightsAdmissible S N) :
    AEStronglyMeasurable
      (fun q : RsgfRunOutcome n Sample N => rsgfRunCandidate S q)
      (rsgfSelectedRunLaw S N hPR) := by
  classical
  have hfib :
      ∀ R : RsgfOutputIndex N,
        AEStronglyMeasurable
          (fun ζ : RsgfSamplePrefix n Sample N => rsgfPrefixIterate S ζ R)
          (rsgfPrefixLaw S N) := fun R =>
    (rsgfPrefixIterate_and_oracle_aestronglyMeasurable S R).1
  simpa [rsgfSelectedRunLaw, rsgfRunCandidate] using
    (aestronglyMeasurable_finite_index_first_prod_of_fibers
      ((rsgfOutputPMF_of_admissible S N hPR).toMeasure)
      (rsgfPrefixLaw S N)
      (fun R ζ => rsgfPrefixIterate S ζ R)
      hfib)

/-- A fixed optimization-run coordinate candidate is a.e.-strongly measurable
under the optimization-phase product law. -/
private theorem rsgfOptimizationRunCandidate_aestronglyMeasurable
    (S : Setup n Sample) {S_count N : ℕ}
    (hN : 1 ≤ N) (hPR : RsgfOutputWeightsAdmissible S N)
    (s : Fin S_count) :
    AEStronglyMeasurable
      (fun runs : RsgfOptimizationRuns n Sample S_count N =>
        rsgfRunCandidate S (runs s))
      (rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR) := by
  classical
  let ν : Measure (RsgfRunOutcome n Sample N) := rsgfSelectedRunLaw S N hPR
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
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, rsgfSelectedRunLaw]
    infer_instance
  haveI : SigmaFinite ν := inferInstance
  have hsel :
      AEStronglyMeasurable
        (fun q : RsgfRunOutcome n Sample N => rsgfRunCandidate S q) ν := by
    simpa [ν] using rsgfRunCandidate_aestronglyMeasurable_selectedRunLaw S hPR
  have hqmp :
      Measure.QuasiMeasurePreserving
        (Function.eval s)
        (Measure.pi (fun _ : Fin S_count => ν))
        ν := by
    simpa [ν] using
      (Measure.quasiMeasurePreserving_eval
        (μ := fun _ : Fin S_count => ν) s)
  simpa [rsgfOptimizationPhaseLaw_independentProduct, ν] using
    hsel.comp_quasiMeasurePreserving hqmp

/-- A coordinate projection from the optimization-run product law has the
selected-run law. -/
private theorem rsgfOptimizationPhaseLaw_eval_measurePreserving
    (S : Setup n Sample) {S_count N : ℕ}
    (hN : 1 ≤ N) (hPR : RsgfOutputWeightsAdmissible S N)
    (s : Fin S_count) :
    MeasurePreserving
      (fun runs : RsgfOptimizationRuns n Sample S_count N => runs s)
      (rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR)
      (rsgfSelectedRunLaw S N hPR) := by
  classical
  let ν : Measure (RsgfRunOutcome n Sample N) := rsgfSelectedRunLaw S N hPR
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
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, rsgfSelectedRunLaw]
    infer_instance
  refine ⟨measurable_pi_apply s, ?_⟩
  simpa [rsgfOptimizationPhaseLaw_independentProduct, ν, Measure.pi_map_eval]

/-- The selected-run gradient-square expectation bound transported to any fixed
coordinate of the optimization-run product law. -/
private theorem rsgf_optimization_run_coordinate_gradient_sq_integral_le
    (S : Setup n Sample) {S_count N : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) (s : Fin S_count) :
    (∫ runs : RsgfOptimizationRuns n Sample S_count N,
        ‖∇ (objective S) (rsgfRunCandidate S (runs s))‖ ^ (2 : ℕ)
        ∂(rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR)) ≤
      S.L * rsgfBbar S N Dtilde := by
  classical
  let φ : RsgfRunOutcome n Sample N → ℝ := fun q =>
    ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ)
  have hφ_int : Integrable φ (rsgfSelectedRunLaw S N hPR) :=
    rsgf_selected_gradient_norm_sq_integrable_of_admissible S hN hPR
  have hmp :=
    rsgfOptimizationPhaseLaw_eval_measurePreserving
      S hN hPR s
  have hφ_aesm : AEStronglyMeasurable φ (rsgfSelectedRunLaw S N hPR) :=
    hφ_int.aestronglyMeasurable
  have hφ_aesm_map :
      AEStronglyMeasurable φ
        (Measure.map
          (fun runs : RsgfOptimizationRuns n Sample S_count N => runs s)
          (rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR)) := by
    rw [hmp.map_eq]
    exact hφ_aesm
  calc
    (∫ runs : RsgfOptimizationRuns n Sample S_count N,
        ‖∇ (objective S) (rsgfRunCandidate S (runs s))‖ ^ (2 : ℕ)
        ∂(rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR))
        = ∫ runs : RsgfOptimizationRuns n Sample S_count N, φ (runs s)
            ∂(rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR) := by
          rfl
    _ = ∫ q : RsgfRunOutcome n Sample N, φ q
          ∂Measure.map
            (fun runs : RsgfOptimizationRuns n Sample S_count N => runs s)
            (rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR) := by
          exact (integral_map hmp.aemeasurable hφ_aesm_map).symm
    _ = ∫ q : RsgfRunOutcome n Sample N, φ q
          ∂(rsgfSelectedRunLaw S N hPR) := by
          rw [hmp.map_eq]
    _ ≤ S.L * rsgfBbar S N Dtilde :=
      rsgf_selected_gradient_norm_sq_integral_le_L_Bbar
        S hN hDtilde hsteps hPR hsmooth

/-- A coordinate projection from the post-optimization evaluation prefix has
law `rsgfZetaLaw S`. -/
private theorem rsgfEvaluationLaw_eval_measurePreserving
    (S : Setup n Sample) {T : ℕ} (k : RsgfOutputIndex T) :
    MeasurePreserving
      (fun η : RsgfEvaluationPrefix n Sample T => η k)
      (rsgfEvaluationLaw S T)
      (rsgfZetaLaw S) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  refine ⟨measurable_pi_apply k, ?_⟩
  simp [rsgfEvaluationLaw, Measure.pi_map_eval]

/-- Split the post-optimization evaluation product law at one output coordinate.
The selected coordinate is integrated as a fresh `rsgfZetaLaw` sample and the
remaining coordinates are integrated under their product law. -/
private theorem rsgfEvaluationLaw_coordinate_resampling_integral
    (S : Setup n Sample) {T : ℕ} (R : RsgfOutputIndex T)
    (Φ : RsgfEvaluationPrefix n Sample T → ℝ)
    (hΦ : Integrable Φ (rsgfEvaluationLaw S T)) :
    (∫ η : RsgfEvaluationPrefix n Sample T, Φ η ∂rsgfEvaluationLaw S T) =
      ∫ ηrest : ({Q : RsgfOutputIndex T // Q ≠ R} → RsgfZeta n Sample),
        ∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex T =>
            if h : Q = R then z else ηrest ⟨Q, h⟩)
          ∂rsgfZetaLaw S
        ∂(Measure.pi
            (fun _ : {Q : RsgfOutputIndex T // Q ≠ R} => rsgfZetaLaw S)) := by
  classical
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfZetaLaw S) := by
    dsimp [rsgfZetaLaw]
    infer_instance
  simpa [rsgfEvaluationLaw] using
    (integral_pi_eq_integral_subtype_compl_integral_coordinate
      (ν := rsgfZetaLaw S) R Φ hΦ)

/-- Fixed-query residual measurability under the one-sample RSGF law. -/
private theorem rsgfResidual_aestronglyMeasurable
    (S : Setup n Sample) (x : Space n) :
    AEStronglyMeasurable
      (fun z : RsgfZeta n Sample => rsgfResidual S x z.1 z.2)
      (rsgfZetaLaw S) := by
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  have horacle :
      AEStronglyMeasurable
        (fun z : Sample × Space n => rsgfOracle S x z.1 z.2)
        (S.P.prod (gaussianDirectionLaw n)) :=
    rsgfOracle_aestronglyMeasurable S x
  have hgrad :
      AEStronglyMeasurable
        (fun _z : Sample × Space n => ∇ (gaussianSmoothing S) x)
        (S.P.prod (gaussianDirectionLaw n)) :=
    aestronglyMeasurable_const
  simpa [SOptLib.oracleEstimatorError, rsgfZetaLaw] using horacle.sub hgrad

/-- Distinct post-optimization evaluation coordinates have zero fixed-candidate
residual cross integral under the independent evaluation-prefix product law. -/
private theorem rsgfEvaluationLaw_fixed_candidate_residual_cross_integral_eq_zero
    (S : Setup n Sample) {T : ℕ} (x : Space n)
    {i j : RsgfOutputIndex T} (hij : i ≠ j) :
    (∫ η : RsgfEvaluationPrefix n Sample T,
        ⟪rsgfResidual S x (η i).1 (η i).2,
          rsgfResidual S x (η j).1 (η j).2⟫_ℝ
        ∂rsgfEvaluationLaw S T) = 0 := by
  classical
  let νeval : Measure (RsgfEvaluationPrefix n Sample T) := rsgfEvaluationLaw S T
  let νz : Measure (RsgfZeta n Sample) := rsgfZetaLaw S
  let u : RsgfEvaluationPrefix n Sample T → Space n :=
    fun η => rsgfResidual S x (η i).1 (η i).2
  let v : RsgfEvaluationPrefix n Sample T → Space n :=
    fun η => rsgfResidual S x (η j).1 (η j).2
  let Φ : RsgfEvaluationPrefix n Sample T → ℝ := fun η => ⟪u η, v η⟫_ℝ
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure νz := by
    dsimp [νz, rsgfZetaLaw]
    infer_instance
  haveI : IsProbabilityMeasure νeval := by
    dsimp [νeval, rsgfEvaluationLaw]
    infer_instance
  have hmp_i :
      MeasurePreserving
        (fun η : RsgfEvaluationPrefix n Sample T => η i) νeval νz := by
    simpa [νeval, νz] using rsgfEvaluationLaw_eval_measurePreserving S i
  have hmp_j :
      MeasurePreserving
        (fun η : RsgfEvaluationPrefix n Sample T => η j) νeval νz := by
    simpa [νeval, νz] using rsgfEvaluationLaw_eval_measurePreserving S j
  have hres_aesm :
      AEStronglyMeasurable
        (fun z : RsgfZeta n Sample => rsgfResidual S x z.1 z.2) νz := by
    simpa [νz] using rsgfResidual_aestronglyMeasurable S x
  have hu_meas : AEStronglyMeasurable u νeval := by
    simpa [u] using hres_aesm.comp_measurePreserving hmp_i
  have hv_meas : AEStronglyMeasurable v νeval := by
    simpa [v] using hres_aesm.comp_measurePreserving hmp_j
  have hsq_z :
      Integrable
        (fun z : RsgfZeta n Sample =>
          ‖rsgfResidual S x z.1 z.2‖ ^ (2 : ℕ)) νz := by
    simpa [νz, rsgfZetaLaw] using rsgfResidual_norm_sq_integrable S x
  have hu_sq : Integrable (fun η : RsgfEvaluationPrefix n Sample T => ‖u η‖ ^ (2 : ℕ)) νeval := by
    let φ : RsgfZeta n Sample → ℝ :=
      fun z => ‖rsgfResidual S x z.1 z.2‖ ^ (2 : ℕ)
    have hφ_map : Integrable φ (Measure.map (fun η : RsgfEvaluationPrefix n Sample T => η i) νeval) := by
      rw [hmp_i.map_eq]
      simpa [φ, νz] using hsq_z
    have hcomp :
        Integrable
          (fun η : RsgfEvaluationPrefix n Sample T =>
            φ ((fun η : RsgfEvaluationPrefix n Sample T => η i) η)) νeval :=
      (integrable_map_measure hφ_map.aestronglyMeasurable hmp_i.aemeasurable).mp
        hφ_map
    simpa [φ, u] using hcomp
  have hv_sq : Integrable (fun η : RsgfEvaluationPrefix n Sample T => ‖v η‖ ^ (2 : ℕ)) νeval := by
    let φ : RsgfZeta n Sample → ℝ :=
      fun z => ‖rsgfResidual S x z.1 z.2‖ ^ (2 : ℕ)
    have hφ_map : Integrable φ (Measure.map (fun η : RsgfEvaluationPrefix n Sample T => η j) νeval) := by
      rw [hmp_j.map_eq]
      simpa [φ, νz] using hsq_z
    have hcomp :
        Integrable
          (fun η : RsgfEvaluationPrefix n Sample T =>
            φ ((fun η : RsgfEvaluationPrefix n Sample T => η j) η)) νeval :=
      (integrable_map_measure hφ_map.aestronglyMeasurable hmp_j.aemeasurable).mp
        hφ_map
    simpa [φ, v] using hcomp
  have hΦ_int : Integrable Φ νeval :=
    integrable_inner_of_integrable_sq_norm hu_meas hv_meas hu_sq hv_sq
  have hsplit :=
    rsgfEvaluationLaw_coordinate_resampling_integral S i Φ (by
      simpa [νeval] using hΦ_int)
  have hinner_zero :
      ∀ ηrest : ({Q : RsgfOutputIndex T // Q ≠ i} → RsgfZeta n Sample),
        (∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex T =>
            if h : Q = i then z else ηrest ⟨Q, h⟩) ∂νz) = 0 := by
    intro ηrest
    have hji : j ≠ i := Ne.symm hij
    let d : Space n :=
      rsgfResidual S x (ηrest ⟨j, hji⟩).1 (ηrest ⟨j, hji⟩).2
    calc
      (∫ z : RsgfZeta n Sample,
          Φ (fun Q : RsgfOutputIndex T =>
            if h : Q = i then z else ηrest ⟨Q, h⟩) ∂νz)
          =
        ∫ z : RsgfZeta n Sample,
          ⟪rsgfResidual S x z.1 z.2, d⟫_ℝ ∂νz := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun z => by
              simp [Φ, u, v, d, hji]
      _ = 0 := by
            simpa [νz, rsgfZetaLaw, d] using
              rsgfResidual_inner_integral_eq_zero S x d
  calc
    (∫ η : RsgfEvaluationPrefix n Sample T,
        ⟪rsgfResidual S x (η i).1 (η i).2,
          rsgfResidual S x (η j).1 (η j).2⟫_ℝ
        ∂rsgfEvaluationLaw S T)
        = ∫ η : RsgfEvaluationPrefix n Sample T, Φ η ∂rsgfEvaluationLaw S T := by
            simp [Φ, u, v]
    _ = ∫ ηrest : ({Q : RsgfOutputIndex T // Q ≠ i} → RsgfZeta n Sample),
          ∫ z : RsgfZeta n Sample,
            Φ (fun Q : RsgfOutputIndex T =>
              if h : Q = i then z else ηrest ⟨Q, h⟩)
            ∂rsgfZetaLaw S
          ∂(Measure.pi
              (fun _ : {Q : RsgfOutputIndex T // Q ≠ i} => rsgfZetaLaw S)) := hsplit
    _ = ∫ _ηrest : ({Q : RsgfOutputIndex T // Q ≠ i} → RsgfZeta n Sample),
          (0 : ℝ)
          ∂(Measure.pi
              (fun _ : {Q : RsgfOutputIndex T // Q ≠ i} => rsgfZetaLaw S)) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun ηrest => by
              simpa [νz] using hinner_zero ηrest
    _ = 0 := by simp

/-- One fixed post-optimization residual coordinate is a.e.-strongly measurable
under the full independent two-phase law. -/
private theorem rsgf_two_phase_fixed_candidate_residual_coordinate_aesm
    (S : Setup n Sample) {S_count N T : ℕ}
    (hN : 1 ≤ N) (hPR : RsgfOutputWeightsAdmissible S N)
    (s : Fin S_count) (k : RsgfOutputIndex T) :
    AEStronglyMeasurable
      (fun q : RsgfOptimizationRuns n Sample S_count N ×
          RsgfEvaluationPrefix n Sample T =>
        rsgfResidual S (rsgfRunCandidate S (q.1 s)) (q.2 k).1 (q.2 k).2)
      (rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR) := by
  classical
  let νruns : Measure (RsgfOptimizationRuns n Sample S_count N) :=
    rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR
  let νeval : Measure (RsgfEvaluationPrefix n Sample T) :=
    rsgfEvaluationLaw S T
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
  haveI : IsProbabilityMeasure (rsgfSelectedRunLaw S N hPR) := by
    dsimp [rsgfSelectedRunLaw]
    infer_instance
  haveI : IsProbabilityMeasure νruns := by
    dsimp [νruns, rsgfOptimizationPhaseLaw_independentProduct]
    infer_instance
  haveI : SFinite νruns := inferInstance
  haveI : IsProbabilityMeasure νeval := by
    dsimp [νeval, rsgfEvaluationLaw]
    infer_instance
  let X : RsgfOptimizationRuns n Sample S_count N → Space n :=
    fun runs => rsgfRunCandidate S (runs s)
  have hX : AEStronglyMeasurable X νruns := by
    simpa [X, νruns] using
      rsgfOptimizationRunCandidate_aestronglyMeasurable S hN hPR s
  have hres :
      AEStronglyMeasurable
        (fun p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample =>
          rsgfResidual S (X p.1) p.2.1 p.2.2)
        (νruns.prod (rsgfZetaLaw S)) :=
    rsgfResidual_random_query_aestronglyMeasurable_of_aesm S X hX
  have hmp_eval :
      MeasurePreserving
        (fun η : RsgfEvaluationPrefix n Sample T => η k)
        νeval
        (rsgfZetaLaw S) := by
    simpa [νeval] using rsgfEvaluationLaw_eval_measurePreserving S k
  have hmp :
      MeasurePreserving
        (fun q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T => (q.1, q.2 k))
        (νruns.prod νeval)
        (νruns.prod (rsgfZetaLaw S)) := by
    simpa [Function.comp_def] using
      (MeasurePreserving.id νruns).prod hmp_eval
  simpa [X, νruns, νeval, rsgfTwoPhaseJointLaw_independentProduct] using
    hres.comp_measurePreserving hmp

/-- A fixed post-optimization residual coordinate has the source residual
second-moment budget `𝒟_N` under the independent two-phase law. -/
private theorem rsgf_two_phase_fixed_candidate_residual_coordinate_l2_bound
    (S : Setup n Sample) {S_count N T : ℕ} {Dtilde : ℝ}
    (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N)
    (s : Fin S_count) (k : RsgfOutputIndex T) :
    let μ :=
      rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
    let D_N : ℝ :=
      2 * ((n : ℝ) + 4) *
        (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
          S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ)))
    Integrable
        (fun q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T =>
          ‖rsgfResidual S (rsgfRunCandidate S (q.1 s)) (q.2 k).1 (q.2 k).2‖ ^
            (2 : ℕ))
        μ ∧
      (∫ q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T,
          ‖rsgfResidual S (rsgfRunCandidate S (q.1 s)) (q.2 k).1 (q.2 k).2‖ ^
            (2 : ℕ) ∂μ) ≤ D_N := by
  classical
  let μfull : Measure (RsgfOptimizationRuns n Sample S_count N ×
      RsgfEvaluationPrefix n Sample T) :=
    rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
  let νruns : Measure (RsgfOptimizationRuns n Sample S_count N) :=
    rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR
  let νeval : Measure (RsgfEvaluationPrefix n Sample T) :=
    rsgfEvaluationLaw S T
  let νz : Measure (RsgfZeta n Sample) := rsgfZetaLaw S
  let X : RsgfOptimizationRuns n Sample S_count N → Space n :=
    fun runs => rsgfRunCandidate S (runs s)
  let φ : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample → ℝ :=
    fun p => ‖rsgfResidual S (X p.1) p.2.1 p.2.2‖ ^ (2 : ℕ)
  let C : ℝ :=
    S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 2 * ((n : ℝ) + 6) ^ (3 : ℕ)
  let c : ℝ := 2 * ((n : ℝ) + 4)
  let B : RsgfOptimizationRuns n Sample S_count N → ℝ := fun runs =>
    c * (‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ)) + C
  let D_N : ℝ :=
    2 * ((n : ℝ) + 4) *
      (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
        S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ)))
  letI : IsProbabilityMeasure S.P := S.P_isProbability
  haveI : IsProbabilityMeasure (gaussianDirectionLaw n) := by
    rw [gaussianDirectionLaw_def]
    infer_instance
  haveI : IsProbabilityMeasure νz := by
    dsimp [νz, rsgfZetaLaw]
    infer_instance
  haveI : SFinite νz := inferInstance
  haveI : IsProbabilityMeasure (rsgfPrefixLaw S N) := by
    unfold rsgfPrefixLaw
    infer_instance
  haveI : IsProbabilityMeasure (rsgfSelectedRunLaw S N hPR) := by
    dsimp [rsgfSelectedRunLaw]
    infer_instance
  haveI : IsProbabilityMeasure νruns := by
    dsimp [νruns, rsgfOptimizationPhaseLaw_independentProduct]
    infer_instance
  haveI : IsProbabilityMeasure νeval := by
    dsimp [νeval, rsgfEvaluationLaw]
    infer_instance
  have hX_aesm : AEStronglyMeasurable X νruns := by
    simpa [X, νruns] using
      rsgfOptimizationRunCandidate_aestronglyMeasurable S hN hPR s
  have hres_prod :
      AEStronglyMeasurable
        (fun p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample =>
          rsgfResidual S (X p.1) p.2.1 p.2.2)
        (νruns.prod νz) := by
    simpa [νz] using
      rsgfResidual_random_query_aestronglyMeasurable_of_aesm S X hX_aesm
  have hφ_prod :
      AEStronglyMeasurable φ (νruns.prod νz) := by
    simpa [φ] using
      ((hres_prod.norm.aemeasurable.pow_const 2).aestronglyMeasurable)
  have hgrad_int :
      Integrable
        (fun runs : RsgfOptimizationRuns n Sample S_count N =>
          ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ)) νruns := by
    let gradφ : RsgfRunOutcome n Sample N → ℝ := fun q =>
      ‖∇ (objective S) (rsgfRunCandidate S q)‖ ^ (2 : ℕ)
    let evalRun : RsgfOptimizationRuns n Sample S_count N → RsgfRunOutcome n Sample N :=
      fun runs => runs s
    have hmp :=
      rsgfOptimizationPhaseLaw_eval_measurePreserving S hN hPR s
    have hsel_int : Integrable gradφ (rsgfSelectedRunLaw S N hPR) := by
      simpa [gradφ] using
        rsgf_selected_gradient_norm_sq_integrable_of_admissible S hN hPR
    have hmap_int : Integrable gradφ (Measure.map evalRun νruns) := by
      rw [show Measure.map evalRun νruns = rsgfSelectedRunLaw S N hPR by
        simpa [evalRun, νruns] using hmp.map_eq]
      exact hsel_int
    have hcomp :
        Integrable (fun runs : RsgfOptimizationRuns n Sample S_count N =>
          gradφ (evalRun runs)) νruns :=
      (integrable_map_measure hmap_int.aestronglyMeasurable
        (by simpa [evalRun, νruns] using hmp.aemeasurable)).mp hmap_int
    simpa [gradφ, evalRun, X] using hcomp
  have hB_int : Integrable B νruns := by
    have hgrad_sigma :
        Integrable
          (fun runs : RsgfOptimizationRuns n Sample S_count N =>
            ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ)) νruns :=
      hgrad_int.add (integrable_const _)
    exact (hgrad_sigma.const_mul c).add (integrable_const C)
  have hfixed_int :
      ∀ runs : RsgfOptimizationRuns n Sample S_count N,
        Integrable (fun z : RsgfZeta n Sample => φ (runs, z)) νz := by
    intro runs
    simpa [φ, X, νz, rsgfZetaLaw] using
      rsgfResidual_norm_sq_integrable S (X runs)
  have hfixed_bound :
      ∀ runs : RsgfOptimizationRuns n Sample S_count N,
        (∫ z : RsgfZeta n Sample, φ (runs, z) ∂νz) ≤ B runs := by
    intro runs
    simpa [φ, B, C, c, X, νz, rsgfZetaLaw, add_assoc] using
      rsgfResidual_secondMoment_le_gradient_sigma S (X runs)
  have hprod_int :
      Integrable φ (νruns.prod νz) := by
    exact
      integrable_prod_of_nonneg_fiber_integral_le_integrable_bound
        (μ := νruns) (ν := νz) (φ := fun runs z => φ (runs, z)) (B := B)
        (by simpa [Function.uncurry, Prod.mk.eta] using hφ_prod)
        (fun runs z => sq_nonneg ‖rsgfResidual S (X runs) z.1 z.2‖)
        hfixed_int hB_int hfixed_bound
  have hprod_bound :
      (∫ p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample,
          φ p ∂(νruns.prod νz)) ≤ D_N := by
    have hprod :
        (∫ p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample,
            φ p ∂(νruns.prod νz)) =
          ∫ runs : RsgfOptimizationRuns n Sample S_count N,
            ∫ z : RsgfZeta n Sample, φ (runs, z) ∂νz ∂νruns := by
      exact MeasureTheory.integral_prod φ hprod_int
    have hinner_int :
        Integrable
          (fun runs : RsgfOptimizationRuns n Sample S_count N =>
            ∫ z : RsgfZeta n Sample, φ (runs, z) ∂νz) νruns :=
      hprod_int.integral_prod_left
    have hinner_le :
        (∫ runs : RsgfOptimizationRuns n Sample S_count N,
            ∫ z : RsgfZeta n Sample, φ (runs, z) ∂νz ∂νruns) ≤
          ∫ runs : RsgfOptimizationRuns n Sample S_count N, B runs ∂νruns := by
      exact integral_mono hinner_int hB_int hfixed_bound
    have hB_eval :
        (∫ runs : RsgfOptimizationRuns n Sample S_count N, B runs ∂νruns) =
          c *
              ((∫ runs : RsgfOptimizationRuns n Sample S_count N,
                ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) +
                S.σ ^ (2 : ℕ)) + C := by
      have hconst_sigma :
          Integrable
            (fun _runs : RsgfOptimizationRuns n Sample S_count N => S.σ ^ (2 : ℕ))
            νruns := integrable_const _
      have hsum :
          (∫ runs : RsgfOptimizationRuns n Sample S_count N,
            ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ) ∂νruns) =
            (∫ runs : RsgfOptimizationRuns n Sample S_count N,
              ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) +
              S.σ ^ (2 : ℕ) := by
        rw [integral_add hgrad_int hconst_sigma]
        simp
      have hgrad_sigma :
          Integrable
            (fun runs : RsgfOptimizationRuns n Sample S_count N =>
              ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ)) νruns :=
        hgrad_int.add hconst_sigma
      have hscaled :
          Integrable
            (fun runs : RsgfOptimizationRuns n Sample S_count N =>
              c * (‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ))) νruns :=
        hgrad_sigma.const_mul c
      have hconst_C :
          Integrable (fun _runs : RsgfOptimizationRuns n Sample S_count N => C) νruns :=
        integrable_const _
      calc
        (∫ runs : RsgfOptimizationRuns n Sample S_count N, B runs ∂νruns)
            =
          ∫ runs : RsgfOptimizationRuns n Sample S_count N,
            c * (‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ)) + C
            ∂νruns := by
              simp [B]
        _ =
          (∫ runs : RsgfOptimizationRuns n Sample S_count N,
            c * (‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ)) ∂νruns) +
            ∫ _runs : RsgfOptimizationRuns n Sample S_count N, C ∂νruns := by
              exact integral_add hscaled hconst_C
        _ =
          c *
              (∫ runs : RsgfOptimizationRuns n Sample S_count N,
                ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) + S.σ ^ (2 : ℕ) ∂νruns) + C := by
              simp [integral_const_mul]
        _ =
          c *
              ((∫ runs : RsgfOptimizationRuns n Sample S_count N,
                ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) +
                S.σ ^ (2 : ℕ)) + C := by
              rw [hsum]
    have hgrad_bound :
        (∫ runs : RsgfOptimizationRuns n Sample S_count N,
            ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) ≤
          S.L * rsgfBbar S N Dtilde := by
      simpa [X, νruns] using
        rsgf_optimization_run_coordinate_gradient_sq_integral_le
          S hN hDtilde hsteps hPR hsmooth s
    have hsmoothing_bias :
        C ≤ c * (S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) := by
      simpa [C, c] using
        rsgf_smoothing_oracle_bias_second_moment_le_budget S hN hsmooth
    have hc_nonneg : 0 ≤ c := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      dsimp [c]
      nlinarith
    have hbudget :
        c *
              ((∫ runs : RsgfOptimizationRuns n Sample S_count N,
                ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) +
                S.σ ^ (2 : ℕ)) + C ≤
          D_N := by
      have hmul :
          c *
              ((∫ runs : RsgfOptimizationRuns n Sample S_count N,
                ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) +
                S.σ ^ (2 : ℕ)) ≤
            c * (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ)) := by
        have hadd :
            (∫ runs : RsgfOptimizationRuns n Sample S_count N,
              ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) +
                S.σ ^ (2 : ℕ) ≤
              S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) := by
          nlinarith [hgrad_bound]
        exact mul_le_mul_of_nonneg_left hadd hc_nonneg
      dsimp [D_N, c] at *
      nlinarith [hmul, hsmoothing_bias]
    calc
      (∫ p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample,
          φ p ∂(νruns.prod νz))
          =
        ∫ runs : RsgfOptimizationRuns n Sample S_count N,
          ∫ z : RsgfZeta n Sample, φ (runs, z) ∂νz ∂νruns := hprod
      _ ≤ ∫ runs : RsgfOptimizationRuns n Sample S_count N, B runs ∂νruns := hinner_le
      _ = c *
            ((∫ runs : RsgfOptimizationRuns n Sample S_count N,
              ‖∇ (objective S) (X runs)‖ ^ (2 : ℕ) ∂νruns) +
              S.σ ^ (2 : ℕ)) + C := hB_eval
      _ ≤ D_N := hbudget
  have hmp_eval :
      MeasurePreserving
        (fun η : RsgfEvaluationPrefix n Sample T => η k)
        νeval νz := by
    simpa [νeval, νz] using rsgfEvaluationLaw_eval_measurePreserving S k
  let coord :
      RsgfOptimizationRuns n Sample S_count N × RsgfEvaluationPrefix n Sample T →
        RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample :=
    fun q => (q.1, q.2 k)
  have hmp_coord :
      MeasurePreserving coord (νruns.prod νeval) (νruns.prod νz) := by
    simpa [coord, Function.comp_def] using
      (MeasurePreserving.id νruns).prod hmp_eval
  have hφ_map_int :
      Integrable φ (Measure.map coord (νruns.prod νeval)) := by
    rw [hmp_coord.map_eq]
    exact hprod_int
  have hcoord_int :
      Integrable (fun q : RsgfOptimizationRuns n Sample S_count N ×
          RsgfEvaluationPrefix n Sample T => φ (coord q)) (νruns.prod νeval) :=
    (integrable_map_measure hφ_map_int.aestronglyMeasurable hmp_coord.aemeasurable).mp
      hφ_map_int
  have hcoord_integral :
      (∫ q : RsgfOptimizationRuns n Sample S_count N × RsgfEvaluationPrefix n Sample T,
          φ (coord q) ∂(νruns.prod νeval)) =
        ∫ p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample,
          φ p ∂(νruns.prod νz) := by
    calc
      (∫ q : RsgfOptimizationRuns n Sample S_count N × RsgfEvaluationPrefix n Sample T,
          φ (coord q) ∂(νruns.prod νeval))
          =
        ∫ p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample,
          φ p ∂Measure.map coord (νruns.prod νeval) := by
            exact (integral_map hmp_coord.aemeasurable hφ_map_int.aestronglyMeasurable).symm
      _ =
        ∫ p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample,
          φ p ∂(νruns.prod νz) := by
            rw [hmp_coord.map_eq]
  refine ⟨?_, ?_⟩
  · simpa [μfull, νruns, νeval, φ, coord, X,
      rsgfTwoPhaseJointLaw_independentProduct] using hcoord_int
  · calc
      (∫ q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T,
          ‖rsgfResidual S (rsgfRunCandidate S (q.1 s)) (q.2 k).1 (q.2 k).2‖ ^
            (2 : ℕ) ∂μfull)
          =
        ∫ q : RsgfOptimizationRuns n Sample S_count N × RsgfEvaluationPrefix n Sample T,
          φ (coord q) ∂(νruns.prod νeval) := by
            simp [μfull, νruns, νeval, φ, coord, X,
              rsgfTwoPhaseJointLaw_independentProduct]
      _ =
        ∫ p : RsgfOptimizationRuns n Sample S_count N × RsgfZeta n Sample,
          φ p ∂(νruns.prod νz) := hcoord_integral
      _ ≤ D_N := hprod_bound

/-- The post-optimization empirical-gradient error is the average of the
fresh centered RSGF residuals at the fixed candidate. -/
private theorem rsgf_two_phase_empirical_error_eq_residual_average
    (S : Setup n Sample) {S_count N T : ℕ} (hT : 1 ≤ T)
    (runs : RsgfOptimizationRuns n Sample S_count N)
    (η : RsgfEvaluationPrefix n Sample T) (s : Fin S_count) :
    rsgfTwoPhaseEmpiricalGradient S runs η s -
        ∇ (gaussianSmoothing S) (rsgfRunCandidate S (runs s)) =
      ((T : ℝ)⁻¹) •
        Finset.univ.sum
          (fun k : RsgfOutputIndex T =>
            rsgfResidual S (rsgfRunCandidate S (runs s)) (η k).1 (η k).2) := by
  classical
  let x : Space n := rsgfRunCandidate S (runs s)
  let g : Space n := ∇ (gaussianSmoothing S) x
  have hcard_nat : Fintype.card (RsgfOutputIndex T) = T := by
    have hcard_finset : (Icc 1 T).card = T := by
      rw [Nat.card_Icc]
      omega
    simpa [RsgfOutputIndex] using hcard_finset
  have hcard_real : (Fintype.card (RsgfOutputIndex T) : ℝ) = (T : ℝ) := by
    exact_mod_cast hcard_nat
  have hT_real : (T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hT)
  have hscale_g_nat : ((T : ℝ)⁻¹) • (T • g) = g := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hmul : (T : ℝ)⁻¹ * (T : ℝ) = 1 := inv_mul_cancel₀ hT_real
    simp [hmul]
  calc
    rsgfTwoPhaseEmpiricalGradient S runs η s -
        ∇ (gaussianSmoothing S) (rsgfRunCandidate S (runs s))
        =
      ((T : ℝ)⁻¹) • Finset.univ.sum
          (fun k : RsgfOutputIndex T => rsgfOracle S x (η k).1 (η k).2) - g := by
        simp [rsgfTwoPhaseEmpiricalGradient, rsgfEmpiricalGradient, x, g,
          one_div]
    _ =
      ((T : ℝ)⁻¹) •
        (Finset.univ.sum
          (fun k : RsgfOutputIndex T => rsgfOracle S x (η k).1 (η k).2) -
            Finset.univ.sum (fun _k : RsgfOutputIndex T => g)) := by
        simp [Finset.smul_sum, Finset.sum_const, hcard_real, hscale_g_nat, hT_real, g,
          sub_eq_add_neg, smul_add, smul_neg]
    _ =
      ((T : ℝ)⁻¹) •
        Finset.univ.sum
          (fun k : RsgfOutputIndex T =>
            rsgfResidual S (rsgfRunCandidate S (runs s)) (η k).1 (η k).2) := by
        simp [x, g, rsgfResidual_def, SOptLib.oracleEstimatorError,
          Finset.sum_sub_distrib]

/-- Fixed-candidate post-optimization empirical-residual second-moment bound,
the source scale `𝒟_N / T` from (6.1.88).  This is the product-law bridge
needed before applying the fixed-candidate Markov/Lemma 6.1(a) tail. -/
private theorem rsgf_two_phase_fixed_candidate_residual_avg_second_moment_6_1_88
    (S : Setup n Sample) (S_count N T : ℕ) (Dtilde : ℝ)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) (s : Fin S_count) :
    let μ :=
      rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
    Integrable
        (fun q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T =>
          ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
              ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ))
        μ ∧
      (∫ q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T,
          ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
              ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ)
          ∂μ) ≤
        2 * ((n : ℝ) + 4) *
          (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
            S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) /
          (T : ℝ) := by
  classical
  let μ : Measure (RsgfOptimizationRuns n Sample S_count N ×
      RsgfEvaluationPrefix n Sample T) :=
    rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
  let I : Finset (RsgfOutputIndex T) := Finset.univ
  let D_N : ℝ :=
    2 * ((n : ℝ) + 4) *
      (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
        S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ)))
  let eps :
      RsgfOutputIndex T →
        RsgfOptimizationRuns n Sample S_count N ×
          RsgfEvaluationPrefix n Sample T → Space n :=
    fun k q =>
      rsgfResidual S (rsgfRunCandidate S (q.1 s)) (q.2 k).1 (q.2 k).2
  have hT_pos : 0 < T := hT
  have hcard : I.card = T := by
    have hcard_univ : Fintype.card (RsgfOutputIndex T) = T := by
      have hcard_finset : (Icc 1 T).card = T := by
        rw [Nat.card_Icc]
        omega
      simpa [RsgfOutputIndex] using hcard_finset
    simpa [I] using hcard_univ
  have hmeas : ∀ k ∈ I, AEStronglyMeasurable (eps k) μ := by
    intro k hk
    simpa [eps, μ] using
      rsgf_two_phase_fixed_candidate_residual_coordinate_aesm
        S hN hPR s k
  have hdiag :
      ∀ k ∈ I,
        Integrable (fun q => ‖eps k q‖ ^ (2 : ℕ)) μ ∧
          (∫ q, ‖eps k q‖ ^ (2 : ℕ) ∂μ) ≤ D_N := by
    intro k hk
    simpa [eps, μ, D_N] using
      rsgf_two_phase_fixed_candidate_residual_coordinate_l2_bound
        S hN hDtilde hsteps hPR hsmooth s k
  have hcross :
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        (∫ q, ⟪eps i q, eps j q⟫_ℝ ∂μ) = 0 := by
    intro i hi j hj hij
    let νruns : Measure (RsgfOptimizationRuns n Sample S_count N) :=
      rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR
    let νeval : Measure (RsgfEvaluationPrefix n Sample T) :=
      rsgfEvaluationLaw S T
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
    haveI : IsProbabilityMeasure (rsgfSelectedRunLaw S N hPR) := by
      dsimp [rsgfSelectedRunLaw]
      infer_instance
    haveI : IsProbabilityMeasure νruns := by
      dsimp [νruns, rsgfOptimizationPhaseLaw_independentProduct]
      infer_instance
    haveI : IsProbabilityMeasure νeval := by
      dsimp [νeval, rsgfEvaluationLaw]
      infer_instance
    haveI : SFinite νeval := inferInstance
    have hint : Integrable (fun q => ⟪eps i q, eps j q⟫_ℝ) μ :=
      integrable_inner_of_integrable_sq_norm
        (hmeas i hi) (hmeas j hj) (hdiag i hi).1 (hdiag j hj).1
    calc
      (∫ q, ⟪eps i q, eps j q⟫_ℝ ∂μ)
          =
        ∫ runs : RsgfOptimizationRuns n Sample S_count N,
          ∫ η : RsgfEvaluationPrefix n Sample T,
            ⟪rsgfResidual S (rsgfRunCandidate S (runs s)) (η i).1 (η i).2,
              rsgfResidual S (rsgfRunCandidate S (runs s)) (η j).1 (η j).2⟫_ℝ
            ∂νeval
          ∂νruns := by
            simpa [μ, νruns, νeval, eps, rsgfTwoPhaseJointLaw_independentProduct] using
              MeasureTheory.integral_prod (fun q =>
                ⟪eps i q, eps j q⟫_ℝ) hint
      _ = ∫ _runs : RsgfOptimizationRuns n Sample S_count N, (0 : ℝ) ∂νruns := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun runs => by
              simpa [νeval] using
                rsgfEvaluationLaw_fixed_candidate_residual_cross_integral_eq_zero
                  S (rsgfRunCandidate S (runs s)) hij
      _ = 0 := by simp
  have havg_int :
      Integrable
        (fun q =>
          ‖((T : ℝ)⁻¹) • Finset.univ.sum (fun k : RsgfOutputIndex T => eps k q)‖ ^
            (2 : ℕ)) μ := by
    exact
      integrable_sq_norm_centeredMiniBatchAverage
        μ I T eps
        (fun q =>
          ((T : ℝ)⁻¹) • I.sum (fun k : RsgfOutputIndex T => eps k q))
        hmeas (fun k hk => (hdiag k hk).1) rfl
  have havg_bound :
      (∫ q,
          ‖((T : ℝ)⁻¹) • Finset.univ.sum (fun k : RsgfOutputIndex T => eps k q)‖ ^
            (2 : ℕ) ∂μ) ≤
        D_N / (T : ℝ) := by
    simpa [I] using
      centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero
        μ I T eps D_N hT_pos hcard hmeas hdiag hcross
  refine ⟨?_, ?_⟩
  · refine havg_int.congr (Filter.Eventually.of_forall ?_)
    intro q
    have hid :=
      rsgf_two_phase_empirical_error_eq_residual_average
        S hT q.1 q.2 s
    simpa [μ, eps] using congrArg (fun v : Space n => ‖v‖ ^ (2 : ℕ)) hid.symm
  · have hrewrite :
        (∫ q : RsgfOptimizationRuns n Sample S_count N ×
              RsgfEvaluationPrefix n Sample T,
            ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
                ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ)
            ∂μ) =
          ∫ q,
            ‖((T : ℝ)⁻¹) • Finset.univ.sum (fun k : RsgfOutputIndex T => eps k q)‖ ^
              (2 : ℕ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro q
        have hid :=
          rsgf_two_phase_empirical_error_eq_residual_average
            S hT q.1 q.2 s
        simpa [eps] using congrArg (fun v : Space n => ‖v‖ ^ (2 : ℕ)) hid
    rw [hrewrite]
    simpa [D_N, μ] using havg_bound

/-- Fixed-candidate post-optimization residual tail used in (6.1.89), obtained
from the source second-moment scale (6.1.88) by Markov's inequality. -/
private theorem rsgf_two_phase_fixed_candidate_residual_tail_6_1_89
    (S : Setup n Sample) (S_count N T : ℕ) (Dtilde lambda : ℝ)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hDtilde : 0 < Dtilde)
    (hlambda : 0 < lambda)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) (s : Fin S_count) :
    (rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR).real
        {q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T |
          ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
              ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≥
            2 * ((n : ℝ) + 4) * lambda / (T : ℝ) *
              (S.L * rsgfBbar S N Dtilde +
                ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                  S.σ ^ (2 : ℕ))} ≤
      1 / lambda := by
  classical
  let μ :=
    rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
  let f :
      RsgfOptimizationRuns n Sample S_count N ×
        RsgfEvaluationPrefix n Sample T → ℝ :=
    fun q =>
      ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
          ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ)
  let C : ℝ :=
    2 * ((n : ℝ) + 4) *
      (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
        S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) /
      (T : ℝ)
  let threshold : ℝ :=
    2 * ((n : ℝ) + 4) * lambda / (T : ℝ) *
      (S.L * rsgfBbar S N Dtilde +
        ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
          S.σ ^ (2 : ℕ))
  have hL2 :=
    rsgf_two_phase_fixed_candidate_residual_avg_second_moment_6_1_88
      S S_count N T Dtilde hN hT hDtilde hsteps hPR hsmooth s
  have hf_int : Integrable f μ := by
    simpa [f, μ] using hL2.1
  have hf_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    exact sq_nonneg _
  have h_int_le : (∫ q, f q ∂μ) ≤ C := by
    simpa [f, μ, C] using hL2.2
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hBbar_nonneg : 0 ≤ rsgfBbar S N Dtilde :=
    rsgfBbar_nonneg S hN hDtilde
  have hinside_pos :
      0 <
        S.L * rsgfBbar S N Dtilde +
          ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
            S.σ ^ (2 : ℕ) := by
    have hBbar_pos : 0 < rsgfBbar S N Dtilde :=
      rsgfBbar_pos_of_smoothing S hN hDtilde hsmooth
    have hLB_pos : 0 < S.L * rsgfBbar S N Dtilde :=
      mul_pos S.L_pos hBbar_pos
    have hmid_nonneg :
        0 ≤ ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) := by
      positivity
    have hsigma_nonneg : 0 ≤ S.σ ^ (2 : ℕ) := sq_nonneg S.σ
    nlinarith
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hratio : C / threshold ≤ 1 / lambda := by
    have hsource_le_target :
        S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
            S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) ≤
          S.L * rsgfBbar S N Dtilde +
            ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
              S.σ ^ (2 : ℕ) := by
      have hdf_nonneg : 0 ≤ S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) := by
        positivity
      have hn4_ge_half : (1 / 2 : ℝ) ≤ (n : ℝ) + 4 := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      have hmid :
          S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ)) ≤
            ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) := by
        have hN_nonneg : 0 ≤ (N : ℝ) := le_of_lt hN_pos
        calc
          S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))
              = (1 / 2) * (S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ)) := by
                field_simp [ne_of_gt hN_pos]
          _ ≤ ((n : ℝ) + 4) *
                (S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ)) := by
                exact mul_le_mul_of_nonneg_right hn4_ge_half
                  (div_nonneg hdf_nonneg hN_nonneg)
          _ =
              ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) := by
                ring
      nlinarith
    have hcoef_pos : 0 < 2 * ((n : ℝ) + 4) / (T : ℝ) := by
      positivity
    have hden_ne :
        S.L * rsgfBbar S N Dtilde +
          ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
            S.σ ^ (2 : ℕ) ≠ 0 := ne_of_gt hinside_pos
    have hcalc :
        C / threshold =
          (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
              S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) /
            (lambda *
              (S.L * rsgfBbar S N Dtilde +
                ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                  S.σ ^ (2 : ℕ))) := by
      dsimp [C, threshold]
      field_simp [ne_of_gt hT_pos, ne_of_gt hlambda, hden_ne]
    rw [hcalc]
    have htarget_pos :
        0 <
          S.L * rsgfBbar S N Dtilde +
            ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
              S.σ ^ (2 : ℕ) := hinside_pos
    have hdiv_le :
        (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
              S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) /
            (lambda *
              (S.L * rsgfBbar S N Dtilde +
                ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                  S.σ ^ (2 : ℕ))) ≤
          (S.L * rsgfBbar S N Dtilde +
                ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                  S.σ ^ (2 : ℕ)) /
            (lambda *
              (S.L * rsgfBbar S N Dtilde +
                ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                  S.σ ^ (2 : ℕ))) := by
      exact div_le_div_of_nonneg_right hsource_le_target
        (mul_nonneg hlambda.le htarget_pos.le)
    calc
      (S.L * rsgfBbar S N Dtilde + S.σ ^ (2 : ℕ) +
              S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (2 * (N : ℝ))) /
            (lambda *
              (S.L * rsgfBbar S N Dtilde +
                ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                  S.σ ^ (2 : ℕ)))
          ≤
        (S.L * rsgfBbar S N Dtilde +
              ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                S.σ ^ (2 : ℕ)) /
          (lambda *
            (S.L * rsgfBbar S N Dtilde +
              ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                S.σ ^ (2 : ℕ))) := hdiv_le
      _ = 1 / lambda := by
        let B : ℝ :=
          S.L * rsgfBbar S N Dtilde +
            ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
              S.σ ^ (2 : ℕ)
        have hB_pos : 0 < B := by
          simpa [B] using htarget_pos
        change B / (lambda * B) = 1 / lambda
        field_simp [ne_of_gt hlambda, ne_of_gt hB_pos]
  have htail :
      μ {q | f q ≥ threshold} ≤ ENNReal.ofReal (1 / lambda) :=
    measure_ge_le_of_integral_le_of_nonneg
      (μ := μ) (f := f) (t := threshold) (C := C) (b := 1 / lambda)
      hf_int hf_nonneg h_int_le hthreshold_pos hratio
  have hone_nonneg : 0 ≤ 1 / lambda := by positivity
  have htail_real :
      μ.real {q | f q ≥ threshold} ≤ 1 / lambda := by
    have hmono :=
      ENNReal.toReal_mono
        (ENNReal.ofReal_ne_top : ENNReal.ofReal (1 / lambda) ≠ ⊤) htail
    calc
      μ.real {q | f q ≥ threshold}
          = (μ {q | f q ≥ threshold}).toReal := rfl
      _ ≤ (ENNReal.ofReal (1 / lambda)).toReal := hmono
      _ = 1 / lambda := ENNReal.toReal_ofReal hone_nonneg
  simpa [μ, f, threshold] using htail_real

/-- Real-valued finite union bound over a finite type, written in the event
shape used by the fixed-candidate residual maximum. -/
private theorem measureReal_exists_fin_le_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E : ι → Set Ω) :
    μ.real {ω | ∃ i, ω ∈ E i} ≤ ∑ i, μ.real (E i) := by
  classical
  have hfin :
      ∀ F : Finset ι,
        μ.real (⋃ i ∈ (F : Set ι), E i) ≤
          Finset.sum F (fun i => μ.real (E i)) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
        simp
    | insert a F ha ih =>
        have hset :
            (⋃ i ∈ ((insert a F : Finset ι) : Set ι), E i) =
              E a ∪ (⋃ i ∈ (F : Set ι), E i) := by
          ext ω
          simp [ha]
        calc
          μ.real (⋃ i ∈ ((insert a F : Finset ι) : Set ι), E i)
              = μ.real (E a ∪ (⋃ i ∈ (F : Set ι), E i)) := by
                rw [hset]
          _ ≤ μ.real (E a) + μ.real (⋃ i ∈ (F : Set ι), E i) :=
                measureReal_union_le (E a) (⋃ i ∈ (F : Set ι), E i)
          _ ≤ μ.real (E a) + Finset.sum F (fun i => μ.real (E i)) :=
                add_le_add le_rfl ih
          _ = Finset.sum (insert a F) (fun i => μ.real (E i)) := by
                simp [ha]
  have hset : {ω | ∃ i, ω ∈ E i} = ⋃ i, E i := by
    ext ω
    simp
  simpa [hset] using hfin (Finset.univ : Finset ι)

/-- Smoothing-bias square bound used in the 2-RSGF selector decomposition,
equation (6.1.85). -/
private theorem rsgf_smoothing_bias_sq_bound_6_1_85
    (S : Setup n Sample) {N : ℕ}
    (hN : 1 ≤ N)
    (hsmooth : RsgfSmoothingParameterPolicy S N)
    (x : Space n) :
    ‖∇ (gaussianSmoothing S) x - ∇ (objective S) x‖ ^ (2 : ℕ) ≤
      ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) /
        (8 * (N : ℝ)) := by
  classical
  let e : Space n := ∇ (gaussianSmoothing S) x - ∇ (objective S) x
  let M : ℝ :=
    ∫ u : Space n, ‖u‖ ^ (3 : ℕ) ∂gaussianDirectionLaw n
  let C : ℝ := S.μ * S.L / 2
  have herr_norm : ‖e‖ ≤ C * M := by
    simpa [e, C, M] using gaussianSmoothing_gradient_error_le S x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg fun u => by positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hμ_nonneg : 0 ≤ S.μ := le_of_lt S.μ_pos
    have hL_nonneg : 0 ≤ S.L := le_of_lt S.L_pos
    nlinarith [mul_nonneg hμ_nonneg hL_nonneg]
  have hCM_nonneg : 0 ≤ C * M := mul_nonneg hC_nonneg hM_nonneg
  have herr_sq :
      ‖e‖ ^ (2 : ℕ) ≤ (C * M) ^ (2 : ℕ) := by
    nlinarith [herr_norm, norm_nonneg e, hCM_nonneg]
  have hM_sq :
      M ^ (2 : ℕ) ≤ ((n : ℝ) + 3) ^ (3 : ℕ) := by
    simpa [M] using gaussian_norm_three_integral_sq_le (n := n)
  have hcoeff_nonneg : 0 ≤ S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 4 := by
    positivity
  have hbias_mu :
      ‖e‖ ^ (2 : ℕ) ≤
        S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 4 *
          ((n : ℝ) + 3) ^ (3 : ℕ) := by
    calc
      ‖e‖ ^ (2 : ℕ) ≤ (C * M) ^ (2 : ℕ) := herr_sq
      _ = (S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 4) * M ^ (2 : ℕ) := by
            dsimp [C]
            ring
      _ ≤
          S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 4 *
            ((n : ℝ) + 3) ^ (3 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hM_sq hcoeff_nonneg
  have hμsq :
      S.μ ^ (2 : ℕ) ≤
        Df S ^ (2 : ℕ) /
          (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ))) :=
    rsgf_smoothing_parameter_sq_bound S hN hsmooth
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  have hcube3 :
      ((n : ℝ) + 3) ^ (3 : ℕ) ≤ ((n : ℝ) + 4) ^ (3 : ℕ) := by
    have hbase_nonneg : 0 ≤ (n : ℝ) + 3 := by
      exact add_nonneg (Nat.cast_nonneg n) (by norm_num)
    have hbase_le : (n : ℝ) + 3 ≤ (n : ℝ) + 4 := by norm_num
    exact pow_le_pow_left₀ hbase_nonneg hbase_le 3
  have hscale_nonneg :
      0 ≤ S.L ^ (2 : ℕ) / 4 * ((n : ℝ) + 3) ^ (3 : ℕ) := by
    positivity
  have hsub :
      S.μ ^ (2 : ℕ) * S.L ^ (2 : ℕ) / 4 *
          ((n : ℝ) + 3) ^ (3 : ℕ) ≤
        (Df S ^ (2 : ℕ) /
            (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) *
          S.L ^ (2 : ℕ) / 4 *
          ((n : ℝ) + 3) ^ (3 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right hμsq hscale_nonneg
    simpa [mul_assoc, div_eq_mul_inv] using hmul
  have hdim :
      (Df S ^ (2 : ℕ) /
            (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) *
          S.L ^ (2 : ℕ) / 4 *
          ((n : ℝ) + 3) ^ (3 : ℕ) ≤
        ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) /
          (8 * (N : ℝ)) := by
    have hcoef_nonneg :
        0 ≤ Df S ^ (2 : ℕ) * S.L ^ (2 : ℕ) / (8 * (N : ℝ)) := by
      positivity
    have hdim' :
        ((n : ℝ) + 3) ^ (3 : ℕ) / ((n : ℝ) + 4) ^ (2 : ℕ) ≤
          (n : ℝ) + 4 := by
      have hden_pos : 0 < ((n : ℝ) + 4) ^ (2 : ℕ) := by positivity
      rw [div_le_iff₀ hden_pos]
      calc
        ((n : ℝ) + 3) ^ (3 : ℕ)
            ≤ ((n : ℝ) + 4) ^ (3 : ℕ) := hcube3
        _ = ((n : ℝ) + 4) * ((n : ℝ) + 4) ^ (2 : ℕ) := by ring
    calc
      (Df S ^ (2 : ℕ) /
            (((n : ℝ) + 4) ^ (2 : ℕ) * (2 * (N : ℝ)))) *
          S.L ^ (2 : ℕ) / 4 *
          ((n : ℝ) + 3) ^ (3 : ℕ)
          =
        (Df S ^ (2 : ℕ) * S.L ^ (2 : ℕ) / (8 * (N : ℝ))) *
          (((n : ℝ) + 3) ^ (3 : ℕ) / ((n : ℝ) + 4) ^ (2 : ℕ)) := by
            field_simp [ne_of_gt hN_pos, ne_of_gt hn4_pos]
            ring
      _ ≤
        (Df S ^ (2 : ℕ) * S.L ^ (2 : ℕ) / (8 * (N : ℝ))) *
          ((n : ℝ) + 4) := by
            exact mul_le_mul_of_nonneg_left hdim' hcoef_nonneg
      _ =
        ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) /
          (8 * (N : ℝ)) := by ring
  exact le_trans hbias_mu (le_trans hsub hdim)

/-- Pointwise selector decomposition from the proof of Theorem 6.4(a),
equation (6.1.86).  If all post-optimization empirical residuals are bounded
by `R`, the selected true-gradient square is controlled by any reference run's
true-gradient square, the common residual budget, and the smoothing bias. -/
private theorem rsgf_two_phase_selector_decomposition_pointwise_6_1_86
    (S : Setup n Sample) {S_count N T : ℕ}
    (hS : 0 < S_count) (hN : 1 ≤ N)
    (hsmooth : RsgfSmoothingParameterPolicy S N)
    (runs : RsgfOptimizationRuns n Sample S_count N)
    (η : RsgfEvaluationPrefix n Sample T) (s0 : Fin S_count)
    {R : ℝ}
    (hres :
      ∀ s : Fin S_count,
        ‖rsgfTwoPhaseEmpiricalGradient S runs η s -
            ∇ (gaussianSmoothing S) (rsgfRunCandidate S (runs s))‖ ^ (2 : ℕ) ≤ R) :
    ‖∇ (objective S) (rsgfTwoPhaseSelectedOutput S runs η hS)‖ ^ (2 : ℕ) ≤
      4 * ‖∇ (objective S) (rsgfRunCandidate S (runs s0))‖ ^ (2 : ℕ) +
        12 * R +
          12 * (((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) /
            (8 * (N : ℝ))) := by
  classical
  let sstar : Fin S_count := rsgfTwoPhaseSelector S runs η hS
  let xstar : Space n := rsgfRunCandidate S (runs sstar)
  let x0 : Space n := rsgfRunCandidate S (runs s0)
  let gstar : Space n := rsgfTwoPhaseEmpiricalGradient S runs η sstar
  let g0 : Space n := rsgfTwoPhaseEmpiricalGradient S runs η s0
  let fstar : Space n := ∇ (objective S) xstar
  let f0 : Space n := ∇ (objective S) x0
  let smstar : Space n := ∇ (gaussianSmoothing S) xstar
  let sm0 : Space n := ∇ (gaussianSmoothing S) x0
  let B : ℝ :=
    ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) /
      (8 * (N : ℝ))
  have hselector :
      ‖gstar‖ ^ (2 : ℕ) ≤ ‖g0‖ ^ (2 : ℕ) := by
    simpa [gstar, g0, sstar] using
      rsgfTwoPhaseSelector_spec S runs η hS s0
  have hbias0 : ‖sm0 - f0‖ ^ (2 : ℕ) ≤ B := by
    simpa [B, sm0, f0, x0] using
      rsgf_smoothing_bias_sq_bound_6_1_85 S hN hsmooth x0
  have hbiasstar : ‖smstar - fstar‖ ^ (2 : ℕ) ≤ B := by
    simpa [B, smstar, fstar, xstar] using
      rsgf_smoothing_bias_sq_bound_6_1_85 S hN hsmooth xstar
  have hres0 : ‖g0 - sm0‖ ^ (2 : ℕ) ≤ R := by
    simpa [g0, sm0, x0] using hres s0
  have hresstar : ‖gstar - smstar‖ ^ (2 : ℕ) ≤ R := by
    simpa [gstar, smstar, xstar, sstar] using hres sstar
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hR_nonneg : 0 ≤ R :=
    le_trans (sq_nonneg ‖g0 - sm0‖) hres0
  have hg0_split :
      g0 = f0 + ((g0 - sm0) + (sm0 - f0)) := by
    abel
  have hg0_first :
      ‖g0‖ ^ (2 : ℕ) ≤
        2 * ‖f0‖ ^ (2 : ℕ) +
          2 * ‖(g0 - sm0) + (sm0 - f0)‖ ^ (2 : ℕ) := by
    calc
      ‖g0‖ ^ (2 : ℕ) =
          ‖f0 + ((g0 - sm0) + (sm0 - f0))‖ ^ (2 : ℕ) := by
            exact congrArg (fun y : Space n => ‖y‖ ^ (2 : ℕ)) hg0_split
      _ ≤
          2 * ‖f0‖ ^ (2 : ℕ) +
            2 * ‖(g0 - sm0) + (sm0 - f0)‖ ^ (2 : ℕ) :=
          SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
            f0 ((g0 - sm0) + (sm0 - f0))
  have hg0_err :
      ‖(g0 - sm0) + (sm0 - f0)‖ ^ (2 : ℕ) ≤
        2 * ‖g0 - sm0‖ ^ (2 : ℕ) +
          2 * ‖sm0 - f0‖ ^ (2 : ℕ) :=
    SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
      (g0 - sm0) (sm0 - f0)
  have hg0_bound :
      ‖g0‖ ^ (2 : ℕ) ≤ 2 * ‖f0‖ ^ (2 : ℕ) + 4 * R + 4 * B := by
    nlinarith [hg0_first, hg0_err, hres0, hbias0]
  have hstar_err_split :
      fstar - gstar = -((gstar - smstar) + (smstar - fstar)) := by
    abel
  have hstar_err_young :
      ‖fstar - gstar‖ ^ (2 : ℕ) ≤
        2 * ‖gstar - smstar‖ ^ (2 : ℕ) +
          2 * ‖smstar - fstar‖ ^ (2 : ℕ) := by
    calc
      ‖fstar - gstar‖ ^ (2 : ℕ) =
          ‖(gstar - smstar) + (smstar - fstar)‖ ^ (2 : ℕ) := by
            rw [hstar_err_split, norm_neg]
      _ ≤
          2 * ‖gstar - smstar‖ ^ (2 : ℕ) +
            2 * ‖smstar - fstar‖ ^ (2 : ℕ) :=
          SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
            (gstar - smstar) (smstar - fstar)
  have hstar_err_bound :
      ‖fstar - gstar‖ ^ (2 : ℕ) ≤ 2 * R + 2 * B := by
    nlinarith [hstar_err_young, hresstar, hbiasstar]
  have hfstar_split : fstar = gstar + (fstar - gstar) := by
    abel
  have hfstar_young :
      ‖fstar‖ ^ (2 : ℕ) ≤
        2 * ‖gstar‖ ^ (2 : ℕ) + 2 * ‖fstar - gstar‖ ^ (2 : ℕ) := by
    calc
      ‖fstar‖ ^ (2 : ℕ) =
          ‖gstar + (fstar - gstar)‖ ^ (2 : ℕ) := by
            exact congrArg (fun y : Space n => ‖y‖ ^ (2 : ℕ)) hfstar_split
      _ ≤
          2 * ‖gstar‖ ^ (2 : ℕ) + 2 * ‖fstar - gstar‖ ^ (2 : ℕ) :=
          SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
            gstar (fstar - gstar)
  have hmain :
      ‖fstar‖ ^ (2 : ℕ) ≤
        4 * ‖f0‖ ^ (2 : ℕ) + 12 * R + 12 * B := by
    nlinarith [hfstar_young, hselector, hg0_bound, hstar_err_bound]
  simpa [rsgfTwoPhaseSelectedOutput, sstar, xstar, x0, fstar, f0, B]
    using hmain

/-- Event form of the selector decomposition used in Theorem 6.4(a): the
Theorem 6.4 failure event is contained in the union of the optimization-phase
failure event and the post-optimization residual-maximum failure event. -/
private theorem rsgf_theorem64_failure_subset_opt_or_residual_max
    (S : Setup n Sample) (S_count N T : ℕ) (Dtilde lambda : ℝ)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS ⊆
      Prod.fst ⁻¹'
        {runs : RsgfOptimizationRuns n Sample S_count N |
          ∀ s : Fin S_count,
            ‖∇ (objective S) (rsgfRunCandidate S (runs s))‖ ^ (2 : ℕ) ≥
              2 * S.L * rsgfBbar S N Dtilde} ∪
        {q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T |
          ∃ s : Fin S_count,
            ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
                ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≥
              2 * ((n : ℝ) + 4) * lambda / (T : ℝ) *
                (S.L * rsgfBbar S N Dtilde +
                  ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                    S.σ ^ (2 : ℕ))} := by
  classical
  intro q hq
  let B : ℝ :=
    ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) /
      (8 * (N : ℝ))
  let C : ℝ :=
    2 * ((n : ℝ) + 4) * lambda / (T : ℝ) *
      (S.L * rsgfBbar S N Dtilde +
        ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
          S.σ ^ (2 : ℕ))
  by_contra hnot
  have hnot' :
      ¬
        ((∀ s : Fin S_count,
            ‖∇ (objective S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≥
              2 * S.L * rsgfBbar S N Dtilde) ∨
          (∃ s : Fin S_count,
            ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
                ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≥
              C)) := by
    simpa [C, Set.mem_union, Set.mem_preimage] using hnot
  simp only [not_or, not_forall, not_exists, not_le] at hnot'
  rcases hnot' with ⟨⟨s0, hopt_good⟩, hres_good⟩
  have hres_le :
      ∀ s : Fin S_count,
        ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
            ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≤ C := by
    intro s
    exact le_of_lt (hres_good s)
  have hpoint :=
    rsgf_two_phase_selector_decomposition_pointwise_6_1_86
      S hS hN hsmooth q.1 q.2 s0 (R := C) hres_le
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hBbar_nonneg : 0 ≤ rsgfBbar S N Dtilde :=
    rsgfBbar_nonneg S hN hDtilde
  have hinside_nonneg :
      0 ≤
        S.L * rsgfBbar S N Dtilde +
          ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
            S.σ ^ (2 : ℕ) := by
    have hLB_nonneg : 0 ≤ S.L * rsgfBbar S N Dtilde :=
      mul_nonneg S.L_pos.le hBbar_nonneg
    have hmid_nonneg :
        0 ≤ ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) := by
      positivity
    have hsigma_nonneg : 0 ≤ S.σ ^ (2 : ℕ) := sq_nonneg S.σ
    nlinarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hcoef_nonneg : 0 ≤ 2 * ((n : ℝ) + 4) * lambda / (T : ℝ) := by
      positivity
    exact mul_nonneg hcoef_nonneg hinside_nonneg
  have hthreshold_eq :
      rsgfTheorem64Threshold S N T Dtilde lambda =
        8 * S.L * rsgfBbar S N Dtilde + 12 * C + 12 * B := by
    dsimp [rsgfTheorem64Threshold, C, B]
    field_simp [ne_of_gt hT_pos, ne_of_gt hN_pos]
    ring
  have hscalar_lt :
      4 * ‖∇ (objective S) (rsgfRunCandidate S (q.1 s0))‖ ^ (2 : ℕ) +
            12 * C + 12 * B <
        rsgfTheorem64Threshold S N T Dtilde lambda := by
    rw [hthreshold_eq]
    nlinarith [hopt_good]
  have hselected_lt :
      ‖∇ (objective S) (rsgfTwoPhaseSelectedOutput S q.1 q.2 hS)‖ ^ (2 : ℕ) <
        rsgfTheorem64Threshold S N T Dtilde lambda := by
    exact lt_of_le_of_lt (by simpa [B] using hpoint) hscalar_lt
  have hselected_ge :
      ‖∇ (objective S) (rsgfTwoPhaseSelectedOutput S q.1 q.2 hS)‖ ^ (2 : ℕ) ≥
        rsgfTheorem64Threshold S N T Dtilde lambda := by
    simpa [rsgfTheorem64FailureEvent] using hq
  nlinarith

/-- Post-optimization residual maximum tail from Theorem 6.4(a), equation
(6.1.89).  This is the remaining source-derived fixed-candidate martingale
tail plus finite union bound over the `S_count` candidates. -/
private theorem rsgf_two_phase_residual_max_tail_6_1_89
    (S : Setup n Sample) (S_count N T : ℕ) (Dtilde lambda : ℝ)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    (rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR).real
        {q : RsgfOptimizationRuns n Sample S_count N ×
            RsgfEvaluationPrefix n Sample T |
          ∃ s : Fin S_count,
            ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
                ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≥
              2 * ((n : ℝ) + 4) * lambda / (T : ℝ) *
                (S.L * rsgfBbar S N Dtilde +
                  ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                    S.σ ^ (2 : ℕ))} ≤
      (S_count : ℝ) / lambda := by
  classical
  let μ :=
    rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
  let E :
      Fin S_count →
        Set (RsgfOptimizationRuns n Sample S_count N ×
          RsgfEvaluationPrefix n Sample T) :=
    fun s =>
      {q |
        ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
            ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≥
          2 * ((n : ℝ) + 4) * lambda / (T : ℝ) *
            (S.L * rsgfBbar S N Dtilde +
              ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                S.σ ^ (2 : ℕ))}
  have perTail : ∀ s : Fin S_count, μ.real (E s) ≤ 1 / lambda := by
    intro s
    simpa [μ, E] using
      rsgf_two_phase_fixed_candidate_residual_tail_6_1_89
        S S_count N T Dtilde lambda hN hT hDtilde hlambda
        hsteps hPR hsmooth s
  calc
    μ.real {q | ∃ s : Fin S_count, q ∈ E s}
        ≤ ∑ s : Fin S_count, μ.real (E s) :=
          measureReal_exists_fin_le_sum μ E
    _ ≤ ∑ _s : Fin S_count, (1 / lambda : ℝ) := by
          exact Finset.sum_le_sum (fun s _hs => perTail s)
    _ = (S_count : ℝ) / lambda := by
          simp [Fintype.card_fin, div_eq_mul_inv]

/-- Failure event for the `(epsilon, Lambda)` stationarity target in Theorem
6.4(b). -/
def rsgfTwoPhaseEpsilonFailureEvent (S : Setup n Sample)
    (S_count N T : ℕ) (ε : ℝ) (hS : 0 < S_count) :
    Set (RsgfOptimizationRuns n Sample S_count N ×
      RsgfEvaluationPrefix n Sample T) :=
  {q |
    ‖∇ (objective S) (rsgfTwoPhaseSelectedOutput S q.1 q.2 hS)‖ ^ (2 : ℕ) ≥ ε}

/-- Real-valued failure probability for the `(epsilon, Lambda)` solution
statement in Theorem 6.4(b). -/
def rsgfTwoPhaseEpsilonFailureProbability (S : Setup n Sample)
    (S_count N T : ℕ) (ε : ℝ) (hS : 0 < S_count)
    (Dtilde : ℝ) (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N) : ℝ :=
  (rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR).real
    (rsgfTwoPhaseEpsilonFailureEvent S S_count N T ε hS)

/-- Helper-level real-valued failure probability for the `(epsilon, Lambda)`
target under the formalization-only product-law realization. -/
def rsgfTwoPhaseEpsilonFailureProbabilityProductLaw (S : Setup n Sample)
    (S_count N T : ℕ) (ε : ℝ) (hS : 0 < S_count)
    (Dtilde : ℝ) (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N) : ℝ :=
  (rsgfTwoPhaseJointLaw S S_count N T hPR).real
    (rsgfTwoPhaseEpsilonFailureEvent S S_count N T ε hS)

/-- Real-valued failure probability in the product-law realization of Theorem
6.4(b). -/
def rsgfTwoPhaseEpsilonFailureProbabilityProductRealization (S : Setup n Sample)
    (S_count N T : ℕ) (ε : ℝ) (hS : 0 < S_count)
    (Dtilde : ℝ) (hN : 1 ≤ N) (hPR_source : RsgfOutputPMFSourceChoice S N)
    (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde) : ℝ :=
  (rsgfTwoPhaseJointLawProductRealization S S_count N T Dtilde hN hPR_source hDtilde hsteps).real
    (rsgfTwoPhaseEpsilonFailureEvent S S_count N T ε hS)

/-- Helper-level Theorem 6.4(a) variant under the formalization-only independent
product law for optimization runs and post-optimization samples. -/
theorem theorem_6_4a_twoPhase_independentProduct
    (S : Setup n Sample) (S_count N T : ℕ) (Dtilde lambda : ℝ)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    rsgfTheorem64FailureProbability S S_count N T Dtilde lambda hS hN hDtilde
        hsteps hPR ≤
      (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count := by
  classical
  have hopt :=
    rsgf_two_phase_optimization_min_tail_6_1_87
      S hS hN hDtilde hsteps hPR hsmooth
  let optFail : Set (RsgfOptimizationRuns n Sample S_count N) :=
    {runs |
      ∀ s : Fin S_count,
        ‖∇ (objective S) (rsgfRunCandidate S (runs s))‖ ^ (2 : ℕ) ≥
          2 * S.L * rsgfBbar S N Dtilde}
  let residualMaxFail :
      Set (RsgfOptimizationRuns n Sample S_count N ×
        RsgfEvaluationPrefix n Sample T) :=
    {q |
      ∃ s : Fin S_count,
        ‖rsgfTwoPhaseEmpiricalGradient S q.1 q.2 s -
            ∇ (gaussianSmoothing S) (rsgfRunCandidate S (q.1 s))‖ ^ (2 : ℕ) ≥
          2 * ((n : ℝ) + 4) * lambda / (T : ℝ) *
            (S.L * rsgfBbar S N Dtilde +
              ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ) +
                S.σ ^ (2 : ℕ))}
  have hsubset :
      rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS ⊆
        Prod.fst ⁻¹' optFail ∪ residualMaxFail := by
    simpa [optFail, residualMaxFail] using
      rsgf_theorem64_failure_subset_opt_or_residual_max
        S S_count N T Dtilde lambda hS hN hT hDtilde hlambda hsmooth
  let μ :
      Measure (RsgfOptimizationRuns n Sample S_count N ×
        RsgfEvaluationPrefix n Sample T) :=
    rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
  let μopt : Measure (RsgfOptimizationRuns n Sample S_count N) :=
    rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR
  let μeval : Measure (RsgfEvaluationPrefix n Sample T) :=
    rsgfEvaluationLaw S T
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
  haveI : IsProbabilityMeasure μeval := by
    dsimp [μeval, rsgfEvaluationLaw]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfSelectedRunLaw S N hPR) := by
    dsimp [rsgfSelectedRunLaw]
    infer_instance
  haveI : IsProbabilityMeasure μopt := by
    dsimp [μopt, rsgfOptimizationPhaseLaw_independentProduct]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, μopt, μeval, rsgfTwoPhaseJointLaw_independentProduct]
    infer_instance
  have hprob_opt_eq :
      μ.real (Prod.fst ⁻¹' optFail) = μopt.real optFail := by
    have hset :
        Prod.fst ⁻¹' optFail =
          optFail ×ˢ (Set.univ : Set (RsgfEvaluationPrefix n Sample T)) := by
      ext q
      simp
    calc
      μ.real (Prod.fst ⁻¹' optFail) =
          ((μopt.prod μeval).real
            (optFail ×ˢ (Set.univ : Set (RsgfEvaluationPrefix n Sample T)))) := by
            simp [μ, μopt, μeval, rsgfTwoPhaseJointLaw_independentProduct, hset]
      _ = μopt.real optFail := by
            simp
  have hprob_opt :
      μ.real (Prod.fst ⁻¹' optFail) ≤ (1 / 2 : ℝ) ^ S_count := by
    rw [hprob_opt_eq]
    simpa [μopt, optFail] using hopt
  have hprob_residual :
      μ.real residualMaxFail ≤ (S_count : ℝ) / lambda := by
    simpa [μ, residualMaxFail] using
      rsgf_two_phase_residual_max_tail_6_1_89
        S S_count N T Dtilde lambda hS hN hT hDtilde hlambda
        hsteps hPR hsmooth
  have hfailure_bound :
      μ.real (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS) ≤
        (1 / 2 : ℝ) ^ S_count + (S_count : ℝ) / lambda := by
    calc
      μ.real (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS)
          ≤ μ.real (Prod.fst ⁻¹' optFail ∪ residualMaxFail) :=
            measureReal_mono hsubset (by finiteness)
      _ ≤ μ.real (Prod.fst ⁻¹' optFail) + μ.real residualMaxFail :=
            measureReal_union_le (Prod.fst ⁻¹' optFail) residualMaxFail
      _ ≤ (1 / 2 : ℝ) ^ S_count + (S_count : ℝ) / lambda :=
            add_le_add hprob_opt hprob_residual
  have hS_over_lambda :
      (S_count : ℝ) / lambda ≤ (S_count + 1 : ℝ) / lambda := by
    have hcast : (S_count : ℝ) ≤ (S_count + 1 : ℝ) := by
      exact_mod_cast Nat.le_succ S_count
    exact div_le_div_of_nonneg_right hcast hlambda.le
  calc
    rsgfTheorem64FailureProbability S S_count N T Dtilde lambda hS hN hDtilde
        hsteps hPR =
        μ.real (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS) := by
          simp [μ, rsgfTheorem64FailureProbability]
    _ ≤ (1 / 2 : ℝ) ^ S_count + (S_count : ℝ) / lambda := hfailure_bound
    _ ≤ (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count := by
          nlinarith

/-- Helper-level Theorem 6.4(a) variant under the formalization-only two-phase
product law.  The source theorem itself does not print this independence
interface. -/
theorem theorem_6_4a_twoPhase_productLaw
    (S : Setup n Sample) (S_count N T : ℕ) (Dtilde lambda : ℝ)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    rsgfTheorem64FailureProbabilityProductLaw S S_count N T Dtilde lambda hS hN
        hDtilde hsteps hPR ≤
      (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count := by
  exact (show
    rsgfTheorem64FailureProbability S S_count N T Dtilde lambda hS hN hDtilde
        hsteps hPR ≤
      (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count from
    theorem_6_4a_twoPhase_independentProduct S S_count N T Dtilde lambda hS
      hN hT hDtilde hlambda hsteps hPR hsmooth)

/-- Formalization-level Theorem 6.4(a) realization.  The source proof uses an
optimization-run product factorization that is not printed as a paper
assumption, so this declaration is not an A-level source theorem boundary. -/
theorem theorem_6_4a_productLawRealization
    (S : Setup n Sample) (S_count N T : ℕ) (Dtilde lambda : ℝ)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hPR_source : RsgfOutputPMFSourceChoice S N)
    (hDtilde : 0 < Dtilde) (hlambda : 0 < lambda)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    rsgfTheorem64FailureProbabilityProductRealization S S_count N T Dtilde lambda hS hN
        hPR_source hDtilde hsteps ≤
      (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count := by
  classical
  let hPR : RsgfOutputWeightsAdmissible S N :=
    rsgfOutputPMFSourceChoice_admissible S hPR_source
  have hpmf :
      rsgfOutputPMFTheorem63 S N hPR_source =
        rsgfOutputPMF S N hPR := by
    ext R
    rw [rsgfOutputPMFTheorem63_apply, rsgfOutputPMF_apply]
  have hrun :
      rsgfSelectedRunLawTheorem63 S N hPR_source =
        rsgfSelectedRunLawCanonical S N hPR := by
    unfold rsgfSelectedRunLawTheorem63 rsgfSelectedRunLawCanonical
    rw [hpmf]
  have hlaw :
      rsgfTwoPhaseJointLawProductRealization S S_count N T Dtilde hN hPR_source
          hDtilde hsteps =
        rsgfTwoPhaseJointLaw S S_count N T hPR := by
    unfold rsgfTwoPhaseJointLawProductRealization
      rsgfOptimizationPhaseLawProductRealization
      rsgfTwoPhaseJointLaw rsgfOptimizationPhaseLaw
    rw [hrun]
  have hprob :
      rsgfTheorem64FailureProbabilityProductRealization S S_count N T Dtilde
          lambda hS hN hPR_source hDtilde hsteps =
        rsgfTheorem64FailureProbabilityProductLaw S S_count N T Dtilde lambda
          hS hN hDtilde hsteps hPR := by
    unfold rsgfTheorem64FailureProbabilityProductRealization
      rsgfTheorem64FailureProbabilityProductLaw
    rw [hlaw]
  rw [hprob]
  exact theorem_6_4a_twoPhase_productLaw S S_count N T Dtilde lambda hS hN
    hT hDtilde hlambda hsteps hPR hsmooth

/-- Helper-level expansion of the SZO-call-count expression in (6.1.84), using
the policies (6.1.32), (6.1.82), and (6.1.83). -/
theorem rsgfTwoPhase_call_count_formula
    (S : Setup n Sample) (ε Λ Dtilde : ℝ)
    (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    rsgfTwoPhaseCallCount S ε Λ Dtilde =
      2 * (rsgfConfidenceRunCount Λ : ℝ) *
        (rsgfIterationLimitPolicy S ε Dtilde +
          rsgfPostOptimizationSamplePolicy S ε Λ) := by
  rfl

private theorem rsgf_epsilon_failure_probability_le_threshold_failure
    (S : Setup n Sample) (S_count N T : ℕ) (ε Dtilde lambda : ℝ)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hthreshold : rsgfTheorem64Threshold S N T Dtilde lambda ≤ ε) :
    rsgfTwoPhaseEpsilonFailureProbability S S_count N T ε hS Dtilde hN hDtilde
        hsteps hPR ≤
      rsgfTheorem64FailureProbability S S_count N T Dtilde lambda hS hN
        hDtilde hsteps hPR := by
  let μ :=
    rsgfTwoPhaseJointLaw_independentProduct S S_count N T hN hPR
  let μopt : Measure (RsgfOptimizationRuns n Sample S_count N) :=
    rsgfOptimizationPhaseLaw_independentProduct S S_count N hN hPR
  let μeval : Measure (RsgfEvaluationPrefix n Sample T) :=
    rsgfEvaluationLaw S T
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
  haveI : IsProbabilityMeasure μeval := by
    dsimp [μeval, rsgfEvaluationLaw]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfSelectedRunLaw S N hPR) := by
    dsimp [rsgfSelectedRunLaw]
    infer_instance
  haveI : IsProbabilityMeasure μopt := by
    dsimp [μopt, rsgfOptimizationPhaseLaw_independentProduct]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, μopt, μeval, rsgfTwoPhaseJointLaw_independentProduct]
    infer_instance
  have hsubset :
      rsgfTwoPhaseEpsilonFailureEvent S S_count N T ε hS ⊆
        rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS := by
    intro q hq
    exact le_trans hthreshold hq
  calc
    rsgfTwoPhaseEpsilonFailureProbability S S_count N T ε hS Dtilde hN
        hDtilde hsteps hPR =
        μ.real (rsgfTwoPhaseEpsilonFailureEvent S S_count N T ε hS) := by
          simp [μ, rsgfTwoPhaseEpsilonFailureProbability]
    _ ≤ μ.real (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS) :=
          measureReal_mono hsubset (by finiteness)
    _ =
          rsgfTheorem64FailureProbability S S_count N T Dtilde lambda hS hN
          hDtilde hsteps hPR := by
          simp [μ, rsgfTheorem64FailureProbability]

private theorem rsgf_epsilon_failure_probability_productLaw_le_threshold_failure
    (S : Setup n Sample) (S_count N T : ℕ) (ε Dtilde lambda : ℝ)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hthreshold : rsgfTheorem64Threshold S N T Dtilde lambda ≤ ε) :
    rsgfTwoPhaseEpsilonFailureProbabilityProductLaw S S_count N T ε hS Dtilde hN
        hDtilde hsteps hPR ≤
      rsgfTheorem64FailureProbabilityProductLaw S S_count N T Dtilde lambda hS hN
        hDtilde hsteps hPR := by
  let μ := rsgfTwoPhaseJointLaw S S_count N T hPR
  let μopt : Measure (RsgfOptimizationRuns n Sample S_count N) :=
    rsgfOptimizationPhaseLaw S S_count N hPR
  let μeval : Measure (RsgfEvaluationPrefix n Sample T) :=
    rsgfEvaluationLaw S T
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
  haveI : IsProbabilityMeasure μeval := by
    dsimp [μeval, rsgfEvaluationLaw]
    infer_instance
  haveI : IsProbabilityMeasure (rsgfSelectedRunLawCanonical S N hPR) := by
    dsimp [rsgfSelectedRunLawCanonical]
    infer_instance
  haveI : IsProbabilityMeasure μopt := by
    dsimp [μopt, rsgfOptimizationPhaseLaw]
    infer_instance
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, μopt, μeval, rsgfTwoPhaseJointLaw]
    infer_instance
  have hsubset :
      rsgfTwoPhaseEpsilonFailureEvent S S_count N T ε hS ⊆
        rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS := by
    intro q hq
    exact le_trans hthreshold hq
  calc
    rsgfTwoPhaseEpsilonFailureProbabilityProductLaw S S_count N T ε hS Dtilde hN
        hDtilde hsteps hPR =
        μ.real (rsgfTwoPhaseEpsilonFailureEvent S S_count N T ε hS) := by
          simp [μ, rsgfTwoPhaseEpsilonFailureProbabilityProductLaw]
    _ ≤ μ.real (rsgfTheorem64FailureEvent S S_count N T Dtilde lambda hS) :=
          measureReal_mono hsubset (by finiteness)
    _ =
        rsgfTheorem64FailureProbabilityProductLaw S S_count N T Dtilde lambda hS hN
          hDtilde hsteps hPR := by
          simp [μ, rsgfTheorem64FailureProbabilityProductLaw]

private theorem rsgf_6_4b_confidence_rhs_le
    {S_count : ℕ} {Λ : ℝ} (hΛ0 : 0 < Λ)
    (hS_policy : RsgfConfidenceRunPolicy S_count Λ) :
    (S_count + 1 : ℝ) / (2 * (S_count + 1 : ℝ) / Λ) +
        (1 / 2 : ℝ) ^ S_count ≤ Λ := by
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ0
  have hSp1_pos : 0 < (S_count + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos S_count
  have hSp1_ne : (S_count + 1 : ℝ) ≠ 0 := ne_of_gt hSp1_pos
  have hfrac :
      (S_count + 1 : ℝ) / (2 * (S_count + 1 : ℝ) / Λ) = Λ / 2 := by
    field_simp [hΛ_ne, hSp1_ne]
  have htail :
      (1 / 2 : ℝ) ^ S_count ≤ Λ / 2 :=
    rsgfConfidenceRunPolicy_geometric_tail hΛ0 hS_policy
  nlinarith

private theorem rsgf_6_4b_sampling_prefactor_eq_two_div_max
    (S : Setup n Sample) (S_count T : ℕ) (ε Λ : ℝ)
    (hε : 0 < ε) (hΛ0 : 0 < Λ)
    (hS_policy : RsgfConfidenceRunPolicy S_count Λ)
    (hT_policy : RsgfPostOptimizationSamplePolicy S T ε Λ) :
    24 * ((n : ℝ) + 4) * (2 * (S_count + 1 : ℝ) / Λ) / (T : ℝ) =
      2 / max 1 (6 * S.σ ^ (2 : ℕ) / ε) := by
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ0
  have hn4_pos : 0 < (n : ℝ) + 4 := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    nlinarith
  have hrun_pos : 0 < (rsgfConfidenceRunCount Λ + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos (rsgfConfidenceRunCount Λ)
  have hmax_pos : 0 < max 1 (6 * S.σ ^ (2 : ℕ) / ε) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hT_eq :
      (T : ℝ) =
        24 * ((n : ℝ) + 4) * (rsgfConfidenceRunCount Λ + 1 : ℝ) / Λ *
          max 1 (6 * S.σ ^ (2 : ℕ) / ε) := by
    simpa [RsgfPostOptimizationSamplePolicy, rsgfPostOptimizationSamplePolicy]
      using hT_policy
  rw [hT_eq, hS_policy]
  field_simp [hΛ_ne, ne_of_gt hn4_pos, ne_of_gt hrun_pos, ne_of_gt hmax_pos]

private theorem rsgf_6_4b_scalar_threshold_budget
    {ε x y sig2 : ℝ}
    (hε : 0 < ε) (hx_nonneg : 0 ≤ x) (hy_nonneg : 0 ≤ y)
    (hsig2_nonneg : 0 ≤ sig2)
    (hx_small : x ≤ ε / 432) (hy_small : y ≤ ε / 18)
    (hx_trade : sig2 ≠ 0 → x ≤ ε ^ (2 : ℕ) / (20736 * sig2)) :
    (195 / 2) * x + 8 * y +
        2 / max 1 (6 * sig2 / ε) * (13 * x + y + sig2) ≤ ε := by
  by_cases hlow : sig2 ≤ ε / 48
  · have hbranch : max 1 (6 * sig2 / ε) = 1 := by
      apply max_eq_left
      have hε_nonneg : 0 ≤ ε := le_of_lt hε
      have hsig_bound : 6 * sig2 ≤ ε := by nlinarith
      exact (div_le_one hε).mpr hsig_bound
    rw [hbranch]
    norm_num
    nlinarith
  · have hsig2_pos : 0 < sig2 := by
      by_contra hnot
      have hsig2_le_zero : sig2 ≤ 0 := le_of_not_gt hnot
      have : sig2 ≤ ε / 48 := by nlinarith
      exact hlow this
    have hx_trade' : x ≤ ε ^ (2 : ℕ) / (20736 * sig2) :=
      hx_trade (ne_of_gt hsig2_pos)
    by_cases hmid : sig2 ≤ ε / 6
    · have hbranch : max 1 (6 * sig2 / ε) = 1 := by
        apply max_eq_left
        have hsig_bound : 6 * sig2 ≤ ε := by nlinarith
        exact (div_le_one hε).mpr hsig_bound
      rw [hbranch]
      norm_num
      have hsig_lower : ε / 48 ≤ sig2 := le_of_not_ge hlow
      have hden_pos : 0 < 20736 * sig2 := by positivity
      have hx_scaled :
          (20736 * sig2) * x ≤ ε ^ (2 : ℕ) := by
        have := mul_le_mul_of_nonneg_left hx_trade' (le_of_lt hden_pos)
        field_simp [ne_of_gt hden_pos] at this
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have hmain :
          (247 / 2) * x + 10 * y + 2 * sig2 ≤ ε := by
        nlinarith [hx_scaled, hy_small, hsig_lower, hmid, hε]
      nlinarith
    · have hsig_lower : ε / 6 ≤ sig2 := le_of_not_ge hmid
      have hbranch : max 1 (6 * sig2 / ε) = 6 * sig2 / ε := by
        apply max_eq_right
        have hsig_bound : ε ≤ 6 * sig2 := by nlinarith
        exact (one_le_div hε).mpr hsig_bound
      rw [hbranch]
      have hsig2_ne : sig2 ≠ 0 := ne_of_gt hsig2_pos
      have hden_trade_pos : 0 < 20736 * sig2 := by positivity
      have hx_scaled :
          (20736 * sig2) * x ≤ ε ^ (2 : ℕ) := by
        have := mul_le_mul_of_nonneg_left hx_trade' (le_of_lt hden_trade_pos)
        field_simp [ne_of_gt hden_trade_pos] at this
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have hsig_sq_lower : ε ^ (2 : ℕ) ≤ 36 * sig2 ^ (2 : ℕ) := by
        nlinarith [hε, hsig_lower, hsig2_pos]
      field_simp [ne_of_gt hε, hsig2_ne]
      nlinarith [hx_scaled, hsig_sq_lower, hy_small, hsig_lower, hε]

private theorem rsgf_6_4b_iteration_policy_scalar_bounds
    (S : Setup n Sample) (N : ℕ) (ε Dtilde : ℝ)
    (hε : 0 < ε) (hN : 1 ≤ N) (hDtilde : 0 < Dtilde)
    (hN_policy : RsgfIterationLimitPolicy S N ε Dtilde) :
    let x := ((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ)
    let y := S.L *
      ((4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ)) *
        (Dtilde + Df S ^ (2 : ℕ) / Dtilde))
    let sig2 := S.σ ^ (2 : ℕ)
    0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ sig2 ∧ x ≤ ε / 432 ∧ y ≤ ε / 18 ∧
      (sig2 ≠ 0 → x ≤ ε ^ (2 : ℕ) / (20736 * sig2)) := by
  dsimp
  set A : ℝ := (n : ℝ) + 4
  set d : ℝ := Df S
  set W : ℝ := Dtilde + Df S ^ (2 : ℕ) / Dtilde
  set Nr : ℝ := (N : ℝ)
  have hN_pos : 0 < Nr := by
    dsimp [Nr]
    exact_mod_cast hN
  have hN_nonneg : 0 ≤ Nr := le_of_lt hN_pos
  have hN_ne : Nr ≠ 0 := ne_of_gt hN_pos
  have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have ha_pos : 0 < A := by
    dsimp [A]
    nlinarith
  have ha_nonneg : 0 ≤ A := le_of_lt ha_pos
  have hsqrt_a_pos : 0 < Real.sqrt A :=
    Real.sqrt_pos_of_pos ha_pos
  have hsqrt_N_pos : 0 < Real.sqrt Nr :=
    Real.sqrt_pos_of_pos hN_pos
  have hsqrt_N_ne : Real.sqrt Nr ≠ 0 :=
    ne_of_gt hsqrt_N_pos
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    exact Real.sqrt_nonneg _
  have hL_sq_nonneg : 0 ≤ S.L ^ (2 : ℕ) := sq_nonneg S.L
  have hsig2_nonneg : 0 ≤ S.σ ^ (2 : ℕ) := sq_nonneg S.σ
  have hDtilde_ne : Dtilde ≠ 0 := ne_of_gt hDtilde
  have hW_pos : 0 < W := by
    dsimp [W]
    positivity
  have hW_nonneg : 0 ≤ W := le_of_lt hW_pos
  have hx_nonneg :
      0 ≤ A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ) / Nr := by
    positivity
  have hy_nonneg :
      0 ≤ S.L * ((4 * S.σ * Real.sqrt A / Real.sqrt Nr) * W) := by
    exact mul_nonneg S.L_pos.le
      (mul_nonneg
        (div_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) S.σ_nonneg)
            (Real.sqrt_nonneg A))
          (le_of_lt hsqrt_N_pos))
        hW_nonneg)
  have hfirst_le :
      12 * A * (6 * S.L * d) ^ (2 : ℕ) / ε ≤ Nr := by
    have hraw :
        12 * ((n : ℝ) + 4) * (6 * S.L * Df S) ^ (2 : ℕ) / ε ≤
          (N : ℝ) := by
      rw [hN_policy]
      exact le_max_left _ _
    simpa [A, d, Nr] using hraw
  have hfirst_clear :
      432 * (A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ)) ≤ ε * Nr := by
    have h := hfirst_le
    field_simp [ne_of_gt hε] at h
    ring_nf at h ⊢
    exact h
  have hx_small :
      A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ) / Nr ≤ ε / 432 := by
    field_simp [hN_ne]
    nlinarith
  have hsecond_le :
      (72 * S.L * Real.sqrt A * W * S.σ / ε) ^ (2 : ℕ) ≤ Nr := by
    have hraw :
        (72 * S.L * Real.sqrt ((n : ℝ) + 4) *
            (Dtilde + Df S ^ (2 : ℕ) / Dtilde) * S.σ / ε) ^ (2 : ℕ) ≤
          (N : ℝ) := by
      rw [hN_policy]
      exact le_max_right _ _
    simpa [A, W, Nr] using hraw
  let q : ℝ := 72 * S.L * Real.sqrt A * W * S.σ / ε
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity) S.L_pos.le)
            (Real.sqrt_nonneg A))
          hW_nonneg)
        S.σ_nonneg)
      (le_of_lt hε)
  have hq_sqrt_le : q ≤ Real.sqrt Nr := by
    have hroot := Real.sqrt_le_sqrt hsecond_le
    have hq_sqrt : Real.sqrt (q ^ (2 : ℕ)) = q := by
      rw [Real.sqrt_sq_eq_abs]
      exact abs_of_nonneg hq_nonneg
    simpa [q, hq_sqrt, Real.sq_sqrt hN_nonneg] using hroot
  have hq_clear :
      72 * S.L * Real.sqrt A * W * S.σ ≤ ε * Real.sqrt Nr := by
    have h := mul_le_mul_of_nonneg_left hq_sqrt_le (le_of_lt hε)
    dsimp [q] at h
    field_simp [ne_of_gt hε] at h
    ring_nf at h ⊢
    exact h
  have hy_small :
      S.L * ((4 * S.σ * Real.sqrt A / Real.sqrt Nr) * W) ≤ ε / 18 := by
    field_simp [hsqrt_N_ne]
    nlinarith
  have hsecond_clear :
      5184 * (S.L ^ (2 : ℕ) * A * W ^ (2 : ℕ) *
          S.σ ^ (2 : ℕ)) ≤ ε ^ (2 : ℕ) * Nr := by
    have h := hsecond_le
    field_simp [ne_of_gt hε] at h
    rw [Real.sq_sqrt ha_nonneg] at h
    ring_nf at h ⊢
    exact h
  have hW_ge : 2 * d ≤ W := by
    have hraw :
        2 * Df S ≤ Dtilde + Df S ^ (2 : ℕ) / Dtilde := by
      have hsquare : 0 ≤ (Dtilde - Df S) ^ (2 : ℕ) := sq_nonneg _
      field_simp [hDtilde_ne]
      nlinarith
    simpa [d, W] using hraw
  have hW_sq_ge : 4 * d ^ (2 : ℕ) ≤ W ^ (2 : ℕ) := by
    have hmul := mul_le_mul hW_ge hW_ge (by positivity : 0 ≤ 2 * d) hW_nonneg
    nlinarith
  have hx_trade :
      S.σ ^ (2 : ℕ) ≠ 0 →
        A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ) / Nr ≤
          ε ^ (2 : ℕ) / (20736 * S.σ ^ (2 : ℕ)) := by
    intro hsig_ne
    have hsig_pos : 0 < S.σ ^ (2 : ℕ) :=
      lt_of_le_of_ne hsig2_nonneg (Ne.symm hsig_ne)
    have hden_pos : 0 < 20736 * S.σ ^ (2 : ℕ) := by positivity
    have hcoef_nonneg :
        0 ≤ 5184 * (S.L ^ (2 : ℕ) * A * S.σ ^ (2 : ℕ)) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hW_sq_ge hcoef_nonneg
    have htrade_clear :
        20736 * S.σ ^ (2 : ℕ) * (A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ)) ≤
          ε ^ (2 : ℕ) * Nr := by
      calc
        20736 * S.σ ^ (2 : ℕ) * (A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ))
            = 5184 * (S.L ^ (2 : ℕ) * A * S.σ ^ (2 : ℕ)) *
                (4 * d ^ (2 : ℕ)) := by ring
        _ ≤ 5184 * (S.L ^ (2 : ℕ) * A * S.σ ^ (2 : ℕ)) *
                W ^ (2 : ℕ) := hmul
        _ = 5184 * (S.L ^ (2 : ℕ) * A * W ^ (2 : ℕ) *
                S.σ ^ (2 : ℕ)) := by ring
        _ ≤ ε ^ (2 : ℕ) * Nr := hsecond_clear
    rw [div_le_iff₀ hN_pos]
    calc
      A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ)
          ≤ (ε ^ (2 : ℕ) * Nr) / (20736 * S.σ ^ (2 : ℕ)) := by
            rw [le_div_iff₀ hden_pos]
            simpa [mul_comm, mul_left_comm, mul_assoc] using htrade_clear
      _ = ε ^ (2 : ℕ) / (20736 * S.σ ^ (2 : ℕ)) * Nr := by ring
  simpa [A, d, W, Nr] using
    (show
      0 ≤ A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ) / Nr ∧
      0 ≤ S.L * ((4 * S.σ * Real.sqrt A / Real.sqrt Nr) * W) ∧
      0 ≤ S.σ ^ (2 : ℕ) ∧
      A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ) / Nr ≤ ε / 432 ∧
      S.L * ((4 * S.σ * Real.sqrt A / Real.sqrt Nr) * W) ≤ ε / 18 ∧
      (S.σ ^ (2 : ℕ) ≠ 0 →
        A * S.L ^ (2 : ℕ) * d ^ (2 : ℕ) / Nr ≤
          ε ^ (2 : ℕ) / (20736 * S.σ ^ (2 : ℕ))) from
      ⟨hx_nonneg, hy_nonneg, hsig2_nonneg, hx_small, hy_small, hx_trade⟩)

private theorem rsgf_6_4b_policy_threshold_le_epsilon
    (S : Setup n Sample) (S_count N T : ℕ) (ε Λ Dtilde : ℝ)
    (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hDtilde : 0 < Dtilde)
    (hS_policy : RsgfConfidenceRunPolicy S_count Λ)
    (hN_policy : RsgfIterationLimitPolicy S N ε Dtilde)
    (hT_policy : RsgfPostOptimizationSamplePolicy S T ε Λ) :
    rsgfTheorem64Threshold S N T Dtilde
        (2 * (S_count + 1 : ℝ) / Λ) ≤ ε := by
  have hprefactor :
      24 * ((n : ℝ) + 4) * (2 * (S_count + 1 : ℝ) / Λ) / (T : ℝ) =
        2 / max 1 (6 * S.σ ^ (2 : ℕ) / ε) :=
    rsgf_6_4b_sampling_prefactor_eq_two_div_max S S_count T ε Λ
      hε hΛ0 hS_policy hT_policy
  dsimp [rsgfTheorem64Threshold]
  rw [hprefactor]
  have hbounds :=
    rsgf_6_4b_iteration_policy_scalar_bounds S N ε Dtilde
      hε hN hDtilde hN_policy
  dsimp at hbounds
  rcases hbounds with
    ⟨hx_nonneg, hy_nonneg, hsig2_nonneg, hx_small, hy_small, hx_trade⟩
  have hscalar :
      (195 / 2) *
          (((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) / (N : ℝ)) +
        8 *
          (S.L *
            ((4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ)) *
              (Dtilde + Df S ^ (2 : ℕ) / Dtilde))) +
        2 / max 1 (6 * S.σ ^ (2 : ℕ) / ε) *
          (13 *
              (((n : ℝ) + 4) * S.L ^ (2 : ℕ) * Df S ^ (2 : ℕ) /
                (N : ℝ)) +
            (S.L *
              ((4 * S.σ * Real.sqrt ((n : ℝ) + 4) / Real.sqrt (N : ℝ)) *
                (Dtilde + Df S ^ (2 : ℕ) / Dtilde))) +
            S.σ ^ (2 : ℕ)) ≤ ε :=
    rsgf_6_4b_scalar_threshold_budget hε hx_nonneg hy_nonneg hsig2_nonneg
      hx_small hy_small hx_trade
  dsimp [rsgfBbar] at hscalar ⊢
  convert hscalar using 1 <;> ring_nf

/-- Helper-level Theorem 6.4(b) variant under the formalization-only independent
product law. -/
theorem theorem_6_4b_twoPhase_epsilon_solution_independentProduct
    (S : Setup n Sample) (S_count N T : ℕ) (ε Λ Dtilde : ℝ)
    (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hDtilde : 0 < Dtilde)
    (hS_policy : RsgfConfidenceRunPolicy S_count Λ)
    (hN_policy : RsgfIterationLimitPolicy S N ε Dtilde)
    (hT_policy : RsgfPostOptimizationSamplePolicy S T ε Λ)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    rsgfTwoPhaseEpsilonFailureProbability S S_count N T ε hS Dtilde hN hDtilde
        hsteps hPR ≤ Λ ∧
      (2 * (S_count : ℝ) * ((N : ℝ) + (T : ℝ)) ≤
        rsgfTwoPhaseCallCount S ε Λ Dtilde) := by
  classical
  let lambda : ℝ := 2 * (S_count + 1 : ℝ) / Λ
  have hlambda : 0 < lambda := by
    have hSp1_pos : 0 < (S_count + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos S_count
    dsimp [lambda]
    positivity
  have h64 :
      rsgfTheorem64FailureProbability S S_count N T Dtilde lambda hS hN
          hDtilde hsteps hPR ≤
        (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count :=
    theorem_6_4a_twoPhase_independentProduct S S_count N T Dtilde lambda hS
      hN hT hDtilde hlambda hsteps hPR hsmooth
  have hthreshold :
      rsgfTheorem64Threshold S N T Dtilde lambda ≤ ε := by
    dsimp [lambda]
    exact rsgf_6_4b_policy_threshold_le_epsilon S S_count N T ε Λ Dtilde
      hε hΛ0 hΛ1 hN hT hDtilde hS_policy hN_policy hT_policy
  have hmono :
      rsgfTwoPhaseEpsilonFailureProbability S S_count N T ε hS Dtilde hN
          hDtilde hsteps hPR ≤
        rsgfTheorem64FailureProbability S S_count N T Dtilde lambda hS hN
          hDtilde hsteps hPR :=
    rsgf_epsilon_failure_probability_le_threshold_failure S S_count N T ε
      Dtilde lambda hS hN hDtilde hsteps hPR hthreshold
  have hconf :
      (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count ≤ Λ := by
    dsimp [lambda]
    exact rsgf_6_4b_confidence_rhs_le hΛ0 hS_policy
  constructor
  · exact le_trans hmono (le_trans h64 hconf)
  · rw [rsgfTwoPhase_call_count_formula S ε Λ Dtilde hε hΛ0 hΛ1]
    rw [← hN_policy, ← hT_policy, ← hS_policy]

/-- Helper-level Theorem 6.4(b) variant under the formalization-only two-phase
product law.  It retains the paper's policies (6.1.32), (6.1.82), and
(6.1.83), but is not labeled as the source theorem because the source does not
print the needed product-law interface. -/
theorem theorem_6_4b_twoPhase_epsilon_solution_productLaw
    (S : Setup n Sample) (S_count N T : ℕ) (ε Λ Dtilde : ℝ)
    (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hDtilde : 0 < Dtilde)
    (hS_policy : RsgfConfidenceRunPolicy S_count Λ)
    (hN_policy : RsgfIterationLimitPolicy S N ε Dtilde)
    (hT_policy : RsgfPostOptimizationSamplePolicy S T ε Λ)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hPR : RsgfOutputWeightsAdmissible S N)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    rsgfTwoPhaseEpsilonFailureProbabilityProductLaw S S_count N T ε hS Dtilde hN
        hDtilde hsteps hPR ≤ Λ ∧
      (2 * (S_count : ℝ) * ((N : ℝ) + (T : ℝ)) ≤
        rsgfTwoPhaseCallCount S ε Λ Dtilde) := by
  classical
  let lambda : ℝ := 2 * (S_count + 1 : ℝ) / Λ
  have hlambda : 0 < lambda := by
    have hSp1_pos : 0 < (S_count + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos S_count
    dsimp [lambda]
    positivity
  have h64 :
      rsgfTheorem64FailureProbabilityProductLaw S S_count N T Dtilde lambda hS hN
          hDtilde hsteps hPR ≤
        (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count :=
    theorem_6_4a_twoPhase_productLaw S S_count N T Dtilde lambda hS
      hN hT hDtilde hlambda hsteps hPR hsmooth
  have hthreshold :
      rsgfTheorem64Threshold S N T Dtilde lambda ≤ ε := by
    dsimp [lambda]
    exact rsgf_6_4b_policy_threshold_le_epsilon S S_count N T ε Λ Dtilde
      hε hΛ0 hΛ1 hN hT hDtilde hS_policy hN_policy hT_policy
  have hmono :
      rsgfTwoPhaseEpsilonFailureProbabilityProductLaw S S_count N T ε hS Dtilde hN
          hDtilde hsteps hPR ≤
        rsgfTheorem64FailureProbabilityProductLaw S S_count N T Dtilde lambda hS hN
          hDtilde hsteps hPR :=
    rsgf_epsilon_failure_probability_productLaw_le_threshold_failure
      S S_count N T ε Dtilde lambda hS hN hDtilde hsteps hPR hthreshold
  have hconf :
      (S_count + 1 : ℝ) / lambda + (1 / 2 : ℝ) ^ S_count ≤ Λ := by
    dsimp [lambda]
    exact rsgf_6_4b_confidence_rhs_le hΛ0 hS_policy
  constructor
  · exact le_trans hmono (le_trans h64 hconf)
  · rw [rsgfTwoPhase_call_count_formula S ε Λ Dtilde hε hΛ0 hΛ1]
    rw [← hN_policy, ← hT_policy, ← hS_policy]

/-- Formalization-level Theorem 6.4(b) realization.  It keeps the printed
policies (6.1.32), (6.1.82), and (6.1.83), but still depends on the product-law
realization noted above for part (a). -/
theorem theorem_6_4b_productLawRealization
    (S : Setup n Sample) (S_count N T : ℕ) (ε Λ Dtilde : ℝ)
    (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (hS : 0 < S_count) (hN : 1 ≤ N) (hT : 1 ≤ T)
    (hPR_source : RsgfOutputPMFSourceChoice S N) (hDtilde : 0 < Dtilde)
    (hS_policy : RsgfConfidenceRunPolicy S_count Λ)
    (hN_policy : RsgfIterationLimitPolicy S N ε Dtilde)
    (hT_policy : RsgfPostOptimizationSamplePolicy S T ε Λ)
    (hsteps : RsgfConstantStepsizePolicy S N Dtilde)
    (hsmooth : RsgfSmoothingParameterPolicy S N) :
    rsgfTwoPhaseEpsilonFailureProbabilityProductRealization S S_count N T ε hS Dtilde hN
        hPR_source hDtilde hsteps ≤ Λ ∧
      (2 * (S_count : ℝ) * ((N : ℝ) + (T : ℝ)) ≤
        rsgfTwoPhaseCallCount S ε Λ Dtilde) := by
  classical
  let hPR : RsgfOutputWeightsAdmissible S N :=
    rsgfOutputPMFSourceChoice_admissible S hPR_source
  have hpmf :
      rsgfOutputPMFTheorem63 S N hPR_source =
        rsgfOutputPMF S N hPR := by
    ext R
    rw [rsgfOutputPMFTheorem63_apply, rsgfOutputPMF_apply]
  have hrun :
      rsgfSelectedRunLawTheorem63 S N hPR_source =
        rsgfSelectedRunLawCanonical S N hPR := by
    unfold rsgfSelectedRunLawTheorem63 rsgfSelectedRunLawCanonical
    rw [hpmf]
  have hlaw :
      rsgfTwoPhaseJointLawProductRealization S S_count N T Dtilde hN
          hPR_source hDtilde hsteps =
        rsgfTwoPhaseJointLaw S S_count N T hPR := by
    unfold rsgfTwoPhaseJointLawProductRealization
      rsgfOptimizationPhaseLawProductRealization
      rsgfTwoPhaseJointLaw rsgfOptimizationPhaseLaw
    rw [hrun]
  have hprob :
      rsgfTwoPhaseEpsilonFailureProbabilityProductRealization S S_count N T ε
          hS Dtilde hN hPR_source hDtilde hsteps =
        rsgfTwoPhaseEpsilonFailureProbabilityProductLaw S S_count N T ε
          hS Dtilde hN hDtilde hsteps hPR := by
    unfold rsgfTwoPhaseEpsilonFailureProbabilityProductRealization
      rsgfTwoPhaseEpsilonFailureProbabilityProductLaw
    rw [hlaw]
  rw [hprob]
  exact theorem_6_4b_twoPhase_epsilon_solution_productLaw S S_count N T ε Λ
    Dtilde hε hΛ0 hΛ1 hS hN hT hDtilde hS_policy hN_policy
    hT_policy hsteps hPR hsmooth

end

end Algorithms.Unverified.StochasticZerothOrder
