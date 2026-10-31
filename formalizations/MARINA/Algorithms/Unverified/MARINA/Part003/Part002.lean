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
import Algorithms.Unverified.MARINA.Part002
import Algorithms.Unverified.MARINA.Part003.Part001

/-!
# MARINA family: source-facing object model

This file models Algorithms 1--4 of Gorbunov--Burlachenko--Li--Richtárik.
The estimator and iterate processes below are generated definitions, rather
than witness processes constrained by theorem hypotheses.
-/

open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace MARINA

theorem onlinePLDensityCanonicalStepsize_condition
    {L ℒ p ω : ℝ} {mu : PositivePLParameter} {n b0 : Count}
    (hp : RefreshProbabilityAdmissible p) :
    OnlineVRPLStepsizeCondition
      (onlinePLDensityCanonicalStepsize L ℒ p ω mu n b0)
      L ℒ p ω mu n b0 := by
  let D : ℝ := L + Real.sqrt ((2 * (1 - p)) / (p * n.1) *
    (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1))
  let M : ℝ := max (2 * (mu : ℝ) / p) (max 1 D)
  have hp0 : 0 < p := hp.1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 D).trans (le_max_right _ _))
  have hDM : D ≤ M := (le_max_right 1 D).trans (le_max_right _ _)
  have hMuM : 2 * (mu : ℝ) / p ≤ M := le_max_left _ _
  unfold OnlineVRPLStepsizeCondition FiniteSumVRPLStepsizeCondition
  constructor
  · change (1 / M) * D ≤ 1
    calc
      (1 / M) * D = D / M := by ring
      _ ≤ 1 := (div_le_one hM).2 hDM
  · change 2 * (1 / M) * (mu : ℝ) ≤ p
    rw [show 2 * (1 / M) * (mu : ℝ) =
      (2 * (mu : ℝ)) / M by ring]
    rw [div_le_iff₀ hM]
    have := (div_le_iff₀ hp0).1 hMuM
    nlinarith

/-- A typed batch-schedule witness showing why `AccuracyTheta` cannot itself
discharge Eq. (41)'s pointwise half-budget.  The schedule is asymptotically
inverse-square, but at accuracy one its variance floor is one. -/
theorem accuracyTheta_not_pointwise_variance_floor :
    ∃ b : Accuracy → Count,
      AccuracyTheta (fun ε => ((b ε).1 : ℝ))
        (fun ε => 1 / (ε : ℝ) ^ 2) ∧
      ∃ ε : Accuracy, 1 / ((b ε).1 : ℝ) > (ε : ℝ) ^ 2 / 2 := by
  let b : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (1 / (ε : ℝ) ^ 2)), by omega⟩
  refine ⟨b, ?_, ⟨⟨1, by norm_num⟩, ?_⟩⟩
  · unfold AccuracyTheta
    constructor
    · have h := (positive_inverse_square_ceiling_schedule
        1 2 1 (by norm_num) (by norm_num) (by norm_num)).2
      convert h using 1 <;> funext ε <;> simp [b] <;> ring
    · rw [Asymptotics.isBigO_iff]
      refine ⟨1, Filter.Eventually.of_forall ?_⟩
      intro ε
      have hs : 0 ≤ 1 / (ε : ℝ) ^ 2 := by positivity
      have hceil := le_positive_ceil_max_one (1 / (ε : ℝ) ^ 2)
      rw [Real.norm_eq_abs, abs_of_nonneg hs]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ ((b ε).1 : ℝ))]
      simpa [b] using hceil
  · norm_num [b]

/-- The inverse-linear analogue needed for Theorem D.4.  An asymptotic
`Theta(1 / ε)` statement permits an isolated undersized refresh batch, so it
cannot by itself discharge Eq. (49)'s pointwise half-budget. -/
theorem accuracyTheta_not_pointwise_PL_variance_floor :
    ∃ b : Accuracy → Count,
      AccuracyTheta (fun ε => ((b ε).1 : ℝ))
        (fun ε => 1 / (ε : ℝ)) ∧
      ∃ ε : Accuracy, 1 / ((b ε).1 : ℝ) > (ε : ℝ) / 2 := by
  let b : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (1 / (ε : ℝ))), by omega⟩
  refine ⟨b, ?_, ⟨⟨1, by norm_num⟩, ?_⟩⟩
  · unfold AccuracyTheta
    constructor
    · rw [Asymptotics.isBigO_iff]
      refine ⟨3, ?_⟩
      have hEventually : ∀ᶠ ε : Accuracy in accuracyToZero,
          1 ≤ 1 / (ε : ℝ) := by
        rw [accuracyToZero]
        change {ε : Accuracy | 1 ≤ 1 / (ε : ℝ)} ∈
          Filter.comap (fun ε : Accuracy => ((ε : ℝ)⁻¹))
            (Filter.atTop : Filter ℝ)
        rw [Filter.mem_comap]
        refine ⟨Set.Ici 1, Filter.eventually_atTop.2 ⟨1, fun a ha => ha⟩, ?_⟩
        intro ε hε
        simpa [one_div] using hε
      filter_upwards [hEventually] with ε hscale
      let s : ℝ := 1 / (ε : ℝ)
      have hs : 1 ≤ s := by simpa [s] using hscale
      have hceil := natCast_max_one_ceil_le_add_two s (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((b ε).1 : ℝ))]
      rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le zero_lt_one hs)]
      change ((max 1 (Nat.ceil s) : ℕ) : ℝ) ≤ 3 * s
      nlinarith
    · rw [Asymptotics.isBigO_iff]
      refine ⟨1, Filter.Eventually.of_forall ?_⟩
      intro ε
      let s : ℝ := 1 / (ε : ℝ)
      have hs : 0 ≤ s := by
        dsimp [s]
        exact (one_div_nonneg.mpr ε.property.le)
      have hceil : s ≤ ((max 1 (Nat.ceil s) : ℕ) : ℝ) :=
        le_positive_ceil_max_one s
      rw [Real.norm_eq_abs, abs_of_nonneg hs]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((b ε).1 : ℝ))]
      simpa [b, s] using hceil
  · norm_num [b]

/-- The common integer inflation used to turn Remark D.2's asymptotic
heterogeneous batch family into a pointwise-safe family.  Scaling every
worker's batch by the same factor preserves the relative worker allocation
while making the displayed aggregate variance consume at most half of the
requested squared-accuracy budget. -/
noncomputable def heterogeneousOnlineBatchInflationFactor {n : Count}
    (sigma : Worker n → ℝ) (base : Accuracy → Worker n → Count)
    (eps : Accuracy) : ℕ :=
  max 1 (Nat.ceil
    (2 * heterogeneousOnlineVarianceTerm sigma (base eps) / (eps : ℝ) ^ 2))

/-- Executable workerwise batch choice for Remark D.2. -/
noncomputable def heterogeneousOnlineBatchScheduleFromBase {n : Count}
    (sigma : Worker n → ℝ) (base : Accuracy → Worker n → Count)
    (eps : Accuracy) (i : Worker n) : Count :=
  ⟨heterogeneousOnlineBatchInflationFactor sigma base eps * (base eps i).1,
    Nat.mul_pos
      (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _))
      (base eps i).2⟩

theorem heterogeneousOnlineBatchScheduleFromBase_admissible {n : Count}
    (sigma : Worker n → ℝ) (base : Accuracy → Worker n → Count)
    (b0 : Worker n → Count) (hbase : ∀ eps i, (b0 i).1 < (base eps i).1)
    (eps : Accuracy) (i : Worker n) :
    (b0 i).1 < (heterogeneousOnlineBatchScheduleFromBase sigma base eps i).1 := by
  have hfactor : 1 ≤ heterogeneousOnlineBatchInflationFactor sigma base eps :=
    Nat.le_max_left 1 _
  dsimp [heterogeneousOnlineBatchScheduleFromBase]
  nlinarith [hbase eps i, (base eps i).2]

theorem heterogeneousOnlineBatchScheduleFromBase_variance_eq {n : Count}
    (sigma : Worker n → ℝ) (base : Accuracy → Worker n → Count)
    (eps : Accuracy) :
    heterogeneousOnlineVarianceTerm sigma
        (heterogeneousOnlineBatchScheduleFromBase sigma base eps) =
      heterogeneousOnlineVarianceTerm sigma (base eps) /
        heterogeneousOnlineBatchInflationFactor sigma base eps := by
  have hfactor :
      (heterogeneousOnlineBatchInflationFactor sigma base eps : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)))
  unfold heterogeneousOnlineVarianceTerm
  have hpoint (i : Worker n) :
      (sigma i) ^ 2 /
          (heterogeneousOnlineBatchScheduleFromBase sigma base eps i).1 =
        ((sigma i) ^ 2 / (base eps i).1) /
          heterogeneousOnlineBatchInflationFactor sigma base eps := by
    simp only [heterogeneousOnlineBatchScheduleFromBase, Nat.cast_mul]
    field_simp
  rw [show (fun i : Worker n =>
      (sigma i) ^ 2 /
        (heterogeneousOnlineBatchScheduleFromBase sigma base eps i).1) =
      (fun i : Worker n => ((sigma i) ^ 2 / (base eps i).1) /
        heterogeneousOnlineBatchInflationFactor sigma base eps) by
      funext i
      exact hpoint i]
  unfold average SOptLib.finiteUniformAverage
  simp only [smul_eq_mul]
  rw [← Finset.sum_div]
  ring

theorem heterogeneousOnlineBatchScheduleFromBase_variance_floor {n : Count}
    (sigma : Worker n → ℝ) (base : Accuracy → Worker n → Count)
    (eps : Accuracy) :
    heterogeneousOnlineVarianceTerm sigma
        (heterogeneousOnlineBatchScheduleFromBase sigma base eps) ≤
      (eps : ℝ) ^ 2 / 2 := by
  let V := heterogeneousOnlineVarianceTerm sigma (base eps)
  let q := heterogeneousOnlineBatchInflationFactor sigma base eps
  have hV : 0 ≤ V := by
    dsimp [V, heterogeneousOnlineVarianceTerm, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _))
  have hceil : 2 * V / (eps : ℝ) ^ 2 ≤ (q : ℝ) := by
    simpa [q, V, heterogeneousOnlineBatchInflationFactor] using
      le_positive_ceil_max_one (2 * V / (eps : ℝ) ^ 2)
  rw [heterogeneousOnlineBatchScheduleFromBase_variance_eq]
  change V / (q : ℝ) ≤ (eps : ℝ) ^ 2 / 2
  rw [div_le_iff₀ hq]
  have heps : 0 < (eps : ℝ) ^ 2 := sq_pos_of_pos eps.property
  have htwice : 2 * V ≤ (q : ℝ) * (eps : ℝ) ^ 2 := by
    calc
      2 * V = (2 * V / (eps : ℝ) ^ 2) * (eps : ℝ) ^ 2 := by
        field_simp [ne_of_gt eps.property]
      _ ≤ (q : ℝ) * (eps : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hceil heps.le
  nlinarith

theorem heterogeneousOnlineBatchScheduleFromBase_accuracyTheta {n : Count}
    (sigma : Worker n → ℝ) (base : Accuracy → Worker n → Count)
    (hbase : AccuracyTheta
      (fun eps => heterogeneousOnlineVarianceTerm sigma (base eps))
      (fun eps => (eps : ℝ) ^ 2)) :
    AccuracyTheta
      (fun eps => heterogeneousOnlineVarianceTerm sigma
        (heterogeneousOnlineBatchScheduleFromBase sigma base eps))
      (fun eps => (eps : ℝ) ^ 2) := by
  unfold AccuracyTheta at hbase ⊢
  have hVnonneg (eps : Accuracy) :
      0 ≤ heterogeneousOnlineVarianceTerm sigma (base eps) := by
    unfold heterogeneousOnlineVarianceTerm average SOptLib.finiteUniformAverage
    positivity
  have hNewNonneg (eps : Accuracy) :
      0 ≤ heterogeneousOnlineVarianceTerm sigma
        (heterogeneousOnlineBatchScheduleFromBase sigma base eps) := by
    rw [heterogeneousOnlineBatchScheduleFromBase_variance_eq]
    exact div_nonneg (hVnonneg eps) (Nat.cast_nonneg _)
  constructor
  · have hBaseO := hbase.1
    rw [Asymptotics.isBigO_iff'] at hBaseO ⊢
    rcases hBaseO with ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, ?_⟩
    filter_upwards [hC] with eps heps
    let V := heterogeneousOnlineVarianceTerm sigma (base eps)
    let q := heterogeneousOnlineBatchInflationFactor sigma base eps
    have hq : 1 ≤ (q : ℝ) := by
      exact_mod_cast (Nat.le_max_left 1 _)
    have hnewle : V / (q : ℝ) ≤ V := by
      exact div_le_self (by simpa [V] using hVnonneg eps) hq
    rw [heterogeneousOnlineBatchScheduleFromBase_variance_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hVnonneg eps) (by positivity))]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (eps : ℝ))]
    exact hnewle.trans (by
      simpa [V, Real.norm_eq_abs, abs_of_nonneg (hVnonneg eps),
        abs_of_nonneg (sq_nonneg (eps : ℝ))] using heps)
  · have hScaleO := hbase.2
    have hBaseO := hbase.1
    rw [Asymptotics.isBigO_iff'] at hScaleO hBaseO ⊢
    rcases hScaleO with ⟨C, hCpos, hC⟩
    rcases hBaseO with ⟨D, hDpos, hD⟩
    refine ⟨C * (2 * D + 2), mul_pos hCpos (by positivity), ?_⟩
    filter_upwards [hC, hD] with eps heps hbound
    let V := heterogeneousOnlineVarianceTerm sigma (base eps)
    let q := heterogeneousOnlineBatchInflationFactor sigma base eps
    have hV : 0 ≤ V := by simpa [V] using hVnonneg eps
    have hs : 0 < (eps : ℝ) ^ 2 := sq_pos_of_pos eps.property
    have hqpos : 0 < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _))
    have hVbound : V ≤ D * (eps : ℝ) ^ 2 := by
      simpa [V, Real.norm_eq_abs, abs_of_nonneg hV,
        abs_of_nonneg hs.le] using hbound
    have harg : 2 * V / (eps : ℝ) ^ 2 ≤ 2 * D := by
      rw [div_le_iff₀ hs]
      nlinarith
    have hceil := natCast_max_one_ceil_le_add_two
      (2 * V / (eps : ℝ) ^ 2) (by positivity)
    have hqbound : (q : ℝ) ≤ 2 * D + 2 := by
      dsimp [q, heterogeneousOnlineBatchInflationFactor]
      exact hceil.trans (by linarith)
    have hsource : (eps : ℝ) ^ 2 ≤ C * V := by
      simpa [V, Real.norm_eq_abs, abs_of_nonneg hs.le,
        abs_of_nonneg hV] using heps
    have hVeq : V = (V / (q : ℝ)) * q := by
      field_simp
    rw [heterogeneousOnlineBatchScheduleFromBase_variance_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg hs.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hV hqpos.le)]
    rw [hVeq] at hsource
    have hscaled :
        C * ((V / (q : ℝ)) * q) ≤
          (C * (2 * D + 2)) * (V / (q : ℝ)) := by
      have hCD : 0 ≤ C := hCpos.le
      have hnew : 0 ≤ V / (q : ℝ) := div_nonneg hV hqpos.le
      nlinarith
    exact hsource.trans hscaled

/-- Nonfallback nonconvex accuracy endpoint for a generated uniform output. -/
def NonconvexAccuracy {d n : Count} (K : Count) {Ω : Type*} [MeasurableSpace Ω]
    (P : LocalProblem d n) (run : ℕ → Ω → State d) (pathLaw : Measure Ω)
    (ε : PositiveStepsize) : Prop :=
  Integrable (fun z => ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw pathLaw K) ∧
    (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
      ∂uniformOutputExperimentLaw pathLaw K) ≤ (ε : ℝ) ^ 2

/-- Nonfallback PŁ accuracy endpoint for the generated last iterate. -/
def PLAccuracy {d n : Count} (K : Count) {Ω : Type*} [MeasurableSpace Ω]
    (P : LocalProblem d n) (run : ℕ → Ω → State d) (pathLaw : Measure Ω)
    (xStar : Point d) (ε : PositiveStepsize) : Prop :=
  Integrable (fun path =>
      globalObjective P (run K.1 path).x - globalObjective P xStar) pathLaw ∧
    (∫ path, globalObjective P (run K.1 path).x - globalObjective P xStar
      ∂pathLaw) ≤ (ε : ℝ)

/-- Common family-level package for iteration plus one cost endpoint. -/
def TwoEndpointComplexity (K : Accuracy → Count)
    (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
  (cost costScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    AccuracyBigO cost costScale

/-- Common family-level package for iteration, oracle, and communication
endpoints. -/
def ThreeEndpointComplexity (K : Accuracy → Count)
    (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
  (oracle oracleScale communication communicationScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    AccuracyBigO oracle oracleScale ∧
    AccuracyBigO communication communicationScale

/-- Remark D.1/D.2 stepsize denominator after retaining the worker-dependent
`n⁻¹∑ᵢ ℒᵢ²/b⁰ᵢ` term. -/
def HeterogeneousVRStepsizeCondition
    (γ L smoothnessTerm p ω : ℝ) (n : Count) : Prop :=
  γ * (L + Real.sqrt ((1 - p) / (p * n.1) *
    (ω * L ^ 2 + (1 + ω) * smoothnessTerm))) ≤ 1

/-- The heterogeneous Remark D.1/D.2 stepsize absorbs the displacement
coefficient in the same Lyapunov calculation as Eq. (40). -/
theorem heterogeneous_vr_stepsize_absorbs_displacement
    {n : Count} {γ L S p ω : ℝ}
    (hγ : 0 < γ) (hp : RefreshProbabilityAdmissible p)
    (hω : 0 ≤ ω) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hStep : HeterogeneousVRStepsizeCondition γ L S p ω n) :
    0 ≤ 1 / (2 * γ) - L / 2 -
      γ / (2 * p) * ((1 - p) / n.1 * (ω * L ^ 2 + (1 + ω) * S)) := by
  let q : ℝ := ((1 - p) / (p * n.1)) *
    (ω * L ^ 2 + (1 + ω) * S)
  have hp_pos : 0 < p := hp.1
  have hn_pos : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg
      (div_nonneg (sub_nonneg.mpr hp.2) (mul_nonneg hp_pos.le hn_pos.le))
      (add_nonneg (mul_nonneg hω (sq_nonneg L))
        (mul_nonneg (by linarith) hS))
  have hs_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hstep' : γ * (L + Real.sqrt q) ≤ 1 := by
    simpa [HeterogeneousVRStepsizeCondition, q, mul_assoc] using hStep
  have hγs_le_one : γ * Real.sqrt q ≤ 1 := by nlinarith
  have hγs_nonneg : 0 ≤ γ * Real.sqrt q := mul_nonneg hγ.le hs_nonneg
  have hγs_budget : 0 ≤ (γ * Real.sqrt q) * (1 - γ * Real.sqrt q) :=
    mul_nonneg hγs_nonneg (sub_nonneg.mpr hγs_le_one)
  have hγq : γ ^ 2 * q = (γ * Real.sqrt q) ^ 2 := by
    calc
      γ ^ 2 * q = γ ^ 2 * (Real.sqrt q) ^ 2 := by rw [hs_sq]
      _ = (γ * Real.sqrt q) ^ 2 := by ring
  have hcore : 0 ≤ 1 - γ * L - γ ^ 2 * q := by
    rw [hγq]
    nlinarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hn_ne : (n.1 : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  have hq_eq :
      γ / (2 * p) * ((1 - p) / n.1 * (ω * L ^ 2 + (1 + ω) * S)) =
        γ * q / 2 := by
    dsimp [q]
    field_simp [hp_ne, hn_ne]
  rw [hq_eq]
  have hscaled := mul_nonneg (show 0 ≤ (2 * γ)⁻¹ by positivity) hcore
  convert hscaled using 1 <;> field_simp [hγ_ne] <;> ring

/-- Workerwise finite-sum oracle count in Remark D.1. -/
noncomputable def heterogeneousFiniteSumOracleCallCount {n : Count}
    (m K : Count) (b0 : Worker n → Count) (p : ℝ) (i : Worker n) : ℝ :=
  m.1 + K.1 * (p * m.1 + 2 * (1 - p) * (b0 i).1)

/-- Workerwise online oracle count in Remark D.2. -/
noncomputable def heterogeneousOnlineOracleCallCount {n : Count}
    (b b0 : Worker n → Count) (K : Count) (p : ℝ) (i : Worker n) : ℝ :=
  (b i).1 + K.1 * (p * (b i).1 + 2 * (1 - p) * (b0 i).1)

/-- The repeated maximum in Corollaries D.1--D.2. -/
noncomputable def finiteSumDensityBatchRatio
    (d m b0 : Count) (ζ : ℝ) : ℝ :=
  max (d.1 / ζ - 1) (m.1 / b0.1)

/-- The repeated maximum in Corollaries D.3--D.4. -/
noncomputable def onlineDensityBatchRatio
    (d n b0 : Count) (ζ σsq accuracyScale : ℝ) : ℝ :=
  max (d.1 / ζ - 1) (σsq / (n.1 * b0.1 * accuracyScale))

/-- The bracketed iteration scale in the four VR-MARINA corollaries. -/
noncomputable def vrIterationBracket (L ℒ ω ratio : ℝ) (n b0 : Count) : ℝ :=
  L * (1 + Real.sqrt (ω * ratio / n.1)) +
    ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1))

/-- Corollary D.1's finite-sum stochastic-oracle scale. -/
noncomputable def finiteSumNonconvexOracleScale
    (Δ L ℒ ω ζ ε : ℝ) (d n m b0 : Count) : ℝ :=
  let odds := d.1 / ζ - 1
  m.1 + Δ / ε ^ 2 *
    (L * b0.1 + L * Real.sqrt (ω * max (odds * b0.1 ^ 2) (m.1 * b0.1) / n.1) +
      ℒ * Real.sqrt ((1 + ω) * max (odds * b0.1) m.1 / n.1))

/-- Corollary D.2's finite-sum PŁ stochastic-oracle scale. -/
noncomputable def finiteSumPLOracleScale
    (L ℒ ω μ p ζ logGap : ℝ) (d n m b0 : Count) : ℝ :=
  let odds := d.1 / ζ - 1
  m.1 + max (b0.1 / p)
    (L / μ * (b0.1 + Real.sqrt (ω * max (odds * b0.1 ^ 2) (m.1 * b0.1) / n.1)) +
      ℒ / μ * Real.sqrt ((1 + ω) * max (odds * b0.1) m.1 / n.1)) * logGap

/-- Corollary D.3's online stochastic-oracle scale. -/
noncomputable def onlineNonconvexOracleScale
    (Δ L ℒ ω ζ σsq ε : ℝ) (d n b0 : Count) : ℝ :=
  let M := max ((d.1 / ζ - 1) * b0.1) (σsq / (n.1 * ε ^ 2))
  σsq / (n.1 * ε ^ 2) + Δ * L * b0.1 / ε ^ 2 +
    Δ * L / ε ^ 2 * Real.sqrt (ω * b0.1 / n.1 * M) +
    Δ * ℒ / ε ^ 2 * Real.sqrt ((1 + ω) / n.1 * M)

/-- Corollary D.4's online PŁ stochastic-oracle scale. -/
noncomputable def onlinePLOracleScale
    (L ℒ ω μ p ζ σsq ε logGap : ℝ) (d n b0 : Count) : ℝ :=
  let M := max ((d.1 / ζ - 1) * b0.1) (σsq / (n.1 * μ * ε))
  σsq / (n.1 * μ * ε) + max (b0.1 / p)
    (L / μ * (b0.1 + Real.sqrt (ω * b0.1 / n.1 * M)) +
      ℒ / μ * Real.sqrt ((1 + ω) / n.1 * M)) * logGap

/-- Definition 1.1's expected density is nonnegative for every unbiased
quantizer.  Integrability supplies the nonfallback expectation semantics,
while the finite support count bounds the range used by `sSup`. -/
theorem expectedDensity_nonneg_of_unbiased
    {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Quantizer d Ξ} {ω : ℝ} (hQ : IsUnbiasedQuantizer Q ω) :
    0 ≤ expectedDensity Q := by
  letI : IsProbabilityMeasure Q.law := Q.law_isProbability
  rw [ExpectedDensity_Definition]
  have hSemantics : ExpectedDensitySemantics Q :=
    expectedDensitySemantics_of_unbiased hQ
  have hBdd : BddAbove
      (Set.range fun v : Point d =>
        ∫ ξ, quantizerNonzeroCount Q v ξ ∂Q.law) := by
    refine ⟨(d.1 : ℝ), ?_⟩
    rintro y ⟨v, rfl⟩
    have hPointwise : quantizerNonzeroCount Q v ≤ fun _ => (d.1 : ℝ) := by
      intro ξ
      change quantizerNonzeroCount Q v ξ ≤ (d.1 : ℝ)
      have hcard :
          (Finset.univ.filter fun j : Fin d.1 => Q.apply v ξ j ≠ 0).card ≤
            d.1 := by
        simpa using
          (Finset.card_filter_le Finset.univ
            (fun j : Fin d.1 => Q.apply v ξ j ≠ 0))
      unfold quantizerNonzeroCount
      exact_mod_cast hcard
    have hIntegral := MeasureTheory.integral_mono
      (hSemantics v) (integrable_const (d.1 : ℝ)) hPointwise
    simpa using hIntegral
  let v0 : Point d := 0
  have hMember :
      (∫ ξ, quantizerNonzeroCount Q v0 ξ ∂Q.law) ∈
        Set.range (fun v : Point d =>
          ∫ ξ, quantizerNonzeroCount Q v ξ ∂Q.law) := ⟨v0, rfl⟩
  have hValueNonneg :
      0 ≤ ∫ ξ, quantizerNonzeroCount Q v0 ξ ∂Q.law := by
    apply MeasureTheory.integral_nonneg
    intro ξ
    unfold quantizerNonzeroCount
    positivity
  exact hValueNonneg.trans (le_csSup hBdd hMember)

/-- In the already-optimal branch of Corollary C.2 the paper's logarithmic
round formula is outside its positive-gap domain.  The source algorithm may
stop immediately; the existing endpoint API, however, uses `Count` because a
last iterate is evaluated at a natural index.  This lemma verifies the
faithful nonempty-window totalization: one round is enough, the resulting
schedule is uniformly bounded, and both accuracy and communication endpoints
hold without interpreting an arbitrary schedule as `O(0)`. -/
theorem c2_zero_gap_nonempty_window_totalization
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : MARINAPLDensityStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      ω (expectedDensity A.quantizer) μ d n)
    (hSchedule : A.refreshProbability =
      marinaDensityRefreshSchedule (expectedDensity A.quantizer) d)
    (hGap : globalObjective A.problem x0 -
      globalObjective A.problem xStar = 0) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective A.problem x0 - globalObjective A.problem xStar
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => PLAccuracy (K ε) A.problem (marinaProcess A x0)
          (basicPathLaw A) xStar ε)
        (fun ε => max (d.1 / ζ)
          (rootMeanSquare Llocal / μ *
            (1 + Real.sqrt (ω / n.1 * (d.1 / ζ - 1)))) *
          Real.log (Δ / (ε : ℝ)))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + max (d.1 : ℝ)
          (rootMeanSquare Llocal / μ *
            (ζ + Real.sqrt (ω * ζ / n.1 * (d.1 - ζ)))) *
          Real.log (Δ / (ε : ℝ))) := by
  dsimp
  let K₁ : Count := ⟨1, by norm_num⟩
  have hInitialZero : globalObjective A.problem x0 =
      globalObjective A.problem xStar := sub_eq_zero.mp hGap
  refine ⟨fun _ => K₁, ?_⟩
  unfold TwoEndpointComplexity
  refine ⟨?_, ?_, ?_⟩
  · intro ε
    unfold PLAccuracy
    have hGeneralStep : MARINAPLStepsizeCondition A.stepSize
        (rootMeanSquare Llocal) A.refreshProbability ω μ n :=
      density_stepsize_bridge_MARINA_PL hSchedule hStep
    have hC2 := Theorem_C2_MARINA_PL (K := K₁) A x0 xStar Llocal ω fStar μ
      hLower hSmooth hPL hQuantizer hGeneralStep
    refine ⟨hC2.1, ?_⟩
    have hNonpos :
        (∫ path,
          (globalObjective A.problem (marinaProcess A x0 K₁.1 path).x -
            globalObjective A.problem xStar) ∂basicPathLaw A) ≤ 0 := by
      rw [hInitialZero] at hC2
      simpa using hC2.2
    exact hNonpos.trans (le_of_lt ε.property)
  · refine Or.inl ⟨?_, ?_⟩
    · intro ε
      rw [hInitialZero]
      simp
    · unfold AccuracyBigO
      simpa [K₁] using
        (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ)) accuracyToZero)
  · unfold AccuracyBigO
    have hd : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
    rw [show (fun ε : Accuracy => (d.1 : ℝ) + max (d.1 : ℝ)
          (rootMeanSquare Llocal / μ *
            (expectedDensity A.quantizer + Real.sqrt
              (ω * expectedDensity A.quantizer / n.1 *
                (d.1 - expectedDensity A.quantizer)))) *
          Real.log ((globalObjective A.problem x0 -
            globalObjective A.problem xStar) / (ε : ℝ))) =
        (fun _ : Accuracy => (d.1 : ℝ)) by
          funext ε
          rw [hInitialZero]
          simp]
    simpa [allWorkerCommunicationCount, K₁] using
      (Asymptotics.isBigO_const_const
        ((d.1 : ℝ) +
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))
        hd accuracyToZero)

/-! ## Uniform paper complexity endpoints -/

/-- A differentiable objective that is globally lower bounded and has zero
Lipschitz gradient constant is stationary everywhere. -/
theorem zero_rms_smooth_lower_bounded_global_gradient_eq_zero
    {d n : Count} (P : LocalProblem d n) (Llocal : Worker n → ℝ) (fStar : ℝ)
    (hLower : HasUniformLowerBound P fStar)
    (hSmooth : IsLocallySmooth P Llocal)
    (hLzero : rootMeanSquare Llocal = 0) :
    ∀ x, globalGradient P x = 0 := by
  have hGlobal := GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  rw [hLzero] at hGlobal
  intro x
  by_contra hg
  have hnorm : 0 < ‖globalGradient P x‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hgap : 0 ≤ globalObjective P x - fStar := sub_nonneg.mpr (hLower x)
  let t : ℝ := (globalObjective P x - fStar) / ‖globalGradient P x‖ ^ 2 + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hdes := DescentLemma_B1 (globalObjective P) 0 t x
    (globalGradient P x) hGlobal
  have hdisp : x - t • globalGradient P x - x =
      -t • globalGradient P x := by module
  rw [hdisp, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht] at hdes
  have hlowerStep : fStar ≤
      globalObjective P (x - t • globalGradient P x) := hLower _
  have htNorm : t * ‖globalGradient P x‖ ^ 2 =
      globalObjective P x - fStar + ‖globalGradient P x‖ ^ 2 := by
    dsimp [t]
    field_simp [ne_of_gt hnorm]
    <;> ring
  simp only [globalGradient, sub_self, norm_zero, zero_pow, mul_zero,
    add_zero, zero_div, sub_zero] at hdes
  have hdes' : globalObjective P (x - t • globalGradient P x) ≤
      globalObjective P x - t * ‖globalGradient P x‖ ^ 2 := by
    calc
      globalObjective P (x - t • globalGradient P x) ≤ _ := hdes
      _ = globalObjective P x - t * ‖globalGradient P x‖ ^ 2 := by
        unfold globalGradient
        field_simp [ne_of_gt ht]
        <;> ring
  rw [htNorm] at hdes'
  nlinarith

/-- An asymptotic schedule bound transports through an affine cost whenever
the actual per-round payload is bounded by a fixed multiple of the displayed
payload.  Eventual nonnegativity prevents cancellation against the positive
initialization in the displayed affine scale. -/
theorem accuracyBigO_affine_cost_of_schedule
    {K scale : Accuracy → ℝ}
    {init actualPayload targetPayload payloadFactor : ℝ}
    (hK : AccuracyBigO K scale)
    (hinit : 0 < init)
    (hActualPayload : 0 ≤ actualPayload)
    (hTargetPayload : 0 < targetPayload)
    (hPayloadFactor : 0 < payloadFactor)
    (hPayload : actualPayload ≤ payloadFactor * targetPayload)
    (hScaleNonneg : ∀ᶠ ε : Accuracy in accuracyToZero, 0 ≤ scale ε) :
    AccuracyBigO
      (fun ε => init + K ε * actualPayload)
      (fun ε => init + scale ε * targetPayload) := by
  unfold AccuracyBigO at hK ⊢
  have hRound :
      (fun ε => K ε * actualPayload) =O[accuracyToZero]
        (fun ε => scale ε * targetPayload) := by
    rcases hK.exists_pos with ⟨C, hC, hKC⟩
    rw [Asymptotics.isBigO_iff']
    refine ⟨C * payloadFactor, mul_pos hC hPayloadFactor, ?_⟩
    filter_upwards [hKC.bound] with ε hKε
    rw [norm_mul, norm_mul]
    have hActualNorm : ‖actualPayload‖ = actualPayload := by
      rw [Real.norm_eq_abs, abs_of_nonneg hActualPayload]
    have hTargetNorm : ‖targetPayload‖ = targetPayload := by
      rw [Real.norm_eq_abs, abs_of_pos hTargetPayload]
    rw [hActualNorm, hTargetNorm]
    calc
      ‖K ε‖ * actualPayload ≤
          (C * ‖scale ε‖) * actualPayload :=
        mul_le_mul_of_nonneg_right hKε hActualPayload
      _ ≤ (C * ‖scale ε‖) * (payloadFactor * targetPayload) :=
        mul_le_mul_of_nonneg_left hPayload
          (mul_nonneg hC.le (norm_nonneg _))
      _ = (C * payloadFactor) * (‖scale ε‖ * targetPayload) := by ring
  have hTargetPartToTotal :
      (fun ε => scale ε * targetPayload) =O[accuracyToZero]
        (fun ε => init + scale ε * targetPayload) := by
    rw [Asymptotics.isBigO_iff']
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [hScaleNonneg] with ε hscale
    have hpart : 0 ≤ scale ε * targetPayload :=
      mul_nonneg hscale hTargetPayload.le
    rw [Real.norm_eq_abs, abs_of_nonneg hpart, Real.norm_eq_abs,
      abs_of_pos (add_pos_of_pos_of_nonneg hinit hpart), one_mul]
    linarith
  have hInitToTotal :
      (fun _ : Accuracy => init) =O[accuracyToZero]
        (fun ε => init + scale ε * targetPayload) := by
    rw [Asymptotics.isBigO_iff']
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [hScaleNonneg] with ε hscale
    have hpart : 0 ≤ scale ε * targetPayload :=
      mul_nonneg hscale hTargetPayload.le
    rw [Real.norm_eq_abs, abs_of_pos hinit, Real.norm_eq_abs,
      abs_of_pos (add_pos_of_pos_of_nonneg hinit hpart), one_mul]
    linarith
  have hRoundToTotal := hRound.trans hTargetPartToTotal
  simpa using hInitToTotal.add hRoundToTotal

/-- Two asymptotic schedules remain controlled after multiplying the second
one by an accuracy-dependent nonnegative payload that is uniformly bounded by
the displayed positive payload. -/
theorem accuracyBigO_add_mul_varying_payload
    {a b s t payload : Accuracy → ℝ} {targetPayload factor : ℝ}
    (ha : AccuracyBigO a s) (hb : AccuracyBigO b t)
    (ha0 : ∀ ε, 0 ≤ a ε) (hb0 : ∀ ε, 0 ≤ b ε)
    (hs0 : ∀ᶠ ε in accuracyToZero, 0 ≤ s ε)
    (ht0 : ∀ᶠ ε in accuracyToZero, 0 ≤ t ε)
    (hpayload0 : ∀ ε, 0 ≤ payload ε)
    (hTarget : 0 < targetPayload) (hFactor : 0 < factor)
    (hPayload : ∀ ε, payload ε ≤ factor * targetPayload) :
    AccuracyBigO
      (fun ε => a ε + b ε * payload ε)
      (fun ε => s ε + t ε * targetPayload) := by
  unfold AccuracyBigO at ha hb ⊢
  rcases ha.exists_pos with ⟨C₁, hC₁, haC⟩
  rcases hb.exists_pos with ⟨C₂, hC₂, hbC⟩
  rw [Asymptotics.isBigO_iff']
  let C : ℝ := max C₁ (C₂ * factor)
  have hC : 0 < C := hC₁.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  filter_upwards [haC.bound, hbC.bound, hs0, ht0] with ε haε hbε hsε htε
  have ha' : a ε ≤ C₁ * s ε := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (ha0 ε),
      abs_of_nonneg hsε] using haε
  have hb' : b ε ≤ C₂ * t ε := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hb0 ε),
      abs_of_nonneg htε] using hbε
  have hround : b ε * payload ε ≤
      (C₂ * factor) * (t ε * targetPayload) := by
    calc
      b ε * payload ε ≤ (C₂ * t ε) * payload ε :=
        mul_le_mul_of_nonneg_right hb' (hpayload0 ε)
      _ ≤ (C₂ * t ε) * (factor * targetPayload) :=
        mul_le_mul_of_nonneg_left (hPayload ε) (mul_nonneg hC₂.le htε)
      _ = (C₂ * factor) * (t ε * targetPayload) := by ring
  have hactual : 0 ≤ a ε + b ε * payload ε :=
    add_nonneg (ha0 ε) (mul_nonneg (hb0 ε) (hpayload0 ε))
  have htarget : 0 ≤ s ε + t ε * targetPayload :=
    add_nonneg hsε (mul_nonneg htε hTarget.le)
  rw [Real.norm_eq_abs, abs_of_nonneg hactual,
    Real.norm_eq_abs, abs_of_nonneg htarget]
  calc
    a ε + b ε * payload ε ≤
        C₁ * s ε + (C₂ * factor) * (t ε * targetPayload) :=
      add_le_add ha' hround
    _ ≤ C * s ε + C * (t ε * targetPayload) := by
      gcongr <;> simp [C]
    _ = C * (s ε + t ε * targetPayload) := by ring

/-- Eq. (43)'s online oracle count is stable under independent asymptotic
bounds for the refresh batch and the iteration schedule. -/
theorem accuracyBigO_online_oracle_cost
    {batch iterations varianceScale iterationScale : Accuracy → ℝ}
    {p b0 : ℝ}
    (hBatch : AccuracyBigO batch varianceScale)
    (hIterations : AccuracyBigO iterations iterationScale)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hbatch : ∀ ε, 0 ≤ batch ε)
    (hiterations : ∀ ε, 0 ≤ iterations ε)
    (hvariance : ∀ ε, 0 ≤ varianceScale ε)
    (hscale : ∀ᶠ ε in accuracyToZero, 0 ≤ iterationScale ε)
    (hb0 : 0 ≤ b0) :
    AccuracyBigO
      (fun ε => batch ε + iterations ε *
        (p * batch ε + 2 * (1 - p) * b0))
      (fun ε => varianceScale ε + iterationScale ε *
        (p * varianceScale ε + (1 - p) * b0)) := by
  unfold AccuracyBigO at hBatch hIterations ⊢
  rcases hBatch.exists_pos with ⟨C₁, hC₁, hBatchC⟩
  rcases hIterations.exists_pos with ⟨C₂, hC₂, hIterationsC⟩
  rw [Asymptotics.isBigO_iff']
  let M : ℝ := max C₁ 2
  let C : ℝ := max C₁ (C₂ * M)
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hCpos : 0 < C := hC₁.trans_le (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hBatchC.bound, hIterationsC.bound, hscale] with ε hB hK hSnonneg
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hBnonneg := hbatch ε
  have hKnonneg := hiterations ε
  have hVnonneg := hvariance ε
  have hB' : batch ε ≤ C₁ * varianceScale ε := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hBnonneg,
      abs_of_nonneg hVnonneg] using hB
  have hK' : iterations ε ≤ C₂ * iterationScale ε := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
      abs_of_nonneg hSnonneg] using hK
  have hPayloadNonneg :
      0 ≤ p * batch ε + 2 * (1 - p) * b0 := by positivity
  have hTargetPayloadNonneg :
      0 ≤ p * varianceScale ε + (1 - p) * b0 := by positivity
  have hPayload :
      p * batch ε + 2 * (1 - p) * b0 ≤
        M * (p * varianceScale ε + (1 - p) * b0) := by
    have hC₁M : C₁ ≤ M := le_max_left _ _
    have h2M : (2 : ℝ) ≤ M := le_max_right _ _
    have hpart₁ : p * batch ε ≤ M * (p * varianceScale ε) := by
      calc
        p * batch ε ≤ p * (C₁ * varianceScale ε) := by gcongr
        _ = C₁ * (p * varianceScale ε) := by ring
        _ ≤ M * (p * varianceScale ε) := by gcongr
    have hpart₂ : 2 * (1 - p) * b0 ≤ M * ((1 - p) * b0) := by
      calc
        2 * (1 - p) * b0 = 2 * ((1 - p) * b0) := by ring
        _ ≤ M * ((1 - p) * b0) := by gcongr
    calc
      p * batch ε + 2 * (1 - p) * b0 ≤
          M * (p * varianceScale ε) + M * ((1 - p) * b0) :=
        add_le_add hpart₁ hpart₂
      _ = M * (p * varianceScale ε + (1 - p) * b0) := by ring
  have hRound : iterations ε *
      (p * batch ε + 2 * (1 - p) * b0) ≤
        (C₂ * M) * (iterationScale ε *
          (p * varianceScale ε + (1 - p) * b0)) := by
    calc
      iterations ε * (p * batch ε + 2 * (1 - p) * b0) ≤
          (C₂ * iterationScale ε) *
            (p * batch ε + 2 * (1 - p) * b0) := by gcongr
      _ ≤ (C₂ * iterationScale ε) *
          (M * (p * varianceScale ε + (1 - p) * b0)) := by gcongr
      _ = (C₂ * M) * (iterationScale ε *
          (p * varianceScale ε + (1 - p) * b0)) := by ring
  have hActualNonneg : 0 ≤ batch ε + iterations ε *
      (p * batch ε + 2 * (1 - p) * b0) := by positivity
  have hTargetNonneg : 0 ≤ varianceScale ε + iterationScale ε *
      (p * varianceScale ε + (1 - p) * b0) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg,
    Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
  calc
    batch ε + iterations ε *
        (p * batch ε + 2 * (1 - p) * b0) ≤
      C₁ * varianceScale ε + (C₂ * M) *
        (iterationScale ε *
          (p * varianceScale ε + (1 - p) * b0)) := add_le_add hB' hRound
    _ ≤ C * varianceScale ε + C *
        (iterationScale ε *
          (p * varianceScale ε + (1 - p) * b0)) := by
          gcongr <;> simp [C]
    _ = C * (varianceScale ε + iterationScale ε *
        (p * varianceScale ε + (1 - p) * b0)) := by ring

/-- A positive refresh batch makes the fixed one-round online oracle cost
asymptotically no larger than the refresh-batch scale. -/
theorem accuracyBigO_online_oracle_cost_one_round
    {batch varianceScale : Accuracy → ℝ} {p b0 : ℝ}
    (hBatch : AccuracyBigO batch varianceScale)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hbatchOne : ∀ ε, 1 ≤ batch ε)
    (hvariance : ∀ ε, 0 ≤ varianceScale ε)
    (hb0 : 0 ≤ b0) :
    AccuracyBigO
      (fun ε => batch ε + p * batch ε + 2 * (1 - p) * b0)
      varianceScale := by
  unfold AccuracyBigO at hBatch ⊢
  rcases hBatch.exists_pos with ⟨C, hC, hBatchC⟩
  rw [Asymptotics.isBigO_iff']
  have hfactorPos : 0 < 2 + p + 2 * (1 - p) * b0 := by
    have htail : 0 ≤ 2 * (1 - p) * b0 :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1)) hb0
    linarith
  refine ⟨C * (2 + p + 2 * (1 - p) * b0), mul_pos hC hfactorPos, ?_⟩
  filter_upwards [hBatchC.bound] with ε hB
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hBpos : 0 < batch ε := lt_of_lt_of_le zero_lt_one (hbatchOne ε)
  have hVnonneg := hvariance ε
  have hB' : batch ε ≤ C * varianceScale ε := by
    simpa [Real.norm_eq_abs, abs_of_pos hBpos,
      abs_of_nonneg hVnonneg] using hB
  have hOne : 1 ≤ C * varianceScale ε := (hbatchOne ε).trans hB'
  have hActualNonneg :
      0 ≤ batch ε + p * batch ε + 2 * (1 - p) * b0 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg,
    Real.norm_eq_abs, abs_of_nonneg hVnonneg]
  calc
    batch ε + p * batch ε + 2 * (1 - p) * b0 ≤
        (1 + p) * (C * varianceScale ε) +
          2 * (1 - p) * b0 * (C * varianceScale ε) := by
            have hsum : batch ε + p * batch ε ≤
                (1 + p) * (C * varianceScale ε) := by nlinarith
            have hconst : 2 * (1 - p) * b0 ≤
                2 * (1 - p) * b0 * (C * varianceScale ε) := by
              have hcoef : 0 ≤ 2 * (1 - p) * b0 := by positivity
              calc
                2 * (1 - p) * b0 = (2 * (1 - p) * b0) * 1 := by ring
                _ ≤ (2 * (1 - p) * b0) * (C * varianceScale ε) :=
                  mul_le_mul_of_nonneg_left hOne hcoef
            exact add_le_add hsum hconst
    _ = C * (1 + p + 2 * (1 - p) * b0) * varianceScale ε := by ring
    _ ≤ C * (2 + p + 2 * (1 - p) * b0) * varianceScale ε := by
          have hCV : 0 ≤ C * varianceScale ε := mul_nonneg hC.le hVnonneg
          nlinarith

/-- A uniformly bounded one-round payload is absorbed by any positive batch
schedule already controlled by the displayed scale.  This is the
accuracy-indexed counterpart of the fixed-`p` helper above. -/
theorem accuracyBigO_batch_add_bounded_payload
    {batch scale payload : Accuracy → ℝ} {C : ℝ}
    (hBatch : AccuracyBigO batch scale)
    (hBatchOne : ∀ ε, 1 ≤ batch ε)
    (hPayloadNonneg : ∀ ε, 0 ≤ payload ε)
    (hPayloadBound : ∀ ε, payload ε ≤ C)
    (hC : 0 ≤ C) :
    AccuracyBigO (fun ε => batch ε + payload ε) scale := by
  unfold AccuracyBigO at hBatch ⊢
  rw [Asymptotics.isBigO_iff'] at hBatch ⊢
  rcases hBatch with ⟨D, hD, hEventually⟩
  refine ⟨D * (1 + C), mul_pos hD (by linarith), ?_⟩
  filter_upwards [hEventually] with ε hBound
  have hBatchNonneg : 0 ≤ batch ε := le_trans (by norm_num) (hBatchOne ε)
  have hActualNonneg : 0 ≤ batch ε + payload ε :=
    add_nonneg hBatchNonneg (hPayloadNonneg ε)
  have hPayloadBatch : payload ε ≤ C * batch ε := by
    calc
      payload ε ≤ C := hPayloadBound ε
      _ = C * 1 := by ring
      _ ≤ C * batch ε := mul_le_mul_of_nonneg_left (hBatchOne ε) hC
  rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg]
  calc
    batch ε + payload ε ≤ (1 + C) * batch ε := by linarith
    _ = (1 + C) * ‖batch ε‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hBatchNonneg]
    _ ≤ (1 + C) * (D * ‖scale ε‖) :=
      mul_le_mul_of_nonneg_left hBound (by linarith)
    _ = D * (1 + C) * ‖scale ε‖ := by ring

/-- `book/MARINA/MARINA.json#/main_theorem`, Theorem C.1 / Eqs. (18)-(19). -/
theorem Theorem_C1_MARINA_complexity_endpoints
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (ω fStar : ℝ) (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : MARINAStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω n) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective A.problem x0 - fStar
    let bracket := rootMeanSquare Llocal *
      (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
        (A.refreshProbability * n.1)))
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) A.problem (marinaProcess A x0)
          (basicPathLaw A) ε)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 - fStar :=
    sub_nonneg.mpr (hLower x0)
  dsimp
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective A.problem x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal *
    (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
      (A.refreshProbability * n.1)))
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    positivity
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq : globalObjective A.problem x0 - fStar = 0 := hGapZero.symm
    have hΔzero : Δ = 0 := by simpa [Δ] using hGapEq
    refine ⟨fun _ => K₁, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold NonconvexAccuracy
      have hC1 := Theorem_C1_MARINA_nonconvex (K := K₁) A x0
        Llocal ω fStar hLower hSmooth hQuantizer hStep
      refine ⟨hC1.1, hC1.2.trans ?_⟩
      rw [hGapEq]
      simp
      positivity
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        change Δ / (ε : ℝ) ^ 2 * bracket = 0
        rw [hΔzero]
        ring
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt d.2)
      rw [show (fun ε : Accuracy => (d.1 : ℝ) +
          (globalObjective A.problem x0 - fStar) / (ε : ℝ) ^ 2 *
            (rootMeanSquare Llocal *
              (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
                (A.refreshProbability * n.1)))) *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer)) =
          (fun _ : Accuracy => (d.1 : ℝ)) by
        funext ε
        rw [hGapEq]
        simp]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) + (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))
          hdne accuracyToZero)
  · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hBracketEq : bracket = 0 := hBracketZero.symm
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hfactor : 0 < 1 + Real.sqrt
            ((1 - A.refreshProbability) * ω /
              (A.refreshProbability * n.1)) := by
          positivity
        dsimp [bracket] at hBracketEq
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        A.problem Llocal fStar hLower hSmooth hLzero
      refine ⟨fun _ => K₁, ?_⟩
      unfold TwoEndpointComplexity
      refine ⟨?_, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hC1 := Theorem_C1_MARINA_nonconvex (K := K₁) A x0
          Llocal ω fStar hLower hSmooth hQuantizer hStep
        refine ⟨hC1.1, ?_⟩
        have heq : (fun z =>
            ‖globalGradient A.problem
              (uniformOutput (K := K₁) (marinaProcess A x0) z)‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change Δ / (ε : ℝ) ^ 2 * bracket = 0
          rw [hBracketEq]
          ring
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
              accuracyToZero)
      · unfold AccuracyBigO
        have hdne : (d.1 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt d.2)
        rw [show (fun ε : Accuracy => (d.1 : ℝ) +
            (globalObjective A.problem x0 - fStar) / (ε : ℝ) ^ 2 *
              (rootMeanSquare Llocal *
                (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
                  (A.refreshProbability * n.1)))) *
              (A.refreshProbability * d.1 +
                (1 - A.refreshProbability) * expectedDensity A.quantizer)) =
            (fun _ : Accuracy => (d.1 : ℝ)) by
          funext ε
          change (d.1 : ℝ) + Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ) = d.1
          rw [hBracketEq]
          ring]
        simpa [allWorkerCommunicationCount, K₁] using
          (Asymptotics.isBigO_const_const
            ((d.1 : ℝ) + (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer))
            hdne accuracyToZero)
    · let K : Accuracy → Count := fun ε =>
        ⟨max 1 (Nat.ceil (2 * Δ /
          ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
      have hΔpos : 0 < Δ := by simpa [Δ] using hGapPos
      have hScalar := positive_inverse_square_ceiling_schedule
        Δ (A.stepSize : ℝ) bracket hΔpos A.stepSize.property hBracketPos
      have hKBound : ∀ ε : Accuracy,
          2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) ≤
            (ε : ℝ) ^ 2 := by
        intro ε
        simpa [K] using hScalar.1 ε
      have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
          (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) := by
        simpa [K] using hScalar.2
      have hScaleNonneg :
          ∀ᶠ ε : Accuracy in accuracyToZero,
            0 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by
        filter_upwards [] with ε
        positivity
      refine ⟨K, ?_⟩
      unfold TwoEndpointComplexity
      refine ⟨?_, Or.inr hKBigO, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hC1 := Theorem_C1_MARINA_nonconvex (K := K ε) A x0
          Llocal ω fStar hLower hSmooth hQuantizer hStep
        refine ⟨hC1.1, hC1.2.trans ?_⟩
        simpa [Δ] using hKBound ε
      · let commPayload : ℝ := A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ
        have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
        have hCommPayloadPos : 0 < commPayload := by
          dsimp [commPayload]
          exact add_pos_of_pos_of_nonneg
            (mul_pos hp hdpos)
            (mul_nonneg (sub_nonneg.mpr hp1) hζ)
        have hComm := accuracyBigO_affine_cost_of_schedule
          (K := fun ε => ((K ε).1 : ℝ))
          (scale := fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
          (init := (d.1 : ℝ))
          (actualPayload := commPayload)
          (targetPayload := commPayload)
          (payloadFactor := 1)
          hKBigO hdpos hCommPayloadPos.le hCommPayloadPos
            zero_lt_one (by simp) hScaleNonneg
        change AccuracyBigO
          (fun ε => (d.1 : ℝ) + ((K ε).1 : ℝ) * commPayload)
          (fun ε => (d.1 : ℝ) +
            (Δ / (ε : ℝ) ^ 2 * bracket) * commPayload)
        exact hComm

/-- `book/MARINA/MARINA.json#/key_lemmas/11`: Corollary C.1 as a
uniform family over positive accuracy tending to zero. -/
theorem Corollary_C1_MARINA_density_choice
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (ω fStar : ℝ)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : MARINADensityStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      ω (expectedDensity A.quantizer) d n)
    (hSchedule : A.refreshProbability =
      marinaDensityRefreshSchedule (expectedDensity A.quantizer) d) :
    let ζ := expectedDensity A.quantizer
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) A.problem (marinaProcess A x0)
          (basicPathLaw A) ε)
        (fun ε => (globalObjective A.problem x0 - fStar) *
          rootMeanSquare Llocal / (ε : ℝ) ^ 2 *
          (1 + Real.sqrt (ω / n.1 * (d.1 / ζ - 1))))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + (globalObjective A.problem x0 - fStar) *
          rootMeanSquare Llocal / (ε : ℝ) ^ 2 *
          (ζ + Real.sqrt (ω * ζ / n.1 * (d.1 - ζ)))) := by
  dsimp
  have hGeneralStep : MARINAStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) A.refreshProbability ω n :=
    density_stepsize_bridge_MARINA hSchedule hStep
  let ζ : ℝ := expectedDensity A.quantizer
  have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hpEq : A.refreshProbability = ζ / (d.1 : ℝ) := by
    simpa [ζ, marinaDensityRefreshSchedule] using hSchedule
  have hζ : 0 < ζ := by
    have hp := A.refresh_admissible.1
    rw [hpEq] at hp
    rcases div_pos_iff.mp hp with hp | hp
    · exact hp.1
    · exfalso
      linarith
  have hζd : ζ ≤ (d.1 : ℝ) := by
    have hp := A.refresh_admissible.2
    rw [hpEq] at hp
    simpa using (div_le_iff₀ hd).mp hp
  have hOddsNonneg : 0 ≤ (d.1 : ℝ) / ζ - 1 :=
    sub_nonneg.mpr ((one_le_div hζ).2 hζd)
  have hIterRadNonneg :
      0 ≤ ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1) :=
    mul_nonneg (div_nonneg hQuantizer.1.le hn.le) hOddsNonneg
  have hCommRadNonneg :
      0 ≤ ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ) :=
    mul_nonneg
      (div_nonneg (mul_nonneg hQuantizer.1.le hζ.le) hn.le)
      (sub_nonneg.mpr hζd)
  have hRad :
      (1 - ζ / (d.1 : ℝ)) * ω /
          (ζ / (d.1 : ℝ) * (n.1 : ℝ)) =
        ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1) := by
    field_simp [ne_of_gt hζ, ne_of_gt hd, ne_of_gt hn]
    <;> ring
  have hSqrtDensity :
      ζ * Real.sqrt
          (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1)) =
        Real.sqrt
          (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ)) := by
    have hsq :
        (ζ * Real.sqrt
            (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1))) ^ 2 =
          (Real.sqrt
            (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hIterRadNonneg,
        Real.sq_sqrt hCommRadNonneg]
      field_simp [ne_of_gt hζ, ne_of_gt hn]
      <;> ring
    have hleft : 0 ≤ ζ * Real.sqrt
        (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1)) := by positivity
    have hright : 0 ≤ Real.sqrt
        (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ)) :=
      Real.sqrt_nonneg _
    nlinarith
  have hPayloadLe :
      ζ / (d.1 : ℝ) * (d.1 : ℝ) +
          (1 - ζ / (d.1 : ℝ)) * ζ ≤ 2 * ζ := by
    have hform :
        ζ / (d.1 : ℝ) * (d.1 : ℝ) +
            (1 - ζ / (d.1 : ℝ)) * ζ =
          2 * ζ - ζ ^ 2 / (d.1 : ℝ) := by
      field_simp [ne_of_gt hd]
      <;> ring
    rw [hform]
    have hsquareDiv : 0 ≤ ζ ^ 2 / (d.1 : ℝ) := by positivity
    linarith
  rcases (Theorem_C1_MARINA_complexity_endpoints A x0 Llocal ω fStar
      hLower hSmooth hQuantizer hGeneralStep) with
    ⟨K, hAccuracy, hIterations, hCommunication⟩
  refine ⟨K, hAccuracy, ?_, ?_⟩
  · convert hIterations using 1
    funext ε
    rw [hpEq, hRad]
    ring
  · unfold AccuracyBigO at hCommunication ⊢
    refine hCommunication.trans ?_
    rw [Asymptotics.isBigO_iff']
    refine ⟨2, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro ε
    let base : ℝ :=
      (globalObjective A.problem x0 - fStar) / (ε : ℝ) ^ 2 *
        (rootMeanSquare Llocal *
          (1 + Real.sqrt
            (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1))))
    let sourcePayload : ℝ :=
      ζ / (d.1 : ℝ) * (d.1 : ℝ) +
        (1 - ζ / (d.1 : ℝ)) * ζ
    let targetPayload : ℝ :=
      ζ + Real.sqrt
        (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ))
    have hGap : 0 ≤ globalObjective A.problem x0 - fStar :=
      sub_nonneg.mpr (hLower x0)
    have hBase : 0 ≤ base := by
      dsimp [base]
      exact mul_nonneg
        (div_nonneg hGap (sq_nonneg (ε : ℝ)))
        (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hSourcePayload : 0 ≤ sourcePayload := by
      dsimp [sourcePayload]
      exact add_nonneg
        (mul_nonneg (div_nonneg hζ.le hd.le) hd.le)
        (mul_nonneg
          (sub_nonneg.mpr ((div_le_one hd).2 hζd)) hζ.le)
    have hTargetPayload : 0 < targetPayload := by
      dsimp [targetPayload]
      positivity
    have hPayloadBound : sourcePayload ≤ 2 * targetPayload := by
      dsimp [sourcePayload, targetPayload]
      calc
        ζ / (d.1 : ℝ) * (d.1 : ℝ) +
            (1 - ζ / (d.1 : ℝ)) * ζ ≤ 2 * ζ := hPayloadLe
        _ ≤ 2 * (ζ + Real.sqrt
            (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ))) := by
          nlinarith [Real.sqrt_nonneg
            (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ))]
    have hTargetTail :
        (globalObjective A.problem x0 - fStar) *
              rootMeanSquare Llocal / (ε : ℝ) ^ 2 *
              targetPayload =
            base * ζ := by
      dsimp [targetPayload, base]
      rw [← hSqrtDensity]
      ring
    rw [hpEq, hRad]
    change ‖(d.1 : ℝ) + base * sourcePayload‖ ≤
      2 * ‖(d.1 : ℝ) +
        (globalObjective A.problem x0 - fStar) *
          rootMeanSquare Llocal / (ε : ℝ) ^ 2 * targetPayload‖
    rw [hTargetTail, Real.norm_eq_abs,
      abs_of_nonneg
        (add_nonneg hd.le (mul_nonneg hBase hSourcePayload)),
      Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hd.le (mul_nonneg hBase hζ.le))]
    have htail := mul_le_mul_of_nonneg_left hPayloadBound hBase
    nlinarith

/-- `book/MARINA/MARINA.json#/key_lemmas/13`: Corollary C.2 as an
accuracy-indexed Big-O family. -/
theorem Corollary_C2_MARINA_PL_density_choice
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : MARINAPLDensityStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      ω (expectedDensity A.quantizer) μ d n)
    (hSchedule : A.refreshProbability =
      marinaDensityRefreshSchedule (expectedDensity A.quantizer) d) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective A.problem x0 - globalObjective A.problem xStar
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => PLAccuracy (K ε) A.problem (marinaProcess A x0)
          (basicPathLaw A) xStar ε)
        (fun ε => max (d.1 / ζ)
          (rootMeanSquare Llocal / μ *
            (1 + Real.sqrt (ω / n.1 * (d.1 / ζ - 1)))) *
          Real.log (Δ / (ε : ℝ)))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + max (d.1 : ℝ)
          (rootMeanSquare Llocal / μ *
            (ζ + Real.sqrt (ω * ζ / n.1 * (d.1 - ζ)))) *
          Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 -
      globalObjective A.problem xStar := sub_nonneg.mpr (hPL.1 x0)
  rcases hGapNonneg.eq_or_lt with hGap | hGap
  · exact c2_zero_gap_nonempty_window_totalization A x0 xStar Llocal ω fStar μ
      hLower hSmooth hPL hQuantizer hStep hSchedule hGap.symm
  · dsimp
    let ζ : ℝ := expectedDensity A.quantizer
    let Δ : ℝ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    let Siter : ℝ := max (d.1 / ζ)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt (ω / n.1 * (d.1 / ζ - 1))))
    let Scomm : ℝ := max (d.1 : ℝ)
      (rootMeanSquare Llocal / μ *
        (ζ + Real.sqrt (ω * ζ / n.1 * (d.1 - ζ))))
    have hGeneralStep : MARINAPLStepsizeCondition A.stepSize
        (rootMeanSquare Llocal) A.refreshProbability ω μ n :=
      density_stepsize_bridge_MARINA_PL hSchedule hStep
    have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
    have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
    have hpEq : A.refreshProbability = ζ / (d.1 : ℝ) := by
      simpa [ζ, marinaDensityRefreshSchedule] using hSchedule
    have hζ : 0 < ζ := by
      have hp := A.refresh_admissible.1
      rw [hpEq] at hp
      have hm := (div_pos_iff.mp hp)
      rcases hm with hm | hm
      · exact hm.1
      · exfalso
        linarith
    have hζd : ζ ≤ (d.1 : ℝ) := by
      have hp := A.refresh_admissible.2
      rw [hpEq] at hp
      simpa using (div_le_iff₀ hd).mp hp
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos A.stepSize.property μ.property
    have hc1 : c ≤ 1 := by
      have hcP := hGeneralStep.2
      have hp1 := A.refresh_admissible.2
      dsimp [c]
      nlinarith

    have hSiter : 0 < Siter := by
      dsimp [Siter]
      exact (div_pos hd hζ).trans_le (le_max_left _ _)
    have hScomm : 0 < Scomm := by
      dsimp [Scomm]
      exact hd.trans_le (le_max_left _ _)
    let K : Accuracy → Count := fun ε =>
      ⟨max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)), by omega⟩
    have hScalar := positive_geometric_ceiling_schedule
      Δ c Siter hGap hc hc1 hSiter
    have hContract : ∀ ε : Accuracy,
        (1 - c) ^ (K ε).1 * Δ ≤ (ε : ℝ) := by
      intro ε
      simpa [K] using hScalar.1 ε
    have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => Siter * Real.log (Δ / (ε : ℝ))) := by
      simpa [K] using hScalar.2
    refine ⟨K, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hC2 := Theorem_C2_MARINA_PL (K := K ε) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hGeneralStep
      refine ⟨hC2.1, hC2.2.trans ?_⟩
      simpa [c, Δ] using hContract ε
    · refine Or.inr ?_
      simpa [Siter, Δ] using hKBigO
    · let payload : ℝ := A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ
      have hp0 : 0 ≤ A.refreshProbability := A.refresh_admissible.1.le
      have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp0 hd.le)
          (mul_nonneg (sub_nonneg.mpr hp1) hζ.le)
      have hOddsNonneg : 0 ≤ (d.1 : ℝ) / ζ - 1 := by
        exact sub_nonneg.mpr ((one_le_div hζ).2 hζd)
      have hSqrtIterNonneg :
          0 ≤ ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1) := by
        exact mul_nonneg (div_nonneg hQuantizer.1.le hn.le) hOddsNonneg
      have hSqrtCommNonneg :
          0 ≤ ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ) := by
        exact mul_nonneg
          (div_nonneg (mul_nonneg hQuantizer.1.le hζ.le) hn.le)
          (sub_nonneg.mpr hζd)
      have hSqrtDensity :
          ζ * Real.sqrt (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1)) =
            Real.sqrt (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ)) := by
        have hsq :
            (ζ * Real.sqrt
                (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1))) ^ 2 =
              (Real.sqrt
                (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hSqrtIterNonneg,
            Real.sq_sqrt hSqrtCommNonneg]
          field_simp [ne_of_gt hζ, ne_of_gt hn]
        have hleft : 0 ≤ ζ * Real.sqrt
            (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1)) := by positivity
        have hright : 0 ≤ Real.sqrt
            (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ)) := Real.sqrt_nonneg _
        nlinarith
      have hPayloadLe : payload ≤ 2 * ζ := by
        have hform : payload = 2 * ζ - ζ ^ 2 / (d.1 : ℝ) := by
          dsimp [payload]
          rw [hpEq]
          field_simp [ne_of_gt hd]
          ring
        rw [hform]
        have hsquareDiv : 0 ≤ ζ ^ 2 / (d.1 : ℝ) := by positivity
        linarith
      have hSiterZeta : Siter * ζ = Scomm := by
        dsimp [Siter, Scomm]
        rw [max_mul_of_nonneg _ _ hζ.le]
        congr 1
        · field_simp [ne_of_gt hζ]
        · calc
            (rootMeanSquare Llocal / (μ : ℝ) *
                (1 + Real.sqrt
                  (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1)))) * ζ =
              rootMeanSquare Llocal / (μ : ℝ) *
                (ζ + ζ * Real.sqrt
                  (ω / (n.1 : ℝ) * ((d.1 : ℝ) / ζ - 1))) := by ring
            _ = rootMeanSquare Llocal / (μ : ℝ) *
                (ζ + Real.sqrt
                  (ω * ζ / (n.1 : ℝ) * ((d.1 : ℝ) - ζ))) := by
              rw [hSqrtDensity]
      have hPayloadBound : Siter * payload ≤ 2 * Scomm := by
        calc
          Siter * payload ≤ Siter * (2 * ζ) :=
            mul_le_mul_of_nonneg_left hPayloadLe hSiter.le
          _ = 2 * (Siter * ζ) := by ring
          _ = 2 * Scomm := by rw [hSiterZeta]
      unfold AccuracyBigO at hKBigO ⊢
      have hRoundO : Asymptotics.IsBigO accuracyToZero
          (fun ε : Accuracy => ((K ε).1 : ℝ) * payload)
          (fun ε => (d.1 : ℝ) + Scomm * Real.log (Δ / (ε : ℝ))) := by
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨2 * C, by positivity, ?_⟩
        filter_upwards [hKC.bound,
          eventually_one_le_log_gap_div_accuracy hGap]
          with ε hKbound hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have hKn : ((K ε).1 : ℝ) ≤
            C * (Siter * Real.log (Δ / (ε : ℝ))) := by
          have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
          rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
            Real.norm_eq_abs, abs_of_pos (mul_pos hSiter hlogpos)] at hKbound
          exact hKbound
        have hKpayload : ((K ε).1 : ℝ) * payload ≤
            (C * (Siter * Real.log (Δ / (ε : ℝ)))) * payload :=
          mul_le_mul_of_nonneg_right hKn hpayload
        have hscaled := mul_le_mul_of_nonneg_left hPayloadBound hC.le
        have hscaledLog := mul_le_mul_of_nonneg_right hscaled hlogpos.le
        have hround : ((K ε).1 : ℝ) * payload ≤
            2 * C * Scomm * Real.log (Δ / (ε : ℝ)) := by
          calc
            ((K ε).1 : ℝ) * payload ≤
                (C * (Siter * Real.log (Δ / (ε : ℝ)))) * payload := hKpayload
            _ = (C * (Siter * payload)) * Real.log (Δ / (ε : ℝ)) := by ring
            _ ≤ (C * (2 * Scomm)) * Real.log (Δ / (ε : ℝ)) := hscaledLog
            _ = 2 * C * Scomm * Real.log (Δ / (ε : ℝ)) := by ring
        have htargetPos : 0 < (d.1 : ℝ) +
            Scomm * Real.log (Δ / (ε : ℝ)) := by positivity
        have hroundNonneg : 0 ≤ ((K ε).1 : ℝ) * payload := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hroundNonneg,
          Real.norm_eq_abs, abs_of_pos htargetPos]
        calc
          ((K ε).1 : ℝ) * payload ≤
              2 * C * Scomm * Real.log (Δ / (ε : ℝ)) := hround
          _ ≤ (2 * C) *
              ((d.1 : ℝ) + Scomm * Real.log (Δ / (ε : ℝ))) := by
            have : 0 ≤ (2 * C) * (d.1 : ℝ) := by positivity
            nlinarith
      have hInitO : Asymptotics.IsBigO accuracyToZero
          (fun _ : Accuracy => (d.1 : ℝ))
          (fun ε => (d.1 : ℝ) + Scomm * Real.log (Δ / (ε : ℝ))) := by
        rw [Asymptotics.isBigO_iff']
        refine ⟨1, zero_lt_one, ?_⟩
        filter_upwards [eventually_one_le_log_gap_div_accuracy hGap] with ε hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have htargetPos : 0 < (d.1 : ℝ) +
            Scomm * Real.log (Δ / (ε : ℝ)) := by positivity
        rw [Real.norm_eq_abs, abs_of_pos hd,
          Real.norm_eq_abs, abs_of_pos htargetPos, one_mul]
        have htail : 0 ≤ Scomm * Real.log (Δ / (ε : ℝ)) :=
          (mul_pos hScomm hlogpos).le
        linarith
      have hTotalO := hInitO.add hRoundO
      simpa [allWorkerCommunicationCount, payload, ζ, Scomm, Δ] using hTotalO

/-- `book/MARINA/MARINA.json#/key_lemmas/24`, Theorem E.1 / Eqs. (56)-(57). -/
theorem Theorem_E1_PP_MARINA_complexity_endpoints
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (ω fStar : ℝ) (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStep : PPStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω r) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective A.problem x0 - fStar
    let bracket := rootMeanSquare Llocal *
      (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
        (A.refreshProbability * r.1)))
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) A.problem (ppProcess (r := r) A x0)
          (ppPathLaw (r := r) A) ε)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
        (fun ε => ppCommunicationCount d n r (K ε) A.refreshProbability ζ)
        (fun ε => d.1 * n.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 * n.1 +
            (1 - A.refreshProbability) * ζ * r.1)) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 - fStar :=
    sub_nonneg.mpr (hLower x0)
  dsimp
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective A.problem x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal *
    (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
      (A.refreshProbability * r.1)))
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    positivity
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq : globalObjective A.problem x0 - fStar = 0 := hGapZero.symm
    have hΔzero : Δ = 0 := by simpa [Δ] using hGapEq
    refine ⟨fun _ => K₁, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold NonconvexAccuracy
      have hE1 := Theorem_E1_PP_MARINA_nonconvex (K := K₁) A x0
        Llocal ω fStar hLower hSmooth hQuantizer hClients hStep
      refine ⟨hE1.1, hE1.2.trans ?_⟩
      rw [hGapEq]
      simp
      positivity
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        change Δ / (ε : ℝ) ^ 2 * bracket = 0
        rw [hΔzero]
        ring
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · unfold AccuracyBigO
      have hInitNe : (d.1 : ℝ) * n.1 ≠ 0 := by
        exact mul_ne_zero
          (by exact_mod_cast (Nat.ne_of_gt d.2))
          (by exact_mod_cast (Nat.ne_of_gt n.2))
      rw [show (fun ε : Accuracy => (d.1 : ℝ) * n.1 +
          (globalObjective A.problem x0 - fStar) / (ε : ℝ) ^ 2 *
            (rootMeanSquare Llocal *
              (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
                (A.refreshProbability * r.1)))) *
            (A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1)) =
          (fun _ : Accuracy => (d.1 : ℝ) * n.1) by
        funext ε
        rw [hGapEq]
        simp]
      rw [show (fun _ : Accuracy => ppCommunicationCount d n r K₁
          A.refreshProbability (expectedDensity A.quantizer)) =
          (fun _ : Accuracy => (d.1 : ℝ) * n.1 +
            (A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1)) by
        funext ε
        rw [Theorem_E1_E2_communication_count]
        norm_num [K₁]]
      exact
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) * n.1 +
            (A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1))
          hInitNe accuracyToZero)
  · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hBracketEq : bracket = 0 := hBracketZero.symm
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hfactor : 0 < 1 + Real.sqrt
            ((1 - A.refreshProbability) * (1 + ω) /
              (A.refreshProbability * r.1)) := by
          positivity
        dsimp [bracket] at hBracketEq
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        A.problem Llocal fStar hLower hSmooth hLzero
      refine ⟨fun _ => K₁, ?_⟩
      unfold TwoEndpointComplexity
      refine ⟨?_, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hE1 := Theorem_E1_PP_MARINA_nonconvex (K := K₁) A x0
          Llocal ω fStar hLower hSmooth hQuantizer hClients hStep
        refine ⟨hE1.1, ?_⟩
        have heq : (fun z =>
            ‖globalGradient A.problem
              (uniformOutput (K := K₁) (ppProcess (r := r) A x0) z)‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change Δ / (ε : ℝ) ^ 2 * bracket = 0
          rw [hBracketEq]
          ring
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
              accuracyToZero)
      · unfold AccuracyBigO
        have hInitNe : (d.1 : ℝ) * n.1 ≠ 0 := by
          exact mul_ne_zero
            (by exact_mod_cast (Nat.ne_of_gt d.2))
            (by exact_mod_cast (Nat.ne_of_gt n.2))
        rw [show (fun ε : Accuracy => (d.1 : ℝ) * n.1 +
            (globalObjective A.problem x0 - fStar) / (ε : ℝ) ^ 2 *
              (rootMeanSquare Llocal *
                (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
                  (A.refreshProbability * r.1)))) *
              (A.refreshProbability * d.1 * n.1 +
                (1 - A.refreshProbability) *
                  expectedDensity A.quantizer * r.1)) =
            (fun _ : Accuracy => (d.1 : ℝ) * n.1) by
          funext ε
          change (d.1 : ℝ) * n.1 + Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) * ζ * r.1) = d.1 * n.1
          rw [hBracketEq]
          ring]
        rw [show (fun _ : Accuracy => ppCommunicationCount d n r K₁
            A.refreshProbability (expectedDensity A.quantizer)) =
            (fun _ : Accuracy => (d.1 : ℝ) * n.1 +
              (A.refreshProbability * d.1 * n.1 +
                (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1)) by
          funext ε
          rw [Theorem_E1_E2_communication_count]
          norm_num [K₁]]
        exact
          (Asymptotics.isBigO_const_const
            ((d.1 : ℝ) * n.1 +
              (A.refreshProbability * d.1 * n.1 +
                (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1))
            hInitNe accuracyToZero)
    · let K : Accuracy → Count := fun ε =>
        ⟨max 1 (Nat.ceil (2 * Δ /
          ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
      have hΔpos : 0 < Δ := by simpa [Δ] using hGapPos
      have hScalar := positive_inverse_square_ceiling_schedule
        Δ (A.stepSize : ℝ) bracket hΔpos A.stepSize.property hBracketPos
      have hKBound : ∀ ε : Accuracy,
          2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) ≤
            (ε : ℝ) ^ 2 := by
        intro ε
        simpa [K] using hScalar.1 ε
      have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
          (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) := by
        simpa [K] using hScalar.2
      have hScaleNonneg :
          ∀ᶠ ε : Accuracy in accuracyToZero,
            0 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by
        filter_upwards [] with ε
        positivity
      refine ⟨K, ?_⟩
      unfold TwoEndpointComplexity
      refine ⟨?_, Or.inr hKBigO, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hE1 := Theorem_E1_PP_MARINA_nonconvex (K := K ε) A x0
          Llocal ω fStar hLower hSmooth hQuantizer hClients hStep
        refine ⟨hE1.1, hE1.2.trans ?_⟩
        simpa [Δ] using hKBound ε
      · let ppPayload : ℝ := A.refreshProbability * d.1 * n.1 +
            (1 - A.refreshProbability) * ζ * r.1
        have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
        have hnpos : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
        have hInitPos : 0 < (d.1 : ℝ) * n.1 := mul_pos hdpos hnpos
        have hPPPayloadPos : 0 < ppPayload := by
          dsimp [ppPayload]
          exact add_pos_of_pos_of_nonneg
            (mul_pos (mul_pos hp hdpos) hnpos)
            (mul_nonneg
              (mul_nonneg (sub_nonneg.mpr hp1) hζ) (by positivity))
        have hComm := accuracyBigO_affine_cost_of_schedule
          (K := fun ε => ((K ε).1 : ℝ))
          (scale := fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
          (init := (d.1 : ℝ) * n.1)
          (actualPayload := ppPayload)
          (targetPayload := ppPayload)
          (payloadFactor := 1)
          hKBigO hInitPos hPPPayloadPos.le hPPPayloadPos
            zero_lt_one (by simp) hScaleNonneg
        rw [show (fun ε => ppCommunicationCount d n r (K ε)
            A.refreshProbability (expectedDensity A.quantizer)) =
            (fun ε => (d.1 : ℝ) * n.1 + ((K ε).1 : ℝ) * ppPayload) by
          funext ε
          rw [Theorem_E1_E2_communication_count]]
        change AccuracyBigO
          (fun ε => (d.1 : ℝ) * n.1 + ((K ε).1 : ℝ) * ppPayload)
          (fun ε => (d.1 : ℝ) * n.1 +
            (Δ / (ε : ℝ) ^ 2 * bracket) * ppPayload)
        exact hComm

/-- `book/MARINA/MARINA.json#/key_lemmas/25`: Corollary E.1 family. -/
theorem Corollary_E1_PP_MARINA_complexity
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (ω fStar : ℝ) (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStep : PPDensityStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      ω (expectedDensity A.quantizer) d n r)
    (hSchedule : A.refreshProbability =
      ppDensityRefreshSchedule (expectedDensity A.quantizer) d n r) :
    let ζ := expectedDensity A.quantizer
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) A.problem (ppProcess (r := r) A x0)
          (ppPathLaw (r := r) A) ε)
        (fun ε => (globalObjective A.problem x0 - fStar) *
          rootMeanSquare Llocal / (ε : ℝ) ^ 2 *
          (1 + Real.sqrt ((1 + ω) / r.1 *
            (d.1 * n.1 / (ζ * r.1) - 1))))
        (fun ε => ppCommunicationCount d n r (K ε) A.refreshProbability ζ)
        (fun ε => d.1 * n.1 + (globalObjective A.problem x0 - fStar) *
          rootMeanSquare Llocal / (ε : ℝ) ^ 2 *
          (ζ * r.1 + Real.sqrt ((1 + ω) * ζ *
            (d.1 * n.1 - ζ * r.1)))) := by
  dsimp
  have hGeneralStep : PPStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) A.refreshProbability ω r :=
    density_stepsize_bridge_PP hSchedule hStep
  let ζ : ℝ := expectedDensity A.quantizer
  let D : ℝ := (d.1 : ℝ) * (n.1 : ℝ)
  let q : ℝ := ζ * (r.1 : ℝ)
  have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hr : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hpEq : A.refreshProbability = q / D := by
    simpa [q, D, ζ, ppDensityRefreshSchedule] using hSchedule
  have hq : 0 < q := by
    have hp := A.refresh_admissible.1
    rw [hpEq] at hp
    rcases div_pos_iff.mp hp with hp | hp
    · exact hp.1
    · exfalso
      linarith
  have hqD : q ≤ D := by
    have hp := A.refresh_admissible.2
    rw [hpEq] at hp
    simpa using (div_le_iff₀ hD).mp hp
  have hζ : 0 < ζ := by
    dsimp [q] at hq
    nlinarith
  have hOneOmega : 0 ≤ 1 + ω := by
    linarith [hQuantizer.1]
  have hOddsNonneg : 0 ≤ D / q - 1 :=
    sub_nonneg.mpr ((one_le_div hq).2 hqD)
  have hIterRadNonneg :
      0 ≤ (1 + ω) / (r.1 : ℝ) * (D / q - 1) :=
    mul_nonneg (div_nonneg hOneOmega hr.le) hOddsNonneg
  have hCommRadNonneg :
      0 ≤ (1 + ω) * ζ * (D - q) :=
    mul_nonneg (mul_nonneg hOneOmega hζ.le) (sub_nonneg.mpr hqD)
  have hRad :
      (1 - q / D) * (1 + ω) /
          (q / D * (r.1 : ℝ)) =
        (1 + ω) / (r.1 : ℝ) * (D / q - 1) := by
    field_simp [ne_of_gt hD, ne_of_gt hq, ne_of_gt hr]
    <;> ring
  have hSqrtDensity :
      q * Real.sqrt
          ((1 + ω) / (r.1 : ℝ) * (D / q - 1)) =
        Real.sqrt ((1 + ω) * ζ * (D - q)) := by
    have hsq :
        (q * Real.sqrt
            ((1 + ω) / (r.1 : ℝ) * (D / q - 1))) ^ 2 =
          (Real.sqrt ((1 + ω) * ζ * (D - q))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hIterRadNonneg,
        Real.sq_sqrt hCommRadNonneg]
      dsimp [q]
      field_simp [ne_of_gt hζ, ne_of_gt hr]
    have hleft : 0 ≤ q * Real.sqrt
        ((1 + ω) / (r.1 : ℝ) * (D / q - 1)) := by positivity
    have hright : 0 ≤ Real.sqrt ((1 + ω) * ζ * (D - q)) :=
      Real.sqrt_nonneg _
    nlinarith
  have hPayloadLe :
      q / D * D + (1 - q / D) * q ≤ 2 * q := by
    have hform :
        q / D * D + (1 - q / D) * q =
          2 * q - q ^ 2 / D := by
      field_simp [ne_of_gt hD]
      <;> ring
    rw [hform]
    have hsquareDiv : 0 ≤ q ^ 2 / D := by positivity
    linarith
  rcases (Theorem_E1_PP_MARINA_complexity_endpoints A x0 Llocal ω fStar
      hLower hSmooth hQuantizer hClients hGeneralStep) with
    ⟨K, hAccuracy, hIterations, hCommunication⟩
  refine ⟨K, hAccuracy, ?_, ?_⟩
  · convert hIterations using 1
    funext ε
    rw [hpEq, hRad]
    ring
  · unfold AccuracyBigO at hCommunication ⊢
    refine hCommunication.trans ?_
    rw [Asymptotics.isBigO_iff']
    refine ⟨2, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro ε
    let base : ℝ :=
      (globalObjective A.problem x0 - fStar) / (ε : ℝ) ^ 2 *
        (rootMeanSquare Llocal *
          (1 + Real.sqrt
            ((1 + ω) / (r.1 : ℝ) * (D / q - 1))))
    let sourcePayload : ℝ := q / D * D + (1 - q / D) * q
    let targetPayload : ℝ :=
      q + Real.sqrt ((1 + ω) * ζ * (D - q))
    have hGap : 0 ≤ globalObjective A.problem x0 - fStar :=
      sub_nonneg.mpr (hLower x0)
    have hBase : 0 ≤ base := by
      dsimp [base]
      exact mul_nonneg
        (div_nonneg hGap (sq_nonneg (ε : ℝ)))
        (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hSourcePayload : 0 ≤ sourcePayload := by
      dsimp [sourcePayload]
      exact add_nonneg
        (mul_nonneg (div_nonneg hq.le hD.le) hD.le)
        (mul_nonneg
          (sub_nonneg.mpr ((div_le_one hD).2 hqD)) hq.le)
    have hTargetPayload : 0 < targetPayload := by
      dsimp [targetPayload]
      positivity
    have hPayloadBound : sourcePayload ≤ 2 * targetPayload := by
      dsimp [sourcePayload, targetPayload]
      calc
        q / D * D + (1 - q / D) * q ≤ 2 * q := hPayloadLe
        _ ≤ 2 * (q + Real.sqrt ((1 + ω) * ζ * (D - q))) := by
          nlinarith [Real.sqrt_nonneg ((1 + ω) * ζ * (D - q))]
    have hTargetTail :
        (globalObjective A.problem x0 - fStar) *
              rootMeanSquare Llocal / (ε : ℝ) ^ 2 *
              targetPayload =
            base * q := by
      dsimp [targetPayload, base]
      rw [← hSqrtDensity]
      ring
    rw [hpEq, hRad]
    change ‖D + base *
        (q / D * (d.1 : ℝ) * (n.1 : ℝ) +
          (1 - q / D) * ζ * (r.1 : ℝ))‖ ≤
      2 * ‖D +
        (globalObjective A.problem x0 - fStar) *
          rootMeanSquare Llocal / (ε : ℝ) ^ 2 * targetPayload‖
    have hSourcePayloadEq :
        q / D * (d.1 : ℝ) * (n.1 : ℝ) +
            (1 - q / D) * ζ * (r.1 : ℝ) =
          sourcePayload := by
      dsimp [sourcePayload, D, q]
      ring
    rw [hSourcePayloadEq]
    rw [hTargetTail, Real.norm_eq_abs,
      abs_of_nonneg
        (add_nonneg hD.le (mul_nonneg hBase hSourcePayload)),
      Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hD.le (mul_nonneg hBase hq.le))]
    have htail := mul_le_mul_of_nonneg_left hPayloadBound hBase
    nlinarith

set_option maxHeartbeats 800000 in
/-- `book/MARINA/MARINA.json#/key_lemmas/27`: Corollary E.2 family. -/
theorem Corollary_E2_PP_MARINA_PL_complexity
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStep : PPPLDensityStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      ω (expectedDensity A.quantizer) μ d n r)
    (hSchedule : A.refreshProbability =
      ppDensityRefreshSchedule (expectedDensity A.quantizer) d n r) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective A.problem x0 - globalObjective A.problem xStar
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => PLAccuracy (K ε) A.problem (ppProcess (r := r) A x0)
          (ppPathLaw (r := r) A) xStar ε)
        (fun ε => max (d.1 * n.1 / (ζ * r.1))
          (rootMeanSquare Llocal / μ *
            (1 + Real.sqrt ((1 + ω) / r.1 *
              (d.1 * n.1 / (ζ * r.1) - 1)))) * Real.log (Δ / (ε : ℝ)))
        (fun ε => ppCommunicationCount d n r (K ε) A.refreshProbability ζ)
        (fun ε => d.1 * n.1 + max (d.1 * n.1 : ℝ)
          (rootMeanSquare Llocal / μ *
            (ζ * r.1 + Real.sqrt ((1 + ω) * ζ *
              (d.1 * n.1 - ζ * r.1)))) * Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 -
      globalObjective A.problem xStar := sub_nonneg.mpr (hPL.1 x0)
  rcases hGapNonneg.eq_or_lt with hGap | hGap
  · dsimp
    let K₁ : Count := ⟨1, by norm_num⟩
    have hInitialZero : globalObjective A.problem x0 =
        globalObjective A.problem xStar := sub_eq_zero.mp hGap.symm
    refine ⟨fun _ => K₁, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hGeneralStep : PPPLStepsizeCondition A.stepSize
          (rootMeanSquare Llocal) A.refreshProbability ω μ r :=
        density_stepsize_bridge_PP_PL hSchedule hStep
      have hE2 := Theorem_E2_PP_MARINA_PL (K := K₁) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hClients hGeneralStep
      refine ⟨hE2.1, ?_⟩
      have hNonpos :
          (∫ path,
            (globalObjective A.problem (ppProcess (r := r) A x0 K₁.1 path).x -
              globalObjective A.problem xStar) ∂ppPathLaw (r := r) A) ≤ 0 := by
        rw [hInitialZero] at hE2
        simpa using hE2.2
      exact hNonpos.trans (le_of_lt ε.property)
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        rw [hInitialZero]
        simp
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ)) accuracyToZero)
    · unfold AccuracyBigO
      have hdn : (d.1 * n.1 : ℝ) ≠ 0 := by
        exact mul_ne_zero (ne_of_gt (by exact_mod_cast d.2))
          (ne_of_gt (by exact_mod_cast n.2))
      rw [show (fun ε : Accuracy => (d.1 * n.1 : ℝ) +
            max (d.1 * n.1 : ℝ)
              (rootMeanSquare Llocal / μ *
                (expectedDensity A.quantizer * r.1 +
                  Real.sqrt ((1 + ω) * expectedDensity A.quantizer *
                    (d.1 * n.1 - expectedDensity A.quantizer * r.1)))) *
              Real.log ((globalObjective A.problem x0 -
                globalObjective A.problem xStar) / (ε : ℝ))) =
          (fun _ : Accuracy => (d.1 * n.1 : ℝ)) by
            funext ε
            rw [hInitialZero]
            simp]
      simpa [ppCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 * n.1 : ℝ) +
            (A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1))
          hdn accuracyToZero)
  · dsimp
    let ζ : ℝ := expectedDensity A.quantizer
    let Δ : ℝ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let D : ℝ := (d.1 : ℝ) * (n.1 : ℝ)
    let q : ℝ := ζ * (r.1 : ℝ)
    let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    let Siter : ℝ := max (D / q)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 + ω) / (r.1 : ℝ) * (D / q - 1))))
    let Scomm : ℝ := max D
      (rootMeanSquare Llocal / μ *
        (q + Real.sqrt ((1 + ω) * ζ * (D - q))))
    have hGeneralStep : PPPLStepsizeCondition A.stepSize
        (rootMeanSquare Llocal) A.refreshProbability ω μ r :=
      density_stepsize_bridge_PP_PL hSchedule hStep
    have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
    have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
    have hr : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
    have hD : 0 < D := by
      dsimp [D]
      positivity
    have hpEq : A.refreshProbability = q / D := by
      simpa [q, D, ζ, ppDensityRefreshSchedule] using hSchedule
    have hq : 0 < q := by
      have hp := A.refresh_admissible.1
      rw [hpEq] at hp
      rcases div_pos_iff.mp hp with hp | hp
      · exact hp.1
      · exfalso
        linarith
    have hqD : q ≤ D := by
      have hp := A.refresh_admissible.2
      rw [hpEq] at hp
      simpa using (div_le_iff₀ hD).mp hp
    have hζ : 0 < ζ := by
      dsimp [q] at hq
      nlinarith
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos A.stepSize.property μ.property
    have hc1 : c ≤ 1 := by
      have hcP := hGeneralStep.2
      have hp1 := A.refresh_admissible.2
      dsimp [c]
      nlinarith
    have hSiter : 0 < Siter := by
      dsimp [Siter]
      exact (div_pos hD hq).trans_le (le_max_left _ _)
    have hScomm : 0 < Scomm := by
      dsimp [Scomm]
      exact hD.trans_le (le_max_left _ _)
    let K : Accuracy → Count := fun ε =>
      ⟨max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)), by omega⟩
    have hScalar := positive_geometric_ceiling_schedule
      Δ c Siter hGap hc hc1 hSiter
    have hContract : ∀ ε : Accuracy,
        (1 - c) ^ (K ε).1 * Δ ≤ (ε : ℝ) := by
      intro ε
      simpa [K] using hScalar.1 ε
    have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => Siter * Real.log (Δ / (ε : ℝ))) := by
      simpa [K] using hScalar.2
    refine ⟨K, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hE2 := Theorem_E2_PP_MARINA_PL (K := K ε) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hClients hGeneralStep
      refine ⟨hE2.1, hE2.2.trans ?_⟩
      simpa [c, Δ] using hContract ε
    · refine Or.inr ?_
      simpa [Siter, D, q, ζ, Δ] using hKBigO
    · let payload : ℝ := A.refreshProbability * D +
          (1 - A.refreshProbability) * q
      have hp0 : 0 ≤ A.refreshProbability := A.refresh_admissible.1.le
      have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp0 hD.le)
          (mul_nonneg (sub_nonneg.mpr hp1) hq.le)
      have hOddsNonneg : 0 ≤ D / q - 1 := by
        exact sub_nonneg.mpr ((one_le_div hq).2 hqD)
      have hOneOmega : 0 ≤ 1 + ω := by
        linarith [hQuantizer.1]
      have hSqrtIterNonneg :
          0 ≤ (1 + ω) / (r.1 : ℝ) * (D / q - 1) := by
        exact mul_nonneg (div_nonneg hOneOmega hr.le) hOddsNonneg
      have hSqrtCommNonneg :
          0 ≤ (1 + ω) * ζ * (D - q) := by
        exact mul_nonneg (mul_nonneg hOneOmega hζ.le) (sub_nonneg.mpr hqD)
      have hSqrtDensity :
          q * Real.sqrt ((1 + ω) / (r.1 : ℝ) * (D / q - 1)) =
            Real.sqrt ((1 + ω) * ζ * (D - q)) := by
        have hsq :
            (q * Real.sqrt ((1 + ω) / (r.1 : ℝ) * (D / q - 1))) ^ 2 =
              (Real.sqrt ((1 + ω) * ζ * (D - q))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hSqrtIterNonneg,
            Real.sq_sqrt hSqrtCommNonneg]
          dsimp [q]
          field_simp [ne_of_gt hζ, ne_of_gt hr]
        have hleft : 0 ≤ q *
            Real.sqrt ((1 + ω) / (r.1 : ℝ) * (D / q - 1)) := by
          positivity
        have hright : 0 ≤ Real.sqrt ((1 + ω) * ζ * (D - q)) :=
          Real.sqrt_nonneg _
        nlinarith
      have hPayloadLe : payload ≤ 2 * q := by
        have hform : payload = 2 * q - q ^ 2 / D := by
          dsimp [payload]
          rw [hpEq]
          field_simp [ne_of_gt hD]
          ring
        rw [hform]
        have hsquareDiv : 0 ≤ q ^ 2 / D := by positivity
        linarith
      have hSiterQ : Siter * q = Scomm := by
        dsimp [Siter, Scomm]
        rw [max_mul_of_nonneg _ _ hq.le]
        congr 1
        · field_simp [ne_of_gt hq]
        · calc
            (rootMeanSquare Llocal / (μ : ℝ) *
                (1 + Real.sqrt
                  ((1 + ω) / (r.1 : ℝ) * (D / q - 1)))) * q =
              rootMeanSquare Llocal / (μ : ℝ) *
                (q + q * Real.sqrt
                  ((1 + ω) / (r.1 : ℝ) * (D / q - 1))) := by ring
            _ = rootMeanSquare Llocal / (μ : ℝ) *
                (q + Real.sqrt ((1 + ω) * ζ * (D - q))) := by
              rw [hSqrtDensity]
      have hPayloadBound : Siter * payload ≤ 2 * Scomm := by
        calc
          Siter * payload ≤ Siter * (2 * q) :=
            mul_le_mul_of_nonneg_left hPayloadLe hSiter.le
          _ = 2 * (Siter * q) := by ring
          _ = 2 * Scomm := by rw [hSiterQ]
      unfold AccuracyBigO at hKBigO ⊢
      have hRoundO : Asymptotics.IsBigO accuracyToZero
          (fun ε : Accuracy => ((K ε).1 : ℝ) * payload)
          (fun ε => D + Scomm * Real.log (Δ / (ε : ℝ))) := by
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨2 * C, by positivity, ?_⟩
        filter_upwards [hKC.bound,
          eventually_one_le_log_gap_div_accuracy hGap]
          with ε hKbound hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have hKn : ((K ε).1 : ℝ) ≤
            C * (Siter * Real.log (Δ / (ε : ℝ))) := by
          have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
          rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
            Real.norm_eq_abs, abs_of_pos (mul_pos hSiter hlogpos)] at hKbound
          exact hKbound
        have hKpayload : ((K ε).1 : ℝ) * payload ≤
            (C * (Siter * Real.log (Δ / (ε : ℝ)))) * payload :=
          mul_le_mul_of_nonneg_right hKn hpayload
        have hscaled := mul_le_mul_of_nonneg_left hPayloadBound hC.le
        have hscaledLog := mul_le_mul_of_nonneg_right hscaled hlogpos.le
        have hround : ((K ε).1 : ℝ) * payload ≤
            2 * C * Scomm * Real.log (Δ / (ε : ℝ)) := by
          calc
            ((K ε).1 : ℝ) * payload ≤
                (C * (Siter * Real.log (Δ / (ε : ℝ)))) * payload := hKpayload
            _ = (C * (Siter * payload)) * Real.log (Δ / (ε : ℝ)) := by ring
            _ ≤ (C * (2 * Scomm)) * Real.log (Δ / (ε : ℝ)) := hscaledLog
            _ = 2 * C * Scomm * Real.log (Δ / (ε : ℝ)) := by ring
        have htargetPos : 0 < D +
            Scomm * Real.log (Δ / (ε : ℝ)) := by positivity
        have hroundNonneg : 0 ≤ ((K ε).1 : ℝ) * payload := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hroundNonneg,
          Real.norm_eq_abs, abs_of_pos htargetPos]
        calc
          ((K ε).1 : ℝ) * payload ≤
              2 * C * Scomm * Real.log (Δ / (ε : ℝ)) := hround
          _ ≤ (2 * C) *
              (D + Scomm * Real.log (Δ / (ε : ℝ))) := by
            have : 0 ≤ (2 * C) * D := by positivity
            nlinarith
      have hInitO : Asymptotics.IsBigO accuracyToZero
          (fun _ : Accuracy => D)
          (fun ε => D + Scomm * Real.log (Δ / (ε : ℝ))) := by
        rw [Asymptotics.isBigO_iff']
        refine ⟨1, zero_lt_one, ?_⟩
        filter_upwards [eventually_one_le_log_gap_div_accuracy hGap] with ε hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have htargetPos : 0 < D +
            Scomm * Real.log (Δ / (ε : ℝ)) := by positivity
        rw [Real.norm_eq_abs, abs_of_pos hD,
          Real.norm_eq_abs, abs_of_pos htargetPos, one_mul]
        have htail : 0 ≤ Scomm * Real.log (Δ / (ε : ℝ)) :=
          (mul_pos hScomm hlogpos).le
        linarith
      have hTotalO := hInitO.add hRoundO
      convert hTotalO using 1 <;>
        funext ε <;>
        simp only [ppCommunicationCount, payload, D, q, ζ, Scomm, Δ] <;>
        ring

/-- `book/MARINA/MARINA.json#/key_lemmas/12`, Theorem C.2 / Eqs. (25)-(26). -/
theorem Theorem_C2_MARINA_PL_complexity_endpoints
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : MARINAPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω μ n) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let factor := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
          (A.refreshProbability * n.1))))
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => PLAccuracy (K ε) A.problem (marinaProcess A x0)
          (basicPathLaw A) xStar ε)
        (fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + factor *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ) *
          Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 -
      globalObjective A.problem xStar := sub_nonneg.mpr (hPL.1 x0)
  rcases hGapNonneg.eq_or_lt with hGap | hGap
  · dsimp
    let K₁ : Count := ⟨1, by norm_num⟩
    have hInitialZero : globalObjective A.problem x0 =
        globalObjective A.problem xStar := sub_eq_zero.mp hGap.symm
    refine ⟨fun _ => K₁, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hC2 := Theorem_C2_MARINA_PL (K := K₁) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hStep
      refine ⟨hC2.1, ?_⟩
      have hNonpos :
          (∫ path,
            (globalObjective A.problem (marinaProcess A x0 K₁.1 path).x -
              globalObjective A.problem xStar) ∂basicPathLaw A) ≤ 0 := by
        rw [hInitialZero] at hC2
        simpa using hC2.2
      exact hNonpos.trans (le_of_lt ε.property)
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        rw [hInitialZero]
        simp
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt d.2)
      rw [show (fun ε : Accuracy => (d.1 : ℝ) +
          max (1 / A.refreshProbability)
            (rootMeanSquare Llocal / (μ : ℝ) *
              (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
                (A.refreshProbability * (n.1 : ℝ))))) *
            (A.refreshProbability * (d.1 : ℝ) +
              (1 - A.refreshProbability) * expectedDensity A.quantizer) *
            Real.log ((globalObjective A.problem x0 -
              globalObjective A.problem xStar) / (ε : ℝ))) =
          (fun _ : Accuracy => (d.1 : ℝ)) by
            funext ε
            rw [hInitialZero]
            simp]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) +
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer))
          hdne accuracyToZero)
  · dsimp
    let ζ : ℝ := expectedDensity A.quantizer
    let Δ : ℝ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    let factor : ℝ := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
          (A.refreshProbability * n.1))))
    have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
    have hp : 0 < A.refreshProbability := A.refresh_admissible.1
    have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
    have hζ : 0 ≤ ζ := by
      dsimp [ζ]
      exact expectedDensity_nonneg_of_unbiased hQuantizer
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos A.stepSize.property μ.property
    have hc1 : c ≤ 1 := by
      have hcP := hStep.2
      dsimp [c]
      nlinarith
    have hfactor : 0 < factor := by
      dsimp [factor]
      exact (div_pos zero_lt_one hp).trans_le (le_max_left _ _)
    let K : Accuracy → Count := fun ε =>
      ⟨max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)), by omega⟩
    have hScalar := positive_geometric_ceiling_schedule
      Δ c factor hGap hc hc1 hfactor
    have hContract : ∀ ε : Accuracy,
        (1 - c) ^ (K ε).1 * Δ ≤ (ε : ℝ) := by
      intro ε
      simpa [K] using hScalar.1 ε
    have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => factor * Real.log (Δ / (ε : ℝ))) := by
      simpa [K] using hScalar.2
    refine ⟨K, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hC2 := Theorem_C2_MARINA_PL (K := K ε) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hStep
      refine ⟨hC2.1, hC2.2.trans ?_⟩
      simpa [c, Δ] using hContract ε
    · refine Or.inr ?_
      simpa [factor, Δ] using hKBigO
    · let payload : ℝ := A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ
      have hpayload : 0 < payload := by
        dsimp [payload]
        exact add_pos_of_pos_of_nonneg (mul_pos hp hd)
          (mul_nonneg (sub_nonneg.mpr hp1) hζ)
      unfold AccuracyBigO at hKBigO ⊢
      have hRoundO : Asymptotics.IsBigO accuracyToZero
          (fun ε : Accuracy => ((K ε).1 : ℝ) * payload)
          (fun ε => (d.1 : ℝ) + factor * payload *
            Real.log (Δ / (ε : ℝ))) := by
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨C, hC, ?_⟩
        filter_upwards [hKC.bound,
          eventually_one_le_log_gap_div_accuracy hGap]
          with ε hKbound hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have hKn : ((K ε).1 : ℝ) ≤
            C * (factor * Real.log (Δ / (ε : ℝ))) := by
          have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
          rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
            Real.norm_eq_abs, abs_of_pos (mul_pos hfactor hlogpos)] at hKbound
          exact hKbound
        have hKpayload : ((K ε).1 : ℝ) * payload ≤
            (C * (factor * Real.log (Δ / (ε : ℝ)))) * payload :=
          mul_le_mul_of_nonneg_right hKn hpayload.le
        have htargetPos : 0 < (d.1 : ℝ) + factor * payload *
            Real.log (Δ / (ε : ℝ)) := by positivity
        have hroundNonneg : 0 ≤ ((K ε).1 : ℝ) * payload := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hroundNonneg,
          Real.norm_eq_abs, abs_of_pos htargetPos]
        calc
          ((K ε).1 : ℝ) * payload ≤
              (C * (factor * Real.log (Δ / (ε : ℝ)))) * payload := hKpayload
          _ = C * (factor * payload * Real.log (Δ / (ε : ℝ))) := by ring
          _ ≤ C * ((d.1 : ℝ) + factor * payload *
              Real.log (Δ / (ε : ℝ))) := by
            have : 0 ≤ C * (d.1 : ℝ) := by positivity
            nlinarith
      have hInitO : Asymptotics.IsBigO accuracyToZero
          (fun _ : Accuracy => (d.1 : ℝ))
          (fun ε => (d.1 : ℝ) + factor * payload *
            Real.log (Δ / (ε : ℝ))) := by
        rw [Asymptotics.isBigO_iff']
        refine ⟨1, zero_lt_one, ?_⟩
        filter_upwards [eventually_one_le_log_gap_div_accuracy hGap]
          with ε hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have htargetPos : 0 < (d.1 : ℝ) + factor * payload *
            Real.log (Δ / (ε : ℝ)) := by positivity
        rw [Real.norm_eq_abs, abs_of_pos hd,
          Real.norm_eq_abs, abs_of_pos htargetPos, one_mul]
        have htail : 0 ≤ factor * payload * Real.log (Δ / (ε : ℝ)) := by
          positivity
        linarith
      have hTotalO := hInitO.add hRoundO
      simpa [allWorkerCommunicationCount, payload, ζ, factor, Δ] using hTotalO

/-- `book/MARINA/MARINA.json#/key_lemmas/26`, Theorem E.2 / Eqs. (63)-(64). -/
theorem Theorem_E2_PP_MARINA_PL_complexity_endpoints
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStep : PPPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω μ r) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let factor := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
          (A.refreshProbability * r.1))))
    ∃ K : Accuracy → Count,
      TwoEndpointComplexity K
        (fun ε => PLAccuracy (K ε) A.problem (ppProcess (r := r) A x0)
          (ppPathLaw (r := r) A) xStar ε)
        (fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (fun ε => ppCommunicationCount d n r (K ε) A.refreshProbability ζ)
        (fun ε => d.1 * n.1 + factor *
          (A.refreshProbability * d.1 * n.1 +
            (1 - A.refreshProbability) * ζ * r.1) *
          Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 -
      globalObjective A.problem xStar := sub_nonneg.mpr (hPL.1 x0)
  rcases hGapNonneg.eq_or_lt with hGap | hGap
  · dsimp
    let K₁ : Count := ⟨1, by norm_num⟩
    have hInitialZero : globalObjective A.problem x0 =
        globalObjective A.problem xStar := sub_eq_zero.mp hGap.symm
    refine ⟨fun _ => K₁, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hE2 := Theorem_E2_PP_MARINA_PL (K := K₁) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hClients hStep
      refine ⟨hE2.1, ?_⟩
      have hNonpos :
          (∫ path,
            (globalObjective A.problem (ppProcess (r := r) A x0 K₁.1 path).x -
              globalObjective A.problem xStar) ∂ppPathLaw (r := r) A) ≤ 0 := by
        rw [hInitialZero] at hE2
        simpa using hE2.2
      exact hNonpos.trans (le_of_lt ε.property)
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        rw [hInitialZero]
        simp
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · unfold AccuracyBigO
      have hdn : (d.1 * n.1 : ℝ) ≠ 0 := by
        exact mul_ne_zero (ne_of_gt (by exact_mod_cast d.2))
          (ne_of_gt (by exact_mod_cast n.2))
      rw [show (fun ε : Accuracy => (d.1 * n.1 : ℝ) +
          max (1 / A.refreshProbability)
            (rootMeanSquare Llocal / (μ : ℝ) *
              (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
                (A.refreshProbability * (r.1 : ℝ))))) *
            (A.refreshProbability * (d.1 : ℝ) * (n.1 : ℝ) +
              (1 - A.refreshProbability) * expectedDensity A.quantizer *
                (r.1 : ℝ)) *
            Real.log ((globalObjective A.problem x0 -
              globalObjective A.problem xStar) / (ε : ℝ))) =
          (fun _ : Accuracy => (d.1 * n.1 : ℝ)) by
            funext ε
            rw [hInitialZero]
            simp]
      simpa [ppCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 * n.1 : ℝ) +
            (A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1))
          hdn accuracyToZero)
  · dsimp
    let ζ : ℝ := expectedDensity A.quantizer
    let Δ : ℝ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let D : ℝ := (d.1 : ℝ) * (n.1 : ℝ)
    let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    let factor : ℝ := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
          (A.refreshProbability * r.1))))
    have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
    have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
    have hD : 0 < D := by
      dsimp [D]
      positivity
    have hp : 0 < A.refreshProbability := A.refresh_admissible.1
    have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
    have hζ : 0 ≤ ζ := by
      dsimp [ζ]
      exact expectedDensity_nonneg_of_unbiased hQuantizer
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos A.stepSize.property μ.property
    have hc1 : c ≤ 1 := by
      have hcP := hStep.2
      dsimp [c]
      nlinarith
    have hfactor : 0 < factor := by
      dsimp [factor]
      exact (div_pos zero_lt_one hp).trans_le (le_max_left _ _)
    let K : Accuracy → Count := fun ε =>
      ⟨max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)), by omega⟩
    have hScalar := positive_geometric_ceiling_schedule
      Δ c factor hGap hc hc1 hfactor
    have hContract : ∀ ε : Accuracy,
        (1 - c) ^ (K ε).1 * Δ ≤ (ε : ℝ) := by
      intro ε
      simpa [K] using hScalar.1 ε
    have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => factor * Real.log (Δ / (ε : ℝ))) := by
      simpa [K] using hScalar.2
    refine ⟨K, ?_⟩
    unfold TwoEndpointComplexity
    refine ⟨?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hE2 := Theorem_E2_PP_MARINA_PL (K := K ε) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hClients hStep
      refine ⟨hE2.1, hE2.2.trans ?_⟩
      simpa [c, Δ] using hContract ε
    · refine Or.inr ?_
      simpa [factor, Δ] using hKBigO
    · let payload : ℝ := A.refreshProbability * D +
          (1 - A.refreshProbability) * ζ * (r.1 : ℝ)
      have hpayload : 0 < payload := by
        dsimp [payload]
        exact add_pos_of_pos_of_nonneg (mul_pos hp hD)
          (mul_nonneg (mul_nonneg (sub_nonneg.mpr hp1) hζ)
            (by positivity))
      unfold AccuracyBigO at hKBigO ⊢
      have hRoundO : Asymptotics.IsBigO accuracyToZero
          (fun ε : Accuracy => ((K ε).1 : ℝ) * payload)
          (fun ε => D + factor * payload * Real.log (Δ / (ε : ℝ))) := by
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨C, hC, ?_⟩
        filter_upwards [hKC.bound,
          eventually_one_le_log_gap_div_accuracy hGap]
          with ε hKbound hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have hKn : ((K ε).1 : ℝ) ≤
            C * (factor * Real.log (Δ / (ε : ℝ))) := by
          have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
          rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
            Real.norm_eq_abs, abs_of_pos (mul_pos hfactor hlogpos)] at hKbound
          exact hKbound
        have hKpayload : ((K ε).1 : ℝ) * payload ≤
            (C * (factor * Real.log (Δ / (ε : ℝ)))) * payload :=
          mul_le_mul_of_nonneg_right hKn hpayload.le
        have htargetPos : 0 < D + factor * payload *
            Real.log (Δ / (ε : ℝ)) := by positivity
        have hroundNonneg : 0 ≤ ((K ε).1 : ℝ) * payload := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hroundNonneg,
          Real.norm_eq_abs, abs_of_pos htargetPos]
        calc
          ((K ε).1 : ℝ) * payload ≤
              (C * (factor * Real.log (Δ / (ε : ℝ)))) * payload := hKpayload
          _ = C * (factor * payload * Real.log (Δ / (ε : ℝ))) := by ring
          _ ≤ C * (D + factor * payload *
              Real.log (Δ / (ε : ℝ))) := by
            have : 0 ≤ C * D := by positivity
            nlinarith
      have hInitO : Asymptotics.IsBigO accuracyToZero
          (fun _ : Accuracy => D)
          (fun ε => D + factor * payload * Real.log (Δ / (ε : ℝ))) := by
        rw [Asymptotics.isBigO_iff']
        refine ⟨1, zero_lt_one, ?_⟩
        filter_upwards [eventually_one_le_log_gap_div_accuracy hGap]
          with ε hlog
        have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
          lt_of_lt_of_le zero_lt_one hlog
        have htargetPos : 0 < D + factor * payload *
            Real.log (Δ / (ε : ℝ)) := by positivity
        rw [Real.norm_eq_abs, abs_of_pos hD,
          Real.norm_eq_abs, abs_of_pos htargetPos, one_mul]
        have htail : 0 ≤ factor * payload * Real.log (Δ / (ε : ℝ)) := by
          positivity
        linarith
      have hTotalO := hInitO.add hRoundO
      convert hTotalO using 1 <;>
        funext ε <;>
        simp only [ppCommunicationCount, payload, D, ζ, factor, Δ] <;>
        ring

/-- The balanced finite-sum refresh schedule bounds the exact per-round oracle
and communication payloads used by the formal cost counters. -/
theorem finite_sum_density_schedule_payload_bounds
    {d m b0 : Count} {p ζ : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hζ : 0 ≤ ζ) (hb : b0.1 ≤ m.1)
    (hSchedule : p = finiteSumDensityBatchRefreshSchedule ζ d m b0) :
    0 < ζ ∧
      p * m.1 + 2 * (1 - p) * b0.1 ≤ 3 * b0.1 ∧
      p * d.1 + (1 - p) * ζ ≤ 2 * ζ := by
  have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
  have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hpDensity : p ≤ ζ / d.1 := by
    rw [hSchedule, finiteSumDensityBatchRefreshSchedule]
    exact min_le_left _ _
  have hpBatch : p ≤ (b0.1 : ℝ) / (m.1 + b0.1 : ℕ) := by
    rw [hSchedule, finiteSumDensityBatchRefreshSchedule]
    exact min_le_right _ _
  have hζpos : 0 < ζ := by
    have : 0 < ζ / d.1 := lt_of_lt_of_le hp hpDensity
    rcases div_pos_iff.mp this with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hd.le hneg.2).elim
  have hpBatch' : p * ((m.1 : ℝ) + b0.1) ≤ b0.1 := by
    have hden : 0 < (m.1 : ℝ) + b0.1 := by positivity
    apply (le_div_iff₀ hden).mp
    simpa using hpBatch
  have hpM : p * (m.1 : ℝ) ≤ b0.1 := by
    have hpb : 0 ≤ p * (b0.1 : ℝ) := mul_nonneg hp.le hb0.le
    nlinarith
  have hOracle :
      p * m.1 + 2 * (1 - p) * b0.1 ≤ 3 * b0.1 := by
    have htail : 0 ≤ (1 - p) * (b0.1 : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hp1) hb0.le
    have htailLe : (1 - p) * (b0.1 : ℝ) ≤ b0.1 := by
      nlinarith
    nlinarith
  have hpD : p * (d.1 : ℝ) ≤ ζ := by
    exact (le_div_iff₀ hd).mp hpDensity
  have hCommTail : (1 - p) * ζ ≤ ζ := by
    have : 0 ≤ p * ζ := mul_nonneg hp.le hζ
    nlinarith
  exact ⟨hζpos, hOracle, by nlinarith⟩

/-- Moving the positive batch-size factor through the two square roots turns
Corollary D.1's printed oracle scale into `b⁰` times its iteration bracket. -/
theorem finite_sum_nonconvex_oracle_scale_eq
    {d n m b0 : Count} (Δ L ℒ ω ζ ε : ℝ) (hω : 0 ≤ ω) :
    finiteSumNonconvexOracleScale Δ L ℒ ω ζ ε d n m b0 =
      m.1 + Δ / ε ^ 2 *
        (b0.1 * vrIterationBracket L ℒ ω
          (finiteSumDensityBatchRatio d m b0 ζ) n b0) := by
  have hb : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  let odds : ℝ := d.1 / ζ - 1
  let ratio : ℝ := finiteSumDensityBatchRatio d m b0 ζ
  have hmaxSq :
      max (odds * (b0.1 : ℝ) ^ 2) ((m.1 : ℝ) * b0.1) =
        (b0.1 : ℝ) ^ 2 * ratio := by
    dsimp [odds, ratio, finiteSumDensityBatchRatio]
    calc
      max ((d.1 / ζ - 1) * (b0.1 : ℝ) ^ 2) ((m.1 : ℝ) * b0.1) =
          max ((b0.1 : ℝ) ^ 2 * (d.1 / ζ - 1))
            ((b0.1 : ℝ) ^ 2 * (m.1 / b0.1)) := by
              congr 1
              · ring
              · field_simp [ne_of_gt hb]
      _ = (b0.1 : ℝ) ^ 2 * max (d.1 / ζ - 1) (m.1 / b0.1) :=
        (mul_max_of_nonneg _ _ (sq_nonneg (b0.1 : ℝ))).symm
  have hmaxLin :
      max (odds * (b0.1 : ℝ)) (m.1 : ℝ) = (b0.1 : ℝ) * ratio := by
    dsimp [odds, ratio, finiteSumDensityBatchRatio]
    calc
      max ((d.1 / ζ - 1) * (b0.1 : ℝ)) (m.1 : ℝ) =
          max ((b0.1 : ℝ) * (d.1 / ζ - 1))
            ((b0.1 : ℝ) * (m.1 / b0.1)) := by
              congr 1
              · ring
              · field_simp [ne_of_gt hb]
      _ = (b0.1 : ℝ) * max (d.1 / ζ - 1) (m.1 / b0.1) :=
        (mul_max_of_nonneg _ _ hb.le).symm
  have hSqrtSq :
      Real.sqrt (ω * max (odds * (b0.1 : ℝ) ^ 2) (m.1 * b0.1) / n.1) =
        b0.1 * Real.sqrt (ω * ratio / n.1) := by
    rw [hmaxSq]
    rw [show ω * ((b0.1 : ℝ) ^ 2 * ratio) / n.1 =
        (b0.1 : ℝ) ^ 2 * (ω * ratio / n.1) by ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ))]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have hSqrtLin :
      Real.sqrt ((1 + ω) * max (odds * (b0.1 : ℝ)) m.1 / n.1) =
        b0.1 * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) := by
    rw [hmaxLin]
    rw [show (1 + ω) * ((b0.1 : ℝ) * ratio) / n.1 =
        (b0.1 : ℝ) ^ 2 * ((1 + ω) * ratio / (n.1 * b0.1)) by
          field_simp [ne_of_gt hb, ne_of_gt hn] <;> ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ))]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  simp only [finiteSumNonconvexOracleScale, vrIterationBracket]
  change (m.1 : ℝ) + Δ / ε ^ 2 *
      (L * b0.1 + L * Real.sqrt (ω * max (odds * b0.1 ^ 2) (m.1 * b0.1) / n.1) +
        ℒ * Real.sqrt ((1 + ω) * max (odds * b0.1) m.1 / n.1)) = _
  rw [hSqrtSq, hSqrtLin]
  dsimp [ratio]
  ring

/-- Moving the positive batch-size factor through the square roots and maximum
turns Corollary D.2's printed oracle scale into `b⁰` times its iteration
factor. -/
theorem finite_sum_pl_oracle_scale_eq
    {d n m b0 : Count} (L ℒ ω μ p ζ logGap : ℝ)
    (hω : 0 ≤ ω) (hμ : 0 < μ) :
    finiteSumPLOracleScale L ℒ ω μ p ζ logGap d n m b0 =
      m.1 + b0.1 * max (1 / p)
        (vrIterationBracket L ℒ ω
          (finiteSumDensityBatchRatio d m b0 ζ) n b0 / μ) * logGap := by
  have hb : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  let odds : ℝ := d.1 / ζ - 1
  let ratio : ℝ := finiteSumDensityBatchRatio d m b0 ζ
  have hmaxSq :
      max (odds * (b0.1 : ℝ) ^ 2) ((m.1 : ℝ) * b0.1) =
        (b0.1 : ℝ) ^ 2 * ratio := by
    dsimp [odds, ratio, finiteSumDensityBatchRatio]
    calc
      max ((d.1 / ζ - 1) * (b0.1 : ℝ) ^ 2) ((m.1 : ℝ) * b0.1) =
          max ((b0.1 : ℝ) ^ 2 * (d.1 / ζ - 1))
            ((b0.1 : ℝ) ^ 2 * (m.1 / b0.1)) := by
              congr 1
              · ring
              · field_simp [ne_of_gt hb]
      _ = (b0.1 : ℝ) ^ 2 * max (d.1 / ζ - 1) (m.1 / b0.1) :=
        (mul_max_of_nonneg _ _ (sq_nonneg (b0.1 : ℝ))).symm
  have hmaxLin :
      max (odds * (b0.1 : ℝ)) (m.1 : ℝ) = (b0.1 : ℝ) * ratio := by
    dsimp [odds, ratio, finiteSumDensityBatchRatio]
    calc
      max ((d.1 / ζ - 1) * (b0.1 : ℝ)) (m.1 : ℝ) =
          max ((b0.1 : ℝ) * (d.1 / ζ - 1))
            ((b0.1 : ℝ) * (m.1 / b0.1)) := by
              congr 1
              · ring
              · field_simp [ne_of_gt hb]
      _ = (b0.1 : ℝ) * max (d.1 / ζ - 1) (m.1 / b0.1) :=
        (mul_max_of_nonneg _ _ hb.le).symm
  have hSqrtSq :
      Real.sqrt (ω * max (odds * (b0.1 : ℝ) ^ 2) (m.1 * b0.1) / n.1) =
        b0.1 * Real.sqrt (ω * ratio / n.1) := by
    rw [hmaxSq]
    rw [show ω * ((b0.1 : ℝ) ^ 2 * ratio) / n.1 =
        (b0.1 : ℝ) ^ 2 * (ω * ratio / n.1) by ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ))]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have hSqrtLin :
      Real.sqrt ((1 + ω) * max (odds * (b0.1 : ℝ)) m.1 / n.1) =
        b0.1 * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) := by
    rw [hmaxLin]
    rw [show (1 + ω) * ((b0.1 : ℝ) * ratio) / n.1 =
        (b0.1 : ℝ) ^ 2 * ((1 + ω) * ratio / (n.1 * b0.1)) by
          field_simp [ne_of_gt hb, ne_of_gt hn] <;> ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ))]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  simp only [finiteSumPLOracleScale, vrIterationBracket]
  change (m.1 : ℝ) + max (b0.1 / p)
      (L / μ * (b0.1 +
        Real.sqrt (ω * max (odds * b0.1 ^ 2) (m.1 * b0.1) / n.1)) +
       ℒ / μ * Real.sqrt
        ((1 + ω) * max (odds * b0.1) m.1 / n.1)) * logGap = _
  rw [hSqrtSq, hSqrtLin]
  dsimp [ratio]
  rw [show (b0.1 : ℝ) / p = b0.1 * (1 / p) by ring]
  rw [show L / μ * (b0.1 + b0.1 *
        Real.sqrt (ω * finiteSumDensityBatchRatio d m b0 ζ / n.1)) +
      ℒ / μ * (b0.1 * Real.sqrt ((1 + ω) *
        finiteSumDensityBatchRatio d m b0 ζ / (n.1 * b0.1))) =
      b0.1 * ((L * (1 + Real.sqrt
        (ω * finiteSumDensityBatchRatio d m b0 ζ / n.1)) +
        ℒ * Real.sqrt ((1 + ω) * finiteSumDensityBatchRatio d m b0 ζ /
          (n.1 * b0.1))) / μ) by
        field_simp [ne_of_gt hμ] <;> ring]
  rw [mul_max_of_nonneg _ _ hb.le]

/-- The density refresh choice in Corollaries D.3--D.4 bounds both exact
per-round counters by the source's displayed batch and density payloads. -/
theorem online_density_schedule_payload_bounds
    {d b b0 : Count} {p ζ : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hζ : 0 ≤ ζ)
    (hSchedule : p = onlineDensityBatchRefreshSchedule ζ d b b0) :
    0 < ζ ∧
      p * b.1 + 2 * (1 - p) * b0.1 ≤ 3 * b0.1 ∧
      p * d.1 + (1 - p) * ζ ≤ 2 * ζ := by
  have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
  have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hpDensity : p ≤ ζ / d.1 := by
    rw [hSchedule, onlineDensityBatchRefreshSchedule]
    exact min_le_left _ _
  have hpBatch : p ≤ (b0.1 : ℝ) / (b.1 + b0.1 : ℕ) := by
    rw [hSchedule, onlineDensityBatchRefreshSchedule]
    exact min_le_right _ _
  have hζpos : 0 < ζ := by
    have : 0 < ζ / d.1 := lt_of_lt_of_le hp hpDensity
    exact ((div_pos_iff.mp this).resolve_right (by
      intro hneg
      exact (not_lt_of_ge hd.le hneg.2).elim)).1
  have hpBatch' : p * ((b.1 : ℝ) + b0.1) ≤ b0.1 := by
    have hden : 0 < (b.1 : ℝ) + b0.1 := by positivity
    apply (le_div_iff₀ hden).mp
    simpa using hpBatch
  have hpB : p * (b.1 : ℝ) ≤ b0.1 := by
    have hpb0 : 0 ≤ p * (b0.1 : ℝ) := mul_nonneg hp.le hb0.le
    nlinarith
  have hOracle :
      p * b.1 + 2 * (1 - p) * b0.1 ≤ 3 * b0.1 := by
    have htail : 0 ≤ (1 - p) * (b0.1 : ℝ) :=
      mul_nonneg (sub_nonneg.mpr hp1) hb0.le
    have htailLe : (1 - p) * (b0.1 : ℝ) ≤ b0.1 := by nlinarith
    nlinarith
  have hpD : p * (d.1 : ℝ) ≤ ζ := (le_div_iff₀ hd).mp hpDensity
  have hCommTail : (1 - p) * ζ ≤ ζ := by
    have : 0 ≤ p * ζ := mul_nonneg hp.le hζ
    nlinarith
  exact ⟨hζpos, hOracle, by nlinarith⟩

/-- Exact odds identity behind the density/batch minimum in Corollaries
D.3--D.4.  This is the algebraic substitution made in the source proofs. -/
theorem online_density_schedule_odds_eq
    {d b b0 : Count} {p ζ : ℝ}
    (hp : 0 < p) (hSchedule : p = onlineDensityBatchRefreshSchedule ζ d b b0) :
    (1 - p) / p = max (d.1 / ζ - 1) ((b.1 : ℝ) / b0.1) := by
  have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
  have hb : 0 < (b.1 : ℝ) := by exact_mod_cast b.2
  have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hζ : 0 < ζ := by
    have hpDensity : p ≤ ζ / d.1 := by
      rw [hSchedule, onlineDensityBatchRefreshSchedule]
      exact min_le_left _ _
    have : 0 < ζ / d.1 := hp.trans_le hpDensity
    exact (div_pos_iff.mp this).resolve_right (by
      intro hneg
      exact (not_lt_of_ge hd.le hneg.2).elim) |>.1
  rw [hSchedule, onlineDensityBatchRefreshSchedule]
  by_cases h : ζ / d.1 ≤ (b0.1 : ℝ) / (b.1 + b0.1 : ℕ)
  · rw [min_eq_left h]
    have hright : (b.1 : ℝ) / b0.1 ≤ d.1 / ζ - 1 := by
      have hraw : ζ * ((b.1 : ℝ) + b0.1) ≤ b0.1 * d.1 := by
        have hcast : ζ / d.1 ≤ b0.1 / ((b.1 : ℝ) + b0.1) := by
          simpa using h
        have := (div_le_div_iff₀ hd
          (by positivity : 0 < (b.1 : ℝ) + b0.1)).1 hcast
        nlinarith
      apply (le_sub_iff_add_le).2
      rw [show (b.1 : ℝ) / b0.1 + 1 =
        ((b.1 : ℝ) + b0.1) / b0.1 by field_simp]
      rw [div_le_div_iff₀ hb0 hζ]
      nlinarith
    rw [max_eq_left hright]
    field_simp [ne_of_gt hζ, ne_of_gt hd]
    <;> ring
  · have h' : (b0.1 : ℝ) / (b.1 + b0.1 : ℕ) ≤ ζ / d.1 :=
      le_of_not_ge h
    rw [min_eq_right h']
    have hleft : d.1 / ζ - 1 ≤ (b.1 : ℝ) / b0.1 := by
      have hraw : b0.1 * d.1 ≤ ζ * ((b.1 : ℝ) + b0.1) := by
        have hcast : b0.1 / ((b.1 : ℝ) + b0.1) ≤ ζ / d.1 := by
          simpa using h'
        have := (div_le_div_iff₀
          (by positivity : 0 < (b.1 : ℝ) + b0.1) hd).1 hcast
        nlinarith
      apply (sub_le_iff_le_add).2
      rw [show (b.1 : ℝ) / b0.1 + 1 =
        ((b.1 : ℝ) + b0.1) / b0.1 by field_simp]
      rw [div_le_div_iff₀ hζ hb0]
      nlinarith
    rw [max_eq_right hleft]
    rw [Nat.cast_add]
    change (1 - b0.1 / ((b.1 : ℝ) + b0.1)) /
      (b0.1 / ((b.1 : ℝ) + b0.1)) = (b.1 : ℝ) / b0.1
    field_simp [ne_of_gt hb0, ne_of_gt (add_pos hb hb0)]
    <;> ring

/-- With the density refresh schedule, the reciprocal of the executable
Eq. (40) stepsize has the printed Corollary D.3 bracket as its asymptotic
scale.  The only asymptotic input is the source batch relation. -/
theorem online_density_canonical_inverse_step_bigO
    {d n b0 : Count} {batch : Accuracy → Count} {p : Accuracy → ℝ}
    {L ℒ ω ζ variance : ℝ}
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (hL : 0 < L) (hℒ : 0 ≤ ℒ) (hω : 0 ≤ ω)
    (hvariance : 0 ≤ variance)
    (hBatch : AccuracyBigO (fun ε => ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2)))
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule ζ d (batch ε) b0) :
    AccuracyBigO
      (fun ε =>
        ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 :
          PositiveStepsize) : ℝ)⁻¹)
      (fun ε => vrIterationBracket L ℒ ω
        (onlineDensityBatchRatio d n b0 ζ variance ((ε : ℝ) ^ 2)) n b0) := by
  unfold AccuracyBigO at hBatch ⊢
  rw [Asymptotics.isBigO_iff'] at hBatch ⊢
  rcases hBatch with ⟨C, hC, hEventually⟩
  let M : ℝ := max 1 C
  let K : ℝ := 1 / L + Real.sqrt M
  have hM : 1 ≤ M := le_max_left _ _
  have hCM : C ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hEventually] with ε hB
  let s : ℝ := variance / (n.1 * (ε : ℝ) ^ 2)
  let ratio : ℝ := onlineDensityBatchRatio d n b0 ζ variance ((ε : ℝ) ^ 2)
  let coeff : ℝ := ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1
  have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hBpos : 0 < ((batch ε).1 : ℝ) := by exact_mod_cast (batch ε).2
  have hs : 0 < s := by
    have hBle : ((batch ε).1 : ℝ) ≤ C * s := by
      simpa [Real.norm_eq_abs, abs_of_pos hBpos, abs_of_nonneg hvariance,
        s] using hB
    by_contra hs0
    have : C * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt hs0)
    linarith
  have hratio : 0 < ratio := by
    have hsdiv : 0 < variance / (n.1 * b0.1 * (ε : ℝ) ^ 2) := by
      have : s / b0.1 = variance / (n.1 * b0.1 * (ε : ℝ) ^ 2) := by
        dsimp [s]
        field_simp [ne_of_gt hb0, ne_of_gt hn, ne_of_gt ε.property]
      rw [← this]
      exact div_pos hs hb0
    dsimp [ratio, onlineDensityBatchRatio]
    exact hsdiv.trans_le (le_max_right _ _)
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    exact add_nonneg (mul_nonneg hω (sq_nonneg L))
      (div_nonneg (mul_nonneg (by linarith) (sq_nonneg ℒ)) hb0.le)
  have hOdds : (1 - p ε) / p ε ≤ M * ratio := by
    rw [online_density_schedule_odds_eq (hp ε).1 (hSchedule ε)]
    apply max_le
    · calc
        d.1 / ζ - 1 ≤ ratio := by
          dsimp [ratio, onlineDensityBatchRatio]
          exact le_max_left _ _
        _ ≤ M * ratio := by nlinarith
    · have hBle : ((batch ε).1 : ℝ) ≤ C * s := by
        simpa [Real.norm_eq_abs, abs_of_pos hBpos,
          abs_of_nonneg hvariance, abs_of_pos hs, s] using hB
      calc
        ((batch ε).1 : ℝ) / b0.1 ≤ C * s / b0.1 := by gcongr
        _ ≤ M * ratio := by
          have hsratio : s / b0.1 ≤ ratio := by
            dsimp [s, ratio, onlineDensityBatchRatio]
            convert le_max_right (d.1 / ζ - 1)
              (variance / (n.1 * b0.1 * (ε : ℝ) ^ 2)) using 1
            field_simp [ne_of_gt hb0, ne_of_gt hn, ne_of_gt ε.property]
          have hmul := mul_le_mul hCM hsratio (div_pos hs hb0).le hM0
          calc
            C * s / b0.1 = C * (s / b0.1) := by ring
            _ ≤ M * ratio := hmul
  have hq : (1 - p ε) / (p ε * n.1) * coeff ≤
      M * (ratio / n.1 * coeff) := by
    have hp0 := (hp ε).1
    rw [show (1 - p ε) / (p ε * n.1) * coeff =
      (((1 - p ε) / p ε) / n.1) * coeff by
        field_simp [ne_of_gt hp0, ne_of_gt hn] <;> ring]
    calc
      ((1 - p ε) / p ε / n.1) * coeff ≤
          ((M * ratio) / n.1) * coeff := by gcongr
      _ = M * (ratio / n.1 * coeff) := by ring
  have hsqrtTotal : Real.sqrt (ratio / n.1 * coeff) ≤
      L * Real.sqrt (ω * ratio / n.1) +
        ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) := by
    let a : ℝ := L * Real.sqrt (ω * ratio / n.1)
    let b : ℝ := ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1))
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hb' : 0 ≤ b := by dsimp [b]; positivity
    have hsq : ratio / n.1 * coeff = a ^ 2 + b ^ 2 := by
      dsimp [a, b, coeff]
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ω * ratio / n.1),
        mul_pow, Real.sq_sqrt (by positivity :
          0 ≤ (1 + ω) * ratio / (n.1 * b0.1))]
      field_simp [ne_of_gt hn, ne_of_gt hb0]
      <;> ring
    rw [hsq]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · change a ^ 2 + b ^ 2 ≤ (a + b) ^ 2
      nlinarith [mul_nonneg ha hb']
  have hsqrtQ : Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
      Real.sqrt M * Real.sqrt (ratio / n.1 * coeff) := by
    calc
      Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
          Real.sqrt (M * (ratio / n.1 * coeff)) := Real.sqrt_le_sqrt hq
      _ = Real.sqrt M * Real.sqrt (ratio / n.1 * coeff) := by
        rw [Real.sqrt_mul hM0]
  have hD : L + Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
      Real.sqrt M * vrIterationBracket L ℒ ω ratio n b0 := by
    have hsqrtM : 1 ≤ Real.sqrt M := by simpa using hM
    dsimp [vrIterationBracket]
    calc
      L + Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
          L + Real.sqrt M * Real.sqrt (ratio / n.1 * coeff) := by gcongr
      _ ≤ Real.sqrt M *
          (L + (L * Real.sqrt (ω * ratio / n.1) +
            ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)))) := by
        have := mul_le_mul_of_nonneg_left hsqrtTotal (Real.sqrt_nonneg M)
        nlinarith
      _ = Real.sqrt M *
          (L * (1 + Real.sqrt (ω * ratio / n.1)) +
            ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1))) := by ring
  have hbracket : 0 < vrIterationBracket L ℒ ω ratio n b0 := by
    dsimp [vrIterationBracket]
    positivity
  have hInv :
      ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 :
        PositiveStepsize) : ℝ)⁻¹ ≤
        K * vrIterationBracket L ℒ ω ratio n b0 := by
    change (1 / max 1
      (L + Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff)))⁻¹ ≤ _
    rw [inv_div, div_one]
    apply max_le
    · dsimp [K]
      have hOne : 1 ≤ (1 / L) *
          vrIterationBracket L ℒ ω ratio n b0 := by
        have hLb : L ≤ vrIterationBracket L ℒ ω ratio n b0 := by
          dsimp [vrIterationBracket]
          nlinarith [mul_nonneg hL.le (Real.sqrt_nonneg (ω * ratio / n.1)),
            mul_nonneg hℒ (Real.sqrt_nonneg ((1 + ω) * ratio / (n.1 * b0.1)))]
        rwa [one_div_mul_eq_div, one_le_div hL]
      have hnonneg := mul_nonneg (Real.sqrt_nonneg M) hbracket.le
      nlinarith
    · dsimp [K]
      exact hD.trans (by
        have hnonneg := mul_nonneg (one_div_nonneg.mpr hL.le) hbracket.le
        nlinarith)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
    (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0).property)]
  rw [Real.norm_eq_abs, abs_of_pos hbracket]
  exact hInv

theorem eventually_one_le_positive_inverse_square
    {a : ℝ} (ha : 0 < a) :
    ∀ᶠ ε : Accuracy in accuracyToZero, 1 ≤ a / (ε : ℝ) ^ 2 := by
  rw [accuracyToZero]
  change {ε : Accuracy | 1 ≤ a / (ε : ℝ) ^ 2} ∈
    Filter.comap (fun ε : Accuracy => ((ε : ℝ)⁻¹)) (Filter.atTop : Filter ℝ)
  rw [Filter.mem_comap]
  refine ⟨Set.Ici (max 1 (1 / a)), Filter.eventually_atTop.2
    ⟨max 1 (1 / a), fun _ h => h⟩, ?_⟩
  intro ε hε
  change max 1 (1 / a) ≤ (ε : ℝ)⁻¹ at hε
  have hone : 1 ≤ (ε : ℝ)⁻¹ := (le_max_left _ _).trans hε
  have haone : 1 ≤ a * (ε : ℝ)⁻¹ := by
    have := (le_max_right (1 : ℝ) (1 / a)).trans hε
    rw [div_le_iff₀ ha] at this
    simpa [mul_comm] using this
  have hinv : 0 < (ε : ℝ)⁻¹ := inv_pos.mpr ε.property
  have : 1 ≤ a * (ε : ℝ)⁻¹ * (ε : ℝ)⁻¹ := by
    nlinarith
  change 1 ≤ a / (ε : ℝ) ^ 2
  convert this using 1 <;> field_simp [ne_of_gt ε.property]

/-- The additive ceiling term in the executable D.3 schedule is absorbed by
the positive-gap printed iteration scale. -/
theorem online_nonconvex_supplied_scale_bigO_canonical
    {d n b0 : Count} {batch : Accuracy → Count} {p : Accuracy → ℝ}
    {L ℒ ω ζ variance Δ : ℝ}
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (hL : 0 < L) (hℒ : 0 ≤ ℒ) (hω : 0 ≤ ω)
    (hvariance : 0 ≤ variance) (hΔ : 0 < Δ)
    (hBatch : AccuracyBigO (fun ε => ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2)))
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule ζ d (batch ε) b0) :
    AccuracyBigO
      (fun ε => 1 + 4 * Δ /
        ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ) *
          (ε : ℝ) ^ 2))
      (fun ε => Δ / (ε : ℝ) ^ 2 *
        vrIterationBracket L ℒ ω
          (onlineDensityBatchRatio d n b0 ζ variance ((ε : ℝ) ^ 2)) n b0) := by
  have hInv := online_density_canonical_inverse_step_bigO hp hL hℒ hω
    hvariance hBatch hSchedule
  unfold AccuracyBigO at hInv ⊢
  rw [Asymptotics.isBigO_iff'] at hInv ⊢
  rcases hInv with ⟨C, hC, hInv⟩
  refine ⟨1 + 4 * C, by positivity, ?_⟩
  filter_upwards [hInv,
    eventually_one_le_positive_inverse_square (mul_pos hΔ hL)] with ε hInvε hone
  let bracket := vrIterationBracket L ℒ ω
    (onlineDensityBatchRatio d n b0 ζ variance ((ε : ℝ) ^ 2)) n b0
  have hbracket : 0 < bracket := by dsimp [bracket, vrIterationBracket]; positivity
  have hInv' :
      ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ))⁻¹ ≤
        C * bracket := by
    simpa [norm_inv, Real.norm_eq_abs,
      abs_of_pos (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0).property,
      abs_of_pos hbracket, bracket] using hInvε
  have htargetPos : 0 < Δ / (ε : ℝ) ^ 2 * bracket :=
    mul_pos (div_pos hΔ (sq_pos_of_pos ε.property)) hbracket
  have honeTarget : 1 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by
    have hLb : L ≤ bracket := by
      dsimp [bracket, vrIterationBracket]
      have hfirst : 0 ≤ L * Real.sqrt
          (ω * onlineDensityBatchRatio d n b0 ζ variance ((ε : ℝ) ^ 2) / n.1) :=
        mul_nonneg hL.le (Real.sqrt_nonneg _)
      have hsecond : 0 ≤ ℒ * Real.sqrt
          ((1 + ω) * onlineDensityBatchRatio d n b0 ζ variance ((ε : ℝ) ^ 2) /
            (n.1 * b0.1)) := mul_nonneg hℒ (Real.sqrt_nonneg _)
      nlinarith
    have hscale := mul_le_mul_of_nonneg_left hLb
      (div_nonneg hΔ.le (sq_nonneg (ε : ℝ)))
    exact hone.trans (by
      convert hscale using 1 <;> ring)
  have hactual : 0 ≤ 1 + 4 * Δ /
      ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ) *
        (ε : ℝ) ^ 2) := by
    have hdenom : 0 ≤
        (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ) *
          (ε : ℝ) ^ 2 :=
      mul_nonneg (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0).property.le
        (sq_nonneg _)
    have hquot : 0 ≤ 4 * Δ /
        ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ) *
          (ε : ℝ) ^ 2) := div_nonneg (mul_nonneg (by norm_num) hΔ.le) hdenom
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg hactual,
    Real.norm_eq_abs, abs_of_pos htargetPos]
  have hterm : 4 * Δ /
      ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ) *
        (ε : ℝ) ^ 2) ≤
      4 * C * (Δ / (ε : ℝ) ^ 2 * bracket) := by
    have hfactor0 : 0 ≤ 4 * (Δ / (ε : ℝ) ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hInv' hfactor0
    convert hmul using 1 <;>
      field_simp [ne_of_gt
        (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0).property,
        ne_of_gt ε.property] <;> ring
  nlinarith

/-- Linear-accuracy analogue of `online_density_canonical_inverse_step_bigO`,
used by the PŁ density corollary where Eq. (49) scales as `1 / (μ ε)`. -/
theorem online_density_canonical_inverse_step_bigO_linear
    {d n b0 : Count} {batch : Accuracy → Count} {p : Accuracy → ℝ}
    {L ℒ ω ζ variance μ : ℝ}
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (hL : 0 < L) (hℒ : 0 ≤ ℒ) (hω : 0 ≤ ω)
    (hvariance : 0 ≤ variance) (hμ : 0 < μ)
    (hBatch : AccuracyBigO (fun ε => ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * μ * (ε : ℝ))))
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule ζ d (batch ε) b0) :
    AccuracyBigO
      (fun ε =>
        ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 :
          PositiveStepsize) : ℝ)⁻¹)
      (fun ε => vrIterationBracket L ℒ ω
        (onlineDensityBatchRatio d n b0 ζ variance (μ * (ε : ℝ))) n b0) := by
  unfold AccuracyBigO at hBatch ⊢
  rw [Asymptotics.isBigO_iff'] at hBatch ⊢
  rcases hBatch with ⟨C, hC, hEventually⟩
  let M : ℝ := max 1 C
  let K : ℝ := 1 / L + Real.sqrt M
  have hM : 1 ≤ M := le_max_left _ _
  have hCM : C ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hEventually] with ε hB
  let s : ℝ := variance / (n.1 * μ * (ε : ℝ))
  let ratio : ℝ := onlineDensityBatchRatio d n b0 ζ variance (μ * (ε : ℝ))
  let coeff : ℝ := ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1
  have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hBpos : 0 < ((batch ε).1 : ℝ) := by exact_mod_cast (batch ε).2
  have hs : 0 < s := by
    have hBle : ((batch ε).1 : ℝ) ≤ C * s := by
      simpa [Real.norm_eq_abs, abs_of_pos hBpos, abs_of_nonneg hvariance,
        abs_of_pos hμ, abs_of_pos ε.property, s] using hB
    by_contra hs0
    have : C * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt hs0)
    linarith
  have hratio : 0 < ratio := by
    have hsdiv : 0 < variance / (n.1 * b0.1 * (μ * (ε : ℝ))) := by
      have : s / b0.1 = variance / (n.1 * b0.1 * (μ * (ε : ℝ))) := by
        dsimp [s]
        field_simp [ne_of_gt hb0, ne_of_gt hn, ne_of_gt hμ,
          ne_of_gt ε.property]
      rw [← this]
      exact div_pos hs hb0
    dsimp [ratio, onlineDensityBatchRatio]
    exact hsdiv.trans_le (le_max_right _ _)
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    exact add_nonneg (mul_nonneg hω (sq_nonneg L))
      (div_nonneg (mul_nonneg (by linarith) (sq_nonneg ℒ)) hb0.le)
  have hOdds : (1 - p ε) / p ε ≤ M * ratio := by
    rw [online_density_schedule_odds_eq (hp ε).1 (hSchedule ε)]
    apply max_le
    · calc
        d.1 / ζ - 1 ≤ ratio := by
          dsimp [ratio, onlineDensityBatchRatio]
          exact le_max_left _ _
        _ ≤ M * ratio := by nlinarith
    · have hBle : ((batch ε).1 : ℝ) ≤ C * s := by
        simpa [Real.norm_eq_abs, abs_of_pos hBpos,
          abs_of_nonneg hvariance, abs_of_pos hμ, abs_of_pos ε.property,
          abs_of_pos hs, s] using hB
      calc
        ((batch ε).1 : ℝ) / b0.1 ≤ C * s / b0.1 := by gcongr
        _ ≤ M * ratio := by
          have hsratio : s / b0.1 ≤ ratio := by
            dsimp [s, ratio, onlineDensityBatchRatio]
            convert le_max_right (d.1 / ζ - 1)
              (variance / (n.1 * b0.1 * (μ * (ε : ℝ)))) using 1
            field_simp [ne_of_gt hb0, ne_of_gt hn, ne_of_gt hμ,
              ne_of_gt ε.property]
          have hmul := mul_le_mul hCM hsratio (div_pos hs hb0).le hM0
          calc
            C * s / b0.1 = C * (s / b0.1) := by ring
            _ ≤ M * ratio := hmul
  have hq : (1 - p ε) / (p ε * n.1) * coeff ≤
      M * (ratio / n.1 * coeff) := by
    have hp0 := (hp ε).1
    rw [show (1 - p ε) / (p ε * n.1) * coeff =
      (((1 - p ε) / p ε) / n.1) * coeff by
        field_simp [ne_of_gt hp0, ne_of_gt hn] <;> ring]
    calc
      ((1 - p ε) / p ε / n.1) * coeff ≤
          ((M * ratio) / n.1) * coeff := by gcongr
      _ = M * (ratio / n.1 * coeff) := by ring
  have hsqrtTotal : Real.sqrt (ratio / n.1 * coeff) ≤
      L * Real.sqrt (ω * ratio / n.1) +
        ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) := by
    let a : ℝ := L * Real.sqrt (ω * ratio / n.1)
    let c : ℝ := ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1))
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hsq : ratio / n.1 * coeff = a ^ 2 + c ^ 2 := by
      dsimp [a, c, coeff]
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ ω * ratio / n.1),
        mul_pow, Real.sq_sqrt (by positivity :
          0 ≤ (1 + ω) * ratio / (n.1 * b0.1))]
      field_simp [ne_of_gt hn, ne_of_gt hb0]
      <;> ring
    rw [hsq]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · change a ^ 2 + c ^ 2 ≤ (a + c) ^ 2
      nlinarith [mul_nonneg ha hc]
  have hsqrtQ : Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
      Real.sqrt M * Real.sqrt (ratio / n.1 * coeff) := by
    calc
      Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
          Real.sqrt (M * (ratio / n.1 * coeff)) := Real.sqrt_le_sqrt hq
      _ = Real.sqrt M * Real.sqrt (ratio / n.1 * coeff) := by
        rw [Real.sqrt_mul hM0]
  have hD : L + Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
      Real.sqrt M * vrIterationBracket L ℒ ω ratio n b0 := by
    have hsqrtM : 1 ≤ Real.sqrt M := by simpa using hM
    dsimp [vrIterationBracket]
    calc
      L + Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff) ≤
          L + Real.sqrt M * Real.sqrt (ratio / n.1 * coeff) := by gcongr
      _ ≤ Real.sqrt M *
          (L + (L * Real.sqrt (ω * ratio / n.1) +
            ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)))) := by
        have := mul_le_mul_of_nonneg_left hsqrtTotal (Real.sqrt_nonneg M)
        nlinarith
      _ = Real.sqrt M *
          (L * (1 + Real.sqrt (ω * ratio / n.1)) +
            ℒ * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1))) := by ring
  have hbracket : 0 < vrIterationBracket L ℒ ω ratio n b0 := by
    dsimp [vrIterationBracket]
    positivity
  have hInv :
      ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 :
        PositiveStepsize) : ℝ)⁻¹ ≤
        K * vrIterationBracket L ℒ ω ratio n b0 := by
    change (1 / max 1
      (L + Real.sqrt ((1 - p ε) / (p ε * n.1) * coeff)))⁻¹ ≤ _
    rw [inv_div, div_one]
    apply max_le
    · dsimp [K]
      have hOne : 1 ≤ (1 / L) *
          vrIterationBracket L ℒ ω ratio n b0 := by
        have hLb : L ≤ vrIterationBracket L ℒ ω ratio n b0 := by
          dsimp [vrIterationBracket]
          nlinarith [mul_nonneg hL.le (Real.sqrt_nonneg (ω * ratio / n.1)),
            mul_nonneg hℒ (Real.sqrt_nonneg ((1 + ω) * ratio / (n.1 * b0.1)))]
        rwa [one_div_mul_eq_div, one_le_div hL]
      have hnonneg := mul_nonneg (Real.sqrt_nonneg M) hbracket.le
      nlinarith
    · dsimp [K]
      exact hD.trans (by
        have hnonneg := mul_nonneg (one_div_nonneg.mpr hL.le) hbracket.le
        nlinarith)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
    (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0).property)]
  rw [Real.norm_eq_abs, abs_of_pos hbracket]
  exact hInv

/-- The reciprocal PŁ contraction of the executable Eq. (48) choice is
controlled by the exact density-normalized factor printed in Corollary D.4. -/
theorem online_pl_canonical_inverse_contraction_bigO
    {d n b0 : Count} {batch : Accuracy → Count} {p : Accuracy → ℝ}
    {L ℒ ω ζ variance : ℝ} {μ : PositivePLParameter}
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (hL : 0 < L) (hℒ : 0 ≤ ℒ) (hω : 0 ≤ ω)
    (hvariance : 0 ≤ variance)
    (hBatch : AccuracyBigO (fun ε => ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * (μ : ℝ) * (ε : ℝ))))
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule ζ d (batch ε) b0) :
    AccuracyBigO
      (fun ε => 1 / ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)))
      (fun ε => max (1 / p ε)
        (vrIterationBracket L ℒ ω
          (onlineDensityBatchRatio d n b0 ζ variance ((μ : ℝ) * (ε : ℝ))) n b0 /
          (μ : ℝ))) := by
  have hInv := online_density_canonical_inverse_step_bigO_linear hp hL hℒ hω
    hvariance μ.property hBatch hSchedule
  unfold AccuracyBigO at hInv ⊢
  rw [Asymptotics.isBigO_iff'] at hInv ⊢
  rcases hInv with ⟨C, hC, hInv⟩
  refine ⟨2 + 2 * C, by positivity, ?_⟩
  filter_upwards [hInv] with ε hInvε
  let ratio := onlineDensityBatchRatio d n b0 ζ variance ((μ : ℝ) * (ε : ℝ))
  let B := vrIterationBracket L ℒ ω ratio n b0
  let q := (1 - p ε) / (p ε * n.1) *
    (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)
  have hp0 := (hp ε).1
  have hB : 0 < B := by dsimp [B, vrIterationBracket]; positivity
  have hInv' :
      ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ))⁻¹ ≤ C * B := by
    simpa [ratio, B, norm_inv, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr
        (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0).property),
      abs_of_pos (onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0).property,
      abs_of_pos hB] using hInvε
  have hD2 : L + Real.sqrt (2 * q) ≤
      2 * ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ))⁻¹ := by
    have hq : 0 ≤ q := by
      dsimp [q]
      exact mul_nonneg
        (div_nonneg (sub_nonneg.mpr (hp ε).2)
          (mul_nonneg hp0.le (by positivity)))
        (add_nonneg (mul_nonneg hω (sq_nonneg L))
          (div_nonneg (mul_nonneg (by linarith) (sq_nonneg ℒ)) (by positivity)))
    have hsqrt : Real.sqrt (2 * q) ≤ 2 * Real.sqrt q := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
      have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
      exact mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg q)
    have hbase : max 1 (L + Real.sqrt q) =
        ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ))⁻¹ := by
      change max 1 (L + Real.sqrt q) = (1 / max 1 (L + Real.sqrt q))⁻¹
      rw [inv_div, div_one]
    rw [← hbase]
    have hLmax : L ≤ max 1 (L + Real.sqrt q) :=
      le_trans (by linarith [Real.sqrt_nonneg q]) (le_max_right _ _)
    have hsqrtMax : Real.sqrt q ≤ max 1 (L + Real.sqrt q) :=
      le_trans (by linarith [hL]) (le_max_right _ _)
    have hsumMax : L + Real.sqrt q ≤ max 1 (L + Real.sqrt q) :=
      le_max_right _ _
    calc
      L + Real.sqrt (2 * q) ≤ L + 2 * Real.sqrt q := by gcongr
      _ ≤ 2 * max 1 (L + Real.sqrt q) := by nlinarith
  have hActual : 1 / ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)) ≤
      2 * (1 / p ε) + 2 * C * (B / (μ : ℝ)) := by
    simp only [onlinePLDensityCanonicalStepsize]
    change 1 / ((1 / max (2 * (μ : ℝ) / p ε)
      (max 1 (L + Real.sqrt ((2 * (1 - p ε)) / (p ε * n.1) *
        (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1))))) * (μ : ℝ)) ≤ _
    rw [show (2 * (1 - p ε)) / (p ε * n.1) *
        (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1) = 2 * q by
      dsimp [q]
      field_simp [ne_of_gt hp0] <;> ring]
    have hμ := μ.property
    have hMpos : 0 < max (2 * (μ : ℝ) / p ε)
        (max 1 (L + Real.sqrt (2 * q))) :=
      lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans (le_max_right _ _))
    rw [show 1 / ((1 / max (2 * (μ : ℝ) / p ε)
        (max 1 (L + Real.sqrt (2 * q)))) * (μ : ℝ)) =
        max (2 * (μ : ℝ) / p ε) (max 1 (L + Real.sqrt (2 * q))) /
          (μ : ℝ) by
      field_simp [ne_of_gt hMpos, ne_of_gt hμ]]
    have hfirst : (2 * (μ : ℝ) / p ε) / (μ : ℝ) = 2 * (1 / p ε) := by
      field_simp [ne_of_gt hp0, ne_of_gt hμ]
    have hsecond : max 1 (L + Real.sqrt (2 * q)) / (μ : ℝ) ≤
        2 * C * (B / (μ : ℝ)) := by
      have hmax : max 1 (L + Real.sqrt (2 * q)) ≤
          2 * ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ))⁻¹ := by
        apply max_le
        · have hInvOne : 1 ≤
              ((onlineDensityCanonicalStepsize L ℒ (p ε) ω n b0 : ℝ))⁻¹ := by
            change 1 ≤ (1 / max 1 (L + Real.sqrt q))⁻¹
            rw [inv_div, div_one]
            exact le_max_left _ _
          nlinarith
        · exact hD2
      have := div_le_div_of_nonneg_right (hmax.trans (mul_le_mul_of_nonneg_left hInv' (by norm_num))) μ.property.le
      convert this using 1 <;> ring
    rw [← max_div_div_right μ.property.le, hfirst]
    have hleft0 : 0 ≤ 2 * (1 / p ε) := by
      exact mul_nonneg (by norm_num) (one_div_nonneg.mpr hp0.le)
    have hright0 : 0 ≤ 2 * C * (B / (μ : ℝ)) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hC.le)
        (div_nonneg hB.le μ.property.le)
    exact max_le_iff.mpr ⟨le_add_of_nonneg_right hright0,
      hsecond.trans (le_add_of_nonneg_left hleft0)⟩
  have hTarget : 0 < max (1 / p ε) (B / (μ : ℝ)) :=
    (div_pos zero_lt_one hp0).trans_le (le_max_left _ _)
  have hActualPos : 0 < 1 /
      ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)) :=
    one_div_pos.mpr (mul_pos
      (onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0).property μ.property)
  rw [Real.norm_eq_abs, abs_of_pos hActualPos, Real.norm_eq_abs, abs_of_pos hTarget]
  calc
    1 / ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)) ≤
        2 * (1 / p ε) + 2 * C * (B / (μ : ℝ)) := hActual
    _ ≤ (2 + 2 * C) * max (1 / p ε) (B / (μ : ℝ)) := by
      have hC0 := hC.le
      have hleft := le_max_left (1 / p ε) (B / (μ : ℝ))
      have hright := le_max_right (1 / p ε) (B / (μ : ℝ))
      nlinarith

/-- The additive ceiling and `log 2` shift in the executable PŁ horizon are
absorbed by the positive-gap Corollary D.4 factor. -/
theorem online_pl_supplied_scale_bigO_canonical
    {d n b0 : Count} {batch : Accuracy → Count} {p : Accuracy → ℝ}
    {L ℒ ω ζ variance Δ : ℝ} {μ : PositivePLParameter}
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (hL : 0 < L) (hℒ : 0 ≤ ℒ) (hω : 0 ≤ ω)
    (hvariance : 0 ≤ variance) (hΔ : 0 < Δ)
    (hBatch : AccuracyBigO (fun ε => ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * (μ : ℝ) * (ε : ℝ))))
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule ζ d (batch ε) b0) :
    AccuracyBigO
      (fun ε => 1 + max 0
        (Real.log (2 * Δ / (ε : ℝ)) /
          ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ))))
      (fun ε => max (1 / p ε)
        (vrIterationBracket L ℒ ω
          (onlineDensityBatchRatio d n b0 ζ variance ((μ : ℝ) * (ε : ℝ))) n b0 /
          (μ : ℝ)) * Real.log (Δ / (ε : ℝ))) := by
  have hInv := online_pl_canonical_inverse_contraction_bigO hp hL hℒ hω
    hvariance hBatch hSchedule
  unfold AccuracyBigO at hInv ⊢
  rw [Asymptotics.isBigO_iff'] at hInv ⊢
  rcases hInv with ⟨C, hC, hInv⟩
  refine ⟨1 + C * (Real.log 2 + 1), by positivity, ?_⟩
  filter_upwards [hInv, eventually_one_le_log_gap_div_accuracy hΔ] with ε hInvε hlog
  let factor := max (1 / p ε)
    (vrIterationBracket L ℒ ω
      (onlineDensityBatchRatio d n b0 ζ variance ((μ : ℝ) * (ε : ℝ))) n b0 /
      (μ : ℝ))
  have hfactor : 0 < factor :=
    (div_pos zero_lt_one (hp ε).1).trans_le (le_max_left _ _)
  have hInv' : 1 /
      ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)) ≤
      C * factor := by
    have hpos : 0 < 1 /
        ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)) :=
      one_div_pos.mpr (mul_pos
        (onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0).property μ.property)
    rw [Real.norm_eq_abs, abs_of_pos hpos, Real.norm_eq_abs,
      abs_of_pos hfactor] at hInvε
    exact hInvε
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogShift : Real.log (2 * Δ / (ε : ℝ)) =
      Real.log 2 + Real.log (Δ / (ε : ℝ)) := by
    rw [show 2 * Δ / (ε : ℝ) = 2 * (Δ / (ε : ℝ)) by ring,
      Real.log_mul (by norm_num) (ne_of_gt (div_pos hΔ ε.property))]
  have htarget : 0 < factor * Real.log (Δ / (ε : ℝ)) :=
    mul_pos hfactor (lt_of_lt_of_le zero_lt_one hlog)
  have hactual : 0 ≤ 1 + max 0
      (Real.log (2 * Δ / (ε : ℝ)) /
        ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ))) :=
    add_nonneg (by norm_num) (le_max_left _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg hactual,
    Real.norm_eq_abs, abs_of_pos htarget]
  rw [hlogShift, max_eq_right (div_nonneg (add_nonneg hlogTwo (by linarith))
    (mul_nonneg
      (onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0).property.le
      μ.property.le))]
  have hterm : (Real.log 2 + Real.log (Δ / (ε : ℝ))) /
      ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)) ≤
      C * (Real.log 2 + 1) *
        (factor * Real.log (Δ / (ε : ℝ))) := by
    have hshiftBound : Real.log 2 + Real.log (Δ / (ε : ℝ)) ≤
        (Real.log 2 + 1) * Real.log (Δ / (ε : ℝ)) := by
      nlinarith [mul_nonneg hlogTwo (sub_nonneg.mpr hlog)]
    have hpos : 0 ≤ 1 /
        ((onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0 : ℝ) * (μ : ℝ)) :=
      (one_div_pos.mpr (mul_pos
        (onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0).property
        μ.property)).le
    have hshiftTargetNonneg : 0 ≤
        (Real.log 2 + 1) * Real.log (Δ / (ε : ℝ)) :=
      mul_nonneg (by linarith) (by linarith)
    have hmul := mul_le_mul hshiftBound hInv' hpos hshiftTargetNonneg
    convert hmul using 1 <;>
      field_simp [ne_of_gt
        (onlinePLDensityCanonicalStepsize L ℒ (p ε) ω μ n b0).property,
        ne_of_gt μ.property] <;> ring
  have hone : 1 ≤ factor * Real.log (Δ / (ε : ℝ)) := by
    have hpInv : 1 ≤ 1 / p ε :=
      (le_div_iff₀ (hp ε).1).2 (by simpa using (hp ε).2)
    exact one_le_mul_of_one_le_of_one_le (hpInv.trans (le_max_left _ _)) hlog
  nlinarith

/-- The printed D.3 oracle expression is the variance initialization plus
`b⁰` times the density-normalized iteration bracket. -/
theorem online_nonconvex_oracle_scale_eq
    {d n b0 : Count} (Δ L ℒ ω ζ variance ε : ℝ) (hω : 0 ≤ ω) :
    onlineNonconvexOracleScale Δ L ℒ ω ζ variance ε d n b0 =
      variance / (n.1 * ε ^ 2) +
        Δ / ε ^ 2 *
          (b0.1 * vrIterationBracket L ℒ ω
            (onlineDensityBatchRatio d n b0 ζ variance (ε ^ 2)) n b0) := by
  have hb : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  let odds : ℝ := d.1 / ζ - 1
  let v : ℝ := variance / (n.1 * ε ^ 2)
  let ratio : ℝ := onlineDensityBatchRatio d n b0 ζ variance (ε ^ 2)
  have hmax : max (odds * (b0.1 : ℝ)) v = (b0.1 : ℝ) * ratio := by
    dsimp [odds, v, ratio, onlineDensityBatchRatio]
    calc
      max ((d.1 / ζ - 1) * (b0.1 : ℝ))
          (variance / (n.1 * ε ^ 2)) =
        max ((b0.1 : ℝ) * (d.1 / ζ - 1))
          ((b0.1 : ℝ) *
            (variance / (n.1 * b0.1 * ε ^ 2))) := by
              congr 1
              · ring
              · field_simp [ne_of_gt hb, ne_of_gt hn] <;> ring
      _ = (b0.1 : ℝ) * max (d.1 / ζ - 1)
          (variance / (n.1 * b0.1 * ε ^ 2)) :=
        (mul_max_of_nonneg _ _ hb.le).symm
  have hSqrtL :
      Real.sqrt (ω * b0.1 / n.1 * max (odds * b0.1) v) =
        b0.1 * Real.sqrt (ω * ratio / n.1) := by
    rw [hmax]
    rw [show ω * (b0.1 : ℝ) / n.1 * (b0.1 * ratio) =
        (b0.1 : ℝ) ^ 2 * (ω * ratio / n.1) by ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_pos hb]
  have hSqrtA :
      Real.sqrt ((1 + ω) / n.1 * max (odds * b0.1) v) =
        b0.1 * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) := by
    rw [hmax]
    rw [show (1 + ω) / n.1 * (b0.1 * ratio) =
        (b0.1 : ℝ) ^ 2 * ((1 + ω) * ratio / (n.1 * b0.1)) by
          field_simp [ne_of_gt hb, ne_of_gt hn] <;> ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_pos hb]
  simp only [onlineNonconvexOracleScale, vrIterationBracket]
  change v + Δ * L * b0.1 / ε ^ 2 +
      Δ * L / ε ^ 2 * Real.sqrt (ω * b0.1 / n.1 *
        max (odds * b0.1) v) +
      Δ * ℒ / ε ^ 2 * Real.sqrt ((1 + ω) / n.1 *
        max (odds * b0.1) v) = _
  rw [hSqrtL, hSqrtA]
  dsimp [v, ratio]
  ring

/-- The printed D.4 oracle expression is the variance initialization plus
`b⁰` times the density-normalized geometric iteration factor. -/
theorem online_pl_oracle_scale_eq
    {d n b0 : Count} (L ℒ ω μ p ζ variance ε logGap : ℝ)
    (hω : 0 ≤ ω) (hμ : 0 < μ) :
    onlinePLOracleScale L ℒ ω μ p ζ variance ε logGap d n b0 =
      variance / (n.1 * μ * ε) + b0.1 *
        max (1 / p)
          (vrIterationBracket L ℒ ω
            (onlineDensityBatchRatio d n b0 ζ variance (μ * ε)) n b0 / μ) *
        logGap := by
  have hb : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  let odds : ℝ := d.1 / ζ - 1
  let v : ℝ := variance / (n.1 * μ * ε)
  let ratio : ℝ := onlineDensityBatchRatio d n b0 ζ variance (μ * ε)
  have hmax : max (odds * (b0.1 : ℝ)) v = (b0.1 : ℝ) * ratio := by
    dsimp [odds, v, ratio, onlineDensityBatchRatio]
    calc
      max ((d.1 / ζ - 1) * (b0.1 : ℝ))
          (variance / (n.1 * μ * ε)) =
        max ((b0.1 : ℝ) * (d.1 / ζ - 1))
          ((b0.1 : ℝ) *
            (variance / (n.1 * b0.1 * (μ * ε)))) := by
              congr 1
              · ring
              · field_simp [ne_of_gt hb, ne_of_gt hn] <;> ring
      _ = (b0.1 : ℝ) * max (d.1 / ζ - 1)
          (variance / (n.1 * b0.1 * (μ * ε))) :=
        (mul_max_of_nonneg _ _ hb.le).symm
  have hSqrtL :
      Real.sqrt (ω * b0.1 / n.1 * max (odds * b0.1) v) =
        b0.1 * Real.sqrt (ω * ratio / n.1) := by
    rw [hmax]
    rw [show ω * (b0.1 : ℝ) / n.1 * (b0.1 * ratio) =
        (b0.1 : ℝ) ^ 2 * (ω * ratio / n.1) by ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_pos hb]
  have hSqrtA :
      Real.sqrt ((1 + ω) / n.1 * max (odds * b0.1) v) =
        b0.1 * Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) := by
    rw [hmax]
    rw [show (1 + ω) / n.1 * (b0.1 * ratio) =
        (b0.1 : ℝ) ^ 2 * ((1 + ω) * ratio / (n.1 * b0.1)) by
          field_simp [ne_of_gt hb, ne_of_gt hn] <;> ring]
    rw [Real.sqrt_mul (sq_nonneg (b0.1 : ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_pos hb]
  simp only [onlinePLOracleScale, vrIterationBracket]
  change v + max (b0.1 / p)
      (L / μ * (b0.1 + Real.sqrt (ω * b0.1 / n.1 *
        max (odds * b0.1) v)) +
       ℒ / μ * Real.sqrt ((1 + ω) / n.1 *
        max (odds * b0.1) v)) * logGap = _
  rw [hSqrtL, hSqrtA]
  dsimp [v, ratio]
  rw [show (b0.1 : ℝ) / p = b0.1 * (1 / p) by ring]
  rw [show L / μ * (b0.1 + b0.1 *
        Real.sqrt (ω * onlineDensityBatchRatio d n b0 ζ variance (μ * ε) /
          n.1)) +
      ℒ / μ * (b0.1 * Real.sqrt ((1 + ω) *
        onlineDensityBatchRatio d n b0 ζ variance (μ * ε) /
          (n.1 * b0.1))) =
      b0.1 * (vrIterationBracket L ℒ ω
        (onlineDensityBatchRatio d n b0 ζ variance (μ * ε)) n b0 / μ) by
          simp only [vrIterationBracket]
          field_simp [ne_of_gt hμ] <;> ring]
  rw [mul_max_of_nonneg _ _ hb.le]
  simp only [vrIterationBracket]

set_option maxHeartbeats 800000 in
/-- `book/MARINA/MARINA.json#/key_lemmas/16`, Corollary D.1. -/
theorem Corollary_D1_finite_sum_VR_complexity
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatchSize : b0.1 ≤ m.1)
    (hStep : FiniteSumDensityStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
      (expectedDensity A.quantizer) d n m b0)
    (hSchedule : A.refreshProbability =
      finiteSumDensityBatchRefreshSchedule (expectedDensity A.quantizer) d m b0) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective (finiteSumLocalProblem A.problem) x0 - fStar
    let ratio := finiteSumDensityBatchRatio d m b0 ζ
    let bracket := vrIterationBracket (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) ω ratio n b0
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) ε)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
        (fun ε => finiteSumOracleCallCount m b0 (K ε) A.refreshProbability)
        (fun ε => finiteSumNonconvexOracleScale Δ (rootMeanSquare Llocal)
          (rootMeanSquare ℒlocal) ω ζ ε d n m b0)
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ * ζ / (ε : ℝ) ^ 2 * bracket) := by
  have hGapNonneg : 0 ≤
      globalObjective (finiteSumLocalProblem A.problem) x0 - fStar :=
    sub_nonneg.mpr (hLower x0)
  dsimp
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective (finiteSumLocalProblem A.problem) x0 - fStar
  let ratio : ℝ := finiteSumDensityBatchRatio d m b0 ζ
  let bracket : ℝ := vrIterationBracket (rootMeanSquare Llocal)
    (rootMeanSquare ℒlocal) ω ratio n b0
  have hGeneralStep : FiniteSumVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0 :=
    density_stepsize_bridge_finiteSum hSchedule hStep
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hPayload := finite_sum_density_schedule_payload_bounds hp hp1 hζ hBatchSize hSchedule
  have hζpos : 0 < ζ := hPayload.1
  have hOraclePayload := hPayload.2.1
  have hCommPayload := hPayload.2.2
  have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := Real.sqrt_nonneg _
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hratio : 0 < ratio := by
    dsimp [ratio, finiteSumDensityBatchRatio]
    exact (div_pos (by exact_mod_cast m.2) (by exact_mod_cast b0.2)).trans_le
      (le_max_right _ _)
  have hbracket : 0 ≤ bracket := by
    dsimp [bracket, vrIterationBracket]
    positivity
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq :
        globalObjective (finiteSumLocalProblem A.problem) x0 - fStar = 0 :=
      hGapZero.symm
    refine ⟨fun _ => K₁, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ε
      unfold NonconvexAccuracy
      have hD1 := Theorem_D1_finite_sum_VR_nonconvex (K := K₁) A x0
        batchLaw Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw
        hAverageSmooth hQuantizer hGeneralStep
      refine ⟨hD1.1, hD1.2.trans ?_⟩
      rw [hGapEq]
      simp
      positivity
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        rw [hGapEq]
        simp
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ)) accuracyToZero)
    · unfold AccuracyBigO
      have hmne : (m.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt m.2)
      rw [show (fun ε : Accuracy => finiteSumNonconvexOracleScale
          (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar)
          (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
          (expectedDensity A.quantizer) (ε : ℝ) d n m b0) =
          (fun _ : Accuracy => (m.1 : ℝ)) by
        funext ε
        rw [finite_sum_nonconvex_oracle_scale_eq _ _ _ _ _ _ hω, hGapEq]
        simp]
      simpa [finiteSumOracleCallCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((m.1 : ℝ) + (A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * b0.1)) hmne accuracyToZero)
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
      rw [show (fun ε : Accuracy => (d.1 : ℝ) +
          (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) *
            expectedDensity A.quantizer / (ε : ℝ) ^ 2 *
              vrIterationBracket (rootMeanSquare Llocal)
                (rootMeanSquare ℒlocal) ω
                (finiteSumDensityBatchRatio d m b0
                  (expectedDensity A.quantizer)) n b0) =
          (fun _ : Accuracy => (d.1 : ℝ)) by
        funext ε
        rw [hGapEq]
        ring]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) + (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))
          hdne accuracyToZero)
  · rcases hbracket.eq_or_lt with hBracketZero | hBracketPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hBracketEq : bracket = 0 := hBracketZero.symm
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hfirst : 0 ≤ rootMeanSquare Llocal *
            (1 + Real.sqrt (ω * ratio / n.1)) := by positivity
        have hsecond : 0 ≤ rootMeanSquare ℒlocal *
            Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) := by positivity
        have hsum : rootMeanSquare Llocal *
              (1 + Real.sqrt (ω * ratio / n.1)) +
            rootMeanSquare ℒlocal *
              Real.sqrt ((1 + ω) * ratio / (n.1 * b0.1)) = 0 := by
          simpa [bracket, vrIterationBracket] using hBracketEq
        have hfactor : 0 < 1 + Real.sqrt (ω * ratio / n.1) := by positivity
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        (finiteSumLocalProblem A.problem) Llocal fStar hLower hSmooth hLzero
      refine ⟨fun _ => K₁, ?_⟩
      unfold ThreeEndpointComplexity
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD1 := Theorem_D1_finite_sum_VR_nonconvex (K := K₁) A x0
          batchLaw Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw
          hAverageSmooth hQuantizer hGeneralStep
        refine ⟨hD1.1, ?_⟩
        have heq : (fun z =>
            ‖globalGradient (finiteSumLocalProblem A.problem)
              (uniformOutput (K := K₁) (finiteSumProcess (b0 := b0) A x0) z)‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change Δ / (ε : ℝ) ^ 2 * bracket = 0
          rw [hBracketEq]
          ring
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ)) accuracyToZero)
      · unfold AccuracyBigO
        have hmne : (m.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt m.2)
        rw [show (fun ε : Accuracy => finiteSumNonconvexOracleScale
            (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar)
            (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
            (expectedDensity A.quantizer) (ε : ℝ) d n m b0) =
            (fun _ : Accuracy => (m.1 : ℝ)) by
          funext ε
          rw [finite_sum_nonconvex_oracle_scale_eq _ _ _ _ _ _ hω]
          simp [hBracketEq, bracket, ratio, Δ, ζ]]
        simpa [finiteSumOracleCallCount, K₁] using
          (Asymptotics.isBigO_const_const
            ((m.1 : ℝ) + (A.refreshProbability * m.1 +
              2 * (1 - A.refreshProbability) * b0.1)) hmne accuracyToZero)
      · unfold AccuracyBigO
        have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
        rw [show (fun ε : Accuracy => (d.1 : ℝ) +
            (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) *
              expectedDensity A.quantizer / (ε : ℝ) ^ 2 *
                vrIterationBracket (rootMeanSquare Llocal)
                  (rootMeanSquare ℒlocal) ω
                  (finiteSumDensityBatchRatio d m b0
                    (expectedDensity A.quantizer)) n b0) =
            (fun _ : Accuracy => (d.1 : ℝ)) by
          funext ε
          change (d.1 : ℝ) + Δ * ζ / (ε : ℝ) ^ 2 * bracket = d.1
          rw [hBracketEq]
          ring]
        simpa [allWorkerCommunicationCount, K₁] using
          (Asymptotics.isBigO_const_const
            ((d.1 : ℝ) + (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer))
            hdne accuracyToZero)
    · let K : Accuracy → Count := fun ε =>
        ⟨max 1 (Nat.ceil (2 * Δ /
          ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
      have hScalar := positive_inverse_square_ceiling_schedule
        Δ (A.stepSize : ℝ) bracket hGapPos A.stepSize.property hBracketPos
      have hΔpos : 0 < Δ := by simpa [Δ] using hGapPos
      have hKBound : ∀ ε : Accuracy,
          2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) ≤
            (ε : ℝ) ^ 2 := by
        intro ε
        simpa [K] using hScalar.1 ε
      have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
          (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) := by
        simpa [K] using hScalar.2
      refine ⟨K, ?_⟩
      unfold ThreeEndpointComplexity
      refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD1 := Theorem_D1_finite_sum_VR_nonconvex (K := K ε) A x0
          batchLaw Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw
          hAverageSmooth hQuantizer hGeneralStep
        refine ⟨hD1.1, hD1.2.trans ?_⟩
        simpa [Δ] using hKBound ε
      · let oraclePayload : ℝ := A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * b0.1
        have hOraclePayloadNonneg : 0 ≤ oraclePayload := by
          dsimp [oraclePayload]
          have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
          exact add_nonneg (mul_nonneg hp.le (by positivity))
            (mul_nonneg (mul_nonneg (by norm_num) hOneSub) (by positivity))
        unfold AccuracyBigO at hKBigO ⊢
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨1 + 3 * C, by positivity, ?_⟩
        filter_upwards [hKC.bound] with ε hKc
        let base : ℝ := Δ / (ε : ℝ) ^ 2 * bracket
        have hbase : 0 < base := by
          dsimp [base]
          exact mul_pos (div_pos hΔpos (sq_pos_of_pos ε.property)) hBracketPos
        have hKn : ((K ε).1 : ℝ) ≤ C * base := by
          have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
          change ‖((K ε).1 : ℝ)‖ ≤ C * ‖base‖ at hKc
          rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
            Real.norm_eq_abs, abs_of_pos hbase] at hKc
          exact hKc
        have hround : ((K ε).1 : ℝ) * oraclePayload ≤
            3 * C * (base * b0.1) := by
          calc
            ((K ε).1 : ℝ) * oraclePayload ≤
                (C * base) * oraclePayload :=
              mul_le_mul_of_nonneg_right hKn hOraclePayloadNonneg
            _ ≤ (C * base) * (3 * b0.1) :=
              mul_le_mul_of_nonneg_left hOraclePayload (by positivity)
            _ = 3 * C * (base * b0.1) := by ring
        have hscaleEq := finite_sum_nonconvex_oracle_scale_eq
          (d := d) (n := n) (m := m) (b0 := b0)
          Δ (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω ζ
            (ε : ℝ) hω
        rw [finiteSumOracleCallCount, hscaleEq]
        have hleftEq : (m.1 : ℝ) + (K ε).1 *
            (A.refreshProbability * m.1 +
              2 * (1 - A.refreshProbability) * b0.1) =
            m.1 + (K ε).1 * oraclePayload := by rfl
        have hrightEq : (m.1 : ℝ) + Δ / (ε : ℝ) ^ 2 *
            (b0.1 * vrIterationBracket (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) ω
              (finiteSumDensityBatchRatio d m b0 ζ) n b0) =
            m.1 + base * b0.1 := by
          dsimp [base, bracket, ratio]
          ring
        rw [hleftEq, hrightEq]
        have hmpos : 0 < (m.1 : ℝ) := by exact_mod_cast m.2
        have hb0nonneg : 0 ≤ (b0.1 : ℝ) := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
            0 ≤ (m.1 : ℝ) + (K ε).1 * oraclePayload),
          Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg
            hmpos (mul_nonneg hbase.le hb0nonneg))]
        nlinarith
      · let commPayload : ℝ := A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ
        have hCommPayloadNonneg : 0 ≤ commPayload := by
          dsimp [commPayload]
          exact add_nonneg (mul_nonneg hp.le (by positivity))
            (mul_nonneg (sub_nonneg.mpr hp1) hζ)
        unfold AccuracyBigO at hKBigO ⊢
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨1 + 2 * C, by positivity, ?_⟩
        filter_upwards [hKC.bound] with ε hKc
        let base : ℝ := Δ / (ε : ℝ) ^ 2 * bracket
        have hbase : 0 < base := by
          dsimp [base]
          exact mul_pos (div_pos hΔpos (sq_pos_of_pos ε.property)) hBracketPos
        have hKn : ((K ε).1 : ℝ) ≤ C * base := by
          have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
          change ‖((K ε).1 : ℝ)‖ ≤ C * ‖base‖ at hKc
          rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
            Real.norm_eq_abs, abs_of_pos hbase] at hKc
          exact hKc
        have hround : ((K ε).1 : ℝ) * commPayload ≤
            2 * C * (base * ζ) := by
          calc
            ((K ε).1 : ℝ) * commPayload ≤
                (C * base) * commPayload :=
              mul_le_mul_of_nonneg_right hKn hCommPayloadNonneg
            _ ≤ (C * base) * (2 * ζ) :=
              mul_le_mul_of_nonneg_left hCommPayload (by positivity)
            _ = 2 * C * (base * ζ) := by ring
        have hTargetEq : (d.1 : ℝ) +
            Δ * ζ / (ε : ℝ) ^ 2 * bracket = d.1 + base * ζ := by
          dsimp [base]
          ring
        rw [allWorkerCommunicationCount]
        change ‖(d.1 : ℝ) + (K ε).1 * commPayload‖ ≤
          (1 + 2 * C) *
            ‖(d.1 : ℝ) + Δ * ζ / (ε : ℝ) ^ 2 * bracket‖
        rw [hTargetEq, Real.norm_eq_abs, abs_of_nonneg (by positivity :
            0 ≤ (d.1 : ℝ) + (K ε).1 * commPayload),
          Real.norm_eq_abs, abs_of_pos (by positivity :
            0 < (d.1 : ℝ) + base * ζ)]
        nlinarith

/-- `book/MARINA/MARINA.json#/key_lemmas/18`, Corollary D.2. -/
theorem Corollary_D2_finite_sum_VR_PL_complexity
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 xStar : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hPL : SatisfiesPL (finiteSumLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatchSize : b0.1 ≤ m.1)
    (hStep : FiniteSumPLDensityStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
      (expectedDensity A.quantizer) μ d n m b0)
    (hSchedule : A.refreshProbability =
      finiteSumDensityBatchRefreshSchedule (expectedDensity A.quantizer) d m b0) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective (finiteSumLocalProblem A.problem) x0 -
      globalObjective (finiteSumLocalProblem A.problem) xStar
    let ratio := finiteSumDensityBatchRatio d m b0 ζ
    let factor := max (1 / A.refreshProbability)
      (vrIterationBracket (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
        ω ratio n b0 / μ)
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => PLAccuracy (K ε) (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw)
          xStar ε)
        (fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (fun ε => finiteSumOracleCallCount m b0 (K ε) A.refreshProbability)
        (fun ε => finiteSumPLOracleScale (rootMeanSquare Llocal)
          (rootMeanSquare ℒlocal) ω μ A.refreshProbability ζ
          (Real.log (Δ / (ε : ℝ))) d n m b0)
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + ζ * factor * Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤
      globalObjective (finiteSumLocalProblem A.problem) x0 -
        globalObjective (finiteSumLocalProblem A.problem) xStar :=
    sub_nonneg.mpr (hPL.1 x0)
  dsimp
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective (finiteSumLocalProblem A.problem) x0 -
    globalObjective (finiteSumLocalProblem A.problem) xStar
  let ratio : ℝ := finiteSumDensityBatchRatio d m b0 ζ
  let bracket : ℝ := vrIterationBracket (rootMeanSquare Llocal)
    (rootMeanSquare ℒlocal) ω ratio n b0
  let factor : ℝ := max (1 / A.refreshProbability) (bracket / μ)
  have hGeneralStep : FiniteSumVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0 :=
    density_stepsize_bridge_finiteSum_PL hSchedule hStep
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hPayload := finite_sum_density_schedule_payload_bounds
    hp hp1 hζ hBatchSize hSchedule
  have hζpos : 0 < ζ := hPayload.1
  have hOraclePayload := hPayload.2.1
  have hCommPayload := hPayload.2.2
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hfactor : 0 < factor := by
    dsimp [factor]
    exact (div_pos zero_lt_one hp).trans_le (le_max_left _ _)
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq :
        globalObjective (finiteSumLocalProblem A.problem) x0 -
          globalObjective (finiteSumLocalProblem A.problem) xStar = 0 :=
      hGapZero.symm
    refine ⟨fun _ => K₁, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hD2 := Theorem_D2_finite_sum_VR_PL (K := K₁) A x0 xStar
        batchLaw Llocal ℒlocal ω fStar μ hLower hSmooth hBatchLaw
        hAverageSmooth hPL hQuantizer hGeneralStep
      refine ⟨hD2.1, ?_⟩
      have hNonpos :
          (∫ path,
            (globalObjective (finiteSumLocalProblem A.problem)
                (finiteSumProcess (b0 := b0) A x0 K₁.1 path).x -
              globalObjective (finiteSumLocalProblem A.problem) xStar)
            ∂finiteSumPathLaw A batchLaw) ≤ 0 := by
        rw [hGapEq] at hD2
        simpa using hD2.2
      exact hNonpos.trans (le_of_lt ε.property)
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        rw [hGapEq]
        simp
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · unfold AccuracyBigO
      have hmne : (m.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt m.2)
      rw [show (fun ε : Accuracy => finiteSumPLOracleScale
          (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω μ
          A.refreshProbability (expectedDensity A.quantizer)
          (Real.log ((globalObjective (finiteSumLocalProblem A.problem) x0 -
            globalObjective (finiteSumLocalProblem A.problem) xStar) /
              (ε : ℝ))) d n m b0) =
          (fun _ : Accuracy => (m.1 : ℝ)) by
        funext ε
        rw [finite_sum_pl_oracle_scale_eq _ _ _ _ _ _ _ hω μ.property,
          hGapEq]
        simp]
      simpa [finiteSumOracleCallCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((m.1 : ℝ) + (A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * b0.1)) hmne accuracyToZero)
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
      rw [show (fun ε : Accuracy => (d.1 : ℝ) +
          expectedDensity A.quantizer *
            max (1 / A.refreshProbability)
              (vrIterationBracket (rootMeanSquare Llocal)
                (rootMeanSquare ℒlocal) ω
                (finiteSumDensityBatchRatio d m b0
                  (expectedDensity A.quantizer)) n b0 / μ) *
            Real.log ((globalObjective (finiteSumLocalProblem A.problem) x0 -
              globalObjective (finiteSumLocalProblem A.problem) xStar) /
                (ε : ℝ))) = (fun _ : Accuracy => (d.1 : ℝ)) by
        funext ε
        rw [hGapEq]
        simp]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) + (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))
          hdne accuracyToZero)
  · let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    have hΔpos : 0 < Δ := by simpa [Δ] using hGapPos
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos A.stepSize.property μ.property
    have hc1 : c ≤ 1 := by
      have hcP := hGeneralStep.2
      dsimp [c]
      nlinarith
    let K : Accuracy → Count := fun ε =>
      ⟨max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)), by omega⟩
    have hScalar := positive_geometric_ceiling_schedule
      Δ c factor hΔpos hc hc1 hfactor
    have hContract : ∀ ε : Accuracy,
        (1 - c) ^ (K ε).1 * Δ ≤ (ε : ℝ) := by
      intro ε
      simpa [K] using hScalar.1 ε
    have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => factor * Real.log (Δ / (ε : ℝ))) := by
      simpa [K] using hScalar.2
    refine ⟨K, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hD2 := Theorem_D2_finite_sum_VR_PL (K := K ε) A x0 xStar
        batchLaw Llocal ℒlocal ω fStar μ hLower hSmooth hBatchLaw
        hAverageSmooth hPL hQuantizer hGeneralStep
      refine ⟨hD2.1, hD2.2.trans ?_⟩
      simpa [c, Δ] using hContract ε
    · let oraclePayload : ℝ := A.refreshProbability * m.1 +
          2 * (1 - A.refreshProbability) * b0.1
      have hOraclePayloadNonneg : 0 ≤ oraclePayload := by
        dsimp [oraclePayload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            (by positivity))
      unfold AccuracyBigO at hKBigO ⊢
      rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
      rw [Asymptotics.isBigO_iff']
      refine ⟨1 + 3 * C, by positivity, ?_⟩
      filter_upwards [hKC.bound,
        eventually_one_le_log_gap_div_accuracy hΔpos]
        with ε hKc hlog
      let base : ℝ := factor * Real.log (Δ / (ε : ℝ))
      have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
        lt_of_lt_of_le zero_lt_one hlog
      have hbase : 0 < base := by
        dsimp [base]
        exact mul_pos hfactor hlogpos
      have hKn : ((K ε).1 : ℝ) ≤ C * base := by
        have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
        change ‖((K ε).1 : ℝ)‖ ≤ C * ‖base‖ at hKc
        rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
          Real.norm_eq_abs, abs_of_pos hbase] at hKc
        exact hKc
      have hround : ((K ε).1 : ℝ) * oraclePayload ≤
          3 * C * (base * b0.1) := by
        calc
          ((K ε).1 : ℝ) * oraclePayload ≤ (C * base) * oraclePayload :=
            mul_le_mul_of_nonneg_right hKn hOraclePayloadNonneg
          _ ≤ (C * base) * (3 * b0.1) :=
            mul_le_mul_of_nonneg_left hOraclePayload (by positivity)
          _ = 3 * C * (base * b0.1) := by ring
      have hscaleEq := finite_sum_pl_oracle_scale_eq
        (d := d) (n := n) (m := m) (b0 := b0)
        (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω (μ : ℝ)
          A.refreshProbability ζ (Real.log (Δ / (ε : ℝ))) hω μ.property
      rw [finiteSumOracleCallCount, hscaleEq]
      have hleftEq : (m.1 : ℝ) + (K ε).1 *
          (A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * b0.1) =
          m.1 + (K ε).1 * oraclePayload := by rfl
      have hrightEq : (m.1 : ℝ) + b0.1 *
          max (1 / A.refreshProbability)
            (vrIterationBracket (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) ω
              (finiteSumDensityBatchRatio d m b0 ζ) n b0 / μ) *
          Real.log (Δ / (ε : ℝ)) = m.1 + base * b0.1 := by
        dsimp [base, factor, bracket, ratio]
        ring
      rw [hleftEq, hrightEq]
      have hmpos : 0 < (m.1 : ℝ) := by exact_mod_cast m.2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
          0 ≤ (m.1 : ℝ) + (K ε).1 * oraclePayload),
        Real.norm_eq_abs, abs_of_pos (by positivity :
          0 < (m.1 : ℝ) + base * b0.1)]
      nlinarith
    · let commPayload : ℝ := A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ
      have hCommPayloadNonneg : 0 ≤ commPayload := by
        dsimp [commPayload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr hp1) hζ)
      unfold AccuracyBigO at hKBigO ⊢
      rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
      rw [Asymptotics.isBigO_iff']
      refine ⟨1 + 2 * C, by positivity, ?_⟩
      filter_upwards [hKC.bound,
        eventually_one_le_log_gap_div_accuracy hΔpos]
        with ε hKc hlog
      let base : ℝ := factor * Real.log (Δ / (ε : ℝ))
      have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) :=
        lt_of_lt_of_le zero_lt_one hlog
      have hbase : 0 < base := by
        dsimp [base]
        exact mul_pos hfactor hlogpos
      have hKn : ((K ε).1 : ℝ) ≤ C * base := by
        have hKnonneg : 0 ≤ ((K ε).1 : ℝ) := by positivity
        change ‖((K ε).1 : ℝ)‖ ≤ C * ‖base‖ at hKc
        rw [Real.norm_eq_abs, abs_of_nonneg hKnonneg,
          Real.norm_eq_abs, abs_of_pos hbase] at hKc
        exact hKc
      have hround : ((K ε).1 : ℝ) * commPayload ≤
          2 * C * (base * ζ) := by
        calc
          ((K ε).1 : ℝ) * commPayload ≤ (C * base) * commPayload :=
            mul_le_mul_of_nonneg_right hKn hCommPayloadNonneg
          _ ≤ (C * base) * (2 * ζ) :=
            mul_le_mul_of_nonneg_left hCommPayload (by positivity)
          _ = 2 * C * (base * ζ) := by ring
      have hTargetEq : (d.1 : ℝ) + ζ * factor *
          Real.log (Δ / (ε : ℝ)) = d.1 + base * ζ := by
        dsimp [base]
        ring
      rw [allWorkerCommunicationCount]
      change ‖(d.1 : ℝ) + (K ε).1 * commPayload‖ ≤
        (1 + 2 * C) *
          ‖(d.1 : ℝ) + ζ * factor * Real.log (Δ / (ε : ℝ))‖
      rw [hTargetEq, Real.norm_eq_abs, abs_of_nonneg (by positivity :
          0 ≤ (d.1 : ℝ) + (K ε).1 * commPayload),
        Real.norm_eq_abs, abs_of_pos (by positivity :
          0 < (d.1 : ℝ) + base * ζ)]
      nlinarith

/-- `book/MARINA/MARINA.json#/key_lemmas/14`, Theorem D.1 / Eqs. (29)-(31). -/
theorem Theorem_D1_finite_sum_VR_complexity_endpoints
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : FiniteSumVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective (finiteSumLocalProblem A.problem) x0 - fStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) ε)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
        (fun ε => finiteSumOracleCallCount m b0 (K ε) A.refreshProbability)
        (fun ε => m.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * m.1 + (1 - A.refreshProbability) * b0.1))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  have hGapNonneg : 0 ≤
      globalObjective (finiteSumLocalProblem A.problem) x0 - fStar :=
    sub_nonneg.mpr (hLower x0)
  dsimp
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective (finiteSumLocalProblem A.problem) x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((1 - A.refreshProbability) /
      (A.refreshProbability * n.1) *
      (ω * rootMeanSquare Llocal ^ 2 +
        (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    positivity
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq :
        globalObjective (finiteSumLocalProblem A.problem) x0 - fStar = 0 :=
      hGapZero.symm
    have hΔzero : Δ = 0 := by simpa [Δ] using hGapEq
    refine ⟨fun _ => K₁, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ε
      unfold NonconvexAccuracy
      have hD1 := Theorem_D1_finite_sum_VR_nonconvex (K := K₁) A x0
        batchLaw Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw
        hAverageSmooth hQuantizer hStep
      refine ⟨hD1.1, hD1.2.trans ?_⟩
      rw [hGapEq]
      simp
      positivity
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        change Δ / (ε : ℝ) ^ 2 * bracket = 0
        rw [hΔzero]
        ring
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · unfold AccuracyBigO
      have hmne : (m.1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt m.2)
      rw [show (fun ε : Accuracy => (m.1 : ℝ) +
          (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) /
            (ε : ℝ) ^ 2 *
            (rootMeanSquare Llocal +
              Real.sqrt ((1 - A.refreshProbability) /
                (A.refreshProbability * n.1) *
                (ω * rootMeanSquare Llocal ^ 2 +
                  (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) *
            (A.refreshProbability * m.1 +
              (1 - A.refreshProbability) * b0.1)) =
          (fun _ : Accuracy => (m.1 : ℝ)) by
        funext ε
        rw [hGapEq]
        simp]
      simpa [finiteSumOracleCallCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((m.1 : ℝ) + (A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * b0.1)) hmne accuracyToZero)
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt d.2)
      rw [show (fun ε : Accuracy => (d.1 : ℝ) +
          (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) /
            (ε : ℝ) ^ 2 *
            (rootMeanSquare Llocal +
              Real.sqrt ((1 - A.refreshProbability) /
                (A.refreshProbability * n.1) *
                (ω * rootMeanSquare Llocal ^ 2 +
                  (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer)) =
          (fun _ : Accuracy => (d.1 : ℝ)) by
        funext ε
        rw [hGapEq]
        simp]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) + (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))
          hdne accuracyToZero)
  · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hBracketEq : bracket = 0 := hBracketZero.symm
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hsqrt : 0 ≤ Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
            (ω * rootMeanSquare Llocal ^ 2 +
              (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1)) :=
          Real.sqrt_nonneg _
        dsimp [bracket] at hBracketEq
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        (finiteSumLocalProblem A.problem) Llocal fStar hLower hSmooth hLzero
      refine ⟨fun _ => K₁, ?_⟩
      unfold ThreeEndpointComplexity
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD1 := Theorem_D1_finite_sum_VR_nonconvex (K := K₁) A x0
          batchLaw Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw
          hAverageSmooth hQuantizer hStep
        refine ⟨hD1.1, ?_⟩
        have heq : (fun z =>
            ‖globalGradient (finiteSumLocalProblem A.problem)
              (uniformOutput (K := K₁)
                (finiteSumProcess (b0 := b0) A x0) z)‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change Δ / (ε : ℝ) ^ 2 * bracket = 0
          rw [hBracketEq]
          ring
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
              accuracyToZero)
      · unfold AccuracyBigO
        have hmne : (m.1 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt m.2)
        rw [show (fun ε : Accuracy => (m.1 : ℝ) +
            (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) /
              (ε : ℝ) ^ 2 *
              (rootMeanSquare Llocal +
                Real.sqrt ((1 - A.refreshProbability) /
                  (A.refreshProbability * n.1) *
                  (ω * rootMeanSquare Llocal ^ 2 +
                    (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) *
              (A.refreshProbability * m.1 +
                (1 - A.refreshProbability) * b0.1)) =
            (fun _ : Accuracy => (m.1 : ℝ)) by
          funext ε
          change (m.1 : ℝ) + Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * m.1 +
              (1 - A.refreshProbability) * b0.1) = m.1
          rw [hBracketEq]
          ring]
        simpa [finiteSumOracleCallCount, K₁] using
          (Asymptotics.isBigO_const_const
            ((m.1 : ℝ) + (A.refreshProbability * m.1 +
              2 * (1 - A.refreshProbability) * b0.1)) hmne accuracyToZero)
      · unfold AccuracyBigO
        have hdne : (d.1 : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt d.2)
        rw [show (fun ε : Accuracy => (d.1 : ℝ) +
            (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) /
              (ε : ℝ) ^ 2 *
              (rootMeanSquare Llocal +
                Real.sqrt ((1 - A.refreshProbability) /
                  (A.refreshProbability * n.1) *
                  (ω * rootMeanSquare Llocal ^ 2 +
                    (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) *
              (A.refreshProbability * d.1 +
                (1 - A.refreshProbability) * expectedDensity A.quantizer)) =
            (fun _ : Accuracy => (d.1 : ℝ)) by
          funext ε
          change (d.1 : ℝ) + Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ) = d.1
          rw [hBracketEq]
          ring]
        simpa [allWorkerCommunicationCount, K₁] using
          (Asymptotics.isBigO_const_const
            ((d.1 : ℝ) + (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer))
            hdne accuracyToZero)
    · let K : Accuracy → Count := fun ε =>
        ⟨max 1 (Nat.ceil (2 * Δ /
          ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
      have hΔpos : 0 < Δ := by simpa [Δ] using hGapPos
      have hScalar := positive_inverse_square_ceiling_schedule
        Δ (A.stepSize : ℝ) bracket hΔpos A.stepSize.property hBracketPos
      have hKBound : ∀ ε : Accuracy,
          2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) ≤
            (ε : ℝ) ^ 2 := by
        intro ε
        simpa [K] using hScalar.1 ε
      have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
          (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) := by
        simpa [K] using hScalar.2
      have hScaleNonneg :
          ∀ᶠ ε : Accuracy in accuracyToZero,
            0 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by
        filter_upwards [] with ε
        positivity
      refine ⟨K, ?_⟩
      unfold ThreeEndpointComplexity
      refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD1 := Theorem_D1_finite_sum_VR_nonconvex (K := K ε) A x0
          batchLaw Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw
          hAverageSmooth hQuantizer hStep
        refine ⟨hD1.1, hD1.2.trans ?_⟩
        simpa [Δ] using hKBound ε
      · let oraclePayload : ℝ := A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * b0.1
        let targetPayload : ℝ := A.refreshProbability * m.1 +
            (1 - A.refreshProbability) * b0.1
        have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
        have hmpos : 0 < (m.1 : ℝ) := by exact_mod_cast m.2
        have hPMPos : 0 < A.refreshProbability * (m.1 : ℝ) :=
          mul_pos hp hmpos
        have hQBNonneg : 0 ≤
            (1 - A.refreshProbability) * (b0.1 : ℝ) :=
          mul_nonneg hOneSub (by positivity)
        have hOraclePayloadNonneg : 0 ≤ oraclePayload := by
          dsimp [oraclePayload]
          exact add_nonneg hPMPos.le
            (mul_nonneg (mul_nonneg (by norm_num) hOneSub) (by positivity))
        have hTargetPayloadPos : 0 < targetPayload := by
          dsimp [targetPayload]
          exact add_pos_of_pos_of_nonneg hPMPos hQBNonneg
        have hPayloadComparison : oraclePayload ≤ 2 * targetPayload := by
          dsimp [oraclePayload, targetPayload]
          nlinarith [hPMPos.le, hQBNonneg]
        have hOracle := accuracyBigO_affine_cost_of_schedule
          (K := fun ε => ((K ε).1 : ℝ))
          (scale := fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
          (init := (m.1 : ℝ))
          (actualPayload := oraclePayload)
          (targetPayload := targetPayload)
          (payloadFactor := 2)
          hKBigO hmpos hOraclePayloadNonneg hTargetPayloadPos
            (by norm_num) hPayloadComparison hScaleNonneg
        change AccuracyBigO
          (fun ε => (m.1 : ℝ) + ((K ε).1 : ℝ) * oraclePayload)
          (fun ε => (m.1 : ℝ) +
            (Δ / (ε : ℝ) ^ 2 * bracket) * targetPayload)
        exact hOracle
      · let commPayload : ℝ := A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ
        have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
        have hCommPayloadPos : 0 < commPayload := by
          dsimp [commPayload]
          exact add_pos_of_pos_of_nonneg
            (mul_pos hp hdpos)
            (mul_nonneg (sub_nonneg.mpr hp1) hζ)
        have hComm := accuracyBigO_affine_cost_of_schedule
          (K := fun ε => ((K ε).1 : ℝ))
          (scale := fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
          (init := (d.1 : ℝ))
          (actualPayload := commPayload)
          (targetPayload := commPayload)
          (payloadFactor := 1)
          hKBigO hdpos hCommPayloadPos.le hCommPayloadPos
            zero_lt_one (by simp) hScaleNonneg
        change AccuracyBigO
          (fun ε => (d.1 : ℝ) + ((K ε).1 : ℝ) * commPayload)
          (fun ε => (d.1 : ℝ) +
            (Δ / (ε : ℝ) ^ 2 * bracket) * commPayload)
        exact hComm

/-- `book/MARINA/MARINA.json#/key_lemmas/17`, Theorem D.2 / Eqs. (37)-(39). -/
theorem Theorem_D2_finite_sum_VR_PL_complexity_endpoints
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 xStar : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hPL : SatisfiesPL (finiteSumLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : FiniteSumVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective (finiteSumLocalProblem A.problem) x0 -
      globalObjective (finiteSumLocalProblem A.problem) xStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let factor := max (1 / A.refreshProbability) (bracket / μ)
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => PLAccuracy (K ε) (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw)
          xStar ε)
        (fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (fun ε => finiteSumOracleCallCount m b0 (K ε) A.refreshProbability)
        (fun ε => m.1 + factor * (A.refreshProbability * m.1 +
          (1 - A.refreshProbability) * b0.1) * Real.log (Δ / (ε : ℝ)))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + factor * (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ) * Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤
      globalObjective (finiteSumLocalProblem A.problem) x0 -
        globalObjective (finiteSumLocalProblem A.problem) xStar :=
    sub_nonneg.mpr (hPL.1 x0)
  dsimp
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective (finiteSumLocalProblem A.problem) x0 -
    globalObjective (finiteSumLocalProblem A.problem) xStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((1 - A.refreshProbability) /
      (A.refreshProbability * n.1) *
      (ω * rootMeanSquare Llocal ^ 2 +
        (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let factor : ℝ := max (1 / A.refreshProbability) (bracket / μ)
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hfactor : 0 < factor := by
    dsimp [factor]
    exact (div_pos zero_lt_one hp).trans_le (le_max_left _ _)
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq :
        globalObjective (finiteSumLocalProblem A.problem) x0 -
          globalObjective (finiteSumLocalProblem A.problem) xStar = 0 :=
      hGapZero.symm
    refine ⟨fun _ => K₁, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hD2 := Theorem_D2_finite_sum_VR_PL (K := K₁) A x0 xStar
        batchLaw Llocal ℒlocal ω fStar μ hLower hSmooth hBatchLaw
        hAverageSmooth hPL hQuantizer hStep
      refine ⟨hD2.1, ?_⟩
      have hNonpos :
          (∫ path,
            (globalObjective (finiteSumLocalProblem A.problem)
                (finiteSumProcess (b0 := b0) A x0 K₁.1 path).x -
              globalObjective (finiteSumLocalProblem A.problem) xStar)
            ∂finiteSumPathLaw A batchLaw) ≤ 0 := by
        rw [hGapEq] at hD2
        simpa using hD2.2
      exact hNonpos.trans (le_of_lt ε.property)
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        rw [hGapEq]
        simp
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · unfold AccuracyBigO
      have hmne : (m.1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt m.2)
      rw [show (fun ε : Accuracy => (m.1 : ℝ) +
          max (1 / A.refreshProbability)
              ((rootMeanSquare Llocal +
                Real.sqrt ((1 - A.refreshProbability) /
                  (A.refreshProbability * n.1) *
                  (ω * rootMeanSquare Llocal ^ 2 +
                    (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) / μ) *
            (A.refreshProbability * m.1 +
              (1 - A.refreshProbability) * b0.1) *
            Real.log ((globalObjective (finiteSumLocalProblem A.problem) x0 -
              globalObjective (finiteSumLocalProblem A.problem) xStar) /
                (ε : ℝ))) = (fun _ : Accuracy => (m.1 : ℝ)) by
        funext ε
        rw [hGapEq]
        simp]
      simpa [finiteSumOracleCallCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((m.1 : ℝ) + (A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * b0.1)) hmne accuracyToZero)
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt d.2)
      rw [show (fun ε : Accuracy => (d.1 : ℝ) +
          max (1 / A.refreshProbability)
              ((rootMeanSquare Llocal +
                Real.sqrt ((1 - A.refreshProbability) /
                  (A.refreshProbability * n.1) *
                  (ω * rootMeanSquare Llocal ^ 2 +
                    (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) / μ) *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer) *
            Real.log ((globalObjective (finiteSumLocalProblem A.problem) x0 -
              globalObjective (finiteSumLocalProblem A.problem) xStar) /
                (ε : ℝ))) = (fun _ : Accuracy => (d.1 : ℝ)) by
        funext ε
        rw [hGapEq]
        simp]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) + (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))
          hdne accuracyToZero)
  · let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    have hΔpos : 0 < Δ := by simpa [Δ] using hGapPos
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos A.stepSize.property μ.property
    have hc1 : c ≤ 1 := by
      have hcP := hStep.2
      dsimp [c]
      nlinarith
    let K : Accuracy → Count := fun ε =>
      ⟨max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)), by omega⟩
    have hScalar := positive_geometric_ceiling_schedule
      Δ c factor hΔpos hc hc1 hfactor
    have hContract : ∀ ε : Accuracy,
        (1 - c) ^ (K ε).1 * Δ ≤ (ε : ℝ) := by
      intro ε
      simpa [K] using hScalar.1 ε
    have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => factor * Real.log (Δ / (ε : ℝ))) := by
      simpa [K] using hScalar.2
    have hScaleNonneg :
        ∀ᶠ ε : Accuracy in accuracyToZero,
          0 ≤ factor * Real.log (Δ / (ε : ℝ)) := by
      filter_upwards [eventually_one_le_log_gap_div_accuracy hΔpos]
        with ε hlog
      exact mul_nonneg hfactor.le (le_trans (by norm_num) hlog)
    refine ⟨K, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hD2 := Theorem_D2_finite_sum_VR_PL (K := K ε) A x0 xStar
        batchLaw Llocal ℒlocal ω fStar μ hLower hSmooth hBatchLaw
        hAverageSmooth hPL hQuantizer hStep
      refine ⟨hD2.1, hD2.2.trans ?_⟩
      simpa [c, Δ] using hContract ε
    · let oraclePayload : ℝ := A.refreshProbability * m.1 +
          2 * (1 - A.refreshProbability) * b0.1
      let targetPayload : ℝ := A.refreshProbability * m.1 +
          (1 - A.refreshProbability) * b0.1
      have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
      have hmpos : 0 < (m.1 : ℝ) := by exact_mod_cast m.2
      have hPMPos : 0 < A.refreshProbability * (m.1 : ℝ) := by
        exact mul_pos hp hmpos
      have hQBNonneg : 0 ≤
          (1 - A.refreshProbability) * (b0.1 : ℝ) :=
        mul_nonneg hOneSub (by positivity)
      have hOraclePayloadNonneg : 0 ≤ oraclePayload := by
        dsimp [oraclePayload]
        exact add_nonneg hPMPos.le
          (mul_nonneg (mul_nonneg (by norm_num) hOneSub) (by positivity))
      have hTargetPayloadPos : 0 < targetPayload := by
        dsimp [targetPayload]
        exact add_pos_of_pos_of_nonneg hPMPos hQBNonneg
      have hPayloadComparison : oraclePayload ≤ 2 * targetPayload := by
        dsimp [oraclePayload, targetPayload]
        nlinarith [hPMPos.le, hQBNonneg]
      have hOracle := accuracyBigO_affine_cost_of_schedule
        (K := fun ε => ((K ε).1 : ℝ))
        (scale := fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (init := (m.1 : ℝ))
        (actualPayload := oraclePayload)
        (targetPayload := targetPayload)
        (payloadFactor := 2)
        hKBigO hmpos hOraclePayloadNonneg hTargetPayloadPos
          (by norm_num) hPayloadComparison hScaleNonneg
      change AccuracyBigO
        (fun ε => (m.1 : ℝ) + ((K ε).1 : ℝ) * oraclePayload)
        (fun ε => (m.1 : ℝ) + factor * targetPayload *
          Real.log (Δ / (ε : ℝ)))
      rw [show (fun ε : Accuracy => (m.1 : ℝ) + factor * targetPayload *
          Real.log (Δ / (ε : ℝ))) =
          (fun ε : Accuracy => (m.1 : ℝ) +
            (factor * Real.log (Δ / (ε : ℝ))) * targetPayload) by
        funext ε
        ring]
      exact hOracle
    · let commPayload : ℝ := A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ
      have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
      have hCommPayloadPos : 0 < commPayload := by
        dsimp [commPayload]
        exact add_pos_of_pos_of_nonneg
          (mul_pos hp hdpos)
          (mul_nonneg (sub_nonneg.mpr hp1) hζ)
      have hComm := accuracyBigO_affine_cost_of_schedule
        (K := fun ε => ((K ε).1 : ℝ))
        (scale := fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (init := (d.1 : ℝ))
        (actualPayload := commPayload)
        (targetPayload := commPayload)
        (payloadFactor := 1)
        hKBigO hdpos hCommPayloadPos.le hCommPayloadPos
          zero_lt_one (by simp) hScaleNonneg
      change AccuracyBigO
        (fun ε => (d.1 : ℝ) + ((K ε).1 : ℝ) * commPayload)
        (fun ε => (d.1 : ℝ) + factor * commPayload *
          Real.log (Δ / (ε : ℝ)))
      rw [show (fun ε : Accuracy => (d.1 : ℝ) + factor * commPayload *
          Real.log (Δ / (ε : ℝ))) =
          (fun ε : Accuracy => (d.1 : ℝ) +
            (factor * Real.log (Δ / (ε : ℝ))) * commPayload) by
        funext ε
        ring]
      exact hComm

/-- The supplied-stepsize form of Corollary D.3.  Unlike the canonical-step
specialization below, this statement retains the reciprocal of the actually
supplied accuracy-indexed stepsize in every rate.  This is the faithful
conditional interface for the paper's upper-bound-only condition on `γ`:
an admissible but arbitrarily smaller `γ` cannot be assigned the same
`γ`-independent iteration scale.

The additive `1` absorbs the positive natural ceiling.  The factor `4` splits
the target squared accuracy equally between the optimization term in Eq. (41)
and the pointwise-safe refresh-batch variance floor. -/
theorem Corollary_D3_online_VR_complexity_supplied_stepsize_corrected
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (b : Accuracy → Count) (p : Accuracy → ℝ)
    (γ : Accuracy → PositiveStepsize)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess
          (A := onlineDataWithParameters A (γ ε) (p ε) (hp ε))
          hE x0 (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) b ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)))
    (hStep : ∀ ε, OnlineVRStepsizeCondition (γ ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0)
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
      (onlineNonconvexBatchScheduleFromBase n b0
        (varianceAggregateSq σ) b ε) b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) b
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let iterationScale := fun ε : Accuracy =>
      1 + 4 * Δ / ((γ ε : ℝ) * (ε : ℝ) ^ 2)
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) P
          (onlineCorrectedProofExactProcess
            (A := onlineDataWithParameters A (γ ε) (p ε) (hp ε))
            hE x0 (onlineNonconvexBatchScheduleFromBase_admissible n b0
              (varianceAggregateSq σ) b ε))
          (onlineProofExactPathLaw
            (A := onlineDataWithParameters A (γ ε) (p ε) (hp ε))) ε)
        iterationScale
        (fun ε => onlineOracleCallCount (chosenBatch ε) b0 (K ε) (p ε))
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (p ε * (chosenBatch ε).1 + 2 * (1 - p ε) * b0.1))
        (fun ε => allWorkerCommunicationCount d (K ε) (p ε) ζ)
        (fun ε => d.1 + iterationScale ε *
          (p ε * d.1 + (1 - p ε) * ζ)) := by
  dsimp
  let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
    (varianceAggregateSq σ) b
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective P x0 - fStar
  let iterationScale : Accuracy → ℝ := fun ε =>
    1 + 4 * Δ / ((γ ε : ℝ) * (ε : ℝ) ^ 2)
  let K : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (4 * Δ / ((γ ε : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ, P]
    exact sub_nonneg.mpr (hLower x0)
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hFloor (ε : Accuracy) :
      varianceAggregateSq σ / (n.1 * (chosenBatch ε).1) ≤
        (ε : ℝ) ^ 2 / 2 := by
    have hVar : 0 ≤ varianceAggregateSq σ := by
      unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
      simp only [Fintype.card_fin, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    simpa [chosenBatch] using
      onlineNonconvexBatchScheduleFromBase_variance_floor n b0
        (varianceAggregateSq σ) hVar b ε
  have hOptimizationHalf (ε : Accuracy) :
      2 * Δ / ((γ ε : ℝ) * ((K ε).1 : ℝ)) ≤ (ε : ℝ) ^ 2 / 2 := by
    have hKpos : 0 < ((K ε).1 : ℝ) := by exact_mod_cast (K ε).2
    have hγpos : 0 < (γ ε : ℝ) := (γ ε).property
    have hBudget := div_natCast_max_one_ceil_div_le
      (4 * Δ) ((γ ε : ℝ) * (ε : ℝ) ^ 2)
        (mul_pos hγpos (sq_pos_of_pos ε.property))
    have hBudget' :
        4 * Δ / ((γ ε : ℝ) * ((K ε).1 : ℝ)) ≤ (ε : ℝ) ^ 2 := by
      rw [div_le_iff₀ (mul_pos hγpos hKpos)]
      have hRaw : 4 * Δ / ((K ε).1 : ℝ) ≤
          (γ ε : ℝ) * (ε : ℝ) ^ 2 := by
        simpa [K] using hBudget
      rw [div_le_iff₀ hKpos] at hRaw
      nlinarith
    calc
      2 * Δ / ((γ ε : ℝ) * ((K ε).1 : ℝ)) =
          (1 / 2 : ℝ) * (4 * Δ / ((γ ε : ℝ) * ((K ε).1 : ℝ))) := by
            field_simp [ne_of_gt hγpos, ne_of_gt hKpos]
            <;> ring
      _ ≤ (1 / 2 : ℝ) * (ε : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hBudget' (by norm_num)
      _ = (ε : ℝ) ^ 2 / 2 := by ring
  have hKBound (ε : Accuracy) : ((K ε).1 : ℝ) ≤ 2 * iterationScale ε := by
    let q : ℝ := 4 * Δ / ((γ ε : ℝ) * (ε : ℝ) ^ 2)
    have hq : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg (γ ε).property.le (sq_nonneg _))
    have hceil := natCast_max_one_ceil_le_add_two q hq
    have hqEq : q = 4 * Δ / ((γ ε : ℝ) * (ε : ℝ) ^ 2) := rfl
    have hscale : iterationScale ε = 1 + q := by
      simp [iterationScale, q]
    rw [show ((K ε).1 : ℝ) =
      ((max 1 (Nat.ceil q) : ℕ) : ℝ) by simp [K, q]]
    rw [hscale]
    linarith
  have hScalePos (ε : Accuracy) : 0 < iterationScale ε := by
    dsimp [iterationScale]
    have : 0 ≤ 4 * Δ / ((γ ε : ℝ) * (ε : ℝ) ^ 2) :=
      div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg (γ ε).property.le (sq_nonneg _))
    linarith
  have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((K ε).1 : ℝ)),
      Real.norm_eq_abs, abs_of_pos (hScalePos ε)]
    exact hKBound ε
  have hConvergence (ε : Accuracy) :=
    Theorem_D3_online_VR_nonconvex_corrected_BTrack
      (K := K ε)
      (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) hE x0
      Llocal ℒlocal σ ω fStar hLower hSmooth hVariance hQuantizer
      (onlineNonconvexBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) b ε)
      (hAverageSmooth ε) (hStep ε)
  refine ⟨K, ?_⟩
  unfold ThreeEndpointComplexity
  refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
  · intro ε
    unfold NonconvexAccuracy
    refine ⟨(hConvergence ε).1, (hConvergence ε).2.trans ?_⟩
    have hsum := add_le_add (hOptimizationHalf ε) (hFloor ε)
    simpa [P, Δ, chosenBatch] using hsum
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    have hp0 : 0 ≤ p ε := (hp ε).1.le
    have hp1 : p ε ≤ 1 := (hp ε).2
    let payload : ℝ := p ε * (chosenBatch ε).1 +
      2 * (1 - p ε) * b0.1
    have hpayload : 0 ≤ payload := by
      dsimp [payload]
      exact add_nonneg (mul_nonneg hp0 (by positivity))
        (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
          (by positivity))
    have hbatch : 0 ≤ ((chosenBatch ε).1 : ℝ) := by positivity
    have hactual : 0 ≤ onlineOracleCallCount (chosenBatch ε) b0 (K ε) (p ε) := by
      unfold onlineOracleCallCount
      exact add_nonneg (by positivity)
        (mul_nonneg (by positivity) hpayload)
    have htarget : 0 < (chosenBatch ε).1 + iterationScale ε * payload := by
      exact add_pos_of_pos_of_nonneg (by exact_mod_cast (chosenBatch ε).2)
        (mul_nonneg (hScalePos ε).le hpayload)
    rw [Real.norm_eq_abs, abs_of_nonneg hactual,
      Real.norm_eq_abs, abs_of_pos htarget]
    change (chosenBatch ε).1 + ((K ε).1 : ℝ) * payload ≤
      2 * ((chosenBatch ε).1 + iterationScale ε * payload)
    have := mul_le_mul_of_nonneg_right (hKBound ε) hpayload
    nlinarith
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    let payload : ℝ := p ε * d.1 + (1 - p ε) * ζ
    have hpayload : 0 ≤ payload := by
      dsimp [payload]
      exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
        (mul_nonneg (sub_nonneg.mpr (hp ε).2) hζ)
    have hactual : 0 ≤ allWorkerCommunicationCount d (K ε) (p ε) ζ := by
      unfold allWorkerCommunicationCount
      exact add_nonneg (by positivity)
        (mul_nonneg (by positivity) hpayload)
    have htarget : 0 < (d.1 : ℝ) + iterationScale ε * payload := by
      exact add_pos_of_pos_of_nonneg (by exact_mod_cast d.2)
        (mul_nonneg (hScalePos ε).le hpayload)
    rw [Real.norm_eq_abs, abs_of_nonneg hactual,
      Real.norm_eq_abs, abs_of_pos htarget]
    change (d.1 : ℝ) + ((K ε).1 : ℝ) * payload ≤
      2 * ((d.1 : ℝ) + iterationScale ε * payload)
    have := mul_le_mul_of_nonneg_right (hKBound ε) hpayload
    nlinarith

/-- `book/MARINA/MARINA.json#/key_lemmas/21`, Corollary D.3, on the
nonfallback Eq. (6) B-track.  The supplied batch family is the source's
asymptotic representative; every algorithm parameter and cost below is indexed
by its pointwise-safe Eq. (41) inflation. -/
theorem Corollary_D3_online_VR_complexity_canonical_stepsize_corrected
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (b : Accuracy → Count) (p : Accuracy → ℝ)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess
          (A := onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (p ε) ω n b0)
            (p ε) (hp ε))
          hE x0 (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) b ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)))
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
      (onlineNonconvexBatchScheduleFromBase n b0
        (varianceAggregateSq σ) b ε) b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) b
    let chosenStep := fun ε => onlineDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) P
          (onlineCorrectedProofExactProcess
            (A := onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε))
            hE x0 (onlineNonconvexBatchScheduleFromBase_admissible n b0
              (varianceAggregateSq σ) b ε))
          (onlineProofExactPathLaw
            (A := onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε))) ε)
        (fun ε =>
          let ratio := onlineDensityBatchRatio d n b0 ζ (varianceAggregateSq σ)
            ((ε : ℝ) ^ 2)
          Δ / (ε : ℝ) ^ 2 * vrIterationBracket (rootMeanSquare Llocal)
            (rootMeanSquare ℒlocal) ω ratio n b0)
        (fun ε => onlineOracleCallCount (chosenBatch ε) b0 (K ε)
          (onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε)).refreshProbability)
        (fun ε => onlineNonconvexOracleScale Δ (rootMeanSquare Llocal)
          (rootMeanSquare ℒlocal) ω ζ (varianceAggregateSq σ) ε d n b0)
        (fun ε => allWorkerCommunicationCount d (K ε)
          (onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε)).refreshProbability ζ)
        (fun ε =>
          let ratio := onlineDensityBatchRatio d n b0 ζ (varianceAggregateSq σ)
            ((ε : ℝ) ^ 2)
          d.1 + Δ * ζ / (ε : ℝ) ^ 2 *
            vrIterationBracket (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) ω ratio n b0) := by
  dsimp
  have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := Real.sqrt_nonneg _
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hGeneralStep (ε : Accuracy) : OnlineVRStepsizeCondition
      (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (p ε) ω n b0)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0 :=
    onlineDensityCanonicalStepsize_condition
  have hSupplied :=
    Corollary_D3_online_VR_complexity_supplied_stepsize_corrected
      A hE x0 b p
      (fun ε => onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (p ε) ω n b0)
      hp Llocal ℒlocal σ ω fStar hLower hSmooth hVariance hQuantizer
      hAverageSmooth hBatchOrder hGeneralStep hSchedule
  unfold ThreeEndpointComplexity at hSupplied ⊢
  rcases hSupplied with ⟨hAccuracy, hIteration, hOracle, hCommunication⟩
  rcases hCommunication with ⟨hOracleCost, hCommunicationCost⟩
  have hOracleTargetEq :
      (fun ε : Accuracy => onlineNonconvexOracleScale
        (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar)
        (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
        (expectedDensity A.quantizer) (varianceAggregateSq σ) ε d n b0) =
      (fun ε : Accuracy =>
        varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2) +
          (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
              (ε : ℝ) ^ 2 *
            (b0.1 * vrIterationBracket (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) ω
              (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
                (varianceAggregateSq σ) ((ε : ℝ) ^ 2)) n b0)) := by
    funext ε
    exact online_nonconvex_oracle_scale_eq
      (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
      (expectedDensity A.quantizer) (varianceAggregateSq σ) ε hω
  rw [hOracleTargetEq]
  have hvariance : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  let chosenBatch : Accuracy → Count := onlineNonconvexBatchScheduleFromBase
    n b0 (varianceAggregateSq σ) b
  let varianceScale : Accuracy → ℝ := fun ε =>
    varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)
  let bracket : Accuracy → ℝ := fun ε =>
    vrIterationBracket (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
      (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
        (varianceAggregateSq σ) ((ε : ℝ) ^ 2)) n b0
  let targetIteration : Accuracy → ℝ := fun ε =>
    (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
      (ε : ℝ) ^ 2 * bracket ε
  let suppliedIteration : Accuracy → ℝ := fun ε =>
    1 + 4 *
      (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
      ((onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (p ε) ω n b0 : ℝ) * (ε : ℝ) ^ 2)
  have hChosenTheta : AccuracyTheta (fun ε => ((chosenBatch ε).1 : ℝ))
      varianceScale := by
    simpa [chosenBatch, varianceScale] using
      onlineNonconvexBatchScheduleFromBase_accuracyTheta n b0
        (varianceAggregateSq σ) hvariance b hBatchOrder
  have hGap : 0 ≤
      globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar :=
    sub_nonneg.mpr (hLower x0)
  by_cases hRegular :
      0 < globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar ∧
        0 < rootMeanSquare Llocal
  ·
      refine ⟨hAccuracy, hIteration, ?_⟩
      have hGapPos := hRegular.1
      have hLpos := hRegular.2
      have hScale : AccuracyBigO suppliedIteration targetIteration := by
        simpa [suppliedIteration, targetIteration, bracket, chosenBatch] using
          online_nonconvex_supplied_scale_bigO_canonical hp hLpos hℒ hω
            hvariance hGapPos hChosenTheta.1 (by simpa [chosenBatch] using hSchedule)
      have hIteration' : AccuracyIterationBigO
          (fun ε => ((hAccuracy ε).1 : ℝ)) targetIteration := by
        rcases hOracle with hzero | hbig
        · let ε₁ : Accuracy := ⟨1, by norm_num⟩
          have hz := hzero.1 ε₁
          have hpos : 0 < suppliedIteration ε₁ := by
            dsimp [suppliedIteration]
            have hdenom : 0 < (onlineDensityCanonicalStepsize
                (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε₁) ω n b0 : ℝ) *
                (ε₁ : ℝ) ^ 2 := mul_pos
              (onlineDensityCanonicalStepsize
                (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε₁) ω n b0).property
              (sq_pos_of_pos ε₁.property)
            have hquot : 0 < 4 *
                (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
                ((onlineDensityCanonicalStepsize
                  (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε₁) ω n b0 : ℝ) *
                  (ε₁ : ℝ) ^ 2) := div_pos (mul_pos (by norm_num) hGapPos) hdenom
            linarith
          exfalso
          exact (ne_of_gt hpos) hz
        · exact Or.inr (hbig.trans hScale)
      have hVar0 : ∀ᶠ ε in accuracyToZero, 0 ≤ varianceScale ε :=
        Filter.Eventually.of_forall fun ε => by dsimp [varianceScale]; positivity
      have hTarget0 : ∀ᶠ ε in accuracyToZero, 0 ≤ targetIteration ε :=
        Filter.Eventually.of_forall fun ε => by
          dsimp [targetIteration, bracket, vrIterationBracket]
          positivity
      have hSupplied0 (ε : Accuracy) : 0 ≤ suppliedIteration ε := by
        dsimp [suppliedIteration]
        have hdenom : 0 ≤ (onlineDensityCanonicalStepsize
            (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0 : ℝ) *
            (ε : ℝ) ^ 2 := mul_nonneg
          (onlineDensityCanonicalStepsize
            (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0).property.le
          (sq_nonneg _)
        have hquot : 0 ≤ 4 *
            (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
            ((onlineDensityCanonicalStepsize
              (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0 : ℝ) *
              (ε : ℝ) ^ 2) := div_nonneg (mul_nonneg (by norm_num) hGap) hdenom
        linarith
      have hBatch0 (ε : Accuracy) : 0 ≤ ((chosenBatch ε).1 : ℝ) := by positivity
      have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
        (hp ε).1 (hp ε).2 (expectedDensity_nonneg_of_unbiased hQuantizer)
        (by simpa [chosenBatch] using hSchedule ε)
      have hOracleTransport : AccuracyBigO
          (fun ε => (chosenBatch ε).1 + suppliedIteration ε *
            (p ε * (chosenBatch ε).1 + 2 * (1 - p ε) * b0.1))
          (fun ε => varianceScale ε + targetIteration ε * b0.1) := by
        apply accuracyBigO_add_mul_varying_payload
          (targetPayload := (b0.1 : ℝ)) (factor := 3)
          hChosenTheta.1 hScale hBatch0 hSupplied0 hVar0 hTarget0
        · intro ε
          exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
            (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hp ε).2))
              (by positivity))
        · exact_mod_cast b0.2
        · norm_num
        · intro ε
          simpa using (hPayload ε).2.1
      have hOracle' := hOracleCost.trans hOracleTransport
      have hζpos : 0 < expectedDensity A.quantizer := (hPayload ⟨1, by norm_num⟩).1
      have hConstRefl : AccuracyBigO (fun _ : Accuracy => (d.1 : ℝ))
          (fun _ : Accuracy => (d.1 : ℝ)) :=
        Asymptotics.isBigO_refl _ _
      have hCommTransport : AccuracyBigO
          (fun ε => (d.1 : ℝ) + suppliedIteration ε *
            (p ε * d.1 + (1 - p ε) * expectedDensity A.quantizer))
          (fun ε => (d.1 : ℝ) +
            targetIteration ε * expectedDensity A.quantizer) := by
        apply accuracyBigO_add_mul_varying_payload
          (targetPayload := expectedDensity A.quantizer) (factor := 2)
          hConstRefl hScale (fun _ => by positivity) hSupplied0
          (Filter.Eventually.of_forall fun _ => by positivity) hTarget0
        · intro ε
          exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
            (mul_nonneg (sub_nonneg.mpr (hp ε).2)
              (expectedDensity_nonneg_of_unbiased hQuantizer))
        · exact hζpos
        · norm_num
        · intro ε
          simpa using (hPayload ε).2.2
      have hCommunication' := hCommunicationCost.trans hCommTransport
      refine ⟨hIteration', ?_, ?_⟩
      · simpa [onlineDataWithParameters, chosenBatch, suppliedIteration,
          varianceScale, targetIteration, bracket, mul_assoc, mul_left_comm, mul_comm]
          using hOracle'
      · convert hCommunication' using 1 <;>
          ext ε <;>
          simp [onlineDataWithParameters, suppliedIteration, targetIteration, bracket] <;>
          ring
  · have hDegenerate :
        globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar = 0 ∨
          (0 < globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar ∧
            rootMeanSquare Llocal = 0) := by
      rcases hGap.eq_or_lt with hGapZero | hGapPos
      · exact Or.inl hGapZero.symm
      · exact Or.inr ⟨hGapPos, le_antisymm
          (not_lt.mp (fun hLpos => hRegular ⟨hGapPos, hLpos⟩)) hL⟩
    let K₁ : Count := ⟨1, by norm_num⟩
    refine ⟨fun _ => K₁, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ε
      rcases hDegenerate with hGapZero | ⟨hGapPos, hLzero⟩
      · unfold NonconvexAccuracy
        have hD3 := Theorem_D3_online_VR_nonconvex_corrected_BTrack (K := K₁)
          (onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (p ε) ω n b0)
            (p ε) (hp ε)) hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth
          hVariance hQuantizer
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) b ε)
          (hAverageSmooth ε) (hGeneralStep ε)
        refine ⟨hD3.1, hD3.2.trans ?_⟩
        have hFloor := onlineNonconvexBatchScheduleFromBase_variance_floor
          n b0 (varianceAggregateSq σ) hvariance b ε
        change 2 *
              (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
                ((onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
                  (rootMeanSquare ℒlocal) (p ε) ω n b0 : ℝ) * (K₁.1 : ℝ)) +
              varianceAggregateSq σ / (n.1 * (chosenBatch ε).1) ≤
            (ε : ℝ) ^ 2
        rw [hGapZero]
        have hFloor' : varianceAggregateSq σ / (n.1 * (chosenBatch ε).1) ≤
            (ε : ℝ) ^ 2 / 2 := by simpa [chosenBatch] using hFloor
        simpa using hFloor'.trans (by nlinarith [sq_nonneg (ε : ℝ)])
      · unfold NonconvexAccuracy
        have hD3 := Theorem_D3_online_VR_nonconvex_corrected_BTrack (K := K₁)
          (onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (p ε) ω n b0)
            (p ε) (hp ε)) hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth
          hVariance hQuantizer
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) b ε)
          (hAverageSmooth ε) (hGeneralStep ε)
        refine ⟨hD3.1, ?_⟩
        have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
          (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal fStar
          hLower hSmooth hLzero
        have heq : (fun z => ‖globalGradient
            (onlineLocalProblemCorrected ⟨A.problem, hE⟩)
            (uniformOutput (K := K₁)
              (onlineCorrectedProofExactProcess
                (A := onlineDataWithParameters A
                  (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
                    (rootMeanSquare ℒlocal) (p ε) ω n b0)
                  (p ε) (hp ε))
                hE x0 (onlineNonconvexBatchScheduleFromBase_admissible n b0
                  (varianceAggregateSq σ) b ε)) z)‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
    · rcases hDegenerate with hGapZero | ⟨hGapPos, hLzero⟩
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
              fStar) / (ε : ℝ) ^ 2 * bracket ε = 0
          rw [hGapZero]
          ring
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
              accuracyToZero)
      · rcases hℒ.eq_or_lt with hℒzero | hℒpos
        · refine Or.inl ⟨?_, ?_⟩
          · intro ε
            change (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
                fStar) / (ε : ℝ) ^ 2 * bracket ε = 0
            have hBracketZero : bracket ε = 0 := by
              simp [bracket, vrIterationBracket, hLzero, hℒzero.symm]
            rw [hBracketZero]
            ring
          · unfold AccuracyBigO
            simpa [K₁] using
              (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
                accuracyToZero)
        · refine Or.inr ?_
          have hvariancePos : 0 < varianceAggregateSq σ := by
            apply lt_of_le_of_ne hvariance
            intro hzero
            have hScaleZero : varianceScale = fun _ : Accuracy => (0 : ℝ) := by
              funext ε
              simp [varianceScale, ← hzero]
            have hEventuallyZero := hChosenTheta.1
            rw [hScaleZero] at hEventuallyZero
            have hEventuallyZero :
                ∀ᶠ ε in accuracyToZero, ((chosenBatch ε).1 : ℝ) = 0 := by
              exact Asymptotics.isBigO_zero_right_iff.mp hEventuallyZero
            rw [accuracyToZero, Filter.eventually_comap] at hEventuallyZero
            rcases Filter.eventually_atTop.1 hEventuallyZero with ⟨a, ha⟩
            let x : ℝ := max 1 a
            have hx : 0 < x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
            let ε : Accuracy := ⟨1 / x, one_div_pos.mpr hx⟩
            have hInv : ((ε : ℝ)⁻¹) = x := by
              dsimp [ε]
              simp [ne_of_gt hx]
            have hzeroBatch := ha x (le_max_right _ _) ε hInv
            have hpos : 0 < ((chosenBatch ε).1 : ℝ) := by
              exact_mod_cast (chosenBatch ε).2
            exact (ne_of_gt hpos) hzeroBatch
          let S : ℝ := rootMeanSquare ℒlocal * Real.sqrt
            ((1 + ω) * varianceAggregateSq σ /
              ((n.1 * b0.1) * (n.1 * b0.1)))
          have hS : 0 < S := by
            dsimp [S]
            apply mul_pos hℒpos
            apply Real.sqrt_pos.2
            have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
            have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
            exact div_pos (mul_pos (by linarith) hvariancePos)
              (mul_pos (mul_pos hn hb0) (mul_pos hn hb0))
          have hSmall := eventually_one_le_positive_inverse_square
            (mul_pos hGapPos hS)
          have hEpsilonSmall := eventually_one_le_positive_inverse_square zero_lt_one
          unfold AccuracyBigO
          rw [Asymptotics.isBigO_iff']
          refine ⟨1, zero_lt_one, ?_⟩
          filter_upwards [hSmall, hEpsilonSmall] with ε hSmallε hε
          have hεsq : (ε : ℝ) ^ 2 ≤ 1 := by
            have hsqpos : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos ε.property
            exact (one_le_inv₀ hsqpos).mp (by simpa [one_div] using hε)
          have hRatioLower : varianceAggregateSq σ / (n.1 * b0.1) ≤
              onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
                (varianceAggregateSq σ) ((ε : ℝ) ^ 2) := by
            apply le_trans ?_ (le_max_right _ _)
            have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
            have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
            have hden : 0 < (n.1 : ℝ) * b0.1 := mul_pos hn hb0
            have hdenε : 0 < (n.1 : ℝ) * b0.1 * (ε : ℝ) ^ 2 := by
              exact mul_pos hden (sq_pos_of_pos ε.property)
            rw [div_le_div_iff₀ hden hdenε]
            have hmul := mul_le_mul_of_nonneg_left hεsq
              (mul_nonneg hvariancePos.le hden.le)
            nlinarith [hmul]
          have hSqrtLower : Real.sqrt
                ((1 + ω) * varianceAggregateSq σ /
                  ((n.1 * b0.1) * (n.1 * b0.1))) ≤
              Real.sqrt ((1 + ω) *
                onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
                  (varianceAggregateSq σ) ((ε : ℝ) ^ 2) /
                (n.1 * b0.1)) := by
            apply Real.sqrt_le_sqrt
            have hcoef : 0 ≤ (1 + ω) / (n.1 * b0.1) := by positivity
            have hmul := mul_le_mul_of_nonneg_left hRatioLower hcoef
            convert hmul using 1 <;> field_simp <;> ring
          have hBracketLower : S ≤ bracket ε := by
            dsimp [S, bracket, vrIterationBracket]
            rw [hLzero]
            simpa using mul_le_mul_of_nonneg_left hSqrtLower hℒpos.le
          have hTargetLower : 1 ≤ targetIteration ε := by
            have hmul :
                (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
                    fStar) / (ε : ℝ) ^ 2 * S ≤
                  (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
                    fStar) / (ε : ℝ) ^ 2 * bracket ε :=
              mul_le_mul_of_nonneg_left hBracketLower
                (div_nonneg hGapPos.le (sq_nonneg (ε : ℝ)))
            dsimp [targetIteration]
            exact hSmallε.trans (by
              dsimp [S] at hmul ⊢
              convert hmul using 1 <;> ring)
          have hTargetNonneg : 0 ≤ targetIteration ε := hTargetLower.trans' zero_le_one
          rw [Real.norm_eq_abs,
            abs_of_nonneg (by positivity : 0 ≤ (K₁.1 : ℝ)),
            Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
          simpa [K₁] using hTargetLower
    · have hBatchOne : ∀ ε, 1 ≤ ((chosenBatch ε).1 : ℝ) := by
        intro ε
        exact_mod_cast (chosenBatch ε).2
      let payload : Accuracy → ℝ := fun ε =>
        p ε * (chosenBatch ε).1 + 2 * (1 - p ε) * b0.1
      have hPayloadNonneg : ∀ ε, 0 ≤ payload ε := by
        intro ε
        dsimp [payload]
        exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hp ε).2))
            (by positivity))
      have hPayloadBound : ∀ ε, payload ε ≤ 3 * b0.1 := by
        intro ε
        simpa [payload] using
          (online_density_schedule_payload_bounds (hp ε).1 (hp ε).2
            (expectedDensity_nonneg_of_unbiased hQuantizer)
            (by simpa [chosenBatch] using hSchedule ε)).2.1
      have hActualO : AccuracyBigO
          (fun ε => ((chosenBatch ε).1 : ℝ) + payload ε) varianceScale :=
        accuracyBigO_batch_add_bounded_payload hChosenTheta.1 hBatchOne
          hPayloadNonneg hPayloadBound (by positivity)
      have hTargetO : AccuracyBigO varianceScale
          (fun ε => varianceScale ε +
            (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
              (ε : ℝ) ^ 2 * (b0.1 * bracket ε)) := by
        unfold AccuracyBigO
        rw [Asymptotics.isBigO_iff']
        refine ⟨1, zero_lt_one, Filter.Eventually.of_forall ?_⟩
        intro ε
        have hV : 0 ≤ varianceScale ε := by
          dsimp [varianceScale]
          positivity
        have hExtra : 0 ≤
            (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) /
              (ε : ℝ) ^ 2 * (b0.1 * bracket ε) := by
          dsimp [bracket, vrIterationBracket]
          positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hV, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg hV hExtra)]
        linarith
      have hOracleOneRound := hActualO.trans hTargetO
      convert hOracleOneRound using 1 <;>
        ext ε <;> simp [onlineOracleCallCount, K₁, payload, onlineDataWithParameters,
          targetIteration, varianceScale, bracket] <;> ring
    · let commPayload : Accuracy → ℝ := fun ε =>
        p ε * d.1 + (1 - p ε) * expectedDensity A.quantizer
      unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff']
      let C : ℝ := 1 + 2 * expectedDensity A.quantizer / d.1
      have hC : 0 < C := by
        dsimp [C]
        have hζ : 0 ≤ expectedDensity A.quantizer :=
          expectedDensity_nonneg_of_unbiased hQuantizer
        have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
        have hq : 0 ≤ 2 * expectedDensity A.quantizer / d.1 :=
          div_nonneg (mul_nonneg (by norm_num) hζ) hd.le
        linarith
      refine ⟨C, hC, Filter.Eventually.of_forall ?_⟩
      intro ε
      have hPayload := online_density_schedule_payload_bounds
        (hp ε).1 (hp ε).2 (expectedDensity_nonneg_of_unbiased hQuantizer)
        (by simpa [chosenBatch] using hSchedule ε)
      have hActualNonneg : 0 ≤ (d.1 : ℝ) + commPayload ε := by
        dsimp [commPayload]
        exact add_nonneg (by positivity)
          (add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
            (mul_nonneg (sub_nonneg.mpr (hp ε).2)
              (expectedDensity_nonneg_of_unbiased hQuantizer)))
      have hTargetNonneg : 0 ≤ (d.1 : ℝ) +
          (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) *
            expectedDensity A.quantizer / (ε : ℝ) ^ 2 * bracket ε := by
        have hBracket0 : 0 ≤ bracket ε := by
          dsimp [bracket, vrIterationBracket]
          positivity
        exact add_nonneg (by positivity)
          (mul_nonneg
            (div_nonneg
              (mul_nonneg hGap (expectedDensity_nonneg_of_unbiased hQuantizer))
              (sq_nonneg _)) hBracket0)
      have hExtraNonneg : 0 ≤
          (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) *
            expectedDensity A.quantizer / (ε : ℝ) ^ 2 * bracket ε := by
        have hBracket0 : 0 ≤ bracket ε := by
          dsimp [bracket, vrIterationBracket]
          positivity
        exact mul_nonneg
          (div_nonneg
            (mul_nonneg hGap (expectedDensity_nonneg_of_unbiased hQuantizer))
            (sq_nonneg _)) hBracket0
      suffices hFinal : ‖(d.1 : ℝ) + commPayload ε‖ ≤ C *
        ‖(d.1 : ℝ) +
          (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) *
            expectedDensity A.quantizer / (ε : ℝ) ^ 2 * bracket ε‖ by
        simpa [allWorkerCommunicationCount, K₁, commPayload,
          onlineDataWithParameters, bracket] using hFinal
      rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg,
        Real.norm_eq_abs, abs_of_nonneg hTargetNonneg]
      have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
      have hBound : commPayload ε ≤ 2 * expectedDensity A.quantizer := by
        simpa [commPayload] using hPayload.2.2
      dsimp [C]
      calc
        (d.1 : ℝ) + commPayload ε ≤ d.1 + 2 * expectedDensity A.quantizer := by linarith
        _ = (1 + 2 * expectedDensity A.quantizer / d.1) * d.1 := by
          field_simp [ne_of_gt hd]
        _ ≤ (1 + 2 * expectedDensity A.quantizer / d.1) *
            ((d.1 : ℝ) +
              (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar) *
                expectedDensity A.quantizer / (ε : ℝ) ^ 2 * bracket ε) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hExtraNonneg) hC.le

/-- The supplied-stepsize form of Corollary D.4.  The geometric horizon keeps
the reciprocal of the actually supplied contraction `γ(ε) * μ`; unlike the
canonical specialization below, it therefore does not turn the source's upper
stepsize restrictions into an unstated lower bound.  The executed batch is the
pointwise-safe Eq. (49) inflation and consumes half of the target accuracy. -/
theorem Corollary_D4_online_VR_PL_complexity_supplied_stepsize_corrected
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 xStar : Point d) (b : Accuracy → Count) (p : Accuracy → ℝ)
    (γ : Accuracy → PositiveStepsize)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hPL : SatisfiesPL (onlineLocalProblemCorrected ⟨A.problem, hE⟩) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess
          (A := onlineDataWithParameters A (γ ε) (p ε) (hp ε))
          hE x0 (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ b ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * μ * (ε : ℝ))))
    (hStep : ∀ ε, OnlineVRPLStepsizeCondition (γ ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
      (onlinePLBatchScheduleFromBase n b0
        (varianceAggregateSq σ) μ b ε) b0) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ b
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - globalObjective P xStar
    let iterationScale := fun ε : Accuracy =>
      1 + max 0
        (Real.log (2 * Δ / (ε : ℝ)) / ((γ ε : ℝ) * (μ : ℝ)))
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => PLAccuracy (K ε) P
          (onlineCorrectedProofExactProcess
            (A := onlineDataWithParameters A (γ ε) (p ε) (hp ε))
            hE x0 (onlinePLBatchScheduleFromBase_admissible n b0
              (varianceAggregateSq σ) μ b ε))
          (onlineProofExactPathLaw
            (A := onlineDataWithParameters A (γ ε) (p ε) (hp ε))) xStar ε)
        iterationScale
        (fun ε => onlineOracleCallCount (chosenBatch ε) b0 (K ε) (p ε))
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (p ε * (chosenBatch ε).1 + 2 * (1 - p ε) * b0.1))
        (fun ε => allWorkerCommunicationCount d (K ε) (p ε) ζ)
        (fun ε => d.1 + iterationScale ε *
          (p ε * d.1 + (1 - p ε) * ζ)) := by
  dsimp
  let chosenBatch := onlinePLBatchScheduleFromBase n b0
    (varianceAggregateSq σ) μ b
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective P x0 - globalObjective P xStar
  let contractionScale : Accuracy → ℝ := fun ε =>
    max 0 (Real.log (2 * Δ / (ε : ℝ)) / ((γ ε : ℝ) * (μ : ℝ)))
  let iterationScale : Accuracy → ℝ := fun ε => 1 + contractionScale ε
  let K : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (contractionScale ε)), by omega⟩
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ, P]
    exact sub_nonneg.mpr (hPL.1 x0)
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hvariance : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hFloor (ε : Accuracy) :
      varianceAggregateSq σ / (n.1 * (chosenBatch ε).1 * μ) ≤
        (ε : ℝ) / 2 := by
    simpa [chosenBatch] using
      onlinePLBatchScheduleFromBase_variance_floor n b0
        (varianceAggregateSq σ) μ hvariance μ.property b ε
  have hcPos (ε : Accuracy) : 0 < (γ ε : ℝ) * (μ : ℝ) :=
    mul_pos (γ ε).property μ.property
  have hcOne (ε : Accuracy) : (γ ε : ℝ) * (μ : ℝ) ≤ 1 := by
    have htwice := (hStep ε).2
    have hpOne := (hp ε).2
    nlinarith
  have hContract (ε : Accuracy) :
      (1 - (γ ε : ℝ) * (μ : ℝ)) ^ (K ε).1 * Δ ≤ (ε : ℝ) / 2 := by
    rcases hΔ.eq_or_lt with hΔzero | hΔpos
    · calc
        (1 - (γ ε : ℝ) * (μ : ℝ)) ^ (K ε).1 * Δ = 0 :=
          mul_eq_zero_of_right _ hΔzero.symm
        _ ≤ (ε : ℝ) / 2 := (div_pos ε.property (by norm_num)).le
    · by_cases hsmall : (ε : ℝ) < 2 * Δ
      · have hratio : 1 < 2 * Δ / (ε : ℝ) :=
          (one_lt_div ε.property).2 hsmall
        have hlogPos : 0 < Real.log (2 * Δ / (ε : ℝ)) :=
          Real.log_pos hratio
        have hraw : 0 ≤ Real.log (2 * Δ / (ε : ℝ)) /
            ((γ ε : ℝ) * (μ : ℝ)) :=
          div_nonneg hlogPos.le (hcPos ε).le
        have hScalar := positive_geometric_ceiling_schedule_half_budget
          Δ ((γ ε : ℝ) * (μ : ℝ)) 1 hΔpos (hcPos ε) (hcOne ε)
            (by norm_num)
        simpa [K, contractionScale, max_eq_right hraw] using hScalar.1 ε
      · have hbase : 0 ≤ 1 - (γ ε : ℝ) * (μ : ℝ) :=
          sub_nonneg.mpr (hcOne ε)
        have hbaseOne : 1 - (γ ε : ℝ) * (μ : ℝ) ≤ 1 := by
          linarith [hcPos ε]
        calc
          (1 - (γ ε : ℝ) * (μ : ℝ)) ^ (K ε).1 * Δ ≤ 1 * Δ :=
            mul_le_mul_of_nonneg_right
              (pow_le_one₀ hbase hbaseOne) hΔ
          _ = Δ := one_mul Δ
          _ ≤ (ε : ℝ) / 2 := by linarith
  have hScalePos (ε : Accuracy) : 0 < iterationScale ε := by
    dsimp [iterationScale, contractionScale]
    linarith [le_max_left (0 : ℝ)
      (Real.log (2 * Δ / (ε : ℝ)) / ((γ ε : ℝ) * (μ : ℝ)))]
  have hKBound (ε : Accuracy) :
      ((K ε).1 : ℝ) ≤ 2 * iterationScale ε := by
    have hq : 0 ≤ contractionScale ε := by
      dsimp [contractionScale]
      exact le_max_left _ _
    have hceil := natCast_max_one_ceil_le_add_two (contractionScale ε) hq
    change ((max 1 (Nat.ceil (contractionScale ε)) : ℕ) : ℝ) ≤
      2 * (1 + contractionScale ε)
    linarith
  have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((K ε).1 : ℝ)),
      Real.norm_eq_abs, abs_of_pos (hScalePos ε)]
    exact hKBound ε
  have hConvergence (ε : Accuracy) :=
    Theorem_D4_online_VR_PL_corrected_BTrack
      (K := K ε)
      (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) hE x0 xStar
      Llocal ℒlocal σ ω fStar μ hLower hSmooth hVariance hPL hQuantizer
      (onlinePLBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) μ b ε)
      (hAverageSmooth ε) (hStep ε)
  refine ⟨K, ?_⟩
  unfold ThreeEndpointComplexity
  refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
  · intro ε
    unfold PLAccuracy
    refine ⟨(hConvergence ε).1, (hConvergence ε).2.trans ?_⟩
    have hsum := add_le_add (hContract ε) (hFloor ε)
    simpa [P, Δ, chosenBatch] using hsum
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    let payload : ℝ := p ε * (chosenBatch ε).1 +
      2 * (1 - p ε) * b0.1
    have hpayload : 0 ≤ payload := by
      dsimp [payload]
      exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
        (mul_nonneg (mul_nonneg (by norm_num)
          (sub_nonneg.mpr (hp ε).2)) (by positivity))
    have hactual : 0 ≤
        onlineOracleCallCount (chosenBatch ε) b0 (K ε) (p ε) := by
      unfold onlineOracleCallCount
      exact add_nonneg (by positivity) (mul_nonneg (by positivity) hpayload)
    have htarget : 0 <
        (chosenBatch ε).1 + iterationScale ε * payload :=
      add_pos_of_pos_of_nonneg (by exact_mod_cast (chosenBatch ε).2)
        (mul_nonneg (hScalePos ε).le hpayload)
    rw [Real.norm_eq_abs, abs_of_nonneg hactual,
      Real.norm_eq_abs, abs_of_pos htarget]
    change (chosenBatch ε).1 + ((K ε).1 : ℝ) * payload ≤
      2 * ((chosenBatch ε).1 + iterationScale ε * payload)
    have := mul_le_mul_of_nonneg_right (hKBound ε) hpayload
    nlinarith
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    let payload : ℝ := p ε * d.1 + (1 - p ε) * ζ
    have hpayload : 0 ≤ payload := by
      dsimp [payload]
      exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
        (mul_nonneg (sub_nonneg.mpr (hp ε).2) hζ)
    have hactual : 0 ≤
        allWorkerCommunicationCount d (K ε) (p ε) ζ := by
      unfold allWorkerCommunicationCount
      exact add_nonneg (by positivity) (mul_nonneg (by positivity) hpayload)
    have htarget : 0 < (d.1 : ℝ) + iterationScale ε * payload :=
      add_pos_of_pos_of_nonneg (by exact_mod_cast d.2)
        (mul_nonneg (hScalePos ε).le hpayload)
    rw [Real.norm_eq_abs, abs_of_nonneg hactual,
      Real.norm_eq_abs, abs_of_pos htarget]
    change (d.1 : ℝ) + ((K ε).1 : ℝ) * payload ≤
      2 * ((d.1 : ℝ) + iterationScale ε * payload)
    have := mul_le_mul_of_nonneg_right (hKBound ε) hpayload
    nlinarith

set_option maxHeartbeats 800000 in
/-- `book/MARINA/MARINA.json#/key_lemmas/23`, Corollary D.4, corrected
to the explicit nonfallback Eq. (6) B-track.  As in proof step 14 of Theorem
D.4, all parameters execute the pointwise-safe Eq. (49) batch inflation. -/
theorem Corollary_D4_online_VR_PL_complexity_canonical_stepsize_corrected
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 xStar : Point d) (b : Accuracy → Count) (p : Accuracy → ℝ)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hPL : SatisfiesPL (onlineLocalProblemCorrected ⟨A.problem, hE⟩) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess
          (A := onlineDataWithParameters A
            (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
            (p ε) (hp ε))
          hE x0 (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ b ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * μ * (ε : ℝ))))
    (hSchedule : ∀ ε, p ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
      (onlinePLBatchScheduleFromBase n b0
        (varianceAggregateSq σ) μ b ε) b0) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ b
    let chosenStep := fun ε => onlinePLDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω μ n b0
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - globalObjective P xStar
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => PLAccuracy (K ε) P
          (onlineCorrectedProofExactProcess
            (A := onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε))
            hE x0 (onlinePLBatchScheduleFromBase_admissible n b0
              (varianceAggregateSq σ) μ b ε))
          (onlineProofExactPathLaw
            (A := onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε))) xStar ε)
        (fun ε =>
          let ratio := onlineDensityBatchRatio d n b0 ζ (varianceAggregateSq σ)
            (μ * (ε : ℝ))
          max (1 / (onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε)).refreshProbability)
            (vrIterationBracket (rootMeanSquare Llocal)
            (rootMeanSquare ℒlocal) ω ratio n b0 / μ) *
            Real.log (Δ / (ε : ℝ)))
        (fun ε => onlineOracleCallCount (chosenBatch ε) b0 (K ε)
          (onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε)).refreshProbability)
        (fun ε => onlinePLOracleScale (rootMeanSquare Llocal)
          (rootMeanSquare ℒlocal) ω μ
          (onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε)).refreshProbability
          ζ (varianceAggregateSq σ)
          ε (Real.log (Δ / (ε : ℝ))) d n b0)
        (fun ε => allWorkerCommunicationCount d (K ε)
          (onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε)).refreshProbability ζ)
        (fun ε =>
          let ratio := onlineDensityBatchRatio d n b0 ζ (varianceAggregateSq σ)
            (μ * (ε : ℝ))
          let factor := max
            (1 / (onlineDataWithParameters A (chosenStep ε) (p ε) (hp ε)).refreshProbability)
            (vrIterationBracket
            (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω ratio n b0 / μ)
          d.1 + ζ * factor * Real.log (Δ / (ε : ℝ))) := by
  dsimp
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hGeneralStep (ε : Accuracy) : OnlineVRPLStepsizeCondition
      (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω μ n b0 :=
    onlinePLDensityCanonicalStepsize_condition (hp ε)
  have hSupplied :=
    Corollary_D4_online_VR_PL_complexity_supplied_stepsize_corrected
      A hE x0 xStar b p
      (fun ε => onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
      hp Llocal ℒlocal σ ω fStar μ hLower hSmooth hVariance hPL
      hQuantizer hAverageSmooth hBatchOrder hGeneralStep hSchedule
  unfold ThreeEndpointComplexity at hSupplied ⊢
  rcases hSupplied with ⟨hAccuracy, hIteration, hOracle, hCommunication⟩
  have hOracleTargetEq :
      (fun ε : Accuracy => onlinePLOracleScale
        (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω (μ : ℝ)
        (onlineDataWithParameters A
          (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
            (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
          (p ε) (hp ε)).refreshProbability
        (expectedDensity A.quantizer) (varianceAggregateSq σ)
        (ε : ℝ)
        (Real.log
          ((globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
              globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) /
            (ε : ℝ))) d n b0) =
      (fun ε : Accuracy =>
        varianceAggregateSq σ / (n.1 * (μ : ℝ) * (ε : ℝ)) + b0.1 *
          max (1 / (onlineDataWithParameters A
            (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
            (p ε) (hp ε)).refreshProbability)
            (vrIterationBracket (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
              (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
                (varianceAggregateSq σ) ((μ : ℝ) * (ε : ℝ))) n b0 /
              (μ : ℝ)) *
          Real.log
            ((globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
                globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) /
              (ε : ℝ))) := by
    funext ε
    simpa [onlineDataWithParameters] using online_pl_oracle_scale_eq
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω (μ : ℝ) (p ε)
      (expectedDensity A.quantizer) (varianceAggregateSq σ) (ε : ℝ)
      (Real.log
        ((globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
            globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) /
          (ε : ℝ))) hω μ.property
  rw [hOracleTargetEq]
  rcases hCommunication with ⟨hOracleCost, hCommunicationCost⟩
  have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := Real.sqrt_nonneg _
  have hvariance : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  let chosenBatch : Accuracy → Count := onlinePLBatchScheduleFromBase n b0
    (varianceAggregateSq σ) μ b
  let varianceScale : Accuracy → ℝ := fun ε =>
    varianceAggregateSq σ / (n.1 * (μ : ℝ) * (ε : ℝ))
  let factor : Accuracy → ℝ := fun ε =>
    max (1 / p ε)
      (vrIterationBracket (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
        (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
          (varianceAggregateSq σ) ((μ : ℝ) * (ε : ℝ))) n b0 / (μ : ℝ))
  let targetIteration : Accuracy → ℝ := fun ε => factor ε *
    Real.log
      ((globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
          globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) /
        (ε : ℝ))
  let suppliedIteration : Accuracy → ℝ := fun ε => 1 + max 0
    (Real.log
        (2 * (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
          globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) /
          (ε : ℝ)) /
      ((onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (p ε) ω μ n b0 : ℝ) * (μ : ℝ)))
  have hChosenTheta : AccuracyTheta (fun ε => ((chosenBatch ε).1 : ℝ))
      varianceScale := by
    simpa [chosenBatch, varianceScale] using
      onlinePLBatchScheduleFromBase_accuracyTheta n b0
        (varianceAggregateSq σ) μ hvariance μ.property b hBatchOrder
  have hGap : 0 ≤
      globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
        globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar :=
    sub_nonneg.mpr (hPL.1 x0)
  rcases hGap.eq_or_lt with hGapZero | hGapPos
  · refine ⟨hAccuracy, hIteration, ?_⟩
    have hGapEq :
        globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
          globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar = 0 :=
      hGapZero.symm
    have hSuppliedEq : suppliedIteration = fun _ : Accuracy => (1 : ℝ) := by
      funext ε
      dsimp [suppliedIteration]
      rw [hGapEq]
      norm_num
    have hTargetEq : targetIteration = fun _ : Accuracy => (0 : ℝ) := by
      funext ε
      dsimp [targetIteration]
      rw [hGapEq]
      norm_num
    have hOracleSupplied : AccuracyIterationBigO
        (fun ε => ((hAccuracy ε).1 : ℝ)) suppliedIteration := by
      simpa [suppliedIteration] using hOracle
    have hKOne : AccuracyBigO (fun ε => ((hAccuracy ε).1 : ℝ)) (fun _ => (1 : ℝ)) := by
      rcases hOracleSupplied with hzero | hbig
      · exact hzero.2
      · rw [hSuppliedEq] at hbig
        exact hbig
    refine ⟨?_, ?_, ?_⟩
    · change AccuracyIterationBigO
        (fun ε => ((hAccuracy ε).1 : ℝ)) targetIteration
      exact Or.inl ⟨fun ε => congrFun hTargetEq ε, hKOne⟩
    · let payload : Accuracy → ℝ := fun ε =>
        p ε * (chosenBatch ε).1 + 2 * (1 - p ε) * b0.1
      have hBatchOne : ∀ ε, 1 ≤ ((chosenBatch ε).1 : ℝ) := by
        intro ε
        exact_mod_cast (chosenBatch ε).2
      have hPayloadNonneg : ∀ ε, 0 ≤ payload ε := by
        intro ε
        dsimp [payload]
        exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hp ε).2))
            (by positivity))
      have hPayloadBound : ∀ ε, payload ε ≤ 3 * b0.1 := by
        intro ε
        simpa [payload] using
          (online_density_schedule_payload_bounds (hp ε).1 (hp ε).2
            (expectedDensity_nonneg_of_unbiased hQuantizer)
            (by simpa [chosenBatch] using hSchedule ε)).2.1
      have hActualO : AccuracyBigO
          (fun ε => ((chosenBatch ε).1 : ℝ) + payload ε) varianceScale :=
        accuracyBigO_batch_add_bounded_payload hChosenTheta.1 hBatchOne
          hPayloadNonneg hPayloadBound (by positivity)
      have hOracleCost' := hOracleCost
      change AccuracyBigO
        (fun ε => onlineOracleCallCount (chosenBatch ε) b0 (hAccuracy ε) (p ε))
        (fun ε => ((chosenBatch ε).1 : ℝ) + suppliedIteration ε * payload ε) at hOracleCost'
      have hMid : AccuracyBigO
          (fun ε => ((chosenBatch ε).1 : ℝ) + suppliedIteration ε * payload ε)
          varianceScale := by
        rw [hSuppliedEq]
        simpa using hActualO
      have hOracleOne := hOracleCost'.trans hMid
      have hTargetO : AccuracyBigO varianceScale
          (fun ε => varianceScale ε + b0.1 * targetIteration ε) := by
        rw [hTargetEq]
        simpa using (Asymptotics.isBigO_refl varianceScale accuracyToZero)
      have hFinal := hOracleOne.trans hTargetO
      convert hFinal using 1 <;>
        ext ε <;>
        simp [onlineOracleCallCount, onlineDataWithParameters, chosenBatch,
          varianceScale, targetIteration, factor, hGapEq] <;>
        ring
    · let commPayload : Accuracy → ℝ := fun ε =>
        p ε * d.1 + (1 - p ε) * expectedDensity A.quantizer
      have hCommOne : AccuracyBigO
          (fun ε => (d.1 : ℝ) + commPayload ε) (fun _ => (d.1 : ℝ)) := by
        unfold AccuracyBigO
        rw [Asymptotics.isBigO_iff']
        let C : ℝ := 1 + 2 * expectedDensity A.quantizer / d.1
        have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
        have hC : 0 < C := by
          dsimp [C]
          have hq : 0 ≤ 2 * expectedDensity A.quantizer / d.1 :=
            div_nonneg
              (mul_nonneg (by norm_num) (expectedDensity_nonneg_of_unbiased hQuantizer))
              hd.le
          linarith
        refine ⟨C, hC, Filter.Eventually.of_forall ?_⟩
        intro ε
        have hPayload := online_density_schedule_payload_bounds
          (hp ε).1 (hp ε).2 (expectedDensity_nonneg_of_unbiased hQuantizer)
          (by simpa [chosenBatch] using hSchedule ε)
        have hnonneg : 0 ≤ (d.1 : ℝ) + commPayload ε := by
          dsimp [commPayload]
          exact add_nonneg (by positivity)
            (add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
              (mul_nonneg (sub_nonneg.mpr (hp ε).2)
                (expectedDensity_nonneg_of_unbiased hQuantizer)))
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs,
          abs_of_pos hd]
        have hBound : commPayload ε ≤ 2 * expectedDensity A.quantizer := by
          simpa [commPayload] using hPayload.2.2
        dsimp [C]
        calc
          (d.1 : ℝ) + commPayload ε ≤ d.1 + 2 * expectedDensity A.quantizer := by
            linarith
          _ = (1 + 2 * expectedDensity A.quantizer / d.1) * d.1 := by
            field_simp [ne_of_gt hd]
      have hCommunicationCost' := hCommunicationCost
      change AccuracyBigO
        (fun ε => allWorkerCommunicationCount d (hAccuracy ε) (p ε)
          (expectedDensity A.quantizer))
        (fun ε => (d.1 : ℝ) + suppliedIteration ε * commPayload ε) at hCommunicationCost'
      have hMid : AccuracyBigO
          (fun ε => (d.1 : ℝ) + suppliedIteration ε * commPayload ε)
          (fun _ => (d.1 : ℝ)) := by
        rw [hSuppliedEq]
        simpa using hCommOne
      have hCommSupplied := hCommunicationCost'.trans hMid
      convert hCommSupplied using 1
      · ext ε
        rw [hGapEq]
        norm_num [onlineDataWithParameters]
  · have hLpos : 0 < rootMeanSquare Llocal := by
      rcases hL.eq_or_lt with hLzero | hLpos
      · have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
          (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal fStar
          hLower hSmooth hLzero.symm
        have hPLx := hPL.2 x0
        rw [hGradZero] at hPLx
        norm_num at hPLx
        have hprod : 0 < 2 * (μ : ℝ) *
            (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
              globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) :=
          mul_pos (mul_pos (by norm_num) μ.property) hGapPos
        exact (not_lt_of_ge hPLx hprod).elim
      · exact hLpos
    have hScale : AccuracyBigO suppliedIteration targetIteration := by
      simpa [suppliedIteration, targetIteration, factor, chosenBatch] using
        online_pl_supplied_scale_bigO_canonical hp hLpos hℒ hω hvariance
          hGapPos hChosenTheta.1 (by simpa [chosenBatch] using hSchedule)
    have hOracleSupplied : AccuracyIterationBigO
        (fun ε => ((hAccuracy ε).1 : ℝ)) suppliedIteration := by
      simpa [suppliedIteration] using hOracle
    have hIteration' : AccuracyIterationBigO
        (fun ε => ((hAccuracy ε).1 : ℝ)) targetIteration := by
      rcases hOracleSupplied with hzero | hbig
      · let ε₁ : Accuracy := ⟨1, by norm_num⟩
        have hz := hzero.1 ε₁
        have hpos : 0 < suppliedIteration ε₁ := by
          dsimp [suppliedIteration]
          linarith [le_max_left (0 : ℝ)
            (Real.log
                (2 * (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
                  globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) /
                  (ε₁ : ℝ)) /
              ((onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
                (rootMeanSquare ℒlocal) (p ε₁) ω μ n b0 : ℝ) * (μ : ℝ)))]
        exact (ne_of_gt hpos hz).elim
      · exact Or.inr (hbig.trans hScale)
    have hVar0 : ∀ᶠ ε in accuracyToZero, 0 ≤ varianceScale ε :=
      Filter.Eventually.of_forall fun ε => by
        dsimp [varianceScale]
        exact div_nonneg hvariance
          (mul_nonneg (mul_nonneg (by positivity) μ.property.le) ε.property.le)
    have hTarget0 : ∀ᶠ ε in accuracyToZero, 0 ≤ targetIteration ε := by
      filter_upwards [eventually_one_le_log_gap_div_accuracy hGapPos] with ε hlog
      dsimp [targetIteration, factor]
      exact mul_nonneg
        ((div_pos zero_lt_one (hp ε).1).le.trans (le_max_left _ _)) (by linarith)
    have hSupplied0 : ∀ ε, 0 ≤ suppliedIteration ε := by
      intro ε
      dsimp [suppliedIteration]
      linarith [le_max_left (0 : ℝ)
        (Real.log
            (2 * (globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
              globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar) /
              (ε : ℝ)) /
          ((onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
            (rootMeanSquare ℒlocal) (p ε) ω μ n b0 : ℝ) * (μ : ℝ)))]
    have hBatch0 : ∀ ε, 0 ≤ ((chosenBatch ε).1 : ℝ) := fun _ => by positivity
    have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
      (hp ε).1 (hp ε).2 (expectedDensity_nonneg_of_unbiased hQuantizer)
      (by simpa [chosenBatch] using hSchedule ε)
    have hOracleTransport : AccuracyBigO
        (fun ε => (chosenBatch ε).1 + suppliedIteration ε *
          (p ε * (chosenBatch ε).1 + 2 * (1 - p ε) * b0.1))
        (fun ε => varianceScale ε + targetIteration ε * b0.1) := by
      apply accuracyBigO_add_mul_varying_payload
        (targetPayload := (b0.1 : ℝ)) (factor := 3)
        hChosenTheta.1 hScale hBatch0 hSupplied0 hVar0 hTarget0
      · intro ε
        exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hp ε).2))
            (by positivity))
      · exact_mod_cast b0.2
      · norm_num
      · intro ε
        simpa using (hPayload ε).2.1
    have hOracle' := hOracleCost.trans hOracleTransport
    have hζpos : 0 < expectedDensity A.quantizer := (hPayload ⟨1, by norm_num⟩).1
    have hCommTransport : AccuracyBigO
        (fun ε => (d.1 : ℝ) + suppliedIteration ε *
          (p ε * d.1 + (1 - p ε) * expectedDensity A.quantizer))
        (fun ε => (d.1 : ℝ) +
          targetIteration ε * expectedDensity A.quantizer) := by
      apply accuracyBigO_add_mul_varying_payload
        (targetPayload := expectedDensity A.quantizer) (factor := 2)
        (Asymptotics.isBigO_refl _ _) hScale (fun _ => by positivity) hSupplied0
        (Filter.Eventually.of_forall fun _ => by positivity) hTarget0
      · intro ε
        exact add_nonneg (mul_nonneg (hp ε).1.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr (hp ε).2)
            (expectedDensity_nonneg_of_unbiased hQuantizer))
      · exact hζpos
      · norm_num
      · intro ε
        simpa using (hPayload ε).2.2
    have hCommunication' := hCommunicationCost.trans hCommTransport
    refine ⟨hAccuracy, hIteration, hIteration', ?_, ?_⟩
    · simpa [onlineDataWithParameters, chosenBatch, suppliedIteration,
        varianceScale, targetIteration, factor, mul_assoc, mul_left_comm, mul_comm]
        using hOracle'
    · convert hCommunication' using 1 <;>
        ext ε <;>
        simp [onlineDataWithParameters, suppliedIteration, targetIteration, factor] <;>
        ring

/-- Conditional D.3 endpoint for a batch family whose Eq. (41) floor has
already been budgeted pointwise.  The source-facing theorem below constructs
such a family, so this premise is not exposed there. -/
theorem Theorem_D3_online_VR_complexity_endpoints_corrected_of_batch_accuracy
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (b : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess A hE x0 (hBatch ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)))
    (hBatchAccuracy : ∀ ε : Accuracy,
      varianceAggregateSq σ / (n.1 * (b ε).1) ≤ (ε : ℝ) ^ 2 / 2)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) P
          (onlineCorrectedProofExactProcess A hE x0 (hBatch ε))
          (onlineProofExactPathLaw (A := A)) ε)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
        (fun ε => onlineOracleCallCount (b ε) b0 (K ε) A.refreshProbability)
        (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2) +
          Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * varianceAggregateSq σ /
              (n.1 * (ε : ℝ) ^ 2) +
              (1 - A.refreshProbability) * b0.1))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  have hGapNonneg : 0 ≤
      globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar :=
    sub_nonneg.mpr (hLower x0)
  dsimp
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective P x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
      (ω * rootMeanSquare Llocal ^ 2 +
        (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let varianceScale : Accuracy → ℝ := fun ε =>
    varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)
  let iterationScale : Accuracy → ℝ := fun ε =>
    Δ / (ε : ℝ) ^ 2 * bracket
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hVarianceScaleNonneg : ∀ ε, 0 ≤ varianceScale ε := by
    intro ε
    have hVar : 0 ≤ varianceAggregateSq σ := by
      unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
      simp only [Fintype.card_fin, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    dsimp [varianceScale]
    exact div_nonneg hVar (mul_nonneg (by positivity) (sq_nonneg _))
  have hBatchO : AccuracyBigO (fun ε => ((b ε).1 : ℝ)) varianceScale := by
    simpa [AccuracyTheta, varianceScale] using hBatchOrder.1
  have hBatchOne : ∀ ε, (1 : ℝ) ≤ (b ε).1 := by
    intro ε
    exact_mod_cast (b ε).2
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq : globalObjective P x0 - fStar = 0 := by
      simpa [P] using hGapZero.symm
    have hΔzero : Δ = 0 := by simpa [Δ] using hGapEq
    refine ⟨fun _ => K₁, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ε
      unfold NonconvexAccuracy
      have hD3 := Theorem_D3_online_VR_nonconvex_corrected_BTrack (K := K₁)
        A hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
          hQuantizer (hBatch ε) (hAverageSmooth ε) hStep
      dsimp only at hD3
      refine ⟨hD3.1, hD3.2.trans ?_⟩
      calc
        2 * (globalObjective P x0 - fStar) /
              ((A.stepSize : ℝ) * (K₁.1 : ℝ)) +
            varianceAggregateSq σ / (n.1 * (b ε).1) =
            varianceAggregateSq σ / (n.1 * (b ε).1) := by
              rw [hGapEq]
              ring
        _ ≤ (ε : ℝ) ^ 2 / 2 := hBatchAccuracy ε
        _ ≤ (ε : ℝ) ^ 2 := by nlinarith [sq_nonneg (ε : ℝ)]
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        change iterationScale ε = 0
        simp [iterationScale, hΔzero]
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
    · have hOracle := accuracyBigO_online_oracle_cost_one_round
        hBatchO hp hp1 hBatchOne hVarianceScaleNonneg
          (show 0 ≤ (b0.1 : ℝ) by positivity)
      convert hOracle using 1
      · funext ε
        simp [onlineOracleCallCount, K₁]
        ring
      · funext ε
        rw [show globalObjective
            (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 - fStar = 0 by
          simpa [P] using hGapEq]
        simp [varianceScale]
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
      rw [show (fun ε : Accuracy => (d.1 : ℝ) +
          Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) =
          (fun _ : Accuracy => (d.1 : ℝ)) by
        funext ε
        rw [hΔzero]
        ring]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) + (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) hdne accuracyToZero)
  · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hBracketEq : bracket = 0 := hBracketZero.symm
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
        have hsqrt : 0 ≤ Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
            (ω * rootMeanSquare Llocal ^ 2 +
              (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1)) :=
          Real.sqrt_nonneg _
        dsimp [bracket] at hBracketEq
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        P Llocal fStar hLower hSmooth hLzero
      refine ⟨fun _ => K₁, ?_⟩
      unfold ThreeEndpointComplexity
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD3 := Theorem_D3_online_VR_nonconvex_corrected_BTrack (K := K₁)
          A hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
            hQuantizer (hBatch ε) (hAverageSmooth ε) hStep
        dsimp only at hD3
        refine ⟨hD3.1, ?_⟩
        have heq : (fun z => ‖globalGradient P
            (uniformOutput (K := K₁)
              (onlineCorrectedProofExactProcess A hE x0 (hBatch ε)) z)‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
      · refine Or.inl ⟨?_, ?_⟩
        · intro ε
          change iterationScale ε = 0
          simp [iterationScale, hBracketEq]
        · unfold AccuracyBigO
          simpa [K₁] using
            (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
              accuracyToZero)
      · have hOracle := accuracyBigO_online_oracle_cost_one_round
          hBatchO hp hp1 hBatchOne hVarianceScaleNonneg
            (show 0 ≤ (b0.1 : ℝ) by positivity)
        have hBracketConcrete : rootMeanSquare Llocal +
            Real.sqrt ((1 - A.refreshProbability) /
              (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1)) = 0 := by
          simpa [bracket] using hBracketEq
        convert hOracle using 1
        · funext ε
          simp [onlineOracleCallCount, K₁]
          ring
        · funext ε
          rw [hBracketConcrete]
          simp [varianceScale]
      · unfold AccuracyBigO
        have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
        rw [show (fun ε : Accuracy => (d.1 : ℝ) +
            Δ / (ε : ℝ) ^ 2 * bracket *
              (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) =
            (fun _ : Accuracy => (d.1 : ℝ)) by
          funext ε
          rw [hBracketEq]
          ring]
        simpa [allWorkerCommunicationCount, K₁] using
          (Asymptotics.isBigO_const_const
            ((d.1 : ℝ) + (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ)) hdne accuracyToZero)
    · let K : Accuracy → Count := fun ε =>
        ⟨max 1 (Nat.ceil (2 * Δ /
          (((A.stepSize : ℝ) / 2) * (ε : ℝ) ^ 2))), by omega⟩
      have hΔpos : 0 < Δ := by simpa [Δ, P] using hGapPos
      have hHalfStep : 0 < (A.stepSize : ℝ) / 2 :=
        div_pos A.stepSize.property (by norm_num)
      have hScalar := positive_inverse_square_ceiling_schedule
        Δ ((A.stepSize : ℝ) / 2) bracket hΔpos hHalfStep hBracketPos
      have hKHalfBound : ∀ ε : Accuracy,
          2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) ≤
            (ε : ℝ) ^ 2 / 2 := by
        intro ε
        have h := mul_le_mul_of_nonneg_left (hScalar.1 ε)
          (show 0 ≤ (1 / 2 : ℝ) by norm_num)
        have hKpos : 0 < ((K ε).1 : ℝ) := by exact_mod_cast (K ε).2
        have h' : (1 / 2 : ℝ) *
            (2 * Δ / (((A.stepSize : ℝ) / 2) * ((K ε).1 : ℝ))) ≤
              (1 / 2 : ℝ) * (ε : ℝ) ^ 2 := by
          simpa [K] using h
        calc
          2 * Δ / ((A.stepSize : ℝ) * ((K ε).1 : ℝ)) =
              (1 / 2 : ℝ) *
                (2 * Δ / (((A.stepSize : ℝ) / 2) * ((K ε).1 : ℝ))) := by
                  field_simp [ne_of_gt A.stepSize.property, ne_of_gt hKpos]
                  <;> ring
          _ ≤ (1 / 2 : ℝ) * (ε : ℝ) ^ 2 := h'
          _ = (ε : ℝ) ^ 2 / 2 := by ring
      have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
        simpa [K, iterationScale] using hScalar.2
      have hIterationScaleNonneg : ∀ ε, 0 ≤ iterationScale ε := by
        intro ε
        dsimp [iterationScale]
        positivity
      refine ⟨K, ?_⟩
      unfold ThreeEndpointComplexity
      refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
      · intro ε
        unfold NonconvexAccuracy
        have hD3 := Theorem_D3_online_VR_nonconvex_corrected_BTrack (K := K ε)
          A hE x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
            hQuantizer (hBatch ε) (hAverageSmooth ε) hStep
        dsimp only at hD3
        refine ⟨hD3.1, hD3.2.trans ?_⟩
        have hHalf := add_le_add (hKHalfBound ε) (hBatchAccuracy ε)
        simpa [P, Δ] using hHalf
      · have hOracle := accuracyBigO_online_oracle_cost
          hBatchO hKBigO hp hp1
          (fun ε => by positivity) (fun ε => by positivity)
          hVarianceScaleNonneg (Filter.Eventually.of_forall hIterationScaleNonneg)
          (show 0 ≤ (b0.1 : ℝ) by positivity)
        convert hOracle using 1
        funext ε
        dsimp [varianceScale, iterationScale, Δ, bracket, P]
        ring
      · let commPayload : ℝ := A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ
        have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
        have hCommPayloadPos : 0 < commPayload := by
          dsimp [commPayload]
          exact add_pos_of_pos_of_nonneg
            (mul_pos hp hdpos)
            (mul_nonneg (sub_nonneg.mpr hp1) hζ)
        have hComm := accuracyBigO_affine_cost_of_schedule
          (K := fun ε => ((K ε).1 : ℝ))
          (scale := iterationScale)
          (init := (d.1 : ℝ))
          (actualPayload := commPayload)
          (targetPayload := commPayload)
          (payloadFactor := 1)
          hKBigO hdpos hCommPayloadPos.le hCommPayloadPos
            zero_lt_one (by simp) (Filter.Eventually.of_forall hIterationScaleNonneg)
        simpa [allWorkerCommunicationCount, commPayload, iterationScale] using hComm

/-- `book/MARINA/MARINA.json#/key_lemmas/19`, Theorem D.3 / Eqs. (42)-(44),
on the explicit nonfallback Eq. (6) B-track.  Proof step 24 says to choose an
inverse-square refresh batch large enough to control Eq. (41).  Accordingly,
the supplied `b` records the source's asymptotic representative, while the
algorithm uses its canonical pointwise-safe inflation.  No pointwise premise
is exported in this source-facing head. -/
theorem Theorem_D3_online_VR_complexity_endpoints_corrected
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (b : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess A hE x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) b ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)))
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) b
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => NonconvexAccuracy (K ε) P
          (onlineCorrectedProofExactProcess A hE x0
            (onlineNonconvexBatchScheduleFromBase_admissible n b0
              (varianceAggregateSq σ) b ε))
          (onlineProofExactPathLaw (A := A)) ε)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
        (fun ε => onlineOracleCallCount (chosenBatch ε) b0 (K ε)
          A.refreshProbability)
        (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2) +
          Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * varianceAggregateSq σ /
              (n.1 * (ε : ℝ) ^ 2) +
              (1 - A.refreshProbability) * b0.1))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
    (varianceAggregateSq σ) b
  have hvariance : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hChosenBatch : ∀ ε, OnlineBatchAdmissible (chosenBatch ε) b0 :=
    fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) b ε
  have hChosenOrder : AccuracyTheta
      (fun ε => (((chosenBatch ε).1 : ℕ) : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)) := by
    exact onlineNonconvexBatchScheduleFromBase_accuracyTheta n b0
      (varianceAggregateSq σ) hvariance b hBatchOrder
  have hChosenAccuracy : ∀ ε : Accuracy,
      varianceAggregateSq σ / (n.1 * (chosenBatch ε).1) ≤
        (ε : ℝ) ^ 2 / 2 := by
    intro ε
    exact onlineNonconvexBatchScheduleFromBase_variance_floor n b0
      (varianceAggregateSq σ) hvariance b ε
  have hEndpoint :=
    Theorem_D3_online_VR_complexity_endpoints_corrected_of_batch_accuracy
      A hE x0 chosenBatch Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
      hQuantizer hChosenBatch hAverageSmooth hChosenOrder hChosenAccuracy hStep
  simpa [chosenBatch] using hEndpoint

/-- Corrected B-track replacement for Theorem D.4 / Eqs. (50)-(52).
Eq. (51) literally counts `b + K(pb+2(1-p)b⁰)` but prints `m` as the
leading term on the right.  This declaration repairs that free finite-sum
symbol to the online refresh batch `b`; it is intentionally not exported under
the unqualified source theorem name. -/
theorem Theorem_D4_online_VR_PL_complexity_endpoints_corrected_BTrack_of_batch_accuracy
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 xStar : Point d) (b : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hPL : SatisfiesPL (onlineLocalProblemCorrected ⟨A.problem, hE⟩) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess A hE x0 (hBatch ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * μ * (ε : ℝ))))
    (hBatchAccuracy : ∀ ε : Accuracy,
      varianceAggregateSq σ / (n.1 * (b ε).1 * μ) ≤ (ε : ℝ) / 2)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - globalObjective P xStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let factor := max (1 / A.refreshProbability) (bracket / μ)
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => PLAccuracy (K ε) P
          (onlineCorrectedProofExactProcess A hE x0 (hBatch ε))
          (onlineProofExactPathLaw (A := A)) xStar ε)
        (fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (fun ε => onlineOracleCallCount (b ε) b0 (K ε) A.refreshProbability)
        (fun ε => (b ε).1 + factor *
          (A.refreshProbability * (b ε).1 +
            (1 - A.refreshProbability) * b0.1) * Real.log (Δ / (ε : ℝ)))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + factor * (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ) * Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤
      globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
        globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar :=
    sub_nonneg.mpr (hPL.1 x0)
  dsimp
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective P x0 - globalObjective P xStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
      (ω * rootMeanSquare Llocal ^ 2 +
        (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let factor : ℝ := max (1 / A.refreshProbability) (bracket / μ)
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hfactor : 0 < factor := by
    dsimp [factor]
    exact (div_pos zero_lt_one hp).trans_le (le_max_left _ _)
  have hBatchO : AccuracyBigO (fun ε => ((b ε).1 : ℝ))
      (fun ε => ((b ε).1 : ℝ)) :=
    Asymptotics.isBigO_refl _ _
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq : globalObjective P x0 - globalObjective P xStar = 0 := by
      simpa [P] using hGapZero.symm
    refine ⟨fun _ => K₁, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hD4 := Theorem_D4_online_VR_PL_corrected_BTrack (K := K₁)
        A hE x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hVariance
          hPL hQuantizer (hBatch ε) (hAverageSmooth ε) hStep
      dsimp only at hD4
      refine ⟨hD4.1, hD4.2.trans ?_⟩
      rw [hGapEq]
      have hfloor := hBatchAccuracy ε
      nlinarith [ε.property]
    · refine Or.inl ⟨?_, ?_⟩
      · intro ε
        change factor * Real.log (Δ / (ε : ℝ)) = 0
        rw [show Δ = 0 by simpa [Δ] using hGapEq]
        simp
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ)) accuracyToZero)
    · have hOracle := accuracyBigO_online_oracle_cost_one_round
        hBatchO hp hp1 (fun ε => by exact_mod_cast (b ε).2)
          (fun ε => by positivity) (show 0 ≤ (b0.1 : ℝ) by positivity)
      have hΔzero : Δ = 0 := by simpa [Δ] using hGapEq
      convert hOracle using 1
      · funext ε
        simp [onlineOracleCallCount, K₁]
        ring
      · funext ε
        rw [show globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) x0 -
            globalObjective (onlineLocalProblemCorrected ⟨A.problem, hE⟩) xStar = 0 by
          simpa [P] using hGapEq]
        simp
    · unfold AccuracyBigO
      have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
      have hΔzero : Δ = 0 := by simpa [Δ] using hGapEq
      rw [show (fun ε : Accuracy => (d.1 : ℝ) + factor *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ) *
          Real.log (Δ / (ε : ℝ))) = (fun _ : Accuracy => (d.1 : ℝ)) by
        funext ε
        rw [hΔzero]
        simp]
      simpa [allWorkerCommunicationCount, K₁] using
        (Asymptotics.isBigO_const_const
          ((d.1 : ℝ) + (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) hdne accuracyToZero)
  · let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    have hΔpos : 0 < Δ := by simpa [Δ, P] using hGapPos
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos A.stepSize.property μ.property
    have hc1 : c ≤ 1 := by
      have hcP := hStep.2
      dsimp [c]
      nlinarith
    let K : Accuracy → Count := fun ε =>
      ⟨max 1 (Nat.ceil (Real.log (2 * Δ / (ε : ℝ)) / c)), by omega⟩
    have hScalar := positive_geometric_ceiling_schedule_half_budget
      Δ c factor hΔpos hc hc1 hfactor
    have hContract : ∀ ε : Accuracy,
        (1 - c) ^ (K ε).1 * Δ ≤ (ε : ℝ) / 2 := by
      intro ε
      simpa [K] using hScalar.1 ε
    have hKBigO : AccuracyBigO (fun ε => ((K ε).1 : ℝ))
        (fun ε => factor * Real.log (Δ / (ε : ℝ))) := by
      simpa [K] using hScalar.2
    have hScaleEventually : ∀ᶠ ε : Accuracy in accuracyToZero,
        0 ≤ factor * Real.log (Δ / (ε : ℝ)) := by
      filter_upwards [eventually_one_le_log_gap_div_accuracy hΔpos] with ε hlog
      exact mul_nonneg hfactor.le (le_trans (by norm_num) hlog)
    refine ⟨K, ?_⟩
    unfold ThreeEndpointComplexity
    refine ⟨?_, Or.inr hKBigO, ?_, ?_⟩
    · intro ε
      unfold PLAccuracy
      have hD4 := Theorem_D4_online_VR_PL_corrected_BTrack (K := K ε)
        A hE x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hVariance
          hPL hQuantizer (hBatch ε) (hAverageSmooth ε) hStep
      dsimp only at hD4
      refine ⟨hD4.1, hD4.2.trans ?_⟩
      have hsum := add_le_add (hContract ε) (hBatchAccuracy ε)
      simpa [P, Δ, c] using hsum
    · have hOracle := accuracyBigO_online_oracle_cost
        hBatchO hKBigO hp hp1 (fun ε => by positivity) (fun ε => by positivity)
          (fun ε => by positivity) hScaleEventually
          (show 0 ≤ (b0.1 : ℝ) by positivity)
      convert hOracle using 1
      funext ε
      ring
    · let commPayload : ℝ := A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ
      have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
      have hCommPayloadPos : 0 < commPayload := by
        dsimp [commPayload]
        exact add_pos_of_pos_of_nonneg (mul_pos hp hdpos)
          (mul_nonneg (sub_nonneg.mpr hp1) hζ)
      have hComm := accuracyBigO_affine_cost_of_schedule
        (K := fun ε => ((K ε).1 : ℝ))
        (scale := fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (init := (d.1 : ℝ)) (actualPayload := commPayload)
        (targetPayload := commPayload) (payloadFactor := 1)
        hKBigO hdpos hCommPayloadPos.le hCommPayloadPos zero_lt_one
          (by simp) hScaleEventually
      change AccuracyBigO
        (fun ε => (d.1 : ℝ) + ((K ε).1 : ℝ) * commPayload)
        (fun ε => (d.1 : ℝ) + factor * commPayload *
          Real.log (Δ / (ε : ℝ)))
      rw [show (fun ε : Accuracy => (d.1 : ℝ) + factor * commPayload *
          Real.log (Δ / (ε : ℝ))) =
          (fun ε : Accuracy => (d.1 : ℝ) +
            (factor * Real.log (Δ / (ε : ℝ))) * commPayload) by
        funext ε
        ring]
      exact hComm

/-- `book/MARINA/MARINA.json#/key_lemmas/22`, Theorem D.4 / Eqs. (50)-(52),
with proof step 14's batch choice made executable.  The supplied family is an
asymptotic representative; the algorithm runs its pointwise-safe ceiling
inflation, so the Eq. (49) floor consumes at most half of `ε`. -/
theorem Theorem_D4_online_VR_PL_complexity_endpoints_corrected_BTrack
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 xStar : Point d) (b : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hPL : SatisfiesPL (onlineLocalProblemCorrected ⟨A.problem, hE⟩) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothnessCorrected (b0 := b0) ⟨A.problem, hE⟩
        (onlineCorrectedProofExactProcess A hE x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ b ε)) ℒlocal)
    (hBatchOrder : AccuracyTheta (fun ε => ((b ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * μ * (ε : ℝ))))
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ b
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - globalObjective P xStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let factor := max (1 / A.refreshProbability) (bracket / μ)
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun ε => PLAccuracy (K ε) P
          (onlineCorrectedProofExactProcess A hE x0
            (onlinePLBatchScheduleFromBase_admissible n b0
              (varianceAggregateSq σ) μ b ε))
          (onlineProofExactPathLaw (A := A)) xStar ε)
        (fun ε => factor * Real.log (Δ / (ε : ℝ)))
        (fun ε => onlineOracleCallCount (chosenBatch ε) b0 (K ε)
          A.refreshProbability)
        (fun ε => (chosenBatch ε).1 + factor *
          (A.refreshProbability * (chosenBatch ε).1 +
            (1 - A.refreshProbability) * b0.1) * Real.log (Δ / (ε : ℝ)))
        (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability ζ)
        (fun ε => d.1 + factor * (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ) * Real.log (Δ / (ε : ℝ))) := by
  let chosenBatch := onlinePLBatchScheduleFromBase n b0
    (varianceAggregateSq σ) μ b
  have hvariance : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hChosenBatch : ∀ ε, OnlineBatchAdmissible (chosenBatch ε) b0 :=
    fun ε => onlinePLBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) μ b ε
  have hChosenOrder : AccuracyTheta
      (fun ε => (((chosenBatch ε).1 : ℕ) : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * μ * (ε : ℝ))) := by
    exact onlinePLBatchScheduleFromBase_accuracyTheta n b0
      (varianceAggregateSq σ) μ hvariance μ.property b hBatchOrder
  have hChosenAccuracy : ∀ ε : Accuracy,
      varianceAggregateSq σ / (n.1 * (chosenBatch ε).1 * μ) ≤
        (ε : ℝ) / 2 := by
    intro ε
    exact onlinePLBatchScheduleFromBase_variance_floor n b0
      (varianceAggregateSq σ) μ hvariance μ.property b ε
  have hEndpoint :=
    Theorem_D4_online_VR_PL_complexity_endpoints_corrected_BTrack_of_batch_accuracy
      A hE x0 xStar chosenBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hVariance hPL hQuantizer hChosenBatch hAverageSmooth hChosenOrder
      hChosenAccuracy hStep
  simpa [chosenBatch] using hEndpoint

/-- One worker's ordered finite-sum minibatch when Remark D.1 assigns that
worker its own batch size. -/
abbrev HeterogeneousFiniteSumWorkerBatch (m : Count) (b0 : Count) :=
  Fin b0.1 → Component m

/-- Workerwise round-indexed laws for Remark D.1.  Keeping the worker index
outside `Measure` is the dependent-size analogue of `FiniteSumBatchLaw`: the
paper's fixed-iterate worker independence is realized by the product measure
below, rather than being asserted about an arbitrary joint law. -/
abbrev HeterogeneousFiniteSumWorkerBatchLaw (n m : Count)
    (b0 : Worker n → Count) :=
  ℕ → (i : Worker n) → Measure (HeterogeneousFiniteSumWorkerBatch m (b0 i))

/-- Canonical joint law for Remark D.1's independently sampled worker
minibatches.  This is the dependent-batch-size counterpart of
`finiteSumBatchJointLaw`. -/
noncomputable def heterogeneousFiniteSumIndependentBatchLaw {n m : Count}
    {b0 : Worker n → Count}
    (batchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0) :
    HeterogeneousFiniteSumBatchLaw n m b0 :=
  fun k => Measure.infinitePi (batchLaw k)

/-- Workerwise probability laws assemble to a probability law on the complete
heterogeneous batch. -/
theorem heterogeneousFiniteSumIndependentBatchLaw_isProbability
    {n m : Count} {b0 : Worker n → Count}
    (batchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (batchLaw k i)) (k : ℕ) :
    IsProbabilityMeasure (heterogeneousFiniteSumIndependentBatchLaw batchLaw k) := by
  letI (i : Worker n) : IsProbabilityMeasure (batchLaw k i) := hBatchLaw k i
  unfold heterogeneousFiniteSumIndependentBatchLaw
  infer_instance

/-- The `i`th projection of the canonical heterogeneous product law is the
declared worker-`i` minibatch law. -/
theorem heterogeneousFiniteSumIndependentBatchLaw_worker_marginal
    {n m : Count} {b0 : Worker n → Count}
    (batchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (batchLaw k i)) (k : ℕ)
    (i : Worker n) :
    Measure.map (fun batch : HeterogeneousFiniteSumBatch n m b0 => batch i)
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw k) =
      batchLaw k i := by
  letI (j : Worker n) : IsProbabilityMeasure (batchLaw k j) := hBatchLaw k j
  unfold heterogeneousFiniteSumIndependentBatchLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval (μ := batchLaw k) i)

/-- Worker projections are independent under the canonical heterogeneous
product law, which is the exact independence reduction used in Eq. (33). -/
theorem heterogeneousFiniteSumIndependentBatchLaw_worker_independent
    {n m : Count} {b0 : Worker n → Count}
    (batchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (batchLaw k i)) (k : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i (batch : HeterogeneousFiniteSumBatch n m b0) => batch i)
      (heterogeneousFiniteSumIndependentBatchLaw batchLaw k) := by
  letI (i : Worker n) : IsProbabilityMeasure (batchLaw k i) := hBatchLaw k i
  unfold heterogeneousFiniteSumIndependentBatchLaw
  exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)

/-- The arbitrary-joint-law formulation formerly used for Remark D.1 cannot
justify Eq. (33)'s `1 / n` variance reduction from centered worker marginals
alone.  Two workers may carry the same Rademacher innovation: each marginal
is centered with unit second moment, but the squared average still has moment
one rather than the independent-worker bound one half.  Thus the product law
in `heterogeneousFiniteSumIndependentBatchLaw` is correction of the sampling
object, not an extra analytic premise on the source theorem. -/
theorem remark_D1_arbitrary_joint_batchLaw_counterexample :
    ∃ (law : Measure Bool) (innovation : Fin 2 → Bool → ℝ),
      IsProbabilityMeasure law ∧
      (∀ i, Integrable (innovation i) law ∧
        (∫ z, innovation i z ∂law) = 0 ∧
        (∫ z, (innovation i z) ^ 2 ∂law) = 1) ∧
      (∀ z, innovation 0 z = innovation 1 z) ∧
      ¬ ((∫ z, (average (fun i : Fin 2 => innovation i z)) ^ 2 ∂law) ≤
        (1 / 2 : ℝ) * average (fun i : Fin 2 =>
          ∫ z, (innovation i z) ^ 2 ∂law)) := by
  let hpHalf : RefreshProbabilityAdmissible ((1 : ℝ) / 2) := by
    constructor <;> norm_num
  let law := refreshLaw ((1 : ℝ) / 2) hpHalf
  let innovation : Fin 2 → Bool → ℝ := fun _ z => if z then 1 else -1
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold refreshLaw
    infer_instance
  have htrueMass : law.real ({true} : Set Bool) = (1 : ℝ) / 2 := by
    rw [measureReal_def]
    dsimp [law]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
    norm_num [PMF.bernoulli_apply]
  have hfalseMass : law.real ({false} : Set Bool) = (1 : ℝ) / 2 := by
    rw [measureReal_def]
    dsimp [law]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
    simp only [PMF.bernoulli_apply, Bool.cond_false]
    let pNN : NNReal := ⟨(1 : ℝ) / 2, by norm_num⟩
    have hpNN : pNN ≤ (1 : NNReal) := by
      exact_mod_cast (show (1 : ℝ) / 2 ≤ 1 by norm_num)
    change ((1 - pNN : NNReal) : ℝ) = 1 / 2
    rw [NNReal.coe_sub hpNN]
    norm_num [pNN]
  have hMean (i : Fin 2) : (∫ z, innovation i z ∂law) = 0 := by
    rw [MeasureTheory.integral_fintype]
    · norm_num [innovation, htrueMass, hfalseMass]
    · exact Integrable.of_finite
  have hSecond (i : Fin 2) : (∫ z, (innovation i z) ^ 2 ∂law) = 1 := by
    rw [MeasureTheory.integral_fintype]
    · norm_num [innovation, htrueMass, hfalseMass]
    · exact Integrable.of_finite
  refine ⟨law, innovation, inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact ⟨Integrable.of_finite, hMean i, hSecond i⟩
  · intro z
    rfl
  · have hAverage (z : Bool) :
        average (fun i : Fin 2 => innovation i z) = innovation 0 z := by
      change SOptLib.finiteUniformAverage
          (fun _ : Fin 2 => innovation 0 z) = innovation 0 z
      exact SOptLib.finiteUniformAverage_const (innovation 0 z)
    have hAverageSecond :
        (∫ z, (average (fun i : Fin 2 => innovation i z)) ^ 2 ∂law) = 1 := by
      rw [MeasureTheory.integral_fintype]
      · norm_num [hAverage, innovation, htrueMass, hfalseMass]
      · exact Integrable.of_finite
    rw [hAverageSecond]
    simp only [hSecond]
    norm_num [average, SOptLib.finiteUniformAverage]

/-- The finite product of dependent coordinate-pair laws is carried to the
product of the two dependent function laws by coordinatewise unzip.  Mathlib's
`measurePreserving_arrowProdEquivProdArrow` currently exposes only the
nondependent specialization; this is the same cylinder-set argument for the
worker-dependent batch types used by Remark D.1. -/
noncomputable def dependentArrowProdEquivProdArrow
    {ι : Type*} (α β : ι → Type*)
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)] :
    ((i : ι) → α i × β i) ≃ᵐ
      ((i : ι) → α i) × ((i : ι) → β i) where
  __ := Equiv.arrowProdEquivProdArrow ι α β
  measurable_toFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop
  measurable_invFun := by
    dsimp [Equiv.arrowProdEquivProdArrow]
    fun_prop

theorem measurePreserving_dependentArrowProdEquivProdArrow
    {ι : Type*} [Fintype ι] {α β : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
    (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentArrowProdEquivProdArrow α β)
      (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (dependentArrowProdEquivProdArrow α β).measurable
  map_eq := by
    refine (MeasureTheory.Measure.FiniteSpanningSetsIn.ext ?_
      (isPiSystem_pi.prod isPiSystem_pi)
      ((MeasureTheory.Measure.FiniteSpanningSetsIn.pi
          fun i => (μ i).toFiniteSpanningSetsIn).prod
        (MeasureTheory.Measure.FiniteSpanningSetsIn.pi
          fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (MeasureTheory.Measure.FiniteSpanningSetsIn.pi
          (fun i => (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (MeasureTheory.Measure.FiniteSpanningSetsIn.pi
          (fun i => (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (dependentArrowProdEquivProdArrow α β) ⁻¹'
          (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i => s i ×ˢ t i) by
        ext x
        simp [dependentArrowProdEquivProdArrow, Set.mem_pi, forall_and]]
      simp_rw [MeasureTheory.Measure.pi_pi, MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.pi_pi, Finset.prod_mul_distrib]

/-- Under Remark D.1's canonical dependent product law, the complete
minibatch/compressor noise pairs of distinct workers are jointly independent.
This is the exact law-level independence input used to cancel the off-diagonal
worker terms in the heterogeneous Eq. (33) calculation. -/
theorem heterogeneousFiniteSumRoundLaw_worker_noise_iIndep
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (batchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (batchLaw k i)) (k : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i (z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ) =>
        (z.2.1 i, z.2.2 i))
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)) := by
  letI (i : Worker n) : IsProbabilityMeasure (batchLaw k i) := hBatchLaw k i
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw batchLaw k) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability batchLaw hBatchLaw k
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  have hInner :
      Measure.map
          (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
            fun i => (z.1 i, z.2 i))
          ((heterogeneousFiniteSumIndependentBatchLaw batchLaw k).prod
            (workerCompressionLaw A.quantizer)) =
        Measure.infinitePi (fun i : Worker n =>
          (batchLaw k i).prod A.quantizer.law) := by
    unfold heterogeneousFiniteSumIndependentBatchLaw workerCompressionLaw
    rw [MeasureTheory.Measure.infinitePi_eq_pi,
      MeasureTheory.Measure.infinitePi_eq_pi,
      MeasureTheory.Measure.infinitePi_eq_pi]
    simpa [dependentArrowProdEquivProdArrow] using
      (measurePreserving_dependentArrowProdEquivProdArrow
        (fun i : Worker n => batchLaw k i)
        (fun _ : Worker n => A.quantizer.law)).symm.map_eq
  have hWhole :
      Measure.map
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            fun i => (z.2.1 i, z.2.2 i))
          (heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)) =
        Measure.infinitePi (fun i : Worker n =>
          (batchLaw k i).prod A.quantizer.law) := by
    calc
      Measure.map
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            fun i => (z.2.1 i, z.2.2 i))
          (heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)) =
          Measure.map
            (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
              fun i => (z.1 i, z.2 i))
            (Measure.map Prod.snd
              (heterogeneousFiniteSumRoundLaw A
                (heterogeneousFiniteSumIndependentBatchLaw batchLaw k))) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · fun_prop
        · exact measurable_snd
      _ = Measure.map
            (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
              fun i => (z.1 i, z.2 i))
            ((heterogeneousFiniteSumIndependentBatchLaw batchLaw k).prod
              (workerCompressionLaw A.quantizer)) := by
        unfold heterogeneousFiniteSumRoundLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
      _ = Measure.infinitePi (fun i : Worker n =>
          (batchLaw k i).prod A.quantizer.law) := hInner
  have hcoord (i : Worker n) :
      Measure.map
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (z.2.1 i, z.2.2 i))
          (heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)) =
        (batchLaw k i).prod A.quantizer.law := by
    calc
      Measure.map
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (z.2.1 i, z.2.2 i))
          (heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)) =
          Measure.map
            (fun w : (j : Worker n) →
              HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ => w i)
            (Measure.map
              (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
                fun j => (z.2.1 j, z.2.2 j))
              (heterogeneousFiniteSumRoundLaw A
                (heterogeneousFiniteSumIndependentBatchLaw batchLaw k))) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact measurable_pi_apply i
        · fun_prop
      _ = Measure.map
            (fun w : (j : Worker n) →
              HeterogeneousFiniteSumWorkerBatch m (b0 j) × Ξ => w i)
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
        (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          fun i => (z.2.1 i, z.2.2 i))
        (heterogeneousFiniteSumRoundLaw A
          (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)) =
      Measure.infinitePi (fun i : Worker n =>
        (batchLaw k i).prod A.quantizer.law) := hWhole
    _ = Measure.infinitePi (fun i : Worker n =>
        Measure.map
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (z.2.1 i, z.2.2 i))
          (heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw batchLaw k))) := by
      congr 1
      funext i
      exact (hcoord i).symm

/-- Every time coordinate of the heterogeneous Algorithm 2 path has the
canonical round law assembled from the workerwise minibatch laws. -/
theorem heterogeneousFiniteSumPathLaw_round_marginal
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (batchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (batchLaw k i)) (k : ℕ) :
    Measure.map
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => path k)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw batchLaw)) =
      heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw k) := by
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw batchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  unfold heterogeneousFiniteSumPathLaw
  simpa using
    (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun t : ℕ => heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw t)) k)

/-- The worker minibatch/compressor pairs at round `k` remain jointly
independent when read from the complete heterogeneous path law.  This is the
path-level form needed by the centered-innovation cross-term calculation. -/
theorem heterogeneousFiniteSumPathLaw_worker_noise_iIndep
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (batchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (batchLaw k i)) (k : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i
          (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) =>
        ((path k).2.1 i, (path k).2.2 i))
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw)) := by
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw batchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw batchLaw)) := by
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  let roundLaw := heterogeneousFiniteSumRoundLaw A
    (heterogeneousFiniteSumIndependentBatchLaw batchLaw k)
  let roundNoise := fun i
      (z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ) =>
    (z.2.1 i, z.2.2 i)
  have hRound : ProbabilityTheory.iIndepFun roundNoise roundLaw :=
    heterogeneousFiniteSumRoundLaw_worker_noise_iIndep A batchLaw hBatchLaw k
  have hRoundLaw :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map (by
      intro i
      fun_prop)).1 hRound
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map (by
    intro i
    fun_prop)).2
  calc
    Measure.map
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          fun i => ((path k).2.1 i, (path k).2.2 i))
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw batchLaw)) =
      Measure.map
        (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          fun i => (z.2.1 i, z.2.2 i))
        (Measure.map
          (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => path k)
          (heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw batchLaw))) := by
      rw [MeasureTheory.Measure.map_map]
      · rfl
      · fun_prop
      · exact measurable_pi_apply k
    _ = Measure.map
        (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          fun i => (z.2.1 i, z.2.2 i)) roundLaw := by
      rw [heterogeneousFiniteSumPathLaw_round_marginal
        A batchLaw hBatchLaw k]
    _ = Measure.infinitePi (fun i => Measure.map (roundNoise i) roundLaw) :=
      hRoundLaw
    _ = Measure.infinitePi (fun i =>
        Measure.map
          (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            ((path k).2.1 i, (path k).2.2 i))
          (heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw batchLaw))) := by
      congr 1
      funext i
      calc
        Measure.map (roundNoise i) roundLaw =
            Measure.map (roundNoise i)
              (Measure.map
                (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
                  path k)
                (heterogeneousFiniteSumPathLaw A
                  (heterogeneousFiniteSumIndependentBatchLaw batchLaw))) := by
          rw [heterogeneousFiniteSumPathLaw_round_marginal
            A batchLaw hBatchLaw k]
        _ = Measure.map
            (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              ((path k).2.1 i, (path k).2.2 i))
            (heterogeneousFiniteSumPathLaw A
              (heterogeneousFiniteSumIndependentBatchLaw batchLaw)) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · fun_prop
          · exact measurable_pi_apply k

/-- The worker-dependent minibatch difference is jointly measurable in its
two query points and the complete dependent batch.  This is the dependent-size
specialization of `finiteSumWorkerBatchDifference_joint_measurable`. -/
theorem heterogeneousFiniteSumBatchDifference_joint_measurable
    {d n m : Count} {b0 : Worker n → Count}
    (P : FiniteSumProblem d n m) (i : Worker n) :
    Measurable (fun p : (Point d × Point d) ×
        HeterogeneousFiniteSumBatch n m b0 =>
      heterogeneousFiniteSumBatchDifference P b0 p.2 i p.1.1 p.1.2) := by
  have hworker := finiteSumWorkerBatchDifference_joint_measurable
    (b0 := b0 i) P i
  have hselect : Measurable (fun p : (Point d × Point d) ×
      HeterogeneousFiniteSumBatch n m b0 => (p.1, p.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  simpa only [heterogeneousFiniteSumBatchDifference,
    finiteSumWorkerBatchDifference, Function.comp_apply] using
      hworker.comp hselect

/-- The heterogeneous Algorithm 2 worker estimator is jointly measurable in
the previous state and current canonical round noise. -/
theorem heterogeneousFiniteSumWorkerEstimator_round_joint_measurable
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (i : Worker n) :
    Measurable (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      heterogeneousFiniteSumWorkerEstimator A p.2 p.1 i) := by
  classical
  let P := finiteSumLocalProblem A.problem
  have hxNext : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hx : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        p.1.x) := (measurable_state_x d).comp measurable_fst
  have hbatch : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        p.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hqueries : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        ((primalStep A.stepSize p.1, p.1.x), p.2.2.1)) :=
    (hxNext.prodMk hx).prodMk hbatch
  have hdiff : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        heterogeneousFiniteSumBatchDifference A.problem b0 p.2.2.1 i
          (primalStep A.stepSize p.1) p.1.x) := by
    simpa only [Function.comp_apply] using
      (heterogeneousFiniteSumBatchDifference_joint_measurable
        (b0 := b0) A.problem i).comp hqueries
  have hsample : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        p.2.2.2 i) :=
    (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hquantized : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        A.quantizer.apply
          (heterogeneousFiniteSumBatchDifference A.problem b0 p.2.2.1 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    A.quantizer.measurable_apply_uncurry.comp (hdiff.prodMk hsample)
  have hrefresh : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        localGradient P i (primalStep A.stepSize p.1)) :=
    (measurable_localGradient P i).comp hxNext
  have hcarry : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        p.1.g + A.quantizer.apply
          (heterogeneousFiniteSumBatchDifference A.problem b0 p.2.2.1 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    ((measurable_state_g d).comp measurable_fst).add hquantized
  have hrefreshSet : MeasurableSet
      {p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ |
        p.2.1 = true} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
  have hif : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        if p.2.1 = true then
          localGradient P i (primalStep A.stepSize p.1)
        else p.1.g + A.quantizer.apply
          (heterogeneousFiniteSumBatchDifference A.problem b0 p.2.2.1 i
            (primalStep A.stepSize p.1) p.1.x) (p.2.2.2 i)) :=
    @Measurable.ite _ _ _ _ _ _
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        p.2.1 = true)
      (fun p => Bool.decEq p.2.1 true) hrefreshSet hrefresh hcarry
  simpa [heterogeneousFiniteSumWorkerEstimator, P] using hif

/-- The complete heterogeneous Algorithm 2 transition is jointly measurable
in state and current round noise. -/
theorem heterogeneousFiniteSumStep_round_joint_measurable
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) :
    Measurable (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      heterogeneousFiniteSumStep A p.2 p.1) := by
  classical
  have hxNext : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hg : Measurable
      (fun p : State d × HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        average (fun i : Worker n =>
          heterogeneousFiniteSumWorkerEstimator A p.2 p.1 i)) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ (fun i _ =>
      heterogeneousFiniteSumWorkerEstimator_round_joint_measurable A i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
  simpa [heterogeneousFiniteSumStep] using
    (measurable_state_mk d).comp (hxNext.prodMk hg)

/-- Sigma-algebra generated by heterogeneous Algorithm 2 rounds strictly
before time `k`. -/
@[reducible] def heterogeneousFiniteSumStrictPast
    {n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (k : ℕ) :
    MeasurableSpace (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :=
  ⨆ j : Fin k, MeasurableSpace.comap
    (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => path j)
    inferInstance

theorem heterogeneousFiniteSumStrictPast_coordinate_measurable
    {n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] {j k : ℕ} (hjk : j < k) :
    Measurable[heterogeneousFiniteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k]
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ => path j) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le ⟨j, hjk⟩ (by rfl)

theorem heterogeneousFiniteSumStrictPast_le
    {n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (k : ℕ) :
    heterogeneousFiniteSumStrictPast
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
      (inferInstance : MeasurableSpace
        (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ)) := by
  refine iSup_le fun j => ?_
  exact (measurable_pi_apply (j : ℕ)).comap_le

/-- The generated heterogeneous Algorithm 2 state is measurable from exactly
the earlier round coordinates. -/
theorem heterogeneousFiniteSumProcess_strictPast_measurable
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d) (k : ℕ) :
    Measurable[heterogeneousFiniteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k]
      (heterogeneousFiniteSumProcess (b0 := b0) A x0 k) := by
  let past : Unit → MeasurableSpace
      (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :=
    fun _ => heterogeneousFiniteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k
  let driver : ℕ → (ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) →
      HeterogeneousFiniteSumRoundNoise n m b0 Ξ := fun t path => path t
  let step : ℕ → State d → HeterogeneousFiniteSumRoundNoise n m b0 Ξ →
      State d := fun _ s z => heterogeneousFiniteSumStep A z s
  apply SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := past)
      (process := heterogeneousFiniteSumProcess (b0 := b0) A x0)
      (driver := driver) (step := step) (k := ()) (N := k)
  · change Measurable[past ()]
      (fun _ : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        finiteSumInitialState A x0)
    exact measurable_const
  · intro t ht _hprocess
    exact heterogeneousFiniteSumStrictPast_coordinate_measurable
      (Nat.lt_of_succ_le ht)
  · intro _t _ht
    exact heterogeneousFiniteSumStep_round_joint_measurable A
  · intro t _ht
    rfl
  · exact le_rfl

set_option maxHeartbeats 1600000 in
/-- The fixed-query worker innovation calculation used by Remark D.1.
The source proof of Eq. (33) performs this calculation worker by worker before
averaging.  Here the worker's law is obtained from the canonical dependent
product law, so the denominator remains the source's `(b⁰ i)` rather than a
homogeneous surrogate. -/
theorem heterogeneous_finite_sum_fixed_worker_innovation_centered_second_moment
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n)
    (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :
    let x := (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x
    let xNext :=
      (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
    let delta :=
      localGradientDifference (finiteSumLocalProblem A.problem) i xNext x
    let innovation := fun q : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ =>
      A.quantizer.apply
          (finiteSumWorkerBatchDifference A.problem q.1 i xNext x) q.2 - delta
    Integrable (fun q => ‖innovation q‖ ^ 2)
        ((workerBatchLaw k i).prod A.quantizer.law) ∧
      (∫ q, innovation q ∂(workerBatchLaw k i).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(workerBatchLaw k i).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
          ‖xNext - x‖ ^ 2 := by
  let x := (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x
  let xNext :=
    (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
  let delta :=
    localGradientDifference (finiteSumLocalProblem A.problem) i xNext x
  let D := fun batch : HeterogeneousFiniteSumWorkerBatch m (b0 i) =>
    finiteSumWorkerBatchDifference A.problem batch i xNext x
  let innovation := fun q : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ =>
    A.quantizer.apply (D q.1) q.2 - delta
  change Integrable (fun q => ‖innovation q‖ ^ 2)
        ((workerBatchLaw k i).prod A.quantizer.law) ∧
      (∫ q, innovation q ∂(workerBatchLaw k i).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(workerBatchLaw k i).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
          ‖xNext - x‖ ^ 2
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (workerBatchLaw t j) :=
    hBatchLaw t j
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  let jointLaw := heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k
  let project := fun batch : HeterogeneousFiniteSumBatch n m b0 => batch i
  have hproject : Measurable project := measurable_pi_apply i
  have hmarginal : Measure.map project jointLaw = workerBatchLaw k i := by
    simpa [project, jointLaw] using
      heterogeneousFiniteSumIndependentBatchLaw_worker_marginal
        workerBatchLaw hBatchLaw k i
  have hD_meas : Measurable D := by
    have hpair : Measurable
        (fun batch : HeterogeneousFiniteSumWorkerBatch m (b0 i) =>
          ((xNext, x), batch)) :=
      (measurable_const.prodMk measurable_const).prodMk measurable_id
    simpa [D] using
      (finiteSumWorkerBatchDifference_joint_measurable
        (b0 := b0 i) A.problem i).comp hpair
  have hcenter_meas : Measurable (fun batch => ‖D batch - delta‖ ^ 2) := by
    fun_prop
  rcases hAverageSmooth.2 k i path with
    ⟨hD_joint, hcenter_joint, hmean_joint, hvar_joint⟩
  have hD_comp : D ∘ project = fun batch : HeterogeneousFiniteSumBatch n m b0 =>
      heterogeneousFiniteSumBatchDifference A.problem b0 batch i xNext x := by
    funext batch
    rfl
  have hcenter_comp : (fun batch => ‖D batch - delta‖ ^ 2) ∘ project =
      fun batch : HeterogeneousFiniteSumBatch n m b0 =>
        ‖heterogeneousFiniteSumBatchDifference A.problem b0 batch i xNext x -
          delta‖ ^ 2 := by
    funext batch
    rfl
  have hD_int : Integrable D (workerBatchLaw k i) := by
    rw [← hmarginal]
    apply (MeasureTheory.integrable_map_measure
      hD_meas.aestronglyMeasurable hproject.aemeasurable).mpr
    simpa [hD_comp] using hD_joint
  have hD_center_sq : Integrable (fun batch => ‖D batch - delta‖ ^ 2)
      (workerBatchLaw k i) := by
    rw [← hmarginal]
    apply (MeasureTheory.integrable_map_measure
      hcenter_meas.aestronglyMeasurable hproject.aemeasurable).mpr
    simpa [hcenter_comp] using hcenter_joint
  have hD_mean : (∫ batch, D batch ∂workerBatchLaw k i) = delta := by
    rw [← hmarginal,
      MeasureTheory.integral_map hproject.aemeasurable hD_meas.aestronglyMeasurable]
    simpa [hD_comp] using hmean_joint
  have hD_var :
      (∫ batch, ‖D batch - delta‖ ^ 2 ∂workerBatchLaw k i) ≤
        (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2 := by
    rw [← hmarginal,
      MeasureTheory.integral_map hproject.aemeasurable
        hcenter_meas.aestronglyMeasurable]
    simpa [hcenter_comp] using hvar_joint
  have hinnovation_meas : Measurable innovation := by
    have hquantized : Measurable
        (fun q : HeterogeneousFiniteSumWorkerBatch m (b0 i) × Ξ =>
          A.quantizer.apply (D q.1) q.2) :=
      A.quantizer.measurable_apply_uncurry.comp
        ((hD_meas.comp measurable_fst).prodMk measurable_snd)
    exact hquantized.sub measurable_const
  have hD_sq : Integrable (fun batch => ‖D batch‖ ^ 2)
      (workerBatchLaw k i) :=
    oracle_second_moment_integrable_of_centered_second_moment_integrable
      (workerBatchLaw k i) D delta hD_meas.aestronglyMeasurable hD_center_sq
  have hD_second_eq :
      (∫ batch, ‖D batch‖ ^ 2 ∂workerBatchLaw k i) =
        (∫ batch, ‖D batch - delta‖ ^ 2 ∂workerBatchLaw k i) +
          ‖delta‖ ^ 2 :=
    integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
      (workerBatchLaw k i) D delta hD_int hD_center_sq hD_mean
  have hfiber_int : ∀ batch,
      Integrable (fun ξ => ‖innovation (batch, ξ)‖ ^ 2) A.quantizer.law := by
    intro batch
    let v := D batch
    have hnoise_sq : Integrable
        (fun ξ => ‖A.quantizer.apply v ξ - v‖ ^ 2) A.quantizer.law :=
      quantizer_error_sq_integrable hQuantizer v
    have hconst_sq : Integrable
        (fun _ : Ξ => ‖v - delta‖ ^ 2) A.quantizer.law :=
      integrable_const (c := ‖v - delta‖ ^ 2)
    have hnoise_meas : AEStronglyMeasurable
        (fun ξ => A.quantizer.apply v ξ - v) A.quantizer.law :=
      ((hQuantizer.2 v).1.sub (integrable_const (c := v))).aestronglyMeasurable
    have hsum := integrable_sq_norm_add
      hnoise_meas aestronglyMeasurable_const hnoise_sq hconst_sq
    convert hsum using 1
    funext ξ
    congr 2
    simp only [innovation, v]
    abel
  have hfiber_mean : ∀ batch,
      (∫ ξ, innovation (batch, ξ) ∂A.quantizer.law) = D batch - delta := by
    intro batch
    rw [integral_sub (hQuantizer.2 (D batch)).1
      (integrable_const (c := delta))]
    rw [(hQuantizer.2 (D batch)).2.2.1]
    simp [innovation, integral_const, probReal_univ]
  have hfiber_sq_eq : ∀ batch,
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) =
        (∫ ξ, ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := by
    intro batch
    let G := fun ξ => A.quantizer.apply (D batch) ξ - delta
    have hG_int : Integrable G A.quantizer.law :=
      (hQuantizer.2 (D batch)).1.sub (integrable_const (c := delta))
    have hcenter_sq : Integrable
        (fun ξ => ‖G ξ - (D batch - delta)‖ ^ 2) A.quantizer.law := by
      convert (hQuantizer.2 (D batch)).2.1 using 1
      funext ξ
      congr 2
      simp only [G]
      abel
    have hG_mean : (∫ ξ, G ξ ∂A.quantizer.law) = D batch - delta := by
      rw [integral_sub (hQuantizer.2 (D batch)).1
        (integrable_const (c := delta))]
      rw [(hQuantizer.2 (D batch)).2.2.1]
      simp [integral_const, probReal_univ]
    have hdecomp :=
      integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
        A.quantizer.law G (D batch - delta) hG_int hcenter_sq hG_mean
    calc
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) =
          ∫ ξ, ‖G ξ‖ ^ 2 ∂A.quantizer.law := by rfl
      _ = (∫ ξ, ‖G ξ - (D batch - delta)‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := hdecomp
      _ = (∫ ξ, ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
          ∂A.quantizer.law) + ‖D batch - delta‖ ^ 2 := by
            congr 1
            apply integral_congr_ae
            refine Filter.Eventually.of_forall fun ξ => ?_
            have hvec : G ξ - (D batch - delta) =
                A.quantizer.apply (D batch) ξ - D batch := by
              simp only [G]
              abel
            change ‖G ξ - (D batch - delta)‖ ^ 2 =
              ‖A.quantizer.apply (D batch) ξ - D batch‖ ^ 2
            rw [hvec]
  have hfiber_bound : ∀ batch,
      (∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law) ≤
        ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2 := by
    intro batch
    rw [hfiber_sq_eq batch]
    exact add_le_add (hQuantizer.2 (D batch)).2.2.2 le_rfl
  have hbudget_int : Integrable
      (fun batch => ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
      (workerBatchLaw k i) :=
    (hD_sq.const_mul ω).add hD_center_sq
  have hprod_sq : Integrable (fun q => ‖innovation q‖ ^ 2)
      ((workerBatchLaw k i).prod A.quantizer.law) := by
    apply integrable_prod_of_fiber_integral_norm_le_integrable_bound
      (μ := workerBatchLaw k i) (ν := A.quantizer.law)
      (φ := fun batch ξ => ‖innovation (batch, ξ)‖ ^ 2)
      (B := fun batch => ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
    · simpa [pow_two] using
        (hinnovation_meas.norm.mul hinnovation_meas.norm).aestronglyMeasurable
    · exact Filter.Eventually.of_forall hfiber_int
    · exact hbudget_int
    · refine Filter.Eventually.of_forall fun batch => ?_
      calc
        (∫ ξ, ‖‖innovation (batch, ξ)‖ ^ 2‖ ∂A.quantizer.law) =
            ∫ ξ, ‖innovation (batch, ξ)‖ ^ 2 ∂A.quantizer.law := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun ξ =>
                Real.norm_of_nonneg (sq_nonneg _)
        _ ≤ ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2 :=
          hfiber_bound batch
  have hprod_innovation : Integrable innovation
      ((workerBatchLaw k i).prod A.quantizer.law) :=
    integrable_of_integrable_norm_sq hinnovation_meas.aestronglyMeasurable hprod_sq
  have hprod_mean :
      (∫ q, innovation q ∂(workerBatchLaw k i).prod A.quantizer.law) = 0 := by
    rw [integral_prod _ hprod_innovation]
    calc
      (∫ batch, ∫ ξ, innovation (batch, ξ) ∂A.quantizer.law
          ∂workerBatchLaw k i) =
          ∫ batch, D batch - delta ∂workerBatchLaw k i := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hfiber_mean
      _ = 0 := by
        rw [integral_sub hD_int (integrable_const (c := delta)), hD_mean]
        simp [integral_const, probReal_univ]
  have hdelta_norm : ‖delta‖ ≤ Llocal i * ‖xNext - x‖ := by
    simpa [delta, localGradientDifference] using hSmooth.2 i xNext x
  have hdelta_sq : ‖delta‖ ^ 2 ≤ (Llocal i) ^ 2 * ‖xNext - x‖ ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _)
      (le_trans (norm_nonneg _) hdelta_norm)).2 hdelta_norm
  have homega_nonneg : 0 ≤ ω := le_of_lt hQuantizer.1
  have hone_omega_nonneg : 0 ≤ 1 + ω := by linarith
  have hdelta_scaled := mul_le_mul_of_nonneg_left hdelta_sq homega_nonneg
  have hvar_scaled := mul_le_mul_of_nonneg_left hD_var hone_omega_nonneg
  refine ⟨hprod_sq, hprod_mean, ?_⟩
  rw [integral_prod _ hprod_sq]
  calc
    (∫ batch, ∫ ξ, ‖innovation (batch, ξ)‖ ^ 2
        ∂A.quantizer.law ∂workerBatchLaw k i) ≤
        ∫ batch, (ω * ‖D batch‖ ^ 2 + ‖D batch - delta‖ ^ 2)
          ∂workerBatchLaw k i := by
            exact integral_mono hprod_sq.integral_prod_left hbudget_int hfiber_bound
    _ = ω * (∫ batch, ‖D batch‖ ^ 2 ∂workerBatchLaw k i) +
          ∫ batch, ‖D batch - delta‖ ^ 2 ∂workerBatchLaw k i := by
            rw [integral_add (hD_sq.const_mul ω) hD_center_sq,
              integral_const_mul]
    _ = ω * ‖delta‖ ^ 2 + (1 + ω) *
          (∫ batch, ‖D batch - delta‖ ^ 2 ∂workerBatchLaw k i) := by
            rw [hD_second_eq]
            ring
    _ ≤ ω * ((Llocal i) ^ 2 * ‖xNext - x‖ ^ 2) +
          (1 + ω) * ((ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2) :=
            add_le_add hdelta_scaled hvar_scaled
    _ = (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
          ‖xNext - x‖ ^ 2 := by ring

/-- The centered worker innovation read from the generated heterogeneous
Algorithm 2 path.  This is the worker-dependent analogue of
`finiteSumWorkerInnovation`; it unfolds directly to the current product-law
minibatch/compressor coordinate and the two generated query points. -/
noncomputable def heterogeneousFiniteSumWorkerInnovation
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (k : ℕ) (i : Worker n)
    (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) : Point d :=
  let x := (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x
  let xNext :=
    (heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x
  A.quantizer.apply
      (heterogeneousFiniteSumBatchDifference A.problem b0
        (path k).2.1 i xNext x) ((path k).2.2 i) -
    localGradientDifference (finiteSumLocalProblem A.problem) i xNext x

/-- The generated query pair is independent of one worker's current
minibatch/compressor coordinate.  Independence is derived from the canonical
infinite product path law and strict-past measurability; no adaptedness premise
is added to Remark D.1. -/
theorem heterogeneousFiniteSum_strictPast_query_indep_worker_noise
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (k : ℕ) (i : Worker n) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        ((heterogeneousFiniteSumProcess (b0 := b0) A x0 (k + 1) path).x,
          (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x))
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        ((path k).2.1 i, (path k).2.2 i))
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) := by
  classical
  let P := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let round := fun t
      (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) => path t
  let query := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    (primalStep A.stepSize
        (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path),
      (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x)
  let workerNoise := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    ((path k).2.1 i, (path k).2.2 i)
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (workerBatchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hroundMeas : ∀ t, Measurable (round t) := fun t => measurable_pi_apply t
  have hroundIndep : ProbabilityTheory.iIndepFun round P := by
    dsimp [round, P]
    unfold heterogeneousFiniteSumPathLaw
    exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
  have hquery : Measurable[heterogeneousFiniteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k] query := by
    have hs := heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k
    exact ((measurable_primalStep A.stepSize).comp hs).prodMk
      ((measurable_state_x d).comp hs)
  have hstrict : heterogeneousFiniteSumStrictPast
      (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
      (⨆ t ∈ ({t : ℕ | t < k} : Set ℕ),
        MeasurableSpace.comap (round t) inferInstance) := by
    refine iSup_le fun j => ?_
    exact le_iSup_of_le (j : ℕ)
      (le_iSup_of_le (show (j : ℕ) < k from j.2) le_rfl)
  have hdisjoint : Disjoint ({t : ℕ | t < k} : Set ℕ) ({k} : Set ℕ) := by
    rw [Set.disjoint_left]
    intro t ht htk
    exact (Nat.ne_of_lt ht) htk
  have hqueryRound : ProbabilityTheory.IndepFun query (round k) P :=
    SOptLib.iIndepFun_indepFun_strictPast_singleton
      round P hroundMeas hroundIndep
      (heterogeneousFiniteSumStrictPast
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
      ({t : ℕ | t < k} : Set ℕ) k hquery hdisjoint hstrict
  have hqueryWorker := hqueryRound.comp measurable_id
    (show Measurable
      (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (z.2.1 i, z.2.2 i)) by fun_prop)
  simpa [query, round, workerNoise, P, heterogeneousFiniteSumProcess,
    SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep] using
      hqueryWorker

/-! ### Full-interface density-correction countermodel

The scalar obstruction above is not, by itself, a counterexample to the
algorithmic corollaries.  The following private model supplies the concrete
`OnlineData` object needed for the theorem-level check: one worker, one
coordinate, deterministic samples, the quadratic `x ↦ ‖x‖²/2`, and identity
compression.  Its generated proof-exact process is ordinary gradient descent;
all stochastic and compression errors vanish definitionally. -/

private abbrev densityCounterCount : Count := ⟨1, by omega⟩

private abbrev DensityCounterSample
    (_ : Worker densityCounterCount) := Unit

private noncomputable def densityCounterProblem :
    OnlineProblem densityCounterCount densityCounterCount DensityCounterSample where
  sampleLoss _ _ x := ‖x‖ ^ 2 / 2
  sampleLaw _ := Measure.dirac ()
  sampleLaw_isProbability _ := by infer_instance
  sampleLoss_integrable _ _ := by simp

private noncomputable def densityCounterData :
    OnlineData densityCounterCount densityCounterCount DensityCounterSample Unit where
  problem := densityCounterProblem
  quantizer := onlineGeneratedIdentityQuantizer
  stepSize := ⟨1, by norm_num⟩
  refreshProbability := 1
  refresh_admissible := by constructor <;> norm_num

private noncomputable def densityCounterInitialPoint :
    Point densityCounterCount := EuclideanSpace.single 0 1

private theorem densityCounter_loss_hasGradientAt
    (x : Point densityCounterCount) :
    HasGradientAt (fun y : Point densityCounterCount => ‖y‖ ^ 2 / 2) x x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
  · funext y
    ring
  · ext y
    simp

private theorem densityCounter_stochasticGradient
    (i : Worker densityCounterCount) (xi : DensityCounterSample i)
    (x : Point densityCounterCount) :
    stochasticGradient densityCounterProblem i xi x = x := by
  unfold stochasticGradient
  exact (densityCounter_loss_hasGradientAt x).gradient

private theorem densityCounter_localObjective
    (i : Worker densityCounterCount) (x : Point densityCounterCount) :
    (onlineLocalProblemCorrected
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩).localLoss i x =
      ‖x‖ ^ 2 / 2 := by
  simp [onlineLocalProblemCorrected, densityCounterProblem]

private theorem densityCounter_globalObjective
    (x : Point densityCounterCount) :
    globalObjective
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) x =
      ‖x‖ ^ 2 / 2 := by
  simp [globalObjective, average, SOptLib.finiteUniformAverage,
    onlineLocalProblemCorrected, densityCounterProblem, densityCounterCount]

private theorem densityCounter_localGradient
    (i : Worker densityCounterCount) (x : Point densityCounterCount) :
    localGradient
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) i x = x := by
  unfold localGradient
  rw [show
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩).localLoss i =
        (fun y : Point densityCounterCount => ‖y‖ ^ 2 / 2) by
    funext y
    exact densityCounter_localObjective i y]
  exact (densityCounter_loss_hasGradientAt x).gradient

private theorem densityCounter_globalGradient
    (x : Point densityCounterCount) :
    globalGradient
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) x = x := by
  unfold globalGradient
  rw [show globalObjective
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) =
      (fun y : Point densityCounterCount => ‖y‖ ^ 2 / 2) by
    funext y
    exact densityCounter_globalObjective y]
  exact (densityCounter_loss_hasGradientAt x).gradient

private theorem densityCounter_uncorrectedLocalGradient
    (i : Worker densityCounterCount) (x : Point densityCounterCount) :
    localGradient (onlineLocalProblem densityCounterProblem) i x = x := by
  unfold localGradient
  rw [show (onlineLocalProblem densityCounterProblem).localLoss i =
      (fun y : Point densityCounterCount => ‖y‖ ^ 2 / 2) by
    funext y
    simp [onlineLocalProblem, expectedSampleLoss, densityCounterProblem]]
  exact (densityCounter_loss_hasGradientAt x).gradient

private theorem densityCounter_lowerBound :
    HasUniformLowerBound
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) 0 := by
  intro x
  rw [densityCounter_globalObjective]
  positivity

private theorem densityCounter_smooth :
    IsLocallySmooth
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
      (fun _ => 1) := by
  constructor
  · intro i
    intro x
    rw [show
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩).localLoss i =
          (fun y : Point densityCounterCount => ‖y‖ ^ 2 / 2) by
      funext y
      exact densityCounter_localObjective i y]
    exact (densityCounter_loss_hasGradientAt x).differentiableAt
  · intro i x y
    rw [densityCounter_localGradient, densityCounter_localGradient]
    simp

private theorem densityCounter_variance :
    OnlineUnbiasedBoundedVarianceCorrected
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
      (fun _ => 1) := by
  constructor
  · constructor
    · intro i
      norm_num
    · intro i x
      have hs : stochasticGradient densityCounterProblem i () x = x :=
        densityCounter_stochasticGradient i () x
      have hl : localGradient (onlineLocalProblem densityCounterProblem) i x = x :=
        densityCounter_uncorrectedLocalGradient i x
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [densityCounterProblem, hs] using
          (integrable_const (c := x) : Integrable
            (fun _ : Unit => x) (Measure.dirac ()))
      · simpa [densityCounterProblem, hs, hl] using
          (integrable_const (c := (0 : ℝ)) : Integrable
            (fun _ : Unit => (0 : ℝ)) (Measure.dirac ()))
      · simp only [densityCounterProblem, MeasureTheory.integral_dirac]
        exact hs.trans hl.symm
      · simp only [densityCounterProblem, MeasureTheory.integral_dirac,
          one_pow]
        have hz : ‖stochasticGradient densityCounterProblem i () x -
            localGradient (onlineLocalProblem densityCounterProblem) i x‖ ^ 2 = 0 := by
          rw [hs, hl, sub_self, norm_zero]
          norm_num
        have hz' : ‖stochasticGradient
              { sampleLoss := fun _ _ (y : Point densityCounterCount) => ‖y‖ ^ 2 / 2
                sampleLaw := fun _ => Measure.dirac ()
                sampleLaw_isProbability := densityCounterProblem.sampleLaw_isProbability
                sampleLoss_integrable := densityCounterProblem.sampleLoss_integrable }
              i () x -
            localGradient (onlineLocalProblem
              { sampleLoss := fun _ _ (y : Point densityCounterCount) => ‖y‖ ^ 2 / 2
                sampleLaw := fun _ => Measure.dirac ()
                sampleLaw_isProbability := densityCounterProblem.sampleLaw_isProbability
                sampleLoss_integrable := densityCounterProblem.sampleLoss_integrable }) i x‖ ^ 2 = 0 := by
          simpa only [densityCounterProblem] using hz
        rw [hz']
        norm_num
  · intro i
    filter_upwards [] with xi
    intro x
    exact (densityCounter_loss_hasGradientAt x).differentiableAt

private theorem densityCounter_batchDifference
    {b0 : Count}
    (batch : (i : Worker densityCounterCount) →
      Fin b0.1 → DensityCounterSample i)
    (i : Worker densityCounterCount)
    (xNext x : Point densityCounterCount) :
    onlineBatchDifference densityCounterProblem batch i xNext x = xNext - x := by
  letI : Nonempty (Fin b0.1) := ⟨⟨0, b0.2⟩⟩
  unfold onlineBatchDifference
  simp_rw [densityCounter_stochasticGradient]
  change average (fun _ : Fin b0.1 => xNext - x) = xNext - x
  unfold average
  exact SOptLib.finiteUniformAverage_const (xNext - x)

private theorem densityCounter_averageSmoothness
    {b0 : Count} {Omega : Type*} [MeasurableSpace Omega]
    (run : ℕ → Omega → State densityCounterCount) :
    OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
      run (fun _ => 0) := by
  constructor
  · intro i
    norm_num
  · intro k i path
    letI (w : Worker densityCounterCount) :
        IsProbabilityMeasure (densityCounterProblem.sampleLaw w) :=
      densityCounterProblem.sampleLaw_isProbability w
    letI : IsProbabilityMeasure (onlineBatchLaw densityCounterProblem b0) := by
      unfold onlineBatchLaw
      infer_instance
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    have hdiff : localGradientDifference
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        i xNext x = xNext - x := by
      rw [localGradientDifference, densityCounter_localGradient,
        densityCounter_localGradient]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [x, xNext] using
        (integrable_const (c := xNext - x) : Integrable
          (fun _ : (i : Worker densityCounterCount) →
            Fin b0.1 → DensityCounterSample i => xNext - x)
          (onlineBatchLaw densityCounterProblem b0))
    · simpa [x, xNext, hdiff] using
        (integrable_const (c := (0 : ℝ))
          (onlineBatchLaw densityCounterProblem b0))
    · simp [x, xNext, hdiff, densityCounter_batchDifference]
    · simp [x, xNext, hdiff, densityCounter_batchDifference]

private theorem densityCounter_workerEstimator_of_exact
    {b b0 : Count} (gamma : PositiveStepsize) (p : ℝ)
    (hp : RefreshProbabilityAdmissible p)
    (z : OnlineDriver densityCounterCount b b0 DensityCounterSample Unit)
    (s : State densityCounterCount) (hExact : s.g = s.x)
    (i : Worker densityCounterCount) :
    onlineWorkerEstimator
      (onlineDataWithParameters densityCounterData gamma p hp) z s i =
      primalStep (gamma : ℝ) s := by
  letI : Nonempty (Fin b.1) := ⟨⟨0, b.2⟩⟩
  unfold onlineWorkerEstimator
  split
  · simp only [onlineDataWithParameters, densityCounterData]
    simp_rw [densityCounter_stochasticGradient]
    change average (fun _ : Fin b.1 => primalStep (gamma : ℝ) s) = _
    unfold average
    exact SOptLib.finiteUniformAverage_const _
  · change s.g + onlineGeneratedIdentityQuantizer.apply
        (onlineBatchDifference densityCounterProblem z.differenceSample i
          (primalStep (gamma : ℝ) s) s.x) () = _
    rw [densityCounter_batchDifference]
    simp [onlineGeneratedIdentityQuantizer, hExact, sub_eq_add_neg]

private theorem densityCounter_step_of_exact
    {b b0 : Count} (gamma : PositiveStepsize) (p : ℝ)
    (hp : RefreshProbabilityAdmissible p)
    (z : OnlineDriver densityCounterCount b b0 DensityCounterSample Unit)
    (s : State densityCounterCount) (hExact : s.g = s.x) :
    onlineStep (onlineDataWithParameters densityCounterData gamma p hp) z s =
      { x := (1 - (gamma : ℝ)) • s.x
        g := (1 - (gamma : ℝ)) • s.x } := by
  have hx : primalStep (gamma : ℝ) s = (1 - (gamma : ℝ)) • s.x := by
    rw [primalStep_eq, hExact]
    module
  apply (stateEquivPair densityCounterCount).injective
  apply Prod.ext
  · simpa [onlineStep, onlineDataWithParameters] using hx
  · change average
        (onlineWorkerEstimator
          (onlineDataWithParameters densityCounterData gamma p hp) z s) =
        (1 - (gamma : ℝ)) • s.x
    rw [show onlineWorkerEstimator
        (onlineDataWithParameters densityCounterData gamma p hp) z s =
        (fun _ : Worker densityCounterCount => primalStep (gamma : ℝ) s) by
      funext i
      exact densityCounter_workerEstimator_of_exact gamma p hp z s hExact i]
    unfold average
    rw [SOptLib.finiteUniformAverage_const, hx]

private theorem densityCounter_process_state
    {b b0 : Count} (gamma : PositiveStepsize) (p : ℝ)
    (hp : RefreshProbabilityAdmissible p)
    (hBatch : OnlineBatchAdmissible b b0)
    (k : ℕ)
    (path : ℕ → OnlineRoundNoise densityCounterCount b b0
      DensityCounterSample Unit) :
    onlineCorrectedProofExactProcess
        (onlineDataWithParameters densityCounterData gamma p hp)
        (onlineExpectationRealization densityCounterProblem)
        densityCounterInitialPoint hBatch k path =
      { x := (1 - (gamma : ℝ)) ^ k • densityCounterInitialPoint
        g := (1 - (gamma : ℝ)) ^ k • densityCounterInitialPoint } := by
  induction k with
  | zero =>
      rw [show onlineCorrectedProofExactProcess
          (onlineDataWithParameters densityCounterData gamma p hp)
          (onlineExpectationRealization densityCounterProblem)
          densityCounterInitialPoint hBatch 0 path =
        onlineCorrectedExactInitialState
          (onlineDataWithParameters densityCounterData gamma p hp)
          (onlineExpectationRealization densityCounterProblem)
          densityCounterInitialPoint by rfl]
      simp only [pow_zero, one_smul]
      change
        ({ x := densityCounterInitialPoint
           g := globalGradient
             (onlineLocalProblemCorrected
               ⟨densityCounterProblem,
                 onlineExpectationRealization densityCounterProblem⟩)
             densityCounterInitialPoint } : State densityCounterCount) =
          { x := densityCounterInitialPoint, g := densityCounterInitialPoint }
      rw [densityCounter_globalGradient]
  | succ k ih =>
      rw [onlineCorrectedProofExactProcess_succ, ih]
      rw [densityCounter_step_of_exact gamma p hp]
      · apply (stateEquivPair densityCounterCount).injective
        apply Prod.ext <;> change
          (1 - (gamma : ℝ)) •
              ((1 - (gamma : ℝ)) ^ k • densityCounterInitialPoint) =
            (1 - (gamma : ℝ)) ^ (k + 1) • densityCounterInitialPoint
        all_goals rw [← mul_smul, pow_succ]
        all_goals congr 1 <;> ring
      · rfl

private noncomputable def densityCounterD3BaseBatch (eps : Accuracy) : Count :=
  ⟨max 1 (Nat.ceil (1 / (eps : ℝ) ^ 2)), by omega⟩

private noncomputable def densityCounterD3Batch (eps : Accuracy) : Count :=
  onlineNonconvexBatchScheduleFromBase densityCounterCount densityCounterCount 1
    densityCounterD3BaseBatch eps

private noncomputable def densityCounterD3Refresh (eps : Accuracy) : ℝ :=
  onlineDensityBatchRefreshSchedule
    (expectedDensity onlineGeneratedIdentityQuantizer)
    densityCounterCount (densityCounterD3Batch eps) densityCounterCount

private noncomputable def densityCounterD3Gamma
    (eps : Accuracy) : PositiveStepsize :=
  ⟨min (1 / (4 * ((densityCounterD3Batch eps).1 + 1 : ℕ)))
      ((eps : ℝ) ^ 6),
    lt_min (one_div_pos.mpr (by positivity)) (pow_pos eps.property 6)⟩

private noncomputable def densityCounterMu : PositivePLParameter :=
  ⟨(1 : ℝ) / 16, by norm_num⟩

private noncomputable def densityCounterD4BaseBatch (eps : Accuracy) : Count :=
  ⟨max 1 (Nat.ceil (16 / (eps : ℝ))), by omega⟩

private noncomputable def densityCounterD4Batch (eps : Accuracy) : Count :=
  onlinePLBatchScheduleFromBase densityCounterCount densityCounterCount 1
    densityCounterMu densityCounterD4BaseBatch eps

private noncomputable def densityCounterD4Refresh (eps : Accuracy) : ℝ :=
  onlineDensityBatchRefreshSchedule
    (expectedDensity onlineGeneratedIdentityQuantizer)
    densityCounterCount (densityCounterD4Batch eps) densityCounterCount

private noncomputable def densityCounterD4Gamma
    (eps : Accuracy) : PositiveStepsize :=
  ⟨min (1 / (4 * ((densityCounterD4Batch eps).1 + 1 : ℕ)))
      ((eps : ℝ) ^ 6),
    lt_min (one_div_pos.mpr (by positivity)) (pow_pos eps.property 6)⟩

private theorem densityCounter_initial_norm :
    ‖densityCounterInitialPoint‖ = 1 := by
  simp [densityCounterInitialPoint, densityCounterCount]

private theorem densityCounter_expectedDensity :
    expectedDensity onlineGeneratedIdentityQuantizer = 1 := by
  unfold expectedDensity
  apply le_antisymm
  · apply csSup_le
    · exact Set.range_nonempty _
    · rintro y ⟨v, rfl⟩
      simp only [onlineGeneratedIdentityQuantizer, MeasureTheory.integral_dirac]
      unfold quantizerNonzeroCount
      calc
        ((Finset.univ.filter fun j : Fin 1 => v j ≠ 0).card : ℝ) ≤
            (Finset.univ.card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := by simp
  · apply le_csSup
    · refine ⟨1, ?_⟩
      rintro y ⟨v, rfl⟩
      simp only [onlineGeneratedIdentityQuantizer, MeasureTheory.integral_dirac]
      unfold quantizerNonzeroCount
      calc
        ((Finset.univ.filter fun j : Fin 1 => v j ≠ 0).card : ℝ) ≤
            (Finset.univ.card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := by simp
    · refine ⟨densityCounterInitialPoint, ?_⟩
      simp only [onlineGeneratedIdentityQuantizer, MeasureTheory.integral_dirac]
      unfold quantizerNonzeroCount
      have hfilter :
          Finset.univ.filter
              (fun j : Fin 1 => densityCounterInitialPoint j ≠ 0) =
            Finset.univ := by
        ext j
        simp [densityCounterInitialPoint]
      rw [hfilter]
      simp

private theorem densityCounter_rootMeanSquare_one :
    rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)) = 1 := by
  simp [rootMeanSquare, meanSquare, average, SOptLib.finiteUniformAverage,
    densityCounterCount]

private theorem densityCounter_rootMeanSquare_zero :
    rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)) = 0 := by
  simp [rootMeanSquare, meanSquare, average, SOptLib.finiteUniformAverage,
    densityCounterCount]

private theorem densityCounter_varianceAggregateSq_one :
    varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)) = 1 := by
  simp [varianceAggregateSq, meanSquare, average, SOptLib.finiteUniformAverage,
    densityCounterCount]

private theorem densityCounter_D3_base_theta :
    AccuracyTheta
      (fun eps => ((densityCounterD3BaseBatch eps).1 : ℝ))
      (fun eps => 1 / (eps : ℝ) ^ 2) := by
  unfold AccuracyTheta
  constructor
  · have h := (positive_inverse_square_ceiling_schedule
      1 2 1 (by norm_num) (by norm_num) (by norm_num)).2
    convert h using 1 <;> funext eps <;>
      simp [densityCounterD3BaseBatch] <;> ring
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, Filter.Eventually.of_forall ?_⟩
    intro eps
    have hs : 0 ≤ 1 / (eps : ℝ) ^ 2 := by positivity
    have hceil := le_positive_ceil_max_one (1 / (eps : ℝ) ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg hs]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((densityCounterD3BaseBatch eps).1 : ℝ))]
    simpa [densityCounterD3BaseBatch] using hceil

private theorem densityCounter_D4_base_theta :
    AccuracyTheta
      (fun eps => ((densityCounterD4BaseBatch eps).1 : ℝ))
      (fun eps => 16 / (eps : ℝ)) := by
  unfold AccuracyTheta
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨3, ?_⟩
    have hEventually : ∀ᶠ eps : Accuracy in accuracyToZero,
        1 ≤ 16 / (eps : ℝ) := by
      rw [accuracyToZero]
      change {eps : Accuracy | 1 ≤ 16 / (eps : ℝ)} ∈
        Filter.comap (fun eps : Accuracy => ((eps : ℝ)⁻¹))
          (Filter.atTop : Filter ℝ)
      rw [Filter.mem_comap]
      refine ⟨Set.Ici 1, Filter.eventually_atTop.2 ⟨1, fun a ha => ha⟩, ?_⟩
      intro eps heps
      change 1 ≤ (eps : ℝ)⁻¹ at heps
      change 1 ≤ 16 * (eps : ℝ)⁻¹
      nlinarith
    filter_upwards [hEventually] with eps hscale
    let s : ℝ := 16 / (eps : ℝ)
    have hs : 1 ≤ s := by simpa [s] using hscale
    have hceil := natCast_max_one_ceil_le_add_two s (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((densityCounterD4BaseBatch eps).1 : ℝ))]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 16 / (eps : ℝ))]
    change ((max 1 (Nat.ceil s) : ℕ) : ℝ) ≤
      3 * (16 / (eps : ℝ))
    change ((max 1 (Nat.ceil s) : ℕ) : ℝ) ≤ 3 * s
    nlinarith
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, Filter.Eventually.of_forall ?_⟩
    intro eps
    let s : ℝ := 16 / (eps : ℝ)
    have hs : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg (by norm_num) eps.property.le
    have hceil : s ≤ ((max 1 (Nat.ceil s) : ℕ) : ℝ) :=
      le_positive_ceil_max_one s
    have hscalePos : 0 < 16 / (eps : ℝ) :=
      div_pos (by norm_num) eps.property
    rw [Real.norm_eq_abs, abs_of_pos hscalePos]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((densityCounterD4BaseBatch eps).1 : ℝ))]
    simpa [densityCounterD4BaseBatch, s] using hceil

private theorem densityCounter_D3_refresh_eq (eps : Accuracy) :
    densityCounterD3Refresh eps =
      1 / (((densityCounterD3Batch eps).1 : ℝ) + 1) := by
  unfold densityCounterD3Refresh onlineDensityBatchRefreshSchedule
  rw [densityCounter_expectedDensity]
  simp only [densityCounterCount, Nat.cast_one]
  rw [min_eq_right]
  · norm_num
  · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) <
        (((densityCounterD3Batch eps).1 + 1 : ℕ) : ℝ)) (by norm_num)]
    norm_num

private theorem densityCounter_D4_refresh_eq (eps : Accuracy) :
    densityCounterD4Refresh eps =
      1 / (((densityCounterD4Batch eps).1 : ℝ) + 1) := by
  unfold densityCounterD4Refresh onlineDensityBatchRefreshSchedule
  rw [densityCounter_expectedDensity]
  simp only [densityCounterCount, Nat.cast_one]
  rw [min_eq_right]
  · norm_num
  · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) <
        (((densityCounterD4Batch eps).1 + 1 : ℕ) : ℝ)) (by norm_num)]
    norm_num

private theorem densityCounter_D3_refresh_admissible (eps : Accuracy) :
    RefreshProbabilityAdmissible (densityCounterD3Refresh eps) := by
  rw [densityCounter_D3_refresh_eq]
  constructor
  · positivity
  · rw [div_le_iff₀ (show (0 : ℝ) <
        ((densityCounterD3Batch eps).1 : ℝ) + 1 by positivity)]
    norm_num

private theorem densityCounter_D4_refresh_admissible (eps : Accuracy) :
    RefreshProbabilityAdmissible (densityCounterD4Refresh eps) := by
  rw [densityCounter_D4_refresh_eq]
  constructor
  · positivity
  · rw [div_le_iff₀ (show (0 : ℝ) <
        ((densityCounterD4Batch eps).1 : ℝ) + 1 by positivity)]
    norm_num

private theorem densityCounter_D3_step (eps : Accuracy) :
    OnlineVRStepsizeCondition (densityCounterD3Gamma eps)
      (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
      (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
      (densityCounterD3Refresh eps) 1 densityCounterCount densityCounterCount := by
  rw [densityCounter_rootMeanSquare_one, densityCounter_rootMeanSquare_zero,
    densityCounter_D3_refresh_eq]
  unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition
  norm_num [densityCounterCount]
  let B : ℝ := ((densityCounterD3Batch eps).1 : ℝ)
  have hB : 1 ≤ B := by
    have hn : 1 ≤ (densityCounterD3Batch eps).1 :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (densityCounterD3Batch eps).2)
    dsimp [B]
    exact_mod_cast hn
  have hp : 0 < 1 / (B + 1) := by positivity
  have hratio : (1 - 1 / (B + 1)) / (1 / (B + 1)) = B := by
    field_simp [ne_of_gt hp]
    ring
  have hsqrt : Real.sqrt B ≤ B := by
    rw [Real.sqrt_le_iff]
    exact ⟨le_trans (by norm_num) hB, by nlinarith⟩
  have hgamma : (densityCounterD3Gamma eps : ℝ) ≤ 1 / (4 * (B + 1)) := by
    simpa [densityCounterD3Gamma, B] using
      (min_le_left
        (1 / (4 * (((densityCounterD3Batch eps).1 : ℝ) + 1)))
        ((eps : ℝ) ^ 6))
  have hden : 0 < 4 * (B + 1) := by positivity
  have hcalc :
      (densityCounterD3Gamma eps : ℝ) * (1 + Real.sqrt B) ≤ 1 := by
    calc
      (densityCounterD3Gamma eps : ℝ) * (1 + Real.sqrt B) ≤
        (1 / (4 * (B + 1))) * (1 + Real.sqrt B) := by gcongr
      _ ≤ (1 / (4 * (B + 1))) * (B + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hsqrt]) (by positivity)
      _ ≤ 1 := by field_simp [ne_of_gt hden] <;> norm_num
  have hinside :
      (1 - (B + 1)⁻¹) * (B + 1) = B := by
    field_simp [show B + 1 ≠ 0 by positivity]
    ring
  simpa [B, hinside] using hcalc

private theorem densityCounter_D4_step (eps : Accuracy) :
    OnlineVRPLStepsizeCondition (densityCounterD4Gamma eps)
      (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
      (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
      (densityCounterD4Refresh eps) 1 densityCounterMu
      densityCounterCount densityCounterCount := by
  rw [densityCounter_rootMeanSquare_one, densityCounter_rootMeanSquare_zero,
    densityCounter_D4_refresh_eq]
  unfold OnlineVRPLStepsizeCondition FiniteSumVRPLStepsizeCondition
  norm_num [densityCounterCount]
  let B : ℝ := ((densityCounterD4Batch eps).1 : ℝ)
  have hB : 1 ≤ B := by
    have hn : 1 ≤ (densityCounterD4Batch eps).1 :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (densityCounterD4Batch eps).2)
    dsimp [B]
    exact_mod_cast hn
  have hp : 0 < 1 / (B + 1) := by positivity
  have hratio : (2 * (1 - 1 / (B + 1))) / (1 / (B + 1)) = 2 * B := by
    field_simp [ne_of_gt hp]
    ring
  have hsqrt : Real.sqrt (2 * B) ≤ 2 * B := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hgamma : (densityCounterD4Gamma eps : ℝ) ≤ 1 / (4 * (B + 1)) := by
    simpa [densityCounterD4Gamma, B] using
      (min_le_left
        (1 / (4 * (((densityCounterD4Batch eps).1 : ℝ) + 1)))
        ((eps : ℝ) ^ 6))
  constructor
  · have hcalc :
        (densityCounterD4Gamma eps : ℝ) * (1 + Real.sqrt (2 * B)) ≤ 1 := by
      calc
        (densityCounterD4Gamma eps : ℝ) * (1 + Real.sqrt (2 * B)) ≤
          (1 / (4 * (B + 1))) * (1 + Real.sqrt (2 * B)) := by gcongr
        _ ≤ (1 / (4 * (B + 1))) * (2 * (B + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith [hsqrt]) (by positivity)
        _ ≤ 1 := by
          rw [show (1 / (4 * (B + 1))) * (2 * (B + 1)) = (1 / 2 : ℝ) by
            field_simp [show B + 1 ≠ 0 by positivity] <;> ring]
          norm_num
    have hinside :
        2 * (1 - (B + 1)⁻¹) * (B + 1) = 2 * B := by
      field_simp [show B + 1 ≠ 0 by positivity]
      ring
    simpa [B, hinside] using hcalc
  · have hcalc :
        2 * (densityCounterD4Gamma eps : ℝ) * (1 / 16) ≤ 1 / (B + 1) := by
      calc
        2 * (densityCounterD4Gamma eps : ℝ) * (1 / 16) ≤
            2 * (1 / (4 * (B + 1))) * (1 / 16) := by gcongr
        _ ≤ 1 / (B + 1) := by
          have hsmall : (1 / 32 : ℝ) / (B + 1) ≤ 1 / (B + 1) :=
            div_le_div_of_nonneg_right (by norm_num) (by positivity)
          convert hsmall using 1 <;>
            field_simp [show B + 1 ≠ 0 by positivity] <;> ring
    simpa [densityCounterMu, B, div_eq_mul_inv] using hcalc

private noncomputable def densityCounterZeroPoint : Point densityCounterCount := 0

private theorem densityCounter_PL :
    SatisfiesPL
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
      densityCounterMu densityCounterZeroPoint := by
  constructor
  · intro x
    rw [densityCounter_globalObjective, densityCounter_globalObjective]
    simp [densityCounterZeroPoint]
    positivity
  · intro x
    rw [densityCounter_globalObjective, densityCounter_globalObjective,
      densityCounter_globalGradient]
    simp [densityCounterZeroPoint, densityCounterMu]
    nlinarith [sq_nonneg ‖x‖]

private theorem densityCounter_D3_iteration_scale_eq (eps : Accuracy) :
    let P := onlineLocalProblemCorrected
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
    let ratio := onlineDensityBatchRatio densityCounterCount densityCounterCount
      densityCounterCount (expectedDensity onlineGeneratedIdentityQuantizer)
      (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
      ((eps : ℝ) ^ 2)
    (globalObjective P densityCounterInitialPoint - 0) / (eps : ℝ) ^ 2 *
        vrIterationBracket
          (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
          (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
          1 ratio densityCounterCount densityCounterCount =
      (1 / 2 : ℝ) / (eps : ℝ) ^ 2 * (1 + 1 / (eps : ℝ)) := by
  dsimp only
  rw [densityCounter_globalObjective, densityCounter_initial_norm,
    densityCounter_expectedDensity, densityCounter_varianceAggregateSq_one,
    densityCounter_rootMeanSquare_one, densityCounter_rootMeanSquare_zero]
  have hsqrt : Real.sqrt (1 / (eps : ℝ) ^ 2) = 1 / (eps : ℝ) := by
    rw [show 1 / (eps : ℝ) ^ 2 = (1 / (eps : ℝ)) ^ 2 by
      field_simp [ne_of_gt eps.property]]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr eps.property)]
  simp [densityCounterCount, onlineDensityBatchRatio, vrIterationBracket,
    max_eq_right (by positivity : (0 : ℝ) ≤ 1 / (eps : ℝ) ^ 2),
    hsqrt]
  left
  rw [max_eq_right (inv_nonneg.mpr (sq_nonneg _))]
  simpa [one_div] using hsqrt

private def densityCounterD3FormerEndpoint : Prop :=
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun eps => NonconvexAccuracy (K eps)
          (onlineLocalProblemCorrected
            ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
          (onlineCorrectedProofExactProcess
            (A := onlineDataWithParameters densityCounterData
              (densityCounterD3Gamma eps) (densityCounterD3Refresh eps)
              (densityCounter_D3_refresh_admissible eps))
            (onlineExpectationRealization densityCounterProblem)
            densityCounterInitialPoint
            (onlineNonconvexBatchScheduleFromBase_admissible
              densityCounterCount densityCounterCount 1
              densityCounterD3BaseBatch eps))
          (onlineProofExactPathLaw
            (A := onlineDataWithParameters densityCounterData
              (densityCounterD3Gamma eps) (densityCounterD3Refresh eps)
              (densityCounter_D3_refresh_admissible eps))) eps)
        (fun eps =>
          let ratio := onlineDensityBatchRatio densityCounterCount
            densityCounterCount densityCounterCount
            (expectedDensity onlineGeneratedIdentityQuantizer)
            (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
            ((eps : ℝ) ^ 2)
          (globalObjective
              (onlineLocalProblemCorrected
                ⟨densityCounterProblem,
                  onlineExpectationRealization densityCounterProblem⟩)
              densityCounterInitialPoint - 0) / (eps : ℝ) ^ 2 *
            vrIterationBracket
              (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
              (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
              1 ratio densityCounterCount densityCounterCount)
        (fun eps => onlineOracleCallCount (densityCounterD3Batch eps)
          densityCounterCount (K eps) (densityCounterD3Refresh eps))
        (fun eps => onlineNonconvexOracleScale
          (globalObjective
              (onlineLocalProblemCorrected
                ⟨densityCounterProblem,
                  onlineExpectationRealization densityCounterProblem⟩)
              densityCounterInitialPoint - 0)
          (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
          (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
          1 (expectedDensity onlineGeneratedIdentityQuantizer)
          (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
          eps densityCounterCount densityCounterCount densityCounterCount)
        (fun eps => allWorkerCommunicationCount densityCounterCount (K eps)
          (densityCounterD3Refresh eps)
          (expectedDensity onlineGeneratedIdentityQuantizer))
        (fun eps =>
          let ratio := onlineDensityBatchRatio densityCounterCount
            densityCounterCount densityCounterCount
            (expectedDensity onlineGeneratedIdentityQuantizer)
            (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
            ((eps : ℝ) ^ 2)
          densityCounterCount.1 +
            (globalObjective
                (onlineLocalProblemCorrected
                  ⟨densityCounterProblem,
                    onlineExpectationRealization densityCounterProblem⟩)
                densityCounterInitialPoint - 0) *
              expectedDensity onlineGeneratedIdentityQuantizer / (eps : ℝ) ^ 2 *
              vrIterationBracket
                (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
                (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
                1 ratio densityCounterCount densityCounterCount)

private theorem densityCounter_D3_supplied_stepsize_conclusion_false :
    ¬ densityCounterD3FormerEndpoint := by
  unfold densityCounterD3FormerEndpoint
  rintro ⟨K, hEndpoint⟩
  unfold ThreeEndpointComplexity at hEndpoint
  rcases hEndpoint with ⟨hAccuracy, hIteration, _hOracle, _hCommunication⟩
  have hScaleEq :
      (fun eps : Accuracy =>
        let ratio := onlineDensityBatchRatio densityCounterCount
          densityCounterCount densityCounterCount
          (expectedDensity onlineGeneratedIdentityQuantizer)
          (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
          ((eps : ℝ) ^ 2)
        (globalObjective
            (onlineLocalProblemCorrected
              ⟨densityCounterProblem,
                onlineExpectationRealization densityCounterProblem⟩)
            densityCounterInitialPoint - 0) / (eps : ℝ) ^ 2 *
          vrIterationBracket
            (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
            (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
            1 ratio densityCounterCount densityCounterCount) =
        (fun eps : Accuracy => (1 / 2 : ℝ) / (eps : ℝ) ^ 2 *
          (1 + 1 / (eps : ℝ))) := by
    funext eps
    exact densityCounter_D3_iteration_scale_eq eps
  rw [hScaleEq] at hIteration
  have hKBigO : AccuracyBigO (fun eps => ((K eps).1 : ℝ))
      (fun eps => (1 / 2 : ℝ) / (eps : ℝ) ^ 2 *
        (1 + 1 / (eps : ℝ))) := by
    rcases hIteration with hzero | hbig
    · have hz := hzero.1 ⟨1, by norm_num⟩
      norm_num at hz
    · exact hbig
  unfold AccuracyBigO at hKBigO
  rw [Asymptotics.isBigO_iff] at hKBigO
  rcases hKBigO with ⟨c, hc⟩
  rw [accuracyToZero] at hc
  change {eps : Accuracy |
      ‖((K eps).1 : ℝ)‖ ≤ c *
        ‖(1 / 2 : ℝ) / (eps : ℝ) ^ 2 * (1 + 1 / (eps : ℝ))‖} ∈
    Filter.comap (fun eps : Accuracy => ((eps : ℝ)⁻¹))
      (Filter.atTop : Filter ℝ) at hc
  rw [Filter.mem_comap] at hc
  rcases hc with ⟨s, hs, hsSub⟩
  rcases Filter.eventually_atTop.1 hs with ⟨a, ha⟩
  let x : ℝ := max 4 (max a (|c| + 1))
  have hx4 : 4 ≤ x := le_max_left _ _
  have hxa : a ≤ x :=
    (le_max_left a (|c| + 1)).trans (le_max_right 4 _)
  have hxc : |c| + 1 ≤ x :=
    (le_max_right a (|c| + 1)).trans (le_max_right 4 _)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx4
  let eps : Accuracy := ⟨1 / x, one_div_pos.mpr hxpos⟩
  have hepsInv : ((eps : ℝ)⁻¹) = x := by
    dsimp [eps]
    field_simp [ne_of_gt hxpos]
  have hepsMem : ((eps : ℝ)⁻¹) ∈ s := by
    apply ha
    simpa [hepsInv] using hxa
  have hineq := hsSub hepsMem
  change ‖((K eps).1 : ℝ)‖ ≤ c *
    ‖(1 / 2 : ℝ) / (eps : ℝ) ^ 2 * (1 + 1 / (eps : ℝ))‖ at hineq
  have hepsSq : (eps : ℝ) ^ 2 = 1 / x ^ 2 := by
    dsimp [eps]
    field_simp [ne_of_gt hxpos]
  have hepsInv' : 1 / (eps : ℝ) = x := by
    dsimp [eps]
    field_simp [ne_of_gt hxpos]
  rw [hepsSq, hepsInv'] at hineq
  have hscalePos : 0 < (1 / 2 : ℝ) / (1 / x ^ 2) * (1 + x) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((K eps).1 : ℝ)),
    Real.norm_eq_abs, abs_of_pos hscalePos] at hineq
  have hcLt : c < x := (le_abs_self c).trans_lt (by linarith)
  have hKlt : ((K eps).1 : ℝ) < x ^ 4 := by
    have hscaleBound : (1 / 2 : ℝ) / (1 / x ^ 2) * (1 + x) ≤ x ^ 3 := by
      field_simp [ne_of_gt hxpos]
      nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx4)]
    have hcpos : 0 ≤ c := by
      by_contra hcneg
      have : c < 0 := lt_of_not_ge hcneg
      nlinarith [show (0 : ℝ) < ((K eps).1 : ℝ) by exact_mod_cast (K eps).2]
    calc
      ((K eps).1 : ℝ) ≤ c * ((1 / 2 : ℝ) / (1 / x ^ 2) * (1 + x)) := hineq
      _ ≤ c * x ^ 3 := mul_le_mul_of_nonneg_left hscaleBound hcpos
      _ < x * x ^ 3 := mul_lt_mul_of_pos_right hcLt (pow_pos hxpos 3)
      _ = x ^ 4 := by ring
  have hgamma : (densityCounterD3Gamma eps : ℝ) ≤ 1 / x ^ 6 := by
    calc
      (densityCounterD3Gamma eps : ℝ) ≤ (eps : ℝ) ^ 6 := by
        exact min_le_right _ _
      _ = 1 / x ^ 6 := by
        dsimp [eps]
        field_simp [ne_of_gt hxpos]
  have hKgamma : ((K eps).1 : ℝ) * (densityCounterD3Gamma eps : ℝ) < 1 / 4 := by
    have hg0 : 0 ≤ (densityCounterD3Gamma eps : ℝ) :=
      (densityCounterD3Gamma eps).property.le
    calc
      ((K eps).1 : ℝ) * (densityCounterD3Gamma eps : ℝ) <
          x ^ 4 * (densityCounterD3Gamma eps : ℝ) :=
        mul_lt_mul_of_pos_right hKlt (densityCounterD3Gamma eps).property
      _ ≤ x ^ 4 * (1 / x ^ 6) := mul_le_mul_of_nonneg_left hgamma (pow_nonneg hxpos.le 4)
      _ ≤ 1 / 4 := by
        field_simp [ne_of_gt hxpos]
        nlinarith [sq_nonneg x]
  let run := onlineCorrectedProofExactProcess
    (A := onlineDataWithParameters densityCounterData
      (densityCounterD3Gamma eps) (densityCounterD3Refresh eps)
      (densityCounter_D3_refresh_admissible eps))
    (onlineExpectationRealization densityCounterProblem)
    densityCounterInitialPoint
    (onlineNonconvexBatchScheduleFromBase_admissible densityCounterCount
      densityCounterCount 1 densityCounterD3BaseBatch eps)
  let law := onlineProofExactPathLaw
    (b := densityCounterD3Batch eps) (b0 := densityCounterCount)
    (A := onlineDataWithParameters densityCounterData
      (densityCounterD3Gamma eps) (densityCounterD3Refresh eps)
      (densityCounter_D3_refresh_admissible eps))
  letI (w : Worker densityCounterCount) :
      IsProbabilityMeasure (densityCounterProblem.sampleLaw w) :=
    densityCounterProblem.sampleLaw_isProbability w
  letI : IsProbabilityMeasure
      (onlineBatchLaw densityCounterProblem (densityCounterD3Batch eps)) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure
      (onlineBatchLaw densityCounterProblem densityCounterCount) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure onlineGeneratedIdentityQuantizer.law :=
    onlineGeneratedIdentityQuantizer.law_isProbability
  letI : IsProbabilityMeasure
      (workerCompressionLaw (n := densityCounterCount)
        onlineGeneratedIdentityQuantizer) := by
    unfold workerCompressionLaw
    infer_instance
  letI : IsProbabilityMeasure
      (refreshLaw (densityCounterD3Refresh eps)
        (densityCounter_D3_refresh_admissible eps)) := by
    unfold refreshLaw
    infer_instance
  letI : IsProbabilityMeasure
      (onlineRoundLaw (b := densityCounterD3Batch eps)
        (b0 := densityCounterCount)
        (onlineDataWithParameters densityCounterData
          (densityCounterD3Gamma eps) (densityCounterD3Refresh eps)
          (densityCounter_D3_refresh_admissible eps))) := by
    unfold onlineRoundLaw
    simp only [onlineDataWithParameters, densityCounterData]
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold onlineProofExactPathLaw
    infer_instance
  have hFiber (k : Fin (K eps).1) : Integrable
      (fun path => ‖globalGradient
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run k.1 path).x‖ ^ 2) law := by
    have hfun : (fun path => ‖globalGradient
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run k.1 path).x‖ ^ 2) =
        (fun _ => ‖(1 - (densityCounterD3Gamma eps : ℝ)) ^ k.1 •
          densityCounterInitialPoint‖ ^ 2) := by
      funext path
      dsimp [run]
      rw [densityCounter_process_state, densityCounter_globalGradient]
    exact hfun.symm ▸ integrable_const (μ := law) _
  have hAverage := uniformOutput_expectation_eq_average run law
    (fun x => ‖globalGradient
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) x‖ ^ 2)
    hFiber
  have hPoint (k : Fin (K eps).1) :
      (1 / 2 : ℝ) ≤ ∫ path, ‖globalGradient
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run k.1 path).x‖ ^ 2 ∂law := by
    have hg1 : (densityCounterD3Gamma eps : ℝ) ≤ 1 := by
      exact hgamma.trans (by
        have : 1 ≤ x ^ 6 := one_le_pow₀ (by linarith : 1 ≤ x)
        exact (div_le_one (pow_pos hxpos 6)).2 this)
    have hkK : (k.1 : ℝ) ≤ ((K eps).1 : ℝ) := by
      exact_mod_cast Nat.le_of_lt k.2
    have hkgamma : (k.1 : ℝ) * (densityCounterD3Gamma eps : ℝ) < 1 / 4 :=
      (mul_le_mul_of_nonneg_right hkK (densityCounterD3Gamma eps).property.le).trans_lt hKgamma
    have hbern : 1 - (k.1 : ℝ) * (densityCounterD3Gamma eps : ℝ) ≤
        (1 - (densityCounterD3Gamma eps : ℝ)) ^ k.1 := by
      simpa [sub_eq_add_neg, mul_neg] using
        (one_add_mul_le_pow (a := -(densityCounterD3Gamma eps : ℝ))
          (by linarith : (-2 : ℝ) ≤
            -(densityCounterD3Gamma eps : ℝ)) k.1)
    have hpow : 3 / 4 < (1 - (densityCounterD3Gamma eps : ℝ)) ^ k.1 := by
      linarith
    have hfun : (fun path => ‖globalGradient
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run k.1 path).x‖ ^ 2) =
        (fun _ => ((1 - (densityCounterD3Gamma eps : ℝ)) ^ k.1) ^ 2) := by
      funext path
      dsimp [run]
      rw [densityCounter_process_state, densityCounter_globalGradient]
      simp only [norm_smul, Real.norm_eq_abs]
      rw [densityCounter_initial_norm, mul_one, sq_abs]
    have hIntegral : (∫ path, ‖globalGradient
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run k.1 path).x‖ ^ 2 ∂law) =
        ((1 - (densityCounterD3Gamma eps : ℝ)) ^ k.1) ^ 2 := by
      calc
        _ = ∫ _path, ((1 - (densityCounterD3Gamma eps : ℝ)) ^ k.1) ^ 2 ∂law :=
          integral_congr_ae (Filter.Eventually.of_forall fun path => congrFun hfun path)
        _ = _ := by rw [integral_const, probReal_univ]; norm_num
    rw [hIntegral]
    nlinarith [sq_nonneg ((1 - (densityCounterD3Gamma eps : ℝ)) ^ k.1)]
  have hAvgLower : (1 / 2 : ℝ) ≤
      average (fun k : Fin (K eps).1 => ∫ path, ‖globalGradient
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run k.1 path).x‖ ^ 2 ∂law) := by
    letI : Nonempty (Worker (K eps)) := ⟨⟨0, (K eps).2⟩⟩
    have h := average_le_average_of_pointwise (n := K eps)
      (f := fun _ : Worker (K eps) => (1 / 2 : ℝ)) hPoint
    rw [show average (fun _ : Worker (K eps) => (1 / 2 : ℝ)) = 1 / 2 by
      unfold average
      exact SOptLib.finiteUniformAverage_const _] at h
    exact h
  have hAcc :
      (∫ z, ‖globalGradient
          (onlineLocalProblemCorrected
            ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
          (uniformOutput (K := K eps) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law (K eps)) ≤ (eps : ℝ) ^ 2 := by
    simpa [run, law, densityCounterD3Batch] using (hAccuracy eps).2
  have hAverage' :
      (∫ z, ‖globalGradient
          (onlineLocalProblemCorrected
            ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
          (uniformOutput (K := K eps) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law (K eps)) =
        average (fun k : Fin (K eps).1 => ∫ path, ‖globalGradient
          (onlineLocalProblemCorrected
            ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
          (run k.1 path).x‖ ^ 2 ∂law) := by
    simpa [densityCounterD3Batch] using hAverage
  rw [hAverage'] at hAcc
  have hepsSmall : (eps : ℝ) ^ 2 < 1 / 2 := by
    dsimp [eps]
    field_simp [ne_of_gt hxpos]
    nlinarith [sq_nonneg x]
  linarith

private theorem densityCounter_D4_iteration_scale_eq (eps : Accuracy) :
    let P := onlineLocalProblemCorrected
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
    let ratio := onlineDensityBatchRatio densityCounterCount densityCounterCount
      densityCounterCount (expectedDensity onlineGeneratedIdentityQuantizer)
      (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
      (densityCounterMu * (eps : ℝ))
    max (1 / densityCounterD4Refresh eps)
        (vrIterationBracket
          (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
          (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
          1 ratio densityCounterCount densityCounterCount / densityCounterMu) *
      Real.log ((globalObjective P densityCounterInitialPoint -
        globalObjective P densityCounterZeroPoint) / (eps : ℝ)) =
    max (((densityCounterD4Batch eps).1 : ℝ) + 1)
        (16 * (1 + Real.sqrt (16 / (eps : ℝ)))) *
      Real.log ((1 / 2 : ℝ) / (eps : ℝ)) := by
  dsimp only
  rw [densityCounter_D4_refresh_eq, densityCounter_globalObjective,
    densityCounter_globalObjective, densityCounter_initial_norm,
    densityCounter_expectedDensity, densityCounter_varianceAggregateSq_one,
    densityCounter_rootMeanSquare_one, densityCounter_rootMeanSquare_zero]
  have hrefresh : 1 / (1 / (((densityCounterD4Batch eps).1 : ℝ) + 1)) =
      ((densityCounterD4Batch eps).1 : ℝ) + 1 := by
    field_simp [show (0 : ℝ) < ((densityCounterD4Batch eps).1 : ℝ) + 1 by
      positivity]
  rw [hrefresh]
  have hsqrt : Real.sqrt (16 / (eps : ℝ)) =
      Real.sqrt 16 / Real.sqrt (eps : ℝ) :=
    Real.sqrt_div (by norm_num) _
  simp [densityCounterZeroPoint, densityCounterMu, densityCounterCount,
    onlineDensityBatchRatio, vrIterationBracket,
    max_eq_right (show (0 : ℝ) ≤ 16 / (eps : ℝ) from
      div_nonneg (by norm_num) eps.property.le), hsqrt]
  left
  congr 1
  rw [show (eps : ℝ)⁻¹ * 16 = 16 / (eps : ℝ) by ring,
    max_eq_right (show (0 : ℝ) ≤ 16 / (eps : ℝ) from
      div_nonneg (by norm_num) eps.property.le), hsqrt]
  norm_num
  ring

private def densityCounterD4FormerEndpoint : Prop :=
    ∃ K : Accuracy → Count,
      ThreeEndpointComplexity K
        (fun eps => PLAccuracy (K eps)
          (onlineLocalProblemCorrected
            ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
          (onlineCorrectedProofExactProcess
            (A := onlineDataWithParameters densityCounterData
              (densityCounterD4Gamma eps) (densityCounterD4Refresh eps)
              (densityCounter_D4_refresh_admissible eps))
            (onlineExpectationRealization densityCounterProblem)
            densityCounterInitialPoint
            (onlinePLBatchScheduleFromBase_admissible densityCounterCount
              densityCounterCount 1 densityCounterMu
              densityCounterD4BaseBatch eps))
          (onlineProofExactPathLaw
            (A := onlineDataWithParameters densityCounterData
              (densityCounterD4Gamma eps) (densityCounterD4Refresh eps)
              (densityCounter_D4_refresh_admissible eps)))
          densityCounterZeroPoint eps)
        (fun eps =>
          let ratio := onlineDensityBatchRatio densityCounterCount
            densityCounterCount densityCounterCount
            (expectedDensity onlineGeneratedIdentityQuantizer)
            (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
            (densityCounterMu * (eps : ℝ))
          max (1 / densityCounterD4Refresh eps)
            (vrIterationBracket
              (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
              (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
              1 ratio densityCounterCount densityCounterCount / densityCounterMu) *
            Real.log ((globalObjective
                (onlineLocalProblemCorrected
                  ⟨densityCounterProblem,
                    onlineExpectationRealization densityCounterProblem⟩)
                densityCounterInitialPoint -
              globalObjective
                (onlineLocalProblemCorrected
                  ⟨densityCounterProblem,
                    onlineExpectationRealization densityCounterProblem⟩)
                densityCounterZeroPoint) / (eps : ℝ)))
        (fun eps => onlineOracleCallCount (densityCounterD4Batch eps)
          densityCounterCount (K eps) (densityCounterD4Refresh eps))
        (fun eps => onlinePLOracleScale
          (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
          (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
          1 densityCounterMu (densityCounterD4Refresh eps)
          (expectedDensity onlineGeneratedIdentityQuantizer)
          (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
          eps (Real.log ((globalObjective
              (onlineLocalProblemCorrected
                ⟨densityCounterProblem,
                  onlineExpectationRealization densityCounterProblem⟩)
              densityCounterInitialPoint -
            globalObjective
              (onlineLocalProblemCorrected
                ⟨densityCounterProblem,
                  onlineExpectationRealization densityCounterProblem⟩)
              densityCounterZeroPoint) / (eps : ℝ)))
          densityCounterCount densityCounterCount densityCounterCount)
        (fun eps => allWorkerCommunicationCount densityCounterCount (K eps)
          (densityCounterD4Refresh eps)
          (expectedDensity onlineGeneratedIdentityQuantizer))
        (fun eps =>
          let ratio := onlineDensityBatchRatio densityCounterCount
            densityCounterCount densityCounterCount
            (expectedDensity onlineGeneratedIdentityQuantizer)
            (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
            (densityCounterMu * (eps : ℝ))
          let factor := max (1 / densityCounterD4Refresh eps)
            (vrIterationBracket
              (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
              (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
              1 ratio densityCounterCount densityCounterCount / densityCounterMu)
          densityCounterCount.1 +
            expectedDensity onlineGeneratedIdentityQuantizer * factor *
              Real.log ((globalObjective
                  (onlineLocalProblemCorrected
                    ⟨densityCounterProblem,
                      onlineExpectationRealization densityCounterProblem⟩)
                  densityCounterInitialPoint -
                globalObjective
                  (onlineLocalProblemCorrected
                    ⟨densityCounterProblem,
                      onlineExpectationRealization densityCounterProblem⟩)
                  densityCounterZeroPoint) / (eps : ℝ)))

private theorem densityCounter_D4_supplied_stepsize_conclusion_false :
    ¬ densityCounterD4FormerEndpoint := by
  unfold densityCounterD4FormerEndpoint
  rintro ⟨K, hEndpoint⟩
  unfold ThreeEndpointComplexity at hEndpoint
  rcases hEndpoint with ⟨hAccuracy, hIteration, _hOracle, _hCommunication⟩
  have hScaleEq :
      (fun eps : Accuracy =>
        let ratio := onlineDensityBatchRatio densityCounterCount
          densityCounterCount densityCounterCount
          (expectedDensity onlineGeneratedIdentityQuantizer)
          (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
          (densityCounterMu * (eps : ℝ))
        max (1 / densityCounterD4Refresh eps)
          (vrIterationBracket
            (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
            (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
            1 ratio densityCounterCount densityCounterCount / densityCounterMu) *
          Real.log ((globalObjective
              (onlineLocalProblemCorrected
                ⟨densityCounterProblem,
                  onlineExpectationRealization densityCounterProblem⟩)
              densityCounterInitialPoint -
            globalObjective
              (onlineLocalProblemCorrected
                ⟨densityCounterProblem,
                  onlineExpectationRealization densityCounterProblem⟩)
              densityCounterZeroPoint) / (eps : ℝ))) =
      (fun eps : Accuracy =>
        max (((densityCounterD4Batch eps).1 : ℝ) + 1)
            (16 * (1 + Real.sqrt (16 / (eps : ℝ)))) *
          Real.log ((1 / 2 : ℝ) / (eps : ℝ))) := by
    funext eps
    exact densityCounter_D4_iteration_scale_eq eps
  rw [hScaleEq] at hIteration
  let scale : Accuracy → ℝ := fun eps =>
    max (((densityCounterD4Batch eps).1 : ℝ) + 1)
        (16 * (1 + Real.sqrt (16 / (eps : ℝ)))) *
      Real.log ((1 / 2 : ℝ) / (eps : ℝ))
  have hKBigO : AccuracyBigO (fun eps => ((K eps).1 : ℝ)) scale := by
    rcases hIteration with hzero | hbig
    · let eps₁ : Accuracy := ⟨1 / 4, by norm_num⟩
      have hz := hzero.1 eps₁
      have hlog : 0 < Real.log ((1 / 2 : ℝ) / (eps₁ : ℝ)) := by
        apply Real.log_pos
        norm_num [eps₁]
      have hfac : 0 < max (((densityCounterD4Batch eps₁).1 : ℝ) + 1)
          (16 * (1 + Real.sqrt (16 / (eps₁ : ℝ)))) :=
        lt_of_lt_of_le (by positivity) (le_max_left _ _)
      change scale eps₁ = 0 at hz
      dsimp [scale] at hz
      nlinarith
    · simpa [scale] using hbig
  unfold AccuracyBigO at hKBigO
  rw [Asymptotics.isBigO_iff] at hKBigO
  rcases hKBigO with ⟨c, hc⟩
  rw [accuracyToZero] at hc
  change {eps : Accuracy | ‖((K eps).1 : ℝ)‖ ≤ c * ‖scale eps‖} ∈
    Filter.comap (fun eps : Accuracy => ((eps : ℝ)⁻¹))
      (Filter.atTop : Filter ℝ) at hc
  rw [Filter.mem_comap] at hc
  rcases hc with ⟨s, hs, hsSub⟩
  rcases Filter.eventually_atTop.1 hs with ⟨a, ha⟩
  let x : ℝ := max 4 (max a (100 * (|c| + 1)))
  have hx4 : 4 ≤ x := le_max_left _ _
  have hxa : a ≤ x :=
    (le_max_left a (100 * (|c| + 1))).trans (le_max_right 4 _)
  have hxc : 100 * (|c| + 1) ≤ x :=
    (le_max_right a (100 * (|c| + 1))).trans (le_max_right 4 _)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx4
  let eps : Accuracy := ⟨1 / x, one_div_pos.mpr hxpos⟩
  have hepsInv : ((eps : ℝ)⁻¹) = x := by
    dsimp [eps]
    field_simp [ne_of_gt hxpos]
  have hepsMem : ((eps : ℝ)⁻¹) ∈ s := by
    apply ha
    simpa [hepsInv] using hxa
  have hineq := hsSub hepsMem
  change ‖((K eps).1 : ℝ)‖ ≤ c * ‖scale eps‖ at hineq
  have hceil16 := natCast_max_one_ceil_le_add_two (16 * x) (by positivity)
  have hceil32 := natCast_max_one_ceil_le_add_two (32 * x) (by positivity)
  have hBatchBound : ((densityCounterD4Batch eps).1 : ℝ) ≤ 48 * x + 5 := by
    unfold densityCounterD4Batch onlinePLBatchScheduleFromBase
      densityCounterD4BaseBatch densityCounterMu
    simp only [densityCounterCount, Nat.cast_add, Nat.cast_one]
    have harg16 : 16 / (eps : ℝ) = 16 * x := by
      dsimp [eps]
      field_simp [ne_of_gt hxpos]
    have harg32 : 2 * 1 / (1 * (1 / 16) * (eps : ℝ)) = 32 * x := by
      dsimp [eps]
      field_simp [ne_of_gt hxpos]
      ring
    rw [harg16, harg32]
    linarith
  have hsqrt : Real.sqrt (16 * x) ≤ 4 * x := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg x]
  have hfactor : max (((densityCounterD4Batch eps).1 : ℝ) + 1)
      (16 * (1 + Real.sqrt (16 / (eps : ℝ)))) ≤ 68 * x := by
    rw [max_le_iff]
    constructor
    · linarith
    · have harg : 16 / (eps : ℝ) = 16 * x := by
        dsimp [eps]
        field_simp [ne_of_gt hxpos]
      rw [harg]
      nlinarith
  have hlogPos : 0 < Real.log ((1 / 2 : ℝ) / (eps : ℝ)) := by
    apply Real.log_pos
    dsimp [eps]
    field_simp [ne_of_gt hxpos]
    nlinarith
  have hlogBound : Real.log ((1 / 2 : ℝ) / (eps : ℝ)) ≤ x := by
    have hargPos : 0 < (1 / 2 : ℝ) / (eps : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hargPos
    dsimp [eps] at h ⊢
    field_simp [ne_of_gt hxpos] at h ⊢
    nlinarith
  have hscalePos : 0 < scale eps := by
    dsimp [scale]
    exact mul_pos (lt_of_lt_of_le (by positivity) (le_max_left _ _)) hlogPos
  have hscaleBound : scale eps ≤ 68 * x ^ 2 := by
    dsimp [scale]
    exact (mul_le_mul hfactor hlogBound hlogPos.le (by positivity)).trans_eq (by ring)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ((K eps).1 : ℝ)),
    Real.norm_eq_abs, abs_of_pos hscalePos] at hineq
  have hcpos : 0 ≤ c := by
    by_contra hcneg
    have : c < 0 := lt_of_not_ge hcneg
    nlinarith [show (0 : ℝ) < ((K eps).1 : ℝ) by exact_mod_cast (K eps).2]
  have hc68 : 68 * c < x := by
    have hcabs : c ≤ |c| := le_abs_self c
    nlinarith
  have hKlt : ((K eps).1 : ℝ) < x ^ 3 := by
    calc
      ((K eps).1 : ℝ) ≤ c * scale eps := hineq
      _ ≤ c * (68 * x ^ 2) := mul_le_mul_of_nonneg_left hscaleBound hcpos
      _ < x * x ^ 2 := by nlinarith [pow_pos hxpos 2]
      _ = x ^ 3 := by ring
  have hgamma : (densityCounterD4Gamma eps : ℝ) ≤ 1 / x ^ 6 := by
    calc
      (densityCounterD4Gamma eps : ℝ) ≤ (eps : ℝ) ^ 6 := min_le_right _ _
      _ = 1 / x ^ 6 := by
        dsimp [eps]
        field_simp [ne_of_gt hxpos]
  have hKgamma : ((K eps).1 : ℝ) * (densityCounterD4Gamma eps : ℝ) < 1 / 4 := by
    calc
      ((K eps).1 : ℝ) * (densityCounterD4Gamma eps : ℝ) <
          x ^ 3 * (densityCounterD4Gamma eps : ℝ) :=
        mul_lt_mul_of_pos_right hKlt (densityCounterD4Gamma eps).property
      _ ≤ x ^ 3 * (1 / x ^ 6) :=
        mul_le_mul_of_nonneg_left hgamma (pow_nonneg hxpos.le 3)
      _ < 1 / 4 := by
        field_simp [ne_of_gt hxpos]
        nlinarith [pow_pos hxpos 3]
  let run := onlineCorrectedProofExactProcess
    (A := onlineDataWithParameters densityCounterData
      (densityCounterD4Gamma eps) (densityCounterD4Refresh eps)
      (densityCounter_D4_refresh_admissible eps))
    (onlineExpectationRealization densityCounterProblem)
    densityCounterInitialPoint
    (onlinePLBatchScheduleFromBase_admissible densityCounterCount
      densityCounterCount 1 densityCounterMu densityCounterD4BaseBatch eps)
  let law := onlineProofExactPathLaw
    (b := densityCounterD4Batch eps) (b0 := densityCounterCount)
    (A := onlineDataWithParameters densityCounterData
      (densityCounterD4Gamma eps) (densityCounterD4Refresh eps)
      (densityCounter_D4_refresh_admissible eps))
  letI (w : Worker densityCounterCount) :
      IsProbabilityMeasure (densityCounterProblem.sampleLaw w) :=
    densityCounterProblem.sampleLaw_isProbability w
  letI : IsProbabilityMeasure
      (onlineBatchLaw densityCounterProblem (densityCounterD4Batch eps)) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure
      (onlineBatchLaw densityCounterProblem densityCounterCount) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure onlineGeneratedIdentityQuantizer.law :=
    onlineGeneratedIdentityQuantizer.law_isProbability
  letI : IsProbabilityMeasure
      (workerCompressionLaw (n := densityCounterCount)
        onlineGeneratedIdentityQuantizer) := by
    unfold workerCompressionLaw
    infer_instance
  letI : IsProbabilityMeasure
      (refreshLaw (densityCounterD4Refresh eps)
        (densityCounter_D4_refresh_admissible eps)) := by
    unfold refreshLaw
    infer_instance
  letI : IsProbabilityMeasure
      (onlineRoundLaw (b := densityCounterD4Batch eps)
        (b0 := densityCounterCount)
        (onlineDataWithParameters densityCounterData
          (densityCounterD4Gamma eps) (densityCounterD4Refresh eps)
          (densityCounter_D4_refresh_admissible eps))) := by
    unfold onlineRoundLaw
    simp only [onlineDataWithParameters, densityCounterData]
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold onlineProofExactPathLaw
    infer_instance
  have hg1 : (densityCounterD4Gamma eps : ℝ) ≤ 1 := by
    exact hgamma.trans (by
      have : 1 ≤ x ^ 6 := one_le_pow₀ (by linarith : 1 ≤ x)
      exact (div_le_one (pow_pos hxpos 6)).2 this)
  have hbern : 1 - ((K eps).1 : ℝ) * (densityCounterD4Gamma eps : ℝ) ≤
      (1 - (densityCounterD4Gamma eps : ℝ)) ^ (K eps).1 := by
    simpa [sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (a := -(densityCounterD4Gamma eps : ℝ))
        (by linarith : (-2 : ℝ) ≤ -(densityCounterD4Gamma eps : ℝ))
        (K eps).1)
  have hpow : 3 / 4 < (1 - (densityCounterD4Gamma eps : ℝ)) ^ (K eps).1 := by
    linarith
  have hIntegral : (∫ path, globalObjective
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run (K eps).1 path).x -
      globalObjective
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        densityCounterZeroPoint ∂law) =
      ((1 - (densityCounterD4Gamma eps : ℝ)) ^ (K eps).1) ^ 2 / 2 := by
    have hfun : (fun path => globalObjective
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run (K eps).1 path).x -
      globalObjective
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        densityCounterZeroPoint) =
      (fun _ => ((1 - (densityCounterD4Gamma eps : ℝ)) ^ (K eps).1) ^ 2 / 2) := by
      funext path
      dsimp [run]
      rw [densityCounter_process_state, densityCounter_globalObjective,
        densityCounter_globalObjective]
      simp only [densityCounterZeroPoint, norm_zero, zero_pow, zero_div, sub_zero,
        norm_smul, mul_one, Real.norm_eq_abs]
      rw [densityCounter_initial_norm, mul_one]
      rw [sq_abs]
      norm_num
    calc
      _ = ∫ _path,
          ((1 - (densityCounterD4Gamma eps : ℝ)) ^ (K eps).1) ^ 2 / 2 ∂law :=
        integral_congr_ae (Filter.Eventually.of_forall fun path => congrFun hfun path)
      _ = _ := by rw [integral_const, probReal_univ]; norm_num
  have hAcc : (∫ path, globalObjective
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        (run (K eps).1 path).x -
      globalObjective
        (onlineLocalProblemCorrected
          ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
        densityCounterZeroPoint ∂law) ≤ (eps : ℝ) := by
    simpa [run, law, densityCounterD4Batch] using (hAccuracy eps).2
  rw [hIntegral] at hAcc
  have hepsLe : (eps : ℝ) ≤ 1 / 4 := by
    dsimp [eps]
    exact (div_le_iff₀ hxpos).2 (by nlinarith)
  nlinarith [sq_nonneg ((1 - (densityCounterD4Gamma eps : ℝ)) ^ (K eps).1)]

/-! The following two propositions spell out, at the concrete countermodel,
every premise of the former supplied-stepsize D.3 and D.4 interfaces.  They
deliberately do not contain the later canonical-stepsize equality guards. -/

private def densityCounterD3FormerPremises : Prop :=
    (∀ eps, RefreshProbabilityAdmissible (densityCounterD3Refresh eps)) ∧
    HasUniformLowerBound
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) 0 ∧
    IsLocallySmooth
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
      (fun _ : Worker densityCounterCount => 1) ∧
    OnlineUnbiasedBoundedVarianceCorrected
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
      (fun _ : Worker densityCounterCount => 1) ∧
    IsUnbiasedQuantizer onlineGeneratedIdentityQuantizer 1 ∧
    (∀ eps, OnlineAverageSmoothnessCorrected (b0 := densityCounterCount)
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
      (onlineCorrectedProofExactProcess
        (A := onlineDataWithParameters densityCounterData
          (densityCounterD3Gamma eps) (densityCounterD3Refresh eps)
          (densityCounter_D3_refresh_admissible eps))
        (onlineExpectationRealization densityCounterProblem)
        densityCounterInitialPoint
        (onlineNonconvexBatchScheduleFromBase_admissible
          densityCounterCount densityCounterCount 1 densityCounterD3BaseBatch eps))
      (fun _ : Worker densityCounterCount => 0)) ∧
    AccuracyTheta (fun eps => ((densityCounterD3BaseBatch eps).1 : ℝ))
      (fun eps => varianceAggregateSq
        (fun _ : Worker densityCounterCount => (1 : ℝ)) /
          (densityCounterCount.1 * (eps : ℝ) ^ 2)) ∧
    (∀ eps, OnlineVRStepsizeCondition (densityCounterD3Gamma eps)
      (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
      (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
      (densityCounterD3Refresh eps) 1 densityCounterCount densityCounterCount) ∧
    (∀ eps, densityCounterD3Refresh eps = onlineDensityBatchRefreshSchedule
      (expectedDensity onlineGeneratedIdentityQuantizer) densityCounterCount
      (onlineNonconvexBatchScheduleFromBase densityCounterCount densityCounterCount
        (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
        densityCounterD3BaseBatch eps)
      densityCounterCount)

private def densityCounterD4FormerPremises : Prop :=
    (∀ eps, RefreshProbabilityAdmissible (densityCounterD4Refresh eps)) ∧
    HasUniformLowerBound
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩) 0 ∧
    IsLocallySmooth
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
      (fun _ : Worker densityCounterCount => 1) ∧
    OnlineUnbiasedBoundedVarianceCorrected
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
      (fun _ : Worker densityCounterCount => 1) ∧
    SatisfiesPL
      (onlineLocalProblemCorrected
        ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩)
      densityCounterMu densityCounterZeroPoint ∧
    IsUnbiasedQuantizer onlineGeneratedIdentityQuantizer 1 ∧
    (∀ eps, OnlineAverageSmoothnessCorrected (b0 := densityCounterCount)
      ⟨densityCounterProblem, onlineExpectationRealization densityCounterProblem⟩
      (onlineCorrectedProofExactProcess
        (A := onlineDataWithParameters densityCounterData
          (densityCounterD4Gamma eps) (densityCounterD4Refresh eps)
          (densityCounter_D4_refresh_admissible eps))
        (onlineExpectationRealization densityCounterProblem)
        densityCounterInitialPoint
        (onlinePLBatchScheduleFromBase_admissible densityCounterCount
          densityCounterCount 1 densityCounterMu densityCounterD4BaseBatch eps))
      (fun _ : Worker densityCounterCount => 0)) ∧
    AccuracyTheta (fun eps => ((densityCounterD4BaseBatch eps).1 : ℝ))
      (fun eps => varianceAggregateSq
        (fun _ : Worker densityCounterCount => (1 : ℝ)) /
          (densityCounterCount.1 * densityCounterMu * (eps : ℝ))) ∧
    (∀ eps, OnlineVRPLStepsizeCondition (densityCounterD4Gamma eps)
      (rootMeanSquare (fun _ : Worker densityCounterCount => (1 : ℝ)))
      (rootMeanSquare (fun _ : Worker densityCounterCount => (0 : ℝ)))
      (densityCounterD4Refresh eps) 1 densityCounterMu
      densityCounterCount densityCounterCount) ∧
    (∀ eps, densityCounterD4Refresh eps = onlineDensityBatchRefreshSchedule
      (expectedDensity onlineGeneratedIdentityQuantizer) densityCounterCount
      (onlinePLBatchScheduleFromBase densityCounterCount densityCounterCount
        (varianceAggregateSq (fun _ : Worker densityCounterCount => (1 : ℝ)))
        densityCounterMu densityCounterD4BaseBatch eps)
      densityCounterCount)

private theorem densityCounter_D3_all_former_premises :
    densityCounterD3FormerPremises := by
  unfold densityCounterD3FormerPremises
  refine ⟨densityCounter_D3_refresh_admissible, densityCounter_lowerBound,
    densityCounter_smooth, densityCounter_variance,
    onlineGeneratedIdentityQuantizer_unbiased, ?_, ?_, densityCounter_D3_step, ?_⟩
  · intro eps
    exact densityCounter_averageSmoothness _
  · convert densityCounter_D3_base_theta using 1
    funext eps
    rw [densityCounter_varianceAggregateSq_one]
    norm_num [densityCounterCount]
  · intro eps
    rw [densityCounter_varianceAggregateSq_one]
    rfl

private theorem densityCounter_D4_all_former_premises :
    densityCounterD4FormerPremises := by
  unfold densityCounterD4FormerPremises
  refine ⟨densityCounter_D4_refresh_admissible, densityCounter_lowerBound,
    densityCounter_smooth, densityCounter_variance, densityCounter_PL,
    onlineGeneratedIdentityQuantizer_unbiased, ?_, ?_, densityCounter_D4_step, ?_⟩
  · intro eps
    exact densityCounter_averageSmoothness _
  · convert densityCounter_D4_base_theta using 1
    funext eps
    rw [densityCounter_varianceAggregateSq_one]
    norm_num [densityCounterCount, densityCounterMu]
    ring
  · intro eps
    rw [densityCounter_varianceAggregateSq_one]
    rfl

/-- Complete same-interface refutation of the former supplied-step D.3
density claim: every original premise holds, but its full existential
`ThreeEndpointComplexity` conclusion does not. -/
private theorem densityCounter_D3_supplied_stepsize_endpoint_false :
    densityCounterD3FormerPremises ∧ ¬ densityCounterD3FormerEndpoint :=
  ⟨densityCounter_D3_all_former_premises,
    densityCounter_D3_supplied_stepsize_conclusion_false⟩

/-- Complete same-interface refutation of the former supplied-step D.4
density claim: every original premise holds, but its full existential
`ThreeEndpointComplexity` conclusion does not. -/
private theorem densityCounter_D4_supplied_stepsize_endpoint_false :
    densityCounterD4FormerPremises ∧ ¬ densityCounterD4FormerEndpoint :=
  ⟨densityCounter_D4_all_former_premises,
    densityCounter_D4_supplied_stepsize_conclusion_false⟩

/-- The printed supplied-stepsize interfaces of Corollaries D.3 and D.4 are
jointly refuted by the generated scalar quadratic MARINA process.  Unfolding
the four private propositions exposes every former premise and the negations
of the two full existential `ThreeEndpointComplexity` conclusions. -/
theorem corollary_D3_D4_density_source_statement_counterexample :
    (densityCounterD3FormerPremises ∧ ¬ densityCounterD3FormerEndpoint) ∧
      (densityCounterD4FormerPremises ∧ ¬ densityCounterD4FormerEndpoint) :=
  ⟨densityCounter_D3_supplied_stepsize_endpoint_false,
    densityCounter_D4_supplied_stepsize_endpoint_false⟩


end MARINA
