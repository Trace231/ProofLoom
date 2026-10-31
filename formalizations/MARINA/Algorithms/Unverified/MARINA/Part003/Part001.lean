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

/-!
# MARINA family: source-facing object model

This file models Algorithms 1--4 of Gorbunov--Burlachenko--Li--Richtárik.
The estimator and iterate processes below are generated definitions, rather
than witness processes constrained by theorem hypotheses.
-/

open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace MARINA

/-- Corrected B-track realization of `book/MARINA/MARINA.json#/key_lemmas/7`,
Eq. (46).  It has the same estimator recurrence, but every objective and
gradient target is formed through the explicitly nonfallback Eq. (6)
realization rather than Mathlib's totalized integral fallback. -/
theorem online_estimator_recurrence_46_corrected_BTrack
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    let run := onlineCorrectedProofExactProcess A hE x0 hBatch
    let law := onlineProofExactPathLaw (A := A)
    EstimatorErrorMomentWellDefined P run law (k + 1) ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment P run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
        A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
  let run := onlineCorrectedProofExactProcess A hE x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  have hL2k := online_corrected_process_l2_invariant
    A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k
  have hL2succ := online_corrected_process_l2_invariant
    A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth (k + 1)
  have hRegularities (i : Worker n) :=
    onlineEq46_all_exactLaw_regularities A hE x0 hBatch σ hVariance k i
  have hRefresh := online_corrected_refresh_average_second_moment
    A hE x0 Llocal σ hSmooth hVariance hBatch k hRegularities
  have hNonrefresh := online_corrected_nonrefresh_branch_moments
    A hE x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k hL2k.2.2.1 hL2k.2.2.2
  let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    average (fun i : Worker n =>
      onlineCorrectedFixedWorkerInnovation (b0 := b0) A hE
        (run (k + 1) path).x (run k path).x i
        ((path k).2.1.2, (path k).2.2))
  let refreshError := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    average (fun i : Worker n => average (fun j : Fin b.1 =>
      stochasticGradient A.problem i ((path k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => (path k).1
  let refreshSq := fun path => ‖refreshError path‖ ^ 2
  let nonrefreshSq := fun path => ‖residual path + innovation path‖ ^ 2
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n =>
      A.quantizer.apply
        (onlineBatchDifference A.problem (path k).2.1.2 i xN s.x)
        ((path k).2.2 i)
    have hdiffAvg : average (fun i : Worker n =>
        localGradientDifference P i xN s.x) =
        globalGradient P xN - globalGradient P s.x := by
      rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
        globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : innovation path =
        average q - average (fun i : Worker n =>
          localGradientDifference P i xN s.x) := by
      dsimp [innovation, onlineCorrectedFixedWorkerInnovation, q, xN, s]
      rw [show (run (k + 1) path).x = xN by rfl]
      unfold average SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n =>
          onlineWorkerEstimator A (onlineDriverOfRoundNoise (path k)) s i) -
          globalGradient P xN := by rfl
    cases h : branch path with
    | false =>
        simp only [h, Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        change average (fun i : Worker n => s.g + q i) -
            globalGradient P xN = residual path + innovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [h, if_true]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
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
  have hbranchMeas : Measurable branch := by dsimp [branch]; fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    calc
      Measure.map branch law = Measure.map Prod.fst
          (Measure.map (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k) law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact measurable_fst
            · exact measurable_pi_apply k
      _ = Measure.map Prod.fst (onlineRoundLaw A) := by
            rw [show Measure.map
                (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ => path k) law =
                onlineRoundLaw A by
              simpa [law, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = _ := by simp [onlineRoundLaw]
  have htrueMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real ({true} : Set Bool) =
        A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
    simp [PMF.bernoulli_apply]
  have hfalseMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real ({false} : Set Bool) =
        1 - A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
    simp only [PMF.bernoulli_apply, Bool.cond_false]
    let pNN : NNReal :=
      ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
    have hpNN : pNN ≤ (1 : NNReal) := by exact_mod_cast A.refresh_admissible.2
    change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
    rw [NNReal.coe_sub hpNN]
    rfl
  let phiR : ℝ → Bool → ℝ := fun z c => if c then z else 0
  let budgetR : ℝ → ℝ := fun z => A.refreshProbability * z
  let phiN : ℝ → Bool → ℝ := fun z c => if c = false then z else 0
  let budgetN : ℝ → ℝ := fun z => (1 - A.refreshProbability) * z
  have hrefreshInt : Integrable refreshSq law := by
    simpa [refreshSq, refreshError, P, run, law] using hRefresh.1
  have hnonrefreshInt : Integrable nonrefreshSq law := by
    simpa [nonrefreshSq, residual, innovation, P, run, law] using
      hNonrefresh.2.2.2.1
  have hrefreshIndep : ProbabilityTheory.IndepFun refreshSq branch law := by
    simpa [refreshSq, refreshError, branch, P, run, law] using hRefresh.2.2
  have hnonrefreshIndep : ProbabilityTheory.IndepFun nonrefreshSq branch law := by
    simpa [nonrefreshSq, residual, innovation, branch, P, run, law] using
      hNonrefresh.2.2.2.2.2
  have hgateRInt : Integrable (fun path => phiR (refreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = true} :=
      hbranchMeas (measurableSet_singleton true)
    have hp := Integrable.piecewise hs hrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiR, Set.piecewise] using hp
  have hgateNInt : Integrable (fun path => phiN (nonrefreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranchMeas (measurableSet_singleton false)
    have hp := Integrable.piecewise hs hnonrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiN, Set.piecewise] using hp
  have hbudgetRInt : Integrable (fun path => budgetR (refreshSq path)) law := by
    simpa [budgetR] using hrefreshInt.const_mul A.refreshProbability
  have hbudgetNInt : Integrable (fun path => budgetN (nonrefreshSq path)) law := by
    simpa [budgetN] using hnonrefreshInt.const_mul (1 - A.refreshProbability)
  have hgateR := integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
    (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
    (X := refreshSq) (Y := branch) (φ := phiR) (B := budgetR)
    (by exact (show Measurable (Function.uncurry phiR) by
      dsimp [phiR, Function.uncurry]
      apply Measurable.ite
      · exact measurable_snd (measurableSet_singleton true)
      · exact measurable_fst
      · exact measurable_const).aestronglyMeasurable)
    (by exact (show Measurable budgetR by dsimp [budgetR]; fun_prop).aestronglyMeasurable)
    hrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
    hrefreshIndep hbranchLaw hgateRInt hbudgetRInt
    (fun z => by
      rw [MeasureTheory.integral_fintype]
      · simp [Fintype.sum_bool, phiR, budgetR, htrueMass]
      · exact Integrable.of_finite)
  have hgateN := integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
    (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
    (X := nonrefreshSq) (Y := branch) (φ := phiN) (B := budgetN)
    (by exact (show Measurable (Function.uncurry phiN) by
      dsimp [phiN, Function.uncurry]
      apply Measurable.ite
      · exact measurable_snd (measurableSet_singleton false)
      · exact measurable_fst
      · exact measurable_const).aestronglyMeasurable)
    (by exact (show Measurable budgetN by dsimp [budgetN]; fun_prop).aestronglyMeasurable)
    hnonrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
    hnonrefreshIndep hbranchLaw hgateNInt hbudgetNInt
    (fun z => by
      rw [MeasureTheory.integral_fintype]
      · simp [Fintype.sum_bool, phiN, budgetN, hfalseMass]
      · exact Integrable.of_finite)
  have hnextEq : estimatorErrorMoment P run law (k + 1) =
      (∫ path, phiR (refreshSq path) (branch path) ∂law) +
        ∫ path, phiN (nonrefreshSq path) (branch path) ∂law := by
    unfold estimatorErrorMoment
    calc
      (∫ path, ‖(run (k + 1) path).g - globalGradient P (run (k + 1) path).x‖ ^ 2 ∂law) =
          ∫ path, (phiR (refreshSq path) (branch path) +
            phiN (nonrefreshSq path) (branch path)) ∂law := by
              apply integral_congr_ae
              filter_upwards [] with path
              rw [show (run (k + 1) path).g - globalGradient P (run (k + 1) path).x =
                nextResidual path by rfl, hdecomp]
              cases hb : branch path <;> simp [hb, phiR, phiN, refreshSq, nonrefreshSq]
      _ = _ := integral_add hgateRInt hgateNInt
  refine ⟨hL2succ.2.2.1, hL2k.2.2.1, hL2k.2.2.2, ?_⟩
  rw [hnextEq]
  calc
    (∫ path, phiR (refreshSq path) (branch path) ∂law) +
          ∫ path, phiN (nonrefreshSq path) (branch path) ∂law ≤
        (∫ path, budgetR (refreshSq path) ∂law) +
          ∫ path, budgetN (nonrefreshSq path) ∂law := add_le_add hgateR hgateN
    _ = A.refreshProbability * (∫ path, refreshSq path ∂law) +
        (1 - A.refreshProbability) * (∫ path, nonrefreshSq path ∂law) := by
          simp [budgetR, budgetN, integral_const_mul]
    _ ≤ A.refreshProbability * (varianceAggregateSq σ / (n.1 * b.1)) +
        (1 - A.refreshProbability) *
          (estimatorErrorMoment P run law k +
            (1 / (n.1 : ℝ)) *
              (ω * (rootMeanSquare Llocal) ^ 2 +
                (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
              stepMoment run law k) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left
        · simpa [refreshSq, refreshError, P, run, law] using hRefresh.2.1
        · exact le_of_lt A.refresh_admissible.1
      · apply mul_le_mul_of_nonneg_left
        · simpa [nonrefreshSq, residual, innovation, P, run, law] using
            hNonrefresh.2.2.2.2.1
        · exact sub_nonneg.mpr A.refresh_admissible.2
    _ = (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
        A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
      ring

/-- `book/MARINA/MARINA.json#/key_lemmas/7`, Eq. (46), at the proof-exact
source boundary used by Theorems D.3 and D.4.  This boundary consumes the
direct scalar/component-L² proof over `onlineProofExactProcess` and
`onlineProofExactPathLaw`; it does not route through the corrected/full-State
B-track realization. -/
theorem online_estimator_recurrence_46_proof_exact_literal_source_boundary
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law (k + 1) ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment P run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
      stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
        A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  rcases onlineProofExactProcess_scalar_recurrence_components
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k with
    ⟨_hxk, _hresidualk, _hxL2k, _hgL2k, hErrorK, hStepK, _hHistoryK⟩
  rcases onlineProofExactProcess_scalar_recurrence_components
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth (k + 1) with
    ⟨_hxNext, _hresidualNext, _hxL2Next, _hgL2Next, hErrorNext,
      _hStepNext, hHistoryNext⟩
  exact ⟨hErrorNext, hErrorK, hStepK,
    hHistoryNext k (Nat.lt_succ_self k)⟩

/-- Eq. (40) makes the displacement coefficient in the online VR-MARINA
Lyapunov step nonnegative.  This is the scalar square-root calculation used
immediately after combining Lemma B.1 with Eq. (46). -/
theorem online_vr_stepsize_absorbs_displacement
    {n b0 : Count} {γ L ℒ p ω : ℝ}
    (hγ : 0 < γ) (hp : RefreshProbabilityAdmissible p)
    (hω : 0 ≤ ω) (hL : 0 ≤ L) (hℒ : 0 ≤ ℒ)
    (hStep : OnlineVRStepsizeCondition γ L ℒ p ω n b0) :
    0 ≤ 1 / (2 * γ) - L / 2 -
      γ / (2 * p) * ((1 - p) / n.1 *
        (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)) := by
  let q : ℝ := ((1 - p) / (p * n.1)) *
    (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)
  have hp_pos : 0 < p := hp.1
  have hn_pos : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hb0_pos : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
    have h1ω : 0 ≤ 1 + ω := by linarith
    exact mul_nonneg
      (div_nonneg h1mp (mul_nonneg hp_pos.le hn_pos.le))
      (add_nonneg (mul_nonneg hω (sq_nonneg L))
        (div_nonneg (mul_nonneg h1ω (sq_nonneg ℒ)) hb0_pos.le))
  have hs_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hstep' : γ * (L + Real.sqrt q) ≤ 1 := by
    simpa [OnlineVRStepsizeCondition, FiniteSumVRStepsizeCondition, q,
      mul_assoc] using hStep
  have hγs_le_one : γ * Real.sqrt q ≤ 1 := by
    nlinarith
  have hγs_nonneg : 0 ≤ γ * Real.sqrt q :=
    mul_nonneg hγ.le hs_nonneg
  have hγs_budget :
      0 ≤ (γ * Real.sqrt q) * (1 - γ * Real.sqrt q) :=
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
      γ / (2 * p) * ((1 - p) / n.1 *
          (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)) = γ * q / 2 := by
    dsimp [q]
    field_simp [hp_ne, hn_ne]
  rw [hq_eq]
  have hscaled := mul_nonneg (show 0 ≤ (2 * γ)⁻¹ by positivity) hcore
  convert hscaled using 1 <;> field_simp [hγ_ne] <;> ring

/-- Scalar form of the online VR-MARINA one-step Lyapunov calculation.  The
two premises are respectively the integrated Lemma B.1 inequality and Eq. (46);
the coefficient premise is discharged from Eq. (40) by
`online_vr_stepsize_absorbs_displacement`. -/
theorem online_vr_nonconvex_lyapunov_step
    (F E G D : ℕ → ℝ) {γ p L a V : ℝ} (k : ℕ)
    (hγ : 0 < γ) (hp : 0 < p) (hD : 0 ≤ D k)
    (hcoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a)
    (hdescent :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k)
    (hrecurrence :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V) :
    F (k + 1) + γ / (2 * p) * E (k + 1) ≤
      F k + γ / (2 * p) * E k - γ / 2 * G k + γ / 2 * V := by
  have hweight : 0 ≤ γ / (2 * p) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hrecurrence hweight
  have hp_ne : p ≠ 0 := ne_of_gt hp
  calc
    F (k + 1) + γ / (2 * p) * E (k + 1) ≤
        (F k - γ / 2 * G k -
            (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k) +
          γ / (2 * p) * E (k + 1) := add_le_add hdescent (le_refl _)
    _ ≤ (F k - γ / 2 * G k -
            (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k) +
          γ / (2 * p) * (a * D k + (1 - p) * E k + p * V) :=
      add_le_add (le_refl _) hscaled
    _ ≤ F k + γ / (2 * p) * E k - γ / 2 * G k + γ / 2 * V := by
      field_simp [hp_ne] at hcoeff ⊢
      nlinarith

/-- Eq. (48) supplies exactly the three scalar facts used by the online
PŁ Lyapunov argument: displacement absorption at weight `γ / p`, absorption
of the old estimator error, and nonnegativity of the contraction factor. -/
theorem online_vr_pl_stepsize_coefficients
    {n b0 : Count} {γ L ℒ p ω : ℝ} {μ : PositivePLParameter}
    (hγ : 0 < γ) (hp : RefreshProbabilityAdmissible p)
    (hω : 0 ≤ ω) (hL : 0 ≤ L) (hℒ : 0 ≤ ℒ)
    (hStep : OnlineVRPLStepsizeCondition γ L ℒ p ω μ n b0) :
    0 ≤ 1 / (2 * γ) - L / 2 -
        γ / p * ((1 - p) / n.1 *
          (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)) ∧
      γ / 2 + γ / p * (1 - p) ≤ (1 - γ * μ) * (γ / p) ∧
      0 ≤ 1 - γ * μ := by
  let q : ℝ := (2 * (1 - p) / (p * n.1)) *
    (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)
  have hp_pos : 0 < p := hp.1
  have hp_one : p ≤ 1 := hp.2
  have hn_pos : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hb0_pos : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp_one
    have h1ω : 0 ≤ 1 + ω := by linarith
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) h1mp)
        (mul_nonneg hp_pos.le hn_pos.le))
      (add_nonneg (mul_nonneg hω (sq_nonneg L))
        (div_nonneg (mul_nonneg h1ω (sq_nonneg ℒ)) hb0_pos.le))
  have hs_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hstep_sqrt : γ * (L + Real.sqrt q) ≤ 1 := by
    simpa [OnlineVRPLStepsizeCondition, FiniteSumVRPLStepsizeCondition, q]
      using hStep.1
  have hγs_le_one : γ * Real.sqrt q ≤ 1 := by
    nlinarith
  have hγs_nonneg : 0 ≤ γ * Real.sqrt q :=
    mul_nonneg hγ.le hs_nonneg
  have hγs_budget :
      0 ≤ (γ * Real.sqrt q) * (1 - γ * Real.sqrt q) :=
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
      γ / p * ((1 - p) / n.1 *
          (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)) = γ * q / 2 := by
    dsimp [q]
    field_simp [hp_ne, hn_ne]
    <;> ring
  have hdisplacement : 0 ≤ 1 / (2 * γ) - L / 2 -
      γ / p * ((1 - p) / n.1 *
        (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)) := by
    rw [hq_eq]
    have hscaled := mul_nonneg (show 0 ≤ (2 * γ)⁻¹ by positivity) hcore
    convert hscaled using 1 <;> field_simp [hγ_ne] <;> ring
  have hmu : 2 * γ * (μ : ℝ) ≤ p := by
    simpa [OnlineVRPLStepsizeCondition, FiniteSumVRPLStepsizeCondition]
      using hStep.2
  have herror :
      γ / 2 + γ / p * (1 - p) ≤ (1 - γ * μ) * (γ / p) := by
    field_simp [hp_ne]
    nlinarith
  have hcontraction : 0 ≤ 1 - γ * μ := by
    nlinarith
  exact ⟨hdisplacement, herror, hcontraction⟩

/-- The process-free scalar core of the online PŁ proof.  Contracted objective
descent and Eq. (46), weighted by `γ / p`, give the affine Lyapunov step once
the two Eq. (48) coefficient inequalities are available. -/
theorem online_vr_pl_lyapunov_step
    (H E D : ℕ → ℝ) {γ p μ a V c : ℝ} (k : ℕ)
    (hγ : 0 < γ) (hp : 0 < p) (hD : 0 ≤ D k) (hE : 0 ≤ E k)
    (hcoeff : 0 ≤ c - γ / p * a)
    (herror : γ / 2 + γ / p * (1 - p) ≤
      (1 - γ * μ) * (γ / p))
    (hdescent :
      H (k + 1) ≤ (1 - γ * μ) * H k -
        c * D k + γ / 2 * E k)
    (hrecurrence :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V) :
    H (k + 1) + γ / p * E (k + 1) ≤
      (1 - γ * μ) * (H k + γ / p * E k) + γ * V := by
  have hweight : 0 ≤ γ / p := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hrecurrence hweight
  have hdisp :
      -c * D k + γ / p * (a * D k) ≤ 0 := by
    nlinarith [mul_nonneg hcoeff hD]
  have herror_scaled :
      (γ / 2 + γ / p * (1 - p)) * E k ≤
        ((1 - γ * μ) * (γ / p)) * E k :=
    mul_le_mul_of_nonneg_right herror hE
  have hp_ne : p ≠ 0 := ne_of_gt hp
  calc
    H (k + 1) + γ / p * E (k + 1) ≤
        ((1 - γ * μ) * H k - c * D k +
            γ / 2 * E k) + γ / p * E (k + 1) :=
      add_le_add hdescent (le_refl _)
    _ ≤ ((1 - γ * μ) * H k - c * D k +
            γ / 2 * E k) +
          γ / p * (a * D k + (1 - p) * E k + p * V) :=
      add_le_add (le_refl _) hscaled
    _ ≤ (1 - γ * μ) * (H k + γ / p * E k) + γ * V := by
      field_simp [hp_ne] at hdisp herror_scaled ⊢
      nlinarith

/-- An affine contraction with additive term `γ V` has noise floor `V / μ`
when its contraction factor is `1 - γ μ`.  The shifted potential reduces
the claim to the general SOptLib backward-contraction theorem. -/
theorem affine_contraction_le_noise_floor
    (Φ : ℕ → ℝ) {γ μ V : ℝ} (K : ℕ)
    (hμ : 0 < μ) (hV : 0 ≤ V) (hρ : 0 ≤ 1 - γ * μ)
    (hstep : ∀ k, Φ (k + 1) ≤ (1 - γ * μ) * Φ k + γ * V) :
    Φ K ≤ (1 - γ * μ) ^ K * Φ 0 + V / μ := by
  let Ψ : ℕ → ℝ := fun k => Φ k - V / μ
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ
  have hnoise :
      γ * V = (1 - (1 - γ * μ)) * (V / μ) := by
    field_simp [hμ_ne]
    ring
  have hshift (k : ℕ) :
      Ψ (k + 1) ≤ (1 - γ * μ) * Ψ k := by
    dsimp [Ψ]
    calc
      Φ (k + 1) - V / μ ≤
          ((1 - γ * μ) * Φ k + γ * V) - V / μ :=
        sub_le_sub_right (hstep k) _
      _ = (1 - γ * μ) * (Φ k - V / μ) := by
        rw [hnoise]
        ring
  have hiter : Ψ K ≤ (1 - γ * μ) ^ K * Ψ 0 := by
    have h := SOptLib.le_pow_mul_of_backward_contraction_on_Ioc
      Ψ (1 - γ * μ) 0 K (Nat.zero_le K) hρ
      (fun r hr0 _hrK => by
        have hr : r - 1 + 1 = r := by omega
        simpa [hr] using hshift (r - 1))
    simpa using h
  have hfloor : 0 ≤ V / μ := div_nonneg hV hμ.le
  have hpow : 0 ≤ (1 - γ * μ) ^ K := pow_nonneg hρ K
  dsimp [Ψ] at hiter
  nlinarith [mul_nonneg hpow hfloor]

/-- `book/MARINA/MARINA.json#/key_lemmas/8`, Eq. (59). -/
theorem pp_fixed_sampled_compressed_innovation_moments
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (xNext x : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let delta := globalGradient A.problem xNext - globalGradient A.problem x
    let innovation := fun q : Worker n × Ξ =>
      A.quantizer.apply
          (localGradientDifference A.problem q.1 xNext x) q.2 - delta
    Integrable innovation ((workerLaw n).prod A.quantizer.law) ∧
      Integrable (fun q => ‖innovation q‖ ^ 2)
        ((workerLaw n).prod A.quantizer.law) ∧
      (∫ q, innovation q ∂(workerLaw n).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(workerLaw n).prod A.quantizer.law) ≤
        (1 + ω) * (rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2 := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  let v := fun i : Worker n =>
    localGradientDifference A.problem i xNext x
  let delta := globalGradient A.problem xNext - globalGradient A.problem x
  let innovation := fun q : Worker n × Ξ =>
    A.quantizer.apply (v q.1) q.2 - delta
  change Integrable innovation ((workerLaw n).prod A.quantizer.law) ∧
      Integrable (fun q => ‖innovation q‖ ^ 2)
        ((workerLaw n).prod A.quantizer.law) ∧
      (∫ q, innovation q ∂(workerLaw n).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(workerLaw n).prod A.quantizer.law) ≤
        (1 + ω) * (rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2
  have hv_meas : Measurable v := measurable_of_finite v
  have hinnovation_meas : Measurable innovation := by
    have hquantized : Measurable (fun q : Worker n × Ξ =>
        A.quantizer.apply (v q.1) q.2) :=
      A.quantizer.measurable_apply_uncurry.comp
        ((hv_meas.comp measurable_fst).prodMk measurable_snd)
    exact hquantized.sub measurable_const
  have hdelta : average v = delta := by
    dsimp [v, delta]
    rw [globalGradient_eq_averageLocalGradient A.problem hSmooth.1 xNext,
      globalGradient_eq_averageLocalGradient A.problem hSmooth.1 x]
    unfold averageLocalGradient localGradientDifference average
      SOptLib.finiteUniformAverage
    rw [Finset.sum_sub_distrib, smul_sub]
  have hworker_mass (i : Worker n) :
      (workerLaw n).real ({i} : Set (Worker n)) = (n.1 : ℝ)⁻¹ := by
    rw [measureReal_def]
    unfold workerLaw
    rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i)]
    simp [PMF.uniformOfFintype_apply, Fintype.card_fin,
      ENNReal.toReal_inv]
  have hworker_integral_vec (f : Worker n → Point d) :
      (∫ i, f i ∂workerLaw n) = average f := by
    rw [MeasureTheory.integral_fintype .of_finite]
    unfold average SOptLib.finiteUniformAverage
    simp only [hworker_mass, Fintype.card_fin]
    rw [Finset.smul_sum]
  have hworker_integral_real (f : Worker n → ℝ) :
      (∫ i, f i ∂workerLaw n) = average f := by
    rw [MeasureTheory.integral_fintype .of_finite]
    unfold average SOptLib.finiteUniformAverage
    simp only [hworker_mass, Fintype.card_fin, smul_eq_mul]
    rw [Finset.mul_sum]
  have hfiber_sq : ∀ i,
      Integrable (fun ξ => ‖innovation (i, ξ)‖ ^ 2) A.quantizer.law := by
    intro i
    have hnoise_sq := quantizer_error_sq_integrable hQuantizer (v i)
    have hnoise_meas : AEStronglyMeasurable
        (fun ξ => A.quantizer.apply (v i) ξ - v i) A.quantizer.law :=
      ((hQuantizer.2 (v i)).1.sub (integrable_const (c := v i))).aestronglyMeasurable
    have hconst_sq : Integrable
        (fun _ : Ξ => ‖v i - delta‖ ^ 2) A.quantizer.law :=
      integrable_const (c := ‖v i - delta‖ ^ 2)
    convert integrable_sq_norm_add hnoise_meas aestronglyMeasurable_const
      hnoise_sq hconst_sq using 1
    funext ξ
    congr 2
    dsimp [innovation]
    abel
  have hfiber_mean : ∀ i,
      (∫ ξ, innovation (i, ξ) ∂A.quantizer.law) = v i - delta := by
    intro i
    rw [integral_sub (hQuantizer.2 (v i)).1 (integrable_const (c := delta))]
    rw [(hQuantizer.2 (v i)).2.2.1]
    simp [innovation, integral_const, probReal_univ]
  have hfiber_sq_eq : ∀ i,
      (∫ ξ, ‖innovation (i, ξ)‖ ^ 2 ∂A.quantizer.law) =
        (∫ ξ, ‖A.quantizer.apply (v i) ξ - v i‖ ^ 2
          ∂A.quantizer.law) + ‖v i - delta‖ ^ 2 := by
    intro i
    let G := fun ξ => A.quantizer.apply (v i) ξ - delta
    have hG_int : Integrable G A.quantizer.law :=
      (hQuantizer.2 (v i)).1.sub (integrable_const (c := delta))
    have hcenter_sq : Integrable
        (fun ξ => ‖G ξ - (v i - delta)‖ ^ 2) A.quantizer.law := by
      convert (hQuantizer.2 (v i)).2.1 using 1
      funext ξ
      congr 2
      dsimp [G]
      abel
    have hG_mean : (∫ ξ, G ξ ∂A.quantizer.law) = v i - delta := by
      rw [integral_sub (hQuantizer.2 (v i)).1
        (integrable_const (c := delta)), (hQuantizer.2 (v i)).2.2.1]
      simp [integral_const, probReal_univ]
    have hdecomp :=
      integral_norm_sq_eq_integral_norm_sq_sub_mean_add_norm_sq_of_integral_eq
        A.quantizer.law G (v i - delta) hG_int hcenter_sq hG_mean
    calc
      (∫ ξ, ‖innovation (i, ξ)‖ ^ 2 ∂A.quantizer.law) =
          ∫ ξ, ‖G ξ‖ ^ 2 ∂A.quantizer.law := by rfl
      _ = (∫ ξ, ‖G ξ - (v i - delta)‖ ^ 2 ∂A.quantizer.law) +
          ‖v i - delta‖ ^ 2 := hdecomp
      _ = (∫ ξ, ‖A.quantizer.apply (v i) ξ - v i‖ ^ 2
          ∂A.quantizer.law) + ‖v i - delta‖ ^ 2 := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with ξ
        congr 2
        dsimp [G]
        abel
  have hfiber_bound : ∀ i,
      (∫ ξ, ‖innovation (i, ξ)‖ ^ 2 ∂A.quantizer.law) ≤
        ω * ‖v i‖ ^ 2 + ‖v i - delta‖ ^ 2 := by
    intro i
    rw [hfiber_sq_eq i]
    exact add_le_add (hQuantizer.2 (v i)).2.2.2 le_rfl
  let budget := fun i : Worker n => ω * ‖v i‖ ^ 2 + ‖v i - delta‖ ^ 2
  have hbudget_int : Integrable budget (workerLaw n) := Integrable.of_finite
  have hprod_sq : Integrable (fun q => ‖innovation q‖ ^ 2)
      ((workerLaw n).prod A.quantizer.law) := by
    apply integrable_prod_of_fiber_integral_norm_le_integrable_bound
      (μ := workerLaw n) (ν := A.quantizer.law)
      (φ := fun i ξ => ‖innovation (i, ξ)‖ ^ 2) (B := budget)
    · simpa [pow_two] using
        (hinnovation_meas.norm.mul hinnovation_meas.norm).aestronglyMeasurable
    · exact Filter.Eventually.of_forall hfiber_sq
    · exact hbudget_int
    · refine Filter.Eventually.of_forall fun i => ?_
      calc
        (∫ ξ, ‖‖innovation (i, ξ)‖ ^ 2‖ ∂A.quantizer.law) =
            ∫ ξ, ‖innovation (i, ξ)‖ ^ 2 ∂A.quantizer.law := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ξ =>
            Real.norm_of_nonneg (sq_nonneg _)
        _ ≤ budget i := hfiber_bound i
  have hprod_vec : Integrable innovation
      ((workerLaw n).prod A.quantizer.law) :=
    integrable_of_integrable_norm_sq hinnovation_meas.aestronglyMeasurable hprod_sq
  have hprod_mean :
      (∫ q, innovation q ∂(workerLaw n).prod A.quantizer.law) = 0 := by
    rw [integral_prod _ hprod_vec]
    calc
      (∫ i, ∫ ξ, innovation (i, ξ) ∂A.quantizer.law ∂workerLaw n) =
          ∫ i, v i - delta ∂workerLaw n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hfiber_mean
      _ = average (fun i => v i - delta) := hworker_integral_vec _
      _ = average v - delta := by
        calc
          average (fun i => v i - delta) =
              average v - average (fun _ : Worker n => delta) := by
            unfold average SOptLib.finiteUniformAverage
            rw [Finset.sum_sub_distrib, smul_sub]
          _ = average v - delta := by
            rw [show average (fun _ : Worker n => delta) = delta by
              exact SOptLib.finiteUniformAverage_const delta]
      _ = 0 := by rw [hdelta]; simp
  refine ⟨hprod_vec, hprod_sq, hprod_mean, ?_⟩
  rw [integral_prod _ hprod_sq]
  calc
    (∫ i, ∫ ξ, ‖innovation (i, ξ)‖ ^ 2
        ∂A.quantizer.law ∂workerLaw n) ≤
        ∫ i, budget i ∂workerLaw n := by
      exact integral_mono hprod_sq.integral_prod_left hbudget_int hfiber_bound
    _ = average budget := hworker_integral_real _
    _ ≤ average (fun i => (1 + ω) * ‖v i‖ ^ 2) := by
      have hvariance := Finset.weighted_variance_le_second_moment
        (s := (Finset.univ : Finset (Worker n)))
        (q := fun _ : Worker n => (n.1 : ℝ)⁻¹)
        (a := v) (μ := delta) (by simp [n.2.ne']) (by
          simpa [average, SOptLib.finiteUniformAverage_def,
            Fintype.card_fin, ← Finset.smul_sum] using hdelta)
      have hcenter_le : average (fun i => ‖v i - delta‖ ^ 2) ≤
          average (fun i => ‖v i‖ ^ 2) := by
        simpa [average, SOptLib.finiteUniformAverage_def,
          Fintype.card_fin, Finset.mul_sum] using hvariance
      calc
        average budget = ω * average (fun i => ‖v i‖ ^ 2) +
            average (fun i => ‖v i - delta‖ ^ 2) := by
          unfold average SOptLib.finiteUniformAverage
          dsimp [budget]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
        _ ≤ ω * average (fun i => ‖v i‖ ^ 2) +
            average (fun i => ‖v i‖ ^ 2) := by gcongr
        _ = average (fun i => (1 + ω) * ‖v i‖ ^ 2) := by
          unfold average SOptLib.finiteUniformAverage
          simp only [smul_eq_mul]
          rw [← Finset.mul_sum]
          ring
    _ ≤ (1 + ω) * (rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2 := by
      have hLlocal_nonneg : ∀ i, 0 ≤ Llocal i := by
        intro i
        let e : Point d := EuclideanSpace.single ⟨0, d.2⟩ 1
        have hbound := hSmooth.2 i (0 : Point d) e
        have he : ‖(0 : Point d) - e‖ = 1 := by simp [e]
        rw [he, mul_one] at hbound
        exact le_trans (norm_nonneg _) hbound
      have hpoint : ∀ i, ‖v i‖ ^ 2 ≤
          (Llocal i) ^ 2 * ‖xNext - x‖ ^ 2 := by
        intro i
        have hvbound : ‖v i‖ ≤ Llocal i * ‖xNext - x‖ := by
          simpa [v, localGradientDifference] using hSmooth.2 i xNext x
        rw [← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (hLlocal_nonneg i) (norm_nonneg _))).2 hvbound
      have havg_raw : average (fun i => ‖v i‖ ^ 2) ≤
          (rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2 := by
        have hmean_nonneg : 0 ≤ meanSquare Llocal := by
          unfold meanSquare average SOptLib.finiteUniformAverage
          positivity
        have hrms_sq : (rootMeanSquare Llocal) ^ 2 = meanSquare Llocal := by
          unfold rootMeanSquare
          exact Real.sq_sqrt hmean_nonneg
        rw [hrms_sq]
        unfold meanSquare average SOptLib.finiteUniformAverage
        simp only [smul_eq_mul]
        calc
          (Fintype.card (Worker n) : ℝ)⁻¹ *
              ∑ i : Worker n, ‖v i‖ ^ 2 ≤
            (Fintype.card (Worker n) : ℝ)⁻¹ *
              ∑ i : Worker n, (Llocal i) ^ 2 * ‖xNext - x‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun i _hi => hpoint i) (by positivity)
          _ = ((Fintype.card (Worker n) : ℝ)⁻¹ *
              ∑ i : Worker n, (Llocal i) ^ 2) * ‖xNext - x‖ ^ 2 := by
            rw [← Finset.sum_mul]
            ring
      have honega : 0 ≤ 1 + ω := by linarith [hQuantizer.1]
      have hscaled := mul_le_mul_of_nonneg_left havg_raw honega
      calc
        average (fun i => (1 + ω) * ‖v i‖ ^ 2) =
            (1 + ω) * average (fun i => ‖v i‖ ^ 2) := by
          unfold average SOptLib.finiteUniformAverage
          simp only [smul_eq_mul]
          rw [← Finset.mul_sum]
          ring
        _ ≤ (1 + ω) *
            ((rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2) := hscaled
        _ = (1 + ω) * (rootMeanSquare Llocal) ^ 2 *
            ‖xNext - x‖ ^ 2 := by ring

/-- Fixed-query `r`-occurrence PP innovation average.  This is the iid
`1 / r` reduction in the proof of Eq. (59), before the strict-past query is
substituted. -/
theorem pp_fixed_sampled_compressed_row_average_moments
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (xNext x : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let pairLaw := (workerLaw n).prod A.quantizer.law
    let rowLaw := Measure.infinitePi (fun _ : Fin r.1 => pairLaw)
    let delta := globalGradient A.problem xNext - globalGradient A.problem x
    let innovation := fun q : Worker n × Ξ =>
      A.quantizer.apply
          (localGradientDifference A.problem q.1 xNext x) q.2 - delta
    let rowAverage := fun row : Fin r.1 → Worker n × Ξ =>
      average (fun j : Fin r.1 => innovation (row j))
    Integrable rowAverage rowLaw ∧
      (∫ row, rowAverage row ∂rowLaw) = 0 ∧
      Integrable (fun row => ‖rowAverage row‖ ^ 2) rowLaw ∧
      (∫ row, ‖rowAverage row‖ ^ 2 ∂rowLaw) ≤
        ((1 + ω) * (rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2) / r.1 := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  letI : Nonempty (Fin r.1) := ⟨⟨0, r.2⟩⟩
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  let pairLaw := (workerLaw n).prod A.quantizer.law
  let rowLaw := Measure.infinitePi (fun _ : Fin r.1 => pairLaw)
  let delta := globalGradient A.problem xNext - globalGradient A.problem x
  let innovation := fun q : Worker n × Ξ =>
    A.quantizer.apply
        (localGradientDifference A.problem q.1 xNext x) q.2 - delta
  let rowAverage := fun row : Fin r.1 → Worker n × Ξ =>
    average (fun j : Fin r.1 => innovation (row j))
  haveI : IsProbabilityMeasure pairLaw := by dsimp [pairLaw]; infer_instance
  haveI : IsProbabilityMeasure rowLaw := by dsimp [rowLaw]; infer_instance
  have hfixed := pp_fixed_sampled_compressed_innovation_moments
    A xNext x Llocal ω hSmooth hQuantizer
  change Integrable innovation pairLaw ∧
      Integrable (fun q => ‖innovation q‖ ^ 2) pairLaw ∧
      (∫ q, innovation q ∂pairLaw) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2 ∂pairLaw) ≤
        (1 + ω) * (rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2 at hfixed
  have hrowSq := iid_finite_batch_centered_average_sq_integrable_and_le
    pairLaw r innovation
      ((1 + ω) * (rootMeanSquare Llocal) ^ 2 * ‖xNext - x‖ ^ 2)
      hfixed.1 hfixed.2.1 hfixed.2.2.1 hfixed.2.2.2
  have hcoord (j : Fin r.1) :
      Measure.map (fun row : Fin r.1 → Worker n × Ξ => row j) rowLaw =
        pairLaw := by
    dsimp [rowLaw]
    simpa using (MeasureTheory.Measure.infinitePi_map_eval
      (μ := fun _ : Fin r.1 => pairLaw) j)
  have hcoord_int (j : Fin r.1) :
      Integrable (fun row : Fin r.1 → Worker n × Ξ => innovation (row j))
        rowLaw := by
    have honMap : Integrable innovation
        (Measure.map (fun row : Fin r.1 → Worker n × Ξ => row j) rowLaw) := by
      rw [hcoord j]
      exact hfixed.1
    have haesm : AEStronglyMeasurable innovation
        (Measure.map (fun row : Fin r.1 → Worker n × Ξ => row j) rowLaw) :=
      honMap.aestronglyMeasurable
    exact (MeasureTheory.integrable_map_measure haesm
      (measurable_pi_apply j).aemeasurable).mp honMap
  have hcoord_zero (j : Fin r.1) :
      (∫ row, innovation (row j) ∂rowLaw) = 0 := by
    have haesm : AEStronglyMeasurable innovation
        (Measure.map (fun row : Fin r.1 → Worker n × Ξ => row j) rowLaw) := by
      rw [hcoord j]
      exact hfixed.1.aestronglyMeasurable
    calc
      (∫ row, innovation (row j) ∂rowLaw) =
          ∫ q, innovation q
            ∂pairLaw := by
        exact integral_comp_eq_integral_of_map_eq
          (measurable_pi_apply j).aemeasurable haesm (hcoord j)
      _ = 0 := hfixed.2.2.1
  have havgInt : Integrable rowAverage rowLaw := by
    unfold rowAverage average SOptLib.finiteUniformAverage
    simpa [Fintype.card_fin, Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun j _ => hcoord_int j)).smul ((r.1 : ℝ)⁻¹)
  have havgZero : (∫ row, rowAverage row ∂rowLaw) = 0 := by
    unfold rowAverage average SOptLib.finiteUniformAverage
    rw [integral_smul,
      MeasureTheory.integral_finset_sum Finset.univ
        (fun j _ => hcoord_int j)]
    simp [hcoord_zero]
  exact ⟨havgInt, havgZero, hrowSq.1, hrowSq.2⟩

/-- The zipped current PP client/compressor row is an iid row with marginal
`workerLaw n × A.quantizer.law`.  Repeated clients remain allowed. -/
theorem ppRoundLaw_pair_row_marginal
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) :
    Measure.map
        (fun z : PPRoundNoise n r Ξ =>
          fun j : Fin r.1 => (z.2.1 j, z.2.2 j))
        (ppRoundLaw A) =
      Measure.infinitePi
        (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  let restLaw :=
    (ppClientLaw n r).prod (ppCompressionLaw (r := r) A.quantizer)
  have hrest : Measure.map Prod.snd (ppRoundLaw A) = restLaw := by
    unfold ppRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  have hzip : Measure.map
      (fun q : (Fin r.1 → Worker n) × (Fin r.1 → Ξ) =>
        fun j => (q.1 j, q.2 j)) restLaw =
      Measure.infinitePi
        (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
    let α := fun _ : Fin r.1 => Worker n
    let β := fun _ : Fin r.1 => Ξ
    let μ := fun _ : Fin r.1 => workerLaw n
    let ν := fun _ : Fin r.1 => A.quantizer.law
    have hmp := measurePreserving_dependentArrowProdMeasurableEquiv α β μ ν
    have hinv := MeasurePreserving.symm
      (dependentArrowProdMeasurableEquiv α β) hmp
    simpa [restLaw, ppClientLaw, ppCompressionLaw, α, β, μ, ν,
      MeasureTheory.Measure.infinitePi_eq_pi] using hinv.map_eq
  calc
    Measure.map
        (fun z : PPRoundNoise n r Ξ =>
          fun j : Fin r.1 => (z.2.1 j, z.2.2 j))
        (ppRoundLaw A) =
      Measure.map
        (fun q : (Fin r.1 → Worker n) × (Fin r.1 → Ξ) =>
          fun j => (q.1 j, q.2 j))
        (Measure.map Prod.snd (ppRoundLaw A)) := by
      rw [MeasureTheory.Measure.map_map]
      · rfl
      · fun_prop
      · exact measurable_snd
    _ = Measure.map
        (fun q : (Fin r.1 → Worker n) × (Fin r.1 → Ξ) =>
          fun j => (q.1 j, q.2 j)) restLaw := by rw [hrest]
    _ = _ := hzip

/-- The strict PP round prefix is independent of the current zipped iid
client/compressor row, and that row has its canonical iid product law. -/
theorem ppPathLaw_prefix_pair_row_independent
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (k : ℕ) :
    let law := ppPathLaw (r := r) A
    let pastPrefix := fun path : ℕ → PPRoundNoise n r Ξ =>
      fun j : Fin k => path j.1
    let row := fun path : ℕ → PPRoundNoise n r Ξ =>
      fun j : Fin r.1 => ((path k).2.1 j, (path k).2.2 j)
    ProbabilityTheory.IndepFun pastPrefix row law ∧
      Measure.map row law = Measure.infinitePi
        (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  let law := ppPathLaw (r := r) A
  let pastPrefix := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin k => path j.1
  let current := fun path : ℕ → PPRoundNoise n r Ξ => path k
  let roundRow := fun z : PPRoundNoise n r Ξ =>
    fun j : Fin r.1 => (z.2.1 j, z.2.2 j)
  let row := roundRow ∘ current
  have hprefix : Measurable pastPrefix := by
    dsimp [pastPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hroundRow : Measurable roundRow := by
    dsimp [roundRow]
    fun_prop
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  let prefixLaw := Measure.map pastPrefix law
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hpastCurrent : ProbabilityTheory.IndepFun pastPrefix current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path => (pastPrefix path, current path))
      (P := law) (mu := prefixLaw) (nu := ppRoundLaw A)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [law, prefixLaw, pastPrefix, current, ppPathLaw,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => ppRoundLaw (n := n) (r := r) A) k)
  have hindep : ProbabilityTheory.IndepFun pastPrefix row law := by
    simpa [row, Function.comp_def] using
      hpastCurrent.comp measurable_id hroundRow
  have hcurrentLaw : Measure.map current law = ppRoundLaw A := by
    simpa [current, law, ppPathLaw] using
      SOptLib.iidStreamLaw_map_eval (ppRoundLaw (n := n) (r := r) A) k
  have hrowLaw : Measure.map row law = Measure.infinitePi
      (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
    calc
      Measure.map row law = Measure.map roundRow (Measure.map current law) := by
        rw [MeasureTheory.Measure.map_map]
        · exact hroundRow
        · exact hcurrent
      _ = Measure.map roundRow (ppRoundLaw A) := by rw [hcurrentLaw]
      _ = _ := by simpa [roundRow] using ppRoundLaw_pair_row_marginal A
  exact ⟨hindep, hrowLaw⟩

/-- Local gradients remain jointly measurable when the worker is selected by
a finite-valued measurable coordinate. -/
theorem pp_selected_localGradient_joint_measurable
    {d n : Count} (P : LocalProblem d n) :
    Measurable (fun p : Worker n × Point d => localGradient P p.1 p.2) := by
  classical
  have hsum : Measurable (fun p : Worker n × Point d =>
      ∑ i : Worker n,
        if p.1 = i then localGradient P i p.2 else 0) := by
    apply Finset.measurable_sum
    intro i _hi
    apply Measurable.ite
    · exact measurable_fst (measurableSet_singleton i)
    · exact (measurable_localGradient P i).comp measurable_snd
    · exact measurable_const
  convert hsum using 1
  funext p
  simp

/-- The PP transition is jointly measurable in the previous state and current
round noise. -/
theorem ppStep_round_joint_measurable
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) :
    Measurable (fun p : State d × PPRoundNoise n r Ξ =>
      ppStep A (ppDriverOfNoise p.2) p.1) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  letI : Nonempty (Fin r.1) := ⟨⟨0, r.2⟩⟩
  have hxNext : Measurable (fun p : State d × PPRoundNoise n r Ξ =>
      primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hx : Measurable (fun p : State d × PPRoundNoise n r Ξ => p.1.x) :=
    (measurable_state_x d).comp measurable_fst
  have hclient (j : Fin r.1) : Measurable
      (fun p : State d × PPRoundNoise n r Ξ => p.2.2.1 j) := by
    fun_prop
  have hcompression (j : Fin r.1) : Measurable
      (fun p : State d × PPRoundNoise n r Ξ => p.2.2.2 j) := by
    fun_prop
  have hdiff (j : Fin r.1) : Measurable
      (fun p : State d × PPRoundNoise n r Ξ =>
        localGradientDifference A.problem (p.2.2.1 j)
          (primalStep A.stepSize p.1) p.1.x) := by
    unfold localGradientDifference
    have hsel := pp_selected_localGradient_joint_measurable A.problem
    exact (hsel.comp ((hclient j).prodMk hxNext)).sub
      (hsel.comp ((hclient j).prodMk hx))
  have hquantized (j : Fin r.1) : Measurable
      (fun p : State d × PPRoundNoise n r Ξ =>
        A.quantizer.apply
          (localGradientDifference A.problem (p.2.2.1 j)
            (primalStep A.stepSize p.1) p.1.x)
          (p.2.2.2 j)) := by
    exact A.quantizer.measurable_apply_uncurry.comp
      ((hdiff j).prodMk (hcompression j))
  have havg : Measurable
      (fun p : State d × PPRoundNoise n r Ξ =>
        average (fun j : Fin r.1 =>
          A.quantizer.apply
            (localGradientDifference A.problem (p.2.2.1 j)
              (primalStep A.stepSize p.1) p.1.x)
            (p.2.2.2 j))) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ
      (fun j _ => hquantized j)).const_smul
        ((Fintype.card (Fin r.1) : ℝ)⁻¹)
  have hnonrefresh : Measurable
      (fun p : State d × PPRoundNoise n r Ξ => p.1.g +
        average (fun j : Fin r.1 =>
          A.quantizer.apply
            (localGradientDifference A.problem (p.2.2.1 j)
              (primalStep A.stepSize p.1) p.1.x)
            (p.2.2.2 j))) :=
    ((measurable_state_g d).comp measurable_fst).add havg
  have hrefresh : Measurable
      (fun p : State d × PPRoundNoise n r Ξ =>
        globalGradient A.problem (primalStep A.stepSize p.1)) :=
    (measurable_gradient (globalObjective A.problem)).comp hxNext
  have hrefreshSet : MeasurableSet
      {p : State d × PPRoundNoise n r Ξ | p.2.1 = true} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
  have hg : Measurable (fun p : State d × PPRoundNoise n r Ξ =>
      if p.2.1 then
        globalGradient A.problem (primalStep A.stepSize p.1)
      else p.1.g + average (fun j : Fin r.1 =>
        A.quantizer.apply
          (localGradientDifference A.problem (p.2.2.1 j)
            (primalStep A.stepSize p.1) p.1.x)
          (p.2.2.2 j))) := by
    exact Measurable.ite hrefreshSet hrefresh hnonrefresh
  have hgStep : Measurable (fun p : State d × PPRoundNoise n r Ξ =>
      (ppStep A (ppDriverOfNoise p.2) p.1).g) := by
    convert hg using 1
    funext p
    simpa [ppDriverOfNoise] using
      PP_estimator_update A (ppDriverOfNoise p.2) p.1 Llocal hSmooth
  exact (measurable_state_mk d).comp (hxNext.prodMk hgStep)

/-- The PP state at time `k` is measurable from the strict round prefix. -/
theorem ppProcess_strictPast_measurable
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance]
      (ppProcess (r := r) A x0 k) := by
  let past : Unit → MeasurableSpace (ℕ → PPRoundNoise n r Ξ) :=
    fun _ => ⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance
  let driver : ℕ → (ℕ → PPRoundNoise n r Ξ) → PPRoundNoise n r Ξ :=
    fun t path => path t
  let step : ℕ → State d → PPRoundNoise n r Ξ → State d :=
    fun _ s z => ppStep A (ppDriverOfNoise z) s
  apply SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := past) (process := ppProcess (r := r) A x0)
      (driver := driver) (step := step) (k := ()) (N := k)
  · exact measurable_const
  · intro t ht _hprocess
    rw [measurable_iff_comap_le]
    exact le_iSup_of_le ⟨t, Nat.lt_of_succ_le ht⟩ (by rfl)
  · intro _t _ht
    exact ppStep_round_joint_measurable A Llocal hSmooth
  · intro t _ht
    rfl
  · exact le_rfl

/-- The PP query `(x^{k+1},x^k)` is strict-past measurable and independent
of the current iid client/compressor row. -/
theorem pp_strictPast_query_indep_pair_row
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    let law := ppPathLaw (r := r) A
    let run := ppProcess (r := r) A x0
    let query := fun path : ℕ → PPRoundNoise n r Ξ =>
      (primalStep A.stepSize (run k path), (run k path).x)
    let row := fun path : ℕ → PPRoundNoise n r Ξ =>
      fun j : Fin r.1 => ((path k).2.1 j, (path k).2.2 j)
    ProbabilityTheory.IndepFun query row law ∧
      Measure.map row law = Measure.infinitePi
        (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
  let law := ppPathLaw (r := r) A
  let run := ppProcess (r := r) A x0
  let query := fun path : ℕ → PPRoundNoise n r Ξ =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let pastPrefix := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin k => path j.1
  let row := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin r.1 => ((path k).2.1 j, (path k).2.2 j)
  have hbase := ppPathLaw_prefix_pair_row_independent (r := r) A k
  have hbaseIndep : ProbabilityTheory.IndepFun pastPrefix row law := by
    simpa [pastPrefix, row, law] using hbase.1
  have hbaseLaw :
      Measure.map row law = Measure.infinitePi
        (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
    simpa [row, law] using hbase.2
  have hstate : Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance]
      (run k) := by
    simpa [run] using
      ppProcess_strictPast_measurable A x0 Llocal hSmooth k
  have hquery : Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance]
      query := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp hstate).prodMk
      ((measurable_state_x d).comp hstate)
  have hpastPrefix : Measurable pastPrefix := by
    dsimp [pastPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hstrict_le : (⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
      MeasurableSpace.comap pastPrefix inferInstance := by
    refine iSup_le fun j => ?_
    have hpast_comap : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        pastPrefix := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply j).comp hpast_comap).comap_le
  have hcomap : ProbabilityTheory.Indep
      (MeasurableSpace.comap pastPrefix inferInstance)
      (MeasurableSpace.comap row inferInstance) law := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hbaseIndep
  have hindep : ProbabilityTheory.IndepFun query row law :=
    indepFun_of_measurable_left_of_indep_comap hquery
      (ProbabilityTheory.indep_of_indep_of_le_left hcomap hstrict_le)
  exact ⟨hindep, hbaseLaw⟩

/-- The generated PP innovation average has the exact inverse-participation
second-moment factor at the strict-past query. -/
theorem pp_generated_innovation_second_moment
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ)
    (hStep : StepMomentWellDefined (ppProcess (r := r) A x0)
      (ppPathLaw (r := r) A) k) :
    let run := ppProcess (r := r) A x0
    let law := ppPathLaw (r := r) A
    let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
      let xNext := (run (k + 1) path).x
      let x := (run k path).x
      let delta := globalGradient A.problem xNext - globalGradient A.problem x
      average (fun j : Fin r.1 =>
        A.quantizer.apply
            (localGradientDifference A.problem ((path k).2.1 j) xNext x)
            ((path k).2.2 j) - delta)
    Integrable innovation law ∧
      Integrable (fun path => ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        ((1 + ω) * (rootMeanSquare Llocal) ^ 2 / r.1) *
          stepMoment run law k := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  letI : Nonempty (Fin r.1) := ⟨⟨0, r.2⟩⟩
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  letI : IsProbabilityMeasure
      ((workerLaw n).prod A.quantizer.law) := by infer_instance
  let run := ppProcess (r := r) A x0
  let law := ppPathLaw (r := r) A
  let pairLaw := (workerLaw n).prod A.quantizer.law
  let rowLaw := Measure.infinitePi (fun _ : Fin r.1 => pairLaw)
  let query := fun path : ℕ → PPRoundNoise n r Ξ =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let row := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin r.1 => ((path k).2.1 j, (path k).2.2 j)
  let atom := fun z : Point d × Point d => fun q : Worker n × Ξ =>
    A.quantizer.apply
        (localGradientDifference A.problem q.1 z.1 z.2) q.2 -
      (globalGradient A.problem z.1 - globalGradient A.problem z.2)
  let rowAverage := fun z : Point d × Point d =>
    fun samples : Fin r.1 → Worker n × Ξ =>
      average (fun j : Fin r.1 => atom z (samples j))
  let phi := fun z : Point d × Point d =>
    fun samples : Fin r.1 → Worker n × Ξ => ‖rowAverage z samples‖ ^ 2
  let coeff := (1 + ω) * (rootMeanSquare Llocal) ^ 2 / r.1
  let B := fun z : Point d × Point d => coeff * ‖z.1 - z.2‖ ^ 2
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw, pairLaw]
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw ppRoundLaw ppClientLaw
      ppCompressionLaw workerLaw refreshLaw
    infer_instance
  have hquery : Measurable query := by
    have hs := ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    have hsFull := hs.mono hle le_rfl
    exact ((measurable_primalStep A.stepSize).comp hsFull).prodMk
      ((measurable_state_x d).comp hsFull)
  have hrow : Measurable row := by
    dsimp [row]
    fun_prop
  have hfresh := pp_strictPast_query_indep_pair_row
    (r := r) A x0 Llocal hSmooth k
  change ProbabilityTheory.IndepFun query row law ∧
      Measure.map row law = rowLaw at hfresh
  have hselected := pp_selected_localGradient_joint_measurable A.problem
  have hatom : Measurable (Function.uncurry atom) := by
    have hclient : Measurable
        (fun p : (Point d × Point d) × (Worker n × Ξ) => p.2.1) := by fun_prop
    have hxnext : Measurable
        (fun p : (Point d × Point d) × (Worker n × Ξ) => p.1.1) := by fun_prop
    have hx : Measurable
        (fun p : (Point d × Point d) × (Worker n × Ξ) => p.1.2) := by fun_prop
    have hdiff : Measurable
        (fun p : (Point d × Point d) × (Worker n × Ξ) =>
          localGradientDifference A.problem p.2.1 p.1.1 p.1.2) := by
      unfold localGradientDifference
      exact (hselected.comp (hclient.prodMk hxnext)).sub
        (hselected.comp (hclient.prodMk hx))
    have hquantized := A.quantizer.measurable_apply_uncurry.comp
      (hdiff.prodMk (show Measurable
        (fun p : (Point d × Point d) × (Worker n × Ξ) => p.2.2) by
          fun_prop))
    have hdelta : Measurable
        (fun p : (Point d × Point d) × (Worker n × Ξ) =>
          globalGradient A.problem p.1.1 - globalGradient A.problem p.1.2) :=
      ((measurable_gradient (globalObjective A.problem)).comp hxnext).sub
        ((measurable_gradient (globalObjective A.problem)).comp hx)
    simpa [atom, Function.uncurry] using hquantized.sub hdelta
  have hrowAverage : Measurable (Function.uncurry rowAverage) := by
    unfold rowAverage average SOptLib.finiteUniformAverage
    have hcoord (j : Fin r.1) : Measurable
        (fun p : (Point d × Point d) × (Fin r.1 → Worker n × Ξ) =>
          (p.1, p.2 j)) :=
      measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
    have hsum := Finset.measurable_sum Finset.univ
      (fun j _ => hatom.comp (hcoord j))
    exact hsum.const_smul ((Fintype.card (Fin r.1) : ℝ)⁻¹)
  have hphi : Measurable (Function.uncurry phi) := by
    dsimp [phi, Function.uncurry]
    exact hrowAverage.norm.pow_const 2
  have hB : Measurable B := by
    dsimp [B]
    fun_prop
  have hfixed : ∀ z : Point d × Point d,
      Integrable (rowAverage z) rowLaw ∧
      (∫ samples, rowAverage z samples ∂rowLaw) = 0 ∧
      Integrable (phi z) rowLaw ∧
      (∫ samples, phi z samples ∂rowLaw) ≤ B z := by
    intro z
    have hz := pp_fixed_sampled_compressed_row_average_moments
      (r := r) A z.1 z.2 Llocal ω hSmooth hQuantizer
    change Integrable (rowAverage z) rowLaw ∧
      (∫ samples, rowAverage z samples ∂rowLaw) = 0 ∧
      Integrable (phi z) rowLaw ∧
      (∫ samples, phi z samples ∂rowLaw) ≤ B z
    refine ⟨by simpa [pairLaw, rowLaw, atom, rowAverage] using hz.1,
      by simpa [pairLaw, rowLaw, atom, rowAverage] using hz.2.1,
      by simpa [pairLaw, rowLaw, atom, rowAverage, phi] using hz.2.2.1, ?_⟩
    calc
      (∫ samples, phi z samples ∂rowLaw) ≤
          ((1 + ω) * (rootMeanSquare Llocal) ^ 2 * ‖z.1 - z.2‖ ^ 2) /
            r.1 := by
        simpa [pairLaw, rowLaw, atom, rowAverage, phi] using hz.2.2.2
      _ = B z := by dsimp [B, coeff]; ring
  have hBcomp : Integrable (fun path => B (query path)) law := by
    have hs := hStep.const_mul coeff
    simpa [B, query, coeff, run, law, StepMomentWellDefined, ppProcess,
      ppRun_succ, ppStep] using hs
  have hphiComp : Integrable (fun path => phi (query path) (row path)) law := by
    apply integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
      (P := law) (ν := rowLaw) (X := query) (Y := row) (B := B)
    · exact hphi.aestronglyMeasurable
    · exact hB.aestronglyMeasurable
    · exact hquery.aemeasurable
    · exact hrow.aemeasurable
    · exact hfresh.1
    · exact hfresh.2
    · intro z samples
      exact sq_nonneg _
    · intro z
      exact (hfixed z).2.2.1
    · exact hBcomp
    · intro z
      exact (hfixed z).2.2.2
  have hbound :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := rowLaw) (X := query) (Y := row)
      (φ := phi) (B := B) hphi.aestronglyMeasurable hB.aestronglyMeasurable
      hquery.aemeasurable hrow.aemeasurable hfresh.1 hfresh.2
      hphiComp hBcomp (fun z => (hfixed z).2.2.2)
  let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    let delta := globalGradient A.problem xNext - globalGradient A.problem x
    average (fun j : Fin r.1 =>
      A.quantizer.apply
          (localGradientDifference A.problem ((path k).2.1 j) xNext x)
          ((path k).2.2 j) - delta)
  have hinnovation_eq : innovation = fun path => rowAverage (query path) (row path) := by
    funext path
    simp only [innovation, rowAverage, atom, query, row]
    rfl
  have havgMeas : AEStronglyMeasurable innovation law := by
    rw [hinnovation_eq]
    exact (hrowAverage.comp (hquery.prodMk hrow)).aestronglyMeasurable
  have hsq : Integrable (fun path => ‖innovation path‖ ^ 2) law := by
    simpa [hinnovation_eq, phi] using hphiComp
  have hvec := integrable_of_integrable_norm_sq havgMeas hsq
  refine ⟨hvec, hsq, ?_⟩
  calc
    (∫ path, ‖innovation path‖ ^ 2 ∂law) =
        ∫ path, phi (query path) (row path) ∂law := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path => by
        rw [hinnovation_eq]
    _ ≤ ∫ path, B (query path) ∂law := hbound
    _ = coeff * stepMoment run law k := by
      unfold B query stepMoment
      rw [integral_const_mul]
      rfl

/-- The full strict-past PP state is independent of the current paired row. -/
theorem pp_strictPast_state_indep_pair_row
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    let law := ppPathLaw (r := r) A
    let run := ppProcess (r := r) A x0
    let row := fun path : ℕ → PPRoundNoise n r Ξ =>
      fun j : Fin r.1 => ((path k).2.1 j, (path k).2.2 j)
    ProbabilityTheory.IndepFun (run k) row law ∧
      Measure.map row law = Measure.infinitePi
        (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
  let law := ppPathLaw (r := r) A
  let run := ppProcess (r := r) A x0
  let pastPrefix := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin k => path j.1
  let row := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin r.1 => ((path k).2.1 j, (path k).2.2 j)
  have hbase := ppPathLaw_prefix_pair_row_independent (r := r) A k
  have hbaseIndep : ProbabilityTheory.IndepFun pastPrefix row law := by
    simpa [pastPrefix, row, law] using hbase.1
  have hbaseLaw : Measure.map row law = Measure.infinitePi
      (fun _ : Fin r.1 => (workerLaw n).prod A.quantizer.law) := by
    simpa [row, law] using hbase.2
  have hstate : Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance]
      (run k) := by
    simpa [run] using
      ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth k
  have hstrict_le : (⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
      MeasurableSpace.comap pastPrefix inferInstance := by
    refine iSup_le fun j => ?_
    have hpast_comap : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        pastPrefix := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply j).comp hpast_comap).comap_le
  have hcomap : ProbabilityTheory.Indep
      (MeasurableSpace.comap pastPrefix inferInstance)
      (MeasurableSpace.comap row inferInstance) law := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hbaseIndep
  exact ⟨indepFun_of_measurable_left_of_indep_comap hstate
    (ProbabilityTheory.indep_of_indep_of_le_left hcomap hstrict_le), hbaseLaw⟩

/-- The carried PP estimator residual is orthogonal to the generated current
row innovation average. -/
theorem pp_generated_residual_innovation_cross_eq_zero
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ) :
    let run := ppProcess (r := r) A x0
    let law := ppPathLaw (r := r) A
    let residual := fun path : ℕ → PPRoundNoise n r Ξ =>
      (run k path).g - globalGradient A.problem (run k path).x
    let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
      let xNext := (run (k + 1) path).x
      let x := (run k path).x
      let delta := globalGradient A.problem xNext - globalGradient A.problem x
      average (fun j : Fin r.1 =>
        A.quantizer.apply
            (localGradientDifference A.problem ((path k).2.1 j) xNext x)
            ((path k).2.2 j) - delta)
    (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  letI : Nonempty (Fin r.1) := ⟨⟨0, r.2⟩⟩
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  let run := ppProcess (r := r) A x0
  let law := ppPathLaw (r := r) A
  let pairLaw := (workerLaw n).prod A.quantizer.law
  let rowLaw := Measure.infinitePi (fun _ : Fin r.1 => pairLaw)
  let state := run k
  let row := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin r.1 => ((path k).2.1 j, (path k).2.2 j)
  let rowInnovation := fun s : State d =>
    fun samples : Fin r.1 → Worker n × Ξ =>
      let xNext := primalStep A.stepSize s
      let delta := globalGradient A.problem xNext - globalGradient A.problem s.x
      average (fun j : Fin r.1 =>
        A.quantizer.apply
            (localGradientDifference A.problem (samples j).1 xNext s.x)
            (samples j).2 - delta)
  let direction := fun s : State d =>
    s.g - globalGradient A.problem s.x
  haveI : IsProbabilityMeasure pairLaw := by dsimp [pairLaw]; infer_instance
  haveI : IsProbabilityMeasure rowLaw := by dsimp [rowLaw]; infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw ppRoundLaw ppClientLaw
      ppCompressionLaw workerLaw refreshLaw
    infer_instance
  have hstate : Measurable state := by
    have hs := ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    exact hs.mono hle le_rfl
  have hrow : Measurable row := by dsimp [row]; fun_prop
  have hfresh := pp_strictPast_state_indep_pair_row
    (r := r) A x0 Llocal hSmooth k
  change ProbabilityTheory.IndepFun state row law ∧
      Measure.map row law = rowLaw at hfresh
  have hselected := pp_selected_localGradient_joint_measurable A.problem
  have hrowInnovation : Measurable (Function.uncurry rowInnovation) := by
    have hs : Measurable
        (fun p : State d × (Fin r.1 → Worker n × Ξ) => p.1) := measurable_fst
    have hxnext : Measurable
        (fun p : State d × (Fin r.1 → Worker n × Ξ) =>
          primalStep A.stepSize p.1) :=
      (measurable_primalStep A.stepSize).comp hs
    have hx : Measurable
        (fun p : State d × (Fin r.1 → Worker n × Ξ) => p.1.x) :=
      (measurable_state_x d).comp hs
    have hdelta : Measurable
        (fun p : State d × (Fin r.1 → Worker n × Ξ) =>
          globalGradient A.problem (primalStep A.stepSize p.1) -
            globalGradient A.problem p.1.x) :=
      ((measurable_gradient (globalObjective A.problem)).comp hxnext).sub
        ((measurable_gradient (globalObjective A.problem)).comp hx)
    have hterm (j : Fin r.1) : Measurable
        (fun p : State d × (Fin r.1 → Worker n × Ξ) =>
          A.quantizer.apply
              (localGradientDifference A.problem (p.2 j).1
                (primalStep A.stepSize p.1) p.1.x) (p.2 j).2 -
            (globalGradient A.problem (primalStep A.stepSize p.1) -
              globalGradient A.problem p.1.x)) := by
      have hclient : Measurable
          (fun p : State d × (Fin r.1 → Worker n × Ξ) => (p.2 j).1) := by
        fun_prop
      have hdiff : Measurable
          (fun p : State d × (Fin r.1 → Worker n × Ξ) =>
            localGradientDifference A.problem (p.2 j).1
              (primalStep A.stepSize p.1) p.1.x) := by
        unfold localGradientDifference
        exact (hselected.comp (hclient.prodMk hxnext)).sub
          (hselected.comp (hclient.prodMk hx))
      have hquantized := A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk (show Measurable
          (fun p : State d × (Fin r.1 → Worker n × Ξ) => (p.2 j).2) by
            fun_prop))
      exact hquantized.sub hdelta
    unfold rowInnovation average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ
      (fun j _ => hterm j)).const_smul ((Fintype.card (Fin r.1) : ℝ)⁻¹)
  have hdirection : Measurable direction := by
    dsimp [direction]
    exact (measurable_state_g d).sub
      ((measurable_gradient (globalObjective A.problem)).comp (measurable_state_x d))
  have hfixed : ∀ s : State d,
      Integrable (rowInnovation s) rowLaw ∧
      (∫ samples, rowInnovation s samples ∂rowLaw) = 0 := by
    intro s
    have hs := pp_fixed_sampled_compressed_row_average_moments
      (r := r) A (primalStep A.stepSize s) s.x Llocal ω hSmooth hQuantizer
    exact ⟨by simpa [rowInnovation, rowLaw, pairLaw] using hs.1,
      by simpa [rowInnovation, rowLaw, pairLaw] using hs.2.1⟩
  have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
    law rowLaw state row rowInnovation direction hrowInnovation hdirection
      hstate hrow hfresh.1 hfresh.2 (fun s => (hfixed s).1)
      (fun s => (hfixed s).2)
  let residual := fun path : ℕ → PPRoundNoise n r Ξ =>
    (run k path).g - globalGradient A.problem (run k path).x
  let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    let delta := globalGradient A.problem xNext - globalGradient A.problem x
    average (fun j : Fin r.1 =>
      A.quantizer.apply
          (localGradientDifference A.problem ((path k).2.1 j) xNext x)
          ((path k).2.2 j) - delta)
  simpa [residual, innovation, rowInnovation, direction, state, row, run,
    ppProcess, ppRun_succ, ppStep] using hzero

/-- Generated nonrefresh PP residual-plus-innovation moment bound. -/
theorem pp_generated_nonrefresh_branch_moments
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined A.problem
      (ppProcess (r := r) A x0) (ppPathLaw (r := r) A) k)
    (hStep : StepMomentWellDefined (ppProcess (r := r) A x0)
      (ppPathLaw (r := r) A) k) :
    let run := ppProcess (r := r) A x0
    let law := ppPathLaw (r := r) A
    let residual := fun path : ℕ → PPRoundNoise n r Ξ =>
      (run k path).g - globalGradient A.problem (run k path).x
    let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
      let xNext := (run (k + 1) path).x
      let x := (run k path).x
      let delta := globalGradient A.problem xNext - globalGradient A.problem x
      average (fun j : Fin r.1 =>
        A.quantizer.apply
            (localGradientDifference A.problem ((path k).2.1 j) xNext x)
            ((path k).2.2 j) - delta)
    Integrable (fun path => ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment A.problem run law k +
          ((1 + ω) * (rootMeanSquare Llocal) ^ 2 / r.1) *
            stepMoment run law k := by
  let run := ppProcess (r := r) A x0
  let law := ppPathLaw (r := r) A
  let residual := fun path : ℕ → PPRoundNoise n r Ξ =>
    (run k path).g - globalGradient A.problem (run k path).x
  let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    let delta := globalGradient A.problem xNext - globalGradient A.problem x
    average (fun j : Fin r.1 =>
      A.quantizer.apply
          (localGradientDifference A.problem ((path k).2.1 j) xNext x)
          ((path k).2.2 j) - delta)
  have hgen := pp_generated_innovation_second_moment
    (r := r) A x0 Llocal ω hSmooth hQuantizer k hStep
  change Integrable innovation law ∧
      Integrable (fun path => ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        ((1 + ω) * (rootMeanSquare Llocal) ^ 2 / r.1) *
          stepMoment run law k at hgen
  have hcross := pp_generated_residual_innovation_cross_eq_zero
    (r := r) A x0 Llocal ω hSmooth hQuantizer k
  change (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 at hcross
  have hresMeas : AEStronglyMeasurable residual law := by
    have hs := ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    have hsFull := hs.mono hle le_rfl
    dsimp [residual, run]
    exact (((measurable_state_g d).comp hsFull).sub
      ((measurable_gradient (globalObjective A.problem)).comp
        ((measurable_state_x d).comp hsFull))).aestronglyMeasurable
  have hinner : Integrable
      (fun path => ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresMeas hgen.1.aestronglyMeasurable
      hError hgen.2.1
  have hsum : Integrable
      (fun path => ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresMeas hgen.1.aestronglyMeasurable hError hgen.2.1
  refine ⟨hsum, ?_⟩
  calc
    (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          (∫ path, ‖innovation path‖ ^ 2 ∂law) +
          2 * (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) := by
      have hresSq : Integrable (fun path => ‖residual path‖ ^ 2) law := hError
      rw [show (fun path => ‖residual path + innovation path‖ ^ 2) =
          fun path => ‖residual path‖ ^ 2 + ‖innovation path‖ ^ 2 +
            2 * ⟪residual path, innovation path⟫_ℝ by
        funext path
        rw [norm_add_sq_real]
        ring]
      calc
        (∫ path, ‖residual path‖ ^ 2 + ‖innovation path‖ ^ 2 +
            2 * ⟪residual path, innovation path⟫_ℝ ∂law) =
          (∫ path, ‖residual path‖ ^ 2 + ‖innovation path‖ ^ 2 ∂law) +
            ∫ path, 2 * ⟪residual path, innovation path⟫_ℝ ∂law :=
              integral_add (hresSq.add hgen.2.1) (hinner.const_mul 2)
        _ = (∫ path, ‖residual path‖ ^ 2 ∂law) +
            (∫ path, ‖innovation path‖ ^ 2 ∂law) +
            2 * (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) := by
          rw [integral_add hresSq hgen.2.1, integral_const_mul]
    _ = estimatorErrorMoment A.problem run law k +
        (∫ path, ‖innovation path‖ ^ 2 ∂law) := by
      rw [hcross]
      simp [estimatorErrorMoment, residual]
    _ ≤ estimatorErrorMoment A.problem run law k +
        ((1 + ω) * (rootMeanSquare Llocal) ^ 2 / r.1) *
          stepMoment run law k := by linarith [hgen.2.2]

/-- Pathwise PP residual decomposition into the exact-refresh zero branch and
the carried residual plus centered iid-row innovation. -/
theorem pp_next_residual_eq_if_refresh
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ)
    (path : ℕ → PPRoundNoise n r Ξ) :
    let run := ppProcess (r := r) A x0
    let residual := (run k path).g - globalGradient A.problem (run k path).x
    let xNext := (run (k + 1) path).x
    let delta := globalGradient A.problem xNext -
      globalGradient A.problem (run k path).x
    let innovation := average (fun j : Fin r.1 =>
      A.quantizer.apply
          (localGradientDifference A.problem ((path k).2.1 j) xNext
            (run k path).x) ((path k).2.2 j) - delta)
    (run (k + 1) path).g - globalGradient A.problem xNext =
      if (path k).1 then 0 else residual + innovation := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  letI : Nonempty (Fin r.1) := ⟨⟨0, r.2⟩⟩
  let run := ppProcess (r := r) A x0
  let s := run k path
  let xNext := (run (k + 1) path).x
  let delta := globalGradient A.problem xNext - globalGradient A.problem s.x
  let q := fun j : Fin r.1 =>
    A.quantizer.apply
      (localGradientDifference A.problem ((path k).2.1 j) xNext s.x)
      ((path k).2.2 j)
  let innovation := average (fun j : Fin r.1 => q j - delta)
  have hxNext : xNext = primalStep A.stepSize s := by rfl
  have hupdate := PP_estimator_update A (ppDriverOfNoise (path k)) s
    Llocal hSmooth
  have hinnovation : innovation = average q - delta := by
    unfold innovation average SOptLib.finiteUniformAverage
    rw [Finset.sum_sub_distrib, smul_sub]
    rw [show (Fintype.card (Fin r.1) : ℝ)⁻¹ •
        ∑ _j : Fin r.1, delta = delta by
      exact SOptLib.finiteUniformAverage_const delta]
  dsimp [ppDriverOfNoise] at hupdate
  rw [← hxNext] at hupdate
  cases hb : (path k).1 with
  | false =>
      simp only [hb, Bool.false_eq_true, if_false]
      simp [hb] at hupdate
      have hg : (run (k + 1) path).g = s.g + average q := by
        change (ppStep A (ppDriverOfNoise (path k)) s).g = _
        simp only [ppDriverOfNoise]
        rw [hb]
        simpa [q, ppDriverOfNoise] using hupdate
      rw [hg]
      change s.g + average q - globalGradient A.problem xNext =
        (s.g - globalGradient A.problem s.x) + innovation
      rw [hinnovation]
      dsimp [delta]
      abel
  | true =>
      simp only [hb, if_true]
      simp [hb] at hupdate
      have hg : (run (k + 1) path).g = globalGradient A.problem xNext := by
        change (ppStep A (ppDriverOfNoise (path k)) s).g = _
        simp only [ppDriverOfNoise]
        rw [hb]
        simpa [ppDriverOfNoise] using hupdate
      rw [hg]
      exact sub_self _

/-- The PP non-refresh residual square depends on the strict past and the
current client/compressor row, and is therefore independent of the current
refresh coin. -/
theorem pp_nonrefresh_square_indep_refresh
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → PPRoundNoise n r Ξ =>
        let run := ppProcess (r := r) A x0
        let residual := (run k path).g -
          globalGradient A.problem (run k path).x
        let xNext := (run (k + 1) path).x
        let delta := globalGradient A.problem xNext -
          globalGradient A.problem (run k path).x
        let innovation := average (fun j : Fin r.1 =>
          A.quantizer.apply
              (localGradientDifference A.problem ((path k).2.1 j) xNext
                (run k path).x) ((path k).2.2 j) - delta)
        ‖residual + innovation‖ ^ 2)
      (fun path : ℕ → PPRoundNoise n r Ξ => (path k).1)
      (ppPathLaw A) := by
  classical
  let P := ppPathLaw (r := r) A
  let run := ppProcess (r := r) A x0
  let pastBlock := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun j : Fin k => path j.1
  let current := fun path : ℕ → PPRoundNoise n r Ξ => path k
  let rest := fun z : PPRoundNoise n r Ξ => z.2
  let branchRound := fun z : PPRoundNoise n r Ξ => z.1
  let restPath := fun path : ℕ → PPRoundNoise n r Ξ => (path k).2
  let branch := fun path : ℕ → PPRoundNoise n r Ξ => (path k).1
  let joined := fun path : ℕ → PPRoundNoise n r Ξ =>
    (pastBlock path, restPath path)
  let Z := fun path : ℕ → PPRoundNoise n r Ξ =>
    (pastBlock path, current path)
  let prefixLaw := Measure.map pastBlock P
  let restLaw := (ppClientLaw n r).prod
    (ppCompressionLaw (r := r) A.quantizer)
  let roundLaw := ppRoundLaw (n := n) (r := r) A
  let leftProd := fun z : (Fin k → PPRoundNoise n r Ξ) ×
      PPRoundNoise n r Ξ => (z.1, rest z.2)
  let rightProd := fun z : (Fin k → PPRoundNoise n r Ξ) ×
      PPRoundNoise n r Ξ => branchRound z.2
  let nonrefreshSq := fun path : ℕ → PPRoundNoise n r Ξ =>
    let residual := (run k path).g - globalGradient A.problem (run k path).x
    let xNext := (run (k + 1) path).x
    let delta := globalGradient A.problem xNext -
      globalGradient A.problem (run k path).x
    let innovation := average (fun j : Fin r.1 =>
      A.quantizer.apply
          (localGradientDifference A.problem ((path k).2.1 j) xNext
            (run k path).x) ((path k).2.2 j) - delta)
    ‖residual + innovation‖ ^ 2
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hpastBlock : Measurable pastBlock := by
    dsimp [pastBlock]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  have hrest : Measurable rest := measurable_snd
  have hbranchRound : Measurable branchRound := measurable_fst
  have hZ : Measurable Z := hpastBlock.prodMk hcurrent
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hpastBlock.aemeasurable
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  have hZlaw : Measure.map Z P = prefixLaw.prod roundLaw := by
    simpa [Z, pastBlock, current, prefixLaw, roundLaw, P, ppPathLaw,
      SOptLib.iidStreamLaw] using
      (infinitePi_prefix_current_map_eq_prod
        (fun _ : ℕ => ppRoundLaw (n := n) (r := r) A) k)
  have hround : ProbabilityTheory.IndepFun rest branchRound roundLaw := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [roundLaw, ppRoundLaw, restLaw, rest, branchRound] using h
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (prefixLaw.prod roundLaw) :=
    indepFun_prod_left_adjoin_of_indepFun prefixLaw roundLaw rest branchRound
      hrest hbranchRound hround
  have hleftProd : Measurable leftProd :=
    measurable_fst.prodMk (hrest.comp measurable_snd)
  have hrightProd : Measurable rightProd :=
    hbranchRound.comp measurable_snd
  have hpull : ProbabilityTheory.IndepFun joined branch P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hpastBlock.prodMk (hrest.comp hcurrent)).aemeasurable)
      ((hbranchRound.comp hcurrent).aemeasurable)).2
    calc
      Measure.map (fun path => (joined path, branch path)) P =
          Measure.map (fun z => (leftProd z, rightProd z)) (Measure.map Z P) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleftProd.prodMk hrightProd
            · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (prefixLaw.prod roundLaw) := by rw [hZlaw]
      _ = (Measure.map leftProd (prefixLaw.prod roundLaw)).prod
          (Measure.map rightProd (prefixLaw.prod roundLaw)) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleftProd.aemeasurable hrightProd.aemeasurable).1 hprod
      _ = (Measure.map joined P).prod (Measure.map branch P) := by
        rw [show Measure.map leftProd (prefixLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            Measure.map leftProd (prefixLaw.prod roundLaw) =
                Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (prefixLaw.prod roundLaw) =
            Measure.map branch P by
          calc
            Measure.map rightProd (prefixLaw.prod roundLaw) =
                Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map branch P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  have hjoined_comap : Measurable[MeasurableSpace.comap joined inferInstance]
      joined := measurable_iff_comap_le.mpr le_rfl
  have hpast_meas : Measurable[MeasurableSpace.comap joined inferInstance]
      pastBlock := measurable_fst.comp hjoined_comap
  have hrest_meas : Measurable[MeasurableSpace.comap joined inferInstance]
      restPath := by
    simpa [joined, restPath] using (measurable_snd.comp hjoined_comap)
  have hstrict_le : (⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
      MeasurableSpace.comap joined inferInstance := by
    refine iSup_le fun j => ?_
    exact ((measurable_pi_apply j).comp hpast_meas).comap_le
  have hstate : Measurable[MeasurableSpace.comap joined inferInstance]
      (run k) :=
    (ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth k).mono
      hstrict_le le_rfl
  have hx : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => (run k path).x) := (measurable_state_x d).comp hstate
  have hxNext : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => (run (k + 1) path).x) := by
    simpa [run, ppProcess, ppRun_succ, ppStep] using
      (measurable_primalStep A.stepSize).comp hstate
  have hresidual : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => (run k path).g - globalGradient A.problem (run k path).x) :=
    ((measurable_state_g d).comp hstate).sub
      ((measurable_gradient (globalObjective A.problem)).comp hx)
  have hdelta : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => globalGradient A.problem (run (k + 1) path).x -
        globalGradient A.problem (run k path).x) :=
    ((measurable_gradient (globalObjective A.problem)).comp hxNext).sub
      ((measurable_gradient (globalObjective A.problem)).comp hx)
  have hquantized : ∀ j : Fin r.1,
      Measurable[MeasurableSpace.comap joined inferInstance]
        (fun path => A.quantizer.apply
          (localGradientDifference A.problem ((path k).2.1 j)
            (run (k + 1) path).x (run k path).x) ((path k).2.2 j)) := by
    intro j
    have hc : Measurable[MeasurableSpace.comap joined inferInstance]
        (fun path : ℕ → PPRoundNoise n r Ξ => (path k).2.1 j) :=
      (measurable_pi_apply j).comp (measurable_fst.comp hrest_meas)
    have hq : Measurable[MeasurableSpace.comap joined inferInstance]
        (fun path : ℕ → PPRoundNoise n r Ξ => (path k).2.2 j) :=
      (measurable_pi_apply j).comp (measurable_snd.comp hrest_meas)
    have hsel := pp_selected_localGradient_joint_measurable A.problem
    have hdiff := (hsel.comp (hc.prodMk hxNext)).sub
      (hsel.comp (hc.prodMk hx))
    exact A.quantizer.measurable_apply_uncurry.comp (hdiff.prodMk hq)
  have havg : Measurable[MeasurableSpace.comap joined inferInstance]
      (fun path => average (fun j : Fin r.1 =>
        A.quantizer.apply
            (localGradientDifference A.problem ((path k).2.1 j)
              (run (k + 1) path).x (run k path).x) ((path k).2.2 j) -
          (globalGradient A.problem (run (k + 1) path).x -
            globalGradient A.problem (run k path).x))) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ
      (fun j _ => (hquantized j).sub hdelta)).const_smul
        ((Fintype.card (Fin r.1) : ℝ)⁻¹)
  have hsq : Measurable[MeasurableSpace.comap joined inferInstance]
      nonrefreshSq := by
    dsimp [nonrefreshSq]
    have hsum := hresidual.add havg
    exact (continuous_norm.measurable.comp hsum).pow_const 2
  have hjoined_indep : ProbabilityTheory.Indep
      (MeasurableSpace.comap joined inferInstance)
      (MeasurableSpace.comap branch inferInstance) P := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpull
  have h := indepFun_of_measurable_left_of_indep_comap hsq hjoined_indep
  simpa [nonrefreshSq, branch, P, run] using h

/-- The generated PP process remains square-integrable at every time. -/
theorem pp_process_l2_invariant
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    ∀ t,
      Integrable (fun path => ‖(ppProcess (r := r) A x0 t path).x - x0‖ ^ 2)
        (ppPathLaw (r := r) A) ∧
      Integrable (fun path => ‖(ppProcess (r := r) A x0 t path).g‖ ^ 2)
        (ppPathLaw (r := r) A) ∧
      EstimatorErrorMomentWellDefined A.problem (ppProcess (r := r) A x0)
        (ppPathLaw (r := r) A) t ∧
      StepMomentWellDefined (ppProcess (r := r) A x0)
        (ppPathLaw (r := r) A) t := by
  classical
  let run := ppProcess (r := r) A x0
  let law := ppPathLaw (r := r) A
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate_meas : ∀ t, Measurable (run t) := by
    intro t
    have hs := ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth t
    have hle : (⨆ j : Fin t, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    exact hs.mono hle le_rfl
  have hx_meas : ∀ t, AEStronglyMeasurable (fun path => (run t path).x) law := by
    intro t
    exact ((measurable_state_x d).comp (hstate_meas t)).aestronglyMeasurable
  have hg_meas : ∀ t, AEStronglyMeasurable (fun path => (run t path).g) law := by
    intro t
    exact ((measurable_state_g d).comp (hstate_meas t)).aestronglyMeasurable
  have hglobal_grad_l2 : ∀ t,
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) law →
      Integrable (fun path => ‖globalGradient A.problem (run t path).x‖ ^ 2) law := by
    intro t hx
    have hGlobal := GlobalSmoothness_from_Assumption_1_2 A.problem Llocal hSmooth
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient A.problem) (rootMeanSquare Llocal)
        (fun path => (run t path).x) (hx_meas t)
    · simpa [norm_sub_rev] using hx
    · intro x y
      exact hGlobal.2 y x
  intro t
  induction t with
  | zero =>
      have hx0 : Integrable (fun path => ‖(run 0 path).x - x0‖ ^ 2) law := by
        have heq : (fun path => ‖(run 0 path).x - x0‖ ^ 2) =
            (fun _ => (0 : ℝ)) := by
          funext path
          change ‖x0 - x0‖ ^ 2 = 0
          simp
        rw [heq]
        exact integrable_const (c := (0 : ℝ))
      have hg0 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) law := by
        convert integrable_const (μ := law)
          (c := ‖globalGradient A.problem x0‖ ^ 2) using 1
      have herr0 : EstimatorErrorMomentWellDefined A.problem run law 0 := by
        rw [EstimatorErrorMomentWellDefined]
        convert integrable_const (μ := law) (c := (0 : ℝ)) using 1
        funext path
        simp [run, ppProcess, ppRun, SOptLib.recursiveIterateProcess,
          ppInitialState]
      have hstep0 : StepMomentWellDefined run law 0 := by
        rw [StepMomentWellDefined]
        convert integrable_const (μ := law)
          (c := ‖(-(A.stepSize : ℝ)) • globalGradient A.problem x0‖ ^ 2) using 1
        funext path
        change ‖(x0 - (A.stepSize : ℝ) • globalGradient A.problem x0) - x0‖ ^ 2 = _
        congr 2
        rw [neg_smul]
        abel
      exact ⟨hx0, hg0, herr0, hstep0⟩
  | succ t ih =>
      have hx_succ : Integrable
          (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
        have h := integrable_sq_norm_sub_smul_sub_const_of_l2
          (fun path => (run t path).x) (fun path => (run t path).g)
          x0 (A.stepSize : ℝ) (hx_meas t) (hg_meas t) ih.1 ih.2.1
        simpa [run, ppProcess, ppRun_succ, ppStep, primalStep_eq] using h
      have hnon := pp_generated_nonrefresh_branch_moments
        (r := r) A x0 Llocal ω hSmooth hQuantizer t ih.2.2.1 ih.2.2.2
      let residual := fun path : ℕ → PPRoundNoise n r Ξ =>
        (run t path).g - globalGradient A.problem (run t path).x
      let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
        let xNext := (run (t + 1) path).x
        let x := (run t path).x
        let delta := globalGradient A.problem xNext - globalGradient A.problem x
        average (fun j : Fin r.1 =>
          A.quantizer.apply
              (localGradientDifference A.problem ((path t).2.1 j) xNext x)
              ((path t).2.2 j) - delta)
      let nonrefreshSq := fun path => ‖residual path + innovation path‖ ^ 2
      change Integrable nonrefreshSq law ∧ _ at hnon
      let refreshSet : Set (ℕ → PPRoundNoise n r Ξ) :=
        {path | (path t).1 = true}
      have hrefreshSet : MeasurableSet refreshSet := by
        dsimp [refreshSet]
        exact ((measurable_fst.comp (measurable_pi_apply t))
          (measurableSet_singleton true))
      have hnextErr : EstimatorErrorMomentWellDefined A.problem run law (t + 1) := by
        have hpiece := Integrable.piecewise hrefreshSet
          (integrable_const (μ := law) (c := (0 : ℝ))).integrableOn
          hnon.1.integrableOn
        rw [EstimatorErrorMomentWellDefined]
        convert hpiece using 1
        funext path
        rw [pp_next_residual_eq_if_refresh A x0 Llocal hSmooth t path]
        cases hb : (path t).1 <;>
          simp [refreshSet, Set.piecewise, hb, nonrefreshSq, residual, innovation, run]
      have hgrad_succ := hglobal_grad_l2 (t + 1) hx_succ
      have hnextResidualMeas : AEStronglyMeasurable
          (fun path => (run (t + 1) path).g -
            globalGradient A.problem (run (t + 1) path).x) law :=
        (((measurable_state_g d).comp (hstate_meas (t + 1))).sub
          ((measurable_gradient (globalObjective A.problem)).comp
            ((measurable_state_x d).comp (hstate_meas (t + 1))))).aestronglyMeasurable
      have hg_succ : Integrable (fun path => ‖(run (t + 1) path).g‖ ^ 2) law := by
        have hadd := integrable_sq_norm_add hnextResidualMeas
          ((measurable_gradient (globalObjective A.problem)).comp
            ((measurable_state_x d).comp (hstate_meas (t + 1))) |>.aestronglyMeasurable)
          hnextErr hgrad_succ
        convert hadd using 1
        funext path
        change ‖(run (t + 1) path).g‖ ^ 2 =
          ‖((run (t + 1) path).g - globalGradient A.problem (run (t + 1) path).x) +
            globalGradient A.problem (run (t + 1) path).x‖ ^ 2
        congr 2
        abel
      have hstep_succ : StepMomentWellDefined run law (t + 1) := by
        have hscaled := integrable_sq_norm_const_smul
          (-(A.stepSize : ℝ)) hg_succ
        simpa [StepMomentWellDefined, run, ppProcess, ppRun_succ, ppStep,
          primalStep_eq] using hscaled
      exact ⟨hx_succ, hg_succ, hnextErr, hstep_succ⟩

/-- `book/MARINA/MARINA.json#/key_lemmas/8`, Eq. (59). -/
theorem PP_estimator_recurrence_59
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r) (k : ℕ) :
    EstimatorErrorMomentWellDefined A.problem (ppProcess (r := r) A x0)
        (ppPathLaw (r := r) A) (k + 1) ∧
    EstimatorErrorMomentWellDefined A.problem (ppProcess (r := r) A x0)
        (ppPathLaw (r := r) A) k ∧
    StepMomentWellDefined (ppProcess (r := r) A x0)
        (ppPathLaw (r := r) A) k ∧
    estimatorErrorMoment A.problem (ppProcess (r := r) A x0)
        (ppPathLaw (r := r) A) (k + 1) ≤
      (1 - A.refreshProbability) * (1 + ω) *
          (rootMeanSquare Llocal) ^ 2 / r.1 *
          stepMoment (ppProcess (r := r) A x0) (ppPathLaw (r := r) A) k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment A.problem (ppProcess (r := r) A x0)
            (ppPathLaw (r := r) A) k := by
  classical
  let run := ppProcess (r := r) A x0
  let law := ppPathLaw (r := r) A
  let residual := fun path : ℕ → PPRoundNoise n r Ξ =>
    (run k path).g - globalGradient A.problem (run k path).x
  let innovation := fun path : ℕ → PPRoundNoise n r Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    let delta := globalGradient A.problem xNext - globalGradient A.problem x
    average (fun j : Fin r.1 =>
      A.quantizer.apply
          (localGradientDifference A.problem ((path k).2.1 j) xNext x)
          ((path k).2.2 j) - delta)
  let nonrefreshSq := fun path => ‖residual path + innovation path‖ ^ 2
  let branch := fun path : ℕ → PPRoundNoise n r Ξ => (path k).1
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hInvK := pp_process_l2_invariant
    (r := r) A x0 Llocal ω hSmooth hQuantizer k
  have hInvSucc := pp_process_l2_invariant
    (r := r) A x0 Llocal ω hSmooth hQuantizer (k + 1)
  have hnon := pp_generated_nonrefresh_branch_moments
    (r := r) A x0 Llocal ω hSmooth hQuantizer k hInvK.2.2.1 hInvK.2.2.2
  change Integrable nonrefreshSq law ∧
      (∫ path, nonrefreshSq path ∂law) ≤
        estimatorErrorMoment A.problem run law k +
          ((1 + ω) * (rootMeanSquare Llocal) ^ 2 / r.1) *
            stepMoment run law k at hnon
  have hindep : ProbabilityTheory.IndepFun nonrefreshSq branch law := by
    simpa [nonrefreshSq, residual, innovation, branch, run, law] using
      pp_nonrefresh_square_indep_refresh
        (r := r) A x0 Llocal hSmooth k
  have hbranchMeas : Measurable branch := by
    dsimp [branch]
    fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    calc
      Measure.map branch law = Measure.map Prod.fst
          (Measure.map (fun path : ℕ → PPRoundNoise n r Ξ => path k) law) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact measurable_fst
        · exact measurable_pi_apply k
      _ = Measure.map Prod.fst (ppRoundLaw A) := by
        rw [show Measure.map
            (fun path : ℕ → PPRoundNoise n r Ξ => path k) law =
            ppRoundLaw A by
          simpa [law, ppPathLaw] using
            SOptLib.iidStreamLaw_map_eval
              (ppRoundLaw (n := n) (r := r) A) k]
      _ = refreshLaw A.refreshProbability A.refresh_admissible := by
        unfold ppRoundLaw
        rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  have hfalseMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({false} : Set Bool) = 1 - A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
    simp only [PMF.bernoulli_apply, Bool.cond_false]
    let pNN : NNReal :=
      ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
    have hpNN : pNN ≤ (1 : NNReal) := by
      exact_mod_cast A.refresh_admissible.2
    change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
    rw [NNReal.coe_sub hpNN]
    rfl
  let phi : ℝ → Bool → ℝ := fun z b => if b = false then z else 0
  let budget : ℝ → ℝ := fun z => (1 - A.refreshProbability) * z
  have hgateInt : Integrable
      (fun path => phi (nonrefreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranchMeas (measurableSet_singleton false)
    have hp := Integrable.piecewise hs hnon.1.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phi, Set.piecewise] using hp
  have hbudgetInt : Integrable (fun path => budget (nonrefreshSq path)) law := by
    simpa [budget] using hnon.1.const_mul (1 - A.refreshProbability)
  have hgate :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law)
      (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := nonrefreshSq) (Y := branch) (φ := phi) (B := budget)
      (by exact (show Measurable (Function.uncurry phi) by
        dsimp [phi, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton false)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budget by dsimp [budget]; fun_prop).aestronglyMeasurable)
      hnon.1.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hindep hbranchLaw hgateInt hbudgetInt
      (fun z => by
        rw [MeasureTheory.integral_fintype]
        · simp [Fintype.sum_bool, phi, budget, hfalseMass]
        · exact Integrable.of_finite)
  have hnextEq : estimatorErrorMoment A.problem run law (k + 1) =
      ∫ path, phi (nonrefreshSq path) (branch path) ∂law := by
    unfold estimatorErrorMoment
    apply integral_congr_ae
    filter_upwards [] with path
    rw [pp_next_residual_eq_if_refresh A x0 Llocal hSmooth k path]
    cases hb : branch path <;>
      simp [hb, branch, phi, nonrefreshSq, residual, innovation, run]
  refine ⟨hInvSucc.2.2.1, hInvK.2.2.1, hInvK.2.2.2, ?_⟩
  change estimatorErrorMoment A.problem run law (k + 1) ≤ _
  rw [hnextEq]
  calc
    (∫ path, phi (nonrefreshSq path) (branch path) ∂law) ≤
        ∫ path, budget (nonrefreshSq path) ∂law := hgate
    _ = (1 - A.refreshProbability) *
        (∫ path, nonrefreshSq path ∂law) := by
      simp [budget, MeasureTheory.integral_const_mul]
    _ ≤ (1 - A.refreshProbability) *
        (estimatorErrorMoment A.problem run law k +
          ((1 + ω) * (rootMeanSquare Llocal) ^ 2 / r.1) *
            stepMoment run law k) := by
      exact mul_le_mul_of_nonneg_left hnon.2
        (sub_nonneg.mpr A.refresh_admissible.2)
    _ = (1 - A.refreshProbability) * (1 + ω) *
          (rootMeanSquare Llocal) ^ 2 / r.1 * stepMoment run law k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment A.problem run law k := by ring

/-! ## Plain MARINA analytic infrastructure -/

/-- The Algorithm 1 transition is jointly measurable in the previous state
and the current refresh/compressor round. -/
theorem marinaStep_round_joint_measurable
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) :
    Measurable (fun p : State d × BasicRoundNoise n Ξ =>
      marinaStep A (basicDriverOfNoise p.2) p.1) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  have hxNext : Measurable (fun p : State d × BasicRoundNoise n Ξ =>
      primalStep A.stepSize p.1) :=
    (measurable_primalStep A.stepSize).comp measurable_fst
  have hx : Measurable (fun p : State d × BasicRoundNoise n Ξ => p.1.x) :=
    (measurable_state_x d).comp measurable_fst
  have hcompression (i : Worker n) : Measurable
      (fun p : State d × BasicRoundNoise n Ξ => p.2.2 i) := by
    fun_prop
  have hdiff (i : Worker n) : Measurable
      (fun p : State d × BasicRoundNoise n Ξ =>
        localGradientDifference A.problem i
          (primalStep A.stepSize p.1) p.1.x) := by
    unfold localGradientDifference
    exact ((measurable_localGradient A.problem i).comp hxNext).sub
      ((measurable_localGradient A.problem i).comp hx)
  have hquantized (i : Worker n) : Measurable
      (fun p : State d × BasicRoundNoise n Ξ =>
        A.quantizer.apply
          (localGradientDifference A.problem i
            (primalStep A.stepSize p.1) p.1.x)
          (p.2.2 i)) :=
    A.quantizer.measurable_apply_uncurry.comp
      ((hdiff i).prodMk (hcompression i))
  have havg : Measurable
      (fun p : State d × BasicRoundNoise n Ξ =>
        average (fun i : Worker n =>
          A.quantizer.apply
            (localGradientDifference A.problem i
              (primalStep A.stepSize p.1) p.1.x)
            (p.2.2 i))) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ
      (fun i _ => hquantized i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
  have hnonrefresh : Measurable
      (fun p : State d × BasicRoundNoise n Ξ => p.1.g +
        average (fun i : Worker n =>
          A.quantizer.apply
            (localGradientDifference A.problem i
              (primalStep A.stepSize p.1) p.1.x)
            (p.2.2 i))) :=
    ((measurable_state_g d).comp measurable_fst).add havg
  have hrefresh : Measurable
      (fun p : State d × BasicRoundNoise n Ξ =>
        globalGradient A.problem (primalStep A.stepSize p.1)) :=
    (measurable_gradient (globalObjective A.problem)).comp hxNext
  have hrefreshSet : MeasurableSet
      {p : State d × BasicRoundNoise n Ξ | p.2.1 = true} :=
    (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
  have hg : Measurable (fun p : State d × BasicRoundNoise n Ξ =>
      if p.2.1 then globalGradient A.problem (primalStep A.stepSize p.1)
      else p.1.g + average (fun i : Worker n =>
        A.quantizer.apply
          (localGradientDifference A.problem i
            (primalStep A.stepSize p.1) p.1.x)
          (p.2.2 i))) :=
    Measurable.ite hrefreshSet hrefresh hnonrefresh
  have hgStep : Measurable (fun p : State d × BasicRoundNoise n Ξ =>
      (marinaStep A (basicDriverOfNoise p.2) p.1).g) := by
    convert hg using 1
    funext p
    simpa [basicDriverOfNoise] using
      MARINA_estimator_update A (basicDriverOfNoise p.2) p.1 Llocal hSmooth
  exact (measurable_state_mk d).comp (hxNext.prodMk hgStep)

/-- The generated Algorithm 1 state at time `k` is measurable from the strict
prefix of refresh/compressor rounds. -/
theorem marinaProcess_strictPast_measurable
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance]
      (marinaProcess A x0 k) := by
  let past : Unit → MeasurableSpace (ℕ → BasicRoundNoise n Ξ) :=
    fun _ => ⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance
  let driver : ℕ → (ℕ → BasicRoundNoise n Ξ) → BasicRoundNoise n Ξ :=
    fun t path => path t
  let step : ℕ → State d → BasicRoundNoise n Ξ → State d :=
    fun _ s z => marinaStep A (basicDriverOfNoise z) s
  apply SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := past) (process := marinaProcess A x0)
      (driver := driver) (step := step) (k := ()) (N := k)
  · exact measurable_const
  · intro t ht _hprocess
    rw [measurable_iff_comap_le]
    exact le_iSup_of_le ⟨t, Nat.lt_of_succ_le ht⟩ (by rfl)
  · intro _t _ht
    exact marinaStep_round_joint_measurable A Llocal hSmooth
  · intro t _ht
    rfl
  · exact le_rfl

/-- The strict-past Algorithm 1 query is independent of the current complete
worker-compressor row, whose law is the canonical worker product law. -/
theorem marina_strictPast_query_indep_compression_row
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    let law := basicPathLaw A
    let run := marinaProcess A x0
    let query := fun path : ℕ → BasicRoundNoise n Ξ =>
      (primalStep A.stepSize (run k path), (run k path).x)
    let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
    ProbabilityTheory.IndepFun query row law ∧
      Measure.map row law = workerCompressionLaw A.quantizer := by
  let law := basicPathLaw A
  let run := marinaProcess A x0
  let query := fun path : ℕ → BasicRoundNoise n Ξ =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let pastPrefix := fun path : ℕ → BasicRoundNoise n Ξ =>
    fun j : Fin k => path j.1
  let current := fun path : ℕ → BasicRoundNoise n Ξ => path k
  let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
  let prefixLaw := Measure.map pastPrefix law
  let roundLaw := basicRoundLaw A
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hpastPrefix : Measurable pastPrefix := by
    dsimp [pastPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hcurrent : Measurable current := measurable_pi_apply k
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hpastPrefix.aemeasurable
  have hpast_current : ProbabilityTheory.IndepFun pastPrefix current law := by
    refine indepFun_of_map_prod_eq_prod_laws
      (P := law) (Z := fun path => (pastPrefix path, current path))
      (mu := prefixLaw) (nu := roundLaw) ?_ ?_
    · exact (hpastPrefix.prodMk hcurrent).aemeasurable
    · simpa [pastPrefix, current, prefixLaw, roundLaw, law, basicPathLaw,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => basicRoundLaw A) k)
  have hpast_row : ProbabilityTheory.IndepFun pastPrefix row law := by
    have hcomp := hpast_current.comp measurable_id measurable_snd
    simpa [current, row, Function.comp_def] using hcomp
  have hstate : Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance]
      (run k) := by
    simpa [run] using marinaProcess_strictPast_measurable
      A x0 Llocal hSmooth k
  have hquery : Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance]
      query := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp hstate).prodMk
      ((measurable_state_x d).comp hstate)
  have hstrict_le : (⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
      MeasurableSpace.comap pastPrefix inferInstance := by
    refine iSup_le fun j => ?_
    have hpast_comap : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        pastPrefix := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply j).comp hpast_comap).comap_le
  have hcomap : ProbabilityTheory.Indep
      (MeasurableSpace.comap pastPrefix inferInstance)
      (MeasurableSpace.comap row inferInstance) law := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpast_row
  have hindep : ProbabilityTheory.IndepFun query row law :=
    indepFun_of_measurable_left_of_indep_comap hquery
      (ProbabilityTheory.indep_of_indep_of_le_left hcomap hstrict_le)
  have hrowLaw : Measure.map row law = workerCompressionLaw A.quantizer := by
    calc
      Measure.map row law =
          Measure.map Prod.snd (Measure.map current law) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact measurable_snd
        · exact hcurrent
      _ = Measure.map Prod.snd roundLaw := by
        rw [show Measure.map current law = roundLaw by
          simpa [current, law, roundLaw] using basicPathLaw_round_marginal A k]
      _ = workerCompressionLaw A.quantizer := by
        dsimp [roundLaw]
        unfold basicRoundLaw
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  exact ⟨hindep, hrowLaw⟩

/-- At a fixed pair of iterates, the average of the independent centered
worker-compressor errors has the exact `ω / n` second-moment budget. -/
theorem marina_fixed_compression_average_moments
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (xNext x : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let rowLaw := workerCompressionLaw (n := n) A.quantizer
    let innovation := fun row : Worker n → Ξ =>
      average (fun i : Worker n =>
        A.quantizer.apply
            (localGradientDifference A.problem i xNext x) (row i) -
          localGradientDifference A.problem i xNext x)
    Integrable innovation rowLaw ∧
      (∫ row, innovation row ∂rowLaw) = 0 ∧
      Integrable (fun row => ‖innovation row‖ ^ 2) rowLaw ∧
      (∫ row, ‖innovation row‖ ^ 2 ∂rowLaw) ≤
        (ω * (rootMeanSquare Llocal) ^ 2 / n.1) * ‖xNext - x‖ ^ 2 := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let v := fun i : Worker n =>
    localGradientDifference A.problem i xNext x
  let eps := fun i : Worker n => fun row : Worker n → Ξ =>
    A.quantizer.apply (v i) (row i) - v i
  let innovation := fun row : Worker n → Ξ =>
    average (fun i : Worker n => eps i row)
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  have hcoord (i : Worker n) :
      Measure.map (fun row : Worker n → Ξ => row i) rowLaw =
        A.quantizer.law := by
    simpa [rowLaw] using
      workerCompressionLaw_component_marginal A.quantizer i
  have heps_meas (i : Worker n) : Measurable (eps i) := by
    dsimp [eps]
    exact (A.quantizer.measurable_apply_uncurry.comp
      (measurable_const.prodMk (measurable_pi_apply i))).sub measurable_const
  have heps_int (i : Worker n) : Integrable (eps i) rowLaw := by
    have hbase : Integrable
        (fun ξ => A.quantizer.apply (v i) ξ - v i) A.quantizer.law :=
      (hQuantizer.2 (v i)).1.sub (integrable_const (c := v i))
    have hmap : Integrable
        (fun ξ => A.quantizer.apply (v i) ξ - v i)
        (Measure.map (fun row : Worker n → Ξ => row i) rowLaw) := by
      rwa [hcoord i]
    have hcomp := (MeasureTheory.integrable_map_measure
      (show AEStronglyMeasurable
          (fun ξ => A.quantizer.apply (v i) ξ - v i)
          (Measure.map (fun row : Worker n → Ξ => row i) rowLaw) by
        rw [hcoord i]
        exact hbase.aestronglyMeasurable)
      (measurable_pi_apply i).aemeasurable).mp hmap
    simpa [eps, Function.comp_def] using hcomp
  have heps_sq (i : Worker n) : Integrable
      (fun row => ‖eps i row‖ ^ 2) rowLaw := by
    have hmap : Integrable
        (fun ξ => ‖A.quantizer.apply (v i) ξ - v i‖ ^ 2)
        (Measure.map (fun row : Worker n → Ξ => row i) rowLaw) := by
      rw [hcoord i]
      exact quantizer_error_sq_integrable hQuantizer (v i)
    have hcomp := (MeasureTheory.integrable_map_measure
      (show AEStronglyMeasurable
          (fun ξ => ‖A.quantizer.apply (v i) ξ - v i‖ ^ 2)
          (Measure.map (fun row : Worker n → Ξ => row i) rowLaw) by
        rw [hcoord i]
        exact (quantizer_error_sq_integrable hQuantizer
          (v i)).aestronglyMeasurable)
      (measurable_pi_apply i).aemeasurable).mp hmap
    simpa [eps, Function.comp_def] using hcomp
  have heps_mean (i : Worker n) : (∫ row, eps i row ∂rowLaw) = 0 := by
    have hm : AEStronglyMeasurable
        (fun ξ => A.quantizer.apply (v i) ξ - v i)
        (Measure.map (fun row : Worker n → Ξ => row i) rowLaw) := by
      rw [hcoord i]
      exact ((hQuantizer.2 (v i)).1.sub
        (integrable_const (c := v i))).aestronglyMeasurable
    have hmap := MeasureTheory.integral_map
      (μ := rowLaw) (φ := fun row : Worker n → Ξ => row i)
      (measurable_pi_apply i).aemeasurable hm
    rw [hcoord i] at hmap
    calc
      (∫ row, eps i row ∂rowLaw) =
          ∫ ξ, A.quantizer.apply (v i) ξ - v i ∂A.quantizer.law := hmap.symm
      _ = 0 := by
        rw [integral_sub (hQuantizer.2 (v i)).1
          (integrable_const (c := v i)), (hQuantizer.2 (v i)).2.2.1]
        simp [integral_const, probReal_univ]
  have heps_bound (i : Worker n) :
      (∫ row, ‖eps i row‖ ^ 2 ∂rowLaw) ≤ ω * ‖v i‖ ^ 2 := by
    have hm : AEStronglyMeasurable
        (fun ξ => ‖A.quantizer.apply (v i) ξ - v i‖ ^ 2)
        (Measure.map (fun row : Worker n → Ξ => row i) rowLaw) := by
      rw [hcoord i]
      exact (quantizer_error_sq_integrable hQuantizer (v i)).aestronglyMeasurable
    have hmap := MeasureTheory.integral_map
      (μ := rowLaw) (φ := fun row : Worker n → Ξ => row i)
      (measurable_pi_apply i).aemeasurable hm
    rw [hcoord i] at hmap
    exact hmap.symm.trans_le (hQuantizer.2 (v i)).2.2.2
  have hiIndep : ProbabilityTheory.iIndepFun
      (fun i (row : Worker n → Ξ) => row i) rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    exact ProbabilityTheory.iIndepFun_infinitePi
      (fun _ : Worker n => measurable_id)
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ row, ⟪eps i row, eps j row⟫_ℝ ∂rowLaw) = 0 := by
    intro i j hij
    have hkernel : AEStronglyMeasurable
        (fun p : Ξ × Ξ =>
          ⟪A.quantizer.apply (v i) p.1 - v i,
            A.quantizer.apply (v j) p.2 - v j⟫_ℝ)
        ((Measure.map (fun row : Worker n → Ξ => row i) rowLaw).prod
          A.quantizer.law) := by
      have hi : AEStronglyMeasurable
          (fun ξ => A.quantizer.apply (v i) ξ - v i)
          (Measure.map (fun row : Worker n → Ξ => row i) rowLaw) := by
        rw [hcoord i]
        exact ((hQuantizer.2 (v i)).1.sub
          (integrable_const (c := v i))).aestronglyMeasurable
      have hj : AEStronglyMeasurable
          (fun ξ => A.quantizer.apply (v j) ξ - v j) A.quantizer.law :=
        ((hQuantizer.2 (v j)).1.sub
          (integrable_const (c := v j))).aestronglyMeasurable
      exact hi.comp_fst.inner hj.comp_snd
    have hinner : Integrable (fun row => ⟪eps i row, eps j row⟫_ℝ) rowLaw :=
      integrable_inner_of_integrable_sq_norm
        (heps_int i).aestronglyMeasurable (heps_int j).aestronglyMeasurable
        (heps_sq i) (heps_sq j)
    have hfixed : ∀ a : Ξ,
        (∫ z, ⟪A.quantizer.apply (v i) a - v i,
          A.quantizer.apply (v j) z - v j⟫_ℝ ∂A.quantizer.law) = 0 := by
      intro a
      have hjint : Integrable
          (fun z => A.quantizer.apply (v j) z - v j) A.quantizer.law :=
        (hQuantizer.2 (v j)).1.sub (integrable_const (c := v j))
      have hlin := ContinuousLinearMap.integral_comp_comm
        (L := (innerSL ℝ) (A.quantizer.apply (v i) a - v i)) hjint
      calc
        (∫ z, ⟪A.quantizer.apply (v i) a - v i,
            A.quantizer.apply (v j) z - v j⟫_ℝ ∂A.quantizer.law) =
            ⟪A.quantizer.apply (v i) a - v i,
              ∫ z, A.quantizer.apply (v j) z - v j
                ∂A.quantizer.law⟫_ℝ := hlin
        _ = 0 := by
          rw [integral_sub (hQuantizer.2 (v j)).1
            (integrable_const (c := v j)), (hQuantizer.2 (v j)).2.2.1]
          simp [integral_const, probReal_univ]
    exact integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := rowLaw) (ν := A.quantizer.law)
      (φ := fun a z =>
        ⟪A.quantizer.apply (v i) a - v i,
          A.quantizer.apply (v j) z - v j⟫_ℝ)
      (X := fun row : Worker n → Ξ => row i)
      (Y := fun row : Worker n → Ξ => row j)
      hkernel (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable (hiIndep.indepFun hij)
      (hcoord j) hinner hfixed
  have havg_int : Integrable innovation rowLaw := by
    dsimp [innovation, average, SOptLib.finiteUniformAverage]
    simpa [Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ => heps_int i)).smul ((Fintype.card (Worker n) : ℝ)⁻¹)
  have havg_mean : (∫ row, innovation row ∂rowLaw) = 0 := by
    dsimp [innovation, average, SOptLib.finiteUniformAverage]
    rw [integral_smul,
      MeasureTheory.integral_finset_sum Finset.univ
        (fun i _ => heps_int i)]
    simp [heps_mean]
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    rowLaw (Finset.univ : Finset (Worker n)) eps
      (fun i _ => (heps_int i).aestronglyMeasurable)
      (fun i _ => heps_sq i)
      (fun i _ j _ hij => hcross hij)
  have havg_sq : Integrable (fun row => ‖innovation row‖ ^ 2) rowLaw := by
    apply integrable_sq_norm_centeredMiniBatchAverage rowLaw
      (Finset.univ : Finset (Worker n)) n.1 eps innovation
    · intro i _hi
      exact (heps_int i).aestronglyMeasurable
    · intro i _hi
      exact heps_sq i
    · funext row
      simp [innovation, average, SOptLib.finiteUniformAverage_def,
        Fintype.card_fin]
  have hmean_nonneg : 0 ≤ meanSquare Llocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hrms : (rootMeanSquare Llocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (Llocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_nonneg]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
  refine ⟨by simpa [innovation, eps, v] using havg_int,
    by simpa [innovation, eps, v] using havg_mean,
    by simpa [innovation, eps, v] using havg_sq, ?_⟩
  calc
    (∫ row, ‖innovation row‖ ^ 2 ∂rowLaw) =
        ((n.1 : ℝ)⁻¹) ^ 2 *
          ∫ row, ‖Finset.sum Finset.univ (fun i => eps i row)‖ ^ 2
            ∂rowLaw := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with row
      dsimp [innovation, average, SOptLib.finiteUniformAverage]
      simp only [Fintype.card_fin]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n, ∫ row, ‖eps i row‖ ^ 2 ∂rowLaw := by rw [hsum]
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n, ω * ‖v i‖ ^ 2 := by
      gcongr with i
      exact heps_bound i
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n,
          ω * ((Llocal i) ^ 2 * ‖xNext - x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i _hi
      have hlip : ‖v i‖ ≤ Llocal i * ‖xNext - x‖ := by
        simpa [v, localGradientDifference] using hSmooth.2 i xNext x
      have hsquare : ‖v i‖ ^ 2 ≤
          (Llocal i) ^ 2 * ‖xNext - x‖ ^ 2 := by
        rw [← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _)
          (le_trans (norm_nonneg _) hlip)).2 hlip
      exact mul_le_mul_of_nonneg_left hsquare (le_of_lt hQuantizer.1)
    _ = (ω * (rootMeanSquare Llocal) ^ 2 / n.1) *
        ‖xNext - x‖ ^ 2 := by
      rw [← Finset.mul_sum]
      rw [show (∑ i : Worker n,
          (Llocal i) ^ 2 * ‖xNext - x‖ ^ 2) =
          (∑ i : Worker n, (Llocal i) ^ 2) * ‖xNext - x‖ ^ 2 by
        rw [Finset.sum_mul]]
      rw [hrms]
      field_simp [hn]

/-- The generated Algorithm 1 centered compressor average inherits the fixed
query `ω L² / n` displacement budget. -/
theorem marina_generated_innovation_second_moment
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ)
    (hStep : StepMomentWellDefined (marinaProcess A x0)
      (basicPathLaw A) k) :
    let run := marinaProcess A x0
    let law := basicPathLaw A
    let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
      let xNext := (run (k + 1) path).x
      let x := (run k path).x
      average (fun i : Worker n =>
        A.quantizer.apply
            (localGradientDifference A.problem i xNext x) ((path k).2 i) -
          localGradientDifference A.problem i xNext x)
    Integrable innovation law ∧
      Integrable (fun path => ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (ω * (rootMeanSquare Llocal) ^ 2 / n.1) *
          stepMoment run law k := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let run := marinaProcess A x0
  let law := basicPathLaw A
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let query := fun path : ℕ → BasicRoundNoise n Ξ =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
  let rowAverage := fun z : Point d × Point d =>
    fun samples : Worker n → Ξ =>
      average (fun i : Worker n =>
        A.quantizer.apply
            (localGradientDifference A.problem i z.1 z.2) (samples i) -
          localGradientDifference A.problem i z.1 z.2)
  let phi := fun z : Point d × Point d =>
    fun samples : Worker n → Ξ => ‖rowAverage z samples‖ ^ 2
  let coeff := ω * (rootMeanSquare Llocal) ^ 2 / n.1
  let B := fun z : Point d × Point d => coeff * ‖z.1 - z.2‖ ^ 2
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hquery : Measurable query := by
    have hs := marinaProcess_strictPast_measurable
      A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    have hsFull := hs.mono hle le_rfl
    exact ((measurable_primalStep A.stepSize).comp hsFull).prodMk
      ((measurable_state_x d).comp hsFull)
  have hrow : Measurable row := by
    dsimp [row]
    fun_prop
  have hfresh := marina_strictPast_query_indep_compression_row
    A x0 Llocal hSmooth k
  change ProbabilityTheory.IndepFun query row law ∧
      Measure.map row law = rowLaw at hfresh
  have hrowAverage : Measurable (Function.uncurry rowAverage) := by
    unfold rowAverage average SOptLib.finiteUniformAverage
    have hterm (i : Worker n) : Measurable
        (fun p : (Point d × Point d) × (Worker n → Ξ) =>
          A.quantizer.apply
              (localGradientDifference A.problem i p.1.1 p.1.2) (p.2 i) -
            localGradientDifference A.problem i p.1.1 p.1.2) := by
      have hdiff : Measurable
          (fun p : (Point d × Point d) × (Worker n → Ξ) =>
            localGradientDifference A.problem i p.1.1 p.1.2) := by
        unfold localGradientDifference
        exact ((measurable_localGradient A.problem i).comp
          (measurable_fst.comp measurable_fst)).sub
          ((measurable_localGradient A.problem i).comp
            (measurable_snd.comp measurable_fst))
      have hsample : Measurable
          (fun p : (Point d × Point d) × (Worker n → Ξ) => p.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      exact (A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk hsample)).sub hdiff
    exact (Finset.measurable_sum Finset.univ
      (fun i _ => hterm i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
  have hphi : Measurable (Function.uncurry phi) := by
    dsimp [phi, Function.uncurry]
    exact hrowAverage.norm.pow_const 2
  have hB : Measurable B := by
    dsimp [B]
    fun_prop
  have hfixed : ∀ z : Point d × Point d,
      Integrable (rowAverage z) rowLaw ∧
      (∫ samples, rowAverage z samples ∂rowLaw) = 0 ∧
      Integrable (phi z) rowLaw ∧
      (∫ samples, phi z samples ∂rowLaw) ≤ B z := by
    intro z
    have hz := marina_fixed_compression_average_moments
      A z.1 z.2 Llocal ω hSmooth hQuantizer
    exact ⟨by simpa [rowAverage, rowLaw] using hz.1,
      by simpa [rowAverage, rowLaw] using hz.2.1,
      by simpa [rowAverage, rowLaw, phi] using hz.2.2.1,
      by simpa [rowAverage, rowLaw, phi, B, coeff] using hz.2.2.2⟩
  have hBcomp : Integrable (fun path => B (query path)) law := by
    have hs := hStep.const_mul coeff
    simpa [B, query, coeff, run, law, StepMomentWellDefined, marinaProcess,
      marinaRun_succ, marinaStep] using hs
  have hphiComp : Integrable (fun path => phi (query path) (row path)) law := by
    apply integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
      (P := law) (ν := rowLaw) (X := query) (Y := row) (B := B)
    · exact hphi.aestronglyMeasurable
    · exact hB.aestronglyMeasurable
    · exact hquery.aemeasurable
    · exact hrow.aemeasurable
    · exact hfresh.1
    · exact hfresh.2
    · intro z samples
      exact sq_nonneg _
    · intro z
      exact (hfixed z).2.2.1
    · exact hBcomp
    · intro z
      exact (hfixed z).2.2.2
  have hbound :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := rowLaw) (X := query) (Y := row)
      (φ := phi) (B := B) hphi.aestronglyMeasurable hB.aestronglyMeasurable
      hquery.aemeasurable hrow.aemeasurable hfresh.1 hfresh.2
      hphiComp hBcomp (fun z => (hfixed z).2.2.2)
  let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    average (fun i : Worker n =>
      A.quantizer.apply
          (localGradientDifference A.problem i xNext x) ((path k).2 i) -
        localGradientDifference A.problem i xNext x)
  have hinnovation_eq : innovation =
      fun path => rowAverage (query path) (row path) := by
    funext path
    simp only [innovation, rowAverage, query, row]
    rfl
  have havgMeas : AEStronglyMeasurable innovation law := by
    rw [hinnovation_eq]
    exact (hrowAverage.comp (hquery.prodMk hrow)).aestronglyMeasurable
  have hsq : Integrable (fun path => ‖innovation path‖ ^ 2) law := by
    simpa [hinnovation_eq, phi] using hphiComp
  have hvec := integrable_of_integrable_norm_sq havgMeas hsq
  refine ⟨hvec, hsq, ?_⟩
  calc
    (∫ path, ‖innovation path‖ ^ 2 ∂law) =
        ∫ path, phi (query path) (row path) ∂law := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path => by rw [hinnovation_eq]
    _ ≤ ∫ path, B (query path) ∂law := hbound
    _ = coeff * stepMoment run law k := by
      unfold B query stepMoment
      rw [integral_const_mul]
      rfl

/-- Pathwise Algorithm 1 residual decomposition into an exact-refresh zero
branch and the old residual plus the centered compressor average. -/
theorem marina_next_residual_eq_if_refresh
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ)
    (path : ℕ → BasicRoundNoise n Ξ) :
    let run := marinaProcess A x0
    let residual := (run k path).g - globalGradient A.problem (run k path).x
    let xNext := (run (k + 1) path).x
    let innovation := average (fun i : Worker n =>
      A.quantizer.apply
          (localGradientDifference A.problem i xNext (run k path).x)
          ((path k).2 i) -
        localGradientDifference A.problem i xNext (run k path).x)
    (run (k + 1) path).g - globalGradient A.problem xNext =
      if (path k).1 then 0 else residual + innovation := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let run := marinaProcess A x0
  let s := run k path
  let xNext := (run (k + 1) path).x
  let delta := fun i : Worker n =>
    localGradientDifference A.problem i xNext s.x
  let q := fun i : Worker n =>
    A.quantizer.apply (delta i) ((path k).2 i)
  let innovation := average (fun i : Worker n => q i - delta i)
  have hxNext : xNext = primalStep A.stepSize s := by rfl
  have hupdate := MARINA_estimator_update A
    (basicDriverOfNoise (path k)) s Llocal hSmooth
  have hdeltaAvg : average delta =
      globalGradient A.problem xNext - globalGradient A.problem s.x := by
    rw [globalGradient_eq_averageLocalGradient A.problem hSmooth.1 xNext,
      globalGradient_eq_averageLocalGradient A.problem hSmooth.1 s.x]
    unfold delta localGradientDifference averageLocalGradient average
      SOptLib.finiteUniformAverage
    rw [Finset.sum_sub_distrib, smul_sub]
  have hinnovation : innovation = average q - average delta := by
    unfold innovation average SOptLib.finiteUniformAverage
    rw [Finset.sum_sub_distrib, smul_sub]
  dsimp [basicDriverOfNoise] at hupdate
  rw [← hxNext] at hupdate
  cases hb : (path k).1 with
  | false =>
      simp only [hb, Bool.false_eq_true, if_false]
      simp [hb] at hupdate
      have hg : (run (k + 1) path).g = s.g + average q := by
        change (marinaStep A (basicDriverOfNoise (path k)) s).g = _
        simp only [basicDriverOfNoise]
        rw [hb]
        simpa [q, delta, basicDriverOfNoise] using hupdate
      rw [hg]
      change s.g + average q - globalGradient A.problem xNext =
        (s.g - globalGradient A.problem s.x) + innovation
      rw [hinnovation, hdeltaAvg]
      abel
  | true =>
      simp only [hb, if_true]
      simp [hb] at hupdate
      have hg : (run (k + 1) path).g =
          globalGradient A.problem xNext := by
        change (marinaStep A (basicDriverOfNoise (path k)) s).g = _
        simp only [basicDriverOfNoise]
        rw [hb]
        simpa [basicDriverOfNoise] using hupdate
      rw [hg]
      exact sub_self _

/-- The generated plain-MARINA process stays in `L²` at every time. -/
theorem marina_process_l2_invariant
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    ∀ t,
      Integrable (fun path => ‖(marinaProcess A x0 t path).x - x0‖ ^ 2)
        (basicPathLaw A) ∧
      Integrable (fun path => ‖(marinaProcess A x0 t path).g‖ ^ 2)
        (basicPathLaw A) ∧
      EstimatorErrorMomentWellDefined A.problem (marinaProcess A x0)
        (basicPathLaw A) t ∧
      StepMomentWellDefined (marinaProcess A x0) (basicPathLaw A) t := by
  classical
  let run := marinaProcess A x0
  let law := basicPathLaw A
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate_meas : ∀ t, Measurable (run t) := by
    intro t
    have hs := marinaProcess_strictPast_measurable
      A x0 Llocal hSmooth t
    have hle : (⨆ j : Fin t, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    exact hs.mono hle le_rfl
  have hx_meas : ∀ t, AEStronglyMeasurable
      (fun path => (run t path).x) law := by
    intro t
    exact ((measurable_state_x d).comp (hstate_meas t)).aestronglyMeasurable
  have hg_meas : ∀ t, AEStronglyMeasurable
      (fun path => (run t path).g) law := by
    intro t
    exact ((measurable_state_g d).comp (hstate_meas t)).aestronglyMeasurable
  have hglobal_grad_l2 : ∀ t,
      Integrable (fun path => ‖(run t path).x - x0‖ ^ 2) law →
      Integrable (fun path =>
        ‖globalGradient A.problem (run t path).x‖ ^ 2) law := by
    intro t hx
    have hGlobal := GlobalSmoothness_from_Assumption_1_2
      A.problem Llocal hSmooth
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient A.problem) (rootMeanSquare Llocal)
        (fun path => (run t path).x) (hx_meas t)
    · simpa [norm_sub_rev] using hx
    · intro x y
      exact hGlobal.2 y x
  intro t
  induction t with
  | zero =>
      have hx0 : Integrable
          (fun path => ‖(run 0 path).x - x0‖ ^ 2) law := by
        convert integrable_const (μ := law) (c := (0 : ℝ)) using 1
        funext path
        simp [run, marinaProcess, marinaRun, SOptLib.recursiveIterateProcess,
          marinaInitialState]
      have hg0 : Integrable (fun path => ‖(run 0 path).g‖ ^ 2) law := by
        convert integrable_const (μ := law)
          (c := ‖globalGradient A.problem x0‖ ^ 2) using 1
      have herr0 : EstimatorErrorMomentWellDefined A.problem run law 0 := by
        rw [EstimatorErrorMomentWellDefined]
        convert integrable_const (μ := law) (c := (0 : ℝ)) using 1
        funext path
        simp [run, marinaProcess, marinaRun, SOptLib.recursiveIterateProcess,
          marinaInitialState]
      have hstep0 : StepMomentWellDefined run law 0 := by
        rw [StepMomentWellDefined]
        convert integrable_const (μ := law)
          (c := ‖(-(A.stepSize : ℝ)) • globalGradient A.problem x0‖ ^ 2) using 1
        funext path
        change ‖(x0 - (A.stepSize : ℝ) • globalGradient A.problem x0) - x0‖ ^ 2 = _
        congr 2
        rw [neg_smul]
        abel
      exact ⟨hx0, hg0, herr0, hstep0⟩
  | succ t ih =>
      have hx_succ : Integrable
          (fun path => ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
        have h := integrable_sq_norm_sub_smul_sub_const_of_l2
          (fun path => (run t path).x) (fun path => (run t path).g)
          x0 (A.stepSize : ℝ) (hx_meas t) (hg_meas t) ih.1 ih.2.1
        simpa [run, marinaProcess, marinaRun_succ, marinaStep,
          primalStep_eq] using h
      have hgen := marina_generated_innovation_second_moment
        A x0 Llocal ω hSmooth hQuantizer t ih.2.2.2
      let residual := fun path : ℕ → BasicRoundNoise n Ξ =>
        (run t path).g - globalGradient A.problem (run t path).x
      let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
        let xNext := (run (t + 1) path).x
        let x := (run t path).x
        average (fun i : Worker n =>
          A.quantizer.apply
              (localGradientDifference A.problem i xNext x) ((path t).2 i) -
            localGradientDifference A.problem i xNext x)
      change Integrable innovation law ∧
          Integrable (fun path => ‖innovation path‖ ^ 2) law ∧ _ at hgen
      have hres_meas : AEStronglyMeasurable residual law := by
        dsimp [residual]
        exact (((measurable_state_g d).comp (hstate_meas t)).sub
          ((measurable_gradient (globalObjective A.problem)).comp
            ((measurable_state_x d).comp
              (hstate_meas t)))).aestronglyMeasurable
      have hnon : Integrable
          (fun path => ‖residual path + innovation path‖ ^ 2) law :=
        integrable_sq_norm_add hres_meas hgen.1.aestronglyMeasurable
          ih.2.2.1 hgen.2.1
      let refreshSet : Set (ℕ → BasicRoundNoise n Ξ) :=
        {path | (path t).1 = true}
      have hrefreshSet : MeasurableSet refreshSet := by
        dsimp [refreshSet]
        exact ((measurable_fst.comp (measurable_pi_apply t))
          (measurableSet_singleton true))
      have hnextErr : EstimatorErrorMomentWellDefined A.problem run law (t + 1) := by
        have hpiece := Integrable.piecewise hrefreshSet
          (integrable_const (μ := law) (c := (0 : ℝ))).integrableOn
          hnon.integrableOn
        rw [EstimatorErrorMomentWellDefined]
        convert hpiece using 1
        funext path
        rw [marina_next_residual_eq_if_refresh
          A x0 Llocal hSmooth t path]
        cases hb : (path t).1 <;>
          simp [refreshSet, Set.piecewise, hb, residual, innovation, run]
      have hgrad_succ := hglobal_grad_l2 (t + 1) hx_succ
      have hnextResidualMeas : AEStronglyMeasurable
          (fun path => (run (t + 1) path).g -
            globalGradient A.problem (run (t + 1) path).x) law :=
        (((measurable_state_g d).comp (hstate_meas (t + 1))).sub
          ((measurable_gradient (globalObjective A.problem)).comp
            ((measurable_state_x d).comp
              (hstate_meas (t + 1))))).aestronglyMeasurable
      have hg_succ : Integrable
          (fun path => ‖(run (t + 1) path).g‖ ^ 2) law := by
        have hadd := integrable_sq_norm_add hnextResidualMeas
          ((measurable_gradient (globalObjective A.problem)).comp
            ((measurable_state_x d).comp
              (hstate_meas (t + 1))) |>.aestronglyMeasurable)
          hnextErr hgrad_succ
        convert hadd using 1
        funext path
        change ‖(run (t + 1) path).g‖ ^ 2 =
          ‖((run (t + 1) path).g -
            globalGradient A.problem (run (t + 1) path).x) +
            globalGradient A.problem (run (t + 1) path).x‖ ^ 2
        congr 2
        abel
      have hstep_succ : StepMomentWellDefined run law (t + 1) := by
        have hscaled := integrable_sq_norm_const_smul
          (-(A.stepSize : ℝ)) hg_succ
        simpa [StepMomentWellDefined, run, marinaProcess, marinaRun_succ,
          marinaStep, primalStep_eq] using hscaled
      exact ⟨hx_succ, hg_succ, hnextErr, hstep_succ⟩

/-- The strict-past Algorithm 1 state is independent of the current complete
worker-compressor row. -/
theorem marina_strictPast_state_indep_compression_row
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    let law := basicPathLaw A
    let run := marinaProcess A x0
    let state := fun path : ℕ → BasicRoundNoise n Ξ => run k path
    let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
    ProbabilityTheory.IndepFun state row law ∧
      Measure.map row law = workerCompressionLaw A.quantizer := by
  let law := basicPathLaw A
  let run := marinaProcess A x0
  let state := fun path : ℕ → BasicRoundNoise n Ξ => run k path
  let query := fun path : ℕ → BasicRoundNoise n Ξ =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
  have hqueryFresh := marina_strictPast_query_indep_compression_row
    A x0 Llocal hSmooth k
  change ProbabilityTheory.IndepFun query row law ∧
      Measure.map row law = workerCompressionLaw A.quantizer at hqueryFresh
  have hstate : Measurable[⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance]
      state := by
    simpa [state, run] using marinaProcess_strictPast_measurable
      A x0 Llocal hSmooth k
  let pastPrefix := fun path : ℕ → BasicRoundNoise n Ξ =>
    fun j : Fin k => path j.1
  have hpastPrefix : Measurable pastPrefix := by
    dsimp [pastPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hstrict_le : (⨆ j : Fin k, MeasurableSpace.comap
      (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
      MeasurableSpace.comap pastPrefix inferInstance := by
    refine iSup_le fun j => ?_
    have hpast_comap : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        pastPrefix := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply j).comp hpast_comap).comap_le
  have hstatePast : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
      state := hstate.mono hstrict_le le_rfl
  have hqueryPast : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
      query := by
    dsimp [query, state]
    exact ((measurable_primalStep A.stepSize).comp hstatePast).prodMk
      ((measurable_state_x d).comp hstatePast)
  have hcomapQuery : MeasurableSpace.comap query inferInstance ≤
      MeasurableSpace.comap pastPrefix inferInstance := hqueryPast.comap_le
  have hcomapState : MeasurableSpace.comap state inferInstance ≤
      MeasurableSpace.comap pastPrefix inferInstance := hstatePast.comap_le
  have hqueryIndep : ProbabilityTheory.Indep
      (MeasurableSpace.comap query inferInstance)
      (MeasurableSpace.comap row inferInstance) law := by
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hqueryFresh.1
  have hpastIndep : ProbabilityTheory.Indep
      (MeasurableSpace.comap pastPrefix inferInstance)
      (MeasurableSpace.comap row inferInstance) law := by
    -- Reconstruct the larger strict-past independence used to derive the
    -- query-level statement above.
    let current := fun path : ℕ → BasicRoundNoise n Ξ => path k
    let prefixLaw := Measure.map pastPrefix law
    let roundLaw := basicRoundLaw A
    letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
    haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
      unfold workerCompressionLaw
      infer_instance
    haveI : IsProbabilityMeasure
        (refreshLaw A.refreshProbability A.refresh_admissible) := by
      unfold refreshLaw
      infer_instance
    haveI : IsProbabilityMeasure roundLaw := by
      dsimp [roundLaw]
      unfold basicRoundLaw
      infer_instance
    haveI : IsProbabilityMeasure law := by
      dsimp [law]
      unfold basicPathLaw SOptLib.iidStreamLaw
      infer_instance
    haveI : IsProbabilityMeasure prefixLaw :=
      Measure.isProbabilityMeasure_map hpastPrefix.aemeasurable
    have hpastCurrent : ProbabilityTheory.IndepFun pastPrefix current law := by
      refine indepFun_of_map_prod_eq_prod_laws
        (P := law) (Z := fun path => (pastPrefix path, current path))
        (mu := prefixLaw) (nu := roundLaw) ?_ ?_
      · exact (hpastPrefix.prodMk (measurable_pi_apply k)).aemeasurable
      · simpa [pastPrefix, current, prefixLaw, roundLaw, law, basicPathLaw,
          SOptLib.iidStreamLaw] using
          (infinitePi_prefix_current_map_eq_prod
            (fun _ : ℕ => basicRoundLaw A) k)
    have hpastRow : ProbabilityTheory.IndepFun pastPrefix row law := by
      have hcomp := hpastCurrent.comp measurable_id measurable_snd
      simpa [current, row, Function.comp_def] using hcomp
    simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpastRow
  have hstateIndep : ProbabilityTheory.Indep
      (MeasurableSpace.comap state inferInstance)
      (MeasurableSpace.comap row inferInstance) law :=
    ProbabilityTheory.indep_of_indep_of_le_left hpastIndep hcomapState
  exact ⟨by simpa [ProbabilityTheory.IndepFun_iff_Indep] using hstateIndep,
    hqueryFresh.2⟩

/-- The old estimator residual is orthogonal in expectation to the current
centered worker-compressor average. -/
theorem marina_generated_residual_innovation_cross_eq_zero
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ) :
    let run := marinaProcess A x0
    let law := basicPathLaw A
    let residual := fun path : ℕ → BasicRoundNoise n Ξ =>
      (run k path).g - globalGradient A.problem (run k path).x
    let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
      let xNext := (run (k + 1) path).x
      let x := (run k path).x
      average (fun i : Worker n =>
        A.quantizer.apply
            (localGradientDifference A.problem i xNext x) ((path k).2 i) -
          localGradientDifference A.problem i xNext x)
    (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let run := marinaProcess A x0
  let law := basicPathLaw A
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let state := fun path : ℕ → BasicRoundNoise n Ξ => run k path
  let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
  let rowInnovation := fun s : State d => fun samples : Worker n → Ξ =>
    let xNext := primalStep A.stepSize s
    average (fun i : Worker n =>
      A.quantizer.apply
          (localGradientDifference A.problem i xNext s.x) (samples i) -
        localGradientDifference A.problem i xNext s.x)
  let direction := fun s : State d =>
    s.g - globalGradient A.problem s.x
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : Measurable state := by
    have hs := marinaProcess_strictPast_measurable
      A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    simpa [state, run] using hs.mono hle le_rfl
  have hrow : Measurable row := by dsimp [row]; fun_prop
  have hfresh := marina_strictPast_state_indep_compression_row
    A x0 Llocal hSmooth k
  change ProbabilityTheory.IndepFun state row law ∧
      Measure.map row law = rowLaw at hfresh
  have hrowInnovation : Measurable (Function.uncurry rowInnovation) := by
    unfold rowInnovation average SOptLib.finiteUniformAverage
    have hterm (i : Worker n) : Measurable
        (fun p : State d × (Worker n → Ξ) =>
          A.quantizer.apply
              (localGradientDifference A.problem i
                (primalStep A.stepSize p.1) p.1.x) (p.2 i) -
            localGradientDifference A.problem i
              (primalStep A.stepSize p.1) p.1.x) := by
      have hxnext : Measurable
          (fun p : State d × (Worker n → Ξ) =>
            primalStep A.stepSize p.1) :=
        (measurable_primalStep A.stepSize).comp measurable_fst
      have hx : Measurable
          (fun p : State d × (Worker n → Ξ) => p.1.x) :=
        (measurable_state_x d).comp measurable_fst
      have hdiff : Measurable
          (fun p : State d × (Worker n → Ξ) =>
            localGradientDifference A.problem i
              (primalStep A.stepSize p.1) p.1.x) := by
        unfold localGradientDifference
        exact ((measurable_localGradient A.problem i).comp hxnext).sub
          ((measurable_localGradient A.problem i).comp hx)
      have hsample : Measurable
          (fun p : State d × (Worker n → Ξ) => p.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      exact (A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk hsample)).sub hdiff
    exact (Finset.measurable_sum Finset.univ
      (fun i _ => hterm i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
  have hdirection : Measurable direction := by
    dsimp [direction]
    exact (measurable_state_g d).sub
      ((measurable_gradient (globalObjective A.problem)).comp
        (measurable_state_x d))
  have hfixed : ∀ s : State d,
      Integrable (rowInnovation s) rowLaw ∧
      (∫ samples, rowInnovation s samples ∂rowLaw) = 0 := by
    intro s
    have hs := marina_fixed_compression_average_moments A
      (primalStep A.stepSize s) s.x Llocal ω hSmooth hQuantizer
    exact ⟨by simpa [rowInnovation, rowLaw] using hs.1,
      by simpa [rowInnovation, rowLaw] using hs.2.1⟩
  have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
    law rowLaw state row rowInnovation direction hrowInnovation hdirection
      hstate hrow hfresh.1 hfresh.2 (fun s => (hfixed s).1)
      (fun s => (hfixed s).2)
  let residual := fun path : ℕ → BasicRoundNoise n Ξ =>
    (run k path).g - globalGradient A.problem (run k path).x
  let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    average (fun i : Worker n =>
      A.quantizer.apply
          (localGradientDifference A.problem i xNext x) ((path k).2 i) -
        localGradientDifference A.problem i xNext x)
  simpa [residual, innovation, rowInnovation, direction, state, row, run,
    marinaProcess, marinaRun_succ, marinaStep] using hzero

/-- The nonrefresh residual-plus-innovation square is integrable and obeys
the exact additive second-moment bound. -/
theorem marina_generated_nonrefresh_branch_moments
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined A.problem
      (marinaProcess A x0) (basicPathLaw A) k)
    (hStep : StepMomentWellDefined (marinaProcess A x0)
      (basicPathLaw A) k) :
    let run := marinaProcess A x0
    let law := basicPathLaw A
    let residual := fun path : ℕ → BasicRoundNoise n Ξ =>
      (run k path).g - globalGradient A.problem (run k path).x
    let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
      let xNext := (run (k + 1) path).x
      let x := (run k path).x
      average (fun i : Worker n =>
        A.quantizer.apply
            (localGradientDifference A.problem i xNext x) ((path k).2 i) -
          localGradientDifference A.problem i xNext x)
    Integrable (fun path => ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment A.problem run law k +
          (ω * (rootMeanSquare Llocal) ^ 2 / n.1) *
            stepMoment run law k := by
  let run := marinaProcess A x0
  let law := basicPathLaw A
  let residual := fun path : ℕ → BasicRoundNoise n Ξ =>
    (run k path).g - globalGradient A.problem (run k path).x
  let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    average (fun i : Worker n =>
      A.quantizer.apply
          (localGradientDifference A.problem i xNext x) ((path k).2 i) -
        localGradientDifference A.problem i xNext x)
  have hgen := marina_generated_innovation_second_moment
    A x0 Llocal ω hSmooth hQuantizer k hStep
  change Integrable innovation law ∧
      Integrable (fun path => ‖innovation path‖ ^ 2) law ∧ _ at hgen
  have hcross := marina_generated_residual_innovation_cross_eq_zero
    A x0 Llocal ω hSmooth hQuantizer k
  change (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 at hcross
  have hstate : Measurable (run k) := by
    have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    exact hs.mono hle le_rfl
  have hresMeas : AEStronglyMeasurable residual law := by
    dsimp [residual]
    exact (((measurable_state_g d).comp hstate).sub
      ((measurable_gradient (globalObjective A.problem)).comp
        ((measurable_state_x d).comp hstate))).aestronglyMeasurable
  have hinner : Integrable
      (fun path => ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresMeas hgen.1.aestronglyMeasurable
      hError hgen.2.1
  have hsum : Integrable
      (fun path => ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresMeas hgen.1.aestronglyMeasurable
      hError hgen.2.1
  refine ⟨hsum, ?_⟩
  calc
    (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          (∫ path, ‖innovation path‖ ^ 2 ∂law) +
          2 * (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) := by
      have hresSq : Integrable (fun path => ‖residual path‖ ^ 2) law := hError
      rw [show (fun path => ‖residual path + innovation path‖ ^ 2) =
          fun path => ‖residual path‖ ^ 2 + ‖innovation path‖ ^ 2 +
            2 * ⟪residual path, innovation path⟫_ℝ by
        funext path
        rw [norm_add_sq_real]
        ring]
      calc
        (∫ path, ‖residual path‖ ^ 2 + ‖innovation path‖ ^ 2 +
            2 * ⟪residual path, innovation path⟫_ℝ ∂law) =
          (∫ path, ‖residual path‖ ^ 2 + ‖innovation path‖ ^ 2 ∂law) +
            ∫ path, 2 * ⟪residual path, innovation path⟫_ℝ ∂law :=
              integral_add (hresSq.add hgen.2.1) (hinner.const_mul 2)
        _ = _ := by
          rw [integral_add hresSq hgen.2.1, integral_const_mul]
    _ = estimatorErrorMoment A.problem run law k +
        (∫ path, ‖innovation path‖ ^ 2 ∂law) := by
      rw [hcross]
      simp [estimatorErrorMoment, residual]
    _ ≤ estimatorErrorMoment A.problem run law k +
        (ω * (rootMeanSquare Llocal) ^ 2 / n.1) *
          stepMoment run law k := by linarith [hgen.2.2]

/-- The nonrefresh residual square, which depends on the strict-past state and
current compressor row, is independent of the current refresh coin. -/
theorem marina_nonrefresh_square_indep_refresh
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → BasicRoundNoise n Ξ =>
        let run := marinaProcess A x0
        let residual := (run k path).g -
          globalGradient A.problem (run k path).x
        let xNext := (run (k + 1) path).x
        let innovation := average (fun i : Worker n =>
          A.quantizer.apply
              (localGradientDifference A.problem i xNext (run k path).x)
              ((path k).2 i) -
            localGradientDifference A.problem i xNext (run k path).x)
        ‖residual + innovation‖ ^ 2)
      (fun path : ℕ → BasicRoundNoise n Ξ => (path k).1)
      (basicPathLaw A) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := basicPathLaw A
  let run := marinaProcess A x0
  let state := fun path : ℕ → BasicRoundNoise n Ξ => run k path
  let current := fun path : ℕ → BasicRoundNoise n Ξ => path k
  let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
  let branch := fun path : ℕ → BasicRoundNoise n Ξ => (path k).1
  let rest := fun z : BasicRoundNoise n Ξ => z.2
  let branchRound := fun z : BasicRoundNoise n Ξ => z.1
  let stateLaw := Measure.map state P
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let roundLaw := basicRoundLaw A
  let joined := fun path : ℕ → BasicRoundNoise n Ξ => (state path, row path)
  let Z := fun path : ℕ → BasicRoundNoise n Ξ => (state path, current path)
  let leftProd := fun z : State d × BasicRoundNoise n Ξ => (z.1, rest z.2)
  let rightProd := fun z : State d × BasicRoundNoise n Ξ => branchRound z.2
  let rowInnovation := fun s : State d => fun samples : Worker n → Ξ =>
    let xNext := primalStep A.stepSize s
    average (fun i : Worker n =>
      A.quantizer.apply
          (localGradientDifference A.problem i xNext s.x) (samples i) -
        localGradientDifference A.problem i xNext s.x)
  let nonrefreshKernel := fun z : State d × (Worker n → Ξ) =>
    ‖(z.1.g - globalGradient A.problem z.1.x) +
      rowInnovation z.1 z.2‖ ^ 2
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : Measurable state := by
    have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    simpa [state, run] using hs.mono hle le_rfl
  haveI : IsProbabilityMeasure stateLaw :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hcurrent : Measurable current := measurable_pi_apply k
  have hstateCurrent : ProbabilityTheory.IndepFun state current P := by
    let pastPrefix := fun path : ℕ → BasicRoundNoise n Ξ =>
      fun j : Fin k => path j.1
    let prefixLaw := Measure.map pastPrefix P
    have hpastPrefix : Measurable pastPrefix := by
      dsimp [pastPrefix]
      exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
    haveI : IsProbabilityMeasure prefixLaw :=
      Measure.isProbabilityMeasure_map hpastPrefix.aemeasurable
    have hpastCurrent : ProbabilityTheory.IndepFun pastPrefix current P := by
      refine indepFun_of_map_prod_eq_prod_laws
        (P := P) (Z := fun path => (pastPrefix path, current path))
        (mu := prefixLaw) (nu := roundLaw) ?_ ?_
      · exact (hpastPrefix.prodMk hcurrent).aemeasurable
      · simpa [pastPrefix, current, prefixLaw, roundLaw, P, basicPathLaw,
          SOptLib.iidStreamLaw] using
          (infinitePi_prefix_current_map_eq_prod
            (fun _ : ℕ => basicRoundLaw A) k)
    have hstrict : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        state := by
      have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
      have hstrict_le : (⨆ j : Fin k, MeasurableSpace.comap
          (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
          MeasurableSpace.comap pastPrefix inferInstance := by
        refine iSup_le fun j => ?_
        have hpast_comap : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
            pastPrefix := measurable_iff_comap_le.mpr le_rfl
        exact ((measurable_pi_apply j).comp hpast_comap).comap_le
      exact (by simpa [state, run] using hs.mono hstrict_le le_rfl)
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap pastPrefix inferInstance)
        (MeasurableSpace.comap current inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpastCurrent
    exact indepFun_of_measurable_left_of_indep_comap hstrict hcomap
  have hcurrentLaw : Measure.map current P = roundLaw := by
    simpa [current, P, roundLaw] using basicPathLaw_round_marginal A k
  have hZlaw : Measure.map Z P = stateLaw.prod roundLaw := by
    have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hstate.aemeasurable hcurrent.aemeasurable).1 hstateCurrent
    simpa [Z, stateLaw, hcurrentLaw] using hmap
  have hround : ProbabilityTheory.IndepFun rest branchRound roundLaw := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := rowLaw) measurable_id measurable_id).symm
    simpa [roundLaw, basicRoundLaw, rowLaw, rest, branchRound] using h
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (stateLaw.prod roundLaw) :=
    indepFun_prod_left_adjoin_of_indepFun stateLaw roundLaw rest branchRound
      measurable_snd measurable_fst hround
  have hleftProd : Measurable leftProd :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hrightProd : Measurable rightProd :=
    measurable_fst.comp measurable_snd
  have hZ : Measurable Z := hstate.prodMk hcurrent
  have hjoinedBranch : ProbabilityTheory.IndepFun joined branch P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hstate.prodMk ((measurable_snd.comp hcurrent))).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    calc
      Measure.map (fun path => (joined path, branch path)) P =
          Measure.map (fun z => (leftProd z, rightProd z))
            (Measure.map Z P) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact hleftProd.prodMk hrightProd
        · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (stateLaw.prod roundLaw) := by rw [hZlaw]
      _ = (Measure.map leftProd (stateLaw.prod roundLaw)).prod
          (Measure.map rightProd (stateLaw.prod roundLaw)) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleftProd.aemeasurable hrightProd.aemeasurable).1 hprod
      _ = (Measure.map joined P).prod (Measure.map branch P) := by
        rw [show Measure.map leftProd (stateLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            Measure.map leftProd (stateLaw.prod roundLaw) =
                Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (stateLaw.prod roundLaw) =
            Measure.map branch P by
          calc
            Measure.map rightProd (stateLaw.prod roundLaw) =
                Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map branch P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  have hrowInnovation : Measurable (Function.uncurry rowInnovation) := by
    unfold rowInnovation average SOptLib.finiteUniformAverage
    have hterm (i : Worker n) : Measurable
        (fun p : State d × (Worker n → Ξ) =>
          A.quantizer.apply
              (localGradientDifference A.problem i
                (primalStep A.stepSize p.1) p.1.x) (p.2 i) -
            localGradientDifference A.problem i
              (primalStep A.stepSize p.1) p.1.x) := by
      have hxnext : Measurable
          (fun p : State d × (Worker n → Ξ) =>
            primalStep A.stepSize p.1) :=
        (measurable_primalStep A.stepSize).comp measurable_fst
      have hx : Measurable
          (fun p : State d × (Worker n → Ξ) => p.1.x) :=
        (measurable_state_x d).comp measurable_fst
      have hdiff : Measurable
          (fun p : State d × (Worker n → Ξ) =>
            localGradientDifference A.problem i
              (primalStep A.stepSize p.1) p.1.x) := by
        unfold localGradientDifference
        exact ((measurable_localGradient A.problem i).comp hxnext).sub
          ((measurable_localGradient A.problem i).comp hx)
      have hsample : Measurable
          (fun p : State d × (Worker n → Ξ) => p.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      exact (A.quantizer.measurable_apply_uncurry.comp
        (hdiff.prodMk hsample)).sub hdiff
    exact (Finset.measurable_sum Finset.univ
      (fun i _ => hterm i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
  have hkernel : Measurable nonrefreshKernel := by
    have hres : Measurable
        (fun z : State d × (Worker n → Ξ) =>
          z.1.g - globalGradient A.problem z.1.x) :=
      ((measurable_state_g d).comp measurable_fst).sub
        ((measurable_gradient (globalObjective A.problem)).comp
          ((measurable_state_x d).comp measurable_fst))
    exact (continuous_norm.measurable.comp
      (hres.add hrowInnovation)).pow_const 2
  have hcomp := hjoinedBranch.comp hkernel measurable_id
  simpa [nonrefreshKernel, joined, branch, rowInnovation, state, row, run,
    marinaProcess, marinaRun_succ, marinaStep, Function.comp_def] using hcomp

/-- `book/MARINA/MARINA.json#/main_theorem/proof/7`, Eq. (21): the exact
plain-MARINA estimator-error recurrence. -/
theorem marina_estimator_recurrence_21
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) (k : ℕ) :
    EstimatorErrorMomentWellDefined A.problem (marinaProcess A x0)
        (basicPathLaw A) (k + 1) ∧
    EstimatorErrorMomentWellDefined A.problem (marinaProcess A x0)
        (basicPathLaw A) k ∧
    StepMomentWellDefined (marinaProcess A x0) (basicPathLaw A) k ∧
    estimatorErrorMoment A.problem (marinaProcess A x0)
        (basicPathLaw A) (k + 1) ≤
      ((1 - A.refreshProbability) * ω *
          (rootMeanSquare Llocal) ^ 2 / n.1) *
          stepMoment (marinaProcess A x0) (basicPathLaw A) k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment A.problem (marinaProcess A x0)
            (basicPathLaw A) k := by
  classical
  let run := marinaProcess A x0
  let law := basicPathLaw A
  let residual := fun path : ℕ → BasicRoundNoise n Ξ =>
    (run k path).g - globalGradient A.problem (run k path).x
  let innovation := fun path : ℕ → BasicRoundNoise n Ξ =>
    let xNext := (run (k + 1) path).x
    let x := (run k path).x
    average (fun i : Worker n =>
      A.quantizer.apply
          (localGradientDifference A.problem i xNext x) ((path k).2 i) -
        localGradientDifference A.problem i xNext x)
  let nonrefreshSq := fun path => ‖residual path + innovation path‖ ^ 2
  let branch := fun path : ℕ → BasicRoundNoise n Ξ => (path k).1
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hInvK := marina_process_l2_invariant
    A x0 Llocal ω hSmooth hQuantizer k
  have hInvSucc := marina_process_l2_invariant
    A x0 Llocal ω hSmooth hQuantizer (k + 1)
  have hnon := marina_generated_nonrefresh_branch_moments
    A x0 Llocal ω hSmooth hQuantizer k hInvK.2.2.1 hInvK.2.2.2
  change Integrable nonrefreshSq law ∧
      (∫ path, nonrefreshSq path ∂law) ≤
        estimatorErrorMoment A.problem run law k +
          (ω * (rootMeanSquare Llocal) ^ 2 / n.1) *
            stepMoment run law k at hnon
  have hindep : ProbabilityTheory.IndepFun nonrefreshSq branch law := by
    simpa [nonrefreshSq, residual, innovation, branch, run, law] using
      marina_nonrefresh_square_indep_refresh A x0 Llocal hSmooth k
  have hbranchMeas : Measurable branch := by
    dsimp [branch]
    fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law] using basicPathLaw_refresh_marginal A k
  have hfalseMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({false} : Set Bool) = 1 - A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
    simp only [PMF.bernoulli_apply, Bool.cond_false]
    let pNN : NNReal :=
      ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
    have hpNN : pNN ≤ (1 : NNReal) := by
      exact_mod_cast A.refresh_admissible.2
    change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
    rw [NNReal.coe_sub hpNN]
    rfl
  let phi : ℝ → Bool → ℝ := fun z b => if b = false then z else 0
  let budget : ℝ → ℝ := fun z => (1 - A.refreshProbability) * z
  have hgateInt : Integrable
      (fun path => phi (nonrefreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranchMeas (measurableSet_singleton false)
    have hp := Integrable.piecewise hs hnon.1.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phi, Set.piecewise] using hp
  have hbudgetInt : Integrable
      (fun path => budget (nonrefreshSq path)) law := by
    simpa [budget] using hnon.1.const_mul (1 - A.refreshProbability)
  have hgate :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law)
      (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := nonrefreshSq) (Y := branch) (φ := phi) (B := budget)
      (by exact (show Measurable (Function.uncurry phi) by
        dsimp [phi, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton false)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budget by dsimp [budget]; fun_prop).aestronglyMeasurable)
      hnon.1.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hindep hbranchLaw hgateInt hbudgetInt
      (fun z => by
        rw [MeasureTheory.integral_fintype]
        · simp [Fintype.sum_bool, phi, budget, hfalseMass]
        · exact Integrable.of_finite)
  have hnextEq : estimatorErrorMoment A.problem run law (k + 1) =
      ∫ path, phi (nonrefreshSq path) (branch path) ∂law := by
    unfold estimatorErrorMoment
    apply integral_congr_ae
    filter_upwards [] with path
    rw [marina_next_residual_eq_if_refresh
      A x0 Llocal hSmooth k path]
    cases hb : branch path <;>
      simp [hb, branch, phi, nonrefreshSq, residual, innovation, run]
  refine ⟨hInvSucc.2.2.1, hInvK.2.2.1, hInvK.2.2.2, ?_⟩
  change estimatorErrorMoment A.problem run law (k + 1) ≤ _
  rw [hnextEq]
  calc
    (∫ path, phi (nonrefreshSq path) (branch path) ∂law) ≤
        ∫ path, budget (nonrefreshSq path) ∂law := hgate
    _ = (1 - A.refreshProbability) *
        (∫ path, nonrefreshSq path ∂law) := by
      simp [budget, MeasureTheory.integral_const_mul]
    _ ≤ (1 - A.refreshProbability) *
        (estimatorErrorMoment A.problem run law k +
          (ω * (rootMeanSquare Llocal) ^ 2 / n.1) *
            stepMoment run law k) := by
      exact mul_le_mul_of_nonneg_left hnon.2
        (sub_nonneg.mpr A.refresh_admissible.2)
    _ = ((1 - A.refreshProbability) * ω *
          (rootMeanSquare Llocal) ^ 2 / n.1) *
          stepMoment run law k +
        (1 - A.refreshProbability) *
          estimatorErrorMoment A.problem run law k := by ring

/-- Eq. (16) makes the plain-MARINA displacement coefficient nonnegative. -/
theorem marina_nonconvex_stepsize_absorbs_displacement
    {n : Count} {γ L p ω : ℝ}
    (hγ : 0 < γ) (hp : RefreshProbabilityAdmissible p)
    (hω : 0 ≤ ω) (hL : 0 ≤ L)
    (hStep : MARINAStepsizeCondition γ L p ω n) :
    0 ≤ 1 / (2 * γ) - L / 2 -
      γ / (2 * p) * ((1 - p) * ω * L ^ 2 / n.1) := by
  let r : ℝ := (1 - p) * ω / (p * n.1)
  let q : ℝ := r * L ^ 2
  have hp_pos : 0 < p := hp.1
  have hn_pos : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hp.2) hω)
      (mul_nonneg hp_pos.le hn_pos.le)
  have hq_nonneg : 0 ≤ q := mul_nonneg hr_nonneg (sq_nonneg L)
  have hs_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hsqrt : Real.sqrt q = L * Real.sqrt r := by
    dsimp [q]
    rw [mul_comm, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hL]
  have hstep' : γ * (L + Real.sqrt q) ≤ 1 := by
    rw [hsqrt]
    calc
      γ * (L + L * Real.sqrt r) =
          γ * (L * (1 + Real.sqrt r)) := by ring
      _ ≤ 1 := by simpa [MARINAStepsizeCondition, r] using hStep
  have hγs_le_one : γ * Real.sqrt q ≤ 1 := by
    nlinarith
  have hγs_nonneg : 0 ≤ γ * Real.sqrt q :=
    mul_nonneg hγ.le hs_nonneg
  have hγs_budget :
      0 ≤ (γ * Real.sqrt q) * (1 - γ * Real.sqrt q) :=
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
      γ / (2 * p) * ((1 - p) * ω * L ^ 2 / n.1) = γ * q / 2 := by
    dsimp [q, r]
    field_simp [hp_ne, hn_ne]
  rw [hq_eq]
  have hscaled := mul_nonneg (show 0 ≤ (2 * γ)⁻¹ by positivity) hcore
  convert hscaled using 1 <;> field_simp [hγ_ne] <;> ring

/-- Eq. (23) supplies the three scalar coefficient facts used in the
plain-MARINA PŁ Lyapunov argument.  The square-root calculation is valid also
when the aggregate smoothness constant is zero. -/
theorem marina_pl_stepsize_coefficients
    {n : Count} {γ L p ω : ℝ} {μ : PositivePLParameter}
    (hγ : 0 < γ) (hp : RefreshProbabilityAdmissible p)
    (hω : 0 ≤ ω) (hL : 0 ≤ L)
    (hStep : MARINAPLStepsizeCondition γ L p ω μ n) :
    0 ≤ 1 / (2 * γ) - L / 2 -
        γ / p * ((1 - p) * ω * L ^ 2 / n.1) ∧
      γ / 2 + γ / p * (1 - p) ≤ (1 - γ * μ) * (γ / p) ∧
      0 ≤ 1 - γ * μ := by
  let q : ℝ := 2 * (1 - p) * ω / (p * n.1)
  have hp_pos : 0 < p := hp.1
  have hn_pos : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp.2)) hω)
      (mul_nonneg hp_pos.le hn_pos.le)
  have hs_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hstep_sqrt : γ * (L * (1 + Real.sqrt q)) ≤ 1 := by
    simpa [MARINAPLStepsizeCondition, q] using hStep.1
  have hu_nonneg : 0 ≤ γ * L := mul_nonneg hγ.le hL
  have hut_le_one : γ * L * Real.sqrt q ≤ 1 := by
    nlinarith
  have hut_nonneg : 0 ≤ γ * L * Real.sqrt q :=
    mul_nonneg hu_nonneg hs_nonneg
  have hbudget :
      0 ≤ (γ * L * Real.sqrt q) * (1 - γ * L * Real.sqrt q) :=
    mul_nonneg hut_nonneg (sub_nonneg.mpr hut_le_one)
  have hγq : γ ^ 2 * L ^ 2 * q = (γ * L * Real.sqrt q) ^ 2 := by
    calc
      γ ^ 2 * L ^ 2 * q = γ ^ 2 * L ^ 2 * (Real.sqrt q) ^ 2 := by
        rw [hs_sq]
      _ = (γ * L * Real.sqrt q) ^ 2 := by ring
  have hcore : 0 ≤ 1 - γ * L - γ ^ 2 * L ^ 2 * q := by
    rw [hγq]
    nlinarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hn_ne : (n.1 : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  have hq_eq :
      γ / p * ((1 - p) * ω * L ^ 2 / n.1) =
        γ * L ^ 2 * q / 2 := by
    dsimp [q]
    field_simp [hp_ne, hn_ne]
    <;> ring
  have hdisplacement :
      0 ≤ 1 / (2 * γ) - L / 2 -
        γ / p * ((1 - p) * ω * L ^ 2 / n.1) := by
    rw [hq_eq]
    have hscaled := mul_nonneg (show 0 ≤ (2 * γ)⁻¹ by positivity) hcore
    convert hscaled using 1 <;> field_simp [hγ_ne] <;> ring
  have hmu : 2 * γ * (μ : ℝ) ≤ p := by
    simpa [MARINAPLStepsizeCondition] using hStep.2
  have herror :
      γ / 2 + γ / p * (1 - p) ≤ (1 - γ * μ) * (γ / p) := by
    field_simp [hp_ne]
    nlinarith
  have hcontraction : 0 ≤ 1 - γ * μ := by
    nlinarith [hp.2]
  exact ⟨hdisplacement, herror, hcontraction⟩

/-! ## Source-facing principal convergence heads -/

/-- `book/MARINA/MARINA.json#/main_theorem`, Theorem C.1 / Eq. (17).
No Lean-only measurability or integrability premise is added to the paper head. -/
theorem Theorem_C1_MARINA_nonconvex {d n K : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : MARINAStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω n) :
    Integrable (fun z =>
        ‖globalGradient A.problem
          (uniformOutput (K := K) (marinaProcess A x0) z)‖ ^ 2)
        (uniformOutputExperimentLaw (basicPathLaw A) K) ∧
      (∫ z,
          ‖globalGradient A.problem
            (uniformOutput (K := K) (marinaProcess A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (basicPathLaw A) K) ≤
        2 * (globalObjective A.problem x0 - fStar) / (A.stepSize * K.1) := by
  have hEq21 (k : ℕ) :=
    marina_estimator_recurrence_21
      A x0 Llocal ω hSmooth hQuantizer k
  classical
  let P := A.problem
  let run := marinaProcess A x0
  let law := basicPathLaw A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) * ω * L ^ 2 / n.1
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hState (k : ℕ) : Measurable (run k) := by
    have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    exact hs.mono hle le_rfl
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hState k)).aestronglyMeasurable
  have hInv (k : ℕ) :
      Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law k ∧
      StepMomentWellDefined run law k := by
    simpa [P, run, law] using
      (marina_process_l2_invariant
        A x0 Llocal ω hSmooth hQuantizer k)
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [norm_sub_rev] using (hInv k).1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp
        ((measurable_state_x d).comp (hState k))).aestronglyMeasurable
    · simpa [norm_sub_rev] using (hInv k).1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law] using
      (hEq21 k).2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [StepMomentWellDefined, run, law] using (hEq21 k).2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, marinaProcess, marinaRun_succ,
        marinaStep, primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k := by
    have hrec := (hEq21 k).2.2.2
    simpa [E, D, a, P, run, law, p, L] using hrec
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact marina_nonconvex_stepsize_absorbs_displacement
      hγ A.refresh_admissible hQuantizer.1.le hL hStep
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hrec0 :
        E (k + 1) ≤ a * D k + (1 - p) * E k + p * 0 := by
      simpa using hRecurrence k
    simpa [Φ] using
      (online_vr_nonconvex_lyapunov_step
        (V := 0) F E G D k hγ hp hDnonneg hCoeff (hDescent k) hrec0)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤ Φ 0 - Φ N := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        nlinarith
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient A.problem x0 -
        globalGradient A.problem x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable
        (fun _ : ℕ → BasicRoundNoise n Ξ => fStar) law := integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    simp only [mul_zero, add_zero] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
        field_simp [ne_of_gt hγ, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient A.problem
            (uniformOutput (K := K) (marinaProcess A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (basicPathLaw A) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ] using hAverageBound

/-- `book/MARINA/MARINA.json#/key_lemmas/12`, Theorem C.2 / Eq. (24). -/
theorem Theorem_C2_MARINA_PL {d n K : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : MARINAPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω μ n) :
    Integrable (fun path =>
        globalObjective A.problem (marinaProcess A x0 K.1 path).x -
          globalObjective A.problem xStar) (basicPathLaw A) ∧
      (∫ path,
          (globalObjective A.problem (marinaProcess A x0 K.1 path).x -
            globalObjective A.problem xStar) ∂basicPathLaw A) ≤
        (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective A.problem x0 - globalObjective A.problem xStar) := by
  have hEq21 (k : ℕ) :=
    marina_estimator_recurrence_21
      A x0 Llocal ω hSmooth hQuantizer k
  classical
  let P := A.problem
  let run := marinaProcess A x0
  let law := basicPathLaw A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) * ω * L ^ 2 / n.1
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let H : ℕ → ℝ := fun k => F k - globalObjective P xStar
  let Φ : ℕ → ℝ := fun k => H k + γ / p * E k
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hμ : 0 < (μ : ℝ) := μ.property
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hState (k : ℕ) : Measurable (run k) := by
    have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    exact hs.mono hle le_rfl
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hState k)).aestronglyMeasurable
  have hInv (k : ℕ) :
      Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law k ∧
      StepMomentWellDefined run law k := by
    simpa [P, run, law] using
      (marina_process_l2_invariant
        A x0 Llocal ω hSmooth hQuantizer k)
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [norm_sub_rev] using (hInv k).1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp
        ((measurable_state_x d).comp (hState k))).aestronglyMeasurable
    · simpa [norm_sub_rev] using (hInv k).1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law] using
      (hEq21 k).2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [StepMomentWellDefined, run, law] using (hEq21 k).2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, marinaProcess, marinaRun_succ,
        marinaStep, primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hPLInt (k : ℕ) : 2 * (μ : ℝ) * H k ≤ G k := by
    have hgapInt : Integrable (fun path =>
        globalObjective P (run k path).x - globalObjective P xStar) law :=
      (hFInt k).sub (integrable_const _)
    have hmono := integral_mono (hgapInt.const_mul (2 * (μ : ℝ)))
      (hGInt k) (fun path => hPL.2 (run k path).x)
    have hlhs :
        (∫ path, 2 * (μ : ℝ) *
          (globalObjective P (run k path).x - globalObjective P xStar) ∂law) =
          2 * (μ : ℝ) * H k := by
      rw [integral_const_mul,
        integral_sub (hFInt k) (integrable_const _), integral_const]
      simp [H, F]
    rw [hlhs] at hmono
    simpa [G] using hmono
  have hContractedDescent (k : ℕ) :
      H (k + 1) ≤ (1 - γ * (μ : ℝ)) * H k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    dsimp [H]
    dsimp [H] at hPLInt
    nlinarith [hDescent k, hPLInt k]
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k := by
    have hrec := (hEq21 k).2.2.2
    simpa [E, D, a, P, run, law, p, L] using hrec
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hCoefficients := marina_pl_stepsize_coefficients hγ
    A.refresh_admissible hQuantizer.1.le hL hStep
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / p * a := by
    simpa [a] using hCoefficients.1
  have hErrorCoeff :
      γ / 2 + γ / p * (1 - p) ≤
        (1 - γ * (μ : ℝ)) * (γ / p) := hCoefficients.2.1
  have hρ : 0 ≤ 1 - γ * (μ : ℝ) := hCoefficients.2.2
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ (1 - γ * (μ : ℝ)) * Φ k := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hEnonneg : 0 ≤ E k := integral_nonneg fun path => sq_nonneg _
    have hrec0 : E (k + 1) ≤ a * D k + (1 - p) * E k + p * 0 := by
      simpa using hRecurrence k
    simpa [Φ] using online_vr_pl_lyapunov_step H E D k hγ hp
      hDnonneg hEnonneg hCoeff hErrorCoeff (hContractedDescent k) hrec0
  have hPhiTerminal :
      Φ K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 := by
    have h := affine_contraction_le_noise_floor
      (V := 0) Φ K.1 hμ (by norm_num) hρ
        (fun k => by simpa using hLyapunov k)
    simpa using h
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient A.problem x0 - globalGradient A.problem x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hPhi0 :
      Φ 0 = globalObjective P x0 - globalObjective P xStar := by
    dsimp [Φ, H]
    rw [hE0, hF0]
    ring
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hGapLePhi : H K.1 ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / p := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hTerminal :
      H K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 *
        (globalObjective P x0 - globalObjective P xStar) := by
    calc
      H K.1 ≤ Φ K.1 := hGapLePhi
      _ ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 := hPhiTerminal
      _ = (1 - γ * (μ : ℝ)) ^ K.1 *
          (globalObjective P x0 - globalObjective P xStar) := by rw [hPhi0]
  have hGapInt : Integrable (fun path =>
      globalObjective P (run K.1 path).x - globalObjective P xStar) law :=
    (hFInt K.1).sub (integrable_const _)
  have hGapIntegral :
      (∫ path, globalObjective P (run K.1 path).x -
        globalObjective P xStar ∂law) = H K.1 := by
    rw [integral_sub (hFInt K.1) (integrable_const _), integral_const]
    simp [H, F]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hGapInt
  · rw [show (∫ path,
          (globalObjective A.problem (marinaProcess A x0 K.1 path).x -
            globalObjective A.problem xStar) ∂basicPathLaw A) = H K.1 by
          simpa [P, run, law] using hGapIntegral]
    simpa [P, γ] using hTerminal
/-- `book/MARINA/MARINA.json#/key_lemmas/14`, Theorem D.1 / Eq. (28). -/
theorem Theorem_D1_finite_sum_VR_nonconvex
    {d n m b0 K : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : FiniteSumVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    Integrable (fun z =>
        ‖globalGradient (finiteSumLocalProblem A.problem)
          (uniformOutput (K := K) (finiteSumProcess (b0 := b0) A x0) z)‖ ^ 2)
        (uniformOutputExperimentLaw (finiteSumPathLaw A batchLaw) K) ∧
      (∫ z,
          ‖globalGradient (finiteSumLocalProblem A.problem)
            (uniformOutput (K := K) (finiteSumProcess (b0 := b0) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (finiteSumPathLaw A batchLaw) K) ≤
        2 * (globalObjective (finiteSumLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) := by
  have hEq33 (k : ℕ) :=
    finite_sum_estimator_recurrence_33
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k
  classical
  let P := finiteSumLocalProblem A.problem
  let run := finiteSumProcess (b0 := b0) A x0
  let law := finiteSumPathLaw A batchLaw
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold finiteSumPathLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hState (k : ℕ) : Measurable (run k) := by
    exact (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hState k)).aestronglyMeasurable
  have hInv (k : ℕ) :
      Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law k ∧
      StepMomentWellDefined run law k := by
    simpa [P, run, law] using
      (finite_sum_process_l2_invariant
        A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k)
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [norm_sub_rev] using (hInv k).1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp
        ((measurable_state_x d).comp (hState k))).aestronglyMeasurable
    · simpa [norm_sub_rev] using (hInv k).1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law] using
      (hEq33 k).2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [StepMomentWellDefined, run, law] using (hEq33 k).2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, finiteSumProcess, finiteSumRun_succ,
        finiteSumStep, primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k := by
    have hrec := (hEq33 k).2.2.2
    dsimp [E, D, a, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := Real.sqrt_nonneg _
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact online_vr_stepsize_absorbs_displacement hγ A.refresh_admissible
      hQuantizer.1.le hL hℒ hStep
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hrec0 :
        E (k + 1) ≤ a * D k + (1 - p) * E k + p * 0 := by
      simpa using hRecurrence k
    simpa [Φ] using
      (online_vr_nonconvex_lyapunov_step
        (V := 0) F E G D k hγ hp hDnonneg hCoeff (hDescent k) hrec0)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤ Φ 0 - Φ N := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        nlinarith
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient (finiteSumLocalProblem A.problem) x0 -
        globalGradient (finiteSumLocalProblem A.problem) x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable
        (fun _ : ℕ → FiniteSumRoundNoise n m b0 Ξ => fStar) law :=
      integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    simp only [mul_zero, add_zero] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
        field_simp [ne_of_gt hγ, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient (finiteSumLocalProblem A.problem)
            (uniformOutput (K := K) (finiteSumProcess (b0 := b0) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (finiteSumPathLaw A batchLaw) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ] using hAverageBound

/-- `book/MARINA/MARINA.json#/key_lemmas/17`, Theorem D.2 / Eq. (36). -/
theorem Theorem_D2_finite_sum_VR_PL
    {d n m b0 K : Count} {Ξ : Type*} [MeasurableSpace Ξ]
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
    (hStep : FiniteSumVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path =>
        globalObjective (finiteSumLocalProblem A.problem)
            (finiteSumProcess (b0 := b0) A x0 K.1 path).x -
          globalObjective (finiteSumLocalProblem A.problem) xStar)
        (finiteSumPathLaw A batchLaw) ∧
      (∫ path,
          (globalObjective (finiteSumLocalProblem A.problem)
              (finiteSumProcess (b0 := b0) A x0 K.1 path).x -
            globalObjective (finiteSumLocalProblem A.problem) xStar)
        ∂finiteSumPathLaw A batchLaw) ≤
        (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (finiteSumLocalProblem A.problem) x0 -
            globalObjective (finiteSumLocalProblem A.problem) xStar) := by
  have hEq33 (k : ℕ) :=
    finite_sum_estimator_recurrence_33
      A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
        hQuantizer k
  classical
  let P := finiteSumLocalProblem A.problem
  let run := finiteSumProcess (b0 := b0) A x0
  let law := finiteSumPathLaw A batchLaw
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let H : ℕ → ℝ := fun k => F k - globalObjective P xStar
  let Φ : ℕ → ℝ := fun k => H k + γ / p * E k
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold finiteSumPathLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hμ : 0 < (μ : ℝ) := μ.property
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hState (k : ℕ) : Measurable (run k) := by
    exact (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hState k)).aestronglyMeasurable
  have hInv (k : ℕ) :
      Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law k ∧
      StepMomentWellDefined run law k := by
    simpa [P, run, law] using
      (finite_sum_process_l2_invariant
        A x0 batchLaw Llocal ℒlocal ω hSmooth hBatchLaw hAverageSmooth
          hQuantizer k)
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [norm_sub_rev] using (hInv k).1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp
        ((measurable_state_x d).comp (hState k))).aestronglyMeasurable
    · simpa [norm_sub_rev] using (hInv k).1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law] using
      (hEq33 k).2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [StepMomentWellDefined, run, law] using (hEq33 k).2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, finiteSumProcess, finiteSumRun_succ,
        finiteSumStep, primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hPLInt (k : ℕ) : 2 * (μ : ℝ) * H k ≤ G k := by
    have hgapInt : Integrable (fun path =>
        globalObjective P (run k path).x - globalObjective P xStar) law :=
      (hFInt k).sub (integrable_const _)
    have hmono := integral_mono (hgapInt.const_mul (2 * (μ : ℝ)))
      (hGInt k) (fun path => hPL.2 (run k path).x)
    have hlhs :
        (∫ path, 2 * (μ : ℝ) *
          (globalObjective P (run k path).x - globalObjective P xStar) ∂law) =
          2 * (μ : ℝ) * H k := by
      rw [integral_const_mul,
        integral_sub (hFInt k) (integrable_const _), integral_const]
      simp [H, F]
    rw [hlhs] at hmono
    simpa [G] using hmono
  have hContractedDescent (k : ℕ) :
      H (k + 1) ≤ (1 - γ * (μ : ℝ)) * H k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    dsimp [H]
    dsimp [H] at hPLInt
    nlinarith [hDescent k, hPLInt k]
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k := by
    have hrec := (hEq33 k).2.2.2
    dsimp [E, D, a, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := Real.sqrt_nonneg _
  have hCoefficients := online_vr_pl_stepsize_coefficients hγ
    A.refresh_admissible hQuantizer.1.le hL hℒ hStep
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / p * a := by
    simpa [a] using hCoefficients.1
  have hErrorCoeff :
      γ / 2 + γ / p * (1 - p) ≤
        (1 - γ * (μ : ℝ)) * (γ / p) := hCoefficients.2.1
  have hρ : 0 ≤ 1 - γ * (μ : ℝ) := hCoefficients.2.2
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ (1 - γ * (μ : ℝ)) * Φ k := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hEnonneg : 0 ≤ E k := integral_nonneg fun path => sq_nonneg _
    have hrec0 : E (k + 1) ≤ a * D k + (1 - p) * E k + p * 0 := by
      simpa using hRecurrence k
    simpa [Φ] using online_vr_pl_lyapunov_step H E D k hγ hp
      hDnonneg hEnonneg hCoeff hErrorCoeff (hContractedDescent k) hrec0
  have hPhiTerminal :
      Φ K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 := by
    have h := affine_contraction_le_noise_floor
      (V := 0) Φ K.1 hμ (by norm_num) hρ
        (fun k => by simpa using hLyapunov k)
    simpa using h
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient (finiteSumLocalProblem A.problem) x0 -
        globalGradient (finiteSumLocalProblem A.problem) x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hPhi0 :
      Φ 0 = globalObjective P x0 - globalObjective P xStar := by
    dsimp [Φ, H]
    rw [hE0, hF0]
    ring
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hGapLePhi : H K.1 ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / p := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hTerminal :
      H K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 *
        (globalObjective P x0 - globalObjective P xStar) := by
    calc
      H K.1 ≤ Φ K.1 := hGapLePhi
      _ ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 := hPhiTerminal
      _ = (1 - γ * (μ : ℝ)) ^ K.1 *
          (globalObjective P x0 - globalObjective P xStar) := by rw [hPhi0]
  have hGapInt : Integrable (fun path =>
      globalObjective P (run K.1 path).x - globalObjective P xStar) law :=
    (hFInt K.1).sub (integrable_const _)
  have hGapIntegral :
      (∫ path, globalObjective P (run K.1 path).x -
        globalObjective P xStar ∂law) = H K.1 := by
    rw [integral_sub (hFInt K.1) (integrable_const _), integral_const]
    simp [H, F]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hGapInt
  · rw [show (∫ path,
          (globalObjective (finiteSumLocalProblem A.problem)
              (finiteSumProcess (b0 := b0) A x0 K.1 path).x -
            globalObjective (finiteSumLocalProblem A.problem) xStar)
        ∂finiteSumPathLaw A batchLaw) = H K.1 by
          simpa [P, run, law] using hGapIntegral]
    simpa [P, γ] using hTerminal

/-- `book/MARINA/MARINA.json#/key_lemmas/19`, Theorem D.3 / Eq. (41),
using the proof's explicit claim `g⁰=∇f(x⁰)` from
`#/algorithm_spec/initialization/facts/3`.  This does not identify that claim
with Algorithm 3's malformed printed stochastic initialization. -/
theorem Theorem_D3_online_VR_nonconvex_literal_source_boundary
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    Integrable (fun z =>
        ‖globalGradient (onlineLocalProblem A.problem)
          (uniformOutput (K := K)
            (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2)
        (uniformOutputExperimentLaw
          (onlineProofExactPathLaw (b := b) (b0 := b0) A) K) ∧
      (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (onlineProofExactPathLaw (b := b) (b0 := b0) A) K) ≤
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
            (A.stepSize * K.1) + varianceAggregateSq σ / (n.1 * b.1) := by
  have hEq46 (k : ℕ) :=
    online_estimator_recurrence_46_proof_exact_literal_source_boundary
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  let V : ℝ := varianceAggregateSq σ / (n.1 * b.1)
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  have hComponents (k : ℕ) :=
    onlineProofExactProcess_scalar_recurrence_components
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k
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
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law := by
    simpa [P, run, law] using (hComponents k).1
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp_aemeasurable
        (hxMeas k).aemeasurable).aestronglyMeasurable
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, EstimatorErrorMomentWellDefined] using
      (hComponents k).2.2.2.2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, StepMomentWellDefined] using
      (hComponents k).2.2.2.2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, onlineProofExactProcess_succ, onlineStep,
        primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V := by
    have hrec := (hEq46 k).2.2.2
    dsimp [E, D, a, V, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := by exact Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := by exact Real.sqrt_nonneg _
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact online_vr_stepsize_absorbs_displacement hγ A.refresh_admissible
      hQuantizer.1.le hL hℒ hStep
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k + γ / 2 * V := by
    have hDnonneg : 0 ≤ D k := by
      exact integral_nonneg fun path => sq_nonneg _
    simpa [Φ] using online_vr_nonconvex_lyapunov_step F E G D k hγ hp
      hDnonneg hCoeff (hDescent k) (hRecurrence k)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤
        Φ 0 - Φ N + (N : ℝ) * (γ / 2) * V := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) + γ / 2 * V := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient (onlineLocalProblem A.problem) x0 -
        globalGradient (onlineLocalProblem A.problem) x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable (fun _ : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
        fStar) law := integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := by
    exact integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar + (K.1 : ℝ) * (γ / 2) * V := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    simp only [mul_zero, add_zero] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) + V := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar + (K.1 : ℝ) * (γ / 2) * V) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) + V := by
        field_simp [ne_of_gt hγ, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (onlineProofExactPathLaw (b := b) (b0 := b0) A) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ, V] using hAverageBound

theorem online_executable_initial_error_moment_eq_expected
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hBatch : OnlineBatchAdmissible b b0) :
    estimatorErrorMoment (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) 0 =
      expectedOnlineInitialEstimatorErrorSq (b := b) A x0 := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let batchLaw := onlineBatchLaw A.problem b
  let initError := fun batch : (i : Worker n) → Fin b.1 → Sample i =>
    onlineInitialEstimatorErrorSq A x0 { sample := batch }
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
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
      (SOptLib.iidStreamLaw (onlineRoundLaw (b := b) (b0 := b0) A)) := by
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw
    infer_instance
  have hfstLaw : Measure.map
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1) law = batchLaw := by
    unfold law onlinePathLaw batchLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hInitial := online_executable_initial_scalar_moments
    A x0 Llocal σ hSmooth hVariance hBatch
  have hLiftInt : Integrable (fun path => initError path.1) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law, initError,
      onlineInitialEstimatorErrorSq, onlineProcess, onlineRun_zero,
      onlinePathOfNoise] using hInitial.1
  have hBatchMeas : AEStronglyMeasurable initError batchLaw := by
    have hFixed : Integrable initError batchLaw := by
      simpa [initError, batchLaw, onlineInitialEstimatorErrorSq,
        onlineInitialState, onlinePrintedInitialEstimatorAt] using
        (online_fixed_refresh_average_second_moment
          (b := b) A x0 σ hVariance hSmooth.1).1
    exact hFixed.aestronglyMeasurable
  have hMappedMeas : AEStronglyMeasurable initError
      (Measure.map
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1) law) := by
    rw [hfstLaw]
    exact hBatchMeas
  have hBatchInt : Integrable initError batchLaw := by
    rw [← hfstLaw]
    exact integrable_map_measure_of_integrable_comp hMappedMeas
      measurable_fst.aemeasurable (by
        simpa only [Function.comp_apply] using hLiftInt)
  have hmeas : AEStronglyMeasurable initError
      (Measure.map
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1) law) := by
    rw [hfstLaw]
    exact hBatchInt.aestronglyMeasurable
  have hmapIntegral := MeasureTheory.integral_map
    (μ := law)
    (φ := fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.1)
    measurable_fst.aemeasurable hmeas
  rw [hfstLaw] at hmapIntegral
  have hleft : estimatorErrorMoment P run law 0 =
      ∫ path, initError path.1 ∂law := by
    unfold estimatorErrorMoment
    apply integral_congr_ae
    filter_upwards [] with path
    rfl
  rw [hleft, hmapIntegral.symm]
  rfl

/-- B-track correction of Theorem D.3 for the executable minibatch-at-`x⁰`
initialization.  The extra `E‖g⁰-∇f(x⁰)‖²/(pK)` term is the initial
Lyapunov estimator error omitted by the source's proof-exact substitution. -/
theorem Theorem_D3_online_VR_nonconvex_initialization_corrected_literal_source_boundary
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    Integrable (fun z =>
        ‖globalGradient (onlineLocalProblem A.problem)
          (uniformOutput (K := K)
            (onlineProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2)
        (uniformOutputExperimentLaw (onlinePathLaw (b := b) (b0 := b0) A) K) ∧
      (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (onlineProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (onlinePathLaw (b := b) (b0 := b0) A) K) ≤
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
            (A.stepSize * K.1) +
          expectedOnlineInitialEstimatorErrorSq (b := b) A x0 /
            (A.refreshProbability * K.1) +
          varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  let V : ℝ := varianceAggregateSq σ / (n.1 * b.1)
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  have hComponents (k : ℕ) :=
    online_executable_scalar_components_all
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k
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
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law := by
    simpa [P, run, law] using (hComponents k).1
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp_aemeasurable
        (hxMeas k).aemeasurable).aestronglyMeasurable
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, EstimatorErrorMomentWellDefined] using
      (hComponents k).2.2.2.2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, StepMomentWellDefined] using
      (hComponents k).2.2.2.2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, onlineProcess_succ, onlineStep,
        primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V := by
    have hrec :=
      (hComponents (k + 1)).2.2.2.2.2.2 k (Nat.lt_succ_self k)
    dsimp [E, D, a, V, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := by exact Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := by exact Real.sqrt_nonneg _
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact online_vr_stepsize_absorbs_displacement hγ A.refresh_admissible
      hQuantizer.1.le hL hℒ hStep
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k + γ / 2 * V := by
    have hDnonneg : 0 ≤ D k := by
      exact integral_nonneg fun path => sq_nonneg _
    simpa [Φ] using online_vr_nonconvex_lyapunov_step F E G D k hγ hp
      hDnonneg hCoeff (hDescent k) (hRecurrence k)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤
        Φ 0 - Φ N + (N : ℝ) * (γ / 2) * V := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) + γ / 2 * V := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith
  have hE0 :
      E 0 = expectedOnlineInitialEstimatorErrorSq (b := b) A x0 := by
    simpa [E, P, run, law] using
      (online_executable_initial_error_moment_eq_expected
        A x0 Llocal σ hSmooth hVariance hBatch)
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable (fun _ :
        ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => fStar) law :=
      integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := by
    exact integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar +
          γ / (2 * p) * expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
          (K.1 : ℝ) * (γ / 2) * V := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) +
          expectedOnlineInitialEstimatorErrorSq (b := b) A x0 / (p * K.1) +
          V := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar +
            γ / (2 * p) * expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
            (K.1 : ℝ) * (γ / 2) * V) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) +
          expectedOnlineInitialEstimatorErrorSq (b := b) A x0 / (p * K.1) +
          V := by
        field_simp [ne_of_gt hγ, ne_of_gt hp, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (onlineProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (onlinePathLaw (b := b) (b0 := b0) A) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ, V] using hAverageBound


/-- `book/MARINA/MARINA.json#/key_lemmas/22`, Theorem D.4 / Eq. (49),
over the process generated from the proof's exact initialization claim. -/
theorem Theorem_D4_online_VR_PL_literal_source_boundary
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path =>
        globalObjective (onlineLocalProblem A.problem)
            (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch K.1 path).x -
          globalObjective (onlineLocalProblem A.problem) xStar)
        (onlineProofExactPathLaw (b := b) (b0 := b0) A) ∧
      (∫ path,
          (globalObjective (onlineLocalProblem A.problem)
              (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch K.1 path).x -
            globalObjective (onlineLocalProblem A.problem) xStar)
        ∂onlineProofExactPathLaw (b := b) (b0 := b0) A) ≤
        (1 - A.stepSize * μ) ^ K.1 *
            (globalObjective (onlineLocalProblem A.problem) x0 -
              globalObjective (onlineLocalProblem A.problem) xStar) +
          varianceAggregateSq σ / (n.1 * b.1 * μ) := by
  have hEq46 (k : ℕ) :=
    online_estimator_recurrence_46_proof_exact_literal_source_boundary
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  let V : ℝ := varianceAggregateSq σ / (n.1 * b.1)
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let H : ℕ → ℝ := fun k => F k - globalObjective P xStar
  let Φ : ℕ → ℝ := fun k => H k + γ / p * E k
  have hComponents (k : ℕ) :=
    onlineProofExactProcess_scalar_recurrence_components
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k
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
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hμ : 0 < (μ : ℝ) := μ.property
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law := by
    simpa [P, run, law] using (hComponents k).1
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp_aemeasurable
        (hxMeas k).aemeasurable).aestronglyMeasurable
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, EstimatorErrorMomentWellDefined] using
      (hComponents k).2.2.2.2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, StepMomentWellDefined] using
      (hComponents k).2.2.2.2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, onlineProofExactProcess_succ, onlineStep,
        primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hPLInt (k : ℕ) : 2 * (μ : ℝ) * H k ≤ G k := by
    have hgapInt : Integrable (fun path =>
        globalObjective P (run k path).x - globalObjective P xStar) law :=
      (hFInt k).sub (integrable_const _)
    have hmono := integral_mono (hgapInt.const_mul (2 * (μ : ℝ)))
      (hGInt k) (fun path => hPL.2 (run k path).x)
    have hlhs :
        (∫ path, 2 * (μ : ℝ) *
          (globalObjective P (run k path).x - globalObjective P xStar) ∂law) =
          2 * (μ : ℝ) * H k := by
      rw [integral_const_mul,
        integral_sub (hFInt k) (integrable_const _), integral_const]
      simp [H, F]
    rw [hlhs] at hmono
    simpa [G] using hmono
  have hContractedDescent (k : ℕ) :
      H (k + 1) ≤ (1 - γ * (μ : ℝ)) * H k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    dsimp [H]
    dsimp [H] at hPLInt
    nlinarith [hDescent k, hPLInt k]
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V := by
    have hrec := (hEq46 k).2.2.2
    dsimp [E, D, a, V, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := by exact Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := by exact Real.sqrt_nonneg _
  have hCoefficients := online_vr_pl_stepsize_coefficients hγ
    A.refresh_admissible hQuantizer.1.le hL hℒ hStep
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / p * a := by
    simpa [a] using hCoefficients.1
  have hErrorCoeff :
      γ / 2 + γ / p * (1 - p) ≤
        (1 - γ * (μ : ℝ)) * (γ / p) := hCoefficients.2.1
  have hρ : 0 ≤ 1 - γ * (μ : ℝ) := hCoefficients.2.2
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ (1 - γ * (μ : ℝ)) * Φ k + γ * V := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hEnonneg : 0 ≤ E k := integral_nonneg fun path => sq_nonneg _
    simpa [Φ] using online_vr_pl_lyapunov_step H E D k hγ hp
      hDnonneg hEnonneg hCoeff hErrorCoeff (hContractedDescent k)
        (hRecurrence k)
  have hV : 0 ≤ V := by
    dsimp [V, varianceAggregateSq, meanSquare, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hPhiTerminal :
      Φ K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 + V / (μ : ℝ) :=
    affine_contraction_le_noise_floor Φ K.1 hμ hV hρ hLyapunov
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient (onlineLocalProblem A.problem) x0 -
        globalGradient (onlineLocalProblem A.problem) x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hPhi0 :
      Φ 0 = globalObjective P x0 - globalObjective P xStar := by
    dsimp [Φ, H]
    rw [hE0, hF0]
    ring
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hGapLePhi : H K.1 ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / p := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hTerminal :
      H K.1 ≤
        (1 - γ * (μ : ℝ)) ^ K.1 *
            (globalObjective P x0 - globalObjective P xStar) +
          V / (μ : ℝ) := by
    calc
      H K.1 ≤ Φ K.1 := hGapLePhi
      _ ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 +
          V / (μ : ℝ) := hPhiTerminal
      _ = (1 - γ * (μ : ℝ)) ^ K.1 *
            (globalObjective P x0 - globalObjective P xStar) +
          V / (μ : ℝ) := by rw [hPhi0]
  have hGapInt : Integrable (fun path =>
      globalObjective P (run K.1 path).x - globalObjective P xStar) law :=
    (hFInt K.1).sub (integrable_const _)
  have hGapIntegral :
      (∫ path, globalObjective P (run K.1 path).x -
        globalObjective P xStar ∂law) = H K.1 := by
    rw [integral_sub (hFInt K.1) (integrable_const _), integral_const]
    simp [H, F]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hGapInt
  · rw [show (∫ path,
          (globalObjective (onlineLocalProblem A.problem)
              (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch K.1 path).x -
            globalObjective (onlineLocalProblem A.problem) xStar)
        ∂onlineProofExactPathLaw (b := b) (b0 := b0) A) = H K.1 by
          simpa [P, run, law] using hGapIntegral]
    dsimp [P, γ, p, V] at hTerminal ⊢
    have hn_ne : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hb_ne : (b.1 : ℝ) ≠ 0 := by exact_mod_cast b.2.ne'
    have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt hμ
    have hp_ne : A.refreshProbability ≠ 0 := ne_of_gt A.refresh_admissible.1
    convert hTerminal using 1 <;>
      field_simp [hn_ne, hb_ne, hμ_ne, hp_ne] <;> ring

/-- B-track correction of Theorem D.4 for the executable minibatch-at-`x⁰`
initialization.  The decaying additional term is exactly the initial
estimator-error component of the source Lyapunov function. -/
theorem Theorem_D4_online_VR_PL_initialization_corrected_literal_source_boundary
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path =>
        globalObjective (onlineLocalProblem A.problem)
            (onlineProcess (b := b) (b0 := b0) A x0 hBatch K.1 path).x -
          globalObjective (onlineLocalProblem A.problem) xStar)
        (onlinePathLaw (b := b) (b0 := b0) A) ∧
      (∫ path,
          (globalObjective (onlineLocalProblem A.problem)
              (onlineProcess (b := b) (b0 := b0) A x0 hBatch K.1 path).x -
            globalObjective (onlineLocalProblem A.problem) xStar)
        ∂onlinePathLaw (b := b) (b0 := b0) A) ≤
        (1 - A.stepSize * μ) ^ K.1 *
            (globalObjective (onlineLocalProblem A.problem) x0 -
              globalObjective (onlineLocalProblem A.problem) xStar) +
          (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
            A.refreshProbability * expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
          varianceAggregateSq σ / (n.1 * b.1 * μ) := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  let V : ℝ := varianceAggregateSq σ / (n.1 * b.1)
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let H : ℕ → ℝ := fun k => F k - globalObjective P xStar
  let Φ : ℕ → ℝ := fun k => H k + γ / p * E k
  have hComponents (k : ℕ) :=
    online_executable_scalar_components_all
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k
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
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hμ : 0 < (μ : ℝ) := μ.property
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law := by
    simpa [P, run, law] using (hComponents k).1
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp_aemeasurable
        (hxMeas k).aemeasurable).aestronglyMeasurable
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, EstimatorErrorMomentWellDefined] using
      (hComponents k).2.2.2.2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, StepMomentWellDefined] using
      (hComponents k).2.2.2.2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, onlineProcess_succ, onlineStep,
        primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hPLInt (k : ℕ) : 2 * (μ : ℝ) * H k ≤ G k := by
    have hgapInt : Integrable (fun path =>
        globalObjective P (run k path).x - globalObjective P xStar) law :=
      (hFInt k).sub (integrable_const _)
    have hmono := integral_mono (hgapInt.const_mul (2 * (μ : ℝ)))
      (hGInt k) (fun path => hPL.2 (run k path).x)
    have hlhs :
        (∫ path, 2 * (μ : ℝ) *
          (globalObjective P (run k path).x - globalObjective P xStar) ∂law) =
          2 * (μ : ℝ) * H k := by
      rw [integral_const_mul,
        integral_sub (hFInt k) (integrable_const _), integral_const]
      simp [H, F]
    rw [hlhs] at hmono
    simpa [G] using hmono
  have hContractedDescent (k : ℕ) :
      H (k + 1) ≤ (1 - γ * (μ : ℝ)) * H k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    dsimp [H]
    dsimp [H] at hPLInt
    nlinarith [hDescent k, hPLInt k]
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V := by
    have hrec :=
      (hComponents (k + 1)).2.2.2.2.2.2 k (Nat.lt_succ_self k)
    dsimp [E, D, a, V, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := by exact Real.sqrt_nonneg _
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := by exact Real.sqrt_nonneg _
  have hCoefficients := online_vr_pl_stepsize_coefficients hγ
    A.refresh_admissible hQuantizer.1.le hL hℒ hStep
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / p * a := by
    simpa [a] using hCoefficients.1
  have hErrorCoeff :
      γ / 2 + γ / p * (1 - p) ≤
        (1 - γ * (μ : ℝ)) * (γ / p) := hCoefficients.2.1
  have hρ : 0 ≤ 1 - γ * (μ : ℝ) := hCoefficients.2.2
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ (1 - γ * (μ : ℝ)) * Φ k + γ * V := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hEnonneg : 0 ≤ E k := integral_nonneg fun path => sq_nonneg _
    simpa [Φ] using online_vr_pl_lyapunov_step H E D k hγ hp
      hDnonneg hEnonneg hCoeff hErrorCoeff (hContractedDescent k)
        (hRecurrence k)
  have hV : 0 ≤ V := by
    dsimp [V, varianceAggregateSq, meanSquare, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hPhiTerminal :
      Φ K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 + V / (μ : ℝ) :=
    affine_contraction_le_noise_floor Φ K.1 hμ hV hρ hLyapunov
  have hE0 :
      E 0 = expectedOnlineInitialEstimatorErrorSq (b := b) A x0 := by
    simpa [E, P, run, law] using
      (online_executable_initial_error_moment_eq_expected
        A x0 Llocal σ hSmooth hVariance hBatch)
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hPhi0 :
      Φ 0 = globalObjective P x0 - globalObjective P xStar +
        γ / p * expectedOnlineInitialEstimatorErrorSq (b := b) A x0 := by
    dsimp [Φ, H]
    rw [hE0, hF0]
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hGapLePhi : H K.1 ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / p := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hTerminal :
      H K.1 ≤
        (1 - γ * (μ : ℝ)) ^ K.1 *
            (globalObjective P x0 - globalObjective P xStar +
              γ / p * expectedOnlineInitialEstimatorErrorSq (b := b) A x0) +
          V / (μ : ℝ) := by
    calc
      H K.1 ≤ Φ K.1 := hGapLePhi
      _ ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 +
          V / (μ : ℝ) := hPhiTerminal
      _ = (1 - γ * (μ : ℝ)) ^ K.1 *
            (globalObjective P x0 - globalObjective P xStar +
              γ / p * expectedOnlineInitialEstimatorErrorSq (b := b) A x0) +
          V / (μ : ℝ) := by rw [hPhi0]
  have hGapInt : Integrable (fun path =>
      globalObjective P (run K.1 path).x - globalObjective P xStar) law :=
    (hFInt K.1).sub (integrable_const _)
  have hGapIntegral :
      (∫ path, globalObjective P (run K.1 path).x -
        globalObjective P xStar ∂law) = H K.1 := by
    rw [integral_sub (hFInt K.1) (integrable_const _), integral_const]
    simp [H, F]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hGapInt
  · rw [show (∫ path,
          (globalObjective (onlineLocalProblem A.problem)
              (onlineProcess (b := b) (b0 := b0) A x0 hBatch K.1 path).x -
            globalObjective (onlineLocalProblem A.problem) xStar)
        ∂onlinePathLaw (b := b) (b0 := b0) A) = H K.1 by
          simpa [P, run, law] using hGapIntegral]
    have hp_eq : p = A.refreshProbability := rfl
    rw [hp_eq] at hTerminal
    dsimp [P, γ, V] at hTerminal ⊢
    have hn_ne : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hb_ne : (b.1 : ℝ) ≠ 0 := by exact_mod_cast b.2.ne'
    have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt hμ
    have hp_ne : A.refreshProbability ≠ 0 := ne_of_gt A.refresh_admissible.1
    convert hTerminal using 1 <;>
      field_simp [hn_ne, hb_ne, hμ_ne, hp_ne] <;> ring


/-- Theorem 3.2 / D.3 on the explicitly corrected nonfallback Eq. (6)
B-track and the proof's exact-initialization interpretation. -/
theorem Theorem_D3_online_VR_nonconvex_corrected_BTrack
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 : Point d) (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    Integrable (fun z => ‖globalGradient P
      (uniformOutput (K := K) (onlineCorrectedProofExactProcess A hE x0 hBatch) z)‖ ^ 2)
      (uniformOutputExperimentLaw (onlineProofExactPathLaw (A := A)) K) ∧
    (∫ z, ‖globalGradient P
      (uniformOutput (K := K) (onlineCorrectedProofExactProcess A hE x0 hBatch) z)‖ ^ 2
      ∂uniformOutputExperimentLaw (onlineProofExactPathLaw (A := A)) K) ≤
      2 * (globalObjective P x0 - fStar) / (A.stepSize * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) := by
  dsimp only
  have hProblem :=
    onlineLocalProblemCorrected_eq_onlineLocalProblem ⟨A.problem, hE⟩
  have hProcess :=
    onlineCorrectedProofExactProcess_eq_onlineProofExactProcess A hE x0 hBatch
  have hVarianceCanonical : OnlineUnbiasedBoundedVariance A.problem σ :=
    (onlineUnbiasedBoundedVarianceCorrected_iff ⟨A.problem, hE⟩ σ).mp hVariance
  have hAverageCanonical : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal := by
    simpa [OnlineAverageSmoothnessCorrected, OnlineAverageSmoothness,
      hProblem, hProcess] using hAverageSmooth
  have hLowerCanonical : HasUniformLowerBound
      (onlineLocalProblem A.problem) fStar := by
    simpa only [hProblem] using hLower
  have hSmoothCanonical : IsLocallySmooth
      (onlineLocalProblem A.problem) Llocal := by
    simpa only [hProblem] using hSmooth
  have hSource :=
    Theorem_D3_online_VR_nonconvex_literal_source_boundary (K := K)
      A x0 Llocal ℒlocal σ ω fStar hLowerCanonical hSmoothCanonical
        hVarianceCanonical hQuantizer hBatch hAverageCanonical hStep
  simpa only [hProblem, hProcess] using hSource

/-- Theorem D.4 / Eq. (49) on the explicitly corrected nonfallback Eq. (6)
B-track. -/
theorem Theorem_D4_online_VR_PL_corrected_BTrack
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (hE : OnlineExpectationRealization A.problem)
    (x0 xStar : Point d) (Llocal ℒlocal σ : Worker n → ℝ)
    (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) fStar)
    (hSmooth : IsLocallySmooth
      (onlineLocalProblemCorrected ⟨A.problem, hE⟩) Llocal)
    (hVariance : OnlineUnbiasedBoundedVarianceCorrected ⟨A.problem, hE⟩ σ)
    (hPL : SatisfiesPL (onlineLocalProblemCorrected ⟨A.problem, hE⟩) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothnessCorrected (b0 := b0)
      ⟨A.problem, hE⟩ (onlineCorrectedProofExactProcess A hE x0 hBatch) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    let P := onlineLocalProblemCorrected ⟨A.problem, hE⟩
    Integrable (fun path => globalObjective P
      (onlineCorrectedProofExactProcess A hE x0 hBatch K.1 path).x -
        globalObjective P xStar) (onlineProofExactPathLaw (A := A)) ∧
    (∫ path, globalObjective P
      (onlineCorrectedProofExactProcess A hE x0 hBatch K.1 path).x -
        globalObjective P xStar ∂onlineProofExactPathLaw (A := A)) ≤
      (1 - A.stepSize * μ) ^ K.1 *
        (globalObjective P x0 - globalObjective P xStar) +
      varianceAggregateSq σ / (n.1 * b.1 * μ) := by
  dsimp only
  have hProblem :=
    onlineLocalProblemCorrected_eq_onlineLocalProblem ⟨A.problem, hE⟩
  have hProcess :=
    onlineCorrectedProofExactProcess_eq_onlineProofExactProcess A hE x0 hBatch
  have hVarianceCanonical : OnlineUnbiasedBoundedVariance A.problem σ :=
    (onlineUnbiasedBoundedVarianceCorrected_iff ⟨A.problem, hE⟩ σ).mp hVariance
  have hAverageCanonical : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal := by
    simpa [OnlineAverageSmoothnessCorrected, OnlineAverageSmoothness,
      hProblem, hProcess] using hAverageSmooth
  have hLowerCanonical : HasUniformLowerBound
      (onlineLocalProblem A.problem) fStar := by
    simpa only [hProblem] using hLower
  have hSmoothCanonical : IsLocallySmooth
      (onlineLocalProblem A.problem) Llocal := by
    simpa only [hProblem] using hSmooth
  have hPLCanonical : SatisfiesPL
      (onlineLocalProblem A.problem) μ xStar := by
    simpa only [hProblem] using hPL
  have hSource :=
    Theorem_D4_online_VR_PL_literal_source_boundary (K := K)
      A x0 xStar Llocal ℒlocal σ ω fStar μ hLowerCanonical
        hSmoothCanonical hVarianceCanonical hPLCanonical hQuantizer hBatch
        hAverageCanonical hStep
  simpa only [hProblem, hProcess] using hSource

/-- Eq. (54) makes the corrected `r`-denominator displacement coefficient
nonnegative in the PP-MARINA Lyapunov step. -/
theorem pp_nonconvex_stepsize_absorbs_displacement
    {r : Count} {γ L p ω : ℝ}
    (hγ : 0 < γ) (hp : RefreshProbabilityAdmissible p)
    (hω : 0 ≤ ω) (hL : 0 ≤ L)
    (hStep : PPStepsizeCondition γ L p ω r) :
    0 ≤ 1 / (2 * γ) - L / 2 -
      γ / (2 * p) * ((1 - p) * (1 + ω) * L ^ 2 / r.1) := by
  let q : ℝ := (1 - p) * (1 + ω) / (p * r.1)
  have hp_pos : 0 < p := hp.1
  have hr_pos : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hp.2) (by linarith))
      (mul_nonneg hp_pos.le hr_pos.le)
  have hs_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hstep' : γ * (L * (1 + Real.sqrt q)) ≤ 1 := by
    simpa [PPStepsizeCondition, q] using hStep
  have hu_nonneg : 0 ≤ γ * L := mul_nonneg hγ.le hL
  have hut_le_one : γ * L * Real.sqrt q ≤ 1 := by
    nlinarith
  have hut_nonneg : 0 ≤ γ * L * Real.sqrt q :=
    mul_nonneg hu_nonneg hs_nonneg
  have hbudget :
      0 ≤ (γ * L * Real.sqrt q) * (1 - γ * L * Real.sqrt q) :=
    mul_nonneg hut_nonneg (sub_nonneg.mpr hut_le_one)
  have hγq : γ ^ 2 * L ^ 2 * q = (γ * L * Real.sqrt q) ^ 2 := by
    calc
      γ ^ 2 * L ^ 2 * q = γ ^ 2 * L ^ 2 * (Real.sqrt q) ^ 2 := by
        rw [hs_sq]
      _ = (γ * L * Real.sqrt q) ^ 2 := by ring
  have hcore : 0 ≤ 1 - γ * L - γ ^ 2 * L ^ 2 * q := by
    rw [hγq]
    nlinarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hr_ne : (r.1 : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  have hq_eq :
      γ / (2 * p) * ((1 - p) * (1 + ω) * L ^ 2 / r.1) =
        γ * L ^ 2 * q / 2 := by
    dsimp [q]
    field_simp [hp_ne, hr_ne]
    <;> ring
  rw [hq_eq]
  have hscaled := mul_nonneg (show 0 ≤ (2 * γ)⁻¹ by positivity) hcore
  convert hscaled using 1 <;> field_simp [hγ_ne] <;> ring

/-- Eq. (61) supplies the three scalar coefficient facts used in the
PP-MARINA PŁ Lyapunov argument.  The square-root calculation is valid also
when the aggregate smoothness constant is zero. -/
theorem pp_pl_stepsize_coefficients
    {r : Count} {γ L p ω : ℝ} {μ : PositivePLParameter}
    (hγ : 0 < γ) (hp : RefreshProbabilityAdmissible p)
    (hω : 0 ≤ ω) (hL : 0 ≤ L)
    (hStep : PPPLStepsizeCondition γ L p ω μ r) :
    0 ≤ 1 / (2 * γ) - L / 2 -
        γ / p * ((1 - p) * (1 + ω) * L ^ 2 / r.1) ∧
      γ / 2 + γ / p * (1 - p) ≤ (1 - γ * μ) * (γ / p) ∧
      0 ≤ 1 - γ * μ := by
  let q : ℝ := 2 * (1 - p) * (1 + ω) / (p * r.1)
  have hp_pos : 0 < p := hp.1
  have hr_pos : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hp.2)) (by linarith))
      (mul_nonneg hp_pos.le hr_pos.le)
  have hs_nonneg : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  have hstep_sqrt : γ * (L * (1 + Real.sqrt q)) ≤ 1 := by
    simpa [PPPLStepsizeCondition, q] using hStep.1
  have hu_nonneg : 0 ≤ γ * L := mul_nonneg hγ.le hL
  have hut_le_one : γ * L * Real.sqrt q ≤ 1 := by
    nlinarith
  have hut_nonneg : 0 ≤ γ * L * Real.sqrt q :=
    mul_nonneg hu_nonneg hs_nonneg
  have hbudget :
      0 ≤ (γ * L * Real.sqrt q) * (1 - γ * L * Real.sqrt q) :=
    mul_nonneg hut_nonneg (sub_nonneg.mpr hut_le_one)
  have hγq : γ ^ 2 * L ^ 2 * q = (γ * L * Real.sqrt q) ^ 2 := by
    calc
      γ ^ 2 * L ^ 2 * q = γ ^ 2 * L ^ 2 * (Real.sqrt q) ^ 2 := by
        rw [hs_sq]
      _ = (γ * L * Real.sqrt q) ^ 2 := by ring
  have hcore : 0 ≤ 1 - γ * L - γ ^ 2 * L ^ 2 * q := by
    rw [hγq]
    nlinarith
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hr_ne : (r.1 : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ
  have hq_eq :
      γ / p * ((1 - p) * (1 + ω) * L ^ 2 / r.1) =
        γ * L ^ 2 * q / 2 := by
    dsimp [q]
    field_simp [hp_ne, hr_ne]
    <;> ring
  have hdisplacement :
      0 ≤ 1 / (2 * γ) - L / 2 -
        γ / p * ((1 - p) * (1 + ω) * L ^ 2 / r.1) := by
    rw [hq_eq]
    have hscaled := mul_nonneg (show 0 ≤ (2 * γ)⁻¹ by positivity) hcore
    convert hscaled using 1 <;> field_simp [hγ_ne] <;> ring
  have hmu : 2 * γ * (μ : ℝ) ≤ p := by
    simpa [PPPLStepsizeCondition] using hStep.2
  have herror :
      γ / 2 + γ / p * (1 - p) ≤ (1 - γ * μ) * (γ / p) := by
    field_simp [hp_ne]
    nlinarith
  have hcontraction : 0 ≤ 1 - γ * μ := by
    nlinarith [hp.2]
  exact ⟨hdisplacement, herror, hcontraction⟩

/-- `book/MARINA/MARINA.json#/key_lemmas/24`, Theorem E.1 / Eq. (55). -/
theorem Theorem_E1_PP_MARINA_nonconvex {d n r K : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (x0 : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStep : PPStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω r) :
    Integrable (fun z =>
        ‖globalGradient A.problem
          (uniformOutput (K := K) (ppProcess (r := r) A x0) z)‖ ^ 2)
        (uniformOutputExperimentLaw (ppPathLaw (r := r) A) K) ∧
      (∫ z,
          ‖globalGradient A.problem
            (uniformOutput (K := K) (ppProcess (r := r) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (ppPathLaw (r := r) A) K) ≤
        2 * (globalObjective A.problem x0 - fStar) / (A.stepSize * K.1) := by
  have hEq59 (k : ℕ) :=
    PP_estimator_recurrence_59
      (r := r) A x0 Llocal ω hSmooth hQuantizer hClients k
  classical
  let P := A.problem
  let run := ppProcess (r := r) A x0
  let law := ppPathLaw (r := r) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) * (1 + ω) * L ^ 2 / r.1
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hState (k : ℕ) : Measurable (run k) := by
    have hs := ppProcess_strictPast_measurable
      (r := r) A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    simpa [run] using hs.mono hle le_rfl
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hState k)).aestronglyMeasurable
  have hInv (k : ℕ) :
      Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law k ∧
      StepMomentWellDefined run law k := by
    simpa [P, run, law] using
      (pp_process_l2_invariant
        (r := r) A x0 Llocal ω hSmooth hQuantizer k)
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [norm_sub_rev] using (hInv k).1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp
        ((measurable_state_x d).comp (hState k))).aestronglyMeasurable
    · simpa [norm_sub_rev] using (hInv k).1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law] using
      (hEq59 k).2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [StepMomentWellDefined, run, law] using (hEq59 k).2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, ppProcess, ppRun_succ, ppStep,
        primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k := by
    have hrec := (hEq59 k).2.2.2
    dsimp [E, D, a, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    simpa [a] using
      (pp_nonconvex_stepsize_absorbs_displacement
        hγ A.refresh_admissible hQuantizer.1.le hL hStep)
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hrec0 :
        E (k + 1) ≤ a * D k + (1 - p) * E k + p * 0 := by
      simpa using hRecurrence k
    simpa [Φ] using
      (online_vr_nonconvex_lyapunov_step
        (V := 0) F E G D k hγ hp hDnonneg hCoeff (hDescent k) hrec0)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤ Φ 0 - Φ N := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        nlinarith
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient A.problem x0 - globalGradient A.problem x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable (fun _ : ℕ → PPRoundNoise n r Ξ => fStar) law :=
      integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    simp only [mul_zero, add_zero] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) := by
        field_simp [ne_of_gt hγ, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient A.problem
            (uniformOutput (K := K) (ppProcess (r := r) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (ppPathLaw (r := r) A) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ] using hAverageBound

/-- `book/MARINA/MARINA.json#/key_lemmas/26`, Theorem E.2 / Eq. (62). -/
theorem Theorem_E2_PP_MARINA_PL {d n r K : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStep : PPPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω μ r) :
    Integrable (fun path =>
        globalObjective A.problem (ppProcess (r := r) A x0 K.1 path).x -
          globalObjective A.problem xStar) (ppPathLaw (r := r) A) ∧
      (∫ path,
          (globalObjective A.problem (ppProcess (r := r) A x0 K.1 path).x -
            globalObjective A.problem xStar) ∂ppPathLaw (r := r) A) ≤
        (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective A.problem x0 - globalObjective A.problem xStar) := by
  have hEq59 (k : ℕ) :=
    PP_estimator_recurrence_59
      (r := r) A x0 Llocal ω hSmooth hQuantizer hClients k
  classical
  let P := A.problem
  let run := ppProcess (r := r) A x0
  let law := ppPathLaw (r := r) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) * (1 + ω) * L ^ 2 / r.1
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let H : ℕ → ℝ := fun k => F k - globalObjective P xStar
  let Φ : ℕ → ℝ := fun k => H k + γ / p * E k
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hμ : 0 < (μ : ℝ) := μ.property
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hState (k : ℕ) : Measurable (run k) := by
    have hs := ppProcess_strictPast_measurable
      (r := r) A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    simpa [run] using hs.mono hle le_rfl
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hState k)).aestronglyMeasurable
  have hInv (k : ℕ) :
      Integrable (fun path => ‖(run k path).x - x0‖ ^ 2) law ∧
      Integrable (fun path => ‖(run k path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law k ∧
      StepMomentWellDefined run law k := by
    simpa [P, run, law] using
      (pp_process_l2_invariant
        (r := r) A x0 Llocal ω hSmooth hQuantizer k)
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [norm_sub_rev] using (hInv k).1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp
        ((measurable_state_x d).comp (hState k))).aestronglyMeasurable
    · simpa [norm_sub_rev] using (hInv k).1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [EstimatorErrorMomentWellDefined, P, run, law] using
      (hEq59 k).2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [StepMomentWellDefined, run, law] using (hEq59 k).2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, ppProcess, ppRun_succ, ppStep,
        primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hPLInt (k : ℕ) : 2 * (μ : ℝ) * H k ≤ G k := by
    have hgapInt : Integrable (fun path =>
        globalObjective P (run k path).x - globalObjective P xStar) law :=
      (hFInt k).sub (integrable_const _)
    have hmono := integral_mono (hgapInt.const_mul (2 * (μ : ℝ)))
      (hGInt k) (fun path => hPL.2 (run k path).x)
    have hlhs :
        (∫ path, 2 * (μ : ℝ) *
          (globalObjective P (run k path).x - globalObjective P xStar) ∂law) =
          2 * (μ : ℝ) * H k := by
      rw [integral_const_mul,
        integral_sub (hFInt k) (integrable_const _), integral_const]
      simp [H, F]
    rw [hlhs] at hmono
    simpa [G] using hmono
  have hContractedDescent (k : ℕ) :
      H (k + 1) ≤ (1 - γ * (μ : ℝ)) * H k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    dsimp [H]
    dsimp [H] at hPLInt
    nlinarith [hDescent k, hPLInt k]
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k := by
    have hrec := (hEq59 k).2.2.2
    dsimp [E, D, a, P, run, law, p, L]
    convert hrec using 1 <;> ring
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hCoefficients := pp_pl_stepsize_coefficients hγ
    A.refresh_admissible hQuantizer.1.le hL hStep
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / p * a := by
    simpa [a] using hCoefficients.1
  have hErrorCoeff :
      γ / 2 + γ / p * (1 - p) ≤
        (1 - γ * (μ : ℝ)) * (γ / p) := hCoefficients.2.1
  have hρ : 0 ≤ 1 - γ * (μ : ℝ) := hCoefficients.2.2
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ (1 - γ * (μ : ℝ)) * Φ k := by
    have hDnonneg : 0 ≤ D k := integral_nonneg fun path => sq_nonneg _
    have hEnonneg : 0 ≤ E k := integral_nonneg fun path => sq_nonneg _
    have hrec0 : E (k + 1) ≤ a * D k + (1 - p) * E k + p * 0 := by
      simpa using hRecurrence k
    simpa [Φ] using online_vr_pl_lyapunov_step H E D k hγ hp
      hDnonneg hEnonneg hCoeff hErrorCoeff (hContractedDescent k) hrec0
  have hPhiTerminal :
      Φ K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 := by
    have h := affine_contraction_le_noise_floor
      (V := 0) Φ K.1 hμ (by norm_num) hρ
        (fun k => by simpa using hLyapunov k)
    simpa using h
  have hE0 : E 0 = 0 := by
    have heq : (fun path =>
        ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
        (fun _ => (0 : ℝ)) := by
      funext path
      change ‖globalGradient A.problem x0 - globalGradient A.problem x0‖ ^ 2 = 0
      simp
    unfold E estimatorErrorMoment
    rw [heq, integral_zero]
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hPhi0 :
      Φ 0 = globalObjective P x0 - globalObjective P xStar := by
    dsimp [Φ, H]
    rw [hE0, hF0]
    ring
  have hEK : 0 ≤ E K.1 := integral_nonneg fun path => sq_nonneg _
  have hGapLePhi : H K.1 ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / p := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hTerminal :
      H K.1 ≤ (1 - γ * (μ : ℝ)) ^ K.1 *
        (globalObjective P x0 - globalObjective P xStar) := by
    calc
      H K.1 ≤ Φ K.1 := hGapLePhi
      _ ≤ (1 - γ * (μ : ℝ)) ^ K.1 * Φ 0 := hPhiTerminal
      _ = (1 - γ * (μ : ℝ)) ^ K.1 *
          (globalObjective P x0 - globalObjective P xStar) := by rw [hPhi0]
  have hGapInt : Integrable (fun path =>
      globalObjective P (run K.1 path).x - globalObjective P xStar) law :=
    (hFInt K.1).sub (integrable_const _)
  have hGapIntegral :
      (∫ path, globalObjective P (run K.1 path).x -
        globalObjective P xStar ∂law) = H K.1 := by
    rw [integral_sub (hFInt K.1) (integrable_const _), integral_const]
    simp [H, F]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hGapInt
  · rw [show (∫ path,
          (globalObjective A.problem (ppProcess (r := r) A x0 K.1 path).x -
            globalObjective A.problem xStar) ∂ppPathLaw (r := r) A) = H K.1 by
          simpa [P, run, law] using hGapIntegral]
    simpa [P, γ] using hTerminal

/-! ## Accuracy-indexed complexity families -/

/-- The positive accuracy parameter `ε` appearing throughout
`book/MARINA/MARINA.json#/main_theorem` and the individual registered
complexity entries under `book/MARINA/MARINA.json#/key_lemmas`. -/
abbrev Accuracy := SOptLib.PositiveRealParameter

/-- Filter realization of the paper's complexity regime `ε→0⁺`: reciprocal
accuracy tends to infinity.  This is internal asymptotic infrastructure. -/
noncomputable def accuracyToZero : Filter Accuracy :=
  Filter.comap (fun ε : Accuracy => ((ε : ℝ)⁻¹)) (Filter.atTop : Filter ℝ)

/-- The paper's `O(·)` is a uniform relation between complete
accuracy-indexed families, not an existential constant chosen for one scalar. -/
def AccuracyBigO (actual scale : Accuracy → ℝ) : Prop :=
  Asymptotics.IsBigO accuracyToZero actual scale

/-- A positive objective gap makes the logarithmic accuracy factor eventually
at least one as positive accuracy tends to zero. -/
theorem eventually_one_le_log_gap_div_accuracy {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ᶠ ε : Accuracy in accuracyToZero, 1 ≤ Real.log (Δ / (ε : ℝ)) := by
  rw [accuracyToZero]
  change {ε : Accuracy | 1 ≤ Real.log (Δ / (ε : ℝ))} ∈
    Filter.comap (fun ε : Accuracy => ((ε : ℝ)⁻¹)) (Filter.atTop : Filter ℝ)
  rw [Filter.mem_comap]
  refine ⟨Set.Ici (Real.exp 1 / Δ), ?_, ?_⟩
  · exact Filter.eventually_atTop.2
      ⟨Real.exp 1 / Δ, fun b hb => hb⟩
  · intro ε hε
    change Real.exp 1 / Δ ≤ ((ε : ℝ)⁻¹) at hε
    have hexp : Real.exp 1 ≤ Δ * (ε : ℝ)⁻¹ := by
      have := (div_le_iff₀ hΔ).mp hε
      simpa [mul_comm] using this
    have hratio : 0 < Δ / (ε : ℝ) := div_pos hΔ ε.property
    apply (Real.le_log_iff_exp_le hratio).2
    simpa [div_eq_mul_inv] using hexp

/-- Solving a positive geometric contraction with a positive natural ceiling
gives both pointwise accuracy and the logarithmic asymptotic schedule. -/
theorem positive_geometric_ceiling_schedule
    (Δ c S : ℝ) (hΔ : 0 < Δ) (hc : 0 < c) (hc1 : c ≤ 1) (hS : 0 < S) :
    (∀ ε : Accuracy,
        (1 - c) ^ max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) * Δ ≤
          (ε : ℝ)) ∧
      AccuracyBigO
        (fun ε : Accuracy =>
          ((max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) : ℕ) : ℝ))
        (fun ε => S * Real.log (Δ / (ε : ℝ))) := by
  constructor
  · intro ε
    by_cases hsmall : (ε : ℝ) < Δ
    · have hratio : 0 < Δ / (ε : ℝ) := div_pos hΔ ε.property
      have hlogpos : 0 < Real.log (Δ / (ε : ℝ)) := by
        exact Real.log_pos ((one_lt_div ε.property).2 hsmall)
      have hceil := le_positive_ceil_max_one
        (Real.log (Δ / (ε : ℝ)) / c)
      have hlogK : Real.log (Δ / (ε : ℝ)) ≤
          c * ((max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) : ℕ) : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hceil hc.le
        calc
          Real.log (Δ / (ε : ℝ)) =
              c * (Real.log (Δ / (ε : ℝ)) / c) := by
                field_simp [ne_of_gt hc]
          _ ≤ _ := hmul
      have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
      have hpow : (1 - c) ^
            max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) ≤
          (Real.exp (-c)) ^
            max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) :=
        pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg c) _
      calc
        (1 - c) ^ max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) * Δ ≤
            (Real.exp (-c)) ^
              max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) * Δ :=
          mul_le_mul_of_nonneg_right hpow hΔ.le
        _ = Real.exp
              (((max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) : ℕ) : ℝ) *
                (-c)) * Δ := by rw [Real.exp_nat_mul]
        _ ≤ Real.exp (-Real.log (Δ / (ε : ℝ))) * Δ := by
          apply mul_le_mul_of_nonneg_right _ hΔ.le
          apply Real.exp_le_exp.mpr
          nlinarith
        _ = (ε : ℝ) := by
          rw [Real.exp_neg, Real.exp_log hratio]
          field_simp [ne_of_gt hΔ, ne_of_gt ε.property]
    · have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
      have hbase1 : 1 - c ≤ 1 := by linarith
      calc
        (1 - c) ^ max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c)) * Δ ≤
            1 * Δ := mul_le_mul_of_nonneg_right
              (pow_le_one₀ hbase hbase1) hΔ.le
        _ = Δ := one_mul Δ
        _ ≤ (ε : ℝ) := le_of_not_gt hsmall
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨(1 / c + 2) / S, ?_⟩
    filter_upwards [eventually_one_le_log_gap_div_accuracy hΔ] with ε hlog
    have hy : 0 ≤ Real.log (Δ / (ε : ℝ)) / c :=
      div_nonneg (le_trans (by norm_num) hlog) hc.le
    have hceil := natCast_max_one_ceil_le_add_two
      (Real.log (Δ / (ε : ℝ)) / c) hy
    have hlinear : Real.log (Δ / (ε : ℝ)) / c + 2 ≤
        (1 / c + 2) * Real.log (Δ / (ε : ℝ)) := by
      calc
        Real.log (Δ / (ε : ℝ)) / c + 2 =
            (1 / c) * Real.log (Δ / (ε : ℝ)) + 2 := by ring
        _ ≤ (1 / c) * Real.log (Δ / (ε : ℝ)) +
            2 * Real.log (Δ / (ε : ℝ)) := by nlinarith
        _ = (1 / c + 2) * Real.log (Δ / (ε : ℝ)) := by ring
    have hfactor : (1 / c + 2) * Real.log (Δ / (ε : ℝ)) =
        ((1 / c + 2) / S) *
          (S * Real.log (Δ / (ε : ℝ))) := by
      field_simp [ne_of_gt hS]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg
        (max 1 (Nat.ceil (Real.log (Δ / (ε : ℝ)) / c))))]
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hS (lt_of_lt_of_le zero_lt_one hlog))]
    exact hceil.trans (hlinear.trans_eq hfactor)

/-- The PŁ endpoint splits its accuracy budget equally between geometric
contraction and the stationary stochastic floor.  A factor two in the initial
gap changes only the constant in the logarithmic schedule. -/
theorem positive_geometric_ceiling_schedule_half_budget
    (Δ c S : ℝ) (hΔ : 0 < Δ) (hc : 0 < c) (hc1 : c ≤ 1) (hS : 0 < S) :
    (∀ ε : Accuracy,
        (1 - c) ^ max 1 (Nat.ceil (Real.log (2 * Δ / (ε : ℝ)) / c)) * Δ ≤
          (ε : ℝ) / 2) ∧
      AccuracyBigO
        (fun ε : Accuracy =>
          ((max 1 (Nat.ceil (Real.log (2 * Δ / (ε : ℝ)) / c)) : ℕ) : ℝ))
        (fun ε => S * Real.log (Δ / (ε : ℝ))) := by
  have hTwoΔ : 0 < 2 * Δ := mul_pos (by norm_num) hΔ
  have hScalar := positive_geometric_ceiling_schedule
    (2 * Δ) c S hTwoΔ hc hc1 hS
  constructor
  · intro ε
    have h := hScalar.1 ε
    nlinarith [pow_nonneg (sub_nonneg.mpr hc1)
      (max 1 (Nat.ceil (Real.log (2 * Δ / (ε : ℝ)) / c)))]
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨(2 / c + 2) / S, ?_⟩
    filter_upwards [eventually_one_le_log_gap_div_accuracy hΔ] with ε hlog
    have hratio : 0 < Δ / (ε : ℝ) := div_pos hΔ ε.property
    have hlogTwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    have hlogEq : Real.log (2 * Δ / (ε : ℝ)) =
        Real.log 2 + Real.log (Δ / (ε : ℝ)) := by
      rw [show 2 * Δ / (ε : ℝ) = 2 * (Δ / (ε : ℝ)) by ring]
      exact Real.log_mul (by norm_num) (ne_of_gt hratio)
    have hlogTwoΔ : Real.log (2 * Δ / (ε : ℝ)) ≤
        2 * Real.log (Δ / (ε : ℝ)) := by
      rw [hlogEq]
      nlinarith
    have hy : 0 ≤ Real.log (2 * Δ / (ε : ℝ)) / c := by
      apply div_nonneg _ hc.le
      rw [hlogEq]
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    have hceil := natCast_max_one_ceil_le_add_two
      (Real.log (2 * Δ / (ε : ℝ)) / c) hy
    have hlinear : Real.log (2 * Δ / (ε : ℝ)) / c + 2 ≤
        (2 / c + 2) * Real.log (Δ / (ε : ℝ)) := by
      calc
        Real.log (2 * Δ / (ε : ℝ)) / c + 2 ≤
            (2 * Real.log (Δ / (ε : ℝ))) / c + 2 := by
              gcongr
        _ ≤ (2 / c) * Real.log (Δ / (ε : ℝ)) +
            2 * Real.log (Δ / (ε : ℝ)) := by
              rw [show (2 * Real.log (Δ / (ε : ℝ))) / c =
                (2 / c) * Real.log (Δ / (ε : ℝ)) by ring]
              nlinarith
        _ = (2 / c + 2) * Real.log (Δ / (ε : ℝ)) := by ring
    have hfactor : (2 / c + 2) * Real.log (Δ / (ε : ℝ)) =
        ((2 / c + 2) / S) *
          (S * Real.log (Δ / (ε : ℝ))) := by
      field_simp [ne_of_gt hS]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg
        (max 1 (Nat.ceil (Real.log (2 * Δ / (ε : ℝ)) / c))))]
    rw [Real.norm_eq_abs,
      abs_of_pos (mul_pos hS (lt_of_lt_of_le zero_lt_one hlog))]
    exact hceil.trans (hlinear.trans_eq hfactor)

/-- A positive inverse-square accuracy budget can be realized by a positive
natural ceiling, with the same inverse-square asymptotic scale. -/
theorem positive_inverse_square_ceiling_schedule
    (Δ γ S : ℝ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hS : 0 < S) :
    (∀ ε : Accuracy,
        2 * Δ /
            (γ * ((max 1 (Nat.ceil (2 * Δ / (γ * (ε : ℝ) ^ 2))) : ℕ) : ℝ)) ≤
          (ε : ℝ) ^ 2) ∧
      AccuracyBigO
        (fun ε : Accuracy =>
          ((max 1 (Nat.ceil (2 * Δ / (γ * (ε : ℝ) ^ 2))) : ℕ) : ℝ))
        (fun ε => Δ / (ε : ℝ) ^ 2 * S) := by
  constructor
  · intro ε
    have hbudget := div_natCast_max_one_ceil_div_le
      (2 * Δ / γ) ((ε : ℝ) ^ 2) (sq_pos_of_pos ε.property)
    convert hbudget using 1 <;> field_simp [ne_of_gt hγ, ne_of_gt ε.property] <;> ring
  · unfold AccuracyBigO
    have hEventually :
        ∀ᶠ ε : Accuracy in accuracyToZero, 1 ≤ Δ / (ε : ℝ) ^ 2 := by
      rw [accuracyToZero]
      change {ε : Accuracy | 1 ≤ Δ / (ε : ℝ) ^ 2} ∈
        Filter.comap (fun ε : Accuracy => ((ε : ℝ)⁻¹)) (Filter.atTop : Filter ℝ)
      rw [Filter.mem_comap]
      refine ⟨Set.Ici (max 1 (1 / Δ)), ?_, ?_⟩
      · exact Filter.eventually_atTop.2
          ⟨max 1 (1 / Δ), fun b hb => hb⟩
      · intro ε hε
        change max 1 (1 / Δ) ≤ (ε : ℝ)⁻¹ at hε
        change 1 ≤ Δ / (ε : ℝ) ^ 2
        have hone : 1 ≤ (ε : ℝ)⁻¹ := (le_max_left _ _).trans hε
        have hgap : 1 ≤ Δ * (ε : ℝ)⁻¹ := by
          have := (le_max_right (1 : ℝ) (1 / Δ)).trans hε
          rw [div_le_iff₀ hΔ] at this
          simpa [mul_comm] using this
        have hinv : 0 < (ε : ℝ)⁻¹ := inv_pos.mpr ε.property
        have : 1 ≤ Δ * (ε : ℝ)⁻¹ * (ε : ℝ)⁻¹ := by
          nlinarith [hΔ]
        have heq : Δ / (ε : ℝ) ^ 2 =
            Δ * (ε : ℝ)⁻¹ * (ε : ℝ)⁻¹ := by
          field_simp [ne_of_gt ε.property]
        rw [heq]
        exact this
    rw [Asymptotics.isBigO_iff]
    refine ⟨(2 / γ + 2) / S, ?_⟩
    filter_upwards [hEventually] with ε hscale
    have hy : 0 ≤ 2 * Δ / (γ * (ε : ℝ) ^ 2) := by positivity
    have hceil := natCast_max_one_ceil_le_add_two
      (2 * Δ / (γ * (ε : ℝ) ^ 2)) hy
    have hscalePos : 0 < Δ / (ε : ℝ) ^ 2 * S := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((max 1 (Nat.ceil (2 * Δ / (γ * (ε : ℝ) ^ 2))) : ℕ) : ℝ))]
    rw [Real.norm_eq_abs, abs_of_pos hscalePos]
    calc
      ((max 1 (Nat.ceil (2 * Δ / (γ * (ε : ℝ) ^ 2))) : ℕ) : ℝ) ≤
          2 * Δ / (γ * (ε : ℝ) ^ 2) + 2 := hceil
      _ ≤ (2 / γ + 2) * (Δ / (ε : ℝ) ^ 2) := by
        have hyEq : 2 * Δ / (γ * (ε : ℝ) ^ 2) =
            (2 / γ) * (Δ / (ε : ℝ) ^ 2) := by
          field_simp [ne_of_gt hγ, ne_of_gt ε.property]
          <;> ring
        rw [hyEq]
        nlinarith
      _ = ((2 / γ + 2) / S) *
          (Δ / (ε : ℝ) ^ 2 * S) := by
        field_simp [ne_of_gt hS]

/-- Iteration complexity at the source boundary.  The right disjunct is the
ordinary asymptotic statement.  The left disjunct is the nonempty-window
totalization of the paper's already-solved, zero-round case: the displayed
scale vanishes, while the positive `Count` schedule used to state an endpoint
with a nonempty output window must remain uniformly bounded.  In particular,
this branch does not make an arbitrary positive schedule complexity-free. -/
def AccuracyIterationBigO (actual scale : Accuracy → ℝ) : Prop :=
  ((∀ ε, scale ε = 0) ∧ AccuracyBigO actual (fun _ => 1)) ∨
    AccuracyBigO actual scale

/-- The paper's `Θ(·)` batch schedules at accuracy tending to zero. -/
def AccuracyTheta (actual scale : Accuracy → ℝ) : Prop :=
  Asymptotics.IsTheta accuracyToZero actual scale

/-- The refresh-batch choice used in the accuracy conclusion of Theorem D.3.
The first summand makes Algorithm 3's strict inequality `b⁰ < b` intrinsic;
the ceiling makes the variance term in Eq. (41) consume at most half of the
requested squared-accuracy budget. -/
noncomputable def onlineNonconvexBatchSchedule
    (n b0 : Count) (variance : ℝ) (ε : Accuracy) : Count :=
  ⟨b0.1 + max 1
      (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2))), by omega⟩

theorem onlineNonconvexBatchSchedule_admissible
    (n b0 : Count) (variance : ℝ) (ε : Accuracy) :
    OnlineBatchAdmissible (onlineNonconvexBatchSchedule n b0 variance ε) b0 := by
  unfold OnlineBatchAdmissible
  change b0.1 < b0.1 + max 1
    (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2)))
  omega

theorem onlineNonconvexBatchSchedule_variance_floor
    (n b0 : Count) (variance : ℝ) (hvariance : 0 ≤ variance)
    (ε : Accuracy) :
    variance /
        (n.1 * (onlineNonconvexBatchSchedule n b0 variance ε).1) ≤
      (ε : ℝ) ^ 2 / 2 := by
  let q : ℕ := max 1
    (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2)))
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hb : 0 < ((onlineNonconvexBatchSchedule n b0 variance ε).1 : ℝ) := by
    exact_mod_cast (onlineNonconvexBatchSchedule n b0 variance ε).2
  have hqb : (q : ℝ) ≤
      ((onlineNonconvexBatchSchedule n b0 variance ε).1 : ℝ) := by
    dsimp [onlineNonconvexBatchSchedule, q]
    norm_cast
    omega
  have hceil : 2 * variance / (n.1 * (ε : ℝ) ^ 2) ≤ (q : ℝ) := by
    simpa [q] using
      le_positive_ceil_max_one (2 * variance / (n.1 * (ε : ℝ) ^ 2))
  have htwovariance :
      2 * variance ≤ (ε : ℝ) ^ 2 * ((n.1 : ℝ) * q) := by
    calc
      2 * variance =
          (2 * variance / ((n.1 : ℝ) * (ε : ℝ) ^ 2)) *
            ((ε : ℝ) ^ 2 * (n.1 : ℝ)) := by
              field_simp [ne_of_gt ε.property, ne_of_gt hn]
      _ ≤ (q : ℝ) * ((ε : ℝ) ^ 2 * (n.1 : ℝ)) :=
        mul_le_mul_of_nonneg_right hceil (by positivity)
      _ = (ε : ℝ) ^ 2 * ((n.1 : ℝ) * q) := by ring
  have htwobatch : 2 * variance ≤ (ε : ℝ) ^ 2 *
      ((n.1 : ℝ) * (onlineNonconvexBatchSchedule n b0 variance ε).1) :=
    htwovariance.trans (by gcongr)
  rw [div_le_iff₀ (mul_pos hn hb)]
  nlinarith

/-- For positive variance, the canonical D.3 batch choice has exactly the
source's inverse-square asymptotic order.  Positivity is necessary here:
no positive-natural batch family can be `Θ(0)`. -/
theorem onlineNonconvexBatchSchedule_accuracyTheta
    (n b0 : Count) (variance : ℝ) (hvariance : 0 < variance) :
    AccuracyTheta
      (fun ε => ((onlineNonconvexBatchSchedule n b0 variance ε).1 : ℝ))
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2)) := by
  unfold AccuracyTheta
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨(b0.1 : ℝ) + 4, ?_⟩
    have hEventually :
        ∀ᶠ ε : Accuracy in accuracyToZero,
          1 ≤ variance / (n.1 * (ε : ℝ) ^ 2) := by
      rw [accuracyToZero]
      change {ε : Accuracy |
          1 ≤ variance / (n.1 * (ε : ℝ) ^ 2)} ∈
        Filter.comap (fun ε : Accuracy => ((ε : ℝ)⁻¹))
          (Filter.atTop : Filter ℝ)
      rw [Filter.mem_comap]
      refine ⟨Set.Ici (max 1 (n.1 / variance)), ?_, ?_⟩
      · exact Filter.eventually_atTop.2
          ⟨max 1 (n.1 / variance), fun a ha => ha⟩
      · intro ε hε
        change max 1 (n.1 / variance) ≤ (ε : ℝ)⁻¹ at hε
        change 1 ≤ variance / (n.1 * (ε : ℝ) ^ 2)
        have hone : 1 ≤ (ε : ℝ)⁻¹ := (le_max_left _ _).trans hε
        have hratio : n.1 / variance ≤ (ε : ℝ)⁻¹ :=
          (le_max_right _ _).trans hε
        have hprod : (n.1 : ℝ) ≤ variance * (ε : ℝ)⁻¹ := by
          have := (div_le_iff₀ hvariance).1 hratio
          simpa [mul_comm] using this
        have hinv : 0 < (ε : ℝ)⁻¹ := inv_pos.mpr ε.property
        have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
        have : (n.1 : ℝ) ≤ variance * (ε : ℝ)⁻¹ * (ε : ℝ)⁻¹ := by
          nlinarith
        rw [le_div_iff₀ (mul_pos hn (sq_pos_of_pos ε.property))]
        have hmul := mul_le_mul_of_nonneg_right this
          (sq_nonneg (ε : ℝ))
        calc
          1 * ((n.1 : ℝ) * (ε : ℝ) ^ 2) =
              (n.1 : ℝ) * (ε : ℝ) ^ 2 := by ring
          _ ≤ (variance * (ε : ℝ)⁻¹ * (ε : ℝ)⁻¹) *
              (ε : ℝ) ^ 2 := by simpa [mul_assoc] using hmul
          _ = variance := by field_simp [ne_of_gt ε.property]
    filter_upwards [hEventually] with ε hscale
    let s : ℝ := variance / (n.1 * (ε : ℝ) ^ 2)
    have hs : 1 ≤ s := by simpa [s] using hscale
    have harg : 0 ≤ 2 * s := by positivity
    have hceil := natCast_max_one_ceil_le_add_two (2 * s) harg
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineNonconvexBatchSchedule n b0 variance ε).1 : ℝ))]
    rw [Real.norm_eq_abs, abs_of_pos hspos]
    simp only [onlineNonconvexBatchSchedule, Nat.cast_add]
    change (b0.1 : ℝ) +
        ((max 1 (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2))) : ℕ) : ℝ) ≤
      ((b0.1 : ℝ) + 4) * s
    have hargEq : 2 * variance / (n.1 * (ε : ℝ) ^ 2) = 2 * s := by
      simp [s]
      ring
    rw [hargEq]
    calc
      (b0.1 : ℝ) + ((max 1 (Nat.ceil (2 * s)) : ℕ) : ℝ) ≤
          (b0.1 : ℝ) + (2 * s + 2) := by gcongr
      _ ≤ ((b0.1 : ℝ) + 4) * s := by
        have hb0 : 0 ≤ (b0.1 : ℝ) := by positivity
        nlinarith
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, Filter.Eventually.of_forall ?_⟩
    intro ε
    let s : ℝ := variance / (n.1 * (ε : ℝ) ^ 2)
    have hs : 0 ≤ s := by positivity
    have hceil : 2 * s ≤
        ((max 1 (Nat.ceil (2 * s)) : ℕ) : ℝ) :=
      le_positive_ceil_max_one (2 * s)
    have hle : s ≤
        ((onlineNonconvexBatchSchedule n b0 variance ε).1 : ℝ) := by
      have hargEq : 2 * variance / (n.1 * (ε : ℝ) ^ 2) = 2 * s := by
        simp [s]
        ring
      simp only [onlineNonconvexBatchSchedule, Nat.cast_add]
      change s ≤ (b0.1 : ℝ) +
        ((max 1 (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2))) : ℕ) : ℝ)
      rw [hargEq]
      have hb0 : 0 ≤ (b0.1 : ℝ) := by positivity
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg hs]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineNonconvexBatchSchedule n b0 variance ε).1 : ℝ))]
    simpa [s] using hle

/-- Inflation of an arbitrary source-scale representative to the concrete
pointwise-safe batch actually used by the D.3 accuracy endpoint. -/
noncomputable def onlineNonconvexBatchScheduleFromBase
    (n b0 : Count) (variance : ℝ) (base : Accuracy → Count)
    (ε : Accuracy) : Count :=
  ⟨b0.1 + (base ε).1 + max 1
      (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2))), by omega⟩

theorem onlineNonconvexBatchScheduleFromBase_admissible
    (n b0 : Count) (variance : ℝ) (base : Accuracy → Count)
    (ε : Accuracy) :
    OnlineBatchAdmissible
      (onlineNonconvexBatchScheduleFromBase n b0 variance base ε) b0 := by
  unfold OnlineBatchAdmissible
  change b0.1 < b0.1 + (base ε).1 + max 1
    (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2)))
  omega

theorem onlineNonconvexBatchScheduleFromBase_variance_floor
    (n b0 : Count) (variance : ℝ) (hvariance : 0 ≤ variance)
    (base : Accuracy → Count) (ε : Accuracy) :
    variance /
        (n.1 *
          (onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1) ≤
      (ε : ℝ) ^ 2 / 2 := by
  let canonical := onlineNonconvexBatchSchedule n b0 variance ε
  have hcanonical := onlineNonconvexBatchSchedule_variance_floor
    n b0 variance hvariance ε
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hcanonicalPos : 0 < (canonical.1 : ℝ) := by
    exact_mod_cast canonical.2
  have hinflatedPos : 0 <
      ((onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1 : ℝ) := by
    exact_mod_cast
      (onlineNonconvexBatchScheduleFromBase n b0 variance base ε).2
  have hle : (canonical.1 : ℝ) ≤
      ((onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1 : ℝ) := by
    let q := max 1 (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2)))
    have hNat : b0.1 + q ≤ b0.1 + (base ε).1 + q := by omega
    exact_mod_cast hNat
  calc
    variance /
        (n.1 *
          (onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1) ≤
        variance / (n.1 * canonical.1) := by
      apply div_le_div_of_nonneg_left hvariance
        (mul_pos hn hcanonicalPos)
      exact mul_le_mul_of_nonneg_left hle hn.le
    _ ≤ (ε : ℝ) ^ 2 / 2 := by simpa [canonical] using hcanonical

theorem onlineNonconvexBatchScheduleFromBase_accuracyTheta
    (n b0 : Count) (variance : ℝ) (hvariance : 0 ≤ variance)
    (base : Accuracy → Count)
    (hbase : AccuracyTheta (fun ε => ((base ε).1 : ℝ))
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2))) :
    AccuracyTheta
      (fun ε =>
        ((onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1 : ℝ))
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2)) := by
  unfold AccuracyTheta at hbase ⊢
  constructor
  · have hBaseO := hbase.1
    rw [Asymptotics.isBigO_iff'] at hBaseO ⊢
    rcases hBaseO with ⟨C, hCpos, hC⟩
    refine ⟨((b0.1 : ℝ) + 3) * C + 2, by positivity, ?_⟩
    filter_upwards [hC] with ε hε
    let s : ℝ := variance / (n.1 * (ε : ℝ) ^ 2)
    have hs : 0 ≤ s := by dsimp [s]; positivity
    have hbasePos : 0 < ((base ε).1 : ℝ) := by exact_mod_cast (base ε).2
    have hbaseOne : 1 ≤ ((base ε).1 : ℝ) := by exact_mod_cast (base ε).2
    have hceil := natCast_max_one_ceil_le_add_two (2 * s) (by positivity)
    have hargEq : 2 * variance / (n.1 * (ε : ℝ) ^ 2) = 2 * s := by
      simp [s]
      ring
    have hbaseBound : ((base ε).1 : ℝ) ≤ C * s := by
      simpa [Real.norm_eq_abs, abs_of_pos hbasePos,
        abs_of_nonneg hvariance, abs_of_nonneg hs, s] using hε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1 : ℝ))]
    rw [Real.norm_eq_abs, abs_of_nonneg hs]
    simp only [onlineNonconvexBatchScheduleFromBase, Nat.cast_add]
    rw [hargEq]
    calc
      (b0.1 : ℝ) + (base ε).1 +
          ((max 1 (Nat.ceil (2 * s)) : ℕ) : ℝ) ≤
        (b0.1 : ℝ) + (base ε).1 + (2 * s + 2) := by gcongr
      _ ≤ ((b0.1 : ℝ) + 3) * (base ε).1 + 2 * s := by
        have hb0 : 0 ≤ (b0.1 : ℝ) := by positivity
        nlinarith
      _ ≤ (((b0.1 : ℝ) + 3) * C + 2) * s := by
        have hb0 : 0 ≤ (b0.1 : ℝ) := by positivity
        nlinarith
  · have hScaleO := hbase.2
    rw [Asymptotics.isBigO_iff'] at hScaleO ⊢
    rcases hScaleO with ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, ?_⟩
    filter_upwards [hC] with ε hε
    have hbaseInflated : ((base ε).1 : ℝ) ≤
        ((onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1 : ℝ) := by
      let q := max 1 (Nat.ceil (2 * variance / (n.1 * (ε : ℝ) ^ 2)))
      have hNat : (base ε).1 ≤ b0.1 + (base ε).1 + q := by omega
      exact_mod_cast hNat
    have hbasePos : 0 < ((base ε).1 : ℝ) := by exact_mod_cast (base ε).2
    have hinflatedPos : 0 <
        ((onlineNonconvexBatchScheduleFromBase n b0 variance base ε).1 : ℝ) := by
      exact_mod_cast
        (onlineNonconvexBatchScheduleFromBase n b0 variance base ε).2
    exact hε.trans (mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs, abs_of_pos hbasePos,
          abs_of_pos hinflatedPos] using hbaseInflated) hCpos.le)

/-- The batch selected in Theorem D.4, inflated from an arbitrary representative
of the source `Θ(σ²/(nμε))` class.  The positive ceiling is the literal
finite-batch realization of proof step 14's instruction to control Eq. (49). -/
noncomputable def onlinePLBatchScheduleFromBase
    (n b0 : Count) (variance μ : ℝ) (base : Accuracy → Count)
    (ε : Accuracy) : Count :=
  ⟨b0.1 + (base ε).1 + max 1
      (Nat.ceil (2 * variance / (n.1 * μ * (ε : ℝ)))), by omega⟩

theorem onlinePLBatchScheduleFromBase_admissible
    (n b0 : Count) (variance μ : ℝ) (base : Accuracy → Count)
    (ε : Accuracy) :
    OnlineBatchAdmissible
      (onlinePLBatchScheduleFromBase n b0 variance μ base ε) b0 := by
  unfold OnlineBatchAdmissible
  change b0.1 < b0.1 + (base ε).1 + max 1
    (Nat.ceil (2 * variance / (n.1 * μ * (ε : ℝ))))
  omega

theorem onlinePLBatchScheduleFromBase_variance_floor
    (n b0 : Count) (variance μ : ℝ) (hvariance : 0 ≤ variance)
    (hμ : 0 < μ) (base : Accuracy → Count) (ε : Accuracy) :
    variance /
        (n.1 * (onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 * μ) ≤
      (ε : ℝ) / 2 := by
  let q : ℕ := max 1
    (Nat.ceil (2 * variance / (n.1 * μ * (ε : ℝ))))
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hq : 0 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  have hb : 0 <
      ((onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 : ℝ) := by
    exact_mod_cast (onlinePLBatchScheduleFromBase n b0 variance μ base ε).2
  have hqb : (q : ℝ) ≤
      ((onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 : ℝ) := by
    dsimp [onlinePLBatchScheduleFromBase, q]
    norm_cast
    omega
  have hceil : 2 * variance / (n.1 * μ * (ε : ℝ)) ≤ (q : ℝ) := by
    simpa [q] using
      le_positive_ceil_max_one (2 * variance / (n.1 * μ * (ε : ℝ)))
  have htwovariance : 2 * variance ≤ (ε : ℝ) * ((n.1 : ℝ) * q * μ) := by
    calc
      2 * variance =
          (2 * variance / ((n.1 : ℝ) * μ * (ε : ℝ))) *
            ((ε : ℝ) * ((n.1 : ℝ) * μ)) := by
              field_simp [ne_of_gt ε.property, ne_of_gt hn, ne_of_gt hμ]
              <;> ring
      _ ≤ (q : ℝ) * ((ε : ℝ) * ((n.1 : ℝ) * μ)) :=
        mul_le_mul_of_nonneg_right hceil
          (mul_nonneg ε.property.le (mul_nonneg hn.le hμ.le))
      _ = (ε : ℝ) * ((n.1 : ℝ) * q * μ) := by ring
  have htwobatch : 2 * variance ≤ (ε : ℝ) *
      ((n.1 : ℝ) *
        (onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 * μ) :=
    htwovariance.trans (by
      apply mul_le_mul_of_nonneg_left _ ε.property.le
      apply mul_le_mul_of_nonneg_right _ hμ.le
      exact mul_le_mul_of_nonneg_left hqb hn.le)
  rw [div_le_iff₀ (by positivity : 0 < (n.1 : ℝ) *
    (onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 * μ)]
  nlinarith

theorem onlinePLBatchScheduleFromBase_accuracyTheta
    (n b0 : Count) (variance μ : ℝ) (hvariance : 0 ≤ variance)
    (hμ : 0 < μ) (base : Accuracy → Count)
    (hbase : AccuracyTheta (fun ε => ((base ε).1 : ℝ))
      (fun ε => variance / (n.1 * μ * (ε : ℝ)))) :
    AccuracyTheta
      (fun ε =>
        ((onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 : ℝ))
      (fun ε => variance / (n.1 * μ * (ε : ℝ))) := by
  unfold AccuracyTheta at hbase ⊢
  constructor
  · have hBaseO := hbase.1
    rw [Asymptotics.isBigO_iff'] at hBaseO ⊢
    rcases hBaseO with ⟨C, hCpos, hC⟩
    refine ⟨((b0.1 : ℝ) + 3) * C + 2, by positivity, ?_⟩
    filter_upwards [hC] with ε hε
    let s : ℝ := variance / (n.1 * μ * (ε : ℝ))
    have hs : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg hvariance
        (mul_nonneg (mul_nonneg (by positivity) hμ.le) ε.property.le)
    have hbasePos : 0 < ((base ε).1 : ℝ) := by exact_mod_cast (base ε).2
    have hbaseOne : 1 ≤ ((base ε).1 : ℝ) := by exact_mod_cast (base ε).2
    have hceil := natCast_max_one_ceil_le_add_two (2 * s) (by positivity)
    have hargEq : 2 * variance / (n.1 * μ * (ε : ℝ)) = 2 * s := by
      simp [s]
      ring
    have hbaseBound : ((base ε).1 : ℝ) ≤ C * s := by
      simpa [Real.norm_eq_abs, abs_of_pos hbasePos,
        abs_of_nonneg hvariance, abs_of_pos hμ, abs_of_pos ε.property,
        abs_of_nonneg hs, s] using hε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 : ℝ))]
    rw [Real.norm_eq_abs, abs_of_nonneg hs]
    simp only [onlinePLBatchScheduleFromBase, Nat.cast_add]
    rw [hargEq]
    calc
      (b0.1 : ℝ) + (base ε).1 +
          ((max 1 (Nat.ceil (2 * s)) : ℕ) : ℝ) ≤
        (b0.1 : ℝ) + (base ε).1 + (2 * s + 2) := by gcongr
      _ ≤ ((b0.1 : ℝ) + 3) * (base ε).1 + 2 * s := by
        have hb0 : 0 ≤ (b0.1 : ℝ) := by positivity
        nlinarith
      _ ≤ (((b0.1 : ℝ) + 3) * C + 2) * s := by
        have hb0 : 0 ≤ (b0.1 : ℝ) := by positivity
        nlinarith
  · have hScaleO := hbase.2
    rw [Asymptotics.isBigO_iff'] at hScaleO ⊢
    rcases hScaleO with ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, ?_⟩
    filter_upwards [hC] with ε hε
    have hbaseInflated : ((base ε).1 : ℝ) ≤
        ((onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 : ℝ) := by
      let q := max 1 (Nat.ceil (2 * variance / (n.1 * μ * (ε : ℝ))))
      have hNat : (base ε).1 ≤ b0.1 + (base ε).1 + q := by omega
      exact_mod_cast hNat
    have hbasePos : 0 < ((base ε).1 : ℝ) := by exact_mod_cast (base ε).2
    have hinflatedPos : 0 <
        ((onlinePLBatchScheduleFromBase n b0 variance μ base ε).1 : ℝ) := by
      exact_mod_cast (onlinePLBatchScheduleFromBase n b0 variance μ base ε).2
    exact hε.trans (mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs, abs_of_pos hbasePos,
          abs_of_pos hinflatedPos] using hbaseInflated) hCpos.le)

/-- The executable Eq. (40) choice used by Corollary D.3.  The paper prints
an upper bound for `γ`; choosing the reciprocal of the (at-least-one)
denominator makes that choice uniform for an accuracy-indexed family and
avoids treating an arbitrarily smaller stepsize as having the same rate. -/
noncomputable def onlineDensityCanonicalStepsize
    (L ℒ p ω : ℝ) (n b0 : Count) : PositiveStepsize :=
  ⟨1 / max 1 (L + Real.sqrt ((1 - p) / (p * n.1) *
      (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1))), by
    exact one_div_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))⟩

theorem onlineDensityCanonicalStepsize_condition
    {L ℒ p ω : ℝ} {n b0 : Count} :
    OnlineVRStepsizeCondition
      (onlineDensityCanonicalStepsize L ℒ p ω n b0) L ℒ p ω n b0 := by
  let D : ℝ := L + Real.sqrt ((1 - p) / (p * n.1) *
    (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1))
  let M : ℝ := max 1 D
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDM : D ≤ M := le_max_right _ _
  unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition
  change (1 / M) * D ≤ 1
  calc
    (1 / M) * D = D / M := by ring
    _ ≤ 1 := (div_le_one hM).2 hDM

/-- The executable Eq. (48) choice used by Corollary D.4.  Its denominator
simultaneously enforces the smoothness restriction and `2γμ ≤ p`. -/
noncomputable def onlinePLDensityCanonicalStepsize
    (L ℒ p ω : ℝ) (mu : PositivePLParameter) (n b0 : Count) :
    PositiveStepsize :=
  ⟨1 / max (2 * (mu : ℝ) / p)
      (max 1 (L + Real.sqrt ((2 * (1 - p)) / (p * n.1) *
        (ω * L ^ 2 + (1 + ω) * ℒ ^ 2 / b0.1)))), by
    apply one_div_pos.mpr
    exact lt_of_lt_of_le zero_lt_one
      ((le_max_left 1 _).trans (le_max_right _ _))⟩

end MARINA
