import Algorithms.Unverified.MARINA.Part003
import Algorithms.Unverified.MARINA.Part004.Part002
import Algorithms.Unverified.MARINA.Part004.Part003.Part001

-- Aggregator for `Algorithms.Unverified.MARINA`. Source declarations live under `MARINA/`.

namespace MARINA

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-! ## Literal online moment boundary

Assumption 3.3 states only the workerwise fixed-query unbiasedness and
bounded-variance equations.  Adaptive-query regularity used by the generated
Algorithm 3 proofs is kept separate below. -/

set_option maxHeartbeats 3000000 in
/-- Complete executable Eq. (46) at one time.  This is the sampled-initializer
analogue of the proof-exact recurrence: all moments are taken under
`onlinePathLaw`, and Assumption 3.2 is applied to `onlineProcess` itself. -/
theorem online_estimator_recurrence_46_executable_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
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
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  have hRefresh :=
    onlineExecutable_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
      A x0 hBatch σ hLiteral hRegularity hSmooth.1 k
  have hRefreshIndep :=
    onlineExecutable_refresh_error_sq_indep_refresh_of_lawRegularity
      A x0 hBatch σ hLiteral hRegularity k
  have hNonrefresh :=
    onlineExecutable_nonrefresh_branch_moments_of_genuine_assumption32_and_lawRegularity
      A x0 Llocal ℒlocal σ ω hSmooth hLiteral hBatch hAssumption32
        hRegularity hQuantizer k hError hStep
  let residual := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem (path.2 k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let refreshError := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
      stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1
  let refreshSq := fun path ↦ ‖refreshError path‖ ^ 2
  let nonrefreshSq := fun path ↦ ‖residual path + innovation path‖ ^ 2
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n ↦
      A.quantizer.apply
        (onlineBatchDifference A.problem (path.2 k).2.1.2 i xN s.x)
        ((path.2 k).2.2 i)
    have hdiffAvg : average (fun i : Worker n ↦
        localGradientDifference P i xN s.x) =
        globalGradient P xN - globalGradient P s.x := by
      rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
        globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : innovation path =
        average q - average (fun i : Worker n ↦
          localGradientDifference P i xN s.x) := by
      dsimp [innovation, q, xN, s]
      rw [show (run (k + 1) path).x = xN by rfl]
      unfold average SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n ↦
          onlineWorkerEstimator A (onlineDriverOfRoundNoise (path.2 k)) s i) -
          globalGradient P xN := by rfl
    cases h : branch path with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        change average (fun i : Worker n ↦ s.g + q i) -
            globalGradient P xN = residual path + innovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [if_true]
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
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hbranchMeas : Measurable branch := by dsimp [branch]; fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    let evalCoin := fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      (stream k).1
    calc
      Measure.map branch law = Measure.map evalCoin (Measure.map Prod.snd law) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · dsimp [evalCoin]; fun_prop
        · exact measurable_snd
      _ = Measure.map evalCoin
          (SOptLib.iidStreamLaw (onlineRoundLaw (b := b) (b0 := b0) A)) := by
        rw [show Measure.map Prod.snd law =
            SOptLib.iidStreamLaw (onlineRoundLaw (b := b) (b0 := b0) A) by
          dsimp [law, onlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = Measure.map Prod.fst (onlineRoundLaw (b := b) (b0 := b0) A) := by
        rw [show Measure.map evalCoin
            (SOptLib.iidStreamLaw (onlineRoundLaw (b := b) (b0 := b0) A)) =
              Measure.map Prod.fst
                (Measure.map (fun stream : ℕ →
                    OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
                  (SOptLib.iidStreamLaw
                    (onlineRoundLaw (b := b) (b0 := b0) A))) by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · exact measurable_fst
          · exact measurable_pi_apply k]
        rw [SOptLib.iidStreamLaw_map_eval]
      _ = _ := by simp [onlineRoundLaw]
  have htrueMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({true} : Set Bool) = A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
    simp [PMF.bernoulli_apply]
  have hfalseMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({false} : Set Bool) = 1 - A.refreshProbability := by
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
  let phiR : ℝ → Bool → ℝ := fun z c ↦ if c then z else 0
  let budgetR : ℝ → ℝ := fun z ↦ A.refreshProbability * z
  let phiN : ℝ → Bool → ℝ := fun z c ↦ if c = false then z else 0
  let budgetN : ℝ → ℝ := fun z ↦ (1 - A.refreshProbability) * z
  have hrefreshInt : Integrable refreshSq law := by
    simpa [refreshSq, refreshError, P, run, law] using hRefresh.1
  have hnonrefreshInt : Integrable nonrefreshSq law := by
    simpa [nonrefreshSq, residual, innovation, P, run, law] using
      hNonrefresh.2.2.2.1
  have hrefreshIndep : ProbabilityTheory.IndepFun refreshSq branch law := by
    simpa [refreshSq, refreshError, branch, P, run, law] using hRefreshIndep
  have hnonrefreshIndep : ProbabilityTheory.IndepFun nonrefreshSq branch law := by
    simpa [nonrefreshSq, residual, innovation, branch, P, run, law] using
      hNonrefresh.2.2.2.2.2
  have hgateRInt : Integrable
      (fun path ↦ phiR (refreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = true} :=
      hbranchMeas (measurableSet_singleton true)
    have hp := Integrable.piecewise hs hrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiR, Set.piecewise] using hp
  have hgateNInt : Integrable
      (fun path ↦ phiN (nonrefreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranchMeas (measurableSet_singleton false)
    have hp := Integrable.piecewise hs hnonrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiN, Set.piecewise] using hp
  have hbudgetRInt : Integrable (fun path ↦ budgetR (refreshSq path)) law := by
    simpa [budgetR] using hrefreshInt.const_mul A.refreshProbability
  have hbudgetNInt : Integrable (fun path ↦ budgetN (nonrefreshSq path)) law := by
    simpa [budgetN] using hnonrefreshInt.const_mul (1 - A.refreshProbability)
  have hgateR :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := refreshSq) (Y := branch) (φ := phiR) (B := budgetR)
      (by exact (show Measurable (Function.uncurry phiR) by
        dsimp [phiR, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton true)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budgetR by dsimp [budgetR]; fun_prop)
        |>.aestronglyMeasurable)
      hrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hrefreshIndep hbranchLaw hgateRInt hbudgetRInt
      (fun z ↦ by
        rw [MeasureTheory.integral_fintype]
        · simp [phiR, budgetR, htrueMass]
        · exact Integrable.of_finite)
  have hgateN :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := nonrefreshSq) (Y := branch) (φ := phiN) (B := budgetN)
      (by exact (show Measurable (Function.uncurry phiN) by
        dsimp [phiN, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton false)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budgetN by dsimp [budgetN]; fun_prop)
        |>.aestronglyMeasurable)
      hnonrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hnonrefreshIndep hbranchLaw hgateNInt hbudgetNInt
      (fun z ↦ by
        rw [MeasureTheory.integral_fintype]
        · simp [phiN, budgetN, hfalseMass]
        · exact Integrable.of_finite)
  have hnextSq : ∀ path, ‖nextResidual path‖ ^ 2 =
      phiR (refreshSq path) (branch path) +
        phiN (nonrefreshSq path) (branch path) := by
    intro path
    rw [hdecomp]
    cases hb : branch path <;>
      simp [phiR, phiN, refreshSq, nonrefreshSq]
  have hnextInt : Integrable (fun path ↦ ‖nextResidual path‖ ^ 2) law :=
    (hgateRInt.add hgateNInt).congr
      (Filter.Eventually.of_forall fun path ↦ (hnextSq path).symm)
  have hnextEq : estimatorErrorMoment P run law (k + 1) =
      (∫ path, phiR (refreshSq path) (branch path) ∂law) +
        ∫ path, phiN (nonrefreshSq path) (branch path) ∂law := by
    unfold estimatorErrorMoment
    calc
      (∫ path,
          ‖(run (k + 1) path).g - globalGradient P (run (k + 1) path).x‖ ^ 2
          ∂law) = ∫ path,
            (phiR (refreshSq path) (branch path) +
              phiN (nonrefreshSq path) (branch path)) ∂law := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hnextSq
      _ = _ := integral_add hgateRInt hgateNInt
  refine ⟨?_, hError, hStep, ?_⟩
  · simpa [EstimatorErrorMomentWellDefined, nextResidual, P, run, law] using
      hnextInt
  · rw [hnextEq]
    calc
      (∫ path, phiR (refreshSq path) (branch path) ∂law) +
            ∫ path, phiN (nonrefreshSq path) (branch path) ∂law ≤
          (∫ path, budgetR (refreshSq path) ∂law) +
            ∫ path, budgetN (nonrefreshSq path) ∂law :=
        add_le_add hgateR hgateN
      _ = A.refreshProbability * (∫ path, refreshSq path ∂law) +
          (1 - A.refreshProbability) *
            (∫ path, nonrefreshSq path ∂law) := by
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
          · simpa [refreshSq, refreshError, P, run, law] using hRefresh.2
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

set_option maxHeartbeats 3000000 in
/-- Simultaneous executable component `L²` closure and Eq. (46) history.  The
time-zero component is the sampled-initializer bound, rather than the
proof-exact zero-error initialization. -/
theorem onlineProcess_scalar_recurrence_components_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path ↦ (run k path).x) law ∧
    AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law ∧
    Integrable (fun path ↦ ‖(run k path).x - x0‖ ^ 2) law ∧
    Integrable (fun path ↦ ‖(run k path).g‖ ^ 2) law ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    ∀ j, j < k →
      estimatorErrorMoment P run law (j + 1) ≤
        (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
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
  have hState (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_literal_and_lawRegularity
        A x0 hBatch σ hLiteral hRegularity t
  have hGlobal : IsGradientLipschitz (globalObjective P)
      (rootMeanSquare Llocal) :=
    GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hAll : ∀ t,
      AEStronglyMeasurable (fun path ↦ (run t path).x) law ∧
      AEStronglyMeasurable
        (fun path ↦ (run t path).g - globalGradient P (run t path).x) law ∧
      Integrable (fun path ↦ ‖(run t path).x - x0‖ ^ 2) law ∧
      Integrable (fun path ↦ ‖(run t path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law t ∧
      StepMomentWellDefined run law t ∧
      ∀ j, j < t →
        estimatorErrorMoment P run law (j + 1) ≤
          (1 - A.refreshProbability) / n.1 *
              (ω * (rootMeanSquare Llocal) ^ 2 +
                (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
              stepMoment run law j +
            (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
            A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
    intro t
    induction t with
    | zero =>
        have h0 :=
          onlineProcess_scalar_recurrence_components_zero_of_literal_and_lawRegularity
            A x0 Llocal σ hSmooth hLiteral hRegularity hBatch
        refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1,
          h0.2.2.2.2.1, h0.2.2.2.2.2, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        have hRec :=
          online_estimator_recurrence_46_executable_of_literal_and_lawRegularity
            A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
              hAssumption32 hRegularity t ih.2.2.2.2.1 ih.2.2.2.2.2.1
        have hxNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).x) law :=
          ((measurable_state_x d).comp_aemeasurable
            (hState (t + 1))).aestronglyMeasurable
        have hgNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).g) law :=
          ((measurable_state_g d).comp_aemeasurable
            (hState (t + 1))).aestronglyMeasurable
        have hgradNext : AEStronglyMeasurable
            (fun path ↦ globalGradient P (run (t + 1) path).x) law :=
          ((measurable_gradient (globalObjective P)).comp_aemeasurable
            hxNext.aemeasurable).aestronglyMeasurable
        have hrNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).g -
              globalGradient P (run (t + 1) path).x) law :=
          hgNext.sub hgradNext
        have hxl2Next : Integrable
            (fun path ↦ ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
          have hg : AEStronglyMeasurable (fun path ↦ (run t path).g) law := by
            have hsum := ih.2.1.add
              (((measurable_gradient (globalObjective P)).comp_aemeasurable
                ih.1.aemeasurable).aestronglyMeasurable)
            refine hsum.congr (Filter.Eventually.of_forall ?_)
            intro path
            change ((run t path).g - globalGradient P (run t path).x) +
              globalGradient P (run t path).x = (run t path).g
            abel
          have h := integrable_sq_norm_sub_smul_sub_const_of_l2
            (fun path ↦ (run t path).x) (fun path ↦ (run t path).g)
            x0 (A.stepSize : ℝ) ih.1 hg ih.2.2.1 ih.2.2.2.1
          simpa [run, onlineProcess_succ, onlineStep, primalStep_eq] using h
        have hglobalNext : Integrable
            (fun path ↦ ‖globalGradient P (run (t + 1) path).x‖ ^ 2) law := by
          apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
            x0 (globalGradient P) (rootMeanSquare Llocal)
              (fun path ↦ (run (t + 1) path).x) hxNext
          · simpa [norm_sub_rev] using hxl2Next
          · intro x y
            exact hGlobal.2 y x
        have hgl2Next : Integrable
            (fun path ↦ ‖(run (t + 1) path).g‖ ^ 2) law := by
          have hadd := integrable_sq_norm_add hrNext hgradNext
            (by simpa [EstimatorErrorMomentWellDefined, P, run, law] using hRec.1)
            hglobalNext
          apply hadd.congr
          filter_upwards [] with path
          congr 2
          abel
        have hsNext : StepMomentWellDefined run law (t + 1) := by
          have hscaled := integrable_sq_norm_const_smul
            (-(A.stepSize : ℝ)) hgl2Next
          simpa [StepMomentWellDefined, run, onlineProcess_succ,
            onlineStep, primalStep_eq] using hscaled
        have hHistory : ∀ j, j < t + 1 →
            estimatorErrorMoment P run law (j + 1) ≤
              (1 - A.refreshProbability) / n.1 *
                  (ω * (rootMeanSquare Llocal) ^ 2 +
                    (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
                  stepMoment run law j +
                (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
                A.refreshProbability * varianceAggregateSq σ /
                  (n.1 * b.1) := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjt | rfl
          · exact ih.2.2.2.2.2.2 j hjt
          · exact hRec.2.2.2
        exact ⟨hxNext, hrNext, hxl2Next, hgl2Next, hRec.1, hsNext,
          hHistory⟩
  exact hAll k

/-- The executable homogeneous initializer moment is exactly its batch-law
expectation under literal Assumption 3.3.  This is the constant-worker-batch
specialization of the heterogeneous identity, and uses only differentiability
of the averaged local objectives to establish integrability. -/
theorem online_executable_initial_error_moment_eq_expected_of_literal
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i))
    (hBatch : OnlineBatchAdmissible b b0) :
    estimatorErrorMoment (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) 0 =
      expectedOnlineInitialEstimatorErrorSq (b := b) A x0 := by
  have h :=
    heterogeneous_online_executable_initial_error_moment_eq_expected_of_literal
      (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0)
      A x0 σ hLiteral hDiff
  simpa [onlinePathLaw_eq_heterogeneousOnlinePathLaw_const,
    onlineProcess_eq_heterogeneousOnlineProcess_const,
    expectedOnlineInitialEstimatorErrorSq,
    expectedHeterogeneousOnlineInitialEstimatorErrorSq] using h

/-- Internal executable scalar closure consumed by both the nonconvex and PL
telescopes.  Public source boundaries discharge it from either the preserved
every-path compatibility theorem or the source generated conditional kernel. -/
def OnlineProcessScalarRecurrenceClosure
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hBatch : OnlineBatchAdmissible b b0) : Prop :=
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  ∀ k,
    AEStronglyMeasurable (fun path ↦ (run k path).x) law ∧
    AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law ∧
    Integrable (fun path ↦ ‖(run k path).x - x0‖ ^ 2) law ∧
    Integrable (fun path ↦ ‖(run k path).g‖ ^ 2) law ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    ∀ j, j < k →
      estimatorErrorMoment P run law (j + 1) ≤
        (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1)

set_option linter.unnecessarySeqFocus false in
/-- Executable D.3 from the exact scalar recurrence closure.  This isolates
the convergence telescope from the particular source route used to establish
adaptive-law well-posedness. -/
theorem online_D3_initialization_corrected_of_scalar_recurrence
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hClosure : OnlineProcessScalarRecurrenceClosure
      A x0 Llocal ℒlocal σ ω hBatch)
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
  have hComponents (k : ℕ) := by
    simpa [OnlineProcessScalarRecurrenceClosure] using hClosure k
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
      (online_executable_initial_error_moment_eq_expected_of_literal
        A x0 σ hLiteral hSmooth.1 hBatch)
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

/-- Compatibility boundary retaining the historical every-path Assumption 3.2
and all-query-law interface.  The proof now factors through the same scalar
closure used by the source generated-kernel route. -/
theorem Theorem_D3_online_VR_nonconvex_initialization_corrected_of_literal_and_lawRegularity
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    Integrable (fun z ↦
        ‖globalGradient (onlineLocalProblem A.problem)
          (uniformOutput (K := K)
            (onlineProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2)
        (uniformOutputExperimentLaw
          (onlinePathLaw (b := b) (b0 := b0) A) K) ∧
      (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (onlineProcess (b := b) (b0 := b0) A x0 hBatch) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (onlinePathLaw (b := b) (b0 := b0) A) K) ≤
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
            (A.stepSize * K.1) +
          expectedOnlineInitialEstimatorErrorSq (b := b) A x0 /
            (A.refreshProbability * K.1) +
          varianceAggregateSq σ / (n.1 * b.1) := by
  apply online_D3_initialization_corrected_of_scalar_recurrence
    A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hLiteral hQuantizer hBatch
  · intro k
    exact
      onlineProcess_scalar_recurrence_components_of_literal_and_lawRegularity
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          hAssumption32 hRegularity k
  · exact hStep

set_option linter.unnecessarySeqFocus false in
set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- B-track correction of Theorem D.4 for the executable minibatch-at-`x⁰`
initialization.  The decaying additional term is exactly the initial
estimator-error component of the source Lyapunov function. -/
theorem online_D4_initialization_corrected_of_scalar_recurrence
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hClosure : OnlineProcessScalarRecurrenceClosure
      A x0 Llocal ℒlocal σ ω hBatch)
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
  have hComponents (k : ℕ) := by
    simpa [OnlineProcessScalarRecurrenceClosure, P, run, law] using
      hClosure k
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
      (online_executable_initial_error_moment_eq_expected_of_literal
        A x0 σ hLiteral hSmooth.1 hBatch)
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

/-- Compatibility boundary retaining the former every-path Assumption 3.2
interface.  The proof now factors through the discharged scalar-recurrence
core, so callers of the established declaration keep their exact contract. -/
theorem Theorem_D4_online_VR_PL_initialization_corrected_of_literal_and_lawRegularity
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path ↦
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
  apply online_D4_initialization_corrected_of_scalar_recurrence
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hLiteral hPL
      hQuantizer hBatch
  · intro k
    exact
      onlineProcess_scalar_recurrence_components_of_literal_and_lawRegularity
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          hAssumption32 hRegularity k
  · exact hStep



/-- The executable D.3 boundary implies the requested nonconvex accuracy once
the iteration, initialization, and steady-state terms fit the accuracy budget.
The initial-error term is discharged from the canonical minibatch law rather
than postulated. -/
theorem onlineExecutableNonconvexAccuracy_of_budget_of_literal_and_lawRegularity
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (ε : Accuracy)
    (hBudget :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        (varianceAggregateSq σ / (n.1 * b.1)) /
          (A.refreshProbability * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) ≤ (ε : ℝ) ^ 2) :
    NonconvexAccuracy K (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ε := by
  unfold NonconvexAccuracy
  have hBoundary :=
    Theorem_D3_online_VR_nonconvex_initialization_corrected_of_literal_and_lawRegularity
      (K := K) A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hLiteral
      hQuantizer hBatch hAssumption32 hRegularity hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedOnlineInitialEstimatorErrorSq_le_of_literal
    (b := b) A x0 σ hLiteral hSmooth.1
  have hdenom : 0 ≤ (A.refreshProbability : ℝ) * K.1 :=
    mul_nonneg A.refresh_admissible.1.le (by positivity)
  have hInitialDiv :
      expectedOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) ≤
        (varianceAggregateSq σ / (n.1 * b.1)) /
          (A.refreshProbability * K.1) :=
    div_le_div_of_nonneg_right hInitial hdenom
  calc
    2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        expectedOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) ≤
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        (varianceAggregateSq σ / (n.1 * b.1)) /
          (A.refreshProbability * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) := by gcongr
    _ ≤ (ε : ℝ) ^ 2 := hBudget

/-- The analogous executable D.4 bridge.  The coefficient of the initial
estimator error is nonnegative by the PL stepsize condition, so the proved
minibatch variance bound can be substituted monotonically. -/
theorem onlineExecutablePLAccuracy_of_budget_of_literal_and_lawRegularity
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0)
    (ε : Accuracy)
    (hBudget :
      (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability *
            (varianceAggregateSq σ / (n.1 * b.1)) +
        varianceAggregateSq σ / (n.1 * b.1 * μ) ≤ (ε : ℝ)) :
    PLAccuracy K (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) xStar ε := by
  unfold PLAccuracy
  have hBoundary :=
    Theorem_D4_online_VR_PL_initialization_corrected_of_literal_and_lawRegularity
      (K := K) A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hLiteral hPL hQuantizer hBatch hAssumption32 hRegularity hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedOnlineInitialEstimatorErrorSq_le_of_literal
    (b := b) A x0 σ hLiteral hSmooth.1
  have hContraction : 0 ≤ 1 - (A.stepSize : ℝ) * (μ : ℝ) := by
    apply sub_nonneg.mpr
    have hp1 := A.refresh_admissible.2
    nlinarith [hStep.2]
  have hCoefficient : 0 ≤
      (1 - (A.stepSize : ℝ) * (μ : ℝ)) ^ K.1 * A.stepSize /
        A.refreshProbability :=
    div_nonneg
      (mul_nonneg (pow_nonneg hContraction K.1) A.stepSize.property.le)
      A.refresh_admissible.1.le
  have hInitialMul := mul_le_mul_of_nonneg_left hInitial hCoefficient
  calc
    (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability * expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
        varianceAggregateSq σ / (n.1 * b.1 * μ) ≤
      (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability * (varianceAggregateSq σ / (n.1 * b.1)) +
        varianceAggregateSq σ / (n.1 * b.1 * μ) := by gcongr
    _ ≤ (ε : ℝ) := hBudget

/-- Accuracy-family form of the executable D.3 initialization correction.
All varying batch types and laws are instantiated pointwise, and the only
extra hypothesis is the displayed scalar budget obtained by allocating the
source optimization, initial-estimator, and variance terms. -/
theorem onlineExecutableNonconvexAccuracy_family_of_budget_of_literal_and_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAssumption32 : ∀ ε, OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess A x0 (hBatch ε)) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (hBudget : ∀ ε,
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * (K ε).1) +
        (varianceAggregateSq σ / (n.1 * (b ε).1)) /
          (A.refreshProbability * (K ε).1) +
        varianceAggregateSq σ / (n.1 * (b ε).1) ≤ (ε : ℝ) ^ 2) :
    ∀ ε, NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ε := by
  intro ε
  exact onlineExecutableNonconvexAccuracy_of_budget_of_literal_and_lawRegularity A x0 Llocal ℒlocal σ
    ω fStar hLower hSmooth hLiteral hQuantizer (hBatch ε)
    (hAssumption32 ε) hRegularity hStep ε (hBudget ε)

/-- Accuracy-family form of the executable D.4 initialization correction.
The decaying initial-estimator term is budgeted on the same sampled path law
as the terminal iterate and remains separate from proof-exact convergence. -/
theorem onlineExecutablePLAccuracy_family_of_budget_of_literal_and_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAssumption32 : ∀ ε, OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess A x0 (hBatch ε)) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0)
    (hBudget : ∀ ε,
      (1 - A.stepSize * μ) ^ (K ε).1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ (K ε).1 * A.stepSize /
          A.refreshProbability *
            (varianceAggregateSq σ / (n.1 * (b ε).1)) +
        varianceAggregateSq σ / (n.1 * (b ε).1 * μ) ≤ (ε : ℝ)) :
    ∀ ε, PLAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) xStar ε := by
  intro ε
  exact onlineExecutablePLAccuracy_of_budget_of_literal_and_lawRegularity A x0 xStar Llocal ℒlocal σ
    ω fStar μ hLower hSmooth hLiteral hPL hQuantizer
    (hBatch ε) (hAssumption32 ε) hRegularity hStep ε (hBudget ε)


/-- Supplied-stepsize executable D.3 with measured costs.  The refresh batch
is inflated using `2 σ² / p`, rather than merely `σ²`: this pays for
both the steady-state variance and the sampled-initializer error divided by
`p K`.  Thus the convergence field and both cost integrals describe the same
`onlineProcess` experiment; no cost is transferred from the proof-exact
initializer.  `OnlineCommunicationAELawRegularity` is the law-scoped
well-posedness interface used for the adaptive communication observable. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let iterationScale := fun ε : Accuracy =>
      1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let V : ℝ := varianceAggregateSq σ
  let chosenBatch : Accuracy → Count :=
    onlineNonconvexBatchScheduleFromBase n b0
      (2 * V / A.refreshProbability) baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let iterationScale : Accuracy → ℝ := fun ε =>
    1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
  let K : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (4 * Δ /
      ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
  have hV : 0 ≤ V := by
    dsimp [V, varianceAggregateSq, meanSquare, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (hLower x0)
  have hEffectiveVariance : 0 ≤ 2 * V / A.refreshProbability := by
    positivity
  have hBatch : ∀ ε, OnlineBatchAdmissible (chosenBatch ε) b0 := by
    intro ε
    simpa [chosenBatch] using
      onlineNonconvexBatchScheduleFromBase_admissible n b0
        (2 * V / A.refreshProbability) baseBatch ε
  have hFloor (eps : Accuracy) :
      V / (n.1 * (chosenBatch eps).1) ≤
        A.refreshProbability * (eps : ℝ) ^ 2 / 4 := by
    have hEff := onlineNonconvexBatchScheduleFromBase_variance_floor
      n b0 (2 * V / A.refreshProbability) hEffectiveVariance
        baseBatch eps
    have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hb : ((chosenBatch eps).1 : ℝ) ≠ 0 := by
      exact_mod_cast (chosenBatch eps).2.ne'
    have hpne : A.refreshProbability ≠ 0 := ne_of_gt hp
    dsimp [chosenBatch] at hEff ⊢
    rw [div_le_iff₀ (by positivity : 0 < (n.1 : ℝ) *
      (onlineNonconvexBatchScheduleFromBase n b0
        (2 * V / A.refreshProbability) baseBatch eps).1)] at hEff ⊢
    field_simp [hpne, hn, hb] at hEff ⊢
    nlinarith
  have hOptimizationHalf (eps : Accuracy) :
      2 * Δ / ((A.stepSize : ℝ) * (K eps).1) ≤
        (eps : ℝ) ^ 2 / 2 := by
    have hKpos : 0 < ((K eps).1 : ℝ) := by exact_mod_cast (K eps).2
    have hγpos : 0 < (A.stepSize : ℝ) := A.stepSize.property
    have hBudget := div_natCast_max_one_ceil_div_le
      (4 * Δ) ((A.stepSize : ℝ) * (eps : ℝ) ^ 2)
        (mul_pos hγpos (sq_pos_of_pos eps.property))
    have hBudget' :
        4 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ)) ≤
          (eps : ℝ) ^ 2 := by
      rw [div_le_iff₀ (mul_pos hγpos hKpos)]
      have hRaw : 4 * Δ / ((K eps).1 : ℝ) ≤
          (A.stepSize : ℝ) * (eps : ℝ) ^ 2 := by
        simpa [K] using hBudget
      rw [div_le_iff₀ hKpos] at hRaw
      nlinarith
    calc
      2 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ)) =
          (1 / 2 : ℝ) *
            (4 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ))) := by
              field_simp [ne_of_gt hγpos, ne_of_gt hKpos]
              all_goals ring
      _ ≤ (1 / 2 : ℝ) * (eps : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hBudget' (by norm_num)
      _ = (eps : ℝ) ^ 2 / 2 := by ring
  have hInitialQuarter (eps : Accuracy) :
      (V / (n.1 * (chosenBatch eps).1)) /
          (A.refreshProbability * (K eps).1) ≤
        (eps : ℝ) ^ 2 / 4 := by
    have hKone : (1 : ℝ) ≤ (K eps).1 := by
      exact_mod_cast (K eps).2
    rw [div_le_iff₀ (mul_pos hp (by positivity : 0 < ((K eps).1 : ℝ)))]
    have hFloor' := hFloor eps
    calc
      V / (n.1 * (chosenBatch eps).1) ≤
          A.refreshProbability * (eps : ℝ) ^ 2 / 4 := hFloor'
      _ ≤ (A.refreshProbability * (eps : ℝ) ^ 2 / 4) *
          (K eps).1 :=
        le_mul_of_one_le_right (by positivity) hKone
      _ = (eps : ℝ) ^ 2 / 4 *
          (A.refreshProbability * (K eps).1) := by ring
  have hAccuracy : ∀ eps, NonconvexAccuracy (K eps)
      (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch eps))
      (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) eps := by
    apply onlineExecutableNonconvexAccuracy_family_of_budget_of_literal_and_lawRegularity
      A x0 chosenBatch K Llocal ℒlocal σ ω fStar hLower hSmooth
        hLiteral hQuantizer hBatch
    · intro eps
      simpa [chosenBatch] using hAssumption32 eps
    · exact hRegularity
    · exact hStep
    · intro eps
      have hSteadyQuarter :
          V / (n.1 * (chosenBatch eps).1) ≤ (eps : ℝ) ^ 2 / 4 :=
        (hFloor eps).trans (by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left (sq_nonneg _) hp1)
      calc
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
              ((A.stepSize : ℝ) * (K eps).1) +
            (varianceAggregateSq σ / (n.1 * (chosenBatch eps).1)) /
              (A.refreshProbability * (K eps).1) +
            varianceAggregateSq σ / (n.1 * (chosenBatch eps).1) ≤
            (eps : ℝ) ^ 2 / 2 + (eps : ℝ) ^ 2 / 4 +
              (eps : ℝ) ^ 2 / 4 := by
          simpa [V, Δ] using
            (add_le_add (add_le_add (hOptimizationHalf eps)
              (hInitialQuarter eps)) hSteadyQuarter)
        _ = (eps : ℝ) ^ 2 := by ring
  have hKBound (eps : Accuracy) : ((K eps).1 : ℝ) ≤
      2 * iterationScale eps := by
    let q : ℝ := 4 * Δ / ((A.stepSize : ℝ) * (eps : ℝ) ^ 2)
    have hq : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg A.stepSize.property.le (sq_nonneg _))
    have hceil := natCast_max_one_ceil_le_add_two q hq
    have hscale : iterationScale eps = 1 + q := by
      simp [iterationScale, q]
    rw [show ((K eps).1 : ℝ) =
      ((max 1 (Nat.ceil q) : ℕ) : ℝ) by simp [K, q]]
    rw [hscale]
    linarith
  have hScalePos (eps : Accuracy) : 0 < iterationScale eps := by
    dsimp [iterationScale]
    have : 0 ≤ 4 * Δ /
        ((A.stepSize : ℝ) * (eps : ℝ) ^ 2) := by
      exact div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg A.stepSize.property.le (sq_nonneg _))
    linarith
  have hKBigO : AccuracyBigO (fun eps => ((K eps).1 : ℝ))
      iterationScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro eps
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((K eps).1 : ℝ)), Real.norm_eq_abs,
      abs_of_pos (hScalePos eps)]
    exact hKBound eps
  have hEndpoints : ThreeEndpointComplexity K
      (fun eps => NonconvexAccuracy (K eps)
        (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch eps))
        (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) eps)
      iterationScale
      (fun eps => onlineOracleCallCount (chosenBatch eps) b0 (K eps)
        A.refreshProbability)
      (fun eps => (chosenBatch eps).1 + iterationScale eps *
        (A.refreshProbability * (chosenBatch eps).1 +
          2 * (1 - A.refreshProbability) * b0.1))
      (fun eps => allWorkerCommunicationCount d (K eps)
        A.refreshProbability (expectedDensity A.quantizer))
      (fun eps => d.1 + iterationScale eps *
        (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
    unfold ThreeEndpointComplexity
    refine ⟨hAccuracy, Or.inr hKBigO, ?_, ?_⟩
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * (chosenBatch eps).1 +
        2 * (1 - A.refreshProbability) * b0.1
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            (by positivity))
      have hactual : 0 ≤ onlineOracleCallCount (chosenBatch eps) b0
          (K eps) A.refreshProbability := by
        unfold onlineOracleCallCount
        exact add_nonneg (by positivity)
          (mul_nonneg (by positivity) hpayload)
      have htarget : 0 < (chosenBatch eps).1 +
          iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast (chosenBatch eps).2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (chosenBatch eps).1 + ((K eps).1 : ℝ) * payload ≤
        2 * ((chosenBatch eps).1 + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * expectedDensity A.quantizer
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr hp1)
            (expectedDensity_nonneg_of_unbiased hQuantizer))
      have hactual : 0 ≤ allWorkerCommunicationCount d (K eps)
          A.refreshProbability (expectedDensity A.quantizer) := by
        unfold allWorkerCommunicationCount
        positivity
      have htarget : 0 < (d.1 : ℝ) + iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast d.2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (d.1 : ℝ) + ((K eps).1 : ℝ) * payload ≤
        2 * ((d.1 : ℝ) + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
  refine ⟨K, ?_⟩
  apply onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 chosenBatch hBatch
  · intro eps
    exact onlineCommunicationAELawRegularity_of_literal_and_lawRegularity
      A x0 (hBatch eps) σ hLiteral hRegularity
  · exact hQuantizer
  · exact hEndpoints

/-- Supplied-stepsize executable D.4 with measured costs.  The geometric
horizon allocates one quarter of the target to contraction.  The source
batch schedule allocates one half to the stationary variance floor, while
`2 γ μ ≤ p` makes the sampled-initializer contribution at most the
remaining quarter.  Consequently the accuracy field, oracle integral, and
communication integral all refer to the same sampled-initializer
`onlineProcess` experiment. -/
theorem onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let iterationScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δ / (ε : ℝ)) /
        ((A.stepSize : ℝ) * (μ : ℝ)))
    ∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar chosenBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let V : ℝ := varianceAggregateSq σ
  let chosenBatch : Accuracy → Count :=
    onlinePLBatchScheduleFromBase n b0 V μ baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 -
    globalObjective (onlineLocalProblem A.problem) xStar
  let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
  let contractionScale : Accuracy → ℝ := fun ε =>
    max 0 (Real.log (4 * Δ / (ε : ℝ)) / c)
  let iterationScale : Accuracy → ℝ := fun ε => 1 + contractionScale ε
  let K : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (contractionScale ε)), by omega⟩
  have hV : 0 ≤ V := by
    dsimp [V, varianceAggregateSq, meanSquare, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (hPL.1 x0)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos A.stepSize.property μ.property
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith [hStep.2, hp1]
  have hBatch : ∀ ε, OnlineBatchAdmissible (chosenBatch ε) b0 := by
    intro ε
    simpa [chosenBatch] using
      onlinePLBatchScheduleFromBase_admissible n b0 V μ baseBatch ε
  have hFloor (eps : Accuracy) :
      V / (n.1 * (chosenBatch eps).1 * μ) ≤ (eps : ℝ) / 2 := by
    simpa [chosenBatch] using
      onlinePLBatchScheduleFromBase_variance_floor n b0 V μ hV
        μ.property baseBatch eps
  have hContractQuarter (eps : Accuracy) :
      (1 - c) ^ (K eps).1 * Δ ≤ (eps : ℝ) / 4 := by
    rcases hΔ.eq_or_lt with hΔzero | hΔpos
    · calc
        (1 - c) ^ (K eps).1 * Δ = 0 := by rw [← hΔzero]; ring
        _ ≤ (eps : ℝ) / 4 := div_nonneg eps.property.le (by norm_num)
    · by_cases hsmall : (eps : ℝ) < 4 * Δ
      · have hratio : 1 < 4 * Δ / (eps : ℝ) :=
          (one_lt_div eps.property).2 hsmall
        have hlogPos : 0 < Real.log (4 * Δ / (eps : ℝ)) :=
          Real.log_pos hratio
        have hraw : 0 ≤ Real.log (4 * Δ / (eps : ℝ)) / c :=
          div_nonneg hlogPos.le hc.le
        have hScalar := positive_geometric_ceiling_schedule
          (4 * Δ) c 1 (mul_pos (by norm_num) hΔpos) hc hc1
            (by norm_num)
        have hFour :
            (1 - c) ^ (K eps).1 * (4 * Δ) ≤ (eps : ℝ) := by
          simpa [K, contractionScale, max_eq_right hraw] using hScalar.1 eps
        nlinarith [pow_nonneg (sub_nonneg.mpr hc1) (K eps).1]
      · have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
        have hbaseOne : 1 - c ≤ 1 := by linarith [hc]
        calc
          (1 - c) ^ (K eps).1 * Δ ≤ 1 * Δ :=
            mul_le_mul_of_nonneg_right
              (pow_le_one₀ hbase hbaseOne) hΔ
          _ = Δ := one_mul Δ
          _ ≤ (eps : ℝ) / 4 := by linarith
  have hInitialQuarter (eps : Accuracy) :
      (1 - c) ^ (K eps).1 * (A.stepSize : ℝ) /
          A.refreshProbability * (V / (n.1 * (chosenBatch eps).1)) ≤
        (eps : ℝ) / 4 := by
    have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
    have hbaseOne : 1 - c ≤ 1 := by linarith [hc]
    have hpow : (1 - c) ^ (K eps).1 ≤ 1 :=
      pow_le_one₀ hbase hbaseOne
    have hratio : (A.stepSize : ℝ) * (μ : ℝ) /
        A.refreshProbability ≤ 1 / 2 := by
      rw [div_le_iff₀ hp]
      nlinarith [hStep.2]
    have hFloorNonneg : 0 ≤ V / (n.1 * (chosenBatch eps).1 * μ) := by
      exact div_nonneg hV (mul_nonneg
        (mul_nonneg (by positivity) (by positivity)) μ.property.le)
    calc
      (1 - c) ^ (K eps).1 * (A.stepSize : ℝ) /
            A.refreshProbability * (V / (n.1 * (chosenBatch eps).1)) =
          ((1 - c) ^ (K eps).1 *
            ((A.stepSize : ℝ) * (μ : ℝ) /
              A.refreshProbability)) *
            (V / (n.1 * (chosenBatch eps).1 * μ)) := by
              field_simp [ne_of_gt hp, ne_of_gt μ.property]
      _ ≤ (1 * (1 / 2 : ℝ)) *
            (V / (n.1 * (chosenBatch eps).1 * μ)) := by
          gcongr
      _ ≤ (eps : ℝ) / 4 := by
          nlinarith [hFloor eps]
  have hAccuracy : ∀ eps, PLAccuracy (K eps)
      (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch eps))
      (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) xStar eps := by
    apply onlineExecutablePLAccuracy_family_of_budget_of_literal_and_lawRegularity
      A x0 xStar chosenBatch K Llocal ℒlocal σ ω fStar μ hLower
        hSmooth hLiteral hPL hQuantizer hBatch
    · intro eps
      simpa [chosenBatch] using hAssumption32 eps
    · exact hRegularity
    · exact hStep
    · intro eps
      calc
        (1 - A.stepSize * μ) ^ (K eps).1 *
              (globalObjective (onlineLocalProblem A.problem) x0 -
                globalObjective (onlineLocalProblem A.problem) xStar) +
            (1 - A.stepSize * μ) ^ (K eps).1 * A.stepSize /
              A.refreshProbability *
                (varianceAggregateSq σ /
                  (n.1 * (chosenBatch eps).1)) +
            varianceAggregateSq σ /
              (n.1 * (chosenBatch eps).1 * μ) ≤
            (eps : ℝ) / 4 + (eps : ℝ) / 4 + (eps : ℝ) / 2 := by
          simpa [V, Δ, c] using
            (add_le_add (add_le_add (hContractQuarter eps)
              (hInitialQuarter eps)) (hFloor eps))
        _ = (eps : ℝ) := by ring
  have hKBound (eps : Accuracy) : ((K eps).1 : ℝ) ≤
      2 * iterationScale eps := by
    have hq : 0 ≤ contractionScale eps := by
      dsimp [contractionScale]
      exact le_max_left _ _
    have hceil := natCast_max_one_ceil_le_add_two
      (contractionScale eps) hq
    change ((max 1 (Nat.ceil (contractionScale eps)) : ℕ) : ℝ) ≤
      2 * (1 + contractionScale eps)
    linarith
  have hScalePos (eps : Accuracy) : 0 < iterationScale eps := by
    dsimp [iterationScale]
    linarith [show 0 ≤ contractionScale eps by
      dsimp [contractionScale]
      exact le_max_left _ _]
  have hKBigO : AccuracyBigO (fun eps => ((K eps).1 : ℝ))
      iterationScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro eps
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((K eps).1 : ℝ)), Real.norm_eq_abs,
      abs_of_pos (hScalePos eps)]
    exact hKBound eps
  have hEndpoints : ThreeEndpointComplexity K
      (fun eps => PLAccuracy (K eps)
        (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch eps))
        (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) xStar eps)
      iterationScale
      (fun eps => onlineOracleCallCount (chosenBatch eps) b0 (K eps)
        A.refreshProbability)
      (fun eps => (chosenBatch eps).1 + iterationScale eps *
        (A.refreshProbability * (chosenBatch eps).1 +
          2 * (1 - A.refreshProbability) * b0.1))
      (fun eps => allWorkerCommunicationCount d (K eps)
        A.refreshProbability (expectedDensity A.quantizer))
      (fun eps => d.1 + iterationScale eps *
        (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
    unfold ThreeEndpointComplexity
    refine ⟨hAccuracy, Or.inr hKBigO, ?_, ?_⟩
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * (chosenBatch eps).1 +
        2 * (1 - A.refreshProbability) * b0.1
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            (by positivity))
      have hactual : 0 ≤ onlineOracleCallCount (chosenBatch eps) b0
          (K eps) A.refreshProbability := by
        unfold onlineOracleCallCount
        exact add_nonneg (by positivity)
          (mul_nonneg (by positivity) hpayload)
      have htarget : 0 < (chosenBatch eps).1 +
          iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast (chosenBatch eps).2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (chosenBatch eps).1 + ((K eps).1 : ℝ) * payload ≤
        2 * ((chosenBatch eps).1 + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * expectedDensity A.quantizer
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr hp1)
            (expectedDensity_nonneg_of_unbiased hQuantizer))
      have hactual : 0 ≤ allWorkerCommunicationCount d (K eps)
          A.refreshProbability (expectedDensity A.quantizer) := by
        unfold allWorkerCommunicationCount
        positivity
      have htarget : 0 < (d.1 : ℝ) + iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast d.2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (d.1 : ℝ) + ((K eps).1 : ℝ) * payload ≤
        2 * ((d.1 : ℝ) + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
  refine ⟨K, ?_⟩
  apply onlineExecutablePLMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 xStar chosenBatch hBatch
  · intro eps
    exact onlineCommunicationAELawRegularity_of_literal_and_lawRegularity
      A x0 (hBatch eps) σ hLiteral hRegularity
  · exact hQuantizer
  · exact hEndpoints

/-- Canonical Eq. (40) specialization of the executable D.3 measured-cost
family.  The equality premise records the source's canonical choice of the
reciprocal Eq. (40) bracket; unlike the upper-bound-only stepsize condition,
it is strong enough to replace `1 / A.stepSize` by that bracket in the
complexity scale.  The additive `1` is the nonempty-output-window
totalization and also covers the already-solved zero-gap case.

The refresh batch remains the initialization-corrected executable schedule
from the supplied-step theorem.  Thus the convergence statement and the two
cost integrals still concern the same sampled-initializer `onlineProcess`
experiment. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hCanonicalStep :
      (A.stepSize : ℝ) *
        (rootMeanSquare Llocal +
          Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let iterationScale := fun ε : Accuracy =>
      1 + Δ / (ε : ℝ) ^ 2 * bracket
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let chosenBatch : Accuracy → Count :=
    onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((1 - A.refreshProbability) /
      (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let suppliedScale : Accuracy → ℝ := fun ε =>
    1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
  let canonicalScale : Accuracy → ℝ := fun ε =>
    1 + Δ / (ε : ℝ) ^ 2 * bracket
  have hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0 := by
    unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition
    simpa [bracket] using hCanonicalStep.le
  obtain ⟨K, hMeasured⟩ :=
    onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularity
      A x0 baseBatch Llocal ℒlocal σ ω fStar hLower hSmooth hLiteral
        hQuantizer hAssumption32 hRegularity hStep
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (hLower x0)
  have hγ : 0 < (A.stepSize : ℝ) := A.stepSize.property
  have hBracket : 0 < bracket := by
    have hproduct : (A.stepSize : ℝ) * bracket = 1 := by
      simpa [bracket] using hCanonicalStep
    nlinarith
  have hScale : AccuracyBigO suppliedScale canonicalScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨4, Filter.Eventually.of_forall ?_⟩
    intro ε
    have hε : 0 < (ε : ℝ) := ε.property
    have hproduct : (A.stepSize : ℝ) * bracket = 1 := by
      simpa [bracket] using hCanonicalStep
    have hrewrite :
        4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2) =
          4 * (Δ / (ε : ℝ) ^ 2 * bracket) := by
      field_simp [ne_of_gt hγ, ne_of_gt hε]
      nlinarith
    have hterm : 0 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show 0 < suppliedScale ε by
        dsimp [suppliedScale]
        positivity),
      abs_of_pos (show 0 < canonicalScale ε by
        dsimp [canonicalScale]
        positivity)]
    dsimp [suppliedScale, canonicalScale]
    rw [hrewrite]
    nlinarith
  unfold OnlineExecutableNonconvexMeasuredCostComplexity
    OnlineMeasuredCostComplexity at hMeasured ⊢
  rcases hMeasured with ⟨hAccuracy, hIteration, hCosts⟩
  have hIteration' : AccuracyIterationBigO
      (fun ε => ((K ε).1 : ℝ)) canonicalScale := by
    rcases hIteration with hzero | hbig
    · let ε₁ : Accuracy := ⟨1, by norm_num⟩
      have hpos : 0 < suppliedScale ε₁ := by
        dsimp [suppliedScale]
        positivity
      exact (ne_of_gt hpos (hzero.1 ε₁)).elim
    · exact Or.inr (hbig.trans hScale)
  refine ⟨K, hAccuracy, hIteration', ?_⟩
  intro i
  rcases hCosts i with ⟨hOracleInt, hOracle, hCommInt, hComm⟩
  let oraclePayload : Accuracy → ℝ := fun ε =>
    A.refreshProbability * (chosenBatch ε).1 +
      2 * (1 - A.refreshProbability) * b0.1
  let communicationPayload : Accuracy → ℝ := fun _ =>
    A.refreshProbability * d.1 +
      (1 - A.refreshProbability) * expectedDensity A.quantizer
  have hOracleScale : AccuracyBigO
      (fun ε => (chosenBatch ε).1 + suppliedScale ε * oraclePayload ε)
      (fun ε => (chosenBatch ε).1 + canonicalScale ε * oraclePayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl
      (fun ε : Accuracy => ((chosenBatch ε).1 : ℝ)) accuracyToZero).add_add
        (hScale.mul (Asymptotics.isBigO_refl oraclePayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((chosenBatch ε).1 : ℝ)), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [oraclePayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg
              (mul_nonneg (by norm_num)
                (sub_nonneg.mpr A.refresh_admissible.2)) (by positivity))))]
  have hCommunicationScale : AccuracyBigO
      (fun ε => (d.1 : ℝ) + suppliedScale ε * communicationPayload ε)
      (fun ε => (d.1 : ℝ) + canonicalScale ε * communicationPayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl (fun _ : Accuracy => (d.1 : ℝ))
      accuracyToZero).add_add
        (hScale.mul
          (Asymptotics.isBigO_refl communicationPayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (d.1 : ℝ)),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [communicationPayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg (sub_nonneg.mpr A.refresh_admissible.2)
              (expectedDensity_nonneg_of_unbiased hQuantizer))))]
  refine ⟨hOracleInt, ?_, hCommInt, ?_⟩
  · apply hOracle.trans
    simpa [chosenBatch, suppliedScale, canonicalScale, oraclePayload]
      using hOracleScale
  · apply hComm.trans
    simpa [suppliedScale, canonicalScale, communicationPayload]
      using hCommunicationScale

/-- Canonical Eq. (48) specialization of the executable D.4 measured-cost
family.  The canonical denominator simultaneously enforces the doubled
smoothness bracket and `2 γ μ ≤ p`.  Consequently the supplied reciprocal
stepsize scale is controlled by the source factor
`max (1 / p) (bracket / μ)`.  The `max 0` logarithm and additive `1` are the
totalized finite-horizon form of the printed geometric rate. -/
theorem onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hCanonicalStep :
      (A.stepSize : ℝ) * max (2 * (μ : ℝ) / A.refreshProbability)
        (rootMeanSquare Llocal +
          Real.sqrt ((2 * (1 - A.refreshProbability)) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((2 * (1 - A.refreshProbability)) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let factor := max (1 / A.refreshProbability) (bracket / (μ : ℝ))
    let iterationScale := fun ε : Accuracy =>
      1 + factor * max 0 (Real.log (4 * Δ / (ε : ℝ)))
    ∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar chosenBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let chosenBatch : Accuracy → Count :=
    onlinePLBatchScheduleFromBase n b0 (varianceAggregateSq σ) μ baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 -
    globalObjective (onlineLocalProblem A.problem) xStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((2 * (1 - A.refreshProbability)) /
      (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let denominator : ℝ :=
    max (2 * (μ : ℝ) / A.refreshProbability) bracket
  let factor : ℝ := max (1 / A.refreshProbability) (bracket / (μ : ℝ))
  let suppliedScale : Accuracy → ℝ := fun ε =>
    1 + max 0 (Real.log (4 * Δ / (ε : ℝ)) /
      ((A.stepSize : ℝ) * (μ : ℝ)))
  let canonicalScale : Accuracy → ℝ := fun ε =>
    1 + factor * max 0 (Real.log (4 * Δ / (ε : ℝ)))
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hγ : 0 < (A.stepSize : ℝ) := A.stepSize.property
  have hμ : 0 < (μ : ℝ) := μ.property
  have hDenominator : 0 < denominator := by
    dsimp [denominator]
    exact (div_pos (mul_pos (by norm_num) hμ) hp).trans_le (le_max_left _ _)
  have hCanonical : (A.stepSize : ℝ) * denominator = 1 := by
    simpa [denominator, bracket] using hCanonicalStep
  have hFactor : 0 < factor := by
    dsimp [factor]
    exact (div_pos zero_lt_one hp).trans_le (le_max_left _ _)
  have hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0 := by
    unfold OnlineVRPLStepsizeCondition FiniteSumVRPLStepsizeCondition
    constructor
    · have hle : bracket ≤ denominator := by
        exact le_max_right _ _
      have hmul := mul_le_mul_of_nonneg_left hle hγ.le
      simpa [bracket] using hmul.trans_eq hCanonical
    · rw [← div_le_one hp]
      calc
        2 * (A.stepSize : ℝ) * (μ : ℝ) / A.refreshProbability =
            (A.stepSize : ℝ) *
              (2 * (μ : ℝ) / A.refreshProbability) := by ring
        _ ≤ (A.stepSize : ℝ) * denominator :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hγ.le
        _ = 1 := hCanonical
  obtain ⟨K, hMeasured⟩ :=
    onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularity
      A x0 xStar baseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
        hLiteral hPL hQuantizer hAssumption32 hRegularity hStep
  have hDenominatorFactor : denominator / (μ : ℝ) ≤ 2 * factor := by
    dsimp [denominator]
    rw [← max_div_div_right hμ.le]
    apply max_le
    · have heq : (2 * (μ : ℝ) / A.refreshProbability) /
          (μ : ℝ) = 2 * (1 / A.refreshProbability) := by
        field_simp [ne_of_gt hp, ne_of_gt hμ]
      rw [heq]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    · have hle : bracket / (μ : ℝ) ≤ factor := le_max_right _ _
      nlinarith [hFactor]
  have hScale : AccuracyBigO suppliedScale canonicalScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    let q : ℝ := Real.log (4 * Δ / (ε : ℝ))
    have hInv : 1 / (A.stepSize : ℝ) = denominator := by
      rw [div_eq_iff (ne_of_gt hγ)]
      simpa [mul_comm] using hCanonical.symm
    have hquotient : q / ((A.stepSize : ℝ) * (μ : ℝ)) =
        q * (denominator / (μ : ℝ)) := by
      calc
        q / ((A.stepSize : ℝ) * (μ : ℝ)) =
            q * (1 / (A.stepSize : ℝ)) / (μ : ℝ) := by
              field_simp [ne_of_gt hγ, ne_of_gt hμ]
        _ = q * denominator / (μ : ℝ) := by rw [hInv]
        _ = q * (denominator / (μ : ℝ)) := by ring
    have hround : max 0 (q / ((A.stepSize : ℝ) * (μ : ℝ))) ≤
        2 * factor * max 0 q := by
      rw [hquotient]
      by_cases hq : q ≤ 0
      · have hleft : q * (denominator / (μ : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hq
            (div_nonneg hDenominator.le hμ.le)
        rw [max_eq_left hleft, max_eq_left hq]
        positivity
      · have hqpos : 0 < q := lt_of_not_ge hq
        rw [max_eq_right (mul_nonneg hqpos.le
          (div_nonneg hDenominator.le hμ.le)), max_eq_right hqpos.le]
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_of_nonneg_left hDenominatorFactor hqpos.le)
    have hsourcePos : 0 < suppliedScale ε := by
      dsimp [suppliedScale]
      positivity
    have htargetPos : 0 < canonicalScale ε := by
      dsimp [canonicalScale]
      positivity
    rw [Real.norm_eq_abs, abs_of_pos hsourcePos,
      Real.norm_eq_abs, abs_of_pos htargetPos]
    dsimp [suppliedScale, canonicalScale]
    change 1 + max 0 (q / ((A.stepSize : ℝ) * (μ : ℝ))) ≤
      2 * (1 + factor * max 0 q)
    nlinarith [mul_nonneg hFactor.le (le_max_left 0 q)]
  unfold OnlineExecutablePLMeasuredCostComplexity OnlineMeasuredCostComplexity
    at hMeasured ⊢
  rcases hMeasured with ⟨hAccuracy, hIteration, hCosts⟩
  have hIteration' : AccuracyIterationBigO
      (fun ε => ((K ε).1 : ℝ)) canonicalScale := by
    rcases hIteration with hzero | hbig
    · let ε₁ : Accuracy := ⟨1, by norm_num⟩
      have hpos : 0 < suppliedScale ε₁ := by
        dsimp [suppliedScale]
        positivity
      exact (ne_of_gt hpos (hzero.1 ε₁)).elim
    · exact Or.inr (hbig.trans hScale)
  refine ⟨K, hAccuracy, hIteration', ?_⟩
  intro i
  rcases hCosts i with ⟨hOracleInt, hOracle, hCommInt, hComm⟩
  let oraclePayload : Accuracy → ℝ := fun ε =>
    A.refreshProbability * (chosenBatch ε).1 +
      2 * (1 - A.refreshProbability) * b0.1
  let communicationPayload : Accuracy → ℝ := fun _ =>
    A.refreshProbability * d.1 +
      (1 - A.refreshProbability) * expectedDensity A.quantizer
  have hOracleScale : AccuracyBigO
      (fun ε => (chosenBatch ε).1 + suppliedScale ε * oraclePayload ε)
      (fun ε => (chosenBatch ε).1 + canonicalScale ε * oraclePayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl
      (fun ε : Accuracy => ((chosenBatch ε).1 : ℝ)) accuracyToZero).add_add
        (hScale.mul (Asymptotics.isBigO_refl oraclePayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((chosenBatch ε).1 : ℝ)), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [oraclePayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg
              (mul_nonneg (by norm_num)
                (sub_nonneg.mpr A.refresh_admissible.2)) (by positivity))))]
  have hCommunicationScale : AccuracyBigO
      (fun ε => (d.1 : ℝ) + suppliedScale ε * communicationPayload ε)
      (fun ε => (d.1 : ℝ) + canonicalScale ε * communicationPayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl (fun _ : Accuracy => (d.1 : ℝ))
      accuracyToZero).add_add
        (hScale.mul
          (Asymptotics.isBigO_refl communicationPayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (d.1 : ℝ)),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [communicationPayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg (sub_nonneg.mpr A.refresh_admissible.2)
              (expectedDensity_nonneg_of_unbiased hQuantizer))))]
  refine ⟨hOracleInt, ?_, hCommInt, ?_⟩
  · apply hOracle.trans
    simpa [chosenBatch, suppliedScale, canonicalScale, oraclePayload,
      Δ, bracket, factor]
      using hOracleScale
  · apply hComm.trans
    simpa [suppliedScale, canonicalScale, communicationPayload,
      Δ, bracket, factor]
      using hCommunicationScale


/-- Compatibility-strengthened separate-stepsize release boundary.  Its first
conjunct retains the reciprocal dependence on each supplied positive
stepsize; its second conjunct is exactly the existing pair of distinct
Eq. (40)/(48) canonical-scale endpoints. -/
theorem Theorem_D3_D4_measured_cost_complexity_with_separate_canonical_stepsizes_forallPath_compatibility
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (γNonconvex γPL : PositiveStepsize)
    (x0 xStar : Point d)
    (nonconvexBaseBatch plBaseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32Nonconvex : ∀ ε,
      OnlineAssumption32Genuine (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A γNonconvex A.refreshProbability
            A.refresh_admissible) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)) ℒlocal)
    (hAssumption32PL : ∀ ε,
      OnlineAssumption32Genuine (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A γPL A.refreshProbability
            A.refresh_admissible) x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ plBaseBatch ε)) ℒlocal)
    (hCanonicalStepNonconvex :
      (γNonconvex : ℝ) *
        (rootMeanSquare Llocal +
          Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1)
    (hCanonicalStepPL :
      (γPL : ℝ) * max (2 * (μ : ℝ) / A.refreshProbability)
        (rootMeanSquare Llocal +
          Real.sqrt ((2 * (1 - A.refreshProbability)) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let ANonconvex := onlineDataWithParameters A γNonconvex
      A.refreshProbability A.refresh_admissible
    let APL := onlineDataWithParameters A γPL
      A.refreshProbability A.refresh_admissible
    let nonconvexBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) nonconvexBaseBatch
    let plBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ plBaseBatch
    let nonconvexAdmissible := fun ε =>
      onlineNonconvexBatchScheduleFromBase_admissible n b0
        (2 * varianceAggregateSq σ / A.refreshProbability)
        nonconvexBaseBatch ε
    let plAdmissible := fun ε =>
      onlinePLBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) μ plBaseBatch ε
    let Δnc := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let Δpl := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let nonconvexBracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let plBracket := rootMeanSquare Llocal +
      Real.sqrt ((2 * (1 - A.refreshProbability)) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let nonconvexSuppliedScale := fun ε : Accuracy =>
      1 + 4 * Δnc / ((γNonconvex : ℝ) * (ε : ℝ) ^ 2)
    let plSuppliedScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δpl / (ε : ℝ)) /
        ((γPL : ℝ) * (μ : ℝ)))
    let nonconvexCanonicalScale := fun ε : Accuracy =>
      1 + Δnc / (ε : ℝ) ^ 2 * nonconvexBracket
    let plCanonicalScale := fun ε : Accuracy =>
      1 + max (1 / A.refreshProbability) (plBracket / (μ : ℝ)) *
        max 0 (Real.log (4 * Δpl / (ε : ℝ)))
    OnlineSeparateStepsizeMeasuredCostComplexity ANonconvex APL x0 xStar
        nonconvexBatch plBatch nonconvexAdmissible plAdmissible
        nonconvexSuppliedScale plSuppliedScale ∧
      OnlineSeparateStepsizeMeasuredCostComplexity ANonconvex APL x0 xStar
        nonconvexBatch plBatch nonconvexAdmissible plAdmissible
        nonconvexCanonicalScale plCanonicalScale := by
  dsimp only
  let ANonconvex := onlineDataWithParameters A γNonconvex
    A.refreshProbability A.refresh_admissible
  let APL := onlineDataWithParameters A γPL
    A.refreshProbability A.refresh_admissible
  have hStepNonconvex : OnlineVRStepsizeCondition γNonconvex
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0 := by
    unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition
    simpa using hCanonicalStepNonconvex.le
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hγPL : 0 < (γPL : ℝ) := γPL.property
  let plBracket := rootMeanSquare Llocal +
    Real.sqrt ((2 * (1 - A.refreshProbability)) /
      (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let plDenominator := max (2 * (μ : ℝ) / A.refreshProbability) plBracket
  have hCanonicalPL : (γPL : ℝ) * plDenominator = 1 := by
    simpa [plDenominator, plBracket] using hCanonicalStepPL
  have hStepPL : OnlineVRPLStepsizeCondition γPL
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0 := by
    unfold OnlineVRPLStepsizeCondition FiniteSumVRPLStepsizeCondition
    constructor
    · have hle : plBracket ≤ plDenominator := le_max_right _ _
      have hmul := mul_le_mul_of_nonneg_left hle hγPL.le
      simpa [plBracket] using hmul.trans_eq hCanonicalPL
    · rw [← div_le_one hp]
      calc
        2 * (γPL : ℝ) * (μ : ℝ) / A.refreshProbability =
            (γPL : ℝ) * (2 * (μ : ℝ) / A.refreshProbability) := by
              ring
        _ ≤ (γPL : ℝ) * plDenominator :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hγPL.le
        _ = 1 := hCanonicalPL
  constructor
  · unfold OnlineSeparateStepsizeMeasuredCostComplexity
    constructor
    · apply
        onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularity
        ANonconvex x0 nonconvexBaseBatch Llocal ℒlocal σ ω fStar
      · simpa [ANonconvex, onlineDataWithParameters] using hLower
      · simpa [ANonconvex, onlineDataWithParameters] using hSmooth
      · simpa [ANonconvex, onlineDataWithParameters] using hLiteral
      · simpa [ANonconvex, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [ANonconvex, onlineDataWithParameters] using
          hAssumption32Nonconvex ε
      · simpa [ANonconvex, onlineDataWithParameters] using hRegularity
      · simpa [ANonconvex, onlineDataWithParameters] using hStepNonconvex
    · apply
        onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularity
        APL x0 xStar plBaseBatch Llocal ℒlocal σ ω fStar μ
      · simpa [APL, onlineDataWithParameters] using hLower
      · simpa [APL, onlineDataWithParameters] using hSmooth
      · simpa [APL, onlineDataWithParameters] using hLiteral
      · simpa [APL, onlineDataWithParameters] using hPL
      · simpa [APL, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [APL, onlineDataWithParameters] using hAssumption32PL ε
      · simpa [APL, onlineDataWithParameters] using hRegularity
      · simpa [APL, onlineDataWithParameters] using hStepPL
  · unfold OnlineSeparateStepsizeMeasuredCostComplexity
    constructor
    · apply
        onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularity
        ANonconvex x0 nonconvexBaseBatch Llocal ℒlocal σ ω fStar
      · simpa [ANonconvex, onlineDataWithParameters] using hLower
      · simpa [ANonconvex, onlineDataWithParameters] using hSmooth
      · simpa [ANonconvex, onlineDataWithParameters] using hLiteral
      · simpa [ANonconvex, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [ANonconvex, onlineDataWithParameters] using
          hAssumption32Nonconvex ε
      · simpa [ANonconvex, onlineDataWithParameters] using hRegularity
      · simpa [ANonconvex, onlineDataWithParameters] using
          hCanonicalStepNonconvex
    · apply
        onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularity
        APL x0 xStar plBaseBatch Llocal ℒlocal σ ω fStar μ
      · simpa [APL, onlineDataWithParameters] using hLower
      · simpa [APL, onlineDataWithParameters] using hSmooth
      · simpa [APL, onlineDataWithParameters] using hLiteral
      · simpa [APL, onlineDataWithParameters] using hPL
      · simpa [APL, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [APL, onlineDataWithParameters] using hAssumption32PL ε
      · simpa [APL, onlineDataWithParameters] using hRegularity
      · simpa [APL, onlineDataWithParameters] using hCanonicalStepPL

/-- Literal fixed-query refresh moment for a worker-dependent minibatch.  It
is the heterogeneous refresh calculation needed by the executable recurrence,
stated without the older globally differentiable sample-loss carrier. -/
theorem heterogeneousOnline_fixed_refresh_average_second_moment_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    Integrable (fun batch : HeterogeneousOnlineBatch n Sample b ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i (batch i j) x)) -
          globalGradient (onlineLocalProblem A.problem) x‖ ^ 2)
      (heterogeneousOnlineBatchLaw A.problem b) ∧
      (∫ batch : HeterogeneousOnlineBatch n Sample b,
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i (batch i j) x)) -
          globalGradient (onlineLocalProblem A.problem) x‖ ^ 2
        ∂heterogeneousOnlineBatchLaw A.problem b) ≤
        heterogeneousOnlineVarianceTerm σ b := by
  constructor
  · simpa [heterogeneousOnlineInitialEstimatorErrorSq,
      heterogeneousOnlineInitialEstimator] using
      (heterogeneousOnlineInitialEstimatorErrorSq_integrable_of_literal
        (b := b) A x σ hLiteral hDiff)
  · simpa [expectedHeterogeneousOnlineInitialEstimatorErrorSq,
      heterogeneousOnlineInitialEstimatorErrorSq,
      heterogeneousOnlineInitialEstimator] using
      (expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
        (b := b) A x σ hLiteral hDiff)

set_option maxHeartbeats 2000000 in
/-- The refresh error at the actual generated query of executable
heterogeneous Algorithm 3 is integrable and has the Remark D.2 variance
aggregate.  Freshness comes from the canonical strict-prefix/current-round
product law, while adaptive measurability comes only from the explicit
law-scoped correction. -/
theorem
    heterogeneousOnlineExecutable_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i))
    (k : ℕ) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    Integrable refreshErrorSq law ∧
      (∫ path, refreshErrorSq path ∂law) ≤
        heterogeneousOnlineVarianceTerm σ b := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    primalStep A.stepSize (run k path)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let batchOfRound := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
    z.2.1.1
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    batchOfRound (current path)
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let φ := fun (x : Point d) (fresh : HeterogeneousOnlineBatch n Sample b) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
        stochasticGradient A.problem i (fresh i j) x)) -
      globalGradient P x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
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
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 σ hLiteral hRegularity k
  have hqueryStrong : AEStronglyMeasurable query law :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable
      hstate).aestronglyMeasurable
  have hcurrent : Measurable current := by
    dsimp [current]
    fun_prop
  have hbatchOfRound : Measurable batchOfRound := by
    dsimp [batchOfRound]
    fun_prop
  have hbatch : Measurable batch := hbatchOfRound.comp hcurrent
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    have h := (heterogeneousOnlineQuery_indep_current_round_of_measurable
      (b := b) (b0 := b0) A x0 k hstate).comp measurable_fst measurable_id
    simpa [query, run, current, law] using h
  have hqueryBatch : ProbabilityTheory.IndepFun query batch law :=
    hqueryCurrent.comp measurable_id hbatchOfRound
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (Measure.map Prod.snd law) := by
              rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
              rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (SOptLib.iidStreamLaw roundLaw) := by
              rw [show Measure.map Prod.snd law =
                  SOptLib.iidStreamLaw roundLaw by
                dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map batchOfRound
          (Measure.map current law) := by
            rw [Measure.map_map hbatchOfRound hcurrent]
            rfl
      _ = Measure.map batchOfRound roundLaw := by rw [hcurrentLaw]
      _ = batchLaw := by
        let differenceLaw := heterogeneousOnlineBatchLaw A.problem b0
        let compressionLaw := workerCompressionLaw (n := n) A.quantizer
        let restLaw := (batchLaw.prod differenceLaw).prod compressionLaw
        calc
          Measure.map batchOfRound roundLaw =
              Measure.map (fun z :
                  (HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                    z.1.1) (Measure.map Prod.snd roundLaw) := by
                rw [Measure.map_map]
                · rfl
                · fun_prop
                · exact measurable_snd
          _ = Measure.map (fun z :
                  (HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                    z.1.1) restLaw := by
                rw [show Measure.map Prod.snd roundLaw = restLaw by
                  dsimp [roundLaw, restLaw, differenceLaw, compressionLaw,
                    batchLaw]
                  unfold heterogeneousOnlineRoundLaw
                  rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = Measure.map Prod.fst (batchLaw.prod differenceLaw) := by
                rw [show (fun z :
                    (HeterogeneousOnlineBatch n Sample b ×
                      HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                      z.1.1) = Prod.fst ∘ Prod.fst by rfl,
                  ← Measure.map_map measurable_fst measurable_fst,
                  Measure.map_fst_prod, measure_univ, one_smul]
          _ = batchLaw := by
                rw [Measure.map_fst_prod, measure_univ, one_smul]
  haveI : IsProbabilityMeasure (Measure.map query law) :=
    Measure.isProbabilityMeasure_map hqueryStrong.aemeasurable
  have hφ : AEStronglyMeasurable
      (fun p : Point d × HeterogeneousOnlineBatch n Sample b ↦
        φ p.1 p.2) ((Measure.map query law).prod batchLaw) := by
    simpa [φ, P] using
      (heterogeneousOnlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
        (b := b) A.problem hRegularity (Measure.map query law))
  have hfixed (x : Point d) :
      Integrable (φ x) batchLaw ∧
        (∫ fresh, φ x fresh ∂batchLaw) ≤
          heterogeneousOnlineVarianceTerm σ b := by
    simpa [φ, P, batchLaw] using
      (heterogeneousOnline_fixed_refresh_average_second_moment_of_literal
        (b := b) A x σ hLiteral hDiff)
  have hcomp : Integrable (fun path ↦ φ (query path) (batch path)) law :=
    integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := batch)
      (C := heterogeneousOnlineVarianceTerm σ b) hφ
      hqueryStrong.aemeasurable hbatch.aemeasurable hqueryBatch hbatchLaw
      (fun _ _ ↦ sq_nonneg _) (fun x ↦ (hfixed x).1)
      (fun x ↦ (hfixed x).2)
  have hbound : (∫ path, φ (query path) (batch path) ∂law) ≤
      heterogeneousOnlineVarianceTerm σ b :=
    integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := batch)
      hφ hqueryStrong.aemeasurable hbatch.aemeasurable hqueryBatch hbatchLaw
      hcomp (fun x ↦ (hfixed x).2)
  simpa [φ, query, batch, batchOfRound, current, run, law, P,
    heterogeneousOnlineProcess, SOptLib.recursive_process_from_random_initial,
    heterogeneousOnlineStep] using ⟨hcomp, hbound⟩

/-- Genuine sampled-gradient realization of one worker-dependent
Assumption 3.2 minibatch. -/
def GenuineHeterogeneousOnlineBatchDifferenceAt
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample)
    (batch : HeterogeneousOnlineBatch n Sample b0)
    (i : Worker n) (xNext x delta : Point d) : Prop :=
  ∃ gNext gCurrent : Fin (b0 i).1 → Point d,
    (∀ j, GenuineSampleGradientAt P i (batch i j) xNext (gNext j)) ∧
    (∀ j, GenuineSampleGradientAt P i (batch i j) x (gCurrent j)) ∧
    delta = average (fun j ↦ gNext j - gCurrent j)

/-- Source-side Assumption 3.2 for worker-dependent batches and an arbitrary
generated process.  The displayed minibatch difference is required to be
made of genuine sampled gradients almost surely; the other fields are the
conditional mean and second-moment clauses from Eq. (8). -/
def HeterogeneousOnlineAssumption32Genuine
    {d n : Count} {Ω : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k i (path : Ω),
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      ∃ delta : HeterogeneousOnlineBatch n Sample b0 → Point d,
        (∀ᵐ batch ∂heterogeneousOnlineBatchLaw P b0,
          GenuineHeterogeneousOnlineBatchDifferenceAt
            P batch i xNext x (delta batch)) ∧
        Integrable delta (heterogeneousOnlineBatchLaw P b0) ∧
        Integrable (fun batch ↦
          ‖delta batch -
            localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2)
          (heterogeneousOnlineBatchLaw P b0) ∧
        (∫ batch, delta batch ∂heterogeneousOnlineBatchLaw P b0) =
          localGradientDifference (onlineLocalProblem P) i xNext x ∧
        (∫ batch,
            ‖delta batch -
              localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2
            ∂heterogeneousOnlineBatchLaw P b0) ≤
          (ℒ i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2)

/-- Law-a.e. form of the genuine worker-dependent Assumption 3.2 contract.
This matches the source conditional-expectation quantifier: the minibatch
fiber is required at generated paths almost surely, not at null paths. -/
def HeterogeneousOnlineAssumption32GenuineAE
    {d n : Count} {Ω : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k, ∀ᵐ path ∂pathLaw, ∀ i,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      ∃ delta : HeterogeneousOnlineBatch n Sample b0 → Point d,
        (∀ᵐ batch ∂heterogeneousOnlineBatchLaw P b0,
          GenuineHeterogeneousOnlineBatchDifferenceAt
            P batch i xNext x (delta batch)) ∧
        Integrable delta (heterogeneousOnlineBatchLaw P b0) ∧
        Integrable (fun batch ↦
          ‖delta batch -
            localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2)
          (heterogeneousOnlineBatchLaw P b0) ∧
        (∫ batch, delta batch ∂heterogeneousOnlineBatchLaw P b0) =
          localGradientDifference (onlineLocalProblem P) i xNext x ∧
        (∫ batch,
            ‖delta batch -
              localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2
            ∂heterogeneousOnlineBatchLaw P b0) ≤
          (ℒ i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2)

/-- For constant worker batches, the homogeneous and heterogeneous
law-a.e. source contracts are definitionally the same after the proved
process identification.  Their path laws and genuine minibatch objects are
definitionally identical. -/
theorem onlineAssumption32GenuineAE_iff_heterogeneous_const
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ : Worker n → ℝ) :
    OnlineAssumption32GenuineAE (b0 := b0) A.problem
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) ℒ ↔
      HeterogeneousOnlineAssumption32GenuineAE
        (b0 := fun _ : Worker n ↦ b0) A.problem
        (heterogeneousOnlineProcess
          (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0) A x0)
        (heterogeneousOnlinePathLaw
          (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0) A) ℒ := by
  have hProcess : onlineProcess (b := b) (b0 := b0) A x0 hBatch =
      heterogeneousOnlineProcess (b := fun _ : Worker n ↦ b)
        (b0 := fun _ : Worker n ↦ b0) A x0 := by
    funext k path
    exact onlineProcess_eq_heterogeneousOnlineProcess_const
      A x0 hBatch k path
  rw [hProcess, onlinePathLaw_eq_heterogeneousOnlinePathLaw_const A]
  rfl

/-- The worker-dependent smoothness aggregate reduces to the homogeneous
Eq. (40) term for a constant difference-batch family. -/
theorem heterogeneousFiniteBatchSmoothnessTerm_const
    {n b0 : Count} (ℒ : Worker n → ℝ) :
    heterogeneousFiniteBatchSmoothnessTerm ℒ (fun _ : Worker n ↦ b0) =
      (rootMeanSquare ℒ) ^ 2 / b0.1 := by
  have hm : 0 ≤ meanSquare ℒ := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hr : (rootMeanSquare ℒ) ^ 2 = meanSquare ℒ := by
    unfold rootMeanSquare
    exact Real.sq_sqrt hm
  rw [hr]
  unfold heterogeneousFiniteBatchSmoothnessTerm meanSquare average
    SOptLib.finiteUniformAverage
  simp only [Fintype.card_fin, smul_eq_mul]
  ring_nf
  rw [← Finset.sum_mul]
  ring

/-- The worker-dependent refresh variance reduces to the homogeneous
Eq. (46) variance floor for a constant refresh-batch family. -/
theorem heterogeneousOnlineVarianceTerm_const
    {n b : Count} (σ : Worker n → ℝ) :
    heterogeneousOnlineVarianceTerm σ (fun _ : Worker n ↦ b) =
      varianceAggregateSq σ / (n.1 * b.1) := by
  unfold heterogeneousOnlineVarianceTerm varianceAggregateSq meanSquare average
    SOptLib.finiteUniformAverage
  simp only [Fintype.card_fin, smul_eq_mul]
  ring_nf
  rw [← Finset.sum_mul]
  ring

/-- Law-a.e. formal fiber used by the heterogeneous executable recurrence.
It records exactly the conditional mean and second-moment content of source
Assumption 3.2 for the actual `heterogeneousOnlineProcess`. -/
def HeterogeneousOnlineAverageSmoothnessAE
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k, ∀ᵐ path ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A,
      ∀ i,
      let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      Integrable (fun batch ↦
          heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x)
        (heterogeneousOnlineBatchLaw A.problem b0) ∧
      Integrable (fun batch ↦
          ‖heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x -
            localGradientDifference (onlineLocalProblem A.problem)
              i xNext x‖ ^ 2)
        (heterogeneousOnlineBatchLaw A.problem b0) ∧
      (∫ batch, heterogeneousOnlineBatchDifference A.problem b0
          batch i xNext x ∂heterogeneousOnlineBatchLaw A.problem b0) =
        localGradientDifference (onlineLocalProblem A.problem) i xNext x ∧
      (∫ batch,
          ‖heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x -
            localGradientDifference (onlineLocalProblem A.problem)
              i xNext x‖ ^ 2
          ∂heterogeneousOnlineBatchLaw A.problem b0) ≤
        (ℒ i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2)

/-- The earlier universal-path helper is a sufficient compatibility supplier
for the source-faithful law-a.e. Assumption 3.2 interface. -/
theorem heterogeneousOnlineAssumption32GenuineAE_of_forallPath
    {d n : Count} {Ω : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (ℒ : Worker n → ℝ)
    (h : HeterogeneousOnlineAssumption32Genuine (b0 := b0) P run ℒ) :
    HeterogeneousOnlineAssumption32GenuineAE
      (b0 := b0) P run pathLaw ℒ := by
  refine ⟨h.1, ?_⟩
  intro k
  filter_upwards [] with path
  intro i
  exact h.2 k i path

/-- A genuine worker-dependent minibatch is definitionally the formal
heterogeneous batch difference once all displayed gradients exist. -/
theorem heterogeneousOnlineBatchDifference_eq_of_genuineAt
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample}
    {batch : HeterogeneousOnlineBatch n Sample b0}
    {i : Worker n} {xNext x delta : Point d}
    (h : GenuineHeterogeneousOnlineBatchDifferenceAt
      P batch i xNext x delta) :
    heterogeneousOnlineBatchDifference P b0 batch i xNext x = delta := by
  rcases h with ⟨gNext, gCurrent, hNext, hCurrent, rfl⟩
  unfold heterogeneousOnlineBatchDifference
  congr 1
  funext j
  rw [stochasticGradient_eq_of_genuineSampleGradientAt (hNext j),
    stochasticGradient_eq_of_genuineSampleGradientAt (hCurrent j)]

/-- The genuine heterogeneous source predicate supplies the existing
generated-process Assumption 3.2 fiber by an explicit almost-everywhere
identification of the measured minibatch difference. -/
theorem heterogeneousOnlineAssumption32Genuine_to_averageSmoothness
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (ℒ : Worker n → ℝ)
    (h : HeterogeneousOnlineAssumption32Genuine (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) ℒ) :
    HeterogeneousOnlineAverageSmoothness (b := b) (b0 := b0) A x0 ℒ := by
  refine ⟨h.1, ?_⟩
  intro k i path
  rcases h.2 k i path with
    ⟨delta, hGenuine, hIntegrable, hResidualIntegrable, hMean, hVariance⟩
  have hEq : (fun batch ↦ heterogeneousOnlineBatchDifference A.problem b0
      batch i
        (heterogeneousOnlineProcess A x0 (k + 1) path).x
        (heterogeneousOnlineProcess A x0 k path).x) =ᵐ[
          heterogeneousOnlineBatchLaw A.problem b0] delta :=
    hGenuine.mono (fun _ hbatch ↦
      heterogeneousOnlineBatchDifference_eq_of_genuineAt hbatch)
  have hResidualEq :
      (fun batch ↦
        ‖heterogeneousOnlineBatchDifference A.problem b0 batch i
            (heterogeneousOnlineProcess A x0 (k + 1) path).x
            (heterogeneousOnlineProcess A x0 k path).x -
          localGradientDifference (onlineLocalProblem A.problem) i
            (heterogeneousOnlineProcess A x0 (k + 1) path).x
            (heterogeneousOnlineProcess A x0 k path).x‖ ^ 2) =ᵐ[
        heterogeneousOnlineBatchLaw A.problem b0]
      (fun batch ↦
        ‖delta batch -
          localGradientDifference (onlineLocalProblem A.problem) i
            (heterogeneousOnlineProcess A x0 (k + 1) path).x
            (heterogeneousOnlineProcess A x0 k path).x‖ ^ 2) := by
    filter_upwards [hEq] with batch hbatch
    rw [hbatch]
  refine ⟨hIntegrable.congr hEq.symm,
    hResidualIntegrable.congr hResidualEq.symm, ?_, ?_⟩
  · rw [integral_congr_ae hEq, hMean]
  · rw [integral_congr_ae hResidualEq]
    exact hVariance

/-- Source-to-formal transfer for the law-a.e. Assumption 3.2 contract.  Both
sides use the same generated heterogeneous process and path law; the only
change of measured object is the proved a.e. identification of genuine
sampled-gradient differences with `heterogeneousOnlineBatchDifference`. -/
theorem heterogeneousOnlineAssumption32GenuineAE_to_averageSmoothnessAE
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (ℒ : Worker n → ℝ)
    (h : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒ) :
    HeterogeneousOnlineAverageSmoothnessAE
      (b := b) (b0 := b0) A x0 ℒ := by
  refine ⟨h.1, ?_⟩
  intro k
  filter_upwards [h.2 k] with path hpath
  intro i
  rcases hpath i with
    ⟨delta, hGenuine, hIntegrable, hResidualIntegrable, hMean, hVariance⟩
  have hEq : (fun batch ↦ heterogeneousOnlineBatchDifference A.problem b0
      batch i
        (heterogeneousOnlineProcess A x0 (k + 1) path).x
        (heterogeneousOnlineProcess A x0 k path).x) =ᵐ[
          heterogeneousOnlineBatchLaw A.problem b0] delta :=
    hGenuine.mono (fun _ hbatch ↦
      heterogeneousOnlineBatchDifference_eq_of_genuineAt hbatch)
  have hResidualEq :
      (fun batch ↦
        ‖heterogeneousOnlineBatchDifference A.problem b0 batch i
            (heterogeneousOnlineProcess A x0 (k + 1) path).x
            (heterogeneousOnlineProcess A x0 k path).x -
          localGradientDifference (onlineLocalProblem A.problem) i
            (heterogeneousOnlineProcess A x0 (k + 1) path).x
            (heterogeneousOnlineProcess A x0 k path).x‖ ^ 2) =ᵐ[
        heterogeneousOnlineBatchLaw A.problem b0]
      (fun batch ↦
        ‖delta batch -
          localGradientDifference (onlineLocalProblem A.problem) i
            (heterogeneousOnlineProcess A x0 (k + 1) path).x
            (heterogeneousOnlineProcess A x0 k path).x‖ ^ 2) := by
    filter_upwards [hEq] with batch hbatch
    rw [hbatch]
  refine ⟨hIntegrable.congr hEq.symm,
    hResidualIntegrable.congr hResidualEq.symm, ?_, ?_⟩
  · rw [integral_congr_ae hEq, hMean]
  · rw [integral_congr_ae hResidualEq]
    exact hVariance

/-! ## Worker-indexed generated conditional kernel for Remark D.2 -/

/-- The genuine sampled-gradient difference in one worker's own
worker-dependent minibatch row.  This is the workerwise source object in
Assumption 3.2; unlike `GenuineHeterogeneousOnlineBatchDifferenceAt`, it does
not carry the unused rows belonging to the other workers. -/
def GenuineOnlineWorkerBatchDifferenceAt
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n)
    {m : Count} (row : Fin m.1 → Sample i)
    (xNext x delta : Point d) : Prop :=
  ∃ gNext gCurrent : Fin m.1 → Point d,
    (∀ j, GenuineSampleGradientAt P i (row j) xNext (gNext j)) ∧
    (∀ j, GenuineSampleGradientAt P i (row j) x (gCurrent j)) ∧
    delta = average (fun j ↦ gNext j - gCurrent j)

/-- Source Assumption 3.2 for a generated process with worker-dependent
difference batches.  For worker `i`, the jointly measurable conditional
random variable is formed from the exact `b⁰ i` row and its canonical iid
product law.  Thus no artificial common batch size and no unrelated query law
is introduced. -/
def HeterogeneousOnlineAssumption32GeneratedConditionalKernel
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Omega → State d)
    (pathLaw : Measure Omega) (Lcal : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ Lcal i) ∧
    (∀ k, AEStronglyMeasurable
      (fun path ↦ ((run k path).x, (run (k + 1) path).x)) pathLaw) ∧
    (∀ k i, ∃ delta : Omega × (Fin (b0 i).1 → Sample i) → Point d,
      AEStronglyMeasurable delta
        (pathLaw.prod
          (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i))) ∧
      (∀ᵐ z ∂pathLaw.prod
          (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)),
        GenuineOnlineWorkerBatchDifferenceAt P i z.2
          (run (k + 1) z.1).x (run k z.1).x (delta z)) ∧
      (∀ᵐ path ∂pathLaw,
        Integrable (fun row ↦ delta (path, row))
            (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)) ∧
          Integrable (fun row ↦
            ‖delta (path, row) -
              localGradientDifference (onlineLocalProblem P) i
                (run (k + 1) path).x (run k path).x‖ ^ 2)
            (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)) ∧
          (∫ row, delta (path, row)
              ∂Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)) =
            localGradientDifference (onlineLocalProblem P) i
              (run (k + 1) path).x (run k path).x ∧
          (∫ row,
              ‖delta (path, row) -
                localGradientDifference (onlineLocalProblem P) i
                  (run (k + 1) path).x (run k path).x‖ ^ 2
              ∂Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)) ≤
            (Lcal i) ^ 2 / (b0 i).1 *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2))

/-- A genuine worker-row difference is definitionally represented by the
totalized sampled-gradient row average used in the heterogeneous Algorithm 3
update. -/
theorem onlineWorkerBatchDifference_eq_of_genuineAt
    {d n m : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {i : Worker n}
    {row : Fin m.1 → Sample i} {xNext x delta : Point d}
    (h : GenuineOnlineWorkerBatchDifferenceAt
      P i row xNext x delta) :
    average (fun j : Fin m.1 ↦
      stochasticGradient P i (row j) xNext -
        stochasticGradient P i (row j) x) = delta := by
  rcases h with ⟨gNext, gCurrent, hNext, hCurrent, rfl⟩
  congr 1
  funext j
  rw [stochasticGradient_eq_of_genuineSampleGradientAt (hNext j),
    stochasticGradient_eq_of_genuineSampleGradientAt (hCurrent j)]

/-- Assumption 3.2's jointly measurable worker-row kernel makes the actual
totalized row average jointly measurable under the same generated path and
the same worker-specific iid minibatch law. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_rowDifference_joint_aestronglyMeasurable
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} {Lcal : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal) (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (fun z : Omega × (Fin (b0 i).1 → Sample i) ↦
        average (fun j : Fin (b0 i).1 ↦
          stochasticGradient P i (z.2 j) (run (k + 1) z.1).x -
            stochasticGradient P i (z.2 j) (run k z.1).x))
      (pathLaw.prod
        (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i))) := by
  rcases hKernel.2.2 k i with ⟨delta, hdelta, hGenuine, _hFibers⟩
  exact hdelta.congr (hGenuine.mono fun _ hz ↦
    (onlineWorkerBatchDifference_eq_of_genuineAt hz).symm)

/-- One canonical coordinate of the worker-specific conditional kernel
supplies genuine sampled gradients at both consecutive generated queries
under the exact path-by-single-sample product law. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_singleSample_genuine_ae
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {Lcal : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal) (k : ℕ) (i : Worker n) :
    ∀ᵐ z ∂pathLaw.prod (P.sampleLaw i),
      ∃ gNext gCurrent : Point d,
        GenuineSampleGradientAt P i z.2 (run (k + 1) z.1).x gNext ∧
          GenuineSampleGradientAt P i z.2 (run k z.1).x gCurrent := by
  classical
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  let j0 : Fin (b0 i).1 := ⟨0, (b0 i).2⟩
  rcases hKernel.2.2 k i with
    ⟨_delta, _hDelta, hGenuine, _hFibers⟩
  have hCoordinate : ∀ᵐ z ∂pathLaw.prod
      (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)),
      ∃ gNext gCurrent : Point d,
        GenuineSampleGradientAt P i (z.2 j0)
            (run (k + 1) z.1).x gNext ∧
          GenuineSampleGradientAt P i (z.2 j0)
            (run k z.1).x gCurrent := by
    filter_upwards [hGenuine] with z hz
    rcases hz with
      ⟨gNext, gCurrent, hNext, hCurrent, _hDeltaEq⟩
    exact ⟨gNext j0, gCurrent j0, hNext j0, hCurrent j0⟩
  exact ae_singleSample_of_iid_row_coordinate
    pathLaw (P.sampleLaw i) j0
    (fun path xi ↦ ∃ gNext gCurrent : Point d,
      GenuineSampleGradientAt P i xi (run (k + 1) path).x gNext ∧
        GenuineSampleGradientAt P i xi (run k path).x gCurrent)
    hCoordinate

/-- The preceding genuine source gradients are represented by the existing
totalized `stochasticGradient` at the same heterogeneous generated calls. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_singleSample_genuine_totalized_ae
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {Lcal : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal) (k : ℕ) (i : Worker n) :
    ∀ᵐ z ∂pathLaw.prod (P.sampleLaw i),
      GenuineSampleGradientAt P i z.2 (run (k + 1) z.1).x
          (stochasticGradient P i z.2 (run (k + 1) z.1).x) ∧
        GenuineSampleGradientAt P i z.2 (run k z.1).x
          (stochasticGradient P i z.2 (run k z.1).x) := by
  have hGenuine :=
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_singleSample_genuine_ae
      hKernel k i
  filter_upwards [hGenuine] with z hz
  rcases hz with ⟨gNext, gCurrent, hNext, hCurrent⟩
  constructor
  · rw [stochasticGradient_eq_of_genuineSampleGradientAt hNext]
    exact hNext
  · rw [stochasticGradient_eq_of_genuineSampleGradientAt hCurrent]
    exact hCurrent

/-- The worker-indexed source kernel and literal Assumption 3.3 make the
single sampled-gradient difference at consecutive generated queries a random
vector.  The iid reconstruction uses exactly the worker's `b⁰ i` row. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_singleSampleDifference_joint_aestronglyMeasurable
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {Lcal sigma : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal)
    (hLiteral : OnlineAssumption33Literal P sigma)
    (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (fun z : Omega × Sample i ↦
        stochasticGradient P i z.2 (run (k + 1) z.1).x -
          stochasticGradient P i z.2 (run k z.1).x)
      (pathLaw.prod (P.sampleLaw i)) := by
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  have hRow :=
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_rowDifference_joint_aestronglyMeasurable
      hKernel k i
  have hMoments : LegacyOnlineFixedQueryUnbiasedBoundedVariance P sigma :=
    (onlineAssumption33Literal_iff_legacy P sigma).mp hLiteral
  have hFiber : ∀ᵐ path ∂pathLaw,
      Integrable
          (fun xi : Sample i ↦
            stochasticGradient P i xi (run (k + 1) path).x -
              stochasticGradient P i xi (run k path).x)
          (P.sampleLaw i) ∧
        (∫ xi, stochasticGradient P i xi (run (k + 1) path).x -
              stochasticGradient P i xi (run k path).x ∂P.sampleLaw i) =
          localGradientDifference (onlineLocalProblem P) i
            (run (k + 1) path).x (run k path).x := by
    filter_upwards [] with path
    rcases hMoments.2 i (run (k + 1) path).x with
      ⟨hNextInt, _hNextVarianceInt, hNextMean, _hNextVariance⟩
    rcases hMoments.2 i (run k path).x with
      ⟨hCurrentInt, _hCurrentVarianceInt, hCurrentMean,
        _hCurrentVariance⟩
    constructor
    · exact hNextInt.sub hCurrentInt
    · rw [integral_sub hNextInt hCurrentInt, hNextMean, hCurrentMean]
      rfl
  exact singleSample_joint_aestronglyMeasurable_of_iid_average
    pathLaw (P.sampleLaw i)
    (fun path xi ↦
      stochasticGradient P i xi (run (k + 1) path).x -
        stochasticGradient P i xi (run k path).x)
    (fun path ↦ localGradientDifference (onlineLocalProblem P) i
      (run (k + 1) path).x (run k path).x)
    hRow hFiber

/-- Telescoping the worker-indexed Assumption 3.2 differences from a
deterministic initial query supplies joint measurability of the sampled
gradient at every generated iterate. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_adaptiveGradient_joint_aestronglyMeasurable
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {Lcal sigma : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal)
    (hLiteral : OnlineAssumption33Literal P sigma)
    (x0 : Point d) (hInitial : ∀ path, (run 0 path).x = x0)
    (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (fun z : Omega × Sample i ↦
        stochasticGradient P i z.2 (run k z.1).x)
      (pathLaw.prod (P.sampleLaw i)) := by
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  have hMoments : LegacyOnlineFixedQueryUnbiasedBoundedVariance P sigma :=
    (onlineAssumption33Literal_iff_legacy P sigma).mp hLiteral
  induction k with
  | zero =>
      have hBase := (hMoments.2 i x0).1.aestronglyMeasurable.comp_snd
        (μ := pathLaw)
      exact hBase.congr (Filter.Eventually.of_forall fun z ↦ by
        change stochasticGradient P i z.2 x0 =
          stochasticGradient P i z.2 (run 0 z.1).x
        rw [hInitial z.1])
  | succ k ih =>
      have hDifference :=
        heterogeneousOnlineAssumption32GeneratedConditionalKernel_singleSampleDifference_joint_aestronglyMeasurable
          hKernel hLiteral k i
      refine (ih.add hDifference).congr
        (Filter.Eventually.of_forall fun z ↦ ?_)
      change stochasticGradient P i z.2 (run k z.1).x +
          (stochasticGradient P i z.2 (run (k + 1) z.1).x -
            stochasticGradient P i z.2 (run k z.1).x) =
        stochasticGradient P i z.2 (run (k + 1) z.1).x
      abel

/-- Exact worker-dependent executable Algorithm 3 A-track supplier.  Its
process, path law, worker, round, sample law, and `b⁰ i` conditional row are
those of `heterogeneousOnlineProcess`; the conclusion is deliberately the
generated-call fact needed by consumers, not the global all-query regularity
structure. -/
theorem heterogeneousOnlineProcess_adaptiveGradient_source_regular
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (Lcal sigma : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (k : ℕ) (i : Worker n) :
    (∀ᵐ z ∂(heterogeneousOnlinePathLaw (b := b) (b0 := b0) A).prod
        (A.problem.sampleLaw i),
      GenuineSampleGradientAt A.problem i z.2
        (heterogeneousOnlineProcess
          (b := b) (b0 := b0) A x0 k z.1).x
        (stochasticGradient A.problem i z.2
          (heterogeneousOnlineProcess
            (b := b) (b0 := b0) A x0 k z.1).x)) ∧
      AEStronglyMeasurable
        (fun z ↦ stochasticGradient A.problem i z.2
          (heterogeneousOnlineProcess
            (b := b) (b0 := b0) A x0 k z.1).x)
        ((heterogeneousOnlinePathLaw (b := b) (b0 := b0) A).prod
          (A.problem.sampleLaw i)) := by
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  constructor
  · have hGenuine :=
      heterogeneousOnlineAssumption32GeneratedConditionalKernel_singleSample_genuine_totalized_ae
        hKernel k i
    exact hGenuine.mono (fun _ hz ↦ hz.2)
  · exact
      heterogeneousOnlineAssumption32GeneratedConditionalKernel_adaptiveGradient_joint_aestronglyMeasurable
        hKernel hLiteral x0 (fun _ ↦ rfl) k i

/-- Product-law measurability of the complete worker-dependent nonrefresh
innovation.  This is the heterogeneous analogue of the homogeneous helper
used by the executable Eq. (46) proof. -/
theorem
    heterogeneousOnlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} {Ξ Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    [MeasurableSpace Q]
    (A : OnlineData d n Sample Ξ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (mu : Measure Q) [SFinite mu] (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) :
    AEStronglyMeasurable
      (fun p : Q ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
                (xNext p.1) (x p.1))
              (p.2.2 i) -
            localGradientDifference (onlineLocalProblem A.problem) i
              (xNext p.1) (x p.1)))
      (mu.prod ((heterogeneousOnlineBatchLaw A.problem b0).prod
        (workerCompressionLaw (n := n) A.quantizer))) := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let nu := batchLaw.prod compressionLaw
  let P := onlineLocalProblem A.problem
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure nu := by
    unfold nu
    infer_instance
  have hworkerLaw (i : Worker n) : Measure.map
      (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i) batchLaw =
      Measure.infinitePi
        (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i) := by
    simpa [batchLaw] using
      heterogeneous_online_batch_law_worker_marginal A.problem b0 i
  have hcoord (i : Worker n) (j : Fin (b0 i).1) : Measure.map
      (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        q.1 i j) nu = A.problem.sampleLaw i := by
    calc
      Measure.map
          (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
            q.1 i j) nu =
          Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j)
            (Measure.map Prod.fst nu) := by
              rw [Measure.map_map]
              · rfl
              · fun_prop
              · exact measurable_fst
      _ = Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j)
            batchLaw := by
              rw [show Measure.map Prod.fst nu = batchLaw by
                unfold nu
                rw [Measure.map_fst_prod, measure_univ, one_smul]]
      _ = Measure.map (fun row : Fin (b0 i).1 → Sample i ↦ row j)
            (Measure.map
              (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i)
              batchLaw) := by
              rw [Measure.map_map (measurable_pi_apply j)
                (measurable_pi_apply i)]
              rfl
      _ = Measure.map (fun row : Fin (b0 i).1 → Sample i ↦ row j)
            (Measure.infinitePi
              (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)) := by
              rw [hworkerLaw i]
      _ = A.problem.sampleLaw i := by
              simpa using (MeasureTheory.Measure.infinitePi_map_eval
                (μ := fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i) j)
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Q ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
              (xNext p.1) (x p.1))
            (p.2.2 i) -
          localGradientDifference P i (xNext p.1) (x p.1))
      (mu.prod nu) := by
    have hD : AEStronglyMeasurable
        (fun p : Q ×
            (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
          heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
            (xNext p.1) (x p.1)) (mu.prod nu) := by
      unfold heterogeneousOnlineBatchDifference average
        SOptLib.finiteUniformAverage
      have hnext (j : Fin (b0 i).1) : AEStronglyMeasurable
          (fun p : Q ×
              (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
            stochasticGradient A.problem i (p.2.1 i j) (xNext p.1))
          (mu.prod nu) :=
        (stochasticGradient_randomQuery_product_regular_of_lawRegularity
          A.problem hRegularity i mu nu xNext (fun q ↦ q.1 i j) hxNext
            (by fun_prop) (hcoord i j)).2
      have hcurrent (j : Fin (b0 i).1) : AEStronglyMeasurable
          (fun p : Q ×
              (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
            stochasticGradient A.problem i (p.2.1 i j) (x p.1))
          (mu.prod nu) :=
        (stochasticGradient_randomQuery_product_regular_of_lawRegularity
          A.problem hRegularity i mu nu x (fun q ↦ q.1 i j) hx
            (by fun_prop) (hcoord i j)).2
      have hs := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ ↦ (hnext j).sub (hcurrent j))).const_smul
          ((Fintype.card (Fin (b0 i).1) : ℝ)⁻¹)
      refine hs.congr (Filter.Eventually.of_forall ?_)
      intro p
      simp [Finset.sum_apply, Finset.sum_sub_distrib]
    have hquantized : AEStronglyMeasurable
        (fun p : Q ×
            (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
          A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
              (xNext p.1) (x p.1))
            (p.2.2 i)) (mu.prod nu) :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hD.aemeasurable.prodMk
          ((measurable_pi_apply i).comp
            (measurable_snd.comp measurable_snd)).aemeasurable)).aestronglyMeasurable
    have hdelta : AEStronglyMeasurable
        (fun p : Q ×
            (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
          localGradientDifference P i (xNext p.1) (x p.1))
        (mu.prod nu) := by
      unfold localGradientDifference
      exact (((measurable_localGradient P i).comp_aemeasurable
        hxNext.aemeasurable).aestronglyMeasurable.comp_fst).sub
        (((measurable_localGradient P i).comp_aemeasurable
          hx.aemeasurable).aestronglyMeasurable.comp_fst)
    exact hquantized.sub hdelta
  unfold average SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ ↦ hworker i)).const_smul ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [P, Finset.sum_apply]

set_option maxHeartbeats 4000000 in
/-- The worker-dependent nonrefresh innovation at the actual consecutive
queries of executable heterogeneous Algorithm 3 has zero mean and the exact
Remark D.2 second-moment coefficient.  The moment input is precisely the
generated heterogeneous Assumption 3.2 fiber; the Track-B correction is used
only to obtain measurable representatives on the worker-row product laws. -/
theorem
    heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_of_fibers_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ))
    (hFiber : ∀ i,
      let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      Integrable (fun batch ↦
          heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x)
        (heterogeneousOnlineBatchLaw A.problem b0) ∧
      Integrable (fun batch ↦
          ‖heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x -
            localGradientDifference (onlineLocalProblem A.problem)
              i xNext x‖ ^ 2)
        (heterogeneousOnlineBatchLaw A.problem b0) ∧
      (∫ batch, heterogeneousOnlineBatchDifference A.problem b0
          batch i xNext x ∂heterogeneousOnlineBatchLaw A.problem b0) =
        localGradientDifference (onlineLocalProblem A.problem) i xNext x ∧
      (∫ batch,
          ‖heterogeneousOnlineBatchDifference A.problem b0 batch i xNext x -
            localGradientDifference (onlineLocalProblem A.problem)
              i xNext x‖ ^ 2
          ∂heterogeneousOnlineBatchLaw A.problem b0) ≤
        (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2)
    :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    let law := (heterogeneousOnlineBatchLaw A.problem b0).prod
      (workerCompressionLaw (n := n) A.quantizer)
    let innovation := fun i : Worker n ↦
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 q.1 i xNext x)
            (q.2 i) -
          localGradientDifference (onlineLocalProblem A.problem) i xNext x
    Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
      Integrable (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
  classical
  dsimp only
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let x := (run k path).x
  let xNext := (run (k + 1) path).x
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let law := batchLaw.prod compressionLaw
  let source := fun i : Worker n ↦
    fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
      (q.1 i, q.2 i)
  let rowLaw := fun i : Worker n ↦
    (Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)).prod
      A.quantizer.law
  let localInnovation := fun i : Worker n ↦
    fun q : (Fin (b0 i).1 → Sample i) × Ξ ↦
      A.quantizer.apply
          (average (fun j : Fin (b0 i).1 ↦
            stochasticGradient A.problem i (q.1 j) xNext -
              stochasticGradient A.problem i (q.1 j) x)) q.2 -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x
  let innovation := fun i : Worker n ↦
    fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
      localInnovation i (source i q)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hsource : ∀ i : Worker n, Measurable (source i) := by
    intro i
    dsimp [source]
    fun_prop
  have hmap : ∀ i : Worker n, Measure.map (source i) law = rowLaw i := by
    intro i
    dsimp [source, law, rowLaw, batchLaw, compressionLaw]
    calc
      Measure.map
          (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
            (q.1 i, q.2 i))
          ((heterogeneousOnlineBatchLaw A.problem b0).prod
            (workerCompressionLaw A.quantizer)) =
          (Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i)
            (heterogeneousOnlineBatchLaw A.problem b0)).prod
            (Measure.map (fun q : Worker n → Ξ ↦ q i)
              (workerCompressionLaw A.quantizer)) := by
                symm
                simpa [Prod.map] using
                  (MeasureTheory.Measure.map_prod_map
                    (heterogeneousOnlineBatchLaw A.problem b0)
                    (workerCompressionLaw (n := n) A.quantizer)
                    (measurable_pi_apply i) (measurable_pi_apply i))
      _ = _ := by
        rw [heterogeneous_online_batch_law_worker_marginal A.problem b0 i,
          workerCompressionLaw_component_marginal A.quantizer i]
  have hLocalFiber : ∀ i : Worker n,
      Integrable (localInnovation i) (rowLaw i) ∧
      Integrable (fun q ↦ ‖localInnovation i q‖ ^ 2) (rowLaw i) ∧
      (∫ q, localInnovation i q ∂rowLaw i) = 0 ∧
      (∫ q, ‖localInnovation i q‖ ^ 2 ∂rowLaw i) ≤
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
    intro i
    let scalarBatchLaw := onlineBatchLaw A.problem (b0 i)
    let heteroRow := fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i
    let scalarRow := fun batch : (w : Worker n) → Fin (b0 i).1 → Sample w ↦
      batch i
    let localD := fun row : Fin (b0 i).1 → Sample i ↦
      average (fun j : Fin (b0 i).1 ↦
        stochasticGradient A.problem i (row j) xNext -
          stochasticGradient A.problem i (row j) x)
    let delta := localGradientDifference
      (onlineLocalProblem A.problem) i xNext x
    let rows := Measure.infinitePi
      (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
    haveI : IsProbabilityMeasure scalarBatchLaw := by
      unfold scalarBatchLaw onlineBatchLaw
      infer_instance
    have hHetMap : Measure.map heteroRow batchLaw = rows := by
      simpa [heteroRow, batchLaw, rows] using
        heterogeneous_online_batch_law_worker_marginal A.problem b0 i
    have hScalarMap : Measure.map scalarRow scalarBatchLaw = rows := by
      simpa [scalarRow, scalarBatchLaw, rows] using
        onlineBatchLaw_worker_marginal A.problem i
    have hsample (z : Point d) : AEStronglyMeasurable
        (fun xi : Sample i ↦ stochasticGradient A.problem i xi z)
        (A.problem.sampleLaw i) := by
      have hprod :=
        (stochasticGradient_randomQuery_product_regular_of_lawRegularity
          A.problem hRegularity i (Measure.dirac ()) (A.problem.sampleLaw i)
            (fun _ : Unit ↦ z) id aestronglyMeasurable_const measurable_id
            (Measure.map_id)).2
      exact hprod.of_comp_snd Measure.dirac_ne_zero
    have hcoord (j : Fin (b0 i).1) : Measure.map
        (fun row : Fin (b0 i).1 → Sample i ↦ row j) rows =
          A.problem.sampleLaw i := by
      simpa [rows] using
        (MeasureTheory.Measure.infinitePi_map_eval
          (μ := fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i) j)
    have hterm (z : Point d) (j : Fin (b0 i).1) : AEStronglyMeasurable
        (fun row : Fin (b0 i).1 → Sample i ↦
          stochasticGradient A.problem i (row j) z) rows := by
      let eval := fun row : Fin (b0 i).1 → Sample i ↦ row j
      have hqmp : Measure.QuasiMeasurePreserving eval rows
          (A.problem.sampleLaw i) :=
        ⟨measurable_pi_apply j, by
          rw [show Measure.map eval rows = A.problem.sampleLaw i by
            simpa [eval] using hcoord j]⟩
      exact (hsample z).comp_quasiMeasurePreserving hqmp
    have hlocalD : AEStronglyMeasurable localD rows := by
      unfold localD average SOptLib.finiteUniformAverage
      have hs := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ ↦ (hterm xNext j).sub (hterm x j))).const_smul
          ((Fintype.card (Fin (b0 i).1) : ℝ)⁻¹)
      refine hs.congr (Filter.Eventually.of_forall ?_)
      intro row
      simp [Finset.sum_apply, Finset.sum_sub_distrib]
    have hlocalResidual : AEStronglyMeasurable
        (fun row ↦ ‖localD row - delta‖ ^ 2) rows := by
      have hconst : AEStronglyMeasurable
          (fun _ : Fin (b0 i).1 → Sample i ↦ delta) rows :=
        aestronglyMeasurable_const
      exact (hlocalD.sub hconst).norm.pow 2
    have hFiber := hFiber i
    have hDrow : Integrable localD rows := by
      rw [← hHetMap]
      apply (MeasureTheory.integrable_map_measure (by
        rw [hHetMap]
        exact hlocalD) (measurable_pi_apply i).aemeasurable).mpr
      simpa [localD, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw, xNext, x, run] using hFiber.1
    have hResidualRow : Integrable
        (fun row ↦ ‖localD row - delta‖ ^ 2) rows := by
      rw [← hHetMap]
      apply (MeasureTheory.integrable_map_measure (by
        rw [hHetMap]
        exact hlocalResidual) (measurable_pi_apply i).aemeasurable).mpr
      simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw, xNext, x, run] using hFiber.2.1
    have hMeanRow : (∫ row, localD row ∂rows) = delta := by
      rw [← hHetMap, MeasureTheory.integral_map
        (measurable_pi_apply i).aemeasurable
        (by rw [hHetMap]; exact hlocalD)]
      simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw, xNext, x, run] using hFiber.2.2.1
    have hSecondRow : (∫ row, ‖localD row - delta‖ ^ 2 ∂rows) ≤
        (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2 := by
      rw [← hHetMap, MeasureTheory.integral_map
        (measurable_pi_apply i).aemeasurable
        (by rw [hHetMap]; exact hlocalResidual)]
      simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
        batchLaw, xNext, x, run] using hFiber.2.2.2
    have hHomogeneousFiber :
        let delta' := localGradientDifference
          (onlineLocalProblem A.problem) i xNext x
        let D := fun batch ↦ onlineBatchDifference A.problem batch i xNext x
        Integrable D scalarBatchLaw ∧
          Integrable (fun batch ↦ ‖D batch - delta'‖ ^ 2) scalarBatchLaw ∧
          (∫ batch, D batch ∂scalarBatchLaw) = delta' ∧
          (∫ batch, ‖D batch - delta'‖ ^ 2 ∂scalarBatchLaw) ≤
            (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2 := by
      dsimp only
      have hD : Integrable (localD ∘ scalarRow) scalarBatchLaw :=
        (MeasureTheory.integrable_map_measure (by
          rw [hScalarMap]
          exact hlocalD) (measurable_pi_apply i).aemeasurable).mp
          (by rw [hScalarMap]; exact hDrow)
      have hR : Integrable
          ((fun row ↦ ‖localD row - delta‖ ^ 2) ∘ scalarRow)
          scalarBatchLaw :=
        (MeasureTheory.integrable_map_measure (by
          rw [hScalarMap]
          exact hlocalResidual) (measurable_pi_apply i).aemeasurable).mp
          (by rw [hScalarMap]; exact hResidualRow)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [localD, scalarRow, onlineBatchDifference, scalarBatchLaw] using hD
      · simpa [localD, delta, scalarRow, onlineBatchDifference,
          scalarBatchLaw] using hR
      · calc
          (∫ batch, onlineBatchDifference A.problem batch i xNext x
              ∂scalarBatchLaw) =
              ∫ batch, localD (scalarRow batch) ∂scalarBatchLaw := by rfl
          _ = ∫ row, localD row ∂Measure.map scalarRow scalarBatchLaw := by
            rw [MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
              (by rw [hScalarMap]; exact hlocalD)]
          _ = ∫ row, localD row ∂rows := by rw [hScalarMap]
          _ = delta := hMeanRow
      · calc
          (∫ batch,
              ‖onlineBatchDifference A.problem batch i xNext x -
                localGradientDifference (onlineLocalProblem A.problem)
                  i xNext x‖ ^ 2 ∂scalarBatchLaw) =
              ∫ batch, ‖localD (scalarRow batch) - delta‖ ^ 2
                ∂scalarBatchLaw := by rfl
          _ = ∫ row, ‖localD row - delta‖ ^ 2
                ∂Measure.map scalarRow scalarBatchLaw := by
            rw [MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
              (by rw [hScalarMap]; exact hlocalResidual)]
          _ = ∫ row, ‖localD row - delta‖ ^ 2 ∂rows := by rw [hScalarMap]
          _ ≤ _ := hSecondRow
    simpa [localInnovation, rowLaw, rows] using
      (onlineFixed_nonrefresh_worker_row_moment_of_assumption32
        (b0 := b0 i) A xNext x i Llocal ℒlocal ω hSmooth
          hHomogeneousFiber hRegularity hQuantizer)
  have hWhole : Measure.map
      (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        fun i ↦ source i q) law = Measure.infinitePi rowLaw := by
    let α := fun i : Worker n ↦ Fin (b0 i).1 → Sample i
    let β := fun _ : Worker n ↦ Ξ
    let μ := fun i : Worker n ↦
      Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
    let ν := fun _ : Worker n ↦ A.quantizer.law
    have hmp := measurePreserving_dependentArrowProdMeasurableEquiv α β μ ν
    have hinv := MeasurePreserving.symm
      (dependentArrowProdMeasurableEquiv α β) hmp
    simpa [law, batchLaw, compressionLaw, heterogeneousOnlineBatchLaw,
      workerCompressionLaw, source, rowLaw, α, β, μ, ν,
      MeasureTheory.Measure.infinitePi_eq_pi] using hinv.map_eq
  have hindep : ProbabilityTheory.iIndepFun source law := by
    apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun i ↦ hsource i)).2
    rw [hWhole]
    congr 1
    funext i
    exact (hmap i).symm
  have hdiag : ∀ i : Worker n,
      Integrable (fun q ↦ ‖innovation i q‖ ^ 2) law ∧
      (∫ q, ‖innovation i q‖ ^ 2 ∂law) ≤
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
    intro i
    have hsq : AEStronglyMeasurable (fun q ↦ ‖localInnovation i q‖ ^ 2)
        (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hLocalFiber i).2.1.aestronglyMeasurable
    constructor
    · exact (MeasureTheory.integrable_map_measure hsq
        (hsource i).aemeasurable).mp
          (by simpa [hmap i] using (hLocalFiber i).2.1)
    · rw [show (∫ q, ‖innovation i q‖ ^ 2 ∂law) =
          ∫ q, ‖localInnovation i q‖ ^ 2 ∂Measure.map (source i) law by
            rw [MeasureTheory.integral_map (hsource i).aemeasurable hsq],
        hmap i]
      exact (hLocalFiber i).2.2.2
  have hvec : ∀ i : Worker n,
      Integrable (innovation i) law ∧ (∫ q, innovation i q ∂law) = 0 := by
    intro i
    have hm : AEStronglyMeasurable (localInnovation i)
        (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hLocalFiber i).1.aestronglyMeasurable
    constructor
    · exact (MeasureTheory.integrable_map_measure hm
        (hsource i).aemeasurable).mp
          (by simpa [hmap i] using (hLocalFiber i).1)
    · rw [show (∫ q, innovation i q ∂law) =
          ∫ q, localInnovation i q ∂Measure.map (source i) law by
            rw [MeasureTheory.integral_map (hsource i).aemeasurable hm],
        hmap i]
      exact (hLocalFiber i).2.2.1
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) = 0 := by
    intro i j hij
    let fi := localInnovation i
    let fj := localInnovation j
    let fiMk := (hLocalFiber i).1.aestronglyMeasurable.mk fi
    let fjMk := (hLocalFiber j).1.aestronglyMeasurable.mk fj
    have hfiMk : Measurable fiMk :=
      (hLocalFiber i).1.aestronglyMeasurable.measurable_mk
    have hfjMk : Measurable fjMk :=
      (hLocalFiber j).1.aestronglyMeasurable.measurable_mk
    have hfi_ae : fi =ᵐ[rowLaw i] fiMk :=
      (hLocalFiber i).1.aestronglyMeasurable.ae_eq_mk
    have hfj_ae : fj =ᵐ[rowLaw j] fjMk :=
      (hLocalFiber j).1.aestronglyMeasurable.ae_eq_mk
    have hqmpi : Measure.QuasiMeasurePreserving (source i) law (rowLaw i) :=
      ⟨hsource i, by rw [hmap i]⟩
    have hqmpj : Measure.QuasiMeasurePreserving (source j) law (rowLaw j) :=
      ⟨hsource j, by rw [hmap j]⟩
    have hfi_global : innovation i =ᵐ[law] fiMk ∘ source i :=
      hqmpi.tendsto_ae hfi_ae
    have hfj_global : innovation j =ᵐ[law] fjMk ∘ source j :=
      hqmpj.tendsto_ae hfj_ae
    have hfixed_int : ∀ _ : (Fin (b0 j).1 → Sample j) × Ξ,
        Integrable (fun s ↦ fiMk s) (rowLaw i) := by
      intro _
      exact (hLocalFiber i).1.congr hfi_ae
    have hfixed_zero : ∀ _ : (Fin (b0 j).1 → Sample j) × Ξ,
        (∫ s, fiMk s ∂rowLaw i) = 0 := by
      intro _
      rw [← integral_congr_ae hfi_ae]
      exact (hLocalFiber i).2.2.1
    have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      law (rowLaw i) (source j) (source i)
      (fun _ s ↦ fiMk s) fjMk
      (by exact hfiMk.comp measurable_snd) hfjMk
      (hsource j) (hsource i) (hindep.indepFun (Ne.symm hij))
      (hmap i) hfixed_int hfixed_zero
    calc
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) =
          ∫ q, ⟪fiMk (source i q), fjMk (source j q)⟫_ℝ ∂law := by
            apply integral_congr_ae
            filter_upwards [hfi_global, hfj_global] with q hi hj
            simpa [Function.comp_apply] using congrArg₂ (inner ℝ) hi hj
      _ = ∫ q, ⟪fjMk (source j q), fiMk (source i q)⟫_ℝ ∂law := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun q ↦ real_inner_comm _ _
      _ = 0 := hzero
  have hmeas : ∀ i : Worker n, AEStronglyMeasurable (innovation i) law :=
    fun i ↦ (hvec i).1.aestronglyMeasurable
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    law (Finset.univ : Finset (Worker n)) innovation
      (fun i _ ↦ hmeas i) (fun i _ ↦ (hdiag i).1)
      (fun i _ j _ hij ↦ hcross hij)
  have havgSq : Integrable
      (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2) law := by
    apply integrable_sq_norm_centeredMiniBatchAverage law
      (Finset.univ : Finset (Worker n)) n.1 innovation
      (fun q ↦ average (fun i : Worker n ↦ innovation i q))
    · intro i _
      exact hmeas i
    · intro i _
      exact (hdiag i).1
    · funext q
      simp [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
  have havg : Integrable
      (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law := by
    unfold average SOptLib.finiteUniformAverage
    simpa [Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ ↦ (hvec i).1)).smul ((n.1 : ℝ)⁻¹)
  have havgZero :
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 := by
    unfold average SOptLib.finiteUniformAverage
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun i _ ↦ (hvec i).1)]
    simp [hvec]
  refine ⟨by simpa [innovation, law] using havg,
    by simpa [innovation, law] using havgZero,
    by simpa [innovation, law] using havgSq, ?_⟩
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
  calc
    (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) =
        ((n.1 : ℝ)⁻¹) ^ 2 *
          ∫ q, ‖Finset.sum Finset.univ (fun i ↦ innovation i q)‖ ^ 2 ∂law := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      unfold average SOptLib.finiteUniformAverage
      simp only [Fintype.card_fin]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n, ∫ q, ‖innovation i q‖ ^ 2 ∂law := by rw [hsum]
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 * ∑ i : Worker n,
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
      gcongr with i
      exact (hdiag i).2
    _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
      have hmean_nonneg : 0 ≤ meanSquare Llocal := by
        unfold meanSquare average SOptLib.finiteUniformAverage
        positivity
      have hrms : (rootMeanSquare Llocal) ^ 2 = meanSquare Llocal := by
        unfold rootMeanSquare
        exact Real.sq_sqrt hmean_nonneg
      rw [hrms, ← Finset.sum_mul]
      unfold meanSquare heterogeneousFiniteBatchSmoothnessTerm average
        SOptLib.finiteUniformAverage
      simp only [smul_eq_mul, Fintype.card_fin]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ i : Worker n,
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) =
          (1 + ω) * ∑ i : Worker n, (ℒlocal i) ^ 2 / (b0 i).1 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
      field_simp [hn]

/-- Compatibility wrapper for the historical universal-path formulation of
heterogeneous Assumption 3.2.  The proof body above consumes only the fiber at
the displayed generated path. -/
theorem
    heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_of_assumption32_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAverageSmooth : HeterogeneousOnlineAverageSmoothness
      (b := b) (b0 := b0) A x0 ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    let law := (heterogeneousOnlineBatchLaw A.problem b0).prod
      (workerCompressionLaw (n := n) A.quantizer)
    let innovation := fun i : Worker n ↦
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 q.1 i xNext x)
            (q.2 i) -
          localGradientDifference (onlineLocalProblem A.problem) i xNext x
    Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
      Integrable (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
  exact
    heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_of_fibers_and_lawRegularity
      A x0 Llocal ℒlocal ω hSmooth hRegularity hQuantizer k path
        (fun i ↦ hAverageSmooth.2 k i path)

/-- Source-facing genuine-gradient specialization of the worker-dependent
nonrefresh moment at the actual generated executable queries. -/
theorem
    heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_of_genuine_assumption32_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAssumption32 : HeterogeneousOnlineAssumption32Genuine (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    let law := (heterogeneousOnlineBatchLaw A.problem b0).prod
      (workerCompressionLaw (n := n) A.quantizer)
    let innovation := fun i : Worker n ↦
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 q.1 i xNext x)
            (q.2 i) -
          localGradientDifference (onlineLocalProblem A.problem) i xNext x
    Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
      Integrable (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
  exact
    heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_of_assumption32_and_lawRegularity
      A x0 Llocal ℒlocal ω hSmooth
        (heterogeneousOnlineAssumption32Genuine_to_averageSmoothness
          A x0 ℒlocal hAssumption32)
        hRegularity hQuantizer k path

/-- Source-faithful law-a.e. Assumption 3.2 supplies the exact nonrefresh
fiber needed at the generated executable queries.  This avoids strengthening
the printed conditional statement to every null path. -/
theorem
    heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_ae_of_genuine_assumption32_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) :
    ∀ᵐ path ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A,
      let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let law := (heterogeneousOnlineBatchLaw A.problem b0).prod
        (workerCompressionLaw (n := n) A.quantizer)
      let innovation := fun i : Worker n ↦
        fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 q.1 i xNext x)
              (q.2 i) -
            localGradientDifference (onlineLocalProblem A.problem) i xNext x
      Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
        (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
        Integrable
          (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2) law ∧
        (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            ‖xNext - x‖ ^ 2 := by
  have hFormal :=
    heterogeneousOnlineAssumption32GenuineAE_to_averageSmoothnessAE
      A x0 ℒlocal hAssumption32
  filter_upwards [hFormal.2 k] with path hpath
  exact
    heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_of_fibers_and_lawRegularity
      A x0 Llocal ℒlocal ω hSmooth hRegularity hQuantizer k path hpath

/-- Base case for the executable heterogeneous Eq. (46) induction.  Unlike
the proof-exact process, the estimator residual at time zero is random; its
integrability is supplied by the literal fixed-query moment contract through
the canonical worker-dependent initializer law. -/
theorem heterogeneousOnlineProcess_scalar_recurrence_components_zero_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path ↦ (run 0 path).x) law ∧
      AEStronglyMeasurable
        (fun path ↦ (run 0 path).g - globalGradient P (run 0 path).x) law ∧
      Integrable (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) law ∧
      Integrable (fun path ↦ ‖(run 0 path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law 0 ∧
      StepMomentWellDefined run law 0 := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hState : AEMeasurable (run 0) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_zero_aemeasurable_of_literal
        (b := b) (b0 := b0) A x0 σ hLiteral
  have hx : AEStronglyMeasurable (fun path ↦ (run 0 path).x) law :=
    ((measurable_state_x d).comp_aemeasurable hState).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path ↦ (run 0 path).g) law :=
    ((measurable_state_g d).comp_aemeasurable hState).aestronglyMeasurable
  have hgrad : AEStronglyMeasurable
      (fun path ↦ globalGradient P (run 0 path).x) law :=
    ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hr : AEStronglyMeasurable
      (fun path ↦ (run 0 path).g - globalGradient P (run 0 path).x) law :=
    hg.sub hgrad
  have hxl2 : Integrable (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) law := by
    have heq : (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) =
        (fun _ ↦ (0 : ℝ)) := by
      funext path
      change ‖x0 - x0‖ ^ 2 = 0
      simp
    rw [heq]
    exact integrable_const (c := (0 : ℝ))
  have he :=
    (heterogeneous_online_executable_initial_error_moment_le_of_literal
      (b := b) (b0 := b0) A x0 σ hLiteral hSmooth.1).1
  have hgl2 : Integrable (fun path ↦ ‖(run 0 path).g‖ ^ 2) law := by
    have hadd := integrable_sq_norm_add hr hgrad
      (by simpa [EstimatorErrorMomentWellDefined, P, run, law] using he)
      (by
        have heq : (fun path ↦ ‖globalGradient P (run 0 path).x‖ ^ 2) =
            (fun _ ↦ ‖globalGradient P x0‖ ^ 2) := by
          funext path
          rfl
        rw [heq]
        exact integrable_const (c := ‖globalGradient P x0‖ ^ 2))
    apply hadd.congr
    filter_upwards [] with path
    congr 2
    abel
  have hs : StepMomentWellDefined run law 0 := by
    have hscaled := integrable_sq_norm_const_smul
      (-(A.stepSize : ℝ)) hgl2
    simpa [StepMomentWellDefined, run, heterogeneousOnlineProcess,
      SOptLib.recursive_process_from_random_initial, heterogeneousOnlineStep,
      primalStep_eq] using hscaled
  exact ⟨hx, hr, hxl2, hgl2, he, hs⟩

/-- The fresh nonrefresh coordinate of a heterogeneous online round: the
worker-dependent difference minibatch together with the worker compressors.
This is a product-law object, not an added source assumption. -/
noncomputable def heterogeneousOnlineDifferenceCompressionLaw
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) :=
  (heterogeneousOnlineBatchLaw A.problem b0).prod
    (workerCompressionLaw (n := n) A.quantizer)

/-- The canonical heterogeneous round law has exactly the advertised
difference-minibatch/compressor marginal.  This is the law-identification
step needed before fixed-query Assumption 3.2 moments can be integrated at
the generated query. -/
theorem heterogeneousOnlineRoundLaw_differenceCompression_marginal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    Measure.map
        (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
          (z.2.1.2, z.2.2))
        (heterogeneousOnlineRoundLaw A) =
      heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  let batches :=
    (heterogeneousOnlineBatchLaw A.problem b).prod
      (heterogeneousOnlineBatchLaw A.problem b0)
  let compressions := workerCompressionLaw (n := n) A.quantizer
  have hsnd : Measure.map Prod.snd (heterogeneousOnlineRoundLaw A) =
      batches.prod compressions := by
    unfold heterogeneousOnlineRoundLaw
    rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  calc
    Measure.map
        (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
          (z.2.1.2, z.2.2))
        (heterogeneousOnlineRoundLaw A) =
        Measure.map (fun q ↦ (q.1.2, q.2))
          (Measure.map Prod.snd (heterogeneousOnlineRoundLaw A)) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_snd
    _ = Measure.map (fun q ↦ (q.1.2, q.2))
          (batches.prod compressions) := by rw [hsnd]
    _ = (Measure.map Prod.snd batches).prod compressions := by
          symm
          simpa [Prod.map] using
            (MeasureTheory.Measure.map_prod_map batches compressions
              measurable_snd measurable_id)
    _ = (heterogeneousOnlineBatchLaw A.problem b0).prod compressions := by
          rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
    _ = heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A := by
          rfl

/-- The actual generated query pair is independent of the same-round
worker-dependent difference minibatch and compressors.  The theorem is a
direct projection of the already established strict-prefix/current-round
independence and therefore introduces no measurability premise. -/
theorem heterogeneousOnlineQuery_indep_differenceCompression_of_measurable
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (hstate : AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) :
    ProbabilityTheory.IndepFun
      (fun path ↦
        (primalStep A.stepSize
            (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path),
          (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path).x))
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        ((path.2 k).2.1.2, (path.2 k).2.2))
      (heterogeneousOnlinePathLaw A) := by
  have h := heterogeneousOnlineQuery_indep_current_round_of_measurable
    (b := b) (b0 := b0) A x0 k hstate
  exact h.comp measurable_id
    ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

/-- Under the complete executable path law, the round-`k` nonrefresh noise
has the worker-dependent difference/compression product law. -/
theorem heterogeneousOnlinePathLaw_differenceCompression_marginal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) :
    Measure.map
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
          ((path.2 k).2.1.2, (path.2 k).2.2))
        (heterogeneousOnlinePathLaw A) =
      heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let project := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
    (z.2.1.2, z.2.2)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  have hproject : Measurable project := by
    dsimp [project]
    exact (measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have hcurrentLaw : Measure.map current (heterogeneousOnlinePathLaw A) =
      roundLaw := by
    calc
      Measure.map current (heterogeneousOnlinePathLaw A) =
          Measure.map (fun stream : ℕ →
              HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ stream k)
            (Measure.map Prod.snd (heterogeneousOnlinePathLaw A)) := by
              rw [MeasureTheory.Measure.map_map
                (measurable_pi_apply k) measurable_snd]
              rfl
      _ = Measure.map (fun stream : ℕ →
              HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ stream k)
            (SOptLib.iidStreamLaw roundLaw) := by
              rw [show Measure.map Prod.snd (heterogeneousOnlinePathLaw A) =
                  SOptLib.iidStreamLaw roundLaw by
                dsimp [roundLaw, heterogeneousOnlinePathLaw]
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  calc
    Measure.map (project ∘ current) (heterogeneousOnlinePathLaw A) =
        Measure.map project
          (Measure.map current (heterogeneousOnlinePathLaw A)) := by
            rw [MeasureTheory.Measure.map_map hproject hcurrent]
    _ = Measure.map project roundLaw := by rw [hcurrentLaw]
    _ = heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A := by
          simpa [project, roundLaw] using
            heterogeneousOnlineRoundLaw_differenceCompression_marginal
              (b := b) (b0 := b0) A

/-- Source-facing specialization of generated-query/fresh-noise
independence.  Literal Assumption 3.3 supplies initializer measurability and
the separately classified Track-B correction supplies adaptive-gradient
measurability; neither premise assumes the independence conclusion. -/
theorem
    heterogeneousOnlineQuery_indep_differenceCompression_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun path ↦
        (primalStep A.stepSize
            (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path),
          (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path).x))
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        ((path.2 k).2.1.2, (path.2 k).2.2))
      (heterogeneousOnlinePathLaw A) := by
  apply heterogeneousOnlineQuery_indep_differenceCompression_of_measurable
    (b := b) (b0 := b0) A x0 k
  exact heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
    (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k

/- Transfer a law-a.e. fixed-fiber scalar moment through an independent
generated query.  The measurable representative is needed because the
source conditional moment is only an a.e. predicate, while `Measure.map`
transports arbitrary predicates only after a measurable representative has
been chosen. -/
set_option maxHeartbeats 4000000 in
theorem integrable_comp_and_integral_le_of_indep_ae_fixed_fiber
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace S] {mu : Measure Ω} {nu : Measure S}
    [IsFiniteMeasure mu] [SFinite nu]
    (phi : W → S → ℝ) (B : W → ℝ) (X : Ω → W) (Y : Ω → S)
    (hphi : AEStronglyMeasurable (fun p : W × S ↦ phi p.1 p.2)
      ((Measure.map X mu).prod nu))
    (hB : StronglyMeasurable B)
    (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu)
    (hindep : ProbabilityTheory.IndepFun X Y mu)
    (hYLaw : Measure.map Y mu = nu)
    (hfixed : ∀ᵐ omega ∂mu,
      Integrable (phi (X omega)) nu ∧
        (∫ s, phi (X omega) s ∂nu) ≤ B (X omega))
    (hnonneg : ∀ w s, 0 ≤ phi w s)
    (hBComp : Integrable (fun omega ↦ B (X omega)) mu) :
    Integrable (fun omega ↦ phi (X omega) (Y omega)) mu ∧
      (∫ omega, phi (X omega) (Y omega) ∂mu) ≤
        ∫ omega, B (X omega) ∂mu := by
  let phiM := hphi.mk (fun p : W × S => phi p.1 p.2)
  have hphiM : StronglyMeasurable phiM := hphi.stronglyMeasurable_mk
  have hfiberEq : ∀ᵐ w ∂Measure.map X mu,
      (fun s ↦ phi w s) =ᵐ[nu] (fun s ↦ phiM (w, s)) := by
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hphi.ae_eq_mk
  have hfiberEqComp : ∀ᵐ omega ∂mu,
      (fun s ↦ phi (X omega) s) =ᵐ[nu]
        (fun s ↦ phiM (X omega, s)) :=
    MeasureTheory.ae_of_ae_map hX hfiberEq
  have hIntMComp : ∀ᵐ omega ∂mu,
      Integrable (fun s ↦ phiM (X omega, s)) nu := by
    filter_upwards [hfixed, hfiberEqComp] with omega hm heq
    exact hm.1.congr heq
  have hIntMSet : MeasurableSet
      {w : W | Integrable (fun s ↦ phiM (w, s)) nu} := by
    apply measurableSet_integrable
    simpa [Function.uncurry] using hphiM
  have hIntM : ∀ᵐ w ∂Measure.map X mu,
      Integrable (fun s ↦ phiM (w, s)) nu :=
    (MeasureTheory.ae_map_iff hX hIntMSet).2 hIntMComp
  have hfixedInt : ∀ᵐ w ∂Measure.map X mu,
      Integrable (phi w) nu := by
    filter_upwards [hIntM, hfiberEq] with w hm heq
    exact hm.congr heq.symm
  let fiberM := fun w : W ↦ ∫ s, phiM (w, s) ∂nu
  have hfiberM : StronglyMeasurable fiberM := by
    dsimp [fiberM]
    apply StronglyMeasurable.integral_prod_right
    simpa [Function.uncurry] using hphiM
  have hBoundMComp : ∀ᵐ omega ∂mu,
      fiberM (X omega) ≤ B (X omega) := by
    filter_upwards [hfixed, hfiberEqComp] with omega hm heq
    calc
      fiberM (X omega) = ∫ s, phi (X omega) s ∂nu := by
        dsimp [fiberM]
        exact integral_congr_ae heq.symm
      _ ≤ B (X omega) := hm.2
  have hBoundMSet : MeasurableSet {w : W | fiberM w ≤ B w} :=
    measurableSet_le hfiberM.measurable hB.measurable
  have hBoundM : ∀ᵐ w ∂Measure.map X mu, fiberM w ≤ B w :=
    (MeasureTheory.ae_map_iff hX hBoundMSet).2 hBoundMComp
  have hfixedNormBound : ∀ᵐ w ∂Measure.map X mu,
      (∫ s, ‖phi w s‖ ∂nu) ≤ B w := by
    filter_upwards [hBoundM, hfiberEq] with w hbound heq
    calc
      (∫ s, ‖phi w s‖ ∂nu) = ∫ s, phi w s ∂nu := by
        apply integral_congr_ae
        filter_upwards [] with s
        exact Real.norm_of_nonneg (hnonneg w s)
      _ = fiberM w := by
        dsimp [fiberM]
        exact integral_congr_ae heq
      _ ≤ B w := hbound
  have hBMap : Integrable B (Measure.map X mu) :=
    (MeasureTheory.integrable_map_measure hB.aestronglyMeasurable hX).2 hBComp
  have hprodInt : Integrable (fun p : W × S ↦ phi p.1 p.2)
      ((Measure.map X mu).prod nu) :=
    integrable_prod_of_fiber_integral_norm_le_integrable_bound
      hphi hfixedInt hBMap hfixedNormBound
  have hjoint : AEMeasurable (fun omega ↦ (X omega, Y omega)) mu :=
    hX.prodMk hY
  have hjointLaw : Measure.map (fun omega ↦ (X omega, Y omega)) mu =
      (Measure.map X mu).prod nu := by
    rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX hY).mp
      hindep, hYLaw]
  have hphiJoint : AEStronglyMeasurable (fun p : W × S ↦ phi p.1 p.2)
      (Measure.map (fun omega ↦ (X omega, Y omega)) mu) := by
    rw [hjointLaw]
    exact hphi
  have hcompInt : Integrable (fun omega ↦ phi (X omega) (Y omega)) mu :=
    (MeasureTheory.integrable_map_measure hphiJoint hjoint).1 (by
      rw [hjointLaw]
      exact hprodInt)
  refine ⟨hcompInt, ?_⟩
  calc
    (∫ omega, phi (X omega) (Y omega) ∂mu) =
        ∫ p, phi p.1 p.2
          ∂Measure.map (fun omega ↦ (X omega, Y omega)) mu := by
            exact (MeasureTheory.integral_map hjoint hphiJoint).symm
    _ = ∫ p, phi p.1 p.2 ∂(Measure.map X mu).prod nu := by
          rw [hjointLaw]
    _ = ∫ w, ∫ s, phi w s ∂nu ∂Measure.map X mu :=
          MeasureTheory.integral_prod _ hprodInt
    _ ≤ ∫ w, B w ∂Measure.map X mu :=
          MeasureTheory.integral_mono_ae hprodInt.integral_prod_left hBMap
            (by
              filter_upwards [hBoundM, hfiberEq] with w hbound heq
              calc
                (∫ s, phi w s ∂nu) = fiberM w := by
                  dsimp [fiberM]
                  exact integral_congr_ae heq
                _ ≤ B w := hbound)
    _ = ∫ omega, B (X omega) ∂mu :=
          MeasureTheory.integral_map hX hB.aestronglyMeasurable

/- Transfer law-a.e. centered fibers through an independent generated query.
Unlike the library's pointwise-fiber theorem, this version matches a source
conditional moment which is available only at generated paths almost surely. -/
theorem integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
    {Ω W S V : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {mu : Measure Ω} {nu : Measure S} [IsFiniteMeasure mu]
    (phi : W → S → V) (X : Ω → W) (Y : Ω → S)
    (hphi : AEStronglyMeasurable (fun p : W × S ↦ phi p.1 p.2)
      ((Measure.map X mu).prod nu))
    (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu)
    (hindep : ProbabilityTheory.IndepFun X Y mu)
    (hYLaw : Measure.map Y mu = nu)
    (hcomp : Integrable (fun omega ↦ phi (X omega) (Y omega)) mu)
    (hfixed : ∀ᵐ omega ∂mu, (∫ s, phi (X omega) s ∂nu) = 0) :
    (∫ omega, phi (X omega) (Y omega) ∂mu) = 0 := by
  letI : IsFiniteMeasure nu := by
    rw [← hYLaw]
    exact Measure.isFiniteMeasure_map mu Y
  let phiM := hphi.mk (fun p : W × S ↦ phi p.1 p.2)
  have hphiM : StronglyMeasurable phiM := hphi.stronglyMeasurable_mk
  have hfiberEq : ∀ᵐ w ∂Measure.map X mu,
      (fun s ↦ phi w s) =ᵐ[nu] (fun s ↦ phiM (w, s)) := by
    exact MeasureTheory.Measure.ae_ae_of_ae_prod hphi.ae_eq_mk
  have hfiberEqComp : ∀ᵐ omega ∂mu,
      (fun s ↦ phi (X omega) s) =ᵐ[nu]
        (fun s ↦ phiM (X omega, s)) :=
    MeasureTheory.ae_of_ae_map hX hfiberEq
  let fiberM := fun w : W ↦ ∫ s, phiM (w, s) ∂nu
  have hfiberM : StronglyMeasurable fiberM := by
    dsimp [fiberM]
    apply StronglyMeasurable.integral_prod_right
    simpa [Function.uncurry] using hphiM
  have hzeroComp : ∀ᵐ omega ∂mu, fiberM (X omega) = 0 := by
    filter_upwards [hfixed, hfiberEqComp] with omega hz heq
    calc
      fiberM (X omega) = ∫ s, phi (X omega) s ∂nu := by
        dsimp [fiberM]
        exact integral_congr_ae heq.symm
      _ = 0 := hz
  have hzeroSet : MeasurableSet {w : W | fiberM w = 0} :=
    measurableSet_eq_fun hfiberM.measurable measurable_const
  have hzeroM : ∀ᵐ w ∂Measure.map X mu, fiberM w = 0 :=
    (MeasureTheory.ae_map_iff hX hzeroSet).2 hzeroComp
  have hzero : ∀ᵐ w ∂Measure.map X mu,
      (∫ s, phi w s ∂nu) = 0 := by
    filter_upwards [hzeroM, hfiberEq] with w hz heq
    calc
      (∫ s, phi w s ∂nu) = fiberM w := by
        dsimp [fiberM]
        exact integral_congr_ae heq
      _ = 0 := hz
  have hjoint : AEMeasurable (fun omega ↦ (X omega, Y omega)) mu :=
    hX.prodMk hY
  have hjointLaw : Measure.map (fun omega ↦ (X omega, Y omega)) mu =
      (Measure.map X mu).prod nu := by
    rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX hY).mp
      hindep, hYLaw]
  have hphiJoint : AEStronglyMeasurable (fun p : W × S ↦ phi p.1 p.2)
      (Measure.map (fun omega ↦ (X omega, Y omega)) mu) := by
    rw [hjointLaw]
    exact hphi
  have hprodInt : Integrable (fun p : W × S ↦ phi p.1 p.2)
      ((Measure.map X mu).prod nu) := by
    rw [← hjointLaw]
    exact (MeasureTheory.integrable_map_measure hphiJoint hjoint).2 hcomp
  calc
    (∫ omega, phi (X omega) (Y omega) ∂mu) =
        ∫ p : W × S, phi p.1 p.2
          ∂Measure.map (fun omega ↦ (X omega, Y omega)) mu := by
            exact (MeasureTheory.integral_map hjoint hphiJoint).symm
    _ = ∫ p : W × S, phi p.1 p.2 ∂(Measure.map X mu).prod nu := by
          rw [hjointLaw]
    _ = ∫ w : W, ∫ s : S, phi w s ∂nu ∂Measure.map X mu :=
          MeasureTheory.integral_prod _ hprodInt
    _ = 0 := integral_eq_zero_of_ae hzero

set_option maxHeartbeats 8000000 in
/-- The law-a.e. source Assumption 3.2 fiber controls the actual fresh
nonrefresh innovation of proof-exact Algorithm 3.  This is the homogeneous
counterpart of the heterogeneous transfer below: the generated query is kept
under `onlineProofExactPathLaw`, and no condition is imposed on null paths. -/
theorem
    onlineProofExact_nonrefresh_innovation_second_moment_of_genuine_assumption32AE_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hStep : StepMomentWellDefined
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem (path k).2.1.2 i
              (run (k + 1) path).x (run k path).x)
            ((path k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    Integrable (fun path ↦ ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((run (k + 1) path).x, (run k path).x)
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((path k).2.1.2, (path k).2.2)
  let kernel := fun w : Point d × Point d ↦
      fun q : ((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i w.1 w.2) (q.2 i) -
            localGradientDifference P i w.1 w.2)
  let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem (path k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  let B := fun w : Point d × Point d ↦ C * ‖w.1 - w.2‖ ^ 2
  let phi := fun w : Point d × Point d ↦
    fun q : ((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ) ↦
      ‖kernel w q‖ ^ 2
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
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
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  have hstate (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      onlineProofExactProcess_aemeasurable_of_lawRegularity
        A x0 hBatch hRegularity t
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    ((measurable_state_x d).comp_aemeasurable (hstate k)).aestronglyMeasurable
  have hresidual : AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law := by
    exact (((measurable_state_g d).comp_aemeasurable (hstate k)).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable (hstate k)))).aestronglyMeasurable
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_state_x d).comp_aemeasurable (hstate (k + 1))).prodMk
      ((measurable_state_x d).comp_aemeasurable (hstate k))
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hfresh := onlineProofExact_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hindep : ProbabilityTheory.IndepFun query noise law := by
    have h := hfresh.2.1.comp
      (show Measurable
        (fun p : (Point d × Point d) × Point d ↦ p.1) by fun_prop)
      measurable_id
    simpa [query, noise, run, law, P] using h
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    simpa [noise, law, noiseLaw] using hfresh.2.2
  have hkernel : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ↦
        kernel p.1 p.2) ((Measure.map query law).prod noiseLaw) := by
    simpa [kernel, noiseLaw, P] using
      onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity (Measure.map query law)
          (fun w : Point d × Point d ↦ w.1)
          (fun w : Point d × Point d ↦ w.2)
          measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
  have hphi : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ↦
        phi p.1 p.2) ((Measure.map query law).prod noiseLaw) := by
    simpa [phi, pow_two] using hkernel.norm.mul hkernel.norm
  have hMomentPath : ∀ᵐ path ∂law,
      Integrable (phi (query path)) noiseLaw ∧
        (∫ q, phi (query path) q ∂noiseLaw) ≤ B (query path) := by
    have hMoment := onlineFixed_nonrefresh_average_moment_ae_of_genuine_assumption32
      (b0 := b0) A run law Llocal ℒlocal omega hSmooth hAssumption32
        hRegularity hQuantizer k
    filter_upwards [hMoment] with path hpath
    dsimp only at hpath
    refine ⟨?_, ?_⟩
    · simpa [phi, kernel, query, noiseLaw, run, P] using hpath.2.2.1
    · simpa [phi, kernel, query, noiseLaw, B, C, run, P] using hpath.2.2.2
  have hB : StronglyMeasurable B := by
    dsimp [B]
    fun_prop
  have hBComp : Integrable (fun path ↦ B (query path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    dsimp [B, query, run]
  have htransfer :
      Integrable (fun path ↦ phi (query path) (noise path)) law ∧
        (∫ path, phi (query path) (noise path) ∂law) ≤
          ∫ path, B (query path) ∂law :=
    integrable_comp_and_integral_le_of_indep_ae_fixed_fiber
      phi B query noise hphi hB hquery hnoise.aemeasurable hindep hnoiseLaw
        hMomentPath (fun _ _ ↦ sq_nonneg _) hBComp
  have hinnovationEq : ∀ path,
      kernel (query path) (noise path) = innovation path := by
    intro path
    dsimp [kernel, query, noise, innovation, run, P]
  have hactualInt : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law := by
    apply htransfer.1.congr
    filter_upwards [] with path
    simpa only [phi] using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
      (hinnovationEq path)
  refine ⟨hactualInt, ?_⟩
  calc
    (∫ path, ‖innovation path‖ ^ 2 ∂law) =
        ∫ path, phi (query path) (noise path) ∂law := by
          apply integral_congr_ae
          filter_upwards [] with path
          simpa only [phi] using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
            (hinnovationEq path).symm
    _ ≤ ∫ path, B (query path) ∂law := htransfer.2
    _ = C * stepMoment run law k := by
      unfold stepMoment
      rw [← integral_const_mul]
    _ = (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k := by rfl

set_option maxHeartbeats 8000000 in
/-- The actual proof-exact nonrefresh innovation is centered under the
canonical path law from the law-a.e. source Assumption 3.2 contract.  The
fresh-noise product law transports only the generated-query fibers; it does
not manufacture an every-path source premise. -/
theorem
    onlineProofExact_nonrefresh_innovation_integrable_and_centered_of_genuine_assumption32AE_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hStep : StepMomentWellDefined
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem (path k).2.1.2 i
              (run (k + 1) path).x (run k path).x)
            ((path k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    Integrable innovation law ∧ (∫ path, innovation path ∂law) = 0 := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((run (k + 1) path).x, (run k path).x)
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((path k).2.1.2, (path k).2.2)
  let kernel := fun w : Point d × Point d ↦
      fun q : ((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i w.1 w.2) (q.2 i) -
            localGradientDifference P i w.1 w.2)
  let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem (path k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
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
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  have hstate (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      onlineProofExactProcess_aemeasurable_of_lawRegularity
        A x0 hBatch hRegularity t
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    ((measurable_state_x d).comp_aemeasurable (hstate k)).aestronglyMeasurable
  have hresidual : AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law := by
    exact (((measurable_state_g d).comp_aemeasurable (hstate k)).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable (hstate k)))).aestronglyMeasurable
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_state_x d).comp_aemeasurable (hstate (k + 1))).prodMk
      ((measurable_state_x d).comp_aemeasurable (hstate k))
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hfresh := onlineProofExact_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hindep : ProbabilityTheory.IndepFun query noise law := by
    have h := hfresh.2.1.comp
      (show Measurable
        (fun p : (Point d × Point d) × Point d ↦ p.1) by fun_prop)
      measurable_id
    simpa [query, noise, run, law, P] using h
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    simpa [noise, law, noiseLaw] using hfresh.2.2
  have hkernel : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ↦
        kernel p.1 p.2) ((Measure.map query law).prod noiseLaw) := by
    simpa [kernel, noiseLaw, P] using
      onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity (Measure.map query law)
          (fun w : Point d × Point d ↦ w.1)
          (fun w : Point d × Point d ↦ w.2)
          measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
  have hinnovationEq : ∀ path,
      kernel (query path) (noise path) = innovation path := by
    intro path
    dsimp [kernel, query, noise, innovation, run, P]
  have hkernelMapped : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ↦
        kernel p.1 p.2)
      ((Measure.map query law).prod (Measure.map noise law)) := by
    rw [hnoiseLaw]
    exact hkernel
  have hkernelComp : AEStronglyMeasurable
      (fun path ↦ kernel (query path) (noise path)) law :=
    aestronglyMeasurable_comp_of_indep_product_law
      hquery hnoise.aemeasurable
      (inferInstance : SigmaFinite (Measure.map query law))
      (inferInstance : SigmaFinite (Measure.map noise law))
      hindep hkernelMapped
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hkernelComp.congr (Filter.Eventually.of_forall hinnovationEq)
  have hsq :=
    onlineProofExact_nonrefresh_innovation_second_moment_of_genuine_assumption32AE_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hBatch
        hAssumption32 hRegularity hQuantizer k hStep
  have hinnovationInt : Integrable innovation law :=
    integrable_of_integrable_norm_sq hinnovationMeas (by
      simpa [innovation, P, run, law] using hsq.1)
  have hfixed : ∀ᵐ path ∂law,
      (∫ q, kernel (query path) q ∂noiseLaw) = 0 := by
    have hm := onlineFixed_nonrefresh_average_moment_ae_of_genuine_assumption32
      (b0 := b0) A run law Llocal ℒlocal omega hSmooth hAssumption32
        hRegularity hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    simpa [kernel, query, noiseLaw, run, P] using hp.2.1
  have hmeanComp :
      (∫ path, kernel (query path) (noise path) ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      kernel query noise hkernel hquery hnoise.aemeasurable hindep hnoiseLaw
    · exact hinnovationInt.congr
        (Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm)
    · exact hfixed
  refine ⟨hinnovationInt, ?_⟩
  rw [show (∫ path, innovation path ∂law) =
      ∫ path, kernel (query path) (noise path) ∂law by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm]
  exact hmeanComp

set_option maxHeartbeats 16000000 in
/-- The carried proof-exact estimator residual is orthogonal in expectation
to the actual fresh nonrefresh innovation under the law-a.e. source
Assumption 3.2 contract.  Hence the homogeneous nonrefresh branch has the
exact Pythagorean `L²` decomposition without imposing genuine-gradient
moment hypotheses on null paths. -/
theorem
    onlineProofExact_nonrefresh_branch_moments_of_genuine_assumption32AE_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      (run k path).g - globalGradient P (run k path).x
    let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem (path k).2.1.2 i
              (run (k + 1) path).x (run k path).x)
            ((path k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 ∧
      Integrable (fun path ↦ ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment P run law k +
          (1 / (n.1 : ℝ)) *
            (omega * (rootMeanSquare Llocal) ^ 2 +
              (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((run (k + 1) path).x, (run k path).x)
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((path k).2.1.2, (path k).2.2)
  let kernel := fun w : Point d × Point d ↦
      fun q : ((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i w.1 w.2) (q.2 i) -
            localGradientDifference P i w.1 w.2)
  let direction := fun w : Point d × Point d ↦
    w.2 - w.1 - (A.stepSize : ℝ) • globalGradient P w.2
  let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem (path k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
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
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  have hstate (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      onlineProofExactProcess_aemeasurable_of_lawRegularity
        A x0 hBatch hRegularity t
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    ((measurable_state_x d).comp_aemeasurable (hstate k)).aestronglyMeasurable
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable (hstate k)).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable (hstate k)))).aestronglyMeasurable
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_state_x d).comp_aemeasurable (hstate (k + 1))).prodMk
      ((measurable_state_x d).comp_aemeasurable (hstate k))
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hfresh := onlineProofExact_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidualMeas
  have hindep : ProbabilityTheory.IndepFun query noise law := by
    have h := hfresh.2.1.comp
      (show Measurable
        (fun p : (Point d × Point d) × Point d ↦ p.1) by fun_prop)
      measurable_id
    simpa [query, noise, run, law, P] using h
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    simpa [noise, law, noiseLaw] using hfresh.2.2
  have hkernel : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ↦
        kernel p.1 p.2) ((Measure.map query law).prod noiseLaw) := by
    simpa [kernel, noiseLaw, P] using
      onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity (Measure.map query law)
          (fun w : Point d × Point d ↦ w.1)
          (fun w : Point d × Point d ↦ w.2)
          measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
  have hdirection : StronglyMeasurable direction := by
    dsimp [direction]
    exact ((measurable_snd.sub measurable_fst).sub
      (((measurable_gradient (globalObjective P)).comp measurable_snd)
        |>.const_smul (A.stepSize : ℝ))).stronglyMeasurable
  have hscalar : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ↦
        ⟪direction p.1, kernel p.1 p.2⟫_ℝ)
      ((Measure.map query law).prod noiseLaw) :=
    hdirection.aestronglyMeasurable.comp_fst.inner hkernel
  have hinnovationEq : ∀ path,
      kernel (query path) (noise path) = innovation path := by
    intro path
    dsimp [kernel, query, noise, innovation, run, P]
  have hdirectionEq : ∀ path,
      direction (query path) = (A.stepSize : ℝ) • residual path := by
    intro path
    dsimp [direction, query, residual, run]
    rw [show
      (onlineProofExactProcess A x0 hBatch (k + 1) path).x =
        primalStep A.stepSize
          (onlineProofExactProcess A x0 hBatch k path) by rfl]
    rw [primalStep_eq]
    module
  have hcentered :=
    onlineProofExact_nonrefresh_innovation_integrable_and_centered_of_genuine_assumption32AE_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hBatch
        hAssumption32 hRegularity hQuantizer k hStep
  have hinnovationInt : Integrable innovation law := by
    simpa [innovation, P, run, law] using hcentered.1
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hinnovationInt.aestronglyMeasurable
  have hinnovationSq :=
    onlineProofExact_nonrefresh_innovation_second_moment_of_genuine_assumption32AE_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hBatch
        hAssumption32 hRegularity hQuantizer k hStep
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hinnovationSqInt : Integrable
      (fun path ↦ ‖innovation path‖ ^ 2) law := by
    simpa [innovation, P, run, law] using hinnovationSq.1
  have hinnerInt : Integrable
      (fun path ↦ ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq hinnovationSqInt
  have hscalarCompInt : Integrable
      (fun path ↦ ⟪direction (query path), kernel (query path) (noise path)⟫_ℝ)
      law := by
    have hs := hinnerInt.const_mul (A.stepSize : ℝ)
    apply hs.congr
    filter_upwards [] with path
    rw [hdirectionEq path, hinnovationEq path]
    rw [real_inner_smul_left]
  have hfixed : ∀ᵐ path ∂law,
      (∫ q, ⟪direction (query path), kernel (query path) q⟫_ℝ
        ∂noiseLaw) = 0 := by
    have hm := onlineFixed_nonrefresh_average_moment_ae_of_genuine_assumption32
      (b0 := b0) A run law Llocal ℒlocal omega hSmooth hAssumption32
        hRegularity hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction (query path))) hp.1
    calc
      (∫ q, ⟪direction (query path), kernel (query path) q⟫_ℝ
          ∂noiseLaw) =
          (innerSL ℝ) (direction (query path))
            (∫ q, kernel (query path) q ∂noiseLaw) := hlin
      _ = 0 := by
        rw [show (∫ q, kernel (query path) q ∂noiseLaw) = 0 by
          simpa [kernel, query, noiseLaw, run, P] using hp.2.1]
        simp
  have hscaledCross :
      (∫ path,
        ⟪direction (query path), kernel (query path) (noise path)⟫_ℝ
        ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      (fun w q ↦ ⟪direction w, kernel w q⟫_ℝ) query noise hscalar
        hquery hnoise.aemeasurable hindep hnoiseLaw hscalarCompInt hfixed
  have hcross :
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    have hmul : (A.stepSize : ℝ) *
        (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
      rw [← integral_const_mul]
      calc
        (∫ path, (A.stepSize : ℝ) *
            ⟪residual path, innovation path⟫_ℝ ∂law) =
            ∫ path,
              ⟪direction (query path), kernel (query path) (noise path)⟫_ℝ
              ∂law := by
                apply integral_congr_ae
                filter_upwards [] with path
                rw [hdirectionEq path, hinnovationEq path]
                rw [real_inner_smul_left]
        _ = 0 := hscaledCross
    exact (mul_eq_zero.mp hmul).resolve_left
      (ne_of_gt A.stepSize.property)
  have hnonrefreshInt : Integrable
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresidualMeas hinnovationMeas
      hresidualSq hinnovationSqInt
  have hnonrefreshEq :
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          ∫ path, ‖innovation path‖ ^ 2 ∂law := by
    let pair : Bool → (ℕ → OnlineRoundNoise n b b0 Sample Ξ) → Point d :=
      fun z ↦ if z then innovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      law (Finset.univ : Finset Bool) pair
      (fun z _ ↦ by cases z <;> simp [pair, hresidualMeas, hinnovationMeas])
      (fun z _ ↦ by cases z <;> simp [pair, hresidualSq, hinnovationSqInt])
      (fun z _ w _ hzw ↦ by
        cases z <;> cases w
        · exact False.elim (hzw rfl)
        · simpa [pair] using hcross
        · simpa [pair, real_inner_comm] using hcross
        · exact False.elim (hzw rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  refine ⟨hcross, hnonrefreshInt, ?_⟩
  rw [hnonrefreshEq]
  change estimatorErrorMoment P run law k +
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
    estimatorErrorMoment P run law k + C * stepMoment run law k
  exact add_le_add_right (by
    simpa [innovation, P, run, law, C] using hinnovationSq.2) _

set_option maxHeartbeats 8000000 in
/-- The fixed-query worker-dependent Assumption 3.2 moment transfers to the
actual fresh nonrefresh innovation of executable heterogeneous Algorithm 3.
The source premise is kept in its law-a.e. conditional form: the proof moves
that full-measure fiber through the generated-query pushforward before using
the query/noise product law. -/
theorem
    heterogeneousOnlineExecutable_nonrefresh_innovation_second_moment_of_genuine_assumption32AE_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal sigma : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hStep : StepMomentWellDefined
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0
              (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
            ((path.2 k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    Integrable (fun path ↦ ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run law k := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let noiseLaw := heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (primalStep A.stepSize (run k path), (run k path).x)
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    ((path.2 k).2.1.2, (path.2 k).2.2)
  let kernel := fun w : Point d × Point d ↦
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 q.1 i w.1 w.2)
              (q.2 i) -
            localGradientDifference P i w.1 w.2)
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  let B := fun w : Point d × Point d ↦ C * ‖w.1 - w.2‖ ^ 2
  let phi := fun w : Point d × Point d ↦
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        ‖kernel w q‖ ^ 2
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw heterogeneousOnlineDifferenceCompressionLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hindep : ProbabilityTheory.IndepFun query noise law := by
    simpa [query, noise, run, law] using
      heterogeneousOnlineQuery_indep_differenceCompression_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    simpa [noise, law, noiseLaw] using
      heterogeneousOnlinePathLaw_differenceCompression_marginal
        (b := b) (b0 := b0) A k
  have hkernel : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        kernel p.1 p.2)
      ((Measure.map query law).prod noiseLaw) := by
    simpa [kernel, noiseLaw, P] using
      heterogeneousOnlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity (Measure.map query law)
          (fun w : Point d × Point d ↦ w.1)
          (fun w : Point d × Point d ↦ w.2)
          measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
  have hphi : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        phi p.1 p.2)
      ((Measure.map query law).prod noiseLaw) := by
    simpa [phi, pow_two] using hkernel.norm.mul hkernel.norm
  have hMomentPath : ∀ᵐ path ∂law,
      Integrable (phi (query path)) noiseLaw ∧
        (∫ q, phi (query path) q ∂noiseLaw) ≤ B (query path) := by
    have hMoment :=
      heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_ae_of_genuine_assumption32_and_lawRegularity
        (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth
          hAssumption32 hRegularity hQuantizer k
    filter_upwards [hMoment] with path hpath
    have hxNext : (run (k + 1) path).x =
        primalStep A.stepSize (run k path) := rfl
    dsimp only at hpath
    rw [hxNext] at hpath
    refine ⟨?_, ?_⟩
    · simpa [phi, kernel, query, noiseLaw, run, P] using hpath.2.2.1
    · simpa [phi, kernel, query, noiseLaw, B, C, run, P] using hpath.2.2.2
  have hB : StronglyMeasurable B := by
    dsimp [B]
    fun_prop
  have hBComp : Integrable (fun path ↦ B (query path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    dsimp [B, query, run]
    rfl
  have htransfer :
      Integrable (fun path ↦ phi (query path) (noise path)) law ∧
        (∫ path, phi (query path) (noise path) ∂law) ≤
          ∫ path, B (query path) ∂law :=
    integrable_comp_and_integral_le_of_indep_ae_fixed_fiber
      phi B query noise hphi hB hquery hnoise.aemeasurable hindep hnoiseLaw
        hMomentPath (fun _ _ ↦ sq_nonneg _) hBComp
  have hinnovationEq : ∀ path, kernel (query path) (noise path) = innovation path := by
    intro path
    dsimp [kernel, query, noise, innovation, run, P]
    rfl
  have hactualInt : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law := by
    apply htransfer.1.congr
    filter_upwards [] with path
    simpa only [phi] using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
      (hinnovationEq path)
  refine ⟨hactualInt, ?_⟩
  calc
    (∫ path, ‖innovation path‖ ^ 2 ∂law) =
        ∫ path, phi (query path) (noise path) ∂law := by
          apply integral_congr_ae
          filter_upwards [] with path
          simpa only [phi] using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
            (hinnovationEq path).symm
    _ ≤ ∫ path, B (query path) ∂law := htransfer.2
    _ = C * stepMoment run law k := by
      unfold stepMoment
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with path
      dsimp [B, query, run]
      rfl
    _ = (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run law k := by rfl

set_option maxHeartbeats 8000000 in
/-- The actual fresh nonrefresh innovation of executable heterogeneous
Algorithm 3 is centered under the canonical path law.  The source
Assumption 3.2 fiber is only law-a.e.; freshness transports that centered
fiber to the generated query without strengthening it to every null path. -/
theorem
    heterogeneousOnlineExecutable_nonrefresh_innovation_integrable_and_centered_of_genuine_assumption32AE_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal sigma : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hStep : StepMomentWellDefined
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0
              (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
            ((path.2 k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    Integrable innovation law ∧ (∫ path, innovation path ∂law) = 0 := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let noiseLaw := heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (primalStep A.stepSize (run k path), (run k path).x)
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    ((path.2 k).2.1.2, (path.2 k).2.2)
  let kernel := fun w : Point d × Point d ↦
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 q.1 i w.1 w.2)
              (q.2 i) -
            localGradientDifference P i w.1 w.2)
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw heterogeneousOnlineDifferenceCompressionLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hindep : ProbabilityTheory.IndepFun query noise law := by
    simpa [query, noise, run, law] using
      heterogeneousOnlineQuery_indep_differenceCompression_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    simpa [noise, law, noiseLaw] using
      heterogeneousOnlinePathLaw_differenceCompression_marginal
        (b := b) (b0 := b0) A k
  have hkernel : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        kernel p.1 p.2)
      ((Measure.map query law).prod noiseLaw) := by
    simpa [kernel, noiseLaw, P] using
      heterogeneousOnlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity (Measure.map query law)
          (fun w : Point d × Point d ↦ w.1)
          (fun w : Point d × Point d ↦ w.2)
          measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
  have hinnovationEq : ∀ path,
      kernel (query path) (noise path) = innovation path := by
    intro path
    dsimp [kernel, query, noise, innovation, run, P]
    rfl
  have hkernelMapped : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        kernel p.1 p.2)
      ((Measure.map query law).prod (Measure.map noise law)) := by
    rw [hnoiseLaw]
    exact hkernel
  have hkernelComp : AEStronglyMeasurable
      (fun path ↦ kernel (query path) (noise path)) law :=
    aestronglyMeasurable_comp_of_indep_product_law
      hquery hnoise.aemeasurable
      (inferInstance : SigmaFinite (Measure.map query law))
      (inferInstance : SigmaFinite (Measure.map noise law))
      hindep hkernelMapped
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hkernelComp.congr (Filter.Eventually.of_forall hinnovationEq)
  have hsq :=
    heterogeneousOnlineExecutable_nonrefresh_innovation_second_moment_of_genuine_assumption32AE_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal sigma omega hSmooth hLiteral
        hAssumption32 hRegularity hQuantizer k hStep
  have hinnovationInt : Integrable innovation law :=
    integrable_of_integrable_norm_sq hinnovationMeas (by
      simpa [innovation, P, run, law] using hsq.1)
  have hfixed : ∀ᵐ path ∂law,
      (∫ q, kernel (query path) q ∂noiseLaw) = 0 := by
    have hm :=
      heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_ae_of_genuine_assumption32_and_lawRegularity
        (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth
          hAssumption32 hRegularity hQuantizer k
    filter_upwards [hm] with path hp
    have hxNext : (run (k + 1) path).x =
        primalStep A.stepSize (run k path) := rfl
    dsimp only at hp
    rw [hxNext] at hp
    simpa [kernel, query, noiseLaw, run, P] using hp.2.1
  have hmeanComp :
      (∫ path, kernel (query path) (noise path) ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      kernel query noise hkernel hquery hnoise.aemeasurable hindep hnoiseLaw
    · exact hinnovationInt.congr
        (Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm)
    · exact hfixed
  refine ⟨hinnovationInt, ?_⟩
  rw [show (∫ path, innovation path ∂law) =
      ∫ path, kernel (query path) (noise path) ∂law by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm]
  exact hmeanComp

set_option maxHeartbeats 16000000 in
/-- The carried estimator residual is orthogonal in expectation to the actual
fresh heterogeneous nonrefresh innovation.  Consequently the nonrefresh
branch has the exact Pythagorean `L²` decomposition and the Remark D.2
worker-dependent Assumption 3.2 coefficient. -/
theorem
    heterogeneousOnlineExecutable_nonrefresh_branch_moments_of_genuine_assumption32AE_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal sigma : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      (run k path).g - globalGradient P (run k path).x
    let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0
              (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
            ((path.2 k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 ∧
      Integrable (fun path ↦ ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment P run law k +
          (1 / (n.1 : ℝ)) *
            (omega * (rootMeanSquare Llocal) ^ 2 +
              (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run law k := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let noiseLaw := heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (primalStep A.stepSize (run k path), (run k path).x)
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    ((path.2 k).2.1.2, (path.2 k).2.2)
  let kernel := fun w : Point d × Point d ↦
      fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 q.1 i w.1 w.2)
              (q.2 i) -
            localGradientDifference P i w.1 w.2)
  let direction := fun w : Point d × Point d ↦
    w.2 - w.1 - (A.stepSize : ℝ) • globalGradient P w.2
  let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw heterogeneousOnlineDifferenceCompressionLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hindep : ProbabilityTheory.IndepFun query noise law := by
    simpa [query, noise, run, law] using
      heterogeneousOnlineQuery_indep_differenceCompression_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    simpa [noise, law, noiseLaw] using
      heterogeneousOnlinePathLaw_differenceCompression_marginal
        (b := b) (b0 := b0) A k
  have hkernel : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        kernel p.1 p.2)
      ((Measure.map query law).prod noiseLaw) := by
    simpa [kernel, noiseLaw, P] using
      heterogeneousOnlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity (Measure.map query law)
          (fun w : Point d × Point d ↦ w.1)
          (fun w : Point d × Point d ↦ w.2)
          measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
  have hdirection : StronglyMeasurable direction := by
    dsimp [direction]
    exact ((measurable_snd.sub measurable_fst).sub
      (((measurable_gradient (globalObjective P)).comp measurable_snd)
        |>.const_smul (A.stepSize : ℝ))).stronglyMeasurable
  have hscalar : AEStronglyMeasurable
      (fun p : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        ⟪direction p.1, kernel p.1 p.2⟫_ℝ)
      ((Measure.map query law).prod noiseLaw) :=
    hdirection.aestronglyMeasurable.comp_fst.inner hkernel
  have hinnovationEq : ∀ path,
      kernel (query path) (noise path) = innovation path := by
    intro path
    dsimp [kernel, query, noise, innovation, run, P]
    rfl
  have hdirectionEq : ∀ path,
      direction (query path) = (A.stepSize : ℝ) • residual path := by
    intro path
    dsimp [direction, query, residual, run]
    rw [primalStep_eq]
    module
  have hcentered :=
    heterogeneousOnlineExecutable_nonrefresh_innovation_integrable_and_centered_of_genuine_assumption32AE_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal sigma omega hSmooth hLiteral
        hAssumption32 hRegularity hQuantizer k hStep
  have hinnovationInt : Integrable innovation law := by
    simpa [innovation, P, run, law] using hcentered.1
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hinnovationInt.aestronglyMeasurable
  have hinnovationSq :=
    heterogeneousOnlineExecutable_nonrefresh_innovation_second_moment_of_genuine_assumption32AE_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal sigma omega hSmooth hLiteral
        hAssumption32 hRegularity hQuantizer k hStep
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable hstate).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hstate))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hinnovationSqInt : Integrable
      (fun path ↦ ‖innovation path‖ ^ 2) law := by
    simpa [innovation, P, run, law] using hinnovationSq.1
  have hinnerInt : Integrable
      (fun path ↦ ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq hinnovationSqInt
  have hscalarCompInt : Integrable
      (fun path ↦ ⟪direction (query path), kernel (query path) (noise path)⟫_ℝ)
      law := by
    have hs := hinnerInt.const_mul (A.stepSize : ℝ)
    apply hs.congr
    filter_upwards [] with path
    rw [hdirectionEq path, hinnovationEq path]
    rw [real_inner_smul_left]
  have hfixed : ∀ᵐ path ∂law,
      (∫ q, ⟪direction (query path), kernel (query path) q⟫_ℝ
        ∂noiseLaw) = 0 := by
    have hm :=
      heterogeneousOnlineExecutable_fixed_nonrefresh_average_moment_ae_of_genuine_assumption32_and_lawRegularity
        (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth
          hAssumption32 hRegularity hQuantizer k
    filter_upwards [hm] with path hp
    have hxNext : (run (k + 1) path).x =
        primalStep A.stepSize (run k path) := rfl
    dsimp only at hp
    rw [hxNext] at hp
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction (query path))) hp.1
    calc
      (∫ q, ⟪direction (query path), kernel (query path) q⟫_ℝ
          ∂noiseLaw) =
          (innerSL ℝ) (direction (query path))
            (∫ q, kernel (query path) q ∂noiseLaw) := hlin
      _ = 0 := by
        rw [show (∫ q, kernel (query path) q ∂noiseLaw) = 0 by
          simpa [kernel, query, noiseLaw, run, P] using hp.2.1]
        simp
  have hscaledCross :
      (∫ path,
        ⟪direction (query path), kernel (query path) (noise path)⟫_ℝ
        ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      (fun w q ↦ ⟪direction w, kernel w q⟫_ℝ) query noise hscalar
        hquery hnoise.aemeasurable hindep hnoiseLaw hscalarCompInt hfixed
  have hcross :
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    have hmul : (A.stepSize : ℝ) *
        (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
      rw [← integral_const_mul]
      calc
        (∫ path, (A.stepSize : ℝ) *
            ⟪residual path, innovation path⟫_ℝ ∂law) =
            ∫ path,
              ⟪direction (query path), kernel (query path) (noise path)⟫_ℝ
              ∂law := by
                apply integral_congr_ae
                filter_upwards [] with path
                rw [hdirectionEq path, hinnovationEq path]
                rw [real_inner_smul_left]
        _ = 0 := hscaledCross
    exact (mul_eq_zero.mp hmul).resolve_left
      (ne_of_gt A.stepSize.property)
  have hnonrefreshInt : Integrable
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresidualMeas hinnovationMeas
      hresidualSq hinnovationSqInt
  have hnonrefreshEq :
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          ∫ path, ‖innovation path‖ ^ 2 ∂law := by
    let pair : Bool → (HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) → Point d :=
      fun z ↦ if z then innovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      law (Finset.univ : Finset Bool) pair
      (fun z _ ↦ by cases z <;> simp [pair, hresidualMeas, hinnovationMeas])
      (fun z _ ↦ by cases z <;> simp [pair, hresidualSq, hinnovationSqInt])
      (fun z _ w _ hzw ↦ by
        cases z <;> cases w
        · exact False.elim (hzw rfl)
        · simpa [pair] using hcross
        · simpa [pair, real_inner_comm] using hcross
        · exact False.elim (hzw rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  refine ⟨hcross, hnonrefreshInt, ?_⟩
  rw [hnonrefreshEq]
  change estimatorErrorMoment P run law k +
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
    estimatorErrorMoment P run law k + C * stepMoment run law k
  exact add_le_add_right (by
    simpa [innovation, P, run, law, C] using hinnovationSq.2) _

set_option maxHeartbeats 2000000 in
/-- Any scalar observable built a.e.-measurably from the generated
heterogeneous query and the non-coin coordinates of the current round is
independent of that round's refresh coin.  Measurable representatives are
used only internally; the conclusion is about the original observable. -/
theorem heterogeneousOnline_query_rest_kernel_indep_refresh_of_ae_kernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (hstate : AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A))
    (F : (Point d × Point d) ×
      ((HeterogeneousOnlineBatch n Sample b ×
        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) → ℝ)
    (hF : AEStronglyMeasurable F
      ((Measure.map
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
          (primalStep A.stepSize
              (heterogeneousOnlineProcess A x0 k path),
            (heterogeneousOnlineProcess A x0 k path).x))
        (heterogeneousOnlinePathLaw A)).prod
          (((heterogeneousOnlineBatchLaw A.problem b).prod
            (heterogeneousOnlineBatchLaw A.problem b0)).prod
              (workerCompressionLaw (n := n) A.quantizer)))) :
    ProbabilityTheory.IndepFun
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        F ((primalStep A.stepSize
              (heterogeneousOnlineProcess A x0 k path),
            (heterogeneousOnlineProcess A x0 k path).x), (path.2 k).2))
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        (path.2 k).1)
      (heterogeneousOnlinePathLaw A) := by
  classical
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (primalStep A.stepSize (run k path), (run k path).x)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let rest := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.2
  let coin := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.1
  let restPath := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    rest (current path)
  let branch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    coin (current path)
  let restLaw := ((heterogeneousOnlineBatchLaw A.problem b).prod
    (heterogeneousOnlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hqueryStrong : AEStronglyMeasurable query law :=
    (((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)).aestronglyMeasurable
  let query' := hqueryStrong.mk query
  have hquery' : Measurable query' := hqueryStrong.measurable_mk
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hrestPath : Measurable restPath := by dsimp [restPath, rest]; fun_prop
  have hbranch : Measurable branch := by dsimp [branch, coin]; fun_prop
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    simpa [query, current, run, law] using
      heterogeneousOnlineQuery_indep_current_round_of_measurable
        (b := b) (b0 := b0) A x0 k hstate
  have hqueryCurrent' : ProbabilityTheory.IndepFun query' current law := by
    apply hqueryCurrent.congr hqueryStrong.ae_eq_mk
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (Measure.map Prod.snd law) := by
              rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
              rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (SOptLib.iidStreamLaw roundLaw) := by
              rw [show Measure.map Prod.snd law =
                  SOptLib.iidStreamLaw roundLaw by
                dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hqueryPair : ProbabilityTheory.IndepFun query'
      (fun path ↦ (restPath path, branch path)) law := by
    simpa [restPath, branch, rest, coin, current] using
      hqueryCurrent'.comp measurable_id (measurable_snd.prodMk measurable_fst)
  have hpairLaw : Measure.map (fun path ↦ (restPath path, branch path)) law =
      restLaw.prod coinLaw := by
    calc
      Measure.map (fun path ↦ (restPath path, branch path)) law =
          Measure.map Prod.swap (Measure.map current law) := by
            rw [Measure.map_map measurable_swap hcurrent]
            rfl
      _ = Measure.map Prod.swap roundLaw := by rw [hcurrentLaw]
      _ = Measure.map Prod.swap (coinLaw.prod restLaw) := by rfl
      _ = restLaw.prod coinLaw := MeasureTheory.Measure.prod_swap
  have hqueryRestBranch : ProbabilityTheory.IndepFun
      (fun path ↦ (query' path, restPath path)) branch law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law restLaw coinLaw
      query' restPath branch hquery' hrestPath hbranch hqueryPair hpairLaw
  have hqueryRest : ProbabilityTheory.IndepFun query' restPath law := by
    simpa only [Function.comp_apply] using
      hqueryPair.comp measurable_id measurable_fst
  have hrestLaw : Measure.map restPath law = restLaw := by
    calc
      Measure.map restPath law = Measure.map rest (Measure.map current law) := by
        rw [Measure.map_map]
        · rfl
        · exact measurable_snd
        · exact hcurrent
      _ = Measure.map rest roundLaw := by rw [hcurrentLaw]
      _ = restLaw := by
        dsimp [rest, roundLaw]
        unfold heterogeneousOnlineRoundLaw
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hqueryMap : Measure.map query' law = Measure.map query law :=
    Measure.map_congr hqueryStrong.ae_eq_mk.symm
  have hF' : AEStronglyMeasurable F
      ((Measure.map query' law).prod restLaw) := by
    rw [hqueryMap]
    simpa [query, run, law, restLaw] using hF
  let F' := hF'.mk F
  have hF'meas : Measurable F' := hF'.measurable_mk
  let joined := fun path ↦ (query' path, restPath path)
  have hjoined : Measurable joined := hquery'.prodMk hrestPath
  have hjoinedLaw : Measure.map joined law =
      (Measure.map query' law).prod restLaw := by
    calc
      Measure.map joined law =
          (Measure.map query' law).prod (Measure.map restPath law) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hquery'.aemeasurable hrestPath.aemeasurable).1 hqueryRest
      _ = (Measure.map query' law).prod restLaw := by rw [hrestLaw]
  have hjoinedQmp : Measure.QuasiMeasurePreserving joined law
      ((Measure.map query' law).prod restLaw) :=
    ⟨hjoined, by rw [hjoinedLaw]⟩
  have hFcomp :
      (fun path ↦ F (query path, restPath path)) =ᵐ[law]
        (fun path ↦ F' (joined path)) := by
    have hmk := hjoinedQmp.tendsto_ae hF'.ae_eq_mk
    filter_upwards [hqueryStrong.ae_eq_mk, hmk] with path hq hm
    rw [hq, hm]
  have hindep : ProbabilityTheory.IndepFun
      (fun path ↦ F' (joined path)) branch law := by
    simpa only [joined, Function.comp_apply] using
      hqueryRestBranch.comp hF'meas measurable_id
  apply hindep.congr hFcomp.symm (Filter.Eventually.of_forall fun _ ↦ rfl)

set_option maxHeartbeats 3000000 in
/-- The actual heterogeneous refresh-error square is independent of the
same-round Bernoulli coin.  This is a consequence of the canonical round
product law and the weak law-scoped sample-gradient regularity supplier. -/
theorem
    heterogeneousOnlineExecutable_refresh_error_sq_indep_refresh_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    ProbabilityTheory.IndepFun refreshErrorSq
      (fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
          (path.2 k).1) law := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (primalStep A.stepSize (run k path), (run k path).x)
  let queryLaw := Measure.map query law
  let refreshBatchLaw := heterogeneousOnlineBatchLaw A.problem b
  let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let F : (Point d × Point d) ×
      ((HeterogeneousOnlineBatch n Sample b ×
        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) → ℝ :=
    fun z ↦ ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
        stochasticGradient A.problem i (z.2.1.1 i j) z.1.1)) -
      globalGradient P z.1.1‖ ^ 2
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure refreshBatchLaw := by
    dsimp [refreshBatchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    dsimp [differenceBatchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    dsimp [compressionLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)
  haveI : IsProbabilityMeasure queryLaw :=
    Measure.isProbabilityMeasure_map hquery
  have hbase : AEStronglyMeasurable
      (fun z : (Point d × Point d) × HeterogeneousOnlineBatch n Sample b ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i (z.2 i j) z.1.1)) -
          globalGradient P z.1.1‖ ^ 2)
      (queryLaw.prod refreshBatchLaw) := by
    let pull := fun z : (Point d × Point d) ×
        HeterogeneousOnlineBatch n Sample b ↦ (z.1.1, z.2)
    have hpull : Measurable pull := by dsimp [pull]; fun_prop
    have hpullLaw : Measure.map pull (queryLaw.prod refreshBatchLaw) =
        (Measure.map Prod.fst queryLaw).prod refreshBatchLaw := by
      simpa [pull, refreshBatchLaw] using
        (MeasureTheory.Measure.map_prod_map queryLaw refreshBatchLaw
          measurable_fst measurable_id).symm
    have hraw :=
      heterogeneousOnlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
        (b := b) A.problem hRegularity (Measure.map Prod.fst queryLaw)
    have hqmp : Measure.QuasiMeasurePreserving pull
        (queryLaw.prod refreshBatchLaw)
        ((Measure.map Prod.fst queryLaw).prod refreshBatchLaw) :=
      ⟨hpull, by rw [hpullLaw]⟩
    simpa [pull, P] using hraw.comp_quasiMeasurePreserving hqmp
  have hF : AEStronglyMeasurable F (queryLaw.prod restLaw) := by
    let pull := fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
      (z.1, z.2.1.1)
    have hpull : Measurable pull := by dsimp [pull]; fun_prop
    have hproject : Measure.map
        (fun r : ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
          r.1.1) restLaw = refreshBatchLaw := by
      calc
        Measure.map (fun r : ((HeterogeneousOnlineBatch n Sample b ×
            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
            r.1.1) restLaw =
            Measure.map Prod.fst (Measure.map Prod.fst restLaw) := by
              change Measure.map (Prod.fst ∘ Prod.fst) restLaw = _
              rw [← Measure.map_map measurable_fst measurable_fst]
        _ = Measure.map Prod.fst
            (refreshBatchLaw.prod differenceBatchLaw) := by
              rw [show Measure.map Prod.fst restLaw =
                  refreshBatchLaw.prod differenceBatchLaw by
                dsimp [restLaw]
                rw [Measure.map_fst_prod, measure_univ, one_smul]]
        _ = refreshBatchLaw := by
              rw [Measure.map_fst_prod, measure_univ, one_smul]
    have hpullLaw : Measure.map pull (queryLaw.prod restLaw) =
        queryLaw.prod refreshBatchLaw := by
      have hm := MeasureTheory.Measure.map_prod_map queryLaw restLaw
        measurable_id
        (show Measurable
          (fun r : ((HeterogeneousOnlineBatch n Sample b ×
            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
              r.1.1) by fun_prop)
      rw [Measure.map_id, hproject] at hm
      simpa [pull] using hm.symm
    have hqmp : Measure.QuasiMeasurePreserving pull
        (queryLaw.prod restLaw) (queryLaw.prod refreshBatchLaw) :=
      ⟨hpull, by rw [hpullLaw]⟩
    simpa [F, pull] using hbase.comp_quasiMeasurePreserving hqmp
  have hindep :=
    heterogeneousOnline_query_rest_kernel_indep_refresh_of_ae_kernel
      (b := b) (b0 := b0) A x0 k hstate F (by
        simpa [query, queryLaw, law, restLaw, refreshBatchLaw,
          differenceBatchLaw, compressionLaw] using hF)
  simpa [F, P, run, law, heterogeneousOnlineProcess,
    SOptLib.recursive_process_from_random_initial,
    heterogeneousOnlineStep] using hindep

set_option maxHeartbeats 3000000 in
/-- The complete heterogeneous nonrefresh residual square is independent of
the same-round refresh coin.  Positivity of the stepsize reconstructs the
carried estimator from the generated query pair, so no state or cost
measurability premise is added. -/
theorem
    heterogeneousOnlineExecutable_nonrefresh_error_sq_indep_refresh_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      (run k path).g - globalGradient P (run k path).x
    let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0
              (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
            ((path.2 k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2)
      (fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
          (path.2 k).1) law := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (primalStep A.stepSize (run k path), (run k path).x)
  let queryLaw := Measure.map query law
  let refreshBatchLaw := heterogeneousOnlineBatchLaw A.problem b
  let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let noiseLaw := differenceBatchLaw.prod compressionLaw
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let recoveredResidual := fun w : Point d × Point d ↦
    (A.stepSize : ℝ)⁻¹ • (w.2 - w.1) - globalGradient P w.2
  let innovationKernel := fun
      (w : Point d × Point d)
      (q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0 q.1 i w.1 w.2)
          (q.2 i) -
        localGradientDifference P i w.1 w.2)
  let F : (Point d × Point d) ×
      ((HeterogeneousOnlineBatch n Sample b ×
        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) → ℝ :=
    fun z ↦ ‖recoveredResidual z.1 +
      innovationKernel z.1 (z.2.1.2, z.2.2)‖ ^ 2
  let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure refreshBatchLaw := by
    dsimp [refreshBatchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    dsimp [differenceBatchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    dsimp [compressionLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    dsimp [noiseLaw]
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hquery : AEMeasurable query law := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)
  haveI : IsProbabilityMeasure queryLaw :=
    Measure.isProbabilityMeasure_map hquery
  have hinnovation : AEStronglyMeasurable
      (fun z : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        innovationKernel z.1 z.2) (queryLaw.prod noiseLaw) := by
    simpa [innovationKernel, noiseLaw, differenceBatchLaw, compressionLaw, P]
      using
        heterogeneousOnlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
          (b0 := b0) A hRegularity queryLaw
            (fun w : Point d × Point d ↦ w.1)
            (fun w : Point d × Point d ↦ w.2)
            measurable_fst.aestronglyMeasurable
            measurable_snd.aestronglyMeasurable
  have hrecovered : StronglyMeasurable recoveredResidual := by
    dsimp [recoveredResidual]
    exact (((measurable_snd.sub measurable_fst).const_smul
      ((A.stepSize : ℝ)⁻¹)).sub
        ((measurable_gradient (globalObjective P)).comp measurable_snd))
          |>.stronglyMeasurable
  have hbase : AEStronglyMeasurable
      (fun z : (Point d × Point d) ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
        ‖recoveredResidual z.1 + innovationKernel z.1 z.2‖ ^ 2)
      (queryLaw.prod noiseLaw) :=
    (hrecovered.aestronglyMeasurable.comp_fst.add hinnovation).norm.pow 2
  have hF : AEStronglyMeasurable F (queryLaw.prod restLaw) := by
    let pull := fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
      (z.1, (z.2.1.2, z.2.2))
    have hpull : Measurable pull := by dsimp [pull]; fun_prop
    have hproject : Measure.map
        (fun r : ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
          (r.1.2, r.2)) restLaw = noiseLaw := by
      have hm := MeasureTheory.Measure.map_prod_map
        (refreshBatchLaw.prod differenceBatchLaw) compressionLaw
          measurable_snd measurable_id
      rw [Measure.map_snd_prod, measure_univ, one_smul] at hm
      simpa [restLaw, noiseLaw] using hm.symm
    have hpullLaw : Measure.map pull (queryLaw.prod restLaw) =
        queryLaw.prod noiseLaw := by
      have hm := MeasureTheory.Measure.map_prod_map queryLaw restLaw
        measurable_id
        (show Measurable
          (fun r : ((HeterogeneousOnlineBatch n Sample b ×
            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
              (r.1.2, r.2)) by fun_prop)
      rw [Measure.map_id, hproject] at hm
      simpa [pull] using hm.symm
    have hqmp : Measure.QuasiMeasurePreserving pull
        (queryLaw.prod restLaw) (queryLaw.prod noiseLaw) :=
      ⟨hpull, by rw [hpullLaw]⟩
    simpa [F, pull] using hbase.comp_quasiMeasurePreserving hqmp
  have hindep :=
    heterogeneousOnline_query_rest_kernel_indep_refresh_of_ae_kernel
      (b := b) (b0 := b0) A x0 k hstate F (by
        simpa [query, queryLaw, law, restLaw, refreshBatchLaw,
          differenceBatchLaw, compressionLaw] using hF)
  have hcalc : ∀ path, F (query path, (path.2 k).2) =
      ‖residual path + innovation path‖ ^ 2 := by
    intro path
    have hstep : (A.stepSize : ℝ) ≠ 0 := ne_of_gt A.stepSize.property
    have hx : (run (k + 1) path).x = primalStep A.stepSize (run k path) := rfl
    have hr : recoveredResidual (query path) = residual path := by
      dsimp [recoveredResidual, query, residual]
      rw [primalStep_eq, sub_sub_cancel, smul_smul,
        inv_mul_cancel₀ hstep, one_smul]
    dsimp [F]
    rw [hr]
    congr 2
  apply hindep.congr (Filter.Eventually.of_forall hcalc)
    (Filter.Eventually.of_forall fun _ ↦ rfl)

set_option maxHeartbeats 3000000 in
/-- Executable heterogeneous Eq. (46) at one time.  The refresh and
nonrefresh moment packages are assembled through the actual Bernoulli coin
of `heterogeneousOnlineStep`; all moments use the same worker-dependent
batches, generated process, and canonical path law. -/
theorem
    heterogeneous_online_estimator_recurrence_46_executable_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal sigma : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law (k + 1) ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment P run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) *
              heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
      A.refreshProbability * heterogeneousOnlineVarianceTerm sigma b := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  have hRefresh :=
    heterogeneousOnlineExecutable_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
      (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity hSmooth.1 k
  have hRefreshIndep :=
    heterogeneousOnlineExecutable_refresh_error_sq_indep_refresh_of_lawRegularity
      (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  have hNonrefresh :=
    heterogeneousOnlineExecutable_nonrefresh_branch_moments_of_genuine_assumption32AE_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal sigma omega hSmooth hLiteral
        hAssumption32 hRegularity hQuantizer k hError hStep
  have hNonrefreshIndep :=
    heterogeneousOnlineExecutable_nonrefresh_error_sq_indep_refresh_of_lawRegularity
      (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity k
  let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let refreshError := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
      stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.2 k).1
  let refreshSq := fun path ↦ ‖refreshError path‖ ^ 2
  let nonrefreshSq := fun path ↦ ‖residual path + innovation path‖ ^ 2
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n ↦
      A.quantizer.apply
        (heterogeneousOnlineBatchDifference A.problem b0
          (path.2 k).2.1.2 i xN s.x)
        ((path.2 k).2.2 i)
    have hdiffAvg : average (fun i : Worker n ↦
        localGradientDifference P i xN s.x) =
        globalGradient P xN - globalGradient P s.x := by
      rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
        globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : innovation path =
        average q - average (fun i : Worker n ↦
          localGradientDifference P i xN s.x) := by
      dsimp [innovation, q, xN, s]
      rw [show (run (k + 1) path).x = xN by rfl]
      unfold average SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n ↦
          if (path.2 k).1 then average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i ((path.2 k).2.1.1 i j) xN)
          else s.g + q i) - globalGradient P xN := by rfl
    cases h : branch path with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [branch] at h
        rw [h]
        simp only [Bool.false_eq_true, if_false]
        change average (fun i : Worker n ↦ s.g + q i) -
            globalGradient P xN = residual path + innovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [if_true]
        rw [hnext]
        simp only [branch] at h
        rw [h]
        rfl
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hbranchMeas : Measurable branch := by dsimp [branch]; fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    let evalCoin := fun stream : ℕ →
        HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ (stream k).1
    calc
      Measure.map branch law = Measure.map evalCoin (Measure.map Prod.snd law) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · dsimp [evalCoin]; fun_prop
        · exact measurable_snd
      _ = Measure.map evalCoin
          (SOptLib.iidStreamLaw
            (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)) := by
        rw [show Measure.map Prod.snd law =
            SOptLib.iidStreamLaw
              (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) by
          dsimp [law, heterogeneousOnlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = Measure.map Prod.fst
          (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
        rw [show Measure.map evalCoin
            (SOptLib.iidStreamLaw
              (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)) =
              Measure.map Prod.fst
                (Measure.map (fun stream : ℕ →
                    HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ stream k)
                  (SOptLib.iidStreamLaw
                    (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A))) by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · exact measurable_fst
          · exact measurable_pi_apply k]
        rw [SOptLib.iidStreamLaw_map_eval]
      _ = _ := by simp [heterogeneousOnlineRoundLaw]
  have htrueMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({true} : Set Bool) = A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
    simp [PMF.bernoulli_apply]
  have hfalseMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({false} : Set Bool) = 1 - A.refreshProbability := by
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
  let phiR : ℝ → Bool → ℝ := fun z c ↦ if c then z else 0
  let budgetR : ℝ → ℝ := fun z ↦ A.refreshProbability * z
  let phiN : ℝ → Bool → ℝ := fun z c ↦ if c = false then z else 0
  let budgetN : ℝ → ℝ := fun z ↦ (1 - A.refreshProbability) * z
  have hrefreshInt : Integrable refreshSq law := by
    simpa [refreshSq, refreshError, P, run, law] using hRefresh.1
  have hnonrefreshInt : Integrable nonrefreshSq law := by
    simpa [nonrefreshSq, residual, innovation, P, run, law] using
      hNonrefresh.2.1
  have hrefreshIndep : ProbabilityTheory.IndepFun refreshSq branch law := by
    simpa [refreshSq, refreshError, branch, P, run, law] using hRefreshIndep
  have hnonrefreshIndep : ProbabilityTheory.IndepFun nonrefreshSq branch law := by
    simpa [nonrefreshSq, residual, innovation, branch, P, run, law] using
      hNonrefreshIndep
  have hgateRInt : Integrable
      (fun path ↦ phiR (refreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = true} :=
      hbranchMeas (measurableSet_singleton true)
    have hp := Integrable.piecewise hs hrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiR, Set.piecewise] using hp
  have hgateNInt : Integrable
      (fun path ↦ phiN (nonrefreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranchMeas (measurableSet_singleton false)
    have hp := Integrable.piecewise hs hnonrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiN, Set.piecewise] using hp
  have hbudgetRInt : Integrable (fun path ↦ budgetR (refreshSq path)) law := by
    simpa [budgetR] using hrefreshInt.const_mul A.refreshProbability
  have hbudgetNInt : Integrable (fun path ↦ budgetN (nonrefreshSq path)) law := by
    simpa [budgetN] using hnonrefreshInt.const_mul (1 - A.refreshProbability)
  have hgateR :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := refreshSq) (Y := branch) (φ := phiR) (B := budgetR)
      (by exact (show Measurable (Function.uncurry phiR) by
        dsimp [phiR, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton true)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budgetR by dsimp [budgetR]; fun_prop)
        |>.aestronglyMeasurable)
      hrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hrefreshIndep hbranchLaw hgateRInt hbudgetRInt
      (fun z ↦ by
        rw [MeasureTheory.integral_fintype]
        · simp [phiR, budgetR, htrueMass]
        · exact Integrable.of_finite)
  have hgateN :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := nonrefreshSq) (Y := branch) (φ := phiN) (B := budgetN)
      (by exact (show Measurable (Function.uncurry phiN) by
        dsimp [phiN, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton false)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budgetN by dsimp [budgetN]; fun_prop)
        |>.aestronglyMeasurable)
      hnonrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hnonrefreshIndep hbranchLaw hgateNInt hbudgetNInt
      (fun z ↦ by
        rw [MeasureTheory.integral_fintype]
        · simp [phiN, budgetN, hfalseMass]
        · exact Integrable.of_finite)
  have hnextSq : ∀ path, ‖nextResidual path‖ ^ 2 =
      phiR (refreshSq path) (branch path) +
        phiN (nonrefreshSq path) (branch path) := by
    intro path
    rw [hdecomp]
    cases hb : branch path <;>
      simp [phiR, phiN, refreshSq, nonrefreshSq]
  have hnextInt : Integrable (fun path ↦ ‖nextResidual path‖ ^ 2) law :=
    (hgateRInt.add hgateNInt).congr
      (Filter.Eventually.of_forall fun path ↦ (hnextSq path).symm)
  have hnextEq : estimatorErrorMoment P run law (k + 1) =
      (∫ path, phiR (refreshSq path) (branch path) ∂law) +
        ∫ path, phiN (nonrefreshSq path) (branch path) ∂law := by
    unfold estimatorErrorMoment
    calc
      (∫ path,
          ‖(run (k + 1) path).g - globalGradient P (run (k + 1) path).x‖ ^ 2
          ∂law) = ∫ path,
            (phiR (refreshSq path) (branch path) +
              phiN (nonrefreshSq path) (branch path)) ∂law := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hnextSq
      _ = _ := integral_add hgateRInt hgateNInt
  refine ⟨?_, hError, hStep, ?_⟩
  · simpa [EstimatorErrorMomentWellDefined, nextResidual, P, run, law] using
      hnextInt
  · rw [hnextEq]
    calc
      (∫ path, phiR (refreshSq path) (branch path) ∂law) +
            ∫ path, phiN (nonrefreshSq path) (branch path) ∂law ≤
          (∫ path, budgetR (refreshSq path) ∂law) +
            ∫ path, budgetN (nonrefreshSq path) ∂law :=
        add_le_add hgateR hgateN
      _ = A.refreshProbability * (∫ path, refreshSq path ∂law) +
          (1 - A.refreshProbability) *
            (∫ path, nonrefreshSq path ∂law) := by
            simp [budgetR, budgetN, integral_const_mul]
      _ ≤ A.refreshProbability * heterogeneousOnlineVarianceTerm sigma b +
          (1 - A.refreshProbability) *
            (estimatorErrorMoment P run law k +
              (1 / (n.1 : ℝ)) *
                (omega * (rootMeanSquare Llocal) ^ 2 +
                  (1 + omega) *
                    heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
                stepMoment run law k) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
          · simpa [refreshSq, refreshError, P, run, law] using hRefresh.2
          · exact le_of_lt A.refresh_admissible.1
        · apply mul_le_mul_of_nonneg_left
          · simpa [nonrefreshSq, residual, innovation, P, run, law] using
              hNonrefresh.2.2
          · exact sub_nonneg.mpr A.refresh_admissible.2
      _ = (1 - A.refreshProbability) / n.1 *
            (omega * (rootMeanSquare Llocal) ^ 2 +
              (1 + omega) *
                heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run law k +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
          A.refreshProbability * heterogeneousOnlineVarianceTerm sigma b := by
        ring

set_option maxHeartbeats 3000000 in
/-- Simultaneous executable heterogeneous component `L²` closure and Eq. (46)
history.  The base case is the actual worker-dependent sampled initializer,
and every successor uses the same heterogeneous process and canonical path
law as the recurrence. -/
theorem
    heterogeneousOnlineProcess_scalar_recurrence_components_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path ↦ (run k path).x) law ∧
    AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law ∧
    Integrable (fun path ↦ ‖(run k path).x - x0‖ ^ 2) law ∧
    Integrable (fun path ↦ ‖(run k path).g‖ ^ 2) law ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    ∀ j, j < k →
      estimatorErrorMoment P run law (j + 1) ≤
        (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hState (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 σ hLiteral hRegularity t
  have hGlobal : IsGradientLipschitz (globalObjective P)
      (rootMeanSquare Llocal) :=
    GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hAll : ∀ t,
      AEStronglyMeasurable (fun path ↦ (run t path).x) law ∧
      AEStronglyMeasurable
        (fun path ↦ (run t path).g - globalGradient P (run t path).x) law ∧
      Integrable (fun path ↦ ‖(run t path).x - x0‖ ^ 2) law ∧
      Integrable (fun path ↦ ‖(run t path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law t ∧
      StepMomentWellDefined run law t ∧
      ∀ j, j < t →
        estimatorErrorMoment P run law (j + 1) ≤
          (1 - A.refreshProbability) / n.1 *
              (ω * (rootMeanSquare Llocal) ^ 2 +
                (1 + ω) *
                  heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
              stepMoment run law j +
            (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
            A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
    intro t
    induction t with
    | zero =>
        have h0 :=
          heterogeneousOnlineProcess_scalar_recurrence_components_zero_of_literal
            (b := b) (b0 := b0) A x0 Llocal σ hSmooth hLiteral
        refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1,
          h0.2.2.2.2.1, h0.2.2.2.2.2, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        have hRec :=
          heterogeneous_online_estimator_recurrence_46_executable_of_literal_and_lawRegularity
            (b := b) (b0 := b0) A x0 Llocal ℒlocal σ ω hSmooth hLiteral
              hQuantizer hAssumption32 hRegularity t ih.2.2.2.2.1
                ih.2.2.2.2.2.1
        have hxNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).x) law :=
          ((measurable_state_x d).comp_aemeasurable
            (hState (t + 1))).aestronglyMeasurable
        have hgNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).g) law :=
          ((measurable_state_g d).comp_aemeasurable
            (hState (t + 1))).aestronglyMeasurable
        have hgradNext : AEStronglyMeasurable
            (fun path ↦ globalGradient P (run (t + 1) path).x) law :=
          ((measurable_gradient (globalObjective P)).comp_aemeasurable
            hxNext.aemeasurable).aestronglyMeasurable
        have hrNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).g -
              globalGradient P (run (t + 1) path).x) law :=
          hgNext.sub hgradNext
        have hxl2Next : Integrable
            (fun path ↦ ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
          have hg : AEStronglyMeasurable (fun path ↦ (run t path).g) law := by
            have hsum := ih.2.1.add
              (((measurable_gradient (globalObjective P)).comp_aemeasurable
                ih.1.aemeasurable).aestronglyMeasurable)
            refine hsum.congr (Filter.Eventually.of_forall ?_)
            intro path
            change ((run t path).g - globalGradient P (run t path).x) +
              globalGradient P (run t path).x = (run t path).g
            abel
          have h := integrable_sq_norm_sub_smul_sub_const_of_l2
            (fun path ↦ (run t path).x) (fun path ↦ (run t path).g)
            x0 (A.stepSize : ℝ) ih.1 hg ih.2.2.1 ih.2.2.2.1
          simpa [run, heterogeneousOnlineProcess,
            SOptLib.recursive_process_from_random_initial,
            heterogeneousOnlineStep, primalStep_eq] using h
        have hglobalNext : Integrable
            (fun path ↦ ‖globalGradient P (run (t + 1) path).x‖ ^ 2) law := by
          apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
            x0 (globalGradient P) (rootMeanSquare Llocal)
              (fun path ↦ (run (t + 1) path).x) hxNext
          · simpa [norm_sub_rev] using hxl2Next
          · intro x y
            exact hGlobal.2 y x
        have hgl2Next : Integrable
            (fun path ↦ ‖(run (t + 1) path).g‖ ^ 2) law := by
          have hadd := integrable_sq_norm_add hrNext hgradNext
            (by simpa [EstimatorErrorMomentWellDefined, P, run, law] using hRec.1)
            hglobalNext
          apply hadd.congr
          filter_upwards [] with path
          congr 2
          abel
        have hsNext : StepMomentWellDefined run law (t + 1) := by
          have hscaled := integrable_sq_norm_const_smul
            (-(A.stepSize : ℝ)) hgl2Next
          simpa [StepMomentWellDefined, run, heterogeneousOnlineProcess,
            SOptLib.recursive_process_from_random_initial,
            heterogeneousOnlineStep, primalStep_eq] using hscaled
        have hHistory : ∀ j, j < t + 1 →
            estimatorErrorMoment P run law (j + 1) ≤
              (1 - A.refreshProbability) / n.1 *
                  (ω * (rootMeanSquare Llocal) ^ 2 +
                    (1 + ω) *
                      heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
                  stepMoment run law j +
                (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
                A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjt | rfl
          · exact ih.2.2.2.2.2.2 j hjt
          · exact hRec.2.2.2
        exact ⟨hxNext, hrNext, hxl2Next, hgl2Next, hRec.1, hsNext,
          hHistory⟩
  exact hAll k


set_option maxHeartbeats 3000000 in
/-- Homogeneous executable component `L²` closure and Eq. (46) history under
the source-faithful law-a.e. Assumption 3.2 contract.  This is the constant
worker-batch specialization of the heterogeneous executable induction, so the
process, path law, sampled initializer, and every scalar moment are the same
objects as in `onlineProcess`/`onlinePathLaw`; no null-path genuine-gradient
witness is reconstructed. -/
theorem
    onlineProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path ↦ (run k path).x) law ∧
    AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law ∧
    Integrable (fun path ↦ ‖(run k path).x - x0‖ ^ 2) law ∧
    Integrable (fun path ↦ ‖(run k path).g‖ ^ 2) law ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    ∀ j, j < k →
      estimatorErrorMoment P run law (j + 1) ≤
        (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  let bConst := fun _ : Worker n ↦ b
  let b0Const := fun _ : Worker n ↦ b0
  have hAssumption32Het :
      HeterogeneousOnlineAssumption32GenuineAE (b0 := b0Const) A.problem
        (heterogeneousOnlineProcess (b := bConst) (b0 := b0Const) A x0)
        (heterogeneousOnlinePathLaw (b := bConst) (b0 := b0Const) A) ℒlocal :=
    (onlineAssumption32GenuineAE_iff_heterogeneous_const
      A x0 hBatch ℒlocal).mp hAssumption32
  have hComponents :=
    heterogeneousOnlineProcess_scalar_recurrence_components_of_literal_and_lawRegularity
      (b := bConst) (b0 := b0Const) A x0 Llocal ℒlocal σ ω hSmooth
        hLiteral hQuantizer hAssumption32Het hRegularity k
  have hProcess : onlineProcess (b := b) (b0 := b0) A x0 hBatch =
      heterogeneousOnlineProcess (b := bConst) (b0 := b0Const) A x0 := by
    funext t path
    exact onlineProcess_eq_heterogeneousOnlineProcess_const
      A x0 hBatch t path
  rw [hProcess, onlinePathLaw_eq_heterogeneousOnlinePathLaw_const A]
  simp only [bConst, b0Const, heterogeneousFiniteBatchSmoothnessTerm_const,
    heterogeneousOnlineVarianceTerm_const] at hComponents
  rcases hComponents with
    ⟨hx, hr, hxl2, hgl2, hError, hStep, hHistory⟩
  refine ⟨hx, hr, hxl2, hgl2, hError, hStep, ?_⟩
  intro j hj
  have hRec := hHistory j hj
  convert hRec using 1
  all_goals ring

/-- Executable D.4 under the conditional law-a.e. Assumption 3.2 contract at
the actual generated queries.  The scalar closure is supplied by the proved
law-a.e. recurrence above; the telescope itself is the preserved executable
PL proof over `onlineProcess` and `onlinePathLaw`. -/
theorem Theorem_D4_online_VR_PL_initialization_corrected_of_literal_and_lawRegularityAE
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path ↦
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
  apply online_D4_initialization_corrected_of_scalar_recurrence
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hLiteral hPL
      hQuantizer hBatch
  · intro k
    exact
      onlineProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          hAssumption32 hRegularity k
  · exact hStep

/-- Executable PL accuracy with Assumption 3.2 stated only almost everywhere
under the same generated `onlinePathLaw` used by the terminal iterate. -/
theorem onlineExecutablePLAccuracy_of_budget_of_literal_and_lawRegularityAE
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0)
    (ε : Accuracy)
    (hBudget :
      (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability *
            (varianceAggregateSq σ / (n.1 * b.1)) +
        varianceAggregateSq σ / (n.1 * b.1 * μ) ≤ (ε : ℝ)) :
    PLAccuracy K (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) xStar ε := by
  unfold PLAccuracy
  have hBoundary :=
    Theorem_D4_online_VR_PL_initialization_corrected_of_literal_and_lawRegularityAE
      (K := K) A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hLiteral hPL hQuantizer hBatch hAssumption32 hRegularity hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedOnlineInitialEstimatorErrorSq_le_of_literal
    (b := b) A x0 σ hLiteral hSmooth.1
  have hContraction : 0 ≤ 1 - (A.stepSize : ℝ) * (μ : ℝ) := by
    apply sub_nonneg.mpr
    have hp1 := A.refresh_admissible.2
    nlinarith [hStep.2]
  have hCoefficient : 0 ≤
      (1 - (A.stepSize : ℝ) * (μ : ℝ)) ^ K.1 * A.stepSize /
        A.refreshProbability :=
    div_nonneg
      (mul_nonneg (pow_nonneg hContraction K.1) A.stepSize.property.le)
      A.refresh_admissible.1.le
  have hInitialMul := mul_le_mul_of_nonneg_left hInitial hCoefficient
  calc
    (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability * expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
        varianceAggregateSq σ / (n.1 * b.1 * μ) ≤
      (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability * (varianceAggregateSq σ / (n.1 * b.1)) +
        varianceAggregateSq σ / (n.1 * b.1 * μ) := by gcongr
    _ ≤ (ε : ℝ) := hBudget

/-- Accuracy-family form of the executable PL law-a.e. boundary. -/
theorem onlineExecutablePLAccuracy_family_of_budget_of_literal_and_lawRegularityAE
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAssumption32 : ∀ ε, OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0)
    (hBudget : ∀ ε,
      (1 - A.stepSize * μ) ^ (K ε).1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ (K ε).1 * A.stepSize /
          A.refreshProbability *
            (varianceAggregateSq σ / (n.1 * (b ε).1)) +
        varianceAggregateSq σ / (n.1 * (b ε).1 * μ) ≤ (ε : ℝ)) :
    ∀ ε, PLAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) xStar ε := by
  intro ε
  exact onlineExecutablePLAccuracy_of_budget_of_literal_and_lawRegularityAE
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hLiteral hPL
      hQuantizer (hBatch ε) (hAssumption32 ε) hRegularity hStep ε (hBudget ε)


set_option linter.unnecessarySeqFocus false in
/-- Executable heterogeneous Remark D.2 convergence boundary.  It uses the
actual worker-dependent sampled initializer, generated process, and product
path law.  The extra initial-error term is the exact stochastic-initialization
correction omitted by the proof-exact source calculation. -/
theorem Theorem_D3_heterogeneous_online_VR_nonconvex_initialization_corrected_of_literal_and_lawRegularity
    {d n K : Count} {b b0 : Worker n → Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    Integrable (fun z =>
        ‖globalGradient (onlineLocalProblem A.problem)
          (uniformOutput (K := K)
            (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) z)‖ ^ 2)
        (uniformOutputExperimentLaw (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) K) ∧
      (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) K) ≤
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
            (A.stepSize * K.1) +
          expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 /
            (A.refreshProbability * K.1) +
          heterogeneousOnlineVarianceTerm σ b := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  let V : ℝ := heterogeneousOnlineVarianceTerm σ b
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  have hComponents (k : ℕ) :=
    heterogeneousOnlineProcess_scalar_recurrence_components_of_literal_and_lawRegularity
      (b := b) (b0 := b0) A x0 Llocal ℒlocal σ ω hSmooth hLiteral
        hQuantizer hAssumption32 hRegularity k
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
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
      simpa [P, run, γ, L, heterogeneousOnlineProcess,
        SOptLib.recursive_process_from_random_initial, heterogeneousOnlineStep,
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
    exact hrec
  have hL : 0 ≤ L := by exact Real.sqrt_nonneg _
  have hS : 0 ≤ heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0 := by
    unfold heterogeneousFiniteBatchSmoothnessTerm average SOptLib.finiteUniformAverage
    positivity
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact heterogeneous_vr_stepsize_absorbs_displacement hγ A.refresh_admissible
      hQuantizer.1.le hL hS hStep
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
      E 0 = expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 := by
    simpa [E, P, run, law] using
      (heterogeneous_online_executable_initial_error_moment_eq_expected_of_literal
        (b := b) (b0 := b0) A x0 σ hLiteral hSmooth.1)
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
        HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => fStar) law :=
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
          γ / (2 * p) * expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 +
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
          expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 / (p * K.1) +
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
            γ / (2 * p) * expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 +
            (K.1 : ℝ) * (γ / 2) * V) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) +
          expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 / (p * K.1) +
          V := by
        field_simp [ne_of_gt hγ, ne_of_gt hp, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ, V] using hAverageBound

/-- The executable heterogeneous D.3 boundary yields the requested uniform-
output accuracy whenever its iteration, stochastic-initialization, and
worker-dependent variance terms fit the accuracy budget. -/
theorem heterogeneousOnlineExecutableNonconvexAccuracy_of_budget_of_literal_and_lawRegularity
    {d n K : Count} {b b0 : Worker n → Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n)
    (ε : Accuracy)
    (hBudget :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        heterogeneousOnlineVarianceTerm σ b /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm σ b ≤ (ε : ℝ) ^ 2) :
    NonconvexAccuracy K (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ε := by
  unfold NonconvexAccuracy
  have hBoundary :=
    Theorem_D3_heterogeneous_online_VR_nonconvex_initialization_corrected_of_literal_and_lawRegularity
      (b := b) (b0 := b0) (K := K) A x0 Llocal ℒlocal σ ω fStar
        hLower hSmooth hLiteral hQuantizer hAssumption32 hRegularity hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
    (b := b) A x0 σ hLiteral hSmooth.1
  have hdenom : 0 ≤ (A.refreshProbability : ℝ) * K.1 :=
    mul_nonneg A.refresh_admissible.1.le (by positivity)
  have hInitialDiv :
      expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) ≤
        heterogeneousOnlineVarianceTerm σ b /
          (A.refreshProbability * K.1) :=
    div_le_div_of_nonneg_right hInitial hdenom
  calc
    2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm σ b ≤
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        heterogeneousOnlineVarianceTerm σ b /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm σ b := by gcongr
    _ ≤ (ε : ℝ) ^ 2 := hBudget

/-- Homogeneous executable D.3 with source Assumption 3.2 kept in its
conditional law-a.e. form.  This is a proved-transfer wrapper around the
constant-worker-batch specialization of the heterogeneous executable
recurrence: the process, path law, initialization, query schedule, and
measured variance object are identified explicitly. -/
theorem onlineExecutableNonconvexAccuracy_of_budget_of_literal_and_lawRegularityAE
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (ε : Accuracy)
    (hBudget :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        (varianceAggregateSq σ / (n.1 * b.1)) /
          (A.refreshProbability * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) ≤ (ε : ℝ) ^ 2) :
    NonconvexAccuracy K (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ε := by
  let bConst := fun _ : Worker n ↦ b
  let b0Const := fun _ : Worker n ↦ b0
  have hAssumption32Het :
      HeterogeneousOnlineAssumption32GenuineAE (b0 := b0Const) A.problem
        (heterogeneousOnlineProcess (b := bConst) (b0 := b0Const) A x0)
        (heterogeneousOnlinePathLaw (b := bConst) (b0 := b0Const) A) ℒlocal :=
    (onlineAssumption32GenuineAE_iff_heterogeneous_const
      A x0 hBatch ℒlocal).mp hAssumption32
  have hStepHet : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal)
      (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0Const)
      A.refreshProbability ω n := by
    rw [show heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0Const =
        (rootMeanSquare ℒlocal) ^ 2 / b0.1 by
      exact heterogeneousFiniteBatchSmoothnessTerm_const ℒlocal]
    unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition at hStep
    unfold HeterogeneousVRStepsizeCondition
    simpa only [mul_div_assoc] using hStep
  have hBudgetHet :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        heterogeneousOnlineVarianceTerm σ bConst /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm σ bConst ≤ (ε : ℝ) ^ 2 := by
    simpa [bConst, heterogeneousOnlineVarianceTerm_const] using hBudget
  have hHet :=
    heterogeneousOnlineExecutableNonconvexAccuracy_of_budget_of_literal_and_lawRegularity
      (b := bConst) (b0 := b0Const) (K := K) A x0 Llocal ℒlocal σ
        ω fStar hLower hSmooth hLiteral hQuantizer hAssumption32Het
        hRegularity hStepHet ε hBudgetHet
  have hProcess : onlineProcess (b := b) (b0 := b0) A x0 hBatch =
      heterogeneousOnlineProcess (b := bConst) (b0 := b0Const) A x0 := by
    funext k path
    exact onlineProcess_eq_heterogeneousOnlineProcess_const
      A x0 hBatch k path
  rw [hProcess, onlinePathLaw_eq_heterogeneousOnlinePathLaw_const A]
  exact hHet

/-- Accuracy-scheduled homogeneous executable D.3 under the law-a.e. source
Assumption 3.2 contract.  Each accuracy uses its own generated batch, process,
and canonical path law; no universal null-path witness is reconstructed. -/
theorem onlineExecutableNonconvexAccuracy_family_of_budget_of_literal_and_lawRegularityAE
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAssumption32 : ∀ ε, OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (hBudget : ∀ ε,
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * (K ε).1) +
        (varianceAggregateSq σ / (n.1 * (b ε).1)) /
          (A.refreshProbability * (K ε).1) +
        varianceAggregateSq σ / (n.1 * (b ε).1) ≤ (ε : ℝ) ^ 2) :
    ∀ ε, NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ε := by
  intro ε
  exact
    onlineExecutableNonconvexAccuracy_of_budget_of_literal_and_lawRegularityAE
      A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hLiteral hQuantizer
        (hBatch ε) (hAssumption32 ε) hRegularity hStep ε (hBudget ε)

theorem onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularityAE
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε))
      (onlinePathLaw
        (b := onlineNonconvexBatchScheduleFromBase n b0
          (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch ε)
        (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let iterationScale := fun ε : Accuracy =>
      1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let V : ℝ := varianceAggregateSq σ
  let chosenBatch : Accuracy → Count :=
    onlineNonconvexBatchScheduleFromBase n b0
      (2 * V / A.refreshProbability) baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let iterationScale : Accuracy → ℝ := fun ε =>
    1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
  let K : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (4 * Δ /
      ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
  have hV : 0 ≤ V := by
    dsimp [V, varianceAggregateSq, meanSquare, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (hLower x0)
  have hEffectiveVariance : 0 ≤ 2 * V / A.refreshProbability := by
    positivity
  have hBatch : ∀ ε, OnlineBatchAdmissible (chosenBatch ε) b0 := by
    intro ε
    simpa [chosenBatch] using
      onlineNonconvexBatchScheduleFromBase_admissible n b0
        (2 * V / A.refreshProbability) baseBatch ε
  have hFloor (eps : Accuracy) :
      V / (n.1 * (chosenBatch eps).1) ≤
        A.refreshProbability * (eps : ℝ) ^ 2 / 4 := by
    have hEff := onlineNonconvexBatchScheduleFromBase_variance_floor
      n b0 (2 * V / A.refreshProbability) hEffectiveVariance
        baseBatch eps
    have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hb : ((chosenBatch eps).1 : ℝ) ≠ 0 := by
      exact_mod_cast (chosenBatch eps).2.ne'
    have hpne : A.refreshProbability ≠ 0 := ne_of_gt hp
    dsimp [chosenBatch] at hEff ⊢
    rw [div_le_iff₀ (by positivity : 0 < (n.1 : ℝ) *
      (onlineNonconvexBatchScheduleFromBase n b0
        (2 * V / A.refreshProbability) baseBatch eps).1)] at hEff ⊢
    field_simp [hpne, hn, hb] at hEff ⊢
    nlinarith
  have hOptimizationHalf (eps : Accuracy) :
      2 * Δ / ((A.stepSize : ℝ) * (K eps).1) ≤
        (eps : ℝ) ^ 2 / 2 := by
    have hKpos : 0 < ((K eps).1 : ℝ) := by exact_mod_cast (K eps).2
    have hγpos : 0 < (A.stepSize : ℝ) := A.stepSize.property
    have hBudget := div_natCast_max_one_ceil_div_le
      (4 * Δ) ((A.stepSize : ℝ) * (eps : ℝ) ^ 2)
        (mul_pos hγpos (sq_pos_of_pos eps.property))
    have hBudget' :
        4 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ)) ≤
          (eps : ℝ) ^ 2 := by
      rw [div_le_iff₀ (mul_pos hγpos hKpos)]
      have hRaw : 4 * Δ / ((K eps).1 : ℝ) ≤
          (A.stepSize : ℝ) * (eps : ℝ) ^ 2 := by
        simpa [K] using hBudget
      rw [div_le_iff₀ hKpos] at hRaw
      nlinarith
    calc
      2 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ)) =
          (1 / 2 : ℝ) *
            (4 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ))) := by
              field_simp [ne_of_gt hγpos, ne_of_gt hKpos]
              all_goals ring
      _ ≤ (1 / 2 : ℝ) * (eps : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hBudget' (by norm_num)
      _ = (eps : ℝ) ^ 2 / 2 := by ring
  have hInitialQuarter (eps : Accuracy) :
      (V / (n.1 * (chosenBatch eps).1)) /
          (A.refreshProbability * (K eps).1) ≤
        (eps : ℝ) ^ 2 / 4 := by
    have hKone : (1 : ℝ) ≤ (K eps).1 := by
      exact_mod_cast (K eps).2
    rw [div_le_iff₀ (mul_pos hp (by positivity : 0 < ((K eps).1 : ℝ)))]
    have hFloor' := hFloor eps
    calc
      V / (n.1 * (chosenBatch eps).1) ≤
          A.refreshProbability * (eps : ℝ) ^ 2 / 4 := hFloor'
      _ ≤ (A.refreshProbability * (eps : ℝ) ^ 2 / 4) *
          (K eps).1 :=
        le_mul_of_one_le_right (by positivity) hKone
      _ = (eps : ℝ) ^ 2 / 4 *
          (A.refreshProbability * (K eps).1) := by ring
  have hAccuracy : ∀ eps, NonconvexAccuracy (K eps)
      (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch eps))
      (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) eps := by
    apply onlineExecutableNonconvexAccuracy_family_of_budget_of_literal_and_lawRegularityAE
      A x0 chosenBatch K Llocal ℒlocal σ ω fStar hLower hSmooth
        hLiteral hQuantizer hBatch
    · intro eps
      simpa [chosenBatch] using hAssumption32 eps
    · exact hRegularity
    · exact hStep
    · intro eps
      have hSteadyQuarter :
          V / (n.1 * (chosenBatch eps).1) ≤ (eps : ℝ) ^ 2 / 4 :=
        (hFloor eps).trans (by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left (sq_nonneg _) hp1)
      calc
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
              ((A.stepSize : ℝ) * (K eps).1) +
            (varianceAggregateSq σ / (n.1 * (chosenBatch eps).1)) /
              (A.refreshProbability * (K eps).1) +
            varianceAggregateSq σ / (n.1 * (chosenBatch eps).1) ≤
            (eps : ℝ) ^ 2 / 2 + (eps : ℝ) ^ 2 / 4 +
              (eps : ℝ) ^ 2 / 4 := by
          simpa [V, Δ] using
            (add_le_add (add_le_add (hOptimizationHalf eps)
              (hInitialQuarter eps)) hSteadyQuarter)
        _ = (eps : ℝ) ^ 2 := by ring
  have hKBound (eps : Accuracy) : ((K eps).1 : ℝ) ≤
      2 * iterationScale eps := by
    let q : ℝ := 4 * Δ / ((A.stepSize : ℝ) * (eps : ℝ) ^ 2)
    have hq : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg A.stepSize.property.le (sq_nonneg _))
    have hceil := natCast_max_one_ceil_le_add_two q hq
    have hscale : iterationScale eps = 1 + q := by
      simp [iterationScale, q]
    rw [show ((K eps).1 : ℝ) =
      ((max 1 (Nat.ceil q) : ℕ) : ℝ) by simp [K, q]]
    rw [hscale]
    linarith
  have hScalePos (eps : Accuracy) : 0 < iterationScale eps := by
    dsimp [iterationScale]
    have : 0 ≤ 4 * Δ /
        ((A.stepSize : ℝ) * (eps : ℝ) ^ 2) := by
      exact div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg A.stepSize.property.le (sq_nonneg _))
    linarith
  have hKBigO : AccuracyBigO (fun eps => ((K eps).1 : ℝ))
      iterationScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro eps
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((K eps).1 : ℝ)), Real.norm_eq_abs,
      abs_of_pos (hScalePos eps)]
    exact hKBound eps
  have hEndpoints : ThreeEndpointComplexity K
      (fun eps => NonconvexAccuracy (K eps)
        (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch eps))
        (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) eps)
      iterationScale
      (fun eps => onlineOracleCallCount (chosenBatch eps) b0 (K eps)
        A.refreshProbability)
      (fun eps => (chosenBatch eps).1 + iterationScale eps *
        (A.refreshProbability * (chosenBatch eps).1 +
          2 * (1 - A.refreshProbability) * b0.1))
      (fun eps => allWorkerCommunicationCount d (K eps)
        A.refreshProbability (expectedDensity A.quantizer))
      (fun eps => d.1 + iterationScale eps *
        (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
    unfold ThreeEndpointComplexity
    refine ⟨hAccuracy, Or.inr hKBigO, ?_, ?_⟩
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * (chosenBatch eps).1 +
        2 * (1 - A.refreshProbability) * b0.1
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            (by positivity))
      have hactual : 0 ≤ onlineOracleCallCount (chosenBatch eps) b0
          (K eps) A.refreshProbability := by
        unfold onlineOracleCallCount
        exact add_nonneg (by positivity)
          (mul_nonneg (by positivity) hpayload)
      have htarget : 0 < (chosenBatch eps).1 +
          iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast (chosenBatch eps).2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (chosenBatch eps).1 + ((K eps).1 : ℝ) * payload ≤
        2 * ((chosenBatch eps).1 + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * expectedDensity A.quantizer
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr hp1)
            (expectedDensity_nonneg_of_unbiased hQuantizer))
      have hactual : 0 ≤ allWorkerCommunicationCount d (K eps)
          A.refreshProbability (expectedDensity A.quantizer) := by
        unfold allWorkerCommunicationCount
        positivity
      have htarget : 0 < (d.1 : ℝ) + iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast d.2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (d.1 : ℝ) + ((K eps).1 : ℝ) * payload ≤
        2 * ((d.1 : ℝ) + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
  refine ⟨K, ?_⟩
  apply onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 chosenBatch hBatch
  · intro eps
    exact onlineCommunicationAELawRegularity_of_literal_and_lawRegularity
      A x0 (hBatch eps) σ hLiteral hRegularity
  · exact hQuantizer
  · exact hEndpoints

end MARINA
