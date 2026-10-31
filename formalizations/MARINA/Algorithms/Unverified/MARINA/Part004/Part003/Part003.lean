import Algorithms.Unverified.MARINA.Part003
import Algorithms.Unverified.MARINA.Part004.Part002
import Algorithms.Unverified.MARINA.Part004.Part003.Part002

-- Aggregator for `Algorithms.Unverified.MARINA`. Source declarations live under `MARINA/`.

namespace MARINA

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-! ## Literal online moment boundary

Assumption 3.3 states only the workerwise fixed-query unbiasedness and
bounded-variance equations.  Adaptive-query regularity used by the generated
Algorithm 3 proofs is kept separate below. -/

/-- Law-a.e. supplied-stepsize executable D.4 with measured costs.  The geometric
horizon allocates one quarter of the target to contraction.  The source
batch schedule allocates one half to the stationary variance floor, while
`2 γ μ ≤ p` makes the sampled-initializer contribution at most the
remaining quarter.  Consequently the accuracy field, oracle integral, and
communication integral all refer to the same sampled-initializer
`onlineProcess` experiment. -/
theorem onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularityAE
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
    (hAssumption32 : ∀ ε, OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
      (onlinePathLaw
        (b := onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        (b0 := b0) A) ℒlocal)
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
    apply onlineExecutablePLAccuracy_family_of_budget_of_literal_and_lawRegularityAE
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

/-- Law-a.e. canonical Eq. (40) specialization of the executable D.3 measured-cost
family.  The equality premise records the source's canonical choice of the
reciprocal Eq. (40) bracket; unlike the upper-bound-only stepsize condition,
it is strong enough to replace `1 / A.stepSize` by that bracket in the
complexity scale.  The additive `1` is the nonempty-output-window
totalization and also covers the already-solved zero-gap case.

The refresh batch remains the initialization-corrected executable schedule
from the supplied-step theorem.  Thus the convergence statement and the two
cost integrals still concern the same sampled-initializer `onlineProcess`
experiment. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularityAE
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
    onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularityAE
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

/-- Law-a.e. canonical Eq. (48) specialization of the executable D.4 measured-cost
family.  The canonical denominator simultaneously enforces the doubled
smoothness bracket and `2 γ μ ≤ p`.  Consequently the supplied reciprocal
stepsize scale is controlled by the source factor
`max (1 / p) (bracket / μ)`.  The `max 0` logarithm and additive `1` are the
totalized finite-horizon form of the printed geometric rate. -/
theorem onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularityAE
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
    (hAssumption32 : ∀ ε, OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProcess A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
      (onlinePathLaw
        (b := onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        (b0 := b0) A) ℒlocal)
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
    onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularityAE
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




theorem Theorem_D3_D4_measured_cost_complexity_with_separate_canonical_stepsizes_lawRegularityAE_compatibility
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
      OnlineAssumption32GenuineAE (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A γNonconvex A.refreshProbability
            A.refresh_admissible) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε))
        (onlinePathLaw
          (b := onlineNonconvexBatchScheduleFromBase n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)
          (b0 := b0)
          (onlineDataWithParameters A γNonconvex A.refreshProbability
            A.refresh_admissible)) ℒlocal)
    (hAssumption32PL : ∀ ε,
      OnlineAssumption32GenuineAE (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A γPL A.refreshProbability
            A.refresh_admissible) x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ plBaseBatch ε))
        (onlinePathLaw
          (b := onlinePLBatchScheduleFromBase n b0
            (varianceAggregateSq σ) μ plBaseBatch ε)
          (b0 := b0)
          (onlineDataWithParameters A γPL A.refreshProbability
            A.refresh_admissible)) ℒlocal)
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
        onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularityAE
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
        onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_lawRegularityAE
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
        onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularityAE
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
        onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_literal_and_lawRegularityAE
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

/-! ### Accuracy-scheduled executable Remark D.2 costs

The earlier heterogeneous measured-cost package has a single implicit batch
family `b`.  Remark D.2 instead chooses worker batches as a function of the
requested accuracy.  The following package keeps that quantifier visible, so
the accuracy, oracle, and communication statements all use the same batch,
horizon, executable process, and canonical path law. -/

/-- Measured executable Remark D.2 complexity for an accuracy-indexed family
of worker-dependent batches. -/
def HeterogeneousOnlineScheduledMeasuredCostComplexity
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Worker n → Count) (K : Accuracy → Count)
    (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε ↦ (K ε).1) iterationScale ∧
    ∀ i : Worker n,
      (∀ ε, Integrable
        (heterogeneousOnlineWorkerOracleCost
          (b := b ε) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i)
        (heterogeneousOnlinePathLaw (b := b ε) (b0 := b0) A)) ∧
      AccuracyBigO
        (fun ε ↦ ∫ path,
          heterogeneousOnlineWorkerOracleCost
            (b := b ε) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b ε) (b0 := b0) A)
        (oracleScale i) ∧
      (∀ ε, Integrable
        (heterogeneousOnlineWorkerCommunicationCost
          (b := b ε) (b0 := b0) A x0 (K ε) i)
        (heterogeneousOnlinePathLaw (b := b ε) (b0 := b0) A)) ∧
      AccuracyBigO
        (fun ε ↦ ∫ path,
          heterogeneousOnlineWorkerCommunicationCost
            (b := b ε) (b0 := b0) A x0 (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b ε) (b0 := b0) A)
        communicationScale

/-- Accuracy-varying analogue of the source/correction-derived measured-cost
lift.  It derives integrability of the actual observables separately at every
source batch; no cost-measurability or integrability witness is an input. -/
theorem
    heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Worker n → Count)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hGradientRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ)
    (hAccuracy : ∀ ε, accuracy ε)
    (hIteration : AccuracyIterationBigO (fun ε ↦ (K ε).1) iterationScale)
    (hOracle : ∀ i, AccuracyBigO
      (fun ε ↦ ((b ε i).1 : ℝ) + (K ε).1 *
        (A.refreshProbability * (b ε i).1 +
          2 * (1 - A.refreshProbability) * (b0 i).1))
      (oracleScale i))
    (hCommunication : AccuracyBigO
      (fun ε ↦ allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    HeterogeneousOnlineScheduledMeasuredCostComplexity
      (b0 := b0) A x0 b K accuracy iterationScale oracleScale
        communicationScale := by
  unfold HeterogeneousOnlineScheduledMeasuredCostComplexity
  refine ⟨hAccuracy, hIteration, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
      (b := b ε) (b0 := b0) A (K ε) i).1
  · rw [show (fun ε ↦ ∫ path,
        heterogeneousOnlineWorkerOracleCost
          (b := b ε) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b ε) (b0 := b0) A) =
        (fun ε ↦ ((b ε i).1 : ℝ) + (K ε).1 *
          (A.refreshProbability * (b ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1)) by
      funext ε
      exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
        (b := b ε) (b0 := b0) A (K ε) i).2]
    exact hOracle i
  · intro ε
    exact
      (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_literal_and_lawRegularity
        (b := b ε) (b0 := b0) A x0 sigma hLiteral hGradientRegularity hQ
          (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hCommunication
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path ↦
        heterogeneousOnlineWorkerCommunicationCost_nonneg
          A x0 (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability := A.refresh_admissible.1.le
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact
        (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_literal_and_lawRegularity
          (b := b ε) (b0 := b0) A x0 sigma hLiteral hGradientRegularity hQ
            (K ε) i).2

/-- Refresh-scaled accuracy used by the executable Remark D.2 batch schedule.
The scaling reserves one quarter of the requested squared-accuracy budget for
the variance floor and another quarter for the executable initializer. -/
noncomputable def heterogeneousOnlineExecutableBatchAccuracy
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (ε : Accuracy) : Accuracy :=
  ⟨(ε : ℝ) * Real.sqrt (A.refreshProbability / 2),
    mul_pos ε.property (Real.sqrt_pos.2 (div_pos A.refresh_admissible.1 (by norm_num)))⟩

/-- Worker-dependent source schedule with enough common inflation to absorb
the exact stochastic-initialization error of the executable process. -/
noncomputable def heterogeneousOnlineExecutableBatchScheduleFromBase
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (sigma : Worker n → ℝ)
    (base : Accuracy → Worker n → Count)
    (ε : Accuracy) : Worker n → Count :=
  heterogeneousOnlineBatchScheduleFromBase sigma base
    (heterogeneousOnlineExecutableBatchAccuracy A ε)

theorem heterogeneousOnlineExecutableBatchScheduleFromBase_admissible
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (sigma : Worker n → ℝ)
    (base : Accuracy → Worker n → Count) (b0 : Worker n → Count)
    (hbase : ∀ ε i, (b0 i).1 < (base ε i).1)
    (ε : Accuracy) (i : Worker n) :
    (b0 i).1 <
      (heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε i).1 := by
  exact heterogeneousOnlineBatchScheduleFromBase_admissible sigma base b0 hbase
    (heterogeneousOnlineExecutableBatchAccuracy A ε) i

/-- The refresh-scaled batch schedule simultaneously bounds the steady-state
variance and, after division by `p K`, the stochastic-initializer term. -/
theorem heterogeneousOnlineExecutableBatchScheduleFromBase_variance_floor
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (sigma : Worker n → ℝ)
    (base : Accuracy → Worker n → Count) (ε : Accuracy) :
    heterogeneousOnlineVarianceTerm sigma
        (heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε) ≤
      A.refreshProbability * (ε : ℝ) ^ 2 / 4 := by
  have h := heterogeneousOnlineBatchScheduleFromBase_variance_floor sigma base
    (heterogeneousOnlineExecutableBatchAccuracy A ε)
  have hp0 : 0 ≤ A.refreshProbability / 2 :=
    (div_pos A.refresh_admissible.1 (by norm_num)).le
  have hsqrt : (Real.sqrt (A.refreshProbability / 2)) ^ 2 =
      A.refreshProbability / 2 := Real.sq_sqrt hp0
  calc
    heterogeneousOnlineVarianceTerm sigma
        (heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε) ≤
        ((heterogeneousOnlineExecutableBatchAccuracy A ε : Accuracy) : ℝ) ^ 2 / 2 := h
    _ = A.refreshProbability * (ε : ℝ) ^ 2 / 4 := by
      change ((ε : ℝ) * Real.sqrt (A.refreshProbability / 2)) ^ 2 / 2 = _
      rw [mul_pow, hsqrt]
      ring

/-- Rescaling the requested accuracy by the fixed positive refresh factor does
not change the source `Theta(epsilon^2)` order of the worker-dependent variance
term.  Thus this order is stated for the same executable batch family used by
the process, path law, accuracy theorem, and measured costs. -/
theorem heterogeneousOnlineExecutableBatchScheduleFromBase_accuracyTheta
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (sigma : Worker n → ℝ)
    (base : Accuracy → Worker n → Count)
    (hbase : AccuracyTheta
      (fun ε ↦ heterogeneousOnlineVarianceTerm sigma (base ε))
      (fun ε ↦ (ε : ℝ) ^ 2)) :
    AccuracyTheta
      (fun ε ↦ heterogeneousOnlineVarianceTerm sigma
        (heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε))
      (fun ε ↦ (ε : ℝ) ^ 2) := by
  have hScheduled :=
    heterogeneousOnlineBatchScheduleFromBase_accuracyTheta sigma base hbase
  have hpHalf : 0 < A.refreshProbability / 2 :=
    div_pos A.refresh_admissible.1 (by norm_num)
  have hScaleTendsto : Filter.Tendsto
      (heterogeneousOnlineExecutableBatchAccuracy A)
      accuracyToZero accuracyToZero := by
    rw [accuracyToZero, Filter.tendsto_comap_iff]
    have hInv : Filter.Tendsto (fun ε : Accuracy ↦ ((ε : ℝ)⁻¹))
        accuracyToZero Filter.atTop := by
      exact Filter.tendsto_comap
    have hScaled :=
      (Filter.tendsto_const_mul_atTop_of_pos
        (inv_pos.mpr (Real.sqrt_pos.2 hpHalf))).2 hInv
    simpa [Function.comp_def, heterogeneousOnlineExecutableBatchAccuracy,
      mul_inv_rev] using hScaled
  unfold AccuracyTheta at hScheduled ⊢
  have hComposed : Asymptotics.IsTheta accuracyToZero
      ((fun δ : Accuracy ↦ heterogeneousOnlineVarianceTerm sigma
          (heterogeneousOnlineBatchScheduleFromBase sigma base δ)) ∘
        heterogeneousOnlineExecutableBatchAccuracy A)
      ((fun δ : Accuracy ↦ (δ : ℝ) ^ 2) ∘
        heterogeneousOnlineExecutableBatchAccuracy A) :=
    ⟨hScheduled.1.comp_tendsto hScaleTendsto,
      hScheduled.2.comp_tendsto hScaleTendsto⟩
  have hSquare : Asymptotics.IsTheta accuracyToZero
      ((fun δ : Accuracy ↦ (δ : ℝ) ^ 2) ∘
        heterogeneousOnlineExecutableBatchAccuracy A)
      (fun ε : Accuracy ↦ (ε : ℝ) ^ 2) := by
    have hRefl := Asymptotics.isTheta_refl
      (fun ε : Accuracy ↦ (ε : ℝ) ^ 2) accuracyToZero
    have hMul := hRefl.const_mul_left (ne_of_gt hpHalf)
    convert hMul using 1
    funext ε
    change ((ε : ℝ) * Real.sqrt (A.refreshProbability / 2)) ^ 2 =
      (A.refreshProbability / 2) * (ε : ℝ) ^ 2
    rw [mul_pow, Real.sq_sqrt hpHalf.le]
    ring
  simpa [Function.comp_def,
    heterogeneousOnlineExecutableBatchScheduleFromBase] using
      hComposed.trans hSquare

/-- The refresh-scaled batch floor turns the executable three-term D.3 bound
into the requested accuracy once the ordinary optimization term receives half
of the squared-accuracy budget.  This is the scalar bridge used to choose the
single horizon family for convergence and measured costs. -/
theorem heterogeneousOnlineExecutableBatchSchedule_budget
    {d n K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (sigma : Worker n → ℝ)
    (base : Accuracy → Worker n → Count) (ε : Accuracy)
    (gap : ℝ)
    (hOptimization : 2 * gap / (A.stepSize * K.1) ≤ (ε : ℝ) ^ 2 / 2) :
    2 * gap / (A.stepSize * K.1) +
        heterogeneousOnlineVarianceTerm sigma
            (heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε) /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm sigma
            (heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε) ≤
      (ε : ℝ) ^ 2 := by
  let V := heterogeneousOnlineVarianceTerm sigma
    (heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
  have hV : V ≤ A.refreshProbability * (ε : ℝ) ^ 2 / 4 := by
    simpa [V] using
      heterogeneousOnlineExecutableBatchScheduleFromBase_variance_floor
        A sigma base ε
  have hVnonneg : 0 ≤ V := by
    dsimp [V, heterogeneousOnlineVarianceTerm, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hK : 1 ≤ ((K.1 : ℕ) : ℝ) := by exact_mod_cast K.2
  have hdenom : 0 < A.refreshProbability * (K.1 : ℝ) := by positivity
  have hInitial : V / (A.refreshProbability * (K.1 : ℝ)) ≤
      (ε : ℝ) ^ 2 / 4 := by
    rw [div_le_iff₀ hdenom]
    have heps : 0 ≤ (ε : ℝ) ^ 2 := sq_nonneg _
    calc
      V ≤ A.refreshProbability * (ε : ℝ) ^ 2 / 4 := hV
      _ ≤ ((ε : ℝ) ^ 2 / 4) *
          (A.refreshProbability * (K.1 : ℝ)) := by
        nlinarith
  have hSteady : V ≤ (ε : ℝ) ^ 2 / 4 := by
    have heps : 0 ≤ (ε : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  change 2 * gap / (A.stepSize * K.1) +
      V / (A.refreshProbability * K.1) + V ≤ (ε : ℝ) ^ 2
  linarith

/-- Executable heterogeneous accuracy for the refresh-scaled source batch.
Only the ordinary optimization-term budget remains for the horizon chooser;
the literal moment contract supplies the initializer bound and the batch
schedule supplies both variance budgets. -/
theorem
    heterogeneousOnlineExecutableNonconvexAccuracy_of_half_optimization_budget
    {d n K : Count} {Sample : Worker n → Type*} {b0 : Worker n → Count}
    {Ξ : Type*} [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (base : Accuracy → Worker n → Count)
    (Llocal ℒlocal sigma : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (ε : Accuracy)
    (hAssumption32 : HeterogeneousOnlineAssumption32GenuineAE (b0 := b0)
      A.problem
        (heterogeneousOnlineProcess
          (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
          (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw
          (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
          (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n)
    (hOptimization :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) ≤ (ε : ℝ) ^ 2 / 2) :
    NonconvexAccuracy K (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess
        (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
        (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw
        (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
        (b0 := b0) A) ε := by
  apply
    heterogeneousOnlineExecutableNonconvexAccuracy_of_budget_of_literal_and_lawRegularity
      (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
      (b0 := b0) A x0 Llocal ℒlocal sigma ω fStar hLower hSmooth hLiteral
        hQuantizer hAssumption32 hRegularity hStep ε
  exact heterogeneousOnlineExecutableBatchSchedule_budget A sigma base ε
    (globalObjective (onlineLocalProblem A.problem) x0 - fStar) hOptimization

/-! ### Concrete executable Remark D.2 horizon

The executable heterogeneous bound above leaves exactly one half of the
squared-accuracy budget for optimization.  The following positive natural
ceiling realizes that budget.  It is deliberately independent of the batch
family: the refresh-scaled worker batches already pay both stochastic terms,
so this is the single horizon used by accuracy and by both measured costs. -/

/-- Accuracy-indexed executable horizon for Remark D.2.  Its factor four is
the exact price of reserving half of the squared-accuracy budget for the two
variance terms. -/
noncomputable def heterogeneousOnlineExecutableHorizon
    (gap : ℝ) (step : PositiveStepsize) : Accuracy → Count := fun ε ↦
  ⟨max 1 (Nat.ceil
    (2 * gap / (((step : ℝ) / 2) * (ε : ℝ) ^ 2))), by omega⟩

/-- The concrete horizon gives the half-optimization budget for every
nonnegative objective gap, including the source's already-solved zero-gap
case. -/
theorem heterogeneousOnlineExecutableHorizon_half_optimization_budget
    (gap : ℝ) (step : PositiveStepsize) (hgap : 0 ≤ gap) :
    ∀ ε : Accuracy,
      2 * gap /
          ((step : ℝ) * (heterogeneousOnlineExecutableHorizon gap step ε).1) ≤
        (ε : ℝ) ^ 2 / 2 := by
  intro ε
  rcases hgap.eq_or_lt with hzero | hpos
  · rw [← hzero]
    simp only [mul_zero, zero_div]
    exact div_nonneg (sq_nonneg (ε : ℝ)) (by norm_num)
  · have hhalf : 0 < (step : ℝ) / 2 := div_pos step.property (by norm_num)
    have hScalar :=
      (positive_inverse_square_ceiling_schedule gap ((step : ℝ) / 2) 1
        hpos hhalf (by norm_num)).1 ε
    have hKpos : 0 <
        (((heterogeneousOnlineExecutableHorizon gap step ε).1 : ℕ) : ℝ) := by
      exact_mod_cast (heterogeneousOnlineExecutableHorizon gap step ε).2
    have hScaled := mul_le_mul_of_nonneg_left hScalar
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    calc
      2 * gap /
          ((step : ℝ) * (heterogeneousOnlineExecutableHorizon gap step ε).1) =
          (1 / 2 : ℝ) *
            (2 * gap /
              (((step : ℝ) / 2) *
                (heterogeneousOnlineExecutableHorizon gap step ε).1)) := by
                  field_simp [ne_of_gt step.property, ne_of_gt hKpos]
      _ ≤ (1 / 2 : ℝ) * (ε : ℝ) ^ 2 := by
        simpa [heterogeneousOnlineExecutableHorizon] using hScaled
      _ = (ε : ℝ) ^ 2 / 2 := by ring

/-- In the nondegenerate source branch the same concrete horizon has the
printed inverse-square iteration order with the heterogeneous smoothness
bracket. -/
theorem heterogeneousOnlineExecutableHorizon_bigO_source_bracket
    (gap : ℝ) (step : PositiveStepsize) (bracket : ℝ)
    (hgap : 0 < gap) (hbracket : 0 < bracket) :
    AccuracyBigO
      (fun ε ↦ ((heterogeneousOnlineExecutableHorizon gap step ε).1 : ℝ))
      (fun ε ↦ gap / (ε : ℝ) ^ 2 * bracket) := by
  have hhalf : 0 < (step : ℝ) / 2 := div_pos step.property (by norm_num)
  simpa [heterogeneousOnlineExecutableHorizon] using
    (positive_inverse_square_ceiling_schedule gap ((step : ℝ) / 2)
      bracket hgap hhalf hbracket).2

/-- At zero objective gap the concrete horizon is the one-round totalization,
so it satisfies the dedicated zero-scale branch of `AccuracyIterationBigO`. -/
theorem heterogeneousOnlineExecutableHorizon_iteration_bigO_of_gap_zero
    (gap : ℝ) (step : PositiveStepsize) (bracket : ℝ)
    (hgap : gap = 0) :
    AccuracyIterationBigO
      (fun ε ↦ ((heterogeneousOnlineExecutableHorizon gap step ε).1 : ℝ))
      (fun ε ↦ gap / (ε : ℝ) ^ 2 * bracket) := by
  refine Or.inl ⟨?_, ?_⟩
  · intro ε
    rw [hgap]
    ring
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, Filter.Eventually.of_forall ?_⟩
    intro ε
    have hval : (heterogeneousOnlineExecutableHorizon gap step ε).1 = 1 := by
      simp [heterogeneousOnlineExecutableHorizon, hgap]
      exact_mod_cast (rfl : (1 : ℕ) = 1)
    rw [hval]
    norm_num

/-- The release horizon for executable Remark D.2.  When the objective gap or
the heterogeneous smoothness bracket vanishes, the source scale is zero and a
single output round is enough; otherwise it is the concrete executable
ceiling above. -/
noncomputable def heterogeneousOnlineExecutableRemarkHorizon
    (gap : ℝ) (step : PositiveStepsize) (bracket : ℝ) : Accuracy → Count :=
  if gap = 0 ∨ bracket = 0 then fun _ ↦ ⟨1, by norm_num⟩
  else heterogeneousOnlineExecutableHorizon gap step

/-- Conditional compatibility form of the executable measured Remark D.2
boundary.  The public source boundary below replaces its all-query regularity
premise by the generated Assumption 3.2 kernel while preserving this route.  The workerwise
batch family, convergence conclusion, oracle integrals, and communication
integrals all use the same generated `heterogeneousOnlineProcess`, canonical
`heterogeneousOnlinePathLaw`, and branch-aware horizon.  Literal fixed-query
moments and the separately classified adaptive-law correction remain visible;
no cost-measurability or integrability witness is an input. -/
theorem Remark_D2_heterogeneous_online_batches_executable_measured_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (base : Accuracy → Worker n → Count) (b0 : Worker n → Count)
    (Llocal ℒlocal sigma : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBase : ∀ ε i, (b0 i).1 < (base ε i).1)
    (hBaseOrder : AccuracyTheta
      (fun ε ↦ heterogeneousOnlineVarianceTerm sigma (base ε))
      (fun ε ↦ (ε : ℝ) ^ 2))
    (hAssumption32 : ∀ ε,
      HeterogeneousOnlineAssumption32GenuineAE (b0 := b0) A.problem
        (heterogeneousOnlineProcess
          (b := heterogeneousOnlineExecutableBatchScheduleFromBase
            A sigma base ε) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw
          (b := heterogeneousOnlineExecutableBatchScheduleFromBase
            A sigma base ε) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    let chosenBatch :=
      heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base
    let P := onlineLocalProblem A.problem
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal + Real.sqrt
      ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
    let K := heterogeneousOnlineExecutableRemarkHorizon Δ A.stepSize bracket
    AccuracyTheta
        (fun ε ↦ heterogeneousOnlineVarianceTerm sigma (chosenBatch ε))
        (fun ε ↦ (ε : ℝ) ^ 2) ∧
      HeterogeneousOnlineScheduledMeasuredCostComplexity (b0 := b0)
        A x0 chosenBatch K
        (fun ε ↦ NonconvexAccuracy (K ε) P
          (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
          (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
        (fun ε ↦ Δ / (ε : ℝ) ^ 2 * bracket)
        (fun i ε ↦ (chosenBatch ε i).1 +
          Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1))
        (fun ε ↦ d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) := by
  classical
  dsimp
  refine ⟨heterogeneousOnlineExecutableBatchScheduleFromBase_accuracyTheta
    A sigma base hBaseOrder, ?_⟩
  let chosenBatch :=
    heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base
  let P := onlineLocalProblem A.problem
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective P x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal + Real.sqrt
    ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
      (ω * rootMeanSquare Llocal ^ 2 +
        (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
  let K := heterogeneousOnlineExecutableRemarkHorizon Δ A.stepSize bracket
  let iterationScale : Accuracy → ℝ := fun ε ↦
    Δ / (ε : ℝ) ^ 2 * bracket
  have hGapNonneg : 0 ≤ Δ := by
    dsimp [Δ, P]
    exact sub_nonneg.mpr (hLower x0)
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hChosenBatch : ∀ ε i, (b0 i).1 < (chosenBatch ε i).1 := by
    intro ε i
    exact heterogeneousOnlineExecutableBatchScheduleFromBase_admissible
      A sigma base b0 hBase ε i
  have hAccuracyPositive (hGapPos : 0 < Δ) (hBracketPos : 0 < bracket) :
      ∀ ε, NonconvexAccuracy (K ε) P
        (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε := by
    intro ε
    apply heterogeneousOnlineExecutableNonconvexAccuracy_of_half_optimization_budget
      (K := K ε) A x0 base Llocal ℒlocal sigma ω fStar hLower hSmooth
        hLiteral hQuantizer ε (hAssumption32 ε) hRegularity hStep
    simpa [K, chosenBatch, heterogeneousOnlineExecutableRemarkHorizon,
      hGapPos.ne', hBracketPos.ne'] using
        (heterogeneousOnlineExecutableHorizon_half_optimization_budget
          Δ A.stepSize hGapPos.le ε)
  have hOracleZero
      (hKOne : ∀ ε, (K ε).1 = 1)
      (hScaleZero : ∀ ε, iterationScale ε = 0) :
      ∀ i, AccuracyBigO
        (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + (K ε).1 *
          (A.refreshProbability * (chosenBatch ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1))
        (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1)) := by
    intro i
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨4, Filter.Eventually.of_forall ?_⟩
    intro ε
    let B : ℝ := (chosenBatch ε i).1
    let B0 : ℝ := (b0 i).1
    have hB : 0 < B := by
      dsimp [B]
      exact_mod_cast (chosenBatch ε i).2
    have hB0 : 0 < B0 := by
      dsimp [B0]
      exact_mod_cast (b0 i).2
    have hB0B : B0 < B := by
      dsimp [B0, B]
      exact_mod_cast hChosenBatch ε i
    have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
    have hActualNonneg : 0 ≤ B + (A.refreshProbability * B +
        2 * (1 - A.refreshProbability) * B0) := by
      exact add_nonneg hB.le (add_nonneg (mul_nonneg hp.le hB.le)
        (mul_nonneg (mul_nonneg (by norm_num) hOneSub) hB0.le))
    rw [hKOne ε, hScaleZero ε]
    simp only [Nat.cast_one, one_mul, zero_mul, add_zero]
    rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg,
      Real.norm_eq_abs, abs_of_pos hB]
    dsimp [B, B0] at *
    nlinarith [mul_nonneg hp.le hB.le, mul_nonneg hOneSub hB0.le]
  have hCommunicationZero
      (hKOne : ∀ ε, (K ε).1 = 1)
      (hScaleZero : ∀ ε, iterationScale ε = 0) :
      AccuracyBigO
        (fun ε ↦ allWorkerCommunicationCount d (K ε)
          A.refreshProbability ζ)
        (fun ε ↦ (d.1 : ℝ) + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) := by
    have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
    rw [show (fun ε ↦ allWorkerCommunicationCount d (K ε)
          A.refreshProbability ζ) =
        (fun _ : Accuracy ↦ (d.1 : ℝ) +
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) by
      funext ε
      simp [allWorkerCommunicationCount, hKOne ε]]
    rw [show (fun ε ↦ (d.1 : ℝ) + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) =
        (fun _ : Accuracy ↦ (d.1 : ℝ)) by
      funext ε
      rw [hScaleZero ε]
      ring]
    exact Asymptotics.isBigO_const_const
      ((d.1 : ℝ) + (A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * ζ)) hdne accuracyToZero
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · have hΔ : Δ = 0 := hGapZero.symm
    have hKOne : ∀ ε, (K ε).1 = 1 := by
      intro ε
      dsimp [K, heterogeneousOnlineExecutableRemarkHorizon]
      rw [if_pos (Or.inl hΔ)]
      rfl
    have hScaleZero : ∀ ε, iterationScale ε = 0 := by
      intro ε
      simp [iterationScale, hΔ]
    apply
      heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_literal_and_lawRegularity
        A x0 chosenBatch sigma hLiteral hRegularity hQuantizer K
        (fun ε ↦ NonconvexAccuracy (K ε) P
          (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
          (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
        iterationScale
        (fun i ε ↦ (chosenBatch ε i).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1))
        (fun ε ↦ d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ))
    · intro ε
      apply heterogeneousOnlineExecutableNonconvexAccuracy_of_half_optimization_budget
        (K := K ε) A x0 base Llocal ℒlocal sigma ω fStar hLower hSmooth
          hLiteral hQuantizer ε (hAssumption32 ε) hRegularity hStep
      have hRawGap :
          globalObjective (onlineLocalProblem A.problem) x0 - fStar = 0 := by
        simpa [Δ, P] using hΔ
      rw [hRawGap]
      norm_num only [mul_zero, zero_div]
      exact div_nonneg (sq_nonneg (ε : ℝ)) (by norm_num)
    · refine Or.inl ⟨hScaleZero, ?_⟩
      unfold AccuracyBigO
      convert Asymptotics.isBigO_refl (fun _ : Accuracy ↦ (1 : ℝ))
        accuracyToZero using 1
      funext ε
      simp [hKOne ε]
    · exact hOracleZero hKOne hScaleZero
    · exact hCommunicationZero hKOne hScaleZero
  · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
    · have hbracket : bracket = 0 := hBracketZero.symm
      have hKOne : ∀ ε, (K ε).1 = 1 := by
        intro ε
        dsimp [K, heterogeneousOnlineExecutableRemarkHorizon]
        rw [if_pos (Or.inr hbracket)]
        rfl
      have hScaleZero : ∀ ε, iterationScale ε = 0 := by
        intro ε
        simp [iterationScale, hbracket]
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
        have hsqrt : 0 ≤ Real.sqrt
            ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)) :=
          Real.sqrt_nonneg _
        dsimp [bracket] at hbracket
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        P Llocal fStar hLower hSmooth hLzero
      apply
        heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_literal_and_lawRegularity
          A x0 chosenBatch sigma hLiteral hRegularity hQuantizer K
          (fun ε ↦ NonconvexAccuracy (K ε) P
            (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
            (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
          iterationScale
          (fun i ε ↦ (chosenBatch ε i).1 + iterationScale ε *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1))
          (fun ε ↦ d.1 + iterationScale ε *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ))
      · intro ε
        unfold NonconvexAccuracy
        have hBoundary :=
          Theorem_D3_heterogeneous_online_VR_nonconvex_initialization_corrected_of_literal_and_lawRegularity
            (b := chosenBatch ε) (b0 := b0) (K := K ε)
              A x0 Llocal ℒlocal sigma ω fStar hLower hSmooth hLiteral
                hQuantizer (hAssumption32 ε) hRegularity hStep
        refine ⟨hBoundary.1, ?_⟩
        have heq : (fun z ↦ ‖globalGradient P
            (uniformOutput (K := K ε)
              (heterogeneousOnlineProcess
                (b := chosenBatch ε) (b0 := b0) A x0) z)‖ ^ 2) =
            (fun _ ↦ (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
      · refine Or.inl ⟨hScaleZero, ?_⟩
        unfold AccuracyBigO
        convert Asymptotics.isBigO_refl (fun _ : Accuracy ↦ (1 : ℝ))
          accuracyToZero using 1
        funext ε
        simp [hKOne ε]
      · exact hOracleZero hKOne hScaleZero
      · exact hCommunicationZero hKOne hScaleZero
    · have hKBigO : AccuracyBigO (fun ε ↦ ((K ε).1 : ℝ))
          iterationScale := by
        simpa [K, iterationScale, heterogeneousOnlineExecutableRemarkHorizon,
          hGapPos.ne', hBracketPos.ne'] using
            (heterogeneousOnlineExecutableHorizon_bigO_source_bracket
              Δ A.stepSize bracket hGapPos hBracketPos)
      have hScaleNonneg : ∀ᶠ ε in accuracyToZero, 0 ≤ iterationScale ε :=
        Filter.Eventually.of_forall fun ε ↦ by
          dsimp [iterationScale]
          positivity
      have hOracle : ∀ i, AccuracyBigO
          (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + (K ε).1 *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1))
          (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + iterationScale ε *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1)) := by
        intro i
        unfold AccuracyBigO at hKBigO ⊢
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨1 + C, by positivity, ?_⟩
        filter_upwards [hKC.bound] with ε hKc
        let B : ℝ := (chosenBatch ε i).1
        let payload : ℝ := A.refreshProbability * B +
          2 * (1 - A.refreshProbability) * (b0 i).1
        have hB : 0 < B := by
          dsimp [B]
          exact_mod_cast (chosenBatch ε i).2
        have hpayload : 0 ≤ payload := by
          dsimp [payload]
          exact add_nonneg
            (mul_nonneg hp.le (by positivity))
            (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
              (by positivity))
        have hscale : 0 < iterationScale ε := by
          dsimp [iterationScale]
          exact mul_pos (div_pos hGapPos (sq_pos_of_pos ε.property))
            hBracketPos
        have hKn : ((K ε).1 : ℝ) ≤ C * iterationScale ε := by
          change ‖((K ε).1 : ℝ)‖ ≤ C * ‖iterationScale ε‖ at hKc
          simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity :
            0 ≤ ((K ε).1 : ℝ)), abs_of_pos hscale] using hKc
        change ‖B + ((K ε).1 : ℝ) * payload‖ ≤
          (1 + C) * ‖B + iterationScale ε * payload‖
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
            0 ≤ B + ((K ε).1 : ℝ) * payload),
          Real.norm_eq_abs, abs_of_pos
            (add_pos_of_pos_of_nonneg hB (mul_nonneg hscale.le hpayload))]
        nlinarith [mul_le_mul_of_nonneg_right hKn hpayload]
      let commPayload : ℝ := A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * ζ
      have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
      have hCommPayloadPos : 0 < commPayload := by
        dsimp [commPayload]
        exact add_pos_of_pos_of_nonneg (mul_pos hp hdpos)
          (mul_nonneg (sub_nonneg.mpr hp1) hζ)
      have hCommunication : AccuracyBigO
          (fun ε ↦ allWorkerCommunicationCount d (K ε)
            A.refreshProbability ζ)
          (fun ε ↦ (d.1 : ℝ) + iterationScale ε *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ)) := by
        simpa [allWorkerCommunicationCount, commPayload] using
          (accuracyBigO_affine_cost_of_schedule
            (K := fun ε ↦ ((K ε).1 : ℝ))
            (scale := iterationScale) (init := (d.1 : ℝ))
            (actualPayload := commPayload) (targetPayload := commPayload)
            (payloadFactor := 1) hKBigO hdpos hCommPayloadPos.le
              hCommPayloadPos zero_lt_one (by simp) hScaleNonneg)
      apply
        heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_literal_and_lawRegularity
          A x0 chosenBatch sigma hLiteral hRegularity hQuantizer K
          (fun ε ↦ NonconvexAccuracy (K ε) P
            (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
            (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
          iterationScale
          (fun i ε ↦ (chosenBatch ε i).1 + iterationScale ε *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1))
          (fun ε ↦ d.1 + iterationScale ε *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ))
      · exact hAccuracyPositive hGapPos hBracketPos
      · exact Or.inr hKBigO
      · exact hOracle
      · exact hCommunication

set_option maxHeartbeats 3000000 in
/-- The proof-exact nonrefresh residual square is independent of the
same-round Bernoulli refresh coin.  This is a structural consequence of the
strict-past/current-round product law; it uses no Assumption 3.2 moment
premise and therefore applies unchanged at the law-a.e. source boundary. -/
theorem
    onlineProofExact_nonrefresh_error_sq_indep_refresh_of_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
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
    ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2)
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1) law := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((path k).2.1.2, (path k).2.2)
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
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
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let xNext := fun pref ↦ primalStep A.stepSize (prefixState pref)
  let x := fun pref ↦ (prefixState pref).x
  let direction := fun pref ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let innovationKernel := fun
      (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ)
      (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
    A.quantizer.apply
        (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
        (q.2 i) -
      localGradientDifference P i (xNext pref) (x pref))
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
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by rfl
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  have hcurrent : Measurable current := measurable_pi_apply k
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw)
      (nu := onlineRoundLaw (b := b) (b0 := b0) A)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [noise, current, Function.comp_def] using
      hpastCurrent.comp measurable_id
        (by fun_prop : Measurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2)))
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          (onlineRoundLaw A) := by
            rw [show Measure.map current law = onlineRoundLaw A by
              simpa [current, law, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = noiseLaw := by
        simpa [noiseLaw] using onlineRoundLaw_differenceCompression_marginal
          (b := b) (b0 := b0) A
  have hprefixState : AEMeasurable prefixState prefixLaw := by
    simpa [prefixState, prefixLaw] using
      onlineProofExactPrefixState_all_aemeasurable_of_lawRegularity
        A x0 hBatch hRegularity fallback k
  have hxNext : AEStronglyMeasurable xNext prefixLaw :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hprefixState)
      |>.aestronglyMeasurable
  have hx : AEStronglyMeasurable x prefixLaw :=
    ((measurable_state_x d).comp_aemeasurable hprefixState).aestronglyMeasurable
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    exact (((measurable_state_g d).comp_aemeasurable hprefixState).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hprefixState))).aestronglyMeasurable
  have hkernel : AEStronglyMeasurable
      (fun p ↦ innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
    simpa [innovationKernel, xNext, x, noiseLaw, P] using
      onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity prefixLaw xNext x hxNext hx
  have hkernelSq : AEStronglyMeasurable
      (fun p ↦ ‖innovationKernel p.1 p.2‖ ^ 2)
      (prefixLaw.prod noiseLaw) := by
    simpa [pow_two] using hkernel.norm.mul hkernel.norm
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, run]
    exact (onlineProofExactProcess_congr_prefix
      A x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])).symm
  have hinnovationComp : ∀ path,
      innovationKernel (prefixMap path) (noise path) = innovation path := by
    intro path
    dsimp [innovationKernel, innovation, xNext, x, noise]
    rw [hstatePrefix path]
    rw [show (run (k + 1) path).x = primalStep A.stepSize (run k path) by rfl]
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1
  let rest := fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2
  let branchRound := fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.1
  let restLaw := ((onlineBatchLaw A.problem b).prod
    (onlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let joined := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (prefixMap path, noise path)
  have hroundRest : ProbabilityTheory.IndepFun rest branchRound
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [onlineRoundLaw, restLaw, rest, branchRound] using h
  have hprefixRestBranch : ProbabilityTheory.IndepFun
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ ↦ (z.1, rest z.2))
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ ↦ branchRound z.2)
      (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) := by
    exact indepFun_prod_left_adjoin_of_indepFun prefixLaw
      (onlineRoundLaw (b := b) (b0 := b0) A) rest branchRound
      measurable_snd measurable_fst hroundRest
  have hpastRestBranch : ProbabilityTheory.IndepFun
      (fun path ↦ (prefixMap path, rest (current path))) branch law := by
    have hmap : Measure.map (fun path ↦ (prefixMap path, current path)) law =
        prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A) := by
      simpa [law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ onlineRoundLaw (b := b) (b0 := b0) A) k)
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hprefix.prodMk ((measurable_snd).comp hcurrent)).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    let leftProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ ↦ (z.1, rest z.2)
    let rightProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ ↦ branchRound z.2
    let Z := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      (prefixMap path, current path)
    have hleft : Measurable leftProd := by dsimp [leftProd]; fun_prop
    have hright : Measurable rightProd := by dsimp [rightProd]; fun_prop
    have hZ : Measurable Z := hprefix.prodMk hcurrent
    calc
      Measure.map
          (fun path ↦ ((prefixMap path, rest (current path)), branch path)) law =
          Measure.map (fun z ↦ (leftProd z, rightProd z)) (Measure.map Z law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleft.prodMk hright
            · exact hZ
      _ = Measure.map (fun z ↦ (leftProd z, rightProd z))
          (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) := by
            rw [show Measure.map Z law =
                prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A) by
              simpa [Z] using hmap]
      _ = (Measure.map leftProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))).prod
          (Measure.map rightProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleft.aemeasurable hright.aemeasurable).1 hprefixRestBranch
      _ = (Measure.map (fun path ↦ (prefixMap path, rest (current path))) law).prod
          (Measure.map branch law) := by
        rw [show Measure.map leftProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map (fun path ↦ (prefixMap path, rest (current path))) law by
          calc
            _ = Measure.map leftProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hleft hZ]
              congr 1]
        rw [show Measure.map rightProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map branch law by
          calc
            _ = Measure.map rightProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hright hZ]
              congr 1]
  have hjointBranch : ProbabilityTheory.IndepFun joined branch law := by
    have h := hpastRestBranch.comp
      (show Measurable
        (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
            ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) ↦ (z.1, (z.2.1.2, z.2.2))) by fun_prop)
      measurable_id
    simpa [joined, noise, current, rest, branch, Function.comp_def] using h
  have hnonrefreshKernel : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
        ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
      (prefixLaw.prod noiseLaw) := by
    have hv := hdirection.comp_fst.add hkernel
    simpa [pow_two] using hv.norm.mul hv.norm
  have hjJoined : Measurable joined := by
    dsimp [joined]
    exact hprefix.prodMk hnoise
  have hprefixJoined : Measurable[MeasurableSpace.comap joined inferInstance]
      prefixMap :=
    measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)
  have hnoiseJoined : Measurable[MeasurableSpace.comap joined inferInstance]
      noise :=
    measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl)
  obtain ⟨nonrefreshRep, hnonrefreshRepMeas, hnonrefreshAe⟩ :=
    ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
      (MeasurableSpace.comap joined inferInstance) prefixMap prefixMap noise
      (fun pref q ↦ ‖direction pref + innovationKernel pref q‖ ^ 2) law
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law))
      hjJoined.comap_le hprefixJoined hnoiseJoined
      (Filter.Eventually.of_forall fun _ ↦ rfl) hfresh
      (by simpa [hprefixLaw, hnoiseLaw] using hnonrefreshKernel)
  have hrepIndep : ProbabilityTheory.IndepFun nonrefreshRep branch law := by
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap joined inferInstance)
        (MeasurableSpace.comap branch inferInstance) law := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hjointBranch
    exact indepFun_of_measurable_left_of_indep_comap
      hnonrefreshRepMeas.measurable hcomap
  have hnonrefreshComp : ∀ path,
      ‖direction (prefixMap path) + innovationKernel (prefixMap path) (noise path)‖ ^ 2 =
        ‖residual path + innovation path‖ ^ 2 := by
    intro path
    rw [hinnovationComp path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hnonrefreshIndep : ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) branch law := by
    apply hrepIndep.congr ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [hnonrefreshAe] with path hp
    exact hp.symm.trans (hnonrefreshComp path)
  exact hnonrefreshIndep

set_option maxHeartbeats 3000000 in
/-- Complete proof-exact Eq. (46) at one time under literal source
moments, law-a.e. genuine generated-query Assumption 3.2, and the weak law-level
Track-B correction.  The two branch moments are gated by the actual current
Bernoulli refresh coin; current error and step integrability are induction
inputs, while successor error integrability is proved here. -/
theorem online_estimator_recurrence_46_proof_exact_of_literal_and_lawRegularityAE
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
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
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  have hRefresh :=
    onlineProofExact_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
      A x0 hBatch σ hLiteral hRegularity hSmooth.1 k
  have hRefreshIndep :=
    onlineProofExact_refresh_error_sq_indep_refresh_of_lawRegularity
      A x0 hBatch hRegularity k
  have hNonrefresh :=
    onlineProofExact_nonrefresh_branch_moments_of_genuine_assumption32AE_and_lawRegularity
      A x0 Llocal ℒlocal ω hSmooth hBatch hAssumption32 hRegularity
        hQuantizer k hError hStep
  have hNonrefreshIndep :=
    onlineProofExact_nonrefresh_error_sq_indep_refresh_of_lawRegularity
      A x0 hBatch hRegularity k
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
  let refreshError := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
      stochasticGradient A.problem i ((path k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1
  let refreshSq := fun path ↦ ‖refreshError path‖ ^ 2
  let nonrefreshSq := fun path ↦ ‖residual path + innovation path‖ ^ 2
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n ↦
      A.quantizer.apply
        (onlineBatchDifference A.problem (path k).2.1.2 i xN s.x)
        ((path k).2.2 i)
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
          onlineWorkerEstimator A (onlineDriverOfRoundNoise (path k)) s i) -
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
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hbranchMeas : Measurable branch := by dsimp [branch]; fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    calc
      Measure.map branch law = Measure.map Prod.fst
          (Measure.map (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k)
            law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_fst
              · exact measurable_pi_apply k
      _ = Measure.map Prod.fst (onlineRoundLaw A) := by
            rw [show Measure.map
                (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k) law =
                onlineRoundLaw A by
              simpa [law, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
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
              hNonrefresh.2.2
          · exact sub_nonneg.mpr A.refresh_admissible.2
      _ = (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
        ring

set_option maxHeartbeats 3000000 in
/-- Simultaneous proof-exact component `L²` closure and Eq. (46) history
from the source-faithful law-a.e. Assumption 3.2 boundary.  This is the scalar
induction consumed by D.3 and D.4; it never reconstructs genuine-gradient
witnesses on paths of zero `onlineProofExactPathLaw` measure. -/
theorem
    onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE_core
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hStateSource : ∀ t, AEMeasurable
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch t)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A))
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
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
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
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
  have hState (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using hStateSource t
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
        have hx : AEStronglyMeasurable (fun path ↦ (run 0 path).x) law :=
          ((measurable_state_x d).comp_aemeasurable (hState 0)).aestronglyMeasurable
        have hr : AEStronglyMeasurable
            (fun path ↦ (run 0 path).g - globalGradient P (run 0 path).x) law := by
          have heq : (fun path ↦
              (run 0 path).g - globalGradient P (run 0 path).x) =
              (fun _ ↦ (0 : Point d)) := by
            funext path
            change globalGradient P x0 - globalGradient P x0 = 0
            simp
          rw [heq]
          exact aestronglyMeasurable_const
        have hxl2 : Integrable (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) law := by
          have heq : (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) =
              (fun _ ↦ (0 : ℝ)) := by
            funext path
            change ‖x0 - x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (μ := law) (c := (0 : ℝ))
        have hgl2 : Integrable (fun path ↦ ‖(run 0 path).g‖ ^ 2) law := by
          have heq : (fun path ↦ ‖(run 0 path).g‖ ^ 2) =
              (fun _ ↦ ‖globalGradient P x0‖ ^ 2) := by
            funext path
            rfl
          rw [heq]
          exact integrable_const (μ := law) (c := ‖globalGradient P x0‖ ^ 2)
        have he : EstimatorErrorMomentWellDefined P run law 0 := by
          rw [EstimatorErrorMomentWellDefined]
          have heq : (fun path ↦
              ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
              (fun _ ↦ (0 : ℝ)) := by
            funext path
            change ‖globalGradient P x0 - globalGradient P x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (μ := law) (c := (0 : ℝ))
        have hs : StepMomentWellDefined run law 0 := by
          have heq : (fun path ↦ ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
              (fun _ ↦ ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2) := by
            funext path
            change ‖(x0 - (A.stepSize : ℝ) • globalGradient P x0) - x0‖ ^ 2 = _
            congr 2
            rw [neg_smul]
            abel
          rw [StepMomentWellDefined, heq]
          exact integrable_const (μ := law)
            (c := ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2)
        refine ⟨hx, hr, hxl2, hgl2, he, hs, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        have hRec :=
          online_estimator_recurrence_46_proof_exact_of_literal_and_lawRegularityAE
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
          simpa [run, onlineProofExactProcess_succ, onlineStep,
            primalStep_eq] using h
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
          simpa [StepMomentWellDefined, run, onlineProofExactProcess_succ,
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

/-- Compatibility form of the scalar closure.  It retains the established
law-regularity interface while delegating state measurability to that
interface explicitly. -/
theorem
    onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
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
  apply
    onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE_core
      A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
        hAssumption32 hRegularity
  intro t
  exact onlineProofExactProcess_aemeasurable_of_lawRegularity
    A x0 hBatch hRegularity t

/-- Source-kernel form of the same scalar closure.  The recurrence helpers
remain compatible with the narrower law-regularity route, but the complete
state-measurability subcone is now discharged directly from the generated
Assumption 3.2 kernel and positive Algorithm 3 step. -/
theorem
    onlineProofExactProcess_scalar_recurrence_components_of_literal_and_generatedKernel_and_lawRegularityAE
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
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
  apply
    onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE_core
      A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
        (onlineAssumption32GeneratedConditionalKernel_to_genuineAE hKernel)
        hRegularity
  intro t
  exact onlineProofExactProcess_aemeasurable_of_generatedConditionalKernel
    A x0 hBatch ℒlocal hKernel t

/-- Theorem D.3 at the source-faithful public boundary.  Assumption 3.2 is
conditional under the exact generated proof-exact law, literal Assumption 3.3
is exposed separately from the Track-B law regularity correction, and the
conclusion is the original uniform-output object. -/
theorem Theorem_D3_online_VR_nonconvex_source_boundary_of_lawRegularityAE
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    Integrable (fun z ↦
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
  apply onlineProofExactD3_of_scalar_recurrence_components
    A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hQuantizer hBatch
  · intro k
    exact
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_generatedKernel_and_lawRegularityAE
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          hKernel hRegularity k
  · exact hStep

/-- Compatibility supplier for callers that still have the former every-path
Assumption 3.2 formulation.  The public source boundary above remains law-a.e. -/
theorem Theorem_D3_online_VR_nonconvex_source_boundary_of_forallPath
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    Integrable (fun z ↦
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
  apply onlineProofExactD3_of_scalar_recurrence_components
    A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hQuantizer hBatch
  · intro k
    exact
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          (onlineAssumption32GenuineAE_of_forallPath A.problem
            (onlineProofExactProcess A x0 hBatch)
            (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal
            hAssumption32)
          hRegularity k
  · exact hStep

/-- Theorem D.4 at the source-faithful law-a.e. Assumption 3.2 boundary.  Its
measured object is the last proof-exact iterate under the exact proof law. -/
theorem Theorem_D4_online_VR_PL_source_boundary_of_lawRegularityAE
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path ↦
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
  apply onlineProofExactD4_of_scalar_recurrence_components
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hPL hQuantizer hBatch
  · intro k
    exact
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_generatedKernel_and_lawRegularityAE
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          hKernel hRegularity k
  · exact hStep

/-- Compatibility supplier for the former every-path Assumption 3.2 premise. -/
theorem Theorem_D4_online_VR_PL_source_boundary_of_forallPath
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path ↦
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
  apply onlineProofExactD4_of_scalar_recurrence_components
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hPL hQuantizer hBatch
  · intro k
    exact
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularityAE
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          (onlineAssumption32GenuineAE_of_forallPath A.problem
            (onlineProofExactProcess A x0 hBatch)
            (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal
            hAssumption32)
          hRegularity k
  · exact hStep

/-! ## Generated-kernel worker-row transfer

The source conditional kernel is jointly measurable on the generated path and
the complete difference minibatch.  The sharp `1 / n` nonrefresh calculation
also needs each worker contribution on its own independent row law.  The next
lemma performs exactly that disintegration; it does not quantify over any
unrelated query law and uses no adaptive-gradient regularity predicate. -/

/-- For almost every generated path, the actual worker minibatch difference is
a random vector on that worker's canonical iid row law.  Both generated
queries, the worker, the batch size, and the sample law are unchanged from the
source conditional kernel. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_workerRowDifference_aestronglyMeasurable_ae
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {ℒ : Worker n → ℝ}
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ)
    (k : ℕ) (i : Worker n) :
    ∀ᵐ path ∂pathLaw,
      AEStronglyMeasurable
        (fun row : Fin b0.1 → Sample i ↦
          average (fun j : Fin b0.1 ↦
            stochasticGradient P i (row j) (run (k + 1) path).x -
              stochasticGradient P i (row j) (run k path).x))
        (Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw i)) := by
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure
      (Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw i)) := by
    infer_instance
  have hFull :=
    onlineAssumption32GeneratedConditionalKernel_batchDifference_joint_aestronglyMeasurable
      hKernel k i
  have hRow : AEStronglyMeasurable
      (fun p : Omega × (Fin b0.1 → Sample i) ↦
        average (fun j : Fin b0.1 ↦
          stochasticGradient P i (p.2 j) (run (k + 1) p.1).x -
            stochasticGradient P i (p.2 j) (run k p.1).x))
      (pathLaw.prod (Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw i))) := by
    apply aestronglyMeasurable_worker_row_of_onlineBatchLaw P pathLaw i
      (fun path row ↦ average (fun j : Fin b0.1 ↦
        stochasticGradient P i (row j) (run (k + 1) path).x -
          stochasticGradient P i (row j) (run k path).x))
    simpa [onlineBatchDifference] using hFull
  exact hRow.prodMk_left

/-- Simultaneous finite-worker form of the preceding row transfer.  This is
the exact measurable-row family needed by the independent-worker covariance
sum in the sharp nonrefresh second-moment calculation. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_allWorkerRowDifferences_aestronglyMeasurable_ae
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {ℒ : Worker n → ℝ}
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ)
    (k : ℕ) :
    ∀ᵐ path ∂pathLaw, ∀ i : Worker n,
      AEStronglyMeasurable
        (fun row : Fin b0.1 → Sample i ↦
          average (fun j : Fin b0.1 ↦
            stochasticGradient P i (row j) (run (k + 1) path).x -
              stochasticGradient P i (row j) (run k path).x))
        (Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw i)) := by
  apply ae_all_iff.2
  intro i
  exact
    onlineAssumption32GeneratedConditionalKernel_workerRowDifference_aestronglyMeasurable_ae
      hKernel k i

set_option maxHeartbeats 2000000 in
/-- The literal Assumption 3.2 worker-row innovation calculation needs only
measurability of the actual generated worker row, rather than the much
stronger every-query-law regularity predicate.  The full-minibatch fiber
continues to supply integrability, centering, and the source second-moment
bound; `hRowMeasurable` only permits those facts to be transported to the
canonical independent worker row used by the sharp covariance sum. -/
theorem
    onlineFixed_nonrefresh_worker_row_moment_of_assumption32_and_rowMeasurability
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (xNext x : Point d) (i : Worker n) (Llocal ℒlocal : Worker n → ℝ)
    (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAverageFiber :
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let D := fun batch ↦ onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch ↦ ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hRowMeasurable : AEStronglyMeasurable
      (fun row : Fin b0.1 → Sample i ↦
        average (fun j : Fin b0.1 ↦
          stochasticGradient A.problem i (row j) xNext -
            stochasticGradient A.problem i (row j) x))
      (Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)))
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let rowBatchLaw :=
      Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)
    let rowLaw := rowBatchLaw.prod A.quantizer.law
    let delta := localGradientDifference
      (onlineLocalProblem A.problem) i xNext x
    let innovation := fun q : (Fin b0.1 → Sample i) × Ξ ↦
      A.quantizer.apply
          (average (fun j : Fin b0.1 ↦
            stochasticGradient A.problem i (q.1 j) xNext -
              stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
    Integrable innovation rowLaw ∧
      Integrable (fun q ↦ ‖innovation q‖ ^ 2) rowLaw ∧
      (∫ q, innovation q ∂rowLaw) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  classical
  let batchLaw := onlineBatchLaw A.problem b0
  let rowBatchLaw :=
    Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)
  let fullLaw := batchLaw.prod A.quantizer.law
  let rowLaw := rowBatchLaw.prod A.quantizer.law
  let delta := localGradientDifference
    (onlineLocalProblem A.problem) i xNext x
  let localD := fun row : Fin b0.1 → Sample i ↦
    average (fun j : Fin b0.1 ↦
      stochasticGradient A.problem i (row j) xNext -
        stochasticGradient A.problem i (row j) x)
  let innovation := fun q : (Fin b0.1 → Sample i) × Ξ ↦
    A.quantizer.apply (localD q.1) q.2 - delta
  let project := fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
    (q.1 i, q.2)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure rowBatchLaw := by
    dsimp [rowBatchLaw]
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure fullLaw := by
    dsimp [fullLaw]
    infer_instance
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    infer_instance
  have hproject : Measurable project := by
    dsimp [project]
    fun_prop
  have hmap : Measure.map project fullLaw = rowLaw := by
    change Measure.map project fullLaw = rowLaw
    rw [show project = Prod.map
        (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i) id by
      funext q
      rfl]
    dsimp [fullLaw, rowLaw]
    rw [← Measure.map_prod_map batchLaw A.quantizer.law
      (measurable_pi_apply i) measurable_id]
    rw [onlineBatchLaw_worker_marginal A.problem i, Measure.map_id]
  have hD : AEStronglyMeasurable localD rowBatchLaw := by
    simpa [localD, rowBatchLaw] using hRowMeasurable
  let localDMk := hD.mk localD
  have hlocalDMk : Measurable localDMk := hD.measurable_mk
  have hinnovation : AEStronglyMeasurable innovation rowLaw := by
    have hm : Measurable (fun q : (Fin b0.1 → Sample i) × Ξ ↦
        A.quantizer.apply (localDMk q.1) q.2 - delta) :=
      (A.quantizer.measurable_apply_uncurry.comp
        ((hlocalDMk.comp measurable_fst).prodMk measurable_snd)).sub
          measurable_const
    refine hm.aestronglyMeasurable.congr ?_
    have hae : (fun q : (Fin b0.1 → Sample i) × Ξ ↦ localD q.1) =ᵐ[rowLaw]
        (fun q ↦ localDMk q.1) := by
      exact (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := rowBatchLaw) (ν := A.quantizer.law)).tendsto_ae hD.ae_eq_mk
    filter_upwards [hae] with q hq
    simp only [innovation]
    rw [hq]
  have hfull := onlineFixed_nonrefresh_worker_moment_of_assumption32
    (b0 := b0) A xNext x i Llocal ℒlocal ω hSmooth hAverageFiber hQuantizer
  have hcomp : innovation ∘ project =
      fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta := by
    funext q
    rfl
  have hinnovationMap : AEStronglyMeasurable innovation
      (Measure.map project fullLaw) := by
    rw [hmap]
    exact hinnovation
  have hvecMap : Integrable innovation (Measure.map project fullLaw) := by
    apply (MeasureTheory.integrable_map_measure hinnovationMap
      hproject.aemeasurable).mpr
    rw [hcomp]
    simpa [fullLaw, batchLaw, delta] using hfull.1
  have hsqMap : Integrable (fun q ↦ ‖innovation q‖ ^ 2)
      (Measure.map project fullLaw) := by
    apply (MeasureTheory.integrable_map_measure (hinnovationMap.norm.pow 2)
      hproject.aemeasurable).mpr
    change Integrable
      (fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
        ‖A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta‖ ^ 2)
      fullLaw
    simpa [fullLaw, batchLaw, delta] using hfull.2.1
  have hmean : (∫ q, innovation q ∂rowLaw) = 0 := by
    calc
      (∫ q, innovation q ∂rowLaw) =
          ∫ q, innovation q ∂Measure.map project fullLaw := by rw [hmap]
      _ = ∫ q, innovation (project q) ∂fullLaw :=
        MeasureTheory.integral_map hproject.aemeasurable hinnovationMap
      _ = 0 := by
        change (∫ q,
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta
            ∂fullLaw) = 0
        simpa [fullLaw, batchLaw, delta] using hfull.2.2.1
  have hsecond : (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
      (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
        ‖xNext - x‖ ^ 2 := by
    calc
      (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) =
          ∫ q, ‖innovation q‖ ^ 2 ∂Measure.map project fullLaw := by
            rw [hmap]
      _ = ∫ q, ‖innovation (project q)‖ ^ 2 ∂fullLaw :=
        MeasureTheory.integral_map hproject.aemeasurable
          (hinnovationMap.norm.pow 2)
      _ ≤ _ := by
        change (∫ q,
          ‖A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta‖ ^ 2
            ∂fullLaw) ≤ _
        simpa [fullLaw, batchLaw, delta] using hfull.2.2.2
  exact ⟨by simpa [hmap] using hvecMap, by simpa [hmap] using hsqMap,
    hmean, hsecond⟩

/-- Generated-kernel specialization of the preceding worker-row moment.
For almost every actual generated path it supplies row integrability, zero
conditional mean, and the sharp workerwise second moment without
`OnlineAdaptiveSampleGradientLawRegularity`. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_workerRowInnovation_moment_ae
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*} {Ξ : Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (run : ℕ → Omega → State d)
    (pathLaw : Measure Omega) [SFinite pathLaw]
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem run pathLaw ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    ∀ᵐ path ∂pathLaw,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let rowBatchLaw :=
        Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)
      let rowLaw := rowBatchLaw.prod A.quantizer.law
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let innovation := fun q : (Fin b0.1 → Sample i) × Ξ ↦
        A.quantizer.apply
            (average (fun j : Fin b0.1 ↦
              stochasticGradient A.problem i (q.1 j) xNext -
                stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
      Integrable innovation rowLaw ∧
        Integrable (fun q ↦ ‖innovation q‖ ^ 2) rowLaw ∧
        (∫ q, innovation q ∂rowLaw) = 0 ∧
        (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2 := by
  have hAverage :=
    onlineAssumption32GeneratedConditionalKernel_to_averageSmoothnessAE hKernel
  have hRow :=
    onlineAssumption32GeneratedConditionalKernel_workerRowDifference_aestronglyMeasurable_ae
      hKernel k i
  filter_upwards [hAverage.2 k, hRow] with path hFiber hMeasurable
  dsimp only
  apply
    onlineFixed_nonrefresh_worker_row_moment_of_assumption32_and_rowMeasurability
      A (run (k + 1) path).x (run k path).x i Llocal ℒlocal ω hSmooth
        (hFiber i) _ hQuantizer
  letI : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  rw [Measure.infinitePi_eq_pi]
  exact hMeasurable

/-- Finite-worker simultaneous form of the generated row moments.  This is
the exact family needed next for the independent-worker covariance sum. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_allWorkerRowInnovation_moments_ae
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*} {Ξ : Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (run : ℕ → Omega → State d)
    (pathLaw : Measure Omega) [SFinite pathLaw]
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem run pathLaw ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) :
    ∀ᵐ path ∂pathLaw, ∀ i : Worker n,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let rowBatchLaw :=
        Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)
      let rowLaw := rowBatchLaw.prod A.quantizer.law
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let innovation := fun q : (Fin b0.1 → Sample i) × Ξ ↦
        A.quantizer.apply
            (average (fun j : Fin b0.1 ↦
              stochasticGradient A.problem i (q.1 j) xNext -
                stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
      Integrable innovation rowLaw ∧
        Integrable (fun q ↦ ‖innovation q‖ ^ 2) rowLaw ∧
        (∫ q, innovation q ∂rowLaw) = 0 ∧
        (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2 := by
  apply ae_all_iff.2
  intro i
  exact
    onlineAssumption32GeneratedConditionalKernel_workerRowInnovation_moment_ae
      A run pathLaw Llocal ℒlocal ω hSmooth hKernel hQuantizer k i

set_option maxHeartbeats 2000000 in
/-- The independent-worker covariance calculation needs only the canonical
worker-row moments.  Unlike the historical fixed-query wrapper, this theorem
does not reconstruct row measurability from an every-query-law regularity
predicate: its premise is exactly the finite family of row facts supplied by
the generated conditional kernel above. -/
theorem onlineFixed_nonrefresh_average_moment_of_workerRowMoments
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (xNext x : Point d) (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hRows : ∀ i : Worker n,
      let rowLaw :=
        (Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)).prod
          A.quantizer.law
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let innovation := fun q : (Fin b0.1 → Sample i) × Ξ ↦
        A.quantizer.apply
            (average (fun j : Fin b0.1 ↦
              stochasticGradient A.problem i (q.1 j) xNext -
                stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
      Integrable innovation rowLaw ∧
        Integrable (fun q ↦ ‖innovation q‖ ^ 2) rowLaw ∧
        (∫ q, innovation q ∂rowLaw) = 0 ∧
        (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2) :
    let law := onlineDifferenceCompressionLaw (b0 := b0) A
    let innovation := fun i : Worker n ↦
      fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
          localGradientDifference (onlineLocalProblem A.problem) i xNext x
    Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
      Integrable (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  classical
  let law := onlineDifferenceCompressionLaw (b0 := b0) A
  let source := fun i : Worker n ↦
    fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
      (q.1 i, q.2 i)
  let rowLaw := fun i : Worker n ↦
    (Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)).prod
      A.quantizer.law
  let localInnovation := fun i : Worker n ↦
    fun q : (Fin b0.1 → Sample i) × Ξ ↦
      A.quantizer.apply
        (average (fun j : Fin b0.1 ↦
          stochasticGradient A.problem i (q.1 j) xNext -
            stochasticGradient A.problem i (q.1 j) x)) q.2 -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x
  let innovation := fun i : Worker n ↦
    fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineDifferenceCompressionLaw
    infer_instance
  have hsource : ∀ i : Worker n, Measurable (source i) := by
    intro i
    dsimp [source]
    fun_prop
  have hmap : ∀ i : Worker n, Measure.map (source i) law = rowLaw i := by
    intro i
    simpa [source, law, rowLaw] using
      onlineDifferenceCompressionLaw_worker_marginal (b0 := b0) A i
  have hlocal : ∀ i : Worker n,
      Integrable (localInnovation i) (rowLaw i) ∧
      Integrable (fun q ↦ ‖localInnovation i q‖ ^ 2) (rowLaw i) ∧
      (∫ q, localInnovation i q ∂rowLaw i) = 0 ∧
      (∫ q, ‖localInnovation i q‖ ^ 2 ∂rowLaw i) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
    intro i
    simpa [localInnovation, rowLaw] using hRows i
  have hcomp : ∀ i : Worker n,
      localInnovation i ∘ source i = innovation i := by
    intro i
    funext q
    rfl
  have hdiag : ∀ i : Worker n,
      Integrable (fun q ↦ ‖innovation i q‖ ^ 2) law ∧
      (∫ q, ‖innovation i q‖ ^ 2 ∂law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
    intro i
    have hsqaesm : AEStronglyMeasurable
        (fun q ↦ ‖localInnovation i q‖ ^ 2) (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hlocal i).2.1.aestronglyMeasurable
    constructor
    · have honMap : Integrable (fun q ↦ ‖localInnovation i q‖ ^ 2)
          (Measure.map (source i) law) := by
        simpa only [hmap i] using (hlocal i).2.1
      have hpull : Integrable
          ((fun q ↦ ‖localInnovation i q‖ ^ 2) ∘ source i) law :=
        (MeasureTheory.integrable_map_measure hsqaesm
          (hsource i).aemeasurable).mp honMap
      simpa [Function.comp_def, ← hcomp i] using hpull
    · have hInt :
          (∫ q, ‖localInnovation i (source i q)‖ ^ 2 ∂law) =
            ∫ q, ‖localInnovation i q‖ ^ 2
              ∂Measure.map (source i) law := by
        rw [MeasureTheory.integral_map (hsource i).aemeasurable hsqaesm]
      change (∫ q, ‖localInnovation i (source i q)‖ ^ 2 ∂law) ≤ _
      rw [hInt, hmap i]
      exact (hlocal i).2.2.2
  have hvec : ∀ i : Worker n,
      Integrable (innovation i) law ∧ (∫ q, innovation i q ∂law) = 0 := by
    intro i
    have hlocalOnMap : Integrable (localInnovation i)
        (Measure.map (source i) law) := by
      simpa only [hmap i] using (hlocal i).1
    have hlocalAesm : AEStronglyMeasurable (localInnovation i)
        (Measure.map (source i) law) := hlocalOnMap.aestronglyMeasurable
    have hpull : Integrable (localInnovation i ∘ source i) law :=
      (MeasureTheory.integrable_map_measure hlocalAesm
        (hsource i).aemeasurable).mp hlocalOnMap
    constructor
    · simpa [← hcomp i] using hpull
    · change (∫ q, (localInnovation i ∘ source i) q ∂law) = 0
      have hInt := (MeasureTheory.integral_map
        (hsource i).aemeasurable hlocalAesm).symm
      rw [show (∫ q, (localInnovation i ∘ source i) q ∂law) =
          ∫ q, localInnovation i q ∂Measure.map (source i) law by
        simpa [Function.comp_def] using hInt,
        hmap i]
      exact (hlocal i).2.2.1
  have hindep := onlineDifferenceCompressionLaw_worker_iIndep (b0 := b0) A
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) = 0 := by
    intro i j hij
    let fi := localInnovation i
    let fj := localInnovation j
    let fiMk := (hlocal i).1.aestronglyMeasurable.mk fi
    let fjMk := (hlocal j).1.aestronglyMeasurable.mk fj
    have hfiMk : Measurable fiMk :=
      (hlocal i).1.aestronglyMeasurable.measurable_mk
    have hfjMk : Measurable fjMk :=
      (hlocal j).1.aestronglyMeasurable.measurable_mk
    have hfi_ae : fi =ᵐ[rowLaw i] fiMk :=
      (hlocal i).1.aestronglyMeasurable.ae_eq_mk
    have hfj_ae : fj =ᵐ[rowLaw j] fjMk :=
      (hlocal j).1.aestronglyMeasurable.ae_eq_mk
    have hqmpi : Measure.QuasiMeasurePreserving (source i) law (rowLaw i) :=
      ⟨hsource i, by rw [hmap i]⟩
    have hqmpj : Measure.QuasiMeasurePreserving (source j) law (rowLaw j) :=
      ⟨hsource j, by rw [hmap j]⟩
    have hfi_pull : (fi ∘ source i) =ᵐ[law] (fiMk ∘ source i) :=
      hqmpi.tendsto_ae hfi_ae
    have hfj_pull : (fj ∘ source j) =ᵐ[law] (fjMk ∘ source j) :=
      hqmpj.tendsto_ae hfj_ae
    have hfi_global : innovation i =ᵐ[law] fiMk ∘ source i := by
      rw [← hcomp i]
      simpa [fi] using hfi_pull
    have hfj_global : innovation j =ᵐ[law] fjMk ∘ source j := by
      rw [← hcomp j]
      simpa [fj] using hfj_pull
    have hfixed_int : ∀ _ : (Fin b0.1 → Sample j) × Ξ,
        Integrable (fun s ↦ fiMk s) (rowLaw i) := by
      intro _
      exact (hlocal i).1.congr hfi_ae
    have hfixed_zero : ∀ _ : (Fin b0.1 → Sample j) × Ξ,
        (∫ s, fiMk s ∂rowLaw i) = 0 := by
      intro _
      rw [← integral_congr_ae hfi_ae]
      exact (hlocal i).2.2.1
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
  have hmeas : ∀ i : Worker n, AEStronglyMeasurable (innovation i) law := by
    intro i
    exact (hvec i).1.aestronglyMeasurable
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    law (Finset.univ : Finset (Worker n)) innovation
      (fun i _ ↦ hmeas i) (fun i _ ↦ (hdiag i).1)
      (fun i _ j _ hij ↦ hcross hij)
  have havg_int : Integrable
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
  have havg_vec : Integrable
      (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law := by
    unfold average SOptLib.finiteUniformAverage
    simpa [Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ ↦ (hvec i).1)).smul ((n.1 : ℝ)⁻¹)
  have havg_zero :
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 := by
    unfold average SOptLib.finiteUniformAverage
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun i _ ↦ (hvec i).1)]
    simp [hvec]
  refine ⟨by simpa [innovation, law] using havg_vec,
    by simpa [innovation, law] using havg_zero,
    by simpa [innovation, law] using havg_int, ?_⟩
  have hcoeff_sum :
      (∑ i : Worker n,
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1)) =
      ω * ∑ i : Worker n, (Llocal i) ^ 2 +
        ((1 + ω) / b0.1) * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    calc
      _ = (∑ i : Worker n, ω * (Llocal i) ^ 2) +
          ∑ i : Worker n, ((1 + ω) / b0.1) * (ℒlocal i) ^ 2 := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have hmean_L : 0 ≤ meanSquare Llocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hmean_A : 0 ≤ meanSquare ℒlocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hrms_L : (rootMeanSquare Llocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (Llocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_L]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hrms_A : (rootMeanSquare ℒlocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_A]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
  have hb : (b0.1 : ℝ) ≠ 0 := by exact_mod_cast b0.2.ne'
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
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n,
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2 := by
      gcongr with i
      exact (hdiag i).2
    _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
      rw [← Finset.sum_mul, hcoeff_sum, hrms_L, hrms_A]
      field_simp [hn, hb]

/-- Generated-kernel specialization of the independent-worker aggregation.
For almost every actual generated path, it supplies the centered averaged
nonrefresh innovation and the sharp source `1 / n` second-moment bound with
no `OnlineAdaptiveSampleGradientLawRegularity` premise. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_moment_ae
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*} {Ξ : Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (run : ℕ → Omega → State d)
    (pathLaw : Measure Omega) [SFinite pathLaw]
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem run pathLaw ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) :
    ∀ᵐ path ∂pathLaw,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let law := onlineDifferenceCompressionLaw (b0 := b0) A
      let innovation := fun i : Worker n ↦
        fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
            localGradientDifference (onlineLocalProblem A.problem) i xNext x
      Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
        (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
        Integrable
          (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2) law ∧
        (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2 := by
  have hRows :=
    onlineAssumption32GeneratedConditionalKernel_allWorkerRowInnovation_moments_ae
      A run pathLaw Llocal ℒlocal ω hSmooth hKernel hQuantizer k
  filter_upwards [hRows] with path hp
  dsimp only at hp ⊢
  exact onlineFixed_nonrefresh_average_moment_of_workerRowMoments
    A (run (k + 1) path).x (run k path).x Llocal ℒlocal ω hp

/- The preceding generated-kernel bound is naturally measurable only on the
strict-prefix carrier.  This small variant of the existing independent-fiber
transport permits an a.e.-strongly measurable bound on that carrier. -/
theorem
    integrable_comp_and_integral_le_of_indep_ae_fixed_fiber_aebound
    {Omega W S : Type*} [MeasurableSpace Omega] [MeasurableSpace W]
    [MeasurableSpace S] {mu : Measure Omega} {nu : Measure S}
    [IsFiniteMeasure mu] [SFinite nu]
    (phi : W → S → ℝ) (B : W → ℝ) (X : Omega → W) (Y : Omega → S)
    (hphi : AEStronglyMeasurable (fun p : W × S ↦ phi p.1 p.2)
      ((Measure.map X mu).prod nu))
    (hB : AEStronglyMeasurable B (Measure.map X mu))
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
  let BM := hB.mk B
  have hBM : StronglyMeasurable BM := hB.stronglyMeasurable_mk
  have hBeq : B =ᵐ[Measure.map X mu] BM := hB.ae_eq_mk
  have hBeqComp : (fun omega ↦ B (X omega)) =ᵐ[mu]
      (fun omega ↦ BM (X omega)) :=
    MeasureTheory.ae_of_ae_map hX hBeq
  have hfixedM : ∀ᵐ omega ∂mu,
      Integrable (phi (X omega)) nu ∧
        (∫ s, phi (X omega) s ∂nu) ≤ BM (X omega) := by
    filter_upwards [hfixed, hBeqComp] with omega hmoment heq
    exact ⟨hmoment.1, hmoment.2.trans_eq heq⟩
  have hBMComp : Integrable (fun omega ↦ BM (X omega)) mu :=
    hBComp.congr hBeqComp
  have hcore := integrable_comp_and_integral_le_of_indep_ae_fixed_fiber
    phi BM X Y hphi hBM hX hY hindep hYLaw hfixedM hnonneg hBMComp
  refine ⟨hcore.1, hcore.2.trans_eq ?_⟩
  exact integral_congr_ae hBeqComp.symm

set_option maxHeartbeats 8000000 in
/- The generated Assumption 3.2 kernel controls the actual fresh
nonrefresh innovation of proof-exact Algorithm 3.  The strict prefix is the
independent carrier, while the current difference batch and compressor are
the fresh coordinate.  Thus the theorem transports the exact generated
object without `OnlineAdaptiveSampleGradientLawRegularity`. -/
theorem
    onlineProofExact_nonrefresh_innovation_second_moment_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
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
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((path k).2.1.2, (path k).2.2)
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let xNext := fun pref ↦ primalStep A.stepSize (prefixState pref)
  let x := fun pref ↦ (prefixState pref).x
  let kernel := fun pref ↦
      fun q : ((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
              (q.2 i) -
            localGradientDifference P i (xNext pref) (x pref))
  let B := fun pref ↦ C * ‖xNext pref - x pref‖ ^ 2
  let phi := fun pref q ↦ ‖kernel pref q‖ ^ 2
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    simpa [law, roundLaw, prefixMap, prefixLaw,
      onlineProofExactPathLaw, onlineRoundPrefix, SOptLib.iidStreamLaw] using
      (iidStream_prefix_map_eq_infinitePi
        (onlineRoundLaw (b := b) (b0 := b0) A) k)
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hcurrent : Measurable current := measurable_pi_apply k
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · rw [← hprefixLaw]
      simpa [law, roundLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefix, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [noise, current, Function.comp_def] using
      hpastCurrent.comp measurable_id
        (show Measurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2)) by
            fun_prop)
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          roundLaw := by
            rw [show Measure.map current law = roundLaw by
              simpa [current, law, roundLaw, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = noiseLaw := by
        simpa [roundLaw, noiseLaw] using
          onlineRoundLaw_differenceCompression_marginal
            (b := b) (b0 := b0) A
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProofExactProcess_congr_prefix
      A x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback
        (onlineRoundPrefix k path))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hsource :=
    onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_joint_aestronglyMeasurable
      A run law ℒlocal hKernel k
  have hprefixComp :
      (fun z :
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
        kernel (fun j : Fin k ↦ z.2 j.1) z.1) =
      (fun z ↦ average (fun i : Worker n ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem z.1.1 i
              (run (k + 1) z.2).x (run k z.2).x)
            (z.1.2 i) -
          localGradientDifference P i
            (run (k + 1) z.2).x (run k z.2).x)) := by
    funext z
    have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := z.2)
      (path' := onlineExtendRoundPrefix fallback (fun j : Fin k ↦ z.2 j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])
    have hps : prefixState (fun j : Fin k ↦ z.2 j.1) = run k z.2 := by
      exact hs.symm
    dsimp [kernel, xNext, x]
    rw [hps]
    rfl
  have hfullSwap : AEStronglyMeasurable
      (fun z :
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
        kernel (fun j : Fin k ↦ z.2 j.1) z.1)
      (noiseLaw.prod law) := by
    rw [hprefixComp]
    have hs := hsource.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := noiseLaw) (ν := law))
    simpa using hs
  have hfiniteSwap : AEStronglyMeasurable
      (fun z :
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ×
            (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
        kernel z.2 z.1)
      (noiseLaw.prod prefixLaw) := by
    exact aestronglyMeasurable_initial_prefix_of_comp_general
      noiseLaw roundLaw k (fun z ↦ kernel z.2 z.1) hfullSwap
  have hkernel : AEStronglyMeasurable (Function.uncurry kernel)
      (prefixLaw.prod noiseLaw) := by
    have hs := hfiniteSwap.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixLaw) (ν := noiseLaw))
    simpa [Function.uncurry] using hs
  have hphi : AEStronglyMeasurable (Function.uncurry phi)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    rw [hprefixLaw]
    simpa [phi, Function.uncurry, pow_two] using hkernel.norm.mul hkernel.norm
  have hxPrefix : AEStronglyMeasurable x prefixLaw := by
    have hpair := hKernel.2.1 k
    have hfull : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
      (measurable_fst.comp_aemeasurable hpair.aemeasurable)
        |>.aestronglyMeasurable
    apply aestronglyMeasurable_prefix_of_comp_general roundLaw k x
    refine hfull.congr (Filter.Eventually.of_forall ?_)
    intro path
    have hs := congrArg (fun s : State d ↦ s.x) (hstatePrefix path).symm
    simpa [x, prefixMap, onlineRoundPrefix] using hs
  have hxNextPrefix : AEStronglyMeasurable xNext prefixLaw := by
    have hpair := hKernel.2.1 k
    have hfull : AEStronglyMeasurable (fun path ↦ (run (k + 1) path).x) law :=
      (measurable_snd.comp_aemeasurable hpair.aemeasurable)
        |>.aestronglyMeasurable
    apply aestronglyMeasurable_prefix_of_comp_general roundLaw k xNext
    refine hfull.congr (Filter.Eventually.of_forall ?_)
    intro path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    simpa [prefixMap, onlineRoundPrefix] using hnext.symm
  have hB : AEStronglyMeasurable B (Measure.map prefixMap law) := by
    rw [hprefixLaw]
    dsimp [B]
    have hd := hxNextPrefix.sub hxPrefix
    simpa [pow_two] using (hd.norm.mul hd.norm).const_mul C
  have hMomentPath : ∀ᵐ path ∂law,
      Integrable (phi (prefixMap path)) noiseLaw ∧
        (∫ q, phi (prefixMap path) q ∂noiseLaw) ≤ B (prefixMap path) := by
    have hm :=
      onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_moment_ae
        A run law Llocal ℒlocal omega hSmooth hKernel hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    constructor
    · simpa [phi, kernel, noiseLaw, P, hnext, hcur] using hp.2.2.1
    · simpa [phi, kernel, noiseLaw, B, C, P, hnext, hcur] using hp.2.2.2
  have hBComp : Integrable (fun path ↦ B (prefixMap path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    dsimp [B]
    rw [hnext, hcur]
  have htransfer :=
    integrable_comp_and_integral_le_of_indep_ae_fixed_fiber_aebound
      phi B prefixMap noise hphi hB hprefix.aemeasurable hnoise.aemeasurable
        hfresh hnoiseLaw hMomentPath (fun _ _ ↦ sq_nonneg _) hBComp
  have hinnovationEq : ∀ path,
      kernel (prefixMap path) (noise path) = innovation path := by
    intro path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    simp [kernel, noise, innovation, hnext, hcur]
  refine ⟨?_, ?_⟩
  · apply htransfer.1.congr
    filter_upwards [] with path
    change ‖kernel (prefixMap path) (noise path)‖ ^ 2 =
      ‖innovation path‖ ^ 2
    exact congrArg (fun z : Point d ↦ ‖z‖ ^ 2) (hinnovationEq path)
  · calc
      (∫ path, ‖innovation path‖ ^ 2 ∂law) =
          ∫ path, phi (prefixMap path) (noise path) ∂law := by
            apply integral_congr_ae
            filter_upwards [] with path
            change ‖innovation path‖ ^ 2 =
              ‖kernel (prefixMap path) (noise path)‖ ^ 2
            exact congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
              (hinnovationEq path).symm
      _ ≤ ∫ path, B (prefixMap path) ∂law := htransfer.2
      _ = C * stepMoment run law k := by
        unfold stepMoment
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with path
        have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
          dsimp [xNext]
          rw [hstatePrefix path]
          rfl
        have hcur : x (prefixMap path) = (run k path).x := by
          dsimp [x]
          rw [hstatePrefix path]
        dsimp [B]
        rw [hnext, hcur]
      _ = (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k := by rfl

set_option maxHeartbeats 8000000 in
/- The generated Assumption 3.2 kernel also transports its centered fresh
fiber to the actual proof-exact innovation.  The strict prefix is retained as
the conditioning object: this avoids replacing the source joint kernel by a
measurability assertion on arbitrary query pairs.  The same transport makes
the carried estimator residual orthogonal to the current innovation. -/
theorem
    onlineProofExact_nonrefresh_innovation_centered_and_cross_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
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
    Integrable innovation law ∧
      (∫ path, innovation path ∂law) = 0 ∧
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((path k).2.1.2, (path k).2.2)
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let xNext := fun pref ↦ primalStep A.stepSize (prefixState pref)
  let x := fun pref ↦ (prefixState pref).x
  let direction := fun pref ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let kernel := fun pref ↦
      fun q : ((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
              (q.2 i) -
            localGradientDifference P i (xNext pref) (x pref))
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    simpa [law, roundLaw, prefixMap, prefixLaw,
      onlineProofExactPathLaw, onlineRoundPrefix, SOptLib.iidStreamLaw] using
      (iidStream_prefix_map_eq_infinitePi
        (onlineRoundLaw (b := b) (b0 := b0) A) k)
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hcurrent : Measurable current := measurable_pi_apply k
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · rw [← hprefixLaw]
      simpa [law, roundLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefix, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [noise, current, Function.comp_def] using
      hpastCurrent.comp measurable_id
        (show Measurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2)) by
            fun_prop)
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          roundLaw := by
            rw [show Measure.map current law = roundLaw by
              simpa [current, law, roundLaw, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = noiseLaw := by
        simpa [roundLaw, noiseLaw] using
          onlineRoundLaw_differenceCompression_marginal
            (b := b) (b0 := b0) A
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProofExactProcess_congr_prefix
      A x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback
        (onlineRoundPrefix k path))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hsource :=
    onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_joint_aestronglyMeasurable
      A run law ℒlocal hKernel k
  have hprefixComp :
      (fun z :
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
        kernel (fun j : Fin k ↦ z.2 j.1) z.1) =
      (fun z ↦ average (fun i : Worker n ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem z.1.1 i
              (run (k + 1) z.2).x (run k z.2).x)
            (z.1.2 i) -
          localGradientDifference P i
            (run (k + 1) z.2).x (run k z.2).x)) := by
    funext z
    have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := z.2)
      (path' := onlineExtendRoundPrefix fallback (fun j : Fin k ↦ z.2 j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])
    have hps : prefixState (fun j : Fin k ↦ z.2 j.1) = run k z.2 := hs.symm
    dsimp [kernel, xNext, x]
    rw [hps]
    rfl
  have hfullSwap : AEStronglyMeasurable
      (fun z :
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
        kernel (fun j : Fin k ↦ z.2 j.1) z.1)
      (noiseLaw.prod law) := by
    rw [hprefixComp]
    have hs := hsource.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := noiseLaw) (ν := law))
    simpa using hs
  have hfiniteSwap : AEStronglyMeasurable
      (fun z :
          (((i : Worker n) → Fin b0.1 → Sample i) × (Worker n → Ξ)) ×
            (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
        kernel z.2 z.1)
      (noiseLaw.prod prefixLaw) := by
    exact aestronglyMeasurable_initial_prefix_of_comp_general
      noiseLaw roundLaw k (fun z ↦ kernel z.2 z.1) hfullSwap
  have hkernel : AEStronglyMeasurable (Function.uncurry kernel)
      (prefixLaw.prod noiseLaw) := by
    have hs := hfiniteSwap.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixLaw) (ν := noiseLaw))
    simpa [Function.uncurry] using hs
  have hinnovationEq : ∀ path,
      kernel (prefixMap path) (noise path) = innovation path := by
    intro path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    simp [kernel, noise, innovation, hnext, hcur]
  have hkernelMapped : AEStronglyMeasurable (Function.uncurry kernel)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    rw [hprefixLaw]
    exact hkernel
  have hkernelComp : AEStronglyMeasurable
      (fun path ↦ kernel (prefixMap path) (noise path)) law :=
    aestronglyMeasurable_comp_of_indep_product_law
      hprefix.aemeasurable hnoise.aemeasurable
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law)) hfresh (by
        rw [hnoiseLaw]
        exact hkernelMapped)
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hkernelComp.congr (Filter.Eventually.of_forall hinnovationEq)
  have hsq :=
    onlineProofExact_nonrefresh_innovation_second_moment_of_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hBatch
        hKernel hQuantizer k hStep
  have hinnovationSq : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law := by
    simpa [innovation, P, run, law] using hsq.1
  have hinnovationInt : Integrable innovation law :=
    integrable_of_integrable_norm_sq hinnovationMeas hinnovationSq
  have hfixed : ∀ᵐ path ∂law,
      (∫ q, kernel (prefixMap path) q ∂noiseLaw) = 0 := by
    have hm :=
      onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_moment_ae
        A run law Llocal ℒlocal omega hSmooth hKernel hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    simpa [kernel, noiseLaw, P, hnext, hcur] using hp.2.1
  have hmeanComp :
      (∫ path, kernel (prefixMap path) (noise path) ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      kernel prefixMap noise hkernelMapped hprefix.aemeasurable
        hnoise.aemeasurable hfresh hnoiseLaw
    · exact hinnovationInt.congr
        (Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm)
    · exact hfixed
  have hmean : (∫ path, innovation path ∂law) = 0 := by
    rw [show (∫ path, innovation path ∂law) =
        ∫ path, kernel (prefixMap path) (noise path) ∂law by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm]
    exact hmeanComp
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProofExactProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel k
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable hstate).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hstate))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hinnerInt : Integrable
      (fun path ↦ ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq hinnovationSq
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    apply aestronglyMeasurable_prefix_of_comp_general roundLaw k direction
    refine hresidualMeas.congr (Filter.Eventually.of_forall ?_)
    intro path
    change residual path = direction (prefixMap path)
    dsimp only [residual, direction]
    rw [hstatePrefix path]
  have hscalar : AEStronglyMeasurable
      (fun p ↦ ⟪direction p.1, kernel p.1 p.2⟫_ℝ)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    rw [hprefixLaw]
    exact hdirection.comp_fst.inner hkernel
  have hscalarCompInt : Integrable
      (fun path ↦
        ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ)
      law := by
    apply hinnerInt.congr
    filter_upwards [] with path
    rw [hinnovationEq path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hfixedScalar : ∀ᵐ path ∂law,
      (∫ q, ⟪direction (prefixMap path), kernel (prefixMap path) q⟫_ℝ
        ∂noiseLaw) = 0 := by
    have hm :=
      onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_moment_ae
        A run law Llocal ℒlocal omega hSmooth hKernel hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    have hfiberInt : Integrable (kernel (prefixMap path)) noiseLaw := by
      simpa [kernel, noiseLaw, P, hnext, hcur] using hp.1
    have hfiberZero : (∫ q, kernel (prefixMap path) q ∂noiseLaw) = 0 := by
      simpa [kernel, noiseLaw, P, hnext, hcur] using hp.2.1
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction (prefixMap path))) hfiberInt
    calc
      (∫ q, ⟪direction (prefixMap path), kernel (prefixMap path) q⟫_ℝ
          ∂noiseLaw) =
          (innerSL ℝ) (direction (prefixMap path))
            (∫ q, kernel (prefixMap path) q ∂noiseLaw) := hlin
      _ = 0 := by rw [hfiberZero]; simp
  have hcrossComp :
      (∫ path,
        ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ
        ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      (fun pref q ↦ ⟪direction pref, kernel pref q⟫_ℝ)
      prefixMap noise hscalar hprefix.aemeasurable hnoise.aemeasurable
        hfresh hnoiseLaw hscalarCompInt hfixedScalar
  have hcross :
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
        ∫ path,
          ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ
          ∂law by
      apply integral_congr_ae
      filter_upwards [] with path
      rw [hinnovationEq path]
      dsimp [direction, residual]
      rw [hstatePrefix path]]
    exact hcrossComp
  exact ⟨hinnovationInt, hmean, hcross⟩

set_option maxHeartbeats 8000000 in
/- The proof-exact nonrefresh branch now has the source Eq. (46) additive
moment bound directly from the generated Assumption 3.2 kernel.  In
particular, no every-query-law sample-gradient regularity is used. -/
theorem onlineProofExact_nonrefresh_branch_moments_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
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
  have hcentered :=
    onlineProofExact_nonrefresh_innovation_centered_and_cross_of_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hBatch
        hKernel hQuantizer k hError hStep
  have hinnovationInt : Integrable innovation law := by
    simpa [innovation, P, run, law] using hcentered.1
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hinnovationInt.aestronglyMeasurable
  have hcross :
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    simpa [residual, innovation, P, run, law] using hcentered.2.2
  have hinnovationSq :=
    onlineProofExact_nonrefresh_innovation_second_moment_of_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hBatch
        hKernel hQuantizer k hStep
  have hinnovationSqInt : Integrable
      (fun path ↦ ‖innovation path‖ ^ 2) law := by
    simpa [innovation, P, run, law] using hinnovationSq.1
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProofExactProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel k
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable hstate).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hstate))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
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


set_option maxHeartbeats 3000000 in
/-- Complete proof-exact Eq. (46) under the generated conditional kernel and
literal Assumption 3.3.  Both branch moments and both same-round coin
independence facts are derived on the canonical generated law, so no
all-query-law sample-gradient regularity premise is used. -/
theorem online_estimator_recurrence_46_proof_exact_of_literal_and_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
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
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  have hRefresh :=
    onlineProofExact_refresh_error_integrable_and_expectation_le_of_generatedKernel
      A x0 hBatch ℒlocal σ hKernel hLiteral hSmooth.1 k
  have hRefreshIndep :=
    onlineProofExact_refresh_error_sq_indep_refresh_of_generatedKernel
      A x0 hBatch ℒlocal σ hKernel hLiteral k
  have hNonrefresh :=
    onlineProofExact_nonrefresh_branch_moments_of_generatedKernel
      A x0 Llocal ℒlocal ω hSmooth hBatch hKernel hQuantizer k hError hStep
  have hNonrefreshIndep :=
    onlineProofExact_nonrefresh_error_sq_indep_refresh_of_generatedKernel
      A x0 hBatch ℒlocal hKernel k
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
  let refreshError := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
      stochasticGradient A.problem i ((path k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1
  let refreshSq := fun path ↦ ‖refreshError path‖ ^ 2
  let nonrefreshSq := fun path ↦ ‖residual path + innovation path‖ ^ 2
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n ↦
      A.quantizer.apply
        (onlineBatchDifference A.problem (path k).2.1.2 i xN s.x)
        ((path k).2.2 i)
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
          onlineWorkerEstimator A (onlineDriverOfRoundNoise (path k)) s i) -
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
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hbranchMeas : Measurable branch := by dsimp [branch]; fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    calc
      Measure.map branch law = Measure.map Prod.fst
          (Measure.map (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k)
            law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_fst
              · exact measurable_pi_apply k
      _ = Measure.map Prod.fst (onlineRoundLaw A) := by
            rw [show Measure.map
                (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k) law =
                onlineRoundLaw A by
              simpa [law, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
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
              hNonrefresh.2.2
          · exact sub_nonneg.mpr A.refresh_admissible.2
      _ = (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
        ring

set_option maxHeartbeats 3000000 in
/-- Simultaneous proof-exact component `L²` closure and Eq. (46) history
from the generated conditional kernel and literal Assumption 3.3.  State
measurability and every recurrence step are derived on the canonical path law,
without an all-query-law sample-gradient regularity premise. -/
theorem
    onlineProofExactProcess_scalar_recurrence_components_of_literal_and_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
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
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
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
  have hState (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      onlineProofExactProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel t
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
        have hx : AEStronglyMeasurable (fun path ↦ (run 0 path).x) law :=
          ((measurable_state_x d).comp_aemeasurable (hState 0)).aestronglyMeasurable
        have hr : AEStronglyMeasurable
            (fun path ↦ (run 0 path).g - globalGradient P (run 0 path).x) law := by
          have heq : (fun path ↦
              (run 0 path).g - globalGradient P (run 0 path).x) =
              (fun _ ↦ (0 : Point d)) := by
            funext path
            change globalGradient P x0 - globalGradient P x0 = 0
            simp
          rw [heq]
          exact aestronglyMeasurable_const
        have hxl2 : Integrable (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) law := by
          have heq : (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) =
              (fun _ ↦ (0 : ℝ)) := by
            funext path
            change ‖x0 - x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (μ := law) (c := (0 : ℝ))
        have hgl2 : Integrable (fun path ↦ ‖(run 0 path).g‖ ^ 2) law := by
          have heq : (fun path ↦ ‖(run 0 path).g‖ ^ 2) =
              (fun _ ↦ ‖globalGradient P x0‖ ^ 2) := by
            funext path
            rfl
          rw [heq]
          exact integrable_const (μ := law) (c := ‖globalGradient P x0‖ ^ 2)
        have he : EstimatorErrorMomentWellDefined P run law 0 := by
          rw [EstimatorErrorMomentWellDefined]
          have heq : (fun path ↦
              ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
              (fun _ ↦ (0 : ℝ)) := by
            funext path
            change ‖globalGradient P x0 - globalGradient P x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (μ := law) (c := (0 : ℝ))
        have hs : StepMomentWellDefined run law 0 := by
          have heq : (fun path ↦ ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
              (fun _ ↦ ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2) := by
            funext path
            change ‖(x0 - (A.stepSize : ℝ) • globalGradient P x0) - x0‖ ^ 2 = _
            congr 2
            rw [neg_smul]
            abel
          rw [StepMomentWellDefined, heq]
          exact integrable_const (μ := law)
            (c := ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2)
        refine ⟨hx, hr, hxl2, hgl2, he, hs, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        have hRec :=
          online_estimator_recurrence_46_proof_exact_of_literal_and_generatedKernel
            A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
              hKernel t ih.2.2.2.2.1 ih.2.2.2.2.2.1
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
          simpa [run, onlineProofExactProcess_succ, onlineStep,
            primalStep_eq] using h
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
          simpa [StepMomentWellDefined, run, onlineProofExactProcess_succ,
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

/-- Theorem D.3 at the source-faithful public boundary.  The generated
conditional kernel supplies the exact adaptive-query facts on the canonical
proof-exact law, while literal Assumption 3.3 remains the fixed-query moment
contract.  The conclusion is the original uniform-output object. -/
theorem Theorem_D3_online_VR_nonconvex_source_boundary
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω n b0) :
    Integrable (fun z ↦
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
  apply onlineProofExactD3_of_scalar_recurrence_components
    A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hQuantizer hBatch
  · intro k
    exact
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_generatedKernel
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch hKernel k
  · exact hStep

/-- Theorem D.4 at the source-faithful generated-kernel boundary.  Its
measured object is the last proof-exact iterate under the exact proof law, and
no all-query-law sample-gradient regularity premise is required. -/
theorem Theorem_D4_online_VR_PL_source_boundary
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
    (hKernel : OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) A.refreshProbability ω μ n b0) :
    Integrable (fun path ↦
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
  apply onlineProofExactD4_of_scalar_recurrence_components
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hPL hQuantizer hBatch
  · intro k
    exact
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_generatedKernel
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch hKernel k
  · exact hStep

/-! ## Executable generated-kernel state suppliers

The source conditional kernels already assert measurability of consecutive
generated primal iterates.  Since every Algorithm 3 process uses the positive
step `xᵏ⁺¹ = xᵏ - γ gᵏ`, that pair determines the complete current
state.  The next helper records this process-independent reconstruction, and
the following specializations apply it to the two executable processes. -/

/-- A measurable consecutive-primal pair determines the complete current
state for any process whose primal update is the positive Algorithm 3 step. -/
theorem generatedState_aemeasurable_of_primal_pair
    {d : Count} {Omega : Type*} [MeasurableSpace Omega]
    (gamma : PositiveStepsize) (run : ℕ → Omega → State d)
    (law : Measure Omega) (k : ℕ)
    (hPair : AEStronglyMeasurable
      (fun path ↦ ((run k path).x, (run (k + 1) path).x)) law)
    (hStep : ∀ path, (run (k + 1) path).x =
      primalStep gamma (run k path)) :
    AEMeasurable (run k) law := by
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    (measurable_fst.comp_aemeasurable hPair.aemeasurable).aestronglyMeasurable
  have hxNext : AEStronglyMeasurable
      (fun path ↦ (run (k + 1) path).x) law :=
    (measurable_snd.comp_aemeasurable hPair.aemeasurable).aestronglyMeasurable
  have hgRecovered : AEStronglyMeasurable
      (fun path ↦ ((gamma : ℝ)⁻¹) •
        ((run k path).x - (run (k + 1) path).x)) law :=
    (hx.sub hxNext).const_smul ((gamma : ℝ)⁻¹)
  have hg : AEStronglyMeasurable (fun path ↦ (run k path).g) law := by
    refine hgRecovered.congr (Filter.Eventually.of_forall ?_)
    intro path
    have hgamma : (gamma : ℝ) ≠ 0 := ne_of_gt gamma.property
    change ((gamma : ℝ)⁻¹) •
        ((run k path).x - (run (k + 1) path).x) = (run k path).g
    rw [hStep path, primalStep_eq, sub_sub_cancel, smul_smul,
      inv_mul_cancel₀ hgamma, one_smul]
  exact (measurable_state_mk d).comp_aemeasurable
    (hx.aemeasurable.prodMk hg.aemeasurable)

/-- The source generated conditional kernel makes every complete state of the
actual homogeneous executable Algorithm 3 process measurable under its own
path law.  No all-query adaptive-gradient regularity is used. -/
theorem onlineProcess_aemeasurable_of_generatedConditionalKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (Lcal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem (onlineProcess A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (k : ℕ) :
    AEMeasurable (onlineProcess A x0 hBatch k)
      (onlinePathLaw (b := b) (b0 := b0) A) := by
  apply generatedState_aemeasurable_of_primal_pair A.stepSize
    (onlineProcess A x0 hBatch)
    (onlinePathLaw (b := b) (b0 := b0) A) k (hKernel.2.1 k)
  intro path
  rw [onlineProcess_succ]
  rfl

/-- Source-kernel specialization of executable strict-prefix freshness.  The
complete current residual and consecutive generated queries are functions of
the sampled initializer and strict round prefix, while the difference
minibatch and compressors are the fresh non-coin coordinates of round `k`.
Thus the exact nonrefresh parameter is independent of the exact noise used by
Algorithm 3, with its canonical marginal law, without any every-query-law
regularity premise. -/
theorem
    onlineExecutable_nonrefreshParameter_indep_noise_of_generatedConditionalKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (Lcal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    let parameter := fun path :
        ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Xi) ↦
      (((run (k + 1) path).x, (run k path).x),
        (run k path).g - globalGradient P (run k path).x)
    let noise := fun path :
        ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Xi) ↦
      ((path.2 k).2.1.2, (path.2 k).2.2)
    ProbabilityTheory.IndepFun parameter
        (fun path ↦ path.2 k) law ∧
      ProbabilityTheory.IndepFun parameter noise law ∧
      Measure.map noise law = onlineDifferenceCompressionLaw A := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  have hState : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch Lcal hKernel k
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    ((measurable_state_x d).comp_aemeasurable hState).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path ↦ (run k path).g) law :=
    ((measurable_state_g d).comp_aemeasurable hState).aestronglyMeasurable
  have hResidual : AEStronglyMeasurable
      (fun path ↦
        (run k path).g - globalGradient P (run k path).x) law :=
    hg.sub ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  simpa [P, run, law] using
    (onlineExecutable_nonrefreshParameter_indep_noise_of_components
      (b := b) (b0 := b0) A x0 hBatch k hx hResidual)

/-- The same reconstruction supplies every complete state of executable
Remark D.2 with its worker-dependent batches and canonical path law. -/
theorem heterogeneousOnlineProcess_aemeasurable_of_generatedConditionalKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (k : ℕ) :
    AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  apply generatedState_aemeasurable_of_primal_pair A.stepSize
    (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
    (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k (hKernel.2.1 k)
  intro path
  change
    (heterogeneousOnlineStep A (path.2 k)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path)).x =
      primalStep A.stepSize
        (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path)
  rfl

/-! ## Heterogeneous generated-kernel worker-row transfer

The worker-dependent source kernel is already stated on each worker's own
`b⁰ i` row law.  The next two lemmas disintegrate its joint random-vector
fact into the row fibers needed by the independent-worker covariance
calculation.  They use the exact generated process and law and do not
quantify over unrelated query laws. -/

/-- For almost every generated heterogeneous path, the actual totalized
worker-row difference is a random vector on that worker's canonical iid row
law.  This is the worker-dependent analogue of the homogeneous row transfer
above. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_workerRowDifference_aestronglyMeasurable_ae
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {Lcal : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal)
    (k : ℕ) (i : Worker n) :
    ∀ᵐ path ∂pathLaw,
      AEStronglyMeasurable
        (fun row : Fin (b0 i).1 → Sample i ↦
          average (fun j : Fin (b0 i).1 ↦
            stochasticGradient P i (row j) (run (k + 1) path).x -
              stochasticGradient P i (row j) (run k path).x))
        (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)) := by
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure
      (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)) := by
    infer_instance
  exact
    (heterogeneousOnlineAssumption32GeneratedConditionalKernel_rowDifference_joint_aestronglyMeasurable
      hKernel k i).prodMk_left

/-- Simultaneous finite-worker form of the heterogeneous row transfer.  The
finite quantifier is exposed in the shape consumed by the sharp Remark D.2
worker covariance sum. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_allWorkerRowDifferences_aestronglyMeasurable_ae
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {Lcal : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal)
    (k : ℕ) :
    ∀ᵐ path ∂pathLaw, ∀ i : Worker n,
      AEStronglyMeasurable
        (fun row : Fin (b0 i).1 → Sample i ↦
          average (fun j : Fin (b0 i).1 ↦
            stochasticGradient P i (row j) (run (k + 1) path).x -
              stochasticGradient P i (row j) (run k path).x))
        (Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)) := by
  apply ae_all_iff.2
  intro i
  exact
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_workerRowDifference_aestronglyMeasurable_ae
      hKernel k i

/-- The worker-row generated kernel supplies the existing full heterogeneous
law-a.e. Assumption 3.2 fiber by pulling each witness through the canonical
worker-row marginal.  Both sides use the same generated process and path
law; the only representation change is from a worker's own row to that row
inside the independent heterogeneous batch product. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_to_genuineAE
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {Lcal : Worker n → ℝ}
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw Lcal) :
    HeterogeneousOnlineAssumption32GenuineAE
      (b0 := b0) P run pathLaw Lcal := by
  classical
  refine ⟨hKernel.1, ?_⟩
  intro k
  apply ae_all_iff.2
  intro i
  let rowLaw := Measure.pi (fun _ : Fin (b0 i).1 ↦ P.sampleLaw i)
  let batchLaw := heterogeneousOnlineBatchLaw P b0
  let project := fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i
  letI (w : Worker n) : IsProbabilityMeasure (P.sampleLaw w) :=
    P.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    infer_instance
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  have hproject : Measurable project := by
    dsimp [project]
    fun_prop
  have hmap : Measure.map project batchLaw = rowLaw := by
    simpa [project, batchLaw, rowLaw, MeasureTheory.Measure.infinitePi_eq_pi]
      using heterogeneous_online_batch_law_worker_marginal P b0 i
  rcases hKernel.2.2 k i with
    ⟨delta, _hdelta, hGenuine, hFibers⟩
  have hGenuineFiber : ∀ᵐ path ∂pathLaw,
      ∀ᵐ row ∂rowLaw,
        GenuineOnlineWorkerBatchDifferenceAt P i row
          (run (k + 1) path).x (run k path).x (delta (path, row)) := by
    simpa [rowLaw] using
      (MeasureTheory.Measure.ae_ae_of_ae_prod hGenuine)
  filter_upwards [hFibers, hGenuineFiber] with path hFiber hGenuineRow
  let deltaRow := fun row : Fin (b0 i).1 → Sample i ↦ delta (path, row)
  let deltaBatch := fun batch : HeterogeneousOnlineBatch n Sample b0 ↦
    deltaRow (project batch)
  have hqmp : Measure.QuasiMeasurePreserving project batchLaw rowLaw :=
    ⟨hproject, by rw [hmap]⟩
  have hGenuineBatch : ∀ᵐ batch ∂batchLaw,
      GenuineHeterogeneousOnlineBatchDifferenceAt P batch i
        (run (k + 1) path).x (run k path).x (deltaBatch batch) := by
    have hpull := hqmp.tendsto_ae hGenuineRow
    filter_upwards [hpull] with batch hbatch
    simpa [deltaBatch, deltaRow, project,
      GenuineOnlineWorkerBatchDifferenceAt,
      GenuineHeterogeneousOnlineBatchDifferenceAt] using hbatch
  have hdeltaRow : Integrable deltaRow rowLaw := by
    simpa [deltaRow, rowLaw] using hFiber.1
  have hresidualRow : Integrable
      (fun row ↦ ‖deltaRow row -
        localGradientDifference (onlineLocalProblem P) i
          (run (k + 1) path).x (run k path).x‖ ^ 2) rowLaw := by
    simpa [deltaRow, rowLaw] using hFiber.2.1
  have hdeltaBatch : Integrable deltaBatch batchLaw := by
    have honMap : Integrable deltaRow (Measure.map project batchLaw) := by
      simpa [hmap] using hdeltaRow
    have hpull := (MeasureTheory.integrable_map_measure
      (by simpa [hmap] using hdeltaRow.aestronglyMeasurable)
      hproject.aemeasurable).mp honMap
    simpa [deltaBatch, Function.comp_def] using hpull
  have hresidualBatch : Integrable
      (fun batch ↦ ‖deltaBatch batch -
        localGradientDifference (onlineLocalProblem P) i
          (run (k + 1) path).x (run k path).x‖ ^ 2) batchLaw := by
    let residualRow := fun row ↦ ‖deltaRow row -
      localGradientDifference (onlineLocalProblem P) i
        (run (k + 1) path).x (run k path).x‖ ^ 2
    have honMap : Integrable residualRow (Measure.map project batchLaw) := by
      simpa [hmap, residualRow] using hresidualRow
    have hpull := (MeasureTheory.integrable_map_measure
      (by simpa [hmap, residualRow] using hresidualRow.aestronglyMeasurable)
      hproject.aemeasurable).mp honMap
    simpa [residualRow, deltaBatch, Function.comp_def] using hpull
  refine ⟨deltaBatch, hGenuineBatch, hdeltaBatch, hresidualBatch, ?_, ?_⟩
  · calc
      (∫ batch, deltaBatch batch ∂batchLaw) =
          ∫ row, deltaRow row ∂Measure.map project batchLaw := by
            rw [MeasureTheory.integral_map hproject.aemeasurable
              (by simpa [hmap] using hdeltaRow.aestronglyMeasurable)]
      _ = ∫ row, deltaRow row ∂rowLaw := by rw [hmap]
      _ = localGradientDifference (onlineLocalProblem P) i
          (run (k + 1) path).x (run k path).x := by
            simpa [deltaRow, rowLaw] using hFiber.2.2.1
  · let residualRow := fun row ↦ ‖deltaRow row -
      localGradientDifference (onlineLocalProblem P) i
        (run (k + 1) path).x (run k path).x‖ ^ 2
    calc
      (∫ batch, ‖deltaBatch batch -
          localGradientDifference (onlineLocalProblem P) i
            (run (k + 1) path).x (run k path).x‖ ^ 2 ∂batchLaw) =
          ∫ row, residualRow row ∂Measure.map project batchLaw := by
            rw [MeasureTheory.integral_map hproject.aemeasurable
              (by simpa [hmap, residualRow] using
                hresidualRow.aestronglyMeasurable)]
      _ = ∫ row, residualRow row ∂rowLaw := by rw [hmap]
      _ ≤ (Lcal i) ^ 2 / (b0 i).1 *
          ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 := by
            simpa [residualRow, deltaRow, rowLaw] using hFiber.2.2.2

/-- Source-kernel specialization of the generated-query/fresh-noise
independence used by the heterogeneous nonrefresh recurrence.  Its only
input beyond the algorithm data is Assumption 3.2 on this exact process and
law; in particular it has no literal-moment or adaptive-regularity premise. -/
theorem
    heterogeneousOnlineQuery_indep_differenceCompression_of_generatedConditionalKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (k : ℕ) :
    ProbabilityTheory.IndepFun
      (fun path ↦
        (primalStep A.stepSize
            (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path),
          (heterogeneousOnlineProcess
            (b := b) (b0 := b0) A x0 k path).x))
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
        ((path.2 k).2.1.2, (path.2 k).2.2))
      (heterogeneousOnlinePathLaw A) := by
  apply heterogeneousOnlineQuery_indep_differenceCompression_of_measurable
    (b := b) (b0 := b0) A x0 k
  exact
    heterogeneousOnlineProcess_aemeasurable_of_generatedConditionalKernel
      A x0 Lcal hKernel k

set_option maxHeartbeats 2000000 in
/-- Time zero of the actual executable Algorithm 3 scalar recurrence, now
closed directly from the source generated conditional kernel.  Literal
Assumption 3.3 controls the sampled initializer and Assumption 1.2 supplies
only differentiability of the averaged local objectives; no all-query-law
sample-gradient regularity is used. -/
theorem onlineProcess_scalar_recurrence_components_zero_of_literal_and_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path ↦ (run 0 path).x) law ∧
      AEStronglyMeasurable
        (fun path ↦ (run 0 path).g - globalGradient P (run 0 path).x) law ∧
      Integrable (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) law ∧
      Integrable (fun path ↦ ‖(run 0 path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law 0 ∧
      StepMomentWellDefined run law 0 := by
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
  have hState : AEMeasurable (run 0) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel 0
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
  have he := (online_executable_initial_error_moment_le_of_literal_and_smooth
    A x0 Llocal σ hSmooth hLiteral hBatch).1
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
    simpa [StepMomentWellDefined, run, onlineProcess_succ, onlineStep,
      primalStep_eq] using hscaled
  exact ⟨hx, hr, hxl2, hgl2, he, hs⟩

set_option maxHeartbeats 2000000 in
/-- The executable generated query and one independent refresh minibatch form
the exact product-law random variable used by the refresh branch.  Joint
measurability is derived worker-coordinate by worker-coordinate from the
generated Assumption 3.2 kernel and literal fixed-query Assumption 3.3; no
regularity over unrelated query laws is used. -/
theorem
    onlineProcess_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (k : ℕ) :
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    let batchLaw := onlineBatchLaw A.problem b
    AEStronglyMeasurable
      (fun p :
          (((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((i : Worker n) → Fin b.1 → Sample i) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.2 i j)
              (run (k + 1) p.1).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (run (k + 1) p.1).x‖ ^ 2)
      (law.prod batchLaw) := by
  classical
  dsimp only
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let batchLaw := onlineBatchLaw A.problem b
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
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hquery : AEStronglyMeasurable
      (fun path ↦ (run (k + 1) path).x) law := by
    have hpair := hKernel.2.1 (k + 1)
    exact (measurable_fst.comp_aemeasurable
      hpair.aemeasurable).aestronglyMeasurable
  have hgrad (i : Worker n) (j : Fin b.1) : AEStronglyMeasurable
      (fun p :
          (((w : Worker n) → Fin b.1 → Sample w) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b.1 → Sample w) ↦
        stochasticGradient A.problem i (p.2 i j) (run (k + 1) p.1).x)
      (law.prod batchLaw) := by
    have hsingle :=
      (onlineProcess_adaptiveGradient_source_regular
        A x0 hBatch ℒ σ hKernel hLiteral (k + 1) i).2
    have hcoord : MeasurePreserving
        (fun batch : (w : Worker n) → Fin b.1 → Sample w ↦ batch i j)
        batchLaw (A.problem.sampleLaw i) :=
      ⟨(by fun_prop), by
        simpa [batchLaw] using
          onlineBatchLaw_coordinate_marginal A.problem i j⟩
    have hpull := hsingle.comp_measurePreserving
      ((MeasurePreserving.id law).prod hcoord)
    simpa [run, law, batchLaw, Function.comp_def] using hpull
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p :
          (((w : Worker n) → Fin b.1 → Sample w) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b.1 → Sample w) ↦
        average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i (p.2 i j) (run (k + 1) p.1).x))
      (law.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ hgrad i j)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p :
          (((w : Worker n) → Fin b.1 → Sample w) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b.1 → Sample w) ↦
        average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i (p.2 i j)
            (run (k + 1) p.1).x)))
      (law.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ ↦ hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p :
          (((w : Worker n) → Fin b.1 → Sample w) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b.1 → Sample w) ↦
        globalGradient (onlineLocalProblem A.problem)
          (run (k + 1) p.1).x)
      (law.prod batchLaw) :=
    ((measurable_gradient
      (globalObjective (onlineLocalProblem A.problem))).comp_aemeasurable
        hquery.aemeasurable).aestronglyMeasurable.comp_fst
  have hresidual := havg.sub hglobal
  simpa [run, law, batchLaw, pow_two] using
    hresidual.norm.mul hresidual.norm

set_option maxHeartbeats 2000000 in
/-- The executable refresh square remains measurable after discarding the
unused iid tail.  The retained carrier is exactly the sampled initializer and
strict round prefix, while the second coordinate is an independent refresh
minibatch.  This is the prefix-law form needed to transport the literal
fixed-query variance estimate to the actual current round. -/
theorem
    onlineExecutablePrefix_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ) :
    let initialLaw := onlineBatchLaw A.problem b
    let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := initialLaw.prod
      (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
    let batchLaw := onlineBatchLaw A.problem b
    let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
    AEStronglyMeasurable
      (fun p :
          (((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((i : Worker n) → Fin b.1 → Sample i) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.2 i j)
              (primalStep A.stepSize (prefixState p.1)))) -
          globalGradient (onlineLocalProblem A.problem)
            (primalStep A.stepSize (prefixState p.1))‖ ^ 2)
      (prefixLaw.prod batchLaw) := by
  classical
  dsimp only
  let initialLaw := onlineBatchLaw A.problem b
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let batchLaw := onlineBatchLaw A.problem b
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hfull : AEStronglyMeasurable
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((i : Worker n) → Fin b.1 → Sample i)) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.2 i j)
              (run (k + 1) p.1).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (run (k + 1) p.1).x‖ ^ 2)
      (law.prod batchLaw) := by
    simpa [run, law, initialLaw, streamLaw, batchLaw, onlinePathLaw] using
      onlineProcess_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
        A x0 hBatch ℒ σ hKernel hLiteral k
  have hreorder : MeasurePreserving
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              ((i : Worker n) → Fin b.1 → Sample i)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod batchLaw).prod streamLaw)
      ((initialLaw.prod streamLaw).prod batchLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw batchLaw streamLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := batchLaw) (ν := streamLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw streamLaw batchLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hstream : AEStronglyMeasurable
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              ((i : Worker n) → Fin b.1 → Sample i)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.1.2 i j)
              (run (k + 1) (p.1.1, p.2)).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (run (k + 1) (p.1.1, p.2)).x‖ ^ 2)
      ((initialLaw.prod batchLaw).prod streamLaw) := by
    simpa [Function.comp_def] using hfull.comp_measurePreserving hreorder
  let F := fun p :
      (((i : Worker n) → Fin b.1 → Sample i) ×
          ((i : Worker n) → Fin b.1 → Sample i)) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (p.1.2 i j)
          (primalStep A.stepSize (prefixState (p.1.1, p.2))))) -
      globalGradient (onlineLocalProblem A.problem)
        (primalStep A.stepSize (prefixState (p.1.1, p.2)))‖ ^ 2
  have hstatePrefix : ∀ initial stream,
      prefixState (initial, fun j : Fin k ↦ stream j.1) =
        run k (initial, stream) := by
    intro initial stream
    dsimp [prefixState, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k initial
      (path := stream)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ stream j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])).symm
  have hstreamF : AEStronglyMeasurable
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              ((i : Worker n) → Fin b.1 → Sample i)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        F (p.1, fun j : Fin k ↦ p.2 j.1))
      ((initialLaw.prod batchLaw).prod streamLaw) := by
    refine hstream.congr (Filter.Eventually.of_forall ?_)
    intro p
    dsimp [F]
    rw [hstatePrefix p.1.1 p.2]
    rfl
  have hfinite : AEStronglyMeasurable F
      ((initialLaw.prod batchLaw).prod prefixStreamLaw) := by
    simpa [prefixStreamLaw] using
      aestronglyMeasurable_initial_prefix_of_comp_general
        (initialLaw.prod batchLaw) roundLaw k F hstreamF
  have hreorderFinite : MeasurePreserving
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((i : Worker n) → Fin b.1 → Sample i)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod prefixStreamLaw).prod batchLaw)
      ((initialLaw.prod batchLaw).prod prefixStreamLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw prefixStreamLaw batchLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixStreamLaw) (ν := batchLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw batchLaw prefixStreamLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hresult := hfinite.comp_measurePreserving hreorderFinite
  simpa [F, prefixLaw, prefixStreamLaw, prefixState, initialLaw, roundLaw,
    batchLaw, Function.comp_def] using hresult

set_option maxHeartbeats 2000000 in
/-- The actual executable refresh error is integrable and satisfies the
literal Assumption 3.3 variance bound using only the generated Assumption 3.2
kernel.  The sampled initializer and strict round prefix are independent of
the current refresh minibatch under `onlinePathLaw`; no all-query regularity
predicate is used. -/
theorem
    onlineExecutable_refresh_error_integrable_and_expectation_le_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i))
    (k : ℕ) :
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    Integrable refreshErrorSq law ∧
      (∫ path, refreshErrorSq path ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  dsimp only
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let initialLaw := onlineBatchLaw A.problem b
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixMap := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (path.1, onlineRoundPrefix k path.2)
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let current := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ path.2 k
  let batch := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (path.2 k).2.1.1
  let batchLaw := onlineBatchLaw A.problem b
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id,
      iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixMap, prefixLaw, prefixStreamLaw, law, onlineRoundPrefix]
      using hm.symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
          (Measure.map Prod.snd law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact measurable_pi_apply k
            · exact measurable_snd
      _ = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
          streamLaw := by
            rw [show Measure.map Prod.snd law = streamLaw by
              dsimp [law]
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := by
        simpa [streamLaw] using
          SOptLib.iidStreamLaw_map_eval roundLaw k
  have hjoint : Measure.map (fun path ↦ (prefixMap path, current path)) law =
      prefixLaw.prod roundLaw := by
    let streamJoint := fun stream :
        ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      ((fun j : Fin k ↦ stream j.1), stream k)
    have hstreamJoint : MeasurePreserving streamJoint streamLaw
        (prefixStreamLaw.prod roundLaw) := by
      refine ⟨(by
        dsimp [streamJoint]
        exact (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).prodMk
          (measurable_pi_apply k)), ?_⟩
      have hprefixStream : Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
            fun j : Fin k ↦ stream j.1) streamLaw = prefixStreamLaw := by
        simpa [streamLaw, prefixStreamLaw] using
          iidStream_prefix_map_eq_infinitePi roundLaw k
      have hj := infinitePi_prefix_current_map_eq_prod
        (fun _ : ℕ ↦ roundLaw) k
      have hprefixRaw : Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
            fun j : Fin k ↦ stream j.1)
          (Measure.infinitePi (fun _ : ℕ ↦ roundLaw)) =
            prefixStreamLaw := by
        simpa [streamLaw] using hprefixStream
      rw [hprefixRaw] at hj
      simpa [streamJoint, streamLaw] using hj
    have h0 := (MeasurePreserving.id initialLaw).prod hstreamJoint
    have h1 :=
      (measurePreserving_prodAssoc initialLaw prefixStreamLaw roundLaw).symm
    have h := h1.comp h0
    simpa [law, prefixLaw, prefixStreamLaw, prefixMap, current,
      onlineRoundPrefix, streamJoint, Function.comp_def] using h.map_eq
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · exact hjoint
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law := by
    have h := hpastCurrent.comp measurable_id
      (show Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1) by fun_prop)
    simpa [batch, current, Function.comp_def] using h
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1)
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1)
          roundLaw := by rw [hcurrentLaw]
      _ = batchLaw := by
        simpa [roundLaw, batchLaw] using
          onlineRoundLaw_refreshBatch_marginal (b0 := b0) A
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  let query := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    primalStep A.stepSize (prefixState pref)
  let F := fun (pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (fresh : (i : Worker n) → Fin b.1 → Sample i) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (fresh i j) (query pref))) -
      globalGradient (onlineLocalProblem A.problem) (query pref)‖ ^ 2
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod batchLaw) := by
    simpa [F, query, prefixState, prefixLaw, prefixStreamLaw, initialLaw,
      roundLaw, batchLaw] using
      onlineExecutablePrefix_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
        A x0 hBatch ℒ σ hKernel hLiteral fallback k
  have hFmap : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.map prefixMap law).prod batchLaw) := by
    rw [hprefixLaw]
    exact hF
  have hfixed (pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) :
      Integrable (F pref) batchLaw ∧
        (∫ fresh, F pref fresh ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [F, query, batchLaw] using
      (onlineFixedRefreshAverage_secondMoment_of_literal
        (b := b) A (query pref) σ hLiteral hDiff)
  have hcomp : Integrable
      (fun path ↦ F (prefixMap path) (batch path)) law :=
    integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := prefixMap) (Y := batch)
      (C := varianceAggregateSq σ / (n.1 * b.1)) hFmap
      hprefix.aemeasurable hbatch.aemeasurable hprefixBatch hbatchLaw
      (fun _ _ ↦ sq_nonneg _) (fun pref ↦ (hfixed pref).1)
      (fun pref ↦ (hfixed pref).2)
  have hbound : (∫ path, F (prefixMap path) (batch path) ∂law) ≤
      varianceAggregateSq σ / (n.1 * b.1) :=
    integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := prefixMap) (Y := batch)
      hFmap hprefix.aemeasurable hbatch.aemeasurable hprefixBatch hbatchLaw
      hcomp (fun pref ↦ (hfixed pref).2)
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hcalc : ∀ path, F (prefixMap path) (batch path) =
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem)
          (run (k + 1) path).x‖ ^ 2 := by
    intro path
    dsimp [F, query, batch]
    rw [hstatePrefix path]
    rfl
  constructor
  · exact hcomp.congr (Filter.Eventually.of_forall hcalc)
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hcalc)]
    exact hbound

set_option maxHeartbeats 2000000 in
/-- The executable refresh-error square is independent of its same-round
Bernoulli coin under the generated Assumption 3.2 kernel and literal
Assumption 3.3.  The sampled initializer and strict prefix are retained as the
past carrier, and the measurable refresh kernel uses only the non-coin part
of the current round. -/
theorem onlineExecutable_refresh_error_sq_indep_refresh_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (k : ℕ) :
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    ProbabilityTheory.IndepFun refreshErrorSq
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1) law := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let initialLaw := onlineBatchLaw A.problem b
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let refreshBatchLaw := onlineBatchLaw A.problem b
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let roundLaw := coinLaw.prod restLaw
  let prefixLaw := initialLaw.prod
    (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure refreshBatchLaw := by
    unfold refreshBatchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    unfold coinLaw refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    unfold restLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  let xNext := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    primalStep A.stepSize (prefixState pref)
  have hstatePrefix : ∀ path, prefixState
      (path.1, fun j : Fin k ↦ path.2 j.1) = run k path := by
    intro path
    dsimp [prefixState, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ path.2 j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])).symm
  let refreshKernelRest := fun
      (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (r : ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (r.1.1 i j) (xNext pref))) -
      globalGradient P (xNext pref)‖ ^ 2
  have hRefreshPrefixBatch : AEStronglyMeasurable
      (fun p :
          (((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b.1 → Sample w) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.2 i j) (xNext p.1))) -
          globalGradient P (xNext p.1)‖ ^ 2)
      (prefixLaw.prod refreshBatchLaw) := by
    simpa [P, xNext, prefixState, prefixLaw, initialLaw, roundLaw, coinLaw,
      restLaw, refreshBatchLaw, differenceBatchLaw, compressionLaw,
      onlineRoundLaw] using
      onlineExecutablePrefix_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
        A x0 hBatch ℒ σ hKernel hLiteral fallback k
  have hRefreshKernelRest : AEStronglyMeasurable
      (Function.uncurry refreshKernelRest) (prefixLaw.prod restLaw) := by
    let pullBatch := fun p :
        (((i : Worker n) → Fin b.1 → Sample i) ×
          (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
          ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) ↦ (p.1, p.2.1.1)
    have hpullBatch : Measurable pullBatch := by
      dsimp [pullBatch]
      fun_prop
    have hpullBatchLaw : Measure.map pullBatch (prefixLaw.prod restLaw) =
        prefixLaw.prod refreshBatchLaw := by
      let projectBatch := fun r :
          ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) ↦ r.1.1
      have hprojectBatch : Measurable projectBatch := by
        dsimp [projectBatch]
        fun_prop
      have hprojectBatchLaw : Measure.map projectBatch restLaw =
          refreshBatchLaw := by
        calc
          Measure.map projectBatch restLaw =
              Measure.map Prod.fst (Measure.map Prod.fst restLaw) := by
            rw [MeasureTheory.Measure.map_map measurable_fst measurable_fst]
            rfl
          _ = Measure.map Prod.fst
              (refreshBatchLaw.prod differenceBatchLaw) := by
            rw [show Measure.map Prod.fst restLaw =
                refreshBatchLaw.prod differenceBatchLaw by
              dsimp [restLaw]
              rw [Measure.map_fst_prod, measure_univ, one_smul]]
          _ = refreshBatchLaw := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
      have hmap := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
        measurable_id hprojectBatch
      rw [hprojectBatchLaw] at hmap
      simpa [pullBatch, projectBatch] using hmap.symm
    have hqmp : Measure.QuasiMeasurePreserving pullBatch
        (prefixLaw.prod restLaw) (prefixLaw.prod refreshBatchLaw) :=
      ⟨hpullBatch, by rw [hpullBatchLaw]⟩
    simpa [refreshKernelRest, pullBatch, Function.uncurry] using
      hRefreshPrefixBatch.comp_quasiMeasurePreserving hqmp
  have hindep := initial_iidStream_prefix_current_snd_kernel_indep_fst
    initialLaw coinLaw restLaw k refreshKernelRest hRefreshKernelRest
  apply hindep.congr (Filter.Eventually.of_forall ?_)
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  intro path
  change refreshKernelRest
      (path.1, fun j : Fin k ↦ path.2 j.1) (path.2 k).2 = _
  dsimp [refreshKernelRest, xNext]
  rw [hstatePrefix path]
  rfl

set_option maxHeartbeats 3000000 in
/-- The generated Assumption 3.2 kernel makes the exact executable
nonrefresh innovation jointly measurable after the unused iid tail is
discarded.  The retained carrier includes the sampled initializer and the
strict round prefix, so this is the executable (rather than proof-exact)
prefix interface needed by Eq. (46). -/
theorem
    onlineExecutablePrefix_nonrefreshAverage_product_aestronglyMeasurable_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒlocal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let initialLaw := onlineBatchLaw A.problem b
    let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := initialLaw.prod
      (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
    let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
    let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
    AEStronglyMeasurable
      (fun p :
          (((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            (((i : Worker n) → Fin b0.1 → Sample i) ×
              (Worker n → Ξ)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem p.2.1 i
                (primalStep A.stepSize (prefixState p.1))
                (prefixState p.1).x)
              (p.2.2 i) -
            localGradientDifference P i
              (primalStep A.stepSize (prefixState p.1))
              (prefixState p.1).x))
      (prefixLaw.prod noiseLaw) := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let initialLaw := onlineBatchLaw A.problem b
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hfull : AEStronglyMeasurable
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            (((i : Worker n) → Fin b0.1 → Sample i) ×
              (Worker n → Ξ))) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem p.2.1 i
                (run (k + 1) p.1).x (run k p.1).x)
              (p.2.2 i) -
            localGradientDifference P i
              (run (k + 1) p.1).x (run k p.1).x))
      (law.prod noiseLaw) := by
    simpa [P, run, law, initialLaw, streamLaw, noiseLaw, onlinePathLaw] using
      onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_joint_aestronglyMeasurable
        A run law ℒlocal hKernel k
  have hreorder : MeasurePreserving
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              (((i : Worker n) → Fin b0.1 → Sample i) ×
                (Worker n → Ξ))) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod noiseLaw).prod streamLaw)
      ((initialLaw.prod streamLaw).prod noiseLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw noiseLaw streamLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := noiseLaw) (ν := streamLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw streamLaw noiseLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hstream : AEStronglyMeasurable
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              (((i : Worker n) → Fin b0.1 → Sample i) ×
                (Worker n → Ξ))) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem p.1.2.1 i
                (run (k + 1) (p.1.1, p.2)).x
                (run k (p.1.1, p.2)).x)
              (p.1.2.2 i) -
            localGradientDifference P i
              (run (k + 1) (p.1.1, p.2)).x
              (run k (p.1.1, p.2)).x))
      ((initialLaw.prod noiseLaw).prod streamLaw) := by
    simpa [Function.comp_def] using hfull.comp_measurePreserving hreorder
  let F := fun p :
      (((i : Worker n) → Fin b.1 → Sample i) ×
          (((i : Worker n) → Fin b0.1 → Sample i) ×
            (Worker n → Ξ))) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem p.1.2.1 i
            (primalStep A.stepSize (prefixState (p.1.1, p.2)))
            (prefixState (p.1.1, p.2)).x)
          (p.1.2.2 i) -
        localGradientDifference P i
          (primalStep A.stepSize (prefixState (p.1.1, p.2)))
          (prefixState (p.1.1, p.2)).x)
  have hstatePrefix : ∀ initial stream,
      prefixState (initial, fun j : Fin k ↦ stream j.1) =
        run k (initial, stream) := by
    intro initial stream
    dsimp [prefixState, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k initial
      (path := stream)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ stream j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])).symm
  have hstreamF : AEStronglyMeasurable
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              (((i : Worker n) → Fin b0.1 → Sample i) ×
                (Worker n → Ξ))) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        F (p.1, fun j : Fin k ↦ p.2 j.1))
      ((initialLaw.prod noiseLaw).prod streamLaw) := by
    refine hstream.congr (Filter.Eventually.of_forall ?_)
    intro p
    dsimp [F]
    rw [hstatePrefix p.1.1 p.2]
    rfl
  have hfinite : AEStronglyMeasurable F
      ((initialLaw.prod noiseLaw).prod prefixStreamLaw) := by
    simpa [prefixStreamLaw] using
      aestronglyMeasurable_initial_prefix_of_comp_general
        (initialLaw.prod noiseLaw) roundLaw k F hstreamF
  have hreorderFinite : MeasurePreserving
      (fun p :
          ((((i : Worker n) → Fin b.1 → Sample i) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            (((i : Worker n) → Fin b0.1 → Sample i) ×
              (Worker n → Ξ))) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod prefixStreamLaw).prod noiseLaw)
      ((initialLaw.prod noiseLaw).prod prefixStreamLaw) := by
    have h1 :=
      measurePreserving_prodAssoc initialLaw prefixStreamLaw noiseLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixStreamLaw) (ν := noiseLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw noiseLaw prefixStreamLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hresult := hfinite.comp_measurePreserving hreorderFinite
  simpa [F, P, prefixLaw, prefixStreamLaw, prefixState, initialLaw,
    roundLaw, noiseLaw, Function.comp_def] using hresult

set_option maxHeartbeats 3000000 in
/-- The complete executable nonrefresh residual square is independent of its
same-round refresh coin using only the generated Assumption 3.2 kernel.  The
sampled initializer and strict prefix are retained, and the preceding theorem
supplies measurability of the exact current difference/compression kernel; no
all-query sample-gradient regularity is used. -/
theorem onlineExecutable_nonrefresh_error_sq_indep_refresh_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒlocal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
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
    ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2)
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1) law := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let initialLaw := onlineBatchLaw A.problem b
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let refreshBatchLaw := onlineBatchLaw A.problem b
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let noiseLaw := differenceBatchLaw.prod compressionLaw
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let roundLaw := coinLaw.prod restLaw
  let prefixMap := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (path.1, onlineRoundPrefix k path.2)
  let prefixLaw := Measure.map prefixMap law
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure refreshBatchLaw := by
    unfold refreshBatchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    unfold coinLaw refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    unfold restLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  let x := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (prefixState pref).x
  let xNext := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    primalStep A.stepSize (prefixState pref)
  let direction := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let innovationKernel := fun
      (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
          (q.2 i) -
        localGradientDifference P i (xNext pref) (x pref))
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel k
  have hprefixLaw : prefixLaw =
      initialLaw.prod (Measure.infinitePi (fun _ : Fin k ↦ roundLaw)) := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw
      (SOptLib.iidStreamLaw roundLaw) measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixLaw, prefixMap, law, initialLaw, roundLaw, coinLaw, restLaw,
      refreshBatchLaw, differenceBatchLaw, compressionLaw, onlinePathLaw,
      onlineRoundLaw, onlineRoundPrefix] using hm.symm
  have hprefixPoint (f : State d → Point d) (hf : Measurable f) :
      AEStronglyMeasurable (fun pref ↦ f (prefixState pref)) prefixLaw := by
    have hpath : AEStronglyMeasurable (fun path ↦ f (run k path)) law :=
      (hf.comp_aemeasurable hstate).aestronglyMeasurable
    have hcomp : AEStronglyMeasurable
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
          f (prefixState (path.1, fun j : Fin k ↦ path.2 j.1))) law := by
      refine hpath.congr (Filter.Eventually.of_forall ?_)
      intro path
      simpa [prefixMap, onlineRoundPrefix] using
        congrArg f (hstatePrefix path).symm
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      initialLaw roundLaw k (fun pref ↦ f (prefixState pref)) (by
        simpa [law, initialLaw, roundLaw, coinLaw, restLaw, refreshBatchLaw,
          differenceBatchLaw, compressionLaw, onlinePathLaw, onlineRoundLaw]
          using hcomp)
    rw [hprefixLaw]
    exact hfinite
  have hx : AEStronglyMeasurable x prefixLaw := by
    simpa [x] using hprefixPoint (fun s : State d ↦ s.x) (measurable_state_x d)
  have hxNext : AEStronglyMeasurable xNext prefixLaw := by
    simpa [xNext] using hprefixPoint (primalStep A.stepSize)
      (measurable_primalStep A.stepSize)
  have hg : AEStronglyMeasurable (fun pref ↦ (prefixState pref).g)
      prefixLaw :=
    hprefixPoint (fun s : State d ↦ s.g) (measurable_state_g d)
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    exact hg.sub ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hinnovationKernel : AEStronglyMeasurable
      (fun p ↦ innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
    rw [hprefixLaw]
    simpa [innovationKernel, xNext, x, noiseLaw, differenceBatchLaw,
      compressionLaw, onlineDifferenceCompressionLaw, P, prefixState,
      initialLaw, roundLaw, coinLaw, restLaw, refreshBatchLaw, onlineRoundLaw]
      using
        onlineExecutablePrefix_nonrefreshAverage_product_aestronglyMeasurable_of_generatedKernel
          A x0 hBatch ℒlocal hKernel fallback k
  let nonrefreshKernelRest := fun
      (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (r : ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) ↦
    ‖direction pref + innovationKernel pref (r.1.2, r.2)‖ ^ 2
  have hNonrefreshKernelRest : AEStronglyMeasurable
      (Function.uncurry nonrefreshKernelRest) (prefixLaw.prod restLaw) := by
    let pull := fun p :
        (((i : Worker n) → Fin b.1 → Sample i) ×
          (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
          ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) ↦
      (p.1, (p.2.1.2, p.2.2))
    have hpull : Measurable pull := by
      dsimp [pull]
      fun_prop
    have hproject : Measure.map
        (fun r : ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
          (r.1.2, r.2)) restLaw = noiseLaw := by
      dsimp [restLaw, noiseLaw]
      simpa using (MeasureTheory.Measure.map_prod_map
        (refreshBatchLaw.prod differenceBatchLaw) compressionLaw
        measurable_snd measurable_id).symm
    have hpullLaw : Measure.map pull (prefixLaw.prod restLaw) =
        prefixLaw.prod noiseLaw := by
      have hm := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
        measurable_id
        (show Measurable
          (fun r : ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) ↦ (r.1.2, r.2)) by fun_prop)
      rw [Measure.map_id, hproject] at hm
      simpa [pull] using hm.symm
    have hbase : AEStronglyMeasurable
        (fun p ↦ ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
        (prefixLaw.prod noiseLaw) := by
      have hv := hdirection.comp_fst.add hinnovationKernel
      simpa [pow_two] using hv.norm.mul hv.norm
    have hqmp : Measure.QuasiMeasurePreserving pull
        (prefixLaw.prod restLaw) (prefixLaw.prod noiseLaw) :=
      ⟨hpull, by rw [hpullLaw]⟩
    simpa [nonrefreshKernelRest, Function.uncurry, pull] using
      hbase.comp_quasiMeasurePreserving hqmp
  have hindep := initial_iidStream_prefix_current_snd_kernel_indep_fst
    initialLaw coinLaw restLaw k nonrefreshKernelRest (by
      rw [← hprefixLaw]
      exact hNonrefreshKernelRest)
  apply hindep.congr (Filter.Eventually.of_forall ?_)
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  intro path
  change nonrefreshKernelRest (prefixMap path) (path.2 k).2 = _
  dsimp [nonrefreshKernelRest, direction, innovationKernel, xNext, x]
  rw [hstatePrefix path]
  rfl

set_option maxHeartbeats 8000000 in
/- The generated Assumption 3.2 kernel supplies the complete centered moment
package for the actual executable nonrefresh innovation.  The sampled
initializer and strict round prefix are the independent carrier, while the
current difference batch and compressors are the fresh coordinate.  Thus no
all-query sample-gradient regularity is needed. -/
theorem onlineExecutable_nonrefresh_innovation_moments_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
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
    Integrable innovation law ∧
      (∫ path, innovation path ∂law) = 0 ∧
      Integrable (fun path ↦ ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k ∧
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let initialLaw := onlineBatchLaw A.problem b
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let prefixMap := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (path.1, onlineRoundPrefix k path.2)
  let prefixLaw := Measure.map prefixMap law
  let streamPrefix := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let streamCurrent := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    path k
  let current := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ path.2 k
  let noiseOfRound := fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
    (z.2.1.2, z.2.2)
  let noise := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    noiseOfRound (current path)
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hprefixLaw : prefixLaw =
      initialLaw.prod (Measure.infinitePi (fun _ : Fin k ↦ roundLaw)) := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id,
      iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixLaw, prefixMap, law, initialLaw, streamLaw, roundLaw,
      onlinePathLaw, onlineRoundPrefix] using hm.symm
  have hstreamPrefix : Measurable streamPrefix := by
    dsimp [streamPrefix, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hstreamCurrent : Measurable streamCurrent := measurable_pi_apply k
  haveI : IsProbabilityMeasure (Measure.map streamPrefix streamLaw) :=
    Measure.isProbabilityMeasure_map hstreamPrefix.aemeasurable
  have hnoiseOfRound : Measurable noiseOfRound := by
    dsimp [noiseOfRound]
    fun_prop
  have hnoise : Measurable noise := by
    dsimp [noise, current]
    exact hnoiseOfRound.comp (hstreamCurrent.comp measurable_snd)
  have hpastCurrentStream : ProbabilityTheory.IndepFun
      streamPrefix streamCurrent streamLaw := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (streamPrefix path, streamCurrent path))
      (P := streamLaw)
      (mu := Measure.map streamPrefix streamLaw) (nu := roundLaw)
    · exact (hstreamPrefix.prodMk hstreamCurrent).aemeasurable
    · simpa [streamLaw, streamPrefix, streamCurrent, roundLaw,
        onlineRoundPrefix, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod (fun _ : ℕ ↦ roundLaw) k)
  have hpastNoiseStream : ProbabilityTheory.IndepFun streamPrefix
      (noiseOfRound ∘ streamCurrent) streamLaw :=
    hpastCurrentStream.comp measurable_id hnoiseOfRound
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [prefixMap, noise, current, streamPrefix, streamCurrent, law,
      streamLaw, onlinePathLaw, Function.comp_def] using
      indepFun_prod_left_adjoin_of_indepFun initialLaw streamLaw
        streamPrefix (noiseOfRound ∘ streamCurrent) hstreamPrefix
        (hnoiseOfRound.comp hstreamCurrent) hpastNoiseStream
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map (noiseOfRound ∘ streamCurrent)
          (Measure.map Prod.snd law) := by
            change Measure.map ((noiseOfRound ∘ streamCurrent) ∘ Prod.snd) law = _
            rw [MeasureTheory.Measure.map_map
              (hnoiseOfRound.comp hstreamCurrent) measurable_snd]
      _ = Measure.map (noiseOfRound ∘ streamCurrent) streamLaw := by
            rw [show Measure.map Prod.snd law = streamLaw by
              dsimp [law, streamLaw, onlinePathLaw]
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = Measure.map noiseOfRound (Measure.map streamCurrent streamLaw) := by
            rw [MeasureTheory.Measure.map_map hnoiseOfRound hstreamCurrent]
      _ = Measure.map noiseOfRound roundLaw := by
            rw [show Measure.map streamCurrent streamLaw = roundLaw by
              simpa [streamCurrent, streamLaw] using
                SOptLib.iidStreamLaw_map_eval roundLaw k]
      _ = noiseLaw := by
            simpa [noiseOfRound, roundLaw, noiseLaw] using
              onlineRoundLaw_differenceCompression_marginal
                (b := b) (b0 := b0) A
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  let xNext := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    primalStep A.stepSize (prefixState pref)
  let x := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (prefixState pref).x
  let direction := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let kernel := fun
      (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
          (q.2 i) -
        localGradientDifference P i (xNext pref) (x pref))
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
  let residual := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (run k path).g - globalGradient P (run k path).x
  let B := fun pref ↦ C * ‖xNext pref - x pref‖ ^ 2
  let phi := fun pref q ↦ ‖kernel pref q‖ ^ 2
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel k
  have hprefixPoint (f : State d → Point d) (hf : Measurable f) :
      AEStronglyMeasurable (fun pref ↦ f (prefixState pref)) prefixLaw := by
    have hpath : AEStronglyMeasurable (fun path ↦ f (run k path)) law :=
      (hf.comp_aemeasurable hstate).aestronglyMeasurable
    have hcomp : AEStronglyMeasurable
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
          f (prefixState (path.1, fun j : Fin k ↦ path.2 j.1))) law := by
      refine hpath.congr (Filter.Eventually.of_forall ?_)
      intro path
      simpa [prefixMap, onlineRoundPrefix] using
        congrArg f (hstatePrefix path).symm
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      initialLaw roundLaw k (fun pref ↦ f (prefixState pref)) (by
        simpa [law, initialLaw, streamLaw, roundLaw, onlinePathLaw] using hcomp)
    rw [hprefixLaw]
    exact hfinite
  have hx : AEStronglyMeasurable x prefixLaw := by
    simpa [x] using hprefixPoint (fun s : State d ↦ s.x) (measurable_state_x d)
  have hxNext : AEStronglyMeasurable xNext prefixLaw := by
    simpa [xNext] using hprefixPoint (primalStep A.stepSize)
      (measurable_primalStep A.stepSize)
  have hg : AEStronglyMeasurable (fun pref ↦ (prefixState pref).g)
      prefixLaw :=
    hprefixPoint (fun s : State d ↦ s.g) (measurable_state_g d)
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    exact hg.sub ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hkernel : AEStronglyMeasurable (Function.uncurry kernel)
      (prefixLaw.prod noiseLaw) := by
    rw [hprefixLaw]
    simpa [kernel, xNext, x, noiseLaw, P, prefixState, initialLaw, roundLaw]
      using
        onlineExecutablePrefix_nonrefreshAverage_product_aestronglyMeasurable_of_generatedKernel
          A x0 hBatch ℒlocal hKernel fallback k
  have hphi : AEStronglyMeasurable (Function.uncurry phi)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    simpa [prefixLaw, phi, Function.uncurry, pow_two] using
      hkernel.norm.mul hkernel.norm
  have hB : AEStronglyMeasurable B (Measure.map prefixMap law) := by
    simpa [prefixLaw, B, pow_two] using
      ((hxNext.sub hx).norm.mul (hxNext.sub hx).norm).const_mul C
  have hMomentPath : ∀ᵐ path ∂law,
      Integrable (kernel (prefixMap path)) noiseLaw ∧
        (∫ q, kernel (prefixMap path) q ∂noiseLaw) = 0 ∧
        Integrable (phi (prefixMap path)) noiseLaw ∧
        (∫ q, phi (prefixMap path) q ∂noiseLaw) ≤ B (prefixMap path) := by
    have hm :=
      onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_moment_ae
        A run law Llocal ℒlocal omega hSmooth hKernel hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [kernel, noiseLaw, P, hnext, hcur] using hp.1
    · simpa [kernel, noiseLaw, P, hnext, hcur] using hp.2.1
    · simpa [phi, kernel, noiseLaw, P, hnext, hcur] using hp.2.2.1
    · simpa [phi, kernel, noiseLaw, B, C, P, hnext, hcur] using hp.2.2.2
  have hBComp : Integrable (fun path ↦ B (prefixMap path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    dsimp [B]
    rw [hnext, hcur]
  have htransfer :=
    integrable_comp_and_integral_le_of_indep_ae_fixed_fiber_aebound
      phi B prefixMap noise hphi hB hprefix.aemeasurable hnoise.aemeasurable
        hfresh hnoiseLaw
        (hMomentPath.mono fun path hp ↦ ⟨hp.2.2.1, hp.2.2.2⟩)
        (fun _ _ ↦ sq_nonneg _) hBComp
  have hinnovationEq : ∀ path,
      kernel (prefixMap path) (noise path) = innovation path := by
    intro path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    simp [kernel, noise, noiseOfRound, current, innovation, hnext, hcur]
  have hkernelMapped : AEStronglyMeasurable (Function.uncurry kernel)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    simpa [prefixLaw] using hkernel
  have hkernelComp : AEStronglyMeasurable
      (fun path ↦ kernel (prefixMap path) (noise path)) law :=
    aestronglyMeasurable_comp_of_indep_product_law
      hprefix.aemeasurable hnoise.aemeasurable
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law)) hfresh (by
        rw [hnoiseLaw]
        exact hkernelMapped)
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hkernelComp.congr (Filter.Eventually.of_forall hinnovationEq)
  have hinnovationSq : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law := by
    apply htransfer.1.congr
    filter_upwards [] with path
    change ‖kernel (prefixMap path) (noise path)‖ ^ 2 = ‖innovation path‖ ^ 2
    exact congrArg (fun z : Point d ↦ ‖z‖ ^ 2) (hinnovationEq path)
  have hinnovationInt : Integrable innovation law :=
    integrable_of_integrable_norm_sq hinnovationMeas hinnovationSq
  have hmeanComp :
      (∫ path, kernel (prefixMap path) (noise path) ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      kernel prefixMap noise hkernelMapped hprefix.aemeasurable
        hnoise.aemeasurable hfresh hnoiseLaw
    · exact hinnovationInt.congr
        (Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm)
    · exact hMomentPath.mono fun _ hp ↦ hp.2.1
  have hmean : (∫ path, innovation path ∂law) = 0 := by
    rw [show (∫ path, innovation path ∂law) =
        ∫ path, kernel (prefixMap path) (noise path) ∂law by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm]
    exact hmeanComp
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable hstate).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hstate))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hinnerInt : Integrable
      (fun path ↦ ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq hinnovationSq
  have hscalar : AEStronglyMeasurable
      (fun p ↦ ⟪direction p.1, kernel p.1 p.2⟫_ℝ)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    simpa [prefixLaw] using hdirection.comp_fst.inner hkernel
  have hscalarCompInt : Integrable
      (fun path ↦
        ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ)
      law := by
    apply hinnerInt.congr
    filter_upwards [] with path
    rw [hinnovationEq path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hfixedScalar : ∀ᵐ path ∂law,
      (∫ q, ⟪direction (prefixMap path), kernel (prefixMap path) q⟫_ℝ
        ∂noiseLaw) = 0 := by
    filter_upwards [hMomentPath] with path hp
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction (prefixMap path))) hp.1
    calc
      (∫ q, ⟪direction (prefixMap path), kernel (prefixMap path) q⟫_ℝ
          ∂noiseLaw) =
          (innerSL ℝ) (direction (prefixMap path))
            (∫ q, kernel (prefixMap path) q ∂noiseLaw) := hlin
      _ = 0 := by rw [hp.2.1]; simp
  have hcrossComp :
      (∫ path,
        ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ
        ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      (fun pref q ↦ ⟪direction pref, kernel pref q⟫_ℝ)
      prefixMap noise hscalar hprefix.aemeasurable hnoise.aemeasurable
        hfresh hnoiseLaw hscalarCompInt hfixedScalar
  have hcross :
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
        ∫ path,
          ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ
          ∂law by
      apply integral_congr_ae
      filter_upwards [] with path
      rw [hinnovationEq path]
      dsimp [direction, residual]
      rw [hstatePrefix path]]
    exact hcrossComp
  refine ⟨hinnovationInt, hmean, hinnovationSq, ?_, hcross⟩
  calc
    (∫ path, ‖innovation path‖ ^ 2 ∂law) =
        ∫ path, phi (prefixMap path) (noise path) ∂law := by
          apply integral_congr_ae
          filter_upwards [] with path
          change ‖innovation path‖ ^ 2 =
            ‖kernel (prefixMap path) (noise path)‖ ^ 2
          exact congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
            (hinnovationEq path).symm
    _ ≤ ∫ path, B (prefixMap path) ∂law := htransfer.2
    _ = C * stepMoment run law k := by
      unfold stepMoment
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with path
      have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
        dsimp [xNext]
        rw [hstatePrefix path]
        rfl
      have hcur : x (prefixMap path) = (run k path).x := by
        dsimp [x]
        rw [hstatePrefix path]
      dsimp [B]
      rw [hnext, hcur]
    _ = (1 / (n.1 : ℝ)) *
        (omega * (rootMeanSquare Llocal) ^ 2 +
          (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
        stepMoment run law k := by rfl

set_option maxHeartbeats 4000000 in
/- The executable nonrefresh branch of Eq. (46), obtained entirely from the
generated Assumption 3.2 kernel.  This packages the centered innovation,
sharp source coefficient, carried-error orthogonality, and independence from
the same-round refresh coin without an all-query regularity premise. -/
theorem onlineExecutable_nonrefresh_branch_moments_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
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
    Integrable (fun path ↦ ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k ∧
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 ∧
      Integrable (fun path ↦ ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment P run law k +
          (1 / (n.1 : ℝ)) *
            (omega * (rootMeanSquare Llocal) ^ 2 +
              (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k ∧
      ProbabilityTheory.IndepFun
        (fun path ↦ ‖residual path + innovation path‖ ^ 2)
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1) law := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
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
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  have hmom :=
    onlineExecutable_nonrefresh_innovation_moments_of_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hBatch
        hKernel hQuantizer k hError hStep
  have hinnovationInt : Integrable innovation law := by
    simpa [innovation, residual, P, run, law] using hmom.1
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hinnovationInt.aestronglyMeasurable
  have hinnovationSq : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law := by
    simpa [innovation, residual, P, run, law] using hmom.2.2.1
  have hinnovationBound :
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤ C * stepMoment run law k := by
    simpa [innovation, residual, P, run, law, C] using hmom.2.2.2.1
  have hcross :
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    simpa [innovation, residual, P, run, law] using hmom.2.2.2.2
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel k
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable hstate).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hstate))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hnonrefreshInt : Integrable
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresidualMeas hinnovationMeas
      hresidualSq hinnovationSq
  have hnonrefreshEq :
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          ∫ path, ‖innovation path‖ ^ 2 ∂law := by
    let pair : Bool → (((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) → Point d :=
      fun z ↦ if z then innovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      law (Finset.univ : Finset Bool) pair
      (fun z _ ↦ by cases z <;> simp [pair, hresidualMeas, hinnovationMeas])
      (fun z _ ↦ by cases z <;> simp [pair, hresidualSq, hinnovationSq])
      (fun z _ w _ hzw ↦ by
        cases z <;> cases w
        · exact False.elim (hzw rfl)
        · simpa [pair] using hcross
        · simpa [pair, real_inner_comm] using hcross
        · exact False.elim (hzw rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  have hindep : ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2)
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1) law := by
    simpa [residual, innovation, P, run, law] using
      onlineExecutable_nonrefresh_error_sq_indep_refresh_of_generatedKernel
        A x0 hBatch ℒlocal hKernel k
  refine ⟨hinnovationSq, hinnovationBound, hcross, hnonrefreshInt, ?_, hindep⟩
  rw [hnonrefreshEq]
  change estimatorErrorMoment P run law k +
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
    estimatorErrorMoment P run law k + C * stepMoment run law k
  exact add_le_add_right hinnovationBound _

set_option maxHeartbeats 3000000 in
/-- Track-A executable Eq. (46) at one time.  The generated conditional kernel
supplies both branches for the actual `onlineProcess` under `onlinePathLaw`; no
all-query sample-gradient regularity premise is used. -/
theorem online_estimator_recurrence_46_executable_of_literal_and_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
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
    onlineExecutable_refresh_error_integrable_and_expectation_le_of_generatedKernel
      A x0 hBatch ℒlocal σ hKernel hLiteral hSmooth.1 k
  have hRefreshIndep :=
    onlineExecutable_refresh_error_sq_indep_refresh_of_generatedKernel
      A x0 hBatch ℒlocal σ hKernel hLiteral k
  have hNonrefresh :=
    onlineExecutable_nonrefresh_branch_moments_of_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal ω hSmooth hBatch
        hKernel hQuantizer k hError hStep
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
/-- Simultaneous executable component `L²` closure and Eq. (46) history from
the source generated conditional kernel.  The time-zero component is the
actual sampled initializer, and every successor uses the one-step Track-A
recurrence for the same `onlineProcess` and `onlinePathLaw`. -/
theorem onlineProcess_scalar_recurrence_components_of_literal_and_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
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
      onlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒlocal hKernel t
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
          onlineProcess_scalar_recurrence_components_zero_of_literal_and_generatedKernel
            A x0 Llocal ℒlocal σ hSmooth hLiteral hBatch hKernel
        refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1,
          h0.2.2.2.2.1, h0.2.2.2.2.2, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        have hRec :=
          online_estimator_recurrence_46_executable_of_literal_and_generatedKernel
            A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
              hKernel t ih.2.2.2.2.1 ih.2.2.2.2.2.1
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

/-! ### Executable generated-kernel convergence boundaries

These corollaries feed the exact source Assumption 3.2 generated conditional
kernel into the shared executable D.3/D.4 telescopes.  They retain the sampled
initializer and its explicit error term, and require no all-query-law sample
gradient regularity. -/

/-- Executable initialization-corrected D.3 on `onlineProcess` and
`onlinePathLaw`, supplied by the generated conditional kernel. -/
theorem Theorem_D3_online_VR_nonconvex_initialization_corrected_of_literal_and_generatedKernel
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
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
    exact onlineProcess_scalar_recurrence_components_of_literal_and_generatedKernel
      A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch hKernel k
  · exact hStep

/-- Executable initialization-corrected D.4 on `onlineProcess` and
`onlinePathLaw`, supplied by the generated conditional kernel. -/
theorem Theorem_D4_online_VR_PL_initialization_corrected_of_literal_and_generatedKernel
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
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
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
            A.refreshProbability *
              expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
          varianceAggregateSq σ / (n.1 * b.1 * μ) := by
  apply online_D4_initialization_corrected_of_scalar_recurrence
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hLiteral hPL
      hQuantizer hBatch
  · intro k
    exact onlineProcess_scalar_recurrence_components_of_literal_and_generatedKernel
      A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch hKernel k
  · exact hStep

/-- Pointwise executable D.3 accuracy from the source generated kernel. -/
theorem onlineExecutableNonconvexAccuracy_of_budget_of_literal_and_generatedKernel
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
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
    Theorem_D3_online_VR_nonconvex_initialization_corrected_of_literal_and_generatedKernel
      (K := K) A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hLiteral
      hQuantizer hBatch hKernel hStep
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

/-- Pointwise executable D.4 accuracy from the source generated kernel. -/
theorem onlineExecutablePLAccuracy_of_budget_of_literal_and_generatedKernel
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
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
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
    Theorem_D4_online_VR_PL_initialization_corrected_of_literal_and_generatedKernel
      (K := K) A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hLiteral hPL hQuantizer hBatch hKernel hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedOnlineInitialEstimatorErrorSq_le_of_literal
    (b := b) A x0 σ hLiteral hSmooth.1
  have hContraction : 0 ≤ 1 - (A.stepSize : ℝ) * (μ : ℝ) := by
    apply sub_nonneg.mpr
    nlinarith [A.refresh_admissible.2, hStep.2]
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
          A.refreshProbability *
            expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
        varianceAggregateSq σ / (n.1 * b.1 * μ) ≤
      (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability *
            (varianceAggregateSq σ / (n.1 * b.1)) +
        varianceAggregateSq σ / (n.1 * b.1 * μ) := by gcongr
    _ ≤ (ε : ℝ) := hBudget

/-- Accuracy-family form of executable D.3 under the generated kernel. -/
theorem onlineExecutableNonconvexAccuracy_family_of_budget_of_literal_and_generatedKernel
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
    (hKernel : ∀ ε, OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ℒlocal)
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
  exact onlineExecutableNonconvexAccuracy_of_budget_of_literal_and_generatedKernel
    A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hLiteral hQuantizer
      (hBatch ε) (hKernel ε) hStep ε (hBudget ε)

end MARINA
