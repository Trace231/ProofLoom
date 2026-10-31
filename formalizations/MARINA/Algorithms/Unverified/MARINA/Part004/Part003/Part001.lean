import Algorithms.Unverified.MARINA.Part003
import Algorithms.Unverified.MARINA.Part004.Part002

-- Aggregator for `Algorithms.Unverified.MARINA`. Source declarations live under `MARINA/`.

namespace MARINA

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-! ## Literal online moment boundary

Assumption 3.3 states only the workerwise fixed-query unbiasedness and
bounded-variance equations.  Adaptive-query regularity used by the generated
Algorithm 3 proofs is kept separate below. -/

/-- Public D.3/D.4 package retaining the supplied-stepsize measured root and
adding the source Eq. (40)/(48) canonical-step specializations.  The two
canonical equalities are explicit because an upper-bound stepsize hypothesis
alone does not identify `1 / A.stepSize` with the printed source brackets.
All four endpoints use the sampled-initializer `onlineProcess` and its
`onlinePathLaw`; in particular their oracle integrals charge the executable
initial batch and are not costs for either exact-gradient proof process. -/
theorem Theorem_D3_D4_measured_cost_complexity_with_canonical_stepsizes
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (x0 xStar : Point d)
    (nonconvexBaseBatch plBaseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmoothNonconvex : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)) ℒlocal)
    (hAverageSmoothPL : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ plBaseBatch ε)) ℒlocal)
    (hStepNonconvex : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (hStepPL : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0)
    (hCanonicalStepNonconvex :
      (A.stepSize : ℝ) *
        (rootMeanSquare Llocal +
          Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1)
    (hCanonicalStepPL :
      (A.stepSize : ℝ) * max (2 * (μ : ℝ) / A.refreshProbability)
        (rootMeanSquare Llocal +
          Real.sqrt ((2 * (1 - A.refreshProbability)) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let nonconvexBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) nonconvexBaseBatch
    let plBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ plBaseBatch
    let Δnc := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let Δpl := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let nonconvexSuppliedScale := fun ε : Accuracy =>
      1 + 4 * Δnc / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    let plSuppliedScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δpl / (ε : ℝ)) /
        ((A.stepSize : ℝ) * (μ : ℝ)))
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
    let nonconvexCanonicalScale := fun ε : Accuracy =>
      1 + Δnc / (ε : ℝ) ^ 2 * nonconvexBracket
    let plCanonicalScale := fun ε : Accuracy =>
      1 + max (1 / A.refreshProbability) (plBracket / (μ : ℝ)) *
        max 0 (Real.log (4 * Δpl / (ε : ℝ)))
    ((∃ K : Accuracy → Count,
        OnlineExecutableNonconvexMeasuredCostComplexity A x0 nonconvexBatch
          (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)
          K nonconvexSuppliedScale
          (fun ε => (nonconvexBatch ε).1 + nonconvexSuppliedScale ε *
            (A.refreshProbability * (nonconvexBatch ε).1 +
              2 * (1 - A.refreshProbability) * b0.1))
          (fun ε => d.1 + nonconvexSuppliedScale ε *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer))) ∧
      (∃ K : Accuracy → Count,
        OnlineExecutablePLMeasuredCostComplexity A x0 xStar plBatch
          (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ plBaseBatch ε)
          K plSuppliedScale
          (fun ε => (plBatch ε).1 + plSuppliedScale ε *
            (A.refreshProbability * (plBatch ε).1 +
              2 * (1 - A.refreshProbability) * b0.1))
          (fun ε => d.1 + plSuppliedScale ε *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer)))) ∧
    (∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 nonconvexBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          nonconvexBaseBatch ε)
        K nonconvexCanonicalScale
        (fun ε => (nonconvexBatch ε).1 + nonconvexCanonicalScale ε *
          (A.refreshProbability * (nonconvexBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + nonconvexCanonicalScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) ∧
    (∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar plBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ plBaseBatch ε)
        K plCanonicalScale
        (fun ε => (plBatch ε).1 + plCanonicalScale ε *
          (A.refreshProbability * (plBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + plCanonicalScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) := by
  dsimp only
  refine ⟨Theorem_D3_D4_measured_cost_complexity A x0 xStar
    nonconvexBaseBatch plBaseBatch Llocal ℒlocal σ ω fStar μ hLower
      hSmooth hVariance hPL hQuantizer hAverageSmoothNonconvex
      hAverageSmoothPL hStepNonconvex hStepPL, ?_, ?_⟩
  · exact onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize
      A x0 nonconvexBaseBatch Llocal ℒlocal σ ω fStar hLower hSmooth
        hVariance hQuantizer hAverageSmoothNonconvex hCanonicalStepNonconvex
  · exact onlineExecutablePLMeasuredCostComplexity_canonical_stepsize
      A x0 xStar plBaseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
        hVariance hPL hQuantizer hAverageSmoothPL hCanonicalStepPL

/-- Source-faithful companion for the two distinct canonical-step regimes.
Equation (40) and Equation (48) choose different stepsizes, so their measured
endpoints are instantiated with separate `OnlineData` values while sharing
the source problem, quantizer, and refresh probability. -/
theorem
    Theorem_D3_D4_measured_cost_complexity_with_separate_canonical_stepsizes_canonical_pair_compatibility
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
    (hVariance : OnlineAssumption33Literal A.problem σ ∧
      OnlineAdaptiveSampleGradientRegularity A.problem)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmoothNonconvex : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A γNonconvex A.refreshProbability
            A.refresh_admissible) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)) ℒlocal)
    (hAverageSmoothPL : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
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
    let nonconvexScale := fun ε : Accuracy =>
      1 + Δnc / (ε : ℝ) ^ 2 * nonconvexBracket
    let plScale := fun ε : Accuracy =>
      1 + max (1 / A.refreshProbability) (plBracket / (μ : ℝ)) *
        max 0 (Real.log (4 * Δpl / (ε : ℝ)))
    (∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity ANonconvex x0
        nonconvexBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          nonconvexBaseBatch ε)
        K nonconvexScale
        (fun ε => (nonconvexBatch ε).1 + nonconvexScale ε *
          (A.refreshProbability * (nonconvexBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + nonconvexScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) ∧
    (∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity APL x0 xStar plBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ plBaseBatch ε)
        K plScale
        (fun ε => (plBatch ε).1 + plScale ε *
          (A.refreshProbability * (plBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + plScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) := by
  dsimp only
  constructor
  · apply onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize
      (onlineDataWithParameters A γNonconvex A.refreshProbability
        A.refresh_admissible)
      x0 nonconvexBaseBatch Llocal ℒlocal σ ω fStar
    · simpa [onlineDataWithParameters] using hLower
    · simpa [onlineDataWithParameters] using hSmooth
    · simpa [onlineDataWithParameters] using hVariance
    · simpa [onlineDataWithParameters] using hQuantizer
    · intro ε
      simpa [onlineDataWithParameters] using hAverageSmoothNonconvex ε
    · simpa [onlineDataWithParameters] using hCanonicalStepNonconvex
  · apply onlineExecutablePLMeasuredCostComplexity_canonical_stepsize
      (onlineDataWithParameters A γPL A.refreshProbability
        A.refresh_admissible)
      x0 xStar plBaseBatch Llocal ℒlocal σ ω fStar μ
    · simpa [onlineDataWithParameters] using hLower
    · simpa [onlineDataWithParameters] using hSmooth
    · simpa [onlineDataWithParameters] using hVariance
    · simpa [onlineDataWithParameters] using hPL
    · simpa [onlineDataWithParameters] using hQuantizer
    · intro ε
      simpa [onlineDataWithParameters] using hAverageSmoothPL ε
    · simpa [onlineDataWithParameters] using hCanonicalStepPL

/-! The preceding declaration retains the former canonical-pair interface for
callers that project only the two Eq. (40)/(48) endpoints.  The named release
root below strengthens that public result with the reciprocal supplied-step
families required by the source's upper-bound stepsize statements. -/

/-- The D.3/D.4 executable measured-cost pair for two stepsizes.  Both sides
use the sampled initializer, `onlineProcess`, `onlinePathLaw`, and the actual
oracle and communication integrals fixed by the two executable specializations. -/
def OnlineSeparateStepsizeMeasuredCostComplexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (ANonconvex APL : OnlineData d n Sample Ξ)
    (x0 xStar : Point d)
    (nonconvexBatch plBatch : Accuracy → Count)
    (hNonconvexBatch : ∀ ε, OnlineBatchAdmissible (nonconvexBatch ε) b0)
    (hPLBatch : ∀ ε, OnlineBatchAdmissible (plBatch ε) b0)
    (nonconvexScale plScale : Accuracy → ℝ) : Prop :=
  (∃ K : Accuracy → Count,
    OnlineExecutableNonconvexMeasuredCostComplexity ANonconvex x0
      nonconvexBatch hNonconvexBatch K nonconvexScale
      (fun ε => (nonconvexBatch ε).1 + nonconvexScale ε *
        (ANonconvex.refreshProbability * (nonconvexBatch ε).1 +
          2 * (1 - ANonconvex.refreshProbability) * b0.1))
      (fun ε => d.1 + nonconvexScale ε *
        (ANonconvex.refreshProbability * d.1 +
          (1 - ANonconvex.refreshProbability) *
            expectedDensity ANonconvex.quantizer))) ∧
  (∃ K : Accuracy → Count,
    OnlineExecutablePLMeasuredCostComplexity APL x0 xStar plBatch hPLBatch K
      plScale
      (fun ε => (plBatch ε).1 + plScale ε *
        (APL.refreshProbability * (plBatch ε).1 +
          2 * (1 - APL.refreshProbability) * b0.1))
      (fun ε => d.1 + plScale ε *
        (APL.refreshProbability * d.1 +
          (1 - APL.refreshProbability) * expectedDensity APL.quantizer)))

set_option linter.unusedVariables false in
/-- Compatibility corollary for callers that already carry the stronger
global stochastic-gradient kernel realization.  The measured conclusion no
longer needs to consume that premise. -/
theorem Theorem_D3_D4_measured_cost_complexity_of_kernel
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (x0 xStar : Point d)
    (nonconvexBaseBatch plBaseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmoothNonconvex : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)) ℒlocal)
    (hAverageSmoothPL : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ plBaseBatch ε)) ℒlocal)
    (hStepNonconvex : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (hStepPL : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let nonconvexBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) nonconvexBaseBatch
    let plBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ plBaseBatch
    let Δnc := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let Δpl := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let nonconvexIterationScale := fun ε : Accuracy =>
      1 + 4 * Δnc / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    let plIterationScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δpl / (ε : ℝ)) /
        ((A.stepSize : ℝ) * (μ : ℝ)))
    (∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 nonconvexBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          nonconvexBaseBatch ε)
        K nonconvexIterationScale
        (fun ε => (nonconvexBatch ε).1 + nonconvexIterationScale ε *
          (A.refreshProbability * (nonconvexBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + nonconvexIterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) ∧
    (∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar plBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ plBaseBatch ε)
        K plIterationScale
        (fun ε => (plBatch ε).1 + plIterationScale ε *
          (A.refreshProbability * (plBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + plIterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) := by
  apply Theorem_D3_D4_measured_cost_complexity A x0 xStar
    nonconvexBaseBatch plBaseBatch Llocal ℒlocal σ ω fStar μ hLower
    hSmooth hVariance hPL hQuantizer hAverageSmoothNonconvex hAverageSmoothPL
  · exact hStepNonconvex
  · exact hStepPL

/-- Every realized PP-MARINA total communication count is nonnegative; the
sum treats each indexed sampled-client occurrence separately. -/
theorem ppTotalCommunicationCost_nonneg
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (K : Count)
    (path : ℕ → PPRoundNoise n r Ξ) :
    0 ≤ ppTotalCommunicationCost (r := r) A x0 K path := by
  unfold ppTotalCommunicationCost
  apply add_nonneg <;> try positivity
  apply Finset.sum_nonneg
  intro k hk
  split <;> try positivity
  apply Finset.sum_nonneg
  intro j hj
  unfold quantizerNonzeroCount
  positivity

/-- E.1/E.2 package whose communication endpoint is total generated PP
communication under the same `ppPathLaw` used by convergence. -/
def PPMeasuredCommunicationComplexity
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (K : Accuracy → Count)
    (accuracy : Accuracy → Prop) (iterationScale communicationScale : Accuracy → ℝ) :
    Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    (∀ ε, Integrable (ppTotalCommunicationCost (r := r) A x0 (K ε))
      (ppPathLaw A)) ∧
    AccuracyBigO
      (fun ε => ∫ path, ppTotalCommunicationCost (r := r) A x0 (K ε) path
        ∂ppPathLaw A) communicationScale

/-- Lift a proved E.1/E.2 schedule to measured total PP communication. -/
theorem ppMeasuredCommunicationComplexity_of_twoEndpoint
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale communicationScale : Accuracy → ℝ)
    (hEndpoints : TwoEndpointComplexity K accuracy iterationScale
      (fun ε => ppCommunicationCount d n r (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    PPMeasuredCommunicationComplexity (r := r) A x0 K accuracy iterationScale
      communicationScale := by
  unfold TwoEndpointComplexity at hEndpoints
  unfold PPMeasuredCommunicationComplexity
  refine ⟨hEndpoints.1, hEndpoints.2.1, ?_, ?_⟩
  · intro ε
    exact (ppTotalCommunicationCost_integrable_and_expectation_le
      A x0 Llocal hSmooth hQ (K ε)).1
  · apply accuracyBigO_of_nonneg_le hEndpoints.2.2
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        ppTotalCommunicationCost_nonneg A x0 (K ε) path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability :=
        le_of_lt A.refresh_admissible.1
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold ppCommunicationCount
      positivity
    · intro ε
      exact (ppTotalCommunicationCost_integrable_and_expectation_le
        A x0 Llocal hSmooth hQ (K ε)).2

/-- Lift PP convergence and iteration complexity directly to the measured
communication variable.  Unlike the compatibility lift above, this theorem
does not pass through `ppCommunicationCount` or its definitional companion
theorem. -/
theorem ppMeasuredCommunicationComplexity_of_accuracy_iteration
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (hAccuracy : ∀ ε, accuracy ε)
    (hIteration : AccuracyIterationBigO (fun ε => (K ε).1) iterationScale)
    (hScaleNonneg : ∀ᶠ ε : Accuracy in accuracyToZero,
      0 ≤ iterationScale ε) :
    PPMeasuredCommunicationComplexity (r := r) A x0 K accuracy iterationScale
      (fun ε => (d.1 : ℝ) * n.1 + iterationScale ε *
        (A.refreshProbability * d.1 * n.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1)) := by
  let payload : ℝ := A.refreshProbability * d.1 * n.1 +
    (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1
  have hd : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  have hr : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
  have hInitPos : 0 < (d.1 : ℝ) * n.1 := mul_pos hd hn
  have hPayloadPos : 0 < payload := by
    have hζ : 0 ≤ expectedDensity A.quantizer :=
      expectedDensity_nonneg_of_unbiased hQ
    have hp0 : 0 < A.refreshProbability := A.refresh_admissible.1
    have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
    dsimp [payload]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos hp0 hd) hn)
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hp1) hζ) hr.le)
  have hAnalytic : AccuracyBigO
      (fun ε => (d.1 : ℝ) * n.1 + (K ε).1 * payload)
      (fun ε => (d.1 : ℝ) * n.1 + iterationScale ε * payload) := by
    rcases hIteration with hZero | hOrdinary
    · have hBounded := accuracyBigO_affine_cost_of_schedule
        (K := fun ε => ((K ε).1 : ℝ)) (scale := fun _ : Accuracy => 1)
        (init := (d.1 : ℝ) * n.1) (actualPayload := payload)
        (targetPayload := payload) (payloadFactor := 1)
        hZero.2 hInitPos hPayloadPos.le hPayloadPos zero_lt_one
        (by simp) (Filter.Eventually.of_forall fun _ => zero_le_one)
      have hConst : AccuracyBigO
          (fun _ : Accuracy => (d.1 : ℝ) * n.1 + payload)
          (fun _ : Accuracy => (d.1 : ℝ) * n.1) := by
        unfold AccuracyBigO
        exact Asymptotics.isBigO_const_const _ (ne_of_gt hInitPos)
          accuracyToZero
      have hBounded' : AccuracyBigO
          (fun ε => (d.1 : ℝ) * n.1 + (K ε).1 * payload)
          (fun _ : Accuracy => (d.1 : ℝ) * n.1 + payload) := by
        simpa using hBounded
      have hCombined := hBounded'.trans hConst
      rw [show (fun ε : Accuracy => (d.1 : ℝ) * n.1 +
          iterationScale ε * payload) =
          (fun _ : Accuracy => (d.1 : ℝ) * n.1) by
        funext ε
        rw [hZero.1 ε]
        ring]
      simpa using hCombined
    · exact accuracyBigO_affine_cost_of_schedule hOrdinary hInitPos
        hPayloadPos.le hPayloadPos zero_lt_one (by simp) hScaleNonneg
  unfold PPMeasuredCommunicationComplexity
  refine ⟨hAccuracy, hIteration, ?_, ?_⟩
  · intro ε
    exact (ppTotalCommunicationCost_integrable_and_expectation_le
      A x0 Llocal hSmooth hQ (K ε)).1
  · apply accuracyBigO_of_nonneg_le hAnalytic
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        ppTotalCommunicationCost_nonneg A x0 (K ε) path)
    · intro ε
      dsimp [payload]
      positivity
    · intro ε
      simpa [payload] using
        (ppTotalCommunicationCost_integrable_and_expectation_le
          A x0 Llocal hSmooth hQ (K ε)).2

/-- PP-MARINA nonconvex accuracy and iteration complexity, isolated from the
legacy scalar communication endpoint. -/
theorem ppNonconvexAccuracyIterationComplexity
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (ω fStar : ℝ) (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStep : PPStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω r) :
    let Δ := globalObjective A.problem x0 - fStar
    let bracket := rootMeanSquare Llocal *
      (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
        (A.refreshProbability * r.1)))
    ∃ K : Accuracy → Count,
      (∀ ε, NonconvexAccuracy (K ε) A.problem
        (ppProcess (r := r) A x0) (ppPathLaw (r := r) A) ε) ∧
      AccuracyIterationBigO (fun ε => (K ε).1)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 - fStar :=
    sub_nonneg.mpr (hLower x0)
  dsimp
  let Δ : ℝ := globalObjective A.problem x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal *
    (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
      (A.refreshProbability * r.1)))
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hr : 0 < (r.1 : ℝ) := by exact_mod_cast r.2
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _))
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · let K₁ : Count := ⟨1, by norm_num⟩
    have hGapEq : globalObjective A.problem x0 - fStar = 0 := hGapZero.symm
    refine ⟨fun _ => K₁, ?_, Or.inl ⟨?_, ?_⟩⟩
    · intro ε
      unfold NonconvexAccuracy
      have hE1 := Theorem_E1_PP_MARINA_nonconvex (K := K₁) A x0
        Llocal ω fStar hLower hSmooth hQuantizer hClients hStep
      refine ⟨hE1.1, hE1.2.trans ?_⟩
      rw [hGapEq]
      simp
      positivity
    · intro ε
      change Δ / (ε : ℝ) ^ 2 * bracket = 0
      have hΔzero : Δ = 0 := by simpa [Δ] using hGapEq
      rw [hΔzero]
      ring
    · unfold AccuracyBigO
      simpa [K₁] using
        (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
          accuracyToZero)
  · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
    · let K₁ : Count := ⟨1, by norm_num⟩
      have hBracketEq : bracket = 0 := hBracketZero.symm
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hfactor : 0 < 1 + Real.sqrt
            ((1 - A.refreshProbability) * (1 + ω) /
              (A.refreshProbability * r.1)) := by positivity
        dsimp [bracket] at hBracketEq
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        A.problem Llocal fStar hLower hSmooth hLzero
      refine ⟨fun _ => K₁, ?_, Or.inl ⟨?_, ?_⟩⟩
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
      · intro ε
        change Δ / (ε : ℝ) ^ 2 * bracket = 0
        rw [hBracketEq]
        ring
      · unfold AccuracyBigO
        simpa [K₁] using
          (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
            accuracyToZero)
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
      refine ⟨K, ?_, Or.inr hKBigO⟩
      intro ε
      unfold NonconvexAccuracy
      have hE1 := Theorem_E1_PP_MARINA_nonconvex (K := K ε) A x0
        Llocal ω fStar hLower hSmooth hQuantizer hClients hStep
      refine ⟨hE1.1, hE1.2.trans ?_⟩
      simpa [Δ] using hKBound ε

/-- PP-MARINA PŁ accuracy and iteration complexity, isolated from the
legacy scalar communication endpoint. -/
theorem ppPLAccuracyIterationComplexity
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
    let Δ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let factor := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
          (A.refreshProbability * r.1))))
    ∃ K : Accuracy → Count,
      (∀ ε, PLAccuracy (K ε) A.problem (ppProcess (r := r) A x0)
        (ppPathLaw (r := r) A) xStar ε) ∧
      AccuracyIterationBigO (fun ε => (K ε).1)
        (fun ε => factor * Real.log (Δ / (ε : ℝ))) := by
  have hGapNonneg : 0 ≤ globalObjective A.problem x0 -
      globalObjective A.problem xStar := sub_nonneg.mpr (hPL.1 x0)
  rcases hGapNonneg.eq_or_lt with hGap | hGap
  · dsimp
    let K₁ : Count := ⟨1, by norm_num⟩
    have hInitialZero : globalObjective A.problem x0 =
        globalObjective A.problem xStar := sub_eq_zero.mp hGap.symm
    refine ⟨fun _ => K₁, ?_, Or.inl ⟨?_, ?_⟩⟩
    · intro ε
      unfold PLAccuracy
      have hE2 := Theorem_E2_PP_MARINA_PL (K := K₁) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hClients hStep
      refine ⟨hE2.1, ?_⟩
      have hNonpos :
          (∫ path, globalObjective A.problem
              (ppProcess (r := r) A x0 K₁.1 path).x -
              globalObjective A.problem xStar ∂ppPathLaw (r := r) A) ≤ 0 := by
        rw [hInitialZero] at hE2
        simpa using hE2.2
      exact hNonpos.trans (le_of_lt ε.property)
    · intro ε
      rw [hInitialZero]
      simp
    · unfold AccuracyBigO
      simpa [K₁] using
        (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ))
          accuracyToZero)
  · dsimp
    let Δ : ℝ := globalObjective A.problem x0 - globalObjective A.problem xStar
    let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
    let factor : ℝ := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
          (A.refreshProbability * r.1))))
    have hp : 0 < A.refreshProbability := A.refresh_admissible.1
    have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
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
    refine ⟨K, ?_, Or.inr ?_⟩
    · intro ε
      unfold PLAccuracy
      have hE2 := Theorem_E2_PP_MARINA_PL (K := K ε) A x0 xStar
        Llocal ω fStar μ hLower hSmooth hPL hQuantizer hClients hStep
      refine ⟨hE2.1, hE2.2.trans ?_⟩
      simpa [c, Δ] using hContract ε
    · simpa [factor, Δ] using hKBigO

/-- Measured public root for PP-MARINA Theorems E.1 and E.2. -/
theorem Theorem_E1_E2_measured_communication_complexity
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hClients : PPBatchAdmissible n r)
    (hStepNonconvex : PPStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω r)
    (hStepPL : PPPLStepsizeCondition A.stepSize (rootMeanSquare Llocal)
      A.refreshProbability ω μ r) :
    let ζ := expectedDensity A.quantizer
    let Δnc := globalObjective A.problem x0 - fStar
    let bracket := rootMeanSquare Llocal *
      (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
        (A.refreshProbability * r.1)))
    let Δpl := globalObjective A.problem x0 - globalObjective A.problem xStar
    let factor := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
          (A.refreshProbability * r.1))))
    (∃ K : Accuracy → Count,
      PPMeasuredCommunicationComplexity (r := r) A x0 K
        (fun ε => NonconvexAccuracy (K ε) A.problem
          (ppProcess (r := r) A x0) (ppPathLaw (r := r) A) ε)
        (fun ε => Δnc / (ε : ℝ) ^ 2 * bracket)
        (fun ε => d.1 * n.1 + Δnc / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 * n.1 +
            (1 - A.refreshProbability) * ζ * r.1))) ∧
    (∃ K : Accuracy → Count,
      PPMeasuredCommunicationComplexity (r := r) A x0 K
        (fun ε => PLAccuracy (K ε) A.problem (ppProcess (r := r) A x0)
          (ppPathLaw (r := r) A) xStar ε)
        (fun ε => factor * Real.log (Δpl / (ε : ℝ)))
        (fun ε => d.1 * n.1 + factor *
          (A.refreshProbability * d.1 * n.1 +
            (1 - A.refreshProbability) * ζ * r.1) *
          Real.log (Δpl / (ε : ℝ)))) := by
  dsimp
  constructor
  · rcases ppNonconvexAccuracyIterationComplexity A x0 Llocal ω fStar
      hLower hSmooth hQuantizer hClients hStepNonconvex with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    apply ppMeasuredCommunicationComplexity_of_accuracy_iteration A x0 Llocal
      hSmooth hQuantizer K _ _ hK.1 hK.2
    exact Filter.Eventually.of_forall fun ε =>
      mul_nonneg
        (div_nonneg (sub_nonneg.mpr (hLower x0)) (sq_nonneg (ε : ℝ)))
        (mul_nonneg (Real.sqrt_nonneg _)
          (add_nonneg zero_le_one (Real.sqrt_nonneg _)))
  · rcases ppPLAccuracyIterationComplexity A x0 xStar Llocal
      ω fStar μ hLower hSmooth hPL hQuantizer hClients hStepPL with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    have hGapNonneg : 0 ≤ globalObjective A.problem x0 -
        globalObjective A.problem xStar := sub_nonneg.mpr (hPL.1 x0)
    have hFactorPos : 0 < max (1 / A.refreshProbability)
        (rootMeanSquare Llocal / μ *
          (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
            (A.refreshProbability * r.1)))) :=
      (div_pos zero_lt_one A.refresh_admissible.1).trans_le
        (le_max_left _ _)
    have hScaleNonneg : ∀ᶠ ε : Accuracy in accuracyToZero,
        0 ≤ max (1 / A.refreshProbability)
            (rootMeanSquare Llocal / μ *
              (1 + Real.sqrt ((1 - A.refreshProbability) * (1 + ω) /
                (A.refreshProbability * r.1)))) *
          Real.log ((globalObjective A.problem x0 -
            globalObjective A.problem xStar) / (ε : ℝ)) := by
      rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
      · exact Filter.Eventually.of_forall fun ε => by
          rw [show globalObjective A.problem x0 -
            globalObjective A.problem xStar = 0 from hGapZero.symm]
          simp
      · filter_upwards [eventually_one_le_log_gap_div_accuracy hGapPos]
          with ε hlog
        exact mul_nonneg hFactorPos.le (zero_le_one.trans hlog)
    have hMeasured :=
      ppMeasuredCommunicationComplexity_of_accuracy_iteration (r := r)
        A x0 Llocal hSmooth hQuantizer K _ _ hK.1 hK.2 hScaleNonneg
    convert hMeasured using 1
    funext ε
    ring

/-! ## Bounded-below generated refresh defect candidate

The earlier atomless-diagonal construction has a linear expected objective and
therefore does not satisfy Assumption 1.1.  Adding the same smooth quadratic to
every sampled loss leaves its sample-selected jump in place, while making the
expected objective bounded below.  The declarations below isolate that
source-hypothesis repair; they do not claim the final generated-process defect
until the modified process-level diagonal calculation has also been proved. -/

noncomputable def onlineGeneratedBoundedRefreshLoss
    (s : OnlineGeneratedRefreshSample 0) :
    Point oldInitialBoundCounterexampleDimension → ℝ :=
  fun x ↦ onlineGeneratedRefreshLoss s x + ‖x‖ ^ 2 / 2

noncomputable def onlineGeneratedBoundedRefreshProblem :
    OnlineProblem oldInitialBoundCounterexampleDimension
      onlineCoarseCounterexampleWorkers OnlineGeneratedRefreshSample where
  sampleLoss _ s := onlineGeneratedBoundedRefreshLoss s
  sampleLaw := onlineGeneratedRefreshProblem.sampleLaw
  sampleLaw_isProbability := onlineGeneratedRefreshProblem.sampleLaw_isProbability
  sampleLoss_integrable i x := by
    letI : IsProbabilityMeasure
        (onlineGeneratedRefreshProblem.sampleLaw i) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability i
    have hold : Integrable
        (fun s ↦ onlineGeneratedRefreshLoss s x)
        (onlineGeneratedRefreshProblem.sampleLaw i) :=
      onlineGeneratedRefreshProblem.sampleLoss_integrable i x
    have hquad : Integrable
        (fun _ : OnlineGeneratedRefreshSample i ↦ ‖x‖ ^ 2 / 2)
        (onlineGeneratedRefreshProblem.sampleLaw i) :=
      integrable_const (c := ‖x‖ ^ 2 / 2)
    simpa [onlineGeneratedBoundedRefreshLoss] using hold.add hquad

theorem onlineGeneratedBoundedRefresh_expectedSampleLoss
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    expectedSampleLoss onlineGeneratedBoundedRefreshProblem i x =
      10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) x +
        ‖x‖ ^ 2 / 2 := by
  letI : IsProbabilityMeasure
      (onlineGeneratedRefreshProblem.sampleLaw i) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability i
  have hold : Integrable
      (fun s ↦ onlineGeneratedRefreshLoss s x)
      (onlineGeneratedRefreshProblem.sampleLaw i) :=
    onlineGeneratedRefreshProblem.sampleLoss_integrable i x
  have hquad : Integrable
      (fun _ : OnlineGeneratedRefreshSample i ↦ ‖x‖ ^ 2 / 2)
      (onlineGeneratedRefreshProblem.sampleLaw i) :=
    integrable_const (c := ‖x‖ ^ 2 / 2)
  unfold expectedSampleLoss
  change (∫ s, (onlineGeneratedRefreshLoss s x + ‖x‖ ^ 2 / 2)
      ∂onlineGeneratedRefreshProblem.sampleLaw i) = _
  rw [integral_add hold hquad, integral_const, probReal_univ, one_smul]
  have hexpected := onlineGeneratedRefresh_expectedSampleLoss i x
  unfold expectedSampleLoss at hexpected
  change (∫ a : OnlineGeneratedRefreshSample 0,
      onlineGeneratedRefreshLoss a x
        ∂onlineGeneratedRefreshProblem.sampleLaw i) = _ at hexpected
  rw [hexpected]

theorem onlineGeneratedBoundedRefresh_quadratic_hasGradientAt
    (x : Point oldInitialBoundCounterexampleDimension) :
    HasGradientAt (fun y : Point oldInitialBoundCounterexampleDimension =>
      ‖y‖ ^ 2 / 2) x x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (2 : ℝ)⁻¹ using 1
  · funext z
    ring
  · ext z
    simp [InnerProductSpace.toDual_apply_apply]

theorem onlineGeneratedBoundedRefresh_expected_hasGradientAt
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    HasGradientAt
      ((onlineLocalProblem onlineGeneratedBoundedRefreshProblem).localLoss i)
      (10 • oldInitialBoundCounterexampleDirection + x) x := by
  have hfun :
      (onlineLocalProblem onlineGeneratedBoundedRefreshProblem).localLoss i =
        fun y => 10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) y +
          ‖y‖ ^ 2 / 2 := by
    funext y
    exact onlineGeneratedBoundedRefresh_expectedSampleLoss i y
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  have hlinear : HasFDerivAt
      (fun y : Point oldInitialBoundCounterexampleDimension =>
        10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) y)
      (InnerProductSpace.toDual ℝ _ (10 • oldInitialBoundCounterexampleDirection)) x := by
    convert (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt.const_mul 10
      using 1
    ext z
    simp [InnerProductSpace.toDual_apply_apply]
  have hquad :=
    (onlineGeneratedBoundedRefresh_quadratic_hasGradientAt x).hasFDerivAt
  convert hlinear.add hquad using 1
  ext z
  simp [InnerProductSpace.toDual_apply_apply]

theorem onlineGeneratedBoundedRefresh_localGradient
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    localGradient (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) i x =
      10 • oldInitialBoundCounterexampleDirection + x := by
  unfold localGradient
  exact (onlineGeneratedBoundedRefresh_expected_hasGradientAt i x).gradient

theorem onlineGeneratedBoundedRefresh_isLocallySmooth :
    IsLocallySmooth
      (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) (fun _ => 1) := by
  constructor
  · intro i x
    exact (onlineGeneratedBoundedRefresh_expected_hasGradientAt i x).differentiableAt
  · intro i x y
    rw [onlineGeneratedBoundedRefresh_localGradient i x,
      onlineGeneratedBoundedRefresh_localGradient i y]
    simp only [one_mul]
    rw [show 10 • oldInitialBoundCounterexampleDirection + x -
      (10 • oldInitialBoundCounterexampleDirection + y) = x - y by module]

theorem onlineGeneratedBoundedRefresh_globalGradient
    (x : Point oldInitialBoundCounterexampleDimension) :
    globalGradient (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) x =
      10 • oldInitialBoundCounterexampleDirection + x := by
  rw [globalGradient_eq_averageLocalGradient
    (onlineLocalProblem onlineGeneratedBoundedRefreshProblem)
    onlineGeneratedBoundedRefresh_isLocallySmooth.1 x]
  unfold averageLocalGradient average SOptLib.finiteUniformAverage
  norm_num [onlineGeneratedBoundedRefresh_localGradient,
    onlineCoarseCounterexampleWorkers]

theorem onlineGeneratedBoundedRefresh_add_quadratic_hasGradientAt
    {f : Point oldInitialBoundCounterexampleDimension → ℝ}
    {g x : Point oldInitialBoundCounterexampleDimension}
    (h : HasGradientAt f g x) :
    HasGradientAt (fun y => f y + ‖y‖ ^ 2 / 2) (g + x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hquad :=
    (onlineGeneratedBoundedRefresh_quadratic_hasGradientAt x).hasFDerivAt
  convert h.hasFDerivAt.add hquad using 1
  ext z
  simp [InnerProductSpace.toDual_apply_apply]

theorem onlineGeneratedBoundedRefreshLoss_gradient_at_query
    (s : OnlineGeneratedRefreshSample 0) (q : ℝ) :
    gradient (onlineGeneratedBoundedRefreshLoss s)
        (onlineCoarseCounterexamplePoint q) =
      if q = s.1.val then 0
      else onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection +
        onlineCoarseCounterexamplePoint q := by
  by_cases hq : q = s.1.val
  · subst q
    rw [if_pos rfl, gradient_eq_zero_of_not_differentiableAt]
    intro hdiff
    have hquad : DifferentiableAt ℝ
        (fun y : Point oldInitialBoundCounterexampleDimension => ‖y‖ ^ 2 / 2)
        (onlineCoarseCounterexamplePoint s.1.val) :=
      (onlineGeneratedBoundedRefresh_quadratic_hasGradientAt _).differentiableAt
    have holdDiff : DifferentiableAt ℝ (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint s.1.val) := by
      have hsub := hdiff.sub hquad
      convert hsub using 1
      funext y
      simp [onlineGeneratedBoundedRefreshLoss]
    have hcont : ContinuousAt (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint s.1.val) := holdDiff.continuousAt
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
      fun h => hq (onlineCoarseCounterexamplePoint_injective h)
    let base := onlineGeneratedRefreshSlope s •
      innerSL ℝ oldInitialBoundCounterexampleDirection
    have hevent : onlineGeneratedRefreshLoss s =ᶠ[
        nhds (onlineCoarseCounterexamplePoint q)] base := by
      filter_upwards [eventually_ne_nhds hpoint_ne] with y hy
      simp [onlineGeneratedRefreshLoss, base, Function.update_of_ne hy]
    have hbaseGradient : HasGradientAt base
        (onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint q) := by
      rw [hasGradientAt_iff_hasFDerivAt]
      convert (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt.const_smul
        (onlineGeneratedRefreshSlope s) using 1
      ext z
      simp [InnerProductSpace.toDual_apply_apply]
    have holdGradient : HasGradientAt (onlineGeneratedRefreshLoss s)
        (onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint q) :=
      hbaseGradient.congr_of_eventuallyEq hevent
    exact (onlineGeneratedBoundedRefresh_add_quadratic_hasGradientAt
      holdGradient).gradient

theorem onlineGeneratedBoundedRefresh_stochasticGradient_ae
    (x : Point oldInitialBoundCounterexampleDimension) :
    (fun s : OnlineGeneratedRefreshSample 0 =>
      stochasticGradient onlineGeneratedBoundedRefreshProblem 0 s x) =ᵐ[
        onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)]
      (fun s => onlineGeneratedRefreshSlope s •
        oldInitialBoundCounterexampleDirection + x) := by
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
  simpa [stochasticGradient, onlineGeneratedBoundedRefreshProblem, hne] using
    onlineGeneratedBoundedRefreshLoss_gradient_at_query s (x 0)

theorem onlineGeneratedBoundedRefresh_literalVariance :
    OnlineAssumption33Literal onlineGeneratedBoundedRefreshProblem
      (fun _ => 1) := by
  constructor
  · intro i
    norm_num
  · intro i x
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let μ := onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)
    let e := oldInitialBoundCounterexampleDirection
    have hold := onlineGeneratedRefresh_literalVariance.2 0 x
    have holdAE := onlineGeneratedRefresh_stochasticGradient_ae x
    have hnewAE := onlineGeneratedBoundedRefresh_stochasticGradient_ae x
    have hslopeVec : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 =>
          onlineGeneratedRefreshSlope s • e) μ := by
      exact hold.1.congr holdAE
    have hshift : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 =>
          onlineGeneratedRefreshSlope s • e + x) μ :=
      hslopeVec.add (integrable_const (c := x))
    have hgrad : Integrable
        (fun s => stochasticGradient onlineGeneratedBoundedRefreshProblem 0 s x)
        μ := hshift.congr hnewAE.symm
    have hresidualAE :
        (fun s =>
          ‖stochasticGradient onlineGeneratedBoundedRefreshProblem 0 s x -
            localGradient
              (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) 0 x‖ ^ 2)
          =ᵐ[μ]
        (fun s =>
          ‖stochasticGradient onlineGeneratedRefreshProblem 0 s x -
            localGradient (onlineLocalProblem onlineGeneratedRefreshProblem) 0 x‖ ^ 2) := by
      filter_upwards [hnewAE, holdAE] with s hnew hold
      rw [hnew, hold, onlineGeneratedBoundedRefresh_localGradient,
        onlineGeneratedRefresh_localGradient]
      congr 2
      module
    have hresidual : Integrable
        (fun s =>
          ‖stochasticGradient onlineGeneratedBoundedRefreshProblem 0 s x -
            localGradient
              (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) 0 x‖ ^ 2)
        μ := hold.2.1.congr hresidualAE.symm
    refine ⟨hgrad, hresidual, ?_, ?_⟩
    · change (∫ s : OnlineGeneratedRefreshSample 0,
          stochasticGradient onlineGeneratedBoundedRefreshProblem 0 s x ∂μ) = _
      rw [integral_congr_ae hnewAE, integral_add hslopeVec
        (integrable_const (c := x)), integral_const]
      have hμ : μ.real Set.univ = 1 := by
        simp [μ]
      rw [hμ, one_smul]
      have holdMean := hold.2.2.1
      change (∫ s : OnlineGeneratedRefreshSample 0,
          stochasticGradient onlineGeneratedRefreshProblem 0 s x ∂μ) = _ at holdMean
      rw [integral_congr_ae holdAE] at holdMean
      rw [holdMean, onlineGeneratedRefresh_localGradient,
        onlineGeneratedBoundedRefresh_localGradient]
    · change (∫ s : OnlineGeneratedRefreshSample 0,
          ‖stochasticGradient onlineGeneratedBoundedRefreshProblem 0 s x -
            localGradient
              (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) 0 x‖ ^ 2
          ∂μ) ≤ 1 ^ 2
      rw [integral_congr_ae hresidualAE]
      exact hold.2.2.2

theorem onlineGeneratedBoundedDifference_ae_eq_sub
    (x y : Point oldInitialBoundCounterexampleDimension) :
    (fun batch => onlineBatchDifference onlineGeneratedBoundedRefreshProblem
      batch 0 x y) =ᵐ[
        onlineBatchLaw onlineGeneratedBoundedRefreshProblem
          onlineGeneratedDifferenceBatch]
      (fun _ => x - y) := by
  let coord := fun batch :
      (w : Worker onlineCoarseCounterexampleWorkers) →
        Fin onlineGeneratedDifferenceBatch.1 → OnlineGeneratedRefreshSample w =>
    batch 0 0
  have hcoord : Measurable coord := by
    dsimp [coord]
    fun_prop
  have hmap : Measure.map coord
      (onlineBatchLaw onlineGeneratedBoundedRefreshProblem
        onlineGeneratedDifferenceBatch) =
      onlineGeneratedBoundedRefreshProblem.sampleLaw 0 := by
    simpa [coord] using
      (onlineBatchLaw_coordinate_marginal onlineGeneratedBoundedRefreshProblem
        (b := onlineGeneratedDifferenceBatch) 0 0)
  have hqmp : Measure.QuasiMeasurePreserving coord
      (onlineBatchLaw onlineGeneratedBoundedRefreshProblem
        onlineGeneratedDifferenceBatch)
      (onlineGeneratedBoundedRefreshProblem.sampleLaw 0) :=
    ⟨hcoord, by rw [hmap]⟩
  have hx := hqmp.tendsto_ae
    (onlineGeneratedBoundedRefresh_stochasticGradient_ae x)
  have hy := hqmp.tendsto_ae
    (onlineGeneratedBoundedRefresh_stochasticGradient_ae y)
  filter_upwards [hx, hy] with batch hx hy
  change stochasticGradient onlineGeneratedBoundedRefreshProblem 0
      (batch 0 0) x =
    onlineGeneratedRefreshSlope (batch 0 0) •
      oldInitialBoundCounterexampleDirection + x at hx
  change stochasticGradient onlineGeneratedBoundedRefreshProblem 0
      (batch 0 0) y =
    onlineGeneratedRefreshSlope (batch 0 0) •
      oldInitialBoundCounterexampleDirection + y at hy
  unfold onlineBatchDifference average SOptLib.finiteUniformAverage
  rw [Fin.sum_univ_one, hx, hy]
  norm_num

theorem onlineGeneratedBoundedRefresh_averageSmoothness
    {Ω : Type*} [MeasurableSpace Ω]
    (run : ℕ → Ω → State oldInitialBoundCounterexampleDimension) :
    OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
      onlineGeneratedBoundedRefreshProblem run (fun _ => 0) := by
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedBoundedRefreshProblem.sampleLaw w) :=
    onlineGeneratedBoundedRefreshProblem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedBoundedRefreshProblem
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
    have hdiff := onlineGeneratedBoundedDifference_ae_eq_sub xNext x
    have hlocal : localGradientDifference
        (onlineLocalProblem onlineGeneratedBoundedRefreshProblem)
          0 xNext x = xNext - x := by
      unfold localGradientDifference
      rw [onlineGeneratedBoundedRefresh_localGradient 0 xNext,
        onlineGeneratedBoundedRefresh_localGradient 0 x]
      module
    have hint : Integrable
        (fun batch => onlineBatchDifference
          onlineGeneratedBoundedRefreshProblem batch 0 xNext x)
        (onlineBatchLaw onlineGeneratedBoundedRefreshProblem
          onlineGeneratedDifferenceBatch) :=
      (integrable_const (c := xNext - x)).congr hdiff.symm
    have hsqAE :
        (fun batch =>
          ‖onlineBatchDifference onlineGeneratedBoundedRefreshProblem batch
              0 xNext x -
            localGradientDifference
              (onlineLocalProblem onlineGeneratedBoundedRefreshProblem)
              0 xNext x‖ ^ 2) =ᵐ[
          onlineBatchLaw onlineGeneratedBoundedRefreshProblem
            onlineGeneratedDifferenceBatch]
          (fun _ => 0) := by
      filter_upwards [hdiff] with batch hb
      simp [hb, hlocal]
    have hsq : Integrable
        (fun batch =>
          ‖onlineBatchDifference onlineGeneratedBoundedRefreshProblem batch
              0 xNext x -
            localGradientDifference
              (onlineLocalProblem onlineGeneratedBoundedRefreshProblem)
              0 xNext x‖ ^ 2)
        (onlineBatchLaw onlineGeneratedBoundedRefreshProblem
          onlineGeneratedDifferenceBatch) :=
      (integrable_const (c := (0 : ℝ))).congr hsqAE.symm
    refine ⟨hint, hsq, ?_, ?_⟩
    · rw [integral_congr_ae hdiff, hlocal]
      simp
    · rw [integral_congr_ae hsqAE]
      simp

theorem onlineGeneratedBoundedRefresh_globalObjective
    (x : Point oldInitialBoundCounterexampleDimension) :
    globalObjective (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) x =
      10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) x +
        ‖x‖ ^ 2 / 2 := by
  unfold globalObjective average SOptLib.finiteUniformAverage onlineLocalProblem
  norm_num [onlineGeneratedBoundedRefresh_expectedSampleLoss,
    onlineCoarseCounterexampleWorkers]

noncomputable def onlineGeneratedBoundedRefreshMinimizer :
    Point oldInitialBoundCounterexampleDimension :=
  (-10 : ℝ) • oldInitialBoundCounterexampleDirection

theorem onlineGeneratedBoundedRefresh_objective_minimizer :
    globalObjective (onlineLocalProblem onlineGeneratedBoundedRefreshProblem)
      onlineGeneratedBoundedRefreshMinimizer = -50 := by
  rw [onlineGeneratedBoundedRefresh_globalObjective]
  have hinner :
      (innerSL ℝ oldInitialBoundCounterexampleDirection)
        onlineGeneratedBoundedRefreshMinimizer = -10 := by
    rw [onlineGeneratedBoundedRefreshMinimizer, map_smul]
    norm_num [oldInitialBoundCounterexampleDirection,
      innerSL_apply_apply, PiLp.inner_apply]
  have hnorm : ‖onlineGeneratedBoundedRefreshMinimizer‖ ^ 2 = 100 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
    norm_num [onlineGeneratedBoundedRefreshMinimizer,
      oldInitialBoundCounterexampleDirection]
  rw [hinner, hnorm]
  norm_num

theorem onlineGeneratedBoundedRefresh_gradient_norm_sq
    (x : Point oldInitialBoundCounterexampleDimension) :
    ‖globalGradient (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) x‖ ^ 2 =
      (x 0 + 10) ^ 2 := by
  rw [onlineGeneratedBoundedRefresh_globalGradient,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
  simp [oldInitialBoundCounterexampleDirection, Real.norm_eq_abs, sq_abs]
  ring

theorem onlineGeneratedBoundedRefresh_satisfiesPL :
    SatisfiesPL (onlineLocalProblem onlineGeneratedBoundedRefreshProblem)
      ⟨1, by norm_num⟩ onlineGeneratedBoundedRefreshMinimizer := by
  constructor
  · intro x
    rw [onlineGeneratedBoundedRefresh_objective_minimizer,
      onlineGeneratedBoundedRefresh_globalObjective]
    have hs : 0 ≤ (x 0 + 10) ^ 2 := sq_nonneg (x 0 + 10)
    have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    rw [show (innerSL ℝ oldInitialBoundCounterexampleDirection) x = x 0 by
      change inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0
      simp only [PiLp.inner_apply]
      rw [Fin.sum_univ_one, real_inner_eq_re_inner ℝ, RCLike.inner_apply]
      simp]
    nlinarith
  · intro x
    rw [onlineGeneratedBoundedRefresh_objective_minimizer,
      onlineGeneratedBoundedRefresh_globalObjective,
      onlineGeneratedBoundedRefresh_gradient_norm_sq]
    have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    rw [show (innerSL ℝ oldInitialBoundCounterexampleDirection) x = x 0 by
      change inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0
      simp only [PiLp.inner_apply]
      rw [Fin.sum_univ_one]
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
      simp]
    norm_num
    ring_nf
    exact le_rfl

theorem onlineGeneratedBoundedRefresh_hasUniformLowerBound :
    HasUniformLowerBound
      (onlineLocalProblem onlineGeneratedBoundedRefreshProblem) (-50) := by
  intro x
  rw [onlineGeneratedBoundedRefresh_globalObjective]
  have hs : 0 ≤ (x 0 + 10) ^ 2 := sq_nonneg (x 0 + 10)
  have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_one]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  rw [show (innerSL ℝ oldInitialBoundCounterexampleDirection) x = x 0 by
    change inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0
    simp only [PiLp.inner_apply]
    rw [Fin.sum_univ_one]
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
    simp]
  nlinarith

noncomputable def onlineGeneratedBoundedRefreshData :
    OnlineData oldInitialBoundCounterexampleDimension
      onlineCoarseCounterexampleWorkers OnlineGeneratedRefreshSample Unit where
  problem := onlineGeneratedBoundedRefreshProblem
  quantizer := onlineGeneratedIdentityQuantizer
  stepSize := ⟨1, by norm_num⟩
  refreshProbability := 1
  refresh_admissible := by constructor <;> norm_num

noncomputable def onlineGeneratedBoundedRefreshInitialPoint :
    Point oldInitialBoundCounterexampleDimension := 0

theorem onlineGeneratedBoundedRefresh_proofExact_x_one
    (path : ℕ → OnlineRoundNoise onlineCoarseCounterexampleWorkers
      onlineGeneratedRefreshBatch onlineGeneratedDifferenceBatch
      OnlineGeneratedRefreshSample Unit) :
    (onlineProofExactProcess onlineGeneratedBoundedRefreshData
      onlineGeneratedBoundedRefreshInitialPoint
      onlineGeneratedRefresh_batchAdmissible 1 path).x =
        onlineGeneratedBoundedRefreshMinimizer := by
  change (onlineStep onlineGeneratedBoundedRefreshData
    (onlineDriverOfRoundNoise (path 0))
    (onlineProofExactInitialState onlineGeneratedBoundedRefreshData
      onlineGeneratedBoundedRefreshInitialPoint)).x = _
  change onlineGeneratedBoundedRefreshInitialPoint -
      (onlineGeneratedBoundedRefreshData.stepSize : ℝ) •
        globalGradient
          (onlineLocalProblem onlineGeneratedBoundedRefreshData.problem)
          onlineGeneratedBoundedRefreshInitialPoint = _
  rw [show globalGradient
      (onlineLocalProblem onlineGeneratedBoundedRefreshData.problem)
      onlineGeneratedBoundedRefreshInitialPoint =
        10 • oldInitialBoundCounterexampleDirection by
      change globalGradient
        (onlineLocalProblem onlineGeneratedBoundedRefreshProblem)
        onlineGeneratedBoundedRefreshInitialPoint = _
      rw [onlineGeneratedBoundedRefresh_globalGradient]
      simp [onlineGeneratedBoundedRefreshInitialPoint]]
  dsimp [onlineGeneratedBoundedRefreshData,
    onlineGeneratedBoundedRefreshInitialPoint,
    onlineGeneratedBoundedRefreshMinimizer]
  module

/-! ## Source-faithful conditional-kernel form of Assumption 3.2 -/

/-- Source Assumption 3.2 on a generated process, stated as a genuine-gradient
conditional kernel under the exact generated path law and one independent
minibatch law.

The first clause makes the conditioning variables `(x^k,x^{k+1})` genuine
random variables.  For every round and worker, `delta` is one jointly
law-a.e.-measurable path-by-batch version of the displayed genuine minibatch
gradient difference.  Its fixed-path fibers then have exactly the conditional
mean and conditional second-moment bound of Eq. (8).  In particular, this is
strictly stronger than `OnlineAssumption32GenuineAE`, which selects unrelated
batch-fiber witnesses after fixing a path and therefore does not by itself
state joint measurability of the source random variable. -/
def OnlineAssumption32GeneratedConditionalKernel {d n b0 : Count}
    {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k, AEStronglyMeasurable
      (fun path ↦ ((run k path).x, (run (k + 1) path).x)) pathLaw) ∧
    (∀ k i, ∃ delta : Ω ×
        ((w : Worker n) → Fin b0.1 → Sample w) → Point d,
      AEStronglyMeasurable delta
        (pathLaw.prod (onlineBatchLaw P b0)) ∧
      (∀ᵐ p ∂pathLaw.prod (onlineBatchLaw P b0),
        GenuineOnlineBatchDifferenceAt P p.2 i
          (run (k + 1) p.1).x (run k p.1).x (delta p)) ∧
      (∀ᵐ path ∂pathLaw,
        Integrable (fun batch ↦ delta (path, batch))
            (onlineBatchLaw P b0) ∧
          Integrable (fun batch ↦
            ‖delta (path, batch) -
              localGradientDifference (onlineLocalProblem P) i
                (run (k + 1) path).x (run k path).x‖ ^ 2)
            (onlineBatchLaw P b0) ∧
          (∫ batch, delta (path, batch) ∂onlineBatchLaw P b0) =
            localGradientDifference (onlineLocalProblem P) i
              (run (k + 1) path).x (run k path).x ∧
          (∫ batch,
              ‖delta (path, batch) -
                localGradientDifference (onlineLocalProblem P) i
                  (run (k + 1) path).x (run k path).x‖ ^ 2
              ∂onlineBatchLaw P b0) ≤
            (ℒ i) ^ 2 / b0.1 *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2))

/-- Forgetting joint measurability from the source conditional kernel yields
the existing law-a.e. genuine-gradient fiber interface on the same problem,
process, path law, rounds, workers, queries, and minibatch law. -/
theorem onlineAssumption32GeneratedConditionalKernel_to_genuineAE
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {pathLaw : Measure Ω} {ℒ : Worker n → ℝ}
    (h : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ) :
    OnlineAssumption32GenuineAE (b0 := b0) P run pathLaw ℒ := by
  letI (w : Worker n) : IsProbabilityMeasure (P.sampleLaw w) :=
    P.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw P b0) := by
    unfold onlineBatchLaw
    infer_instance
  refine ⟨h.1, ?_⟩
  intro k
  apply ae_all_iff.2
  intro i
  rcases h.2.2 k i with ⟨delta, _hdelta, hGenuine, hFibers⟩
  have hGenuineFibers : ∀ᵐ path ∂pathLaw,
      ∀ᵐ batch ∂onlineBatchLaw P b0,
        GenuineOnlineBatchDifferenceAt P batch i
          (run (k + 1) path).x (run k path).x (delta (path, batch)) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hGenuine
  filter_upwards [hGenuineFibers, hFibers] with path hGenuinePath hFiber
  exact ⟨fun batch ↦ delta (path, batch), hGenuinePath,
    hFiber.1, hFiber.2.1, hFiber.2.2.1, hFiber.2.2.2⟩

/-- Source-to-recurrence transfer for the conditional-kernel formulation.
The transfer changes only the genuine-gradient representative to the existing
totalized `onlineBatchDifference`, using the already proved a.e.
identification; all generated objects and conditional moments are unchanged. -/
theorem onlineAssumption32GeneratedConditionalKernel_to_averageSmoothnessAE
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {pathLaw : Measure Ω} {ℒ : Worker n → ℝ}
    (h : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ) :
    OnlineAverageSmoothnessAE (b0 := b0) P run pathLaw ℒ :=
  onlineAssumption32GenuineAE_to_onlineAverageSmoothnessAE
    (onlineAssumption32GeneratedConditionalKernel_to_genuineAE h)

/-- The source conditional kernel already makes the *actual* formal
`onlineBatchDifference` at the generated consecutive queries a jointly
law-a.e.-measurable random vector.  This keeps the joint information that is
intentionally forgotten by `OnlineAverageSmoothnessAE` and uses no adaptive
sample-gradient regularity correction: the only object change is the proved
a.e. identification of the genuine source minibatch with the totalized formal
minibatch. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_batchDifference_joint_aestronglyMeasurable
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {pathLaw : Measure Ω} {ℒ : Worker n → ℝ}
    (h : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ) (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Ω × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        onlineBatchDifference P p.2 i
          (run (k + 1) p.1).x (run k p.1).x)
      (pathLaw.prod (onlineBatchLaw P b0)) := by
  rcases h.2.2 k i with ⟨delta, hdelta, hGenuine, _hFibers⟩
  have hEq :
      (fun p : Ω × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        onlineBatchDifference P p.2 i
          (run (k + 1) p.1).x (run k p.1).x) =ᵐ[
            pathLaw.prod (onlineBatchLaw P b0)] delta :=
    hGenuine.mono (fun _ hp ↦
      onlineBatchDifference_eq_of_genuineOnlineBatchDifferenceAt hp)
  exact hdelta.congr hEq.symm

/-- Averaging the preceding source-derived jointly measurable minibatch
differences over workers preserves joint measurability.  This is the exact
uncompressed stochastic-difference object in Algorithm 3's non-refresh
branch, still under the same generated path and `b⁰` minibatch law. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_averageBatchDifference_joint_aestronglyMeasurable
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {pathLaw : Measure Ω} {ℒ : Worker n → ℝ}
    (h : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ) (k : ℕ) :
    AEStronglyMeasurable
      (fun p : Ω × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        average (fun i : Worker n ↦ onlineBatchDifference P p.2 i
          (run (k + 1) p.1).x (run k p.1).x))
      (pathLaw.prod (onlineBatchLaw P b0)) := by
  classical
  unfold average SOptLib.finiteUniformAverage
  have hsum := Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ ↦
      onlineAssumption32GeneratedConditionalKernel_batchDifference_joint_aestronglyMeasurable
        h k i)
  refine (hsum.const_smul ((Fintype.card (Worker n) : ℝ)⁻¹)).congr
    (Filter.Eventually.of_forall ?_)
  intro p
  simp [Finset.sum_apply]

/-- Joint a.e. strong measurability of a kernel depending on one worker row
descends from the complete online minibatch law to that worker's canonical
finite product law.  The proof splits the dependent worker product at the
selected worker, removes the nonzero complementary product, and identifies
the remaining singleton dependent coordinate with the worker row. -/
theorem aestronglyMeasurable_worker_row_of_onlineBatchLaw
    {d n b0 : Count} {Q E : Type*}
    {Sample : Worker n → Type*}
    [MeasurableSpace Q] [TopologicalSpace E]
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (pathLaw : Measure Q)
    [SFinite pathLaw] (i : Worker n)
    (f : Q → (Fin b0.1 → Sample i) → E)
    (h : AEStronglyMeasurable
      (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        f p.1 (p.2 i))
      (pathLaw.prod (onlineBatchLaw P b0))) :
    AEStronglyMeasurable (fun p : Q × (Fin b0.1 → Sample i) ↦
      f p.1 p.2)
      (pathLaw.prod
        (Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw i))) := by
  classical
  let Row := fun w : Worker n ↦ Fin b0.1 → Sample w
  letI : Fintype {w : Worker n // w = i} :=
    Subtype.fintype (fun w : Worker n ↦ w = i)
  letI : Fintype {w : Worker n // ¬ w = i} :=
    Subtype.fintype (fun w : Worker n ↦ ¬ w = i)
  let rowLaw := fun w : Worker n ↦
    Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw w)
  let fullLaw : Measure ((w : Worker n) → Row w) := Measure.pi rowLaw
  let selectedLaw : Measure ((w : {w : Worker n // w = i}) → Row w.1) :=
    Measure.pi (fun w : {w : Worker n // w = i} ↦ rowLaw w.1)
  let restLaw : Measure ((w : {w : Worker n // ¬ w = i}) → Row w.1) :=
    Measure.pi (fun w : {w : Worker n // ¬ w = i} ↦ rowLaw w.1)
  let e := MeasurableEquiv.piEquivPiSubtypeProd Row
    (fun w : Worker n ↦ w = i)
  haveI (w : Worker n) : IsProbabilityMeasure (P.sampleLaw w) :=
    P.sampleLaw_isProbability w
  haveI (w : Worker n) : IsProbabilityMeasure (rowLaw w) := by
    dsimp [rowLaw]
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  haveI : Subsingleton {w : Worker n // w = i} :=
    ⟨fun a b ↦ by
      apply Subtype.ext
      exact a.2.trans b.2.symm⟩
  let wi : {w : Worker n // w = i} := ⟨i, rfl⟩
  let selectedEquiv :
      ((w : {w : Worker n // w = i}) → Row w.1) ≃ᵐ Row i :=
    { toFun := fun q ↦ q wi
      invFun := fun row w ↦ _root_.cast (congrArg Row w.2.symm) row
      left_inv := fun q ↦ by
        funext w
        have hw : w = wi := Subsingleton.elim _ _
        subst w
        simp
      right_inv := fun row ↦ by simp [wi]
      measurable_toFun := measurable_pi_apply wi
      measurable_invFun := by
        apply measurable_pi_lambda
        intro w
        rcases w with ⟨w, hw⟩
        subst w
        simpa using (measurable_id : Measurable (fun row : Row i ↦ row)) }
  have hfull : onlineBatchLaw P b0 = fullLaw := by
    simp [onlineBatchLaw, fullLaw, rowLaw,
      MeasureTheory.Measure.infinitePi_eq_pi]
  have hsplit : MeasurePreserving e fullLaw (selectedLaw.prod restLaw) := by
    simpa [e, fullLaw, selectedLaw, restLaw] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun w : Worker n ↦ rowLaw w)
        (fun w : Worker n ↦ w = i))
  have hsplitSymm : MeasurePreserving e.symm
      (selectedLaw.prod restLaw) fullLaw :=
    MeasurePreserving.symm e hsplit
  have hOnSplit : AEStronglyMeasurable
      (fun p : Q ×
          (((w : {w : Worker n // w = i}) → Row w.1) ×
            ((w : {w : Worker n // ¬ w = i}) → Row w.1)) ↦
        f p.1 ((e.symm p.2) i))
      (pathLaw.prod (selectedLaw.prod restLaw)) := by
    have hFull : AEStronglyMeasurable
        (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
          f p.1 (p.2 i)) (pathLaw.prod fullLaw) := by
      rw [← hfull]
      exact h
    have h' := hFull.comp_measurePreserving
      ((MeasurePreserving.id pathLaw).prod hsplitSymm)
    simpa [Function.comp_def] using h'
  have hcoord (q :
      ((w : {w : Worker n // w = i}) → Row w.1) ×
        ((w : {w : Worker n // ¬ w = i}) → Row w.1)) :
      (e.symm q) i = selectedEquiv q.1 := by
    simp [e, selectedEquiv, wi]
  have hOnSplit' : AEStronglyMeasurable
      (fun p : Q ×
          (((w : {w : Worker n // w = i}) → Row w.1) ×
            ((w : {w : Worker n // ¬ w = i}) → Row w.1)) ↦
        f p.1 (selectedEquiv p.2.1))
      (pathLaw.prod (selectedLaw.prod restLaw)) :=
    hOnSplit.congr (Filter.Eventually.of_forall fun p ↦ by
      change f p.1 ((e.symm p.2) i) = f p.1 (selectedEquiv p.2.1)
      rw [hcoord p.2])
  have hassoc : MeasurePreserving
      (fun p :
          (Q × ((w : {w : Worker n // w = i}) → Row w.1)) ×
            ((w : {w : Worker n // ¬ w = i}) → Row w.1) ↦
        (p.1.1, (p.1.2, p.2)))
      ((pathLaw.prod selectedLaw).prod restLaw)
      (pathLaw.prod (selectedLaw.prod restLaw)) := by
    simpa using MeasureTheory.measurePreserving_prodAssoc
      pathLaw selectedLaw restLaw
  have hWithRest : AEStronglyMeasurable
      (fun p :
          (Q × ((w : {w : Worker n // w = i}) → Row w.1)) ×
            ((w : {w : Worker n // ¬ w = i}) → Row w.1) ↦
        f p.1.1 (selectedEquiv p.1.2))
      ((pathLaw.prod selectedLaw).prod restLaw) := by
    simpa [Function.comp_def] using
      hOnSplit'.comp_measurePreserving hassoc
  have hrest_ne : restLaw ≠ 0 := by
    intro hz
    have huniv : restLaw Set.univ = 1 := measure_univ
    rw [hz] at huniv
    simp at huniv
  have hSelected : AEStronglyMeasurable
      (fun p : Q ×
          ((w : {w : Worker n // w = i}) → Row w.1) ↦
        f p.1 (selectedEquiv p.2))
      (pathLaw.prod selectedLaw) := by
    exact MeasureTheory.AEStronglyMeasurable.of_comp_fst hWithRest hrest_ne
  have hsingle : MeasurePreserving selectedEquiv selectedLaw (rowLaw i) := by
    refine ⟨selectedEquiv.measurable, ?_⟩
    change Measure.map (fun q ↦ q wi) selectedLaw = rowLaw i
    dsimp [selectedLaw]
    rw [MeasureTheory.Measure.pi_map_eval]
    simp [wi]
  have hsingleSymm : MeasurePreserving selectedEquiv.symm
      (rowLaw i) selectedLaw :=
    MeasurePreserving.symm selectedEquiv hsingle
  have hResult := hSelected.comp_measurePreserving
    ((MeasurePreserving.id pathLaw).prod hsingleSymm)
  simpa [rowLaw, Function.comp_def] using hResult

/-- An almost-everywhere fact about one worker row under the complete online
minibatch law descends to that row's canonical finite product law.  Unlike a
pushforward argument through `ae_map_iff`, this statement does not require the
predicate to be measurable: the unused worker rows are split off explicitly
and then removed using their nonzero probability law. -/
theorem ae_worker_row_of_onlineBatchLaw
    {n b0 : Count} {Q : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Q] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (pathLaw : Measure Q)
    [SFinite pathLaw] (i : Worker n)
    (p : Q → (Fin b0.1 → Sample i) → Prop)
    (h : ∀ᵐ z ∂pathLaw.prod (onlineBatchLaw P b0), p z.1 (z.2 i)) :
    ∀ᵐ z ∂pathLaw.prod
      (Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw i)), p z.1 z.2 := by
  classical
  let Row := fun w : Worker n ↦ Fin b0.1 → Sample w
  letI : Fintype {w : Worker n // w = i} :=
    Subtype.fintype (fun w : Worker n ↦ w = i)
  letI : Fintype {w : Worker n // ¬ w = i} :=
    Subtype.fintype (fun w : Worker n ↦ ¬ w = i)
  let rowLaw := fun w : Worker n ↦
    Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw w)
  let fullLaw : Measure ((w : Worker n) → Row w) := Measure.pi rowLaw
  let selectedLaw : Measure ((w : {w : Worker n // w = i}) → Row w.1) :=
    Measure.pi (fun w : {w : Worker n // w = i} ↦ rowLaw w.1)
  let restLaw : Measure ((w : {w : Worker n // ¬ w = i}) → Row w.1) :=
    Measure.pi (fun w : {w : Worker n // ¬ w = i} ↦ rowLaw w.1)
  let e := MeasurableEquiv.piEquivPiSubtypeProd Row
    (fun w : Worker n ↦ w = i)
  haveI (w : Worker n) : IsProbabilityMeasure (P.sampleLaw w) :=
    P.sampleLaw_isProbability w
  haveI (w : Worker n) : IsProbabilityMeasure (rowLaw w) := by
    dsimp [rowLaw]
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  haveI : Subsingleton {w : Worker n // w = i} :=
    ⟨fun a b ↦ by
      apply Subtype.ext
      exact a.2.trans b.2.symm⟩
  let wi : {w : Worker n // w = i} := ⟨i, rfl⟩
  let selectedEquiv :
      ((w : {w : Worker n // w = i}) → Row w.1) ≃ᵐ Row i :=
    { toFun := fun q ↦ q wi
      invFun := fun row w ↦ _root_.cast (congrArg Row w.2.symm) row
      left_inv := fun q ↦ by
        funext w
        have hw : w = wi := Subsingleton.elim _ _
        subst w
        simp
      right_inv := fun row ↦ by simp [wi]
      measurable_toFun := measurable_pi_apply wi
      measurable_invFun := by
        apply measurable_pi_lambda
        intro w
        rcases w with ⟨w, hw⟩
        subst w
        simpa using (measurable_id : Measurable (fun row : Row i ↦ row)) }
  have hfull : onlineBatchLaw P b0 = fullLaw := by
    simp [onlineBatchLaw, fullLaw, rowLaw,
      MeasureTheory.Measure.infinitePi_eq_pi]
  have hsplit : MeasurePreserving e fullLaw (selectedLaw.prod restLaw) := by
    simpa [e, fullLaw, selectedLaw, restLaw] using
      (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
        (fun w : Worker n ↦ rowLaw w)
        (fun w : Worker n ↦ w = i))
  have hsplitSymm : MeasurePreserving e.symm
      (selectedLaw.prod restLaw) fullLaw :=
    MeasurePreserving.symm e hsplit
  have hOnSplit : ∀ᵐ z ∂pathLaw.prod (selectedLaw.prod restLaw),
      p z.1 ((e.symm z.2) i) := by
    have hFull : ∀ᵐ z ∂pathLaw.prod fullLaw, p z.1 (z.2 i) := by
      rw [← hfull]
      exact h
    have hPull := ((MeasurePreserving.id pathLaw).prod hsplitSymm).quasiMeasurePreserving.tendsto_ae hFull
    simpa [Function.comp_def] using hPull
  have hcoord (q :
      ((w : {w : Worker n // w = i}) → Row w.1) ×
        ((w : {w : Worker n // ¬ w = i}) → Row w.1)) :
      (e.symm q) i = selectedEquiv q.1 := by
    simp [e, selectedEquiv, wi]
  have hOnSplit' : ∀ᵐ z ∂pathLaw.prod (selectedLaw.prod restLaw),
      p z.1 (selectedEquiv z.2.1) :=
    hOnSplit.mono (fun z hz ↦ by simpa [hcoord z.2] using hz)
  have hassoc : MeasurePreserving
      (fun z :
          (Q × ((w : {w : Worker n // w = i}) → Row w.1)) ×
            ((w : {w : Worker n // ¬ w = i}) → Row w.1) ↦
        (z.1.1, (z.1.2, z.2)))
      ((pathLaw.prod selectedLaw).prod restLaw)
      (pathLaw.prod (selectedLaw.prod restLaw)) := by
    simpa using MeasureTheory.measurePreserving_prodAssoc
      pathLaw selectedLaw restLaw
  have hWithRest : ∀ᵐ z ∂(pathLaw.prod selectedLaw).prod restLaw,
      p z.1.1 (selectedEquiv z.1.2) := by
    have hPull := hassoc.quasiMeasurePreserving.tendsto_ae hOnSplit'
    simpa [Function.comp_def] using hPull
  have hSelected : ∀ᵐ z ∂pathLaw.prod selectedLaw,
      p z.1 (selectedEquiv z.2) := by
    have hFibers := MeasureTheory.Measure.ae_ae_of_ae_prod hWithRest
    filter_upwards [hFibers] with z hz
    exact (hz.exists).choose_spec
  have hsingle : MeasurePreserving selectedEquiv selectedLaw (rowLaw i) := by
    refine ⟨selectedEquiv.measurable, ?_⟩
    change Measure.map (fun q ↦ q wi) selectedLaw = rowLaw i
    dsimp [selectedLaw]
    rw [MeasureTheory.Measure.pi_map_eval]
    simp [wi]
  have hsingleSymm : MeasurePreserving selectedEquiv.symm
      (rowLaw i) selectedLaw :=
    MeasurePreserving.symm selectedEquiv hsingle
  have hResult := ((MeasurePreserving.id pathLaw).prod hsingleSymm).quasiMeasurePreserving.tendsto_ae hSelected
  filter_upwards [hResult] with z hz
  simpa [Function.comp_def] using hz

/-- Replacing one coordinate of an iid row by a fresh sample shows that an
arbitrary almost-everywhere row-coordinate fact already holds under the
single-sample product law.  The proof again avoids any measurability premise
on the proposition. -/
theorem ae_singleSample_of_iid_row_coordinate
    {b0 : Count} {Q Sample : Type*}
    [MeasurableSpace Q] [MeasurableSpace Sample]
    (pathLaw : Measure Q) (sampleLaw : Measure Sample)
    [SFinite pathLaw] [IsProbabilityMeasure sampleLaw]
    (j0 : Fin b0.1) (p : Q → Sample → Prop)
    (h : ∀ᵐ z ∂pathLaw.prod
      (Measure.pi (fun _ : Fin b0.1 ↦ sampleLaw)), p z.1 (z.2 j0)) :
    ∀ᵐ z ∂pathLaw.prod sampleLaw, p z.1 z.2 := by
  classical
  let rowLaw : Measure (Fin b0.1 → Sample) :=
    Measure.pi (fun _ : Fin b0.1 ↦ sampleLaw)
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    infer_instance
  have hUpdate := measurePreserving_update_coordinate_prod_pi sampleLaw j0
  have hPull : ∀ᵐ z ∂pathLaw.prod (rowLaw.prod sampleLaw),
      p z.1 ((Function.update z.2.1 j0 z.2.2) j0) := by
    have h' : ∀ᵐ z ∂pathLaw.prod rowLaw, p z.1 (z.2 j0) := by
      simpa [rowLaw] using h
    have hResult := ((MeasurePreserving.id pathLaw).prod hUpdate).quasiMeasurePreserving.tendsto_ae h'
    simpa [Function.comp_def] using hResult
  have hswap : MeasurePreserving
      (fun z : Sample × (Fin b0.1 → Sample) ↦ (z.2, z.1))
      (sampleLaw.prod rowLaw) (rowLaw.prod sampleLaw) := by
    simpa using
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := sampleLaw) (ν := rowLaw))
  have hinner := (MeasurePreserving.id pathLaw).prod hswap
  have hassoc := MeasureTheory.measurePreserving_prodAssoc
    pathLaw sampleLaw rowLaw
  have hReordered : MeasurePreserving
      (fun z : (Q × Sample) × (Fin b0.1 → Sample) ↦
        (z.1.1, (z.2, z.1.2)))
      ((pathLaw.prod sampleLaw).prod rowLaw)
      (pathLaw.prod (rowLaw.prod sampleLaw)) := by
    simpa [Function.comp_def] using hinner.comp hassoc
  have hWithRow : ∀ᵐ z ∂(pathLaw.prod sampleLaw).prod rowLaw,
      p z.1.1 z.1.2 := by
    have hResult := hReordered.quasiMeasurePreserving.tendsto_ae hPull
    simpa [Function.comp_def] using hResult
  have hFibers := MeasureTheory.Measure.ae_ae_of_ae_prod hWithRow
  filter_upwards [hFibers] with z hz
  exact (hz.exists).choose_spec

/-- Projecting the genuine-gradient witness in the source conditional kernel
to one canonical minibatch coordinate gives genuine sampled gradients at both
generated queries under the exact path-by-single-sample product law.  The
claimed objects are the source gradients in `GenuineOnlineBatchDifferenceAt`;
the formal objects are the same worker, sample, generated queries, and source
sample law after coordinate projection. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_singleSample_genuine_ae
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : Nat → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {ℒ : Worker n → Real}
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ)
    (k : Nat) (i : Worker n) :
    ∀ᵐ z ∂pathLaw.prod (P.sampleLaw i),
      ∃ gNext gCurrent : Point d,
        GenuineSampleGradientAt P i z.2 (run (k + 1) z.1).x gNext ∧
          GenuineSampleGradientAt P i z.2 (run k z.1).x gCurrent := by
  classical
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  let j0 : Fin b0.1 := ⟨0, b0.2⟩
  rcases hKernel.2.2 k i with
    ⟨delta, _hDelta, hGenuine, _hFibers⟩
  have hCoordinate : ∀ᵐ z ∂pathLaw.prod (onlineBatchLaw P b0),
      ∃ gNext gCurrent : Point d,
        GenuineSampleGradientAt P i (z.2 i j0)
            (run (k + 1) z.1).x gNext ∧
          GenuineSampleGradientAt P i (z.2 i j0)
            (run k z.1).x gCurrent := by
    filter_upwards [hGenuine] with z hz
    rcases hz with
      ⟨gNext, gCurrent, hNext, hCurrent, _hDeltaEq⟩
    exact ⟨gNext j0, gCurrent j0, hNext j0, hCurrent j0⟩
  have hRow := ae_worker_row_of_onlineBatchLaw P pathLaw i
    (fun path row ↦ ∃ gNext gCurrent : Point d,
      GenuineSampleGradientAt P i (row j0)
          (run (k + 1) path).x gNext ∧
        GenuineSampleGradientAt P i (row j0)
          (run k path).x gCurrent)
    hCoordinate
  exact ae_singleSample_of_iid_row_coordinate
    pathLaw (P.sampleLaw i) j0
    (fun path xi ↦ ∃ gNext gCurrent : Point d,
      GenuineSampleGradientAt P i xi (run (k + 1) path).x gNext ∧
        GenuineSampleGradientAt P i xi (run k path).x gCurrent)
    hRow

/-- The projected genuine source gradients are represented by the existing
totalized `stochasticGradient` at the same generated calls.  This is the
source-to-formal identification needed before the measurable telescope may be
used by an Algorithm 3 recurrence. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_singleSample_genuine_totalized_ae
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : Nat → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {ℒ : Worker n → Real}
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ)
    (k : Nat) (i : Worker n) :
    ∀ᵐ z ∂pathLaw.prod (P.sampleLaw i),
      GenuineSampleGradientAt P i z.2 (run (k + 1) z.1).x
          (stochasticGradient P i z.2 (run (k + 1) z.1).x) ∧
        GenuineSampleGradientAt P i z.2 (run k z.1).x
          (stochasticGradient P i z.2 (run k z.1).x) := by
  have hGenuine :=
    onlineAssumption32GeneratedConditionalKernel_singleSample_genuine_ae
      hKernel k i
  filter_upwards [hGenuine] with z hz
  rcases hz with ⟨gNext, gCurrent, hNext, hCurrent⟩
  constructor
  · rw [stochasticGradient_eq_of_genuineSampleGradientAt hNext]
    exact hNext
  · rw [stochasticGradient_eq_of_genuineSampleGradientAt hCurrent]
    exact hCurrent

/-- A finite iid minibatch average cannot conceal a nonmeasurable
single-sample kernel once the fixed-query fibers are integrable and have the
stated mean.  The proof resamples one coordinate, integrates out the other
coordinates, and algebraically reconstructs the selected summand.  This is
the finite-product/Fubini step needed to pass from the generated Assumption
3.2 minibatch difference to one fresh sampled-gradient difference. -/
theorem singleSample_joint_aestronglyMeasurable_of_iid_average
    {d b0 : Count} {Q Sample : Type*}
    [MeasurableSpace Q] [MeasurableSpace Sample]
    (pathLaw : Measure Q) (sampleLaw : Measure Sample)
    [SFinite pathLaw] [IsProbabilityMeasure sampleLaw]
    (g : Q → Sample → Point d) (mean : Q → Point d)
    (hAverage : AEStronglyMeasurable
      (fun p : Q × (Fin b0.1 → Sample) ↦
        average (fun j : Fin b0.1 ↦ g p.1 (p.2 j)))
      (pathLaw.prod (Measure.pi (fun _ : Fin b0.1 ↦ sampleLaw))))
    (hFiber : ∀ᵐ q ∂pathLaw,
      Integrable (g q) sampleLaw ∧
        (∫ xi, g q xi ∂sampleLaw) = mean q) :
    AEStronglyMeasurable (fun p : Q × Sample ↦ g p.1 p.2)
      (pathLaw.prod sampleLaw) := by
  classical
  let batchLaw : Measure (Fin b0.1 → Sample) :=
    Measure.pi (fun _ : Fin b0.1 ↦ sampleLaw)
  let j0 : Fin b0.1 := ⟨0, b0.2⟩
  let batchAverage : Q × (Fin b0.1 → Sample) → Point d :=
    fun p ↦ average (fun j : Fin b0.1 ↦ g p.1 (p.2 j))
  have hAverage' : AEStronglyMeasurable batchAverage
      (pathLaw.prod batchLaw) := by
    simpa [batchAverage, batchLaw] using hAverage
  have hAverageFiberMean : ∀ᵐ q ∂pathLaw,
      (∫ batch, batchAverage (q, batch) ∂batchLaw) = mean q := by
    filter_upwards [hFiber] with q hq
    have hcoordInt (j : Fin b0.1) : Integrable
        (fun batch : Fin b0.1 → Sample ↦ g q (batch j)) batchLaw := by
      simpa [batchLaw] using
        (MeasureTheory.integrable_comp_eval
          (X := fun _ : Fin b0.1 ↦ Sample)
          (μ := fun _ : Fin b0.1 ↦ sampleLaw) hq.1)
    unfold batchAverage average SOptLib.finiteUniformAverage
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun j _ ↦ hcoordInt j)]
    have hcoordMean (j : Fin b0.1) :
        (∫ batch : Fin b0.1 → Sample, g q (batch j) ∂batchLaw) = mean q := by
      simpa [batchLaw] using
        (MeasureTheory.integral_comp_eval
          (μ := fun _ : Fin b0.1 ↦ sampleLaw)
          hq.1.aestronglyMeasurable).trans hq.2
    simp_rw [hcoordMean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hb : (b0.1 : ℝ) ≠ 0 := by exact_mod_cast b0.2.ne'
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ hb, one_smul]
  have hMean : AEStronglyMeasurable mean pathLaw :=
    hAverage'.integral_prod_right'.congr hAverageFiberMean
  let replace : (Fin b0.1 → Sample) × Sample → (Fin b0.1 → Sample) :=
    fun p ↦ Function.update p.1 j0 p.2
  have hReplace : MeasurePreserving replace (batchLaw.prod sampleLaw) batchLaw := by
    simpa [replace, batchLaw] using
      (measurePreserving_update_coordinate_prod_pi sampleLaw j0)
  let replaceParam : ((Q × Sample) × (Fin b0.1 → Sample)) →
      Q × (Fin b0.1 → Sample) :=
    fun p ↦ (p.1.1, Function.update p.2 j0 p.1.2)
  have hReplaceParam : MeasurePreserving replaceParam
      ((pathLaw.prod sampleLaw).prod batchLaw)
      (pathLaw.prod batchLaw) := by
    have hswap : MeasurePreserving
        (fun p : Sample × (Fin b0.1 → Sample) ↦ (p.2, p.1))
        (sampleLaw.prod batchLaw) (batchLaw.prod sampleLaw) := by
      simpa using
        (MeasureTheory.Measure.measurePreserving_swap
          (μ := sampleLaw) (ν := batchLaw))
    have hinner : MeasurePreserving
        (fun p : Sample × (Fin b0.1 → Sample) ↦
          Function.update p.2 j0 p.1)
        (sampleLaw.prod batchLaw) batchLaw := by
      simpa [replace, Function.comp_def] using hReplace.comp hswap
    have hprod := (MeasurePreserving.id pathLaw).prod hinner
    have hassoc := MeasureTheory.measurePreserving_prodAssoc
      pathLaw sampleLaw batchLaw
    simpa [replaceParam, Function.comp_def] using hprod.comp hassoc
  have hUpdated : AEStronglyMeasurable
      (fun p : (Q × Sample) × (Fin b0.1 → Sample) ↦
        batchAverage (p.1.1, Function.update p.2 j0 p.1.2))
      ((pathLaw.prod sampleLaw).prod batchLaw) := by
    exact hAverage'.comp_quasiMeasurePreserving
      hReplaceParam.quasiMeasurePreserving
  let reconstructedMean : Q × Sample → Point d := fun p ↦
    ∫ batch, batchAverage (p.1,
      Function.update batch j0 p.2) ∂batchLaw
  have hReconstructedMean : AEStronglyMeasurable reconstructedMean
      (pathLaw.prod sampleLaw) := by
    simpa [reconstructedMean] using hUpdated.integral_prod_right'
  have hReconstruct : ∀ᵐ p ∂pathLaw.prod sampleLaw,
      g p.1 p.2 =
        (b0.1 : ℝ) • reconstructedMean p -
          ((b0.1 : ℝ) - 1) • mean p.1 := by
    have hFiberProd := (MeasureTheory.Measure.quasiMeasurePreserving_fst
      (μ := pathLaw) (ν := sampleLaw)).tendsto_ae hFiber
    filter_upwards [hFiberProd] with p hp
    let q := p.1
    let xi := p.2
    have hq : Integrable (g q) sampleLaw ∧
        (∫ z, g q z ∂sampleLaw) = mean q := by
      simpa [q] using hp
    have hcoordInt (j : Fin b0.1) : Integrable
        (fun batch : Fin b0.1 → Sample ↦
          g q ((Function.update batch j0 xi) j)) batchLaw := by
      by_cases hj : j = j0
      · subst j
        exact integrable_const (μ := batchLaw) (g q xi)
      · have heq : (fun batch : Fin b0.1 → Sample ↦
          g q ((Function.update batch j0 xi) j)) =
          (fun batch ↦ g q (batch j)) := by
          funext batch
          simp [Function.update, hj]
        rw [heq]
        simpa [batchLaw] using
          (MeasureTheory.integrable_comp_eval
            (X := fun _ : Fin b0.1 ↦ Sample)
            (μ := fun _ : Fin b0.1 ↦ sampleLaw) hq.1)
    have hcoordMean (j : Fin b0.1) :
        (∫ batch : Fin b0.1 → Sample,
          g q ((Function.update batch j0 xi) j) ∂batchLaw) =
          if j = j0 then g q xi else mean q := by
      by_cases hj : j = j0
      · subst j
        simp [batchLaw]
      · have heq : (fun batch : Fin b0.1 → Sample ↦
          g q ((Function.update batch j0 xi) j)) =
          (fun batch ↦ g q (batch j)) := by
          funext batch
          simp [Function.update, hj]
        rw [heq]
        simp only [if_neg hj]
        simpa [batchLaw] using
          (MeasureTheory.integral_comp_eval
            (μ := fun _ : Fin b0.1 ↦ sampleLaw)
            hq.1.aestronglyMeasurable).trans hq.2
    have hMeanFormula : reconstructedMean (q, xi) =
        (b0.1 : ℝ)⁻¹ •
          (g q xi + ((b0.1 : ℝ) - 1) • mean q) := by
      unfold reconstructedMean batchAverage average SOptLib.finiteUniformAverage
      rw [integral_smul]
      rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun j _ ↦ hcoordInt j)]
      simp_rw [hcoordMean]
      have hcard : Fintype.card (Fin b0.1) = b0.1 := Fintype.card_fin _
      rw [hcard]
      have hsum : ∑ j : Fin b0.1,
          (if j = j0 then g q xi else mean q) =
          g q xi + ((b0.1 : ℝ) - 1) • mean q := by
        calc
          (∑ j : Fin b0.1, if j = j0 then g q xi else mean q) =
              ∑ j : Fin b0.1,
                (mean q + if j = j0 then g q xi - mean q else 0) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : j = j0 <;> simp [hj]
          _ = (∑ _j : Fin b0.1, mean q) +
              ∑ j : Fin b0.1,
                (if j = j0 then g q xi - mean q else 0) := by
                rw [Finset.sum_add_distrib]
          _ = g q xi + ((b0.1 : ℝ) - 1) • mean q := by
                rw [Finset.sum_ite_eq' Finset.univ j0]
                simp only [Finset.mem_univ, if_true, Finset.sum_const,
                  Finset.card_univ, Fintype.card_fin]
                module
      rw [hsum]
    have hb : (b0.1 : ℝ) ≠ 0 := by exact_mod_cast b0.2.ne'
    have hcalc : g q xi =
        (b0.1 : ℝ) • reconstructedMean (q, xi) -
          ((b0.1 : ℝ) - 1) • mean q := by
      rw [hMeanFormula, smul_smul, mul_inv_cancel₀ hb, one_smul]
      module
    simpa [q, xi] using hcalc
  have hRight : AEStronglyMeasurable
      (fun p : Q × Sample ↦
        (b0.1 : ℝ) • reconstructedMean p -
          ((b0.1 : ℝ) - 1) • mean p.1)
      (pathLaw.prod sampleLaw) :=
    (hReconstructedMean.const_smul (b0.1 : ℝ)).sub
      (hMean.comp_fst.const_smul ((b0.1 : ℝ) - 1))
  exact hRight.congr (hReconstruct.mono fun _ hp ↦ hp.symm)

/-- The source conditional kernel and literal Assumption 3.3 together make
the actual one-sample stochastic-gradient difference at two consecutive
generated queries a random vector.  This is the exact single-coordinate
instantiation of `singleSample_joint_aestronglyMeasurable_of_iid_average`:
the minibatch average comes from Assumption 3.2, while fixed-query
integrability and both means come from the literal moment contract.  No
adaptive-gradient regularity or sample-loss differentiability is assumed. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_singleSampleDifference_joint_aestronglyMeasurable
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {pathLaw : Measure Ω} [SFinite pathLaw]
    {ℒ σ : Worker n → ℝ}
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ)
    (hLiteral : OnlineAssumption33Literal P σ)
    (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Ω × Sample i ↦
        stochasticGradient P i p.2 (run (k + 1) p.1).x -
          stochasticGradient P i p.2 (run k p.1).x)
      (pathLaw.prod (P.sampleLaw i)) := by
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  have hFull :=
    onlineAssumption32GeneratedConditionalKernel_batchDifference_joint_aestronglyMeasurable
      hKernel k i
  have hRow : AEStronglyMeasurable
      (fun p : Ω × (Fin b0.1 → Sample i) ↦
        average (fun j : Fin b0.1 ↦
          stochasticGradient P i (p.2 j) (run (k + 1) p.1).x -
            stochasticGradient P i (p.2 j) (run k p.1).x))
      (pathLaw.prod
        (Measure.pi (fun _ : Fin b0.1 ↦ P.sampleLaw i))) := by
    apply aestronglyMeasurable_worker_row_of_onlineBatchLaw
      P pathLaw i
      (fun path row ↦ average (fun j : Fin b0.1 ↦
        stochasticGradient P i (row j) (run (k + 1) path).x -
          stochasticGradient P i (row j) (run k path).x))
    simpa [onlineBatchDifference] using hFull
  have hMoments : LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ :=
    (onlineAssumption33Literal_iff_legacy P σ).mp hLiteral
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

/-- Telescoping the source-derived measurable one-sample differences from a
deterministic initialization query supplies the totalized sampled gradient at
every generated iterate as a random vector.  The base case uses only the
fixed-query integrability clause of literal Assumption 3.3; each successor
uses the preceding Assumption 3.2 single-sample difference theorem. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_adaptiveGradient_joint_aestronglyMeasurable
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {pathLaw : Measure Ω} [SFinite pathLaw]
    {ℒ σ : Worker n → ℝ}
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ)
    (hLiteral : OnlineAssumption33Literal P σ)
    (x0 : Point d) (hInitial : ∀ path, (run 0 path).x = x0)
    (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Ω × Sample i ↦
        stochasticGradient P i p.2 (run k p.1).x)
      (pathLaw.prod (P.sampleLaw i)) := by
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  have hMoments : LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ :=
    (onlineAssumption33Literal_iff_legacy P σ).mp hLiteral
  induction k with
  | zero =>
      have hBase := (hMoments.2 i x0).1.aestronglyMeasurable.comp_snd
        (μ := pathLaw)
      exact hBase.congr (Filter.Eventually.of_forall fun p ↦ by
        change stochasticGradient P i p.2 x0 =
          stochasticGradient P i p.2 (run 0 p.1).x
        rw [hInitial p.1])
  | succ k ih =>
      have hDifference :=
        onlineAssumption32GeneratedConditionalKernel_singleSampleDifference_joint_aestronglyMeasurable
          hKernel hLiteral k i
      refine (ih.add hDifference).congr
        (Filter.Eventually.of_forall fun p ↦ ?_)
      change stochasticGradient P i p.2 (run k p.1).x +
          (stochasticGradient P i p.2 (run (k + 1) p.1).x -
            stochasticGradient P i p.2 (run k p.1).x) =
        stochasticGradient P i p.2 (run (k + 1) p.1).x
      abel

/-- Process-specific A-track supplier for an adaptive sampled-gradient call at
one generated iterate.  The genuine-gradient conjunct comes from the exact
source Assumption 3.2 kernel, and the random-vector conjunct comes from that
kernel plus literal Assumption 3.3 and deterministic initialization.  Neither
conjunct quantifies over unrelated query laws. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_adaptiveGradient_source_regular
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : Nat → Omega → State d}
    {pathLaw : Measure Omega} [SFinite pathLaw]
    {ℒ sigma : Worker n → Real}
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) P run pathLaw ℒ)
    (hLiteral : OnlineAssumption33Literal P sigma)
    (x0 : Point d) (hInitial : ∀ path, (run 0 path).x = x0)
    (k : Nat) (i : Worker n) :
    (∀ᵐ z ∂pathLaw.prod (P.sampleLaw i),
        GenuineSampleGradientAt P i z.2 (run k z.1).x
          (stochasticGradient P i z.2 (run k z.1).x)) ∧
      AEStronglyMeasurable
        (fun z : Omega × Sample i ↦
          stochasticGradient P i z.2 (run k z.1).x)
        (pathLaw.prod (P.sampleLaw i)) := by
  constructor
  · have hGenuine :=
      onlineAssumption32GeneratedConditionalKernel_singleSample_genuine_totalized_ae
        hKernel k i
    exact hGenuine.mono (fun _ hz ↦ hz.2)
  · exact
      onlineAssumption32GeneratedConditionalKernel_adaptiveGradient_joint_aestronglyMeasurable
        hKernel hLiteral x0 hInitial k i

/-- Exact proof-exact Algorithm 3 instantiation of the process-specific
Assumption 3.2/3.3 supplier.  Both the source genuine-gradient witness and
the formal random-vector fact concern `onlineProofExactProcess` under its
canonical `onlineProofExactPathLaw`; the deterministic initialization needed
by the telescope is definitionally the supplied `x0`. -/
theorem onlineProofExactProcess_adaptiveGradient_source_regular
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ sigma : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (k : ℕ) (i : Worker n) :
    (∀ᵐ z ∂(onlineProofExactPathLaw (b := b) (b0 := b0) A).prod
        (A.problem.sampleLaw i),
      GenuineSampleGradientAt A.problem i z.2
        (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch k z.1).x
        (stochasticGradient A.problem i z.2
          (onlineProofExactProcess
            (b := b) (b0 := b0) A x0 hBatch k z.1).x)) ∧
      AEStronglyMeasurable
        (fun z ↦ stochasticGradient A.problem i z.2
          (onlineProofExactProcess
            (b := b) (b0 := b0) A x0 hBatch k z.1).x)
        ((onlineProofExactPathLaw (b := b) (b0 := b0) A).prod
          (A.problem.sampleLaw i)) := by
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
  exact
    onlineAssumption32GeneratedConditionalKernel_adaptiveGradient_source_regular
      hKernel hLiteral x0 (fun _ ↦ rfl) k i

/-! The refresh branch uses the query determined by the strict round prefix,
not an arbitrary query law.  The following two transfers discard the unused
iid tail from the full-path source supplier while retaining exactly that
canonical prefix and, in the second theorem, one independent source sample. -/

/-- Source Assumption 3.2 makes the next proof-exact query measurable already
on the strict prefix which generates it.  This is the process-specific
replacement for the all-query state-measurability route in refresh proofs. -/
theorem
    onlineProofExactPrefix_query_aestronglyMeasurable_of_generatedConditionalKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ) :
    let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
    let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
    AEStronglyMeasurable
      (fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ ↦
        primalStep A.stepSize (prefixState pref)) prefixLaw := by
  classical
  dsimp only
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  have hFull : AEStronglyMeasurable
      (fun path ↦ (run (k + 1) path).x) law := by
    have hPair := hKernel.2.1 k
    exact (measurable_snd.comp_aemeasurable
      hPair.aemeasurable).aestronglyMeasurable
  apply aestronglyMeasurable_prefix_of_comp_general roundLaw k
  have hEq : (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      primalStep A.stepSize
        (prefixState (fun j : Fin k ↦ path j.1))) =
      (fun path ↦ (run (k + 1) path).x) := by
    funext path
    have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := path)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ path j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])
    change primalStep A.stepSize
        (onlineProofExactProcess A x0 hBatch k
          (onlineExtendRoundPrefix fallback (fun j : Fin k ↦ path j.1))) =
      primalStep A.stepSize (onlineProofExactProcess A x0 hBatch k path)
    rw [← hs]
  rw [hEq]
  simpa [law, roundLaw, onlineProofExactPathLaw] using hFull

/-- The sampled gradient at the strict-prefix query is jointly measurable
with one fresh worker sample.  Both the query and sample law are the actual
objects later used by the refresh minibatch; no unrelated query law is
quantified over. -/
theorem
    onlineProofExactPrefix_adaptiveGradient_source_aestronglyMeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ)
    (k : ℕ) (i : Worker n) :
    let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
    let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
    AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) × Sample i ↦
        stochasticGradient A.problem i p.2
          (primalStep A.stepSize (prefixState p.1)))
      (prefixLaw.prod (A.problem.sampleLaw i)) := by
  classical
  dsimp only
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hFull :=
    onlineProofExactProcess_adaptiveGradient_source_regular
      A x0 hBatch ℒ σ hKernel hLiteral (k + 1) i
  have hSwapped : AEStronglyMeasurable
      (fun p : Sample i × (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
        stochasticGradient A.problem i p.1 (run (k + 1) p.2).x)
      ((A.problem.sampleLaw i).prod law) := by
    have h := hFull.2.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := A.problem.sampleLaw i) (ν := law))
    simpa using h
  have hFinite : AEStronglyMeasurable
      (fun p : Sample i × (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
        stochasticGradient A.problem i p.1
          (primalStep A.stepSize (prefixState p.2)))
      ((A.problem.sampleLaw i).prod prefixLaw) := by
    apply aestronglyMeasurable_initial_prefix_of_comp_general
      (A.problem.sampleLaw i) roundLaw k
    have hEq :
        (fun p : Sample i × (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
          stochasticGradient A.problem i p.1
            (primalStep A.stepSize
              (prefixState (fun j : Fin k ↦ p.2 j.1)))) =
        (fun p ↦ stochasticGradient A.problem i p.1
          (run (k + 1) p.2).x) := by
      funext p
      have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
        (path := p.2)
        (path' := onlineExtendRoundPrefix fallback
          (fun j : Fin k ↦ p.2 j.1))
        (by intro t ht; simp [onlineExtendRoundPrefix, ht])
      congr 1
      change primalStep A.stepSize
          (onlineProofExactProcess A x0 hBatch k
            (onlineExtendRoundPrefix fallback (fun j : Fin k ↦ p.2 j.1))) =
        primalStep A.stepSize (onlineProofExactProcess A x0 hBatch k p.2)
      rw [← hs]
    rw [hEq]
    simpa [law, roundLaw, onlineProofExactPathLaw] using hSwapped
  have h := hFinite.comp_measurePreserving
    (MeasureTheory.Measure.measurePreserving_swap
      (μ := prefixLaw) (ν := A.problem.sampleLaw i))
  simpa using h

/-- The complete refresh residual square is a random variable on the exact
strict-prefix-by-refresh-minibatch product law.  This is the measurable
kernel needed for both the literal variance integration and same-round coin
independence; it is derived solely from the generated Assumption 3.2 kernel
and literal Assumption 3.3. -/
theorem
    onlineProofExactPrefix_refreshErrorSq_source_aestronglyMeasurable
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) (k : ℕ) :
    let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
    let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
    AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((i : Worker n) → Fin b.1 → Sample i) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.2 i j)
              (primalStep A.stepSize (prefixState p.1)))) -
          globalGradient (onlineLocalProblem A.problem)
            (primalStep A.stepSize (prefixState p.1))‖ ^ 2)
      (prefixLaw.prod (onlineBatchLaw A.problem b)) := by
  classical
  dsimp only
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure prefixLaw := by
    unfold prefixLaw
    infer_instance
  have hquery : AEStronglyMeasurable
      (fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ ↦
        primalStep A.stepSize (prefixState pref)) prefixLaw := by
    simpa [roundLaw, prefixLaw, prefixState] using
      onlineProofExactPrefix_query_aestronglyMeasurable_of_generatedConditionalKernel
        A x0 hBatch ℒ hKernel fallback k
  have hgrad (i : Worker n) (j : Fin b.1) : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b.1 → Sample w) ↦
        stochasticGradient A.problem i (p.2 i j)
          (primalStep A.stepSize (prefixState p.1)))
      (prefixLaw.prod batchLaw) := by
    have hsingle :=
      onlineProofExactPrefix_adaptiveGradient_source_aestronglyMeasurable
        A x0 hBatch ℒ σ hKernel hLiteral fallback k i
    have hcoord : MeasurePreserving
        (fun batch : (w : Worker n) → Fin b.1 → Sample w ↦ batch i j)
        batchLaw (A.problem.sampleLaw i) :=
      ⟨(by fun_prop), by
        simpa [batchLaw] using
          onlineBatchLaw_coordinate_marginal A.problem i j⟩
    have hpull := hsingle.comp_measurePreserving
      ((MeasurePreserving.id prefixLaw).prod hcoord)
    simpa [prefixLaw, roundLaw, prefixState, batchLaw,
      Function.comp_def] using hpull
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b.1 → Sample w) ↦
        average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i (p.2 i j)
            (primalStep A.stepSize (prefixState p.1))))
      (prefixLaw.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ hgrad i j)).const_smul
        ((Fintype.card (Fin b.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b.1 → Sample w) ↦
        average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i (p.2 i j)
            (primalStep A.stepSize (prefixState p.1)))))
      (prefixLaw.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ ↦ hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b.1 → Sample w) ↦
        globalGradient (onlineLocalProblem A.problem)
          (primalStep A.stepSize (prefixState p.1)))
      (prefixLaw.prod batchLaw) :=
    ((measurable_gradient
      (globalObjective (onlineLocalProblem A.problem))).comp_aemeasurable
        hquery.aemeasurable).aestronglyMeasurable.comp_fst
  have hresidual := havg.sub hglobal
  simpa [batchLaw, prefixLaw, roundLaw, prefixState, pow_two] using
    hresidual.norm.mul hresidual.norm

set_option maxHeartbeats 2000000 in
/-- The actual proof-exact refresh error is integrable and satisfies the
literal Assumption 3.3 variance bound using only the generated Assumption 3.2
kernel.  The random query is the exact strict-prefix query and the current
refresh minibatch is independent of that prefix under the canonical iid path
law; no all-query regularity predicate is used. -/
theorem
    onlineProofExact_refresh_error_integrable_and_expectation_le_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i))
    (k : ℕ) :
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    Integrable refreshErrorSq law ∧
      (∫ path, refreshErrorSq path ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  dsimp only
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k
  let batch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (path k).2.1.1
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
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let query := fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ ↦
    primalStep A.stepSize (prefixState pref)
  let F := fun (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ)
      (fresh : (i : Worker n) → Fin b.1 → Sample i) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (fresh i j) (query pref))) -
      globalGradient (onlineLocalProblem A.problem) (query pref)‖ ^ 2
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    simpa [law, prefixMap, prefixLaw, roundLaw,
      onlineProofExactPathLaw, onlineRoundPrefix, SOptLib.iidStreamLaw] using
      (iidStream_prefix_map_eq_infinitePi
        (onlineRoundLaw (b := b) (b0 := b0) A) k)
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map prefixMap law) :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hcurrent : Measurable current := measurable_pi_apply k
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := Measure.map prefixMap law) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [law, prefixMap, current, roundLaw,
        onlineProofExactPathLaw, onlineRoundPrefix, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law := by
    simpa [batch, current, Function.comp_def] using
      hpastCurrent.comp measurable_id
        (show Measurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1) by fun_prop)
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
          roundLaw := by
            rw [show Measure.map current law = roundLaw by
              simpa [current, law, roundLaw, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = batchLaw := by
        simpa [roundLaw, batchLaw] using
          onlineRoundLaw_refreshBatch_marginal (b0 := b0) A
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod batchLaw) := by
    simpa [F, query, prefixState, prefixLaw, roundLaw, batchLaw] using
      onlineProofExactPrefix_refreshErrorSq_source_aestronglyMeasurable
        A x0 hBatch ℒ σ hKernel hLiteral fallback k
  have hFmap : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.map prefixMap law).prod batchLaw) := by
    rw [hprefixLaw]
    exact hF
  have hfixed (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ) :
      Integrable (F pref) batchLaw ∧
        (∫ fresh, F pref fresh ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [F, query, batchLaw] using
      (onlineFixedRefreshAverage_secondMoment_of_literal
        (b := b) A (query pref) σ hLiteral hDiff)
  have hcomp : Integrable (fun path ↦ F (prefixMap path) (batch path)) law :=
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
    dsimp [prefixState, run]
    exact (onlineProofExactProcess_congr_prefix
      A x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])).symm
  have hcalc : ∀ path, F (prefixMap path) (batch path) =
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2 := by
    intro path
    dsimp [F, query, batch]
    rw [hstatePrefix path]
    rfl
  constructor
  · exact hcomp.congr (Filter.Eventually.of_forall hcalc)
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hcalc)]
    exact hbound

set_option maxHeartbeats 2000000 in
/-- The proof-exact refresh-error square is independent of its same-round
Bernoulli coin under the generated Assumption 3.2 kernel and literal
Assumption 3.3.  The observable is a measurable function of the strict prefix
and current non-coin coordinates, so the result follows from the canonical
iid product law without all-query regularity. -/
theorem onlineProofExact_refresh_error_sq_indep_refresh_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ σ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (k : ℕ) :
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    ProbabilityTheory.IndepFun refreshErrorSq
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1) law := by
  classical
  dsimp only
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let refreshBatchLaw := onlineBatchLaw A.problem b
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let roundLaw := coinLaw.prod restLaw
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let batch := fun rest : ((((w : Worker n) → Fin b.1 → Sample w) ×
      ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦ rest.1.1
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
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
  haveI : IsProbabilityMeasure
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
    unfold onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure
      (onlineProofExactPathLaw (b := b) (b0 := b0) A))
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let query := fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ ↦
    primalStep A.stepSize (prefixState pref)
  let F := fun (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ)
      (rest : ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (batch rest i j) (query pref))) -
      globalGradient (onlineLocalProblem A.problem) (query pref)‖ ^ 2
  have hprefixLaw : prefixLaw = onlineRoundPrefixLaw A k := by
    unfold prefixLaw onlineRoundPrefixLaw onlineProofExactPathLaw
    simpa [roundLaw, coinLaw, restLaw, refreshBatchLaw,
      differenceBatchLaw, compressionLaw, onlineRoundLaw] using
      (iidStream_prefix_map_eq_infinitePi
        (onlineRoundLaw (b := b) (b0 := b0) A) k).symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [hprefixLaw]
    unfold onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map
      (show AEMeasurable (onlineRoundPrefix
        (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k)
          (onlineProofExactPathLaw (b := b) (b0 := b0) A) from
        (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).aemeasurable)
  have hsource : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((w : Worker n) → Fin b.1 → Sample w) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.2 i j) (query p.1))) -
          globalGradient (onlineLocalProblem A.problem) (query p.1)‖ ^ 2)
      (prefixLaw.prod refreshBatchLaw) := by
    simpa [query, prefixState, prefixLaw, roundLaw, refreshBatchLaw,
      coinLaw, restLaw, differenceBatchLaw, compressionLaw, onlineRoundLaw] using
      onlineProofExactPrefix_refreshErrorSq_source_aestronglyMeasurable
        A x0 hBatch ℒ σ hKernel hLiteral fallback k
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hbatchLaw : Measure.map batch restLaw = refreshBatchLaw := by
    calc
      Measure.map batch restLaw = Measure.map Prod.fst
          (Measure.map Prod.fst restLaw) := by
            rw [MeasureTheory.Measure.map_map measurable_fst measurable_fst]
            rfl
      _ = refreshBatchLaw := by simp [restLaw]
  let pull := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
      ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
    (z.1, batch z.2)
  have hpull : Measurable pull := by
    dsimp [pull]
    fun_prop
  have hpullLaw : Measure.map pull (prefixLaw.prod restLaw) =
      prefixLaw.prod refreshBatchLaw := by
    have hm := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
      measurable_id hbatch
    rw [Measure.map_id, hbatchLaw] at hm
    simpa [pull] using hm.symm
  have hqmp : Measure.QuasiMeasurePreserving pull
      (prefixLaw.prod restLaw) (prefixLaw.prod refreshBatchLaw) :=
    ⟨hpull, by rw [hpullLaw]⟩
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod restLaw) := by
    simpa [F, pull] using hsource.comp_quasiMeasurePreserving hqmp
  have hi := iidStream_prefix_current_snd_kernel_indep_fst
    coinLaw restLaw k F hF
  have hcalc : ∀ path : ℕ → OnlineRoundNoise n b b0 Sample Ξ,
      F (fun j : Fin k ↦ path j.1) (path k).2 =
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i ((path k).2.1.1 i j)
              (onlineProofExactProcess A x0 hBatch (k + 1) path).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (onlineProofExactProcess A x0 hBatch (k + 1) path).x‖ ^ 2 := by
    intro path
    have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := path)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ path j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])
    simp only [F, batch, query, prefixState]
    rw [onlineProofExactProcess_succ, hs]
    rfl
  simpa [coinLaw, restLaw, roundLaw, refreshBatchLaw, differenceBatchLaw,
    compressionLaw, onlineProofExactPathLaw, onlineRoundLaw] using
    hi.congr (Filter.Eventually.of_forall hcalc)
      (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- The generated conditional kernel makes the complete proof-exact state a
random variable under its canonical path law without the all-query adaptive
regularity predicate.  The kernel directly supplies joint measurability of
`(x^k,x^{k+1})`; the positive Algorithm 3 step then reconstructs
`g^k = γ⁻¹ • (x^k - x^{k+1})`.  Thus this theorem uses the exact
generated process and law occurring in source Assumption 3.2, rather than a
regularity statement quantified over unrelated query laws. -/
theorem onlineProofExactProcess_aemeasurable_of_generatedConditionalKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
    (k : ℕ) :
    AEMeasurable
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch k)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  have hpair : AEStronglyMeasurable
      (fun path ↦ ((run k path).x, (run (k + 1) path).x)) law :=
    hKernel.2.1 k
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    (measurable_fst.comp_aemeasurable hpair.aemeasurable).aestronglyMeasurable
  have hxNext : AEStronglyMeasurable
      (fun path ↦ (run (k + 1) path).x) law :=
    (measurable_snd.comp_aemeasurable hpair.aemeasurable).aestronglyMeasurable
  have hgRecovered : AEStronglyMeasurable
      (fun path ↦ ((A.stepSize : ℝ)⁻¹) •
        ((run k path).x - (run (k + 1) path).x)) law :=
    (hx.sub hxNext).const_smul ((A.stepSize : ℝ)⁻¹)
  have hg : AEStronglyMeasurable (fun path ↦ (run k path).g) law := by
    refine hgRecovered.congr (Filter.Eventually.of_forall ?_)
    intro path
    have hstep : (A.stepSize : ℝ) ≠ 0 := ne_of_gt A.stepSize.property
    change ((A.stepSize : ℝ)⁻¹) •
        ((run k path).x - (run (k + 1) path).x) = (run k path).g
    rw [show (run (k + 1) path).x =
        primalStep A.stepSize (run k path) by rfl]
    rw [primalStep_eq, sub_sub_cancel, smul_smul,
      inv_mul_cancel₀ hstep, one_smul]
  exact (measurable_state_mk d).comp_aemeasurable
    (hx.aemeasurable.prodMk hg.aemeasurable)

/-- The generated Assumption 3.2 kernel makes the complete compressed
nonrefresh innovation jointly measurable with the canonical fresh
difference-minibatch/compressor coordinate.  This is the exact product
kernel used by proof-exact Algorithm 3; no regularity over unrelated query
laws is required. -/
theorem
    onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_joint_aestronglyMeasurable
    {d n b0 : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {Ξ : Type*} [MeasurableSpace Omega]
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (run : ℕ → Omega → State d)
    (pathLaw : Measure Omega) [SFinite pathLaw] (ℒ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem run pathLaw ℒ)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
    AEStronglyMeasurable
      (fun p : Omega ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem p.2.1 i
                (run (k + 1) p.1).x (run k p.1).x)
              (p.2.2 i) -
            localGradientDifference P i
              (run (k + 1) p.1).x (run k p.1).x))
      (pathLaw.prod noiseLaw) := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let batchLaw := onlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  let reassoc := fun p : Omega ×
      (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
    ((p.1, p.2.1), p.2.2)
  have hreassoc : MeasurePreserving reassoc
      (pathLaw.prod noiseLaw) ((pathLaw.prod batchLaw).prod compressionLaw) := by
    simpa [reassoc, noiseLaw, onlineDifferenceCompressionLaw] using
      (MeasureTheory.measurePreserving_prodAssoc
        pathLaw batchLaw compressionLaw).symm
  have hpair : AEStronglyMeasurable
      (fun p : Omega × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        ((run (k + 1) p.1).x, (run k p.1).x))
      (pathLaw.prod batchLaw) := by
    have hp := hKernel.2.1 k
    exact (((measurable_snd.comp_aemeasurable hp.aemeasurable)
      |>.aestronglyMeasurable).prodMk
        ((measurable_fst.comp_aemeasurable hp.aemeasurable)
          |>.aestronglyMeasurable)).comp_fst
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Omega ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem p.2.1 i
              (run (k + 1) p.1).x (run k p.1).x)
            (p.2.2 i) -
          localGradientDifference P i
            (run (k + 1) p.1).x (run k p.1).x)
      (pathLaw.prod noiseLaw) := by
    have hD :=
      onlineAssumption32GeneratedConditionalKernel_batchDifference_joint_aestronglyMeasurable
        hKernel k i
    have hDprod : AEStronglyMeasurable
        (fun p : (Omega ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ) ↦
          onlineBatchDifference A.problem p.1.2 i
            (run (k + 1) p.1.1).x (run k p.1.1).x)
        ((pathLaw.prod batchLaw).prod compressionLaw) := hD.comp_fst
    have hxi : Measurable
        (fun p : (Omega ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ) ↦
          p.2 i) := by fun_prop
    have hquantized : AEStronglyMeasurable
        (fun p : (Omega ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ) ↦
          A.quantizer.apply
            (onlineBatchDifference A.problem p.1.2 i
              (run (k + 1) p.1.1).x (run k p.1.1).x)
            (p.2 i))
        ((pathLaw.prod batchLaw).prod compressionLaw) :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hDprod.aemeasurable.prodMk hxi.aemeasurable)).aestronglyMeasurable
    have hdelta : AEStronglyMeasurable
        (fun p : (Omega ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ) ↦
          localGradientDifference P i
            (run (k + 1) p.1.1).x (run k p.1.1).x)
        ((pathLaw.prod batchLaw).prod compressionLaw) := by
      have hm : AEStronglyMeasurable
          (fun p : Omega ×
              ((w : Worker n) → Fin b0.1 → Sample w) ↦
            localGradientDifference P i
              (run (k + 1) p.1).x (run k p.1).x)
          (pathLaw.prod batchLaw) :=
        (((measurable_localGradient P i).comp_aemeasurable
            hpair.aemeasurable.fst).sub
          ((measurable_localGradient P i).comp_aemeasurable
            hpair.aemeasurable.snd)).aestronglyMeasurable
      exact hm.comp_fst
    have hsource := hquantized.sub hdelta
    simpa [reassoc, batchLaw, compressionLaw, noiseLaw, P,
      Function.comp_def] using hsource.comp_measurePreserving hreassoc
  unfold average SOptLib.finiteUniformAverage
  have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ ↦ hworker i)).const_smul
      ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hsum.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [P, Finset.sum_apply, Finset.sum_sub_distrib]

set_option maxHeartbeats 3000000 in
/-- The complete proof-exact nonrefresh residual square is independent of
the same-round refresh coin under the generated Assumption 3.2 kernel.  The
proof first obtains the actual compressed-innovation product kernel above,
then discards the unused iid tail and applies the canonical coin/rest product
decomposition. -/
theorem onlineProofExact_nonrefresh_error_sq_indep_refresh_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) ℒ)
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
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let refreshBatchLaw := onlineBatchLaw A.problem b
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let noiseLaw := differenceBatchLaw.prod compressionLaw
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let roundLaw := coinLaw.prod restLaw
  let law := SOptLib.iidStreamLaw roundLaw
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
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
  haveI : IsProbabilityMeasure restLaw := by
    unfold restLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    unfold coinLaw refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let residualPrefix := fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let noiseOfRest := fun rest :
      ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
    (rest.1.2, rest.2)
  let innovationPrefix := fun
      (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ)
      (rest : ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem (noiseOfRest rest).1 i
            (primalStep A.stepSize (prefixState pref)) (prefixState pref).x)
          ((noiseOfRest rest).2 i) -
        localGradientDifference P i
          (primalStep A.stepSize (prefixState pref)) (prefixState pref).x)
  let F := fun
      (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ)
      (rest : ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) ↦
    ‖residualPrefix pref + innovationPrefix pref rest‖ ^ 2
  have hstate := onlineProofExactProcess_aemeasurable_of_generatedConditionalKernel
    A x0 hBatch ℒ hKernel k
  have hresidual : AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law := by
    have hg := ((measurable_state_g d).comp_aemeasurable hstate)
      |>.aestronglyMeasurable
    have hx := ((measurable_state_x d).comp_aemeasurable hstate)
      |>.aestronglyMeasurable
    exact hg.sub ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hnoiseOfRest : Measurable noiseOfRest := by
    dsimp [noiseOfRest]
    fun_prop
  have hnoiseOfRestLaw : Measure.map noiseOfRest restLaw = noiseLaw := by
    calc
      Measure.map noiseOfRest restLaw =
          (Measure.map Prod.snd (refreshBatchLaw.prod differenceBatchLaw)).prod
            compressionLaw := by
        simpa [noiseOfRest, restLaw, noiseLaw, Prod.map] using
          (MeasureTheory.Measure.map_prod_map
            (refreshBatchLaw.prod differenceBatchLaw) compressionLaw
            measurable_snd measurable_id).symm
      _ = noiseLaw := by
        rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
  have hnoiseMP : MeasurePreserving noiseOfRest restLaw noiseLaw :=
    ⟨hnoiseOfRest, hnoiseOfRestLaw⟩
  have hinnovationSource :=
    onlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_joint_aestronglyMeasurable
      A run law ℒ hKernel k
  have hinnovationRest : AEStronglyMeasurable
      (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem (noiseOfRest p.2).1 i
                (run (k + 1) p.1).x (run k p.1).x)
              ((noiseOfRest p.2).2 i) -
            localGradientDifference P i
              (run (k + 1) p.1).x (run k p.1).x))
      (law.prod restLaw) := by
    have hpull := hinnovationSource.comp_measurePreserving
      ((MeasurePreserving.id law).prod hnoiseMP)
    simpa [noiseOfRest, noiseLaw, differenceBatchLaw, compressionLaw,
      onlineDifferenceCompressionLaw, P, Function.comp_def] using hpull
  have hfull : AEStronglyMeasurable
      (fun p : (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ×
          ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        ‖((run k p.1).g - globalGradient P (run k p.1).x) +
          average (fun i : Worker n ↦
            A.quantizer.apply
                (onlineBatchDifference A.problem (noiseOfRest p.2).1 i
                  (run (k + 1) p.1).x (run k p.1).x)
                ((noiseOfRest p.2).2 i) -
              localGradientDifference P i
                (run (k + 1) p.1).x (run k p.1).x)‖ ^ 2)
      (law.prod restLaw) := by
    have hv := hresidual.comp_fst.add hinnovationRest
    simpa [pow_two] using hv.norm.mul hv.norm
  have hprefixComp :
      (fun z :
          (((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        F (fun j : Fin k ↦ z.2 j.1) z.1) =
      (fun z ↦
        ‖((run k z.2).g - globalGradient P (run k z.2).x) +
          average (fun i : Worker n ↦
            A.quantizer.apply
                (onlineBatchDifference A.problem (noiseOfRest z.1).1 i
                  (run (k + 1) z.2).x (run k z.2).x)
                ((noiseOfRest z.1).2 i) -
              localGradientDifference P i
                (run (k + 1) z.2).x (run k z.2).x)‖ ^ 2) := by
    funext z
    have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := z.2)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ z.2 j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])
    have hps : onlineProofExactPrefixState A x0 hBatch fallback k
        (fun j : Fin k ↦ z.2 j.1) = run k z.2 := by
      exact hs.symm
    dsimp [F, residualPrefix, innovationPrefix, prefixState]
    rw [hps]
    rfl
  have hfullSwap : AEStronglyMeasurable
      (fun z :
          (((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        F (fun j : Fin k ↦ z.2 j.1) z.1)
      (restLaw.prod law) := by
    rw [hprefixComp]
    have hs := hfull.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := restLaw) (ν := law))
    simpa using hs
  have hfiniteSwap : AEStronglyMeasurable
      (fun z :
          (((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        F z.2 z.1)
      (restLaw.prod prefixLaw) := by
    exact aestronglyMeasurable_initial_prefix_of_comp_general
      restLaw roundLaw k (fun z ↦ F z.2 z.1) hfullSwap
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod restLaw) := by
    have hs := hfiniteSwap.comp_measurePreserving
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixLaw) (ν := restLaw))
    simpa [Function.uncurry] using hs
  have hi := iidStream_prefix_current_snd_kernel_indep_fst
    coinLaw restLaw k F hF
  have hcalc : ∀ path : ℕ → OnlineRoundNoise n b b0 Sample Ξ,
      F (fun j : Fin k ↦ path j.1) (path k).2 =
        ‖((run k path).g - globalGradient P (run k path).x) +
          average (fun i : Worker n ↦
            A.quantizer.apply
                (onlineBatchDifference A.problem (path k).2.1.2 i
                  (run (k + 1) path).x (run k path).x)
                ((path k).2.2 i) -
              localGradientDifference P i
                (run (k + 1) path).x (run k path).x)‖ ^ 2 := by
    intro path
    have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := path)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ path j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])
    have hps : onlineProofExactPrefixState A x0 hBatch fallback k
        (fun j : Fin k ↦ path j.1) = run k path := by
      exact hs.symm
    dsimp [F, residualPrefix, innovationPrefix, prefixState, noiseOfRest]
    rw [hps]
    rfl
  simpa [coinLaw, restLaw, roundLaw, refreshBatchLaw,
    differenceBatchLaw, compressionLaw, law, P, run,
    onlineProofExactPathLaw, onlineRoundLaw] using
    hi.congr (Filter.Eventually.of_forall hcalc)
      (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Exact executable Algorithm 3 instantiation of the same A-track supplier.
The statement is polymorphic in `b` and `b0`, so it applies independently to
the nonconvex and PL schedule families used by the measured release theorem.
Its process, law, initialization minibatch, worker, round, and fresh-sample
law are exactly those of `onlineProcess` and `onlinePathLaw`. -/
theorem onlineProcess_adaptiveGradient_source_regular
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒ sigma : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (k : ℕ) (i : Worker n) :
    (∀ᵐ z ∂(onlinePathLaw (b := b) (b0 := b0) A).prod
        (A.problem.sampleLaw i),
      GenuineSampleGradientAt A.problem i z.2
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch k z.1).x
        (stochasticGradient A.problem i z.2
          (onlineProcess (b := b) (b0 := b0) A x0 hBatch k z.1).x)) ∧
      AEStronglyMeasurable
        (fun z ↦ stochasticGradient A.problem i z.2
          (onlineProcess (b := b) (b0 := b0) A x0 hBatch k z.1).x)
        ((onlinePathLaw (b := b) (b0 := b0) A).prod
          (A.problem.sampleLaw i)) := by
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
  haveI : IsProbabilityMeasure (onlinePathLaw (b := b) (b0 := b0) A) := by
    unfold onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  exact
    onlineAssumption32GeneratedConditionalKernel_adaptiveGradient_source_regular
      hKernel hLiteral x0 (fun _ ↦ rfl) k i

/-- The bounded generated problem satisfies the source-level objective,
smoothness, literal fixed-query moment, PL, quantizer, batch, and
average-smoothness hypotheses.  This package deliberately makes no claim yet
about failure of a requested D.3/D.4 generated expectation. -/
theorem onlineGeneratedBoundedRefresh_source_hypotheses :
    HasUniformLowerBound
        (onlineLocalProblem onlineGeneratedBoundedRefreshData.problem) (-50) ∧
      IsLocallySmooth
        (onlineLocalProblem onlineGeneratedBoundedRefreshData.problem)
        (fun _ => 1) ∧
      OnlineAssumption33Literal onlineGeneratedBoundedRefreshData.problem
        (fun _ => 1) ∧
      SatisfiesPL (onlineLocalProblem onlineGeneratedBoundedRefreshData.problem)
        ⟨1, by norm_num⟩ onlineGeneratedBoundedRefreshMinimizer ∧
      IsUnbiasedQuantizer onlineGeneratedBoundedRefreshData.quantizer 1 ∧
      OnlineBatchAdmissible onlineGeneratedRefreshBatch
        onlineGeneratedDifferenceBatch ∧
      OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedBoundedRefreshData.problem
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedBoundedRefreshData
          onlineGeneratedBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (fun _ => 0) := by
  exact ⟨onlineGeneratedBoundedRefresh_hasUniformLowerBound,
    onlineGeneratedBoundedRefresh_isLocallySmooth,
    onlineGeneratedBoundedRefresh_literalVariance,
    onlineGeneratedBoundedRefresh_satisfiesPL,
    onlineGeneratedIdentityQuantizer_unbiased,
    onlineGeneratedRefresh_batchAdmissible,
    onlineGeneratedBoundedRefresh_averageSmoothness _⟩

/-! ## Fresh quarter-quadratic generated refresh candidate

This fresh namespace-by-prefix variant preserves every earlier public bounded
candidate declaration while retaining the nontrivial time-two generated query
needed for the exact D.3/D.4 observable audit.

The earlier atomless-diagonal construction has a linear expected objective and
therefore does not satisfy Assumption 1.1.  Adding the same smooth quadratic to
every sampled loss leaves its sample-selected jump in place, while making the
expected objective bounded below.  The declarations below isolate that
source-hypothesis repair; they do not claim the final generated-process defect
until the modified process-level diagonal calculation has also been proved. -/

noncomputable def onlineGeneratedQuarterBoundedRefreshLoss
    (s : OnlineGeneratedRefreshSample 0) :
    Point oldInitialBoundCounterexampleDimension → ℝ :=
  fun x ↦ onlineGeneratedRefreshLoss s x + ‖x‖ ^ 2 / 4

noncomputable def onlineGeneratedQuarterBoundedRefreshProblem :
    OnlineProblem oldInitialBoundCounterexampleDimension
      onlineCoarseCounterexampleWorkers OnlineGeneratedRefreshSample where
  sampleLoss _ s := onlineGeneratedQuarterBoundedRefreshLoss s
  sampleLaw := onlineGeneratedRefreshProblem.sampleLaw
  sampleLaw_isProbability := onlineGeneratedRefreshProblem.sampleLaw_isProbability
  sampleLoss_integrable i x := by
    letI : IsProbabilityMeasure
        (onlineGeneratedRefreshProblem.sampleLaw i) :=
      onlineGeneratedRefreshProblem.sampleLaw_isProbability i
    have hold : Integrable
        (fun s ↦ onlineGeneratedRefreshLoss s x)
        (onlineGeneratedRefreshProblem.sampleLaw i) :=
      onlineGeneratedRefreshProblem.sampleLoss_integrable i x
    have hquad : Integrable
        (fun _ : OnlineGeneratedRefreshSample i ↦ ‖x‖ ^ 2 / 4)
        (onlineGeneratedRefreshProblem.sampleLaw i) :=
      integrable_const (c := ‖x‖ ^ 2 / 4)
    simpa [onlineGeneratedQuarterBoundedRefreshLoss] using hold.add hquad

theorem onlineGeneratedQuarterBoundedRefresh_expectedSampleLoss
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    expectedSampleLoss onlineGeneratedQuarterBoundedRefreshProblem i x =
      10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) x +
        ‖x‖ ^ 2 / 4 := by
  letI : IsProbabilityMeasure
      (onlineGeneratedRefreshProblem.sampleLaw i) :=
    onlineGeneratedRefreshProblem.sampleLaw_isProbability i
  have hold : Integrable
      (fun s ↦ onlineGeneratedRefreshLoss s x)
      (onlineGeneratedRefreshProblem.sampleLaw i) :=
    onlineGeneratedRefreshProblem.sampleLoss_integrable i x
  have hquad : Integrable
      (fun _ : OnlineGeneratedRefreshSample i ↦ ‖x‖ ^ 2 / 4)
      (onlineGeneratedRefreshProblem.sampleLaw i) :=
    integrable_const (c := ‖x‖ ^ 2 / 4)
  unfold expectedSampleLoss
  change (∫ s, (onlineGeneratedRefreshLoss s x + ‖x‖ ^ 2 / 4)
      ∂onlineGeneratedRefreshProblem.sampleLaw i) = _
  rw [integral_add hold hquad, integral_const, probReal_univ, one_smul]
  have hexpected := onlineGeneratedRefresh_expectedSampleLoss i x
  unfold expectedSampleLoss at hexpected
  change (∫ a : OnlineGeneratedRefreshSample 0,
      onlineGeneratedRefreshLoss a x
        ∂onlineGeneratedRefreshProblem.sampleLaw i) = _ at hexpected
  rw [hexpected]

theorem onlineGeneratedQuarterBoundedRefresh_quadratic_hasGradientAt
    (x : Point oldInitialBoundCounterexampleDimension) :
    HasGradientAt (fun y : Point oldInitialBoundCounterexampleDimension =>
      ‖y‖ ^ 2 / 4) ((2 : ℝ)⁻¹ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (4 : ℝ)⁻¹ using 1
  · funext z
    ring
  · ext z
    simp [InnerProductSpace.toDual_apply_apply]
    ring

theorem onlineGeneratedQuarterBoundedRefresh_expected_hasGradientAt
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    HasGradientAt
      ((onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem).localLoss i)
      (10 • oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • x) x := by
  have hfun :
      (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem).localLoss i =
        fun y => 10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) y +
          ‖y‖ ^ 2 / 4 := by
    funext y
    exact onlineGeneratedQuarterBoundedRefresh_expectedSampleLoss i y
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  have hlinear : HasFDerivAt
      (fun y : Point oldInitialBoundCounterexampleDimension =>
        10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) y)
      (InnerProductSpace.toDual ℝ _ (10 • oldInitialBoundCounterexampleDirection)) x := by
    convert (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt.const_mul 10
      using 1
    ext z
    simp [InnerProductSpace.toDual_apply_apply]
  have hquad :=
    (onlineGeneratedQuarterBoundedRefresh_quadratic_hasGradientAt x).hasFDerivAt
  convert hlinear.add hquad using 1
  ext z
  simp [InnerProductSpace.toDual_apply_apply]

theorem onlineGeneratedQuarterBoundedRefresh_localGradient
    (i : Worker onlineCoarseCounterexampleWorkers)
    (x : Point oldInitialBoundCounterexampleDimension) :
    localGradient (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) i x =
      10 • oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • x := by
  unfold localGradient
  exact (onlineGeneratedQuarterBoundedRefresh_expected_hasGradientAt i x).gradient

theorem onlineGeneratedQuarterBoundedRefresh_isLocallySmooth :
    IsLocallySmooth
      (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) (fun _ => 1) := by
  constructor
  · intro i x
    exact (onlineGeneratedQuarterBoundedRefresh_expected_hasGradientAt i x).differentiableAt
  · intro i x y
    rw [onlineGeneratedQuarterBoundedRefresh_localGradient i x,
      onlineGeneratedQuarterBoundedRefresh_localGradient i y]
    simp only [one_mul]
    rw [show 10 • oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • x -
      (10 • oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • y) =
        (2 : ℝ)⁻¹ • (x - y) by module]
    rw [norm_smul]
    norm_num
    nlinarith [norm_nonneg (x - y)]

theorem onlineGeneratedQuarterBoundedRefresh_globalGradient
    (x : Point oldInitialBoundCounterexampleDimension) :
    globalGradient (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) x =
      10 • oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • x := by
  rw [globalGradient_eq_averageLocalGradient
    (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
    onlineGeneratedQuarterBoundedRefresh_isLocallySmooth.1 x]
  unfold averageLocalGradient average SOptLib.finiteUniformAverage
  norm_num [onlineGeneratedQuarterBoundedRefresh_localGradient,
    onlineCoarseCounterexampleWorkers]

theorem onlineGeneratedQuarterBoundedRefresh_add_quadratic_hasGradientAt
    {f : Point oldInitialBoundCounterexampleDimension → ℝ}
    {g x : Point oldInitialBoundCounterexampleDimension}
    (h : HasGradientAt f g x) :
    HasGradientAt (fun y => f y + ‖y‖ ^ 2 / 4)
      (g + (2 : ℝ)⁻¹ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hquad :=
    (onlineGeneratedQuarterBoundedRefresh_quadratic_hasGradientAt x).hasFDerivAt
  convert h.hasFDerivAt.add hquad using 1
  ext z
  simp [InnerProductSpace.toDual_apply_apply]

theorem onlineGeneratedQuarterBoundedRefreshLoss_gradient_at_query
    (s : OnlineGeneratedRefreshSample 0) (q : ℝ) :
    gradient (onlineGeneratedQuarterBoundedRefreshLoss s)
        (onlineCoarseCounterexamplePoint q) =
      if q = s.1.val then 0
      else onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection +
        (2 : ℝ)⁻¹ • onlineCoarseCounterexamplePoint q := by
  by_cases hq : q = s.1.val
  · subst q
    rw [if_pos rfl, gradient_eq_zero_of_not_differentiableAt]
    intro hdiff
    have hquad : DifferentiableAt ℝ
        (fun y : Point oldInitialBoundCounterexampleDimension => ‖y‖ ^ 2 / 4)
        (onlineCoarseCounterexamplePoint s.1.val) :=
      (onlineGeneratedQuarterBoundedRefresh_quadratic_hasGradientAt _).differentiableAt
    have holdDiff : DifferentiableAt ℝ (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint s.1.val) := by
      have hsub := hdiff.sub hquad
      convert hsub using 1
      funext y
      simp [onlineGeneratedQuarterBoundedRefreshLoss]
    have hcont : ContinuousAt (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint s.1.val) := holdDiff.continuousAt
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
      fun h => hq (onlineCoarseCounterexamplePoint_injective h)
    let base := onlineGeneratedRefreshSlope s •
      innerSL ℝ oldInitialBoundCounterexampleDirection
    have hevent : onlineGeneratedRefreshLoss s =ᶠ[
        nhds (onlineCoarseCounterexamplePoint q)] base := by
      filter_upwards [eventually_ne_nhds hpoint_ne] with y hy
      simp [onlineGeneratedRefreshLoss, base, Function.update_of_ne hy]
    have hbaseGradient : HasGradientAt base
        (onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint q) := by
      rw [hasGradientAt_iff_hasFDerivAt]
      convert (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt.const_smul
        (onlineGeneratedRefreshSlope s) using 1
      ext z
      simp [InnerProductSpace.toDual_apply_apply]
    have holdGradient : HasGradientAt (onlineGeneratedRefreshLoss s)
        (onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint q) :=
      hbaseGradient.congr_of_eventuallyEq hevent
    exact (onlineGeneratedQuarterBoundedRefresh_add_quadratic_hasGradientAt
      holdGradient).gradient

/-- Exact genuine-gradient domain of the quarter-bounded sampled loss.  The
sample-selected diagonal is excluded because the loss has a unit jump there;
away from it the displayed source gradient genuinely exists. -/
theorem onlineGeneratedQuarterBoundedRefreshLoss_differentiableAt_iff
    (s : OnlineGeneratedRefreshSample 0) (q : ℝ) :
    DifferentiableAt ℝ (onlineGeneratedQuarterBoundedRefreshLoss s)
        (onlineCoarseCounterexamplePoint q) ↔
      q ≠ s.1.val := by
  constructor
  · intro hdiff hq
    subst q
    have hquad : DifferentiableAt ℝ
        (fun y : Point oldInitialBoundCounterexampleDimension => ‖y‖ ^ 2 / 4)
        (onlineCoarseCounterexamplePoint s.1.val) :=
      (onlineGeneratedQuarterBoundedRefresh_quadratic_hasGradientAt _).differentiableAt
    have holdDiff : DifferentiableAt ℝ (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint s.1.val) := by
      have hsub := hdiff.sub hquad
      convert hsub using 1
      funext y
      simp [onlineGeneratedQuarterBoundedRefreshLoss]
    have hcont : ContinuousAt (onlineGeneratedRefreshLoss s)
        (onlineCoarseCounterexamplePoint s.1.val) := holdDiff.continuousAt
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
  · intro hq
    have hpoint_ne : onlineCoarseCounterexamplePoint q ≠
        onlineCoarseCounterexamplePoint s.1.val :=
      fun h => hq (onlineCoarseCounterexamplePoint_injective h)
    let base := onlineGeneratedRefreshSlope s •
      innerSL ℝ oldInitialBoundCounterexampleDirection
    have hevent : onlineGeneratedRefreshLoss s =ᶠ[
        nhds (onlineCoarseCounterexamplePoint q)] base := by
      filter_upwards [eventually_ne_nhds hpoint_ne] with y hy
      simp [onlineGeneratedRefreshLoss, base, Function.update_of_ne hy]
    have hbaseGradient : HasGradientAt base
        (onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint q) := by
      rw [hasGradientAt_iff_hasFDerivAt]
      convert (innerSL ℝ oldInitialBoundCounterexampleDirection).hasFDerivAt.const_smul
        (onlineGeneratedRefreshSlope s) using 1
      ext z
      simp [InnerProductSpace.toDual_apply_apply]
    have holdGradient : HasGradientAt (onlineGeneratedRefreshLoss s)
        (onlineGeneratedRefreshSlope s •
          oldInitialBoundCounterexampleDirection)
        (onlineCoarseCounterexamplePoint q) :=
      hbaseGradient.congr_of_eventuallyEq hevent
    exact (onlineGeneratedQuarterBoundedRefresh_add_quadratic_hasGradientAt
      holdGradient).differentiableAt

/-- On the excluded diagonal, the formal stochastic gradient is precisely
Mathlib's zero fallback, and there is no genuine sampled gradient to which it
could transfer. -/
theorem onlineGeneratedQuarterBoundedRefresh_diagonal_totalization_only
    (s : OnlineGeneratedRefreshSample 0) :
    stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s
        (onlineCoarseCounterexamplePoint s.1.val) = 0 ∧
      ¬ ∃ g, GenuineSampleGradientAt
        onlineGeneratedQuarterBoundedRefreshProblem 0 s
          (onlineCoarseCounterexamplePoint s.1.val) g := by
  constructor
  · simpa [stochasticGradient, onlineGeneratedQuarterBoundedRefreshProblem]
      using onlineGeneratedQuarterBoundedRefreshLoss_gradient_at_query s s.1.val
  · rintro ⟨g, hg⟩
    have hdiff := hg.differentiableAt
    exact (onlineGeneratedQuarterBoundedRefreshLoss_differentiableAt_iff
      s s.1.val).mp hdiff rfl

/-- Every fixed query has a genuine sampled gradient almost surely.  Thus the
generated failure below is not caused by omitting the source's fixed-query
gradient semantics; it appears only after the query is coupled to a fresh
sample in the Algorithm 3 transition. -/
theorem onlineGeneratedQuarterBoundedRefresh_fixedQuery_genuineGradient_ae
    (x : Point oldInitialBoundCounterexampleDimension) :
    ∀ᵐ s ∂onlineGeneratedQuarterBoundedRefreshProblem.sampleLaw 0,
      ∃ g, GenuineSampleGradientAt onlineGeneratedQuarterBoundedRefreshProblem
        0 s x g := by
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
  have hdiff : DifferentiableAt ℝ
      (onlineGeneratedQuarterBoundedRefreshLoss s) x := by
    rw [← onlineCoarseCounterexamplePoint_coordinate x]
    exact (onlineGeneratedQuarterBoundedRefreshLoss_differentiableAt_iff
      s (x 0)).2 hne
  exact ⟨stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s x,
    hdiff.hasGradientAt⟩

theorem onlineGeneratedQuarterBoundedRefresh_stochasticGradient_ae
    (x : Point oldInitialBoundCounterexampleDimension) :
    (fun s : OnlineGeneratedRefreshSample 0 =>
      stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s x) =ᵐ[
        onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)]
      (fun s => onlineGeneratedRefreshSlope s •
        oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • x) := by
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
  simpa [stochasticGradient, onlineGeneratedQuarterBoundedRefreshProblem, hne] using
    onlineGeneratedQuarterBoundedRefreshLoss_gradient_at_query s (x 0)

theorem onlineGeneratedQuarterBoundedRefresh_literalVariance :
    OnlineAssumption33Literal onlineGeneratedQuarterBoundedRefreshProblem
      (fun _ => 1) := by
  constructor
  · intro i
    norm_num
  · intro i x
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    let μ := onlineCoarseLaw.prod (ProbabilityTheory.gaussianReal 0 1)
    let e := oldInitialBoundCounterexampleDirection
    have hold := onlineGeneratedRefresh_literalVariance.2 0 x
    have holdAE := onlineGeneratedRefresh_stochasticGradient_ae x
    have hnewAE := onlineGeneratedQuarterBoundedRefresh_stochasticGradient_ae x
    have hslopeVec : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 =>
          onlineGeneratedRefreshSlope s • e) μ := by
      exact hold.1.congr holdAE
    have hshift : Integrable
        (fun s : OnlineGeneratedRefreshSample 0 =>
          onlineGeneratedRefreshSlope s • e + (2 : ℝ)⁻¹ • x) μ :=
      hslopeVec.add (integrable_const (c := (2 : ℝ)⁻¹ • x))
    have hgrad : Integrable
        (fun s => stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s x)
        μ := hshift.congr hnewAE.symm
    have hresidualAE :
        (fun s =>
          ‖stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s x -
            localGradient
              (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) 0 x‖ ^ 2)
          =ᵐ[μ]
        (fun s =>
          ‖stochasticGradient onlineGeneratedRefreshProblem 0 s x -
            localGradient (onlineLocalProblem onlineGeneratedRefreshProblem) 0 x‖ ^ 2) := by
      filter_upwards [hnewAE, holdAE] with s hnew hold
      rw [hnew, hold, onlineGeneratedQuarterBoundedRefresh_localGradient,
        onlineGeneratedRefresh_localGradient]
      congr 2
      module
    have hresidual : Integrable
        (fun s =>
          ‖stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s x -
            localGradient
              (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) 0 x‖ ^ 2)
        μ := hold.2.1.congr hresidualAE.symm
    refine ⟨hgrad, hresidual, ?_, ?_⟩
    · change (∫ s : OnlineGeneratedRefreshSample 0,
          stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s x ∂μ) = _
      rw [integral_congr_ae hnewAE, integral_add hslopeVec
        (integrable_const (c := (2 : ℝ)⁻¹ • x)), integral_const]
      have hμ : μ.real Set.univ = 1 := by
        simp [μ]
      rw [hμ, one_smul]
      have holdMean := hold.2.2.1
      change (∫ s : OnlineGeneratedRefreshSample 0,
          stochasticGradient onlineGeneratedRefreshProblem 0 s x ∂μ) = _ at holdMean
      rw [integral_congr_ae holdAE] at holdMean
      rw [holdMean, onlineGeneratedRefresh_localGradient,
        onlineGeneratedQuarterBoundedRefresh_localGradient]
    · change (∫ s : OnlineGeneratedRefreshSample 0,
          ‖stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0 s x -
            localGradient
              (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) 0 x‖ ^ 2
          ∂μ) ≤ 1 ^ 2
      rw [integral_congr_ae hresidualAE]
      exact hold.2.2.2

theorem onlineGeneratedQuarterBoundedDifference_ae_eq_half_sub
    (x y : Point oldInitialBoundCounterexampleDimension) :
    (fun batch => onlineBatchDifference onlineGeneratedQuarterBoundedRefreshProblem
      batch 0 x y) =ᵐ[
        onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
          onlineGeneratedDifferenceBatch]
      (fun _ => (2 : ℝ)⁻¹ • (x - y)) := by
  let coord := fun batch :
      (w : Worker onlineCoarseCounterexampleWorkers) →
        Fin onlineGeneratedDifferenceBatch.1 → OnlineGeneratedRefreshSample w =>
    batch 0 0
  have hcoord : Measurable coord := by
    dsimp [coord]
    fun_prop
  have hmap : Measure.map coord
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
        onlineGeneratedDifferenceBatch) =
      onlineGeneratedQuarterBoundedRefreshProblem.sampleLaw 0 := by
    simpa [coord] using
      (onlineBatchLaw_coordinate_marginal onlineGeneratedQuarterBoundedRefreshProblem
        (b := onlineGeneratedDifferenceBatch) 0 0)
  have hqmp : Measure.QuasiMeasurePreserving coord
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
        onlineGeneratedDifferenceBatch)
      (onlineGeneratedQuarterBoundedRefreshProblem.sampleLaw 0) :=
    ⟨hcoord, by rw [hmap]⟩
  have hx := hqmp.tendsto_ae
    (onlineGeneratedQuarterBoundedRefresh_stochasticGradient_ae x)
  have hy := hqmp.tendsto_ae
    (onlineGeneratedQuarterBoundedRefresh_stochasticGradient_ae y)
  filter_upwards [hx, hy] with batch hx hy
  change stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
      (batch 0 0) x =
    onlineGeneratedRefreshSlope (batch 0 0) •
      oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • x at hx
  change stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
      (batch 0 0) y =
    onlineGeneratedRefreshSlope (batch 0 0) •
      oldInitialBoundCounterexampleDirection + (2 : ℝ)⁻¹ • y at hy
  unfold onlineBatchDifference average SOptLib.finiteUniformAverage
  rw [Fin.sum_univ_one, hx, hy]
  norm_num
  module

theorem onlineGeneratedQuarterBoundedRefresh_averageSmoothness
    {Ω : Type*} [MeasurableSpace Ω]
    (run : ℕ → Ω → State oldInitialBoundCounterexampleDimension) :
    OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
      onlineGeneratedQuarterBoundedRefreshProblem run (fun _ => 0) := by
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure (onlineGeneratedQuarterBoundedRefreshProblem.sampleLaw w) :=
    onlineGeneratedQuarterBoundedRefreshProblem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
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
    have hdiff := onlineGeneratedQuarterBoundedDifference_ae_eq_half_sub xNext x
    have hlocal : localGradientDifference
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
          0 xNext x = (2 : ℝ)⁻¹ • (xNext - x) := by
      unfold localGradientDifference
      rw [onlineGeneratedQuarterBoundedRefresh_localGradient 0 xNext,
        onlineGeneratedQuarterBoundedRefresh_localGradient 0 x]
      module
    have hint : Integrable
        (fun batch => onlineBatchDifference
          onlineGeneratedQuarterBoundedRefreshProblem batch 0 xNext x)
        (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
          onlineGeneratedDifferenceBatch) :=
      (integrable_const (c := (2 : ℝ)⁻¹ • (xNext - x))).congr hdiff.symm
    have hsqAE :
        (fun batch =>
          ‖onlineBatchDifference onlineGeneratedQuarterBoundedRefreshProblem batch
              0 xNext x -
            localGradientDifference
              (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
              0 xNext x‖ ^ 2) =ᵐ[
          onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
            onlineGeneratedDifferenceBatch]
          (fun _ => 0) := by
      filter_upwards [hdiff] with batch hb
      simp [hb, hlocal]
    have hsq : Integrable
        (fun batch =>
          ‖onlineBatchDifference onlineGeneratedQuarterBoundedRefreshProblem batch
              0 xNext x -
            localGradientDifference
              (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
              0 xNext x‖ ^ 2)
        (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
          onlineGeneratedDifferenceBatch) :=
      (integrable_const (c := (0 : ℝ))).congr hsqAE.symm
    refine ⟨hint, hsq, ?_, ?_⟩
    · rw [integral_congr_ae hdiff, hlocal]
      simp
    · rw [integral_congr_ae hsqAE]
      simp

/-- The counterexample's Assumption 3.2 witness uses genuine sampled
gradients at the two generated queries.  Conditional on a path those queries
are fixed, and the independently drawn difference minibatch avoids both
sample-selected singularities almost surely. -/
theorem onlineGeneratedQuarterBoundedRefresh_assumption32Genuine
    {Ω : Type*} [MeasurableSpace Ω]
    (run : ℕ → Ω → State oldInitialBoundCounterexampleDimension) :
    OnlineAssumption32Genuine (b0 := onlineGeneratedDifferenceBatch)
      onlineGeneratedQuarterBoundedRefreshProblem run (fun _ ↦ 0) := by
  let batchLaw := onlineBatchLaw onlineGeneratedQuarterBoundedRefreshProblem
    onlineGeneratedDifferenceBatch
  have hAverage := onlineGeneratedQuarterBoundedRefresh_averageSmoothness run
  refine ⟨hAverage.1, ?_⟩
  intro k i path
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  let x := (run k path).x
  let xNext := (run (k + 1) path).x
  rcases hAverage.2 k 0 path with
    ⟨hIntegrable, hResidualIntegrable, hMean, hVariance⟩
  refine ⟨(fun batch ↦ onlineBatchDifference
      onlineGeneratedQuarterBoundedRefreshProblem batch 0 xNext x), ?_,
    hIntegrable, hResidualIntegrable, hMean, hVariance⟩
  let coord := fun batch :
      (w : Worker onlineCoarseCounterexampleWorkers) →
        Fin onlineGeneratedDifferenceBatch.1 → OnlineGeneratedRefreshSample w ↦
    batch 0 0
  have hcoord : Measurable coord := by
    dsimp [coord]
    fun_prop
  have hmap : Measure.map coord batchLaw =
      onlineGeneratedQuarterBoundedRefreshProblem.sampleLaw 0 := by
    simpa [batchLaw, coord] using
      (onlineBatchLaw_coordinate_marginal
        onlineGeneratedQuarterBoundedRefreshProblem
        (b := onlineGeneratedDifferenceBatch) 0 0)
  have hqmp : Measure.QuasiMeasurePreserving coord batchLaw
      (onlineGeneratedQuarterBoundedRefreshProblem.sampleLaw 0) :=
    ⟨hcoord, by rw [hmap]⟩
  have hNext := hqmp.tendsto_ae
    (onlineGeneratedQuarterBoundedRefresh_fixedQuery_genuineGradient_ae xNext)
  have hCurrent := hqmp.tendsto_ae
    (onlineGeneratedQuarterBoundedRefresh_fixedQuery_genuineGradient_ae x)
  filter_upwards [hNext, hCurrent] with batch hNextBatch hCurrentBatch
  rcases hNextBatch with ⟨gNext, hgNext⟩
  rcases hCurrentBatch with ⟨gCurrent, hgCurrent⟩
  refine ⟨(fun _ ↦ gNext), (fun _ ↦ gCurrent), ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    exact hgNext
  · intro j
    fin_cases j
    exact hgCurrent
  · unfold onlineBatchDifference
    congr 1
    funext j
    fin_cases j
    change stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
        (batch 0 0) xNext -
      stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
        (batch 0 0) x = gNext - gCurrent
    change GenuineSampleGradientAt onlineGeneratedQuarterBoundedRefreshProblem
      0 (batch 0 0) xNext gNext at hgNext
    change GenuineSampleGradientAt onlineGeneratedQuarterBoundedRefreshProblem
      0 (batch 0 0) x gCurrent at hgCurrent
    rw [stochasticGradient_eq_of_genuineSampleGradientAt hgNext,
      stochasticGradient_eq_of_genuineSampleGradientAt hgCurrent]

theorem onlineGeneratedQuarterBoundedRefresh_globalObjective
    (x : Point oldInitialBoundCounterexampleDimension) :
    globalObjective (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) x =
      10 * (innerSL ℝ oldInitialBoundCounterexampleDirection) x +
        ‖x‖ ^ 2 / 4 := by
  unfold globalObjective average SOptLib.finiteUniformAverage onlineLocalProblem
  norm_num [onlineGeneratedQuarterBoundedRefresh_expectedSampleLoss,
    onlineCoarseCounterexampleWorkers]

noncomputable def onlineGeneratedQuarterBoundedRefreshMinimizer :
    Point oldInitialBoundCounterexampleDimension :=
  (-20 : ℝ) • oldInitialBoundCounterexampleDirection

theorem onlineGeneratedQuarterBoundedRefresh_objective_minimizer :
    globalObjective (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
      onlineGeneratedQuarterBoundedRefreshMinimizer = -100 := by
  rw [onlineGeneratedQuarterBoundedRefresh_globalObjective]
  have hinner :
      (innerSL ℝ oldInitialBoundCounterexampleDirection)
        onlineGeneratedQuarterBoundedRefreshMinimizer = -20 := by
    rw [onlineGeneratedQuarterBoundedRefreshMinimizer, map_smul]
    norm_num [oldInitialBoundCounterexampleDirection,
      innerSL_apply_apply, PiLp.inner_apply]
  have hnorm : ‖onlineGeneratedQuarterBoundedRefreshMinimizer‖ ^ 2 = 400 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
    norm_num [onlineGeneratedQuarterBoundedRefreshMinimizer,
      oldInitialBoundCounterexampleDirection]
  rw [hinner, hnorm]
  norm_num

theorem onlineGeneratedQuarterBoundedRefresh_gradient_norm_sq
    (x : Point oldInitialBoundCounterexampleDimension) :
    ‖globalGradient (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) x‖ ^ 2 =
      (x 0 / 2 + 10) ^ 2 := by
  rw [onlineGeneratedQuarterBoundedRefresh_globalGradient,
    EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
  simp [oldInitialBoundCounterexampleDirection, Real.norm_eq_abs, sq_abs]
  ring

theorem onlineGeneratedQuarterBoundedRefresh_satisfiesPL :
    SatisfiesPL (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
      ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineGeneratedQuarterBoundedRefreshMinimizer := by
  constructor
  · intro x
    rw [onlineGeneratedQuarterBoundedRefresh_objective_minimizer,
      onlineGeneratedQuarterBoundedRefresh_globalObjective]
    have hs : 0 ≤ (x 0 + 20) ^ 2 := sq_nonneg (x 0 + 20)
    have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    rw [show (innerSL ℝ oldInitialBoundCounterexampleDirection) x = x 0 by
      change inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0
      simp only [PiLp.inner_apply]
      rw [Fin.sum_univ_one, real_inner_eq_re_inner ℝ, RCLike.inner_apply]
      simp]
    nlinarith
  · intro x
    rw [onlineGeneratedQuarterBoundedRefresh_objective_minimizer,
      onlineGeneratedQuarterBoundedRefresh_globalObjective,
      onlineGeneratedQuarterBoundedRefresh_gradient_norm_sq]
    have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    rw [show (innerSL ℝ oldInitialBoundCounterexampleDirection) x = x 0 by
      change inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0
      simp only [PiLp.inner_apply]
      rw [Fin.sum_univ_one]
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
      simp]
    norm_num
    ring_nf
    exact le_rfl

theorem onlineGeneratedQuarterBoundedRefresh_hasUniformLowerBound :
    HasUniformLowerBound
      (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) (-100) := by
  intro x
  rw [onlineGeneratedQuarterBoundedRefresh_globalObjective]
  have hs : 0 ≤ (x 0 + 20) ^ 2 := sq_nonneg (x 0 + 20)
  have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_one]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  rw [show (innerSL ℝ oldInitialBoundCounterexampleDirection) x = x 0 by
    change inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0
    simp only [PiLp.inner_apply]
    rw [Fin.sum_univ_one]
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
    simp]
  nlinarith

noncomputable def onlineGeneratedQuarterBoundedRefreshData :
    OnlineData oldInitialBoundCounterexampleDimension
      onlineCoarseCounterexampleWorkers OnlineGeneratedRefreshSample Unit where
  problem := onlineGeneratedQuarterBoundedRefreshProblem
  quantizer := onlineGeneratedIdentityQuantizer
  stepSize := ⟨1, by norm_num⟩
  refreshProbability := 1
  refresh_admissible := by constructor <;> norm_num

noncomputable def onlineGeneratedQuarterBoundedRefreshInitialPoint :
    Point oldInitialBoundCounterexampleDimension :=
  (20 : ℝ) • oldInitialBoundCounterexampleDirection

theorem onlineGeneratedQuarterBoundedRefresh_proofExact_x_one
    (path : ℕ → OnlineRoundNoise onlineCoarseCounterexampleWorkers
      onlineGeneratedRefreshBatch onlineGeneratedDifferenceBatch
      OnlineGeneratedRefreshSample Unit) :
    (onlineProofExactProcess onlineGeneratedQuarterBoundedRefreshData
      onlineGeneratedQuarterBoundedRefreshInitialPoint
      onlineGeneratedRefresh_batchAdmissible 1 path).x =
        0 := by
  change (onlineStep onlineGeneratedQuarterBoundedRefreshData
    (onlineDriverOfRoundNoise (path 0))
    (onlineProofExactInitialState onlineGeneratedQuarterBoundedRefreshData
      onlineGeneratedQuarterBoundedRefreshInitialPoint)).x = _
  change onlineGeneratedQuarterBoundedRefreshInitialPoint -
      (onlineGeneratedQuarterBoundedRefreshData.stepSize : ℝ) •
        globalGradient
          (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
          onlineGeneratedQuarterBoundedRefreshInitialPoint = _
  rw [show globalGradient
      (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
      onlineGeneratedQuarterBoundedRefreshInitialPoint =
        20 • oldInitialBoundCounterexampleDirection by
      change globalGradient
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
        onlineGeneratedQuarterBoundedRefreshInitialPoint = _
      rw [onlineGeneratedQuarterBoundedRefresh_globalGradient]
      simp [onlineGeneratedQuarterBoundedRefreshInitialPoint]
      module]
  dsimp [onlineGeneratedQuarterBoundedRefreshData,
    onlineGeneratedQuarterBoundedRefreshInitialPoint,
    onlineGeneratedQuarterBoundedRefreshMinimizer]
  module

/-! The first refresh starts from `x¹ = 0`, exactly as in the unbounded
diagnostic, so the second query retains the same atomless formula.  Unlike the
diagnostic, the objective here is bounded below and satisfies PL. -/

noncomputable def onlineGeneratedQuarterBoundedRefreshTwoRoundState
    (pref : Fin 2 → OnlineGeneratedRefreshRound) :
    State oldInitialBoundCounterexampleDimension :=
  onlineStep onlineGeneratedQuarterBoundedRefreshData
    (onlineDriverOfRoundNoise (pref 1))
    (onlineStep onlineGeneratedQuarterBoundedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint))

noncomputable def onlineGeneratedQuarterBoundedRefreshTimeTwoQuery
    (pref : Fin 2 → OnlineGeneratedRefreshRound) : ℝ :=
  (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x 0

theorem onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula
    (pref : Fin 2 → OnlineGeneratedRefreshRound)
    (hrefresh : (pref 0).1 = true)
    (hcoarse0 : ((pref 0).2.1.1 0 0).1.val ≠ 0)
    (hcoarse1 : ((pref 0).2.1.1 0 1).1.val ≠ 0) :
    onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref =
      -(10 + (onlineGeneratedRefreshCenteredCoordinate
          ((pref 0).2.1.1 0 0).2 +
        onlineGeneratedRefreshCenteredCoordinate
          ((pref 0).2.1.1 0 1).2) / 2) := by
  have hzero0 : (0 : ℝ) ≠ ((pref 0).2.1.1 0 0).1.val := hcoarse0.symm
  have hzero1 : (0 : ℝ) ≠ ((pref 0).2.1.1 0 1).1.val := hcoarse1.symm
  unfold onlineGeneratedQuarterBoundedRefreshTimeTwoQuery
    onlineGeneratedQuarterBoundedRefreshTwoRoundState
  simp only [onlineStep]
  change (primalStep onlineGeneratedQuarterBoundedRefreshData.stepSize
    (onlineStep onlineGeneratedQuarterBoundedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint))).1 0 = _
  rw [primalStep_eq]
  have hx1 : (onlineStep onlineGeneratedQuarterBoundedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint)).x = 0 := by
    exact onlineGeneratedQuarterBoundedRefresh_proofExact_x_one
      (fun k => if k = 0 then pref 0 else pref 1)
  rw [hx1]
  simp only [zero_sub]
  have hxnext0 : primalStep onlineGeneratedQuarterBoundedRefreshData.stepSize
      (onlineProofExactInitialState onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint) = 0 := by
    change (onlineStep onlineGeneratedQuarterBoundedRefreshData
      (onlineDriverOfRoundNoise (pref 0))
      (onlineProofExactInitialState onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint)).x = 0
    exact hx1
  simp only [onlineStep]
  unfold onlineWorkerEstimator
  rw [hxnext0]
  simp only [onlineDriverOfRoundNoise, onlineGeneratedQuarterBoundedRefreshData,
    hrefresh, if_true]
  unfold average SOptLib.finiteUniformAverage
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num [onlineCoarseCounterexampleWorkers, onlineGeneratedRefreshBatch]
  rw [show stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
        ((pref 0).2.1.1 0 0) 0 =
        onlineGeneratedRefreshSlope ((pref 0).2.1.1 0 0) •
          oldInitialBoundCounterexampleDirection by
      simpa [stochasticGradient, onlineGeneratedQuarterBoundedRefreshProblem,
        onlineCoarseCounterexamplePoint, hzero0] using
        (onlineGeneratedQuarterBoundedRefreshLoss_gradient_at_query
          ((pref 0).2.1.1 0 0) 0),
    show stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
        ((pref 0).2.1.1 0 1) 0 =
        onlineGeneratedRefreshSlope ((pref 0).2.1.1 0 1) •
          oldInitialBoundCounterexampleDirection by
      simpa [stochasticGradient, onlineGeneratedQuarterBoundedRefreshProblem,
        onlineCoarseCounterexamplePoint, hzero1] using
        (onlineGeneratedQuarterBoundedRefreshLoss_gradient_at_query
          ((pref 0).2.1.1 0 1) 0)]
  simp [onlineGeneratedRefreshSlope, oldInitialBoundCounterexampleDirection]
  ring

theorem onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula_ae :
    onlineGeneratedQuarterBoundedRefreshTimeTwoQuery =ᵐ[
      Measure.infinitePi (fun _ : Fin 2 =>
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData)]
      (fun pref => onlineGeneratedRefreshRoundQueryFormula (pref 0)) := by
  have hcoin : ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
      onlineRoundLaw (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData), (pref 0).1 = true := by
    simpa [onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using
      onlineGeneratedRefreshTimeZeroCoin_ae_true
  have hsample (j : Fin 2) :
      ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedQuarterBoundedRefreshData),
        ((pref 0).2.1.1 0 j).1.val ≠ 0 := by
    simpa [onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using
      (show ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData),
        ((pref 0).2.1.1 0 j).1.val ≠ 0 from by
          have hqmp : Measure.QuasiMeasurePreserving
              (fun pref : Fin 2 → OnlineGeneratedRefreshRound =>
                (pref 0).2.1.1 0 j)
              (Measure.infinitePi (fun _ : Fin 2 =>
                onlineRoundLaw (b := onlineGeneratedRefreshBatch)
                  (b0 := onlineGeneratedDifferenceBatch)
                  onlineGeneratedRefreshData))
              (onlineGeneratedRefreshProblem.sampleLaw 0) :=
            ⟨by fun_prop, by rw [onlineGeneratedRefreshTimeZeroSample_marginal j]⟩
          exact hqmp.tendsto_ae
            onlineGeneratedRefreshSample_coarse_ne_zero_ae)
  filter_upwards [hcoin, hsample 0, hsample 1] with pref hc h0 h1
  simpa [onlineGeneratedRefreshRoundQueryFormula,
    onlineGeneratedRefreshQueryFormula] using
    onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula pref hc h0 h1

noncomputable def onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq
    (pref : Fin 2 → OnlineGeneratedRefreshRound) : ℝ :=
  ‖(onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).g -
      globalGradient
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x‖ ^ 2

theorem onlineGeneratedQuarterBoundedRefresh_timeTwo_refreshResidual_formula
    (pref : Fin 2 → OnlineGeneratedRefreshRound)
    (hrefresh : (pref 1).1 = true) :
    onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq pref =
      (((if onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref =
            ((pref 1).2.1.1 0 0).1.val then 0
          else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 0) +
            onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref / 2) +
        (if onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref =
            ((pref 1).2.1.1 0 1).1.val then 0
          else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 1) +
            onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref / 2)) / 2 -
          (10 + onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref / 2)) ^ 2 := by
  let state := onlineGeneratedQuarterBoundedRefreshTwoRoundState pref
  let q := onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref
  have hx : state.x = onlineCoarseCounterexamplePoint q := by
    ext i
    fin_cases i
    simp [state, q, onlineGeneratedQuarterBoundedRefreshTimeTwoQuery,
      onlineCoarseCounterexamplePoint,
      oldInitialBoundCounterexampleDirection]
  have hgrad (j : Fin 2) :
      stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
          ((pref 1).2.1.1 0 j) state.x =
        (if q = ((pref 1).2.1.1 0 j).1.val then 0
          else (onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 j) + q / 2) •
            oldInitialBoundCounterexampleDirection) := by
    rw [hx]
    change gradient (onlineGeneratedQuarterBoundedRefreshLoss ((pref 1).2.1.1 0 j))
      (onlineCoarseCounterexamplePoint q) = _
    rw [onlineGeneratedQuarterBoundedRefreshLoss_gradient_at_query]
    split_ifs with h
    · rfl
    · rw [onlineCoarseCounterexamplePoint]
      module
  have hg : state.g = average (fun _ : Worker onlineCoarseCounterexampleWorkers =>
      average (fun j : Fin onlineGeneratedRefreshBatch.1 =>
        stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
          ((pref 1).2.1.1 0 j) state.x)) := by
    dsimp [state, onlineGeneratedQuarterBoundedRefreshTwoRoundState]
    simp only [onlineStep, onlineDriverOfRoundNoise, hrefresh]
    rfl
  let a0 := if q = ((pref 1).2.1.1 0 0).1.val then 0
    else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 0) + q / 2
  let a1 := if q = ((pref 1).2.1.1 0 1).1.val then 0
    else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 1) + q / 2
  have herror : state.g -
      globalGradient (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
        state.x = ((a0 + a1) / 2 - (10 + q / 2)) •
          oldInitialBoundCounterexampleDirection := by
    rw [onlineGeneratedQuarterBoundedRefresh_globalGradient state.x, hx, hg]
    rw [onlineGeneratedRefresh_average_worker]
    unfold average SOptLib.finiteUniformAverage
    rw [Fin.sum_univ_two, hgrad 0, hgrad 1]
    norm_num [onlineCoarseCounterexampleWorkers, onlineGeneratedRefreshBatch,
      onlineCoarseCounterexamplePoint]
    dsimp [a0, a1]
    split_ifs <;> module
  have hdirnorm : ‖oldInitialBoundCounterexampleDirection‖ = 1 := by
    norm_num [oldInitialBoundCounterexampleDirection]
  unfold onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq
  change ‖state.g -
      globalGradient (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
        state.x‖ ^ 2 = _
  rw [herror, norm_smul, hdirnorm]
  rw [mul_one, Real.norm_eq_abs, sq_abs]

theorem onlineGeneratedQuarterBoundedRefresh_timeTwo_refreshResidual_threshold_preimage
    (pref : Fin 2 → OnlineGeneratedRefreshRound)
    (hrefresh : (pref 1).1 = true)
    (hqLower : -11 < onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref)
    (hqUpper : onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref < -9) :
    1 < onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq pref ↔
      onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref =
          ((pref 1).2.1.1 0 0).1.val ∨
        onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref =
          ((pref 1).2.1.1 0 1).1.val := by
  rw [onlineGeneratedQuarterBoundedRefresh_timeTwo_refreshResidual_formula pref hrefresh]
  let q := onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref
  let c0 := onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 0).2
  let c1 := onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 1).2
  have hc0 := abs_lt.mp
    (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
      ((pref 1).2.1.1 0 0).2)
  have hc1 := abs_lt.mp
    (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
      ((pref 1).2.1.1 0 1).2)
  change 1 <
      (((if q = ((pref 1).2.1.1 0 0).1.val then 0
          else 10 + c0 + q / 2) +
        (if q = ((pref 1).2.1.1 0 1).1.val then 0
          else 10 + c1 + q / 2)) / 2 - (10 + q / 2)) ^ 2 ↔
      q = ((pref 1).2.1.1 0 0).1.val ∨
        q = ((pref 1).2.1.1 0 1).1.val
  change -11 < q at hqLower
  change q < -9 at hqUpper
  by_cases h0 : q = ((pref 1).2.1.1 0 0).1.val
  all_goals by_cases h1 : q = ((pref 1).2.1.1 0 1).1.val
  · constructor
    · intro _
      exact Or.inl h0
    · intro _
      rw [if_pos h0, if_pos h1]
      have hz : 1 < 10 + q / 2 := by linarith
      nlinarith [sq_nonneg (10 + q / 2 - 1)]
  · constructor
    · intro _
      exact Or.inl h0
    · intro _
      rw [if_pos h0, if_neg h1]
      dsimp [c1] at hc1 ⊢
      let z := (onlineGeneratedRefreshCenteredCoordinate
        ((pref 1).2.1.1 0 1).2 - 10 - q / 2) / 2
      have hz : z < -1 := by
        dsimp [z]
        linarith
      have hzsq : 1 < z ^ 2 := by nlinarith [sq_nonneg (z + 1)]
      dsimp [z] at hzsq
      nlinarith
  · constructor
    · intro _
      exact Or.inr h1
    · intro _
      rw [if_neg h0, if_pos h1]
      dsimp [c0] at hc0 ⊢
      let z := (onlineGeneratedRefreshCenteredCoordinate
        ((pref 1).2.1.1 0 0).2 - 10 - q / 2) / 2
      have hz : z < -1 := by
        dsimp [z]
        linarith
      have hzsq : 1 < z ^ 2 := by nlinarith [sq_nonneg (z + 1)]
      dsimp [z] at hzsq
      nlinarith
  · constructor
    · intro hbad
      rw [if_neg h0, if_neg h1] at hbad
      dsimp [c0, c1] at hc0 hc1 hbad
      let z := (onlineGeneratedRefreshCenteredCoordinate
        ((pref 1).2.1.1 0 0).2 +
          onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 1).2) / 2
      have hzLower : -1 < z := by
        dsimp [z]
        linarith
      have hzUpper : z < 1 := by
        dsimp [z]
        linarith
      have hz : 0 < (1 - z) * (1 + z) :=
        mul_pos (by linarith) (by linarith)
      have heq :
          ((10 + onlineGeneratedRefreshCenteredCoordinate
                ((pref 1).2.1.1 0 0).2 + q / 2 +
              (10 + onlineGeneratedRefreshCenteredCoordinate
                ((pref 1).2.1.1 0 1).2 + q / 2)) / 2 -
            (10 + q / 2)) = z := by
        dsimp [z]
        ring
      rw [heq] at hbad
      nlinarith
    · intro hor
      exact False.elim (hor.elim h0 h1)

/-- The bounded generated problem satisfies the source-level objective,
smoothness, literal fixed-query moment, PL, quantizer, batch, and
average-smoothness hypotheses.  This package deliberately makes no claim yet
about failure of a requested D.3/D.4 generated expectation. -/
theorem onlineGeneratedQuarterBoundedRefresh_source_hypotheses :
    HasUniformLowerBound
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem) (-100) ∧
      IsLocallySmooth
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        (fun _ => 1) ∧
      OnlineAssumption33Literal onlineGeneratedQuarterBoundedRefreshData.problem
        (fun _ => 1) ∧
      SatisfiesPL (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineGeneratedQuarterBoundedRefreshMinimizer ∧
      IsUnbiasedQuantizer onlineGeneratedQuarterBoundedRefreshData.quantizer 1 ∧
      OnlineBatchAdmissible onlineGeneratedRefreshBatch
        onlineGeneratedDifferenceBatch ∧
      OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData.problem
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (fun _ => 0) := by
  exact ⟨onlineGeneratedQuarterBoundedRefresh_hasUniformLowerBound,
    onlineGeneratedQuarterBoundedRefresh_isLocallySmooth,
    onlineGeneratedQuarterBoundedRefresh_literalVariance,
    onlineGeneratedQuarterBoundedRefresh_satisfiesPL,
    onlineGeneratedIdentityQuantizer_unbiased,
    onlineGeneratedRefresh_batchAdmissible,
    onlineGeneratedQuarterBoundedRefresh_averageSmoothness _⟩

/-- The failure domain of the *genuine* sampled-gradient calls in the second
refresh is not even null-measurable under the canonical two-round law.  This
statement refers directly to the sampled losses and the generated time-two
query; it does not inspect, or assign a value to, Mathlib's totalized
`stochasticGradient` on that domain. -/
theorem onlineGeneratedQuarterBoundedRefresh_genuine_gradient_failure_not_nullMeasurable :
    ¬ NullMeasurableSet
      {pref : Fin 2 → OnlineGeneratedRefreshRound |
        ¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 0))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x ∨
          ¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 1))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x}
      (Measure.infinitePi (fun _ : Fin 2 ↦
        onlineRoundLaw (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData)) := by
  let prefixLaw : Measure (Fin 2 → OnlineGeneratedRefreshRound) :=
    Measure.infinitePi (fun _ : Fin 2 ↦
      onlineRoundLaw (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData)
  intro hfailure
  have hquery : onlineGeneratedQuarterBoundedRefreshTimeTwoQuery =ᵐ[prefixLaw]
      (fun pref ↦ onlineGeneratedRefreshRoundQueryFormula (pref 0)) := by
    simpa [prefixLaw] using
      onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula_ae
  have hevent :
      ({pref : Fin 2 → OnlineGeneratedRefreshRound |
        ¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 0))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x ∨
          ¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 1))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x} :
          Set (Fin 2 → OnlineGeneratedRefreshRound)) =ᵐ[prefixLaw]
      {pref : Fin 2 → OnlineGeneratedRefreshRound |
        onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 0).1.val ∨
          onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 1).1.val} := by
    filter_upwards [hquery] with pref hq
    apply propext
    have hx : (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x =
        onlineCoarseCounterexamplePoint
          (onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref) := by
      exact (onlineCoarseCounterexamplePoint_coordinate
        (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x).symm
    change
      (¬ DifferentiableAt ℝ
          (onlineGeneratedQuarterBoundedRefreshLoss ((pref 1).2.1.1 0 0))
          (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x ∨
        ¬ DifferentiableAt ℝ
          (onlineGeneratedQuarterBoundedRefreshLoss ((pref 1).2.1.1 0 1))
          (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x) ↔
        (onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 0).1.val ∨
          onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 1).1.val)
    rw [hx,
      onlineGeneratedQuarterBoundedRefreshLoss_differentiableAt_iff,
      onlineGeneratedQuarterBoundedRefreshLoss_differentiableAt_iff]
    simp only [not_ne_iff]
    rw [hq]
  have hunion := NullMeasurableSet.congr hfailure hevent
  exact onlineGeneratedRefresh_union_diagonals_not_nullMeasurable (by
    simpa [prefixLaw, onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using hunion)

/-- The fresh bounded instance satisfies the exact Eq. (40) restriction with
`γ = L = p = ω = n = b⁰ = 1` and `ℒ = 0`. -/
theorem onlineGeneratedQuarterBoundedRefresh_nonconvex_stepsize :
    OnlineVRStepsizeCondition
      onlineGeneratedQuarterBoundedRefreshData.stepSize
      (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 1))
      (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 0))
      onlineGeneratedQuarterBoundedRefreshData.refreshProbability 1
      onlineCoarseCounterexampleWorkers onlineGeneratedDifferenceBatch := by
  unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition
  norm_num [onlineGeneratedQuarterBoundedRefreshData,
    onlineCoarseCounterexampleWorkers, onlineGeneratedDifferenceBatch,
    rootMeanSquare, meanSquare, average, SOptLib.finiteUniformAverage]

/-- The same instance satisfies Eq. (48) for its proved PL parameter `μ=1/2`.
This closes the stepsize hypothesis omitted by the earlier state-level
diagnostic. -/
theorem onlineGeneratedQuarterBoundedRefresh_PL_stepsize :
    OnlineVRPLStepsizeCondition
      onlineGeneratedQuarterBoundedRefreshData.stepSize
      (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 1))
      (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 0))
      onlineGeneratedQuarterBoundedRefreshData.refreshProbability 1
      ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineCoarseCounterexampleWorkers
      onlineGeneratedDifferenceBatch := by
  unfold OnlineVRPLStepsizeCondition FiniteSumVRPLStepsizeCondition
  norm_num [onlineGeneratedQuarterBoundedRefreshData,
    onlineCoarseCounterexampleWorkers, onlineGeneratedDifferenceBatch,
    rootMeanSquare, meanSquare, average, SOptLib.finiteUniformAverage]

/-- Compatibility package for the atomless-diagonal auxiliary obstruction.
It proves genuine-gradient moments separately after each path is fixed, but
does not supply a jointly measurable path-by-batch conditional random
variable.  Thus its `OnlineAssumption32Genuine` conjunct is weaker than the
source-faithful conditional-kernel contract above, and this theorem is not an
original-object B-track gate.  The theorem remains useful for locating the
missing joint regularity and uses no value of totalized `stochasticGradient`
on the displayed genuine-gradient failure domain. -/
theorem onlineGeneratedQuarterBoundedRefresh_original_genuine_transition_undefined :
    HasUniformLowerBound
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem) (-100) ∧
      IsLocallySmooth
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        (fun _ ↦ 1) ∧
      OnlineAssumption33Literal onlineGeneratedQuarterBoundedRefreshData.problem
        (fun _ ↦ 1) ∧
      (∀ x, ∀ᵐ s ∂onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0,
        ∃ g, GenuineSampleGradientAt
          onlineGeneratedQuarterBoundedRefreshData.problem 0 s x g) ∧
      SatisfiesPL
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineGeneratedQuarterBoundedRefreshMinimizer ∧
      IsUnbiasedQuantizer onlineGeneratedQuarterBoundedRefreshData.quantizer 1 ∧
      OnlineBatchAdmissible onlineGeneratedRefreshBatch
        onlineGeneratedDifferenceBatch ∧
      OnlineAssumption32Genuine (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData.problem
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (fun _ ↦ 0) ∧
      OnlineVRStepsizeCondition
        onlineGeneratedQuarterBoundedRefreshData.stepSize
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers ↦ 1))
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers ↦ 0))
        onlineGeneratedQuarterBoundedRefreshData.refreshProbability 1
        onlineCoarseCounterexampleWorkers onlineGeneratedDifferenceBatch ∧
      OnlineVRPLStepsizeCondition
        onlineGeneratedQuarterBoundedRefreshData.stepSize
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers ↦ 1))
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers ↦ 0))
        onlineGeneratedQuarterBoundedRefreshData.refreshProbability 1
        ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineCoarseCounterexampleWorkers
        onlineGeneratedDifferenceBatch ∧
      ¬ NullMeasurableSet
        {pref : Fin 2 → OnlineGeneratedRefreshRound |
          ¬ DifferentiableAt ℝ
              (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
                ((pref 1).2.1.1 0 0))
              (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x ∨
            ¬ DifferentiableAt ℝ
              (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
                ((pref 1).2.1.1 0 1))
              (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x}
        (Measure.infinitePi (fun _ : Fin 2 ↦
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedQuarterBoundedRefreshData)) := by
  exact ⟨onlineGeneratedQuarterBoundedRefresh_source_hypotheses.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.1,
    by
      intro x
      simpa [onlineGeneratedQuarterBoundedRefreshData] using
        onlineGeneratedQuarterBoundedRefresh_fixedQuery_genuineGradient_ae x,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_assumption32Genuine _,
    onlineGeneratedQuarterBoundedRefresh_nonconvex_stepsize,
    onlineGeneratedQuarterBoundedRefresh_PL_stepsize,
    onlineGeneratedQuarterBoundedRefresh_genuine_gradient_failure_not_nullMeasurable⟩

/-- Auxiliary state-level diagnostic for the totalized formal process.  It
does not discharge the B-track gate: besides measuring a complete `(x,g)`
state rather than a requested scalar, its estimator uses the zero fallback
where the source sampled gradient does not exist. -/
theorem onlineGeneratedQuarterBoundedRefresh_original_generated_transition_defect :
    HasUniformLowerBound
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem) (-100) ∧
      IsLocallySmooth
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        (fun _ => 1) ∧
      OnlineAssumption33Literal onlineGeneratedQuarterBoundedRefreshData.problem
        (fun _ => 1) ∧
      SatisfiesPL (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineGeneratedQuarterBoundedRefreshMinimizer ∧
      IsUnbiasedQuantizer onlineGeneratedQuarterBoundedRefreshData.quantizer 1 ∧
      OnlineBatchAdmissible onlineGeneratedRefreshBatch
        onlineGeneratedDifferenceBatch ∧
      OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData.problem
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (fun _ => 0) ∧
      ¬ AEMeasurable
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible 2)
        (onlineProofExactPathLaw
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData) := by
  refine ⟨onlineGeneratedQuarterBoundedRefresh_source_hypotheses.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.2.2, ?_⟩
  intro hstate
  let run := onlineProofExactProcess
    (b := onlineGeneratedRefreshBatch)
    (b0 := onlineGeneratedDifferenceBatch)
    onlineGeneratedQuarterBoundedRefreshData
    onlineGeneratedQuarterBoundedRefreshInitialPoint
    onlineGeneratedRefresh_batchAdmissible
  let law := onlineProofExactPathLaw
    (b := onlineGeneratedRefreshBatch)
    (b0 := onlineGeneratedDifferenceBatch)
    onlineGeneratedQuarterBoundedRefreshData
  have hx : AEMeasurable (fun path => (run 2 path).x) law :=
    (measurable_state_x oldInitialBoundCounterexampleDimension).comp_aemeasurable
      hstate
  have hg : AEMeasurable (fun path => (run 2 path).g) law :=
    (measurable_state_g oldInitialBoundCounterexampleDimension).comp_aemeasurable
      hstate
  have hglobal : AEMeasurable
      (fun path => globalGradient
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        (run 2 path).x) law :=
    (measurable_gradient
      (globalObjective
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem))).comp_aemeasurable hx
  have hscalar : AEStronglyMeasurable
      (fun path => ‖(run 2 path).g -
        globalGradient
          (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
          (run 2 path).x‖ ^ 2) law :=
    (hg.sub hglobal).norm.pow_const 2 |>.aestronglyMeasurable
  let roundLaw : Measure OnlineGeneratedRefreshRound :=
    onlineRoundLaw onlineGeneratedQuarterBoundedRefreshData
  let prefixLaw : Measure (Fin 2 → OnlineGeneratedRefreshRound) :=
    Measure.infinitePi (fun _ : Fin 2 => roundLaw)
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure
        (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw w) :=
    onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure
      onlineGeneratedQuarterBoundedRefreshData.quantizer.law :=
    onlineGeneratedQuarterBoundedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedQuarterBoundedRefreshData.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw onlineGeneratedQuarterBoundedRefreshData.refreshProbability
        onlineGeneratedQuarterBoundedRefreshData.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  have hpref : AEStronglyMeasurable
      onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq prefixLaw := by
    apply aestronglyMeasurable_prefix_of_comp roundLaw 2
    simpa [run, law, roundLaw, onlineProofExactPathLaw,
      onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq,
      onlineGeneratedQuarterBoundedRefreshTwoRoundState, onlineProofExactProcess,
      onlineProofExactRun, SOptLib.recursiveIterateProcess] using hscalar
  have hthreshold : NullMeasurableSet
      {pref : Fin 2 → OnlineGeneratedRefreshRound |
        1 < onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq pref} prefixLaw := by
    have h := hpref.aemeasurable.nullMeasurableSet_preimage
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))
    simpa only [Set.preimage_setOf_eq] using h
  have hcoin : ∀ᵐ pref ∂prefixLaw, (pref 1).1 = true := by
    simpa [prefixLaw, roundLaw, onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using
      onlineGeneratedRefreshTimeOneCoin_ae_true
  have hquery : onlineGeneratedQuarterBoundedRefreshTimeTwoQuery =ᵐ[prefixLaw]
      (fun pref => onlineGeneratedRefreshRoundQueryFormula (pref 0)) := by
    simpa [prefixLaw, roundLaw] using
      onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula_ae
  have hevent :
      ({pref : Fin 2 → OnlineGeneratedRefreshRound |
        1 < onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq pref} :
          Set (Fin 2 → OnlineGeneratedRefreshRound)) =ᵐ[prefixLaw]
      {pref : Fin 2 → OnlineGeneratedRefreshRound |
        onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 0).1.val ∨
          onlineGeneratedRefreshRoundQueryFormula (pref 0) =
            ((pref 1).2.1.1 0 1).1.val} := by
    filter_upwards [hcoin, hquery] with pref hc hq
    have hc0 := abs_lt.mp
      (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
        ((pref 0).2.1.1 0 0).2)
    have hc1 := abs_lt.mp
      (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
        ((pref 0).2.1.1 0 1).2)
    have hqFormula : onlineGeneratedRefreshRoundQueryFormula (pref 0) =
        -(10 +
          (onlineGeneratedRefreshCenteredCoordinate ((pref 0).2.1.1 0 0).2 +
            onlineGeneratedRefreshCenteredCoordinate ((pref 0).2.1.1 0 1).2) / 2) :=
      rfl
    have hqLower : -11 < onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref := by
      rw [hq, hqFormula]
      linarith
    have hqUpper : onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref < -9 := by
      rw [hq, hqFormula]
      linarith
    apply propext
    change (1 < onlineGeneratedQuarterBoundedRefreshTimeTwoResidualSq pref) ↔
      (onlineGeneratedRefreshRoundQueryFormula (pref 0) =
          ((pref 1).2.1.1 0 0).1.val ∨
        onlineGeneratedRefreshRoundQueryFormula (pref 0) =
          ((pref 1).2.1.1 0 1).1.val)
    rw [onlineGeneratedQuarterBoundedRefresh_timeTwo_refreshResidual_threshold_preimage
      pref hc hqLower hqUpper, hq]
  have hbad := NullMeasurableSet.congr hthreshold hevent
  exact onlineGeneratedRefresh_union_diagonals_not_nullMeasurable (by
    simpa [prefixLaw, roundLaw, onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using hbad)

/-- Although the complete time-two state is not measurable, its iterate
component is: it is definitionally the measurable atomless query generated by
the first round.  This separates the bad estimator component needed below. -/
theorem onlineGeneratedQuarterBoundedRefresh_iterate_two_aemeasurable :
    AEMeasurable
      (fun path =>
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible 2 path).x)
      (onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData) := by
  let roundLaw : Measure OnlineGeneratedRefreshRound :=
    onlineRoundLaw onlineGeneratedQuarterBoundedRefreshData
  let prefixLaw : Measure (Fin 2 → OnlineGeneratedRefreshRound) :=
    Measure.infinitePi (fun _ : Fin 2 => roundLaw)
  let law := onlineProofExactPathLaw
    (b := onlineGeneratedRefreshBatch)
    (b0 := onlineGeneratedDifferenceBatch)
    onlineGeneratedQuarterBoundedRefreshData
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure
        (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw w) :=
    onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure
      onlineGeneratedQuarterBoundedRefreshData.quantizer.law :=
    onlineGeneratedQuarterBoundedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedQuarterBoundedRefreshData.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw onlineGeneratedQuarterBoundedRefreshData.refreshProbability
        onlineGeneratedQuarterBoundedRefreshData.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  have hqueryRight : Measurable
      (fun pref : Fin 2 → OnlineGeneratedRefreshRound =>
        onlineGeneratedRefreshRoundQueryFormula (pref 0)) :=
    onlineGeneratedRefreshRoundQueryFormula_measurable.comp (measurable_pi_apply 0)
  have hquery : AEMeasurable
      onlineGeneratedQuarterBoundedRefreshTimeTwoQuery prefixLaw := by
    exact hqueryRight.aemeasurable.congr
      (by simpa [prefixLaw, roundLaw] using
        onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula_ae.symm)
  have hxPrefix : AEMeasurable
      (fun pref : Fin 2 → OnlineGeneratedRefreshRound =>
        (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x)
      prefixLaw := by
    have hpoint : Measurable
        (fun q : ℝ => onlineCoarseCounterexamplePoint q) := by
      unfold onlineCoarseCounterexamplePoint
      fun_prop
    have hcomp := hpoint.comp_aemeasurable hquery
    refine hcomp.congr (Filter.Eventually.of_forall ?_)
    intro pref
    simpa [Function.comp_def,
      onlineGeneratedQuarterBoundedRefreshTimeTwoQuery] using
      (onlineCoarseCounterexamplePoint_coordinate
        (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x)
  have hprefix : AEMeasurable
      (onlineRoundPrefix
        (n := onlineCoarseCounterexampleWorkers)
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        (Sample := OnlineGeneratedRefreshSample) (Ξ := Unit) 2)
      law := (measurable_pi_lambda _ fun j => measurable_pi_apply j.1).aemeasurable
  have hmap : Measure.map
      (onlineRoundPrefix
        (n := onlineCoarseCounterexampleWorkers)
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        (Sample := OnlineGeneratedRefreshSample) (Ξ := Unit) 2) law =
      prefixLaw := by
    simpa [law, prefixLaw, roundLaw, onlineProofExactPathLaw,
      onlineRoundPrefix] using iidStream_prefix_map_eq_infinitePi roundLaw 2
  rw [← hmap] at hxPrefix
  have hpull := hxPrefix.comp_aemeasurable hprefix
  simpa [law, onlineRoundPrefix,
    onlineGeneratedQuarterBoundedRefreshTwoRoundState,
    onlineProofExactProcess, onlineProofExactRun,
    SOptLib.recursiveIterateProcess] using hpull

/-- The state-level obstruction is located in the generated estimator, not in
the time-two iterate. -/
theorem onlineGeneratedQuarterBoundedRefresh_estimator_two_not_aemeasurable :
    ¬ AEMeasurable
      (fun path =>
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible 2 path).g)
      (onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData) := by
  intro hg
  rcases onlineGeneratedQuarterBoundedRefresh_original_generated_transition_defect with
    ⟨_, _, _, _, _, _, _, hstateBad⟩
  apply hstateBad
  have hx := onlineGeneratedQuarterBoundedRefresh_iterate_two_aemeasurable
  exact (measurable_state_mk oldInitialBoundCounterexampleDimension).comp_aemeasurable
    (hx.prodMk hg)

/-- At horizon three the bad time-two estimator is used by the literal
Algorithm 3 primal update, so the requested last iterate itself is not
a.e.-measurable. -/
theorem onlineGeneratedQuarterBoundedRefresh_iterate_three_not_aemeasurable :
    ¬ AEMeasurable
      (fun path =>
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible 3 path).x)
      (onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData) := by
  intro hx3
  apply onlineGeneratedQuarterBoundedRefresh_estimator_two_not_aemeasurable
  have hx2 := onlineGeneratedQuarterBoundedRefresh_iterate_two_aemeasurable
  refine (hx2.sub hx3).congr (Filter.Eventually.of_forall ?_)
  intro path
  change
    (onlineProofExactProcess onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint
        onlineGeneratedRefresh_batchAdmissible 2 path).x -
      (onlineProofExactProcess onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint
        onlineGeneratedRefresh_batchAdmissible 3 path).x =
      (onlineProofExactProcess onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint
        onlineGeneratedRefresh_batchAdmissible 2 path).g
  simp [onlineProofExactProcess, onlineProofExactRun,
    SOptLib.recursiveIterateProcess, onlineStep, primalStep,
    onlineGeneratedQuarterBoundedRefreshData]

/-- The existing atomless-diagonal example does **not** satisfy the
source-faithful conditional-kernel formulation of Assumption 3.2.  That
contract makes every generated conditioning pair a random variable, whereas
the example's time-three iterate is not even a.e. measurable.  Consequently
its fixed-path `OnlineAssumption32Genuine` witness cannot certify all original
source hypotheses and the example is only an auxiliary-route obstruction. -/
theorem
    onlineGeneratedQuarterBoundedRefresh_not_assumption32GeneratedConditionalKernel :
    ¬ OnlineAssumption32GeneratedConditionalKernel
      (b0 := onlineGeneratedDifferenceBatch)
      onlineGeneratedQuarterBoundedRefreshData.problem
      (onlineProofExactProcess
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData
        onlineGeneratedQuarterBoundedRefreshInitialPoint
        onlineGeneratedRefresh_batchAdmissible)
      (onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData)
      (fun _ ↦ 0) := by
  intro hKernel
  apply onlineGeneratedQuarterBoundedRefresh_iterate_three_not_aemeasurable
  have hPair := (hKernel.2.1 3).aemeasurable
  exact measurable_fst.comp_aemeasurable hPair

noncomputable def onlineGeneratedQuarterBoundedRefreshTimeThreeIterate
    (pref : Fin 2 → OnlineGeneratedRefreshRound) :
    Point oldInitialBoundCounterexampleDimension :=
  primalStep onlineGeneratedQuarterBoundedRefreshData.stepSize
    (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref)

/-- On the full-measure canonical refresh event, the time-three iterate lies
strictly to the right of the minimizer `-20`.  Hence the quadratic objective
is injective on the generated range. -/
theorem onlineGeneratedQuarterBoundedRefresh_timeThree_above_minimizer
    (pref : Fin 2 → OnlineGeneratedRefreshRound)
    (hrefresh0 : (pref 0).1 = true)
    (hrefresh1 : (pref 1).1 = true)
    (hcoarse0 : ((pref 0).2.1.1 0 0).1.val ≠ 0)
    (hcoarse1 : ((pref 0).2.1.1 0 1).1.val ≠ 0) :
    -20 < onlineGeneratedQuarterBoundedRefreshTimeThreeIterate pref 0 := by
  let state := onlineGeneratedQuarterBoundedRefreshTwoRoundState pref
  let q := onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref
  have hqFormula : q = -(10 +
      (onlineGeneratedRefreshCenteredCoordinate ((pref 0).2.1.1 0 0).2 +
        onlineGeneratedRefreshCenteredCoordinate ((pref 0).2.1.1 0 1).2) / 2) :=
    onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula pref hrefresh0
      hcoarse0 hcoarse1
  have hc00 := abs_lt.mp
    (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
      ((pref 0).2.1.1 0 0).2)
  have hc01 := abs_lt.mp
    (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
      ((pref 0).2.1.1 0 1).2)
  have hqLower : -11 < q := by
    change -11 < q
    rw [hqFormula]
    linarith
  have hqUpper : q < -9 := by
    change q < -9
    rw [hqFormula]
    linarith
  have hx : state.x = onlineCoarseCounterexamplePoint q := by
    ext i
    fin_cases i
    simp [state, q, onlineGeneratedQuarterBoundedRefreshTimeTwoQuery,
      onlineCoarseCounterexamplePoint, oldInitialBoundCounterexampleDirection]
  let term := fun j : Fin 2 =>
    if q = ((pref 1).2.1.1 0 j).1.val then 0
    else onlineGeneratedRefreshSlope ((pref 1).2.1.1 0 j) + q / 2
  have hterm (j : Fin 2) :
      (stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
        ((pref 1).2.1.1 0 j) state.x) 0 = term j := by
    rw [hx]
    change (gradient
      (onlineGeneratedQuarterBoundedRefreshLoss ((pref 1).2.1.1 0 j))
      (onlineCoarseCounterexamplePoint q)) 0 = _
    rw [onlineGeneratedQuarterBoundedRefreshLoss_gradient_at_query]
    dsimp [term]
    split_ifs with h
    · rfl
    · simp [onlineCoarseCounterexamplePoint,
        oldInitialBoundCounterexampleDirection]
      ring
  have htermBounds (j : Fin 2) : 0 ≤ term j ∧ term j < 7 := by
    have hc := abs_lt.mp
      (onlineGeneratedRefreshCenteredCoordinate_abs_lt_one
        ((pref 1).2.1.1 0 j).2)
    dsimp [term]
    split_ifs
    · constructor <;> norm_num
    · change 0 ≤ 10 +
          onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 j).2 +
          q / 2 ∧
        10 + onlineGeneratedRefreshCenteredCoordinate ((pref 1).2.1.1 0 j).2 +
          q / 2 < 7
      constructor <;> linarith
  have hg : state.g 0 = (term 0 + term 1) / 2 := by
    have hstateG : state.g = average
        (fun _ : Worker onlineCoarseCounterexampleWorkers =>
          average (fun j : Fin onlineGeneratedRefreshBatch.1 =>
            stochasticGradient onlineGeneratedQuarterBoundedRefreshProblem 0
              ((pref 1).2.1.1 0 j) state.x)) := by
      dsimp [state, onlineGeneratedQuarterBoundedRefreshTwoRoundState]
      simp only [onlineStep, onlineDriverOfRoundNoise, hrefresh1]
      rfl
    rw [hstateG]
    unfold average SOptLib.finiteUniformAverage
    rw [Fin.sum_univ_one, Fin.sum_univ_two]
    norm_num [onlineCoarseCounterexampleWorkers, onlineGeneratedRefreshBatch]
    rw [hterm 0, hterm 1]
    ring
  have hgLower : 0 ≤ state.g 0 := by
    rw [hg]
    linarith [htermBounds 0 |>.1, htermBounds 1 |>.1]
  have hgUpper : state.g 0 < 7 := by
    rw [hg]
    linarith [htermBounds 0 |>.2, htermBounds 1 |>.2]
  unfold onlineGeneratedQuarterBoundedRefreshTimeThreeIterate primalStep
  change -20 < state.x 0 -
    (onlineGeneratedQuarterBoundedRefreshData.stepSize : ℝ) * state.g 0
  rw [hx]
  norm_num [onlineCoarseCounterexamplePoint,
    oldInitialBoundCounterexampleDirection,
    onlineGeneratedQuarterBoundedRefreshData]
  linarith

theorem onlineGeneratedQuarterBoundedRefresh_timeThree_above_minimizer_ae :
    ∀ᵐ path ∂onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData,
      -20 <
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible 3 path).x 0 := by
  let roundLaw : Measure OnlineGeneratedRefreshRound :=
    onlineRoundLaw onlineGeneratedQuarterBoundedRefreshData
  let prefixLaw : Measure (Fin 2 → OnlineGeneratedRefreshRound) :=
    Measure.infinitePi (fun _ : Fin 2 => roundLaw)
  let law := onlineProofExactPathLaw
    (b := onlineGeneratedRefreshBatch)
    (b0 := onlineGeneratedDifferenceBatch)
    onlineGeneratedQuarterBoundedRefreshData
  let prefixMap := onlineRoundPrefix
    (n := onlineCoarseCounterexampleWorkers)
    (b := onlineGeneratedRefreshBatch)
    (b0 := onlineGeneratedDifferenceBatch)
    (Sample := OnlineGeneratedRefreshSample) (Ξ := Unit) 2
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure
        (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw w) :=
    onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure
      onlineGeneratedQuarterBoundedRefreshData.quantizer.law :=
    onlineGeneratedQuarterBoundedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedQuarterBoundedRefreshData.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw onlineGeneratedQuarterBoundedRefreshData.refreshProbability
        onlineGeneratedQuarterBoundedRefreshData.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  have hcoin0 : ∀ᵐ pref ∂prefixLaw, (pref 0).1 = true := by
    simpa [prefixLaw, roundLaw, onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using
      onlineGeneratedRefreshTimeZeroCoin_ae_true
  have hcoin1 : ∀ᵐ pref ∂prefixLaw, (pref 1).1 = true := by
    simpa [prefixLaw, roundLaw, onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using
      onlineGeneratedRefreshTimeOneCoin_ae_true
  have hsample (j : Fin 2) :
      ∀ᵐ pref ∂prefixLaw, ((pref 0).2.1.1 0 j).1.val ≠ 0 := by
    simpa [prefixLaw, roundLaw, onlineGeneratedQuarterBoundedRefreshData,
      onlineGeneratedQuarterBoundedRefreshProblem] using
      (show ∀ᵐ pref ∂Measure.infinitePi (fun _ : Fin 2 =>
          onlineRoundLaw (b := onlineGeneratedRefreshBatch)
            (b0 := onlineGeneratedDifferenceBatch)
            onlineGeneratedRefreshData),
        ((pref 0).2.1.1 0 j).1.val ≠ 0 from by
          have hqmp : Measure.QuasiMeasurePreserving
              (fun pref : Fin 2 → OnlineGeneratedRefreshRound =>
                (pref 0).2.1.1 0 j)
              (Measure.infinitePi (fun _ : Fin 2 =>
                onlineRoundLaw (b := onlineGeneratedRefreshBatch)
                  (b0 := onlineGeneratedDifferenceBatch)
                  onlineGeneratedRefreshData))
              (onlineGeneratedRefreshProblem.sampleLaw 0) :=
            ⟨by fun_prop, by rw [onlineGeneratedRefreshTimeZeroSample_marginal j]⟩
          exact hqmp.tendsto_ae
            onlineGeneratedRefreshSample_coarse_ne_zero_ae)
  have hpref : ∀ᵐ pref ∂prefixLaw,
      -20 < onlineGeneratedQuarterBoundedRefreshTimeThreeIterate pref 0 := by
    filter_upwards [hcoin0, hcoin1, hsample 0, hsample 1]
      with pref hc0 hc1 hs0 hs1
    exact onlineGeneratedQuarterBoundedRefresh_timeThree_above_minimizer
      pref hc0 hc1 hs0 hs1
  have hprefixMeas : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hmap : Measure.map prefixMap law = prefixLaw := by
    simpa [prefixMap, law, prefixLaw, roundLaw, onlineProofExactPathLaw,
      onlineRoundPrefix] using iidStream_prefix_map_eq_infinitePi roundLaw 2
  have hpull :=
    (show Measure.QuasiMeasurePreserving prefixMap law prefixLaw from
      ⟨hprefixMeas, by rw [hmap]⟩).tendsto_ae hpref
  simpa [prefixMap, law, onlineRoundPrefix,
    onlineGeneratedQuarterBoundedRefreshTimeThreeIterate,
    onlineGeneratedQuarterBoundedRefreshTwoRoundState,
    onlineProofExactProcess, onlineProofExactRun, onlineStep, primalStep,
    SOptLib.recursiveIterateProcess] using hpull

theorem onlineGeneratedQuarterBoundedRefresh_objective_gap_coordinate
    (x : Point oldInitialBoundCounterexampleDimension) :
    globalObjective (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem) x -
        globalObjective (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshProblem)
          onlineGeneratedQuarterBoundedRefreshMinimizer =
      (x 0 + 20) ^ 2 / 4 := by
  rw [onlineGeneratedQuarterBoundedRefresh_objective_minimizer,
    onlineGeneratedQuarterBoundedRefresh_globalObjective]
  have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  rw [show (innerSL ℝ oldInitialBoundCounterexampleDirection) x = x 0 by
    change inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = x 0
    simp only [PiLp.inner_apply]
    rw [Fin.sum_univ_one, real_inner_eq_re_inner ℝ, RCLike.inner_apply]
    simp]
  ring

/-- Exact D.4 observable obstruction: the last-iterate objective gap at
`K = 3` is not a.e.-measurable under the canonical proof-exact path law. -/
theorem onlineGeneratedQuarterBoundedRefresh_D4_objective_gap_not_aemeasurable :
    ¬ AEMeasurable
      (fun path =>
        globalObjective
            (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
            (onlineProofExactProcess
              (b := onlineGeneratedRefreshBatch)
              (b0 := onlineGeneratedDifferenceBatch)
              onlineGeneratedQuarterBoundedRefreshData
              onlineGeneratedQuarterBoundedRefreshInitialPoint
              onlineGeneratedRefresh_batchAdmissible 3 path).x -
          globalObjective
            (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
            onlineGeneratedQuarterBoundedRefreshMinimizer)
      (onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData) := by
  intro hgap
  apply onlineGeneratedQuarterBoundedRefresh_iterate_three_not_aemeasurable
  let run := onlineProofExactProcess
    (b := onlineGeneratedRefreshBatch)
    (b0 := onlineGeneratedDifferenceBatch)
    onlineGeneratedQuarterBoundedRefreshData
    onlineGeneratedQuarterBoundedRefreshInitialPoint
    onlineGeneratedRefresh_batchAdmissible
  let P := onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem
  let gap := fun path => globalObjective P (run 3 path).x -
    globalObjective P onlineGeneratedQuarterBoundedRefreshMinimizer
  have hinverse : Measurable (fun y : ℝ => -20 + 2 * Real.sqrt y) := by
    fun_prop
  have hpoint : Measurable
      (fun q : ℝ => onlineCoarseCounterexamplePoint q) := by
    unfold onlineCoarseCounterexamplePoint
    fun_prop
  have hrecovered : AEMeasurable
      (fun path => onlineCoarseCounterexamplePoint
        (-20 + 2 * Real.sqrt (gap path)))
      (onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData) :=
    hpoint.comp_aemeasurable
      (hinverse.comp_aemeasurable (by simpa [gap, P, run] using hgap))
  refine hrecovered.congr ?_
  filter_upwards
    [onlineGeneratedQuarterBoundedRefresh_timeThree_above_minimizer_ae]
    with path habove
  rw [← onlineCoarseCounterexamplePoint_coordinate (run 3 path).x]
  congr 1
  have hgapFormula : gap path = ((run 3 path).x 0 + 20) ^ 2 / 4 := by
    simpa [gap, P, onlineGeneratedQuarterBoundedRefreshData] using
      onlineGeneratedQuarterBoundedRefresh_objective_gap_coordinate (run 3 path).x
  rw [hgapFormula]
  have hhalf : 0 < ((run 3 path).x 0 + 20) / 2 := by
    linarith
  rw [show ((run 3 path).x 0 + 20) ^ 2 / 4 =
      (((run 3 path).x 0 + 20) / 2) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_pos hhalf]
  ring

theorem onlineGeneratedQuarterBoundedRefresh_D4_objective_gap_not_integrable :
    ¬ Integrable
      (fun path =>
        globalObjective
            (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
            (onlineProofExactProcess
              (b := onlineGeneratedRefreshBatch)
              (b0 := onlineGeneratedDifferenceBatch)
              onlineGeneratedQuarterBoundedRefreshData
              onlineGeneratedQuarterBoundedRefreshInitialPoint
              onlineGeneratedRefresh_batchAdmissible 3 path).x -
          globalObjective
            (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
            onlineGeneratedQuarterBoundedRefreshMinimizer)
      (onlineProofExactPathLaw
        (b := onlineGeneratedRefreshBatch)
        (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData) := by
  intro h
  exact onlineGeneratedQuarterBoundedRefresh_D4_objective_gap_not_aemeasurable
    h.aestronglyMeasurable.aemeasurable

/-- Compatibility name for the auxiliary totalized-gradient D.4 diagnostic.
Its scalar and nonintegrability conclusion are valid for
`onlineProofExactProcess`, but that formal process assigns zero on precisely
the nondifferentiable diagonal.  Therefore this theorem is not, by itself, a
source-statement defect and must not be used to justify a B-track correction.
The genuine-transition theorem identifies undefined calls before
totalization, but the conditional-kernel audit below proves that it does not
satisfy every original Assumption 3.2 hypothesis either. -/
theorem onlineGeneratedQuarterBoundedRefresh_original_D4_requested_expectation_defect :
    HasUniformLowerBound
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem) (-100) ∧
      IsLocallySmooth
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        (fun _ => 1) ∧
      OnlineAssumption33Literal onlineGeneratedQuarterBoundedRefreshData.problem
        (fun _ => 1) ∧
      SatisfiesPL
        (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
        ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineGeneratedQuarterBoundedRefreshMinimizer ∧
      IsUnbiasedQuantizer onlineGeneratedQuarterBoundedRefreshData.quantizer 1 ∧
      OnlineBatchAdmissible onlineGeneratedRefreshBatch
        onlineGeneratedDifferenceBatch ∧
      OnlineAverageSmoothness (b0 := onlineGeneratedDifferenceBatch)
        onlineGeneratedQuarterBoundedRefreshData.problem
        (onlineProofExactProcess
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData
          onlineGeneratedQuarterBoundedRefreshInitialPoint
          onlineGeneratedRefresh_batchAdmissible)
        (fun _ => 0) ∧
      OnlineVRStepsizeCondition
        onlineGeneratedQuarterBoundedRefreshData.stepSize
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 1))
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 0))
        onlineGeneratedQuarterBoundedRefreshData.refreshProbability 1
        onlineCoarseCounterexampleWorkers onlineGeneratedDifferenceBatch ∧
      OnlineVRPLStepsizeCondition
        onlineGeneratedQuarterBoundedRefreshData.stepSize
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 1))
        (rootMeanSquare (fun _ : Worker onlineCoarseCounterexampleWorkers => 0))
        onlineGeneratedQuarterBoundedRefreshData.refreshProbability 1
        ⟨(2 : ℝ)⁻¹, by positivity⟩ onlineCoarseCounterexampleWorkers
        onlineGeneratedDifferenceBatch ∧
      ¬ Integrable
        (fun path =>
          globalObjective
              (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
              (onlineProofExactProcess
                (b := onlineGeneratedRefreshBatch)
                (b0 := onlineGeneratedDifferenceBatch)
                onlineGeneratedQuarterBoundedRefreshData
                onlineGeneratedQuarterBoundedRefreshInitialPoint
                onlineGeneratedRefresh_batchAdmissible 3 path).x -
            globalObjective
              (onlineLocalProblem onlineGeneratedQuarterBoundedRefreshData.problem)
              onlineGeneratedQuarterBoundedRefreshMinimizer)
        (onlineProofExactPathLaw
          (b := onlineGeneratedRefreshBatch)
          (b0 := onlineGeneratedDifferenceBatch)
          onlineGeneratedQuarterBoundedRefreshData) := by
  exact ⟨onlineGeneratedQuarterBoundedRefresh_source_hypotheses.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.2.1,
    onlineGeneratedQuarterBoundedRefresh_source_hypotheses.2.2.2.2.2.2,
    onlineGeneratedQuarterBoundedRefresh_nonconvex_stepsize,
    onlineGeneratedQuarterBoundedRefresh_PL_stepsize,
    onlineGeneratedQuarterBoundedRefresh_D4_objective_gap_not_integrable⟩

/-! ## Conditional adaptive-law development (source gate still open) -/

/-- The atomless-diagonal obstruction excludes the weaker law-level
regularity predicate.  Applied to the law of the measurable first-round query
and either coordinate of the independent second-round refresh batch, the
correction makes both genuine sampled gradients exist almost everywhere.
Pulling those two product-law facts back to the canonical two-round prefix
would make the certified failure domain null-measurable, contradicting
`onlineGeneratedQuarterBoundedRefresh_genuine_gradient_failure_not_nullMeasurable`.

This proves that the predicate excludes the auxiliary example; because the
example fails `OnlineAssumption32GeneratedConditionalKernel`, it does not by
itself justify adding that predicate at the source release boundary. -/
theorem
    onlineGeneratedQuarterBoundedRefresh_not_adaptiveSampleGradientLawRegularity :
    ¬ OnlineAdaptiveSampleGradientLawRegularity
      onlineGeneratedQuarterBoundedRefreshData.problem := by
  intro hRegularity
  let roundLaw : Measure OnlineGeneratedRefreshRound :=
    onlineRoundLaw (b := onlineGeneratedRefreshBatch)
      (b0 := onlineGeneratedDifferenceBatch)
      onlineGeneratedQuarterBoundedRefreshData
  let prefixLaw : Measure (Fin 2 → OnlineGeneratedRefreshRound) :=
    Measure.infinitePi (fun _ : Fin 2 ↦ roundLaw)
  let query : OnlineGeneratedRefreshRound →
      Point oldInitialBoundCounterexampleDimension :=
    fun r ↦ onlineCoarseCounterexamplePoint
      (onlineGeneratedRefreshRoundQueryFormula r)
  letI (w : Worker onlineCoarseCounterexampleWorkers) :
      IsProbabilityMeasure
        (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw w) :=
    onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedRefreshBatch) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
        onlineGeneratedDifferenceBatch) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure
      onlineGeneratedQuarterBoundedRefreshData.quantizer.law :=
    onlineGeneratedQuarterBoundedRefreshData.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := onlineCoarseCounterexampleWorkers)
        onlineGeneratedQuarterBoundedRefreshData.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw onlineGeneratedQuarterBoundedRefreshData.refreshProbability
        onlineGeneratedQuarterBoundedRefreshData.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold onlineRoundLaw
    infer_instance
  have hqueryMeas : Measurable query := by
    dsimp [query]
    have hpoint : Measurable
        (fun q : ℝ ↦ onlineCoarseCounterexamplePoint q) := by
      unfold onlineCoarseCounterexamplePoint
      fun_prop
    exact hpoint.comp onlineGeneratedRefreshRoundQueryFormula_measurable
  have hsampleLaw (j : Fin onlineGeneratedRefreshBatch.1) :
      Measure.map
          (fun r : OnlineGeneratedRefreshRound ↦ r.2.1.1 0 j) roundLaw =
        onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0 := by
    calc
      Measure.map
          (fun r : OnlineGeneratedRefreshRound ↦ r.2.1.1 0 j) roundLaw =
          Measure.map (fun batch ↦ batch 0 j)
            (Measure.map (fun r : OnlineGeneratedRefreshRound ↦ r.2.1.1)
              roundLaw) := by
                rw [Measure.map_map]
                · rfl
                all_goals fun_prop
      _ = Measure.map (fun batch ↦ batch 0 j)
          (onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
            onlineGeneratedRefreshBatch) := by
            rw [show Measure.map
                (fun r : OnlineGeneratedRefreshRound ↦ r.2.1.1) roundLaw =
                onlineBatchLaw onlineGeneratedQuarterBoundedRefreshData.problem
                  onlineGeneratedRefreshBatch by
              simpa [roundLaw] using
                (onlineRoundLaw_refreshBatch_marginal
                  (b := onlineGeneratedRefreshBatch)
                  (b0 := onlineGeneratedDifferenceBatch)
                  onlineGeneratedQuarterBoundedRefreshData)]
      _ = onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0 :=
        onlineBatchLaw_coordinate_marginal
          onlineGeneratedQuarterBoundedRefreshData.problem 0 j
  have hpairLaw :
      Measure.map
          (fun pref : Fin 2 → OnlineGeneratedRefreshRound ↦
            (pref 0, pref 1)) prefixLaw =
        roundLaw.prod roundLaw := by
    have hcoords : ProbabilityTheory.iIndepFun
        (fun i (pref : Fin 2 → OnlineGeneratedRefreshRound) ↦ pref i)
        prefixLaw := by
      dsimp [prefixLaw]
      exact ProbabilityTheory.iIndepFun_infinitePi
        (fun _ : Fin 2 ↦ measurable_id)
    have hindep : ProbabilityTheory.IndepFun
        (fun pref : Fin 2 → OnlineGeneratedRefreshRound ↦ pref 0)
        (fun pref : Fin 2 → OnlineGeneratedRefreshRound ↦ pref 1)
        prefixLaw := hcoords.indepFun (by decide)
    have hmap :=
      (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        (measurable_pi_apply (0 : Fin 2)).aemeasurable
        (measurable_pi_apply (1 : Fin 2)).aemeasurable).mp hindep
    have hmarg (j : Fin 2) :
        Measure.map (fun pref : Fin 2 → OnlineGeneratedRefreshRound ↦ pref j)
            prefixLaw = roundLaw := by
      dsimp [prefixLaw]
      simpa using (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin 2 ↦ roundLaw) j)
    rw [hmarg (0 : Fin 2), hmarg (1 : Fin 2)] at hmap
    exact hmap
  have hpairQMP : Measure.QuasiMeasurePreserving
      (fun pref : Fin 2 → OnlineGeneratedRefreshRound ↦ (pref 0, pref 1))
      prefixLaw (roundLaw.prod roundLaw) :=
    ⟨(measurable_pi_apply (0 : Fin 2)).prodMk
        (measurable_pi_apply (1 : Fin 2)), by rw [hpairLaw]⟩
  have hgoodProduct (j : Fin onlineGeneratedRefreshBatch.1) :
      ∀ᵐ p ∂roundLaw.prod roundLaw,
        DifferentiableAt ℝ
          (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
            (p.2.2.1.1 0 j))
          (query p.1) :=
    (stochasticGradient_randomQuery_product_regular_of_lawRegularity
      onlineGeneratedQuarterBoundedRefreshData.problem hRegularity 0
      roundLaw roundLaw query
      (fun r : OnlineGeneratedRefreshRound ↦ r.2.1.1 0 j)
      hqueryMeas.aestronglyMeasurable (by fun_prop) (hsampleLaw j)).1
  have hgoodPrefix (j : Fin onlineGeneratedRefreshBatch.1) :
      ∀ᵐ pref ∂prefixLaw,
        DifferentiableAt ℝ
          (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
            ((pref 1).2.1.1 0 j))
          (query (pref 0)) := by
    simpa using hpairQMP.tendsto_ae (hgoodProduct j)
  have hqueryAE : onlineGeneratedQuarterBoundedRefreshTimeTwoQuery =ᵐ[prefixLaw]
      (fun pref ↦ onlineGeneratedRefreshRoundQueryFormula (pref 0)) := by
    simpa [prefixLaw, roundLaw] using
      onlineGeneratedQuarterBoundedRefresh_timeTwo_query_formula_ae
  have hgoodGenerated (j : Fin onlineGeneratedRefreshBatch.1) :
      ∀ᵐ pref ∂prefixLaw,
        DifferentiableAt ℝ
          (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
            ((pref 1).2.1.1 0 j))
          (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x := by
    filter_upwards [hgoodPrefix j, hqueryAE] with pref hgood hquery
    have hx : (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x =
        onlineCoarseCounterexamplePoint
          (onlineGeneratedQuarterBoundedRefreshTimeTwoQuery pref) :=
      (onlineCoarseCounterexamplePoint_coordinate
        (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x).symm
    rw [hx, hquery]
    exact hgood
  have hnotFailure : ∀ᵐ pref ∂prefixLaw,
      ¬ (¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 0))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x ∨
          ¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 1))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x) := by
    filter_upwards [hgoodGenerated 0, hgoodGenerated 1]
      with pref h0 h1
    exact not_or_intro (not_not_intro h0) (not_not_intro h1)
  have hfailureNull : NullMeasurableSet
      {pref : Fin 2 → OnlineGeneratedRefreshRound |
        ¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 0))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x ∨
          ¬ DifferentiableAt ℝ
            (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0
              ((pref 1).2.1.1 0 1))
            (onlineGeneratedQuarterBoundedRefreshTwoRoundState pref).x}
      prefixLaw := by
    apply NullMeasurableSet.of_null
    simpa only [not_not] using (ae_iff.mp hnotFailure)
  exact onlineGeneratedQuarterBoundedRefresh_genuine_gradient_failure_not_nullMeasurable
    (by simpa [prefixLaw, roundLaw] using hfailureNull)

/-- The original generated-query obstruction is excluded by the explicit
Track-B correction: every sample loss in its law fails differentiability at
its own sample-selected query, so there cannot be a law-full set on which the
sample losses are differentiable at every query. -/
theorem
    onlineGeneratedQuarterBoundedRefresh_not_adaptiveSampleGradientRegularity :
    ¬ OnlineAdaptiveSampleGradientRegularity
      onlineGeneratedQuarterBoundedRefreshData.problem := by
  intro hRegularity
  have hDiff : OnlineSampleLossDifferentiable
      onlineGeneratedQuarterBoundedRefreshData.problem :=
    (onlineAdaptiveSampleGradientRegularity_iff _).mp hRegularity
  have hAlmost : ∀ᵐ s ∂onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0,
      Differentiable ℝ
        (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0 s) :=
    hDiff 0
  have hFalse : ∀ᵐ s ∂onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0,
      False := hAlmost.mono (by
    intro s hs
    have hAt : DifferentiableAt ℝ
        (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLoss 0 s)
        (onlineCoarseCounterexamplePoint s.1.val) :=
      hs (onlineCoarseCounterexamplePoint s.1.val)
    exact (onlineGeneratedQuarterBoundedRefreshLoss_differentiableAt_iff
      s s.1.val).mp hAt rfl)
  have hzero :
      onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0 = 0 := by
    simpa using hFalse
  letI : IsProbabilityMeasure
      (onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0) :=
    onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw_isProbability 0
  have hmass :
      onlineGeneratedQuarterBoundedRefreshData.problem.sampleLaw 0 Set.univ = 1 :=
    measure_univ
  rw [hzero] at hmass
  simp at hmass

/-- Eq. (46) at the corrected proof-exact source boundary.  This packages
the simultaneous component/history induction without reintroducing the
legacy global sample-loss differentiability premise. -/
theorem online_estimator_recurrence_46_proof_exact_of_literal_and_lawRegularity_boundary
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
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
  rcases
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularity
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          hAssumption32 hRegularity k with
    ⟨_hxk, _hresidualk, _hxL2k, _hgL2k, hErrorK, hStepK, _hHistoryK⟩
  rcases
      onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularity
        A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
          hAssumption32 hRegularity (k + 1) with
    ⟨_hxNext, _hresidualNext, _hxL2Next, _hgL2Next, hErrorNext,
      _hStepNext, hHistoryNext⟩
  exact ⟨hErrorNext, hErrorK, hStepK,
    hHistoryNext k (Nat.lt_succ_self k)⟩

/-- Theorem D.3 at the public source boundary.  Literal Assumption 3.3 and
the Track-B adaptive sampled-gradient correction are separate premises.  The
conclusion is the existing proof-exact uniform output under the product of
`onlineProofExactPathLaw` and the independent uniform `Fin K` law. -/
theorem onlineProofExactD3_of_scalar_recurrence_components
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hComponents : ∀ k,
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
            A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1))
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
    have hrec :=
      (hComponents (k + 1)).2.2.2.2.2.2 k (Nat.lt_succ_self k)
    dsimp [E, D, a, V, P, run, law, p, L]
    convert hrec using 1
    all_goals ring
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


set_option linter.unusedVariables false in
/-- Theorem D.4 at the same corrected public source boundary.  Its measured
object is the last proof-exact iterate under `onlineProofExactPathLaw`; no
executable initialization or unrelated scalar process is substituted. -/
theorem onlineProofExactD4_of_scalar_recurrence_components
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hComponents : ∀ k,
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
            A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1))
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
    have hrec :=
      (hComponents (k + 1)).2.2.2.2.2.2 k (Nat.lt_succ_self k)
    dsimp [E, D, a, V, P, run, law, p, L]
    convert hrec using 1
    all_goals ring
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
    convert hTerminal using 1
    all_goals field_simp [hn_ne, hb_ne, hμ_ne, hp_ne]

/-! ## Executable homogeneous initialization at the literal moment boundary

The worker-dependent initializer developed for Remark D.2 specializes
definitionally to the homogeneous Algorithm 3 initializer when every worker
uses the same batch size.  These wrappers expose that specialization without
reconstructing the stronger global sampled-loss differentiability premise. -/

/-- The executable homogeneous Algorithm 3 initializer obeys the usual
`sigma^2 / (n b)` bound from literal fixed-query Assumption 3.3.  The only
differentiability used here is that of the averaged local objectives, supplied
by source Assumption 1.2; no sample-loss regularity is bundled into the moment
premise. -/
theorem expectedOnlineInitialEstimatorErrorSq_le_of_literal
    {d n b : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    expectedOnlineInitialEstimatorErrorSq (b := b) A x0 ≤
      varianceAggregateSq σ / (n.1 * b.1) := by
  have h := expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
    (b := fun _ : Worker n ↦ b) A x0 σ hLiteral hDiff
  change expectedHeterogeneousOnlineInitialEstimatorErrorSq
      (b := fun _ : Worker n ↦ b) A x0 ≤
    varianceAggregateSq σ / (n.1 * b.1)
  calc
    expectedHeterogeneousOnlineInitialEstimatorErrorSq
        (b := fun _ : Worker n ↦ b) A x0 ≤
      heterogeneousOnlineVarianceTerm σ (fun _ : Worker n ↦ b) := h
    _ = varianceAggregateSq σ / (n.1 * b.1) := by
      unfold heterogeneousOnlineVarianceTerm varianceAggregateSq meanSquare
        average SOptLib.finiteUniformAverage
      have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
      have hb : (b.1 : ℝ) ≠ 0 := by exact_mod_cast b.2.ne'
      simp only [Fintype.card_fin, smul_eq_mul]
      field_simp [hn, hb]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hb]

/-- Time zero of the executable homogeneous process is a genuine integrable
estimator-error random variable and satisfies the literal Assumption 3.3
initialization bound.  This is the base case needed by the weak-correction
executable recurrence. -/
theorem online_executable_initial_error_moment_le_of_literal
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i))
    (hBatch : OnlineBatchAdmissible b b0) :
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) 0 ∧
      estimatorErrorMoment (onlineLocalProblem A.problem)
          (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
          (onlinePathLaw (b := b) (b0 := b0) A) 0 ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  let batchLaw := onlineBatchLaw A.problem b
  let streamLaw := SOptLib.iidStreamLaw
    (onlineRoundLaw (b := b) (b0 := b0) A)
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let initError := fun batch : (i : Worker n) → Fin b.1 → Sample i ↦
    onlineInitialEstimatorErrorSq A x0 { sample := batch }
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
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
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    dsimp [streamLaw]
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law, onlinePathLaw]
    infer_instance
  have hInitInt : Integrable initError batchLaw := by
    have h := heterogeneousOnlineInitialEstimatorErrorSq_integrable_of_literal
      (b := fun _ : Worker n ↦ b) A x0 σ hLiteral hDiff
    simpa [initError, batchLaw, onlineInitialEstimatorErrorSq,
      onlineInitialState, onlinePrintedInitialEstimatorAt,
      heterogeneousOnlineInitialEstimatorErrorSq,
      heterogeneousOnlineInitialEstimator, heterogeneousOnlineBatchLaw,
      onlineBatchLaw] using h
  have hLiftInt : Integrable (fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ initError path.1) law := by
    dsimp [law, onlinePathLaw]
    exact hInitInt.comp_fst streamLaw
  have hMomentEq : estimatorErrorMoment (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) law 0 =
        expectedOnlineInitialEstimatorErrorSq (b := b) A x0 := by
    let projection := fun path :
        ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ path.1
    have hfstLaw : Measure.map projection law = batchLaw := by
      dsimp [projection, law, batchLaw, onlinePathLaw]
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    have hMappedMeas : AEStronglyMeasurable initError
        (Measure.map projection law) := by
      rw [hfstLaw]
      exact hInitInt.aestronglyMeasurable
    have hmapIntegral := MeasureTheory.integral_map
      (μ := law) (φ := projection) measurable_fst.aemeasurable hMappedMeas
    rw [hfstLaw] at hmapIntegral
    have hleft : estimatorErrorMoment (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch) law 0 =
          ∫ path, initError path.1 ∂law := by
      unfold estimatorErrorMoment
      apply integral_congr_ae
      filter_upwards [] with path
      rfl
    rw [hleft, hmapIntegral.symm]
    rfl
  constructor
  · simpa [EstimatorErrorMomentWellDefined, initError, law,
      onlineInitialEstimatorErrorSq] using hLiftInt
  · rw [hMomentEq]
    exact expectedOnlineInitialEstimatorErrorSq_le_of_literal
      (b := b) A x0 σ hLiteral hDiff

/-- Source-facing form of the executable time-zero bound.  Local-objective
differentiability is discharged by Assumption 1.2 (`IsLocallySmooth`) and is
not an additional sampled-loss or adaptive-law premise. -/
theorem online_executable_initial_error_moment_le_of_literal_and_smooth
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hBatch : OnlineBatchAdmissible b b0) :
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
        (onlinePathLaw (b := b) (b0 := b0) A) 0 ∧
      estimatorErrorMoment (onlineLocalProblem A.problem)
          (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
          (onlinePathLaw (b := b) (b0 := b0) A) 0 ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
  exact online_executable_initial_error_moment_le_of_literal
    A x0 σ hLiteral hSmooth.1 hBatch

set_option maxHeartbeats 2000000 in
/-- Base of the weak-correction executable Eq. (46) induction.  Every scalar
component at time zero is well defined under literal Assumption 3.3 and the
law-scoped correction; no globally differentiable sampled-loss family is
reconstructed. -/
theorem onlineProcess_scalar_recurrence_components_zero_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hBatch : OnlineBatchAdmissible b b0) :
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
      onlineProcess_aemeasurable_of_literal_and_lawRegularity
        A x0 hBatch σ hLiteral hRegularity 0
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
/-- The refresh error of the executable Algorithm 3 process at its actual
generated next query is integrable and obeys the literal Assumption 3.3
variance bound.  The initial minibatch remains part of `onlinePathLaw`; the
current refresh minibatch is fresh because the generated query is a function
of the initial minibatch and the strict round prefix.  The law-scoped Track-B
correction is used only for adaptive product-law measurability. -/
theorem
    onlineExecutable_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
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
  let P := onlineLocalProblem A.problem
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let query := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (run (k + 1) path).x
  let batch := fun path :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (path.2 k).2.1.1
  let batchLaw := onlineBatchLaw A.problem b
  let φ := fun (x : Point d)
      (fresh : (i : Worker n) → Fin b.1 → Sample i) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (fresh i j) x)) -
      globalGradient P x‖ ^ 2
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
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_literal_and_lawRegularity
        A x0 hBatch σ hLiteral hRegularity k
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law :=
    ((measurable_state_x d).comp_aemeasurable hstate).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path ↦ (run k path).g) law :=
    ((measurable_state_g d).comp_aemeasurable hstate).aestronglyMeasurable
  have hresidual : AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law :=
    hg.sub ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hquery : AEStronglyMeasurable query law := by
    have hstep := hx.sub (hg.const_smul (A.stepSize : ℝ))
    simpa [query, run, onlineProcess_succ, onlineStep, primalStep_eq] using hstep
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hfresh := onlineExecutable_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hqueryBatch : ProbabilityTheory.IndepFun query batch law := by
    have h := hfresh.1.comp
      (show Measurable
        (fun p : (Point d × Point d) × Point d ↦ p.1.1) by fun_prop)
      (show Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1) by fun_prop)
    simpa [query, batch, run, law, P] using h
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law =
          Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1)
            (Measure.map
              (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
                  (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ path.2 k)
              law) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · exact (measurable_pi_apply k).comp measurable_snd
      _ = Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1)
            (onlineRoundLaw A) := by
              rw [show Measure.map
                  (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
                      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ path.2 k)
                    law = onlineRoundLaw A by
                calc
                  Measure.map
                      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
                          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ path.2 k)
                      law = Measure.map (fun stream :
                          ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
                        (Measure.map Prod.snd law) := by
                          rw [MeasureTheory.Measure.map_map]
                          · rfl
                          · exact measurable_pi_apply k
                          · exact measurable_snd
                  _ = Measure.map (fun stream :
                          ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
                        (SOptLib.iidStreamLaw (onlineRoundLaw A)) := by
                          rw [show Measure.map Prod.snd law =
                              SOptLib.iidStreamLaw (onlineRoundLaw A) by
                            dsimp [law, onlinePathLaw]
                            rw [Measure.map_snd_prod, measure_univ, one_smul]]
                  _ = onlineRoundLaw A := by
                    exact SOptLib.iidStreamLaw_map_eval
                      (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = batchLaw := by
        simpa [batchLaw] using onlineRoundLaw_refreshBatch_marginal
          (b0 := b0) A
  haveI : IsProbabilityMeasure (Measure.map query law) :=
    Measure.isProbabilityMeasure_map hquery.aemeasurable
  have hφ : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) ↦
        φ p.1 p.2) ((Measure.map query law).prod batchLaw) := by
    simpa [φ, P] using
      (onlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
        (b := b) A.problem hRegularity (Measure.map query law))
  have hfixed (x : Point d) :
      Integrable (φ x) batchLaw ∧
        (∫ fresh, φ x fresh ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [φ, P, batchLaw] using
      (onlineFixedRefreshAverage_secondMoment_of_literal
        (b := b) A x σ hLiteral hDiff)
  have hcomp : Integrable (fun path ↦ φ (query path) (batch path)) law :=
    integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := batch)
      (C := varianceAggregateSq σ / (n.1 * b.1)) hφ
      hquery.aemeasurable hbatch.aemeasurable hqueryBatch hbatchLaw
      (fun _ _ ↦ sq_nonneg _) (fun x ↦ (hfixed x).1)
      (fun x ↦ (hfixed x).2)
  have hbound : (∫ path, φ (query path) (batch path) ∂law) ≤
      varianceAggregateSq σ / (n.1 * b.1) :=
    integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := batch)
      hφ hquery.aemeasurable hbatch.aemeasurable hqueryBatch hbatchLaw
      hcomp (fun x ↦ (hfixed x).2)
  simpa [φ, query, batch, run, law, P] using ⟨hcomp, hbound⟩

set_option maxHeartbeats 2000000 in
/-- The executable refresh-error square is independent of its same-round
Bernoulli refresh coin.  The initial minibatch is included in the strict-past
carrier, while the current round is split into its independent coin and
non-coin coordinates. -/
theorem onlineExecutable_refresh_error_sq_indep_refresh_of_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
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
  let xNext := fun pref :
      ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    primalStep A.stepSize (prefixState pref)
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hquery : AEStronglyMeasurable
      (fun path ↦ (run (k + 1) path).x) law := by
    have hstate : AEMeasurable (run (k + 1)) law := by
      simpa [run, law] using
        onlineProcess_aemeasurable_of_literal_and_lawRegularity
          A x0 hBatch σ hLiteral hRegularity (k + 1)
    exact ((measurable_state_x d).comp_aemeasurable hstate).aestronglyMeasurable
  have hprefixLaw : prefixLaw =
      initialLaw.prod (Measure.infinitePi (fun _ : Fin k ↦ roundLaw)) := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw
      (SOptLib.iidStreamLaw roundLaw) measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id,
      iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixLaw, prefixMap, law, initialLaw, roundLaw, coinLaw, restLaw,
      refreshBatchLaw, differenceBatchLaw, compressionLaw, onlinePathLaw,
      onlineRoundLaw, onlineRoundPrefix] using hm.symm
  have hxNext : AEStronglyMeasurable xNext prefixLaw := by
    have hcomp : AEStronglyMeasurable
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
          xNext (path.1, fun j : Fin k ↦ path.2 j.1)) law := by
      refine hquery.congr (Filter.Eventually.of_forall ?_)
      intro path
      dsimp [xNext]
      rw [show prefixState (path.1, fun j : Fin k ↦ path.2 j.1) =
          run k path by
        simpa [prefixMap, onlineRoundPrefix] using hstatePrefix path]
      rfl
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      initialLaw roundLaw k xNext (by
        simpa [law, initialLaw, roundLaw, coinLaw, restLaw, refreshBatchLaw,
          differenceBatchLaw, compressionLaw, onlinePathLaw, onlineRoundLaw]
          using hcomp)
    rw [hprefixLaw]
    exact hfinite
  let refreshKernelRest := fun
      (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (r : ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (r.1.1 i j) (xNext pref))) -
      globalGradient P (xNext pref)‖ ^ 2
  have hRefreshKernelRest : AEStronglyMeasurable
      (Function.uncurry refreshKernelRest) (prefixLaw.prod restLaw) := by
    let refreshKernelPrefixBatch := fun p :
        (((i : Worker n) → Fin b.1 → Sample i) ×
          (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
          ((w : Worker n) → Fin b.1 → Sample w) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i (p.2 i j) (xNext p.1))) -
        globalGradient P (xNext p.1)‖ ^ 2
    have hRefreshPrefixBatch : AEStronglyMeasurable
        refreshKernelPrefixBatch (prefixLaw.prod refreshBatchLaw) := by
      let X := fun p :
          (((i : Worker n) → Fin b.1 → Sample i) ×
            (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b.1 → Sample w) ↦ xNext p.1
      let Y := fun p :
          (((i : Worker n) → Fin b.1 → Sample i) ×
            (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b.1 → Sample w) ↦ p.2
      have hX : AEMeasurable X (prefixLaw.prod refreshBatchLaw) :=
        hxNext.comp_fst.aemeasurable
      have hY : AEMeasurable Y (prefixLaw.prod refreshBatchLaw) :=
        measurable_snd.aemeasurable
      have hXY : ProbabilityTheory.IndepFun X Y
          (prefixLaw.prod refreshBatchLaw) := by
        let xMk := hxNext.mk xNext
        have hxMk : Measurable xMk := hxNext.measurable_mk
        have hindepMk := ProbabilityTheory.indepFun_prod
          (μ := prefixLaw) (ν := refreshBatchLaw) hxMk measurable_id
        have hxae : X =ᵐ[prefixLaw.prod refreshBatchLaw]
            (fun p ↦ xMk p.1) := by
          exact (Measure.quasiMeasurePreserving_fst
            (μ := prefixLaw) (ν := refreshBatchLaw)).tendsto_ae
              hxNext.ae_eq_mk
        exact hindepMk.congr hxae.symm
          (Filter.Eventually.of_forall fun _ ↦ rfl)
      haveI : IsProbabilityMeasure
          (Measure.map X (prefixLaw.prod refreshBatchLaw)) :=
        Measure.isProbabilityMeasure_map hX
      have hmapX : Measure.map X (prefixLaw.prod refreshBatchLaw) =
          Measure.map xNext prefixLaw := by
        have hxMap : AEMeasurable xNext
            (Measure.map Prod.fst (prefixLaw.prod refreshBatchLaw)) := by
          rw [Measure.map_fst_prod, measure_univ, one_smul]
          exact hxNext.aemeasurable
        calc
          Measure.map X (prefixLaw.prod refreshBatchLaw) =
              Measure.map xNext
                (Measure.map Prod.fst (prefixLaw.prod refreshBatchLaw)) := by
            dsimp [X]
            exact (AEMeasurable.map_map_of_aemeasurable
              hxMap measurable_fst.aemeasurable).symm
          _ = Measure.map xNext prefixLaw := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
      have hmapY : Measure.map Y (prefixLaw.prod refreshBatchLaw) =
          refreshBatchLaw := by
        dsimp [Y]
        rw [Measure.map_snd_prod, measure_univ, one_smul]
      have hbase : AEStronglyMeasurable
          (fun p : Point d × ((w : Worker n) → Fin b.1 → Sample w) ↦
            ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
                stochasticGradient A.problem i (p.2 i j) p.1)) -
              globalGradient P p.1‖ ^ 2)
          ((Measure.map X (prefixLaw.prod refreshBatchLaw)).prod
            (Measure.map Y (prefixLaw.prod refreshBatchLaw))) := by
        rw [hmapX, hmapY]
        letI : IsProbabilityMeasure (Measure.map xNext prefixLaw) :=
          Measure.isProbabilityMeasure_map hxNext.aemeasurable
        simpa [P] using
          (onlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
            (b := b) A.problem hRegularity (Measure.map xNext prefixLaw))
      have hcomp := aestronglyMeasurable_comp_of_indep_product_law
        hX hY
        (inferInstance : SigmaFinite
          (Measure.map X (prefixLaw.prod refreshBatchLaw)))
        (inferInstance : SigmaFinite
          (Measure.map Y (prefixLaw.prod refreshBatchLaw)))
        hXY hbase
      simpa [refreshKernelPrefixBatch, X, Y] using hcomp
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
    simpa [refreshKernelRest, refreshKernelPrefixBatch, pullBatch,
      Function.uncurry] using
      hRefreshPrefixBatch.comp_quasiMeasurePreserving hqmp
  have hindep := initial_iidStream_prefix_current_snd_kernel_indep_fst
    initialLaw coinLaw restLaw k refreshKernelRest (by
      rw [← hprefixLaw]
      exact hRefreshKernelRest)
  apply hindep.congr (Filter.Eventually.of_forall ?_)
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  intro path
  change refreshKernelRest (prefixMap path) (path.2 k).2 = _
  dsimp [refreshKernelRest, xNext]
  rw [hstatePrefix path]
  rfl

set_option maxHeartbeats 2000000 in
/-- The complete executable nonrefresh residual square is independent of its
same-round Bernoulli refresh coin.  The sampled initializer and strict round
prefix form the past carrier; the difference minibatch and compressor are the
non-coin coordinates of the current round.  This is the executable analogue
of the independence component used in the proof-exact Eq. (46) recurrence. -/
theorem onlineExecutable_nonrefresh_error_sq_indep_refresh_of_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
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
      onlineProcess_aemeasurable_of_literal_and_lawRegularity
        A x0 hBatch σ hLiteral hRegularity k
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
    simpa [innovationKernel, xNext, x, noiseLaw, differenceBatchLaw,
      compressionLaw, onlineDifferenceCompressionLaw, P] using
      onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity prefixLaw xNext x hxNext hx
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

set_option maxHeartbeats 16000000 in
/-- The executable nonrefresh branch under genuine source Assumption 3.2 and
the weak law-level Track-B correction.  The independent initial minibatch is
retained in the strict-past carrier, so the fixed-query Assumption 3.2 moment
is applied at the actual generated executable queries. -/
theorem
    onlineExecutable_nonrefresh_branch_moments_of_genuine_assumption32_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
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
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k ∧
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 ∧
      Integrable (fun path ↦ ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment P run law k +
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k ∧
      ProbabilityTheory.IndepFun
        (fun path ↦ ‖residual path + innovation path‖ ^ 2)
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1) law := by
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
  let streamCurrent := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k
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
    (ω * (rootMeanSquare Llocal) ^ 2 +
      (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
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
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ roundLaw) k)
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
  let innovationKernel := fun
      (pref : ((i : Worker n) → Fin b.1 → Sample i) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
          (q.2 i) -
        localGradientDifference P i (xNext pref) (x pref))
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
  let B := fun pref ↦ C * ‖xNext pref - x pref‖ ^ 2
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      onlineProcess_aemeasurable_of_literal_and_lawRegularity
        A x0 hBatch σ hLiteral hRegularity k
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
  have hkernel : AEStronglyMeasurable
      (fun p ↦ innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
    simpa [innovationKernel, xNext, x, noiseLaw, P] using
      onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity prefixLaw xNext x hxNext hx
  have hkernelSq : AEStronglyMeasurable
      (fun p ↦ ‖innovationKernel p.1 p.2‖ ^ 2)
      (prefixLaw.prod noiseLaw) := by
    simpa [pow_two] using hkernel.norm.mul hkernel.norm
  have hAverage : OnlineAverageSmoothness (b0 := b0) A.problem run ℒlocal :=
    onlineAssumption32Genuine_to_onlineAverageSmoothness hAssumption32
  have hfixed (pref) := onlineFixed_nonrefresh_average_moment_of_assumption32
    (b0 := b0) A (xNext pref) (x pref) Llocal ℒlocal ω hSmooth
      (fun i ↦ by
        simpa [xNext, x, prefixState, run, onlineExecutablePrefixState,
          onlineProcess_succ, onlineStep, primalStep_eq] using
          hAverage.2 k i
            (pref.1, onlineExtendRoundPrefix fallback pref.2))
      hRegularity hQuantizer
  have hB_aesm : AEStronglyMeasurable B prefixLaw := by
    dsimp [B]
    simpa [pow_two] using
      ((hxNext.sub hx).norm.mul (hxNext.sub hx).norm).const_mul C
  have hB_comp_int : Integrable (fun path ↦ B (prefixMap path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    dsimp [B, xNext, x, prefixState, run]
    rw [onlineProcess_succ]
    have heq := onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])
    rw [heq]
    rfl
  have havgSqComp : Integrable
      (fun path ↦ ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2) law :=
    integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
      (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
      (φ := fun pref q ↦ ‖innovationKernel pref q‖ ^ 2) (B := B)
      hkernelSq hB_aesm hprefix.aemeasurable hnoise.aemeasurable hfresh
      hnoiseLaw (fun _ _ ↦ sq_nonneg _) (fun pref ↦ (hfixed pref).2.2.1)
      hB_comp_int (fun pref ↦ by simpa [B, C] using (hfixed pref).2.2.2)
  have hinnovationComp : ∀ path,
      innovationKernel (prefixMap path) (noise path) = innovation path := by
    intro path
    dsimp [innovationKernel, innovation, xNext, x, noise, noiseOfRound, current]
    rw [hstatePrefix path]
    rw [show (run (k + 1) path).x = primalStep A.stepSize (run k path) by rfl]
  have hinnovationMeas : AEStronglyMeasurable innovation law := by
    have hkernelMapped : AEStronglyMeasurable
        (fun p ↦ innovationKernel p.1 p.2)
        ((Measure.map prefixMap law).prod (Measure.map noise law)) := by
      rw [show Measure.map prefixMap law = prefixLaw from rfl, hnoiseLaw]
      exact hkernel
    have hcomp := aestronglyMeasurable_comp_of_indep_product_law
      hprefix.aemeasurable hnoise.aemeasurable
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law))
      hfresh hkernelMapped
    exact hcomp.congr (Filter.Eventually.of_forall hinnovationComp)
  have havgSq : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law :=
    havgSqComp.congr (Filter.Eventually.of_forall fun path ↦ by
      simpa only using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
        (hinnovationComp path))
  have havgBoundComp :
      (∫ path, ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2 ∂law) ≤
        ∫ path, B (prefixMap path) ∂law :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
      (φ := fun pref q ↦ ‖innovationKernel pref q‖ ^ 2) (B := B)
      hkernelSq hB_aesm hprefix.aemeasurable hnoise.aemeasurable hfresh
      hnoiseLaw havgSqComp hB_comp_int
      (fun pref ↦ by simpa [B, C] using (hfixed pref).2.2.2)
  have havgBound : (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
      C * stepMoment run law k := by
    calc
      (∫ path, ‖innovation path‖ ^ 2 ∂law) =
          ∫ path, ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2 ∂law := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun path ↦ by
              simpa only using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
                (hinnovationComp path).symm
      _ ≤ ∫ path, B (prefixMap path) ∂law := havgBoundComp
      _ = C * stepMoment run law k := by
        unfold stepMoment
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with path
        dsimp [B, xNext, x, prefixState, run, stepMoment]
        rw [onlineProcess_succ]
        have heq := onlineProcess_congr_round_prefix A x0 hBatch k path.1
          (path := path.2)
          (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
          (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])
        rw [heq]
        rfl
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable hstate).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hstate))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hinnerInt : Integrable
      (fun path ↦ ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq havgSq
  have hscalarProd : AEStronglyMeasurable
      (fun p ↦ ⟪direction p.1, innovationKernel p.1 p.2⟫_ℝ)
      (prefixLaw.prod noiseLaw) :=
    hdirection.comp_fst.inner hkernel
  have hinnerComp : ∀ path,
      ⟪direction (prefixMap path), innovationKernel (prefixMap path) (noise path)⟫_ℝ =
        ⟪residual path, innovation path⟫_ℝ := by
    intro path
    rw [hinnovationComp path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hinnerCompInt : Integrable
      (fun path ↦ ⟪direction (prefixMap path),
        innovationKernel (prefixMap path) (noise path)⟫_ℝ) law :=
    hinnerInt.congr (Filter.Eventually.of_forall fun path ↦ (hinnerComp path).symm)
  have hfixedInnerZero : ∀ pref,
      (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) = 0 := by
    intro pref
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction pref)) (hfixed pref).1
    calc
      (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) =
          (innerSL ℝ) (direction pref)
            (∫ q, innovationKernel pref q ∂noiseLaw) := hlin
      _ = 0 := by rw [(hfixed pref).2.1]; simp
  have hcrossComp :=
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := law) (ν := noiseLaw) (X := prefixMap) (Y := noise)
      (φ := fun pref q ↦ ⟪direction pref, innovationKernel pref q⟫_ℝ)
      hscalarProd hprefix.aemeasurable hnoise.aemeasurable hfresh hnoiseLaw
      hinnerCompInt hfixedInnerZero
  have hcross : (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
        ∫ path, ⟪direction (prefixMap path),
          innovationKernel (prefixMap path) (noise path)⟫_ℝ ∂law by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path ↦ (hinnerComp path).symm]
    exact hcrossComp
  have hnonrefreshInt : Integrable
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresidualMeas hinnovationMeas hresidualSq havgSq
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
      (fun z _ ↦ by cases z <;> simp [pair, hresidualSq, havgSq])
      (fun z _ w _ hzw ↦ by
        cases z <;> cases w
        · exact False.elim (hzw rfl)
        · simpa [pair] using hcross
        · simpa [pair, real_inner_comm] using hcross
        · exact False.elim (hzw rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  have hnonrefreshIndep : ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2)
      (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1) law := by
    simpa [residual, innovation, P, run, law] using
      onlineExecutable_nonrefresh_error_sq_indep_refresh_of_lawRegularity
        A x0 hBatch σ hLiteral hRegularity k
  refine ⟨havgSq, ?_, hcross, hnonrefreshInt, ?_, hnonrefreshIndep⟩
  · simpa [C] using havgBound
  · rw [hnonrefreshEq]
    change estimatorErrorMoment P run law k +
        (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤ _
    exact add_le_add_right (by simpa [C] using havgBound) _

/-- Source-facing executable refresh-branch package.  Assumption 1.2
discharges differentiability of the averaged local objectives; the only
sample-gradient premises are literal Assumption 3.3 and the separately
classified law-scoped correction. -/
theorem onlineExecutable_refresh_branch_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal σ : Worker n → ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ) :
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlinePathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    (Integrable refreshErrorSq law ∧
      (∫ path, refreshErrorSq path ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1)) ∧
      ProbabilityTheory.IndepFun refreshErrorSq
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1) law := by
  dsimp only
  constructor
  · exact
      onlineExecutable_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
        A x0 hBatch σ hLiteral hRegularity hSmooth.1 k
  · exact onlineExecutable_refresh_error_sq_indep_refresh_of_lawRegularity
      A x0 hBatch σ hLiteral hRegularity k

end MARINA
