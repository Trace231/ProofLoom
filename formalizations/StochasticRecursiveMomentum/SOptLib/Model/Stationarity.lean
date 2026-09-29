import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SOptLib.Glue.Probability
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Objective

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace SOptLib

/-- Finite weighted expectation of squared exact stationarity certificates.

For an abstract finite output index set, real stopping weights, sample law, and
exact stationarity certificate `g`, this names the weighted sum
`∑ k, w k * E[‖g k‖²]` used by randomized output analyses.

Layer: Model | Concept: Objective
Proof: (definitional construction; finite weighted Bochner-integral wrapper for
  squared norm exact stationarity certificates)
Source: Mathlib finite sums, normed-type APIs, and Bochner integration of real
  observables
Used in: randomized stochastic mirror descent weighted stopping expectation of
  exact projected-gradient squared norms
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def weightedExpectedExactStationarity
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (w : ι → ℝ) (μ : Measure Ω) (g : ι → Ω → E) : ℝ :=
  Finset.sum times (fun k => w k * ∫ ω, ‖g k ω‖ ^ 2 ∂μ)

/-- Finite weighted expectation of squared stationarity certificates.

For an abstract finite set of output times, weights, sample law, and stochastic
stationarity certificate `G`, this names the weighted sum
`∑ k, w k * E[‖G k‖²]` used by randomized output analyses.

Layer: Model | Concept: Objective
Proof: (definitional construction; finite weighted Bochner-integral wrapper for
  squared norm stationarity certificates)
Source: Mathlib finite sums, normed-type APIs, and Bochner integration of real
  observables
Used in: randomized stochastic mirror descent weighted stopping expectation of
  stochastic projected-gradient squared norms
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
noncomputable def weightedExpectedStationarity
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (w : ι → ℝ) (μ : Measure Ω) (G : ι → Ω → E) : ℝ :=
  Finset.sum times (fun k => w k * ∫ ω, ‖G k ω‖ ^ 2 ∂μ)

namespace ConditionalGradient

/-- Scalar expected conditional-gradient Wolfe-gap upper bound with an
epoch-penalty term and a normalized L1 mini-batch floor.

The expression first collects the alpha-normalized objective-gap, curvature,
epoch-penalty, and variance terms, then appends the retained
`diameter * noiseScale / sqrt batchSize` L1 floor.

Layer: Model | Concept: Objective
Proof: (definitional construction; corrected scalar conditional-gradient
  convergence bound assembled from epoch-penalty and normalized L1-floor
  templates)
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after the Theorem 7.17 epoch-penalty bound is corrected by the
  Lemma 7.5 L1 floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def expectedWolfeGapUpperBoundWithEpochPenaltyAndL1Floor
    (initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ)
    (iterations batchSize : ℕ) (alphaSqSum epochPenalty : ℝ) : ℝ :=
  (initialValue - optimalValue) / alphaSum +
    smoothness * diameter ^ 2 / alphaSum *
      (3 / 2 * alphaSqSum + epochPenalty) +
    (iterations : ℝ) * noiseScale ^ 2 /
      (2 * smoothness * batchSize * alphaSum) +
    diameter * noiseScale / Real.sqrt (batchSize : ℝ)

/-- The epoch-penalty-and-L1-floor expected Wolfe-gap upper-bound template
unfolds to its collected scalar contributions.

Layer: Model | Gap: Level 0 (epoch-penalty and L1-floor expected Wolfe-gap
  upper-bound unfolding)
Proof: by rfl after unfolding
  `expectedWolfeGapUpperBoundWithEpochPenaltyAndL1Floor` and its two scalar
  component templates.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after the Theorem 7.17 epoch-penalty bound is corrected by the
  Lemma 7.5 L1 floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem expectedWolfeGapUpperBoundWithEpochPenaltyAndL1Floor_def
    (initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ)
    (iterations batchSize : ℕ) (alphaSqSum epochPenalty : ℝ) :
    expectedWolfeGapUpperBoundWithEpochPenaltyAndL1Floor initialValue
        optimalValue smoothness diameter noiseScale alphaSum iterations
        batchSize alphaSqSum epochPenalty =
      (initialValue - optimalValue) / alphaSum +
        smoothness * diameter ^ 2 / alphaSum *
          (3 / 2 * alphaSqSum + epochPenalty) +
        (iterations : ℝ) * noiseScale ^ 2 /
          (2 * smoothness * batchSize * alphaSum) +
        diameter * noiseScale / Real.sqrt (batchSize : ℝ) := by
  rfl

/-- Adding the normalized L1 mini-batch floor can only increase the
epoch-penalty scalar expression when the diameter and noise scale are
nonnegative.

Layer: Model | Gap: Level 0 (epoch-penalty-and-L1-floor lower estimate)
Proof: the added floor term is nonnegative because both scalar factors and
  `Real.sqrt` are nonnegative.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: comparisons between epoch-penalty-only and corrected
  epoch-penalty-and-L1-floor stochastic conditional-gradient bounds
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem expectedWolfeGapUpperBoundWithEpochPenalty_le_expectedWolfeGapUpperBoundWithEpochPenaltyAndL1Floor
    {initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ}
    {iterations batchSize : ℕ} {alphaSqSum epochPenalty : ℝ}
    (hdiameter : 0 ≤ diameter) (hnoiseScale : 0 ≤ noiseScale) :
    (initialValue - optimalValue) / alphaSum +
        smoothness * diameter ^ 2 / alphaSum *
          (3 / 2 * alphaSqSum + epochPenalty) +
        (iterations : ℝ) * noiseScale ^ 2 /
          (2 * smoothness * batchSize * alphaSum) ≤
      expectedWolfeGapUpperBoundWithEpochPenaltyAndL1Floor initialValue
        optimalValue smoothness diameter noiseScale alphaSum iterations
        batchSize alphaSqSum epochPenalty := by
  rw [expectedWolfeGapUpperBoundWithEpochPenaltyAndL1Floor_def]
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg hdiameter hnoiseScale) (Real.sqrt_nonneg _))

/-- Scalar upper-bound template for an expected conditional-gradient Wolfe gap.

The expression combines the initial objective gap, the smoothness-diameter
term, and the stochastic-noise term with iteration and batch-size normalizers.

Layer: Model | Concept: Objective
Proof: (definitional construction; scalar conditional-gradient convergence
  bound assembled from objective-gap, smoothness-diameter, and oracle-noise
  contributions)
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after telescope and variance terms are collected
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def expectedWolfeGapUpperBound
    (initialValue optimalValue smoothness diameter noiseScale : ℝ)
    (iterations batchSize : ℕ) : ℝ :=
  (initialValue - optimalValue) / Real.sqrt (iterations : ℝ) +
    7 * smoothness * diameter ^ 2 / (2 * Real.sqrt (iterations : ℝ)) +
    4 * noiseScale * diameter / Real.sqrt (batchSize : ℝ)

/-- The expected Wolfe-gap upper-bound template unfolds to its three scalar
contributions.

Layer: Model | Gap: Level 0 (expected Wolfe-gap upper-bound unfolding)
Proof: by rfl after unfolding `expectedWolfeGapUpperBound`.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after telescope and variance terms are collected
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem expectedWolfeGapUpperBound_def
    (initialValue optimalValue smoothness diameter noiseScale : ℝ)
    (iterations batchSize : ℕ) :
    expectedWolfeGapUpperBound initialValue optimalValue smoothness diameter
        noiseScale iterations batchSize =
      (initialValue - optimalValue) / Real.sqrt (iterations : ℝ) +
        7 * smoothness * diameter ^ 2 / (2 * Real.sqrt (iterations : ℝ)) +
        4 * noiseScale * diameter / Real.sqrt (batchSize : ℝ) := by
  rfl

/-- Nonnegativity of the scalar expected Wolfe-gap upper-bound template under
the standard nonnegative convergence parameters.

Layer: Model | Gap: Level 0 (expected Wolfe-gap upper-bound nonnegativity)
Proof: each summand is nonnegative from the corresponding parameter
  nonnegativity and nonnegative square-root normalizers.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  displays and sanity checks for collected scalar RHS terms
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem expectedWolfeGapUpperBound_nonneg
    {initialValue optimalValue smoothness diameter noiseScale : ℝ}
    {iterations batchSize : ℕ}
    (hgap : 0 ≤ initialValue - optimalValue)
    (hsmoothness : 0 ≤ smoothness)
    (hdiameter : 0 ≤ diameter)
    (hnoiseScale : 0 ≤ noiseScale) :
    0 ≤ expectedWolfeGapUpperBound initialValue optimalValue smoothness diameter
      noiseScale iterations batchSize := by
  rw [expectedWolfeGapUpperBound_def]
  positivity

/-- Scalar upper-bound template for an expected conditional-gradient Wolfe gap
with an epoch-penalty term.

The expression combines an alpha-normalized initial objective gap, a
smoothness-diameter curvature term weighted by alpha-square and epoch
penalties, and a normalized stochastic-noise term.

Layer: Model | Concept: Objective
Proof: (definitional construction; scalar conditional-gradient convergence
  bound assembled from alpha normalization, curvature, epoch-penalty, and
  oracle-noise contributions)
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after alpha-square, epoch-penalty, and variance terms are collected
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def expectedWolfeGapUpperBoundWithEpochPenalty
    (initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ)
    (iterations batchSize : ℕ) (alphaSqSum epochPenalty : ℝ) : ℝ :=
  (initialValue - optimalValue) / alphaSum +
    smoothness * diameter ^ 2 / alphaSum *
      (3 / 2 * alphaSqSum + epochPenalty) +
    (iterations : ℝ) * noiseScale ^ 2 /
      (2 * smoothness * batchSize * alphaSum)

/-- The epoch-penalty expected Wolfe-gap upper-bound template unfolds to its
alpha-normalized scalar contributions.

Layer: Model | Gap: Level 0 (epoch-penalty expected Wolfe-gap upper-bound
  unfolding)
Proof: by rfl after unfolding `expectedWolfeGapUpperBoundWithEpochPenalty`.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after alpha-square, epoch-penalty, and variance terms are collected
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem expectedWolfeGapUpperBoundWithEpochPenalty_def
    (initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ)
    (iterations batchSize : ℕ) (alphaSqSum epochPenalty : ℝ) :
    expectedWolfeGapUpperBoundWithEpochPenalty initialValue optimalValue
        smoothness diameter noiseScale alphaSum iterations batchSize alphaSqSum
        epochPenalty =
      (initialValue - optimalValue) / alphaSum +
        smoothness * diameter ^ 2 / alphaSum *
          (3 / 2 * alphaSqSum + epochPenalty) +
        (iterations : ℝ) * noiseScale ^ 2 /
        (2 * smoothness * batchSize * alphaSum) := by
  rfl

/-- The epoch-penalty expected Wolfe-gap upper-bound template is monotone in
the epoch penalty whenever the curvature scale multiplying that penalty is
nonnegative.

Layer: Model | Gap: Level 0 (epoch-penalty monotonicity for expected Wolfe-gap
  upper bounds)
Proof: the only changing term is the epoch-penalty contribution, multiplied by
  a nonnegative curvature scale.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: comparisons between printed and corrected stochastic
  conditional-gradient bounds after epoch residual terms are collected
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem expectedWolfeGapUpperBoundWithEpochPenalty_mono_epochPenalty
    {initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ}
    {iterations batchSize : ℕ} {alphaSqSum epochPenalty epochPenalty' : ℝ}
    (hcurv : 0 ≤ smoothness * diameter ^ 2 / alphaSum)
    (hepoch : epochPenalty ≤ epochPenalty') :
    expectedWolfeGapUpperBoundWithEpochPenalty initialValue optimalValue
        smoothness diameter noiseScale alphaSum iterations batchSize alphaSqSum
        epochPenalty ≤
      expectedWolfeGapUpperBoundWithEpochPenalty initialValue optimalValue
        smoothness diameter noiseScale alphaSum iterations batchSize alphaSqSum
        epochPenalty' := by
  have hmiddle :
      smoothness * diameter ^ 2 / alphaSum *
          (3 / 2 * alphaSqSum + epochPenalty) ≤
        smoothness * diameter ^ 2 / alphaSum *
          (3 / 2 * alphaSqSum + epochPenalty') :=
    mul_le_mul_of_nonneg_left (add_le_add_right hepoch (3 / 2 * alphaSqSum))
      hcurv
  exact add_le_add_left
    (add_le_add_right hmiddle ((initialValue - optimalValue) / alphaSum))
    ((iterations : ℝ) * noiseScale ^ 2 /
      (2 * smoothness * batchSize * alphaSum))

/-- Corrected scalar upper-bound template for an expected conditional-gradient
Wolfe gap with a normalized L1 mini-batch floor.

The expression appends `diameter * noiseScale / sqrt batchSize` to a previously
collected expected-Wolfe-gap upper bound, isolating the floor term that remains
after mini-batch L1 control is normalized.

Layer: Model | Concept: Objective
Proof: (definitional construction; scalar conditional-gradient convergence
  bound corrected by a normalized diameter-noise mini-batch floor)
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with mini-batch variance control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after the printed bound is corrected by the Lemma 7.5 L1 floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def expectedWolfeGapUpperBoundWithL1Floor
    (baseBound diameter noiseScale : ℝ) (batchSize : ℕ) : ℝ :=
  baseBound + diameter * noiseScale / Real.sqrt (batchSize : ℝ)

/-- The corrected expected Wolfe-gap upper-bound template unfolds to the base
bound plus the normalized L1 mini-batch floor.

Layer: Model | Gap: Level 0 (corrected expected Wolfe-gap upper-bound unfolding)
Proof: by rfl after unfolding `expectedWolfeGapUpperBoundWithL1Floor`.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with mini-batch variance control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after the printed bound is corrected by the Lemma 7.5 L1 floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem expectedWolfeGapUpperBoundWithL1Floor_def
    (baseBound diameter noiseScale : ℝ) (batchSize : ℕ) :
    expectedWolfeGapUpperBoundWithL1Floor baseBound diameter noiseScale batchSize =
      baseBound + diameter * noiseScale / Real.sqrt (batchSize : ℝ) := by
  rfl

/-- The normalized L1 mini-batch floor can only increase the base upper bound
when the diameter and noise scale are nonnegative.

Layer: Model | Gap: Level 0 (corrected expected Wolfe-gap upper-bound lower
  estimate)
Proof: the added floor term is nonnegative because both scalar factors and
  `Real.sqrt` are nonnegative.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with mini-batch variance control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display after the printed bound is corrected by the Lemma 7.5 L1 floor
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem le_expectedWolfeGapUpperBoundWithL1Floor
    {baseBound diameter noiseScale : ℝ} {batchSize : ℕ}
    (hdiameter : 0 ≤ diameter) (hnoiseScale : 0 ≤ noiseScale) :
    baseBound ≤
      expectedWolfeGapUpperBoundWithL1Floor baseBound diameter noiseScale batchSize := by
  rw [expectedWolfeGapUpperBoundWithL1Floor_def]
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg hdiameter hnoiseScale) (Real.sqrt_nonneg _))

/-- Scalar expected conditional-gradient Wolfe-gap upper bound assembled from a
stepsize schedule and epoch maximum penalties.

The expression computes the alpha-square budget and the epoch-maximum penalty
from a schedule `alpha` and an epoch index map, then feeds those two scalar
terms into the epoch-penalty Wolfe-gap upper-bound template.

Layer: Model | Concept: Objective
Proof: (definitional construction; finite schedule sums assembled before
  applying the scalar epoch-penalty conditional-gradient convergence template)
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display under a realized Algorithm 7.13 stepsize schedule
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def expected_wolfe_gap_upper_bound_with_epoch_schedule
    (initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ)
    (iterations batchSize epochs epochLength : ℕ)
    (alpha : ℕ → ℝ) (globalIndex : ℕ → ℕ → ℕ) (epochMaxAlpha : ℕ → ℝ) : ℝ :=
  expectedWolfeGapUpperBoundWithEpochPenalty initialValue optimalValue
    smoothness diameter noiseScale alphaSum iterations batchSize
    (Finset.sum (Finset.Icc 1 iterations) (fun k => alpha k ^ 2))
    (Finset.sum (Finset.Icc 0 epochs) (fun s =>
      Finset.sum (Finset.Icc 1 epochLength) (fun j => alpha (globalIndex s j)) *
        epochMaxAlpha s))

/-- The schedule-indexed expected Wolfe-gap upper-bound template unfolds to the
alpha-normalized scalar contributions with finite schedule sums.

Layer: Model | Gap: Level 0 (schedule-indexed expected Wolfe-gap upper-bound
  unfolding)
Proof: by rfl after unfolding `expected_wolfe_gap_upper_bound_with_epoch_schedule`
  and the scalar epoch-penalty upper-bound template.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: stochastic nonconvex conditional-gradient final expected Wolfe-gap
  display under a realized Algorithm 7.13 stepsize schedule
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
@[simp]
theorem expected_wolfe_gap_upper_bound_with_epoch_schedule_def
    (initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ)
    (iterations batchSize epochs epochLength : ℕ)
    (alpha : ℕ → ℝ) (globalIndex : ℕ → ℕ → ℕ) (epochMaxAlpha : ℕ → ℝ) :
    expected_wolfe_gap_upper_bound_with_epoch_schedule initialValue optimalValue
        smoothness diameter noiseScale alphaSum iterations batchSize epochs
        epochLength alpha globalIndex epochMaxAlpha =
      (initialValue - optimalValue) / alphaSum +
        smoothness * diameter ^ 2 / alphaSum *
          (3 / 2 *
            Finset.sum (Finset.Icc 1 iterations) (fun k => alpha k ^ 2) +
          Finset.sum (Finset.Icc 0 epochs) (fun s =>
            Finset.sum (Finset.Icc 1 epochLength)
              (fun j => alpha (globalIndex s j)) *
            epochMaxAlpha s)) +
        (iterations : ℝ) * noiseScale ^ 2 /
          (2 * smoothness * batchSize * alphaSum) := by
  rfl

/-- The schedule-indexed expected Wolfe-gap upper-bound template is monotone in
the epoch maximum schedule when each epoch's schedule weight is nonnegative and
the curvature scale multiplying the epoch penalty is nonnegative.

Layer: Model | Gap: Level 0 (schedule-indexed epoch-maximum monotonicity for
  expected Wolfe-gap upper bounds)
Proof: collect pointwise monotonicity of each weighted epoch penalty into a
  finite-sum inequality, then apply the scalar epoch-penalty monotonicity
  template.
Source: Frank-Wolfe and stochastic conditional-gradient expected stationarity
  convergence bounds with variance-reduced epoch residual control
Used in: comparisons of stochastic conditional-gradient bounds under larger
  epoch maximum residual controls
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem expected_wolfe_gap_upper_bound_with_epoch_schedule_mono_epoch_max_alpha
    {initialValue optimalValue smoothness diameter noiseScale alphaSum : ℝ}
    {iterations batchSize epochs epochLength : ℕ}
    {alpha : ℕ → ℝ} {globalIndex : ℕ → ℕ → ℕ}
    {epochMaxAlpha epochMaxAlpha' : ℕ → ℝ}
    (hcurv : 0 ≤ smoothness * diameter ^ 2 / alphaSum)
    (hweight_nonneg :
      ∀ s ∈ Finset.Icc 0 epochs,
        0 ≤ Finset.sum (Finset.Icc 1 epochLength)
          (fun j => alpha (globalIndex s j)))
    (hmax :
      ∀ s ∈ Finset.Icc 0 epochs, epochMaxAlpha s ≤ epochMaxAlpha' s) :
    expected_wolfe_gap_upper_bound_with_epoch_schedule initialValue optimalValue
        smoothness diameter noiseScale alphaSum iterations batchSize epochs
        epochLength alpha globalIndex epochMaxAlpha ≤
      expected_wolfe_gap_upper_bound_with_epoch_schedule initialValue optimalValue
        smoothness diameter noiseScale alphaSum iterations batchSize epochs
        epochLength alpha globalIndex epochMaxAlpha' := by
  apply expectedWolfeGapUpperBoundWithEpochPenalty_mono_epochPenalty hcurv
  exact Finset.sum_le_sum (fun s hs =>
    mul_le_mul_of_nonneg_left (hmax s hs) (hweight_nonneg s hs))

/-- A Wolfe-gap certificate is measurable when realized by a measurable linear
minimization oracle.

For a measurable parameterization `eval`, a measurable gradient along that
parameterization, and a measurable LMO selector, the selected-maximizer Wolfe
gap is measurable whenever the selector certificates identify it with the LMO
inner-product model.

Layer: Model | Gap: Level 1 (LMO-realized Wolfe-gap measurability)
Proof: compose the measurable gradient with the measurable LMO, build the
  measurable displacement by subtraction, compose the continuous inner product,
  and rewrite the selected Wolfe gap using the LMO realization theorem.
Source: Frank-Wolfe conditional-gradient stationarity certificates and Mathlib
  measurable arithmetic for subtraction and continuous inner products
Used in: stochastic and finite-sum conditional-gradient expected Wolfe-gap
  integrability through a measurable linear minimization oracle
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem wolfeGap_measurable_of_lmo
    {P E : Type*} [MeasurableSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [MeasurableSub₂ E] [OpensMeasurableSpace (E × E)]
    {X : Set E} (eval : P → E) (grad : E → E)
    (maximizer : E → {y : E // y ∈ X}) (linearMinimizer : E → E)
    (heval : Measurable eval)
    (hgrad : Measurable (fun p : P => grad (eval p)))
    (hlmo : Measurable linearMinimizer)
    (linearMinimizer_mem : ∀ g : E, linearMinimizer g ∈ X)
    (linearMinimizer_is_argmin :
      ∀ g z : E, z ∈ X → ⟪g, linearMinimizer g⟫_ℝ ≤ ⟪g, z⟫_ℝ)
    (hmax : ∀ x : E, ∀ z : {z : E // z ∈ X},
      ⟪grad x, x - (z : E)⟫_ℝ ≤
        ⟪grad x, x - (maximizer x : E)⟫_ℝ) :
    Measurable (fun p : P => wolfeGap grad maximizer (eval p)) := by
  classical
  have hlmo_grad : Measurable (fun p : P => linearMinimizer (grad (eval p))) :=
    hlmo.comp hgrad
  have hdisp :
      Measurable (fun p : P => eval p - linearMinimizer (grad (eval p))) :=
    heval.sub hlmo_grad
  have hmodel : Measurable
      (fun p : P => ⟪grad (eval p),
        eval p - linearMinimizer (grad (eval p))⟫_ℝ) :=
    continuous_inner.measurable.comp (hgrad.prodMk hdisp)
  rw [show (fun p : P => wolfeGap grad maximizer (eval p)) =
      (fun p : P => ⟪grad (eval p),
        eval p - linearMinimizer (grad (eval p))⟫_ℝ) from
      funext (fun p =>
        wolfeGap_eq_linearMinimizer
          (grad := grad) (maximizer := maximizer)
          (linearMinimizer := linearMinimizer)
          (linearMinimizer_mem := linearMinimizer_mem)
          (linearMinimizer_is_argmin := linearMinimizer_is_argmin)
          (hmax := hmax) (eval p))]
  exact hmodel

end ConditionalGradient

/-- Selected-output certificate expectations agree when the selected law and
certificate agree.

For an output-index PMF and sample law, the joint selected-output law is the
product of the PMF measure and the sample measure. If two selected PMFs are
equal and their certificates agree pointwise on index/sample pairs, their
Bochner expectations under these joint laws are equal.

Layer: Model | Gap: Level 0 (selected-output law and certificate congruence)
Proof: rewrite the selected-index PMF equality through the product law, then
  apply Bochner integral congruence from pointwise certificate equality.
Source: Mathlib probability mass functions, product measures, and Bochner
  integral congruence APIs
Used in: stochastic nonconvex conditional gradient well-defined branch
  randomized Wolfe-gap expectation and stochastic mirror descent selected
  stationarity-certificate expectation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem expected_selected_output_certificate_eq_of_law_and_certificate_eq
    {α Ω β : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [NormedAddCommGroup β] [NormedSpace ℝ β]
    (μ : Measure Ω) (p_ext p_ref : PMF α)
    (cert_ext cert_ref : α × Ω → β)
    (h_law : p_ext = p_ref)
    (h_cert : ∀ q, cert_ext q = cert_ref q) :
    ∫ q, cert_ext q ∂(p_ext.toMeasure.prod μ) =
      ∫ q, cert_ref q ∂(p_ref.toMeasure.prod μ) := by
  subst p_ext
  exact integral_congr_ae (Filter.Eventually.of_forall h_cert)

/-- A normalized finite weighted expectation of scalar certificates.

For a finite set of candidate output times, real weights, a normalizing
denominator, a sample law, and scalar certificates, this names
`W⁻¹ * ∑ k, w k * E[cert k]`, the randomized-output expectation formula used
for scalar stationarity or gap certificates.

Layer: Model | Concept: Objective
Proof: (definitional construction; inverse-normalized finite weighted
  Bochner-integral wrapper for scalar certificates)
Source: Mathlib finite sums, real scalar algebra, and Bochner integration of
  real observables
Used in: randomized stochastic conditional gradient Wolfe-gap expectation and
  randomized stochastic mirror descent stationarity-certificate expectation
Book citation: book/PAPER/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def normalizedWeightedExpectedCertificate
    {ι Ω : Type*} [MeasurableSpace Ω]
    (times : Finset ι) (denom : ℝ) (w : ι → ℝ)
    (μ : Measure Ω) (cert : ι → Ω → ℝ) : ℝ :=
  denom⁻¹ * Finset.sum times (fun k => w k * ∫ ω, cert k ω ∂μ)

@[simp] theorem normalizedWeightedExpectedCertificate_def
    {ι Ω : Type*} [MeasurableSpace Ω]
    (times : Finset ι) (denom : ℝ) (w : ι → ℝ)
    (μ : Measure Ω) (cert : ι → Ω → ℝ) :
    normalizedWeightedExpectedCertificate times denom w μ cert =
      denom⁻¹ * Finset.sum times (fun k => w k * ∫ ω, cert k ω ∂μ) := rfl

/-- The normalized weighted expected certificate is the sum using normalized weights. -/
theorem normalizedWeightedExpectedCertificate_eq_sum_normalized
    {ι Ω : Type*} [MeasurableSpace Ω]
    (times : Finset ι) (denom : ℝ) (w : ι → ℝ)
    (μ : Measure Ω) (cert : ι → Ω → ℝ) :
    normalizedWeightedExpectedCertificate times denom w μ cert =
      Finset.sum times (fun k => (w k / denom) * ∫ ω, cert k ω ∂μ) := by
  rw [normalizedWeightedExpectedCertificate_def]
  calc
    denom⁻¹ * Finset.sum times (fun k => w k * ∫ ω, cert k ω ∂μ) =
        Finset.sum times (fun k => w k * ∫ ω, cert k ω ∂μ) / denom := by
      ring
    _ = Finset.sum times (fun k => (w k * ∫ ω, cert k ω ∂μ) / denom) := by
      rw [Finset.sum_div]
    _ = Finset.sum times (fun k => (w k / denom) * ∫ ω, cert k ω ∂μ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring

open MeasureTheory
open scoped BigOperators

/-- An a.e. scalar certificate bound lifts to a normalized weighted expectation bound.

For a finite output window with nonnegative weights and nonnegative inverse
normalizer, if each integrable scalar certificate `A i` is almost everywhere
bounded by `c * B i`, then its normalized weighted expected certificate is
bounded by `c` times the normalized weighted expected certificate of `B`.

Layer: Model | Concept: Stationarity certificate expectation API
Target home: `SOptLib/Model/Stationarity.lean`, adjacent to
  `normalizedWeightedExpectedCertificate`
Proof: apply `MeasureTheory.integral_mono_ae` in each fiber, multiply by the
  nonnegative finite-window weights, sum the inequalities, scale by the
  nonnegative inverse denominator, and pull the constant through the finite sum.
Source: Mathlib Bochner integral monotonicity, finite-sum order APIs, and real
  scalar algebra
Used in: randomized stochastic proximal output stationarity-certificate
  expectation bound
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem normalizedWeightedExpectedCertificate_le_const_mul
    {ι Ω : Type*} [MeasurableSpace Ω]
    (times : Finset ι) (denom c : ℝ) (w : ι → ℝ)
    (μ : Measure Ω) (A B : ι → Ω → ℝ)
    (hdenom_inv_nonneg : 0 ≤ denom⁻¹)
    (hw_nonneg : ∀ i, i ∈ times → 0 ≤ w i)
    (hA_int : ∀ i, i ∈ times → Integrable (A i) μ)
    (hB_int : ∀ i, i ∈ times → Integrable (B i) μ)
    (hpoint : ∀ i, i ∈ times → ∀ᵐ ω ∂μ, A i ω ≤ c * B i ω) :
    normalizedWeightedExpectedCertificate times denom w μ A ≤
      c * normalizedWeightedExpectedCertificate times denom w μ B := by
  classical
  have hint :
      ∀ i, i ∈ times →
        (∫ ω, A i ω ∂μ) ≤ ∫ ω, c * B i ω ∂μ := by
    intro i hi
    exact MeasureTheory.integral_mono_ae
      (hA_int i hi)
      ((hB_int i hi).const_mul c)
      (hpoint i hi)
  have hterm :
      ∀ i, i ∈ times →
        w i * (∫ ω, A i ω ∂μ) ≤
          w i * ∫ ω, c * B i ω ∂μ := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (hint i hi) (hw_nonneg i hi)
  have hsum :
      Finset.sum times (fun i => w i * (∫ ω, A i ω ∂μ)) ≤
        Finset.sum times (fun i => w i * ∫ ω, c * B i ω ∂μ) :=
    Finset.sum_le_sum hterm
  rw [normalizedWeightedExpectedCertificate_def]
  calc
    denom⁻¹ * Finset.sum times (fun i => w i * ∫ ω, A i ω ∂μ) ≤
        denom⁻¹ * Finset.sum times (fun i => w i * ∫ ω, c * B i ω ∂μ) :=
      mul_le_mul_of_nonneg_left hsum hdenom_inv_nonneg
    _ = c * (denom⁻¹ * Finset.sum times (fun i => w i * ∫ ω, B i ω ∂μ)) := by
      simp [MeasureTheory.integral_const_mul]
      calc
        denom⁻¹ * Finset.sum times (fun i => w i * (c * ∫ ω, B i ω ∂μ)) =
            denom⁻¹ * Finset.sum times (fun i => c * (w i * ∫ ω, B i ω ∂μ)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
        _ = denom⁻¹ * (c * Finset.sum times (fun i => w i * ∫ ω, B i ω ∂μ)) := by
          exact congrArg (fun t => denom⁻¹ * t)
            (Finset.mul_sum (s := times) (f := fun i => w i * ∫ ω, B i ω ∂μ) c).symm
        _ = c * (denom⁻¹ * Finset.sum times (fun i => w i * ∫ ω, B i ω ∂μ)) := by
          ring

/-- A one-based finite selected-output expectation expands from selector atoms.

If the selected-index law on `{1, ..., N}` assigns singleton real mass
`weight k / denom`, then the selector-first product expectation of a real
observable is `denom⁻¹` times the raw weighted sum of its fiber expectations.

Layer: Model | Gap: Level 1 (law-abstract selected-output expectation expansion)
Proof: swap the selector-first product integral, apply the finite selected-index
  product expansion using singleton real masses, reindex the subtype over
  `Finset.Icc 1 N`, and factor the inverse denominator through the finite sum.
Source: Mathlib product-measure Bochner integration, finite subtype sums, and
  real field normalization APIs
Used in: stochastic nonconvex conditional-gradient randomized Wolfe-gap
  expectation after constructing the output law separately
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem expectedSelectedOutput_eq_inv_mul_Icc_weighted_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (N : ℕ) (weight : ℕ → ℝ) (denom : ℝ)
    (P : Measure Ω) [SFinite P]
    (ν : Measure {k : ℕ // k ∈ Finset.Icc 1 N})
    [IsFiniteMeasure ν]
    (score : ℕ → Ω → ℝ)
    (hν_singleton :
      ∀ R : {k : ℕ // k ∈ Finset.Icc 1 N},
        ν.real ({R} : Set {k : ℕ // k ∈ Finset.Icc 1 N}) =
          weight R.1 / denom)
    (hden_ne : denom ≠ 0)
    (hscore_int :
      ∀ R : {k : ℕ // k ∈ Finset.Icc 1 N},
        Integrable (score R.1) P) :
    ∫ q : {k : ℕ // k ∈ Finset.Icc 1 N} × Ω,
        score q.1.1 q.2 ∂(ν.prod P) =
      denom⁻¹ *
        Finset.sum (Finset.Icc 1 N)
          (fun k => weight k * ∫ ω, score k ω ∂P) := by
  classical
  let times : Finset ℕ := Finset.Icc 1 N
  let ι : Type := {k : ℕ // k ∈ times}
  let p : ι → ℝ := fun R => weight R.1 / denom
  have hprod :
      ∫ q : ι × Ω, score q.1.1 q.2 ∂(ν.prod P) =
        Finset.sum Finset.univ
          (fun R : ι => p R * ∫ ω, score R.1 ω ∂P) := by
    have hswap :
        ∫ q : ι × Ω, score q.1.1 q.2 ∂(ν.prod P) =
          ∫ q : Ω × ι, score q.2.1 q.1 ∂(P.prod ν) := by
      simpa [ι, times] using
        (MeasureTheory.integral_prod_swap (μ := P) (ν := ν)
          (f := fun q : Ω × {k : ℕ // k ∈ Finset.Icc 1 N} =>
            score q.2.1 q.1))
    rw [hswap]
    exact integral_selected_finite_index_prod_eq_sum_weights
      (μ := P) (ν := ν) (p := p)
      (F := fun R : ι => fun ω => score R.1 ω)
      (by simpa [ι, times, p] using hν_singleton)
      (by simpa [ι, times] using hscore_int)
  have hreindex :
      Finset.sum Finset.univ
          (fun R : ι => p R * ∫ ω, score R.1 ω ∂P) =
        Finset.sum times
          (fun k => (weight k / denom) * ∫ ω, score k ω ∂P) := by
    simpa [ι, p] using
      (Finset.sum_attach (s := times)
        (f := fun k => (weight k / denom) * ∫ ω, score k ω ∂P))
  calc
    ∫ q : {k : ℕ // k ∈ Finset.Icc 1 N} × Ω,
        score q.1.1 q.2 ∂(ν.prod P)
        = Finset.sum times
            (fun k => (weight k / denom) * ∫ ω, score k ω ∂P) := by
          simpa [times, ι] using hprod.trans hreindex
    _ = Finset.sum times
            (fun k => denom⁻¹ * (weight k * ∫ ω, score k ω ∂P)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          field_simp [hden_ne]
    _ = denom⁻¹ *
        Finset.sum times
          (fun k => weight k * ∫ ω, score k ω ∂P) := by
          rw [Finset.mul_sum]
    _ = denom⁻¹ *
        Finset.sum (Finset.Icc 1 N)
          (fun k => weight k * ∫ ω, score k ω ∂P) := by
          simp [times]

end SOptLib

namespace SOptLib

/-- The expected root of the finite sum of squared certificate norms.

This is the expected pathwise `ℓ²` energy of a finite certificate process; the
square root is taken before integration.

Layer: Model | Concept: finite-horizon expected certificate root energy
Proof: (definitional construction; Bochner integral of the square root of a finite squared-norm sum)
Source: Mathlib finite sums, normed-group norms, real square roots, and Bochner integration
Used in: finite-horizon stationarity analyses before Cauchy--Schwarz and self-normalized root-energy bounds
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/19
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
noncomputable def expectedRootSumSqNorm
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (μ : Measure Ω) (certificate : ι → Ω → E) : ℝ :=
  ∫ ω, Real.sqrt (Finset.sum times (fun i => ‖certificate i ω‖ ^ 2)) ∂μ

/-- The expected finite-horizon certificate root energy unfolds to its defining integral.

Layer: Model | Gap: Level 0 (expected finite certificate root-energy unfolding)
Proof: by rfl after unfolding `expectedRootSumSqNorm`.
Source: Mathlib finite sums, normed-group norms, real square roots, and Bochner integration
Used in: specializing abstract certificate root energy to objective-gradient trajectories in recursive-momentum stationarity proofs
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/19
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
@[simp]
theorem expectedRootSumSqNorm_def
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (μ : Measure Ω) (certificate : ι → Ω → E) :
    expectedRootSumSqNorm times μ certificate =
      ∫ ω, Real.sqrt (Finset.sum times (fun i => ‖certificate i ω‖ ^ 2)) ∂μ := by
  rfl

/-- The expected root of a finite sum of squared certificate norms is nonnegative.

Layer: Model | Gap: Level 0 (expected finite certificate root-energy nonnegativity)
Proof: the square root is pointwise nonnegative, so its Bochner integral is nonnegative.
Source: Mathlib Bochner integral nonnegativity and real square-root nonnegativity
Used in: scalar absorption and case splits for finite-horizon stationarity bounds
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/19
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem expectedRootSumSqNorm_nonneg
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (μ : Measure Ω) (certificate : ι → Ω → E) :
    0 ≤ expectedRootSumSqNorm times μ certificate := by
  rw [expectedRootSumSqNorm_def]
  exact integral_nonneg (fun _ => Real.sqrt_nonneg _)

/-- The expected finite sum of random weights times squared certificate norms.

The weights may depend on the same sample as the certificate, so the weighted
sum is formed pointwise before integration.

Layer: Model | Concept: randomly weighted expected certificate energy
Proof: (definitional construction; Bochner integral of a finite sum of sample-dependent weights times squared norms)
Source: Mathlib finite sums, normed-type norms, and Bochner integration of real observables
Used in: adaptive stochastic-gradient and recursive-momentum telescope bounds for randomly step-size-weighted stationarity certificates
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/14
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
noncomputable def expected_weighted_certificate_energy
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (μ : Measure Ω) (weight : ι → Ω → ℝ)
    (certificate : ι → Ω → E) : ℝ :=
  ∫ ω, Finset.sum times (fun i => weight i ω * ‖certificate i ω‖ ^ 2) ∂μ

/-- The randomly weighted expected certificate energy unfolds to its defining integral.

Layer: Model | Gap: Level 0 (randomly weighted expected certificate-energy unfolding)
Proof: by rfl after unfolding `expected_weighted_certificate_energy`.
Source: Mathlib finite sums, normed-type norms, and Bochner integration of real observables
Used in: specializing an abstract randomly weighted energy to adaptive stepsizes and objective-gradient trajectories
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/14
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
@[simp]
theorem expected_weighted_certificate_energy_def
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (μ : Measure Ω) (weight : ι → Ω → ℝ)
    (certificate : ι → Ω → E) :
    expected_weighted_certificate_energy times μ weight certificate =
      ∫ ω, Finset.sum times
        (fun i => weight i ω * ‖certificate i ω‖ ^ 2) ∂μ := by
  rfl

/-- The expected weighted squared-norm energy is nonnegative when every weight
is nonnegative almost everywhere.

Layer: Model | Gap: Level 0 (randomly weighted expected certificate-energy nonnegativity)
Proof: combine the finite family of a.e. weight bounds, then apply Bochner-integral nonnegativity to the resulting a.e. nonnegative sum.
Source: Mathlib `Finset.eventually_all`, `Finset.sum_nonneg`, norm-square nonnegativity, and `MeasureTheory.integral_nonneg_of_ae`
Used in: adaptive stochastic-method energy estimates before division, scaling, and telescope-bound composition
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/14
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem expected_weighted_certificate_energy_nonneg
    {ι Ω E : Type*} [MeasurableSpace Ω] [Norm E]
    (times : Finset ι) (μ : Measure Ω) (weight : ι → Ω → ℝ)
    (certificate : ι → Ω → E)
    (hweight : ∀ i ∈ times, ∀ᵐ ω ∂μ, 0 ≤ weight i ω) :
    0 ≤ expected_weighted_certificate_energy times μ weight certificate := by
  rw [expected_weighted_certificate_energy_def]
  refine integral_nonneg_of_ae ?_
  filter_upwards [times.eventually_all.2 hweight] with ω hweightω
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (hweightω i hi) (sq_nonneg _)

end SOptLib

/-- A scalar upper certificate gives the negative reversed-displacement bound.

If `m` is bounded above by the inner product in the `x - y` orientation,
then the reversed displacement has value at most `-m`.

Layer: Model | Gap: Level 0 (inner-product sign orientation)
Proof: rewrite the reversed displacement as a negated difference, use
  `inner_neg_right`, and negate the scalar upper certificate.
Source: Real Hilbert-space inner-product algebra and ordered additive groups
Used in: stochastic nonconvex conditional-gradient one-step Wolfe-gap descent
  after the linear minimization oracle comparison
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem inner_sub_le_neg_of_le_inner_sub
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G x y : E) (m : ℝ)
    (hm : m ≤ ⟪G, x - y⟫_ℝ) :
    ⟪G, y - x⟫_ℝ ≤ -m := by
  calc
    ⟪G, y - x⟫_ℝ = -⟪G, x - y⟫_ℝ := by
      rw [← neg_sub x y, inner_neg_right]
    _ ≤ -m := by
      exact neg_le_neg hm

namespace SOptLib

/-- Deterministic approximate stationary solution with a feasible nearby witness.

For a feasible set `X`, a stationarity gap on feasible points, tolerances `ε`
and `δ`, and an output `x`, this records that `x` is feasible and has a feasible
witness `xHat` whose squared stationarity gap is at most `ε` and whose squared
distance from `x` is at most `δ`.

Layer: Model | Concept: Stationarity
Proof: (definitional construction; deterministic feasibility and squared
  stationarity/proximity certificate predicate)
Source: variational-analysis stationarity residuals and Mathlib normed-space APIs
Used in: randomized accelerated proximal-point deterministic stationarity
  certificate before passing to stochastic selected-output guarantees
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
def ApproximateStationarySolution
    {E : Type*} [NormedAddCommGroup E] (X : Set E) (gap : {x : E // x ∈ X} → ℝ)
    (ε δ : ℝ) (x : E) : Prop :=
  x ∈ X ∧ ∃ xHat, ∃ hxHat : xHat ∈ X,
    gap ⟨xHat, hxHat⟩ ^ 2 ≤ ε ∧ ‖x - xHat‖ ^ 2 ≤ δ

/-- The deterministic approximate-stationary-solution predicate unfolds to
feasibility, a feasible witness, and the two squared certificate bounds.

Layer: Model | Gap: Level 0 (approximate-stationary-solution unfolding)
Proof: by rfl after unfolding `ApproximateStationarySolution`.
Source: variational-analysis stationarity residuals and Mathlib normed-space APIs
Used in: randomized accelerated proximal-point deterministic stationarity
  certificate before passing to stochastic selected-output guarantees
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
@[simp]
theorem ApproximateStationarySolution_def
    {E : Type*} [NormedAddCommGroup E] (X : Set E) (gap : {x : E // x ∈ X} → ℝ)
    (ε δ : ℝ) (x : E) :
    ApproximateStationarySolution X gap ε δ x =
      (x ∈ X ∧ ∃ xHat, ∃ hxHat : xHat ∈ X,
        gap ⟨xHat, hxHat⟩ ^ 2 ≤ ε ∧ ‖x - xHat‖ ^ 2 ≤ δ) := by
  rfl

/-- A deterministic approximate stationary solution is feasible.

Layer: Model | Gap: Level 0 (approximate-stationary-solution feasibility)
Proof: project the first conjunct of the definitional certificate.
Source: variational-analysis stationarity residuals and Mathlib normed-space APIs
Used in: randomized accelerated proximal-point extraction of feasible selected
  outputs from approximate-stationarity certificates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem ApproximateStationarySolution.mem
    {E : Type*} [NormedAddCommGroup E] {X : Set E}
    {gap : {x : E // x ∈ X} → ℝ} {ε δ : ℝ} {x : E} :
    ApproximateStationarySolution X gap ε δ x → x ∈ X := by
  intro h
  exact h.1

/-- The normal cone of a set `X` at a point `x` as variational inequalities.

This names the standard set-valued object
`{v | ∀ y ∈ X, ⟪v, y - x⟫ ≤ 0}` used in constrained stationarity
certificates.

Layer: Model | Concept: Stationarity
Proof: (definitional construction; affine normal-cone wrapper by inner-product
  variational inequalities)
Source: variational analysis normal-cone definitions in real Hilbert spaces and
  Mathlib inner-product set notation
Used in: constrained proximal-point stationarity certificates and normal-cone
  distance residuals
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
def normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (x : E) : Set E :=
  {v : E | ∀ y ∈ X, ⟪v, y - x⟫_ℝ ≤ 0}

/-- The normal cone is the set of vectors satisfying the defining variational inequality.

Layer: Model | Gap: Level 0 (normal-cone set unfolding)
Proof: by rfl after unfolding `normalCone`.
Source: variational analysis normal-cone definitions in real Hilbert spaces and
  Mathlib inner-product set notation
Used in: constrained proximal-point stationarity certificates and normal-cone
  distance residuals -/
@[simp]
theorem normalCone_def {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (x : E) :
    normalCone X x = {v : E | ∀ y ∈ X, ⟪v, y - x⟫_ℝ ≤ 0} := by
  rfl

/-- Membership in the normal cone is exactly the defining variational inequality.

Layer: Model | Gap: Level 0 (normal-cone membership unfolding)
Proof: by rfl after unfolding `normalCone`.
Source: variational analysis normal-cone definitions in real Hilbert spaces and
  Mathlib inner-product set notation
Used in: constrained proximal-point stationarity certificates and normal-cone
  distance residuals
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem mem_normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {x v : E} :
    v ∈ normalCone X x ↔ ∀ y ∈ X, ⟪v, y - x⟫_ℝ ≤ 0 := by
  rfl

/-- The zero vector belongs to every normal cone.

Layer: Model | Gap: Level 0 (normal-cone algebra API)
Proof: unfold membership and simplify the zero inner product.
Source: variational analysis normal-cone definitions in real Hilbert spaces and
  Mathlib inner-product set notation
Used in: constrained proximal-point stationarity certificates and normal-cone
  distance residuals -/
theorem zero_mem_normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (x : E) :
    (0 : E) ∈ normalCone X x := by
  rw [mem_normalCone]
  intro y hy
  simp

/-- Normal cones are closed under addition.

Layer: Model | Gap: Level 0 (normal-cone algebra API)
Proof: unfold membership and add the two variational inequalities.
Source: variational analysis normal-cone definitions in real Hilbert spaces and
  Mathlib inner-product set notation
Used in: constrained proximal-point stationarity certificates and normal-cone
  distance residuals -/
theorem add_mem_normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {x v w : E} (hv : v ∈ normalCone X x) (hw : w ∈ normalCone X x) :
    v + w ∈ normalCone X x := by
  rw [mem_normalCone] at hv hw ⊢
  intro y hy
  simpa [inner_add_left] using add_nonpos (hv y hy) (hw y hy)

/-- Normal cones are closed under multiplication by nonnegative scalars.

Layer: Model | Gap: Level 0 (normal-cone algebra API)
Proof: unfold membership and scale the variational inequality by a nonnegative scalar.
Source: variational analysis normal-cone definitions in real Hilbert spaces and
  Mathlib inner-product set notation
Used in: constrained proximal-point stationarity certificates and normal-cone
  distance residuals -/
theorem smul_mem_normalCone_of_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {X : Set E} {x v : E} {c : ℝ} (hc : 0 ≤ c)
    (hv : v ∈ normalCone X x) :
    c • v ∈ normalCone X x := by
  rw [mem_normalCone] at hv ⊢
  intro y hy
  simpa [real_inner_smul_left] using mul_nonpos_of_nonneg_of_nonpos hc (hv y hy)

/-- The normal cone is antitone in the carrier set.

Layer: Model | Gap: Level 0 (normal-cone carrier API)
Proof: unfold membership and restrict the quantified carrier point.
Source: variational analysis normal-cone definitions in real Hilbert spaces and
  Mathlib inner-product set notation
Used in: constrained proximal-point stationarity certificates and normal-cone
  distance residuals -/
theorem normalCone_antitone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X Y : Set E} (hXY : X ⊆ Y) (x : E) :
    normalCone Y x ⊆ normalCone X x := by
  intro v hv
  rw [mem_normalCone] at hv ⊢
  intro y hy
  exact hv y (hXY hy)

/-- Distance from a gradient-like vector to the negative normal cone of a set.

For a feasible set `X`, point `x`, and first-order certificate `grad`, this names
the constrained stationarity residual `dist(grad, -N_X(x))` using Mathlib's
distance-to-set primitive.

Layer: Model | Concept: Stationarity
Proof: (definitional construction; distance-to-set wrapper for the negative
  normal cone built from variational inequalities)
Source: variational analysis normal-cone stationarity residuals in real Hilbert
  spaces and Mathlib metric distance-to-set APIs
Used in: constrained proximal-point stationarity certificates and
  distance-to-negative-normal-cone residual bounds
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def normalConeStationarityGap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (grad x : E) : ℝ :=
  Metric.infDist grad {v : E | -v ∈ normalCone X x}

/-- The normal-cone stationarity gap unfolds to the distance from `grad` to `-N_X(x)`.

Layer: Model | Gap: Level 0 (normal-cone stationarity-gap unfolding)
Proof: by rfl after unfolding `normalConeStationarityGap`.
Source: variational analysis normal-cone stationarity residuals in real Hilbert
  spaces and Mathlib metric distance-to-set APIs
Used in: constrained proximal-point stationarity certificates and
  distance-to-negative-normal-cone residual bounds
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem normalConeStationarityGap_def {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (grad x : E) :
    normalConeStationarityGap X grad x =
      Metric.infDist grad {v : E | -v ∈ normalCone X x} := by
  rfl

/-- The normal-cone stationarity gap is nonnegative.

Layer: Model | Gap: Level 0 (normal-cone stationarity-gap nonnegativity)
Proof: immediate from Mathlib's nonnegativity of distance to a set.
Source: variational analysis normal-cone stationarity residuals in real Hilbert
  spaces and Mathlib metric distance-to-set APIs
Used in: squaring stationarity-gap bounds from normal-cone certificates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem normalConeStationarityGap_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (grad x : E) :
    0 ≤ normalConeStationarityGap X grad x := by
  simpa [normalConeStationarityGap] using
    (Metric.infDist_nonneg (x := grad) (s := {v : E | -v ∈ normalCone X x}))

/-- The normal-cone stationarity gap is bounded by the distance to any certificate
in the negative normal cone.

Layer: Model | Gap: Level 0 (normal-cone stationarity-gap certificate bound)
Proof: immediate from Mathlib's distance-to-set bound by any member.
Source: variational analysis normal-cone stationarity residuals in real Hilbert
  spaces and Mathlib metric distance-to-set APIs
Used in: converting first-order optimality certificates into stationarity bounds
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem normalConeStationarityGap_le_dist_of_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (grad x G : E)
    (hG : G ∈ {v : E | -v ∈ normalCone X x}) :
    normalConeStationarityGap X grad x ≤ dist grad G := by
  simpa [normalConeStationarityGap] using
    (Metric.infDist_le_dist_of_mem (x := grad)
      (s := {v : E | -v ∈ normalCone X x}) hG)

/-- Squared normal-cone stationarity-gap integrand for a random candidate.

For a feasible set `X`, stationarity gap `gapOn` defined on feasible points, and
random candidate `xHat`, this names the pointwise observable that evaluates the
squared feasible stationarity gap and uses `0` outside the feasible set.

Layer: Model | Concept: Stationarity
Proof: (definitional construction; pointwise squared stationarity-gap observable
  with an outside-feasible fallback)
Source: stochastic constrained optimization stationarity criteria and Mathlib
  subtype/set membership APIs
Used in: randomized accelerated proximal-point final expected stationarity
  criterion and stochastic constrained-method output certification
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
noncomputable def normalConeStationarityGapIntegrand
    {Ω E : Type*}
    (X : Set E) (gapOn : {x : E // x ∈ X} → ℝ) (xHat : Ω → E) : Ω → ℝ := by
  classical
  exact fun ω =>
    (if hxω : xHat ω ∈ X then
      gapOn ⟨xHat ω, hxω⟩
    else 0) ^ 2

/-- The squared normal-cone stationarity-gap integrand unfolds to its
outside-feasible fallback formula.

Layer: Model | Gap: Level 0 (normal-cone stationarity-gap integrand unfolding)
Proof: by rfl after unfolding `normalConeStationarityGapIntegrand`.
Source: stochastic constrained optimization stationarity criteria and Mathlib
  subtype/set membership APIs
Used in: randomized accelerated proximal-point final expected stationarity
  criterion and stochastic constrained-method output certification
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem normalConeStationarityGapIntegrand_def
    {Ω E : Type*}
    (X : Set E) (gapOn : {x : E // x ∈ X} → ℝ) (xHat : Ω → E) : by
    classical
    exact
    normalConeStationarityGapIntegrand X gapOn xHat =
      (fun ω =>
        (if hxω : xHat ω ∈ X then
          gapOn ⟨xHat ω, hxω⟩
        else 0) ^ 2) := by
  rfl

/-- The squared normal-cone stationarity-gap integrand is pointwise
nonnegative.

Layer: Model | Gap: Level 0 (normal-cone stationarity-gap integrand
nonnegativity)
Proof: unfold `normalConeStationarityGapIntegrand` and use `sq_nonneg`.
Source: stochastic constrained optimization stationarity criteria and Mathlib
ordered-ring APIs
Used in: stochastic constrained-method output certification and expectation
nonnegativity arguments
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
Machine Learning, randomized accelerated proximal-point method -/
theorem normalConeStationarityGapIntegrand_nonneg
    {Ω E : Type*}
    (X : Set E) (gapOn : {x : E // x ∈ X} → ℝ) (xHat : Ω → E) (ω : Ω) :
    0 ≤ normalConeStationarityGapIntegrand X gapOn xHat ω := by
  classical
  by_cases hxω : xHat ω ∈ X
  · simpa [normalConeStationarityGapIntegrand, hxω] using
      (sq_nonneg (gapOn ⟨xHat ω, hxω⟩))
  · simp [normalConeStationarityGapIntegrand, hxω]

/-- The pointwise squared distance between an output process and its certificate process.

This observable is the canonical proximity term used in stochastic approximate-solution
criteria before integrating against the sampling law.

Layer: Model | Concept: Objective
Proof: (definitional construction; pointwise squared seminorm distance between two stochastic processes)
Source: Mathlib seminormed additive group APIs for subtraction and norms
Used in: randomized accelerated proximal-point stochastic approximate-solution proximity expectation
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized accelerated proximal-point method -/
noncomputable def squaredProximityIntegrand
    {Ω E : Type*} [SeminormedAddCommGroup E] (x xHat : Ω → E) : Ω → ℝ :=
  fun ω => ‖x ω - xHat ω‖ ^ 2

/-- The squared proximity integrand unfolds to the pointwise squared norm distance.

Layer: Model | Gap: Level 0 (squared proximity integrand unfolding)
Proof: by rfl after unfolding `squaredProximityIntegrand`.
Source: Mathlib seminormed additive group APIs for subtraction and norms
Used in: randomized accelerated proximal-point stochastic approximate-solution proximity expectation
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized accelerated proximal-point method -/
@[simp]
theorem squaredProximityIntegrand_def
    {Ω E : Type*} [SeminormedAddCommGroup E] (x xHat : Ω → E) :
    squaredProximityIntegrand x xHat = fun ω => ‖x ω - xHat ω‖ ^ 2 := by
  rfl

/-- The squared proximity integrand is pointwise nonnegative.

Layer: Model | Gap: Level 0 (squared proximity integrand nonnegativity)
Proof: unfold `squaredProximityIntegrand` and use nonnegativity of squares.
Source: Mathlib ordered-ring square nonnegativity
Used in: stochastic approximate-solution proximity expectation bounds
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized accelerated proximal-point method -/
theorem squaredProximityIntegrand_nonneg
    {Ω E : Type*} [SeminormedAddCommGroup E] (x xHat : Ω → E) (ω : Ω) :
    0 ≤ squaredProximityIntegrand x xHat ω := by
  exact sq_nonneg ‖x ω - xHat ω‖

/-- Stochastic approximate solution predicate with a feasible witness and two
expected squared certificate bounds.

For a feasible set `X`, a stationarity gap on feasible points, a sample law `μ`,
and random output/witness pair `x`, `xHat`, this records a.e. feasibility of both
random points together with integrability and expectation bounds for the squared
stationarity gap and squared output-witness distance.

Layer: Model | Concept: Stationarity
Proof: (definitional construction; stochastic feasibility and expected squared
  certificate predicate assembled from Bochner expectation and integrability)
Source: Mathlib measure theory Bochner expectation and normed-space APIs
Used in: randomized accelerated proximal-point final stochastic stationarity
  certificate after selecting the random outer iterate and feasible prox witness
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
noncomputable def StochasticApproximateSolution
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : Set E) (gapOn : {x : E // x ∈ X} → ℝ)
    (ε δ : ℝ) (x xHat : Ω → E) : Prop := by
  classical
  exact
    (∀ᵐ ω ∂μ, x ω ∈ X ∧ xHat ω ∈ X) ∧
      ∃ hstat : Integrable
          (fun ω =>
            (if hxω : xHat ω ∈ X then
              gapOn ⟨xHat ω, hxω⟩
            else 0) ^ 2) μ,
      ∃ hprox : Integrable (fun ω => ‖x ω - xHat ω‖ ^ 2) μ,
        expectation μ
            (fun ω =>
              (if hxω : xHat ω ∈ X then
                gapOn ⟨xHat ω, hxω⟩
              else 0) ^ 2) ≤ ε ∧
          expectation μ (fun ω => ‖x ω - xHat ω‖ ^ 2) ≤ δ

/-- The stochastic approximate-solution predicate unfolds to feasibility,
integrability, and the two expected squared certificate bounds. -/
@[simp] theorem StochasticApproximateSolution_def
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (X : Set E) (gapOn : {x : E // x ∈ X} → ℝ)
    (ε δ : ℝ) (x xHat : Ω → E) : by
    classical
    exact
    StochasticApproximateSolution μ X gapOn ε δ x xHat =
      ((∀ᵐ ω ∂μ, x ω ∈ X ∧ xHat ω ∈ X) ∧
        ∃ hstat : Integrable
            (fun ω =>
              (if hxω : xHat ω ∈ X then
                gapOn ⟨xHat ω, hxω⟩
              else 0) ^ 2) μ,
        ∃ hprox : Integrable (fun ω => ‖x ω - xHat ω‖ ^ 2) μ,
          expectation μ
              (fun ω =>
                (if hxω : xHat ω ∈ X then
                  gapOn ⟨xHat ω, hxω⟩
                else 0) ^ 2) ≤ ε ∧
            expectation μ (fun ω => ‖x ω - xHat ω‖ ^ 2) ≤ δ) := by
  rfl

/-- A stochastic approximate solution is a.e. feasible together with its witness. -/
theorem StochasticApproximateSolution.ae_mem
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Set E} {gapOn : {x : E // x ∈ X} → ℝ}
    {ε δ : ℝ} {x xHat : Ω → E}
    (h : StochasticApproximateSolution μ X gapOn ε δ x xHat) :
    ∀ᵐ ω ∂μ, x ω ∈ X ∧ xHat ω ∈ X :=
  h.1

/-- The output of a stochastic approximate solution is a.e. feasible. -/
theorem StochasticApproximateSolution.ae_output_mem
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Set E} {gapOn : {x : E // x ∈ X} → ℝ}
    {ε δ : ℝ} {x xHat : Ω → E}
    (h : StochasticApproximateSolution μ X gapOn ε δ x xHat) :
    ∀ᵐ ω ∂μ, x ω ∈ X :=
  h.ae_mem.mono fun _ hω => hω.1

/-- The witness of a stochastic approximate solution is a.e. feasible. -/
theorem StochasticApproximateSolution.ae_witness_mem
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Set E} {gapOn : {x : E // x ∈ X} → ℝ}
    {ε δ : ℝ} {x xHat : Ω → E}
    (h : StochasticApproximateSolution μ X gapOn ε δ x xHat) :
    ∀ᵐ ω ∂μ, xHat ω ∈ X :=
  h.ae_mem.mono fun _ hω => hω.2

/-- The squared stationarity certificate in a stochastic approximate solution is integrable. -/
theorem StochasticApproximateSolution.stationarity_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Set E} {gapOn : {x : E // x ∈ X} → ℝ}
    {ε δ : ℝ} {x xHat : Ω → E}
    (h : StochasticApproximateSolution μ X gapOn ε δ x xHat) : by
    classical
    exact
    Integrable
      (fun ω =>
        (if hxω : xHat ω ∈ X then
          gapOn ⟨xHat ω, hxω⟩
        else 0) ^ 2) μ := by
  classical
  rcases h.2 with ⟨hstat, _hprox, _hbound⟩
  exact hstat

/-- The squared output-witness distance in a stochastic approximate solution is integrable. -/
theorem StochasticApproximateSolution.proximity_integrable
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Set E} {gapOn : {x : E // x ∈ X} → ℝ}
    {ε δ : ℝ} {x xHat : Ω → E}
    (h : StochasticApproximateSolution μ X gapOn ε δ x xHat) :
    Integrable (fun ω => ‖x ω - xHat ω‖ ^ 2) μ := by
  rcases h.2 with ⟨_hstat, hprox, _hbound⟩
  exact hprox

/-- The expected squared stationarity certificate is bounded by `ε`. -/
theorem StochasticApproximateSolution.stationarity_expectation_le
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Set E} {gapOn : {x : E // x ∈ X} → ℝ}
    {ε δ : ℝ} {x xHat : Ω → E}
    (h : StochasticApproximateSolution μ X gapOn ε δ x xHat) : by
    classical
    exact
    expectation μ
        (fun ω =>
          (if hxω : xHat ω ∈ X then
            gapOn ⟨xHat ω, hxω⟩
          else 0) ^ 2) ≤ ε := by
  classical
  rcases h.2 with ⟨_hstat, _hprox, hstat_le, _hprox_le⟩
  exact hstat_le

/-- The expected squared output-witness distance is bounded by `δ`. -/
theorem StochasticApproximateSolution.proximity_expectation_le
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} {X : Set E} {gapOn : {x : E // x ∈ X} → ℝ}
    {ε δ : ℝ} {x xHat : Ω → E}
    (h : StochasticApproximateSolution μ X gapOn ε δ x xHat) :
    expectation μ (fun ω => ‖x ω - xHat ω‖ ^ 2) ≤ δ := by
  rcases h.2 with ⟨_hstat, _hprox, _hstat_le, hprox_le⟩
  exact hprox_le

end SOptLib

open scoped InnerProductSpace

namespace SOptLib

/-- An affine negative-normal-cone certificate bounds the squared normal-cone
stationarity gap.

If `grad + a • (x - c)` lies in the negative normal cone at `x`, then the
normal-cone stationarity gap of `grad` at `x` is at most the squared norm of the
affine displacement `a • (x - c)`.

Layer: Layer0 | Gap: Level 0 (affine normal-cone stationarity certificate)
Proof: use the certificate as the witness in the distance-to-negative-normal-cone
  bound, square the nonnegative distance inequality, and rewrite the witness
  distance by `dist_eq_norm` and `norm_smul`.
Source: variational analysis normal-cone stationarity residuals and Mathlib
  metric distance-to-set and normed-module scalar multiplication APIs
Used in: constrained proximal subproblem optimality converted into a squared
  stationarity residual bound by the previous-center displacement
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem normalConeGap_sq_le_sq_mul_norm_sub_sq_of_affine_certificate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (grad x c : E) (a : ℝ)
    (hcert : grad + a • (x - c) ∈ {v : E | -v ∈ normalCone X x}) :
    normalConeStationarityGap X grad x ^ 2 ≤ a ^ 2 * ‖x - c‖ ^ 2 := by
  have hgap_le :
      normalConeStationarityGap X grad x ≤ dist grad (grad + a • (x - c)) :=
    normalConeStationarityGap_le_dist_of_mem (X := X) (grad := grad) (x := x)
      (G := grad + a • (x - c)) hcert
  have hgap_nonneg : 0 ≤ normalConeStationarityGap X grad x :=
    normalConeStationarityGap_nonneg X grad x
  have hsq_le :
      normalConeStationarityGap X grad x ^ 2 ≤
        dist grad (grad + a • (x - c)) ^ 2 := by
    exact sq_le_sq.mpr
      (by
        rw [abs_of_nonneg hgap_nonneg,
          abs_of_nonneg (dist_nonneg : 0 ≤ dist grad (grad + a • (x - c)))]
        exact hgap_le)
  calc
    normalConeStationarityGap X grad x ^ 2
        ≤ dist grad (grad + a • (x - c)) ^ 2 := hsq_le
    _ = a ^ 2 * ‖x - c‖ ^ 2 := by
      rw [dist_eq_norm]
      have hsub : grad - (grad + a • (x - c)) = -(a • (x - c)) := by
        abel
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs]
      rw [mul_pow, sq_abs]

end SOptLib
