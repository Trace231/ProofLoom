import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Real.Sqrt
import SOptLib.Glue.Probability
import SOptLib.Model.ConditionalGradient

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
