import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SOptLib

/-- Total oracle calls for a two-phase method with repeated independent runs.

Given a run-count selector, an optimization-phase call selector, and a
validation-phase call selector, this packages the standard accounting identity:
each run pays the optimization calls plus the validation calls.

Layer: Model | Concept: Oracle
Proof: (definitional construction; natural-number product of run count and
  per-run optimization-plus-validation call counts)
Source: Mathlib natural-number arithmetic and stochastic optimization oracle-call
  accounting for two-phase methods
Used in: two-phase randomized stochastic mirror descent SFO complexity accounting
  for Theorem 6.7 parameter choices
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def oracleCallsForTwoPhaseChoices
    {ε ρ : Type*}
    (runs : ρ → ℕ)
    (optimizationCalls : ε → ℕ)
    (validationCalls : ε → ρ → ℕ)
    (eps : ε) (conf : ρ) : ℕ :=
  runs conf * (optimizationCalls eps + validationCalls eps conf)

/-- Closed-form logarithmic SFO rate for a two-phase stochastic method.

The rate records the three asymptotic terms from the two-phase analysis:
an optimization term proportional to `ε⁻¹ log₂(1/Λ)`, a variance term
proportional to `σ² ε⁻² log₂(1/Λ)`, and a validation term proportional to
`σ² (Λ ε)⁻¹ log₂(1/Λ)^2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; closed-form real-valued complexity rate with
  a base-two logarithmic confidence factor)
Source: Mathlib real logarithm, inverse, power, multiplication, and division
  APIs for closed-form asymptotic-rate expressions
Used in: two-phase randomized stochastic mirror descent SFO complexity rate for
  the optimization and validation phases
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def twoPhaseLogAsymptoticRate (σ ε Λ : ℝ) : ℝ :=
  ε⁻¹ * (Real.log (1 / Λ) / Real.log 2) +
    σ ^ 2 * ε⁻¹ ^ 2 * (Real.log (1 / Λ) / Real.log 2) +
      σ ^ 2 / (Λ * ε) * (Real.log (1 / Λ) / Real.log 2) ^ 2

/-- The closed-form two-phase logarithmic SFO rate is positive for `ε > 0`
and confidence level `Λ ∈ (0,1)`.

The first term is strictly positive because `ε⁻¹ > 0` and
`log₂(1/Λ) > 0`; the variance and validation terms are nonnegative squares.

Layer: Model | Gap: Level 0 (positivity of logarithmic two-phase complexity rate)
Proof: prove positivity of the base-two logarithmic factor from `Λ < 1`, show
  the remaining two summands are nonnegative by square nonnegativity, and close
  the ordered-ring inequality.
Source: Mathlib real logarithm, inverse positivity, square nonnegativity, and
  ordered-field arithmetic APIs
Used in: two-phase randomized stochastic mirror descent displayed SFO
  asymptotic-rate positivity for the optimization and validation phases
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/complexity
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem twoPhaseLogAsymptoticRate_pos
    (σ ε Λ : ℝ) (hε : 0 < ε) (hΛ_pos : 0 < Λ) (hΛ_lt : Λ < 1) :
    0 < twoPhaseLogAsymptoticRate σ ε Λ := by
  unfold twoPhaseLogAsymptoticRate
  have hlog_arg : 1 < 1 / Λ := by
    field_simp [ne_of_gt hΛ_pos]
    exact hΛ_lt
  have hlog_pos : 0 < Real.log (1 / Λ) / Real.log 2 :=
    div_pos (Real.log_pos hlog_arg) (Real.log_pos one_lt_two)
  have hε_inv_pos : 0 < ε⁻¹ := inv_pos.mpr hε
  have hσ_sq_nonneg : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hthird_nonneg :
      0 ≤ σ ^ 2 / (Λ * ε) *
        (Real.log (1 / Λ) / Real.log 2) ^ 2 := by
    exact mul_nonneg
      (div_nonneg hσ_sq_nonneg (le_of_lt (mul_pos hΛ_pos hε)))
      (sq_nonneg _)
  have hsecond_nonneg :
      0 ≤ σ ^ 2 * ε⁻¹ ^ 2 *
        (Real.log (1 / Λ) / Real.log 2) := by
    exact mul_nonneg
      (mul_nonneg hσ_sq_nonneg (sq_nonneg ε⁻¹))
      (le_of_lt hlog_pos)
  nlinarith [mul_pos hε_inv_pos hlog_pos]

/-- Displayed SFO call bound for a two-phase method with repeated independent runs.

The selector abstracts the paper-specific choices into a run-count function, an
optimization-phase budget, and a validation-phase budget indexed by the target
accuracy and confidence parameters.

Layer: Model | Concept: Oracle
Proof: (definitional construction; natural-number product of run count and per-run optimization-plus-validation SFO calls)
Source: Mathlib natural-number arithmetic and stochastic optimization oracle-call accounting for two-phase methods
Used in: two-phase randomized stochastic mirror descent displayed SFO call bound for Theorem 6.7 parameter choices
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def twoPhaseSFOCallBound
    {ε ρ : Type*}
    (runs : ρ → ℕ)
    (N : ε → ℕ)
    (T : ε → ρ → ℕ)
    (eps : ε) (conf : ρ) : ℕ :=
  runs conf * (N eps + T eps conf)

/-- The displayed two-phase SFO bound is the generic two-phase oracle-call accounting identity.

This bridges paper-facing notation for the displayed SFO bound to the reusable
oracle-call accounting wrapper used by the algorithm model.

Layer: Model | Gap: Level 0 (two-phase SFO accounting normalization)
Proof: by rfl after unfolding the displayed bound and the generic oracle-call accounting wrapper.
Source: Mathlib natural-number arithmetic and stochastic optimization oracle-call accounting for two-phase methods
Used in: two-phase randomized stochastic mirror descent comparison between paper SFO call notation and generic oracle-call accounting
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic mirror descent -/
theorem twoPhaseSFOCallBound_eq_oracleCallsForTwoPhaseChoices
    {ε ρ : Type*}
    (runs : ρ → ℕ)
    (N : ε → ℕ)
    (T : ε → ρ → ℕ)
    (eps : ε) (conf : ρ) :
    twoPhaseSFOCallBound runs N T eps conf =
      oracleCallsForTwoPhaseChoices runs N T eps conf := by
  rfl

/-- One-run finite-sum epoch call count with full refreshes and recursive batches.

Each epoch pays `refreshCalls` full-refresh oracle calls and
`batchSize * epochLength` recursive mini-batch calls; the number of epochs is
`ceil (iterations / epochLength)`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; natural-number epoch count multiplied by the
  full-refresh plus recursive mini-batch calls paid per epoch)
Source: Mathlib natural-number arithmetic, real casts, and ceiling APIs for
  finite-sum variance-reduced oracle-call accounting
Used in: finite-sum stochastic nonconvex conditional-gradient sliding SFO
  complexity accounting for epoch refreshes and recursive mini-batches
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/complexity
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
noncomputable def singlePhaseEpochCallCount
    (refreshCalls batchSize epochLength iterations : ℕ) : ℕ :=
  (refreshCalls + batchSize * epochLength) *
    Nat.ceil ((iterations : ℝ) / (epochLength : ℝ))

/-- The one-run finite-sum epoch call count unfolds to the full-refresh plus
recursive mini-batch formula.

Layer: Model | Gap: Level 0 (single-phase epoch call-count unfolding)
Proof: by rfl after unfolding `singlePhaseEpochCallCount`.
Source: Mathlib natural-number arithmetic, real casts, and ceiling APIs for
  finite-sum variance-reduced oracle-call accounting
Used in: finite-sum stochastic nonconvex conditional-gradient sliding SFO
  complexity accounting for epoch refreshes and recursive mini-batches
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/complexity
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
@[simp]
theorem singlePhaseEpochCallCount_def
    (refreshCalls batchSize epochLength iterations : ℕ) :
    singlePhaseEpochCallCount refreshCalls batchSize epochLength iterations =
      (refreshCalls + batchSize * epochLength) *
        Nat.ceil ((iterations : ℝ) / (epochLength : ℝ)) := by
  rfl

/-- The one-run finite-sum epoch call count is monotone in the iteration budget.

Layer: Model | Gap: Level 0 (single-phase epoch call-count monotonicity)
Proof: unfold the call count, compare real epoch ratios with the same
  nonnegative denominator, apply `Nat.ceil_mono`, and multiply by the fixed
  per-epoch cost.
Source: Mathlib natural-number arithmetic, real casts, division monotonicity,
  and natural ceiling monotonicity
Used in: finite-sum stochastic optimization complexity accounting when an
  iteration budget is rounded up or replaced by a larger sufficient budget -/
theorem singlePhaseEpochCallCount_mono_iterations
    (refreshCalls batchSize epochLength : ℕ) {iterations iterations' : ℕ}
    (hiterations : iterations ≤ iterations') :
    singlePhaseEpochCallCount refreshCalls batchSize epochLength iterations ≤
      singlePhaseEpochCallCount refreshCalls batchSize epochLength iterations' := by
  unfold singlePhaseEpochCallCount
  exact Nat.mul_le_mul_left
    (refreshCalls + batchSize * epochLength)
    (Nat.ceil_mono
      (div_le_div_of_nonneg_right
        (Nat.cast_le.mpr hiterations)
        (Nat.cast_nonneg epochLength)))

end SOptLib

-- Batch 2 promoted from Staging/epoch_call_count_le_sqrt_bound_of_epoch_sq_eq_refresh.lean
-- Generalization plan (G0):
-- concept/name: epoch_call_count_le_sqrt_bound_of_epoch_sq_eq_refresh exposes
--   the square-root epoch-budget bound for a finite-sum full-refresh plus
--   recursive-batch call count; orig was
--   singlePhaseEpochCallCount_le_sqrt_refresh_bound_of_batch_eq_const_mul_epoch,
--   renamed away from the paper-local stochastic-gradient-call context.
-- generality used: pure natural-number epoch accounting and real square-root
--   arithmetic; no carrier type, measure, independence, integrability,
--   convexity, smoothness, oracle, topology, or finite-dimensional hypotheses
--   are used.
-- portable call pattern: finite-sum variance-reduced SGD, SVRG/SAGA-style epoch
--   refresh analyses, and variance-reduced conditional-gradient proofs can
--   change `iterations`, `refreshCalls`, `epochLength`, and the fixed batch
--   ratio while preserving the same `(refresh + batch * epoch) * ceil(N/T)`
--   to square-root-budget step.
-- counterargument checked: this is not paper-local traceability because it is a
--   reusable arithmetic bridge from the named epoch call-count object to the
--   standard `N / sqrt(m) + 1` epoch complexity shape; it is not a pure wrapper
--   around Mathlib because it combines `Nat.ceil` overshoot, natural call-count
--   casts, and the epoch-square hypothesis.
-- coverage search: searched CATALOG.md, SOptLib, Staging, and the algorithm
--   source for `epoch`, `call count`, `sqrt`, `refresh`, `Nat.ceil`, and the
--   precise finite-sum epoch-count shape. The relevant hit
--   `SOptLib.singlePhaseEpochCallCount` is the named Model object this theorem
--   strengthens; `le_positive_ceil_max_one`, `natCast_max_one_ceil_le_add_two`,
--   and `budget_bound_le_half_of_budget_choice` cover different ceiling
--   patterns. LeanSearch returned Mathlib ceiling/sqrt primitives but no
--   duplicate packaged bound.
-- minimal hypotheses: all already minimal; the epoch-square equality is stated
--   over real casts because callers typically obtain it from a real
--   `epochLength = sqrt refreshCalls` parameter choice.


namespace SOptLib

/-- A square-root epoch choice gives the standard finite-sum epoch call-count bound.

If the epoch length squares to the full-refresh cost and each recursive
mini-batch has size `ratio * epochLength`, then the one-run epoch call count is
bounded by `(ratio + 1) * refreshCalls * (iterations / sqrt refreshCalls + 1)`.

Layer: Model | Gap: Level 1 (finite-sum epoch call-count square-root bound)
Proof: unfold the named epoch call-count object, bound the real natural ceiling
  by one unit of overshoot, rewrite the per-epoch cost using the square epoch
  hypothesis, and multiply by the nonnegative per-epoch cost.
Source: Mathlib real square-root, natural ceiling, real casts, and ordered-ring
  arithmetic APIs
Used in: finite-sum stochastic nonconvex conditional-gradient sliding SFO
  complexity accounting from epoch refreshes to the displayed square-root budget
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/complexity
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem epoch_call_count_le_sqrt_bound_of_epoch_sq_eq_refresh
    (iterations refreshCalls epochLength ratio : ℕ)
    (hepoch_sq : (epochLength : ℝ) ^ 2 = (refreshCalls : ℝ)) :
    (singlePhaseEpochCallCount refreshCalls (ratio * epochLength) epochLength iterations : ℝ) ≤
      ((ratio : ℝ) + 1) * (refreshCalls : ℝ) *
        ((iterations : ℝ) / Real.sqrt (refreshCalls : ℝ) + 1) := by
  have hsqrt_eq : Real.sqrt (refreshCalls : ℝ) = (epochLength : ℝ) := by
    rw [← hepoch_sq]
    exact Real.sqrt_sq (Nat.cast_nonneg epochLength)
  have hceil_arg_nonneg :
      0 ≤ (iterations : ℝ) / (epochLength : ℝ) := by
    exact div_nonneg (Nat.cast_nonneg iterations) (Nat.cast_nonneg epochLength)
  have hceil_le :
      (Nat.ceil ((iterations : ℝ) / (epochLength : ℝ)) : ℝ) ≤
        (iterations : ℝ) / (epochLength : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hceil_arg_nonneg)
  have hceil_le_sqrt :
      (Nat.ceil
          ((iterations : ℝ) / Real.sqrt (refreshCalls : ℝ)) : ℝ) ≤
        (iterations : ℝ) / Real.sqrt (refreshCalls : ℝ) + 1 := by
    simpa [hsqrt_eq] using hceil_le
  have hbase_eq :
      ((refreshCalls + (ratio * epochLength) * epochLength : ℕ) : ℝ) =
        ((ratio : ℝ) + 1) * (refreshCalls : ℝ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    calc
      (refreshCalls : ℝ) + ((ratio : ℝ) * (epochLength : ℝ)) * (epochLength : ℝ)
          = (refreshCalls : ℝ) + (ratio : ℝ) * ((epochLength : ℝ) ^ 2) := by
            ring
      _ = (refreshCalls : ℝ) + (ratio : ℝ) * (refreshCalls : ℝ) := by
            rw [hepoch_sq]
      _ = ((ratio : ℝ) + 1) * (refreshCalls : ℝ) := by
            ring
  have hbase_nonneg :
      0 ≤ ((ratio : ℝ) + 1) * (refreshCalls : ℝ) := by
    exact mul_nonneg (by positivity) (Nat.cast_nonneg refreshCalls)
  calc
    (singlePhaseEpochCallCount refreshCalls (ratio * epochLength) epochLength iterations : ℝ)
        =
          ((refreshCalls + (ratio * epochLength) * epochLength : ℕ) : ℝ) *
            (Nat.ceil ((iterations : ℝ) / (epochLength : ℝ)) : ℝ) := by
            rw [singlePhaseEpochCallCount_def, Nat.cast_mul]
    _ =
          (((ratio : ℝ) + 1) * (refreshCalls : ℝ)) *
            (Nat.ceil
              ((iterations : ℝ) / Real.sqrt (refreshCalls : ℝ)) : ℝ) := by
            rw [hbase_eq, hsqrt_eq]
    _ ≤
          (((ratio : ℝ) + 1) * (refreshCalls : ℝ)) *
            ((iterations : ℝ) / Real.sqrt (refreshCalls : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_left hceil_le_sqrt hbase_nonneg
    _ =
          ((ratio : ℝ) + 1) * (refreshCalls : ℝ) *
            ((iterations : ℝ) / Real.sqrt (refreshCalls : ℝ) + 1) := by
            ring


-- Generalization plan (G0):
-- concept/name: smooth finite-sum gradient-evaluation accuracy-split Big-O
--   predicate; orig was smoothGradientEvaluationPiecewiseBigO, renamed away
--   from paper-local setup fields while retaining the domain phrase
--   finite-sum gradient evaluation.
-- generality used: pure real scalar split parameters `m` and `D0`, an
--   accuracy-indexed call counter, and two caller-provided rate functions; no
--   carrier type, measure, independence, integrability, convexity,
--   smoothness/oracle proof, topology, normed vector space, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: smooth finite-sum accelerated-gradient,
--   SVRG/SARAH-style, and variance-reduced proximal-gradient complexity
--   proofs can vary the generated call counter, component count, initial
--   budget, and branch rate formulas while preserving the same two
--   principal-filter split by `m * epsilon >= D0`.
-- counterargument checked: this is not merely paper-local traceability because
--   it packages the recurring two-branch principal-filter Big-O envelope over
--   arbitrary branch rates; it is not covered by Mathlib, whose
--   `Asymptotics.isBigO_principal` and `isBigOWith_principal` are
--   single-branch primitives rather than a named finite-sum split predicate.
-- coverage search: searched CATALOG.md, SOptLib, Staging, registry, and the
--   algorithm file for finite-sum gradient evaluation, piecewise Big-O,
--   principal filter, and smooth finite-sum complexity; Mathlib LeanSearch
--   found `Asymptotics.isBigO_principal` and
--   `Asymptotics.isBigOWith_principal`, partial branch-level coverage only.
-- minimal hypotheses: all already minimal; branch-rate formulas and positivity
--   side conditions stay with callers, while the reusable predicate records
--   only the two filters and the two asymptotic comparisons.

/-- Two-branch smooth finite-sum component-gradient evaluation Big-O envelope.

The predicate records a call counter bounded on the principal branch
`m * epsilon >= D0` by `case1`, and on the complementary principal branch by
`case2`.

Layer: Model | Concept: Oracle
Proof: (definitional construction; two principal-filter Big-O conditions split
  by the finite-sum accuracy threshold)
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting for the smooth two-branch accuracy split
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def smoothFiniteSumGradientEvaluationPiecewiseBigO
    (m D0 : ℝ) (callsByAccuracy case1 case2 : ℝ -> ℝ) : Prop :=
  Asymptotics.IsBigO
      (Filter.principal {epsilon : ℝ | m * epsilon >= D0})
      callsByAccuracy case1 ∧
    Asymptotics.IsBigO
      (Filter.principal {epsilon : ℝ | ¬ m * epsilon >= D0})
      callsByAccuracy case2

/-- The two-branch smooth finite-sum envelope unfolds to its two principal-filter
Big-O conditions.

Layer: Model | Gap: Level 0 (finite-sum two-branch gradient-evaluation envelope unfolding)
Proof: by rfl after unfolding `smoothFiniteSumGradientEvaluationPiecewiseBigO`.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when the paper-local two-branch envelope is normalized to a
  reusable finite-sum predicate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem smoothFiniteSumGradientEvaluationPiecewiseBigO_def
    (m D0 : ℝ) (callsByAccuracy case1 case2 : ℝ -> ℝ) :
    smoothFiniteSumGradientEvaluationPiecewiseBigO
        m D0 callsByAccuracy case1 case2 =
      (Asymptotics.IsBigO
          (Filter.principal {epsilon : ℝ | m * epsilon >= D0})
          callsByAccuracy case1 ∧
        Asymptotics.IsBigO
          (Filter.principal {epsilon : ℝ | ¬ m * epsilon >= D0})
          callsByAccuracy case2) := by
  rfl

/-- First principal branch of the two-branch smooth finite-sum envelope.

Layer: Model | Gap: Level 0 (finite-sum two-branch envelope first projection)
Proof: project the left conjunct of the definitional envelope.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting on the `m * epsilon >= D0` branch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationPiecewiseBigO_first
    {m D0 : ℝ} {callsByAccuracy case1 case2 : ℝ -> ℝ}
    (h :
      smoothFiniteSumGradientEvaluationPiecewiseBigO
        m D0 callsByAccuracy case1 case2) :
    Asymptotics.IsBigO
      (Filter.principal {epsilon : ℝ | m * epsilon >= D0})
      callsByAccuracy case1 := by
  exact h.1

/-- Second principal branch of the two-branch smooth finite-sum envelope.

Layer: Model | Gap: Level 0 (finite-sum two-branch envelope second projection)
Proof: project the right conjunct of the definitional envelope.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting on the complement of `m * epsilon >= D0`
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationPiecewiseBigO_second
    {m D0 : ℝ} {callsByAccuracy case1 case2 : ℝ -> ℝ}
    (h :
      smoothFiniteSumGradientEvaluationPiecewiseBigO
        m D0 callsByAccuracy case1 case2) :
    Asymptotics.IsBigO
      (Filter.principal {epsilon : ℝ | ¬ m * epsilon >= D0})
      callsByAccuracy case2 := by
  exact h.2

/-- Assemble the two branch estimates into the smooth finite-sum envelope.

Layer: Model | Gap: Level 0 (finite-sum two-branch envelope introduction)
Proof: pair the two supplied branch estimates as the definitional conjunction.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting after pointwise bounds have been converted to branch Big-O
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationPiecewiseBigO_intro
    {m D0 : ℝ} {callsByAccuracy case1 case2 : ℝ -> ℝ}
    (h₁ :
      Asymptotics.IsBigO
        (Filter.principal {epsilon : ℝ | m * epsilon >= D0})
        callsByAccuracy case1)
    (h₂ :
      Asymptotics.IsBigO
        (Filter.principal {epsilon : ℝ | ¬ m * epsilon >= D0})
        callsByAccuracy case2) :
    smoothFiniteSumGradientEvaluationPiecewiseBigO
      m D0 callsByAccuracy case1 case2 := by
  exact ⟨h₁, h₂⟩

/-- The two-branch smooth finite-sum envelope is equivalent to its two branch
estimates.

Layer: Model | Gap: Level 0 (finite-sum two-branch envelope equivalence)
Proof: by rfl after unfolding the definitional conjunction.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when switching between named and unfolded branch predicates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationPiecewiseBigO_iff
    (m D0 : ℝ) (callsByAccuracy case1 case2 : ℝ -> ℝ) :
    smoothFiniteSumGradientEvaluationPiecewiseBigO
        m D0 callsByAccuracy case1 case2 ↔
      Asymptotics.IsBigO
        (Filter.principal {epsilon : ℝ | m * epsilon >= D0})
        callsByAccuracy case1 ∧
      Asymptotics.IsBigO
        (Filter.principal {epsilon : ℝ | ¬ m * epsilon >= D0})
        callsByAccuracy case2 := by
  rfl

-- Generalization plan (G0):
-- concept/name: smooth finite-sum gradient-evaluation piecewise Big-O envelope; orig was theorem59GradientEvaluationPiecewiseBigO, renamed away from theorem numbering and setup fields
-- generality used: real-valued component count `m`, average smoothness `L`, strong-convexity parameter `mu`, initial budget `D0`, and call counter `callsByAccuracy`; no carrier, measure, independence, integrability, convexity proof, oracle, topology, normed vector space, or finite-dimensional hypotheses are used
-- portable call pattern: finite-sum accelerated gradient, SVRG/SARAH-style strongly convex complexity proofs, and variance-reduced proximal-gradient analyses can change the call counter and parameters `m`, `L`, `mu`, and `D0` while preserving the same three branch predicates and closed-form rates
-- counterargument checked: this is not only paper-local traceability because the theorem-numbered setup has been removed and the result names the reusable three-regime finite-sum call-complexity envelope; it is not a one-line Mathlib wrapper, although each branch itself uses Mathlib `Asymptotics.IsBigO`
-- coverage search: searched CATALOG.md, SOptLib, Staging, registry, and the algorithm file for finite-sum gradient evaluation, piecewise Big-O, principal filter, and smooth finite-sum complexity; Mathlib LeanSearch found `Asymptotics.isBigO_principal` and `Asymptotics.isBigOWith_principal`, which are branch-level primitives but do not provide the three-regime finite-sum envelope
-- minimal hypotheses: all already minimal; the predicate only records asymptotic branch filters and rate formulas, so positivity assumptions on `mu` or `epsilon` are branch-side conditions rather than global hypotheses

/-- Three-regime finite-sum component-gradient evaluation Big-O envelope.

The predicate records the standard smooth strongly-convex finite-sum complexity
display with branches for the large-component, intermediate, and large
accuracy-ratio regimes.

Layer: Model | Concept: Oracle
Proof: (definitional construction; three branch filters paired with the
  closed-form finite-sum component-gradient rate functions)
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters, real logarithms, and square roots
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting for a generated accuracy-to-epoch selector
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
def smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO
    (m L mu D0 : ℝ) (callsByAccuracy : ℝ -> ℝ) : Prop :=
  Asymptotics.IsBigO
      (Filter.principal
        {epsilon : ℝ |
          0 < epsilon ∧
            (m >= D0 / epsilon ∨
              m >= 3 * L / (4 * mu))})
      callsByAccuracy
      (fun epsilon => m * Real.log (D0 / epsilon)) ∧
    Asymptotics.IsBigO
      (Filter.principal
        {epsilon : ℝ |
          0 < epsilon ∧
            ¬ (m >= D0 / epsilon ∨
                m >= 3 * L / (4 * mu)) ∧
              D0 / epsilon <= 3 * L / (4 * mu)})
      callsByAccuracy
      (fun epsilon => m * Real.log m + Real.sqrt (m * D0 / epsilon)) ∧
    Asymptotics.IsBigO
      (Filter.comap (fun epsilon : ℝ => D0 / epsilon)
          (Filter.atTop : Filter ℝ) ⊓
        Filter.principal
          {epsilon : ℝ |
            0 < epsilon ∧
              ¬ (m >= D0 / epsilon ∨
                  m >= 3 * L / (4 * mu)) ∧
                ¬ D0 / epsilon <= 3 * L / (4 * mu)})
      callsByAccuracy
      (fun epsilon =>
        m * Real.log m +
          Real.sqrt (m * L / mu) *
            Real.log ((D0 / epsilon) / (3 * L / (4 * mu))))

/-- The smooth finite-sum component-gradient envelope unfolds to its three
branch Big-O conditions.

Layer: Model | Gap: Level 0 (finite-sum gradient-evaluation envelope unfolding)
Proof: by rfl after unfolding `smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO`.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters, real logarithms, and square roots
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when a paper-local envelope is normalized to the reusable
  finite-sum predicate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_def
    (m L mu D0 : ℝ) (callsByAccuracy : ℝ -> ℝ) :
    smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO m L mu D0 callsByAccuracy =
      (Asymptotics.IsBigO
          (Filter.principal
            {epsilon : ℝ |
              0 < epsilon ∧
                (m >= D0 / epsilon ∨
                  m >= 3 * L / (4 * mu))})
          callsByAccuracy
          (fun epsilon => m * Real.log (D0 / epsilon)) ∧
        Asymptotics.IsBigO
          (Filter.principal
            {epsilon : ℝ |
              0 < epsilon ∧
                ¬ (m >= D0 / epsilon ∨
                    m >= 3 * L / (4 * mu)) ∧
                  D0 / epsilon <= 3 * L / (4 * mu)})
          callsByAccuracy
          (fun epsilon => m * Real.log m + Real.sqrt (m * D0 / epsilon)) ∧
        Asymptotics.IsBigO
          (Filter.comap (fun epsilon : ℝ => D0 / epsilon)
              (Filter.atTop : Filter ℝ) ⊓
            Filter.principal
              {epsilon : ℝ |
                0 < epsilon ∧
                  ¬ (m >= D0 / epsilon ∨
                      m >= 3 * L / (4 * mu)) ∧
                    ¬ D0 / epsilon <= 3 * L / (4 * mu)})
          callsByAccuracy
          (fun epsilon =>
            m * Real.log m +
              Real.sqrt (m * L / mu) *
                Real.log ((D0 / epsilon) / (3 * L / (4 * mu))))) := by
  rfl

/-- First branch of the three-regime smooth finite-sum component-gradient envelope.

Layer: Model | Gap: Level 0 (three-regime finite-sum envelope first projection)
Proof: project the first conjunct of the definitional three-regime envelope.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters, real logarithms, and square roots
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting on the large-component or large-accuracy branch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_first
    {m L mu D0 : ℝ} {callsByAccuracy : ℝ -> ℝ}
    (h :
      smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO
        m L mu D0 callsByAccuracy) :
    Asymptotics.IsBigO
      (Filter.principal
        {epsilon : ℝ |
          0 < epsilon ∧
            (m >= D0 / epsilon ∨
              m >= 3 * L / (4 * mu))})
      callsByAccuracy
      (fun epsilon => m * Real.log (D0 / epsilon)) := by
  exact h.1

/-- Second branch of the three-regime smooth finite-sum component-gradient envelope.

Layer: Model | Gap: Level 0 (three-regime finite-sum envelope second projection)
Proof: project the first conjunct of the tail pair in the definitional
  three-regime envelope.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters, real logarithms, and square roots
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting on the intermediate branch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_second
    {m L mu D0 : ℝ} {callsByAccuracy : ℝ -> ℝ}
    (h :
      smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO
        m L mu D0 callsByAccuracy) :
    Asymptotics.IsBigO
      (Filter.principal
        {epsilon : ℝ |
          0 < epsilon ∧
            ¬ (m >= D0 / epsilon ∨
                m >= 3 * L / (4 * mu)) ∧
              D0 / epsilon <= 3 * L / (4 * mu)})
      callsByAccuracy
      (fun epsilon => m * Real.log m + Real.sqrt (m * D0 / epsilon)) := by
  exact h.2.1

/-- Third, large accuracy-ratio branch of the three-regime smooth finite-sum envelope.

Layer: Model | Gap: Level 0 (three-regime finite-sum envelope tail projection)
Proof: project the second conjunct of the tail pair in the definitional
  three-regime envelope.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters, real logarithms, and square roots
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting on the large accuracy-ratio tail branch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_third
    {m L mu D0 : ℝ} {callsByAccuracy : ℝ -> ℝ}
    (h :
      smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO
        m L mu D0 callsByAccuracy) :
    Asymptotics.IsBigO
      (Filter.comap (fun epsilon : ℝ => D0 / epsilon)
          (Filter.atTop : Filter ℝ) ⊓
        Filter.principal
          {epsilon : ℝ |
            0 < epsilon ∧
              ¬ (m >= D0 / epsilon ∨
                  m >= 3 * L / (4 * mu)) ∧
                ¬ D0 / epsilon <= 3 * L / (4 * mu)})
      callsByAccuracy
      (fun epsilon =>
        m * Real.log m +
          Real.sqrt (m * L / mu) *
            Real.log ((D0 / epsilon) / (3 * L / (4 * mu)))) := by
  exact h.2.2

/-- Assemble the three branch estimates into the three-regime smooth finite-sum envelope.

Layer: Model | Gap: Level 0 (three-regime finite-sum envelope introduction)
Proof: pair the three supplied branch estimates as the definitional nested
  conjunction.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters, real logarithms, and square roots
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting after branch estimates have been proved separately
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_intro
    {m L mu D0 : ℝ} {callsByAccuracy : ℝ -> ℝ}
    (h₁ :
      Asymptotics.IsBigO
        (Filter.principal
          {epsilon : ℝ |
            0 < epsilon ∧
              (m >= D0 / epsilon ∨
                m >= 3 * L / (4 * mu))})
        callsByAccuracy
        (fun epsilon => m * Real.log (D0 / epsilon)))
    (h₂ :
      Asymptotics.IsBigO
        (Filter.principal
          {epsilon : ℝ |
            0 < epsilon ∧
              ¬ (m >= D0 / epsilon ∨
                  m >= 3 * L / (4 * mu)) ∧
                D0 / epsilon <= 3 * L / (4 * mu)})
        callsByAccuracy
        (fun epsilon => m * Real.log m + Real.sqrt (m * D0 / epsilon)))
    (h₃ :
      Asymptotics.IsBigO
        (Filter.comap (fun epsilon : ℝ => D0 / epsilon)
            (Filter.atTop : Filter ℝ) ⊓
          Filter.principal
            {epsilon : ℝ |
              0 < epsilon ∧
                ¬ (m >= D0 / epsilon ∨
                    m >= 3 * L / (4 * mu)) ∧
                  ¬ D0 / epsilon <= 3 * L / (4 * mu)})
        callsByAccuracy
        (fun epsilon =>
          m * Real.log m +
            Real.sqrt (m * L / mu) *
              Real.log ((D0 / epsilon) / (3 * L / (4 * mu))))) :
    smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO
      m L mu D0 callsByAccuracy := by
  exact ⟨h₁, h₂, h₃⟩

/-- The three-regime smooth finite-sum envelope is equivalent to its branch estimates.

Layer: Model | Gap: Level 0 (three-regime finite-sum envelope equivalence)
Proof: by rfl after unfolding the definitional nested conjunction.
Source: finite-sum variance-reduction complexity displays and Mathlib
  asymptotic Big-O filters, real logarithms, and square roots
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when switching between named and unfolded three-regime predicates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_iff
    (m L mu D0 : ℝ) (callsByAccuracy : ℝ -> ℝ) :
    smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO
        m L mu D0 callsByAccuracy ↔
      Asymptotics.IsBigO
        (Filter.principal
          {epsilon : ℝ |
            0 < epsilon ∧
              (m >= D0 / epsilon ∨
                m >= 3 * L / (4 * mu))})
        callsByAccuracy
        (fun epsilon => m * Real.log (D0 / epsilon)) ∧
      Asymptotics.IsBigO
        (Filter.principal
          {epsilon : ℝ |
            0 < epsilon ∧
              ¬ (m >= D0 / epsilon ∨
                  m >= 3 * L / (4 * mu)) ∧
                D0 / epsilon <= 3 * L / (4 * mu)})
        callsByAccuracy
        (fun epsilon => m * Real.log m + Real.sqrt (m * D0 / epsilon)) ∧
      Asymptotics.IsBigO
        (Filter.comap (fun epsilon : ℝ => D0 / epsilon)
            (Filter.atTop : Filter ℝ) ⊓
          Filter.principal
            {epsilon : ℝ |
              0 < epsilon ∧
                ¬ (m >= D0 / epsilon ∨
                    m >= 3 * L / (4 * mu)) ∧
                  ¬ D0 / epsilon <= 3 * L / (4 * mu)})
        callsByAccuracy
        (fun epsilon =>
          m * Real.log m +
            Real.sqrt (m * L / mu) *
              Real.log ((D0 / epsilon) / (3 * L / (4 * mu)))) := by
  rfl


/-- Pointwise bounds on a set and its complement give the corresponding
principal-filter Big-O bounds. -/
theorem isBigO_principal_and_compl_of_forall_norm_le
    {α E F₁ F₂ : Type*} [Norm E] [Norm F₁] [Norm F₂]
    (s : Set α) (f : α -> E) (g₁ : α -> F₁) (g₂ : α -> F₂) (C₁ C₂ : Real)
    (hs :
      forall x, x ∈ s -> ‖f x‖ <= C₁ * ‖g₁ x‖)
    (hcompl :
      forall x, x ∈ sᶜ -> ‖f x‖ <= C₂ * ‖g₂ x‖) :
    Asymptotics.IsBigO (Filter.principal s) f g₁ ∧
      Asymptotics.IsBigO (Filter.principal sᶜ) f g₂ := by
  exact ⟨
    (Asymptotics.isBigOWith_principal
      (c := C₁) (s := s) (f := f) (g := g₁)).2 hs |>.isBigO,
    (Asymptotics.isBigOWith_principal
      (c := C₂) (s := sᶜ) (f := f) (g := g₂)).2 hcompl |>.isBigO⟩


-- Generalization plan (G0):
-- concept/name: smooth finite-sum gradient-evaluation logarithmic rate; orig was
--   smoothGradientEvaluationCase1, renamed away from paper-local case numbering
--   and setup fields.
-- generality used: pure real scalar complexity parameters `m`, `epsilon`, and
--   `D0`; no carrier type, measure, independence, integrability, convexity,
--   smoothness proof, oracle model, topology, normed vector space, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: smooth finite-sum VR complexity corollaries, including
--   accelerated finite-sum gradient descent and SVRG/SARAH-style branch
--   analyses, can vary the component count `m`, initial gap/budget `D0`, and
--   target accuracy `epsilon` while preserving the logarithmic branch rate.
-- counterargument checked: the body is a single formula, but it is the named
--   first branch of a reusable finite-sum gradient-evaluation envelope rather
--   than paper-local traceability; it pairs with an unfolding theorem and
--   supports callers that want named rate functions inside Big-O goals.
-- coverage search: searched CATALOG.md, SOptLib, Staging, registry, and the
--   algorithm file for finite-sum gradient evaluation, log rate, logarithmic
--   branch, and `m * log (D0 / epsilon)`. Existing hits include
--   `SOptLib.smoothFiniteSumGradientEvaluationTwoBranchPiecewiseBigO`, whose first
--   branch can use this named rate, but no named reusable rate definition
--   covers the standalone branch.
-- minimal hypotheses: all already minimal; positivity of `epsilon` or `D0` is
--   a caller-side domain condition for estimates, not needed to name the rate.

/-- Logarithmic branch rate for smooth finite-sum component-gradient evaluations.

This names the first closed-form branch `m * log (D0 / epsilon)` that appears
when a smooth finite-sum variance-reduced complexity bound is in the
large-component or sufficiently-large-accuracy regime.

Layer: Model | Concept: Oracle
Proof: (definitional construction; closed-form real-valued finite-sum
  component-gradient rate with logarithmic accuracy ratio)
Source: finite-sum variance-reduction complexity displays and Mathlib real
  logarithm, multiplication, and division APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting for the logarithmic branch of the smooth finite-sum envelope
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def smoothFiniteSumGradientEvaluationLogRate
    (m epsilon D0 : Real) : Real :=
  m * Real.log (D0 / epsilon)

/-- The smooth finite-sum logarithmic gradient-evaluation rate unfolds to
`m * log (D0 / epsilon)`.

Layer: Model | Gap: Level 0 (finite-sum gradient-evaluation logarithmic rate formula)
Proof: by rfl after unfolding `smoothFiniteSumGradientEvaluationLogRate`.
Source: finite-sum variance-reduction complexity displays and Mathlib real
  logarithm, multiplication, and division APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when a paper-local branch formula is normalized to a reusable
  finite-sum rate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem smoothFiniteSumGradientEvaluationLogRate_def
    (m epsilon D0 : Real) :
    smoothFiniteSumGradientEvaluationLogRate m epsilon D0 =
      m * Real.log (D0 / epsilon) := by
  rfl

/-- The logarithmic finite-sum gradient-evaluation rate is nonnegative when
the component count is nonnegative and the accuracy ratio is at least one. -/
theorem smoothFiniteSumGradientEvaluationLogRate_nonneg
    {m epsilon D0 : ℝ} (hm : 0 ≤ m) (h_ratio : 1 ≤ D0 / epsilon) :
    0 ≤ smoothFiniteSumGradientEvaluationLogRate m epsilon D0 := by
  simpa [smoothFiniteSumGradientEvaluationLogRate] using
    mul_nonneg hm (Real.log_nonneg h_ratio)

/-- The first branch of the smooth finite-sum Big-O envelope can be read using
the named logarithmic rate. -/
theorem smoothFiniteSumGradientEvaluationTwoBranchPiecewiseBigO_first_logRate
    {m D0 : ℝ} {callsByAccuracy case2 : ℝ -> ℝ}
    (h :
      smoothFiniteSumGradientEvaluationPiecewiseBigO
        m D0 callsByAccuracy
        (fun epsilon => smoothFiniteSumGradientEvaluationLogRate m epsilon D0)
        case2) :
    Asymptotics.IsBigO
      (Filter.principal {epsilon : ℝ | m * epsilon >= D0})
      callsByAccuracy
      (fun epsilon => smoothFiniteSumGradientEvaluationLogRate m epsilon D0) := by
  exact smoothFiniteSumGradientEvaluationPiecewiseBigO_first (h := h)


-- Generalization plan (G0):
-- concept/name: smooth finite-sum gradient-evaluation square-root plus
--   logarithmic rate; orig was smoothGradientEvaluationCase2, renamed away
--   from paper-local case numbering and setup fields.
-- generality used: pure real scalar complexity parameters `m`, `epsilon`, and
--   `D0`; no carrier type, measure, independence, integrability, convexity,
--   smoothness proof, oracle model, topology, normed vector space, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: smooth finite-sum VR complexity corollaries, including
--   accelerated finite-sum gradient descent and SVRG/SARAH-style intermediate
--   branch analyses, can vary the component count `m`, initial gap/budget
--   `D0`, and target accuracy `epsilon` while preserving the
--   `sqrt (m * D0 / epsilon) + m * log m` branch rate.
-- counterargument checked: the body is a single formula, but it is the named
--   intermediate branch of a reusable finite-sum gradient-evaluation envelope
--   rather than paper-local traceability; it pairs with an unfolding theorem
--   and supports callers that want named rate functions inside Big-O goals.
-- coverage search: searched CATALOG.md, SOptLib, Staging, registry, and the
--   algorithm file for finite-sum gradient evaluation, square-root log rate,
--   `sqrt (m * D0 / epsilon) + m * log m`, and piecewise smooth finite-sum
--   complexity. Existing hits include
--   `SOptLib.smoothFiniteSumGradientEvaluationTwoBranchPiecewiseBigO`, whose second
--   branch can use this named rate, but no named reusable standalone rate
--   definition covers the branch.
-- minimal hypotheses: all already minimal for the definition; the nonnegativity
--   API theorem adds only the natural domain condition `1 <= m`.

/-- Square-root plus logarithmic branch rate for smooth finite-sum
component-gradient evaluations.

This names the intermediate closed-form branch
`sqrt (m * D0 / epsilon) + m * log m` that appears in smooth finite-sum
variance-reduced complexity bounds when neither the pure logarithmic nor the
large accuracy-ratio branch controls the display.

Layer: Model | Concept: Oracle
Proof: (definitional construction; closed-form real-valued finite-sum
  component-gradient rate with a square-root accuracy term and logarithmic
  component-count term)
Source: finite-sum variance-reduction complexity displays and Mathlib real
  square-root, logarithm, multiplication, and division APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting for the intermediate branch of the smooth finite-sum envelope
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def smoothFiniteSumGradientEvaluationSqrtLogRate
    (m epsilon D0 : Real) : Real :=
  Real.sqrt (m * D0 / epsilon) + m * Real.log m

/-- The smooth finite-sum square-root plus logarithmic gradient-evaluation rate
unfolds to `sqrt (m * D0 / epsilon) + m * log m`.

Layer: Model | Gap: Level 0 (finite-sum gradient-evaluation square-root logarithmic rate formula)
Proof: by rfl after unfolding `smoothFiniteSumGradientEvaluationSqrtLogRate`.
Source: finite-sum variance-reduction complexity displays and Mathlib real
  square-root, logarithm, multiplication, and division APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when a paper-local branch formula is normalized to a reusable
  finite-sum rate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem smoothFiniteSumGradientEvaluationSqrtLogRate_def
    (m epsilon D0 : Real) :
    smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0 =
      Real.sqrt (m * D0 / epsilon) + m * Real.log m := by
  rfl

/-- The square-root plus logarithmic finite-sum gradient-evaluation rate is
nonnegative when the component count is at least one.

Layer: Model | Gap: Level 0 (nonnegativity of finite-sum square-root logarithmic rate)
Proof: combine nonnegativity of real square root with `log m >= 0` from
  `1 <= m`, then close by ordered-ring nonnegativity of products and sums.
Source: Mathlib real square-root nonnegativity, logarithm nonnegativity, and
  ordered-ring arithmetic APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when the intermediate branch is compared through real norms
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationSqrtLogRate_nonneg
    {m epsilon D0 : ℝ} (hm : 1 ≤ m) :
    0 ≤ smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0 := by
  unfold smoothFiniteSumGradientEvaluationSqrtLogRate
  exact add_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (le_trans zero_le_one hm) (Real.log_nonneg hm))

/-- The second branch of the smooth finite-sum Big-O envelope can be read using
the named square-root plus logarithmic rate.

Layer: Model | Gap: Level 0 (finite-sum envelope intermediate branch normalization)
Proof: project the second branch from the piecewise envelope and rewrite the
  raw branch formula to the named rate, using commutativity of addition.
Source: Mathlib asymptotic Big-O filters, real square-root and logarithm APIs,
  and finite-sum variance-reduction complexity displays
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting for the intermediate branch of the smooth finite-sum envelope
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationTwoBranchPiecewiseBigO_second_sqrtLogRate
    {m D0 : ℝ} {callsByAccuracy case1 : ℝ -> ℝ}
    (h :
      smoothFiniteSumGradientEvaluationPiecewiseBigO
        m D0 callsByAccuracy case1
        (fun epsilon =>
          smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0)) :
    Asymptotics.IsBigO
      (Filter.principal {epsilon : ℝ | ¬ m * epsilon >= D0})
      callsByAccuracy
      (fun epsilon =>
        smoothFiniteSumGradientEvaluationSqrtLogRate m epsilon D0) := by
  exact smoothFiniteSumGradientEvaluationPiecewiseBigO_second (h := h)


-- Generalization plan (G0):
-- concept/name: smooth finite-sum gradient-evaluation linear-tail rate; orig
--   was theorem59GradientEvaluationCase3, renamed away from theorem numbering
--   and setup fields while retaining the domain phrase finite-sum gradient
--   evaluation.
-- generality used: pure real scalar complexity parameters `m`, `L`, `mu`,
--   `epsilon`, and `D0`; no carrier type, measure, independence,
--   integrability, convexity proof, smoothness proof, oracle model, topology,
--   normed vector space, or finite-dimensional hypotheses are used.
-- portable call pattern: strongly-convex smooth finite-sum accelerated
--   gradient, SVRG/SARAH-style, and variance-reduced proximal-gradient
--   complexity proofs can vary the component count, smoothness scale,
--   strong-convexity scale, target accuracy, and initial budget while
--   preserving the `m log m + sqrt (m L / mu)` logarithmic residual tail.
-- counterargument checked: the body is a single formula, but it is the named
--   third branch of an already staged reusable finite-sum gradient-evaluation
--   envelope rather than paper-local traceability; it is not covered by the
--   first logarithmic branch or the intermediate square-root branch.
-- coverage search: searched CATALOG.md, SOptLib, Staging, registry, and the
--   algorithm source for finite-sum gradient evaluation, linear tail rate,
--   `sqrt (m * L / mu)`, and the precise residual logarithm. The relevant hit
--   is the raw third branch inside
--   `SOptLib.smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO`; no
--   standalone named reusable rate exists. LeanSearch returned Mathlib
--   primitives such as `Real.sqrt`, `Real.sqrt_nonneg`, and `Real.log_sqrt`,
--   but no finite-sum complexity rate definition.
-- minimal hypotheses: all already minimal for the definition; positivity of
--   `mu`, `epsilon`, `D0`, or the residual ratio is a caller-side domain
--   condition for estimates, not needed to name the rate.

/-- Linear-tail branch rate for smooth finite-sum component-gradient evaluations.

This names the large accuracy-ratio branch
`m * log m + sqrt (m * L / mu) * log ((D0 / epsilon) / (3 * L / (4 * mu)))`
from smooth strongly-convex finite-sum variance-reduced complexity bounds.

Layer: Model | Concept: Oracle
Proof: (definitional construction; closed-form real-valued finite-sum
  component-gradient rate with a condition-number square-root factor and
  logarithmic residual ratio)
Source: finite-sum variance-reduction complexity displays and Mathlib real
  square-root, logarithm, multiplication, and division APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting for the large accuracy-ratio tail branch of the smooth finite-sum
  envelope
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
noncomputable def smoothFiniteSumGradientEvaluationLinearTailRate
    (m L mu epsilon D0 : Real) : Real :=
  m * Real.log m +
    Real.sqrt (m * L / mu) *
      Real.log ((D0 / epsilon) / (3 * L / (4 * mu)))

/-- The smooth finite-sum linear-tail gradient-evaluation rate unfolds to the
closed-form third branch formula.

Layer: Model | Gap: Level 0 (finite-sum gradient-evaluation linear-tail rate formula)
Proof: by rfl after unfolding `smoothFiniteSumGradientEvaluationLinearTailRate`.
Source: finite-sum variance-reduction complexity displays and Mathlib real
  square-root, logarithm, multiplication, and division APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when a paper-local tail formula is normalized to a reusable
  finite-sum rate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
@[simp]
theorem smoothFiniteSumGradientEvaluationLinearTailRate_def
    (m L mu epsilon D0 : Real) :
    smoothFiniteSumGradientEvaluationLinearTailRate m L mu epsilon D0 =
      m * Real.log m +
        Real.sqrt (m * L / mu) *
          Real.log ((D0 / epsilon) / (3 * L / (4 * mu))) := by
  rfl

/-- The linear-tail finite-sum gradient-evaluation rate is nonnegative on its
natural displayed domain.

Layer: Model | Gap: Level 0 (nonnegativity of finite-sum linear-tail rate)
Proof: combine nonnegativity of the component-count logarithmic term with
  nonnegativity of real square root and logarithm on arguments at least one.
Source: Mathlib real square-root nonnegativity, logarithm nonnegativity, and
  ordered-ring arithmetic APIs
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting when the tail branch is compared through real norms
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationLinearTailRate_nonneg
    {m L mu epsilon D0 : Real}
    (hm : 1 <= m)
    (h_ratio : 1 <= (D0 / epsilon) / (3 * L / (4 * mu))) :
    0 <= smoothFiniteSumGradientEvaluationLinearTailRate m L mu epsilon D0 := by
  unfold smoothFiniteSumGradientEvaluationLinearTailRate
  exact add_nonneg
    (mul_nonneg (le_trans zero_le_one hm) (Real.log_nonneg hm))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg h_ratio))

/-- The third branch of the three-regime smooth finite-sum envelope can be read
using the named linear-tail rate.

Layer: Model | Gap: Level 0 (finite-sum envelope tail branch normalization)
Proof: project the third branch from the three-regime envelope and rewrite the
  raw branch formula to the named linear-tail rate.
Source: Mathlib asymptotic Big-O filters, real square-root and logarithm APIs,
  and finite-sum variance-reduction complexity displays
Used in: variance-reduced accelerated-gradient component-gradient complexity
  accounting for the large accuracy-ratio tail branch of the smooth finite-sum
  envelope
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_third_linearTailRate
    {m L mu D0 : Real} {callsByAccuracy : Real -> Real}
    (h :
      smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO
        m L mu D0 callsByAccuracy) :
    Asymptotics.IsBigO
      (Filter.comap (fun epsilon : Real => D0 / epsilon)
          (Filter.atTop : Filter Real) ⊓
        Filter.principal
          {epsilon : Real |
            0 < epsilon ∧
              ¬ (m >= D0 / epsilon ∨
                  m >= 3 * L / (4 * mu)) ∧
                ¬ D0 / epsilon <= 3 * L / (4 * mu)})
      callsByAccuracy
      (fun epsilon =>
        smoothFiniteSumGradientEvaluationLinearTailRate m L mu epsilon D0) := by
  simpa [smoothFiniteSumGradientEvaluationLinearTailRate] using
    smoothFiniteSumGradientEvaluationThreeRegimePiecewiseBigO_third (h := h)

end SOptLib
