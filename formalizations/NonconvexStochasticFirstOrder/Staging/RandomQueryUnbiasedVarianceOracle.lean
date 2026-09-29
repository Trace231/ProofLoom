import SOptLib.Model.StochasticOracle

open MeasureTheory

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: random-query unbiased bounded-variance stochastic oracle; orig
--   was RandomQueryOracleBridge.
-- generality used: arbitrary sample space Omega with a measurable space,
--   arbitrary query type X, sample type Sample, index type T, normed real
--   vector codomain E with measurable codomain structure, measure mu,
--   stochastic kernel G, deterministic target field, indexed sample process,
--   and variance scale sigma; no objective, gradient, filtration,
--   independence, smoothness, convexity, or finite-dimensional assumptions are
--   needed by this packaging predicate.
-- portable call pattern: stochastic-gradient, stochastic mirror-descent,
--   validation, and randomized-output proofs can instantiate the sample space,
--   oracle kernel, target field, query, indexed sample process, measure, and
--   variance radius while keeping the same random-query well-definedness,
--   unbiased expectation identity, and centered second-moment conclusion.
-- counterargument checked: not paper-local traceability because this is the
--   reusable random-query counterpart of fixed-query unbiased-variance oracle
--   assumptions; not a caller-side expression once downstream proofs project
--   well-definedness, mean equality, residual integrability, and variance
--   bounds at many random queries.
-- coverage search: searched "random query oracle well-defined unbiased
--   expectation second moment bound", "sampled oracle random iterate
--   expectation equals target variance bound", and "integrable unbiased
--   variance bounded centered second moment random query oracle contract";
--   top hits included SOptLib.oracleRandomIterateVarianceBound,
--   SOptLib.FixedQueryUnbiasedVarianceOracle, and
--   SOptLib.BoundedVarianceUnbiasedOracleOn, all partial rather than this
--   all-random-query bundled mean-plus-variance contract.
-- minimal hypotheses: all already minimal for the predicate; MeasurableSpace E
--   is needed for the explicit Measurable oracle-value field, and the normed
--   real vector structure is needed for Bochner integrability, subtraction,
--   norms, and squared residuals.

/-- Random-query stochastic oracle assumptions with unbiased expectation and
bounded centered second moment.

For every index and random query, the sampled oracle value is measurable and
integrable, its centered residual is integrable, the squared residual is
integrable, the oracle expectation equals the target expectation, and the
centered second moment is bounded by `sigma ^ 2`.

Layer: Model | Concept: Random-query unbiased bounded-variance stochastic oracle
Proof: (definitional construction; indexed conjunction of random-query
  measurability, Bochner integrability, mean equality, and centered squared
  residual moment control)
Source: Stochastic first-order oracle assumptions, Mathlib Bochner integral
  notation, and normed-space residual second-moment predicates
Used in: randomized stochastic gradient descent proofs when Assumption 13 is
  projected at algorithm-generated iterates and post-optimization validation
  queries before martingale and second-moment estimates
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
def RandomQueryUnbiasedVarianceOracle
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → Sample → E) (target : X → E)
    (sample : T → Ω → Sample) (sigma : ℝ) : Prop :=
  ∀ (t : T) (query : Ω → X),
    (Measurable (fun ω : Ω => G (query ω) (sample t ω)) ∧
      Integrable (fun ω : Ω => G (query ω) (sample t ω)) μ ∧
      Integrable (fun ω : Ω => G (query ω) (sample t ω) - target (query ω)) μ ∧
      Integrable
        (fun ω : Ω => ‖G (query ω) (sample t ω) - target (query ω)‖ ^ (2 : ℕ)) μ) ∧
    ((∫ ω, G (query ω) (sample t ω) ∂μ) =
        ∫ ω, target (query ω) ∂μ) ∧
      (∫ ω, ‖G (query ω) (sample t ω) - target (query ω)‖ ^ (2 : ℕ) ∂μ) ≤
        sigma ^ (2 : ℕ)

/-- The random-query unbiased-variance oracle predicate unfolds to its
well-definedness, mean equality, and second-moment clauses.

Layer: Model | Gap: Level 0 (random-query oracle contract unfolding)
Proof: by rfl after unfolding RandomQueryUnbiasedVarianceOracle.
Source: Mathlib Bochner integral notation and normed-space residual
  second-moment predicates
Used in: randomized stochastic gradient descent proofs that project Assumption
  13 at a chosen random iterate or validation query
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
@[simp]
theorem RandomQueryUnbiasedVarianceOracle_def
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (G : X → Sample → E) (target : X → E)
    (sample : T → Ω → Sample) (sigma : ℝ) :
    RandomQueryUnbiasedVarianceOracle μ G target sample sigma ↔
      ∀ (t : T) (query : Ω → X),
        (Measurable (fun ω : Ω => G (query ω) (sample t ω)) ∧
          Integrable (fun ω : Ω => G (query ω) (sample t ω)) μ ∧
          Integrable (fun ω : Ω => G (query ω) (sample t ω) - target (query ω)) μ ∧
          Integrable
            (fun ω : Ω =>
              ‖G (query ω) (sample t ω) - target (query ω)‖ ^ (2 : ℕ)) μ) ∧
        ((∫ ω, G (query ω) (sample t ω) ∂μ) =
            ∫ ω, target (query ω) ∂μ) ∧
          (∫ ω, ‖G (query ω) (sample t ω) - target (query ω)‖ ^ (2 : ℕ) ∂μ) ≤
            sigma ^ (2 : ℕ) := by
  rfl

theorem RandomQueryUnbiasedVarianceOracle.measurable
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {G : X → Sample → E} {target : X → E}
    {sample : T → Ω → Sample} {sigma : ℝ}
    (h : RandomQueryUnbiasedVarianceOracle μ G target sample sigma)
    (t : T) (query : Ω → X) :
    Measurable (fun ω : Ω => G (query ω) (sample t ω)) :=
  (h t query).1.1

theorem RandomQueryUnbiasedVarianceOracle.integrable
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {G : X → Sample → E} {target : X → E}
    {sample : T → Ω → Sample} {sigma : ℝ}
    (h : RandomQueryUnbiasedVarianceOracle μ G target sample sigma)
    (t : T) (query : Ω → X) :
    Integrable (fun ω : Ω => G (query ω) (sample t ω)) μ :=
  (h t query).1.2.1

theorem RandomQueryUnbiasedVarianceOracle.centered_integrable
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {G : X → Sample → E} {target : X → E}
    {sample : T → Ω → Sample} {sigma : ℝ}
    (h : RandomQueryUnbiasedVarianceOracle μ G target sample sigma)
    (t : T) (query : Ω → X) :
    Integrable
      (fun ω : Ω => G (query ω) (sample t ω) - target (query ω)) μ :=
  (h t query).1.2.2.1

theorem RandomQueryUnbiasedVarianceOracle.centered_sq_integrable
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {G : X → Sample → E} {target : X → E}
    {sample : T → Ω → Sample} {sigma : ℝ}
    (h : RandomQueryUnbiasedVarianceOracle μ G target sample sigma)
    (t : T) (query : Ω → X) :
    Integrable
      (fun ω : Ω => ‖G (query ω) (sample t ω) - target (query ω)‖ ^ (2 : ℕ)) μ :=
  (h t query).1.2.2.2

theorem RandomQueryUnbiasedVarianceOracle.mean_eq
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {G : X → Sample → E} {target : X → E}
    {sample : T → Ω → Sample} {sigma : ℝ}
    (h : RandomQueryUnbiasedVarianceOracle μ G target sample sigma)
    (t : T) (query : Ω → X) :
    (∫ ω, G (query ω) (sample t ω) ∂μ) =
      ∫ ω, target (query ω) ∂μ :=
  (h t query).2.1

theorem RandomQueryUnbiasedVarianceOracle.variance_bound
    {Ω X Sample E T : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {G : X → Sample → E} {target : X → E}
    {sample : T → Ω → Sample} {sigma : ℝ}
    (h : RandomQueryUnbiasedVarianceOracle μ G target sample sigma)
    (t : T) (query : Ω → X) :
    (∫ ω, ‖G (query ω) (sample t ω) - target (query ω)‖ ^ (2 : ℕ) ∂μ) ≤
      sigma ^ (2 : ℕ) :=
  (h t query).2.2

end SOptLib
