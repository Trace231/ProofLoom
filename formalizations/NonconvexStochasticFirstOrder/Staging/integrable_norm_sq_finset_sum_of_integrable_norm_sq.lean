import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-sum L2 closure as squared-norm integrability; orig was
--   `integrable_norm_sq_finset_sum_of_integrable_sq_norm`, renamed to expose
--   the `norm_sq` conclusion and the `integrable_norm_sq` hypotheses.
-- generality used: arbitrary measurable sample space, arbitrary measure, finite
--   index set, and normed additive commutative target group; no probability,
--   independence, oracle, objective, convexity, smoothness, scalar action, inner
--   product, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: finite mini-batch, validation-residual, martingale, and
--   distributed-noise proofs close the squared norm of a finite aggregate after
--   proving a.e. strong measurability and squared-norm integrability for each
--   summand; the index finset, measure, carrier, and summand process vary.
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; Mathlib has the underlying `MemLp` finite-sum lemma, but not the
--   direct squared-norm-integrability wrapper used at algorithm call sites.
-- coverage search: queried `integrable squared norm finite sum summands`,
--   `MemLp finite sum integrable squared norm`, and LeanSearch `integrable
--   squared norm of finite sum from integrable squared norms MemLp`; closest
--   hits were Mathlib `MeasureTheory.memLp_finset_sum` and
--   `MeasureTheory.memLp_two_iff_integrable_sq_norm`, plus SOptLib
--   `integrable_sq_norm_centeredMiniBatchAverage`, which is a Layer0 scaled
--   mini-batch-average wrapper rather than the unscaled Glue finite-sum closure.
-- minimal hypotheses: weakened the source's real vector-space assumption to a
--   normed additive commutative group; the proof needs only component
--   a.e.-strong measurability and component squared-norm integrability.

/-- The squared norm of a finite pointwise sum is integrable when every summand
has integrable squared norm.

Layer: Glue | Gap: Level 1 (finite-sum L2 squared-norm integrability closure)
Proof: convert each squared-norm integrability hypothesis to `MemLp · 2`, close
  `MemLp` under finite sums, and convert the aggregate back by
  `memLp_two_iff_integrable_sq_norm`.
Source: Mathlib Lp-space finite-sum closure and squared-norm integrability
  characterization in `MeasureTheory.Function.L2Space`
Used in: martingale and validation residual proofs for two-phase stochastic
  gradient methods, where finite aggregate noise terms need squared-norm
  integrability before Markov or second-moment bounds are applied
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem integrable_norm_sq_finset_sum_of_integrable_norm_sq
    {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E]
    (μ : Measure Ω) (I : Finset ι) (δ : ι -> Ω -> E)
    (hmeas : forall i, i ∈ I -> AEStronglyMeasurable (δ i) μ)
    (hL2 : forall i, i ∈ I -> Integrable (fun ω => ‖δ i ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖Finset.sum I (fun i => δ i ω)‖ ^ 2) μ := by
  classical
  have hδ_l2 : forall i, i ∈ I -> MemLp (δ i) 2 μ := by
    intro i hi
    exact (memLp_two_iff_integrable_sq_norm (hmeas i hi)).2 (hL2 i hi)
  have hsum_l2 : MemLp (fun ω => Finset.sum I (fun i => δ i ω)) 2 μ := by
    simpa using memLp_finset_sum I hδ_l2
  exact (memLp_two_iff_integrable_sq_norm hsum_l2.aestronglyMeasurable).1 hsum_l2

end SOptLib
