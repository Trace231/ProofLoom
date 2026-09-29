import SOptLib.Glue.Probability

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite PMF product-measure fiber-event upper bound from uniform fiber bounds; orig was fixed_candidate_tail_under_stopping_vector_for_candidate.
-- generality used: finite measurable selector type, arbitrary measurable sample space, arbitrary sample measure with `SFinite`, an arbitrary dependent family of fiber events, and a pointwise ENNReal bound.
-- portable call pattern: finite randomized-output or stopping-vector arguments first prove the same tail bound for every selected fiber, then lift it to the selector/sample product law while the selector law, sample law, event family, and constant vary.
-- counterargument checked: this is a short aggregation over an existing PMF expansion, but it removes caller-side finite-sum bookkeeping and does not duplicate the more general measurable-set product theorem because no measurability of the dependent event is required.
-- coverage search: queried `product measure fiber event upper bound forall fiber measure le`, `product measure set fiber measure bounded by constant implies product measure bounded`, and catalog PMF product-measure fiber entries; hits were Mathlib `Measure.prod_apply_le`, staged `Measure.prod_le_of_forall_fiber_le`, and SOptLib `PMF.prod_measure_set_sigma_eq_sum`, all partial rather than this no-measurability finite-PMF bound.
-- minimal hypotheses: `SFinite μ` is needed by the reused PMF finite product expansion; the selector side only needs `Fintype`, `MeasurableSpace`, and `MeasurableSingletonClass`.

namespace PMF

/-- A finite PMF/product-measure dependent fiber event has mass at most `C`
when every fiber has measure at most `C`.

For a finite discrete selector law `p`, this packages the weighted finite-sum
argument: expand the product event into `∑ a, p a * μ (A a)`, dominate each
fiber by `C`, and use that the PMF masses sum to one.

Layer: Glue | Gap: Level 1 (finite PMF product-measure uniform fiber tail lift)
Proof: reuse the SOptLib finite PMF product-fiber expansion, apply finite-sum monotonicity to the pointwise fiber bounds, and normalize by `PMF.tsum_coe`.
Source: Mathlib probability mass functions, finite sums in `ENNReal`, and product-measure fiber expansions
Used in: two-phase randomized stochastic gradient validation, lifting a fixed stopping-vector/candidate validation tail bound over the stopping-vector PMF and validation-sample product law
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient descent -/
theorem prod_measure_fiber_event_le_of_forall_le
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (p : PMF α) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω) (C : ENNReal) (hfiber : ∀ a, μ (A a) ≤ C) :
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} ≤ C := by
  classical
  have hsum_le :
      ∑ a : α, p a * μ (A a) ≤ ∑ a : α, p a * C := by
    exact Finset.sum_le_sum (by
      intro a _ha
      exact mul_le_mul_left' (hfiber a) (p a))
  have hpmf_sum : ∑ a : α, p a = 1 := by
    simpa using (PMF.tsum_coe p)
  calc
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1}
        = ∑ a : α, p a * μ (A a) := by
          exact PMF.prod_measure_set_sigma_eq_sum p μ A
    _ ≤ ∑ a : α, p a * C := hsum_le
    _ = C := by
      rw [← Finset.sum_mul, hpmf_sum, one_mul]

end PMF
