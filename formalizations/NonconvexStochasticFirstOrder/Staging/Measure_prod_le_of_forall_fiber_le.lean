import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: product-measure bound from uniformly bounded right fibers; orig was prod_measure_le_of_fiber_measure_le.
-- generality used: arbitrary measurable spaces, arbitrary left and right measures, a probability assumption only on the left marginal, and pointwise bounds on all right fibers of a measurable product set.
-- portable call pattern: stochastic-optimization validation or fresh-sample steps first prove a tail bound for every fixed history/query fiber, then lift that bound to the joint product law while the history law, sample law, event, and constant vary.
-- counterargument checked: this is a short wrapper around `Measure.prod_apply_le`, but it packages a recurring Fubini/Tonelli monotonicity step; existing PMF fiber expansions cover finite left laws and equalities, not arbitrary probability left marginals with uniform fiber bounds.
-- coverage search: queried `product measure set less equal constant from all section fiber measures bounded measurable set` and `Measure prod_apply_le measurable set product measure less equal lintegral fiber`; top hits were Mathlib `Measure.prod_apply_le`, Mathlib `Measure.prod_apply`, and SOptLib PMF finite-fiber sum lemmas, giving partial ingredient coverage but no full uniform-bound theorem.
-- minimal hypotheses: `SFinite ν` from the source proof is unnecessary because `Measure.prod_apply_le` gives the required inequality; all remaining hypotheses are used.

namespace Measure

/-- A product-measure event has mass at most `C` when every right fiber has
measure at most `C` and the left marginal is a probability measure.

Layer: Glue | Gap: Level 1 (product-measure uniform fiber tail lift)
Proof: apply Mathlib `Measure.prod_apply_le`, dominate the fiber-measure lintegral by the constant `C`, and use the probability mass of the left marginal.
Source: Mathlib product-measure Tonelli API and probability-measure normalization
Used in: two-phase randomized stochastic gradient validation, where a fixed-candidate post-optimization tail bound is lifted over the optimization-history/sample product law
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient descent -/
theorem prod_le_of_forall_fiber_le
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ]
    (E : Set (A × B)) (hE : MeasurableSet E) (C : ENNReal)
    (hfiber : ∀ a, ν (Prod.mk a ⁻¹' E) ≤ C) :
    (μ.prod ν) E ≤ C := by
  calc
    (μ.prod ν) E ≤ ∫⁻ a, ν (Prod.mk a ⁻¹' E) ∂μ :=
      Measure.prod_apply_le hE
    _ ≤ ∫⁻ _a : A, C ∂μ :=
      lintegral_mono hfiber
    _ = C := by simp

end Measure
