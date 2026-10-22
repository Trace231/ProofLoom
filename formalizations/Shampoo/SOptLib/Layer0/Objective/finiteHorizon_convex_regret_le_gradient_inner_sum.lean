import SOptLib.Glue.Calculus

open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: finite-horizon convex regret bounded by a gradient inner-product sum; orig was generated_convex_regret_le_gradient_sum
-- generality used: a complete real inner-product normed additive group, a feasible carrier, a natural-indexed convex loss family, finite-horizon iterates and gradient witnesses; no measure, filtration, independence, oracle, or finite-dimensional assumption is used
-- portable call pattern: online convex optimization, finite-sum gradient, stochastic-gradient, and mirror-descent regret proofs can change the carrier, loss family, horizon, iterates, comparator, and gradient witnesses while reusing the same finite-sum first-order convexity bound
-- counterargument checked: not paper-local traceability or a caller-side expression because it packages the nontrivial convex first-order support step with finite aggregation; it is not a duplicate of SOptLib's pointwise support theorem, which has no finite-horizon regret conclusion
-- coverage search: queried `finite sum convex first order inequality gradient inner product regret`, `convex value difference inner product HasGradientAt`, and the SOptLib catalog; `ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt` was a partial pointwise hit, with no existing finite-horizon aggregation theorem
-- minimal hypotheses: the feasible iterates and gradient witnesses are pointwise only on `Finset.Icc 1 T`; the complete-space instance is retained because the reused SOptLib first-order support API requires it

/-- A finite-horizon sum of convex losses is bounded by the corresponding
gradient-inner-product sum against any feasible comparator.

Layer: Layer0 | Gap: Level 1 (finite-horizon convex first-order regret bound)
Proof: apply the convex first-order supporting-hyperplane inequality at each
feasible iterate and sum the resulting pointwise bounds over the closed
one-based horizon.
Source: Mathlib convex first-order support, real inner-product algebra, and
finite-set sum monotonicity
Used in: online convex optimization proofs that convert the loss regret of
feasible iterates into the accumulated inner products with their gradient
witnesses before the algorithm-specific update telescope
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad online convex optimization -/
theorem finite_horizon_convex_regret_le_gradient_inner_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : Set E) (loss : ℕ → E → ℝ) (x g : ℕ → E)
    (T : ℕ) (xStar : E)
    (hconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ F (loss t))
    (hx : ∀ t ∈ Finset.Icc 1 T, x t ∈ F)
    (hxStar : xStar ∈ F)
    (hgrad :
      ∀ t ∈ Finset.Icc 1 T, HasGradientWithinAt (loss t) (g t) F (x t)) :
    (Finset.Icc 1 T).sum (fun t => loss t (x t)) -
        (Finset.Icc 1 T).sum (fun t => loss t xStar) ≤
      (Finset.Icc 1 T).sum (fun t => inner ℝ (g t) (x t - xStar)) := by
  have hsum :
      (Finset.Icc 1 T).sum (fun t => loss t (x t) - loss t xStar) ≤
        (Finset.Icc 1 T).sum (fun t => inner ℝ (g t) (x t - xStar)) :=
    Finset.sum_le_sum (by
      intro t ht
      have hsupport :
          loss t (x t) + inner ℝ (g t) (xStar - x t) ≤ loss t xStar :=
        by
          exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
            (hconv t ht) (hx t ht) hxStar (hgrad t ht)
      have hinner :
          inner ℝ (g t) (xStar - x t) =
            -inner ℝ (g t) (x t - xStar) := by
        rw [← inner_neg_right]
        congr 1
        abel
      linarith)
  simpa [Finset.sum_sub_distrib] using hsum
