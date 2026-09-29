import Mathlib.Data.Real.Sqrt

-- Generalization plan (G0):
-- concept/name: scaled objective-gap radius; orig was `objectiveRadius`,
--   renamed away from the paper-local `D_f` wrapper and setup fields while
--   retaining the stochastic-optimization budget concept.
-- generality used: four scalar real parameters `scale`, `initialValue`,
--   `optimumValue`, and denominator `L`; no carrier, measure, filtration,
--   convexity, smoothness, oracle, normed-space, or finite-dimensional
--   hypotheses are needed for the definition, and the square theorem only
--   needs nonnegative scale, nonnegative objective gap, and positive `L`.
-- portable call pattern: nonconvex stochastic first-order and mirror-descent
--   convergence proofs call this when turning a scaled initial objective gap
--   into a radius whose square reappears in descent and complexity budgets;
--   `scale`, endpoint values, and smoothness denominator change while the
--   closed-form radius and square identity stay the same.
-- counterargument checked: this is a one-line formula, but the existing
--   algorithm repeatedly uses the named radius and its square identity in
--   budgets; Mathlib only provides `Real.sq_sqrt`, and the existing SOptLib
--   `objectiveGapRadius` is the unscaled special case, so neither covers the
--   scaled objective-gap boundary without an unnatural caller rewrite.
-- coverage search: searched `scaled objective gap radius square identity
--   positive denominator` and `objective gap radius sqrt divided by
--   smoothness square`; top hits were SOptLib `objectiveGapRadius`,
--   `objectiveGapRadius_eq`, the local paper theorem
--   `objectiveRadius_sq_eq_scaled_initial_gap`, and Mathlib `Real.sq_sqrt`;
--   coverage is partial, not a full duplicate.
-- minimal hypotheses: all already minimal; the caller's bounded-below proof is
--   reduced to the pointwise gap premise `optimumValue <= initialValue`.

/-- Scaled objective-gap radius obtained by multiplying an objective gap by a
nonnegative scale, dividing by a smoothness denominator, and taking a square
root.

`scaledObjectiveGapRadius scale initialValue optimumValue L` names the
closed-form radius `sqrt (scale * (initialValue - optimumValue) / L)` without
committing to a particular objective, algorithm state, or optimum witness.

Layer: Model | Concept: scaled objective-gap radius
Proof: (definitional construction; square-root radius from a scaled real objective gap)
Source: Mathlib real square-root and ordered-field APIs for scaled objective-gap radii
Used in: two-phase randomized stochastic gradient descent initialization of the `D_f` radius before descent telescoping and complexity-budget bounds
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient descent -/
noncomputable def scaledObjectiveGapRadius
    (scale initialValue optimumValue L : Real) : Real :=
  Real.sqrt (scale * (initialValue - optimumValue) / L)

/-- The scaled objective-gap radius unfolds to its square-root formula.

Layer: Model | Gap: Level 0 (scaled objective-gap radius formula)
Proof: by rfl after unfolding `scaledObjectiveGapRadius`.
Source: Mathlib real square-root and ordered-field APIs for scaled objective-gap radii
Used in: two-phase randomized stochastic gradient descent initialization of the `D_f` radius before exposing its closed form in later bounds
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient descent -/
@[simp]
theorem scaledObjectiveGapRadius_eq
    (scale initialValue optimumValue L : Real) :
    scaledObjectiveGapRadius scale initialValue optimumValue L =
      Real.sqrt (scale * (initialValue - optimumValue) / L) := by
  rfl

/-- The square of a scaled objective-gap radius is the scaled gap divided by
the nonnegative denominator.

Layer: Model | Gap: Level 0 (scaled objective-gap radius square identity)
Proof: unfold the radius and apply `Real.sq_sqrt`, proving the radicand is nonnegative from the nonnegative scale, nonnegative objective gap, and nonnegative denominator.
Source: Mathlib `Real.sq_sqrt` with ordered-field nonnegativity for products and quotients
Used in: two-phase randomized stochastic gradient descent descent telescope where `D_f^2` is rewritten as `2 * (f x_1 - f^*) / L`
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient descent -/
theorem scaledObjectiveGapRadius_sq_eq
    (scale initialValue optimumValue L : Real)
    (hscale_nonneg : 0 <= scale)
    (hgap_nonneg : optimumValue <= initialValue)
    (hL_nonneg : 0 <= L) :
    scaledObjectiveGapRadius scale initialValue optimumValue L ^ 2 =
      scale * (initialValue - optimumValue) / L := by
  rw [scaledObjectiveGapRadius_eq]
  exact Real.sq_sqrt
    (div_nonneg
      (mul_nonneg hscale_nonneg (sub_nonneg.mpr hgap_nonneg))
      hL_nonneg)
