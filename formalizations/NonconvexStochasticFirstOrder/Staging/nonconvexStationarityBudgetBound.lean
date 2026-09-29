import Mathlib.Data.Real.Sqrt

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: nonconvex stationarity budget bound; orig was
--   `stationarityBudgetFormula`, renamed away from the paper-local wrapper
--   while retaining the reusable smoothness/radius/noise budget concept.
-- generality used: real scalar smoothness, stationarity or objective-radius,
--   balancing radius, noise standard-deviation scale, and a natural horizon;
--   no measure, independence, integrability, convexity, oracle, normed-space,
--   or finite-dimensional assumptions are needed for the definition.
-- portable call pattern: nonconvex stochastic first-order, randomized-output
--   smooth-descent, and mirror-descent one-run stationarity proofs call the
--   same deterministic-plus-square-root-noise scalar budget after changing
--   `L`, `D`, `Dtilde`, `sigma`, and `N`.
-- counterargument checked: this is a closed-form formula, but it is not merely
--   paper-local traceability because convergence statements and complexity
--   reductions reuse this exact budget shape as a named model object; Mathlib
--   only provides the underlying real square-root and field operations.
-- coverage search: searched `closed form nonconvex stationarity budget L D
--   sigma Dtilde sqrt N`, `stationarity budget bound smoothness radius
--   variance balancing radius horizon`, and Mathlib LeanSearch for the same
--   square-root budget shape; the closest hit `rsmdBudgetBound` has different
--   RSMD constants and an internal maximum, so coverage is related but partial
--   and not a duplicate.
-- minimal hypotheses: all already minimal; no positivity hypotheses are needed
--   to define the totalized real-division expression.

/-- Closed-form one-run stationarity budget for nonconvex stochastic first-order
methods.

The budget combines the deterministic smoothness-radius term `L * D^2 / N`
with the square-root-horizon oracle-noise term
`(Dtilde + D^2 / Dtilde) * sigma / sqrt N`.

Layer: Model | Concept: nonconvex stationarity budget bound
Proof: (definitional construction; closed-form real-valued budget combining a deterministic descent term and a square-root-horizon oracle-noise term)
Source: Mathlib real square-root, division, powers, and ordered-field notation for stochastic approximation stationarity budgets
Used in: two-phase randomized stochastic-gradient one-run stationarity bound before Markov and validation-sample amplification
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
noncomputable def nonconvexStationarityBudgetBound
    (L D Dtilde sigma : ℝ) (N : Nat) : ℝ :=
  L * D ^ 2 / (N : ℝ) +
    (Dtilde + D ^ 2 / Dtilde) * sigma / Real.sqrt (N : ℝ)

/-- The nonconvex stationarity budget unfolds to its closed-form scalar formula.

Layer: Model | Gap: Level 0 (nonconvex stationarity budget unfolding)
Proof: by rfl after unfolding `nonconvexStationarityBudgetBound`.
Source: Mathlib real square-root, division, powers, and ordered-field notation for stochastic approximation stationarity budgets
Used in: rewriting the named one-run nonconvex stochastic-gradient stationarity budget to the printed scalar expression
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
@[simp]
theorem nonconvexStationarityBudgetBound_def
    (L D Dtilde sigma : ℝ) (N : Nat) :
    nonconvexStationarityBudgetBound L D Dtilde sigma N =
      L * D ^ 2 / (N : ℝ) +
        (Dtilde + D ^ 2 / Dtilde) * sigma / Real.sqrt (N : ℝ) := by
  rfl

/-- The closed-form nonconvex stationarity budget is nonnegative under the
usual nonnegative smoothness, balancing-radius, and noise assumptions.

Layer: Model | Gap: Level 0 (nonconvex stationarity budget nonnegativity)
Proof: each summand in the closed-form budget is nonnegative by ordered-field
arithmetic, square nonnegativity, nonnegativity of the balancing radius, and
nonnegativity of the real square root.
Source: Mathlib real square-root, division, powers, and ordered-field
nonnegativity rules for stochastic approximation stationarity budgets
Used in: Markov-tail and complexity reductions that need a positive or
nonnegative stationarity budget threshold -/
theorem nonconvexStationarityBudgetBound_nonneg
    {L D Dtilde sigma : ℝ} {N : Nat}
    (hL : 0 ≤ L) (hDtilde : 0 ≤ Dtilde) (hsigma : 0 ≤ sigma) :
    0 ≤ nonconvexStationarityBudgetBound L D Dtilde sigma N := by
  have hfirst :
      0 ≤ L * D ^ 2 / (N : ℝ) := by
    exact div_nonneg (mul_nonneg hL (sq_nonneg D)) (Nat.cast_nonneg N)
  have hD_div : 0 ≤ D ^ 2 / Dtilde := by
    exact div_nonneg (sq_nonneg D) hDtilde
  have hfactor : 0 ≤ Dtilde + D ^ 2 / Dtilde := by
    exact add_nonneg hDtilde hD_div
  have hsecond :
      0 ≤ (Dtilde + D ^ 2 / Dtilde) * sigma / Real.sqrt (N : ℝ) := by
    exact div_nonneg (mul_nonneg hfactor hsigma) (Real.sqrt_nonneg _)
  simpa [nonconvexStationarityBudgetBound] using add_nonneg hfirst hsecond

end SOptLib
