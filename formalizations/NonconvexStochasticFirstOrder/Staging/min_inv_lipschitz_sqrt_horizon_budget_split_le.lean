import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: minimum inverse-Lipschitz square-root-horizon budget split;
--   orig was `constant_stepsize_min_budget_split_scalar`.
-- generality used: real scalar radius, smoothness, noise, balancing radius,
--   horizon, and stepsize; no measure, independence, integrability,
--   convexity, oracle, normed-space, or finite-dimensional assumptions are
--   used.
-- portable call pattern: constant-stepsize smooth-descent proofs with
--   `gamma = min (1 / L) (d / (sigma * sqrt N))` call this when converting
--   the generic `D^2/(N*gamma) + sigma^2*gamma` descent budget into a closed
--   deterministic-plus-square-root noise rate; `D`, `L`, `sigma`, `d`, and
--   `N` vary while the split conclusion stays the same.
-- counterargument checked: although the proof is scalar algebra, it is not
--   merely paper-local traceability because the same clipped inverse-Lipschitz
--   and square-root-horizon stepsize split appears in randomized-output
--   nonconvex SGD and related smooth-descent budget proofs.
-- coverage search: searched "minimum inverse Lipschitz square root horizon
--   stepsize budget split upper bound", "D squared over N gamma plus sigma
--   squared gamma bound gamma min one over L d over sigma sqrt N", and
--   "min_inv_lipschitz_sqrt_horizon stationarity budget bound"; hits included
--   `min_inv_lipschitz_sqrt_horizon_stepsize`, its branch bounds,
--   `nonconvexStationarityBudgetBound`, and
--   `sq_add_sq_mul_mul_sq_div_mul_sub_le_div_add_sq_mul_of_mul_le_one`, but no
--   existing declaration covers this closed-form min-stepsize budget split.
-- minimal hypotheses: positivity of `N`, `L`, `sigma`, and `d` are exactly the
--   denominator and branch-comparison assumptions consumed by the scalar proof.

/-- The inverse-Lipschitz and square-root-horizon minimum stepsize splits the
generic constant-stepsize budget into its closed-form deterministic and noise
terms.

For `gamma = min (1 / L) (d / (sigma * sqrt N))`, the expression
`D^2/(N*gamma) + sigma^2*gamma` is bounded by
`L*D^2/N + (d + D^2/d)*sigma/sqrt N`.

Layer: Glue | Gap: Level 1 (minimum-stepsize closed-form budget split)
Proof: split on which branch of the minimum is active; the inverse-Lipschitz
  branch uses the branch inequality to bound the variance term, and the
  square-root-horizon branch simplifies the two budget terms by field algebra.
Source: Mathlib real square-root, lattice minimum, and ordered-field arithmetic APIs
Used in: randomized-output nonconvex stochastic-gradient one-run stationarity
  proof after the smooth-descent ratio has been reduced to a constant-stepsize
  scalar budget
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/parameters/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem min_inv_lipschitz_sqrt_horizon_budget_split_le
    (D L sigma d N gamma : ℝ)
    (hN : 0 < N) (hL : 0 < L) (hsigma : 0 < sigma) (hd : 0 < d)
    (hgamma : gamma = min (1 / L) (d / (sigma * Real.sqrt N))) :
    D ^ 2 / (N * gamma) + sigma ^ 2 * gamma ≤
      L * D ^ 2 / N + (d + D ^ 2 / d) * sigma / Real.sqrt N := by
  subst gamma
  let s : ℝ := Real.sqrt N
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 hN
  have hs_sq : s ^ 2 = N := by
    dsimp [s]
    exact Real.sq_sqrt (le_of_lt hN)
  have hden_pos : 0 < sigma * s := mul_pos hsigma hs_pos
  change
    D ^ 2 / (N * min (1 / L) (d / (sigma * s))) +
        sigma ^ 2 * min (1 / L) (d / (sigma * s)) ≤
      L * D ^ 2 / N + (d + D ^ 2 / d) * sigma / s
  by_cases hcase : 1 / L ≤ d / (sigma * s)
  · have hgamma_eq :
        min (1 / L) (d / (sigma * s)) = 1 / L := min_eq_left hcase
    have hD_eq : D ^ 2 / (N * (1 / L)) = L * D ^ 2 / N := by
      field_simp [ne_of_gt hN, ne_of_gt hL]
    have hvar :
        sigma ^ 2 * (1 / L) ≤ d * sigma / s := by
      calc
        sigma ^ 2 * (1 / L)
            ≤ sigma ^ 2 * (d / (sigma * s)) := by
              exact mul_le_mul_of_nonneg_left hcase (sq_nonneg sigma)
        _ = d * sigma / s := by
              field_simp [ne_of_gt hsigma, ne_of_gt hs_pos]
    have hextra : 0 ≤ (D ^ 2 / d) * sigma / s := by
      exact div_nonneg
        (mul_nonneg
          (div_nonneg (sq_nonneg D) (le_of_lt hd))
          (le_of_lt hsigma))
        (le_of_lt hs_pos)
    rw [hgamma_eq, hD_eq]
    calc
      L * D ^ 2 / N + sigma ^ 2 * (1 / L)
          ≤ L * D ^ 2 / N + d * sigma / s := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hvar (L * D ^ 2 / N)
      _ ≤ L * D ^ 2 / N + (d * sigma / s + (D ^ 2 / d) * sigma / s) := by
            nlinarith
      _ = L * D ^ 2 / N + (d + D ^ 2 / d) * sigma / s := by
            ring
  · have hb_le : d / (sigma * s) ≤ 1 / L := le_of_not_ge hcase
    have hgamma_eq :
        min (1 / L) (d / (sigma * s)) = d / (sigma * s) := min_eq_right hb_le
    have hsplit :
        D ^ 2 / (N * (d / (sigma * s))) +
            sigma ^ 2 * (d / (sigma * s)) =
          (D ^ 2 / d) * sigma / s + d * sigma / s := by
      field_simp [ne_of_gt hN, ne_of_gt hd, ne_of_gt hsigma, ne_of_gt hs_pos]
      nlinarith [hs_sq]
    have hLterm : 0 ≤ L * D ^ 2 / N := by
      exact div_nonneg
        (mul_nonneg (le_of_lt hL) (sq_nonneg D))
        (le_of_lt hN)
    rw [hgamma_eq, hsplit]
    calc
      (D ^ 2 / d) * sigma / s + d * sigma / s
          = (d + D ^ 2 / d) * sigma / s := by
            ring
      _ ≤ L * D ^ 2 / N + (d + D ^ 2 / d) * sigma / s := by
            nlinarith

end SOptLib
