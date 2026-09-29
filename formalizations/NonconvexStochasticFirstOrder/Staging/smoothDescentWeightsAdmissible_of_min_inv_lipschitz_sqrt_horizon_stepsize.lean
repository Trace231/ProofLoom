import Mathlib.Tactic
import SOptLib.Model.Selection
import Staging.smoothDescentOutputWeight

open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: admissibility of smooth-descent output weights for the
--   minimum inverse-Lipschitz and variance-balanced constant stepsize; orig
--   was `stoppingLawAdmissible_of_positive_sigma`.
-- generality used: natural finite horizon and real scalar parameters `L`,
--   `sigma`, and `d`; no measure, independence, integrability, convexity,
--   oracle, normed-space, or finite-dimensional assumptions are used.
-- portable call pattern: constant-stepsize nonconvex SGD, randomized-output
--   smooth descent, and variance-balanced stochastic-gradient proofs choose
--   `min (1 / L) (d / (sigma * sqrt N))`; the positive parameter values and
--   horizon change while finite-window weight admissibility stays identical.
-- counterargument checked: this is not merely a paper-local wrapper because it
--   packages the recurring scalar feasibility, positive atom, and denominator
--   proof for the generic `FiniteWindowWeightsAdmissible` contract; existing
--   APIs cover the weight formula and finite-window normalization separately.
-- coverage search: queried "min inverse Lipschitz sigma sqrt horizon stepsize
--   smooth descent output weights admissible positive denominator", "finite
--   window weights admissible smooth descent output weight positive stepsize
--   feasible", and "min one over L d over sigma sqrt N positive less than two
--   over L"; hits included `smoothDescentOutputWeight_nonneg_on_of_feasible`,
--   `smoothDescentOutputWeight_denominator_pos_of_pos_of_feasible`,
--   `FiniteWindowWeightsAdmissible`, and block-descent analogues, but no
--   declaration combines the min stepsize choice with admissible weights.
-- minimal hypotheses: all already minimal for this formula: `1 <= N`,
--   `0 < L`, `0 < sigma`, and `0 < d`.

/-- The min inverse-Lipschitz and square-root-horizon stepsize gives admissible
smooth-descent output weights on a positive finite horizon.

For `gamma = min (1 / L) (d / (sigma * sqrt N))`, positivity of `L`, `sigma`,
`d`, and `N` makes every smooth-descent weight nonnegative and supplies a
positive atom, hence a positive finite-window denominator.

Layer: Model | Gap: Level 1 (variance-balanced smooth-descent output-weight admissibility)
Proof: prove the constant min stepsize is positive and below `2 / L`, then use
  the staged smooth-descent output-weight positivity API together with
  `FiniteWindowWeightsAdmissible.of_nonneg_of_pos`.
Source: Mathlib real square-root and ordered-field arithmetic, plus SOptLib
  finite-window normalized-selection APIs
Used in: two-phase randomized stochastic-gradient stopping-law construction
  for the constant variance-balanced stepsize before forming the output PMF
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem smoothDescentWeightsAdmissible_of_min_inv_lipschitz_sqrt_horizon_stepsize
    (N : Nat) (L sigma d : ℝ)
    (hN : 1 ≤ N) (hL_pos : 0 < L) (hsigma_pos : 0 < sigma) (hd_pos : 0 < d) :
    FiniteWindowWeightsAdmissible (Finset.univ : Finset (Fin N))
      (smoothDescentOutputWeight L
        (fun _ : Fin N => min (1 / L) (d / (sigma * Real.sqrt (N : ℝ))))) := by
  let gamma : ℝ := min (1 / L) (d / (sigma * Real.sqrt (N : ℝ)))
  have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN_real
  have hden_pos : 0 < sigma * Real.sqrt (N : ℝ) :=
    mul_pos hsigma_pos hsqrt_pos
  have hgamma_pos : 0 < gamma := by
    dsimp [gamma]
    exact lt_min (one_div_pos.mpr hL_pos) (div_pos hd_pos hden_pos)
  have hgamma_lt_two_div : gamma < 2 / L := by
    have hgamma_le_inv : gamma ≤ 1 / L := by
      dsimp [gamma]
      exact min_le_left _ _
    have hinv_lt_two : 1 / L < 2 / L :=
      div_lt_div_of_pos_right one_lt_two hL_pos
    exact lt_of_le_of_lt hgamma_le_inv hinv_lt_two
  have hgamma_nonneg :
      ∀ t : Fin N, t ∈ (Finset.univ : Finset (Fin N)) → 0 ≤ (fun _ : Fin N => gamma) t := by
    intro _ _
    exact le_of_lt hgamma_pos
  have hfeasible :
      smoothDescentStepsizeFeasibleOn (Finset.univ : Finset (Fin N)) L
        (fun _ : Fin N => gamma) := by
    intro _ _
    exact hgamma_lt_two_div
  have hN_pos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  let first : Fin N := ⟨0, hN_pos⟩
  have hadm :
      FiniteWindowWeightsAdmissible (Finset.univ : Finset (Fin N))
        (smoothDescentOutputWeight L (fun _ : Fin N => gamma)) := by
    refine FiniteWindowWeightsAdmissible.of_nonneg_of_pos
      (smoothDescentOutputWeight_nonneg_on_of_feasible
        (Finset.univ : Finset (Fin N)) L (fun _ : Fin N => gamma)
        hL_pos hgamma_nonneg hfeasible)
      (show first ∈ (Finset.univ : Finset (Fin N)) by simp)
      ?_
    exact smoothDescentOutputWeight_pos_of_pos_of_lt_two_div
      L (fun _ : Fin N => gamma) first hL_pos hgamma_pos hgamma_lt_two_div
  simpa [gamma] using hadm

end SOptLib
