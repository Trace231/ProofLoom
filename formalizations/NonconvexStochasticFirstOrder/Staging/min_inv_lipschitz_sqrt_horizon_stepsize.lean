import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: minimum inverse-Lipschitz square-root-horizon stepsize selector;
--   orig was `paperStepSizeFormula`.
-- generality used: real scalar smoothness/noise/radius parameters `L`,
--   `sigma`, and `D`, plus a natural horizon `N`; no measure, independence,
--   integrability, convexity, oracle, normed-space, or finite-dimensional
--   assumptions are used.
-- portable call pattern: constant-stepsize nonconvex SGD and randomized-output
--   smooth-descent proofs choose `min (1 / L) (D / (sigma * sqrt N))`; the
--   smoothness scale, noise scale, radius, and horizon vary while the selector
--   and denominator side condition stay identical.
-- counterargument checked: this is a single closed-form selector, but it is not
--   merely paper-local because the same variance-balanced constant stepsize is
--   reused by smooth-descent feasibility and stopping-law constructions; the
--   staging theorem for admissible weights consumes this formula but does not
--   name the scalar selector itself.
-- coverage search: queried "minimum inverse Lipschitz sqrt horizon stepsize
--   denominator nonzero positive sigma positive horizon", "min inverse
--   Lipschitz square root horizon stepsize formula", and "sigma times sqrt
--   natural cast nonzero positive sigma positive N"; hits included the staged
--   smooth-descent weight admissibility theorem, half-Lipschitz schedules,
--   square-root positivity facts, and unrelated Mathlib Lipschitz `min`
--   continuity lemmas, but no existing named scalar parameter choice.
-- minimal hypotheses: the definition has no hypotheses; the denominator
--   theorem uses exactly `1 <= N` and `0 < sigma`.

/-- Constant variance-balanced stepsize clipped by an inverse Lipschitz scale.

For smoothness scale `L`, noise scale `sigma`, radius `D`, and horizon `N`,
this names the standard selector `min (1 / L) (D / (sigma * sqrt N))`.

Layer: Model | Concept: variance-balanced constant stepsize selector
Proof: (definitional construction; minimum of the inverse-Lipschitz scale and a square-root-horizon variance-balance quotient)
Source: Mathlib real field operations, lattice minimum, and real square-root APIs for stochastic approximation parameter choices
Used in: nonconvex stochastic-gradient constant-stepsize selection before proving smooth-descent stopping weights and output probabilities
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
noncomputable def min_inv_lipschitz_sqrt_horizon_stepsize
    (L sigma D : ℝ) (N : Nat) : ℝ :=
  min (1 / L) (D / (sigma * Real.sqrt (N : ℝ)))

/-- The variance-balanced clipped stepsize unfolds to its closed-form scalar formula.

Layer: Model | Gap: Level 0 (variance-balanced stepsize unfolding)
Proof: by rfl after unfolding `min_inv_lipschitz_sqrt_horizon_stepsize`.
Source: Mathlib real field operations, lattice minimum, and real square-root APIs
Used in: rewriting a named nonconvex stochastic-gradient constant stepsize to the printed scalar formula
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
@[simp]
theorem min_inv_lipschitz_sqrt_horizon_stepsize_def
    (L sigma D : ℝ) (N : Nat) :
    min_inv_lipschitz_sqrt_horizon_stepsize L sigma D N =
      min (1 / L) (D / (sigma * Real.sqrt (N : ℝ))) := by
  rfl

/-- The clipped variance-balanced stepsize is bounded by the inverse
Lipschitz scale.

Layer: Model | Gap: Level 0 (clipped stepsize inverse-Lipschitz upper bound)
Proof: the selector is a minimum whose left branch is `1 / L`.
Source: Mathlib lattice minimum API for real scalar parameter choices
Used in: verifying smooth-descent constant-stepsize feasibility bounds -/
theorem min_inv_lipschitz_sqrt_horizon_stepsize_le_inv_lipschitz
    (L sigma D : ℝ) (N : Nat) :
    min_inv_lipschitz_sqrt_horizon_stepsize L sigma D N ≤ 1 / L := by
  rw [min_inv_lipschitz_sqrt_horizon_stepsize_def]
  exact min_le_left _ _

/-- The clipped variance-balanced stepsize is bounded by its
square-root-horizon balance branch.

Layer: Model | Gap: Level 0 (clipped stepsize variance-balance upper bound)
Proof: the selector is a minimum whose right branch is
  `D / (sigma * sqrt N)`.
Source: Mathlib lattice minimum API for real scalar parameter choices
Used in: converting constant-stepsize smooth-descent bounds into
  square-root-horizon rates -/
theorem min_inv_lipschitz_sqrt_horizon_stepsize_le_sqrt_horizon_balance
    (L sigma D : ℝ) (N : Nat) :
    min_inv_lipschitz_sqrt_horizon_stepsize L sigma D N ≤
      D / (sigma * Real.sqrt (N : ℝ)) := by
  rw [min_inv_lipschitz_sqrt_horizon_stepsize_def]
  exact min_le_right _ _

/-- The square-root-horizon denominator is nonzero on a positive horizon with
positive noise scale.

Layer: Model | Gap: Level 0 (square-root-horizon denominator nonzero)
Proof: `1 <= N` makes `sqrt (N : Real)` positive, and multiplying by a positive
  `sigma` preserves nonzeroness.
Source: Mathlib real square-root positivity, natural-number casts, and ordered-field multiplication APIs
Used in: validating the denominator of the nonconvex stochastic-gradient variance-balanced constant stepsize
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem min_inv_lipschitz_sqrt_horizon_stepsize_denominator_ne_zero
    (sigma : ℝ) (N : Nat) (hN : 1 ≤ N) (hsigma : 0 < sigma) :
    sigma * Real.sqrt (N : ℝ) ≠ 0 := by
  apply mul_ne_zero (ne_of_gt hsigma)
  exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hN))

end SOptLib
