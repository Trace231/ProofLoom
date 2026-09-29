import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-window smooth descent stepsize feasibility; orig was
--   RSGDStepsizeFeasible.
-- generality used: arbitrary finite index set, real smoothness parameter, and
--   real stepsize schedule; no measure, independence, integrability,
--   convexity, oracle, normed-space, or finite-dimensional assumptions are used.
-- portable call pattern: SGD, mirror descent, randomized-output descent, and
--   block/prox descent proofs use an output window of iteration indices and
--   require every selected stepsize to satisfy the strict smoothness bound
--   `gamma t < 2 / L`; the index type, finite window, smoothness constant, and
--   schedule vary while the conclusion stays the same.
-- counterargument checked: the source declaration is a short Prop-valued
--   wrapper, but it names a recurring descent-domain contract rather than a
--   paper-local traceability boundary; Mathlib has no optimization-specific
--   predicate for this finite-window reciprocal-smoothness bound.
-- coverage search: queried "finite set stepsize schedule strictly less than
--   two over smoothness constant", "stepsize feasible on finite set gamma less
--   than 2 divided by L", and "smooth descent stepsize feasible finite
--   window strict bound"; hits included the paper-local RSGD predicate,
--   halfLipschitzStepSizeSchedule, min_block_descent_factor_nonneg_of_pos_of_lt_two_div,
--   and AcceleratedFiniteWindowScalarStepCondition, but none provide this
--   standalone finite-window feasibility predicate.
-- minimal hypotheses: all already minimal; the definition uses only membership
--   in `times` and the pointwise strict upper bound.

/-- Finite-window feasibility for a smooth-descent stepsize schedule.

The predicate records that every stepsize selected by a finite output window is
strictly below the reciprocal smoothness threshold `2 / L`.

Layer: Model | Concept: finite-window smooth descent stepsize feasibility
Proof: (definitional construction; finite-set pointwise strict upper bound for
  a real-valued stepsize schedule)
Source: smooth first-order descent stepsize restrictions and Mathlib finite-set
  membership quantification
Used in: randomized-output stochastic-gradient stationarity bounds before
  constructing the stopping law from weights `2 * gamma t - L * gamma t ^ 2`
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
def smoothDescentStepsizeFeasibleOn
    {T : Type*} (times : Finset T) (L : ℝ) (gamma : T → ℝ) : Prop :=
  ∀ t, t ∈ times → gamma t < 2 / L

/-- The finite-window smooth-descent feasibility predicate unfolds to a
pointwise strict upper bound on the selected indices.

Layer: Model | Gap: Level 0 (finite-window stepsize-feasibility unfolding)
Proof: by rfl after unfolding `smoothDescentStepsizeFeasibleOn`.
Source: smooth first-order descent stepsize restrictions and Mathlib finite-set
  membership quantification
Used in: exposing randomized-output stochastic-gradient stepsize feasibility as
  a pointwise bound on the output window
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
@[simp]
theorem smoothDescentStepsizeFeasibleOn_def
    {T : Type*} (times : Finset T) (L : ℝ) (gamma : T → ℝ) :
    smoothDescentStepsizeFeasibleOn times L gamma ↔
      ∀ t, t ∈ times → gamma t < 2 / L := by
  rfl

end SOptLib
