import Mathlib.Tactic
import SOptLib.Model.Iterates
import Staging.smoothDescentStepsizeFeasibleOn

open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: smooth-descent randomized-output weight; orig was
--   rsgdWeightFromStepsize.
-- generality used: arbitrary output index type, real smoothness constant, and
--   real stepsize schedule; no measure, independence, integrability,
--   convexity, oracle, normed-space, or finite-dimensional assumptions are
--   used.
-- portable call pattern: nonconvex SGD, stochastic mirror descent, and
--   randomized-output descent proofs use the same numerator weight
--   `2 * gamma t - L * gamma t ^ 2` before normalizing over a finite output
--   window; the index type, finite window, smoothness constant, and stepsize
--   schedule vary while the formula and positivity proof stay fixed.
-- counterargument checked: the declaration is formula-bodied, but it names a
--   recurring descent weight that travels with nonnegativity, positivity, and
--   denominator APIs; generic `normalizedOutputMass` and
--   `outputWeightDenominator` cover normalization, not this smooth-descent
--   numerator.
-- coverage search: queried "smooth descent output weight stepsize
--   nonnegative denominator normalized mass", "normalized output mass sum one
--   nonnegative denominator weights", "2 gamma minus L gamma squared
--   nonnegative less than two divided by L", and Mathlib LeanSearch for the
--   same ordered-field fact; hits covered generic normalized masses, finite
--   output denominators, block-descent output weights, and the already staged
--   stepsize-feasibility predicate, but not this scalar smooth-descent weight.
-- minimal hypotheses: the definition has only the scalar data it uses; the
--   positivity lemmas require exactly positive smoothness, positive or
--   nonnegative stepsize, and the reciprocal smoothness bound needed to make
--   `2 - L * gamma t` nonnegative or positive.

/-- The randomized-output numerator weight from a smooth descent step.

For a stepsize schedule `gamma` and smoothness constant `L`, this names the
scalar weight `2 * gamma t - L * gamma t ^ 2` used before finite-window
normalization in nonconvex smooth-descent output laws.

Layer: Model | Concept: smooth-descent randomized-output weight
Proof: (definitional construction; pointwise quadratic weight from a real
  stepsize schedule and smoothness constant)
Source: smooth first-order descent inequalities and Mathlib real polynomial
  arithmetic
Used in: randomized-output stochastic-gradient stopping laws before normalizing
  the finite family of descent weights into a PMF
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
noncomputable def smoothDescentOutputWeight
    {T : Type*} (L : ℝ) (gamma : T → ℝ) (t : T) : ℝ :=
  2 * gamma t - L * gamma t ^ 2

/-- The smooth-descent randomized-output weight unfolds to its quadratic
stepsize formula.

Layer: Model | Gap: Level 0 (smooth-descent output-weight unfolding)
Proof: by rfl after unfolding `smoothDescentOutputWeight`.
Source: smooth first-order descent inequalities and Mathlib real polynomial
  arithmetic
Used in: exposing the randomized-output stochastic-gradient stopping weight as
  the printed quadratic formula
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
@[simp]
theorem smoothDescentOutputWeight_def
    {T : Type*} (L : ℝ) (gamma : T → ℝ) (t : T) :
    smoothDescentOutputWeight L gamma t =
      2 * gamma t - L * gamma t ^ 2 := by
  rfl

/-- The smooth-descent output weight factors into the stepsize times the
remaining descent margin.

Layer: Model | Gap: Level 0 (smooth-descent output-weight factorization)
Proof: unfold the weight and normalize the quadratic expression by ring
  arithmetic.
Source: Mathlib commutative ring normalization for real polynomials
Used in: proving nonnegativity of randomized-output stochastic-gradient
  stopping weights from a reciprocal smoothness stepsize bound
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem smoothDescentOutputWeight_eq_mul_sub
    {T : Type*} (L : ℝ) (gamma : T → ℝ) (t : T) :
    smoothDescentOutputWeight L gamma t = gamma t * (2 - L * gamma t) := by
  rw [smoothDescentOutputWeight_def]
  ring

/-- The smooth-descent output weight is nonnegative under the closed
reciprocal smoothness stepsize bound.

Layer: Model | Gap: Level 1 (smooth-descent output-weight nonnegativity)
Proof: factor the quadratic weight, multiply the stepsize bound by the
  positive smoothness constant, and apply nonnegativity of products.
Source: Mathlib ordered-field arithmetic and smooth first-order descent
  stepsize restrictions
Used in: randomized-output stochastic-gradient stopping-law admissibility when
  constructing nonnegative PMF masses
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem smoothDescentOutputWeight_nonneg_of_nonneg_of_le_two_div
    {T : Type*} (L : ℝ) (gamma : T → ℝ) (t : T)
    (hL_pos : 0 < L)
    (hgamma_nonneg : 0 ≤ gamma t)
    (hgamma_le : gamma t ≤ 2 / L) :
    0 ≤ smoothDescentOutputWeight L gamma t := by
  rw [smoothDescentOutputWeight_eq_mul_sub]
  refine mul_nonneg hgamma_nonneg ?_
  have hmul : L * gamma t ≤ L * (2 / L) :=
    mul_le_mul_of_nonneg_left hgamma_le (le_of_lt hL_pos)
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have htwo : L * (2 / L) = 2 := by
    field_simp [hL_ne]
  nlinarith

/-- The smooth-descent output weight is positive under the strict reciprocal
smoothness stepsize bound.

Layer: Model | Gap: Level 1 (smooth-descent output-weight positivity)
Proof: factor the quadratic weight, multiply the strict stepsize bound by the
  positive smoothness constant, and apply positivity of products.
Source: Mathlib ordered-field arithmetic and smooth first-order descent
  stepsize restrictions
Used in: proving positive finite denominators for randomized-output
  stochastic-gradient stopping laws
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem smoothDescentOutputWeight_pos_of_pos_of_lt_two_div
    {T : Type*} (L : ℝ) (gamma : T → ℝ) (t : T)
    (hL_pos : 0 < L)
    (hgamma_pos : 0 < gamma t)
    (hgamma_lt : gamma t < 2 / L) :
    0 < smoothDescentOutputWeight L gamma t := by
  rw [smoothDescentOutputWeight_eq_mul_sub]
  refine mul_pos hgamma_pos ?_
  have hmul : L * gamma t < L * (2 / L) :=
    mul_lt_mul_of_pos_left hgamma_lt hL_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have htwo : L * (2 / L) = 2 := by
    field_simp [hL_ne]
  nlinarith

/-- A finite feasible smooth-descent stepsize schedule gives nonnegative
output weights on the selected window.

Layer: Model | Gap: Level 1 (finite-window smooth-descent output-weight nonnegativity)
Proof: specialize the finite-window feasibility predicate at each selected
  index and apply the pointwise output-weight nonnegativity lemma.
Source: Mathlib finite-set membership APIs and ordered-field smooth-descent
  stepsize algebra
Used in: randomized-output stochastic-gradient stopping-law admissibility over
  a finite set of candidate stopping times
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem smoothDescentOutputWeight_nonneg_on_of_feasible
    {T : Type*} (times : Finset T) (L : ℝ) (gamma : T → ℝ)
    (hL_pos : 0 < L)
    (hgamma_nonneg : ∀ t, t ∈ times → 0 ≤ gamma t)
    (hfeasible : smoothDescentStepsizeFeasibleOn times L gamma) :
    ∀ t, t ∈ times → 0 ≤ smoothDescentOutputWeight L gamma t := by
  intro t ht
  exact smoothDescentOutputWeight_nonneg_of_nonneg_of_le_two_div
    L gamma t hL_pos (hgamma_nonneg t ht) (le_of_lt (hfeasible t ht))

/-- Positive feasible smooth-descent stepsizes give a positive finite output
weight denominator.

Layer: Model | Gap: Level 1 (finite-window smooth-descent denominator positivity)
Proof: use strict pointwise positivity of the smooth-descent output weight on
  the window, then invoke the generic finite output-weight denominator
  positivity theorem.
Source: Mathlib finite sums over ordered real additive monoids and smooth
  first-order descent stepsize restrictions
Used in: randomized-output stochastic-gradient stopping laws before dividing
  by the total smooth-descent output weight
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem smoothDescentOutputWeight_denominator_pos_of_pos_of_feasible
    {T : Type*} (times : Finset T) (L : ℝ) (gamma : T → ℝ)
    (hL_pos : 0 < L)
    (hgamma_pos : ∀ t, t ∈ times → 0 < gamma t)
    (hfeasible : smoothDescentStepsizeFeasibleOn times L gamma)
    (htimes_nonempty : times.Nonempty) :
    0 < outputWeightDenominator times (smoothDescentOutputWeight L gamma) := by
  exact outputWeightDenominator_pos times (smoothDescentOutputWeight L gamma)
    (fun t ht =>
      smoothDescentOutputWeight_pos_of_pos_of_lt_two_div
        L gamma t hL_pos (hgamma_pos t ht) (hfeasible t ht))
    htimes_nonempty

end SOptLib
