-- Generalization plan (G0):
-- concept/name: finite_average_norm_sq_add_le_of_cross_zero bounds the average
--   squared norm of a fixed vector plus a finite family; orig was
--   line4_variance_fiber_square_expansion_block.
-- generality used: any finite index type and real inner-product space over a
--   seminormed additive commutative group; no measure, completeness, finite
--   dimension, convexity, smoothness, or oracle hypotheses.
-- portable call pattern: SARAH/SPIDER finite-sampling residual recurrences and
--   finite-noise perturbation bounds change the fixed vector, increment family,
--   and second-moment budget while retaining the same additive bound.
-- counterargument checked: this is finite averaged orthogonality, not a known
--   mean identity or pointwise orthogonality. The measure-level recurrence API
--   requires measurability and integrability; this algebraic contract supports
--   seminormed carriers and empty index types without those structures.
-- coverage search: queried "finite uniform average squared norm of sum bounded
--   by squared norm plus second moment when average inner product is zero",
--   "average norm squared addition upper bound cross zero", and "finite sum
--   squared norm add expansion inner product" with lean_search_symbols.
--   Full signatures inspected: finset_weighted_variance_eq_second_moment_sub_norm_mean_sq
--   requires a specified vector mean; second_moment_add_recurrence_le_of_cross_zero
--   is a measure-level recurrence; norm_add_sq_real is the pointwise expansion.
--   These give partial coverage, not this finite-average contract. LeanSearch
--   timed out; local Mathlib inner-product and finite-average sources were checked.
--   The round registry has no equivalent statement.
-- minimal hypotheses: only scalar averaged cross cancellation and an averaged
--   squared-norm bound are assumed; neither zero vector mean nor nonemptiness
--   nor a separate nonnegative-budget hypothesis is necessary.

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import SOptLib.Model.Selection

namespace SOptLib

/-- If the averaged cross inner product vanishes and the increment second moment
is at most `q`, the average of `‖u + r i‖²` is at most `‖u‖² + q`.

Layer: Glue | Gap: Level 1 (finite-average orthogonal perturbation second-moment bound)
Proof: expand with `norm_add_sq_real`, distribute the finite sums, use `finiteUniformAverage_const`, cancel the averaged cross term, and apply the moment bound. For an empty index type, use nonnegativity of the squared norm and the supplied bound.
Source: Mathlib real inner-product norm-square identities and finite sums; SOptLib finite uniform average and its constant-function specification
Used in: the recursive estimator variance proof after fixing the past, cancelling the old-error/increment cross average, and bounding the current sampling-row second moment
Book citation: book/research/PAGE.json#/key_lemmas/2/proof/6
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization, Algorithm 1 (PAGE) -/
theorem finite_average_norm_sq_add_le_of_cross_zero
    {R V : Type*} [Fintype R]
    [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (r : R → V) (q : ℝ)
    (hcross : finiteUniformAverage (fun i => inner ℝ u (r i)) = 0)
    (hmoment : finiteUniformAverage (fun i => ‖r i‖ ^ 2) ≤ q) :
    finiteUniformAverage (fun i => ‖u + r i‖ ^ 2) ≤ ‖u‖ ^ 2 + q := by
  classical
  rcases isEmpty_or_nonempty R with hR | hR
  · letI := hR
    simp only [finiteUniformAverage_def, Finset.univ_eq_empty, Finset.sum_empty,
      smul_zero] at hmoment ⊢
    exact add_nonneg (sq_nonneg _) hmoment
  · letI := hR
    have hexpand :
        finiteUniformAverage (fun i => ‖u + r i‖ ^ 2) =
          finiteUniformAverage (fun _ : R => ‖u‖ ^ 2) +
            2 * finiteUniformAverage (fun i => inner ℝ u (r i)) +
            finiteUniformAverage (fun i => ‖r i‖ ^ 2) := by
      simp only [finiteUniformAverage_def, smul_eq_mul, norm_add_sq_real,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    rw [hexpand, finiteUniformAverage_const, hcross, mul_zero, add_zero]
    calc
      ‖u‖ ^ 2 + finiteUniformAverage (fun i => ‖r i‖ ^ 2) ≤
          ‖u‖ ^ 2 + q := add_le_add_right hmoment _

end SOptLib
