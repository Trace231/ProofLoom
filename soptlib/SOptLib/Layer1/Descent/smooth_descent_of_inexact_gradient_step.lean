import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import SOptLib.Glue.Algebra.inner_neg_smul_eq_neg_half_eta_norm_sq_sub_step_sq_add_error_sq
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: exact inexact-gradient smooth descent step; orig was the PAGE-local `descent_with_inexact_gradient`
-- generality used: a seminormed real inner-product space, arbitrary objective and direction field, explicit current and next points, a supplied quadratic upper model, and a positive real stepsize; no measure, probability, completeness, finite-dimensionality, or convexity assumptions are used
-- portable call pattern: biased SGD, stochastic-gradient, PAGE/SPIDER/SARAH, and other variance-reduced proofs provide their pointwise quadratic upper model and affine update `xNext = x - η • g`, then reuse the same exact gradient-square, displacement-square, and direction-error inequality
-- counterargument checked: the nearby affine-direction descent theorem requires `0 < L` and `η ≤ 1 / (4 * L)` and has a different absorbed conclusion; this theorem retains the exact inverse-stepsize coefficient and therefore is not a duplicate, caller-side wrapper, or paper-only traceability boundary
-- coverage search: searched `smooth descent inexact gradient quadratic upper bound positive step`, `objective xNext x - eta smul direction error`, and SOptLib/Layer1/Descent; the closest hit was `smooth_descent_affine_update_with_direction_error`, which is structurally different and only partial
-- minimal hypotheses: `[SeminormedAddCommGroup E] [InnerProductSpace ℝ E]`, a pointwise quadratic upper model, the affine update equality, and `0 < η`; all completeness, finite-dimensional, measure, and smoothness-positivity assumptions are unnecessary

/-- A quadratic upper model and an inexact-gradient affine step give the exact
one-step descent inequality with a squared direction-error penalty.

The update is `xNext = x - η • g`; the conclusion keeps the displacement
coefficient `((2 * η)⁻¹ - L / 2)` explicit, so callers can later use any
stepsize or smoothness side condition available in their analysis.

Layer: Layer1 | Gap: Level 1 (inexact-gradient smooth descent algebra)
Proof: rewrite the supplied upper model through the affine update, use the
negative-step inner-product polarization identity, and collect the quadratic
terms by ring normalization.
Source: smooth first-order descent calculus in real inner-product spaces,
Mathlib inner-product bilinearity, and the staged negative-step polarization identity
Used in: PAGE, SPIDER, SARAH, biased SGD, and stochastic-gradient one-step bounds before integrating objective decrease and estimator-error moments
Book citation: book/research/PAGE.json#/key_lemmas/1
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem smooth_descent_of_inexact_gradient_step
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (x xNext g : E) (η L : ℝ)
    (h_smooth :
      f xNext ≤
        f x + inner ℝ (grad x) (xNext - x) + (L / 2) * ‖xNext - x‖ ^ 2)
    (h_update : xNext = x - η • g) (hη : 0 < η) :
    f xNext ≤
      f x - (η / 2) * ‖grad x‖ ^ 2 -
        ((2 * η)⁻¹ - L / 2) * ‖xNext - x‖ ^ 2 +
        (η / 2) * ‖g - grad x‖ ^ 2 := by
  have hinner :
      inner ℝ (grad x) (-η • g) =
        -(η / 2) * ‖grad x‖ ^ 2 -
          (2 * η)⁻¹ * ‖-η • g‖ ^ 2 +
          (η / 2) * ‖g - grad x‖ ^ 2 :=
    inner_neg_smul_eq_neg_half_eta_norm_sq_sub_step_sq_add_error_sq
      (ne_of_gt hη) (grad x) g
  have hdisp : xNext - x = -η • g := by
    rw [h_update]
    simp [sub_eq_add_neg, add_comm, add_left_comm, neg_smul]
  calc
    f xNext ≤
        f x + inner ℝ (grad x) (-η • g) + (L / 2) * ‖-η • g‖ ^ 2 := by
      simpa [hdisp] using h_smooth
    _ = f x - (η / 2) * ‖grad x‖ ^ 2 -
        ((2 * η)⁻¹ - L / 2) * ‖xNext - x‖ ^ 2 +
        (η / 2) * ‖g - grad x‖ ^ 2 := by
      rw [hinner, hdisp]
      ring

end SOptLib
