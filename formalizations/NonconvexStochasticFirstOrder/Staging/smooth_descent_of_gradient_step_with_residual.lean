import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: smooth descent of a gradient step with an additive residual;
--   orig was `setup_smooth_residual_descent_pointwise`.
-- generality used: an arbitrary real inner-product space `E`, objective
--   `f : E -> ℝ`, gradient field `grad : E -> E`, smoothness scalar `L`,
--   stepsize `η`, base point `x`, and residual `δ`; no measure,
--   independence, integrability, convexity, completeness, or finite-dimensional
--   assumptions are needed once the pointwise smooth upper model is supplied.
-- portable call pattern: SGD, noisy-gradient descent, stochastic recursive
--   momentum, and variance-reduced gradient proofs call this after expressing
--   their next point as `x - η • (grad x + δ)`; the objective, gradient,
--   stepsize, current point, residual, and smooth upper-model proof vary while
--   the explicit three-coefficient conclusion stays fixed.
-- counterargument checked: the candidate is not paper-local traceability or a
-- caller-side expression because it packages the nontrivial Hilbert-space
-- expansion of a smooth upper model through an additive gradient residual.
-- The existing `smooth_descent_affine_update_with_direction_error` theorem in
-- `SOptLib/Layer1/Descent.lean` is only partial: it requires a small-stepsize
-- bound and concludes with absorbed gradient/error squares, not the exact
-- gradient-square, cross-term, and residual-square coefficients here.
-- coverage search: queried `smooth descent gradient step residual pointwise
-- quadratic upper bound inner product norm square`, `smooth descent affine
-- update direction error residual gradient norm cross term`, and the same
-- statement through Mathlib LeanSearch. Relevant hits were
-- `smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`,
-- `smooth_descent_affine_update_with_direction_error`, and generic
-- `norm_add_sq_real`; coverage is partial, not full.
-- minimal hypotheses: the global smoothness assumptions are reduced to the
-- single pointwise upper-model inequality at the displayed update, and all
-- remaining typeclasses are exactly those required by real inner-product and
-- scalar-norm algebra.

/-- A smooth upper model at a gradient step expands into explicit gradient,
residual-cross, and residual-square coefficients.

Layer: Layer1 | Gap: Level 1 (smooth gradient-step residual expansion)
Proof: rewrite the update displacement as `-η • (grad x + δ)`, expand its
  inner product and squared norm in a real inner-product space, and normalize
  the scalar coefficients by ring arithmetic.
Source: Mathlib real inner-product bilinearity, norm-square polarization, scalar
  norm identities, and ordered-ring normalization
Used in: stochastic-gradient and noisy-gradient one-step descent before
  summing weighted gradient bounds and cancelling or bounding residual terms
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/key_lemmas/0/proof/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem smooth_descent_of_gradient_step_with_residual
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (L η : ℝ) (x δ : E)
    (hsmooth :
      f (x - η • (grad x + δ)) ≤
        f x + ⟪grad x, x - η • (grad x + δ) - x⟫_ℝ +
          (L / 2) * ‖x - η • (grad x + δ) - x‖ ^ 2) :
    f (x - η • (grad x + δ)) ≤
      f x -
        (η - L / 2 * η ^ 2) * ‖grad x‖ ^ 2 -
        (η - L * η ^ 2) * ⟪grad x, δ⟫_ℝ +
        (L / 2) * η ^ 2 * ‖δ‖ ^ 2 := by
  let g : E := grad x
  have hdisp : x - η • (g + δ) - x = -(η • (g + δ)) := by
    abel
  have hinner :
      ⟪g, x - η • (g + δ) - x⟫_ℝ =
        -η * ‖g‖ ^ 2 - η * ⟪g, δ⟫_ℝ := by
    rw [hdisp]
    simp [inner_add_right, inner_smul_right]
    ring
  have hnorm :
      ‖x - η • (g + δ) - x‖ ^ 2 =
        η ^ 2 * (‖g‖ ^ 2 + 2 * ⟪g, δ⟫_ℝ + ‖δ‖ ^ 2) := by
    calc
      ‖x - η • (g + δ) - x‖ ^ 2 = ‖-(η • (g + δ))‖ ^ 2 := by
        rw [hdisp]
      _ = ‖η • (g + δ)‖ ^ 2 := by
        rw [norm_neg]
      _ = η ^ 2 * ‖g + δ‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ = η ^ 2 * (‖g‖ ^ 2 + 2 * ⟪g, δ⟫_ℝ + ‖δ‖ ^ 2) := by
        rw [norm_add_sq_real]
  calc
    f (x - η • (grad x + δ)) =
        f (x - η • (g + δ)) := by simp [g]
    _ ≤ f x + ⟪g, x - η • (g + δ) - x⟫_ℝ +
          (L / 2) * ‖x - η • (g + δ) - x‖ ^ 2 := by
      simpa [g] using hsmooth
    _ = f x -
          (η - L / 2 * η ^ 2) * ‖g‖ ^ 2 -
          (η - L * η ^ 2) * ⟪g, δ⟫_ℝ +
          (L / 2) * η ^ 2 * ‖δ‖ ^ 2 := by
      rw [hinner, hnorm]
      ring
    _ = f x -
          (η - L / 2 * η ^ 2) * ‖grad x‖ ^ 2 -
          (η - L * η ^ 2) * ⟪grad x, δ⟫_ℝ +
          (L / 2) * η ^ 2 * ‖δ‖ ^ 2 := by
      simp [g]
