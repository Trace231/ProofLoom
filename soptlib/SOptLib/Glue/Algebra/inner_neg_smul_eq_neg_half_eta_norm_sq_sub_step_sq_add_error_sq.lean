import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: exact negative-step inner-product polarization identity; orig was
--   the PAGE-local `inexact_gradient_step_inner_identity`, renamed away from
--   the algorithm and its inexact-gradient terminology.
-- generality used: a seminormed real inner-product space, a nonzero real step
--   size, and two vectors; no measure, probability, oracle, objective,
--   smoothness, or finite-dimensional assumptions are used.
-- portable call pattern: gradient, stochastic-gradient, variance-reduced, and
--   proximal one-step proofs can change η, the reference vector, and the
--   direction while reusing the same exact polarization decomposition of
--   `⟪a, -η • g⟫` into the reference, step, and error norm squares.
-- counterargument checked: this is a substantive Hilbert-space algebra bridge,
--   not paper-local traceability or a caller-side expression; Mathlib supplies
--   the component polarization lemmas but no theorem with this combined
--   scaled-step/error conclusion, and SOptLib search found only inequalities or
--   a different affine-update distance identity.
-- coverage search: queried `inner product negative scalar step norm squared error
--   squared polarization identity`, `inner negative eta smul exact norm identity`,
--   and `update inner squared distance`; closest hits were Mathlib
--   `norm_sub_sq_real`, SOptLib `inner_update_eq_sq_dist_sub_sq_dist_add_norm_sq`,
--   and `inner_neg_smul_add_half_mul_norm_sq_le_of_le_inv_four_mul`, all partial
--   or structurally different.
-- minimal hypotheses: `[SeminormedAddCommGroup V] [InnerProductSpace ℝ V]` and
--   `η ≠ 0` are exactly those used to clear the nonzero scalar and expand norms.

/-- The inner product with a negative scaled direction decomposes into reference,
step, and error squared norms.

Layer: Glue | Gap: Level 1 (Hilbert negative-step polarization identity)
Proof: Expand `‖g - a‖²` with real inner-product polarization, rewrite the norm
of `-η • g`, and clear the nonzero step-size denominator by field arithmetic.
Source: Mathlib real inner-product polarization (`norm_sub_sq_real`), scalar-norm,
and inner-product bilinearity APIs.
Used in: one-step smoothness/descent proofs after substituting a gradient or
inexact-gradient update `xNext = x - η • g`, where the inner product against the
full gradient is rewritten into a negative gradient square, update square, and
estimation-error square.
Book citation: book/research/PAGE.json#/key_lemmas/1
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem inner_neg_smul_eq_neg_half_eta_norm_sq_sub_step_sq_add_error_sq
    {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    {η : ℝ} (hη : η ≠ 0) (a g : V) :
    inner ℝ a (-η • g) =
      -(η / 2) * ‖a‖ ^ 2 -
        (2 * η)⁻¹ * ‖-η • g‖ ^ 2 +
        (η / 2) * ‖g - a‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, norm_neg]
  rw [Real.norm_eq_abs, mul_pow, sq_abs]
  simp [inner_smul_right, real_inner_comm]
  field_simp [hη]
  ring

end SOptLib
