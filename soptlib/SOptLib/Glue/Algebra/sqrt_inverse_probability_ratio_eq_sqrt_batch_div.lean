import SOptLib.Glue.Algebra
import SOptLib.Glue.Algebra.one_sub_div_div_mul_eq_div_sq_of_pos
-- Generalization plan (G0):
-- concept/name: square-root normalization of the complementary refresh-probability ratio; orig was `corollaryTwo_ratio_identity`
-- generality used: positive real batch scales `b` and `b'`; no measure, convexity, smoothness, oracle, or optimization assumptions are used
-- portable call pattern: any two-branch stochastic method choosing refresh probability `p = b' / (b + b')` can normalize its reciprocal recursive-branch factor; only the positive scales change
-- counterargument checked: this is a substantive reusable scalar normalization composing denominator clearing with square-root identities, not paper traceability or a caller-side wrapper; no complete Mathlib/SOptLib result was found
-- coverage search: queried `sqrt ratio positive probability batch scales`, `sqrt div square positive ratio`, and `Glue/Algebra`; only the lower-level staged denominator identity `one_sub_div_div_mul_eq_div_sq_of_pos` matched partially
-- minimal hypotheses: positivity of both real scales is sufficient and is used to establish nonzero denominators and remove the absolute value

/-- The square-root ratio induced by refresh probability `b' / (b + b')`
equals `sqrt b / b'` for positive real batch scales.

Layer: Glue | Gap: Level 1 (square-root refresh-ratio normalization)
Proof: reduce the complementary probability ratio to `b / b'^2` with the positive denominator identity, then apply real square-root division and positivity of `b'`.
Source: Mathlib real square-root division and ordered-field arithmetic, together with the positive denominator normalization for ordered fields
Used in: two-branch stochastic-optimization rate proofs that substitute the batch-size refresh probability before displaying the square-root complexity factor
Book citation: book/research/PAGE.json#/extension/additions/main_theorem/proof/0
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization (Corollary 2) -/
theorem sqrt_inverse_probability_ratio_eq_sqrt_batch_div
    {b b' : ℝ} (hb : 0 < b) (hb' : 0 < b') :
    Real.sqrt ((1 - b' / (b + b')) / ((b' / (b + b')) * b')) =
      Real.sqrt b / b' := by
  have hratio :
      (1 - b' / (b + b')) / ((b' / (b + b')) * b') =
        b / b' ^ 2 := by
    exact one_sub_div_div_mul_eq_div_sq_of_pos hb hb'
  rw [hratio]
  rw [Real.sqrt_div (by positivity : 0 ≤ b)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hb']
