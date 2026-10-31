import SOptLib.Glue.Algebra

-- Generalization plan (G0):
-- concept/name: complementary ratio over a positive denominator; orig was the PAGE-local `hratio`
-- generality used: an arbitrary field with a linear order and strict ordered-ring structure, plus positive scalars `b`, `b'`; no measure, convexity, smoothness, oracle, or optimization assumptions are used
-- portable call pattern: stochastic-optimization rate and batch-cost proofs can instantiate any positive real (or ordered-field) scales before square-root normalization; only the two scales and their positivity proofs change
-- counterargument checked: this is a substantive denominator-clearing identity used across batch-ratio calculations, rather than paper traceability or a caller-side name; no matching Mathlib/SOptLib theorem was found
-- coverage search: searched `one sub division division multiplication equal quotient square positive`, `batch ratio algebra`, `div_sq`, and Glue/Algebra; existing ordered-field lemmas were lower-level and no complete identity was present
-- minimal hypotheses: `[Field K] [LinearOrder K] [IsStrictOrderedRing K]` plus `0 < b` and `0 < b'` suffice; the proof uses positivity only to establish nonzero denominators

/-- The complementary ratio `(1 - b'/(b+b')) / ((b'/(b+b')) * b')`
equals `b / b'^2` for positive scales.

Layer: Glue | Gap: Level 1 (positive batch-ratio denominator normalization)
Proof: clear the positive denominators with `field_simp`, then close the resulting polynomial identity with `ring`.
Source: Mathlib ordered-field division, positivity, and ring-normalization tactics
Used in: stochastic-optimization rate proofs that substitute a refresh probability `b'/(b+b')` before applying square-root normalization to the resulting batch ratio
Book citation: book/research/PAGE.json#/extension/additions/main_theorem/proof/0
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization (Corollary 2) -/
theorem one_sub_div_div_mul_eq_div_sq_of_pos
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {b b' : K}
    (hb : 0 < b) (hb' : 0 < b') :
    (1 - b' / (b + b')) / ((b' / (b + b')) * b') =
      b / b' ^ 2 := by
  have hsum : b + b' ≠ 0 := by positivity
  field_simp [hsum, ne_of_gt hb']
  ring
