import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: two-branch complexity factor under a square-root batch range; orig was `two_branch_complexity_factor_bound`
-- generality used: real batch scales `b`, `b'`, and a nonnegative real multiplier `q`; no measure, convexity, smoothness, or oracle assumptions are used
-- portable call pattern: gradient-complexity and rate proofs simplify a two-branch refresh cost after choosing probability `b' / (b + b')`; only the positive scales, multiplier, and range hypothesis change
-- counterargument checked: not paper-local traceability or a caller-side wrapper; the theorem composes denominator normalization, square-root range comparison, and monotone scaling into a reusable scalar envelope
-- coverage search: searched `batch range complexity factor`, `positive reals sqrt quotient product inequality`, and existing Glue/Algebra entries; nearby square-root rate lemmas were partial and no complete statement was found
-- minimal hypotheses: positivity of both batch scales, nonnegativity of the multiplier, and `b' ≤ sqrt b`; all other PAGE setup fields are removed

/-- A two-branch batch factor is bounded by a square-root rate under the batch range.

Layer: Glue | Gap: Level 1 (two-branch scalar complexity envelope)
Proof: first bound the normalized product by `2 * b'`, then use `b' ≤ sqrt b` to bound the resulting sum; monotonicity of multiplication by the nonnegative multiplier finishes the result.
Source: Mathlib real square-root order, positive-denominator division, and ordered-ring arithmetic
Used in: stochastic gradient-complexity proofs that replace the two-branch cost `2*b*b'/(b+b')` by the square-root rate after selecting the optimal refresh probability
Book citation: book/research/PAGE.json#/extension/additions/main_theorem/statement_math
Origin algorithm: Li, Bao, Zhang, and Richtarik - PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization (Corollary 2) -/
theorem two_branch_complexity_factor_le_of_batch_range
    {b b' q : ℝ}
    (hq : 0 ≤ q) (hb : 0 < b) (hb' : 0 < b')
    (h_range : b' ≤ Real.sqrt b) :
    q * ((1 + Real.sqrt b / b') * (2 * b * b' / (b + b'))) ≤
      q * (4 * Real.sqrt b) := by
  have hsum : 0 < b + b' := by positivity
  have hcost : 2 * b * b' / (b + b') ≤ 2 * b' := by
    have hfrac : b / (b + b') ≤ 1 := by
      exact (div_le_one hsum).2 (by nlinarith [hb'.le])
    have hmul :=
      mul_le_mul_of_nonneg_right hfrac
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb'.le)
    calc
      2 * b * b' / (b + b') = (b / (b + b')) * (2 * b') := by
        field_simp [ne_of_gt hsum]
      _ ≤ 1 * (2 * b') := hmul
      _ = 2 * b' := by ring
  have hfactor :
      (1 + Real.sqrt b / b') * (2 * b * b' / (b + b')) ≤
        4 * Real.sqrt b := by
    have hfactor' :
        (1 + Real.sqrt b / b') * (2 * b') ≤
          4 * Real.sqrt b := by
      have heq :
          (1 + Real.sqrt b / b') * (2 * b') =
            2 * b' + 2 * Real.sqrt b := by
        field_simp [ne_of_gt hb']
      rw [heq]
      nlinarith [Real.sqrt_nonneg b]
    exact
      le_trans
        (mul_le_mul_of_nonneg_left hcost
          (by positivity : 0 ≤ 1 + Real.sqrt b / b'))
        hfactor'
  exact mul_le_mul_of_nonneg_left hfactor hq
