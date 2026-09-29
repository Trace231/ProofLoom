import Mathlib.Tactic

/-- Bound a quotient by enlarging the denominator through `L * gamma <= 1`
and then splitting the numerator. -/
theorem sq_add_sq_mul_mul_sq_div_mul_sub_le_div_add_sq_mul_of_mul_le_one
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (D L sigma N gamma : K)
    (hN : 0 < N) (hgamma : 0 < gamma) (hLgamma : L * gamma <= 1) :
    (D ^ 2 + sigma ^ 2 * (N * gamma ^ 2)) /
        (N * (2 * gamma - L * gamma ^ 2)) <=
      D ^ 2 / (N * gamma) + sigma ^ 2 * gamma := by
  have hfactor_ge_one : 1 <= 2 - L * gamma := by linarith
  have hsmall_pos : 0 < N * gamma := mul_pos hN hgamma
  have hden_eq :
      N * (2 * gamma - L * gamma ^ 2) = (N * gamma) * (2 - L * gamma) := by
    ring
  have hden_le : N * gamma <= N * (2 * gamma - L * gamma ^ 2) := by
    rw [hden_eq]
    simpa using
      (mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hsmall_pos))
  have hnum_nonneg :
      0 <= D ^ 2 + sigma ^ 2 * (N * gamma ^ 2) := by
    have hprod_nonneg :
        0 <= sigma ^ 2 * (N * gamma ^ 2) :=
      mul_nonneg (sq_nonneg sigma)
        (mul_nonneg (le_of_lt hN) (sq_nonneg gamma))
    nlinarith [sq_nonneg D, hprod_nonneg]
  calc
    (D ^ 2 + sigma ^ 2 * (N * gamma ^ 2)) /
        (N * (2 * gamma - L * gamma ^ 2))
        <= (D ^ 2 + sigma ^ 2 * (N * gamma ^ 2)) / (N * gamma) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hsmall_pos hden_le
    _ = D ^ 2 / (N * gamma) + sigma ^ 2 * gamma := by
          field_simp [ne_of_gt hN, ne_of_gt hgamma]
