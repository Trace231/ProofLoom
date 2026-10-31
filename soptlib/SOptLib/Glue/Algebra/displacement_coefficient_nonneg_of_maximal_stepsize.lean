import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: nonnegative displacement coefficient under a maximal square-root stepsize; orig was theoremOne_displacement_coefficient_nonneg
-- generality used: real smoothness scale L, probability p, secondary batch scale b, and stepsize η; no measure, independence, integrability, optimization, or finite-dimensional assumptions are needed.
-- portable call pattern: a stochastic-gradient Lyapunov proof changes L, p, the secondary batch size b, and the stepsize while retaining the maximal reciprocal-square-root identity and uses the resulting nonnegative displacement coefficient.
-- counterargument checked: the source theorem is paper-local in its hypotheses, but its proof is a reusable scalar ordered-field argument; Mathlib has the square-root and field APIs but no theorem packaging this coefficient contract.
-- coverage search: searched "nonnegative displacement coefficient maximal square root stepsize" and "coefficient nonnegative maximal stepsize square root" across SOptLib and Mathlib; hits were unrelated adaptive-step and square-norm lemmas, so coverage was partial and non-duplicative.
-- minimal hypotheses: replaced the source smoothness and schedule structures by the pointwise facts actually used: 0 < L, 0 < p, p ≤ 1, 0 < b, and the maximal stepsize equality.

/-- The maximal reciprocal-square-root stepsize makes the displacement coefficient
nonnegative in the collected Lyapunov inequality.

Layer: Glue | Gap: Level 1 (maximal stepsize coefficient sign)
Proof: introduce the square-root ratio, clear its defining denominator, and use
ordered-field arithmetic after substituting the maximal stepsize identity.
Source: Mathlib real square-root identities and ordered-field arithmetic
Used in: stochastic-gradient Lyapunov telescopes that drop a squared-displacement term after choosing the maximal variance-balanced stepsize
Book citation: book/research/PAGE.json#/main_theorem/proof/12
Origin algorithm: Li, Bao, Zhang, and Richtarik - PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization (Theorem 1) -/
theorem displacement_coefficient_nonneg_of_maximal_stepsize
    {L p b η : ℝ}
    (hL_pos : 0 < L)
    (hp_pos : 0 < p)
    (hp_le_one : p ≤ 1)
    (hb_pos : 0 < b)
    (hη_eq : η = (L * (1 + Real.sqrt ((1 - p) / (p * b))))⁻¹) :
    0 ≤ (2 * η)⁻¹ - L / 2 - ((1 - p) * η * L ^ 2) / (2 * p * b) := by
  let r : ℝ := Real.sqrt ((1 - p) / (p * b))
  have hratio_nonneg : 0 ≤ (1 - p) / (p * b) := by
    exact div_nonneg (sub_nonneg.mpr hp_le_one)
      (mul_nonneg hp_pos.le hb_pos.le)
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = (1 - p) / (p * b) := by
    simpa [r] using Real.sq_sqrt hratio_nonneg
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hpb_ne : p * b ≠ 0 := mul_ne_zero hp_ne hb_ne
  have hrsq_clear : r ^ 2 * (p * b) = 1 - p :=
    (eq_div_iff hpb_ne).mp hrsq
  have h_one_add_r_pos : 0 < 1 + r := by linarith
  have h_one_add_r_ne : 1 + r ≠ 0 := ne_of_gt h_one_add_r_pos
  rw [hη_eq]
  change 0 ≤
    (2 * (L * (1 + r))⁻¹)⁻¹ - L / 2 -
      ((1 - p) * (L * (1 + r))⁻¹ * L ^ 2) / (2 * p * b)
  have hcalc :
      (2 * (L * (1 + r))⁻¹)⁻¹ - L / 2 -
          ((1 - p) * (L * (1 + r))⁻¹ * L ^ 2) / (2 * p * b) =
        L * r / (2 * (1 + r)) := by
    field_simp [hL_ne, hp_ne, hb_ne, h_one_add_r_ne]
    nlinarith [hrsq_clear]
  rw [hcalc]
  exact div_nonneg (mul_nonneg hL_pos.le hr_nonneg)
    (mul_nonneg (by norm_num) h_one_add_r_pos.le)
