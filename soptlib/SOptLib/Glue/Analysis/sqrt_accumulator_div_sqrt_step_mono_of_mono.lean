import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: adjacent ratio monotonicity for a nonnegative square-root accumulator under a reciprocal-square-root step schedule; orig was generated_inverse_learning_rate_mono.
-- generality used: real-valued natural-time sequences, a finite one-based horizon, pointwise nonnegative square-root witnesses, coordinate-free accumulator monotonicity, and a positive base stepsize; no measure, filtration, optimization, oracle, norm, inner-product, convexity, smoothness, or finite-dimensional assumptions are used.
-- portable call pattern: adaptive-gradient, AdaGrad-style, and diagonal preconditioner proofs instantiate `v` with an accumulated scale, `sqrtv` with its root witness, and `alpha_t` with the active step schedule; the horizon and pointwise monotonicity witnesses vary while the adjacent quotient conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the theorem packages the nontrivial bridge from accumulator order plus `alpha_t = alpha / sqrt(t)` to the inverse-step ratio order; it is more than a caller-side expression or a pure specialization of `Real.sqrt_le_sqrt`.
-- coverage search: searched `ratio monotonicity nonnegative sequence square root step schedule`, `monotonicity ratio nonnegative square root accumulator`, and `sqrt accumulator divided by sqrt step monotone`; Mathlib supplied only square-root/order and division primitives, while SOptLib's ratio hits concern accelerated finite-window contracts and do not cover this accumulator-plus-schedule conclusion.
-- minimal hypotheses: the AMSGrad setup is reduced to a positive base stepsize, pointwise root specifications, pointwise accumulator monotonicity on adjacent active times, and the schedule identity `sqrt(t) * alpha_t t = alpha`.

/-- A nonnegative square-root accumulator divided by a reciprocal-square-root
step schedule is nondecreasing across adjacent positive times.

If `sqrtv` is a nonnegative square-root witness for an accumulator `v` that is
nondecreasing on a finite horizon, and `alpha_t` satisfies
`Real.sqrt t * alpha_t t = alpha` for a positive base stepsize, then
`sqrtv (t - 1) / alpha_t (t - 1) ≤ sqrtv t / alpha_t t`.

Layer: Glue | Gap: Level 1 (accumulator-to-inverse-step ratio monotonicity)
Proof: derive monotonicity of the supplied square-root witnesses from the
  accumulator order, compare the positive natural-time square roots, and
  normalize both quotients by the positive base stepsize.
Source: Mathlib real square-root order and square identities, natural-number
  interval arithmetic, and ordered-field division APIs
Used in: adaptive-coordinate regret and metric telescopes where a
  nondecreasing diagonal accumulator is paired with an `alpha / sqrt(t)` step
  schedule
Book citation: book/ICLR2018/AMSGrad.json#/main_theorem/proof/4
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem sqrt_accumulator_div_sqrt_step_mono_of_mono
    (alpha : ℝ) (v sqrtv alpha_t : ℕ → ℝ) (T : ℕ)
    (h_alpha_pos : 0 < alpha)
    (h_sqrt_spec :
      ∀ t ∈ Finset.Icc 1 T, 0 ≤ sqrtv t ∧ sqrtv t ^ 2 = v t)
    (h_v_mono :
      ∀ t ∈ Finset.Icc 2 T, v (t - 1) ≤ v t)
    (h_step_schedule :
      ∀ t ∈ Finset.Icc 1 T,
        Real.sqrt (t : ℝ) * alpha_t t = alpha) :
    ∀ t ∈ Finset.Icc 2 T,
      sqrtv (t - 1) / alpha_t (t - 1) ≤ sqrtv t / alpha_t t := by
  intro t ht
  have ht_low : 2 ≤ t := (Finset.mem_Icc.mp ht).1
  have ht_high : t ≤ T := (Finset.mem_Icc.mp ht).2
  have ht_mem : t ∈ Finset.Icc 1 T :=
    Finset.mem_Icc.mpr ⟨by omega, ht_high⟩
  have ht_pred_mem : t - 1 ∈ Finset.Icc 1 T :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hprev := h_sqrt_spec (t - 1) ht_pred_mem
  have hcur := h_sqrt_spec t ht_mem
  have hsq :
      (sqrtv (t - 1)) ^ 2 ≤ (sqrtv t) ^ 2 := by
    rw [hprev.2, hcur.2]
    exact h_v_mono t ht
  have hsqrtv_mono : sqrtv (t - 1) ≤ sqrtv t := by
    have habs := sq_le_sq.mp hsq
    simpa [abs_of_nonneg hprev.1, abs_of_nonneg hcur.1] using habs
  have ht_pred_real_pos : 0 < ((t - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < t - 1 by omega)
  have ht_real_pos : 0 < (t : ℝ) := by
    exact_mod_cast (show 0 < t by omega)
  have hsqrt_pred_pos : 0 < Real.sqrt ((t - 1 : ℕ) : ℝ) :=
    Real.sqrt_pos.2 ht_pred_real_pos
  have hsqrt_cur_pos : 0 < Real.sqrt (t : ℝ) :=
    Real.sqrt_pos.2 ht_real_pos
  have hsqrt_pred_le_cur :
      Real.sqrt ((t - 1 : ℕ) : ℝ) ≤ Real.sqrt (t : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (Nat.sub_le t 1)
  have halpha_pred_pos : 0 < alpha_t (t - 1) := by
    have hpred_schedule := h_step_schedule (t - 1) ht_pred_mem
    have hpred_eq :
        alpha_t (t - 1) =
          alpha / Real.sqrt ((t - 1 : ℕ) : ℝ) := by
      apply (eq_div_iff (ne_of_gt hsqrt_pred_pos)).2
      simpa [mul_comm] using hpred_schedule
    rw [hpred_eq]
    exact div_pos h_alpha_pos hsqrt_pred_pos
  have halpha_cur_pos : 0 < alpha_t t := by
    have hcur_schedule := h_step_schedule t ht_mem
    have hcur_eq :
        alpha_t t = alpha / Real.sqrt (t : ℝ) := by
      apply (eq_div_iff (ne_of_gt hsqrt_cur_pos)).2
      simpa [mul_comm] using hcur_schedule
    rw [hcur_eq]
    exact div_pos h_alpha_pos hsqrt_cur_pos
  have hprod :
      sqrtv (t - 1) * Real.sqrt ((t - 1 : ℕ) : ℝ) ≤
        sqrtv t * Real.sqrt (t : ℝ) := by
    calc
      sqrtv (t - 1) * Real.sqrt ((t - 1 : ℕ) : ℝ)
          ≤ sqrtv t * Real.sqrt ((t - 1 : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_right hsqrtv_mono hsqrt_pred_pos.le
      _ ≤ sqrtv t * Real.sqrt (t : ℝ) := by
            exact mul_le_mul_of_nonneg_left hsqrt_pred_le_cur hcur.1
  have hprev_ratio_eq :
      sqrtv (t - 1) / alpha_t (t - 1) =
        sqrtv (t - 1) * Real.sqrt ((t - 1 : ℕ) : ℝ) / alpha := by
    rw [← h_step_schedule (t - 1) ht_pred_mem]
    field_simp [ne_of_gt hsqrt_pred_pos, ne_of_gt halpha_pred_pos]
  have hcur_ratio_eq :
      sqrtv t / alpha_t t =
        sqrtv t * Real.sqrt (t : ℝ) / alpha := by
    rw [← h_step_schedule t ht_mem]
    field_simp [ne_of_gt hsqrt_cur_pos, ne_of_gt halpha_cur_pos]
  calc
    sqrtv (t - 1) / alpha_t (t - 1)
        = sqrtv (t - 1) * Real.sqrt ((t - 1 : ℕ) : ℝ) / alpha :=
          hprev_ratio_eq
    _ ≤ sqrtv t * Real.sqrt (t : ℝ) / alpha := by
      exact div_le_div_of_nonneg_right hprod h_alpha_pos.le
    _ = sqrtv t / alpha_t t := hcur_ratio_eq.symm
