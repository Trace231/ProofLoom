import SOptLib.Glue.Algebra.geometric_sq_div_le_gamma_abs_div_sqrt_one_sub_of_sqrt_quotient
import SOptLib.Glue.Algebra.sq_sum_Icc_geometric_abs_le_inv_one_sub_mul_sum_geometric_sq
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: pointwise adaptive-momentum squared numerator over square-root
--   accumulator bounded by a geometric gradient-history tail; orig was
--   generated_eq17_pointwise_adaptive_momentum_bound.
-- generality used: real scalar sequences indexed by natural time, with no
--   measure, filtration, convexity, smoothness, oracle, normed-space, or
--   finite-dimensional assumptions; coordinate and algorithm state are pushed
--   to caller-provided scalar histories.
-- portable call pattern: Adam/AMSGrad-style proofs instantiate the first-moment
--   coordinate, gradient history, retained square-root accumulator, beta/gamma
--   quotient witnesses, and inverse-square-root step schedule before summing
--   the Eq. (17)-style pointwise momentum contribution.
-- counterargument checked: not paper-local traceability because it composes the
--   recurring first-moment Cauchy bound, denominator transport, and step-size
--   scaling; not a duplicate because existing staged entries cover only the
--   geometric Cauchy and denominator-transport ingredients separately.
-- coverage search: searched `adaptive momentum square divided by sqrt
--   accumulator geometric history tail bound lower bound`, `geometric history
--   momentum squared denominator lower bound alpha schedule`, and `first moment
--   geometric history cauchy second moment lower denominator transport step
--   size alpha over sqrt time`; top SOptLib/project hits were
--   `sq_sum_Icc_geometric_abs_le_inv_one_sub_mul_sum_geometric_sq` and
--   `geometric_sq_div_le_gamma_abs_div_sqrt_one_sub_of_sqrt_quotient`, which
--   are partial ingredients rather than the full composed summand bound.
-- minimal hypotheses: the algorithm setup is reduced to pointwise first-moment
--   history control, retained accumulator lower bounds, denominator positivity,
--   beta/gamma square-root quotient witnesses, nonnegative step sizes, and the
--   scalar equation `sqrtTime * alpha_t t = alpha`.

/-- A pointwise adaptive-momentum summand is bounded by a geometric
absolute-gradient history tail.

The lemma composes three standard scalar estimates used by Adam/AMSGrad-style
analyses: a first-moment geometric-history bound, finite geometric
Cauchy-Schwarz, and transport through a retained second-moment square-root
accumulator.  The final scaling uses a horizon-local
`alpha_t = alpha / sqrt(t)` schedule expressed by
`sqrtTime * alpha_t t = alpha`.

Layer: Layer1 | Gap: Level 1 (adaptive-momentum pointwise history-tail bound)
Proof: square the first-moment history bound, apply the finite geometric
Cauchy bound, transport each denominator term through the retained accumulator
lower bound, and rewrite the step-size schedule into the displayed
`alpha / sqrt(t)` coefficient.
Source: Mathlib finite sums, ordered real division, absolute-value and square
arithmetic, together with SOptLib geometric Cauchy and square-root denominator
transport lemmas
Used in: Adam/AMSGrad adaptive-momentum regret estimates just before the
coordinatewise pointwise summand bound is summed into a triangular
geometric-history tail
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/2/proof/2
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem adaptive_momentum_sq_div_sqrt_accumulator_le_geometric_history_tail
    (m g vhatSqrt alpha_t : ℕ → ℝ)
    (alpha beta1 beta2 sqrtBeta2 gamma sqrtOneMinusBeta2 : ℝ) (T : ℕ)
    (hsqrtBeta2 : realSqrtSpec beta2 sqrtBeta2)
    (hgamma : sqrtBeta2 * gamma = beta1)
    (hsqrtOneMinus : realSqrtSpec (1 - beta2) sqrtOneMinusBeta2)
    (hgamma_nonneg : 0 ≤ gamma)
    (hbeta1_nonneg : 0 ≤ beta1)
    (hbeta1_lt : beta1 < 1)
    (hsqrtOneMinus_pos : 0 < sqrtOneMinusBeta2)
    (hm_abs :
      ∀ t ∈ Finset.Icc 1 T,
        |m t| ≤ ∑ j ∈ Finset.Icc 1 t, beta1 ^ (t - j) * |g j|)
    (hvhat_pos : ∀ t ∈ Finset.Icc 1 T, 0 < vhatSqrt t)
    (hvhat_history_lower :
      ∀ t ∈ Finset.Icc 1 T, ∀ j ∈ Finset.Icc 1 t,
        (1 - beta2) * beta2 ^ (t - j) * (g j) ^ 2 ≤
          (vhatSqrt t) ^ 2)
    (halpha_t_nonneg : ∀ t ∈ Finset.Icc 1 T, 0 ≤ alpha_t t)
    (halpha_schedule :
      ∀ t ∈ Finset.Icc 1 T,
        ∃ sqrtTime,
          sqrtTime = Real.sqrt (t : ℝ) ∧ sqrtTime ≠ 0 ∧
            sqrtTime * alpha_t t = alpha) :
    ∀ t ∈ Finset.Icc 1 T,
      alpha_t t * ((m t) ^ 2 / vhatSqrt t) ≤
        (alpha / ((1 - beta1) * sqrtOneMinusBeta2)) *
          ((1 / Real.sqrt (t : ℝ)) *
            ∑ j ∈ Finset.Icc 1 t, gamma ^ (t - j) * |g j|) := by
  intro t ht
  have hden_pos : 0 < vhatSqrt t := hvhat_pos t ht
  have hterm_transport :
      ∀ j ∈ Finset.Icc 1 t,
        beta1 ^ (t - j) * (g j) ^ 2 / vhatSqrt t ≤
          gamma ^ (t - j) * |g j| / sqrtOneMinusBeta2 := by
    intro j hj
    exact
      geometric_sq_div_le_gamma_abs_div_sqrt_one_sub_of_sqrt_quotient
        (t - j) hsqrtBeta2 hgamma hsqrtOneMinus hgamma_nonneg
        hden_pos hsqrtOneMinus_pos (hvhat_history_lower t ht j hj)
  have hbeta_history_nonneg :
      0 ≤ ∑ j ∈ Finset.Icc 1 t, beta1 ^ (t - j) * |g j| := by
    refine Finset.sum_nonneg ?_
    intro j _hj
    exact mul_nonneg (pow_nonneg hbeta1_nonneg (t - j)) (abs_nonneg _)
  have hm_sq_le_history_sq :
      (m t) ^ 2 ≤
        (∑ j ∈ Finset.Icc 1 t, beta1 ^ (t - j) * |g j|) ^ 2 := by
    have hsq_abs_le :
        |m t| ^ 2 ≤
          (∑ j ∈ Finset.Icc 1 t, beta1 ^ (t - j) * |g j|) ^ 2 := by
      nlinarith [hm_abs t ht, abs_nonneg (m t), hbeta_history_nonneg]
    simpa [sq_abs] using hsq_abs_le
  have hm_sq_cauchy :
      (m t) ^ 2 ≤
        (1 / (1 - beta1)) *
          (∑ j ∈ Finset.Icc 1 t, beta1 ^ (t - j) * (g j) ^ 2) :=
    le_trans hm_sq_le_history_sq
      (sq_sum_Icc_geometric_abs_le_inv_one_sub_mul_sum_geometric_sq
        beta1 hbeta1_nonneg hbeta1_lt t g)
  have hsum_transport :
      (∑ j ∈ Finset.Icc 1 t, beta1 ^ (t - j) * (g j) ^ 2) /
          vhatSqrt t ≤
        ∑ j ∈ Finset.Icc 1 t,
          gamma ^ (t - j) * |g j| / sqrtOneMinusBeta2 := by
    calc
      (∑ j ∈ Finset.Icc 1 t, beta1 ^ (t - j) * (g j) ^ 2) /
          vhatSqrt t
          = ∑ j ∈ Finset.Icc 1 t,
              (beta1 ^ (t - j) * (g j) ^ 2) / vhatSqrt t := by
              rw [← Finset.sum_div]
      _ ≤ ∑ j ∈ Finset.Icc 1 t,
            gamma ^ (t - j) * |g j| / sqrtOneMinusBeta2 := by
            exact Finset.sum_le_sum hterm_transport
  have hbeta_recip_nonneg :
      0 ≤ (1 / (1 - beta1) : ℝ) := by
    exact one_div_nonneg.mpr (le_of_lt (sub_pos.mpr hbeta1_lt))
  have hcore_unscaled :
      (m t) ^ 2 / vhatSqrt t ≤
        (1 / (1 - beta1)) *
          (∑ j ∈ Finset.Icc 1 t,
            gamma ^ (t - j) * |g j| / sqrtOneMinusBeta2) := by
    calc
      (m t) ^ 2 / vhatSqrt t
          ≤ ((1 / (1 - beta1)) *
              (∑ j ∈ Finset.Icc 1 t,
                beta1 ^ (t - j) * (g j) ^ 2)) / vhatSqrt t := by
              exact div_le_div_of_nonneg_right hm_sq_cauchy
                (le_of_lt hden_pos)
      _ = (1 / (1 - beta1)) *
            ((∑ j ∈ Finset.Icc 1 t,
              beta1 ^ (t - j) * (g j) ^ 2) / vhatSqrt t) := by
              ring
      _ ≤ (1 / (1 - beta1)) *
            (∑ j ∈ Finset.Icc 1 t,
              gamma ^ (t - j) * |g j| / sqrtOneMinusBeta2) := by
              exact mul_le_mul_of_nonneg_left hsum_transport
                hbeta_recip_nonneg
  have hsum_gamma_div :
      (∑ j ∈ Finset.Icc 1 t,
        gamma ^ (t - j) * |g j| / sqrtOneMinusBeta2) =
        (∑ j ∈ Finset.Icc 1 t,
          gamma ^ (t - j) * |g j|) / sqrtOneMinusBeta2 := by
    rw [Finset.sum_div]
  rcases halpha_schedule t ht with
    ⟨sqrtTime, hsqrtTime_eq, hsqrtTime_ne, halpha_eq⟩
  calc
    alpha_t t * ((m t) ^ 2 / vhatSqrt t)
        ≤ alpha_t t *
            ((1 / (1 - beta1)) *
              ((∑ j ∈ Finset.Icc 1 t,
                gamma ^ (t - j) * |g j|) / sqrtOneMinusBeta2)) := by
          rw [← hsum_gamma_div]
          exact mul_le_mul_of_nonneg_left hcore_unscaled
            (halpha_t_nonneg t ht)
    _ = (alpha / ((1 - beta1) * sqrtOneMinusBeta2)) *
          ((1 / Real.sqrt (t : ℝ)) *
            ∑ j ∈ Finset.Icc 1 t, gamma ^ (t - j) * |g j|) := by
          rw [← hsqrtTime_eq]
          field_simp [ne_of_gt (by linarith : 0 < 1 - beta1),
            ne_of_gt hsqrtOneMinus_pos, hsqrtTime_ne]
          calc
            (alpha_t t *
                ∑ x ∈ Finset.Icc 1 t, gamma ^ (t - x) * |g x|) *
                sqrtTime =
              (∑ x ∈ Finset.Icc 1 t, gamma ^ (t - x) * |g x|) *
                (sqrtTime * alpha_t t) := by
                ring
            _ = (∑ x ∈ Finset.Icc 1 t, gamma ^ (t - x) * |g x|) *
                alpha := by
                rw [halpha_eq]
