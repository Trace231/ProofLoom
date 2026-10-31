import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: scalar absolute-value recurrence bound by a geometric history; orig was generated_mSeq_coord_abs_le_geometric_history.
-- generality used: sequences over a linearly ordered commutative ring indexed by natural time, a dominating coefficient in the same ring, a zero initial value, and pointwise scalar recurrence/coefficient inequalities; no measure, filtration, optimization, oracle, norm, inner-product, or finite-dimensional assumptions are used.
-- portable call pattern: momentum and exponentially weighted-history proofs instantiate the state sequence, input history, time-varying coefficients, and horizon; the same geometric absolute-history conclusion is reused after changing those recurrence witnesses.
-- counterargument checked: not paper-local traceability or a caller-side expression because the theorem packages the nontrivial finite-history induction; existing Mathlib/SOptLib recurrence entries cover different telescopes or weighted sums and do not provide this absolute-value geometric-history conclusion.
-- coverage search: searched `absolute value recurrence geometric history coefficient bounded`, `scalar recurrence geometric weighted history`, and `momentum absolute history bound`; the closest hits were the two paper-local AMSGrad helpers, generic finite-window recurrence telescopes, and the separate geometric Cauchy bound, so coverage is partial rather than full.
-- minimal hypotheses: the setup/domain fields are replaced by `m 0 = 0`, a pointwise recurrence, pointwise coefficient nonnegativity, coefficient domination, and `beta < 1`; on the nonempty target horizon, `0 ≤ beta` is derived from the first coefficient and its domination bound, while strict per-time denominator positivity follows from coefficient domination and `beta < 1`.

/-- A scalar recurrence with nonnegative coefficients bounded by `beta` is
bounded in absolute value by the corresponding beta-geometric input history.

Layer: Glue | Gap: Level 1 (finite geometric-history recurrence bound)
Proof: Induct on the time horizon, use the absolute-value triangle inequality
on the recurrence, and shift the previous history by one power of `beta`.
Source: Mathlib ordered-ring arithmetic, absolute-value inequalities, natural
number interval sums, and finite-sum power algebra
Used in: momentum and exponentially weighted-history estimates that replace a
recursively updated scalar numerator by a finite geometric sum of input
magnitudes
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/2/proof/1
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond - AMSGrad Algorithm 2 -/
theorem abs_recurrence_le_geometric_history_of_coeff_le
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (m g beta_t : ℕ → R) (beta : R) (T : ℕ)
    (hm_zero : m 0 = 0)
    (hrec : ∀ t ∈ Finset.Icc 1 T,
      m t = beta_t t * m (t - 1) + (1 - beta_t t) * g t)
    (hcoeff_nonneg : ∀ t ∈ Finset.Icc 1 T, 0 ≤ beta_t t)
    (hcoeff_le : ∀ t ∈ Finset.Icc 1 T, beta_t t ≤ beta)
    (hbeta_lt : beta < 1) :
    ∀ t ∈ Finset.Icc 1 T,
      |m t| ≤ ∑ j ∈ Finset.Icc 1 t, beta ^ (t - j) * |g j| := by
  intro t ht
  have ht1 : 1 ∈ Finset.Icc 1 T := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, le_trans (Finset.mem_Icc.mp ht).1
      (Finset.mem_Icc.mp ht).2⟩
  have hbeta_nonneg : 0 ≤ beta := by
    linarith [hcoeff_nonneg 1 ht1, hcoeff_le 1 ht1]
  induction t with
  | zero =>
      simp at ht
  | succ n ih =>
      cases n with
      | zero =>
          have ht1 : 1 ∈ Finset.Icc 1 T := by simpa using ht
          have hrec1 :
              m 1 = (1 - beta_t 1) * g 1 := by
            simpa [hm_zero] using hrec 1 ht1
          calc
            |m 1| = (1 - beta_t 1) * |g 1| := by
              calc
                |m 1| = |(1 - beta_t 1) * g 1| := by rw [hrec1]
                _ = |1 - beta_t 1| * |g 1| := by rw [abs_mul]
                _ = (1 - beta_t 1) * |g 1| := by
                  rw [abs_of_nonneg]
                  linarith [hcoeff_le 1 ht1, hbeta_lt]
            _ ≤ 1 * |g 1| := by
              exact mul_le_mul_of_nonneg_right
                (by linarith [hcoeff_nonneg 1 ht1]) (abs_nonneg _)
            _ = ∑ j ∈ Finset.Icc 1 1, beta ^ (1 - j) * |g j| := by
              simp
      | succ n =>
          have htcur : n + 2 ∈ Finset.Icc 1 T := by simpa using ht
          have htprev : n + 1 ∈ Finset.Icc 1 T := by
            have htb := Finset.mem_Icc.mp htcur
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hrec_cur :
              m (n + 2) =
                beta_t (n + 2) * m (n + 1) +
                  (1 - beta_t (n + 2)) * g (n + 2) :=
            hrec (n + 2) htcur
          have hb_t_nonneg : 0 ≤ beta_t (n + 2) :=
            hcoeff_nonneg (n + 2) htcur
          have hone_t_nonneg : 0 ≤ 1 - beta_t (n + 2) := by
            linarith [hcoeff_le (n + 2) htcur, hbeta_lt]
          have hone_t_le_one : 1 - beta_t (n + 2) ≤ 1 := by
            linarith
          have hprev := ih htprev
          have hsum_shift :
              beta_t (n + 2) *
                  (∑ j ∈ Finset.Icc 1 (n + 1),
                    beta ^ (n + 1 - j) * |g j|) ≤
                ∑ j ∈ Finset.Icc 1 (n + 1),
                    beta ^ (n + 2 - j) * |g j| := by
            calc
              beta_t (n + 2) *
                  (∑ j ∈ Finset.Icc 1 (n + 1),
                    beta ^ (n + 1 - j) * |g j|)
                  = ∑ j ∈ Finset.Icc 1 (n + 1),
                      beta_t (n + 2) *
                        (beta ^ (n + 1 - j) * |g j|) := by
                    rw [Finset.mul_sum]
              _ ≤ ∑ j ∈ Finset.Icc 1 (n + 1),
                    beta ^ (n + 2 - j) * |g j| := by
                    refine Finset.sum_le_sum ?_
                    intro j hj
                    have hjb := Finset.mem_Icc.mp hj
                    have hpow_shift : n + 2 - j = (n + 1 - j) + 1 := by
                      omega
                    have hterm_nonneg :
                        0 ≤ beta ^ (n + 1 - j) * |g j| := by
                      exact mul_nonneg
                        (pow_nonneg hbeta_nonneg (n + 1 - j))
                        (abs_nonneg _)
                    calc
                      beta_t (n + 2) *
                          (beta ^ (n + 1 - j) * |g j|)
                          ≤ beta *
                              (beta ^ (n + 1 - j) * |g j|) := by
                            exact mul_le_mul_of_nonneg_right
                              (hcoeff_le (n + 2) htcur) hterm_nonneg
                      _ = beta ^ (n + 2 - j) * |g j| := by
                            rw [hpow_shift, pow_succ]
                            ring
          have htop_le :
              (1 - beta_t (n + 2)) * |g (n + 2)| ≤ |g (n + 2)| := by
            calc
              (1 - beta_t (n + 2)) * |g (n + 2)|
                  ≤ 1 * |g (n + 2)| := by
                    exact mul_le_mul_of_nonneg_right hone_t_le_one
                      (abs_nonneg _)
              _ = |g (n + 2)| := by ring
          calc
            |m (n + 2)| ≤
                beta_t (n + 2) * |m (n + 1)| +
                  (1 - beta_t (n + 2)) * |g (n + 2)| := by
              rw [hrec_cur]
              calc
                |beta_t (n + 2) * m (n + 1) +
                    (1 - beta_t (n + 2)) * g (n + 2)|
                    ≤ |beta_t (n + 2) * m (n + 1)| +
                      |(1 - beta_t (n + 2)) * g (n + 2)| :=
                      abs_add_le _ _
                _ = beta_t (n + 2) * |m (n + 1)| +
                      (1 - beta_t (n + 2)) * |g (n + 2)| := by
                      rw [abs_mul, abs_mul, abs_of_nonneg hb_t_nonneg,
                        abs_of_nonneg hone_t_nonneg]
            _ ≤ beta_t (n + 2) *
                  (∑ j ∈ Finset.Icc 1 (n + 1),
                    beta ^ (n + 1 - j) * |g j|) +
                (1 - beta_t (n + 2)) * |g (n + 2)| := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right
                  (mul_le_mul_of_nonneg_left hprev hb_t_nonneg)
                  ((1 - beta_t (n + 2)) * |g (n + 2)|)
            _ ≤ ∑ j ∈ Finset.Icc 1 (n + 1),
                    beta ^ (n + 2 - j) * |g j| +
                |g (n + 2)| := by
              exact add_le_add hsum_shift htop_le
            _ = ∑ j ∈ Finset.Icc 1 (n + 2),
                    beta ^ (n + 2 - j) * |g j| := by
              rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 2)]
              simp
