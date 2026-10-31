import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Tactic

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-window metric-drop plus beta-correction telescope; orig was amsgrad_metric_beta_telescope_scalar
-- generality used: a field with linear order and strict ordered-ring structure, natural-number horizon, nonnegative bounded potential, nonnegative nondecreasing weights, and nonnegative nonincreasing beta parameters bounded by betaMax
-- portable call pattern: adaptive-method convergence proofs telescope weighted squared-distance drops together with beta corrections; the weight schedule, beta schedule, potential sequence, horizon, and cap change while the scalar inequality stays fixed
-- counterargument checked: existing two-coefficient and monotone weighted-drop telescopes cover only partial coefficient bridges; this expression's beta correction needs the stronger local coefficient estimate proved by the induction below, so it is not a caller-side wrapper or duplicate
-- coverage search: searched `finite window scalar telescope metric drop beta correction monotone weights nonincreasing beta bounded nonnegative potential`; top hit `SOptLib.sum_Icc_two_coeff_telescope_le` has a different adjacent coefficient premise, while `sum_Icc_mono_coeff_mul_sub_le_terminal` handles plain drops only
-- minimal hypotheses: the source's pointwise window hypotheses are retained; the scalar carrier is generalized from ℝ to `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`, and no measure, finite-dimensional, or optimization assumptions are needed

/-- A finite-window weighted potential-drop sum with a beta correction is bounded by
the uniform potential cap times the terminal weight and the accumulated beta-weighted
coefficients.

Layer: Glue | Gap: Level 1 (beta-corrected finite-window scalar telescope)
Proof: Induct on the right endpoint, retaining the negative terminal tail. Monotone
weights and nonincreasing beta parameters control the exposed middle coefficient,
after which the bounded nonnegative potential supplies the cap.
Source: Mathlib finite sums over natural intervals, ordered-field division, and
real-arithmetic-style monotonicity arguments
Used in: adaptive-method convergence proofs that telescope weighted squared-distance
drops together with beta correction terms under a bounded comparator distance
Book citation: book/ICLR2018/AMSGrad.json#/main_theorem/proof/4
Origin algorithm: Reddi, Kale, and Kumar - On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem sum_metric_drop_add_beta_correction_le_of_mono
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a beta y : ℕ → R) (T : ℕ) (D2 betaMax : R)
    (hT : 1 ≤ T)
    (hy_nonneg : ∀ t, 1 ≤ t → t ≤ T + 1 → 0 ≤ y t)
    (hy_le : ∀ t, 1 ≤ t → t ≤ T → y t ≤ D2)
    (ha_nonneg : ∀ t, 1 ≤ t → t ≤ T → 0 ≤ a t)
    (ha_mono : ∀ t, 2 ≤ t → t ≤ T → a (t - 1) ≤ a t)
    (hbeta_nonneg : ∀ t, 1 ≤ t → t ≤ T → 0 ≤ beta t)
    (hbeta_le : ∀ t, 1 ≤ t → t ≤ T → beta t ≤ betaMax)
    (hbeta_mono : ∀ t, 2 ≤ t → t ≤ T → beta t ≤ beta (t - 1))
    (hbetaMax_lt : betaMax < 1) :
    (∑ t ∈ Finset.Icc 1 T, (
        a t * (y t - y (t + 1)) / (1 - beta t) +
          beta t * a t * y t / (1 - beta t))) ≤
      D2 / (1 - betaMax) *
        (a T + ∑ t ∈ Finset.Icc 1 T, beta t * a t) := by
  classical
  have hdenMax_pos : 0 < 1 - betaMax := by linarith
  have hD2_nonneg : 0 ≤ D2 := by
    exact le_trans (hy_nonneg 1 (by norm_num) (Nat.le_trans hT (Nat.le_succ T)))
      (hy_le 1 (by norm_num) hT)
  have hstrong : ∀ k, (hk1 : 1 ≤ k) → k ≤ T →
      (∑ t ∈ Finset.Icc 1 k, (
          a t * (y t - y (t + 1)) / (1 - beta t) +
            beta t * a t * y t / (1 - beta t))) ≤
        D2 / (1 - betaMax) *
            (a k + ∑ t ∈ Finset.Icc 1 k, beta t * a t) -
          a k * y (k + 1) / (1 - beta k) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
        intro hkT
        have ha1 : 0 ≤ a 1 := ha_nonneg 1 (by norm_num) hkT
        have hb1 : 0 ≤ beta 1 := hbeta_nonneg 1 (by norm_num) hkT
        have hb1_le : beta 1 ≤ betaMax := hbeta_le 1 (by norm_num) hkT
        have hden1_pos : 0 < 1 - beta 1 := by linarith
        have hy1_le : y 1 ≤ D2 := hy_le 1 (by norm_num) hkT
        have hy1_nonneg : 0 ≤ y 1 :=
          hy_nonneg 1 (by norm_num) (Nat.le_trans hkT (Nat.le_succ T))
        have hrecip : (1 : R) / (1 - beta 1) ≤ 1 / (1 - betaMax) := by
          exact one_div_le_one_div_of_le hdenMax_pos (by linarith)
        have hmain :
            a 1 * y 1 / (1 - beta 1) +
                beta 1 * a 1 * y 1 / (1 - beta 1) ≤
              D2 / (1 - betaMax) * (a 1 + beta 1 * a 1) := by
          have hpart1 :
              a 1 * y 1 / (1 - beta 1) ≤
                D2 / (1 - betaMax) * a 1 := by
            have hcoef : a 1 * ((1 : R) / (1 - beta 1)) ≤
                a 1 * (1 / (1 - betaMax)) :=
              mul_le_mul_of_nonneg_left hrecip ha1
            calc
              a 1 * y 1 / (1 - beta 1)
                  = (a 1 * ((1 : R) / (1 - beta 1))) * y 1 := by ring
              _ ≤ (a 1 * (1 / (1 - betaMax))) * y 1 := by
                  exact mul_le_mul_of_nonneg_right hcoef hy1_nonneg
              _ ≤ (a 1 * (1 / (1 - betaMax))) * D2 := by
                  exact mul_le_mul_of_nonneg_left hy1_le (by positivity)
              _ = D2 / (1 - betaMax) * a 1 := by ring
          have hpart2 :
              beta 1 * a 1 * y 1 / (1 - beta 1) ≤
                D2 / (1 - betaMax) * (beta 1 * a 1) := by
            have hba_nonneg : 0 ≤ beta 1 * a 1 := mul_nonneg hb1 ha1
            have hcoef : beta 1 * a 1 * ((1 : R) / (1 - beta 1)) ≤
                beta 1 * a 1 * (1 / (1 - betaMax)) :=
              mul_le_mul_of_nonneg_left hrecip hba_nonneg
            calc
              beta 1 * a 1 * y 1 / (1 - beta 1)
                  = (beta 1 * a 1 * ((1 : R) / (1 - beta 1))) * y 1 := by
                    ring
              _ ≤ (beta 1 * a 1 * (1 / (1 - betaMax))) * y 1 := by
                  exact mul_le_mul_of_nonneg_right hcoef hy1_nonneg
              _ ≤ (beta 1 * a 1 * (1 / (1 - betaMax))) * D2 := by
                  exact mul_le_mul_of_nonneg_left hy1_le (by positivity)
              _ = D2 / (1 - betaMax) * (beta 1 * a 1) := by ring
          nlinarith [hpart1, hpart2]
        have hbase_goal :
            a 1 * (y 1 - y (1 + 1)) / (1 - beta 1) +
                beta 1 * a 1 * y 1 / (1 - beta 1) ≤
              D2 / (1 - betaMax) * (a 1 + beta 1 * a 1) -
                a 1 * y (1 + 1) / (1 - beta 1) := by
          calc
            a 1 * (y 1 - y (1 + 1)) / (1 - beta 1) +
                beta 1 * a 1 * y 1 / (1 - beta 1)
                = (a 1 * y 1 / (1 - beta 1) +
                    beta 1 * a 1 * y 1 / (1 - beta 1)) -
                  a 1 * y (1 + 1) / (1 - beta 1) := by ring
            _ ≤ D2 / (1 - betaMax) * (a 1 + beta 1 * a 1) -
                  a 1 * y (1 + 1) / (1 - beta 1) := by
                exact sub_le_sub_right hmain _
        simpa [Finset.Icc_self] using hbase_goal
    | succ n hn ih =>
        intro hsuccT
        have hnT : n ≤ T := Nat.le_trans (Nat.le_succ n) hsuccT
        have hsum_split :
            (∑ t ∈ Finset.Icc 1 (n + 1), (
                a t * (y t - y (t + 1)) / (1 - beta t) +
                  beta t * a t * y t / (1 - beta t))) =
              (∑ t ∈ Finset.Icc 1 n, (
                a t * (y t - y (t + 1)) / (1 - beta t) +
                  beta t * a t * y t / (1 - beta t))) +
                (a (n + 1) * (y (n + 1) - y (n + 2)) /
                    (1 - beta (n + 1)) +
                  beta (n + 1) * a (n + 1) * y (n + 1) /
                    (1 - beta (n + 1))) := by
          rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hn)]
        rw [hsum_split]
        have hih := ih hnT
        have hden_n_pos : 0 < 1 - beta n := by
          have hb_le := hbeta_le n hn hnT
          linarith
        have hden_succ_pos : 0 < 1 - beta (n + 1) := by
          have hb_le := hbeta_le (n + 1) (Nat.le_succ_of_le hn) hsuccT
          linarith
        have ha_n_nonneg : 0 ≤ a n := ha_nonneg n hn hnT
        have ha_succ_nonneg : 0 ≤ a (n + 1) :=
          ha_nonneg (n + 1) (Nat.le_succ_of_le hn) hsuccT
        have hb_succ_nonneg : 0 ≤ beta (n + 1) :=
          hbeta_nonneg (n + 1) (Nat.le_succ_of_le hn) hsuccT
        have ha_step : a n ≤ a (n + 1) := by
          have hpred : n + 1 - 1 = n := Nat.succ_sub_one n
          simpa [hpred] using
            ha_mono (n + 1) (Nat.succ_le_succ hn) hsuccT
        have hb_step : beta (n + 1) ≤ beta n :=
          hbeta_mono (n + 1) (Nat.succ_le_succ hn) hsuccT
        have hrecip_step :
            (1 : R) / (1 - beta n) ≥ 1 / (1 - beta (n + 1)) := by
          have hden_le : 1 - beta n ≤ 1 - beta (n + 1) := by linarith
          exact one_div_le_one_div_of_le hden_n_pos hden_le
        have hrecip_succ_global :
            (1 : R) / (1 - beta (n + 1)) ≤ 1 / (1 - betaMax) := by
          exact one_div_le_one_div_of_le hdenMax_pos
            (by
              have := hbeta_le (n + 1) (Nat.le_succ_of_le hn) hsuccT
              linarith)
        have hdelta_nonneg :
            0 ≤ (a (n + 1) - a n) + beta (n + 1) * a (n + 1) := by
          nlinarith [ha_step, mul_nonneg hb_succ_nonneg ha_succ_nonneg]
        have hcoeff_le :
            a (n + 1) / (1 - beta (n + 1)) +
                beta (n + 1) * a (n + 1) / (1 - beta (n + 1)) -
              a n / (1 - beta n) ≤
            ((a (n + 1) - a n) + beta (n + 1) * a (n + 1)) /
              (1 - betaMax) := by
          have hneg_transport :
              a n / (1 - beta (n + 1)) ≤ a n / (1 - beta n) := by
            have hcoef := mul_le_mul_of_nonneg_left hrecip_step ha_n_nonneg
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcoef
          have hlocal :
              a (n + 1) / (1 - beta (n + 1)) +
                  beta (n + 1) * a (n + 1) / (1 - beta (n + 1)) -
                a n / (1 - beta n) ≤
              ((a (n + 1) - a n) +
                    beta (n + 1) * a (n + 1)) /
                (1 - beta (n + 1)) := by
            calc
              a (n + 1) / (1 - beta (n + 1)) +
                    beta (n + 1) * a (n + 1) / (1 - beta (n + 1)) -
                  a n / (1 - beta n)
                  ≤ a (n + 1) / (1 - beta (n + 1)) +
                      beta (n + 1) * a (n + 1) / (1 - beta (n + 1)) -
                    a n / (1 - beta (n + 1)) := by
                    linarith
              _ = ((a (n + 1) - a n) +
                    beta (n + 1) * a (n + 1)) /
                  (1 - beta (n + 1)) := by ring
          have hglobal :
              ((a (n + 1) - a n) + beta (n + 1) * a (n + 1)) /
                (1 - beta (n + 1)) ≤
              ((a (n + 1) - a n) + beta (n + 1) * a (n + 1)) /
                (1 - betaMax) := by
            have hcoef := mul_le_mul_of_nonneg_left hrecip_succ_global
              hdelta_nonneg
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcoef
          exact le_trans hlocal hglobal
        have hy_succ_nonneg : 0 ≤ y (n + 1) :=
          hy_nonneg (n + 1) (Nat.le_succ_of_le hn)
            (Nat.le_trans hsuccT (Nat.le_succ T))
        have hy_succ_le : y (n + 1) ≤ D2 :=
          hy_le (n + 1) (Nat.le_succ_of_le hn) hsuccT
        have hmiddle :
            (a (n + 1) / (1 - beta (n + 1)) +
                beta (n + 1) * a (n + 1) / (1 - beta (n + 1)) -
              a n / (1 - beta n)) * y (n + 1) ≤
            D2 / (1 - betaMax) *
              ((a (n + 1) - a n) + beta (n + 1) * a (n + 1)) := by
          have hmul1 := mul_le_mul_of_nonneg_right hcoeff_le hy_succ_nonneg
          have hmul2 := mul_le_mul_of_nonneg_left hy_succ_le
            (div_nonneg hdelta_nonneg (le_of_lt hdenMax_pos))
          calc
            (a (n + 1) / (1 - beta (n + 1)) +
                beta (n + 1) * a (n + 1) / (1 - beta (n + 1)) -
              a n / (1 - beta n)) * y (n + 1)
                ≤ ((a (n + 1) - a n) +
                    beta (n + 1) * a (n + 1)) /
                    (1 - betaMax) * y (n + 1) := hmul1
            _ ≤ ((a (n + 1) - a n) +
                    beta (n + 1) * a (n + 1)) /
                    (1 - betaMax) * D2 := hmul2
            _ = D2 / (1 - betaMax) *
                  ((a (n + 1) - a n) +
                    beta (n + 1) * a (n + 1)) := by ring
        rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hn)]
        calc
          (∑ t ∈ Finset.Icc 1 n,
              (a t * (y t - y (t + 1)) / (1 - beta t) +
                beta t * a t * y t / (1 - beta t))) +
              (a (n + 1) * (y (n + 1) - y (n + 2)) /
                  (1 - beta (n + 1)) +
                beta (n + 1) * a (n + 1) * y (n + 1) /
                  (1 - beta (n + 1)))
              ≤ (D2 / (1 - betaMax) *
                    (a n + ∑ t ∈ Finset.Icc 1 n, beta t * a t) -
                  a n * y (n + 1) / (1 - beta n)) +
                (a (n + 1) * (y (n + 1) - y (n + 2)) /
                    (1 - beta (n + 1)) +
                  beta (n + 1) * a (n + 1) * y (n + 1) /
                    (1 - beta (n + 1))) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right hih
                      (a (n + 1) * (y (n + 1) - y (n + 2)) /
                        (1 - beta (n + 1)) +
                      beta (n + 1) * a (n + 1) * y (n + 1) /
                        (1 - beta (n + 1)))
          _ = D2 / (1 - betaMax) *
                  (a n + ∑ t ∈ Finset.Icc 1 n, beta t * a t) +
                (a (n + 1) / (1 - beta (n + 1)) +
                    beta (n + 1) * a (n + 1) /
                      (1 - beta (n + 1)) -
                  a n / (1 - beta n)) * y (n + 1) -
                a (n + 1) * y (n + 2) /
                  (1 - beta (n + 1)) := by
                  ring
          _ ≤ D2 / (1 - betaMax) *
                  (a n + ∑ t ∈ Finset.Icc 1 n, beta t * a t) +
                D2 / (1 - betaMax) *
                  (a (n + 1) - a n +
                    beta (n + 1) * a (n + 1)) -
                a (n + 1) * y (n + 2) /
                  (1 - beta (n + 1)) := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    sub_le_sub_right
                      (add_le_add_left hmiddle
                        (D2 / (1 - betaMax) *
                          (a n + ∑ t ∈ Finset.Icc 1 n, beta t * a t)))
                      (a (n + 1) * y (n + 2) /
                        (1 - beta (n + 1)))
          _ = D2 / (1 - betaMax) *
                  (a (n + 1) +
                    (∑ t ∈ Finset.Icc 1 n, beta t * a t +
                      beta (n + 1) * a (n + 1))) -
                a (n + 1) * y (n + 1 + 1) /
                  (1 - beta (n + 1)) := by
                  ring
  have htail_nonneg :
      0 ≤ a T * y (T + 1) / (1 - beta T) := by
    have haT : 0 ≤ a T := ha_nonneg T hT le_rfl
    have hyT : 0 ≤ y (T + 1) := hy_nonneg (T + 1) (Nat.le_succ_of_le hT) le_rfl
    have hdenT : 0 < 1 - beta T := by
      have hb_le := hbeta_le T hT le_rfl
      linarith
    exact div_nonneg (mul_nonneg haT hyT) (le_of_lt hdenT)
  have h := hstrong T hT le_rfl
  nlinarith [h, htail_nonneg]
