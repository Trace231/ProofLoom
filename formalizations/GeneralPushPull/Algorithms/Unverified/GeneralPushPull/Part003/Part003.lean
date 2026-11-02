import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENNReal.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Process.Filtration
import SOptLib.Glue.Calculus
import SOptLib.Glue.Martingale
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Iterates
import SOptLib.Model.NetworkMatrix
import Algorithms.Unverified.GeneralPushPull.Part002
import Algorithms.Unverified.GeneralPushPull.Part003.Part002

noncomputable section

open scoped BigOperators InnerProductSpace Matrix
open MeasureTheory

namespace Algorithms.Unverified.GeneralPushPull

/-! # General Push--Pull: source-facing object model

This file models the fixed algorithm in `book/GeneralPushPull/GeneralPushPull.json`.
The network is deterministic and horizon-independent by construction. An oracle
table and every algorithm state are derived below; neither is supplied as a witness.
-/

variable {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 5000000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 3000000
set_option maxHeartbeats 1000000

/-- Complete deterministic certificate exported by the backward gain-budget
partition.  The weight `omega j = 64 s M_j`, where `M_j` is the suffix maximum
of block lengths, dominates the gain-normalized block length and is
nonincreasing.  The same endpoints supply the full-horizon reindexing and all
causal-window premises of `gain_block_suffix_influence_overcount`. -/
theorem backward_gain_partition_overcount_certificate
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (htotal : epsilon / 2 ≤
      s.1 * ∑ t ∈ Finset.range T.1, gain N t) :
    ∃ blockCount : ℕ, ∃ endpoint : ℕ → ℕ,
      let blocks : ℕ → Finset ℕ := fun j =>
        Finset.Ico (endpoint j) (endpoint (j + 1))
      let M : ℕ → ℕ := fun j =>
        (Finset.Ico j blockCount).sup fun l => (blocks l).card
      let omega : ℕ → ℝ := fun j => 64 * s.1 * (M j : ℝ)
      0 < blockCount ∧ endpoint 0 = 0 ∧ endpoint blockCount = T.1 ∧
      (∀ j < blockCount, endpoint j < endpoint (j + 1)) ∧
      (∀ j < blockCount,
        1 / (64 * s.1) ≤ ∑ t ∈ blocks j, gain N t ∧
          (∑ t ∈ blocks j, gain N t) ≤ 1 / (16 * s.1)) ∧
      (∀ f : ℕ → ℝ,
        (∑ j ∈ Finset.range blockCount, ∑ t ∈ blocks j, f t) =
          ∑ t ∈ Finset.range T.1, f t) ∧
      (∀ j, 0 ≤ omega j) ∧ (∀ j, omega (j + 1) ≤ omega j) ∧
      (∀ j < blockCount,
        ((blocks j).card : ℝ) ≤
          omega j * ∑ t ∈ blocks j, gain N t) ∧
      (∑ j ∈ Finset.range blockCount,
          omega j * ∑ t ∈ blocks j, influenceEnergy N t) ≤
        64 * s.1 *
          (windowInfluenceSum N T.1 s.1 +
            influenceRowBound N ^ 2 *
              (windowLength N T.1 0 s.1 : ℝ) ^ 2) := by
  classical
  obtain ⟨blockCount, endpoint, hcount, he0, heT, hestrict, hebudget⟩ :=
    exists_backward_gain_budget_partition N T s htotal
  let blocks : ℕ → Finset ℕ := fun j =>
    Finset.Ico (endpoint j) (endpoint (j + 1))
  let M : ℕ → ℕ := fun j =>
    (Finset.Ico j blockCount).sup fun l => (blocks l).card
  let omega : ℕ → ℝ := fun j => 64 * s.1 * (M j : ℝ)
  have hendpoint_mono : ∀ {a b : ℕ}, a ≤ b → b ≤ blockCount →
      endpoint a ≤ endpoint b := by
    intro a b hab hb
    induction b with
    | zero =>
      have ha0 : a = 0 := by omega
      subst a
      exact le_rfl
    | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact (ih hab' (by omega)).trans (hestrict b (by omega)).le
  have hpartition : ∀ f : ℕ → ℝ,
      (∑ j ∈ Finset.range blockCount, ∑ t ∈ blocks j, f t) =
        ∑ t ∈ Finset.range T.1, f t := by
    intro f
    have hpartial : ∀ k ≤ blockCount,
        (∑ j ∈ Finset.range k, ∑ t ∈ blocks j, f t) =
          ∑ t ∈ Finset.Ico 0 (endpoint k), f t := by
      intro k hk
      induction k with
      | zero => simp [he0]
      | succ k ih =>
        rw [Finset.sum_range_succ, ih (by omega)]
        dsimp [blocks]
        rw [← Finset.sum_Ico_consecutive f
          (Nat.zero_le (endpoint k))
          (hestrict k (by omega)).le]
    rw [hpartial blockCount le_rfl, heT]
    simp
  have hMmono : ∀ j, M (j + 1) ≤ M j := by
    intro j
    dsimp [M]
    apply Finset.sup_mono
    intro l hl
    simp only [Finset.mem_Ico] at hl ⊢
    omega
  have hMterminal : M blockCount = 0 := by
    simp [M]
  have hcard_le_M (j : ℕ) (hj : j < blockCount) :
      (blocks j).card ≤ M j := by
    dsimp [M]
    exact Finset.le_sup (f := fun l => (blocks l).card)
      (Finset.mem_Ico.mpr ⟨le_rfl, hj⟩)
  have hdropCard : ∀ j < blockCount,
      M (j + 1) < M j → (blocks j).card = M j := by
    intro j hj hdrop
    have hupper : M j ≤ max (blocks j).card (M (j + 1)) := by
      dsimp [M]
      apply Finset.sup_le
      intro l hl
      simp only [Finset.mem_Ico] at hl
      by_cases hlj : l = j
      · subst l
        exact le_max_left _ _
      · have hfuture : l ∈ Finset.Ico (j + 1) blockCount := by
          simp only [Finset.mem_Ico]
          omega
        have hfuture_le :
            (blocks l).card ≤
              (Finset.Ico (j + 1) blockCount).sup
                (fun l => (blocks l).card) :=
          Finset.le_sup (f := fun l => (blocks l).card) hfuture
        exact hfuture_le.trans (le_max_right _ _)
    have hcard := hcard_le_M j hj
    omega
  have hwindow : ∀ j < blockCount, ∀ t ∈ blocks j,
      M (j + 1) ≤ windowLength N T.1 (t + 1) s.1 := by
    intro j hj t ht
    dsimp [M]
    apply Finset.sup_le
    intro l hl
    have hlbounds : j + 1 ≤ l ∧ l < blockCount := by
      simpa only [Finset.mem_Ico] using hl
    have htBounds : endpoint j ≤ t ∧ t < endpoint (j + 1) := by
      simpa only [blocks, Finset.mem_Ico] using ht
    have hstart : t + 1 ≤ endpoint l := by
      have hnext : endpoint (j + 1) ≤ endpoint l :=
        hendpoint_mono hlbounds.1 hlbounds.2.le
      omega
    have hend : endpoint (l + 1) ≤ T.1 := by
      rw [← heT]
      exact hendpoint_mono (by omega) le_rfl
    have hbudget := (hebudget l hlbounds.2).2
    have hbudget' :
        s.1 * ∑ r ∈ Finset.Ico (endpoint l) (endpoint (l + 1)), gain N r ≤
          epsilon := by
      have hs : 0 < s.1 := s.2.1
      calc
        s.1 * ∑ r ∈ Finset.Ico (endpoint l) (endpoint (l + 1)), gain N r ≤
            s.1 * (1 / (16 * s.1)) :=
          mul_le_mul_of_nonneg_left hbudget hs.le
        _ = epsilon := by
          rw [show epsilon = (1 : ℝ) / 16 by norm_num [epsilon]]
          field_simp [ne_of_gt hs]
    have hlen := interval_length_le_windowLength N T.1 (t + 1)
      (endpoint l) (endpoint (l + 1)) s.1
      (by
        exact lt_of_le_of_lt hstart
          ((hestrict l hlbounds.2).trans_le hend))
      hstart (hestrict l hlbounds.2) hend hbudget'
    simpa [blocks, Nat.card_Ico] using hlen
  have hMzero : M 0 ≤ windowLength N T.1 0 s.1 := by
    dsimp [M]
    apply Finset.sup_le
    intro l hl
    have hlbounds : 0 ≤ l ∧ l < blockCount := by
      simpa only [Finset.mem_Ico] using hl
    have hend : endpoint (l + 1) ≤ T.1 := by
      rw [← heT]
      exact hendpoint_mono (by omega) le_rfl
    have hbudget := (hebudget l hlbounds.2).2
    have hbudget' :
        s.1 * ∑ r ∈ Finset.Ico (endpoint l) (endpoint (l + 1)), gain N r ≤
          epsilon := by
      have hs : 0 < s.1 := s.2.1
      calc
        s.1 * ∑ r ∈ Finset.Ico (endpoint l) (endpoint (l + 1)), gain N r ≤
            s.1 * (1 / (16 * s.1)) :=
          mul_le_mul_of_nonneg_left hbudget hs.le
        _ = epsilon := by
          rw [show epsilon = (1 : ℝ) / 16 by norm_num [epsilon]]
          field_simp [ne_of_gt hs]
    have hlen := interval_length_le_windowLength N T.1 0
      (endpoint l) (endpoint (l + 1)) s.1 T.2 (Nat.zero_le _)
      (hestrict l hlbounds.2) hend hbudget'
    simpa [blocks, Nat.card_Ico] using hlen
  have homega_nonneg : ∀ j, 0 ≤ omega j := by
    intro j
    exact mul_nonneg (mul_nonneg (by norm_num) s.2.1.le) (Nat.cast_nonneg _)
  have homega_anti : ∀ j, omega (j + 1) ≤ omega j := by
    intro j
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hMmono j)
      (mul_nonneg (by norm_num) s.2.1.le)
  have hcard_weight : ∀ j < blockCount,
      ((blocks j).card : ℝ) ≤
        omega j * ∑ t ∈ blocks j, gain N t := by
    intro j hj
    have hK := (hebudget j hj).1
    have hcardM : ((blocks j).card : ℝ) ≤ M j := by
      exact_mod_cast hcard_le_M j hj
    have hMnonneg : 0 ≤ (M j : ℝ) := Nat.cast_nonneg _
    have hs : 0 < s.1 := s.2.1
    dsimp [omega]
    field_simp [ne_of_gt hs] at hK
    nlinarith
  have hover := gain_block_suffix_influence_overcount N T s blocks M omega
    blockCount (fun j _hj => hMmono j) hMterminal hdropCard hwindow
    hpartition (fun j _hj => le_rfl) hMzero
  exact ⟨blockCount, endpoint, hcount, he0, heT, hestrict, hebudget,
    hpartition, homega_nonneg, homega_anti, hcard_weight, hover⟩

/-- Innovations at distinct times are orthogonal.  The earlier innovation is
measurable in the later strict-past history, and the later innovation is
conditionally centered there. -/
theorem influence_noise_cross_integral_eq_zero_of_lt
    (S : Setup n d Ω) {a b : ℕ} (hab : a < b) :
    (∫ omega,
      ⟪influenceNoise S omega a, influenceNoise S omega b⟫_ℝ
        ∂S.probability) = 0 := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  have hnoise_meas : Measurable[preSamplingHistory S b] (S.noise a) :=
    noise_measurable_preSamplingHistory_of_lt S hab
  have hU_meas : Measurable[preSamplingHistory S b]
      (fun omega => influenceNoise S omega a) := by
    unfold influenceNoise
    apply Finset.measurable_sum
    intro i _hi
    exact ((measurable_pi_apply i).comp hnoise_meas).const_smul
      (influenceRow S.network a i)
  have hmom := weighted_noise_conditional_moments S a
    (influenceRow S.network a)
  have hU_int : Integrable (fun omega => influenceNoise S omega a)
      S.probability := by
    simpa [influenceNoise] using hmom.1.1.integrable
  have hU_sq : Integrable (fun omega => ‖influenceNoise S omega a‖ ^ 2)
      S.probability := by
    simpa [influenceNoise] using hmom.2.1.integrable
  have hU_mem : MemLp (fun omega => influenceNoise S omega a) 2
      S.probability :=
    (memLp_two_iff_integrable_sq_norm hU_int.aestronglyMeasurable).2 hU_sq
  exact (influence_noise_martingale_interface S b
    (fun omega => influenceNoise S omega a) hU_meas hU_mem).2.1

/-- Martingale orthogonality gives the sharp block-noise energy, without the
extra block-cardinality factor produced by deterministic Cauchy--Schwarz. -/
theorem influence_noise_finset_sum_expected_norm_sq_le
    (S : Setup n d Ω) (I : Finset ℕ) :
    SOptLib.expectation S.probability (fun omega =>
        ‖∑ t ∈ I, influenceNoise S omega t‖ ^ 2) ≤
      S.σ ^ 2 * ∑ t ∈ I, influenceEnergy S.network t := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  have hmeas : ∀ t ∈ I,
      AEStronglyMeasurable (fun omega => influenceNoise S omega t)
        S.probability := by
    intro t _ht
    have hmom := weighted_noise_conditional_moments S t
      (influenceRow S.network t)
    have hint : Integrable (fun omega => influenceNoise S omega t)
        S.probability := by
      simpa [influenceNoise] using hmom.1.1.integrable
    exact hint.aestronglyMeasurable
  have hsq : ∀ t ∈ I,
      Integrable (fun omega => ‖influenceNoise S omega t‖ ^ 2)
        S.probability := by
    intro t _ht
    have hmom := weighted_noise_conditional_moments S t
      (influenceRow S.network t)
    simpa [influenceNoise] using hmom.2.1.integrable
  have hcross : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      (∫ omega,
        ⟪influenceNoise S omega a, influenceNoise S omega b⟫_ℝ
          ∂S.probability) = 0 := by
    intro a _ha b _hb hab
    apply integral_inner_eq_zero_of_ne_of_forward_cross_zero S.probability
      (fun t omega => influenceNoise S omega t) a b
    · intro u v huv
      exact influence_noise_cross_integral_eq_zero_of_lt S huv
    · exact hab
  have hdiag := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    S.probability I (fun t omega => influenceNoise S omega t)
    hmeas hsq hcross
  have hterm (t : ℕ) (ht : t ∈ I) :
      (∫ omega, ‖influenceNoise S omega t‖ ^ 2 ∂S.probability) ≤
        S.σ ^ 2 * influenceEnergy S.network t := by
    have hzero_meas : Measurable[preSamplingHistory S t]
        (fun _ : Ω => (0 : Point d)) := measurable_const
    have hzero_mem : MemLp (fun _ : Ω => (0 : Point d)) 2 S.probability :=
      memLp_const (0 : Point d)
    exact (influence_noise_martingale_interface S t
      (fun _ : Ω => (0 : Point d)) hzero_meas hzero_mem).2.2
  unfold SOptLib.expectation
  rw [hdiag]
  calc
    (∑ t ∈ I, ∫ omega, ‖influenceNoise S omega t‖ ^ 2 ∂S.probability) ≤
        ∑ t ∈ I, S.σ ^ 2 * influenceEnergy S.network t :=
      Finset.sum_le_sum hterm
    _ = S.σ ^ 2 * ∑ t ∈ I, influenceEnergy S.network t := by
      rw [Finset.mul_sum]

/-- Exact interval telescope of the corrected-center recursion.  This is the
pathwise decomposition used before applying weighted Cauchy--Schwarz to the
predictable terms and martingale orthogonality to the innovation sum. -/
theorem correctedCenter_sub_eq_neg_smul_Ico_sum
    (S : Setup n d Ω) (omega : Ω) (alpha : ℝ) {a t : ℕ} (hat : a ≤ t) :
    correctedCenter S omega alpha t - correctedCenter S omega alpha a =
      (-alpha) • ∑ r ∈ Finset.Ico a t,
        ((gain S.network r) •
            gradient (averageObjective S)
              (correctedCenter S omega alpha r) +
          correctedDrift S omega alpha r + influenceNoise S omega r) := by
  induction t, hat using Nat.le_induction with
  | base => simp
  | @succ t hat ih =>
    rw [correctedCenter_succ, Finset.sum_Ico_succ_top hat]
    let z : Point d := correctedCenter S omega alpha t
    let v : Point d :=
      (gain S.network t) •
          gradient (averageObjective S) (correctedCenter S omega alpha t) +
        correctedDrift S omega alpha t + influenceNoise S omega t
    let q : Point d := ∑ r ∈ Finset.Ico a t,
      ((gain S.network r) •
          gradient (averageObjective S) (correctedCenter S omega alpha r) +
        correctedDrift S omega alpha r + influenceNoise S omega r)
    change z - alpha • v - correctedCenter S omega alpha a =
      (-alpha) • (q + v)
    have ih' : z - correctedCenter S omega alpha a = (-alpha) • q := by
      simpa [z, q] using ih
    rw [show z - alpha • v - correctedCenter S omega alpha a =
      (z - correctedCenter S omega alpha a) - alpha • v by module, ih']
    module

/-- Weighted finite-vector Cauchy--Schwarz in the form used for the gain and
drift pieces of the within-block movement estimate. -/
theorem norm_sq_finset_sum_nonneg_smul_le_sum_mul_weighted_energy
    {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ι) (w : ι → ℝ) (x : ι → E)
    (hw : ∀ i ∈ I, 0 ≤ w i) :
    ‖∑ i ∈ I, w i • x i‖ ^ 2 ≤
      (∑ i ∈ I, w i) * ∑ i ∈ I, w i * ‖x i‖ ^ 2 := by
  classical
  have hraw := norm_sq_finset_sum_smul_le_sum_sq_mul_sum_norm_sq I
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) • x i)
  have hsum :
      (∑ i ∈ I, Real.sqrt (w i) • (Real.sqrt (w i) • x i)) =
        ∑ i ∈ I, w i • x i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul, show Real.sqrt (w i) * Real.sqrt (w i) =
      Real.sqrt (w i) ^ 2 by ring, Real.sq_sqrt (hw i hi)]
  have hweights :
      (∑ i ∈ I, Real.sqrt (w i) ^ 2) = ∑ i ∈ I, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i hi)
  have henergy :
      (∑ i ∈ I, ‖Real.sqrt (w i) • x i‖ ^ 2) =
        ∑ i ∈ I, w i * ‖x i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (hw i hi)]
  rw [hsum, hweights, henergy] at hraw
  exact hraw

/-- Component smoothness transfers to the average gradient with the same
Lipschitz constant. -/
theorem average_gradient_norm_sub_le
    (S : Setup n d Ω) (x y : Point d) :
    ‖gradient (averageObjective S) x - gradient (averageObjective S) y‖ ≤
      S.L * ‖x - y‖ := by
  classical
  have hgradEq (z : Point d) :
      gradient (averageObjective S) z =
        (n : ℝ)⁻¹ • ∑ i : Fin n, gradient (S.localObjective i) z := by
    have hfun : averageObjective S =
        SOptLib.finiteUniformAverage S.localObjective := by
      funext q
      simp [averageObjective, SOptLib.finiteUniformAverage_def,
        Fintype.card_fin, smul_eq_mul]
    have h :=
      SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
        S.localObjective (fun i q => gradient (S.localObjective i) q) z
        (fun i => ((S.local_smooth i).1 z).hasGradientAt)
    rw [hfun]
    simpa [SOptLib.finiteUniformAverage_def, Fintype.card_fin] using h
  rw [hgradEq, hgradEq, ← smul_sub, ← Finset.sum_sub_distrib,
    norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ *
        ‖∑ i : Fin n,
          (gradient (S.localObjective i) x -
            gradient (S.localObjective i) y)‖ ≤
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        ‖gradient (S.localObjective i) x -
          gradient (S.localObjective i) y‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_sum_le Finset.univ fun i : Fin n =>
          gradient (S.localObjective i) x - gradient (S.localObjective i) y)
        (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, S.L * ‖x - y‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      exact Finset.sum_le_sum fun i _hi =>
        (S.local_smooth i).2.norm_sub_le x y
    _ = S.L * ‖x - y‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt S.hn)
      field_simp

/-- Integrated weighted Cauchy--Schwarz for the gain-gradient part of one
block.  Its right side is exactly `K_j D_j`. -/
theorem corrected_center_gain_gradient_block_energy_le
    (S : Setup n d Ω) (alpha : ℝ) (I : Finset ℕ) :
    SOptLib.expectation S.probability (fun omega =>
        ‖∑ r ∈ I, (gain S.network r) •
          gradient (averageObjective S)
            (correctedCenter S omega alpha r)‖ ^ 2) ≤
      (∑ r ∈ I, gain S.network r) *
        ∑ r ∈ I, gain S.network r *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha r)‖ ^ 2) := by
  classical
  let gradAt : ℕ → Ω → Point d := fun r omega =>
    gradient (averageObjective S) (correctedCenter S omega alpha r)
  have hgradMem (r : ℕ) : MemLp (gradAt r) 2 S.probability := by
    simpa [gradAt] using
      (corrected_center_descent_payload_memLp_two S alpha r).2.1
  have hsumMem : MemLp (fun omega =>
      ∑ r ∈ I, (gain S.network r) • gradAt r omega) 2 S.probability := by
    apply memLp_finset_sum I
    intro r _hr
    exact (hgradMem r).const_smul (gain S.network r)
  have hleftInt : Integrable (fun omega =>
      ‖∑ r ∈ I, (gain S.network r) • gradAt r omega‖ ^ 2)
      S.probability :=
    (memLp_two_iff_integrable_sq_norm hsumMem.aestronglyMeasurable).1 hsumMem
  have hgradSqInt (r : ℕ) : Integrable (fun omega => ‖gradAt r omega‖ ^ 2)
      S.probability :=
    (memLp_two_iff_integrable_sq_norm
      (hgradMem r).aestronglyMeasurable).1 (hgradMem r)
  have hweightedInt (r : ℕ) : Integrable (fun omega =>
      gain S.network r * ‖gradAt r omega‖ ^ 2) S.probability :=
    (hgradSqInt r).const_mul (gain S.network r)
  have hrightInt : Integrable (fun omega =>
      (∑ r ∈ I, gain S.network r) *
        ∑ r ∈ I, gain S.network r * ‖gradAt r omega‖ ^ 2)
      S.probability :=
    (integrable_finset_sum I fun r _hr => hweightedInt r).const_mul _
  have hpoint (omega : Ω) :
      ‖∑ r ∈ I, (gain S.network r) • gradAt r omega‖ ^ 2 ≤
        (∑ r ∈ I, gain S.network r) *
          ∑ r ∈ I, gain S.network r * ‖gradAt r omega‖ ^ 2 := by
    exact norm_sq_finset_sum_nonneg_smul_le_sum_mul_weighted_energy
      I (gain S.network) (fun r => gradAt r omega)
      (fun r _hr =>
        ((uniform_mixing_and_influence S.network).2.2.2.2.2.2.2.1.le.trans
          (gain_bounds_before_corrected_center_control S.network r).1))
  have hmono := MeasureTheory.integral_mono hleftInt hrightInt hpoint
  unfold SOptLib.expectation
  rw [MeasureTheory.integral_const_mul,
    integral_finset_sum I (fun r _hr => hweightedInt r)] at hmono
  simp_rw [MeasureTheory.integral_const_mul] at hmono
  simpa [gradAt] using hmono

/-- Integrated unweighted Cauchy--Schwarz for the corrected-drift part of one
block.  Its right side is exactly `m_j V_j`. -/
theorem corrected_center_drift_block_energy_le
    (S : Setup n d Ω) (alpha : ℝ) (I : Finset ℕ) :
    SOptLib.expectation S.probability (fun omega =>
        ‖∑ r ∈ I, correctedDrift S omega alpha r‖ ^ 2) ≤
      (I.card : ℝ) * ∑ r ∈ I,
        SOptLib.expectation S.probability (fun omega =>
          ‖correctedDrift S omega alpha r‖ ^ 2) := by
  classical
  let driftAt : ℕ → Ω → Point d := fun r omega =>
    correctedDrift S omega alpha r
  have hdriftMem (r : ℕ) : MemLp (driftAt r) 2 S.probability := by
    simpa [driftAt] using
      (corrected_center_descent_payload_memLp_two S alpha r).2.2.1
  have hsumMem : MemLp (fun omega => ∑ r ∈ I, driftAt r omega)
      2 S.probability := by
    apply memLp_finset_sum I
    intro r _hr
    exact hdriftMem r
  have hleftInt : Integrable (fun omega =>
      ‖∑ r ∈ I, driftAt r omega‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hsumMem.aestronglyMeasurable).1 hsumMem
  have hdriftSqInt (r : ℕ) : Integrable (fun omega => ‖driftAt r omega‖ ^ 2)
      S.probability :=
    (memLp_two_iff_integrable_sq_norm
      (hdriftMem r).aestronglyMeasurable).1 (hdriftMem r)
  have hrightInt : Integrable (fun omega =>
      (I.card : ℝ) * ∑ r ∈ I, ‖driftAt r omega‖ ^ 2) S.probability :=
    (integrable_finset_sum I fun r _hr => hdriftSqInt r).const_mul _
  have hpoint (omega : Ω) :
      ‖∑ r ∈ I, driftAt r omega‖ ^ 2 ≤
        (I.card : ℝ) * ∑ r ∈ I, ‖driftAt r omega‖ ^ 2 := by
    have hraw :=
      norm_sq_finset_sum_nonneg_smul_le_sum_mul_weighted_energy
        I (fun _ => (1 : ℝ)) (fun r => driftAt r omega)
        (fun _ _ => by norm_num)
    simpa using hraw
  have hmono := MeasureTheory.integral_mono hleftInt hrightInt hpoint
  unfold SOptLib.expectation
  rw [MeasureTheory.integral_const_mul,
    integral_finset_sum I (fun r _hr => hdriftSqInt r)] at hmono
  simpa [driftAt] using hmono

/-- The within-interval movement display preceding source equation (15), with
all three energies taken on the exact prefix from the block start to `t`. -/
theorem corrected_center_within_interval_gradient_movement
    (S : Setup n d Ω) (alpha : ℝ) {a t : ℕ} (hat : a ≤ t) :
    SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S) (correctedCenter S omega alpha t) -
          gradient (averageObjective S) (correctedCenter S omega alpha a)‖ ^ 2) ≤
      3 * (S.L * alpha) ^ 2 *
        ((∑ r ∈ Finset.Ico a t, gain S.network r) *
            ∑ r ∈ Finset.Ico a t, gain S.network r *
              SOptLib.expectation S.probability (fun omega =>
                ‖gradient (averageObjective S)
                  (correctedCenter S omega alpha r)‖ ^ 2) +
          ((Finset.Ico a t).card : ℝ) *
            ∑ r ∈ Finset.Ico a t,
              SOptLib.expectation S.probability (fun omega =>
                ‖correctedDrift S omega alpha r‖ ^ 2) +
          S.σ ^ 2 * ∑ r ∈ Finset.Ico a t,
            influenceEnergy S.network r) := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  let I := Finset.Ico a t
  let gradAt : ℕ → Ω → Point d := fun r omega =>
    gradient (averageObjective S) (correctedCenter S omega alpha r)
  let driftAt : ℕ → Ω → Point d := fun r omega =>
    correctedDrift S omega alpha r
  let noiseAt : ℕ → Ω → Point d := fun r omega => influenceNoise S omega r
  let A : Ω → Point d := fun omega =>
    ∑ r ∈ I, (gain S.network r) • gradAt r omega
  let B : Ω → Point d := fun omega => ∑ r ∈ I, driftAt r omega
  let C : Ω → Point d := fun omega => ∑ r ∈ I, noiseAt r omega
  have hgradMem (r : ℕ) : MemLp (gradAt r) 2 S.probability := by
    simpa [gradAt] using
      (corrected_center_descent_payload_memLp_two S alpha r).2.1
  have hdriftMem (r : ℕ) : MemLp (driftAt r) 2 S.probability := by
    simpa [driftAt] using
      (corrected_center_descent_payload_memLp_two S alpha r).2.2.1
  have hnoiseMem (r : ℕ) : MemLp (noiseAt r) 2 S.probability := by
    have hmom := weighted_noise_conditional_moments S r
      (influenceRow S.network r)
    have hint : Integrable (noiseAt r) S.probability := by
      simpa [noiseAt, influenceNoise] using hmom.1.1.integrable
    have hsq : Integrable (fun omega => ‖noiseAt r omega‖ ^ 2)
        S.probability := by
      simpa [noiseAt, influenceNoise] using hmom.2.1.integrable
    exact (memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable).2 hsq
  have hAMem : MemLp A 2 S.probability := by
    dsimp [A]
    apply memLp_finset_sum I
    intro r _hr
    exact (hgradMem r).const_smul (gain S.network r)
  have hBMem : MemLp B 2 S.probability := by
    dsimp [B]
    exact memLp_finset_sum I fun r _hr => hdriftMem r
  have hCMem : MemLp C 2 S.probability := by
    dsimp [C]
    exact memLp_finset_sum I fun r _hr => hnoiseMem r
  have hAInt : Integrable (fun omega => ‖A omega‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hAMem.aestronglyMeasurable).1 hAMem
  have hBInt : Integrable (fun omega => ‖B omega‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hBMem.aestronglyMeasurable).1 hBMem
  have hCInt : Integrable (fun omega => ‖C omega‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hCMem.aestronglyMeasurable).1 hCMem
  have hleftMem : MemLp (fun omega => gradAt t omega - gradAt a omega)
      2 S.probability := (hgradMem t).sub (hgradMem a)
  have hleftInt : Integrable (fun omega =>
      ‖gradAt t omega - gradAt a omega‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hleftMem.aestronglyMeasurable).1 hleftMem
  have hrightInt : Integrable (fun omega =>
      3 * (S.L * alpha) ^ 2 *
        (‖A omega‖ ^ 2 + ‖B omega‖ ^ 2 + ‖C omega‖ ^ 2)) S.probability :=
    ((hAInt.add hBInt).add hCInt).const_mul _
  have hpoint (omega : Ω) :
      ‖gradAt t omega - gradAt a omega‖ ^ 2 ≤
        3 * (S.L * alpha) ^ 2 *
          (‖A omega‖ ^ 2 + ‖B omega‖ ^ 2 + ‖C omega‖ ^ 2) := by
    have htel := correctedCenter_sub_eq_neg_smul_Ico_sum
      S omega alpha hat
    simp_rw [Finset.sum_add_distrib] at htel
    have htel' :
        correctedCenter S omega alpha t - correctedCenter S omega alpha a =
          (-alpha) • (A omega + B omega + C omega) := by
      simpa [I, A, B, C, gradAt, driftAt, noiseAt] using htel
    have hLip := average_gradient_norm_sub_le S
      (correctedCenter S omega alpha t) (correctedCenter S omega alpha a)
    have hLipSq :
        ‖gradAt t omega - gradAt a omega‖ ^ 2 ≤
          S.L ^ 2 *
            ‖correctedCenter S omega alpha t -
              correctedCenter S omega alpha a‖ ^ 2 := by
      have hrhs : 0 ≤ S.L *
          ‖correctedCenter S omega alpha t -
            correctedCenter S omega alpha a‖ :=
        mul_nonneg S.hL.le (norm_nonneg _)
      simpa [gradAt, mul_pow] using
        ((sq_le_sq₀ (norm_nonneg _) hrhs).2 hLip)
    have hthreeNorm :
        ‖A omega + B omega + C omega‖ ≤
          ‖A omega‖ + ‖B omega‖ + ‖C omega‖ := norm_add₃_le
    have hthree :
        ‖A omega + B omega + C omega‖ ^ 2 ≤
          3 * (‖A omega‖ ^ 2 + ‖B omega‖ ^ 2 + ‖C omega‖ ^ 2) := by
      have hsum_nonneg :
          0 ≤ ‖A omega‖ + ‖B omega‖ + ‖C omega‖ := by positivity
      have hsquare :=
        (sq_le_sq₀ (norm_nonneg _) hsum_nonneg).2 hthreeNorm
      nlinarith [hsquare,
        sq_nonneg (‖A omega‖ + ‖B omega‖ + ‖C omega‖),
        sq_nonneg (‖A omega‖ - ‖B omega‖),
        sq_nonneg (‖A omega‖ - ‖C omega‖),
        sq_nonneg (‖B omega‖ - ‖C omega‖)]
    rw [htel', norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs] at hLipSq
    have hscale := mul_le_mul_of_nonneg_left hthree
      (mul_nonneg (sq_nonneg S.L) (sq_nonneg alpha))
    nlinarith
  have hmono := MeasureTheory.integral_mono hleftInt hrightInt hpoint
  have hA := corrected_center_gain_gradient_block_energy_le S alpha I
  have hB := corrected_center_drift_block_energy_le S alpha I
  have hC := influence_noise_finset_sum_expected_norm_sq_le S I
  unfold SOptLib.expectation at hmono hA hB hC ⊢
  rw [MeasureTheory.integral_const_mul] at hmono
  have hintABC :
      (∫ omega, ‖A omega‖ ^ 2 + ‖B omega‖ ^ 2 + ‖C omega‖ ^ 2
          ∂S.probability) =
        (∫ omega, ‖A omega‖ ^ 2 ∂S.probability) +
          (∫ omega, ‖B omega‖ ^ 2 ∂S.probability) +
          ∫ omega, ‖C omega‖ ^ 2 ∂S.probability := by
    calc
      _ = (∫ omega, ‖A omega‖ ^ 2 + ‖B omega‖ ^ 2 ∂S.probability) +
          ∫ omega, ‖C omega‖ ^ 2 ∂S.probability :=
        MeasureTheory.integral_add (hAInt.add hBInt) hCInt
      _ = _ := by rw [MeasureTheory.integral_add hAInt hBInt]
  rw [hintABC] at hmono
  have hsum :
      (∫ omega, ‖A omega‖ ^ 2 ∂S.probability) +
          (∫ omega, ‖B omega‖ ^ 2 ∂S.probability) +
          ∫ omega, ‖C omega‖ ^ 2 ∂S.probability ≤
        ((∑ r ∈ I, gain S.network r) *
            ∑ r ∈ I, gain S.network r *
              ∫ omega, ‖gradAt r omega‖ ^ 2 ∂S.probability) +
          (I.card : ℝ) *
            ∑ r ∈ I, ∫ omega, ‖driftAt r omega‖ ^ 2 ∂S.probability +
          S.σ ^ 2 * ∑ r ∈ I, influenceEnergy S.network r := by
    dsimp [A, B, C, gradAt, driftAt, noiseAt] at hA hB hC ⊢
    linarith
  have hcoef : 0 ≤ 3 * (S.L * alpha) ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  exact hmono.trans (mul_le_mul_of_nonneg_left hsum hcoef)

/-- Integrated binary norm-square comparison.  This packages the two
pointwise Young inequalities used to compare every block gradient with the
gradient at the block's left endpoint. -/
theorem expectation_norm_sq_le_two_add_two_sub
    (μ : Measure Ω) (f g : Ω → Point d)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    SOptLib.expectation μ (fun omega => ‖f omega‖ ^ 2) ≤
      2 * SOptLib.expectation μ (fun omega => ‖g omega‖ ^ 2) +
        2 * SOptLib.expectation μ (fun omega => ‖f omega - g omega‖ ^ 2) := by
  have hsub : MemLp (fun omega => f omega - g omega) 2 μ := hf.sub hg
  have hfInt : Integrable (fun omega => ‖f omega‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hgInt : Integrable (fun omega => ‖g omega‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have hsubInt : Integrable (fun omega => ‖f omega - g omega‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hsub.aestronglyMeasurable).1 hsub
  have hrhsInt : Integrable (fun omega =>
      2 * ‖g omega‖ ^ 2 + 2 * ‖f omega - g omega‖ ^ 2) μ :=
    (hgInt.const_mul 2).add (hsubInt.const_mul 2)
  have hpoint (omega : Ω) :
      ‖f omega‖ ^ 2 ≤
        2 * ‖g omega‖ ^ 2 + 2 * ‖f omega - g omega‖ ^ 2 := by
    have hyoung := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
      (f omega - g omega) (g omega)
    simpa [sub_add_cancel, add_comm] using hyoung
  unfold SOptLib.expectation
  calc
    (∫ omega, ‖f omega‖ ^ 2 ∂μ) ≤
        ∫ omega, 2 * ‖g omega‖ ^ 2 +
          2 * ‖f omega - g omega‖ ^ 2 ∂μ :=
      MeasureTheory.integral_mono hfInt hrhsInt hpoint
    _ = 2 * (∫ omega, ‖g omega‖ ^ 2 ∂μ) +
        2 * ∫ omega, ‖f omega - g omega‖ ^ 2 ∂μ := by
      rw [MeasureTheory.integral_add, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      · exact hgInt.const_mul 2
      · exact hsubInt.const_mul 2

/-- Scalar block-start elimination used in source equation (15).  If every
point of a finite block is within squared-gradient energy `R` of its first
point, the gain-weighted block energy controls the unweighted block energy.
The constants `4` and `6` are the two applications of
`‖x‖² ≤ 2‖y‖² + 2‖x-y‖²` in the source proof. -/
theorem finset_energy_le_of_start_comparisons
    (I : Finset ℕ) (k e : ℕ → ℝ) (a : ℕ) (R : ℝ)
    (hk : ∀ t ∈ I, 0 ≤ k t)
    (hK : 0 < ∑ t ∈ I, k t)
    (hforward : ∀ t ∈ I, e t ≤ 2 * e a + 2 * R)
    (hbackward : ∀ t ∈ I, e a ≤ 2 * e t + 2 * R) :
    ∑ t ∈ I, e t ≤
      4 * ((I.card : ℝ) / (∑ t ∈ I, k t)) *
          (∑ t ∈ I, k t * e t) +
        6 * (I.card : ℝ) * R := by
  classical
  let K : ℝ := ∑ t ∈ I, k t
  let D : ℝ := ∑ t ∈ I, k t * e t
  let m : ℝ := I.card
  have hweighted := Finset.sum_le_sum fun t ht =>
    mul_le_mul_of_nonneg_left (hbackward t ht) (hk t ht)
  have hweighted' : K * e a ≤ 2 * D + 2 * K * R := by
    dsimp [K, D]
    calc
      (∑ t ∈ I, k t) * e a = ∑ t ∈ I, k t * e a := by
        rw [Finset.sum_mul]
      _ ≤ ∑ t ∈ I, k t * (2 * e t + 2 * R) := hweighted
      _ = 2 * (∑ t ∈ I, k t * e t) +
          2 * (∑ t ∈ I, k t) * R := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp_rw [show ∀ t, k t * (2 * e t) = 2 * (k t * e t) by
          intro t
          ring]
        simp_rw [show ∀ t, k t * (2 * R) = 2 * k t * R by
          intro t
          ring]
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        have htwo : (∑ t ∈ I, 2 * k t) = 2 * (∑ t ∈ I, k t) := by
          rw [Finset.mul_sum]
        rw [htwo]
  have hunweighted := Finset.sum_le_sum fun t ht => hforward t ht
  have hunweighted' : ∑ t ∈ I, e t ≤ 2 * m * e a + 2 * m * R := by
    calc
      _ ≤ ∑ t ∈ I, (2 * e a + 2 * R) := hunweighted
      _ = 2 * m * e a + 2 * m * R := by
        simp [m]
        ring
  have hea : e a ≤ 2 * D / K + 2 * R := by
    calc
      e a ≤ (2 * D + 2 * K * R) / K := (le_div_iff₀ hK).2 (by
        rw [mul_comm]
        exact hweighted')
      _ = 2 * D / K + 2 * R := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          (2 * D + 2 * K * R) * K⁻¹ =
              2 * D * K⁻¹ + 2 * R * (K * K⁻¹) := by ring
          _ = 2 * D * K⁻¹ + 2 * R := by
            rw [mul_inv_cancel₀ (ne_of_gt hK)]
            ring
  have hm : 0 ≤ m := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hea
    (show 0 ≤ 2 * m by positivity)
  have hscaled' : 2 * m * e a ≤
      4 * m * (D / K) + 4 * m * R := by
    calc
      2 * m * e a ≤ 2 * m * (2 * D / K + 2 * R) := hscaled
      _ = 4 * m * (D / K) + 4 * m * R := by ring
  calc
    ∑ t ∈ I, e t ≤
        4 * m * (D / K) + 6 * m * R := by
      linarith [hunweighted', hscaled']
    _ = 4 * ((I.card : ℝ) / (∑ t ∈ I, k t)) *
          (∑ t ∈ I, k t * e t) + 6 * (I.card : ℝ) * R := by
      dsimp [K, D, m]
      ring

/-- The scalar constant calculation completing source equation (15).  The
dimensionless block budget `s K ≤ ε` turns the coefficient
`4 + 18 (s K)²` into the printed constant `5`. -/
theorem finset_energy_le_five_of_block_movement
    (I : Finset ℕ) (k e : ℕ → ℝ) (a : ℕ) (s V W : ℝ)
    (hk : ∀ t ∈ I, 0 ≤ k t)
    (he : ∀ t ∈ I, 0 ≤ e t)
    (hK : 0 < ∑ t ∈ I, k t)
    (hs : 0 ≤ s) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hsK : s * (∑ t ∈ I, k t) ≤ epsilon)
    (hforward : ∀ t ∈ I,
      e t ≤ 2 * e a + 6 * s ^ 2 *
        ((∑ r ∈ I, k r) * (∑ r ∈ I, k r * e r) +
          (I.card : ℝ) * V + W))
    (hbackward : ∀ t ∈ I,
      e a ≤ 2 * e t + 6 * s ^ 2 *
        ((∑ r ∈ I, k r) * (∑ r ∈ I, k r * e r) +
          (I.card : ℝ) * V + W)) :
    ∑ t ∈ I, e t ≤
      5 * ((I.card : ℝ) / (∑ t ∈ I, k t)) *
          (∑ t ∈ I, k t * e t) +
        18 * s ^ 2 * (I.card : ℝ) ^ 2 * V +
        18 * s ^ 2 * (I.card : ℝ) * W := by
  classical
  let K : ℝ := ∑ t ∈ I, k t
  let D : ℝ := ∑ t ∈ I, k t * e t
  let m : ℝ := I.card
  let R : ℝ := 3 * s ^ 2 * (K * D + m * V + W)
  have hforward' : ∀ t ∈ I, e t ≤ 2 * e a + 2 * R := by
    intro t ht
    convert hforward t ht using 1 <;> dsimp [R, K, D, m] <;> ring
  have hbackward' : ∀ t ∈ I, e a ≤ 2 * e t + 2 * R := by
    intro t ht
    convert hbackward t ht using 1 <;> dsimp [R, K, D, m] <;> ring
  have hbase := finset_energy_le_of_start_comparisons
    I k e a R hk hK hforward' hbackward'
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun t ht =>
      mul_nonneg (hk t ht) (he t ht)
  have hm : 0 ≤ m := by positivity
  have hratio : 0 ≤ m / K := div_nonneg hm hK.le
  have hsK_nonneg : 0 ≤ s * K := mul_nonneg hs hK.le
  have hsK' : s * K ≤ epsilon := by simpa [K] using hsK
  have hsq : s ^ 2 * K ^ 2 ≤ epsilon ^ 2 := by
    nlinarith [sq_le_sq₀ hsK_nonneg (by norm_num [epsilon]) |>.2 hsK']
  have hcoef : 4 + 18 * s ^ 2 * K ^ 2 ≤ 5 := by
    norm_num [epsilon] at hsq ⊢
    nlinarith
  have hcoefScaled := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg hratio hD)
  calc
    ∑ t ∈ I, e t ≤
        4 * (m / K) * D + 6 * m * R := by
      simpa [K, D, m] using hbase
    _ = (4 + 18 * s ^ 2 * K ^ 2) * (m / K) * D +
        18 * s ^ 2 * m ^ 2 * V + 18 * s ^ 2 * m * W := by
      dsimp [R]
      rw [div_eq_mul_inv]
      have hcancel : K ^ 2 * K⁻¹ = K := by
        calc
          K ^ 2 * K⁻¹ = K * (K * K⁻¹) := by ring
          _ = K := by rw [mul_inv_cancel₀ (ne_of_gt hK)]; ring
      have hcancelm : m * K ^ 2 * K⁻¹ = m * K := by
        rw [mul_assoc, hcancel]
      ring_nf
      rw [hcancelm]
    _ ≤ 5 * (m / K) * D +
        18 * s ^ 2 * m ^ 2 * V + 18 * s ^ 2 * m * W := by
      linarith
    _ = _ := by
      dsimp [K, D, m]

/-- Source equation (15) on one contiguous gain-budget block.  Prefix
movement is enlarged to the whole block and then the block-start gradient is
eliminated by the preceding scalar lemma. -/
theorem corrected_center_block_gradient_energy_le
    (S : Setup n d Ω) (alpha : ℝ) {a b : ℕ} (hab : a < b)
    (hK : 0 < ∑ t ∈ Finset.Ico a b, gain S.network t)
    (hbudget : (S.L * alpha) *
      (∑ t ∈ Finset.Ico a b, gain S.network t) ≤ epsilon)
    (halpha : 0 < alpha) :
    ∑ t ∈ Finset.Ico a b,
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
            (correctedCenter S omega alpha t)‖ ^ 2) ≤
      5 * (((Finset.Ico a b).card : ℝ) /
          (∑ t ∈ Finset.Ico a b, gain S.network t)) *
        (∑ t ∈ Finset.Ico a b, gain S.network t *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) +
      18 * (S.L * alpha) ^ 2 * ((Finset.Ico a b).card : ℝ) ^ 2 *
        (∑ t ∈ Finset.Ico a b,
          SOptLib.expectation S.probability (fun omega =>
            ‖correctedDrift S omega alpha t‖ ^ 2)) +
      18 * (S.L * alpha) ^ 2 * ((Finset.Ico a b).card : ℝ) *
        (S.σ ^ 2 * ∑ t ∈ Finset.Ico a b,
          influenceEnergy S.network t) := by
  classical
  let I := Finset.Ico a b
  let k : ℕ → ℝ := fun t => gain S.network t
  let e : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2)
  let V : ℝ := ∑ t ∈ I,
    SOptLib.expectation S.probability (fun omega =>
      ‖correctedDrift S omega alpha t‖ ^ 2)
  let Q : ℝ := ∑ t ∈ I, influenceEnergy S.network t
  let W : ℝ := S.σ ^ 2 * Q
  have hgain (t : ℕ) : 0 ≤ k t := by
    dsimp [k]
    unfold gain dotProduct
    exact Finset.sum_nonneg fun q _hq =>
      mul_nonneg ((absoluteProbability_mem_stdSimplex S.network (t + 1)).1 q)
        (pushMass_nonneg S.network t q)
  have he (t : ℕ) : 0 ≤ e t := by
    dsimp [e, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hdrift (t : ℕ) : 0 ≤ SOptLib.expectation S.probability
      (fun omega => ‖correctedDrift S omega alpha t‖ ^ 2) := by
    unfold SOptLib.expectation
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have henergy (t : ℕ) : 0 ≤ influenceEnergy S.network t := by
    unfold influenceEnergy
    exact Finset.sum_nonneg fun i _hi => sq_nonneg (influenceRow S.network t i)
  have hV : 0 ≤ V := Finset.sum_nonneg fun t _ht => hdrift t
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun t _ht => henergy t
  have hW : 0 ≤ W := mul_nonneg (sq_nonneg _) hQ
  have hgradMem (t : ℕ) : MemLp (fun omega =>
      gradient (averageObjective S) (correctedCenter S omega alpha t))
      2 S.probability :=
    (corrected_center_descent_payload_memLp_two S alpha t).2.1
  have hmovement (t : ℕ) (ht : t ∈ I) :
      SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S) (correctedCenter S omega alpha t) -
          gradient (averageObjective S) (correctedCenter S omega alpha a)‖ ^ 2) ≤
        3 * (S.L * alpha) ^ 2 *
          ((∑ r ∈ I, k r) * (∑ r ∈ I, k r * e r) +
            (I.card : ℝ) * V + W) := by
    have hat : a ≤ t := (Finset.mem_Ico.1 ht).1
    have htb : t ≤ b := (Finset.mem_Ico.1 ht).2.le
    have hsubset : Finset.Ico a t ⊆ I := by
      dsimp [I]
      exact Finset.Ico_subset_Ico_right htb
    have hKpre : (∑ r ∈ Finset.Ico a t, k r) ≤ ∑ r ∈ I, k r :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _hr _hnot => hgain r)
    have hDpre : (∑ r ∈ Finset.Ico a t, k r * e r) ≤
        ∑ r ∈ I, k r * e r :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _hr _hnot => mul_nonneg (hgain r) (he r))
    have hVpre : (∑ r ∈ Finset.Ico a t,
        SOptLib.expectation S.probability (fun omega =>
          ‖correctedDrift S omega alpha r‖ ^ 2)) ≤ V := by
      dsimp [V]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _hr _hnot => hdrift r)
    have hQpre : (∑ r ∈ Finset.Ico a t,
        influenceEnergy S.network r) ≤ Q := by
      dsimp [Q]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _hr _hnot => henergy r)
    have hcard : ((Finset.Ico a t).card : ℝ) ≤ (I.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hKpre0 : 0 ≤ ∑ r ∈ Finset.Ico a t, k r :=
      Finset.sum_nonneg fun r _hr => hgain r
    have hKfull0 : 0 ≤ ∑ r ∈ I, k r :=
      Finset.sum_nonneg fun r _hr => hgain r
    have hDpre0 : 0 ≤ ∑ r ∈ Finset.Ico a t, k r * e r :=
      Finset.sum_nonneg fun r _hr => mul_nonneg (hgain r) (he r)
    have hDfull0 : 0 ≤ ∑ r ∈ I, k r * e r :=
      Finset.sum_nonneg fun r _hr => mul_nonneg (hgain r) (he r)
    have hprod := mul_le_mul hKpre hDpre hDpre0 hKfull0
    have hcardV := mul_le_mul hcard hVpre
      (Finset.sum_nonneg fun r _hr => hdrift r) (by positivity)
    have hnoise := mul_le_mul_of_nonneg_left hQpre (sq_nonneg S.σ)
    have hinside :
        (∑ r ∈ Finset.Ico a t, k r) *
            (∑ r ∈ Finset.Ico a t, k r * e r) +
          ((Finset.Ico a t).card : ℝ) *
            (∑ r ∈ Finset.Ico a t,
              SOptLib.expectation S.probability (fun omega =>
                ‖correctedDrift S omega alpha r‖ ^ 2)) +
          S.σ ^ 2 * (∑ r ∈ Finset.Ico a t,
            influenceEnergy S.network r) ≤
        (∑ r ∈ I, k r) * (∑ r ∈ I, k r * e r) +
          (I.card : ℝ) * V + W := by
      dsimp [W]
      linarith
    have hraw := corrected_center_within_interval_gradient_movement
      S alpha hat
    have hcoef : 0 ≤ 3 * (S.L * alpha) ^ 2 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hinside hcoef
    simpa [I, k, e, V, Q, W] using hraw.trans hscaled
  have hforward : ∀ t ∈ I, e t ≤ 2 * e a +
      6 * (S.L * alpha) ^ 2 *
        ((∑ r ∈ I, k r) * (∑ r ∈ I, k r * e r) +
          (I.card : ℝ) * V + W) := by
    intro t ht
    have hcompare := expectation_norm_sq_le_two_add_two_sub
      S.probability
      (fun omega => gradient (averageObjective S)
        (correctedCenter S omega alpha t))
      (fun omega => gradient (averageObjective S)
        (correctedCenter S omega alpha a))
      (hgradMem t) (hgradMem a)
    dsimp [e] at hcompare ⊢
    linarith [hmovement t ht]
  have hbackward : ∀ t ∈ I, e a ≤ 2 * e t +
      6 * (S.L * alpha) ^ 2 *
        ((∑ r ∈ I, k r) * (∑ r ∈ I, k r * e r) +
          (I.card : ℝ) * V + W) := by
    intro t ht
    have hcompare := expectation_norm_sq_le_two_add_two_sub
      S.probability
      (fun omega => gradient (averageObjective S)
        (correctedCenter S omega alpha a))
      (fun omega => gradient (averageObjective S)
        (correctedCenter S omega alpha t))
      (hgradMem a) (hgradMem t)
    have hreverse : SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S) (correctedCenter S omega alpha a) -
          gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2) =
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S) (correctedCenter S omega alpha t) -
            gradient (averageObjective S) (correctedCenter S omega alpha a)‖ ^ 2) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with omega
      rw [norm_sub_rev]
    dsimp [e] at hcompare ⊢
    rw [hreverse] at hcompare
    linarith [hmovement t ht]
  have hmain := finset_energy_le_five_of_block_movement
    I k e a (S.L * alpha) V W (fun t _ht => hgain t) (fun t _ht => he t)
    (by simpa [I, k] using hK) (mul_nonneg S.hL.le halpha.le) hV hW
    (by simpa [I, k] using hbudget) hforward hbackward
  simpa [I, k, e, V, Q, W] using hmain

/-- The exact gain-weighted expected smooth-descent inequality used in source
equation (16), before replacing the time-varying gain by its uniform floor or
absorbing the drift terms.  The two innovation cross terms vanish by the
source filtration contract, while the sharp `L/2` noise coefficient is kept. -/
theorem corrected_center_expected_one_step_gain_descent
    (S : Setup n d Ω) (alpha : ℝ) (halpha : 0 < alpha) (t : ℕ) :
    alpha * gain S.network t *
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
            (correctedCenter S omega alpha t)‖ ^ 2) ≤
      SOptLib.expectation S.probability (fun omega =>
        averageObjective S (correctedCenter S omega alpha t) -
          averageObjective S (correctedCenter S omega alpha (t + 1))) -
      alpha * SOptLib.expectation S.probability (fun omega =>
        ⟪gradient (averageObjective S) (correctedCenter S omega alpha t),
          correctedDrift S omega alpha t⟫_ℝ) +
      (S.L * alpha ^ 2 / 2) *
        SOptLib.expectation S.probability (fun omega =>
          ‖(gain S.network t) •
                gradient (averageObjective S)
                  (correctedCenter S omega alpha t) +
              correctedDrift S omega alpha t‖ ^ 2) +
      S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
        influenceEnergy S.network t := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  let k : ℝ := gain S.network t
  have hpayload := corrected_center_descent_payload_memLp_two S alpha t
  have hgrad_mem := hpayload.2.1
  have hdrift_mem := hpayload.2.2.1
  have hcombined_mem := hpayload.2.2.2
  have hgrad_sq : Integrable (fun omega =>
      ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2)
      S.probability :=
    (memLp_two_iff_integrable_sq_norm hgrad_mem.aestronglyMeasurable).1
      hgrad_mem
  have hdrift_sq : Integrable (fun omega =>
      ‖correctedDrift S omega alpha t‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hdrift_mem.aestronglyMeasurable).1
      hdrift_mem
  have hcombined_sq : Integrable (fun omega =>
      ‖(gain S.network t) •
          gradient (averageObjective S) (correctedCenter S omega alpha t) +
        correctedDrift S omega alpha t‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hcombined_mem.aestronglyMeasurable).1
      hcombined_mem
  have hinner : Integrable (fun omega =>
      ⟪gradient (averageObjective S) (correctedCenter S omega alpha t),
        correctedDrift S omega alpha t⟫_ℝ) S.probability :=
    integrable_inner_of_integrable_sq_norm
      hgrad_mem.aestronglyMeasurable hdrift_mem.aestronglyMeasurable
      hgrad_sq hdrift_sq
  have hgrad_meas : Measurable[preSamplingHistory S t] (fun omega =>
      gradient (averageObjective S) (correctedCenter S omega alpha t)) := by
    have hcenter := (correctedCenter_and_drift_measurable S alpha).1 t
    have hgradEq (x : Point d) :
        gradient (averageObjective S) x =
          (n : ℝ)⁻¹ • ∑ i : Fin n, gradient (S.localObjective i) x := by
      have hfun : averageObjective S =
          SOptLib.finiteUniformAverage S.localObjective := by
        funext z
        simp [averageObjective, SOptLib.finiteUniformAverage_def,
          Fintype.card_fin, smul_eq_mul]
      rw [hfun]
      have h :=
        SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
          S.localObjective (fun i z => gradient (S.localObjective i) z) x
          (fun i => ((S.local_smooth i).1 x).hasGradientAt)
      simpa [SOptLib.finiteUniformAverage_def, Fintype.card_fin] using h
    have hsum : Measurable[preSamplingHistory S t] (fun omega =>
        ∑ i : Fin n,
          gradient (S.localObjective i) (correctedCenter S omega alpha t)) := by
      apply Finset.measurable_sum
      intro i _hi
      exact (S.local_smooth i).2.continuous.measurable.comp hcenter
    simpa only [hgradEq] using hsum.const_smul ((n : ℝ)⁻¹)
  have hcombined_meas : Measurable[preSamplingHistory S t] (fun omega =>
      (gain S.network t) •
          gradient (averageObjective S) (correctedCenter S omega alpha t) +
        correctedDrift S omega alpha t) :=
    hgrad_meas.const_smul (gain S.network t) |>.add
      ((correctedCenter_and_drift_measurable S alpha).2 t)
  have hcross_grad := influence_noise_martingale_interface S t
    (fun omega =>
      gradient (averageObjective S) (correctedCenter S omega alpha t))
    hgrad_meas hgrad_mem
  have hcross_combined := influence_noise_martingale_interface S t
    (fun omega =>
      (gain S.network t) •
          gradient (averageObjective S) (correctedCenter S omega alpha t) +
        correctedDrift S omega alpha t)
    hcombined_meas hcombined_mem
  have hnoise_sq : Integrable (fun omega =>
      ‖influenceNoise S omega t‖ ^ 2) S.probability := by
    have hmom := weighted_noise_conditional_moments S t
      (influenceRow S.network t)
    simpa [influenceNoise, influenceEnergy] using hmom.2.1.integrable
  have hobj := corrected_center_objective_integrable S alpha t
  have hobj_next := corrected_center_objective_integrable S alpha (t + 1)
  let A : Ω → ℝ := fun omega => alpha * k *
    ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2
  let Drop : Ω → ℝ := fun omega =>
    averageObjective S (correctedCenter S omega alpha t) -
      averageObjective S (correctedCenter S omega alpha (t + 1))
  let DriftCross : Ω → ℝ := fun omega => -alpha *
    ⟪gradient (averageObjective S) (correctedCenter S omega alpha t),
      correctedDrift S omega alpha t⟫_ℝ
  let Combined : Ω → ℝ := fun omega => (S.L * alpha ^ 2 / 2) *
    ‖k • gradient (averageObjective S) (correctedCenter S omega alpha t) +
      correctedDrift S omega alpha t‖ ^ 2
  let CrossGrad : Ω → ℝ := fun omega => -alpha *
    ⟪gradient (averageObjective S) (correctedCenter S omega alpha t),
      influenceNoise S omega t⟫_ℝ
  let CrossCombined : Ω → ℝ := fun omega => S.L * alpha ^ 2 *
    ⟪k • gradient (averageObjective S) (correctedCenter S omega alpha t) +
        correctedDrift S omega alpha t,
      influenceNoise S omega t⟫_ℝ
  let Noise : Ω → ℝ := fun omega => (S.L * alpha ^ 2 / 2) *
    ‖influenceNoise S omega t‖ ^ 2
  have hA : Integrable A S.probability := hgrad_sq.const_mul _
  have hDrop : Integrable Drop S.probability := hobj.sub hobj_next
  have hDriftCross : Integrable DriftCross S.probability := hinner.const_mul _
  have hCombined : Integrable Combined S.probability := by
    simpa [Combined, k] using hcombined_sq.const_mul (S.L * alpha ^ 2 / 2)
  have hCrossGrad : Integrable CrossGrad S.probability :=
    hcross_grad.1.const_mul _
  have hCrossCombined : Integrable CrossCombined S.probability := by
    simpa [CrossCombined, k] using hcross_combined.1.const_mul (S.L * alpha ^ 2)
  have hNoise : Integrable Noise S.probability := hnoise_sq.const_mul _
  have hpoint : ∀ omega, A omega ≤
      (((((Drop omega + DriftCross omega) + Combined omega) +
        CrossGrad omega) + CrossCombined omega) + Noise omega) := by
    intro omega
    have hstep := corrected_center_smooth_step_exact S omega alpha halpha t
    dsimp [A, Drop, DriftCross, Combined, CrossGrad, CrossCombined, Noise, k]
    nlinarith
  have hintegral := MeasureTheory.integral_mono hA
    (((((hDrop.add hDriftCross).add hCombined).add hCrossGrad).add
      hCrossCombined).add hNoise) hpoint
  have hcross_grad_scaled :
      (∫ omega, CrossGrad omega ∂S.probability) = 0 := by
    dsimp [CrossGrad]
    rw [MeasureTheory.integral_const_mul, hcross_grad.2.1, mul_zero]
  have hcross_combined_scaled :
      (∫ omega, CrossCombined omega ∂S.probability) = 0 := by
    dsimp [CrossCombined, k]
    rw [MeasureTheory.integral_const_mul, hcross_combined.2.1, mul_zero]
  have hIntegralDriftCross :
      (∫ omega, Drop omega + DriftCross omega ∂S.probability) =
        (∫ omega, Drop omega ∂S.probability) +
          ∫ omega, DriftCross omega ∂S.probability := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add hDrop hDriftCross
  have hIntegralCombined :
      (∫ omega, (Drop omega + DriftCross omega) + Combined omega
          ∂S.probability) =
        (∫ omega, Drop omega + DriftCross omega ∂S.probability) +
          ∫ omega, Combined omega ∂S.probability := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add (hDrop.add hDriftCross) hCombined
  have hIntegralCrossGrad :
      (∫ omega, ((Drop omega + DriftCross omega) + Combined omega) +
          CrossGrad omega ∂S.probability) =
        (∫ omega, (Drop omega + DriftCross omega) + Combined omega
          ∂S.probability) +
          ∫ omega, CrossGrad omega ∂S.probability := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add ((hDrop.add hDriftCross).add hCombined)
        hCrossGrad
  have hIntegralCrossCombined :
      (∫ omega, (((Drop omega + DriftCross omega) + Combined omega) +
          CrossGrad omega) + CrossCombined omega ∂S.probability) =
        (∫ omega, ((Drop omega + DriftCross omega) + Combined omega) +
          CrossGrad omega ∂S.probability) +
          ∫ omega, CrossCombined omega ∂S.probability := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add
        (((hDrop.add hDriftCross).add hCombined).add hCrossGrad)
        hCrossCombined
  have hIntegralNoise :
      (∫ omega, ((((Drop omega + DriftCross omega) + Combined omega) +
          CrossGrad omega) + CrossCombined omega) + Noise omega
          ∂S.probability) =
        (∫ omega, (((Drop omega + DriftCross omega) + Combined omega) +
          CrossGrad omega) + CrossCombined omega ∂S.probability) +
          ∫ omega, Noise omega ∂S.probability := by
    simpa only [Pi.add_apply] using
      MeasureTheory.integral_add
        ((((hDrop.add hDriftCross).add hCombined).add hCrossGrad).add
          hCrossCombined) hNoise
  have hexpanded :
      (∫ omega, A omega ∂S.probability) ≤
        (∫ omega, Drop omega ∂S.probability) +
        (∫ omega, DriftCross omega ∂S.probability) +
        (∫ omega, Combined omega ∂S.probability) +
        (∫ omega, Noise omega ∂S.probability) := by
    simp only [Pi.add_apply] at hintegral
    rw [hIntegralNoise, hIntegralCrossCombined, hIntegralCrossGrad,
      hIntegralCombined, hIntegralDriftCross,
      hcross_grad_scaled, hcross_combined_scaled] at hintegral
    linarith
  have hnoise_scaled :
      (∫ omega, Noise omega ∂S.probability) ≤
        S.L * alpha ^ 2 / 2 *
          (S.σ ^ 2 * influenceEnergy S.network t) := by
    dsimp [Noise]
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hcross_grad.2.2
      (div_nonneg (mul_nonneg S.hL.le (sq_nonneg alpha)) (by norm_num))
  calc
    alpha * gain S.network t *
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
            (correctedCenter S omega alpha t)‖ ^ 2) =
      ∫ omega, A omega ∂S.probability := by
        dsimp [A, k, SOptLib.expectation]
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (∫ omega, Drop omega ∂S.probability) +
        (∫ omega, DriftCross omega ∂S.probability) +
        (∫ omega, Combined omega ∂S.probability) +
        (∫ omega, Noise omega ∂S.probability) := hexpanded
    _ ≤ (∫ omega, Drop omega ∂S.probability) +
        (∫ omega, DriftCross omega ∂S.probability) +
        (∫ omega, Combined omega ∂S.probability) +
        S.L * alpha ^ 2 / 2 *
          (S.σ ^ 2 * influenceEnergy S.network t) := by linarith
    _ = _ := by
      dsimp [Drop, DriftCross, Combined, k, SOptLib.expectation]
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      ring

/-- The objective-drop part of source equation (16).  Multiplying the exact
one-step descent inequality by any nonnegative nonincreasing deterministic
weight sequence costs only the first weight times the declared initial gap;
all internal boundary terms and the terminal gap have the favorable sign. -/
theorem corrected_center_weighted_objective_drop_telescope
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon)
    (w : ℕ → ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_anti : ∀ t, w (t + 1) ≤ w t) :
    (∑ t ∈ Finset.range T.1,
        w t * SOptLib.expectation S.probability (fun omega =>
          averageObjective S (correctedCenter S omega alpha t) -
            averageObjective S (correctedCenter S omega alpha (t + 1)))) ≤
      w 0 * S.Δ := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  let lower : ℝ := sInf (Set.range (averageObjective S))
  let F : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      averageObjective S (correctedCenter S omega alpha t)) - lower
  have hbdd : BddBelow (Set.range (averageObjective S)) := by
    simpa [averageObjective] using S.average_lower_bounded
  have hF_nonneg (t : ℕ) : 0 ≤ F t := by
    have hobj := corrected_center_objective_integrable S alpha t
    have hlower : lower ≤
        SOptLib.expectation S.probability (fun omega =>
          averageObjective S (correctedCenter S omega alpha t)) := by
      have hmono := MeasureTheory.integral_mono
        (integrable_const lower) hobj (fun omega =>
          csInf_le hbdd ⟨correctedCenter S omega alpha t, rfl⟩)
      simpa [lower, SOptLib.expectation] using hmono
    dsimp [F]
    linarith
  have hdrop (t : ℕ) :
      SOptLib.expectation S.probability (fun omega =>
          averageObjective S (correctedCenter S omega alpha t) -
            averageObjective S (correctedCenter S omega alpha (t + 1))) =
        F t - F (t + 1) := by
    have hobj := corrected_center_objective_integrable S alpha t
    have hobj_next := corrected_center_objective_integrable S alpha (t + 1)
    dsimp [F]
    unfold SOptLib.expectation
    rw [MeasureTheory.integral_sub hobj hobj_next]
    ring
  let c : ℕ → ℝ := fun k => w (k - 1)
  let beta : ℕ → ℝ := fun _ => 1
  have hc_mono : ∀ k, 1 ≤ k → k < T.1 →
      c (k + 1) ≤ c k * beta k := by
    intro k hk _hkT
    have hkpred : k - 1 + 1 = k := Nat.sub_add_cancel hk
    dsimp [c, beta]
    simpa [Nat.add_sub_cancel, hkpred] using hw_anti (k - 1)
  have htelescope := sum_weighted_sub_mul_le_first_sub_tail
    c beta F T.1 T.2
    (fun k _hk _hkT => hF_nonneg k) hc_mono
  have hreindex :
      (∑ t ∈ Finset.range T.1, w t * (F t - F (t + 1))) =
        ∑ k ∈ Finset.Icc 1 T.1,
          c k * (F (k - 1) - beta k * F k) := by
    rw [sum_Icc_one_eq_sum_range_succ]
    apply Finset.sum_congr rfl
    intro t _ht
    dsimp [c, beta]
    simp only [Nat.add_sub_cancel, one_mul]
  have hterminal : 0 ≤ c T.1 * beta T.1 * F T.1 := by
    exact mul_nonneg
      (mul_nonneg (hw_nonneg (T.1 - 1)) (by simp [beta]))
      (hF_nonneg T.1)
  have hweightedF :
      (∑ t ∈ Finset.range T.1, w t * (F t - F (t + 1))) ≤
        w 0 * F 0 := by
    rw [hreindex]
    have hcfirst : c 1 = w 0 := by simp [c]
    rw [hcfirst] at htelescope
    linarith
  have hFzero : F 0 = S.Δ := by
    dsimp [F, lower]
    simp only [correctedCenter_zero]
    rw [show SOptLib.expectation S.probability
          (fun _omega : Ω => averageObjective S S.initialPoint) =
        averageObjective S S.initialPoint by
      unfold SOptLib.expectation
      simp]
    simpa [averageObjective] using S.exact_initial_gap
  calc
    (∑ t ∈ Finset.range T.1,
        w t * SOptLib.expectation S.probability (fun omega =>
          averageObjective S (correctedCenter S omega alpha t) -
            averageObjective S (correctedCenter S omega alpha (t + 1)))) =
      ∑ t ∈ Finset.range T.1, w t * (F t - F (t + 1)) := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [hdrop]
    _ ≤ w 0 * F 0 := hweightedF
    _ = w 0 * S.Δ := by rw [hFzero]

/-- Weighted exact gain descent, the direct finite-horizon form of source
equation (16) before Cauchy--Schwarz and Young bounds. -/
theorem corrected_center_weighted_gain_descent
    (S : Setup n d Ω) (alpha : ℝ) (halpha : 0 < alpha)
    (T : PositiveHorizon) (w : ℕ → ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_anti : ∀ t, w (t + 1) ≤ w t) :
    alpha * (∑ t ∈ Finset.range T.1,
        w t * gain S.network t *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) ≤
      w 0 * S.Δ -
        alpha * (∑ t ∈ Finset.range T.1,
          w t * SOptLib.expectation S.probability (fun omega =>
            ⟪gradient (averageObjective S)
                (correctedCenter S omega alpha t),
              correctedDrift S omega alpha t⟫_ℝ)) +
        (S.L * alpha ^ 2 / 2) *
          (∑ t ∈ Finset.range T.1,
            w t * SOptLib.expectation S.probability (fun omega =>
              ‖(gain S.network t) •
                    gradient (averageObjective S)
                      (correctedCenter S omega alpha t) +
                  correctedDrift S omega alpha t‖ ^ 2)) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ t ∈ Finset.range T.1,
            w t * influenceEnergy S.network t) := by
  have hone (t : ℕ) :=
    corrected_center_expected_one_step_gain_descent S alpha halpha t
  have hweighted (t : ℕ) :
      w t * (alpha * gain S.network t *
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
            (correctedCenter S omega alpha t)‖ ^ 2)) ≤
      w t * (SOptLib.expectation S.probability (fun omega =>
          averageObjective S (correctedCenter S omega alpha t) -
            averageObjective S (correctedCenter S omega alpha (t + 1))) -
        alpha * SOptLib.expectation S.probability (fun omega =>
          ⟪gradient (averageObjective S) (correctedCenter S omega alpha t),
            correctedDrift S omega alpha t⟫_ℝ) +
        (S.L * alpha ^ 2 / 2) *
          SOptLib.expectation S.probability (fun omega =>
            ‖(gain S.network t) •
                  gradient (averageObjective S)
                    (correctedCenter S omega alpha t) +
                correctedDrift S omega alpha t‖ ^ 2) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          influenceEnergy S.network t) :=
    mul_le_mul_of_nonneg_left (hone t) (hw_nonneg t)
  have hsum := Finset.sum_le_sum fun t (_ht : t ∈ Finset.range T.1) =>
    hweighted t
  have hdrop := corrected_center_weighted_objective_drop_telescope
    S alpha T w hw_nonneg hw_anti
  calc
    alpha * (∑ t ∈ Finset.range T.1,
        w t * gain S.network t *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) =
      ∑ t ∈ Finset.range T.1,
        w t * (alpha * gain S.network t *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
    _ ≤ ∑ t ∈ Finset.range T.1,
      w t * (SOptLib.expectation S.probability (fun omega =>
          averageObjective S (correctedCenter S omega alpha t) -
            averageObjective S (correctedCenter S omega alpha (t + 1))) -
        alpha * SOptLib.expectation S.probability (fun omega =>
          ⟪gradient (averageObjective S) (correctedCenter S omega alpha t),
            correctedDrift S omega alpha t⟫_ℝ) +
        (S.L * alpha ^ 2 / 2) *
          SOptLib.expectation S.probability (fun omega =>
            ‖(gain S.network t) •
                  gradient (averageObjective S)
                    (correctedCenter S omega alpha t) +
                correctedDrift S omega alpha t‖ ^ 2) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          influenceEnergy S.network t) := hsum
    _ = (∑ t ∈ Finset.range T.1,
          w t * SOptLib.expectation S.probability (fun omega =>
            averageObjective S (correctedCenter S omega alpha t) -
              averageObjective S (correctedCenter S omega alpha (t + 1)))) -
        alpha * (∑ t ∈ Finset.range T.1,
          w t * SOptLib.expectation S.probability (fun omega =>
            ⟪gradient (averageObjective S)
                (correctedCenter S omega alpha t),
              correctedDrift S omega alpha t⟫_ℝ)) +
        (S.L * alpha ^ 2 / 2) *
          (∑ t ∈ Finset.range T.1,
            w t * SOptLib.expectation S.probability (fun omega =>
              ‖(gain S.network t) •
                    gradient (averageObjective S)
                      (correctedCenter S omega alpha t) +
                  correctedDrift S omega alpha t‖ ^ 2)) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ t ∈ Finset.range T.1,
            w t * influenceEnergy S.network t) := by
      simp_rw [mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      have hcrossReorder :
          (∑ t ∈ Finset.range T.1,
            w t * (alpha * SOptLib.expectation S.probability (fun omega =>
              ⟪gradient (averageObjective S)
                  (correctedCenter S omega alpha t),
                correctedDrift S omega alpha t⟫_ℝ))) =
          ∑ t ∈ Finset.range T.1,
            alpha * (w t * SOptLib.expectation S.probability (fun omega =>
              ⟪gradient (averageObjective S)
                  (correctedCenter S omega alpha t),
                correctedDrift S omega alpha t⟫_ℝ)) := by
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      have hcombinedReorder :
          (∑ t ∈ Finset.range T.1,
            w t * ((S.L * alpha ^ 2 / 2) *
              SOptLib.expectation S.probability (fun omega =>
                ‖(gain S.network t) •
                      gradient (averageObjective S)
                        (correctedCenter S omega alpha t) +
                    correctedDrift S omega alpha t‖ ^ 2))) =
          ∑ t ∈ Finset.range T.1,
            (S.L * alpha ^ 2 / 2) *
              (w t * SOptLib.expectation S.probability (fun omega =>
                ‖(gain S.network t) •
                      gradient (averageObjective S)
                        (correctedCenter S omega alpha t) +
                    correctedDrift S omega alpha t‖ ^ 2)) := by
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      have hnoiseReorder :
          (∑ t ∈ Finset.range T.1,
            w t * ((S.L * alpha ^ 2 * S.σ ^ 2 / 2) *
              influenceEnergy S.network t)) =
          ∑ t ∈ Finset.range T.1,
            (S.L * alpha ^ 2 * S.σ ^ 2 / 2) *
              (w t * influenceEnergy S.network t) := by
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      rw [hcrossReorder, hcombinedReorder, hnoiseReorder]
    _ ≤ w 0 * S.Δ -
        alpha * (∑ t ∈ Finset.range T.1,
          w t * SOptLib.expectation S.probability (fun omega =>
            ⟪gradient (averageObjective S)
                (correctedCenter S omega alpha t),
              correctedDrift S omega alpha t⟫_ℝ)) +
        (S.L * alpha ^ 2 / 2) *
          (∑ t ∈ Finset.range T.1,
            w t * SOptLib.expectation S.probability (fun omega =>
              ‖(gain S.network t) •
                    gradient (averageObjective S)
                      (correctedCenter S omega alpha t) +
                  correctedDrift S omega alpha t‖ ^ 2)) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ t ∈ Finset.range T.1,
            w t * influenceEnergy S.network t) := by
      linarith

/-- The drift cross term in source equation (16).  The block-suffix weights
factor out through their first (largest) value, while probability-space and
time-index Cauchy--Schwarz give the two global root energies. -/
theorem corrected_center_weighted_gradient_drift_cross_le
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon) (w : ℕ → ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_le_first : ∀ t, w t ≤ w 0) :
    -(∑ t ∈ Finset.range T.1,
        w t * SOptLib.expectation S.probability (fun omega =>
          ⟪gradient (averageObjective S)
              (correctedCenter S omega alpha t),
            correctedDrift S omega alpha t⟫_ℝ)) ≤
      w 0 *
        (Real.sqrt (correctedGradientEnergy S alpha T) *
          Real.sqrt (correctedDriftEnergy S alpha T)) := by
  classical
  let gEnergy : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖gradient (averageObjective S)
        (correctedCenter S omega alpha t)‖ ^ 2)
  let vEnergy : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖correctedDrift S omega alpha t‖ ^ 2)
  have hg_nonneg (t : ℕ) : 0 ≤ gEnergy t := by
    dsimp [gEnergy, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _omega => sq_nonneg _
  have hv_nonneg (t : ℕ) : 0 ≤ vEnergy t := by
    dsimp [vEnergy, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _omega => sq_nonneg _
  have hcross (t : ℕ) :
      -SOptLib.expectation S.probability (fun omega =>
          ⟪gradient (averageObjective S)
              (correctedCenter S omega alpha t),
            correctedDrift S omega alpha t⟫_ℝ) ≤
        Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t) := by
    let gradAt : Ω → Point d := fun omega =>
      gradient (averageObjective S) (correctedCenter S omega alpha t)
    let driftAt : Ω → Point d := fun omega =>
      correctedDrift S omega alpha t
    have hpayload := corrected_center_descent_payload_memLp_two S alpha t
    have hg_mem : MemLp gradAt 2 S.probability := by
      simpa [gradAt] using hpayload.2.1
    have hv_mem : MemLp driftAt 2 S.probability := by
      simpa [driftAt] using hpayload.2.2.1
    have hinner : Integrable (fun omega =>
        ⟪gradAt omega, driftAt omega⟫_ℝ) S.probability :=
      integrable_inner_of_integrable_sq_norm
        hg_mem.aestronglyMeasurable hv_mem.aestronglyMeasurable
        ((memLp_two_iff_integrable_sq_norm
          hg_mem.aestronglyMeasurable).1 hg_mem)
        ((memLp_two_iff_integrable_sq_norm
          hv_mem.aestronglyMeasurable).1 hv_mem)
    have hprod : Integrable (fun omega =>
        ‖gradAt omega‖ * ‖driftAt omega‖) S.probability := by
      simpa [Pi.mul_apply] using
        (MemLp.integrable_mul hg_mem.norm hv_mem.norm :
          Integrable ((fun omega => ‖gradAt omega‖) *
            (fun omega => ‖driftAt omega‖)) S.probability)
    have hmono :
        (∫ omega, -⟪gradAt omega, driftAt omega⟫_ℝ
            ∂S.probability) ≤
          ∫ omega, ‖gradAt omega‖ * ‖driftAt omega‖
            ∂S.probability := by
      apply MeasureTheory.integral_mono hinner.neg hprod
      intro omega
      exact (neg_le_abs _).trans
        (abs_real_inner_le_norm (gradAt omega) (driftAt omega))
    have hholder :=
      integral_norm_mul_norm_le_sqrt_integral_norm_sq_mul_sqrt_integral_norm_sq
        hg_mem hv_mem
    calc
      -SOptLib.expectation S.probability (fun omega =>
          ⟪gradient (averageObjective S)
              (correctedCenter S omega alpha t),
            correctedDrift S omega alpha t⟫_ℝ) =
          ∫ omega, -⟪gradAt omega, driftAt omega⟫_ℝ
            ∂S.probability := by
        dsimp [SOptLib.expectation, gradAt, driftAt]
        rw [MeasureTheory.integral_neg]
      _ ≤ ∫ omega, ‖gradAt omega‖ * ‖driftAt omega‖
            ∂S.probability := hmono
      _ ≤ Real.sqrt (∫ omega, ‖gradAt omega‖ ^ 2 ∂S.probability) *
          Real.sqrt (∫ omega, ‖driftAt omega‖ ^ 2 ∂S.probability) := hholder
      _ = Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t) := by
        rfl
  have hterm (t : ℕ) :
      w t *
          (-SOptLib.expectation S.probability (fun omega =>
            ⟪gradient (averageObjective S)
                (correctedCenter S omega alpha t),
              correctedDrift S omega alpha t⟫_ℝ)) ≤
        w 0 * (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) := by
    calc
      w t *
          (-SOptLib.expectation S.probability (fun omega =>
            ⟪gradient (averageObjective S)
                (correctedCenter S omega alpha t),
              correctedDrift S omega alpha t⟫_ℝ)) ≤
        w t * (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) :=
          mul_le_mul_of_nonneg_left (hcross t) (hw_nonneg t)
      _ ≤ w 0 * (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) :=
        mul_le_mul_of_nonneg_right (hw_le_first t)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsum := Finset.sum_le_sum fun t
      (_ht : t ∈ Finset.range T.1) => hterm t
  have hcauchy := Real.sum_sqrt_mul_sqrt_le (Finset.range T.1)
    hg_nonneg hv_nonneg
  calc
    -(∑ t ∈ Finset.range T.1,
        w t * SOptLib.expectation S.probability (fun omega =>
          ⟪gradient (averageObjective S)
              (correctedCenter S omega alpha t),
            correctedDrift S omega alpha t⟫_ℝ)) =
      ∑ t ∈ Finset.range T.1,
        w t *
          (-SOptLib.expectation S.probability (fun omega =>
            ⟪gradient (averageObjective S)
                (correctedCenter S omega alpha t),
              correctedDrift S omega alpha t⟫_ℝ)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
    _ ≤ ∑ t ∈ Finset.range T.1,
        w 0 * (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) := hsum
    _ = w 0 * (∑ t ∈ Finset.range T.1,
        Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) := by
      rw [Finset.mul_sum]
    _ ≤ w 0 *
        (Real.sqrt (∑ t ∈ Finset.range T.1, gEnergy t) *
          Real.sqrt (∑ t ∈ Finset.range T.1, vEnergy t)) :=
      mul_le_mul_of_nonneg_left hcauchy (hw_nonneg 0)
    _ = w 0 *
        (Real.sqrt (correctedGradientEnergy S alpha T) *
          Real.sqrt (correctedDriftEnergy S alpha T)) := by
      rfl

/-- The deterministic combined direction in source equation (16) has the
global `L²` triangle bound after suffix weighting. -/
theorem corrected_center_weighted_combined_energy_le
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon) (w : ℕ → ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_le_first : ∀ t, w t ≤ w 0) :
    (∑ t ∈ Finset.range T.1,
        w t * SOptLib.expectation S.probability (fun omega =>
          ‖(gain S.network t) •
                gradient (averageObjective S)
                  (correctedCenter S omega alpha t) +
              correctedDrift S omega alpha t‖ ^ 2)) ≤
      w 0 * ((n : ℝ) *
          Real.sqrt (correctedGradientEnergy S alpha T) +
        Real.sqrt (correctedDriftEnergy S alpha T)) ^ 2 := by
  classical
  let gEnergy : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖gradient (averageObjective S)
        (correctedCenter S omega alpha t)‖ ^ 2)
  let vEnergy : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖correctedDrift S omega alpha t‖ ^ 2)
  have hn : 0 < (n : ℝ) := by exact_mod_cast S.hn
  have hmu : 0 < mixingMinorization S.network := by
    unfold mixingMinorization
    split_ifs
    · exact pow_pos ((lt_min_iff).2 ⟨S.network.ha, by norm_num⟩) _
    · norm_num
  have hg_nonneg (t : ℕ) : 0 ≤ gEnergy t := by
    dsimp [gEnergy, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _omega => sq_nonneg _
  have hv_nonneg (t : ℕ) : 0 ≤ vEnergy t := by
    dsimp [vEnergy, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _omega => sq_nonneg _
  have hone (t : ℕ) :
      SOptLib.expectation S.probability (fun omega =>
          ‖(gain S.network t) •
                gradient (averageObjective S)
                  (correctedCenter S omega alpha t) +
              correctedDrift S omega alpha t‖ ^ 2) ≤
        (n : ℝ) ^ 2 * gEnergy t +
          2 * (n : ℝ) *
            (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) +
          vEnergy t := by
    let k := gain S.network t
    let gradAt : Ω → Point d := fun omega =>
      gradient (averageObjective S) (correctedCenter S omega alpha t)
    let driftAt : Ω → Point d := fun omega =>
      correctedDrift S omega alpha t
    have hk_nonneg : 0 ≤ k := by
      have hgain := gain_ge_n_mul_mixingMinorization S.network t
      have hprod : 0 < (n : ℝ) * mixingMinorization S.network :=
        mul_pos hn hmu
      exact hprod.le.trans hgain
    have hk_le : k ≤ (n : ℝ) := by
      dsimp [k]
      exact gain_le_n S.network t
    have hpayload := corrected_center_descent_payload_memLp_two S alpha t
    have hg_mem : MemLp gradAt 2 S.probability := by
      simpa [gradAt] using hpayload.2.1
    have hv_mem : MemLp driftAt 2 S.probability := by
      simpa [driftAt] using hpayload.2.2.1
    have hcombined_mem : MemLp (fun omega =>
        k • gradAt omega + driftAt omega) 2 S.probability := by
      simpa [k, gradAt, driftAt] using hpayload.2.2.2
    have hg_sq : Integrable (fun omega => ‖gradAt omega‖ ^ 2)
        S.probability :=
      (memLp_two_iff_integrable_sq_norm
        hg_mem.aestronglyMeasurable).1 hg_mem
    have hv_sq : Integrable (fun omega => ‖driftAt omega‖ ^ 2)
        S.probability :=
      (memLp_two_iff_integrable_sq_norm
        hv_mem.aestronglyMeasurable).1 hv_mem
    have hcombined_sq : Integrable (fun omega =>
        ‖k • gradAt omega + driftAt omega‖ ^ 2) S.probability :=
      (memLp_two_iff_integrable_sq_norm
        hcombined_mem.aestronglyMeasurable).1 hcombined_mem
    have hprod_int : Integrable (fun omega =>
        ‖gradAt omega‖ * ‖driftAt omega‖) S.probability := by
      simpa [Pi.mul_apply] using
        (MemLp.integrable_mul hg_mem.norm hv_mem.norm :
          Integrable ((fun omega => ‖gradAt omega‖) *
            (fun omega => ‖driftAt omega‖)) S.probability)
    have hrhs_int : Integrable (fun omega =>
        k ^ 2 * ‖gradAt omega‖ ^ 2 +
          2 * k * (‖gradAt omega‖ * ‖driftAt omega‖) +
          ‖driftAt omega‖ ^ 2) S.probability :=
      ((hg_sq.const_mul _).add (hprod_int.const_mul _)).add hv_sq
    have hpoint (omega : Ω) :
        ‖k • gradAt omega + driftAt omega‖ ^ 2 ≤
          k ^ 2 * ‖gradAt omega‖ ^ 2 +
            2 * k * (‖gradAt omega‖ * ‖driftAt omega‖) +
            ‖driftAt omega‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hk_nonneg, mul_pow, inner_smul_left]
      simp only [starRingEnd_apply, star_trivial]
      have hinner := real_inner_le_norm (gradAt omega) (driftAt omega)
      nlinarith
    have hmono := MeasureTheory.integral_mono hcombined_sq hrhs_int hpoint
    have hrhs_expand :
        (∫ omega,
            k ^ 2 * ‖gradAt omega‖ ^ 2 +
              2 * k * (‖gradAt omega‖ * ‖driftAt omega‖) +
              ‖driftAt omega‖ ^ 2 ∂S.probability) =
          k ^ 2 * gEnergy t +
            2 * k *
              (∫ omega, ‖gradAt omega‖ * ‖driftAt omega‖
                ∂S.probability) +
            vEnergy t := by
      have hall := MeasureTheory.integral_add
        ((hg_sq.const_mul (k ^ 2)).add (hprod_int.const_mul (2 * k))) hv_sq
      have hfirst := MeasureTheory.integral_add
        (hg_sq.const_mul (k ^ 2)) (hprod_int.const_mul (2 * k))
      rw [show (∫ omega,
            k ^ 2 * ‖gradAt omega‖ ^ 2 +
              2 * k * (‖gradAt omega‖ * ‖driftAt omega‖) +
              ‖driftAt omega‖ ^ 2 ∂S.probability) =
            (∫ omega,
              k ^ 2 * ‖gradAt omega‖ ^ 2 +
                2 * k * (‖gradAt omega‖ * ‖driftAt omega‖)
                ∂S.probability) +
              ∫ omega, ‖driftAt omega‖ ^ 2 ∂S.probability by
          simpa only [Pi.add_apply] using hall]
      rw [show (∫ omega,
            k ^ 2 * ‖gradAt omega‖ ^ 2 +
              2 * k * (‖gradAt omega‖ * ‖driftAt omega‖)
              ∂S.probability) =
            (∫ omega, k ^ 2 * ‖gradAt omega‖ ^ 2 ∂S.probability) +
              ∫ omega, 2 * k *
                (‖gradAt omega‖ * ‖driftAt omega‖) ∂S.probability by
          simpa only [Pi.add_apply] using hfirst]
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
      rfl
    have hholder :=
      integral_norm_mul_norm_le_sqrt_integral_norm_sq_mul_sqrt_integral_norm_sq
        hg_mem hv_mem
    have hraw :
        SOptLib.expectation S.probability (fun omega =>
            ‖k • gradAt omega + driftAt omega‖ ^ 2) ≤
          k ^ 2 * gEnergy t +
            2 * k * (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) +
            vEnergy t := by
      unfold SOptLib.expectation
      rw [hrhs_expand] at hmono
      have hcoef : 0 ≤ 2 * k := mul_nonneg (by norm_num) hk_nonneg
      have hscale := mul_le_mul_of_nonneg_left hholder hcoef
      have hscale' :
          2 * k *
              (∫ omega, ‖gradAt omega‖ * ‖driftAt omega‖
                ∂S.probability) ≤
            2 * k * (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) := by
        simpa [gEnergy, vEnergy, gradAt, driftAt,
          SOptLib.expectation] using hscale
      nlinarith [hmono, hscale']
    have hroot_nonneg :
        0 ≤ Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq : k ^ 2 * gEnergy t ≤ (n : ℝ) ^ 2 * gEnergy t := by
      have hk_sq : k ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hk_sq (hg_nonneg t)
    have hroot :
        2 * k * (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) ≤
          2 * (n : ℝ) *
            (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk_le (by norm_num)) hroot_nonneg
    simpa [k, gradAt, driftAt] using
      (hraw.trans (add_le_add (add_le_add hsq hroot) le_rfl))
  have hterm (t : ℕ) :
      w t * SOptLib.expectation S.probability (fun omega =>
          ‖(gain S.network t) •
                gradient (averageObjective S)
                  (correctedCenter S omega alpha t) +
              correctedDrift S omega alpha t‖ ^ 2) ≤
        w 0 * ((n : ℝ) ^ 2 * gEnergy t +
          2 * (n : ℝ) *
            (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) +
          vEnergy t) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := hn.le
    have hmiddle_nonneg : 0 ≤
        2 * (n : ℝ) *
          (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) :=
      mul_nonneg (mul_nonneg (by norm_num) hn_nonneg)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hrhs_nonneg' : 0 ≤
        (n : ℝ) ^ 2 * gEnergy t +
          2 * (n : ℝ) *
            (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) +
          vEnergy t :=
      add_nonneg (add_nonneg
        (mul_nonneg (sq_nonneg _) (hg_nonneg t)) hmiddle_nonneg)
        (hv_nonneg t)
    calc
      _ ≤ w t * ((n : ℝ) ^ 2 * gEnergy t +
          2 * (n : ℝ) *
            (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) +
          vEnergy t) := mul_le_mul_of_nonneg_left (hone t) (hw_nonneg t)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hw_le_first t) hrhs_nonneg'
  have hsum := Finset.sum_le_sum fun t
    (_ht : t ∈ Finset.range T.1) => hterm t
  have hcauchy := Real.sum_sqrt_mul_sqrt_le (Finset.range T.1)
    hg_nonneg hv_nonneg
  have hweightedCauchy := mul_le_mul_of_nonneg_left hcauchy
    (mul_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)) (hw_nonneg 0))
  have hG_nonneg : 0 ≤ ∑ t ∈ Finset.range T.1, gEnergy t :=
    Finset.sum_nonneg fun t _ht => hg_nonneg t
  have hV_nonneg : 0 ≤ ∑ t ∈ Finset.range T.1, vEnergy t :=
    Finset.sum_nonneg fun t _ht => hv_nonneg t
  calc
    _ ≤ ∑ t ∈ Finset.range T.1,
        w 0 * ((n : ℝ) ^ 2 * gEnergy t +
          2 * (n : ℝ) *
            (Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) +
          vEnergy t) := hsum
    _ = w 0 * ((n : ℝ) ^ 2 *
          (∑ t ∈ Finset.range T.1, gEnergy t) +
        2 * (n : ℝ) *
          (∑ t ∈ Finset.range T.1,
            Real.sqrt (gEnergy t) * Real.sqrt (vEnergy t)) +
        (∑ t ∈ Finset.range T.1, vEnergy t)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ ≤ w 0 * ((n : ℝ) ^ 2 *
          (∑ t ∈ Finset.range T.1, gEnergy t) +
        2 * (n : ℝ) *
          (Real.sqrt (∑ t ∈ Finset.range T.1, gEnergy t) *
            Real.sqrt (∑ t ∈ Finset.range T.1, vEnergy t)) +
        (∑ t ∈ Finset.range T.1, vEnergy t)) := by
      nlinarith
    _ = w 0 * ((n : ℝ) *
          Real.sqrt (correctedGradientEnergy S alpha T) +
        Real.sqrt (correctedDriftEnergy S alpha T)) ^ 2 := by
      dsimp [correctedGradientEnergy, correctedDriftEnergy,
        gEnergy, vEnergy]
      rw [add_sq, mul_pow, Real.sq_sqrt hG_nonneg,
        Real.sq_sqrt hV_nonneg]
      ring

/-- Source equation (16), before substituting the block/window estimates.
Every analytic term is now expressed through the global corrected-gradient,
drift, and influence energies; only the finite gain-block data remain. -/
theorem corrected_center_suffix_weighted_gain_descent
    (S : Setup n d Ω) (alpha : ℝ) (halpha : 0 < alpha)
    (T : PositiveHorizon) (w : ℕ → ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_anti : ∀ t, w (t + 1) ≤ w t)
    (hw_le_first : ∀ t, w t ≤ w 0) :
    alpha * (∑ t ∈ Finset.range T.1,
        w t * gain S.network t *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) ≤
      w 0 * S.Δ +
        alpha * w 0 *
          (Real.sqrt (correctedGradientEnergy S alpha T) *
            Real.sqrt (correctedDriftEnergy S alpha T)) +
        (S.L * alpha ^ 2 / 2) * w 0 *
          ((n : ℝ) * Real.sqrt (correctedGradientEnergy S alpha T) +
            Real.sqrt (correctedDriftEnergy S alpha T)) ^ 2 +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ t ∈ Finset.range T.1,
            w t * influenceEnergy S.network t) := by
  have hdescent := corrected_center_weighted_gain_descent
    S alpha halpha T w hw_nonneg hw_anti
  have hcross := corrected_center_weighted_gradient_drift_cross_le
    S alpha T w hw_nonneg hw_le_first
  have hcombined := corrected_center_weighted_combined_energy_le
    S alpha T w hw_nonneg hw_le_first
  have hcross_scaled := mul_le_mul_of_nonneg_left hcross halpha.le
  have hcombined_coef : 0 ≤ S.L * alpha ^ 2 / 2 :=
    div_nonneg (mul_nonneg S.hL.le (sq_nonneg alpha)) (by norm_num)
  have hcombined_scaled :=
    mul_le_mul_of_nonneg_left hcombined hcombined_coef
  nlinarith

/-- Corrected-center descent with the block-constant suffix weights of source
equation (16).  This is the analytic consumer of the weighted objective-drop
telescope; the remaining drift and stochastic terms retain their exact
weighted finite-sum form for the block estimates. -/
theorem corrected_center_weighted_expected_descent
    (S : Setup n d Ω) (alpha : ℝ) (halpha : 0 < alpha)
    (hsCap : dimensionlessStepsize S.L alpha ≤
      correctedCenterStepCap S.network)
    (T : PositiveHorizon) (w : ℕ → ℝ)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_anti : ∀ t, w (t + 1) ≤ w t) :
    alpha * gainFloor S.network / 2 *
        (∑ t ∈ Finset.range T.1,
          w t * SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) ≤
      w 0 * S.Δ +
        2 * alpha / gainFloor S.network *
          (∑ t ∈ Finset.range T.1,
            w t * SOptLib.expectation S.probability (fun omega =>
              ‖correctedDrift S omega alpha t‖ ^ 2)) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ t ∈ Finset.range T.1,
            w t * influenceEnergy S.network t) := by
  have hone (t : ℕ) :=
    corrected_center_expected_one_step_descent S alpha halpha hsCap t
  have hweighted (t : ℕ) :
      w t * (alpha * gainFloor S.network / 2 *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) ≤
        w t * (SOptLib.expectation S.probability (fun omega =>
            averageObjective S (correctedCenter S omega alpha t) -
              averageObjective S (correctedCenter S omega alpha (t + 1))) +
          2 * alpha / gainFloor S.network *
            SOptLib.expectation S.probability (fun omega =>
              ‖correctedDrift S omega alpha t‖ ^ 2) +
          S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
            influenceEnergy S.network t) :=
    mul_le_mul_of_nonneg_left (hone t) (hw_nonneg t)
  have hsum := Finset.sum_le_sum fun t (_ht : t ∈ Finset.range T.1) =>
    hweighted t
  have hdrop := corrected_center_weighted_objective_drop_telescope
    S alpha T w hw_nonneg hw_anti
  calc
    alpha * gainFloor S.network / 2 *
        (∑ t ∈ Finset.range T.1,
          w t * SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) =
      ∑ t ∈ Finset.range T.1,
        w t * (alpha * gainFloor S.network / 2 *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
    _ ≤ ∑ t ∈ Finset.range T.1,
        w t * (SOptLib.expectation S.probability (fun omega =>
            averageObjective S (correctedCenter S omega alpha t) -
              averageObjective S (correctedCenter S omega alpha (t + 1))) +
          2 * alpha / gainFloor S.network *
            SOptLib.expectation S.probability (fun omega =>
              ‖correctedDrift S omega alpha t‖ ^ 2) +
          S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
            influenceEnergy S.network t) := hsum
    _ = (∑ t ∈ Finset.range T.1,
          w t * SOptLib.expectation S.probability (fun omega =>
            averageObjective S (correctedCenter S omega alpha t) -
              averageObjective S (correctedCenter S omega alpha (t + 1)))) +
        2 * alpha / gainFloor S.network *
          (∑ t ∈ Finset.range T.1,
            w t * SOptLib.expectation S.probability (fun omega =>
              ‖correctedDrift S omega alpha t‖ ^ 2)) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ t ∈ Finset.range T.1,
            w t * influenceEnergy S.network t) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      · apply Finset.sum_congr rfl
        intro t _ht
        ring
    _ ≤ w 0 * S.Δ +
        2 * alpha / gainFloor S.network *
          (∑ t ∈ Finset.range T.1,
            w t * SOptLib.expectation S.probability (fun omega =>
              ‖correctedDrift S omega alpha t‖ ^ 2)) +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ t ∈ Finset.range T.1,
            w t * influenceEnergy S.network t) := by
      linarith

/-- Fixed-class specialization of the equation-(17) output transfer.  The
remaining source work is to improve the corrected-gradient term by the
gain-block argument of equations (14)--(18). -/
theorem fixed_instance_cost_le_corrected_energy_expression
    (N : NetworkSetup n) (L Δ σ H : ℝ) (hL : 0 < L)
    (I : fixedInstanceClass N L Δ σ H)
    (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n)
    (hsCap : s.1 ≤ correctedCenterStepCap N) :
    let G := @correctedGradientEnergy n I.1.d I.1.Ω
      I.1.measurableSpace I.1.setup (s.1 / L) T
    FiniteInstance.cost I.1 (s.1 / L) T ≤
      (T.1 : ℝ)⁻¹ *
        (2 * G +
          2 * s.1 ^ 2 *
            (controlJB N * G +
              controlJH N * n * H ^ 2 +
              controlJN N * σ ^ 2 * T.1)) := by
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  dsimp only
  let S := I.1.setup
  have hnetwork : S.network = N := by
    simpa [S, FiniteInstance.network] using I.2.1
  have hLip : S.L = L := by
    simpa [S, FiniteInstance.lipschitz] using I.2.2.1
  have hnoise : S.σ = σ := by
    simpa [S, FiniteInstance.noiseScale] using I.2.2.2.2.1
  have hheterogeneity : S.H = H := by
    simpa [S, FiniteInstance.heterogeneityScale] using I.2.2.2.2.2
  have hfinite : InFiniteHeterogeneityLayer S := by
    simpa [S] using I.1.finite_layer
  have halpha : 0 < s.1 / L := div_pos s.2.1 hL
  have hdimensionless : dimensionlessStepsize S.L (s.1 / L) = s.1 := by
    rw [hLip]
    exact dimensionlessStepsize_div L s.1 hL
  have hcontrol := corrected_center_uniform_control S hfinite (s.1 / L)
    halpha (by rw [hdimensionless, hnetwork]; exact hsCap) T
  rcases hcontrol with
    ⟨_, _, _, _, _, _, _, _, _, hJ, _⟩
  have hJ' :
      correctedCenterOffsetEnergy S (s.1 / L) T ≤
        (s.1 / L) ^ 2 *
          (controlJB N * correctedGradientEnergy S (s.1 / L) T +
            controlJH N * n * H ^ 2 + controlJN N * σ ^ 2 * T.1) := by
    rw [hnetwork, hheterogeneity, hnoise] at hJ
    exact hJ
  have htransfer := stationarityError_le_corrected_energy S (s.1 / L) T
  change stationarityError S (s.1 / L) T ≤ _
  calc
    stationarityError S (s.1 / L) T ≤
        (T.1 : ℝ)⁻¹ *
          (2 * correctedGradientEnergy S (s.1 / L) T +
            2 * S.L ^ 2 * correctedCenterOffsetEnergy S (s.1 / L) T) :=
      htransfer
    _ ≤ (T.1 : ℝ)⁻¹ *
          (2 * correctedGradientEnergy S (s.1 / L) T +
            2 * S.L ^ 2 * ((s.1 / L) ^ 2 *
              (controlJB N * correctedGradientEnergy S (s.1 / L) T +
                controlJH N * n * H ^ 2 +
                controlJN N * σ ^ 2 * T.1))) := by
      gcongr
    _ = _ := by
      rw [hLip]
      field_simp [ne_of_gt hL]
      ring

/-- The backward partition carries two distinct weights.  The source weight is
the suffix maximum of the gain-normalized block lengths; it has the sharp
`1 / gainFloor` bound needed by the Young inequalities.  The coarser
`64 * s * M` weight is used only to invoke the causal-window overcount. -/
private theorem backward_gain_partition_source_weight_certificate
    (N : NetworkSetup n) (T : PositiveHorizon)
    (s : AdmissibleDimensionlessStepsize n)
    (htotal : epsilon / 2 ≤
      s.1 * ∑ t ∈ Finset.range T.1, gain N t) :
    ∃ blockCount : ℕ, ∃ endpoint : ℕ → ℕ, ∃ w : ℕ → ℝ,
      let blocks : ℕ → Finset ℕ := fun j =>
        Finset.Ico (endpoint j) (endpoint (j + 1))
      let K : ℕ → ℝ := fun j => ∑ t ∈ blocks j, gain N t
      let M : ℕ → ℕ := fun j =>
        (Finset.Ico j blockCount).sup fun l => (blocks l).card
      0 < blockCount ∧ endpoint 0 = 0 ∧ endpoint blockCount = T.1 ∧
      (∀ j < blockCount, endpoint j < endpoint (j + 1)) ∧
      (∀ j < blockCount,
        1 / (64 * s.1) ≤ K j ∧ K j ≤ 1 / (16 * s.1)) ∧
      (∀ f : ℕ → ℝ,
        (∑ j ∈ Finset.range blockCount, ∑ t ∈ blocks j, f t) =
          ∑ t ∈ Finset.range T.1, f t) ∧
      (∀ j, 0 ≤ w j) ∧ (∀ j, w (j + 1) ≤ w j) ∧
      w 0 ≤ 1 / gainFloor N ∧
      (∀ j < blockCount,
        ((blocks j).card : ℝ) / K j ≤ w j ∧
          w j ≤ 64 * s.1 * (M j : ℝ)) ∧
      M 0 ≤ windowLength N T.1 0 s.1 ∧
      (∑ j ∈ Finset.range blockCount,
          w j * ∑ t ∈ blocks j, influenceEnergy N t) ≤
        64 * s.1 *
          (windowInfluenceSum N T.1 s.1 +
            influenceRowBound N ^ 2 *
              (windowLength N T.1 0 s.1 : ℝ) ^ 2) := by
  classical
  obtain ⟨blockCount, endpoint, hcount, he0, heT, hestrict, hebudget,
      hpartition, _homega_nonneg, _homega_anti, _hcard_weight, hover⟩ :=
    backward_gain_partition_overcount_certificate N T s htotal
  let blocks : ℕ → Finset ℕ := fun j =>
    Finset.Ico (endpoint j) (endpoint (j + 1))
  let K : ℕ → ℝ := fun j => ∑ t ∈ blocks j, gain N t
  let M : ℕ → ℕ := fun j =>
    (Finset.Ico j blockCount).sup fun l => (blocks l).card
  let ratio : ℕ → ℝ := fun j => ((blocks j).card : ℝ) / K j
  have hsuffix_nonempty (j : ℕ) (hj : j < blockCount) :
      ((Finset.Ico j blockCount).image ratio).Nonempty := by
    exact Finset.image_nonempty.mpr
      ⟨j, Finset.mem_Ico.mpr ⟨le_rfl, hj⟩⟩
  let w : ℕ → ℝ := fun j =>
    if hj : j < blockCount then
      ((Finset.Ico j blockCount).image ratio).max'
        (hsuffix_nonempty j hj)
    else 0
  have hs : 0 < s.1 := s.2.1
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hKpos (j : ℕ) (hj : j < blockCount) : 0 < K j := by
    have hlo := (hebudget j hj).1
    have hinv : 0 < 1 / (64 * s.1) := one_div_pos.mpr (mul_pos (by norm_num) hs)
    dsimp [K, blocks]
    dsimp [blocks, K] at hlo
    linarith
  have hratio_nonneg (j : ℕ) (hj : j < blockCount) : 0 ≤ ratio j := by
    exact div_nonneg (Nat.cast_nonneg _) (hKpos j hj).le
  have hratio_le_floor (j : ℕ) (hj : j < blockCount) :
      ratio j ≤ 1 / gainFloor N := by
    have hgainSum : gainFloor N * ((blocks j).card : ℝ) ≤ K j := by
      calc
        gainFloor N * ((blocks j).card : ℝ) =
            ∑ t ∈ blocks j, gainFloor N := by
          simp
          ring
        _ ≤ ∑ t ∈ blocks j, gain N t :=
          Finset.sum_le_sum fun t _ht => gainFloor_le_gain N t
        _ = K j := rfl
    apply (div_le_div_iff₀ (hKpos j hj) hg).2
    simpa [ratio, mul_comm] using hgainSum
  have hcard_le_M (j : ℕ) (hj : j < blockCount) :
      (blocks j).card ≤ M j := by
    dsimp [M]
    exact Finset.le_sup (f := fun l => (blocks l).card)
      (Finset.mem_Ico.mpr ⟨le_rfl, hj⟩)
  have hratio_le_majorant (j : ℕ) (hj : j < blockCount) :
      ratio j ≤ 64 * s.1 * (M j : ℝ) := by
    have hlo := (hebudget j hj).1
    have hcardM : ((blocks j).card : ℝ) ≤ M j := by
      exact_mod_cast hcard_le_M j hj
    have hK := hKpos j hj
    dsimp [K] at hlo hK
    dsimp [ratio, K]
    apply (div_le_iff₀ hK).2
    field_simp [ne_of_gt hs] at hlo
    have hMnonneg : 0 ≤ (M j : ℝ) := Nat.cast_nonneg _
    have hcardnonneg : 0 ≤ ((blocks j).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hw_nonneg : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hj : j < blockCount
    · rw [show w j = ((Finset.Ico j blockCount).image ratio).max'
          (hsuffix_nonempty j hj) by simp [w, hj]]
      obtain ⟨l, hl, hratio⟩ := Finset.mem_image.mp
        (Finset.max'_mem ((Finset.Ico j blockCount).image ratio)
          (hsuffix_nonempty j hj))
      rw [← hratio]
      exact hratio_nonneg l (Finset.mem_Ico.mp hl).2
    · simp [w, hj]
  have hw_anti : ∀ j, w (j + 1) ≤ w j := by
    intro j
    by_cases hj1 : j + 1 < blockCount
    · have hj : j < blockCount := by omega
      rw [show w (j + 1) =
          ((Finset.Ico (j + 1) blockCount).image ratio).max'
            (hsuffix_nonempty (j + 1) hj1) by simp [w, hj1]]
      rw [show w j = ((Finset.Ico j blockCount).image ratio).max'
          (hsuffix_nonempty j hj) by simp [w, hj]]
      apply Finset.max'_le
      intro y hy
      apply Finset.le_max'
      exact Finset.mem_of_subset
        (Finset.image_subset_image (by
          intro l hl
          simp only [Finset.mem_Ico] at hl ⊢
          omega)) hy
    · have hwj1 : w (j + 1) = 0 := by simp [w, hj1]
      rw [hwj1]
      exact hw_nonneg j
  have hw0 : w 0 ≤ 1 / gainFloor N := by
    have h0 : 0 < blockCount := hcount
    rw [show w 0 = ((Finset.Ico 0 blockCount).image ratio).max'
        (hsuffix_nonempty 0 h0) by simp [w, h0]]
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨l, hl, rfl⟩
    exact hratio_le_floor l (Finset.mem_Ico.mp hl).2
  have hratio_le_w : ∀ j < blockCount, ratio j ≤ w j := by
    intro j hj
    rw [show w j = ((Finset.Ico j blockCount).image ratio).max'
        (hsuffix_nonempty j hj) by simp [w, hj]]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr
      ⟨j, Finset.mem_Ico.mpr ⟨le_rfl, hj⟩, rfl⟩)
  have hw_le_majorant : ∀ j < blockCount,
      w j ≤ 64 * s.1 * (M j : ℝ) := by
    intro j hj
    rw [show w j = ((Finset.Ico j blockCount).image ratio).max'
        (hsuffix_nonempty j hj) by simp [w, hj]]
    apply Finset.max'_le
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨l, hl, rfl⟩
    have hlj := Finset.mem_Ico.mp hl
    exact (hratio_le_majorant l hlj.2).trans
      (mul_le_mul_of_nonneg_left
        (by
          exact_mod_cast (Finset.sup_mono
            (show Finset.Ico l blockCount ⊆ Finset.Ico j blockCount by
              intro q hq
              simp only [Finset.mem_Ico] at hq ⊢
              omega) : M l ≤ M j))
        (mul_nonneg (by norm_num) hs.le))
  have hendpoint_mono : ∀ {a b : ℕ}, a ≤ b → b ≤ blockCount →
      endpoint a ≤ endpoint b := by
    intro a b hab hb
    induction b with
    | zero =>
      have ha0 : a = 0 := by omega
      subst a
      exact le_rfl
    | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact (ih hab' (by omega)).trans (hestrict b (by omega)).le
  have hMzero : M 0 ≤ windowLength N T.1 0 s.1 := by
    dsimp [M]
    apply Finset.sup_le
    intro l hl
    have hlbounds : 0 ≤ l ∧ l < blockCount := by
      simpa only [Finset.mem_Ico] using hl
    have hend : endpoint (l + 1) ≤ T.1 := by
      rw [← heT]
      exact hendpoint_mono (by omega) le_rfl
    have hbudget := (hebudget l hlbounds.2).2
    have hbudget' :
        s.1 * ∑ r ∈ Finset.Ico (endpoint l) (endpoint (l + 1)), gain N r ≤
          epsilon := by
      calc
        s.1 * ∑ r ∈ Finset.Ico (endpoint l) (endpoint (l + 1)), gain N r ≤
            s.1 * (1 / (16 * s.1)) :=
          mul_le_mul_of_nonneg_left hbudget hs.le
        _ = epsilon := by
          rw [show epsilon = (1 : ℝ) / 16 by norm_num [epsilon]]
          field_simp [ne_of_gt hs]
    have hlen := interval_length_le_windowLength N T.1 0
      (endpoint l) (endpoint (l + 1)) s.1 T.2 (Nat.zero_le _)
      (hestrict l hlbounds.2) hend hbudget'
    simpa [blocks, Nat.card_Ico] using hlen
  have hwInfluence :
      (∑ j ∈ Finset.range blockCount,
          w j * ∑ t ∈ blocks j, influenceEnergy N t) ≤
        ∑ j ∈ Finset.range blockCount,
          (64 * s.1 * (M j : ℝ)) *
            ∑ t ∈ blocks j, influenceEnergy N t := by
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_right
      (hw_le_majorant j (Finset.mem_range.mp hj))
    exact Finset.sum_nonneg fun t _ht => by
      unfold influenceEnergy
      exact Finset.sum_nonneg fun i _hi => sq_nonneg _
  refine ⟨blockCount, endpoint, w, ?_⟩
  dsimp only
  refine ⟨hcount, he0, heT, hestrict, hebudget, hpartition,
    hw_nonneg, hw_anti, hw0, ?_, hMzero, ?_⟩
  · intro j hj
    exact ⟨hratio_le_w j hj, hw_le_majorant j hj⟩
  · exact hwInfluence.trans hover

/-- Summing source equation (15) over the backward partition, with the sharp
ratio-suffix weight.  The gain floor controls the drift coefficient, while the
block gain budget controls the noise coefficient without replacing `w` by its
coarse causal majorant. -/
private theorem corrected_center_partition_gradient_energy_le
    (N : NetworkSetup n) (S : Setup n d Ω) (hnetwork : S.network = N)
    (alpha : ℝ) (halpha : 0 < alpha) (T : PositiveHorizon)
    (blockCount : ℕ) (endpoint : ℕ → ℕ) (w : ℕ → ℝ)
    (hestrict : ∀ j < blockCount, endpoint j < endpoint (j + 1))
    (hebudget : ∀ j < blockCount,
      1 / (64 * (S.L * alpha)) ≤
          ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t ∧
        (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t) ≤
          1 / (16 * (S.L * alpha)))
    (hpartition : ∀ f : ℕ → ℝ,
      (∑ j ∈ Finset.range blockCount,
          ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), f t) =
        ∑ t ∈ Finset.range T.1, f t)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hratio : ∀ j < blockCount,
      ((Finset.Ico (endpoint j) (endpoint (j + 1))).card : ℝ) /
          (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t) ≤ w j) :
    correctedGradientEnergy S alpha T ≤
      5 * ∑ j ∈ Finset.range blockCount,
        w j * (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
          gain N t * SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) +
      18 * epsilon ^ 2 / gainFloor N ^ 2 *
        correctedDriftEnergy S alpha T +
      18 * epsilon * (S.L * alpha) * S.σ ^ 2 *
        (∑ j ∈ Finset.range blockCount,
          w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
            influenceEnergy N t) := by
  classical
  let blocks : ℕ → Finset ℕ := fun j =>
    Finset.Ico (endpoint j) (endpoint (j + 1))
  let K : ℕ → ℝ := fun j => ∑ t ∈ blocks j, gain N t
  let e : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2)
  let v : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖correctedDrift S omega alpha t‖ ^ 2)
  let q : ℕ → ℝ := fun t => influenceEnergy N t
  let sdim : ℝ := S.L * alpha
  have hs : 0 < sdim := mul_pos S.hL halpha
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hv_nonneg (t : ℕ) : 0 ≤ v t := by
    dsimp [v, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hq_nonneg (t : ℕ) : 0 ≤ q t := by
    dsimp [q, influenceEnergy]
    exact Finset.sum_nonneg fun i _hi => sq_nonneg _
  have hblock : ∀ j < blockCount,
      ∑ t ∈ blocks j, e t ≤
        5 * w j * (∑ t ∈ blocks j, gain N t * e t) +
        18 * epsilon ^ 2 / gainFloor N ^ 2 * (∑ t ∈ blocks j, v t) +
        18 * epsilon * sdim * S.σ ^ 2 *
          (w j * ∑ t ∈ blocks j, q t) := by
    intro j hj
    have hKpos : 0 < K j := by
      have hlo := (hebudget j hj).1
      have hinv : 0 < 1 / (64 * sdim) :=
        one_div_pos.mpr (mul_pos (by norm_num) hs)
      dsimp [K, blocks, sdim] at hlo ⊢
      linarith
    have hsK : sdim * K j ≤ epsilon := by
      have hupper := (hebudget j hj).2
      calc
        sdim * K j ≤ sdim * (1 / (16 * sdim)) :=
          mul_le_mul_of_nonneg_left (by simpa [K, blocks, sdim] using hupper) hs.le
        _ = epsilon := by
          rw [show epsilon = (1 : ℝ) / 16 by norm_num [epsilon]]
          field_simp [ne_of_gt hs]
    have hgainCard : gainFloor N * ((blocks j).card : ℝ) ≤ K j := by
      calc
        gainFloor N * ((blocks j).card : ℝ) =
            ∑ t ∈ blocks j, gainFloor N := by simp; ring
        _ ≤ ∑ t ∈ blocks j, gain N t :=
          Finset.sum_le_sum fun t _ht => gainFloor_le_gain N t
        _ = K j := rfl
    have hsm : sdim * ((blocks j).card : ℝ) ≤ epsilon / gainFloor N := by
      apply (le_div_iff₀ hg).2
      have hscaled := mul_le_mul_of_nonneg_left hgainCard hs.le
      nlinarith
    have hsm_nonneg : 0 ≤ sdim * ((blocks j).card : ℝ) :=
      mul_nonneg hs.le (Nat.cast_nonneg _)
    have hepsg_nonneg : 0 ≤ epsilon / gainFloor N :=
      div_nonneg (by norm_num [epsilon]) hg.le
    have hdriftCoef :
        sdim ^ 2 * ((blocks j).card : ℝ) ^ 2 ≤
          epsilon ^ 2 / gainFloor N ^ 2 := by
      have hsq := (sq_le_sq₀ hsm_nonneg hepsg_nonneg).2 hsm
      rw [mul_pow, div_pow] at hsq
      exact hsq
    have hmWeight : ((blocks j).card : ℝ) ≤ w j * K j := by
      exact (div_le_iff₀ hKpos).1 (by simpa [K, blocks] using hratio j hj)
    have hnoiseCoef :
        sdim ^ 2 * ((blocks j).card : ℝ) ≤ epsilon * sdim * w j := by
      have hfirst := mul_le_mul_of_nonneg_left hmWeight (sq_nonneg sdim)
      have hsecond := mul_le_mul_of_nonneg_left hsK
        (mul_nonneg hs.le (hw_nonneg j))
      nlinarith
    have hlocal := corrected_center_block_gradient_energy_le S alpha
      (hestrict j hj) (by simpa [K, blocks, hnetwork] using hKpos)
      (by simpa [sdim, K, blocks, hnetwork] using hsK) halpha
    rw [hnetwork] at hlocal
    have hDnonneg : 0 ≤ ∑ t ∈ blocks j, gain N t * e t := by
      apply Finset.sum_nonneg
      intro t _ht
      apply mul_nonneg
      · exact (gainFloor_le_gain N t).trans' hg.le
      · dsimp [e, SOptLib.expectation]
        exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
    have hVnonneg : 0 ≤ ∑ t ∈ blocks j, v t :=
      Finset.sum_nonneg fun t _ht => hv_nonneg t
    have hQnonneg : 0 ≤ ∑ t ∈ blocks j, q t :=
      Finset.sum_nonneg fun t _ht => hq_nonneg t
    have hratioD := mul_le_mul_of_nonneg_right (hratio j hj) hDnonneg
    have hdriftScaled := mul_le_mul_of_nonneg_right hdriftCoef hVnonneg
    have hnoiseScaled := mul_le_mul_of_nonneg_right hnoiseCoef
      (mul_nonneg (sq_nonneg S.σ) hQnonneg)
    have hDscaled := mul_le_mul_of_nonneg_left hratioD
      (by norm_num : (0 : ℝ) ≤ 5)
    have hVscaled := mul_le_mul_of_nonneg_left hdriftScaled
      (by norm_num : (0 : ℝ) ≤ 18)
    have hQscaled := mul_le_mul_of_nonneg_left hnoiseScaled
      (by norm_num : (0 : ℝ) ≤ 18)
    dsimp [blocks, e, v, q, sdim] at hlocal hDscaled hVscaled hQscaled ⊢
    calc
      _ ≤ (5 * (((Finset.Ico (endpoint j) (endpoint (j + 1))).card : ℝ) /
              (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t)) *
            (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
              gain N t * SOptLib.expectation S.probability (fun omega =>
                ‖gradient (averageObjective S)
                  (correctedCenter S omega alpha t)‖ ^ 2)) +
          18 * (S.L * alpha) ^ 2 *
            ((Finset.Ico (endpoint j) (endpoint (j + 1))).card : ℝ) ^ 2 *
            (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
              SOptLib.expectation S.probability (fun omega =>
                ‖correctedDrift S omega alpha t‖ ^ 2))) +
          18 * (S.L * alpha) ^ 2 *
            ((Finset.Ico (endpoint j) (endpoint (j + 1))).card : ℝ) *
            (S.σ ^ 2 * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
              influenceEnergy N t) := hlocal
      _ ≤ _ := by
        convert add_le_add (add_le_add hDscaled hVscaled) hQscaled using 1 <;> ring
  have hsum := Finset.sum_le_sum fun j (hj : j ∈ Finset.range blockCount) =>
    hblock j (Finset.mem_range.mp hj)
  have hePartition :
      (∑ j ∈ Finset.range blockCount, ∑ t ∈ blocks j, e t) =
        correctedGradientEnergy S alpha T := by
    simpa [blocks, e, correctedGradientEnergy] using hpartition e
  have hvPartition :
      (∑ j ∈ Finset.range blockCount, ∑ t ∈ blocks j, v t) =
        correctedDriftEnergy S alpha T := by
    simpa [blocks, v, correctedDriftEnergy] using hpartition v
  have hfive :
      (∑ j ∈ Finset.range blockCount,
        5 * w j * (∑ t ∈ blocks j, gain N t * e t)) =
        5 * ∑ j ∈ Finset.range blockCount,
          w j * (∑ t ∈ blocks j, gain N t * e t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hePartition] at hsum
  calc
    correctedGradientEnergy S alpha T ≤
        ∑ j ∈ Finset.range blockCount,
          (5 * w j * (∑ t ∈ blocks j, gain N t * e t) +
            18 * epsilon ^ 2 / gainFloor N ^ 2 * (∑ t ∈ blocks j, v t) +
            18 * epsilon * sdim * S.σ ^ 2 *
              (w j * ∑ t ∈ blocks j, q t)) := hsum
    _ = 5 * ∑ j ∈ Finset.range blockCount,
          w j * (∑ t ∈ blocks j, gain N t * e t) +
        18 * epsilon ^ 2 / gainFloor N ^ 2 *
          correctedDriftEnergy S alpha T +
        18 * epsilon * sdim * S.σ ^ 2 *
          (∑ j ∈ Finset.range blockCount,
            w j * ∑ t ∈ blocks j, q t) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        hfive, ← Finset.mul_sum, ← Finset.mul_sum, hvPartition]
    _ = _ := by
      rfl

/-- Source equation (16) for block-indexed suffix weights.  The proof builds
the monotone block index selected by the largest block start not exceeding the
current time, then invokes the already-proved time-weighted descent theorem. -/
private theorem corrected_center_partition_suffix_descent
    (N : NetworkSetup n) (S : Setup n d Ω) (hnetwork : S.network = N)
    (alpha : ℝ) (halpha : 0 < alpha) (T : PositiveHorizon)
    (blockCount : ℕ) (endpoint : ℕ → ℕ) (w : ℕ → ℝ)
    (hcount : 0 < blockCount) (he0 : endpoint 0 = 0)
    (heT : endpoint blockCount = T.1)
    (hestrict : ∀ j < blockCount, endpoint j < endpoint (j + 1))
    (hpartition : ∀ f : ℕ → ℝ,
      (∑ j ∈ Finset.range blockCount,
          ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), f t) =
        ∑ t ∈ Finset.range T.1, f t)
    (hw_nonneg : ∀ j, 0 ≤ w j)
    (hw_anti : ∀ j, w (j + 1) ≤ w j) :
    alpha * (∑ j ∈ Finset.range blockCount,
        w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
          gain N t * SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) ≤
      w 0 * S.Δ +
        alpha * w 0 *
          (Real.sqrt (correctedGradientEnergy S alpha T) *
            Real.sqrt (correctedDriftEnergy S alpha T)) +
        (S.L * alpha ^ 2 / 2) * w 0 *
          ((n : ℝ) * Real.sqrt (correctedGradientEnergy S alpha T) +
            Real.sqrt (correctedDriftEnergy S alpha T)) ^ 2 +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 *
          (∑ j ∈ Finset.range blockCount,
            w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
              influenceEnergy N t) := by
  classical
  have hendpoint_mono : ∀ {a b : ℕ}, a ≤ b → b ≤ blockCount →
      endpoint a ≤ endpoint b := by
    intro a b hab hb
    induction b with
    | zero =>
      have ha0 : a = 0 := by omega
      subst a
      exact le_rfl
    | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact (ih hab' (by omega)).trans (hestrict b (by omega)).le
  have hw_le_of_le : ∀ {a b : ℕ}, a ≤ b → w b ≤ w a := by
    intro a b hab
    induction b with
    | zero =>
      have ha0 : a = 0 := by omega
      subst a
      exact le_rfl
    | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact (hw_anti b).trans (ih hab')
  let eligible : ℕ → Finset ℕ := fun t =>
    (Finset.range blockCount).filter fun j => endpoint j ≤ t
  have heligible_nonempty (t : ℕ) : (eligible t).Nonempty := by
    refine ⟨0, ?_⟩
    simp [eligible, hcount, he0]
  let index : ℕ → ℕ := fun t => (eligible t).max' (heligible_nonempty t)
  have hindex_mem (t : ℕ) : index t ∈ eligible t := by
    exact Finset.max'_mem _ _
  have hindex_lt (t : ℕ) : index t < blockCount := by
    have hm := hindex_mem t
    simpa [eligible] using (Finset.mem_filter.mp hm).1
  have hindex_start (t : ℕ) : endpoint (index t) ≤ t := by
    have hm := hindex_mem t
    exact (Finset.mem_filter.mp hm).2
  have hindex_mono {t u : ℕ} (htu : t ≤ u) : index t ≤ index u := by
    apply Finset.le_max'
    have hm := hindex_mem t
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp hm).1,
      (Finset.mem_filter.mp hm).2.trans htu⟩
  have hindex_eq (j t : ℕ) (hj : j < blockCount)
      (ht : t ∈ Finset.Ico (endpoint j) (endpoint (j + 1))) :
      index t = j := by
    have htbounds := Finset.mem_Ico.mp ht
    apply le_antisymm
    · have himem := hindex_mem t
      have hiRange := (Finset.mem_filter.mp himem).1
      have hiStart := (Finset.mem_filter.mp himem).2
      have hiLt : index t < blockCount := Finset.mem_range.mp hiRange
      by_contra hnot
      have hji : j + 1 ≤ index t := by omega
      have hmono := hendpoint_mono hji hiLt.le
      omega
    · apply Finset.le_max'
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hj, htbounds.1⟩
  let timeWeight : ℕ → ℝ := fun t => w (index t)
  have htime_nonneg (t : ℕ) : 0 ≤ timeWeight t := hw_nonneg _
  have htime_anti (t : ℕ) : timeWeight (t + 1) ≤ timeWeight t := by
    exact hw_le_of_le (hindex_mono (Nat.le_succ t))
  have htime_le_first (t : ℕ) : timeWeight t ≤ timeWeight 0 := by
    exact hw_le_of_le (hindex_mono (Nat.zero_le t))
  have hindex_zero : index 0 = 0 := by
    apply hindex_eq 0 0 hcount
    apply Finset.mem_Ico.mpr
    constructor
    · rw [he0]
    · simpa [he0] using hestrict 0 hcount
  have htime_zero : timeWeight 0 = w 0 := by simp [timeWeight, hindex_zero]
  have hweighted_partition (f : ℕ → ℝ) :
      (∑ t ∈ Finset.range T.1, timeWeight t * f t) =
        ∑ j ∈ Finset.range blockCount,
          w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), f t := by
    rw [← hpartition (fun t => timeWeight t * f t)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [show timeWeight t = w j by
      simp only [timeWeight]
      rw [hindex_eq j t (Finset.mem_range.mp hj) ht]]
  have hgradPartition :
      (∑ t ∈ Finset.range T.1,
        timeWeight t * gain N t *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t)‖ ^ 2)) =
        ∑ j ∈ Finset.range blockCount,
          w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
            gain N t * SOptLib.expectation S.probability (fun omega =>
              ‖gradient (averageObjective S)
                (correctedCenter S omega alpha t)‖ ^ 2) := by
    calc
      _ = ∑ t ∈ Finset.range T.1,
          timeWeight t * (gain N t *
            SOptLib.expectation S.probability (fun omega =>
              ‖gradient (averageObjective S)
                (correctedCenter S omega alpha t)‖ ^ 2)) := by
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      _ = _ := hweighted_partition _
  have hdescent := corrected_center_suffix_weighted_gain_descent
    S alpha halpha T timeWeight htime_nonneg htime_anti htime_le_first
  rw [hnetwork] at hdescent
  rw [hgradPartition, hweighted_partition (fun t => influenceEnergy N t),
    htime_zero] at hdescent
  exact hdescent

/-- The scalar Young-inequality and feedback absorption between source
equations (16) and (17).  The cap hypotheses are exactly the three scalar
consequences of equation (14) used in this calculation. -/
private theorem corrected_center_equation17_gradient_absorption
    (s alpha g nR Δ σ H TR rH rB rN G V Q D w0 : ℝ)
    (hs : 0 < s) (halpha : 0 < alpha) (hg : 0 < g) (hn : 0 ≤ nR)
    (hG : 0 ≤ G) (hV : 0 ≤ V) (hw0nonneg : 0 ≤ w0)
    (hw0 : w0 ≤ 1 / g)
    (hcapG : 20 * s * nR ^ 2 ≤ g)
    (hcapV : 20 * s * g ≤ 1)
    (hcapRB : 104 * s ^ 2 * rB ≤ g ^ 2)
    (haggregate : G ≤
      5 * D + 18 * epsilon ^ 2 / g ^ 2 * V +
        18 * epsilon * s * σ ^ 2 * Q)
    (hdescent : D ≤
      w0 * Δ / alpha +
        w0 * (Real.sqrt G * Real.sqrt V) +
        (s / 2) * w0 * (nR * Real.sqrt G + Real.sqrt V) ^ 2 +
        s * σ ^ 2 / 2 * Q)
    (hcontrol : V ≤ rH * nR * H ^ 2 +
      s ^ 2 * (rB * G + rN * σ ^ 2 * TR)) :
    G ≤ 20 * w0 * Δ / alpha +
      104 * rH * nR * H ^ 2 / g ^ 2 +
      104 * rN * s ^ 2 * σ ^ 2 * TR / g ^ 2 +
      (29 / 2) * s * σ ^ 2 * Q := by
  set_option maxHeartbeats 3000000 in
  have hs0 : 0 ≤ s := hs.le
  have hg2 : 0 < g ^ 2 := sq_pos_of_pos hg
  have hsqrtG : 0 ≤ Real.sqrt G := Real.sqrt_nonneg _
  have hsqrtV : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
  have hsqrtGsq : (Real.sqrt G) ^ 2 = G := Real.sq_sqrt hG
  have hsqrtVsq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV
  have hrootprod : 0 ≤ Real.sqrt G * Real.sqrt V :=
    mul_nonneg hsqrtG hsqrtV
  have hwroot :
      5 * w0 * (Real.sqrt G * Real.sqrt V) ≤
        5 * (1 / g) * (Real.sqrt G * Real.sqrt V) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw0 (by norm_num)) hrootprod
  have hyoungBase := sq_nonneg (g * Real.sqrt G / 2 - 5 * Real.sqrt V)
  have hyoungScaled :
      5 * g * (Real.sqrt G * Real.sqrt V) ≤
        g ^ 2 * G / 4 + 25 * V := by
    nlinarith [hsqrtGsq, hsqrtVsq, hyoungBase]
  have hyoungCross :
      5 * w0 * (Real.sqrt G * Real.sqrt V) ≤
        G / 4 + 25 * V / g ^ 2 := by
    calc
      _ ≤ 5 * (1 / g) * (Real.sqrt G * Real.sqrt V) := hwroot
      _ ≤ G / 4 + 25 * V / g ^ 2 := by
        have hscaled := mul_le_mul_of_nonneg_left hyoungScaled
          (one_div_nonneg.mpr hg2.le)
        convert hscaled using 1 <;> field_simp [ne_of_gt hg] <;> ring
  have hrootSum :
      (nR * Real.sqrt G + Real.sqrt V) ^ 2 ≤
        2 * (nR ^ 2 * G + V) := by
    nlinarith [sq_nonneg (nR * Real.sqrt G - Real.sqrt V)]
  have hweightCoef : (5 * s / 2) * w0 ≤ (5 * s / 2) * (1 / g) := by
    exact mul_le_mul_of_nonneg_left hw0
      (div_nonneg (mul_nonneg (by norm_num) hs0) (by norm_num))
  have hrootSumNonneg : 0 ≤ (nR * Real.sqrt G + Real.sqrt V) ^ 2 :=
    sq_nonneg _
  have hweightedRoot :
      (5 * s / 2) * w0 * (nR * Real.sqrt G + Real.sqrt V) ^ 2 ≤
        5 * s / g * (nR ^ 2 * G + V) := by
    have hfirst := mul_le_mul_of_nonneg_right hweightCoef hrootSumNonneg
    have hcoefnonneg : 0 ≤ (5 * s / 2) * (1 / g) :=
      mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hs0) (by norm_num))
        (one_div_nonneg.mpr hg.le)
    have hsecond := mul_le_mul_of_nonneg_left hrootSum hcoefnonneg
    calc
      _ ≤ (5 * s / 2) * (1 / g) *
          (nR * Real.sqrt G + Real.sqrt V) ^ 2 := hfirst
      _ ≤ (5 * s / 2) * (1 / g) * (2 * (nR ^ 2 * G + V)) := hsecond
      _ ≤ 5 * s / g * (nR ^ 2 * G + V) := by
        have hX : 0 ≤ nR ^ 2 * G + V :=
          add_nonneg (mul_nonneg (sq_nonneg _) hG) hV
        have hcoef : 5 * s / 2 * (1 / g) * 2 ≤ 5 * s / g := by
          field_simp [ne_of_gt hg]
          nlinarith
        nlinarith
  have hcoefG : 5 * s / g * nR ^ 2 ≤ 1 / 4 := by
    rw [show 5 * s / g * nR ^ 2 = (5 * s * nR ^ 2) / g by ring]
    apply (div_le_iff₀ hg).2
    nlinarith
  have hGabsorb : 5 * s / g * (nR ^ 2 * G) ≤ G / 4 := by
    have := mul_le_mul_of_nonneg_right hcoefG hG
    nlinarith
  have hcoefV : 5 * s / g ≤ 1 / (4 * g ^ 2) := by
    apply (div_le_div_iff₀ hg (mul_pos (by norm_num) hg2)).2
    nlinarith
  have hVabsorb : 5 * s / g * V ≤ V / (4 * g ^ 2) := by
    convert mul_le_mul_of_nonneg_right hcoefV hV using 1 <;> ring
  have hyoungSquare :
      (5 * s / 2) * w0 * (nR * Real.sqrt G + Real.sqrt V) ^ 2 ≤
        G / 4 + V / (4 * g ^ 2) := by
    calc
      _ ≤ 5 * s / g * (nR ^ 2 * G + V) := hweightedRoot
      _ = 5 * s / g * (nR ^ 2 * G) + 5 * s / g * V := by ring
      _ ≤ _ := add_le_add hGabsorb hVabsorb
  have hDscaled := mul_le_mul_of_nonneg_left hdescent
    (by norm_num : (0 : ℝ) ≤ 5)
  norm_num [epsilon] at haggregate
  have hpreControl :
      G ≤ 10 * w0 * Δ / alpha +
        52 * V / g ^ 2 + (29 / 4) * s * σ ^ 2 * Q := by
    have hraw :
        G ≤ 5 * w0 * Δ / alpha + G / 2 +
          26 * V / g ^ 2 + (29 / 8) * s * σ ^ 2 * Q := by
      have hinv : 0 ≤ (g ^ 2)⁻¹ := inv_nonneg.mpr hg2.le
      have hVinv : 0 ≤ V * (g ^ 2)⁻¹ := mul_nonneg hV hinv
      ring_nf at haggregate hDscaled hyoungCross hyoungSquare ⊢
      nlinarith
    ring_nf at hraw ⊢
    linarith
  have hcontrolScaled := mul_le_mul_of_nonneg_left hcontrol
    (div_nonneg (by norm_num) hg2.le : 0 ≤ 52 / g ^ 2)
  have hfeedbackCoef : 52 * s ^ 2 * rB / g ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ hg2).2
    nlinarith
  have hfeedback : 52 * s ^ 2 * rB / g ^ 2 * G ≤ G / 2 :=
    by convert mul_le_mul_of_nonneg_right hfeedbackCoef hG using 1 <;> ring
  have hwithFeedback :
      G ≤ 10 * w0 * Δ / alpha +
        52 * rH * nR * H ^ 2 / g ^ 2 +
        52 * rN * s ^ 2 * σ ^ 2 * TR / g ^ 2 +
        (29 / 4) * s * σ ^ 2 * Q + G / 2 := by
    ring_nf at hpreControl hcontrolScaled hfeedback ⊢
    nlinarith
  ring_nf at hwithFeedback ⊢
  linarith

/-- Equation (17) for one member of the fixed instance class, before the
causal-window substitution. -/
private theorem fixed_instance_partition_cost_le
    (N : NetworkSetup n) (L Δ σ H : ℝ) (hL : 0 < L)
    (I : fixedInstanceClass N L Δ σ H)
    (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n)
    (hsCap : s.1 ≤ correctedCenterStepCap N)
    (hcapG : 20 * s.1 * (n : ℝ) ^ 2 ≤ gainFloor N)
    (hcapV : 20 * s.1 * gainFloor N ≤ 1)
    (hcapRB : 104 * s.1 ^ 2 * controlRB N ≤ gainFloor N ^ 2)
    (hcapJB : s.1 ^ 2 * controlJB N ≤ 1)
    (blockCount : ℕ) (endpoint : ℕ → ℕ) (w : ℕ → ℝ)
    (hcount : 0 < blockCount) (he0 : endpoint 0 = 0)
    (heT : endpoint blockCount = T.1)
    (hestrict : ∀ j < blockCount, endpoint j < endpoint (j + 1))
    (hebudget : ∀ j < blockCount,
      1 / (64 * s.1) ≤
          ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t ∧
        (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t) ≤
          1 / (16 * s.1))
    (hpartition : ∀ f : ℕ → ℝ,
      (∑ j ∈ Finset.range blockCount,
          ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), f t) =
        ∑ t ∈ Finset.range T.1, f t)
    (hw_nonneg : ∀ j, 0 ≤ w j) (hw_anti : ∀ j, w (j + 1) ≤ w j)
    (hw0 : w 0 ≤ 1 / gainFloor N)
    (hratio : ∀ j < blockCount,
      ((Finset.Ico (endpoint j) (endpoint (j + 1))).card : ℝ) /
          (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t) ≤ w j) :
    let Qw := ∑ j ∈ Finset.range blockCount,
      w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
        influenceEnergy N t
    let KH :=
      (416 * controlRH N / gainFloor N ^ 2 +
          2 * correctedCenterStepCap N ^ 2 * controlJH N) * n * H ^ 2
    let KN := 416 * controlRN N / gainFloor N ^ 2 + 2 * controlJN N
    FiniteInstance.cost I.1 (s.1 / L) T ≤
      80 * Δ * w 0 / ((s.1 / L) * T.1) +
        58 * s.1 * σ ^ 2 * Qw / T.1 + KH / T.1 +
        KN * σ ^ 2 * s.1 ^ 2 := by
  set_option maxHeartbeats 3000000 in
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  dsimp only
  let S := I.1.setup
  let alpha : ℝ := s.1 / L
  let Qw : ℝ := ∑ j ∈ Finset.range blockCount,
    w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
      influenceEnergy N t
  let KH : ℝ :=
    (416 * controlRH N / gainFloor N ^ 2 +
        2 * correctedCenterStepCap N ^ 2 * controlJH N) * n * H ^ 2
  let KN : ℝ := 416 * controlRN N / gainFloor N ^ 2 + 2 * controlJN N
  have hnetwork : S.network = N := by
    simpa [S, FiniteInstance.network] using I.2.1
  have hLip : S.L = L := by
    simpa [S, FiniteInstance.lipschitz] using I.2.2.1
  have hgap : S.Δ = Δ := by
    simpa [S, FiniteInstance.gap] using I.2.2.2.1
  have hnoise : S.σ = σ := by
    simpa [S, FiniteInstance.noiseScale] using I.2.2.2.2.1
  have hheterogeneity : S.H = H := by
    simpa [S, FiniteInstance.heterogeneityScale] using I.2.2.2.2.2
  have hfinite : InFiniteHeterogeneityLayer S := by
    simpa [S] using I.1.finite_layer
  have halpha : 0 < alpha := div_pos s.2.1 hL
  have hsDim : S.L * alpha = s.1 := by
    dsimp [alpha]
    rw [hLip]
    field_simp [ne_of_gt hL]
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hGnonneg : 0 ≤ correctedGradientEnergy S alpha T := by
    unfold correctedGradientEnergy
    exact Finset.sum_nonneg fun t _ht => by
      unfold SOptLib.expectation
      exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hVnonneg : 0 ≤ correctedDriftEnergy S alpha T := by
    unfold correctedDriftEnergy
    exact Finset.sum_nonneg fun t _ht => by
      unfold SOptLib.expectation
      exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hw0nonneg : 0 ≤ w 0 := hw_nonneg 0
  have hebudgetS : ∀ j < blockCount,
      1 / (64 * (S.L * alpha)) ≤
          ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t ∧
        (∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)), gain N t) ≤
          1 / (16 * (S.L * alpha)) := by
    simpa [hsDim] using hebudget
  have haggregate := corrected_center_partition_gradient_energy_le
    N S hnetwork alpha halpha T blockCount endpoint w hestrict hebudgetS
    hpartition hw_nonneg hratio
  have hdescentRaw := corrected_center_partition_suffix_descent
    N S hnetwork alpha halpha T blockCount endpoint w hcount he0 heT
    hestrict hpartition hw_nonneg hw_anti
  let D : ℝ := ∑ j ∈ Finset.range blockCount,
    w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
      gain N t * SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2)
  have hdescent : D ≤
      w 0 * S.Δ / alpha +
        w 0 * (Real.sqrt (correctedGradientEnergy S alpha T) *
          Real.sqrt (correctedDriftEnergy S alpha T)) +
        (s.1 / 2) * w 0 *
          ((n : ℝ) * Real.sqrt (correctedGradientEnergy S alpha T) +
            Real.sqrt (correctedDriftEnergy S alpha T)) ^ 2 +
        s.1 * S.σ ^ 2 / 2 * Qw := by
    have hLa2 : S.L * alpha ^ 2 = s.1 * alpha := by
      rw [← hsDim]
      ring
    have hscaled : alpha * D ≤ alpha *
        (w 0 * S.Δ / alpha +
          w 0 * (Real.sqrt (correctedGradientEnergy S alpha T) *
            Real.sqrt (correctedDriftEnergy S alpha T)) +
          (s.1 / 2) * w 0 *
            ((n : ℝ) * Real.sqrt (correctedGradientEnergy S alpha T) +
              Real.sqrt (correctedDriftEnergy S alpha T)) ^ 2 +
          s.1 * S.σ ^ 2 / 2 * Qw) := by
      dsimp [D, Qw] at hdescentRaw ⊢
      rw [hLa2] at hdescentRaw
      convert hdescentRaw using 1 <;>
        field_simp [ne_of_gt halpha] <;> ring
    exact le_of_mul_le_mul_left hscaled halpha
  have hcontrol := corrected_center_uniform_control S hfinite alpha halpha
    (by
      rw [show dimensionlessStepsize S.L alpha = s.1 by
        unfold dimensionlessStepsize
        simpa [mul_comm] using hsDim]
      rw [hnetwork]
      exact hsCap) T
  rcases hcontrol with ⟨_, _, _, _, _, _, _, _, hVcontrol, _, _⟩
  have hVcontrol' : correctedDriftEnergy S alpha T ≤
      controlRH N * (n : ℝ) * H ^ 2 +
        s.1 ^ 2 * (controlRB N * correctedGradientEnergy S alpha T +
          controlRN N * σ ^ 2 * T.1) := by
    rw [hnetwork, hheterogeneity, hnoise] at hVcontrol
    rw [show dimensionlessStepsize S.L alpha = s.1 by
      unfold dimensionlessStepsize
      simpa [mul_comm] using hsDim] at hVcontrol
    exact hVcontrol
  have hGbound := corrected_center_equation17_gradient_absorption
    s.1 alpha (gainFloor N) (n : ℝ) S.Δ S.σ S.H T.1
    (controlRH N) (controlRB N) (controlRN N)
    (correctedGradientEnergy S alpha T) (correctedDriftEnergy S alpha T)
    Qw D (w 0) s.2.1 halpha hg hn hGnonneg hVnonneg hw0nonneg hw0
    hcapG hcapV hcapRB (by
      rw [hsDim] at haggregate
      simpa [D, Qw] using haggregate) hdescent
    (by simpa [hheterogeneity, hnoise] using hVcontrol')
  rw [hgap, hnoise, hheterogeneity] at hGbound
  have hcost := fixed_instance_cost_le_corrected_energy_expression
    N L Δ σ H hL I T s hsCap
  have hT : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  have hsCap0 : 0 ≤ correctedCenterStepCap N := s.2.1.le.trans hsCap
  have hsSqCap : s.1 ^ 2 ≤ correctedCenterStepCap N ^ 2 := by
    exact (sq_le_sq₀ s.2.1.le hsCap0).2 hsCap
  have hGcoef : 2 + 2 * s.1 ^ 2 * controlJB N ≤ 4 := by
    nlinarith
  have hJHnonneg : 0 ≤ controlJH N := by
    have hdenom : 0 ≤ 1 - mixingRate N ^ 2 := by
      nlinarith [mixingRate_nonneg N, mixingRate_lt_one N]
    have hA0 : 0 ≤ trackerInitialKernel N := by
      unfold trackerInitialKernel
      exact div_nonneg (by positivity) hdenom
    unfold controlJH controlMH disagreementKernel
    positivity
  have hHterm :
      2 * s.1 ^ 2 * controlJH N * (n : ℝ) * H ^ 2 ≤
        2 * correctedCenterStepCap N ^ 2 * controlJH N * (n : ℝ) * H ^ 2 := by
    have hcoef : 0 ≤ 2 * controlJH N * (n : ℝ) * H ^ 2 :=
      mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hJHnonneg) hn)
        (sq_nonneg H)
    have htmp := mul_le_mul_of_nonneg_right hsSqCap hcoef
    convert htmp using 1 <;> ring
  dsimp only at hcost
  have hGscaled := mul_le_mul_of_nonneg_left hGbound
    (by norm_num : (0 : ℝ) ≤ 4)
  have hTinv : 0 ≤ (T.1 : ℝ)⁻¹ := inv_nonneg.mpr hT.le
  let G : ℝ := correctedGradientEnergy S alpha T
  have hinside :
      2 * G + 2 * s.1 ^ 2 *
          (controlJB N * G + controlJH N * (n : ℝ) * H ^ 2 +
            controlJN N * σ ^ 2 * T.1) ≤
        4 * G +
          2 * correctedCenterStepCap N ^ 2 * controlJH N * (n : ℝ) * H ^ 2 +
          2 * controlJN N * σ ^ 2 * T.1 * s.1 ^ 2 := by
    have hGpart := mul_le_mul_of_nonneg_right hGcoef hGnonneg
    dsimp [G] at hGpart ⊢
    convert add_le_add (add_le_add hGpart hHterm)
      (le_refl (2 * controlJN N * σ ^ 2 * T.1 * s.1 ^ 2)) using 1 <;> ring
  have hinside2 :
      4 * G +
          2 * correctedCenterStepCap N ^ 2 * controlJH N * (n : ℝ) * H ^ 2 +
          2 * controlJN N * σ ^ 2 * T.1 * s.1 ^ 2 ≤
        4 * (20 * w 0 * Δ / alpha +
          104 * controlRH N * (n : ℝ) * H ^ 2 / gainFloor N ^ 2 +
          104 * controlRN N * s.1 ^ 2 * σ ^ 2 * T.1 / gainFloor N ^ 2 +
          (29 / 2) * s.1 * σ ^ 2 * Qw) +
          2 * correctedCenterStepCap N ^ 2 * controlJH N * (n : ℝ) * H ^ 2 +
          2 * controlJN N * σ ^ 2 * T.1 * s.1 ^ 2 := by
    dsimp [G] at hGscaled ⊢
    convert add_le_add hGscaled (le_refl
      (2 * correctedCenterStepCap N ^ 2 * controlJH N * (n : ℝ) * H ^ 2 +
        2 * controlJN N * σ ^ 2 * T.1 * s.1 ^ 2)) using 1 <;> ring
  calc
    FiniteInstance.cost I.1 (s.1 / L) T ≤
        (T.1 : ℝ)⁻¹ * (2 * G + 2 * s.1 ^ 2 *
          (controlJB N * G + controlJH N * (n : ℝ) * H ^ 2 +
            controlJN N * σ ^ 2 * T.1)) := by
      simpa [G, S, alpha] using hcost
    _ ≤ (T.1 : ℝ)⁻¹ * (4 * G +
          2 * correctedCenterStepCap N ^ 2 * controlJH N * (n : ℝ) * H ^ 2 +
          2 * controlJN N * σ ^ 2 * T.1 * s.1 ^ 2) :=
      mul_le_mul_of_nonneg_left hinside hTinv
    _ ≤ (T.1 : ℝ)⁻¹ * (4 * (20 * w 0 * Δ / alpha +
          104 * controlRH N * (n : ℝ) * H ^ 2 / gainFloor N ^ 2 +
          104 * controlRN N * s.1 ^ 2 * σ ^ 2 * T.1 / gainFloor N ^ 2 +
          (29 / 2) * s.1 * σ ^ 2 * Qw) +
          2 * correctedCenterStepCap N ^ 2 * controlJH N * (n : ℝ) * H ^ 2 +
          2 * controlJN N * σ ^ 2 * T.1 * s.1 ^ 2) :=
      mul_le_mul_of_nonneg_left hinside2 hTinv
    _ = _ := by
      dsimp [alpha, KH, KN, Qw]
      field_simp [ne_of_gt hT, ne_of_gt hL, ne_of_gt s.2.1]
      ring

set_option maxHeartbeats 3000000

/-- Equations (18)--(20): one deterministic horizon-dependent constant
stepsize controls every instance in the same class. -/
theorem block_window_upper_bound
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    ∃ Tplus : ℕ, ∀ H : ℝ, 0 ≤ H → ∃ K₂ : ℝ,
      ∀ T : PositiveHorizon, Tplus ≤ T.1 →
      ∃ sT : AdmissibleDimensionlessStepsize n,
        dimensionlessStepsize L (sT.1 / L) = sT.1 ∧
        comparatorAt N L Δ σ T sT ≤
          comparator N L Δ σ T + ADelta L Δ / T.1 ∧
        (⨆ I : fixedInstanceClass N L Δ σ H,
          ENNReal.ofReal (FiniteInstance.cost I.1 (sT.1 / L) T)) ≤
            ENNReal.ofReal (512 * comparator N L Δ σ T + K₂ / T.1) := by
  obtain ⟨Tloc, hselect⟩ :=
    localized_near_comparator_with_center_cap N L Δ σ hL hΔ hσ
  let C : ℝ := comparatorStepUpperConstant N L Δ σ
  have hC : 0 < C :=
    (comparator_localization_constants_pos N L Δ σ hL hΔ hσ).2.2.2.2.2
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hdis : 0 ≤ disagreementKernel N := by
    unfold disagreementKernel
    positivity
  have htrackerInc : 0 ≤ trackerIncrementKernel N := by
    unfold trackerIncrementKernel incrementKernel
    positivity
  have hRB : 0 ≤ controlRB N := by
    unfold controlRB controlKa controlMB
    positivity
  have hJB : 0 ≤ controlJB N := by
    unfold controlJB controlMB
    positivity
  let capThreshold : ℝ := max ((20 * C * (n : ℝ) ^ 2 / gainFloor N) ^ 2)
    (max ((20 * C * gainFloor N) ^ 2)
      (max (104 * C ^ 2 * controlRB N / gainFloor N ^ 2)
        (C ^ 2 * controlJB N)))
  obtain ⟨Tcap, hTcap⟩ := exists_nat_gt capThreshold
  let Tplus : ℕ := max Tloc Tcap
  refine ⟨Tplus, ?_⟩
  intro H hH
  let KH : ℝ :=
    (416 * controlRH N / gainFloor N ^ 2 +
        2 * correctedCenterStepCap N ^ 2 * controlJH N) * n * H ^ 2
  let KN : ℝ := 416 * controlRN N / gainFloor N ^ 2 + 2 * controlJN N
  let K₂ : ℝ :=
    512 * ADelta L Δ + KH +
      (29 / 2) * σ ^ 2 * influenceRowBound N ^ 2 / gainFloor N ^ 2 +
      KN * σ ^ 2 * comparatorStepUpperConstant N L Δ σ ^ 2
  refine ⟨K₂, ?_⟩
  intro T hTplus
  have hTloc : Tloc ≤ T.1 := (le_max_left Tloc Tcap).trans hTplus
  have hTcapNat : Tcap ≤ T.1 := (le_max_right Tloc Tcap).trans hTplus
  obtain ⟨sT, hnear, hlower, hupper, hcap, htotal⟩ := hselect T hTloc
  have hTreal : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  have hsqrtT : 0 < Real.sqrt (T.1 : ℝ) := Real.sqrt_pos.2 hTreal
  have hcapThresholdT : capThreshold < (T.1 : ℝ) := by
    exact hTcap.trans_le (by exact_mod_cast hTcapNat)
  have hsquareUpper : sT.1 ^ 2 * (T.1 : ℝ) ≤ C ^ 2 := by
    have hmul : sT.1 * Real.sqrt (T.1 : ℝ) ≤ C :=
      (le_div_iff₀ hsqrtT).1 (by simpa [C] using hupper)
    have hsq := (sq_le_sq₀
      (mul_nonneg sT.2.1.le (Real.sqrt_nonneg _)) hC.le).2 hmul
    rw [mul_pow, Real.sq_sqrt hTreal.le] at hsq
    nlinarith
  have hcapG : 20 * sT.1 * (n : ℝ) ^ 2 ≤ gainFloor N := by
    have hth : (20 * C * (n : ℝ) ^ 2 / gainFloor N) ^ 2 <
        (T.1 : ℝ) := lt_of_le_of_lt (le_max_left _ _) hcapThresholdT
    have hroot : 20 * C * (n : ℝ) ^ 2 / gainFloor N <
        Real.sqrt (T.1 : ℝ) := Real.lt_sqrt_of_sq_lt hth
    have hcross : C * (20 * (n : ℝ) ^ 2) <
        gainFloor N * Real.sqrt (T.1 : ℝ) := by
      have := (div_lt_iff₀ hg).1 hroot
      nlinarith
    have hratio : C / Real.sqrt (T.1 : ℝ) <
        gainFloor N / (20 * (n : ℝ) ^ 2) :=
      (div_lt_div_iff₀ hsqrtT (by positivity)).2 (by nlinarith)
    have hsSmall : sT.1 < gainFloor N / (20 * (n : ℝ) ^ 2) :=
      hupper.trans_lt (by simpa [C] using hratio)
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 20 * (n : ℝ) ^ 2)).1 hsSmall
    nlinarith
  have hcapV : 20 * sT.1 * gainFloor N ≤ 1 := by
    have hle : (20 * C * gainFloor N) ^ 2 ≤ capThreshold := by
      dsimp [capThreshold]
      exact (le_max_left _ _).trans (le_max_right _ _)
    have hth : (20 * C * gainFloor N) ^ 2 < (T.1 : ℝ) :=
      hle.trans_lt hcapThresholdT
    have hroot : 20 * C * gainFloor N < Real.sqrt (T.1 : ℝ) :=
      Real.lt_sqrt_of_sq_lt hth
    have hratio : C / Real.sqrt (T.1 : ℝ) < 1 / (20 * gainFloor N) :=
      (div_lt_div_iff₀ hsqrtT (mul_pos (by norm_num) hg)).2 (by nlinarith)
    have hsSmall : sT.1 < 1 / (20 * gainFloor N) :=
      hupper.trans_lt (by simpa [C] using hratio)
    have := (lt_div_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 20) hg)).1 hsSmall
    nlinarith
  have hcapRB : 104 * sT.1 ^ 2 * controlRB N ≤ gainFloor N ^ 2 := by
    have hle : 104 * C ^ 2 * controlRB N / gainFloor N ^ 2 ≤
        capThreshold := by
      dsimp [capThreshold]
      exact ((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)
    have hth : 104 * C ^ 2 * controlRB N / gainFloor N ^ 2 <
        (T.1 : ℝ) := hle.trans_lt hcapThresholdT
    have hth' : 104 * C ^ 2 * controlRB N <
        (T.1 : ℝ) * gainFloor N ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hg)).1 hth
    have hscaled := mul_le_mul_of_nonneg_right hsquareUpper
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 104) hRB)
    have hTnonneg : 0 ≤ (T.1 : ℝ) := hTreal.le
    have hfinal : (104 * sT.1 ^ 2 * controlRB N) * (T.1 : ℝ) ≤
        gainFloor N ^ 2 * (T.1 : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right hfinal hTreal
  have hcapJB : sT.1 ^ 2 * controlJB N ≤ 1 := by
    have hle : C ^ 2 * controlJB N ≤ capThreshold := by
      dsimp [capThreshold]
      exact ((le_max_right _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)
    have hth : C ^ 2 * controlJB N < (T.1 : ℝ) :=
      hle.trans_lt hcapThresholdT
    have hscaled := mul_le_mul_of_nonneg_right hsquareUpper hJB
    have hfinal : (sT.1 ^ 2 * controlJB N) * (T.1 : ℝ) ≤
        (T.1 : ℝ) := by nlinarith
    exact le_of_mul_le_mul_right
      (show (sT.1 ^ 2 * controlJB N) * (T.1 : ℝ) ≤
        1 * (T.1 : ℝ) by simpa using hfinal) hTreal
  have hblockCertificate :=
    backward_gain_partition_source_weight_certificate N T sT htotal
  refine ⟨sT, dimensionlessStepsize_div L sT.1 hL, hnear, ?_⟩
  classical
  obtain ⟨blockCount, endpoint, w, hcount, he0, heT, hestrict,
      hebudget, hpartition, hw_nonneg, hw_anti, hw0, hweight,
      hMzero, hQw⟩ := hblockCertificate
  let blocks : ℕ → Finset ℕ := fun j =>
    Finset.Ico (endpoint j) (endpoint (j + 1))
  let M : ℕ → ℕ := fun j =>
    (Finset.Ico j blockCount).sup fun l => (blocks l).card
  let Qw : ℝ := ∑ j ∈ Finset.range blockCount,
    w j * ∑ t ∈ blocks j, influenceEnergy N t
  let W : ℝ := windowLength N T.1 0 sT.1
  let SW : ℝ := windowInfluenceSum N T.1 sT.1
  let B : ℝ := influenceRowBound N
  let g : ℝ := gainFloor N
  have hWnonneg : 0 ≤ W := Nat.cast_nonneg _
  have hSWnonneg : 0 ≤ SW := by
    dsimp [SW, windowInfluenceSum]
    exact Finset.sum_nonneg fun j _hj =>
      mul_nonneg (by
        unfold influenceEnergy
        exact Finset.sum_nonneg fun i _hi => sq_nonneg _)
        (Nat.cast_nonneg _)
  have hQw' : Qw ≤ 64 * sT.1 * (SW + B ^ 2 * W ^ 2) := by
    simpa [Qw, SW, B, W, blocks] using hQw
  have hw0major : w 0 ≤ 64 * sT.1 * W := by
    have hwM := (hweight 0 hcount).2
    have hMcast : (M 0 : ℝ) ≤ W := by
      dsimp [M, W, blocks]
      exact_mod_cast hMzero
    exact hwM.trans (mul_le_mul_of_nonneg_left hMcast
      (mul_nonneg (by norm_num) sT.2.1.le))
  have hWupper : W ≤ epsilon / (sT.1 * g) := by
    simpa [W, g] using
      windowLength_le_budget_div_gainFloor N T.1 0 sT.1 sT.2.1
  have hWsq : sT.1 ^ 2 * g ^ 2 * W ^ 2 ≤ epsilon ^ 2 := by
    have hprod : sT.1 * g * W ≤ epsilon := by
      have hden : 0 < sT.1 * g := mul_pos sT.2.1 hg
      have hmul := (le_div_iff₀ hden).1 hWupper
      nlinarith
    have hprod0 : 0 ≤ sT.1 * g * W :=
      mul_nonneg (mul_nonneg sT.2.1.le hg.le) hWnonneg
    have hsq := (sq_le_sq₀ hprod0 (by norm_num [epsilon])).2 hprod
    nlinarith
  have hTpos : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  have hA : 0 ≤ ADelta L Δ := (mul_pos hL hΔ).le
  have hSignalComp : 0 ≤ ADelta L Δ * W / (epsilon * T.1) :=
    div_nonneg (mul_nonneg hA hWnonneg)
      (mul_nonneg (by norm_num [epsilon]) hTpos.le)
  have hNoiseComp : 0 ≤
      (σ ^ 2 / 2 * sT.1 ^ 2 * SW) / (epsilon * T.1) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (div_nonneg (sq_nonneg σ) (by norm_num))
          (sq_nonneg sT.1)) hSWnonneg)
      (mul_nonneg (by norm_num [epsilon]) hTpos.le)
  have hsignal :
      80 * Δ * w 0 / ((sT.1 / L) * T.1) ≤
        320 * (ADelta L Δ * W / (epsilon * T.1)) := by
    have hwdiv : w 0 / sT.1 ≤ 64 * W := by
      apply (div_le_iff₀ sT.2.1).2
      nlinarith [hw0major]
    have hscaled := mul_le_mul_of_nonneg_left hwdiv
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) hΔ.le) hL.le)
    have hscaledT := div_le_div_of_nonneg_right hscaled hTpos.le
    unfold ADelta
    norm_num [epsilon]
    convert hscaledT using 1 <;>
      field_simp [ne_of_gt sT.2.1, ne_of_gt hL, ne_of_gt hTpos] <;> ring
  have hnoiseRaw :
      58 * sT.1 * σ ^ 2 * Qw / T.1 ≤
        58 * sT.1 * σ ^ 2 *
          (64 * sT.1 * (SW + B ^ 2 * W ^ 2)) / T.1 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQw'
        (mul_nonneg (mul_nonneg (by norm_num) sT.2.1.le) (sq_nonneg σ)))
      hTpos.le
  have hboundary :
      3712 * sT.1 ^ 2 * σ ^ 2 * B ^ 2 * W ^ 2 / T.1 ≤
        (29 / 2) * σ ^ 2 * B ^ 2 / g ^ 2 / T.1 := by
    have hscale0 : 0 ≤ σ ^ 2 * B ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hcore : 3712 * sT.1 ^ 2 * g ^ 2 * W ^ 2 ≤ 29 / 2 := by
      norm_num [epsilon] at hWsq ⊢
      nlinarith
    apply div_le_div_of_nonneg_right _ hTpos.le
    apply (le_div_iff₀ (sq_pos_of_pos hg)).2
    have hscaled := mul_le_mul_of_nonneg_right hcore hscale0
    convert hscaled using 1 <;> ring
  have hnoise :
      58 * sT.1 * σ ^ 2 * Qw / T.1 ≤
        464 * ((σ ^ 2 / 2 * sT.1 ^ 2 * SW) / (epsilon * T.1)) +
          (29 / 2) * σ ^ 2 * B ^ 2 / g ^ 2 / T.1 := by
    calc
      _ ≤ 58 * sT.1 * σ ^ 2 *
          (64 * sT.1 * (SW + B ^ 2 * W ^ 2)) / T.1 := hnoiseRaw
      _ = 464 * ((σ ^ 2 / 2 * sT.1 ^ 2 * SW) /
            (epsilon * T.1)) +
          3712 * sT.1 ^ 2 * σ ^ 2 * B ^ 2 * W ^ 2 / T.1 := by
        norm_num [epsilon]
        field_simp [ne_of_gt hTpos]
        ring
      _ ≤ _ := add_le_add (le_refl _) hboundary
  have hmain :
      80 * Δ * w 0 / ((sT.1 / L) * T.1) +
          58 * sT.1 * σ ^ 2 * Qw / T.1 ≤
        512 * comparatorAt N L Δ σ T sT +
          (29 / 2) * σ ^ 2 * B ^ 2 / g ^ 2 / T.1 := by
    have hsum := add_le_add hsignal hnoise
    have henlarge :
        320 * (ADelta L Δ * W / (epsilon * T.1)) +
            (464 * ((σ ^ 2 / 2 * sT.1 ^ 2 * SW) / (epsilon * T.1)) +
              (29 / 2) * σ ^ 2 * B ^ 2 / g ^ 2 / T.1) ≤
          512 * ((ADelta L Δ * W +
              (σ ^ 2 / 2) * sT.1 ^ 2 * SW) / (epsilon * T.1)) +
            (29 / 2) * σ ^ 2 * B ^ 2 / g ^ 2 / T.1 := by
      have hcombine :
          (ADelta L Δ * W + (σ ^ 2 / 2) * sT.1 ^ 2 * SW) /
              (epsilon * T.1) =
            ADelta L Δ * W / (epsilon * T.1) +
              (σ ^ 2 / 2 * sT.1 ^ 2 * SW) / (epsilon * T.1) := by ring
      rw [hcombine]
      nlinarith
    calc
      _ ≤ _ := hsum
      _ ≤ _ := by
        unfold comparatorAt comparatorNumerator
        simpa [W, SW] using henlarge
  apply iSup_le
  intro I
  apply ENNReal.ofReal_le_ofReal
  have hcost17 := fixed_instance_partition_cost_le N L Δ σ H hL I T sT
    hcap hcapG hcapV hcapRB hcapJB blockCount endpoint w hcount he0 heT
    hestrict hebudget hpartition hw_nonneg hw_anti hw0
    (fun j hj => (hweight j hj).1)
  have hcost18 : FiniteInstance.cost I.1 (sT.1 / L) T ≤
      512 * comparatorAt N L Δ σ T sT + KH / T.1 +
        (29 / 2) * σ ^ 2 * influenceRowBound N ^ 2 / gainFloor N ^ 2 / T.1 +
        KN * σ ^ 2 * sT.1 ^ 2 := by
    dsimp only at hcost17
    dsimp [Qw, KH, KN, B, g, blocks] at hmain ⊢
    calc
      _ ≤ (80 * Δ * w 0 / ((sT.1 / L) * T.1) +
          58 * sT.1 * σ ^ 2 *
              (∑ j ∈ Finset.range blockCount,
                w j * ∑ t ∈ Finset.Ico (endpoint j) (endpoint (j + 1)),
                  influenceEnergy N t) / T.1) +
          (KH / T.1 + KN * σ ^ 2 * sT.1 ^ 2) := by
        convert hcost17 using 1 <;> ring
      _ ≤ (512 * comparatorAt N L Δ σ T sT +
            (29 / 2) * σ ^ 2 * influenceRowBound N ^ 2 /
              gainFloor N ^ 2 / T.1) +
          (KH / T.1 + KN * σ ^ 2 * sT.1 ^ 2) :=
        add_le_add hmain (le_refl _)
      _ = _ := by ring
  have hKN : 0 ≤ KN := by
    have hrho0 : 0 < mixingRate N := (uniform_mixing_and_influence N).1
    have hrho1 : mixingRate N < 1 := (uniform_mixing_and_influence N).2.1
    have hrhoSq : mixingRate N ^ 2 < 1 := by
      have hprod := mul_pos hrho0 (sub_pos.mpr hrho1)
      nlinarith
    have hfiltered : 0 ≤ filteredNoiseKernel N := by
      unfold filteredNoiseKernel
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)) (sq_nonneg _))
        (sub_nonneg.mpr hrhoSq.le)
    have hcurrent : 0 ≤ currentNoiseKernel N := by
      unfold currentNoiseKernel
      positivity
    have hMN : 0 ≤ controlMN N := by
      unfold controlMN
      positivity
    have hKa : 0 ≤ controlKa N := by
      unfold controlKa
      positivity
    have hKb : 0 ≤ controlKb N := by
      unfold controlKb
      positivity
    have hRN : 0 ≤ controlRN N := by
      unfold controlRN
      positivity
    have hJN : 0 ≤ controlJN N := by
      unfold controlJN
      positivity
    dsimp [KN]
    have hfirst : 0 ≤ 416 * controlRN N / gainFloor N ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hRN) (sq_nonneg _)
    exact add_nonneg hfirst (mul_nonneg (by norm_num) hJN)
  have hstepRemainder : KN * σ ^ 2 * sT.1 ^ 2 ≤
      KN * σ ^ 2 * C ^ 2 / T.1 := by
    have hscaled := mul_le_mul_of_nonneg_left hsquareUpper
      (mul_nonneg hKN (sq_nonneg σ))
    apply (le_div_iff₀ hTpos).2
    convert hscaled using 1 <;> ring
  have hnearScaled := mul_le_mul_of_nonneg_left hnear
    (by norm_num : (0 : ℝ) ≤ 512)
  have hnearTerm : 512 * comparatorAt N L Δ σ T sT ≤
      512 * comparator N L Δ σ T + 512 * ADelta L Δ / T.1 := by
    calc
      _ ≤ 512 * (comparator N L Δ σ T + ADelta L Δ / T.1) := hnearScaled
      _ = _ := by ring
  calc
    FiniteInstance.cost I.1 (sT.1 / L) T ≤
        512 * comparatorAt N L Δ σ T sT + KH / T.1 +
          (29 / 2) * σ ^ 2 * influenceRowBound N ^ 2 /
              gainFloor N ^ 2 / T.1 +
          KN * σ ^ 2 * sT.1 ^ 2 := hcost18
    _ ≤ (512 * comparator N L Δ σ T + 512 * ADelta L Δ / T.1) +
          KH / T.1 +
          (29 / 2) * σ ^ 2 * influenceRowBound N ^ 2 /
              gainFloor N ^ 2 / T.1 +
          KN * σ ^ 2 * C ^ 2 / T.1 :=
      add_le_add
        (add_le_add (add_le_add hnearTerm (le_refl _)) (le_refl _))
        hstepRemainder
    _ = 512 * comparator N L Δ σ T + K₂ / T.1 := by
      dsimp [K₂, C]
      ring

set_option maxHeartbeats 1000000

/-- Equation (60) at one fixed network and horizon.  A numerator witness
bounds the infimum with the same constant; conversely, factor-two slack turns
an infimum bound into an approximate numerator witness without attainment. -/
theorem comparator_window_budget_pointwise
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon) (C : ℝ) (hC : 0 < C) :
    ((∃ s : AdmissibleDimensionlessStepsize n,
        comparatorNumerator N L Δ σ T s ≤
          C * epsilon * σ * Real.sqrt (ADelta L Δ * T.1 / n)) →
      comparator N L Δ σ T ≤
        C * centralizedStochasticScale n L Δ σ T) ∧
    (comparator N L Δ σ T ≤
        C * centralizedStochasticScale n L Δ σ T →
      ∃ s : AdmissibleDimensionlessStepsize n,
        comparatorNumerator N L Δ σ T s ≤
          (2 * C) * epsilon * σ *
            Real.sqrt (ADelta L Δ * T.1 / n)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast N.hn
  have hT : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  have hden : 0 < epsilon * (T.1 : ℝ) :=
    mul_pos (by norm_num [epsilon]) hT
  have hscale : 0 < centralizedStochasticScale n L Δ σ T := by
    unfold centralizedStochasticScale
    exact mul_pos hσ (Real.sqrt_pos.2 (div_pos hA (mul_pos hn hT)))
  have hnormalize :
      (T.1 : ℝ) * Real.sqrt (ADelta L Δ / (n * T.1)) =
        Real.sqrt (ADelta L Δ * T.1 / n) :=
    horizon_sqrt_budget_normalization (ADelta L Δ) n T.1 hA hn hT
  have hrange_nonempty :
      (Set.range fun s : AdmissibleDimensionlessStepsize n =>
        comparatorAt N L Δ σ T s).Nonempty := by
    let s₀ : AdmissibleDimensionlessStepsize n :=
      ⟨1 / (64 * (n : ℝ)), one_div_pos.mpr (mul_pos (by norm_num) hn), le_rfl⟩
    exact ⟨comparatorAt N L Δ σ T s₀, ⟨s₀, rfl⟩⟩
  have hrange_bdd := comparatorAt_range_bddBelow N L Δ σ hL hΔ T
  constructor
  · rintro ⟨s, hs⟩
    calc
      comparator N L Δ σ T ≤ comparatorAt N L Δ σ T s := by
        unfold comparator
        exact csInf_le hrange_bdd ⟨s, rfl⟩
      _ ≤ C * centralizedStochasticScale n L Δ σ T := by
        unfold comparatorAt centralizedStochasticScale
        rw [div_le_iff₀ hden]
        calc
          comparatorNumerator N L Δ σ T s ≤
              C * epsilon * σ * Real.sqrt (ADelta L Δ * T.1 / n) := hs
          _ = (C * (σ * Real.sqrt (ADelta L Δ / (n * T.1)))) *
                (epsilon * T.1) := by
            rw [← hnormalize]
            ring
  · intro hcomparator
    have hstrict :
        comparator N L Δ σ T <
          (2 * C) * centralizedStochasticScale n L Δ σ T := by
      have hCscale : 0 < C * centralizedStochasticScale n L Δ σ T :=
        mul_pos hC hscale
      nlinarith
    have hinf_strict :
        sInf (Set.range fun s : AdmissibleDimensionlessStepsize n =>
          comparatorAt N L Δ σ T s) <
            (2 * C) * centralizedStochasticScale n L Δ σ T := by
      simpa [comparator] using hstrict
    rcases exists_lt_of_csInf_lt hrange_nonempty hinf_strict with
      ⟨y, ⟨s, rfl⟩, hs⟩
    refine ⟨s, le_of_lt ?_⟩
    unfold comparatorAt centralizedStochasticScale at hs
    rw [div_lt_iff₀ hden] at hs
    calc
      comparatorNumerator N L Δ σ T s <
          ((2 * C) * (σ * Real.sqrt (ADelta L Δ / (n * T.1)))) *
            (epsilon * T.1) := hs
      _ = (2 * C) * epsilon * σ *
            Real.sqrt (ADelta L Δ * T.1 / n) := by
        rw [← hnormalize]
        ring

/-- Equation (58) at a fixed network and horizon: a constant-factor upper
bound on the explicit comparator is exactly the corresponding effective-node
lower bound. -/
theorem comparator_effectiveNodeCount_pointwise
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon)
    (hB : 0 < comparator N L Δ σ T) (C : ℝ) (hC : 0 < C) :
    (comparator N L Δ σ T ≤
        C * centralizedStochasticScale n L Δ σ T ↔
      2 * n / C ^ 2 ≤
        effectiveNodeCount N L Δ σ ⟨T, hB⟩) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast N.hn
  have hT : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  have hrad : 0 < ADelta L Δ / ((n : ℝ) * T.1) :=
    div_pos hA (mul_pos hn hT)
  have hscale : 0 < centralizedStochasticScale n L Δ σ T := by
    unfold centralizedStochasticScale
    exact mul_pos hσ (Real.sqrt_pos.2 hrad)
  have hC2 : 0 < C ^ 2 := sq_pos_of_pos hC
  have hB2 : 0 < comparator N L Δ σ T ^ 2 := sq_pos_of_pos hB
  have hTB2 :
      0 < (T.1 : ℝ) * comparator N L Δ σ T ^ 2 :=
    mul_pos hT hB2
  have hnT : 0 < (n : ℝ) * T.1 := mul_pos hn hT
  constructor
  · intro hcompare
    have hsquares :
        comparator N L Δ σ T ^ 2 ≤
          (C * centralizedStochasticScale n L Δ σ T) ^ 2 :=
      (sq_le_sq₀ hB.le (mul_pos hC hscale).le).2 hcompare
    have hratio :
        comparator N L Δ σ T ^ 2 ≤
          (C ^ 2 * σ ^ 2 * ADelta L Δ) / ((n : ℝ) * T.1) := by
      calc
        comparator N L Δ σ T ^ 2 ≤
            (C * centralizedStochasticScale n L Δ σ T) ^ 2 := hsquares
        _ = (C ^ 2 * σ ^ 2 * ADelta L Δ) / ((n : ℝ) * T.1) := by
          unfold centralizedStochasticScale
          rw [mul_pow, mul_pow, Real.sq_sqrt hrad.le]
          ring
    have hcross :
        comparator N L Δ σ T ^ 2 * ((n : ℝ) * T.1) ≤
          C ^ 2 * σ ^ 2 * ADelta L Δ :=
      (le_div_iff₀ hnT).mp hratio
    unfold effectiveNodeCount
    rw [div_le_div_iff₀ hC2 hTB2]
    nlinarith [hcross]
  · intro heffective
    have hcross :
        (2 * (n : ℝ)) *
            ((T.1 : ℝ) * comparator N L Δ σ T ^ 2) ≤
          (2 * ADelta L Δ * σ ^ 2) * C ^ 2 := by
      unfold effectiveNodeCount at heffective
      exact (div_le_div_iff₀ hC2 hTB2).mp heffective
    have hcross' :
        comparator N L Δ σ T ^ 2 * ((n : ℝ) * T.1) ≤
          C ^ 2 * σ ^ 2 * ADelta L Δ := by
      nlinarith [hcross]
    have hratio :
        comparator N L Δ σ T ^ 2 ≤
          (C ^ 2 * σ ^ 2 * ADelta L Δ) / ((n : ℝ) * T.1) :=
      (le_div_iff₀ hnT).2 hcross'
    have hsquares :
        comparator N L Δ σ T ^ 2 ≤
          (C * centralizedStochasticScale n L Δ σ T) ^ 2 := by
      calc
        comparator N L Δ σ T ^ 2 ≤
            (C ^ 2 * σ ^ 2 * ADelta L Δ) / ((n : ℝ) * T.1) := hratio
        _ = (C * centralizedStochasticScale n L Δ σ T) ^ 2 := by
          unfold centralizedStochasticScale
          rw [mul_pow, mul_pow, Real.sq_sqrt hrad.le]
          ring
    exact (sq_le_sq₀ hB.le (mul_pos hC hscale).le).1 hsquares

/-- The localization budget also dominates the centralized benchmark used
for stepsizes outside the competing set. -/
theorem centralized_scale_le_localization_budget
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon) :
    (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
      comparatorLocalizationBudget N L Δ σ / Real.sqrt T.1 := by
  have hconst := comparator_localization_constants_pos N L Δ σ hL hΔ hσ
  have hA : 0 < ADelta L Δ := hconst.1
  have hg : 0 < gainFloor N := hconst.2.1
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hT
  have hg_le_n : gainFloor N ≤ (n : ℝ) :=
    (gainFloor_le_gain N 0).trans (gain_le_n N 0)
  have hB : 1 ≤ influenceRowBound N := by
    have hrate : 0 ≤ 1 - mixingRate N :=
      (sub_pos.mpr (sourceMixingRate_lt_one N)).le
    have hcol : 0 ≤ columnMixingConstant N := by
      unfold columnMixingConstant
      exact div_nonneg (Real.sqrt_nonneg _) (blockContraction_pos N).le
    have hD : 0 ≤ influenceOperatorBound N := by
      unfold influenceOperatorBound
      exact div_nonneg hcol hrate
    unfold influenceRowBound
    nlinarith [mul_nonneg (by positivity : 0 ≤ 1 + Real.sqrt n) hD]
  have hbase :
      σ ^ 2 / (128 * (n : ℝ)) ≤
        comparatorLocalizationBaseCost N L Δ σ := by
    unfold comparatorLocalizationBaseCost
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hn) hg]
    have hBsq : 1 ≤ influenceRowBound N ^ 2 := by nlinarith [sq_nonneg (influenceRowBound N - 1)]
    have hsig : σ ^ 2 * gainFloor N ≤ σ ^ 2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hg_le_n (sq_nonneg σ)
    nlinarith [mul_nonneg hA.le hn.le,
      mul_le_mul_of_nonneg_left hBsq (mul_nonneg (sq_nonneg σ) hn.le)]
  have hbudget :
      ADelta L Δ + σ ^ 2 / (128 * (n : ℝ)) ≤
        comparatorLocalizationBudget N L Δ σ := by
    unfold comparatorLocalizationBudget
    linarith
  have htwo := centralized_scale_le_two_term_window_bound
    N L Δ σ hL hΔ hσ T (epsilon * Real.sqrt T.1)
      (mul_pos (by norm_num [epsilon]) hsqrt)
  calc
    (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
        ADelta L Δ * (epsilon * Real.sqrt T.1) / (epsilon * T.1) +
          σ ^ 2 * epsilon /
            (128 * n * (epsilon * Real.sqrt T.1)) := htwo
    _ = (ADelta L Δ + σ ^ 2 / (128 * (n : ℝ))) /
          Real.sqrt T.1 := by
      field_simp [ne_of_gt hn, ne_of_gt hsqrt, epsilon]
      rw [Real.sq_sqrt hT.le]
      ring
    _ ≤ comparatorLocalizationBudget N L Δ σ / Real.sqrt T.1 :=
      div_le_div_of_nonneg_right hbudget hsqrt.le

/-- Equations (58)--(60), including the complete weighted-window route in
(59). Book `#/key_lemmas/6/statement_math`:
“`S_T(s)\ge K^2T/(64nW_0(s))`, `B_T(s)` has the displayed two-term lower
bound, `n_eff\le64n`”, under the three printed onset conditions. -/
theorem effective_nodes_and_speedup
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    ∃ Tonset : ℕ, ∀ T : PositiveHorizon, Tonset ≤ T.1 →
      (∀ s : AdmissibleDimensionlessStepsize n,
        IsCompetingStepsize N L Δ σ T s →
        comparatorStepLowerConstant N L Δ σ / Real.sqrt T.1 ≤ s.1 ∧
        s.1 ≤ comparatorStepUpperConstant N L Δ σ / Real.sqrt T.1 ∧
        let K := epsilon / s.1
        2 * Nat.ceil (K / gainFloor N) + 2 ≤ T.1 ∧
        16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ T.1 ∧
        4 * epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4 ≤
          Real.sqrt T.1 ∧
        0 < windowLength N T.1 0 s.1 ∧
        K ^ 2 * T.1 /
                (64 * n * windowLength N T.1 0 s.1) ≤
          windowInfluenceSum N T.1 s.1 ∧
        ADelta L Δ * windowLength N T.1 0 s.1 /
                  (epsilon * T.1) +
                σ ^ 2 * epsilon /
                  (128 * n * windowLength N T.1 0 s.1) ≤
          comparatorAt N L Δ σ T s ∧
        (1 / (4 * Real.sqrt 2)) *
                centralizedStochasticScale n L Δ σ T ≤
          comparatorAt N L Δ σ T s) ∧
      0 < comparator N L Δ σ T ∧
      (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
        comparator N L Δ σ T ∧
      ∀ hB : 0 < comparator N L Δ σ T,
        let Tp : PositiveComparatorHorizon N L Δ σ := ⟨T, hB⟩
        effectiveNodeCount N L Δ σ Tp ≤ 64 * n ∧
        ∀ C : ℝ, 0 < C →
          (comparator N L Δ σ T ≤ C * centralizedStochasticScale n L Δ σ T ↔
            2 * n / C ^ 2 ≤ effectiveNodeCount N L Δ σ Tp) ∧
          ((∃ s : AdmissibleDimensionlessStepsize n,
              comparatorNumerator N L Δ σ T s ≤
                C * epsilon * σ * Real.sqrt (ADelta L Δ * T.1 / n)) →
            comparator N L Δ σ T ≤ C * centralizedStochasticScale n L Δ σ T) ∧
          (comparator N L Δ σ T < C * centralizedStochasticScale n L Δ σ T →
            ∃ s : AdmissibleDimensionlessStepsize n,
              comparatorNumerator N L Δ σ T s <
                C * epsilon * σ * Real.sqrt (ADelta L Δ * T.1 / n)) := by
  let R : ℝ := max 1 (max
    (2 * epsilon * comparatorLocalizationBudget N L Δ σ / ADelta L Δ)
    (4 * epsilon /
      (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4))
  let Troot : ℕ := max 1 (Nat.ceil (R ^ 2))
  let Tcob : ℕ := max 1 (Nat.ceil
    (16 * Real.sqrt n * coboundaryBound N / gainFloor N))
  let Tonset : ℕ := max Troot
    (max (2 * influenceEnergyWindowThreshold N) Tcob)
  refine ⟨Tonset, ?_⟩
  intro T hTonset
  have hconst := comparator_localization_constants_pos N L Δ σ hL hΔ hσ
  have hA : 0 < ADelta L Δ := hconst.1
  have hg : 0 < gainFloor N := hconst.2.1
  have hM : 0 < comparatorLocalizationBudget N L Δ σ := hconst.2.2.2.1
  have hc : 0 < comparatorStepLowerConstant N L Δ σ :=
    hconst.2.2.2.2.1
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hT
  have hsqrt_sq : (Real.sqrt T.1) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hT.le
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact (le_max_left 1 _).trans' (by norm_num)
  have hTroot : Troot ≤ T.1 := by
    dsimp [Tonset] at hTonset
    omega
  have hR2root : R ^ 2 ≤ (Troot : ℝ) := by
    dsimp [Troot]
    exact le_positive_ceil_max_one (R ^ 2)
  have hrootT : (Troot : ℝ) ≤ (T.1 : ℝ) := by exact_mod_cast hTroot
  have hRle : R ≤ Real.sqrt T.1 := by
    apply (sq_le_sq₀ hRnonneg hsqrt.le).1
    rw [hsqrt_sq]
    exact hR2root.trans hrootT
  have hsignalOnset :
      2 * epsilon * comparatorLocalizationBudget N L Δ σ / ADelta L Δ ≤
        Real.sqrt T.1 := by
    exact (le_max_left _ _).trans ((le_max_right 1 _).trans hRle)
  have hsqrtBudget :
      4 * epsilon /
          (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4 ≤
        Real.sqrt T.1 := by
    exact (le_max_right _ _).trans ((le_max_right 1 _).trans hRle)
  have henergyOnset : 2 * influenceEnergyWindowThreshold N ≤ T.1 := by
    dsimp [Tonset] at hTonset
    omega
  have hTcob : Tcob ≤ T.1 := by
    dsimp [Tonset] at hTonset
    omega
  have hcob :
      16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ (T.1 : ℝ) := by
    have hle :
        16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ (Tcob : ℝ) := by
      dsimp [Tcob]
      exact le_positive_ceil_max_one _
    exact hle.trans (by exact_mod_cast hTcob)
  have hlocal (s : AdmissibleDimensionlessStepsize n)
      (hcomp : IsCompetingStepsize N L Δ σ T s) :=
    competingStepsize_localization_of_horizon N L Δ σ hL hΔ hσ T
      hsignalOnset henergyOnset s hcomp
  have hcompeting : ∀ s : AdmissibleDimensionlessStepsize n,
      IsCompetingStepsize N L Δ σ T s →
      comparatorStepLowerConstant N L Δ σ / Real.sqrt T.1 ≤ s.1 ∧
      s.1 ≤ comparatorStepUpperConstant N L Δ σ / Real.sqrt T.1 ∧
      let K := epsilon / s.1
      2 * Nat.ceil (K / gainFloor N) + 2 ≤ T.1 ∧
      16 * Real.sqrt n * coboundaryBound N / gainFloor N ≤ T.1 ∧
      4 * epsilon /
              (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4 ≤
        Real.sqrt T.1 ∧
      0 < windowLength N T.1 0 s.1 ∧
      K ^ 2 * T.1 / (64 * n * windowLength N T.1 0 s.1) ≤
        windowInfluenceSum N T.1 s.1 ∧
      ADelta L Δ * windowLength N T.1 0 s.1 / (epsilon * T.1) +
          σ ^ 2 * epsilon / (128 * n * windowLength N T.1 0 s.1) ≤
        comparatorAt N L Δ σ T s ∧
      (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
        comparatorAt N L Δ σ T s := by
    intro s hcomp
    have hloc := hlocal s hcomp
    let K : ℝ := epsilon / s.1
    have hs : 0 < s.1 := s.2.1
    have hKnonneg : 0 ≤ K / gainFloor N := by
      dsimp [K]
      exact div_nonneg (div_nonneg (by norm_num [epsilon]) hs.le) hg.le
    have hKbound :
        K / gainFloor N ≤
          (epsilon / (gainFloor N * comparatorStepLowerConstant N L Δ σ)) *
            Real.sqrt T.1 := by
      dsimp [K]
      field_simp [ne_of_gt hs, ne_of_gt hg, ne_of_gt hc, ne_of_gt hsqrt] at hloc ⊢
      nlinarith [show 0 < epsilon by norm_num [epsilon]]
    have hceil_lt := Nat.ceil_lt_add_one hKnonneg
    have hceilReal :
        (2 * Nat.ceil (K / gainFloor N) + 2 : ℕ) ≤ T.1 := by
      have hmul := mul_le_mul_of_nonneg_right hsqrtBudget hsqrt.le
      have ha :
          0 ≤ epsilon / (gainFloor N * comparatorStepLowerConstant N L Δ σ) := by
        exact div_nonneg (by norm_num [epsilon]) (mul_nonneg hg.le hc.le)
      have hr4 : 4 ≤ Real.sqrt T.1 := by
        have hfour :
            4 ≤ 4 * epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4 := by
          calc
            (4 : ℝ) ≤ 4 * (epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ)) + 4 := by
              nlinarith
            _ = 4 * epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4 := by ring
        exact hfour.trans hsqrtBudget
      have hcast :
          ((2 * Nat.ceil (K / gainFloor N) + 2 : ℕ) : ℝ) ≤ (T.1 : ℝ) := by
        push_cast
        have har :
            0 ≤ (epsilon /
              (gainFloor N * comparatorStepLowerConstant N L Δ σ)) *
                Real.sqrt T.1 := mul_nonneg ha hsqrt.le
        have hstep :
            2 * (Nat.ceil (K / gainFloor N) : ℝ) + 2 <
              2 * (epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) *
                  Real.sqrt T.1) + 4 := by
          nlinarith [hKbound, hceil_lt]
        have hmid :
            2 * (epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) *
                  Real.sqrt T.1) + 4 ≤
              (4 * epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4) *
                  Real.sqrt T.1 := by
          have hfourr : (4 : ℝ) ≤ 4 * Real.sqrt T.1 := by nlinarith
          have htwoar :
              0 ≤ 2 * (epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) *
                  Real.sqrt T.1) := by nlinarith
          ring_nf at har htwoar hfourr ⊢
          nlinarith
        calc
          2 * (Nat.ceil (K / gainFloor N) : ℝ) + 2 ≤
              2 * (epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) *
                  Real.sqrt T.1) + 4 := hstep.le
          _ ≤ (4 * epsilon /
                (gainFloor N * comparatorStepLowerConstant N L Δ σ) + 4) *
                  Real.sqrt T.1 := hmid
          _ ≤ Real.sqrt T.1 * Real.sqrt T.1 := hmul
          _ = (T.1 : ℝ) := by nlinarith [hsqrt_sq]
      exact_mod_cast hcast
    have hw := comparator_lower_from_weighted_window
      N L Δ σ hL hΔ hσ T s hceilReal hcob
    refine ⟨hloc.1, hloc.2, ?_⟩
    dsimp [K]
    exact ⟨hceilReal, hcob, hsqrtBudget, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2⟩
  have hinitial := comparator_initial_window_lower_bound N L Δ σ hL hΔ T
  have hpositive : 0 < comparator N L Δ σ T := by
    have : 0 < ADelta L Δ / (epsilon * (T.1 : ℝ)) :=
      div_pos hA (mul_pos (by norm_num [epsilon]) hT)
    exact this.trans_le hinitial
  have hrange_nonempty :
      (Set.range fun s : AdmissibleDimensionlessStepsize n =>
        comparatorAt N L Δ σ T s).Nonempty := by
    let s₀ : AdmissibleDimensionlessStepsize n :=
      ⟨1 / (64 * (n : ℝ)), one_div_pos.mpr (mul_pos (by norm_num) hn), le_rfl⟩
    exact ⟨comparatorAt N L Δ σ T s₀, ⟨s₀, rfl⟩⟩
  have hpoint (s : AdmissibleDimensionlessStepsize n) :
      (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
        comparatorAt N L Δ σ T s := by
    by_cases hscomp : IsCompetingStepsize N L Δ σ T s
    · exact (hcompeting s hscomp).2.2.2.2.2.2.2.2
    · exact (centralized_scale_le_localization_budget N L Δ σ
        hL hΔ hσ T).trans (le_of_lt (lt_of_not_ge hscomp))
  have hcentral :
      (1 / (4 * Real.sqrt 2)) * centralizedStochasticScale n L Δ σ T ≤
        comparator N L Δ σ T := by
    unfold comparator
    apply le_csInf hrange_nonempty
    rintro y ⟨s, rfl⟩
    exact hpoint s
  refine ⟨hcompeting, hpositive, hcentral, ?_⟩
  intro hB
  dsimp
  have hrad : 0 ≤ ADelta L Δ / ((n : ℝ) * T.1) := by positivity
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have heffective :
      effectiveNodeCount N L Δ σ ⟨T, hB⟩ ≤ 64 * (n : ℝ) := by
    have hsquares := (sq_le_sq₀
      (mul_nonneg (by positivity) (by unfold centralizedStochasticScale; positivity))
      hB.le).2 hcentral
    unfold centralizedStochasticScale at hsquares
    change 2 * ADelta L Δ * σ ^ 2 /
      ((T.1 : ℝ) * comparator N L Δ σ T ^ 2) ≤ 64 * (n : ℝ)
    rw [mul_pow, mul_pow, Real.sq_sqrt hrad] at hsquares
    field_simp [ne_of_gt hn, ne_of_gt hT, ne_of_gt hB, ne_of_gt hsqrt2] at hsquares ⊢
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsquares
    nlinarith
  refine ⟨heffective, ?_⟩
  intro C hC
  refine ⟨comparator_effectiveNodeCount_pointwise N L Δ σ
    hL hΔ hσ T hB C hC, ?_⟩
  constructor
  · exact (comparator_window_budget_pointwise N L Δ σ hL hΔ hσ T C hC).1
  · intro hstrict
    have hrange_bdd := comparatorAt_range_bddBelow N L Δ σ hL hΔ T
    have hinf :
        sInf (Set.range fun s : AdmissibleDimensionlessStepsize n =>
          comparatorAt N L Δ σ T s) <
          C * centralizedStochasticScale n L Δ σ T := by
      simpa [comparator] using hstrict
    rcases exists_lt_of_csInf_lt hrange_nonempty hinf with ⟨y, ⟨s, rfl⟩, hsAt⟩
    refine ⟨s, ?_⟩
    have hden : 0 < epsilon * (T.1 : ℝ) :=
      mul_pos (by norm_num [epsilon]) hT
    have hnorm := horizon_sqrt_budget_normalization
      (ADelta L Δ) n T.1 hA hn hT
    unfold comparatorAt centralizedStochasticScale at hsAt
    rw [div_lt_iff₀ hden] at hsAt
    calc
      comparatorNumerator N L Δ σ T s <
          (C * (σ * Real.sqrt (ADelta L Δ / (n * T.1)))) *
            (epsilon * T.1) := hsAt
      _ = C * epsilon * σ * Real.sqrt (ADelta L Δ * T.1 / n) := by
        rw [← hnorm]
        ring

/-- A squared onset turns an inverse-horizon transient into an
inverse-square-root transient.  This is the scalar absorption in (57). -/
theorem inverse_horizon_absorption_from_sqrt_lower
    {K β t : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) (ht : 0 < t)
    (hsq : (K / β) ^ 2 ≤ t) :
    K / t ≤ β / Real.sqrt t := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hratio : 0 ≤ K / β := div_nonneg hK hβ.le
  have hratio_le : K / β ≤ Real.sqrt t := by
    apply (sq_le_sq₀ hratio hsqrt.le).1
    simpa [Real.sq_sqrt ht.le] using hsq
  rw [div_le_iff₀ ht]
  calc
    K ≤ Real.sqrt t * β := (div_le_iff₀ hβ).1 hratio_le
    _ = β / Real.sqrt t * t := by
      field_simp [ne_of_gt hsqrt]
      nlinarith [Real.sq_sqrt ht.le]

/-- Main theorem (8), with the same class in the upper and lower bounds and
all sufficiently large integer horizons. `K₂` is independent of `T`, instance,
and dimension; `Tstar` and `Tzero` are chosen after the fixed network/scales. -/
theorem main_matching_bound
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    ∃ Tstar : ℕ, ∀ H : ℝ, 0 ≤ H → ∃ K₂ : ℝ, ∃ Tzero : ℕ,
      (∀ T : PositiveHorizon, Tstar ≤ T.1 →
        ENNReal.ofReal (comparator N L Δ σ T / 6400) ≤
          minimaxRisk (fixedInstanceClass N L Δ σ H) T ∧
        minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
          ENNReal.ofReal (512 * comparator N L Δ σ T + K₂ / T.1)) ∧
      (∀ T : PositiveHorizon, Tzero ≤ T.1 →
        ENNReal.ofReal (comparator N L Δ σ T / 6400) ≤
          minimaxRisk (fixedInstanceClass N L Δ σ H) T ∧
        minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
          ENNReal.ofReal (1024 * comparator N L Δ σ T)) := by
  obtain ⟨Tminus, hminus⟩ :=
    actual_quadratic_response_all_stepsizes N L Δ σ hL hΔ hσ
  obtain ⟨Tplus, hplus⟩ := block_window_upper_bound N L Δ σ hL hΔ hσ
  obtain ⟨Tonset, heffective⟩ := effective_nodes_and_speedup N L Δ σ hL hΔ hσ
  let Tstar : ℕ := max Tminus Tplus
  refine ⟨Tstar, ?_⟩
  intro H hH
  obtain ⟨Kraw, hupper⟩ := hplus H hH
  let K₂ : ℝ := max Kraw 0
  have hK₂ : 0 ≤ K₂ := by
    dsimp [K₂]
    exact le_max_right _ _
  have hKraw : Kraw ≤ K₂ := by
    dsimp [K₂]
    exact le_max_left _ _
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  let β : ℝ :=
    (1 / (4 * Real.sqrt 2)) * σ * Real.sqrt (ADelta L Δ / n)
  have hβ : 0 < β := by
    dsimp [β]
    positivity
  let Tabs : ℕ := max 1 (Nat.ceil ((K₂ / (512 * β)) ^ 2))
  let Tzero : ℕ := max Tstar (max Tonset Tabs)
  refine ⟨K₂, Tzero, ?_, ?_⟩
  · intro T hTstar
    have hminusT : Tminus ≤ T.1 := by
      dsimp [Tstar] at hTstar
      omega
    have hplusT : Tplus ≤ T.1 := by
      dsimp [Tstar] at hTstar
      omega
    constructor
    · unfold minimaxRisk
      apply le_iInf
      intro α
      obtain ⟨I, hIC, hI⟩ := hminus H hH T hminusT α.1 α.2
      exact le_iSup_of_le ⟨I, hIC⟩ hI
    · obtain ⟨sT, _, _, hsT⟩ := hupper T hplusT
      have hselected :
          minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
            ENNReal.ofReal
              (512 * comparator N L Δ σ T + Kraw / T.1) := by
        unfold minimaxRisk
        exact iInf_le_of_le
          ⟨sT.1 / L, div_pos sT.2.1 hL⟩ hsT
      refine hselected.trans (ENNReal.ofReal_le_ofReal ?_)
      have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
      have hdiv : Kraw / (T.1 : ℝ) ≤ K₂ / T.1 :=
        div_le_div_of_nonneg_right hKraw hT.le
      linarith
  · intro T hTzero
    have hTstar : Tstar ≤ T.1 := by
      dsimp [Tzero] at hTzero
      omega
    have hTonset : Tonset ≤ T.1 := by
      dsimp [Tzero] at hTzero
      omega
    have hTabs : Tabs ≤ T.1 := by
      dsimp [Tzero] at hTzero
      omega
    have hminusT : Tminus ≤ T.1 := by
      dsimp [Tstar] at hTstar
      omega
    have hplusT : Tplus ≤ T.1 := by
      dsimp [Tstar] at hTstar
      omega
    constructor
    · unfold minimaxRisk
      apply le_iInf
      intro α
      obtain ⟨I, hIC, hI⟩ := hminus H hH T hminusT α.1 α.2
      exact le_iSup_of_le ⟨I, hIC⟩ hI
    · obtain ⟨sT, _, _, hsT⟩ := hupper T hplusT
      have hselected :
          minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
            ENNReal.ofReal
              (512 * comparator N L Δ σ T + Kraw / T.1) := by
        unfold minimaxRisk
        exact iInf_le_of_le
          ⟨sT.1 / L, div_pos sT.2.1 hL⟩ hsT
      have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
      have hdiv : Kraw / (T.1 : ℝ) ≤ K₂ / T.1 :=
        div_le_div_of_nonneg_right hKraw hT.le
      have hselected₂ :
          minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
            ENNReal.ofReal
              (512 * comparator N L Δ σ T + K₂ / T.1) := by
        refine hselected.trans (ENNReal.ofReal_le_ofReal ?_)
        linarith
      have hcentral := (heffective T hTonset).2.2.1
      have hscale :
          β / Real.sqrt T.1 ≤ comparator N L Δ σ T := by
        calc
          β / Real.sqrt T.1 =
              (1 / (4 * Real.sqrt 2)) *
                centralizedStochasticScale n L Δ σ T := by
            calc
              β / Real.sqrt T.1 =
                  (1 / (4 * Real.sqrt 2)) * σ *
                    (Real.sqrt (ADelta L Δ / n) / Real.sqrt T.1) := by
                dsimp [β]
                ring
              _ = (1 / (4 * Real.sqrt 2)) * σ *
                    Real.sqrt ((ADelta L Δ / n) / T.1) := by
                rw [Real.sqrt_div (div_nonneg hA.le hn.le) (T.1 : ℝ)]
              _ = (1 / (4 * Real.sqrt 2)) *
                    centralizedStochasticScale n L Δ σ T := by
                unfold centralizedStochasticScale
                rw [show (ADelta L Δ / (n : ℝ)) / T.1 =
                    ADelta L Δ / ((n : ℝ) * T.1) by ring]
                ring
          _ ≤ comparator N L Δ σ T := hcentral
      have hsqTabs : (K₂ / (512 * β)) ^ 2 ≤ (Tabs : ℝ) := by
        dsimp [Tabs]
        exact le_positive_ceil_max_one _
      have hTabsT : (Tabs : ℝ) ≤ (T.1 : ℝ) := by
        exact_mod_cast hTabs
      have habsorb :
          K₂ / (T.1 : ℝ) ≤
            (512 * β) / Real.sqrt T.1 :=
        inverse_horizon_absorption_from_sqrt_lower hK₂
          (mul_pos (by norm_num) hβ) hT (hsqTabs.trans hTabsT)
      have habsorbComp :
          K₂ / (T.1 : ℝ) ≤ 512 * comparator N L Δ σ T := by
        calc
          K₂ / (T.1 : ℝ) ≤
              (512 * β) / Real.sqrt T.1 := habsorb
          _ = 512 * (β / Real.sqrt T.1) := by ring
          _ ≤ 512 * comparator N L Δ σ T :=
            mul_le_mul_of_nonneg_left hscale (by norm_num)
      refine hselected₂.trans (ENNReal.ofReal_le_ofReal ?_)
      linarith

/-- Family version of (60).  `hmatch` records the source warning that a
finite constant for each fixed network does not provide a uniform family
onset; equations (55) and (57) must hold uniformly.
Book `#/key_lemmas/6/statement_math`:
“对 `n` 或网络变化的家族，`c`、`C` 必须统一”. -/
theorem effective_nodes_family_qualification
    (F : Set (NetworkSetup n)) (L Δ σ H : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hH : 0 ≤ H)
    (hmatch : UniformMatchingOnset F L Δ σ H) :
    UniformCentralizedComparator F L Δ σ ↔
      UniformWindowSpeedupCriterion F L Δ σ := by
  constructor
  · rintro ⟨C, hC, Tonset, hcentral⟩
    refine ⟨2 * C, by linarith, Tonset, ?_⟩
    intro N hNF T hTonset
    exact (comparator_window_budget_pointwise N L Δ σ hL hΔ hσ T C hC).2
      (hcentral N hNF T hTonset)
  · rintro ⟨C, hC, Tonset, hwindow⟩
    refine ⟨C, hC, Tonset, ?_⟩
    intro N hNF T hTonset
    exact (comparator_window_budget_pointwise N L Δ σ hL hΔ hσ T C hC).1
      (hwindow N hNF T hTonset)

/-! ### Families with varying node counts

The fixed-`n` predicates above are useful companions, but the qualification
following (60) also ranges over families in which `n` itself varies.  The
dependent member below keeps each network together with its own node count and
problem scales, so none of those data can be projected into one ambient
`NetworkSetup n`.
-/

/-- One member of the source's varying-`n` or varying-network family.  The
positive stochastic regime and finite heterogeneity layer are part of each
member's paper data, not theorem-local calibration assumptions.
Book `#/key_lemmas/6/statement_math`:
“对 `n` 或网络变化的家族，`c`、`C` 必须统一”. -/
structure VaryingNetworkFamilyMember where
  nodeCount : ℕ
  network : NetworkSetup nodeCount
  lipschitz : {L : ℝ // 0 < L}
  gap : {Δ : ℝ // 0 < Δ}
  noiseScale : {σ : ℝ // 0 < σ}
  heterogeneityScale : {H : ℝ // 0 ≤ H}

/-- Uniform equation-(8) matching and additive-to-absorbed transition for a
family whose node counts, networks, and problem scales may all vary.  `K₂`,
`Tstar`, and `Tzero` are outside the member quantifier, expressing the source's
uniform transient and onset requirement.
Book `#/key_lemmas/6/statement_math`:
“也可用加法版本直接要求 `K_2/T` 相对集中式尺度一致可控。单个固定网络的有限常数不自动给出家族上的统一起效时间”. -/
def VaryingUniformMatchingOnset
    (F : Set VaryingNetworkFamilyMember) : Prop :=
  ∃ K₂ : ℝ, ∃ Tstar Tzero : ℕ, ∀ M ∈ F,
    (∀ T : PositiveHorizon, Tstar ≤ T.1 →
      ENNReal.ofReal
          (comparator M.network M.lipschitz.1 M.gap.1 M.noiseScale.1 T / 6400) ≤
        minimaxRisk
          (fixedInstanceClass M.network M.lipschitz.1 M.gap.1
            M.noiseScale.1 M.heterogeneityScale.1) T ∧
      minimaxRisk
          (fixedInstanceClass M.network M.lipschitz.1 M.gap.1
            M.noiseScale.1 M.heterogeneityScale.1) T ≤
        ENNReal.ofReal
          (512 * comparator M.network M.lipschitz.1 M.gap.1 M.noiseScale.1 T +
            K₂ / T.1)) ∧
    (∀ T : PositiveHorizon, Tzero ≤ T.1 →
      minimaxRisk
          (fixedInstanceClass M.network M.lipschitz.1 M.gap.1
            M.noiseScale.1 M.heterogeneityScale.1) T ≤
        ENNReal.ofReal
          (1024 * comparator M.network M.lipschitz.1 M.gap.1 M.noiseScale.1 T))

/-- A single comparison constant and onset certify centralized scaling for
every observed member, including when its node count differs from the others.
Book `#/key_lemmas/6/statement_math`:
“`B_T=O(\sigma\sqrt{L\Delta/(nT)})` ... 对 `n` 或网络变化的家族，`c`、`C` 必须统一”. -/
def VaryingUniformCentralizedComparator
    (F : Set VaryingNetworkFamilyMember) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Tonset : ℕ, ∀ M ∈ F,
    ∀ T : PositiveHorizon, Tonset ≤ T.1 →
      comparator M.network M.lipschitz.1 M.gap.1 M.noiseScale.1 T ≤
        C * centralizedStochasticScale M.nodeCount M.lipschitz.1 M.gap.1
          M.noiseScale.1 T

/-- The family-uniform effective-node formulation of (58)--(60).  Positivity
of each observed comparator is asserted as the derived domain certificate
needed to form its canonical `effectiveNodeCount`; it is not an extra input.
Book `#/key_lemmas/6/statement_math`:
“`n_{\rm eff}\ge c n` ... 对 `n` 或网络变化的家族，`c`、`C` 必须统一”. -/
def VaryingUniformEffectiveNodeScaling
    (F : Set VaryingNetworkFamilyMember) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ Tonset : ℕ, ∀ M ∈ F,
    ∀ T : PositiveHorizon, Tonset ≤ T.1 →
      ∃ hB : 0 < comparator M.network M.lipschitz.1 M.gap.1 M.noiseScale.1 T,
        c * M.nodeCount ≤
          effectiveNodeCount M.network M.lipschitz.1 M.gap.1 M.noiseScale.1
            ⟨T, hB⟩

/-- Equation (60) with one comparison constant and one onset outside the
dependent family quantifier.
Book `#/key_lemmas/6/statement_math`:
“存在 `s` 使 `A_\Delta W_0(s)+(\sigma^2/2)s^2S_T(s)\le C\epsilon\sigma\sqrt{A_\Delta T/n}`”. -/
def VaryingUniformWindowSpeedupCriterion
    (F : Set VaryingNetworkFamilyMember) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Tonset : ℕ, ∀ M ∈ F,
    ∀ T : PositiveHorizon, Tonset ≤ T.1 →
      ∃ s : AdmissibleDimensionlessStepsize M.nodeCount,
        comparatorNumerator M.network M.lipschitz.1 M.gap.1 M.noiseScale.1 T s ≤
          C * epsilon * M.noiseScale.1 *
            Real.sqrt (ADelta M.lipschitz.1 M.gap.1 * T.1 / M.nodeCount)

/-- Source-facing varying-node-count family qualification following (60).
The matching premise supplies common control of the equation-(55)/(57)
transients; the conclusion states all three uniformly quantified formulations.
Book `#/key_lemmas/6/statement_math`:
“`B_T=O(\sigma\sqrt{L\Delta/(nT)})` ... 等价于 `n_{\rm eff}\ge c n` ... 未优化形式是存在 `s` ... 对 `n` 或网络变化的家族，`c`、`C` 必须统一，并且必须在每个观察时域核查 (55)、(57) 等门槛”. -/
theorem varying_nodes_effective_nodes_family_qualification
    (F : Set VaryingNetworkFamilyMember)
    (hmatch : VaryingUniformMatchingOnset F) :
    VaryingUniformCentralizedComparator F ↔
      VaryingUniformEffectiveNodeScaling F ∧
        VaryingUniformWindowSpeedupCriterion F := by
  constructor
  · rintro ⟨C, hC, Tonset, hcentral⟩
    constructor
    · refine ⟨2 / C ^ 2, div_pos (by norm_num) (sq_pos_of_pos hC),
          Tonset, ?_⟩
      intro M hMF T hTonset
      have hA : 0 < ADelta M.lipschitz.1 M.gap.1 := by
        unfold ADelta
        exact mul_pos M.lipschitz.property M.gap.property
      have hT : (0 : ℝ) < T.1 := by exact_mod_cast T.2
      have hbase :
          0 < ADelta M.lipschitz.1 M.gap.1 / (epsilon * T.1) :=
        div_pos hA (mul_pos (by norm_num [epsilon]) hT)
      have hB :
          0 < comparator M.network M.lipschitz.1 M.gap.1
            M.noiseScale.1 T :=
        lt_of_lt_of_le hbase
          (comparator_initial_window_lower_bound M.network
            M.lipschitz.1 M.gap.1 M.noiseScale.1
            M.lipschitz.property M.gap.property T)
      refine ⟨hB, ?_⟩
      have heffective :=
        (comparator_effectiveNodeCount_pointwise M.network
          M.lipschitz.1 M.gap.1 M.noiseScale.1
          M.lipschitz.property M.gap.property M.noiseScale.property
          T hB C hC).1 (hcentral M hMF T hTonset)
      convert heffective using 1 <;> ring
    · refine ⟨2 * C, mul_pos (by norm_num) hC, Tonset, ?_⟩
      intro M hMF T hTonset
      exact (comparator_window_budget_pointwise M.network
        M.lipschitz.1 M.gap.1 M.noiseScale.1
        M.lipschitz.property M.gap.property M.noiseScale.property
        T C hC).2 (hcentral M hMF T hTonset)
  · rintro ⟨⟨c, hc, Tonset, heffective⟩, hwindow⟩
    let C : ℝ := Real.sqrt (2 / c)
    have hratio : 0 < (2 : ℝ) / c := div_pos (by norm_num) hc
    have hC : 0 < C := by
      dsimp [C]
      exact Real.sqrt_pos.2 hratio
    have hCsq : C ^ 2 = (2 : ℝ) / c := by
      dsimp [C]
      exact Real.sq_sqrt hratio.le
    refine ⟨C, hC, Tonset, ?_⟩
    intro M hMF T hTonset
    rcases heffective M hMF T hTonset with ⟨hB, hneffective⟩
    apply (comparator_effectiveNodeCount_pointwise M.network
      M.lipschitz.1 M.gap.1 M.noiseScale.1
      M.lipschitz.property M.gap.property M.noiseScale.property
      T hB C hC).2
    calc
      2 * M.nodeCount / C ^ 2 = c * M.nodeCount := by
        rw [hCsq]
        field_simp [ne_of_gt hc]
      _ ≤ effectiveNodeCount M.network M.lipschitz.1 M.gap.1
          M.noiseScale.1 ⟨T, hB⟩ := hneffective

/-- Rows are doubly stochastic at every time; the column schedule remains the
general source-admissible one and need not be periodic. -/
def IsDoublyStochasticRow (N : NetworkSetup n) : Prop :=
  ∀ t, N.rowMix t ∈ Matrix.colStochastic ℝ (Fin n)

/-- Double stochasticity of the row schedule collapses all five network
quantities in the specialization following (60). -/
theorem uniform_network_quantities_of_doubly_stochastic_row
    (N : NetworkSetup n) (hds : IsDoublyStochasticRow N) :
    (∀ t, absoluteProbability N t = uniformRow n) ∧
    (∀ t (z : ZeroSumNodeVector n), influenceOperator N t z = 0) ∧
    (∀ t, gain N t = 1) ∧
    (∀ t, influenceRow N t = uniformRow n) ∧
    (∀ t, influenceEnergy N t = 1 / n) := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hrowProduct (k j : ℕ) :
      FiniteNetwork.consecutiveProduct N.rowMix k j ∈
        Matrix.colStochastic ℝ (Fin n) := by
    induction j with
    | zero => exact (Matrix.colStochastic ℝ (Fin n)).one_mem
    | succ j ih =>
        rw [FiniteNetwork.consecutiveProduct_succ]
        exact (Matrix.colStochastic ℝ (Fin n)).mul_mem (hds (k + j)) ih
  have hcolProduct (k j : ℕ) :
      FiniteNetwork.consecutiveProduct N.colMix k j ∈
        Matrix.colStochastic ℝ (Fin n) := by
    induction j with
    | zero => exact (Matrix.colStochastic ℝ (Fin n)).one_mem
    | succ j ih =>
        rw [FiniteNetwork.consecutiveProduct_succ]
        exact (Matrix.colStochastic ℝ (Fin n)).mul_mem
          (N.col_stochastic (k + j)) ih
  have huniform_vecMul (A : NetworkMatrix n)
      (hA : A ∈ Matrix.colStochastic ℝ (Fin n)) :
      uniformRow n ᵥ* A = uniformRow n := by
    funext i
    simp only [uniformRow, Matrix.vecMul, dotProduct]
    rw [← Finset.mul_sum]
    rw [Matrix.sum_col_of_mem_colStochastic hA i]
    simp
  have hpi : ∀ t, absoluteProbability N t = uniformRow n := by
    intro t
    have hconstant :
        Filter.Tendsto
          (fun q => uniformRow n ᵥ* forwardProduct N.rowMix q t)
          Filter.atTop (nhds (uniformRow n)) := by
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall fun q => by
        unfold forwardProduct
        exact (huniform_vecMul _ (hrowProduct t (q - t))).symm
    exact tendsto_nhds_unique (absoluteProbability_tendsto N t) hconstant
  have hseries_zero : ∀ t (z : ZeroSumNodeVector n) ℓ,
      influenceSeriesTerm N t ℓ z = 0 := by
    intro t z ℓ
    simp only [influenceSeriesTerm,
      FiniteNetwork.periodicCorrectedLiftSeriesTerm_def, hpi]
    rw [show (∑ i : Fin n,
        (uniformRow n i) •
          Matrix.smulVec
            (FiniteNetwork.consecutiveProduct N.colMix t ℓ) z.1 i) =
        (n : ℝ)⁻¹ *
          ∑ i : Fin n,
            Matrix.smulVec
              (FiniteNetwork.consecutiveProduct N.colMix t ℓ) z.1 i by
      simp [uniformRow, Finset.mul_sum]]
    rw [Matrix.sum_smulVec_of_mem_colStochastic z.1 (hcolProduct t ℓ), z.2]
    ring
  have hD : ∀ t (z : ZeroSumNodeVector n),
      influenceOperator N t z = 0 := by
    intro t z
    exact HasSum.unique (influenceOperator_hasSum N t z)
      (by simpa [hseries_zero t z] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0))
  have hgain : ∀ t, gain N t = 1 := by
    intro t
    unfold gain dotProduct
    rw [hpi]
    simp only [uniformRow, ← Finset.mul_sum]
    have hmass : ∑ i, pushMass N t i = (n : ℝ) := by
      have hnorm := normalizedPushMass_sum_eq_one N t
      simp only [normalizedPushMass, ← Finset.mul_sum] at hnorm
      field_simp [ne_of_gt hn] at hnorm ⊢
      exact hnorm
    rw [hmass]
    field_simp
  have hb : ∀ t, influenceRow N t = uniformRow n := by
    intro t
    funext i
    simp [influenceRow, hpi, hD]
  have hq : ∀ t, influenceEnergy N t = 1 / n := by
    intro t
    unfold influenceEnergy
    rw [hb]
    simp [uniformRow, ne_of_gt hn]
    field_simp
  exact ⟨hpi, hD, hgain, hb, hq⟩

/-- With unit gain, the nested finite supremum defining a window is exactly
the smaller of the remaining horizon and the scalar budget floor. -/
theorem window_length_eq_min_floor_of_gain_eq_one
    (N : NetworkSetup n) (hgain : ∀ t, gain N t = 1)
    (T r : ℕ) (s : AdmissibleDimensionlessStepsize n) :
    windowLength N T r s.1 =
      min (T - r) (Nat.floor (epsilon / s.1)) := by
  classical
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast N.hn
  have hs : 0 < s.1 := s.2.1
  have hs_le : s.1 ≤ 1 / 64 := by
    calc
      s.1 ≤ 1 / (64 * (n : ℝ)) := s.2.2
      _ ≤ 1 / 64 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  let m : ℕ := Nat.floor (epsilon / s.1)
  have hmpos : 0 < m := by
    dsimp [m]
    apply Nat.floor_pos.mpr
    rw [one_le_div hs]
    norm_num [epsilon] at hs_le ⊢
    linarith
  unfold windowLength
  by_cases hrT : r < T
  · rw [if_pos hrT]
    apply le_antisymm
    · apply Finset.sup_le
      intro P hP
      apply Finset.sup_le
      intro Q hQ
      split_ifs with hbudget
      · have hPt : r ≤ P := (Finset.mem_Icc.1 hP).1
        have hQT : Q ≤ T := (Finset.mem_Icc.1 hQ).2
        have hPQ : P ≤ Q := by
          have := (Finset.mem_Icc.1 hQ).1
          omega
        apply le_min
        · omega
        · apply Nat.le_floor
          have hsum :
              ∑ x ∈ Finset.Ico P Q, gain N x = ((Q - P : ℕ) : ℝ) := by
            simp [hgain, hPQ]
          rw [hsum] at hbudget
          exact (le_div_iff₀ hs).2 (by simpa [mul_comm] using hbudget)
      · exact Nat.zero_le _
    · let k : ℕ := min (T - r) m
      have hkpos : 0 < k := by
        dsimp [k]
        exact lt_min (Nat.sub_pos_of_lt hrT) hmpos
      have hkT : r + k ≤ T := by
        dsimp [k]
        omega
      have hkm : k ≤ m := by simp [k]
      have hPmem : r ∈ Finset.Icc r T := by simp [hrT.le]
      have hQmem : r + k ∈ Finset.Icc (r + 1) T := by
        simp only [Finset.mem_Icc]
        omega
      have hm_floor : (m : ℝ) ≤ epsilon / s.1 := by
        dsimp [m]
        exact Nat.floor_le (div_nonneg (by norm_num [epsilon]) hs.le)
      have hk_floor : (k : ℝ) ≤ epsilon / s.1 := by
        exact (by exact_mod_cast hkm : (k : ℝ) ≤ (m : ℝ)).trans hm_floor
      have hbudget :
          s.1 * ∑ x ∈ Finset.Ico r (r + k), gain N x ≤ epsilon := by
        have hsum :
            ∑ x ∈ Finset.Ico r (r + k), gain N x = (k : ℝ) := by
          simp [hgain]
        rw [hsum]
        simpa [mul_comm] using (le_div_iff₀ hs).1 hk_floor
      have hselected :
          k ≤ (if s.1 * ∑ x ∈ Finset.Ico r (r + k), gain N x ≤ epsilon
            then (r + k) - r else 0) := by
        simp [hbudget]
      have hinner := hselected.trans
        (Finset.le_sup
          (s := Finset.Icc (r + 1) T)
          (f := fun Q =>
            if s.1 * ∑ x ∈ Finset.Ico r Q, gain N x ≤ epsilon
            then Q - r else 0) hQmem)
      have houter := hinner.trans
        (Finset.le_sup
          (s := Finset.Icc r T)
          (f := fun P =>
            (Finset.Icc (P + 1) T).sup fun Q =>
              if s.1 * ∑ x ∈ Finset.Ico P Q, gain N x ≤ epsilon
              then Q - P else 0) hPmem)
      simpa [k, m] using houter
  · rw [if_neg hrT]
    have hTr : T ≤ r := Nat.le_of_not_gt hrT
    simp [Nat.sub_eq_zero_of_le hTr]

/-- The reflected capped range has the triangular-tail closed form used in
the exact specialization of `S_T`. -/
theorem sum_range_min_closed_form (m T : ℕ) (hm : m ≤ T) :
    ∑ j ∈ Finset.range T, min j m =
      m * T - m * (m + 1) / 2 := by
  classical
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => min j m) hm
  have hprefix :
      ∑ j ∈ Finset.range m, min j m = ∑ j ∈ Finset.range m, j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact min_eq_left (Finset.mem_range.1 hj).le
  have htail :
      ∑ j ∈ Finset.Ico m T, min j m = (T - m) * m := by
    calc
      ∑ j ∈ Finset.Ico m T, min j m =
          ∑ _j ∈ Finset.Ico m T, m := by
        apply Finset.sum_congr rfl
        intro j hj
        exact min_eq_right (Finset.mem_Ico.1 hj).1
      _ = (T - m) * m := by simp [hm]
  have htri :
      m * (m + 1) / 2 = ∑ j ∈ Finset.range (m + 1), j := by
    rw [Finset.sum_range_id]
    simp [Nat.mul_comm]
  have hpoly :
      m * (m - 1) + m + (T - m) * m = m * T := by
    by_cases hm0 : m = 0
    · simp [hm0]
    · have hm_one : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      have hmsplit : m - 1 + 1 = m := Nat.sub_add_cancel hm_one
      have hTsplit : T - m + m = T := Nat.sub_add_cancel hm
      calc
        m * (m - 1) + m + (T - m) * m =
            m * ((m - 1) + 1 + (T - m)) := by ring
        _ = m * T := by congr 1; omega
  apply Nat.eq_sub_of_add_eq
  calc
    (∑ j ∈ Finset.range T, min j m) + m * (m + 1) / 2 =
        ((∑ j ∈ Finset.range m, j) + (T - m) * m) +
          (∑ j ∈ Finset.range (m + 1), j) := by
      rw [← hsplit, hprefix, htail, htri]
    _ = (∑ j ∈ Finset.range m, j) * 2 + m + (T - m) * m := by
      rw [Finset.sum_range_succ]
      ring
    _ = m * (m - 1) + m + (T - m) * m := by
      rw [Finset.sum_range_id_mul_two]
    _ = m * T := hpoly

/-- For uniform influence energy, the exact capped windows sum to the source's
printed arithmetic-series formula. -/
theorem uniform_window_influence_sum_closed_form
    (N : NetworkSetup n) (hgain : ∀ t, gain N t = 1)
    (henergy : ∀ t, influenceEnergy N t = 1 / (n : ℝ))
    (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n)
    (hm : Nat.floor (epsilon / s.1) ≤ T.1) :
    windowInfluenceSum N T.1 s.1 =
      (((Nat.floor (epsilon / s.1) * T.1 -
        Nat.floor (epsilon / s.1) *
          (Nat.floor (epsilon / s.1) + 1) / 2 : ℕ) : ℝ) / n) := by
  classical
  let m : ℕ := Nat.floor (epsilon / s.1)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hreflect :
      (∑ j ∈ Finset.range T.1, min (T.1 - (j + 1)) m) =
        ∑ j ∈ Finset.range T.1, min j m := by
    calc
      (∑ j ∈ Finset.range T.1, min (T.1 - (j + 1)) m) =
          ∑ j ∈ Finset.range T.1, min (T.1 - 1 - j) m := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        omega
      _ = ∑ j ∈ Finset.range T.1, min j m :=
        Finset.sum_range_reflect (fun j => min j m) T.1
  unfold windowInfluenceSum
  simp_rw [henergy, window_length_eq_min_floor_of_gain_eq_one N hgain]
  rw [← Finset.mul_sum]
  rw [show Nat.floor (epsilon / s.1) = m by rfl]
  simp only [one_div]
  change (n : ℝ)⁻¹ *
      (∑ j ∈ Finset.range T.1, ((min (T.1 - (j + 1)) m : ℕ) : ℝ)) =
    (((m * T.1 - m * (m + 1) / 2 : ℕ) : ℝ) / n)
  rw [← Nat.cast_sum]
  rw [hreflect, sum_range_min_closed_form m T.1 (by simpa [m] using hm)]
  field_simp

/-- Exact inverse-linear/linear balance, written in a form convenient for the
floor-cell comparator argument. -/
theorem reciprocal_linear_balance
    {a b x t : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (ht : 0 < t) :
    2 * Real.sqrt a * Real.sqrt b / Real.sqrt t ≤ a * x / t + b / x := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have ha_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hb_sq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have ht_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hsquare := sq_nonneg (Real.sqrt a * x - Real.sqrt b * Real.sqrt t)
  have hamgm :
      2 * Real.sqrt a * x * Real.sqrt b * Real.sqrt t ≤
        a * x ^ 2 + b * t := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hamgm hst.le
  have hcleared :
      2 * Real.sqrt a * Real.sqrt b * x * t ≤
        Real.sqrt t * (a * x ^ 2 + b * t) := by
    calc
      2 * Real.sqrt a * Real.sqrt b * x * t =
          Real.sqrt t *
            (2 * Real.sqrt a * x * Real.sqrt b * Real.sqrt t) := by
        nth_rewrite 1 [← ht_sq]
        ring
      _ ≤ Real.sqrt t * (a * x ^ 2 + b * t) := hmul
  field_simp [ne_of_gt hx, ne_of_gt ht, ne_of_gt hst] at ⊢
  nlinarith [hcleared]

/-- The balanced scalar coefficient agrees with the source's centralized
leading constant. -/
theorem uniform_balance_constant_eq
    (n : ℕ) (L Δ σ : ℝ) (hn : 0 < n)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    2 * Real.sqrt (ADelta L Δ / epsilon) *
        Real.sqrt (σ ^ 2 * epsilon / (2 * (n : ℝ))) =
      σ * Real.sqrt (2 * ADelta L Δ / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  have heps : 0 < epsilon := by norm_num [epsilon]
  have ha : 0 ≤ ADelta L Δ / epsilon := (div_pos hA heps).le
  have hb : 0 ≤ σ ^ 2 * epsilon / (2 * (n : ℝ)) := by positivity
  have hc : 0 ≤ 2 * ADelta L Δ / (n : ℝ) := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [mul_pow, Real.sq_sqrt hc]
  field_simp [ne_of_gt hnR, ne_of_gt heps]

/-- Lower estimate on one floor cell of the explicit scalar staircase.  The
two cases isolate small floor indices from the balanced range and retain only
an inverse-horizon rounding loss. -/
theorem floor_cell_staircase_lower
    (n m T : ℕ) (A σ s : ℝ) (hn : 0 < n) (hA : 0 < A) (hσ : 0 < σ)
    (hT : 0 < T) (hs : 0 < s) (hcap : s ≤ 1 / (64 * (n : ℝ)))
    (hfloor : m = Nat.floor (epsilon / s)) (hmT : m ≤ T) :
    let a := A / epsilon
    let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
    let c := 2 * Real.sqrt a * Real.sqrt b
    let D := b / (2 * c)
    let Ctail := σ ^ 2 * (epsilon + 1 / (64 * (n : ℝ))) / (4 * (n : ℝ))
    c / Real.sqrt T - (a + b / D ^ 2 + Ctail) / T ≤
      (A * (m : ℝ) + (σ ^ 2 / 2) * s ^ 2 *
        (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
        (epsilon * T) := by
  dsimp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have heps : 0 < epsilon := by norm_num [epsilon]
  let a := A / epsilon
  let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
  let c := 2 * Real.sqrt a * Real.sqrt b
  let D := b / (2 * c)
  let Ctail := σ ^ 2 * (epsilon + 1 / (64 * (n : ℝ))) / (4 * (n : ℝ))
  have ha : 0 < a := div_pos hA heps
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs64 : s ≤ 1 / 64 := by
    calc
      s ≤ 1 / (64 * (n : ℝ)) := hcap
      _ ≤ 1 / 64 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hm4 : 4 ≤ m := by
    have hx : 4 ≤ epsilon / s := by
      rw [le_div_iff₀ hs]
      norm_num [epsilon] at hs64 ⊢
      linarith
    rw [hfloor]
    exact Nat.le_floor hx
  let k : ℕ := m + 1
  have hkR : (0 : ℝ) < k := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm4)
  have hfloor_le : (m : ℝ) ≤ epsilon / s := by
    rw [hfloor]
    exact Nat.floor_le (div_nonneg heps.le hs.le)
  have hfloor_lt : epsilon / s < (k : ℝ) := by
    dsimp [k]
    rw [hfloor]
    simpa using Nat.lt_floor_add_one (epsilon / s)
  have hsm : s * (m : ℝ) ≤ epsilon := by
    simpa [mul_comm] using (le_div_iff₀ hs).1 hfloor_le
  have hsk : s * (k : ℝ) ≤ epsilon + 1 / (64 * (n : ℝ)) := by
    dsimp [k]
    push_cast
    nlinarith
  have hslow : epsilon / (k : ℝ) < s := by
    apply (div_lt_iff₀ hkR).2
    have := (div_lt_iff₀ hs).1 hfloor_lt
    simpa [mul_comm] using this
  have htriLe : m * (m + 1) / 2 ≤ m * T := by
    apply Nat.div_le_of_le_mul
    calc
      m * (m + 1) ≤ m * (2 * T) := by gcongr; omega
      _ = 2 * (m * T) := by ring
  have hdivCast :
      (((m * (m + 1) / 2 : ℕ) : ℝ)) ≤
        (m : ℝ) * (k : ℝ) / 2 := by
    calc
      (((m * (m + 1) / 2 : ℕ) : ℝ)) ≤
          ((m * (m + 1) : ℕ) : ℝ) / (2 : ℝ) := Nat.cast_div_le
      _ = (m : ℝ) * (k : ℝ) / 2 := by simp [k]
  have hstair :
      ((m : ℝ) * T - (m : ℝ) * (k : ℝ) / 2) ≤
        ((m * T - m * (m + 1) / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub htriLe]
    push_cast
    linarith
  have hfirst :
      b * (m : ℝ) / (k : ℝ) ^ 2 ≤
        σ ^ 2 * s ^ 2 * (m : ℝ) / (2 * epsilon * (n : ℝ)) := by
    dsimp [b]
    have hsquare : (epsilon / (k : ℝ)) ^ 2 ≤ s ^ 2 :=
      (sq_le_sq₀ (div_nonneg heps.le hkR.le) hs.le).2 hslow.le
    field_simp [ne_of_gt hnR, ne_of_gt hkR, ne_of_gt heps]
      at hsquare ⊢
    nlinarith
  have htail :
      σ ^ 2 * s ^ 2 * (m : ℝ) * (k : ℝ) /
          (4 * epsilon * (n : ℝ) * T) ≤ Ctail / T := by
    have hprod := mul_le_mul hsm hsk (mul_nonneg hs.le hkR.le) heps.le
    dsimp [Ctail]
    field_simp [ne_of_gt hnR, ne_of_gt hTR, ne_of_gt heps] at hprod ⊢
    nlinarith [sq_nonneg σ]
  have hnoise :
      b * (m : ℝ) / (k : ℝ) ^ 2 - Ctail / T ≤
        ((σ ^ 2 / 2) * s ^ 2 *
          (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
          (epsilon * T) := by
    have hcoef :
        0 ≤ σ ^ 2 * s ^ 2 / (2 * epsilon * (n : ℝ) * T) := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hstair hcoef
    have hnoiseLower :
        σ ^ 2 * s ^ 2 * (m : ℝ) / (2 * epsilon * (n : ℝ)) -
            σ ^ 2 * s ^ 2 * (m : ℝ) * (k : ℝ) /
              (4 * epsilon * (n : ℝ) * T) ≤
          ((σ ^ 2 / 2) * s ^ 2 *
            (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
            (epsilon * T) := by
      calc
        σ ^ 2 * s ^ 2 * (m : ℝ) / (2 * epsilon * (n : ℝ)) -
              σ ^ 2 * s ^ 2 * (m : ℝ) * (k : ℝ) /
                (4 * epsilon * (n : ℝ) * T) =
            (σ ^ 2 * s ^ 2 / (2 * epsilon * (n : ℝ) * T)) *
              ((m : ℝ) * T - (m : ℝ) * (k : ℝ) / 2) := by
              field_simp [ne_of_gt hnR, ne_of_gt hTR, ne_of_gt heps]
              ring
        _ ≤ (σ ^ 2 * s ^ 2 / (2 * epsilon * (n : ℝ) * T)) *
              ((m * T - m * (m + 1) / 2 : ℕ) : ℝ) := hscaled
        _ = ((σ ^ 2 / 2) * s ^ 2 *
              (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
              (epsilon * T) := by
                ring
    linarith
  by_cases hkSmall : (k : ℝ) ≤ D * Real.sqrt T
  · have hkTwo : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    have hnoiseLead : c / Real.sqrt T ≤ b * (m : ℝ) / (k : ℝ) ^ 2 := by
      have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 hTR
      have hck : c * (k : ℝ) ≤ b * Real.sqrt T / 2 := by
        calc
          c * (k : ℝ) ≤ c * (D * Real.sqrt T) :=
            mul_le_mul_of_nonneg_left hkSmall hc.le
          _ = b * Real.sqrt T / 2 := by
            dsimp [D]
            field_simp [ne_of_gt hc]
      have hkm : (k : ℝ) / 2 ≤ m := by
        have hm4R : (4 : ℝ) ≤ m := by exact_mod_cast hm4
        dsimp [k]
        push_cast
        nlinarith
      have hck' := mul_le_mul_of_nonneg_right hck hkR.le
      have hscale :
          b * Real.sqrt T * ((k : ℝ) / 2) ≤
            b * Real.sqrt T * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hkm
          (mul_nonneg hb.le (Real.sqrt_nonneg (T : ℝ)))
      have hcleared :
          c * (k : ℝ) ^ 2 ≤ b * (m : ℝ) * Real.sqrt T := by
        nlinarith [hck', hscale]
      apply (div_le_iff₀ hsqrt).2
      calc
        c ≤ (b * (m : ℝ) * Real.sqrt T) / (k : ℝ) ^ 2 :=
          (le_div_iff₀ (sq_pos_of_pos hkR)).2 hcleared
        _ = b * (m : ℝ) / (k : ℝ) ^ 2 * Real.sqrt T := by ring
    have hsignal : 0 ≤ A * (m : ℝ) / (epsilon * T) := by positivity
    change c / Real.sqrt T - (a + b / D ^ 2 + Ctail) / T ≤
      (A * (m : ℝ) + (σ ^ 2 / 2) * s ^ 2 *
        (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
        (epsilon * T)
    have hRhs :
        (A * (m : ℝ) + (σ ^ 2 / 2) * s ^ 2 *
          (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
            (epsilon * T) =
          A * (m : ℝ) / (epsilon * T) +
            ((σ ^ 2 / 2) * s ^ 2 *
              (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
              (epsilon * T) := by ring
    rw [hRhs]
    have hrem : 0 ≤ (a + b / D ^ 2) / T := by positivity
    have hsplit : (a + b / D ^ 2 + Ctail) / T =
        (a + b / D ^ 2) / T + Ctail / T := by ring
    rw [hsplit]
    linarith
  · have hkLarge : D * Real.sqrt T < (k : ℝ) := lt_of_not_ge hkSmall
    have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 hTR
    have hbinv : b / (k : ℝ) ^ 2 ≤ b / (D ^ 2 * T) := by
      have hsquare : D ^ 2 * T ≤ (k : ℝ) ^ 2 := by
        have hsquare' := (sq_le_sq₀
          (mul_nonneg hD.le (Real.sqrt_nonneg _)) hkR.le).2 hkLarge.le
        simpa [Real.sq_sqrt hTR.le, mul_pow] using hsquare'
      exact div_le_div_of_nonneg_left hb.le (by positivity) hsquare
    have hbalance := reciprocal_linear_balance ha hb hkR hTR
    change c / Real.sqrt T ≤ a * (k : ℝ) / T + b / (k : ℝ) at hbalance
    have hsignalEq :
        a * (k : ℝ) / T - a / T = A * (m : ℝ) / (epsilon * T) := by
      dsimp [a, k]
      push_cast
      field_simp [ne_of_gt hTR, ne_of_gt heps]
      ring
    have hnoiseEq :
        b / (k : ℝ) - b / (k : ℝ) ^ 2 =
          b * (m : ℝ) / (k : ℝ) ^ 2 := by
      dsimp [k]
      push_cast
      field_simp [ne_of_gt hkR]
      ring
    change c / Real.sqrt T - (a + b / D ^ 2 + Ctail) / T ≤
      (A * (m : ℝ) + (σ ^ 2 / 2) * s ^ 2 *
        (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
        (epsilon * T)
    have hRhs :
        (A * (m : ℝ) + (σ ^ 2 / 2) * s ^ 2 *
          (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
            (epsilon * T) =
          A * (m : ℝ) / (epsilon * T) +
            ((σ ^ 2 / 2) * s ^ 2 *
              (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
              (epsilon * T) := by ring
    rw [hRhs]
    have hsplit : (a + b / D ^ 2 + Ctail) / T =
        a / T + b / (D ^ 2 * T) + Ctail / T := by ring
    rw [hsplit]
    linarith
/-
  dsimp
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have heps : 0 < epsilon := by norm_num [epsilon]
  let a := A / epsilon
  let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
  let c := 2 * Real.sqrt a * Real.sqrt b
  let D := b / (2 * c)
  let Ctail := σ ^ 2 * (epsilon + 1 / (64 * (n : ℝ))) / (4 * (n : ℝ))
  have ha : 0 < a := div_pos hA heps
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs64 : s ≤ 1 / 64 := by
    calc
      s ≤ 1 / (64 * (n : ℝ)) := hcap
      _ ≤ 1 / 64 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hm4 : 4 ≤ m := by
    have hx : 4 ≤ epsilon / s := by
      rw [le_div_iff₀ hs]
      norm_num [epsilon] at hs64 ⊢
      linarith
    rw [hfloor]
    exact Nat.le_floor hx
  let k : ℕ := m + 1
  have hkR : (0 : ℝ) < k := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm4)
  have hfloor_le : (m : ℝ) ≤ epsilon / s := by
    rw [hfloor]
    exact Nat.floor_le (div_nonneg heps.le hs.le)
  have hfloor_lt : epsilon / s < (k : ℝ) := by
    dsimp [k]
    rw [hfloor]
    simpa using Nat.lt_floor_add_one (epsilon / s)
  have hsm : s * (m : ℝ) ≤ epsilon := by
    simpa [mul_comm] using (le_div_iff₀ hs).1 hfloor_le
  have hsk : s * (k : ℝ) ≤ epsilon + 1 / (64 * (n : ℝ)) := by
    dsimp [k]
    push_cast
    nlinarith
  have hslow : epsilon / (k : ℝ) < s := by
    apply (div_lt_iff₀ hkR).2
    have := (div_lt_iff₀ hs).1 hfloor_lt
    simpa [mul_comm] using this
  have htriLe : m * (m + 1) / 2 ≤ m * T := by
    apply Nat.div_le_of_le_mul
    calc
      m * (m + 1) ≤ m * (2 * T) := by gcongr; omega
      _ = 2 * (m * T) := by ring
  have hdivCast :
      (((m * (m + 1) / 2 : ℕ) : ℝ)) ≤
        (m : ℝ) * (k : ℝ) / 2 := by
    calc
      (((m * (m + 1) / 2 : ℕ) : ℝ)) ≤
          ((m * (m + 1) : ℕ) : ℝ) / (2 : ℝ) := Nat.cast_div_le
      _ = (m : ℝ) * (k : ℝ) / 2 := by simp [k]
  have hstair :
      ((m : ℝ) * T - (m : ℝ) * (k : ℝ) / 2) ≤
        ((m * T - m * (m + 1) / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub htriLe]
    push_cast
    linarith
  have hfirst :
      b * (m : ℝ) / (k : ℝ) ^ 2 ≤
        σ ^ 2 * s ^ 2 * (m : ℝ) / (2 * epsilon * (n : ℝ)) := by
    dsimp [b]
    have hsquare : (epsilon / (k : ℝ)) ^ 2 ≤ s ^ 2 :=
      (sq_le_sq₀ (div_nonneg heps.le hkR.le) hs.le).2 hslow.le
    field_simp [ne_of_gt hnR, ne_of_gt hkR, ne_of_gt heps]
      at hsquare ⊢
    nlinarith
  have htail :
      σ ^ 2 * s ^ 2 * (m : ℝ) * (k : ℝ) /
          (4 * epsilon * (n : ℝ) * T) ≤ Ctail / T := by
    have hprod := mul_le_mul hsm hsk (mul_nonneg hs.le hkR.le) heps.le
    dsimp [Ctail]
    field_simp [ne_of_gt hnR, ne_of_gt hTR, ne_of_gt heps] at hprod ⊢
    nlinarith [sq_nonneg σ]
  have hnoise :
      b * (m : ℝ) / (k : ℝ) ^ 2 - Ctail / T ≤
        ((σ ^ 2 / 2) * s ^ 2 *
          (((m * T - m * (m + 1) / 2 : ℕ) : ℝ) / n)) /
          (epsilon * T) := by
    sorry
  by_cases hkSmall : (k : ℝ) ≤ D * Real.sqrt T
  · have hkTwo : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
    have hnoiseLead : c / Real.sqrt T ≤ b * (m : ℝ) / (k : ℝ) ^ 2 := by
      sorry
    have hsignal : 0 ≤ A * (m : ℝ) / (epsilon * T) := by positivity
    sorry
  · have hkLarge : D * Real.sqrt T < (k : ℝ) := lt_of_not_ge hkSmall
    have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 hTR
    have hbinv : b / (k : ℝ) ^ 2 ≤ b / (D ^ 2 * T) := by
      have hsquare : D ^ 2 * T ≤ (k : ℝ) ^ 2 := by
        have hsquare' := (sq_le_sq₀
          (mul_nonneg hD.le (Real.sqrt_nonneg _)) hkR.le).2 hkLarge.le
        simpa [Real.sq_sqrt hTR.le, mul_pow] using hsquare'
      exact div_le_div_of_nonneg_left hb.le (by positivity) hsquare
    have hbalance := reciprocal_linear_balance ha hb hkR hTR
    sorry
-/

/-- The exact uniform-window staircase bounds every admissible comparator
value from below.  The onset is needed only for the saturated cell `T < m`,
where the full-horizon signal term already dominates the square-root scale. -/
theorem uniform_comparator_lower
    (N : NetworkSetup n) (hgain : ∀ t, gain N t = 1)
    (henergy : ∀ t, influenceEnergy N t = 1 / (n : ℝ))
    (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon)
    (hlarge :
      let a := ADelta L Δ / epsilon
      let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
      let c := 2 * Real.sqrt a * Real.sqrt b
      (c / a) ^ 2 ≤ (T.1 : ℝ)) :
    let a := ADelta L Δ / epsilon
    let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
    let c := 2 * Real.sqrt a * Real.sqrt b
    let D := b / (2 * c)
    let Ctail := σ ^ 2 * (epsilon + 1 / (64 * (n : ℝ))) / (4 * (n : ℝ))
    c / Real.sqrt T.1 - (a + b / D ^ 2 + Ctail) / T.1 ≤
      comparator N L Δ σ T := by
  classical
  let A := ADelta L Δ
  let a := A / epsilon
  let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
  let c := 2 * Real.sqrt a * Real.sqrt b
  let D := b / (2 * c)
  let Ctail := σ ^ 2 * (epsilon + 1 / (64 * (n : ℝ))) / (4 * (n : ℝ))
  change (c / a) ^ 2 ≤ (T.1 : ℝ) at hlarge
  change c / Real.sqrt T.1 - (a + b / D ^ 2 + Ctail) / T.1 ≤
    comparator N L Δ σ T
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hTR : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have heps : 0 < epsilon := by norm_num [epsilon]
  have hA : 0 < A := by
    dsimp [A, ADelta]
    exact mul_pos hL hΔ
  have ha : 0 < a := div_pos hA heps
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
  have hK : 0 ≤ a + b / D ^ 2 + Ctail := by positivity
  have hrange_nonempty :
      (Set.range fun s : AdmissibleDimensionlessStepsize n =>
        comparatorAt N L Δ σ T s).Nonempty := by
    let s₀ : AdmissibleDimensionlessStepsize n :=
      ⟨1 / (64 * (n : ℝ)), one_div_pos.mpr (mul_pos (by norm_num) hnR), le_rfl⟩
    exact ⟨comparatorAt N L Δ σ T s₀, ⟨s₀, rfl⟩⟩
  unfold comparator
  apply le_csInf hrange_nonempty
  rintro y ⟨s, rfl⟩
  let m : ℕ := Nat.floor (epsilon / s.1)
  by_cases hmT : m ≤ T.1
  · have hcell := floor_cell_staircase_lower
      n m T.1 A σ s.1 N.hn hA hσ T.2 s.2.1 s.2.2 rfl hmT
    have hwindow := window_length_eq_min_floor_of_gain_eq_one
      N hgain T.1 0 s
    have hsum := uniform_window_influence_sum_closed_form
      N hgain henergy T s (by simpa [m] using hmT)
    unfold comparatorAt comparatorNumerator
    dsimp only
    rw [hwindow, hsum]
    simp only [Nat.cast_min, Nat.cast_zero, tsub_zero]
    rw [min_eq_right (by exact_mod_cast hmT : (m : ℝ) ≤ T.1)]
    simpa [A, a, b, c, D, Ctail, m] using hcell
  · have hTm : T.1 ≤ m := Nat.le_of_lt (lt_of_not_ge hmT)
    have hwindow := window_length_eq_min_floor_of_gain_eq_one
      N hgain T.1 0 s
    have hwindowSum : 0 ≤ windowInfluenceSum N T.1 s.1 := by
      unfold windowInfluenceSum
      exact Finset.sum_nonneg fun j _ => by
        rw [henergy]
        exact mul_nonneg (by positivity) (Nat.cast_nonneg _)
    have hnoise :
        0 ≤ (σ ^ 2 / 2) * s.1 ^ 2 * windowInfluenceSum N T.1 s.1 := by
      positivity
    have hden : 0 < epsilon * (T.1 : ℝ) := mul_pos heps hTR
    have hcompA : a ≤ comparatorAt N L Δ σ T s := by
      unfold comparatorAt comparatorNumerator
      rw [hwindow]
      simp only [Nat.cast_min, Nat.cast_zero, tsub_zero]
      rw [min_eq_left (by exact_mod_cast hTm : (T.1 : ℝ) ≤ m)]
      calc
        a = A * (T.1 : ℝ) / (epsilon * T.1) := by
          dsimp [a]
          field_simp [ne_of_gt hTR]
        _ ≤ (A * (T.1 : ℝ) +
              (σ ^ 2 / 2) * s.1 ^ 2 * windowInfluenceSum N T.1 s.1) /
              (epsilon * T.1) :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_right hnoise) hden.le
    have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hTR
    have hsquares : (c / a) ^ 2 ≤ (Real.sqrt T.1) ^ 2 := by
      simpa [Real.sq_sqrt hTR.le] using hlarge
    have hratio : c / a ≤ Real.sqrt T.1 :=
      (sq_le_sq₀ (div_nonneg hc.le ha.le) (Real.sqrt_nonneg _)).mp hsquares
    have hcross : c ≤ a * Real.sqrt T.1 := by
      calc
        c = a * (c / a) := by field_simp [ne_of_gt ha]
        _ ≤ a * Real.sqrt T.1 := mul_le_mul_of_nonneg_left hratio ha.le
    have hlead : c / Real.sqrt T.1 ≤ a :=
      (div_le_iff₀ hsqrt).2 (by simpa [mul_comm] using hcross)
    have hrem : 0 ≤ (a + b / D ^ 2 + Ctail) / T.1 :=
      div_nonneg hK hTR.le
    linarith

/-- Rounding the continuously balanced cell length upward gives an admissible
test stepsize and loses at most one signal cell. -/
theorem uniform_comparator_upper
    (N : NetworkSetup n) (hgain : ∀ t, gain N t = 1)
    (henergy : ∀ t, influenceEnergy N t = 1 / (n : ℝ))
    (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (T : PositiveHorizon)
    (hcapOnset :
      let a := ADelta L Δ / epsilon
      let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
      let c := 2 * Real.sqrt a * Real.sqrt b
      let x := c * Real.sqrt T.1 / (2 * a)
      (4 * n : ℝ) ≤ x)
    (hhorizon :
      let a := ADelta L Δ / epsilon
      let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
      let c := 2 * Real.sqrt a * Real.sqrt b
      let x := c * Real.sqrt T.1 / (2 * a)
      x + 1 ≤ (T.1 : ℝ)) :
    let a := ADelta L Δ / epsilon
    let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
    let c := 2 * Real.sqrt a * Real.sqrt b
    comparator N L Δ σ T ≤ c / Real.sqrt T.1 + a / T.1 := by
  classical
  let A := ADelta L Δ
  let a := A / epsilon
  let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
  let c := 2 * Real.sqrt a * Real.sqrt b
  let x := c * Real.sqrt T.1 / (2 * a)
  change (4 * n : ℝ) ≤ x at hcapOnset
  change x + 1 ≤ (T.1 : ℝ) at hhorizon
  change comparator N L Δ σ T ≤ c / Real.sqrt T.1 + a / T.1
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hTR : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have heps : 0 < epsilon := by norm_num [epsilon]
  have hA : 0 < A := by
    dsimp [A, ADelta]
    exact mul_pos hL hΔ
  have ha : 0 < a := div_pos hA heps
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hTR
  have hx : 0 < x := by dsimp [x]; positivity
  have haSq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hbSq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hTSq : (Real.sqrt T.1) ^ 2 = (T.1 : ℝ) := Real.sq_sqrt hTR.le
  have hcSq : c ^ 2 = 4 * a * b := by
    dsimp [c]
    rw [mul_pow, mul_pow, haSq, hbSq]
    ring
  let m : ℕ := Nat.ceil x
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.ceil_pos.mpr hx
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
  have hxm : x ≤ (m : ℝ) := by
    dsimp [m]
    exact Nat.le_ceil x
  have hmx : (m : ℝ) < x + 1 := by
    dsimp [m]
    exact Nat.ceil_lt_add_one hx.le
  have hmT : m ≤ T.1 := by
    exact_mod_cast (hmx.le.trans hhorizon)
  have h4nm : 4 * n ≤ m := by
    exact_mod_cast hcapOnset.trans hxm
  let sₜ : AdmissibleDimensionlessStepsize n := ⟨epsilon / (m : ℝ), by
    constructor
    · exact div_pos heps hmR
    · have h4nmR : (4 * (n : ℝ)) ≤ (m : ℝ) := by exact_mod_cast h4nm
      rw [div_le_iff₀ hmR]
      field_simp [ne_of_gt hnR]
      norm_num [epsilon] at h4nmR ⊢
      nlinarith
  ⟩
  have hratio : epsilon / sₜ.1 = (m : ℝ) := by
    dsimp [sₜ]
    field_simp [ne_of_gt heps, ne_of_gt hmR]
  have hfloor : Nat.floor (epsilon / sₜ.1) = m := by
    rw [hratio]
    exact Nat.floor_natCast m
  have hwindow := window_length_eq_min_floor_of_gain_eq_one
    N hgain T.1 0 sₜ
  have hsum := uniform_window_influence_sum_closed_form
    N hgain henergy T sₜ (by simpa [hfloor] using hmT)
  have htri :
      (((m * T.1 - m * (m + 1) / 2 : ℕ) : ℝ)) ≤
        (m : ℝ) * T.1 := by
    exact_mod_cast (Nat.sub_le (m * T.1) (m * (m + 1) / 2))
  have hAt : comparatorAt N L Δ σ T sₜ ≤
      a * (m : ℝ) / T.1 + b / (m : ℝ) := by
    have htriScaled := mul_le_mul_of_nonneg_right htri
      (mul_nonneg (sq_nonneg σ) (sq_nonneg epsilon))
    unfold comparatorAt comparatorNumerator
    rw [hwindow, hsum, hfloor]
    simp only [Nat.cast_min, Nat.cast_zero, tsub_zero]
    rw [min_eq_right (by exact_mod_cast hmT : (m : ℝ) ≤ T.1)]
    dsimp [sₜ, a, b, A]
    field_simp [ne_of_gt hnR, ne_of_gt hTR, ne_of_gt hmR,
      ne_of_gt heps] at htri ⊢
    nlinarith [htriScaled]
  have hsignalRound : a * (m : ℝ) / T.1 ≤
      a * x / T.1 + a / T.1 := by
    have hmx' : (m : ℝ) ≤ x + 1 := hmx.le
    have := mul_le_mul_of_nonneg_left hmx' ha.le
    calc
      a * (m : ℝ) / T.1 ≤ a * (x + 1) / T.1 :=
        div_le_div_of_nonneg_right this hTR.le
      _ = a * x / T.1 + a / T.1 := by ring
  have hnoiseRound : b / (m : ℝ) ≤ b / x := by
    exact div_le_div_of_nonneg_left hb.le hx hxm
  have hbalance : a * x / T.1 + b / x = c / Real.sqrt T.1 := by
    dsimp [x]
    field_simp [ne_of_gt ha, ne_of_gt hc, ne_of_gt hsqrt,
      ne_of_gt hTR]
    nlinarith [hcSq, hTSq]
  unfold comparator
  have hrange : comparatorAt N L Δ σ T sₜ ∈
      Set.range (fun s : AdmissibleDimensionlessStepsize n =>
        comparatorAt N L Δ σ T s) := ⟨sₜ, rfl⟩
  have hinf := csInf_le (comparatorAt_range_bddBelow N L Δ σ hL hΔ T) hrange
  linarith

/-- The genuinely nonperiodic subclass following (60), including the exact
`W`, `S`, and leading-comparator formulas.
Book `#/key_lemmas/7/statement_math`:
“`\pi_t=u`, `D_tz=0`, `\kappa_t=1`, `b_t=u`, `q_t=1/n`”. -/
theorem doubly_stochastic_row_nonperiodic_subclass
    (N : NetworkSetup n) (hds : IsDoublyStochasticRow N)
    (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    (∀ t, absoluteProbability N t = uniformRow n) ∧
    (∀ t (z : ZeroSumNodeVector n), influenceOperator N t z = 0) ∧
    (∀ t, gain N t = 1) ∧
    (∀ t, influenceRow N t = uniformRow n) ∧
    (∀ t, influenceEnergy N t = 1 / n) ∧
    (∀ (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n) (r : ℕ),
      r ≤ T.1 →
      windowLength N T.1 r s.1 = min (T.1 - r) (Nat.floor (epsilon / s.1))) ∧
    (∀ (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n),
      let m := Nat.floor (epsilon / s.1)
      m ≤ T.1 →
      windowInfluenceSum N T.1 s.1 =
        ((m * T.1 - m * (m + 1) / 2 : ℕ) : ℝ) / n) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Tonset : ℕ, ∀ T : PositiveHorizon, Tonset ≤ T.1 →
      |comparator N L Δ σ T -
        σ * Real.sqrt (2 * ADelta L Δ / (n * T.1))| ≤ K / T.1 := by
  classical
  rcases uniform_network_quantities_of_doubly_stochastic_row N hds with
    ⟨hpi, hD, hgain, hb, henergy⟩
  refine ⟨hpi, hD, hgain, hb, henergy, ?_, ?_, ?_⟩
  · intro T s r hr
    exact window_length_eq_min_floor_of_gain_eq_one N hgain T.1 r s
  · intro T s
    dsimp
    intro hm
    exact uniform_window_influence_sum_closed_form
      N hgain henergy T s hm
  · let A := ADelta L Δ
    let a := A / epsilon
    let b := σ ^ 2 * epsilon / (2 * (n : ℝ))
    let c := 2 * Real.sqrt a * Real.sqrt b
    let D := b / (2 * c)
    let Ctail := σ ^ 2 * (epsilon + 1 / (64 * (n : ℝ))) / (4 * (n : ℝ))
    let Klo := a + b / D ^ 2 + Ctail
    let q := c / (2 * a)
    let R := max ((c / a) ^ 2)
      (max ((8 * a * (n : ℝ) / c) ^ 2) ((q + 1) ^ 2))
    let Tonset : ℕ := Nat.ceil R
    let K := Klo + a
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
    have hTRpos : ∀ T : PositiveHorizon, (0 : ℝ) < T.1 :=
      fun T => Nat.cast_pos.mpr T.2
    have heps : 0 < epsilon := by norm_num [epsilon]
    have hA : 0 < A := by
      dsimp [A, ADelta]
      exact mul_pos hL hΔ
    have ha : 0 < a := div_pos hA heps
    have hbpos : 0 < b := by dsimp [b]; positivity
    have hc : 0 < c := by dsimp [c]; positivity
    have hD : 0 < D := by dsimp [D]; positivity
    have hCtail : 0 ≤ Ctail := by dsimp [Ctail]; positivity
    have hKlo : 0 ≤ Klo := by dsimp [Klo]; positivity
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨K, hK, Tonset, ?_⟩
    intro T hTonset
    have hTR : (0 : ℝ) < T.1 := hTRpos T
    have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hTR
    have hsqrtSq : (Real.sqrt T.1) ^ 2 = (T.1 : ℝ) :=
      Real.sq_sqrt hTR.le
    have hRT : R ≤ (T.1 : ℝ) := by
      calc
        R ≤ (Nat.ceil R : ℕ) := Nat.le_ceil R
        _ ≤ (T.1 : ℝ) := by exact_mod_cast hTonset
    have hlowerOnset : (c / a) ^ 2 ≤ (T.1 : ℝ) := by
      exact (le_max_left _ _).trans hRT
    have hcapSq : (8 * a * (n : ℝ) / c) ^ 2 ≤ (T.1 : ℝ) := by
      calc
        (8 * a * (n : ℝ) / c) ^ 2 ≤
            max ((8 * a * (n : ℝ) / c) ^ 2) ((q + 1) ^ 2) := le_max_left _ _
        _ ≤ R := le_max_right _ _
        _ ≤ (T.1 : ℝ) := hRT
    have hhorizonSq : (q + 1) ^ 2 ≤ (T.1 : ℝ) := by
      calc
        (q + 1) ^ 2 ≤
            max ((8 * a * (n : ℝ) / c) ^ 2) ((q + 1) ^ 2) := le_max_right _ _
        _ ≤ R := le_max_right _ _
        _ ≤ (T.1 : ℝ) := hRT
    have hcapRoot : 8 * a * (n : ℝ) / c ≤ Real.sqrt T.1 := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      simpa [hsqrtSq] using hcapSq
    have hcapOnset : (4 * n : ℝ) ≤ c * Real.sqrt T.1 / (2 * a) := by
      field_simp [ne_of_gt ha, ne_of_gt hc] at hcapRoot ⊢
      nlinarith
    have hq : 0 < q := by dsimp [q]; positivity
    have hhorizonRoot : q + 1 ≤ Real.sqrt T.1 := by
      apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      simpa [hsqrtSq] using hhorizonSq
    have hhorizon : c * Real.sqrt T.1 / (2 * a) + 1 ≤ (T.1 : ℝ) := by
      have hqform : c * Real.sqrt T.1 / (2 * a) = q * Real.sqrt T.1 := by
        dsimp [q]
        ring
      rw [hqform]
      calc
        q * Real.sqrt T.1 + 1 ≤ (Real.sqrt T.1) ^ 2 := by
          nlinarith [mul_nonneg hq.le (Real.sqrt_nonneg (T.1 : ℝ))]
        _ = (T.1 : ℝ) := hsqrtSq
    have hlower := uniform_comparator_lower
      N hgain henergy L Δ σ hL hΔ hσ T (by
        simpa [A, a, b, c] using hlowerOnset)
    have hupper := uniform_comparator_upper
      N hgain henergy L Δ σ hL hΔ hσ T (by
        simpa [A, a, b, c] using hcapOnset) (by
        simpa [A, a, b, c] using hhorizon)
    have hcEq : c = σ * Real.sqrt (2 * A / (n : ℝ)) := by
      simpa [A, a, b, c] using
        (uniform_balance_constant_eq n L Δ σ N.hn hL hΔ hσ)
    let lead := σ * Real.sqrt (2 * A / ((n : ℝ) * T.1))
    have hleadEq : lead = c / Real.sqrt T.1 := by
      rw [hcEq]
      dsimp [lead]
      have hrad1 : 0 ≤ 2 * A / ((n : ℝ) * T.1) := by positivity
      have hrad2 : 0 ≤ 2 * A / (n : ℝ) := by positivity
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt hrad1]
      rw [div_pow, mul_pow, Real.sq_sqrt hrad2, Real.sq_sqrt hTR.le]
      field_simp [ne_of_gt hnR, ne_of_gt hTR]
    change |comparator N L Δ σ T - lead| ≤ K / T.1
    rw [hleadEq]
    change c / Real.sqrt T.1 - Klo / T.1 ≤ comparator N L Δ σ T at hlower
    change comparator N L Δ σ T ≤ c / Real.sqrt T.1 + a / T.1 at hupper
    have hKloK : Klo ≤ K := by dsimp [K]; linarith [ha]
    have haK : a ≤ K := by dsimp [K]; linarith [hKlo]
    have hKloDiv : Klo / (T.1 : ℝ) ≤ K / T.1 :=
      div_le_div_of_nonneg_right hKloK hTR.le
    have haDiv : a / (T.1 : ℝ) ≤ K / T.1 :=
      div_le_div_of_nonneg_right haK hTR.le
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- Periodicity domain from `#/key_lemmas/8/statement_math`:
“若网络周期为 `p`”. -/
def IsPeriodicNetwork (N : NetworkSetup n) (p : PositiveHorizon) : Prop :=
  Function.Periodic N.rowMix p.1 ∧ Function.Periodic N.colMix p.1

/-- A normalized periodic forward push-mass sequence. Book
`#/key_lemmas/8/proof/0/description`:
“Periodicity and uniqueness make pi,D,b periodic; the forward push mass
converges summably to its unique periodic sequence. Sum the coboundary over
one period.” -/
def IsPeriodicPushMass (N : NetworkSetup n) (p : PositiveHorizon)
    (w : ℕ → Fin n → ℝ) : Prop :=
  Function.Periodic w p.1 ∧
    (∀ t, w (t + 1) = N.colMix t *ᵥ w t) ∧
    (∀ t, ∑ i, w t i = n)

/-- Existence and uniqueness of the periodic mass characterized above. Book
`#/key_lemmas/8/proof/0/description`:
“Periodicity and uniqueness make pi,D,b periodic; the forward push mass
converges summably to its unique periodic sequence. Sum the coboundary over
one period.” -/
theorem exists_unique_periodicPushMass
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃! w : ℕ → Fin n → ℝ, IsPeriodicPushMass N p w := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  obtain ⟨seqs, hseq⟩ :=
    FiniteNetwork.exists_unique_positive_periodic_push_pull_perron_sequences
      (Node := Fin n) N.rowMix N.colMix p.1 p.2
      N.row_stochastic N.col_stochastic
      N.row_positive_diagonal N.col_positive_diagonal
      N.row_strongly_connected N.col_strongly_connected hp.1 hp.2
  let w : ℕ → Fin n → ℝ := fun t i => (n : ℝ) * seqs.2 t i
  have hw : IsPeriodicPushMass N p w := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      funext i
      change (n : ℝ) * seqs.2 (t + p.1) i = (n : ℝ) * seqs.2 t i
      rw [hseq.2.1.2.2.2 t]
    · intro t
      funext i
      change (n : ℝ) * seqs.2 (t + 1) i =
        (N.colMix t *ᵥ (fun j => (n : ℝ) * seqs.2 t j)) i
      calc
        (n : ℝ) * seqs.2 (t + 1) i =
            (n : ℝ) * (N.colMix t *ᵥ seqs.2 t) i := by
              exact congrArg (fun x => (n : ℝ) * x) (hseq.1.2.2.1 t i).symm
        _ = (N.colMix t *ᵥ (fun j => (n : ℝ) * seqs.2 t j)) i := by
              simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc,
                mul_comm, mul_left_comm]
    · intro t
      simp only [w, ← Finset.mul_sum, hseq.1.2.2.2 t]
      ring
  refine ⟨w, hw, ?_⟩
  intro wcomp hwcomp
  let e : ℕ → Fin n → ℝ := fun t => wcomp t - w t
  have he_periodic : Function.Periodic e p.1 := by
    intro t
    dsimp [e]
    rw [hwcomp.1 t, hw.1 t]
  have he_step (t : ℕ) : N.colMix t *ᵥ e t = e (t + 1) := by
    dsimp [e]
    rw [Matrix.mulVec_sub, hwcomp.2.1 t, hw.2.1 t]
  have he_mass (t : ℕ) : ∑ i, e t i = 0 := by
    dsimp [e]
    rw [Finset.sum_sub_distrib, hwcomp.2.2 t, hw.2.2 t, sub_self]
  have he_prop (t q : ℕ) :
      forwardProduct N.colMix (t + q) t *ᵥ e t = e (t + q) := by
    have hprod :=
      FiniteNetwork.consecutiveProduct_mulVec_eq_of_step N.colMix e t q
        (fun k _hk => he_step (t + k))
    simpa [forwardProduct] using hprod
  have he_period_mul (t m : ℕ) : e (t + p.1 * m) = e t := by
    simpa [Nat.mul_comm] using he_periodic.nat_mul m t
  have hfixed (t m : ℕ) :
      forwardProduct N.colMix (t + p.1 * m) t *ᵥ e t = e t := by
    rw [he_prop, he_period_mul]
  have hperiod_rate_nonneg : 0 ≤ mixingRate N ^ p.1 :=
    pow_nonneg (mixingRate_nonneg N) _
  have hperiod_rate_lt_one : mixingRate N ^ p.1 < 1 :=
    pow_lt_one₀ (mixingRate_nonneg N) (mixingRate_lt_one N)
      (Nat.ne_of_gt p.2)
  have hgeom : Filter.Tendsto (fun m : ℕ => (mixingRate N ^ p.1) ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      hperiod_rate_nonneg hperiod_rate_lt_one
  funext t i
  have hbound (m : ℕ) :
      nodeL2Norm (e t) ≤ columnMixingConstant N *
        mixingRate N ^ (p.1 * m) * nodeL2Norm (e t) := by
    have h := scalar_colMix_nodeL2_geometric N (t + p.1 * m) t
      (by omega) (e t) (he_mass t)
    rw [hfixed] at h
    simpa using h
  have hlimit : Filter.Tendsto
      (fun m : ℕ => columnMixingConstant N *
        mixingRate N ^ (p.1 * m) * nodeL2Norm (e t))
      Filter.atTop (nhds 0) := by
    simpa [pow_mul] using
      (hgeom.const_mul (columnMixingConstant N)).mul_const (nodeL2Norm (e t))
  have hnorm_le : nodeL2Norm (e t) ≤ 0 :=
    ge_of_tendsto' hlimit hbound
  have hnorm : nodeL2Norm (e t) = 0 :=
    le_antisymm hnorm_le (Real.sqrt_nonneg _)
  have habs : |e t i| ≤ 0 := by
    simpa [hnorm] using abs_le_nodeL2Norm (e t) i
  have hei : e t i = 0 := abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
  dsimp [e] at hei
  exact sub_eq_zero.mp hei

/-- The unique periodic forward push-mass sequence. Book
`#/key_lemmas/8/proof/0/description`:
“Periodicity and uniqueness make pi,D,b periodic; the forward push mass
converges summably to its unique periodic sequence. Sum the coboundary over
one period.” -/
def periodicPushMass (N : NetworkSetup n) (p : PositiveHorizon)
    (hp : IsPeriodicNetwork N p) : ℕ → Fin n → ℝ :=
  Classical.choose (exists_unique_periodicPushMass N p hp)

/-- The chosen periodic mass has the periodicity, forward recurrence, and
normalization that characterize the source's unique periodic sequence. Book
`#/key_lemmas/8/proof/0/description`:
“Periodicity and uniqueness make pi,D,b periodic; the forward push mass
converges summably to its unique periodic sequence. Sum the coboundary over
one period.” -/
theorem periodicPushMass_spec
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    IsPeriodicPushMass N p (periodicPushMass N p hp) :=
  (Classical.choose_spec (exists_unique_periodicPushMass N p hp)).1

/-- Source correspondence for the periodic mass: the canonical trajectory
`pushMass`, initialized at `1` and generated by the actual column schedule,
has summable difference from the selected periodic solution and hence
converges to it phasewise. Book `#/key_lemmas/8/proof/0/description`:
“Periodicity and uniqueness make pi,D,b periodic; the forward push mass
converges summably to its unique periodic sequence. Sum the coboundary over
one period.” -/
theorem pushMass_summable_to_periodicPushMass
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    Summable (fun t => pushMass N t - periodicPushMass N p hp t) ∧
      Filter.Tendsto
        (fun t => pushMass N t - periodicPushMass N p hp t)
        Filter.atTop (nhds 0) := by
  classical
  let e : ℕ → Fin n → ℝ :=
    fun t => pushMass N t - periodicPushMass N p hp t
  have he_mass (t : ℕ) : ∑ i, e t i = 0 := by
    dsimp [e]
    rw [Finset.sum_sub_distrib, pushMass_sum_eq_n,
      (periodicPushMass_spec N p hp).2.2 t, sub_self]
  have he_step (t : ℕ) : N.colMix t *ᵥ e t = e (t + 1) := by
    dsimp [e]
    rw [Matrix.mulVec_sub, ← pushMass_succ,
      ← (periodicPushMass_spec N p hp).2.1 t]
  have he_prop (t : ℕ) :
      e t = forwardProduct N.colMix t 0 *ᵥ e 0 := by
    have hprod :=
      FiniteNetwork.consecutiveProduct_mulVec_eq_of_step N.colMix e 0 t
        (fun k _hk => by simpa using he_step k)
    simpa [forwardProduct] using hprod.symm
  have hnorm_node (x : Fin n → ℝ) : ‖x‖ ≤ nodeL2Norm x := by
    rw [Pi.norm_def]
    let C : NNReal := ⟨nodeL2Norm x, Real.sqrt_nonneg _⟩
    change (↑(Finset.univ.sup fun b => ‖x b‖₊) : ℝ) ≤ (C : ℝ)
    exact_mod_cast Finset.sup_le (fun i _hi => by
      change ‖x i‖₊ ≤ C
      exact_mod_cast (by
        simpa [Real.norm_eq_abs] using abs_le_nodeL2Norm x i))
  have hnode (t : ℕ) : nodeL2Norm (e t) ≤
      columnMixingConstant N * mixingRate N ^ t * nodeL2Norm (e 0) := by
    rw [he_prop]
    simpa using scalar_colMix_nodeL2_geometric N t 0 (Nat.zero_le t)
      (e 0) (he_mass 0)
  have hnorm (t : ℕ) : ‖e t‖ ≤
      (columnMixingConstant N * nodeL2Norm (e 0)) * mixingRate N ^ t := by
    calc
      ‖e t‖ ≤ nodeL2Norm (e t) := hnorm_node (e t)
      _ ≤ columnMixingConstant N * mixingRate N ^ t * nodeL2Norm (e 0) :=
        hnode t
      _ = (columnMixingConstant N * nodeL2Norm (e 0)) *
          mixingRate N ^ t := by ring
  have hs : Summable e :=
    (summable_and_norm_tsum_le_of_geometric_bound e
      (columnMixingConstant N * nodeL2Norm (e 0)) (mixingRate N)
      (mixingRate_nonneg N) (mixingRate_lt_one N) hnorm).1
  exact ⟨hs, hs.tendsto_atTop_zero⟩

/-- The phase mean `h` on its exact source domain.  Book
`#/key_lemmas/8/proof/0/math`:
“`h={1\over p}\sum_{r<p}b_r^\top1={1\over p}\sum_{r<p}\pi_{r+1}^\top
w_r^{per}>0`”.  The preceding correspondence theorem identifies
`w_r^{per}` with the summable periodic limit of canonical `pushMass`; there
is no nonperiodic fallback value. -/
def periodicGainMean (N : NetworkSetup n) (p : PositiveHorizon)
    (hp : IsPeriodicNetwork N p) : ℝ :=
  (p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1,
    dotProduct (absoluteProbability N (r + 1)) (periodicPushMass N p hp r)

/-- The phase mean `q`. Book `#/key_lemmas/8/proof/0/math`:
“`q={1\over p}\sum_{r<p}\|b_r\|^2`”. -/
def periodicInfluenceMean (N : NetworkSetup n) (p : PositiveHorizon) : ℝ :=
  (p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1, influenceEnergy N r

/-- Block length used for the simplified periodic upper remainder. Book
`#/key_lemmas/8/proof/13/description`:
“Choose every periodic block length between m and 2m, merge the short tail,
and set m=\lceil T^{1/6}\rceil; then m\le\sqrt T, so the valid-use
restriction for (63) holds.” -/
def periodicRiskBlockLength (T : PositiveHorizon) : ℕ :=
  max 1 (Nat.ceil (Real.rpow T.1 (1 / 6)))

/-- A finite-period scalar sequence has uniformly bounded interval deviation
from its phase mean. -/
private theorem periodic_interval_sum_deviation_le
    (p : ℕ) (hp : 0 < p) (f : ℕ → ℝ) (hf : Function.Periodic f p)
    (a b : ℕ) (hab : a ≤ b) :
    |(∑ t ∈ Finset.Ico a b, f t) -
        ((b - a : ℕ) : ℝ) * ((p : ℝ)⁻¹ * ∑ r ∈ Finset.range p, f r)| ≤
      2 * ∑ r ∈ Finset.range p,
        |f r - ((p : ℝ)⁻¹ * ∑ q ∈ Finset.range p, f q)| := by
  let μ : ℝ := (p : ℝ)⁻¹ * ∑ r ∈ Finset.range p, f r
  let g : ℕ → ℝ := fun t => f t - μ
  have hg : Function.Periodic g p := by
    intro t
    dsimp [g]
    rw [hf t]
  have hperiodZero : ∑ t ∈ Finset.range p, g t = 0 := by
    dsimp [g, μ]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
    field_simp
    ring
  have hprefix : ∀ T : ℕ,
      |∑ t ∈ Finset.range T, g t| ≤
        ∑ r ∈ Finset.range p, |g r| := by
    intro T
    induction T using Nat.strong_induction_on with
    | h T ih =>
        by_cases hTp : T < p
        · calc
            |∑ t ∈ Finset.range T, g t| ≤
                ∑ t ∈ Finset.range T, |g t| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r ∈ Finset.range p, |g r| :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_mono hTp.le)
                (fun r _hr _hrt => abs_nonneg (g r))
        · have hpT : p ≤ T := le_of_not_gt hTp
          have htail :
              (∑ t ∈ Finset.Ico p T, g t) =
                ∑ t ∈ Finset.range (T - p), g t := by
            rw [Finset.sum_Ico_eq_sum_range]
            apply Finset.sum_congr rfl
            intro t _ht
            rw [show p + t = t + p by omega, hg t]
          have hreduce :
              (∑ t ∈ Finset.range T, g t) =
                ∑ t ∈ Finset.range (T - p), g t := by
            rw [← Finset.sum_range_add_sum_Ico g hpT, hperiodZero,
              zero_add, htail]
          rw [hreduce]
          exact ih (T - p) (by omega)
  have hcenter :
      (∑ t ∈ Finset.Ico a b, f t) - ((b - a : ℕ) : ℝ) * μ =
        ∑ t ∈ Finset.Ico a b, g t := by
    dsimp [g]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  change |(∑ t ∈ Finset.Ico a b, f t) - ((b - a : ℕ) : ℝ) * μ| ≤
    2 * ∑ r ∈ Finset.range p, |g r|
  rw [hcenter, Finset.sum_Ico_eq_sub _ hab]
  calc
    |(∑ t ∈ Finset.range b, g t) - ∑ t ∈ Finset.range a, g t| ≤
        |∑ t ∈ Finset.range b, g t| +
          |∑ t ∈ Finset.range a, g t| := abs_sub _ _
    _ ≤ (∑ r ∈ Finset.range p, |g r|) +
        ∑ r ∈ Finset.range p, |g r| :=
      add_le_add (hprefix b) (hprefix a)
    _ = 2 * ∑ r ∈ Finset.range p, |g r| := by ring

/-- Equation (61): periodicity identifies the phase-average influence row
with the normalized Perron overlap, and finite Cauchy--Schwarz controls its
second moment. -/
private theorem periodic_phase_coefficients
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    0 < periodicGainMean N p hp ∧
    periodicGainMean N p hp ^ 2 / n ≤ periodicInfluenceMean N p ∧
    ((p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1, ∑ i, influenceRow N r i =
      periodicGainMean N p hp) ∧
    (∀ i, (p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1, influenceRow N r i =
      periodicGainMean N p hp / n) := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  obtain ⟨seqs, hseq⟩ :=
    FiniteNetwork.exists_unique_positive_periodic_push_pull_perron_sequences
      (Node := Fin n) N.rowMix N.colMix p.1 p.2
      N.row_stochastic N.col_stochastic
      N.row_positive_diagonal N.col_positive_diagonal
      N.row_strongly_connected N.col_strongly_connected hp.1 hp.2
  rcases hseq with ⟨heq, hpositive, hunique⟩
  rcases heq with ⟨hleftStep, hleftMass, hrightStep, hrightMass⟩
  rcases hpositive with
    ⟨hleftPos, hrightPos, hleftPeriodic, hrightPeriodic⟩
  have hleftSpec : IsAbsoluteProbabilitySequence N seqs.1 := by
    refine ⟨fun t i => (hleftPos t i).le, hleftMass, ?_⟩
    intro t
    funext i
    exact hleftStep t i
  have hleftEq : seqs.1 = absoluteProbability N :=
    (exists_unique_absoluteProbabilitySequence N).unique hleftSpec
      (absoluteProbability_spec N)
  let w : ℕ → Fin n → ℝ := fun t i => (n : ℝ) * seqs.2 t i
  have hwSpec : IsPeriodicPushMass N p w := by
    refine ⟨?_, ?_, ?_⟩
    · intro t
      funext i
      exact congrArg (fun x : ℝ => (n : ℝ) * x)
        (congrFun (hrightPeriodic t) i)
    · intro t
      funext i
      calc
        w (t + 1) i = (n : ℝ) * seqs.2 (t + 1) i := rfl
        _ = (n : ℝ) * (N.colMix t *ᵥ seqs.2 t) i := by
          rw [hrightStep t i]
        _ = (N.colMix t *ᵥ w t) i := by
          simp [w, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc,
            mul_comm, mul_left_comm]
    · intro t
      simp only [w, ← Finset.mul_sum, hrightMass t]
      ring
  have hwEq : w = periodicPushMass N p hp :=
    (exists_unique_periodicPushMass N p hp).unique hwSpec
      (periodicPushMass_spec N p hp)
  let v : ℕ → Fin n → ℝ :=
    fun t i => periodicPushMass N p hp t i / (n : ℝ)
  have hnR : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.hn)
  have hvEq : v = seqs.2 := by
    funext t i
    have hwi := congrFun (congrFun hwEq t) i
    dsimp [v, w] at hwi ⊢
    rw [← hwi]
    field_simp
  have hpiPeriodic : Function.Periodic (absoluteProbability N) p.1 := by
    rw [← hleftEq]
    exact hleftPeriodic
  have hvPeriodic : Function.Periodic v p.1 := by
    rw [hvEq]
    exact hrightPeriodic
  have hoverlapPos : 0 < FiniteNetwork.averagePeriodicPerronOverlap
      (p := p.1) (absoluteProbability N) v := by
    apply FiniteNetwork.averagePeriodicPerronOverlap_pos
      (absoluteProbability N) v p.2
    · intro r i
      rw [← hleftEq]
      exact hleftPos _ _
    · intro r i
      rw [hvEq]
      exact hrightPos _ _
  have hoverlapEq : FiniteNetwork.averagePeriodicPerronOverlap
      (p := p.1) (absoluteProbability N) v =
      periodicGainMean N p hp / (n : ℝ) := by
    unfold FiniteNetwork.averagePeriodicPerronOverlap periodicGainMean
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ => ∑ i : Fin n, absoluteProbability N (r + 1) i * v r i)]
    have hinner (r : ℕ) :
        (∑ i, absoluteProbability N (r + 1) i * v r i) =
          dotProduct (absoluteProbability N (r + 1))
            (periodicPushMass N p hp r) / (n : ℝ) := by
      simp only [v, dotProduct, div_eq_mul_inv, mul_assoc,
        Finset.sum_mul]
    simp_rw [hinner]
    rw [← Finset.sum_div]
    ring
  have haverage :=
    FiniteNetwork.periodicInfluenceAverage_eq_averagePerronOverlap
      N.colMix (absoluteProbability N) v hp.2 hpiPeriodic
      (by simpa using hvPeriodic 0)
      (fun t _ht => periodicInfluenceSeries_summable N t)
      (fun t _ht j => Matrix.sum_col_of_mem_colStochastic
        (N.col_stochastic t) j)
      (fun t _ht => by rw [hvEq]; exact hrightMass t)
      (fun t _ht => by rw [hvEq]; funext i; exact hrightStep t i)
      (fun t _ht i => by
        simpa [influenceSeriesTerm] using
          influenceSeries_summable N t
            (FiniteNetwork.normalizedCoordinateError (v t) i
              (by rw [hvEq]; exact hrightMass t)))
  have hsourceSummable :
      Summable (fun t => pushMass N t - periodicPushMass N p hp t) :=
    (pushMass_summable_to_periodicPushMass N p hp).1
  have hcoord (i : Fin n) :
      (p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1, influenceRow N r i =
        periodicGainMean N p hp / (n : ℝ) := by
    have hi := congrFun haverage i
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ =>
        FiniteNetwork.periodicInfluence N.colMix
          (absoluteProbability N) r i)] at hi
    simpa only [← influenceRow_eq_periodicInfluence, hoverlapEq] using hi
  have hsum :
      (p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1, ∑ i, influenceRow N r i =
        periodicGainMean N p hp := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    simp_rw [hcoord]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hh : 0 < periodicGainMean N p hp := by
    have hdiv : 0 < periodicGainMean N p hp / (n : ℝ) := by
      rw [← hoverlapEq]
      exact hoverlapPos
    calc
      0 < (periodicGainMean N p hp / (n : ℝ)) * (n : ℝ) :=
        mul_pos hdiv (Nat.cast_pos.mpr N.hn)
      _ = periodicGainMean N p hp := by field_simp
  have hcauchy :=
    FiniteNetwork.periodicInfluenceGain_sq_le_card_mul_secondMoment
      (fun r : Fin p.1 => influenceRow N r.1)
  rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ => ∑ i : Fin n, influenceRow N r i),
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ => ∑ i : Fin n, (influenceRow N r i) ^ 2)] at hcauchy
  have hcauchy' :
      ((p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1,
          ∑ i, influenceRow N r i) ^ 2 ≤
        (n : ℝ) * periodicInfluenceMean N p := by
    simpa only [Fintype.card_fin, periodicInfluenceMean, influenceEnergy]
      using hcauchy
  rw [hsum] at hcauchy'
  have hhq : periodicGainMean N p hp ^ 2 / (n : ℝ) ≤
      periodicInfluenceMean N p := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr N.hn)).2
    simpa [mul_comm] using hcauchy'
  exact ⟨hh, hhq, hsum, hcoord⟩

/-- Uniform interval deviations used in the periodic comparator, block upper,
and quadratic lower routes. -/
private theorem periodic_interval_deviation_bounds
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain Cenergy : ℝ, 0 ≤ Cgain ∧ 0 ≤ Cenergy ∧
      ∀ a b : ℕ, a ≤ b →
        |(∑ t ∈ Finset.Ico a b, gain N t) -
            ((b - a : ℕ) : ℝ) * periodicGainMean N p hp| ≤ Cgain ∧
        |(∑ t ∈ Finset.Ico a b, influenceEnergy N t) -
            ((b - a : ℕ) : ℝ) * periodicInfluenceMean N p| ≤ Cenergy := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp N.hn
  obtain ⟨seqs, hseq⟩ :=
    FiniteNetwork.exists_unique_positive_periodic_push_pull_perron_sequences
      (Node := Fin n) N.rowMix N.colMix p.1 p.2
      N.row_stochastic N.col_stochastic
      N.row_positive_diagonal N.col_positive_diagonal
      N.row_strongly_connected N.col_strongly_connected hp.1 hp.2
  rcases hseq with ⟨heq, hpositive, hunique⟩
  rcases heq with ⟨hleftStep, hleftMass, hrightStep, hrightMass⟩
  rcases hpositive with
    ⟨hleftPos, hrightPos, hleftPeriodic, hrightPeriodic⟩
  have hleftSpec : IsAbsoluteProbabilitySequence N seqs.1 := by
    refine ⟨fun t i => (hleftPos t i).le, hleftMass, ?_⟩
    intro t
    funext i
    exact hleftStep t i
  have hleftEq : seqs.1 = absoluteProbability N :=
    (exists_unique_absoluteProbabilitySequence N).unique hleftSpec
      (absoluteProbability_spec N)
  have hpiPeriodic : Function.Periodic (absoluteProbability N) p.1 := by
    rw [← hleftEq]
    exact hleftPeriodic
  let gainPer : ℕ → ℝ := fun t =>
    dotProduct (absoluteProbability N (t + 1))
      (periodicPushMass N p hp t)
  have hgainPerPeriodic : Function.Periodic gainPer p.1 := by
    intro t
    dsimp [gainPer]
    rw [show t + p.1 + 1 = (t + 1) + p.1 by omega,
      hpiPeriodic (t + 1), (periodicPushMass_spec N p hp).1 t]
  have hrowPeriodic : Function.Periodic (influenceRow N) p.1 := by
    intro t
    rw [influenceRow_eq_periodicInfluence,
      influenceRow_eq_periodicInfluence]
    exact FiniteNetwork.periodicInfluence_periodic hp.2 hpiPeriodic t
  have henergyPeriodic : Function.Periodic (influenceEnergy N) p.1 := by
    intro t
    unfold influenceEnergy
    rw [hrowPeriodic t]
  let CgainPer : ℝ :=
    2 * ∑ r ∈ Finset.range p.1,
      |gainPer r - periodicGainMean N p hp|
  let Cenergy : ℝ :=
    2 * ∑ r ∈ Finset.range p.1,
      |influenceEnergy N r - periodicInfluenceMean N p|
  have hgainPerDeviation (a b : ℕ) (hab : a ≤ b) :
      |(∑ t ∈ Finset.Ico a b, gainPer t) -
          ((b - a : ℕ) : ℝ) * periodicGainMean N p hp| ≤ CgainPer := by
    simpa [CgainPer, gainPer, periodicGainMean] using
      periodic_interval_sum_deviation_le p.1 p.2 gainPer
        hgainPerPeriodic a b hab
  have henergyDeviation (a b : ℕ) (hab : a ≤ b) :
      |(∑ t ∈ Finset.Ico a b, influenceEnergy N t) -
          ((b - a : ℕ) : ℝ) * periodicInfluenceMean N p| ≤ Cenergy := by
    simpa [Cenergy, periodicInfluenceMean] using
      periodic_interval_sum_deviation_le p.1 p.2 (influenceEnergy N)
        henergyPeriodic a b hab
  let e : ℕ → Fin n → ℝ :=
    fun t => pushMass N t - periodicPushMass N p hp t
  let z : ℕ → ℝ := fun t =>
    dotProduct (absoluteProbability N (t + 1)) (e t)
  have he : Summable e :=
    (pushMass_summable_to_periodicPushMass N p hp).1
  have hzBound (t : ℕ) : |z t| ≤ ‖e t‖ := by
    rcases absoluteProbability_spec N with ⟨hpiNonneg, hpiMass, _hpiStep⟩
    calc
      |z t| ≤ ∑ i, |absoluteProbability N (t + 1) i * e t i| := by
        dsimp [z, dotProduct]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, absoluteProbability N (t + 1) i * |e t i| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul, abs_of_nonneg (hpiNonneg (t + 1) i)]
      _ ≤ ∑ i, absoluteProbability N (t + 1) i * ‖e t‖ := by
        apply Finset.sum_le_sum
        intro i _hi
        apply mul_le_mul_of_nonneg_left _ (hpiNonneg (t + 1) i)
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (e t) i
      _ = ‖e t‖ := by
        rw [← Finset.sum_mul, hpiMass (t + 1), one_mul]
  have hz : Summable z := by
    apply Summable.of_norm_bounded he.norm
    intro t
    simpa [Real.norm_eq_abs] using hzBound t
  let Ctrans : ℝ := ∑' t : ℕ, |z t|
  have htransNonneg : 0 ≤ Ctrans := tsum_nonneg fun _ => abs_nonneg _
  have htransDeviation (a b : ℕ) :
      |∑ t ∈ Finset.Ico a b, z t| ≤ Ctrans := by
    calc
      |∑ t ∈ Finset.Ico a b, z t| ≤
          ∑ t ∈ Finset.Ico a b, |z t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑' t : ℕ, |z t| := by
        simpa [Real.norm_eq_abs] using
          hz.norm.sum_le_tsum (Finset.Ico a b)
            (fun t _ht => norm_nonneg (z t))
      _ = Ctrans := rfl
  have hgainSplit (t : ℕ) : gain N t = gainPer t + z t := by
    unfold gain
    dsimp [gainPer, z, e]
    simp only [dotProduct]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Pi.sub_apply]
    ring
  refine ⟨CgainPer + Ctrans, Cenergy, ?_, ?_, ?_⟩
  · exact add_nonneg (by
      dsimp [CgainPer]
      positivity) htransNonneg
  · dsimp [Cenergy]
    positivity
  · intro a b hab
    constructor
    · have hdecomp :
          (∑ t ∈ Finset.Ico a b, gain N t) -
              ((b - a : ℕ) : ℝ) * periodicGainMean N p hp =
            ((∑ t ∈ Finset.Ico a b, gainPer t) -
                ((b - a : ℕ) : ℝ) * periodicGainMean N p hp) +
              ∑ t ∈ Finset.Ico a b, z t := by
        simp_rw [hgainSplit, Finset.sum_add_distrib]
        ring
      rw [hdecomp]
      exact (abs_add_le _ _).trans
        (add_le_add (hgainPerDeviation a b hab) (htransDeviation a b))
    · exact henergyDeviation a b hab

/-- The scalar quadratic remainder used in the periodic logarithmic product
expansion (source proof step 18). -/
private theorem log_one_sub_add_abs_le_two_sq
    (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hbase : 0 < 1 - x := by linarith
  have hupper : Real.log (1 - x) + x ≤ 0 := by
    have hlog := Real.log_le_sub_one_of_pos hbase
    linarith
  have hinv : 0 < (1 - x)⁻¹ := inv_pos.mpr hbase
  have hlogInv := Real.log_le_sub_one_of_pos hinv
  have hrat : (1 - x)⁻¹ - 1 ≤ x + 2 * x ^ 2 := by
    field_simp [ne_of_gt hbase]
    nlinarith [sq_nonneg x]
  have hlower : -(2 * x ^ 2) ≤ Real.log (1 - x) + x := by
    rw [Real.log_inv] at hlogInv
    linarith
  rw [abs_of_nonpos hupper]
  linarith

/-- A finite exponential geometric mass differs from the reciprocal decay
rate only by a unit discretization error and its explicit terminal tail. -/
private theorem finite_exp_geometric_sum_reciprocal_bounds
    (lambda : ℝ) (T : ℕ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1) :
    1 / lambda -
        Real.exp (-(lambda * (T : ℝ))) * (1 + lambda) / lambda ≤
      ∑ t ∈ Finset.range T, Real.exp (-(lambda * (t : ℝ))) ∧
    (∑ t ∈ Finset.range T, Real.exp (-(lambda * (t : ℝ)))) ≤
      1 / lambda + 1 := by
  let r : ℝ := Real.exp (-lambda)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    exact (Real.exp_lt_one_iff).2 (by linarith)
  have hden : 0 < 1 - r := sub_pos.mpr hrlt
  have hdenUpper : 1 - r ≤ lambda := by
    have h := Real.one_sub_le_exp_neg lambda
    dsimp [r]
    linarith
  have hexpInv : r ≤ 1 / (1 + lambda) := by
    dsimp [r]
    rw [Real.exp_neg]
    have hadd : 1 + lambda ≤ Real.exp lambda := by
      simpa [add_comm] using Real.add_one_le_exp lambda
    simpa [one_div] using
      (one_div_le_one_div_of_le (by linarith : 0 < 1 + lambda) hadd)
  have hdenLower : lambda / (1 + lambda) ≤ 1 - r := by
    have hdenOne : 0 < 1 + lambda := by linarith
    apply (div_le_iff₀ hdenOne).2
    have hscaled := mul_le_mul_of_nonneg_left hexpInv hdenOne.le
    field_simp [ne_of_gt hdenOne] at hscaled ⊢
    linarith
  have hsumEq :
      (∑ t ∈ Finset.range T, Real.exp (-(lambda * (t : ℝ)))) =
        (1 - r ^ T) / (1 - r) := by
    have hterm (t : ℕ) : Real.exp (-(lambda * (t : ℝ))) = r ^ t := by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp_rw [hterm]
    rw [geom_sum_eq (ne_of_lt hrlt)]
    have hrsub : r - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hrlt)
    field_simp [hrsub, ne_of_gt hden]
    ring
  have hrpow : 0 ≤ r ^ T := (pow_pos hrpos T).le
  have htailCoef : 1 / (1 - r) ≤ (1 + lambda) / lambda := by
    have hlambdaDen : 0 < lambda / (1 + lambda) := by positivity
    have hinv := one_div_le_one_div_of_le hlambdaDen hdenLower
    field_simp [ne_of_gt hlambda, ne_of_gt (by linarith : 0 < 1 + lambda)] at hinv ⊢
    exact hinv
  have hmainCoef : 1 / lambda ≤ 1 / (1 - r) :=
    one_div_le_one_div_of_le hden hdenUpper
  rw [hsumEq]
  constructor
  · have htail : r ^ T / (1 - r) ≤
        r ^ T * (1 + lambda) / lambda := by
      have hm := mul_le_mul_of_nonneg_left htailCoef hrpow
      convert hm using 1 <;> ring
    have hsplit : (1 - r ^ T) / (1 - r) =
        1 / (1 - r) - r ^ T / (1 - r) := by ring
    rw [hsplit]
    have hrpowExp : r ^ T = Real.exp (-(lambda * (T : ℝ))) := by
      dsimp [r]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hrpowExp] at htail ⊢
    linarith
  · have hnum : 1 - r ^ T ≤ 1 := by linarith
    have hquot : (1 - r ^ T) / (1 - r) ≤ 1 / (1 - r) :=
      div_le_div_of_nonneg_right hnum hden.le
    have hcoefUpper : 1 / (1 - r) ≤ 1 / lambda + 1 := by
      calc
        1 / (1 - r) ≤ (1 + lambda) / lambda := htailCoef
        _ = 1 / lambda + 1 := by field_simp [ne_of_gt hlambda]
    exact hquot.trans hcoefUpper

/-- Source proof step 18 at interval granularity: periodic gain deviations
control the linear part of the logarithm, while the scalar remainder is
quadratic in the dimensionless stepsize. -/
private theorem periodic_gain_product_log_expansion
    (N : NetworkSetup n) (h Cgain s : ℝ) (a b : ℕ) (hab : a ≤ b)
    (hs : 0 < s) (hsn : s * (n : ℝ) ≤ 1 / 2)
    (hdev : |(∑ t ∈ Finset.Ico a b, gain N t) -
      ((b - a : ℕ) : ℝ) * h| ≤ Cgain) :
    |Real.log (∏ t ∈ Finset.Ico a b, (1 - s * gain N t)) +
        s * ((b - a : ℕ) : ℝ) * h| ≤
      s * Cgain + 2 * s ^ 2 * (n : ℝ) ^ 2 * ((b - a : ℕ) : ℝ) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hgain0 (t : ℕ) : 0 ≤ gain N t := by
    unfold gain dotProduct
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg ((absoluteProbability_spec N).1 (t + 1) i)
        (pushMass_nonneg N t i)
  have hsmall (t : ℕ) : s * gain N t ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_left (gain_le_n N t) hs.le).trans hsn
  have hfactor (t : ℕ) : 0 < 1 - s * gain N t := by
    linarith [hsmall t]
  rw [Real.log_prod (fun t _ => ne_of_gt (hfactor t))]
  have hremainder :
      |∑ t ∈ Finset.Ico a b,
          (Real.log (1 - s * gain N t) + s * gain N t)| ≤
        2 * s ^ 2 * (n : ℝ) ^ 2 * ((b - a : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ t ∈ Finset.Ico a b,
          |Real.log (1 - s * gain N t) + s * gain N t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.Ico a b, 2 * s ^ 2 * (n : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        calc
          |Real.log (1 - s * gain N t) + s * gain N t| ≤
              2 * (s * gain N t) ^ 2 :=
            log_one_sub_add_abs_le_two_sq _
              (mul_nonneg hs.le (hgain0 t)) (hsmall t)
          _ ≤ 2 * s ^ 2 * (n : ℝ) ^ 2 := by
            have hg := gain_le_n N t
            nlinarith [sq_nonneg (gain N t),
              mul_nonneg (sub_nonneg.mpr hg) (add_nonneg (hgain0 t) hn.le)]
      _ = 2 * s ^ 2 * (n : ℝ) ^ 2 * ((b - a : ℕ) : ℝ) := by
        simp [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        ring
  have hrewrite :
      (∑ t ∈ Finset.Ico a b, Real.log (1 - s * gain N t)) +
          s * ((b - a : ℕ) : ℝ) * h =
        (∑ t ∈ Finset.Ico a b,
            (Real.log (1 - s * gain N t) + s * gain N t)) -
          s * ((∑ t ∈ Finset.Ico a b, gain N t) -
            ((b - a : ℕ) : ℝ) * h) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hrewrite]
  calc
    _ ≤ |∑ t ∈ Finset.Ico a b,
          (Real.log (1 - s * gain N t) + s * gain N t)| +
        |s * ((∑ t ∈ Finset.Ico a b, gain N t) -
          ((b - a : ℕ) : ℝ) * h)| := abs_sub _ _
    _ ≤ 2 * s ^ 2 * (n : ℝ) ^ 2 * ((b - a : ℕ) : ℝ) +
        s * Cgain := by
      rw [abs_mul, abs_of_pos hs]
      exact add_le_add hremainder (mul_le_mul_of_nonneg_left hdev hs.le)
    _ = _ := by ring

/-- The network-level form of source proof step 18, obtained directly from
the periodic interval-deviation scaffold. -/
private theorem periodic_gain_product_log_expansion_uniform
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain : ℝ, 0 ≤ Cgain ∧
      ∀ s : ℝ, 0 < s → s * (n : ℝ) ≤ 1 / 2 →
      ∀ a b : ℕ, a ≤ b →
        |Real.log (∏ t ∈ Finset.Ico a b, (1 - s * gain N t)) +
            s * ((b - a : ℕ) : ℝ) * periodicGainMean N p hp| ≤
          s * Cgain +
            2 * s ^ 2 * (n : ℝ) ^ 2 * ((b - a : ℕ) : ℝ) := by
  obtain ⟨Cgain, Cenergy, hCgain, hCenergy, hinterval⟩ :=
    periodic_interval_deviation_bounds N p hp
  refine ⟨Cgain, hCgain, ?_⟩
  intro s hs hsn a b hab
  exact periodic_gain_product_log_expansion N
    (periodicGainMean N p hp) Cgain s a b hab hs hsn
    (hinterval a b hab).1

/-- Exponentiated form of the periodic logarithmic expansion.  Unlike a
constant-factor contraction envelope, its exponent retains the exact
`s * h * length` term and isolates the quadratic correction required for the
energy summations in source proof steps 19--20. -/
private theorem periodic_gain_product_exp_sandwich
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain : ℝ, 0 ≤ Cgain ∧
      ∀ s : ℝ, 0 < s → s * (n : ℝ) ≤ 1 / 2 →
      ∀ a b : ℕ, a ≤ b →
        let len : ℝ := ((b - a : ℕ) : ℝ)
        let err : ℝ := s * Cgain + 2 * s ^ 2 * (n : ℝ) ^ 2 * len
        Real.exp (-s * len * periodicGainMean N p hp - err) ≤
            ∏ t ∈ Finset.Ico a b, (1 - s * gain N t) ∧
          (∏ t ∈ Finset.Ico a b, (1 - s * gain N t)) ≤
            Real.exp (-s * len * periodicGainMean N p hp + err) := by
  obtain ⟨Cgain, hCgain, hlog⟩ :=
    periodic_gain_product_log_expansion_uniform N p hp
  refine ⟨Cgain, hCgain, ?_⟩
  intro s hs hsn a b hab
  dsimp only
  let P : ℝ := ∏ t ∈ Finset.Ico a b, (1 - s * gain N t)
  let err : ℝ :=
    s * Cgain + 2 * s ^ 2 * (n : ℝ) ^ 2 * ((b - a : ℕ) : ℝ)
  have hgain0 (t : ℕ) : 0 ≤ gain N t := by
    unfold gain dotProduct
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg ((absoluteProbability_spec N).1 (t + 1) i)
        (pushMass_nonneg N t i)
  have hfactor (t : ℕ) : 0 < 1 - s * gain N t := by
    have hsmall :=
      (mul_le_mul_of_nonneg_left (gain_le_n N t) hs.le).trans hsn
    linarith
  have hP : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun t ht => hfactor t
  have hlogP :
      |Real.log P + s * ((b - a : ℕ) : ℝ) *
          periodicGainMean N p hp| ≤ err := by
    dsimp [P, err]
    exact hlog s hs hsn a b hab
  have hlower :
      -s * ((b - a : ℕ) : ℝ) * periodicGainMean N p hp - err ≤
        Real.log P := by
    linarith [(abs_le.mp hlogP).1]
  have hupper :
      Real.log P ≤
        -s * ((b - a : ℕ) : ℝ) * periodicGainMean N p hp + err := by
    linarith [(abs_le.mp hlogP).2]
  constructor
  · calc
      Real.exp (-s * ((b - a : ℕ) : ℝ) * periodicGainMean N p hp - err) ≤
          Real.exp (Real.log P) := Real.exp_le_exp.mpr hlower
      _ = P := Real.exp_log hP
  · calc
      P = Real.exp (Real.log P) := (Real.exp_log hP).symm
      _ ≤ Real.exp (-s * ((b - a : ℕ) : ℝ) *
          periodicGainMean N p hp + err) := Real.exp_le_exp.mpr hupper

/-- Source proof step 19 reduced to scalar exponential masses.  The two rates
differ from `2*s*h` only by the signed quadratic logarithmic correction. -/
private theorem periodic_signal_product_energy_exponential_squeeze
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain : ℝ, 0 ≤ Cgain ∧
      ∀ s : ℝ, 0 < s → s * (n : ℝ) ≤ 1 / 2 →
      4 * s * (n : ℝ) ^ 2 < periodicGainMean N p hp →
      2 * s * periodicGainMean N p hp + 4 * s ^ 2 * (n : ℝ) ^ 2 ≤ 1 →
      ∀ T : ℕ,
        let lambdaLo :=
          2 * s * periodicGainMean N p hp - 4 * s ^ 2 * (n : ℝ) ^ 2
        let lambdaHi :=
          2 * s * periodicGainMean N p hp + 4 * s ^ 2 * (n : ℝ) ^ 2
        Real.exp (-2 * s * Cgain) *
              (1 / lambdaHi -
                Real.exp (-(lambdaHi * (T : ℝ))) * (1 + lambdaHi) / lambdaHi) ≤
            ∑ t ∈ Finset.range T,
              (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 ∧
          (∑ t ∈ Finset.range T,
              (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2) ≤
            Real.exp (2 * s * Cgain) * (1 / lambdaLo + 1) := by
  obtain ⟨Cgain, hCgain, hprod⟩ := periodic_gain_product_exp_sandwich N p hp
  refine ⟨Cgain, hCgain, ?_⟩
  intro s hs hsn hsrate hlambdaHiOne T
  dsimp only
  let lambdaLo : ℝ :=
    2 * s * periodicGainMean N p hp - 4 * s ^ 2 * (n : ℝ) ^ 2
  let lambdaHi : ℝ :=
    2 * s * periodicGainMean N p hp + 4 * s ^ 2 * (n : ℝ) ^ 2
  have hlambdaLo : 0 < lambdaLo := by
    dsimp [lambdaLo]
    have hgap : 0 < periodicGainMean N p hp - 4 * s * (n : ℝ) ^ 2 := by
      linarith
    nlinarith [mul_pos hs hgap]
  have hlambdaHi : 0 < lambdaHi := by
    dsimp [lambdaHi]
    have hh := (periodic_phase_coefficients N p hp).1
    positivity
  have hlambdaLoOne : lambdaLo ≤ 1 := by
    dsimp [lambdaLo]
    nlinarith [sq_nonneg s, sq_nonneg (n : ℝ)]
  have hlambdaHiOne' : lambdaHi ≤ 1 := by
    simpa [lambdaHi] using hlambdaHiOne
  have hsumsLo := finite_exp_geometric_sum_reciprocal_bounds
    lambdaLo T hlambdaLo hlambdaLoOne
  have hsumsHi := finite_exp_geometric_sum_reciprocal_bounds
    lambdaHi T hlambdaHi hlambdaHiOne'
  have hpoint (t : ℕ) :
      Real.exp (-2 * s * Cgain) *
          Real.exp (-(lambdaHi * (t : ℝ))) ≤
        (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 ∧
      (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 ≤
        Real.exp (2 * s * Cgain) *
          Real.exp (-(lambdaLo * (t : ℝ))) := by
    have hprodPoint := hprod s hs hsn 0 t (Nat.zero_le t)
    dsimp only [Nat.sub_zero, Nat.cast_id] at hprodPoint
    let P : ℝ := ∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)
    let elo : ℝ := Real.exp
      (-s * (t : ℝ) * periodicGainMean N p hp -
        (s * Cgain + 2 * s ^ 2 * (n : ℝ) ^ 2 * (t : ℝ)))
    let ehi : ℝ := Real.exp
      (-s * (t : ℝ) * periodicGainMean N p hp +
        (s * Cgain + 2 * s ^ 2 * (n : ℝ) ^ 2 * (t : ℝ)))
    have hPpos : 0 < P := lt_of_lt_of_le (Real.exp_pos _) hprodPoint.1
    have hsquareLo : elo ^ 2 ≤ P ^ 2 :=
      (sq_le_sq₀ (Real.exp_pos _).le hPpos.le).2 hprodPoint.1
    have hsquareHi : P ^ 2 ≤ ehi ^ 2 :=
      (sq_le_sq₀ hPpos.le (Real.exp_pos _).le).2 hprodPoint.2
    constructor
    · calc
        Real.exp (-2 * s * Cgain) * Real.exp (-(lambdaHi * (t : ℝ))) =
            elo ^ 2 := by
          dsimp [elo, lambdaHi]
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          congr 1
          ring
        _ ≤ P ^ 2 := hsquareLo
    · calc
        P ^ 2 ≤ ehi ^ 2 := hsquareHi
        _ = Real.exp (2 * s * Cgain) *
            Real.exp (-(lambdaLo * (t : ℝ))) := by
          dsimp [ehi, lambdaLo]
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          congr 1
          ring
  constructor
  · calc
      Real.exp (-2 * s * Cgain) *
            (1 / lambdaHi -
              Real.exp (-(lambdaHi * (T : ℝ))) * (1 + lambdaHi) / lambdaHi) ≤
          Real.exp (-2 * s * Cgain) *
            (∑ t ∈ Finset.range T,
              Real.exp (-(lambdaHi * (t : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsumsHi.1 (Real.exp_pos _).le
      _ = ∑ t ∈ Finset.range T,
            Real.exp (-2 * s * Cgain) *
              Real.exp (-(lambdaHi * (t : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ ∑ t ∈ Finset.range T,
            (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 := by
        exact Finset.sum_le_sum fun t ht => (hpoint t).1
  · calc
      (∑ t ∈ Finset.range T,
          (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2) ≤
          ∑ t ∈ Finset.range T,
            Real.exp (2 * s * Cgain) *
              Real.exp (-(lambdaLo * (t : ℝ))) := by
        exact Finset.sum_le_sum fun t ht => (hpoint t).2
      _ = Real.exp (2 * s * Cgain) *
          (∑ t ∈ Finset.range T,
            Real.exp (-(lambdaLo * (t : ℝ)))) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (2 * s * Cgain) * (1 / lambdaLo + 1) :=
        mul_le_mul_of_nonneg_left hsumsLo.2 (Real.exp_pos _).le

/-- The arbitrary-start product mass used in source steps 19--20.  The
auxiliary exponential rates have been eliminated: their quadratic
perturbation contributes only a uniform constant, while the finite terminal
loss is retained explicitly. -/
private theorem periodic_shifted_product_energy_tail_bound
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ K sCap : ℝ, 0 ≤ K ∧ 0 < sCap ∧
      ∀ s : ℝ, 0 < s → s ≤ sCap → ∀ a U : ℕ,
        |(∑ u ∈ Finset.range U,
            (∏ r ∈ Finset.Ico a (a + u), (1 - s * gain N r)) ^ 2) -
            1 / (2 * s * periodicGainMean N p hp)| ≤
          K + K * Real.exp
            (-(s * periodicGainMean N p hp * (U : ℝ))) / s := by
  obtain ⟨Cgain, hCgain, hprod⟩ :=
    periodic_gain_product_exp_sandwich N p hp
  have hh := (periodic_phase_coefficients N p hp).1
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  let h := periodicGainMean N p hp
  let nr : ℝ := n
  let sCap : ℝ :=
    min 1 (min (1 / (2 * nr))
      (min (h / (8 * nr ^ 2))
        (min (1 / (4 * h))
          (min (1 / (8 * nr ^ 2)) (1 / (2 * (Cgain + 1)))))))
  let K : ℝ :=
    4 * Cgain / h + 2 * nr ^ 2 / h ^ 2 + 3 + 1 / h
  have hnr : 0 < nr := by simpa [nr] using hn
  have hh' : 0 < h := by simpa [h] using hh
  have hsCap : 0 < sCap := by
    dsimp [sCap, h, nr]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K, h, nr]
    positivity
  refine ⟨K, sCap, hK, hsCap, ?_⟩
  intro s hs hsCap' a U
  have hs_one : s ≤ 1 := hsCap'.trans (by
    dsimp [sCap]
    exact min_le_left _ _)
  have hs_n : s * nr ≤ 1 / 2 := by
    have hc : s ≤ 1 / (2 * nr) := hsCap'.trans (by
      dsimp [sCap]
      exact (min_le_right _ _).trans (min_le_left _ _))
    calc
      s * nr ≤ (1 / (2 * nr)) * nr :=
        mul_le_mul_of_nonneg_right hc hnr.le
      _ = 1 / 2 := by field_simp [ne_of_gt hnr]
  have hs_h8n : s ≤ h / (8 * nr ^ 2) := hsCap'.trans (by
    dsimp [sCap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hs_4h : s ≤ 1 / (4 * h) := hsCap'.trans (by
    dsimp [sCap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hs_8n : s ≤ 1 / (8 * nr ^ 2) := hsCap'.trans (by
    dsimp [sCap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _)))))
  have hs_C : s ≤ 1 / (2 * (Cgain + 1)) := hsCap'.trans (by
    dsimp [sCap]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))))
  have hsmallRate : 4 * s * nr ^ 2 ≤ h / 2 := by
    calc
      4 * s * nr ^ 2 ≤ 4 * (h / (8 * nr ^ 2)) * nr ^ 2 := by
        gcongr
      _ = h / 2 := by field_simp [ne_of_gt hnr]; ring
  have hsn : s * (n : ℝ) ≤ 1 / 2 := by simpa [nr] using hs_n
  let lambdaLo : ℝ := 2 * s * h - 4 * s ^ 2 * nr ^ 2
  let lambdaHi : ℝ := 2 * s * h + 4 * s ^ 2 * nr ^ 2
  have hlambdaLo_lower : s * h ≤ lambdaLo := by
    dsimp [lambdaLo]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsmallRate)]
  have hlambdaLo : 0 < lambdaLo := (mul_pos hs hh).trans_le hlambdaLo_lower
  have hlambdaHi_lower : 2 * s * h ≤ lambdaHi := by
    dsimp [lambdaHi]
    nlinarith [sq_nonneg s, sq_nonneg nr]
  have hlambdaHi : 0 < lambdaHi := (mul_pos (by positivity) hh).trans_le
    hlambdaHi_lower
  have hquadHalf : 4 * s ^ 2 * nr ^ 2 ≤ 1 / 2 := by
    have hsSq : s ^ 2 ≤ s := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hs_one)]
    calc
      4 * s ^ 2 * nr ^ 2 ≤ 4 * s * nr ^ 2 := by gcongr
      _ ≤ 4 * (1 / (8 * nr ^ 2)) * nr ^ 2 := by gcongr
      _ = 1 / 2 := by field_simp [ne_of_gt hnr]; ring
  have hlinearHalf : 2 * s * h ≤ 1 / 2 := by
    calc
      2 * s * h ≤ 2 * (1 / (4 * h)) * h := by gcongr
      _ = 1 / 2 := by field_simp [ne_of_gt hh']; ring
  have hlambdaHi_one : lambdaHi ≤ 1 := by
    dsimp [lambdaHi]
    linarith
  have hlambdaLo_one : lambdaLo ≤ 1 := by
    dsimp [lambdaLo]
    nlinarith [sq_nonneg s, sq_nonneg nr]
  have hxC0 : 0 ≤ 2 * s * Cgain := by positivity
  have hxC1 : 2 * s * Cgain ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_right hs_C
      (by positivity : 0 ≤ 2 * (Cgain + 1))
    field_simp [show Cgain + 1 ≠ 0 by positivity] at hm
    nlinarith [mul_nonneg hs.le hCgain]
  have hexpUpper : Real.exp (2 * s * Cgain) ≤ 1 + 4 * s * Cgain := by
    convert Real.exp_le_one_add_two_mul_of_mem_Icc_zero_one
      (Set.mem_Icc.mpr ⟨hxC0, hxC1⟩) using 1 <;> ring
  have hexpUpperThree : Real.exp (2 * s * Cgain) ≤ 3 := by
    have : 4 * s * Cgain ≤ 2 := by nlinarith
    linarith
  have hexpNegUpper : Real.exp (-2 * s * Cgain) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have honeSubExp : 1 - Real.exp (-2 * s * Cgain) ≤ 2 * s * Cgain := by
    have he := Real.add_one_le_exp (-2 * s * Cgain)
    linarith
  have hsumsLo := finite_exp_geometric_sum_reciprocal_bounds
    lambdaLo U hlambdaLo hlambdaLo_one
  have hsumsHi := finite_exp_geometric_sum_reciprocal_bounds
    lambdaHi U hlambdaHi hlambdaHi_one
  let mass : ℝ := ∑ u ∈ Finset.range U,
    (∏ r ∈ Finset.Ico a (a + u), (1 - s * gain N r)) ^ 2
  have hpoint (u : ℕ) :
      Real.exp (-2 * s * Cgain) *
          Real.exp (-(lambdaHi * (u : ℝ))) ≤
        (∏ r ∈ Finset.Ico a (a + u), (1 - s * gain N r)) ^ 2 ∧
      (∏ r ∈ Finset.Ico a (a + u), (1 - s * gain N r)) ^ 2 ≤
        Real.exp (2 * s * Cgain) *
          Real.exp (-(lambdaLo * (u : ℝ))) := by
    have hp := hprod s hs hsn a (a + u) (by omega)
    simp only [Nat.add_sub_cancel_left, Nat.cast_id] at hp
    have hPpos : 0 < ∏ r ∈ Finset.Ico a (a + u),
        (1 - s * gain N r) := lt_of_lt_of_le (Real.exp_pos _) hp.1
    constructor
    · calc
        Real.exp (-2 * s * Cgain) *
              Real.exp (-(lambdaHi * (u : ℝ))) =
            (Real.exp (-s * (u : ℝ) * h -
              (s * Cgain + 2 * s ^ 2 * nr ^ 2 * (u : ℝ)))) ^ 2 := by
                dsimp [lambdaHi]
                rw [← Real.exp_add, ← Real.exp_nat_mul]
                congr 1
                ring
        _ ≤ (∏ r ∈ Finset.Ico a (a + u),
              (1 - s * gain N r)) ^ 2 :=
          (sq_le_sq₀ (Real.exp_pos _).le hPpos.le).2 hp.1
    · calc
        (∏ r ∈ Finset.Ico a (a + u),
              (1 - s * gain N r)) ^ 2 ≤
            (Real.exp (-s * (u : ℝ) * h +
              (s * Cgain + 2 * s ^ 2 * nr ^ 2 * (u : ℝ)))) ^ 2 :=
          (sq_le_sq₀ hPpos.le (Real.exp_pos _).le).2 hp.2
        _ = Real.exp (2 * s * Cgain) *
              Real.exp (-(lambdaLo * (u : ℝ))) := by
                dsimp [lambdaLo]
                rw [← Real.exp_add, ← Real.exp_nat_mul]
                congr 1
                ring
  have hmassLower :
      Real.exp (-2 * s * Cgain) *
          (1 / lambdaHi -
            Real.exp (-(lambdaHi * (U : ℝ))) *
              (1 + lambdaHi) / lambdaHi) ≤ mass := by
    calc
      _ ≤ Real.exp (-2 * s * Cgain) *
          (∑ u ∈ Finset.range U,
            Real.exp (-(lambdaHi * (u : ℝ)))) :=
        mul_le_mul_of_nonneg_left hsumsHi.1 (Real.exp_pos _).le
      _ = ∑ u ∈ Finset.range U,
          Real.exp (-2 * s * Cgain) *
            Real.exp (-(lambdaHi * (u : ℝ))) := by rw [Finset.mul_sum]
      _ ≤ mass := Finset.sum_le_sum fun u hu => (hpoint u).1
  have hmassUpper : mass ≤
      Real.exp (2 * s * Cgain) * (1 / lambdaLo + 1) := by
    calc
      mass ≤ ∑ u ∈ Finset.range U,
          Real.exp (2 * s * Cgain) *
            Real.exp (-(lambdaLo * (u : ℝ))) :=
        Finset.sum_le_sum fun u hu => (hpoint u).2
      _ = Real.exp (2 * s * Cgain) *
          (∑ u ∈ Finset.range U,
            Real.exp (-(lambdaLo * (u : ℝ)))) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (2 * s * Cgain) * (1 / lambdaLo + 1) :=
        mul_le_mul_of_nonneg_left hsumsLo.2 (Real.exp_pos _).le
  have hloRecip : 1 / lambdaLo - 1 / (2 * s * h) ≤
      2 * nr ^ 2 / h ^ 2 := by
    have hden0 : 0 < 2 * s * h := by positivity
    have hid : 1 / lambdaLo - 1 / (2 * s * h) =
        (4 * s ^ 2 * nr ^ 2) / (lambdaLo * (2 * s * h)) := by
      calc
        1 / lambdaLo - 1 / (2 * s * h) =
            ((2 * s * h) - lambdaLo) / (lambdaLo * (2 * s * h)) := by
          field_simp [ne_of_gt hlambdaLo, ne_of_gt hden0]
        _ = (4 * s ^ 2 * nr ^ 2) / (lambdaLo * (2 * s * h)) := by
          congr 1
          dsimp [lambdaLo]
          ring
    rw [hid]
    calc
      (4 * s ^ 2 * nr ^ 2) / (lambdaLo * (2 * s * h)) ≤
          (4 * s ^ 2 * nr ^ 2) / ((s * h) * (2 * s * h)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hlambdaLo_lower hden0.le
      _ = 2 * nr ^ 2 / h ^ 2 := by
        field_simp [ne_of_gt hs, ne_of_gt hh']
        ring
  have hhiRecip : 1 / (2 * s * h) - 1 / lambdaHi ≤
      nr ^ 2 / h ^ 2 := by
    have hden0 : 0 < 2 * s * h := by positivity
    have hid : 1 / (2 * s * h) - 1 / lambdaHi =
        (4 * s ^ 2 * nr ^ 2) / ((2 * s * h) * lambdaHi) := by
      calc
        1 / (2 * s * h) - 1 / lambdaHi =
            (lambdaHi - (2 * s * h)) / ((2 * s * h) * lambdaHi) := by
          field_simp [ne_of_gt hlambdaHi, ne_of_gt hden0]
        _ = (4 * s ^ 2 * nr ^ 2) / ((2 * s * h) * lambdaHi) := by
          congr 1
          dsimp [lambdaHi]
          ring
    rw [hid]
    calc
      (4 * s ^ 2 * nr ^ 2) / ((2 * s * h) * lambdaHi) ≤
          (4 * s ^ 2 * nr ^ 2) / ((2 * s * h) * (2 * s * h)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hlambdaHi_lower hden0.le
      _ = nr ^ 2 / h ^ 2 := by
        field_simp [ne_of_gt hs, ne_of_gt hh']
        ring
  have hupperError : mass - 1 / (2 * s * h) ≤
      4 * Cgain / h + 2 * nr ^ 2 / h ^ 2 + 3 := by
    have hratio : (Real.exp (2 * s * Cgain) - 1) / lambdaLo ≤
        4 * Cgain / h := by
      have hnum : Real.exp (2 * s * Cgain) - 1 ≤ 4 * s * Cgain := by
        linarith
      have hnum0 : 0 ≤ Real.exp (2 * s * Cgain) - 1 := by
        rw [sub_nonneg, Real.one_le_exp_iff]
        positivity
      calc
        _ ≤ (4 * s * Cgain) / lambdaLo :=
          div_le_div_of_nonneg_right hnum hlambdaLo.le
        _ ≤ (4 * s * Cgain) / (s * h) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hs hh)
            hlambdaLo_lower
        _ = 4 * Cgain / h := by field_simp [ne_of_gt hs, ne_of_gt hh]
    calc
      mass - 1 / (2 * s * h) ≤
          Real.exp (2 * s * Cgain) * (1 / lambdaLo + 1) -
            1 / (2 * s * h) := sub_le_sub_right hmassUpper _
      _ = (Real.exp (2 * s * Cgain) - 1) / lambdaLo +
            (1 / lambdaLo - 1 / (2 * s * h)) +
            Real.exp (2 * s * Cgain) := by ring
      _ ≤ 4 * Cgain / h + 2 * nr ^ 2 / h ^ 2 + 3 := by
        linarith
  have htail :
      Real.exp (-2 * s * Cgain) *
          (Real.exp (-(lambdaHi * (U : ℝ))) *
            (1 + lambdaHi) / lambdaHi) ≤
        (1 / h) * Real.exp (-(s * h * (U : ℝ))) / s := by
    have hU0 : 0 ≤ (U : ℝ) := Nat.cast_nonneg _
    have hexpRate : Real.exp (-(lambdaHi * (U : ℝ))) ≤
        Real.exp (-(s * h * (U : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have : s * h ≤ lambdaHi := (show s * h ≤ 2 * s * h by
        nlinarith [mul_pos hs hh]).trans hlambdaHi_lower
      nlinarith [mul_nonneg (sub_nonneg.mpr this) hU0]
    have hcoef : (1 + lambdaHi) / lambdaHi ≤ 1 / (s * h) := by
      have hsum : 1 + lambdaHi ≤ 2 := by linarith
      calc
        (1 + lambdaHi) / lambdaHi ≤ 2 / lambdaHi :=
          div_le_div_of_nonneg_right hsum hlambdaHi.le
        _ ≤ 2 / (2 * s * h) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            hlambdaHi_lower
        _ = 1 / (s * h) := by field_simp [ne_of_gt hs, ne_of_gt hh]
    have hnonnegExp : 0 ≤ Real.exp (-(lambdaHi * (U : ℝ))) :=
      (Real.exp_pos _).le
    have hcoef0 : 0 ≤ (1 + lambdaHi) / lambdaHi :=
      div_nonneg (by linarith) hlambdaHi.le
    have htailBase0 : 0 ≤ Real.exp (-(lambdaHi * (U : ℝ))) *
        (1 + lambdaHi) / lambdaHi := by positivity
    calc
      _ ≤ Real.exp (-(lambdaHi * (U : ℝ))) *
          ((1 + lambdaHi) / lambdaHi) := by
        calc
          Real.exp (-2 * s * Cgain) *
                (Real.exp (-(lambdaHi * (U : ℝ))) *
                  (1 + lambdaHi) / lambdaHi) ≤
              1 * (Real.exp (-(lambdaHi * (U : ℝ))) *
                (1 + lambdaHi) / lambdaHi) :=
            mul_le_mul_of_nonneg_right hexpNegUpper htailBase0
          _ = _ := by ring
      _ ≤ Real.exp (-(s * h * (U : ℝ))) * (1 / (s * h)) := by
        calc
          Real.exp (-(lambdaHi * (U : ℝ))) *
                ((1 + lambdaHi) / lambdaHi) ≤
              Real.exp (-(s * h * (U : ℝ))) *
                ((1 + lambdaHi) / lambdaHi) :=
            mul_le_mul_of_nonneg_right hexpRate hcoef0
          _ ≤ Real.exp (-(s * h * (U : ℝ))) * (1 / (s * h)) :=
            mul_le_mul_of_nonneg_left hcoef (Real.exp_pos _).le
      _ = (1 / h) * Real.exp (-(s * h * (U : ℝ))) / s := by
        field_simp [ne_of_gt hs, ne_of_gt hh'] <;> ring
  have hlowerError : 1 / (2 * s * h) - mass ≤
      (Cgain / h + nr ^ 2 / h ^ 2) +
        (1 / h) * Real.exp (-(s * h * (U : ℝ))) / s := by
    have hfactor :
        (1 - Real.exp (-2 * s * Cgain)) / lambdaHi ≤ Cgain / h := by
      calc
        _ ≤ (2 * s * Cgain) / lambdaHi :=
          div_le_div_of_nonneg_right honeSubExp hlambdaHi.le
        _ ≤ (2 * s * Cgain) / (2 * s * h) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            hlambdaHi_lower
        _ = Cgain / h := by field_simp [ne_of_gt hs, ne_of_gt hh]
    calc
      1 / (2 * s * h) - mass ≤
          1 / (2 * s * h) -
            Real.exp (-2 * s * Cgain) *
              (1 / lambdaHi -
                Real.exp (-(lambdaHi * (U : ℝ))) *
                  (1 + lambdaHi) / lambdaHi) :=
        sub_le_sub_left hmassLower _
      _ = (1 / (2 * s * h) - 1 / lambdaHi) +
            (1 - Real.exp (-2 * s * Cgain)) / lambdaHi +
            Real.exp (-2 * s * Cgain) *
              (Real.exp (-(lambdaHi * (U : ℝ))) *
                (1 + lambdaHi) / lambdaHi) := by ring
      _ ≤ (Cgain / h + nr ^ 2 / h ^ 2) +
            (1 / h) * Real.exp (-(s * h * (U : ℝ))) / s := by
        linarith
  change |mass - 1 / (2 * s * h)| ≤
    K + K * Real.exp (-(s * h * (U : ℝ))) / s
  apply (abs_le).2
  constructor
  · have htail0 : 0 ≤ Real.exp (-(s * h * (U : ℝ))) / s := by positivity
    have hCg : 0 ≤ Cgain / h := div_nonneg hCgain hh.le
    have hn2 : 0 ≤ nr ^ 2 / h ^ 2 := by positivity
    have hhInv : 0 ≤ 1 / h := by positivity
    have hbaseK : Cgain / h + nr ^ 2 / h ^ 2 ≤ K := by
      have hrest : 0 ≤ 3 * (Cgain / h) + nr ^ 2 / h ^ 2 + 3 + 1 / h := by
        positivity
      have heq : K - (Cgain / h + nr ^ 2 / h ^ 2) =
          3 * (Cgain / h) + nr ^ 2 / h ^ 2 + 3 + 1 / h := by
        dsimp [K]
        ring
      rw [← sub_nonneg, heq]
      exact hrest
    have htailK : 1 / h ≤ K := by
      dsimp [K]
      have hrest : 0 ≤ 4 * Cgain / h + 2 * nr ^ 2 / h ^ 2 + 3 := by
        positivity
      linarith
    have htotal := add_le_add hbaseK
      (mul_le_mul_of_nonneg_right htailK htail0)
    have hneg := neg_le_neg htotal
    calc
      -(K + K * Real.exp (-(s * h * (U : ℝ))) / s) ≤
          -((Cgain / h + nr ^ 2 / h ^ 2) +
            (1 / h) * Real.exp (-(s * h * (U : ℝ))) / s) := by
        convert hneg using 1 <;> ring
      _ ≤ mass - 1 / (2 * s * h) := by linarith [hlowerError]
  · have htail0 : 0 ≤ Real.exp (-(s * h * (U : ℝ))) / s := by positivity
    have hhInv : 0 ≤ 1 / h := by positivity
    have hbaseK : 4 * Cgain / h + 2 * nr ^ 2 / h ^ 2 + 3 ≤ K := by
      dsimp [K]
      linarith
    have htailTerm : 0 ≤ K * Real.exp (-(s * h * (U : ℝ))) / s := by
      positivity
    calc
      mass - 1 / (2 * s * h) ≤
          4 * Cgain / h + 2 * nr ^ 2 / h ^ 2 + 3 := hupperError
      _ ≤ K := hbaseK
      _ ≤ K + K * Real.exp (-(s * h * (U : ℝ))) / s := by linarith

/-- Source step 19: on a fixed positive square-root stepsize band the
terminal loss in the shifted product estimate is uniformly bounded. -/
private theorem periodic_signal_product_energy_band_expansion
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ T₀ : ℕ, ∀ T : PositiveHorizon, T₀ ≤ T.1 →
      ∀ s : ℝ, 0 < s →
        c ≤ s * Real.sqrt (T.1 : ℝ) →
        s * Real.sqrt (T.1 : ℝ) ≤ C →
        |(∑ t ∈ Finset.range T.1,
            (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2) -
            1 / (2 * s * periodicGainMean N p hp)| ≤ K := by
  obtain ⟨Ktail, sCap, hKtail, hsCap, htail⟩ :=
    periodic_shifted_product_energy_tail_bound N p hp
  have hh := (periodic_phase_coefficients N p hp).1
  let h := periodicGainMean N p hp
  have hh' : 0 < h := by simpa [h] using hh
  let K : ℝ := Ktail + Ktail / (c ^ 2 * h)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt ((C / sCap) ^ 2)
  refine ⟨K, hK, T₀, ?_⟩
  intro T hT s hs hslow hshigh
  have hTR : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
  have hsqrt : 0 < Real.sqrt (T.1 : ℝ) := Real.sqrt_pos.2 hTR
  have hsqrtSq : Real.sqrt (T.1 : ℝ) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hTR.le
  have hTlarge : (C / sCap) ^ 2 < (T.1 : ℝ) :=
    hT₀.trans_le (by exact_mod_cast hT)
  have hratio0 : 0 < C / sCap := div_pos hC hsCap
  have hratio : C / sCap < Real.sqrt (T.1 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (T.1 : ℝ) - C / sCap)]
  have hCroot : C / Real.sqrt (T.1 : ℝ) ≤ sCap := by
    have hmul : C < sCap * Real.sqrt (T.1 : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hsCap).mp hratio
    exact (div_le_iff₀ hsqrt).2 hmul.le
  have hsCap' : s ≤ sCap := by
    have hsC : s ≤ C / Real.sqrt (T.1 : ℝ) :=
      (le_div_iff₀ hsqrt).2 hshigh
    exact hsC.trans hCroot
  have hraw := htail s hs hsCap' 0 T.1
  simp only [Nat.zero_add] at hraw
  let x : ℝ := s * h * (T.1 : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hexpInv : Real.exp (-x) ≤ 1 / x := by
    rw [Real.exp_neg]
    have hxExp : x ≤ Real.exp x :=
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)).trans
        (by simpa [add_comm] using Real.add_one_le_exp x)
    simpa [one_div] using one_div_le_one_div_of_le hx hxExp
  have htailFirst : Real.exp (-x) / s ≤ 1 / (s * x) := by
    calc
      Real.exp (-x) / s ≤ (1 / x) / s :=
        div_le_div_of_nonneg_right hexpInv hs.le
      _ = 1 / (s * x) := by field_simp [ne_of_gt hs, ne_of_gt hx]
  have hbandSq : c ^ 2 ≤ s ^ 2 * (T.1 : ℝ) := by
    have hsprod0 : 0 ≤ s * Real.sqrt (T.1 : ℝ) := by positivity
    have hsq := (sq_le_sq₀ hc.le hsprod0).2 hslow
    rw [mul_pow, hsqrtSq] at hsq
    exact hsq
  have hdenBand : c ^ 2 * h ≤ s * x := by
    dsimp [x]
    nlinarith [mul_le_mul_of_nonneg_right hbandSq hh'.le]
  have htailBand : Real.exp (-x) / s ≤ 1 / (c ^ 2 * h) := by
    calc
      Real.exp (-x) / s ≤ 1 / (s * x) := htailFirst
      _ ≤ 1 / (c ^ 2 * h) :=
        one_div_le_one_div_of_le (by positivity) hdenBand
  have hraw' :
      |(∑ t ∈ Finset.range T.1,
          (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2) -
          1 / (2 * s * h)| ≤
        Ktail + Ktail * Real.exp (-x) / s := by
    simpa [h, x, mul_assoc] using hraw
  calc
    _ ≤ Ktail + Ktail * Real.exp (-x) / s := hraw'
    _ ≤ Ktail + Ktail * (1 / (c ^ 2 * h)) := by
      have hm := mul_le_mul_of_nonneg_left htailBand hKtail
      have hm' : Ktail * Real.exp (-x) / s ≤
          Ktail * (1 / (c ^ 2 * h)) := by
        calc
          Ktail * Real.exp (-x) / s = Ktail * (Real.exp (-x) / s) := by ring
          _ ≤ _ := hm
      simpa [add_comm] using add_le_add_left hm' Ktail
    _ = K := by dsimp [K]; ring

/-- Reverse the strict lower-triangular horizon sum into suffix coordinates.
This is the bookkeeping identity used before applying the shifted product
estimate to every noise impulse. -/
private theorem sum_range_sum_range_triangular_swap
    (T : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, f j t) =
      ∑ j ∈ Finset.range T, ∑ u ∈ Finset.range (T - j - 1),
        f j (j + 1 + u) := by
  calc
    (∑ t ∈ Finset.range T, ∑ j ∈ Finset.range t, f j t) =
        ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range T,
          if j < t then f j t else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have htT : t < T := Finset.mem_range.mp ht
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp [hj.2]
    _ = ∑ j ∈ Finset.range T, ∑ t ∈ Finset.range T,
          if j < t then f j t else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range T, ∑ t ∈ Finset.Ico (j + 1) T, f j t := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro t ht
        simp
    _ = ∑ j ∈ Finset.range T, ∑ u ∈ Finset.range (T - j - 1),
          f j (j + 1 + u) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr
      · congr 1
      · intro u hu
        congr 2

/-- The reversed terminal exponential mass has the same horizon-uniform
bound as the forward geometric mass.  This is the exact Nat-subtraction
index produced by the lower-triangular variance reindexing. -/
private theorem sum_range_reverse_exp_tail_le
    (lambda : ℝ) (T : ℕ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1) :
    (∑ j ∈ Finset.range T,
        Real.exp (-(lambda * ((T - j - 1 : ℕ) : ℝ)))) ≤
      1 / lambda + 1 := by
  have hreflect :
      (∑ j ∈ Finset.range T,
          Real.exp (-(lambda * ((T - j - 1 : ℕ) : ℝ)))) =
        ∑ j ∈ Finset.range T, Real.exp (-(lambda * (j : ℝ))) := by
    rw [← Finset.sum_range_reflect
      (fun j : ℕ => Real.exp (-(lambda * (j : ℝ)))) T]
    apply Finset.sum_congr rfl
    intro j hj
    have hjT : j < T := Finset.mem_range.mp hj
    have hindex : T - j - 1 = T - 1 - j := by omega
    rw [hindex]
  rw [hreflect]
  exact (finite_exp_geometric_sum_reciprocal_bounds
    lambda T hlambda hlambda_one).2

/-- Source step 20: after triangular reindexing, the periodic proxy variance
energy has leading term `s*q*T/(2*h)`.  The interval-energy deviation controls
the reciprocal mass, while the reversed exponential estimate controls all
terminal losses uniformly on a positive square-root stepsize band. -/
private theorem periodic_variance_product_energy_band_expansion
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (Cenergy : ℝ) (hCenergy : 0 ≤ Cenergy)
    (hintervalEnergy : ∀ a b : ℕ, a ≤ b →
      |(∑ t ∈ Finset.Ico a b, influenceEnergy N t) -
          ((b - a : ℕ) : ℝ) * periodicInfluenceMean N p| ≤ Cenergy)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ T₀ : ℕ, ∀ T : PositiveHorizon, T₀ ≤ T.1 →
      ∀ s : ℝ, 0 < s →
        c ≤ s * Real.sqrt (T.1 : ℝ) →
        s * Real.sqrt (T.1 : ℝ) ≤ C →
        |s ^ 2 * (∑ t ∈ Finset.range T.1,
            ∑ j ∈ Finset.range t, influenceEnergy N j *
              (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r)) ^ 2) -
            s * periodicInfluenceMean N p * T.1 /
              (2 * periodicGainMean N p hp)| ≤
          K * (1 + s ^ 2 * T.1) := by
  classical
  obtain ⟨Ktail, sCap, hKtail, hsCap, htail⟩ :=
    periodic_shifted_product_energy_tail_bound N p hp
  obtain ⟨hh, hhq, _hsum, _hcoord⟩ := periodic_phase_coefficients N p hp
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  let h : ℝ := periodicGainMean N p hp
  let q : ℝ := periodicInfluenceMean N p
  have hh' : 0 < h := by simpa [h] using hh
  have hq : 0 < q := by
    dsimp [q]
    exact (div_pos (sq_pos_of_pos hh) hn).trans_le hhq
  let M : ℝ := q + Cenergy
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have henergy_nonneg (j : ℕ) : 0 ≤ influenceEnergy N j := by
    unfold influenceEnergy
    exact Finset.sum_nonneg fun i _hi => sq_nonneg (influenceRow N j i)
  have henergy_upper (j : ℕ) : influenceEnergy N j ≤ M := by
    have hdev := hintervalEnergy j (j + 1) (by omega)
    have hright := (abs_le.mp hdev).2
    have hsingle :
        (∑ t ∈ Finset.Ico j (j + 1), influenceEnergy N t) =
          influenceEnergy N j := by simp
    rw [hsingle] at hright
    simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul] at hright
    dsimp [M, q]
    linarith
  let sSmall : ℝ := min sCap (min 1 (1 / h))
  have hsSmall : 0 < sSmall := by
    dsimp [sSmall]
    positivity
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt ((C / sSmall) ^ 2)
  let Kconst : ℝ :=
    Ktail * Cenergy + Ktail * M * (1 / h + 1) + Cenergy / (2 * h)
  let K : ℝ := Ktail * q + Kconst
  have hKconst : 0 ≤ Kconst := by
    dsimp [Kconst]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, T₀, ?_⟩
  intro T hT s hs _hslow hshigh
  have hTR : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
  have hsqrt : 0 < Real.sqrt (T.1 : ℝ) := Real.sqrt_pos.2 hTR
  have hsqrtSq : Real.sqrt (T.1 : ℝ) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hTR.le
  have hTlarge : (C / sSmall) ^ 2 < (T.1 : ℝ) :=
    hT₀.trans_le (by exact_mod_cast hT)
  have hratio0 : 0 < C / sSmall := div_pos hC hsSmall
  have hratio : C / sSmall < Real.sqrt (T.1 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (T.1 : ℝ) - C / sSmall)]
  have hCroot : C / Real.sqrt (T.1 : ℝ) ≤ sSmall := by
    have hmul : C < sSmall * Real.sqrt (T.1 : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hsSmall).mp hratio
    exact (div_le_iff₀ hsqrt).2 hmul.le
  have hsSmall' : s ≤ sSmall := by
    have hsC : s ≤ C / Real.sqrt (T.1 : ℝ) :=
      (le_div_iff₀ hsqrt).2 hshigh
    exact hsC.trans hCroot
  have hsCap' : s ≤ sCap := hsSmall'.trans (by
    dsimp [sSmall]
    exact min_le_left _ _)
  have hs_one : s ≤ 1 := hsSmall'.trans (by
    dsimp [sSmall]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hs_h : s ≤ 1 / h := hsSmall'.trans (by
    dsimp [sSmall]
    exact (min_le_right _ _).trans (min_le_right _ _))
  have hlambda : 0 < s * h := mul_pos hs hh'
  have hlambda_one : s * h ≤ 1 := by
    calc
      s * h ≤ (1 / h) * h := mul_le_mul_of_nonneg_right hs_h hh'.le
      _ = 1 := by field_simp [ne_of_gt hh']
  let mass : ℕ → ℝ := fun j =>
    ∑ u ∈ Finset.range (T.1 - j - 1),
      (∏ r ∈ Finset.Ico (j + 1) (j + 1 + u),
        (1 - s * gain N r)) ^ 2
  have hswap :
      (∑ t ∈ Finset.range T.1,
          ∑ j ∈ Finset.range t, influenceEnergy N j *
            (∏ r ∈ Finset.Ico (j + 1) t,
              (1 - s * gain N r)) ^ 2) =
        ∑ j ∈ Finset.range T.1, influenceEnergy N j * mass j := by
    rw [sum_range_sum_range_triangular_swap]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [mass]
    rw [Finset.mul_sum]
  have hmass (j : ℕ) :
      |mass j - 1 / (2 * s * h)| ≤
        Ktail + Ktail * Real.exp
          (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ))) / s := by
    simpa [mass, h, mul_assoc] using
      htail s hs hsCap' (j + 1) (T.1 - j - 1)
  have hsumEnergyDev :
      |(∑ j ∈ Finset.range T.1, influenceEnergy N j) -
          (T.1 : ℝ) * q| ≤ Cenergy := by
    simpa [q] using hintervalEnergy 0 T.1 (Nat.zero_le _)
  have hsumEnergyUpper :
      (∑ j ∈ Finset.range T.1, influenceEnergy N j) ≤
        (T.1 : ℝ) * q + Cenergy := by
    linarith [(abs_le.mp hsumEnergyDev).2]
  have hreverse := sum_range_reverse_exp_tail_le
    (s * h) T.1 hlambda hlambda_one
  have hterminal :
      (∑ j ∈ Finset.range T.1, influenceEnergy N j *
          Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ)))) ≤
        M * (1 / (s * h) + 1) := by
    calc
      _ ≤ ∑ j ∈ Finset.range T.1, M *
          Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ))) := by
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (henergy_upper j) (Real.exp_pos _).le
      _ = M * (∑ j ∈ Finset.range T.1,
          Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ)))) := by
        rw [Finset.mul_sum]
      _ ≤ M * (1 / (s * h) + 1) :=
        mul_le_mul_of_nonneg_left hreverse hM
  have hdiff :
      s ^ 2 * (∑ j ∈ Finset.range T.1,
          influenceEnergy N j * mass j) -
          s ^ 2 * (1 / (2 * s * h)) *
            (∑ j ∈ Finset.range T.1, influenceEnergy N j) =
        ∑ j ∈ Finset.range T.1,
          (s ^ 2 * influenceEnergy N j) *
            (mass j - 1 / (2 * s * h)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hpointWeighted (j : ℕ) :
      |(s ^ 2 * influenceEnergy N j) *
          (mass j - 1 / (2 * s * h))| ≤
        Ktail * s ^ 2 * influenceEnergy N j +
          Ktail * s * influenceEnergy N j *
            Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ))) := by
    rw [abs_mul, abs_of_nonneg
      (mul_nonneg (sq_nonneg s) (henergy_nonneg j))]
    have hmul := mul_le_mul_of_nonneg_left (hmass j)
      (mul_nonneg (sq_nonneg s) (henergy_nonneg j))
    calc
      s ^ 2 * influenceEnergy N j *
          |mass j - 1 / (2 * s * h)| ≤
        s ^ 2 * influenceEnergy N j *
          (Ktail + Ktail *
            Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ))) / s) := hmul
      _ = Ktail * s ^ 2 * influenceEnergy N j +
          Ktail * s * influenceEnergy N j *
            Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ))) := by
        field_simp [ne_of_gt hs] <;> ring
  have hproxyError :
      |s ^ 2 * (∑ j ∈ Finset.range T.1,
          influenceEnergy N j * mass j) -
          s ^ 2 * (1 / (2 * s * h)) *
            (∑ j ∈ Finset.range T.1, influenceEnergy N j)| ≤
        Ktail * q * (s ^ 2 * T.1) +
          Ktail * Cenergy + Ktail * M * (1 / h + 1) := by
    rw [hdiff]
    calc
      |∑ j ∈ Finset.range T.1,
          (s ^ 2 * influenceEnergy N j) *
            (mass j - 1 / (2 * s * h))| ≤
        ∑ j ∈ Finset.range T.1,
          |(s ^ 2 * influenceEnergy N j) *
            (mass j - 1 / (2 * s * h))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range T.1,
          (Ktail * s ^ 2 * influenceEnergy N j +
            Ktail * s * influenceEnergy N j *
              Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ)))) :=
        Finset.sum_le_sum fun j hj => hpointWeighted j
      _ = Ktail * s ^ 2 *
            (∑ j ∈ Finset.range T.1, influenceEnergy N j) +
          Ktail * s *
            (∑ j ∈ Finset.range T.1, influenceEnergy N j *
              Real.exp (-(s * h * ((T.1 - j - 1 : ℕ) : ℝ)))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        ring
      _ ≤ Ktail * s ^ 2 * ((T.1 : ℝ) * q + Cenergy) +
          Ktail * s * (M * (1 / (s * h) + 1)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsumEnergyUpper
            (mul_nonneg hKtail (sq_nonneg s)))
          (mul_le_mul_of_nonneg_left hterminal
            (mul_nonneg hKtail hs.le))
      _ = Ktail * q * (s ^ 2 * T.1) + Ktail * Cenergy * s ^ 2 +
          Ktail * M * (1 / h + s) := by
        field_simp [ne_of_gt hs, ne_of_gt hh'] <;> ring
      _ ≤ Ktail * q * (s ^ 2 * T.1) +
          Ktail * Cenergy + Ktail * M * (1 / h + 1) := by
        have hsSq : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
        have hCE : 0 ≤ Ktail * Cenergy := mul_nonneg hKtail hCenergy
        have hKM : 0 ≤ Ktail * M := mul_nonneg hKtail hM
        nlinarith [mul_le_mul_of_nonneg_left hsSq hCE,
          mul_le_mul_of_nonneg_left hs_one hKM]
  have hmeanError :
      |s ^ 2 * (1 / (2 * s * h)) *
          (∑ j ∈ Finset.range T.1, influenceEnergy N j) -
          s * q * T.1 / (2 * h)| ≤ Cenergy / (2 * h) := by
    have hcoef : 0 ≤ s / (2 * h) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hsumEnergyDev hcoef
    calc
      _ = (s / (2 * h)) *
          |(∑ j ∈ Finset.range T.1, influenceEnergy N j) -
            (T.1 : ℝ) * q| := by
        rw [show s ^ 2 * (1 / (2 * s * h)) *
            (∑ j ∈ Finset.range T.1, influenceEnergy N j) -
              s * q * T.1 / (2 * h) =
            (s / (2 * h)) *
              ((∑ j ∈ Finset.range T.1, influenceEnergy N j) -
                (T.1 : ℝ) * q) by
          field_simp [ne_of_gt hs, ne_of_gt hh'] <;> ring]
        rw [abs_mul, abs_of_nonneg hcoef]
      _ ≤ (s / (2 * h)) * Cenergy := hscaled
      _ ≤ Cenergy / (2 * h) := by
        have hden : 0 < 2 * h := by positivity
        rw [show s / (2 * h) * Cenergy =
          (s * Cenergy) / (2 * h) by ring]
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith [mul_nonneg hCenergy (sub_nonneg.mpr hs_one)]
  rw [hswap]
  have htotal := (abs_add_le
    (s ^ 2 * (∑ j ∈ Finset.range T.1, influenceEnergy N j * mass j) -
      s ^ 2 * (1 / (2 * s * h)) *
        (∑ j ∈ Finset.range T.1, influenceEnergy N j))
    (s ^ 2 * (1 / (2 * s * h)) *
      (∑ j ∈ Finset.range T.1, influenceEnergy N j) -
        s * q * T.1 / (2 * h))).trans
      (add_le_add hproxyError hmeanError)
  have hrewrite :
      (s ^ 2 * (∑ j ∈ Finset.range T.1,
          influenceEnergy N j * mass j) -
        s ^ 2 * (1 / (2 * s * h)) *
          (∑ j ∈ Finset.range T.1, influenceEnergy N j)) +
      (s ^ 2 * (1 / (2 * s * h)) *
        (∑ j ∈ Finset.range T.1, influenceEnergy N j) -
          s * q * T.1 / (2 * h)) =
      s ^ 2 * (∑ j ∈ Finset.range T.1,
          influenceEnergy N j * mass j) - s * q * T.1 / (2 * h) := by
    ring
  rw [hrewrite] at htotal
  change |s ^ 2 * (∑ j ∈ Finset.range T.1,
      influenceEnergy N j * mass j) - s * q * T.1 / (2 * h)| ≤
    K * (1 + s ^ 2 * T.1)
  calc
    _ ≤ Ktail * q * (s ^ 2 * T.1) + Kconst := by
      simpa [Kconst, add_assoc] using htotal
    _ ≤ K * (1 + s ^ 2 * T.1) := by
      have hx : 0 ≤ s ^ 2 * (T.1 : ℝ) := by positivity
      dsimp [K]
      nlinarith [mul_nonneg hKconst hx,
        mul_nonneg (mul_nonneg hKtail hq.le) (by positivity : 0 ≤ (1 : ℝ))]

/-- Scalar substitution through equations (49)--(50).  Once the actual signal
and variance energies are compared with their periodic proxies, the two proxy
expansions give the exact leading quadratic cost with an inverse-horizon
remainder on a square-root stepsize band. -/
private theorem actual_quadratic_band_expansion_of_proxy_comparisons
    (A sigma h q C KD KV CD CV t s Dproxy Vproxy Dact Vact Q : ℝ)
    (hA : 0 ≤ A) (hh : 0 < h) (hC : 0 ≤ C)
    (hKD : 0 ≤ KD) (hKV : 0 ≤ KV) (hCD : 0 ≤ CD) (hCV : 0 ≤ CV)
    (ht : 0 < t) (hs : 0 < s)
    (hband : s * Real.sqrt t ≤ C)
    (h49 : t * Q = 2 * A * Dact + sigma ^ 2 * Vact)
    (hDproxy : |Dproxy - 1 / (2 * s * h)| ≤ KD)
    (hVproxy : |Vproxy - s * q * t / (2 * h)| ≤ KV * (1 + s ^ 2 * t))
    (hD50 : |Dact - Dproxy| ≤ CD)
    (hV50 : |Vact - Vproxy| ≤ CV * s ^ 2 * t) :
    |Q - (A / (s * h * t) + sigma ^ 2 * q * s / (2 * h))| ≤
      (2 * A * (CD + KD) + sigma ^ 2 * (CV + KV) * (1 + C ^ 2)) / t := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsqrtSq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have hsprod : 0 ≤ s * Real.sqrt t := by positivity
  have hsSqT : s ^ 2 * t ≤ C ^ 2 := by
    have hsq := (sq_le_sq₀ hsprod hC).2 hband
    rw [mul_pow, hsqrtSq] at hsq
    exact hsq
  have hDact : |Dact - 1 / (2 * s * h)| ≤ CD + KD := by
    calc
      |Dact - 1 / (2 * s * h)| =
          |(Dact - Dproxy) + (Dproxy - 1 / (2 * s * h))| := by ring_nf
      _ ≤ |Dact - Dproxy| + |Dproxy - 1 / (2 * s * h)| := abs_add_le _ _
      _ ≤ CD + KD := add_le_add hD50 hDproxy
  have hVact : |Vact - s * q * t / (2 * h)| ≤
      (CV + KV) * (1 + C ^ 2) := by
    calc
      |Vact - s * q * t / (2 * h)| =
          |(Vact - Vproxy) + (Vproxy - s * q * t / (2 * h))| := by ring_nf
      _ ≤ |Vact - Vproxy| + |Vproxy - s * q * t / (2 * h)| := abs_add_le _ _
      _ ≤ CV * s ^ 2 * t + KV * (1 + s ^ 2 * t) :=
        add_le_add hV50 hVproxy
      _ ≤ (CV + KV) * (1 + C ^ 2) := by
        have hx : 0 ≤ s ^ 2 * t := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hsSqT hCV,
          mul_le_mul_of_nonneg_left hsSqT hKV,
          mul_nonneg hCV (by positivity : 0 ≤ (1 : ℝ)),
          mul_nonneg hKV (by positivity : 0 ≤ (1 : ℝ))]
  have hcostIdentity :
      t * (Q - (A / (s * h * t) + sigma ^ 2 * q * s / (2 * h))) =
        2 * A * (Dact - 1 / (2 * s * h)) +
          sigma ^ 2 * (Vact - s * q * t / (2 * h)) := by
    rw [mul_sub, h49]
    field_simp [ne_of_gt ht, ne_of_gt hs, ne_of_gt hh]
    ring
  have hscaled :
      |t * (Q - (A / (s * h * t) + sigma ^ 2 * q * s / (2 * h)))| ≤
        2 * A * (CD + KD) + sigma ^ 2 * (CV + KV) * (1 + C ^ 2) := by
    rw [hcostIdentity]
    calc
      |2 * A * (Dact - 1 / (2 * s * h)) +
          sigma ^ 2 * (Vact - s * q * t / (2 * h))| ≤
        |2 * A * (Dact - 1 / (2 * s * h))| +
          |sigma ^ 2 * (Vact - s * q * t / (2 * h))| := abs_add_le _ _
      _ = 2 * A * |Dact - 1 / (2 * s * h)| +
          sigma ^ 2 * |Vact - s * q * t / (2 * h)| := by
        simp only [abs_mul]
        rw [abs_of_nonneg hA, abs_of_nonneg (sq_nonneg sigma)]
        norm_num
      _ ≤ 2 * A * (CD + KD) + sigma ^ 2 * (CV + KV) * (1 + C ^ 2) :=
        by
          simpa [mul_assoc] using add_le_add
            (mul_le_mul_of_nonneg_left hDact (mul_nonneg (by norm_num) hA))
            (mul_le_mul_of_nonneg_left hVact (sq_nonneg sigma))
  have habsScale :
      |t * (Q - (A / (s * h * t) + sigma ^ 2 * q * s / (2 * h)))| =
        t * |Q - (A / (s * h * t) + sigma ^ 2 * q * s / (2 * h))| := by
    rw [abs_mul, abs_of_pos ht]
  rw [habsScale] at hscaled
  apply (le_div_iff₀ ht).2
  simpa [mul_comm] using hscaled

/-- The scalar core of the periodic suffix-window upper estimate: any interval
admissible for the gain budget has length controlled by the phase mean, with
only the uniform periodic/transient deviation as an additive loss. -/
private theorem periodic_gain_budget_interval_length_le
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain : ℝ, 0 ≤ Cgain ∧ ∀ a b : ℕ, a ≤ b → ∀ s : ℝ, 0 < s →
      s * ∑ t ∈ Finset.Ico a b, gain N t ≤ epsilon →
        ((b - a : ℕ) : ℝ) ≤
          (epsilon / s + Cgain) / periodicGainMean N p hp := by
  obtain ⟨Cgain, Cenergy, hCgain, hCenergy, hinterval⟩ :=
    periodic_interval_deviation_bounds N p hp
  have hh := (periodic_phase_coefficients N p hp).1
  refine ⟨Cgain, hCgain, ?_⟩
  intro a b hab s hs hbudget
  have hdev := (hinterval a b hab).1
  have hlower :
      ((b - a : ℕ) : ℝ) * periodicGainMean N p hp - Cgain ≤
        ∑ t ∈ Finset.Ico a b, gain N t := by
    have hleft := (abs_le.mp hdev).1
    linarith
  have hsumUpper :
      (∑ t ∈ Finset.Ico a b, gain N t) ≤ epsilon / s := by
    apply (le_div_iff₀ hs).2
    simpa [mul_comm] using hbudget
  apply (le_div_iff₀ hh).2
  linarith

/-- The actual suffix-window definition inherits the periodic gain bound,
with the natural ceiling recording the endpoint rounding loss. -/
private theorem periodic_windowLength_le_ceil
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain : ℝ, 0 ≤ Cgain ∧ ∀ T t : ℕ, ∀ s : ℝ, 0 < s →
      windowLength N T t s ≤
        Nat.ceil ((epsilon / s + Cgain) / periodicGainMean N p hp) := by
  obtain ⟨Cgain, hCgain, hbudgetLength⟩ :=
    periodic_gain_budget_interval_length_le N p hp
  refine ⟨Cgain, hCgain, ?_⟩
  intro T t s hs
  have hh := (periodic_phase_coefficients N p hp).1
  have hquotNonneg :
      0 ≤ (epsilon / s + Cgain) / periodicGainMean N p hp := by
    apply div_nonneg
    · exact add_nonneg (div_nonneg (by norm_num [epsilon]) hs.le) hCgain
    · exact hh.le
  unfold windowLength
  split_ifs with ht
  · apply Finset.sup_le
    intro P hP
    apply Finset.sup_le
    intro Q hQ
    split_ifs with hbudget
    · have hlen := hbudgetLength P Q (by
        simp only [Finset.mem_Icc] at hQ
        omega) s hs hbudget
      have hreal : ((Q - P : ℕ) : ℝ) ≤
          (Nat.ceil ((epsilon / s + Cgain) /
            periodicGainMean N p hp) : ℕ) :=
        hlen.trans (Nat.le_ceil _)
      exact_mod_cast hreal
    · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- The converse scalar window estimate: an interval shorter than the
phase-mean budget after paying the deviation constant is admissible. -/
private theorem periodic_gain_interval_budget_of_length
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain : ℝ, 0 ≤ Cgain ∧ ∀ a b : ℕ, a ≤ b → ∀ s : ℝ, 0 < s →
      ((b - a : ℕ) : ℝ) * periodicGainMean N p hp + Cgain ≤ epsilon / s →
        s * ∑ t ∈ Finset.Ico a b, gain N t ≤ epsilon := by
  obtain ⟨Cgain, Cenergy, hCgain, hCenergy, hinterval⟩ :=
    periodic_interval_deviation_bounds N p hp
  refine ⟨Cgain, hCgain, ?_⟩
  intro a b hab s hs hlength
  have hdev := (hinterval a b hab).1
  have hsumUpper :
      (∑ t ∈ Finset.Ico a b, gain N t) ≤
        ((b - a : ℕ) : ℝ) * periodicGainMean N p hp + Cgain := by
    have hright := (abs_le.mp hdev).2
    linarith
  rw [mul_comm]
  exact (le_div_iff₀ hs).mp (hsumUpper.trans hlength)

/-- A concrete interval satisfying the periodic scalar budget is realized by
the nested supremum in `windowLength`. -/
private theorem periodic_length_le_windowLength_of_budget
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ Cgain : ℝ, 0 ≤ Cgain ∧
      ∀ T t ell : ℕ, t < T → 0 < ell → t + ell ≤ T →
        ∀ s : ℝ, 0 < s →
          (ell : ℝ) * periodicGainMean N p hp + Cgain ≤ epsilon / s →
            ell ≤ windowLength N T t s := by
  obtain ⟨Cgain, hCgain, hbudget⟩ :=
    periodic_gain_interval_budget_of_length N p hp
  refine ⟨Cgain, hCgain, ?_⟩
  intro T t ell htT hell htell s hs hlength
  have hadmissible :
      s * ∑ r ∈ Finset.Ico t (t + ell), gain N r ≤ epsilon := by
    apply hbudget t (t + ell) (by omega) s hs
    simpa using hlength
  unfold windowLength
  rw [if_pos htT]
  have hP : t ∈ Finset.Icc t T := by
    simp only [Finset.mem_Icc]
    omega
  have hQ : t + ell ∈ Finset.Icc (t + 1) T := by
    simp only [Finset.mem_Icc]
    omega
  calc
    ell = (t + ell) - t := by omega
    _ = if s * ∑ r ∈ Finset.Ico t (t + ell), gain N r ≤ epsilon
        then (t + ell) - t else 0 := by rw [if_pos hadmissible]
    _ ≤ (Finset.Icc (t + 1) T).sup fun Q =>
        if s * ∑ r ∈ Finset.Ico t Q, gain N r ≤ epsilon
        then Q - t else 0 :=
      Finset.le_sup (s := Finset.Icc (t + 1) T) (f := fun Q =>
        if s * ∑ r ∈ Finset.Ico t Q, gain N r ≤ epsilon
        then Q - t else 0) hQ
    _ ≤ (Finset.Icc t T).sup fun P =>
        (Finset.Icc (P + 1) T).sup fun Q =>
          if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
          then Q - P else 0 :=
      Finset.le_sup (s := Finset.Icc t T) (f := fun P =>
        (Finset.Icc (P + 1) T).sup fun Q =>
          if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
          then Q - P else 0) hP

/-- The weighted suffix-window expansion displayed immediately before (62).
The last `O(1/s)` indices are the only ones whose horizon truncation can
contribute more than the uniform rounding/deviation error. -/
private theorem periodic_windowInfluenceSum_expansion
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℕ, ∀ s : ℝ, 0 < s →
      |windowInfluenceSum N T s -
          (epsilon / (s * periodicGainMean N p hp)) *
            ∑ j ∈ Finset.range T, influenceEnergy N j| ≤
        K * ((T : ℝ) + (s⁻¹) ^ 2) := by
  classical
  obtain ⟨hh, hhq, _hsum, _hcoord⟩ := periodic_phase_coefficients N p hp
  obtain ⟨Cgain, Cenergy, hCgain, hCenergy, hinterval⟩ :=
    periodic_interval_deviation_bounds N p hp
  obtain ⟨Cceil, hCceil, hwindowUpper⟩ :=
    periodic_windowLength_le_ceil N p hp
  obtain ⟨Cfloor, hCfloor, hwindowLower⟩ :=
    periodic_length_le_windowLength_of_budget N p hp
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hq : 0 < periodicInfluenceMean N p := by
    have hbase : 0 < periodicGainMean N p hp ^ 2 / (n : ℝ) := by
      positivity
    exact hbase.trans_le hhq
  let M : ℝ := periodicInfluenceMean N p + Cenergy
  let U : ℝ := Cceil / periodicGainMean N p hp + 1
  let D : ℝ := Cfloor / periodicGainMean N p hp + 1
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let K : ℝ :=
    M * (D + U) +
      M * (2 + U) * (epsilon / periodicGainMean N p hp) ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hU : 1 ≤ U := by
    dsimp [U]
    exact le_add_of_nonneg_left (div_nonneg hCceil hh.le)
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_left (div_nonneg hCfloor hh.le)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro T s hs
  let x : ℝ := epsilon / (s * periodicGainMean N p hp)
  have hx : 0 < x := by
    dsimp [x]
    exact div_pos (by norm_num [epsilon]) (mul_pos hs hh)
  have henergy_nonneg (j : ℕ) : 0 ≤ influenceEnergy N j := by
    unfold influenceEnergy
    exact Finset.sum_nonneg fun i _hi => sq_nonneg (influenceRow N j i)
  have henergy_upper (j : ℕ) : influenceEnergy N j ≤ M := by
    have hdev := (hinterval j (j + 1) (by omega)).2
    have hright := (abs_le.mp hdev).2
    have hsingle : ∑ t ∈ Finset.Ico j (j + 1), influenceEnergy N t =
        influenceEnergy N j := by simp
    rw [hsingle] at hright
    simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul] at hright
    dsimp [M]
    linarith
  have hwindow_upper (t : ℕ) : (windowLength N T t s : ℝ) ≤ x + U := by
    have hnat := hwindowUpper T t s hs
    have hargNonneg :
        0 ≤ (epsilon / s + Cceil) / periodicGainMean N p hp := by
      apply div_nonneg
      · exact add_nonneg (div_nonneg (by norm_num [epsilon]) hs.le) hCceil
      · exact hh.le
    have hceil :
        (Nat.ceil ((epsilon / s + Cceil) /
          periodicGainMean N p hp) : ℝ) ≤
          (epsilon / s + Cceil) / periodicGainMean N p hp + 1 :=
      (Nat.ceil_lt_add_one hargNonneg).le
    have hcast : (windowLength N T t s : ℝ) ≤
        (Nat.ceil ((epsilon / s + Cceil) /
          periodicGainMean N p hp) : ℕ) := by
      exact_mod_cast hnat
    calc
      (windowLength N T t s : ℝ) ≤
          (Nat.ceil ((epsilon / s + Cceil) /
            periodicGainMean N p hp) : ℕ) := hcast
      _ ≤ (epsilon / s + Cceil) / periodicGainMean N p hp + 1 := hceil
      _ = x + U := by dsimp [x, U]; field_simp; ring
  have hrearrange :
      windowInfluenceSum N T s - x *
          (∑ j ∈ Finset.range T, influenceEnergy N j) =
        ∑ j ∈ Finset.range T,
          influenceEnergy N j * ((windowLength N T (j + 1) s : ℝ) - x) := by
    unfold windowInfluenceSum
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [show epsilon / (s * periodicGainMean N p hp) = x by rfl, hrearrange]
  calc
    |∑ j ∈ Finset.range T,
        influenceEnergy N j * ((windowLength N T (j + 1) s : ℝ) - x)| ≤
        ∑ j ∈ Finset.range T,
          |influenceEnergy N j *
            ((windowLength N T (j + 1) s : ℝ) - x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ K * ((T : ℝ) + (s⁻¹) ^ 2) := by
      by_cases hxD : x ≤ D
      · have hpoint (j : ℕ) :
            |influenceEnergy N j *
                ((windowLength N T (j + 1) s : ℝ) - x)| ≤
              M * (D + U) := by
          rw [abs_mul, abs_of_nonneg (henergy_nonneg j)]
          apply mul_le_mul (henergy_upper j) ?_ (abs_nonneg _) hM
          apply (abs_le).2
          constructor
          · have hw0 : 0 ≤ (windowLength N T (j + 1) s : ℝ) :=
              Nat.cast_nonneg _
            linarith
          · have hu := hwindow_upper (j + 1)
            linarith
        calc
          (∑ j ∈ Finset.range T,
              |influenceEnergy N j *
                ((windowLength N T (j + 1) s : ℝ) - x)|) ≤
              ∑ _j ∈ Finset.range T, M * (D + U) := by
            exact Finset.sum_le_sum fun j _hj => hpoint j
          _ = (T : ℝ) * (M * (D + U)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ K * ((T : ℝ) + (s⁻¹) ^ 2) := by
            have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
            have hinv : 0 ≤ (s⁻¹) ^ 2 := sq_nonneg _
            dsimp [K]
            nlinarith [mul_nonneg hM (by linarith : 0 ≤ D + U),
              mul_nonneg (mul_nonneg hM (by linarith : 0 ≤ 2 + U))
                (sq_nonneg (epsilon / periodicGainMean N p hp))]
      · have hxD' : D < x := lt_of_not_ge hxD
        let ell : ℕ := Nat.floor ((epsilon / s - Cfloor) /
          periodicGainMean N p hp)
        have hy : 0 ≤ (epsilon / s - Cfloor) /
            periodicGainMean N p hp := by
          apply div_nonneg
          · dsimp [D, x] at hxD'
            field_simp at hxD'
            have hnum : Cfloor ≤ epsilon / s := by
              apply (le_div_iff₀ hs).2
              nlinarith [mul_pos hs hh]
            linarith
          · exact hh.le
        have hell_pos : 0 < ell := by
          apply Nat.floor_pos.mpr
          dsimp [ell]
          dsimp [D, x] at hxD'
          have : 1 < (epsilon / s - Cfloor) /
              periodicGainMean N p hp := by
            field_simp at hxD' ⊢
            nlinarith
          exact this.le
        have hell_le_x : (ell : ℝ) ≤ x := by
          have hfloor := Nat.floor_le hy
          dsimp [x]
          calc
            (ell : ℝ) ≤
                (epsilon / s - Cfloor) / periodicGainMean N p hp := hfloor
            _ ≤ epsilon / (s * periodicGainMean N p hp) := by
              field_simp
              nlinarith
        have hx_lt_ellD : x < (ell : ℝ) + D := by
          have hfloor := Nat.lt_floor_add_one
            ((epsilon / s - Cfloor) / periodicGainMean N p hp)
          change (epsilon / s - Cfloor) / periodicGainMean N p hp <
            (ell : ℝ) + 1 at hfloor
          have hxy : x =
              (epsilon / s - Cfloor) / periodicGainMean N p hp +
                Cfloor / periodicGainMean N p hp := by
            dsimp [x]
            field_simp
            ring
          rw [hxy]
          dsimp [D]
          linarith
        have hwindow_lower {j : ℕ} (hj : j < T - ell) :
            ell ≤ windowLength N T (j + 1) s := by
          apply hwindowLower T (j + 1) ell (by omega) hell_pos (by omega) s hs
          have hfloor := Nat.floor_le hy
          change (ell : ℝ) ≤
            (epsilon / s - Cfloor) / periodicGainMean N p hp at hfloor
          have := mul_le_mul_of_nonneg_right hfloor hh.le
          rw [div_mul_cancel₀ _ (ne_of_gt hh)] at this
          linarith
        have hinterior (j : ℕ) (hj : j ∈ Finset.range (T - ell)) :
            |influenceEnergy N j *
                ((windowLength N T (j + 1) s : ℝ) - x)| ≤
              M * (D + U) := by
          rw [abs_mul, abs_of_nonneg (henergy_nonneg j)]
          apply mul_le_mul (henergy_upper j) ?_ (abs_nonneg _) hM
          apply (abs_le).2
          constructor
          · have hlowerR : (ell : ℝ) ≤
                (windowLength N T (j + 1) s : ℕ) := by
              exact_mod_cast hwindow_lower (Finset.mem_range.mp hj)
            linarith
          · have hu := hwindow_upper (j + 1)
            linarith
        have htail (j : ℕ) (hj : j ∈ Finset.Ico (T - ell) T) :
            |influenceEnergy N j *
                ((windowLength N T (j + 1) s : ℝ) - x)| ≤
              M * ((2 + U) * x) := by
          rw [abs_mul, abs_of_nonneg (henergy_nonneg j)]
          apply mul_le_mul (henergy_upper j) ?_ (abs_nonneg _) hM
          have hw0 : 0 ≤ (windowLength N T (j + 1) s : ℝ) :=
            Nat.cast_nonneg _
          have habs : |(windowLength N T (j + 1) s : ℝ) - x| ≤
              (windowLength N T (j + 1) s : ℝ) + x := by
            simpa [abs_of_nonneg hw0, abs_of_nonneg hx.le] using
              abs_sub (windowLength N T (j + 1) s : ℝ) x
          have hxone : 1 ≤ x := hD.trans hxD'.le
          have hUx : U ≤ U * x := by
            nlinarith [mul_nonneg (by linarith : 0 ≤ U) (sub_nonneg.mpr hxone)]
          have htailScalar :
              (windowLength N T (j + 1) s : ℝ) + x ≤ (2 + U) * x := by
            have hu := hwindow_upper (j + 1)
            nlinarith
          exact habs.trans htailScalar
        have hsplit := Finset.sum_range_add_sum_Ico
          (fun j => |influenceEnergy N j *
            ((windowLength N T (j + 1) s : ℝ) - x)|)
          (Nat.sub_le T ell)
        rw [← hsplit]
        calc
          (∑ j ∈ Finset.range (T - ell),
                |influenceEnergy N j *
                  ((windowLength N T (j + 1) s : ℝ) - x)|) +
              ∑ j ∈ Finset.Ico (T - ell) T,
                |influenceEnergy N j *
                  ((windowLength N T (j + 1) s : ℝ) - x)| ≤
              (∑ _j ∈ Finset.range (T - ell), M * (D + U)) +
                ∑ _j ∈ Finset.Ico (T - ell) T,
                  M * ((2 + U) * x) := by
            exact add_le_add
              (Finset.sum_le_sum fun j hj => hinterior j hj)
              (Finset.sum_le_sum fun j hj => htail j hj)
          _ = ((T - ell : ℕ) : ℝ) * (M * (D + U)) +
              ((T - (T - ell) : ℕ) : ℝ) *
                (M * ((2 + U) * x)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (T : ℝ) * (M * (D + U)) +
              M * (2 + U) * x ^ 2 := by
            have hprefix : ((T - ell : ℕ) : ℝ) ≤ (T : ℝ) := by
              exact_mod_cast Nat.sub_le T ell
            have htailcard : ((T - (T - ell) : ℕ) : ℝ) ≤ (ell : ℝ) := by
              exact_mod_cast (by omega : T - (T - ell) ≤ ell)
            have hDU : 0 ≤ M * (D + U) :=
              mul_nonneg hM (by linarith)
            have h2U : 0 ≤ M * (2 + U) :=
              mul_nonneg hM (by linarith)
            calc
              ((T - ell : ℕ) : ℝ) * (M * (D + U)) +
                    ((T - (T - ell) : ℕ) : ℝ) *
                      (M * ((2 + U) * x)) ≤
                  (T : ℝ) * (M * (D + U)) +
                    (ell : ℝ) * (M * ((2 + U) * x)) := by
                gcongr
              _ ≤ (T : ℝ) * (M * (D + U)) +
                    M * (2 + U) * x ^ 2 := by
                have := mul_le_mul_of_nonneg_right hell_le_x
                  (mul_nonneg h2U hx.le)
                nlinarith
          _ ≤ K * ((T : ℝ) + (s⁻¹) ^ 2) := by
            have hxformula : x = (epsilon / periodicGainMean N p hp) * s⁻¹ := by
              dsimp [x]
              field_simp
            rw [hxformula, mul_pow]
            have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
            have hinv : 0 ≤ (s⁻¹) ^ 2 := sq_nonneg _
            have hA : 0 ≤ M * (D + U) :=
              mul_nonneg hM (by linarith)
            have hB : 0 ≤
                M * (2 + U) * (epsilon / periodicGainMean N p hp) ^ 2 := by
              positivity
            dsimp [K]
            nlinarith

/-- Substitution of the periodic window and influence-prefix expansions into
the explicit comparator (7), before imposing the square-root stepsize band. -/
private theorem periodic_comparatorAt_expansion_of_window_zero
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ C₀ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hC₀ : 0 ≤ C₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : PositiveHorizon,
      ∀ s : AdmissibleDimensionlessStepsize n,
        |(windowLength N T.1 0 s.1 : ℝ) -
            epsilon / (s.1 * periodicGainMean N p hp)| ≤ C₀ →
        |comparatorAt N L Δ σ T s -
            (ADelta L Δ /
                (s.1 * periodicGainMean N p hp * T.1) +
              σ ^ 2 * periodicInfluenceMean N p * s.1 /
                (2 * periodicGainMean N p hp))| ≤
          K * (s.1 ^ 2 + 1 / T.1 + s.1 / T.1) := by
  classical
  obtain ⟨hh, _hhq, _hsum, _hcoord⟩ := periodic_phase_coefficients N p hp
  obtain ⟨Cgain, Cenergy, hCgain, hCenergy, hinterval⟩ :=
    periodic_interval_deviation_bounds N p hp
  obtain ⟨KS, hKS, hS⟩ := periodic_windowInfluenceSum_expansion N p hp
  have heps : 0 < epsilon := by norm_num [epsilon]
  have hA : 0 < ADelta L Δ := by
    unfold ADelta
    exact mul_pos hL hΔ
  let K : ℝ :=
    ADelta L Δ * C₀ / epsilon + σ ^ 2 * KS / (2 * epsilon) +
      σ ^ 2 * Cenergy / (2 * periodicGainMean N p hp)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro T s hW₀
  have hT : (0 : ℝ) < T.1 := Nat.cast_pos.mpr T.2
  have hs : 0 < s.1 := s.2.1
  let x : ℝ := epsilon / (s.1 * periodicGainMean N p hp)
  have hx : 0 < x := div_pos heps (mul_pos hs hh)
  have hQ :
      |(∑ j ∈ Finset.range T.1, influenceEnergy N j) -
          (T.1 : ℝ) * periodicInfluenceMean N p| ≤ Cenergy := by
    simpa using (hinterval 0 T.1 (Nat.zero_le _)).2
  have hSerr :
      |windowInfluenceSum N T.1 s.1 -
          x * ∑ j ∈ Finset.range T.1, influenceEnergy N j| ≤
        KS * ((T.1 : ℝ) + (s.1⁻¹) ^ 2) := by
    simpa [x] using hS T.1 s.1 hs
  let eW : ℝ := (windowLength N T.1 0 s.1 : ℝ) - x
  let eS : ℝ := windowInfluenceSum N T.1 s.1 -
    x * ∑ j ∈ Finset.range T.1, influenceEnergy N j
  let eQ : ℝ := (∑ j ∈ Finset.range T.1, influenceEnergy N j) -
    (T.1 : ℝ) * periodicInfluenceMean N p
  have heW : |eW| ≤ C₀ := by simpa [eW, x] using hW₀
  have heS : |eS| ≤ KS * ((T.1 : ℝ) + (s.1⁻¹) ^ 2) := by
    simpa [eS] using hSerr
  have heQ : |eQ| ≤ Cenergy := by simpa [eQ] using hQ
  have hid :
      comparatorAt N L Δ σ T s -
          (ADelta L Δ /
              (s.1 * periodicGainMean N p hp * T.1) +
            σ ^ 2 * periodicInfluenceMean N p * s.1 /
              (2 * periodicGainMean N p hp)) =
        ADelta L Δ / (epsilon * T.1) * eW +
          σ ^ 2 * s.1 ^ 2 / (2 * epsilon * T.1) * eS +
          σ ^ 2 * s.1 ^ 2 * x / (2 * epsilon * T.1) * eQ := by
    unfold comparatorAt comparatorNumerator
    dsimp [eW, eS, eQ, x]
    field_simp [ne_of_gt heps, ne_of_gt hT, ne_of_gt hs, ne_of_gt hh]
    ring
  have hcW : 0 ≤ ADelta L Δ / (epsilon * T.1) := by positivity
  have hcS : 0 ≤ σ ^ 2 * s.1 ^ 2 / (2 * epsilon * T.1) := by positivity
  have hcQ : 0 ≤ σ ^ 2 * s.1 ^ 2 * x / (2 * epsilon * T.1) := by
    positivity
  have htermW :
      |ADelta L Δ / (epsilon * T.1) * eW| ≤
        (ADelta L Δ * C₀ / epsilon) * (1 / T.1) := by
    rw [abs_mul, abs_of_nonneg hcW]
    calc
      ADelta L Δ / (epsilon * T.1) * |eW| ≤
          ADelta L Δ / (epsilon * T.1) * C₀ :=
        mul_le_mul_of_nonneg_left heW hcW
      _ = (ADelta L Δ * C₀ / epsilon) * (1 / T.1) := by ring
  have htermS :
      |σ ^ 2 * s.1 ^ 2 / (2 * epsilon * T.1) * eS| ≤
        (σ ^ 2 * KS / (2 * epsilon)) *
          (s.1 ^ 2 + 1 / T.1) := by
    rw [abs_mul, abs_of_nonneg hcS]
    calc
      σ ^ 2 * s.1 ^ 2 / (2 * epsilon * T.1) * |eS| ≤
          σ ^ 2 * s.1 ^ 2 / (2 * epsilon * T.1) *
            (KS * ((T.1 : ℝ) + (s.1⁻¹) ^ 2)) :=
        mul_le_mul_of_nonneg_left heS hcS
      _ = (σ ^ 2 * KS / (2 * epsilon)) *
          (s.1 ^ 2 + 1 / T.1) := by
        field_simp [ne_of_gt hs, ne_of_gt hT, ne_of_gt heps]
  have htermQ :
      |σ ^ 2 * s.1 ^ 2 * x / (2 * epsilon * T.1) * eQ| ≤
        (σ ^ 2 * Cenergy / (2 * periodicGainMean N p hp)) *
          (s.1 / T.1) := by
    rw [abs_mul, abs_of_nonneg hcQ]
    calc
      σ ^ 2 * s.1 ^ 2 * x / (2 * epsilon * T.1) * |eQ| ≤
          σ ^ 2 * s.1 ^ 2 * x / (2 * epsilon * T.1) * Cenergy :=
        mul_le_mul_of_nonneg_left heQ hcQ
      _ = (σ ^ 2 * Cenergy / (2 * periodicGainMean N p hp)) *
          (s.1 / T.1) := by
        dsimp [x]
        field_simp [ne_of_gt hs, ne_of_gt hT, ne_of_gt heps, ne_of_gt hh]
  rw [hid]
  calc
    |ADelta L Δ / (epsilon * T.1) * eW +
        σ ^ 2 * s.1 ^ 2 / (2 * epsilon * T.1) * eS +
        σ ^ 2 * s.1 ^ 2 * x / (2 * epsilon * T.1) * eQ| ≤
      |ADelta L Δ / (epsilon * T.1) * eW| +
        |σ ^ 2 * s.1 ^ 2 / (2 * epsilon * T.1) * eS| +
        |σ ^ 2 * s.1 ^ 2 * x / (2 * epsilon * T.1) * eQ| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ (ADelta L Δ * C₀ / epsilon) * (1 / T.1) +
        (σ ^ 2 * KS / (2 * epsilon)) * (s.1 ^ 2 + 1 / T.1) +
        (σ ^ 2 * Cenergy / (2 * periodicGainMean N p hp)) *
          (s.1 / T.1) := add_le_add (add_le_add htermW htermS) htermQ
    _ ≤ K * (s.1 ^ 2 + 1 / T.1 + s.1 / T.1) := by
      have hs2 : 0 ≤ s.1 ^ 2 := sq_nonneg _
      have hTin : 0 ≤ 1 / (T.1 : ℝ) := by positivity
      have hsT : 0 ≤ s.1 / (T.1 : ℝ) := div_nonneg hs.le hT.le
      have hkw : 0 ≤ ADelta L Δ * C₀ / epsilon := by positivity
      have hks : 0 ≤ σ ^ 2 * KS / (2 * epsilon) := by positivity
      have hkq : 0 ≤
          σ ^ 2 * Cenergy / (2 * periodicGainMean N p hp) := by positivity
      dsimp [K]
      nlinarith

/-- The time-zero window has only the periodic deviation and integer-rounding
error once its floor witness fits inside the horizon. -/
private theorem periodic_windowLength_zero_expansion
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p) :
    ∃ C₀ Cfloor : ℝ, 0 ≤ C₀ ∧ 0 ≤ Cfloor ∧
      ∀ T : PositiveHorizon, ∀ s : AdmissibleDimensionlessStepsize n,
        Cfloor / periodicGainMean N p hp + 1 <
            epsilon / (s.1 * periodicGainMean N p hp) →
          Nat.floor ((epsilon / s.1 - Cfloor) /
              periodicGainMean N p hp) ≤ T.1 →
            |(windowLength N T.1 0 s.1 : ℝ) -
              epsilon / (s.1 * periodicGainMean N p hp)| ≤ C₀ := by
  classical
  obtain ⟨hh, _hhq, _hsum, _hcoord⟩ := periodic_phase_coefficients N p hp
  obtain ⟨Cceil, hCceil, hwindowUpper⟩ :=
    periodic_windowLength_le_ceil N p hp
  obtain ⟨Cfloor, hCfloor, hwindowLower⟩ :=
    periodic_length_le_windowLength_of_budget N p hp
  let U : ℝ := Cceil / periodicGainMean N p hp + 1
  let D : ℝ := Cfloor / periodicGainMean N p hp + 1
  have hUzero : 0 ≤ U := by dsimp [U]; positivity
  have hDzero : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D + U, Cfloor, by dsimp [D, U]; positivity, hCfloor, ?_⟩
  intro T s
  intro hxD hellT
  let x : ℝ := epsilon / (s.1 * periodicGainMean N p hp)
  let ell : ℕ := Nat.floor ((epsilon / s.1 - Cfloor) /
    periodicGainMean N p hp)
  have hs : 0 < s.1 := s.2.1
  have hy : 0 ≤ (epsilon / s.1 - Cfloor) /
      periodicGainMean N p hp := by
    apply div_nonneg
    · have hscaled := hxD
      field_simp at hscaled
      have hnum : Cfloor ≤ epsilon / s.1 := by
        apply (le_div_iff₀ hs).2
        nlinarith [mul_pos hs hh]
      linarith
    · exact hh.le
  have hell_pos : 0 < ell := by
    apply Nat.floor_pos.mpr
    have hscaled := hxD
    field_simp at hscaled ⊢
    nlinarith
  have hell_lower : ell ≤ windowLength N T.1 0 s.1 := by
    apply hwindowLower T.1 0 ell (by omega) hell_pos (by simpa [ell] using hellT)
      s.1 hs
    have hfloor := Nat.floor_le hy
    change (ell : ℝ) ≤
      (epsilon / s.1 - Cfloor) / periodicGainMean N p hp at hfloor
    have hmul := mul_le_mul_of_nonneg_right hfloor hh.le
    rw [div_mul_cancel₀ _ (ne_of_gt hh)] at hmul
    linarith
  have hx_lt : x < (ell : ℝ) + D := by
    have hfloor := Nat.lt_floor_add_one
      ((epsilon / s.1 - Cfloor) / periodicGainMean N p hp)
    change (epsilon / s.1 - Cfloor) / periodicGainMean N p hp <
      (ell : ℝ) + 1 at hfloor
    have hxy : x =
        (epsilon / s.1 - Cfloor) / periodicGainMean N p hp +
          Cfloor / periodicGainMean N p hp := by
      dsimp [x]
      field_simp
      ring
    rw [hxy]
    dsimp [D]
    linarith
  have harg : 0 ≤ (epsilon / s.1 + Cceil) /
      periodicGainMean N p hp := by
    exact div_nonneg
      (add_nonneg (div_nonneg (by norm_num [epsilon]) hs.le) hCceil) hh.le
  have hupperNat := hwindowUpper T.1 0 s.1 hs
  have hupper : (windowLength N T.1 0 s.1 : ℝ) ≤ x + U := by
    calc
      (windowLength N T.1 0 s.1 : ℝ) ≤
          (Nat.ceil ((epsilon / s.1 + Cceil) /
            periodicGainMean N p hp) : ℕ) := by exact_mod_cast hupperNat
      _ ≤ (epsilon / s.1 + Cceil) / periodicGainMean N p hp + 1 :=
        (Nat.ceil_lt_add_one harg).le
      _ = x + U := by dsimp [x, U]; field_simp; ring
  change |(windowLength N T.1 0 s.1 : ℝ) - x| ≤ D + U
  apply (abs_le).2
  constructor
  · have hlowerR : (ell : ℝ) ≤
        (windowLength N T.1 0 s.1 : ℕ) := by exact_mod_cast hell_lower
    linarith
  · linarith

/-- Pointwise form of the comparator expansion on every horizon/stepsize pair
for which the source floor window is genuinely interior. -/
private theorem periodic_comparatorAt_expansion_interior
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) :
    ∃ K Cfloor : ℝ, 0 ≤ K ∧ 0 ≤ Cfloor ∧
      ∀ T : PositiveHorizon, ∀ s : AdmissibleDimensionlessStepsize n,
        Cfloor / periodicGainMean N p hp + 1 <
            epsilon / (s.1 * periodicGainMean N p hp) →
          Nat.floor ((epsilon / s.1 - Cfloor) /
              periodicGainMean N p hp) ≤ T.1 →
            |comparatorAt N L Δ σ T s -
                (ADelta L Δ /
                    (s.1 * periodicGainMean N p hp * T.1) +
                  σ ^ 2 * periodicInfluenceMean N p * s.1 /
                    (2 * periodicGainMean N p hp))| ≤
              K * (s.1 ^ 2 + 1 / T.1 + s.1 / T.1) := by
  obtain ⟨C₀, Cfloor, hC₀, hCfloor, hwindow⟩ :=
    periodic_windowLength_zero_expansion N p hp
  obtain ⟨K, hK, hcomparator⟩ :=
    periodic_comparatorAt_expansion_of_window_zero
      N p hp L Δ σ C₀ hL hΔ hC₀
  refine ⟨K, Cfloor, hK, hCfloor, ?_⟩
  intro T s hinterior hfits
  exact hcomparator T s (hwindow T s hinterior hfits)

/-- On the source's localized `s * sqrt T` band, the floor-selected periodic
window is eventually interior and the pointwise equation-(62) remainder is
uniformly `O(T⁻¹)`. -/
private theorem periodic_sqrt_band_pointwise_expansion
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ)
    (hh : 0 < periodicGainMean N p hp)
    (hhq : periodicGainMean N p hp ^ 2 / n ≤
      periodicInfluenceMean N p)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (KAt CfloorAt : ℝ) (hKAt : 0 ≤ KAt) (hCfloorAt : 0 ≤ CfloorAt)
    (hAtExpansion :
      ∀ T : PositiveHorizon, ∀ s : AdmissibleDimensionlessStepsize n,
        CfloorAt / periodicGainMean N p hp + 1 <
            epsilon / (s.1 * periodicGainMean N p hp) →
          Nat.floor ((epsilon / s.1 - CfloorAt) /
              periodicGainMean N p hp) ≤ T.1 →
            |comparatorAt N L Δ σ T s -
                (ADelta L Δ /
                    (s.1 * periodicGainMean N p hp * T.1) +
                  σ ^ 2 * periodicInfluenceMean N p * s.1 /
                    (2 * periodicGainMean N p hp))| ≤
              KAt * (s.1 ^ 2 + 1 / T.1 + s.1 / T.1)) :
    ∃ Kband : ℝ, 0 ≤ Kband ∧ ∃ Tband : ℕ,
      ∀ T : PositiveHorizon, Tband ≤ T.1 →
        ∀ s : AdmissibleDimensionlessStepsize n,
          c / Real.sqrt T.1 ≤ s.1 →
          s.1 ≤ C / Real.sqrt T.1 →
          (CfloorAt / periodicGainMean N p hp + 1 <
              epsilon / (s.1 * periodicGainMean N p hp) ∧
            Nat.floor ((epsilon / s.1 - CfloorAt) /
              periodicGainMean N p hp) ≤ T.1) ∧
          |comparatorAt N L Δ σ T s -
              (ADelta L Δ /
                  (s.1 * periodicGainMean N p hp * T.1) +
                σ ^ 2 * periodicInfluenceMean N p * s.1 /
                  (2 * periodicGainMean N p hp))| ≤ Kband / T.1 := by
  let h := periodicGainMean N p hp
  let q := periodicInfluenceMean N p
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hq : 0 < q := by
    dsimp [q]
    exact lt_of_lt_of_le (div_pos (sq_pos_of_pos hh) hn) hhq
  have heps : 0 < epsilon := by norm_num [epsilon]
  let a₁ := ((CfloorAt + h) * C) / epsilon
  let a₂ := epsilon / (c * h)
  have ha₁ : 0 ≤ a₁ := by
    dsimp [a₁, h]
    positivity
  have ha₂ : 0 ≤ a₂ := by
    dsimp [a₂, h]
    positivity
  let onset : ℝ := max (a₁ ^ 2) (max (a₂ ^ 2) (max (1 / q) 1))
  obtain ⟨Tband, hTband⟩ := exists_nat_gt onset
  let Kband := KAt * (C ^ 2 + 1 + C)
  refine ⟨Kband, ?_, Tband, ?_⟩
  · dsimp [Kband]
    positivity
  · intro T hTlarge s hsLower hsUpper
    have hTR : (0 : ℝ) < T.1 := by exact_mod_cast T.2
    have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hTR
    have hsqrtSq : Real.sqrt T.1 ^ 2 = (T.1 : ℝ) :=
      Real.sq_sqrt hTR.le
    have honsetT : onset < (T.1 : ℝ) :=
      hTband.trans_le (by exact_mod_cast hTlarge)
    have ha₁Sq : a₁ ^ 2 < (T.1 : ℝ) := by
      exact lt_of_le_of_lt (le_max_left _ _) honsetT
    have ha₂Sq : a₂ ^ 2 < (T.1 : ℝ) := by
      exact lt_of_le_of_lt (le_max_of_le_right (le_max_left _ _)) honsetT
    have honeT : (1 : ℝ) < T.1 := by
      exact lt_of_le_of_lt
        (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) honsetT
    have ha₁Sqrt : a₁ < Real.sqrt T.1 := by
      nlinarith
    have ha₂Sqrt : a₂ < Real.sqrt T.1 := by
      nlinarith
    have hsqrtOne : 1 ≤ Real.sqrt T.1 := by
      nlinarith
    have hspos : 0 < s.1 := s.2.1
    have hsmall : (CfloorAt + h) * s.1 < epsilon := by
      have hmul : (CfloorAt + h) * s.1 ≤
          (CfloorAt + h) * (C / Real.sqrt T.1) := by
        exact mul_le_mul_of_nonneg_left hsUpper
          (add_nonneg hCfloorAt hh.le)
      have hnum : (CfloorAt + h) * C < epsilon * Real.sqrt T.1 := by
        have := (div_lt_iff₀ heps).mp ha₁Sqrt
        simpa [a₁, mul_comm, mul_left_comm, mul_assoc] using this
      have hfrac : (CfloorAt + h) * C / Real.sqrt T.1 < epsilon :=
        (div_lt_iff₀ hsqrt).2 (by simpa [mul_comm] using hnum)
      exact hmul.trans_lt (by simpa [mul_div_assoc] using hfrac)
    have hinterior : CfloorAt / h + 1 < epsilon / (s.1 * h) := by
      dsimp [h]
      field_simp [ne_of_gt hh, ne_of_gt hspos]
      nlinarith [hsmall]
    have hcsqrt : c ≤ s.1 * Real.sqrt T.1 :=
      (div_le_iff₀ hsqrt).mp hsLower
    have hepsBound : epsilon < c * h * Real.sqrt T.1 := by
      have := (div_lt_iff₀ (mul_pos hc hh)).mp ha₂Sqrt
      simpa [a₂, h, mul_comm, mul_left_comm, mul_assoc] using this
    have hepsRatio : epsilon / (s.1 * h) ≤ (T.1 : ℝ) := by
      apply (div_le_iff₀ (mul_pos hspos hh)).2
      calc
        epsilon ≤ c * h * Real.sqrt T.1 := hepsBound.le
        _ ≤ s.1 * Real.sqrt T.1 * h * Real.sqrt T.1 := by
          nlinarith [mul_nonneg hh.le hsqrt.le]
        _ = s.1 * h * Real.sqrt T.1 ^ 2 := by ring
        _ = (T.1 : ℝ) * (s.1 * h) := by rw [hsqrtSq]; ring
    have harg : (epsilon / s.1 - CfloorAt) / h ≤ (T.1 : ℝ) := by
      calc
        (epsilon / s.1 - CfloorAt) / h ≤ epsilon / (s.1 * h) := by
          calc
            (epsilon / s.1 - CfloorAt) / h ≤ (epsilon / s.1) / h :=
              div_le_div_of_nonneg_right
                (sub_le_self (epsilon / s.1) hCfloorAt) hh.le
            _ = epsilon / (s.1 * h) := by
              field_simp [ne_of_gt hh, ne_of_gt hspos]
        _ ≤ (T.1 : ℝ) := hepsRatio
    have hfits : Nat.floor ((epsilon / s.1 - CfloorAt) / h) ≤ T.1 :=
      Nat.floor_le_of_le harg
    have hsC : s.1 ≤ C := by
      calc
        s.1 ≤ C / Real.sqrt T.1 := hsUpper
        _ ≤ C := by
          apply (div_le_iff₀ hsqrt).2
          nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hsqrtOne)]
    have hsSq : s.1 ^ 2 ≤ C ^ 2 / T.1 := by
      calc
        s.1 ^ 2 ≤ (C / Real.sqrt T.1) ^ 2 :=
          (sq_le_sq₀ hspos.le (div_nonneg hC.le hsqrt.le)).2 hsUpper
        _ = C ^ 2 / T.1 := by rw [div_pow, hsqrtSq]
    have hsDiv : s.1 / T.1 ≤ C / T.1 :=
      div_le_div_of_nonneg_right hsC hTR.le
    have hrem : s.1 ^ 2 + 1 / T.1 + s.1 / T.1 ≤
        (C ^ 2 + 1 + C) / T.1 := by
      calc
        s.1 ^ 2 + 1 / T.1 + s.1 / T.1 ≤
            C ^ 2 / T.1 + 1 / T.1 + C / T.1 := by linarith
        _ = (C ^ 2 + 1 + C) / T.1 := by ring
    have hexp := hAtExpansion T s (by simpa [h] using hinterior)
      (by simpa [h] using hfits)
    refine ⟨⟨by simpa [h] using hinterior, by simpa [h] using hfits⟩, ?_⟩
    calc
      |comparatorAt N L Δ σ T s -
          (ADelta L Δ / (s.1 * periodicGainMean N p hp * T.1) +
            σ ^ 2 * periodicInfluenceMean N p * s.1 /
              (2 * periodicGainMean N p hp))| ≤
          KAt * (s.1 ^ 2 + 1 / T.1 + s.1 / T.1) := hexp
      _ ≤ KAt * ((C ^ 2 + 1 + C) / T.1) :=
        mul_le_mul_of_nonneg_left hrem hKAt
      _ = Kband / T.1 := by
        dsimp [Kband]
        ring

/-- Equation (62) for the explicit periodic comparator.  The upper direction
uses the exact balanced admissible trial; the lower direction uses the
localized additive near-minimizer and reciprocal-linear balance. -/
private theorem periodic_comparator_equation62
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (hh : 0 < periodicGainMean N p hp)
    (hhq : periodicGainMean N p hp ^ 2 / n ≤
      periodicInfluenceMean N p)
    (KAt CfloorAt : ℝ) (hKAt : 0 ≤ KAt) (hCfloorAt : 0 ≤ CfloorAt)
    (hAtExpansion :
      ∀ T : PositiveHorizon, ∀ s : AdmissibleDimensionlessStepsize n,
        CfloorAt / periodicGainMean N p hp + 1 <
            epsilon / (s.1 * periodicGainMean N p hp) →
          Nat.floor ((epsilon / s.1 - CfloorAt) /
              periodicGainMean N p hp) ≤ T.1 →
            |comparatorAt N L Δ σ T s -
                (ADelta L Δ /
                    (s.1 * periodicGainMean N p hp * T.1) +
                  σ ^ 2 * periodicInfluenceMean N p * s.1 /
                    (2 * periodicGainMean N p hp))| ≤
              KAt * (s.1 ^ 2 + 1 / T.1 + s.1 / T.1))
    (Tloc : ℕ)
    (hlocalized : ∀ T : PositiveHorizon, Tloc ≤ T.1 →
      ∃ s : AdmissibleDimensionlessStepsize n,
        comparatorAt N L Δ σ T s ≤
            comparator N L Δ σ T + ADelta L Δ / T.1 ∧
          comparatorStepLowerConstant N L Δ σ / Real.sqrt T.1 ≤ s.1 ∧
          s.1 ≤ comparatorStepUpperConstant N L Δ σ /
            Real.sqrt T.1 ∧
          s.1 ≤ correctedCenterStepCap N ∧
          epsilon / 2 ≤ s.1 * ∑ t ∈ Finset.range T.1, gain N t) :
    ∃ KB : ℝ, 0 ≤ KB ∧ ∃ TB : ℕ, ∀ T : PositiveHorizon,
      TB ≤ T.1 →
      |comparator N L Δ σ T -
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1))| ≤ KB / T.1 := by
  let A := ADelta L Δ
  let h := periodicGainMean N p hp
  let q := periodicInfluenceMean N p
  let a := A / h
  let b := σ ^ 2 * q / (2 * h)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hA : 0 < A := by dsimp [A, ADelta]; exact mul_pos hL hΔ
  have hq : 0 < q := by
    dsimp [q]
    exact lt_of_lt_of_le (div_pos (sq_pos_of_pos hh) hn) hhq
  have ha : 0 < a := div_pos hA hh
  have hb : 0 < b := by dsimp [b]; positivity
  let d := Real.sqrt (a / b)
  have hd : 0 < d := Real.sqrt_pos.2 (div_pos ha hb)
  have hdSq : d ^ 2 = a / b := by
    exact Real.sq_sqrt (div_pos ha hb).le
  have habd : a = b * d ^ 2 := by
    rw [hdSq]
    field_simp [ne_of_gt hb]
  have hsqrtProd : Real.sqrt a * Real.sqrt b = b * d := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, mul_pow, hdSq]
    field_simp [ne_of_gt hb]
  let cB := comparatorStepLowerConstant N L Δ σ
  let CB := comparatorStepUpperConstant N L Δ σ
  have hconstants := comparator_localization_constants_pos N L Δ σ hL hΔ hσ
  have hcB : 0 < cB := by simpa [cB] using hconstants.2.2.2.2.1
  have hCB : 0 < CB := by simpa [CB] using hconstants.2.2.2.2.2
  let c := min cB d
  let C := max CB d
  have hc : 0 < c := lt_min hcB hd
  have hC : 0 < C := lt_of_lt_of_le hCB (le_max_left _ _)
  obtain ⟨Kband, hKband, Tband, hband⟩ :=
    periodic_sqrt_band_pointwise_expansion N p hp L Δ σ hL hΔ
      hh hhq c C hc hC KAt CfloorAt hKAt hCfloorAt hAtExpansion
  let capScale : ℝ := 64 * (n : ℝ) * d
  obtain ⟨Ttrial, hTtrial⟩ := exists_nat_gt (capScale ^ 2)
  let TB := max Tloc (max Tband Ttrial)
  let KB := A + Kband
  refine ⟨KB, ?_, TB, ?_⟩
  · dsimp [KB]
    exact add_nonneg hA.le hKband
  · intro T hTlarge
    have hlocT : Tloc ≤ T.1 := le_trans (le_max_left _ _) hTlarge
    have hbandT : Tband ≤ T.1 :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTlarge
    have htrialT : Ttrial ≤ T.1 :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTlarge
    have hTR : (0 : ℝ) < T.1 := by exact_mod_cast T.2
    have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hTR
    have hsqrtSq : Real.sqrt T.1 ^ 2 = (T.1 : ℝ) := Real.sq_sqrt hTR.le
    have hcapScale : 0 ≤ capScale := by dsimp [capScale]; positivity
    have hcapSq : capScale ^ 2 < (T.1 : ℝ) :=
      hTtrial.trans_le (by exact_mod_cast htrialT)
    have hcapRoot : capScale < Real.sqrt T.1 := by nlinarith
    have htrialCap : d / Real.sqrt T.1 ≤ 1 / (64 * (n : ℝ)) := by
      apply (div_le_iff₀ hsqrt).2
      calc
        d ≤ Real.sqrt T.1 / (64 * (n : ℝ)) := by
          apply (le_div_iff₀ (mul_pos (by norm_num) hn)).2
          dsimp [capScale] at hcapRoot
          simpa [mul_comm, mul_left_comm, mul_assoc] using hcapRoot.le
        _ = 1 / (64 * (n : ℝ)) * Real.sqrt T.1 := by ring
    let sstar : AdmissibleDimensionlessStepsize n :=
      ⟨d / Real.sqrt T.1, div_pos hd hsqrt, htrialCap⟩
    have hstarLower : c / Real.sqrt T.1 ≤ sstar.1 := by
      dsimp [sstar, c]
      exact div_le_div_of_nonneg_right (min_le_right _ _) hsqrt.le
    have hstarUpper : sstar.1 ≤ C / Real.sqrt T.1 := by
      dsimp [sstar, C]
      exact div_le_div_of_nonneg_right (le_max_right _ _) hsqrt.le
    have hstarExpansion := (hband T hbandT sstar hstarLower hstarUpper).2
    have hmainBalance :
        2 * Real.sqrt a * Real.sqrt b / Real.sqrt T.1 =
          σ * Real.sqrt (2 * A * q / (h ^ 2 * T.1)) := by
      have hrad : 0 ≤ 2 * A * q / (h ^ 2 * (T.1 : ℝ)) := by positivity
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      have hleft :
          (2 * Real.sqrt a * Real.sqrt b / Real.sqrt T.1) ^ 2 =
            4 * a * b / T.1 := by
        rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt ha.le,
          Real.sq_sqrt hb.le, Real.sq_sqrt hTR.le]
        ring
      have hright :
          (σ * Real.sqrt (2 * A * q / (h ^ 2 * T.1))) ^ 2 =
            σ ^ 2 * (2 * A * q / (h ^ 2 * T.1)) := by
        rw [mul_pow, Real.sq_sqrt hrad]
      rw [hleft, hright]
      dsimp [a, b]
      field_simp [ne_of_gt hh, ne_of_gt hTR]
      ring
    have hstarLead :
        A / (sstar.1 * h * T.1) + σ ^ 2 * q * sstar.1 / (2 * h) =
          2 * Real.sqrt a * Real.sqrt b / Real.sqrt T.1 := by
      rw [show A / (sstar.1 * h * T.1) = a / (sstar.1 * T.1) by
        dsimp [a]
        field_simp [ne_of_gt hh, ne_of_gt sstar.2.1, ne_of_gt hTR]]
      rw [show σ ^ 2 * q * sstar.1 / (2 * h) = b * sstar.1 by
        dsimp [b]
        ring]
      dsimp [sstar]
      calc
        a / ((d / Real.sqrt T.1) * T.1) + b * (d / Real.sqrt T.1) =
            (a / d + b * d) / Real.sqrt T.1 := by
          field_simp [ne_of_gt hd, ne_of_gt hsqrt, ne_of_gt hTR]
          nlinarith [hsqrtSq]
        _ = (2 * b * d) / Real.sqrt T.1 := by rw [habd]; field_simp; ring
        _ = 2 * Real.sqrt a * Real.sqrt b / Real.sqrt T.1 := by
          rw [show 2 * Real.sqrt a * Real.sqrt b =
            2 * (Real.sqrt a * Real.sqrt b) by ring, hsqrtProd]
          ring
    have hstarLeadMain :
        ADelta L Δ /
              (sstar.1 * periodicGainMean N p hp * T.1) +
            σ ^ 2 * periodicInfluenceMean N p * sstar.1 /
              (2 * periodicGainMean N p hp) =
          σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) := by
      simpa [A, h, q] using hstarLead.trans hmainBalance
    have hstarUpperAt : comparatorAt N L Δ σ T sstar ≤
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1)) + Kband / T.1 := by
      rw [← hstarLeadMain]
      linarith [(abs_le.mp hstarExpansion).2]
    have hrange : comparatorAt N L Δ σ T sstar ∈
        Set.range (fun s : AdmissibleDimensionlessStepsize n =>
          comparatorAt N L Δ σ T s) := ⟨sstar, rfl⟩
    have hinf := csInf_le (comparatorAt_range_bddBelow N L Δ σ hL hΔ T) hrange
    have hupper : comparator N L Δ σ T ≤
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1)) + Kband / T.1 := by
      exact hinf.trans hstarUpperAt
    obtain ⟨s, hsNear, hsLow, hsHigh, hsCap, hsBudget⟩ := hlocalized T hlocT
    have hsBandLow : c / Real.sqrt T.1 ≤ s.1 := by
      calc
        c / Real.sqrt T.1 ≤ cB / Real.sqrt T.1 :=
          div_le_div_of_nonneg_right (min_le_left _ _) hsqrt.le
        _ ≤ s.1 := by simpa [cB] using hsLow
    have hsBandHigh : s.1 ≤ C / Real.sqrt T.1 := by
      calc
        s.1 ≤ CB / Real.sqrt T.1 := by simpa [CB] using hsHigh
        _ ≤ C / Real.sqrt T.1 :=
          div_le_div_of_nonneg_right (le_max_left _ _) hsqrt.le
    have hsExpansion := (hband T hbandT s hsBandLow hsBandHigh).2
    have hbalance := reciprocal_linear_balance ha hb
      (inv_pos.mpr s.2.1) hTR
    have hbalanceLead :
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) ≤
          ADelta L Δ / (s.1 * periodicGainMean N p hp * T.1) +
            σ ^ 2 * periodicInfluenceMean N p * s.1 /
              (2 * periodicGainMean N p hp) := by
      rw [← hmainBalance]
      convert hbalance using 1 <;> dsimp [a, b, A, h, q]
      field_simp [ne_of_gt s.2.1, ne_of_gt hh, ne_of_gt hTR]
      <;> ring
    have hleadNear :
        ADelta L Δ / (s.1 * periodicGainMean N p hp * T.1) +
            σ ^ 2 * periodicInfluenceMean N p * s.1 /
              (2 * periodicGainMean N p hp) ≤
          comparatorAt N L Δ σ T s + Kband / T.1 :=
      by linarith [(abs_le.mp hsExpansion).1]
    have hlower :
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) ≤
          comparator N L Δ σ T + KB / T.1 := by
      calc
        _ ≤ ADelta L Δ /
              (s.1 * periodicGainMean N p hp * T.1) +
            σ ^ 2 * periodicInfluenceMean N p * s.1 /
              (2 * periodicGainMean N p hp) := hbalanceLead
        _ ≤ comparatorAt N L Δ σ T s + Kband / T.1 := hleadNear
        _ ≤ (comparator N L Δ σ T + ADelta L Δ / T.1) +
              Kband / T.1 := by
          simpa [add_assoc, add_comm, add_left_comm] using
            add_le_add_right hsNear (Kband / T.1)
        _ = comparator N L Δ σ T + KB / T.1 := by
          dsimp [KB, A]
          ring
    apply (abs_le).2
    constructor
    · have : -(KB / T.1) ≤ comparator N L Δ σ T -
          σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) := by linarith
      exact this
    · have hKle : Kband / T.1 ≤ KB / T.1 := by
        apply div_le_div_of_nonneg_right _ hTR.le
        dsimp [KB, A]
        linarith
      linarith

/-- Rescaling equation (62) through the explicit reciprocal-square definition
of effective node count gives the periodic effective-size limit. -/
private theorem periodic_effective_node_limit_of_equation62
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ)
    (hh : 0 < periodicGainMean N p hp)
    (hhq : periodicGainMean N p hp ^ 2 / n ≤
      periodicInfluenceMean N p)
    (KB : ℝ) (hKB : 0 ≤ KB) (TB : ℕ)
    (hEquation62 : ∀ T : PositiveHorizon, TB ≤ T.1 →
      |comparator N L Δ σ T -
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1))| ≤ KB / T.1) :
    ∀ ε : ℝ, 0 < ε → ∃ Tε : ℕ, ∀ T : PositiveHorizon,
      Tε ≤ T.1 → ∀ hB : 0 < comparator N L Δ σ T,
        |effectiveNodeCount N L Δ σ ⟨T, hB⟩ -
          periodicGainMean N p hp ^ 2 / periodicInfluenceMean N p| < ε := by
  let A := ADelta L Δ
  let h := periodicGainMean N p hp
  let q := periodicInfluenceMean N p
  let D := 2 * A * σ ^ 2
  let z := h ^ 2 / q
  let r := σ * Real.sqrt (2 * A * q / h ^ 2)
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hA : 0 < A := by dsimp [A, ADelta]; exact mul_pos hL hΔ
  have hq : 0 < q := by
    dsimp [q]
    exact lt_of_lt_of_le (div_pos (sq_pos_of_pos hh) hn) hhq
  have hD : 0 < D := by dsimp [D]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hrad : 0 < 2 * A * q / h ^ 2 := by positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hrSq : r ^ 2 = D / z := by
    dsimp [r, D, z]
    rw [mul_pow, Real.sq_sqrt hrad.le]
    field_simp [ne_of_gt hh, ne_of_gt hq]
  intro ε hε
  let u : ℝ := 2 * KB / r
  let v : ℝ := 10 * D * KB / (ε * r ^ 3)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  let onset : ℝ := max (u ^ 2) (v ^ 2)
  obtain ⟨Tscale, hTscale⟩ := exists_nat_gt onset
  refine ⟨max TB Tscale, ?_⟩
  intro T hTlarge hB
  have hTB : TB ≤ T.1 := le_trans (le_max_left _ _) hTlarge
  have hscaleT : Tscale ≤ T.1 := le_trans (le_max_right _ _) hTlarge
  have hTR : (0 : ℝ) < T.1 := by exact_mod_cast T.2
  have hsqrt : 0 < Real.sqrt T.1 := Real.sqrt_pos.2 hTR
  have hsqrtSq : Real.sqrt T.1 ^ 2 = (T.1 : ℝ) := Real.sq_sqrt hTR.le
  have honset : onset < (T.1 : ℝ) :=
    hTscale.trans_le (by exact_mod_cast hscaleT)
  have huSq : u ^ 2 < (T.1 : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) honset
  have hvSq : v ^ 2 < (T.1 : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) honset
  have huRoot : u < Real.sqrt T.1 := by nlinarith
  have hvRoot : v < Real.sqrt T.1 := by nlinarith
  have hmain :
      σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1)) = r / Real.sqrt T.1 := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    have hradT : 0 ≤ 2 * A * q / (h ^ 2 * (T.1 : ℝ)) := by positivity
    rw [mul_pow, Real.sq_sqrt hradT]
    rw [div_pow, mul_pow, Real.sq_sqrt hrad.le, Real.sq_sqrt hTR.le]
    dsimp [A, h, q, r]
    field_simp [ne_of_gt hh, ne_of_gt hTR]
  let y := Real.sqrt T.1 * comparator N L Δ σ T
  have hy : 0 < y := mul_pos hsqrt hB
  have hscaled : |y - r| ≤ KB / Real.sqrt T.1 := by
    have heq := hEquation62 T hTB
    rw [hmain] at heq
    have hmul := mul_le_mul_of_nonneg_left heq hsqrt.le
    calc
      |y - r| = Real.sqrt T.1 *
          |comparator N L Δ σ T - r / Real.sqrt T.1| := by
        rw [show y - r = Real.sqrt T.1 *
            (comparator N L Δ σ T - r / Real.sqrt T.1) by
          dsimp [y]
          field_simp [ne_of_gt hsqrt]]
        rw [abs_mul, abs_of_pos hsqrt]
      _ ≤ Real.sqrt T.1 * (KB / T.1) := hmul
      _ = KB / Real.sqrt T.1 := by
        field_simp [ne_of_gt hsqrt, ne_of_gt hTR]
        nlinarith [hsqrtSq]
  have hhalf : KB / Real.sqrt T.1 < r / 2 := by
    dsimp [u] at huRoot
    apply (div_lt_iff₀ hsqrt).2
    field_simp [ne_of_gt hr] at huRoot
    nlinarith
  have hsmall : KB / Real.sqrt T.1 < ε * r ^ 3 / (10 * D) := by
    dsimp [v] at hvRoot
    apply (div_lt_iff₀ hsqrt).2
    field_simp [ne_of_gt hε, ne_of_gt hr, ne_of_gt hD] at hvRoot ⊢
    nlinarith
  have hyLower : r / 2 < y := by
    have := (abs_le.mp hscaled).1
    linarith
  have hyUpper : y < 3 * r / 2 := by
    have := (abs_le.mp hscaled).2
    linarith
  have hySqLower : r ^ 2 / 4 ≤ y ^ 2 := by
    have hsquares := (sq_le_sq₀ (by positivity : 0 ≤ r / 2) hy.le).2 hyLower.le
    nlinarith
  have heffective : effectiveNodeCount N L Δ σ ⟨T, hB⟩ = D / y ^ 2 := by
    unfold effectiveNodeCount
    dsimp [D, y, A]
    field_simp [ne_of_gt hsqrt, ne_of_gt hB, ne_of_gt hTR]
    nlinarith [hsqrtSq]
  have htarget : h ^ 2 / q = D / r ^ 2 := by
    change z = D / r ^ 2
    rw [hrSq]
    field_simp [ne_of_gt hz, ne_of_gt hD]
  rw [heffective]
  change |D / y ^ 2 - z| < ε
  rw [show z = D / r ^ 2 by simpa [z] using htarget]
  have hdiff : |D / y ^ 2 - D / r ^ 2| =
      D * |y - r| * (y + r) / (y ^ 2 * r ^ 2) := by
    have heq : D / y ^ 2 - D / r ^ 2 =
        D * (r - y) * (r + y) / (y ^ 2 * r ^ 2) := by
      field_simp [ne_of_gt hy, ne_of_gt hr]
      ring
    rw [heq, abs_div, abs_mul, abs_mul, abs_mul]
    rw [abs_of_pos (mul_pos (by norm_num) hA),
      abs_of_pos (sq_pos_of_pos hσ), abs_sub_comm, abs_of_pos (add_pos hr hy),
      abs_of_pos (mul_pos (sq_pos_of_pos hy) (sq_pos_of_pos hr))]
    dsimp [D]
    ring
  rw [hdiff]
  have hsum : y + r ≤ 5 * r / 2 := by linarith
  have hnum : D * |y - r| * (y + r) ≤
      D * (KB / Real.sqrt T.1) * (5 * r / 2) := by
    gcongr
  have hden : r ^ 4 / 4 ≤ y ^ 2 * r ^ 2 := by
    have := mul_le_mul_of_nonneg_right hySqLower (sq_nonneg r)
    nlinarith
  have hnumNonneg : 0 ≤ D * (KB / Real.sqrt T.1) * (5 * r / 2) := by positivity
  calc
    D * |y - r| * (y + r) / (y ^ 2 * r ^ 2) ≤
        (D * (KB / Real.sqrt T.1) * (5 * r / 2)) /
          (y ^ 2 * r ^ 2) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg (sq_nonneg y) (sq_nonneg r))
    _ ≤ (D * (KB / Real.sqrt T.1) * (5 * r / 2)) /
          (r ^ 4 / 4) := by
      exact div_le_div_of_nonneg_left hnumNonneg
        (by positivity : 0 < r ^ 4 / 4) hden
    _ = 10 * D * (KB / Real.sqrt T.1) / r ^ 3 := by
      field_simp [ne_of_gt hr]
      ring
    _ < ε := by
      apply (div_lt_iff₀ (pow_pos hr 3)).2
      have hscaledSmall :
          (10 * D) * (KB / Real.sqrt T.1) <
            (10 * D) * (ε * r ^ 3 / (10 * D)) :=
        mul_lt_mul_of_pos_left hsmall (mul_pos (by norm_num) hD)
      calc
        10 * D * (KB / Real.sqrt T.1) <
            10 * D * (ε * r ^ 3 / (10 * D)) := by
          simpa [mul_assoc] using hscaledSmall
        _ = ε * r ^ 3 := by
          field_simp [ne_of_gt hD]

/-- The source choice `m = max 1 (ceil (T^(1/6)))` eventually satisfies the
valid-use restriction `m ≤ sqrt T` in equation (63). -/
private theorem periodic_risk_block_length_le_sqrt_eventually :
    ∃ Tblock : ℕ, ∀ T : PositiveHorizon, Tblock ≤ T.1 →
      (periodicRiskBlockLength T : ℝ) ≤ Real.sqrt (T.1 : ℝ) := by
  refine ⟨64, ?_⟩
  intro T hT
  have hTR : (64 : ℝ) ≤ (T.1 : ℝ) := by exact_mod_cast hT
  have hTnonneg : (0 : ℝ) ≤ (T.1 : ℝ) := by positivity
  let x : ℝ := Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)
  have hxnonneg : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg hTnonneg _
  have hxpow : x ^ (6 : ℕ) = (T.1 : ℝ) := by
    dsimp [x]
    calc
      (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) ^ (6 : ℕ) =
          Real.rpow (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) := by
        exact (Real.rpow_natCast
          (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) 6).symm
      _ = Real.rpow (T.1 : ℝ) (((1 : ℝ) / 6) * 6) :=
        (Real.rpow_mul hTnonneg ((1 : ℝ) / 6) (6 : ℝ)).symm
      _ = (T.1 : ℝ) := by norm_num
  have hxTwo : (2 : ℝ) ≤ x := by
    by_contra hnot
    have hxlt : x < 2 := lt_of_not_ge hnot
    have hp := pow_lt_pow_left₀ hxlt hxnonneg (by norm_num : (6 : ℕ) ≠ 0)
    rw [hxpow] at hp
    norm_num at hp
    linarith
  have hxmul : 2 * x ≤ x * x := by
    exact mul_le_mul_of_nonneg_right hxTwo hxnonneg
  have hxcube : 2 * (x * x) ≤ x * x * x := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hxmul hxnonneg
  have hxAdd : x + 2 ≤ x ^ (3 : ℕ) := by
    norm_num [pow_succ]
    nlinarith
  have hxSqrt : x ^ (3 : ℕ) = Real.sqrt (T.1 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    dsimp [x]
    calc
      (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) ^ (3 : ℕ) =
          Real.rpow (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) (3 : ℝ) := by
        exact (Real.rpow_natCast
          (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) 3).symm
      _ = Real.rpow (T.1 : ℝ) (((1 : ℝ) / 6) * 3) :=
        (Real.rpow_mul hTnonneg ((1 : ℝ) / 6) (3 : ℝ)).symm
      _ = Real.rpow (T.1 : ℝ) ((1 : ℝ) / 2) := by norm_num
  unfold periodicRiskBlockLength
  calc
    ((max 1 (Nat.ceil (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6))) : ℕ) : ℝ) ≤
        Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6) + 2 :=
      natCast_max_one_ceil_le_add_two _ (Real.rpow_nonneg hTnonneg _)
    _ = x + 2 := by rfl
    _ ≤ x ^ (3 : ℕ) := hxAdd
    _ = Real.sqrt (T.1 : ℝ) := hxSqrt

/-- The source schedule `m = max 1 (ceil (T^(1/6)))` is controlled by the
single scale `r = T^(1/6)`.  These exact power identities are the scalar
normalization used when collecting the equation-(63) remainder. -/
private theorem periodic_risk_schedule_facts (T : PositiveHorizon) :
    let r := Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)
    (1 : ℝ) ≤ r ∧
      r ^ (6 : ℕ) = (T.1 : ℝ) ∧
      r ≤ (periodicRiskBlockLength T : ℝ) ∧
      (periodicRiskBlockLength T : ℝ) ≤ r + 2 ∧
      Real.rpow (T.1 : ℝ) ((2 : ℝ) / 3) = r ^ (4 : ℕ) := by
  dsimp only
  have hTpos : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
  have hTnonneg : 0 ≤ (T.1 : ℝ) := hTpos.le
  let r := Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)
  have hrpos : 0 < r := Real.rpow_pos_of_pos hTpos _
  have hrpow : r ^ (6 : ℕ) = (T.1 : ℝ) := by
    dsimp [r]
    calc
      (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) ^ (6 : ℕ) =
          Real.rpow (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) (6 : ℝ) := by
        exact (Real.rpow_natCast
          (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) 6).symm
      _ = Real.rpow (T.1 : ℝ) (((1 : ℝ) / 6) * 6) :=
        (Real.rpow_mul hTnonneg ((1 : ℝ) / 6) (6 : ℝ)).symm
      _ = (T.1 : ℝ) := by norm_num
  have hrone : (1 : ℝ) ≤ r := by
    dsimp [r]
    exact Real.one_le_rpow (by exact_mod_cast T.2) (by norm_num)
  have hrceil : r ≤ (Nat.ceil r : ℝ) := Nat.le_ceil r
  have hceilOne : 1 ≤ Nat.ceil r := by
    exact_mod_cast hrone.trans hrceil
  have hmLower : r ≤ (periodicRiskBlockLength T : ℝ) := by
    unfold periodicRiskBlockLength
    rw [max_eq_right hceilOne]
    exact hrceil
  have hmUpper : (periodicRiskBlockLength T : ℝ) ≤ r + 2 := by
    unfold periodicRiskBlockLength
    simpa [r] using natCast_max_one_ceil_le_add_two r hrpos.le
  have hrFour : Real.rpow (T.1 : ℝ) ((2 : ℝ) / 3) = r ^ (4 : ℕ) := by
    dsimp [r]
    calc
      Real.rpow (T.1 : ℝ) ((2 : ℝ) / 3) =
          Real.rpow (T.1 : ℝ) (((1 : ℝ) / 6) * 4) := by norm_num
      _ = Real.rpow (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) (4 : ℝ) :=
        Real.rpow_mul hTnonneg ((1 : ℝ) / 6) (4 : ℝ)
      _ = (Real.rpow (T.1 : ℝ) ((1 : ℝ) / 6)) ^ (4 : ℕ) := by
        exact Real.rpow_natCast _ 4
  exact ⟨hrone, hrpow, hmLower, hmUpper, hrFour⟩

/-- Equations (51)--(53), with the actual impulse energy exposed at the
consumer boundary.  The newest impulse first forces the response cap.  In
that cap, the actual-to-proxy comparison is fed to equation (51), including
all floor and influence-window side conditions, and equation (53) then gives
the exhaustive high-cost-or-square-root-band alternative. -/
private theorem actual_quadratic_high_or_band_of_equation51
    (N : NetworkSetup n) (A M sigma Csig sResp Cvar : ℝ)
    (hA : 0 < A) (hM : 0 < M) (hsigma : 0 < sigma)
    (hCsig : 0 ≤ Csig) (hsResp : 0 < sResp) (hCvar : 0 ≤ Cvar)
    (hRespEight : sResp ≤ 1 / (8 * (n : ℝ)))
    (hRespThreshold : sResp ≤ 1 / (4 * (n : ℝ) *
      ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
    (hRespAbsorb : sResp ≤ gainFloor N ^ 2 /
      (256 * (n : ℝ) ^ 2 * (Cvar + 1))) :
    ∃ Tscreen : ℕ, ∀ T : PositiveHorizon, Tscreen ≤ T.1 →
      ∀ s D V Q : ℝ, 0 < s → 0 ≤ D → 0 ≤ V →
        (T.1 : ℝ) * Q = 2 * A * D + sigma ^ 2 * V →
        V = ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          ((n : ℝ)⁻¹ * ∑ q,
            (actualQuadraticScalarTrajectory N s 0
              (fun r q => if r = j then if q = i then 1 else 0 else 0)
              t).1 q) ^ 2 →
        (s ≤ sResp → D ≥ (1 / 2 : ℝ) * min (T.1 : ℝ)
          ((4 * (n : ℝ) * s)⁻¹) - Csig) →
        (s ≤ sResp →
          |V - s ^ 2 * ∑ t ∈ Finset.range T.1,
            ∑ j ∈ Finset.range t, ∑ i,
              (influenceRow N j i *
                (∏ r ∈ Finset.Ico (j + 1) t,
                  (1 - s * gain N r))) ^ 2| ≤
            Cvar * s ^ 2 * (T.1 : ℝ)) →
        M / Real.sqrt T.1 < Q ∨
          A / (8 * (n : ℝ) * M) ≤
              s * Real.sqrt (T.1 : ℝ) ∧
          s * Real.sqrt (T.1 : ℝ) ≤
            256 * (n : ℝ) ^ 2 * M /
              (sigma ^ 2 * gainFloor N ^ 2) := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  obtain ⟨Tscreen, hscreen⟩ :=
    actual_quadratic_equation53_low_cost_localization
      n A M sigma (gainFloor N) Csig sResp N.hn hA hM hsigma hg
        hCsig hsResp
  refine ⟨Tscreen, ?_⟩
  intro T hT s D V Q hs hD hV hcost hVactual hSignal hCompare
  have hNewest :
      (((T.1 - 1 : ℕ) : ℝ) * s ^ 2) / (n : ℝ) ≤ V := by
    rw [hVactual]
    exact actual_quadratic_newest_noise_variance_lower N s T
  by_cases hhigh : M / Real.sqrt T.1 < Q
  · exact Or.inl hhigh
  · right
    have hlow : Q ≤ M / Real.sqrt T.1 := le_of_not_gt hhigh
    have hlocalized := hscreen T.1 hT T.2 s D V Q hs hD hV hcost hNewest
      hSignal (by
        intro hsCap h2m
        let m : ℕ := Nat.floor ((4 * (n : ℝ) * s)⁻¹)
        let x : ℝ := (4 * (n : ℝ) * s)⁻¹
        have hx : 0 < x := by dsimp [x]; positivity
        have hmle : (m : ℝ) ≤ x := by
          dsimp [m, x]
          exact Nat.floor_le hx.le
        have hsEight : s ≤ 1 / (8 * (n : ℝ)) :=
          hsCap.trans hRespEight
        have hsnEight : s * (n : ℝ) ≤ 1 / 8 := by
          have h := (le_div_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mp
            hsEight
          nlinarith
        have hmBudget : (m : ℝ) * (s * (n : ℝ)) ≤ 1 / 4 := by
          have hmul := mul_le_mul_of_nonneg_right hmle
            (by positivity : 0 ≤ s * (n : ℝ))
          have hxmul : x * (s * (n : ℝ)) = 1 / 4 := by
            dsimp [x]
            field_simp [hs.ne', hn.ne']
          rwa [hxmul] at hmul
        have hsThreshold : s ≤ 1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)) :=
          hsCap.trans hRespThreshold
        have hthresholdReal :
            (influenceEnergyWindowThreshold N : ℝ) ≤ x := by
          have hthresholdPos :
              0 < ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ) := by
            positivity
          have hcap := (le_div_iff₀
            (mul_pos (by positivity : 0 < 4 * (n : ℝ))
              hthresholdPos)).mp hsThreshold
          dsimp [x]
          rw [inv_eq_one_div,
            le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ) * s)]
          calc
            (influenceEnergyWindowThreshold N : ℝ) *
                (4 * (n : ℝ) * s) ≤
              ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ) *
                (4 * (n : ℝ) * s) := by
              apply mul_le_mul_of_nonneg_right
              · norm_num
              · positivity
            _ = s * (4 * (n : ℝ) *
                ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)) := by
              ring
            _ ≤ 1 := hcap
        have hmThreshold : influenceEnergyWindowThreshold N ≤ m := by
          dsimp [m]
          exact Nat.le_floor hthresholdReal
        have hxTwo : 2 ≤ x := by
          dsimp [x]
          rw [inv_eq_one_div,
            le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ) * s)]
          nlinarith
        have hxlt : x < (m : ℝ) + 1 := by
          dsimp [m, x]
          simpa using Nat.lt_floor_add_one ((4 * (n : ℝ) * s)⁻¹)
        have hmLower : (8 * (n : ℝ) * s)⁻¹ ≤ (m : ℝ) := by
          have hinv : (8 * (n : ℝ) * s)⁻¹ = x / 2 := by
            dsimp [x]
            field_simp [hs.ne', hn.ne']
            ring
          rw [hinv]
          nlinarith
        have hsAbsorb : s ≤ gainFloor N ^ 2 /
            (256 * (n : ℝ) ^ 2 * (Cvar + 1)) :=
          hsCap.trans hRespAbsorb
        have hCvarAbsorb :
            Cvar * s ≤ gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2) := by
          have hsAbsorb' : s ≤
              (gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2)) /
                (Cvar + 1) := by
            calc
              s ≤ gainFloor N ^ 2 /
                  (256 * (n : ℝ) ^ 2 * (Cvar + 1)) := hsAbsorb
              _ = (gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2)) /
                  (Cvar + 1) := (div_div _ _ _).symm
          have hcap := (le_div_iff₀ (by positivity : 0 < Cvar + 1)).mp
            hsAbsorb'
          calc
            Cvar * s ≤ (Cvar + 1) * s := by nlinarith
            _ = s * (Cvar + 1) := by ring
            _ ≤ gainFloor N ^ 2 / (256 * (n : ℝ) ^ 2) := by
              simpa [div_eq_mul_inv, mul_assoc] using hcap
        apply actual_quadratic_equation51_variance_floor
          N s T.1 m V Cvar hs hmThreshold hmLower hmBudget
        · simpa [m] using h2m
        · exact hCvarAbsorb
        · exact hCompare hsCap)
      hlow
    have hsqrt : 0 < Real.sqrt (T.1 : ℝ) :=
      Real.sqrt_pos.2 (Nat.cast_pos.mpr T.2)
    constructor
    · have := hlocalized.1
      rw [div_le_iff₀ hsqrt] at this
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    · have := hlocalized.2
      rw [le_div_iff₀ hsqrt] at this
      simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- The canonical iid quadratic realizes the screening data above.  Thus every
positive stepsize is either already expensive on this legal fixed-class
instance or lies in the exact equation-(53) square-root band. -/
private theorem periodic_quadratic_band_or_high_cost
    (N : NetworkSetup n) (L Δ σ H M : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hH : 0 ≤ H) (hM : 0 < M) :
    ∃ Tscreen : ℕ, ∀ T : PositiveHorizon, Tscreen ≤ T.1 →
      ∀ alpha : ℝ, 0 < alpha →
        ∃ I ∈ fixedInstanceClass N L Δ σ H,
          M / Real.sqrt T.1 < FiniteInstance.cost I alpha T ∨
            ADelta L Δ / (8 * (n : ℝ) * M) ≤
                dimensionlessStepsize L alpha * Real.sqrt (T.1 : ℝ) ∧
            dimensionlessStepsize L alpha * Real.sqrt (T.1 : ℝ) ≤
              256 * (n : ℝ) ^ 2 * M /
                (σ ^ 2 * gainFloor N ^ 2) := by
  classical
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hA : 0 < ADelta L Δ := by unfold ADelta; positivity
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hgf_le_n : gainFloor N ≤ (n : ℝ) :=
    (gainFloor_le_gain N 0).trans (gain_le_n N 0)
  rcases actual_quadratic_equation48_deterministic_signal N with
    ⟨Ca, sSignal, hCa, hsSignal, hSignal⟩
  rcases actual_quadratic_equation48_impulse_response N with
    ⟨Cr, sPulse, hCr, hsPulse, hPulse⟩
  let Csig : ℝ := (8 * Ca + 4 * Ca ^ 2) / gainFloor N
  have hCsig : 0 ≤ Csig := by dsimp [Csig]; positivity
  have hB : 0 ≤ influenceRowBound N := by
    have hnorm : 0 ≤ nodeL2Norm (influenceRow N 0) := by
      unfold nodeL2Norm
      exact Real.sqrt_nonneg _
    exact hnorm.trans (influenceRow_nodeL2_le N 0)
  have hrf0 : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrf1 : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  let Kvar : ℝ :=
    8 * influenceRowBound N * Cr / gainFloor N +
      2 * influenceRowBound N * Cr / (1 - loadingTransverseRate N) +
      8 * Cr ^ 2 / gainFloor N +
      2 * Cr ^ 2 / (1 - loadingTransverseRate N ^ 2)
  have hKvar : 0 ≤ Kvar := by
    have hden1 : 0 ≤ 1 - loadingTransverseRate N := sub_nonneg.mpr hrf1.le
    have hden2 : 0 ≤ 1 - loadingTransverseRate N ^ 2 := by
      nlinarith [mul_nonneg hrf0 (sub_nonneg.mpr hrf1.le)]
    dsimp [Kvar]
    positivity
  let Cvar : ℝ := (n : ℝ) * Kvar
  have hCvar : 0 ≤ Cvar := by dsimp [Cvar]; positivity
  let sVariance : ℝ :=
    min sPulse (min 1
      (min (1 / (8 * (n : ℝ)))
        (min (1 / (4 * (n : ℝ) *
          ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
          (gainFloor N ^ 2 /
            (256 * (n : ℝ) ^ 2 * (Cvar + 1))))))
  have hsVariance : 0 < sVariance := by
    have hthreshold :
        0 < ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ) := by
      positivity
    dsimp [sVariance]
    positivity
  let sResp : ℝ :=
    min sSignal (min sVariance (min 1 (1 / (4 * (n : ℝ)))))
  have hsResp : 0 < sResp := by dsimp [sResp]; positivity
  have hRespEight : sResp ≤ 1 / (8 * (n : ℝ)) := by
    calc
      sResp ≤ sVariance :=
        (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ min 1 (min (1 / (8 * (n : ℝ)))
          (min (1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
            (gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1))))) := min_le_right _ _
      _ ≤ min (1 / (8 * (n : ℝ)))
          (min (1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
            (gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1)))) := min_le_right _ _
      _ ≤ 1 / (8 * (n : ℝ)) := min_le_left _ _
  have hRespThreshold : sResp ≤ 1 / (4 * (n : ℝ) *
      ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)) := by
    calc
      sResp ≤ sVariance :=
        (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ min 1 (min (1 / (8 * (n : ℝ)))
          (min (1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
            (gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1))))) := min_le_right _ _
      _ ≤ min (1 / (8 * (n : ℝ)))
          (min (1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
            (gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1)))) := min_le_right _ _
      _ ≤ min (1 / (4 * (n : ℝ) *
          ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
          (gainFloor N ^ 2 /
            (256 * (n : ℝ) ^ 2 * (Cvar + 1))) := min_le_right _ _
      _ ≤ 1 / (4 * (n : ℝ) *
          ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)) := min_le_left _ _
  have hRespAbsorb : sResp ≤ gainFloor N ^ 2 /
      (256 * (n : ℝ) ^ 2 * (Cvar + 1)) := by
    calc
      sResp ≤ sVariance :=
        (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ min 1 (min (1 / (8 * (n : ℝ)))
          (min (1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
            (gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1))))) := min_le_right _ _
      _ ≤ min (1 / (8 * (n : ℝ)))
          (min (1 / (4 * (n : ℝ) *
            ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
            (gainFloor N ^ 2 /
              (256 * (n : ℝ) ^ 2 * (Cvar + 1)))) := min_le_right _ _
      _ ≤ min (1 / (4 * (n : ℝ) *
          ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
          (gainFloor N ^ 2 /
            (256 * (n : ℝ) ^ 2 * (Cvar + 1))) := min_le_right _ _
      _ ≤ gainFloor N ^ 2 /
          (256 * (n : ℝ) ^ 2 * (Cvar + 1)) := min_le_right _ _
  obtain ⟨Tscreen, hscreen⟩ := actual_quadratic_high_or_band_of_equation51
    N (ADelta L Δ) M σ Csig sResp Cvar hA hM hσ hCsig hsResp hCvar
      hRespEight hRespThreshold hRespAbsorb
  refine ⟨Tscreen, ?_⟩
  intro T hT alpha halpha
  rcases actual_quadratic_iid_instance_spec N L Δ σ H hL hΔ hσ hH with
    ⟨atom, nu, phi, S, hfinite, hnu, hatomInt, hcenter, hsecond,
      _heven, hphi, hprob, hnoise, hx0, hI, _hheterogeneity, hgrad,
      _hrow, _hcol, hrec⟩
  let I : FiniteInstance n :=
    { d := 1
      Ω := SOptLib.miniBatchSamplePath n (Fin 3)
      setup := S
      finite_layer := hfinite }
  let s : ℝ := dimensionlessStepsize L alpha
  let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
  let pulse := fun (j : ℕ) (i : Fin n) =>
    actualQuadraticScalarTrajectory N s 0
      (fun r q => if r = j then if q = i then 1 else 0 else 0)
  let D : ℝ := ∑ t ∈ Finset.range T.1,
    ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2
  let V : ℝ := ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
    ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2
  have hs : 0 < s := by dsimp [s, dimensionlessStepsize]; positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun t _ => sq_nonneg _
  have hV : 0 ≤ V := by
    dsimp [V]
    exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ => sq_nonneg _
  have h49 := actual_quadratic_equation49_iid_cost_identity
    N L Δ σ atom nu phi S hfinite hL hΔ hnu hatomInt hcenter hsecond
    hphi hprob hnoise hx0 hgrad alpha (hrec alpha) T
  dsimp only at h49
  have hscreenUse := hscreen T hT s D V (FiniteInstance.cost I alpha T)
    hs hD hV (by simpa [D, V, signal, pulse, s] using h49)
    (by simp [V, pulse])
    (by
      intro hsCap
      have hsSignalCap : s ≤ sSignal :=
        hsCap.trans (min_le_left _ _)
      have hsTail : s ≤ min sVariance (min 1 (1 / (4 * (n : ℝ)))) :=
        hsCap.trans (min_le_right _ _)
      have hsOne : s ≤ 1 :=
        (hsTail.trans (min_le_right _ _)).trans (min_le_left _ _)
      have hsQuarter : s ≤ 1 / (4 * (n : ℝ)) :=
        (hsTail.trans (min_le_right _ _)).trans (min_le_right _ _)
      have hsn : s * (n : ℝ) ≤ 1 / 4 := by
        have h := (le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ))).mp
          hsQuarter
        nlinarith
      have hsignal48 (m : ℕ) :
          |(n : ℝ)⁻¹ * ∑ q, (signal m).1 q -
              (∏ r ∈ Finset.Ico 0 m, (1 - s * gain N r))| ≤
            Ca * s * (1 - gainFloor N * s / 4) ^ m := by
        apply hSignal s hs hsSignalCap
          (fun t => (signal t).1) (fun t => (signal t).2) m
        · rfl
        · rfl
        · intro t
          exact actualQuadraticScalarTrajectory_tracker_sum_eq_zero
            N s 1 (fun _ _ => 0) t
        · intro t
          dsimp [signal]
          rw [actualQuadraticScalarTrajectory]
          funext q
          simp [Matrix.mulVec]
        · intro t
          dsimp [signal]
          rw [actualQuadraticScalarTrajectory]
          funext q
          simp [Matrix.mulVec]
      have hD50 :
          |D - ∑ t ∈ Finset.range T.1,
            (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2| ≤ Csig := by
        apply actual_quadratic_signal_energy_comparison
          (gainFloor N) Ca s T.1
          (fun t => (n : ℝ)⁻¹ * ∑ q, (signal t).1 q)
          (fun t => ∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r))
          hg hCa hs hsOne
        · have hscaled := mul_le_mul_of_nonneg_right hgf_le_n hs.le
          nlinarith
        · intro t ht
          simpa using
            (actual_quadratic_gain_product_abs_le_slow_rate N s 0 t hs hsn)
        · intro t ht
          exact hsignal48 t
      let x : ℝ := (4 * (n : ℝ) * s)⁻¹
      let m : ℕ := Nat.floor x
      let k : ℕ := min T.1 (m + 1)
      have hx : 0 < x := by dsimp [x]; positivity
      have hmle : (m : ℝ) ≤ x := by
        dsimp [m]
        exact Nat.floor_le hx.le
      have hxlt : x < (m : ℝ) + 1 := by
        dsimp [m]
        simpa using Nat.lt_floor_add_one x
      have hkT : k ≤ T.1 := by dsimp [k]; exact min_le_left _ _
      have hkpred : k - 1 ≤ m := by dsimp [k]; omega
      have hkbudget : ((k - 1 : ℕ) : ℝ) * (s * (n : ℝ)) ≤ 1 / 4 := by
        have hkcast : ((k - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hkpred
        have hknx : ((k - 1 : ℕ) : ℝ) ≤ x := hkcast.trans hmle
        have hmul := mul_le_mul_of_nonneg_right hknx
          (by positivity : 0 ≤ s * (n : ℝ))
        have hxmul : x * (s * (n : ℝ)) = 1 / 4 := by
          dsimp [x]
          field_simp [hs.ne', hn.ne']
        rwa [hxmul] at hmul
      have hterm (t : ℕ) (ht : t ∈ Finset.range k) :
          (1 / 2 : ℝ) ≤
            (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 := by
        have htkNat : t ≤ k - 1 :=
          Nat.le_sub_one_of_lt (Finset.mem_range.mp ht)
        have htk : (t : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast htkNat
        have htb : (t : ℝ) * (s * (n : ℝ)) ≤ 1 / 4 :=
          (mul_le_mul_of_nonneg_right htk (by positivity)).trans hkbudget
        have hlin := actual_quadratic_gain_product_ge_linear N s 0 t hs
          (htb.trans (by norm_num))
        simp only [zero_add] at hlin
        have hthree : (3 / 4 : ℝ) ≤
            ∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r) := by
          nlinarith
        nlinarith [sq_nonneg
          ((∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) - 3 / 4)]
      have hproxy : (k : ℝ) / 2 ≤
          ∑ t ∈ Finset.range T.1,
            (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 := by
        calc
          (k : ℝ) / 2 = ∑ _t ∈ Finset.range k, (1 / 2 : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
          _ ≤ ∑ t ∈ Finset.range k,
              (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 :=
            Finset.sum_le_sum hterm
          _ ≤ ∑ t ∈ Finset.range T.1,
              (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkT)
            intro t htT htk
            exact sq_nonneg _
      have hkreal : min (T.1 : ℝ) x ≤ (k : ℝ) := by
        by_cases hcase : T.1 ≤ m + 1
        · have hk : k = T.1 := by dsimp [k]; exact Nat.min_eq_left hcase
          rw [hk]
          exact min_le_left _ _
        · have hmT : m + 1 ≤ T.1 := Nat.le_of_not_ge hcase
          have hk : k = m + 1 := by dsimp [k]; exact Nat.min_eq_right hmT
          rw [hk]
          have hxcast : x ≤ ((m + 1 : ℕ) : ℝ) := by
            norm_num
            exact hxlt.le
          exact (min_le_right (T.1 : ℝ) x).trans hxcast
      have hlow := (abs_le.mp hD50).1
      dsimp [x, Csig]
      dsimp [D] at hlow
      nlinarith)
    (by
      intro hsCap
      have hsVarianceCap : s ≤ sVariance :=
        (hsCap.trans (min_le_right _ _)).trans (min_le_left _ _)
      have hsPulseCap : s ≤ sPulse :=
        hsVarianceCap.trans (min_le_left _ _)
      have hsRest : s ≤ min 1
          (min (1 / (8 * (n : ℝ)))
            (min (1 / (4 * (n : ℝ) *
              ((influenceEnergyWindowThreshold N + 1 : ℕ) : ℝ)))
              (gainFloor N ^ 2 /
                (256 * (n : ℝ) ^ 2 * (Cvar + 1))))) :=
        hsVarianceCap.trans (min_le_right _ _)
      have hsOne : s ≤ 1 := hsRest.trans (min_le_left _ _)
      have hsEight : s ≤ 1 / (8 * (n : ℝ)) :=
        (hsRest.trans (min_le_right _ _)).trans (min_le_left _ _)
      have hsn : s * (n : ℝ) ≤ 1 / 4 := by
        have h := (le_div_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mp
          hsEight
        nlinarith
      have hpulse48 (j : ℕ) (i : Fin n) (m : ℕ) :
          |(n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q +
              s * influenceRow N j i *
                (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
                  (1 - s * gain N r))| ≤
            Cr * (s ^ 2 * (1 - gainFloor N * s / 4) ^ m +
              s * loadingTransverseRate N ^ m) := by
        apply hPulse s hs hsPulseCap j i
          (fun t => (pulse j i t).1) (fun t => (pulse j i t).2)
        · intro t
          exact actualQuadraticScalarTrajectory_tracker_sum_eq_zero
            N s 0 (fun r q => if r = j then if q = i then 1 else 0 else 0) t
        · exact congrArg Prod.fst
            (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
        · exact congrArg Prod.snd
            (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
        · intro t
          rfl
        · intro t
          rfl
      have hgfs : gainFloor N * s ≤ 1 := by
        have hscaled := mul_le_mul_of_nonneg_right hgf_le_n hs.le
        linarith
      have hper (j : ℕ) (hj : j ∈ Finset.range T.1) (i : Fin n) :
          |∑ m ∈ Finset.range (T.1 - 1 - j),
              ((n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q) ^ 2 -
            ∑ m ∈ Finset.range (T.1 - 1 - j),
              (-s * influenceRow N j i *
                (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
                  (1 - s * gain N r))) ^ 2| ≤ Kvar * s ^ 2 := by
        have hrow : |influenceRow N j i| ≤ influenceRowBound N :=
          (abs_le_nodeL2Norm (influenceRow N j) i).trans
            (influenceRow_nodeL2_le N j)
        apply two_rate_impulse_square_energy_error_le
          (gainFloor N) (influenceRowBound N) Cr s
          (loadingTransverseRate N) (T.1 - 1 - j)
          (fun m => (n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q)
          (fun m => ∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
            (1 - s * gain N r))
          (influenceRow N j i) hg hB hCr hs hsOne hgfs hrf0 hrf1 hrow
        · intro m hm
          simpa using
            (actual_quadratic_gain_product_abs_le_slow_rate
              N s (j + 1) m hs hsn)
        · intro m hm
          simpa [sub_neg_eq_add] using hpulse48 j i m
      let AA : ℕ → Fin n → ℕ → ℝ := fun j i m =>
        ((n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q) ^ 2
      let BB : ℕ → Fin n → ℕ → ℝ := fun j i m =>
        (-s * influenceRow N j i *
          (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
            (1 - s * gain N r))) ^ 2
      have htri := triangular_square_energy_difference_le
        T.1 AA BB (Kvar * s ^ 2) (mul_nonneg hKvar (sq_nonneg s))
        (fun j hj i => by simpa [AA, BB] using hper j hj i)
      have hAtri :
          (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
            AA j i (t - 1 - j)) = V := by
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro j hj
        have hjt : j < t := Finset.mem_range.mp hj
        have heq : j + 1 + (t - 1 - j) = t := by omega
        simp only [AA, heq, V]
      have hBtri :
          (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
            BB j i (t - 1 - j)) =
          ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
            (-s * influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        apply Finset.sum_congr rfl
        intro j hj
        have hjt : j < t := Finset.mem_range.mp hj
        have heq : j + 1 + (t - 1 - j) = t := by omega
        simp only [BB, heq]
      rw [hAtri, hBtri] at htri
      have hfactor :
          (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
            (-s * influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2) =
          s ^ 2 * ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
            (influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hfactor] at htri
      dsimp [Cvar, Kvar] at htri ⊢
      simp only [Fintype.card_fin] at htri
      convert htri using 1 <;> ring)
  refine ⟨I, ?_, ?_⟩
  · simpa [I] using hI
  · simpa [s] using hscreenUse

/-- Source step 21 on the localized band: the canonical iid quadratic witness
inherits the periodic signal and variance proxy expansions through the exact
cost identity (49) and both comparison estimates in (50). -/
private theorem periodic_actual_quadratic_band_expansion
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ H : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hH : 0 ≤ H)
    (Cenergy : ℝ) (hCenergy : 0 ≤ Cenergy)
    (hintervalEnergy : ∀ a b : ℕ, a ≤ b →
      |(∑ t ∈ Finset.Ico a b, influenceEnergy N t) -
          ((b - a : ℕ) : ℝ) * periodicInfluenceMean N p| ≤ Cenergy)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ T₀ : ℕ, ∀ T : PositiveHorizon, T₀ ≤ T.1 →
      ∀ alpha : ℝ, 0 < alpha →
        c ≤ dimensionlessStepsize L alpha * Real.sqrt (T.1 : ℝ) →
        dimensionlessStepsize L alpha * Real.sqrt (T.1 : ℝ) ≤ C →
        ∃ I ∈ fixedInstanceClass N L Δ σ H,
          |FiniteInstance.cost I alpha T -
              (ADelta L Δ /
                  (dimensionlessStepsize L alpha * periodicGainMean N p hp * T.1) +
                σ ^ 2 * periodicInfluenceMean N p * dimensionlessStepsize L alpha /
                  (2 * periodicGainMean N p hp))| ≤ K / T.1 := by
  classical
  obtain ⟨KD, hKD, TD, hSignalExpansion⟩ :=
    periodic_signal_product_energy_band_expansion N p hp c C hc hC
  obtain ⟨KV, hKV, TV, hVarianceExpansion⟩ :=
    periodic_variance_product_energy_band_expansion N p hp
      Cenergy hCenergy hintervalEnergy c C hc hC
  rcases actual_quadratic_equation48_deterministic_signal N with
    ⟨Ca, sSignal, hCa, hsSignal, hSignal⟩
  rcases actual_quadratic_equation48_impulse_response N with
    ⟨Cr, sPulse, hCr, hsPulse, hPulse⟩
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hgf : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hgf_le_n : gainFloor N ≤ (n : ℝ) :=
    (gainFloor_le_gain N 0).trans (gain_le_n N 0)
  have hB : 0 ≤ influenceRowBound N := by
    have hnorm : 0 ≤ nodeL2Norm (influenceRow N 0) := by
      unfold nodeL2Norm
      exact Real.sqrt_nonneg _
    exact hnorm.trans (influenceRow_nodeL2_le N 0)
  have hrf0 : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hrf1 : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  let Kvar : ℝ :=
    8 * influenceRowBound N * Cr / gainFloor N +
      2 * influenceRowBound N * Cr / (1 - loadingTransverseRate N) +
      8 * Cr ^ 2 / gainFloor N +
      2 * Cr ^ 2 / (1 - loadingTransverseRate N ^ 2)
  have hKvar : 0 ≤ Kvar := by
    have hden1 : 0 ≤ 1 - loadingTransverseRate N := sub_nonneg.mpr hrf1.le
    have hden2 : 0 ≤ 1 - loadingTransverseRate N ^ 2 := by
      nlinarith [mul_nonneg hrf0 (sub_nonneg.mpr hrf1.le)]
    dsimp [Kvar]
    positivity
  let CD : ℝ := (8 * Ca + 4 * Ca ^ 2) / gainFloor N
  let CV : ℝ := (n : ℝ) * Kvar
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have hCV : 0 ≤ CV := by dsimp [CV]; positivity
  let sResp : ℝ := min sSignal (min sPulse (min 1 (1 / (4 * (n : ℝ)))))
  have hsResp : 0 < sResp := by dsimp [sResp]; positivity
  obtain ⟨Tcap, hTcap⟩ := exists_nat_gt ((C / sResp) ^ 2)
  let T₀ : ℕ := max TD (max TV Tcap)
  let K : ℝ :=
    2 * ADelta L Δ * (CD + KD) + σ ^ 2 * (CV + KV) * (1 + C ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    unfold ADelta
    positivity
  refine ⟨K, hK, T₀, ?_⟩
  intro T hT alpha halpha hslow hshigh
  have hTD : TD ≤ T.1 := (le_max_left _ _).trans hT
  have hTV : TV ≤ T.1 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTcapUse : Tcap ≤ T.1 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  let s : ℝ := dimensionlessStepsize L alpha
  have hs : 0 < s := by dsimp [s, dimensionlessStepsize]; positivity
  have hTR : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
  have hsqrt : 0 < Real.sqrt (T.1 : ℝ) := Real.sqrt_pos.2 hTR
  have hsqrtSq : Real.sqrt (T.1 : ℝ) ^ 2 = (T.1 : ℝ) :=
    Real.sq_sqrt hTR.le
  have hTlarge : (C / sResp) ^ 2 < (T.1 : ℝ) :=
    hTcap.trans_le (by exact_mod_cast hTcapUse)
  have hratio0 : 0 < C / sResp := div_pos hC hsResp
  have hratio : C / sResp < Real.sqrt (T.1 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (T.1 : ℝ) - C / sResp)]
  have hCroot : C / Real.sqrt (T.1 : ℝ) ≤ sResp := by
    have hmul : C < sResp * Real.sqrt (T.1 : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hsResp).mp hratio
    exact (div_le_iff₀ hsqrt).2 hmul.le
  have hsRespUse : s ≤ sResp := by
    have hsC : s ≤ C / Real.sqrt (T.1 : ℝ) :=
      (le_div_iff₀ hsqrt).2 (by simpa [s] using hshigh)
    exact hsC.trans hCroot
  have hsSignalUse : s ≤ sSignal := hsRespUse.trans (by
    dsimp [sResp]
    exact min_le_left _ _)
  have hsPulseUse : s ≤ sPulse := hsRespUse.trans (by
    dsimp [sResp]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hsOne : s ≤ 1 := hsRespUse.trans (by
    dsimp [sResp]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))
  have hsQuarter : s * (n : ℝ) ≤ 1 / 4 := by
    have hcap : s ≤ 1 / (4 * (n : ℝ)) := hsRespUse.trans (by
      dsimp [sResp]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))
    have hmul := mul_le_mul_of_nonneg_right hcap hn.le
    field_simp [ne_of_gt hn] at hmul ⊢
    nlinarith
  rcases actual_quadratic_iid_instance_spec N L Δ σ H hL hΔ hσ hH with
    ⟨atom, nu, phi, S, hfinite, hnu, hatomInt, hcenter, hsecond,
      _heven, hphi, hprob, hnoise, hx0, hI, _hheterogeneity, hgrad,
      _hrow, _hcol, hrec⟩
  let I : FiniteInstance n :=
    { d := 1
      Ω := SOptLib.miniBatchSamplePath n (Fin 3)
      setup := S
      finite_layer := hfinite }
  have h49 := actual_quadratic_equation49_iid_cost_identity
    N L Δ σ atom nu phi S hfinite hL hΔ hnu hatomInt hcenter hsecond
    hphi hprob hnoise hx0 hgrad alpha (hrec alpha) T
  dsimp only at h49
  let signal := actualQuadraticScalarTrajectory N s 1 (fun _ _ => 0)
  let pulse := fun (j : ℕ) (i : Fin n) =>
    actualQuadraticScalarTrajectory N s 0
      (fun r q => if r = j then if q = i then 1 else 0 else 0)
  let Dproxy : ℝ := ∑ t ∈ Finset.range T.1,
    (∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r)) ^ 2
  let Vproxy : ℝ := s ^ 2 * ∑ t ∈ Finset.range T.1,
    ∑ j ∈ Finset.range t, influenceEnergy N j *
      (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r)) ^ 2
  let Dact : ℝ := ∑ t ∈ Finset.range T.1,
    ((n : ℝ)⁻¹ * ∑ q, (signal t).1 q) ^ 2
  let Vact : ℝ := ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
    ((n : ℝ)⁻¹ * ∑ q, (pulse j i t).1 q) ^ 2
  have hsignal48 (m : ℕ) :
      |(n : ℝ)⁻¹ * ∑ q, (signal m).1 q -
          (∏ r ∈ Finset.Ico 0 m, (1 - s * gain N r))| ≤
        Ca * s * (1 - gainFloor N * s / 4) ^ m := by
    apply hSignal s hs hsSignalUse
      (fun t => (signal t).1) (fun t => (signal t).2) m
    · rfl
    · rfl
    · intro t
      exact actualQuadraticScalarTrajectory_tracker_sum_eq_zero
        N s 1 (fun _ _ => 0) t
    · intro t
      dsimp [signal]
      rw [actualQuadraticScalarTrajectory]
      funext q
      simp [Matrix.mulVec]
    · intro t
      dsimp [signal]
      rw [actualQuadraticScalarTrajectory]
      funext q
      simp [Matrix.mulVec]
  have hpulse48 (j : ℕ) (i : Fin n) (m : ℕ) :
      |(n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q +
          s * influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
              (1 - s * gain N r))| ≤
        Cr * (s ^ 2 * (1 - gainFloor N * s / 4) ^ m +
          s * loadingTransverseRate N ^ m) := by
    apply hPulse s hs hsPulseUse j i
      (fun t => (pulse j i t).1) (fun t => (pulse j i t).2)
    · intro t
      exact actualQuadraticScalarTrajectory_tracker_sum_eq_zero
        N s 0 (fun r q => if r = j then if q = i then 1 else 0 else 0) t
    · exact congrArg Prod.fst
        (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
    · exact congrArg Prod.snd
        (actualQuadraticScalarTrajectory_zero_before_pulse N s j i j le_rfl)
    · intro t
      rfl
    · intro t
      rfl
  have hgfs : gainFloor N * s ≤ 1 := by
    have hscaled := mul_le_mul_of_nonneg_right hgf_le_n hs.le
    linarith
  have hD50 : |Dact - Dproxy| ≤ CD := by
    apply actual_quadratic_signal_energy_comparison
      (gainFloor N) Ca s T.1
      (fun t => (n : ℝ)⁻¹ * ∑ q, (signal t).1 q)
      (fun t => ∏ r ∈ Finset.Ico 0 t, (1 - s * gain N r))
      hgf hCa hs hsOne hgfs
    · intro t ht
      simpa using
        (actual_quadratic_gain_product_abs_le_slow_rate N s 0 t hs hsQuarter)
    · intro t ht
      exact hsignal48 t
  have hV50raw :
      |Vact - s ^ 2 * ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2| ≤
        CV * s ^ 2 * (T.1 : ℝ) := by
    have hper (j : ℕ) (hj : j ∈ Finset.range T.1) (i : Fin n) :
        |∑ m ∈ Finset.range (T.1 - 1 - j),
            ((n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q) ^ 2 -
          ∑ m ∈ Finset.range (T.1 - 1 - j),
            (-s * influenceRow N j i *
              (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
                (1 - s * gain N r))) ^ 2| ≤ Kvar * s ^ 2 := by
      have hrow : |influenceRow N j i| ≤ influenceRowBound N :=
        (abs_le_nodeL2Norm (influenceRow N j) i).trans
          (influenceRow_nodeL2_le N j)
      apply two_rate_impulse_square_energy_error_le
        (gainFloor N) (influenceRowBound N) Cr s
        (loadingTransverseRate N) (T.1 - 1 - j)
        (fun m => (n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q)
        (fun m => ∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
          (1 - s * gain N r))
        (influenceRow N j i) hgf hB hCr hs hsOne hgfs hrf0 hrf1 hrow
      · intro m hm
        simpa using
          (actual_quadratic_gain_product_abs_le_slow_rate
            N s (j + 1) m hs hsQuarter)
      · intro m hm
        simpa [sub_neg_eq_add] using hpulse48 j i m
    let AA : ℕ → Fin n → ℕ → ℝ := fun j i m =>
      ((n : ℝ)⁻¹ * ∑ q, (pulse j i (j + 1 + m)).1 q) ^ 2
    let BB : ℕ → Fin n → ℕ → ℝ := fun j i m =>
      (-s * influenceRow N j i *
        (∏ r ∈ Finset.Ico (j + 1) (j + 1 + m),
          (1 - s * gain N r))) ^ 2
    have htri := triangular_square_energy_difference_le
      T.1 AA BB (Kvar * s ^ 2) (mul_nonneg hKvar (sq_nonneg s))
      (fun j hj i => by simpa [AA, BB] using hper j hj i)
    have hAtri :
        (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          AA j i (t - 1 - j)) = Vact := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      have heq : j + 1 + (t - 1 - j) = t := by omega
      simp only [AA, heq, Vact]
    have hBtri :
        (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          BB j i (t - 1 - j)) =
        ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (-s * influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro j hj
      have hjt : j < t := Finset.mem_range.mp hj
      have heq : j + 1 + (t - 1 - j) = t := by omega
      simp only [BB, heq]
    rw [hAtri, hBtri] at htri
    have hfactor :
        (∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (-s * influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2) =
        s ^ 2 * ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hfactor] at htri
    dsimp [CV, Kvar] at htri ⊢
    simp only [Fintype.card_fin] at htri
    convert htri using 1 <;> ring
  have hproxyEq :
      s ^ 2 * ∑ t ∈ Finset.range T.1, ∑ j ∈ Finset.range t, ∑ i,
          (influenceRow N j i *
            (∏ r ∈ Finset.Ico (j + 1) t, (1 - s * gain N r))) ^ 2 =
        Vproxy := by
    dsimp [Vproxy]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro j hj
    unfold influenceEnergy
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hV50 : |Vact - Vproxy| ≤ CV * s ^ 2 * (T.1 : ℝ) := by
    rwa [hproxyEq] at hV50raw
  have hDproxy := hSignalExpansion T hTD s hs
    (by simpa [s] using hslow) (by simpa [s] using hshigh)
  have hVproxy := hVarianceExpansion T hTV s hs
    (by simpa [s] using hslow) (by simpa [s] using hshigh)
  have hActual := actual_quadratic_band_expansion_of_proxy_comparisons
    (ADelta L Δ) σ (periodicGainMean N p hp) (periodicInfluenceMean N p)
    C KD KV CD CV (T.1 : ℝ) s Dproxy Vproxy Dact Vact
    (FiniteInstance.cost I alpha T)
    (by unfold ADelta; positivity) (periodic_phase_coefficients N p hp).1 hC.le
    hKD hKV hCD hCV hTR hs (by simpa [s] using hshigh)
    (by simpa [Dact, Vact, signal, pulse, s] using h49)
    (by simpa [Dproxy] using hDproxy)
    (by simpa [Vproxy] using hVproxy) hD50 hV50
  refine ⟨I, ?_, ?_⟩
  · simpa [I] using hI
  · simpa [K, s] using hActual

/-- The exact scalar balance used after the periodic actual-response
expansion.  It is written directly in the source coefficients, avoiding any
loss in the leading constant. -/
private theorem periodic_leading_le_reciprocal_linear
    (A sigma h q s t : ℝ)
    (hA : 0 < A) (hsigma : 0 < sigma) (hh : 0 < h) (hq : 0 < q)
    (hs : 0 < s) (ht : 0 < t) :
    sigma * Real.sqrt (2 * A * q / (h ^ 2 * t)) ≤
      A / (s * h * t) + sigma ^ 2 * q * s / (2 * h) := by
  let x : ℝ := A / (s * h * t)
  let y : ℝ := sigma ^ 2 * q * s / (2 * h)
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hrad : 0 ≤ 2 * A * q / (h ^ 2 * t) := by positivity
  have hleft : 0 ≤ sigma * Real.sqrt (2 * A * q / (h ^ 2 * t)) :=
    mul_nonneg hsigma.le (Real.sqrt_nonneg _)
  have hright : 0 ≤ x + y := add_nonneg hx.le hy.le
  have hsq :
      (sigma * Real.sqrt (2 * A * q / (h ^ 2 * t))) ^ 2 =
        4 * x * y := by
    rw [mul_pow, Real.sq_sqrt hrad]
    dsimp [x, y]
    field_simp [hs.ne', hh.ne', ht.ne']
    ring
  apply (sq_le_sq₀ hleft hright).1
  rw [hsq]
  nlinarith [sq_nonneg (x - y)]

/-- Source step 22: combine the equation-(51)/(53) exhaustive screening with
the exact periodic band expansion.  The high-cost branch is compared to the
same leading term through equation (62), while the localized branch uses the
coefficient-preserving scalar balance above. -/
private theorem periodic_exact_all_stepsizes_response_lower
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ H M KB Kact : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hH : 0 ≤ H)
    (hM : 0 < M)
    (hMdef : M =
      (ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) / gainFloor N)
    (hKB : 0 ≤ KB) (hKact : 0 ≤ Kact)
    (TB Tact : ℕ)
    (hEquation62 : ∀ T : PositiveHorizon, TB ≤ T.1 →
      |comparator N L Δ σ T -
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1))| ≤ KB / T.1)
    (hActualBand : ∀ T : PositiveHorizon, Tact ≤ T.1 →
      ∀ alpha : ℝ, 0 < alpha →
        ADelta L Δ / (8 * (n : ℝ) * M) ≤
            dimensionlessStepsize L alpha * Real.sqrt (T.1 : ℝ) →
        dimensionlessStepsize L alpha * Real.sqrt (T.1 : ℝ) ≤
          256 * (n : ℝ) ^ 2 * M / (σ ^ 2 * gainFloor N ^ 2) →
        ∃ I ∈ fixedInstanceClass N L Δ σ H,
          |FiniteInstance.cost I alpha T -
              (ADelta L Δ /
                  (dimensionlessStepsize L alpha *
                    periodicGainMean N p hp * T.1) +
                σ ^ 2 * periodicInfluenceMean N p *
                    dimensionlessStepsize L alpha /
                  (2 * periodicGainMean N p hp))| ≤ Kact / T.1) :
    ∃ Klo : ℝ, 0 ≤ Klo ∧ ∃ Tlo : ℕ,
      ∀ T : PositiveHorizon, Tlo ≤ T.1 → ∀ alpha : ℝ, 0 < alpha →
        ∃ I ∈ fixedInstanceClass N L Δ σ H,
          σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
              (periodicGainMean N p hp ^ 2 * T.1)) - Klo / T.1 ≤
            FiniteInstance.cost I alpha T := by
  obtain ⟨hh, hhq, _hsum, _hcoord⟩ := periodic_phase_coefficients N p hp
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hq : 0 < periodicInfluenceMean N p := by
    have hhSq : 0 < periodicGainMean N p hp ^ 2 := sq_pos_of_pos hh
    have hquot : 0 < periodicGainMean N p hp ^ 2 / (n : ℝ) :=
      div_pos hhSq hn
    exact hquot.trans_le hhq
  obtain ⟨Tscreen, hscreen⟩ :=
    periodic_quadratic_band_or_high_cost N L Δ σ H M
      hL hΔ hσ hH hM
  let Klo : ℝ := KB + Kact
  let Tlo : ℕ := max ((64 * n) ^ 2) (max TB (max Tact Tscreen))
  have hKlo : 0 ≤ Klo := by dsimp [Klo]; positivity
  refine ⟨Klo, hKlo, Tlo, ?_⟩
  intro T hT alpha halpha
  have hlarge : (64 * n : ℕ) ^ 2 ≤ T.1 :=
    (le_max_left _ _).trans hT
  have hTB : TB ≤ T.1 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTact : Tact ≤ T.1 :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
  have hTscreen : Tscreen ≤ T.1 :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hT))
  obtain ⟨I, hI, hhigh | hband⟩ := hscreen T hTscreen alpha halpha
  · refine ⟨I, hI, ?_⟩
    have htrial : comparator N L Δ σ T ≤ M / Real.sqrt T.1 := by
      simpa [hMdef] using actual_quadratic_comparator_trial_upper
        N L Δ σ hL hΔ T hlarge
    have hEqLow := (abs_le.mp (hEquation62 T hTB)).1
    have hTR : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
    have hfrac : KB / (T.1 : ℝ) ≤ Klo / (T.1 : ℝ) := by
      apply div_le_div_of_nonneg_right _ hTR.le
      dsimp [Klo]
      linarith
    calc
      σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) - Klo / T.1 ≤
          σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) - KB / T.1 :=
        sub_le_sub_left hfrac _
      _ ≤ comparator N L Δ σ T := by linarith
      _ ≤ M / Real.sqrt T.1 := htrial
      _ ≤ FiniteInstance.cost I alpha T := hhigh.le
  · obtain ⟨J, hJ, hcost⟩ :=
      hActualBand T hTact alpha halpha hband.1 hband.2
    refine ⟨J, hJ, ?_⟩
    let s : ℝ := dimensionlessStepsize L alpha
    have hs : 0 < s := by dsimp [s, dimensionlessStepsize]; positivity
    have hTR : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
    have hbalance := periodic_leading_le_reciprocal_linear
      (ADelta L Δ) σ (periodicGainMean N p hp)
      (periodicInfluenceMean N p) s (T.1 : ℝ)
      (by unfold ADelta; positivity) hσ hh hq hs hTR
    have hcostLow := (abs_le.mp hcost).1
    have hfrac : Kact / (T.1 : ℝ) ≤ Klo / (T.1 : ℝ) := by
      apply div_le_div_of_nonneg_right _ hTR.le
      dsimp [Klo]
      linarith
    dsimp [s] at hbalance
    calc
      σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) - Klo / T.1 ≤
          σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) - Kact / T.1 :=
        sub_le_sub_left hfrac _
      _ ≤ (ADelta L Δ /
              (dimensionlessStepsize L alpha * periodicGainMean N p hp * T.1) +
            σ ^ 2 * periodicInfluenceMean N p * dimensionlessStepsize L alpha /
              (2 * periodicGainMean N p hp)) - Kact / T.1 :=
        sub_le_sub_right hbalance _
      _ ≤ FiniteInstance.cost J alpha T := by linarith

/-- Complete-lattice transport for the source's non-exchanged hard-instance
quantifiers: each positive stepsize may use its own member of the same class. -/
private theorem minimaxRisk_lower_of_all_stepsizes
    (C : Set (FiniteInstance n)) (T : PositiveHorizon) (r : ENNReal)
    (hresponse : ∀ α : ℝ, 0 < α →
      ∃ I ∈ C, r ≤ ENNReal.ofReal (FiniteInstance.cost I α T)) :
    r ≤ minimaxRisk C T := by
  unfold minimaxRisk
  apply le_iInf
  intro α
  obtain ⟨I, hI, hcost⟩ := hresponse α.1 α.2
  exact le_iSup_of_le ⟨I, hI⟩ hcost

/-- The exported equation-(56) response theorem already supplies the correct
`∀ α > 0, ∃ Iα` order; this lemma records its exact (coarse) minimax
consequence.  The sharp periodic equation-(64) endpoint requires the separate
periodic response expansion from the source. -/
private theorem fixed_class_minimax_lower_of_actual_response_coarse
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    ∃ Tminus : ℕ, ∀ H : ℝ, 0 ≤ H →
      ∀ T : PositiveHorizon, Tminus ≤ T.1 →
        ENNReal.ofReal (comparator N L Δ σ T / 6400) ≤
          minimaxRisk (fixedInstanceClass N L Δ σ H) T := by
  obtain ⟨Tminus, hresponse⟩ :=
    actual_quadratic_response_all_stepsizes N L Δ σ hL hΔ hσ
  refine ⟨Tminus, ?_⟩
  intro H hH T hT
  apply minimaxRisk_lower_of_all_stepsizes
  intro α hα
  exact hresponse H hH T hT α hα

/-- Sharp arithmetic-output transfer used in the periodic equation-(63) route.
Unlike `stationarityError_le_corrected_energy`, this keeps coefficient one on
the corrected-gradient energy and pays the exact geometric cross term. -/
private theorem stationarityError_le_corrected_energy_sharp
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon) :
    stationarityError S alpha T ≤
      (T.1 : ℝ)⁻¹ *
        (correctedGradientEnergy S alpha T +
          2 * S.L * Real.sqrt (correctedGradientEnergy S alpha T) *
            Real.sqrt (correctedCenterOffsetEnergy S alpha T) +
          S.L ^ 2 * correctedCenterOffsetEnergy S alpha T) := by
  classical
  let x : ℕ → Ω → Point d := fun t omega =>
    gradient (averageObjective S) (arithmeticMean S omega alpha t)
  let u : ℕ → Ω → Point d := fun t omega =>
    gradient (averageObjective S) (correctedCenter S omega alpha t)
  let D : ℝ := ∑ t ∈ Finset.range T.1,
    ∫ omega, ‖x t omega - u t omega‖ ^ 2 ∂S.probability
  let G : ℝ := correctedGradientEnergy S alpha T
  let J : ℝ := correctedCenterOffsetEnergy S alpha T
  have hx : ∀ t ∈ Finset.range T.1, MemLp (x t) 2 S.probability := by
    intro t _ht
    simpa [x] using average_gradient_along_arithmeticMean_memLp_two S alpha t
  have hu : ∀ t ∈ Finset.range T.1, MemLp (u t) 2 S.probability := by
    intro t _ht
    simpa [u] using (corrected_center_descent_payload_memLp_two S alpha t).2.1
  have hpert :=
    finite_average_integral_sq_abs_sub_le_average_error_sq_add_cross
      T.1 x u hx hu
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun t _ht =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hG_nonneg : 0 ≤ G := by
    dsimp [G, correctedGradientEnergy]
    exact Finset.sum_nonneg fun t _ht =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hJ_nonneg : 0 ≤ J := by
    dsimp [J, correctedCenterOffsetEnergy]
    exact Finset.sum_nonneg fun t _ht =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hD : D ≤ S.L ^ 2 * J := by
    dsimp [D, J, correctedCenterOffsetEnergy]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have hmean := arithmeticMean_memLp_two S alpha t
    have hcenter := (corrected_center_descent_payload_memLp_two S alpha t).1
    have hdiff := (hx t ht).sub (hu t ht)
    have hoff := hcenter.sub hmean
    have hdiffInt : Integrable (fun omega => ‖x t omega - u t omega‖ ^ 2)
        S.probability :=
      (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).1 hdiff
    have hoffInt : Integrable (fun omega =>
        S.L ^ 2 * ‖correctedCenter S omega alpha t -
          arithmeticMean S omega alpha t‖ ^ 2) S.probability :=
      ((memLp_two_iff_integrable_sq_norm
        hoff.aestronglyMeasurable).1 hoff).const_mul (S.L ^ 2)
    calc
      (∫ omega, ‖x t omega - u t omega‖ ^ 2 ∂S.probability) ≤
          ∫ omega, S.L ^ 2 *
            ‖correctedCenter S omega alpha t -
              arithmeticMean S omega alpha t‖ ^ 2 ∂S.probability := by
        apply MeasureTheory.integral_mono hdiffInt hoffInt
        intro omega
        have hLip := average_gradient_norm_sub_le S
          (arithmeticMean S omega alpha t) (correctedCenter S omega alpha t)
        have hsq := (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg S.hL.le (norm_nonneg _))).2 hLip
        simpa [x, u, mul_pow, norm_sub_rev] using hsq
      _ = S.L ^ 2 *
          ∫ omega, ‖correctedCenter S omega alpha t -
            arithmeticMean S omega alpha t‖ ^ 2 ∂S.probability := by
        rw [MeasureTheory.integral_const_mul]
  have hT : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
  have hr : 0 ≤ (T.1 : ℝ)⁻¹ := (inv_nonneg.mpr hT.le)
  have hDG : D * G ≤ (S.L ^ 2 * J) * G :=
    mul_le_mul_of_nonneg_right hD hG_nonneg
  have hsqrtDG : Real.sqrt (D * G) ≤
      S.L * Real.sqrt G * Real.sqrt J := by
    calc
      Real.sqrt (D * G) ≤ Real.sqrt ((S.L ^ 2 * J) * G) :=
        Real.sqrt_le_sqrt hDG
      _ = S.L * Real.sqrt G * Real.sqrt J := by
        rw [show (S.L ^ 2 * J) * G = S.L ^ 2 * (G * J) by ring,
          Real.sqrt_mul (sq_nonneg S.L), Real.sqrt_sq_eq_abs,
          abs_of_nonneg S.hL.le, Real.sqrt_mul hG_nonneg]
        ring
  have hsqrt_scaled :
      Real.sqrt (((T.1 : ℝ)⁻¹ * D) * ((T.1 : ℝ)⁻¹ * G)) =
        (T.1 : ℝ)⁻¹ * Real.sqrt (D * G) := by
    rw [show ((T.1 : ℝ)⁻¹ * D) * ((T.1 : ℝ)⁻¹ * G) =
      ((T.1 : ℝ)⁻¹) ^ 2 * (D * G) by ring,
      Real.sqrt_mul (sq_nonneg ((T.1 : ℝ)⁻¹)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hr]
  have hmain :
      (T.1 : ℝ)⁻¹ * G +
          ((T.1 : ℝ)⁻¹ * D +
            2 * Real.sqrt (((T.1 : ℝ)⁻¹ * D) * ((T.1 : ℝ)⁻¹ * G))) ≤
        (T.1 : ℝ)⁻¹ *
          (G + 2 * S.L * Real.sqrt G * Real.sqrt J + S.L ^ 2 * J) := by
    rw [hsqrt_scaled]
    have hDr := mul_le_mul_of_nonneg_left hD hr
    have hcross : 2 * (T.1 : ℝ)⁻¹ * Real.sqrt (D * G) ≤
        2 * (T.1 : ℝ)⁻¹ *
          (S.L * Real.sqrt G * Real.sqrt J) :=
      mul_le_mul_of_nonneg_left hsqrtDG
        (mul_nonneg (by norm_num) hr)
    nlinarith
  have hraw : stationarityError S alpha T ≤
      (T.1 : ℝ)⁻¹ * G +
        ((T.1 : ℝ)⁻¹ * D +
          2 * Real.sqrt (((T.1 : ℝ)⁻¹ * D) * ((T.1 : ℝ)⁻¹ * G))) := by
    unfold stationarityError stationarityIntegrand SOptLib.expectation
    have hsub := (le_abs_self
      (((T.1 : ℝ)⁻¹ * ∑ t ∈ Finset.range T.1,
          ∫ omega, ‖x t omega‖ ^ 2 ∂S.probability) -
        ((T.1 : ℝ)⁻¹ * ∑ t ∈ Finset.range T.1,
          ∫ omega, ‖u t omega‖ ^ 2 ∂S.probability))).trans hpert
    dsimp [x, u, D, G, correctedGradientEnergy] at hsub ⊢
    unfold SOptLib.expectation at hsub ⊢
    linarith
  exact hraw.trans (by simpa [G, J] using hmain)

/-- Fixed-class sharp output interface for equation (63).  This consumes the
coefficient-one transfer above and only substitutes the already-proved uniform
bound for the corrected-center offset energy. -/
private theorem fixed_instance_cost_le_corrected_energy_sharp
    (N : NetworkSetup n) (L Δ σ H : ℝ) (hL : 0 < L)
    (I : fixedInstanceClass N L Δ σ H)
    (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n)
    (hsCap : s.1 ≤ correctedCenterStepCap N) :
    let G := @correctedGradientEnergy n I.1.d I.1.Ω
      I.1.measurableSpace I.1.setup (s.1 / L) T
    let B := controlJB N * G + controlJH N * n * H ^ 2 +
      controlJN N * σ ^ 2 * T.1
    FiniteInstance.cost I.1 (s.1 / L) T ≤
      (T.1 : ℝ)⁻¹ *
        (G + 2 * s.1 * Real.sqrt G * Real.sqrt B + s.1 ^ 2 * B) := by
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  dsimp only
  let S := I.1.setup
  let G := correctedGradientEnergy S (s.1 / L) T
  let J := correctedCenterOffsetEnergy S (s.1 / L) T
  let B := controlJB N * G + controlJH N * n * H ^ 2 +
    controlJN N * σ ^ 2 * T.1
  have hnetwork : S.network = N := by
    simpa [S, FiniteInstance.network] using I.2.1
  have hLip : S.L = L := by
    simpa [S, FiniteInstance.lipschitz] using I.2.2.1
  have hnoise : S.σ = σ := by
    simpa [S, FiniteInstance.noiseScale] using I.2.2.2.2.1
  have hheterogeneity : S.H = H := by
    simpa [S, FiniteInstance.heterogeneityScale] using I.2.2.2.2.2
  have hfinite : InFiniteHeterogeneityLayer S := by
    simpa [S] using I.1.finite_layer
  have halpha : 0 < s.1 / L := div_pos s.2.1 hL
  have hdim : dimensionlessStepsize S.L (s.1 / L) = s.1 := by
    rw [hLip]
    exact dimensionlessStepsize_div L s.1 hL
  have hcontrol := corrected_center_uniform_control S hfinite (s.1 / L)
    halpha (by rw [hdim, hnetwork]; exact hsCap) T
  rcases hcontrol with ⟨_, _, _, _, _, _, _, _, _, hJraw, _⟩
  have hJ : J ≤ (s.1 / L) ^ 2 * B := by
    rw [hnetwork, hheterogeneity, hnoise] at hJraw
    simpa [J, B, G] using hJraw
  have hJnonneg : 0 ≤ J := by
    dsimp [J, correctedCenterOffsetEnergy]
    exact Finset.sum_nonneg fun t _ht =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hBnonneg : 0 ≤ B := by
    have hsquare : 0 < (s.1 / L) ^ 2 := sq_pos_of_pos halpha
    nlinarith
  have hsqrtJ : Real.sqrt J ≤ (s.1 / L) * Real.sqrt B := by
    calc
      Real.sqrt J ≤ Real.sqrt ((s.1 / L) ^ 2 * B) := Real.sqrt_le_sqrt hJ
      _ = (s.1 / L) * Real.sqrt B := by
        rw [Real.sqrt_mul (sq_nonneg (s.1 / L)), Real.sqrt_sq_eq_abs,
          abs_of_pos halpha]
  have hGnonneg : 0 ≤ G := by
    dsimp [G, correctedGradientEnergy]
    exact Finset.sum_nonneg fun t _ht =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have htransfer := stationarityError_le_corrected_energy_sharp
    S (s.1 / L) T
  change stationarityError S (s.1 / L) T ≤ _
  calc
    stationarityError S (s.1 / L) T ≤
        (T.1 : ℝ)⁻¹ *
          (G + 2 * S.L * Real.sqrt G * Real.sqrt J + S.L ^ 2 * J) := by
      simpa [G, J] using htransfer
    _ ≤ (T.1 : ℝ)⁻¹ *
          (G + 2 * S.L * Real.sqrt G * ((s.1 / L) * Real.sqrt B) +
            S.L ^ 2 * ((s.1 / L) ^ 2 * B)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      have hcross :
          (2 * S.L * Real.sqrt G) * Real.sqrt J ≤
            (2 * S.L * Real.sqrt G) * ((s.1 / L) * Real.sqrt B) :=
        mul_le_mul_of_nonneg_left hsqrtJ
          (mul_nonneg (mul_nonneg (by norm_num) S.hL.le)
            (Real.sqrt_nonneg G))
      have hoffset : S.L ^ 2 * J ≤
          S.L ^ 2 * ((s.1 / L) ^ 2 * B) :=
        mul_le_mul_of_nonneg_left hJ (sq_nonneg S.L)
      linarith
    _ = (T.1 : ℝ)⁻¹ *
          (G + 2 * s.1 * Real.sqrt G * Real.sqrt B + s.1 ^ 2 * B) := by
      rw [hLip]
      field_simp [hL.ne']
    _ = _ := by rfl

/-- The quotient blocks of length `m`, with the Euclidean-division tail merged
into the last block, form a contiguous partition whose lengths lie in
`[m, 2m]`.  This is the finite combinatorial certificate used in the periodic
equation-(63) argument. -/
private theorem regular_tail_merged_partition_certificate
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (T m : ℕ)
    (hm : 0 < m) (hmT : m ≤ T) :
    let k := T / m
    let blockEnd : ℕ → ℕ := fun j =>
      if j + 1 = k then T else (j + 1) * m
    (∀ j ∈ Finset.range k,
        m ≤ blockEnd j - j * m ∧ blockEnd j - j * m ≤ 2 * m) ∧
      (∑ t ∈ Finset.range T, f t) =
        ∑ j ∈ Finset.range k,
          ∑ t ∈ Finset.Ico (j * m) (blockEnd j), f t := by
  classical
  dsimp only
  let k := T / m
  have hk : 0 < k := by
    dsimp [k]
    exact Nat.div_pos hmT hm
  have hdecomp : T = k * m + T % m := by
    dsimp [k]
    simpa [Nat.mul_comm] using (Nat.div_add_mod T m).symm
  have hrem : T % m < m := Nat.mod_lt T hm
  have hlength : ∀ j ∈ Finset.range k,
      m ≤ (if j + 1 = k then T else (j + 1) * m) - j * m ∧
        (if j + 1 = k then T else (j + 1) * m) - j * m ≤ 2 * m := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    by_cases hlast : j + 1 = k
    · rw [if_pos hlast]
      have hjmul : j * m + m = k * m := by
        rw [← hlast, Nat.add_mul]
        simp
      omega
    · rw [if_neg hlast, Nat.add_mul]
      simp
      omega
  refine ⟨hlength, ?_⟩
  let K := k - 1
  have hkK : k = K + 1 := by
    dsimp [K]
    omega
  have hKm : K * m ≤ T := by
    rw [hdecomp]
    have hKle : K ≤ k := by dsimp [K]; omega
    exact Nat.le_add_right_of_le (Nat.mul_le_mul_right m hKle)
  have hblock (j : ℕ) :
      (∑ t ∈ Finset.Ico (j * m) ((j + 1) * m), f t) =
        ∑ r ∈ Finset.range m, f (j * m + r) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_mul]
  have hprefix :
      (∑ t ∈ Finset.range (K * m), f t) =
        ∑ j ∈ Finset.range K,
          ∑ t ∈ Finset.Ico (j * m) ((j + 1) * m), f t := by
    rw [sum_range_mul_eq_sum_blocks]
    apply Finset.sum_congr rfl
    intro j _hj
    exact (hblock j).symm
  have hprefixIf :
      (∑ j ∈ Finset.range K,
          ∑ t ∈ Finset.Ico (j * m)
            (if j + 1 = K + 1 then T else (j + 1) * m), f t) =
        ∑ j ∈ Finset.range K,
          ∑ t ∈ Finset.Ico (j * m) ((j + 1) * m), f t := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_neg]
    exact fun h => by
      have hjK : j < K := Finset.mem_range.mp hj
      omega
  change (∑ t ∈ Finset.range T, f t) =
    ∑ j ∈ Finset.range k,
      ∑ t ∈ Finset.Ico (j * m)
        (if j + 1 = k then T else (j + 1) * m), f t
  rw [hkK, Finset.sum_range_succ]
  rw [hprefixIf]
  simp only [Nat.add_eq, if_pos rfl]
  rw [← hprefix]
  exact (Finset.sum_range_add_sum_Ico f hKm).symm

/-- On one regular block, replacing the gain by its block average loses at
most `n` times the block-start energy error.  The interval deviation and the
lower block-length bound give the coefficient `h - C / m`. -/
private theorem block_average_gain_replacement_lower
    (gainSeq energy : ℕ → ℝ) (a b m : ℕ) (h C nR : ℝ)
    (hab : a < b) (hm : 0 < m) (hlen : m ≤ b - a)
    (hC : 0 ≤ C) (hnR : 0 ≤ nR)
    (hgain0 : ∀ t ∈ Finset.Ico a b, 0 ≤ gainSeq t)
    (hgainN : ∀ t ∈ Finset.Ico a b, gainSeq t ≤ nR)
    (henergy : ∀ t ∈ Finset.Ico a b, 0 ≤ energy t)
    (hdev : |(∑ t ∈ Finset.Ico a b, gainSeq t) -
      (((b - a : ℕ) : ℝ) * h)| ≤ C) :
    (h - C / (m : ℝ)) * (∑ t ∈ Finset.Ico a b, energy t) -
        nR * (∑ t ∈ Finset.Ico a b, |energy t - energy a|) ≤
      ∑ t ∈ Finset.Ico a b, gainSeq t * energy t := by
  classical
  let I := Finset.Ico a b
  let len : ℝ := ((b - a : ℕ) : ℝ)
  let gainSum : ℝ := ∑ t ∈ I, gainSeq t
  let mu : ℝ := gainSum / len
  have hlenNat : 0 < b - a := Nat.sub_pos_of_lt hab
  have hlenPos : 0 < len := by
    dsimp [len]
    exact Nat.cast_pos.mpr hlenNat
  have hcard : (I.card : ℝ) = len := by
    simp [I, len, Nat.card_Ico]
  have hgainSum0 : 0 ≤ gainSum := by
    dsimp [gainSum, I]
    exact Finset.sum_nonneg hgain0
  have hgainSumN : gainSum ≤ len * nR := by
    dsimp [gainSum, I]
    calc
      (∑ t ∈ Finset.Ico a b, gainSeq t) ≤
          ∑ _t ∈ Finset.Ico a b, nR := Finset.sum_le_sum hgainN
      _ = len * nR := by
        simp [len, Nat.card_Ico, nsmul_eq_mul]
  have hmu0 : 0 ≤ mu := div_nonneg hgainSum0 hlenPos.le
  have hmuN : mu ≤ nR := by
    apply (div_le_iff₀ hlenPos).2
    simpa [mu, gainSum, len, mul_comm] using hgainSumN
  have hdevLower : len * h - C ≤ gainSum := by
    have := neg_le_of_abs_le hdev
    linarith
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlenGe : (m : ℝ) ≤ len := by
    dsimp [len]
    exact_mod_cast hlen
  have hCdiv : C / len ≤ C / (m : ℝ) := by
    exact div_le_div_of_nonneg_left hC hmR hlenGe
  have hmuLower : h - C / (m : ℝ) ≤ mu := by
    have hscaled : h - C / len ≤ mu := by
      apply (le_div_iff₀ hlenPos).2
      dsimp [mu, gainSum]
      field_simp [ne_of_gt hlenPos]
      linarith
    linarith
  have hmuCard : mu * (I.card : ℝ) = gainSum := by
    rw [hcard]
    dsimp [mu]
    field_simp [ne_of_gt hlenPos]
  have hcentered :
      (∑ t ∈ I, gainSeq t * energy t) =
        mu * (∑ t ∈ I, energy t) +
          ∑ t ∈ I, (gainSeq t - mu) * (energy t - energy a) := by
    simp_rw [mul_sub, sub_mul]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      ← Finset.sum_mul]
    have hsumGain : (∑ t ∈ I, gainSeq t) = gainSum := rfl
    have hsumMu : (∑ _t ∈ I, mu) = mu * (I.card : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]
    rw [hsumGain, hsumMu, hmuCard]
    ring
  have herrTerm : ∀ t ∈ I,
      -nR * |energy t - energy a| ≤
        (gainSeq t - mu) * (energy t - energy a) := by
    intro t ht
    have hcoeff : |gainSeq t - mu| ≤ nR := by
      rw [abs_le]
      constructor <;> linarith [hgain0 t ht, hgainN t ht, hmu0, hmuN]
    have habs : |(gainSeq t - mu) * (energy t - energy a)| ≤
        nR * |energy t - energy a| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
    convert (neg_le_of_abs_le habs) using 1 <;> ring
  have herr := Finset.sum_le_sum herrTerm
  have henergySum : 0 ≤ ∑ t ∈ I, energy t :=
    Finset.sum_nonneg henergy
  have hmainCoeff :
      (h - C / (m : ℝ)) * (∑ t ∈ I, energy t) ≤
        mu * (∑ t ∈ I, energy t) :=
    mul_le_mul_of_nonneg_right hmuLower henergySum
  rw [hcentered]
  rw [← Finset.mul_sum] at herr
  linarith

/-- Summing the finite-average L2 perturbation estimate over a family of
blocks controls the total block-start energy replacement error by the total
within-block movement and the current energy. -/
private theorem nested_block_energy_replacement_error_le
    {ι E : Type*} [NormedAddCommGroup E]
    (μ : Measure Ω) (J : Finset ι) (I : ι → Finset ℕ)
    (a : ι → ℕ) (x : ℕ → Ω → E)
    (hx : ∀ t, MemLp (x t) 2 μ) :
    (∑ j ∈ J, ∑ t ∈ I j,
        |(∫ omega, ‖x t omega‖ ^ 2 ∂μ) -
          ∫ omega, ‖x (a j) omega‖ ^ 2 ∂μ|) ≤
      (∑ j ∈ J, ∑ t ∈ I j,
          ∫ omega, ‖x t omega - x (a j) omega‖ ^ 2 ∂μ) +
        2 * Real.sqrt
          (∑ j ∈ J, ∑ t ∈ I j,
            ∫ omega, ‖x t omega - x (a j) omega‖ ^ 2 ∂μ) *
          Real.sqrt
            (∑ j ∈ J, ∑ t ∈ I j,
              ∫ omega, ‖x t omega‖ ^ 2 ∂μ) := by
  classical
  let D : ι → ℕ → ℝ := fun j t =>
    ∫ omega, ‖x t omega - x (a j) omega‖ ^ 2 ∂μ
  let G : ℕ → ℝ := fun t => ∫ omega, ‖x t omega‖ ^ 2 ∂μ
  have hD (j : ι) (t : ℕ) : 0 ≤ D j t := by
    dsimp [D]
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hG (t : ℕ) : 0 ≤ G t := by
    dsimp [G]
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hpoint (j : ι) (t : ℕ) :
      |G t - G (a j)| ≤ D j t +
        2 * (Real.sqrt (D j t) * Real.sqrt (G t)) := by
    have hraw :=
      finite_average_integral_sq_abs_sub_le_average_error_sq_add_cross
        1 (fun _ => x (a j)) (fun _ => x t)
        (fun _ _ => hx (a j)) (fun _ _ => hx t)
    rw [← Real.sqrt_mul (hD j t)]
    dsimp [D, G]
    simpa [abs_sub_comm, norm_sub_rev] using hraw
  have hsumPoint :
      (∑ j ∈ J, ∑ t ∈ I j, |G t - G (a j)|) ≤
        (∑ j ∈ J, ∑ t ∈ I j, D j t) +
          2 * (∑ j ∈ J, ∑ t ∈ I j,
            Real.sqrt (D j t) * Real.sqrt (G t)) := by
    calc
      _ ≤ ∑ j ∈ J, ∑ t ∈ I j,
          (D j t + 2 * (Real.sqrt (D j t) * Real.sqrt (G t))) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.sum_le_sum fun t ht => hpoint j t
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hblockCS (j : ι) :
      (∑ t ∈ I j, Real.sqrt (D j t) * Real.sqrt (G t)) ≤
        Real.sqrt (∑ t ∈ I j, D j t) *
          Real.sqrt (∑ t ∈ I j, G t) :=
    Real.sum_sqrt_mul_sqrt_le (I j) (hD j) hG
  have hcrossBlocks :
      (∑ j ∈ J, ∑ t ∈ I j,
          Real.sqrt (D j t) * Real.sqrt (G t)) ≤
        ∑ j ∈ J,
          Real.sqrt (∑ t ∈ I j, D j t) *
            Real.sqrt (∑ t ∈ I j, G t) :=
    Finset.sum_le_sum fun j _hj => hblockCS j
  have houterCS :
      (∑ j ∈ J,
          Real.sqrt (∑ t ∈ I j, D j t) *
            Real.sqrt (∑ t ∈ I j, G t)) ≤
        Real.sqrt (∑ j ∈ J, ∑ t ∈ I j, D j t) *
          Real.sqrt (∑ j ∈ J, ∑ t ∈ I j, G t) := by
    exact Real.sum_sqrt_mul_sqrt_le J
      (fun j => Finset.sum_nonneg fun t _ht => hD j t)
      (fun j => Finset.sum_nonneg fun t _ht => hG t)
  have hcross := hcrossBlocks.trans houterCS
  dsimp [D, G] at hsumPoint hcross ⊢
  nlinarith

/-- The regular tail-merged partition gives the coefficient-preserving
gain replacement used before equation (63).  Its error is expressed by the
actual summed within-block gradient movement, ready for the movement bound. -/
private theorem regular_partition_gain_replacement_lower
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon) (m : ℕ)
    (h Cgain : ℝ) (hm : 0 < m) (hmT : m ≤ T.1)
    (hCgain : 0 ≤ Cgain)
    (hintervalGain : ∀ a b : ℕ, a ≤ b →
      |(∑ t ∈ Finset.Ico a b, gain S.network t) -
        (((b - a : ℕ) : ℝ) * h)| ≤ Cgain) :
    let k := T.1 / m
    let blockEnd : ℕ → ℕ := fun j =>
      if j + 1 = k then T.1 else (j + 1) * m
    let e : ℕ → ℝ := fun t =>
      SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S)
          (correctedCenter S omega alpha t)‖ ^ 2)
    let G := ∑ t ∈ Finset.range T.1, e t
    let W := ∑ j ∈ Finset.range k,
      ∑ t ∈ Finset.Ico (j * m) (blockEnd j),
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t) -
            gradient (averageObjective S)
              (correctedCenter S omega alpha (j * m))‖ ^ 2)
    (h - Cgain / (m : ℝ)) * G -
        (n : ℝ) * (2 * Real.sqrt G * Real.sqrt W + W) ≤
      ∑ t ∈ Finset.range T.1, gain S.network t * e t := by
  classical
  dsimp only
  let k := T.1 / m
  let blockEnd : ℕ → ℕ := fun j =>
    if j + 1 = k then T.1 else (j + 1) * m
  let blocks : ℕ → Finset ℕ := fun j => Finset.Ico (j * m) (blockEnd j)
  let x : ℕ → Ω → Point d := fun t omega =>
    gradient (averageObjective S) (correctedCenter S omega alpha t)
  let e : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega => ‖x t omega‖ ^ 2)
  let G : ℝ := ∑ t ∈ Finset.range T.1, e t
  let W : ℝ := ∑ j ∈ Finset.range k, ∑ t ∈ blocks j,
    SOptLib.expectation S.probability (fun omega =>
      ‖x t omega - x (j * m) omega‖ ^ 2)
  let E : ℝ := ∑ j ∈ Finset.range k, ∑ t ∈ blocks j,
    |e t - e (j * m)|
  have hcertE := regular_tail_merged_partition_certificate
    e T.1 m hm hmT
  have hcertGain := regular_tail_merged_partition_certificate
    (fun t => gain S.network t * e t) T.1 m hm hmT
  change (∀ j ∈ Finset.range k,
      m ≤ blockEnd j - j * m ∧ blockEnd j - j * m ≤ 2 * m) ∧
    (∑ t ∈ Finset.range T.1, e t) =
      ∑ j ∈ Finset.range k, ∑ t ∈ blocks j, e t at hcertE
  change (∀ j ∈ Finset.range k,
      m ≤ blockEnd j - j * m ∧ blockEnd j - j * m ≤ 2 * m) ∧
    (∑ t ∈ Finset.range T.1, gain S.network t * e t) =
      ∑ j ∈ Finset.range k,
        ∑ t ∈ blocks j, gain S.network t * e t at hcertGain
  have hlength := hcertE.1
  have hpartE := hcertE.2
  have hpartGain := hcertGain.2
  have he0 (t : ℕ) : 0 ≤ e t := by
    dsimp [e, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hgain0 (t : ℕ) : 0 ≤ gain S.network t :=
    (gainFloor_le_gain S.network t).trans'
      (uniform_mixing_and_influence S.network).2.2.2.2.2.2.2.1.le
  have hgainN (t : ℕ) : gain S.network t ≤ (n : ℝ) :=
    gain_le_n S.network t
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hblock (j : ℕ) (hj : j ∈ Finset.range k) :
      (h - Cgain / (m : ℝ)) * (∑ t ∈ blocks j, e t) -
          (n : ℝ) * (∑ t ∈ blocks j, |e t - e (j * m)|) ≤
        ∑ t ∈ blocks j, gain S.network t * e t := by
    have hlen := (hlength j hj).1
    have hstartEnd : j * m < blockEnd j := by omega
    apply block_average_gain_replacement_lower
      (gain S.network) e (j * m) (blockEnd j) m h Cgain (n : ℝ)
      hstartEnd hm hlen hCgain hnR
    · intro t _ht
      exact hgain0 t
    · intro t _ht
      exact hgainN t
    · intro t _ht
      exact he0 t
    · exact hintervalGain (j * m) (blockEnd j) hstartEnd.le
  have hblocks := Finset.sum_le_sum hblock
  have haggregate :
      (h - Cgain / (m : ℝ)) * G - (n : ℝ) * E ≤
        ∑ t ∈ Finset.range T.1, gain S.network t * e t := by
    dsimp [G, E]
    rw [hpartGain, hpartE]
    simpa [Finset.mul_sum, Finset.sum_sub_distrib] using hblocks
  have hx (t : ℕ) : MemLp (x t) 2 S.probability := by
    simpa [x] using
      (corrected_center_descent_payload_memLp_two S alpha t).2.1
  have hreplace := nested_block_energy_replacement_error_le
    S.probability (Finset.range k) blocks (fun j => j * m) x hx
  dsimp [e, x, SOptLib.expectation] at hpartE
  rw [← hpartE] at hreplace
  have hEG : E ≤ W + 2 * Real.sqrt W * Real.sqrt G := by
    dsimp [E, W, G, e, x, blocks, SOptLib.expectation]
    simpa using hreplace
  have hEG' : E ≤ 2 * Real.sqrt G * Real.sqrt W + W := by
    nlinarith
  change (h - Cgain / (m : ℝ)) * G -
      (n : ℝ) * (2 * Real.sqrt G * Real.sqrt W + W) ≤
    ∑ t ∈ Finset.range T.1, gain S.network t * e t
  nlinarith [mul_le_mul_of_nonneg_left hEG' hnR]

/-- Summed within-block movement on a block of length at most `2m`. -/
private theorem corrected_center_regular_block_movement_sum_le
    (S : Setup n d Ω) (alpha : ℝ) {a b m : ℕ}
    (hab : a ≤ b) (hlen : b - a ≤ 2 * m) :
    (∑ t ∈ Finset.Ico a b,
      SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S) (correctedCenter S omega alpha t) -
          gradient (averageObjective S)
            (correctedCenter S omega alpha a)‖ ^ 2)) ≤
      12 * (S.L * alpha) ^ 2 *
        ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 *
            (∑ t ∈ Finset.Ico a b,
              SOptLib.expectation S.probability (fun omega =>
                ‖gradient (averageObjective S)
                  (correctedCenter S omega alpha t)‖ ^ 2)) +
          (m : ℝ) ^ 2 *
            (∑ t ∈ Finset.Ico a b,
              SOptLib.expectation S.probability (fun omega =>
                ‖correctedDrift S omega alpha t‖ ^ 2)) +
          (m : ℝ) * S.σ ^ 2 *
            (∑ t ∈ Finset.Ico a b, influenceEnergy S.network t)) := by
  classical
  let I := Finset.Ico a b
  let e : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2)
  let v : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖correctedDrift S omega alpha t‖ ^ 2)
  let q : ℕ → ℝ := fun t => influenceEnergy S.network t
  let G := ∑ t ∈ I, e t
  let V := ∑ t ∈ I, v t
  let Q := ∑ t ∈ I, q t
  have he0 (t : ℕ) : 0 ≤ e t := by
    dsimp [e, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hv0 (t : ℕ) : 0 ≤ v t := by
    dsimp [v, SOptLib.expectation]
    exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hq0 (t : ℕ) : 0 ≤ q t := by
    dsimp [q, influenceEnergy]
    exact Finset.sum_nonneg fun i _hi => sq_nonneg _
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun t _ht => he0 t
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun t _ht => hv0 t
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun t _ht => hq0 t
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hcard : (I.card : ℝ) ≤ 2 * (m : ℝ) := by
    dsimp [I]
    simp only [Nat.card_Ico]
    exact_mod_cast hlen
  have hterm (t : ℕ) (ht : t ∈ I) :
      SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S) (correctedCenter S omega alpha t) -
          gradient (averageObjective S) (correctedCenter S omega alpha a)‖ ^ 2) ≤
        3 * (S.L * alpha) ^ 2 *
          (2 * (m : ℝ) * (n : ℝ) ^ 2 * G +
            2 * (m : ℝ) * V + S.σ ^ 2 * Q) := by
    have hat : a ≤ t := (Finset.mem_Ico.1 ht).1
    have htb : t ≤ b := (Finset.mem_Ico.1 ht).2.le
    have hsub : Finset.Ico a t ⊆ I := by
      dsimp [I]
      exact Finset.Ico_subset_Ico_right htb
    have hcardpreI : ((Finset.Ico a t).card : ℝ) ≤ (I.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hcardpre : ((Finset.Ico a t).card : ℝ) ≤ 2 * (m : ℝ) :=
      hcardpreI.trans hcard
    have hgainpre : (∑ r ∈ Finset.Ico a t, gain S.network r) ≤
        2 * (m : ℝ) * (n : ℝ) := by
      calc
        _ ≤ ∑ _r ∈ Finset.Ico a t, (n : ℝ) :=
          Finset.sum_le_sum fun r _hr => gain_le_n S.network r
        _ = ((Finset.Ico a t).card : ℝ) * (n : ℝ) := by
          simp [nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hcardpre hn0
    have hgainE : (∑ r ∈ Finset.Ico a t, gain S.network r * e r) ≤
        (n : ℝ) * G := by
      calc
        _ ≤ ∑ r ∈ Finset.Ico a t, (n : ℝ) * e r :=
          Finset.sum_le_sum fun r _hr =>
            mul_le_mul_of_nonneg_right (gain_le_n S.network r) (he0 r)
        _ ≤ ∑ r ∈ I, (n : ℝ) * e r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun r _hr _ => mul_nonneg hn0 (he0 r))
        _ = (n : ℝ) * G := by rw [Finset.mul_sum]
    have hgainpre0 : 0 ≤ ∑ r ∈ Finset.Ico a t, gain S.network r :=
      Finset.sum_nonneg fun r _ =>
        (gainFloor_le_gain S.network r).trans'
          (uniform_mixing_and_influence S.network).2.2.2.2.2.2.2.1.le
    have hgainE0 : 0 ≤ ∑ r ∈ Finset.Ico a t, gain S.network r * e r :=
      Finset.sum_nonneg fun r _ => mul_nonneg
        ((gainFloor_le_gain S.network r).trans'
          (uniform_mixing_and_influence S.network).2.2.2.2.2.2.2.1.le)
        (he0 r)
    have hprod := mul_le_mul hgainpre hgainE hgainE0
      (by positivity : 0 ≤ 2 * (m : ℝ) * (n : ℝ))
    have hVpre : (∑ r ∈ Finset.Ico a t, v r) ≤ V :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hv0 r)
    have hQpre : (∑ r ∈ Finset.Ico a t, q r) ≤ Q :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hq0 r)
    have hins :
        (∑ r ∈ Finset.Ico a t, gain S.network r) *
            (∑ r ∈ Finset.Ico a t, gain S.network r * e r) +
          ((Finset.Ico a t).card : ℝ) * (∑ r ∈ Finset.Ico a t, v r) +
          S.σ ^ 2 * (∑ r ∈ Finset.Ico a t, q r) ≤
        2 * (m : ℝ) * (n : ℝ) ^ 2 * G +
          2 * (m : ℝ) * V + S.σ ^ 2 * Q := by
      have hcardV := mul_le_mul hcardpre hVpre
        (Finset.sum_nonneg fun r _ => hv0 r)
        (by positivity : 0 ≤ 2 * (m : ℝ))
      have hnoise := mul_le_mul_of_nonneg_left hQpre (sq_nonneg S.σ)
      nlinarith
    have hraw := corrected_center_within_interval_gradient_movement
      S alpha hat
    exact hraw.trans (mul_le_mul_of_nonneg_left hins (by positivity))
  have hsum := Finset.sum_le_sum hterm
  have hinside0 : 0 ≤
      2 * (m : ℝ) * (n : ℝ) ^ 2 * G +
        2 * (m : ℝ) * V + S.σ ^ 2 * Q := by positivity
  have hscale := mul_le_mul_of_nonneg_right hcard hinside0
  dsimp [I, e, v, q, G, V, Q] at hsum ⊢
  calc
    _ ≤ ∑ _t ∈ Finset.Ico a b,
        3 * (S.L * alpha) ^ 2 *
          (2 * (m : ℝ) * (n : ℝ) ^ 2 *
              (∑ t ∈ Finset.Ico a b,
                SOptLib.expectation S.probability (fun omega =>
                  ‖gradient (averageObjective S)
                    (correctedCenter S omega alpha t)‖ ^ 2)) +
            2 * (m : ℝ) *
              (∑ t ∈ Finset.Ico a b,
                SOptLib.expectation S.probability (fun omega =>
                  ‖correctedDrift S omega alpha t‖ ^ 2)) +
            S.σ ^ 2 *
              (∑ t ∈ Finset.Ico a b, influenceEnergy S.network t)) := hsum
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcoef : 0 ≤ 3 * (S.L * alpha) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hscale hcoef
      calc
        ((Finset.Ico a b).card : ℝ) *
            (3 * (S.L * alpha) ^ 2 *
              (2 * (m : ℝ) * (n : ℝ) ^ 2 * G +
                2 * (m : ℝ) * V + S.σ ^ 2 * Q)) =
            3 * (S.L * alpha) ^ 2 *
              ((I.card : ℝ) *
                (2 * (m : ℝ) * (n : ℝ) ^ 2 * G +
                  2 * (m : ℝ) * V + S.σ ^ 2 * Q)) := by
              dsimp [I]
              ring
        _ ≤ 3 * (S.L * alpha) ^ 2 *
              (2 * (m : ℝ) *
                (2 * (m : ℝ) * (n : ℝ) ^ 2 * G +
                  2 * (m : ℝ) * V + S.σ ^ 2 * Q)) := this
        _ ≤ 12 * (S.L * alpha) ^ 2 *
            ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G +
              (m : ℝ) ^ 2 * V + (m : ℝ) * S.σ ^ 2 * Q) := by
              have hnoise : 0 ≤
                  (S.L * alpha) ^ 2 * (m : ℝ) * S.σ ^ 2 * Q := by
                positivity
              nlinarith

/-- The regular tail-merged partition sums the one-block movement bounds into
the global variation budget used in equation (63). -/
private theorem regular_partition_movement_le
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon) (m : ℕ)
    (hm : 0 < m) (hmT : m ≤ T.1) :
    let k := T.1 / m
    let blockEnd : ℕ → ℕ := fun j =>
      if j + 1 = k then T.1 else (j + 1) * m
    let W := ∑ j ∈ Finset.range k,
      ∑ t ∈ Finset.Ico (j * m) (blockEnd j),
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t) -
            gradient (averageObjective S)
              (correctedCenter S omega alpha (j * m))‖ ^ 2)
    W ≤ 12 * (S.L * alpha) ^ 2 *
      ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * correctedGradientEnergy S alpha T +
        (m : ℝ) ^ 2 * correctedDriftEnergy S alpha T +
        (m : ℝ) * S.σ ^ 2 *
          (∑ t ∈ Finset.range T.1, influenceEnergy S.network t)) := by
  classical
  dsimp only
  let k := T.1 / m
  let blockEnd : ℕ → ℕ := fun j =>
    if j + 1 = k then T.1 else (j + 1) * m
  let blocks : ℕ → Finset ℕ := fun j => Finset.Ico (j * m) (blockEnd j)
  let e : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2)
  let v : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖correctedDrift S omega alpha t‖ ^ 2)
  let q : ℕ → ℝ := fun t => influenceEnergy S.network t
  have hcertE := regular_tail_merged_partition_certificate e T.1 m hm hmT
  have hcertV := regular_tail_merged_partition_certificate v T.1 m hm hmT
  have hcertQ := regular_tail_merged_partition_certificate q T.1 m hm hmT
  change (∀ j ∈ Finset.range k,
      m ≤ blockEnd j - j * m ∧ blockEnd j - j * m ≤ 2 * m) ∧
    (∑ t ∈ Finset.range T.1, e t) =
      ∑ j ∈ Finset.range k, ∑ t ∈ blocks j, e t at hcertE
  change (∀ j ∈ Finset.range k,
      m ≤ blockEnd j - j * m ∧ blockEnd j - j * m ≤ 2 * m) ∧
    (∑ t ∈ Finset.range T.1, v t) =
      ∑ j ∈ Finset.range k, ∑ t ∈ blocks j, v t at hcertV
  change (∀ j ∈ Finset.range k,
      m ≤ blockEnd j - j * m ∧ blockEnd j - j * m ≤ 2 * m) ∧
    (∑ t ∈ Finset.range T.1, q t) =
      ∑ j ∈ Finset.range k, ∑ t ∈ blocks j, q t at hcertQ
  have hblock (j : ℕ) (hj : j ∈ Finset.range k) :=
    corrected_center_regular_block_movement_sum_le
      S alpha (a := j * m) (b := blockEnd j) (m := m)
      (by
        have hlen := (hcertE.1 j hj).1
        omega)
      (hcertE.1 j hj).2
  have hsum := Finset.sum_le_sum hblock
  rw [← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  rw [← hcertE.2, ← hcertV.2, ← hcertQ.2] at hsum
  simpa [correctedGradientEnergy, correctedDriftEnergy] using hsum

/-- The complete T2 bridge: the regular partition has the explicit global
movement budget, and that budget supplies the coefficient-preserving periodic
gain replacement. -/
private theorem periodic_regular_block_movement_gain_lower
    (S : Setup n d Ω) (alpha : ℝ) (T : PositiveHorizon) (m : ℕ)
    (h Cgain : ℝ) (hm : 0 < m) (hmT : m ≤ T.1)
    (hCgain : 0 ≤ Cgain)
    (hintervalGain : ∀ a b : ℕ, a ≤ b →
      |(∑ t ∈ Finset.Ico a b, gain S.network t) -
        (((b - a : ℕ) : ℝ) * h)| ≤ Cgain) :
    let k := T.1 / m
    let blockEnd : ℕ → ℕ := fun j =>
      if j + 1 = k then T.1 else (j + 1) * m
    let e : ℕ → ℝ := fun t =>
      SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S)
          (correctedCenter S omega alpha t)‖ ^ 2)
    let G := correctedGradientEnergy S alpha T
    let V := correctedDriftEnergy S alpha T
    let Q := ∑ t ∈ Finset.range T.1, influenceEnergy S.network t
    let W := ∑ j ∈ Finset.range k,
      ∑ t ∈ Finset.Ico (j * m) (blockEnd j),
        SOptLib.expectation S.probability (fun omega =>
          ‖gradient (averageObjective S)
              (correctedCenter S omega alpha t) -
            gradient (averageObjective S)
              (correctedCenter S omega alpha (j * m))‖ ^ 2)
    let Wvar := 12 * (S.L * alpha) ^ 2 *
      ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G +
        (m : ℝ) ^ 2 * V + (m : ℝ) * S.σ ^ 2 * Q)
    W ≤ Wvar ∧
      (h - Cgain / (m : ℝ)) * G -
          (n : ℝ) * (2 * Real.sqrt G * Real.sqrt Wvar + Wvar) ≤
        ∑ t ∈ Finset.range T.1, gain S.network t * e t := by
  classical
  dsimp only
  let k := T.1 / m
  let blockEnd : ℕ → ℕ := fun j =>
    if j + 1 = k then T.1 else (j + 1) * m
  let e : ℕ → ℝ := fun t =>
    SOptLib.expectation S.probability (fun omega =>
      ‖gradient (averageObjective S) (correctedCenter S omega alpha t)‖ ^ 2)
  let G := correctedGradientEnergy S alpha T
  let V := correctedDriftEnergy S alpha T
  let Q := ∑ t ∈ Finset.range T.1, influenceEnergy S.network t
  let W := ∑ j ∈ Finset.range k,
    ∑ t ∈ Finset.Ico (j * m) (blockEnd j),
      SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S) (correctedCenter S omega alpha t) -
          gradient (averageObjective S)
            (correctedCenter S omega alpha (j * m))‖ ^ 2)
  let Wvar := 12 * (S.L * alpha) ^ 2 *
    ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G +
      (m : ℝ) ^ 2 * V + (m : ℝ) * S.σ ^ 2 * Q)
  have hmove := regular_partition_movement_le S alpha T m hm hmT
  change W ≤ Wvar at hmove
  have hgain := regular_partition_gain_replacement_lower
    S alpha T m h Cgain hm hmT hCgain hintervalGain
  change (h - Cgain / (m : ℝ)) * G -
      (n : ℝ) * (2 * Real.sqrt G * Real.sqrt W + W) ≤
    ∑ t ∈ Finset.range T.1, gain S.network t * e t at hgain
  have hW0 : 0 ≤ W := by
    dsimp [W, SOptLib.expectation]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun t _ =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hG0 : 0 ≤ G := by
    dsimp [G, correctedGradientEnergy, SOptLib.expectation]
    exact Finset.sum_nonneg fun t _ =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hsqrt := Real.sqrt_le_sqrt hmove
  have hrem :
      2 * Real.sqrt G * Real.sqrt W + W ≤
        2 * Real.sqrt G * Real.sqrt Wvar + Wvar := by
    have hcross := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg G))
    linarith
  refine ⟨hmove, ?_⟩
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hrem hn0]

/-- Insert the regular-partition gain replacement into the exact constant
weight corrected-center descent.  This is the unsimplified scalar predecessor
of equation (63). -/
private theorem periodic_regular_gain_descent_scalar
    (S : Setup n d Ω) (alpha : ℝ) (halpha : 0 < alpha)
    (T : PositiveHorizon) (m : ℕ) (h Cgain : ℝ)
    (hm : 0 < m) (hmT : m ≤ T.1) (hCgain : 0 ≤ Cgain)
    (hintervalGain : ∀ a b : ℕ, a ≤ b →
      |(∑ t ∈ Finset.Ico a b, gain S.network t) -
        (((b - a : ℕ) : ℝ) * h)| ≤ Cgain) :
    let G := correctedGradientEnergy S alpha T
    let V := correctedDriftEnergy S alpha T
    let Q := ∑ t ∈ Finset.range T.1, influenceEnergy S.network t
    let Wvar := 12 * (S.L * alpha) ^ 2 *
      ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G +
        (m : ℝ) ^ 2 * V + (m : ℝ) * S.σ ^ 2 * Q)
    alpha * ((h - Cgain / (m : ℝ)) * G -
        (n : ℝ) * (2 * Real.sqrt G * Real.sqrt Wvar + Wvar)) ≤
      S.Δ + alpha * (Real.sqrt G * Real.sqrt V) +
        (S.L * alpha ^ 2 / 2) *
          ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 +
        S.L * alpha ^ 2 * S.σ ^ 2 / 2 * Q := by
  dsimp only
  let G := correctedGradientEnergy S alpha T
  let V := correctedDriftEnergy S alpha T
  let Q := ∑ t ∈ Finset.range T.1, influenceEnergy S.network t
  let Wvar := 12 * (S.L * alpha) ^ 2 *
    ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G +
      (m : ℝ) ^ 2 * V + (m : ℝ) * S.σ ^ 2 * Q)
  have hreplace := (periodic_regular_block_movement_gain_lower
    S alpha T m h Cgain hm hmT hCgain hintervalGain).2
  change (h - Cgain / (m : ℝ)) * G -
      (n : ℝ) * (2 * Real.sqrt G * Real.sqrt Wvar + Wvar) ≤
    ∑ t ∈ Finset.range T.1, gain S.network t *
      SOptLib.expectation S.probability (fun omega =>
        ‖gradient (averageObjective S)
          (correctedCenter S omega alpha t)‖ ^ 2) at hreplace
  have hscaled := mul_le_mul_of_nonneg_left hreplace halpha.le
  have hdescent := corrected_center_suffix_weighted_gain_descent
    S alpha halpha T (fun _ => (1 : ℝ))
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
  exact hscaled.trans (by simpa [G, V, Q] using hdescent)

/-- Exact scalar balancing used in the source substitution after (63). -/
private theorem periodic_balanced_leading_pair_eq
    (L Δ σ q h t : ℝ) (hL : 0 < L) (hΔ : 0 < Δ)
    (hσ : 0 < σ) (hq : 0 < q) (hh : 0 < h) (ht : 0 < t) :
    let s := Real.sqrt (2 * ADelta L Δ / (σ ^ 2 * q * t))
    (Δ * L / s + s * σ ^ 2 * q * t / 2) / (h * t) =
      σ * Real.sqrt (2 * ADelta L Δ * q / (h ^ 2 * t)) := by
  dsimp only
  let s := Real.sqrt (2 * ADelta L Δ / (σ ^ 2 * q * t))
  have hsarg : 0 < 2 * ADelta L Δ / (σ ^ 2 * q * t) := by
    unfold ADelta
    positivity
  have hs : 0 < s := Real.sqrt_pos.2 hsarg
  have hsSq : s ^ 2 = 2 * ADelta L Δ / (σ ^ 2 * q * t) := by
    dsimp [s]
    exact Real.sq_sqrt hsarg.le
  have hbalance : s * σ ^ 2 * q * t / 2 = Δ * L / s := by
    apply (mul_left_cancel₀ hs.ne')
    rw [show ADelta L Δ = L * Δ by rfl] at hsSq
    field_simp [hs.ne', hσ.ne', hq.ne', ht.ne'] at hsSq ⊢
    nlinarith
  change (Δ * L / s + s * σ ^ 2 * q * t / 2) / (h * t) = _
  rw [hbalance]
  let y := (2 * (Δ * L / s)) / (h * t)
  let z := σ * Real.sqrt (2 * ADelta L Δ * q / (h ^ 2 * t))
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzArg : 0 ≤ 2 * ADelta L Δ * q / (h ^ 2 * t) := by
    unfold ADelta
    positivity
  have hzSq : z ^ 2 = σ ^ 2 *
      (2 * ADelta L Δ * q / (h ^ 2 * t)) := by
    dsimp [z]
    rw [mul_pow, Real.sq_sqrt hzArg]
  have hySq : y ^ 2 = σ ^ 2 *
      (2 * ADelta L Δ * q / (h ^ 2 * t)) := by
    dsimp [y]
    rw [show ADelta L Δ = L * Δ by rfl] at hsSq ⊢
    field_simp [hs.ne', hh.ne', ht.ne', hσ.ne', hq.ne'] at hsSq ⊢
    nlinarith
  have : y = z := by nlinarith
  simpa [y, z, two_mul] using this

/-- Positivity of the source corrected-center cap, used to make the balanced
step admissible at one instance-independent horizon. -/
private theorem correctedCenterStepCap_pos (N : NetworkSetup n) :
    0 < correctedCenterStepCap N := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hg : 0 < gainFloor N :=
    (mul_pos hn (by
      unfold mixingMinorization
      split_ifs
      · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
      · norm_num)).trans_le (gainFloor_ge_n_mul_mixingMinorization N)
  have hrate : mixingRate N < 1 := mixingRate_lt_one N
  have hrow : 0 < rowMixingConstant N := by
    unfold rowMixingConstant
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hn))
      (blockContraction_pos N)
  have hdisagreement_pos : 0 < disagreementKernel N := by
    unfold disagreementKernel
    exact div_pos (sq_pos_of_pos hrow) (sq_pos_of_pos (sub_pos.mpr hrate))
  have hcolumn : 0 < columnMixingConstant N := by
    unfold columnMixingConstant
    exact div_pos (Real.sqrt_pos.2 hn) (blockContraction_pos N)
  have hincrement : 0 < incrementKernel N := by
    unfold incrementKernel
    positivity
  have htrackerIncrement : 0 < trackerIncrementKernel N := by
    unfold trackerIncrementKernel
    exact div_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hcolumn))
          (sq_pos_of_pos (by positivity : 0 < 1 + Real.sqrt n)))
        hincrement)
      (sq_pos_of_pos (sub_pos.mpr hrate))
  have hcontrolRB : 0 < controlRB N := by
    unfold controlRB controlKa controlMB
    have hcoef : 0 < (3 * (n : ℝ) + 6 * (n : ℝ) ^ 2) := by positivity
    positivity
  unfold correctedCenterStepCap
  simp only [lt_min_iff]
  refine ⟨by norm_num, by positivity, ?_, ?_, ?_⟩
  · exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))
  · exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))
  · exact div_pos hg (Real.sqrt_pos.2 (by positivity))

set_option maxHeartbeats 12000000 in
/-- Source steps 11--17 at their common-step boundary.  The balanced
dimensionless step is chosen before the fixed-class instance, while all
instance dependence is discharged by the uniform corrected-center controls. -/
private theorem periodic_equation63_uniform_fixed_instance_upper
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ H : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hH : 0 ≤ H)
    (hh : 0 < periodicGainMean N p hp)
    (hhq : periodicGainMean N p hp ^ 2 / (n : ℝ) ≤
      periodicInfluenceMean N p)
    (Cgain Cenergy : ℝ) (hCgain : 0 ≤ Cgain) (hCenergy : 0 ≤ Cenergy)
    (hinterval : ∀ a b : ℕ, a ≤ b →
      |(∑ t ∈ Finset.Ico a b, gain N t) -
          ((b - a : ℕ) : ℝ) * periodicGainMean N p hp| ≤ Cgain ∧
      |(∑ t ∈ Finset.Ico a b, influenceEnergy N t) -
          ((b - a : ℕ) : ℝ) * periodicInfluenceMean N p| ≤ Cenergy)
    (Tblock : ℕ)
    (hBlockLength : ∀ T : PositiveHorizon, Tblock ≤ T.1 →
      (periodicRiskBlockLength T : ℝ) ≤ Real.sqrt (T.1 : ℝ)) :
    ∃ Kup : ℝ, 0 ≤ Kup ∧ ∃ Tup : ℕ, ∀ T : PositiveHorizon, Tup ≤ T.1 →
      ∃ sT : AdmissibleDimensionlessStepsize n,
        sT.1 = Real.sqrt (2 * ADelta L Δ /
          (σ ^ 2 * periodicInfluenceMean N p * T.1)) ∧
        ∀ I : fixedInstanceClass N L Δ σ H,
          I.1.cost (sT.1 / L) T ≤
            σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
              (periodicGainMean N p hp ^ 2 * T.1)) +
              Kup / Real.rpow T.1 ((2 : ℝ) / 3) := by
  let h := periodicGainMean N p hp
  let q := periodicInfluenceMean N p
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hq : 0 < q := by
    have hleft : 0 < periodicGainMean N p hp ^ 2 / (n : ℝ) :=
      div_pos (sq_pos_of_pos hh) hn
    exact hleft.trans_le hhq
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  let c := Real.sqrt (2 * ADelta L Δ / (σ ^ 2 * q))
  have hcarg : 0 < 2 * ADelta L Δ / (σ ^ 2 * q) := by
    dsimp [q]
    unfold ADelta
    positivity
  have hc : 0 < c := Real.sqrt_pos.2 hcarg
  have hcSq : c ^ 2 = 2 * ADelta L Δ / (σ ^ 2 * q) := by
    dsimp [c]
    exact Real.sq_sqrt hcarg.le
  let aCap := min (correctedCenterStepCap N) (1 / (64 * (n : ℝ)))
  have haCap : 0 < aCap := by
    dsimp [aCap]
    exact lt_min (correctedCenterStepCap_pos N) (by positivity)
  let R := max 1 (c / aCap)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let Tup := max Tblock (Nat.ceil (R ^ (6 : ℕ)))
  let CG : ℝ :=
    4 * Δ * L / (c * gainFloor N) +
      8 * |controlRH N| * (n : ℝ) * H ^ 2 / gainFloor N ^ 2 +
      8 * |controlRN N| * c ^ 2 * σ ^ 2 / gainFloor N ^ 2 +
      2 * c * σ ^ 2 / gainFloor N * (q + Cenergy)
  let CV : ℝ :=
    |controlRH N| * (n : ℝ) * H ^ 2 +
      c ^ 2 * (|controlRB N| * CG + |controlRN N| * σ ^ 2)
  let CW : ℝ := 12 * c ^ 2 *
    (9 * (n : ℝ) ^ 2 * CG + 9 * CV + 3 * σ ^ 2 * (q + Cenergy))
  let CB : ℝ :=
    |controlJB N| * CG + |controlJH N| * (n : ℝ) * H ^ 2 +
      |controlJN N| * σ ^ 2
  let KE : ℝ := 2 * Real.sqrt (CG * CW) + CW
  let KD : ℝ := 2 * (n : ℝ) ^ 2 * CG + 2 * CV
  let KO : ℝ := 2 * c * Real.sqrt (CG * CB) + c ^ 2 * CB
  let KR : ℝ :=
    Real.sqrt (CG * CV) + c * KD / 2 +
      c * σ ^ 2 * Cenergy / 2 + (n : ℝ) * KE + Cgain * CG
  let Kup : ℝ := KR / h + KO
  have hCG : 0 ≤ CG := by dsimp [CG]; positivity
  have hCV : 0 ≤ CV := by dsimp [CV]; positivity
  have hCW : 0 ≤ CW := by dsimp [CW]; positivity
  have hCB : 0 ≤ CB := by dsimp [CB]; positivity
  have hKE : 0 ≤ KE := by dsimp [KE]; positivity
  have hKD : 0 ≤ KD := by dsimp [KD]; positivity
  have hKO : 0 ≤ KO := by dsimp [KO]; positivity
  have hKR : 0 ≤ KR := by dsimp [KR]; positivity
  have hKup : 0 ≤ Kup := by dsimp [Kup, h]; positivity
  refine ⟨Kup, hKup, Tup, ?_⟩
  intro T hTup
  have hTblock : Tblock ≤ T.1 := (le_max_left _ _).trans hTup
  let t : ℝ := (T.1 : ℝ)
  let r : ℝ := Real.rpow t ((1 : ℝ) / 6)
  obtain ⟨hrOne, hrSix, hrm, hmr, hrFour⟩ := periodic_risk_schedule_facts T
  change (1 : ℝ) ≤ r at hrOne
  change r ^ (6 : ℕ) = t at hrSix
  change r ≤ (periodicRiskBlockLength T : ℝ) at hrm
  change (periodicRiskBlockLength T : ℝ) ≤ r + 2 at hmr
  change Real.rpow t ((2 : ℝ) / 3) = r ^ (4 : ℕ) at hrFour
  have hr : 0 < r := zero_lt_one.trans_le hrOne
  have ht : 0 < t := by
    dsimp [t]
    exact Nat.cast_pos.mpr T.2
  have hceil : R ^ (6 : ℕ) ≤ (Nat.ceil (R ^ (6 : ℕ)) : ℝ) :=
    Nat.le_ceil _
  have hceilT : Nat.ceil (R ^ (6 : ℕ)) ≤ T.1 :=
    (le_max_right _ _).trans hTup
  have hRpow : R ^ (6 : ℕ) ≤ r ^ (6 : ℕ) := by
    rw [hrSix]
    exact hceil.trans (by dsimp [t]; exact_mod_cast hceilT)
  have hRr : R ≤ r :=
    (pow_le_pow_iff_left₀ hR0 (show 0 ≤ r from hr.le)
      (by norm_num : (6 : ℕ) ≠ 0)).mp hRpow
  have hcar : c / aCap ≤ r := (le_max_right _ _).trans hRr
  have hcLe : c ≤ aCap * r := by
    simpa [mul_comm] using (div_le_iff₀ haCap).mp hcar
  have hrCube : r ≤ r ^ (3 : ℕ) := by
    calc
      r ≤ r * r := by
        calc
          r = r * 1 := by ring
          _ ≤ r * r := mul_le_mul_of_nonneg_left hrOne hr.le
      _ ≤ r * r * r := by
        simpa using
          (mul_le_mul_of_nonneg_left hrOne (mul_nonneg hr.le hr.le))
      _ = r ^ (3 : ℕ) := by ring
  have hcLeCube : c ≤ aCap * r ^ (3 : ℕ) :=
    hcLe.trans (mul_le_mul_of_nonneg_left hrCube haCap.le)
  let s : ℝ := c / r ^ (3 : ℕ)
  have hs : 0 < s := div_pos hc (pow_pos hr 3)
  have hsCapBoth : s ≤ aCap := by
    exact (div_le_iff₀ (pow_pos hr 3)).2 (by simpa [mul_comm] using hcLeCube)
  have hsCenter : s ≤ correctedCenterStepCap N :=
    hsCapBoth.trans (min_le_left _ _)
  have hsAdmissible : s ≤ 1 / (64 * (n : ℝ)) :=
    hsCapBoth.trans (min_le_right _ _)
  let sT : AdmissibleDimensionlessStepsize n := ⟨s, hs, hsAdmissible⟩
  have hsFormula : s = Real.sqrt (2 * ADelta L Δ / (σ ^ 2 * q * t)) := by
    have hsArg : 0 ≤ 2 * ADelta L Δ / (σ ^ 2 * q * t) := by
      unfold ADelta
      positivity
    have hright : 0 ≤ Real.sqrt (2 * ADelta L Δ / (σ ^ 2 * q * t)) :=
      Real.sqrt_nonneg _
    apply (sq_eq_sq₀ hs.le hright).mp
    rw [Real.sq_sqrt hsArg]
    calc
      s ^ 2 = c ^ 2 / r ^ (6 : ℕ) := by
        dsimp [s]
        rw [div_pow]
        ring
      _ = (2 * ADelta L Δ / (σ ^ 2 * q)) / t := by
        rw [hcSq, hrSix]
      _ = 2 * ADelta L Δ / (σ ^ 2 * q * t) := by ring
  refine ⟨sT, ?_, ?_⟩
  · simpa [sT, q, t] using hsFormula
  intro I
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  let S := I.1.setup
  let m := periodicRiskBlockLength T
  let G := correctedGradientEnergy S (s / L) T
  let V := correctedDriftEnergy S (s / L) T
  let J := correctedCenterOffsetEnergy S (s / L) T
  let Q := ∑ u ∈ Finset.range T.1, influenceEnergy N u
  let W := 12 * (L * (s / L)) ^ 2 *
    ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G +
      (m : ℝ) ^ 2 * V + (m : ℝ) * σ ^ 2 * Q)
  let B := controlJB N * G + controlJH N * (n : ℝ) * H ^ 2 +
    controlJN N * σ ^ 2 * T.1
  have hnetwork : S.network = N := by
    simpa [S, FiniteInstance.network] using I.2.1
  have hLip : S.L = L := by
    simpa [S, FiniteInstance.lipschitz] using I.2.2.1
  have hgap : S.Δ = Δ := by
    simpa [S, FiniteInstance.gap] using I.2.2.2.1
  have hnoise : S.σ = σ := by
    simpa [S, FiniteInstance.noiseScale] using I.2.2.2.2.1
  have hheterogeneity : S.H = H := by
    simpa [S, FiniteInstance.heterogeneityScale] using I.2.2.2.2.2
  have hfinite : InFiniteHeterogeneityLayer S := by
    simpa [S] using I.1.finite_layer
  have hdim : dimensionlessStepsize S.L (s / L) = s := by
    rw [hLip]
    exact dimensionlessStepsize_div L s hL
  have hcontrol := corrected_center_uniform_control S hfinite (s / L)
    (div_pos hs hL) (by rw [hdim, hnetwork]; exact hsCenter) T
  rcases hcontrol with ⟨_, _, _, _, _, _, _, _, hVraw, hJraw, hGraw⟩
  have hQdevN := (hinterval 0 T.1 (Nat.zero_le _)).2
  have hQdev : |Q - t * q| ≤ Cenergy := by
    dsimp [Q, t, q]
    simpa [Nat.Ico_zero_eq_range] using hQdevN
  have hQupper : Q ≤ q * t + Cenergy := by
    simpa [mul_comm, add_comm] using
      (sub_le_iff_le_add).mp (le_of_abs_le hQdev)
  have hQ0 : 0 ≤ Q := by
    dsimp [Q, influenceEnergy]
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG0 : 0 ≤ G := by
    dsimp [G, correctedGradientEnergy, SOptLib.expectation]
    exact Finset.sum_nonneg fun u _ =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hV0 : 0 ≤ V := by
    dsimp [V, correctedDriftEnergy, SOptLib.expectation]
    exact Finset.sum_nonneg fun u _ =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hmPos : 0 < m := by
    dsimp [m]
    unfold periodicRiskBlockLength
    omega
  have hmTreal : (m : ℝ) ≤ t := by
    change (m : ℝ) ≤ (T.1 : ℝ)
    apply (hBlockLength T hTblock).trans
    have hTone : (1 : ℝ) ≤ T.1 := by exact_mod_cast T.2
    have hsqrtOne : (1 : ℝ) ≤ Real.sqrt T.1 := by
      simpa using (Real.sqrt_le_sqrt hTone)
    calc
      Real.sqrt T.1 = Real.sqrt T.1 * 1 := by ring
      _ ≤ Real.sqrt T.1 * Real.sqrt T.1 :=
        mul_le_mul_of_nonneg_left hsqrtOne (Real.sqrt_nonneg _)
      _ = (Real.sqrt T.1) ^ 2 := by ring
      _ = T.1 := Real.sq_sqrt (by positivity)
  have hmT : m ≤ T.1 := by
    change (m : ℝ) ≤ (T.1 : ℝ) at hmTreal
    exact_mod_cast hmTreal
  have hdescentRaw := periodic_regular_gain_descent_scalar
    S (s / L) (div_pos hs hL) T m h Cgain hmPos hmT hCgain
      (fun a b hab => by rw [hnetwork]; simpa [h] using (hinterval a b hab).1)
  rw [hLip, hgap, hnoise, hnetwork] at hdescentRaw
  have hdescent : (s / L) * ((h - Cgain / (m : ℝ)) * G -
        (n : ℝ) * (2 * Real.sqrt G * Real.sqrt W + W)) ≤
      Δ + (s / L) * (Real.sqrt G * Real.sqrt V) +
        (L * (s / L) ^ 2 / 2) *
          ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 +
        L * (s / L) ^ 2 * σ ^ 2 / 2 * Q := by
    simpa [G, V, Q, W] using hdescentRaw
  have hcost := fixed_instance_cost_le_corrected_energy_sharp
    N L Δ σ H hL I T sT hsCenter
  change I.1.cost (s / L) T ≤ t⁻¹ *
    (G + 2 * s * Real.sqrt G * Real.sqrt B + s ^ 2 * B) at hcost
  have hrThreeOne : (1 : ℝ) ≤ r ^ (3 : ℕ) := by
    exact one_le_pow₀ hrOne
  have hrThreeSix : r ^ (3 : ℕ) ≤ r ^ (6 : ℕ) :=
    pow_le_pow_right₀ hrOne (by omega)
  have htOne : (1 : ℝ) ≤ t := by rw [← hrSix]; exact one_le_pow₀ hrOne
  have hmThree : (m : ℝ) ≤ 3 * r := by
    change (periodicRiskBlockLength T : ℝ) ≤ 3 * r
    calc
      (periodicRiskBlockLength T : ℝ) ≤ r + 2 := hmr
      _ ≤ r + 2 * r := by
        simpa [add_comm] using
          (add_le_add_left
            (mul_le_mul_of_nonneg_left hrOne (show (0 : ℝ) ≤ 2 by norm_num)) r)
      _ = 3 * r := by ring
  have hsSqT : s ^ 2 * t = c ^ 2 := by
    dsimp [s]
    rw [← hrSix]
    field_simp [hr.ne']
  have hQcoarse : Q ≤ (q + Cenergy) * t := by
    calc
      Q ≤ q * t + Cenergy := hQupper
      _ ≤ q * t + Cenergy * t := by
        have := mul_le_mul_of_nonneg_left htOne hCenergy
        simpa using this
      _ = (q + Cenergy) * t := by ring
  have htermOne : 4 * Δ / ((s / L) * gainFloor N) =
      (4 * Δ * L / (c * gainFloor N)) * r ^ (3 : ℕ) := by
    dsimp [s]
    field_simp [hc.ne', hr.ne', hL.ne', hg.ne']
  have htermTwo :
      8 * controlRH N * (n : ℝ) * H ^ 2 / gainFloor N ^ 2 ≤
        (8 * |controlRH N| * (n : ℝ) * H ^ 2 /
          gainFloor N ^ 2) * r ^ (3 : ℕ) := by
    calc
      _ ≤ 8 * |controlRH N| * (n : ℝ) * H ^ 2 / gainFloor N ^ 2 := by
        gcongr
        exact le_abs_self _
      _ = (8 * |controlRH N| * (n : ℝ) * H ^ 2 /
          gainFloor N ^ 2) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrThreeOne (by positivity)
  have htermThree :
      8 * controlRN N * s ^ 2 * σ ^ 2 * t / gainFloor N ^ 2 ≤
        (8 * |controlRN N| * c ^ 2 * σ ^ 2 /
          gainFloor N ^ 2) * r ^ (3 : ℕ) := by
    calc
      _ ≤ 8 * |controlRN N| * s ^ 2 * σ ^ 2 * t /
          gainFloor N ^ 2 := by
        gcongr
        exact le_abs_self _
      _ = 8 * |controlRN N| * c ^ 2 * σ ^ 2 /
          gainFloor N ^ 2 := by rw [← hsSqT]; ring
      _ = (8 * |controlRN N| * c ^ 2 * σ ^ 2 /
          gainFloor N ^ 2) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrThreeOne (by positivity)
  have hsQ : s * Q ≤ c * (q + Cenergy) * r ^ (3 : ℕ) := by
    calc
      s * Q ≤ s * ((q + Cenergy) * t) :=
        mul_le_mul_of_nonneg_left hQcoarse hs.le
      _ = c * (q + Cenergy) * r ^ (3 : ℕ) := by
        dsimp [s]
        rw [← hrSix]
        field_simp [hr.ne']
  have htermFour :
      2 * L * (s / L) * σ ^ 2 / gainFloor N * Q ≤
        (2 * c * σ ^ 2 / gainFloor N * (q + Cenergy)) *
          r ^ (3 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hsQ
      (show 0 ≤ 2 * σ ^ 2 / gainFloor N by positivity)
    convert hscaled using 1 <;> field_simp [hL.ne', hg.ne'] <;> ring
  have hGraw' : G ≤
      4 * Δ / ((s / L) * gainFloor N) +
      8 * controlRH N * (n : ℝ) * H ^ 2 / gainFloor N ^ 2 +
      8 * controlRN N * s ^ 2 * σ ^ 2 * t / gainFloor N ^ 2 +
      2 * L * (s / L) * σ ^ 2 / gainFloor N * Q := by
    unfold correctedGradientUpperBound at hGraw
    rw [hnetwork, hLip, hgap, hnoise, hheterogeneity] at hGraw
    rw [dimensionlessStepsize_div L s hL] at hGraw
    simpa [G, Q, t] using hGraw
  have hGcoarse : G ≤ CG * r ^ (3 : ℕ) := by
    calc
      G ≤ _ := hGraw'
      _ ≤ (4 * Δ * L / (c * gainFloor N)) * r ^ (3 : ℕ) +
          (8 * |controlRH N| * (n : ℝ) * H ^ 2 /
            gainFloor N ^ 2) * r ^ (3 : ℕ) +
          (8 * |controlRN N| * c ^ 2 * σ ^ 2 /
            gainFloor N ^ 2) * r ^ (3 : ℕ) +
          (2 * c * σ ^ 2 / gainFloor N * (q + Cenergy)) *
            r ^ (3 : ℕ) := by
        rw [htermOne]
        exact add_le_add (add_le_add (add_le_add le_rfl htermTwo) htermThree)
          htermFour
      _ = CG * r ^ (3 : ℕ) := by dsimp [CG]; ring
  have hGt : G ≤ CG * t := by
    calc
      G ≤ CG * r ^ (3 : ℕ) := hGcoarse
      _ ≤ CG * r ^ (6 : ℕ) :=
        mul_le_mul_of_nonneg_left hrThreeSix hCG
      _ = CG * t := by rw [hrSix]
  have hVraw' : V ≤ controlRH N * (n : ℝ) * H ^ 2 +
      s ^ 2 * (controlRB N * G + controlRN N * σ ^ 2 * t) := by
    rw [hnetwork, hheterogeneity, hnoise, hdim] at hVraw
    simpa [V, G, t] using hVraw
  have hVabs : V ≤ |controlRH N| * (n : ℝ) * H ^ 2 +
      s ^ 2 * (|controlRB N| * G + |controlRN N| * σ ^ 2 * t) := by
    calc
      V ≤ _ := hVraw'
      _ ≤ _ := by
        gcongr
        · exact le_abs_self _
        · exact le_abs_self _
        · exact le_abs_self _
  have hVcoarse : V ≤ CV := by
    calc
      V ≤ _ := hVabs
      _ ≤ |controlRH N| * (n : ℝ) * H ^ 2 +
          s ^ 2 * (|controlRB N| * (CG * t) +
            |controlRN N| * σ ^ 2 * t) := by gcongr
      _ = |controlRH N| * (n : ℝ) * H ^ 2 +
          c ^ 2 * (|controlRB N| * CG + |controlRN N| * σ ^ 2) := by
        rw [← hsSqT]
        ring
      _ = CV := by rfl
  have hVsqrt : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV0
  have hGsqrt : (Real.sqrt G) ^ 2 = G := Real.sq_sqrt hG0
  have hdirection :
      ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 ≤
        KD * r ^ (3 : ℕ) := by
    calc
      ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 ≤
          ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 +
            ((n : ℝ) * Real.sqrt G - Real.sqrt V) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = 2 * ((n : ℝ) * Real.sqrt G) ^ 2 +
            2 * (Real.sqrt V) ^ 2 := by ring
      _ = 2 * (n : ℝ) ^ 2 * G + 2 * V := by
        rw [mul_pow, hGsqrt, hVsqrt]
        ring
      _ ≤ 2 * (n : ℝ) ^ 2 * (CG * r ^ (3 : ℕ)) + 2 * CV := by
        gcongr
      _ ≤ 2 * (n : ℝ) ^ 2 * (CG * r ^ (3 : ℕ)) +
          2 * CV * r ^ (3 : ℕ) := by
        exact add_le_add_right (by
          simpa using
            (mul_le_mul_of_nonneg_left hrThreeOne
              (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hCV))) _
      _ = KD * r ^ (3 : ℕ) := by dsimp [KD]; ring
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmSq : (m : ℝ) ^ 2 ≤ 9 * r ^ 2 := by
    have hsquare := (sq_le_sq₀ hm0 (by positivity : 0 ≤ 3 * r)).2 hmThree
    calc
      (m : ℝ) ^ 2 ≤ (3 * r) ^ 2 := hsquare
      _ = 9 * r ^ 2 := by ring
  have hsSqRfive : s ^ 2 * r ^ (5 : ℕ) ≤ c ^ 2 * r := by
    have hp : r ^ (5 : ℕ) ≤ r ^ (7 : ℕ) :=
      pow_le_pow_right₀ hrOne (by omega)
    calc
      s ^ 2 * r ^ (5 : ℕ) ≤ s ^ 2 * r ^ (7 : ℕ) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg s)
      _ = (s ^ 2 * r ^ (6 : ℕ)) * r := by ring
      _ = c ^ 2 * r := by rw [show s ^ 2 * r ^ (6 : ℕ) = c ^ 2 by
        rw [hrSix]; exact hsSqT]
  have hsSqRtwo : s ^ 2 * r ^ (2 : ℕ) ≤ c ^ 2 * r := by
    have hp : r ^ (2 : ℕ) ≤ r ^ (7 : ℕ) :=
      pow_le_pow_right₀ hrOne (by omega)
    calc
      s ^ 2 * r ^ (2 : ℕ) ≤ s ^ 2 * r ^ (7 : ℕ) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg s)
      _ = (s ^ 2 * r ^ (6 : ℕ)) * r := by ring
      _ = c ^ 2 * r := by rw [show s ^ 2 * r ^ (6 : ℕ) = c ^ 2 by
        rw [hrSix]; exact hsSqT]
  have hWA : s ^ 2 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G) ≤
      9 * c ^ 2 * (n : ℝ) ^ 2 * CG * r := by
    calc
      _ ≤ s ^ 2 * ((9 * r ^ 2) * (n : ℝ) ^ 2 *
          (CG * r ^ (3 : ℕ))) := by gcongr
      _ = 9 * (n : ℝ) ^ 2 * CG * (s ^ 2 * r ^ (5 : ℕ)) := by ring
      _ ≤ 9 * (n : ℝ) ^ 2 * CG * (c ^ 2 * r) := by gcongr
      _ = _ := by ring
  have hWB : s ^ 2 * ((m : ℝ) ^ 2 * V) ≤
      9 * c ^ 2 * CV * r := by
    calc
      _ ≤ s ^ 2 * ((9 * r ^ 2) * CV) := by gcongr
      _ = 9 * CV * (s ^ 2 * r ^ (2 : ℕ)) := by ring
      _ ≤ 9 * CV * (c ^ 2 * r) := by gcongr
      _ = _ := by ring
  have hWC : s ^ 2 * ((m : ℝ) * σ ^ 2 * Q) ≤
      3 * c ^ 2 * σ ^ 2 * (q + Cenergy) * r := by
    calc
      _ ≤ s ^ 2 * ((3 * r) * σ ^ 2 * ((q + Cenergy) * t)) := by gcongr
      _ = 3 * σ ^ 2 * (q + Cenergy) * r * (s ^ 2 * t) := by ring
      _ = _ := by rw [hsSqT]; ring
  have hWform : W = 12 * s ^ 2 *
      ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G +
        (m : ℝ) ^ 2 * V + (m : ℝ) * σ ^ 2 * Q) := by
    dsimp [W]
    field_simp [hL.ne']
  have hWcoarse : W ≤ CW * r := by
    rw [hWform, mul_add, mul_add]
    calc
      12 * s ^ 2 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G) +
          12 * s ^ 2 * ((m : ℝ) ^ 2 * V) +
          12 * s ^ 2 * ((m : ℝ) * σ ^ 2 * Q) =
        12 * (s ^ 2 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 * G)) +
          12 * (s ^ 2 * ((m : ℝ) ^ 2 * V)) +
          12 * (s ^ 2 * ((m : ℝ) * σ ^ 2 * Q)) := by ring
      _ ≤
        12 * (9 * c ^ 2 * (n : ℝ) ^ 2 * CG * r) +
          12 * (9 * c ^ 2 * CV * r) +
          12 * (3 * c ^ 2 * σ ^ 2 * (q + Cenergy) * r) := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left hWA (by norm_num))
            (mul_le_mul_of_nonneg_left hWB (by norm_num)))
          (mul_le_mul_of_nonneg_left hWC (by norm_num))
      _ = CW * r := by dsimp [CW]; ring
  have hW0 : 0 ≤ W := by
    rw [hWform]
    positivity
  have hrSq : r ≤ r ^ (2 : ℕ) := by
    calc
      r = r * 1 := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_left hrOne hr.le
      _ = r ^ (2 : ℕ) := by ring
  have hGW : G * W ≤ (CG * CW) * r ^ (4 : ℕ) := by
    calc
      G * W ≤ (CG * r ^ (3 : ℕ)) * (CW * r) :=
        mul_le_mul hGcoarse hWcoarse hW0
          (mul_nonneg hCG (pow_nonneg hr.le _))
      _ = (CG * CW) * r ^ (4 : ℕ) := by ring
  have hsqrtGW : Real.sqrt G * Real.sqrt W ≤
      Real.sqrt (CG * CW) * r ^ (2 : ℕ) := by
    have hsqrt := Real.sqrt_le_sqrt hGW
    rw [Real.sqrt_mul hG0] at hsqrt
    rw [Real.sqrt_mul (mul_nonneg hCG hCW)] at hsqrt
    have hr4 : r ^ (4 : ℕ) = (r ^ (2 : ℕ)) ^ 2 := by ring
    rw [hr4, Real.sqrt_sq (sq_nonneg r)] at hsqrt
    exact hsqrt
  have hE : 2 * Real.sqrt G * Real.sqrt W + W ≤
      KE * r ^ (2 : ℕ) := by
    calc
      _ = 2 * (Real.sqrt G * Real.sqrt W) + W := by ring
      _ ≤ 2 * (Real.sqrt (CG * CW) * r ^ (2 : ℕ)) + CW * r :=
        add_le_add (mul_le_mul_of_nonneg_left hsqrtGW (by norm_num)) hWcoarse
      _ ≤ 2 * (Real.sqrt (CG * CW) * r ^ (2 : ℕ)) +
          CW * r ^ (2 : ℕ) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hrSq hCW) _
      _ = KE * r ^ (2 : ℕ) := by dsimp [KE]; ring
  have hGVprod : G * V ≤ (CG * CV) * r ^ (4 : ℕ) := by
    calc
      G * V ≤ (CG * r ^ (3 : ℕ)) * CV :=
        mul_le_mul hGcoarse hVcoarse hV0
          (mul_nonneg hCG (pow_nonneg hr.le _))
      _ ≤ (CG * r ^ (4 : ℕ)) * CV :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hrOne (by omega)) hCG) hCV
      _ = (CG * CV) * r ^ (4 : ℕ) := by ring
  have hGV : Real.sqrt G * Real.sqrt V ≤
      Real.sqrt (CG * CV) * r ^ (2 : ℕ) := by
    have hsqrt := Real.sqrt_le_sqrt hGVprod
    rw [Real.sqrt_mul hG0] at hsqrt
    rw [Real.sqrt_mul (mul_nonneg hCG hCV)] at hsqrt
    have hr4 : r ^ (4 : ℕ) = (r ^ (2 : ℕ)) ^ 2 := by ring
    rw [hr4, Real.sqrt_sq (sq_nonneg r)] at hsqrt
    exact hsqrt
  have hJ0 : 0 ≤ J := by
    dsimp [J, correctedCenterOffsetEnergy, SOptLib.expectation]
    exact Finset.sum_nonneg fun u _ =>
      MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hJ : J ≤ (s / L) ^ 2 * B := by
    rw [hnetwork, hheterogeneity, hnoise] at hJraw
    simpa [J, B, G, t] using hJraw
  have hB0 : 0 ≤ B := by
    have halphaSq : 0 < (s / L) ^ 2 := sq_pos_of_pos (div_pos hs hL)
    exact nonneg_of_mul_nonneg_right (hJ0.trans hJ) halphaSq
  have hBupper : B ≤ CB * t := by
    calc
      B ≤ |controlJB N| * G + |controlJH N| * (n : ℝ) * H ^ 2 +
          |controlJN N| * σ ^ 2 * t := by
        dsimp [B]
        gcongr <;> exact le_abs_self _
      _ ≤ |controlJB N| * (CG * t) +
          |controlJH N| * (n : ℝ) * H ^ 2 * t +
          |controlJN N| * σ ^ 2 * t := by
        apply add_le_add
        · exact add_le_add
            (mul_le_mul_of_nonneg_left hGt (abs_nonneg _)) (by
              simpa using
                (mul_le_mul_of_nonneg_left htOne
                  (show 0 ≤ |controlJH N| * (n : ℝ) * H ^ 2 by positivity)))
        · exact le_rfl
      _ = CB * t := by dsimp [CB]; ring
  have hGfour : G ≤ CG * r ^ (4 : ℕ) := by
    exact hGcoarse.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hrOne (by omega)) hCG)
  have hGB : G * B ≤ (CG * CB) * r ^ (10 : ℕ) := by
    calc
      G * B ≤ (CG * r ^ (4 : ℕ)) * (CB * t) :=
        mul_le_mul hGfour hBupper hB0
          (mul_nonneg hCG (pow_nonneg hr.le _))
      _ = (CG * CB) * r ^ (10 : ℕ) := by rw [← hrSix]; ring
  have hsqrtGB : Real.sqrt G * Real.sqrt B ≤
      Real.sqrt (CG * CB) * r ^ (5 : ℕ) := by
    have hsqrt := Real.sqrt_le_sqrt hGB
    rw [Real.sqrt_mul hG0] at hsqrt
    rw [Real.sqrt_mul (mul_nonneg hCG hCB)] at hsqrt
    have hr10 : r ^ (10 : ℕ) = (r ^ (5 : ℕ)) ^ 2 := by ring
    rw [hr10, Real.sqrt_sq (by positivity : 0 ≤ r ^ (5 : ℕ))] at hsqrt
    exact hsqrt
  have hsRfive : s * r ^ (5 : ℕ) = c * r ^ (2 : ℕ) := by
    dsimp [s]
    field_simp [hr.ne']
  have hOutput : 2 * s * Real.sqrt G * Real.sqrt B + s ^ 2 * B ≤
      KO * r ^ (2 : ℕ) := by
    calc
      _ = (2 * s) * (Real.sqrt G * Real.sqrt B) + s ^ 2 * B := by ring
      _ ≤ (2 * s) * (Real.sqrt (CG * CB) * r ^ (5 : ℕ)) +
          s ^ 2 * (CB * t) := add_le_add
        (mul_le_mul_of_nonneg_left hsqrtGB (by positivity))
        (mul_le_mul_of_nonneg_left hBupper (sq_nonneg s))
      _ = 2 * s * (Real.sqrt (CG * CB) * r ^ (5 : ℕ)) +
          s ^ 2 * (CB * t) := by ring
      _ = 2 * c * Real.sqrt (CG * CB) * r ^ (2 : ℕ) + c ^ 2 * CB := by
        rw [show 2 * s * (Real.sqrt (CG * CB) * r ^ (5 : ℕ)) =
          2 * Real.sqrt (CG * CB) * (s * r ^ (5 : ℕ)) by ring,
          hsRfive, ← hsSqT]
        ring
      _ ≤ 2 * c * Real.sqrt (CG * CB) * r ^ (2 : ℕ) +
          c ^ 2 * CB * r ^ (2 : ℕ) := by
        exact add_le_add_right (by
          simpa using
            (mul_le_mul_of_nonneg_left (one_le_pow₀ hrOne)
              (mul_nonneg (sq_nonneg c) hCB))) _
      _ = KO * r ^ (2 : ℕ) := by dsimp [KO]; ring
  have hdesc : (h - Cgain / (m : ℝ)) * G -
        (n : ℝ) * (2 * Real.sqrt G * Real.sqrt W + W) ≤
      Δ * L / s + Real.sqrt G * Real.sqrt V +
        s / 2 * ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 +
        s * σ ^ 2 / 2 * Q := by
    apply le_of_mul_le_mul_left ?_ (div_pos hs hL)
    convert hdescent using 1 <;> field_simp [hs.ne', hL.ne'] <;> ring
  have hgainError : Cgain / (m : ℝ) * G ≤
      (Cgain * CG) * r ^ (2 : ℕ) := by
    have hmR : r ≤ (m : ℝ) := by simpa [m] using hrm
    have hfrac : Cgain / (m : ℝ) ≤ Cgain / r := by
      exact div_le_div₀ hCgain le_rfl hr hmR
    calc
      Cgain / (m : ℝ) * G ≤ (Cgain / r) * (CG * r ^ (3 : ℕ)) :=
        mul_le_mul hfrac hGcoarse hG0 (div_nonneg hCgain hr.le)
      _ = (Cgain * CG) * r ^ (2 : ℕ) := by
        field_simp [hr.ne']
  have hsRthree : s * r ^ (3 : ℕ) = c := by
    dsimp [s]
    field_simp [hr.ne']
  have hdirectionTerm : s / 2 *
      ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 ≤
        (c * KD / 2) * r ^ (2 : ℕ) := by
    calc
      _ ≤ s / 2 * (KD * r ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left hdirection (by positivity)
      _ = c * KD / 2 := by rw [show s / 2 * (KD * r ^ (3 : ℕ)) =
        KD / 2 * (s * r ^ (3 : ℕ)) by ring, hsRthree]; ring
      _ ≤ (c * KD / 2) * r ^ (2 : ℕ) := by
        simpa using
          (mul_le_mul_of_nonneg_left (one_le_pow₀ hrOne)
            (show 0 ≤ c * KD / 2 by positivity))
  have hsLeC : s ≤ c := by
    calc
      s = c / r ^ (3 : ℕ) := rfl
      _ ≤ c / 1 := div_le_div₀ hc.le le_rfl (by norm_num) hrThreeOne
      _ = c := by ring
  have hQterm : s * σ ^ 2 / 2 * Q ≤
      s * σ ^ 2 * q * t / 2 +
        (c * σ ^ 2 * Cenergy / 2) * r ^ (2 : ℕ) := by
    calc
      _ ≤ s * σ ^ 2 / 2 * (q * t + Cenergy) :=
        mul_le_mul_of_nonneg_left hQupper (by positivity)
      _ = s * σ ^ 2 * q * t / 2 + s * σ ^ 2 * Cenergy / 2 := by ring
      _ ≤ s * σ ^ 2 * q * t / 2 + c * σ ^ 2 * Cenergy / 2 := by
        gcongr
      _ ≤ s * σ ^ 2 * q * t / 2 +
          (c * σ ^ 2 * Cenergy / 2) * r ^ (2 : ℕ) := by
        exact add_le_add_right (by
          simpa using
            (mul_le_mul_of_nonneg_left (one_le_pow₀ hrOne)
              (show 0 ≤ c * σ ^ 2 * Cenergy / 2 by positivity))) _
  have hGsharp : h * G ≤
      (Δ * L / s + s * σ ^ 2 * q * t / 2) +
        KR * r ^ (2 : ℕ) := by
    calc
      h * G = ((h - Cgain / (m : ℝ)) * G -
          (n : ℝ) * (2 * Real.sqrt G * Real.sqrt W + W)) +
          (n : ℝ) * (2 * Real.sqrt G * Real.sqrt W + W) +
          Cgain / (m : ℝ) * G := by ring
      _ ≤ (Δ * L / s + Real.sqrt G * Real.sqrt V +
          s / 2 * ((n : ℝ) * Real.sqrt G + Real.sqrt V) ^ 2 +
          s * σ ^ 2 / 2 * Q) +
          (n : ℝ) * (KE * r ^ (2 : ℕ)) +
          (Cgain * CG) * r ^ (2 : ℕ) := by
        gcongr
      _ ≤ (Δ * L / s +
          Real.sqrt (CG * CV) * r ^ (2 : ℕ) +
          (c * KD / 2) * r ^ (2 : ℕ) +
          (s * σ ^ 2 * q * t / 2 +
            (c * σ ^ 2 * Cenergy / 2) * r ^ (2 : ℕ))) +
          (n : ℝ) * (KE * r ^ (2 : ℕ)) +
          (Cgain * CG) * r ^ (2 : ℕ) := by
        gcongr
      _ = (Δ * L / s + s * σ ^ 2 * q * t / 2) +
          KR * r ^ (2 : ℕ) := by dsimp [KR]; ring
  have hh' : 0 < h := by simpa [h] using hh
  have hGfinal : G ≤
      (Δ * L / s + s * σ ^ 2 * q * t / 2) / h +
        (KR / h) * r ^ (2 : ℕ) := by
    apply le_of_mul_le_mul_left ?_ hh'
    convert hGsharp using 1 <;> field_simp [hh'.ne'] <;> ring
  have hCostPair : I.1.cost (s / L) T ≤
      (Δ * L / s + s * σ ^ 2 * q * t / 2) / (h * t) +
        Kup / r ^ (4 : ℕ) := by
    calc
      I.1.cost (s / L) T ≤ t⁻¹ *
          (G + 2 * s * Real.sqrt G * Real.sqrt B + s ^ 2 * B) := hcost
      _ = t⁻¹ * (G +
          (2 * s * Real.sqrt G * Real.sqrt B + s ^ 2 * B)) := by ring
      _ ≤ t⁻¹ * (((Δ * L / s + s * σ ^ 2 * q * t / 2) / h +
          (KR / h) * r ^ (2 : ℕ)) + KO * r ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left (add_le_add hGfinal hOutput)
          (inv_nonneg.mpr ht.le)
      _ = (Δ * L / s + s * σ ^ 2 * q * t / 2) / (h * t) +
          Kup / r ^ (4 : ℕ) := by
        rw [← hrSix]
        dsimp [Kup]
        field_simp [hh'.ne', hr.ne']
        ring
  have hLead :
      (Δ * L / s + s * σ ^ 2 * q * t / 2) / (h * t) =
        σ * Real.sqrt (2 * ADelta L Δ * q / (h ^ 2 * t)) := by
    rw [hsFormula]
    exact periodic_balanced_leading_pair_eq
      L Δ σ q h t hL hΔ hσ hq hh' ht
  calc
    I.1.cost (sT.1 / L) T = I.1.cost (s / L) T := rfl
    _ ≤ (Δ * L / s + s * σ ^ 2 * q * t / 2) / (h * t) +
        Kup / r ^ (4 : ℕ) := hCostPair
    _ = σ * Real.sqrt (2 * ADelta L Δ * q / (h ^ 2 * t)) +
        Kup / Real.rpow t ((2 : ℝ) / 3) := by rw [hLead, hrFour]
    _ = σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1)) +
        Kup / Real.rpow T.1 ((2 : ℝ) / 3) := by rfl

/-- Equations (61)--(64): periodic comparator expansion, effective-node
limit, and the distinct `T⁻¹` lower and `T⁻²ᐟ³` upper risk remainders.
Book `#/key_lemmas/8/statement_math`:
“若网络周期为 `p` ... `\sigma\sqrt{{2L\Delta q\over h^2T}}-O(T^{-1})\le R_T`”. -/
theorem periodic_reduction
    (N : NetworkSetup n) (p : PositiveHorizon) (hp : IsPeriodicNetwork N p)
    (L Δ σ H : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hH : 0 ≤ H) :
    0 < periodicGainMean N p hp ∧
    periodicGainMean N p hp ^ 2 / n ≤ periodicInfluenceMean N p ∧
    ((p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1, ∑ i, influenceRow N r i =
      periodicGainMean N p hp) ∧
    (∀ i, (p.1 : ℝ)⁻¹ * ∑ r ∈ Finset.range p.1, influenceRow N r i =
      periodicGainMean N p hp / n) ∧
    (∃ KB : ℝ, 0 ≤ KB ∧ ∃ TB : ℕ, ∀ T : PositiveHorizon, TB ≤ T.1 →
      |comparator N L Δ σ T -
        σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
          (periodicGainMean N p hp ^ 2 * T.1))| ≤ KB / T.1) ∧
    (∀ ε : ℝ, 0 < ε → ∃ Tε : ℕ, ∀ T : PositiveHorizon, Tε ≤ T.1 →
      ∀ hB : 0 < comparator N L Δ σ T,
        |effectiveNodeCount N L Δ σ ⟨T, hB⟩ -
          periodicGainMean N p hp ^ 2 / periodicInfluenceMean N p| < ε) ∧
    ∃ Klo Kup : ℝ, 0 ≤ Klo ∧ 0 ≤ Kup ∧ ∃ Trisk : ℕ,
      ∀ T : PositiveHorizon, Trisk ≤ T.1 →
        (periodicRiskBlockLength T : ℝ) ≤ Real.sqrt T.1 ∧
        ENNReal.ofReal
            (σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
              (periodicGainMean N p hp ^ 2 * T.1)) - Klo / T.1) ≤
          minimaxRisk (fixedInstanceClass N L Δ σ H) T ∧
        minimaxRisk (fixedInstanceClass N L Δ σ H) T ≤
          ENNReal.ofReal
            (σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
              (periodicGainMean N p hp ^ 2 * T.1)) +
              Kup / Real.rpow T.1 (2 / 3)) := by
  obtain ⟨hh, hhq, hsum, hcoord⟩ := periodic_phase_coefficients N p hp
  obtain ⟨Cgain, Cenergy, hCgain, hCenergy, hinterval⟩ :=
    periodic_interval_deviation_bounds N p hp
  obtain ⟨Cwindow, hCwindow, hwindowBudget⟩ :=
    periodic_gain_budget_interval_length_le N p hp
  obtain ⟨Cceil, hCceil, hwindowUpper⟩ :=
    periodic_windowLength_le_ceil N p hp
  obtain ⟨Cfloor, hCfloor, hwindowLower⟩ :=
    periodic_length_le_windowLength_of_budget N p hp
  obtain ⟨KAt, CfloorAt, hKAt, hCfloorAt, hAtExpansion⟩ :=
    periodic_comparatorAt_expansion_interior N p hp L Δ σ hL hΔ
  obtain ⟨Tloc, hlocalized⟩ :=
    localized_near_comparator_with_center_cap N L Δ σ hL hΔ hσ
  obtain ⟨KB, hKB, TB, hEquation62⟩ :=
    periodic_comparator_equation62 N p hp L Δ σ hL hΔ hσ hh hhq
      KAt CfloorAt hKAt hCfloorAt hAtExpansion Tloc hlocalized
  refine ⟨hh, hhq, hsum, hcoord, ?_⟩
  refine ⟨⟨KB, hKB, TB, hEquation62⟩, ?_⟩
  refine ⟨periodic_effective_node_limit_of_equation62
    N p hp L Δ σ hL hΔ hσ hh hhq KB hKB TB hEquation62, ?_⟩
  have hg : 0 < gainFloor N :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  let M₀ : ℝ :=
    (ADelta L Δ + σ ^ 2 * influenceRowBound N ^ 2 / 2) / gainFloor N
  have hM₀ : 0 < M₀ := by
    dsimp [M₀]
    apply div_pos
    · exact add_pos_of_pos_of_nonneg
        (by unfold ADelta; positivity) (by positivity)
    · exact hg
  let cQ : ℝ := ADelta L Δ / (8 * (n : ℝ) * M₀)
  let CQ : ℝ := 256 * (n : ℝ) ^ 2 * M₀ /
    (σ ^ 2 * gainFloor N ^ 2)
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
  have hcQ : 0 < cQ := by
    dsimp [cQ]
    exact div_pos (by unfold ADelta; positivity)
      (mul_pos (mul_pos (by norm_num) hn) hM₀)
  have hCQ : 0 < CQ := by
    dsimp [CQ]
    exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hn)) hM₀)
      (mul_pos (sq_pos_of_pos hσ) (sq_pos_of_pos hg))
  obtain ⟨Kact, hKact, Tact, hActualBand⟩ :=
    periodic_actual_quadratic_band_expansion N p hp L Δ σ H
      hL hΔ hσ hH Cenergy hCenergy
      (fun a b hab => (hinterval a b hab).2) cQ CQ hcQ hCQ
  obtain ⟨Klo, hKlo, Tlo, hSharpResponse⟩ :=
    periodic_exact_all_stepsizes_response_lower
      N p hp L Δ σ H M₀ KB Kact hL hΔ hσ hH hM₀ rfl hKB hKact
      TB Tact hEquation62 (by
        intro T hT alpha halpha hslow hshigh
        exact hActualBand T hT alpha halpha
          (by simpa [cQ] using hslow) (by simpa [CQ] using hshigh))
  have hLowerMinimax : ∀ T : PositiveHorizon, Tlo ≤ T.1 →
      ENNReal.ofReal
          (σ * Real.sqrt (2 * ADelta L Δ * periodicInfluenceMean N p /
            (periodicGainMean N p hp ^ 2 * T.1)) - Klo / T.1) ≤
        minimaxRisk (fixedInstanceClass N L Δ σ H) T := by
    intro T hT
    apply minimaxRisk_lower_of_all_stepsizes
    intro alpha halpha
    obtain ⟨I, hI, hcost⟩ := hSharpResponse T hT alpha halpha
    exact ⟨I, hI, ENNReal.ofReal_le_ofReal hcost⟩
  obtain ⟨Tblock, hBlockLength⟩ :=
    periodic_risk_block_length_le_sqrt_eventually
  obtain ⟨Kup, hKup, Tup, hUpperFixed⟩ :=
    periodic_equation63_uniform_fixed_instance_upper
      N p hp L Δ σ H hL hΔ hσ hH hh hhq Cgain Cenergy
        hCgain hCenergy hinterval Tblock hBlockLength
  refine ⟨Klo, Kup, hKlo, hKup, max Tlo (max Tblock Tup), ?_⟩
  intro T hT
  have hTlo : Tlo ≤ T.1 := by omega
  have hTblock : Tblock ≤ T.1 := by omega
  have hTup : Tup ≤ T.1 := by omega
  refine ⟨hBlockLength T hTblock, hLowerMinimax T hTlo, ?_⟩
  obtain ⟨sT, _hsFormula, hcost⟩ := hUpperFixed T hTup
  unfold minimaxRisk
  refine iInf_le_of_le
    (⟨sT.1 / L, div_pos sT.2.1 hL⟩ : {a : ℝ // 0 < a}) ?_
  refine iSup_le fun I => ?_
  exact ENNReal.ofReal_le_ofReal (hcost I)

/-- The deterministic homogeneous quadratic is a legal member of the fixed
class, and its time-zero gradient supplies the exact lower endpoint in (65). -/
private theorem deterministic_quadratic_time_zero_witness
    (N : NetworkSetup n) (L Δ σ H : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hH : 0 ≤ H)
    (T : PositiveHorizon) :
    ∀ α : ℝ, 0 < α →
      ∃ I : fixedInstanceClass N L Δ σ H,
        2 * ADelta L Δ / (T.1 : ℝ) ≤ I.1.cost α T := by
  classical
  obtain ⟨hobjective, hobjNonneg, hobjInf, hobjGap, hobjGrad⟩ :=
    actualQuadraticObjective_spec L Δ hL hΔ
  let F : Point 1 → ℝ := fun x => (L / 2) * ‖x‖ ^ 2
  let x0 : Point 1 :=
    WithLp.toLp 2 (fun _ : Fin 1 => Real.sqrt (2 * Δ / L))
  let noise : ℕ → Unit → NodeTable n 1 := fun _ _ _ => 0
  have hhistory (t : ℕ) :
      preSamplingHistoryOf noise t ≤ PUnit.instMeasurableSpace := by
    unfold preSamplingHistoryOf
    refine iSup_le fun j => iSup_le fun hj => ?_
    rw [← measurable_iff_comap_le]
    exact measurable_const
  let S : Setup n 1 Unit :=
    { network := N
      hd := by norm_num
      L := L
      Δ := Δ
      σ := σ
      H := H
      hL := hL
      hΔ := hΔ
      hσ := hσ
      hH := hH
      localObjective := fun _ => F
      initialPoint := x0
      noise := noise
      probability := escapedBinderProbability
      is_probability := escapedBinderProbability_isProbability
      local_smooth := fun _ => hobjective
      average_lower_bounded := by
        refine ⟨0, ?_⟩
        rintro _ ⟨z, rfl⟩
        simpa [F, Nat.ne_of_gt N.hn] using hobjNonneg z
      exact_initial_gap := by
        simpa [F, x0, Nat.ne_of_gt N.hn] using hobjGap
      noise_centered := by
        intro t i
        exact diracUnitConditionalExpectationEqSelf
          (preSamplingHistoryOf noise t) (hhistory t) _
      noise_second_moment := by
        intro t i
        have hz := diracUnitConditionalSecondMomentZero
          (E := Point 1) (preSamplingHistoryOf noise t) (hhistory t)
        refine ⟨hz.1, ?_⟩
        filter_upwards [hz.2] with omega homega
        exact homega.trans (sq_nonneg σ)
      node_conditional_independence := by
        intro t
        exact diracUnitNodeConditionallyIndependentZero _ (hhistory t) }
  have haverage : averageObjective S = F := by
    funext z
    simp [averageObjective, S, Nat.ne_of_gt N.hn]
  have hheterogeneity : initialHeterogeneitySq S = 0 := by
    unfold initialHeterogeneitySq
    simp only [S, haverage, sub_self, norm_zero, zero_pow, Nat.ofNat_pos,
      Finset.sum_const_zero, mul_zero]
    simp
  have hfinite : InFiniteHeterogeneityLayer S := by
    unfold InFiniteHeterogeneityLayer
    rw [hheterogeneity]
    exact sq_nonneg H
  let I : FiniteInstance n :=
    { d := 1
      Ω := Unit
      setup := S
      finite_layer := hfinite }
  have hfixed : I ∈ fixedInstanceClass N L Δ σ H := by
    simp [fixedInstanceClass, I, S, FiniteInstance.network,
      FiniteInstance.lipschitz, FiniteInstance.gap, FiniteInstance.noiseScale,
      FiniteInstance.heterogeneityScale]
  have hx0norm : ‖x0‖ ^ 2 = 2 * Δ / L := by
    have harg : 0 ≤ 2 * Δ / L := by positivity
    dsimp [x0]
    rw [PiLp.norm_eq_of_L2]
    simp [Real.sq_sqrt harg]
  have hzero : ∀ α : ℝ,
      SOptLib.expectation S.probability (stationarityIntegrand S α 0) =
        2 * ADelta L Δ := by
    intro α
    have hmean : arithmeticMean S () α 0 = x0 := by
      simp only [arithmeticMean, primal_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]
      change (n : ℝ)⁻¹ • (n • x0) = x0
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      rw [smul_smul]
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt N.hn)
      rw [inv_mul_cancel₀ hn0, one_smul]
    have hgrad : gradient (averageObjective S) x0 = L • x0 := by
      rw [haverage]
      exact hobjGrad x0
    unfold SOptLib.expectation
    rw [show S.probability = Measure.dirac () by rfl]
    rw [MeasureTheory.integral_dirac]
    simp only [stationarityIntegrand, hmean, hgrad, norm_smul,
      Real.norm_eq_abs, abs_of_pos hL, mul_pow]
    rw [hx0norm]
    unfold ADelta
    field_simp [hL.ne']
  intro α hα
  refine ⟨⟨I, hfixed⟩, ?_⟩
  have hsum : 2 * ADelta L Δ ≤
      ∑ t ∈ Finset.range T.1,
        SOptLib.expectation S.probability (stationarityIntegrand S α t) := by
    rw [← hzero α]
    let f : ℕ → ℝ := fun t =>
      SOptLib.expectation S.probability (stationarityIntegrand S α t)
    change f 0 ≤ ∑ t ∈ Finset.range T.1, f t
    exact Finset.single_le_sum (s := Finset.range T.1) (a := 0)
      (fun t ht => by
        dsimp [f, SOptLib.expectation]
        exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
      (by simp [T.2])
  change 2 * ADelta L Δ / (T.1 : ℝ) ≤
    (T.1 : ℝ)⁻¹ * ∑ t ∈ Finset.range T.1,
      SOptLib.expectation S.probability (stationarityIntegrand S α t)
  calc
    2 * ADelta L Δ / (T.1 : ℝ) =
        (T.1 : ℝ)⁻¹ * (2 * ADelta L Δ) := by ring
    _ ≤ (T.1 : ℝ)⁻¹ * ∑ t ∈ Finset.range T.1,
        SOptLib.expectation S.probability (stationarityIntegrand S α t) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The feedback branch of the source cap is stronger than the auxiliary
`1/(64n)` domain used by the equation-(17) transfer theorem. -/
private theorem correctedCenterStepCap_pos_and_admissible
    (N : NetworkSetup n) :
    0 < correctedCenterStepCap N ∧
      correctedCenterStepCap N ≤ 1 / (64 * (n : ℝ)) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hg : 0 < gainFloor N :=
    (mul_pos hn (by
      unfold mixingMinorization
      split_ifs
      · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
      · norm_num)).trans_le (gainFloor_ge_n_mul_mixingMinorization N)
  have hrate : mixingRate N < 1 := mixingRate_lt_one N
  have hrow : 0 < rowMixingConstant N := by
    unfold rowMixingConstant
    exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hn))
      (blockContraction_pos N)
  have hdisagreement_pos : 0 < disagreementKernel N := by
    unfold disagreementKernel
    exact div_pos (sq_pos_of_pos hrow) (sq_pos_of_pos (sub_pos.mpr hrate))
  have hcolumn : 0 < columnMixingConstant N := by
    unfold columnMixingConstant
    exact div_pos (Real.sqrt_pos.2 hn) (blockContraction_pos N)
  have hincrement : 0 < incrementKernel N := by
    unfold incrementKernel
    positivity
  have htrackerIncrement : 0 < trackerIncrementKernel N := by
    unfold trackerIncrementKernel
    exact div_pos
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hcolumn))
          (sq_pos_of_pos (by positivity : 0 < 1 + Real.sqrt n)))
        hincrement)
      (sq_pos_of_pos (sub_pos.mpr hrate))
  have hcontrolRB : 0 < controlRB N := by
    unfold controlRB controlKa controlMB
    have hcoef : 0 < (3 * (n : ℝ) + 6 * (n : ℝ) ^ 2) := by positivity
    positivity
  have hcap_pos : 0 < correctedCenterStepCap N := by
    unfold correctedCenterStepCap
    simp only [lt_min_iff]
    refine ⟨by norm_num, by positivity, ?_, ?_, ?_⟩
    · exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))
    · exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))
    · exact div_pos hg (Real.sqrt_pos.2 (by positivity))
  refine ⟨hcap_pos, ?_⟩
  have hmu : 0 ≤ mixingMinorization N := by
    unfold mixingMinorization
    split_ifs
    · exact (pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _).le
    · norm_num
  have hdelta_le : blockContraction N ≤ 1 := by
    rw [blockContraction, max_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hrow_lower : 2 * Real.sqrt n ≤ rowMixingConstant N := by
    unfold rowMixingConstant
    apply (le_div_iff₀ (blockContraction_pos N)).2
    have hroot : 0 ≤ 2 * Real.sqrt n := by positivity
    nlinarith
  have hrow_sq : 4 * (n : ℝ) ≤ rowMixingConstant N ^ 2 := by
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ 2 * Real.sqrt n)
      hrow.le).2 hrow_lower
    rw [mul_pow, Real.sq_sqrt hn.le] at hs
    nlinarith
  have hden_pos : 0 < 1 - mixingRate N := sub_pos.mpr hrate
  have hden_le : 1 - mixingRate N ≤ 1 := by
    nlinarith [mixingRate_nonneg N]
  have hden_sq : (1 - mixingRate N) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - mixingRate N)]
  have hkernel_lower : 4 * (n : ℝ) ≤ disagreementKernel N := by
    unfold disagreementKernel
    have hrow_nonneg : 0 ≤ rowMixingConstant N ^ 2 := sq_nonneg _
    have hdiv : rowMixingConstant N ^ 2 ≤
        rowMixingConstant N ^ 2 / (1 - mixingRate N) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hden_pos)).2
      nlinarith
    exact hrow_sq.trans hdiv
  have htracker_nonneg : 0 ≤ trackerIncrementKernel N :=
    htrackerIncrement.le
  have hka_lower : 24 * (n : ℝ) ^ 3 ≤ controlKa N := by
    unfold controlKa
    have hcoef : 0 ≤ 3 * (n : ℝ) + 6 * (n : ℝ) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hkernel_lower hcoef
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) htracker_nonneg]
  have hrb_lower : 1152 * (n : ℝ) ^ 5 ≤ controlRB N := by
    unfold controlRB controlMB
    have hmul := mul_le_mul_of_nonneg_right hka_lower
      (by positivity : 0 ≤ 48 * (n : ℝ) ^ 2)
    nlinarith
  have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast N.hn
  have hrb_target : 512 * (n : ℝ) ^ 4 ≤ controlRB N := by
    have hn4 : 0 ≤ (n : ℝ) ^ 4 := by positivity
    have : 512 * (n : ℝ) ^ 4 ≤ 1152 * (n : ℝ) ^ 5 := by
      nlinarith [mul_nonneg hn4 (sub_nonneg.mpr hn_one)]
    exact this.trans hrb_lower
  have hsqrt_lower : 64 * (n : ℝ) ^ 2 ≤
      Real.sqrt (8 * controlRB N) := by
    have hsq : (64 * (n : ℝ) ^ 2) ^ 2 ≤ 8 * controlRB N := by
      nlinarith
    have hleft_nonneg : 0 ≤ 64 * (n : ℝ) ^ 2 := by positivity
    rw [← Real.sqrt_sq hleft_nonneg]
    exact Real.sqrt_le_sqrt hsq
  have hgain_le : gainFloor N ≤ (n : ℝ) :=
    (gainFloor_le_gain N 0).trans (gain_le_n N 0)
  have hlast : correctedCenterStepCap N ≤
      gainFloor N / Real.sqrt (8 * controlRB N) := by
    unfold correctedCenterStepCap
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hratio : gainFloor N / Real.sqrt (8 * controlRB N) ≤
      (n : ℝ) / (64 * (n : ℝ) ^ 2) := by
    exact div_le_div₀ hn.le hgain_le (by positivity) hsqrt_lower
  calc
    correctedCenterStepCap N ≤
        gainFloor N / Real.sqrt (8 * controlRB N) := hlast
    _ ≤ (n : ℝ) / (64 * (n : ℝ) ^ 2) := hratio
    _ = 1 / (64 * (n : ℝ)) := by field_simp [ne_of_gt hn]

/-- Deterministic specialization of the corrected-center energy estimate at
the maximal source step `x_*`. -/
private theorem deterministic_fixed_step_cost_upper
    (N : NetworkSetup n) (L Δ H : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hH : 0 ≤ H)
    (T : PositiveHorizon) (I : fixedInstanceClass N L Δ 0 H) :
    I.1.cost (correctedCenterStepCap N / L) T ≤
      ((16 * ADelta L Δ /
          (gainFloor N * correctedCenterStepCap N) +
        (32 * controlRH N / gainFloor N ^ 2 +
          2 * controlJH N * correctedCenterStepCap N ^ 2) *
            (n : ℝ) * H ^ 2) / (T.1 : ℝ)) := by
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  let x := correctedCenterStepCap N
  let g := gainFloor N
  let S := I.1.setup
  let G := correctedGradientEnergy S (x / L) T
  have hxdata := correctedCenterStepCap_pos_and_admissible N
  have hx : 0 < x := hxdata.1
  have hg : 0 < g :=
    (uniform_mixing_and_influence N).2.2.2.2.2.2.2.1
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hnetwork : S.network = N := by
    simpa [S, FiniteInstance.network] using I.2.1
  have hLip : S.L = L := by
    simpa [S, FiniteInstance.lipschitz] using I.2.2.1
  have hgap : S.Δ = Δ := by
    simpa [S, FiniteInstance.gap] using I.2.2.2.1
  have hnoise : S.σ = 0 := by
    simpa [S, FiniteInstance.noiseScale] using I.2.2.2.2.1
  have hheterogeneity : S.H = H := by
    simpa [S, FiniteInstance.heterogeneityScale] using I.2.2.2.2.2
  have hfinite : InFiniteHeterogeneityLayer S := by
    simpa [S] using I.1.finite_layer
  have halpha : 0 < x / L := div_pos hx hL
  have hdim : dimensionlessStepsize S.L (x / L) = x := by
    rw [hLip]
    exact dimensionlessStepsize_div L x hL
  have hcontrol := corrected_center_uniform_control S hfinite (x / L)
    halpha (by rw [hdim, hnetwork]) T
  rcases hcontrol with ⟨_, _, _, _, _, _, _, _, _, _, hGraw⟩
  have hG : G ≤
      4 * Δ / ((x / L) * g) +
        8 * controlRH N * (n : ℝ) * H ^ 2 / g ^ 2 := by
    unfold correctedGradientUpperBound at hGraw
    rw [hnetwork, hLip, hgap, hnoise, hheterogeneity] at hGraw
    simpa [G, g] using hGraw
  let sCap : AdmissibleDimensionlessStepsize n :=
    ⟨x, hx, by simpa [x] using hxdata.2⟩
  have hcost := fixed_instance_cost_le_corrected_energy_expression
    N L Δ 0 H hL I T sCap (by simp [sCap, x])
  dsimp only at hcost
  have hG_nonneg : 0 ≤ G := by
    unfold G correctedGradientEnergy
    exact Finset.sum_nonneg fun t _ht => by
      unfold SOptLib.expectation
      exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hJB_pos : 0 < controlJB N := by
    have hrow : 0 < rowMixingConstant N := by
      unfold rowMixingConstant
      exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hn))
        (blockContraction_pos N)
    have hkernel : 0 < disagreementKernel N := by
      unfold disagreementKernel
      exact div_pos (sq_pos_of_pos hrow)
        (sq_pos_of_pos (sub_pos.mpr (mixingRate_lt_one N)))
    unfold controlJB controlMB
    positivity
  have hcapJB : x ≤ 1 / Real.sqrt (controlJB N) := by
    dsimp [x]
    unfold correctedCenterStepCap controlJB controlMB
    convert (min_le_right (1 : ℝ) _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))) using 1 <;> ring
  have hJB : x ^ 2 * controlJB N ≤ 1 := by
    have hsqrt : 0 < Real.sqrt (controlJB N) := Real.sqrt_pos.2 hJB_pos
    have hinv : 0 ≤ 1 / Real.sqrt (controlJB N) := by positivity
    have hsq : x ^ 2 ≤ (1 / Real.sqrt (controlJB N)) ^ 2 :=
      (sq_le_sq₀ hx.le hinv).2 hcapJB
    have hmul := mul_le_mul_of_nonneg_right hsq hJB_pos.le
    calc
      x ^ 2 * controlJB N ≤
          (1 / Real.sqrt (controlJB N)) ^ 2 * controlJB N := hmul
      _ = 1 := by
        rw [div_pow, one_pow, Real.sq_sqrt hJB_pos.le]
        field_simp [hJB_pos.ne']
  have hcoef : 2 + 2 * x ^ 2 * controlJB N ≤ 4 := by
    nlinarith
  have hinside :
      2 * G + 2 * x ^ 2 *
          (controlJB N * G + controlJH N * (n : ℝ) * H ^ 2 +
            controlJN N * 0 ^ 2 * (T.1 : ℝ)) ≤
        16 * ADelta L Δ / (g * x) +
          (32 * controlRH N / g ^ 2 +
            2 * controlJH N * x ^ 2) * (n : ℝ) * H ^ 2 := by
    have hGcoef := mul_le_mul_of_nonneg_right hcoef hG_nonneg
    have hG4 := mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 4)
    have hmain :
        (2 + 2 * x ^ 2 * controlJB N) * G +
            2 * x ^ 2 * controlJH N * (n : ℝ) * H ^ 2 ≤
          4 * (4 * Δ / ((x / L) * g) +
            8 * controlRH N * (n : ℝ) * H ^ 2 / g ^ 2) +
            2 * x ^ 2 * controlJH N * (n : ℝ) * H ^ 2 := by
      linarith
    unfold ADelta
    field_simp [hL.ne', hx.ne', hg.ne'] at hmain ⊢
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hinside
    (inv_nonneg.mpr (Nat.cast_nonneg T.1))
  calc
    I.1.cost (correctedCenterStepCap N / L) T ≤
        (T.1 : ℝ)⁻¹ *
          (2 * G + 2 * x ^ 2 *
            (controlJB N * G + controlJH N * (n : ℝ) * H ^ 2 +
              controlJN N * 0 ^ 2 * (T.1 : ℝ))) := by
        simpa [sCap, x, G, S] using hcost
    _ ≤ (T.1 : ℝ)⁻¹ *
        (16 * ADelta L Δ / (g * x) +
          (32 * controlRH N / g ^ 2 +
            2 * controlJH N * x ^ 2) * (n : ℝ) * H ^ 2) := hscaled
    _ = ((16 * ADelta L Δ /
          (gainFloor N * correctedCenterStepCap N) +
        (32 * controlRH N / gainFloor N ^ 2 +
          2 * controlJH N * correctedCenterStepCap N ^ 2) *
            (n : ℝ) * H ^ 2) / (T.1 : ℝ)) := by
      dsimp [g, x]
      ring

private theorem one_node_zero_sum_state_eq_zero
    {E : Type*} [AddCommGroup E]
    (z : FiniteNetwork.ZeroSumState (Fin 1) E) : z = 0 := by
  apply Subtype.ext
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simpa using z.property

/-- With one node the corrected Perron center is literally the arithmetic
algorithm output; the zero-sum correction carrier has collapsed. -/
private theorem one_node_correctedCenter_eq_arithmeticMean
    (S : Setup n d Ω) (hn1 : n = 1)
    (omega : Ω) (alpha : ℝ) (t : ℕ) :
    correctedCenter S omega alpha t = arithmeticMean S omega alpha t := by
  classical
  subst n
  have hz : filteredNoiseZeroSum S omega t = 0 :=
    one_node_zero_sum_state_eq_zero (filteredNoiseZeroSum S omega t)
  have hDnorm := influenceOperatorPoint_norm_le S.network t
    (0 : FiniteNetwork.ZeroSumState (Fin 1) (Point d))
  have hD : influenceOperatorPoint S.network t
      (0 : FiniteNetwork.ZeroSumState (Fin 1) (Point d)) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm
    · simpa using hDnorm
    · exact norm_nonneg _
  have hpi : absoluteProbability S.network t (0 : Fin 1) = 1 := by
    simpa using (absoluteProbability_spec S.network).2.1 t
  unfold correctedCenter arithmeticMean
  rw [hz, hD]
  simp [hpi]

/-- The predictable corrected drift has no transverse component on a
one-node network. -/
private theorem one_node_correctedDrift_eq_zero
    (S : Setup n d Ω) (hn1 : n = 1)
    (omega : Ω) (alpha : ℝ) (t : ℕ) :
    correctedDrift S omega alpha t = 0 := by
  classical
  subst n
  have hcenter := one_node_correctedCenter_eq_arithmeticMean
    S rfl omega alpha t
  have hmean : arithmeticMean S omega alpha t = primal S omega alpha t 0 := by
    simp [arithmeticMean]
  have havg : averageObjective S = S.localObjective 0 := by
    funext z
    simp [averageObjective]
  have hdis : correctedTrackerDisagreement S omega alpha t = 0 := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simpa using correctedTrackerDisagreement_sum_zero S omega alpha t
  unfold correctedDrift
  rw [hcenter, hmean, havg, hdis]
  simp [gradientTable]

/-- Sharp deterministic one-node gradient-descent cost, including the
original stochastic-oracle interface specialized through its zero moment. -/
private theorem one_node_deterministic_cost_upper
    (N : NetworkSetup n) (L Δ H : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hH : 0 ≤ H)
    (T : PositiveHorizon) (hn1 : n = 1)
    (I : fixedInstanceClass N L Δ 0 H) :
    I.1.cost (1 / L) T ≤
      2 * ADelta L Δ / (T.1 : ℝ) := by
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  let S := I.1.setup
  have hnetwork : S.network = N := by
    simpa [S, FiniteInstance.network] using I.2.1
  have hLip : S.L = L := by
    simpa [S, FiniteInstance.lipschitz] using I.2.2.1
  have hgap : S.Δ = Δ := by
    simpa [S, FiniteInstance.gap] using I.2.2.2.1
  have hnoise : S.σ = 0 := by
    simpa [S, FiniteInstance.noiseScale] using I.2.2.2.2.1
  have halpha : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have hstep (t : ℕ) :
      (1 / (2 * L)) *
          SOptLib.expectation S.probability (fun omega =>
            ‖gradient (averageObjective S)
              (correctedCenter S omega (1 / L) t)‖ ^ 2) ≤
        SOptLib.expectation S.probability (fun omega =>
          averageObjective S (correctedCenter S omega (1 / L) t) -
            averageObjective S (correctedCenter S omega (1 / L) (t + 1))) := by
    have hsourceExact (omega : I.1.Ω) :=
      corrected_center_smooth_step_exact S omega (1 / L) halpha t
    have h := corrected_center_expected_one_step_gain_descent
      S (1 / L) halpha t
    have hgain : gain S.network t = 1 := by
      rw [hnetwork]
      exact gain_eq_one_of_n_eq_one N hn1 t
    simp_rw [one_node_correctedDrift_eq_zero S hn1] at h
    rw [hgain, hLip, hnoise] at h
    simp only [one_smul, norm_zero, zero_pow, Nat.ofNat_pos, mul_zero,
      add_zero, inner_zero_right] at h
    have hzeroExpectation :
        SOptLib.expectation S.probability (fun _ : I.1.Ω => (0 : ℝ)) = 0 := by
      simp [SOptLib.expectation]
    rw [hzeroExpectation] at h
    norm_num at h
    field_simp [hL.ne'] at h ⊢
    linarith
  have hsum := Finset.sum_le_sum fun t
    (_ht : t ∈ Finset.range T.1) => hstep t
  have hdrop := corrected_center_objective_drop_telescope S (1 / L) T
  have henergy :
      (1 / (2 * L)) * correctedGradientEnergy S (1 / L) T ≤ Δ := by
    unfold correctedGradientEnergy
    rw [← Finset.mul_sum] at hsum
    rw [hgap] at hdrop
    exact hsum.trans hdrop
  have hcenter (omega : I.1.Ω) (t : ℕ) :
      correctedCenter S omega (1 / L) t =
        arithmeticMean S omega (1 / L) t :=
    one_node_correctedCenter_eq_arithmeticMean S hn1 omega (1 / L) t
  have hcostEnergy : I.1.cost (1 / L) T =
      (T.1 : ℝ)⁻¹ * correctedGradientEnergy S (1 / L) T := by
    change stationarityError S (1 / L) T =
      (T.1 : ℝ)⁻¹ * correctedGradientEnergy S (1 / L) T
    unfold stationarityError correctedGradientEnergy
    apply congrArg ((T.1 : ℝ)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro t ht
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun omega => by
      unfold stationarityIntegrand
      rw [← hcenter omega t]
  have hG : correctedGradientEnergy S (1 / L) T ≤ 2 * L * Δ := by
    calc
      correctedGradientEnergy S (1 / L) T =
          (2 * L) * ((1 / (2 * L)) *
            correctedGradientEnergy S (1 / L) T) := by
        field_simp [hL.ne']
      _ ≤ (2 * L) * Δ :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = 2 * L * Δ := by ring
  rw [hcostEnergy]
  have hscaled := mul_le_mul_of_nonneg_left hG
    (inv_nonneg.mpr (Nat.cast_nonneg T.1))
  unfold ADelta
  calc
    (T.1 : ℝ)⁻¹ * correctedGradientEnergy S (1 / L) T ≤
        (T.1 : ℝ)⁻¹ * (2 * L * Δ) := hscaled
    _ = 2 * (L * Δ) / (T.1 : ℝ) := by ring

/-- Equation (65), including the exact `n=1` boundary for every positive
horizon.
Book `#/key_lemmas/9/statement_math`:
“`\sigma=0\Longrightarrow {2L\Delta\over T}\le R_T`”. -/
theorem deterministic_endpoint
    (N : NetworkSetup n) (L Δ H : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hH : 0 ≤ H) :
    ∀ T : PositiveHorizon,
      ENNReal.ofReal (2 * ADelta L Δ / T.1) ≤
        minimaxRisk (fixedInstanceClass N L Δ 0 H) T ∧
      minimaxRisk (fixedInstanceClass N L Δ 0 H) T ≤
        ENNReal.ofReal
          ((16 * ADelta L Δ /
              (gainFloor N * correctedCenterStepCap N) +
            (32 * controlRH N / gainFloor N ^ 2 +
              2 * controlJH N * correctedCenterStepCap N ^ 2) * n * H ^ 2) /
            T.1) ∧
      (n = 1 →
        minimaxRisk (fixedInstanceClass N L Δ 0 H) T =
          ENNReal.ofReal (2 * ADelta L Δ / T.1)) := by
  intro T
  have hLowerReal :=
    deterministic_quadratic_time_zero_witness N L Δ 0 H hL hΔ le_rfl hH T
  have hLower : ENNReal.ofReal (2 * ADelta L Δ / (T.1 : ℝ)) ≤
      minimaxRisk (fixedInstanceClass N L Δ 0 H) T := by
    unfold minimaxRisk
    apply le_iInf
    intro α
    obtain ⟨I, hI⟩ := hLowerReal α.1 α.2
    exact le_iSup_of_le I (ENNReal.ofReal_le_ofReal hI)
  have hx := correctedCenterStepCap_pos_and_admissible N
  have halphaStar : 0 < correctedCenterStepCap N / L :=
    div_pos hx.1 hL
  have hUpper : minimaxRisk (fixedInstanceClass N L Δ 0 H) T ≤
      ENNReal.ofReal
        ((16 * ADelta L Δ /
            (gainFloor N * correctedCenterStepCap N) +
          (32 * controlRH N / gainFloor N ^ 2 +
            2 * controlJH N * correctedCenterStepCap N ^ 2) *
              (n : ℝ) * H ^ 2) / (T.1 : ℝ)) := by
    unfold minimaxRisk
    refine iInf_le_of_le
      ⟨correctedCenterStepCap N / L, halphaStar⟩ ?_
    apply iSup_le
    intro I
    exact ENNReal.ofReal_le_ofReal
      (deterministic_fixed_step_cost_upper N L Δ H hL hΔ hH T I)
  refine ⟨hLower, hUpper, ?_⟩
  intro hn1
  apply le_antisymm
  · unfold minimaxRisk
    refine iInf_le_of_le ⟨1 / L, one_div_pos.mpr hL⟩ ?_
    apply iSup_le
    intro I
    exact ENNReal.ofReal_le_ofReal
      (one_node_deterministic_cost_upper N L Δ H hL hΔ hH T hn1 I)
  · exact hLower

/-- The original class before imposing a finite layer. Book
`#/key_lemmas/10/statement_math`: “the unrestricted-H class”. -/
def unrestrictedInstanceClass
    (N : NetworkSetup n) (L Δ σ : ℝ) : Set (FiniteInstance n) :=
  {I | I.network = N ∧ I.lipschitz = L ∧ I.gap = Δ ∧ I.noiseScale = σ}

/-- `bar lambda`. Book `#/key_lemmas/10/statement_math`:
“`\bar\lambda=n^{-1}\sum_i\lambda_i`”. -/
def averageCurvature (lam : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i, lam i

/-- The projected coefficient. Book `#/key_lemmas/10/statement_math`:
“`v=\Pi(\alpha\lambda-R_1^\top1)\ne0`”. -/
def unboundedHeterogeneityDirection
    (N : NetworkSetup n) (α : ℝ) (lam : Fin n → ℝ) : Fin n → ℝ :=
  disagreement (fun i => α * lam i - ∑ j, N.rowMix 1 j i)

/-- Correspondence to the explicit family. Book
`#/key_lemmas/10/statement_math`:
“`f_i(x)=\lambda_i x^2/2+Mv_ix`, `x_0=\sqrt{2\Delta/\bar\lambda}`”. -/
def IsUnboundedQuadraticFamilyInstance
    (I : FiniteInstance n) (lam v : Fin n → ℝ) (M Δ : ℝ) : Prop :=
  ∃ hd : I.d = 1,
    (∀ i (x : Point 1),
      (@Setup.localObjective n I.d I.Ω I.measurableSpace I.setup i) (hd.symm ▸ x) =
        lam i * (x 0) ^ 2 / 2 + M * v i * x 0) ∧
    (∀ k : Fin 1,
      (hd ▸ (@Setup.initialPoint n I.d I.Ω I.measurableSpace I.setup)) k =
        Real.sqrt (2 * Δ / averageCurvature lam))

/-- The bounded curvature choice in the verification supplement for (66).
The proof compares a constant vector with a one-coordinate perturbation; their
disagreement projections cannot both vanish when there are two nodes. -/
private theorem exists_bounded_curvature_nonzero_direction
    (N : NetworkSetup n) (L α : ℝ) (hn : 2 ≤ n)
    (hL : 0 < L) (hα : 0 < α) :
    ∃ lam : Fin n → ℝ,
      (∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4) ∧
      unboundedHeterogeneityDirection N α lam ≠ 0 := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  let lam₀ : Fin n → ℝ := fun _ => L / 2
  let lam₁ : Fin n → ℝ := fun i => if i = i₀ then 5 * L / 8 else L / 2
  have hlam₀ : ∀ i, L / 4 ≤ lam₀ i ∧ lam₀ i ≤ 3 * L / 4 := by
    intro i
    dsimp [lam₀]
    constructor <;> nlinarith
  have hlam₁ : ∀ i, L / 4 ≤ lam₁ i ∧ lam₁ i ≤ 3 * L / 4 := by
    intro i
    dsimp [lam₁]
    split_ifs <;> constructor <;> nlinarith
  by_cases hv₀ : unboundedHeterogeneityDirection N α lam₀ ≠ 0
  · exact ⟨lam₀, hlam₀, hv₀⟩
  · refine ⟨lam₁, hlam₁, ?_⟩
    intro hv₁
    have hconstAtZero := congrFun (not_ne_iff.mp hv₀) i₀
    have hconstAtOne := congrFun (not_ne_iff.mp hv₀) i₁
    have hperturbAtZero := congrFun hv₁ i₀
    have hperturbAtOne := congrFun hv₁ i₁
    simp only [unboundedHeterogeneityDirection, disagreement, Pi.zero_apply] at hconstAtZero hconstAtOne hperturbAtZero hperturbAtOne
    dsimp [lam₀, lam₁, i₀, i₁] at hconstAtZero hconstAtOne hperturbAtZero hperturbAtOne
    norm_num at hconstAtZero hconstAtOne hperturbAtZero hperturbAtOne
    nlinarith

/-- The arithmetic disagreement projection has zero total mass, as used when
the linear terms in the family (66) are averaged. -/
private theorem unboundedHeterogeneityDirection_sum_eq_zero
    (N : NetworkSetup n) (α : ℝ) (lam : Fin n → ℝ) :
    ∑ i, unboundedHeterogeneityDirection N α lam i = 0 := by
  let z : Fin n → ℝ := fun i => α * lam i - ∑ j, N.rowMix 1 j i
  change ∑ i, disagreement z i = 0
  unfold disagreement
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.hn)
  field_simp [hn0]
  ring

/-- Coordinatewise curvature bounds pass to the arithmetic average, with
strict positivity supplied by `L > 0`. -/
private theorem averageCurvature_bounds
    (N : NetworkSetup n) (L : ℝ) (hL : 0 < L) (lam : Fin n → ℝ)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4) :
    L / 4 ≤ averageCurvature lam ∧
      averageCurvature lam ≤ 3 * L / 4 ∧ 0 < averageCurvature lam := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  have hsumLower : (n : ℝ) * (L / 4) ≤ ∑ i, lam i := by
    calc
      (n : ℝ) * (L / 4) = ∑ _ : Fin n, L / 4 := by simp
      _ ≤ ∑ i, lam i := Finset.sum_le_sum fun i _ => (hlam i).1
  have hsumUpper : (∑ i, lam i) ≤ (n : ℝ) * (3 * L / 4) := by
    calc
      (∑ i, lam i) ≤ ∑ _ : Fin n, 3 * L / 4 :=
        Finset.sum_le_sum fun i _ => (hlam i).2
      _ = (n : ℝ) * (3 * L / 4) := by simp
  have hinv : 0 ≤ (n : ℝ)⁻¹ := (inv_pos.mpr hn).le
  have hlower := mul_le_mul_of_nonneg_left hsumLower hinv
  have hupper := mul_le_mul_of_nonneg_left hsumUpper hinv
  have hleft : L / 4 ≤ averageCurvature lam := by
    unfold averageCurvature
    calc
      L / 4 = (n : ℝ)⁻¹ * ((n : ℝ) * (L / 4)) := by
        field_simp [ne_of_gt hn]
      _ ≤ (n : ℝ)⁻¹ * ∑ i, lam i := hlower
  have hright : averageCurvature lam ≤ 3 * L / 4 := by
    unfold averageCurvature
    calc
      (n : ℝ)⁻¹ * ∑ i, lam i ≤
          (n : ℝ)⁻¹ * ((n : ℝ) * (3 * L / 4)) := hupper
      _ = 3 * L / 4 := by field_simp [ne_of_gt hn]
  exact ⟨hleft, hright, lt_of_lt_of_le (by positivity) hleft⟩

/-- Calculus package for one local quadratic in (66).  The affine term changes
the gradient value but not its Lipschitz constant. -/
private theorem unbounded_quadratic_local_objective_spec
    (L lam beta : ℝ) (hL : 0 < L) (hlam0 : 0 ≤ lam) (hlamL : lam ≤ L) :
    let F : Point 1 → ℝ := fun x => lam * (x 0) ^ 2 / 2 + beta * x 0
    (Differentiable ℝ F ∧ LipschitzWith ⟨L, hL.le⟩ (gradient F)) ∧
      ∀ x, gradient F x = PiLp.single 2 (0 : Fin 1) (lam * x 0 + beta) := by
  let f : Fin 1 → ℝ → ℝ :=
    fun _ z => lam * z ^ 2 / 2 + beta * z
  let g : Fin 1 → ℝ → ℝ := fun _ z => lam * z + beta
  have hderiv : ∀ k z, HasDerivAt (f k) (g k z) z := by
    intro k z
    dsimp [f, g]
    convert (((((hasDerivAt_id z).pow 2).const_mul lam).div_const 2).add
      ((hasDerivAt_id z).const_mul beta)) using 1 <;> simp only [id_eq] <;> ring
  have hlip : ∀ k x y, ‖g k x - g k y‖ ≤ L * ‖x - y‖ := by
    intro k x y
    dsimp [g]
    rw [show lam * x + beta - (lam * y + beta) = lam * (x - y) by ring]
    rw [abs_mul, abs_of_nonneg hlam0]
    exact mul_le_mul_of_nonneg_right hlamL (abs_nonneg _)
  have hsmooth := separablePoint_local_smooth f g L hL.le hderiv hlip
  let F : Point 1 → ℝ := fun x => lam * (x 0) ^ 2 / 2 + beta * x 0
  have hF : (fun z : Point 1 => ∑ k, f k (z k)) = F := by
    funext z
    simp [f, F]
  rw [hF] at hsmooth
  have hgrad (x : Point 1) :
      gradient F x =
        PiLp.single 2 (0 : Fin 1) (lam * x 0 + beta) := by
    have hx := (hasGradientAt_separablePoint f g x (hderiv · _)).gradient
    rw [hF] at hx
    rw [hx]
    ext k
    fin_cases k
    simp [g]
  exact ⟨hsmooth, hgrad⟩

/-- Each positive scale in (66) gives a legal finite instance.  Its declared
noise scale is `σ` although its realized noise is zero, and its finite
heterogeneity radius is chosen separately from its actual initial energy. -/
private theorem unbounded_quadratic_family_instance
    (N : NetworkSetup n) (L Δ σ α M : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (lam : Fin n → ℝ)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4) :
    ∃ I : FiniteInstance n,
      I ∈ unrestrictedInstanceClass N L Δ σ ∧
      IsUnboundedQuadraticFamilyInstance I lam
        (unboundedHeterogeneityDirection N α lam) M Δ ∧
      (∀ t ω i,
        @Setup.noise n I.d I.Ω I.measurableSpace I.setup t ω i = 0) := by
  classical
  let v := unboundedHeterogeneityDirection N α lam
  let q := averageCurvature lam
  have hvsum : ∑ i, v i = 0 := by
    simpa [v] using unboundedHeterogeneityDirection_sum_eq_zero N α lam
  have hq := averageCurvature_bounds N L hL lam hlam
  have hqpos : 0 < q := by simpa [q] using hq.2.2
  let F : Fin n → Point 1 → ℝ :=
    fun i x => lam i * (x 0) ^ 2 / 2 + M * v i * x 0
  let x0 : Point 1 :=
    WithLp.toLp 2 (fun _ : Fin 1 => Real.sqrt (2 * Δ / q))
  let noise : ℕ → Unit → NodeTable n 1 := fun _ _ _ => 0
  have hhistory (t : ℕ) :
      preSamplingHistoryOf noise t ≤ PUnit.instMeasurableSpace := by
    unfold preSamplingHistoryOf
    refine iSup_le fun j => iSup_le fun hj => ?_
    rw [← measurable_iff_comap_le]
    exact measurable_const
  have hlocal (i : Fin n) :
      Differentiable ℝ (F i) ∧
        LipschitzWith ⟨L, hL.le⟩ (gradient (F i)) := by
    have hli0 : 0 ≤ lam i := le_trans (by positivity) (hlam i).1
    have hliL : lam i ≤ L := by nlinarith [(hlam i).2]
    simpa [F, v] using
      (unbounded_quadratic_local_objective_spec L (lam i) (M * v i)
        hL hli0 hliL).1
  have havg (x : Point 1) :
      (n : ℝ)⁻¹ * ∑ i, F i x = q * (x 0) ^ 2 / 2 := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt N.hn)
    simp only [F, Finset.sum_add_distrib]
    have hquad : ∑ i, lam i * (x 0) ^ 2 / 2 =
        (∑ i, lam i) * (x 0) ^ 2 / 2 := by
      calc
        ∑ i, lam i * (x 0) ^ 2 / 2 =
            ∑ i, lam i * ((x 0) ^ 2 / 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (∑ i, lam i) * ((x 0) ^ 2 / 2) := by rw [Finset.sum_mul]
        _ = (∑ i, lam i) * (x 0) ^ 2 / 2 := by ring
    have hlin : ∑ i, M * v i * x 0 = 0 := by
      calc
        ∑ i, M * v i * x 0 = ∑ i, v i * (M * x 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, v i) * (M * x 0) := by rw [Finset.sum_mul]
        _ = 0 := by rw [hvsum]; ring
    rw [hquad, hlin, add_zero]
    dsimp [q, averageCurvature]
    field_simp [hn0]
  have hsinf :
      sInf (Set.range fun x : Point 1 => (n : ℝ)⁻¹ * ∑ i, F i x) = 0 := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · refine ⟨0, ⟨0, ?_⟩⟩
      simp [havg]
    · rintro _ ⟨x, rfl⟩
      change 0 ≤ (n : ℝ)⁻¹ * ∑ i, F i x
      rw [havg]
      exact div_nonneg (mul_nonneg hqpos.le (sq_nonneg _)) (by norm_num)
    · intro w hw
      refine ⟨0, ⟨0, ?_⟩, ?_⟩
      · simp [havg]
      · simpa using hw
  have hgap :
      (n : ℝ)⁻¹ * ∑ i, F i x0 -
          sInf (Set.range fun x : Point 1 => (n : ℝ)⁻¹ * ∑ i, F i x) = Δ := by
    rw [hsinf, havg]
    have harg : 0 ≤ 2 * Δ / q := by
      exact div_nonneg (mul_nonneg (by norm_num) hΔ.le) hq.2.2.le
    dsimp [x0]
    rw [Real.sq_sqrt harg]
    field_simp [hqpos.ne']
    ring
  let S0 : Setup n 1 Unit :=
    { network := N
      hd := by norm_num
      L := L
      Δ := Δ
      σ := σ
      H := 0
      hL := hL
      hΔ := hΔ
      hσ := hσ
      hH := le_rfl
      localObjective := F
      initialPoint := x0
      noise := noise
      probability := escapedBinderProbability
      is_probability := escapedBinderProbability_isProbability
      local_smooth := hlocal
      average_lower_bounded := by
        refine ⟨0, ?_⟩
        rintro _ ⟨x, rfl⟩
        change 0 ≤ (n : ℝ)⁻¹ * ∑ i, F i x
        rw [havg]
        exact div_nonneg (mul_nonneg hqpos.le (sq_nonneg _)) (by norm_num)
      exact_initial_gap := hgap
      noise_centered := by
        intro t i
        exact diracUnitConditionalExpectationEqSelf
          (preSamplingHistoryOf noise t) (hhistory t) _
      noise_second_moment := by
        intro t i
        have hz := diracUnitConditionalSecondMomentZero
          (E := Point 1) (preSamplingHistoryOf noise t) (hhistory t)
        refine ⟨hz.1, ?_⟩
        filter_upwards [hz.2] with ω hω
        exact hω.trans (sq_nonneg σ)
      node_conditional_independence := by
        intro t
        exact diracUnitNodeConditionallyIndependentZero _ (hhistory t) }
  let E : ℝ := initialHeterogeneitySq S0
  have hE : 0 ≤ E := by
    dsimp [E, initialHeterogeneitySq]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  let S : Setup n 1 Unit := { S0 with H := Real.sqrt E, hH := Real.sqrt_nonneg E }
  have hfinite : InFiniteHeterogeneityLayer S := by
    unfold InFiniteHeterogeneityLayer
    change E ≤ Real.sqrt E ^ 2
    rw [Real.sq_sqrt hE]
  let I : FiniteInstance n :=
    { d := 1
      Ω := Unit
      setup := S
      finite_layer := hfinite }
  refine ⟨I, ?_, ?_, ?_⟩
  · simp [unrestrictedInstanceClass, I, S, S0, FiniteInstance.network,
      FiniteInstance.lipschitz, FiniteInstance.gap, FiniteInstance.noiseScale]
  · refine ⟨rfl, ?_, ?_⟩
    · intro i x
      rfl
    · intro k
      fin_cases k
      rfl
  · intro t ω i
    rfl

/-- The T1 witness and the legal per-scale construction assembled in the
quantifier order required by (66), retaining zero realized noise for the true
two-step recurrence calculation. -/
private theorem unbounded_quadratic_family_data
    (N : NetworkSetup n) (L Δ σ α : ℝ)
    (hn : 2 ≤ n) (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hα : 0 < α) :
    ∃ lam : Fin n → ℝ,
      (∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4) ∧
      unboundedHeterogeneityDirection N α lam ≠ 0 ∧
      ∃ I : {M : ℝ // 0 < M} → FiniteInstance n,
        ∀ M,
          I M ∈ unrestrictedInstanceClass N L Δ σ ∧
          IsUnboundedQuadraticFamilyInstance (I M) lam
            (unboundedHeterogeneityDirection N α lam) M.1 Δ ∧
          (∀ t ω i,
            @Setup.noise n (I M).d (I M).Ω (I M).measurableSpace
              (I M).setup t ω i = 0) := by
  obtain ⟨lam, hlam, hv⟩ :=
    exists_bounded_curvature_nonzero_direction N L α hn hL hα
  have hinstance (M : {M : ℝ // 0 < M}) :=
    unbounded_quadratic_family_instance N L Δ σ α M.1 hL hΔ hσ lam hlam
  choose I hI using hinstance
  exact ⟨lam, hlam, hv, I, hI⟩

/-- The first true Push--Pull primal step for the source quadratic family.
This is the `X₁ = 1 x₀ - α g₀` part of the two-step calculation. -/
private theorem unbounded_quadratic_first_primal
    (S : Setup n 1 Ω) (omega : Ω)
    (L α M xzero : ℝ) (lam v : Fin n → ℝ)
    (hL : 0 < L)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4)
    (hobj : ∀ i (x : Point 1),
      S.localObjective i x = lam i * (x 0) ^ 2 / 2 + M * v i * x 0)
    (hinit : ∀ k : Fin 1, S.initialPoint k = xzero)
    (hnoise : ∀ t ω i, S.noise t ω i = 0) :
    ∀ i, (primal S omega α 1 i) 0 =
      xzero - α * (lam i * xzero + M * v i) := by
  intro i
  have hli0 : 0 ≤ lam i := le_trans (by positivity) (hlam i).1
  have hliL : lam i ≤ L := by nlinarith [(hlam i).2]
  have hfun : S.localObjective i =
      fun x : Point 1 => lam i * (x 0) ^ 2 / 2 + M * v i * x 0 := by
    funext x
    exact hobj i x
  have hgrad :
      (gradient (S.localObjective i) S.initialPoint) 0 =
        lam i * xzero + M * v i := by
    rw [hfun]
    have hg := (unbounded_quadratic_local_objective_spec
      L (lam i) (M * v i) hL hli0 hliL).2 S.initialPoint
    rw [hg]
    simp [hinit]
  have hrow : ∑ j, S.rowMix 0 i j = 1 :=
    Matrix.sum_row_of_mem_rowStochastic (S.row_stochastic 0) i
  have heval_sum (Z : Fin n → Point 1) :
      (∑ r, Z r) (0 : Fin 1) = ∑ r, (Z r) 0 := by
    let p := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) (0 : Fin 1)
    change p (∑ r, Z r) = ∑ r, p (Z r)
    exact map_sum p Z Finset.univ
  have hmul_eval (B : NetworkMatrix n) (Z : Fin n → Point 1) (q : Fin n) :
      (leftAct B Z q) 0 = ∑ r, B q r * (Z r) 0 := by
    unfold leftAct
    rw [Matrix.smulVec_apply, heval_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [PiLp.smul_apply, smul_eq_mul]
  rw [congrFun (primal_succ S omega α 0) i]
  simp only [Pi.sub_apply, PiLp.sub_apply, Pi.smul_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [hmul_eval]
  change (∑ j, S.rowMix 0 i j * (primal S omega α 0 j) 0) -
      α * (tracker S omega α 0 i) 0 = _
  simp only [primal_zero, tracker_zero]
  rw [sampledOracle_eq_gradient_add_noise]
  rw [primal_zero]
  rw [hnoise, add_zero, hgrad]
  simp_rw [hinit]
  rw [← Finset.sum_mul, hrow]
  ring

/-- The exact time-one oracle value obtained from the true first primal step. -/
private theorem unbounded_quadratic_oracle_one
    (S : Setup n 1 Ω) (omega : Ω)
    (L α M xzero : ℝ) (lam v : Fin n → ℝ)
    (hL : 0 < L)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4)
    (hobj : ∀ i (x : Point 1),
      S.localObjective i x = lam i * (x 0) ^ 2 / 2 + M * v i * x 0)
    (hinit : ∀ k : Fin 1, S.initialPoint k = xzero)
    (hnoise : ∀ t ω i, S.noise t ω i = 0) :
    ∀ i, (sampledOracle S omega α 1 i) 0 =
      lam i * (xzero - α * (lam i * xzero + M * v i)) + M * v i := by
  intro i
  have hfirst := unbounded_quadratic_first_primal
    S omega L α M xzero lam v hL hlam hobj hinit hnoise i
  have hli0 : 0 ≤ lam i := le_trans (by positivity) (hlam i).1
  have hliL : lam i ≤ L := by nlinarith [(hlam i).2]
  have hfun : S.localObjective i =
      fun x : Point 1 => lam i * (x 0) ^ 2 / 2 + M * v i * x 0 := by
    funext x
    exact hobj i x
  rw [sampledOracle_eq_gradient_add_noise, hnoise, add_zero, hfun]
  have hg := (unbounded_quadratic_local_objective_spec
    L (lam i) (M * v i) hL hli0 hliL).2 (primal S omega α 1 i)
  rw [hg]
  simp only [PiLp.single_apply, if_pos]
  rw [hfirst]

/-- The exact scalar arithmetic mean after the second true Push--Pull step,
before collecting its affine `M` coefficient. -/
private theorem unbounded_quadratic_second_mean_raw
    (S : Setup n 1 Ω) (omega : Ω)
    (L α M xzero : ℝ) (lam v : Fin n → ℝ)
    (hL : 0 < L)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4)
    (hobj : ∀ i (x : Point 1),
      S.localObjective i x = lam i * (x 0) ^ 2 / 2 + M * v i * x 0)
    (hinit : ∀ k : Fin 1, S.initialPoint k = xzero)
    (hnoise : ∀ t ω i, S.noise t ω i = 0) :
    (arithmeticMean S omega α 2) 0 =
      (n : ℝ)⁻¹ *
        ((∑ i, ∑ j, S.rowMix 1 i j *
            (xzero - α * (lam j * xzero + M * v j))) -
          α * ∑ i,
            (lam i * (xzero - α * (lam i * xzero + M * v i)) + M * v i)) := by
  have hfirst := unbounded_quadratic_first_primal
    S omega L α M xzero lam v hL hlam hobj hinit hnoise
  have horacle := unbounded_quadratic_oracle_one
    S omega L α M xzero lam v hL hlam hobj hinit hnoise
  have heval_sum (Z : Fin n → Point 1) :
      (∑ r, Z r) (0 : Fin 1) = ∑ r, (Z r) 0 := by
    let p := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) (0 : Fin 1)
    change p (∑ r, Z r) = ∑ r, p (Z r)
    exact map_sum p Z Finset.univ
  have hmul_eval (B : NetworkMatrix n) (Z : Fin n → Point 1) (q : Fin n) :
      (leftAct B Z q) 0 = ∑ r, B q r * (Z r) 0 := by
    unfold leftAct
    rw [Matrix.smulVec_apply, heval_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [PiLp.smul_apply, smul_eq_mul]
  have htracker :
      ∑ i, (tracker S omega α 1 i) 0 =
        ∑ i, (sampledOracle S omega α 1 i) 0 := by
    have ht := tracker_sum_eq_sampledOracle_sum S omega α 1
    have hp := congrArg
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) (0 : Fin 1)) ht
    simpa only [map_sum] using hp
  have hsecond (i : Fin n) :
      (primal S omega α 2 i) 0 =
        (∑ j, S.rowMix 1 i j *
          (xzero - α * (lam j * xzero + M * v j))) -
          α * (tracker S omega α 1 i) 0 := by
    rw [congrFun (primal_succ S omega α 1) i]
    simp only [Pi.sub_apply, PiLp.sub_apply, Pi.smul_apply,
      PiLp.smul_apply, smul_eq_mul]
    rw [hmul_eval]
    simp_rw [hfirst]
  unfold arithmeticMean
  simp only [PiLp.smul_apply, smul_eq_mul, heval_sum]
  simp_rw [hsecond]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htracker]
  simp_rw [horacle]

/-- Orthogonality of arithmetic disagreement to constants, in the exact form
needed to collect the `M` coefficient of the raw second iterate. -/
private theorem unbounded_direction_dot_eq_square
    (N : NetworkSetup n) (α : ℝ) (lam : Fin n → ℝ) :
    ∑ i, (α * lam i - ∑ j, N.rowMix 1 j i) *
        unboundedHeterogeneityDirection N α lam i =
      ∑ i, unboundedHeterogeneityDirection N α lam i ^ 2 := by
  let z : Fin n → ℝ := fun i => α * lam i - ∑ j, N.rowMix 1 j i
  let v : Fin n → ℝ := disagreement z
  let mu : ℝ := (n : ℝ)⁻¹ * ∑ j, z j
  have hvsum : ∑ i, v i = 0 := by
    simpa [v, z, unboundedHeterogeneityDirection] using
      unboundedHeterogeneityDirection_sum_eq_zero N α lam
  change ∑ i, z i * v i = ∑ i, v i ^ 2
  calc
    ∑ i, z i * v i = ∑ i, (v i ^ 2 + mu * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [v, disagreement, mu]
      ring
    _ = (∑ i, v i ^ 2) + mu * ∑ i, v i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ i, v i ^ 2 := by rw [hvsum]; ring

/-- The second arithmetic mean in (66), with all dependence on the family
scale collected into the source coefficient `α ‖v‖² / n`. -/
private theorem unbounded_quadratic_second_mean_affine
    (S : Setup n 1 Ω) (omega : Ω)
    (L α M xzero : ℝ) (lam : Fin n → ℝ)
    (hL : 0 < L)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4)
    (hobj : ∀ i (x : Point 1),
      S.localObjective i x = lam i * (x 0) ^ 2 / 2 +
        M * unboundedHeterogeneityDirection S.network α lam i * x 0)
    (hinit : ∀ k : Fin 1, S.initialPoint k = xzero)
    (hnoise : ∀ t omega i, S.noise t omega i = 0) :
    (arithmeticMean S omega α 2) 0 =
      (n : ℝ)⁻¹ *
        ((∑ i, ∑ j, S.rowMix 1 i j *
            (xzero - α * (lam j * xzero))) -
          α * ∑ i, lam i * (xzero - α * (lam i * xzero))) +
      M * (α / (n : ℝ) *
        ∑ i, unboundedHeterogeneityDirection S.network α lam i ^ 2) := by
  let v := unboundedHeterogeneityDirection S.network α lam
  have hvsum : ∑ i, v i = 0 := by
    simpa [v] using
      unboundedHeterogeneityDirection_sum_eq_zero S.network α lam
  have hdot :
      ∑ i, (α * lam i - ∑ j, S.rowMix 1 j i) * v i =
        ∑ i, v i ^ 2 := by
    simpa [v] using unbounded_direction_dot_eq_square S.network α lam
  have hrow :
      (∑ i, ∑ j, S.rowMix 1 i j *
          (xzero - α * (lam j * xzero + M * v j))) =
        (∑ i, ∑ j, S.rowMix 1 i j *
          (xzero - α * (lam j * xzero))) -
        α * M * ∑ j, (∑ i, S.rowMix 1 i j) * v j := by
    calc
      (∑ i, ∑ j, S.rowMix 1 i j *
          (xzero - α * (lam j * xzero + M * v j))) =
          ∑ i, ∑ j,
            (S.rowMix 1 i j * (xzero - α * (lam j * xzero)) -
              α * M * (S.rowMix 1 i j * v j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ∑ i,
          ((∑ j, S.rowMix 1 i j * (xzero - α * (lam j * xzero))) -
            ∑ j, α * M * (S.rowMix 1 i j * v j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_sub_distrib]
      _ = (∑ i, ∑ j, S.rowMix 1 i j *
            (xzero - α * (lam j * xzero))) -
          ∑ i, ∑ j, α * M * (S.rowMix 1 i j * v j) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ i, ∑ j, S.rowMix 1 i j *
            (xzero - α * (lam j * xzero))) -
          α * M * ∑ i, ∑ j, S.rowMix 1 i j * v j := by
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = (∑ i, ∑ j, S.rowMix 1 i j *
            (xzero - α * (lam j * xzero))) -
          α * M * ∑ j, ∑ i, S.rowMix 1 i j * v j := by
            have hswap :
                (∑ i, ∑ j, S.rowMix 1 i j * v j) =
                  ∑ j, ∑ i, S.rowMix 1 i j * v j := by
              exact Finset.sum_comm
            rw [hswap]
      _ = (∑ i, ∑ j, S.rowMix 1 i j *
            (xzero - α * (lam j * xzero))) -
          α * M * ∑ j, (∑ i, S.rowMix 1 i j) * v j := by
            congr 2
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_mul]
  have hlocal :
      (∑ i, (lam i * (xzero - α * (lam i * xzero + M * v i)) +
          M * v i)) =
        (∑ i, lam i * (xzero - α * (lam i * xzero))) +
          M * ∑ i, (1 - α * lam i) * v i := by
    calc
      (∑ i, (lam i * (xzero - α * (lam i * xzero + M * v i)) +
          M * v i)) =
          ∑ i, (lam i * (xzero - α * (lam i * xzero)) +
            M * ((1 - α * lam i) * v i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i, lam i * (xzero - α * (lam i * xzero))) +
          ∑ i, M * ((1 - α * lam i) * v i) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ i, lam i * (xzero - α * (lam i * xzero))) +
          M * ∑ i, (1 - α * lam i) * v i := by
            rw [Finset.mul_sum]
  have hcoeff :
      -(α * M * ∑ j, (∑ i, S.rowMix 1 i j) * v j) -
          α * (M * ∑ i, (1 - α * lam i) * v i) =
        α * M *
          ((∑ i, (α * lam i - ∑ j, S.rowMix 1 j i) * v i) -
            ∑ i, v i) := by
    have hleft :
        ∑ i, (1 - α * lam i) * v i =
          (∑ i, v i) - α * ∑ i, lam i * v i := by
      calc
        ∑ i, (1 - α * lam i) * v i =
            ∑ i, (v i - α * (lam i * v i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (∑ i, v i) - ∑ i, α * (lam i * v i) := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ i, v i) - α * ∑ i, lam i * v i := by
              rw [Finset.mul_sum]
    have hright :
        ∑ i, (α * lam i - ∑ j, S.rowMix 1 j i) * v i =
          α * ∑ i, lam i * v i -
            ∑ i, (∑ j, S.rowMix 1 j i) * v i := by
      calc
        ∑ i, (α * lam i - ∑ j, S.rowMix 1 j i) * v i =
            ∑ i, (α * (lam i * v i) -
              (∑ j, S.rowMix 1 j i) * v i) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = (∑ i, α * (lam i * v i)) -
            ∑ i, (∑ j, S.rowMix 1 j i) * v i := by
              rw [Finset.sum_sub_distrib]
        _ = α * ∑ i, lam i * v i -
            ∑ i, (∑ j, S.rowMix 1 j i) * v i := by
              rw [Finset.mul_sum]
    rw [hleft, hright]
    ring
  rw [unbounded_quadratic_second_mean_raw S omega L α M xzero lam v
    hL hlam (by simpa [v] using hobj) hinit hnoise]
  rw [hrow, hlocal]
  change (n : ℝ)⁻¹ *
      ((∑ i, ∑ j, S.rowMix 1 i j * (xzero - α * (lam j * xzero))) -
        α * M * ∑ j, (∑ i, S.rowMix 1 i j) * v j -
        α * ((∑ i, lam i * (xzero - α * (lam i * xzero))) +
          M * ∑ i, (1 - α * lam i) * v i)) = _
  rw [show
    (∑ i, ∑ j, S.rowMix 1 i j * (xzero - α * (lam j * xzero))) -
          α * M * ∑ j, (∑ i, S.rowMix 1 i j) * v j -
          α * ((∑ i, lam i * (xzero - α * (lam i * xzero))) +
            M * ∑ i, (1 - α * lam i) * v i) =
      ((∑ i, ∑ j, S.rowMix 1 i j * (xzero - α * (lam j * xzero))) -
        α * ∑ i, lam i * (xzero - α * (lam i * xzero))) +
      (-(α * M * ∑ j, (∑ i, S.rowMix 1 i j) * v j) -
        α * (M * ∑ i, (1 - α * lam i) * v i)) by ring]
  rw [hcoeff, hvsum, sub_zero, hdot]
  dsimp [v]
  ring

/-- The projected-square coefficient in the verification supplement for (66)
is strictly positive for the T1 witness. -/
private theorem unbounded_projected_square_coefficient_pos
    (N : NetworkSetup n) (α : ℝ) (lam : Fin n → ℝ) (hα : 0 < α)
    (hv : unboundedHeterogeneityDirection N α lam ≠ 0) :
    0 < α / (n : ℝ) *
      ∑ i, unboundedHeterogeneityDirection N α lam i ^ 2 := by
  let v := unboundedHeterogeneityDirection N α lam
  have hv' : v ≠ 0 := hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv'
  have hi' : v i ≠ 0 := by simpa using hi
  have hsquare : 0 < ∑ j, v j ^ 2 := by
    have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hi') hle
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr N.hn
  change 0 < α / (n : ℝ) * ∑ i, v i ^ 2
  exact mul_pos (div_pos hα hn) hsquare

/-- The time-two term of the stationarity output retains the positive
quadratic response generated by the affine second mean. -/
private theorem unbounded_quadratic_time_two_cost_lower
    (S : Setup n 1 Ω) (T : PositiveHorizon) (hT : 3 ≤ T.1)
    (L α M xzero : ℝ) (lam : Fin n → ℝ)
    (hL : 0 < L)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4)
    (hobj : ∀ i (x : Point 1),
      S.localObjective i x = lam i * (x 0) ^ 2 / 2 +
        M * unboundedHeterogeneityDirection S.network α lam i * x 0)
    (hinit : ∀ k : Fin 1, S.initialPoint k = xzero)
    (hnoise : ∀ t omega i, S.noise t omega i = 0) :
    (T.1 : ℝ)⁻¹ * averageCurvature lam ^ 2 *
        ((n : ℝ)⁻¹ *
          ((∑ i, ∑ j, S.rowMix 1 i j *
              (xzero - α * (lam j * xzero))) -
            α * ∑ i, lam i * (xzero - α * (lam i * xzero))) +
          M * (α / (n : ℝ) *
            ∑ i, unboundedHeterogeneityDirection S.network α lam i ^ 2)) ^ 2 ≤
      stationarityError S α T := by
  classical
  let v := unboundedHeterogeneityDirection S.network α lam
  let q := averageCurvature lam
  let c : ℝ := (n : ℝ)⁻¹ *
    ((∑ i, ∑ j, S.rowMix 1 i j *
        (xzero - α * (lam j * xzero))) -
      α * ∑ i, lam i * (xzero - α * (lam i * xzero)))
  let b : ℝ := α / (n : ℝ) * ∑ i, v i ^ 2
  have hvsum : ∑ i, v i = 0 := by
    simpa [v] using
      unboundedHeterogeneityDirection_sum_eq_zero S.network α lam
  have heval_sum (Z : Fin n → Point 1) :
      (∑ i, Z i) (0 : Fin 1) = ∑ i, (Z i) 0 := by
    let p := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) (0 : Fin 1)
    change p (∑ i, Z i) = ∑ i, p (Z i)
    exact map_sum p Z Finset.univ
  have hlocalGrad (i : Fin n) (x : Point 1) :
      gradient (S.localObjective i) x =
        PiLp.single 2 (0 : Fin 1) (lam i * x 0 + M * v i) := by
    have hli0 : 0 ≤ lam i := le_trans (by positivity) (hlam i).1
    have hliL : lam i ≤ L := by nlinarith [(hlam i).2]
    have hfun : S.localObjective i =
        fun z : Point 1 => lam i * (z 0) ^ 2 / 2 + M * v i * z 0 := by
      funext z
      simpa [v] using hobj i z
    rw [hfun]
    exact (unbounded_quadratic_local_objective_spec
      L (lam i) (M * v i) hL hli0 hliL).2 x
  have havgGrad (x : Point 1) :
      gradient (averageObjective S) x =
        PiLp.single 2 (0 : Fin 1) (q * x 0) := by
    have havg := SOptLib.finiteAverageObjective_hasGradientAt
      S.localObjective (fun i z => gradient (S.localObjective i) z) x
      (fun i => ((S.local_smooth i).1 x).hasGradientAt)
    calc
      gradient (averageObjective S) x =
          (n : ℝ)⁻¹ • ∑ i, gradient (S.localObjective i) x := by
            simpa only [averageObjective, Fintype.card_fin] using havg.gradient
      _ = PiLp.single 2 (0 : Fin 1) (q * x 0) := by
        ext k
        fin_cases k
        change (n : ℝ)⁻¹ *
          (∑ i, gradient (S.localObjective i) x) (0 : Fin 1) = q * x 0
        rw [heval_sum]
        simp_rw [hlocalGrad]
        simp only [PiLp.single_apply, if_pos]
        calc
          (n : ℝ)⁻¹ * ∑ i, (lam i * x 0 + M * v i) =
              (n : ℝ)⁻¹ * ((∑ i, lam i) * x 0 + M * ∑ i, v i) := by
                rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
          _ = q * x 0 := by
            rw [hvsum]
            dsimp [q, averageCurvature]
            ring
  have haffine (omega : Ω) :
      (arithmeticMean S omega α 2) 0 = c + M * b := by
    simpa [c, b, v] using
      unbounded_quadratic_second_mean_affine S omega L α M xzero lam
        hL hlam hobj hinit hnoise
  have hintegrand (omega : Ω) :
      stationarityIntegrand S α 2 omega = q ^ 2 * (c + M * b) ^ 2 := by
    unfold stationarityIntegrand
    rw [havgGrad, PiLp.norm_single, haffine]
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  have hexpect :
      SOptLib.expectation S.probability (stationarityIntegrand S α 2) =
        q ^ 2 * (c + M * b) ^ 2 := by
    letI : IsProbabilityMeasure S.probability := S.is_probability
    unfold SOptLib.expectation
    rw [show stationarityIntegrand S α 2 =
        fun _ : Ω => q ^ 2 * (c + M * b) ^ 2 by
      funext omega
      exact hintegrand omega]
    simp
  have hsingle :
      SOptLib.expectation S.probability (stationarityIntegrand S α 2) ≤
        ∑ t ∈ Finset.range T.1,
          SOptLib.expectation S.probability (stationarityIntegrand S α t) := by
    let f : ℕ → ℝ := fun t =>
      SOptLib.expectation S.probability (stationarityIntegrand S α t)
    change f 2 ≤ ∑ t ∈ Finset.range T.1, f t
    exact Finset.single_le_sum (s := Finset.range T.1) (a := 2)
      (fun t ht => by
        dsimp [f, SOptLib.expectation]
        exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
      (by simp; omega)
  unfold stationarityError
  rw [hexpect] at hsingle
  have hscaled := mul_le_mul_of_nonneg_left hsingle
    (inv_nonneg.mpr (Nat.cast_nonneg T.1))
  simpa [q, c, b, v, mul_assoc] using hscaled

/-- A positive multiple of a real affine square is unbounded along the
positive scale ray, expressed in the ENNReal supremum used by minimax risk. -/
private theorem iSup_ennreal_ofReal_pos_mul_affine_sq_eq_top
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (⨆ M : {M : ℝ // 0 < M},
      ENNReal.ofReal (a * (c + M.1 * b) ^ 2)) = ⊤ := by
  apply (iSup_eq_top _).2
  intro z hz
  have hznonneg : 0 ≤ z.toReal := ENNReal.toReal_nonneg
  let m : ℝ := (|c| + 2 + z.toReal / a) / b
  have hmpos : 0 < m := by
    dsimp [m]
    apply div_pos
    · have : 0 < |c| + 2 := by positivity
      exact add_pos_of_pos_of_nonneg this (div_nonneg hznonneg ha.le)
    · exact hb
  let M : {M : ℝ // 0 < M} := ⟨m, hmpos⟩
  refine ⟨M, ?_⟩
  have hlinear : c + m * b = c + |c| + 2 + z.toReal / a := by
    dsimp [m]
    field_simp [hb.ne']
    ring
  have hcabs : 0 ≤ c + |c| := by
    have hc := neg_le_abs c
    linarith
  have hxone : 1 < c + m * b := by
    rw [hlinear]
    nlinarith [div_nonneg hznonneg ha.le]
  have hxa : z.toReal < a * (c + m * b) := by
    have hdiv : a * (z.toReal / a) = z.toReal := by
      field_simp [ha.ne']
    rw [hlinear]
    nlinarith [mul_pos ha (show 0 < c + |c| + 1 by nlinarith)]
  have hxsq : c + m * b < (c + m * b) ^ 2 := by
    have hxpos : 0 < c + m * b := lt_trans (by norm_num) hxone
    nlinarith [mul_pos hxpos (sub_pos.mpr hxone)]
  have hreal : z.toReal < a * (c + m * b) ^ 2 :=
    lt_trans hxa (mul_lt_mul_of_pos_left hxsq ha)
  rw [← ENNReal.ofReal_toReal (ne_of_lt hz)]
  exact (ENNReal.ofReal_lt_ofReal_iff
    (lt_of_le_of_lt hznonneg hreal)).2 hreal

/-- The legal quadratic family has infinite fixed-stepsize cost supremum. -/
private theorem unbounded_quadratic_family_cost_iSup_eq_top
    (N : NetworkSetup n) (L Δ σ α : ℝ)
    (T : PositiveHorizon) (hT : 3 ≤ T.1)
    (hL : 0 < L) (hα : 0 < α)
    (lam : Fin n → ℝ)
    (hlam : ∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4)
    (hv : unboundedHeterogeneityDirection N α lam ≠ 0)
    (I : {M : ℝ // 0 < M} → FiniteInstance n)
    (hI : ∀ M,
      I M ∈ unrestrictedInstanceClass N L Δ σ ∧
      IsUnboundedQuadraticFamilyInstance (I M) lam
        (unboundedHeterogeneityDirection N α lam) M.1 Δ ∧
      (∀ t omega i,
        @Setup.noise n (I M).d (I M).Ω (I M).measurableSpace
          (I M).setup t omega i = 0)) :
    (⨆ M : {M : ℝ // 0 < M},
      ENNReal.ofReal (FiniteInstance.cost (I M) α T)) = ⊤ := by
  classical
  let v := unboundedHeterogeneityDirection N α lam
  let q := averageCurvature lam
  let c : ℝ := (n : ℝ)⁻¹ *
    ((∑ i, ∑ j, N.rowMix 1 i j *
        (Real.sqrt (2 * Δ / q) - α *
          (lam j * Real.sqrt (2 * Δ / q)))) -
      α * ∑ i, lam i *
        (Real.sqrt (2 * Δ / q) - α *
          (lam i * Real.sqrt (2 * Δ / q))))
  let b : ℝ := α / (n : ℝ) * ∑ i, v i ^ 2
  let a : ℝ := (T.1 : ℝ)⁻¹ * q ^ 2
  have hqpos : 0 < q := by
    simpa [q] using (averageCurvature_bounds N L hL lam hlam).2.2
  have hb : 0 < b := by
    simpa [b, v] using
      unbounded_projected_square_coefficient_pos N α lam hα hv
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr T.2)) (sq_pos_of_pos hqpos)
  have hscalar :
      (⨆ M : {M : ℝ // 0 < M},
        ENNReal.ofReal (a * (c + M.1 * b) ^ 2)) = ⊤ :=
    iSup_ennreal_ofReal_pos_mul_affine_sq_eq_top a b c ha hb
  apply top_unique
  rw [← hscalar]
  apply iSup_le
  intro M
  let J : FiniteInstance n := I M
  have hJ : J = I M := rfl
  have hdata :
      J ∈ unrestrictedInstanceClass N L Δ σ ∧
      IsUnboundedQuadraticFamilyInstance J lam
        (unboundedHeterogeneityDirection N α lam) M.1 Δ ∧
      (∀ t omega i,
        @Setup.noise n J.d J.Ω J.measurableSpace J.setup t omega i = 0) := by
    simpa [J] using hI M
  rcases J with ⟨d, ΩM, S, hfinite⟩
  rcases hdata with ⟨hmem, ⟨hd, hobj, hinit⟩, hnoise⟩
  change d = 1 at hd
  subst d
  have hnet : S.network = N := hmem.1
  have hobj' : ∀ i (x : Point 1),
      S.localObjective i x =
        lam i * (x 0) ^ 2 / 2 + M.1 *
          unboundedHeterogeneityDirection S.network α lam i * x 0 := by
    intro i x
    rw [hnet]
    simpa using hobj i x
  have hinit' : ∀ k : Fin 1,
      S.initialPoint k = Real.sqrt (2 * Δ / q) := by
    intro k
    simpa [q] using hinit k
  have hlower := unbounded_quadratic_time_two_cost_lower
    S T hT L α M.1 (Real.sqrt (2 * Δ / q)) lam
    hL hlam hobj' hinit' hnoise
  rw [hnet] at hlower
  have hlower' : a * (c + M.1 * b) ^ 2 ≤
      FiniteInstance.cost
        { d := 1, Ω := ΩM, setup := S, finite_layer := hfinite } α T := by
    simpa [a, b, c, q, v, Setup.rowMix, hnet,
      FiniteInstance.cost, mul_assoc] using hlower
  have hlowerI : a * (c + M.1 * b) ^ 2 ≤
      FiniteInstance.cost (I M) α T := by
    simpa only [hJ] using hlower'
  exact le_iSup_of_le M (ENNReal.ofReal_le_ofReal hlowerI)

/-- Pointwise family membership lifts its infinite supremum to the full
unrestricted instance class. -/
private theorem unrestricted_cost_iSup_eq_top_of_family
    (N : NetworkSetup n) (L Δ σ α : ℝ) (T : PositiveHorizon)
    (I : {M : ℝ // 0 < M} → FiniteInstance n)
    (hmem : ∀ M, I M ∈ unrestrictedInstanceClass N L Δ σ)
    (hfamilyTop :
      (⨆ M : {M : ℝ // 0 < M},
        ENNReal.ofReal (FiniteInstance.cost (I M) α T)) = ⊤) :
    (⨆ J : unrestrictedInstanceClass N L Δ σ,
      ENNReal.ofReal (FiniteInstance.cost J.1 α T)) = ⊤ := by
  apply top_unique
  rw [← hfamilyTop]
  apply iSup_le
  intro M
  exact le_iSup_of_le ⟨I M, hmem M⟩ le_rfl

/-- If every positive stepsize has infinite unrestricted cost supremum, the
source-ordered infimum over stepsizes remains infinite. -/
private theorem minimaxRisk_eq_top_of_all_stepsize_iSup_top
    (N : NetworkSetup n) (L Δ σ : ℝ) (T : PositiveHorizon)
    (htop : ∀ α : ℝ, 0 < α →
      (⨆ I : unrestrictedInstanceClass N L Δ σ,
        ENNReal.ofReal (FiniteInstance.cost I.1 α T)) = ⊤) :
    minimaxRisk (unrestrictedInstanceClass N L Δ σ) T = ⊤ := by
  apply top_unique
  unfold minimaxRisk
  apply le_iInf
  intro α
  rw [htop α.1 α.2]

/-- The homogeneous exact quadratic has zero realized noise but may declare
any admissible noise scale, so its time-zero term lower-bounds the unrestricted
class at every horizon. -/
private theorem unrestricted_time_zero_minimax_lower
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ)
    (T : PositiveHorizon) :
    ENNReal.ofReal (2 * ADelta L Δ / (T.1 : ℝ)) ≤
      minimaxRisk (unrestrictedInstanceClass N L Δ σ) T := by
  have hwitness := deterministic_quadratic_time_zero_witness
    N L Δ σ 0 hL hΔ hσ le_rfl T
  unfold minimaxRisk
  apply le_iInf
  intro α
  obtain ⟨I, hcost⟩ := hwitness α.1 α.2
  let J : unrestrictedInstanceClass N L Δ σ :=
    ⟨I.1, I.2.1, I.2.2.1, I.2.2.2.1, I.2.2.2.2.1⟩
  exact le_iSup_of_le J (ENNReal.ofReal_le_ofReal hcost)

/-- With one node the average objective is the sole local objective, so the
initial gradient disagreement vanishes in every unrestricted instance. -/
private theorem one_node_unrestricted_initial_heterogeneity_eq_zero
    (N : NetworkSetup n) (L Δ σ : ℝ) (hn1 : n = 1) :
    ∀ I : unrestrictedInstanceClass N L Δ σ,
      @initialHeterogeneitySq n I.1.d I.1.Ω I.1.measurableSpace I.1.setup = 0 := by
  subst n
  intro I
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  let S := I.1.setup
  have havg : averageObjective S = S.localObjective 0 := by
    funext x
    simp [averageObjective]
  unfold initialHeterogeneitySq
  rw [havg]
  simp [S]

/-- The first arithmetic mean is the common initial point minus the averaged
initial stochastic oracle.  This identity is sample-space independent. -/
private theorem arithmeticMean_one_eq_initial_sub_average_oracle
    (S : Setup n d Ω) (omega : Ω) (α : ℝ) :
    arithmeticMean S omega α 1 =
      S.initialPoint - α • ((n : ℝ)⁻¹ • ∑ i, sampledOracle S omega α 0 i) := by
  classical
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt S.hn)
  have hrow (i : Fin n) : ∑ j, S.rowMix 0 i j = 1 :=
    Matrix.sum_row_of_mem_rowStochastic (S.row_stochastic 0) i
  rw [show arithmeticMean S omega α 1 =
      (n : ℝ)⁻¹ • ∑ i,
        (leftAct (S.rowMix 0) (primal S omega α 0) i -
          α • tracker S omega α 0 i) by
    unfold arithmeticMean
    congr 1]
  simp only [primal_zero, tracker_zero]
  have hmix (i : Fin n) :
      leftAct (S.rowMix 0) (fun _ : Fin n => S.initialPoint) i =
        S.initialPoint := by
    unfold leftAct
    rw [Matrix.smulVec_apply]
    calc
      (∑ j, S.rowMix 0 i j • S.initialPoint) =
          (∑ j, S.rowMix 0 i j) • S.initialPoint := by
            rw [Finset.sum_smul]
      _ = S.initialPoint := by rw [hrow]; simp
  simp_rw [hmix]
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.smul_sum]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
    inv_mul_cancel₀ hn0, one_smul, smul_smul]
  simp only [smul_smul, mul_comm]

/-- The uniform average of one noise table has expected squared norm at most
the declared per-node noise scale squared. -/
private theorem average_noise_expected_norm_sq_le
    (S : Setup n d Ω) (t : ℕ) :
    SOptLib.expectation S.probability
        (fun omega => ‖(n : ℝ)⁻¹ • ∑ i, S.noise t omega i‖ ^ 2) ≤
      S.σ ^ 2 := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt S.hn)
  have hmom := (weighted_noise_conditional_moments S t
    (fun _ : Fin n => (n : ℝ)⁻¹)).2
  have hint : Integrable
      (fun omega => ‖∑ i, (n : ℝ)⁻¹ • S.noise t omega i‖ ^ 2)
      S.probability := hmom.1.integrable
  have hbound :
      (∫ omega, ‖∑ i, (n : ℝ)⁻¹ • S.noise t omega i‖ ^ 2
        ∂S.probability) ≤
        S.σ ^ 2 * ∑ _i : Fin n, ((n : ℝ)⁻¹) ^ 2 := by
    calc
      _ = ∫ omega, MeasureTheory.condExp (preSamplingHistory S t)
          S.probability
          (fun omega => ‖∑ i, (n : ℝ)⁻¹ • S.noise t omega i‖ ^ 2) omega
          ∂S.probability := hmom.1.integral_condExp.symm
      _ ≤ ∫ _omega : Ω,
          S.σ ^ 2 * ∑ _i : Fin n, ((n : ℝ)⁻¹) ^ 2
          ∂S.probability := by
        apply MeasureTheory.integral_mono_ae MeasureTheory.integrable_condExp
          (integrable_const _)
        exact hmom.2
      _ = S.σ ^ 2 * ∑ _i : Fin n, ((n : ℝ)⁻¹) ^ 2 := by simp
  rw [show (fun omega => ‖(n : ℝ)⁻¹ • ∑ i, S.noise t omega i‖ ^ 2) =
      (fun omega => ‖∑ i, (n : ℝ)⁻¹ • S.noise t omega i‖ ^ 2) by
    funext omega
    rw [Finset.smul_sum]]
  unfold SOptLib.expectation
  calc
    (∫ omega, ‖∑ i, (n : ℝ)⁻¹ • S.noise t omega i‖ ^ 2
        ∂S.probability) ≤
        S.σ ^ 2 * ∑ _i : Fin n, ((n : ℝ)⁻¹) ^ 2 := hbound
    _ = S.σ ^ 2 * (n : ℝ)⁻¹ := by
      have hcoeff : ∑ _i : Fin n, ((n : ℝ)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp [hn0]
      rw [hcoeff]
    _ ≤ S.σ ^ 2 := by
      have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast S.hn
      have hinv : (n : ℝ)⁻¹ ≤ 1 :=
        (inv_le_one₀ (show 0 < (n : ℝ) by positivity)).2 hnreal
      nlinarith [sq_nonneg S.σ]

/-- Smoothness and the exact initial gap bound the squared gradient of the
average objective at the common initial point. -/
private theorem initial_average_gradient_sq_le
    (S : Setup n d Ω) :
    ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 ≤
      2 * S.L * S.Δ := by
  let z := S.initialPoint
  let g := gradient (averageObjective S) z
  let znext := z - S.L⁻¹ • g
  have hsmooth := average_objective_smooth_interface S znext z
  have hstep : znext - z = (-S.L⁻¹) • g := by
    dsimp [znext]
    module
  rw [hstep, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (inv_pos.mpr S.hL), mul_pow] at hsmooth
  have hinv : 0 < S.L⁻¹ := inv_pos.mpr S.hL
  have hcancel : S.L * S.L⁻¹ = 1 := mul_inv_cancel₀ S.hL.ne'
  have hsmooth' : averageObjective S znext - averageObjective S z +
      S.L⁻¹ * ‖g‖ ^ 2 ≤
    S.L / 2 * (S.L⁻¹ ^ 2 * ‖g‖ ^ 2) := by
    dsimp [g]
    nlinarith [hsmooth]
  have hcoef : S.L / 2 * S.L⁻¹ ^ 2 = S.L⁻¹ / 2 := by
    field_simp [S.hL.ne']
  rw [← mul_assoc, hcoef] at hsmooth'
  have hdescent :
      (2 * S.L)⁻¹ * ‖g‖ ^ 2 ≤
        averageObjective S z - averageObjective S znext := by
    have htwo : (2 * S.L)⁻¹ = S.L⁻¹ / 2 := by
      field_simp [S.hL.ne']
    rw [htwo]
    nlinarith [hsmooth', sq_nonneg ‖g‖]
  have hinf :
      sInf (Set.range (averageObjective S)) ≤ averageObjective S znext := by
    exact csInf_le S.average_lower_bounded ⟨znext, rfl⟩
  have hgap :
      averageObjective S z - sInf (Set.range (averageObjective S)) = S.Δ := by
    simpa [averageObjective] using S.exact_initial_gap
  have hscaled : ‖g‖ ^ 2 ≤
      (2 * S.L) * (averageObjective S z - averageObjective S znext) := by
    have hpos : 0 < 2 * S.L := mul_pos (by norm_num) S.hL
    have := mul_le_mul_of_nonneg_left hdescent hpos.le
    calc
      ‖g‖ ^ 2 = (2 * S.L) * ((2 * S.L)⁻¹ * ‖g‖ ^ 2) := by
        field_simp [S.hL.ne']
      _ ≤ (2 * S.L) *
          (averageObjective S z - averageObjective S znext) := this
  dsimp [g, z] at hscaled ⊢
  nlinarith

/-- At horizon two the only stochastic displacement is one averaged oracle
step.  Its excess stationarity cost is linear in a stepsize bounded by one,
with a coefficient independent of the instance heterogeneity bound. -/
private theorem stationarityError_two_le_initial_plus_linear
    (S : Setup n d Ω) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    stationarityError S α ⟨2, by omega⟩ ≤
      ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
        α * (S.L * ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
          2 * (S.L + S.L ^ 2) *
            (‖gradient (averageObjective S) S.initialPoint‖ ^ 2 + S.σ ^ 2)) := by
  classical
  letI : IsProbabilityMeasure S.probability := S.is_probability
  let g : Point d := gradient (averageObjective S) S.initialPoint
  let eta : Ω → Point d := fun omega =>
    (n : ℝ)⁻¹ • ∑ i, S.noise 0 omega i
  let u : Ω → Point d := fun omega => g + eta omega
  have havggrad :
      (n : ℝ)⁻¹ • ∑ i,
          gradient (S.localObjective i) S.initialPoint = g := by
    have havg := SOptLib.finiteAverageObjective_hasGradientAt
      S.localObjective (fun i x => gradient (S.localObjective i) x)
      S.initialPoint (fun i => ((S.local_smooth i).1 _).hasGradientAt)
    simpa only [g, averageObjective, Fintype.card_fin] using havg.gradient.symm
  have hmean (omega : Ω) :
      arithmeticMean S omega α 1 = S.initialPoint - α • u omega := by
    rw [arithmeticMean_one_eq_initial_sub_average_oracle]
    simp_rw [sampledOracle_eq_gradient_add_noise, primal_zero]
    rw [Finset.sum_add_distrib, smul_add, havggrad]
  have hetaMem : MemLp eta 2 S.probability := by
    have hsum : MemLp (fun omega => ∑ i, S.noise 0 omega i)
        2 S.probability := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (memLp_two_iff_integrable_sq_norm
        (noise_integrable S 0 i).aestronglyMeasurable).2
          (noise_norm_sq_integrable S 0 i)
    simpa only [eta] using hsum.const_smul ((n : ℝ)⁻¹)
  have huMem : MemLp u 2 S.probability := by
    exact (memLp_const g).add hetaMem
  have huInt : Integrable (fun omega => ‖u omega‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm huMem.aestronglyMeasurable).1 huMem
  have hetaInt : Integrable (fun omega => ‖eta omega‖ ^ 2) S.probability :=
    (memLp_two_iff_integrable_sq_norm hetaMem.aestronglyMeasurable).1 hetaMem
  have huExpected :
      SOptLib.expectation S.probability (fun omega => ‖u omega‖ ^ 2) ≤
        2 * ‖g‖ ^ 2 + 2 * S.σ ^ 2 := by
    have hpoint (omega : Ω) :
        ‖u omega‖ ^ 2 ≤ 2 * ‖g‖ ^ 2 + 2 * ‖eta omega‖ ^ 2 := by
      exact SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        g (eta omega)
    have hright : Integrable
        (fun omega : Ω => 2 * ‖g‖ ^ 2 + 2 * ‖eta omega‖ ^ 2)
        S.probability :=
      (integrable_const _).add (hetaInt.const_mul 2)
    have hmono := MeasureTheory.integral_mono huInt hright hpoint
    have hetaBound := average_noise_expected_norm_sq_le S 0
    unfold SOptLib.expectation at hmono hetaBound ⊢
    rw [MeasureTheory.integral_add (integrable_const _)
      (hetaInt.const_mul 2)] at hmono
    simp at hmono
    rw [MeasureTheory.integral_const_mul] at hmono
    change (∫ omega, ‖eta omega‖ ^ 2 ∂S.probability) ≤ S.σ ^ 2 at hetaBound
    nlinarith
  have hpointOne (omega : Ω) :
      stationarityIntegrand S α 1 omega ≤
        ‖g‖ ^ 2 + (S.L * α) * ‖g‖ ^ 2 +
          ((S.L * α) + (S.L * α) ^ 2) * ‖u omega‖ ^ 2 := by
    unfold stationarityIntegrand
    rw [hmean]
    have hLip := average_gradient_norm_sub_le S
      (S.initialPoint - α • u omega) S.initialPoint
    have hdisp :
        ‖(S.initialPoint - α • u omega) - S.initialPoint‖ =
          α * ‖u omega‖ := by
      rw [show (S.initialPoint - α • u omega) - S.initialPoint =
          (-α) • u omega by module,
        norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hα]
    rw [hdisp] at hLip
    have htri :
        ‖gradient (averageObjective S) (S.initialPoint - α • u omega)‖ ≤
          ‖g‖ + S.L * (α * ‖u omega‖) := by
      calc
        _ = ‖g + (gradient (averageObjective S)
              (S.initialPoint - α • u omega) - g)‖ := by
                congr 1
                dsimp [g]
                module
        _ ≤ ‖g‖ + ‖gradient (averageObjective S)
              (S.initialPoint - α • u omega) - g‖ := norm_add_le _ _
        _ ≤ ‖g‖ + S.L * (α * ‖u omega‖) := by
          dsimp [g] at hLip ⊢
          linarith
    have hrhs : 0 ≤ ‖g‖ + S.L * (α * ‖u omega‖) :=
      add_nonneg (norm_nonneg _)
        (mul_nonneg S.hL.le (mul_nonneg hα.le (norm_nonneg _)))
    have hsquare := (sq_le_sq₀ (norm_nonneg _) hrhs).2 htri
    have hyoung : 2 * ‖g‖ * ‖u omega‖ ≤
        ‖g‖ ^ 2 + ‖u omega‖ ^ 2 := by
      nlinarith [sq_nonneg (‖g‖ - ‖u omega‖)]
    have hscaled := mul_le_mul_of_nonneg_left hyoung
      (mul_nonneg S.hL.le hα.le)
    nlinarith
  have hOneInt := stationarityIntegrand_integrable S α 1
  have hcoef0 : 0 ≤ (S.L * α) + (S.L * α) ^ 2 :=
    add_nonneg (mul_nonneg S.hL.le hα.le) (sq_nonneg _)
  have hrightInt : Integrable
      (fun omega : Ω =>
        ‖g‖ ^ 2 + (S.L * α) * ‖g‖ ^ 2 +
          ((S.L * α) + (S.L * α) ^ 2) * ‖u omega‖ ^ 2)
      S.probability :=
    (integrable_const _).add (huInt.const_mul _)
  have hOneMono := MeasureTheory.integral_mono hOneInt hrightInt hpointOne
  have hOneExpected :
      SOptLib.expectation S.probability (stationarityIntegrand S α 1) ≤
        ‖g‖ ^ 2 + (S.L * α) * ‖g‖ ^ 2 +
          ((S.L * α) + (S.L * α) ^ 2) *
            (2 * ‖g‖ ^ 2 + 2 * S.σ ^ 2) := by
    unfold SOptLib.expectation at hOneMono huExpected ⊢
    rw [MeasureTheory.integral_add (integrable_const _)
      (huInt.const_mul _)] at hOneMono
    simp at hOneMono
    rw [MeasureTheory.integral_const_mul] at hOneMono
    have hmul := mul_le_mul_of_nonneg_left huExpected hcoef0
    exact hOneMono.trans (by nlinarith)
  have hmeanZero (omega : Ω) :
      arithmeticMean S omega α 0 = S.initialPoint := by
    simp only [arithmeticMean, primal_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    change (n : ℝ)⁻¹ • (n • S.initialPoint) = S.initialPoint
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt S.hn)
    rw [inv_mul_cancel₀ hn0, one_smul]
  have hZeroExpected :
      SOptLib.expectation S.probability (stationarityIntegrand S α 0) =
        ‖g‖ ^ 2 := by
    unfold SOptLib.expectation stationarityIntegrand
    rw [show (fun omega : Ω =>
        ‖gradient (averageObjective S) (arithmeticMean S omega α 0)‖ ^ 2) =
      (fun _ : Ω => ‖g‖ ^ 2) by
        funext omega
        rw [hmeanZero]
        ]
    simp
  unfold stationarityError
  rw [show (∑ t ∈ Finset.range 2,
      SOptLib.expectation S.probability (stationarityIntegrand S α t)) =
      SOptLib.expectation S.probability (stationarityIntegrand S α 0) +
        SOptLib.expectation S.probability (stationarityIntegrand S α 1) by
    simp [Finset.sum_range_succ]]
  rw [hZeroExpected]
  norm_num
  have hquad : (S.L * α) ^ 2 ≤ S.L ^ 2 * α := by
    nlinarith [S.hL.le]
  have hcoef : S.L * α + (S.L * α) ^ 2 ≤
      α * (S.L + S.L ^ 2) := by
    nlinarith
  have henergy0 : 0 ≤
      2 * ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
        2 * S.σ ^ 2 := by positivity
  have hcoefEnergy := mul_le_mul_of_nonneg_right hcoef henergy0
  dsimp [g] at hOneExpected ⊢
  have hOneFinal :
      SOptLib.expectation S.probability (stationarityIntegrand S α 1) ≤
        ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
          S.L * α * ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
          α * (S.L + S.L ^ 2) *
            (2 * ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
              2 * S.σ ^ 2) := by
    exact hOneExpected.trans (by nlinarith [hcoefEnergy])
  have hKnonneg : 0 ≤
      S.L * ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
        2 * (S.L + S.L ^ 2) *
          (‖gradient (averageObjective S) S.initialPoint‖ ^ 2 + S.σ ^ 2) := by
    exact add_nonneg
      (mul_nonneg S.hL.le
        (sq_nonneg ‖gradient (averageObjective S) S.initialPoint‖))
      (mul_nonneg
        (mul_nonneg (by norm_num) (add_nonneg S.hL.le (sq_nonneg S.L)))
        (add_nonneg
          (sq_nonneg ‖gradient (averageObjective S) S.initialPoint‖)
          (sq_nonneg S.σ)))
  have hαK := mul_nonneg hα.le hKnonneg
  nlinarith [hOneFinal, hαK, sq_nonneg S.σ,
    sq_nonneg ‖gradient (averageObjective S) S.initialPoint‖]

/-- At horizon one only the deterministic common initialization is observed,
so the unrestricted class is uniformly bounded by the smooth initial gap. -/
private theorem unrestricted_time_one_minimax_upper
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) :
    minimaxRisk (unrestrictedInstanceClass N L Δ σ) ⟨1, by omega⟩ ≤
      ENNReal.ofReal (2 * ADelta L Δ) := by
  unfold minimaxRisk
  refine iInf_le_of_le ⟨1, zero_lt_one⟩ ?_
  apply iSup_le
  intro I
  letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
  let S := I.1.setup
  have hLip : S.L = L := by
    simpa [S, FiniteInstance.lipschitz] using I.2.2.1
  have hgap : S.Δ = Δ := by
    simpa [S, FiniteInstance.gap] using I.2.2.2.1
  have hmean (omega : I.1.Ω) :
      arithmeticMean S omega 1 0 = S.initialPoint := by
    simp only [arithmeticMean, primal_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    change (n : ℝ)⁻¹ • (n • S.initialPoint) = S.initialPoint
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hn0 : (n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt S.hn)
    rw [inv_mul_cancel₀ hn0, one_smul]
  have hcost : FiniteInstance.cost I.1 1 ⟨1, by omega⟩ ≤
      2 * ADelta L Δ := by
    change stationarityError S 1 ⟨1, by omega⟩ ≤ _
    unfold stationarityError
    norm_num
    unfold SOptLib.expectation
    letI : IsProbabilityMeasure S.probability := S.is_probability
    rw [show stationarityIntegrand S 1 0 =
        fun _ : I.1.Ω =>
          ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 by
      funext omega
      unfold stationarityIntegrand
      rw [hmean]]
    simp only [integral_const]
    simp
    calc
      ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 ≤
          2 * S.L * S.Δ := initial_average_gradient_sq_le S
      _ = 2 * ADelta L Δ := by rw [hLip, hgap]; unfold ADelta; ring
  exact ENNReal.ofReal_le_ofReal hcost

/-- Sending the uniform one-step estimate to the positive-stepsize infimum
gives the source upper endpoint at horizon two. -/
private theorem unrestricted_time_two_minimax_upper
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) :
    minimaxRisk (unrestrictedInstanceClass N L Δ σ) ⟨2, by omega⟩ ≤
      ENNReal.ofReal (2 * ADelta L Δ) := by
  let C : ℝ := 2 * ADelta L Δ
  let K : ℝ :=
    L * C + 2 * (L + L ^ 2) * (C + σ ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C, ADelta]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (mul_nonneg hL.le hC)
      (mul_nonneg
        (mul_nonneg (by norm_num) (add_nonneg hL.le (sq_nonneg L)))
        (add_nonneg hC (sq_nonneg σ)))
  unfold minimaxRisk
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hfinite
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  let α : ℝ := min (1 / 2) ((ε : ℝ) / (K + 1))
  have hK1 : 0 < K + 1 := by linarith
  have hα : 0 < α := by
    dsimp [α]
    exact lt_min (by norm_num) (div_pos hεR hK1)
  have hα1 : α ≤ 1 := by
    exact (min_le_left _ _).trans (by norm_num)
  have hαK : α * K ≤ (ε : ℝ) := by
    have hαq : α ≤ (ε : ℝ) / (K + 1) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hαq hK
    have hfrac : (ε : ℝ) / (K + 1) * K ≤ (ε : ℝ) := by
      rw [show (ε : ℝ) / (K + 1) * K =
          ((ε : ℝ) * K) / (K + 1) by ring]
      exact (div_le_iff₀ hK1).2 (by nlinarith [mul_nonneg hεR.le hK])
    exact hmul.trans hfrac
  have hclass :
      (⨆ I : unrestrictedInstanceClass N L Δ σ,
        ENNReal.ofReal (FiniteInstance.cost I.1 α ⟨2, by omega⟩)) ≤
        ENNReal.ofReal (C + α * K) := by
    apply iSup_le
    intro I
    letI : MeasurableSpace I.1.Ω := I.1.measurableSpace
    let S := I.1.setup
    have hLip : S.L = L := by
      simpa [S, FiniteInstance.lipschitz] using I.2.2.1
    have hgap : S.Δ = Δ := by
      simpa [S, FiniteInstance.gap] using I.2.2.2.1
    have hnoise : S.σ = σ := by
      simpa [S, FiniteInstance.noiseScale] using I.2.2.2.2
    have hraw := stationarityError_two_le_initial_plus_linear S α hα hα1
    have hgrad := initial_average_gradient_sq_le S
    have hgradC :
        ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 ≤ C := by
      rw [hLip, hgap] at hgrad
      dsimp [C, ADelta]
      nlinarith
    have hcoefnonneg : 0 ≤ L + 2 * (L + L ^ 2) := by
      exact add_nonneg hL.le
        (mul_nonneg (by norm_num) (add_nonneg hL.le (sq_nonneg L)))
    have hgradScaled := mul_le_mul_of_nonneg_left hgradC hcoefnonneg
    have hlocalK :
        S.L * ‖gradient (averageObjective S) S.initialPoint‖ ^ 2 +
            2 * (S.L + S.L ^ 2) *
              (‖gradient (averageObjective S) S.initialPoint‖ ^ 2 + S.σ ^ 2) ≤
          K := by
      rw [hLip, hnoise]
      dsimp [K]
      nlinarith
    have hscaledK := mul_le_mul_of_nonneg_left hlocalK hα.le
    have hcost : FiniteInstance.cost I.1 α ⟨2, by omega⟩ ≤ C + α * K := by
      change stationarityError S α ⟨2, by omega⟩ ≤ _
      nlinarith
    exact ENNReal.ofReal_le_ofReal hcost
  calc
    (⨅ α : {a : ℝ // 0 < a},
        ⨆ I : unrestrictedInstanceClass N L Δ σ,
          ENNReal.ofReal (FiniteInstance.cost I.1 α.1 ⟨2, by omega⟩)) ≤
        ⨆ I : unrestrictedInstanceClass N L Δ σ,
          ENNReal.ofReal (FiniteInstance.cost I.1 α ⟨2, by omega⟩) :=
      iInf_le_of_le ⟨α, hα⟩ le_rfl
    _ ≤ ENNReal.ofReal (C + α * K) := hclass
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal (α * K) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal C + ε := by
      exact add_le_add_right (ENNReal.ofReal_le_coe.mpr hαK) _
    _ = ENNReal.ofReal (2 * ADelta L Δ) + ε := by rfl

/-- Equation (66) and all stated boundary cases.  The quantifier order keeps
one coherent positive-`M` quadratic family dependent on each fixed positive
stepsize. Book `#/key_lemmas/10/statement_math`:
“`sup_{M>0} E_T^{I_M}(α)=sup_{I in the unrestricted-H class} E_T^I(α)=+∞`”. -/
theorem unbounded_initial_heterogeneity
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) :
    (2 ≤ n → ∀ T : PositiveHorizon, 3 ≤ T.1 →
      (∀ α : ℝ, 0 < α →
        ∃ lam : Fin n → ℝ,
          (∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4) ∧
          unboundedHeterogeneityDirection N α lam ≠ 0 ∧
          ∃ I : {M : ℝ // 0 < M} → FiniteInstance n,
          (∀ M,
            I M ∈ unrestrictedInstanceClass N L Δ σ ∧
            IsUnboundedQuadraticFamilyInstance (I M) lam
              (unboundedHeterogeneityDirection N α lam) M.1 Δ) ∧
          (⨆ M : {M : ℝ // 0 < M},
            ENNReal.ofReal (FiniteInstance.cost (I M) α T)) = ⊤ ∧
          (⨆ I : unrestrictedInstanceClass N L Δ σ,
            ENNReal.ofReal (FiniteInstance.cost I.1 α T)) = ⊤) ∧
      minimaxRisk (unrestrictedInstanceClass N L Δ σ) T = ⊤) ∧
    (n = 1 → ∀ I : unrestrictedInstanceClass N L Δ σ,
      @initialHeterogeneitySq n I.1.d I.1.Ω I.1.measurableSpace I.1.setup = 0) ∧
    minimaxRisk (unrestrictedInstanceClass N L Δ σ) ⟨1, by omega⟩ =
      ENNReal.ofReal (2 * ADelta L Δ) ∧
    ENNReal.ofReal (ADelta L Δ) ≤
      minimaxRisk (unrestrictedInstanceClass N L Δ σ) ⟨2, by omega⟩ ∧
    minimaxRisk (unrestrictedInstanceClass N L Δ σ) ⟨2, by omega⟩ ≤
      ENNReal.ofReal (2 * ADelta L Δ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hn T hT
    have hfamilies : ∀ α : ℝ, 0 < α →
        ∃ lam : Fin n → ℝ,
          (∀ i, L / 4 ≤ lam i ∧ lam i ≤ 3 * L / 4) ∧
          unboundedHeterogeneityDirection N α lam ≠ 0 ∧
          ∃ I : {M : ℝ // 0 < M} → FiniteInstance n,
            (∀ M,
              I M ∈ unrestrictedInstanceClass N L Δ σ ∧
              IsUnboundedQuadraticFamilyInstance (I M) lam
                (unboundedHeterogeneityDirection N α lam) M.1 Δ) ∧
            (⨆ M : {M : ℝ // 0 < M},
              ENNReal.ofReal (FiniteInstance.cost (I M) α T)) = ⊤ ∧
            (⨆ I : unrestrictedInstanceClass N L Δ σ,
              ENNReal.ofReal (FiniteInstance.cost I.1 α T)) = ⊤ := by
      intro α hα
      obtain ⟨lam, hlam, hv, I, hI⟩ :=
        unbounded_quadratic_family_data N L Δ σ α hn hL hΔ hσ hα
      have hfamilyTop := unbounded_quadratic_family_cost_iSup_eq_top
        N L Δ σ α T hT hL hα lam hlam hv I hI
      have hunrestrictedTop := unrestricted_cost_iSup_eq_top_of_family
        N L Δ σ α T I (fun M => (hI M).1) hfamilyTop
      exact ⟨lam, hlam, hv, I,
        (fun M => ⟨(hI M).1, (hI M).2.1⟩),
        hfamilyTop, hunrestrictedTop⟩
    refine ⟨hfamilies, minimaxRisk_eq_top_of_all_stepsize_iSup_top
      N L Δ σ T ?_⟩
    intro α hα
    obtain ⟨lam, hlam, hv, I, hI, hfamilyTop, hunrestrictedTop⟩ :=
      hfamilies α hα
    exact hunrestrictedTop
  · exact one_node_unrestricted_initial_heterogeneity_eq_zero N L Δ σ
  · apply le_antisymm
    · exact unrestricted_time_one_minimax_upper N L Δ σ hL hΔ hσ
    · simpa using unrestricted_time_zero_minimax_lower
        N L Δ σ hL hΔ hσ ⟨1, by omega⟩
  · simpa using unrestricted_time_zero_minimax_lower
      N L Δ σ hL hΔ hσ ⟨2, by omega⟩
  · exact unrestricted_time_two_minimax_upper N L Δ σ hL hΔ hσ

end Algorithms.Unverified.GeneralPushPull

end
