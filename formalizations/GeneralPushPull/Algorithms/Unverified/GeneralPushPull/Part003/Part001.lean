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

/-- The reference-center growth between two shifted times is controlled by
the exponential of the intervening gain budget.  This is the product estimate
used in equation (39). -/
theorem loading_reference_ratio_le_exp_gain
    (N : NetworkSetup n) (s : ℝ) (k p m : ℕ)
    (hs : 0 ≤ s) (hpm : p ≤ m)
    (href_pos : ∀ q,
      0 < (loadingUnitCenterReferenceOrbit N s k q).1)
    (href_ratio : ∀ q,
      (loadingUnitCenterReferenceOrbit N s k (q + 1)).1 /
          (loadingUnitCenterReferenceOrbit N s k q).1 ≤
        1 + 3 * s * gain N (k + q) / 2) :
    (loadingUnitCenterReferenceOrbit N s k m).1 /
        (loadingUnitCenterReferenceOrbit N s k p).1 ≤
      Real.exp ((3 / 2) * s *
        ∑ t ∈ Finset.Ico (k + p) (k + m), gain N t) := by
  let R := loadingUnitCenterReferenceOrbit N s k
  induction m, hpm using Nat.le_induction with
  | base =>
      rw [div_self (ne_of_gt (href_pos p))]
      simp
  | @succ m hpm ih =>
      have hRm : 0 < (R m).1 := by simpa [R] using href_pos m
      have hRp : 0 < (R p).1 := by simpa [R] using href_pos p
      have hgain_nonneg : 0 ≤ gain N (k + m) := by
        unfold gain dotProduct
        exact Finset.sum_nonneg fun q _ =>
          mul_nonneg
            ((absoluteProbability_mem_stdSimplex N (k + m + 1)).1 q)
            (pushMass_nonneg N (k + m) q)
      have hstep : (R (m + 1)).1 / (R m).1 ≤
          Real.exp (3 * s * gain N (k + m) / 2) := by
        calc
          (R (m + 1)).1 / (R m).1 ≤
              1 + 3 * s * gain N (k + m) / 2 := by
            simpa [R] using href_ratio m
          _ ≤ Real.exp (3 * s * gain N (k + m) / 2) := by
            simpa [add_comm] using
              Real.add_one_le_exp (3 * s * gain N (k + m) / 2)
      have hratio_nonneg : 0 ≤ (R m).1 / (R p).1 :=
        div_nonneg hRm.le hRp.le
      have hstep_nonneg : 0 ≤ Real.exp (3 * s * gain N (k + m) / 2) :=
        (Real.exp_pos _).le
      have hfactor : (R (m + 1)).1 / (R p).1 =
          ((R (m + 1)).1 / (R m).1) * ((R m).1 / (R p).1) := by
        field_simp [ne_of_gt hRm, ne_of_gt hRp]
      rw [hfactor]
      calc
        (R (m + 1)).1 / (R m).1 * ((R m).1 / (R p).1) ≤
            Real.exp (3 * s * gain N (k + m) / 2) *
              ((R m).1 / (R p).1) :=
          mul_le_mul_of_nonneg_right hstep hratio_nonneg
        _ ≤ Real.exp (3 * s * gain N (k + m) / 2) *
            Real.exp ((3 / 2) * s *
              ∑ t ∈ Finset.Ico (k + p) (k + m), gain N t) :=
          mul_le_mul_of_nonneg_left ih hstep_nonneg
        _ = Real.exp ((3 / 2) * s *
              ∑ t ∈ Finset.Ico (k + p) (k + (m + 1)), gain N t) := by
          rw [← Real.exp_add]
          rw [show k + (m + 1) = k + m + 1 by omega,
            Finset.sum_Ico_succ_top (by omega : k + p ≤ k + m)]
          ring

/-- First-exit identification for equations (39)--(40).  A formally safe
slow/fast orbit, initialized by the genuine loaded state, stays on the true
negative-curvature branch; uniqueness of the normalized recurrence then
identifies the genuine and formal slow/fast states at every checked time. -/
theorem loading_formal_actual_branch_persistence
    (N : NetworkSetup n) (L D s a : ℝ) (j : ℕ) (i : Fin n)
    (k horizon : ℕ) (hL : 0 < L) (hD : 0 < D) (hs : 0 < s)
    (hjk : j < k)
    (href_pos : ∀ m,
      0 < (loadingUnitCenterReferenceOrbit N s k m).1) :
    let e := -a * D / ((s / L) * influenceRow N j i)
    let X : ℕ → Fin n → ℝ := fun r q =>
      (loadingTrajectory N L D s j i e r).primal q - D
    let U : ℕ → Fin n → ℝ := fun r q =>
      -retainedLoadingTracker N L D s j i e r q / L
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let xiFormal := loadingFormalCorrectedCenter N s k (xi k) (F k)
    let FFormal := loadingFormalFastState N s k (xi k) (F k)
    (∀ m, m ≤ horizon →
      |xiFormal m| +
          (nodeSupNorm (FFormal m).1 + nodeL1Norm (FFormal m).2) < D / 2) →
    ∀ m, m ≤ horizon →
      (∀ q,
        D / 2 ≤ (loadingTrajectory N L D s j i e (k + m)).primal q ∧
        (loadingTrajectory N L D s j i e (k + m)).primal q ≤ 3 * D / 2) ∧
      xi (k + m) = xiFormal m ∧ F (k + m) = FFormal m := by
  let e := -a * D / ((s / L) * influenceRow N j i)
  let X : ℕ → Fin n → ℝ := fun r q =>
    (loadingTrajectory N L D s j i e r).primal q - D
  let U : ℕ → Fin n → ℝ := fun r q =>
    -retainedLoadingTracker N L D s j i e r q / L
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let R := loadingUnitCenterReferenceOrbit N s k
  let G := loadingCorrectedTransverseOrbit N s k (F k)
  let xiFormal := loadingFormalCorrectedCenter N s k (xi k) (F k)
  let FFormal := loadingFormalFastState N s k (xi k) (F k)
  change (∀ m, m ≤ horizon →
      |xiFormal m| +
          (nodeSupNorm (FFormal m).1 + nodeL1Norm (FFormal m).2) < D / 2) →
    ∀ m, m ≤ horizon →
      (∀ q,
        D / 2 ≤ (loadingTrajectory N L D s j i e (k + m)).primal q ∧
        (loadingTrajectory N L D s j i e (k + m)).primal q ≤ 3 * D / 2) ∧
      xi (k + m) = xiFormal m ∧ F (k + m) = FFormal m
  intro hsafe
  have hbranch_of_identification (m : ℕ) (hm : m ≤ horizon)
      (hxi : xi (k + m) = xiFormal m)
      (hF : F (k + m) = FFormal m) :
      ∀ q,
        D / 2 ≤ (loadingTrajectory N L D s j i e (k + m)).primal q ∧
        (loadingTrajectory N L D s j i e (k + m)).primal q ≤ 3 * D / 2 := by
    intro q
    have hcoord : X (k + m) q = xi (k + m) + (F (k + m)).1 q := by
      simp only [F, loadingFastCoordinates]
      ring
    have hEsup : |(FFormal m).1 q| ≤ nodeSupNorm (FFormal m).1 :=
      abs_le_nodeSupNorm (FFormal m).1 q
    have hEfast : |(FFormal m).1 q| ≤
        nodeSupNorm (FFormal m).1 + nodeL1Norm (FFormal m).2 :=
      hEsup.trans (le_add_of_nonneg_right
        (Finset.sum_nonneg fun r _ => abs_nonneg _))
    have hshift : |X (k + m) q| < D / 2 := by
      rw [hcoord, hxi, hF]
      have hsum : |xiFormal m| + |(FFormal m).1 q| ≤
          |xiFormal m| +
            (nodeSupNorm (FFormal m).1 + nodeL1Norm (FFormal m).2) := by
        linarith
      exact (abs_add_le _ _).trans_lt
        (hsum.trans_lt (hsafe m hm))
    have hinterval := abs_lt.mp hshift
    constructor <;> dsimp [X] at hinterval ⊢ <;> linarith
  intro m hm
  induction m with
  | zero =>
      have hxi0 : xi (k + 0) = xiFormal 0 := by
        simp [xiFormal, loadingFormalCorrectedCenter]
      have hF0 : F (k + 0) = FFormal 0 := by
        ext q <;>
          simp [FFormal, loadingFormalFastState, G, R, loadingFastScale]
      exact ⟨hbranch_of_identification 0 hm hxi0 hF0, hxi0, hF0⟩
  | succ m ih =>
      have hm' : m ≤ horizon := by omega
      obtain ⟨hbranch, hxi_ident, hF_ident⟩ := ih hm'
      have hrec := loading_negative_branch_shifted_recurrence
        N L D s j i e (k + m) hL hD (by omega) hbranch
      have hsf := loading_negative_branch_slow_fast_coordinates
        N L D s a j i (k + m) (by
          simpa [e, X, U] using hrec)
      dsimp only at hsf
      have hxi_step : xi (k + m + 1) =
          (1 + s * gain N (k + m)) * xi (k + m) +
            s * dotProduct (absoluteProbability N (k + m + 1))
              ((F (k + m)).1 + (F (k + m)).2) := by
        simpa [e, X, U, xi, F] using hsf.2.1
      have hF_step : F (k + m + 1) =
          loadingPerturbedFastStep N s (k + m) (F (k + m)) +
            loadingFastScale s
              (loadingFastCenterInput N (k + m) (xi (k + m))) := by
        simpa [e, X, U, xi, F, loadingPerturbedFastStep] using hsf.2.2
      have hnormalized := loading_reference_normalized_residual_step
        N s k m xi F hxi_step hF_step
          (by simpa [R] using href_pos m)
          (by simpa [R] using href_pos (m + 1))
      let H : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
        loadingFastScale ((R r).1)⁻¹ (R r).2
      let Gactual : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
        F (k + r) - loadingFastScale (xi (k + r)) (H r)
      have hG_ident : Gactual m = G m := by
        change F (k + m) - loadingFastScale (xi (k + m)) (H m) = G m
        rw [hF_ident, hxi_ident]
        dsimp [xiFormal]
        simp [Gactual, FFormal, loadingFormalFastState, G, H, R]
      have hxi_next : xi (k + (m + 1)) = xiFormal (m + 1) := by
        rw [show k + (m + 1) = k + m + 1 by omega]
        have h := hnormalized.1
        change xi (k + m + 1) =
            ((R (m + 1)).1 / (R m).1) * xi (k + m) +
              s * dotProduct (absoluteProbability N (k + m + 1))
                ((Gactual m).1 + (Gactual m).2) at h
        rw [h, hxi_ident, hG_ident]
        rfl
      have hG_next : Gactual (m + 1) = G (m + 1) := by
        have h := hnormalized.2
        change Gactual (m + 1) =
            loadingPerturbedFastStep N s (k + m) (Gactual m) -
              loadingFastScale s
                (loadingFastScale
                  (dotProduct (absoluteProbability N (k + m + 1))
                    ((Gactual m).1 + (Gactual m).2))
                  (H (m + 1))) at h
        rw [h, hG_ident]
        simp only [G, loadingCorrectedTransverseOrbit_succ,
          loadingCorrectedTransverseStep,
          loadingCorrectedTransverseInnovation]
        simp [loadingPerturbedFastStep, H, R]
        abel
      have hF_next : F (k + (m + 1)) = FFormal (m + 1) := by
        change F (k + (m + 1)) =
          G (m + 1) + loadingFastScale (xiFormal (m + 1)) (H (m + 1))
        rw [← hG_next, ← hxi_next]
        change F (k + (m + 1)) =
          (F (k + (m + 1)) -
              loadingFastScale (xi (k + (m + 1))) (H (m + 1))) +
            loadingFastScale (xi (k + (m + 1))) (H (m + 1))
        abel
      exact ⟨hbranch_of_identification (m + 1) hm hxi_next hF_next,
        hxi_next, hF_next⟩

set_option maxHeartbeats 5000000
/-- Equations (21)--(40): a calibrated pulse reaches any sufficiently delayed
gain-budget window along the true nonlinear trajectory, while the tracker
generated during loading remains in the state.
Book `#/key_lemmas/3/statement_math`:
“`P\ge j+\tau(s)` ... `\Longrightarrow |V_D'(\bar x_t)|\ge LD/16`”. -/
theorem negative_curvature_loading
    (N : NetworkSetup n) (L : ℝ) (hL : 0 < L) :
    ∃ sLoad : ℝ, 0 < sLoad ∧ sLoad ≤ 1 / (64 * n) ∧
      ∀ (D s : ℝ), 0 < D → 0 < s → s ≤ sLoad →
      ∀ (j : ℕ) (i : Fin n), s ≤ |influenceRow N j i| →
      ∀ P Q : ℕ, j + loadingDelay N s ≤ P → P < Q →
        s * ∑ t ∈ Finset.Ico P Q, gain N t ≤ epsilon →
        ∃ a : ℝ, 3 / 4 ≤ a ∧ a ≤ 5 / 4 ∧
          let e := -a * D / ((s / L) * influenceRow N j i)
          (∀ t ∈ Finset.Ico P Q,
            L * D / 16 ≤
              |negativeCurvatureDerivative L D
                (loadingArithmeticMean N L D s j i e t)|) ∧
          (∀ t,
            retainedLoadingTracker N L D s j i e (t + 1) =
              N.colMix t *ᵥ retainedLoadingTracker N L D s j i e t +
                (N.colMix t - 1) *ᵥ
                  (fun k => negativeCurvatureDerivative L D
                    ((loadingTrajectory N L D s j i e t).primal k) +
                    loadingPulse j i e t k)) := by
  obtain ⟨sLoad, hsLoad, hsLoad_cap, hsLoad_geom⟩ :=
    loading_half_delay_geometric_budget N
  obtain ⟨Mtri, hMtri, hMtri_nonneg, htriangular⟩ :=
    exists_loading_triangular_product_constant N
  let M : ℝ := max 1 Mtri
  let J0 : ℝ := 2 * ((n : ℝ) + 1)
  have hM : 1 ≤ M := by exact le_max_left _ _
  have hMtri_le : Mtri ≤ M := by exact le_max_right _ _
  have hfast_lt_one : loadingFastRate N < 1 := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have htrans_lt_one : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate
    linarith
  have hgap : 0 < loadingTransverseRate N - loadingFastRate N := by
    unfold loadingTransverseRate
    linarith
  have hJ0 : 0 < J0 := by dsimp [J0]; positivity
  have hden : 0 < M * J0 := mul_pos (lt_of_lt_of_le zero_lt_one hM) hJ0
  let sPert : ℝ :=
    (loadingTransverseRate N - loadingFastRate N) / (M * J0)
  have hsPert : 0 < sPert := by dsimp [sPert]; positivity
  let B0 : ℝ := 2 * (n : ℝ) * ((n : ℝ) + 1)
  let Cp : ℝ := M * B0 / (1 - loadingTransverseRate N)
  let Cseed : ℝ := 1 / 16 +
    (((blockContraction N)⁻¹ * (n : ℝ)) /
      (1 - mixingRate N) + 5 / 4) + 9 * (n : ℝ) / 16
  let C3 : ℝ := (M / loadingConstant N) * Cseed + (9 / 32) * Cp
  have hB0 : 0 < B0 := by
    dsimp [B0]
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr N.hn)) (by
      positivity)
  have hCp : 0 < Cp := by
    dsimp [Cp]
    exact div_pos (mul_pos (lt_of_lt_of_le zero_lt_one hM) hB0)
      (sub_pos.mpr htrans_lt_one)
  let C2 : ℝ := M / (1 - loadingTransverseRate N)
  have hC2 : 0 < C2 := by
    dsimp [C2]
    exact div_pos (lt_of_lt_of_le zero_lt_one hM)
      (sub_pos.mpr htrans_lt_one)
  have hCseed : 0 < Cseed := by
    dsimp [Cseed]
    have hblock : 0 < blockContraction N := blockContraction_pos N
    have hmix : 0 < 1 - mixingRate N := sub_pos.mpr (mixingRate_lt_one N)
    positivity
  have hC3 : 0 < C3 := by
    dsimp [C3]
    have hload : 0 < loadingConstant N :=
      lt_of_lt_of_le zero_lt_one (loading_constants_spec N).2.2.2.2.2.1
    positivity
  let sCal : ℝ := min 1 ((1 / 32) / (C2 * C3))
  have hsCal : 0 < sCal := by
    dsimp [sCal]
    exact lt_min zero_lt_one (div_pos (by norm_num) (mul_pos hC2 hC3))
  let sPersistCenter : ℝ := min 1
    ((1 / 64) /
      (C2 * C3 * Real.exp (3 * epsilon / 2)))
  have hsPersistCenter : 0 < sPersistCenter := by
    dsimp [sPersistCenter]
    exact lt_min zero_lt_one (div_pos (by norm_num)
      (mul_pos (mul_pos hC2 hC3) (Real.exp_pos _)))
  let sPersistFast : ℝ := (1 / 64) / (Cp + M * C3)
  have hsPersistFast : 0 < sPersistFast := by
    dsimp [sPersistFast]
    exact div_pos (by norm_num)
      (add_pos hCp (mul_pos (lt_of_lt_of_le zero_lt_one hM) hC3))
  have hinfluenceBound : 0 < influenceRowBound N := by
    unfold influenceRowBound influenceOperatorBound columnMixingConstant
    have hblock : 0 < blockContraction N := blockContraction_pos N
    have hmix : 0 < 1 - mixingRate N := sub_pos.mpr (mixingRate_lt_one N)
    have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    positivity
  let sPersistInfluence : ℝ := (1 / 4) / influenceRowBound N
  have hsPersistInfluence : 0 < sPersistInfluence := by
    dsimp [sPersistInfluence]
    exact div_pos (by norm_num) hinfluenceBound
  let sEq39 : ℝ :=
    min (min sPersistCenter sPersistFast) sPersistInfluence
  have hsEq39 : 0 < sEq39 := by
    dsimp [sEq39]
    exact lt_min (lt_min hsPersistCenter hsPersistFast) hsPersistInfluence
  let sCorrect : ℝ := min 1
    ((loadingTransverseRate N - loadingFastRate N) /
      (M * (J0 + Cp)))
  have hsCorrect : 0 < sCorrect := by
    dsimp [sCorrect]
    exact lt_min zero_lt_one (div_pos hgap (mul_pos
      (lt_of_lt_of_le zero_lt_one hM) (add_pos hJ0 hCp)))
  have hgainFloor : 0 < gainFloor N := by
    have hmu : 0 < mixingMinorization N := by
      unfold mixingMinorization
      split_ifs
      · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
      · norm_num
    exact (mul_pos (Nat.cast_pos.mpr N.hn) hmu).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  let sCenter : ℝ :=
    min ((gainFloor N / 2) / Cp) ((1 / 64) / Cp)
  have hsCenter : 0 < sCenter := by
    dsimp [sCenter]
    exact lt_min (div_pos (div_pos hgainFloor (by norm_num)) hCp)
      (div_pos (by norm_num) hCp)
  obtain ⟨sResidual, hsResidual, hsResidual_cap⟩ :=
    loading_half_delay_residual_cap N
  let sResidual' : ℝ := min sResidual sCorrect
  have hsResidual' : 0 < sResidual' :=
    lt_min hsResidual hsCorrect
  let sLoad' : ℝ :=
    min (min (min (min (min sLoad sPert) sCenter) sResidual') sCal) sEq39
  have hsLoad' : 0 < sLoad' := by
    dsimp [sLoad']
    exact lt_min (lt_min (lt_min (lt_min (lt_min hsLoad hsPert) hsCenter)
      hsResidual') hsCal) hsEq39
  refine ⟨sLoad', hsLoad', ?_, ?_⟩
  · exact (min_le_left _ _).trans
      ((min_le_left _ _).trans ((min_le_left _ _).trans
        ((min_le_left _ _).trans ((min_le_left _ _).trans hsLoad_cap))))
  · intro D s hD hs hsCap j i hrow P Q hP hPQ hbudget
    have hsPreCal :
        s ≤ min (min (min sLoad sPert) sCenter) sResidual' :=
      hsCap.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hsCalCap : s ≤ sCal :=
      hsCap.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hsEq39Cap : s ≤ sEq39 := hsCap.trans (min_le_right _ _)
    have hsBase : s ≤ sLoad :=
      hsPreCal.trans ((min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_left _ _)))
    have hsPertCap : s ≤ sPert :=
      hsPreCal.trans ((min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_right _ _)))
    have hsCenterCap : s ≤ sCenter :=
      hsPreCal.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hsResidual'Cap : s ≤ sResidual' :=
      hsPreCal.trans (min_le_right _ _)
    have hsResidualCap : s ≤ sResidual :=
      hsResidual'Cap.trans (min_le_left _ _)
    have hsCorrectCap : s ≤ sCorrect :=
      hsResidual'Cap.trans (min_le_right _ _)
    have hδ :
        (5 / 4) * s ^ 2 +
            (2 * ((((blockContraction N)⁻¹ * (n : ℝ)) /
              (1 - mixingRate N)) + 1 / 2)) * s *
              ((loadingHalfDelay N s : ℝ) + 1) ≤ 1 / 32 := by
      simpa using hsResidual_cap s hs hsResidualCap
    have hcenterFloorCap : Cp * s ≤ gainFloor N / 2 := by
      have hs' : s ≤ (gainFloor N / 2) / Cp :=
        hsCenterCap.trans (min_le_left _ _)
      have := (le_div_iff₀ hCp).mp hs'
      simpa [mul_comm] using this
    have hcenterFineCap : Cp * s ≤ 1 / 64 := by
      have hs' : s ≤ (1 / 64) / Cp :=
        hsCenterCap.trans (min_le_right _ _)
      have := (le_div_iff₀ hCp).mp hs'
      simpa [mul_comm] using this
    have hcenterOneCap : Cp * s ≤ 1 / 8 :=
      hcenterFineCap.trans (by norm_num)
    have hcalibration_error_cap : C2 * C3 * s ^ 2 ≤ 1 / 32 := by
      have hs_one : s ≤ 1 := hsCalCap.trans (min_le_left _ _)
      have hs_coeff : s * (C2 * C3) ≤ 1 / 32 := by
        apply (le_div_iff₀ (mul_pos hC2 hC3)).mp
        simpa [sCal] using hsCalCap.trans (min_le_right _ _)
      have hsq : s ^ 2 ≤ s := by nlinarith
      calc
        C2 * C3 * s ^ 2 ≤ C2 * C3 * s :=
          mul_le_mul_of_nonneg_left hsq (mul_pos hC2 hC3).le
        _ = s * (C2 * C3) := by ring
        _ ≤ 1 / 32 := hs_coeff
    have hpersistence_center_cap :
        C2 * C3 * s ^ 2 * Real.exp (3 * epsilon / 2) ≤ 1 / 64 := by
      have hsPersistCenterCap : s ≤ sPersistCenter :=
        hsEq39Cap.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hs_one : s ≤ 1 :=
        hsPersistCenterCap.trans (min_le_left _ _)
      have hcoeff_pos :
          0 < C2 * C3 * Real.exp (3 * epsilon / 2) :=
        mul_pos (mul_pos hC2 hC3) (Real.exp_pos _)
      have hs_coeff :
          s * (C2 * C3 * Real.exp (3 * epsilon / 2)) ≤ 1 / 64 := by
        apply (le_div_iff₀ hcoeff_pos).mp
        simpa [sPersistCenter] using
          hsPersistCenterCap.trans (min_le_right _ _)
      have hsq : s ^ 2 ≤ s := by nlinarith
      calc
        C2 * C3 * s ^ 2 * Real.exp (3 * epsilon / 2) ≤
            C2 * C3 * s * Real.exp (3 * epsilon / 2) := by
          gcongr
        _ = s * (C2 * C3 * Real.exp (3 * epsilon / 2)) := by ring
        _ ≤ 1 / 64 := hs_coeff
    have hpersistence_fast_cap : (Cp + M * C3) * s ≤ 1 / 64 := by
      have hsPersistFastCap : s ≤ sPersistFast :=
        hsEq39Cap.trans ((min_le_left _ _).trans (min_le_right _ _))
      have hcoeff_pos : 0 < Cp + M * C3 :=
        add_pos hCp (mul_pos (lt_of_lt_of_le zero_lt_one hM) hC3)
      have hraw := (le_div_iff₀ hcoeff_pos).mp (by
        simpa [sPersistFast] using hsPersistFastCap)
      simpa [mul_comm] using hraw
    have hpersistence_influence_cap :
        s * influenceRowBound N ≤ 1 / 4 := by
      have hsPersistInfluenceCap : s ≤ sPersistInfluence :=
        hsEq39Cap.trans (min_le_right _ _)
      exact (le_div_iff₀ hinfluenceBound).mp (by
        simpa [sPersistInfluence] using hsPersistInfluenceCap)
    have hperturbation_cap : loadingFastRate N + M * (s * J0) ≤
        loadingTransverseRate N := by
      have hmul : s * (M * J0) ≤
          loadingTransverseRate N - loadingFastRate N := by
        apply (le_div_iff₀ hden).mp
        simpa [sPert] using hsPertCap
      nlinarith
    have hcorrected_perturbation_cap :
        loadingFastRate N + M * (s * J0 + Cp * s ^ 2) ≤
          loadingTransverseRate N := by
      have hs_one : s ≤ 1 :=
        hsCorrectCap.trans (min_le_left _ _)
      have hsq : s ^ 2 ≤ s := by nlinarith
      have hdenCorrect : 0 < M * (J0 + Cp) :=
        mul_pos (lt_of_lt_of_le zero_lt_one hM) (add_pos hJ0 hCp)
      have hs_gap : s * (M * (J0 + Cp)) ≤
          loadingTransverseRate N - loadingFastRate N := by
        apply (le_div_iff₀ hdenCorrect).mp
        simpa [sCorrect] using
          hsCorrectCap.trans (min_le_right _ _)
      have hquad : Cp * s ^ 2 ≤ Cp * s :=
        mul_le_mul_of_nonneg_left hsq hCp.le
      have hpert_le : M * (s * J0 + Cp * s ^ 2) ≤
          s * (M * (J0 + Cp)) := by
        calc
          M * (s * J0 + Cp * s ^ 2) ≤ M * (s * J0 + Cp * s) := by
            gcongr
          _ = s * (M * (J0 + Cp)) := by ring
      exact add_le_of_le_sub_left (hpert_le.trans hs_gap)
    have htriangular' (k t : ℕ) (hkt : k ≤ t) (E K : Fin n → ℝ)
        (hE : dotProduct (absoluteProbability N k) E = 0)
        (hK : (∑ q, K q) = 0) :
        nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
            nodeL1Norm
              (forwardProduct N.colMix t k *ᵥ K +
                ∑ q ∈ Finset.Ico k t,
                  forwardProduct N.colMix t (q + 1) *ᵥ
                    ((N.colMix q - 1) *ᵥ
                      (forwardProduct N.rowMix q k *ᵥ E))) ≤
          M * loadingFastRate N ^ (t - k) *
            (nodeSupNorm E + nodeL1Norm K) := by
      have hraw := htriangular k t hkt E K hE hK
      refine hraw.trans ?_
      have hp : 0 ≤ loadingFastRate N ^ (t - k) := by
        exact pow_nonneg (by
          unfold loadingFastRate loadingTriangularRate
          linarith [mixingRate_nonneg N]) _
      have hg : 0 ≤ nodeSupNorm E + nodeL1Norm K := by
        exact add_nonneg (nodeSupNorm_nonneg N E)
          (Finset.sum_nonneg fun q _ => abs_nonneg _)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMtri_le hp) hg
    have hgeom : loadingConstant N *
        loadingRate N ^ loadingHalfDelay N s ≤ s ^ 3 :=
      hsLoad_geom s hs hsBase
    have hfirst (a : ℝ) (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4) :=
      calibrated_true_first_segment_bounds
        N L D s a j i hL hD hs hrow ha_lo ha_hi hgeom
    have hretained_succ (a : ℝ) (t : ℕ) :
        let e := -a * D / ((s / L) * influenceRow N j i)
        retainedLoadingTracker N L D s j i e (t + 1) =
          N.colMix t *ᵥ retainedLoadingTracker N L D s j i e t +
            (N.colMix t - 1) *ᵥ
              (fun k => negativeCurvatureDerivative L D
                ((loadingTrajectory N L D s j i e t).primal k) +
                loadingPulse j i e t k) := by
      dsimp only
      exact retained_loading_tracker_succ N L D s j i _ t
    have hnegative_recurrence (a : ℝ) (t : ℕ) (hjt : j < t)
        (hbranch : ∀ q,
          D / 2 ≤ (loadingTrajectory N L D s j i
            (-a * D / ((s / L) * influenceRow N j i)) t).primal q ∧
          (loadingTrajectory N L D s j i
            (-a * D / ((s / L) * influenceRow N j i)) t).primal q ≤
              3 * D / 2) :=
      loading_negative_branch_shifted_recurrence
        N L D s j i (-a * D / ((s / L) * influenceRow N j i)) t
          hL hD hjt hbranch
    have hslowfast (a : ℝ) (t : ℕ) (hjt : j < t)
        (hbranch : ∀ q,
          D / 2 ≤ (loadingTrajectory N L D s j i
            (-a * D / ((s / L) * influenceRow N j i)) t).primal q ∧
          (loadingTrajectory N L D s j i
            (-a * D / ((s / L) * influenceRow N j i)) t).primal q ≤
              3 * D / 2) :=
      loading_negative_branch_slow_fast_coordinates N L D s a j i t (by
        dsimp only
        exact hnegative_recurrence a t hjt hbranch)
    have hseed (a : ℝ) (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4) :=
      loading_first_segment_branch_center_bounds
        N L D s a j i hL hD hs hrow ha_lo ha_hi hgeom hδ
    have hseed_slowfast (a : ℝ) (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4) :=
      hslowfast a (j + loadingHalfDelay N s + 1) (by omega)
        (hseed a ha_lo ha_hi).1
    let kRef : ℕ := j + loadingDelay N s
    have hsOne : s ≤ 1 :=
      hsCorrectCap.trans (min_le_left _ _)
    have hsecond (a : ℝ) (ha_lo : 3 / 4 ≤ a) (ha_hi : a ≤ 5 / 4) :=
      loading_second_half_loaded_endpoint_source_bound
        N L D s a M j i hL hD hs hsOne hrow ha_lo ha_hi hM hgeom hδ
          htriangular' (by simpa [J0] using hperturbation_cap)
    have hsecond_endpoint (a : ℝ) (ha_lo : 3 / 4 ≤ a)
        (ha_hi : a ≤ 5 / 4) :
        let e := -a * D / ((s / L) * influenceRow N j i)
        let X : ℕ → Fin n → ℝ := fun r q =>
          (loadingTrajectory N L D s j i e r).primal q - D
        let U : ℕ → Fin n → ℝ := fun r q =>
          -retainedLoadingTracker N L D s j i e r q / L
        let xi := loadingSlowCenter N X
        let F := loadingFastCoordinates N X U
        |xi kRef - (a - 1) * D| ≤ D / 32 ∧
          nodeSupNorm (F kRef).1 + nodeL1Norm (F kRef).2 ≤ C3 * s * D := by
      simpa [kRef, C3, Cseed, Cp, B0] using
        (hsecond a ha_lo ha_hi).2.2
    let Ref := loadingUnitCenterReferenceOrbit N s kRef
    have hreference_eq24 : ∀ m,
        0 < (Ref m).1 ∧
        1 + s * gain N (kRef + m) / 2 ≤
          (Ref (m + 1)).1 / (Ref m).1 ∧
        (Ref (m + 1)).1 / (Ref m).1 ≤
          1 + 3 * s * gain N (kRef + m) / 2 ∧
        nodeSupNorm (Ref m).2.1 + nodeL1Norm (Ref m).2.2 ≤
          Cp * s * (Ref m).1 := by
      simpa [Ref, Cp, B0] using
        (loading_unit_center_reference_bounds N M s kRef hM hs
          htriangular' (by simpa [J0] using hperturbation_cap)
          (by simpa [Cp, B0] using hcenterFloorCap)
          (by simpa [Cp, B0] using hcenterOneCap))
    have hreference_one : ∀ m, 1 ≤ (Ref m).1 := by
      intro m
      induction m with
      | zero => simp [Ref]
      | succ m ih =>
          have hgain_nonneg : 0 ≤ gain N (kRef + m) := by
            unfold gain dotProduct
            exact Finset.sum_nonneg fun q _ =>
              mul_nonneg
                ((absoluteProbability_mem_stdSimplex N (kRef + m + 1)).1 q)
                (pushMass_nonneg N (kRef + m) q)
          have hratio : 1 ≤ (Ref (m + 1)).1 / (Ref m).1 := by
            exact (by nlinarith : 1 ≤
              1 + s * gain N (kRef + m) / 2).trans
                (hreference_eq24 m).2.1
          have hmono : (Ref m).1 ≤ (Ref (m + 1)).1 := by
            simpa using (le_div_iff₀ (hreference_eq24 m).1).mp hratio
          exact ih.trans hmono
    have hreference_mono : ∀ u v, u ≤ v → (Ref u).1 ≤ (Ref v).1 := by
      intro u v huv
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
      induction d with
      | zero => simp
      | succ d ih =>
          have hgain_nonneg : 0 ≤ gain N (kRef + (u + d)) := by
            unfold gain dotProduct
            exact Finset.sum_nonneg fun q _ =>
              mul_nonneg
                ((absoluteProbability_mem_stdSimplex
                  N (kRef + (u + d) + 1)).1 q)
                (pushMass_nonneg N (kRef + (u + d)) q)
          have hratio : 1 ≤
              (Ref (u + d + 1)).1 / (Ref (u + d)).1 := by
            exact (by nlinarith : 1 ≤
              1 + s * gain N (kRef + (u + d)) / 2).trans
                (by simpa [Nat.add_assoc] using
                  (hreference_eq24 (u + d)).2.1)
          have hstep : (Ref (u + d)).1 ≤ (Ref (u + d + 1)).1 := by
            simpa using
              (le_div_iff₀ (hreference_eq24 (u + d)).1).mp hratio
          have hud : u ≤ u + d := by omega
          exact (ih hud).trans hstep
    have hnormalized_step (a : ℝ) (m : ℕ)
        (hbranch : ∀ q,
          D / 2 ≤ (loadingTrajectory N L D s j i
            (-a * D / ((s / L) * influenceRow N j i))
              (kRef + m)).primal q ∧
          (loadingTrajectory N L D s j i
            (-a * D / ((s / L) * influenceRow N j i))
              (kRef + m)).primal q ≤ 3 * D / 2) := by
      let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
      let X : ℕ → Fin n → ℝ := fun r q =>
        (loadingTrajectory N L D s j i e r).primal q - D
      let U : ℕ → Fin n → ℝ := fun r q =>
        -retainedLoadingTracker N L D s j i e r q / L
      let xi := loadingSlowCenter N X
      let F := loadingFastCoordinates N X U
      have hsf := hslowfast a (kRef + m) (by
        dsimp [kRef, loadingDelay]
        omega) (by simpa [e] using hbranch)
      dsimp only at hsf
      have hxi_step : xi (kRef + m + 1) =
          (1 + s * gain N (kRef + m)) * xi (kRef + m) +
            s * dotProduct (absoluteProbability N (kRef + m + 1))
              ((F (kRef + m)).1 + (F (kRef + m)).2) := by
        simpa [e, X, U, xi, F] using hsf.2.1
      have hF_step : F (kRef + m + 1) =
          loadingPerturbedFastStep N s (kRef + m) (F (kRef + m)) +
            loadingFastScale s
              (loadingFastCenterInput N (kRef + m) (xi (kRef + m))) := by
        simpa [e, X, U, xi, F, loadingPerturbedFastStep] using hsf.2.2
      exact loading_reference_normalized_residual_step
        N s kRef m xi F hxi_step hF_step
          (by simpa [Ref] using (hreference_eq24 m).1)
          (by simpa [Ref] using (hreference_eq24 (m + 1)).1)
    have hnormalized_correction (m : ℕ) (E K : Fin n → ℝ) := by
      exact loading_normalized_reference_correction_invariants_bound
        N s Cp kRef m E K hs.le
          (by simpa [Ref] using (hreference_eq24 (m + 1)).1)
          (by simpa [Ref] using (hreference_eq24 (m + 1)).2.2.2)
    have hkRefP : kRef ≤ P := by simpa [kRef] using hP
    have hcalibration_spec (a : ℝ) (ha_lo : 3 / 4 ≤ a)
        (ha_hi : a ≤ 5 / 4) := by
      let e : ℝ := -a * D / ((s / L) * influenceRow N j i)
      let X : ℕ → Fin n → ℝ := fun r q =>
        (loadingTrajectory N L D s j i e r).primal q - D
      let U : ℕ → Fin n → ℝ := fun r q =>
        -retainedLoadingTracker N L D s j i e r q / L
      let xi := loadingSlowCenter N X
      let F := loadingFastCoordinates N X U
      have hbranch_k : ∀ q,
          D / 2 ≤ (loadingTrajectory N L D s j i e kRef).primal q ∧
          (loadingTrajectory N L D s j i e kRef).primal q ≤ 3 * D / 2 := by
        simpa [e, kRef] using
          (hsecond a ha_lo ha_hi).1 kRef (by
            dsimp [kRef, loadingDelay]
            omega) le_rfl
      have hsf := hslowfast a kRef (by
        dsimp [kRef, loadingDelay]
        omega) (by simpa [e] using hbranch_k)
      have hcarrier :
          dotProduct (absoluteProbability N kRef) (F kRef).1 = 0 ∧
            (∑ q, (F kRef).2 q) = 0 := by
        simpa [e, X, U, xi, F] using hsf.1
      have hspec := loading_calibration_functional_spec
        N M s Cp kRef hM hs.le hCp.le htriangular'
          (by simpa [J0] using hcorrected_perturbation_cap)
          (fun m => by simpa [Ref] using (hreference_eq24 m).1)
          (fun m => by simpa [Ref] using hreference_one m)
          (fun m => by simpa [Ref] using (hreference_eq24 m).2.2.2)
          (xi kRef) (F kRef) hcarrier.1 hcarrier.2 (P - kRef)
      have hbackward
          (hcal : loadingFormalCorrectedCenter N s kRef (xi kRef)
            (F kRef) (P - kRef) = D / 8) :=
        loading_calibrated_backward_propagation
          N M s Cp kRef hM hs.le hCp.le htriangular'
            (by simpa [J0] using hcorrected_perturbation_cap)
            (fun m => by simpa [Ref] using (hreference_eq24 m).1)
            (fun m => by simpa [Ref] using hreference_one m)
            (fun u v huv => by simpa [Ref] using hreference_mono u v huv)
            (fun m => by simpa [Ref] using (hreference_eq24 m).2.2.2)
            (xi kRef) (D / 8) (F kRef) hcarrier.1 hcarrier.2
            (P - kRef) hcal
      have hforward
          (hcal : loadingFormalCorrectedCenter N s kRef (xi kRef)
            (F kRef) (P - kRef) = D / 8) :=
        loading_calibrated_forward_propagation
          N M s Cp kRef hM hs.le hCp.le htriangular'
            (by simpa [J0] using hcorrected_perturbation_cap)
            (fun m => by simpa [Ref] using (hreference_eq24 m).1)
            (fun m => by simpa [Ref] using hreference_one m)
            (fun u v huv => by simpa [Ref] using hreference_mono u v huv)
            (fun m => by simpa [Ref] using (hreference_eq24 m).2.2.2)
            (xi kRef) (D / 8) (F kRef) hcarrier.1 hcarrier.2
            (P - kRef) hcal
      exact And.intro hspec (And.intro hbackward hforward)
    let endpointPulse : ℝ → ℝ := fun a ↦
      -a * D / ((s / L) * influenceRow N j i)
    let endpointX : ℝ → Fin n → ℝ := fun a q ↦
      (loadingTrajectory N L D s j i (endpointPulse a) kRef).primal q - D
    let endpointU : ℝ → Fin n → ℝ := fun a q ↦
      -retainedLoadingTracker N L D s j i (endpointPulse a) kRef q / L
    let endpointXi : ℝ → ℝ := fun a ↦
      dotProduct (absoluteProbability N kRef) (endpointX a)
    let endpointFast : ℝ → (Fin n → ℝ) × (Fin n → ℝ) :=
      fun a ↦
        (fun q ↦ endpointX a q - endpointXi a,
          fun q ↦ endpointU a q -
            (pushMass N kRef q - 1) * endpointXi a)
    have hpulse_cont : Continuous endpointPulse := by
      dsimp [endpointPulse]
      fun_prop
    have htrajectory_cont :=
      loading_trajectory_continuous_in_pulse N L D s j i hD.le kRef
    have hprimal_cont (q : Fin n) :
        Continuous (fun a ↦
          (loadingTrajectory N L D s j i (endpointPulse a) kRef).primal q) :=
      (htrajectory_cont.1 q).comp hpulse_cont
    have htracker_cont (q : Fin n) :
        Continuous (fun a ↦
          (loadingTrajectory N L D s j i (endpointPulse a) kRef).tracker q) :=
      (htrajectory_cont.2 q).comp hpulse_cont
    have hpulse_value_cont (q : Fin n) :
        Continuous (fun a ↦ loadingPulse j i (endpointPulse a) kRef q) := by
      by_cases h : kRef = j ∧ q = i
      · simpa [loadingPulse, h] using hpulse_cont
      · simpa [loadingPulse, h] using
          (continuous_const : Continuous (fun _a : ℝ ↦ (0 : ℝ)))
    have horacle_cont (q : Fin n) :
        Continuous (fun a ↦ loadingOracle L D j i (endpointPulse a) kRef
          (loadingTrajectory N L D s j i (endpointPulse a) kRef).primal q) := by
      unfold loadingOracle
      exact ((negative_curvature_derivative_continuous L D hD.le).comp
        (hprimal_cont q)).add (hpulse_value_cont q)
    have hretained_cont (q : Fin n) :
        Continuous (fun a ↦
          retainedLoadingTracker N L D s j i (endpointPulse a) kRef q) := by
      simpa only [retainedLoadingTracker, Pi.sub_apply] using
        (htracker_cont q).sub (horacle_cont q)
    have hX_cont (q : Fin n) : Continuous (fun a ↦ endpointX a q) := by
      dsimp [endpointX]
      fun_prop
    have hU_cont (q : Fin n) : Continuous (fun a ↦ endpointU a q) := by
      dsimp [endpointU]
      fun_prop
    have hXi_cont : Continuous endpointXi := by
      dsimp [endpointXi, dotProduct]
      exact continuous_finset_sum _ (fun q _ ↦
        continuous_const.mul (hX_cont q))
    have hFast_cont : Continuous endpointFast := by
      dsimp [endpointFast]
      fun_prop
    have hformal_cont : Continuous (fun a ↦
        loadingFormalCorrectedCenter N s kRef (endpointXi a)
          (endpointFast a) (P - kRef)) :=
      loading_calibration_functional_continuous N s kRef (P - kRef)
        endpointXi endpointFast hXi_cont hFast_cont
    have hloaded_lo := hsecond_endpoint (3 / 4) (by norm_num) (by norm_num)
    have hloaded_hi := hsecond_endpoint (5 / 4) (by norm_num) (by norm_num)
    have hxi_lo : |endpointXi (3 / 4) - ((3 / 4 : ℝ) - 1) * D| ≤
        D / 32 := by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates] using hloaded_lo.1
    have hxi_hi : |endpointXi (5 / 4) - ((5 / 4 : ℝ) - 1) * D| ≤
        D / 32 := by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates] using hloaded_hi.1
    have hspec_lo := hcalibration_spec (3 / 4) (by norm_num) (by norm_num)
    have hspec_hi := hcalibration_spec (5 / 4) (by norm_num) (by norm_num)
    have hpsi_lo :
        |loadingCalibrationFunctional N s kRef (P - kRef)
          (endpointFast (3 / 4))| ≤ D / 32 := by
      have hraw := hspec_lo.1.2
      have hfast : nodeSupNorm (endpointFast (3 / 4)).1 +
          nodeL1Norm (endpointFast (3 / 4)).2 ≤ C3 * s * D := by
        simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
          loadingSlowCenter, loadingFastCoordinates] using hloaded_lo.2
      calc
        |loadingCalibrationFunctional N s kRef (P - kRef)
            (endpointFast (3 / 4))| ≤
            C2 * s * (nodeSupNorm (endpointFast (3 / 4)).1 +
              nodeL1Norm (endpointFast (3 / 4)).2) := by
          simpa [C2, endpointXi, endpointFast, endpointX, endpointU,
            endpointPulse, loadingSlowCenter, loadingFastCoordinates] using hraw
        _ ≤ C2 * s * (C3 * s * D) := by
          gcongr
        _ = (C2 * C3 * s ^ 2) * D := by ring
        _ ≤ (1 / 32) * D :=
          mul_le_mul_of_nonneg_right hcalibration_error_cap hD.le
        _ = D / 32 := by ring
    have hpsi_hi :
        |loadingCalibrationFunctional N s kRef (P - kRef)
          (endpointFast (5 / 4))| ≤ D / 32 := by
      have hraw := hspec_hi.1.2
      have hfast : nodeSupNorm (endpointFast (5 / 4)).1 +
          nodeL1Norm (endpointFast (5 / 4)).2 ≤ C3 * s * D := by
        simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
          loadingSlowCenter, loadingFastCoordinates] using hloaded_hi.2
      calc
        |loadingCalibrationFunctional N s kRef (P - kRef)
            (endpointFast (5 / 4))| ≤
            C2 * s * (nodeSupNorm (endpointFast (5 / 4)).1 +
              nodeL1Norm (endpointFast (5 / 4)).2) := by
          simpa [C2, endpointXi, endpointFast, endpointX, endpointU,
            endpointPulse, loadingSlowCenter, loadingFastCoordinates] using hraw
        _ ≤ C2 * s * (C3 * s * D) := by
          gcongr
        _ = (C2 * C3 * s ^ 2) * D := by ring
        _ ≤ (1 / 32) * D :=
          mul_le_mul_of_nonneg_right hcalibration_error_cap hD.le
        _ = D / 32 := by ring
    obtain ⟨aCal, haCal, hcal⟩ := loading_calibration_exists
      N s D kRef (P - kRef) endpointXi endpointFast hD hformal_cont
        (by simpa [Ref] using (hreference_eq24 (P - kRef)).1)
        (by simpa [Ref] using hreference_one (P - kRef))
        hxi_lo hxi_hi hpsi_lo hpsi_hi
        (by simpa [endpointXi, endpointFast, endpointX, endpointU,
          endpointPulse, loadingSlowCenter, loadingFastCoordinates] using
            hspec_lo.1.1)
        (by simpa [endpointXi, endpointFast, endpointX, endpointU,
          endpointPulse, loadingSlowCenter, loadingFastCoordinates] using
            hspec_hi.1.1)
    have hcalibrated_propagation :=
      (hcalibration_spec aCal haCal.1 haCal.2).2
    have hcalibrated_backward := hcalibrated_propagation.1 (by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates] using hcal)
    have hcalibrated_forward := hcalibrated_propagation.2 (by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates] using hcal)
    have hreference_at_P := hreference_eq24 (P - kRef)
    have hkRef_add : kRef + (P - kRef) = P := Nat.add_sub_of_le hkRefP
    rw [hkRef_add] at hreference_at_P
    have hinfluence_ne : influenceRow N j i ≠ 0 := by
      exact abs_pos.mp (hs.trans_le hrow)
    have hscale_ne : (s / L) * influenceRow N j i ≠ 0 :=
      mul_ne_zero (div_ne_zero (ne_of_gt hs) (ne_of_gt hL)) hinfluence_ne
    have hrate_nonneg : 0 ≤ loadingTransverseRate N := by
      unfold loadingTransverseRate loadingFastRate loadingTriangularRate
      linarith [mixingRate_nonneg N]
    have hrate_one : loadingTransverseRate N ≤ 1 := htrans_lt_one.le
    have hloaded_cal := hsecond_endpoint aCal haCal.1 haCal.2
    have hfast0 : nodeSupNorm (endpointFast aCal).1 +
        nodeL1Norm (endpointFast aCal).2 ≤ C3 * s * D := by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates] using hloaded_cal.2
    have hbranch_k_cal : ∀ q,
        D / 2 ≤ (loadingTrajectory N L D s j i (endpointPulse aCal)
          kRef).primal q ∧
        (loadingTrajectory N L D s j i (endpointPulse aCal)
          kRef).primal q ≤ 3 * D / 2 := by
      simpa [endpointPulse, kRef] using
        (hsecond aCal haCal.1 haCal.2).1 kRef (by
          dsimp [kRef, loadingDelay]
          omega) le_rfl
    have hsf_cal := hslowfast aCal kRef (by
      dsimp [kRef, loadingDelay]
      omega) (by simpa [endpointPulse] using hbranch_k_cal)
    have hcarrier_cal :
        dotProduct (absoluteProbability N kRef) (endpointFast aCal).1 = 0 ∧
          (∑ q, (endpointFast aCal).2 q) = 0 := by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates] using hsf_cal.1
    have hformal_fast_global := loading_formal_fast_state_bound
      N M s Cp kRef hM hs.le hCp.le htriangular'
        (by simpa [J0] using hcorrected_perturbation_cap)
        (fun m => by simpa [Ref] using (hreference_eq24 m).1)
        (fun m => by simpa [Ref] using (hreference_eq24 m).2.2.2)
        (endpointXi aCal) (endpointFast aCal)
        hcarrier_cal.1 hcarrier_cal.2
    have hexp_upper : Real.exp (3 * epsilon / 2) ≤ 19 / 16 := by
      have hmem : 3 * epsilon / 2 ∈ Set.Icc (0 : ℝ) 1 := by
        norm_num [epsilon]
      have hraw := Real.exp_le_one_add_two_mul_of_mem_Icc_zero_one hmem
      norm_num [epsilon] at hraw ⊢
      exact hraw
    have hreference_window_ratio (m : ℕ)
        (hPm : P - kRef ≤ m) (hmQ : m ≤ Q - kRef) :
        (Ref m).1 / (Ref (P - kRef)).1 ≤
          Real.exp (3 * epsilon / 2) := by
      have hraw := loading_reference_ratio_le_exp_gain
        N s kRef (P - kRef) m hs.le hPm
          (fun q => by simpa [Ref] using (hreference_eq24 q).1)
          (fun q => by simpa [Ref] using (hreference_eq24 q).2.2.1)
      have hstart : kRef + (P - kRef) = P := Nat.add_sub_of_le hkRefP
      have hend : kRef + m ≤ Q := by omega
      have hsubset : Finset.Ico (kRef + (P - kRef)) (kRef + m) ⊆
          Finset.Ico P Q := by
        intro t ht
        rw [hstart] at ht
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp ht).1,
          (Finset.mem_Ico.mp ht).2.trans_le hend⟩
      have hsum_le :
          (∑ t ∈ Finset.Ico (kRef + (P - kRef)) (kRef + m), gain N t) ≤
            ∑ t ∈ Finset.Ico P Q, gain N t := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun t _ _ => by
          unfold gain dotProduct
          exact Finset.sum_nonneg fun q _ =>
            mul_nonneg
              ((absoluteProbability_mem_stdSimplex N (t + 1)).1 q)
              (pushMass_nonneg N t q))
      have hscaled : s *
          (∑ t ∈ Finset.Ico (kRef + (P - kRef)) (kRef + m), gain N t) ≤
            epsilon :=
        (mul_le_mul_of_nonneg_left hsum_le hs.le).trans hbudget
      have hexponent : (3 / 2) * s *
          (∑ t ∈ Finset.Ico (kRef + (P - kRef)) (kRef + m), gain N t) ≤
            3 * epsilon / 2 := by
        nlinarith
      exact hraw.trans (Real.exp_le_exp.mpr hexponent)
    have hbackward_error (m : ℕ) (hmP : m ≤ P - kRef) :
        |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m -
          (Ref m).1 / (Ref (P - kRef)).1 * (D / 8)| ≤ D / 32 := by
      have hraw := (hcalibrated_backward m hmP).1
      have hpow : loadingTransverseRate N ^ m ≤ 1 :=
        pow_le_one₀ hrate_nonneg hrate_one
      calc
        |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
              (endpointFast aCal) m -
            (Ref m).1 / (Ref (P - kRef)).1 * (D / 8)| ≤
            C2 * s * loadingTransverseRate N ^ m *
              (nodeSupNorm (endpointFast aCal).1 +
                nodeL1Norm (endpointFast aCal).2) := by
          simpa [C2, Ref, endpointXi, endpointFast, endpointX, endpointU,
            endpointPulse, loadingSlowCenter, loadingFastCoordinates] using hraw
        _ ≤ C2 * s * 1 * (C3 * s * D) := by
          have hgauge_nonneg : 0 ≤ nodeSupNorm (endpointFast aCal).1 +
              nodeL1Norm (endpointFast aCal).2 :=
            add_nonneg (nodeSupNorm_nonneg N _)
              (Finset.sum_nonneg fun q _ => abs_nonneg _)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hpow (mul_nonneg hC2.le hs.le))
            hfast0 hgauge_nonneg
            (mul_nonneg (mul_nonneg hC2.le hs.le) zero_le_one)
        _ = (C2 * C3 * s ^ 2) * D := by ring
        _ ≤ (1 / 32) * D :=
          mul_le_mul_of_nonneg_right hcalibration_error_cap hD.le
        _ = D / 32 := by ring
    have hforward_error (m : ℕ) (hPm : P - kRef ≤ m)
        (hmQ : m ≤ Q - kRef) :
        |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m -
          (Ref m).1 / (Ref (P - kRef)).1 * (D / 8)| ≤ D / 64 := by
      have hraw := hcalibrated_forward m hPm
      have hratio := hreference_window_ratio m hPm hmQ
      have hratio_nonneg : 0 ≤ (Ref m).1 / (Ref (P - kRef)).1 :=
        div_nonneg (hreference_eq24 m).1.le
          (hreference_eq24 (P - kRef)).1.le
      have hpow : loadingTransverseRate N ^ (P - kRef) ≤ 1 :=
        pow_le_one₀ hrate_nonneg hrate_one
      calc
        |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
              (endpointFast aCal) m -
            (Ref m).1 / (Ref (P - kRef)).1 * (D / 8)| ≤
            (Ref m).1 / (Ref (P - kRef)).1 *
              (C2 * s * loadingTransverseRate N ^ (P - kRef) *
                (nodeSupNorm (endpointFast aCal).1 +
                  nodeL1Norm (endpointFast aCal).2)) := by
          simpa [C2, Ref, endpointXi, endpointFast, endpointX, endpointU,
            endpointPulse, loadingSlowCenter, loadingFastCoordinates] using hraw
        _ ≤ Real.exp (3 * epsilon / 2) *
              (C2 * s * 1 * (C3 * s * D)) := by
          have hgauge_nonneg : 0 ≤ nodeSupNorm (endpointFast aCal).1 +
              nodeL1Norm (endpointFast aCal).2 :=
            add_nonneg (nodeSupNorm_nonneg N _)
              (Finset.sum_nonneg fun q _ => abs_nonneg _)
          have hinner :
              C2 * s * loadingTransverseRate N ^ (P - kRef) *
                  (nodeSupNorm (endpointFast aCal).1 +
                    nodeL1Norm (endpointFast aCal).2) ≤
                C2 * s * 1 * (C3 * s * D) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left hpow (mul_nonneg hC2.le hs.le))
              hfast0 hgauge_nonneg
              (mul_nonneg (mul_nonneg hC2.le hs.le) zero_le_one)
          exact mul_le_mul hratio hinner
            (mul_nonneg (mul_nonneg (mul_nonneg hC2.le hs.le)
              (pow_nonneg hrate_nonneg _)) hgauge_nonneg)
            (Real.exp_pos _).le
        _ = (C2 * C3 * s ^ 2 * Real.exp (3 * epsilon / 2)) * D := by
          ring
        _ ≤ (1 / 64) * D :=
          mul_le_mul_of_nonneg_right hpersistence_center_cap hD.le
        _ = D / 64 := by ring
    have hformal_center_abs (m : ℕ) (hmQ : m ≤ Q - kRef) :
        |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m| ≤ 21 * D / 128 := by
      by_cases hmP : m ≤ P - kRef
      · have herr := hbackward_error m hmP
        have hratio_nonneg : 0 ≤ (Ref m).1 / (Ref (P - kRef)).1 :=
          div_nonneg (hreference_eq24 m).1.le
            (hreference_eq24 (P - kRef)).1.le
        have hratio_le : (Ref m).1 / (Ref (P - kRef)).1 ≤ 1 :=
          (div_le_one (hreference_eq24 (P - kRef)).1).2
            (hreference_mono m (P - kRef) hmP)
        have htarget :
            |(Ref m).1 / (Ref (P - kRef)).1 * (D / 8)| ≤ D / 8 := by
          rw [abs_of_nonneg (mul_nonneg hratio_nonneg (div_nonneg hD.le
            (by norm_num)))]
          nlinarith
        have htriangle := abs_add_le
          (loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m -
              (Ref m).1 / (Ref (P - kRef)).1 * (D / 8))
          ((Ref m).1 / (Ref (P - kRef)).1 * (D / 8))
        have hid :
            loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
                (endpointFast aCal) m =
              (loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
                  (endpointFast aCal) m -
                (Ref m).1 / (Ref (P - kRef)).1 * (D / 8)) +
              (Ref m).1 / (Ref (P - kRef)).1 * (D / 8) := by ring
        rw [← hid] at htriangle
        linarith
      · have hPm : P - kRef ≤ m := by omega
        have herr := hforward_error m hPm hmQ
        have hratio_nonneg : 0 ≤ (Ref m).1 / (Ref (P - kRef)).1 :=
          div_nonneg (hreference_eq24 m).1.le
            (hreference_eq24 (P - kRef)).1.le
        have hratio_le := hreference_window_ratio m hPm hmQ
        have htarget :
            |(Ref m).1 / (Ref (P - kRef)).1 * (D / 8)| ≤
              19 * D / 128 := by
          rw [abs_of_nonneg (mul_nonneg hratio_nonneg (div_nonneg hD.le
            (by norm_num)))]
          nlinarith [hexp_upper]
        have htriangle := abs_add_le
          (loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m -
              (Ref m).1 / (Ref (P - kRef)).1 * (D / 8))
          ((Ref m).1 / (Ref (P - kRef)).1 * (D / 8))
        have hid :
            loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
                (endpointFast aCal) m =
              (loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
                  (endpointFast aCal) m -
                (Ref m).1 / (Ref (P - kRef)).1 * (D / 8)) +
              (Ref m).1 / (Ref (P - kRef)).1 * (D / 8) := by ring
        rw [← hid] at htriangle
        linarith
    have hformal_fast_cap (m : ℕ) (hmQ : m ≤ Q - kRef) :
        nodeSupNorm
            (loadingFormalFastState N s kRef (endpointXi aCal)
              (endpointFast aCal) m).1 +
          nodeL1Norm
            (loadingFormalFastState N s kRef (endpointXi aCal)
              (endpointFast aCal) m).2 ≤ D / 64 := by
      have hcenter := hformal_center_abs m hmQ
      have hcenterD :
          |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
              (endpointFast aCal) m| ≤ D := by
        nlinarith only [hcenter, hD]
      have hpow : loadingTransverseRate N ^ m ≤ 1 :=
        pow_le_one₀ hrate_nonneg hrate_one
      calc
        nodeSupNorm
              (loadingFormalFastState N s kRef (endpointXi aCal)
                (endpointFast aCal) m).1 +
            nodeL1Norm
              (loadingFormalFastState N s kRef (endpointXi aCal)
                (endpointFast aCal) m).2 ≤
            Cp * s *
                |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
                  (endpointFast aCal) m| +
              M * loadingTransverseRate N ^ m *
                (nodeSupNorm (endpointFast aCal).1 +
                  nodeL1Norm (endpointFast aCal).2) := hformal_fast_global m
        _ ≤ Cp * s * D + M * 1 * (C3 * s * D) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hcenterD
              (mul_nonneg hCp.le hs.le)
          · have hgauge_nonneg : 0 ≤
                nodeSupNorm (endpointFast aCal).1 +
                  nodeL1Norm (endpointFast aCal).2 :=
              add_nonneg (nodeSupNorm_nonneg N _)
                (Finset.sum_nonneg fun q _ => abs_nonneg _)
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left hpow
                (lt_of_lt_of_le zero_lt_one hM).le)
              hfast0 hgauge_nonneg
              (mul_nonneg (lt_of_lt_of_le zero_lt_one hM).le zero_le_one)
        _ = ((Cp + M * C3) * s) * D := by ring
        _ ≤ (1 / 64) * D :=
          mul_le_mul_of_nonneg_right hpersistence_fast_cap hD.le
        _ = D / 64 := by ring
    have hformal_safe (m : ℕ) (hmQ : m ≤ Q - kRef) :
        |loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m| +
          (nodeSupNorm
              (loadingFormalFastState N s kRef (endpointXi aCal)
                (endpointFast aCal) m).1 +
            nodeL1Norm
              (loadingFormalFastState N s kRef (endpointXi aCal)
                (endpointFast aCal) m).2) < D / 2 := by
      nlinarith only [hformal_center_abs m hmQ, hformal_fast_cap m hmQ, hD]
    have hpersistence := loading_formal_actual_branch_persistence
      N L D s aCal j i kRef (Q - kRef) hL hD hs (by
        dsimp [kRef, loadingDelay]
        omega) (fun m => by simpa [Ref] using (hreference_eq24 m).1) (by
          intro m hm
          simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
            loadingSlowCenter, loadingFastCoordinates] using hformal_safe m hm)
    refine ⟨aCal, haCal.1, haCal.2, ?_, hretained_succ aCal⟩
    intro t ht
    have hPt : P ≤ t := (Finset.mem_Ico.mp ht).1
    have htQ : t < Q := (Finset.mem_Ico.mp ht).2
    have hkt : kRef ≤ t := hkRefP.trans hPt
    let m : ℕ := t - kRef
    have hkm : kRef + m = t := by dsimp [m]; omega
    have hmQ : m ≤ Q - kRef := by dsimp [m]; omega
    have hPm : P - kRef ≤ m := by dsimp [m]; omega
    have hpersist_m := hpersistence m hmQ
    have hbranch_t : ∀ q,
        D / 2 ≤ (loadingTrajectory N L D s j i (endpointPulse aCal) t).primal q ∧
        (loadingTrajectory N L D s j i (endpointPulse aCal) t).primal q ≤
          3 * D / 2 := by
      simpa [endpointPulse, hkm] using hpersist_m.1
    have hxi_ident :
        loadingSlowCenter N (fun r q =>
          (loadingTrajectory N L D s j i (endpointPulse aCal) r).primal q - D) t =
        loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
          (endpointFast aCal) m := by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates, hkm] using hpersist_m.2.1
    have hF_ident :
        loadingFastCoordinates N
            (fun r q =>
              (loadingTrajectory N L D s j i (endpointPulse aCal) r).primal q - D)
            (fun r q =>
              -retainedLoadingTracker N L D s j i (endpointPulse aCal) r q / L) t =
          loadingFormalFastState N s kRef (endpointXi aCal)
            (endpointFast aCal) m := by
      simpa [endpointXi, endpointFast, endpointX, endpointU, endpointPulse,
        loadingSlowCenter, loadingFastCoordinates, hkm] using hpersist_m.2.2
    have herr := hforward_error m hPm hmQ
    have hratio_one : 1 ≤ (Ref m).1 / (Ref (P - kRef)).1 := by
      apply (le_div_iff₀ (hreference_eq24 (P - kRef)).1).2
      simpa using hreference_mono (P - kRef) m hPm
    have hxi_lower : 7 * D / 64 ≤
        loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
          (endpointFast aCal) m := by
      have hlower := (abs_le.mp herr).1
      have htarget_lower : D / 8 ≤
          (Ref m).1 / (Ref (P - kRef)).1 * (D / 8) :=
        le_mul_of_one_le_left (div_nonneg hD.le (by norm_num)) hratio_one
      linarith only [hlower, htarget_lower]
    have hmean_error := loading_arithmetic_mean_center_error_le_fast
      N L D s j i (endpointPulse aCal) t
    have hmean_error' :
        |loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D -
            loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
              (endpointFast aCal) m| ≤
          nodeSupNorm
            (loadingFormalFastState N s kRef (endpointXi aCal)
              (endpointFast aCal) m).1 := by
      simpa [hxi_ident, hF_ident] using hmean_error
    have hsup_fast :
        nodeSupNorm
            (loadingFormalFastState N s kRef (endpointXi aCal)
              (endpointFast aCal) m).1 ≤ D / 64 :=
      (le_add_of_nonneg_right
        (Finset.sum_nonneg fun q _ => abs_nonneg _)).trans
          (hformal_fast_cap m hmQ)
    have hmean_lower : 6 * D / 64 ≤
        loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D := by
      have hlower := (abs_le.mp hmean_error').1
      linarith
    have hmean_shift_abs :
        |loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D| <
          D / 2 := by
      have htriangle := abs_add_le
        (loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D -
          loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m)
        (loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
          (endpointFast aCal) m)
      have hid : loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D =
          (loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D -
            loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
              (endpointFast aCal) m) +
          loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
            (endpointFast aCal) m := by ring
      rw [← hid] at htriangle
      have hsafe := hformal_safe m hmQ
      have hmean_to_gauge :
          |loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D -
              loadingFormalCorrectedCenter N s kRef (endpointXi aCal)
                (endpointFast aCal) m| ≤
            nodeSupNorm
                (loadingFormalFastState N s kRef (endpointXi aCal)
                  (endpointFast aCal) m).1 +
              nodeL1Norm
                (loadingFormalFastState N s kRef (endpointXi aCal)
                  (endpointFast aCal) m).2 :=
        hmean_error'.trans (le_add_of_nonneg_right
          (Finset.sum_nonneg fun q _ => abs_nonneg _))
      linarith
    have hmean_interval := abs_lt.mp hmean_shift_abs
    have hmean_lo : D / 2 ≤
        loadingArithmeticMean N L D s j i (endpointPulse aCal) t := by
      linarith
    have hmean_hi :
        loadingArithmeticMean N L D s j i (endpointPulse aCal) t ≤
          3 * D / 2 := by
      linarith
    rw [negativeCurvatureDerivative_eq_negative_branch L D
      (loadingArithmeticMean N L D s j i (endpointPulse aCal) t)
      hD hmean_lo hmean_hi]
    rw [abs_mul, abs_of_pos hL,
      abs_of_nonpos (by linarith [hmean_lower])]
    have hdist : D / 16 ≤
        loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D := by
      linarith only [hmean_lower, hD]
    calc
      L * D / 16 = L * (D / 16) := by ring
      _ ≤ L *
          (loadingArithmeticMean N L D s j i (endpointPulse aCal) t - D) :=
        mul_le_mul_of_nonneg_left hdist hL.le
      _ = L *
          -(D - loadingArithmeticMean N L D s j i (endpointPulse aCal) t) := by
        ring

set_option maxHeartbeats 1000000

/-! ## The varying-dimension instance class and the literal minimax risk -/

/-- The integral-defined storage potential has exactly the printed derivative
as its gradient.  This is the objective-side calculus input for the product
instance used in (41)--(42). -/
theorem negativeCurvaturePotential_hasGradientAt
    (L D x : ℝ) (hD : 0 ≤ D) :
    HasGradientAt (negativeCurvaturePotential L D)
      (negativeCurvatureDerivative L D x) x := by
  have hcont := negative_curvature_derivative_continuous L D hD
  unfold negativeCurvaturePotential
  simpa using
    (intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt).hasGradientAt

/-- The printed storage derivative has the exact global Lipschitz constant
needed by the source instance, rather than a sum of coordinate constants. -/
theorem negativeCurvatureDerivative_norm_sub_le
    (L D x y : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    ‖negativeCurvatureDerivative L D x -
        negativeCurvatureDerivative L D y‖ ≤ L * ‖x - y‖ := by
  simp only [Real.norm_eq_abs]
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    rw [abs_le]
    constructor <;>
      unfold negativeCurvatureDerivative negativeCurvatureDerivativePositive <;>
      split_ifs <;> nlinarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [abs_le]
    constructor <;>
      unfold negativeCurvatureDerivative negativeCurvatureDerivativePositive <;>
      split_ifs <;> nlinarith

/-- Objective-side legality of each storage coordinate.  This is stated in
the exact form required by `Setup.local_smooth`. -/
theorem negativeCurvaturePotential_local_smooth
    (L D : ℝ) (hL : 0 < L) (hD : 0 ≤ D) :
    Differentiable ℝ (negativeCurvaturePotential L D) ∧
      LipschitzWith ⟨L, hL.le⟩
        (gradient (negativeCurvaturePotential L D)) := by
  constructor
  · intro x
    exact (negativeCurvaturePotential_hasGradientAt L D x hD).differentiableAt
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hgrad (z : ℝ) :
        gradient (negativeCurvaturePotential L D) z =
          negativeCurvatureDerivative L D z :=
      (negativeCurvaturePotential_hasGradientAt L D z hD).gradient
    rw [hgrad x, hgrad y]
    simpa [Real.dist_eq] using
      negativeCurvatureDerivative_norm_sub_le L D x y hL.le hD

theorem negativeCurvatureDerivative_neg
    (L D x : ℝ) :
    negativeCurvatureDerivative L D (-x) =
      -negativeCurvatureDerivative L D x := by
  by_cases hx : x < 0
  · have hnegx : ¬ -x < 0 := by linarith
    simp [negativeCurvatureDerivative, hx, hnegx]
  · by_cases hx0 : x = 0
    · subst x
      simp [negativeCurvatureDerivative_zero]
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx0)
      have hnegx : -x < 0 := by linarith
      simp [negativeCurvatureDerivative, hx, hnegx]

theorem loadingPulse_neg
    (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ) :
    loadingPulse j i (-e) t = -loadingPulse j i e t := by
  funext q
  by_cases h : t = j ∧ q = i <;> simp [loadingPulse, h]

/-- Oddness of the storage derivative and of the unique pulse makes the
complete scalar oracle odd. -/
theorem loadingOracle_neg
    (L D : ℝ) (j : ℕ) (i : Fin n) (e : ℝ) (t : ℕ)
    (X : Fin n → ℝ) :
    loadingOracle L D j i (-e) t (-X) =
      -loadingOracle L D j i e t X := by
  funext q
  simp only [loadingOracle, Pi.neg_apply, Pi.add_apply]
  rw [negativeCurvatureDerivative_neg, loadingPulse_neg]
  simp only [Pi.neg_apply]
  ring

/-- The trajectory driven by the negative atom is the pointwise reflection of
the trajectory driven by the positive atom. -/
theorem loadingTrajectory_neg
    (N : NetworkSetup n) (L D s : ℝ) (j : ℕ) (i : Fin n) (e : ℝ)
    (t : ℕ) :
    (loadingTrajectory N L D s j i (-e) t).primal =
        -(loadingTrajectory N L D s j i e t).primal ∧
      (loadingTrajectory N L D s j i (-e) t).tracker =
        -(loadingTrajectory N L D s j i e t).tracker := by
  induction t with
  | zero =>
      constructor
      · simp [loadingTrajectory]
      · simpa [loadingTrajectory] using
          loadingOracle_neg L D j i e 0 (0 : Fin n → ℝ)
  | succ t ih =>
      have hnext_core :
          N.rowMix t *ᵥ (-(loadingTrajectory N L D s j i e t).primal) -
              (s / L) • (-(loadingTrajectory N L D s j i e t).tracker) =
            -(N.rowMix t *ᵥ
                (loadingTrajectory N L D s j i e t).primal -
              (s / L) •
                (loadingTrajectory N L D s j i e t).tracker) := by
        funext q
        simp [Matrix.smulVec, Matrix.mulVec, dotProduct]
        ring
      have hprimal :
          (loadingTrajectory N L D s j i (-e) (t + 1)).primal =
            -(loadingTrajectory N L D s j i e (t + 1)).primal := by
        simp only [loadingTrajectory, SOptLib.pushPullStep]
        rw [ih.1, ih.2]
        exact hnext_core
      have hnext_core_q (q : Fin n) :
          (Matrix.smulVec (N.rowMix t)
                (-(loadingTrajectory N L D s j i e t).primal) -
              (s / L) •
                (-(loadingTrajectory N L D s j i e t).tracker)) q =
            -((Matrix.smulVec (N.rowMix t)
                (loadingTrajectory N L D s j i e t).primal -
              (s / L) •
                (loadingTrajectory N L D s j i e t).tracker) q) := by
        simp [Matrix.smulVec, Matrix.mulVec, dotProduct]
        ring
      refine ⟨hprimal, ?_⟩
      funext q
      simp only [loadingTrajectory, SOptLib.pushPullStep, Pi.add_apply,
        Pi.sub_apply, Pi.neg_apply]
      rw [ih.1, ih.2]
      simp only [loadingOracle, Pi.add_apply]
      rw [hnext_core_q q]
      rw [negativeCurvatureDerivative_neg]
      simp only [Pi.neg_apply]
      rw [negativeCurvatureDerivative_neg]
      rw [congrFun (loadingPulse_neg j i e (t + 1)) q,
        congrFun (loadingPulse_neg j i e t) q]
      simp only [Pi.neg_apply]
      simp [Matrix.smulVec, Matrix.mulVec, dotProduct]
      ring

/-- The storage potential is even, as required when a calibrated loading uses
the reflected pulse sign. -/
theorem negativeCurvaturePotential_neg
    (L D x : ℝ) :
    negativeCurvaturePotential L D (-x) =
      negativeCurvaturePotential L D x := by
  unfold negativeCurvaturePotential
  calc
    (∫ y in (0 : ℝ)..-x, negativeCurvatureDerivative L D y) =
        -(∫ y in -x..(0 : ℝ), negativeCurvatureDerivative L D y) := by
      rw [intervalIntegral.integral_symm]
    _ = -(∫ y in (0 : ℝ)..x,
          negativeCurvatureDerivative L D (-y)) := by
      rw [intervalIntegral.integral_comp_neg]
      simp
    _ = ∫ y in (0 : ℝ)..x, negativeCurvatureDerivative L D y := by
      simp_rw [negativeCurvatureDerivative_neg]
      rw [intervalIntegral.integral_neg]
      ring

theorem negativeCurvaturePotential_eq_first_branch
    (L D x : ℝ) (hD : 0 ≤ D) (hx0 : 0 ≤ x) (hx : x ≤ D / 2) :
    negativeCurvaturePotential L D x = L * x ^ 2 / 2 := by
  unfold negativeCurvaturePotential
  have heq : Set.EqOn (negativeCurvatureDerivative L D)
      (fun y : ℝ => L * y) (Set.uIcc (0 : ℝ) x) := by
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    have hy0 : ¬y < 0 := not_lt_of_ge hy.1
    have hyhalf : y ≤ D / 2 := hy.2.trans hx
    simp [negativeCurvatureDerivative, negativeCurvatureDerivativePositive,
      hy0, hyhalf]
  rw [intervalIntegral.integral_congr heq]
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x) (f := fun y : ℝ => L * y ^ 2 / 2)
    (f' := fun y : ℝ => L * y)
    (fun y _hy => by
      convert ((((hasDerivAt_id y).pow 2).const_mul L).div_const 2) using 1 <;>
        simp [id] <;> ring)
    ((continuous_const.mul continuous_id).intervalIntegrable 0 x)
  rw [hcalc]
  ring

theorem negativeCurvaturePotential_eq_middle_branch
    (L D x : ℝ) (hD : 0 < D)
    (hxlo : D / 2 ≤ x) (hxhi : x ≤ 3 * D / 2) :
    negativeCurvaturePotential L D x =
      L * (D * x - x ^ 2 / 2 - D ^ 2 / 4) := by
  have hcont := negative_curvature_derivative_continuous L D hD.le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := negativeCurvatureDerivative L D)
    (a := (0 : ℝ)) (b := D / 2) (c := x)
    (hcont.intervalIntegrable (0 : ℝ) (D / 2))
    (hcont.intervalIntegrable (D / 2) x)
  have hfirst := negativeCurvaturePotential_eq_first_branch
    L D (D / 2) hD.le (by positivity) le_rfl
  have heq : Set.EqOn (negativeCurvatureDerivative L D)
      (fun y : ℝ => L * (D - y)) (Set.uIcc (D / 2) x) := by
    intro y hy
    rw [Set.uIcc_of_le hxlo] at hy
    exact negativeCurvatureDerivative_eq_negative_branch
      L D y hD hy.1 (hy.2.trans hxhi)
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := D / 2) (b := x)
    (f := fun y : ℝ => L * (D * y - y ^ 2 / 2))
    (f' := fun y : ℝ => L * (D - y))
    (fun y _hy => by
      convert (((((hasDerivAt_const y D).mul (hasDerivAt_id y)).sub
        (((hasDerivAt_id y).pow 2).div_const 2)).const_mul L)) using 1 <;>
        simp [id] <;> ring)
    ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable
      (D / 2) x)
  unfold negativeCurvaturePotential at hfirst ⊢
  rw [← hsplit, hfirst, intervalIntegral.integral_congr heq, hcalc]
  ring

theorem negativeCurvaturePotential_eq_third_branch
    (L D x : ℝ) (hD : 0 < D)
    (hxlo : 3 * D / 2 ≤ x) (hxhi : x ≤ 2 * D) :
    negativeCurvaturePotential L D x = L * (x - 2 * D) ^ 2 / 2 := by
  have hcont := negative_curvature_derivative_continuous L D hD.le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := negativeCurvatureDerivative L D)
    (a := (0 : ℝ)) (b := 3 * D / 2) (c := x)
    (hcont.intervalIntegrable (0 : ℝ) (3 * D / 2))
    (hcont.intervalIntegrable (3 * D / 2) x)
  have hmiddle := negativeCurvaturePotential_eq_middle_branch
    L D (3 * D / 2) hD (by linarith) le_rfl
  have heq : Set.EqOn (negativeCurvatureDerivative L D)
      (fun y : ℝ => L * (y - 2 * D)) (Set.uIcc (3 * D / 2) x) := by
    intro y hy
    rw [Set.uIcc_of_le hxlo] at hy
    by_cases hthree : y ≤ 3 * D / 2
    · have hyeq : y = 3 * D / 2 := le_antisymm hthree hy.1
      subst y
      rw [negativeCurvatureDerivative_eq_negative_branch L D (3 * D / 2)
        hD (by linarith) le_rfl]
      ring
    · have hy0 : ¬y < 0 := by nlinarith [hD, hy.1]
      have hhalf : ¬y ≤ D / 2 := by nlinarith [hD, hy.1]
      have htwo : y ≤ 2 * D := hy.2.trans hxhi
      simp [negativeCurvatureDerivative, negativeCurvatureDerivativePositive,
        hy0, hhalf, hthree, htwo]
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 3 * D / 2) (b := x)
    (f := fun y : ℝ => L * (y ^ 2 / 2 - 2 * D * y))
    (f' := fun y : ℝ => L * (y - 2 * D))
    (fun y _hy => by
      convert (((((hasDerivAt_id y).pow 2).div_const 2).sub
        ((hasDerivAt_const y (2 * D)).mul (hasDerivAt_id y))).const_mul L)
        using 1 <;> simp [id] <;> ring)
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable
      (3 * D / 2) x)
  unfold negativeCurvaturePotential at hmiddle ⊢
  rw [← hsplit, hmiddle, intervalIntegral.integral_congr heq, hcalc]
  ring

theorem negativeCurvaturePotential_eq_outer_branch
    (L D x : ℝ) (hD : 0 < D) (hx : 2 * D ≤ x) :
    negativeCurvaturePotential L D x = 0 := by
  have hcont := negative_curvature_derivative_continuous L D hD.le
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := negativeCurvatureDerivative L D)
    (a := (0 : ℝ)) (b := 2 * D) (c := x)
    (hcont.intervalIntegrable (0 : ℝ) (2 * D))
    (hcont.intervalIntegrable (2 * D) x)
  have hthird := negativeCurvaturePotential_eq_third_branch
    L D (2 * D) hD (by linarith) le_rfl
  have heq : Set.EqOn (negativeCurvatureDerivative L D)
      (fun _y : ℝ => 0) (Set.uIcc (2 * D) x) := by
    intro y hy
    rw [Set.uIcc_of_le hx] at hy
    have hy0 : ¬y < 0 := by nlinarith [hD, hy.1]
    have hhalf : ¬y ≤ D / 2 := by nlinarith [hD, hy.1]
    have hthree : ¬y ≤ 3 * D / 2 := by nlinarith [hD, hy.1]
    by_cases htwo : y ≤ 2 * D
    · have hyeq : y = 2 * D := le_antisymm htwo hy.1
      subst y
      unfold negativeCurvatureDerivative negativeCurvatureDerivativePositive
      rw [if_neg (by linarith : ¬2 * D < 0),
        if_neg (by linarith : ¬2 * D ≤ D / 2),
        if_neg (by linarith : ¬2 * D ≤ 3 * D / 2), if_pos le_rfl]
      ring
    · simp [negativeCurvatureDerivative, negativeCurvatureDerivativePositive,
        hy0, hhalf, hthree, htwo]
  unfold negativeCurvaturePotential at hthird ⊢
  rw [← hsplit, hthird, intervalIntegral.integral_congr heq]
  simp

/-- The source storage potential is nonnegative and is normalized to vanish at
the common initialization/minimizer. -/
theorem negativeCurvaturePotential_nonneg
    (L D x : ℝ) (hL : 0 ≤ L) (hD : 0 < D) :
    0 ≤ negativeCurvaturePotential L D x := by
  by_cases hx0 : 0 ≤ x
  · by_cases hfirst : x ≤ D / 2
    · rw [negativeCurvaturePotential_eq_first_branch L D x hD.le hx0 hfirst]
      positivity
    · have hxhalf : D / 2 ≤ x := le_of_not_ge hfirst
      by_cases hmiddle : x ≤ 3 * D / 2
      · rw [negativeCurvaturePotential_eq_middle_branch L D x hD hxhalf hmiddle]
        apply mul_nonneg hL
        have hprod : 0 ≤ (x - D / 2) * (3 * D / 2 - x) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      · have hxthree : 3 * D / 2 ≤ x := le_of_not_ge hmiddle
        by_cases hthird : x ≤ 2 * D
        · rw [negativeCurvaturePotential_eq_third_branch L D x hD hxthree hthird]
          positivity
        · rw [negativeCurvaturePotential_eq_outer_branch L D x hD
            (le_of_not_ge hthird)]
  · have hxneg : 0 ≤ -x := by linarith
    rw [← negativeCurvaturePotential_neg L D x]
    by_cases hfirst : -x ≤ D / 2
    · rw [negativeCurvaturePotential_eq_first_branch L D (-x) hD.le hxneg hfirst]
      positivity
    · have hxhalf : D / 2 ≤ -x := le_of_not_ge hfirst
      by_cases hmiddle : -x ≤ 3 * D / 2
      · rw [negativeCurvaturePotential_eq_middle_branch L D (-x) hD hxhalf hmiddle]
        apply mul_nonneg hL
        have hprod : 0 ≤ (-x - D / 2) * (3 * D / 2 - (-x)) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      · have hxthree : 3 * D / 2 ≤ -x := le_of_not_ge hmiddle
        by_cases hthird : -x ≤ 2 * D
        · rw [negativeCurvaturePotential_eq_third_branch L D (-x) hD hxthree hthird]
          positivity
        · rw [negativeCurvaturePotential_eq_outer_branch L D (-x) hD
            (le_of_not_ge hthird)]

theorem negativeCurvaturePotential_sInf
    (L D : ℝ) (hL : 0 ≤ L) (hD : 0 < D) :
    sInf (Set.range (negativeCurvaturePotential L D)) = 0 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨0, ⟨0, by simp [negativeCurvaturePotential]⟩⟩
  · rintro _ ⟨x, rfl⟩
    exact negativeCurvaturePotential_nonneg L D x hL hD
  · intro w hw
    exact ⟨0, ⟨0, by simp [negativeCurvaturePotential]⟩, hw⟩

/-- Complete objective-side legality package for one equation-(41) storage
coordinate.  Its fields feed the separable product `Setup` constructor. -/
theorem negativeCurvaturePotential_setup_spec
    (L D : ℝ) (hL : 0 < L) (hD : 0 < D) :
    (∀ x, HasGradientAt (negativeCurvaturePotential L D)
      (negativeCurvatureDerivative L D x) x) ∧
    Differentiable ℝ (negativeCurvaturePotential L D) ∧
    LipschitzWith ⟨L, hL.le⟩ (gradient (negativeCurvaturePotential L D)) ∧
    (∀ x, 0 ≤ negativeCurvaturePotential L D x) ∧
    sInf (Set.range (negativeCurvaturePotential L D)) = 0 := by
  refine ⟨fun x => negativeCurvaturePotential_hasGradientAt L D x hD.le,
    (negativeCurvaturePotential_local_smooth L D hL hD.le).1,
    (negativeCurvaturePotential_local_smooth L D hL hD.le).2,
    fun x => negativeCurvaturePotential_nonneg L D x hL.le hD, ?_⟩
  exact negativeCurvaturePotential_sInf L D hL.le hD

/-! ### The deterministic gap coordinate, source equations (29)--(30) -/

def deterministicGapDerivativePositive (L A x : ℝ) : ℝ :=
  L * if x ≤ A then -x else x - 2 * A

def deterministicGapDerivative (L A x : ℝ) : ℝ :=
  if x < 0 then -deterministicGapDerivativePositive L A (-x)
  else deterministicGapDerivativePositive L A x

noncomputable def deterministicGapPotential (L A x : ℝ) : ℝ :=
  L * A ^ 2 + ∫ y in (0 : ℝ)..x, deterministicGapDerivative L A y

theorem deterministic_gap_derivative_continuous
    (L A : ℝ) (hA : 0 ≤ A) :
    Continuous (deterministicGapDerivative L A) := by
  have hinner : Continuous (fun x : ℝ => L * (-x)) :=
    continuous_const.mul continuous_id.neg
  have houter : Continuous (fun x : ℝ => L * (x - 2 * A)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  have hpos : Continuous (deterministicGapDerivativePositive L A) := by
    unfold deterministicGapDerivativePositive
    simpa only [mul_ite] using
      hinner.if_le houter continuous_id continuous_const (by
        intro x hx
        change x = A at hx
        subst x
        ring)
  have hneg : Continuous (fun x : ℝ =>
      -deterministicGapDerivativePositive L A (-x)) :=
    (hpos.comp continuous_id.neg).neg
  have hwhole : Continuous (fun x : ℝ =>
      if (0 : ℝ) ≤ x then deterministicGapDerivativePositive L A x
      else -deterministicGapDerivativePositive L A (-x)) := by
    exact hpos.if_le hneg continuous_const continuous_id (by
      intro x hx
      change (0 : ℝ) = x at hx
      subst x
      simp [deterministicGapDerivativePositive, hA])
  convert hwhole using 1
  funext x
  unfold deterministicGapDerivative
  by_cases hx : x < 0
  · simp [hx, not_le.mpr hx]
  · simp [hx, le_of_not_gt hx]

theorem deterministicGapDerivative_neg (L A x : ℝ) (hA : 0 ≤ A) :
    deterministicGapDerivative L A (-x) =
      -deterministicGapDerivative L A x := by
  by_cases hx : x < 0
  · have hnegx : ¬ -x < 0 := by linarith
    simp [deterministicGapDerivative, hx, hnegx]
  · by_cases hx0 : x = 0
    · subst x
      simp [deterministicGapDerivative, deterministicGapDerivativePositive, hA]
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hx0)
      have hnegx : -x < 0 := by linarith
      simp [deterministicGapDerivative, hx, hnegx]

theorem deterministicGapDerivative_eq_neg_mul_of_abs_le
    (L A x : ℝ) (hx : |x| ≤ A) :
    deterministicGapDerivative L A x = -L * x := by
  have hbounds := abs_le.mp hx
  unfold deterministicGapDerivative deterministicGapDerivativePositive
  split_ifs <;> nlinarith

theorem deterministicGapPotential_hasGradientAt
    (L A x : ℝ) (hA : 0 ≤ A) :
    HasGradientAt (deterministicGapPotential L A)
      (deterministicGapDerivative L A x) x := by
  have hcont := deterministic_gap_derivative_continuous L A hA
  unfold deterministicGapPotential
  simpa using
    ((intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt).const_add (L * A ^ 2)).hasGradientAt

theorem deterministicGapDerivative_norm_sub_le
    (L A x y : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) :
    ‖deterministicGapDerivative L A x -
        deterministicGapDerivative L A y‖ ≤ L * ‖x - y‖ := by
  simp only [Real.norm_eq_abs]
  by_cases hxy : x ≤ y
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    rw [abs_le]
    constructor <;>
      unfold deterministicGapDerivative deterministicGapDerivativePositive <;>
      split_ifs <;> nlinarith
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    rw [abs_le]
    constructor <;>
      unfold deterministicGapDerivative deterministicGapDerivativePositive <;>
      split_ifs <;> nlinarith

theorem deterministicGapPotential_local_smooth
    (L A : ℝ) (hL : 0 < L) (hA : 0 ≤ A) :
    Differentiable ℝ (deterministicGapPotential L A) ∧
      LipschitzWith ⟨L, hL.le⟩
        (gradient (deterministicGapPotential L A)) := by
  constructor
  · intro x
    exact (deterministicGapPotential_hasGradientAt L A x hA).differentiableAt
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hgrad (z : ℝ) :
        gradient (deterministicGapPotential L A) z =
          deterministicGapDerivative L A z :=
      (deterministicGapPotential_hasGradientAt L A z hA).gradient
    rw [hgrad x, hgrad y]
    simpa [Real.dist_eq] using
      deterministicGapDerivative_norm_sub_le L A x y hL.le hA

theorem deterministicGapPotential_neg
    (L A x : ℝ) (hA : 0 ≤ A) :
    deterministicGapPotential L A (-x) =
      deterministicGapPotential L A x := by
  unfold deterministicGapPotential
  congr 1
  calc
    (∫ y in (0 : ℝ)..-x, deterministicGapDerivative L A y) =
        -(∫ y in -x..(0 : ℝ), deterministicGapDerivative L A y) := by
      rw [intervalIntegral.integral_symm]
    _ = -(∫ y in (0 : ℝ)..x, deterministicGapDerivative L A (-y)) := by
      rw [intervalIntegral.integral_comp_neg]
      simp
    _ = ∫ y in (0 : ℝ)..x, deterministicGapDerivative L A y := by
      simp_rw [deterministicGapDerivative_neg L A _ hA]
      rw [intervalIntegral.integral_neg]
      ring

theorem deterministicGapPotential_eq_inner_nonneg
    (L A x : ℝ) (hA : 0 ≤ A) (hx0 : 0 ≤ x) (hxA : x ≤ A) :
    deterministicGapPotential L A x = L * (A ^ 2 - x ^ 2 / 2) := by
  unfold deterministicGapPotential
  have heq : Set.EqOn (deterministicGapDerivative L A)
      (fun y : ℝ => L * (-y)) (Set.uIcc (0 : ℝ) x) := by
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    have hy0 : ¬y < 0 := not_lt_of_ge hy.1
    have hyA : y ≤ A := hy.2.trans hxA
    simp [deterministicGapDerivative, deterministicGapDerivativePositive,
      hy0, hyA]
  rw [intervalIntegral.integral_congr heq]
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := x) (f := fun y : ℝ => -L * y ^ 2 / 2)
    (f' := fun y : ℝ => L * (-y))
    (fun y _hy => by
      convert ((((hasDerivAt_id y).pow 2).const_mul (-L)).div_const 2)
        using 1 <;> simp [id] <;> ring)
    ((continuous_const.mul continuous_id.neg).intervalIntegrable 0 x)
  rw [hcalc]
  ring

theorem deterministicGapPotential_eq_outer_nonneg
    (L A x : ℝ) (hA : 0 ≤ A) (hxA : A ≤ x) :
    deterministicGapPotential L A x = L * (x - 2 * A) ^ 2 / 2 := by
  have hcont := deterministic_gap_derivative_continuous L A hA
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (μ := MeasureTheory.volume) (f := deterministicGapDerivative L A)
    (a := (0 : ℝ)) (b := A) (c := x)
    (hcont.intervalIntegrable (0 : ℝ) A)
    (hcont.intervalIntegrable A x)
  have hinner := deterministicGapPotential_eq_inner_nonneg
    L A A hA hA le_rfl
  have heq : Set.EqOn (deterministicGapDerivative L A)
      (fun y : ℝ => L * (y - 2 * A)) (Set.uIcc A x) := by
    intro y hy
    rw [Set.uIcc_of_le hxA] at hy
    have hy_nonneg : 0 ≤ y := hA.trans hy.1
    have hy0 : ¬y < 0 := not_lt_of_ge hy_nonneg
    by_cases hyA : y ≤ A
    · have hyeq : y = A := le_antisymm hyA hy.1
      subst y
      simp [deterministicGapDerivative, deterministicGapDerivativePositive,
        hA]
      ring
    · simp [deterministicGapDerivative, deterministicGapDerivativePositive,
        hy0, hyA]
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := A) (b := x)
    (f := fun y : ℝ => L * (y ^ 2 / 2 - 2 * A * y))
    (f' := fun y : ℝ => L * (y - 2 * A))
    (fun y _hy => by
      convert (((((hasDerivAt_id y).pow 2).div_const 2).sub
        ((hasDerivAt_const y (2 * A)).mul (hasDerivAt_id y))).const_mul L)
        using 1 <;> simp [id] <;> ring)
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable
      A x)
  unfold deterministicGapPotential at hinner ⊢
  rw [← hsplit]
  calc
    L * A ^ 2 +
        ((∫ y in (0 : ℝ)..A, deterministicGapDerivative L A y) +
          ∫ y in A..x, deterministicGapDerivative L A y) =
        (L * A ^ 2 +
          ∫ y in (0 : ℝ)..A, deterministicGapDerivative L A y) +
          ∫ y in A..x, deterministicGapDerivative L A y := by ring
    _ = L * (A ^ 2 - A ^ 2 / 2) +
          ∫ y in A..x, deterministicGapDerivative L A y := by rw [hinner]
    _ = L * (A ^ 2 - A ^ 2 / 2) +
          ∫ y in A..x, L * (y - 2 * A) := by
            rw [intervalIntegral.integral_congr heq]
    _ = L * (x - 2 * A) ^ 2 / 2 := by rw [hcalc]; ring

theorem deterministicGapPotential_eq_inner
    (L A x : ℝ) (hA : 0 ≤ A) (hx : |x| ≤ A) :
    deterministicGapPotential L A x = L * (A ^ 2 - x ^ 2 / 2) := by
  by_cases hx0 : 0 ≤ x
  · exact deterministicGapPotential_eq_inner_nonneg L A x hA hx0
      ((le_abs_self x).trans hx)
  · rw [← deterministicGapPotential_neg L A x hA]
    have hneg0 : 0 ≤ -x := by linarith
    have hnegA : -x ≤ A := by
      rw [← abs_of_nonpos (le_of_not_ge hx0)]
      exact hx
    rw [deterministicGapPotential_eq_inner_nonneg L A (-x) hA hneg0 hnegA]
    ring

theorem deterministicGapPotential_nonneg
    (L A x : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) :
    0 ≤ deterministicGapPotential L A x := by
  by_cases hx0 : 0 ≤ x
  · by_cases hxA : x ≤ A
    · rw [deterministicGapPotential_eq_inner_nonneg L A x hA hx0 hxA]
      apply mul_nonneg hL
      nlinarith [sq_nonneg (A - x), sq_nonneg x]
    · rw [deterministicGapPotential_eq_outer_nonneg L A x hA
          (le_of_not_ge hxA)]
      positivity
  · rw [← deterministicGapPotential_neg L A x hA]
    have hneg0 : 0 ≤ -x := by linarith
    by_cases hnegA : -x ≤ A
    · rw [deterministicGapPotential_eq_inner_nonneg L A (-x) hA hneg0 hnegA]
      apply mul_nonneg hL
      nlinarith [sq_nonneg (A + x), sq_nonneg x]
    · rw [deterministicGapPotential_eq_outer_nonneg L A (-x) hA
          (le_of_not_ge hnegA)]
      positivity

theorem deterministicGapPotential_sInf
    (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) :
    sInf (Set.range (deterministicGapPotential L A)) = 0 := by
  have hzero : deterministicGapPotential L A (2 * A) = 0 := by
    rw [deterministicGapPotential_eq_outer_nonneg L A (2 * A) hA (by linarith)]
    ring
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨0, ⟨2 * A, hzero⟩⟩
  · rintro _ ⟨x, rfl⟩
    exact deterministicGapPotential_nonneg L A x hL hA
  · intro w hw
    exact ⟨0, ⟨2 * A, hzero⟩, hw⟩

theorem deterministicGapPotential_setup_spec
    (L A : ℝ) (hL : 0 < L) (hA : 0 ≤ A) :
    (∀ x, HasGradientAt (deterministicGapPotential L A)
      (deterministicGapDerivative L A x) x) ∧
    Differentiable ℝ (deterministicGapPotential L A) ∧
    LipschitzWith ⟨L, hL.le⟩ (gradient (deterministicGapPotential L A)) ∧
    (∀ x, 0 ≤ deterministicGapPotential L A x) ∧
    sInf (Set.range (deterministicGapPotential L A)) = 0 := by
  refine ⟨fun x => deterministicGapPotential_hasGradientAt L A x hA,
    (deterministicGapPotential_local_smooth L A hL hA).1,
    (deterministicGapPotential_local_smooth L A hL hA).2,
    fun x => deterministicGapPotential_nonneg L A x hL.le hA, ?_⟩
  exact deterministicGapPotential_sInf L A hL.le hA

theorem deterministicGapPotential_gap_fill
    (L Δ A x y : ℝ) (hL : 0 < L) (hA : 0 ≤ A)
    (hA_sq : A ^ 2 = Δ / (2 * L)) (hx : |x| ≤ A)
    (hy_sq : y ^ 2 = Δ / L + x ^ 2) :
    deterministicGapPotential L A x + L * y ^ 2 / 2 = Δ := by
  rw [deterministicGapPotential_eq_inner L A x hA hx, hy_sq, hA_sq]
  field_simp [hL.ne']
  ring

/-- A network-only positive cap under which the equation-(24) unit-center
orbit has the precise positivity, ratio, and small-fast-state bounds needed
for the deterministic signal coordinate in equation (30). -/
theorem deterministic_signal_reference_cap (N : NetworkSetup n) :
    ∃ sSignal : ℝ, 0 < sSignal ∧ sSignal ≤ 1 / (64 * n) ∧
      ∀ s : ℝ, 0 < s → s ≤ sSignal →
        let R := loadingUnitCenterReferenceOrbit N s 0
        ∀ m,
          0 < (R m).1 ∧
          1 + s * gain N m / 2 ≤ (R (m + 1)).1 / (R m).1 ∧
          (R (m + 1)).1 / (R m).1 ≤
            1 + 3 * s * gain N m / 2 ∧
          nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
            (1 / 64) * (R m).1 := by
  obtain ⟨Mtri, hMtri, _hMtri_nonneg, htriangular⟩ :=
    exists_loading_triangular_product_constant N
  let M : ℝ := max 1 Mtri
  let J0 : ℝ := 2 * ((n : ℝ) + 1)
  let B0 : ℝ := 2 * (n : ℝ) * ((n : ℝ) + 1)
  let Cp : ℝ := M * B0 / (1 - loadingTransverseRate N)
  have hM : 1 ≤ M := le_max_left _ _
  have hMtri_le : Mtri ≤ M := le_max_right _ _
  have htrans_lt_one : loadingTransverseRate N < 1 := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hfast_lt_one : loadingFastRate N < 1 := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hgap : 0 < loadingTransverseRate N - loadingFastRate N := by
    unfold loadingTransverseRate
    linarith [hfast_lt_one]
  have hJ0 : 0 < J0 := by dsimp [J0]; positivity
  have hB0 : 0 < B0 := by
    dsimp [B0]
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr N.hn)) (by
      positivity)
  have hCp : 0 < Cp := by
    dsimp [Cp]
    exact div_pos (mul_pos (lt_of_lt_of_le zero_lt_one hM) hB0)
      (sub_pos.mpr htrans_lt_one)
  have hgainFloor : 0 < gainFloor N := by
    have hmu : 0 < mixingMinorization N := by
      unfold mixingMinorization
      split_ifs
      · exact pow_pos ((lt_min_iff).2 ⟨N.ha, by norm_num⟩) _
      · norm_num
    exact (mul_pos (Nat.cast_pos.mpr N.hn) hmu).trans_le
      (gainFloor_ge_n_mul_mixingMinorization N)
  let sPert : ℝ :=
    (loadingTransverseRate N - loadingFastRate N) / (M * J0)
  let sCenter : ℝ :=
    min ((gainFloor N / 2) / Cp) ((1 / 64) / Cp)
  let sClass : ℝ := 1 / (64 * n)
  let sSignal : ℝ := min sPert (min sCenter sClass)
  have hsPert : 0 < sPert := by
    dsimp [sPert]
    exact div_pos hgap (mul_pos (lt_of_lt_of_le zero_lt_one hM) hJ0)
  have hsCenter : 0 < sCenter := by
    dsimp [sCenter]
    exact lt_min (div_pos (div_pos hgainFloor (by norm_num)) hCp)
      (div_pos (by norm_num) hCp)
  have hsClass : 0 < sClass := by
    dsimp [sClass]
    exact one_div_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr N.hn))
  have hsSignal : 0 < sSignal := by
    dsimp [sSignal]
    exact lt_min hsPert (lt_min hsCenter hsClass)
  refine ⟨sSignal, hsSignal,
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro s hs hsCap
  let R := loadingUnitCenterReferenceOrbit N s 0
  have hsPertCap : s ≤ sPert := hsCap.trans (min_le_left _ _)
  have hsCenterCap : s ≤ sCenter :=
    hsCap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcenterFloorCap : Cp * s ≤ gainFloor N / 2 := by
    have hs' : s ≤ (gainFloor N / 2) / Cp :=
      hsCenterCap.trans (min_le_left _ _)
    have := (le_div_iff₀ hCp).mp hs'
    simpa [mul_comm] using this
  have hcenterFineCap : Cp * s ≤ 1 / 64 := by
    have hs' : s ≤ (1 / 64) / Cp :=
      hsCenterCap.trans (min_le_right _ _)
    have := (le_div_iff₀ hCp).mp hs'
    simpa [mul_comm] using this
  have hperturbationCap :
      loadingFastRate N + M * (s * J0) ≤ loadingTransverseRate N := by
    have hden : 0 < M * J0 :=
      mul_pos (lt_of_lt_of_le zero_lt_one hM) hJ0
    have hmul : s * (M * J0) ≤
        loadingTransverseRate N - loadingFastRate N := by
      apply (le_div_iff₀ hden).mp
      simpa [sPert] using hsPertCap
    nlinarith
  have htriangular' (k t : ℕ) (hkt : k ≤ t) (E K : Fin n → ℝ)
      (hE : dotProduct (absoluteProbability N k) E = 0)
      (hK : (∑ q, K q) = 0) :
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K) := by
    have hraw := htriangular k t hkt E K hE hK
    refine hraw.trans ?_
    have hp : 0 ≤ loadingFastRate N ^ (t - k) := by
      exact pow_nonneg (by
        unfold loadingFastRate loadingTriangularRate
        linarith [mixingRate_nonneg N]) _
    have hg : 0 ≤ nodeSupNorm E + nodeL1Norm K :=
      add_nonneg (nodeSupNorm_nonneg N E)
        (Finset.sum_nonneg fun q _ => abs_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMtri_le hp) hg
  have href := loading_unit_center_reference_bounds N M s 0 hM hs
    htriangular' (by simpa [J0] using hperturbationCap)
    (by simpa [Cp, B0] using hcenterFloorCap)
    (by
      have hcenterOne : Cp * s ≤ 1 / 8 :=
        hcenterFineCap.trans (by norm_num)
      simpa [Cp, B0] using hcenterOne)
  dsimp only
  intro m
  have hm := href m
  refine ⟨by simpa [R] using hm.1, ?_, ?_, ?_⟩
  · simpa [R] using hm.2.1
  · simpa [R] using hm.2.2.1
  · have hfast := hm.2.2.2
    have hscale : Cp * s *
        (loadingUnitCenterReferenceOrbit N s 0 m).1 ≤
        (1 / 64) * (loadingUnitCenterReferenceOrbit N s 0 m).1 :=
      mul_le_mul_of_nonneg_right hcenterFineCap hm.1.le
    exact (by simpa [R, Cp, B0] using hfast.trans hscale)

/-- The scaled equation-(24) orbit chosen at an attaining source window stays
inside the equation-(29) quadratic branch through that window.  Its arithmetic
mean is bounded away from zero by the source's `7A/16` margin. -/
theorem deterministic_signal_reference_window_bounds
    (N : NetworkSetup n) (s A : ℝ) (P Q : ℕ)
    (hs : 0 < s) (hA : 0 < A) (hPQ : P ≤ Q)
    (hbudget : s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon)
    (href :
      let R := loadingUnitCenterReferenceOrbit N s 0
      ∀ m,
        0 < (R m).1 ∧
        1 + s * gain N m / 2 ≤ (R (m + 1)).1 / (R m).1 ∧
        (R (m + 1)).1 / (R m).1 ≤
          1 + 3 * s * gain N m / 2 ∧
        nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
          (1 / 64) * (R m).1) :
    let R := loadingUnitCenterReferenceOrbit N s 0
    let x0 := A / (2 * (R P).1)
    let X : ℕ → Fin n → ℝ := fun t q => x0 * ((R t).1 + (R t).2.1 q)
    let mean : ℕ → ℝ := fun t => (n : ℝ)⁻¹ * ∑ q, X t q
    (∀ t, t ≤ Q → ∀ q, |X t q| ≤ A) ∧
      ∀ t ∈ Finset.Ico P Q, 7 * A / 16 ≤ mean t ∧ mean t ≤ A := by
  let R := loadingUnitCenterReferenceOrbit N s 0
  let x0 := A / (2 * (R P).1)
  let X : ℕ → Fin n → ℝ := fun t q => x0 * ((R t).1 + (R t).2.1 q)
  let mean : ℕ → ℝ := fun t => (n : ℝ)⁻¹ * ∑ q, X t q
  have href' : ∀ m,
      0 < (R m).1 ∧
      1 + s * gain N m / 2 ≤ (R (m + 1)).1 / (R m).1 ∧
      (R (m + 1)).1 / (R m).1 ≤
        1 + 3 * s * gain N m / 2 ∧
      nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
        (1 / 64) * (R m).1 := by
    simpa [R] using href
  have hgain_nonneg (t : ℕ) : 0 ≤ gain N t := by
    unfold gain dotProduct
    exact Finset.sum_nonneg fun q _ =>
      mul_nonneg ((absoluteProbability_mem_stdSimplex N (t + 1)).1 q)
        (pushMass_nonneg N t q)
  have hmono : ∀ u v, u ≤ v → (R u).1 ≤ (R v).1 := by
    intro u v huv
    induction v, huv using Nat.le_induction with
    | base => exact le_rfl
    | @succ v huv ih =>
        have hpos : 0 < (R v).1 := (href' v).1
        have hratio : 1 ≤ (R (v + 1)).1 / (R v).1 := by
          calc
            1 ≤ 1 + s * gain N v / 2 := by
              nlinarith [mul_nonneg hs.le (hgain_nonneg v)]
            _ ≤ (R (v + 1)).1 / (R v).1 := (href' v).2.1
        exact ih.trans (by
          simpa only [one_mul] using (le_div_iff₀ hpos).mp hratio)
  have hexp_upper : Real.exp (3 * epsilon / 2) ≤ 19 / 16 := by
    have hmem : 3 * epsilon / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      norm_num [epsilon]
    have hraw := Real.exp_le_one_add_two_mul_of_mem_Icc_zero_one hmem
    norm_num [epsilon] at hraw ⊢
    exact hraw
  have hratio_window (t : ℕ) (hPt : P ≤ t) (htQ : t ≤ Q) :
      (R t).1 / (R P).1 ≤ 19 / 16 := by
    have hraw := loading_reference_ratio_le_exp_gain
      N s 0 P t hs.le hPt (fun q => (href' q).1)
        (fun q => by simpa [R] using (href' q).2.2.1)
    have hsubset : Finset.Ico P t ⊆ Finset.Ico P Q := by
      intro r hr
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hr).1,
        (Finset.mem_Ico.mp hr).2.trans_le htQ⟩
    have hsum_le :
        (∑ r ∈ Finset.Ico P t, gain N r) ≤
          ∑ r ∈ Finset.Ico P Q, gain N r :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r _ _ => hgain_nonneg r)
    have hscaled : s * (∑ r ∈ Finset.Ico P t, gain N r) ≤ epsilon :=
      (mul_le_mul_of_nonneg_left hsum_le hs.le).trans hbudget
    have hexponent :
        (3 / 2) * s * (∑ r ∈ Finset.Ico P t, gain N r) ≤
          3 * epsilon / 2 := by
      nlinarith
    have hzero : Finset.Ico (0 + P) (0 + t) = Finset.Ico P t := by simp
    rw [hzero] at hraw
    exact hraw.trans ((Real.exp_le_exp.mpr hexponent).trans hexp_upper)
  have hratio_prefix (t : ℕ) (htQ : t ≤ Q) :
      (R t).1 / (R P).1 ≤ 19 / 16 := by
    by_cases hPt : P ≤ t
    · exact hratio_window t hPt htQ
    · have htP : t ≤ P := by omega
      have hRPpos : 0 < (R P).1 := (href' P).1
      have hratio_one : (R t).1 / (R P).1 ≤ 1 :=
        (div_le_one hRPpos).2 (hmono t P htP)
      norm_num at hratio_one ⊢
      linarith
  have hx0pos : 0 < x0 := by
    dsimp [x0]
    exact div_pos hA (mul_pos (by norm_num) (href' P).1)
  have hcenter_eq (t : ℕ) :
      x0 * (R t).1 = (A / 2) * ((R t).1 / (R P).1) := by
    dsimp [x0]
    field_simp [ne_of_gt (href' P).1]
  have hcenter_upper (t : ℕ) (htQ : t ≤ Q) :
      x0 * (R t).1 ≤ 19 * A / 32 := by
    rw [hcenter_eq]
    have hratio_nonneg : 0 ≤ (R t).1 / (R P).1 :=
      div_nonneg (href' t).1.le (href' P).1.le
    have hAhalf : 0 ≤ A / 2 := div_nonneg hA.le (by norm_num)
    have h := mul_le_mul_of_nonneg_left (hratio_prefix t htQ)
      hAhalf
    nlinarith
  have hcenter_lower (t : ℕ) (hPt : P ≤ t) :
      A / 2 ≤ x0 * (R t).1 := by
    rw [hcenter_eq]
    have hRPpos : 0 < (R P).1 := (href' P).1
    have hratio_one : 1 ≤ (R t).1 / (R P).1 :=
      (le_div_iff₀ hRPpos).2 (by
        simpa only [one_mul] using hmono P t hPt)
    exact (by nlinarith)
  have hfast_point (t : ℕ) (q : Fin n) :
      |(R t).2.1 q| ≤ (1 / 64) * (R t).1 := by
    have hsup : nodeSupNorm (R t).2.1 ≤ (1 / 64) * (R t).1 := by
      have hL1 : 0 ≤ nodeL1Norm (R t).2.2 :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith [(href' t).2.2.2]
    exact (abs_le_nodeSupNorm (R t).2.1 q).trans hsup
  have hmean_deviation (t : ℕ) :
      |mean t - x0 * (R t).1| ≤ (1 / 64) * (x0 * (R t).1) := by
    have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr N.hn
    have hsum_abs : |∑ q, (R t).2.1 q| ≤
        (n : ℝ) * nodeSupNorm (R t).2.1 := by
      calc
        |∑ q, (R t).2.1 q| ≤ ∑ q, |(R t).2.1 q| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = nodeL1Norm (R t).2.1 := rfl
        _ ≤ (n : ℝ) * nodeSupNorm (R t).2.1 :=
          nodeL1Norm_le_card_mul_nodeSupNorm _
    have havg_abs : |(n : ℝ)⁻¹ * ∑ q, (R t).2.1 q| ≤
        nodeSupNorm (R t).2.1 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hn)]
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using hsum_abs)
    have hsup : nodeSupNorm (R t).2.1 ≤ (1 / 64) * (R t).1 := by
      have hL1 : 0 ≤ nodeL1Norm (R t).2.2 :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith [(href' t).2.2.2]
    have hmean_id :
        mean t - x0 * (R t).1 =
          x0 * ((n : ℝ)⁻¹ * ∑ q, (R t).2.1 q) := by
      dsimp [mean, X]
      rw [Finset.mul_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_fin]
      rw [show Finset.univ.card = n by simp]
      rw [← Finset.mul_sum]
      field_simp [ne_of_gt hn]
      rw [Finset.mul_sum]
      ring
    rw [hmean_id, abs_mul, abs_of_pos hx0pos]
    calc
      x0 * |(n : ℝ)⁻¹ * ∑ q, (R t).2.1 q| ≤
          x0 * nodeSupNorm (R t).2.1 :=
        mul_le_mul_of_nonneg_left havg_abs hx0pos.le
      _ ≤ x0 * ((1 / 64) * (R t).1) :=
        mul_le_mul_of_nonneg_left hsup hx0pos.le
      _ = (1 / 64) * (x0 * (R t).1) := by ring
  constructor
  · intro t htQ q
    have htriangle := abs_add_le (x0 * (R t).1) (x0 * (R t).2.1 q)
    have hXid : X t q = x0 * (R t).1 + x0 * (R t).2.1 q := by
      dsimp [X]
      ring
    rw [← hXid] at htriangle
    have hcenter_nonneg : 0 ≤ x0 * (R t).1 :=
      mul_nonneg hx0pos.le (href' t).1.le
    have herror : |x0 * (R t).2.1 q| ≤
        (1 / 64) * (x0 * (R t).1) := by
      rw [abs_mul, abs_of_pos hx0pos]
      have := mul_le_mul_of_nonneg_left (hfast_point t q) hx0pos.le
      nlinarith
    rw [abs_of_nonneg hcenter_nonneg] at htriangle
    nlinarith [hcenter_upper t htQ]
  · intro t ht
    have hPt : P ≤ t := (Finset.mem_Ico.mp ht).1
    have htQ : t ≤ Q := (Finset.mem_Ico.mp ht).2.le
    have hdev := hmean_deviation t
    have hcenter_lo := hcenter_lower t hPt
    have hcenter_hi := hcenter_upper t htQ
    constructor
    · have hneg := neg_le_of_abs_le hdev
      nlinarith
    · have hpos := le_of_abs_le hdev
      nlinarith

/-- Reconstructing primal and retained-tracker coordinates from the unit-center
reference orbit gives the exact negative-quadratic Push--Pull recurrence. -/
theorem loading_scaled_reference_recurrence
    (N : NetworkSetup n) (s x0 : ℝ) :
    let R := loadingUnitCenterReferenceOrbit N s 0
    let X : ℕ → Fin n → ℝ := fun t q =>
      x0 * ((R t).1 + (R t).2.1 q)
    let U : ℕ → Fin n → ℝ := fun t q =>
      x0 * ((pushMass N t q - 1) * (R t).1 + (R t).2.2 q)
    ∀ t,
      X (t + 1) = (fun q =>
        (N.rowMix t *ᵥ X t) q + s * X t q + s * U t q) ∧
      U (t + 1) = (fun q =>
        (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q) := by
  let R := loadingUnitCenterReferenceOrbit N s 0
  let X : ℕ → Fin n → ℝ := fun t q =>
    x0 * ((R t).1 + (R t).2.1 q)
  let U : ℕ → Fin n → ℝ := fun t q =>
    x0 * ((pushMass N t q - 1) * (R t).1 + (R t).2.2 q)
  dsimp only
  intro t
  have hsucc := loadingUnitCenterReferenceOrbit_succ N s 0 t
  have ha := congrArg Prod.fst hsucc
  have hfast := congrArg Prod.snd hsucc
  have hrow_sum (q : Fin n) : ∑ r, N.rowMix t q r = 1 :=
    Matrix.sum_row_of_mem_rowStochastic (N.row_stochastic t) q
  constructor
  · funext q
    have hE := congrArg (fun z => z.1 q) hfast
    simp only [loadingPerturbedFastStep, loadingFastStep,
      loadingFastScale, loadingFastPerturbationInput,
      loadingFastCenterInput, Prod.fst_add, Pi.add_apply] at hE
    dsimp [R] at ha hE
    dsimp [X, U]
    rw [ha, hE]
    simp only [Matrix.smulVec, Matrix.mulVec, dotProduct]
    rw [show (∑ r, N.rowMix t q r *
          (x0 * ((R t).1 + (R t).2.1 r))) =
        x0 * (R t).1 + x0 *
          (∑ r, N.rowMix t q r * (R t).2.1 r) by
      calc
        (∑ r, N.rowMix t q r *
            (x0 * ((R t).1 + (R t).2.1 r))) =
            x0 * (R t).1 * (∑ r, N.rowMix t q r) +
              x0 * (∑ r, N.rowMix t q r * (R t).2.1 r) := by
                rw [Finset.mul_sum, Finset.mul_sum]
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro r _
                ring
        _ = _ := by rw [hrow_sum q]; ring]
    dsimp [R]
    ring
  · funext q
    have hK := congrArg (fun z => z.2 q) hfast
    simp only [loadingPerturbedFastStep, loadingFastStep,
      loadingFastScale, loadingFastPerturbationInput,
      loadingFastCenterInput, Prod.snd_add, Pi.add_apply] at hK
    dsimp [R] at ha hK
    dsimp [U, X]
    rw [ha, hK]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Matrix.smulVec, Matrix.mulVec, dotProduct]
    have hCU : (∑ r, N.colMix t q r *
          (x0 * ((pushMass N t r - 1) * (R t).1 + (R t).2.2 r))) =
        x0 * (((∑ r, N.colMix t q r * pushMass N t r) -
            ∑ r, N.colMix t q r) * (R t).1 +
          ∑ r, N.colMix t q r * (R t).2.2 r) := by
      calc
        (∑ r, N.colMix t q r *
            (x0 * ((pushMass N t r - 1) * (R t).1 + (R t).2.2 r))) =
            ∑ r, x0 * (N.colMix t q r *
              ((pushMass N t r - 1) * (R t).1 + (R t).2.2 r)) := by
                apply Finset.sum_congr rfl
                intro r _
                ring
        _ = x0 * ∑ r, N.colMix t q r *
              ((pushMass N t r - 1) * (R t).1 + (R t).2.2 r) := by
                rw [Finset.mul_sum]
        _ = x0 * (((∑ r, N.colMix t q r * pushMass N t r) -
              ∑ r, N.colMix t q r) * (R t).1 +
            ∑ r, N.colMix t q r * (R t).2.2 r) := by
          congr 1
          calc
        (∑ r, N.colMix t q r *
            ((pushMass N t r - 1) * (R t).1 + (R t).2.2 r)) =
            ∑ r, ((N.colMix t q r * pushMass N t r) * (R t).1 -
              N.colMix t q r * (R t).1 +
              N.colMix t q r * (R t).2.2 r) := by
                apply Finset.sum_congr rfl
                intro r _
                ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.sum_mul, ← Finset.sum_mul]
          ring
    have hdelta : (∑ r, (1 : NetworkMatrix n) q r) = 1 := by
      simp [Matrix.one_apply]
    have hIX : (∑ r, (N.colMix t - 1) q r *
          (x0 * ((R t).1 + (R t).2.1 r))) =
        x0 * (((∑ r, N.colMix t q r) - 1) * (R t).1 +
          ∑ r, (N.colMix t - 1) q r *
            (R t).2.1 r) := by
      calc
        (∑ r, (N.colMix t - 1) q r *
            (x0 * ((R t).1 + (R t).2.1 r))) =
            ∑ r, x0 * ((N.colMix t - 1) q r *
              ((R t).1 + (R t).2.1 r)) := by
                apply Finset.sum_congr rfl
                intro r _
                ring
        _ = x0 * ∑ r, (N.colMix t - 1) q r *
              ((R t).1 + (R t).2.1 r) := by
                rw [Finset.mul_sum]
        _ = x0 * (((∑ r, N.colMix t q r) - 1) * (R t).1 +
            ∑ r, (N.colMix t - 1) q r * (R t).2.1 r) := by
          congr 1
          calc
        (∑ r, (N.colMix t - 1) q r *
            ((R t).1 + (R t).2.1 r)) =
            (∑ r, (N.colMix t - 1) q r *
              (R t).1) +
            ∑ r, (N.colMix t - 1) q r *
              (R t).2.1 r := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro r _
                ring
        _ = _ := by
          rw [← Finset.sum_mul]
          simp only [Matrix.sub_apply]
          rw [Finset.sum_sub_distrib, hdelta]
    rw [hCU, hIX]
    dsimp [R]
    ring

/-- A deterministic coordinate of a genuine generated `Setup` trajectory is
the scaled reference orbit through the attaining window.  In particular, the
equation-(29) branch bound is proved before the derivative floor is used. -/
theorem deterministic_signal_true_trajectory_spec
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (N : NetworkSetup n) (S : Setup n d Ω) (ω : Ω) (k : Fin d)
    (L A s : ℝ) (P Q : ℕ)
    (hnetwork : S.network = N) (hL : 0 < L) (hA : 0 < A) (hs : 0 < s)
    (hPQ : P ≤ Q)
    (hbudget : s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon)
    (href :
      let R := loadingUnitCenterReferenceOrbit N s 0
      ∀ m,
        0 < (R m).1 ∧
        1 + s * gain N m / 2 ≤ (R (m + 1)).1 / (R m).1 ∧
        (R (m + 1)).1 / (R m).1 ≤
          1 + 3 * s * gain N m / 2 ∧
        nodeSupNorm (R m).2.1 + nodeL1Norm (R m).2.2 ≤
          (1 / 64) * (R m).1)
    (hgradient : ∀ i z,
      (gradient (S.localObjective i) z) k =
        deterministicGapDerivative L A (z k))
    (hnoise : ∀ t i, (S.noise t ω i) k = 0) :
    let R := loadingUnitCenterReferenceOrbit N s 0
    let x0 := A / (2 * (R P).1)
    let X : ℕ → Fin n → ℝ := fun t q => x0 * ((R t).1 + (R t).2.1 q)
    let mean : ℕ → ℝ := fun t => (n : ℝ)⁻¹ * ∑ q, X t q
    S.initialPoint k = x0 →
      (∀ t, t ≤ Q → ∀ q, (primal S ω (s / L) t q) k = X t q) ∧
      ∀ t ∈ Finset.Ico P Q,
        7 * L * A / 16 ≤
          |deterministicGapDerivative L A
            ((arithmeticMean S ω (s / L) t) k)| := by
  let R := loadingUnitCenterReferenceOrbit N s 0
  let x0 := A / (2 * (R P).1)
  let X : ℕ → Fin n → ℝ := fun t q => x0 * ((R t).1 + (R t).2.1 q)
  let U : ℕ → Fin n → ℝ := fun t q =>
    x0 * ((pushMass N t q - 1) * (R t).1 + (R t).2.2 q)
  let Y : ℕ → Fin n → ℝ := fun t q => -L * (X t q + U t q)
  let Xactual : ℕ → Fin n → ℝ := fun t q => (primal S ω (s / L) t q) k
  let Yactual : ℕ → Fin n → ℝ := fun t q => (tracker S ω (s / L) t q) k
  let mean : ℕ → ℝ := fun t => (n : ℝ)⁻¹ * ∑ q, X t q
  dsimp only
  intro hinitial
  have hbounds := deterministic_signal_reference_window_bounds
    N s A P Q hs hA hPQ hbudget href
  have hrefrec := loading_scaled_reference_recurrence N s x0
  have heval_sum (Z : Fin n → Point d) :
      (∑ r, Z r) k = ∑ r, (Z r) k := by
    let p := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) k
    change p (∑ r, Z r) = ∑ r, p (Z r)
    exact map_sum p Z Finset.univ
  have hmul_eval (B : NetworkMatrix n) (Z : Fin n → Point d) (q : Fin n) :
      (leftAct B Z q) k = ∑ r, B q r * (Z r) k := by
    unfold leftAct
    rw [Matrix.smulVec_apply, heval_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [PiLp.smul_apply, smul_eq_mul]
  have htrajectory : ∀ t, t ≤ Q → Xactual t = X t ∧ Yactual t = Y t := by
    intro t
    induction t with
    | zero =>
      intro _htQ
      constructor
      · funext q
        change S.initialPoint k = X 0 q
        simpa [X, R, x0] using hinitial
      · funext q
        have hx0bound : |x0| ≤ A := by
          simpa [X, R] using hbounds.1 0 (Nat.zero_le Q) q
        have hderiv : deterministicGapDerivative L A x0 = -L * x0 :=
          deterministicGapDerivative_eq_neg_mul_of_abs_le L A x0 hx0bound
        have hg := sampledOracle_eq_gradient_add_noise S ω (s / L) 0 q
        have hgk := congrArg (fun z : Point d => z k) hg
        have hgk' : (sampledOracle S ω (s / L) 0 q) k =
            (gradient (S.localObjective q) (primal S ω (s / L) 0 q)) k +
              (S.noise 0 ω q) k := by
          simpa only [PiLp.add_apply] using hgk
        rw [hgradient q, hnoise 0 q] at hgk'
        simp only [primal_zero, hinitial] at hgk'
        rw [hderiv] at hgk'
        change (tracker S ω (s / L) 0 q) k = Y 0 q
        rw [congrFun (tracker_zero S ω (s / L)) q, hgk']
        simp [Y, X, U, R]
    | succ t ih =>
        intro htQ
        have htQ' : t ≤ Q := Nat.le_of_succ_le htQ
        have ih' := ih htQ'
        have hXref := (hrefrec t).1
        have hUref := (hrefrec t).2
        have hroweq : S.rowMix t = N.rowMix t := by
          exact congrArg (fun M : NetworkSetup n => M.rowMix t) hnetwork
        have hcoleq : S.colMix t = N.colMix t := by
          exact congrArg (fun M : NetworkSetup n => M.colMix t) hnetwork
        have hXnext : Xactual (t + 1) = X (t + 1) := by
          funext q
          have hiX := congrFun ih'.1
          have hiY := congrFun ih'.2
          have hrefq := congrFun hXref q
          have hp' : Xactual (t + 1) q =
              (∑ r, S.rowMix t q r * Xactual t r) -
                (s / L) * Yactual t q := by
            change (primal S ω (s / L) (t + 1) q) k = _
            rw [congrFun (primal_succ S ω (s / L) t) q]
            simp only [Pi.sub_apply, PiLp.sub_apply, Pi.smul_apply,
              PiLp.smul_apply, smul_eq_mul, hmul_eval]
            rfl
          simp_rw [hiX, hiY] at hp'
          dsimp [Y] at hp'
          have hLne : L ≠ 0 := ne_of_gt hL
          field_simp [hLne] at hp'
          rw [hroweq] at hp'
          have hrefq' : X (t + 1) q =
              (N.rowMix t *ᵥ X t) q + s * X t q + s * U t q := by
            change X (t + 1) q =
              (N.rowMix t *ᵥ X t) q + s * X t q + s * U t q at hrefq
            exact hrefq
          simp only [Matrix.smulVec, Matrix.mulVec, dotProduct] at hrefq'
          nlinarith [hp', hrefq']
        have hGcurrent (q : Fin n) :
            (sampledOracle S ω (s / L) t q) k = -L * Xactual t q := by
          have hg := sampledOracle_eq_gradient_add_noise S ω (s / L) t q
          have hgk := congrArg (fun z : Point d => z k) hg
          have hgk' : (sampledOracle S ω (s / L) t q) k =
              (gradient (S.localObjective q) (primal S ω (s / L) t q)) k +
                (S.noise t ω q) k := by
            simpa only [PiLp.add_apply] using hgk
          have hbranch : |Xactual t q| ≤ A := by
            rw [congrFun ih'.1 q]
            exact hbounds.1 t htQ' q
          rw [hgradient q, hnoise t q,
            deterministicGapDerivative_eq_neg_mul_of_abs_le
              L A (Xactual t q) hbranch] at hgk'
          simpa [Xactual] using hgk'
        have hGnext (q : Fin n) :
            (sampledOracle S ω (s / L) (t + 1) q) k =
              -L * Xactual (t + 1) q := by
          have hg := sampledOracle_eq_gradient_add_noise S ω (s / L) (t + 1) q
          have hgk := congrArg (fun z : Point d => z k) hg
          have hgk' : (sampledOracle S ω (s / L) (t + 1) q) k =
              (gradient (S.localObjective q)
                (primal S ω (s / L) (t + 1) q)) k +
                (S.noise (t + 1) ω q) k := by
            simpa only [PiLp.add_apply] using hgk
          have hbranch : |Xactual (t + 1) q| ≤ A := by
            rw [congrFun hXnext q]
            exact hbounds.1 (t + 1) htQ q
          rw [hgradient q, hnoise (t + 1) q,
            deterministicGapDerivative_eq_neg_mul_of_abs_le
              L A (Xactual (t + 1) q) hbranch] at hgk'
          simpa [Xactual] using hgk'
        have hYnext : Yactual (t + 1) = Y (t + 1) := by
          funext q
          have hiX := congrFun ih'.1
          have hiY := congrFun ih'.2
          have hXn := congrFun hXnext
          have hUn := congrFun hUref
          have hy' : Yactual (t + 1) q =
              (∑ r, S.colMix t q r * Yactual t r) +
                (sampledOracle S ω (s / L) (t + 1) q) k -
                (sampledOracle S ω (s / L) t q) k := by
            change (tracker S ω (s / L) (t + 1) q) k = _
            rw [congrFun (tracker_succ S ω (s / L) t) q]
            simp only [Pi.add_apply, Pi.sub_apply, PiLp.add_apply,
              PiLp.sub_apply, hmul_eval]
            rfl
          simp_rw [hiY] at hy'
          rw [hGnext q, hGcurrent q] at hy'
          dsimp [Y] at hy' ⊢
          have hUn' : U (t + 1) q =
              (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q := by
            have hUnq := hUn q
            change U (t + 1) q =
              (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q at hUnq
            exact hUnq
          rw [show (∑ r, S.colMix t q r *
                (-L * (X t r + U t r))) =
              -L * ((S.colMix t *ᵥ X t) q +
                (S.colMix t *ᵥ U t) q) by
            simp only [Matrix.smulVec, Matrix.mulVec]
            calc
              ∑ r, S.colMix t q r * (-L * (X t r + U t r)) =
                  ∑ r, -L * (S.colMix t q r * X t r +
                    S.colMix t q r * U t r) := by
                    apply Finset.sum_congr rfl
                    intro r _
                    ring
              _ = -L * ∑ r, (S.colMix t q r * X t r +
                    S.colMix t q r * U t r) := by
                    rw [Finset.mul_sum]
              _ = -L * ((∑ r, S.colMix t q r * X t r) +
                    ∑ r, S.colMix t q r * U t r) := by
                    rw [Finset.sum_add_distrib]] at hy'
          rw [hcoleq] at hy'
          simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at hUn'
          rw [hXn q, hiX q] at hy'
          nlinarith [hy', hXn q]
        exact ⟨hXnext, hYnext⟩
  constructor
  · intro t htQ q
    exact congrFun (htrajectory t htQ).1 q
  · intro t ht
    have htQ : t ≤ Q := (Finset.mem_Ico.mp ht).2.le
    have hmean_eq : (arithmeticMean S ω (s / L) t) k = mean t := by
      unfold arithmeticMean
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [heval_sum]
      dsimp [mean]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      exact congrFun (htrajectory t htQ).1 q
    have hmean := hbounds.2 t ht
    rw [hmean_eq,
      deterministicGapDerivative_eq_neg_mul_of_abs_le L A (mean t) (by
        rw [abs_of_nonneg]
        · exact hmean.2
        · nlinarith [hmean.1])]
    rw [abs_mul, abs_neg, abs_of_pos hL, abs_of_nonneg (by nlinarith [hmean.1])]
    nlinarith [hmean.1]

/-- The scalar finite-sum step in source equation (30).  The remaining
dynamical task is to supply the pointwise `7LA/16` floor from the calibrated
unit-center trajectory. -/
theorem deterministic_gap_window_sum_lower
    (L Δ A : ℝ) (P Q : ℕ) (mean : ℕ → ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hA : 0 ≤ A)
    (hPQ : P ≤ Q)
    (hA_sq : A ^ 2 = Δ / (2 * L))
    (hpoint : ∀ t ∈ Finset.Ico P Q,
      7 * L * A / 16 ≤ |deterministicGapDerivative L A (mean t)|) :
    L * Δ / 16 * (Q - P) ≤
      ∑ t ∈ Finset.Ico P Q,
        deterministicGapDerivative L A (mean t) ^ 2 := by
  have hApos : 0 < A := by
    have hratio : 0 < Δ / (2 * L) := div_pos hΔ (mul_pos (by norm_num) hL)
    nlinarith [hA_sq]
  have hterm (t : ℕ) (ht : t ∈ Finset.Ico P Q) :
      L * Δ / 16 ≤ deterministicGapDerivative L A (mean t) ^ 2 := by
    have hfloor_nonneg : 0 ≤ 7 * L * A / 16 := by positivity
    have hsquare : (7 * L * A / 16) ^ 2 ≤
        |deterministicGapDerivative L A (mean t)| ^ 2 :=
      (sq_le_sq₀ hfloor_nonneg (abs_nonneg _)).2 (hpoint t ht)
    rw [sq_abs] at hsquare
    have hDelta : A ^ 2 * (2 * L) = Δ :=
      (eq_div_iff (mul_ne_zero (by norm_num) hL.ne')).mp hA_sq
    nlinarith [hsquare, sq_nonneg (L * A)]
  calc
    L * Δ / 16 * (Q - P) =
        ∑ _t ∈ Finset.Ico P Q, L * Δ / 16 := by
      simp [Nat.cast_sub hPQ]
      ring
    _ ≤ ∑ t ∈ Finset.Ico P Q,
        deterministicGapDerivative L A (mean t) ^ 2 := by
      exact Finset.sum_le_sum fun t ht => hterm t ht

/-- A scalar coordinate objective lifts to the finite Euclidean product with
its gradient supported on exactly that coordinate. -/
theorem hasGradientAt_pointCoordinate
    {d : ℕ} (f : ℝ → ℝ) (x : Point d) (k : Fin d) (g : ℝ)
    (hf : HasDerivAt f g (x k)) :
    HasGradientAt (fun z : Point d => f (z k))
      (PiLp.single 2 k g) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcomp := hf.hasFDerivAt.comp x
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) k).hasFDerivAt
  convert hcomp using 1
  ext z
  simp only [InnerProductSpace.toDual_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    PiLp.proj_apply, one_smul]
  rw [real_inner_comm, ← SOptLib.piLp_inner_coord_single]
  change g * z k = z k * g
  ring

/-- Gradients of finitely many scalar coordinate objectives assemble into the
corresponding Euclidean product vector. -/
theorem hasGradientAt_separablePoint
    {d : ℕ} (f g : Fin d → ℝ → ℝ) (x : Point d)
    (hf : ∀ k, HasDerivAt (f k) (g k (x k)) (x k)) :
    HasGradientAt (fun z : Point d => ∑ k, f k (z k))
      (WithLp.toLp 2 (fun k => g k (x k))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsum := HasFDerivAt.fun_sum (x := x) (u := Finset.univ)
    (fun k _hk =>
      (hasGradientAt_pointCoordinate (f k) x k (g k (x k))
        (hf k)).hasFDerivAt)
  convert hsum using 1
  rw [← map_sum]
  congr 1
  exact (SOptLib.finset_sum_piLp_single_apply_self
    (p := 2) (v := WithLp.toLp 2 (fun k => g k (x k)))).symm

/-- Coordinatewise scalar objectives with a common derivative Lipschitz bound
form an objective with that same (maximum, not summed) smoothness constant on
the Euclidean product. -/
theorem separablePoint_local_smooth
    {d : ℕ} (f g : Fin d → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hderiv : ∀ k z, HasDerivAt (f k) (g k z) z)
    (hlip : ∀ k x y, ‖g k x - g k y‖ ≤ L * ‖x - y‖) :
    Differentiable ℝ (fun z : Point d => ∑ k, f k (z k)) ∧
      LipschitzWith ⟨L, hL⟩
        (gradient (fun z : Point d => ∑ k, f k (z k))) := by
  let F : Point d → ℝ := fun z => ∑ k, f k (z k)
  let G : Point d → Point d := fun z =>
    WithLp.toLp 2 (fun k => g k (z k))
  have hFG (z : Point d) : HasGradientAt F (G z) z := by
    simpa [F, G] using hasGradientAt_separablePoint f g z (hderiv · _)
  constructor
  · intro z
    exact (hFG z).differentiableAt
  · have hgradient : gradient F = G := funext fun z => (hFG z).gradient
    rw [show (fun z : Point d => ∑ k, f k (z k)) = F from rfl,
      hgradient]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hL (norm_nonneg (x - y)))).1
    have henergy :=
      SOptLib.dependent_product_norm_sq_map_sub_le_of_pointwise_lipschitz
        g L (fun k => x k) (fun k => y k) hL (fun k => hlip k (x k) (y k))
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [G, PiLp.sub_apply, PiLp.toLp_apply]
    calc
      (∑ k, ‖g k (x k) - g k (y k)‖ ^ 2) ≤
          L ^ 2 * ∑ k, ‖x k - y k‖ ^ 2 := henergy
      _ = (L * ‖x - y‖) ^ 2 := by
        rw [mul_pow, PiLp.norm_sq_eq_of_L2]
        simp only [PiLp.sub_apply]

/-- A finite family of storage coordinates is a legal common objective with
the same smoothness constant `L`. -/
theorem storageSeparable_local_smooth
    {d : ℕ} (L : ℝ) (D : Fin d → ℝ) (hL : 0 < L)
    (hD : ∀ k, 0 < D k) :
    Differentiable ℝ
        (fun z : Point d => ∑ k, negativeCurvaturePotential L (D k) (z k)) ∧
      LipschitzWith ⟨L, hL.le⟩
        (gradient
          (fun z : Point d => ∑ k, negativeCurvaturePotential L (D k) (z k))) := by
  apply separablePoint_local_smooth
    (fun k => negativeCurvaturePotential L (D k))
    (fun k => negativeCurvatureDerivative L (D k)) L hL.le
  · intro k z
    have hspec := negativeCurvaturePotential_setup_spec L (D k) hL (hD k)
    simpa using (hspec.1 z).hasDerivAt
  · intro k x y
    exact negativeCurvatureDerivative_norm_sub_le L (D k) x y hL.le (hD k).le

theorem storageSeparable_nonneg
    {d : ℕ} (L : ℝ) (D : Fin d → ℝ) (hL : 0 ≤ L)
    (hD : ∀ k, 0 < D k) (x : Point d) :
    0 ≤ ∑ k, negativeCurvaturePotential L (D k) (x k) := by
  exact Finset.sum_nonneg fun k _hk =>
    negativeCurvaturePotential_nonneg L (D k) (x k) hL (hD k)

theorem storageSeparable_sInf
    {d : ℕ} (L : ℝ) (D : Fin d → ℝ) (hL : 0 ≤ L)
    (hD : ∀ k, 0 < D k) :
    sInf (Set.range
      (fun x : Point d => ∑ k, negativeCurvaturePotential L (D k) (x k))) = 0 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · refine ⟨0, ⟨0, ?_⟩⟩
    simp [negativeCurvaturePotential]
  · rintro _ ⟨x, rfl⟩
    exact storageSeparable_nonneg L D hL hD x
  · intro w hw
    refine ⟨0, ⟨0, ?_⟩, hw⟩
    simp [negativeCurvaturePotential]

/-- Independent time-node row samples remain conditionally independent after
applying deterministic, time- and node-dependent measurable transforms.  This
is the probability-space bridge needed by the equation-(41) storage noise:
the generated history may forget raw samples, so it is first refined to the
strict raw-coordinate prefix before current-node event factorization. -/
theorem iidMiniBatchSampleLaw_nodeConditionallyIndependent
    {A : Type*} [MeasurableSpace A]
    (n d : ℕ) (mu : Measure A) [IsProbabilityMeasure mu]
    (phi : ℕ → Fin n → A → Point d)
    (hphi : ∀ t i, Measurable (phi t i)) :
    ∀ t,
      @NodeConditionallyIndependent (Fin n) (Point d)
        (SOptLib.miniBatchSamplePath n A) _ _ _ _
        (SOptLib.iidMiniBatchSampleLaw n mu)
        (preSamplingHistoryOf
          (fun k omega i => phi k i (omega k i)) t)
        (fun i omega => phi t i (omega t i)) := by
  classical
  let Omega := SOptLib.miniBatchSamplePath n A
  let mOmega : MeasurableSpace Omega := inferInstance
  let P : Measure Omega := SOptLib.iidMiniBatchSampleLaw n mu
  let xi : (ℕ × Fin n) → Omega → A := fun q omega => omega q.1 q.2
  let noise : ℕ → Omega → Fin n → Point d :=
    fun k omega i => phi k i (omega k i)
  have hxi_meas : ∀ q, Measurable (xi q) := by
    intro q
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hxi_indep : ProbabilityTheory.iIndepFun xi P := by
    simpa [P, xi, Omega] using
      (SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval n mu)
  have hnoise_meas : ∀ k, Measurable (noise k) := by
    intro k
    refine measurable_pi_lambda _ ?_
    intro i
    exact (hphi k i).comp
      ((measurable_pi_apply i).comp (measurable_pi_apply k))
  intro t
  let past : Set (ℕ × Fin n) := {q | q.1 < t}
  let current : Set (ℕ × Fin n) := {q | q.1 = t}
  let mPast : MeasurableSpace Omega := preSamplingHistoryOf noise t
  let mCurrent : MeasurableSpace Omega :=
    ⨆ q ∈ current,
      MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A)
  have hmPast_le : mPast ≤ mOmega := by
    unfold mPast preSamplingHistoryOf
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact (hnoise_meas j).comap_le
  have hmCurrent_le : mCurrent ≤ mOmega := by
    unfold mCurrent
    refine iSup_le fun q => iSup_le fun _hq => ?_
    exact (hxi_meas q).comap_le
  have hmPast_raw :
      mPast ≤
        ⨆ q ∈ past,
          MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A) := by
    calc
      mPast ≤
          ⨆ q ∈ past,
            MeasurableSpace.comap
              (fun omega : Omega => noise q.1 omega q.2)
                (inferInstance : MeasurableSpace (Point d)) := by
        simpa [mPast, past] using
          (pi_prefixMeasurableSpace_le_timeCoordinate_iSup noise t)
      _ ≤ ⨆ q ∈ past,
          MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A) := by
        refine iSup_mono fun q => iSup_mono' fun hq => ⟨hq, ?_⟩
        change MeasurableSpace.comap (fun omega => phi q.1 q.2 (xi q omega))
            (inferInstance : MeasurableSpace (Point d)) ≤
          MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A)
        exact ((hphi q.1 q.2).comp
          (Measurable.of_comap_le le_rfl)).comap_le
  have hpast_current : Disjoint past current := by
    rw [Set.disjoint_left]
    intro q hqPast hqCurrent
    exact (Nat.ne_of_lt hqPast) hqCurrent
  have hPastCurrent : ProbabilityTheory.Indep mPast mCurrent P := by
    have hraw : ProbabilityTheory.Indep
        (⨆ q ∈ past,
          MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A))
        (⨆ q ∈ current,
          MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A)) P := by
      apply ProbabilityTheory.indep_iSup_of_disjoint
        (m := fun q => MeasurableSpace.comap (xi q)
          (inferInstance : MeasurableSpace A))
      · exact fun q => (hxi_meas q).comap_le
      · simpa using hxi_indep.iIndep
      · exact hpast_current
    exact ProbabilityTheory.indep_of_indep_of_le_left hraw hmPast_raw
  have hcurrent_raw (i : Fin n) :
      Measurable[mCurrent] (fun omega : Omega => omega t i) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le (t, i) (le_iSup_of_le (by simp [current]) le_rfl)
  have hcurrent_noise (i : Fin n) :
      Measurable[mCurrent] (fun omega : Omega => noise t omega i) := by
    exact (hphi t i).comp (hcurrent_raw i)
  have hcurrent_indep :
      ProbabilityTheory.iIndepFun
        (fun (i : Fin n) (omega : Omega) => noise t omega i) P := by
    have hraw := hxi_indep.precomp
      (g := fun i : Fin n => (t, i)) (fun _ _ h => congrArg Prod.snd h)
    simpa [noise, xi] using
      hraw.comp (fun i => phi t i) (fun i => hphi t i)
  intro s events hevents
  let hit : Fin n → Set Omega :=
    fun i => (fun omega => noise t omega i) ⁻¹' events i
  have hhit_current : ∀ i ∈ s, @MeasurableSet Omega mCurrent (hit i) := by
    intro i hi
    exact (hcurrent_noise i) (hevents i hi)
  have hhit_ambient : ∀ i ∈ s, @MeasurableSet Omega mOmega (hit i) := by
    intro i hi
    exact hmCurrent_le (hit i) (hhit_current i hi)
  let joint : Set Omega := ⋂ i ∈ s, hit i
  have hjoint_current : @MeasurableSet Omega mCurrent joint := by
    exact s.measurableSet_biInter fun i hi => hhit_current i hi
  have hjoint_ambient : @MeasurableSet Omega mOmega joint :=
    hmCurrent_le joint hjoint_current
  letI : @SigmaFinite Omega mPast (P.trim hmPast_le) := by infer_instance
  have hcoord_wd : ∀ i ∈ s,
      @SOptLib.ConditionalExpectation.conditionalExpectationWellDefined
        Omega ℝ mOmega _ P mPast
        ((hit i).indicator fun _ => (1 : ℝ)) := by
    intro i hi
    exact ⟨hmPast_le, inferInstance,
      (integrable_const (1 : ℝ)).indicator (hhit_ambient i hi)⟩
  refine ⟨hcoord_wd, ?_⟩
  have hcoord_ce : ∀ i ∈ s,
      P[(hit i).indicator (fun _ => (1 : ℝ)) | mPast] =ᵐ[P]
        fun _ => P.real (hit i) := by
    intro i hi
    exact condExp_indicator_eq_const_of_indep
      (mΩ := mOmega) (μ := P) (m := mPast) (mfresh := mCurrent)
      (hit := hit i) (p := P.real (hit i))
      hmCurrent_le hmPast_le (hhit_current i hi) hPastCurrent rfl
  have hjoint_ce :
      P[joint.indicator (fun _ => (1 : ℝ)) | mPast] =ᵐ[P]
        fun _ => P.real joint := by
    exact condExp_indicator_eq_const_of_indep
      (mΩ := mOmega) (μ := P) (m := mPast) (mfresh := mCurrent)
      (hit := joint) (p := P.real joint)
      hmCurrent_le hmPast_le hjoint_current hPastCurrent rfl
  have hjoint_prob : P.real joint = ∏ i ∈ s, P.real (hit i) := by
    have hmeasure := hcurrent_indep.measure_inter_preimage_eq_mul s hevents
    have hmeasure' : P joint = ∏ i ∈ s, P (hit i) := by
      simpa [joint, hit] using hmeasure
    simp only [Measure.real, hmeasure', ENNReal.toReal_prod]
  have prod_ae_of_ae
      (u v : Fin n → Omega → ℝ) (r : Finset (Fin n))
      (h : ∀ i ∈ r, u i =ᵐ[P] v i) :
      (fun omega => ∏ i ∈ r, u i omega) =ᵐ[P]
        fun omega => ∏ i ∈ r, v i omega := by
    induction r using Finset.induction_on with
    | empty => simp
    | @insert i r hi ih =>
        simpa [Finset.prod_insert, hi] using
          (h i (Finset.mem_insert_self i r)).mul
            (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
  have hprod_ce :
      (fun omega => ∏ i ∈ s,
        P[(hit i).indicator (fun _ => (1 : ℝ)) | mPast] omega) =ᵐ[P]
      fun _ => ∏ i ∈ s, P.real (hit i) := by
    exact prod_ae_of_ae
      (fun i omega =>
        P[(hit i).indicator (fun _ => (1 : ℝ)) | mPast] omega)
      (fun i _ => P.real (hit i)) s hcoord_ce
  refine ⟨?_, ?_⟩
  · refine ⟨hmPast_le, inferInstance, ?_⟩
    have hindicator :
        (fun omega => ∏ i ∈ s,
          (hit i).indicator (fun _ => (1 : ℝ)) omega) =
          joint.indicator (fun _ => (1 : ℝ)) := by
      funext omega
      rw [prod_indicator_const_apply]
      change joint.indicator ((fun _ : Omega => (1 : ℝ)) ^ s.card) omega =
        joint.indicator (fun _ => (1 : ℝ)) omega
      by_cases homega : omega ∈ joint
      · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega]
        simp [Pi.pow_apply]
      · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
    change Integrable
      (fun omega => ∏ i ∈ s,
        (hit i).indicator (fun _ => (1 : ℝ)) omega) P
    rw [hindicator]
    exact (integrable_const (1 : ℝ)).indicator hjoint_ambient
  · have hjoint_indicator :
        (fun omega => ∏ i ∈ s,
          (hit i).indicator (fun _ => (1 : ℝ)) omega) =
          joint.indicator (fun _ => (1 : ℝ)) := by
      funext omega
      rw [prod_indicator_const_apply]
      change joint.indicator ((fun _ : Omega => (1 : ℝ)) ^ s.card) omega =
        joint.indicator (fun _ => (1 : ℝ)) omega
      by_cases homega : omega ∈ joint
      · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega]
        simp [Pi.pow_apply]
      · rw [Set.indicator_of_notMem homega, Set.indicator_of_notMem homega]
    change P[(fun omega => ∏ i ∈ s,
        (hit i).indicator (fun _ => (1 : ℝ)) omega) | mPast] =ᵐ[P]
      fun omega => ∏ i ∈ s,
        P[(hit i).indicator (fun _ => (1 : ℝ)) | mPast] omega
    rw [hjoint_indicator]
    have hconst : (fun _ : Omega => P.real joint) =ᵐ[P]
        fun _ => ∏ i ∈ s, P.real (hit i) :=
      Filter.Eventually.of_forall (fun _ => hjoint_prob)
    exact hjoint_ce.trans (hconst.trans hprod_ce.symm)

/-- Fixed-row centering and second-moment estimates lift to the exact
strict-history stochastic contracts for the transformed iid time-node table. -/
theorem iidMiniBatchSampleLaw_centered_secondMoment
    {A : Type*} [MeasurableSpace A]
    (n d : ℕ) (mu : Measure A) [IsProbabilityMeasure mu]
    (phi : ℕ → Fin n → A → Point d)
    (hphi : ∀ t i, Measurable (phi t i))
    (sigma : ℝ)
    (hphi_int : ∀ t i, Integrable (phi t i) mu)
    (hcenter : ∀ t i, ∫ a, phi t i a ∂mu = 0)
    (hsq_int : ∀ t i, Integrable (fun a => ‖phi t i a‖ ^ 2) mu)
    (hsq_le : ∀ t i, ∫ a, ‖phi t i a‖ ^ 2 ∂mu ≤ sigma ^ 2) :
    (∀ t i,
      SOptLib.ConditionalExpectation.conditionalExpectationEq
        (SOptLib.iidMiniBatchSampleLaw n mu)
        (preSamplingHistoryOf (fun k omega j => phi k j (omega k j)) t)
        (fun omega => phi t i (omega t i)) (fun _ => 0)) ∧
    (∀ t i,
      ConditionalSecondMomentBound
        (SOptLib.iidMiniBatchSampleLaw n mu)
        (preSamplingHistoryOf (fun k omega j => phi k j (omega k j)) t)
        (fun omega => phi t i (omega t i)) (sigma ^ 2)) := by
  classical
  let Omega := SOptLib.miniBatchSamplePath n A
  let mOmega : MeasurableSpace Omega := inferInstance
  let P : Measure Omega := SOptLib.iidMiniBatchSampleLaw n mu
  let xi : (ℕ × Fin n) → Omega → A := fun q omega => omega q.1 q.2
  let noise : ℕ → Omega → Fin n → Point d :=
    fun k omega i => phi k i (omega k i)
  have hxi_meas : ∀ q, Measurable (xi q) := by
    intro q
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hxi_indep : ProbabilityTheory.iIndepFun xi P := by
    simpa [P, xi, Omega] using
      (SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval n mu)
  have hnoise_meas : ∀ k, Measurable (noise k) := by
    intro k
    refine measurable_pi_lambda _ ?_
    intro i
    exact (hphi k i).comp
      ((measurable_pi_apply i).comp (measurable_pi_apply k))
  have one_coordinate (t : ℕ) (i : Fin n) :
      SOptLib.ConditionalExpectation.conditionalExpectationEq P
          (preSamplingHistoryOf noise t)
          (fun omega => noise t omega i) (fun _ => 0) ∧
        ConditionalSecondMomentBound P (preSamplingHistoryOf noise t)
          (fun omega => noise t omega i) (sigma ^ 2) := by
    let mPast : MeasurableSpace Omega := preSamplingHistoryOf noise t
    let past : Set (ℕ × Fin n) := {q | q.1 < t}
    let current : ℕ × Fin n := (t, i)
    have hmPast_le : mPast ≤ mOmega := by
      unfold mPast preSamplingHistoryOf
      refine iSup_le fun j => iSup_le fun hj => ?_
      exact (hnoise_meas j).comap_le
    have hmPast_raw :
        mPast ≤ ⨆ q ∈ past,
          MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A) := by
      calc
        mPast ≤ ⨆ q ∈ past,
            MeasurableSpace.comap
              (fun omega : Omega => noise q.1 omega q.2)
                (inferInstance : MeasurableSpace (Point d)) := by
          simpa [mPast, past] using
            (pi_prefixMeasurableSpace_le_timeCoordinate_iSup noise t)
        _ ≤ ⨆ q ∈ past,
            MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A) := by
          refine iSup_mono fun q => iSup_mono' fun hq => ⟨hq, ?_⟩
          change MeasurableSpace.comap (fun omega => phi q.1 q.2 (xi q omega))
              (inferInstance : MeasurableSpace (Point d)) ≤
            MeasurableSpace.comap (xi q) (inferInstance : MeasurableSpace A)
          exact ((hphi q.1 q.2).comp
            (Measurable.of_comap_le le_rfl)).comap_le
    have hpast_disj : Disjoint past ({current} : Set (ℕ × Fin n)) := by
      rw [Set.disjoint_singleton_right]
      simp [past, current]
    have hPastFresh : ProbabilityTheory.Indep mPast
        (MeasurableSpace.comap (xi current)
          (inferInstance : MeasurableSpace A)) P :=
      SOptLib.iIndepFun_indep_strictPast_singleton
        (mOmega := mOmega) (mSample := inferInstance)
        (xi := xi) (mu := P) (hxi_meas := hxi_meas)
        (hxi_iIndep := hxi_indep) (strictPast := mPast)
        (pastSet := past) (current := current) hpast_disj hmPast_raw
    letI : @SigmaFinite Omega mPast (P.trim hmPast_le) := by infer_instance
    have hmap : @Measure.map Omega A mOmega _ (xi current) P = mu := by
      simpa [P, xi, current, Omega] using
        (SOptLib.iidMiniBatchSampleLaw_map_eval n mu t i)
    have hraw_meas : @Measurable Omega A mOmega _ (xi current) :=
      hxi_meas current
    have hnoise_int : Integrable (fun omega => noise t omega i) P := by
      have hmapped : Integrable (phi t i)
          (@Measure.map Omega A mOmega _ (xi current) P) := by
        rw [hmap]
        exact hphi_int t i
      simpa [noise, xi, current, Function.comp_def] using
        hmapped.comp_measurable hraw_meas
    have hnoise_integral : ∫ omega, noise t omega i ∂P = 0 := by
      calc
        ∫ omega, noise t omega i ∂P = ∫ a, phi t i a ∂mu := by
          simpa [noise, xi, current, Function.comp_def] using
            (@integral_comp_eq_integral_of_map_eq
              Omega A (Point d) mOmega _ _ _ P (xi current) mu (phi t i)
              hraw_meas.aemeasurable
              (by simpa [hmap] using (hphi t i).aestronglyMeasurable)
              hmap)
        _ = 0 := hcenter t i
    have hfresh_le : MeasurableSpace.comap (xi current)
        (inferInstance : MeasurableSpace A) ≤ mOmega := hraw_meas.comap_le
    have hnoise_strong : StronglyMeasurable[
        MeasurableSpace.comap (xi current) (inferInstance : MeasurableSpace A)]
        (fun omega => noise t omega i) := by
      exact ((hphi t i).comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    have hcenter_ce : P[(fun omega => noise t omega i) | mPast] =ᵐ[P]
        fun _ => (0 : Point d) := by
      have hce := MeasureTheory.condExp_indep_eq
        hfresh_le hmPast_le hnoise_strong hPastFresh.symm
      exact hce.trans (Filter.Eventually.of_forall fun _ => hnoise_integral)
    have hcentered :
        @SOptLib.ConditionalExpectation.conditionalExpectationEq
          Omega (Point d) mOmega _ _ _ P mPast
          (fun omega => noise t omega i) (fun _ => 0) :=
      ⟨⟨hmPast_le, inferInstance, hnoise_int⟩, hcenter_ce⟩
    let sq : Omega → ℝ := fun omega => ‖noise t omega i‖ ^ 2
    have hsq_meas_fresh : StronglyMeasurable[
        MeasurableSpace.comap (xi current) (inferInstance : MeasurableSpace A)] sq := by
      exact hnoise_strong.norm.pow 2
    have hsq_integrable : Integrable sq P := by
      have hmapped : Integrable (fun a => ‖phi t i a‖ ^ 2)
          (@Measure.map Omega A mOmega _ (xi current) P) := by
        rw [hmap]
        exact hsq_int t i
      simpa [sq, noise, xi, current, Function.comp_def] using
        hmapped.comp_measurable hraw_meas
    have hsq_integral : ∫ omega, sq omega ∂P = ∫ a, ‖phi t i a‖ ^ 2 ∂mu := by
      simpa [sq, noise, xi, current, Function.comp_def] using
        (@integral_comp_eq_integral_of_map_eq
          Omega A ℝ mOmega _ _ _ P (xi current) mu
            (fun a => ‖phi t i a‖ ^ 2)
          hraw_meas.aemeasurable
          (by simpa [hmap] using
            ((hphi t i).norm.pow_const 2).aestronglyMeasurable)
          hmap)
    have hsq_ce : P[sq | mPast] =ᵐ[P] fun _ => ∫ omega, sq omega ∂P :=
      MeasureTheory.condExp_indep_eq
        hfresh_le hmPast_le hsq_meas_fresh hPastFresh.symm
    have hsq_bound : P[sq | mPast] ≤ᵐ[P] fun _ => sigma ^ 2 := by
      filter_upwards [hsq_ce] with omega homega
      rw [homega, hsq_integral]
      exact hsq_le t i
    exact ⟨hcentered, ⟨⟨hmPast_le, inferInstance, hsq_integrable⟩, hsq_bound⟩⟩
  constructor
  · intro t i
    simpa [P, noise] using (one_coordinate t i).1
  · intro t i
    simpa [P, noise] using (one_coordinate t i).2

/-- The complete stochastic part of a `Setup` for a deterministic transform of
the canonical iid time-node table.  The remaining equation-(41) work is now
finite-row data: exhibit the three-point marginal and verify its elementary
center and second moment. -/
theorem iidMiniBatchSampleLaw_stochasticContracts
    {A : Type*} [MeasurableSpace A]
    (n d : ℕ) (mu : Measure A) [IsProbabilityMeasure mu]
    (phi : ℕ → Fin n → A → Point d)
    (hphi : ∀ t i, Measurable (phi t i))
    (sigma : ℝ)
    (hphi_int : ∀ t i, Integrable (phi t i) mu)
    (hcenter : ∀ t i, ∫ a, phi t i a ∂mu = 0)
    (hsq_int : ∀ t i, Integrable (fun a => ‖phi t i a‖ ^ 2) mu)
    (hsq_le : ∀ t i, ∫ a, ‖phi t i a‖ ^ 2 ∂mu ≤ sigma ^ 2) :
    let noise : ℕ → SOptLib.miniBatchSamplePath n A → NodeTable n d :=
      fun t omega i => phi t i (omega t i)
    (∀ t i,
      SOptLib.ConditionalExpectation.conditionalExpectationEq
        (SOptLib.iidMiniBatchSampleLaw n mu)
        (preSamplingHistoryOf noise t) (fun omega => noise t omega i) (fun _ => 0)) ∧
    (∀ t i,
      ConditionalSecondMomentBound (SOptLib.iidMiniBatchSampleLaw n mu)
        (preSamplingHistoryOf noise t) (fun omega => noise t omega i)
        (sigma ^ 2)) ∧
    (∀ t,
      NodeConditionallyIndependent (SOptLib.iidMiniBatchSampleLaw n mu)
        (preSamplingHistoryOf noise t) (fun i omega => noise t omega i)) := by
  dsimp only
  obtain ⟨hcentered, hsecond⟩ :=
    iidMiniBatchSampleLaw_centered_secondMoment n d mu phi hphi sigma
      hphi_int hcenter hsq_int hsq_le
  exact ⟨hcentered, hsecond,
    iidMiniBatchSampleLaw_nodeConditionallyIndependent n d mu phi hphi⟩

/-- The symmetric three-point atom in source equation (41), with its exact
center and second moment. -/
theorem storageThreePointAtom_spec (p e : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ (atom : Fin 3 → ℝ) (nu : Measure (Fin 3)),
      IsProbabilityMeasure nu ∧ Integrable atom nu ∧
      (∫ a, atom a ∂nu) = 0 ∧
      (∫ a, ‖atom a‖ ^ 2 ∂nu) = p * e ^ 2 ∧
      ∀ F : ℝ → ℝ, F 0 = 0 → F (-e) = F e →
        (∫ a, F (atom a) ∂nu) = p * F e := by
  let mass : Fin 3 → ℝ := fun a =>
    if a = 0 then p / 2 else if a = 1 then p / 2 else 1 - p
  have hmass_nonneg : ∀ a, 0 ≤ mass a := by
    intro a
    fin_cases a <;> simp [mass] <;> linarith
  have hmass_sum : ∑ a, mass a = 1 := by
    simp [mass, Fin.sum_univ_succ]
    ring
  let pmf : PMF (Fin 3) :=
    PMF.ofFintypeOfReal mass hmass_nonneg hmass_sum
  let nu : Measure (Fin 3) := pmf.toMeasure
  let atom : Fin 3 → ℝ := fun a =>
    if a = 0 then e else if a = 1 then -e else 0
  have hnu_probability : IsProbabilityMeasure nu := by
    dsimp [nu]
    infer_instance
  have hatom_integrable : Integrable atom nu := by
    exact Integrable.of_finite
  have hmass_real (a : Fin 3) : nu.real ({a} : Set (Fin 3)) = mass a := by
    rw [Measure.real_def]
    rw [PMF.toMeasure_apply_singleton pmf a (measurableSet_singleton a)]
    simp [pmf, PMF.ofFintypeOfReal_apply, hmass_nonneg a]
  have hcenter : (∫ a, atom a ∂nu) = 0 := by
    rw [MeasureTheory.integral_fintype .of_finite]
    simp_rw [hmass_real]
    simp [mass, atom, Fin.sum_univ_succ]
  have hsecond : (∫ a, ‖atom a‖ ^ 2 ∂nu) = p * e ^ 2 := by
    rw [MeasureTheory.integral_fintype .of_finite]
    simp_rw [hmass_real]
    simp [mass, atom, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    ring
  have heven (F : ℝ → ℝ) (hF0 : F 0 = 0) (hFe : F (-e) = F e) :
      (∫ a, F (atom a) ∂nu) = p * F e := by
    rw [MeasureTheory.integral_fintype .of_finite]
    simp_rw [hmass_real]
    simp [mass, atom, Fin.sum_univ_succ, hF0, hFe]
    ring
  exact ⟨atom, nu, hnu_probability, hatom_integrable, hcenter, hsecond, heven⟩

/-- Label-dependent equation-(41) atoms may be sampled simultaneously from one
finite product law.  Each selected coordinate retains its own center and exact
second moment. -/
theorem finite_three_point_product_law_spec
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p e : ι → ℝ) (hp0 : ∀ l, 0 ≤ p l) (hp1 : ∀ l, p l ≤ 1) :
    ∃ (atom : ι → Fin 3 → ℝ) (nu : ι → Measure (Fin 3)),
      (∀ l, IsProbabilityMeasure (nu l)) ∧
      let mu : Measure (ι → Fin 3) := Measure.pi nu
      IsProbabilityMeasure mu ∧ ∀ l,
        Integrable (fun z => atom l (z l)) mu ∧
        (∫ z, atom l (z l) ∂mu) = 0 ∧
        Integrable (fun z => ‖atom l (z l)‖ ^ 2) mu ∧
        (∫ z, ‖atom l (z l)‖ ^ 2 ∂mu) = p l * e l ^ 2 ∧
        ∀ F : ℝ → ℝ, F 0 = 0 → F (-(e l)) = F (e l) →
          (∫ z, F (atom l (z l)) ∂mu) = p l * F (e l) := by
  classical
  have hlabel : ∀ l, ∃ (a : Fin 3 → ℝ) (m : Measure (Fin 3)),
      IsProbabilityMeasure m ∧ Integrable a m ∧
      (∫ x, a x ∂m) = 0 ∧ (∫ x, ‖a x‖ ^ 2 ∂m) = p l * e l ^ 2 ∧
      ∀ F : ℝ → ℝ, F 0 = 0 → F (-(e l)) = F (e l) →
        (∫ x, F (a x) ∂m) = p l * F (e l) := by
    intro l
    exact storageThreePointAtom_spec (p l) (e l) (hp0 l) (hp1 l)
  choose atom nu hnu hatom_int hcenter hsecond heven using hlabel
  refine ⟨atom, nu, hnu, ?_⟩
  letI (l : ι) : IsProbabilityMeasure (nu l) := hnu l
  let mu : Measure (ι → Fin 3) := Measure.pi nu
  have hmu_probability : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  refine ⟨hmu_probability, fun l => ?_⟩
  have hmap : Measure.map (fun z : ι → Fin 3 => z l) mu = nu l := by
    simpa [mu] using (Measure.pi_map_eval (μ := nu) l)
  have heval : Measurable (fun z : ι → Fin 3 => z l) :=
    measurable_pi_apply l
  have hselected_int : Integrable (fun z : ι → Fin 3 => atom l (z l)) mu := by
    have hmapped : Integrable (atom l)
        (Measure.map (fun z : ι → Fin 3 => z l) mu) := by
      rw [hmap]
      exact hatom_int l
    simpa [Function.comp_def] using hmapped.comp_measurable heval
  have hselected_center : (∫ z : ι → Fin 3, atom l (z l) ∂mu) = 0 := by
    calc
      (∫ z : ι → Fin 3, atom l (z l) ∂mu) =
          ∫ x, atom l x ∂nu l := by
        exact integral_comp_eq_integral_of_map_eq heval.aemeasurable
          (by simpa [hmap] using (hatom_int l).aestronglyMeasurable) hmap
      _ = 0 := hcenter l
  have hselected_sq_int :
      Integrable (fun z : ι → Fin 3 => ‖atom l (z l)‖ ^ 2) mu := by
    have hatom_sq_int : Integrable (fun x => ‖atom l x‖ ^ 2) (nu l) :=
      Integrable.of_finite
    have hmapped : Integrable (fun x => ‖atom l x‖ ^ 2)
        (Measure.map (fun z : ι → Fin 3 => z l) mu) := by
      rw [hmap]
      exact hatom_sq_int
    simpa [Function.comp_def] using hmapped.comp_measurable heval
  refine ⟨hselected_int, hselected_center, hselected_sq_int, ?_, ?_⟩
  · calc
      (∫ z : ι → Fin 3, ‖atom l (z l)‖ ^ 2 ∂mu) =
          ∫ x, ‖atom l x‖ ^ 2 ∂nu l := by
        exact integral_comp_eq_integral_of_map_eq heval.aemeasurable
          (by rw [hmap]; exact (Integrable.of_finite :
            Integrable (fun x => ‖atom l x‖ ^ 2) (nu l)).aestronglyMeasurable) hmap
      _ = p l * e l ^ 2 := hsecond l
  · intro F hF0 hFe
    calc
      (∫ z : ι → Fin 3, F (atom l (z l)) ∂mu) =
          ∫ x, F (atom l x) ∂nu l := by
        exact integral_comp_eq_integral_of_map_eq heval.aemeasurable
          (by rw [hmap]; exact (Integrable.of_finite :
            Integrable (fun x => F (atom l x)) (nu l)).aestronglyMeasurable) hmap
      _ = p l * F (e l) := heven l F hF0 hFe

/-- The label product supplies one storage atom and one independent quadratic
atom to every time-node row.  Their orthogonal coordinate placement spends at
most `sigma^2 / 2` on each component, so the transformed iid table satisfies
all three stochastic `Setup` contracts. -/
theorem storage_noise_transform_spec
    (m n : ℕ) (sigma : ℝ) (hsigma : 0 < sigma)
    (p e : Fin m × Fin n → ℝ)
    (hp0 : ∀ q, 0 ≤ p q) (hp1 : ∀ q, p q ≤ 1)
    (hstorage : ∀ q, p q * e q ^ 2 ≤ sigma ^ 2 / 2) :
    ∃ (atom : ((Fin m × Fin n) ⊕ Unit) → Fin 3 → ℝ)
      (nu : ((Fin m × Fin n) ⊕ Unit) → Measure (Fin 3))
        (phi : ℕ → Fin n →
          (((Fin m × Fin n) ⊕ Unit) → Fin 3) → Point (m * n + 2)),
      (∀ l, IsProbabilityMeasure (nu l)) ∧
      (∀ (q : Fin m × Fin n) (F : ℝ → ℝ),
        F 0 = 0 → F (-(e q)) = F (e q) →
          (∫ z, F (atom (Sum.inl q) (z (Sum.inl q))) ∂Measure.pi nu) =
            p q * F (e q)) ∧
      (∀ (t : Fin m) (i : Fin n) z,
        phi t.1 i z =
          PiLp.single 2
              (Fin.castAdd 2 (finProdFinEquiv (t, i)))
              (atom (Sum.inl (t, i)) (z (Sum.inl (t, i)))) +
            PiLp.single 2 (Fin.last (m * n + 1))
              (atom (Sum.inr ()) (z (Sum.inr ())))) ∧
      (∀ (q : Fin m × Fin n) (t : ℕ) (i : Fin n) z,
        phi t i z (Fin.castAdd 2 (finProdFinEquiv q)) =
          loadingPulse q.1.1 q.2
            (atom (Sum.inl q) (z (Sum.inl q))) t i) ∧
      (∀ t i z, phi t i z ⟨m * n, by omega⟩ = 0) ∧
      let mu : Measure ((((Fin m × Fin n) ⊕ Unit) → Fin 3)) := Measure.pi nu
      let noise : ℕ →
          SOptLib.miniBatchSamplePath n
            ((((Fin m × Fin n) ⊕ Unit) → Fin 3)) → NodeTable n (m * n + 2) :=
        fun t omega i => phi t i (omega t i)
      (∀ t i,
        SOptLib.ConditionalExpectation.conditionalExpectationEq
          (SOptLib.iidMiniBatchSampleLaw n mu)
          (preSamplingHistoryOf noise t)
          (fun omega => noise t omega i) (fun _ => 0)) ∧
      (∀ t i,
        ConditionalSecondMomentBound (SOptLib.iidMiniBatchSampleLaw n mu)
          (preSamplingHistoryOf noise t) (fun omega => noise t omega i)
          (sigma ^ 2)) ∧
      (∀ t,
        NodeConditionallyIndependent (SOptLib.iidMiniBatchSampleLaw n mu)
          (preSamplingHistoryOf noise t) (fun i omega => noise t omega i)) := by
  classical
  let pAll : ((Fin m × Fin n) ⊕ Unit) → ℝ := fun l =>
    match l with
    | Sum.inl q => p q
    | Sum.inr _ => 1
  let eAll : ((Fin m × Fin n) ⊕ Unit) → ℝ := fun l =>
    match l with
    | Sum.inl q => e q
    | Sum.inr _ => sigma / Real.sqrt 2
  have hpAll0 : ∀ l, 0 ≤ pAll l := by
    intro l
    cases l with
    | inl q => exact hp0 q
    | inr u => cases u; simp [pAll]
  have hpAll1 : ∀ l, pAll l ≤ 1 := by
    intro l
    cases l with
    | inl q => exact hp1 q
    | inr u => cases u; simp [pAll]
  obtain ⟨atom, nu, hnu, hrow⟩ :=
    finite_three_point_product_law_spec pAll eAll hpAll0 hpAll1
  letI (l : ((Fin m × Fin n) ⊕ Unit)) : IsProbabilityMeasure (nu l) := hnu l
  let mu : Measure ((((Fin m × Fin n) ⊕ Unit) → Fin 3)) := Measure.pi nu
  have hmu_probability : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  letI : IsProbabilityMeasure mu := hmu_probability
  have hrow' : ∀ l,
      Integrable (fun z => atom l (z l)) mu ∧
      (∫ z, atom l (z l) ∂mu) = 0 ∧
      Integrable (fun z => ‖atom l (z l)‖ ^ 2) mu ∧
      (∫ z, ‖atom l (z l)‖ ^ 2 ∂mu) = pAll l * eAll l ^ 2 := by
    intro l
    have hl := hrow.2 l
    exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1⟩
  let storageCoord : Fin m × Fin n → Fin (m * n + 2) :=
    fun q => Fin.castAdd 2 (finProdFinEquiv q)
  let quadraticCoord : Fin (m * n + 2) := Fin.last (m * n + 1)
  have hcoord_ne (q : Fin m × Fin n) : storageCoord q ≠ quadraticCoord := by
    intro h
    have hval := congrArg Fin.val h
    change (finProdFinEquiv q).val = m * n + 1 at hval
    omega
  let phi : ℕ → Fin n →
      ((((Fin m × Fin n) ⊕ Unit) → Fin 3)) → Point (m * n + 2) :=
    fun t i z =>
      if ht : t < m then
        PiLp.single 2 (storageCoord (⟨t, ht⟩, i))
            (atom (Sum.inl (⟨t, ht⟩, i)) (z (Sum.inl (⟨t, ht⟩, i)))) +
          PiLp.single 2 quadraticCoord
            (atom (Sum.inr ()) (z (Sum.inr ())))
      else
        PiLp.single 2 quadraticCoord
          (atom (Sum.inr ()) (z (Sum.inr ())) )
  have hphi_meas : ∀ t i, Measurable (phi t i) := by
    intro t i
    exact measurable_of_finite _
  have hphi_int : ∀ t i, Integrable (phi t i) mu := by
    intro t i
    exact Integrable.of_finite
  have hsingle_center
      (k : Fin (m * n + 2)) (l : ((Fin m × Fin n) ⊕ Unit))
      (hc : (∫ z, atom l (z l) ∂mu) = 0) :
      (∫ z, (PiLp.single 2 k (atom l (z l)) : Point (m * n + 2)) ∂mu) = 0 := by
    apply PiLp.ext
    intro q
    change (PiLp.proj (𝕜 := ℝ) 2
      (fun _ : Fin (m * n + 2) => ℝ) q)
        (∫ z, (PiLp.single 2 k (atom l (z l)) : Point (m * n + 2)) ∂mu) = 0
    rw [← (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (m * n + 2) => ℝ) q).integral_comp_comm
      (Integrable.of_finite : Integrable
        (fun z => (PiLp.single 2 k (atom l (z l)) : Point (m * n + 2))) mu)]
    by_cases hq : q = k
    · subst q
      simpa using hc
    · simp [hq]
  have hphi_center : ∀ t i, (∫ z, phi t i z ∂mu) = 0 := by
    intro t i
    by_cases ht : t < m
    · rw [show phi t i = fun z =>
          PiLp.single 2 (storageCoord (⟨t, ht⟩, i))
              (atom (Sum.inl (⟨t, ht⟩, i))
                (z (Sum.inl (⟨t, ht⟩, i)))) +
            PiLp.single 2 quadraticCoord
              (atom (Sum.inr ()) (z (Sum.inr ()))) by
          funext z
          simp [phi, ht]]
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        hsingle_center _ _ (hrow' (Sum.inl (⟨t, ht⟩, i))).2.1,
        hsingle_center _ _ (hrow' (Sum.inr ())).2.1]
      simp
    · rw [show phi t i = fun z =>
          PiLp.single 2 quadraticCoord
            (atom (Sum.inr ()) (z (Sum.inr ()))) by
          funext z
          simp [phi, ht]]
      exact hsingle_center _ _ (hrow' (Sum.inr ())).2.1
  have hquad_second :
      (∫ z, ‖atom (Sum.inr ()) (z (Sum.inr ()))‖ ^ 2 ∂mu) =
        sigma ^ 2 / 2 := by
    calc
      (∫ z, ‖atom (Sum.inr ()) (z (Sum.inr ()))‖ ^ 2 ∂mu) =
          pAll (Sum.inr ()) * eAll (Sum.inr ()) ^ 2 :=
        (hrow' (Sum.inr ())).2.2.2
      _ = sigma ^ 2 / 2 := by
        have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
          Real.sq_sqrt (by norm_num)
        simp only [pAll, eAll, one_mul]
        rw [div_pow, hsqrt]
  have hnorm_two (q : Fin m × Fin n) (a b : ℝ) :
      ‖(PiLp.single 2 (storageCoord q) a +
          PiLp.single 2 quadraticCoord b : Point (m * n + 2))‖ ^ 2 =
        ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have horth : inner ℝ
        (PiLp.single 2 (storageCoord q) a : Point (m * n + 2))
        (PiLp.single 2 quadraticCoord b) = 0 := by
      rw [PiLp.inner_apply]
      apply Finset.sum_eq_zero
      intro x _hx
      by_cases hx : x = storageCoord q
      · subst x
        simp [hcoord_ne q]
      · simp [hx]
    simpa [pow_two, PiLp.norm_single] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (PiLp.single 2 (storageCoord q) a : Point (m * n + 2))
        (PiLp.single 2 quadraticCoord b) horth)
  have hsigma_sq_pos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hphi_sq_int : ∀ t i,
      Integrable (fun z => ‖phi t i z‖ ^ 2) mu := by
    intro t i
    exact Integrable.of_finite
  have hphi_sq_le : ∀ t i,
      (∫ z, ‖phi t i z‖ ^ 2 ∂mu) ≤ sigma ^ 2 := by
    intro t i
    by_cases ht : t < m
    · let q : Fin m × Fin n := (⟨t, ht⟩, i)
      calc
        (∫ z, ‖phi t i z‖ ^ 2 ∂mu) =
            (∫ z, ‖atom (Sum.inl q) (z (Sum.inl q))‖ ^ 2 +
              ‖atom (Sum.inr ()) (z (Sum.inr ()))‖ ^ 2 ∂mu) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            simp only [phi, dif_pos ht]
            exact hnorm_two q _ _
        _ = (∫ z, ‖atom (Sum.inl q) (z (Sum.inl q))‖ ^ 2 ∂mu) +
              (∫ z, ‖atom (Sum.inr ()) (z (Sum.inr ()))‖ ^ 2 ∂mu) := by
          rw [integral_add Integrable.of_finite Integrable.of_finite]
        _ = p q * e q ^ 2 + sigma ^ 2 / 2 := by
          rw [hquad_second, (hrow' (Sum.inl q)).2.2.2]
        _ ≤ sigma ^ 2 := by
          nlinarith [hstorage q]
    · calc
        (∫ z, ‖phi t i z‖ ^ 2 ∂mu) =
            ∫ z, ‖atom (Sum.inr ()) (z (Sum.inr ()))‖ ^ 2 ∂mu := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            simp [phi, ht, PiLp.norm_single]
        _ = sigma ^ 2 / 2 := hquad_second
        _ ≤ sigma ^ 2 := by nlinarith
  have hcontracts := iidMiniBatchSampleLaw_stochasticContracts
    n (m * n + 2) mu phi hphi_meas sigma hphi_int hphi_center
      hphi_sq_int hphi_sq_le
  refine ⟨atom, nu, phi, hnu, ?_, ?_, ?_, ?_, ?_⟩
  · intro q F hF0 hFe
    simpa [pAll, eAll, mu] using
      ((hrow.2 (Sum.inl q)).2.2.2.2 F hF0 hFe)
  · intro t i z
    simp [phi, storageCoord, quadraticCoord, t.isLt]
  · intro q t i z
    by_cases ht : t < m
    · let q' : Fin m × Fin n := (⟨t, ht⟩, i)
      by_cases hqq : q' = q
      · subst q
        simp [phi, ht, storageCoord, quadraticCoord, loadingPulse, q',
          hcoord_ne]
      · have hcoord : storageCoord q' ≠ storageCoord q := by
          intro h
          apply hqq
          apply finProdFinEquiv.injective
          dsimp [storageCoord] at h
          have hv := congrArg (fun x : Fin (m * n + 2) => x.val) h
          exact Fin.ext hv
        have hpulse : ¬ (t = q.1.1 ∧ i = q.2) := by
          rintro ⟨htq, hiq⟩
          apply hqq
          apply Prod.ext
          · exact Fin.ext htq
          · exact hiq
        simp [phi, ht, storageCoord, quadraticCoord, loadingPulse, q', hcoord,
          hcoord_ne, hpulse]
    · have htq : t ≠ q.1.1 := by
        intro h
        subst t
        exact ht q.1.2
      simp [phi, ht, storageCoord, quadraticCoord, loadingPulse, hcoord_ne,
        htq]
  · intro t i z
    let signalCoord : Fin (m * n + 2) := ⟨m * n, by omega⟩
    have hsignal_storage (q : Fin m × Fin n) :
        signalCoord ≠ storageCoord q := by
      intro h
      have hv := congrArg Fin.val h
      change m * n = (finProdFinEquiv q).val at hv
      have hlt : (finProdFinEquiv q).val < m * n := (finProdFinEquiv q).isLt
      omega
    have hsignal_quadratic : signalCoord ≠ quadraticCoord := by
      intro h
      have hv := congrArg Fin.val h
      change m * n = m * n + 1 at hv
      omega
    change phi t i z signalCoord = 0
    by_cases ht : t < m
    · simp [phi, ht, hsignal_storage, hsignal_quadratic]
    · simp [phi, ht, hsignal_quadratic]
  · simpa [mu] using hcontracts

/-- A positive source window length is realized by an actual admissible
interval.  This extracts the pulse-calibration window hidden inside the two
finite suprema in `windowLength`. -/
theorem windowLength_attained
    (N : NetworkSetup n) (T t : ℕ) (s : ℝ)
    (htT : t < T) (hW : 0 < windowLength N T t s) :
    ∃ P Q : ℕ, t ≤ P ∧ P < Q ∧ Q ≤ T ∧
      s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon ∧
      Q - P = windowLength N T t s := by
  classical
  let outer : Finset ℕ := Finset.Icc t T
  let inner : ℕ → Finset ℕ := fun P => Finset.Icc (P + 1) T
  let value : ℕ → ℕ → ℕ := fun P Q =>
    if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon then Q - P else 0
  let best : ℕ → ℕ := fun P => (inner P).sup (value P)
  have houter_nonempty : outer.Nonempty := by
    exact ⟨t, by simp [outer, Nat.le_of_lt htT]⟩
  have hwindow : windowLength N T t s = outer.sup best := by
    simp [windowLength, htT, outer, inner, value, best]
  obtain ⟨P, hPmem, hPbest⟩ :=
    Finset.exists_mem_eq_sup outer houter_nonempty best
  have hbest_pos : 0 < best P := by
    rw [← hPbest, ← hwindow]
    exact hW
  have hPT : P < T := by
    have hPle : P ≤ T := (Finset.mem_Icc.1 hPmem).2
    apply lt_of_le_of_ne hPle
    intro hEq
    have hTP : P = T := hEq
    subst P
    simp [best, inner] at hbest_pos
  have hinner_nonempty : (inner P).Nonempty := by
    exact ⟨P + 1, by simp [inner, Nat.succ_le_iff, hPT]⟩
  obtain ⟨Q, hQmem, hQvalue⟩ :=
    Finset.exists_mem_eq_sup (inner P) hinner_nonempty (value P)
  have hvalue_pos : 0 < value P Q := by
    rw [← hQvalue]
    exact hbest_pos
  have hbudget : s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon := by
    by_contra hnot
    simp [value, hnot] at hvalue_pos
  have hPbounds := Finset.mem_Icc.1 hPmem
  have hQbounds := Finset.mem_Icc.1 hQmem
  refine ⟨P, Q, hPbounds.1, ?_, hQbounds.2, hbudget, ?_⟩
  · exact hQbounds.1
  · rw [hwindow, hPbest]
    change Q - P = (inner P).sup (value P)
    rw [hQvalue]
    simp [value, hbudget]

/-- Every retained positive-window label has a deterministic calibrated pulse
whose magnitude is large enough for the equation-(41) probability.  The cap is
shrunk by the network-only influence bound before invoking the source loading
theorem. -/
theorem storage_calibrated_pulse_spec
    (N : NetworkSetup n) (L sigma : ℝ) (hL : 0 < L) (hsigma : 0 < sigma) :
    ∃ sLoad : ℝ, 0 < sLoad ∧ sLoad ≤ 1 / (64 * n) ∧
      ∀ (T : ℕ) (s : ℝ), 0 < s → s ≤ sLoad →
      ∀ (j : ℕ) (i : Fin n),
        j + loadingDelay N s < T → s ≤ |influenceRow N j i| →
        0 < windowLength N T (j + loadingDelay N s) s →
        ∃ P Q : ℕ, ∃ a e : ℝ,
          3 / 4 ≤ a ∧ a ≤ 5 / 4 ∧
          e = -a * sigma / (s * influenceRow N j i) ∧
          j + loadingDelay N s ≤ P ∧ P < Q ∧ Q ≤ T ∧
          Q - P = windowLength N T (j + loadingDelay N s) s ∧
          3 * sigma ≤ |e| ∧
          (∀ t ∈ Finset.Ico P Q,
            L * (sigma / L) / 16 ≤
              |negativeCurvatureDerivative L (sigma / L)
                (loadingArithmeticMean N L (sigma / L) s j i e t)|) ∧
          (∀ t,
            retainedLoadingTracker N L (sigma / L) s j i e (t + 1) =
              N.colMix t *ᵥ retainedLoadingTracker N L (sigma / L) s j i e t +
                (N.colMix t - 1) *ᵥ
                  (fun k => negativeCurvatureDerivative L (sigma / L)
                    ((loadingTrajectory N L (sigma / L) s j i e t).primal k) +
                    loadingPulse j i e t k)) := by
  obtain ⟨s0, hs0, hs0cap, hload⟩ := negative_curvature_loading N L hL
  have hB : 0 < influenceRowBound N := by
    unfold influenceRowBound influenceOperatorBound columnMixingConstant
    have hblock : 0 < blockContraction N := blockContraction_pos N
    have hmix : 0 < 1 - mixingRate N := sub_pos.mpr (mixingRate_lt_one N)
    have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    positivity
  let sLoad : ℝ := min s0 ((1 / 4) / influenceRowBound N)
  have hsLoad : 0 < sLoad := by
    dsimp [sLoad]
    exact lt_min hs0 (div_pos (by norm_num) hB)
  refine ⟨sLoad, hsLoad, (min_le_left _ _).trans hs0cap, ?_⟩
  intro T s hs hsCap j i hjT hji hW
  obtain ⟨P, Q, htP, hPQ, hQT, hbudget, hlength⟩ :=
    windowLength_attained N T (j + loadingDelay N s) s hjT hW
  have hD : 0 < sigma / L := div_pos hsigma hL
  have hs0le : s ≤ s0 := hsCap.trans (min_le_left _ _)
  obtain ⟨a, ha0, ha1, hloaded⟩ :=
    hload (sigma / L) s hD hs hs0le j i hji P Q htP hPQ hbudget
  let e : ℝ := -a * (sigma / L) / ((s / L) * influenceRow N j i)
  have hbne : influenceRow N j i ≠ 0 := by
    have habs : 0 < |influenceRow N j i| := hs.trans_le hji
    exact abs_pos.mp habs
  have hsBcap : s * influenceRowBound N ≤ 1 / 4 := by
    have hsdiv : s ≤ (1 / 4) / influenceRowBound N :=
      hsCap.trans (min_le_right _ _)
    exact (le_div_iff₀ hB).1 hsdiv
  have hbB : |influenceRow N j i| ≤ influenceRowBound N := by
    exact (abs_le_nodeL2Norm (influenceRow N j) i).trans
      (influenceRow_nodeL2_le N j)
  have hsabsB : s * |influenceRow N j i| ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hbB hs.le).trans hsBcap
  have hdenpos : 0 < s * |influenceRow N j i| :=
    mul_pos hs (abs_pos.mpr hbne)
  have heq : e = -a * sigma / (s * influenceRow N j i) := by
    dsimp [e]
    field_simp [hL.ne', hs.ne', hbne]
  have heabs : |e| = a * sigma / (s * |influenceRow N j i|) := by
    rw [heq, abs_div, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ a),
      abs_of_pos hsigma, abs_of_pos hs]
  have hscaled : 3 * sigma * (s * |influenceRow N j i|) ≤ a * sigma := by
    have hleft : 3 * sigma * (s * |influenceRow N j i|) ≤ 3 * sigma * (1 / 4) :=
      mul_le_mul_of_nonneg_left hsabsB (by positivity)
    have hright : 3 * sigma * (1 / 4) ≤ a * sigma := by
      nlinarith
    exact hleft.trans hright
  have heLower : 3 * sigma ≤ |e| := by
    rw [heabs]
    exact (le_div_iff₀ hdenpos).2 hscaled
  refine ⟨P, Q, a, e, ha0, ha1, heq, htP, hPQ, hQT, hlength, heLower, ?_, ?_⟩
  · simpa [e] using hloaded.1
  · simpa [e] using hloaded.2

/-- Objective-side package for the source equation-(41) finite product.  The
storage coordinates use the reflected loading potential, the penultimate
coordinate is the deterministic equation-(29) signal, and the last coordinate
is the quadratic gap filler. -/
theorem storage_product_objective_spec
    (m n : ℕ) (L Δ sigma A x0 y0 : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hsigma : 0 < sigma) (hA : 0 < A)
    (hx0 : |x0| ≤ A)
    (hA_sq : A ^ 2 = Δ / (2 * L))
    (hy0_sq : y0 ^ 2 = Δ / L + x0 ^ 2) :
    let d := m * n + 2
    let signalCoord : Fin d := ⟨m * n, by omega⟩
    let quadraticCoord : Fin d := Fin.last (m * n + 1)
    let f : Fin d → ℝ → ℝ := fun k x =>
      if k = signalCoord then deterministicGapPotential L A x
      else if k = quadraticCoord then L * x ^ 2 / 2
      else negativeCurvaturePotential L (sigma / L) x
    let g : Fin d → ℝ → ℝ := fun k x =>
      if k = signalCoord then deterministicGapDerivative L A x
      else if k = quadraticCoord then L * x
      else negativeCurvatureDerivative L (sigma / L) x
    let F : Point d → ℝ := fun z => ∑ k, f k (z k)
    let initial : Point d := WithLp.toLp 2 (fun k =>
      if k = signalCoord then x0 else if k = quadraticCoord then y0 else 0)
    (Differentiable ℝ F ∧ LipschitzWith ⟨L, hL.le⟩ (gradient F)) ∧
      (∀ z, 0 ≤ F z) ∧
      sInf (Set.range F) = 0 ∧
      F initial - sInf (Set.range F) = Δ ∧
      (∀ z, (gradient F z) signalCoord =
        deterministicGapDerivative L A (z signalCoord)) ∧
      (∀ z, gradient F z = WithLp.toLp 2 (fun k => g k (z k))) := by
  let d := m * n + 2
  let signalCoord : Fin d := ⟨m * n, by omega⟩
  let quadraticCoord : Fin d := Fin.last (m * n + 1)
  let f : Fin d → ℝ → ℝ := fun k x =>
    if k = signalCoord then deterministicGapPotential L A x
    else if k = quadraticCoord then L * x ^ 2 / 2
    else negativeCurvaturePotential L (sigma / L) x
  let g : Fin d → ℝ → ℝ := fun k x =>
    if k = signalCoord then deterministicGapDerivative L A x
    else if k = quadraticCoord then L * x
    else negativeCurvatureDerivative L (sigma / L) x
  let F : Point d → ℝ := fun z => ∑ k, f k (z k)
  let initial : Point d := WithLp.toLp 2 (fun k =>
    if k = signalCoord then x0 else if k = quadraticCoord then y0 else 0)
  dsimp only
  have hsignal_ne_quad : signalCoord ≠ quadraticCoord := by
    intro h
    have hv := congrArg Fin.val h
    change m * n = m * n + 1 at hv
    omega
  have hquad_ne_signal : quadraticCoord ≠ signalCoord :=
    Ne.symm hsignal_ne_quad
  have hD : 0 < sigma / L := div_pos hsigma hL
  have hderiv : ∀ k z, HasDerivAt (f k) (g k z) z := by
    intro k z
    by_cases hks : k = signalCoord
    · subst k
      simp only [f, g, if_pos rfl]
      simpa using
        (deterministicGapPotential_hasGradientAt L A z hA.le).hasDerivAt
    · by_cases hkq : k = quadraticCoord
      · subst k
        simp only [f, g]
        simp only [if_neg hquad_ne_signal, if_pos rfl]
        simp only [if_true]
        have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * z) z := by
          simpa using (hasDerivAt_pow 2 z)
        convert hsq.const_mul (L / 2) using 1 <;> ring
      · simp only [f, g, if_neg hks, if_neg hkq]
        simpa using
          (negativeCurvaturePotential_hasGradientAt L (sigma / L) z hD.le).hasDerivAt
  have hlip : ∀ k x y, ‖g k x - g k y‖ ≤ L * ‖x - y‖ := by
    intro k x y
    by_cases hks : k = signalCoord
    · subst k
      simp only [g, if_pos rfl]
      exact deterministicGapDerivative_norm_sub_le L A x y hL.le hA.le
    · by_cases hkq : k = quadraticCoord
      · subst k
        simp only [g]
        simp only [if_neg hquad_ne_signal, if_pos rfl]
        simp only [if_true]
        rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_pos hL]
      · simp only [g, if_neg hks, if_neg hkq]
        exact negativeCurvatureDerivative_norm_sub_le
          L (sigma / L) x y hL.le hD.le
  have hsmooth : Differentiable ℝ F ∧
      LipschitzWith ⟨L, hL.le⟩ (gradient F) := by
    simpa only [F] using
      separablePoint_local_smooth f g L hL.le hderiv hlip
  have hnonneg : ∀ z, 0 ≤ F z := by
    intro z
    dsimp only [F]
    apply Finset.sum_nonneg
    intro k _hk
    by_cases hks : k = signalCoord
    · simp only [f, if_pos hks]
      exact deterministicGapPotential_nonneg L A (z k) hL.le hA.le
    · by_cases hkq : k = quadraticCoord
      · simp only [f, if_neg hks, if_pos hkq]
        positivity
      · simp only [f, if_neg hks, if_neg hkq]
        exact negativeCurvaturePotential_nonneg L (sigma / L) (z k) hL.le hD
  have hgap_zero : deterministicGapPotential L A (2 * A) = 0 := by
    rw [deterministicGapPotential_eq_outer_nonneg L A (2 * A) hA.le (by linarith)]
    ring
  let minimizer : Point d := WithLp.toLp 2 (fun k =>
    if k = signalCoord then 2 * A else 0)
  have hFmin : F minimizer = 0 := by
    dsimp only [F]
    apply Finset.sum_eq_zero
    intro k _hk
    by_cases hks : k = signalCoord
    · subst k
      simp [f, minimizer, hgap_zero]
    · by_cases hkq : k = quadraticCoord
      · subst k
        simp only [f, minimizer, PiLp.toLp_apply]
        simp only [if_neg hquad_ne_signal, if_pos rfl, zero_pow, Nat.ofNat_pos,
          ne_eq, not_false_eq_true, zero_div, mul_zero]
        simp only [if_true]
        ring
      · simp [f, minimizer, hks, hkq, negativeCurvaturePotential]
  have hsinf : sInf (Set.range F) = 0 := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨0, ⟨minimizer, hFmin⟩⟩
    · rintro _ ⟨z, rfl⟩
      exact hnonneg z
    · intro w hw
      exact ⟨0, ⟨minimizer, hFmin⟩, hw⟩
  have hFinit : F initial = Δ := by
    have hcoord : ∀ k, f k (initial k) =
        if k = signalCoord then deterministicGapPotential L A x0
        else if k = quadraticCoord then L * y0 ^ 2 / 2 else 0 := by
      intro k
      by_cases hks : k = signalCoord
      · subst k
        simp [f, initial]
      · by_cases hkq : k = quadraticCoord
        · subst k
          simp [f, initial, hquad_ne_signal]
        · simp [f, initial, hks, hkq, negativeCurvaturePotential]
    dsimp only [F]
    simp_rw [hcoord]
    rw [show (∑ k : Fin d,
          if k = signalCoord then deterministicGapPotential L A x0
          else if k = quadraticCoord then L * y0 ^ 2 / 2 else 0) =
        deterministicGapPotential L A x0 + L * y0 ^ 2 / 2 by
      calc
        (∑ k : Fin d,
            if k = signalCoord then deterministicGapPotential L A x0
            else if k = quadraticCoord then L * y0 ^ 2 / 2 else 0) =
            (∑ k : Fin d,
              ((if k = signalCoord then deterministicGapPotential L A x0 else 0) +
                (if k = quadraticCoord then L * y0 ^ 2 / 2 else 0))) := by
                apply Finset.sum_congr rfl
                intro k _hk
                by_cases hks : k = signalCoord
                · simp [hks, hsignal_ne_quad]
                · simp [hks]
        _ = (∑ k : Fin d,
              if k = signalCoord then deterministicGapPotential L A x0 else 0) +
            (∑ k : Fin d,
              if k = quadraticCoord then L * y0 ^ 2 / 2 else 0) := by
                rw [Finset.sum_add_distrib]
        _ = deterministicGapPotential L A x0 + L * y0 ^ 2 / 2 := by
                simp]
    exact deterministicGapPotential_gap_fill
      L Δ A x0 y0 hL hA.le hA_sq hx0 hy0_sq
  have hgradient (z : Point d) :
      gradient F z = WithLp.toLp 2 (fun k => g k (z k)) := by
    exact (hasGradientAt_separablePoint f g z (hderiv · _)).gradient
  refine ⟨hsmooth, hnonneg, hsinf, ?_, ?_, hgradient⟩
  · change F initial - sInf (Set.range F) = Δ
    rw [hFinit, hsinf]
    ring
  · intro z
    change (gradient F z) signalCoord =
      deterministicGapDerivative L A (z signalCoord)
    rw [hgradient]
    simp [g]

/-- One legal finite-dimensional source instance. The dimension and probability
space may vary between instances, as explicitly allowed by the paper. -/
structure FiniteInstance (n : ℕ) where
  d : ℕ
  Ω : Type
  [measurableSpace : MeasurableSpace Ω]
  setup : @Setup n d Ω measurableSpace
  finite_layer : @InFiniteHeterogeneityLayer n d Ω measurableSpace setup

namespace FiniteInstance

/-- The actual stationarity error of an instance under a positive constant
stepsize; no performance witness is stored in `FiniteInstance`. -/
def cost (I : FiniteInstance n) (α : ℝ) (T : PositiveHorizon) : ℝ :=
  @stationarityError n I.d I.Ω I.measurableSpace I.setup α T

def network (I : FiniteInstance n) : NetworkSetup n :=
  @Setup.network n I.d I.Ω I.measurableSpace I.setup

def lipschitz (I : FiniteInstance n) : ℝ :=
  @Setup.L n I.d I.Ω I.measurableSpace I.setup

def gap (I : FiniteInstance n) : ℝ :=
  @Setup.Δ n I.d I.Ω I.measurableSpace I.setup

def noiseScale (I : FiniteInstance n) : ℝ :=
  @Setup.σ n I.d I.Ω I.measurableSpace I.setup

def heterogeneityScale (I : FiniteInstance n) : ℝ :=
  @Setup.H n I.d I.Ω I.measurableSpace I.setup

end FiniteInstance

/-- The source class `C_H`: all legal finite-dimensional instances sharing
the fixed infinite network and declared scales, with initial heterogeneity at
most `H`. Book `#/assumptions/2/math`:
“`C_H` ... `H_0^2=...\le H^2` ... 每个 supremum 都在这个相同、与 `T` 无关的类上”. -/
def fixedInstanceClass
    (N : NetworkSetup n) (L Δ σ H : ℝ) : Set (FiniteInstance n) :=
  {I | I.network = N ∧
    I.lipschitz = L ∧ I.gap = Δ ∧ I.noiseScale = σ ∧ I.heterogeneityScale = H}

/-- The shifted, retained-component influence sum `\widetilde S_T(s)` in
(42), using the loading delay from (35). -/
def shiftedWindowInfluenceSum (N : NetworkSetup n) (T : PositiveHorizon)
    (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range T.1, ∑ i,
    if s ≤ |influenceRow N j i| then
      influenceRow N j i ^ 2 * windowLength N T.1 (j + loadingDelay N s) s
    else 0

theorem storage_windowLength_antitone
    (N : NetworkSetup n) (T : ℕ) (s : ℝ) {t u : ℕ} (htu : t ≤ u) :
    windowLength N T u s ≤ windowLength N T t s := by
  classical
  unfold windowLength
  by_cases huT : u < T
  · have htT : t < T := lt_of_le_of_lt htu huT
    rw [if_pos huT, if_pos htT]
    apply Finset.sup_le
    intro P hP
    have hP' : P ∈ Finset.Icc t T := by
      simp only [Finset.mem_Icc] at hP ⊢
      exact ⟨htu.trans hP.1, hP.2⟩
    exact Finset.le_sup (s := Finset.Icc t T)
      (f := fun P =>
        (Finset.Icc (P + 1) T).sup fun Q =>
          if s * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon
          then Q - P else 0) hP'
  · rw [if_neg huT]
    exact Nat.zero_le _

theorem storage_window_shift_sum_le
    (N : NetworkSetup n) (T τ : ℕ) (s : ℝ) (hτ : 1 ≤ τ) :
    (∑ j ∈ Finset.range T,
        ((windowLength N T (j + 1) s : ℝ) -
          (windowLength N T (j + τ) s : ℝ))) ≤
      (τ - 1 : ℕ) * (windowLength N T 0 s : ℝ) := by
  classical
  have hpoint (j : ℕ) :
      (windowLength N T (j + 1) s : ℝ) -
          (windowLength N T (j + τ) s : ℝ) =
        ∑ r ∈ Finset.range (τ - 1),
          ((windowLength N T (j + r + 1) s : ℝ) -
            (windowLength N T (j + r + 2) s : ℝ)) := by
    have htel := Finset.sum_range_sub'
      (fun r => (windowLength N T (j + r + 1) s : ℝ)) (τ - 1)
    have hsub : τ - 1 + 1 = τ := Nat.sub_add_cancel hτ
    simpa [hsub, Nat.add_assoc] using htel.symm
  have hr (r : ℕ) :
      (∑ j ∈ Finset.range T,
          ((windowLength N T (j + r + 1) s : ℝ) -
            (windowLength N T (j + r + 2) s : ℝ))) ≤
        (windowLength N T 0 s : ℝ) := by
    let A : ℕ → ℝ := fun j => (windowLength N T (j + r + 1) s : ℝ)
    have hterminal : 0 ≤ A T := by
      dsimp [A]
      exact_mod_cast Nat.zero_le (windowLength N T (T + r + 1) s)
    have htel := sum_range_sub_succ_le_first_of_last_nonneg
      A T hterminal
    have hfirst : A 0 ≤ (windowLength N T 0 s : ℝ) := by
      dsimp [A]
      simpa using storage_windowLength_antitone N T s (Nat.zero_le (r + 1))
    calc
      (∑ j ∈ Finset.range T,
          ((windowLength N T (j + r + 1) s : ℝ) -
            (windowLength N T (j + r + 2) s : ℝ))) =
          ∑ j ∈ Finset.range T, (A j - A (j + 1)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            change
              (windowLength N T (j + r + 1) s : ℝ) -
                  (windowLength N T (j + r + 2) s : ℝ) =
                (windowLength N T (j + r + 1) s : ℝ) -
                  (windowLength N T ((j + 1) + r + 1) s : ℝ)
            rw [show (j + 1) + r + 1 = j + r + 2 by omega]
      _ ≤ A 0 := htel
      _ ≤ (windowLength N T 0 s : ℝ) := hfirst
  calc
    (∑ j ∈ Finset.range T,
        ((windowLength N T (j + 1) s : ℝ) -
          (windowLength N T (j + τ) s : ℝ))) =
        ∑ j ∈ Finset.range T,
          ∑ r ∈ Finset.range (τ - 1),
            ((windowLength N T (j + r + 1) s : ℝ) -
              (windowLength N T (j + r + 2) s : ℝ)) := by
                apply Finset.sum_congr rfl
                intro j _hj
                exact hpoint j
    _ = ∑ r ∈ Finset.range (τ - 1),
          ∑ j ∈ Finset.range T,
            ((windowLength N T (j + r + 1) s : ℝ) -
              (windowLength N T (j + r + 2) s : ℝ)) := by
                rw [Finset.sum_comm]
    _ ≤ ∑ r ∈ Finset.range (τ - 1),
          (windowLength N T 0 s : ℝ) := by
            exact Finset.sum_le_sum fun r _hr => hr r
    _ = (τ - 1 : ℕ) * (windowLength N T 0 s : ℝ) := by
          rw [Finset.sum_const, Finset.card_range]
          simp

/-- Equations (41)--(45): all tagged pulse coordinates, the deterministic gap
coordinate, and the quadratic noise coordinate occur in one finite-dimensional
legal instance.  The residual inequality and its exact absorption condition
are both retained.
Book `#/key_lemmas/4/statement_math`:
“`{\cal E}_T^{I_{s,T}}(s/L)\ge{{\cal B}_T(s)\over6400}+...`”. -/
theorem storage_instance_lower_bound_uniform_in_H
    (N : NetworkSetup n) (L Δ σ : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) :
    ∃ sLoad : ℝ, 0 < sLoad ∧ sLoad ≤ 1 / (64 * n) ∧
      ∀ H : ℝ, 0 ≤ H →
      ∀ (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n),
        s.1 ≤ sLoad →
        ∃ I ∈ fixedInstanceClass N L Δ σ H,
          @initialHeterogeneitySq n I.d I.Ω I.measurableSpace I.setup = 0 ∧
          ENNReal.ofReal
              (ADelta L Δ * windowLength N T.1 0 s.1 / (16 * T.1) +
                σ ^ 2 * s.1 ^ 2 * shiftedWindowInfluenceSum N T s.1 /
                  (800 * T.1)) ≤
            ENNReal.ofReal (FiniteInstance.cost I (s.1 / L) T) ∧
          ENNReal.ofReal
              (comparatorAt N L Δ σ T s / 6400 +
                (windowLength N T.1 0 s.1 / T.1) *
                  (3 * ADelta L Δ / 50 -
                    σ ^ 2 / 800 *
                      (influenceRowBound N ^ 2 * s.1 ^ 2 *
                          (loadingDelay N s.1 - 1) + n * s.1 ^ 4 * T.1))) ≤
            ENNReal.ofReal (FiniteInstance.cost I (s.1 / L) T) ∧
          (σ ^ 2 *
              (influenceRowBound N ^ 2 * s.1 ^ 2 *
                  (loadingDelay N s.1 - 1) + n * s.1 ^ 4 * T.1) ≤
                48 * ADelta L Δ →
            ENNReal.ofReal (comparatorAt N L Δ σ T s / 6400) ≤
              ENNReal.ofReal (FiniteInstance.cost I (s.1 / L) T)) := by
  classical
  obtain ⟨sPulse, hsPulse, hsPulseCap, hcalibrate⟩ :=
    storage_calibrated_pulse_spec N L σ hL hσ
  obtain ⟨sSignal, hsSignal, hsSignalCap, hsignalReference⟩ :=
    deterministic_signal_reference_cap N
  let sLoad : ℝ := min sPulse sSignal
  have hsLoad : 0 < sLoad := lt_min hsPulse hsSignal
  have hsLoadCap : sLoad ≤ 1 / (64 * n) :=
    (min_le_left _ _).trans hsPulseCap
  refine ⟨sLoad, hsLoad, hsLoadCap, ?_⟩
  intro H hH T s hsCap
  have hsPulseUse : s.1 ≤ sPulse := hsCap.trans (min_le_left _ _)
  have hsSignalUse : s.1 ≤ sSignal := hsCap.trans (min_le_right _ _)
  have hsignalBounds := hsignalReference s.1 s.2.1 hsSignalUse
  let signalRadius : ℝ := Real.sqrt (Δ / (2 * L))
  have hsignalRadiusPos : 0 < signalRadius := by
    dsimp [signalRadius]
    exact Real.sqrt_pos.2 (div_pos hΔ (mul_pos (by norm_num) hL))
  have hsignalRadiusSq : signalRadius ^ 2 = Δ / (2 * L) := by
    dsimp [signalRadius]
    exact Real.sq_sqrt (div_nonneg hΔ.le (mul_nonneg (by norm_num) hL.le))
  have hsignalPotential := deterministicGapPotential_setup_spec
    L signalRadius hL hsignalRadiusPos.le
  let Active : Fin T.1 × Fin n → Prop := fun q =>
    q.1.1 + loadingDelay N s.1 < T.1 ∧
      s.1 ≤ |influenceRow N q.1.1 q.2| ∧
      0 < windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1
  let PulseSpec : (Fin T.1 × Fin n) → ℕ → ℕ → ℝ → ℝ → Prop :=
    fun q P Q a e =>
      3 / 4 ≤ a ∧ a ≤ 5 / 4 ∧
      e = -a * σ / (s.1 * influenceRow N q.1.1 q.2) ∧
      q.1.1 + loadingDelay N s.1 ≤ P ∧ P < Q ∧ Q ≤ T.1 ∧
      Q - P = windowLength N T.1
        (q.1.1 + loadingDelay N s.1) s.1 ∧
      3 * σ ≤ |e| ∧
      (∀ t ∈ Finset.Ico P Q,
        L * (σ / L) / 16 ≤
          |negativeCurvatureDerivative L (σ / L)
            (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2 e t)|) ∧
      (∀ t,
        retainedLoadingTracker N L (σ / L) s.1 q.1.1 q.2 e (t + 1) =
          N.colMix t *ᵥ
              retainedLoadingTracker N L (σ / L) s.1 q.1.1 q.2 e t +
            (N.colMix t - 1) *ᵥ
              (fun k => negativeCurvatureDerivative L (σ / L)
                ((loadingTrajectory N L (σ / L) s.1 q.1.1 q.2 e t).primal k) +
                loadingPulse q.1.1 q.2 e t k))
  have hpulse : ∀ q : Fin T.1 × Fin n,
      ∃ P Q : ℕ, ∃ a e : ℝ, Active q → PulseSpec q P Q a e := by
    intro q
    by_cases hq : Active q
    · obtain ⟨P, Q, a, e, ha0, ha1, heq, hP, hPQ, hQT, hlen, he,
          hderiv, htrack⟩ :=
        hcalibrate T.1 s.1 s.2.1 hsPulseUse q.1.1 q.2
          hq.1 hq.2.1 hq.2.2
      exact ⟨P, Q, a, e, fun _ =>
        ⟨ha0, ha1, heq, hP, hPQ, hQT, hlen, he, hderiv, htrack⟩⟩
    · exact ⟨0, 0, 1, 1, fun h => (hq h).elim⟩
  choose pulseStart pulseEnd pulseScale pulseAmplitude hpulseSpec using hpulse
  let pulseProbability : Fin T.1 × Fin n → ℝ := fun q =>
    if Active q then σ ^ 2 / (2 * pulseAmplitude q ^ 2) else 0
  have hpulseLower (q : Fin T.1 × Fin n) (hq : Active q) :
      3 * σ ≤ |pulseAmplitude q| :=
    (hpulseSpec q hq).2.2.2.2.2.2.2.1
  have hpulse_ne (q : Fin T.1 × Fin n) (hq : Active q) :
      pulseAmplitude q ≠ 0 := by
    have habs : 0 < |pulseAmplitude q| :=
      (mul_pos (by norm_num) hσ).trans_le (hpulseLower q hq)
    exact abs_pos.mp habs
  have hp0 : ∀ q, 0 ≤ pulseProbability q := by
    intro q
    by_cases hq : Active q
    · simp only [pulseProbability, if_pos hq]
      positivity
    · simp [pulseProbability, hq]
  have hp1 : ∀ q, pulseProbability q ≤ 1 := by
    intro q
    by_cases hq : Active q
    · simp only [pulseProbability, if_pos hq]
      have heLower := hpulseLower q hq
      have heSq : (3 * σ) ^ 2 ≤ pulseAmplitude q ^ 2 := by
        rw [← sq_abs (pulseAmplitude q)]
        exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).2 heLower
      have hden : 0 < 2 * pulseAmplitude q ^ 2 := by
        exact mul_pos (by norm_num) (sq_pos_of_ne_zero (hpulse_ne q hq))
      apply (div_le_one hden).2
      nlinarith [sq_nonneg σ]
    · simp [pulseProbability, hq]
  have hpulseBudget : ∀ q,
      pulseProbability q * pulseAmplitude q ^ 2 ≤ σ ^ 2 / 2 := by
    intro q
    by_cases hq : Active q
    · simp only [pulseProbability, if_pos hq]
      field_simp [hpulse_ne q hq]
      norm_num
    · simp [pulseProbability, hq]
      positivity
  have hpulseWeightFloor (q : Fin T.1 × Fin n) (hq : Active q) :
      σ ^ 2 * s.1 ^ 2 * influenceRow N q.1.1 q.2 ^ 2 / 800 ≤
        pulseProbability q * (L * (σ / L) / 16) ^ 2 := by
    have ha0 : 3 / 4 ≤ pulseScale q := (hpulseSpec q hq).1
    have ha1 : pulseScale q ≤ 5 / 4 := (hpulseSpec q hq).2.1
    have heq : pulseAmplitude q =
        -pulseScale q * σ / (s.1 * influenceRow N q.1.1 q.2) :=
      (hpulseSpec q hq).2.2.1
    have ha_pos : 0 < pulseScale q := by linarith
    have hb_pos : 0 < |influenceRow N q.1.1 q.2| :=
      s.2.1.trans_le hq.2.1
    have hb_ne : influenceRow N q.1.1 q.2 ≠ 0 := abs_pos.mp hb_pos
    have hidentity :
        (σ ^ 2 / (2 * pulseAmplitude q ^ 2)) *
            (L * (σ / L) / 16) ^ 2 =
          (σ ^ 2 * s.1 ^ 2 * influenceRow N q.1.1 q.2 ^ 2) /
            (512 * pulseScale q ^ 2) := by
      rw [heq]
      field_simp [hL.ne', hσ.ne', s.2.1.ne', hb_ne, ha_pos.ne']
      <;> ring
    simp only [pulseProbability, if_pos hq]
    rw [hidentity]
    have hscaleSq : 512 * pulseScale q ^ 2 ≤ 800 := by
      nlinarith [sq_nonneg (pulseScale q - 5 / 4)]
    have hnum : 0 ≤
        σ ^ 2 * s.1 ^ 2 * influenceRow N q.1.1 q.2 ^ 2 := by positivity
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 800)
      (mul_pos (by norm_num) (sq_pos_of_pos ha_pos))).2
    exact mul_le_mul_of_nonneg_left hscaleSq hnum
  obtain ⟨atom, nu, phi, hnu, hpulseLaw, hphi_storage,
      hphi_storage_coord, hphi_signal_zero, hstochastic⟩ :=
    storage_noise_transform_spec T.1 n σ hσ pulseProbability pulseAmplitude
      hp0 hp1 hpulseBudget
  have hsignalWindowChoice : ∃ P Q : ℕ,
      P ≤ Q ∧ Q ≤ T.1 ∧
      s.1 * ∑ r ∈ Finset.Ico P Q, gain N r ≤ epsilon ∧
      Q - P = windowLength N T.1 0 s.1 := by
    by_cases hW : 0 < windowLength N T.1 0 s.1
    · obtain ⟨P, Q, _h0P, hPQ, hQT, hbudget, hlength⟩ :=
        windowLength_attained N T.1 0 s.1 T.2 hW
      exact ⟨P, Q, hPQ.le, hQT, hbudget, hlength⟩
    · have hW0 : windowLength N T.1 0 s.1 = 0 :=
        Nat.eq_zero_of_not_pos hW
      refine ⟨0, 0, le_rfl, Nat.zero_le _, ?_, ?_⟩
      · norm_num [epsilon]
      · simpa [hW0]
  obtain ⟨signalStart, signalEnd, hsignalPQ, hsignalQT,
      hsignalBudget, hsignalLength⟩ := hsignalWindowChoice
  let signalReference := loadingUnitCenterReferenceOrbit N s.1 0
  let signalInitial : ℝ :=
    signalRadius / (2 * (signalReference signalStart).1)
  have hsignalWindow := deterministic_signal_reference_window_bounds
    N s.1 signalRadius signalStart signalEnd s.2.1 hsignalRadiusPos
      hsignalPQ hsignalBudget hsignalBounds
  have hsignalInitialBound : |signalInitial| ≤ signalRadius := by
    let q0 : Fin n := ⟨0, N.hn⟩
    have hzero := hsignalWindow.1 0 (Nat.zero_le signalEnd) q0
    simpa [signalInitial, signalReference] using hzero
  let quadraticInitial : ℝ :=
    Real.sqrt (Δ / L + signalInitial ^ 2)
  have hquadraticArg : 0 ≤ Δ / L + signalInitial ^ 2 := by
    exact add_nonneg (div_nonneg hΔ.le hL.le) (sq_nonneg signalInitial)
  have hquadraticInitialSq : quadraticInitial ^ 2 =
      Δ / L + signalInitial ^ 2 := by
    dsimp [quadraticInitial]
    exact Real.sq_sqrt hquadraticArg
  have hproductObjective := storage_product_objective_spec
    T.1 n L Δ σ signalRadius signalInitial quadraticInitial
      hL hΔ hσ hsignalRadiusPos hsignalInitialBound
      hsignalRadiusSq hquadraticInitialSq
  let d : ℕ := T.1 * n + 2
  let signalCoord : Fin d := ⟨T.1 * n, by omega⟩
  let quadraticCoord : Fin d := Fin.last (T.1 * n + 1)
  let storageCoord : Fin T.1 × Fin n → Fin d := fun q =>
    Fin.castAdd 2 (finProdFinEquiv q)
  have hstorage_ne_signal (q : Fin T.1 × Fin n) :
      storageCoord q ≠ signalCoord := by
    intro h
    have hv := congrArg (fun x : Fin d => x.val) h
    change (finProdFinEquiv q).val = T.1 * n at hv
    exact (Nat.ne_of_lt (finProdFinEquiv q).isLt) hv
  have hstorage_ne_quadratic (q : Fin T.1 × Fin n) :
      storageCoord q ≠ quadraticCoord := by
    intro h
    have hv := congrArg (fun x : Fin d => x.val) h
    change (finProdFinEquiv q).val = T.1 * n + 1 at hv
    have hlt : (finProdFinEquiv q).val < T.1 * n :=
      (finProdFinEquiv q).isLt
    omega
  let coordinatePotential : Fin d → ℝ → ℝ := fun k x =>
    if k = signalCoord then deterministicGapPotential L signalRadius x
    else if k = quadraticCoord then L * x ^ 2 / 2
    else negativeCurvaturePotential L (σ / L) x
  let coordinateDerivative : Fin d → ℝ → ℝ := fun k x =>
    if k = signalCoord then deterministicGapDerivative L signalRadius x
    else if k = quadraticCoord then L * x
    else negativeCurvatureDerivative L (σ / L) x
  let productObjective : Point d → ℝ := fun z =>
    ∑ k, coordinatePotential k (z k)
  let productInitial : Point d := WithLp.toLp 2 (fun k =>
    if k = signalCoord then signalInitial
    else if k = quadraticCoord then quadraticInitial else 0)
  have hobjective :
      (Differentiable ℝ productObjective ∧
        LipschitzWith ⟨L, hL.le⟩ (gradient productObjective)) ∧
      (∀ z, 0 ≤ productObjective z) ∧
      sInf (Set.range productObjective) = 0 ∧
      productObjective productInitial - sInf (Set.range productObjective) = Δ ∧
      (∀ z, (gradient productObjective z) signalCoord =
        deterministicGapDerivative L signalRadius (z signalCoord)) ∧
      (∀ z, gradient productObjective z =
        WithLp.toLp 2 (fun k => coordinateDerivative k (z k))) := by
    simpa [d, signalCoord, quadraticCoord, coordinatePotential,
      coordinateDerivative, productObjective, productInitial] using
        hproductObjective
  let Label := (Fin T.1 × Fin n) ⊕ Unit
  let Sample := Label → Fin 3
  letI (l : Label) : IsProbabilityMeasure (nu l) := hnu l
  let mu : Measure Sample := Measure.pi nu
  have hmu : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  letI : IsProbabilityMeasure mu := hmu
  let Omega := SOptLib.miniBatchSamplePath n Sample
  let productNoise : ℕ → Omega → NodeTable n d :=
    fun t omega i => phi t i (omega t i)
  let productProbability : Measure Omega :=
    SOptLib.iidMiniBatchSampleLaw n mu
  have hproductProbability : IsProbabilityMeasure productProbability := by
    dsimp [productProbability]
    infer_instance
  let productSetup : Setup n d Omega :=
    { network := N
      hd := by dsimp [d]; omega
      L := L
      Δ := Δ
      σ := σ
      H := H
      hL := hL
      hΔ := hΔ
      hσ := hσ.le
      hH := hH
      localObjective := fun _ => productObjective
      initialPoint := productInitial
      noise := productNoise
      probability := productProbability
      is_probability := hproductProbability
      local_smooth := fun _ => hobjective.1
      average_lower_bounded := by
        refine ⟨0, ?_⟩
        rintro _ ⟨z, rfl⟩
        simpa [productObjective, Nat.ne_of_gt N.hn] using hobjective.2.1 z
      exact_initial_gap := by
        simpa [productObjective, productInitial, Nat.ne_of_gt N.hn] using
          hobjective.2.2.2.1
      noise_centered := by
        simpa [productNoise, productProbability, mu, d, Label, Sample, Omega] using
          hstochastic.1
      noise_second_moment := by
        simpa [productNoise, productProbability, mu, d, Label, Sample, Omega] using
          hstochastic.2.1
      node_conditional_independence := by
        simpa [productNoise, productProbability, mu, d, Label, Sample, Omega] using
          hstochastic.2.2 }
  let omega0 : Omega := fun _t _i _l => 0
  have hproductGradient : ∀ i z,
      (gradient (productSetup.localObjective i) z) signalCoord =
        deterministicGapDerivative L signalRadius (z signalCoord) := by
    intro i z
    simpa [productSetup] using hobjective.2.2.2.2.1 z
  have hproductStorageGradient (i : Fin n) (z : Point d)
      (q : Fin T.1 × Fin n) :
      (gradient (productSetup.localObjective i) z) (storageCoord q) =
        negativeCurvatureDerivative L (σ / L) (z (storageCoord q)) := by
    simp only [productSetup]
    rw [hobjective.2.2.2.2.2 z]
    simp [coordinateDerivative, hstorage_ne_signal q,
      hstorage_ne_quadratic q]
  have hproductStorageNoise (omega : Omega) (q : Fin T.1 × Fin n)
      (t : ℕ) (i : Fin n) :
      (productSetup.noise t omega i) (storageCoord q) =
        loadingPulse q.1.1 q.2
          (atom (Sum.inl q) ((omega t i) (Sum.inl q))) t i := by
    simpa [productSetup, productNoise, storageCoord, d, Label, Sample, Omega]
      using hphi_storage_coord q t i (omega t i)
  have hproductStorageNoiseFixed (omega : Omega) (q : Fin T.1 × Fin n)
      (t : ℕ) (i : Fin n) :
      (productSetup.noise t omega i) (storageCoord q) =
        loadingPulse q.1.1 q.2
          (atom (Sum.inl q)
            ((omega q.1.1 q.2) (Sum.inl q))) t i := by
    rw [hproductStorageNoise]
    unfold loadingPulse
    by_cases hti : t = q.1.1 ∧ i = q.2
    · rcases hti with ⟨rfl, rfl⟩
      rfl
    · simp [hti]
  have hproductSignalNoise : ∀ t i,
      (productSetup.noise t omega0 i) signalCoord = 0 := by
    intro t i
    simpa [productSetup, productNoise, omega0, signalCoord, d, Label, Sample,
      Omega] using hphi_signal_zero t i (omega0 t i)
  have hproductSignalInitial : productSetup.initialPoint signalCoord =
      signalInitial := by
    simp [productSetup, productInitial]
  have hproductStorageInitial (q : Fin T.1 × Fin n) :
      productSetup.initialPoint (storageCoord q) = 0 := by
    simp [productSetup, productInitial, hstorage_ne_signal q,
      hstorage_ne_quadratic q]
  have hevalStorageLeftAct (A : NetworkMatrix n) (Z : NodeTable n d)
      (q : Fin T.1 × Fin n) (i : Fin n) :
      (leftAct A Z i) (storageCoord q) =
        (A *ᵥ (fun k => (Z k) (storageCoord q))) i := by
    simp [leftAct, Matrix.smulVec, Matrix.mulVec, dotProduct]
  have hstorageSampledOracle (omega : Omega) (q : Fin T.1 × Fin n)
      (t : ℕ) (i : Fin n) :
      (sampledOracle productSetup omega (s.1 / L) t i) (storageCoord q) =
        loadingOracle L (σ / L) q.1.1 q.2
          (atom (Sum.inl q) ((omega q.1.1 q.2) (Sum.inl q))) t
          (fun k => (primal productSetup omega (s.1 / L) t k)
            (storageCoord q)) i := by
    rw [sampledOracle_eq_gradient_add_noise]
    simp only [PiLp.add_apply]
    rw [hproductStorageGradient, hproductStorageNoiseFixed]
    rfl
  have hstorageTrajectory (omega : Omega) (q : Fin T.1 × Fin n) :
      ∀ t : ℕ,
        (fun k => (primal productSetup omega (s.1 / L) t k)
            (storageCoord q)) =
            (loadingTrajectory N L (σ / L) s.1 q.1.1 q.2
              (atom (Sum.inl q)
                ((omega q.1.1 q.2) (Sum.inl q))) t).primal ∧
        (fun k => (tracker productSetup omega (s.1 / L) t k)
            (storageCoord q)) =
            (loadingTrajectory N L (σ / L) s.1 q.1.1 q.2
              (atom (Sum.inl q)
                ((omega q.1.1 q.2) (Sum.inl q))) t).tracker := by
    intro t
    induction t with
    | zero =>
        constructor
        · funext k
          exact hproductStorageInitial q
        · funext k
          simp only [tracker, Setup.trajectory, initialState, oracleTable,
            PiLp.add_apply, loadingTrajectory, loadingOracle]
          rw [hproductStorageGradient, hproductStorageInitial,
            hproductStorageNoiseFixed]
          rfl
    | succ t ih =>
        have hprimalNext :
            (fun k => (primal productSetup omega (s.1 / L) (t + 1) k)
                (storageCoord q)) =
              (loadingTrajectory N L (σ / L) s.1 q.1.1 q.2
                (atom (Sum.inl q)
                  ((omega q.1.1 q.2) (Sum.inl q))) (t + 1)).primal := by
          funext k
          rw [primal_succ]
          simp only [Pi.sub_apply, Pi.smul_apply, PiLp.sub_apply,
            PiLp.smul_apply, smul_eq_mul]
          rw [hevalStorageLeftAct]
          simp_rw [congrFun ih.1]
          rw [congrFun ih.2 k]
          rfl
        constructor
        · exact hprimalNext
        · funext k
          rw [tracker_succ]
          simp only [Pi.add_apply, Pi.sub_apply, PiLp.add_apply,
            PiLp.sub_apply]
          rw [hevalStorageLeftAct]
          simp_rw [congrFun ih.2]
          rw [hstorageSampledOracle, hstorageSampledOracle]
          rw [ih.1, hprimalNext]
          rfl
  have hevalStorageSum (Z : Fin n → Point d) (q : Fin T.1 × Fin n) :
      (∑ i, Z i) (storageCoord q) =
        ∑ i, (Z i) (storageCoord q) := by
    let p := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) (storageCoord q)
    change p (∑ i, Z i) = ∑ i, p (Z i)
    exact map_sum p Z Finset.univ
  have hstorageMean (omega : Omega) (q : Fin T.1 × Fin n) (t : ℕ) :
      (arithmeticMean productSetup omega (s.1 / L) t) (storageCoord q) =
        loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
          (atom (Sum.inl q) ((omega q.1.1 q.2) (Sum.inl q))) t := by
    unfold arithmeticMean loadingArithmeticMean
    simp only [PiLp.smul_apply, smul_eq_mul, hevalStorageSum]
    rw [(hstorageTrajectory omega q t).1]
  have htrueSignal := deterministic_signal_true_trajectory_spec
    N productSetup omega0 signalCoord L signalRadius s.1 signalStart signalEnd
      (by rfl) hL hsignalRadiusPos s.2.1 hsignalPQ hsignalBudget
      hsignalBounds hproductGradient hproductSignalNoise
  have htrueSignal' := htrueSignal hproductSignalInitial
  let actualSignalMean : ℕ → ℝ := fun t =>
    (arithmeticMean productSetup omega0 (s.1 / L) t) signalCoord
  have hdeterministicWindow := deterministic_gap_window_sum_lower
    L Δ signalRadius signalStart signalEnd actualSignalMean
      hL hΔ hsignalRadiusPos.le hsignalPQ hsignalRadiusSq (by
        intro t ht
        simpa [actualSignalMean] using htrueSignal'.2 t ht)
  have hdeterministicWindow' :
      L * Δ / 16 * (windowLength N T.1 0 s.1 : ℝ) ≤
        ∑ t ∈ Finset.Ico signalStart signalEnd,
          deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2 := by
    have hcastLength : (windowLength N T.1 0 s.1 : ℝ) =
        (signalEnd : ℝ) - signalStart := by
      rw [← hsignalLength, Nat.cast_sub hsignalPQ]
    rw [hcastLength]
    exact hdeterministicWindow
  have haverageProductObjective : averageObjective productSetup =
      productObjective := by
    funext z
    simp [averageObjective, productSetup, Nat.ne_of_gt N.hn]
  have hstorageAverageGradient (omega : Omega)
      (q : Fin T.1 × Fin n) (t : ℕ) :
      (gradient (averageObjective productSetup)
          (arithmeticMean productSetup omega (s.1 / L) t)) (storageCoord q) =
        negativeCurvatureDerivative L (σ / L)
          (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
            (atom (Sum.inl q) ((omega q.1.1 q.2) (Sum.inl q))) t) := by
    rw [haverageProductObjective, hobjective.2.2.2.2.2]
    simp only [PiLp.toLp_apply]
    rw [hstorageMean]
    simp [coordinateDerivative, hstorage_ne_signal q,
      hstorage_ne_quadratic q]
  have hloadingMeanZero (q : Fin T.1 × Fin n) (t : ℕ) :
      loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2 0 t = 0 := by
    have hneg := (loadingTrajectory_neg N L (σ / L) s.1
      q.1.1 q.2 0 t).1
    simp only [neg_zero] at hneg
    unfold loadingArithmeticMean
    have hx : ∀ k,
        (loadingTrajectory N L (σ / L) s.1 q.1.1 q.2 0 t).primal k = 0 := by
      intro k
      have hk :
          (loadingTrajectory N L (σ / L) s.1 q.1.1 q.2 0 t).primal k =
            -(loadingTrajectory N L (σ / L) s.1 q.1.1 q.2 0 t).primal k := by
        simpa only [Pi.neg_apply] using congrFun hneg k
      linarith
    simp [hx]
  have hloadingMeanNeg (q : Fin T.1 × Fin n) (e : ℝ) (t : ℕ) :
      loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2 (-e) t =
        -loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2 e t := by
    have hneg := (loadingTrajectory_neg N L (σ / L) s.1
      q.1.1 q.2 e t).1
    unfold loadingArithmeticMean
    rw [hneg]
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    ring
  have hstoragePulseLaw (q : Fin T.1 × Fin n) (t : ℕ) :
      (∫ omega : Omega,
          negativeCurvatureDerivative L (σ / L)
              (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
                (atom (Sum.inl q)
                  ((omega q.1.1 q.2) (Sum.inl q))) t) ^ 2
            ∂productSetup.probability) =
        pulseProbability q *
          negativeCurvatureDerivative L (σ / L)
              (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
                (pulseAmplitude q) t) ^ 2 := by
    let F : ℝ → ℝ := fun e =>
      negativeCurvatureDerivative L (σ / L)
          (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2 e t) ^ 2
    have hF0 : F 0 = 0 := by
      simp [F, hloadingMeanZero, negativeCurvatureDerivative_zero]
    have hFeven : F (-(pulseAmplitude q)) = F (pulseAmplitude q) := by
      simp only [F, hloadingMeanNeg, negativeCurvatureDerivative_neg]
      ring
    have hevalMeas : Measurable (fun omega : Omega => omega q.1.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1.1)
    have hmap : Measure.map (fun omega : Omega => omega q.1.1 q.2)
        productSetup.probability = mu := by
      simpa [productSetup, productProbability, Omega] using
        (SOptLib.iidMiniBatchSampleLaw_map_eval n mu q.1.1 q.2)
    have hFint : Integrable
        (fun z : Sample => F (atom (Sum.inl q) (z (Sum.inl q)))) mu :=
      Integrable.of_finite
    have hFintMap : Integrable
        (fun z : Sample => F (atom (Sum.inl q) (z (Sum.inl q))))
        (Measure.map (fun omega : Omega => omega q.1.1 q.2)
          productSetup.probability) := by
      rw [hmap]
      exact hFint
    change (∫ omega : Omega,
        F (atom (Sum.inl q) ((omega q.1.1 q.2) (Sum.inl q)))
          ∂productSetup.probability) =
      pulseProbability q * F (pulseAmplitude q)
    calc
      (∫ omega : Omega,
          F (atom (Sum.inl q) ((omega q.1.1 q.2) (Sum.inl q)))
            ∂productSetup.probability) =
          ∫ z : Sample, F (atom (Sum.inl q) (z (Sum.inl q))) ∂mu := by
        simpa [Function.comp_def] using
          (integral_comp_eq_integral_of_map_eq hevalMeas.aemeasurable
            hFintMap.aestronglyMeasurable hmap)
      _ = pulseProbability q * F (pulseAmplitude q) :=
        hpulseLaw q F hF0 hFeven
  have hstoragePulseExpectationLower (q : Fin T.1 × Fin n)
      (hq : Active q) (t : ℕ)
      (ht : t ∈ Finset.Ico (pulseStart q) (pulseEnd q)) :
      σ ^ 2 * s.1 ^ 2 * influenceRow N q.1.1 q.2 ^ 2 / 800 ≤
        ∫ omega : Omega,
          ((gradient (averageObjective productSetup)
              (arithmeticMean productSetup omega (s.1 / L) t))
                (storageCoord q)) ^ 2 ∂productSetup.probability := by
    obtain ⟨_ha0, _ha1, _heq, _hP, _hPQ, _hQT, _hlen, _heLower,
      hderiv, _htrack⟩ := hpulseSpec q hq
    have hderivSq : (L * (σ / L) / 16) ^ 2 ≤
        negativeCurvatureDerivative L (σ / L)
            (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
              (pulseAmplitude q) t) ^ 2 := by
      have hbase : 0 ≤ L * (σ / L) / 16 := by positivity
      rw [← sq_abs (L * (σ / L) / 16),
        ← sq_abs (negativeCurvatureDerivative L (σ / L)
          (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
            (pulseAmplitude q) t)), abs_of_nonneg hbase]
      exact (sq_le_sq₀ hbase (abs_nonneg _)).2 (hderiv t ht)
    calc
      σ ^ 2 * s.1 ^ 2 * influenceRow N q.1.1 q.2 ^ 2 / 800 ≤
          pulseProbability q * (L * (σ / L) / 16) ^ 2 :=
        hpulseWeightFloor q hq
      _ ≤ pulseProbability q *
          negativeCurvatureDerivative L (σ / L)
              (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
                (pulseAmplitude q) t) ^ 2 :=
        mul_le_mul_of_nonneg_left hderivSq (hp0 q)
      _ = ∫ omega : Omega,
          negativeCurvatureDerivative L (σ / L)
              (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
                (atom (Sum.inl q)
                  ((omega q.1.1 q.2) (Sum.inl q))) t) ^ 2
            ∂productSetup.probability := (hstoragePulseLaw q t).symm
      _ = ∫ omega : Omega,
          ((gradient (averageObjective productSetup)
              (arithmeticMean productSetup omega (s.1 / L) t))
                (storageCoord q)) ^ 2 ∂productSetup.probability := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => by
          exact congrArg (fun x : ℝ => x ^ 2)
            (hstorageAverageGradient omega q t).symm
  have hproductHeterogeneity : initialHeterogeneitySq productSetup = 0 := by
    unfold initialHeterogeneitySq
    simp only [productSetup, haverageProductObjective, sub_self, norm_zero,
      zero_pow, Nat.ofNat_pos, Finset.sum_const_zero, mul_zero]
    simp
  have hproductFiniteLayer : InFiniteHeterogeneityLayer productSetup := by
    unfold InFiniteHeterogeneityLayer
    rw [hproductHeterogeneity]
    exact sq_nonneg H
  let productInstance : FiniteInstance n :=
    { d := d
      Ω := Omega
      setup := productSetup
      finite_layer := hproductFiniteLayer }
  have hproductFixed : productInstance ∈ fixedInstanceClass N L Δ σ H := by
    simp [fixedInstanceClass, productInstance, productSetup,
      FiniteInstance.network, FiniteInstance.lipschitz, FiniteInstance.gap,
      FiniteInstance.noiseScale, FiniteInstance.heterogeneityScale]
  have htrueSignalAll (omega : Omega) :=
    (deterministic_signal_true_trajectory_spec
      N productSetup omega signalCoord L signalRadius s.1 signalStart signalEnd
        (by rfl) hL hsignalRadiusPos s.2.1 hsignalPQ hsignalBudget
        hsignalBounds hproductGradient (by
          intro t i
          simpa [productSetup, productNoise, signalCoord, d, Label, Sample,
            Omega] using hphi_signal_zero t i (omega t i)))
      hproductSignalInitial
  have hevalSignalSum (Z : Fin n → Point d) :
      (∑ i, Z i) signalCoord = ∑ i, (Z i) signalCoord := by
    let p := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) signalCoord
    change p (∑ i, Z i) = ∑ i, p (Z i)
    exact map_sum p Z Finset.univ
  have hsignalMeanAll (omega : Omega) (t : ℕ) (ht : t ≤ signalEnd) :
      (arithmeticMean productSetup omega (s.1 / L) t) signalCoord =
        actualSignalMean t := by
    unfold arithmeticMean
    simp only [PiLp.smul_apply, smul_eq_mul, hevalSignalSum]
    dsimp only [actualSignalMean]
    unfold arithmeticMean
    simp only [PiLp.smul_apply, smul_eq_mul, hevalSignalSum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    rw [(htrueSignalAll omega).1 t ht i,
      htrueSignal'.1 t ht i]
  have hstationaritySignalPointwise (omega : Omega) (t : ℕ) :
      deterministicGapDerivative L signalRadius
          ((arithmeticMean productSetup omega (s.1 / L) t) signalCoord) ^ 2 ≤
        stationarityIntegrand productSetup (s.1 / L) t omega := by
    let G := gradient (averageObjective productSetup)
      (arithmeticMean productSetup omega (s.1 / L) t)
    have hcoord : G signalCoord = deterministicGapDerivative L signalRadius
        ((arithmeticMean productSetup omega (s.1 / L) t) signalCoord) := by
      dsimp [G]
      rw [haverageProductObjective]
      exact hobjective.2.2.2.2.1 _
    have hnorm : ‖G signalCoord‖ ≤ ‖G‖ := PiLp.norm_apply_le G signalCoord
    have hsquare : ‖G signalCoord‖ ^ 2 ≤ ‖G‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
    unfold stationarityIntegrand
    rw [hcoord, Real.norm_eq_abs, sq_abs] at hsquare
    exact hsquare
  have hstorageCoordInjective : Function.Injective storageCoord := by
    intro q r hqr
    apply finProdFinEquiv.injective
    have hv := congrArg (fun x : Fin d => x.val) hqr
    exact Fin.ext hv
  have hstationaritySignalStoragePointwise (omega : Omega) (t : ℕ) :
      deterministicGapDerivative L signalRadius
          ((arithmeticMean productSetup omega (s.1 / L) t) signalCoord) ^ 2 +
        ∑ q : Fin T.1 × Fin n,
          ((gradient (averageObjective productSetup)
              (arithmeticMean productSetup omega (s.1 / L) t))
                (storageCoord q)) ^ 2 ≤
        stationarityIntegrand productSetup (s.1 / L) t omega := by
    let G := gradient (averageObjective productSetup)
      (arithmeticMean productSetup omega (s.1 / L) t)
    let storageSet : Finset (Fin d) := Finset.univ.image storageCoord
    let selected : Finset (Fin d) := storageSet ∪ {signalCoord}
    have hsignal : G signalCoord = deterministicGapDerivative L signalRadius
        ((arithmeticMean productSetup omega (s.1 / L) t) signalCoord) := by
      dsimp [G]
      rw [haverageProductObjective]
      exact hobjective.2.2.2.2.1 _
    have hdisjoint : Disjoint storageSet ({signalCoord} : Finset (Fin d)) := by
      rw [Finset.disjoint_singleton_right]
      simp [storageSet, hstorage_ne_signal]
    have himage :
        (∑ k ∈ storageSet, ‖G k‖ ^ 2) =
          ∑ q : Fin T.1 × Fin n, ‖G (storageCoord q)‖ ^ 2 := by
      dsimp [storageSet]
      rw [Finset.sum_image]
      exact fun q _ r _ h => hstorageCoordInjective h
    have hselected :
        (∑ k ∈ selected, ‖G k‖ ^ 2) =
          ‖G signalCoord‖ ^ 2 +
            ∑ q : Fin T.1 × Fin n, ‖G (storageCoord q)‖ ^ 2 := by
      dsimp [selected]
      rw [Finset.sum_union hdisjoint]
      simp only [Real.norm_eq_abs] at himage ⊢
      rw [himage]
      simp
      ring
    have hsubset : selected ⊆ Finset.univ := by
      intro k _hk
      simp
    have hsumle : (∑ k ∈ selected, ‖G k‖ ^ 2) ≤
        ∑ k : Fin d, ‖G k‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _hk _hnot => sq_nonneg ‖G k‖)
    rw [hselected] at hsumle
    unfold stationarityIntegrand
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [G, hsignal, Real.norm_eq_abs, sq_abs] using hsumle
  have hstorageGradientSqIntegrable (q : Fin T.1 × Fin n) (t : ℕ) :
      Integrable (fun omega : Omega =>
        ((gradient (averageObjective productSetup)
            (arithmeticMean productSetup omega (s.1 / L) t))
              (storageCoord q)) ^ 2) productSetup.probability := by
    let f : Sample → ℝ := fun z =>
      negativeCurvatureDerivative L (σ / L)
          (loadingArithmeticMean N L (σ / L) s.1 q.1.1 q.2
            (atom (Sum.inl q) (z (Sum.inl q))) t) ^ 2
    have hevalMeas : Measurable (fun omega : Omega => omega q.1.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1.1)
    have hmap : Measure.map (fun omega : Omega => omega q.1.1 q.2)
        productSetup.probability = mu := by
      simpa [productSetup, productProbability, Omega] using
        (SOptLib.iidMiniBatchSampleLaw_map_eval n mu q.1.1 q.2)
    have hfMap : Integrable f
        (Measure.map (fun omega : Omega => omega q.1.1 q.2)
          productSetup.probability) := by
      rw [hmap]
      exact Integrable.of_finite
    have hpull : Integrable (fun omega : Omega => f (omega q.1.1 q.2))
        productSetup.probability := by
      simpa [Function.comp_def] using hfMap.comp_measurable hevalMeas
    apply hpull.congr
    exact Filter.Eventually.of_forall fun omega => by
      exact congrArg (fun x : ℝ => x ^ 2)
        (hstorageAverageGradient omega q t).symm
  have hsignalStorageExpectation (t : ℕ) (ht : t ≤ signalEnd) :
      deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2 +
          ∑ q : Fin T.1 × Fin n,
            ∫ omega : Omega,
              ((gradient (averageObjective productSetup)
                  (arithmeticMean productSetup omega (s.1 / L) t))
                    (storageCoord q)) ^ 2 ∂productSetup.probability ≤
        SOptLib.expectation productSetup.probability
          (stationarityIntegrand productSetup (s.1 / L) t) := by
    let signalSq : Omega → ℝ := fun omega =>
      deterministicGapDerivative L signalRadius
          ((arithmeticMean productSetup omega (s.1 / L) t) signalCoord) ^ 2
    let storageSq : (Fin T.1 × Fin n) → Omega → ℝ := fun q omega =>
      ((gradient (averageObjective productSetup)
          (arithmeticMean productSetup omega (s.1 / L) t))
            (storageCoord q)) ^ 2
    have hsignalInt : Integrable signalSq productSetup.probability := by
      have heq : signalSq = fun _ : Omega =>
          deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2 := by
        funext omega
        simp only [signalSq]
        rw [hsignalMeanAll omega t ht]
      rw [heq]
      exact integrable_const _
    have hstorageInt : ∀ q, Integrable (storageSq q) productSetup.probability := by
      intro q
      exact hstorageGradientSqIntegrable q t
    have hcombinedInt : Integrable
        (fun omega => signalSq omega + ∑ q, storageSq q omega)
        productSetup.probability :=
      hsignalInt.add (integrable_finset_sum _ fun q _hq => hstorageInt q)
    unfold SOptLib.expectation
    calc
      deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2 +
            ∑ q : Fin T.1 × Fin n, ∫ omega, storageSq q omega
                ∂productSetup.probability =
          ∫ omega, signalSq omega + ∑ q, storageSq q omega
            ∂productSetup.probability := by
        rw [integral_add hsignalInt
          (integrable_finset_sum _ fun q _hq => hstorageInt q),
          integral_finset_sum _ fun q _hq => hstorageInt q]
        simp only [signalSq]
        rw [show (fun omega : Omega =>
            deterministicGapDerivative L signalRadius
                ((arithmeticMean productSetup omega (s.1 / L) t) signalCoord) ^ 2) =
              fun _ => deterministicGapDerivative L signalRadius
                (actualSignalMean t) ^ 2 by
          funext omega
          rw [hsignalMeanAll omega t ht]]
        simp [productSetup]
      _ ≤ ∫ omega,
          stationarityIntegrand productSetup (s.1 / L) t omega
            ∂productSetup.probability := by
        apply MeasureTheory.integral_mono hcombinedInt
          (stationarityIntegrand_integrable productSetup (s.1 / L) t)
        intro omega
        exact hstationaritySignalStoragePointwise omega t
  have hstorageWindowSumLower (q : Fin T.1 × Fin n) :
      (σ ^ 2 * s.1 ^ 2 / 800) *
          (if s.1 ≤ |influenceRow N q.1.1 q.2| then
            influenceRow N q.1.1 q.2 ^ 2 *
              windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1
          else 0) ≤
        ∑ t ∈ Finset.range T.1,
          ∫ omega : Omega,
            ((gradient (averageObjective productSetup)
                (arithmeticMean productSetup omega (s.1 / L) t))
                  (storageCoord q)) ^ 2 ∂productSetup.probability := by
    let E : ℕ → ℝ := fun t =>
      ∫ omega : Omega,
        ((gradient (averageObjective productSetup)
            (arithmeticMean productSetup omega (s.1 / L) t))
              (storageCoord q)) ^ 2 ∂productSetup.probability
    have hEnonneg : ∀ t, 0 ≤ E t := by
      intro t
      apply integral_nonneg
      intro omega
      exact sq_nonneg _
    by_cases hq : Active q
    · have hthreshold : s.1 ≤ |influenceRow N q.1.1 q.2| := hq.2.1
      obtain ⟨_ha0, _ha1, _heq, _hP, hPQ, hQT, hlen, _heLower,
        _hderiv, _htrack⟩ := hpulseSpec q hq
      have hlocal :
          ∑ t ∈ Finset.Ico (pulseStart q) (pulseEnd q),
              (σ ^ 2 * s.1 ^ 2 * influenceRow N q.1.1 q.2 ^ 2 / 800) ≤
            ∑ t ∈ Finset.Ico (pulseStart q) (pulseEnd q), E t := by
        exact Finset.sum_le_sum fun t ht =>
          hstoragePulseExpectationLower q hq t ht
      have hleft :
          ∑ t ∈ Finset.Ico (pulseStart q) (pulseEnd q),
              (σ ^ 2 * s.1 ^ 2 * influenceRow N q.1.1 q.2 ^ 2 / 800) =
            (σ ^ 2 * s.1 ^ 2 / 800) *
              (influenceRow N q.1.1 q.2 ^ 2 *
                windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1) := by
        rw [Finset.sum_const, Nat.card_Ico, hlen]
        push_cast
        ring
      have hsubset : Finset.Ico (pulseStart q) (pulseEnd q) ⊆
          Finset.range T.1 := by
        intro t ht
        rw [Finset.mem_range]
        exact (Finset.mem_Ico.mp ht).2.trans_le hQT
      simp only [if_pos hthreshold]
      rw [← hleft]
      exact hlocal.trans (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun t _ht _hnot => hEnonneg t))
    · have htermZero :
          (if s.1 ≤ |influenceRow N q.1.1 q.2| then
            influenceRow N q.1.1 q.2 ^ 2 *
              windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1
          else 0) = 0 := by
        by_cases hthreshold : s.1 ≤ |influenceRow N q.1.1 q.2|
        · have hWzero :
              windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1 = 0 := by
            by_cases hj : q.1.1 + loadingDelay N s.1 < T.1
            · by_contra hW
              exact hq ⟨hj, hthreshold, Nat.pos_of_ne_zero hW⟩
            · simp [windowLength, hj]
          simp [hthreshold, hWzero]
        · simp [hthreshold]
      rw [htermZero, mul_zero]
      exact Finset.sum_nonneg fun t _ht => hEnonneg t
  have hshiftedAsProductSum : shiftedWindowInfluenceSum N T s.1 =
      ∑ q : Fin T.1 × Fin n,
        if s.1 ≤ |influenceRow N q.1.1 q.2| then
          influenceRow N q.1.1 q.2 ^ 2 *
            windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1
        else 0 := by
    unfold shiftedWindowInfluenceSum
    calc
      (∑ j ∈ Finset.range T.1,
          ∑ i : Fin n,
            if s.1 ≤ |influenceRow N j i| then
              influenceRow N j i ^ 2 *
                windowLength N T.1 (j + loadingDelay N s.1) s.1
            else 0) =
          ∑ j ∈ Finset.range T.1,
            if h : j < T.1 then
              ∑ i : Fin n,
                if s.1 ≤ |influenceRow N (⟨j, h⟩ : Fin T.1).1 i| then
                  influenceRow N (⟨j, h⟩ : Fin T.1).1 i ^ 2 *
                    windowLength N T.1
                      ((⟨j, h⟩ : Fin T.1).1 + loadingDelay N s.1) s.1
                else 0
            else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [dif_pos (Finset.mem_range.mp hj)]
      _ = ∑ j : Fin T.1,
            ∑ i : Fin n,
              if s.1 ≤ |influenceRow N j.1 i| then
                influenceRow N j.1 i ^ 2 *
                  windowLength N T.1 (j.1 + loadingDelay N s.1) s.1
              else 0 :=
        (Finset.sum_fin_eq_sum_range
          (fun j : Fin T.1 =>
            ∑ i : Fin n,
              if s.1 ≤ |influenceRow N j.1 i| then
                influenceRow N j.1 i ^ 2 *
                  windowLength N T.1 (j.1 + loadingDelay N s.1) s.1
              else 0)).symm
      _ = ∑ q : Fin T.1 × Fin n,
            if s.1 ≤ |influenceRow N q.1.1 q.2| then
              influenceRow N q.1.1 q.2 ^ 2 *
                windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1
            else 0 := by rw [Fintype.sum_prod_type]
  have hstorageAllWindowsLower :
      (σ ^ 2 * s.1 ^ 2 / 800) * shiftedWindowInfluenceSum N T s.1 ≤
        ∑ t ∈ Finset.range T.1,
          ∑ q : Fin T.1 × Fin n,
            ∫ omega : Omega,
              ((gradient (averageObjective productSetup)
                  (arithmeticMean productSetup omega (s.1 / L) t))
                    (storageCoord q)) ^ 2 ∂productSetup.probability := by
    have hsum := Finset.sum_le_sum
      (fun q (_hq : q ∈ (Finset.univ : Finset (Fin T.1 × Fin n))) =>
        hstorageWindowSumLower q)
    calc
      (σ ^ 2 * s.1 ^ 2 / 800) * shiftedWindowInfluenceSum N T s.1 =
          ∑ q : Fin T.1 × Fin n,
            (σ ^ 2 * s.1 ^ 2 / 800) *
              (if s.1 ≤ |influenceRow N q.1.1 q.2| then
                influenceRow N q.1.1 q.2 ^ 2 *
                  windowLength N T.1 (q.1.1 + loadingDelay N s.1) s.1
              else 0) := by
        rw [hshiftedAsProductSum, Finset.mul_sum]
      _ ≤ ∑ q : Fin T.1 × Fin n,
          ∑ t ∈ Finset.range T.1,
            ∫ omega : Omega,
              ((gradient (averageObjective productSetup)
                  (arithmeticMean productSetup omega (s.1 / L) t))
                    (storageCoord q)) ^ 2 ∂productSetup.probability := hsum
      _ = ∑ t ∈ Finset.range T.1,
          ∑ q : Fin T.1 × Fin n,
            ∫ omega : Omega,
              ((gradient (averageObjective productSetup)
                  (arithmeticMean productSetup omega (s.1 / L) t))
                    (storageCoord q)) ^ 2 ∂productSetup.probability := by
        rw [Finset.sum_comm]
  have hstorageExpectation (t : ℕ) :
      (∑ q : Fin T.1 × Fin n,
          ∫ omega : Omega,
            ((gradient (averageObjective productSetup)
                (arithmeticMean productSetup omega (s.1 / L) t))
                  (storageCoord q)) ^ 2 ∂productSetup.probability) ≤
        SOptLib.expectation productSetup.probability
          (stationarityIntegrand productSetup (s.1 / L) t) := by
    let storageSq : (Fin T.1 × Fin n) → Omega → ℝ := fun q omega =>
      ((gradient (averageObjective productSetup)
          (arithmeticMean productSetup omega (s.1 / L) t))
            (storageCoord q)) ^ 2
    have hstorageInt : ∀ q, Integrable (storageSq q) productSetup.probability := by
      intro q
      exact hstorageGradientSqIntegrable q t
    unfold SOptLib.expectation
    rw [← integral_finset_sum _ fun q _hq => hstorageInt q]
    apply MeasureTheory.integral_mono
      (integrable_finset_sum _ fun q _hq => hstorageInt q)
      (stationarityIntegrand_integrable productSetup (s.1 / L) t)
    intro omega
    have hpoint := hstationaritySignalStoragePointwise omega t
    dsimp only [storageSq]
    nlinarith [sq_nonneg (deterministicGapDerivative L signalRadius
      ((arithmeticMean productSetup omega (s.1 / L) t) signalCoord))]
  have hsignalStorageHorizon :
      (∑ t ∈ Finset.Ico signalStart signalEnd,
          deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2) +
          ∑ t ∈ Finset.range T.1,
            ∑ q : Fin T.1 × Fin n,
              ∫ omega : Omega,
                ((gradient (averageObjective productSetup)
                    (arithmeticMean productSetup omega (s.1 / L) t))
                      (storageCoord q)) ^ 2 ∂productSetup.probability ≤
        ∑ t ∈ Finset.range T.1,
          SOptLib.expectation productSetup.probability
            (stationarityIntegrand productSetup (s.1 / L) t) := by
    let signalSq : ℕ → ℝ := fun t =>
      deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2
    let storageSq : ℕ → ℝ := fun t =>
      ∑ q : Fin T.1 × Fin n,
        ∫ omega : Omega,
          ((gradient (averageObjective productSetup)
              (arithmeticMean productSetup omega (s.1 / L) t))
                (storageCoord q)) ^ 2 ∂productSetup.probability
    have hwindowSubset : Finset.Ico signalStart signalEnd ⊆
        Finset.range T.1 := by
      intro t ht
      rw [Finset.mem_range]
      exact (Finset.mem_Ico.mp ht).2.trans_le hsignalQT
    have hindicator :
        (∑ t ∈ Finset.range T.1,
            if t ∈ Finset.Ico signalStart signalEnd then signalSq t else 0) =
          ∑ t ∈ Finset.Ico signalStart signalEnd, signalSq t := by
      symm
      calc
        (∑ t ∈ Finset.Ico signalStart signalEnd, signalSq t) =
            ∑ t ∈ Finset.Ico signalStart signalEnd,
              if t ∈ Finset.Ico signalStart signalEnd then signalSq t else 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          simp [ht]
        _ = ∑ t ∈ Finset.range T.1,
              if t ∈ Finset.Ico signalStart signalEnd then signalSq t else 0 := by
          apply Finset.sum_subset hwindowSubset
          intro t _htRange htNot
          simp [htNot]
    calc
      (∑ t ∈ Finset.Ico signalStart signalEnd,
          deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2) +
          ∑ t ∈ Finset.range T.1,
            ∑ q : Fin T.1 × Fin n,
              ∫ omega : Omega,
                ((gradient (averageObjective productSetup)
                    (arithmeticMean productSetup omega (s.1 / L) t))
                      (storageCoord q)) ^ 2 ∂productSetup.probability =
          ∑ t ∈ Finset.range T.1,
            ((if t ∈ Finset.Ico signalStart signalEnd then signalSq t else 0) +
              storageSq t) := by
        rw [Finset.sum_add_distrib, hindicator]
      _ ≤ ∑ t ∈ Finset.range T.1,
          SOptLib.expectation productSetup.probability
            (stationarityIntegrand productSetup (s.1 / L) t) := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases htWindow : t ∈ Finset.Ico signalStart signalEnd
        · simp only [if_pos htWindow]
          dsimp only [signalSq, storageSq]
          exact hsignalStorageExpectation t (Finset.mem_Ico.mp htWindow).2.le
        · simp only [if_neg htWindow, zero_add]
          dsimp only [storageSq]
          exact hstorageExpectation t
  have hsignalStorageNumerator :
      L * Δ / 16 * (windowLength N T.1 0 s.1 : ℝ) +
          (σ ^ 2 * s.1 ^ 2 / 800) * shiftedWindowInfluenceSum N T s.1 ≤
        ∑ t ∈ Finset.range T.1,
          SOptLib.expectation productSetup.probability
            (stationarityIntegrand productSetup (s.1 / L) t) := by
    exact (add_le_add hdeterministicWindow' hstorageAllWindowsLower).trans
      hsignalStorageHorizon
  have hequation42 :
      ADelta L Δ * (windowLength N T.1 0 s.1 : ℝ) / (16 * T.1) +
          σ ^ 2 * s.1 ^ 2 * shiftedWindowInfluenceSum N T s.1 /
            (800 * T.1) ≤
        FiniteInstance.cost productInstance (s.1 / L) T := by
    have hTpos : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
    change ADelta L Δ * (windowLength N T.1 0 s.1 : ℝ) / (16 * T.1) +
        σ ^ 2 * s.1 ^ 2 * shiftedWindowInfluenceSum N T s.1 /
          (800 * T.1) ≤ stationarityError productSetup (s.1 / L) T
    unfold stationarityError
    calc
      ADelta L Δ * (windowLength N T.1 0 s.1 : ℝ) / (16 * T.1) +
            σ ^ 2 * s.1 ^ 2 * shiftedWindowInfluenceSum N T s.1 /
              (800 * T.1) =
          (T.1 : ℝ)⁻¹ *
            (L * Δ / 16 * (windowLength N T.1 0 s.1 : ℝ) +
              (σ ^ 2 * s.1 ^ 2 / 800) * shiftedWindowInfluenceSum N T s.1) := by
                unfold ADelta
                field_simp [ne_of_gt hTpos]
                <;> ring
      _ ≤ (T.1 : ℝ)⁻¹ *
          ∑ t ∈ Finset.range T.1,
            SOptLib.expectation productSetup.probability
              (stationarityIntegrand productSetup (s.1 / L) t) := by
        exact mul_le_mul_of_nonneg_left hsignalStorageNumerator
          (inv_nonneg.mpr hTpos.le)
  have hloadingDelayOne : 1 ≤ loadingDelay N s.1 := by
    unfold loadingDelay
    omega
  have hrowEnergyLe (j : ℕ) :
      influenceEnergy N j ≤ influenceRowBound N ^ 2 := by
    have hnormsq : nodeL2Norm (influenceRow N j) ^ 2 =
        influenceEnergy N j := by
      unfold nodeL2Norm influenceEnergy
      rw [Real.sq_sqrt]
      exact Finset.sum_nonneg fun i _hi => sq_nonneg (influenceRow N j i)
    have hnormnonneg : 0 ≤ nodeL2Norm (influenceRow N j) := by
      unfold nodeL2Norm
      positivity
    have hnormle := influenceRow_nodeL2_le N j
    rw [← hnormsq]
    nlinarith
  have hrowWindowLoss (j : ℕ) :
      influenceEnergy N j * (windowLength N T.1 (j + 1) s.1 : ℝ) -
          (∑ i : Fin n,
            if s.1 ≤ |influenceRow N j i| then
              influenceRow N j i ^ 2 *
                (windowLength N T.1 (j + loadingDelay N s.1) s.1 : ℝ)
            else 0) ≤
        influenceRowBound N ^ 2 *
            ((windowLength N T.1 (j + 1) s.1 : ℝ) -
              (windowLength N T.1 (j + loadingDelay N s.1) s.1 : ℝ)) +
          (n : ℝ) * s.1 ^ 2 * (windowLength N T.1 0 s.1 : ℝ) := by
    let W1 : ℝ := windowLength N T.1 (j + 1) s.1
    let Wτ : ℝ := windowLength N T.1 (j + loadingDelay N s.1) s.1
    let W0 : ℝ := windowLength N T.1 0 s.1
    have hindex : j + 1 ≤ j + loadingDelay N s.1 :=
      Nat.add_le_add_left hloadingDelayOne j
    have hWmonoNat := storage_windowLength_antitone N T.1 s.1 hindex
    have hWmono : Wτ ≤ W1 := by
      simpa [Wτ, W1] using hWmonoNat
    have hW1zeroNat := storage_windowLength_antitone N T.1 s.1
      (Nat.zero_le (j + 1))
    have hW1zero : W1 ≤ W0 := by
      simpa [W1, W0] using hW1zeroNat
    have hW1nonneg : 0 ≤ W1 := by
      dsimp [W1]
      positivity
    have hdiff : 0 ≤ W1 - Wτ := sub_nonneg.mpr hWmono
    have hpoint (i : Fin n) :
        influenceRow N j i ^ 2 * W1 -
            (if s.1 ≤ |influenceRow N j i| then
              influenceRow N j i ^ 2 * Wτ else 0) ≤
          influenceRow N j i ^ 2 * (W1 - Wτ) + s.1 ^ 2 * W0 := by
      by_cases hi : s.1 ≤ |influenceRow N j i|
      · rw [if_pos hi]
        have hconst : 0 ≤ s.1 ^ 2 * W0 := by positivity
        nlinarith
      · rw [if_neg hi, sub_zero]
        have habs : |influenceRow N j i| < s.1 := lt_of_not_ge hi
        have hb2 : influenceRow N j i ^ 2 ≤ s.1 ^ 2 := by
          have hprod : 0 <
              (s.1 - |influenceRow N j i|) *
                (s.1 + |influenceRow N j i|) :=
            mul_pos (sub_pos.mpr habs)
              (add_pos_of_pos_of_nonneg s.2.1 (abs_nonneg _))
          nlinarith [sq_abs (influenceRow N j i)]
        calc
          influenceRow N j i ^ 2 * W1 ≤ s.1 ^ 2 * W1 :=
            mul_le_mul_of_nonneg_right hb2 hW1nonneg
          _ ≤ s.1 ^ 2 * W0 :=
            mul_le_mul_of_nonneg_left hW1zero (sq_nonneg s.1)
          _ ≤ influenceRow N j i ^ 2 * (W1 - Wτ) + s.1 ^ 2 * W0 := by
            exact le_add_of_nonneg_left
              (mul_nonneg (sq_nonneg (influenceRow N j i)) hdiff)
    change influenceEnergy N j * W1 -
        ∑ i : Fin n,
          (if s.1 ≤ |influenceRow N j i| then
            influenceRow N j i ^ 2 * Wτ else 0) ≤
      influenceRowBound N ^ 2 * (W1 - Wτ) + (n : ℝ) * s.1 ^ 2 * W0
    rw [influenceEnergy, Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc
      (∑ i : Fin n,
          (influenceRow N j i ^ 2 * W1 -
            if s.1 ≤ |influenceRow N j i| then
              influenceRow N j i ^ 2 * Wτ else 0)) ≤
          ∑ i : Fin n,
            (influenceRow N j i ^ 2 * (W1 - Wτ) + s.1 ^ 2 * W0) := by
              exact Finset.sum_le_sum fun i _hi => hpoint i
      _ = influenceEnergy N j * (W1 - Wτ) +
          (n : ℝ) * s.1 ^ 2 * W0 := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            unfold influenceEnergy
            ring
      _ ≤ influenceRowBound N ^ 2 * (W1 - Wτ) +
          (n : ℝ) * s.1 ^ 2 * W0 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right (hrowEnergyLe j) hdiff) le_rfl
  have htotalWindowLoss :
      windowInfluenceSum N T.1 s.1 - shiftedWindowInfluenceSum N T s.1 ≤
        influenceRowBound N ^ 2 *
            (∑ j ∈ Finset.range T.1,
              ((windowLength N T.1 (j + 1) s.1 : ℝ) -
                (windowLength N T.1 (j + loadingDelay N s.1) s.1 : ℝ))) +
          (n : ℝ) * s.1 ^ 2 * T.1 *
            (windowLength N T.1 0 s.1 : ℝ) := by
    unfold windowInfluenceSum shiftedWindowInfluenceSum
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ j ∈ Finset.range T.1,
          (influenceEnergy N j * (windowLength N T.1 (j + 1) s.1 : ℝ) -
            ∑ i : Fin n,
              if s.1 ≤ |influenceRow N j i| then
                influenceRow N j i ^ 2 *
                  (windowLength N T.1 (j + loadingDelay N s.1) s.1 : ℝ)
              else 0)) ≤
          ∑ j ∈ Finset.range T.1,
            (influenceRowBound N ^ 2 *
                ((windowLength N T.1 (j + 1) s.1 : ℝ) -
                  (windowLength N T.1 (j + loadingDelay N s.1) s.1 : ℝ)) +
              (n : ℝ) * s.1 ^ 2 * (windowLength N T.1 0 s.1 : ℝ)) := by
                exact Finset.sum_le_sum fun j _hj => hrowWindowLoss j
      _ = influenceRowBound N ^ 2 *
            (∑ j ∈ Finset.range T.1,
              ((windowLength N T.1 (j + 1) s.1 : ℝ) -
                (windowLength N T.1 (j + loadingDelay N s.1) s.1 : ℝ))) +
          (n : ℝ) * s.1 ^ 2 * T.1 *
            (windowLength N T.1 0 s.1 : ℝ) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
  have hequation43 :
      windowInfluenceSum N T.1 s.1 - shiftedWindowInfluenceSum N T s.1 ≤
        (influenceRowBound N ^ 2 * (loadingDelay N s.1 - 1) +
          (n : ℝ) * s.1 ^ 2 * T.1) *
            (windowLength N T.1 0 s.1 : ℝ) := by
    have hshift := storage_window_shift_sum_le N T.1
      (loadingDelay N s.1) s.1 hloadingDelayOne
    have hBsq : 0 ≤ influenceRowBound N ^ 2 := sq_nonneg _
    calc
      windowInfluenceSum N T.1 s.1 - shiftedWindowInfluenceSum N T s.1 ≤
          influenceRowBound N ^ 2 *
              (∑ j ∈ Finset.range T.1,
                ((windowLength N T.1 (j + 1) s.1 : ℝ) -
                  (windowLength N T.1 (j + loadingDelay N s.1) s.1 : ℝ))) +
            (n : ℝ) * s.1 ^ 2 * T.1 *
              (windowLength N T.1 0 s.1 : ℝ) := htotalWindowLoss
      _ ≤ influenceRowBound N ^ 2 *
              ((loadingDelay N s.1 - 1 : ℕ) *
                (windowLength N T.1 0 s.1 : ℝ)) +
            (n : ℝ) * s.1 ^ 2 * T.1 *
              (windowLength N T.1 0 s.1 : ℝ) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hshift hBsq) le_rfl
      _ = (influenceRowBound N ^ 2 * (loadingDelay N s.1 - 1) +
            (n : ℝ) * s.1 ^ 2 * T.1) *
              (windowLength N T.1 0 s.1 : ℝ) := by
                rw [Nat.cast_sub hloadingDelayOne]
                ring
  have hequation44 :
      comparatorAt N L Δ σ T s / 6400 +
          ((windowLength N T.1 0 s.1 : ℝ) / T.1) *
            (3 * ADelta L Δ / 50 -
              σ ^ 2 / 800 *
                (influenceRowBound N ^ 2 * s.1 ^ 2 *
                    (loadingDelay N s.1 - 1) +
                  (n : ℝ) * s.1 ^ 4 * T.1)) ≤
        FiniteInstance.cost productInstance (s.1 / L) T := by
    let W : ℝ := windowLength N T.1 0 s.1
    let S : ℝ := windowInfluenceSum N T.1 s.1
    let Sshift : ℝ := shiftedWindowInfluenceSum N T s.1
    let K : ℝ := influenceRowBound N ^ 2 * (loadingDelay N s.1 - 1) +
      (n : ℝ) * s.1 ^ 2 * T.1
    have hshiftLower : S - K * W ≤ Sshift := by
      dsimp only [S, Sshift, K, W]
      linarith [hequation43]
    have hTpos : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
    have hcoeff : 0 ≤ σ ^ 2 * s.1 ^ 2 / (800 * (T.1 : ℝ)) := by
      positivity
    have hrearrange :
        comparatorAt N L Δ σ T s / 6400 +
            W / T.1 *
              (3 * ADelta L Δ / 50 -
                σ ^ 2 / 800 *
                  (influenceRowBound N ^ 2 * s.1 ^ 2 *
                      (loadingDelay N s.1 - 1) +
                    (n : ℝ) * s.1 ^ 4 * T.1)) =
          ADelta L Δ * W / (16 * T.1) +
            (σ ^ 2 * s.1 ^ 2 / (800 * T.1)) * (S - K * W) := by
      dsimp only [W, S, K]
      unfold comparatorAt comparatorNumerator epsilon
      field_simp [ne_of_gt hTpos]
      ring
    rw [hrearrange]
    calc
      ADelta L Δ * W / (16 * T.1) +
            (σ ^ 2 * s.1 ^ 2 / (800 * T.1)) * (S - K * W) ≤
          ADelta L Δ * W / (16 * T.1) +
            (σ ^ 2 * s.1 ^ 2 / (800 * T.1)) * Sshift := by
              exact add_le_add le_rfl
                (mul_le_mul_of_nonneg_left hshiftLower hcoeff)
      _ = ADelta L Δ * (windowLength N T.1 0 s.1 : ℝ) /
              (16 * T.1) +
            σ ^ 2 * s.1 ^ 2 * shiftedWindowInfluenceSum N T s.1 /
              (800 * T.1) := by
                dsimp only [W, Sshift]
                ring
      _ ≤ FiniteInstance.cost productInstance (s.1 / L) T := hequation42
  have hsignalExpectation (t : ℕ) (ht : t ≤ signalEnd) :
      deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2 ≤
        SOptLib.expectation productSetup.probability
          (stationarityIntegrand productSetup (s.1 / L) t) := by
    rw [← hsignalMeanAll omega0 t ht]
    unfold SOptLib.expectation
    calc
      deterministicGapDerivative L signalRadius
            ((arithmeticMean productSetup omega0 (s.1 / L) t) signalCoord) ^ 2 =
          ∫ _omega : Omega,
            deterministicGapDerivative L signalRadius
              ((arithmeticMean productSetup omega0 (s.1 / L) t) signalCoord) ^ 2
              ∂productSetup.probability := by
                simp [productSetup]
      _ ≤ ∫ omega : Omega,
          stationarityIntegrand productSetup (s.1 / L) t omega
            ∂productSetup.probability := by
        apply MeasureTheory.integral_mono
        · exact integrable_const _
        · exact stationarityIntegrand_integrable productSetup (s.1 / L) t
        · intro omega
          rw [hsignalMeanAll omega0 t ht, ← hsignalMeanAll omega t ht]
          exact hstationaritySignalPointwise omega t
  have hsignalExpectationNonneg (t : ℕ) : 0 ≤
      SOptLib.expectation productSetup.probability
        (stationarityIntegrand productSetup (s.1 / L) t) := by
    unfold SOptLib.expectation
    apply MeasureTheory.integral_nonneg
    intro omega
    exact sq_nonneg _
  have hsignalWindowExpectations :
      (∑ t ∈ Finset.Ico signalStart signalEnd,
          deterministicGapDerivative L signalRadius (actualSignalMean t) ^ 2) ≤
        ∑ t ∈ Finset.Ico signalStart signalEnd,
          SOptLib.expectation productSetup.probability
            (stationarityIntegrand productSetup (s.1 / L) t) := by
    exact Finset.sum_le_sum fun t ht =>
      hsignalExpectation t (Finset.mem_Ico.mp ht).2.le
  have hsignalIcoSubset : Finset.Ico signalStart signalEnd ⊆
      Finset.range T.1 := by
    intro t ht
    rw [Finset.mem_range]
    exact (Finset.mem_Ico.mp ht).2.trans_le hsignalQT
  have hsignalWindowWithinHorizon :
      (∑ t ∈ Finset.Ico signalStart signalEnd,
          SOptLib.expectation productSetup.probability
            (stationarityIntegrand productSetup (s.1 / L) t)) ≤
        ∑ t ∈ Finset.range T.1,
          SOptLib.expectation productSetup.probability
            (stationarityIntegrand productSetup (s.1 / L) t) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsignalIcoSubset
      (fun t _ht _hnot => hsignalExpectationNonneg t)
  have hdeterministicCost :
      ADelta L Δ * (windowLength N T.1 0 s.1 : ℝ) / (16 * T.1) ≤
        FiniteInstance.cost productInstance (s.1 / L) T := by
    have hsum : L * Δ / 16 * (windowLength N T.1 0 s.1 : ℝ) ≤
        ∑ t ∈ Finset.range T.1,
          SOptLib.expectation productSetup.probability
            (stationarityIntegrand productSetup (s.1 / L) t) :=
      hdeterministicWindow'.trans
        (hsignalWindowExpectations.trans hsignalWindowWithinHorizon)
    have hTpos : 0 < (T.1 : ℝ) := Nat.cast_pos.mpr T.2
    change ADelta L Δ * (windowLength N T.1 0 s.1 : ℝ) / (16 * T.1) ≤
      stationarityError productSetup (s.1 / L) T
    unfold stationarityError
    calc
      ADelta L Δ * (windowLength N T.1 0 s.1 : ℝ) / (16 * T.1) =
          (T.1 : ℝ)⁻¹ *
            (L * Δ / 16 * (windowLength N T.1 0 s.1 : ℝ)) := by
              unfold ADelta
              field_simp [ne_of_gt hTpos]
      _ ≤ (T.1 : ℝ)⁻¹ *
          ∑ t ∈ Finset.range T.1,
            SOptLib.expectation productSetup.probability
              (stationarityIntegrand productSetup (s.1 / L) t) := by
        exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTpos.le)
  refine ⟨productInstance, hproductFixed, hproductHeterogeneity, ?_, ?_, ?_⟩
  · exact ENNReal.ofReal_le_ofReal hequation42
  · exact ENNReal.ofReal_le_ofReal hequation44
  · intro habsorb
    apply ENNReal.ofReal_le_ofReal
    have hADelta : 0 < ADelta L Δ := by
      unfold ADelta
      exact mul_pos hL hΔ
    have hresidual : 0 ≤
        3 * ADelta L Δ / 50 -
          σ ^ 2 / 800 *
            (influenceRowBound N ^ 2 * s.1 ^ 2 *
                (loadingDelay N s.1 - 1) +
              (n : ℝ) * s.1 ^ 4 * T.1) := by
      nlinarith
    have hwindowRatio : 0 ≤
        (windowLength N T.1 0 s.1 : ℝ) / T.1 := by positivity
    calc
      comparatorAt N L Δ σ T s / 6400 ≤
          comparatorAt N L Δ σ T s / 6400 +
            ((windowLength N T.1 0 s.1 : ℝ) / T.1) *
              (3 * ADelta L Δ / 50 -
                σ ^ 2 / 800 *
                  (influenceRowBound N ^ 2 * s.1 ^ 2 *
                      (loadingDelay N s.1 - 1) +
                    (n : ℝ) * s.1 ^ 4 * T.1)) := by
            exact le_add_of_nonneg_right (mul_nonneg hwindowRatio hresidual)
      _ ≤ FiniteInstance.cost productInstance (s.1 / L) T := hequation44

/-- Equations (41)--(45), with the paper-facing quantifier order preserved.
The implementation factors through an internal supplier whose loading cap is
chosen before the heterogeneity layer, as required by the H-uniform use in
equations (54)--(56). -/
theorem storage_instance_lower_bound
    (N : NetworkSetup n) (L Δ σ H : ℝ)
    (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 < σ) (hH : 0 ≤ H) :
    ∃ sLoad : ℝ, 0 < sLoad ∧ sLoad ≤ 1 / (64 * n) ∧
      ∀ (T : PositiveHorizon) (s : AdmissibleDimensionlessStepsize n),
        s.1 ≤ sLoad →
        ∃ I ∈ fixedInstanceClass N L Δ σ H,
          @initialHeterogeneitySq n I.d I.Ω I.measurableSpace I.setup = 0 ∧
          ENNReal.ofReal
              (ADelta L Δ * windowLength N T.1 0 s.1 / (16 * T.1) +
                σ ^ 2 * s.1 ^ 2 * shiftedWindowInfluenceSum N T s.1 /
                  (800 * T.1)) ≤
            ENNReal.ofReal (FiniteInstance.cost I (s.1 / L) T) ∧
          ENNReal.ofReal
              (comparatorAt N L Δ σ T s / 6400 +
                (windowLength N T.1 0 s.1 / T.1) *
                  (3 * ADelta L Δ / 50 -
                    σ ^ 2 / 800 *
                      (influenceRowBound N ^ 2 * s.1 ^ 2 *
                          (loadingDelay N s.1 - 1) + n * s.1 ^ 4 * T.1))) ≤
            ENNReal.ofReal (FiniteInstance.cost I (s.1 / L) T) ∧
          (σ ^ 2 *
              (influenceRowBound N ^ 2 * s.1 ^ 2 *
                  (loadingDelay N s.1 - 1) + n * s.1 ^ 4 * T.1) ≤
                48 * ADelta L Δ →
            ENNReal.ofReal (comparatorAt N L Δ σ T s / 6400) ≤
              ENNReal.ofReal (FiniteInstance.cost I (s.1 / L) T)) := by
  obtain ⟨sLoad, hsLoad, hsLoadCap, hload⟩ :=
    storage_instance_lower_bound_uniform_in_H N L Δ σ hL hΔ hσ
  exact ⟨sLoad, hsLoad, hsLoadCap, hload H hH⟩

/-- Objective-side data for the homogeneous one-dimensional quadratic used in
equation (46).  This is kept separate from the iid construction so that the
state recurrence below can expose exactly which facts come from the objective
and which come from the generated noise law. -/
theorem actualQuadraticObjective_spec
    (L Δ : ℝ) (hL : 0 < L) (hΔ : 0 < Δ) :
    let F : Point 1 → ℝ := fun x => (L / 2) * ‖x‖ ^ 2
    let x0 : Point 1 :=
      WithLp.toLp 2 (fun _ : Fin 1 => Real.sqrt (2 * Δ / L))
    (Differentiable ℝ F ∧ LipschitzWith ⟨L, hL.le⟩ (gradient F)) ∧
      (∀ x, 0 ≤ F x) ∧
      sInf (Set.range F) = 0 ∧
      F x0 - sInf (Set.range F) = Δ ∧
      ∀ x, gradient F x = L • x := by
  let F : Point 1 → ℝ := fun x => (L / 2) * ‖x‖ ^ 2
  let x0 : Point 1 :=
    WithLp.toLp 2 (fun _ : Fin 1 => Real.sqrt (2 * Δ / L))
  have hgrad (x : Point 1) : gradient F x = L • x := by
    dsimp [F]
    simpa [smul_eq_mul] using
      (hasGradientAt_const_mul_norm_sub_sq_centered
        L (0 : Point 1) x).gradient
  have hsmooth : Differentiable ℝ F ∧
      LipschitzWith ⟨L, hL.le⟩ (gradient F) := by
    constructor
    · intro x
      simpa [F] using (hasGradientAt_const_mul_norm_sub_sq_centered
        L (0 : Point 1) x).differentiableAt
    · rw [funext hgrad]
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos hL]
      exact le_rfl
  have hnonneg : ∀ x, 0 ≤ F x := by
    intro x
    exact mul_nonneg (div_nonneg hL.le (by norm_num)) (sq_nonneg _)
  have hsinf : sInf (Set.range F) = 0 := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨0, ⟨0, by simp [F]⟩⟩
    · rintro _ ⟨x, rfl⟩
      exact hnonneg x
    · intro w hw
      exact ⟨0, ⟨0, by simp [F]⟩, hw⟩
  have hx0norm : ‖x0‖ ^ 2 = 2 * Δ / L := by
    have harg : 0 ≤ 2 * Δ / L := by positivity
    dsimp [x0]
    rw [PiLp.norm_eq_of_L2]
    simp [Real.sq_sqrt harg]
  have hgap : F x0 - sInf (Set.range F) = Δ := by
    rw [hsinf]
    dsimp [F]
    rw [hx0norm]
    field_simp [hL.ne']
    ring
  exact ⟨hsmooth, hnonneg, hsinf, hgap, hgrad⟩

/-- The iid node-time Rademacher table used by the actual quadratic response.
The contracts are stated for the generated strict history, not for a substituted
raw product filtration. -/
def actualQuadraticFastOutput
    (N : NetworkSetup n) (t : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  dotProduct (absoluteProbability N (t + 1)) (F.1 + F.2)

def actualQuadraticCorrectedLiftTerm
    (N : NetworkSetup n) (t j : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  actualQuadraticFastOutput N (t + j)
    (loadingFastPropagator N (t + j) t F.1 F.2)

noncomputable def actualQuadraticCorrectedLift
    (N : NetworkSetup n) (t : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑' j : ℕ, actualQuadraticCorrectedLiftTerm N t j F

/-- Removing the first triangular fast step from a propagated state shifts
the base time of the remaining unperturbed product. -/
theorem actualQuadraticFastPropagator_shift
    (N : NetworkSetup n) (t j : ℕ) (E K : Fin n → ℝ) :
    loadingFastPropagator N (t + 1 + j) t E K =
      loadingFastPropagator N (t + 1 + j) (t + 1)
        (loadingFastStep N t (E, K)).1
        (loadingFastStep N t (E, K)).2 := by
  induction j with
  | zero =>
      calc
        loadingFastPropagator N (t + 1 + 0) t E K =
            loadingFastStep N t (loadingFastPropagator N t t E K) := by
              simpa using loadingFastPropagator_succ N t t le_rfl E K
        _ = loadingFastStep N t (E, K) := by
              rw [loadingFastPropagator_self]
        _ = loadingFastPropagator N (t + 1 + 0) (t + 1)
              (loadingFastStep N t (E, K)).1
              (loadingFastStep N t (E, K)).2 := by
              rw [loadingFastPropagator_self]
  | succ j ih =>
      rw [show t + 1 + (j + 1) = (t + 1 + j) + 1 by omega]
      rw [loadingFastPropagator_succ N (t + 1 + j) t (by omega)]
      rw [loadingFastPropagator_succ N (t + 1 + j) (t + 1) (by omega)]
      rw [ih]

/-- Absolute convergence and the uniform geometric norm bound for the
equation-(47) corrected-lift series. -/
theorem actualQuadraticCorrectedLift_summable_bound
    (N : NetworkSetup n) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (t : ℕ) (E K : Fin n → ℝ),
        dotProduct (absoluteProbability N t) E = 0 →
        (∑ i, K i) = 0 →
        Summable (fun j =>
          actualQuadraticCorrectedLiftTerm N t j (E, K)) ∧
        |actualQuadraticCorrectedLift N t (E, K)| ≤
          (M / (1 - loadingFastRate N)) *
            (nodeSupNorm E + nodeL1Norm K) := by
  classical
  obtain ⟨Mtri, _hMtriBase, _hMtri_nonneg, htriangular⟩ :=
    exists_loading_triangular_product_constant N
  let M : ℝ := max 1 Mtri
  have hM : 1 ≤ M := le_max_left _ _
  have hMtri_le : Mtri ≤ M := le_max_right _ _
  have hr_nonneg : 0 ≤ loadingFastRate N := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hr_lt_one : loadingFastRate N < 1 := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have htriangularM : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K) := by
    intro k t hkt E K hE hK
    have hraw := htriangular k t hkt E K hE hK
    have hpow : 0 ≤ loadingFastRate N ^ (t - k) :=
      pow_nonneg hr_nonneg _
    have hgauge : 0 ≤ nodeSupNorm E + nodeL1Norm K := by
      exact add_nonneg (nodeSupNorm_nonneg N E)
        (Finset.sum_nonneg fun i _ => abs_nonneg (K i))
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMtri_le hpow) hgauge)
  refine ⟨M, hM, ?_⟩
  intro t E K hE hK
  let g : ℝ := nodeSupNorm E + nodeL1Norm K
  have hterm (j : ℕ) :
      ‖actualQuadraticCorrectedLiftTerm N t j (E, K)‖ ≤
        (M * g) * loadingFastRate N ^ j := by
    have hout := loadingCenterFeedback_abs_le_gauge N (t + j + 1)
      (loadingFastPropagator N (t + j) t E K).1
      (loadingFastPropagator N (t + j) t E K).2
    have hprop := loadingFastPropagator_gauge_le
      N M (loadingFastRate N) htriangularM (t + j) t (by omega)
        E K hE hK
    rw [show t + j - t = j by omega] at hprop
    change |actualQuadraticCorrectedLiftTerm N t j (E, K)| ≤ _
    exact (hout.trans hprop).trans_eq (by dsimp [g]; ring)
  have hseries := summable_and_norm_tsum_le_of_geometric_bound
    (fun j => actualQuadraticCorrectedLiftTerm N t j (E, K))
    (M * g) (loadingFastRate N) hr_nonneg hr_lt_one hterm
  constructor
  · exact hseries.1
  · rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one] at hseries
    change |actualQuadraticCorrectedLift N t (E, K)| ≤ _
    rw [show |actualQuadraticCorrectedLift N t (E, K)| =
        ‖actualQuadraticCorrectedLift N t (E, K)‖ by rfl]
    dsimp [actualQuadraticCorrectedLift]
    calc
      ‖∑' j, actualQuadraticCorrectedLiftTerm N t j (E, K)‖ ≤
          (M * g) * (1 - loadingFastRate N)⁻¹ := hseries.2
      _ = (M / (1 - loadingFastRate N)) *
          (nodeSupNorm E + nodeL1Norm K) := by
        dsimp [g]
        rw [div_eq_mul_inv]
        ring

/-- The absolutely convergent lift satisfies the source's one-step resolvent
identity on the time-dependent triangular fast carrier. -/
theorem actualQuadraticCorrectedLift_resolvent
    (N : NetworkSetup n) (t : ℕ) (E K : Fin n → ℝ)
    (hE : dotProduct (absoluteProbability N t) E = 0)
    (hK : (∑ i, K i) = 0) :
    actualQuadraticCorrectedLift N t (E, K) =
      actualQuadraticFastOutput N t (E, K) +
        actualQuadraticCorrectedLift N (t + 1)
          (loadingFastStep N t (E, K)) := by
  obtain ⟨M, _hM, hbound⟩ :=
    actualQuadraticCorrectedLift_summable_bound N
  have hsum := (hbound t E K hE hK).1
  have hnextCarrier := loadingFastStep_invariants N t E K hE hK
  have hnextSum :=
    (hbound (t + 1) (loadingFastStep N t (E, K)).1
      (loadingFastStep N t (E, K)).2
      hnextCarrier.1 hnextCarrier.2).1
  have hhead :
      actualQuadraticCorrectedLiftTerm N t 0 (E, K) =
        actualQuadraticFastOutput N t (E, K) := by
    simp [actualQuadraticCorrectedLiftTerm,
      loadingFastPropagator_self]
  have htail (j : ℕ) :
      actualQuadraticCorrectedLiftTerm N t (j + 1) (E, K) =
        actualQuadraticCorrectedLiftTerm N (t + 1) j
          (loadingFastStep N t (E, K)) := by
    unfold actualQuadraticCorrectedLiftTerm
    rw [show t + (j + 1) = t + 1 + j by omega]
    rw [actualQuadraticFastPropagator_shift N t j E K]
  rw [actualQuadraticCorrectedLift, hsum.tsum_eq_zero_add, hhead]
  congr 1
  exact tsum_congr htail

/-- On a pure tracker fast state, the triangular corrected lift is exactly the
already-constructed column resolvent `D_t`. -/
theorem actualQuadraticCorrectedLift_pure_tracker
    (N : NetworkSetup n) (t : ℕ) (K : Fin n → ℝ)
    (hK : (∑ i, K i) = 0) :
    actualQuadraticCorrectedLift N t (0, K) =
      influenceOperator N t ⟨K, hK⟩ := by
  unfold actualQuadraticCorrectedLift influenceOperator
  apply tsum_congr
  intro j
  simp [actualQuadraticCorrectedLiftTerm, actualQuadraticFastOutput,
    loadingFastPropagator, forwardProduct,
    FiniteNetwork.periodicCorrectedLift,
    FiniteNetwork.periodicCorrectedLiftSeriesTerm, dotProduct]
  rfl

/-- Applying the pull-only input `N_t^0 e=(0,(C_t-I)e)` to the corrected
lift produces the source influence-row coefficient after adding the direct
Perron term. -/
theorem actualQuadraticCorrectedLift_pull_input
    (N : NetworkSetup n) (t : ℕ) (e : Fin n → ℝ) :
    dotProduct (absoluteProbability N (t + 1)) e +
        actualQuadraticCorrectedLift N (t + 1)
          (0, (N.colMix t - 1) *ᵥ e) =
      dotProduct (influenceRow N t) e := by
  classical
  have hzero : (∑ i, ((N.colMix t - 1) *ᵥ e) i) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec,
      show (∑ i, (N.colMix t *ᵥ e - e) i) =
          (∑ i, (N.colMix t *ᵥ e) i) - ∑ i, e i by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib],
      Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t)]
    ring
  rw [actualQuadraticCorrectedLift_pure_tracker N (t + 1)
    ((N.colMix t - 1) *ᵥ e) hzero]
  let W : Fin n → ZeroSumNodeVector n := fun i => columnInnovation N t i
  have hinput :
      (⟨(N.colMix t - 1) *ᵥ e, hzero⟩ : ZeroSumNodeVector n) =
        ⟨fun q => ∑ i, e i * (W i).1 q, by
          change ∑ q, ∑ i, e i * (W i).1 q = 0
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro i hi
          rw [← Finset.mul_sum, (W i).2, mul_zero]⟩ := by
    apply Subtype.ext
    funext q
    change ((N.colMix t - 1) *ᵥ e) q =
      ∑ i, e i * (columnInnovation N t i).1 q
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change (∑ x, N.colMix t q x * e x) - e q =
      ∑ x, e x * (N.colMix t q x - if q = x then 1 else 0)
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  rw [hinput]
  rw [influenceOperator_finset_sum_smul N (t + 1)
    (Finset.univ : Finset (Fin n)) e W]
  unfold dotProduct influenceRow
  simp only [Finset.sum_add_distrib, add_mul]
  simpa [W, mul_comm]

/-- Complete T1 interface for the corrected lift used in equation (47). -/
theorem actual_quadratic_corrected_lift_spec
    (N : NetworkSetup n) :
    ∃ M : ℝ, 1 ≤ M ∧
      (∀ (t : ℕ) (E K : Fin n → ℝ),
        dotProduct (absoluteProbability N t) E = 0 →
        (∑ i, K i) = 0 →
        Summable (fun j =>
          actualQuadraticCorrectedLiftTerm N t j (E, K)) ∧
        |actualQuadraticCorrectedLift N t (E, K)| ≤
          (M / (1 - loadingFastRate N)) *
            (nodeSupNorm E + nodeL1Norm K)) ∧
      (∀ (t : ℕ) (E K : Fin n → ℝ),
        dotProduct (absoluteProbability N t) E = 0 →
        (∑ i, K i) = 0 →
        actualQuadraticCorrectedLift N t (E, K) =
          actualQuadraticFastOutput N t (E, K) +
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastStep N t (E, K))) ∧
      (∀ (t : ℕ) (K : Fin n → ℝ) (hK : (∑ i, K i) = 0),
        actualQuadraticCorrectedLift N t (0, K) =
          influenceOperator N t ⟨K, hK⟩) ∧
      (∀ (t : ℕ) (e : Fin n → ℝ),
        dotProduct (absoluteProbability N (t + 1)) e +
            actualQuadraticCorrectedLift N (t + 1)
              (0, (N.colMix t - 1) *ᵥ e) =
          dotProduct (influenceRow N t) e) := by
  obtain ⟨M, hM, hbound⟩ :=
    actualQuadraticCorrectedLift_summable_bound N
  exact ⟨M, hM, hbound,
    fun t E K hE hK =>
      actualQuadraticCorrectedLift_resolvent N t E K hE hK,
    fun t K hK => actualQuadraticCorrectedLift_pure_tracker N t K hK,
    actualQuadraticCorrectedLift_pull_input N⟩

/-- Uniform pure-network majorants for the three operators that enter the
forced equation-(47) bootstrap.  These are the constructive `K₀`, `J₀`, and
`B₀` ingredients from the verification supplement. -/
theorem actual_quadratic_equation47_operator_majorants
    (N : NetworkSetup n) :
    ∃ K0 J0 B0 : ℝ,
      0 ≤ K0 ∧ 0 ≤ J0 ∧ 0 ≤ B0 ∧
      (∀ (t : ℕ) (E K : Fin n → ℝ),
        dotProduct (absoluteProbability N t) E = 0 →
        (∑ i, K i) = 0 →
        |actualQuadraticCorrectedLift N t (E, K)| ≤
          K0 * (nodeSupNorm E + nodeL1Norm K)) ∧
      (∀ (t : ℕ) (E K : Fin n → ℝ),
        nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
            nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
          J0 * (nodeSupNorm E + nodeL1Norm K)) ∧
      ∀ (t : ℕ) (z : ℝ),
        nodeSupNorm (loadingFastCenterInput N t z).1 +
            nodeL1Norm (loadingFastCenterInput N t z).2 ≤ B0 * |z| := by
  obtain ⟨M, hM, hbound, _hres, _hpure, _hpull⟩ :=
    actual_quadratic_corrected_lift_spec N
  let K0 := M / (1 - loadingFastRate N)
  let J0 := 2 * ((n : ℝ) + 1)
  let B0 := 2 * (n : ℝ) * ((n : ℝ) + 1)
  have hfast_lt : loadingFastRate N < 1 := by
    unfold loadingFastRate loadingTriangularRate
    linarith [mixingRate_lt_one N]
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    exact div_nonneg (by linarith) (by linarith)
  have hJ0 : 0 ≤ J0 := by dsimp [J0]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  refine ⟨K0, J0, B0, hK0, hJ0, hB0, ?_, ?_, ?_⟩
  · intro t E K hE hK
    simpa [K0] using (hbound t E K hE hK).2
  · intro t E K
    simpa [J0] using (loadingFastPerturbationInput_spec N t E K).2.2
  · intro t z
    simpa [B0] using loadingFastCenterInput_gauge_le N t z

/-- The two scalar coefficient bounds `A_q` and `L_q` appearing in the
supplemental slow recurrence.  They are assembled only from the operator
majorants above and the network gain bound. -/
theorem actual_quadratic_equation47_slow_coefficient_majorants
    (N : NetworkSetup n) (K0 J0 B0 : ℝ)
    (hK0 : 0 ≤ K0) (hJ0 : 0 ≤ J0) (hB0 : 0 ≤ B0)
    (hK : ∀ (t : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N t) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N t (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K))
    (hJ : ∀ (t : ℕ) (E K : Fin n → ℝ),
      nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
        J0 * (nodeSupNorm E + nodeL1Norm K))
    (hB : ∀ (t : ℕ) (z : ℝ),
      nodeSupNorm (loadingFastCenterInput N t z).1 +
          nodeL1Norm (loadingFastCenterInput N t z).2 ≤ B0 * |z|) :
    ∃ Aq Lq : ℝ, 0 ≤ Aq ∧ 0 ≤ Lq ∧
      ∀ (s : ℝ), 0 ≤ s → s ≤ 1 → ∀ (t : ℕ)
        (F : (Fin n → ℝ) × (Fin n → ℝ)),
        dotProduct (absoluteProbability N t) F.1 = 0 →
        (∑ i, F.2 i) = 0 →
        (∀ z : ℝ,
          |actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t z)| ≤ Aq * |z|) ∧
        |-gain N t * actualQuadraticCorrectedLift N t F +
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastPerturbationInput N t F.1 F.2) +
            s * actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t
                (actualQuadraticCorrectedLift N t F))| ≤
          Lq * (nodeSupNorm F.1 + nodeL1Norm F.2) := by
  let Aq := K0 * B0
  let Lq := (n : ℝ) * K0 + K0 * J0 + K0 * B0 * K0
  have hAq : 0 ≤ Aq := by dsimp [Aq]; positivity
  have hLq : 0 ≤ Lq := by dsimp [Lq]; positivity
  refine ⟨Aq, Lq, hAq, hLq, ?_⟩
  intro s hs hs1 t F hF1 hF2
  let G : ℝ := nodeSupNorm F.1 + nodeL1Norm F.2
  have hG : 0 ≤ G := by
    dsimp [G]
    exact add_nonneg (nodeSupNorm_nonneg N F.1)
      (Finset.sum_nonneg fun i _ => abs_nonneg (F.2 i))
  have hKF : |actualQuadraticCorrectedLift N t F| ≤ K0 * G := by
    simpa [G] using hK t F.1 F.2 hF1 hF2
  have hP := loadingFastPerturbationInput_spec N t F.1 F.2
  have hKPraw := hK (t + 1)
    (loadingFastPerturbationInput N t F.1 F.2).1
    (loadingFastPerturbationInput N t F.1 F.2).2 hP.1 hP.2.1
  have hKP :
      |actualQuadraticCorrectedLift N (t + 1)
          (loadingFastPerturbationInput N t F.1 F.2)| ≤
        K0 * J0 * G := by
    calc
      _ ≤ K0 * (nodeSupNorm
            (loadingFastPerturbationInput N t F.1 F.2).1 +
          nodeL1Norm
            (loadingFastPerturbationInput N t F.1 F.2).2) := hKPraw
      _ ≤ K0 * (J0 * G) :=
        mul_le_mul_of_nonneg_left (by simpa [G] using hJ t F.1 F.2) hK0
      _ = K0 * J0 * G := by ring
  have hcenter (z : ℝ) :
      |actualQuadraticCorrectedLift N (t + 1)
          (loadingFastCenterInput N t z)| ≤ K0 * B0 * |z| := by
    have hcarrier := loadingFastCenterInput_invariants N t z
    have hraw := hK (t + 1)
      (loadingFastCenterInput N t z).1
      (loadingFastCenterInput N t z).2 hcarrier.1 hcarrier.2
    calc
      _ ≤ K0 * (nodeSupNorm (loadingFastCenterInput N t z).1 +
          nodeL1Norm (loadingFastCenterInput N t z).2) := hraw
      _ ≤ K0 * (B0 * |z|) :=
        mul_le_mul_of_nonneg_left (hB t z) hK0
      _ = K0 * B0 * |z| := by ring
  have hKBK :
      |actualQuadraticCorrectedLift N (t + 1)
          (loadingFastCenterInput N t
            (actualQuadraticCorrectedLift N t F))| ≤
        K0 * B0 * K0 * G := by
    calc
      _ ≤ K0 * B0 * |actualQuadraticCorrectedLift N t F| :=
        hcenter (actualQuadraticCorrectedLift N t F)
      _ ≤ K0 * B0 * (K0 * G) :=
        mul_le_mul_of_nonneg_left hKF (mul_nonneg hK0 hB0)
      _ = K0 * B0 * K0 * G := by ring
  constructor
  · intro z
    simpa [Aq] using hcenter z
  · have hgain0 : 0 ≤ gain N t := by
      unfold gain dotProduct
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg ((absoluteProbability_spec N).1 (t + 1) i)
          (pushMass_nonneg N t i)
    have hgainN : gain N t ≤ (n : ℝ) :=
      (gain_bounds_before_corrected_center_control N t).2
    calc
      |-gain N t * actualQuadraticCorrectedLift N t F +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t F.1 F.2) +
          s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t F))| ≤
          gain N t * |actualQuadraticCorrectedLift N t F| +
            |actualQuadraticCorrectedLift N (t + 1)
              (loadingFastPerturbationInput N t F.1 F.2)| +
            s * |actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t
                (actualQuadraticCorrectedLift N t F))| := by
            calc
              _ ≤ |-gain N t * actualQuadraticCorrectedLift N t F| +
                  |actualQuadraticCorrectedLift N (t + 1)
                    (loadingFastPerturbationInput N t F.1 F.2)| +
                  |s * actualQuadraticCorrectedLift N (t + 1)
                    (loadingFastCenterInput N t
                      (actualQuadraticCorrectedLift N t F))| := by
                    exact (abs_add_le _ _).trans
                      (add_le_add (abs_add_le _ _) le_rfl)
              _ = _ := by simp [abs_mul, abs_of_nonneg hgain0,
                abs_of_nonneg hs]
      _ ≤ (n : ℝ) * (K0 * G) + K0 * J0 * G +
          s * (K0 * B0 * K0 * G) := by
            have hgainKF : gain N t *
                |actualQuadraticCorrectedLift N t F| ≤
                (n : ℝ) * (K0 * G) := by
              exact mul_le_mul hgainN hKF (abs_nonneg _)
                (Nat.cast_nonneg n)
            have hsKBK : s *
                |actualQuadraticCorrectedLift N (t + 1)
                  (loadingFastCenterInput N t
                    (actualQuadraticCorrectedLift N t F))| ≤
                s * (K0 * B0 * K0 * G) :=
              mul_le_mul_of_nonneg_left hKBK hs
            exact add_le_add (add_le_add hgainKF hKP) hsKBK
      _ ≤ (n : ℝ) * K0 * G + K0 * J0 * G +
          K0 * B0 * K0 * G := by
            have hR : 0 ≤ K0 * B0 * K0 * G := by positivity
            have hsR : s * (K0 * B0 * K0 * G) ≤
                K0 * B0 * K0 * G := by
              simpa using mul_le_mul_of_nonneg_right hs1 hR
            nlinarith
      _ = Lq * G := by dsimp [Lq]; ring
      _ = Lq * (nodeSupNorm F.1 + nodeL1Norm F.2) := by rfl

/-- Stable-sign slow/fast form of the exact quadratic state equation (46),
including both the pull input `N_t^0 e` and the `C_t-I` contribution. -/
theorem actualQuadratic_slow_fast_coordinates_of_recurrence
    (N : NetworkSetup n) (s : ℝ)
    (X U e : ℕ → Fin n → ℝ) (t : ℕ)
    (hUzero : ∀ r, (∑ q, U r q) = 0)
    (hXrec : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q)
    (hUrec : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q) :
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
      (∑ q, (F t).2 q) = 0) ∧
    xi (t + 1) =
      (1 - s * gain N t) * xi t -
        s * actualQuadraticFastOutput N t (F t) -
        s * dotProduct (absoluteProbability N (t + 1)) (e t) ∧
    F (t + 1) =
      loadingFastStep N t (F t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (F t).1 (F t).2) -
        loadingFastScale s (loadingFastCenterInput N t (xi t)) +
        (0, (N.colMix t - 1) *ᵥ e t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (e t) 0) := by
  classical
  let Xnext0 : Fin n → ℝ := fun q =>
    (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q
  let Unext0 : Fin n → ℝ := fun q =>
    (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q
  let X0 : ℕ → Fin n → ℝ := fun r =>
    if r = t then X t else if r = t + 1 then Xnext0 else 0
  let U0 : ℕ → Fin n → ℝ := fun r =>
    if r = t then U t else if r = t + 1 then Unext0 else 0
  have hX0t : X0 t = X t := by simp [X0]
  have hU0t : U0 t = U t := by simp [U0]
  have hX0next : X0 (t + 1) = Xnext0 := by simp [X0]
  have hU0next : U0 (t + 1) = Unext0 := by simp [U0]
  have hUnext0zero : (∑ q, Unext0 q) = 0 := by
    have hcol : (∑ q, (N.colMix t *ᵥ U t) q) = 0 := by
      rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t),
        hUzero t]
    have hinnovation :
        (∑ q, ((N.colMix t - 1) *ᵥ X t) q) = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t)]
      ring
    dsimp [Unext0]
    simp only [Finset.sum_add_distrib]
    rw [hcol, hinnovation]
    ring
  have hU0zero : ∀ r, (∑ q, U0 r q) = 0 := by
    intro r
    by_cases hrt : r = t
    · subst r
      simpa [hU0t] using hUzero t
    · by_cases hrnext : r = t + 1
      · subst r
        simpa [hU0next] using hUnext0zero
      · simp [U0, hrt, hrnext]
  have hX0rec : X0 (t + 1) = fun q =>
      (N.rowMix t *ᵥ X0 t) q + (-s) * X0 t q + (-s) * U0 t q := by
    rw [hX0next, hX0t, hU0t]
    funext q
    simp [Xnext0]
    ring
  have hU0rec : U0 (t + 1) = fun q =>
      (N.colMix t *ᵥ U0 t) q + ((N.colMix t - 1) *ᵥ X0 t) q := by
    rw [hU0next, hX0t, hU0t]
  have hbase := loading_slow_fast_coordinates_of_recurrence
    N (-s) X0 U0 t hU0zero hX0rec hU0rec
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let xi0 := loadingSlowCenter N X0
  let F0 := loadingFastCoordinates N X0 U0
  have hxit : xi0 t = xi t := by simp [xi0, xi, loadingSlowCenter, hX0t]
  have hFt : F0 t = F t := by
    unfold F0 F loadingFastCoordinates
    rw [hX0t, hU0t]
    rw [show loadingSlowCenter N X0 t = loadingSlowCenter N X t by
      exact hxit]
  have hcarrier :
      dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
        (∑ q, (F t).2 q) = 0 := by
    simpa [xi0, F0, hFt] using hbase.1
  have hXnoise : X (t + 1) = Xnext0 - fun q => s * e t q := by
    rw [hXrec]
    funext q
    simp [Xnext0]
  have hUnoise :
      U (t + 1) = Unext0 + (N.colMix t - 1) *ᵥ e t := by
    rw [hUrec]
    funext q
    simp [Unext0]
  have hxiNoise :
      xi (t + 1) = xi0 (t + 1) -
        s * dotProduct (absoluteProbability N (t + 1)) (e t) := by
    unfold xi xi0 loadingSlowCenter
    rw [hXnoise, hX0next]
    unfold dotProduct
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    apply congrArg₂ (· - ·) rfl
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hslow :
      xi (t + 1) =
        (1 - s * gain N t) * xi t -
          s * actualQuadraticFastOutput N t (F t) -
          s * dotProduct (absoluteProbability N (t + 1)) (e t) := by
    rw [hxiNoise]
    have hbaseSlow := hbase.2.1
    change xi0 (t + 1) =
      (1 + -s * gain N t) * xi0 t +
        -s * dotProduct (absoluteProbability N (t + 1))
          ((F0 t).1 + (F0 t).2) at hbaseSlow
    rw [hbaseSlow, hxit, hFt]
    unfold actualQuadraticFastOutput
    ring
  have hFnoise :
      F (t + 1) = F0 (t + 1) +
        (0, (N.colMix t - 1) *ᵥ e t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (e t) 0) := by
    have hxiNoise' :
        loadingSlowCenter N X (t + 1) =
          loadingSlowCenter N X0 (t + 1) -
            s * dotProduct (absoluteProbability N (t + 1)) (e t) := by
      simpa [xi, xi0] using hxiNoise
    apply Prod.ext <;> funext q
    · simp only [F, F0, loadingFastCoordinates, Prod.fst_add,
        Prod.fst_sub, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
        loadingFastScale, loadingFastPerturbationInput]
      rw [hXnoise, hX0next, hxiNoise']
      simp only [Pi.sub_apply]
      ring
    · simp only [F, F0, loadingFastCoordinates, Prod.snd_add,
        Prod.snd_sub, Pi.add_apply, Pi.sub_apply,
        loadingFastScale, loadingFastPerturbationInput]
      rw [hUnoise, hU0next, hxiNoise']
      simp only [Pi.add_apply]
      ring
  have hfast :
      F (t + 1) =
        loadingFastStep N t (F t) -
          loadingFastScale s
            (loadingFastPerturbationInput N t (F t).1 (F t).2) -
          loadingFastScale s (loadingFastCenterInput N t (xi t)) +
          (0, (N.colMix t - 1) *ᵥ e t) -
          loadingFastScale s
            (loadingFastPerturbationInput N t (e t) 0) := by
    rw [hFnoise]
    have hbaseFast := hbase.2.2
    change F0 (t + 1) =
      loadingFastStep N t (F0 t) +
        loadingFastScale (-s)
          (loadingFastPerturbationInput N t (F0 t).1 (F0 t).2) +
        loadingFastScale (-s) (loadingFastCenterInput N t (xi0 t)) at hbaseFast
    rw [hbaseFast, hFt, hxit]
    apply Prod.ext <;> funext q <;>
      simp [loadingFastScale, sub_eq_add_neg] <;> ring
  exact ⟨hcarrier, hslow, hfast⟩

theorem actualQuadraticFastPropagator_scale
    (N : NetworkSetup n) (t j : ℕ) (a : ℝ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) :
    loadingFastPropagator N (t + j) t
        (loadingFastScale a F).1 (loadingFastScale a F).2 =
      loadingFastScale a
        (loadingFastPropagator N (t + j) t F.1 F.2) := by
  have hstepScale (r : ℕ)
      (G : (Fin n → ℝ) × (Fin n → ℝ)) :
      loadingFastStep N r (loadingFastScale a G) =
        loadingFastScale a (loadingFastStep N r G) := by
    apply Prod.ext
    · funext q
      simp only [loadingFastStep, loadingFastScale, Matrix.mulVec,
        dotProduct, Prod.fst]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    · funext q
      simp only [loadingFastStep, loadingFastScale, Matrix.mulVec,
        dotProduct, Prod.snd, Pi.add_apply, Matrix.sub_apply]
      rw [mul_add]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> ring
  induction j with
  | zero => simp [loadingFastPropagator_self, loadingFastScale]
  | succ j ih =>
      rw [show t + (j + 1) = (t + j) + 1 by omega]
      rw [loadingFastPropagator_succ N (t + j) t (by omega)]
      rw [loadingFastPropagator_succ N (t + j) t (by omega)]
      rw [ih, hstepScale]

theorem actualQuadraticFastPropagator_add
    (N : NetworkSetup n) (t j : ℕ)
    (E₁ K₁ E₂ K₂ : Fin n → ℝ) :
    loadingFastPropagator N (t + j) t (E₁ + E₂) (K₁ + K₂) =
      loadingFastPropagator N (t + j) t E₁ K₁ +
        loadingFastPropagator N (t + j) t E₂ K₂ := by
  induction j with
  | zero => simp [loadingFastPropagator_self]
  | succ j ih =>
      rw [show t + (j + 1) = (t + j) + 1 by omega]
      rw [loadingFastPropagator_succ N (t + j) t (by omega)]
      rw [loadingFastPropagator_succ N (t + j) t (by omega)]
      rw [loadingFastPropagator_succ N (t + j) t (by omega)]
      rw [ih, loadingFastStep_add]

/-- Homogeneity of the triangular corrected lift. -/
theorem actualQuadraticCorrectedLift_scale
    (N : NetworkSetup n) (t : ℕ) (a : ℝ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) :
    actualQuadraticCorrectedLift N t (loadingFastScale a F) =
      a * actualQuadraticCorrectedLift N t F := by
  unfold actualQuadraticCorrectedLift
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  unfold actualQuadraticCorrectedLiftTerm
  rw [actualQuadraticFastPropagator_scale]
  simp [actualQuadraticFastOutput, loadingFastScale, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Additivity of the triangular corrected lift on two certified fast-carrier
states. -/
theorem actualQuadraticCorrectedLift_add
    (N : NetworkSetup n) (t : ℕ)
    (E₁ K₁ E₂ K₂ : Fin n → ℝ)
    (hE₁ : dotProduct (absoluteProbability N t) E₁ = 0)
    (hK₁ : (∑ i, K₁ i) = 0)
    (hE₂ : dotProduct (absoluteProbability N t) E₂ = 0)
    (hK₂ : (∑ i, K₂ i) = 0) :
    actualQuadraticCorrectedLift N t (E₁ + E₂, K₁ + K₂) =
      actualQuadraticCorrectedLift N t (E₁, K₁) +
        actualQuadraticCorrectedLift N t (E₂, K₂) := by
  obtain ⟨M, _hM, hbound⟩ :=
    actualQuadraticCorrectedLift_summable_bound N
  have hsum₁ := (hbound t E₁ K₁ hE₁ hK₁).1
  have hsum₂ := (hbound t E₂ K₂ hE₂ hK₂).1
  unfold actualQuadraticCorrectedLift
  calc
    (∑' j, actualQuadraticCorrectedLiftTerm N t j (E₁ + E₂, K₁ + K₂)) =
        ∑' j, (actualQuadraticCorrectedLiftTerm N t j (E₁, K₁) +
          actualQuadraticCorrectedLiftTerm N t j (E₂, K₂)) := by
      apply tsum_congr
      intro j
      unfold actualQuadraticCorrectedLiftTerm
      rw [actualQuadraticFastPropagator_add]
      simp [actualQuadraticFastOutput, dotProduct,
        Finset.sum_add_distrib]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑' j, actualQuadraticCorrectedLiftTerm N t j (E₁, K₁)) +
        ∑' j, actualQuadraticCorrectedLiftTerm N t j (E₂, K₂) :=
      hsum₁.tsum_add hsum₂

/-- The fast half of equation (47), obtained by substituting the corrected
slow coordinate into the compiled stable-sign equation-(46) decomposition.
The final nested scale is the literal `s^2 B_t K_t` self-innovation. -/
theorem actualQuadratic_corrected_fast_recurrence
    (N : NetworkSetup n) (s : ℝ)
    (X U e : ℕ → Fin n → ℝ) (t : ℕ)
    (hUzero : ∀ r, (∑ q, U r q) = 0)
    (hXrec : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q)
    (hUrec : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q) :
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let zq : ℕ → ℝ := fun r =>
      xi r - s * actualQuadraticCorrectedLift N r (F r)
    (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
      (∑ q, (F t).2 q) = 0) ∧
    F (t + 1) =
      loadingFastStep N t (F t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (F t).1 (F t).2) -
        loadingFastScale s (loadingFastCenterInput N t (zq t)) -
        loadingFastScale s
          (loadingFastScale s
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) +
        (0, (N.colMix t - 1) *ᵥ e t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (e t) 0) := by
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℕ → ℝ := fun r =>
    xi r - s * actualQuadraticCorrectedLift N r (F r)
  have hsf := actualQuadratic_slow_fast_coordinates_of_recurrence
    N s X U e t hUzero hXrec hUrec
  have hcarrier :
      dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
        (∑ q, (F t).2 q) = 0 := by
    simpa [xi, F] using hsf.1
  have hcenterSplit :
      loadingFastCenterInput N t (xi t) =
        loadingFastCenterInput N t (zq t) +
          loadingFastScale s
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t))) := by
    apply Prod.ext <;> funext q <;>
      simp [loadingFastCenterInput, loadingFastScale, zq] <;> ring
  have hraw := hsf.2.2
  change F (t + 1) =
    loadingFastStep N t (F t) -
      loadingFastScale s
        (loadingFastPerturbationInput N t (F t).1 (F t).2) -
      loadingFastScale s (loadingFastCenterInput N t (xi t)) +
      (0, (N.colMix t - 1) *ᵥ e t) -
      loadingFastScale s
        (loadingFastPerturbationInput N t (e t) 0) at hraw
  rw [hcenterSplit] at hraw
  refine ⟨hcarrier, ?_⟩
  change F (t + 1) =
    loadingFastStep N t (F t) -
      loadingFastScale s
        (loadingFastPerturbationInput N t (F t).1 (F t).2) -
      loadingFastScale s (loadingFastCenterInput N t (zq t)) -
      loadingFastScale s
        (loadingFastScale s
          (loadingFastCenterInput N t
            (actualQuadraticCorrectedLift N t (F t)))) +
      (0, (N.colMix t - 1) *ᵥ e t) -
      loadingFastScale s
        (loadingFastPerturbationInput N t (e t) 0)
  rw [hraw]
  apply Prod.ext <;> funext q <;>
    simp [loadingFastScale, sub_eq_add_neg] <;> ring

/-- The slow half of equation (47).  The resolvent cancels the order-`s`
fast output, while the pull-only input is combined with the direct Perron
term into the exact influence row. -/
theorem actualQuadratic_corrected_slow_recurrence
    (N : NetworkSetup n) (s : ℝ)
    (X U e : ℕ → Fin n → ℝ) (t : ℕ)
    (hUzero : ∀ r, (∑ q, U r q) = 0)
    (hXrec : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q)
    (hUrec : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q) :
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let zq : ℕ → ℝ := fun r =>
      xi r - s * actualQuadraticCorrectedLift N r (F r)
    (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
      (∑ q, (F t).2 q) = 0) ∧
    zq (t + 1) =
      (1 - s * gain N t) * zq t + s ^ 2 *
        (-gain N t * actualQuadraticCorrectedLift N t (F t) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (F t).1 (F t).2) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t (zq t)) +
          s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) -
        s * dotProduct (influenceRow N t) (e t) + s ^ 2 *
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (e t) 0) := by
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℕ → ℝ := fun r =>
    xi r - s * actualQuadraticCorrectedLift N r (F r)
  have hsf := actualQuadratic_slow_fast_coordinates_of_recurrence
    N s X U e t hUzero hXrec hUrec
  have hcarrier :
      dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
        (∑ q, (F t).2 q) = 0 := by
    simpa [xi, F] using hsf.1
  obtain ⟨_M, _hM, _hbound, hresSpec, _hpure, hpullSpec⟩ :=
    actual_quadratic_corrected_lift_spec N
  let A := loadingFastStep N t (F t)
  let J := loadingFastScale (-s)
    (loadingFastPerturbationInput N t (F t).1 (F t).2)
  let Bz := loadingFastScale (-s) (loadingFastCenterInput N t (zq t))
  let BK := loadingFastScale (-s)
    (loadingFastScale s
      (loadingFastCenterInput N t
        (actualQuadraticCorrectedLift N t (F t))))
  let N0 : (Fin n → ℝ) × (Fin n → ℝ) :=
    (0, (N.colMix t - 1) *ᵥ e t)
  let N1 := loadingFastScale (-s)
    (loadingFastPerturbationInput N t (e t) 0)
  have hscaleCarrier (a : ℝ)
      (G : (Fin n → ℝ) × (Fin n → ℝ))
      (hG : dotProduct (absoluteProbability N (t + 1)) G.1 = 0 ∧
        (∑ q, G.2 q) = 0) :
      dotProduct (absoluteProbability N (t + 1))
          (loadingFastScale a G).1 = 0 ∧
        (∑ q, (loadingFastScale a G).2 q) = 0 := by
    constructor
    · unfold dotProduct at hG ⊢
      simp only [loadingFastScale]
      calc
        (∑ x, absoluteProbability N (t + 1) x * (a * G.1 x)) =
            a * ∑ x, absoluteProbability N (t + 1) x * G.1 x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = 0 := by rw [hG.1, mul_zero]
    · simp only [loadingFastScale]
      rw [← Finset.mul_sum, hG.2, mul_zero]
  have haddCarrier
      (G H : (Fin n → ℝ) × (Fin n → ℝ))
      (hG : dotProduct (absoluteProbability N (t + 1)) G.1 = 0 ∧
        (∑ q, G.2 q) = 0)
      (hH : dotProduct (absoluteProbability N (t + 1)) H.1 = 0 ∧
        (∑ q, H.2 q) = 0) :
      dotProduct (absoluteProbability N (t + 1)) (G + H).1 = 0 ∧
        (∑ q, (G + H).2 q) = 0 := by
    constructor
    · unfold dotProduct at hG hH ⊢
      simp only [Prod.fst_add, Pi.add_apply, mul_add,
        Finset.sum_add_distrib, hG.1, hH.1, add_zero]
    · simp only [Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib,
        hG.2, hH.2, add_zero]
  have hA : dotProduct (absoluteProbability N (t + 1)) A.1 = 0 ∧
      (∑ q, A.2 q) = 0 := by
    simpa [A] using loadingFastStep_invariants N t (F t).1 (F t).2
      hcarrier.1 hcarrier.2
  have hP := loadingFastPerturbationInput_spec N t (F t).1 (F t).2
  have hJ : dotProduct (absoluteProbability N (t + 1)) J.1 = 0 ∧
      (∑ q, J.2 q) = 0 := by
    exact hscaleCarrier (-s) _ ⟨hP.1, hP.2.1⟩
  have hCz := loadingFastCenterInput_invariants N t (zq t)
  have hBz : dotProduct (absoluteProbability N (t + 1)) Bz.1 = 0 ∧
      (∑ q, Bz.2 q) = 0 := by
    exact hscaleCarrier (-s) _ hCz
  have hCK := loadingFastCenterInput_invariants N t
    (actualQuadraticCorrectedLift N t (F t))
  have hBK : dotProduct (absoluteProbability N (t + 1)) BK.1 = 0 ∧
      (∑ q, BK.2 q) = 0 := by
    exact hscaleCarrier (-s) _ (hscaleCarrier s _ hCK)
  have hN0 : dotProduct (absoluteProbability N (t + 1)) N0.1 = 0 ∧
      (∑ q, N0.2 q) = 0 := by
    constructor
    · simp [N0, dotProduct]
    · dsimp [N0]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib]
      rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic t)]
      ring
  have hPe := loadingFastPerturbationInput_spec N t (e t) 0
  have hN1 : dotProduct (absoluteProbability N (t + 1)) N1.1 = 0 ∧
      (∑ q, N1.2 q) = 0 := by
    exact hscaleCarrier (-s) _ ⟨hPe.1, hPe.2.1⟩
  have hfastSum : F (t + 1) = A + J + Bz + BK + N0 + N1 := by
    have hfast := (actualQuadratic_corrected_fast_recurrence
      N s X U e t hUzero hXrec hUrec).2
    change F (t + 1) =
      loadingFastStep N t (F t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (F t).1 (F t).2) -
        loadingFastScale s (loadingFastCenterInput N t (zq t)) -
        loadingFastScale s
          (loadingFastScale s
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) +
        (0, (N.colMix t - 1) *ᵥ e t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (e t) 0) at hfast
    change F (t + 1) = A + J + Bz + BK + N0 + N1
    rw [hfast]
    apply Prod.ext <;> funext q <;>
      simp [A, J, Bz, BK, N0, N1, loadingFastScale,
        sub_eq_add_neg] <;> ring
  have hAJ := haddCarrier A J hA hJ
  have hAJBz := haddCarrier (A + J) Bz hAJ hBz
  have hAJBzBK := haddCarrier (A + J + Bz) BK hAJBz hBK
  have hAJBzBKN0 := haddCarrier (A + J + Bz + BK) N0 hAJBzBK hN0
  have hKadd
      (G H : (Fin n → ℝ) × (Fin n → ℝ))
      (hG : dotProduct (absoluteProbability N (t + 1)) G.1 = 0 ∧
        (∑ q, G.2 q) = 0)
      (hH : dotProduct (absoluteProbability N (t + 1)) H.1 = 0 ∧
        (∑ q, H.2 q) = 0) :
      actualQuadraticCorrectedLift N (t + 1) (G + H) =
        actualQuadraticCorrectedLift N (t + 1) G +
          actualQuadraticCorrectedLift N (t + 1) H := by
    simpa only [Prod.fst_add, Prod.snd_add] using
      (actualQuadraticCorrectedLift_add N (t + 1)
        G.1 G.2 H.1 H.2 hG.1 hG.2 hH.1 hH.2)
  have hKsum :
      actualQuadraticCorrectedLift N (t + 1) (F (t + 1)) =
        actualQuadraticCorrectedLift N (t + 1) A +
          actualQuadraticCorrectedLift N (t + 1) J +
          actualQuadraticCorrectedLift N (t + 1) Bz +
          actualQuadraticCorrectedLift N (t + 1) BK +
          actualQuadraticCorrectedLift N (t + 1) N0 +
          actualQuadraticCorrectedLift N (t + 1) N1 := by
    rw [hfastSum]
    rw [hKadd (A + J + Bz + BK + N0) N1 hAJBzBKN0 hN1]
    rw [hKadd (A + J + Bz + BK) N0 hAJBzBK hN0]
    rw [hKadd (A + J + Bz) BK hAJBz hBK]
    rw [hKadd (A + J) Bz hAJ hBz]
    rw [hKadd A J hA hJ]
  have hKA :
      actualQuadraticCorrectedLift N (t + 1) A =
        actualQuadraticCorrectedLift N t (F t) -
          actualQuadraticFastOutput N t (F t) := by
    have hres := hresSpec t (F t).1 (F t).2 hcarrier.1 hcarrier.2
    dsimp [A]
    linarith
  have hKJ : actualQuadraticCorrectedLift N (t + 1) J =
      -s * actualQuadraticCorrectedLift N (t + 1)
        (loadingFastPerturbationInput N t (F t).1 (F t).2) := by
    simpa [J] using actualQuadraticCorrectedLift_scale N (t + 1) (-s)
      (loadingFastPerturbationInput N t (F t).1 (F t).2)
  have hKBz : actualQuadraticCorrectedLift N (t + 1) Bz =
      -s * actualQuadraticCorrectedLift N (t + 1)
        (loadingFastCenterInput N t (zq t)) := by
    simpa [Bz] using actualQuadraticCorrectedLift_scale N (t + 1) (-s)
      (loadingFastCenterInput N t (zq t))
  have hKBK : actualQuadraticCorrectedLift N (t + 1) BK =
      (-s) * s * actualQuadraticCorrectedLift N (t + 1)
        (loadingFastCenterInput N t
          (actualQuadraticCorrectedLift N t (F t))) := by
    rw [show BK = loadingFastScale (-s)
      (loadingFastScale s (loadingFastCenterInput N t
        (actualQuadraticCorrectedLift N t (F t)))) by rfl]
    rw [actualQuadraticCorrectedLift_scale,
      actualQuadraticCorrectedLift_scale]
    ring
  have hKN1 : actualQuadraticCorrectedLift N (t + 1) N1 =
      -s * actualQuadraticCorrectedLift N (t + 1)
        (loadingFastPerturbationInput N t (e t) 0) := by
    simpa [N1] using actualQuadraticCorrectedLift_scale N (t + 1) (-s)
      (loadingFastPerturbationInput N t (e t) 0)
  have hslow := hsf.2.1
  change xi (t + 1) =
    (1 - s * gain N t) * xi t -
      s * actualQuadraticFastOutput N t (F t) -
      s * dotProduct (absoluteProbability N (t + 1)) (e t) at hslow
  refine ⟨hcarrier, ?_⟩
  change xi (t + 1) -
      s * actualQuadraticCorrectedLift N (t + 1) (F (t + 1)) = _
  rw [hslow, hKsum, hKA, hKJ, hKBz, hKBK, hKN1]
  have hpull := hpullSpec t (e t)
  change dotProduct (absoluteProbability N (t + 1)) (e t) +
      actualQuadraticCorrectedLift N (t + 1) N0 =
        dotProduct (influenceRow N t) (e t) at hpull
  rw [← hpull]
  dsimp [zq]
  ring

/-- Literal paired equation-(47) recurrence, with the printed signs and the
`C_t-I` noise channel retained. -/
theorem actual_quadratic_corrected_slow_fast_recurrence
    (N : NetworkSetup n) (s : ℝ)
    (X U e : ℕ → Fin n → ℝ) (t : ℕ)
    (hUzero : ∀ r, (∑ q, U r q) = 0)
    (hXrec : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q)
    (hUrec : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q) :
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let zq : ℕ → ℝ := fun r =>
      xi r - s * actualQuadraticCorrectedLift N r (F r)
    (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
      (∑ q, (F t).2 q) = 0) ∧
    zq (t + 1) =
      (1 - s * gain N t) * zq t + s ^ 2 *
        (-gain N t * actualQuadraticCorrectedLift N t (F t) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (F t).1 (F t).2) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t (zq t)) +
          s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) -
        s * dotProduct (influenceRow N t) (e t) + s ^ 2 *
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (e t) 0) ∧
    F (t + 1) =
      loadingFastStep N t (F t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (F t).1 (F t).2) -
        loadingFastScale s (loadingFastCenterInput N t (zq t)) -
        loadingFastScale s
          (loadingFastScale s
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) +
        (0, (N.colMix t - 1) *ᵥ e t) -
        loadingFastScale s
          (loadingFastPerturbationInput N t (e t) 0) := by
  dsimp only
  have hs := actualQuadratic_corrected_slow_recurrence
    N s X U e t hUzero hXrec hUrec
  have hf := actualQuadratic_corrected_fast_recurrence
    N s X U e t hUzero hXrec hUrec
  exact ⟨hs.1, hs.2, hf.2⟩

theorem actualQuadraticNoise_spec
    (n : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ (atom : Fin 3 → ℝ) (nu : Measure (Fin 3))
        (phi : ℕ → Fin n → Fin 3 → Point 1),
      IsProbabilityMeasure nu ∧
      Integrable atom nu ∧
      (∫ a, atom a ∂nu) = 0 ∧
      (∫ a, ‖atom a‖ ^ 2 ∂nu) = sigma ^ 2 ∧
      (∀ F : ℝ → ℝ, F 0 = 0 → F (-sigma) = F sigma →
        (∫ a, F (atom a) ∂nu) = F sigma) ∧
      (∀ t i a, phi t i a = PiLp.single 2 (0 : Fin 1) (atom a)) ∧
      let noise : ℕ → SOptLib.miniBatchSamplePath n (Fin 3) →
          NodeTable n 1 := fun t omega i => phi t i (omega t i)
      (∀ t i,
        SOptLib.ConditionalExpectation.conditionalExpectationEq
          (SOptLib.iidMiniBatchSampleLaw n nu)
          (preSamplingHistoryOf noise t)
          (fun omega => noise t omega i) (fun _ => 0)) ∧
      (∀ t i,
        ConditionalSecondMomentBound
          (SOptLib.iidMiniBatchSampleLaw n nu)
          (preSamplingHistoryOf noise t)
          (fun omega => noise t omega i) (sigma ^ 2)) ∧
      (∀ t,
        NodeConditionallyIndependent
          (SOptLib.iidMiniBatchSampleLaw n nu)
          (preSamplingHistoryOf noise t)
          (fun i omega => noise t omega i)) := by
  classical
  obtain ⟨atom, nu, hnu, hatomInt, hcenter, hsecond, heven⟩ :=
    storageThreePointAtom_spec 1 sigma (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure nu := hnu
  let phi : ℕ → Fin n → Fin 3 → Point 1 :=
    fun _t _i a => PiLp.single 2 (0 : Fin 1) (atom a)
  have hphiMeas : ∀ t i, Measurable (phi t i) := by
    intro t i
    exact measurable_of_finite _
  have hphiInt : ∀ t i, Integrable (phi t i) nu := by
    intro t i
    exact Integrable.of_finite
  have hphiCenter : ∀ t i, (∫ a, phi t i a ∂nu) = 0 := by
    intro t i
    apply PiLp.ext
    intro k
    change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) k)
        (∫ a, phi t i a ∂nu) = 0
    rw [← (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 1 => ℝ) k).integral_comp_comm
      (Integrable.of_finite : Integrable (phi t i) nu)]
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    simpa [phi] using hcenter
  have hphiSqInt : ∀ t i,
      Integrable (fun a => ‖phi t i a‖ ^ 2) nu := by
    intro t i
    exact Integrable.of_finite
  have hphiSecond : ∀ t i,
      (∫ a, ‖phi t i a‖ ^ 2 ∂nu) ≤ sigma ^ 2 := by
    intro t i
    simpa [phi, PiLp.norm_single] using hsecond.le
  have hcontracts := iidMiniBatchSampleLaw_stochasticContracts
    n 1 nu phi hphiMeas sigma hphiInt hphiCenter hphiSqInt hphiSecond
  refine ⟨atom, nu, phi, hnu, hatomInt, hcenter, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hsecond
  · intro F hF0 hFe
    simpa using heven F hF0 hFe
  · intro t i a
    rfl
  · simpa [phi] using hcontracts.1
  · exact ⟨by simpa [phi] using hcontracts.2.1,
      by simpa [phi] using hcontracts.2.2⟩

/-- Full homogeneous fast-product estimate for equation (47).  The relative
innovation combines both the stable-sign `-sJ_t F_t` term and the nested
`-s^2 B_t \mathcal K_t F_t` term before applying the triangular product
estimate. -/
theorem actual_quadratic_fast_product_geometric
    (N : NetworkSetup n) (M s : ℝ)
    (hM : 1 ≤ M) (hs : 0 ≤ s)
    (K0 J0 B0 : ℝ) (hK0 : 0 ≤ K0) (hJ0 : 0 ≤ J0)
    (hB0 : 0 ≤ B0)
    (hK : ∀ (t : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N t) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N t (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K))
    (hJ : ∀ (t : ℕ) (E K : Fin n → ℝ),
      nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
        J0 * (nodeSupNorm E + nodeL1Norm K))
    (hB : ∀ (t : ℕ) (z : ℝ),
      nodeSupNorm (loadingFastCenterInput N t z).1 +
          nodeL1Norm (loadingFastCenterInput N t z).2 ≤ B0 * |z|)
    (htriangular : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K))
    : ∀ (hcap : loadingFastRate N +
          M * (s * J0 + s ^ 2 * B0 * K0) ≤ loadingTransverseRate N)
        (E K : ℕ → Fin n → ℝ) (k : ℕ),
        dotProduct (absoluteProbability N k) (E k) = 0 →
        (∑ i, K k i) = 0 →
        (∀ t, k ≤ t →
          (E (t + 1), K (t + 1)) =
            loadingFastStep N t (E t, K t) -
              loadingFastScale s
                (loadingFastPerturbationInput N t (E t) (K t)) -
              loadingFastScale s
                (loadingFastScale s
                  (loadingFastCenterInput N t
                    (actualQuadraticCorrectedLift N t (E t, K t))))) →
        ∀ t, k ≤ t →
          nodeSupNorm (E t) + nodeL1Norm (K t) ≤
            M * loadingTransverseRate N ^ (t - k) *
              (nodeSupNorm (E k) + nodeL1Norm (K k)) := by
  intro hcap E K k hEinit hKinit hstep
  let P : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun t =>
    loadingFastScale s
      (loadingFastPerturbationInput N t (E t) (K t))
  let C : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun t =>
    loadingFastScale s
      (loadingFastScale s
        (loadingFastCenterInput N t
          (actualQuadraticCorrectedLift N t (E t, K t))))
  let I : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun t =>
    loadingFastScale (-1) (P t) + loadingFastScale (-1) (C t)
  let d : ℝ := s * J0 + s ^ 2 * B0 * K0
  have hIcarrier (t : ℕ) :
      dotProduct (absoluteProbability N (t + 1)) (I t).1 = 0 ∧
        (∑ i, (I t).2 i) = 0 := by
    have hP0 := loadingFastPerturbationInput_spec N t (E t) (K t)
    have hPs := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastPerturbationInput N t (E t) (K t)) hP0.1 hP0.2.1
    have hC0 := loadingFastCenterInput_invariants N t
      (actualQuadraticCorrectedLift N t (E t, K t))
    have hCs1 := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastCenterInput N t
        (actualQuadraticCorrectedLift N t (E t, K t))) hC0.1 hC0.2
    have hCs2 := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastScale s
        (loadingFastCenterInput N t
          (actualQuadraticCorrectedLift N t (E t, K t))))
      hCs1.1 hCs1.2.1
    have hPneg : dotProduct (absoluteProbability N (t + 1))
        (loadingFastScale (-1) (P t)).1 = 0 := by
      unfold dotProduct at hPs ⊢
      simpa [P, loadingFastScale] using congrArg Neg.neg hPs.1
    have hCneg : dotProduct (absoluteProbability N (t + 1))
        (loadingFastScale (-1) (C t)).1 = 0 := by
      unfold dotProduct at hCs2 ⊢
      simpa [C, loadingFastScale] using congrArg Neg.neg hCs2.1
    constructor
    · dsimp only [I, Prod.fst_add]
      rw [dotProduct_add, hPneg, hCneg, add_zero]
    · dsimp only [I, Prod.snd_add]
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      have hPsum : (∑ i, (loadingFastScale (-1) (P t)).2 i) = 0 := by
        simpa [P, loadingFastScale] using congrArg Neg.neg hPs.2.1
      have hCsum : (∑ i, (loadingFastScale (-1) (C t)).2 i) = 0 := by
        simpa [C, loadingFastScale] using congrArg Neg.neg hCs2.2.1
      rw [hPsum, hCsum, add_zero]
  have hstepI (t : ℕ) (hkt : k ≤ t) :
      (E (t + 1), K (t + 1)) =
        loadingFastStep N t (E t, K t) + I t := by
    rw [hstep t hkt]
    apply Prod.ext <;> funext q <;>
      simp [I, P, C, loadingFastScale] <;> ring
  have hcarrier : ∀ t, k ≤ t →
      dotProduct (absoluteProbability N t) (E t) = 0 ∧
        (∑ i, K t i) = 0 := by
    intro t hkt
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkt
    induction m with
    | zero => simpa using And.intro hEinit hKinit
    | succ m ihm =>
        have ihm' := ihm (by omega)
        have hA := loadingFastStep_invariants N (k + m)
          (E (k + m)) (K (k + m)) ihm'.1 ihm'.2
        have hIt := hIcarrier (k + m)
        have hrec := hstepI (k + m) (by omega)
        have hrecE := congrArg Prod.fst hrec
        have hrecK := congrArg Prod.snd hrec
        have hrecE' : E (k + m + 1) =
            (loadingFastStep N (k + m) (E (k + m), K (k + m)) +
              I (k + m)).1 := by simpa using hrecE
        have hrecK' : K (k + m + 1) =
            (loadingFastStep N (k + m) (E (k + m), K (k + m)) +
              I (k + m)).2 := by simpa using hrecK
        constructor
        · rw [show k + (m + 1) = k + m + 1 by omega, hrecE']
          simp only [Prod.fst_add]
          rw [dotProduct_add, hA.1, hIt.1, add_zero]
        · rw [show k + (m + 1) = k + m + 1 by omega, hrecK']
          simp only [Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
          rw [hA.2, hIt.2, add_zero]
  have hIgauge (t : ℕ) (hkt : k ≤ t) :
      nodeSupNorm (I t).1 + nodeL1Norm (I t).2 ≤
        d * (nodeSupNorm (E t) + nodeL1Norm (K t)) := by
    let G := nodeSupNorm (E t) + nodeL1Norm (K t)
    have hG : 0 ≤ G := add_nonneg (nodeSupNorm_nonneg N _)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hP0 := loadingFastPerturbationInput_spec N t (E t) (K t)
    have hPs := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastPerturbationInput N t (E t) (K t)) hP0.1 hP0.2.1
    have hPbound : nodeSupNorm (P t).1 + nodeL1Norm (P t).2 ≤
        s * J0 * G := by
      calc
        nodeSupNorm (P t).1 + nodeL1Norm (P t).2 ≤
            s * (nodeSupNorm
              (loadingFastPerturbationInput N t (E t) (K t)).1 +
              nodeL1Norm
                (loadingFastPerturbationInput N t (E t) (K t)).2) := by
          simpa [P] using hPs.2.2
        _ ≤ s * (J0 * G) :=
          mul_le_mul_of_nonneg_left (by simpa [G] using hJ t (E t) (K t)) hs
        _ = s * J0 * G := by ring
    have hC0 := loadingFastCenterInput_invariants N t
      (actualQuadraticCorrectedLift N t (E t, K t))
    have hCs1 := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastCenterInput N t
        (actualQuadraticCorrectedLift N t (E t, K t))) hC0.1 hC0.2
    have hCs2 := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastScale s
        (loadingFastCenterInput N t
          (actualQuadraticCorrectedLift N t (E t, K t))))
      hCs1.1 hCs1.2.1
    have hlift : |actualQuadraticCorrectedLift N t (E t, K t)| ≤
        K0 * G := by
      simpa [G] using hK t (E t) (K t)
        (hcarrier t hkt).1 (hcarrier t hkt).2
    have hCbound : nodeSupNorm (C t).1 + nodeL1Norm (C t).2 ≤
        s ^ 2 * B0 * K0 * G := by
      calc
        nodeSupNorm (C t).1 + nodeL1Norm (C t).2 ≤
            s * (nodeSupNorm
              (loadingFastScale s
                (loadingFastCenterInput N t
                  (actualQuadraticCorrectedLift N t (E t, K t)))).1 +
              nodeL1Norm
                (loadingFastScale s
                  (loadingFastCenterInput N t
                    (actualQuadraticCorrectedLift N t (E t, K t)))).2) := by
          simpa [C] using hCs2.2.2
        _ ≤ s * (s * (nodeSupNorm
              (loadingFastCenterInput N t
                (actualQuadraticCorrectedLift N t (E t, K t))).1 +
              nodeL1Norm
                (loadingFastCenterInput N t
                  (actualQuadraticCorrectedLift N t (E t, K t))).2)) :=
          mul_le_mul_of_nonneg_left hCs1.2.2 hs
        _ ≤ s * (s * (B0 *
              |actualQuadraticCorrectedLift N t (E t, K t)|)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (hB t (actualQuadraticCorrectedLift N t (E t, K t))) hs) hs
        _ ≤ s * (s * (B0 * (K0 * G))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hlift hB0) hs) hs
        _ = s ^ 2 * B0 * K0 * G := by ring
    have hPneg := loadingFastScale_gauge_le_abs N (-1) (P t)
    have hCneg := loadingFastScale_gauge_le_abs N (-1) (C t)
    norm_num at hPneg hCneg
    calc
      nodeSupNorm (I t).1 + nodeL1Norm (I t).2 ≤
          (nodeSupNorm (loadingFastScale (-1) (P t)).1 +
            nodeL1Norm (loadingFastScale (-1) (P t)).2) +
          (nodeSupNorm (loadingFastScale (-1) (C t)).1 +
            nodeL1Norm (loadingFastScale (-1) (C t)).2) := by
        simpa [I] using loadingFastGauge_add_le N
          (loadingFastScale (-1) (P t)) (loadingFastScale (-1) (C t))
      _ ≤ (s * J0 + s ^ 2 * B0 * K0) * G := by
        calc
          _ ≤ (s * J0 * G) + (s ^ 2 * B0 * K0 * G) :=
            add_le_add (hPneg.trans hPbound) (hCneg.trans hCbound)
          _ = (s * J0 + s ^ 2 * B0 * K0) * G := by ring
      _ = d * (nodeSupNorm (E t) + nodeL1Norm (K t)) := by rfl
  apply loading_fast_product_geometric_of_relative_innovation
    N M (loadingTransverseRate N) d hM
      (by unfold loadingTransverseRate loadingFastRate loadingTriangularRate
          linarith [mixingRate_nonneg N])
      (by dsimp [d]; positivity) htriangular (by simpa [d] using hcap)
      E K (fun t => (I t).1) (fun t => (I t).2) k hEinit hKinit
      (fun t _ => hIcarrier t) (fun t hkt => hIgauge t hkt)
  exact hstepI

/-- The homogeneous fast operator in equation (47), with both self terms
included and only the external slow forcing removed. -/
noncomputable def actualQuadraticHomogeneousFastStep
    (N : NetworkSetup n) (s : ℝ) (t : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  loadingFastStep N t F -
    loadingFastScale s
      (loadingFastPerturbationInput N t F.1 F.2) -
    loadingFastScale s
      (loadingFastScale s
        (loadingFastCenterInput N t
          (actualQuadraticCorrectedLift N t F)))

/-- Homogeneous equation-(47) evolution started at absolute time `k`. -/
noncomputable def actualQuadraticHomogeneousFastOrbit
    (N : NetworkSetup n) (s : ℝ) (k : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => F
  | m + 1 => actualQuadraticHomogeneousFastStep N s (k + m)
      (actualQuadraticHomogeneousFastOrbit N s k F m)

@[simp] theorem actualQuadraticHomogeneousFastOrbit_zero
    (N : NetworkSetup n) (s : ℝ) (k : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) :
    actualQuadraticHomogeneousFastOrbit N s k F 0 = F := rfl

@[simp] theorem actualQuadraticHomogeneousFastOrbit_succ
    (N : NetworkSetup n) (s : ℝ) (k m : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ)) :
    actualQuadraticHomogeneousFastOrbit N s k F (m + 1) =
      actualQuadraticHomogeneousFastStep N s (k + m)
        (actualQuadraticHomogeneousFastOrbit N s k F m) := rfl

theorem actualQuadraticHomogeneousFastStep_invariants
    (N : NetworkSetup n) (s : ℝ) (hs : 0 ≤ s) (t : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N t) F.1 = 0)
    (hK : (∑ i, F.2 i) = 0) :
    dotProduct (absoluteProbability N (t + 1))
        (actualQuadraticHomogeneousFastStep N s t F).1 = 0 ∧
      (∑ i, (actualQuadraticHomogeneousFastStep N s t F).2 i) = 0 := by
  let A := loadingFastStep N t F
  let P := loadingFastScale s
    (loadingFastPerturbationInput N t F.1 F.2)
  let C := loadingFastScale s
    (loadingFastScale s
      (loadingFastCenterInput N t
        (actualQuadraticCorrectedLift N t F)))
  have hA := loadingFastStep_invariants N t F.1 F.2 hE hK
  have hP0 := loadingFastPerturbationInput_spec N t F.1 F.2
  have hP := loadingFastScale_invariants_bound N (t + 1) s hs
    (loadingFastPerturbationInput N t F.1 F.2) hP0.1 hP0.2.1
  have hC0 := loadingFastCenterInput_invariants N t
    (actualQuadraticCorrectedLift N t F)
  have hC1 := loadingFastScale_invariants_bound N (t + 1) s hs
    (loadingFastCenterInput N t (actualQuadraticCorrectedLift N t F))
    hC0.1 hC0.2
  have hC := loadingFastScale_invariants_bound N (t + 1) s hs
    (loadingFastScale s
      (loadingFastCenterInput N t (actualQuadraticCorrectedLift N t F)))
    hC1.1 hC1.2.1
  constructor
  · change dotProduct (absoluteProbability N (t + 1))
      (A.1 - P.1 - C.1) = 0
    unfold dotProduct
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    change dotProduct (absoluteProbability N (t + 1)) A.1 -
        dotProduct (absoluteProbability N (t + 1)) P.1 -
        dotProduct (absoluteProbability N (t + 1)) C.1 = 0
    rw [show dotProduct (absoluteProbability N (t + 1)) A.1 = 0 by
        simpa [A] using hA.1,
      show dotProduct (absoluteProbability N (t + 1)) P.1 = 0 by
        simpa [P] using hP.1,
      show dotProduct (absoluteProbability N (t + 1)) C.1 = 0 by
        simpa [C] using hC.1]
    ring
  · change (∑ i, (A.2 - P.2 - C.2) i) = 0
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [show (∑ i, A.2 i) = 0 by simpa [A] using hA.2,
      show (∑ i, P.2 i) = 0 by simpa [P] using hP.2.1,
      show (∑ i, C.2 i) = 0 by simpa [C] using hC.2.1]
    ring

theorem actualQuadraticHomogeneousFastOrbit_invariants
    (N : NetworkSetup n) (s : ℝ) (hs : 0 ≤ s) (k m : ℕ)
    (F : (Fin n → ℝ) × (Fin n → ℝ))
    (hE : dotProduct (absoluteProbability N k) F.1 = 0)
    (hK : (∑ i, F.2 i) = 0) :
    dotProduct (absoluteProbability N (k + m))
        (actualQuadraticHomogeneousFastOrbit N s k F m).1 = 0 ∧
      (∑ i, (actualQuadraticHomogeneousFastOrbit N s k F m).2 i) = 0 := by
  induction m with
  | zero => simpa using And.intro hE hK
  | succ m ihm =>
      simpa [show k + (m + 1) = k + m + 1 by omega] using
        actualQuadraticHomogeneousFastStep_invariants N s hs (k + m)
          (actualQuadraticHomogeneousFastOrbit N s k F m) ihm.1 ihm.2

theorem actualQuadraticHomogeneousFastStep_add
    (N : NetworkSetup n) (s : ℝ) (t : ℕ)
    (F G : (Fin n → ℝ) × (Fin n → ℝ))
    (hFE : dotProduct (absoluteProbability N t) F.1 = 0)
    (hFK : (∑ i, F.2 i) = 0)
    (hGE : dotProduct (absoluteProbability N t) G.1 = 0)
    (hGK : (∑ i, G.2 i) = 0) :
    actualQuadraticHomogeneousFastStep N s t (F + G) =
      actualQuadraticHomogeneousFastStep N s t F +
        actualQuadraticHomogeneousFastStep N s t G := by
  have hLift := actualQuadraticCorrectedLift_add N t
    F.1 F.2 G.1 G.2 hFE hFK hGE hGK
  have hLift' : actualQuadraticCorrectedLift N t (F + G) =
      actualQuadraticCorrectedLift N t F +
        actualQuadraticCorrectedLift N t G := by
    simpa using hLift
  have hdot : dotProduct (absoluteProbability N (t + 1))
      ((F.1 + G.1) + (F.2 + G.2)) =
      dotProduct (absoluteProbability N (t + 1)) (F.1 + F.2) +
        dotProduct (absoluteProbability N (t + 1)) (G.1 + G.2) := by
    unfold dotProduct
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  apply Prod.ext <;> funext q <;>
    simp [actualQuadraticHomogeneousFastStep, loadingFastStep,
      loadingFastScale, loadingFastPerturbationInput,
      loadingFastCenterInput, Matrix.mulVec_add,
      Finset.sum_add_distrib, hLift', hdot] <;> ring

theorem actualQuadraticHomogeneousFastOrbit_add
    (N : NetworkSetup n) (s : ℝ) (hs : 0 ≤ s) (k m : ℕ)
    (F G : (Fin n → ℝ) × (Fin n → ℝ))
    (hFE : dotProduct (absoluteProbability N k) F.1 = 0)
    (hFK : (∑ i, F.2 i) = 0)
    (hGE : dotProduct (absoluteProbability N k) G.1 = 0)
    (hGK : (∑ i, G.2 i) = 0) :
    actualQuadraticHomogeneousFastOrbit N s k (F + G) m =
      actualQuadraticHomogeneousFastOrbit N s k F m +
        actualQuadraticHomogeneousFastOrbit N s k G m := by
  induction m with
  | zero => rfl
  | succ m ihm =>
      rw [actualQuadraticHomogeneousFastOrbit_succ,
        actualQuadraticHomogeneousFastOrbit_succ,
        actualQuadraticHomogeneousFastOrbit_succ, ihm]
      have hF := actualQuadraticHomogeneousFastOrbit_invariants
        N s hs k m F hFE hFK
      have hG := actualQuadraticHomogeneousFastOrbit_invariants
        N s hs k m G hGE hGK
      exact actualQuadraticHomogeneousFastStep_add N s (k + m)
        (actualQuadraticHomogeneousFastOrbit N s k F m)
        (actualQuadraticHomogeneousFastOrbit N s k G m)
        hF.1 hF.2 hG.1 hG.2

theorem actualQuadraticFastCarrier_finset_sum
    (N : NetworkSetup n) (t : ℕ) {ι : Type*} (S : Finset ι)
    (F : ι → (Fin n → ℝ) × (Fin n → ℝ))
    (hF : ∀ r ∈ S,
      dotProduct (absoluteProbability N t) (F r).1 = 0 ∧
        (∑ i, (F r).2 i) = 0) :
    dotProduct (absoluteProbability N t) (∑ r ∈ S, F r).1 = 0 ∧
      (∑ i, (∑ r ∈ S, F r).2 i) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [dotProduct]
  | @insert a S ha ih =>
      have haC := hF a (Finset.mem_insert_self a S)
      have hSC := ih (fun r hr => hF r (Finset.mem_insert_of_mem hr))
      constructor
      · simp only [Finset.sum_insert, ha, not_false_eq_true, Prod.fst_add]
        rw [dotProduct_add, haC.1, hSC.1, add_zero]
      · simp only [Finset.sum_insert, ha, not_false_eq_true, Prod.snd_add,
          Pi.add_apply, Finset.sum_add_distrib]
        rw [haC.2, hSC.2, add_zero]

theorem actualQuadraticHomogeneousFastStep_sum
    (N : NetworkSetup n) (s : ℝ) (t : ℕ) {ι : Type*}
    (S : Finset ι) (F : ι → (Fin n → ℝ) × (Fin n → ℝ))
    (hF : ∀ r ∈ S,
      dotProduct (absoluteProbability N t) (F r).1 = 0 ∧
        (∑ i, (F r).2 i) = 0) :
    actualQuadraticHomogeneousFastStep N s t (∑ r ∈ S, F r) =
      ∑ r ∈ S, actualQuadraticHomogeneousFastStep N s t (F r) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hLift0 : actualQuadraticCorrectedLift N t (0, 0) = 0 := by
        have h := actualQuadraticCorrectedLift_scale N t 0 (0, 0)
        simpa [loadingFastScale] using h
      have hLift0' : actualQuadraticCorrectedLift N t
          (0 : (Fin n → ℝ) × (Fin n → ℝ)) = 0 := by
        simpa using hLift0
      apply Prod.ext <;> funext q <;>
        simp [actualQuadraticHomogeneousFastStep, loadingFastStep,
          loadingFastScale, loadingFastPerturbationInput,
          loadingFastCenterInput, dotProduct, hLift0']
  | @insert a S ha ih =>
      have haC := hF a (Finset.mem_insert_self a S)
      have hrest : ∀ r ∈ S,
          dotProduct (absoluteProbability N t) (F r).1 = 0 ∧
            (∑ i, (F r).2 i) = 0 :=
        fun r hr => hF r (Finset.mem_insert_of_mem hr)
      have hsum := actualQuadraticFastCarrier_finset_sum N t S F hrest
      simp only [Finset.sum_insert, ha, not_false_eq_true]
      rw [actualQuadraticHomogeneousFastStep_add N s t (F a)
        (∑ r ∈ S, F r) haC.1 haC.2 hsum.1 hsum.2, ih hrest]

/-- Carrier-aware variation of constants for the full homogeneous
equation-(47) operator.  Each forcing inserted at time `r` is propagated from
the shifted carrier at `r+1`. -/
theorem actualQuadraticHomogeneousFast_duhamel_on_Ico
    (N : NetworkSetup n) (s : ℝ) (hs : 0 ≤ s)
    (F I : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k T : ℕ)
    (hkT : k ≤ T)
    (hFcenter : dotProduct (absoluteProbability N k) (F k).1 = 0)
    (hFzero : (∑ i, (F k).2 i) = 0)
    (hI : ∀ r ∈ Finset.Ico k T,
      dotProduct (absoluteProbability N (r + 1)) (I r).1 = 0 ∧
        (∑ i, (I r).2 i) = 0)
    (hstep : ∀ r, k ≤ r → r < T →
      F (r + 1) = actualQuadraticHomogeneousFastStep N s r (F r) + I r) :
    F T = actualQuadraticHomogeneousFastOrbit N s k (F k) (T - k) +
      ∑ r ∈ Finset.Ico k T,
        actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
          (T - r - 1) := by
  classical
  induction T generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      simp
  | succ t ih =>
      by_cases hEq : k = t + 1
      · subst k
        simp
      · have hkt : k ≤ t := by omega
        have hstep' : ∀ r, k ≤ r → r < t →
            F (r + 1) =
              actualQuadraticHomogeneousFastStep N s r (F r) + I r := by
          intro r hkr hrt
          exact hstep r hkr (by omega)
        have hI' : ∀ r ∈ Finset.Ico k t,
            dotProduct (absoluteProbability N (r + 1)) (I r).1 = 0 ∧
              (∑ i, (I r).2 i) = 0 := by
          intro r hr
          rcases Finset.mem_Ico.mp hr with ⟨hkr, hrt⟩
          exact hI r (Finset.mem_Ico.mpr ⟨hkr, by omega⟩)
        rw [hstep t hkt (by omega),
          ih k hkt hFcenter hFzero hI' hstep']
        let O0 := actualQuadraticHomogeneousFastOrbit N s k (F k) (t - k)
        let OI : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun r =>
          actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
            (t - r - 1)
        have hO0 : dotProduct (absoluteProbability N t) O0.1 = 0 ∧
            (∑ i, O0.2 i) = 0 := by
          have h := actualQuadraticHomogeneousFastOrbit_invariants
            N s hs k (t - k) (F k) hFcenter hFzero
          simpa [O0, show k + (t - k) = t by omega] using h
        have hOI : ∀ r ∈ Finset.Ico k t,
            dotProduct (absoluteProbability N t) (OI r).1 = 0 ∧
              (∑ i, (OI r).2 i) = 0 := by
          intro r hr
          rcases Finset.mem_Ico.mp hr with ⟨hkr, hrt⟩
          have hrI := hI' r hr
          have h := actualQuadraticHomogeneousFastOrbit_invariants
            N s hs (r + 1) (t - r - 1) (I r) hrI.1 hrI.2
          simpa [OI, show r + 1 + (t - r - 1) = t by
            omega] using h
        have hsumCarrier := actualQuadraticFastCarrier_finset_sum
          N t (Finset.Ico k t) OI hOI
        rw [actualQuadraticHomogeneousFastStep_add N s t O0
          (∑ r ∈ Finset.Ico k t, OI r)
          hO0.1 hO0.2 hsumCarrier.1 hsumCarrier.2]
        rw [actualQuadraticHomogeneousFastStep_sum N s t
          (Finset.Ico k t) OI hOI]
        have hinitial : actualQuadraticHomogeneousFastStep N s t O0 =
            actualQuadraticHomogeneousFastOrbit N s k (F k) (t + 1 - k) := by
          rw [show t + 1 - k = (t - k) + 1 by omega,
            actualQuadraticHomogeneousFastOrbit_succ,
            show k + (t - k) = t by omega]
        rw [hinitial]
        have hterm (r : ℕ) (hr : r ∈ Finset.Ico k t) :
            actualQuadraticHomogeneousFastStep N s t (OI r) =
              actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
                (t + 1 - r - 1) := by
          have hrt := (Finset.mem_Ico.mp hr).2
          rw [show t + 1 - r - 1 = (t - r - 1) + 1 by omega,
            actualQuadraticHomogeneousFastOrbit_succ,
            show r + 1 + (t - r - 1) = t by omega]
        have hsum :
            (∑ r ∈ Finset.Ico k t,
              actualQuadraticHomogeneousFastStep N s t (OI r)) =
              ∑ r ∈ Finset.Ico k t,
                actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
                  (t + 1 - r - 1) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hterm r hr
        have hzeroexp : t + 1 - t - 1 = 0 := by omega
        rw [hsum, Finset.sum_Ico_succ_top hkt, hzeroexp,
          actualQuadraticHomogeneousFastOrbit_zero]
        abel

/-- Forced fast estimate from equation (47).  The full homogeneous operator
is propagated at rate `loadingTransverseRate`; only the external
`-s B_t z_t` input remains in the convolution. -/
theorem actual_quadratic_forced_fast_duhamel_bound
    (N : NetworkSetup n) (M s : ℝ) (hM : 1 ≤ M) (hs : 0 ≤ s)
    (K0 J0 B0 : ℝ) (hK0 : 0 ≤ K0) (hJ0 : 0 ≤ J0)
    (hB0 : 0 ≤ B0)
    (hK : ∀ (t : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N t) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N t (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K))
    (hJ : ∀ (t : ℕ) (E K : Fin n → ℝ),
      nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
        J0 * (nodeSupNorm E + nodeL1Norm K))
    (hB : ∀ (t : ℕ) (z : ℝ),
      nodeSupNorm (loadingFastCenterInput N t z).1 +
          nodeL1Norm (loadingFastCenterInput N t z).2 ≤ B0 * |z|)
    (htriangular : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K)) :
    ∀ (hcap : loadingFastRate N +
          M * (s * J0 + s ^ 2 * B0 * K0) ≤ loadingTransverseRate N)
        (z : ℕ → ℝ)
        (F : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k m : ℕ),
        dotProduct (absoluteProbability N k) (F k).1 = 0 →
        (∑ i, (F k).2 i) = 0 →
        (∀ t, k ≤ t →
          F (t + 1) = actualQuadraticHomogeneousFastStep N s t (F t) -
            loadingFastScale s (loadingFastCenterInput N t (z t))) →
        nodeSupNorm (F (k + m)).1 + nodeL1Norm (F (k + m)).2 ≤
          M * loadingTransverseRate N ^ m *
              (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
            (s * M * B0) *
              ∑ i ∈ Finset.range m,
                loadingTransverseRate N ^ (m - i - 1) * |z (k + i)| := by
  have hproduct := actual_quadratic_fast_product_geometric
    N M s hM hs K0 J0 B0 hK0 hJ0 hB0 hK hJ hB htriangular
  intro hcap z F k m hFcenter hFzero hstep
  have horbit (a d : ℕ)
      (Z : (Fin n → ℝ) × (Fin n → ℝ))
      (hZE : dotProduct (absoluteProbability N a) Z.1 = 0)
      (hZK : (∑ i, Z.2 i) = 0) :
      nodeSupNorm (actualQuadraticHomogeneousFastOrbit N s a Z d).1 +
          nodeL1Norm (actualQuadraticHomogeneousFastOrbit N s a Z d).2 ≤
        M * loadingTransverseRate N ^ d *
          (nodeSupNorm Z.1 + nodeL1Norm Z.2) := by
    let O := actualQuadraticHomogeneousFastOrbit N s a Z
    let E : ℕ → Fin n → ℝ := fun t =>
      if a ≤ t then (O (t - a)).1 else Z.1
    let K : ℕ → Fin n → ℝ := fun t =>
      if a ≤ t then (O (t - a)).2 else Z.2
    have hEa : E a = Z.1 := by simp [E, O]
    have hKa : K a = Z.2 := by simp [K, O]
    have hrec (t : ℕ) (hat : a ≤ t) :
        (E (t + 1), K (t + 1)) =
          loadingFastStep N t (E t, K t) -
            loadingFastScale s
              (loadingFastPerturbationInput N t (E t) (K t)) -
            loadingFastScale s
              (loadingFastScale s
                (loadingFastCenterInput N t
                  (actualQuadraticCorrectedLift N t (E t, K t)))) := by
      have hsucc : t + 1 - a = (t - a) + 1 := by omega
      have htime : a + (t - a) = t := by omega
      simp only [E, K, if_pos hat, if_pos (by omega : a ≤ t + 1)]
      rw [hsucc]
      change actualQuadraticHomogeneousFastOrbit N s a Z (t - a + 1) =
        actualQuadraticHomogeneousFastStep N s t
          (actualQuadraticHomogeneousFastOrbit N s a Z (t - a))
      rw [actualQuadraticHomogeneousFastOrbit_succ, htime]
    have hbound := hproduct hcap E K a
      (by simpa [hEa] using hZE) (by simpa [hKa] using hZK) hrec
      (a + d) (by omega)
    simpa [E, K, O] using hbound
  let I : ℕ → (Fin n → ℝ) × (Fin n → ℝ) := fun t =>
    loadingFastScale (-1)
      (loadingFastScale s (loadingFastCenterInput N t (z t)))
  have hIcarrier (t : ℕ) :
      dotProduct (absoluteProbability N (t + 1)) (I t).1 = 0 ∧
        (∑ i, (I t).2 i) = 0 := by
    have hB0t := loadingFastCenterInput_invariants N t (z t)
    have hBs := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastCenterInput N t (z t)) hB0t.1 hB0t.2
    constructor
    · unfold dotProduct at hBs ⊢
      simpa [I, loadingFastScale] using congrArg Neg.neg hBs.1
    · simpa [I, loadingFastScale] using congrArg Neg.neg hBs.2.1
  have hIgauge (t : ℕ) :
      nodeSupNorm (I t).1 + nodeL1Norm (I t).2 ≤
        s * B0 * |z t| := by
    have hB0t := loadingFastCenterInput_invariants N t (z t)
    have hBs := loadingFastScale_invariants_bound N (t + 1) s hs
      (loadingFastCenterInput N t (z t)) hB0t.1 hB0t.2
    have hneg := loadingFastScale_gauge_le_abs N (-1)
      (loadingFastScale s (loadingFastCenterInput N t (z t)))
    norm_num at hneg
    calc
      nodeSupNorm (I t).1 + nodeL1Norm (I t).2 ≤
          nodeSupNorm
              (loadingFastScale s (loadingFastCenterInput N t (z t))).1 +
            nodeL1Norm
              (loadingFastScale s (loadingFastCenterInput N t (z t))).2 := by
        simpa [I] using hneg
      _ ≤ s * (nodeSupNorm (loadingFastCenterInput N t (z t)).1 +
            nodeL1Norm (loadingFastCenterInput N t (z t)).2) := hBs.2.2
      _ ≤ s * (B0 * |z t|) :=
        mul_le_mul_of_nonneg_left (hB t (z t)) hs
      _ = s * B0 * |z t| := by ring
  have hstepI (t : ℕ) (hkt : k ≤ t) :
      F (t + 1) = actualQuadraticHomogeneousFastStep N s t (F t) + I t := by
    rw [hstep t hkt]
    apply Prod.ext <;> funext q <;>
      simp [I, loadingFastScale] <;> ring
  let T := k + m
  have hduhamel := actualQuadraticHomogeneousFast_duhamel_on_Ico
    N s hs F I k T (by dsimp [T]; omega) hFcenter hFzero
      (fun r _ => hIcarrier r)
      (fun r hkr _ => hstepI r hkr)
  let Z0 := actualQuadraticHomogeneousFastOrbit N s k (F k) (T - k)
  let Zsum := ∑ r ∈ Finset.Ico k T,
    actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r) (T - r - 1)
  have hbase : nodeSupNorm Z0.1 + nodeL1Norm Z0.2 ≤
      M * loadingTransverseRate N ^ (T - k) *
        (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) := by
    simpa [Z0] using horbit k (T - k) (F k) hFcenter hFzero
  have hzsum_fst : Zsum.1 =
      ∑ r ∈ Finset.Ico k T,
        (actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
          (T - r - 1)).1 := by
    classical
    dsimp [Zsum]
    induction Finset.Ico k T using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [ha, ih]
  have hzsum_snd : Zsum.2 =
      ∑ r ∈ Finset.Ico k T,
        (actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
          (T - r - 1)).2 := by
    classical
    dsimp [Zsum]
    induction Finset.Ico k T using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp [ha, ih]
  have hresponse : nodeSupNorm Zsum.1 + nodeL1Norm Zsum.2 ≤
      ∑ r ∈ Finset.Ico k T,
        (nodeSupNorm
            (actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
              (T - r - 1)).1 +
          nodeL1Norm
            (actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
              (T - r - 1)).2) := by
    rw [hzsum_fst, hzsum_snd]
    exact loadingFastGauge_finset_sum_le N (Finset.Ico k T)
      (fun r => actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
        (T - r - 1))
  have hterms :
      (∑ r ∈ Finset.Ico k T,
        (nodeSupNorm
            (actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
              (T - r - 1)).1 +
          nodeL1Norm
            (actualQuadraticHomogeneousFastOrbit N s (r + 1) (I r)
              (T - r - 1)).2)) ≤
        ∑ r ∈ Finset.Ico k T,
          M * loadingTransverseRate N ^ (T - r - 1) *
            (s * B0 * |z r|) := by
    apply Finset.sum_le_sum
    intro r hr
    have horb := horbit (r + 1) (T - r - 1) (I r)
      (hIcarrier r).1 (hIcarrier r).2
    have hcoeff : 0 ≤ M * loadingTransverseRate N ^ (T - r - 1) := by
      have hrate : 0 ≤ loadingTransverseRate N := by
        unfold loadingTransverseRate loadingFastRate loadingTriangularRate
        linarith [mixingRate_nonneg N]
      exact mul_nonneg (by linarith) (pow_nonneg hrate _)
    exact horb.trans (mul_le_mul_of_nonneg_left (hIgauge r) hcoeff)
  have hraw : nodeSupNorm (F T).1 + nodeL1Norm (F T).2 ≤
      M * loadingTransverseRate N ^ (T - k) *
          (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
        ∑ r ∈ Finset.Ico k T,
          M * loadingTransverseRate N ^ (T - r - 1) *
            (s * B0 * |z r|) := by
    rw [hduhamel]
    change nodeSupNorm (Z0 + Zsum).1 + nodeL1Norm (Z0 + Zsum).2 ≤ _
    exact (loadingFastGauge_add_le N Z0 Zsum).trans
      (add_le_add hbase (hresponse.trans hterms))
  calc
    nodeSupNorm (F (k + m)).1 + nodeL1Norm (F (k + m)).2 =
        nodeSupNorm (F T).1 + nodeL1Norm (F T).2 := by rfl
    _ ≤ M * loadingTransverseRate N ^ (T - k) *
          (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
        ∑ r ∈ Finset.Ico k T,
          M * loadingTransverseRate N ^ (T - r - 1) *
            (s * B0 * |z r|) := hraw
    _ = M * loadingTransverseRate N ^ m *
          (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
        (s * M * B0) *
          ∑ i ∈ Finset.range m,
            loadingTransverseRate N ^ (m - i - 1) * |z (k + i)| := by
      dsimp [T]
      rw [Finset.sum_Ico_eq_sum_range,
        show k + m - k = m by omega, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · rfl
      · apply Finset.sum_congr rfl
        intro i hi
        rw [show k + m - (k + i) - 1 = m - i - 1 by omega]
        ring

/-- The separated-rate convolution used twice in the equation-(48)
bootstrap.  Its denominator is the spectral gap `q-r`; retaining that gap is
what keeps the fast impulse tail visible after the slow/fast split. -/
theorem sum_range_separated_geometric_convolution_le
    (r q : ℝ) (hr : 0 ≤ r) (hrq : r < q) (m : ℕ) :
    (∑ i ∈ Finset.range m, r ^ (m - i - 1) * q ^ i) ≤
      q ^ m / (q - r) := by
  have hgap : 0 < q - r := sub_pos.mpr hrq
  have hq : 0 ≤ q := hr.trans (le_of_lt hrq)
  have hid : ∀ k : ℕ,
      (q - r) * (∑ i ∈ Finset.range k,
        r ^ (k - i - 1) * q ^ i) = q ^ k - r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hprefix :
            (∑ i ∈ Finset.range k,
              r ^ (k + 1 - i - 1) * q ^ i) =
              r * ∑ i ∈ Finset.range k,
                r ^ (k - i - 1) * q ^ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hik : i < k := Finset.mem_range.mp hi
          have hexp : k + 1 - i - 1 = (k - i - 1) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        rw [Finset.sum_range_succ, hprefix]
        have hlast : r ^ (k + 1 - k - 1) * q ^ k = q ^ k := by simp
        rw [hlast, mul_add]
        calc
          (q - r) * (r * ∑ i ∈ Finset.range k,
                r ^ (k - i - 1) * q ^ i) + (q - r) * q ^ k =
              r * ((q - r) * ∑ i ∈ Finset.range k,
                r ^ (k - i - 1) * q ^ i) + (q - r) * q ^ k := by ring
          _ = r * (q ^ k - r ^ k) + (q - r) * q ^ k := by rw [ih]
          _ = q ^ (k + 1) - r ^ (k + 1) := by
            rw [pow_succ, pow_succ]
            ring
  have heq :
      (∑ i ∈ Finset.range m, r ^ (m - i - 1) * q ^ i) =
        (q ^ m - r ^ m) / (q - r) := by
    apply (eq_div_iff hgap.ne').2
    simpa [mul_comm] using hid m
  rw [heq]
  apply (div_le_div_iff_of_pos_right hgap).2
  exact sub_le_self _ (pow_nonneg hr m)

/-- The forced fast estimate in the weighted slow coordinates used for
`Z_m`.  The pointwise slow envelope is obtained from the actual finite
maximum, rather than assumed. -/
theorem actual_quadratic_forced_fast_Zmax_bound
    (N : NetworkSetup n) (M s : ℝ) (hM : 1 ≤ M) (hs : 0 ≤ s)
    (K0 J0 B0 : ℝ) (hK0 : 0 ≤ K0) (hJ0 : 0 ≤ J0)
    (hB0 : 0 ≤ B0)
    (hK : ∀ (t : ℕ) (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N t) E = 0 →
      (∑ i, K i) = 0 →
      |actualQuadraticCorrectedLift N t (E, K)| ≤
        K0 * (nodeSupNorm E + nodeL1Norm K))
    (hJ : ∀ (t : ℕ) (E K : Fin n → ℝ),
      nodeSupNorm (loadingFastPerturbationInput N t E K).1 +
          nodeL1Norm (loadingFastPerturbationInput N t E K).2 ≤
        J0 * (nodeSupNorm E + nodeL1Norm K))
    (hB : ∀ (t : ℕ) (z : ℝ),
      nodeSupNorm (loadingFastCenterInput N t z).1 +
          nodeL1Norm (loadingFastCenterInput N t z).2 ≤ B0 * |z|)
    (htriangular : ∀ (k t : ℕ), k ≤ t → ∀ (E K : Fin n → ℝ),
      dotProduct (absoluteProbability N k) E = 0 →
      (∑ i, K i) = 0 →
      nodeSupNorm (forwardProduct N.rowMix t k *ᵥ E) +
          nodeL1Norm
            (forwardProduct N.colMix t k *ᵥ K +
              ∑ q ∈ Finset.Ico k t,
                forwardProduct N.colMix t (q + 1) *ᵥ
                  ((N.colMix q - 1) *ᵥ
                    (forwardProduct N.rowMix q k *ᵥ E))) ≤
        M * loadingFastRate N ^ (t - k) *
          (nodeSupNorm E + nodeL1Norm K)) :
    ∀ (q : ℝ), 0 < q → loadingTransverseRate N < q →
      ∀ (hcap : loadingFastRate N +
          M * (s * J0 + s ^ 2 * B0 * K0) ≤ loadingTransverseRate N)
        (z : ℕ → ℝ)
        (F : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k m : ℕ),
        dotProduct (absoluteProbability N k) (F k).1 = 0 →
        (∑ i, (F k).2 i) = 0 →
        (∀ t, k ≤ t →
          F (t + 1) = actualQuadraticHomogeneousFastStep N s t (F t) -
            loadingFastScale s (loadingFastCenterInput N t (z t))) →
        let u : ℕ → ℝ := fun i => |z (k + i)| / q ^ i
        ∀ hS : ((Finset.range (m + 1)).image u).Nonempty,
          nodeSupNorm (F (k + m)).1 + nodeL1Norm (F (k + m)).2 ≤
            M * loadingTransverseRate N ^ m *
                (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
              (s * M * B0 / (q - loadingTransverseRate N)) *
                ((Finset.range (m + 1)).image u).max' hS * q ^ m := by
  have hforced := actual_quadratic_forced_fast_duhamel_bound
    N M s hM hs K0 J0 B0 hK0 hJ0 hB0 hK hJ hB htriangular
  intro q hq hrateq hcap z F k m hFcenter hFzero hstep
  dsimp only
  intro hS
  let u : ℕ → ℝ := fun i => |z (k + i)| / q ^ i
  change ((Finset.range (m + 1)).image u).Nonempty at hS
  let Zm := ((Finset.range (m + 1)).image u).max' hS
  have hrate_nonneg : 0 ≤ loadingTransverseRate N := by
    unfold loadingTransverseRate loadingFastRate loadingTriangularRate
    linarith [mixingRate_nonneg N]
  have hZm_nonneg : 0 ≤ Zm := by
    have hu0 : 0 ≤ u 0 := by
      dsimp [u]
      positivity
    have hu0mem : u 0 ∈ (Finset.range (m + 1)).image u :=
      Finset.mem_image.mpr ⟨0, by simp, rfl⟩
    exact hu0.trans (Finset.le_max' _ _ hu0mem)
  have hz (i : ℕ) (hi : i ∈ Finset.range m) :
      |z (k + i)| ≤ Zm * q ^ i := by
    have him : i ∈ Finset.range (m + 1) := by
      simp only [Finset.mem_range] at hi ⊢
      omega
    have hui : u i ≤ Zm := by
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, him, rfl⟩)
    have hqpow : 0 < q ^ i := pow_pos hq _
    have hscaled := mul_le_mul_of_nonneg_right hui hqpow.le
    simpa [u, div_mul_cancel₀ _ hqpow.ne'] using hscaled
  have hraw := hforced hcap z F k m hFcenter hFzero hstep
  have hsum :
      (∑ i ∈ Finset.range m,
        loadingTransverseRate N ^ (m - i - 1) * |z (k + i)|) ≤
        Zm * ∑ i ∈ Finset.range m,
          loadingTransverseRate N ^ (m - i - 1) * q ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hcoeff : 0 ≤ loadingTransverseRate N ^ (m - i - 1) :=
      pow_nonneg hrate_nonneg _
    calc
      loadingTransverseRate N ^ (m - i - 1) * |z (k + i)| ≤
          loadingTransverseRate N ^ (m - i - 1) * (Zm * q ^ i) :=
        mul_le_mul_of_nonneg_left (hz i hi) hcoeff
      _ = Zm *
          (loadingTransverseRate N ^ (m - i - 1) * q ^ i) := by ring
  have hconv := sum_range_separated_geometric_convolution_le
    (loadingTransverseRate N) q hrate_nonneg hrateq m
  have hsum' :
      (∑ i ∈ Finset.range m,
        loadingTransverseRate N ^ (m - i - 1) * |z (k + i)|) ≤
        Zm * (q ^ m / (q - loadingTransverseRate N)) :=
    hsum.trans (mul_le_mul_of_nonneg_left hconv hZm_nonneg)
  have hsMB : 0 ≤ s * M * B0 := by positivity
  calc
    nodeSupNorm (F (k + m)).1 + nodeL1Norm (F (k + m)).2 ≤
        M * loadingTransverseRate N ^ m *
            (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
          (s * M * B0) *
            ∑ i ∈ Finset.range m,
              loadingTransverseRate N ^ (m - i - 1) * |z (k + i)| := hraw
    _ ≤ M * loadingTransverseRate N ^ m *
            (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
          (s * M * B0) *
            (Zm * (q ^ m / (q - loadingTransverseRate N))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum' hsMB)
    _ = M * loadingTransverseRate N ^ m *
            (nodeSupNorm (F k).1 + nodeL1Norm (F k).2) +
          (s * M * B0 / (q - loadingTransverseRate N)) *
            ((Finset.range (m + 1)).image u).max' hS * q ^ m := by
      dsimp [Zm]
      ring

/-- Coordinatewise specialization of equation (46) for a genuinely
one-dimensional state.  Besides projecting the two vector recurrences, this
proves the tracker carrier invariant needed by the corrected equation-(47)
bridge, rather than assuming it separately. -/
theorem actual_quadratic_scalar_equation47_of_recurrence
    (N : NetworkSetup n) (s : ℝ)
    (XV UV eV : ℕ → NodeTable n 1)
    (hUVzero : UV 0 = 0)
    (hstep : ∀ t,
      XV (t + 1) =
          leftAct (N.rowMix t - s • 1) (XV t) - s • UV t - s • eV t ∧
      UV (t + 1) =
          leftAct (N.colMix t - 1) (XV t) +
            leftAct (N.colMix t) (UV t) +
            leftAct (N.colMix t - 1) (eV t)) :
    let X : ℕ → Fin n → ℝ := fun r i => XV r i (0 : Fin 1)
    let U : ℕ → Fin n → ℝ := fun r i => UV r i (0 : Fin 1)
    let e : ℕ → Fin n → ℝ := fun r i => eV r i (0 : Fin 1)
    let xi := loadingSlowCenter N X
    let F := loadingFastCoordinates N X U
    let zq : ℕ → ℝ := fun r =>
      xi r - s * actualQuadraticCorrectedLift N r (F r)
    (∀ r, (∑ q, U r q) = 0) ∧
    ∀ t,
      (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
        (∑ q, (F t).2 q) = 0) ∧
      zq (t + 1) =
        (1 - s * gain N t) * zq t + s ^ 2 *
          (-gain N t * actualQuadraticCorrectedLift N t (F t) +
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastPerturbationInput N t (F t).1 (F t).2) +
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t (zq t)) +
            s * actualQuadraticCorrectedLift N (t + 1)
              (loadingFastCenterInput N t
                (actualQuadraticCorrectedLift N t (F t)))) -
          s * dotProduct (influenceRow N t) (e t) + s ^ 2 *
            actualQuadraticCorrectedLift N (t + 1)
              (loadingFastPerturbationInput N t (e t) 0) ∧
      F (t + 1) =
        loadingFastStep N t (F t) -
          loadingFastScale s
            (loadingFastPerturbationInput N t (F t).1 (F t).2) -
          loadingFastScale s (loadingFastCenterInput N t (zq t)) -
          loadingFastScale s
            (loadingFastScale s
              (loadingFastCenterInput N t
                (actualQuadraticCorrectedLift N t (F t)))) +
          (0, (N.colMix t - 1) *ᵥ e t) -
          loadingFastScale s
            (loadingFastPerturbationInput N t (e t) 0) := by
  classical
  dsimp only
  let X : ℕ → Fin n → ℝ := fun r i => XV r i (0 : Fin 1)
  let U : ℕ → Fin n → ℝ := fun r i => UV r i (0 : Fin 1)
  let e : ℕ → Fin n → ℝ := fun r i => eV r i (0 : Fin 1)
  have hXrec (t : ℕ) : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q := by
    funext q
    have hq := congrFun (hstep t).1 q
    have hc := congrArg (fun z : Point 1 => z (0 : Fin 1)) hq
    simp [X, U, e, leftAct, Matrix.smulVec_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Finset.sum_sub_distrib, Finset.smul_sum, smul_smul] at hc
    simp only [X, U, e]
    rw [hc]
    simp [X, U, e, Matrix.mulVec, dotProduct, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Finset.sum_sub_distrib,
      sub_mul]
  have hUrec (t : ℕ) : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q := by
    funext q
    have hq := congrFun (hstep t).2 q
    have hc := congrArg (fun z : Point 1 => z (0 : Fin 1)) hq
    simp [X, U, e, leftAct, Matrix.smulVec_apply,
      Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib,
      Finset.sum_add_distrib] at hc
    simp only [X, U, e]
    rw [hc]
    simp [X, U, e, Matrix.mulVec, dotProduct, Matrix.sub_apply,
      Matrix.one_apply, Finset.sum_sub_distrib, sub_mul]
    ring
  have hUzero : ∀ r, (∑ q, U r q) = 0 := by
    intro r
    induction r with
    | zero =>
        have hcoord := congrArg
          (fun Z : NodeTable n 1 => fun i => Z i (0 : Fin 1)) hUVzero
        have hU0 : U 0 = 0 := by simpa [U] using hcoord
        rw [hU0]
        simp
    | succ r ihr =>
        rw [hUrec]
        simp only [Finset.sum_add_distrib]
        have hcolU : (∑ q, (N.colMix r *ᵥ U r) q) = 0 := by
          rw [Matrix.sum_mulVec_of_mem_colStochastic
            (N.col_stochastic r), ihr]
        have hcolX : (∑ q, ((N.colMix r - 1) *ᵥ X r) q) = 0 := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
          simp only [Pi.sub_apply, Finset.sum_sub_distrib]
          rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic r)]
          ring
        have hcole : (∑ q, ((N.colMix r - 1) *ᵥ e r) q) = 0 := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec]
          simp only [Pi.sub_apply, Finset.sum_sub_distrib]
          rw [Matrix.sum_mulVec_of_mem_colStochastic (N.col_stochastic r)]
          ring
        rw [hcolU, hcolX, hcole]
        ring
  refine ⟨hUzero, ?_⟩
  intro t
  exact actual_quadratic_corrected_slow_fast_recurrence
    N s X U e t hUzero (hXrec t) (hUrec t)

/-- The noiseless slow coordinate in the corrected equation-(47) system is
contractive up to the genuine fast residual.  This is the scalar one-step
estimate used before the finite `Z_m` bootstrap. -/
theorem actual_quadratic_slow_one_step_majorant
    (N : NetworkSetup n) (Aq Lq : ℝ)
    (hAq : 0 ≤ Aq) (hLq : 0 ≤ Lq)
    (hmajor : ∀ (s : ℝ), 0 ≤ s → s ≤ 1 → ∀ (t : ℕ)
      (F : (Fin n → ℝ) × (Fin n → ℝ)),
      dotProduct (absoluteProbability N t) F.1 = 0 →
      (∑ i, F.2 i) = 0 →
      (∀ z : ℝ,
        |actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t z)| ≤ Aq * |z|) ∧
      |-gain N t * actualQuadraticCorrectedLift N t F +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t F.1 F.2) +
          s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t F))| ≤
        Lq * (nodeSupNorm F.1 + nodeL1Norm F.2)) :
      ∀ (s : ℝ), 0 ≤ s → s ≤ 1 →
        s * (n : ℝ) ≤ 1 / 4 →
        s * Aq ≤ gainFloor N / 2 →
        ∀ (X U : ℕ → Fin n → ℝ) (t : ℕ),
          (∀ r, (∑ q, U r q) = 0) →
          X (t + 1) = (fun q =>
            (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q) →
          U (t + 1) = (fun q =>
            (N.colMix t *ᵥ U t) q +
              ((N.colMix t - 1) *ᵥ X t) q) →
          let xi := loadingSlowCenter N X
          let F := loadingFastCoordinates N X U
          let zq : ℕ → ℝ := fun r =>
            xi r - s * actualQuadraticCorrectedLift N r (F r)
          |zq (t + 1)| ≤
            (1 - s * gainFloor N / 2) * |zq t| +
              s ^ 2 * Lq *
                (nodeSupNorm (F t).1 + nodeL1Norm (F t).2) := by
  intro s hs hs1 hsn hsAq X U t hUzero hXrec hUrec
  dsimp only
  let e : ℕ → Fin n → ℝ := fun _ _ => 0
  let xi := loadingSlowCenter N X
  let F := loadingFastCoordinates N X U
  let zq : ℕ → ℝ := fun r =>
    xi r - s * actualQuadraticCorrectedLift N r (F r)
  have hXrec0 : X (t + 1) = fun q =>
      (N.rowMix t *ᵥ X t) q - s * X t q - s * U t q - s * e t q := by
    simpa [e] using hXrec
  have hUrec0 : U (t + 1) = fun q =>
      (N.colMix t *ᵥ U t) q + ((N.colMix t - 1) *ᵥ X t) q +
        ((N.colMix t - 1) *ᵥ e t) q := by
    rw [hUrec]
    funext q
    simp [e, Matrix.mulVec, dotProduct]
  have hslow := actualQuadratic_corrected_slow_recurrence
    N s X U e t hUzero hXrec0 hUrec0
  change
    (dotProduct (absoluteProbability N t) (F t).1 = 0 ∧
      (∑ q, (F t).2 q) = 0) ∧
    zq (t + 1) =
      (1 - s * gain N t) * zq t + s ^ 2 *
        (-gain N t * actualQuadraticCorrectedLift N t (F t) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (F t).1 (F t).2) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t (zq t)) +
          s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) -
        s * dotProduct (influenceRow N t) (e t) + s ^ 2 *
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (e t) 0) at hslow
  have hdot0 : dotProduct (influenceRow N t) (e t) = 0 := by
    simp [e, dotProduct]
  have hinput0 : loadingFastPerturbationInput N t (e t) 0 = 0 := by
    apply Prod.ext <;> funext q <;>
      simp [e, loadingFastPerturbationInput, dotProduct]
  have hlift0 : actualQuadraticCorrectedLift N (t + 1)
      (loadingFastPerturbationInput N t (e t) 0) = 0 := by
    rw [hinput0]
    have h := actualQuadraticCorrectedLift_scale N (t + 1) 0 (0, 0)
    simpa [loadingFastScale] using h
  have hslowEq : zq (t + 1) =
      (1 - s * gain N t) * zq t + s ^ 2 *
        (-gain N t * actualQuadraticCorrectedLift N t (F t) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (F t).1 (F t).2) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t (zq t)) +
          s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) := by
    simpa [hdot0, hlift0] using hslow.2
  let R : ℝ :=
    -gain N t * actualQuadraticCorrectedLift N t (F t) +
      actualQuadraticCorrectedLift N (t + 1)
        (loadingFastPerturbationInput N t (F t).1 (F t).2) +
      s * actualQuadraticCorrectedLift N (t + 1)
        (loadingFastCenterInput N t
          (actualQuadraticCorrectedLift N t (F t)))
  let C : ℝ := actualQuadraticCorrectedLift N (t + 1)
    (loadingFastCenterInput N t (zq t))
  have hcoeff := hmajor s hs hs1 t (F t) hslow.1.1 hslow.1.2
  have hC : |C| ≤ Aq * |zq t| := by
    simpa [C] using hcoeff.1 (zq t)
  have hR : |R| ≤ Lq *
      (nodeSupNorm (F t).1 + nodeL1Norm (F t).2) := by
    simpa [R, add_assoc, add_left_comm, add_comm] using hcoeff.2
  have hbase_nonneg : 0 ≤ 1 - s * gain N t := by
    have hsgain : s * gain N t ≤ s * (n : ℝ) :=
      mul_le_mul_of_nonneg_left (gain_le_n N t) hs
    linarith
  have hslow_coeff :
      1 - s * gain N t + s ^ 2 * Aq ≤
        1 - s * gainFloor N / 2 := by
    have hscaled : s * (s * Aq) ≤ s * (gainFloor N / 2) :=
      mul_le_mul_of_nonneg_left hsAq hs
    have hgain_scaled : s * gainFloor N ≤ s * gain N t :=
      mul_le_mul_of_nonneg_left (gainFloor_le_gain N t) hs
    nlinarith
  have hcenter :
      |(1 - s * gain N t) * zq t + s ^ 2 * C| ≤
        (1 - s * gainFloor N / 2) * |zq t| := by
    calc
      |(1 - s * gain N t) * zq t + s ^ 2 * C| ≤
          |(1 - s * gain N t) * zq t| + |s ^ 2 * C| :=
        abs_add_le _ _
      _ = (1 - s * gain N t) * |zq t| + s ^ 2 * |C| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hbase_nonneg,
          abs_of_nonneg (sq_nonneg s)]
      _ ≤ (1 - s * gain N t) * |zq t| +
          s ^ 2 * (Aq * |zq t|) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (sq_nonneg s))
      _ = (1 - s * gain N t + s ^ 2 * Aq) * |zq t| := by ring
      _ ≤ (1 - s * gainFloor N / 2) * |zq t| :=
        mul_le_mul_of_nonneg_right hslow_coeff (abs_nonneg _)
  change |zq (t + 1)| ≤
    (1 - s * gainFloor N / 2) * |zq t| +
      s ^ 2 * Lq *
        (nodeSupNorm (F t).1 + nodeL1Norm (F t).2)
  rw [hslowEq]
  have hrearrange :
      (1 - s * gain N t) * zq t + s ^ 2 *
        (-gain N t * actualQuadraticCorrectedLift N t (F t) +
          actualQuadraticCorrectedLift N (t + 1)
            (loadingFastPerturbationInput N t (F t).1 (F t).2) +
          C + s * actualQuadraticCorrectedLift N (t + 1)
            (loadingFastCenterInput N t
              (actualQuadraticCorrectedLift N t (F t)))) =
        ((1 - s * gain N t) * zq t + s ^ 2 * C) + s ^ 2 * R := by
    dsimp [R]
    ring
  rw [hrearrange]
  calc
    |((1 - s * gain N t) * zq t + s ^ 2 * C) + s ^ 2 * R| ≤
        |(1 - s * gain N t) * zq t + s ^ 2 * C| + |s ^ 2 * R| :=
      abs_add_le _ _
    _ ≤ (1 - s * gainFloor N / 2) * |zq t| + s ^ 2 * |R| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
      exact add_le_add hcenter le_rfl
    _ ≤ (1 - s * gainFloor N / 2) * |zq t| +
        s ^ 2 * (Lq *
          (nodeSupNorm (F t).1 + nodeL1Norm (F t).2)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hR (sq_nonneg s))
    _ = (1 - s * gainFloor N / 2) * |zq t| +
        s ^ 2 * Lq *
          (nodeSupNorm (F t).1 + nodeL1Norm (F t).2) := by ring

/-- Iteration of a nonnegative scalar one-step majorant from an arbitrary
starting time.  This is the variation-of-constants form used to assemble the
pointwise `Z_m` premise. -/
theorem abs_slow_recurrence_geometric_unroll
    (z G : ℕ → ℝ) (k : ℕ) (q b : ℝ)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hG : ∀ t, 0 ≤ G t)
    (hstep : ∀ t, k ≤ t →
      |z (t + 1)| ≤ q * |z t| + b * G t) :
    ∀ i : ℕ,
      |z (k + i)| ≤ q ^ i * |z k| +
        b * ∑ j ∈ Finset.range i,
          q ^ (i - j - 1) * G (k + j) := by
  intro i
  induction i with
  | zero =>
      simp
  | succ i ih =>
      have hshift :
          (∑ j ∈ Finset.range i,
            q ^ (i + 1 - j - 1) * G (k + j)) =
            q * ∑ j ∈ Finset.range i,
              q ^ (i - j - 1) * G (k + j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j < i := Finset.mem_range.mp hj
        rw [show i + 1 - j - 1 = (i - j - 1) + 1 by omega, pow_succ]
        ring
      have hnew :
          q ^ (i + 1 - i - 1) * G (k + i) = G (k + i) := by simp
      calc
        |z (k + (i + 1))| = |z ((k + i) + 1)| := by
          congr 2 <;> omega
        _ ≤ q * |z (k + i)| + b * G (k + i) :=
          hstep (k + i) (by omega)
        _ ≤ q * (q ^ i * |z k| +
              b * ∑ j ∈ Finset.range i,
                q ^ (i - j - 1) * G (k + j)) + b * G (k + i) := by
          exact add_le_add (mul_le_mul_of_nonneg_left ih hq) le_rfl
        _ = q ^ (i + 1) * |z k| +
              b * ∑ j ∈ Finset.range (i + 1),
                q ^ (i + 1 - j - 1) * G (k + j) := by
          rw [Finset.sum_range_succ, hshift, hnew, pow_succ]
          ring

/-- A separated geometric convolution is unchanged when its two rates are
exchanged together with reflection of the finite time index. -/
theorem sum_range_geometric_convolution_comm
    (r q : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, q ^ (m - i - 1) * r ^ i) =
      ∑ i ∈ Finset.range m, r ^ (m - i - 1) * q ^ i := by
  rw [← Finset.sum_range_reflect
    (fun i => r ^ (m - i - 1) * q ^ i) m]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  rw [show m - (m - 1 - i) - 1 = i by omega,
    show m - 1 - i = m - i - 1 by omega]
  ring

/-- Finite weighted-maximum absorption used for `Z_m`.  The pointwise
estimate is required at every index in the range, so this is the genuine
finite-max closure step rather than an assumption of the desired endpoint
bound. -/
theorem range_image_max_le_two_mul_of_pointwise_self_half
    (u : ℕ → ℝ) (A theta : ℝ) (m : ℕ)
    (hA : 0 ≤ A) (htheta : 0 ≤ theta) (hthetaHalf : theta ≤ 1 / 2)
    (hu : ∀ i ∈ Finset.range (m + 1), 0 ≤ u i)
    (hpoint : ∀ (hS : ((Finset.range (m + 1)).image u).Nonempty)
        (i : ℕ), i ∈ Finset.range (m + 1) →
        u i ≤ A + theta *
          ((Finset.range (m + 1)).image u).max' hS) :
    ∀ hS : ((Finset.range (m + 1)).image u).Nonempty,
      ((Finset.range (m + 1)).image u).max' hS ≤ 2 * A := by
  intro hS
  have hmem := Finset.max'_mem ((Finset.range (m + 1)).image u) hS
  obtain ⟨i, hi, himax⟩ := Finset.mem_image.mp hmem
  have hiBound := hpoint hS i hi
  rw [← himax] at hiBound
  have hthetaMax : theta *
        ((Finset.range (m + 1)).image u).max' hS ≤
      (1 / 2 : ℝ) * ((Finset.range (m + 1)).image u).max' hS := by
    have hmax_nonneg : 0 ≤
        ((Finset.range (m + 1)).image u).max' hS := by
      have hzero_mem : u 0 ∈ (Finset.range (m + 1)).image u :=
        Finset.mem_image.mpr ⟨0, by simp, rfl⟩
      have hle := Finset.le_max'
        ((Finset.range (m + 1)).image u) (u 0) hzero_mem
      have hu0 : 0 ≤ u 0 := hu 0 (by simp)
      exact hu0.trans hle
    exact mul_le_mul_of_nonneg_right hthetaHalf hmax_nonneg
  nlinarith

/-- Source `Z_m` absorption in the weighted coordinates
`q^{-i}|z_{k+i}|`.  The caller supplies the slow-convolution estimate with
the fast feedback still present as `theta * Z_m`; this lemma performs the
finite maximum selection, half-feedback absorption, and conversion back to
the unweighted slow state. -/
theorem actual_quadratic_Zmax_absorption
    (z : ℕ → ℝ) (k m : ℕ) (q A theta : ℝ)
    (hq : 0 < q) (hA : 0 ≤ A) (htheta : 0 ≤ theta)
    (hthetaHalf : theta ≤ 1 / 2)
    (hpoint :
      let u : ℕ → ℝ := fun i => |z (k + i)| / q ^ i
      ∀ (hS : ((Finset.range (m + 1)).image u).Nonempty)
        (i : ℕ), i ∈ Finset.range (m + 1) →
        u i ≤ A + theta *
          ((Finset.range (m + 1)).image u).max' hS) :
    |z (k + m)| ≤ 2 * A * q ^ m := by
  let u : ℕ → ℝ := fun i => |z (k + i)| / q ^ i
  have hu : ∀ i ∈ Finset.range (m + 1), 0 ≤ u i := by
    intro i hi
    exact div_nonneg (abs_nonneg _) (pow_nonneg hq.le _)
  have hS : ((Finset.range (m + 1)).image u).Nonempty := by
    exact ⟨u 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  have hmax := range_image_max_le_two_mul_of_pointwise_self_half
    u A theta m hA htheta hthetaHalf hu (by simpa [u] using hpoint) hS
  have humax : u m ≤ ((Finset.range (m + 1)).image u).max' hS := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨m, by simp, rfl⟩
  have huBound : u m ≤ 2 * A := humax.trans hmax
  have hqpow : 0 < q ^ m := pow_pos hq _
  calc
    |z (k + m)| = u m * q ^ m := by
      dsimp [u]
      field_simp [hqpow.ne']
    _ ≤ (2 * A) * q ^ m :=
      mul_le_mul_of_nonneg_right huBound hqpow.le
    _ = 2 * A * q ^ m := rfl

end Algorithms.Unverified.GeneralPushPull
end
