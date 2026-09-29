import Algorithms.Unverified.StochasticGradientSliding.Part002
import SOptLib.Model.Bregman
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Proximal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
Stochastic gradient sliding.

Phase 0 object layer for Lan's stochastic gradient sliding method.  The
declarations below encode the paper-facing mathematical objects as definitions:
the composite objective, Bregman prox geometry, stochastic oracle samples, SPS
inner update, and the outer SGS recursion.
-/

open scoped BigOperators Gradient InnerProductSpace
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 800000

namespace StochasticGradientSliding


universe u v w z

variable {E : Type u} {Sample : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (S : Setup.{u, v, w} E Sample)

/-- Pointwise generated reverse-gap absorption for the averaged SPS output.

Aligns with Lan Proposition 8.3 step 3 / Eq. (8.1.63): after the weighted
average identity, the reverse `Phi` gap is absorbed into the displayed terminal
Bregman term plus previous-window terms. Candidate audit: considered the later
selected pointwise helper
`selected_sgs_inner_average_phi_reverse_gap_splitCgap_pointwise`,
`sps_avg_eq_weighted_sum`, and the SOptLib weighted-average candidates. The
selected helper is tied to canonical selector states, while `sps_avg_eq_weighted_sum`
is only the average identity component; no SOptLib lemma combines the generated
SPS process, random outer center, fixed-slope reverse-gap decomposition, and
paper-specific Young constants. -/
theorem generated_sgs_inner_average_phi_reverse_gap_pairing_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (xTarget : FeasiblePoint S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem : ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ) (χa : ℝ) (χb : E)
    (hχminor : ∀ y : {x : E // x ∈ S.X}, χa + ⟪χb, y.1⟫_ℝ ≤ S.chi y.1) :
    ∀ ω,
      spsPhiFormulaOnX S
          (smoothLinearization S
            (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
          (states (κ.1 - 1) ω).x (beta κ) xTarget -
        spsPhiFormulaOnX S
          (smoothLinearization S
            (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
          (states (κ.1 - 1) ω).x (beta κ)
          (inner κ (j + 1) ω).avg ≤
        (beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2) *
            bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          generated_sgs_inner_average_phi_reverse_gap_repairedCgap
            (S := S) law xTarget beta gamma states inner hquery_mem κ j χa χb ω := by
  classical
  intro ω
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let outerPrev : SGSState S := states (κ.1 - 1) ω
  let xUnder : E := outerExtrapolation S gamma κ outerPrev
  let gk : E → ℝ := fun y => smoothLinearization S xUnder y
  let sampleω : ℕ → Ω → Sample := fun i _ => law.sample κ i ω
  let statesω : ℕ → Ω → SPSState S := fun i _ => inner κ i ω
  have hrun' : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner := by
    exact hrun.1
  have hprocess :
      IsGeneratedSPSProcess S
        (fun ω u =>
          smoothLinearization S
            (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)) u)
        (fun ω => (states (κ.1 - 1) ω).x)
        (beta κ) (law.sample κ) (inner κ) :=
    hrun'.2.1 κ
  have hfixed : IsSPSProcess S gk outerPrev.x (beta κ) sampleω statesω := by
    rcases hprocess with ⟨hβpos, hinit, htrans⟩
    refine ⟨hβpos, ?_, ?_⟩
    · intro ω'
      simpa [statesω, outerPrev] using hinit ω
    · intro n ω'
      simpa [statesω, sampleω, gk, outerPrev, xUnder] using htrans n ω
  have havg_closed :
      (inner κ t.1 ω).avg.1 =
        (psWeightProduct spsP t.1 *
            (1 - psWeightProduct spsP t.1)⁻¹) •
          (Finset.range t.1).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
              (inner κ (i + 1) ω).u.1) := by
    have hclosed :=
      sps_avg_eq_weighted_sum
        (S := S) gk outerPrev.x (beta κ) sampleω statesω hfixed ω t
    simpa [statesω, sampleω, gk, outerPrev, xUnder] using hclosed
  have hxUnder_mem : xUnder ∈ S.X := by
    dsimp [xUnder, outerPrev, outerExtrapolation]
    exact convexCombination_mem_X S (states (κ.1 - 1) ω).xbar
      (states (κ.1 - 1) ω).x (hgamma κ).1 (hgamma κ).2
  have hOneSub : 0 < 1 - psWeightProduct spsP t.1 :=
    one_sub_psWeightProduct_spsP_pos_of_pos t.2
  have hpropCoeff_pos :
      0 < beta κ * (1 - psWeightProduct spsP t.1)⁻¹ := by
    exact mul_pos (hbeta κ) (inv_pos.mpr hOneSub)
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let C : ℝ := psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹
  let w : ℕ → ℝ := fun i =>
    (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹
  let totalSlope : E := sourceSmoothGradient S xUnder + S.hSubgradient xTarget.1 + χb
  let fixedSlope : E := sourceSmoothGradient S xTarget.1 + S.hSubgradient xTarget.1 + χb
  let residual : ℝ :=
    beta κ * bregmanFormulaOnX S outerPrev.x xTarget +
      (S.chi xTarget.1 - χa - ⟪χb, xTarget.1⟫_ℝ)
  have hpropCoeff_pos' : 0 < propCoeff := by
    simpa [propCoeff] using hpropCoeff_pos
  have hdecomp :
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) xTarget -
          spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
            (inner κ t.1 ω).avg ≤
        (smoothLinearization S xUnder xTarget.1 -
            smoothLinearization S xUnder (inner κ t.1 ω).avg.1 -
            ⟪sourceSmoothGradient S xTarget.1,
              xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ) +
          ⟪fixedSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ +
            residual := by
    have hh_support :
        S.h (inner κ t.1 ω).avg.1 ≥
          S.h xTarget.1 +
            ⟪S.hSubgradient xTarget.1,
              (inner κ t.1 ω).avg.1 - xTarget.1⟫_ℝ := by
      have hmem := (setup_hSubgradientMem S) xTarget.1 xTarget.2
      exact (SOptLib.mem_carrierSubdifferential_iff.mp hmem) (inner κ t.1 ω).avg
    have hh_gap :
        S.h xTarget.1 - S.h (inner κ t.1 ω).avg.1 ≤
          ⟪S.hSubgradient xTarget.1,
            xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
      have hinner :
          ⟪S.hSubgradient xTarget.1,
              (inner κ t.1 ω).avg.1 - xTarget.1⟫_ℝ =
            -⟪S.hSubgradient xTarget.1,
              xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
        simp [inner_sub_right]
      nlinarith
    have hχavg :
        χa + ⟪χb, (inner κ t.1 ω).avg.1⟫_ℝ ≤
          S.chi (inner κ t.1 ω).avg.1 :=
      hχminor (inner κ t.1 ω).avg
    have hχ_gap :
        S.chi xTarget.1 - S.chi (inner κ t.1 ω).avg.1 ≤
          (S.chi xTarget.1 - χa - ⟪χb, xTarget.1⟫_ℝ) +
            ⟪χb, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
      have hinner :
          ⟪χb, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ =
            ⟪χb, xTarget.1⟫_ℝ - ⟪χb, (inner κ t.1 ω).avg.1⟫_ℝ := by
        simp [inner_sub_right]
      nlinarith
    have hVcenter_avg_nonneg :
        0 ≤ bregmanFormulaOnX S outerPrev.x (inner κ t.1 ω).avg := by
      have hlower :=
        bregmanFormulaOnX_lower_bound_from_prox_geometry S outerPrev.x
          (inner κ t.1 ω).avg
      nlinarith [sq_nonneg
        (S.primalNorm ((inner κ t.1 ω).avg.1 - outerPrev.x.1))]
    have hβ_gap :
        beta κ * bregmanFormulaOnX S outerPrev.x xTarget -
            beta κ * bregmanFormulaOnX S outerPrev.x (inner κ t.1 ω).avg ≤
          beta κ * bregmanFormulaOnX S outerPrev.x xTarget := by
      nlinarith [(hbeta κ).le, hVcenter_avg_nonneg]
    have hsmooth_split :
        smoothLinearization S xUnder xTarget.1 -
            smoothLinearization S xUnder (inner κ t.1 ω).avg.1 =
          (smoothLinearization S xUnder xTarget.1 -
              smoothLinearization S xUnder (inner κ t.1 ω).avg.1 -
              ⟪sourceSmoothGradient S xTarget.1,
                xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ) +
            ⟪sourceSmoothGradient S xTarget.1,
              xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
      ring
    have hfixed_sum :
        ⟪sourceSmoothGradient S xTarget.1,
            xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ +
            ⟪S.hSubgradient xTarget.1,
              xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ +
            ⟪χb, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ =
          ⟪fixedSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
      simp [fixedSlope, inner_add_left]
    unfold spsPhiFormulaOnX spsPhi
    dsimp [residual]
    nlinarith [hh_gap, hχ_gap, hβ_gap, hsmooth_split, hfixed_sum]
  have hsmooth_exact :
      smoothLinearization S xUnder xTarget.1 -
          smoothLinearization S xUnder (inner κ t.1 ω).avg.1 -
          ⟪sourceSmoothGradient S xTarget.1,
            xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ =
        ⟪sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1,
          xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
    simp [smoothLinearization, inner_sub_right, inner_sub_left]
    ring
  have hpair_combine :
      ⟪sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1,
          xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ +
        ⟪fixedSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ =
          ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
    simp [fixedSlope, totalSlope, inner_add_left, inner_sub_left]
    ring
  have hgap_pair :
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) xTarget -
          spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
            (inner κ t.1 ω).avg ≤
        ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ + residual := by
    nlinarith [hdecomp, hsmooth_exact, hpair_combine]
  have hqsum :
      (Finset.range t.1).sum (fun i => C * w i) = 1 := by
    simpa [C, w, mul_assoc] using sps_normalized_weight_sum_eq_one t.1 t.2
  have hq_nonneg : ∀ i ∈ Finset.range t.1, 0 ≤ C * w i := by
    intro i _hi
    have hnorm :
        C * w i =
          2 * ((i : ℝ) + 2) / ((t.1 : ℝ) * ((t.1 : ℝ) + 3)) := by
      simpa [C, w] using sps_normalized_weight_eq t.1 i t.2
    rw [hnorm]
    positivity
  have havg_weighted :
      (inner κ t.1 ω).avg.1 =
        (Finset.range t.1).sum (fun i =>
          (C * w i) • (inner κ (i + 1) ω).u.1) := by
    calc
      (inner κ t.1 ω).avg.1 =
          C • (Finset.range t.1).sum (fun i =>
            w i • (inner κ (i + 1) ω).u.1) := by
            simpa [C, w] using havg_closed
      _ = (Finset.range t.1).sum (fun i =>
            (C * w i) • (inner κ (i + 1) ω).u.1) := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [smul_smul]
  have hx_minus_avg :
      xTarget.1 - (inner κ t.1 ω).avg.1 =
        (Finset.range t.1).sum (fun i =>
          (C * w i) • (xTarget.1 - (inner κ (i + 1) ω).u.1)) := by
    have hx_as_sum :
        xTarget.1 = (Finset.range t.1).sum (fun i => (C * w i) • xTarget.1) := by
      rw [← Finset.sum_smul, hqsum, one_smul]
    calc
      xTarget.1 - (inner κ t.1 ω).avg.1 =
          (Finset.range t.1).sum (fun i => (C * w i) • xTarget.1) -
            (Finset.range t.1).sum (fun i =>
              (C * w i) • (inner κ (i + 1) ω).u.1) := by
            rw [havg_weighted]
            conv_lhs => rw [hx_as_sum]
      _ = (Finset.range t.1).sum (fun i =>
            (C * w i) • xTarget.1 - (C * w i) • (inner κ (i + 1) ω).u.1) := by
            rw [Finset.sum_sub_distrib]
      _ = (Finset.range t.1).sum (fun i =>
            (C * w i) • (xTarget.1 - (inner κ (i + 1) ω).u.1)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [smul_sub]
  have hpair_sum_formula :
      ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ =
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) := by
    rw [hx_minus_avg]
    simp [inner_sum, inner_smul_right, mul_comm]
  have hq_pos_of_mem : ∀ i ∈ Finset.range t.1, 0 < C * w i := by
    intro i _hi
    have hnorm :
        C * w i =
          2 * ((i : ℝ) + 2) / ((t.1 : ℝ) * ((t.1 : ℝ) + 3)) := by
      simpa [C, w] using sps_normalized_weight_eq t.1 i t.2
    rw [hnorm]
    positivity
  have hqj_pos : 0 < C * w j := by
    have hjmem : j ∈ Finset.range t.1 := by
      simp [t]
    exact hq_pos_of_mem j hjmem
  have hterminal_young :
      (C * w j) *
          ⟪totalSlope, xTarget.1 - (inner κ (j + 1) ω).u.1⟫_ℝ ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          (C * w j) ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff := by
    let qj : ℝ := C * w j
    have hqj' : 0 < qj := by
      simpa [qj] using hqj_pos
    let eps : ℝ := propCoeff / (2 * qj)
    have heps : 0 < eps := by
      dsimp [eps]
      positivity
    have hbase :=
      fixed_linear_pairing_bregman_absorb_with_epsilon_explicit
        (S := S) xTarget totalSlope heps (inner κ (j + 1) ω).u
    have hmul :=
      mul_le_mul_of_nonneg_left hbase hqj'.le
    have hcoefV :
        qj * eps = propCoeff / 2 := by
      dsimp [eps]
      field_simp [eps, ne_of_gt hqj']
    have hcoefD :
        qj * (dualNorm S totalSlope ^ 2 / (2 * eps)) =
          qj ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff := by
      dsimp [eps]
      field_simp [eps, ne_of_gt hqj', ne_of_gt hpropCoeff_pos']
    calc
      (C * w j) *
          ⟪totalSlope, xTarget.1 - (inner κ (j + 1) ω).u.1⟫_ℝ
          = qj * ⟪totalSlope, xTarget.1 - (inner κ (j + 1) ω).u.1⟫_ℝ := by
            rfl
      _ ≤ qj *
              (eps * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
                dualNorm S totalSlope ^ 2 / (2 * eps)) := by
            simpa [eps] using hmul
      _ =
          qj * eps * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
            qj * (dualNorm S totalSlope ^ 2 / (2 * eps)) := by
            ring
      _ =
          (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
            qj ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff := by
            rw [hcoefV, hcoefD]
      _ =
          (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
            (C * w j) ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff := by
            simp [qj]
  have hprev_young_sum_raw :
      (Finset.range j).sum (fun i =>
          (C * w i) * ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) ≤
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget +
            2 * (j + 1 : ℝ) * (C * w i) ^ 2 *
              dualNorm S totalSlope ^ 2 / propCoeff) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hit : i ∈ Finset.range t.1 := by
      have hi_lt : i < j := Finset.mem_range.mp hi
      simp [t]
      omega
    have hqi : 0 < C * w i := hq_pos_of_mem i hit
    have hn : 0 < (j + 1 : ℝ) := by positivity
    simpa using
      (fixed_linear_pairing_bregman_absorb_previous_window
        (S := S) xTarget (inner κ (i + 1) ω).u totalSlope
        (propCoeff := propCoeff) (n := (j + 1 : ℝ)) (q := C * w i)
        hpropCoeff_pos' hn hqi)
  have hprev_young_sum :
      (Finset.range j).sum (fun i =>
          (C * w i) * ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) ≤
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (2 * (j + 1 : ℝ) *
              (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff := by
    calc
      (Finset.range j).sum (fun i =>
          (C * w i) * ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ)
          ≤
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget +
            2 * (j + 1 : ℝ) * (C * w i) ^ 2 *
              dualNorm S totalSlope ^ 2 / propCoeff) := hprev_young_sum_raw
      _ =
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (2 * (j + 1 : ℝ) *
              (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff := by
          rw [Finset.sum_add_distrib]
          congr 1
          calc
            (Finset.range j).sum (fun i =>
                2 * (j + 1 : ℝ) * (C * w i) ^ 2 *
                  dualNorm S totalSlope ^ 2 / propCoeff)
                =
              (Finset.range j).sum (fun i =>
                (C * w i) ^ 2 *
                  (2 * (j + 1 : ℝ) * dualNorm S totalSlope ^ 2 / propCoeff)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
            _ =
              ((Finset.range j).sum (fun i => (C * w i) ^ 2)) *
                (2 * (j + 1 : ℝ) * dualNorm S totalSlope ^ 2 / propCoeff) := by
                rw [Finset.sum_mul]
            _ =
              (2 * (j + 1 : ℝ) *
                  (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
                dualNorm S totalSlope ^ 2 / propCoeff := by
                ring
  have hpair_sum_split :
      (Finset.range t.1).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪totalSlope, xTarget.1 - (inner κ (j + 1) ω).u.1⟫_ℝ := by
    simpa [t] using
      (Finset.sum_range_succ (fun i =>
        (C * w i) *
          ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) j)
  have hpair_sum_split_total :
      ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪totalSlope, xTarget.1 - (inner κ (j + 1) ω).u.1⟫_ℝ := by
    exact hpair_sum_formula.trans hpair_sum_split
  have hpair_young_bound :
      ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          (Finset.range j).sum (fun i =>
            (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (((C * w j) ^ 2 +
              2 * (j + 1 : ℝ) *
                (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff) := by
    calc
      ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, xTarget.1 - (inner κ (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪totalSlope, xTarget.1 - (inner κ (j + 1) ω).u.1⟫_ℝ :=
          hpair_sum_split_total
      _ ≤
        ((Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (2 * (j + 1 : ℝ) *
              (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff) +
          ((propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
            (C * w j) ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff) := by
          exact add_le_add hprev_young_sum hterminal_young
      _ =
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          (Finset.range j).sum (fun i =>
            (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (((C * w j) ^ 2 +
              2 * (j + 1 : ℝ) *
                (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff) := by
          ring
  let qsqBudget : ℝ :=
    (C * w j) ^ 2 +
      2 * (j + 1 : ℝ) * (Finset.range j).sum (fun i => (C * w i) ^ 2)
  let smoothCgap : ℝ :=
    generated_sgs_inner_average_phi_reverse_gap_smoothUpperCgap
      (S := S) law xTarget beta gamma states κ (propCoeff / 2) χa χb ω
  have hsmooth_dom :
      dualNorm S totalSlope ^ 2 / propCoeff + |residual| ≤ smoothCgap := by
    let xUnderFp : FeasiblePoint S := ⟨xUnder, hxUnder_mem⟩
    let xUnderSq : ℝ := S.primalNorm (xTarget.1 - xUnder) ^ 2
    let slopeNorm : ℝ := dualNorm S totalSlope
    have hgrad_lip :
        ∀ x y : FeasiblePoint S,
          dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) ≤
            S.lSmooth * S.primalNorm (y.1 - x.1) :=
      sourceSmoothGradient_dual_lipschitz_from_smoothness (S := S)
    have hdiff_sq :
        dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1) ^ 2 ≤
          S.lSmooth ^ 2 * xUnderSq := by
      have hraw :=
        sourceSmoothGradient_dualNorm_sq_le_smooth_displacement_sq_of_dual_lipschitz
          (S := S) hgrad_lip xTarget xUnderFp
      have hsym :
          S.primalNorm (xUnder - xTarget.1) = S.primalNorm (xTarget.1 - xUnder) := by
        have hneg : xUnder - xTarget.1 = -(xTarget.1 - xUnder) := by abel
        rw [hneg]
        simpa using (map_neg_eq_map S.primalNorm (xTarget.1 - xUnder))
      simpa [xUnderSq, xUnderFp, hsym] using hraw
    have hfixed_nonneg : 0 ≤ dualNorm S fixedSlope := by
      simpa [dualNorm] using
        SOptLib.canonicalDualNorm_nonneg S.primalNorm fixedSlope
    have hslope_add :
        slopeNorm ≤
          dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1) +
            dualNorm S fixedSlope := by
      have hdecompSlope :
          totalSlope =
            (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1) +
              fixedSlope := by
        simp [totalSlope, fixedSlope]
        abel
      have hadd :=
        SOptLib.canonicalDualNorm_add_le
          (p := S.primalNorm)
          (zeta := sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1)
          (eta := fixedSlope)
          (dualNorm_supportSet_bddAbove S
            (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1))
          (dualNorm_supportSet_bddAbove S fixedSlope)
      simpa [slopeNorm, dualNorm, hdecompSlope] using hadd
    have hdiff_nonneg :
        0 ≤ dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1) := by
      simpa [dualNorm] using
        SOptLib.canonicalDualNorm_nonneg S.primalNorm
          (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1)
    have hslope_nonneg : 0 ≤ slopeNorm := by
      dsimp [slopeNorm]
      simpa [dualNorm] using
        SOptLib.canonicalDualNorm_nonneg S.primalNorm totalSlope
    have hsq_add :
        slopeNorm ^ 2 ≤
          2 *
            (dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1) ^ 2 +
              dualNorm S fixedSlope ^ 2) := by
      nlinarith [hslope_add, hslope_nonneg, hdiff_nonneg, hfixed_nonneg,
        sq_nonneg
          (dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S xTarget.1) -
            dualNorm S fixedSlope)]
    have hnum :
        slopeNorm ^ 2 ≤
          2 * (S.lSmooth ^ 2 * xUnderSq + dualNorm S fixedSlope ^ 2) := by
      nlinarith [hsq_add, hdiff_sq]
    have heps : 0 < propCoeff / 2 := by positivity
    have hscale_nonneg : 0 ≤ (2 * (propCoeff / 2))⁻¹ :=
      inv_nonneg.mpr (mul_nonneg (by norm_num) heps.le)
    have hscaled := mul_le_mul_of_nonneg_right hnum hscale_nonneg
    have hrewrite :
        2 * (S.lSmooth ^ 2 * xUnderSq + dualNorm S fixedSlope ^ 2) *
            (2 * (propCoeff / 2))⁻¹ =
          ((2 * S.lSmooth ^ 2) / (2 * (propCoeff / 2))) * xUnderSq +
            (2 * dualNorm S fixedSlope ^ 2) / (2 * (propCoeff / 2)) := by
      ring
    rw [hrewrite] at hscaled
    have hslope_part :
        dualNorm S totalSlope ^ 2 / propCoeff ≤
          ((2 * S.lSmooth ^ 2) / (2 * (propCoeff / 2))) * xUnderSq +
            (2 * dualNorm S fixedSlope ^ 2) / (2 * (propCoeff / 2)) := by
      have hden : 2 * (propCoeff / 2) = propCoeff := by ring
      simpa [slopeNorm, xUnderSq, div_eq_mul_inv, hden, mul_comm, mul_left_comm,
        mul_assoc] using hscaled
    dsimp [smoothCgap, generated_sgs_inner_average_phi_reverse_gap_smoothUpperCgap,
      outerPrev, xUnder, xUnderSq, fixedSlope, residual]
    nlinarith [hslope_part]
  have hDpart_nonneg : 0 ≤ dualNorm S totalSlope ^ 2 / propCoeff := by
    exact div_nonneg (sq_nonneg _) hpropCoeff_pos'.le
  have hqsq_nonneg : 0 ≤ qsqBudget := by
    have hsum_nonneg :
        0 ≤ (Finset.range j).sum (fun i => (C * w i) ^ 2) := by
      exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hscale_nonneg :
        0 ≤ 2 * (j + 1 : ℝ) *
          (Finset.range j).sum (fun i => (C * w i) ^ 2) := by
      have htwo_nonneg : 0 ≤ (2 : ℝ) := by norm_num
      have hj_nonneg : 0 ≤ (j + 1 : ℝ) := by exact_mod_cast Nat.zero_le (j + 1)
      exact mul_nonneg (mul_nonneg htwo_nonneg hj_nonneg) hsum_nonneg
    dsimp [qsqBudget]
    exact add_nonneg (sq_nonneg (C * w j)) hscale_nonneg
  have hDpart_le_smooth :
      dualNorm S totalSlope ^ 2 / propCoeff ≤ smoothCgap := by
    have hle :
        dualNorm S totalSlope ^ 2 / propCoeff ≤
          dualNorm S totalSlope ^ 2 / propCoeff + |residual| := by
      linarith [abs_nonneg residual]
    exact hle.trans hsmooth_dom
  have hresidual_le_smooth : residual ≤ smoothCgap := by
    have hle_abs : residual ≤ |residual| := le_abs_self residual
    have habs_le :
        |residual| ≤ dualNorm S totalSlope ^ 2 / propCoeff + |residual| := by
      linarith [hDpart_nonneg]
    exact hle_abs.trans (habs_le.trans hsmooth_dom)
  have hbudget_absorb :
      qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual ≤
        (1 + qsqBudget) * smoothCgap := by
    have hmul :=
      mul_le_mul_of_nonneg_left hDpart_le_smooth hqsq_nonneg
    nlinarith [hmul, hresidual_le_smooth]
  have hfinal_pair :
      ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ + residual ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          generated_sgs_inner_average_phi_reverse_gap_repairedCgap
            (S := S) law xTarget beta gamma states inner hquery_mem κ j χa χb ω := by
    calc
      ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ + residual
          ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
            (Finset.range j).sum (fun i =>
              (propCoeff / (4 * (j + 1 : ℝ))) *
                bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (((C * w j) ^ 2 +
              2 * (j + 1 : ℝ) *
                (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff) +
          residual := by
          have hbase := add_le_add_right hpair_young_bound residual
          calc
            ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ + residual =
                residual + ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ := by
                ring
            _ ≤
                residual +
                  ((propCoeff / 2) *
                      bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
                    (Finset.range j).sum (fun i =>
                      (propCoeff / (4 * (j + 1 : ℝ))) *
                        bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
                    (((C * w j) ^ 2 +
                        2 * (j + 1 : ℝ) *
                          (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
                      dualNorm S totalSlope ^ 2 / propCoeff)) := hbase
            _ =
                (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
                  (Finset.range j).sum (fun i =>
                    (propCoeff / (4 * (j + 1 : ℝ))) *
                      bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
                (((C * w j) ^ 2 +
                    2 * (j + 1 : ℝ) *
                      (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
                  dualNorm S totalSlope ^ 2 / propCoeff) +
                residual := by
                ring
      _ =
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          (Finset.range j).sum (fun i =>
            (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual) := by
          dsimp [qsqBudget]
          ring
      _ ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          (Finset.range j).sum (fun i =>
            (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
          (1 + qsqBudget) * smoothCgap := by
          let fixedTerms : ℝ :=
            (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget)
          have hbase := add_le_add_left hbudget_absorb fixedTerms
          calc
            (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
                (Finset.range j).sum (fun i =>
                  (propCoeff / (4 * (j + 1 : ℝ))) *
                    bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
              (qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual)
                =
              qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual +
                fixedTerms := by
                dsimp [fixedTerms]
                ring
            _ ≤ (1 + qsqBudget) * smoothCgap + fixedTerms := hbase
            _ =
              (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
                (Finset.range j).sum (fun i =>
                  (propCoeff / (4 * (j + 1 : ℝ))) *
                    bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
                (1 + qsqBudget) * smoothCgap := by
                dsimp [fixedTerms]
                ring
      _ =
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          generated_sgs_inner_average_phi_reverse_gap_repairedCgap
            (S := S) law xTarget beta gamma states inner hquery_mem κ j χa χb ω := by
          change
            (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
                (Finset.range j).sum (fun i =>
                  (propCoeff / (4 * (j + 1 : ℝ))) *
                    bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) +
              (1 + qsqBudget) * smoothCgap =
            (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
              ((1 + qsqBudget) * smoothCgap +
                (Finset.range j).sum (fun i =>
                  (propCoeff / (4 * (j + 1 : ℝ))) *
                    bregmanFormulaOnX S
                      (⟨sgsGeneratedOracleQuery S inner κ (i + 1) ω,
                        hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S) xTarget))
          have hprev_breg :
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S (inner κ (i + 1) ω).u xTarget) =
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S
                    (⟨sgsGeneratedOracleQuery S inner κ (i + 1) ω,
                      hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S) xTarget) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hpoint :
                (inner κ (i + 1) ω).u =
                  (⟨sgsGeneratedOracleQuery S inner κ (i + 1) ω,
                    hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S) := by
              apply Subtype.ext
              simp [sgsGeneratedOracleQuery]
            rw [hpoint]
          rw [hprev_breg]
          ring
  calc
    spsPhiFormulaOnX S
          (smoothLinearization S
            (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
          (states (κ.1 - 1) ω).x (beta κ) xTarget -
        spsPhiFormulaOnX S
          (smoothLinearization S
            (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
          (states (κ.1 - 1) ω).x (beta κ)
          (inner κ (j + 1) ω).avg
        =
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) xTarget -
        spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
          (inner κ t.1 ω).avg := by
        simp [xUnder, outerPrev, t]
    _ ≤ ⟪totalSlope, xTarget.1 - (inner κ t.1 ω).avg.1⟫_ℝ + residual :=
      hgap_pair
    _ ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          generated_sgs_inner_average_phi_reverse_gap_repairedCgap
            (S := S) law xTarget beta gamma states inner hquery_mem κ j χa χb ω :=
      hfinal_pair
    _ =
        (beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2) *
            bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
          generated_sgs_inner_average_phi_reverse_gap_repairedCgap
            (S := S) law xTarget beta gamma states inner hquery_mem κ j χa χb ω := by
      have hcoeff :
          propCoeff / 2 =
            beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2 := by
        simp [propCoeff, t]
      rw [hcoeff]

/-- Generated averaged-output reverse `Phi` gap envelope.

Aligns with Lan Proposition 8.3 proof step 3, the absorption of
`Φ(u)-Φ(tilde u_t)` after Eq. (8.1.63). Candidate audit: considered the
selected envelope `selected_sgs_inner_average_phi_reverse_gap_integrable_envelope`,
the fixed-center envelope `fixed_spsPhiFormulaOnX_reverse_gap_integrable_envelope`,
and SOptLib telescope/weighted-average helpers. The selected helper is tied to
canonical selector states, the fixed-center helper cannot handle the random SGS
outer center, and SOptLib does not combine the paper-local random smooth model,
SPS weighted average, and Bregman absorption constants. This generated helper
is the remaining relation-form port of the source reverse-gap envelope. -/
theorem generated_sgs_inner_average_phi_reverse_gap_integrable_envelope
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (xTarget : FeasiblePoint S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem : ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsGeneratedOracleQuery S inner k i ω,
          hquery_mem k i ω⟩ : FeasiblePoint S)))
    (κ : PositiveTime) (j : ℕ)
    (houter_xbar_sq :
      Integrable
        (fun ω =>
          S.primalNorm (xTarget.1 - (states (κ.1 - 1) ω).xbar.1) ^ 2)
        law.P)
    (hprev_window :
      ∀ i, i < j + 1 →
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsGeneratedOracleQuery S inner κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              xTarget)
      law.P) :
    ∃ Cgap : Ω → ℝ,
      Integrable Cgap law.P ∧
        (∀ᵐ ω ∂law.P,
          spsPhiFormulaOnX S
              (smoothLinearization S
                (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
              (states (κ.1 - 1) ω).x (beta κ) xTarget -
            spsPhiFormulaOnX S
              (smoothLinearization S
                (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
              (states (κ.1 - 1) ω).x (beta κ)
              (inner κ (j + 1) ω).avg ≤
            (beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2) *
                bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
              Cgap ω) := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  obtain ⟨χa, χb, hχminor⟩ :=
    convexOn_feasible_affine_minorant
      (X := S.X) S.convex_X (⟨xTarget.1, xTarget.2⟩ : {x : E // x ∈ S.X})
      S.chi S.convex_chi
  let Cgap : Ω → ℝ :=
    generated_sgs_inner_average_phi_reverse_gap_repairedCgap
      (S := S) law xTarget beta gamma states inner hquery_mem κ j χa χb
  have hCgap_int : Integrable Cgap law.P := by
    simpa [Cgap] using
      generated_sgs_inner_average_phi_reverse_gap_repairedCgap_integrable
        (S := S) law xTarget x0 beta gamma T states inner hrun hbeta
        hquery_mem hquery_meas κ j χa χb houter_xbar_sq hprev_window
  have hpoint :
      ∀ ω,
        spsPhiFormulaOnX S
            (smoothLinearization S
              (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
            (states (κ.1 - 1) ω).x (beta κ) xTarget -
          spsPhiFormulaOnX S
            (smoothLinearization S
              (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)))
            (states (κ.1 - 1) ω).x (beta κ)
            (inner κ (j + 1) ω).avg ≤
          (beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2) *
              bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
            Cgap ω := by
    simpa [Cgap] using
      generated_sgs_inner_average_phi_reverse_gap_pairing_bound
        (S := S) law xTarget x0 beta gamma T states inner hrun hbeta hgamma
        hquery_mem κ j χa χb hχminor
  refine ⟨Cgap, hCgap_int, ?_⟩
  exact Filter.Eventually.of_forall hpoint

/-- Generated one-step Bregman integrability transfer for arbitrary relation-form
SGS/SPS runs.

Aligns with Lan Proposition 8.3 Eq. (8.1.63) as used in Theorem 8.2 proof
step 2. Candidate audit: considered the selected helper
`sgsOracleQuery_successor_bregman_integrable_of_prev_bregman`; it proves the
same mathematical transfer but is selector-specific. This helper uses the
relation-form generated RHS integrability and generated averaged reverse-gap
envelope above, then applies
`generated_sps_terminal_bregman_integrable_of_average_phi_envelope`. -/
theorem generated_sgs_query_successor_bregman_integrable_of_prev_window
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (xTarget : FeasiblePoint S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem : ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsGeneratedOracleQuery S inner k i ω,
          hquery_mem k i ω⟩ : FeasiblePoint S)))
    (hvar : generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (κ : PositiveTime) (j : ℕ)
    (houter_xbar_sq :
      Integrable
        (fun ω =>
          S.primalNorm (xTarget.1 - (states (κ.1 - 1) ω).xbar.1) ^ 2)
        law.P)
    (hprev_window :
      ∀ i, i < j + 1 →
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsGeneratedOracleQuery S inner κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              xTarget)
          law.P) :
    Integrable
      (fun ω =>
        bregmanFormulaOnX S
          (⟨sgsGeneratedOracleQuery S inner κ (j + 1) ω,
            hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
          xTarget)
      law.P := by
  classical
  have hrun' : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner := by
    exact hrun.1
  let gκ : Ω → E → ℝ := fun ω u =>
    smoothLinearization S
      (outerExtrapolation S gamma κ (states (κ.1 - 1) ω)) u
  let xκ : Ω → FeasiblePoint S := fun ω => (states (κ.1 - 1) ω).x
  have hprocess :
      IsGeneratedSPSProcess S gκ xκ (beta κ) (law.sample κ) (inner κ) := by
    simpa [gκ, xκ] using hrun'.2.1 κ
  have hgκ : ∀ ω, IsAffineModel (gκ ω) := by
    intro ω
    exact smoothLinearization_isAffineModel S
      (outerExtrapolation S gamma κ (states (κ.1 - 1) ω))
  have hnext_meas : Measurable (fun ω => (inner κ (j + 1) ω).u) := by
    simpa [sgsGeneratedOracleQuery] using hquery_meas κ (j + 1)
  have hRHS_int :
      Integrable
        (fun ω =>
          beta κ * psWeightProduct spsP (j + 1) *
              (1 - psWeightProduct spsP (j + 1))⁻¹ *
              bregmanFormulaOnX S (xκ ω) xTarget +
            psWeightProduct spsP (j + 1) *
              (1 - psWeightProduct spsP (j + 1))⁻¹ *
              (Finset.range (j + 1)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω)
                (spsP ι * psWeightProduct spsP i)⁻¹ *
                  (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                    ⟪δ, xTarget.1 - (inner κ i ω).u.1⟫_ℝ)))
        law.P := by
    simpa [xκ] using
      generated_sgs_inner_average_rhs_integrable
        (S := S) law xTarget x0 beta gamma T states inner hrun
        hquery_mem hquery_meas hvar κ j hprev_window
  have havgEnvelope :
      ∃ Cgap : Ω → ℝ,
        Integrable Cgap law.P ∧
          (∀ᵐ ω ∂law.P,
            spsPhiFormulaOnX S (gκ ω) (xκ ω) (beta κ) xTarget -
                spsPhiFormulaOnX S (gκ ω) (xκ ω) (beta κ)
                  (inner κ (j + 1) ω).avg ≤
              (beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2) *
                  bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget +
                Cgap ω) := by
    simpa [gκ, xκ] using
      generated_sgs_inner_average_phi_reverse_gap_integrable_envelope
        (S := S) law xTarget x0 beta gamma T states inner hrun
        hbeta hgamma hquery_mem hquery_meas κ j houter_xbar_sq hprev_window
  have hterminal :
      Integrable
        (fun ω => bregmanFormulaOnX S (inner κ (j + 1) ω).u xTarget)
        law.P :=
    generated_sps_terminal_bregman_integrable_of_average_phi_envelope
      (S := S) law.P gκ xκ (beta κ) (law.sample κ) (inner κ)
      hprocess hgκ xTarget j hnext_meas hRHS_int havgEnvelope
  simpa [sgsGeneratedOracleQuery] using hterminal

/-- One generated outer SGS step after inserting the generated SPS inner bound.

Aligns with Lan Eq. (8.1.31) plus Eq. (8.1.65), the first proof step of
Eq. (8.1.69). Candidate audit: the selected helper
`sgs_selected_one_step_gap_recurrence_formulaExtension` proves this only for
`sgsProcess_formulaExtensionSelector`; this relation-form helper instead uses
`hinner_proc` and `houter_update` from `IsGeneratedSGSProcess`, avoiding any
selector equality or uniqueness assumption for SPS argmins. -/
theorem generated_sgs_one_step_gap_recurrence_formulaExtension
    (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (k : PositiveTime) (hTpos : 0 < T k)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hinner_proc :
      IsGeneratedSPSProcess S
        (fun ω u =>
          smoothLinearization S
            (outerExtrapolation S gamma k (states (k.1 - 1) ω)) u)
        (fun ω => (states (k.1 - 1) ω).x)
        (beta k) (sample k) (inner k))
    (ω : Ω)
    (houter_update :
      (states k.1 ω).x = (inner k (T k) ω).u ∧
        (states k.1 ω).xbar.1 =
          (1 - gamma k) • (states (k.1 - 1) ω).xbar.1 +
            gamma k • (inner k (T k) ω).avg.1)
    (u : FeasiblePoint S) :
    let stPrev := states (k.1 - 1) ω
    let stCurr := states k.1 ω
    let δinner := inner k
    objective S stCurr.xbar.1 - objective S u.1 ≤
      (1 - gamma k) * (objective S stPrev.xbar.1 - objective S u.1) +
        gamma k *
          (beta k * (1 - psWeightProduct spsP (T k))⁻¹ *
              (bregmanFormulaOnX S stPrev.x u -
                bregmanFormulaOnX S stCurr.x u) +
            psWeightProduct spsP (T k) *
              (1 - psWeightProduct spsP (T k))⁻¹ *
                (Finset.range (T k)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample k i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
                      ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))) := by
  classical
  dsimp only
  let stPrev := states (k.1 - 1) ω
  let stCurr := states k.1 ω
  let δinner := inner k
  let xUnder := outerExtrapolation S gamma k stPrev
  let gk : E → ℝ := fun y => smoothLinearization S xUnder y
  let P : ℝ := psWeightProduct spsP (T k)
  let invOneMinusP : ℝ := (1 - P)⁻¹
  let Vprev : ℝ := bregmanFormulaOnX S stPrev.x u
  let Vcurr : ℝ := bregmanFormulaOnX S stCurr.x u
  let noise : ℝ :=
    (Finset.range (T k)).sum (fun i =>
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
      let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample k i ω);
      (spsP ι * psWeightProduct spsP i)⁻¹ *
        (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
          ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))
  let phiGap : ℝ :=
    spsPhiFormulaOnX S gk stPrev.x (beta k) (δinner (T k) ω).avg -
      spsPhiFormulaOnX S gk stPrev.x (beta k) u
  have hcurr_x : stCurr.x = (δinner (T k) ω).u := by
    simpa [stCurr, δinner] using houter_update.1
  have houter :
      objective S stCurr.xbar.1 - objective S u.1 ≤
        (1 - gamma k) * (objective S stPrev.xbar.1 - objective S u.1) +
          gamma k * (phiGap + beta k * Vprev) := by
    have h :=
      generated_outer_one_step_8_1_31_formulaExtension
        (S := S) beta gamma hbeta hgamma hlower k stPrev stCurr
        (δinner (T k) ω).avg houter_update.2 u
    simpa [stPrev, stCurr, δinner, xUnder, gk, phiGap, Vprev] using h
  let t : PositiveTime := ⟨T k, hTpos⟩
  have hsps :=
    generated_sps_inner_bound_formulaOnX_fixedPath
      (S := S)
      (g := fun ω u =>
        smoothLinearization S
          (outerExtrapolation S gamma k (states (k.1 - 1) ω)) u)
      (x := fun ω => (states (k.1 - 1) ω).x)
      (β := beta k) (sample := sample k) (states := inner k)
      hinner_proc ω t u
      (smoothLinearization_isAffineModel S xUnder)
  rw [← hcurr_x] at hsps
  have hsps' :
      beta k * invOneMinusP * Vcurr + phiGap ≤
        beta k * P * invOneMinusP * Vprev + P * invOneMinusP * noise := by
    simpa [t, P, invOneMinusP, Vprev, Vcurr, noise, phiGap,
      stPrev, stCurr, δinner, xUnder, gk] using hsps
  have hOneSubpos : 0 < 1 - P := by
    exact one_sub_psWeightProduct_spsP_pos_of_pos hTpos
  have hden : 1 - P ≠ 0 := ne_of_gt hOneSubpos
  have hphi :
      phiGap + beta k * Vprev ≤
        beta k * invOneMinusP * (Vprev - Vcurr) +
          P * invOneMinusP * noise := by
    have haux :
        phiGap ≤ beta k * P * invOneMinusP * Vprev +
            P * invOneMinusP * noise -
          beta k * invOneMinusP * Vcurr := by
      linarith [hsps']
    calc
      phiGap + beta k * Vprev
          ≤ beta k * P * invOneMinusP * Vprev +
              P * invOneMinusP * noise -
            beta k * invOneMinusP * Vcurr +
              beta k * Vprev := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right haux (beta k * Vprev)
      _ = beta k * invOneMinusP * (Vprev - Vcurr) +
            P * invOneMinusP * noise := by
            dsimp [invOneMinusP]
            field_simp [hden]
            ring
  have hscaled := mul_le_mul_of_nonneg_left hphi (hgamma k).1
  calc
    objective S stCurr.xbar.1 - objective S u.1
        ≤ (1 - gamma k) * (objective S stPrev.xbar.1 - objective S u.1) +
            gamma k * (phiGap + beta k * Vprev) := houter
    _ ≤ (1 - gamma k) * (objective S stPrev.xbar.1 - objective S u.1) +
          gamma k *
            (beta k * invOneMinusP * (Vprev - Vcurr) +
              P * invOneMinusP * noise) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hscaled
              ((1 - gamma k) * (objective S stPrev.xbar.1 - objective S u.1))
    _ =
      (1 - gamma k) * (objective S stPrev.xbar.1 - objective S u.1) +
        gamma k *
          (beta k * (1 - psWeightProduct spsP (T k))⁻¹ *
              (bregmanFormulaOnX S stPrev.x u -
                bregmanFormulaOnX S stCurr.x u) +
            psWeightProduct spsP (T k) *
              (1 - psWeightProduct spsP (T k))⁻¹ *
                (Finset.range (T k)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample k i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
                      ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))) := by
          simp [P, invOneMinusP, Vprev, Vcurr, noise]


/-- Generated-run formula-extension version of Lan Eq. (8.1.69).

Candidate audit: considered the pre-searched selected
`SGSMasterInequality_8_1_69_formulaExtension`, SOptLib telescope helpers
`finite_window_weighted_recurrence_telescope_with_tail_sums` and
`integral_scaled_finset_sum_le_scaled_sum_of_integral_bounds`, and target-file
generated-process projections around `IsGeneratedSGSProcess`.  The selected
master theorem is tied to `sgsProcess_formulaExtensionSelector`, while this
paper step must use the arbitrary relation-form generated run `hrun`; the
SOptLib lemmas provide only scalar/integral infrastructure, not the SGS
transition-to-noise bridge.  This helper aligns with Lan Theorem 8.2 proof step
1 by exposing Eq. (8.1.69) for the actual generated `states`/`inner`. -/
theorem generated_sgs_master_inequality_8_1_69_formulaExtension
    (x0 : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T sample states inner)
    (u : FeasiblePoint S)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T) :
    ∀ ω,
      objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S u ≤
        Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
            bregmanFormulaOnX S x0 u +
          Gamma N *
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              let stPrev := states k ω;
              let δinner := inner κ;
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                        ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))) := by
  classical
  -- Direct proof attempt: unfold the generated-process spine to recover the
  -- per-outer SPS process and outer update equations.  The remaining work is
  -- to port the already proved selected telescope to these relation-form
  -- projections without assuming selector equality for the nonunique SPS
  -- argmins.
  have hrun' : IsGeneratedSGSProcess S x0 beta gamma T sample states inner := by
    exact hrun
  have hinit : ∀ ω, states 0 ω = sgsInitial S x0 := hrun'.1
  have hinner_proc :
      ∀ k : PositiveTime,
        IsGeneratedSPSProcess S
          (fun ω u =>
            smoothLinearization S
              (outerExtrapolation S gamma k (states (k.1 - 1) ω)) u)
          (fun ω => (states (k.1 - 1) ω).x)
          (beta k) (sample k) (inner k) := hrun'.2.1
  have houter_update :
      ∀ k : PositiveTime, ∀ ω,
        (states k.1 ω).x = (inner k (T k) ω).u ∧
          (states k.1 ω).xbar.1 =
            (1 - gamma k) • (states (k.1 - 1) ω).xbar.1 +
              gamma k • (inner k (T k) ω).avg.1 := hrun'.2.2.1
  have hgamma_nonneg : gammaNonnegativeCondition gamma := hrun'.2.2.2
  have hTpos : ∀ k : PositiveTime, 0 < T k :=
    positive_inner_budget_of_forwardMonotonicity_beforeMaster beta gamma Gamma T hmono
  have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
    outer_gamma_positive_of_weight_condition_and_forward_denom_beforeMaster
      beta gamma Gamma T hgamma hGamma hmono
  have hforward_coeff_mono :
      ∀ n, (hn : 1 ≤ n) →
        gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ *
            beta ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ /
              (Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ *
                (1 - psWeightProduct spsP
                  (T ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩))) ≤
          gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
              (Gamma ⟨n, hn⟩ *
                (1 - psWeightProduct spsP (T ⟨n, hn⟩))) :=
    forwardMonotonicity_nat_coeff_mono_beforeMaster beta gamma Gamma T hmono
  intro ω
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  let process : ℕ → SGSState S := fun n => states n ω
  let A : ℕ → ℝ := fun n => objective S (process n).xbar.1 - objective S u.1
  let V : ℕ → ℝ := fun n => bregmanFormulaOnX S (process n).x u
  let alpha : ℕ → ℝ := fun n => if hn : 1 ≤ n then gamma ⟨n, hn⟩ else 0
  let GammaNat : ℕ → ℝ := fun n => if hn : 1 ≤ n then Gamma ⟨n, hn⟩ else 1
  let D : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then
      let κ : PositiveTime := ⟨n, hn⟩
      let δinner := inner κ;
      gamma κ *
        (beta κ * (1 - psWeightProduct spsP (T κ))⁻¹ *
            (V (n - 1) - V n) +
          psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
              (Finset.range (T κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
                (spsP ι * psWeightProduct spsP i)⁻¹ *
                  (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                    ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ)))
    else 0
  have hGammaNat_ne : ∀ t, 1 ≤ t → GammaNat t ≠ 0 := by
    intro t ht
    simp [GammaNat, ht, ne_of_gt (hGamma_pos ⟨t, ht⟩)]
  have hGammaNat_one : GammaNat 1 = 1 := by
    have hOne : (⟨1, by norm_num⟩ : PositiveTime) = oneTime := by
      ext
      rfl
    simp [GammaNat, hOne, hGamma.1]
  have halpha_one : alpha 1 = 1 := by
    have hOne : (⟨1, by norm_num⟩ : PositiveTime) = oneTime := by
      ext
      rfl
    simp [alpha, hOne, hlower.1]
  have halpha_le_one : ∀ t, 1 ≤ t → alpha t ≤ 1 := by
    intro t ht
    simpa [alpha, ht] using (hgamma ⟨t, ht⟩).2
  have hGamma_succ_nat :
      ∀ t, 1 ≤ t → GammaNat (t + 1) = (1 - alpha (t + 1)) * GammaNat t := by
    intro t ht
    have htpos : 1 ≤ t + 1 := by omega
    have hk2 : 2 ≤ t + 1 := by omega
    let κ : PositiveTime := ⟨t + 1, htpos⟩
    have hpred : predTime κ hk2 = (⟨t, ht⟩ : PositiveTime) := by
      apply Subtype.ext
      simp [κ, predTime]
    have h := hGamma.2 κ hk2
    simpa [GammaNat, alpha, ht, htpos, κ, hpred] using h
  have hstep_nat : ∀ t, 1 ≤ t →
      A t ≤ (1 - alpha t) * A (t - 1) + D t := by
    intro t ht
    have hs :=
      generated_sgs_one_step_gap_recurrence_formulaExtension
        (S := S) beta gamma T sample hbeta hgamma hlower
        ⟨t, ht⟩ (hTpos ⟨t, ht⟩) states inner (hinner_proc ⟨t, ht⟩) ω
        (houter_update ⟨t, ht⟩ ω) u
    simpa [A, D, alpha, process, V, ht] using hs
  have hrawIcc :
      A N.1 ≤ GammaNat N.1 *
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) := by
    exact
      finite_window_weighted_recurrence_telescope_no_source_beforeMaster
        alpha GammaNat A D N.1 N.2 hGammaNat_ne hGammaNat_one
        halpha_one halpha_le_one hGamma_succ_nat hstep_nat
  let c : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then
      gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
        (Gamma ⟨n, hn⟩ * (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
    else 0
  have hV_nonneg_window : ∀ n, 1 ≤ n → n ≤ N.1 → 0 ≤ V n := by
    intro n _hn _hnN
    have hB := bregmanFormulaOnX_lower_bound_from_prox_geometry S (process n).x u
    have hsq : 0 ≤ S.primalNorm (u.1 - (process n).x.1) ^ 2 := sq_nonneg _
    nlinarith
  have hc_mono : ∀ n, 1 ≤ n → n < N.1 → c (n + 1) ≤ c n := by
    intro n hn _hnN
    have h := hforward_coeff_mono n hn
    simpa [c, hn] using h
  have hc_nonneg : ∀ n, 1 ≤ n → 0 ≤ c n := by
    intro n hn
    let κ : PositiveTime := ⟨n, hn⟩
    have hOneSub : 0 < 1 - psWeightProduct spsP (T κ) :=
      one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)
    have hden : 0 < Gamma κ * (1 - psWeightProduct spsP (T κ)) :=
      mul_pos (hGamma_pos κ) hOneSub
    have hnum : 0 ≤ gamma κ * beta κ :=
      mul_nonneg (hgamma κ).1 (le_of_lt (hbeta κ))
    have hcκ :
        0 ≤ gamma κ * beta κ /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) :=
      div_nonneg hnum (le_of_lt hden)
    simpa [c, κ, hn] using hcκ
  have hbregIcc :
      Finset.sum (Finset.Icc 1 N.1) (fun t => c t * (V (t - 1) - V t)) ≤
        c 1 * V 0 := by
    have htail : 0 ≤ c N.1 * V N.1 :=
      mul_nonneg (hc_nonneg N.1 N.2)
        (hV_nonneg_window N.1 N.2 (le_refl N.1))
    exact
      sum_weighted_sub_le_first_of_forward_mono_beforeMaster c V N.1 N.2
        hV_nonneg_window hc_mono htail
  have hV_zero : V 0 = bregmanFormulaOnX S x0 u := by
    simp [V, process, hinit ω, sgsInitial]
  have hc_one :
      c 1 = beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ := by
    have hOne : (⟨1, by norm_num⟩ : PositiveTime) = oneTime := by
      ext
      rfl
    have hden :
        1 - psWeightProduct spsP (T oneTime) ≠ 0 :=
      ne_of_gt (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos oneTime))
    simp [c, hOne, hGamma.1, hlower.1, hden, div_eq_mul_inv]
  have hbregBoundary :
      c 1 * V 0 =
        beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
          bregmanFormulaOnX S x0 u := by
    rw [hc_one, hV_zero]
  let rawNoise : PositiveTime → ℝ := fun κ =>
    let δinner := inner κ;
    gamma κ * psWeightProduct spsP (T κ) /
      (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
          (spsP ι * psWeightProduct spsP i)⁻¹ *
            (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
              ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))
  let relaxedNoise : PositiveTime → ℝ := fun κ =>
    let δinner := inner κ;
    gamma κ * psWeightProduct spsP (T κ) /
      (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
          (spsP ι * psWeightProduct spsP i)⁻¹ *
            ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
              ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))
  let rawNoiseRange : ℝ :=
    (Finset.range N.1).sum (fun k => rawNoise ⟨k + 1, Nat.succ_pos k⟩)
  let relaxedNoiseRange : ℝ :=
    (Finset.range N.1).sum (fun k => relaxedNoise ⟨k + 1, Nat.succ_pos k⟩)
  let boundary : ℝ :=
    beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
      bregmanFormulaOnX S x0 u
  have hobj_eq :
      objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
        objectiveOn S u = A N.1 := by
    simp [A, process, sgsGeneratedOutput, objectiveOn]
  have hGammaNat_N : GammaNat N.1 = Gamma N := by
    simp [GammaNat, N.2]
  have hpoint : ∀ t (ht : 1 ≤ t),
      D t / GammaNat t = c t * (V (t - 1) - V t) + rawNoise ⟨t, ht⟩ := by
    intro t ht
    simp [D, GammaNat, c, rawNoise, ht, div_eq_mul_inv]
    ring
  have hsplit :
      Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) =
        Finset.sum (Finset.Icc 1 N.1) (fun t => c t * (V (t - 1) - V t)) +
          rawNoiseRange := by
    have hsum_point :
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) =
          Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t) +
              if ht : 1 ≤ t then rawNoise ⟨t, ht⟩ else 0) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem
      have ht : 1 ≤ t := (Finset.mem_Icc.mp htmem).1
      rw [hpoint t ht]
      simp [ht]
    rw [hsum_point]
    rw [Finset.sum_add_distrib]
    congr 1
    exact positiveTime_Icc_range_sum_reindex_beforeMaster N.1 N.2 rawNoise
  have hbreg_bound :
      Finset.sum (Finset.Icc 1 N.1) (fun t => c t * (V (t - 1) - V t)) ≤
        boundary := by
    simpa [boundary, hbregBoundary] using hbregIcc
  have hsum_le :
      Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) ≤
        boundary + rawNoiseRange := by
    rw [hsplit]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right hbreg_bound rawNoiseRange
  have hnoise_relax_local : rawNoiseRange ≤ relaxedNoiseRange := by
    refine Finset.sum_le_sum ?_
    intro k hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
    let δinner := inner κ;
    have hPpos : 0 < psWeightProduct spsP (T κ) := by
      rw [psWeightProduct_spsP_eq (T κ)]
      positivity
    have hOneSubpos : 0 < 1 - psWeightProduct spsP (T κ) :=
      one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)
    have houter_nonneg :
        0 ≤ gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) := by
      exact div_nonneg
        (mul_nonneg (hgamma κ).1 (le_of_lt hPpos))
        (le_of_lt (mul_pos (hGamma_pos κ) hOneSubpos))
    refine mul_le_mul_of_nonneg_left ?_ houter_nonneg
    refine Finset.sum_le_sum ?_
    intro i hi
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
    let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
    have hspsP_pos : 0 < spsP ι := by
      unfold spsP
      positivity
    have hprod_pos : 0 < psWeightProduct spsP i := by
      rw [psWeightProduct_spsP_eq i]
      positivity
    have hinner_coeff_nonneg :
        0 ≤ (spsP ι * psWeightProduct spsP i)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt (mul_pos hspsP_pos hprod_pos))
    have hpoint_noise :
        ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
            ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ ≤
          (S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
            ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ := by
      have hsquare :=
        sps_noise_square_relaxation_beforeMaster (β := beta κ) (p := spsP ι)
          (M := S.mGrowth) (d := dualNorm S δ) (hbeta κ) hspsP_pos
          S.M_pos.le (SOptLib.canonicalDualNorm_nonneg S.primalNorm δ)
      linarith
    exact mul_le_mul_of_nonneg_left hpoint_noise hinner_coeff_nonneg
  have hGamma_nonneg : 0 ≤ Gamma N := le_of_lt (hGamma_pos N)
  have hscaled_sum :
      Gamma N * Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) ≤
        Gamma N * (boundary + rawNoiseRange) :=
    mul_le_mul_of_nonneg_left hsum_le hGamma_nonneg
  have hscaled_noise :
      Gamma N * (boundary + rawNoiseRange) ≤
        Gamma N * (boundary + relaxedNoiseRange) := by
    have hbase : boundary + rawNoiseRange ≤ boundary + relaxedNoiseRange := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hnoise_relax_local boundary
    exact mul_le_mul_of_nonneg_left hbase hGamma_nonneg
  calc
    objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
        objectiveOn S u = A N.1 := hobj_eq
    _ ≤ GammaNat N.1 *
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) := hrawIcc
    _ = Gamma N *
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) := by
      rw [hGammaNat_N]
    _ ≤ Gamma N * (boundary + rawNoiseRange) := hscaled_sum
    _ ≤ Gamma N * (boundary + relaxedNoiseRange) := hscaled_noise
    _ = Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
            bregmanFormulaOnX S x0 u +
          Gamma N *
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              let stPrev := states k ω;
              let δinner := inner κ;
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                        ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))) := by
      simp [boundary, relaxedNoiseRange, relaxedNoise]
      ring

/-- Raw generated-run Eq. (8.1.69) before either forward or reverse
monotonicity collapses the Bregman-drop telescope.

Aligns with Lan Eq. (8.1.69), proof step 1: the outer recurrence and SPS
inner bound telescope to an explicit weighted Bregman-drop sum plus stochastic
noise. Candidate audit: considered the existing generated master
`generated_sgs_master_inequality_8_1_69_formulaExtension`, the selected-process
master around `SGSMasterInequality_8_1_69_formulaExtension`, SOptLib
`finite_window_weighted_recurrence_telescope_with_tail_sums`, and searches
`raw generated master Bregman drop stochastic noise` / `weighted recurrence
telescope no source Bregman drop sum`; the existing masters already consume
forward monotonicity or are selector-specific, while the SOptLib telescope does
not include the SGS transition/noise bridge. -/
theorem generated_sgs_raw_master_inequality_8_1_69_formulaExtension
    (x0 : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T sample states inner)
    (u : FeasiblePoint S)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hTpos : ∀ k : PositiveTime, 0 < T k)
    (hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k) :
    ∀ ω,
      objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
          objectiveOn S u ≤
        Gamma N *
          (let process : ℕ → SGSState S := fun n => states n ω;
           let c : ℕ → ℝ := fun n =>
            if hn : 1 ≤ n then
              gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
                (Gamma ⟨n, hn⟩ *
                  (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
            else 0;
           let V : ℕ → ℝ := fun n => bregmanFormulaOnX S (process n).x u;
           Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t))) +
          Gamma N *
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              let δinner := inner κ;
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                        ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))) := by
  classical
  have hrun' : IsGeneratedSGSProcess S x0 beta gamma T sample states inner := by
    exact hrun
  have hinit : ∀ ω, states 0 ω = sgsInitial S x0 := hrun'.1
  have hinner_proc :
      ∀ k : PositiveTime,
        IsGeneratedSPSProcess S
          (fun ω u =>
            smoothLinearization S
              (outerExtrapolation S gamma k (states (k.1 - 1) ω)) u)
          (fun ω => (states (k.1 - 1) ω).x)
          (beta k) (sample k) (inner k) := hrun'.2.1
  have houter_update :
      ∀ k : PositiveTime, ∀ ω,
        (states k.1 ω).x = (inner k (T k) ω).u ∧
          (states k.1 ω).xbar.1 =
            (1 - gamma k) • (states (k.1 - 1) ω).xbar.1 +
              gamma k • (inner k (T k) ω).avg.1 := hrun'.2.2.1
  intro ω
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  let process : ℕ → SGSState S := fun n => states n ω
  let A : ℕ → ℝ := fun n => objective S (process n).xbar.1 - objective S u.1
  let V : ℕ → ℝ := fun n => bregmanFormulaOnX S (process n).x u
  let alpha : ℕ → ℝ := fun n => if hn : 1 ≤ n then gamma ⟨n, hn⟩ else 0
  let GammaNat : ℕ → ℝ := fun n => if hn : 1 ≤ n then Gamma ⟨n, hn⟩ else 1
  let D : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then
      let κ : PositiveTime := ⟨n, hn⟩
      let δinner := inner κ;
      gamma κ *
        (beta κ * (1 - psWeightProduct spsP (T κ))⁻¹ *
            (V (n - 1) - V n) +
          psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
              (Finset.range (T κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
                (spsP ι * psWeightProduct spsP i)⁻¹ *
                  (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                    ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ)))
    else 0
  have hGammaNat_ne : ∀ t, 1 ≤ t → GammaNat t ≠ 0 := by
    intro t ht
    simp [GammaNat, ht, ne_of_gt (hGamma_pos ⟨t, ht⟩)]
  have hGammaNat_one : GammaNat 1 = 1 := by
    have hOne : (⟨1, by norm_num⟩ : PositiveTime) = oneTime := by
      ext
      rfl
    simp [GammaNat, hOne, hGamma.1]
  have halpha_one : alpha 1 = 1 := by
    have hOne : (⟨1, by norm_num⟩ : PositiveTime) = oneTime := by
      ext
      rfl
    simp [alpha, hOne, hlower.1]
  have halpha_le_one : ∀ t, 1 ≤ t → alpha t ≤ 1 := by
    intro t ht
    simpa [alpha, ht] using (hgamma ⟨t, ht⟩).2
  have hGamma_succ_nat :
      ∀ t, 1 ≤ t → GammaNat (t + 1) = (1 - alpha (t + 1)) * GammaNat t := by
    intro t ht
    have htpos : 1 ≤ t + 1 := by omega
    have hk2 : 2 ≤ t + 1 := by omega
    let κ : PositiveTime := ⟨t + 1, htpos⟩
    have hpred : predTime κ hk2 = (⟨t, ht⟩ : PositiveTime) := by
      apply Subtype.ext
      simp [κ, predTime]
    have h := hGamma.2 κ hk2
    simpa [GammaNat, alpha, ht, htpos, κ, hpred] using h
  have hstep_nat : ∀ t, 1 ≤ t →
      A t ≤ (1 - alpha t) * A (t - 1) + D t := by
    intro t ht
    have hs :=
      generated_sgs_one_step_gap_recurrence_formulaExtension
        (S := S) beta gamma T sample hbeta hgamma hlower
        ⟨t, ht⟩ (hTpos ⟨t, ht⟩) states inner (hinner_proc ⟨t, ht⟩) ω
        (houter_update ⟨t, ht⟩ ω) u
    simpa [A, D, alpha, process, V, ht] using hs
  have hrawIcc :
      A N.1 ≤ GammaNat N.1 *
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) := by
    exact
      finite_window_weighted_recurrence_telescope_no_source_beforeMaster
        alpha GammaNat A D N.1 N.2 hGammaNat_ne hGammaNat_one
        halpha_one halpha_le_one hGamma_succ_nat hstep_nat
  let c : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then
      gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
        (Gamma ⟨n, hn⟩ * (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
    else 0
  let rawNoise : PositiveTime → ℝ := fun κ =>
    let δinner := inner κ;
    gamma κ * psWeightProduct spsP (T κ) /
      (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
          (spsP ι * psWeightProduct spsP i)⁻¹ *
            (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
              ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))
  let relaxedNoise : PositiveTime → ℝ := fun κ =>
    let δinner := inner κ;
    gamma κ * psWeightProduct spsP (T κ) /
      (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
          (spsP ι * psWeightProduct spsP i)⁻¹ *
            ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
              ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))
  let rawNoiseRange : ℝ :=
    (Finset.range N.1).sum (fun k => rawNoise ⟨k + 1, Nat.succ_pos k⟩)
  let relaxedNoiseRange : ℝ :=
    (Finset.range N.1).sum (fun k => relaxedNoise ⟨k + 1, Nat.succ_pos k⟩)
  have hobj_eq :
      objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
        objectiveOn S u = A N.1 := by
    simp [A, process, sgsGeneratedOutput, objectiveOn]
  have hGammaNat_N : GammaNat N.1 = Gamma N := by
    simp [GammaNat, N.2]
  have hpoint : ∀ t (ht : 1 ≤ t),
      D t / GammaNat t = c t * (V (t - 1) - V t) + rawNoise ⟨t, ht⟩ := by
    intro t ht
    simp [D, GammaNat, c, rawNoise, ht, div_eq_mul_inv]
    ring
  have hsplit :
      Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) =
        Finset.sum (Finset.Icc 1 N.1) (fun t => c t * (V (t - 1) - V t)) +
          rawNoiseRange := by
    have hsum_point :
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) =
          Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t) +
              if ht : 1 ≤ t then rawNoise ⟨t, ht⟩ else 0) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem
      have ht : 1 ≤ t := (Finset.mem_Icc.mp htmem).1
      rw [hpoint t ht]
      simp [ht]
    rw [hsum_point]
    rw [Finset.sum_add_distrib]
    congr 1
    exact positiveTime_Icc_range_sum_reindex_beforeMaster N.1 N.2 rawNoise
  have hnoise_relax_local : rawNoiseRange ≤ relaxedNoiseRange := by
    refine Finset.sum_le_sum ?_
    intro k hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
    let δinner := inner κ;
    have hPpos : 0 < psWeightProduct spsP (T κ) := by
      rw [psWeightProduct_spsP_eq (T κ)]
      positivity
    have hOneSubpos : 0 < 1 - psWeightProduct spsP (T κ) :=
      one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)
    have houter_nonneg :
        0 ≤ gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) := by
      exact div_nonneg
        (mul_nonneg (hgamma κ).1 (le_of_lt hPpos))
        (le_of_lt (mul_pos (hGamma_pos κ) hOneSubpos))
    refine mul_le_mul_of_nonneg_left ?_ houter_nonneg
    refine Finset.sum_le_sum ?_
    intro i hi
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
    let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω)
    have hspsP_pos : 0 < spsP ι := by
      unfold spsP
      positivity
    have hprod_pos : 0 < psWeightProduct spsP i := by
      rw [psWeightProduct_spsP_eq i]
      positivity
    have hinner_coeff_nonneg :
        0 ≤ (spsP ι * psWeightProduct spsP i)⁻¹ := by
      exact inv_nonneg.mpr (le_of_lt (mul_pos hspsP_pos hprod_pos))
    have hpoint_noise :
        ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
            ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ ≤
          (S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
            ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ := by
      have hsquare :=
        sps_noise_square_relaxation_beforeMaster (β := beta κ) (p := spsP ι)
          (M := S.mGrowth) (d := dualNorm S δ) (hbeta κ) hspsP_pos
          S.M_pos.le (SOptLib.canonicalDualNorm_nonneg S.primalNorm δ)
      linarith
    exact mul_le_mul_of_nonneg_left hpoint_noise hinner_coeff_nonneg
  have hGamma_nonneg : 0 ≤ Gamma N := le_of_lt (hGamma_pos N)
  have hscaled_sum :
      Gamma N * Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) ≤
        Gamma N *
          (Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)) + rawNoiseRange) := by
    rw [hsplit]
  have hscaled_noise :
      Gamma N *
          (Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)) + rawNoiseRange) ≤
        Gamma N *
          (Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)) + relaxedNoiseRange) := by
    have hbase :
        Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)) + rawNoiseRange ≤
          Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)) + relaxedNoiseRange := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hnoise_relax_local
          (Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)))
    exact mul_le_mul_of_nonneg_left hbase hGamma_nonneg
  calc
    objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
        objectiveOn S u = A N.1 := hobj_eq
    _ ≤ GammaNat N.1 *
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) := hrawIcc
    _ = Gamma N *
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) := by
      rw [hGammaNat_N]
    _ ≤ Gamma N *
          (Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)) + rawNoiseRange) := hscaled_sum
    _ ≤ Gamma N *
          (Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t)) + relaxedNoiseRange) := hscaled_noise
    _ =
        Gamma N *
          (Finset.sum (Finset.Icc 1 N.1) (fun t =>
            c t * (V (t - 1) - V t))) +
          Gamma N *
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              let δinner := inner κ;
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((δinner i ω).u.1) (sample κ i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                        ⟪δ, u.1 - (δinner i ω).u.1⟫_ℝ))) := by
      simp [relaxedNoiseRange, relaxedNoise]
      ring

/-- Single stochastic bracket expectation step used in Theorem 8.2 proof step 2:
the linear martingale term integrates to zero, and the quadratic noise term is
bounded by its second-moment budget under a nonnegative deterministic scale. -/
theorem theorem82_expected_single_noise_bracket_le
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M σ betaP : ℝ) (quad lin : Ω → ℝ)
    (hquad_int : Integrable quad μ) (hlin_int : Integrable lin μ)
    (hquad_bound : (∫ ω, quad ω ∂μ) ≤ σ)
    (hlin_zero : (∫ ω, lin ω ∂μ) = 0)
    (hscale_nonneg : 0 ≤ betaP⁻¹) :
    (∫ ω, (M + quad ω) / betaP + lin ω ∂μ) ≤ (M + σ) / betaP := by
  have hscaled_int : Integrable (fun ω => (M + quad ω) / betaP) μ := by
    have hsum : Integrable (fun ω => M + quad ω) μ :=
      (integrable_const (c := M)).add hquad_int
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hsum.const_mul betaP⁻¹
  have hsplit :
      (∫ ω, (M + quad ω) / betaP + lin ω ∂μ) =
        (∫ ω, (M + quad ω) / betaP ∂μ) + ∫ ω, lin ω ∂μ :=
    integral_add hscaled_int hlin_int
  have hscaled :
      (∫ ω, (M + quad ω) / betaP ∂μ) ≤ (M + σ) / betaP := by
    have hrewrite :
        (∫ ω, (M + quad ω) / betaP ∂μ) =
          betaP⁻¹ * (M + ∫ ω, quad ω ∂μ) := by
      calc
        (∫ ω, (M + quad ω) / betaP ∂μ)
            = ∫ ω, betaP⁻¹ * (M + quad ω) ∂μ := by
                congr 1
                ext ω
                rw [div_eq_mul_inv, mul_comm]
        _ = betaP⁻¹ * ∫ ω, M + quad ω ∂μ := by
                rw [integral_const_mul]
        _ = betaP⁻¹ * (M + ∫ ω, quad ω ∂μ) := by
                rw [integral_add (integrable_const (c := M)) hquad_int]
                simp
    calc
      (∫ ω, (M + quad ω) / betaP ∂μ)
          = betaP⁻¹ * (M + ∫ ω, quad ω ∂μ) := hrewrite
      _ ≤ betaP⁻¹ * (M + σ) := by
            have hsum_le : M + (∫ ω, quad ω ∂μ) ≤ M + σ :=
              by
                simpa [add_comm, add_left_comm, add_assoc] using
                  add_le_add_left hquad_bound M
            exact mul_le_mul_of_nonneg_left
              hsum_le hscale_nonneg
      _ = (M + σ) / betaP := by
            rw [div_eq_mul_inv]
            ring
  calc
    (∫ ω, (M + quad ω) / betaP + lin ω ∂μ)
        = (∫ ω, (M + quad ω) / betaP ∂μ) + ∫ ω, lin ω ∂μ := hsplit
    _ = (∫ ω, (M + quad ω) / betaP ∂μ) := by simp [hlin_zero]
    _ ≤ (M + σ) / betaP := hscaled

/-- Finite aggregation for deterministic nonnegative coefficients in the
Theorem 8.2 expectation algebra.  This is the local form of the standard
finite-sum expectation step used after applying the single noise bracket bound. -/
theorem theorem82_integral_finset_sum_scaled_le
    [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} (s : Finset ι) (scale bound : ι → ℝ) (summand : ι → Ω → ℝ)
    (hsummand_int : ∀ i ∈ s, Integrable (summand i) μ)
    (hsummand_bound : ∀ i ∈ s, (∫ ω, summand i ω ∂μ) ≤ bound i)
    (hscale_nonneg : ∀ i ∈ s, 0 ≤ scale i) :
    (∫ ω, s.sum (fun i => scale i * summand i ω) ∂μ) ≤
      s.sum (fun i => scale i * bound i) := by
  classical
  have hterm_int :
      ∀ i ∈ s, Integrable (fun ω => scale i * summand i ω) μ := by
    intro i hi
    exact (hsummand_int i hi).const_mul (scale i)
  rw [integral_finset_sum s hterm_int]
  refine Finset.sum_le_sum ?_
  intro i hi
  calc
    (∫ ω, scale i * summand i ω ∂μ)
        = scale i * ∫ ω, summand i ω ∂μ := by
            rw [integral_const_mul]
    _ ≤ scale i * bound i := by
            exact mul_le_mul_of_nonneg_left (hsummand_bound i hi)
              (hscale_nonneg i hi)

/-- Corrected generated-run formula-extension helper for Theorem 8.2(a).

This is the FILL-ready branch corresponding to the conditional source-boundary
variant
`SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman_under_gammaRange`.
The additional `hgamma` premise is precisely the condition consumed by
`OuterOneStep_8_1_31_formulaExtension` through
`outer_h_chi_convex_combination_8_1_28`; it is not hidden in the generated-run
relation. -/
theorem SGSGenericConvergence_Theorem8_2_expected_runFormulaExtension_under_gammaRange
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T) :
    (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
        objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
      theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N beta gamma Gamma T := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  have hquad :
      ∀ κ i,
        (∫ ω,
          dualNorm S
            (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω)) ^ 2 ∂law.P) ≤ S.sigmaSq :=
    sgsGeneratedOracleQuery_dual_noise_sq_integral_le
      (S := S) law.P law.sample inner hgenerated_var
  have hlinear_zero_of_integrable :
      (∀ κ i (hquery : ∀ ω, sgsGeneratedOracleQuery S inner κ i ω ∈ S.X),
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              xStar - (sgsGeneratedOracleQuery S inner κ i ω)⟫_ℝ)
          law.P) →
        ∀ κ i,
          (∫ ω,
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ ∂law.P) = 0 := by
    intro hinner_int
    simpa using
      sgsGeneratedOracleQuery_target_noise_inner_integral_zero_of_integrable
        (S := S) (law := law) inner ⟨xStar, hxStar.1⟩ hindep hinner_int
  have hmaster :
      ∀ ω,
        objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ ≤
          Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
              bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
            Gamma N *
              (Finset.range N.1).sum (fun k =>
                let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                let stPrev := states k ω;
                let δinner := inner κ;
                gamma κ * psWeightProduct spsP (T κ) /
                  (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                    (Finset.range (T κ)).sum (fun i =>
                      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                      let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                      (spsP ι * psWeightProduct spsP i)⁻¹ *
                        ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                          ⟪δ, xStar - (δinner i ω).u.1⟫_ℝ))) :=
    generated_sgs_master_inequality_8_1_69_formulaExtension
      (S := S) x0 beta gamma Gamma T law.sample N states inner hrun.1
      ⟨xStar, hxStar.1⟩ hbeta hgamma hlower hGamma hmono
  classical
  let gap : Ω → ℝ := fun ω =>
    objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
      objectiveOn S ⟨xStar, hxStar.1⟩
  let masterRHS : Ω → ℝ := fun ω =>
    Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
        bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
      Gamma N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
          let δinner := inner κ;
          gamma κ * psWeightProduct spsP (T κ) /
            (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
              (Finset.range (T κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                (spsP ι * psWeightProduct spsP i)⁻¹ *
                  ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                    ⟪δ, xStar - (δinner i ω).u.1⟫_ℝ)))
  have hmaster_pointwise : gap ≤ masterRHS := by
    intro ω
    simpa [gap, masterRHS] using hmaster ω
  rcases hindep with ⟨hquery_mem, hquery_meas, _hindep_qs⟩
  have hdual_sq_int :
      ∀ κ i,
        Integrable
          (fun ω =>
            dualNorm S
              (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω)) ^ 2) law.P := by
    intro κ i
    simpa using
      generatedSFOVariance_integrable_obligation
        S law.P law.sample (sgsGeneratedOracleQuery S inner) hgenerated_var κ i
  have hquery_disp_sq_int :
      ∀ κ i,
        Integrable
          (fun ω =>
            S.primalNorm
              (xStar - sgsGeneratedOracleQuery S inner κ i ω) ^ 2) law.P := by
    letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
    have hgenerated_avg_sq_from_bregman_window :
        ∀ κ m,
          (∀ i, i < m + 1 →
            Integrable
              (fun ω =>
                bregmanFormulaOnX S
                  (⟨sgsGeneratedOracleQuery S inner κ i ω,
                    hquery_mem κ i ω⟩ : FeasiblePoint S)
                  ⟨xStar, hxStar.1⟩)
              law.P) →
          Integrable
            (fun ω =>
              S.primalNorm
                (xStar - (inner κ m ω).avg.1) ^ 2) law.P := by
      intro κ m hwindow
      simpa using
        generated_sgs_inner_avg_sq_integrable_from_bregman_window
          (S := S) law ⟨xStar, hxStar.1⟩ x0 beta gamma T states inner
          hrun hquery_mem hquery_meas κ m hwindow
    -- Remaining generated-process recurrence leaf: prove the Bregman
    -- integrability window for every generated SPS query from the Phi/Bregman
    -- finite telescope; the average L2 side above is now available for that
    -- relation-form route.
    have hrun' : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner := by
      exact hrun.1
    have hinit : ∀ ω, states 0 ω = sgsInitial S x0 := hrun'.1
    have hinner_proc :
        ∀ k : PositiveTime,
          IsGeneratedSPSProcess S
            (fun ω u =>
              smoothLinearization S
                (outerExtrapolation S gamma k (states (k.1 - 1) ω)) u)
            (fun ω => (states (k.1 - 1) ω).x)
            (beta k) (law.sample k) (inner k) := hrun'.2.1
    have houter_update :
        ∀ k : PositiveTime, ∀ ω,
          (states k.1 ω).x = (inner k (T k) ω).u ∧
            (states k.1 ω).xbar.1 =
              (1 - gamma k) • (states (k.1 - 1) ω).xbar.1 +
                gamma k • (inner k (T k) ω).avg.1 := hrun'.2.2.1
    have hstates_xbar_meas :
        ∀ n : ℕ, AEStronglyMeasurable (fun ω => (states n ω).xbar.1) law.P := by
      intro n
      induction n with
      | zero =>
          refine (aestronglyMeasurable_const :
            AEStronglyMeasurable (fun _ : Ω => x0.1) law.P).congr
              (Filter.Eventually.of_forall ?_)
          intro ω
          simp [hinit ω, sgsInitial]
      | succ m ihm =>
          let κcur : PositiveTime := ⟨m + 1, Nat.succ_pos m⟩
          have hprocess := hinner_proc κcur
          have hu_meas : ∀ i, Measurable (fun ω => (inner κcur i ω).u) := by
            intro i
            simpa [sgsGeneratedOracleQuery] using hquery_meas κcur i
          have havg_meas :
              AEStronglyMeasurable
                (fun ω => (inner κcur (T κcur) ω).avg.1) law.P :=
            generated_sps_avg_aestronglyMeasurable_of_u_meas
              (S := S) law.P
              (fun ω u =>
                smoothLinearization S
                  (outerExtrapolation S gamma κcur (states (κcur.1 - 1) ω)) u)
              (fun ω => (states (κcur.1 - 1) ω).x)
              (beta κcur) (law.sample κcur) (inner κcur) hprocess
              (fun i =>
                (measurable_subtype_coe.comp (hu_meas i)).aestronglyMeasurable)
              (T κcur)
          have hcombo :
              AEStronglyMeasurable
                (fun ω =>
                  (1 - gamma κcur) • (states m ω).xbar.1 +
                    gamma κcur • (inner κcur (T κcur) ω).avg.1) law.P :=
            (ihm.const_smul (1 - gamma κcur)).add
              (havg_meas.const_smul (gamma κcur))
          refine hcombo.congr (Filter.Eventually.of_forall ?_)
          intro ω
          have hxbar := (houter_update κcur ω).2
          simpa [κcur] using hxbar.symm
    let B : PositiveTime → ℕ → Prop := fun κ i =>
      Integrable
        (fun ω =>
          bregmanFormulaOnX S
            (⟨sgsGeneratedOracleQuery S inner κ i ω,
              hquery_mem κ i ω⟩ : FeasiblePoint S)
            ⟨xStar, hxStar.1⟩)
        law.P
    let Xbar : ℕ → Prop := fun n =>
      Integrable
        (fun ω =>
          S.primalNorm (xStar - (states n ω).xbar.1) ^ 2)
        law.P
    have hPair :
        ∀ n : ℕ,
          (∀ κ : PositiveTime, κ.1 = n → ∀ i : ℕ, B κ i) ∧ Xbar n := by
      intro n
      refine Nat.strong_induction_on n ?_
      intro n ih
      have hB_current : ∀ κ : PositiveTime, κ.1 = n → ∀ i : ℕ, B κ i := by
        intro κ hκ
        intro i
        refine Nat.strong_induction_on i ?_
        intro i ihInner
        cases i with
        | zero =>
            rcases κ with ⟨k, hk⟩
            cases k with
            | zero =>
                omega
            | succ k =>
                cases k with
                | zero =>
                    have hconst :
                        Integrable
                          (fun _ : Ω =>
                            bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩)
                          law.P :=
                      integrable_const _
                    have hcongr :
                        (fun ω =>
                          bregmanFormulaOnX S
                            (⟨sgsGeneratedOracleQuery S inner
                                (⟨1, by omega⟩ : PositiveTime) 0 ω,
                              hquery_mem (⟨1, by omega⟩ : PositiveTime) 0 ω⟩ :
                              FeasiblePoint S)
                            ⟨xStar, hxStar.1⟩) =
                        (fun _ : Ω =>
                          bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩) := by
                      funext ω
                      have hproc := hinner_proc (⟨1, by omega⟩ : PositiveTime)
                      have hinit_inner := hproc.2.1 ω
                      apply congrArg
                        (fun y : FeasiblePoint S =>
                          bregmanFormulaOnX S y ⟨xStar, hxStar.1⟩)
                      apply Subtype.ext
                      simpa [sgsGeneratedOracleQuery, hinit_inner, spsInitial,
                        hinit ω, sgsInitial]
                    change B (⟨1, by omega⟩ : PositiveTime) 0
                    simpa [B, hcongr] using hconst
                | succ k =>
                    let κcur : PositiveTime := ⟨k + 1 + 1, hk⟩
                    have hκcur_two : 2 ≤ κcur.1 := by
                      dsimp [κcur]
                      omega
                    have hpred_lt : (predTime κcur hκcur_two).1 < n := by
                      have hn_eq : n = k + 1 + 1 := by
                        simpa [κcur] using hκ.symm
                      subst hn_eq
                      dsimp [κcur, predTime]
                      omega
                    have hprev_terminal :
                        B (predTime κcur hκcur_two) (T (predTime κcur hκcur_two)) :=
                      (ih (predTime κcur hκcur_two).1 hpred_lt).1
                        (predTime κcur hκcur_two) rfl
                        (T (predTime κcur hκcur_two))
                    have hterminal :
                        ∀ ω,
                          sgsGeneratedOracleQuery S inner κcur 0 ω =
                            sgsGeneratedOracleQuery S inner
                              (predTime κcur hκcur_two)
                              (T (predTime κcur hκcur_two)) ω := by
                      intro ω
                      have hproc := hinner_proc κcur
                      have hinit_inner := hproc.2.1 ω
                      have houter := (houter_update (predTime κcur hκcur_two) ω).1
                      dsimp [sgsGeneratedOracleQuery]
                      rw [hinit_inner]
                      simp [spsInitial]
                      exact congrArg Subtype.val
                        (by
                          simpa [κcur, predTime] using houter)
                    have hcongr :
                        (fun ω =>
                          bregmanFormulaOnX S
                            (⟨sgsGeneratedOracleQuery S inner κcur 0 ω,
                              hquery_mem κcur 0 ω⟩ : FeasiblePoint S)
                            ⟨xStar, hxStar.1⟩) =
                        (fun ω =>
                          bregmanFormulaOnX S
                            (⟨sgsGeneratedOracleQuery S inner
                                (predTime κcur hκcur_two)
                                (T (predTime κcur hκcur_two)) ω,
                              hquery_mem (predTime κcur hκcur_two)
                                (T (predTime κcur hκcur_two)) ω⟩ : FeasiblePoint S)
                            ⟨xStar, hxStar.1⟩) := by
                      funext ω
                      simp [hterminal ω]
                    change B κcur 0
                    simpa [B, hcongr] using hprev_terminal
        | succ j =>
            have hprev_window : ∀ i, i < j + 1 → B κ i := by
              intro i hi
              exact ihInner i hi
            have houter_xbar_sq : Xbar (κ.1 - 1) := by
              have hprev_lt : κ.1 - 1 < n := by
                have hkpos : 0 < κ.1 := κ.2
                omega
              exact (ih (κ.1 - 1) hprev_lt).2
            exact
              generated_sgs_query_successor_bregman_integrable_of_prev_window
                (S := S) law ⟨xStar, hxStar.1⟩ x0 beta gamma T states inner
                hrun hbeta hgamma hquery_mem hquery_meas hgenerated_var κ j
                (by simpa [Xbar] using houter_xbar_sq) hprev_window
      have hXbar_current : Xbar n := by
        cases n with
        | zero =>
            refine (integrable_const
              (c := S.primalNorm (xStar - x0.1) ^ 2)).congr ?_
            filter_upwards with ω
            simp [Xbar, hinit ω, sgsInitial]
        | succ m =>
            let κcur : PositiveTime := ⟨m + 1, Nat.succ_pos m⟩
            have hprev_xbar_sq : Xbar m :=
              (ih m (Nat.lt_succ_self m)).2
            have hwindow :
                ∀ i, i < T κcur + 1 → B κcur i := by
              intro i _hi
              exact hB_current κcur rfl i
            have havg_sq :
                Integrable
                  (fun ω =>
                    S.primalNorm
                      (xStar - (inner κcur (T κcur) ω).avg.1) ^ 2)
                  law.P :=
              hgenerated_avg_sq_from_bregman_window κcur (T κcur) hwindow
            have hprev_meas :
                AEStronglyMeasurable (fun ω => (states m ω).xbar.1) law.P :=
              hstates_xbar_meas m
            have hprocess := hinner_proc κcur
            have hu_meas : ∀ i, Measurable (fun ω => (inner κcur i ω).u) := by
              intro i
              simpa [sgsGeneratedOracleQuery] using hquery_meas κcur i
            have havg_meas :
                AEStronglyMeasurable
                  (fun ω => (inner κcur (T κcur) ω).avg.1) law.P :=
              generated_sps_avg_aestronglyMeasurable_of_u_meas
                (S := S) law.P
                (fun ω u =>
                  smoothLinearization S
                    (outerExtrapolation S gamma κcur (states (κcur.1 - 1) ω)) u)
                (fun ω => (states (κcur.1 - 1) ω).x)
                (beta κcur) (law.sample κcur) (inner κcur) hprocess
                (fun i =>
                  (measurable_subtype_coe.comp (hu_meas i)).aestronglyMeasurable)
                (T κcur)
            have hcombo :
                Integrable
                  (fun ω =>
                    S.primalNorm
                      (xStar -
                        ((1 - gamma κcur) • (states m ω).xbar.1 +
                          gamma κcur • (inner κcur (T κcur) ω).avg.1)) ^ 2)
                  law.P :=
              primalNorm_sq_integrable_affine_update
                (S := S) law.P ⟨xStar, hxStar.1⟩
                (fun ω => (states m ω).xbar.1)
                (fun ω => (inner κcur (T κcur) ω).avg.1)
                (gamma κcur) hprev_meas havg_meas
                (by simpa [Xbar] using hprev_xbar_sq) havg_sq
            refine hcombo.congr ?_
            filter_upwards with ω
            have hxbar := (houter_update κcur ω).2
            simpa [Xbar, κcur, hxbar]
      exact ⟨hB_current, hXbar_current⟩
    have hbreg_all : ∀ κ i, B κ i := by
      intro κ i
      exact (hPair κ.1).1 κ rfl i
    intro κ i
    exact
      query_sq_integrable_of_bregman_integrable
        (S := S) law.P ⟨xStar, hxStar.1⟩
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner κ i ω,
            hquery_mem κ i ω⟩ : FeasiblePoint S))
        (hquery_meas κ i) (by simpa [B] using hbreg_all κ i)
  have hlinear_int :
      ∀ κ i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P := by
    intro κ i
    let queryFP : Ω → FeasiblePoint S :=
      fun ω => ⟨sgsGeneratedOracleQuery S inner κ i ω, hquery_mem κ i ω⟩
    have hpair_meas : Measurable (fun ω => (queryFP ω, law.sample κ i ω)) :=
      (hquery_meas κ i).prod (law.sample_measurable κ i)
    have hleft_inner_aemeas :
        AEStronglyMeasurable
          (fun ω =>
            ⟪xStar - sgsGeneratedOracleQuery S inner κ i ω,
              oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω)⟫_ℝ) law.P := by
      have hkernel :=
        oracle_residual_target_inner_measurable_of_residual_measurable
          (S := S) (x := ⟨xStar, hxStar.1⟩) law.oracle_residual_measurable
      simpa [queryFP] using (hkernel.comp hpair_meas).aestronglyMeasurable
    have hinner_aemeas :
        AEStronglyMeasurable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P :=
      hleft_inner_aemeas.congr
        (Filter.Eventually.of_forall (fun ω => by
          simpa using
            (real_inner_comm
              (xStar - sgsGeneratedOracleQuery S inner κ i ω)
              (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω))).symm))
    exact
      generated_target_inner_integrable_of_primal_displacement_l2
        (S := S) law.P law.sample (sgsGeneratedOracleQuery S inner)
        ⟨xStar, hxStar.1⟩ κ i (hdual_sq_int κ i)
        (hquery_disp_sq_int κ i) hinner_aemeas
  have hlinear_zero :
      ∀ κ i,
        (∫ ω,
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ ∂law.P) = 0 :=
    hlinear_zero_of_integrable (fun κ i _hquery => hlinear_int κ i)
  have hmasterRHS_int : Integrable masterRHS law.P := by
    have houter_const :
        Integrable
          (fun _ : Ω =>
            Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
              bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩) law.P :=
      integrable_const _
    let outerSum : Ω → ℝ := fun ω =>
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        let δinner := inner κ;
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                  ⟪δ, xStar - (δinner i ω).u.1⟫_ℝ)))
    have houter_sum : Integrable outerSum law.P := by
      refine integrable_finset_sum (Finset.range N.1) ?_
      intro k hk
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
      have hinner_sum :
          Integrable
            (fun ω =>
              (Finset.range (T κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω);
                (spsP ι * psWeightProduct spsP i)⁻¹ *
                  ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                    ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ))) law.P := by
        refine integrable_finset_sum (Finset.range (T κ)) ?_
        intro i hi
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
        have hquad_part :
            Integrable
              (fun ω =>
                (S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) /
                  (beta κ * spsP ι)) law.P := by
          have hsum :
              Integrable
                (fun ω =>
                  S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) law.P :=
            (integrable_const (c := S.mGrowth ^ 2)).add (hdual_sq_int κ i)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            hsum.const_mul ((beta κ * spsP ι)⁻¹)
        have hstoch :
            Integrable
              (fun ω =>
                (S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) /
                    (beta κ * spsP ι) +
                  ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                      (law.sample κ i ω),
                    xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P :=
          hquad_part.add (hlinear_int κ i)
        have hstoch_inner :
            Integrable
              (fun ω =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω);
                ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                  ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ)) law.P := by
          simpa [sgsGeneratedOracleQuery] using hstoch
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          hstoch_inner.const_mul
            ((spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) *
              psWeightProduct spsP i)⁻¹)
      change
        Integrable
          (fun ω =>
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                      ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ))) law.P
      exact
        hinner_sum.const_mul
          (gamma κ * psWeightProduct spsP (T κ) /
            (Gamma κ * (1 - psWeightProduct spsP (T κ))))
    change
      Integrable
        (fun ω =>
          Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
              bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
            Gamma N * outerSum ω) law.P
    exact houter_const.add (houter_sum.const_mul (Gamma N))
  have hgap_nonneg : 0 ≤ᵐ[law.P] gap := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hopt := hxStar.2 (sgsGeneratedOutput S states N.1 ω).2
    have hopt_le :
        objectiveOn S ⟨xStar, hxStar.1⟩ ≤
          objectiveOn S (sgsGeneratedOutput S states N.1 ω) := by
      simpa [objectiveOn] using hopt
    simpa [gap] using sub_nonneg.mpr hopt_le
  have hle_master : (∫ ω, gap ω ∂law.P) ≤ ∫ ω, masterRHS ω ∂law.P :=
    MeasureTheory.integral_mono_of_nonneg hgap_nonneg hmasterRHS_int
      (Filter.Eventually.of_forall hmaster_pointwise)
  have hmaster_expected_bound :
      (∫ ω, masterRHS ω ∂law.P) ≤
        theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩
          N beta gamma Gamma T := by
    haveI : IsProbabilityMeasure law.P := law.isProbability
    have hper :
        ∀ κ i,
          (∫ ω,
            ((S.mGrowth ^ 2 +
                  dualNorm S
                    (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                      (law.sample κ i ω)) ^ 2) /
                (beta κ * spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)) +
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω),
                xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) ∂law.P) ≤
            (S.mGrowth ^ 2 + S.sigmaSq) /
              (beta κ * spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)) := by
      intro κ i
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
      have hspsP_pos : 0 < spsP ι := by
        unfold spsP
        positivity
      have hscale_nonneg : 0 ≤ (beta κ * spsP ι)⁻¹ :=
        inv_nonneg.mpr (le_of_lt (mul_pos (hbeta κ) hspsP_pos))
      have hquad_part_int :
          Integrable
            (fun ω =>
              dualNorm S
                (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω)) ^ 2) law.P :=
        hdual_sq_int κ i
      have hlin_int :
          Integrable
            (fun ω =>
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω),
                xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P :=
        hlinear_int κ i
      simpa [ι] using
        theorem82_expected_single_noise_bracket_le
          (μ := law.P) (M := S.mGrowth ^ 2) (σ := S.sigmaSq)
          (betaP := beta κ * spsP ι)
          (quad := fun ω =>
            dualNorm S
              (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω)) ^ 2)
          (lin := fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ)
          hquad_part_int hlin_int (hquad κ i) (hlinear_zero κ i)
          hscale_nonneg
    -- Remaining finite expectation algebra: commute through the nested finite
    -- sums, rewrite the linear terms by `hlinear_zero_of_integrable`, and use
    -- `hquad` with nonnegative deterministic coefficients.
    have hinnerBound : ∀ κ,
        (∫ ω,
          (Finset.range (T κ)).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω)
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ)) ∂law.P) ≤
          (Finset.range (T κ)).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι))) := by
      intro κ
      refine theorem82_integral_finset_sum_scaled_le (μ := law.P)
        (s := Finset.range (T κ))
        (scale := fun i =>
          (spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) *
            psWeightProduct spsP i)⁻¹)
        (bound := fun i =>
          (S.mGrowth ^ 2 + S.sigmaSq) /
            (beta κ * spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)))
        (summand := fun i ω =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω)
          ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
            ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ)) ?_ ?_ ?_
      · intro i _hi
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
        have hquad_part :
            Integrable
              (fun ω =>
                (S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) /
                  (beta κ * spsP ι)) law.P := by
          have hsum :
              Integrable
                (fun ω =>
                  S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) law.P :=
            (integrable_const (c := S.mGrowth ^ 2)).add (hdual_sq_int κ i)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            hsum.const_mul ((beta κ * spsP ι)⁻¹)
        have hstoch : Integrable
            (fun ω =>
              (S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) /
                  (beta κ * spsP ι) +
                ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω),
                  xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P :=
          hquad_part.add (hlinear_int κ i)
        simpa [sgsGeneratedOracleQuery, ι] using hstoch
      · intro i _hi
        simpa [sgsGeneratedOracleQuery] using hper κ i
      · intro i _hi
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
        have hspsP_pos : 0 < spsP ι := by
          unfold spsP
          positivity
        have hprod_pos : 0 < psWeightProduct spsP i := by
          rw [psWeightProduct_spsP_eq i]
          positivity
        exact inv_nonneg.mpr (le_of_lt (mul_pos hspsP_pos hprod_pos))
    have hTpos : ∀ k : PositiveTime, 0 < T k :=
      positive_inner_budget_of_forwardMonotonicity_beforeMaster beta gamma Gamma T hmono
    have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
      outer_gamma_positive_of_weight_condition_and_forward_denom_beforeMaster
        beta gamma Gamma T hgamma hGamma hmono
    have houterBound :
        (∫ ω,
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω)
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                      ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ))) ∂law.P) ≤
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι)))) := by
      refine theorem82_integral_finset_sum_scaled_le (μ := law.P)
        (s := Finset.range N.1)
        (scale := fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
          gamma κ * psWeightProduct spsP (T κ) /
            (Gamma κ * (1 - psWeightProduct spsP (T κ))))
        (bound := fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
          (Finset.range (T κ)).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι)))
        )
        (summand := fun k ω =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
          (Finset.range (T κ)).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω)
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ))) ?_ ?_ ?_
      · intro k _hk
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        refine integrable_finset_sum (Finset.range (T κ)) ?_
        intro i _hi
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
        have hquad_part :
            Integrable
              (fun ω =>
                (S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) /
                  (beta κ * spsP ι)) law.P := by
          have hsum :
              Integrable
                (fun ω =>
                  S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) law.P :=
            (integrable_const (c := S.mGrowth ^ 2)).add (hdual_sq_int κ i)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            hsum.const_mul ((beta κ * spsP ι)⁻¹)
        have hstoch : Integrable
            (fun ω =>
              (S.mGrowth ^ 2 +
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) /
                  (beta κ * spsP ι) +
                ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω),
                  xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P :=
          hquad_part.add (hlinear_int κ i)
        have hstoch_inner :
            Integrable
              (fun ω =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω)
                ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                  ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ)) law.P := by
          simpa [sgsGeneratedOracleQuery, ι] using hstoch
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          hstoch_inner.const_mul
            ((spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) *
              psWeightProduct spsP i)⁻¹)
      · intro k _hk
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        simpa [κ] using hinnerBound κ
      · intro k _hk
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        have hPpos : 0 < psWeightProduct spsP (T κ) := by
          rw [psWeightProduct_spsP_eq (T κ)]
          positivity
        have hOneSubpos : 0 < 1 - psWeightProduct spsP (T κ) :=
          one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)
        exact div_nonneg
          (mul_nonneg (hgamma κ).1 (le_of_lt hPpos))
          (le_of_lt (mul_pos (hGamma_pos κ) hOneSubpos))
    let boundaryTerm : ℝ :=
      Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
        bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩
    let outerStoch : Ω → ℝ := fun ω =>
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω)
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                  ⟪δ, xStar - (inner κ i ω).u.1⟫_ℝ)))
    let deterministicOuter : ℝ :=
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι))))
    have houterBound_named :
        (∫ ω, outerStoch ω ∂law.P) ≤ deterministicOuter := by
      simpa [outerStoch, deterministicOuter] using houterBound
    have hmaster_repr :
        masterRHS = fun ω => boundaryTerm + Gamma N * outerStoch ω := by
      funext ω
      simp [masterRHS, boundaryTerm, outerStoch]
    have hscaled_outer_int :
        Integrable (fun ω => Gamma N * outerStoch ω) law.P := by
      have hconst : Integrable (fun _ : Ω => boundaryTerm) law.P :=
        integrable_const _
      have hsum_int :
          Integrable (fun ω => boundaryTerm + Gamma N * outerStoch ω) law.P := by
        simpa [hmaster_repr] using hmasterRHS_int
      have hdiff := hsum_int.sub hconst
      refine hdiff.congr ?_
      filter_upwards with ω
      simp only [Pi.sub_apply]
      ring
    have houter_int : Integrable outerStoch law.P := by
      have hscaled :
          Integrable (fun ω => (Gamma N)⁻¹ * (Gamma N * outerStoch ω)) law.P :=
        hscaled_outer_int.const_mul (Gamma N)⁻¹
      refine hscaled.congr ?_
      filter_upwards with ω
      have hGN : Gamma N ≠ 0 := ne_of_gt (hGamma_pos N)
      field_simp [hGN]
    have hmaster_split :
        (∫ ω, masterRHS ω ∂law.P) =
          boundaryTerm + Gamma N * ∫ ω, outerStoch ω ∂law.P := by
      calc
        (∫ ω, masterRHS ω ∂law.P)
            = ∫ ω, boundaryTerm + Gamma N * outerStoch ω ∂law.P := by
                rw [hmaster_repr]
        _ = (∫ _ω : Ω, boundaryTerm ∂law.P) +
              ∫ ω, Gamma N * outerStoch ω ∂law.P := by
                exact integral_add (integrable_const _) (houter_int.const_mul (Gamma N))
        _ = boundaryTerm + Gamma N * ∫ ω, outerStoch ω ∂law.P := by
                simp [integral_const_mul]
    have hdeterministic_normalize :
        boundaryTerm + Gamma N * deterministicOuter =
          theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩
            N beta gamma Gamma T := by
      have houter_normalize :
          deterministicOuter =
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              (Finset.range (T κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                (S.mGrowth ^ 2 + S.sigmaSq) * gamma κ * psWeightProduct spsP (T κ) /
                  (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i))) := by
        simp [deterministicOuter]
        refine Finset.sum_congr rfl ?_
        intro k _hk
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
        have hbeta_ne : beta κ ≠ 0 := ne_of_gt (hbeta κ)
        have hGamma_ne : Gamma κ ≠ 0 := ne_of_gt (hGamma_pos κ)
        have hOneSub_ne : 1 - psWeightProduct spsP (T κ) ≠ 0 :=
          ne_of_gt (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ))
        have hspsP_ne : spsP ι ≠ 0 := by
          unfold spsP
          positivity
        have hprod_ne : psWeightProduct spsP i ≠ 0 := by
          rw [psWeightProduct_spsP_eq i]
          positivity
        field_simp [κ, ι, hbeta_ne, hGamma_ne, hOneSub_ne, hspsP_ne,
          hprod_ne, pow_two]
      rw [houter_normalize]
      simp [boundaryTerm, theorem82ExpectedBound_formulaExtension,
        genericExpectedBound_formulaExtension]
    calc
      (∫ ω, masterRHS ω ∂law.P)
          = boundaryTerm + Gamma N * ∫ ω, outerStoch ω ∂law.P := hmaster_split
      _ ≤ boundaryTerm + Gamma N * deterministicOuter := by
            have hscaled :
                Gamma N * (∫ ω, outerStoch ω ∂law.P) ≤
                  Gamma N * deterministicOuter :=
              mul_le_mul_of_nonneg_left houterBound_named (le_of_lt (hGamma_pos N))
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hscaled boundaryTerm
      _ = theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩
            N beta gamma Gamma T := hdeterministic_normalize
  calc
    (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
        objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P)
        = ∫ ω, gap ω ∂law.P := by
          rfl
    _ ≤ ∫ ω, masterRHS ω ∂law.P := hle_master
    _ ≤ theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩
          N beta gamma Gamma T := hmaster_expected_bound

/-- Compiled route witness for the corrected gamma-range Theorem 8.2(a) branch.

The first projection confirms that the corrected branch is still a generated-run
formula-extension statement, not a selected-realization wrapper.  The second
projection routes the checked public bound through the corrected run-level
formula-extension helper. -/
theorem SGSGenericConvergence_Theorem8_2_expected_under_gammaRange_formulaExtension_consumer
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    IsGeneratedSGSProcess_formulaExtension S x0 beta gamma (innerBudgetNat T)
        law.sample states inner ∧
      expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
          xStar hxStar hrun hindep ≤
          theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
            beta gamma Gamma T
            (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
              (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
                law.sample states inner hrun)
              hlower hGamma hmono) := by
  have hrun_formula :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma (innerBudgetNat T)
        law.sample states inner := by
    exact ⟨hrun, trivial⟩
  refine ⟨hrun_formula, ?_⟩
  have hraw :=
    SGSGenericConvergence_Theorem8_2_expected_runFormulaExtension_under_gammaRange
      S law x0 xStar beta gamma Gamma (innerBudgetNat T) N states inner hrun_formula
      hindep hxStar
      (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
        law.sample states inner hrun)
      hgamma hlower hGamma hmono
  have hchecked :=
    theorem82ExpectedBound_checked_eq_formulaExtension S x0 ⟨xStar, hxStar.1⟩
      N beta gamma Gamma T
      (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
        (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
          law.sample states inner hrun)
        hlower hGamma hmono)
  rw [hchecked]
  simpa [expectedOutputGap, expectedOutputGapRaw, outputGapRandomVariable] using hraw

/-- Corrected canonical Theorem 8.2(a) expected-form source-boundary statement.

The concrete zero-dimensional counterexample above formally retires the old
unqualified declaration.  This canonical name is therefore the executable
generated-run boundary for Theorem 8.2(a): it keeps the same feasible-Bregman and
checked-quotient objects, and adds exactly the gamma upper-bound premise needed
by Eq. (8.1.28)'s convexity argument. -/
theorem SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep ≤
        theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          beta gamma Gamma T
          (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
            (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
              law.sample states inner hrun)
            hlower hGamma hmono) := by
  have hrun_formula :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma (innerBudgetNat T)
        law.sample states inner := by
    exact ⟨hrun, trivial⟩
  have hraw :=
    SGSGenericConvergence_Theorem8_2_expected_runFormulaExtension_under_gammaRange
      S law x0 xStar beta gamma Gamma (innerBudgetNat T) N states inner hrun_formula
      hindep hxStar
      (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
        law.sample states inner hrun)
      hgamma hlower hGamma hmono
  have hchecked :=
    theorem82ExpectedBound_checked_eq_formulaExtension S x0 ⟨xStar, hxStar.1⟩
      N beta gamma Gamma T
      (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
        (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
          law.sample states inner hrun)
        hlower hGamma hmono)
  rw [hchecked]
  simpa [expectedOutputGap, expectedOutputGapRaw, outputGapRandomVariable] using hraw

/-- Compiled consumer showing that Theorem 8.2(a)'s expected route has a local
well-definedness leaf, rather than relying on raw-integral fallback semantics.

The extra `hgap` premise is deliberately scoped to this audit helper.  It is
the exact technical fact FILL should derive from the pathwise bounded master
inequality or an output-objective integrability bridge before using integral
API; it is not added to the source-boundary theorem head above. -/
theorem SGSGenericConvergence_Theorem8_2_expected_wellDefined_consumer
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T))
    (hgap : Integrable (outputGapRandomVariable S states N xStar hxStar) law.P) :
    expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep =
        ∫ ω, outputGapRandomVariable S states N xStar hxStar ω ∂law.P ∧
      expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep ≤
        theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          beta gamma Gamma T
          (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
            (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
              law.sample states inner hrun)
            hlower hGamma hmono) := by
  refine ⟨?_, ?_⟩
  · exact expectedOutputGap_eq_raw_integral_of_integrable S law x0 beta gamma
      (innerBudgetNat T) states inner N xStar hxStar hrun hindep hgap
  · exact SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N states inner hgamma hrun hindep hxStar
      hlower hGamma hmono

/-- Corrected conditional Theorem 8.2(a) expected-form boundary.

This declaration is the executable correction target for the gamma source gap
recorded above: it keeps the generated-run, feasible-Bregman, checked-quotient
public boundary, but makes explicit the extra `γ_k ≤ 1` condition needed by
Eq. (8.1.28)'s convexity step.  It is therefore a corrected conditional variant,
not the unqualified source statement. -/
theorem SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman_under_gammaRange
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep ≤
        theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          beta gamma Gamma T
          (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
            (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
              law.sample states inner hrun)
            hlower hGamma hmono) := by
  exact SGSGenericConvergence_Theorem8_2_expected_sourceBoundary_feasibleBregman
    S law x0 xStar beta gamma Gamma T N states inner hgamma hrun hindep hxStar
    hlower hGamma hmono

/-- Strict-past adaptedness of the generated SGS oracle query.

This is the remaining Algorithm 8.2 recursion bridge needed before the
Lemma 4.1 martingale hypotheses for Eq. (8.1.70) can be instantiated.  The
strict-past sigma-algebra is generated by the flattened sample coordinates
whose lexicographic `(outer, inner)` index is earlier than the current query. -/
theorem sgsGeneratedOracleQuery_measurable_strictPastSampleSpace
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hadapted_run : sgsGeneratedQueriesStrictPastAdapted S law.sample inner)
    (hquery_mem :
      ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X) :
    ∀ k i,
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω, hquery_mem k i ω⟩ :
            FeasiblePoint S)) := by
  intro k i
  simpa [sgsGeneratedOracleQuery] using hadapted_run k i

/-- Conditional mean-zero leaf for the linear martingale increment in
Eq. (8.1.70), after generated-query strict-past adaptedness has been supplied.

This is deliberately smaller than the large-deviation conclusion: it should be
proved from strict-past adaptedness, current-sample freshness, Eq. (8.1.6), and
the scalar integrability of the displayed increment. -/
theorem linear_tail_condExp_zero_of_strictPast_adapted
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (k : PositiveTime) (i : ℕ)
    (hadapted :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            (Classical.choose hindep) k i ω⟩ : FeasiblePoint S)))
    (hscalar_int :
      Integrable
        (fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ)
        law.P) :
    let ζ : Ω → ℝ := fun ω =>
      ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω),
        uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
    law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0 := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  let queryFP : Ω → FeasiblePoint S :=
    fun ω =>
      ⟨sgsGeneratedOracleQuery S inner k i ω,
        (Classical.choose hindep) k i ω⟩
  let δ : Ω → E :=
    fun ω =>
      S.oracle (queryFP ω).1 (law.sample k i ω) -
        S.hSubgradient (queryFP ω).1
  have hpast_le :
      sgsStrictPastSampleSpace (Ω := Ω) law.sample k i ≤
        (by infer_instance : MeasurableSpace Ω) := by
    simpa using
      sgsStrictPastSampleSpace_le (Ω := Ω) law.sample law.sample_measurable k i
  have hquery_meas_ambient : Measurable queryFP := by
    exact hadapted.mono hpast_le le_rfl
  have hadapted_E :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω => (queryFP ω : E)) := by
    exact (measurable_subtype_coe.comp hadapted)
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hmean_int := generatedSFOUnbiased_integrable_obligation
    (S := S) law.P law.sample (sgsGeneratedOracleQuery S inner) hgenerated_mean k i
  have hδ_int : Integrable δ law.P := by
    simpa [δ, queryFP, oracleNoiseAt] using hmean_int.1.sub hmean_int.2
  have h_indep_set :
      ∀ s : Set Ω,
        @MeasurableSet Ω (sgsStrictPastSampleSpace (Ω := Ω) law.sample k i) s →
        IndepFun (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω, queryFP ω))
          (law.sample k i) law.P := by
    intro s hs
    have hindicator :
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
          (s.indicator (fun _ : Ω => (1 : ℝ))) :=
      measurable_const.indicator hs
    have hpair_past :
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
          (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω, queryFP ω)) :=
      hindicator.prod hadapted
    exact sgsStrictPast_adapted_indep_current_sample
      (S := S) law k i hpair_past
  have hfixed_zero :
      ∀ z : FeasiblePoint S,
        ∫ y, S.oracle z.1 y - S.hSubgradient z.1
          ∂(Measure.map (law.sample k i) law.P) = 0 := by
    intro z
    have hfiber_meas :
        Measurable (fun y : Sample => S.oracle z.1 y - S.hSubgradient z.1) := by
      have hpair : Measurable (fun y : Sample => (z, y)) :=
        (measurable_const : Measurable (fun _ : Sample => z)).prod measurable_id
      simpa [oracleNoiseAt, Function.uncurry] using
        law.oracle_residual_measurable.comp hpair
    have hmap :
        (∫ y, S.oracle z.1 y - S.hSubgradient z.1
            ∂(Measure.map (law.sample k i) law.P)) =
          ∫ ω, S.oracle z.1 (law.sample k i ω) - S.hSubgradient z.1 ∂law.P := by
      exact integral_map (law.sample_measurable k i).aemeasurable
        hfiber_meas.aestronglyMeasurable
    rw [hmap]
    exact coordinateSFOUnbiased_residual_integral_zero
      (S := S) law.P law.sample law.unbiased law.fixed_oracle_integrable k i z
  have hδ_cond :
      law.P[δ | sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0 := by
    exact condExp_oracle_noise_eq_zero_of_iid_adapted
      (μ := law.P) (m := sgsStrictPastSampleSpace (Ω := Ω) law.sample k i) hpast_le
      (G := fun z : FeasiblePoint S => fun y : Sample => S.oracle z.1 y)
      (g := fun z : FeasiblePoint S => S.hSubgradient z.1)
      (x := queryFP) (Y := law.sample k i)
      (by
        simpa [oracleNoiseAt, Function.uncurry] using law.oracle_residual_measurable)
      hadapted hquery_meas_ambient (law.sample_measurable k i)
      h_indep_set hδ_int hfixed_zero
  have hinner_int_adapted :
      Integrable (fun ω => ⟪δ ω, (queryFP ω : E) - uStar.1⟫_ℝ) law.P := by
    refine hscalar_int.neg.congr (Filter.Eventually.of_forall ?_)
    intro ω
    have hδω :
        δ ω =
          oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω) := by
      rfl
    have hdir :
        (queryFP ω : E) - uStar.1 =
          - (uStar.1 - sgsGeneratedOracleQuery S inner k i ω) := by
      simp [queryFP, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    symm
    change ⟪δ ω, (queryFP ω : E) - uStar.1⟫_ℝ =
      - ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω),
        uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
    rw [hδω, hdir, inner_neg_right]
  have hscalar :
      law.P[(fun ω => ⟪δ ω, (queryFP ω : E) - uStar.1⟫_ℝ) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0 := by
    exact condExp_inner_sub_const_eq_zero_of_condExp_eq_zero
      (P := law.P) (m := sgsStrictPastSampleSpace (Ω := Ω) law.sample k i)
      (δ := δ) (x := fun ω => (queryFP ω : E))
      (c := uStar.1) hadapted_E hδ_cond hδ_int hinner_int_adapted
  have htarget_eq :
      (fun ω =>
        ⟪δ ω, queryFP ω - uStar.1⟫_ℝ) =
        fun ω =>
          - ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ := by
    funext ω
    have hδω :
        δ ω =
          oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω) := by
      rfl
    have hdir :
        (queryFP ω : E) - uStar.1 =
          - (uStar.1 - sgsGeneratedOracleQuery S inner k i ω) := by
      simp [queryFP, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hδω, hdir, inner_neg_right]
  have hneg :
      law.P[(fun ω =>
        - ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0 := by
    simpa [htarget_eq] using hscalar
  have hcond_neg :
      law.P[(fun ω =>
        - ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P]
          fun ω =>
            - law.P[(fun ω =>
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                  (law.sample k i ω),
                uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ω := by
    simpa using
      (condExp_neg (μ := law.P)
        (m := sgsStrictPastSampleSpace (Ω := Ω) law.sample k i)
        (f := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ))
  filter_upwards [hneg, hcond_neg] with ω hzero hneg_eq
  have hz :
      - law.P[(fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ω = 0 := by
    exact hneg_eq ▸ hzero
  exact neg_eq_zero.mp hz

/-- Scalar Cauchy-Schwarz/Bregman-envelope domination behind Lan Eq. (8.1.70).

This is the pointwise part of the conditional light-tail proof: after the compact
envelope gives `‖u* - u_{k,i}‖² ≤ 2 \bar V(u*)`, the exponential-square
martingale increment is bounded by the oracle-noise exponential from
Assumption (8.1.57).  It is deliberately independent of conditional
expectation and of the final tail event. -/
theorem linear_tail_scalar_exp_le_oracle_exp_of_envelope
    (uStar q : FeasiblePoint S) (hcompact : IsCompact S.X) (δ : E)
    (hsigma_pos : 0 < S.sigmaSq)
    (henvelope_pos : 0 < bregmanEnvelope_formulaExtension S uStar hcompact)
    (hdisp :
      S.primalNorm (uStar.1 - q.1) ^ 2 ≤
        2 * bregmanEnvelope_formulaExtension S uStar hcompact) :
    Real.exp
        (⟪δ, uStar.1 - q.1⟫_ℝ ^ 2 /
          (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq)) ≤
      Real.exp (lightTailExponent S (dualNorm S δ ^ 2)) := by
  have habs := abs_inner_le_dualNorm_mul_primalNorm S δ (uStar.1 - q.1)
  have hdual_nonneg : 0 ≤ dualNorm S δ :=
    SOptLib.canonicalDualNorm_nonneg S.primalNorm δ
  have hprim_nonneg : 0 ≤ S.primalNorm (uStar.1 - q.1) :=
    apply_nonneg S.primalNorm _
  have hinner_sq_le :
      ⟪δ, uStar.1 - q.1⟫_ℝ ^ 2 ≤
        dualNorm S δ ^ 2 * S.primalNorm (uStar.1 - q.1) ^ 2 := by
    have hmul_nonneg : 0 ≤ dualNorm S δ * S.primalNorm (uStar.1 - q.1) :=
      mul_nonneg hdual_nonneg hprim_nonneg
    have hsq :
        |⟪δ, uStar.1 - q.1⟫_ℝ| ^ 2 ≤
          (dualNorm S δ * S.primalNorm (uStar.1 - q.1)) ^ 2 :=
      sq_le_sq' (by nlinarith [abs_nonneg ⟪δ, uStar.1 - q.1⟫_ℝ, hmul_nonneg])
        habs
    calc
      ⟪δ, uStar.1 - q.1⟫_ℝ ^ 2 =
          |⟪δ, uStar.1 - q.1⟫_ℝ| ^ 2 := by rw [sq_abs]
      _ ≤ (dualNorm S δ * S.primalNorm (uStar.1 - q.1)) ^ 2 := hsq
      _ = dualNorm S δ ^ 2 * S.primalNorm (uStar.1 - q.1) ^ 2 := by ring
  have hnum_le :
      ⟪δ, uStar.1 - q.1⟫_ℝ ^ 2 ≤
        dualNorm S δ ^ 2 * (2 * bregmanEnvelope_formulaExtension S uStar hcompact) := by
    have hdual_sq_nonneg : 0 ≤ dualNorm S δ ^ 2 := sq_nonneg _
    exact hinner_sq_le.trans
      (mul_le_mul_of_nonneg_left hdisp hdual_sq_nonneg)
  have hden_pos :
      0 < 2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq := by
    nlinarith [henvelope_pos, hsigma_pos]
  have hquot_le :
      ⟪δ, uStar.1 - q.1⟫_ℝ ^ 2 /
          (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq) ≤
        dualNorm S δ ^ 2 / S.sigmaSq := by
    have hmul_ne :
        2 * bregmanEnvelope_formulaExtension S uStar hcompact ≠ 0 := by
      nlinarith [henvelope_pos]
    field_simp [hden_pos.ne', hsigma_pos.ne', hmul_ne]
    nlinarith [hnum_le, hsigma_pos]
  exact Real.exp_le_exp.mpr (by simpa [lightTailExponent] using hquot_le)

/-- Compact feasible-envelope domination for the formula-extension Bregman
section.

This is the pointwise `\bar V(u*)` step used in Lan Eq. (8.1.70): the feasible
formula-extension envelope is the least upper bound of the feasible left
section, and compactness plus source-core continuity supplies the boundedness
side condition required by `le_csSup`. -/
theorem bregmanEnvelope_formulaExtension_domination
    (uStar q : FeasiblePoint S) (hcompact : IsCompact S.X) :
    bregmanFormulaOnX S q uStar ≤
      bregmanEnvelope_formulaExtension S uStar hcompact := by
  classical
  let f : FeasiblePoint S → ℝ := fun x => bregmanFormulaOnX S x uStar
  have hcompact_feasible : IsCompact (Set.univ : Set (FeasiblePoint S)) := by
    simpa using (isCompact_iff_isCompact_univ.mp hcompact)
  have hcont : Continuous f := by
    let toCore : FeasiblePoint S → ProxCorePoint S := fun x =>
      ⟨x.1, feasible_mem_proxCore_for_literal_bridge (S := S) x⟩
    have htoCore : Continuous toCore := by
      exact Continuous.subtype_mk
        (by
          simpa [toCore] using
            (continuous_subtype_val : Continuous (fun x : FeasiblePoint S => (x : E))))
        (fun x => feasible_mem_proxCore_for_literal_bridge (S := S) x)
    have hsource : Continuous (fun x : FeasiblePoint S => bregmanOn S (toCore x) uStar) :=
      (bregmanOn_left_section_continuous (S := S) uStar).comp htoCore
    have hfun : f = fun x : FeasiblePoint S => bregmanOn S (toCore x) uStar := by
      funext x
      exact bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore
        (S := S) x uStar (feasible_mem_proxCore_for_literal_bridge (S := S) x)
    simpa [hfun]
      using hsource
  rcases hcompact_feasible.exists_isMaxOn (⟨uStar, by simp⟩) hcont.continuousOn with
    ⟨xMax, _hxMax, hxMax⟩
  have hbdd :
      BddAbove (Set.range fun x : FeasiblePoint S => bregmanFormulaOnX S x uStar) := by
    refine ⟨bregmanFormulaOnX S xMax uStar, ?_⟩
    rintro y ⟨x, rfl⟩
    simpa [f] using (isMaxOn_iff.mp hxMax) x (by simp)
  simpa [bregmanEnvelope_formulaExtension, bregmanEnvelopeFormulaOnX] using
    (le_csSup hbdd (Set.mem_range_self q))

/-- The compact feasible Bregman envelope is nonnegative.

This follows by evaluating the envelope at the comparator itself and using the
prox-geometry lower bound for the zero displacement. -/
theorem bregmanEnvelope_formulaExtension_nonneg
    (uStar : FeasiblePoint S) (hcompact : IsCompact S.X) :
    0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact := by
  have hlower := bregmanFormulaOnX_lower_bound_from_prox_geometry S uStar uStar
  have hdom := bregmanEnvelope_formulaExtension_domination S uStar uStar hcompact
  have hzero :
      (0 : ℝ) ≤ bregmanFormulaOnX S uStar uStar := by
    simpa using hlower
  exact hzero.trans hdom

/-- Squared primal displacement controlled by the compact formula-extension
Bregman envelope.

This is the deterministic scalar envelope requested by the reconstruct audit for
`linear_tail_condExp_light_of_strictPast_adapted`. -/
theorem primal_displacement_sq_le_two_bregmanEnvelope_formulaExtension
    (uStar q : FeasiblePoint S) (hcompact : IsCompact S.X) :
    S.primalNorm (uStar.1 - q.1) ^ 2 ≤
      2 * bregmanEnvelope_formulaExtension S uStar hcompact := by
  have hlower := bregmanFormulaOnX_lower_bound_from_prox_geometry S q uStar
  have hdom := bregmanEnvelope_formulaExtension_domination S uStar q hcompact
  nlinarith [hlower, hdom]

/-- Nonnegative-envelope variant of the scalar light-tail domination.

The strict-envelope lemma above covers the ordinary case.  If the compact
envelope is zero, the displacement bound forces the scalar increment to vanish,
so the left exponential is `exp 0` and is still bounded by the oracle
exponential in the positive-variance branch. -/
theorem linear_tail_scalar_exp_le_oracle_exp_of_envelope_nonneg
    (uStar q : FeasiblePoint S) (hcompact : IsCompact S.X) (δ : E)
    (hsigma_pos : 0 < S.sigmaSq)
    (henvelope_nonneg : 0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact)
    (hdisp :
      S.primalNorm (uStar.1 - q.1) ^ 2 ≤
        2 * bregmanEnvelope_formulaExtension S uStar hcompact) :
    Real.exp
        (⟪δ, uStar.1 - q.1⟫_ℝ ^ 2 /
          (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq)) ≤
      Real.exp (lightTailExponent S (dualNorm S δ ^ 2)) := by
  by_cases henvelope_pos : 0 < bregmanEnvelope_formulaExtension S uStar hcompact
  · exact
      linear_tail_scalar_exp_le_oracle_exp_of_envelope
        (S := S) uStar q hcompact δ hsigma_pos henvelope_pos hdisp
  · have henvelope_zero :
        bregmanEnvelope_formulaExtension S uStar hcompact = 0 :=
      le_antisymm (le_of_not_gt henvelope_pos) henvelope_nonneg
    have hsq_zero :
        S.primalNorm (uStar.1 - q.1) ^ 2 = 0 := by
      have hle0 :
          S.primalNorm (uStar.1 - q.1) ^ 2 ≤ 0 := by
        simpa [henvelope_zero] using hdisp
      exact le_antisymm hle0 (sq_nonneg _)
    have hnorm_zero : S.primalNorm (uStar.1 - q.1) = 0 :=
      sq_eq_zero_iff.mp hsq_zero
    have hvec_zero : uStar.1 - q.1 = 0 :=
      (primalNorm_isSeparating S (uStar.1 - q.1)).mp hnorm_zero
    have hinner_zero : ⟪δ, uStar.1 - q.1⟫_ℝ = 0 := by
      rw [hvec_zero, inner_zero_right]
    have harg_nonneg : 0 ≤ lightTailExponent S (dualNorm S δ ^ 2) := by
      have hdual_sq_nonneg : 0 ≤ dualNorm S δ ^ 2 := sq_nonneg _
      simpa [lightTailExponent] using div_nonneg hdual_sq_nonneg (le_of_lt hsigma_pos)
    calc
      Real.exp
          (⟪δ, uStar.1 - q.1⟫_ℝ ^ 2 /
            (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq))
          = Real.exp 0 := by simp [hinner_zero]
      _ ≤ Real.exp (lightTailExponent S (dualNorm S δ ^ 2)) :=
          Real.exp_le_exp.mpr harg_nonneg

/-- Conditional-expectation upper bound from source-measurable set-integral bounds.

This is a Mathlib-level bridge used for the strict-past light-tail transfer:
to prove `E[f | past] <= C`, it suffices to bound the integral of `f` over
every past-measurable event by `C` times that event's probability. -/
theorem condExp_le_const_of_forall_setIntegral_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) {f : Ω → ℝ} {C : ℝ}
    (hf : Integrable f P)
    (hset :
      ∀ s : Set Ω, @MeasurableSet Ω m s →
        ∫ ω in s, f ω ∂P ≤ C * P.real s) :
    P[f | m] ≤ᵐ[P] fun _ => C := by
  classical
  have hcond_sm : StronglyMeasurable[m] (P[f | m]) :=
    stronglyMeasurable_condExp
  have hconst_sm : StronglyMeasurable[m] (fun _ : Ω => C) :=
    stronglyMeasurable_const
  refine ae_le_of_ae_le_trim (hm := hm) ?_
  refine ae_le_of_forall_setIntegral_le
    ((integrable_condExp (μ := P) (m := m) (f := f)).trim hm hcond_sm)
    ((integrable_const C).trim hm hconst_sm) ?_
  intro s hs hfin
  have hs_top : @MeasurableSet Ω mΩ s := hm _ hs
  have hcond_trim :
      ∫ ω in s, (P[f | m]) ω ∂P.trim hm =
        ∫ ω in s, (P[f | m]) ω ∂P := by
    exact (setIntegral_trim (μ := P) hm hcond_sm hs).symm
  have hconst_trim :
      ∫ ω in s, (fun _ : Ω => C) ω ∂P.trim hm =
        ∫ ω in s, (fun _ : Ω => C) ω ∂P := by
    exact (setIntegral_trim (μ := P) hm hconst_sm hs).symm
  rw [hcond_trim, hconst_trim]
  calc
    ∫ ω in s, (P[f | m]) ω ∂P = ∫ ω in s, f ω ∂P := by
      exact setIntegral_condExp hm hf hs
    _ ≤ C * P.real s := hset s hs
    _ = ∫ ω in s, (fun _ : Ω => C) ω ∂P := by
      rw [setIntegral_const]
      simp [smul_eq_mul, mul_comm]

/-- Weighted product-law integral transfer.

This is the positive-light-tail analogue of the existing zero-integral product
bridge: the past event is encoded as a nonnegative weight in the first
component, so the fixed-fiber bound integrates to the event probability rather
than losing the probability factor. -/
theorem integral_comp_weighted_le_of_indep_fixed_integral_bound
    {Ω W Sample : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Sample]
    {P : Measure Ω} {ν : Measure Sample} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → Sample → ℝ} {a : W → ℝ} {X : Ω → W} {Y : Ω → Sample} {C : ℝ}
    (hφ : Measurable (Function.uncurry φ))
    (ha : Measurable a)
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => a (X ω) * φ (X ω) (Y ω)) P)
    (ha_int : Integrable a (Measure.map X P))
    (ha_nonneg : 0 ≤ᵐ[Measure.map X P] a)
    (hfixed_bound : ∀ w, ∫ y, φ w y ∂ν ≤ C) :
    ∫ ω, a (X ω) * φ (X ω) (Y ω) ∂P ≤
      C * ∫ w, a w ∂Measure.map X P := by
  classical
  let ψ : W × Sample → ℝ := fun p => a p.1 * φ p.1 p.2
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have hψ_meas : Measurable ψ := by
    have hcoef : Measurable (fun p : W × Sample => a p.1) :=
      ha.comp measurable_fst
    simpa [ψ, Function.uncurry] using hcoef.mul hφ
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  have h_int_prod : Integrable ψ ((P.map X).prod ν) := by
    have h1 : Integrable ψ (P.map (fun ω => (X ω, Y ω))) :=
      (integrable_map_measure hψ_meas.aestronglyMeasurable h_joint_meas).mpr
        (by simpa [ψ] using h_int)
    rwa [h_prod_eq] at h1
  have h_rhs_int : Integrable (fun w => C * a w) (Measure.map X P) :=
    ha_int.const_mul C
  calc
    ∫ ω, a (X ω) * φ (X ω) (Y ω) ∂P =
        ∫ p : W × Sample, ψ p ∂P.map (fun ω => (X ω, Y ω)) := by
          exact (integral_map h_joint_meas hψ_meas.aestronglyMeasurable).symm
    _ = ∫ p : W × Sample, ψ p ∂(P.map X).prod ν := by rw [h_prod_eq]
    _ = ∫ w, ∫ y, ψ (w, y) ∂ν ∂Measure.map X P := by
      exact integral_prod _ h_int_prod
    _ ≤ ∫ w, C * a w ∂Measure.map X P := by
      refine integral_mono_ae h_int_prod.integral_prod_left h_rhs_int ?_
      filter_upwards [ha_nonneg] with w hw
      calc
        ∫ y, ψ (w, y) ∂ν = a w * ∫ y, φ w y ∂ν := by
          simpa [ψ] using integral_const_mul (a w) (fun y => φ w y) (μ := ν)
        _ ≤ a w * C := mul_le_mul_of_nonneg_left (hfixed_bound w) hw
        _ = C * a w := by ring
    _ = C * ∫ w, a w ∂Measure.map X P := by
      rw [integral_const_mul]

/-- Measurability of the positive-variance light-tail exponential kernel.

This is Lean regularity for Eq. (8.1.57), derived from the measurable oracle
residual kernel and the canonical dual norm.  It is private proof
infrastructure, not a new oracle assumption. -/
theorem oracle_light_tail_exp_measurable_of_residual_measurable
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (hres :
      Measurable (fun p : FeasiblePoint S × Sample =>
        oracleNoiseAt S p.1.1 p.2)) :
    Measurable (fun p : FeasiblePoint S × Sample =>
      Real.exp (lightTailExponent S (dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))) := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm (primalNorm_isSeparating S) with ⟨C, hC_nonneg, hC⟩
  have hdual_meas : Measurable (fun z : E => dualNorm S z) := by
    have hunit : ∀ x : E, S.primalNorm x ≤ 1 → ‖x‖ ≤ C := by
      intro x hx
      have hmul : C * S.primalNorm x ≤ C * 1 :=
        mul_le_mul_of_nonneg_left hx hC_nonneg
      exact (hC x).trans (by simpa using hmul)
    simpa [dualNorm] using
      (SOptLib.canonicalDualNorm_continuous
        (p := S.primalNorm) (C := C) hunit).measurable
  have hnoise :
      Measurable (fun p : FeasiblePoint S × Sample =>
        dualNorm S (oracleNoiseAt S p.1.1 p.2)) :=
    hdual_meas.comp hres
  have hsq :
      Measurable (fun p : FeasiblePoint S × Sample =>
        dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2) := by
    simpa [pow_two] using hnoise.mul hnoise
  have harg :
      Measurable (fun p : FeasiblePoint S × Sample =>
        lightTailExponent S (dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2)) := by
    simpa [lightTailExponent] using hsq.div_const S.sigmaSq
  exact Real.measurable_exp.comp harg

/-- Generated-query exponential integrability from coordinate Eq. (8.1.57) and
fresh-sample independence.

This is the integrability half of the positive light-tail conditionalization
route.  It proves the random-query moment is a real Bochner expectation by
transporting the fixed-fiber coordinate moment through the current sample law. -/
theorem generated_query_light_tail_exp_integrable_of_coordinate_positive
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (hsample_measurable : ∀ k i, Measurable (sample k i))
    (queryFP : Ω → FeasiblePoint S)
    (k : PositiveTime) (i : ℕ)
    (hquery_meas : Measurable queryFP)
    (hcurrent_indep : IndepFun queryFP (sample k i) P)
    (hpositive_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        Real.exp (lightTailExponent S (dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))))
    (hcoord_pos : coordinateSFOLightTailPositive S P sample) :
    Integrable
      (fun ω =>
        Real.exp (lightTailExponent S
          (dualNorm S (oracleNoiseAt S (queryFP ω).1 (sample k i ω)) ^ 2)))
      P := by
  classical
  let φ : FeasiblePoint S → Sample → ℝ := fun u xi =>
    Real.exp (lightTailExponent S (dualNorm S (oracleNoiseAt S u.1 xi) ^ 2))
  haveI : IsProbabilityMeasure (Measure.map (sample k i) P) :=
    Measure.isProbabilityMeasure_map (hsample_measurable k i).aemeasurable
  have hφ_meas : Measurable (Function.uncurry φ) := by
    simpa [φ, Function.uncurry] using hpositive_meas
  have hfixed_int :
      ∀ u : FeasiblePoint S,
        Integrable (fun xi => φ u xi) (Measure.map (sample k i) P) := by
    intro u
    have hφu_meas : Measurable (fun xi : Sample => φ u xi) := by
      have hpair : Measurable (fun xi : Sample => (u, xi)) :=
        (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
      simpa [φ, Function.uncurry] using hpositive_meas.comp hpair
    have hΩ :
        Integrable (fun ω => φ u (sample k i ω)) P := by
      simpa [φ, oracleNoiseDualNorm, oracleNoiseAt] using
        (hcoord_pos.2 k i u.1 u.2).1
    exact
      (integrable_map_measure hφu_meas.aestronglyMeasurable
        (hsample_measurable k i).aemeasurable).mpr hΩ
  have hfixed_bound :
      ∀ u : FeasiblePoint S,
        ∫ xi, φ u xi ∂Measure.map (sample k i) P ≤ Real.exp 1 := by
    intro u
    have hφu_meas : Measurable (fun xi : Sample => φ u xi) := by
      have hpair : Measurable (fun xi : Sample => (u, xi)) :=
        (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
      simpa [φ, Function.uncurry] using hpositive_meas.comp hpair
    have hmap :
        (∫ xi, φ u xi ∂Measure.map (sample k i) P) =
          ∫ ω, φ u (sample k i ω) ∂P := by
      exact integral_map (hsample_measurable k i).aemeasurable
        hφu_meas.aestronglyMeasurable
    rw [hmap]
    simpa [φ, oracleNoiseDualNorm, oracleNoiseAt] using
      (hcoord_pos.2 k i u.1 u.2).2
  simpa [φ] using
    integrable_comp_of_indep_fixed_integral_bound
      (P := P) (ν := Measure.map (sample k i) P)
      (φ := φ) (X := queryFP) (Y := sample k i) (C := Real.exp 1)
      hφ_meas hquery_meas (hsample_measurable k i) hcurrent_indep rfl
      (fun _ _ => Real.exp_nonneg _)
      (le_of_lt (Real.exp_pos 1)) hfixed_int hfixed_bound

/-- Positive-variance conditionalization leaf for the oracle exponential moment.

This is the exact remaining product-law/conditional-expectation bridge requested
by the reconstruct audit.  Its hypotheses are strictly smaller than
`linear_tail_condExp_light_of_strictPast_adapted`: a past-measurable feasible
query, freshness of the current sample, coordinate Eq. (8.1.57), and the
measurability/integrability needed to form the conditional expectation. -/
theorem coordinate_light_tail_condExp_bound_of_strictPast_indep
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (queryFP : Ω → FeasiblePoint S)
    (k : PositiveTime) (i : ℕ)
    (hpast_le :
      sgsStrictPastSampleSpace (Ω := Ω) law.sample k i ≤
        (by infer_instance : MeasurableSpace Ω))
    (hquery_meas : Measurable queryFP)
    (hcurrent_indep :
      ∀ s : Set Ω,
        @MeasurableSet Ω (sgsStrictPastSampleSpace (Ω := Ω) law.sample k i) s →
        IndepFun (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω, queryFP ω))
          (law.sample k i) law.P)
    (hpositive_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        Real.exp (lightTailExponent S (dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))))
    (hpositive_int :
      Integrable
        (fun ω =>
          Real.exp (lightTailExponent S
            (dualNorm S (oracleNoiseAt S (queryFP ω).1 (law.sample k i ω)) ^ 2)))
        law.P)
    (hcoord_pos : coordinateSFOLightTailPositive S law.P law.sample) :
    law.P[(fun ω =>
          Real.exp (lightTailExponent S
            (dualNorm S (oracleNoiseAt S (queryFP ω).1 (law.sample k i ω)) ^ 2))) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
      fun _ => Real.exp 1 := by
  classical
  let f : Ω → ℝ := fun ω =>
    Real.exp (lightTailExponent S
      (dualNorm S (oracleNoiseAt S (queryFP ω).1 (law.sample k i ω)) ^ 2))
  refine condExp_le_const_of_forall_setIntegral_le (P := law.P)
    (sgsStrictPastSampleSpace (Ω := Ω) law.sample k i) hpast_le
    (f := f) (C := Real.exp 1) hpositive_int ?_
  intro s hs
  let a : Ω → ℝ := s.indicator (fun _ : Ω => (1 : ℝ))
  let X : Ω → ℝ × FeasiblePoint S := fun ω => (a ω, queryFP ω)
  let φ : (ℝ × FeasiblePoint S) → Sample → ℝ := fun z y =>
    Real.exp (lightTailExponent S
      (dualNorm S (oracleNoiseAt S z.2.1 y) ^ 2))
  have hs_top : MeasurableSet s := hpast_le _ hs
  have ha_meas : Measurable a := by
    have hconst : Measurable (fun _ : Ω => (1 : ℝ)) := measurable_const
    simpa [a] using hconst.indicator hs_top
  have hX_meas : Measurable X := ha_meas.prodMk hquery_meas
  have hφ_meas : Measurable (Function.uncurry φ) := by
    have hpair :
        Measurable (fun p : (ℝ × FeasiblePoint S) × Sample => (p.1.2, p.2)) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    simpa [φ, Function.uncurry] using hpositive_meas.comp hpair
  haveI : IsProbabilityMeasure (Measure.map (law.sample k i) law.P) :=
    Measure.isProbabilityMeasure_map (law.sample_measurable k i).aemeasurable
  have hfixed_bound :
      ∀ z : ℝ × FeasiblePoint S, ∫ y, φ z y ∂Measure.map (law.sample k i) law.P ≤
        Real.exp 1 := by
    intro z
    have hfiber_meas : Measurable (fun y : Sample => φ z y) := by
      have hpair : Measurable (fun y : Sample => (z.2, y)) :=
        (measurable_const : Measurable (fun _ : Sample => z.2)).prod measurable_id
      simpa [φ, Function.uncurry] using hpositive_meas.comp hpair
    have hmap :
        (∫ y, φ z y ∂Measure.map (law.sample k i) law.P) =
          ∫ ω, φ z (law.sample k i ω) ∂law.P := by
      exact integral_map (law.sample_measurable k i).aemeasurable
        hfiber_meas.aestronglyMeasurable
    rw [hmap]
    simpa [φ, oracleNoiseDualNorm, oracleNoiseAt] using
      (hcoord_pos.2 k i z.2.1 z.2.2).2
  have hweighted_eq :
      (fun ω => a ω * φ (X ω) (law.sample k i ω)) =
        s.indicator f := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [a, X, φ, f, hω]
  have hweighted_int :
      Integrable (fun ω => a ω * φ (X ω) (law.sample k i ω)) law.P := by
    simpa [hweighted_eq] using hpositive_int.indicator hs_top
  have ha_nonneg_map : 0 ≤ᵐ[Measure.map X law.P] fun z : ℝ × FeasiblePoint S => z.1 := by
    change ∀ᵐ z ∂Measure.map X law.P, z ∈
      ({z : ℝ × FeasiblePoint S | 0 ≤ z.1} : Set (ℝ × FeasiblePoint S))
    exact (ae_map_iff hX_meas.aemeasurable
      (measurableSet_Ici.preimage
        (measurable_fst : Measurable (fun z : ℝ × FeasiblePoint S => z.1)))).mpr
      (Filter.Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ s <;> simp [X, a, hω]
      )
  have ha_int_map :
      Integrable (fun z : ℝ × FeasiblePoint S => z.1) (Measure.map X law.P) := by
    have hcomp : Integrable (fun ω => (X ω).1) law.P := by
      simpa [X, a] using (integrable_const (1 : ℝ)).indicator hs_top
    exact (integrable_map_measure (measurable_fst : Measurable (fun z : ℝ × FeasiblePoint S => z.1)).aestronglyMeasurable
      hX_meas.aemeasurable).mpr hcomp
  have hmain :
      ∫ ω, a ω * φ (X ω) (law.sample k i ω) ∂law.P ≤
        Real.exp 1 *
          ∫ z, z.1 ∂Measure.map X law.P := by
    exact integral_comp_weighted_le_of_indep_fixed_integral_bound
      (P := law.P) (ν := Measure.map (law.sample k i) law.P)
      (φ := φ) (a := fun z : ℝ × FeasiblePoint S => z.1)
      (X := X) (Y := law.sample k i) (C := Real.exp 1)
      hφ_meas (measurable_fst : Measurable (fun z : ℝ × FeasiblePoint S => z.1))
      hX_meas (law.sample_measurable k i) (by simpa [X, a] using hcurrent_indep s hs)
      rfl (by simpa [X] using hweighted_int) ha_int_map ha_nonneg_map hfixed_bound
  have hmap_weight :
      (∫ z, z.1 ∂Measure.map X law.P) = ∫ ω, a ω ∂law.P := by
    exact integral_map hX_meas.aemeasurable
      (measurable_fst : Measurable (fun z : ℝ × FeasiblePoint S => z.1)).aestronglyMeasurable
  rw [← MeasureTheory.integral_indicator (μ := law.P) (f := f) hs_top]
  calc
    ∫ ω, s.indicator f ω ∂law.P =
        ∫ ω, a ω * φ (X ω) (law.sample k i ω) ∂law.P := by
          rw [hweighted_eq]
    _ ≤ Real.exp 1 * ∫ z, z.1 ∂Measure.map X law.P := hmain
    _ = Real.exp 1 * ∫ ω, a ω ∂law.P := by rw [hmap_weight]
    _ = Real.exp 1 * law.P.real s := by
      rw [integral_indicator hs_top, setIntegral_const]
      simp [a, smul_eq_mul]

/-- Deterministic `σ² = 0` conditional light-tail leaf.

The deterministic branch of Assumption (8.1.57) says the current oracle noise is
zero a.e.; then the martingale scalar exponent is `exp 0`, hence bounded by
`exp 1`. -/
theorem linear_tail_condExp_light_deterministic_of_zero_noise
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hdet : coordinateSFOLightTailDeterministic S law.P law.sample)
    (hcompact : IsCompact S.X)
    (k : PositiveTime) (i : ℕ)
    (hadapted :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            (Classical.choose hindep) k i ω⟩ : FeasiblePoint S))) :
    let ζ : Ω → ℝ := fun ω =>
      ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω),
        uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
      law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
            sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
        fun _ => Real.exp 1 := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  let queryFP : Ω → FeasiblePoint S :=
    fun ω =>
      ⟨sgsGeneratedOracleQuery S inner k i ω,
        (Classical.choose hindep) k i ω⟩
  have hpast_le :
      sgsStrictPastSampleSpace (Ω := Ω) law.sample k i ≤
        (by infer_instance : MeasurableSpace Ω) := by
    simpa using
      sgsStrictPastSampleSpace_le (Ω := Ω) law.sample law.sample_measurable k i
  have hquery_meas : Measurable queryFP := hadapted.mono hpast_le le_rfl
  have hcurrent_indep : IndepFun queryFP (law.sample k i) law.P :=
    sgsStrictPast_adapted_indep_current_sample (S := S) law k i hadapted
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm (primalNorm_isSeparating S) with ⟨C, hC_nonneg, hC⟩
  have hdual_meas : Measurable (fun z : E => dualNorm S z) := by
    have hunit : ∀ x : E, S.primalNorm x ≤ 1 → ‖x‖ ≤ C := by
      intro x hx
      have hmul : C * S.primalNorm x ≤ C * 1 :=
        mul_le_mul_of_nonneg_left hx hC_nonneg
      exact (hC x).trans (by simpa using hmul)
    simpa [dualNorm] using
      (SOptLib.canonicalDualNorm_continuous
        (p := S.primalNorm) (C := C) hunit).measurable
  let R : FeasiblePoint S → Sample → Prop :=
    fun u xi => dualNorm S (oracleNoiseAt S u.1 xi) = 0
  have hR : MeasurableSet {p : FeasiblePoint S × Sample | R p.1 p.2} := by
    have hnoise :
        Measurable (fun p : FeasiblePoint S × Sample =>
          dualNorm S (oracleNoiseAt S p.1.1 p.2)) :=
      hdual_meas.comp law.oracle_residual_measurable
    simpa [R] using zero_noise_event_measurable_of_noise_norm_measurable
      (S := S) hnoise
  haveI : IsProbabilityMeasure (Measure.map (law.sample k i) law.P) :=
    Measure.isProbabilityMeasure_map (law.sample_measurable k i).aemeasurable
  have hfixed_ae :
      ∀ u : FeasiblePoint S,
        ∀ᵐ xi ∂Measure.map (law.sample k i) law.P, R u xi := by
    intro u
    have hRu : MeasurableSet {xi : Sample | R u xi} := by
      have hpair : Measurable (fun xi : Sample => (u, xi)) :=
        (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
      simpa [R] using hR.preimage hpair
    exact (ae_map_iff (law.sample_measurable k i).aemeasurable hRu).mpr
      (by simpa [R, oracleNoiseDualNorm, oracleNoiseAt] using hdet.2 k i u.1 u.2)
  have hzero_dual :
      ∀ᵐ ω ∂law.P,
        dualNorm S
          (oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω)) = 0 := by
    simpa [R, queryFP] using
      ae_comp_of_indep_fixed_ae
        (P := law.P) (ν := Measure.map (law.sample k i) law.P) (R := R)
        (X := queryFP) (Y := law.sample k i) hR hquery_meas
        (law.sample_measurable k i) hcurrent_indep rfl hfixed_ae
  have hζ_zero :
      (fun ω =>
        ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω),
          uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) =ᵐ[law.P]
        fun _ => 0 := by
    filter_upwards [hzero_dual] with ω hzero
    have habs :=
      abs_inner_le_dualNorm_mul_primalNorm S
        (oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω))
        (uStar.1 - sgsGeneratedOracleQuery S inner k i ω)
    have hle0 :
        |⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω),
          uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ| ≤ 0 := by
      simpa [hzero] using habs
    have habs0 :
        |⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω),
          uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ| = 0 :=
      le_antisymm hle0 (abs_nonneg _)
    exact abs_eq_zero.mp habs0
  have hf_eq_one :
      (fun ω =>
        Real.exp
          ((⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                (law.sample k i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) ^ 2 /
            (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq))) =ᵐ[law.P]
        fun _ => (1 : ℝ) := by
    filter_upwards [hζ_zero] with ω hζ
    simp [hζ]
  have hcond_eq :
      law.P[(fun ω =>
        Real.exp
          ((⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                (law.sample k i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) ^ 2 /
            (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq))) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P]
        law.P[(fun _ : Ω => (1 : ℝ)) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] :=
    MeasureTheory.condExp_congr_ae (m := sgsStrictPastSampleSpace (Ω := Ω) law.sample k i)
      hf_eq_one
  have hconst :
      law.P[(fun _ : Ω => (1 : ℝ)) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =
        fun _ : Ω => (1 : ℝ) :=
    MeasureTheory.condExp_const
      (μ := law.P) (m := sgsStrictPastSampleSpace (Ω := Ω) law.sample k i)
      hpast_le (1 : ℝ)
  refine ⟨?_, ?_⟩
  · exact (integrable_const (1 : ℝ)).congr hf_eq_one.symm
  · filter_upwards [hcond_eq] with ω hω
    rw [hω, hconst]
    simpa using (Real.exp_le_exp.mpr zero_le_one : Real.exp 0 ≤ Real.exp 1)

/-- Conditional exponential-square leaf for the linear martingale increment in
Eq. (8.1.70), after generated-query strict-past adaptedness has been supplied.

This is the light-tail half of the Lemma 4.1 interface.  It is not a wrapper
around the final tail event; it only states the conditional moment bound for one
flattened `(k,i)` increment. -/
theorem linear_tail_condExp_light_of_strictPast_adapted
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hcoordinate_light : coordinateSFOLightTail S law.P law.sample)
    (hcompact : IsCompact S.X)
    (k : PositiveTime) (i : ℕ)
    (hadapted :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            (Classical.choose hindep) k i ω⟩ : FeasiblePoint S))) :
    let ζ : Ω → ℝ := fun ω =>
      ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω),
        uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
      law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
            sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
        fun _ => Real.exp 1 := by
  classical
  let queryFP : Ω → FeasiblePoint S :=
    fun ω =>
      ⟨sgsGeneratedOracleQuery S inner k i ω,
        (Classical.choose hindep) k i ω⟩
  have hpast_le :
      sgsStrictPastSampleSpace (Ω := Ω) law.sample k i ≤
        (by infer_instance : MeasurableSpace Ω) := by
    simpa using
      sgsStrictPastSampleSpace_le (Ω := Ω) law.sample law.sample_measurable k i
  have hquery_meas : Measurable queryFP := hadapted.mono hpast_le le_rfl
  have hcurrent_indep : IndepFun queryFP (law.sample k i) law.P :=
    sgsStrictPast_adapted_indep_current_sample (S := S) law k i hadapted
  have hcurrent_indep_set :
      ∀ s : Set Ω,
        @MeasurableSet Ω (sgsStrictPastSampleSpace (Ω := Ω) law.sample k i) s →
        IndepFun (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω, queryFP ω))
          (law.sample k i) law.P := by
    intro s hs
    have hindicator :
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
          (s.indicator (fun _ : Ω => (1 : ℝ))) :=
      measurable_const.indicator hs
    have hpair_past :
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
          (fun ω => (s.indicator (fun _ : Ω => (1 : ℝ)) ω, queryFP ω)) :=
      hindicator.prod hadapted
    exact sgsStrictPast_adapted_indep_current_sample
      (S := S) law k i hpair_past
  rcases hcoordinate_light with hcoord_pos | hcoord_det
  · have hpositive_meas :
        Measurable (fun p : FeasiblePoint S × Sample =>
          Real.exp (lightTailExponent S
            (dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))) :=
      oracle_light_tail_exp_measurable_of_residual_measurable
        (S := S) law.oracle_residual_measurable
    have hpositive_int :
        Integrable
          (fun ω =>
            Real.exp (lightTailExponent S
              (dualNorm S
                (oracleNoiseAt S (queryFP ω).1 (law.sample k i ω)) ^ 2)))
          law.P :=
      generated_query_light_tail_exp_integrable_of_coordinate_positive
        (S := S) law.P law.sample law.sample_measurable queryFP k i
        hquery_meas hcurrent_indep hpositive_meas hcoord_pos
    have hsource_cond :
        law.P[(fun ω =>
              Real.exp (lightTailExponent S
                (dualNorm S (oracleNoiseAt S (queryFP ω).1 (law.sample k i ω)) ^ 2))) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
          fun _ => Real.exp 1 := by
      simpa [queryFP] using
        coordinate_light_tail_condExp_bound_of_strictPast_indep
          (S := S) law queryFP k i hpast_le hquery_meas hcurrent_indep_set
          hpositive_meas hpositive_int
          hcoord_pos
    have hscalar_le :
        (fun ω =>
          Real.exp
            ((⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                  (law.sample k i ω),
                uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) ^ 2 /
              (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq))) ≤ᵐ[law.P]
          fun ω =>
            Real.exp (lightTailExponent S
              (dualNorm S
                (oracleNoiseAt S (queryFP ω).1 (law.sample k i ω)) ^ 2)) := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have henv_nonneg :
          0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact :=
        bregmanEnvelope_formulaExtension_nonneg S uStar hcompact
      have hdisp :
          S.primalNorm (uStar.1 - (queryFP ω).1) ^ 2 ≤
            2 * bregmanEnvelope_formulaExtension S uStar hcompact :=
        primal_displacement_sq_le_two_bregmanEnvelope_formulaExtension
          S uStar (queryFP ω) hcompact
      simpa [queryFP] using
        linear_tail_scalar_exp_le_oracle_exp_of_envelope_nonneg
          (S := S) uStar (queryFP ω) hcompact
          (oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω))
          hcoord_pos.1 henv_nonneg hdisp
    have hleft_int :
        Integrable
          (fun ω =>
            Real.exp
              ((⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                  (law.sample k i ω),
                  uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) ^ 2 /
                (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq)))
          law.P := by
      have hpair_meas :
          Measurable (fun ω => (queryFP ω, law.sample k i ω)) :=
        hquery_meas.prod (law.sample_measurable k i)
      have hinner_meas :
          Measurable (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                (law.sample k i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) :=
        by
          have htarget :=
            oracle_residual_target_inner_measurable_of_residual_measurable
              (S := S) (x := uStar) law.oracle_residual_measurable
          simpa [queryFP, real_inner_comm] using htarget.comp hpair_meas
      have hleft_meas :
          Measurable
            (fun ω =>
              Real.exp
                ((⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                      (law.sample k i ω),
                    uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) ^ 2 /
                  (2 * bregmanEnvelope_formulaExtension S uStar hcompact *
                    S.sigmaSq))) := by
        have hsq :
            Measurable
              (fun ω =>
                (⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                    (law.sample k i ω),
                  uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ) ^ 2) := by
          simpa [pow_two] using hinner_meas.mul hinner_meas
        exact Real.measurable_exp.comp
          (hsq.div_const
            (2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq))
      refine Integrable.mono hpositive_int hleft_meas.aestronglyMeasurable ?_
      filter_upwards [hscalar_le] with ω hle
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (Real.exp_nonneg _)]
      exact hle
    have hright_int :
        Integrable
          (fun ω =>
            Real.exp (lightTailExponent S
              (dualNorm S
                (oracleNoiseAt S (queryFP ω).1 (law.sample k i ω)) ^ 2)))
          law.P := by
      exact hpositive_int
    have hcond_mono :=
      MeasureTheory.condExp_mono
        (m := sgsStrictPastSampleSpace (Ω := Ω) law.sample k i)
        hleft_int hright_int hscalar_le
    exact ⟨hleft_int, by simpa [queryFP] using hcond_mono.trans hsource_cond⟩
  · simpa [queryFP] using
      linear_tail_condExp_light_deterministic_of_zero_noise
        (S := S) law uStar inner hindep hcoord_det hcompact k i hadapted

/-- Exact-head proof attempt artifact for the conditional light-tail leaf.

The proof route is source Eq. (8.1.57) plus strict-past freshness: dominate
`exp(ζ^2 / (2 * \bar V(u*) * σ^2))` by the coordinate oracle-noise exponential
moment using the Bregman-envelope displacement bound, then transfer the
fixed-fiber integral bound through the current-sample independence and identify
the result as a conditional expectation bound on strict-past events via
`ae_eq_condExp_of_forall_setIntegral_eq`/`condExp_mono`. -/
theorem _voucher_attempt_linear_tail_condExp_light_of_strictPast_adapted_11
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hcoordinate_light : coordinateSFOLightTail S law.P law.sample)
    (hcompact : IsCompact S.X)
    (k : PositiveTime) (i : ℕ)
    (hadapted :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            (Classical.choose hindep) k i ω⟩ : FeasiblePoint S))) :
    let ζ : Ω → ℝ := fun ω =>
      ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω),
        uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
      fun _ => Real.exp 1 := by
  classical
  simpa using
    (linear_tail_condExp_light_of_strictPast_adapted
      (S := S) law uStar inner hindep hcoordinate_light hcompact k i hadapted).2

/-- Iteration-32 exact-head attempt artifact for
`linear_tail_condExp_light_of_strictPast_adapted`.

This keeps the current selected-route context visible to the compiler: strict
past inclusion, adapted query measurability, and current-sample freshness are
available before the remaining conditional light-tail transfer.  The remaining
proof leaf is the genuine Eq. (8.1.57) conditionalization plus compact
Bregman-envelope domination, not the final Eq. (8.1.70) tail event. -/
theorem _voucher_attempt_linear_tail_condExp_light_of_strictPast_adapted_32
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hcoordinate_light : coordinateSFOLightTail S law.P law.sample)
    (hcompact : IsCompact S.X)
    (k : PositiveTime) (i : ℕ)
    (hadapted :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            (Classical.choose hindep) k i ω⟩ : FeasiblePoint S))) :
    let ζ : Ω → ℝ := fun ω =>
      ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω),
        uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
          sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
      fun _ => Real.exp 1 := by
  classical
  simpa using
    (linear_tail_condExp_light_of_strictPast_adapted
      (S := S) law uStar inner hindep hcoordinate_light hcompact k i hadapted).2

/-- Conditional martingale hypotheses for the linear noise increments in
Eq. (8.1.70).

The statement packages the real source obligation produced by Lemma 4.1 after
the SGS sample family is flattened: each query is strict-past adapted, each
query is therefore independent of the current fresh sample, and the scalar
linear increment has zero conditional mean and conditional exponential-square
control given the strict past.  The subsequent finite large-deviation leaf
should apply Lemma 4.1 to this bridge; this theorem deliberately does not
assume the final probability bound. -/
theorem linear_tail_mds_light_tail_bridge
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
    (uStar : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hadapted_run : sgsGeneratedQueriesStrictPastAdapted S law.sample inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hcoordinate_light : coordinateSFOLightTail S law.P law.sample)
    (hlinear_int :
      ∀ k i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                (law.sample k i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ)
          law.P)
    (hcompact : IsCompact S.X) :
    ∀ k i,
      let ζ : Ω → ℝ := fun ω =>
        ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω),
          uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
      let lightScale : ℝ :=
        2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
          (fun ω =>
            (⟨sgsGeneratedOracleQuery S inner k i ω,
              (Classical.choose hindep) k i ω⟩ : FeasiblePoint S)) ∧
        IndepFun
          (fun ω =>
            (⟨sgsGeneratedOracleQuery S inner k i ω,
              (Classical.choose hindep) k i ω⟩ : FeasiblePoint S))
          (law.sample k i) law.P ∧
        (law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0) ∧
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
          (law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
                sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
              fun _ => Real.exp 1) := by
  classical
  intro k i
  let hquery_mem : ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X :=
    Classical.choose hindep
  have hadapted :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            hquery_mem k i ω⟩ : FeasiblePoint S)) :=
    sgsGeneratedOracleQuery_measurable_strictPastSampleSpace
      (S := S) (law := law) (x0 := x0) (beta := beta) (gamma := gamma)
      (T := T) (states := states) (inner := inner) hrun hadapted_run hquery_mem k i
  have hcurrent_indep :
      IndepFun
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            hquery_mem k i ω⟩ : FeasiblePoint S))
        (law.sample k i) law.P :=
    sgsStrictPast_adapted_indep_current_sample
      (S := S) law k i hadapted
  have hcond_zero :
      (let ζ : Ω → ℝ := fun ω =>
        ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω),
          uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
      law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0) :=
    linear_tail_condExp_zero_of_strictPast_adapted
      (S := S) law uStar inner hindep k i hadapted (hlinear_int k i)
  have hcond_light :
      (let ζ : Ω → ℝ := fun ω =>
        ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
            (law.sample k i ω),
          uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
      let lightScale : ℝ :=
        2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
      Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
            fun _ => Real.exp 1) :=
    linear_tail_condExp_light_of_strictPast_adapted
      (S := S) law uStar inner hindep hcoordinate_light hcompact k i hadapted
  exact ⟨hadapted, hcurrent_indep, hcond_zero, hcond_light.1, hcond_light.2⟩

/-- Source-disclosed Lemma 4.1 interface for the generated SGS linear noise.

This is the smallest high-probability boundary needed by Lan Eq. (8.1.70):
for every flattened `(k,i)` coordinate, the scalar linear noise increment is
integrable, has conditional mean zero given the strict past, and satisfies the
conditional exponential-square moment used by Lemma 4.1.  It deliberately stops
before the finite probability tail, so it is not a wrapper around the final
Theorem 8.2(b) event.  A fully causal selected-process realization should prove
this predicate from `sample_iIndep`, strict-past generated-query adaptedness,
Eq. (8.1.6), Eq. (8.1.57), and the compact Bregman-envelope bound. -/
def SGSLinearMDSLightTailInterface [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hcompact : IsCompact S.X) : Prop :=
  ∀ k i,
    let ζ : Ω → ℝ := fun ω =>
      ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
          (law.sample k i ω),
        uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω => sgsGeneratedOracleQuery S inner k i ω) ∧
      Integrable ζ law.P ∧
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0 ∧
          Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
            law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
                  sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
              fun _ => Real.exp 1

/-- The detailed strict-past bridge implies the source-disclosed Lemma 4.1
interface.  This adapter proves the new interface from strictly smaller
source-derived facts; it does not assume the finite probability tail. -/
theorem SGSLinearMDSLightTailInterface.of_strictPast_bridge
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
    (uStar : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hadapted_run : sgsGeneratedQueriesStrictPastAdapted S law.sample inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hcoordinate_light : coordinateSFOLightTail S law.P law.sample)
    (hlinear_int :
      ∀ k i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                (law.sample k i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ)
          law.P)
    (hcompact : IsCompact S.X) :
    SGSLinearMDSLightTailInterface S law uStar inner hcompact := by
  classical
  intro k i
  have hbridge :=
    linear_tail_mds_light_tail_bridge
      (S := S) (law := law) (x0 := x0) (uStar := uStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := T)
      (states := states) (inner := inner) hrun hadapted_run hindep
      hcoordinate_light hlinear_int hcompact k i
  have hquery_adapted :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
        (fun ω => sgsGeneratedOracleQuery S inner k i ω) := by
    simpa using measurable_subtype_coe.comp hbridge.1
  exact ⟨hquery_adapted, hlinear_int k i, hbridge.2.2.1,
    hbridge.2.2.2.1, hbridge.2.2.2.2⟩

/-- Selected-realization constructor for the Lemma 4.1 linear-noise interface.

This is the source-facing route requested by the reconstruct audit: for the
canonical selected SGS/SPS recursion, strict-past adaptedness is supplied by
`sgsSelectedGeneratedQueriesStrictPastAdapted` rather than by an arbitrary
relation-form generated-run obligation.  The remaining conditional light-tail
leaf is still the genuine one-coordinate Eq. (8.1.57) transfer, not a final
probability-tail wrapper. -/
theorem SGSLinearMDSLightTailInterface.of_selected_run
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
    (uStar : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hcoordinate_light : coordinateSFOLightTail S law.P law.sample)
    (hlinear_int :
      ∀ k i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S
                (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω)
                (law.sample k i ω),
              uStar.1 -
                sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω⟫_ℝ)
          law.P)
    (hcompact : IsCompact S.X) :
    SGSLinearMDSLightTailInterface S law uStar
      (sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma T law.sample)
      hcompact := by
  classical
  let states := sgsSelectedStates S x0 beta hbeta gamma hgamma T law.sample
  let inner := sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma T law.sample
  have hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner := by
    simpa [states, inner, sgsSelectedStates, sgsSelectedInnerProcesses] using
      sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
        (S := S) x0 beta hbeta gamma hgamma T law.sample
  have hadapted :
      sgsGeneratedQueriesStrictPastAdapted S law.sample inner := by
    simpa [inner, sgsSelectedInnerProcesses] using
      sgsSelectedGeneratedQueriesStrictPastAdapted
        (S := S) x0 beta hbeta gamma hgamma T law.sample law.sample_measurable
  have hindep_generated :
      sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
    simpa [inner, sgsSelectedInnerProcesses, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery] using hindep
  have hlinear_int_generated :
      ∀ k i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                (law.sample k i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ)
          law.P := by
    intro k i
    simpa [inner, sgsSelectedInnerProcesses, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery] using hlinear_int k i
  exact
    SGSLinearMDSLightTailInterface.of_strictPast_bridge
      (S := S) (law := law) (x0 := x0) (uStar := uStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := T)
      (states := states) (inner := inner) hrun hadapted hindep_generated
      hcoordinate_light hlinear_int_generated hcompact

/-- Finite weighted Chernoff step after the martingale mgf recurrence.

This is the Markov/optimization half of Lan Lemma 4.1 for a finite weighted
sum.  The conditional square-exponential hypotheses are intentionally not
assumed away here; they are the source martingale recurrence that must produce
`hmgf`.  This theorem is nevertheless a checked smaller boundary than the SGS
tail event: once the Lemma 4.1 recurrence gives the displayed mgf estimate for
the flattened finite sum, this lemma performs the exponential Markov step and
the minimizing choice of the Chernoff parameter. -/
theorem finite_weighted_condExp_light_tail_chernoff_bound_of_mgf
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (idx : Finset ι) (ζ : ι → Ω → ℝ) (coeff : ι → ℝ)
    (variance lambda : ℝ)
    (hlambda : 0 < lambda) (hvariance_pos : 0 < variance)
    (hmgf :
      ∀ ν : ℝ, 0 ≤ ν →
        Integrable
          (fun ω => Real.exp (ν * idx.sum (fun a => coeff a * ζ a ω))) μ ∧
        (∫ ω, Real.exp (ν * idx.sum (fun a => coeff a * ζ a ω)) ∂μ) ≤
          Real.exp (3 * ν ^ 2 * variance / 4)) :
    μ {ω | idx.sum (fun a => coeff a * ζ a ω) ≥ lambda * Real.sqrt variance} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
  classical
  let Z : Ω → ℝ := fun ω => idx.sum (fun a => coeff a * ζ a ω)
  let r : ℝ := Real.sqrt variance
  let ν : ℝ := 2 * lambda / (3 * r)
  have hr_pos : 0 < r := by
    simpa [r] using Real.sqrt_pos.2 hvariance_pos
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hν_nonneg : 0 ≤ ν := by
    positivity
  have hν_pos : 0 < ν := by
    positivity
  rcases hmgf ν hν_nonneg with ⟨hmgf_int, hmgf_bound⟩
  have hthreshold_pos : 0 < Real.exp (ν * (lambda * r)) :=
    Real.exp_pos _
  have hmarkov :
      μ {ω | Real.exp (ν * Z ω) ≥ Real.exp (ν * (lambda * r))} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
    refine measure_ge_le_of_integral_le_of_nonneg
      (μ := μ) (fun ω => Real.exp (ν * Z ω))
      (Real.exp (ν * (lambda * r)))
      (Real.exp (3 * ν ^ 2 * variance / 4))
      (Real.exp (-(lambda ^ 2) / 3))
      ?_ ?_ ?_ hthreshold_pos ?_
    · simpa [Z] using hmgf_int
    · intro ω
      exact le_of_lt (Real.exp_pos _)
    · simpa [Z] using hmgf_bound
    · have hsq : r ^ 2 = variance := by
        simpa [r] using Real.sq_sqrt (le_of_lt hvariance_pos)
      have hνr : ν * r = 2 * lambda / 3 := by
        rw [show ν = 2 * lambda / (3 * r) by rfl]
        field_simp [hr_pos.ne']
      have h_exp_arg :
          3 * ν ^ 2 * variance / 4 - ν * (lambda * r) =
            -(lambda ^ 2) / 3 := by
        calc
          3 * ν ^ 2 * variance / 4 - ν * (lambda * r)
              = 3 * (ν * r) ^ 2 / 4 - lambda * (ν * r) := by
                  rw [← hsq]
                  ring
          _ = 3 * (2 * lambda / 3) ^ 2 / 4 - lambda * (2 * lambda / 3) := by
                  rw [hνr]
          _ = -(lambda ^ 2) / 3 := by
                  ring
      apply le_of_eq
      calc
        Real.exp (3 * ν ^ 2 * variance / 4) /
            Real.exp (ν * (lambda * r))
            = Real.exp (3 * ν ^ 2 * variance / 4 - ν * (lambda * r)) := by
                rw [Real.exp_sub]
        _ = Real.exp (-(lambda ^ 2) / 3) := by rw [h_exp_arg]
  have hsubset :
      {ω | Z ω ≥ lambda * r} ⊆
        {ω | Real.exp (ν * Z ω) ≥ Real.exp (ν * (lambda * r))} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hν_nonneg)
  exact (measure_mono hsubset).trans hmarkov

/-- One-step conditional-MGF recurrence for a prefix-adapted exponential factor.

This is the internal martingale infrastructure used by Lan Lemma 4.1: if the
already-accumulated exponential prefix is measurable with respect to the current
past sigma-algebra, and the current exponential increment has a conditional MGF
bound, then the unconditional MGF advances by the same deterministic factor.
The lemma assumes only one-step conditional MGF control, not the full finite
`hmgf` conclusion consumed by the Chernoff wrapper below. -/
theorem finite_weighted_condExp_mgf_recurrence_step
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {pref step : Ω → ℝ} {C : ℝ}
    (hprefix_sm : StronglyMeasurable[m] pref)
    (hprefix_int : Integrable pref μ)
    (hstep_int : Integrable step μ)
    (hprod_int : Integrable (fun ω => pref ω * step ω) μ)
    (hprefix_nonneg : 0 ≤ᵐ[μ] pref)
    (hcond : μ[step | m] ≤ᵐ[μ] fun _ => C) :
    (∫ ω, pref ω * step ω ∂μ) ≤ C * ∫ ω, pref ω ∂μ := by
  classical
  have hpull :
      μ[(fun ω => pref ω * step ω) | m] =ᵐ[μ]
        fun ω => pref ω * μ[step | m] ω :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := μ) (m := m) hprefix_sm hprod_int hstep_int
  have hpulled_int :
      Integrable (fun ω => pref ω * μ[step | m] ω) μ :=
    (MeasureTheory.integrable_condExp
      (μ := μ) (m := m) (f := fun ω => pref ω * step ω)).congr hpull
  have hright_int : Integrable (fun ω => C * pref ω) μ :=
    hprefix_int.const_mul C
  have hpoint :
      (fun ω => pref ω * μ[step | m] ω) ≤ᵐ[μ]
        fun ω => C * pref ω := by
    filter_upwards [hprefix_nonneg, hcond] with ω hpre hce
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_left hce hpre)
  calc
    (∫ ω, pref ω * step ω ∂μ)
        = ∫ ω, μ[(fun ω => pref ω * step ω) | m] ω ∂μ := by
            exact (MeasureTheory.integral_condExp
              (μ := μ) (m := m) (f := fun ω => pref ω * step ω) hm).symm
    _ = ∫ ω, pref ω * μ[step | m] ω ∂μ := by
            exact integral_congr_ae hpull
    _ ≤ ∫ ω, C * pref ω ∂μ :=
            MeasureTheory.integral_mono_ae hpulled_int hright_int hpoint
    _ = C * ∫ ω, pref ω ∂μ := by
            rw [integral_const_mul]

/-- One-step conditional-MGF assembly from a scalar quadratic domination.

This is the measure-theoretic part of Lan Lemma 4.1's scalar step.  It does
not assume the MGF bound directly: it reduces the one-step conditional MGF
obligation to a pointwise scalar domination of `exp (nu * Z)` by a centered
linear term plus the conditional square-exponential term.  The remaining
unproved content for the source Lemma 4.1 adapter is the pure real inequality
supplying `C` and `hC_bound` from `0 <= nu` and `0 < scale`. -/
theorem condExp_exp_linear_le_of_pointwise_quadratic_domination
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {mSub : MeasurableSpace Ω} {Z : Ω → ℝ} {scale ν C B : ℝ}
    (hZ_int : Integrable Z μ)
    (hexp_linear_int : Integrable (fun ω => Real.exp (ν * Z ω)) μ)
    (hexp_sq_int : Integrable (fun ω => Real.exp (Z ω ^ 2 / scale)) μ)
    (hpoint :
      (fun ω => Real.exp (ν * Z ω)) ≤ᵐ[μ]
        fun ω => ν * Z ω + C * Real.exp (Z ω ^ 2 / scale))
    (hcond_zero : μ[Z | mSub] =ᵐ[μ] 0)
    (hcond_light :
      μ[(fun ω => Real.exp (Z ω ^ 2 / scale)) | mSub] ≤ᵐ[μ]
        fun _ => Real.exp 1)
    (hC_nonneg : 0 ≤ C)
    (hC_bound : C * Real.exp 1 ≤ B) :
    μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ≤ᵐ[μ] fun _ => B := by
  classical
  let Q : Ω → ℝ := fun ω => Real.exp (Z ω ^ 2 / scale)
  let Combo : Ω → ℝ := fun ω => ν * Z ω + C * Q ω
  have hνZ_int : Integrable (fun ω => ν * Z ω) μ := hZ_int.const_mul ν
  have hCQ_int : Integrable (fun ω => C * Q ω) μ := by
    simpa [Q] using hexp_sq_int.const_mul C
  have hcombo_int : Integrable Combo μ := hνZ_int.add hCQ_int
  have hmono :
      μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ≤ᵐ[μ] μ[Combo | mSub] := by
    exact MeasureTheory.condExp_mono
      (m := mSub) hexp_linear_int hcombo_int (by simpa [Combo, Q] using hpoint)
  have hνZ_cond :
      μ[(fun ω => ν * Z ω) | mSub] =ᵐ[μ] fun ω => ν * μ[Z | mSub] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul
        (μ := μ) (c := ν) (f := Z) (m := mSub))
  have hCQ_cond :
      μ[(fun ω => C * Q ω) | mSub] =ᵐ[μ] fun ω => C * μ[Q | mSub] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul
        (μ := μ) (c := C) (f := Q) (m := mSub))
  have hcombo_cond :
      μ[Combo | mSub] =ᵐ[μ]
        fun ω => ν * μ[Z | mSub] ω + C * μ[Q | mSub] ω := by
    have hadd :
        μ[(fun ω => ν * Z ω + C * Q ω) | mSub] =ᵐ[μ]
          μ[(fun ω => ν * Z ω) | mSub] + μ[(fun ω => C * Q ω) | mSub] :=
      MeasureTheory.condExp_add
        (μ := μ) (f := fun ω => ν * Z ω) (g := fun ω => C * Q ω)
        hνZ_int hCQ_int mSub
    filter_upwards [hadd, hνZ_cond, hCQ_cond] with ω haddω hνω hCω
    calc
      μ[Combo | mSub] ω =
          μ[(fun ω => ν * Z ω + C * Q ω) | mSub] ω := by rfl
      _ = (μ[(fun ω => ν * Z ω) | mSub] +
            μ[(fun ω => C * Q ω) | mSub]) ω := haddω
      _ = ν * μ[Z | mSub] ω + C * μ[Q | mSub] ω := by
            simp [hνω, hCω]
  filter_upwards [hmono, hcombo_cond, hcond_zero, hcond_light] with
    ω hle hcomboω hzeroω hlightω
  have hzero_scalar : μ[Z | mSub] ω = 0 := by simpa using hzeroω
  calc
    μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ω
        ≤ μ[Combo | mSub] ω := hle
    _ = ν * μ[Z | mSub] ω + C * μ[Q | mSub] ω := hcomboω
    _ = C * μ[Q | mSub] ω := by rw [hzero_scalar]; ring
    _ ≤ C * Real.exp 1 := mul_le_mul_of_nonneg_left hlightω hC_nonneg
    _ ≤ B := hC_bound

/-- One-step conditional-MGF assembly from a pointwise linear-plus-residual
bound.

This is the measure-theoretic core needed by the small-parameter branch of
Lan Lemma 4.1: once `exp (ν Z)` is dominated by the centered linear term
`ν Z` plus an integrable residual `R`, conditional mean-zero removes the
linear term and a conditional residual bound supplies the deterministic MGF
constant. -/
theorem condExp_exp_linear_le_of_pointwise_linear_plus
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {mSub : MeasurableSpace Ω} {Z R : Ω → ℝ} {ν B : ℝ}
    (hZ_int : Integrable Z μ)
    (hexp_linear_int : Integrable (fun ω => Real.exp (ν * Z ω)) μ)
    (hR_int : Integrable R μ)
    (hpoint :
      (fun ω => Real.exp (ν * Z ω)) ≤ᵐ[μ]
        fun ω => ν * Z ω + R ω)
    (hcond_zero : μ[Z | mSub] =ᵐ[μ] 0)
    (hcond_R : μ[R | mSub] ≤ᵐ[μ] fun _ => B) :
    μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ≤ᵐ[μ] fun _ => B := by
  classical
  let Combo : Ω → ℝ := fun ω => ν * Z ω + R ω
  have hνZ_int : Integrable (fun ω => ν * Z ω) μ := hZ_int.const_mul ν
  have hcombo_int : Integrable Combo μ := hνZ_int.add hR_int
  have hmono :
      μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ≤ᵐ[μ] μ[Combo | mSub] := by
    exact MeasureTheory.condExp_mono
      (m := mSub) hexp_linear_int hcombo_int (by simpa [Combo] using hpoint)
  have hνZ_cond :
      μ[(fun ω => ν * Z ω) | mSub] =ᵐ[μ] fun ω => ν * μ[Z | mSub] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul
        (μ := μ) (c := ν) (f := Z) (m := mSub))
  have hcombo_cond :
      μ[Combo | mSub] =ᵐ[μ] fun ω => ν * μ[Z | mSub] ω + μ[R | mSub] ω := by
    have hadd :
        μ[(fun ω => ν * Z ω + R ω) | mSub] =ᵐ[μ]
          μ[(fun ω => ν * Z ω) | mSub] + μ[R | mSub] :=
      MeasureTheory.condExp_add
        (μ := μ) (f := fun ω => ν * Z ω) (g := R)
        hνZ_int hR_int mSub
    filter_upwards [hadd, hνZ_cond] with ω haddω hνω
    calc
      μ[Combo | mSub] ω =
          μ[(fun ω => ν * Z ω + R ω) | mSub] ω := by rfl
      _ = (μ[(fun ω => ν * Z ω) | mSub] + μ[R | mSub]) ω := haddω
      _ = ν * μ[Z | mSub] ω + μ[R | mSub] ω := by simp [hνω]
  filter_upwards [hmono, hcombo_cond, hcond_zero, hcond_R] with
    ω hle hcomboω hzeroω hRω
  have hzero_scalar : μ[Z | mSub] ω = 0 := by simpa using hzeroω
  calc
    μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ω
        ≤ μ[Combo | mSub] ω := hle
    _ = ν * μ[Z | mSub] ω + μ[R | mSub] ω := hcomboω
    _ = μ[R | mSub] ω := by rw [hzero_scalar]; ring
    _ ≤ B := hRω

/-- Scalar Young domination for the exponential-linear term in Lan Lemma 4.1.

For positive quadratic scale, `ν z` is bounded by a deterministic constant plus
`z^2 / scale`.  This is the pure real inequality used to turn the source
square-exponential moment into one-step exponential-linear integrability and
conditional-MGF control. -/
theorem exp_linear_le_const_mul_exp_quadratic
    {scale ν z : ℝ} (hscale : 0 < scale) :
    Real.exp (ν * z) ≤
      Real.exp (ν ^ 2 * scale / 4) * Real.exp (z ^ 2 / scale) := by
  have harg : ν * z ≤ ν ^ 2 * scale / 4 + z ^ 2 / scale := by
    have hsq : 0 ≤ (z - ν * scale / 2) ^ 2 := sq_nonneg _
    have hmul :
        0 ≤ scale * (ν ^ 2 * scale / 4 + z ^ 2 / scale - ν * z) := by
      field_simp [hscale.ne']
      nlinarith [hsq]
    have hnonneg :
        0 ≤ ν ^ 2 * scale / 4 + z ^ 2 / scale - ν * z :=
      (mul_nonneg_iff_of_pos_left hscale).mp hmul
    linarith
  calc
    Real.exp (ν * z) ≤ Real.exp (ν ^ 2 * scale / 4 + z ^ 2 / scale) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp (ν ^ 2 * scale / 4) * Real.exp (z ^ 2 / scale) := by
      rw [Real.exp_add]

/-- Exponential-linear integrability from a square-exponential moment.

This is the Lean well-definedness side of the Lemma 4.1 scalar step.  It is
private route-local infrastructure: the source light-tail assumption supplies
the square-exponential integrability, and the scalar Young domination above
supplies the finite-measure domination needed by Mathlib's `Integrable.mono`. -/
theorem integrable_exp_linear_of_integrable_exp_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} {scale ν : ℝ}
    (hscale : 0 < scale)
    (hZ_int : Integrable Z μ)
    (hexp_sq_int : Integrable (fun ω => Real.exp (Z ω ^ 2 / scale)) μ) :
    Integrable (fun ω => Real.exp (ν * Z ω)) μ := by
  classical
  let C : ℝ := Real.exp (ν ^ 2 * scale / 4)
  have htarget_aesm :
      AEStronglyMeasurable (fun ω => Real.exp (ν * Z ω)) μ := by
    have hcont : Continuous fun x : ℝ => Real.exp (ν * x) := by fun_prop
    exact hcont.aestronglyMeasurable.comp_aemeasurable
      hZ_int.aestronglyMeasurable.aemeasurable
  refine Integrable.mono (hexp_sq_int.const_mul C) htarget_aesm ?_
  filter_upwards with ω
  have hle := exp_linear_le_const_mul_exp_quadratic
    (scale := scale) (ν := ν) (z := Z ω) hscale
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.exp_nonneg _)]
  rw [abs_of_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) (Real.exp_nonneg _))]
  simpa [C] using hle

/-- Conditional Jensen for fractional powers of a nonnegative random variable.

This is the small-parameter part of Lan Lemma 4.1's one-step MGF proof.  If
`0 <= α <= 1`, concavity of `x ↦ x^α` on `[0,∞)` gives
`E[Q^α | m] <= E[Q | m]^α` for nonnegative `Q`. -/
theorem condExp_rpow_le_rpow_condExp_of_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {mSub : MeasurableSpace Ω} (hmSub : mSub ≤ mΩ)
    {Q : Ω → ℝ} {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hQ_int : Integrable Q μ)
    (hQα_int : Integrable (fun ω => (Q ω) ^ α) μ)
    (hQ_nonneg : 0 ≤ᵐ[μ] Q) :
    μ[(fun ω => (Q ω) ^ α) | mSub] ≤ᵐ[μ]
      fun ω => (μ[Q | mSub] ω) ^ α := by
  classical
  have hconc : ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ α) :=
    Real.concaveOn_rpow hα_nonneg hα_le_one
  have hcont :
      ContinuousOn (fun x : ℝ => x ^ α) (Set.Ici (0 : ℝ)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inr hα_nonneg)
  have hJ :
      μ[((fun x : ℝ => x ^ α) ∘ Q) | mSub] ≤ᵐ[μ]
        (fun x : ℝ => x ^ α) ∘ μ[Q | mSub] := by
    exact
      hconc.condExp_map_le
        (μ := μ) (m := mSub) (mα := mΩ) (f := Q)
        (φ := fun x : ℝ => x ^ α) (s := Set.Ici (0 : ℝ))
        hmSub hcont.upperSemicontinuousOn hQ_nonneg isClosed_Ici
        hQ_int (by simpa [Function.comp_def] using hQα_int)
  simpa [Function.comp_def] using hJ

/-- Fractional powers of a nonnegative integrable real random variable are
integrable for exponents in `[0, 1]`. -/
theorem integrable_rpow_of_integrable_nonneg_of_exponent_le_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Q : Ω → ℝ} {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hQ_int : Integrable Q μ)
    (hQ_nonneg : ∀ ω, 0 ≤ Q ω) :
    Integrable (fun ω => (Q ω) ^ α) μ := by
  classical
  have htarget_aesm :
      AEStronglyMeasurable (fun ω => (Q ω) ^ α) μ := by
    have hcont : Continuous fun x : ℝ => x ^ α :=
      continuous_id.rpow_const (fun _ => Or.inr hα_nonneg)
    exact hcont.aestronglyMeasurable.comp_aemeasurable
      hQ_int.aestronglyMeasurable.aemeasurable
  have hbound :
      (fun ω => ‖(Q ω) ^ α‖) ≤ᵐ[μ] fun ω => (1 : ℝ) + Q ω := by
    filter_upwards with ω
    have hQ0 : 0 ≤ Q ω := hQ_nonneg ω
    have hpownonneg : 0 ≤ (Q ω) ^ α := Real.rpow_nonneg hQ0 α
    rw [Real.norm_eq_abs, abs_of_nonneg hpownonneg]
    by_cases hle : Q ω ≤ 1
    · have hp_le_one : (Q ω) ^ α ≤ 1 :=
        Real.rpow_le_one hQ0 hle hα_nonneg
      linarith [hQ0]
    · have hone_le : 1 ≤ Q ω := le_of_not_ge hle
      have hp_le_self : (Q ω) ^ α ≤ Q ω :=
        Real.rpow_le_self_of_one_le hone_le hα_le_one
      linarith
  exact Integrable.mono' ((integrable_const (1 : ℝ)).add hQ_int)
    htarget_aesm hbound

/-- Conditional fractional-power control from the square-exponential light-tail
bound.

For `0 <= α <= 1`, if `Q >= 0` and `E[Q | m] <= exp 1`, then conditional
Jensen gives `E[Q^α | m] <= exp α`. -/
theorem condExp_rpow_le_exp_of_condExp_le_exp_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {mSub : MeasurableSpace Ω} (hmSub : mSub ≤ mΩ)
    {Q : Ω → ℝ} {α : ℝ}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hQ_int : Integrable Q μ)
    (hQα_int : Integrable (fun ω => (Q ω) ^ α) μ)
    (hQ_nonneg : 0 ≤ᵐ[μ] Q)
    (hcond_Q : μ[Q | mSub] ≤ᵐ[μ] fun _ => Real.exp 1) :
    μ[(fun ω => (Q ω) ^ α) | mSub] ≤ᵐ[μ] fun _ => Real.exp α := by
  classical
  have hJ :=
    condExp_rpow_le_rpow_condExp_of_nonneg
      (mΩ := mΩ) (μ := μ) (mSub := mSub) hmSub hα_nonneg hα_le_one
      hQ_int hQα_int hQ_nonneg
  have hcond_nonneg : 0 ≤ᵐ[μ] μ[Q | mSub] := by
    have hzero : (fun _ : Ω => (0 : ℝ)) ≤ᵐ[μ] Q := by
      simpa using hQ_nonneg
    have hmono :
        μ[(fun _ : Ω => (0 : ℝ)) | mSub] ≤ᵐ[μ] μ[Q | mSub] :=
      MeasureTheory.condExp_mono
        (m := mSub) (integrable_const (0 : ℝ)) hQ_int hzero
    have hconst :
        μ[(fun _ : Ω => (0 : ℝ)) | mSub] = fun _ : Ω => (0 : ℝ) :=
      MeasureTheory.condExp_const (μ := μ) (m := mSub) hmSub (0 : ℝ)
    filter_upwards [hmono] with ω hω
    simpa [hconst] using hω
  filter_upwards [hJ, hcond_nonneg, hcond_Q] with ω hJω hnonnegω hQω
  calc
    μ[(fun ω => (Q ω) ^ α) | mSub] ω
        ≤ (μ[Q | mSub] ω) ^ α := hJω
    _ ≤ (Real.exp 1) ^ α :=
        Real.rpow_le_rpow hnonnegω hQω hα_nonneg
    _ = Real.exp α := by
        simpa using (Real.exp_one_rpow α)

/-- Scalar exponential domination used in Lan Lemma 4.1's small-parameter
one-step MGF branch. -/
theorem exp_le_self_add_exp_three_mul_sq_div_four (x : ℝ) :
    Real.exp x ≤ x + Real.exp (3 * x ^ 2 / 4) := by
  classical
  let f : ℝ → ℝ := fun y => y + Real.exp (y ^ 2 * (3 / 4)) - Real.exp y
  have hexp_quarter_le : Real.exp ((1 : ℝ) / 4) ≤ 3 / 2 := by
    have h :=
      Real.exp_bound' (x := (1 : ℝ) / 4) (n := 3)
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hexp_one_le : Real.exp (1 : ℝ) ≤ 11 / 4 := by
    have h :=
      Real.exp_bound' (x := (1 : ℝ)) (n := 4)
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hexp_neg_one_le_half : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
    simpa [Real.exp_neg] using h
  have hpos_small :
      ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
        Real.exp y ≤ y + Real.exp (3 * y ^ 2 / 4) := by
    intro y hy0 hy1
    have h :=
      Real.exp_bound' (x := y) (n := 3) hy0 hy1 (by norm_num)
    have hpoly :
        (∑ m ∈ Finset.range 3, y ^ m / (m.factorial : ℝ)) +
            y ^ 3 * (3 + 1 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)
          ≤ y + (1 + 3 * y ^ 2 / 4) := by
      have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
      have hy_cube_le_sq : y ^ 3 ≤ y ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hy1 hy0]
      norm_num [Finset.sum_range_succ, pow_succ]
      nlinarith
    have htail :
        y + (1 + 3 * y ^ 2 / 4) ≤
          y + Real.exp (3 * y ^ 2 / 4) := by
      have hadd := Real.add_one_le_exp (3 * y ^ 2 / 4)
      linarith
    exact h.trans (hpoly.trans htail)
  have hneg_small :
      ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
        Real.exp (-y) + y ≤ Real.exp (3 * y ^ 2 / 4) := by
    intro y hy0 hy1
    have hy_abs : |(-y : ℝ)| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg hy0]
      exact hy1
    have h :=
      Real.exp_bound (x := -y) (n := 3) hy_abs (by norm_num)
    have hupper :
        Real.exp (-y) ≤
          (∑ m ∈ Finset.range 3, (-y) ^ m / (m.factorial : ℝ)) +
            y ^ 3 * ((4 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) := by
      have habs_pow : |(-y : ℝ)| ^ 3 = y ^ 3 := by
        rw [abs_neg, abs_of_nonneg hy0]
      have hleft := (abs_sub_le_iff.mp h).1
      rw [habs_pow] at hleft
      simpa [Nat.succ_eq_add_one] using sub_le_iff_le_add'.mp hleft
    have hpoly :
        (∑ m ∈ Finset.range 3, (-y) ^ m / (m.factorial : ℝ)) +
            y ^ 3 * (3 + 1 : ℝ) / ((Nat.factorial 3 : ℝ) * 3) + y
          ≤ 1 + 3 * y ^ 2 / 4 := by
      have hy_cube_le_sq : y ^ 3 ≤ y ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hy1 hy0]
      norm_num [Finset.sum_range_succ, pow_succ]
      nlinarith
    have htail :
        1 + 3 * y ^ 2 / 4 ≤ Real.exp (3 * y ^ 2 / 4) :=
      by
        have h := Real.add_one_le_exp (3 * y ^ 2 / 4)
        linarith
    linarith
  have hpos_mid :
      ∀ y : ℝ, 1 ≤ y → y ≤ 4 / 3 →
        Real.exp y ≤ y + Real.exp (3 * y ^ 2 / 4) := by
    intro y hy1 hy43
    have hmono : MonotoneOn f (Set.Icc (1 : ℝ) (4 / 3)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
      · exact (by fun_prop : Continuous f).continuousOn
      · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc (1 : ℝ) (4 / 3))))
      · intro z hz
        have hz1 : 1 ≤ z := by
          have hz' : z ∈ Set.Ioo (1 : ℝ) (4 / 3) := by simpa using hz
          exact le_of_lt hz'.1
        have hderiv :
            deriv f z =
              1 + z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) -
                Real.exp z := by
          have hf_has :
              HasDerivAt f
                (1 + Real.exp (z ^ 2 * (3 / 4)) * (2 * z * (3 / 4)) -
                  Real.exp z) z := by
            have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
              simpa using (hasDerivAt_pow 2 z)
            have hquad :
                HasDerivAt (fun t : ℝ => t ^ 2 * (3 / 4)) (2 * z * (3 / 4)) z :=
              hsq.mul_const (3 / 4)
            have hexp_quad :
                HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 * (3 / 4)))
                  (Real.exp (z ^ 2 * (3 / 4)) * (2 * z * (3 / 4))) z :=
              hquad.exp
            simpa [f, sub_eq_add_neg] using
              ((hasDerivAt_id' z).add hexp_quad).add ((Real.hasDerivAt_exp z).neg)
          have hf_deriv := hf_has.deriv
          calc
            deriv f z =
                1 + Real.exp (z ^ 2 * (3 / 4)) * (2 * z * (3 / 4)) -
                  Real.exp z := hf_deriv
            _ = 1 + z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) -
                  Real.exp z := by ring
        rw [hderiv]
        have harg : z - 3 * z ^ 2 / 4 ≤ (1 : ℝ) / 4 := by
          nlinarith [sq_nonneg (z - 2 / 3)]
        have hexp_factor :
            Real.exp z ≤ (3 / 2) * Real.exp (3 * z ^ 2 / 4) := by
          calc
            Real.exp z =
                Real.exp (3 * z ^ 2 / 4) * Real.exp (z - 3 * z ^ 2 / 4) := by
                  rw [← Real.exp_add]
                  congr 1
                  ring
            _ ≤ Real.exp (3 * z ^ 2 / 4) * Real.exp ((1 : ℝ) / 4) := by
                  exact mul_le_mul_of_nonneg_left
                    (Real.exp_le_exp.mpr harg) (le_of_lt (Real.exp_pos _))
            _ ≤ Real.exp (3 * z ^ 2 / 4) * (3 / 2) := by
                  exact mul_le_mul_of_nonneg_left hexp_quarter_le
                    (le_of_lt (Real.exp_pos _))
            _ = (3 / 2) * Real.exp (3 * z ^ 2 / 4) := by ring
        have hfactor_le :
            (3 / 2) * Real.exp (3 * z ^ 2 / 4) ≤
              z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) := by
          have hcoeff : (3 / 2 : ℝ) ≤ z * (3 / 2) := by nlinarith
          calc
            (3 / 2) * Real.exp (3 * z ^ 2 / 4)
                ≤ (z * (3 / 2)) * Real.exp (3 * z ^ 2 / 4) := by
                    exact mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
            _ = z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) := by ring
        nlinarith
    have hbase : 0 ≤ f 1 := by
      have hlow : (7 / 4 : ℝ) ≤ Real.exp (3 / 4 : ℝ) := by
        have h := Real.add_one_le_exp (3 / 4 : ℝ)
        norm_num at h ⊢
        linarith
      have hval : f 1 = 1 + Real.exp (3 / 4) - Real.exp 1 := by
        simp [f]
      rw [hval]
      linarith
    have hy_mem : y ∈ Set.Icc (1 : ℝ) (4 / 3) := ⟨hy1, hy43⟩
    have hle := hmono (by norm_num) hy_mem hy1
    have hf_nonneg : 0 ≤ f y := hbase.trans hle
    dsimp [f] at hf_nonneg
    have hquad_eq : y ^ 2 * (3 / 4) = 3 * y ^ 2 / 4 := by ring
    rw [hquad_eq] at hf_nonneg
    linarith
  have hneg_mid :
      ∀ y : ℝ, 1 ≤ y → y ≤ 4 / 3 →
        Real.exp (-y) + y ≤ Real.exp (3 * y ^ 2 / 4) := by
    intro y hy1 hy43
    let g : ℝ → ℝ := fun z => Real.exp (z ^ 2 * (3 / 4)) - z - Real.exp (-z)
    have hmono : MonotoneOn g (Set.Icc (1 : ℝ) (4 / 3)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
      · exact (by fun_prop : Continuous g).continuousOn
      · exact (by fun_prop : DifferentiableOn ℝ g (interior (Set.Icc (1 : ℝ) (4 / 3))))
      · intro z hz
        have hz1 : 1 ≤ z := by
          have hz' : z ∈ Set.Ioo (1 : ℝ) (4 / 3) := by simpa using hz
          exact le_of_lt hz'.1
        have hderiv :
            deriv g z =
              -1 + z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) +
                Real.exp (-z) := by
          have hg_has :
              HasDerivAt g
                (Real.exp (z ^ 2 * (3 / 4)) * (2 * z * (3 / 4)) - 1 +
                  Real.exp (-z)) z := by
            have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
              simpa using (hasDerivAt_pow 2 z)
            have hquad :
                HasDerivAt (fun t : ℝ => t ^ 2 * (3 / 4)) (2 * z * (3 / 4)) z :=
              hsq.mul_const (3 / 4)
            have hexp_quad :
                HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 * (3 / 4)))
                  (Real.exp (z ^ 2 * (3 / 4)) * (2 * z * (3 / 4))) z :=
              hquad.exp
            have hexp_neg :
                HasDerivAt (fun t : ℝ => Real.exp (-t))
                  (Real.exp (-z) * (-1)) z := by
              simpa using (hasDerivAt_id' z).neg.exp
            simpa [g, sub_eq_add_neg] using
              (hexp_quad.add ((hasDerivAt_id' z).neg)).add (hexp_neg.neg)
          have hg_deriv := hg_has.deriv
          calc
            deriv g z =
                Real.exp (z ^ 2 * (3 / 4)) * (2 * z * (3 / 4)) - 1 +
                  Real.exp (-z) := hg_deriv
            _ = -1 + z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) +
                  Real.exp (-z) := by ring
        rw [hderiv]
        have hmain : (1 : ℝ) ≤ z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) := by
          have hcoeff : 1 ≤ z * (3 / 2 : ℝ) := by nlinarith
          have hexp_ge : 1 ≤ Real.exp (3 * z ^ 2 / 4) := by
            exact Real.one_le_exp (by positivity)
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (z * (3 / 2)) * Real.exp (3 * z ^ 2 / 4) := by
                exact mul_le_mul hcoeff hexp_ge zero_le_one (by nlinarith)
            _ = z * Real.exp (z ^ 2 * (3 / 4)) * (3 / 2) := by ring
        nlinarith [Real.exp_pos (-z)]
    have hbase : 0 ≤ g 1 := by
      have hlow : (7 / 4 : ℝ) ≤ Real.exp (3 / 4 : ℝ) := by
        have h := Real.add_one_le_exp (3 / 4 : ℝ)
        norm_num at h ⊢
        linarith
      have hval : g 1 = Real.exp (3 / 4) - 1 - Real.exp (-(1 : ℝ)) := by
        simp [g]
      rw [hval]
      nlinarith
    have hy_mem : y ∈ Set.Icc (1 : ℝ) (4 / 3) := ⟨hy1, hy43⟩
    have hle := hmono (by norm_num) hy_mem hy1
    have hg_nonneg : 0 ≤ g y := hbase.trans hle
    dsimp [g] at hg_nonneg
    have hquad_eq : y ^ 2 * (3 / 4) = 3 * y ^ 2 / 4 := by ring
    rw [hquad_eq] at hg_nonneg
    linarith
  by_cases hx0 : 0 ≤ x
  · by_cases hx1 : x ≤ 1
    · exact hpos_small x hx0 hx1
    · have hx1' : 1 ≤ x := le_of_not_ge hx1
      by_cases hx43 : x ≤ 4 / 3
      · exact hpos_mid x hx1' hx43
      · have hlarge_arg : x ≤ 3 * x ^ 2 / 4 := by
          have hx43' : 4 / 3 ≤ x := le_of_not_ge hx43
          nlinarith
        calc
          Real.exp x ≤ Real.exp (3 * x ^ 2 / 4) :=
            Real.exp_le_exp.mpr hlarge_arg
          _ ≤ x + Real.exp (3 * x ^ 2 / 4) :=
            le_add_of_nonneg_left hx0
  · let y : ℝ := -x
    have hy0 : 0 ≤ y := by dsimp [y]; linarith
    have hx_eq : x = -y := by dsimp [y]; ring
    by_cases hy1 : y ≤ 1
    · have h := hneg_small y hy0 hy1
      rw [hx_eq]
      have hsquare : (-y) ^ 2 = y ^ 2 := by ring
      rw [hsquare]
      nlinarith
    · have hy1' : 1 ≤ y := le_of_not_ge hy1
      by_cases hy43 : y ≤ 4 / 3
      · have h := hneg_mid y hy1' hy43
        rw [hx_eq]
        have hsquare : (-y) ^ 2 = y ^ 2 := by ring
        rw [hsquare]
        nlinarith
      · have hy43' : 4 / 3 ≤ y := le_of_not_ge hy43
        have hy_le_quad : y ≤ 3 * y ^ 2 / 4 := by nlinarith
        have htail :
            y + 1 ≤ Real.exp (3 * y ^ 2 / 4) := by
          have hadd := Real.add_one_le_exp (3 * y ^ 2 / 4)
          nlinarith
        have hexp_neg_le_one : Real.exp (-y) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          linarith
        rw [hx_eq]
        have hsquare : (-y) ^ 2 = y ^ 2 := by ring
        rw [hsquare]
        nlinarith

/-- Nonnegative real exponential dominates its quadratic Taylor truncation.

This private real-analysis helper is used only to close the scalar inequality
from Lan Lemma 4.1; it follows by differentiating
`exp x - (1 + x + x^2/2)` and using `1 + x <= exp x`. -/
theorem one_add_self_add_sq_div_two_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + (1 / 2 : ℝ) * x ^ 2 ≤ Real.exp x := by
  classical
  let f : ℝ → ℝ := fun t => Real.exp t - (1 + t + (1 / 2 : ℝ) * t ^ 2)
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (by fun_prop : Continuous f).continuousOn
    · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) x)))
    · intro z hz
      have hz_nonneg : 0 ≤ z := by
        have hz' : z ∈ Set.Ioo (0 : ℝ) x := by simpa using hz
        exact le_of_lt hz'.1
      have hderiv :
          deriv f z = Real.exp z - (1 + z) := by
        have hp :
            HasDerivAt (fun t : ℝ => 1 + t + (1 / 2 : ℝ) * t ^ 2) (1 + z) z := by
          have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
            simpa using (hasDerivAt_pow 2 z)
          have hsq_div :
              HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) z z := by
            convert hsq.const_mul ((1 : ℝ) / 2) using 1 <;> ring
          simpa using
            ((hasDerivAt_const (x := z) (c := (1 : ℝ))).add
              (hasDerivAt_id' z)).add hsq_div
        have hf_has : HasDerivAt f (Real.exp z - (1 + z)) z := by
          convert (Real.hasDerivAt_exp z).sub hp using 1 <;> ext t <;> ring
        exact hf_has.deriv
      rw [hderiv]
      linarith [Real.add_one_le_exp z]
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx⟩
  have hx_mem : x ∈ Set.Icc (0 : ℝ) x := ⟨hx, le_rfl⟩
  have hle := hmono h0_mem hx_mem hx
  have hf0 : f 0 = 0 := by simp [f]
  have hfx : f x = Real.exp x - (1 + x + (1 / 2 : ℝ) * x ^ 2) := by simp [f]
  rw [hf0, hfx] at hle
  linarith

/-- Nonnegative real exponential dominates its cubic Taylor truncation.

This is obtained from the quadratic truncation by the same derivative
argument. -/
theorem one_add_self_add_sq_div_two_add_cube_div_six_le_exp
    {x : ℝ} (hx : 0 ≤ x) :
    1 + x + (1 / 2 : ℝ) * x ^ 2 + (1 / 6 : ℝ) * x ^ 3 ≤ Real.exp x := by
  classical
  let f : ℝ → ℝ :=
    fun t => Real.exp t - (1 + t + (1 / 2 : ℝ) * t ^ 2 + (1 / 6 : ℝ) * t ^ 3)
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (by fun_prop : Continuous f).continuousOn
    · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) x)))
    · intro z hz
      have hz_nonneg : 0 ≤ z := by
        have hz' : z ∈ Set.Ioo (0 : ℝ) x := by simpa using hz
        exact le_of_lt hz'.1
      have hderiv :
          deriv f z = Real.exp z - (1 + z + (1 / 2 : ℝ) * z ^ 2) := by
        have hp :
            HasDerivAt
              (fun t : ℝ =>
                1 + t + (1 / 2 : ℝ) * t ^ 2 + (1 / 6 : ℝ) * t ^ 3)
              (1 + z + (1 / 2 : ℝ) * z ^ 2) z := by
          have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
            simpa using (hasDerivAt_pow 2 z)
          have hsq_div :
              HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) z z := by
            convert hsq.const_mul ((1 : ℝ) / 2) using 1 <;> ring
          have hcube : HasDerivAt (fun t : ℝ => t ^ 3) (3 * z ^ 2) z := by
            simpa using (hasDerivAt_pow 3 z)
          have hcube_div :
              HasDerivAt (fun t : ℝ => (1 / 6 : ℝ) * t ^ 3)
                ((1 / 2 : ℝ) * z ^ 2) z := by
            convert hcube.const_mul ((1 : ℝ) / 6) using 1 <;> ring
          simpa using
            (((hasDerivAt_const (x := z) (c := (1 : ℝ))).add
              (hasDerivAt_id' z)).add hsq_div).add hcube_div
        have hf_has :
            HasDerivAt f (Real.exp z - (1 + z + (1 / 2 : ℝ) * z ^ 2)) z := by
          convert (Real.hasDerivAt_exp z).sub hp using 1 <;> ext t <;> ring
        exact hf_has.deriv
      rw [hderiv]
      exact sub_nonneg.mpr (one_add_self_add_sq_div_two_le_exp hz_nonneg)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx⟩
  have hx_mem : x ∈ Set.Icc (0 : ℝ) x := ⟨hx, le_rfl⟩
  have hle := hmono h0_mem hx_mem hx
  have hf0 : f 0 = 0 := by simp [f]
  have hfx :
      f x =
        Real.exp x - (1 + x + (1 / 2 : ℝ) * x ^ 2 + (1 / 6 : ℝ) * x ^ 3) := by
    simp [f]
  rw [hf0, hfx] at hle
  linarith

/-- Quartic certificate for the small positive branch of Lan Lemma 4.1.

Candidate audit: searched target/SOptLib/Mathlib for the sharp
`exp x <= x + exp (9*x^2/16)` scalar inequality and interval polynomial
certificates; the only matching exponential helper was the weaker local
`exp_le_self_add_exp_three_mul_sq_div_four`, so this route-local polynomial
certificate supplies the missing `9/16` Taylor comparison. -/
theorem quartic_nonneg_for_exp_nine_small {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    0 ≤ 729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536 := by
  by_cases hyhalf : y ≤ (1 : ℝ) / 2
  · have hquad_nonneg :
        0 ≤ 2608 * (y - 512 / 652) ^ 2 := by positivity
    nlinarith [hquad_nonneg]
  · have hyhalf' : (1 : ℝ) / 2 ≤ y := le_of_not_ge hyhalf
    by_cases hy23 : y ≤ (2 : ℝ) / 3
    · let s : ℝ := (2 : ℝ) / 3 - y
      have hs0 : 0 ≤ s := by dsimp [s]; linarith
      have hs_le : s ≤ (1 : ℝ) / 6 := by dsimp [s]; linarith
      have hs2_le : s ^ 2 ≤ (1 / 6 : ℝ) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hs0 hs_le
      have hs3_le : s ^ 3 ≤ (1 / 6 : ℝ) ^ 3 := by
        have hmul := mul_le_mul hs2_le hs_le hs0 (by positivity : 0 ≤ (1 / 6 : ℝ) ^ 2)
        simpa [pow_succ] using hmul
      have hrewrite :
          729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536 =
            729 * s ^ 4 - 1944 * s ^ 3 + 4552 * s ^ 2 -
              (736 / 3) * s + 976 / 9 := by
        dsimp [s]
        ring
      rw [hrewrite]
      nlinarith [sq_nonneg s, hs3_le]
    · have hy23' : (2 : ℝ) / 3 ≤ y := le_of_not_ge hy23
      let t : ℝ := y - (2 : ℝ) / 3
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have hrewrite :
          729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536 =
            729 * t ^ 4 + 1944 * t ^ 3 + 4552 * t ^ 2 +
              (736 / 3) * t + 976 / 9 := by
        dsimp [t]
        ring
      rw [hrewrite]
      positivity

/-- Small positive branch of the sharp scalar inequality in Lan Lemma 4.1.

This uses `Real.exp_bound'` at order four and the cubic Taylor lower bound for
`exp ((9/16) y^2)`.  Candidate audit: searched target/SOptLib/Mathlib for a
sharp `9/16` exponential-square inequality; only the weaker local `3/4`
version matched, so this helper proves the source-specific small interval
directly. -/
theorem exp_pos_small_branch_le_self_add_exp_nine_mul_sq_div_sixteen
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y ≤ y + Real.exp (9 * y ^ 2 / 16) := by
  let a : ℝ := 9 / 16
  have hquad_nonneg : 0 ≤ a * y ^ 2 := by positivity
  have hlower_cubic :
      1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 +
          (1 / 6 : ℝ) * (a * y ^ 2) ^ 3 ≤
        Real.exp (a * y ^ 2) := by
    exact one_add_self_add_sq_div_two_add_cube_div_six_le_exp hquad_nonneg
  have hupper :=
    Real.exp_bound' (x := y) (n := 4) hy0 hy1 (by norm_num)
  have hpoly :
      (∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
          y ^ 4 * (4 + 1 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)
        ≤ y + (1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 +
            (1 / 6 : ℝ) * (a * y ^ 2) ^ 3) := by
    have hq := quartic_nonneg_for_exp_nine_small hy0 hy1
    have hprod :
        0 ≤ y ^ 2 * (729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536) := by
      exact mul_nonneg (sq_nonneg y) hq
    norm_num [a, Finset.sum_range_succ, pow_succ]
    nlinarith
  calc
    Real.exp y
        ≤ (∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
            y ^ 4 * (4 + 1 : ℝ) / ((Nat.factorial 4 : ℝ) * 4) := hupper
    _ ≤ y + (1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 +
            (1 / 6 : ℝ) * (a * y ^ 2) ^ 3) := hpoly
    _ ≤ y + Real.exp (a * y ^ 2) := by linarith
    _ = y + Real.exp (9 * y ^ 2 / 16) := by
          congr 1
          congr 1
          dsimp [a]
          ring

/-- Mid positive branch of the sharp scalar inequality in Lan Lemma 4.1.

On `1 <= y < 16/9`, the residual
`y + exp ((9/16)y^2) - exp y` is monotone.  The derivative comparison uses
`exp y = exp 1 * exp (y-1)`, `Real.exp_bound'` for `y-1 <= 1`, and a
positive-coefficient polynomial certificate after shifting by `1`. -/
theorem exp_pos_mid_branch_le_self_add_exp_nine_mul_sq_div_sixteen
    {y : ℝ} (hy1 : 1 ≤ y) (hy_upper : y < (16 : ℝ) / 9) :
    Real.exp y ≤ y + Real.exp (9 * y ^ 2 / 16) := by
  classical
  let a : ℝ := 9 / 16
  let f : ℝ → ℝ := fun z => z + Real.exp (z ^ 2 * a) - Real.exp z
  have hexp_one_le : Real.exp (1 : ℝ) ≤ 11 / 4 := by
    have h :=
      Real.exp_bound' (x := (1 : ℝ)) (n := 4)
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hmono : MonotoneOn f (Set.Icc (1 : ℝ) (16 / 9)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (by fun_prop : Continuous f).continuousOn
    · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc (1 : ℝ) (16 / 9))))
    · intro z hz
      have hz' : z ∈ Set.Ioo (1 : ℝ) (16 / 9) := by simpa using hz
      have hz1 : 1 ≤ z := le_of_lt hz'.1
      have hz_upper : z ≤ (16 : ℝ) / 9 := le_of_lt hz'.2
      have hderiv :
          deriv f z =
            1 + z * Real.exp (z ^ 2 * a) * (9 / 8) - Real.exp z := by
        have hf_has :
            HasDerivAt f
              (1 + Real.exp (z ^ 2 * a) * (2 * z * a) - Real.exp z) z := by
          have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
            simpa using (hasDerivAt_pow 2 z)
          have hquad :
              HasDerivAt (fun t : ℝ => t ^ 2 * a) (2 * z * a) z :=
            hsq.mul_const a
          have hexp_quad :
              HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 * a))
                (Real.exp (z ^ 2 * a) * (2 * z * a)) z :=
            hquad.exp
          simpa [f, sub_eq_add_neg] using
            ((hasDerivAt_id' z).add hexp_quad).add ((Real.hasDerivAt_exp z).neg)
        have hf_deriv := hf_has.deriv
        calc
          deriv f z =
              1 + Real.exp (z ^ 2 * a) * (2 * z * a) - Real.exp z := hf_deriv
          _ = 1 + z * Real.exp (z ^ 2 * a) * (9 / 8) - Real.exp z := by
                dsimp [a]
                ring
      rw [hderiv]
      let t : ℝ := z - 1
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have ht_le_one : t ≤ 1 := by dsimp [t]; linarith
      have hupper_t :=
        Real.exp_bound' (x := t) (n := 2) ht0 ht_le_one (by norm_num)
      have hlower_quad :
          1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
              (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3 ≤
            Real.exp (z ^ 2 * a) := by
        have hnonneg : 0 ≤ z ^ 2 * a := by positivity
        exact one_add_self_add_sq_div_two_add_cube_div_six_le_exp hnonneg
      have hpoly :
          (11 / 4 : ℝ) *
              ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2))
            ≤ 1 + z * (9 / 8) *
                (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                  (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3) := by
        have hcert :
            0 ≤
              2187 * t ^ 7 + 15309 * t ^ 6 + 57591 * t ^ 5 +
                134865 * t ^ 4 + 234657 * t ^ 3 + 151815 * t ^ 2 +
                  91549 * t + 14363 := by
          positivity
        have hrewrite :
            (1 + z * (9 / 8) *
                (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                  (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3)) -
              ((11 / 4 : ℝ) *
                ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                  t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2))) =
              (2187 * t ^ 7 + 15309 * t ^ 6 + 57591 * t ^ 5 +
                134865 * t ^ 4 + 234657 * t ^ 3 + 151815 * t ^ 2 +
                  91549 * t + 14363) / 65536 := by
          dsimp [a, t]
          norm_num [Finset.sum_range_succ, pow_succ]
          ring
        have hdiff_nonneg :
            0 ≤
              (1 + z * (9 / 8) *
                (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                  (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3)) -
              ((11 / 4 : ℝ) *
                ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                  t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2))) := by
          rw [hrewrite]
          positivity
        linarith
      have hexp_z_le :
          Real.exp z ≤
            (11 / 4 : ℝ) *
              ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) := by
        have hz_eq : z = 1 + t := by dsimp [t]; ring
        calc
          Real.exp z = Real.exp (1 : ℝ) * Real.exp t := by
                rw [hz_eq, Real.exp_add]
          _ ≤ (11 / 4 : ℝ) *
              ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) := by
                exact mul_le_mul hexp_one_le hupper_t (Real.exp_nonneg t) (by norm_num)
      have hscaled :
          z * (9 / 8) *
              (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3)
            ≤ z * (9 / 8) * Real.exp (z ^ 2 * a) := by
        exact mul_le_mul_of_nonneg_left hlower_quad (by positivity)
      nlinarith [hexp_z_le, hpoly, hscaled]
  have hbase : 0 ≤ f 1 := by
    have hnonneg : 0 ≤ (9 / 16 : ℝ) := by norm_num
    have hlow :
        1 + (9 / 16 : ℝ) + (1 / 2 : ℝ) * (9 / 16 : ℝ) ^ 2 +
            (1 / 6 : ℝ) * (9 / 16 : ℝ) ^ 3 ≤
          Real.exp (9 / 16 : ℝ) :=
      one_add_self_add_sq_div_two_add_cube_div_six_le_exp hnonneg
    have hval : f 1 = 1 + Real.exp (9 / 16) - Real.exp 1 := by
      simp [f, a]
    rw [hval]
    norm_num at hlow ⊢
    linarith
  have hy_mem : y ∈ Set.Icc (1 : ℝ) (16 / 9) := ⟨hy1, le_of_lt hy_upper⟩
  have hle := hmono (by norm_num) hy_mem hy1
  have hf_nonneg : 0 ≤ f y := hbase.trans hle
  dsimp [f, a] at hf_nonneg
  have hquad_eq : y ^ 2 * (9 / 16 : ℝ) = 9 * y ^ 2 / 16 := by ring
  rw [hquad_eq] at hf_nonneg
  nlinarith

/-- Scalar exponential domination from Lan Lemma 4.1's proof.

The PDF proof of Lemma 4.1 uses the sharper moment inequality
`exp x <= x + exp (9*x^2/16)` for the small-parameter branch.  This private
scalar leaf is deliberately isolated from the probability model; it is pure
real analysis and is consumed by the one-step conditional-MGF adapter below. -/
theorem exp_le_self_add_exp_nine_mul_sq_div_sixteen (x : ℝ) :
    Real.exp x ≤ x + Real.exp (9 * x ^ 2 / 16) := by
  -- Source: FOML PDF, Lemma 4.1 proof, line immediately after defining
  -- `ζbar_t`.  The unbounded tails are elementary; the remaining bounded
  -- interval is a pure scalar calculus/Taylor comparison.
  have hbounded :
      ∀ y : ℝ, 0 ≤ y → y < (16 : ℝ) / 9 →
        Real.exp y ≤ y + Real.exp (9 * y ^ 2 / 16) ∧
          Real.exp (-y) + y ≤ Real.exp (9 * y ^ 2 / 16) := by
    intro y hy0 hy_upper
    let a : ℝ := 9 / 16
    have ha_nonneg : 0 ≤ a := by norm_num [a]
    have hquad_nonneg : 0 ≤ a * y ^ 2 := by positivity
    have hlower_quad :
        1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 ≤
          Real.exp (a * y ^ 2) := by
      exact one_add_self_add_sq_div_two_le_exp hquad_nonneg
    have hlower_cubic :
        1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 +
            (1 / 6 : ℝ) * (a * y ^ 2) ^ 3 ≤
          Real.exp (a * y ^ 2) := by
      exact one_add_self_add_sq_div_two_add_cube_div_six_le_exp hquad_nonneg
    constructor
    · -- Remaining bounded positive interval leaf.  The negative half below is
      -- now proved from the Taylor truncation helpers; this is the only scalar
      -- calculus/Taylor comparison left in the Lemma 4.1 adapter.
      by_cases hy1 : y ≤ 1
      · exact exp_pos_small_branch_le_self_add_exp_nine_mul_sq_div_sixteen hy0 hy1
      · have hy1' : 1 ≤ y := le_of_not_ge hy1
        exact exp_pos_mid_branch_le_self_add_exp_nine_mul_sq_div_sixteen hy1' hy_upper
    · by_cases hy1 : y ≤ 1
      · have hy_abs : |(-y : ℝ)| ≤ 1 := by
          rw [abs_neg, abs_of_nonneg hy0]
          exact hy1
        have hupper :=
          Real.exp_bound (x := -y) (n := 4) hy_abs (by norm_num)
        have hupper_exp :
            Real.exp (-y) ≤
              (∑ m ∈ Finset.range 4, (-y) ^ m / (m.factorial : ℝ)) +
                y ^ 4 * ((5 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) := by
          have habs_pow : |(-y : ℝ)| ^ 4 = y ^ 4 := by
            rw [abs_neg, abs_of_nonneg hy0]
          have hleft := (abs_sub_le_iff.mp hupper).1
          rw [habs_pow] at hleft
          simpa [Nat.succ_eq_add_one] using sub_le_iff_le_add'.mp hleft
        have hpoly :
            (∑ m ∈ Finset.range 4, (-y) ^ m / (m.factorial : ℝ)) +
                y ^ 4 * ((5 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) + y
              ≤ 1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := by
          have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
          have hy3_nonneg : 0 ≤ y ^ 3 := by positivity
          norm_num [a, Finset.sum_range_succ, pow_succ]
          nlinarith [hy_sq_nonneg, hy3_nonneg]
        calc
          Real.exp (-y) + y
              ≤ (∑ m ∈ Finset.range 4, (-y) ^ m / (m.factorial : ℝ)) +
                  y ^ 4 * ((5 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) + y := by
                linarith
          _ ≤ 1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := hpoly
          _ ≤ Real.exp (a * y ^ 2) := hlower_quad
          _ = Real.exp (9 * y ^ 2 / 16) := by
                congr 1
                dsimp [a]
                ring
      · have hy1' : 1 ≤ y := le_of_not_ge hy1
        have hexp_neg_le_half : Real.exp (-y) ≤ 1 / 2 := by
          have hle : -y ≤ -(1 : ℝ) := by linarith
          have h_exp_le : Real.exp (-y) ≤ Real.exp (-(1 : ℝ)) :=
            Real.exp_le_exp.mpr hle
          have htwo : (2 : ℝ) ≤ Real.exp 1 := by
            linarith [Real.add_one_le_exp (1 : ℝ)]
          have hhalf : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
            have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
            simpa [Real.exp_neg] using h
          exact h_exp_le.trans hhalf
        have hpoly :
            y + 1 / 2 ≤ 1 + a * y ^ 2 := by
          dsimp [a]
          nlinarith [sq_nonneg (3 * y - 8 / 3)]
        calc
          Real.exp (-y) + y ≤ 1 / 2 + y := by linarith
          _ = y + 1 / 2 := by ring
          _ ≤ 1 + a * y ^ 2 := hpoly
          _ ≤ Real.exp (a * y ^ 2) := by
                have hbase :
                    1 + a * y ^ 2 ≤
                      1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := by
                  have hs : 0 ≤ (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := by positivity
                  linarith
                exact hbase.trans hlower_quad
          _ = Real.exp (9 * y ^ 2 / 16) := by
                congr 1
                dsimp [a]
                ring
  by_cases hx0 : 0 ≤ x
  · by_cases hxlarge : (16 : ℝ) / 9 ≤ x
    · have hx_le_quad : x ≤ 9 * x ^ 2 / 16 := by nlinarith
      calc
        Real.exp x ≤ Real.exp (9 * x ^ 2 / 16) :=
          Real.exp_le_exp.mpr hx_le_quad
        _ ≤ x + Real.exp (9 * x ^ 2 / 16) :=
          le_add_of_nonneg_left hx0
    · have hx_upper : x < (16 : ℝ) / 9 := lt_of_not_ge hxlarge
      exact (hbounded x hx0 hx_upper).1
  · let y : ℝ := -x
    have hy0 : 0 ≤ y := by dsimp [y]; linarith
    have hx_eq : x = -y := by dsimp [y]; ring
    by_cases hylarge : (16 : ℝ) / 9 ≤ y
    · have hy_le_quad : y ≤ 9 * y ^ 2 / 16 := by nlinarith
      have htail : y + 1 ≤ Real.exp (9 * y ^ 2 / 16) := by
        have hadd := Real.add_one_le_exp (9 * y ^ 2 / 16)
        nlinarith
      have hexp_neg_le_one : Real.exp (-y) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      rw [hx_eq]
      have hsquare : (-y) ^ 2 = y ^ 2 := by ring
      rw [hsquare]
      nlinarith
    · have hy_upper : y < (16 : ℝ) / 9 := lt_of_not_ge hylarge
      have h := (hbounded y hy0 hy_upper).2
      rw [hx_eq]
      have hsquare : (-y) ^ 2 = y ^ 2 := by ring
      rw [hsquare]
      nlinarith

/-- Weighted one-step conditional-MGF assembly for flattened Lemma 4.1 terms.

The finite recurrence works with already weighted increments.  This adapter
starts from an unweighted martingale difference `zeta`, transports the
conditional mean-zero hypothesis through multiplication by the deterministic
coefficient, and then invokes
`condExp_exp_linear_le_of_pointwise_quadratic_domination` for the weighted
increment.  The square-exponential hypothesis is intentionally stated in the
weighted scale; the remaining SGS-specific algebra is exactly to rewrite
`(coeff * zeta)^2 / (coeff^2 * scale)` to the source light-tail scale on every
nonzero coefficient, with the zero-coefficient branch handled separately. -/
theorem weighted_condExp_exp_linear_le_of_pointwise_quadratic_domination
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {mSub : MeasurableSpace Ω} {ζ : Ω → ℝ} {varianceTerm ν coeff C B : ℝ}
    (hζ_int : Integrable ζ μ)
    (hexp_linear_int :
      Integrable (fun ω => Real.exp (ν * (coeff * ζ ω))) μ)
    (hexp_sq_int :
      Integrable (fun ω => Real.exp ((coeff * ζ ω) ^ 2 / varianceTerm)) μ)
    (hpoint :
      (fun ω => Real.exp (ν * (coeff * ζ ω))) ≤ᵐ[μ]
        fun ω =>
          ν * (coeff * ζ ω) +
            C * Real.exp ((coeff * ζ ω) ^ 2 / varianceTerm))
    (hcond_zero : μ[ζ | mSub] =ᵐ[μ] 0)
    (hcond_light_weighted :
      μ[(fun ω => Real.exp ((coeff * ζ ω) ^ 2 / varianceTerm)) | mSub] ≤ᵐ[μ]
        fun _ => Real.exp 1)
    (hC_nonneg : 0 ≤ C)
    (hC_bound : C * Real.exp 1 ≤ B) :
    μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ≤ᵐ[μ] fun _ => B := by
  classical
  let Z : Ω → ℝ := fun ω => coeff * ζ ω
  have hZ_int : Integrable Z μ := by
    simpa [Z] using hζ_int.const_mul coeff
  have hZ_cond_zero : μ[Z | mSub] =ᵐ[μ] 0 := by
    have hsmul :
        μ[(fun ω => coeff * ζ ω) | mSub] =ᵐ[μ]
          fun ω => coeff * μ[ζ | mSub] ω := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (MeasureTheory.condExp_smul
          (μ := μ) (c := coeff) (f := ζ) (m := mSub))
    filter_upwards [hsmul, hcond_zero] with ω hsmulω hzeroω
    have hzero_scalar : μ[ζ | mSub] ω = 0 := by simpa using hzeroω
    calc
      μ[Z | mSub] ω = μ[(fun ω => coeff * ζ ω) | mSub] ω := by rfl
      _ = coeff * μ[ζ | mSub] ω := hsmulω
      _ = 0 := by rw [hzero_scalar, mul_zero]
      _ = (0 : Ω → ℝ) ω := by rfl
  let Q : Ω → ℝ := fun ω => Real.exp (Z ω ^ 2 / varianceTerm)
  let Combo : Ω → ℝ := fun ω => ν * Z ω + C * Q ω
  have hνZ_int : Integrable (fun ω => ν * Z ω) μ := hZ_int.const_mul ν
  have hCQ_int : Integrable (fun ω => C * Q ω) μ := by
    simpa [Q, Z] using hexp_sq_int.const_mul C
  have hcombo_int : Integrable Combo μ := hνZ_int.add hCQ_int
  have hmono :
      μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ≤ᵐ[μ] μ[Combo | mSub] := by
    exact MeasureTheory.condExp_mono
      (m := mSub)
      (by simpa [Z] using hexp_linear_int)
      hcombo_int
      (by simpa [Combo, Q, Z] using hpoint)
  have hνZ_cond :
      μ[(fun ω => ν * Z ω) | mSub] =ᵐ[μ]
        fun ω => ν * μ[Z | mSub] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul
        (μ := μ) (c := ν) (f := Z) (m := mSub))
  have hCQ_cond :
      μ[(fun ω => C * Q ω) | mSub] =ᵐ[μ]
        fun ω => C * μ[Q | mSub] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (MeasureTheory.condExp_smul
        (μ := μ) (c := C) (f := Q) (m := mSub))
  have hcombo_cond :
      μ[Combo | mSub] =ᵐ[μ]
        fun ω => ν * μ[Z | mSub] ω + C * μ[Q | mSub] ω := by
    have hadd :
        μ[(fun ω => ν * Z ω + C * Q ω) | mSub] =ᵐ[μ]
          μ[(fun ω => ν * Z ω) | mSub] + μ[(fun ω => C * Q ω) | mSub] :=
      MeasureTheory.condExp_add
        (μ := μ) (f := fun ω => ν * Z ω) (g := fun ω => C * Q ω)
        hνZ_int hCQ_int mSub
    filter_upwards [hadd, hνZ_cond, hCQ_cond] with ω haddω hνω hCω
    calc
      μ[Combo | mSub] ω =
          μ[(fun ω => ν * Z ω + C * Q ω) | mSub] ω := by rfl
      _ = (μ[(fun ω => ν * Z ω) | mSub] +
            μ[(fun ω => C * Q ω) | mSub]) ω := haddω
      _ = ν * μ[Z | mSub] ω + C * μ[Q | mSub] ω := by
            simp [hνω, hCω]
  filter_upwards [hmono, hcombo_cond, hZ_cond_zero, hcond_light_weighted] with
    ω hle hcomboω hzeroω hlightω
  have hzero_scalar : μ[Z | mSub] ω = 0 := by simpa using hzeroω
  calc
    μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ω
        = μ[(fun ω => Real.exp (ν * Z ω)) | mSub] ω := by rfl
    _ ≤ μ[Combo | mSub] ω := hle
    _ = ν * μ[Z | mSub] ω + C * μ[Q | mSub] ω := hcomboω
    _ = C * μ[Q | mSub] ω := by rw [hzero_scalar]; ring
    _ ≤ C * Real.exp 1 := by
          exact mul_le_mul_of_nonneg_left (by simpa [Q, Z] using hlightω) hC_nonneg
    _ ≤ B := hC_bound

/-- Route-local one-step conditional-MGF scale adapter for the SGS flattened
linear term.

This is the internal bridge between the source light-tail scale
`exp (ζ^2 / lightScale)` and the weighted finite martingale recurrence, whose
increment is `coeff * ζ`.  The zero-light-scale and zero-coefficient branches
are discharged without interpreting `ζ^2 / 0` as source mathematics.  The
positive-scale branch is split at the fractional-power Jensen threshold used in
Lan Lemma 4.1. -/
theorem theorem82_weighted_one_step_cond_mgf_scale_adapter
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {mSub : MeasurableSpace Ω} (hmSub : mSub ≤ mΩ)
    {ζ : Ω → ℝ} {lightScale ν coeff : ℝ}
    (hν_nonneg : 0 ≤ ν)
    (hζ_int : Integrable ζ μ)
    (hexp_linear_int :
      Integrable (fun ω => Real.exp (ν * (coeff * ζ ω))) μ)
    (hexp_sq_light_int :
      Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) μ)
    (hlightScale_nonneg : 0 ≤ lightScale)
    (hcond_zero : μ[ζ | mSub] =ᵐ[μ] 0)
    (hcond_light :
      μ[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) | mSub] ≤ᵐ[μ]
        fun _ => Real.exp 1)
    (hzero_lightScale : lightScale = 0 → ζ =ᵐ[μ] 0) :
    μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ≤ᵐ[μ]
      fun _ => Real.exp (3 * ν ^ 2 * (coeff ^ 2 * lightScale) / 4) := by
  classical
  by_cases hscale_pos : 0 < lightScale
  · by_cases hcoeff_zero : coeff = 0
    · have hpoint :
          (fun ω => Real.exp (ν * (coeff * ζ ω))) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
        filter_upwards with ω
        simp [hcoeff_zero]
      have hcond_le :
          μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ≤ᵐ[μ]
            μ[(fun _ : Ω => (1 : ℝ)) | mSub] :=
        MeasureTheory.condExp_mono
          (m := mSub) hexp_linear_int (integrable_const (1 : ℝ)) hpoint
      have hconst :
          μ[(fun _ : Ω => (1 : ℝ)) | mSub] = fun _ : Ω => (1 : ℝ) :=
        MeasureTheory.condExp_const (μ := μ) (m := mSub) hmSub (1 : ℝ)
      filter_upwards [hcond_le] with ω hω
      calc
        μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ω
            ≤ μ[(fun _ : Ω => (1 : ℝ)) | mSub] ω := hω
        _ = 1 := by rw [hconst]
        _ = Real.exp (3 * ν ^ 2 * (coeff ^ 2 * lightScale) / 4) := by
              simp [hcoeff_zero]
    · let α : ℝ := 9 * (ν * coeff) ^ 2 * lightScale / 16
      by_cases hsmall : α ≤ 1
      · -- Small-parameter branch: conditional Jensen for
        -- `Q = exp (ζ^2 / lightScale)` at exponent `α`.
        let Q : Ω → ℝ := fun ω => Real.exp (ζ ω ^ 2 / lightScale)
        have hα_nonneg : 0 ≤ α := by
          dsimp [α]
          positivity
        have hQ_int : Integrable Q μ := by
          simpa [Q] using hexp_sq_light_int
        have hQ_nonneg_point : ∀ ω, 0 ≤ Q ω := fun ω => Real.exp_nonneg _
        have hQ_nonneg_ae : 0 ≤ᵐ[μ] Q :=
          Filter.Eventually.of_forall hQ_nonneg_point
        have hQα_int : Integrable (fun ω => (Q ω) ^ α) μ :=
          @integrable_rpow_of_integrable_nonneg_of_exponent_le_one
            Ω mΩ μ _ Q α
            hα_nonneg hsmall hQ_int hQ_nonneg_point
        have hcond_Qα :
            μ[(fun ω => (Q ω) ^ α) | mSub] ≤ᵐ[μ] fun _ => Real.exp α :=
          condExp_rpow_le_exp_of_condExp_le_exp_one
            (mΩ := mΩ) (μ := μ) (mSub := mSub) hmSub hα_nonneg hsmall
            hQ_int hQα_int hQ_nonneg_ae
            (by simpa [Q] using hcond_light)
        have hZ_int : Integrable (fun ω => coeff * ζ ω) μ := by
          simpa using hζ_int.const_mul coeff
        have hpoint :
            (fun ω => Real.exp (ν * (coeff * ζ ω))) ≤ᵐ[μ]
              fun ω => ν * (coeff * ζ ω) + (Q ω) ^ α := by
          filter_upwards with ω
          have hscalar :=
            exp_le_self_add_exp_nine_mul_sq_div_sixteen
              (ν * (coeff * ζ ω))
          have hQpow :
              (Q ω) ^ α =
                Real.exp (9 * (ν * (coeff * ζ ω)) ^ 2 / 16) := by
            calc
              (Q ω) ^ α =
                  Real.exp ((ζ ω ^ 2 / lightScale) * α) := by
                    simpa [Q] using
                      (Real.exp_mul (ζ ω ^ 2 / lightScale) α).symm
              _ = Real.exp (9 * (ν * (coeff * ζ ω)) ^ 2 / 16) := by
                    congr 1
                    dsimp [α]
                    field_simp [hscale_pos.ne'] <;> ring
          simpa [hQpow] using hscalar
        have hmain :=
          @condExp_exp_linear_le_of_pointwise_linear_plus
            Ω mΩ μ _ mSub (fun ω => coeff * ζ ω)
            (fun ω => (Q ω) ^ α) ν (Real.exp α)
            hZ_int hexp_linear_int hQα_int hpoint
            (by
              have hsmul :
                  μ[(fun ω => coeff * ζ ω) | mSub] =ᵐ[μ]
                    fun ω => coeff * μ[ζ | mSub] ω := by
                simpa [Pi.smul_apply, smul_eq_mul] using
                  (MeasureTheory.condExp_smul
                    (μ := μ) (c := coeff) (f := ζ) (m := mSub))
              filter_upwards [hsmul, hcond_zero] with ω hsmulω hzeroω
              have hzero_scalar : μ[ζ | mSub] ω = 0 := by simpa using hzeroω
              calc
                μ[(fun ω => coeff * ζ ω) | mSub] ω
                    = coeff * μ[ζ | mSub] ω := hsmulω
                _ = 0 := by rw [hzero_scalar, mul_zero]
                _ = (0 : Ω → ℝ) ω := by rfl)
            hcond_Qα
        filter_upwards [hmain] with ω hω
        calc
          μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ω
              ≤ Real.exp α := hω
          _ ≤ Real.exp (3 * ν ^ 2 * (coeff ^ 2 * lightScale) / 4) := by
                apply Real.exp_le_exp.mpr
                dsimp [α]
                nlinarith [sq_nonneg (ν * coeff), hscale_pos.le]
      · -- Large-parameter branch from the source proof: use
        -- `λ x <= 3 λ^2/8 + 2 x^2/3`, then conditional Jensen at exponent
        -- `2/3` and the fact that the branch has
        -- `(ν*coeff)^2*lightScale >= 16/9`.
        let Q : Ω → ℝ := fun ω => Real.exp (ζ ω ^ 2 / lightScale)
        let θ : ℝ := (2 : ℝ) / 3
        let C : ℝ := Real.exp (3 * (ν * coeff) ^ 2 * lightScale / 8)
        have hα_gt : 1 < α := lt_of_not_ge hsmall
        have ht_lower : (16 : ℝ) / 9 ≤ (ν * coeff) ^ 2 * lightScale := by
          dsimp [α] at hα_gt
          nlinarith
        have hθ_nonneg : 0 ≤ θ := by norm_num [θ]
        have hθ_le_one : θ ≤ 1 := by norm_num [θ]
        have hQ_int : Integrable Q μ := by
          simpa [Q] using hexp_sq_light_int
        have hQ_nonneg_point : ∀ ω, 0 ≤ Q ω := fun ω => Real.exp_nonneg _
        have hQ_nonneg_ae : 0 ≤ᵐ[μ] Q :=
          Filter.Eventually.of_forall hQ_nonneg_point
        have hQθ_int : Integrable (fun ω => (Q ω) ^ θ) μ :=
          @integrable_rpow_of_integrable_nonneg_of_exponent_le_one
            Ω mΩ μ _ Q θ hθ_nonneg hθ_le_one hQ_int hQ_nonneg_point
        have hcond_Qθ :
            μ[(fun ω => (Q ω) ^ θ) | mSub] ≤ᵐ[μ] fun _ => Real.exp θ :=
          condExp_rpow_le_exp_of_condExp_le_exp_one
            (mΩ := mΩ) (μ := μ) (mSub := mSub) hmSub hθ_nonneg hθ_le_one
            hQ_int hQθ_int hQ_nonneg_ae
            (by simpa [Q] using hcond_light)
        have hpoint :
            (fun ω => Real.exp (ν * (coeff * ζ ω))) ≤ᵐ[μ]
              fun ω => C * (Q ω) ^ θ := by
          filter_upwards with ω
          have hyoung :
              ν * (coeff * ζ ω) ≤
                3 * (ν * coeff) ^ 2 * lightScale / 8 +
                  (2 / 3 : ℝ) * (ζ ω ^ 2 / lightScale) := by
            have hnonneg :
                0 ≤
                  3 * (ν * coeff) ^ 2 * lightScale / 8 +
                    (2 / 3 : ℝ) * (ζ ω ^ 2 / lightScale) -
                      ν * (coeff * ζ ω) := by
              have hmul :
                  0 ≤ lightScale *
                    (3 * (ν * coeff) ^ 2 * lightScale / 8 +
                      (2 / 3 : ℝ) * (ζ ω ^ 2 / lightScale) -
                        ν * (coeff * ζ ω)) := by
                field_simp [hscale_pos.ne']
                nlinarith [sq_nonneg (4 * ζ ω - 3 * (ν * coeff) * lightScale)]
              exact (mul_nonneg_iff_of_pos_left hscale_pos).mp hmul
            linarith
          have hQpow :
              (Q ω) ^ θ =
                Real.exp ((ζ ω ^ 2 / lightScale) * θ) := by
            simpa [Q] using (Real.exp_mul (ζ ω ^ 2 / lightScale) θ).symm
          calc
            Real.exp (ν * (coeff * ζ ω))
                ≤ Real.exp
                    (3 * (ν * coeff) ^ 2 * lightScale / 8 +
                      (2 / 3 : ℝ) * (ζ ω ^ 2 / lightScale)) :=
                  Real.exp_le_exp.mpr hyoung
            _ = C * (Q ω) ^ θ := by
                  rw [Real.exp_add, hQpow]
                  dsimp [C, θ]
                  ring
        have hcond_le :
            μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ≤ᵐ[μ]
              μ[(fun ω => C * (Q ω) ^ θ) | mSub] :=
          MeasureTheory.condExp_mono
            (m := mSub) hexp_linear_int (hQθ_int.const_mul C) hpoint
        have hC_cond :
            μ[(fun ω => C * (Q ω) ^ θ) | mSub] =ᵐ[μ]
              fun ω => C * μ[(fun ω => (Q ω) ^ θ) | mSub] ω := by
          simpa [Pi.smul_apply, smul_eq_mul] using
            (MeasureTheory.condExp_smul
              (μ := μ) (c := C) (f := fun ω => (Q ω) ^ θ) (m := mSub))
        filter_upwards [hcond_le, hC_cond, hcond_Qθ] with
          ω hle hCω hQω
        calc
          μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ω
              ≤ μ[(fun ω => C * (Q ω) ^ θ) | mSub] ω := hle
          _ = C * μ[(fun ω => (Q ω) ^ θ) | mSub] ω := hCω
          _ ≤ C * Real.exp θ := by
                exact mul_le_mul_of_nonneg_left hQω (le_of_lt (Real.exp_pos _))
          _ = Real.exp (3 * (ν * coeff) ^ 2 * lightScale / 8 + θ) := by
                dsimp [C]
                rw [Real.exp_add]
          _ ≤ Real.exp (3 * ν ^ 2 * (coeff ^ 2 * lightScale) / 4) := by
                apply Real.exp_le_exp.mpr
                dsimp [θ]
                have ht_rewrite :
                    (ν * coeff) ^ 2 * lightScale =
                      ν ^ 2 * (coeff ^ 2 * lightScale) := by ring
                nlinarith [ht_lower]
  · have hscale_zero : lightScale = 0 :=
      le_antisymm (le_of_not_gt hscale_pos) hlightScale_nonneg
    have hζ_zero : ζ =ᵐ[μ] 0 := hzero_lightScale hscale_zero
    have hpoint :
        (fun ω => Real.exp (ν * (coeff * ζ ω))) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
      filter_upwards [hζ_zero] with ω hζω
      simp [hζω]
    have hcond_le :
        μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ≤ᵐ[μ]
          μ[(fun _ : Ω => (1 : ℝ)) | mSub] :=
      MeasureTheory.condExp_mono
        (m := mSub) hexp_linear_int (integrable_const (1 : ℝ)) hpoint
    have hconst :
        μ[(fun _ : Ω => (1 : ℝ)) | mSub] = fun _ : Ω => (1 : ℝ) :=
      MeasureTheory.condExp_const (μ := μ) (m := mSub) hmSub (1 : ℝ)
    filter_upwards [hcond_le] with ω hω
    calc
      μ[(fun ω => Real.exp (ν * (coeff * ζ ω))) | mSub] ω
          ≤ μ[(fun _ : Ω => (1 : ℝ)) | mSub] ω := hω
      _ = 1 := by rw [hconst]
      _ = Real.exp (3 * ν ^ 2 * (coeff ^ 2 * lightScale) / 4) := by
            simp [hscale_zero]

/-- Finite-prefix exponential measurability for the ordered martingale
recurrence.

This is the Mathlib endpoint for the `hprefix_sm` leaf in Lan Lemma 4.1:
after the SGS adapter proves every earlier weighted increment is measurable
with respect to the current strict-past sigma-algebra, finite sums, scalar
multiplication, and `Real.exp` supply the strongly-measurable prefix factor
required by `finite_weighted_condExp_mgf_recurrence_step`. -/
theorem stronglyMeasurable_exp_prefix_sum_of_terms
    {Ω : Type*} [MeasurableSpace Ω] (mSub : MeasurableSpace Ω)
    (Z : ℕ → Ω → ℝ) (ν : ℝ) (j : ℕ)
    (hZ :
      ∀ r ∈ Finset.range j, Measurable[mSub] (Z r)) :
    StronglyMeasurable[mSub]
      (fun ω => Real.exp (ν * (Finset.range j).sum (fun r => Z r ω))) := by
  classical
  have hsum :
      Measurable[mSub] (fun ω => (Finset.range j).sum (fun r => Z r ω)) := by
    exact Finset.measurable_fun_sum (Finset.range j) (fun r hr => hZ r hr)
  have harg :
      Measurable[mSub] (fun ω => ν * (Finset.range j).sum (fun r => Z r ω)) :=
    measurable_const.mul hsum
  exact (Real.measurable_exp.comp harg).stronglyMeasurable

/-- Finite ordered conditional-MGF recurrence for weighted martingale increments.

The sequence `Z i` is already the weighted scalar increment.  For each current
index `i`, the exponential prefix over `range i` is assumed measurable with
respect to the corresponding past sigma-algebra, and the current exponential
increment has the one-step conditional MGF bound with deterministic variance
term `varianceTerm i`.  The conclusion is exactly the finite `hmgf` shape used
by `finite_weighted_condExp_light_tail_chernoff_bound_of_mgf`, but derived from
one-step conditional MGF bounds rather than assumed wholesale. -/
theorem finite_weighted_condExp_light_tail_mgf_recurrence
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (Z : ℕ → Ω → ℝ) (varianceTerm : ℕ → ℝ)
    (past : ℕ → MeasurableSpace Ω) (ν : ℝ) (hν_nonneg : 0 ≤ ν)
    (hpast_le :
      ∀ i, i < n → past i ≤ (by infer_instance : MeasurableSpace Ω))
    (hprefix_sm :
      ∀ i, i < n →
        StronglyMeasurable[past i]
          (fun ω => Real.exp (ν * (Finset.range i).sum (fun j => Z j ω))))
    (hprefix_int :
      ∀ i, i ≤ n →
        Integrable
          (fun ω => Real.exp (ν * (Finset.range i).sum (fun j => Z j ω))) μ)
    (hstep_int :
      ∀ i, i < n → Integrable (fun ω => Real.exp (ν * Z i ω)) μ)
    (hstep_cond_mgf :
      ∀ i, i < n →
        μ[(fun ω => Real.exp (ν * Z i ω)) | past i] ≤ᵐ[μ]
          fun _ => Real.exp (3 * ν ^ 2 * varianceTerm i / 4)) :
    Integrable
        (fun ω => Real.exp (ν * (Finset.range n).sum (fun j => Z j ω))) μ ∧
      (∫ ω, Real.exp (ν * (Finset.range n).sum (fun j => Z j ω)) ∂μ) ≤
        Real.exp (3 * ν ^ 2 * (Finset.range n).sum varianceTerm / 4) := by
  classical
  revert Z varianceTerm past ν
  induction n with
  | zero =>
      intro Z varianceTerm past ν hν_nonneg hpast_le hprefix_sm hprefix_int
        hstep_int hstep_cond_mgf
      refine ⟨hprefix_int 0 le_rfl, ?_⟩
      refine le_of_eq ?_
      calc
        (∫ ω, Real.exp (ν * (Finset.range 0).sum (fun j => Z j ω)) ∂μ)
            = ∫ _ω, (1 : ℝ) ∂μ := by
                simp
        _ = 1 := by
                simp [probReal_univ]
        _ = Real.exp (3 * ν ^ 2 * (Finset.range 0).sum varianceTerm / 4) := by
                simp
  | succ n ih =>
      intro Z varianceTerm past ν hν_nonneg hpast_le hprefix_sm hprefix_int
        hstep_int hstep_cond_mgf
      have hn_lt : n < n + 1 := Nat.lt_succ_self n
      have hprev :=
        ih Z varianceTerm past ν hν_nonneg
          (fun i hi => hpast_le i (Nat.lt_trans hi hn_lt))
          (fun i hi => hprefix_sm i (Nat.lt_trans hi hn_lt))
          (fun i hi => hprefix_int i (Nat.le_trans hi (Nat.le_succ n)))
          (fun i hi => hstep_int i (Nat.lt_trans hi hn_lt))
          (fun i hi => hstep_cond_mgf i (Nat.lt_trans hi hn_lt))
      let pref : Ω → ℝ :=
        fun ω => Real.exp (ν * (Finset.range n).sum (fun j => Z j ω))
      let step : Ω → ℝ := fun ω => Real.exp (ν * Z n ω)
      let C : ℝ := Real.exp (3 * ν ^ 2 * varianceTerm n / 4)
      have hfull_prod :
          (fun ω =>
              Real.exp (ν * (Finset.range (n + 1)).sum (fun j => Z j ω))) =ᵐ[μ]
            fun ω => pref ω * step ω := by
        exact Filter.Eventually.of_forall fun ω => by
          have hsum :
              (Finset.range (n + 1)).sum (fun j => Z j ω) =
                (Finset.range n).sum (fun j => Z j ω) + Z n ω := by
            rw [Finset.sum_range_succ]
          calc
            Real.exp (ν * (Finset.range (n + 1)).sum (fun j => Z j ω))
                = Real.exp (ν * (Finset.range n).sum (fun j => Z j ω) +
                    ν * Z n ω) := by
                    rw [hsum]
                    ring
            _ = pref ω * step ω := by
                    simp [pref, step, Real.exp_add]
      have hprod_int : Integrable (fun ω => pref ω * step ω) μ :=
        (hprefix_int (n + 1) le_rfl).congr hfull_prod
      have hprefix_nonneg : 0 ≤ᵐ[μ] pref :=
        Filter.Eventually.of_forall fun ω => Real.exp_nonneg _
      have hstep_bound :
          (∫ ω, pref ω * step ω ∂μ) ≤ C * ∫ ω, pref ω ∂μ := by
        exact
          finite_weighted_condExp_mgf_recurrence_step
            (μ := μ) (m := past n) (pref := pref) (step := step) (C := C)
            (hpast_le n hn_lt)
            (by simpa [pref] using hprefix_sm n hn_lt)
            (by simpa [pref] using hprefix_int n (Nat.le_succ n))
            (by simpa [step] using hstep_int n hn_lt)
            hprod_int hprefix_nonneg
            (by simpa [step, C] using hstep_cond_mgf n hn_lt)
      refine ⟨hprefix_int (n + 1) le_rfl, ?_⟩
      calc
        (∫ ω, Real.exp (ν * (Finset.range (n + 1)).sum (fun j => Z j ω)) ∂μ)
            = ∫ ω, pref ω * step ω ∂μ := by
                exact integral_congr_ae hfull_prod
        _ ≤ C * ∫ ω, pref ω ∂μ := hstep_bound
        _ ≤ C * Real.exp (3 * ν ^ 2 * (Finset.range n).sum varianceTerm / 4) := by
                exact mul_le_mul_of_nonneg_left hprev.2 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (3 * ν ^ 2 *
              (Finset.range (n + 1)).sum varianceTerm / 4) := by
                have hsum :
                    (Finset.range (n + 1)).sum varianceTerm =
                      (Finset.range n).sum varianceTerm + varianceTerm n := by
                  rw [Finset.sum_range_succ]
                rw [hsum]
                have harg :
                    3 * ν ^ 2 *
                        ((Finset.range n).sum varianceTerm + varianceTerm n) / 4 =
                      3 * ν ^ 2 * (Finset.range n).sum varianceTerm / 4 +
                        3 * ν ^ 2 * varianceTerm n / 4 := by
                  ring
                rw [harg, Real.exp_add]
                simp [C, mul_comm, mul_left_comm, mul_assoc]

/-- Finite ordered conditional-MGF recurrence with internal prefix integrability.

This is the non-circular recurrence needed by the Eq. (8.1.70) bridge.  The
older recurrence above assumes integrability of every exponential prefix,
including the full prefix it is meant to bound.  Here prefix integrability is
proved inside the induction: to justify the product at Chernoff parameter `ν`,
the induction hypothesis is also used at `2 * ν`, and the pointwise inequality
`xy <= (x^2 + y^2) / 2` dominates the product of the two exponential factors. -/
theorem finite_weighted_condExp_light_tail_mgf_recurrence_internal_integrability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (Z : ℕ → Ω → ℝ) (varianceTerm : ℕ → ℝ)
    (past : ℕ → MeasurableSpace Ω)
    (hpast_le :
      ∀ i, i < n → past i ≤ (by infer_instance : MeasurableSpace Ω))
    (hprefix_sm :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        StronglyMeasurable[past i]
          (fun ω => Real.exp (ν * (Finset.range i).sum (fun j => Z j ω))))
    (hstep_int :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        Integrable (fun ω => Real.exp (ν * Z i ω)) μ)
    (hstep_cond_mgf :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        μ[(fun ω => Real.exp (ν * Z i ω)) | past i] ≤ᵐ[μ]
          fun _ => Real.exp (3 * ν ^ 2 * varianceTerm i / 4)) :
    ∀ ν : ℝ, 0 ≤ ν →
      Integrable
          (fun ω => Real.exp (ν * (Finset.range n).sum (fun j => Z j ω))) μ ∧
        (∫ ω, Real.exp (ν * (Finset.range n).sum (fun j => Z j ω)) ∂μ) ≤
          Real.exp (3 * ν ^ 2 * (Finset.range n).sum varianceTerm / 4) := by
  classical
  revert Z varianceTerm past
  induction n with
  | zero =>
      intro Z varianceTerm past hpast_le hprefix_sm hstep_int hstep_cond_mgf
        ν hν_nonneg
      refine ⟨?_, ?_⟩
      · simpa using (integrable_const (c := (1 : ℝ)))
      · refine le_of_eq ?_
        calc
          (∫ ω, Real.exp (ν * (Finset.range 0).sum (fun j => Z j ω)) ∂μ)
              = ∫ _ω, (1 : ℝ) ∂μ := by
                  simp
          _ = 1 := by
                  simp [probReal_univ]
          _ = Real.exp (3 * ν ^ 2 * (Finset.range 0).sum varianceTerm / 4) := by
                  simp
  | succ n ih =>
      intro Z varianceTerm past hpast_le hprefix_sm hstep_int hstep_cond_mgf
        ν hν_nonneg
      have hn_lt : n < n + 1 := Nat.lt_succ_self n
      have hprev :=
        ih Z varianceTerm past
          (fun i hi => hpast_le i (Nat.lt_trans hi hn_lt))
          (fun ν hν i hi => hprefix_sm ν hν i (Nat.lt_trans hi hn_lt))
          (fun ν hν i hi => hstep_int ν hν i (Nat.lt_trans hi hn_lt))
          (fun ν hν i hi => hstep_cond_mgf ν hν i (Nat.lt_trans hi hn_lt))
          ν hν_nonneg
      have htwoν_nonneg : 0 ≤ 2 * ν := by positivity
      have hprev_two :=
        ih Z varianceTerm past
          (fun i hi => hpast_le i (Nat.lt_trans hi hn_lt))
          (fun ν hν i hi => hprefix_sm ν hν i (Nat.lt_trans hi hn_lt))
          (fun ν hν i hi => hstep_int ν hν i (Nat.lt_trans hi hn_lt))
          (fun ν hν i hi => hstep_cond_mgf ν hν i (Nat.lt_trans hi hn_lt))
          (2 * ν) htwoν_nonneg
      let pref : Ω → ℝ :=
        fun ω => Real.exp (ν * (Finset.range n).sum (fun j => Z j ω))
      let step : Ω → ℝ := fun ω => Real.exp (ν * Z n ω)
      let pref2 : Ω → ℝ :=
        fun ω => Real.exp ((2 * ν) * (Finset.range n).sum (fun j => Z j ω))
      let step2 : Ω → ℝ := fun ω => Real.exp ((2 * ν) * Z n ω)
      let C : ℝ := Real.exp (3 * ν ^ 2 * varianceTerm n / 4)
      have hfull_prod :
          (fun ω =>
              Real.exp (ν * (Finset.range (n + 1)).sum (fun j => Z j ω))) =ᵐ[μ]
            fun ω => pref ω * step ω := by
        exact Filter.Eventually.of_forall fun ω => by
          have hsum :
              (Finset.range (n + 1)).sum (fun j => Z j ω) =
                (Finset.range n).sum (fun j => Z j ω) + Z n ω := by
            rw [Finset.sum_range_succ]
          calc
            Real.exp (ν * (Finset.range (n + 1)).sum (fun j => Z j ω))
                = Real.exp (ν * (Finset.range n).sum (fun j => Z j ω) +
                    ν * Z n ω) := by
                    rw [hsum]
                    ring
            _ = pref ω * step ω := by
                    simp [pref, step, Real.exp_add]
      have hpref_sm_full :
          StronglyMeasurable
            (fun ω => Real.exp (ν * (Finset.range n).sum (fun j => Z j ω))) :=
        (hprefix_sm ν hν_nonneg n hn_lt).mono (hpast_le n hn_lt)
      have hprod_aesm :
          AEStronglyMeasurable (fun ω => pref ω * step ω) μ := by
        exact hpref_sm_full.aestronglyMeasurable.mul
          ((hstep_int ν hν_nonneg n hn_lt).aestronglyMeasurable)
      have hprod_bound_int :
          Integrable (fun ω => (1 / 2 : ℝ) * pref2 ω + (1 / 2 : ℝ) * step2 ω) μ := by
        exact (hprev_two.1.const_mul (1 / 2 : ℝ)).add
          ((hstep_int (2 * ν) htwoν_nonneg n hn_lt).const_mul (1 / 2 : ℝ))
      have hprod_bound :
          (fun ω => ‖pref ω * step ω‖) ≤ᵐ[μ]
            fun ω => (1 / 2 : ℝ) * pref2 ω + (1 / 2 : ℝ) * step2 ω := by
        filter_upwards with ω
        have hpref_nonneg : 0 ≤ pref ω := Real.exp_nonneg _
        have hstep_nonneg : 0 ≤ step ω := Real.exp_nonneg _
        have hpref_sq : pref ω ^ 2 = pref2 ω := by
          calc
            pref ω ^ 2 = Real.exp (2 * (ν *
                (Finset.range n).sum (fun j => Z j ω))) := by
                  rw [sq, ← Real.exp_add]
                  ring
            _ = pref2 ω := by
                  congr 1
                  ring
        have hstep_sq : step ω ^ 2 = step2 ω := by
          calc
            step ω ^ 2 = Real.exp (2 * (ν * Z n ω)) := by
                  rw [sq, ← Real.exp_add]
                  ring
            _ = step2 ω := by
                  congr 1
                  ring
        have hxy :
            pref ω * step ω ≤ (pref ω ^ 2 + step ω ^ 2) / 2 := by
          nlinarith [sq_nonneg (pref ω - step ω)]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpref_nonneg hstep_nonneg)]
        calc
          pref ω * step ω ≤ (pref ω ^ 2 + step ω ^ 2) / 2 := hxy
          _ = (1 / 2 : ℝ) * pref2 ω + (1 / 2 : ℝ) * step2 ω := by
                rw [hpref_sq, hstep_sq]
                ring
      have hprod_int : Integrable (fun ω => pref ω * step ω) μ :=
        Integrable.mono' hprod_bound_int hprod_aesm hprod_bound
      have hprefix_nonneg : 0 ≤ᵐ[μ] pref :=
        Filter.Eventually.of_forall fun ω => Real.exp_nonneg _
      have hstep_bound :
          (∫ ω, pref ω * step ω ∂μ) ≤ C * ∫ ω, pref ω ∂μ := by
        exact
          finite_weighted_condExp_mgf_recurrence_step
            (μ := μ) (m := past n) (pref := pref) (step := step) (C := C)
            (hpast_le n hn_lt)
            (by simpa [pref] using hprefix_sm ν hν_nonneg n hn_lt)
            (by simpa [pref] using hprev.1)
            (by simpa [step] using hstep_int ν hν_nonneg n hn_lt)
            hprod_int hprefix_nonneg
            (by simpa [step, C] using hstep_cond_mgf ν hν_nonneg n hn_lt)
      refine ⟨hprod_int.congr hfull_prod.symm, ?_⟩
      calc
        (∫ ω, Real.exp (ν * (Finset.range (n + 1)).sum (fun j => Z j ω)) ∂μ)
            = ∫ ω, pref ω * step ω ∂μ := by
                exact integral_congr_ae hfull_prod
        _ ≤ C * ∫ ω, pref ω ∂μ := hstep_bound
        _ ≤ C * Real.exp (3 * ν ^ 2 * (Finset.range n).sum varianceTerm / 4) := by
                exact mul_le_mul_of_nonneg_left hprev.2 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (3 * ν ^ 2 *
              (Finset.range (n + 1)).sum varianceTerm / 4) := by
                have hsum :
                    (Finset.range (n + 1)).sum varianceTerm =
                      (Finset.range n).sum varianceTerm + varianceTerm n := by
                  rw [Finset.sum_range_succ]
                rw [hsum]
                have harg :
                    3 * ν ^ 2 *
                        ((Finset.range n).sum varianceTerm + varianceTerm n) / 4 =
                      3 * ν ^ 2 * (Finset.range n).sum varianceTerm / 4 +
                        3 * ν ^ 2 * varianceTerm n / 4 := by
                  ring
                rw [harg, Real.exp_add]
                simp [C, mul_comm, mul_left_comm, mul_assoc]

/-- Finite ordered Chernoff bound from one-step conditional MGF bounds.

This packages the newly proved recurrence with the existing Chernoff optimizer.
It is the route-local replacement for assuming the finite `hmgf` premise:
downstream SGS code may supply prefix adaptedness, integrability, and one-step
conditional MGF estimates for the flattened ordered increments. -/
theorem finite_weighted_condExp_light_tail_chernoff_bound_of_cond_mgf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (Z : ℕ → Ω → ℝ) (varianceTerm : ℕ → ℝ)
    (past : ℕ → MeasurableSpace Ω) (variance lambda : ℝ)
    (hlambda : 0 < lambda) (hvariance_pos : 0 < variance)
    (hvariance :
      variance = (Finset.range n).sum varianceTerm)
    (hpast_le :
      ∀ i, i < n → past i ≤ (by infer_instance : MeasurableSpace Ω))
    (hprefix_sm :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        StronglyMeasurable[past i]
          (fun ω => Real.exp (ν * (Finset.range i).sum (fun j => Z j ω))))
    (hstep_int :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        Integrable (fun ω => Real.exp (ν * Z i ω)) μ)
    (hstep_cond_mgf :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        μ[(fun ω => Real.exp (ν * Z i ω)) | past i] ≤ᵐ[μ]
          fun _ => Real.exp (3 * ν ^ 2 * varianceTerm i / 4)) :
    μ {ω |
        (Finset.range n).sum (fun i => Z i ω) ≥
          lambda * Real.sqrt variance} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
  classical
  let idx : Finset ℕ := Finset.range n
  let ζ : ℕ → Ω → ℝ := Z
  let coeff : ℕ → ℝ := fun _ => 1
  have hmgf :
      ∀ ν : ℝ, 0 ≤ ν →
        Integrable
          (fun ω => Real.exp (ν * idx.sum (fun a => coeff a * ζ a ω))) μ ∧
        (∫ ω, Real.exp (ν * idx.sum (fun a => coeff a * ζ a ω)) ∂μ) ≤
          Real.exp (3 * ν ^ 2 * variance / 4) := by
    intro ν hν
    have hrec :=
      finite_weighted_condExp_light_tail_mgf_recurrence_internal_integrability
        (μ := μ) n Z varianceTerm past hpast_le hprefix_sm hstep_int
        hstep_cond_mgf ν hν
    simpa [idx, ζ, coeff, hvariance] using hrec
  have htail :=
    finite_weighted_condExp_light_tail_chernoff_bound_of_mgf
      (μ := μ) (idx := idx) (ζ := ζ) (coeff := coeff)
      (variance := variance) (lambda := lambda)
      hlambda hvariance_pos hmgf
  simpa [idx, ζ, coeff] using htail

/-- Strict-event form of the finite ordered Chernoff bound.

Lan Lemma 4.1 and Eq. (8.1.70) use a strict deviation event.  The existing
finite Chernoff optimizer proves the slightly larger non-strict event, so the
source strict event follows by `measure_mono`; this avoids using the false
zero-variance non-strict event as the source bridge. -/
theorem finite_weighted_condExp_light_tail_chernoff_bound_gt_of_cond_mgf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (Z : ℕ → Ω → ℝ) (varianceTerm : ℕ → ℝ)
    (past : ℕ → MeasurableSpace Ω) (variance lambda : ℝ)
    (hlambda : 0 < lambda) (hvariance_pos : 0 < variance)
    (hvariance :
      variance = (Finset.range n).sum varianceTerm)
    (hpast_le :
      ∀ i, i < n → past i ≤ (by infer_instance : MeasurableSpace Ω))
    (hprefix_sm :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        StronglyMeasurable[past i]
          (fun ω => Real.exp (ν * (Finset.range i).sum (fun j => Z j ω))))
    (hstep_int :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        Integrable (fun ω => Real.exp (ν * Z i ω)) μ)
    (hstep_cond_mgf :
      ∀ ν : ℝ, 0 ≤ ν → ∀ i, i < n →
        μ[(fun ω => Real.exp (ν * Z i ω)) | past i] ≤ᵐ[μ]
          fun _ => Real.exp (3 * ν ^ 2 * varianceTerm i / 4)) :
    μ {ω |
        (Finset.range n).sum (fun i => Z i ω) >
          lambda * Real.sqrt variance} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
  classical
  have hge :
      μ {ω |
          (Finset.range n).sum (fun i => Z i ω) ≥
            lambda * Real.sqrt variance} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) :=
    finite_weighted_condExp_light_tail_chernoff_bound_of_cond_mgf
      (μ := μ) (n := n) (Z := Z) (varianceTerm := varianceTerm)
      (past := past) (variance := variance) (lambda := lambda)
      hlambda hvariance_pos hvariance hpast_le hprefix_sm hstep_int
      hstep_cond_mgf
  exact
    (measure_mono (by
      intro ω hω
      change (Finset.range n).sum (fun i => Z i ω) ≥
        lambda * Real.sqrt variance
      exact le_of_lt hω)).trans hge

/-- Deterministic zero-variance branch for the strict finite Lemma 4.1 event.

This is the source-safe branch missing from the non-strict route: when the
flattened increments are a.e. zero and the variance parameter is nonpositive,
the strict event has probability zero.  No non-strict event is concluded here,
matching Lan Lemma 4.1's strict `>` display. -/
theorem finite_strict_tail_zero_of_ae_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n : ℕ) (Z : ℕ → Ω → ℝ) (variance lambda : ℝ)
    (_hlambda : 0 < lambda) (hvariance_nonpos : variance ≤ 0)
    (hZ_zero : ∀ j, j < n → Z j =ᵐ[μ] 0) :
    μ {ω | (Finset.range n).sum (fun j => Z j ω) >
          lambda * Real.sqrt variance} = 0 := by
  classical
  have hsum_zero :
      (fun ω => (Finset.range n).sum (fun j => Z j ω)) =ᵐ[μ]
        fun _ => (0 : ℝ) := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hprev :
            (fun ω => (Finset.range n).sum (fun j => Z j ω)) =ᵐ[μ]
              fun _ => (0 : ℝ) := by
          exact ih (fun j hj => hZ_zero j (Nat.lt_trans hj (Nat.lt_succ_self n)))
        have hlast : Z n =ᵐ[μ] 0 := hZ_zero n (Nat.lt_succ_self n)
        filter_upwards [hprev, hlast] with ω hprevω hlastω
        simp [Finset.sum_range_succ, hprevω, hlastω]
  have hsqrt_zero : Real.sqrt variance = 0 :=
    Real.sqrt_eq_zero_of_nonpos hvariance_nonpos
  have hnot_bad :
      ∀ᵐ ω ∂μ,
        ω ∉ {ω | (Finset.range n).sum (fun j => Z j ω) >
          lambda * Real.sqrt variance} := by
    filter_upwards [hsum_zero] with ω hsumω
    simp [hsumω, hsqrt_zero]
  simpa using
    ((MeasureTheory.ae_iff (μ := μ)
      (p := fun ω =>
        ω ∉ {ω | (Finset.range n).sum (fun j => Z j ω) >
          lambda * Real.sqrt variance})).mp hnot_bad)

/-- Row-major finite flattening of the SGS coordinates used in Lan Eq. (8.1.70).

No SOptLib match: searched sample-prefix/filtration and tail-probability
helpers; those provide independence and martingale inequalities for an already
ordered sequence, while this private definition is only the paper's concrete
lexicographic enumeration of `(k,i)` coordinates over `k < N`, `i < T_k`.
It replaces the opaque `Finset.toList.get` decoder in the Lemma 4.1 bridge. -/
def sgsLexFlatIndexList (N : PositiveTime) (T : PositiveTime → ℕ) :
    List (Σ _k : ℕ, ℕ) :=
  (List.range N.1).flatMap (fun k =>
    (List.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).map
      (fun i => (⟨k, i⟩ : Σ _k : ℕ, ℕ)))

/-- The row-major SGS flattening is strictly lexicographically ordered.

This is a private list-order fact for the Lemma 4.1 adapter.  It proves the
paper's intended order for the concrete enumerator, leaving the probabilistic
content to the martingale bridge. -/
theorem sgsLexFlatIndexList_pairwise_lex
    (N : PositiveTime) (T : PositiveTime → ℕ) :
    List.Pairwise
      (fun a b : Σ _k : ℕ, ℕ =>
        a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))
      (sgsLexFlatIndexList N T) := by
  classical
  dsimp [sgsLexFlatIndexList]
  rw [List.pairwise_flatMap]
  constructor
  · intro k _hk
    rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    right
    constructor
    · simp
    · simpa [List.getElem_range] using hij
  · rw [List.pairwise_iff_getElem]
    intro p q hp hq hpq
    intro x hx y hy
    rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
    rcases List.mem_map.mp hy with ⟨j, _hj, rfl⟩
    left
    simpa [List.getElem_range] using hpq

/-- Earlier positions in the row-major SGS flattening are exactly strict-past
coordinates for the later decoded coordinate.

This is the concrete decoder-order leaf requested by the reconstruct audit.
The proof is list arithmetic for `List.range.flatMap`; the statement is
deliberately about the row-major list, not the final probability event. -/
theorem sgsLexFlatIndexList_get_before
    (N : PositiveTime) (T : PositiveTime → ℕ)
    {r j : ℕ} (hrj : r < j)
    (hj : j < (sgsLexFlatIndexList N T).length) :
    let a := (sgsLexFlatIndexList N T).get ⟨r, Nat.lt_trans hrj hj⟩
    let b := (sgsLexFlatIndexList N T).get ⟨j, hj⟩
    sgsSampleIndexBefore
      ((⟨b.1 + 1, Nat.succ_pos b.1⟩ : PositiveTime), b.2)
      ((⟨a.1 + 1, Nat.succ_pos a.1⟩ : PositiveTime), a.2) := by
  classical
  have hpair := sgsLexFlatIndexList_pairwise_lex N T
  have hlex :
      let a := (sgsLexFlatIndexList N T).get ⟨r, Nat.lt_trans hrj hj⟩
      let b := (sgsLexFlatIndexList N T).get ⟨j, hj⟩
      a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2) := by
    simpa using
      (List.pairwise_iff_get.1 hpair
        ⟨r, Nat.lt_trans hrj hj⟩ ⟨j, hj⟩ hrj)
  exact sgsSampleIndexBefore_of_sigmaNat_lex hlex

/-- Summing a list through the out-of-range-safe Nat decoder is the same as
summing the mapped list.

Candidate audit: checked target-file `sgsLexFlatIndexList_get_before`,
SOptLib finite-sum/integrability helpers, and Mathlib `Fin.sum_univ_getElem`.
The SOptLib hits aggregate already-indexed finite sums, while this helper is
the lower-level `List.get` decoder bridge needed for Lan Eq. (8.1.70). -/
theorem list_sum_range_decode_eq_map_sum
    {α β : Type*} [AddCommMonoid α] (l : List β) (default : β) (F : β → α) :
    (Finset.range l.length).sum
        (fun j => F (if hj : j < l.length then l.get ⟨j, hj⟩ else default)) =
      (l.map F).sum := by
  classical
  rw [Finset.sum_range]
  simpa using (Fin.sum_univ_getElem (l.map F)).symm

/-- A zero-based list range has the same additive sum as the matching Finset
range.

Candidate audit: Mathlib provides `Finset.sum_range` and
`Fin.sum_univ_getElem`, but no checked `List.range` map-sum theorem was found
by `lean_check_name`/symbol search. This is the small list API bridge needed by
`sgsLexFlatIndexList_map_sum`. -/
theorem list_range_map_sum
    {α : Type*} [AddCommMonoid α] (n : ℕ) (F : ℕ → α) :
    ((List.range n).map F).sum = (Finset.range n).sum F := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, Finset.sum_range_succ]
      simp [List.map_append, ih]

/-- Row-major SGS flattening preserves finite additive sums.

No existing match: searched `row major flatMap range sum decode Finset` and
`List sum flatMap map`; the hits were one-dimensional range reindexing,
probability/integrability sum aggregators, or the order-only
`sgsLexFlatIndexList_get_before`. This helper is the literal finite
`List.range.flatMap` reindex for the `(k,i)` coordinates in Lan Eq. (8.1.70). -/
theorem sgsLexFlatIndexList_map_sum
    {α : Type*} [AddCommMonoid α]
    (N : PositiveTime) (T : PositiveTime → ℕ)
    (F : (Σ _k : ℕ, ℕ) → α) :
    ((sgsLexFlatIndexList N T).map F).sum =
      (Finset.range N.1).sum (fun k =>
        (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
          (fun i => F (⟨k, i⟩ : Σ _k : ℕ, ℕ))) := by
  classical
  dsimp [sgsLexFlatIndexList]
  induction N.1 with
  | zero =>
      simp
  | succ n ih =>
      rw [List.range_succ, Finset.sum_range_succ]
      simp [List.map_append, ih, list_range_map_sum]

/-- Row-major SGS flattening preserves finite additive sums when accessed
through the theorem's out-of-range-safe Nat decoder.

Candidate audit: this combines the checked local helpers
`list_sum_range_decode_eq_map_sum` and `sgsLexFlatIndexList_map_sum`; searched
SOptLib finite-sum aggregators and Mathlib range/list APIs do not provide this
dependent `(k,i)` decoder statement. This is the direct finite reindexing
bridge for Lan Eq. (8.1.70). -/
theorem sgsLexFlatIndexList_sum_range_decode
    {α : Type*} [AddCommMonoid α]
    (N : PositiveTime) (T : PositiveTime → ℕ)
    (default : Σ _k : ℕ, ℕ) (F : (Σ _k : ℕ, ℕ) → α) :
    (Finset.range (sgsLexFlatIndexList N T).length).sum
        (fun j =>
          F (if hj : j < (sgsLexFlatIndexList N T).length then
            (sgsLexFlatIndexList N T).get ⟨j, hj⟩
          else default)) =
      (Finset.range N.1).sum (fun k =>
        (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
          (fun i => F (⟨k, i⟩ : Σ _k : ℕ, ℕ))) := by
  rw [list_sum_range_decode_eq_map_sum]
  exact sgsLexFlatIndexList_map_sum N T F

/-- Scalar normalization for the flattened Eq. (8.1.70) variance summands.

Candidate audit: searched real square/division finite-sum helpers; available
hits concern summing and bounding finite families, not this local identity
between the `coeff` factorization used by the martingale adapter and the
displayed paper denominator. -/
theorem theorem82_linear_variance_summand_normalize
    (G A D q B sig : ℝ) :
    (G * (A / D) * q⁻¹) ^ 2 * (2 * B * sig) =
      G ^ 2 * sig * (2 * B * (A / (D * q)) ^ 2) := by
  ring_nf

/-- Factor a constant out of a dependent two-level finite sum.

Candidate audit: Mathlib `Finset.mul_sum` is the primitive; no separate
dependent nested version was found in SOptLib, whose finite-sum helpers here
target probability/integrability aggregation rather than pure scalar factoring. -/
theorem finset_sum_nested_const_mul
    {α β R : Type*} [CommSemiring R]
    (s : Finset α) (t : α → Finset β) (C : R) (f : α → β → R) :
    (s.sum (fun a => (t a).sum (fun b => C * f a b))) =
      C * s.sum (fun a => (t a).sum (fun b => f a b)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Finset.mul_sum]

/-- Factor a global constant and a row-dependent coefficient out of a dependent
two-level finite sum.

Candidate audit: this is a direct composition of Mathlib `Finset.mul_sum`;
SOptLib finite-sum helpers found in search package integrability or
expectation bounds, not this pure row-major scalar factoring shape. -/
theorem finset_sum_nested_global_row_mul
    {α β R : Type*} [CommSemiring R]
    (s : Finset α) (t : α → Finset β)
    (C : R) (A : α → R) (f : α → β → R) :
    (s.sum (fun a => (t a).sum (fun b => C * A a * f a b))) =
      C * s.sum (fun a => A a * (t a).sum (fun b => f a b)) := by
  simp [Finset.mul_sum, mul_assoc]

/-- Finite Lemma 4.1-style martingale large-deviation bridge for Lan
Eq. (8.1.70), specialized to the SGS nested linear-noise sum.

This is the source theorem that should consume the reconstructed strict-past
interface: the flattened `(k,i)` increments have scalar integrability,
conditional mean zero, and conditional exponential-square control with respect
to the strict-past sample sigma-algebra.  The conclusion is only the linear
tail in Eq. (8.1.70), not the final Theorem 8.2(b) union-bound event.

Source constant audit: `book/FOML/StochasticGradientSliding.json` records
Lemma 4.1 with `exp{-lambda^2/3}`, and the FOML PDF line for Eq. (8.1.70)
states the displayed SGS linear event with the same exponent.  The stronger
`exp{-(2*lambda^2)/3}` appearing in Theorem 8.2(b)'s final bound must therefore
be justified by a separate rescaling/correction step, not by this source bridge. -/
theorem theorem82_linear_tail_martingale_large_deviation_formulaExtension
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hlambda : 0 < lambda)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k)
    (hTpos : ∀ k : PositiveTime, 0 < T k)
    (hcompact : IsCompact S.X)
    (hlinear_int :
      ∀ k i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
                (law.sample k i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ)
          law.P)
    (hadapted_query :
      ∀ k i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i]
          (fun ω => sgsGeneratedOracleQuery S inner k i ω))
    (hcondExp_zero :
      ∀ k i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] =ᵐ[law.P] 0)
    (hcondExp_sq_integrable :
      ∀ k i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P)
    (hcondExp_light :
      ∀ k i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] ≤ᵐ[law.P]
            fun _ => Real.exp 1)
    (hzero_lightScale :
      ∀ k i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner k i ω)
              (law.sample k i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner k i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
        lightScale = 0 → ζ =ᵐ[law.P] 0) :
    law.P
      {ω |
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let δinner := inner κ;
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ))
          >
            lambda *
              (sigma S * Gamma N *
                Real.sqrt
                  (2 * bregmanEnvelope_formulaExtension S uStar hcompact *
                    (Finset.range N.1).sum (fun k =>
                      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                      (Finset.range (T κ)).sum (fun i =>
                        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                        (gamma κ * psWeightProduct spsP (T κ) /
                          (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                            spsP ι * psWeightProduct spsP i)) ^ 2))))} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
  classical
  let idx : Finset (Σ _k : ℕ, ℕ) :=
    (Finset.range N.1).sigma (fun k =>
      Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
  let flatList : List (Σ _k : ℕ, ℕ) := sgsLexFlatIndexList N T
  let n : ℕ := flatList.length
  let decode : ℕ → Σ _k : ℕ, ℕ := fun j =>
    if hj : j < n then flatList.get ⟨j, by simpa [n] using hj⟩
    else (⟨0, 0⟩ : Σ _k : ℕ, ℕ)
  let ζ : (Σ _k : ℕ, ℕ) → Ω → ℝ := fun a ω =>
    let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
    ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ a.2 ω)
        (law.sample κ a.2 ω),
      uStar.1 - sgsGeneratedOracleQuery S inner κ a.2 ω⟫_ℝ
  let coeff : (Σ _k : ℕ, ℕ) → ℝ := fun a =>
    let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
    let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
    Gamma N *
      (gamma κ * psWeightProduct spsP (T κ) /
        (Gamma κ * (1 - psWeightProduct spsP (T κ)))) *
        (spsP ι * psWeightProduct spsP a.2)⁻¹
  let Z : ℕ → Ω → ℝ := fun j ω => coeff (decode j) * ζ (decode j) ω
  let past : ℕ → MeasurableSpace Ω := fun j =>
    let a := decode j
    sgsStrictPastSampleSpace (Ω := Ω) law.sample
      (⟨a.1 + 1, Nat.succ_pos a.1⟩ : PositiveTime) a.2
  let varianceTerm : ℕ → ℝ := fun j =>
    let a := decode j
    let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    (coeff a) ^ 2 * lightScale
  have hdecode_query_adapted :
      ∀ j, j < n →
        Measurable[past j]
          (fun ω =>
            sgsGeneratedOracleQuery S inner
              (⟨(decode j).1 + 1, Nat.succ_pos (decode j).1⟩ : PositiveTime)
              (decode j).2 ω) := by
    intro j hj
    simpa [past] using
      hadapted_query
        (⟨(decode j).1 + 1, Nat.succ_pos (decode j).1⟩ : PositiveTime)
        (decode j).2
  let variance : ℝ :=
    (sigma S * Gamma N *
      Real.sqrt
        (2 * bregmanEnvelope_formulaExtension S uStar hcompact *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι * psWeightProduct spsP i)) ^ 2)))) ^ 2
  have hvariance_eq : variance = (Finset.range n).sum varianceTerm := by
    -- Exact scalar bookkeeping: the row-major Nat enumeration preserves the
    -- displayed nested variance sum after expanding the deterministic
    -- Lemma 4.1 scale `(coeff a)^2 * lightScale`.
    let B : ℝ := bregmanEnvelope_formulaExtension S uStar hcompact
    let nestedCoeffSq : ℝ :=
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (gamma κ * psWeightProduct spsP (T κ) /
            (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
              spsP ι * psWeightProduct spsP i)) ^ 2))
    have hflat :
        (Finset.range n).sum varianceTerm =
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (coeff (⟨k, i⟩ : Σ _k : ℕ, ℕ)) ^ 2 *
                (2 * B * S.sigmaSq))) := by
      simpa [n, flatList, decode, varianceTerm, B] using
        (sgsLexFlatIndexList_sum_range_decode
          (N := N) (T := T)
          (default := (⟨0, 0⟩ : Σ _k : ℕ, ℕ))
          (F := fun a =>
            let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
            let lightScale : ℝ := 2 * B * S.sigmaSq
            (coeff a) ^ 2 * lightScale))
    have hsum_eq :
        (Finset.range n).sum varianceTerm =
          Gamma N ^ 2 * S.sigmaSq * (2 * B * nestedCoeffSq) := by
      rw [hflat]
      calc
        (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (coeff (⟨k, i⟩ : Σ _k : ℕ, ℕ)) ^ 2 *
                (2 * B * S.sigmaSq)))
            =
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (Gamma N ^ 2 * S.sigmaSq * (2 * B)) *
                (gamma κ * psWeightProduct spsP (T κ) /
                  (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                    spsP ι * psWeightProduct spsP i)) ^ 2)) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              refine Finset.sum_congr rfl ?_
              intro i hi
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              have hnorm :=
                theorem82_linear_variance_summand_normalize
                  (G := Gamma N)
                  (A := gamma κ * psWeightProduct spsP (T κ))
                  (D := Gamma κ * (1 - psWeightProduct spsP (T κ)))
                  (q := spsP ι * psWeightProduct spsP i)
                  (B := B) (sig := S.sigmaSq)
              simpa [coeff, κ, ι, mul_assoc, mul_left_comm, mul_comm] using hnorm
        _ = (Gamma N ^ 2 * S.sigmaSq * (2 * B)) * nestedCoeffSq := by
              rw [finset_sum_nested_const_mul]
        _ = Gamma N ^ 2 * S.sigmaSq * (2 * B * nestedCoeffSq) := by
              ring
    rw [hsum_eq]
    dsimp [variance, sigma, B, nestedCoeffSq]
    have hrad_nonneg :
        0 ≤ 2 * bregmanEnvelope_formulaExtension S uStar hcompact *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι * psWeightProduct spsP i)) ^ 2)) := by
      have hB_nonneg :
          0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact :=
        bregmanEnvelope_formulaExtension_nonneg S uStar hcompact
      have hsum_nonneg :
          0 ≤ (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι * psWeightProduct spsP i)) ^ 2)) := by
        refine Finset.sum_nonneg ?_
        intro k hk
        refine Finset.sum_nonneg ?_
        intro i hi
        exact sq_nonneg _
      positivity
    simp_rw [mul_pow]
    rw [Real.sq_sqrt hrad_nonneg, Real.sq_sqrt S.sigmaSq_nonneg]
    ring
  have hpast_le :
      ∀ j, j < n → past j ≤ (by infer_instance : MeasurableSpace Ω) := by
    intro j hj
    dsimp [past]
    exact
      sgsStrictPastSampleSpace_le (Ω := Ω) law.sample law.sample_measurable
        (⟨(decode j).1 + 1, Nat.succ_pos (decode j).1⟩ : PositiveTime)
        (decode j).2
  have hprefix_sm :
      ∀ ν : ℝ, 0 ≤ ν → ∀ j, j < n →
        StronglyMeasurable[past j]
          (fun ω => Real.exp (ν * (Finset.range j).sum (fun r => Z r ω))) := by
    intro ν hν j hj
    refine
      stronglyMeasurable_exp_prefix_sum_of_terms
        (mSub := past j) (Z := Z) (ν := ν) (j := j) ?_
    intro r hr
    have hrj : r < j := by
      simpa using (Finset.mem_range.mp hr)
    have hrn : r < n := Nat.lt_trans hrj hj
    let ar : Σ _k : ℕ, ℕ := decode r
    let aj : Σ _k : ℕ, ℕ := decode j
    let κr : PositiveTime := ⟨ar.1 + 1, Nat.succ_pos ar.1⟩
    let κj : PositiveTime := ⟨aj.1 + 1, Nat.succ_pos aj.1⟩
    have hbefore : sgsSampleIndexBefore (κj, aj.2) (κr, ar.2) := by
      have hrow :=
        sgsLexFlatIndexList_get_before (N := N) (T := T) hrj
          (by simpa [n, flatList] using hj)
      simpa [ar, aj, κr, κj, decode, n, flatList, hrn, hj] using hrow
    have hquery_later :
        Measurable[past j]
          (fun ω => sgsGeneratedOracleQuery S inner κr ar.2 ω) := by
      simpa [past, aj, κj] using
        (sgsGeneratedQuery_measurable_laterStrictPast_of_indexBefore
          (S := S) (sample := law.sample) (inner := inner)
          hadapted_query (k := κr) (k' := κj) (i := ar.2) (i' := aj.2)
          hbefore)
    have hsample_later :
        Measurable[past j] (fun ω => law.sample κr ar.2 ω) := by
      simpa [past, aj, κj] using
        (sgsSample_measurable_strictPast (Ω := Ω) law.sample κj aj.2 κr ar.2
          hbefore)
    let queryFP : Ω → FeasiblePoint S :=
      fun ω =>
        ⟨sgsGeneratedOracleQuery S inner κr ar.2 ω,
          sgsGeneratedOracleQuery_mem_X S inner κr ar.2 ω⟩
    have hqueryFP_later : Measurable[past j] queryFP := by
      simpa [queryFP] using hquery_later.subtype_mk
    have hpair_later :
        Measurable[past j] (fun ω => (queryFP ω, law.sample κr ar.2 ω)) :=
      hqueryFP_later.prod hsample_later
    have hscalar_later :
        Measurable[past j]
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κr ar.2 ω)
                (law.sample κr ar.2 ω),
              uStar.1 - sgsGeneratedOracleQuery S inner κr ar.2 ω⟫_ℝ) :=
      by
        have hkernel :=
          oracle_residual_target_inner_measurable_of_residual_measurable
            (S := S) (x := uStar) law.oracle_residual_measurable
        have hleft :
            Measurable[past j]
              (fun ω =>
                ⟪uStar.1 - sgsGeneratedOracleQuery S inner κr ar.2 ω,
                  oracleNoiseAt S (sgsGeneratedOracleQuery S inner κr ar.2 ω)
                    (law.sample κr ar.2 ω)⟫_ℝ) := by
          simpa [queryFP] using hkernel.comp hpair_later
        simpa [real_inner_comm] using hleft
    simpa [Z, ζ, coeff, ar, κr] using
      hscalar_later.const_mul (coeff ar)
  have hstep_int :
      ∀ ν : ℝ, 0 ≤ ν → ∀ j, j < n →
        Integrable (fun ω => Real.exp (ν * Z j ω)) law.P := by
    intro ν hν j hj
    let a : Σ _k : ℕ, ℕ := decode j
    let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    by_cases hscale : 0 < lightScale
    · have hbase :
          Integrable
            (fun ω => Real.exp ((ν * coeff a) * ζ a ω)) law.P := by
        exact
          integrable_exp_linear_of_integrable_exp_quadratic
            (μ := law.P) (Z := ζ a) (scale := lightScale)
            (ν := ν * coeff a) hscale
            (by simpa [ζ, a, κ] using hlinear_int κ a.2)
            (by simpa [ζ, lightScale, a, κ] using
              hcondExp_sq_integrable κ a.2)
      simpa [Z, a, mul_assoc] using hbase
    · have hlightScale_nonneg : 0 ≤ lightScale := by
        have henv_nonneg :
            0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact :=
          bregmanEnvelope_formulaExtension_nonneg S uStar hcompact
        have hsigma_nonneg : 0 ≤ S.sigmaSq := S.sigmaSq_nonneg
        dsimp [lightScale]
        positivity
      have hlightScale_zero : lightScale = 0 :=
        le_antisymm (le_of_not_gt hscale) hlightScale_nonneg
      have hζ_zero : ζ a =ᵐ[law.P] 0 := by
        simpa [ζ, lightScale, a, κ] using
          hzero_lightScale κ a.2 hlightScale_zero
      have hZ_zero :
          (fun ω => Real.exp (ν * Z j ω)) =ᵐ[law.P] fun _ => (1 : ℝ) := by
        filter_upwards [hζ_zero] with ω hζω
        simp [Z, ζ, a, hζω]
      exact (integrable_const (1 : ℝ)).congr hZ_zero.symm
  have hstep_cond_mgf :
      ∀ ν : ℝ, 0 ≤ ν → ∀ j, j < n →
        law.P[(fun ω => Real.exp (ν * Z j ω)) | past j] ≤ᵐ[law.P]
          fun _ => Real.exp (3 * ν ^ 2 * varianceTerm j / 4) := by
    intro ν hν j hj
    let a : Σ _k : ℕ, ℕ := decode j
    let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
    let lightScale : ℝ :=
      2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
    have hlightScale_nonneg : 0 ≤ lightScale := by
      have henv_nonneg :
          0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact :=
        bregmanEnvelope_formulaExtension_nonneg S uStar hcompact
      have hsigma_nonneg : 0 ≤ S.sigmaSq := S.sigmaSq_nonneg
      dsimp [lightScale]
      positivity
    have hbase :=
      theorem82_weighted_one_step_cond_mgf_scale_adapter
        (μ := law.P) (mSub := past j) (ζ := ζ a)
        (lightScale := lightScale) (ν := ν) (coeff := coeff a)
        (hpast_le j hj) hν
        (by simpa [ζ, a, κ] using hlinear_int κ a.2)
        (by simpa [Z, a] using hstep_int ν hν j hj)
        (by simpa [ζ, lightScale, a, κ] using
          hcondExp_sq_integrable κ a.2)
        hlightScale_nonneg
        (by simpa [ζ, past, a, κ] using hcondExp_zero κ a.2)
        (by simpa [ζ, lightScale, past, a, κ] using hcondExp_light κ a.2)
        (by
          intro hscale_zero
          simpa [ζ, lightScale, a, κ] using
            hzero_lightScale κ a.2 hscale_zero)
    simpa [Z, varianceTerm, lightScale, a] using hbase
  have hflat_tail :
      law.P {ω | (Finset.range n).sum (fun j => Z j ω) >
          lambda * Real.sqrt variance} ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
    by_cases hvariance_pos : 0 < variance
    · simpa using
        (finite_weighted_condExp_light_tail_chernoff_bound_gt_of_cond_mgf
          (μ := law.P) (n := n) (Z := Z) (varianceTerm := varianceTerm)
          (past := past) (variance := variance) (lambda := lambda)
          hlambda hvariance_pos hvariance_eq hpast_le hprefix_sm hstep_int
          hstep_cond_mgf)
    · have hvariance_nonpos : variance ≤ 0 := le_of_not_gt hvariance_pos
      have hZ_zero : ∀ j, j < n → Z j =ᵐ[law.P] 0 := by
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
        have hlightScale_nonneg : 0 ≤ lightScale := by
          have henv_nonneg :
              0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact :=
            bregmanEnvelope_formulaExtension_nonneg S uStar hcompact
          have hsigma_nonneg : 0 ≤ S.sigmaSq := S.sigmaSq_nonneg
          dsimp [lightScale]
          positivity
        have hvariance_sum_nonpos :
            (Finset.range n).sum varianceTerm ≤ 0 := by
          simpa [hvariance_eq] using hvariance_nonpos
        have hvarianceTerm_nonneg :
            ∀ r ∈ Finset.range n, 0 ≤ varianceTerm r := by
          intro r _hr
          dsimp [varianceTerm]
          exact mul_nonneg (sq_nonneg _) hlightScale_nonneg
        intro j hj
        have hjmem : j ∈ Finset.range n := Finset.mem_range.mpr hj
        have hsingle :
            varianceTerm j ≤ (Finset.range n).sum varianceTerm :=
          Finset.single_le_sum hvarianceTerm_nonneg hjmem
        have hterm_zero : varianceTerm j = 0 :=
          le_antisymm (le_trans hsingle hvariance_sum_nonpos)
            (hvarianceTerm_nonneg j hjmem)
        let a : Σ _k : ℕ, ℕ := decode j
        let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
        have hprod_zero : (coeff a) ^ 2 * lightScale = 0 := by
          simpa [varianceTerm, a, lightScale] using hterm_zero
        rcases (mul_eq_zero.mp hprod_zero) with hcoeff_sq_zero | hscale_zero
        · have hcoeff_zero : coeff a = 0 := sq_eq_zero_iff.mp hcoeff_sq_zero
          filter_upwards with ω
          simp [Z, a, hcoeff_zero]
        · have hζ_zero : ζ a =ᵐ[law.P] 0 := by
            simpa [ζ, lightScale, a, κ] using
              hzero_lightScale κ a.2 hscale_zero
          filter_upwards [hζ_zero] with ω hζω
          simp [Z, a, hζω]
      have hzero :
          law.P {ω | (Finset.range n).sum (fun j => Z j ω) >
              lambda * Real.sqrt variance} = 0 :=
        finite_strict_tail_zero_of_ae_zero
          (μ := law.P) (n := n) (Z := Z) (variance := variance)
          (lambda := lambda) hlambda hvariance_nonpos hZ_zero
      rw [hzero]
      exact zero_le _
  -- Remaining exact leaf: rewrite the Nat-enumerated finite tail `hflat_tail`
  -- back to the displayed nested SGS event and replace `variance` by the
  -- paper's square-root scale.
  have hsum_eq :
      ∀ ω, (Finset.range n).sum (fun j => Z j ω) =
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            let δinner := inner κ
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                  let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω)
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ)) := by
    intro ω
    have hdecode_sum :
        (Finset.range n).sum (fun j => Z j ω) =
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              coeff (⟨k, i⟩ : Σ _k : ℕ, ℕ) *
                ζ (⟨k, i⟩ : Σ _k : ℕ, ℕ) ω)) := by
      simpa [n, flatList, decode, Z] using
        (sgsLexFlatIndexList_sum_range_decode
          (N := N) (T := T)
          (default := (⟨0, 0⟩ : Σ _k : ℕ, ℕ))
          (F := fun a => coeff a * ζ a ω))
    rw [hdecode_sum]
    calc
      (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range (T κ)).sum (fun i =>
            coeff (⟨k, i⟩ : Σ _k : ℕ, ℕ) *
              ζ (⟨k, i⟩ : Σ _k : ℕ, ℕ) ω))
          =
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range (T κ)).sum (fun i =>
            Gamma N *
              (gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ)))) *
              ((spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) *
                  psWeightProduct spsP i)⁻¹ *
                ζ (⟨k, i⟩ : Σ _k : ℕ, ℕ) ω))) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [coeff, mul_assoc, mul_left_comm, mul_comm]
      _ = Gamma N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (gamma κ * psWeightProduct spsP (T κ) /
            (Gamma κ * (1 - psWeightProduct spsP (T κ)))) *
            (Finset.range (T κ)).sum (fun i =>
              (spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) *
                psWeightProduct spsP i)⁻¹ *
                ζ (⟨k, i⟩ : Σ _k : ℕ, ℕ) ω)) := by
            simpa [mul_assoc] using
              (finset_sum_nested_global_row_mul
                (s := Finset.range N.1)
                (t := fun k =>
                  Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
                (C := Gamma N)
                (A := fun k =>
                  let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
                  gamma κ * psWeightProduct spsP (T κ) /
                    (Gamma κ * (1 - psWeightProduct spsP (T κ))))
                (f := fun k i =>
                  (spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) *
                    psWeightProduct spsP i)⁻¹ *
                    ζ (⟨k, i⟩ : Σ _k : ℕ, ℕ) ω))
      _ = Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            let δinner := inner κ
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                  let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω)
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ)) := by
            simp [ζ, sgsGeneratedOracleQuery, mul_assoc]
  have hscale_eq :
      Real.sqrt variance =
        sigma S * Gamma N *
          Real.sqrt
            (2 * bregmanEnvelope_formulaExtension S uStar hcompact *
              (Finset.range N.1).sum (fun k =>
                let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                  (gamma κ * psWeightProduct spsP (T κ) /
                    (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                      spsP ι * psWeightProduct spsP i)) ^ 2))) := by
    dsimp [variance]
    rw [Real.sqrt_sq_eq_abs]
    apply abs_of_nonneg
    have hsigma_nonneg : 0 ≤ sigma S := by
      dsimp [sigma]
      exact Real.sqrt_nonneg _
    have hgamma_nonneg : 0 ≤ Gamma N := le_of_lt (hGamma_pos N)
    positivity
  have hevent :
      {ω |
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            let δinner := inner κ
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                  let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω)
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ))
          >
            lambda *
              (sigma S * Gamma N *
                Real.sqrt
                  (2 * bregmanEnvelope_formulaExtension S uStar hcompact *
                    (Finset.range N.1).sum (fun k =>
                      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
                      (Finset.range (T κ)).sum (fun i =>
                        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                        (gamma κ * psWeightProduct spsP (T κ) /
                          (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                            spsP ι * psWeightProduct spsP i)) ^ 2))))} =
      {ω | (Finset.range n).sum (fun j => Z j ω) >
          lambda * Real.sqrt variance} := by
    ext ω
    simp [hsum_eq ω, hscale_eq]
  rw [hevent]
  exact hflat_tail

/-- Checked source-boundary probability union for Theorem 8.2(b).

The source Eq. (8.1.70) bridge gives `exp(-lambda^2/3)` for the displayed
linear event, and Eq. (8.1.71) gives `exp(-lambda)` for the quadratic event.
This helper intentionally returns only that checked source union bound.  It must
not be used as a same-event strengthening to the theorem statement's
`exp(-(2*lambda^2)/3)` linear exponent; the counterexample below shows that
strengthening is false without a rescaled event or a corrected source boundary. -/
theorem theorem82_final_probability_constant_source_boundary_formulaExtension
    [MeasurableSpace Ω] (P : Measure Ω) (target : Set Ω) (lambda : ℝ)
    (hsource_union :
      P target ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda))) :
    P target ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  exact hsource_union

/-- The final linear-tail constant requested by the current Theorem 8.2(b)
assembly is strictly stronger than the Eq. (8.1.70) source constant for every
positive confidence parameter.

This private source-boundary certificate prevents the missing factor `2` from
being hidden inside a same-event wrapper: `exp (-(2 * lambda^2)/3)` is a smaller
right-hand side than `exp (-(lambda^2)/3)` whenever `0 < lambda`. -/
theorem theorem82_linear_tail_final_constant_same_event_strictly_stronger
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ENNReal.ofReal (Real.exp (-(2 * lambda ^ 2) / 3)) <
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
  have hsquare_pos : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
  have harg :
      -(2 * lambda ^ 2) / 3 < -(lambda ^ 2) / 3 := by
    nlinarith
  exact (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    (Real.exp_lt_exp.mpr harg)

/-- Concrete counterexample to deriving the final linear-tail constant from the
Eq. (8.1.70) same-event source bound alone.

For `lambda = 1`, an event with mass `exp (-1/2)` satisfies the source
`exp (-1/3)` bound but violates the stronger `exp (-2/3)` bound. -/
theorem theorem82_linear_tail_final_constant_same_event_counterexample :
    ¬ (∀ (P : Measure Unit) (linearBad : Set Unit),
        P linearBad ≤ ENNReal.ofReal (Real.exp (-((1 : ℝ) ^ 2) / 3)) →
          P linearBad ≤ ENNReal.ofReal (Real.exp (-(2 * (1 : ℝ) ^ 2) / 3))) := by
  classical
  intro h
  let P : Measure Unit :=
    ENNReal.ofReal (Real.exp (-(1 : ℝ) / 2)) • Measure.dirac ()
  have hP_univ :
      P Set.univ = ENNReal.ofReal (Real.exp (-(1 : ℝ) / 2)) := by
    simp [P]
  have hsource :
      P Set.univ ≤ ENNReal.ofReal (Real.exp (-((1 : ℝ) ^ 2) / 3)) := by
    rw [hP_univ]
    refine ENNReal.ofReal_le_ofReal ?_
    have harg : -(1 : ℝ) / 2 ≤ -((1 : ℝ) ^ 2) / 3 := by norm_num
    exact Real.exp_le_exp.mpr harg
  have hbad :
      P Set.univ ≤ ENNReal.ofReal (Real.exp (-(2 * (1 : ℝ) ^ 2) / 3)) :=
    h P Set.univ hsource
  rw [hP_univ] at hbad
  have hstrict :
      ENNReal.ofReal (Real.exp (-(2 * (1 : ℝ) ^ 2) / 3)) <
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / 2)) := by
    refine (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2 ?_
    have harg : -(2 * (1 : ℝ) ^ 2) / 3 < -(1 : ℝ) / 2 := by norm_num
    exact Real.exp_lt_exp.mpr harg
  exact not_le_of_gt hstrict hbad

/-- Zero-variance source-boundary certificate for the non-strict linear event.

Lan Eq. (8.1.70), as extracted from the PDF, uses a strict `>` deviation event.
The currently generated Lean linear-tail bridge still has a non-strict `≥`
event.  A deterministic zero-variance branch cannot prove that non-strict event
has the subunit Lemma 4.1 tail: for zero increments and zero threshold the event
is all of the probability space.  This certificate prevents the zero-scale
branch from being closed by a false "a.e. zero implies null bad event" rewrite. -/
theorem theorem82_linear_tail_zero_variance_nonstrict_counterexample :
    ¬ (∀ P : Measure Unit,
        P Set.univ ≤ ENNReal.ofReal (Real.exp (-((1 : ℝ) ^ 2) / 3))) := by
  intro h
  have hdirac := h (Measure.dirac ())
  have hmass : (Measure.dirac () : Measure Unit) Set.univ = 1 := by
    simp
  rw [hmass] at hdirac
  have hstrict :
      ENNReal.ofReal (Real.exp (-((1 : ℝ) ^ 2) / 3)) < (1 : ENNReal) := by
    have hexp_lt_one : Real.exp (-((1 : ℝ) ^ 2) / 3) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    have hlt :
        ENNReal.ofReal (Real.exp (-((1 : ℝ) ^ 2) / 3)) <
          ENNReal.ofReal (1 : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hexp_lt_one
    simpa using hlt
  exact not_le_of_gt hstrict hdirac

/-- Union-bound assembly for Lan Theorem 8.2(b)'s high-probability conclusion.

Candidate audit: searched SOptLib tail-probability/selection wrappers and
Mathlib measure union APIs.  The SOptLib candidates package selected-output or
finite-stopping expansions, while this source step only needs Mathlib's
`measure_union_le`, `measure_mono`, and `ENNReal.ofReal_add` to combine the two
Eq. (8.1.70)/(8.1.71) events into the displayed Theorem 8.2(b) probability
bound. -/
theorem theorem82_highProbability_union_bound_formulaExtension
    [MeasurableSpace Ω] (P : Measure Ω)
    (target linearBad quadraticBad : Set Ω) (lambda : ℝ)
    (hsubset : target ⊆ linearBad ∪ quadraticBad)
    (hlinear :
      P linearBad ≤ ENNReal.ofReal (Real.exp (-(2 * lambda ^ 2) / 3)))
    (hquadratic :
      P quadraticBad ≤ ENNReal.ofReal (Real.exp (-lambda))) :
    P target ≤
      ENNReal.ofReal (Real.exp (-(2 * lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  calc
    P target ≤ P (linearBad ∪ quadraticBad) := MeasureTheory.measure_mono hsubset
    _ ≤ P linearBad + P quadraticBad := measure_union_le linearBad quadraticBad
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * lambda ^ 2) / 3)) +
          ENNReal.ofReal (Real.exp (-lambda)) := add_le_add hlinear hquadratic
    _ = ENNReal.ofReal
          (Real.exp (-(2 * lambda ^ 2) / 3) + Real.exp (-lambda)) := by
          rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]

/-- Union-bound assembly with the source constant from Lan Eq. (8.1.70).

This is the checked probability-combination step directly supported by Lemma
4.1 and Eq. (8.1.71): the linear event contributes `exp(-lambda^2/3)` and the
quadratic event contributes `exp(-lambda)`.  Any later appearance of
`exp(-(2*lambda^2)/3)` must be justified separately, not by strengthening this
same linear event. -/
theorem theorem82_highProbability_union_bound_source_formulaExtension
    [MeasurableSpace Ω] (P : Measure Ω)
    (target linearBad quadraticBad : Set Ω) (lambda : ℝ)
    (hsubset : target ⊆ linearBad ∪ quadraticBad)
    (hlinear :
      P linearBad ≤ ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)))
    (hquadratic :
      P quadraticBad ≤ ENNReal.ofReal (Real.exp (-lambda))) :
    P target ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  calc
    P target ≤ P (linearBad ∪ quadraticBad) := MeasureTheory.measure_mono hsubset
    _ ≤ P linearBad + P quadraticBad := measure_union_le linearBad quadraticBad
    _ ≤ ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) +
          ENNReal.ofReal (Real.exp (-lambda)) := add_le_add hlinear hquadratic
    _ = ENNReal.ofReal
          (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
          rw [ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]

/-- Scalar event inclusion used after Lan Eq. (8.1.69).

Candidate audit: searched SOptLib tail-probability wrappers, target-file
high-probability helpers, and Mathlib measure/set APIs.  None states this
ordered-real decomposition: if the master inequality bounds the gap by a
deterministic term plus a linear noise term and a centered quadratic excess,
then exceeding the deterministic bound plus the two probability scales forces
either the linear bad event or the strict quadratic bad event from Lan
Eq. (8.1.71).  This is the pure event-subset algebra behind the sentence
following that display. -/
theorem theorem82_highProbability_master_event_subset_scalar
    {Ω : Type*} (gap linear quadratic : Ω → ℝ)
    (Bd quadraticMean linearScale quadraticScale lambda : ℝ)
    (hmaster :
      ∀ ω, gap ω ≤ Bd + linear ω + (quadratic ω - quadraticMean)) :
    {ω | gap ω ≥ Bd + lambda * (linearScale + quadraticScale)} ⊆
      {ω | linear ω ≥ lambda * linearScale} ∪
        {ω | quadratic ω > quadraticMean + lambda * quadraticScale} := by
  intro ω hω
  by_cases hlinear : linear ω ≥ lambda * linearScale
  · exact Or.inl hlinear
  · right
    by_contra hquadratic
    have hlinear_lt : linear ω < lambda * linearScale := lt_of_not_ge hlinear
    have hquadratic_le :
        quadratic ω ≤ quadraticMean + lambda * quadraticScale :=
      le_of_not_gt hquadratic
    have hupper := hmaster ω
    have hstrict :
        Bd + linear ω + (quadratic ω - quadraticMean) <
          Bd + lambda * (linearScale + quadraticScale) := by
      have hquad_diff : quadratic ω - quadraticMean ≤ lambda * quadraticScale := by
        linarith
      linarith
    have hgap_lower : Bd + lambda * (linearScale + quadraticScale) ≤ gap ω := by
      simpa using hω
    linarith

/-- Strict scalar event inclusion for the checked source-boundary route.

The strict output-gap event is the event that is actually compatible with the
strict Eq. (8.1.70) and Eq. (8.1.71) source tails. -/
theorem theorem82_highProbability_master_strict_event_subset_scalar
    {Ω : Type*} (gap linear quadratic : Ω → ℝ)
    (Bd quadraticMean linearScale quadraticScale lambda : ℝ)
    (hmaster :
      ∀ ω, gap ω ≤ Bd + linear ω + (quadratic ω - quadraticMean)) :
    {ω | gap ω > Bd + lambda * (linearScale + quadraticScale)} ⊆
      {ω | linear ω > lambda * linearScale} ∪
        {ω | quadratic ω > quadraticMean + lambda * quadraticScale} := by
  intro ω hω
  by_cases hlinear : linear ω > lambda * linearScale
  · exact Or.inl hlinear
  · right
    by_contra hquadratic
    have hlinear_le : linear ω ≤ lambda * linearScale := le_of_not_gt hlinear
    have hquadratic_le :
        quadratic ω ≤ quadraticMean + lambda * quadraticScale :=
      le_of_not_gt hquadratic
    have hupper := hmaster ω
    have hgap_upper : gap ω ≤ Bd + lambda * (linearScale + quadraticScale) := by
      linarith
    exact not_lt_of_ge hgap_upper hω

/-- Measure-theoretic aggregation step after the pointwise Jensen inequality in
Lan Eq. (8.1.71).

The source-specific coefficient normalization and convexity calculation are
kept outside this helper.  Once those give
`exp f <= sum_i q_i * exp (Y_i)` with nonnegative weights summing to one, this
lemma supplies the Lean well-posedness missing from the old light-tail model:
integrability of `exp f` follows by domination, and the integral bound follows
from the coordinate exponential-moment bounds. -/
theorem finite_exp_moment_of_pointwise_le_weighted_sum
    [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (Y : ι → Ω → ℝ) (f : Ω → ℝ)
    (hf_aestronglyMeasurable : AEStronglyMeasurable (fun ω => Real.exp (f ω)) μ)
    (hY_int : ∀ i ∈ s, Integrable (fun ω => Real.exp (Y i ω)) μ)
    (hY_bound : ∀ i ∈ s, (∫ ω, Real.exp (Y i ω) ∂μ) ≤ Real.exp 1)
    (hq_nonneg : ∀ i ∈ s, 0 ≤ q i)
    (hq_sum : s.sum q = 1)
    (hpoint :
      (fun ω => Real.exp (f ω)) ≤ᵐ[μ]
        fun ω => s.sum (fun i => q i * Real.exp (Y i ω))) :
    Integrable (fun ω => Real.exp (f ω)) μ ∧
      (∫ ω, Real.exp (f ω) ∂μ) ≤ Real.exp 1 := by
  classical
  let majorant : Ω → ℝ := fun ω => s.sum (fun i => q i * Real.exp (Y i ω))
  have hmajorant_int : Integrable majorant μ := by
    dsimp [majorant]
    refine integrable_finset_sum s ?_
    intro i hi
    exact (hY_int i hi).const_mul (q i)
  have hmajorant_nonneg : ∀ ω, 0 ≤ majorant ω := by
    intro ω
    dsimp [majorant]
    exact Finset.sum_nonneg
      (fun i hi => mul_nonneg (hq_nonneg i hi) (Real.exp_nonneg _))
  have hf_int : Integrable (fun ω => Real.exp (f ω)) μ := by
    refine Integrable.mono hmajorant_int hf_aestronglyMeasurable ?_
    filter_upwards [hpoint] with ω hω
    have hmajorantω_nonneg : 0 ≤ majorant ω := hmajorant_nonneg ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg hmajorantω_nonneg]
    exact hω
  have hintegral_le_majorant :
      (∫ ω, Real.exp (f ω) ∂μ) ≤ ∫ ω, majorant ω ∂μ :=
    integral_mono_ae hf_int hmajorant_int hpoint
  have hmajorant_bound :
      (∫ ω, majorant ω ∂μ) ≤ Real.exp 1 := by
    have hterm_int :
        ∀ i ∈ s, Integrable (fun ω => q i * Real.exp (Y i ω)) μ := by
      intro i hi
      exact (hY_int i hi).const_mul (q i)
    calc
      (∫ ω, majorant ω ∂μ)
          = s.sum (fun i => ∫ ω, q i * Real.exp (Y i ω) ∂μ) := by
              dsimp [majorant]
              rw [integral_finset_sum s hterm_int]
      _ = s.sum (fun i => q i * ∫ ω, Real.exp (Y i ω) ∂μ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [integral_const_mul]
      _ ≤ s.sum (fun i => q i * Real.exp 1) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact mul_le_mul_of_nonneg_left (hY_bound i hi) (hq_nonneg i hi)
      _ = Real.exp 1 := by
              rw [← Finset.sum_mul, hq_sum, one_mul]
  exact ⟨hf_int, le_trans hintegral_le_majorant hmajorant_bound⟩

/-- Finite Jensen inequality for the scalar exponential in Lan Eq. (8.1.71).

This is the source convexity step only: deterministic nonnegative weights
normalized to one turn the exponential of the weighted average into the
weighted sum of exponentials. -/
theorem finite_exp_jensen_of_weighted_sum
    {ι : Type*} (s : Finset ι) (q : ι → ℝ) (Y : ι → ℝ) (f : ℝ)
    (hq_nonneg : ∀ i ∈ s, 0 ≤ q i)
    (hq_sum : s.sum q = 1)
    (hf : f = s.sum (fun i => q i * Y i)) :
    Real.exp f ≤ s.sum (fun i => q i * Real.exp (Y i)) := by
  classical
  have hJ :=
    convexOn_exp.map_sum_le (t := s) (w := q) (p := Y)
      hq_nonneg hq_sum (by intro i hi; trivial)
  simpa [hf, smul_eq_mul] using hJ

/-- Nested finite-sum algebra identifying the normalized quadratic term with
the weighted average of coordinate light-tail exponents in Lan Eq. (8.1.71). -/
theorem nested_quadratic_normalized_lightTail_algebra
    {α β : Type*} (s : Finset α) (t : α → Finset β)
    (G sigma scale : ℝ) (C B sp prevP : α → β → ℝ) (Z : α → β → ℝ)
    (hsigma_ne : sigma ≠ 0) :
    (G * (s.sum fun a =>
      ((t a).sum fun b =>
        C a b * ((sp a b * prevP a b)⁻¹ *
          (Z a b / (B a b * sp a b)))))) / scale =
    ((s.sigma t).sum fun x =>
      ((sigma * G *
          (C x.1 x.2 / (B x.1 x.2 * sp x.1 x.2 ^ 2 *
            prevP x.1 x.2))) / scale) *
        (Z x.1 x.2 / sigma)) := by
  classical
  rw [Finset.sum_sigma]
  calc
    (G * (s.sum fun a =>
      ((t a).sum fun b =>
        C a b * ((sp a b * prevP a b)⁻¹ *
          (Z a b / (B a b * sp a b)))))) / scale
        =
      (s.sum fun a =>
        ((t a).sum fun b =>
          (G * (C a b * ((sp a b * prevP a b)⁻¹ *
            (Z a b / (B a b * sp a b))))) / scale)) := by
          rw [Finset.mul_sum, Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum, Finset.sum_div]
    _ =
      (s.sum fun a =>
        ((t a).sum fun b =>
          ((sigma * G *
              (C a b / (B a b * sp a b ^ 2 * prevP a b))) /
            scale) * (Z a b / sigma))) := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          refine Finset.sum_congr rfl ?_
          intro b _hb
          field_simp [hsigma_ne]

/-- Outer-coefficient form of `nested_quadratic_normalized_lightTail_algebra`.

The SGS quadratic term keeps the outer `k` coefficient outside the inner
finite sum.  This helper performs that finite-sum distribution before applying
the normalized light-tail algebra. -/
theorem nested_quadratic_normalized_lightTail_algebra_outer
    {α β : Type*} (s : Finset α) (t : α → Finset β)
    (G sigma scale : ℝ) (C : α → ℝ) (B sp prevP : α → β → ℝ)
    (Z : α → β → ℝ) (hsigma_ne : sigma ≠ 0) :
    (G * (s.sum fun a =>
      C a * ((t a).sum fun b =>
        (sp a b * prevP a b)⁻¹ *
          (Z a b / (B a b * sp a b))))) / scale =
    ((s.sigma t).sum fun x =>
      ((sigma * G *
          (C x.1 / (B x.1 x.2 * sp x.1 x.2 ^ 2 *
            prevP x.1 x.2))) / scale) *
        (Z x.1 x.2 / sigma)) := by
  classical
  have hdist :
      (G * (s.sum fun a =>
        C a * ((t a).sum fun b =>
          (sp a b * prevP a b)⁻¹ *
            (Z a b / (B a b * sp a b))))) / scale =
      (G * (s.sum fun a =>
        ((t a).sum fun b =>
          C a * ((sp a b * prevP a b)⁻¹ *
            (Z a b / (B a b * sp a b)))))) / scale := by
    congr 2
    refine Finset.sum_congr rfl ?_
    intro a _ha
    rw [Finset.mul_sum]
  have hraw :=
    nested_quadratic_normalized_lightTail_algebra
      (s := s) (t := t) (G := G) (sigma := sigma) (scale := scale)
      (C := fun a _b => C a) (B := B) (sp := sp) (prevP := prevP)
      (Z := Z) hsigma_ne
  calc
    (G * (s.sum fun a =>
      C a * ((t a).sum fun b =>
        (sp a b * prevP a b)⁻¹ *
          (Z a b / (B a b * sp a b))))) / scale
        =
      (G * (s.sum fun a =>
        ((t a).sum fun b =>
          C a * ((sp a b * prevP a b)⁻¹ *
            (Z a b / (B a b * sp a b)))))) / scale := hdist
    _ =
      ((s.sigma t).sum fun x =>
        ((sigma * G *
            (C x.1 / (B x.1 x.2 * sp x.1 x.2 ^ 2 *
              prevP x.1 x.2))) / scale) *
          (Z x.1 x.2 / sigma)) := by
        simpa using hraw

/-- Strict exponential Markov bridge used in Lan Eq. (8.1.71).

Aligns with Lan Eq. (8.1.71)'s final Markov step after the convexity-of-exp
aggregation.  SOptLib candidate `measure_gt_le_of_integral_le_of_nonneg` is
used directly; this helper only packages the exponential monotonicity and
`exp 1 / exp (1 + λ) = exp (-λ)` scalar simplification needed by the paper's
displayed form. -/
theorem strict_markov_exp_tail_from_exp_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (lambda : ℝ)
    (hf_int : Integrable (fun ω => Real.exp (f ω)) μ)
    (hexp_int_le : (∫ ω, Real.exp (f ω) ∂μ) ≤ Real.exp 1)
    (hlambda : 0 < lambda) :
    μ {ω | f ω > 1 + lambda} ≤ ENNReal.ofReal (Real.exp (-lambda)) := by
  have hsubset :
      {ω | f ω > 1 + lambda} ⊆
        {ω | Real.exp (f ω) > Real.exp (1 + lambda)} := by
    intro ω hω
    exact Real.exp_lt_exp.mpr hω
  have htail :
      μ {ω | Real.exp (f ω) > Real.exp (1 + lambda)} ≤
        ENNReal.ofReal (Real.exp (-lambda)) := by
    refine
      measure_gt_le_of_integral_le_of_nonneg
        (μ := μ) (fun ω => Real.exp (f ω)) (Real.exp (1 + lambda))
        (Real.exp 1) (Real.exp (-lambda)) hf_int
        (fun ω => le_of_lt (Real.exp_pos _)) hexp_int_le
        (le_of_lt (Real.exp_pos _)) ?_ ?_
    · intro _ht
      have hpos1 : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
      have hposLam : Real.exp lambda ≠ 0 := Real.exp_ne_zero lambda
      have hratio :
          Real.exp 1 / Real.exp (1 + lambda) = Real.exp (-lambda) := by
        calc
        Real.exp 1 / Real.exp (1 + lambda)
            = Real.exp 1 / (Real.exp 1 * Real.exp lambda) := by
                rw [Real.exp_add]
        _ = (Real.exp lambda)⁻¹ := by
              field_simp [hpos1, hposLam]
        _ = Real.exp (-lambda) := by
              rw [Real.exp_neg]
      exact le_of_eq hratio
    · intro hzero
      exact False.elim ((Real.exp_ne_zero (1 + lambda)) hzero)
  exact le_trans (measure_mono hsubset) htail

/-- Nested finite-sum algebra factoring the `σ²` term in Lan Eq. (8.1.71).

This is the scalar normalization behind `quadraticMean = quadraticScale` in the
positive-variance branch.  Candidate audit: checked SOptLib weighted-average and
telescope helpers plus target-file high-probability helpers; those package
Jensen/tail steps, while this route-local fact is only real-field algebra for
the literal nested coefficients in Eq. (8.1.71). -/
theorem nested_quadratic_mean_scale_algebra
    {α β : Type*} (s : Finset α) (t : α → Finset β)
    (G sigma : ℝ) (A beta sp prevP : α → β → ℝ) :
    G * (s.sum fun a =>
      ((t a).sum fun b =>
        A a b * ((sp a b * prevP a b)⁻¹ *
          (sigma / (beta a b * sp a b))))) =
      sigma * G *
        (s.sum fun a =>
          ((t a).sum fun b =>
            A a b / (beta a b * sp a b ^ 2 * prevP a b))) := by
  classical
  have hpoint : ∀ a b,
      A a b * ((sp a b * prevP a b)⁻¹ *
          (sigma / (beta a b * sp a b))) =
        sigma * (A a b / (beta a b * sp a b ^ 2 * prevP a b)) := by
    intro a b
    ring_nf
  calc
    G * (s.sum fun a =>
      ((t a).sum fun b =>
        A a b * ((sp a b * prevP a b)⁻¹ *
          (sigma / (beta a b * sp a b)))))
        =
      G * (s.sum fun a =>
        ((t a).sum fun b =>
          sigma * (A a b / (beta a b * sp a b ^ 2 * prevP a b)))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          refine Finset.sum_congr rfl ?_
          intro b _hb
          exact hpoint a b
    _ =
      G * (s.sum fun a =>
        sigma * ((t a).sum fun b =>
          A a b / (beta a b * sp a b ^ 2 * prevP a b))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      G * (sigma * (s.sum fun a =>
        ((t a).sum fun b =>
          A a b / (beta a b * sp a b ^ 2 * prevP a b)))) := by
          congr 1
          rw [Finset.mul_sum]
    _ =
      sigma * G *
        (s.sum fun a =>
          ((t a).sum fun b =>
            A a b / (beta a b * sp a b ^ 2 * prevP a b))) := by
          ring

/-- Exact outer-coefficient version of the `quadraticMean = quadraticScale`
normalization in Lan Eq. (8.1.71).

This specializes the preceding algebra helper to the shape used by the SGS proof,
where the outer `k` coefficient multiplies the inner `i` sum before the
`σ²` factor is pulled out. -/
theorem nested_quadratic_mean_scale_algebra_outer
    {α β : Type*} (s : Finset α) (t : α → Finset β)
    (G sigma : ℝ) (C : α → ℝ) (beta sp prevP : α → β → ℝ) :
    G * (s.sum fun a =>
      C a * ((t a).sum fun b =>
        (sp a b * prevP a b)⁻¹ * (sigma / (beta a b * sp a b)))) =
      sigma * G *
        (s.sum fun a =>
          ((t a).sum fun b =>
            C a / (beta a b * sp a b ^ 2 * prevP a b))) := by
  classical
  have hpoint : ∀ a b,
      C a * ((sp a b * prevP a b)⁻¹ *
          (sigma / (beta a b * sp a b))) =
        sigma * (C a / (beta a b * sp a b ^ 2 * prevP a b)) := by
    intro a b
    ring_nf
  calc
    G * (s.sum fun a =>
      C a * ((t a).sum fun b =>
        (sp a b * prevP a b)⁻¹ * (sigma / (beta a b * sp a b))))
        =
      G * (s.sum fun a =>
        ((t a).sum fun b =>
          C a * ((sp a b * prevP a b)⁻¹ *
            (sigma / (beta a b * sp a b))))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      G * (s.sum fun a =>
        ((t a).sum fun b =>
          sigma * (C a / (beta a b * sp a b ^ 2 * prevP a b)))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          refine Finset.sum_congr rfl ?_
          intro b _hb
          exact hpoint a b
    _ =
      G * (s.sum fun a =>
        sigma * ((t a).sum fun b =>
          C a / (beta a b * sp a b ^ 2 * prevP a b))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      G * (sigma * (s.sum fun a =>
        ((t a).sum fun b =>
          C a / (beta a b * sp a b ^ 2 * prevP a b)))) := by
          congr 1
          rw [Finset.mul_sum]
    _ =
      sigma * G *
        (s.sum fun a =>
          ((t a).sum fun b =>
            C a / (beta a b * sp a b ^ 2 * prevP a b))) := by
          ring

/-- Fully expanded denominator version of the `quadraticMean = quadraticScale`
normalization used by the SGS Theorem 8.2 high-probability proof.

This is the literal coefficient form in Lan Eq. (8.1.71), with the outer
denominator kept separate from the inner `β p_i^2 P_{i-1}` denominator. -/
theorem nested_quadratic_mean_scale_algebra_coeff
    {α β : Type*} (s : Finset α) (t : α → Finset β)
    (G sigma : ℝ) (C D E : α → ℝ) (B sp prevP : α → β → ℝ) :
    G * (s.sum fun a =>
      C a / (D a * E a) * ((t a).sum fun b =>
        (sp a b * prevP a b)⁻¹ * (sigma / (B a b * sp a b)))) =
      sigma * G *
        (s.sum fun a =>
          ((t a).sum fun b =>
            C a / ((B a b * D a * E a) * sp a b ^ 2 * prevP a b))) := by
  classical
  have hpoint : ∀ a b,
      C a / (D a * E a) * ((sp a b * prevP a b)⁻¹ *
          (sigma / (B a b * sp a b))) =
        sigma * (C a / ((B a b * D a * E a) * sp a b ^ 2 * prevP a b)) := by
    intro a b
    ring_nf
  calc
    G * (s.sum fun a =>
      C a / (D a * E a) * ((t a).sum fun b =>
        (sp a b * prevP a b)⁻¹ * (sigma / (B a b * sp a b))))
        =
      G * (s.sum fun a =>
        ((t a).sum fun b =>
          C a / (D a * E a) * ((sp a b * prevP a b)⁻¹ *
            (sigma / (B a b * sp a b))))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      G * (s.sum fun a =>
        ((t a).sum fun b =>
          sigma * (C a / ((B a b * D a * E a) * sp a b ^ 2 * prevP a b)))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          refine Finset.sum_congr rfl ?_
          intro b _hb
          exact hpoint a b
    _ =
      G * (s.sum fun a =>
        sigma * ((t a).sum fun b =>
          C a / ((B a b * D a * E a) * sp a b ^ 2 * prevP a b))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          rw [Finset.mul_sum]
    _ =
      G * (sigma * (s.sum fun a =>
        ((t a).sum fun b =>
          C a / ((B a b * D a * E a) * sp a b ^ 2 * prevP a b)))) := by
          congr 1
          rw [Finset.mul_sum]
    _ =
      sigma * G *
        (s.sum fun a =>
          ((t a).sum fun b =>
            C a / ((B a b * D a * E a) * sp a b ^ 2 * prevP a b))) := by
          ring

/-- Pure nested finite-sum algebra for the Lan Eq. (8.1.69) bracket split.

Candidate audit: considered the pre-searched SOptLib probability/filtration and
descent candidates, target-file high-probability helpers, and Mathlib
`Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, and `Finset.mul_sum`.
Those APIs distribute sums and products but do not package this pointwise
weighted split of `(M^2 + q)/d + l` into deterministic, linear, realized
quadratic, and centered quadratic parts, so this route-local scalar lemma is
used directly for Lan Theorem 8.2 after Eq. (8.1.69). -/
theorem nested_weighted_master_bracket_decomp
    {α β : Type*} (s : Finset α) (t : α → Finset β)
    (G : ℝ) (C : α → ℝ) (I D M2 Q Sigma L : α → β → ℝ) :
    G * (s.sum fun a =>
      C a * ((t a).sum fun b => I a b * (((M2 a b + Q a b) / D a b) + L a b))) =
        G * (s.sum fun a =>
          C a * ((t a).sum fun b => I a b * ((M2 a b + Sigma a b) / D a b))) +
        G * (s.sum fun a =>
          C a * ((t a).sum fun b => I a b * L a b)) +
        (G * (s.sum fun a =>
            C a * ((t a).sum fun b => I a b * (Q a b / D a b))) -
          G * (s.sum fun a =>
            C a * ((t a).sum fun b => I a b * (Sigma a b / D a b)))) := by
  have hpoint :
      ∀ a b,
        I a b * (((M2 a b + Q a b) / D a b) + L a b) =
          I a b * ((M2 a b + Sigma a b) / D a b) +
            I a b * L a b +
              (I a b * (Q a b / D a b) - I a b * (Sigma a b / D a b)) := by
    intro a b
    ring_nf
  calc
    G * (s.sum fun a =>
      C a * ((t a).sum fun b => I a b * (((M2 a b + Q a b) / D a b) + L a b)))
        = G * (s.sum fun a =>
          C a * ((t a).sum fun b =>
            I a b * ((M2 a b + Sigma a b) / D a b) +
              I a b * L a b +
                (I a b * (Q a b / D a b) - I a b * (Sigma a b / D a b)))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          congr 1
          refine Finset.sum_congr rfl ?_
          intro b _hb
          exact hpoint a b
    _ = G * (s.sum fun a =>
          C a * (((t a).sum fun b => I a b * ((M2 a b + Sigma a b) / D a b)) +
            ((t a).sum fun b => I a b * L a b) +
              (((t a).sum fun b => I a b * (Q a b / D a b)) -
                ((t a).sum fun b => I a b * (Sigma a b / D a b))))) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = G * (s.sum fun a =>
          (C a * ((t a).sum fun b => I a b * ((M2 a b + Sigma a b) / D a b)) +
            C a * ((t a).sum fun b => I a b * L a b) +
              (C a * ((t a).sum fun b => I a b * (Q a b / D a b)) -
                C a * ((t a).sum fun b => I a b * (Sigma a b / D a b))))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro a _ha
          ring
    _ = G * (s.sum fun a =>
          C a * ((t a).sum fun b => I a b * ((M2 a b + Sigma a b) / D a b))) +
        G * (s.sum fun a =>
          C a * ((t a).sum fun b => I a b * L a b)) +
        (G * (s.sum fun a =>
            C a * ((t a).sum fun b => I a b * (Q a b / D a b))) -
          G * (s.sum fun a =>
            C a * ((t a).sum fun b => I a b * (Sigma a b / D a b)))) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          ring

/-- Zero-light-scale transfer for the SGS linear martingale increment.

This is the deterministic branch needed by the Eq. (8.1.70) one-step adapter.
It avoids interpreting the totalized quotient `ζ^2 / 0` as source content:
when `sigmaSq = 0`, generated light-tail gives zero oracle noise a.e.; when
`sigmaSq > 0`, a zero light scale forces the compact Bregman envelope to vanish,
and the envelope displacement bound makes the comparator displacement zero
pointwise. -/
theorem theorem82_linear_zero_of_zero_lightScale
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (uStar : FeasiblePoint S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hcompact : IsCompact S.X)
    (hquery_mem :
      ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X)
    (hgenerated_light :
      generatedSFOLightTail S law.P law.sample
        (sgsGeneratedOracleQuery S inner)) :
    ∀ κ i,
      let ζ : Ω → ℝ := fun ω =>
        ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
            (law.sample κ i ω),
          uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
      let lightScale : ℝ :=
        2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
      lightScale = 0 → ζ =ᵐ[law.P] 0 := by
  classical
  intro κ i
  dsimp
  intro hscale
  by_cases hsigma_zero : S.sigmaSq = 0
  · rcases hgenerated_light with ⟨_hquery_light, hlight_pos | hlight_det⟩
    · exact False.elim ((ne_of_gt hlight_pos.1) hsigma_zero)
    · have hzero_dual :
          ∀ᵐ ω ∂law.P,
            dualNorm S
              (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω)) = 0 := by
        exact hlight_det.2 κ i
      filter_upwards [hzero_dual] with ω hzero
      have habs :=
        abs_inner_le_dualNorm_mul_primalNorm S
          (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
            (law.sample κ i ω))
          (uStar.1 - sgsGeneratedOracleQuery S inner κ i ω)
      have hle0 :
          |⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ| ≤ 0 := by
        simpa [hzero] using habs
      have habs0 :
          |⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ| = 0 :=
        le_antisymm hle0 (abs_nonneg _)
      exact abs_eq_zero.mp habs0
  · have hsigma_pos : 0 < S.sigmaSq :=
      lt_of_le_of_ne S.sigmaSq_nonneg (Ne.symm hsigma_zero)
    have henv_nonneg :
        0 ≤ bregmanEnvelope_formulaExtension S uStar hcompact :=
      bregmanEnvelope_formulaExtension_nonneg S uStar hcompact
    have henv_zero :
        bregmanEnvelope_formulaExtension S uStar hcompact = 0 := by
      nlinarith [hscale, henv_nonneg, hsigma_pos]
    filter_upwards with ω
    let q : FeasiblePoint S :=
      ⟨sgsGeneratedOracleQuery S inner κ i ω, hquery_mem κ i ω⟩
    have hdisp :
        S.primalNorm (uStar.1 - q.1) ^ 2 ≤
          2 * bregmanEnvelope_formulaExtension S uStar hcompact :=
      primal_displacement_sq_le_two_bregmanEnvelope_formulaExtension
        S uStar q hcompact
    have hsq_zero : S.primalNorm (uStar.1 - q.1) ^ 2 = 0 := by
      have hle0 : S.primalNorm (uStar.1 - q.1) ^ 2 ≤ 0 := by
        simpa [henv_zero] using hdisp
      exact le_antisymm hle0 (sq_nonneg _)
    have hnorm_zero : S.primalNorm (uStar.1 - q.1) = 0 :=
      sq_eq_zero_iff.mp hsq_zero
    have hvec_zero : uStar.1 - q.1 = 0 :=
      (primalNorm_isSeparating S (uStar.1 - q.1)).mp hnorm_zero
    simpa [q, hvec_zero] using
      (inner_zero_right
        (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
          (law.sample κ i ω)) : ⟪oracleNoiseAt S
            (sgsGeneratedOracleQuery S inner κ i ω) (law.sample κ i ω),
          (0 : E)⟫_ℝ = 0)

set_option maxHeartbeats 0


end StochasticGradientSliding
