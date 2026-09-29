import Algorithms.Unverified.StochasticGradientSliding.Part004
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

/-- Weighted affine-pairing absorption for the repaired averaged-output
reverse gap.

This is the lower-level obstruction behind the selected proof hole: expand the
Eq. (8.1.24) average, apply Young/Bregman absorption to the terminal SPS query
with coefficient `propCoeff / 2`, and put only previous-window Bregman terms
into the repaired Cgap.  Candidate audit: the local
`fixed_linear_pairing_bregman_absorb_with_epsilon_explicit`,
`sps_normalized_weight_eq`, and `sps_normalized_weight_sum_eq_one` are the
matching primitives; SOptLib telescope/variance helpers do not expose the
terminal-vs-previous split or the reciprocal-`propCoeff` smooth-slope budget. -/
theorem selected_sgs_inner_average_phi_reverse_gap_repairedCgap_pairing_bound
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ) (χa : ℝ) (χb : E) :
    let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
    let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
    let Vnext : Ω → ℝ := fun ω =>
      bregmanFormulaOnX S
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
          hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
        x
    ∀ ω,
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      let inner :=
        sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
          law.sample κ
      let totalSlope : E := sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb
      ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ +
          (beta κ * bregmanFormulaOnX S outerPrev.x x +
            (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)) ≤
        (propCoeff / 2) * Vnext ω +
          selected_sgs_inner_average_phi_reverse_gap_repairedCgap
            (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j χa χb ω := by
  classical
  dsimp
  intro ω
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  have hOneSub : 0 < 1 - psWeightProduct spsP t.1 :=
    one_sub_psWeightProduct_spsP_pos_of_pos t.2
  have hpropCoeff_pos : 0 < propCoeff := by
    dsimp [propCoeff]
    exact mul_pos (hbeta κ) (inv_pos.mpr hOneSub)
  let outerPrev :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
      (κ.1 - 1) ω
  let xUnder := outerExtrapolation S gamma κ outerPrev
  let inner :=
    sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
  let C : ℝ := psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹
  let w : ℕ → ℝ := fun i =>
    (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹
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
  have havg_closed :
      (inner t.1 ω).avg.1 =
        (psWeightProduct spsP t.1 *
            (1 - psWeightProduct spsP t.1)⁻¹) •
          (Finset.range t.1).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
              (inner (i + 1) ω).u.1) := by
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let hgk : IsAffineModel gk := smoothLinearization_isAffineModel S xUnder
    let states :=
      spsProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩ (law.sample κ)
    have hprocess : IsSPSProcess S gk outerPrev.x (beta κ) (law.sample κ) states := by
      simpa [states] using
        spsProcess_isSPSProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩
          (law.sample κ)
    simpa [t, gk, hgk, outerPrev, xUnder, states, inner,
      sgsInnerProcess_formulaExtensionSelector] using
      sps_avg_eq_weighted_sum S gk outerPrev.x (beta κ) (law.sample κ)
        states hprocess ω t
  have havg_weighted :
      (inner t.1 ω).avg.1 =
        (Finset.range t.1).sum (fun i =>
          (C * w i) • (inner (i + 1) ω).u.1) := by
    calc
      (inner t.1 ω).avg.1 =
          C • (Finset.range t.1).sum (fun i =>
            w i • (inner (i + 1) ω).u.1) := by
            simpa [C, w] using havg_closed
      _ = (Finset.range t.1).sum (fun i =>
            (C * w i) • (inner (i + 1) ω).u.1) := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [smul_smul]
  have hx_minus_avg :
      x.1 - (inner t.1 ω).avg.1 =
        (Finset.range t.1).sum (fun i =>
          (C * w i) • (x.1 - (inner (i + 1) ω).u.1)) := by
    have hx_as_sum :
        x.1 = (Finset.range t.1).sum (fun i => (C * w i) • x.1) := by
      rw [← Finset.sum_smul, hqsum, one_smul]
    calc
      x.1 - (inner t.1 ω).avg.1 =
          (Finset.range t.1).sum (fun i => (C * w i) • x.1) -
            (Finset.range t.1).sum (fun i =>
              (C * w i) • (inner (i + 1) ω).u.1) := by
            rw [havg_weighted]
            conv_lhs => rw [hx_as_sum]
      _ = (Finset.range t.1).sum (fun i =>
            (C * w i) • x.1 - (C * w i) • (inner (i + 1) ω).u.1) := by
            rw [Finset.sum_sub_distrib]
      _ = (Finset.range t.1).sum (fun i =>
            (C * w i) • (x.1 - (inner (i + 1) ω).u.1)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [smul_sub]
  have hpair_sum_formula :
      ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
          x.1 - (inner t.1 ω).avg.1⟫_ℝ =
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
              x.1 - (inner (i + 1) ω).u.1⟫_ℝ) := by
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
  have hterminal_eps_pos : 0 < propCoeff / (2 * (C * w j)) := by
    positivity
  have hprev_eps_pos :
      ∀ i ∈ Finset.range j, 0 < propCoeff / (4 * (j + 1 : ℝ) * (C * w i)) := by
    intro i hi
    have hit : i ∈ Finset.range t.1 := by
      have hi_lt : i < j := Finset.mem_range.mp hi
      simp [t]
      omega
    have hqi := hq_pos_of_mem i hit
    positivity
  have hpair_sum_split :
      (Finset.range t.1).sum (fun i =>
          (C * w i) *
            ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
              x.1 - (inner (i + 1) ω).u.1⟫_ℝ) =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
              x.1 - (inner (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
              x.1 - (inner (j + 1) ω).u.1⟫_ℝ := by
    simpa [t] using
      (Finset.sum_range_succ (fun i =>
        (C * w i) *
          ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
            x.1 - (inner (i + 1) ω).u.1⟫_ℝ) j)
  let totalSlope : E := sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb
  have hterminal_young :
      (C * w j) *
          ⟪totalSlope, x.1 - (inner (j + 1) ω).u.1⟫_ℝ ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
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
        (S := S) x totalSlope heps (inner (j + 1) ω).u
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
      field_simp [eps, ne_of_gt hqj', ne_of_gt hpropCoeff_pos]
    calc
      (C * w j) *
          ⟪totalSlope, x.1 - (inner (j + 1) ω).u.1⟫_ℝ
          = qj * ⟪totalSlope, x.1 - (inner (j + 1) ω).u.1⟫_ℝ := by
            rfl
      _ ≤ qj *
              (eps * bregmanFormulaOnX S (inner (j + 1) ω).u x +
                dualNorm S totalSlope ^ 2 / (2 * eps)) := by
            simpa [eps] using hmul
      _ =
          qj * eps * bregmanFormulaOnX S (inner (j + 1) ω).u x +
            qj * (dualNorm S totalSlope ^ 2 / (2 * eps)) := by
            ring
      _ =
          (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
            qj ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff := by
            rw [hcoefV, hcoefD]
      _ =
          (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
            (C * w j) ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff := by
            simp [qj]
  have hprev_young_sum_raw :
      (Finset.range j).sum (fun i =>
          (C * w i) * ⟪totalSlope, x.1 - (inner (i + 1) ω).u.1⟫_ℝ) ≤
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner (i + 1) ω).u x +
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
        (S := S) x (inner (i + 1) ω).u totalSlope
        (propCoeff := propCoeff) (n := (j + 1 : ℝ)) (q := C * w i)
        hpropCoeff_pos hn hqi)
  have hprev_young_sum :
      (Finset.range j).sum (fun i =>
          (C * w i) * ⟪totalSlope, x.1 - (inner (i + 1) ω).u.1⟫_ℝ) ≤
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner (i + 1) ω).u x) +
          (2 * (j + 1 : ℝ) *
              (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff := by
    calc
      (Finset.range j).sum (fun i =>
          (C * w i) * ⟪totalSlope, x.1 - (inner (i + 1) ω).u.1⟫_ℝ)
          ≤
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner (i + 1) ω).u x +
            2 * (j + 1 : ℝ) * (C * w i) ^ 2 *
              dualNorm S totalSlope ^ 2 / propCoeff) := hprev_young_sum_raw
      _ =
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner (i + 1) ω).u x) +
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
  have hpair_sum_split_total :
      ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, x.1 - (inner (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪totalSlope, x.1 - (inner (j + 1) ω).u.1⟫_ℝ := by
    calc
      ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ =
          ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
            x.1 - (inner t.1 ω).avg.1⟫_ℝ := by
            rfl
      _ =
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
              x.1 - (inner (i + 1) ω).u.1⟫_ℝ) := hpair_sum_formula
      _ =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
              x.1 - (inner (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb,
              x.1 - (inner (j + 1) ω).u.1⟫_ℝ := hpair_sum_split
      _ =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, x.1 - (inner (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪totalSlope, x.1 - (inner (j + 1) ω).u.1⟫_ℝ := by
            rfl
  have hpair_young_bound :
      ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ ≤
        (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
          (Finset.range j).sum (fun i =>
            (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner (i + 1) ω).u x) +
          (((C * w j) ^ 2 +
              2 * (j + 1 : ℝ) *
                (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff) := by
    calc
      ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ =
        (Finset.range j).sum (fun i =>
          (C * w i) *
            ⟪totalSlope, x.1 - (inner (i + 1) ω).u.1⟫_ℝ) +
          (C * w j) *
            ⟪totalSlope, x.1 - (inner (j + 1) ω).u.1⟫_ℝ := hpair_sum_split_total
      _ ≤
        ((Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner (i + 1) ω).u x) +
          (2 * (j + 1 : ℝ) *
              (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff) +
          ((propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
            (C * w j) ^ 2 * dualNorm S totalSlope ^ 2 / propCoeff) := by
          exact add_le_add hprev_young_sum hterminal_young
      _ =
        (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
          (Finset.range j).sum (fun i =>
            (propCoeff / (4 * (j + 1 : ℝ))) *
              bregmanFormulaOnX S (inner (i + 1) ω).u x) +
          (((C * w j) ^ 2 +
              2 * (j + 1 : ℝ) *
                (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
            dualNorm S totalSlope ^ 2 / propCoeff) := by
          ring
  let residual : ℝ :=
    beta κ * bregmanFormulaOnX S outerPrev.x x +
      (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)
  let qsqBudget : ℝ :=
    (C * w j) ^ 2 +
      2 * (j + 1 : ℝ) * (Finset.range j).sum (fun i => (C * w i) ^ 2)
  let smoothCgap : ℝ :=
    selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap
      (S := S) law x0 x beta gamma T hbeta hgamma κ (propCoeff / 2) χa χb ω
  have hsmooth_dom :
      dualNorm S totalSlope ^ 2 / propCoeff + |residual| ≤ smoothCgap := by
    have hgrad_lip :
        ∀ x y : FeasiblePoint S,
          dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) ≤
            S.lSmooth * S.primalNorm (y.1 - x.1) :=
      sourceSmoothGradient_dual_lipschitz_from_smoothness (S := S)
    have heps : 0 < propCoeff / 2 := by positivity
    have hdom :=
      selected_sgs_inner_average_phi_reverse_gap_explicitCgap_le_smoothUpperCgap
        (S := S) law x0 x beta gamma T hbeta hgamma κ
        (eps := propCoeff / 2) heps χa χb hgrad_lip ω
    have hden : 2 * (propCoeff / 2) = propCoeff := by ring
    simpa [smoothCgap, selected_sgs_inner_average_phi_reverse_gap_explicitCgap,
      residual, totalSlope, outerPrev, xUnder, hden] using hdom
  have hDpart_nonneg : 0 ≤ dualNorm S totalSlope ^ 2 / propCoeff := by
    exact div_nonneg (sq_nonneg _) hpropCoeff_pos.le
  have hqsq_nonneg : 0 ≤ qsqBudget := by
    have hsum_nonneg :
        0 ≤ (Finset.range j).sum (fun i => (C * w i) ^ 2) := by
      exact Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hscale_nonneg :
        0 ≤ 2 * (j + 1 : ℝ) *
          (Finset.range j).sum (fun i => (C * w i) ^ 2) := by
      positivity
    dsimp [qsqBudget]
    nlinarith [sq_nonneg (C * w j), hscale_nonneg]
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
  calc
    ⟪sourceSmoothGradient S
              (outerExtrapolation S gamma κ
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
                  (κ.1 - 1) ω)) +
            S.hSubgradient x.1 +
          χb,
        x.1 -
          (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
            κ (j + 1) ω).avg.1⟫_ℝ +
      (beta κ *
          bregmanFormulaOnX S
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
              (κ.1 - 1) ω).x x +
        (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ))
        =
      ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ + residual := by
        simp [residual, totalSlope, outerPrev, xUnder, inner, t]
    _ ≤
      (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
            bregmanFormulaOnX S (inner (i + 1) ω).u x) +
        (qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual) := by
        have hbudget_rewrite :
            (((C * w j) ^ 2 +
                2 * (j + 1 : ℝ) *
                  (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
              dualNorm S totalSlope ^ 2 / propCoeff) =
              qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) := by
          dsimp [qsqBudget]
          ring
        calc
          ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ + residual
              ≤
            (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
                (Finset.range j).sum (fun i =>
                  (propCoeff / (4 * (j + 1 : ℝ))) *
                    bregmanFormulaOnX S (inner (i + 1) ω).u x) +
              (((C * w j) ^ 2 +
                  2 * (j + 1 : ℝ) *
                    (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
                dualNorm S totalSlope ^ 2 / propCoeff) +
              residual := by
              have hbase := add_le_add_right hpair_young_bound residual
              calc
                ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ + residual =
                    residual + ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ := by
                    ring
                _ ≤
                    residual +
                      ((propCoeff / 2) *
                          bregmanFormulaOnX S (inner (j + 1) ω).u x +
                        (Finset.range j).sum (fun i =>
                          (propCoeff / (4 * (j + 1 : ℝ))) *
                            bregmanFormulaOnX S (inner (i + 1) ω).u x) +
                        (((C * w j) ^ 2 +
                            2 * (j + 1 : ℝ) *
                              (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
                          dualNorm S totalSlope ^ 2 / propCoeff)) := hbase
                _ =
                    (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
                      (Finset.range j).sum (fun i =>
                        (propCoeff / (4 * (j + 1 : ℝ))) *
                          bregmanFormulaOnX S (inner (i + 1) ω).u x) +
                    (((C * w j) ^ 2 +
                        2 * (j + 1 : ℝ) *
                          (Finset.range j).sum (fun i => (C * w i) ^ 2)) *
                      dualNorm S totalSlope ^ 2 / propCoeff) +
                    residual := by
                    ring
          _ =
            (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S (inner (i + 1) ω).u x) +
              (qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual) := by
              rw [hbudget_rewrite]
              ring
    _ ≤
      (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
        (Finset.range j).sum (fun i =>
          (propCoeff / (4 * (j + 1 : ℝ))) *
            bregmanFormulaOnX S (inner (i + 1) ω).u x) +
        (1 + qsqBudget) * smoothCgap := by
        let fixedTerms : ℝ :=
          (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
            (Finset.range j).sum (fun i =>
              (propCoeff / (4 * (j + 1 : ℝ))) *
                bregmanFormulaOnX S (inner (i + 1) ω).u x)
        have hbase := add_le_add_left hbudget_absorb fixedTerms
        calc
          (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S (inner (i + 1) ω).u x) +
            (qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual)
              =
            qsqBudget * (dualNorm S totalSlope ^ 2 / propCoeff) + residual +
              fixedTerms := by
              dsimp [fixedTerms]
              ring
          _ ≤ (1 + qsqBudget) * smoothCgap + fixedTerms := hbase
          _ =
            (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S (inner (i + 1) ω).u x) +
              (1 + qsqBudget) * smoothCgap := by
              dsimp [fixedTerms]
              ring
    _ =
      beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2 *
          bregmanFormulaOnX S
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
              hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) x +
        selected_sgs_inner_average_phi_reverse_gap_repairedCgap
          S law x0 x beta gamma T hbeta hgamma hquery_mem κ j χa χb ω := by
        change
          (propCoeff / 2) * bregmanFormulaOnX S (inner (j + 1) ω).u x +
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S (inner (i + 1) ω).u x) +
            (1 + qsqBudget) * smoothCgap =
          beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2 *
              bregmanFormulaOnX S
                (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
                  hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) x +
            ((1 + qsqBudget) * smoothCgap +
              (Finset.range j).sum (fun i =>
                (propCoeff / (4 * (j + 1 : ℝ))) *
                  bregmanFormulaOnX S
                    (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
                      hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S) x))
        have hcoeff :
            propCoeff / 2 =
              beta κ * (1 - psWeightProduct spsP (j + 1))⁻¹ / 2 := by
          simp [propCoeff, t]
        have hterm_point :
            (inner (j + 1) ω).u =
              (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
                hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) := by
          apply Subtype.ext
          simp [sgsOracleQuery, inner]
        have hterm_breg :
            bregmanFormulaOnX S (inner (j + 1) ω).u x =
              bregmanFormulaOnX S
                (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
                  hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) x := by
          rw [hterm_point]
        have hprev_breg :
            (Finset.range j).sum (fun i =>
              (propCoeff / (4 * (j + 1 : ℝ))) *
                bregmanFormulaOnX S (inner (i + 1) ω).u x) =
            (Finset.range j).sum (fun i =>
              (propCoeff / (4 * (j + 1 : ℝ))) *
                bregmanFormulaOnX S
                  (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
                    hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S) x) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hpoint :
              (inner (i + 1) ω).u =
                (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
                  hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S) := by
            apply Subtype.ext
            simp [sgsOracleQuery, inner]
          rw [hpoint]
        rw [hcoeff, hterm_breg, hprev_breg]
        ring

/-- Integrability of the repaired selected reverse-gap Cgap.

This is the measure-theoretic companion to the repaired affine-pairing bridge:
the smooth-slope part is handled by
`selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap_integrable_of_dual_lipschitz`,
and the only Bregman terms are the previous-window queries already supplied to
the successor induction. -/
theorem selected_sgs_inner_average_phi_reverse_gap_repairedCgap_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω,
          hquery_mem k i ω⟩ : FeasiblePoint S)))
    (κ : PositiveTime) (j : ℕ) (χa : ℝ) (χb : E)
    (houter_xbar_sq :
      Integrable
        (fun ω =>
          let outerPrev :=
            sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
              (κ.1 - 1) ω
          S.primalNorm (x.1 - outerPrev.xbar.1) ^ 2)
        law.P)
    (hprev_window :
      ∀ i, i < j + 1 →
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              x)
          law.P) :
    Integrable
      (selected_sgs_inner_average_phi_reverse_gap_repairedCgap
        (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j χa χb)
      law.P := by
  classical
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let C : ℝ := psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹
  let w : ℕ → ℝ := fun i =>
    (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹
  let qsqBudget : ℝ :=
    (C * w j) ^ 2 +
      2 * (j + 1 : ℝ) * (Finset.range j).sum (fun i => (C * w i) ^ 2)
  let smoothCgap : Ω → ℝ :=
    selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap
      (S := S) law x0 x beta gamma T hbeta hgamma κ (propCoeff / 2) χa χb
  let scaledPrevBregSum : Ω → ℝ := fun ω =>
    (Finset.range j).sum (fun i =>
      (propCoeff / (4 * (j + 1 : ℝ))) *
        bregmanFormulaOnX S
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
            hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S)
          x)
  have hOneSub : 0 < 1 - psWeightProduct spsP t.1 :=
    one_sub_psWeightProduct_spsP_pos_of_pos t.2
  have hpropCoeff_pos : 0 < propCoeff := by
    dsimp [propCoeff]
    exact mul_pos (hbeta κ) (inv_pos.mpr hOneSub)
  have heps : 0 < propCoeff / 2 := by positivity
  have hsmooth_int : Integrable smoothCgap law.P := by
    simpa [smoothCgap] using
      selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap_integrable_of_dual_lipschitz
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas κ j heps χa χb houter_xbar_sq hprev_window
  have hscaledPrevBregSum_int : Integrable scaledPrevBregSum law.P := by
    refine integrable_finset_sum (Finset.range j) ?_
    intro i hi
    have hi_lt : i + 1 < j + 1 := by
      exact Nat.succ_lt_succ (Finset.mem_range.mp hi)
    exact (hprev_window (i + 1) hi_lt).const_mul
      (propCoeff / (4 * (j + 1 : ℝ)))
  have htotal :
      Integrable (fun ω => (1 + qsqBudget) * smoothCgap ω + scaledPrevBregSum ω)
        law.P :=
    (hsmooth_int.const_mul (1 + qsqBudget)).add hscaledPrevBregSum_int
  refine htotal.congr (Filter.Eventually.of_forall ?_)
  intro ω
  simp [selected_sgs_inner_average_phi_reverse_gap_repairedCgap, smoothCgap,
    scaledPrevBregSum, qsqBudget, C, w, propCoeff, t]

/-- Concrete split witness for the selected averaged-output reverse `Phi` gap.

This is the direct Proposition 8.3 step-3 bridge requested by the active
frontier.  Candidate audit: the pre-searched weighted-variance/telescope
helpers in `SOptLib/Glue/Algebra.lean` and `SOptLib/Layer1/Telescope.lean`
package generic weighted averages or telescopes, but none combines the SGS
fixed-slope reverse-gap decomposition with the paper-local split Cgap below;
the existing local `sps_avg_eq_weighted_sum`,
`spsPhiFormulaOnX_reverse_gap_decompose_fixed_slope`, and
`bregmanFormulaOnX_lower_bound_from_prox_geometry` are the aligned route. -/
theorem selected_sgs_inner_average_phi_reverse_gap_splitCgap_pointwise
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ) (χa : ℝ) (χb : E)
    (hχminor : ∀ y : {x : E // x ∈ S.X}, χa + ⟪χb, y.1⟫_ℝ ≤ S.chi y.1) :
    let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
    let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
    let fixedSlope : E := sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb
    let squareCoeff : ℝ :=
      1 + S.lSmooth ^ 2 + dualNorm S fixedSlope ^ 2 + propCoeff
    let χresidual : ℝ := S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ
    let Vnext : Ω → ℝ := fun ω =>
      bregmanFormulaOnX S
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
          hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
        x
    let Φavg : Ω → ℝ := fun ω =>
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      let inner :=
        sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
        (inner t.1 ω).avg
    let Φu : Ω → ℝ := fun ω =>
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) x
    ∀ ω,
      Φu ω - Φavg ω ≤
        (propCoeff / 2) * Vnext ω +
          selected_sgs_inner_average_phi_reverse_gap_repairedCgap
            (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j χa χb ω := by
  classical
  dsimp
  intro ω
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let outerPrev :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
      (κ.1 - 1) ω
  let xUnder := outerExtrapolation S gamma κ outerPrev
  let inner :=
    sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let fixedSlope : E := sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb
  have hdecomp :=
    spsPhiFormulaOnX_reverse_gap_decompose_fixed_slope
      (S := S) x outerPrev.x (inner t.1 ω).avg xUnder
      (hbeta κ).le χa χb hχminor
  have havg_closed :
      (inner t.1 ω).avg.1 =
        (psWeightProduct spsP t.1 *
            (1 - psWeightProduct spsP t.1)⁻¹) •
          (Finset.range t.1).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
              (inner (i + 1) ω).u.1) := by
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let hgk : IsAffineModel gk := smoothLinearization_isAffineModel S xUnder
    let states :=
      spsProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩ (law.sample κ)
    have hprocess : IsSPSProcess S gk outerPrev.x (beta κ) (law.sample κ) states := by
      simpa [states] using
        spsProcess_isSPSProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩
          (law.sample κ)
    simpa [t, gk, hgk, outerPrev, xUnder, states, inner,
      sgsInnerProcess_formulaExtensionSelector] using
      sps_avg_eq_weighted_sum S gk outerPrev.x (beta κ) (law.sample κ)
        states hprocess ω t
  have hxUnder_mem : xUnder ∈ S.X := by
    dsimp [xUnder, outerExtrapolation]
    exact convexCombination_mem_X S outerPrev.xbar outerPrev.x (hgamma κ).1 (hgamma κ).2
  have hsmooth_resid :
      smoothLinearization S xUnder x.1 -
          smoothLinearization S xUnder (inner t.1 ω).avg.1 -
          ⟪sourceSmoothGradient S x.1, x.1 - (inner t.1 ω).avg.1⟫_ℝ ≤
        (S.lSmooth / 2) *
          S.primalNorm ((inner t.1 ω).avg.1 - xUnder) ^ 2 := by
    exact smooth_linearization_reverse_residual_le_under_avg_square
      S x (inner t.1 ω).avg xUnder hxUnder_mem
  let C : ℝ := psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹
  let w : ℕ → ℝ := fun i =>
    (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹
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
  have hOneSub : 0 < 1 - psWeightProduct spsP t.1 :=
    one_sub_psWeightProduct_spsP_pos_of_pos t.2
  have hpropCoeff_pos : 0 < propCoeff := by
    dsimp [propCoeff]
    exact mul_pos (hbeta κ) (inv_pos.mpr hOneSub)
  have havg_weighted :
      (inner t.1 ω).avg.1 =
        (Finset.range t.1).sum (fun i =>
          (C * w i) • (inner (i + 1) ω).u.1) := by
    calc
      (inner t.1 ω).avg.1 =
          C • (Finset.range t.1).sum (fun i =>
            w i • (inner (i + 1) ω).u.1) := by
            simpa [C, w] using havg_closed
      _ = (Finset.range t.1).sum (fun i =>
            (C * w i) • (inner (i + 1) ω).u.1) := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [smul_smul]
  have havg_target_sq :
      S.primalNorm (x.1 - (inner t.1 ω).avg.1) ^ 2 ≤
        (Finset.range t.1).sum (fun i =>
          (C * w i) * S.primalNorm (x.1 - (inner (i + 1) ω).u.1) ^ 2) := by
    exact primalNorm_sq_weighted_average_sub_le_sum
      S x (Finset.range t.1) (fun i => C * w i)
      (fun i => (inner (i + 1) ω).u.1) (inner t.1 ω).avg.1
      hq_nonneg hqsum havg_weighted
  have havg_target_breg :
      S.primalNorm (x.1 - (inner t.1 ω).avg.1) ^ 2 ≤
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            (2 * bregmanFormulaOnX S (inner (i + 1) ω).u x)) := by
    refine havg_target_sq.trans ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    have hlower :=
      bregmanFormulaOnX_lower_bound_from_prox_geometry S (inner (i + 1) ω).u x
    have hsquare_le :
        S.primalNorm (x.1 - (inner (i + 1) ω).u.1) ^ 2 ≤
          2 * bregmanFormulaOnX S (inner (i + 1) ω).u x := by
      nlinarith
    exact mul_le_mul_of_nonneg_left hsquare_le (hq_nonneg i hi)
  have havg_under_sq :
      S.primalNorm ((inner t.1 ω).avg.1 - xUnder) ^ 2 ≤
        2 *
          (S.primalNorm (x.1 - (inner t.1 ω).avg.1) ^ 2 +
            S.primalNorm (x.1 - xUnder) ^ 2) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      primalNorm_sub_sq_le_two_sq_add S (inner t.1 ω).avg.1 x.1 xUnder
  have hsmooth_budget :
      smoothLinearization S xUnder x.1 -
          smoothLinearization S xUnder (inner t.1 ω).avg.1 -
          ⟪sourceSmoothGradient S x.1, x.1 - (inner t.1 ω).avg.1⟫_ℝ ≤
        S.lSmooth *
          ((Finset.range t.1).sum (fun i =>
            (C * w i) *
              (2 * bregmanFormulaOnX S (inner (i + 1) ω).u x)) +
            S.primalNorm (x.1 - xUnder) ^ 2) := by
    have hL_nonneg : 0 ≤ S.lSmooth := le_of_lt S.L_pos
    nlinarith [hsmooth_resid, havg_under_sq, havg_target_breg]
  have hfixed_budget :
      ⟪fixedSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ ≤
        (1 / 2 : ℝ) *
          (dualNorm S fixedSlope ^ 2 +
            (Finset.range t.1).sum (fun i =>
              (C * w i) *
                (2 * bregmanFormulaOnX S (inner (i + 1) ω).u x))) := by
    have hyoung :=
      dual_noise_young_square_control S fixedSlope
        (x.1 - (inner t.1 ω).avg.1)
    nlinarith [havg_target_breg]
  let totalSlope : E := sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb
  have hsmooth_exact :
      smoothLinearization S xUnder x.1 -
          smoothLinearization S xUnder (inner t.1 ω).avg.1 -
          ⟪sourceSmoothGradient S x.1, x.1 - (inner t.1 ω).avg.1⟫_ℝ =
        ⟪sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1,
          x.1 - (inner t.1 ω).avg.1⟫_ℝ := by
    simp [smoothLinearization, inner_sub_right, inner_sub_left]
    ring
  have hpair_sum :
      ⟪sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1,
          x.1 - (inner t.1 ω).avg.1⟫_ℝ +
        ⟪fixedSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ =
          ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ := by
    simp [fixedSlope, totalSlope, inner_add_left, inner_sub_left]
    ring
  have hgap_pair :
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) x -
          spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
            (inner t.1 ω).avg ≤
        ⟪totalSlope, x.1 - (inner t.1 ω).avg.1⟫_ℝ +
          (beta κ * bregmanFormulaOnX S outerPrev.x x +
            (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)) := by
    nlinarith [hdecomp, hsmooth_exact, hpair_sum]
  have hpair_absorb :=
    selected_sgs_inner_average_phi_reverse_gap_repairedCgap_pairing_bound
      (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j χa χb ω
  exact hgap_pair.trans (by simpa [t, propCoeff, outerPrev, xUnder, inner,
    totalSlope] using hpair_absorb)

/-- Pointwise averaged-output reverse gap envelope for the selected SGS inner call.

This is the non-measure-theoretic half of the rebuilt reverse-gap leaf.  The
constant is explicit rather than an existential/random `Classical.choose`, so
the measure-theoretic theorem can prove integrability term by term. -/
theorem selected_sgs_inner_average_phi_reverse_gap_pointwise_envelope
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ) :
    let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
    let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
    let Vnext : Ω → ℝ := fun ω =>
      bregmanFormulaOnX S
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
          hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
        x
    let Φavg : Ω → ℝ := fun ω =>
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      let inner :=
        sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
        (inner t.1 ω).avg
    let Φu : Ω → ℝ := fun ω =>
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) x
    ∃ Cgap : Ω → ℝ,
      ∀ ω, Φu ω - Φavg ω ≤ (propCoeff / 2) * Vnext ω + Cgap ω := by
  classical
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  obtain ⟨χa, χb, _hχminor⟩ :=
    convexOn_feasible_affine_minorant
      (X := S.X) S.convex_X (⟨x.1, x.2⟩ : {x : E // x ∈ S.X})
      S.chi S.convex_chi
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let Vnext : Ω → ℝ := fun ω =>
    bregmanFormulaOnX S
      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
        hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
      x
  let Φavg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    let inner :=
      sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
    spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
      (inner t.1 ω).avg
  let Φu : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) x
  have hOneSub : 0 < 1 - psWeightProduct spsP t.1 := by
    rw [psWeightProduct_spsP_eq t.1]
    have htpos : 0 < (t.1 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one t.2)
    have hDpos : 0 < (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) := by
      positivity
    have hrewrite :
        1 - 2 / (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) =
          ((t.1 : ℝ) * ((t.1 : ℝ) + 3)) /
            (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) := by
      field_simp [ne_of_gt hDpos]
      ring
    rw [hrewrite]
    exact div_pos (mul_pos htpos (by positivity)) hDpos
  have hpropCoeff : 0 < propCoeff := by
    dsimp [propCoeff]
    exact mul_pos (hbeta κ) (inv_pos.mpr hOneSub)
  let Cgap : Ω → ℝ :=
    selected_sgs_inner_average_phi_reverse_gap_repairedCgap
      (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j χa χb
  refine ⟨Cgap, ?_⟩
  simpa [Cgap, propCoeff, Vnext, Φavg, Φu, t] using
    selected_sgs_inner_average_phi_reverse_gap_splitCgap_pointwise
      (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j
      χa χb _hχminor

/-- Averaged-output reverse gap envelope for the selected SGS inner call.

This is the source-facing companion to Eq. (8.1.63): the proposition controls
the terminal Bregman term together with `Phi(tilde u_t)-Phi(u)`, so the
absorption step needs an integrable envelope for the reverse averaged-output
gap, not the stale terminal-iterate gap. -/
theorem selected_sgs_inner_average_phi_reverse_gap_integrable_envelope
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω,
          hquery_mem k i ω⟩ : FeasiblePoint S)))
    (hquery_core :
      ∀ k i ω,
        sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈
          proxCore S.X S.proxPotential)
    (hvar :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (κ : PositiveTime) (j : ℕ)
    (houter_xbar_sq :
      Integrable
        (fun ω =>
          let outerPrev :=
            sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
              (κ.1 - 1) ω
          S.primalNorm (x.1 - outerPrev.xbar.1) ^ 2)
        law.P)
    (hprev_window :
      ∀ i, i < j + 1 →
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              x)
          law.P) :
    let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
    let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
    let Vnext : Ω → ℝ := fun ω =>
      bregmanFormulaOnX S
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
          hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
        x
    let Φavg : Ω → ℝ := fun ω =>
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      let inner :=
        sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
        (inner t.1 ω).avg
    let Φu : Ω → ℝ := fun ω =>
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) x
    ∃ Cgap : Ω → ℝ,
      Integrable Cgap law.P ∧
        (∀ᵐ ω ∂law.P,
          Φu ω - Φavg ω ≤ (propCoeff / 2) * Vnext ω + Cgap ω) := by
  classical
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let Vnext : Ω → ℝ := fun ω =>
    bregmanFormulaOnX S
      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
        hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
      x
  let Φavg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    let inner :=
      sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
    spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
      (inner t.1 ω).avg
  let Φu : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) x
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  obtain ⟨χa, χb, hχminor⟩ :=
    convexOn_feasible_affine_minorant
      (X := S.X) S.convex_X (⟨x.1, x.2⟩ : {x : E // x ∈ S.X})
      S.chi S.convex_chi
  let Cgap : Ω → ℝ :=
    selected_sgs_inner_average_phi_reverse_gap_repairedCgap
      (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j χa χb
  have hCgap_pointwise :
      ∀ ω, Φu ω - Φavg ω ≤ (propCoeff / 2) * Vnext ω + Cgap ω := by
    simpa [Cgap, propCoeff, Vnext, Φavg, Φu, t] using
      selected_sgs_inner_average_phi_reverse_gap_splitCgap_pointwise
        (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j
        χa χb hχminor
  refine ⟨Cgap, ?_, ?_⟩
  ·
    simpa [Cgap] using
      selected_sgs_inner_average_phi_reverse_gap_repairedCgap_integrable
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas κ j χa χb
        houter_xbar_sq hprev_window
  ·
    simpa [propCoeff, Vnext, Φavg, Φu, t] using
      Filter.Eventually.of_forall hCgap_pointwise

/-- One-step Bregman integrability transfer for the selected SGS/SPS query.

Aligns with Lan Proposition 8.3, Eq. (8.1.61)-(8.1.63): the finite window of
previous-query Bregman integrability facts gives the L2 inputs needed for the
finite stochastic RHS, while the source one-step Phi/Bregman recurrence controls
the successor Bregman term.
Candidate audit: checked the pre-searched target helpers
`_voucher_step_sgsOracleQuery_successor_exposes_selected_phi_bregman_18`,
`query_sq_integrable_of_bregman_integrable`, and the affine-minorant helpers;
SOptLib's finite-window state-square induction is not imported here and its
two-component square-state shape does not provide this selected SGS
Bregman-transfer step. -/
theorem sgsOracleQuery_successor_bregman_integrable_of_prev_bregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω,
          hquery_mem k i ω⟩ : FeasiblePoint S)))
    (hquery_core :
      ∀ k i ω,
        sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈
          proxCore S.X S.proxPotential)
    (hvar :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (κ : PositiveTime) (j : ℕ)
    (houter_xbar_sq :
      Integrable
        (fun ω =>
          let outerPrev :=
            sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
              (κ.1 - 1) ω
          S.primalNorm (x.1 - outerPrev.xbar.1) ^ 2)
        law.P)
    (hprev_window :
      ∀ i, i < j + 1 →
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              x)
          law.P) :
    Integrable
      (fun ω =>
        bregmanFormulaOnX S
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
            hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
          x)
      law.P := by
  classical
  have hprev_breg :
      Integrable
        (fun ω =>
          bregmanFormulaOnX S
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω,
              hquery_mem κ j ω⟩ : FeasiblePoint S)
            x)
        law.P :=
    hprev_window j (Nat.lt_succ_self j)
  have hprev_l2_query :
      Integrable
        (fun ω =>
          S.primalNorm
            (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω) ^ 2)
        law.P :=
    query_sq_integrable_of_bregman_integrable
      (S := S) law.P x
      (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω,
          hquery_mem κ j ω⟩ : FeasiblePoint S))
      (hquery_meas κ j) hprev_breg
  have hdual_sq_prev :
      Integrable
        (fun ω =>
          dualNorm S
              (oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                (law.sample κ j ω)) ^ 2)
        law.P := by
    simpa using
      generatedSFOVariance_integrable_obligation
        (S := S) law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hvar κ j
  have hinner_aemeas_prev :
      AEStronglyMeasurable
        (fun ω =>
          ⟪oracleNoiseAt S
              (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
              (law.sample κ j ω),
            x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω⟫_ℝ)
        law.P := by
    have hkernel :
        Measurable (fun p : FeasiblePoint S × Sample =>
          ⟪x.1 - p.1.1, oracleNoiseAt S p.1.1 p.2⟫_ℝ) :=
      oracle_residual_target_inner_measurable_of_residual_measurable
        (S := S) x law.oracle_residual_measurable
    have hpair :
        Measurable (fun ω =>
          ((⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω,
              hquery_mem κ j ω⟩ : FeasiblePoint S),
            law.sample κ j ω)) :=
      (hquery_meas κ j).prod (law.sample_measurable κ j)
    have hscalar :
        Measurable
          (fun ω =>
            ⟪x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω,
              oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                (law.sample κ j ω)⟫_ℝ) := by
      simpa using hkernel.comp hpair
    simpa [real_inner_comm] using hscalar.aestronglyMeasurable
  have hinner_int_prev :
      Integrable
        (fun ω =>
          ⟪oracleNoiseAt S
              (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
              (law.sample κ j ω),
            x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω⟫_ℝ)
        law.P :=
    generated_target_inner_integrable_of_primal_displacement_l2
      (S := S) law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)
      x κ j hdual_sq_prev hprev_l2_query hinner_aemeas_prev
  have hdual_l1_prev :
      Integrable
        (fun ω =>
          dualNorm S
            (oracleNoiseAt S
              (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
              (law.sample κ j ω)))
        law.P := by
    have hnonneg :
        ∀ᵐ ω ∂law.P,
          0 ≤
            dualNorm S
              (oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                (law.sample κ j ω)) := by
      exact Filter.Eventually.of_forall (fun ω => by
        simpa [dualNorm] using
          SOptLib.canonicalDualNorm_nonneg S.primalNorm
            (oracleNoiseAt S
              (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
              (law.sample κ j ω)))
    exact
      (integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
        (μ := law.P) hdual_sq_prev hnonneg (C :=
          ∫ ω,
            dualNorm S
              (oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                (law.sample κ j ω)) ^ 2 ∂law.P)
        le_rfl).1
  have hshifted_dual_sq_prev :
      Integrable
        (fun ω =>
          (S.mGrowth +
              dualNorm S
                (oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                  (law.sample κ j ω))) ^ 2)
        law.P := by
    have hpoly :
        Integrable
          (fun ω =>
            S.mGrowth ^ 2 +
              (2 * S.mGrowth) *
                dualNorm S
                  (oracleNoiseAt S
                    (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                    (law.sample κ j ω)) +
              dualNorm S
                (oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                  (law.sample κ j ω)) ^ 2)
          law.P :=
      ((integrable_const (c := S.mGrowth ^ 2)).add
        (hdual_l1_prev.const_mul (2 * S.mGrowth))).add hdual_sq_prev
    refine hpoly.congr ?_
    filter_upwards with ω
    ring
  have hstoch_rhs_int :
      Integrable
        (fun ω =>
          ((S.mGrowth +
              dualNorm S
                (oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                  (law.sample κ j ω))) ^ 2) /
              (2 * beta κ * spsP (⟨j + 1, Nat.succ_pos j⟩ : PositiveTime)) +
            ⟪oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                (law.sample κ j ω),
              x.1 -
                sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω⟫_ℝ)
        law.P := by
    have hscaled :
        Integrable
          (fun ω =>
            ((S.mGrowth +
                dualNorm S
                  (oracleNoiseAt S
                    (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                    (law.sample κ j ω))) ^ 2) /
                (2 * beta κ * spsP (⟨j + 1, Nat.succ_pos j⟩ : PositiveTime)))
          law.P := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hshifted_dual_sq_prev.const_mul
          ((2 * beta κ * spsP (⟨j + 1, Nat.succ_pos j⟩ : PositiveTime))⁻¹)
    exact hscaled.add hinner_int_prev
  have hstep :
      ∀ ω,
        let outerPrev :=
          sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
            (κ.1 - 1) ω;
        let xUnder := outerExtrapolation S gamma κ outerPrev;
        let prev :=
          (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
            law.sample κ j ω).u;
        let βκ : {β : ℝ // 0 < β} := ⟨beta κ, hbeta κ⟩;
        let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩;
        let next : FeasiblePoint S :=
          (spsStep_formulaExtensionSelector S (smoothLinearization S xUnder)
            (smoothLinearization_isAffineModel S xUnder) outerPrev.x βκ t prev
            (law.sample κ j ω)).1;
        sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω =
            next.1 ∧
          (let δ := oracleNoiseAt S prev.1 (law.sample κ j ω);
            spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x
                (beta κ) next -
              spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x
                (beta κ) x ≤
              beta κ * spsP t * bregmanFormulaOnX S prev x -
                beta κ * (1 + spsP t) * bregmanFormulaOnX S next x +
                ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP t) +
                ⟪δ, x.1 - prev.1⟫_ℝ) := by
    intro ω
    exact
      _voucher_step_sgsOracleQuery_successor_exposes_selected_phi_bregman_18
        (S := S) x0 x beta gamma T law.sample hbeta hgamma κ j ω
  -- The remaining leaf is the nontrivial source recurrence integration step:
  -- combine `hstep` with `hprev_breg` and the proved stochastic-error
  -- integrability `hstoch_rhs_int`, then absorb the Phi difference using the
  -- feasible affine-minorant infrastructure.
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let coeff : ℝ := beta κ * (1 + spsP t)
  let Vprev : Ω → ℝ := fun ω =>
    bregmanFormulaOnX S
      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω,
        hquery_mem κ j ω⟩ : FeasiblePoint S)
      x
  let Vnext : Ω → ℝ := fun ω =>
    bregmanFormulaOnX S
      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
        hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
      x
  let R : Ω → ℝ := fun ω =>
    ((S.mGrowth +
        dualNorm S
          (oracleNoiseAt S
            (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
            (law.sample κ j ω))) ^ 2) /
        (2 * beta κ * spsP t) +
      ⟪oracleNoiseAt S
          (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
          (law.sample κ j ω),
        x.1 -
          sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω⟫_ℝ
  let Φnext : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
        hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
  let Φu : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ) x
  have hcoeff : 0 < coeff := by
    have hp_nonneg : 0 ≤ spsP t := by
      have ht : 0 < (t.1 : ℝ) := by exact_mod_cast t.2
      unfold spsP
      positivity
    dsimp [coeff]
    nlinarith [hbeta κ, hp_nonneg]
  have hrec_scalar :
      ∀ ω, Φnext ω - Φu ω ≤
        beta κ * spsP t * Vprev ω - coeff * Vnext ω + R ω := by
    intro ω
    rcases hstep ω with ⟨hnext_eq, hineq⟩
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    let prev :=
      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
        law.sample κ j ω).u
    let βκ : {β : ℝ // 0 < β} := ⟨beta κ, hbeta κ⟩
    let next : FeasiblePoint S :=
      (spsStep_formulaExtensionSelector S (smoothLinearization S xUnder)
        (smoothLinearization_isAffineModel S xUnder) outerPrev.x βκ t prev
        (law.sample κ j ω)).1
    have hnext_fp :
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
          hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) = next := by
      apply Subtype.ext
      simpa [outerPrev, xUnder, prev, βκ, next, t] using hnext_eq
    have hinner_next_fp :
        (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
          law.sample κ (j + 1) ω).u = next := by
      simpa [sgsOracleQuery] using hnext_fp
    have hinner_next_expr :
        (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
          law.sample κ (j + 1) ω).u =
          (spsStep_formulaExtensionSelector S (smoothLinearization S xUnder)
            (smoothLinearization_isAffineModel S xUnder) outerPrev.x βκ t prev
            (law.sample κ j ω)).1 := by
      simpa [next] using hinner_next_fp
    rw [← hinner_next_expr] at hineq
    dsimp [Φnext, Φu, Vprev, Vnext, R, coeff, t, sgsOracleQuery,
      outerPrev, xUnder, prev, βκ, next] at hineq ⊢
    nlinarith [hineq]
  have hVnext_nonneg : ∀ᵐ ω ∂law.P, 0 ≤ Vnext ω := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hlower :=
      bregmanFormulaOnX_lower_bound_from_prox_geometry S
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
          hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) x
    nlinarith [hlower,
      sq_nonneg
        (S.primalNorm
          (x.1 -
            sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω))]
  have hVnext_aestrong : AEStronglyMeasurable Vnext law.P := by
    exact
      selected_query_bregmanFormulaOnX_aestronglyMeasurable_of_proxCore
        (S := S)
        (query := fun ω =>
          sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω)
        (hmem := fun ω => hquery_mem κ (j + 1) ω)
        (hcore := fun ω => hquery_core κ (j + 1) ω)
        (hmeas := hquery_meas κ (j + 1)) x
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let Φavg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    let inner :=
      sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
    spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x (beta κ)
      (inner t.1 ω).avg
  let RHSavg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let inner :=
      sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
    beta κ * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
        bregmanFormulaOnX S outerPrev.x x +
      psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
        (Finset.range t.1).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((inner i ω).u.1) (law.sample κ i ω)
          (spsP ι * psWeightProduct spsP i)⁻¹ *
            (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
              ⟪δ, x.1 - (inner i ω).u.1⟫_ℝ))
  have hpropCoeff : 0 < propCoeff := by
    have hOneSub : 0 < 1 - psWeightProduct spsP t.1 := by
      rw [psWeightProduct_spsP_eq t.1]
      have htpos : 0 < (t.1 : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one t.2)
      have hDpos : 0 < (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) := by
        positivity
      have hrewrite :
          1 - 2 / (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) =
            ((t.1 : ℝ) * ((t.1 : ℝ) + 3)) /
              (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) := by
        field_simp [ne_of_gt hDpos]
        ring
      rw [hrewrite]
      exact div_pos (mul_pos htpos (by positivity)) hDpos
    dsimp [propCoeff]
    exact mul_pos (hbeta κ) (inv_pos.mpr hOneSub)
  have hRHSavg_int : Integrable RHSavg law.P := by
    simpa [RHSavg, t] using
      selected_sgs_inner_average_rhs_integrable
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas hvar κ j hprev_window
  have hpropAvg :
      ∀ ω, propCoeff * Vnext ω + (Φavg ω - Φu ω) ≤ RHSavg ω := by
    intro ω
    simpa [propCoeff, Vnext, Φavg, Φu, RHSavg, t] using
      selected_sgs_inner_Proposition8_3_successor_query_formulaOnXProcess
        (S := S) x0 beta gamma T law.sample hbeta hgamma hquery_mem κ j ω x
  have havgEnvelope :
      ∃ Cgap : Ω → ℝ,
        Integrable Cgap law.P ∧
          (∀ᵐ ω ∂law.P,
            Φu ω - Φavg ω ≤ (propCoeff / 2) * Vnext ω + Cgap ω) := by
    simpa [propCoeff, Vnext, Φavg, Φu, t] using
      selected_sgs_inner_average_phi_reverse_gap_integrable_envelope
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas hquery_core hvar κ j houter_xbar_sq hprev_window
  rcases havgEnvelope with ⟨Cgap, hCgap_int, havg_gap_ae⟩
  have hVnext_int : Integrable Vnext law.P :=
    terminal_bregman_integrable_of_average_phi_envelope
      (P := law.P) (coeff := propCoeff)
      (Vnext := Vnext) (RHS := RHSavg) (C := Cgap)
      (Φavg := Φavg) (Φu := Φu)
      hpropCoeff hRHSavg_int hCgap_int hVnext_aestrong
      hVnext_nonneg hpropAvg havg_gap_ae
  simpa [Vnext] using hVnext_int

/-- Canonical selected SGS query Bregman integrability induction.

Aligns with Lan Proposition 8.3 as used in Eq. (8.1.61)-(8.1.63): the inner
base case uses the previous outer call's terminal query, and successor queries
use the one-step Phi/Bregman transfer above. Candidate audit: considered the
pre-searched independence/filtration candidates and SOptLib finite-window
state-square induction; those do not state the selected query Bregman observable
needed here, so this helper packages the paper-local lexicographic induction. -/
theorem sgsOracleQuery_target_bregman_integrable_from_phi_bregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hquery_core :
      ∀ k i ω,
        sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈
          proxCore S.X S.proxPotential) :
    ∀ κ i,
      Integrable
        (fun ω =>
          bregmanFormulaOnX S
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
              (by
                rcases hindep with ⟨hquery_mem, _hquery_meas, _hindep_qs⟩
                exact hquery_mem κ i ω)⟩ : FeasiblePoint S)
            x)
        law.P := by
  classical
  rcases hindep with ⟨hquery_mem, hquery_meas, hindep_qs⟩
  have hvar :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)
      ⟨hquery_mem, hquery_meas, hindep_qs⟩
  let B : PositiveTime → ℕ → Prop := fun κ i =>
    Integrable
      (fun ω =>
        bregmanFormulaOnX S
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
            hquery_mem κ i ω⟩ : FeasiblePoint S)
          x)
      law.P
  let Xbar : ℕ → Prop := fun n =>
    Integrable
      (fun ω =>
        S.primalNorm
          (x.1 -
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
              n ω).xbar.1) ^ 2)
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
                        (fun _ : Ω => bregmanFormulaOnX S x0 x) law.P :=
                    integrable_const _
                  simpa [B, sgsOracleQuery, sgsInnerProcess_formulaExtensionSelector,
                    spsProcess, SOptLib.recursiveIterateProcess, spsInitial,
                    sgsProcess_formulaExtensionSelector, sgsInitial] using hconst
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
                        sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κcur 0 ω =
                          sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
                            (predTime κcur hκcur_two)
                            (T (predTime κcur hκcur_two)) ω := by
                    intro ω
                    rw [sgsOracleQuery_zero_eq_outer_center
                      (S := S) x0 beta gamma T law.sample hbeta hgamma κcur ω]
                    exact
                      selected_outer_center_eq_previous_terminal_query
                        (S := S) x0 beta gamma T law.sample hbeta hgamma
                        κcur hκcur_two ω
                  have hcongr :
                      (fun ω =>
                        bregmanFormulaOnX S
                          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
                              κcur 0 ω,
                            hquery_mem κcur 0 ω⟩ : FeasiblePoint S)
                          x) =
                      (fun ω =>
                        bregmanFormulaOnX S
                          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
                              (predTime κcur hκcur_two)
                              (T (predTime κcur hκcur_two)) ω,
                            hquery_mem (predTime κcur hκcur_two)
                              (T (predTime κcur hκcur_two)) ω⟩ : FeasiblePoint S)
                          x) := by
                    funext ω
                    simp [hterminal ω]
                  change B κcur 0
                  simpa [B, hcongr] using hprev_terminal
      | succ j =>
          have hprev_window : ∀ i, i < j + 1 → B κ i := by
            intro i hi
            exact ihInner i hi
          have houter_xbar_sq :
              Integrable
                (fun ω =>
                  let outerPrev :=
                    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                      law.sample (κ.1 - 1) ω
                  S.primalNorm (x.1 - outerPrev.xbar.1) ^ 2)
                law.P := by
            have hprev_lt : κ.1 - 1 < n := by
              have hkpos : 0 < κ.1 := κ.2
              omega
            have hxbar_prev := (ih (κ.1 - 1) hprev_lt).2
            simpa [Xbar] using hxbar_prev
          exact
            sgsOracleQuery_successor_bregman_integrable_of_prev_bregman
              (S := S) law x0 x beta gamma T hbeta hgamma
              hquery_mem hquery_meas hquery_core hvar κ j
              houter_xbar_sq hprev_window
    have hXbar_current : Xbar n := by
      cases n with
      | zero =>
          refine (integrable_const (c := S.primalNorm (x.1 - x0.1) ^ 2)).congr ?_
          filter_upwards with ω
          simp [Xbar, sgsProcess_formulaExtensionSelector, sgsInitial,
            SOptLib.recursiveIterateProcess]
      | succ m =>
          let κcur : PositiveTime := ⟨m + 1, Nat.succ_pos m⟩
          let states : ℕ → Ω → SGSState S :=
            sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
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
                    (x.1 -
                      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                        law.sample κcur (T κcur) ω).avg.1) ^ 2)
                  law.P :=
            selected_sgs_inner_avg_sq_integrable_from_bregman_window
              (S := S) law x0 x beta gamma T hbeta hgamma
              hquery_mem hquery_meas κcur (T κcur) hwindow
          have hprev_meas :
              AEStronglyMeasurable (fun ω => (states m ω).xbar.1) law.P := by
            simpa [states, κcur] using
              selected_sgs_outer_prev_xbar_aestronglyMeasurable
                (S := S) law x0 beta gamma T hbeta hgamma
                hquery_mem hquery_meas κcur
          have havg_meas :
              AEStronglyMeasurable
                (fun ω =>
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample κcur (T κcur) ω).avg.1) law.P :=
            selected_sgs_inner_avg_aestronglyMeasurable_of_query_meas
              (S := S) law x0 beta gamma T hbeta hgamma
              hquery_mem hquery_meas κcur (T κcur)
          have hcombo :
              Integrable
                (fun ω =>
                  S.primalNorm
                    (x.1 -
                      ((1 - gamma κcur) • (states m ω).xbar.1 +
                        gamma κcur •
                          (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma
                            hgamma T law.sample κcur (T κcur) ω).avg.1)) ^ 2)
                law.P :=
            primalNorm_sq_integrable_affine_update
              (S := S) law.P x
              (fun ω => (states m ω).xbar.1)
              (fun ω =>
                (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                  law.sample κcur (T κcur) ω).avg.1)
              (gamma κcur)
              hprev_meas havg_meas
              (by simpa [Xbar, states] using hprev_xbar_sq)
              havg_sq
          refine hcombo.congr (Filter.Eventually.of_forall ?_)
          intro ω
          have hsucc :
              states (m + 1) ω =
                sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta)
                  gamma T law.sample hgamma m (states m ω) ω := by
            simpa [states, sgsProcess_formulaExtensionSelector] using
              SOptLib.recursiveIterateProcess_succ
                (SOptLib.recursiveIterateProcess (sgsInitial S x0)
                  (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta)
                    gamma T law.sample hgamma))
                (sgsInitial S x0)
                (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta)
                  gamma T law.sample hgamma)
                rfl m ω
          have hxbar_eq :
              (states (m + 1) ω).xbar.1 =
                (1 - gamma κcur) • (states m ω).xbar.1 +
                  gamma κcur •
                    (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma
                      hgamma T law.sample κcur (T κcur) ω).avg.1 := by
            rw [hsucc]
            simp [sgsTransition_formulaExtensionSelector, spsOutput, states,
              sgsInnerProcess_formulaExtensionSelector, positiveBetaSchedule, κcur]
          simp [Xbar, states, hxbar_eq]
    exact ⟨hB_current, hXbar_current⟩
  intro κ i
  change B κ i
  exact (hPair κ.1).1 κ rfl i

/-- Exact-head voucher attempt for the selected-query displacement L2 leaf.

The attempt opens the target theorem itself, splits the inner index, exposes the
base-query recursion, and in the successor case consumes the compiled
source-faithful displacement-control voucher above.  The remaining `sorry` is
the finite Phi/Bregman telescope plus integrability algebra, not a missing
noncompact selected-minimizer square bound. -/
theorem _voucher_attempt_sgsOracleQuery_target_primal_displacement_sq_integrable_from_phi_bregman_5
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)) :
    ∀ κ i,
      Integrable
        (fun ω =>
          S.primalNorm
            (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω) ^ 2)
        law.P := by
  classical
  rcases hindep with ⟨hquery_mem, hquery_meas, hindep_qs⟩
  have hvar :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)
      ⟨hquery_mem, hquery_meas, hindep_qs⟩
  have hquery_core :
      ∀ k i ω,
        sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈
          proxCore S.X S.proxPotential := by
    intro k i ω
    exact feasible_mem_proxCore_before_stability
      (S := S)
      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω,
        hquery_mem k i ω⟩ : FeasiblePoint S)
  have hbreg_all :
      ∀ κ i,
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              x)
          law.P := by
    have hcanon :=
      sgsOracleQuery_target_bregman_integrable_from_phi_bregman
        (S := S) law x0 x beta gamma T hbeta hgamma
        ⟨hquery_mem, hquery_meas, hindep_qs⟩ hquery_core
    intro κ i
    simpa using hcanon κ i
  intro κ i
  cases i with
  | zero =>
      have hbase :
          ∀ ω,
            sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω =
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
                (κ.1 - 1) ω).x.1 := by
        intro ω
        exact
          sgsOracleQuery_zero_eq_outer_center
            (S := S) x0 beta gamma T law.sample hbeta hgamma κ ω
      have hbase_meas :
          Measurable (fun ω =>
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω,
              hquery_mem κ 0 ω⟩ : FeasiblePoint S)) :=
        hquery_meas κ 0
      rcases κ with ⟨k, hk⟩
      cases k with
      | zero =>
          omega
      | succ k =>
          cases k with
          | zero =>
              have hconst :
                  Integrable
                    (fun _ : Ω => S.primalNorm (x.1 - x0.1) ^ 2) law.P :=
                integrable_const _
              simpa [sgsOracleQuery, sgsInnerProcess_formulaExtensionSelector,
                spsProcess, SOptLib.recursiveIterateProcess, spsInitial,
                sgsProcess_formulaExtensionSelector, sgsInitial] using hconst
          | succ k =>
              let κcur : PositiveTime := ⟨k + 1 + 1, hk⟩
              have hκcur_two : 2 ≤ κcur.1 := by
                dsimp [κcur]
                omega
              have hterminal :
                  ∀ ω,
                    sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κcur 0 ω =
                      sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
                        (predTime κcur hκcur_two) (T (predTime κcur hκcur_two)) ω := by
                intro ω
                rw [hbase ω]
                exact
                  selected_outer_center_eq_previous_terminal_query
                    (S := S) x0 beta gamma T law.sample hbeta hgamma
                    κcur hκcur_two ω
              have hprev_terminal_l2 :
                  Integrable
                    (fun ω =>
                      S.primalNorm
                        (x.1 -
                          sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
                            (predTime κcur hκcur_two)
                            (T (predTime κcur hκcur_two)) ω) ^ 2)
                    law.P := by
                have hprev_terminal_breg :
                    Integrable
                      (fun ω =>
                        bregmanFormulaOnX S
                          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
                              (predTime κcur hκcur_two)
                              (T (predTime κcur hκcur_two)) ω,
                            hquery_mem (predTime κcur hκcur_two)
                              (T (predTime κcur hκcur_two)) ω⟩ : FeasiblePoint S)
                          x)
                      law.P := by
                  exact hbreg_all (predTime κcur hκcur_two)
                    (T (predTime κcur hκcur_two))
                exact
                  query_sq_integrable_of_bregman_integrable
                    (S := S) law.P x
                    (fun ω =>
                      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
                          (predTime κcur hκcur_two)
                          (T (predTime κcur hκcur_two)) ω,
                        hquery_mem (predTime κcur hκcur_two)
                          (T (predTime κcur hκcur_two)) ω⟩ : FeasiblePoint S))
                    (hquery_meas (predTime κcur hκcur_two)
                      (T (predTime κcur hκcur_two)))
                    hprev_terminal_breg
              convert hprev_terminal_l2 using 1
  | succ j =>
      have hsucc :
          ∀ ω,
            let outerPrev :=
              sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
                (κ.1 - 1) ω;
            let xUnder := outerExtrapolation S gamma κ outerPrev;
            let prev :=
              (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                law.sample κ j ω).u;
            let βκ : {β : ℝ // 0 < β} := ⟨beta κ, hbeta κ⟩;
            let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩;
            let next : FeasiblePoint S :=
              (spsStep_formulaExtensionSelector S (smoothLinearization S xUnder)
                (smoothLinearization_isAffineModel S xUnder) outerPrev.x βκ t prev
                (law.sample κ j ω)).1;
            sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω =
                next.1 ∧
              (let δ := oracleNoiseAt S prev.1 (law.sample κ j ω);
                beta κ * (1 + spsP t) *
                    ((1 / 2 : ℝ) * S.primalNorm (x.1 - next.1) ^ 2) ≤
                  beta κ * spsP t * bregmanFormulaOnX S prev x +
                    ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP t) +
                    ⟪δ, x.1 - prev.1⟫_ℝ +
                    (spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x
                        (beta κ) x -
                      spsPhiFormulaOnX S (smoothLinearization S xUnder) outerPrev.x
                        (beta κ) next)) := by
        intro ω
        exact
          _voucher_step_sgsOracleQuery_successor_phi_controls_target_displacement_19
            (S := S) x0 x beta gamma T law.sample hbeta hgamma κ j ω
      have hsucc_meas :
          Measurable (fun ω =>
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
              hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)) :=
        hquery_meas κ (j + 1)
      have hdual_sq_prev :
          Integrable
            (fun ω =>
              dualNorm S
                  (oracleNoiseAt S
                    ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                      law.sample κ j ω).u.1)
                    (law.sample κ j ω)) ^ 2)
            law.P := by
        simpa [sgsOracleQuery] using
          generatedSFOVariance_integrable_obligation
            (S := S) law.P law.sample
            (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hvar κ j
      have hinner_aemeas_prev :
          AEStronglyMeasurable
            (fun ω =>
              ⟪oracleNoiseAt S
                  ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample κ j ω).u.1)
                  (law.sample κ j ω),
                x.1 -
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample κ j ω).u.1⟫_ℝ)
            law.P := by
        have hkernel :
            Measurable (fun p : FeasiblePoint S × Sample =>
              ⟪x.1 - p.1.1, oracleNoiseAt S p.1.1 p.2⟫_ℝ) :=
          oracle_residual_target_inner_measurable_of_residual_measurable
            (S := S) x law.oracle_residual_measurable
        have hpair :
            Measurable (fun ω =>
              ((⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω,
                  hquery_mem κ j ω⟩ : FeasiblePoint S),
                law.sample κ j ω)) :=
          (hquery_meas κ j).prod (law.sample_measurable κ j)
        have hscalar :
            Measurable
              (fun ω =>
                ⟪x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω,
                  oracleNoiseAt S
                    (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                    (law.sample κ j ω)⟫_ℝ) := by
          simpa using hkernel.comp hpair
        simpa [sgsOracleQuery, real_inner_comm] using hscalar.aestronglyMeasurable
      have hinner_int_from_prev_l2 :
          Integrable
            (fun ω =>
              S.primalNorm
                (x.1 -
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample κ j ω).u.1) ^ 2)
            law.P →
          Integrable
            (fun ω =>
              ⟪oracleNoiseAt S
                  ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample κ j ω).u.1)
                  (law.sample κ j ω),
                x.1 -
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample κ j ω).u.1⟫_ℝ)
            law.P := by
        intro hprev_l2
        have hprev_l2_query :
            Integrable
              (fun ω =>
                S.primalNorm
                  (x.1 -
                    sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω) ^ 2)
              law.P := by
          simpa [sgsOracleQuery] using hprev_l2
        have hinner_query :
            Integrable
              (fun ω =>
                ⟪oracleNoiseAt S
                    (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω)
                    (law.sample κ j ω),
                  x.1 -
                    sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ j ω⟫_ℝ)
              law.P :=
          generated_target_inner_integrable_of_primal_displacement_l2
            (S := S) law.P law.sample
            (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)
            x κ j
            (generatedSFOVariance_integrable_obligation
              (S := S) law.P law.sample
              (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hvar κ j)
            hprev_l2_query
            (by simpa [sgsOracleQuery] using hinner_aemeas_prev)
        simpa [sgsOracleQuery] using hinner_query
      -- Remaining successor subgoal: integrate `hsucc`, divide by the positive
      -- coefficient, telescope the Phi/Bregman terms over the finite SPS
      -- window, and use generated variance for the dual-noise-square summands.
      have hnext_breg :
          Integrable
            (fun ω =>
              bregmanFormulaOnX S
                (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
                  hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S)
                x)
            law.P := by
        exact hbreg_all κ (j + 1)
      exact
        query_sq_integrable_of_bregman_integrable
          (S := S) law.P x
          (fun ω =>
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (j + 1) ω,
              hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S))
          hsucc_meas hnext_breg

/-- Source-recurrence displacement integrability for the selected SGS oracle query.

This is the exact remaining well-definedness obligation behind the martingale
term in Eq. (8.1.69): it asks only for the L2 size of the already selected
query `u_{k,i}` relative to the fixed comparator.  It must be proved from the
finite Proposition 8.3 Phi/Bregman telescope and the generated variance law; it
is not a pointwise square domination theorem for the SPS minimizer and it does
not introduce compact/envelope control in the noncompact Theorem 8.2(a) branch. -/
theorem sgsOracleQuery_target_primal_displacement_sq_integrable_from_phi_bregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)) :
    ∀ κ i,
      Integrable
        (fun ω =>
          S.primalNorm
            (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω) ^ 2)
        law.P := by
  classical
  -- FILL route: use `sgsOracleQuery_zero_eq_outer_center` for the inner base
  -- case and
  -- `_voucher_step_sgsOracleQuery_successor_exposes_selected_phi_bregman_18`
  -- for successor queries.  Integrate the displayed one-step recurrence,
  -- telescope the retained Phi/Bregman terms over the finite SPS window, and
  -- use `generatedSFOVariance_integrable_obligation` for the finite dual-norm
  -- square summands.  Do not reintroduce a noncompact pointwise square budget
  -- for the selected minimizer.
  exact
    _voucher_attempt_sgsOracleQuery_target_primal_displacement_sq_integrable_from_phi_bregman_5
      (S := S) law x0 x beta gamma T hbeta hgamma hindep

/-- Compiled Cauchy-Schwarz bridge for the selected martingale scalar.

Generated variance supplies the L2 bound for the oracle noise.  Once the
source-recurrence leaf above supplies the L2 displacement of the selected query,
the scalar product in Eq. (8.1.69) is integrable by the paper primal/dual norm
Cauchy-Schwarz bound. -/
theorem sgsOracleQuery_target_noise_inner_integrable_of_displacement_l2
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hdisp_sq :
      ∀ κ i,
        Integrable
          (fun ω =>
            S.primalNorm
              (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω) ^ 2)
          law.P) :
    ∀ κ i,
      Integrable
        (fun ω =>
          ⟪oracleNoiseAt S
              (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
              (law.sample κ i ω),
            x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ)
        law.P := by
  classical
  let query := sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample query :=
    law.generated_variance query hindep
  rcases hindep with ⟨hquery, hquery_meas, _hindep_qs⟩
  intro κ i
  have hdual_sq :
      Integrable
        (fun ω =>
          dualNorm S (oracleNoiseAt S (query κ i ω) (law.sample κ i ω)) ^ 2)
        law.P := by
    simpa [query] using
      generatedSFOVariance_integrable_obligation
        S law.P law.sample query hgenerated_var κ i
  let queryFP : Ω → FeasiblePoint S :=
    fun ω => ⟨query κ i ω, hquery κ i ω⟩
  have hqueryFP_meas : Measurable queryFP := by
    simpa [queryFP] using hquery_meas κ i
  have hpair_meas : Measurable (fun ω => (queryFP ω, law.sample κ i ω)) :=
    hqueryFP_meas.prod (law.sample_measurable κ i)
  have hleft_inner_aemeas :
      AEStronglyMeasurable
        (fun ω =>
          ⟪x.1 - query κ i ω,
            oracleNoiseAt S (query κ i ω) (law.sample κ i ω)⟫_ℝ) law.P := by
    have hkernel :=
      oracle_residual_target_inner_measurable_of_residual_measurable
        (S := S) x law.oracle_residual_measurable
    simpa [queryFP] using (hkernel.comp hpair_meas).aestronglyMeasurable
  have hinner_aemeas :
      AEStronglyMeasurable
        (fun ω =>
          ⟪oracleNoiseAt S (query κ i ω) (law.sample κ i ω),
            x.1 - query κ i ω⟫_ℝ) law.P :=
    hleft_inner_aemeas.congr
      (Filter.Eventually.of_forall (fun ω => by
        simpa using
          (real_inner_comm
            (x.1 - query κ i ω)
            (oracleNoiseAt S (query κ i ω) (law.sample κ i ω))).symm))
  simpa [query] using
    generated_target_inner_integrable_of_primal_displacement_l2
      (S := S) law.P law.sample query x κ i hdual_sq
      (by simpa [query] using hdisp_sq κ i) hinner_aemeas

/-- Scalar integrability of the selected SGS martingale product.

This replaces the rejected noncompact route through a global L2 bound for the
selected Eq. (8.1.58) minimizer.  Proposition 8.3 only needs the scalar term
`⟪δ_{k,i}, x-u_{k,i}⟫`; proving this leaf should integrate the
Phi/Bregman recurrence and use the generated variance bound, without asserting a
standalone square envelope for the selected minimizer. -/
theorem sgsOracleQuery_target_noise_inner_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)) :
    ∀ κ i,
      Integrable
        (fun ω =>
          ⟪oracleNoiseAt S
              (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
              (law.sample κ i ω),
            x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ)
        law.P := by
  classical
  have hdisp_sq :=
    sgsOracleQuery_target_primal_displacement_sq_integrable_from_phi_bregman
      (S := S) law x0 x beta gamma T hbeta hgamma hindep
  exact
    sgsOracleQuery_target_noise_inner_integrable_of_displacement_l2
      (S := S) law x0 x beta gamma T hbeta hgamma hindep hdisp_sq

/-- Martingale cancellation for the selected Algorithm 8.2 query direction.

The proof is now compiled against the scalar integrability leaf above, so the
expected Theorem 8.2 route no longer depends on a selected-minimizer L2
regularity theorem. -/
theorem sgsOracleQuery_target_noise_inner_integral_zero
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)) :
    ∀ κ i,
      (∫ ω,
        ⟪oracleNoiseAt S
            (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
            (law.sample κ i ω),
          x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ
        ∂law.P) = 0 := by
  classical
  let query := sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
  have hinner_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        ⟪(fun q : FeasiblePoint S => x.1 - q.1) p.1,
          oracleNoiseAt S p.1.1 p.2⟫_ℝ) := by
    simpa using
      oracle_residual_target_inner_measurable_of_residual_measurable
        (S := S) (x := x) law.oracle_residual_measurable
  have hinner_int :
      ∀ κ i (hquery : ∀ ω, query κ i ω ∈ S.X),
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (query κ i ω) (law.sample κ i ω),
              (fun q : FeasiblePoint S => x.1 - q.1)
                ⟨query κ i ω, hquery ω⟩⟫_ℝ) law.P := by
    intro κ i hquery
    simpa [query] using
      sgsOracleQuery_target_noise_inner_integrable
        (S := S) (law := law) x0 x beta gamma T hbeta hgamma hindep κ i
  intro κ i
  rcases generated_oracle_noise_inner_query_direction_zero
      (S := S) (law := law) (query := query) hindep
      (fun q : FeasiblePoint S => x.1 - q.1)
      hinner_meas hinner_int κ i with ⟨_hquery, hzero⟩
  simpa [query] using hzero

/-- Source-domain caller for selected-query Bregman integrability.

This is the executable boundary requested by the reconstruction audit: the
formula-extension selected run is consumed only after an explicit source-domain
inner invariant has supplied `u_{k,i} ∈ X^o`.  The invariant is the same one
used by `sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_sourceDomain_obligation`;
the proof projects it to the query-core hypothesis needed by the local
Bregman-integrability induction. -/
theorem sgsOracleQuery_target_bregman_integrable_from_sourceDomain_phi_bregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hinner :
      ∀ k i ω,
        ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          k i ω).u).1 ∈
            proxCore S.X S.proxPotential) :
    ∀ κ i,
      Integrable
        (fun ω =>
          bregmanFormulaOnX S
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
              (by
                rcases hindep with ⟨hquery_mem, _hquery_meas, _hindep_qs⟩
                exact hquery_mem κ i ω)⟩ : FeasiblePoint S)
            x)
        law.P := by
  classical
  have hquery_core :
      ∀ k i ω,
        sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈
          proxCore S.X S.proxPotential := by
    intro k i ω
    simpa [sgsOracleQuery] using hinner k i ω
  exact
    sgsOracleQuery_target_bregman_integrable_from_phi_bregman
      (S := S) law x0 x beta gamma T hbeta hgamma hindep hquery_core

/-- Public selected-realization source-domain entry point for query Bregman
integrability.

This is the run-level bridge requested by the reconstruction audit.  It keeps
Algorithm 8.1/8.2's selected feasible process at its displayed `X` boundary,
but exposes the extra source-domain witness needed to interpret each Bregman
first argument in `X^o`.  The theorem deliberately consumes explicit
`hx0`/`houter`/`hinner` invariants instead of strengthening the global SPS
solver to return prox-core minimizers. -/
theorem sgsOracleQuery_target_bregman_integrable_from_selectedSourceDomain_invariants
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hx0 : x0.1 ∈ proxCore S.X S.proxPotential)
    (houter :
      ∀ n ω,
        ((sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          n ω).x).1 ∈ proxCore S.X S.proxPotential)
    (hinner :
      ∀ k i ω,
        ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
          law.sample k i ω).u).1 ∈ proxCore S.X S.proxPotential) :
    ∀ κ i,
      Integrable
        (fun ω =>
          bregmanFormulaOnX S
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
              (by
                rcases hindep with ⟨hquery_mem, _hquery_meas, _hindep_qs⟩
                exact hquery_mem κ i ω)⟩ : FeasiblePoint S)
            x)
        law.P := by
  classical
  have _hrun :
      IsGeneratedSGSProcess_sourceDomain S ⟨x0.1, hx0⟩ beta gamma T law.sample
        (fun n ω =>
          sgsSourceStateOfFeasible S
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
              law.sample n ω)
            (houter n ω))
        (fun k i ω =>
          spsSourceStateOfFeasible S
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
              law.sample k i ω)
            (hinner k i ω)) :=
    sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_sourceDomain_obligation
      (S := S) x0 beta hbeta gamma hgamma T law.sample hx0 houter hinner
  exact
    sgsOracleQuery_target_bregman_integrable_from_sourceDomain_phi_bregman
      (S := S) law x0 x beta gamma T hbeta hgamma hindep hinner

/-- Source-domain selected-query displacement integrability.

Once the selected inner source-domain invariant supplies the `X^o` bases, the
paper Bregman route gives the L2 displacement by the prox-geometry lower bound.
This is intentionally separate from the formula-extension theorem below, whose
unqualified feasible interface still cannot manufacture prox-core membership
from feasibility alone. -/
theorem sgsOracleQuery_target_primal_displacement_sq_integrable_from_sourceDomain_phi_bregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hinner :
      ∀ k i ω,
        ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          k i ω).u).1 ∈
            proxCore S.X S.proxPotential) :
    ∀ κ i,
      Integrable
        (fun ω =>
          S.primalNorm
            (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω) ^ 2)
        law.P := by
  classical
  rcases hindep with ⟨hquery_mem, hquery_meas, hindep_qs⟩
  have hindep' :
      sfoIndependent S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    ⟨hquery_mem, hquery_meas, hindep_qs⟩
  have hbreg_all :=
    sgsOracleQuery_target_bregman_integrable_from_sourceDomain_phi_bregman
      (S := S) law x0 x beta gamma T hbeta hgamma hindep' hinner
  intro κ i
  exact
    query_sq_integrable_of_bregman_integrable
      (S := S) law.P x
      (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
          hquery_mem κ i ω⟩ : FeasiblePoint S))
      (hquery_meas κ i) (hbreg_all κ i)

/-- Public selected-realization source-domain entry point for query L2
displacement integrability.

This is the L2 counterpart of
`sgsOracleQuery_target_bregman_integrable_from_selectedSourceDomain_invariants`.
It gives source-facing convergence callers a compiled route from the selected
source-domain invariants to the martingale/displacement integrability leaf,
without invoking the arbitrary-boundary fallback of `bregmanFormulaOnX`. -/
theorem sgsOracleQuery_target_primal_displacement_sq_integrable_from_selectedSourceDomain_invariants
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hx0 : x0.1 ∈ proxCore S.X S.proxPotential)
    (houter :
      ∀ n ω,
        ((sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          n ω).x).1 ∈ proxCore S.X S.proxPotential)
    (hinner :
      ∀ k i ω,
        ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
          law.sample k i ω).u).1 ∈ proxCore S.X S.proxPotential) :
    ∀ κ i,
      Integrable
        (fun ω =>
          S.primalNorm
            (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω) ^ 2)
        law.P := by
  classical
  have _hrun :
      IsGeneratedSGSProcess_sourceDomain S ⟨x0.1, hx0⟩ beta gamma T law.sample
        (fun n ω =>
          sgsSourceStateOfFeasible S
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
              law.sample n ω)
            (houter n ω))
        (fun k i ω =>
          spsSourceStateOfFeasible S
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
              law.sample k i ω)
            (hinner k i ω)) :=
    sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_sourceDomain_obligation
      (S := S) x0 beta hbeta gamma hgamma T law.sample hx0 houter hinner
  exact
    sgsOracleQuery_target_primal_displacement_sq_integrable_from_sourceDomain_phi_bregman
      (S := S) law x0 x beta gamma T hbeta hgamma hindep hinner


/-- Forward-monotonicity denominator admissibility implies every displayed
inner budget is positive.

Aligns with the denominator side condition in Eq. (8.1.33) before applying
Proposition 8.3 at `t = T_k`. Candidate audit: checked
`one_sub_psWeightProduct_spsP_pos_of_pos`, `psWeightProduct_spsP_eq`, and
`forwardMonotonicityCondition_denominators`; none states this reverse
well-formedness bridge, so this helper extracts it from
`Γ_k(1-P_{T_k}) ≠ 0` and `P_0 = 1`. -/
theorem positive_inner_budget_of_forwardMonotonicity
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T)
    (k : PositiveTime) :
    0 < T k := by
  have hdenom := forwardMonotonicityCondition_denominators beta gamma Gamma T hmono
  by_contra hnot
  have hzero : T k = 0 := Nat.eq_zero_of_not_pos hnot
  have hfactor : 1 - psWeightProduct spsP (T k) = 0 := by
    simp [hzero, psWeightProduct]
  exact hdenom k (by simp [hfactor])

/-- Forward denominator admissibility and the Eq. (8.1.32) outer-weight
recurrence make every displayed `Γ_k` strictly positive.

Aligns with Lan Eq. (8.1.32) and the denominator side of Eq. (8.1.33).
Candidate audit: considered `gamma_ne_of_monotonicityQuotientDenominators`,
`forwardMonotonicityCondition_denominators`, `outerWeightCondition`, and
SOptLib telescope helpers; they provide nonzero denominators or consume
nonzero weights, but none combines the recurrence with `γ_k ∈ [0,1]` to prove
strict positivity for the SGS schedule. -/
theorem outer_gamma_positive_of_weight_condition_and_forward_denom
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hgamma : gammaRangeCondition gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T) :
    ∀ k : PositiveTime, 0 < Gamma k := by
  classical
  have hdenom :
      monotonicityQuotientDenominators Gamma T :=
    forwardMonotonicityCondition_denominators beta gamma Gamma T hmono
  have hGamma_ne : ∀ k : PositiveTime, Gamma k ≠ 0 :=
    gamma_ne_of_monotonicityQuotientDenominators Gamma T hdenom
  have hGamma_nonneg : ∀ k : PositiveTime, 0 ≤ Gamma k := by
    intro k
    have hk_pos : 1 ≤ k.1 := k.2
    have hnat :
        ∀ n : ℕ, 1 ≤ n → ∀ j : PositiveTime, j.1 = n → 0 ≤ Gamma j := by
      intro n
      exact Nat.strong_induction_on n (fun n ih => by
        intro hn j hj
        by_cases hn1 : n = 1
        · have hj_one : j = oneTime := by
            apply Subtype.ext
            simpa [oneTime, hj, hn1]
          rw [hj_one, hGamma.1]
          norm_num
        · have hj2 : 2 ≤ j.1 := by omega
          have hpred_lt : (predTime j hj2).1 < n := by
            simp [predTime, hj]
            omega
          have hpred_ge : 1 ≤ (predTime j hj2).1 := (predTime j hj2).2
          have hpred_nonneg : 0 ≤ Gamma (predTime j hj2) :=
            ih (predTime j hj2).1 hpred_lt hpred_ge (predTime j hj2) rfl
          have hcoeff_nonneg : 0 ≤ 1 - gamma j :=
            sub_nonneg.mpr (hgamma j).2
          rw [hGamma.2 j hj2]
          exact mul_nonneg hcoeff_nonneg hpred_nonneg)
    exact hnat k.1 hk_pos k rfl
  intro k
  exact lt_of_le_of_ne (hGamma_nonneg k) (Ne.symm (hGamma_ne k))

/-- Nested finite-sum version of the final Young-square relaxation in
Eq. (8.1.69).

Aligns with the last scalar relaxation in Lan Eq. (8.1.69). Candidate audit:
considered `sps_noise_square_relaxation`, `SOptLib.canonicalDualNorm_nonneg`,
and finite-sum monotonicity lemmas; the scalar helper is exactly the pointwise
ingredient, while no existing result packages this SGS-selected nested
outer/inner sum with the paper's `γ_k P_{T_k}/(Γ_k(1-P_{T_k}))` coefficient. -/
theorem outer_inner_noise_square_relaxation_sum
    (x0 : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (N : PositiveTime) (ω : Ω) (u : FeasiblePoint S)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T) :
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        let xUnder := outerExtrapolation S gamma κ
          (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω);
        let gk : E → ℝ := fun y => smoothLinearization S xUnder y;
        let inner := spsProcess_formulaExtensionSelector S gk (smoothLinearization_isAffineModel S xUnder)
          (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω).x
          ⟨beta κ, hbeta κ⟩ (sample κ);
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω);
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                  ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))) ≤
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        let xUnder := outerExtrapolation S gamma κ
          (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω);
        let gk : E → ℝ := fun y => smoothLinearization S xUnder y;
        let inner := spsProcess_formulaExtensionSelector S gk (smoothLinearization_isAffineModel S xUnder)
          (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω).x
          ⟨beta κ, hbeta κ⟩ (sample κ);
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω);
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                  ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))) := by
  classical
  have hTpos : ∀ k : PositiveTime, 0 < T k :=
    positive_inner_budget_of_forwardMonotonicity beta gamma Gamma T hmono
  have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
    outer_gamma_positive_of_weight_condition_and_forward_denom beta gamma Gamma T
      hgamma hGamma hmono
  refine Finset.sum_le_sum ?_
  intro k hk
  let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
  let xUnder := outerExtrapolation S gamma κ
    (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω)
  let gk : E → ℝ := fun y => smoothLinearization S xUnder y
  let inner := spsProcess_formulaExtensionSelector S gk (smoothLinearization_isAffineModel S xUnder)
    (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω).x
    ⟨beta κ, hbeta κ⟩ (sample κ)
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
  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
  let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω)
  have hspsP_pos : 0 < spsP ι := by
    unfold spsP
    positivity
  have hprod_pos : 0 < psWeightProduct spsP i := by
    rw [psWeightProduct_spsP_eq i]
    positivity
  have hinner_coeff_nonneg :
      0 ≤ (spsP ι * psWeightProduct spsP i)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (mul_pos hspsP_pos hprod_pos))
  have hpoint :
      ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
          ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ ≤
        (S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
          ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ := by
    have hsquare :=
      sps_noise_square_relaxation (β := beta κ) (p := spsP ι)
        (M := S.mGrowth) (d := dualNorm S δ) (hbeta κ) hspsP_pos
        S.M_pos.le (SOptLib.canonicalDualNorm_nonneg S.primalNorm δ)
    linarith
  exact mul_le_mul_of_nonneg_left hpoint hinner_coeff_nonneg

/-- Positive-time unfolding of the selected outer SGS recursion.

Aligns with Algorithm 8.1's transition from outer state `k-1` to `k`.
Candidate audit: considered `SOptLib.recursiveIterateProcess_succ` and
`sgsTransition_formulaExtensionSelector_positiveTime`; the SOptLib lemma is the
raw zero-based recursion equation and this helper specializes it to the
paper-positive index used by Eq. (8.1.31)/(8.1.69). -/
theorem sgsProcess_formulaExtensionSelector_positiveTime_eq_transition
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k) (gamma : PositiveTime → ℝ)
    (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) (ω : Ω) :
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k.1 ω =
      sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma
        (k.1 - 1)
        (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
          (k.1 - 1) ω) ω := by
  cases k with
  | mk m hm =>
      have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
      subst hn
      simp [sgsProcess_formulaExtensionSelector, Nat.succ_sub_one,
        SOptLib.recursiveIterateProcess]

/-- Reindex a one-based natural interval as the zero-based `range` used by the
formula-extension SGS output.

Candidate audit: considered SOptLib `sum_positiveTimeOutputWindowTimes_eq_Icc`
and `sum_times_eq_Icc`; those handle the library's output-window wrapper, while
Eq. (8.1.69) needs this direct `Finset.Icc 1 N` to `Finset.range N` successor
form after applying the scalar telescope. -/
theorem positiveTime_Icc_range_sum_reindex
    {α : Type*} [AddCommMonoid α] (N : ℕ) (hN : 1 ≤ N)
    (φ : PositiveTime → α) :
    (Finset.Icc 1 N).sum (fun t =>
        if ht : 1 ≤ t then φ ⟨t, ht⟩ else 0) =
      (Finset.range N).sum (fun k => φ ⟨k + 1, Nat.succ_pos k⟩) := by
  classical
  induction N, hN using Nat.le_induction with
  | base =>
      simp
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]
      rw [Finset.sum_range_succ]
      simp [ih]

/-- Zero-source specialization of the finite-window weighted recurrence
telescope used in the first line of Eq. (8.1.69).

Aligns with Lan Eq. (8.1.69) proof step 1 after setting the source terms
`L = B = 0`. Candidate audit: this is a direct specialization of SOptLib
`finite_window_weighted_recurrence_telescope_with_tail_sums`; no new primitive
is introduced, only the SGS-needed no-source corollary is packaged. -/
theorem finite_window_weighted_recurrence_telescope_no_source
    (alpha Gamma A D : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hGamma_ne : ∀ t, 1 ≤ t → Gamma t ≠ 0)
    (hGamma_one : Gamma 1 = 1)
    (halpha_one : alpha 1 = 1)
    (halpha_le_one : ∀ t, 1 ≤ t → alpha t ≤ 1)
    (hGamma_succ :
      ∀ t, 1 ≤ t → Gamma (t + 1) = (1 - alpha (t + 1)) * Gamma t)
    (hstep : ∀ t, 1 ≤ t →
      A t ≤ (1 - alpha t) * A (t - 1) + D t) :
    A k ≤ Gamma k * Finset.sum (Finset.Icc 1 k) (fun t => D t / Gamma t) := by
  classical
  let zero : ℕ → ℝ := fun _ => 0
  have htelescope :=
    finite_window_weighted_recurrence_telescope_with_tail_sums
      (R := ℝ) alpha (fun _ => (1 : ℝ)) Gamma A zero zero D k hk
      (by intro t ht; norm_num)
      hGamma_ne hGamma_one halpha_one halpha_le_one hGamma_succ ?_
  · have hleft :
        A k - Gamma k *
            Finset.sum (Finset.Icc 1 k) (fun t => alpha t / Gamma t * zero t) =
          A k := by simp [zero]
    have hright :
        Gamma k * (1 - alpha 1) * A 0 +
            Gamma k *
              Finset.sum (Finset.Icc 1 k)
                (fun t => alpha t / ((fun _ => (1 : ℝ)) t * Gamma t) * zero t) +
            Gamma k *
              Finset.sum (Finset.Icc 1 k) (fun t => D t / Gamma t) =
          Gamma k * Finset.sum (Finset.Icc 1 k) (fun t => D t / Gamma t) := by
        simp [zero, halpha_one]
    rwa [hleft, hright] at htelescope
  · intro t ht
    simpa [zero] using hstep t ht

/-- No-tail corollary of the weighted drop telescope used for the forward
Bregman window in Eq. (8.1.69).

Aligns with Lan Eq. (8.1.37) as invoked in Eq. (8.1.69). Candidate audit:
this directly specializes SOptLib `sum_weighted_sub_mul_le_first_sub_tail` with
the multiplier sequence constantly `1`; the only additional step is dropping
the nonnegative terminal Bregman tail. -/
theorem sum_weighted_sub_le_first_of_forward_mono
    (c V : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hV_nonneg : ∀ n, 1 ≤ n → n ≤ k → 0 ≤ V n)
    (hc_mono : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ c n)
    (hc_tail_nonneg : 0 ≤ c k * V k) :
    Finset.sum (Finset.Icc 1 k) (fun t => c t * (V (t - 1) - V t)) ≤
      c 1 * V 0 := by
  classical
  have htel :=
    sum_weighted_sub_mul_le_first_sub_tail c (fun _ => (1 : ℝ)) V k hk
      (by
        intro n hn hnk
        exact hV_nonneg n hn (le_of_lt hnk))
      (by
        intro n hn hnk
        simpa using hc_mono n hn hnk)
  have htel' :
      Finset.sum (Finset.Icc 1 k) (fun t => c t * (V (t - 1) - V t)) ≤
        c 1 * V 0 - c k * V k := by
    simpa using htel
  nlinarith

/-- Natural-index form of the forward monotonicity quotient used by the
Bregman-window telescope in Eq. (8.1.69).

Aligns with Lan Eq. (8.1.33). Candidate audit: considered
`forwardMonotonicityCondition_checked_spec`, which is the exact source
predicate over `PositiveTime`; this helper only rewrites its predecessor index
to the `n+1`/`n` natural form needed by SOptLib's scalar telescope. -/
theorem forwardMonotonicity_nat_coeff_mono
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T) :
    ∀ n, (hn : 1 ≤ n) →
      gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ *
          beta ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ /
            (Gamma ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩ *
              (1 - psWeightProduct spsP
                (T ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩))) ≤
        gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
            (Gamma ⟨n, hn⟩ *
              (1 - psWeightProduct spsP (T ⟨n, hn⟩))) := by
  intro n hn
  let κ : PositiveTime := ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩
  have hk2 : 2 ≤ κ.1 := by
    dsimp [κ]
    omega
  have hpred : predTime κ hk2 = (⟨n, hn⟩ : PositiveTime) := by
    apply Subtype.ext
    simp [κ, predTime]
  have h :=
    forwardMonotonicityCondition_checked_spec beta gamma Gamma T hmono κ hk2
  simpa [checkedQuotient_def, κ, hpred] using h

/-- One selected outer SGS step after inserting the feasible Proposition 8.3
inner bound.

Aligns with Lan Eq. (8.1.31) plus Eq. (8.1.65), the first proof step of
Eq. (8.1.69). Candidate audit: considered the pre-searched SOptLib algebra
lemmas `finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`weighted_sq_norm_sub_center_le`, and the scalar telescope
`finite_window_weighted_recurrence_telescope_with_tail_sums`; none combines
this file's selected SGS transition with Proposition 8.3, so this helper
specializes the already proved `OuterOneStep_8_1_31_formulaExtension` and
`SPSInnerBound_Proposition8_3_formulaOnXProcess`. -/
theorem sgs_selected_one_step_gap_recurrence_formulaExtension
    (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (k : PositiveTime) (hTpos : 0 < T k) (st : SGSState S) (ω : Ω)
    (u : FeasiblePoint S) :
    let xUnder := outerExtrapolation S gamma k st
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let inner := spsProcess S gk (smoothLinearization_isAffineModel S xUnder)
      st.x ⟨beta k, hbeta k⟩ (sample k)
    let next :=
      sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma
        (k.1 - 1) st ω
    objective S next.xbar.1 - objective S u.1 ≤
      (1 - gamma k) * (objective S st.xbar.1 - objective S u.1) +
        gamma k *
          (beta k * (1 - psWeightProduct spsP (T k))⁻¹ *
              (bregmanFormulaOnX S st.x u -
                bregmanFormulaOnX S next.x u) +
            psWeightProduct spsP (T k) *
              (1 - psWeightProduct spsP (T k))⁻¹ *
                (Finset.range (T k)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((inner i ω).u.1) (sample k i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
                      ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))) := by
  classical
  dsimp only
  let xUnder := outerExtrapolation S gamma k st
  let gk : E → ℝ := fun y => smoothLinearization S xUnder y
  let inner := spsProcess S gk (smoothLinearization_isAffineModel S xUnder)
    st.x ⟨beta k, hbeta k⟩ (sample k)
  let next :=
    sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma
      (k.1 - 1) st ω
  let P : ℝ := psWeightProduct spsP (T k)
  let invOneMinusP : ℝ := (1 - P)⁻¹
  let Vprev : ℝ := bregmanFormulaOnX S st.x u
  let Vcurr : ℝ := bregmanFormulaOnX S next.x u
  let noise : ℝ :=
    (Finset.range (T k)).sum (fun i =>
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
      let δ := oracleNoiseAt S ((inner i ω).u.1) (sample k i ω);
      (spsP ι * psWeightProduct spsP i)⁻¹ *
        (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
          ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))
  let phiGap : ℝ :=
    spsPhiFormulaOnX S gk st.x (beta k) (inner (T k) ω).avg -
      spsPhiFormulaOnX S gk st.x (beta k) u
  have hk_step : (⟨k.1 - 1 + 1, Nat.succ_pos (k.1 - 1)⟩ : PositiveTime) = k := by
    apply Subtype.ext
    exact Nat.sub_add_cancel k.2
  have hnext_x :
      next.x = (inner (T k) ω).u := by
    dsimp [next, inner, xUnder, gk, sgsTransition_formulaExtensionSelector,
      spsOutput, spsProcess]
    rw [hk_step]
    simp [positiveBetaSchedule]
  have houter :
      objective S next.xbar.1 - objective S u.1 ≤
        (1 - gamma k) * (objective S st.xbar.1 - objective S u.1) +
          gamma k * (phiGap + beta k * Vprev) := by
    have h :=
      OuterOneStep_8_1_31_formulaExtension S beta gamma T sample hbeta hgamma hlower
        k st ω u
    simpa [next, xUnder, gk, inner, phiGap, Vprev, spsOutput, spsProcess] using h
  have hprocess :
      IsSPSProcess S gk st.x (beta k) (sample k) inner := by
    simpa [inner] using
      spsProcess_isSPSProcess S gk (smoothLinearization_isAffineModel S xUnder)
        st.x ⟨beta k, hbeta k⟩ (sample k)
  let t : PositiveTime := ⟨T k, hTpos⟩
  have hsps :=
    SPSInnerBound_Proposition8_3_formulaOnXProcess S gk
      (smoothLinearization_isAffineModel S xUnder) st.x (beta k) (sample k)
      inner hprocess ω t u
  have hsps' :
      beta k * invOneMinusP * Vcurr + phiGap ≤
        beta k * P * invOneMinusP * Vprev + P * invOneMinusP * noise := by
    simpa [t, P, invOneMinusP, Vprev, Vcurr, noise, phiGap, hnext_x] using hsps
  have hPpos : 0 < P := by
    dsimp [P]
    rw [psWeightProduct_spsP_eq (T k)]
    positivity
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
    objective S next.xbar.1 - objective S u.1
        ≤ (1 - gamma k) * (objective S st.xbar.1 - objective S u.1) +
            gamma k * (phiGap + beta k * Vprev) := houter
    _ ≤ (1 - gamma k) * (objective S st.xbar.1 - objective S u.1) +
          gamma k *
            (beta k * invOneMinusP * (Vprev - Vcurr) +
              P * invOneMinusP * noise) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hscaled
              ((1 - gamma k) * (objective S st.xbar.1 - objective S u.1))
    _ =
      (1 - gamma k) * (objective S st.xbar.1 - objective S u.1) +
        gamma k *
          (beta k * (1 - psWeightProduct spsP (T k))⁻¹ *
              (bregmanFormulaOnX S st.x u -
                bregmanFormulaOnX S next.x u) +
            psWeightProduct spsP (T k) *
              (1 - psWeightProduct spsP (T k))⁻¹ *
                (Finset.range (T k)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((inner i ω).u.1) (sample k i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
                      ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))) := by
          simp [P, invOneMinusP, Vprev, Vcurr, noise]

/-- Formula-extension version of Eq. (8.1.69), the SGS master pathwise inequality.

This helper uses `bregmanFormulaOnX` for terms whose first argument is only known
to lie in `X`; it is not exported under the paper-original name because Section
3.2 types the source prox-function on `X^o × X`. -/
theorem SGSMasterInequality_8_1_69_formulaExtension (x0 : FeasiblePoint S)
    (beta gamma Gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (N : PositiveTime) (ω : Ω) (u : FeasiblePoint S)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T) :
    objectiveOn S
        (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma
          hgamma T sample N.1 ω) -
        objectiveOn S u ≤
      Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
          bregmanFormulaOnX S x0 u +
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let xUnder := outerExtrapolation S gamma κ
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω);
            let gk : E → ℝ := fun y => smoothLinearization S xUnder y;
            let inner := spsProcess_formulaExtensionSelector S gk (smoothLinearization_isAffineModel S xUnder)
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k ω).x
              ⟨beta κ, hbeta κ⟩ (sample κ);
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                (Finset.range (T κ)).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
    ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                      ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))) := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
    outer_gamma_positive_of_weight_condition_and_forward_denom beta gamma Gamma T
      hgamma hGamma hmono
  have hnoise_relax :=
    outer_inner_noise_square_relaxation_sum S x0 beta gamma Gamma T sample N ω u
      hbeta hgamma hGamma hmono
  have hstate_step :
      ∀ k : PositiveTime,
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k.1 ω =
          sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma
            (k.1 - 1)
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              (k.1 - 1) ω) ω := by
    intro k
    exact sgsProcess_formulaExtensionSelector_positiveTime_eq_transition
      S x0 beta hbeta gamma hgamma T sample k ω
  have hTpos_all : ∀ k : PositiveTime, 0 < T k :=
    positive_inner_budget_of_forwardMonotonicity beta gamma Gamma T hmono
  have hselected_step :
      ∀ k : PositiveTime,
        let stPrev :=
          sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            (k.1 - 1) ω
        let stCurr :=
          sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            k.1 ω
        let xUnder := outerExtrapolation S gamma k stPrev
        let gk : E → ℝ := fun y => smoothLinearization S xUnder y
        let inner := spsProcess_formulaExtensionSelector S gk
          (smoothLinearization_isAffineModel S xUnder) stPrev.x
          ⟨beta k, hbeta k⟩ (sample k)
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
                      let δ := oracleNoiseAt S ((inner i ω).u.1) (sample k i ω);
                      (spsP ι * psWeightProduct spsP i)⁻¹ *
                        (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
                          ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))) := by
    intro k
    let stPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
        (k.1 - 1) ω
    let stCurr :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
        k.1 ω
    let xUnder := outerExtrapolation S gamma k stPrev
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let inner := spsProcess_formulaExtensionSelector S gk
      (smoothLinearization_isAffineModel S xUnder) stPrev.x
      ⟨beta k, hbeta k⟩ (sample k)
    have hrec :=
      sgs_selected_one_step_gap_recurrence_formulaExtension
        S beta gamma T sample hbeta hgamma hlower k (hTpos_all k) stPrev ω u
    rw [← hstate_step k] at hrec
    simpa [stPrev, stCurr, xUnder, gk, inner,
      spsProcess, spsProcess_formulaExtensionSelector] using hrec
  let process : ℕ → SGSState S := fun n =>
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample n ω
  let A : ℕ → ℝ := fun n => objective S (process n).xbar.1 - objective S u.1
  let V : ℕ → ℝ := fun n => bregmanFormulaOnX S (process n).x u
  let alpha : ℕ → ℝ := fun n => if hn : 1 ≤ n then gamma ⟨n, hn⟩ else 0
  let GammaNat : ℕ → ℝ := fun n => if hn : 1 ≤ n then Gamma ⟨n, hn⟩ else 1
  let D : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then
      let κ : PositiveTime := ⟨n, hn⟩
      let stPrev := process (n - 1)
      let stCurr := process n
      let xUnder := outerExtrapolation S gamma κ stPrev
      let gk : E → ℝ := fun y => smoothLinearization S xUnder y
      let inner := spsProcess_formulaExtensionSelector S gk
        (smoothLinearization_isAffineModel S xUnder) stPrev.x
        ⟨beta κ, hbeta κ⟩ (sample κ)
      gamma κ *
        (beta κ * (1 - psWeightProduct spsP (T κ))⁻¹ *
            (V (n - 1) - V n) +
          psWeightProduct spsP (T κ) *
            (1 - psWeightProduct spsP (T κ))⁻¹ *
              (Finset.range (T κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω)
                (spsP ι * psWeightProduct spsP i)⁻¹ *
                  (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                    ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ)))
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
    have hs := hselected_step ⟨t, ht⟩
    simpa [A, D, alpha, process, V, ht] using hs
  have hrawIcc :
      A N.1 ≤ GammaNat N.1 *
        Finset.sum (Finset.Icc 1 N.1) (fun t => D t / GammaNat t) := by
    exact
      finite_window_weighted_recurrence_telescope_no_source
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
    have h :=
      forwardMonotonicity_nat_coeff_mono beta gamma Gamma T hmono n hn
    simpa [c, hn] using h
  have hc_nonneg : ∀ n, 1 ≤ n → 0 ≤ c n := by
    intro n hn
    let κ : PositiveTime := ⟨n, hn⟩
    have hOneSub : 0 < 1 - psWeightProduct spsP (T κ) :=
      one_sub_psWeightProduct_spsP_pos_of_pos (hTpos_all κ)
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
      sum_weighted_sub_le_first_of_forward_mono c V N.1 N.2
        hV_nonneg_window hc_mono htail
  have hV_zero : V 0 = bregmanFormulaOnX S x0 u := by
    simp [V, process, sgsProcess_formulaExtensionSelector,
      SOptLib.recursiveIterateProcess, sgsInitial]
  have hc_one :
      c 1 = beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ := by
    have hOne : (⟨1, by norm_num⟩ : PositiveTime) = oneTime := by
      ext
      rfl
    have hden :
        1 - psWeightProduct spsP (T oneTime) ≠ 0 :=
      ne_of_gt (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos_all oneTime))
    simp [c, hOne, hGamma.1, hlower.1, hden, div_eq_mul_inv]
  have hbregBoundary :
      c 1 * V 0 =
        beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
          bregmanFormulaOnX S x0 u := by
    rw [hc_one, hV_zero]
  let rawNoise : PositiveTime → ℝ := fun κ =>
    let stPrev := process (κ.1 - 1)
    let xUnder := outerExtrapolation S gamma κ stPrev
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let inner := spsProcess_formulaExtensionSelector S gk
      (smoothLinearization_isAffineModel S xUnder) stPrev.x
      ⟨beta κ, hbeta κ⟩ (sample κ)
    gamma κ * psWeightProduct spsP (T κ) /
      (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω)
          (spsP ι * psWeightProduct spsP i)⁻¹ *
            (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
              ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))
  let relaxedNoise : PositiveTime → ℝ := fun κ =>
    let stPrev := process (κ.1 - 1)
    let xUnder := outerExtrapolation S gamma κ stPrev
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let inner := spsProcess_formulaExtensionSelector S gk
      (smoothLinearization_isAffineModel S xUnder) stPrev.x
      ⟨beta κ, hbeta κ⟩ (sample κ)
    gamma κ * psWeightProduct spsP (T κ) /
      (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω)
          (spsP ι * psWeightProduct spsP i)⁻¹ *
            ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
              ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))
  let rawNoiseRange : ℝ :=
    (Finset.range N.1).sum (fun k => rawNoise ⟨k + 1, Nat.succ_pos k⟩)
  let relaxedNoiseRange : ℝ :=
    (Finset.range N.1).sum (fun k => relaxedNoise ⟨k + 1, Nat.succ_pos k⟩)
  let boundary : ℝ :=
    beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
      bregmanFormulaOnX S x0 u
  have hobj_eq :
      objectiveOn S
          (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            N.1 ω) -
        objectiveOn S u = A N.1 := by
    simp [A, process, sgsOutput_formulaExtensionSelector, objectiveOn]
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
    exact positiveTime_Icc_range_sum_reindex N.1 N.2 rawNoise
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
    simpa [rawNoiseRange, relaxedNoiseRange, rawNoise, relaxedNoise, process]
      using hnoise_relax
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
    objectiveOn S
        (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
          N.1 ω) -
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
              let xUnder := outerExtrapolation S gamma κ
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                  k ω);
              let gk : E → ℝ := fun y => smoothLinearization S xUnder y;
              let inner := spsProcess_formulaExtensionSelector S gk
                (smoothLinearization_isAffineModel S xUnder)
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                  k ω).x
                ⟨beta κ, hbeta κ⟩ (sample κ);
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                        ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ))) := by
      simp [boundary, relaxedNoiseRange, relaxedNoise, process]
      ring

/-- Formula-extension helper corresponding to Theorem 8.2(a).

This is boundary-corrected helper infrastructure, not the source-typed paper
theorem, because its bound uses `bregmanFormulaOnX`. -/
theorem SGSGenericConvergence_Theorem8_2_expected_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime)
    (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma
        hgamma T law.sample)) :
    (∫ ω,
        objectiveOn S
          (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma
            hgamma T law.sample N.1 ω) -
        objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
      genericExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N beta gamma Gamma T := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_unbiased
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hindep
  classical
  let query := sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample
  have hTpos : ∀ k : PositiveTime, 0 < T k :=
    positive_inner_budget_of_forwardMonotonicity beta gamma Gamma T hmono
  have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
    outer_gamma_positive_of_weight_condition_and_forward_denom beta gamma Gamma T
      hgamma hGamma hmono
  have hmaster :
      ∀ ω,
        objectiveOn S
            (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma
              hgamma T law.sample N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ ≤
        Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
            bregmanFormulaOnX S x0 ⟨xStar, hxStar.1⟩ +
          Gamma N *
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              let xUnder := outerExtrapolation S gamma κ
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
                  k ω);
              let gk : E → ℝ := fun y => smoothLinearization S xUnder y;
              let inner := spsProcess_formulaExtensionSelector S gk
                (smoothLinearization_isAffineModel S xUnder)
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
                  k ω).x
                ⟨beta κ, hbeta κ⟩ (law.sample κ);
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((inner i ω).u.1) (law.sample κ i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                        ⟪δ, xStar - (inner i ω).u.1⟫_ℝ))) := by
    intro ω
    simpa [query] using
      SGSMasterInequality_8_1_69_formulaExtension S x0 beta gamma Gamma T
        law.sample N ω ⟨xStar, hxStar.1⟩ hbeta hgamma hlower hGamma hmono
  have hquad :
      ∀ κ i,
        (∫ ω,
            dualNorm S (oracleNoiseAt S (query κ i ω) (law.sample κ i ω)) ^ 2
              ∂law.P) ≤ S.sigmaSq := by
    intro κ i
    rcases hgenerated_var κ i with ⟨_hquery, _hint, hle⟩
    simpa [query] using hle
  have hmean_integrable :
      ∀ κ i,
        Integrable (fun ω => S.oracle (query κ i ω) (law.sample κ i ω)) law.P ∧
          Integrable (fun ω => S.hSubgradient (query κ i ω)) law.P := by
    simpa [query] using
      generatedSFOUnbiased_integrable_obligation S law.P law.sample query hgenerated_mean
  have hmean_eq :
      ∀ κ i,
        (∫ ω, S.oracle (query κ i ω) (law.sample κ i ω) ∂law.P) =
          ∫ ω, S.hSubgradient (query κ i ω) ∂law.P := by
    intro κ i
    rcases hgenerated_mean κ i with ⟨_hquery, _horacle_int, _hmean_int, hEq⟩
    simpa [query] using hEq
  have hnoise_mean_zero :
      ∀ κ i,
        (∫ ω, oracleNoiseAt S (query κ i ω) (law.sample κ i ω) ∂law.P) = 0 := by
    intro κ i
    have hres_int :
        Integrable
          (fun ω => S.oracle (query κ i ω) (law.sample κ i ω) -
            S.hSubgradient (query κ i ω)) law.P :=
      (hmean_integrable κ i).1.sub (hmean_integrable κ i).2
    have hsplit :
        (∫ ω,
            S.oracle (query κ i ω) (law.sample κ i ω) -
              S.hSubgradient (query κ i ω) ∂law.P) =
          (∫ ω, S.oracle (query κ i ω) (law.sample κ i ω) ∂law.P) -
            ∫ ω, S.hSubgradient (query κ i ω) ∂law.P := by
      simpa using integral_sub (hmean_integrable κ i).1 (hmean_integrable κ i).2
    calc
      (∫ ω, oracleNoiseAt S (query κ i ω) (law.sample κ i ω) ∂law.P)
          = (∫ ω,
              S.oracle (query κ i ω) (law.sample κ i ω) -
                S.hSubgradient (query κ i ω) ∂law.P) := by
              simp [oracleNoiseAt]
      _ = (∫ ω, S.oracle (query κ i ω) (law.sample κ i ω) ∂law.P) -
            ∫ ω, S.hSubgradient (query κ i ω) ∂law.P := hsplit
      _ = 0 := by
            rw [hmean_eq κ i]
            exact sub_self _
  have hlinear_fixed_zero :
      ∀ κ i v,
        (∫ ω,
            ⟪oracleNoiseAt S (query κ i ω) (law.sample κ i ω), v⟫_ℝ ∂law.P) = 0 := by
    intro κ i v
    have hres_int :
        Integrable
          (fun ω => oracleNoiseAt S (query κ i ω) (law.sample κ i ω)) law.P := by
      simpa [oracleNoiseAt] using
        (hmean_integrable κ i).1.sub (hmean_integrable κ i).2
    have hlin :=
      ContinuousLinearMap.integral_comp_comm (L := (innerSL ℝ) v) hres_int
    calc
      (∫ ω,
          ⟪oracleNoiseAt S (query κ i ω) (law.sample κ i ω), v⟫_ℝ ∂law.P)
          = ∫ ω,
              ⟪v, oracleNoiseAt S (query κ i ω) (law.sample κ i ω)⟫_ℝ ∂law.P := by
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall (fun ω => by
                simpa using
                  real_inner_comm
                    v (oracleNoiseAt S (query κ i ω) (law.sample κ i ω)))
      _ = ((innerSL ℝ) v)
            (∫ ω, oracleNoiseAt S (query κ i ω) (law.sample κ i ω) ∂law.P) := hlin
      _ = 0 := by simp [hnoise_mean_zero κ i]
  have hquery_direction_zero :
      ∀ κ i,
        (∫ ω,
            ⟪oracleNoiseAt S (query κ i ω) (law.sample κ i ω),
              xStar - query κ i ω⟫_ℝ ∂law.P) = 0 := by
    simpa [query] using
      sgsOracleQuery_target_noise_inner_integral_zero
        (S := S) (law := law) x0 ⟨xStar, hxStar.1⟩ beta gamma T hbeta hgamma hindep
  let states := sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
  let inner := sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
  have hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner := by
    simpa [states, inner] using
      sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
        (S := S) x0 beta hbeta gamma hgamma T law.sample
  have hindep_generated :
      sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
    simpa [inner, sgsOracleQuery, sgsGeneratedOracleQuery] using hindep
  have hraw :=
    SGSGenericConvergence_Theorem8_2_expected_runFormulaExtension_under_gammaRange
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := T) (N := N)
      (states := states) (inner := inner)
      hrun hindep_generated hxStar hbeta hgamma hlower hGamma hmono
  simpa [states, inner, sgsOutput_formulaExtensionSelector, sgsGeneratedOutput,
    theorem82ExpectedBound_formulaExtension] using hraw

/-- Selected-run formula-extension helper for Theorem 8.2(b), high-probability
form under the explicit gamma-range guard.

This is the executable replacement route for the arbitrary relation-form
adaptedness boundary in the generic helper above.  The stochastic process is the
canonical selected Algorithm 8.2 realization, so the Lemma 4.1 coordinate
conditional facts are derived directly from `sgsSelectedGeneratedQueriesStrictPastAdapted`
and the one-coordinate conditional mean/light-tail bridges, not hidden behind a
theorem-head `SGSLinearMDSLightTailInterface` premise. -/
theorem SGSGenericConvergence_Theorem8_2_highProbability_selectedRunFormulaExtension_under_gammaRange
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (hcompact : IsCompact S.X) :
      law.P {ω | objectiveOn S
              (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
                N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ >
              genericExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩
                N beta gamma Gamma T +
              lambda *
                genericProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩
                  hcompact N beta gamma Gamma T} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  classical
  let uStar : FeasiblePoint S := ⟨xStar, hxStar.1⟩
  have hcoordinate_light : coordinateSFOLightTail S law.P law.sample :=
    sgsOracleLightTailAssumption_8_1_57.coordinate S law hlight
  have hlinear_int :
      ∀ κ i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                (law.sample κ i ω),
              uStar.1 -
                  sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ)
            law.P := by
    intro κ i
    simpa [uStar] using
      sgsOracleQuery_target_noise_inner_integrable
        (S := S) (law := law) x0 uStar beta gamma T hbeta hgamma hindep κ i
  let states := sgsSelectedStates S x0 beta hbeta gamma hgamma T law.sample
  let inner := sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma T law.sample
  have hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner := by
    simpa [states, inner, sgsSelectedStates, sgsSelectedInnerProcesses] using
      sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
        (S := S) x0 beta hbeta gamma hgamma T law.sample
  have hindep_generated :
      sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
    simpa [inner, sgsSelectedInnerProcesses, sgsOracleQuery, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery] using hindep
  have hlinear_int_generated :
      ∀ κ i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ)
          law.P := by
    intro κ i
    simpa [inner, sgsSelectedInnerProcesses, sgsOracleQuery, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery, uStar] using hlinear_int κ i
  have hadapted_run :
      sgsGeneratedQueriesStrictPastAdapted S law.sample inner := by
    simpa [inner, sgsSelectedInnerProcesses] using
      sgsSelectedGeneratedQueriesStrictPastAdapted
        (S := S) x0 beta hbeta gamma hgamma T law.sample law.sample_measurable
  have hquery_mem :
      ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X :=
    Classical.choose hindep_generated
  have hadapted :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω =>
            (⟨sgsGeneratedOracleQuery S inner κ i ω,
              hquery_mem κ i ω⟩ : FeasiblePoint S)) := by
    intro κ i
    exact
      sgsGeneratedOracleQuery_measurable_strictPastSampleSpace
        (S := S) (law := law) (x0 := x0) (beta := beta) (gamma := gamma)
        (T := T) (states := states) (inner := inner) hrun hadapted_run
        hquery_mem κ i
  have hquery_strictPast_meas :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω => sgsGeneratedOracleQuery S inner κ i ω) := by
    intro κ i
    exact measurable_subtype_coe.comp (hadapted κ i)
  have hlinear_condExp_zero :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] =ᵐ[law.P] 0 := by
    intro κ i
    simpa [uStar] using
      linear_tail_condExp_zero_of_strictPast_adapted
        (S := S) law uStar inner hindep_generated κ i (hadapted κ i)
        (hlinear_int_generated κ i)
  have hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
          law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
                sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
              fun _ => Real.exp 1 := by
    intro κ i
    simpa [uStar] using
      linear_tail_condExp_light_of_strictPast_adapted
        (S := S) law uStar inner hindep_generated hcoordinate_light hcompact
        κ i (hadapted κ i)
  have hlinear_exp_sq_integrable :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P := by
    intro κ i
    exact (hlinear_condExp_light κ i).1
  have hlinear_condExp_light_bound :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1 := by
    intro κ i
    exact (hlinear_condExp_light κ i).2
  have htail :=
    SGSGenericConvergence_Theorem8_2_highProbability_runFormulaExtension_from_mds_under_gammaRange
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := T)
      (N := N) (lambda := lambda) (states := states) (inner := inner)
      hrun hindep_generated hlambda hxStar hbeta hgamma hlight hlower hGamma
      hmono hcompact hquery_strictPast_meas hlinear_condExp_zero hlinear_exp_sq_integrable
      hlinear_condExp_light_bound
  simpa [states, inner, sgsSelectedStates, sgsSelectedInnerProcesses,
    sgsOutput_formulaExtensionSelector, sgsGeneratedOutput,
    theorem82ExpectedBound_formulaExtension, theorem82ProbabilityScale_formulaExtension]
    using htail

/-- Formal migration certificate for the previous arbitrary-run helper.

The exact relation-form conclusion is executable only after supplying the
missing causal-selector transport: the arbitrary generated output must agree
pointwise with the canonical selected Algorithm 8.2 output, and the selected
oracle queries must satisfy the source SFO independence premise.  Under that
explicit transport invariant, the previous arbitrary event is proved by the
selected-run theorem.  Without such a transport invariant, the relation-form
`states`/`inner` theorem remains non-executable for Eq. (8.1.70). -/
theorem SGSGenericConvergence_Theorem8_2_highProbability_runFormulaExtension_migration_certificate
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T)
    (hcompact : IsCompact S.X)
    (hselected_indep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (houtput_transport :
      ∀ ω,
        sgsGeneratedOutput S states N.1 ω =
          sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
            N.1 ω) :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ >
              theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N beta gamma Gamma T +
              lambda *
                theorem82ProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact N beta gamma Gamma T} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  classical
  have hselected :=
    SGSGenericConvergence_Theorem8_2_highProbability_selectedRunFormulaExtension_under_gammaRange
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := T)
      (N := N) (lambda := lambda) hlambda hxStar hbeta hgamma hlight
      hlower hGamma hmono hselected_indep hcompact
  simpa [houtput_transport, theorem82ExpectedBound_formulaExtension,
    theorem82ProbabilityScale_formulaExtension] using hselected

/-- Private selected-realization extension corresponding to Theorem 8.2(b),
high-probability bound.

The probability event is evaluated on `sgsSelectedOutput`, and this extension
now consumes the selected-run formula route rather than the arbitrary
relation-form generated-run helper. -/
theorem SGSGenericConvergence_Theorem8_2_highProbability_selectedRealizationExtension_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime) (lambda : ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
        (innerBudgetNat T) law.sample))
    (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T))
    (hcompact : IsCompact S.X) :
      sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
          (innerBudgetNat T) N xStar hxStar
        (theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
            beta gamma Gamma T
            (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
              hbeta hlower hGamma hmono) +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                hcompact N beta gamma Gamma T
                (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                  hbeta hlower hGamma hmono))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hdenom :
      theorem82DenominatorAdmissible beta Gamma (innerBudgetNat T) :=
    theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
      hbeta hlower hGamma hmono
  have hBd :
      theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          beta gamma Gamma T hdenom =
        theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N
          beta gamma Gamma (innerBudgetNat T) :=
    theorem82ExpectedBound_checked_eq_formulaExtension S x0 ⟨xStar, hxStar.1⟩
      N beta gamma Gamma T hdenom
  have hBp :
      theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta gamma Gamma T hdenom =
        theorem82ProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta gamma Gamma (innerBudgetNat T) :=
    theorem82ProbabilityScale_checked_eq_formulaExtension S ⟨xStar, hxStar.1⟩
      hcompact N beta gamma Gamma T hdenom
  have htail :=
    SGSGenericConvergence_Theorem8_2_highProbability_selectedRunFormulaExtension_under_gammaRange
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := innerBudgetNat T)
      (N := N) (lambda := lambda) hlambda hxStar hbeta hgamma hlight
      hlower hGamma hmono hindep hcompact
  rw [hBd, hBp]
  simpa [sgsSelectedOutputGapStrictTailProbability, outputGapStrictTailProbability,
    outputGapStrictTailProbabilityRaw, outputGapStrictTailEvent, outputGapRandomVariable,
    sgsGeneratedOutput, sgsSelectedStates, sgsSelectedOutput,
    sgsOutput_formulaExtensionSelector, theorem82ExpectedBound_formulaExtension,
    theorem82ProbabilityScale_formulaExtension] using htail

/-- Public selected-source-boundary Theorem 8.2(b) high-probability route.

The arbitrary generated-run statement remains as a non-executable compatibility
boundary until a causal-selector invariant is proved.  The active source route
for Algorithm 8.2(b) is the canonical selected SGS/SPS process, whose
strict-past martingale interface is supplied by the selected-run helper above. -/
theorem SGSGenericConvergence_Theorem8_2_highProbability_selectedSourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime) (lambda : ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
        (innerBudgetNat T) law.sample))
    (hmono : forwardMonotonicityCondition beta gamma Gamma (innerBudgetNat T))
    (hcompact : IsCompact S.X) :
      sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
          (innerBudgetNat T) N xStar hxStar
        (theorem82ExpectedBound_checkedFormulaExtension S x0 ⟨xStar, hxStar.1⟩ N
            beta gamma Gamma T
            (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
              hbeta hlower hGamma hmono) +
          lambda *
            theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                hcompact N beta gamma Gamma T
                (theorem82DenominatorAdmissible_forward_source_obligation S beta gamma Gamma T
                  hbeta hlower hGamma hmono))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  exact
    SGSGenericConvergence_Theorem8_2_highProbability_selectedRealizationExtension_feasibleBregman
      S law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hlambda hxStar
      hlight hlower hGamma hindep hmono hcompact

/-- Selected source-boundary run-level helper for Theorem 8.2(c),
high-probability form, with the selected-query light-tail assumption from
Eq. (8.1.57) and the bound written at the paper-facing formula-extension
boundary.

Theorem 8.2(c)'s proof says to repeat the high-probability proof of part (b)
using the reverse first-term replacement from Eq. (8.1.38).  The declaration is
placed after the reconstructed reverse `_from_mds` and selected-query
integrability leaves so this source theorem has an executable consumer path:
selected strict-past adaptedness supplies the MDS interface, and only the
lower-level finite large-deviation assembly remains as the local proof leaf. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_highProbability_selectedSourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime) (lambda : ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
        (innerBudgetNat T) law.sample))
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
        (innerBudgetNat T) N
        xStar hxStar
        (theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
              hcompact N beta gamma Gamma T
              (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                hbeta hlower hGamma hmono) +
            lambda *
              theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                hcompact N beta gamma Gamma T
                (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                  hbeta hlower hGamma hmono))
        hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  classical
  let uStar : FeasiblePoint S := ⟨xStar, hxStar.1⟩
  let states := sgsSelectedStates S x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample
  let inner := sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma
    (innerBudgetNat T) law.sample
  have hindep_oracle :
      sfoIndependent S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample) := by
    simpa [sgsOracleQuery, sgsSelectedOracleQuery] using hindep
  have hcoordinate_light : coordinateSFOLightTail S law.P law.sample :=
    sgsOracleLightTailAssumption_8_1_57.coordinate S law hlight
  have hlinear_int :
      ∀ κ i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma
                  (innerBudgetNat T) law.sample κ i ω)
                (law.sample κ i ω),
              uStar.1 -
                  sgsOracleQuery S x0 beta hbeta gamma hgamma
                    (innerBudgetNat T) law.sample κ i ω⟫_ℝ)
          law.P :=
    sgsOracleQuery_target_noise_inner_integrable
      (S := S) law x0 uStar beta gamma (innerBudgetNat T) hbeta hgamma hindep_oracle
  have hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma (innerBudgetNat T)
        law.sample states inner := by
    simpa [states, inner, sgsSelectedStates, sgsSelectedInnerProcesses] using
      sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
        (S := S) x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample
  have hindep_generated :
      sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
    simpa [inner, sgsSelectedInnerProcesses, sgsOracleQuery, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery] using hindep_oracle
  have hlinear_int_generated :
      ∀ κ i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ)
          law.P := by
    intro κ i
    simpa [inner, sgsSelectedInnerProcesses, sgsOracleQuery, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery, uStar] using hlinear_int κ i
  have hadapted_run :
      sgsGeneratedQueriesStrictPastAdapted S law.sample inner := by
    simpa [inner, sgsSelectedInnerProcesses] using
      sgsSelectedGeneratedQueriesStrictPastAdapted
        (S := S) x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample
        law.sample_measurable
  have hquery_mem :
      ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X :=
    Classical.choose hindep_generated
  have hadapted :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω =>
            (⟨sgsGeneratedOracleQuery S inner κ i ω,
              hquery_mem κ i ω⟩ : FeasiblePoint S)) := by
    intro κ i
    exact
      sgsGeneratedOracleQuery_measurable_strictPastSampleSpace
        (S := S) (law := law) (x0 := x0) (beta := beta) (gamma := gamma)
        (T := innerBudgetNat T) (states := states) (inner := inner) hrun
        hadapted_run hquery_mem κ i
  have hquery_strictPast_meas :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω => sgsGeneratedOracleQuery S inner κ i ω) := by
    intro κ i
    exact measurable_subtype_coe.comp (hadapted κ i)
  have hlinear_condExp_zero :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] =ᵐ[law.P] 0 := by
    intro κ i
    simpa [uStar] using
      linear_tail_condExp_zero_of_strictPast_adapted
        (S := S) law uStar inner hindep_generated κ i (hadapted κ i)
        (hlinear_int_generated κ i)
  have hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
          law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
                sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
              fun _ => Real.exp 1 := by
    intro κ i
    simpa [uStar] using
      linear_tail_condExp_light_of_strictPast_adapted
        (S := S) law uStar inner hindep_generated hcoordinate_light hcompact
        κ i (hadapted κ i)
  have hlinear_exp_sq_integrable :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P := by
    intro κ i
    exact (hlinear_condExp_light κ i).1
  have hlinear_condExp_light_bound :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1 := by
    intro κ i
    exact (hlinear_condExp_light κ i).2
  have hdenom :
      theorem82DenominatorAdmissible beta Gamma (innerBudgetNat T) :=
    theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
      hbeta hlower hGamma hmono
  have hBd :
      theorem82ReverseExpectedBound_checkedFormulaExtension S uStar hcompact N
          beta gamma Gamma T hdenom =
        gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
            (1 - psWeightProduct spsP (innerBudgetNat T N))⁻¹ +
          Gamma N *
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              (Finset.range (innerBudgetNat T κ)).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                (S.mGrowth ^ 2 + S.sigmaSq) * gamma κ *
                    psWeightProduct spsP (innerBudgetNat T κ) /
                  (beta κ * Gamma κ *
                    (1 - psWeightProduct spsP (innerBudgetNat T κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i))) :=
    theorem82ReverseExpectedBound_checked_eq_formulaExtension S uStar hcompact
      N beta gamma Gamma T hdenom
  have hBp :
      theorem82ProbabilityScale_checkedFormulaExtension S uStar hcompact N
          beta gamma Gamma T hdenom =
        theorem82ProbabilityScale_formulaExtension S uStar hcompact N beta gamma Gamma
          (innerBudgetNat T) :=
    theorem82ProbabilityScale_checked_eq_formulaExtension S uStar hcompact
      N beta gamma Gamma T hdenom
  have htail :=
    SGSGenericConvergence_Theorem8_2_reverse_highProbability_runFormulaExtension_from_mds
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := innerBudgetNat T)
      (N := N) (lambda := lambda) (states := states) (inner := inner)
      hrun hindep_generated hlambda hxStar hbeta hcompact hlight hlower hGamma hmono
      hgamma hquery_strictPast_meas hlinear_condExp_zero hlinear_exp_sq_integrable
      hlinear_condExp_light_bound
  rw [hBd, hBp]
  simpa [uStar, states, inner, sgsSelectedOutputGapStrictTailProbability,
    outputGapStrictTailProbability, outputGapStrictTailProbabilityRaw,
    outputGapStrictTailEvent, outputGapRandomVariable, sgsGeneratedOutput,
    sgsSelectedStates, sgsSelectedOutput, sgsSelectedInnerProcesses,
    sgsOutput_formulaExtensionSelector, theorem82ProbabilityScale_formulaExtension]
    using htail

/-- Compiled consumer for the reverse-monotone high-probability branch, pairing
the generated-query Assumption (8.1.57) projection with the public Theorem
8.2(c) probability bound. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_highProbability_generatedLightTail_consumer
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime) (lambda : ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
        (innerBudgetNat T) law.sample))
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    generatedSFOLightTail S law.P law.sample
        (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample) ∧
      sgsSelectedOutputGapStrictTailProbability S law x0 beta hbeta gamma hgamma
          (innerBudgetNat T) N
          xStar hxStar
          (theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                hcompact N beta gamma Gamma T
                (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                  hbeta hlower hGamma hmono) +
              lambda *
                theorem82ProbabilityScale_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
                  hcompact N beta gamma Gamma T
                  (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                    hbeta hlower hGamma hmono))
          hindep ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  refine ⟨?_, ?_⟩
  · exact sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample)
      hindep
  · exact SGSGenericConvergence_Theorem8_2_reverse_highProbability_selectedSourceBoundary_feasibleBregman
      S law x0 xStar beta gamma Gamma T N lambda hbeta hgamma hindep hlambda hxStar
      hcompact hlight hlower hGamma hmono

/-- Formula-extension helper corresponding to Theorem 8.2(b).

This is boundary-corrected helper infrastructure, not the source-typed paper
theorem, because its bound uses the feasible-formula envelope. -/
theorem SGSGenericConvergence_Theorem8_2_highProbability_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma
        hgamma T law.sample))
    (hcompact : IsCompact S.X) :
      law.P {ω | objectiveOn S
              (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma
                hgamma T law.sample N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ >
              genericExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N beta gamma Gamma T +
              lambda *
                genericProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact N beta gamma Gamma T} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  exact
    SGSGenericConvergence_Theorem8_2_highProbability_selectedRunFormulaExtension_under_gammaRange
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := T)
      (N := N) (lambda := lambda) hlambda hxStar hbeta hgamma hlight
      hlower hGamma hmono hindep hcompact

/-- Formula-extension helper corresponding to Theorem 8.2(c), expected form.

This is boundary-corrected helper infrastructure under the compact reverse
monotonicity condition, not the source-typed paper theorem. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_expected_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime)
    (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hcompact : IsCompact S.X)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma T)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma
        hgamma T law.sample)) :
    (∫ ω,
        objectiveOn S
          (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma
            hgamma T law.sample N.1 ω) -
        objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P) ≤
      gamma N * beta N * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
          (1 - psWeightProduct spsP (T N))⁻¹ +
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            (S.mGrowth ^ 2 + S.sigmaSq) * gamma κ * psWeightProduct spsP (T κ) /
                (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i))) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_unbiased
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hindep
  let states := sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
  let inner := sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
  have hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner := by
    simpa [states, inner] using
      sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
        S x0 beta hbeta gamma hgamma T law.sample
  have hindep_generated :
      sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
    simpa [inner, sgsOracleQuery, sgsGeneratedOracleQuery] using hindep
  have hraw :=
    SGSGenericConvergence_Theorem8_2_reverse_expected_runFormulaExtension
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma)
      (T := T) (N := N) (states := states) (inner := inner)
      hrun hindep_generated hxStar hbeta hcompact hlower hGamma hmono
  simpa [states, inner, sgsOutput_formulaExtensionSelector, sgsGeneratedOutput] using hraw

/-- Formula-extension helper corresponding to Theorem 8.2(c), high-probability
form.

This is boundary-corrected helper infrastructure under the compact reverse
monotonicity condition, not the source-typed paper theorem. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_highProbability_formulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma T)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma
        hgamma T law.sample)) :
    law.P {ω | objectiveOn S
            (sgsOutput_formulaExtensionSelector S x0 beta hbeta gamma
              hgamma T law.sample N.1 ω) -
          objectiveOn S ⟨xStar, hxStar.1⟩ >
            gamma N * beta N * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
                (1 - psWeightProduct spsP (T N))⁻¹ +
              Gamma N *
                (Finset.range N.1).sum (fun k =>
                  let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    (S.mGrowth ^ 2 + S.sigmaSq) * gamma κ * psWeightProduct spsP (T κ) /
                      (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                        spsP ι ^ 2 * psWeightProduct spsP i))) +
              lambda *
                genericProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact N beta gamma Gamma T} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_unbiased
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    law.generated_variance
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hindep
  have hgenerated_light :
      generatedSFOLightTail S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) :=
    sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hindep
  classical
  let uStar : FeasiblePoint S := ⟨xStar, hxStar.1⟩
  have hcoordinate_light : coordinateSFOLightTail S law.P law.sample :=
    sgsOracleLightTailAssumption_8_1_57.coordinate S law hlight
  have hlinear_int :
      ∀ κ i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                (law.sample κ i ω),
              uStar.1 -
                  sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ)
            law.P := by
    intro κ i
    simpa [uStar] using
      sgsOracleQuery_target_noise_inner_integrable
        (S := S) (law := law) x0 uStar beta gamma T hbeta hgamma hindep κ i
  let states := sgsSelectedStates S x0 beta hbeta gamma hgamma T law.sample
  let inner := sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma T law.sample
  have hrun :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner := by
    simpa [states, inner, sgsSelectedStates, sgsSelectedInnerProcesses] using
      sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
        (S := S) x0 beta hbeta gamma hgamma T law.sample
  have hindep_generated :
      sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
    simpa [inner, sgsSelectedInnerProcesses, sgsOracleQuery, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery] using hindep
  have hlinear_int_generated :
      ∀ κ i,
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ)
          law.P := by
    intro κ i
    simpa [inner, sgsSelectedInnerProcesses, sgsOracleQuery, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery, uStar] using hlinear_int κ i
  have hadapted_run :
      sgsGeneratedQueriesStrictPastAdapted S law.sample inner := by
    simpa [inner, sgsSelectedInnerProcesses] using
      sgsSelectedGeneratedQueriesStrictPastAdapted
        (S := S) x0 beta hbeta gamma hgamma T law.sample law.sample_measurable
  have hquery_mem :
      ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X :=
    Classical.choose hindep_generated
  have hadapted :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω =>
            (⟨sgsGeneratedOracleQuery S inner κ i ω,
              hquery_mem κ i ω⟩ : FeasiblePoint S)) := by
    intro κ i
    exact
      sgsGeneratedOracleQuery_measurable_strictPastSampleSpace
        (S := S) (law := law) (x0 := x0) (beta := beta) (gamma := gamma)
        (T := T) (states := states) (inner := inner) hrun hadapted_run
        hquery_mem κ i
  have hquery_strictPast_meas :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω => sgsGeneratedOracleQuery S inner κ i ω) := by
    intro κ i
    exact measurable_subtype_coe.comp (hadapted κ i)
  have hlinear_condExp_zero :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] =ᵐ[law.P] 0 := by
    intro κ i
    simpa [uStar] using
      linear_tail_condExp_zero_of_strictPast_adapted
        (S := S) law uStar inner hindep_generated κ i (hadapted κ i)
        (hlinear_int_generated κ i)
  have hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P ∧
          law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
                sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
              fun _ => Real.exp 1 := by
    intro κ i
    simpa [uStar] using
      linear_tail_condExp_light_of_strictPast_adapted
        (S := S) law uStar inner hindep_generated hcoordinate_light hcompact
        κ i (hadapted κ i)
  have hlinear_exp_sq_integrable :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P := by
    intro κ i
    exact (hlinear_condExp_light κ i).1
  have hlinear_condExp_light_bound :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1 := by
    intro κ i
    exact (hlinear_condExp_light κ i).2
  have htail :=
    SGSGenericConvergence_Theorem8_2_reverse_highProbability_runFormulaExtension_from_mds
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma) (T := T)
      (N := N) (lambda := lambda) (states := states) (inner := inner)
      hrun hindep_generated hlambda hxStar hbeta hcompact hlight hlower hGamma
      hmono hgamma hquery_strictPast_meas hlinear_condExp_zero
      hlinear_exp_sq_integrable hlinear_condExp_light_bound
  simpa [states, inner, sgsSelectedStates, sgsSelectedInnerProcesses,
    sgsOutput_formulaExtensionSelector, sgsGeneratedOutput,
    theorem82ProbabilityScale_formulaExtension] using htail

/-- Fixed-horizon forward monotonicity quotient normalized to its scalar
`2L/(1-P_T)` form.

Aligns with Lan Eq. (8.1.40) and Eq. (8.1.46).  Candidate audit: considered
`checkedQuotient_def`, `fixedHorizonBeta`, `fixedHorizonGamma`,
`fixedHorizonGammaWeight`, and generic SOptLib quotient/telescope helpers; this
is a paper-local closed-form cancellation, so it unfolds the fixed schedules
directly. -/
theorem fixed_horizon_forward_quotient_eq
    (T : PositiveTime → ℕ)
    (hdenom : monotonicityQuotientDenominators fixedHorizonGammaWeight T)
    (k : PositiveTime) :
    checkedQuotient (fixedHorizonGamma k * fixedHorizonBeta S k)
        (fixedHorizonGammaWeight k * (1 - psWeightProduct spsP (T k)))
        (hdenom k) =
      (2 * S.lSmooth) / (1 - psWeightProduct spsP (T k)) := by
  rw [checkedQuotient_def]
  unfold fixedHorizonGamma fixedHorizonBeta fixedHorizonGammaWeight
  have hk_pos : 0 < (k.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one k.2)
  have hk1_pos : 0 < (k.1 : ℝ) + 1 := by positivity
  have hgap_ne : 1 - psWeightProduct spsP (T k) ≠ 0 :=
    (mul_ne_zero_iff.mp (hdenom k)).2
  field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos, hgap_ne]

/-- Fixed-horizon Eq. (8.1.72) ceiling budgets are monotone between a paper
time and its predecessor.

Aligns with Lan Corollary 8.3 proof step 2, using the explicit budget
`T_k = ceil(N(M^2+σ^2)k^2/(\tilde D L^2))`.  Candidate audit: considered
`fixedHorizonInnerBudgetReal`, `fixedHorizonInnerBudget`,
`fixedHorizonInnerBudgetSource`, SOptLib ceiling helpers such as
`le_positive_ceil_max_one`, and the pre-searched telescope/process candidates;
none state this predecessor monotonicity for the SGS fixed-horizon ceiling, so
the proof specializes `Nat.ceil_mono` to Eq. (8.1.72). -/
theorem fixed_horizon_inner_budget_mono_pred
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (k : PositiveTime) (hk : 2 ≤ k.1) :
    innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) (predTime k hk) ≤
      innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k := by
  change fixedHorizonInnerBudget S N.1 Dtilde (predTime k hk) ≤
    fixedHorizonInnerBudget S N.1 Dtilde k
  unfold fixedHorizonInnerBudget
  apply Nat.ceil_mono
  unfold fixedHorizonInnerBudgetReal
  have hN_nonneg : 0 ≤ (N.1 : ℝ) := by positivity
  have hM2_nonneg : 0 ≤ S.mGrowth ^ 2 := sq_nonneg S.mGrowth
  have hvar_nonneg : 0 ≤ S.mGrowth ^ 2 + S.sigmaSq := by
    nlinarith [hM2_nonneg, S.sigmaSq_nonneg]
  have hcoef_nonneg : 0 ≤ (N.1 : ℝ) * (S.mGrowth ^ 2 + S.sigmaSq) :=
    mul_nonneg hN_nonneg hvar_nonneg
  have hden_pos : 0 < Dtilde * S.lSmooth ^ 2 :=
    mul_pos hDtilde (sq_pos_of_ne_zero (ne_of_gt S.L_pos))
  have hpred_cast : ((predTime k hk).1 : ℝ) = (k.1 : ℝ) - 1 := by
    unfold predTime
    rw [Nat.cast_sub (by omega : 1 ≤ k.1)]
    norm_num
  have hpred_sq_le : ((predTime k hk).1 : ℝ) ^ 2 ≤ (k.1 : ℝ) ^ 2 := by
    rw [hpred_cast]
    have hk_real : 2 ≤ (k.1 : ℝ) := by exact_mod_cast hk
    nlinarith
  have hnum_le :
      (N.1 : ℝ) * (S.mGrowth ^ 2 + S.sigmaSq) * ((predTime k hk).1 : ℝ) ^ 2 ≤
        (N.1 : ℝ) * (S.mGrowth ^ 2 + S.sigmaSq) * (k.1 : ℝ) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hpred_sq_le hcoef_nonneg
  exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)

/-- The explicit SPS product `P_t = 2/((t+1)(t+2))` is antitone in the positive
inner budget.

Aligns with Lan Eq. (8.1.44) and Eq. (8.1.45).  Candidate audit: considered
`psWeightProduct_spsP_eq`, `one_sub_psWeightProduct_spsP_pos_of_pos`,
`sps_step_weight_inv_eq`, and SOptLib output/telescope helpers; the existing
lemmas give the closed form or consume monotonicity, but none provide this
positive-budget antitone comparison, so this proof compares the explicit
quadratic denominators. -/
theorem sps_product_antitone_on_positive_budgets
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    psWeightProduct spsP n ≤ psWeightProduct spsP m := by
  rw [psWeightProduct_spsP_eq n, psWeightProduct_spsP_eq m]
  have hmn_real : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hden_m_pos : 0 < (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by positivity
  have hden_le :
      (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    have hleft : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
    have hright : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by linarith
    exact mul_le_mul hleft hright (by positivity) (le_of_lt (by positivity : 0 < (n : ℝ) + 1))
  exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hden_m_pos hden_le

/-- Ratio form of the explicit SPS product used in the stochastic term of
Lan Eq. (8.1.78).

Candidate audit: considered `psWeightProduct_spsP_eq`,
`one_sub_psWeightProduct_spsP_pos_of_pos`, `sps_step_weight_inv_eq`, and the
new antitone helper above.  They provide positivity or the product itself, but
not this quotient closed form, so the proof is the direct algebraic
specialization of Eq. (8.1.44). -/
theorem sps_product_ratio_eq {T : ℕ} (hT : 0 < T) :
    psWeightProduct spsP T / (1 - psWeightProduct spsP T) =
      2 / ((T : ℝ) * ((T : ℝ) + 3)) := by
  rw [psWeightProduct_spsP_eq T]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_ne : (((T : ℝ) + 1) * ((T : ℝ) + 2)) ≠ 0 := by positivity
  have htarget_ne : (T : ℝ) * ((T : ℝ) + 3) ≠ 0 := by positivity
  have htarget_ne' : (T : ℝ) * 3 + (T : ℝ) ^ 2 ≠ 0 := by
    positivity
  field_simp [hden_ne, htarget_ne, htarget_ne']
  have hden_eq :
      ((T : ℝ) + 1) * ((T : ℝ) + 2) - 2 =
        (T : ℝ) * ((T : ℝ) + 3) := by
    ring
  rw [hden_eq]
  exact div_self htarget_ne

/-- Positive-budget upper bound `P_T ≤ 1/3` for the SPS product.

Aligns with the compact-policy verification before Lan Eq. (8.1.51). Candidate
audit: considered `psWeightProduct_spsP_eq`,
`one_sub_psWeightProduct_spsP_pos_of_pos`, and
`sps_product_antitone_on_positive_budgets`; they provide the product closed form,
strict gap, or monotonicity, but not this endpoint bound used by the compact
outer lower condition. -/
theorem explicitP_le_one_third_of_pos {T : ℕ} (hT : 0 < T) :
    explicitP T ≤ (1 / 3 : ℝ) := by
  unfold explicitP
  have hTreal : 1 ≤ (T : ℝ) := by
    exact_mod_cast hT
  have hden_pos : 0 < (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by positivity
  rw [div_le_iff₀ hden_pos]
  nlinarith [sq_nonneg (T : ℝ)]

/-- Compact-policy reverse quotient closed form from Eq. (8.1.51).

Aligns with Lan Corollary 8.3 proof step 5. Candidate audit: considered
`fixed_horizon_outer_conditions`, `reverseMonotonicityCondition_checked_spec`,
`psWeightProduct_spsP_eq`, and the SOptLib weighted-output candidates from the
pre-search.  The fixed-horizon helper has the opposite schedule and monotonicity
orientation, while the generic predicates only consume the quotient relation;
this helper specializes the compact closed forms directly. -/
theorem compact_policy_reverse_quotient_eq
    (T : PositiveTime → ℕ)
    (hTpos : ∀ k : PositiveTime, 0 < T k)
    (hdenom : monotonicityQuotientDenominators compactGammaWeight T)
    (k : PositiveTime) :
    checkedQuotient (compactGamma k * compactBeta S T k)
        (compactGammaWeight k * (1 - psWeightProduct spsP (T k)))
        (hdenom k) =
      9 * S.lSmooth * (k.1 : ℝ) / 4 := by
  rw [checkedQuotient_def, psWeightProduct_spsP_eq (T k)]
  unfold compactGamma compactBeta compactGammaWeight explicitP
  have hk_pos : 0 < (k.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one k.2)
  have hk1_pos : 0 < (k.1 : ℝ) + 1 := by positivity
  have hk2_pos : 0 < (k.1 : ℝ) + 2 := by positivity
  have hGammaDen_ne :
      (k.1 : ℝ) * ((k.1 : ℝ) + 1) * ((k.1 : ℝ) + 2) ≠ 0 := by
    positivity
  have hgap_ne_raw : 1 - psWeightProduct spsP (T k) ≠ 0 :=
    (mul_ne_zero_iff.mp (hdenom k)).2
  have hgap_ne : 1 - 2 / (((T k : ℝ) + 1) * ((T k : ℝ) + 2)) ≠ 0 := by
    simpa [psWeightProduct_spsP_eq] using hgap_ne_raw
  have hTden_ne : (((T k : ℝ) + 1) * ((T k : ℝ) + 2)) ≠ 0 := by
    positivity
  have hTreal_pos : 0 < (T k : ℝ) := by
    exact_mod_cast hTpos k
  have hTtarget_ne : (T k : ℝ) * 3 + (T k : ℝ) ^ 2 ≠ 0 := by
    nlinarith [hTreal_pos]
  field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos, ne_of_gt hk2_pos,
    hGammaDen_ne, hgap_ne, hTden_ne, hTtarget_ne]
  have hA_ne :
      ((T k : ℝ) + 1) * ((T k : ℝ) + 2) - 2 ≠ 0 := by
    nlinarith [hTreal_pos, sq_nonneg (T k : ℝ)]
  field_simp [hA_ne]
  ring

/-- Compact schedules satisfy the outer hypotheses for Theorem 8.2(c).

Aligns with Lan Corollary 8.3 proof step 5, Eq. (8.1.50), and Eq. (8.1.51).
Candidate audit: considered `fixed_horizon_outer_conditions`,
`outerWeightCondition`, `reverseMonotonicityCondition_checked_spec`,
`one_sub_psWeightProduct_spsP_pos_of_pos`, `psWeightProduct_spsP_eq`, and the
pre-searched SOptLib selected-output candidates.  The fixed-horizon helper
proves a forward condition for different schedules; the generic predicates and
SOptLib output lemmas do not prove this compact schedule specialization. -/
theorem compact_policy_outer_conditions
    (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    outerLowerBoundCondition S
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        compactGamma ∧
      outerWeightCondition compactGamma compactGammaWeight ∧
        reverseMonotonicityCondition
          (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
          compactGamma compactGammaWeight
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · unfold compactGamma oneTime
      norm_num
    · intro k
      let T : PositiveTime → ℕ :=
        innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
      let P : ℝ := explicitP (T k)
      have hTpos : 0 < T k :=
        (compactInnerBudgetSource S Dtilde hDtilde k).2
      have hP_le : P ≤ (1 / 3 : ℝ) := by
        simpa [P] using explicitP_le_one_third_of_pos hTpos
      have hk_pos : 0 < (k.1 : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one k.2)
      have hk1_pos : 0 < (k.1 : ℝ) + 1 := by positivity
      have hk2_pos : 0 < (k.1 : ℝ) + 2 := by positivity
      have hgap_lower : (2 / 3 : ℝ) ≤ 1 - P := by
        linarith
      have hgap_mul :
          (2 / 3 : ℝ) * ((k.1 : ℝ) + 2) ≤ (1 - P) * ((k.1 : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hgap_lower (le_of_lt hk2_pos)
      have hbracket :
          0 ≤ 9 * (1 - P) * ((k.1 : ℝ) + 2) -
            2 * ((k.1 : ℝ) + 1) * 3 := by
        nlinarith [hgap_mul, hk_pos]
      unfold compactBeta compactGamma
      change
        0 ≤ 9 * S.lSmooth * (1 - P) / (2 * ((k.1 : ℝ) + 1)) -
          S.lSmooth * (3 / ((k.1 : ℝ) + 2))
      field_simp [ne_of_gt hk1_pos, ne_of_gt hk2_pos]
      simpa using mul_nonneg (le_of_lt S.L_pos) hbracket
  · constructor
    · unfold compactGammaWeight oneTime
      norm_num
    · intro k hk
      have hk_real : 2 ≤ (k.1 : ℝ) := by exact_mod_cast hk
      have hk_pos : 0 < (k.1 : ℝ) := by nlinarith
      have hkm1_pos : 0 < (k.1 : ℝ) - 1 := by nlinarith
      have hk1_pos : 0 < (k.1 : ℝ) + 1 := by nlinarith
      have hk2_pos : 0 < (k.1 : ℝ) + 2 := by nlinarith
      have hcast_pred : ((k.1 - 1 : ℕ) : ℝ) = (k.1 : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k.1)]
        norm_num
      change
        6 / ((k.1 : ℝ) * ((k.1 : ℝ) + 1) * ((k.1 : ℝ) + 2)) =
          (1 - 3 / ((k.1 : ℝ) + 2)) *
            (6 / (((k.1 - 1 : ℕ) : ℝ) *
              (((k.1 - 1 : ℕ) : ℝ) + 1) *
                (((k.1 - 1 : ℕ) : ℝ) + 2)))
      rw [hcast_pred]
      field_simp [ne_of_gt hk_pos, ne_of_gt hkm1_pos, ne_of_gt hk1_pos,
        ne_of_gt hk2_pos]
      ring
  · let T : PositiveTime → ℕ :=
        innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
    let hdenom :
        monotonicityQuotientDenominators compactGammaWeight T := by
      intro k
      have hGamma_pos : 0 < compactGammaWeight k := by
        unfold compactGammaWeight
        have hk_pos : 0 < (k.1 : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one k.2)
        have hk1_pos : 0 < (k.1 : ℝ) + 1 := by positivity
        have hk2_pos : 0 < (k.1 : ℝ) + 2 := by positivity
        exact div_pos (by norm_num) (mul_pos (mul_pos hk_pos hk1_pos) hk2_pos)
      have hgap :
          0 < 1 - psWeightProduct spsP (T k) :=
        one_sub_psWeightProduct_spsP_pos_of_pos
          ((compactInnerBudgetSource S Dtilde hDtilde k).2)
      exact mul_ne_zero (ne_of_gt hGamma_pos) (ne_of_gt hgap)
    refine ⟨hdenom, ?_⟩
    intro k hk
    have hTpos : ∀ j : PositiveTime, 0 < T j := by
      intro j
      exact (compactInnerBudgetSource S Dtilde hDtilde j).2
    rw [compact_policy_reverse_quotient_eq (S := S) T hTpos hdenom (predTime k hk),
      compact_policy_reverse_quotient_eq (S := S) T hTpos hdenom k]
    have hpred_le : ((predTime k hk).1 : ℝ) ≤ (k.1 : ℝ) := by
      exact_mod_cast Nat.sub_le k.1 1
    nlinarith [S.L_pos, hpred_le]

/-- Compact ceiling-budget ratio used in Lan Eq. (8.1.79).

Aligns with Corollary 8.3 proof step 6 after Eq. (8.1.75). Candidate audit:
considered `fixed_horizon_budget_ratio_without_three_le`, `compactInnerBudgetReal`,
`compactInnerBudget`, `Nat.le_ceil`, and SOptLib budget/telescope helpers.  The
fixed-horizon helper uses the different `Nk²` budget; no existing lemma states
the compact `(k+1)^3` ceiling consequence needed for Eq. (8.1.79). -/
theorem compact_budget_ratio_le
    (Dtilde : ℝ) (hDtilde : 0 < Dtilde) (k : PositiveTime) :
    (S.mGrowth ^ 2 + S.sigmaSq) * (k.1 : ℝ) * ((k.1 : ℝ) + 1) ^ 2 /
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) k : ℝ) ≤
      Dtilde * S.lSmooth ^ 2 := by
  let T : ℕ := innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) k
  let A : ℝ := S.mGrowth ^ 2 + S.sigmaSq
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg S.mGrowth, S.sigmaSq_nonneg]
  have hT_pos_nat : 0 < T :=
    (compactInnerBudgetSource S Dtilde hDtilde k).2
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast hT_pos_nat
  have hk_pos : 0 < (k.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one k.2)
  have hk_le : (k.1 : ℝ) ≤ (k.1 : ℝ) + 1 := by linarith
  have hk1_nonneg : 0 ≤ ((k.1 : ℝ) + 1) ^ 2 := sq_nonneg _
  have hDL2_pos : 0 < Dtilde * S.lSmooth ^ 2 :=
    mul_pos hDtilde (sq_pos_of_ne_zero (ne_of_gt S.L_pos))
  have hceil :
      compactInnerBudgetReal S Dtilde k ≤ (T : ℝ) := by
    change compactInnerBudgetReal S Dtilde k ≤
      (compactInnerBudget S Dtilde k : ℝ)
    unfold compactInnerBudget
    exact Nat.le_ceil _
  have hbase :
      A * ((k.1 : ℝ) + 1) ^ 3 ≤ (T : ℝ) * (Dtilde * S.lSmooth ^ 2) := by
    have h := hceil
    unfold compactInnerBudgetReal at h
    rw [div_le_iff₀ hDL2_pos] at h
    simpa [A, pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hnum_le :
      A * (k.1 : ℝ) * ((k.1 : ℝ) + 1) ^ 2 ≤
        A * ((k.1 : ℝ) + 1) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hk_le hA_nonneg
    have hmul2 := mul_le_mul_of_nonneg_right hmul hk1_nonneg
    nlinarith
  have hmul :
      A * (k.1 : ℝ) * ((k.1 : ℝ) + 1) ^ 2 ≤
        (T : ℝ) * (Dtilde * S.lSmooth ^ 2) :=
    le_trans hnum_le hbase
  rw [div_le_iff₀ hT_pos]
  simpa [T, A, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Compact first term in Eq. (8.1.79), after quotient cancellation.

Aligns with Lan Eq. (8.1.79), first displayed term. Candidate audit: considered
`compact_policy_reverse_quotient_eq`,
`theorem82ReverseExpectedBound_checked_eq_formulaExtension`,
`psWeightProduct_spsP_eq`, and `bregmanEnvelope_formulaExtension_nonneg`.
The reverse quotient helper normalizes the adjacent monotonicity quotient, while
this theorem records the actual terminal Bregman-envelope term used in the
public compact expected bound. -/
theorem compact_expected_bregman_term_eq_public
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    compactGamma N *
        compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) N *
        bregmanEnvelope_formulaExtension S xStar hcompact *
        (1 - psWeightProduct spsP
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) N))⁻¹ =
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * bregmanEnvelope_formulaExtension S xStar hcompact) / 2) := by
  let T : PositiveTime → ℕ :=
    innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
  let V : ℝ := bregmanEnvelope_formulaExtension S xStar hcompact
  have hTpos : 0 < T N :=
    (compactInnerBudgetSource S Dtilde hDtilde N).2
  have hgap : 0 < 1 - psWeightProduct spsP (T N) :=
    one_sub_psWeightProduct_spsP_pos_of_pos hTpos
  change
    compactGamma N * compactBeta S T N * V *
        (1 - psWeightProduct spsP (T N))⁻¹ =
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * V) / 2)
  rw [psWeightProduct_spsP_eq (T N)]
  unfold compactGamma compactBeta explicitP
  have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
  have hN2_pos : 0 < (N.1 : ℝ) + 2 := by positivity
  have hTden_ne : (((T N : ℝ) + 1) * ((T N : ℝ) + 2)) ≠ 0 := by
    positivity
  have hgap_ne :
      1 - 2 / (((T N : ℝ) + 1) * ((T N : ℝ) + 2)) ≠ 0 := by
    simpa [T, psWeightProduct_spsP_eq] using ne_of_gt hgap
  have hTreal_pos : 0 < (T N : ℝ) := by
    exact_mod_cast hTpos
  have hA_ne :
      ((T N : ℝ) + 1) * ((T N : ℝ) + 2) - 2 ≠ 0 := by
    nlinarith [hTreal_pos, sq_nonneg (T N : ℝ)]
  field_simp [ne_of_gt hN1_pos, ne_of_gt hN2_pos, hTden_ne, hgap_ne, hA_ne]
  ring

/-- SPS squared-denominator finite-sum estimate used in Lan Eq. (8.1.78)
and the compact stochastic part of Eq. (8.1.79).

Candidate audit: considered `sps_step_weight_inv_eq`,
`sps_normalized_weight_sum_eq_one`, `psWeightProduct_spsP_eq`, and SOptLib
finite-sum/telescope helpers.  The existing local identities normalize nearby
SPS weights, but this exact squared-denominator summand is specific to the
SGS stochastic term, so the proof specializes `psWeightProduct_spsP_eq` and
then sums the pointwise bound. -/
theorem sps_inner_weight_sum_le_four_budget (T : ℕ) :
    (Finset.range T).sum (fun i =>
      ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
        psWeightProduct spsP i)⁻¹) ≤ 4 * (T : ℝ) := by
  have hpoint : ∀ i : ℕ,
      ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
        psWeightProduct spsP i)⁻¹ ≤ (4 : ℝ) := by
    intro i
    have hterm :
        ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
          psWeightProduct spsP i)⁻¹ =
          2 * ((i : ℝ) + 2) / ((i : ℝ) + 1) := by
      rw [spsP, psWeightProduct_spsP_eq i]
      have hi1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
      rw [hi1]
      have h1 : (i : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (i : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
    rw [hterm]
    have hden_pos : 0 < (i : ℝ) + 1 := by positivity
    rw [div_le_iff₀ hden_pos]
    nlinarith
  calc
    (Finset.range T).sum (fun i =>
        ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
          psWeightProduct spsP i)⁻¹)
        ≤ (Finset.range T).sum (fun _ => (4 : ℝ)) := by
          exact Finset.sum_le_sum (fun i _ => hpoint i)
    _ = 4 * (T : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Squared-gap SPS product ratio used in the compact stochastic term of
Lan Eq. (8.1.79).

Candidate audit: considered `psWeightProduct_spsP_eq`,
`one_sub_psWeightProduct_spsP_pos_of_pos`, `sps_product_ratio_eq`, and the
pre-searched SOptLib output/telescope candidates.  They provide the product,
positivity, or the one-gap quotient, but Eq. (8.1.79) needs the compact
two-gap ratio, so this helper proves the explicit scalar inequality from
Eq. (8.1.44). -/
theorem sps_product_gap_square_ratio_le_two_inv_sq {T : ℕ} (hT : 0 < T) :
    psWeightProduct spsP T * (1 - psWeightProduct spsP T)⁻¹ *
        (1 - psWeightProduct spsP T)⁻¹ ≤
      2 / (T : ℝ) ^ 2 := by
  rw [psWeightProduct_spsP_eq T]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hden_pos : 0 < (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by positivity
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hTreal
  have hden_ne : (((T : ℝ) + 1) * ((T : ℝ) + 2)) ≠ 0 := ne_of_gt hden_pos
  have hgap_pos :
      0 < 1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    rw [sub_pos]
    exact (div_lt_one hden_pos).2 (by nlinarith [sq_nonneg (T : ℝ)])
  have hgap_ne : 1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) ≠ 0 :=
    ne_of_gt hgap_pos
  have hleft_eq :
      2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) *
          (1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)))⁻¹ *
          (1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)))⁻¹ =
        (2 * (((T : ℝ) + 1) * ((T : ℝ) + 2))) /
          ((T : ℝ) ^ 2 * ((T : ℝ) + 3) ^ 2) := by
    have hgap_eq :
        1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) =
          ((T : ℝ) * ((T : ℝ) + 3)) /
            (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by
      field_simp [hden_ne]
      ring
    rw [hgap_eq]
    have hT3_ne : (T : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hden_ne, hT_ne, hT3_ne]
  rw [hleft_eq]
  have hden_total_pos : 0 < (T : ℝ) ^ 2 * ((T : ℝ) + 3) ^ 2 := by
    positivity
  rw [div_le_div_iff₀ hden_total_pos (sq_pos_of_ne_zero hT_ne)]
  nlinarith [sq_nonneg ((T : ℝ) + 3), sq_nonneg (T : ℝ)]

/-- Scalar denominator split for stochastic summands in Lan Eq. (8.1.78) and
Eq. (8.1.79).

Candidate audit: considered Mathlib ordered-field simplification lemmas and the
local SPS schedule identities; no existing lemma packages this exact six-factor
quotient split, so this keeps paper-specific row proofs focused on source
ratios. -/
theorem stochastic_summand_fraction_split {A gamma P beta Gamma gap Q : ℝ}
    (hbeta : beta ≠ 0) (hGamma : Gamma ≠ 0) (hgap : gap ≠ 0) (hQ : Q ≠ 0) :
    A * gamma * P / (beta * Gamma * gap * Q) =
      A * (gamma / (beta * Gamma)) * (P / gap) * Q⁻¹ := by
  field_simp [hbeta, hGamma, hgap, hQ, mul_ne_zero hbeta hGamma]

/-- Compact schedule coefficient in the stochastic summand of Lan Eq. (8.1.79).

Candidate audit: considered `compact_policy_reverse_quotient_eq`,
`compactGamma`, `compactBeta`, `compactGammaWeight`, and SOptLib
output/telescope helpers.  The quotient helper normalizes the reverse
monotonicity coefficient, while Eq. (8.1.79) needs this stochastic coefficient
with one explicit SPS gap in the denominator. -/
theorem compact_stochastic_schedule_coeff_eq
    (T : PositiveTime → ℕ) {κ : PositiveTime} (hTκ : 0 < T κ) :
    compactGamma κ / (compactBeta S T κ * compactGammaWeight κ) =
      ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) /
        (9 * S.lSmooth * (1 - psWeightProduct spsP (T κ))) := by
  have hP_eq : explicitP (T κ) = psWeightProduct spsP (T κ) := by
    simpa [explicitP] using (psWeightProduct_spsP_eq (T κ)).symm
  have hk_pos : 0 < (κ.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
  have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
  have hk2_pos : 0 < (κ.1 : ℝ) + 2 := by positivity
  have hgap_pos : 0 < 1 - psWeightProduct spsP (T κ) :=
    one_sub_psWeightProduct_spsP_pos_of_pos hTκ
  have hgap_ne : 1 - psWeightProduct spsP (T κ) ≠ 0 := ne_of_gt hgap_pos
  unfold compactGamma compactBeta compactGammaWeight
  rw [hP_eq]
  field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos, ne_of_gt hk2_pos,
    ne_of_gt S.L_pos, hgap_ne]
  ring

/-- Pointwise compact stochastic summand normalization in Lan Eq. (8.1.79).

Candidate audit: considered `sps_product_gap_square_ratio_le_two_inv_sq`,
`compact_stochastic_schedule_coeff_eq`, `stochastic_summand_fraction_split`,
and SOptLib finite-sum/telescope candidates.  The listed local helpers expose
the source ratios, but no existing theorem combines the compact schedules with
the squared SPS denominator for a single Eq. (8.1.79) summand. -/
theorem compact_stochastic_summand_eq_of_pos
    (T : PositiveTime → ℕ) {κ : PositiveTime} (hTκ : 0 < T κ) (i : ℕ) :
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
    (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
        psWeightProduct spsP (T κ) /
      (compactBeta S T κ * compactGammaWeight κ *
        (1 - psWeightProduct spsP (T κ)) *
          spsP ι ^ 2 * psWeightProduct spsP i) =
    (((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) /
        (9 * S.lSmooth)) *
      (psWeightProduct spsP (T κ) *
        (1 - psWeightProduct spsP (T κ))⁻¹ *
          (1 - psWeightProduct spsP (T κ))⁻¹) *
      ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
  intro ι
  have hP_eq : explicitP (T κ) = psWeightProduct spsP (T κ) := by
    simpa [explicitP] using (psWeightProduct_spsP_eq (T κ)).symm
  have hgap_pos : 0 < 1 - psWeightProduct spsP (T κ) :=
    one_sub_psWeightProduct_spsP_pos_of_pos hTκ
  have hgap_ne : 1 - psWeightProduct spsP (T κ) ≠ 0 := ne_of_gt hgap_pos
  have hb : compactBeta S T κ ≠ 0 := by
    unfold compactBeta
    rw [hP_eq]
    have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
    exact ne_of_gt
      (div_pos (mul_pos (mul_pos (by norm_num) S.L_pos) hgap_pos)
        (mul_pos (by norm_num) hk1_pos))
  have hG : compactGammaWeight κ ≠ 0 := by
    unfold compactGammaWeight
    have hk_pos : 0 < (κ.1 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
    have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
    have hk2_pos : 0 < (κ.1 : ℝ) + 2 := by positivity
    exact ne_of_gt (div_pos (by norm_num) (mul_pos (mul_pos hk_pos hk1_pos) hk2_pos))
  have hsps_pos : 0 < spsP ι := by
    unfold spsP
    positivity
  have hPi_pos : 0 < psWeightProduct spsP i := by
    rw [psWeightProduct_spsP_eq i]
    positivity
  have hQ : spsP ι ^ 2 * psWeightProduct spsP i ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (ne_of_gt hsps_pos)) (ne_of_gt hPi_pos)
  calc
    (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
        psWeightProduct spsP (T κ) /
      (compactBeta S T κ * compactGammaWeight κ *
        (1 - psWeightProduct spsP (T κ)) *
          spsP ι ^ 2 * psWeightProduct spsP i)
        =
      (S.mGrowth ^ 2 + S.sigmaSq) *
        (compactGamma κ / (compactBeta S T κ * compactGammaWeight κ)) *
        (psWeightProduct spsP (T κ) / (1 - psWeightProduct spsP (T κ))) *
        (spsP ι ^ 2 * psWeightProduct spsP i)⁻¹ := by
          simpa [mul_assoc] using
            (stochastic_summand_fraction_split
              (A := S.mGrowth ^ 2 + S.sigmaSq)
              (gamma := compactGamma κ)
              (P := psWeightProduct spsP (T κ))
              (beta := compactBeta S T κ)
              (Gamma := compactGammaWeight κ)
              (gap := 1 - psWeightProduct spsP (T κ))
              (Q := spsP ι ^ 2 * psWeightProduct spsP i)
              hb hG hgap_ne hQ)
    _ =
      (((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) /
          (9 * S.lSmooth)) *
        (psWeightProduct spsP (T κ) *
          (1 - psWeightProduct spsP (T κ))⁻¹ *
            (1 - psWeightProduct spsP (T κ))⁻¹) *
        ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
        rw [compact_stochastic_schedule_coeff_eq (S := S) T hTκ]
        field_simp [ne_of_gt S.L_pos, hgap_ne]

/-- Per-outer-iteration compact stochastic inner-sum normalization in
Lan Eq. (8.1.79).

Candidate audit: considered the now-available
`sps_inner_weight_sum_le_four_budget`,
`sps_product_gap_square_ratio_le_two_inv_sq`,
`compact_stochastic_summand_eq_of_pos`, and SOptLib finite-sum/telescope
helpers.  The target-file helpers provide exactly the Eq. (8.1.44) SPS ratio
and finite inner-weight estimate; no existing declaration packages the compact
Eq. (8.1.79) per-`κ` stochastic row. -/
theorem compact_stochastic_inner_sum_le
    (Dtilde : ℝ) (hDtilde : 0 < Dtilde) (κ : PositiveTime) :
    (Finset.range
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
      (fun i =>
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
        (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
          (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
            compactGammaWeight κ *
            (1 - psWeightProduct spsP
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i)) ≤
      (8 / (9 * S.lSmooth)) *
        ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 /
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ)) := by
  classical
  let T : PositiveTime → ℕ := innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)
  let Tκ : ℕ := T κ
  let A : ℝ := S.mGrowth ^ 2 + S.sigmaSq
  let C : ℝ := (A * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (9 * S.lSmooth)
  let R : ℝ :=
    psWeightProduct spsP Tκ * (1 - psWeightProduct spsP Tκ)⁻¹ *
      (1 - psWeightProduct spsP Tκ)⁻¹
  let B : ℝ := C * (2 / (Tκ : ℝ) ^ 2)
  have hTκ_pos_nat : 0 < Tκ :=
    (compactInnerBudgetSource S Dtilde hDtilde κ).2
  have hTκ_pos : 0 < (Tκ : ℝ) := by exact_mod_cast hTκ_pos_nat
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg S.mGrowth, S.sigmaSq_nonneg]
  have hk_pos : 0 < (κ.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hA_nonneg (le_of_lt hk_pos)) (sq_nonneg _))
      (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
  have hratio :
      R ≤ 2 / (Tκ : ℝ) ^ 2 := by
    simpa [R] using
      (sps_product_gap_square_ratio_le_two_inv_sq (T := Tκ) hTκ_pos_nat)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hC_nonneg
      (div_nonneg (by norm_num) (sq_nonneg (Tκ : ℝ)))
  have hpoint : ∀ i ∈ Finset.range Tκ,
      C * R *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹ ≤
        B *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹ := by
    intro i _hi
    have hsps_pos : 0 < spsP ⟨i + 1, Nat.succ_pos i⟩ := by
      unfold spsP
      positivity
    have hPi_pos : 0 < psWeightProduct spsP i := by
      rw [psWeightProduct_spsP_eq i]
      positivity
    have hQinv_nonneg :
        0 ≤ ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹ := by
      exact le_of_lt (inv_pos.mpr
        (mul_pos (pow_pos hsps_pos 2) hPi_pos))
    have hcoeff :
        C * R ≤ B := by
      dsimp [B]
      exact mul_le_mul_of_nonneg_left hratio hC_nonneg
    exact mul_le_mul_of_nonneg_right hcoeff hQinv_nonneg
  have hweights := sps_inner_weight_sum_le_four_budget Tκ
  have hmul :
      B *
          (Finset.range Tκ).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹) ≤
        B * (4 * (Tκ : ℝ)) :=
    mul_le_mul_of_nonneg_left hweights hB_nonneg
  calc
    (Finset.range
        (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
      (fun i =>
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
        (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
          (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
            compactGammaWeight κ *
            (1 - psWeightProduct spsP
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i))
        =
      (Finset.range Tκ).sum (fun i =>
        C * R *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹) := by
          refine Finset.sum_congr ?_ ?_
          · simp [T, Tκ]
          · intro i _hi
            simpa [T, Tκ, A, C, R] using
              (compact_stochastic_summand_eq_of_pos (S := S)
                T hTκ_pos_nat i)
    _ ≤
      (Finset.range Tκ).sum (fun i =>
        B *
          ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
            psWeightProduct spsP i)⁻¹) := by
        exact Finset.sum_le_sum hpoint
    _ =
      B * (Finset.range Tκ).sum (fun i =>
        ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
          psWeightProduct spsP i)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ B * (4 * (Tκ : ℝ)) := hmul
    _ =
      (8 / (9 * S.lSmooth)) *
        ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 /
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ)) := by
        dsimp [B, C, A, Tκ, T]
        field_simp [ne_of_gt S.L_pos, ne_of_gt hTκ_pos]
        ring

/-- Outer aggregation of compact stochastic rows in Lan Eq. (8.1.79).

Candidate audit: considered `compact_stochastic_inner_sum_le`,
`compact_budget_ratio_le`, `Finset.sum_le_sum`, `Finset.sum_const`, and SOptLib
finite-window/telescope candidates.  The local row and budget helpers give the
exact source ingredients for the compact public `16/3` constant; no existing
declaration assembles this Eq. (8.1.79) stochastic double-sum. -/
theorem compact_stochastic_outer_sum_le_public
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
            (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                  psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
                (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
                  compactGammaWeight κ *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i))) ≤
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((16 * Dtilde) / 3) := by
  classical
  let C : ℝ := 8 * Dtilde * S.lSmooth / 9
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
  have hN2_pos : 0 < (N.1 : ℝ) + 2 := by positivity
  have hGamma_nonneg : 0 ≤ compactGammaWeight N := by
    unfold compactGammaWeight
    positivity
  have hscale_nonneg : 0 ≤ 8 / (9 * S.lSmooth) := by
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
  have hpoint : ∀ k ∈ Finset.range N.1,
      (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
       (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
              compactGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)) ≤ C) := by
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    have hinner := compact_stochastic_inner_sum_le (S := S) Dtilde hDtilde κ
    have hbudget := compact_budget_ratio_le (S := S) Dtilde hDtilde κ
    have hbudget_scaled :
        (8 / (9 * S.lSmooth)) *
            ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 /
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ)) ≤
          (8 / (9 * S.lSmooth)) * (Dtilde * S.lSmooth ^ 2) :=
      mul_le_mul_of_nonneg_left hbudget hscale_nonneg
    calc
      (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
            (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
              compactGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i))
          ≤
        (8 / (9 * S.lSmooth)) *
            ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 /
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ : ℝ)) :=
          hinner
      _ ≤ (8 / (9 * S.lSmooth)) * (Dtilde * S.lSmooth ^ 2) :=
          hbudget_scaled
      _ = C := by
          dsimp [C]
          field_simp [ne_of_gt S.L_pos]
  have hsum :
      (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
            (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                  psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
                (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
                  compactGammaWeight κ *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i))) ≤
        (N.1 : ℝ) * C := by
    calc
      (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
            (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                  psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
                (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
                  compactGammaWeight κ *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i)))
          ≤ (Finset.range N.1).sum (fun _ => C) := by
            exact Finset.sum_le_sum hpoint
      _ = (N.1 : ℝ) * C := by
            simp [Finset.sum_const, nsmul_eq_mul]
  calc
    compactGammaWeight N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (Finset.range
              (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
            (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                  psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
                (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)) κ *
                  compactGammaWeight κ *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i)))
        ≤ compactGammaWeight N * ((N.1 : ℝ) * C) := by
          exact mul_le_mul_of_nonneg_left hsum hGamma_nonneg
    _ =
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((16 * Dtilde) / 3) := by
          unfold compactGammaWeight
          dsimp [C]
          field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos, ne_of_gt hN2_pos,
            ne_of_gt S.L_pos]
          ring

/-- Compact public scalar simplification of the checked Theorem 8.2(c) expected
bound.

Aligns with Lan Eq. (8.1.79). Candidate audit: considered
`theorem82ReverseExpectedBound_checked_eq_formulaExtension`,
`compact_expected_bregman_term_eq_public`, `compact_budget_ratio_le`,
`sps_inner_weight_sum_le_four_budget`, `Finset.sum_le_sum`, and SOptLib
finite-window/telescope candidates.  The existing helpers provide quotient
normalization, compact ceiling control, and SPS inner summation, but no existing
declaration assembles the compact reverse expected public constant `16/3`. -/
theorem compact_reverse_expected_checked_bound_le_public
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (hdenom : theorem82DenominatorAdmissible
      (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
      compactGammaWeight
      (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde))) :
    theorem82ReverseExpectedBound_checkedFormulaExtension S xStar hcompact N
        (compactBeta S (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde)))
        compactGamma compactGammaWeight
        (compactInnerBudgetSource S Dtilde hDtilde) hdenom ≤
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * bregmanEnvelope_formulaExtension S xStar hcompact) / 2 +
          (16 * Dtilde) / 3) := by
  classical
  rw [theorem82ReverseExpectedBound_checked_eq_formulaExtension]
  let Tsrc : PositiveTime → InnerBudget := compactInnerBudgetSource S Dtilde hDtilde
  let T : PositiveTime → ℕ := innerBudgetNat Tsrc
  let V : ℝ := bregmanEnvelope_formulaExtension S xStar hcompact
  have hfirst :
      compactGamma N * compactBeta S T N * V *
          (1 - psWeightProduct spsP (T N))⁻¹ =
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((27 * V) / 2) := by
    simpa [Tsrc, T, V] using
      compact_expected_bregman_term_eq_public (S := S) xStar hcompact
        N Dtilde hDtilde
  have hstoch :
      compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                  psWeightProduct spsP (T κ) /
                (compactBeta S T κ * compactGammaWeight κ *
                  (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i))) ≤
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((16 * Dtilde) / 3) := by
    simpa [Tsrc, T] using
      compact_stochastic_outer_sum_le_public (S := S) N Dtilde hDtilde
  calc
    compactGamma N * compactBeta S T N * V *
          (1 - psWeightProduct spsP (T N))⁻¹ +
        compactGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (S.mGrowth ^ 2 + S.sigmaSq) * compactGamma κ *
                  psWeightProduct spsP (T κ) /
                (compactBeta S T κ * compactGammaWeight κ *
                  (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i)))
        ≤
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((27 * V) / 2) +
        S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
          ((16 * Dtilde) / 3) := by
        exact add_le_add (le_of_eq hfirst) hstoch
    _ =
      S.lSmooth / (((N.1 : ℝ) + 1) * ((N.1 : ℝ) + 2)) *
        ((27 * V) / 2 + (16 * Dtilde) / 3) := by
        ring

/-- Fixed-horizon schedules satisfy the three Theorem 8.2(a) outer hypotheses.

Aligns with Lan Eq. (8.1.40), Eq. (8.1.46), and the forward monotonicity
condition used in Corollary 8.3(a).  Candidate audit: considered
`outerWeightCondition`, `forwardMonotonicityCondition_checked_spec`,
`one_sub_psWeightProduct_spsP_pos_of_pos`, `psWeightProduct_spsP_eq`, and the
SOptLib telescope/output-window candidates from the pre-search; none packages
the fixed-horizon closed forms with the Eq. (8.1.72) ceiling budget, so this
helper specializes the local schedule definitions directly. -/
theorem fixed_horizon_outer_conditions
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    outerLowerBoundCondition S (fixedHorizonBeta S) fixedHorizonGamma ∧
      outerWeightCondition fixedHorizonGamma fixedHorizonGammaWeight ∧
        forwardMonotonicityCondition (fixedHorizonBeta S) fixedHorizonGamma
          fixedHorizonGammaWeight
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · unfold fixedHorizonGamma oneTime
      norm_num
    · intro k
      unfold fixedHorizonBeta fixedHorizonGamma
      have hk_pos : 0 < (k.1 : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one k.2)
      have hk1_pos : 0 < (k.1 : ℝ) + 1 := by positivity
      have hprod_pos : 0 < (k.1 : ℝ) * ((k.1 : ℝ) + 1) :=
        mul_pos hk_pos hk1_pos
      have hrewrite :
          2 * S.lSmooth / (k.1 : ℝ) -
              S.lSmooth * (2 / ((k.1 : ℝ) + 1)) =
            2 * S.lSmooth / ((k.1 : ℝ) * ((k.1 : ℝ) + 1)) := by
        field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos, ne_of_gt hprod_pos]
        ring
      rw [hrewrite]
      exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt S.L_pos))
        (le_of_lt hprod_pos)
  · constructor
    · unfold fixedHorizonGammaWeight oneTime
      norm_num
    · intro k hk
      have hk_real : 2 ≤ (k.1 : ℝ) := by exact_mod_cast hk
      have hk_pos : 0 < (k.1 : ℝ) := by nlinarith
      have hkm1_pos : 0 < (k.1 : ℝ) - 1 := by nlinarith
      have hk1_pos : 0 < (k.1 : ℝ) + 1 := by nlinarith
      have hcast_pred : ((k.1 - 1 : ℕ) : ℝ) = (k.1 : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k.1)]
        norm_num
      change
        2 / ((k.1 : ℝ) * ((k.1 : ℝ) + 1)) =
          (1 - 2 / ((k.1 : ℝ) + 1)) *
            (2 / (((k.1 - 1 : ℕ) : ℝ) *
              (((k.1 - 1 : ℕ) : ℝ) + 1)))
      rw [hcast_pred]
      field_simp [ne_of_gt hk_pos, ne_of_gt hkm1_pos, ne_of_gt hk1_pos]
      ring
  · let hdenom :
        monotonicityQuotientDenominators fixedHorizonGammaWeight
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)) := by
      intro k
      have hGamma_pos : 0 < fixedHorizonGammaWeight k := by
        unfold fixedHorizonGammaWeight
        have hk_pos : 0 < (k.1 : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one k.2)
        have hk1_pos : 0 < (k.1 : ℝ) + 1 := by positivity
        exact div_pos (by norm_num) (mul_pos hk_pos hk1_pos)
      have hgap :
          0 < 1 - psWeightProduct spsP
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k) :=
        one_sub_psWeightProduct_spsP_pos_of_pos
          ((fixedHorizonInnerBudgetSource S N Dtilde hDtilde k).2)
      exact mul_ne_zero (ne_of_gt hGamma_pos) (ne_of_gt hgap)
    refine ⟨hdenom, ?_⟩
    intro k hk
    rw [fixed_horizon_forward_quotient_eq (S := S)
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
        hdenom k,
      fixed_horizon_forward_quotient_eq (S := S)
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))
        hdenom (predTime k hk)]
    -- Remaining scalar obligation: Eq. (8.1.33) for the fixed-horizon
    -- ceiling budget, using monotonicity of Eq. (8.1.72) and
    -- `psWeightProduct_spsP_eq`.
    have hTmono :
        innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) (predTime k hk) ≤
          innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k :=
      fixed_horizon_inner_budget_mono_pred (S := S) N Dtilde hDtilde k hk
    have hPmono :
        psWeightProduct spsP
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k) ≤
          psWeightProduct spsP
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)
              (predTime k hk)) := by
      exact sps_product_antitone_on_positive_budgets
        ((fixedHorizonInnerBudgetSource S N Dtilde hDtilde (predTime k hk)).2)
        hTmono
    have hden_pred_pos :
        0 < 1 - psWeightProduct spsP
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)
            (predTime k hk)) :=
      one_sub_psWeightProduct_spsP_pos_of_pos
        ((fixedHorizonInnerBudgetSource S N Dtilde hDtilde (predTime k hk)).2)
    have hden_le :
        1 - psWeightProduct spsP
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)
              (predTime k hk)) ≤
          1 - psWeightProduct spsP
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k) := by
      linarith
    exact div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt S.L_pos))
      hden_pred_pos hden_le

/-- Shifted square sum used in the fixed-horizon probability-scale SPS
coefficient bound. -/
theorem sum_range_shift_two_sq_eq (T : ℕ) :
    (Finset.range T).sum (fun i => ((i : ℝ) + 2) ^ 2) =
      (T : ℝ) * ((T : ℝ) - 1) * (2 * (T : ℝ) - 1) / 6 +
        2 * (T : ℝ) * ((T : ℝ) - 1) + 4 * (T : ℝ) := by
  induction T with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      ring

/-- SPS square-coefficient inner sum for the square-root part of Lan
Eq. (8.1.68).

Candidate audit: considered `sps_normalized_weight_eq`,
`sps_normalized_weight_sum_eq_one`, `sps_step_weight_inv_eq`,
`sum_sq_le_card_mul_max_sq`, and Mathlib range-sum APIs.  The normalized-weight
helpers expose the coefficient, but the reusable max-square estimate is too
weak for the displayed `4/sqrt(3)` constant, so this proves the exact shifted
square-sum inequality. -/
theorem sps_probability_square_inner_sum_le (T : ℕ) (hT : 0 < T) :
    (Finset.range T).sum (fun i =>
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) ^ 2) ≤
      8 / (3 * (T : ℝ)) := by
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hT3_pos : 0 < (T : ℝ) + 3 := by positivity
  have hT3_ne : (T : ℝ) + 3 ≠ 0 := ne_of_gt hT3_pos
  have hden_pos : 0 < (3 : ℝ) * (T : ℝ) := by positivity
  have hmain :
      (4 / (((T : ℝ) ^ 2 * ((T : ℝ) + 3) ^ 2)) *
          ((Finset.range T).sum (fun i => ((i : ℝ) + 2) ^ 2))) ≤
        8 / (3 * (T : ℝ)) := by
    rw [sum_range_shift_two_sq_eq]
    rw [le_div_iff₀ hden_pos]
    field_simp [hT_ne, hT3_ne]
    nlinarith [sq_nonneg (T : ℝ)]
  calc
    (Finset.range T).sum (fun i =>
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) ^ 2)
        =
      (Finset.range T).sum (fun i =>
        (4 / (((T : ℝ) ^ 2 * ((T : ℝ) + 3) ^ 2)) *
          ((i : ℝ) + 2) ^ 2)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          field_simp [hT_ne, hT3_ne]
          ring
    _ =
      (4 / (((T : ℝ) ^ 2 * ((T : ℝ) + 3) ^ 2)) *
        (Finset.range T).sum (fun i => ((i : ℝ) + 2) ^ 2)) := by
          rw [Finset.mul_sum]
    _ ≤ 8 / (3 * (T : ℝ)) := hmain

/-- Fixed-horizon schedule coefficient in the stochastic summand of
Lan Eq. (8.1.78).

Candidate audit: considered `fixed_horizon_forward_quotient_eq`,
`fixedHorizonBeta`, `fixedHorizonGamma`, `fixedHorizonGammaWeight`, and
SOptLib telescope/output-weight helpers.  The quotient helper has the
neighboring monotonicity coefficient, but this exact stochastic coefficient
is the literal fixed-horizon schedule algebra used in Eq. (8.1.78). -/
theorem fixed_horizon_stochastic_schedule_coeff_eq (κ : PositiveTime) :
    fixedHorizonGamma κ / (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ) =
      (κ.1 : ℝ) ^ 2 / (2 * S.lSmooth) := by
  unfold fixedHorizonGamma fixedHorizonBeta fixedHorizonGammaWeight
  have hk_pos : 0 < (κ.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
  have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
  have hL_pos : 0 < S.lSmooth := S.L_pos
  field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos, ne_of_gt hL_pos]

/-- Pointwise fixed-horizon martingale square coefficient normalization in
Lan Eq. (8.1.68).

Candidate audit: considered `sps_normalized_weight_eq`,
`sps_product_ratio_eq`, `fixed_horizon_stochastic_schedule_coeff_eq`, and
SOptLib square-sum helpers.  The SPS helper gives the normalized inner
`P_T/((1-P_T)p_iP_{i-1})` factor, but the high-probability scale additionally
requires the fixed-horizon outer ratio `γ_k/Γ_k = k`, recorded here. -/
theorem fixed_horizon_probability_square_coeff_eq
    {T : ℕ} (hT : 0 < T) (κ : PositiveTime) (i : ℕ) :
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
    fixedHorizonGamma κ * psWeightProduct spsP T /
        (fixedHorizonGammaWeight κ * (1 - psWeightProduct spsP T) *
          spsP ι * psWeightProduct spsP i) =
      (κ.1 : ℝ) *
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) := by
  intro ι
  have hnorm := sps_normalized_weight_eq T i hT
  have hk_pos : 0 < (κ.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
  have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
  have hGamma_ne : fixedHorizonGammaWeight κ ≠ 0 := by
    unfold fixedHorizonGammaWeight
    exact div_ne_zero (by norm_num) (mul_ne_zero (ne_of_gt hk_pos) (ne_of_gt hk1_pos))
  have hgap_ne : 1 - psWeightProduct spsP T ≠ 0 :=
    ne_of_gt (one_sub_psWeightProduct_spsP_pos_of_pos hT)
  have hsps_ne : spsP ι ≠ 0 := by
    unfold spsP
    positivity
  have hprev_ne : psWeightProduct spsP i ≠ 0 := by
    rw [psWeightProduct_spsP_eq i]
    positivity
  calc
    fixedHorizonGamma κ * psWeightProduct spsP T /
        (fixedHorizonGammaWeight κ * (1 - psWeightProduct spsP T) *
          spsP ι * psWeightProduct spsP i)
        =
      (fixedHorizonGamma κ / fixedHorizonGammaWeight κ) *
        (psWeightProduct spsP T * (1 - psWeightProduct spsP T)⁻¹ *
          (spsP ι * psWeightProduct spsP i)⁻¹) := by
          field_simp [hGamma_ne, hgap_ne, hsps_ne, hprev_ne]
    _ =
      (fixedHorizonGamma κ / fixedHorizonGammaWeight κ) *
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) := by
          rw [hnorm]
    _ =
      (κ.1 : ℝ) *
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) := by
          unfold fixedHorizonGamma fixedHorizonGammaWeight
          field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos]

/-- Pointwise fixed-horizon stochastic summand normalization in
Lan Eq. (8.1.78).

Candidate audit: considered `sps_product_ratio_eq`,
`fixed_horizon_stochastic_schedule_coeff_eq`,
`sps_inner_weight_sum_le_four_budget`, and SOptLib finite-sum helpers.  The
first two are exactly the source ratios, while no existing lemma combines them
with the squared SPS denominator for a single Eq. (8.1.78) summand. -/
theorem fixed_horizon_stochastic_summand_eq_of_pos
    {T : ℕ} (hT : 0 < T) (κ : PositiveTime) (i : ℕ) :
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
    (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
        psWeightProduct spsP T /
      (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
        (1 - psWeightProduct spsP T) * spsP ι ^ 2 *
          psWeightProduct spsP i) =
    ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) ^ 2 /
        (S.lSmooth * ((T : ℝ) * ((T : ℝ) + 3)))) *
      ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
  intro ι
  have hb : fixedHorizonBeta S κ ≠ 0 :=
    ne_of_gt (fixedHorizonBeta_pos S κ)
  have hG : fixedHorizonGammaWeight κ ≠ 0 := by
    unfold fixedHorizonGammaWeight
    have hk_pos : 0 < (κ.1 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
    have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
    exact ne_of_gt (div_pos (by norm_num) (mul_pos hk_pos hk1_pos))
  have hgap : 1 - psWeightProduct spsP T ≠ 0 :=
    ne_of_gt (one_sub_psWeightProduct_spsP_pos_of_pos hT)
  have hsps_pos : 0 < spsP ι := by
    unfold spsP
    positivity
  have hPi_pos : 0 < psWeightProduct spsP i := by
    rw [psWeightProduct_spsP_eq i]
    positivity
  have hQ : spsP ι ^ 2 * psWeightProduct spsP i ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (ne_of_gt hsps_pos)) (ne_of_gt hPi_pos)
  calc
    (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
        psWeightProduct spsP T /
      (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
        (1 - psWeightProduct spsP T) * spsP ι ^ 2 *
          psWeightProduct spsP i)
        =
      (S.mGrowth ^ 2 + S.sigmaSq) *
        (fixedHorizonGamma κ /
          (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ)) *
        (psWeightProduct spsP T / (1 - psWeightProduct spsP T)) *
        (spsP ι ^ 2 * psWeightProduct spsP i)⁻¹ := by
          simpa [mul_assoc] using
            (stochastic_summand_fraction_split
              (A := S.mGrowth ^ 2 + S.sigmaSq)
              (gamma := fixedHorizonGamma κ)
              (P := psWeightProduct spsP T)
              (beta := fixedHorizonBeta S κ)
              (Gamma := fixedHorizonGammaWeight κ)
              (gap := 1 - psWeightProduct spsP T)
              (Q := spsP ι ^ 2 * psWeightProduct spsP i)
              hb hG hgap hQ)
    _ =
      ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) ^ 2 /
        (S.lSmooth * ((T : ℝ) * ((T : ℝ) + 3)))) *
      ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
        rw [fixed_horizon_stochastic_schedule_coeff_eq (S := S) κ,
          sps_product_ratio_eq (T := T) hT]
        have hL : S.lSmooth ≠ 0 := ne_of_gt S.L_pos
        have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
        have hT3 : (T : ℝ) + 3 ≠ 0 := by positivity
        field_simp [hL, hT0, hT3]

/-- Per-outer-iteration stochastic inner-sum bound in Lan Eq. (8.1.78).

Candidate audit: considered `sps_product_ratio_eq`,
`sps_inner_weight_sum_le_four_budget`,
`fixed_horizon_stochastic_summand_eq_of_pos`, and SOptLib finite-sum/telescope
helpers.  The target-file SPS helpers provide the needed source ratios and
finite inner-weight estimate, while no imported theorem packages the
fixed-horizon Eq. (8.1.78) per-`κ` stochastic sum. -/
theorem fixed_horizon_stochastic_inner_sum_le
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (κ : PositiveTime) :
    (Finset.range
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
      (fun i =>
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
        (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
          (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
            (1 - psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i)) ≤
      (4 / S.lSmooth) *
        ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) ^ 2 /
          ((innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ : ℝ) + 3)) := by
  classical
  let Tκ : ℕ := innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
  let C : ℝ :=
    (S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) ^ 2 /
      (S.lSmooth * ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))
  have hTκ : 0 < Tκ :=
    (fixedHorizonInnerBudgetSource S N Dtilde hDtilde κ).2
  have hA_nonneg : 0 ≤ S.mGrowth ^ 2 + S.sigmaSq := by
    nlinarith [sq_nonneg S.mGrowth, S.sigmaSq_nonneg]
  have hTκ_real_pos : 0 < (Tκ : ℝ) := by exact_mod_cast hTκ
  have hTκ3_pos : 0 < (Tκ : ℝ) + 3 := by positivity
  have hden_pos : 0 < S.lSmooth * ((Tκ : ℝ) * ((Tκ : ℝ) + 3)) :=
    mul_pos S.L_pos (mul_pos hTκ_real_pos hTκ3_pos)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (mul_nonneg hA_nonneg (sq_nonneg (κ.1 : ℝ)))
      (le_of_lt hden_pos)
  have hweights := sps_inner_weight_sum_le_four_budget Tκ
  have hmul :
      C *
          (Finset.range Tκ).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
              psWeightProduct spsP i)⁻¹) ≤
        C * (4 * (Tκ : ℝ)) :=
    mul_le_mul_of_nonneg_left hweights hC_nonneg
  calc
    (Finset.range
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
      (fun i =>
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
        (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
          (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
            (1 - psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i))
        =
      (Finset.range Tκ).sum (fun i =>
        C * ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
          psWeightProduct spsP i)⁻¹) := by
          refine Finset.sum_congr ?_ ?_
          · simp [Tκ]
          · intro i _hi
            simpa [Tκ, C] using
              (fixed_horizon_stochastic_summand_eq_of_pos (S := S)
                (T := Tκ) hTκ κ i)
    _ =
      C * (Finset.range Tκ).sum (fun i =>
        ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
          psWeightProduct spsP i)⁻¹) := by
          rw [Finset.mul_sum]
    _ ≤ C * (4 * (Tκ : ℝ)) := hmul
    _ =
      (4 / S.lSmooth) *
        ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) ^ 2 /
          ((innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ : ℝ) + 3)) := by
          have hTinner_pos :
              0 <
                (innerBudgetNat
                  (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ : ℝ) := by
            simpa [Tκ] using hTκ_real_pos
          have hTinner3_pos :
              0 <
                (innerBudgetNat
                  (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ : ℝ) + 3 := by
            simpa [Tκ] using hTκ3_pos
          dsimp [C, Tκ]
          field_simp [ne_of_gt S.L_pos, ne_of_gt hTinner_pos, ne_of_gt hTinner3_pos]

/-- Initial fixed-horizon SPS gap reciprocal bound used in Lan Eq. (8.1.78).

Candidate audit: considered `psWeightProduct_spsP_eq`,
`one_sub_psWeightProduct_spsP_pos_of_pos`, `sps_product_ratio_eq`, and SOptLib
telescope/output-weight helpers.  The existing facts give the closed form,
positivity, or the stochastic ratio, but not the initial-term reciprocal
estimate `P_T ≤ 1/3`, so this proof specializes the closed form for `T ≥ 1`. -/
theorem sps_initial_gap_inv_le_three_halves {T : ℕ} (hT : 0 < T) :
    (1 - psWeightProduct spsP T)⁻¹ ≤ (3 / 2 : ℝ) := by
  rw [psWeightProduct_spsP_eq T]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hTreal_ge_one : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hden_pos : 0 < (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by positivity
  have hden_ge_six : (6 : ℝ) ≤ ((T : ℝ) + 1) * ((T : ℝ) + 2) := by
    nlinarith
  have hgap_ge :
      (2 / 3 : ℝ) ≤
        1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by
    rw [le_sub_iff_add_le]
    field_simp [ne_of_gt hden_pos]
    nlinarith
  have hgap_pos : 0 < 1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by
    nlinarith [hgap_ge]
  have hmain :
      (1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)))⁻¹ ≤
        ((2 / 3 : ℝ))⁻¹ := by
    exact (inv_le_inv₀ hgap_pos (by norm_num : (0 : ℝ) < 2 / 3)).2 hgap_ge
  norm_num at hmain
  exact hmain

/-- Fixed-horizon initial Bregman contribution in Lan Eq. (8.1.78).

Aligns with the first line of Eq. (8.1.78).  Candidate audit: considered
`theorem82ExpectedBound_checked_eq_formulaExtension`,
`genericExpectedBound_formulaExtension`, `psWeightProduct_spsP_eq`,
`sps_initial_gap_inv_le_three_halves`, and the SOptLib Bregman nonnegativity
helpers.  The generic formula exposes the term, while this paper-local helper
combines the fixed schedules, positive ceiling budget, and feasible Bregman
lower bound to get the displayed `3V` contribution. -/
theorem fixed_horizon_initial_bregman_term_le
    (x0 xStar : FeasiblePoint S) (N : PositiveTime) (Dtilde : ℝ)
    (hDtilde : 0 < Dtilde) :
    fixedHorizonGammaWeight N * fixedHorizonBeta S oneTime *
        (1 - psWeightProduct spsP
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) oneTime))⁻¹ *
        bregmanFormulaOnX S x0 xStar ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (3 * bregmanFormulaOnX S x0 xStar) := by
  let T1 : ℕ :=
    innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) oneTime
  let V : ℝ := bregmanFormulaOnX S x0 xStar
  have hT1_pos : 0 < T1 := by
    exact (fixedHorizonInnerBudgetSource S N Dtilde hDtilde oneTime).2
  have hV_nonneg : 0 ≤ V := by
    have hlower := bregmanFormulaOnX_lower_bound_from_prox_geometry S x0 xStar
    have hsq : 0 ≤ (1 / 2 : ℝ) * S.primalNorm (xStar.1 - x0.1) ^ 2 := by
      positivity
    dsimp [V]
    linarith
  have hInv :
      (1 - psWeightProduct spsP T1)⁻¹ ≤ (3 / 2 : ℝ) :=
    sps_initial_gap_inv_le_three_halves hT1_pos
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
  have hden_pos : 0 < (N.1 : ℝ) * ((N.1 : ℝ) + 1) :=
    mul_pos hN_pos hN1_pos
  have hscale_nonneg :
      0 ≤ (2 / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (2 * S.lSmooth) * V) := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg (by norm_num) (le_of_lt hden_pos))
        (mul_nonneg (by norm_num) (le_of_lt S.L_pos)))
      hV_nonneg
  have hmul :
      (2 / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (2 * S.lSmooth) * V) *
          (1 - psWeightProduct spsP T1)⁻¹ ≤
        (2 / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (2 * S.lSmooth) * V) *
          (3 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hInv hscale_nonneg
  calc
    fixedHorizonGammaWeight N * fixedHorizonBeta S oneTime *
        (1 - psWeightProduct spsP
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) oneTime))⁻¹ *
        bregmanFormulaOnX S x0 xStar
        = (2 / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (2 * S.lSmooth) * V) *
            (1 - psWeightProduct spsP T1)⁻¹ := by
          simp [fixedHorizonGammaWeight, fixedHorizonBeta, oneTime, T1, V]
          ring
    _ ≤ (2 / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (2 * S.lSmooth) * V) *
          (3 / 2 : ℝ) := hmul
    _ = (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) * (3 * V) := by
          ring
    _ = (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (3 * bregmanFormulaOnX S x0 xStar) := by
          dsimp [V]

/-- Fixed-horizon ceiling-budget ratio from Lan Eq. (8.1.72).

Aligns with the stochastic-term simplification in Eq. (8.1.78).  Candidate
audit: considered `fixedHorizonInnerBudgetReal`, `fixedHorizonInnerBudget`,
`fixedHorizonInnerBudget_pos`, `Nat.le_ceil`, and SOptLib budget/telescope
helpers.  The existing facts define and prove positivity of the ceiling budget,
but none state the ordered-field ratio obtained by inverting the Eq. (8.1.72)
lower bound, so this helper proves that scalar bridge directly. -/
theorem fixed_horizon_budget_ratio_le
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) (k : PositiveTime) :
    (S.mGrowth ^ 2 + S.sigmaSq) * (k.1 : ℝ) ^ 2 /
        ((innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k : ℝ) + 3) ≤
      Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ) := by
  let T : ℕ := innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k
  let A : ℝ := S.mGrowth ^ 2 + S.sigmaSq
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
  have hT3_pos : 0 < (T : ℝ) + 3 := by positivity
  have hDL2_pos : 0 < Dtilde * S.lSmooth ^ 2 :=
    mul_pos hDtilde (sq_pos_of_ne_zero (ne_of_gt S.L_pos))
  have hceil :
      fixedHorizonInnerBudgetReal S N.1 Dtilde k ≤ (T : ℝ) := by
    change fixedHorizonInnerBudgetReal S N.1 Dtilde k ≤
      (fixedHorizonInnerBudget S N.1 Dtilde k : ℝ)
    unfold fixedHorizonInnerBudget
    exact Nat.le_ceil _
  have hceil3 :
      fixedHorizonInnerBudgetReal S N.1 Dtilde k ≤ (T : ℝ) + 3 := by
    linarith
  have hmul :
      (N.1 : ℝ) * A * (k.1 : ℝ) ^ 2 ≤ ((T : ℝ) + 3) * (Dtilde * S.lSmooth ^ 2) := by
    have h := hceil3
    unfold fixedHorizonInnerBudgetReal at h
    rw [div_le_iff₀ hDL2_pos] at h
    nlinarith
  field_simp [ne_of_gt hT3_pos, ne_of_gt hN_pos]
  nlinarith

/-- Sharper fixed-horizon ceiling-budget ratio without the harmless `+3`.

This is the scalar budget bridge needed for the square-root part of Lan
Eq. (8.1.68).  Candidate audit: considered `fixed_horizon_budget_ratio_le`,
`fixedHorizonInnerBudgetReal`, `fixedHorizonInnerBudget`, `Nat.le_ceil`, and
SOptLib budget/telescope helpers.  The existing ratio helper intentionally
targets the stochastic Eq. (8.1.78) denominator `(T_k+3)`, while the probability
square-sum route needs the direct ceiling consequence with denominator `T_k`. -/
theorem fixed_horizon_budget_ratio_without_three_le
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) (k : PositiveTime) :
    (S.mGrowth ^ 2 + S.sigmaSq) * (k.1 : ℝ) ^ 2 /
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k : ℝ) ≤
      Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ) := by
  let T : ℕ := innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) k
  let A : ℝ := S.mGrowth ^ 2 + S.sigmaSq
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hT_pos_nat : 0 < T :=
    (fixedHorizonInnerBudgetSource S N Dtilde hDtilde k).2
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast hT_pos_nat
  have hDL2_pos : 0 < Dtilde * S.lSmooth ^ 2 :=
    mul_pos hDtilde (sq_pos_of_ne_zero (ne_of_gt S.L_pos))
  have hceil :
      fixedHorizonInnerBudgetReal S N.1 Dtilde k ≤ (T : ℝ) := by
    change fixedHorizonInnerBudgetReal S N.1 Dtilde k ≤
      (fixedHorizonInnerBudget S N.1 Dtilde k : ℝ)
    unfold fixedHorizonInnerBudget
    exact Nat.le_ceil _
  have hmul :
      (N.1 : ℝ) * A * (k.1 : ℝ) ^ 2 ≤ (T : ℝ) * (Dtilde * S.lSmooth ^ 2) := by
    have h := hceil
    unfold fixedHorizonInnerBudgetReal at h
    rw [div_le_iff₀ hDL2_pos] at h
    nlinarith
  rw [div_le_div_iff₀ hT_pos hN_pos]
  nlinarith

/-- Outer aggregation of the fixed-horizon stochastic inner sums in
Lan Eq. (8.1.78).

Candidate audit: considered `fixed_horizon_stochastic_inner_sum_le`,
`fixed_horizon_budget_ratio_le`, `Finset.sum_le_sum`, and SOptLib finite-window
telescope helpers.  The first two local source-derived helpers give the exact
per-`κ` Eq. (8.1.78) and Eq. (8.1.72) ingredients; no SOptLib theorem packages
this fixed-horizon ceiling-budget aggregation. -/
theorem fixed_horizon_stochastic_outer_sum_le_four_Dtilde_L
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i))) ≤
      4 * Dtilde * S.lSmooth := by
  classical
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hscale_nonneg : 0 ≤ 4 / S.lSmooth := by
    exact div_nonneg (by norm_num) (le_of_lt S.L_pos)
  have hpoint : ∀ k ∈ Finset.range N.1,
      (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
       (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)) ≤
        4 * Dtilde * S.lSmooth / (N.1 : ℝ)) := by
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    have hinner :=
      fixed_horizon_stochastic_inner_sum_le (S := S) N Dtilde hDtilde κ
    have hbudget :=
      fixed_horizon_budget_ratio_le (S := S) N Dtilde hDtilde κ
    have hbudget_scaled :
        (4 / S.lSmooth) *
            ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) ^ 2 /
              ((innerBudgetNat
                (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ : ℝ) + 3)) ≤
          (4 / S.lSmooth) * (Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget hscale_nonneg
    calc
      (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i))
          ≤
        (4 / S.lSmooth) *
            ((S.mGrowth ^ 2 + S.sigmaSq) * (κ.1 : ℝ) ^ 2 /
              ((innerBudgetNat
                (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ : ℝ) + 3)) :=
          hinner
      _ ≤ (4 / S.lSmooth) * (Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ)) :=
          hbudget_scaled
      _ = 4 * Dtilde * S.lSmooth / (N.1 : ℝ) := by
          field_simp [ne_of_gt S.L_pos, ne_of_gt hN_pos]
  calc
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)))
        ≤ (Finset.range N.1).sum (fun _ => 4 * Dtilde * S.lSmooth / (N.1 : ℝ)) := by
          exact Finset.sum_le_sum hpoint
    _ = 4 * Dtilde * S.lSmooth := by
          simp [Finset.sum_const, nsmul_eq_mul]
          field_simp [ne_of_gt hN_pos]

/-- Linear `σ²` part of the fixed-horizon high-probability scale in
Lan Eq. (8.1.68), bounded by the Eq. (8.1.78) stochastic budget.

Aligns with Corollary 8.3 proof step 4.  Candidate audit: considered
`theorem82ProbabilityScale_checked_eq_formulaExtension`,
`fixed_horizon_stochastic_outer_sum_le_four_Dtilde_L`,
`fixed_horizon_stochastic_inner_sum_le`, and SOptLib finite-sum/tail helpers.
The checked/formula bridge exposes this summand, while the only matching
budget estimate is the local Eq. (8.1.78) stochastic helper with coefficient
`M² + σ²`; this lemma specializes it using `σ² ≤ M² + σ²`. -/
theorem fixed_horizon_probability_linear_outer_sum_le_four_Dtilde_L
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          S.sigmaSq * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i))) ≤
      4 * Dtilde * S.lSmooth := by
  classical
  have hsig_le_A : S.sigmaSq ≤ S.mGrowth ^ 2 + S.sigmaSq := by
    nlinarith [sq_nonneg S.mGrowth]
  have hpoint : ∀ k ∈ Finset.range N.1, ∀ i ∈
      Finset.range
        (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde)
          (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)),
      (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
       let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
       S.sigmaSq * fixedHorizonGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
          (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
            (1 - psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i)) ≤
        (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
         let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
         (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)) := by
    intro k _hk i _hi
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
    let Tκ : ℕ := innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
    let C : ℝ :=
      fixedHorizonGamma κ * psWeightProduct spsP Tκ /
        (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
          (1 - psWeightProduct spsP Tκ) * spsP ι ^ 2 *
            psWeightProduct spsP i)
    have hC_nonneg : 0 ≤ C := by
      have hgamma_pos : 0 < fixedHorizonGamma κ := by
        unfold fixedHorizonGamma
        positivity
      have hP_pos : 0 < psWeightProduct spsP Tκ := by
        rw [psWeightProduct_spsP_eq Tκ]
        positivity
      have hbeta_pos : 0 < fixedHorizonBeta S κ := fixedHorizonBeta_pos S κ
      have hGamma_pos : 0 < fixedHorizonGammaWeight κ := by
        unfold fixedHorizonGammaWeight
        positivity
      have hgap_pos : 0 < 1 - psWeightProduct spsP Tκ :=
        one_sub_psWeightProduct_spsP_pos_of_pos
          ((fixedHorizonInnerBudgetSource S N Dtilde hDtilde κ).2)
      have hsps_pos : 0 < spsP ι := by
        unfold spsP
        positivity
      have hprev_pos : 0 < psWeightProduct spsP i := by
        rw [psWeightProduct_spsP_eq i]
        positivity
      dsimp [C]
      exact div_nonneg
        (mul_nonneg (le_of_lt hgamma_pos) (le_of_lt hP_pos))
        (le_of_lt
          (mul_pos
            (mul_pos (mul_pos (mul_pos hbeta_pos hGamma_pos) hgap_pos)
              (pow_pos hsps_pos 2))
            hprev_pos))
    calc
      (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
       let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
       S.sigmaSq * fixedHorizonGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
          (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
            (1 - psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i))
          = S.sigmaSq * C := by
            dsimp [κ, ι, Tκ, C]
            ring
      _ ≤ (S.mGrowth ^ 2 + S.sigmaSq) * C :=
            mul_le_mul_of_nonneg_right hsig_le_A hC_nonneg
      _ =
        (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
         let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
         (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)) := by
            dsimp [κ, ι, Tκ, C]
            ring
  calc
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          S.sigmaSq * fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)))
        ≤
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            (S.mGrowth ^ 2 + S.sigmaSq) * fixedHorizonGamma κ *
                psWeightProduct spsP
                  (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
              (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i))) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          refine Finset.sum_le_sum ?_
          intro i hi
          exact hpoint k hk i hi
    _ ≤ 4 * Dtilde * S.lSmooth :=
          fixed_horizon_stochastic_outer_sum_le_four_Dtilde_L (S := S)
            N Dtilde hDtilde

/-- Square-sum budget for the fixed-horizon high-probability scale.

This is the source-derived scalar heart of Corollary 8.3 proof step 4 for the
linear martingale scale in Lan Eq. (8.1.68).  Candidate audit: considered
`sps_probability_square_inner_sum_le`,
`fixed_horizon_budget_ratio_without_three_le`,
`fixed_horizon_stochastic_outer_sum_le_four_Dtilde_L`, and SOptLib square-sum
helpers.  The stochastic outer helper controls the `σ²` linear summand, not the
squared martingale coefficients; the exact SPS square helper plus the sharp
ceiling-budget ratio are needed for the displayed `4/sqrt(3)` term. -/
theorem fixed_horizon_probability_square_outer_sum_le
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    S.sigmaSq *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        let Tκ : ℕ :=
          innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
        (Finset.range Tκ).sum (fun i =>
          ((κ.1 : ℝ) *
            (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2)) ≤
      (8 / 3) * Dtilde * S.lSmooth ^ 2 := by
  classical
  let A : ℝ := S.mGrowth ^ 2 + S.sigmaSq
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg S.mGrowth, S.sigmaSq_nonneg]
  have hsig_le_A : S.sigmaSq ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg S.mGrowth]
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hpoint : ∀ k ∈ Finset.range N.1,
      S.sigmaSq *
        (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
         let Tκ : ℕ :=
          innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
         (Finset.range Tκ).sum (fun i =>
          ((κ.1 : ℝ) *
            (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2)) ≤
        (8 / 3) * Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ) := by
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    let Tκ : ℕ :=
      innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
    let row : ℝ :=
      (Finset.range Tκ).sum (fun i =>
        ((κ.1 : ℝ) *
          (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2)
    have hTκ_pos : 0 < Tκ :=
      (fixedHorizonInnerBudgetSource S N Dtilde hDtilde κ).2
    have hinner := sps_probability_square_inner_sum_le Tκ hTκ_pos
    have hrow_nonneg : 0 ≤ row := by
      dsimp [row]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    have hrow_le :
        row ≤ (κ.1 : ℝ) ^ 2 * (8 / (3 * (Tκ : ℝ))) := by
      calc
        row =
          (κ.1 : ℝ) ^ 2 *
            (Finset.range Tκ).sum (fun i =>
              (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3))) ^ 2) := by
            dsimp [row]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
        _ ≤ (κ.1 : ℝ) ^ 2 * (8 / (3 * (Tκ : ℝ))) :=
            mul_le_mul_of_nonneg_left hinner (sq_nonneg (κ.1 : ℝ))
    have hbudget :=
      fixed_horizon_budget_ratio_without_three_le (S := S)
        N Dtilde hDtilde κ
    have hscaled_A :
        A * row ≤ (8 / 3) * Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ) := by
      have hrow_scaled :
          A * row ≤ A * ((κ.1 : ℝ) ^ 2 * (8 / (3 * (Tκ : ℝ)))) :=
        mul_le_mul_of_nonneg_left hrow_le hA_nonneg
      have hbudget_scaled :
          A * ((κ.1 : ℝ) ^ 2 * (8 / (3 * (Tκ : ℝ)))) ≤
            (8 / 3) * Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ) := by
        have hcoef_nonneg : 0 ≤ (8 / 3 : ℝ) := by norm_num
        have hbudget_scaled' :=
          mul_le_mul_of_nonneg_left hbudget hcoef_nonneg
        calc
          A * ((κ.1 : ℝ) ^ 2 * (8 / (3 * (Tκ : ℝ))))
              = (8 / 3) *
                  (A * (κ.1 : ℝ) ^ 2 / (Tκ : ℝ)) := by
                have hTκ_ne : (Tκ : ℝ) ≠ 0 := by
                  exact_mod_cast (ne_of_gt hTκ_pos)
                field_simp [hTκ_ne]
          _ ≤ (8 / 3) * (Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ)) :=
                hbudget_scaled'
          _ = (8 / 3) * Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ) := by
                ring
      exact le_trans hrow_scaled hbudget_scaled
    calc
      S.sigmaSq *
        (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
         let Tκ : ℕ :=
          innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
         (Finset.range Tκ).sum (fun i =>
          ((κ.1 : ℝ) *
            (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2))
          = S.sigmaSq * row := by
            rfl
      _ ≤ A * row := mul_le_mul_of_nonneg_right hsig_le_A hrow_nonneg
      _ ≤ (8 / 3) * Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ) := hscaled_A
  calc
    S.sigmaSq *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        let Tκ : ℕ :=
          innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
        (Finset.range Tκ).sum (fun i =>
          ((κ.1 : ℝ) *
            (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2))
        =
      (Finset.range N.1).sum (fun k =>
        S.sigmaSq *
          (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
           let Tκ : ℕ :=
            innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
           (Finset.range Tκ).sum (fun i =>
            ((κ.1 : ℝ) *
              (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2))) := by
          rw [Finset.mul_sum]
    _ ≤ (Finset.range N.1).sum
        (fun _ => (8 / 3) * Dtilde * S.lSmooth ^ 2 / (N.1 : ℝ)) := by
          exact Finset.sum_le_sum hpoint
    _ = (8 / 3) * Dtilde * S.lSmooth ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
          field_simp [ne_of_gt hN_pos]

/-- Actual Theorem 8.2 probability-scale square sum under the fixed-horizon
schedules.

This consumes the pointwise coefficient normalization and the normalized square
budget above, giving the square-root branch a statement in the same summand
shape as `theorem82ProbabilityScale_checkedFormulaExtension`. -/
theorem fixed_horizon_probability_square_checked_sum_le
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    S.sigmaSq *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            (fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
              (fixedHorizonGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι * psWeightProduct spsP i)) ^ 2)) ≤
      (8 / 3) * Dtilde * S.lSmooth ^ 2 := by
  classical
  calc
    S.sigmaSq *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            (fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
              (fixedHorizonGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι * psWeightProduct spsP i)) ^ 2))
        =
      S.sigmaSq *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          let Tκ : ℕ :=
            innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
          (Finset.range Tκ).sum (fun i =>
            ((κ.1 : ℝ) *
              (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k _hk
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          let Tκ : ℕ :=
            innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ
          refine Finset.sum_congr ?_ ?_
          · simp [Tκ]
          · intro i _hi
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            have hTκ_pos : 0 < Tκ :=
              (fixedHorizonInnerBudgetSource S N Dtilde hDtilde κ).2
            have hcoeff :=
              fixed_horizon_probability_square_coeff_eq (T := Tκ) hTκ_pos κ i
            simpa [κ, Tκ] using congrArg (fun z : ℝ => z ^ 2) hcoeff
    _ ≤ (8 / 3) * Dtilde * S.lSmooth ^ 2 :=
          fixed_horizon_probability_square_outer_sum_le (S := S)
            N Dtilde hDtilde

/-- Scalar square-root normalization for the fixed-horizon probability scale.

Aligns with Lan Corollary 8.3 proof step 4 after Eq. (8.1.68).  Candidate
audit: considered target-file `fixed_horizon_probability_square_checked_sum_le`,
Mathlib `Real.sqrt_le_sqrt`, `Real.sq_sqrt`, `Real.sqrt_mul`, and SOptLib
square-root algebra hits; none packages this exact `8/3` to `4/sqrt 3`
normalization, so this helper isolates the pure ordered-real calculation. -/
theorem fixed_horizon_probability_sqrt_scalar_le
    {sigmaSq squareSum Vbar Dtilde L : ℝ}
    (hsigmaSq : 0 ≤ sigmaSq) (hsquareSum : 0 ≤ squareSum)
    (hVbar : 0 ≤ Vbar) (hDtilde : 0 < Dtilde) (hL : 0 < L)
    (hsquare :
      sigmaSq * squareSum ≤ (8 / 3) * Dtilde * L ^ 2) :
    Real.sqrt sigmaSq * Real.sqrt (2 * Vbar * squareSum) ≤
      4 * L * Real.sqrt (Dtilde * Vbar) / Real.sqrt 3 := by
  have htwoV_nonneg : 0 ≤ 2 * Vbar := by positivity
  have hsqrtArg_nonneg : 0 ≤ 2 * Vbar * squareSum :=
    mul_nonneg htwoV_nonneg hsquareSum
  have hDV_nonneg : 0 ≤ Dtilde * Vbar := mul_nonneg (le_of_lt hDtilde) hVbar
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hright_nonneg :
      0 ≤ 4 * L * Real.sqrt (Dtilde * Vbar) / Real.sqrt 3 := by
    positivity
  have hleft_nonneg :
      0 ≤ Real.sqrt sigmaSq * Real.sqrt (2 * Vbar * squareSum) := by
    positivity
  have hscaled :
      2 * Vbar * (sigmaSq * squareSum) ≤
        2 * Vbar * ((8 / 3) * Dtilde * L ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsquare htwoV_nonneg
  have hsq :
      (Real.sqrt sigmaSq * Real.sqrt (2 * Vbar * squareSum)) ^ 2 ≤
        (4 * L * Real.sqrt (Dtilde * Vbar) / Real.sqrt 3) ^ 2 := by
    calc
      (Real.sqrt sigmaSq * Real.sqrt (2 * Vbar * squareSum)) ^ 2
          = 2 * Vbar * (sigmaSq * squareSum) := by
            rw [mul_pow, Real.sq_sqrt hsigmaSq, Real.sq_sqrt hsqrtArg_nonneg]
            ring
      _ ≤ 2 * Vbar * ((8 / 3) * Dtilde * L ^ 2) := hscaled
      _ = (4 * L * Real.sqrt (Dtilde * Vbar) / Real.sqrt 3) ^ 2 := by
            rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hDV_nonneg,
              Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
            field_simp [ne_of_gt hsqrt3_pos]
            ring
  have habs := (sq_le_sq.mp hsq)
  rwa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] at habs

/-- Fixed-horizon public bound for the checked Theorem 8.2 probability scale.

Aligns with Lan Corollary 8.3 proof step 4 and Eq. (8.1.68).  Candidate audit:
considered the pre-searched `theorem82ProbabilityScale_checked_eq_formulaExtension`,
`fixed_horizon_probability_linear_outer_sum_le_four_Dtilde_L`,
`fixed_horizon_probability_square_checked_sum_le`,
`bregmanEnvelope_formulaExtension_nonneg`, and Mathlib square-root APIs.  These
are exactly the ingredients but no existing declaration assembles them into the
public fixed-horizon `B_p(N)` scale, so this helper records that assembly. -/
theorem fixed_horizon_probability_scale_checked_le_public
    (xStar : FeasiblePoint S) (hcompact : IsCompact S.X)
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (hdenom : theorem82DenominatorAdmissible (fixedHorizonBeta S)
      fixedHorizonGammaWeight
      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde))) :
    theorem82ProbabilityScale_checkedFormulaExtension S xStar hcompact N
        (fixedHorizonBeta S) fixedHorizonGamma fixedHorizonGammaWeight
        (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) hdenom ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (4 * Dtilde +
          (4 * Real.sqrt (Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) := by
  classical
  rw [theorem82ProbabilityScale_checked_eq_formulaExtension]
  unfold theorem82ProbabilityScale_formulaExtension genericProbabilityScale_formulaExtension
  let sqSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          (fixedHorizonGamma κ *
            psWeightProduct spsP
              (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
              spsP ι * psWeightProduct spsP i)) ^ 2))
  let linSum : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      (Finset.range
          (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
        (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          fixedHorizonGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
            (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
              (1 - psWeightProduct spsP
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)))
  have hGammaN_nonneg : 0 ≤ fixedHorizonGammaWeight N := by
    unfold fixedHorizonGammaWeight
    positivity
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hN1_pos : 0 < (N.1 : ℝ) + 1 := by positivity
  have hVbar_nonneg :
      0 ≤ bregmanEnvelope_formulaExtension S xStar hcompact :=
    bregmanEnvelope_formulaExtension_nonneg S xStar hcompact
  have hsqSum_nonneg : 0 ≤ sqSum := by
    dsimp [sqSum]
    exact Finset.sum_nonneg (fun k _hk =>
      Finset.sum_nonneg (fun i _hi => sq_nonneg _))
  have hsqBound :
      S.sigmaSq * sqSum ≤ (8 / 3) * Dtilde * S.lSmooth ^ 2 := by
    simpa [sqSum] using
      fixed_horizon_probability_square_checked_sum_le (S := S)
        N Dtilde hDtilde
  have hsqrt_core :
      sigma S *
          Real.sqrt
            (2 * bregmanEnvelope_formulaExtension S xStar hcompact * sqSum) ≤
        4 * S.lSmooth *
            Real.sqrt (Dtilde *
              bregmanEnvelope_formulaExtension S xStar hcompact) / Real.sqrt 3 := by
    simpa [sigma, mul_assoc] using
      fixed_horizon_probability_sqrt_scalar_le
        (sigmaSq := S.sigmaSq) (squareSum := sqSum)
        (Vbar := bregmanEnvelope_formulaExtension S xStar hcompact)
        (Dtilde := Dtilde) (L := S.lSmooth)
        S.sigmaSq_nonneg hsqSum_nonneg hVbar_nonneg hDtilde S.L_pos hsqBound
  have hsqrt :
      sigma S * fixedHorizonGammaWeight N *
          Real.sqrt
            (2 * bregmanEnvelope_formulaExtension S xStar hcompact * sqSum) ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          ((4 * Real.sqrt (Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) := by
    calc
      sigma S * fixedHorizonGammaWeight N *
          Real.sqrt
            (2 * bregmanEnvelope_formulaExtension S xStar hcompact * sqSum)
          = fixedHorizonGammaWeight N *
              (sigma S *
                Real.sqrt
                  (2 * bregmanEnvelope_formulaExtension S xStar hcompact * sqSum)) := by
            ring
      _ ≤ fixedHorizonGammaWeight N *
            (4 * S.lSmooth *
              Real.sqrt (Dtilde *
                bregmanEnvelope_formulaExtension S xStar hcompact) / Real.sqrt 3) :=
            mul_le_mul_of_nonneg_left hsqrt_core hGammaN_nonneg
      _ = (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          ((4 * Real.sqrt (Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) := by
            unfold fixedHorizonGammaWeight
            field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos]
  have hlinSum :
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range
            (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            S.sigmaSq * fixedHorizonGamma κ *
                psWeightProduct spsP
                  (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
              (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i))) ≤
        4 * Dtilde * S.lSmooth :=
    fixed_horizon_probability_linear_outer_sum_le_four_Dtilde_L (S := S)
      N Dtilde hDtilde
  have hlin :
      S.sigmaSq * fixedHorizonGammaWeight N * linSum ≤
        (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (4 * Dtilde) := by
    have hlin_rewrite :
        S.sigmaSq * linSum =
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
              (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                S.sigmaSq * fixedHorizonGamma κ *
                    psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
                  (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i))) := by
      dsimp [linSum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      ring
    calc
      S.sigmaSq * fixedHorizonGammaWeight N * linSum
          = fixedHorizonGammaWeight N * (S.sigmaSq * linSum) := by ring
      _ = fixedHorizonGammaWeight N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            (Finset.range
                (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)).sum
              (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                S.sigmaSq * fixedHorizonGamma κ *
                    psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ) /
                  (fixedHorizonBeta S κ * fixedHorizonGammaWeight κ *
                    (1 - psWeightProduct spsP
                      (innerBudgetNat (fixedHorizonInnerBudgetSource S N Dtilde hDtilde) κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i))) := by
            rw [hlin_rewrite]
      _ ≤ fixedHorizonGammaWeight N * (4 * Dtilde * S.lSmooth) :=
            mul_le_mul_of_nonneg_left hlinSum hGammaN_nonneg
      _ = (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
          (4 * Dtilde) := by
            unfold fixedHorizonGammaWeight
            field_simp [ne_of_gt hN_pos, ne_of_gt hN1_pos]
  change
    sigma S * fixedHorizonGammaWeight N *
          Real.sqrt
            (2 * bregmanEnvelope_formulaExtension S xStar hcompact * sqSum) +
        S.sigmaSq * fixedHorizonGammaWeight N * linSum ≤
      (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (4 * Dtilde +
          (4 * Real.sqrt (Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3)
  calc
    sigma S * fixedHorizonGammaWeight N *
          Real.sqrt
            (2 * bregmanEnvelope_formulaExtension S xStar hcompact * sqSum) +
        S.sigmaSq * fixedHorizonGammaWeight N * linSum
        ≤ (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
            ((4 * Real.sqrt (Dtilde *
              bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) +
          (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
            (4 * Dtilde) := add_le_add hsqrt hlin
    _ = (2 * S.lSmooth) / ((N.1 : ℝ) * ((N.1 : ℝ) + 1)) *
        (4 * Dtilde +
          (4 * Real.sqrt (Dtilde *
            bregmanEnvelope_formulaExtension S xStar hcompact)) / Real.sqrt 3) := by
          ring

/-- Pointwise compact-policy martingale square coefficient normalization in
Lan Corollary 8.3 proof step 7.

Aligns with the displayed identity before Eq. (8.1.77). Candidate audit:
considered the pre-searched `sps_probability_square_inner_sum_le`,
`sps_normalized_weight_eq`, `compact_stochastic_schedule_coeff_eq`, and SOptLib
finite-sum helpers.  The SPS helper supplies the inner normalized weight, but no
existing declaration combines it with the compact ratio `γ_k/Γ_k=k(k+1)/2`. -/
theorem compact_probability_square_coeff_eq
    {T : ℕ} (hT : 0 < T) (κ : PositiveTime) (i : ℕ) :
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
    compactGamma κ * psWeightProduct spsP T /
        (compactGammaWeight κ * (1 - psWeightProduct spsP T) *
          spsP ι * psWeightProduct spsP i) =
      (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1)) / 2) *
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) := by
  intro ι
  have hnorm := sps_normalized_weight_eq T i hT
  have hk_pos : 0 < (κ.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
  have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
  have hk2_pos : 0 < (κ.1 : ℝ) + 2 := by positivity
  have hGamma_ne : compactGammaWeight κ ≠ 0 := by
    unfold compactGammaWeight
    exact div_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero (ne_of_gt hk_pos) (ne_of_gt hk1_pos))
        (ne_of_gt hk2_pos))
  have hgap_ne : 1 - psWeightProduct spsP T ≠ 0 :=
    ne_of_gt (one_sub_psWeightProduct_spsP_pos_of_pos hT)
  have hsps_ne : spsP ι ≠ 0 := by
    unfold spsP
    positivity
  have hprev_ne : psWeightProduct spsP i ≠ 0 := by
    rw [psWeightProduct_spsP_eq i]
    positivity
  calc
    compactGamma κ * psWeightProduct spsP T /
        (compactGammaWeight κ * (1 - psWeightProduct spsP T) *
          spsP ι * psWeightProduct spsP i)
        =
      (compactGamma κ / compactGammaWeight κ) *
        (psWeightProduct spsP T * (1 - psWeightProduct spsP T)⁻¹ *
          (spsP ι * psWeightProduct spsP i)⁻¹) := by
          field_simp [hGamma_ne, hgap_ne, hsps_ne, hprev_ne]
    _ =
      (compactGamma κ / compactGammaWeight κ) *
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) := by
          rw [hnorm]
    _ =
      (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1)) / 2) *
        (2 * ((i : ℝ) + 2) / ((T : ℝ) * ((T : ℝ) + 3))) := by
          unfold compactGamma compactGammaWeight
          field_simp [ne_of_gt hk_pos, ne_of_gt hk1_pos, ne_of_gt hk2_pos]
          ring

/-- Compact-policy square-sum budget for the square-root part of Theorem 8.2(c).

Aligns with Corollary 8.3 proof step 7, where the source bounds the compact
square coefficients by the ceiling budget from Eq. (8.1.75). Candidate audit:
considered `sps_probability_square_inner_sum_le`,
`compact_probability_square_coeff_eq`, `compact_budget_ratio_le`, and SOptLib
finite-sum/telescope helpers.  These are exactly the source ingredients, but no
existing declaration aggregates this compact high-probability square branch. -/
theorem compact_probability_square_checked_sum_le
    (N : PositiveTime) (Dtilde : ℝ) (hDtilde : 0 < Dtilde) :
    S.sigmaSq *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            (compactGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
              (compactGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                spsP ι * psWeightProduct spsP i)) ^ 2)) ≤
      (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) ^ 2 := by
  classical
  let A : ℝ := S.mGrowth ^ 2 + S.sigmaSq
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg S.mGrowth, S.sigmaSq_nonneg]
  have hsig_le_A : S.sigmaSq ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg S.mGrowth]
  have hN_pos : 0 < (N.1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one N.2)
  have hpoint : ∀ k ∈ Finset.range N.1,
      S.sigmaSq *
        (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
         (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            (compactGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
              (compactGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                spsP ι * psWeightProduct spsP i)) ^ 2)) ≤
        (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) := by
    intro k hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    let Tκ : ℕ := innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ
    let row : ℝ :=
      (Finset.range Tκ).sum (fun i =>
        ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1)) / 2) *
          (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3)))) ^ 2)
    have hTκ_pos : 0 < Tκ :=
      (compactInnerBudgetSource S Dtilde hDtilde κ).2
    have hinner := sps_probability_square_inner_sum_le Tκ hTκ_pos
    have hkappa_le_N_nat : κ.1 ≤ N.1 := by
      dsimp [κ]
      exact Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hkappa_le_N : (κ.1 : ℝ) ≤ (N.1 : ℝ) := by
      exact_mod_cast hkappa_le_N_nat
    have hkappa_nonneg : 0 ≤ (κ.1 : ℝ) := by positivity
    have hrow_nonneg : 0 ≤ row := by
      dsimp [row]
      exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
    have hrow_le :
        row ≤
          ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) / 2) ^ 2 *
            (8 / (3 * (Tκ : ℝ))) := by
      calc
        row =
          ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) / 2) ^ 2 *
            (Finset.range Tκ).sum (fun i =>
              (2 * ((i : ℝ) + 2) / ((Tκ : ℝ) * ((Tκ : ℝ) + 3))) ^ 2) := by
            dsimp [row]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
        _ ≤ ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) / 2) ^ 2 *
              (8 / (3 * (Tκ : ℝ))) :=
            mul_le_mul_of_nonneg_left hinner (sq_nonneg _)
    have hbudget :=
      compact_budget_ratio_le (S := S) Dtilde hDtilde κ
    have hArow :
        A * row ≤ (2 / 3) * (κ.1 : ℝ) * (Dtilde * S.lSmooth ^ 2) := by
      have hrow_scaled :
          A * row ≤
            A * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) / 2) ^ 2 *
              (8 / (3 * (Tκ : ℝ)))) :=
        mul_le_mul_of_nonneg_left hrow_le hA_nonneg
      have hcoef_nonneg : 0 ≤ (2 / 3) * (κ.1 : ℝ) := by positivity
      have hbudget_scaled :=
        mul_le_mul_of_nonneg_left hbudget hcoef_nonneg
      calc
        A * row ≤
            A * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) / 2) ^ 2 *
              (8 / (3 * (Tκ : ℝ)))) := hrow_scaled
        _ =
            (2 / 3) * (κ.1 : ℝ) *
              (A * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / (Tκ : ℝ)) := by
              have hTκ_ne : (Tκ : ℝ) ≠ 0 := by
                exact_mod_cast (ne_of_gt hTκ_pos)
              field_simp [hTκ_ne]
              ring
        _ ≤ (2 / 3) * (κ.1 : ℝ) * (Dtilde * S.lSmooth ^ 2) :=
              hbudget_scaled
    have hsigrow :
        S.sigmaSq * row ≤ (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) := by
      have hsigrow_le : S.sigmaSq * row ≤ A * row :=
        mul_le_mul_of_nonneg_right hsig_le_A hrow_nonneg
      have hNscale :
          (2 / 3) * (κ.1 : ℝ) * (Dtilde * S.lSmooth ^ 2) ≤
            (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) := by
        have hcoef_nonneg : 0 ≤ (2 / 3) * (Dtilde * S.lSmooth ^ 2) := by
          positivity
        have hmul :=
          mul_le_mul_of_nonneg_left hkappa_le_N hcoef_nonneg
        nlinarith
      exact le_trans hsigrow_le (le_trans hArow hNscale)
    calc
      S.sigmaSq *
        (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
         (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            (compactGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
              (compactGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                spsP ι * psWeightProduct spsP i)) ^ 2))
          = S.sigmaSq * row := by
            dsimp [row, κ, Tκ]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _hi
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            have hcoeff :=
              compact_probability_square_coeff_eq (T := Tκ) hTκ_pos κ i
            simpa [κ, Tκ] using congrArg (fun z : ℝ => z ^ 2) hcoeff
      _ ≤ (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) := hsigrow
  calc
    S.sigmaSq *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        (Finset.range
          (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
          (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            (compactGamma κ *
              psWeightProduct spsP
                (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
              (compactGammaWeight κ *
                (1 - psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                spsP ι * psWeightProduct spsP i)) ^ 2))
        =
      (Finset.range N.1).sum (fun k =>
        S.sigmaSq *
          (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
           (Finset.range
            (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)).sum
            (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              (compactGamma κ *
                psWeightProduct spsP
                  (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ) /
                (compactGammaWeight κ *
                  (1 - psWeightProduct spsP
                    (innerBudgetNat (compactInnerBudgetSource S Dtilde hDtilde) κ)) *
                  spsP ι * psWeightProduct spsP i)) ^ 2))) := by
          rw [Finset.mul_sum]
    _ ≤ (Finset.range N.1).sum
        (fun _ => (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ)) := by
          exact Finset.sum_le_sum hpoint
    _ = (2 / 3) * Dtilde * S.lSmooth ^ 2 * (N.1 : ℝ) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring

/-- Sigma-only compact stochastic summand normalization for the linear
high-probability branch.

Aligns with Lan Corollary 8.3 proof step 7 and Eq. (8.1.52). Candidate audit:
considered `compact_stochastic_summand_eq_of_pos`,
`compact_stochastic_schedule_coeff_eq`, `stochastic_summand_fraction_split`,
and SOptLib finite-sum/telescope helpers. The expected helper normalizes the
same coefficient with `M²+σ²`; this theorem records the sigma-only instance
needed by `B_p(N)`. -/
theorem compact_probability_linear_summand_eq_of_pos
    (T : PositiveTime → ℕ) {κ : PositiveTime} (hTκ : 0 < T κ) (i : ℕ) :
    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
    compactGamma κ * psWeightProduct spsP (T κ) /
      (compactBeta S T κ * compactGammaWeight κ *
        (1 - psWeightProduct spsP (T κ)) *
          spsP ι ^ 2 * psWeightProduct spsP i) =
    (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) /
        (9 * S.lSmooth)) *
      (psWeightProduct spsP (T κ) *
        (1 - psWeightProduct spsP (T κ))⁻¹ *
          (1 - psWeightProduct spsP (T κ))⁻¹) *
      ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
  intro ι
  have hP_eq : explicitP (T κ) = psWeightProduct spsP (T κ) := by
    simpa [explicitP] using (psWeightProduct_spsP_eq (T κ)).symm
  have hgap_pos : 0 < 1 - psWeightProduct spsP (T κ) :=
    one_sub_psWeightProduct_spsP_pos_of_pos hTκ
  have hgap_ne : 1 - psWeightProduct spsP (T κ) ≠ 0 := ne_of_gt hgap_pos
  have hb : compactBeta S T κ ≠ 0 := by
    unfold compactBeta
    rw [hP_eq]
    have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
    exact ne_of_gt
      (div_pos (mul_pos (mul_pos (by norm_num) S.L_pos) hgap_pos)
        (mul_pos (by norm_num) hk1_pos))
  have hG : compactGammaWeight κ ≠ 0 := by
    unfold compactGammaWeight
    have hk_pos : 0 < (κ.1 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one κ.2)
    have hk1_pos : 0 < (κ.1 : ℝ) + 1 := by positivity
    have hk2_pos : 0 < (κ.1 : ℝ) + 2 := by positivity
    exact ne_of_gt (div_pos (by norm_num) (mul_pos (mul_pos hk_pos hk1_pos) hk2_pos))
  have hsps_pos : 0 < spsP ι := by
    unfold spsP
    positivity
  have hPi_pos : 0 < psWeightProduct spsP i := by
    rw [psWeightProduct_spsP_eq i]
    positivity
  have hQ : spsP ι ^ 2 * psWeightProduct spsP i ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (ne_of_gt hsps_pos)) (ne_of_gt hPi_pos)
  calc
    compactGamma κ * psWeightProduct spsP (T κ) /
      (compactBeta S T κ * compactGammaWeight κ *
        (1 - psWeightProduct spsP (T κ)) *
          spsP ι ^ 2 * psWeightProduct spsP i)
        =
      (compactGamma κ / (compactBeta S T κ * compactGammaWeight κ)) *
        (psWeightProduct spsP (T κ) / (1 - psWeightProduct spsP (T κ))) *
        (spsP ι ^ 2 * psWeightProduct spsP i)⁻¹ := by
          simpa [mul_assoc] using
            (stochastic_summand_fraction_split
              (A := (1 : ℝ))
              (gamma := compactGamma κ)
              (P := psWeightProduct spsP (T κ))
              (beta := compactBeta S T κ)
              (Gamma := compactGammaWeight κ)
              (gap := 1 - psWeightProduct spsP (T κ))
              (Q := spsP ι ^ 2 * psWeightProduct spsP i)
              hb hG hgap_ne hQ)
    _ =
      (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) /
          (9 * S.lSmooth)) *
        (psWeightProduct spsP (T κ) *
          (1 - psWeightProduct spsP (T κ))⁻¹ *
            (1 - psWeightProduct spsP (T κ))⁻¹) *
        ((spsP ι) ^ 2 * psWeightProduct spsP i)⁻¹ := by
        rw [compact_stochastic_schedule_coeff_eq (S := S) T hTκ]
        field_simp [ne_of_gt S.L_pos, hgap_ne]

/-- Exact squared-denominator split for the SPS linear probability row.

Aligns with Lan Corollary 8.3 proof step 7 after Eq. (8.1.52). Candidate
audit: considered `sps_step_weight_inv_eq`, `psWeightProduct_spsP_eq`,
`sps_inner_weight_sum_le_four_budget`, and SOptLib finite-sum helpers.  The
coarse sum helper only gives the expected-bound-style estimate; the compact
linear branch needs this literal summand split. -/
theorem sps_linear_squared_denominator_exact_split (i : ℕ) :
    ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 * psWeightProduct spsP i)⁻¹ =
      2 + 2 / ((i : ℝ) + 1) := by
  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
  have hstep := sps_step_weight_inv_eq i
  have hsps_pos : 0 < spsP ι := by
    dsimp [ι, spsP]
    positivity
  have hP_pos : 0 < psWeightProduct spsP i := by
    rw [psWeightProduct_spsP_eq i]
    positivity
  have hsps_ne : spsP ι ≠ 0 := ne_of_gt hsps_pos
  have hP_ne : psWeightProduct spsP i ≠ 0 := ne_of_gt hP_pos
  calc
    ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 * psWeightProduct spsP i)⁻¹
        = (spsP ι)⁻¹ * (spsP ι * psWeightProduct spsP i)⁻¹ := by
          dsimp [ι]
          field_simp [hsps_ne, hP_ne]
    _ = (spsP ι)⁻¹ * ((i : ℝ) + 2) := by
          rw [hstep]
    _ = 2 + 2 / ((i : ℝ) + 1) := by
          dsimp [ι, spsP]
          have h1 : (i : ℝ) + 1 ≠ 0 := by positivity
          field_simp [h1]
          norm_num
          ring

/-- Exact two-gap SPS factor for the compact linear probability row.

Aligns with Lan Corollary 8.3 proof step 7 using Eq. (8.1.44). Candidate
audit: considered `sps_product_gap_square_ratio_le_two_inv_sq`,
`psWeightProduct_spsP_eq`, `one_sub_psWeightProduct_spsP_pos_of_pos`, and
SOptLib telescope/output-weight helpers.  The existing ratio helper is an
upper bound; this branch needs the closed form before the aggregate correction
is isolated. -/
theorem sps_gap_square_factor_closed_form {T : ℕ} (hT : 0 < T) :
    psWeightProduct spsP T * (1 - psWeightProduct spsP T)⁻¹ *
        (1 - psWeightProduct spsP T)⁻¹ =
      2 * ((T : ℝ) + 1) * ((T : ℝ) + 2) /
        ((T : ℝ) ^ 2 * ((T : ℝ) + 3) ^ 2) := by
  rw [psWeightProduct_spsP_eq T]
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hTreal
  have hden_pos : 0 < (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by positivity
  have hden_ne : (((T : ℝ) + 1) * ((T : ℝ) + 2)) ≠ 0 := ne_of_gt hden_pos
  have hgap_pos :
      0 < 1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by
    have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    rw [sub_pos]
    exact (div_lt_one hden_pos).2 (by nlinarith [sq_nonneg (T : ℝ)])
  have hgap_ne : 1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) ≠ 0 :=
    ne_of_gt hgap_pos
  have hgap_eq :
      1 - 2 / (((T : ℝ) + 1) * ((T : ℝ) + 2)) =
        ((T : ℝ) * ((T : ℝ) + 3)) /
          (((T : ℝ) + 1) * ((T : ℝ) + 2)) := by
    field_simp [hden_ne]
    ring
  rw [hgap_eq]
  have hT3_ne : (T : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hden_ne, hT_ne, hT3_ne]

/-- Exact split of a compact linear SPS inner row into its constant and
reciprocal correction parts.

Aligns with Lan Corollary 8.3 proof step 7 after Eq. (8.1.52). Candidate
audit: considered `sps_linear_squared_denominator_exact_split`,
`sps_gap_square_factor_closed_form`, `sps_inner_weight_sum_le_four_budget`,
and SOptLib finite-sum helpers.  The first two are the exact source-aligned
ingredients; this helper packages their finite-row use and exposes the
reciprocal correction left for aggregate control. -/
theorem sps_linear_inner_row_exact_split {T : ℕ} (hT : 0 < T) :
    (Finset.range T).sum (fun i =>
      (psWeightProduct spsP T *
        (1 - psWeightProduct spsP T)⁻¹ *
          (1 - psWeightProduct spsP T)⁻¹) *
      ((spsP ⟨i + 1, Nat.succ_pos i⟩) ^ 2 *
        psWeightProduct spsP i)⁻¹) =
    (2 * ((T : ℝ) + 1) * ((T : ℝ) + 2) /
        ((T : ℝ) ^ 2 * ((T : ℝ) + 3) ^ 2)) *
      (Finset.range T).sum (fun i => 2 + 2 / ((i : ℝ) + 1)) := by
  rw [sps_gap_square_factor_closed_form hT]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [sps_linear_squared_denominator_exact_split i]

/-- Constant part of the exact compact linear SPS row is bounded by `4/9`.

Aligns with the main `2T_k` part of Lan Corollary 8.3 proof step 7 after
substituting the SPS row identity. Candidate audit: considered
`sps_inner_weight_sum_le_four_budget`, `sps_product_gap_square_ratio_le_two_inv_sq`,
and Mathlib ordered-field lemmas; the existing SPS bounds are too coarse for
the sharp split, so this proves the elementary rowwise scalar estimate. -/
theorem compact_linear_sps_main_row_le_four_ninth
    (c : ℝ) (κ : PositiveTime) {t : ℕ} (ht : 0 < t)
    (hbudget : c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 ≤ (t : ℝ)) :
    c * ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
          (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
            ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
          (Finset.range t).sum (fun _ => (2 : ℝ))) ≤
      4 / 9 := by
  let a : ℝ := (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2
  let coef : ℝ :=
    4 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
      (9 * (t : ℝ) * ((t : ℝ) + 3) ^ 2)
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hcoef_nonneg : 0 ≤ coef := by
    dsimp [coef]
    positivity
  have hbudget' : c * a ≤ (t : ℝ) := by
    simpa [a, mul_assoc] using hbudget
  have hmul : (c * a) * coef ≤ (t : ℝ) * coef :=
    mul_le_mul_of_nonneg_right hbudget' hcoef_nonneg
  have hcoef_bound : (t : ℝ) * coef ≤ 4 / 9 := by
    dsimp [coef]
    have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htR
    have ht3_ne : (t : ℝ) + 3 ≠ 0 := by positivity
    field_simp [ht_ne, ht3_ne]
    nlinarith [sq_nonneg ((t : ℝ) + 3)]
  calc
    c * ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
          (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
            ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
          (Finset.range t).sum (fun _ => (2 : ℝ)))
        = (c * a) * coef := by
          dsimp [a, coef]
          simp [Finset.sum_const, nsmul_eq_mul]
          field_simp [ne_of_gt htR]
          ring
    _ ≤ (t : ℝ) * coef := hmul
    _ ≤ 4 / 9 := hcoef_bound

/-- Compact inner-budget ratios sum to at most the number of outer steps.

Aligns with the ceiling-budget consequence used in Lan Corollary 8.3 proof
step 7 after Eq. (8.1.75). Candidate audit: considered target helper
`compact_budget_ratio_le`, SOptLib telescope/budget hits, and Mathlib
`Finset.sum_le_sum`/division lemmas.  The target helper is tied to the concrete
`Dtilde,L,M,σ` setup, while this local scalar route only has the abstract
`c * k(k+1)^2 ≤ T_k` hypothesis; the proof is the direct ratio consequence
summed over the compact grid. -/
theorem compact_linear_sps_ratio_sum_le_card
    (N : PositiveTime) (c : ℝ)
    (T : PositiveTime → ℕ) (hTpos : ∀ κ, 0 < T κ)
    (hbudget_scale : ∀ κ : PositiveTime,
      c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 ≤ (T κ : ℝ)) :
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)) ≤
      (N.1 : ℝ) := by
  classical
  have hpoint : ∀ k ∈ Finset.range N.1,
      (let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
       c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ)) ≤ 1 := by
    intro k _hk
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    have hTposR : 0 < (T κ : ℝ) := by exact_mod_cast hTpos κ
    have hbudget : c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) ≤ (T κ : ℝ) := by
      simpa [κ, mul_assoc] using hbudget_scale κ
    have hdiv :
        c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ) ≤ 1 := by
      exact (div_le_one hTposR).2 hbudget
    simpa [κ] using hdiv
  calc
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))
        ≤ (Finset.range N.1).sum (fun _ => (1 : ℝ)) := by
          exact Finset.sum_le_sum hpoint
    _ = (N.1 : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- One compact linear SPS row equals its normalized main-plus-reciprocal form.

Aligns with Lan Corollary 8.3 proof step 7 after the exact
`2 + 2/(i+1)` split. Candidate audit: considered
`sps_linear_inner_row_exact_split`, `compact_linear_sps_main_row_le_four_ninth`,
SOptLib finite-window/telescope helpers, and Mathlib field simplification
lemmas.  The split helper exposes the source row before factoring out the
common scalar budget ratio; this lemma is the route-local algebraic bridge. -/
theorem compact_linear_sps_combined_row_eq_normalized
    (c : ℝ) (κ : PositiveTime) {t : ℕ} (ht : 0 < t) :
    c *
        (((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
              (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
                ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
              ((t : ℝ) * 2)) +
            ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
              (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
                ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
              (Finset.range t).sum (fun i => 2 / ((i : ℝ) + 1)))) =
      (4 / 9) *
        ((c * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (t : ℝ)) *
          (((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2)) *
          (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (t : ℝ))) := by
  classical
  let a : ℝ := (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2
  let H : ℝ := (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htR
  have ht3_ne : (t : ℝ) + 3 ≠ 0 := by positivity
  have hsum_two :
      (Finset.range t).sum (fun i => 2 / ((i : ℝ) + 1)) = 2 * H := by
    dsimp [H]
    calc
      (Finset.range t).sum (fun i => 2 / ((i : ℝ) + 1))
          = (Finset.range t).sum (fun i => 2 * (1 / ((i : ℝ) + 1))) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
      _ = 2 * (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1)) := by
              rw [Finset.mul_sum]
  rw [hsum_two]
  dsimp [a, H]
  field_simp [ht_ne, ht3_ne]
  ring

/-- Sum-distributed form of `compact_linear_sps_combined_row_eq_normalized`.

Aligns with the same Lan Corollary 8.3 row normalization, but matches the
shape produced by `Finset.mul_sum` before summing over outer iterations. -/
theorem compact_linear_sps_combined_row_eq_normalized_sum_form
    (c : ℝ) (κ : PositiveTime) {t : ℕ} (ht : 0 < t) :
    c *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / 9 *
            (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
              ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
          ((t : ℝ) * 2))) +
      c *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / 9 *
            (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
              ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
          (Finset.range t).sum (fun i => 2 / ((i : ℝ) + 1)))) =
      (4 / 9) *
        ((c * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (t : ℝ)) *
          (((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2)) *
          (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (t : ℝ))) := by
  have hrow := compact_linear_sps_combined_row_eq_normalized c κ ht
  calc
    c *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / 9 *
            (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
              ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
          ((t : ℝ) * 2))) +
      c *
        (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 / 9 *
            (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
              ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
          (Finset.range t).sum (fun i => 2 / ((i : ℝ) + 1))))
        =
      c *
        (((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
              (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
                ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
              ((t : ℝ) * 2)) +
            ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / 9) *
              (2 * ((t : ℝ) + 1) * ((t : ℝ) + 2) /
                ((t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 2)) *
              (Finset.range t).sum (fun i => 2 / ((i : ℝ) + 1)))) := by
          ring
    _ =
      (4 / 9) *
        ((c * (((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (t : ℝ)) *
          (((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2)) *
          (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (t : ℝ))) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hrow

/-- Exact excess identity for the normalized compact linear SPS row.

Aligns with Lan Corollary 8.3 proof step 7 after the normalized row is split
against the budget ratio. Candidate audit: considered
`compact_linear_sps_combined_row_eq_normalized`,
`compact_linear_sps_combined_row_eq_normalized_sum_form`, and SOptLib
finite-sum/telescope helpers; those expose the row normalization or aggregate
telescopes, but not this literal ratio-excess algebraic form. -/
theorem compact_linear_sps_normalized_row_excess_identity
    (c : ℝ) (κ : PositiveTime) {t : ℕ} (ht : 0 < t) :
    ((c * ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (t : ℝ))) *
        (((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2)) *
        (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
          (t : ℝ))) -
      (c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (t : ℝ)) =
      (c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (t : ℝ)) *
        ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
          (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (t : ℝ)) -
          1) := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htR
  have ht3_ne : (t : ℝ) + 3 ≠ 0 := by positivity
  field_simp [ht_ne, ht3_ne]

/-- Expanded numerator for the normalized compact SPS excess factor.

Aligns with the algebraic simplification implicit in Lan Corollary 8.3 proof
step 7 after the normalized row is written as `ratio * q(T_k)`. Candidate
audit: considered `compact_linear_sps_normalized_row_excess_identity`,
target SPS row-normalization helpers, and Mathlib field simplification lemmas;
the existing helpers stop before this literal `q - 1` numerator form. -/
theorem compact_linear_sps_normalized_q_minus_one_eq {t : ℕ} (ht : 0 < t) :
    ((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
        (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
          (t : ℝ)) -
        1) =
      (((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) *
          ((t : ℝ) ^ 2 + 3 * (t : ℝ) + 2) -
        (3 * (t : ℝ) ^ 2 + 7 * (t : ℝ))) /
        ((t : ℝ) * ((t : ℝ) + 3) ^ 2) := by
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htR
  have ht3_ne : (t : ℝ) + 3 ≠ 0 := by positivity
  field_simp [ht_ne, ht3_ne]
  ring

/-- The normalized compact SPS row factor `q(t) / t` decreases across one
positive inner-budget step.

Aligns with Lan Corollary 8.3 proof step 7 when arbitrary admissible compact
budgets are compared to the tight common-budget scale. Candidate audit:
considered SOptLib/Mathlib monotonicity and telescope hits
`sum_range_sub_succ_le_first_of_last_nonneg`, `Finset.sum_range_sub'`, and the
local algebra helper `compact_linear_sps_normalized_q_minus_one_eq`; none states
this harmonic successor comparison, so the proof expands the literal SPS factor
and uses `Finset.sum_range_succ`. -/
theorem compact_linear_sps_normalized_q_over_t_antitone_succ
    {t : ℕ} (ht : 0 < t) :
    (((((t : ℝ) + 2) * ((t : ℝ) + 3) / ((t : ℝ) + 4) ^ 2) *
          (1 + ((Finset.range (t + 1)).sum (fun i => 1 / ((i : ℝ) + 1))) /
            ((t : ℝ) + 1))) /
        ((t : ℝ) + 1)) ≤
      (((((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2) *
          (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (t : ℝ))) /
        (t : ℝ)) := by
  classical
  let H : ℝ := (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    exact Finset.sum_nonneg (by intro i _hi; positivity)
  have hsum_nonneg :
      0 ≤ (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1)) := by
    simpa [H] using hH_nonneg
  have hsum_succ :
      (Finset.range (t + 1)).sum (fun i => 1 / ((i : ℝ) + 1)) =
        H + 1 / ((t : ℝ) + 1) := by
    dsimp [H]
    rw [Finset.sum_range_succ]
  have hsum_eq :
      (Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1)) = H := by
    rfl
  rw [hsum_succ, hsum_eq]
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htR
  have ht1_ne : (t : ℝ) + 1 ≠ 0 := by positivity
  have ht3_ne : (t : ℝ) + 3 ≠ 0 := by positivity
  have ht4_ne : (t : ℝ) + 4 ≠ 0 := by positivity
  field_simp [ht_ne, ht1_ne, ht3_ne, ht4_ne]
  have hdiff_nonneg :
      0 ≤
        ((t : ℝ) + 4) ^ 2 * ((t : ℝ) + 1) ^ 4 * ((t : ℝ) + H) -
          (t : ℝ) ^ 2 * ((t : ℝ) + 3) ^ 3 *
            (((t : ℝ) + 1) ^ 2 + (H * ((t : ℝ) + 1) + 1)) := by
    ring_nf
    positivity
  nlinarith [hH_nonneg, hsum_nonneg, sq_nonneg ((t : ℝ) + 3),
    sq_nonneg ((t : ℝ) + 4), hdiff_nonneg]

/-- Finite-step antitone form of the compact SPS normalized row factor.

Aligns with the same Corollary 8.3 scalar reduction as
`compact_linear_sps_normalized_q_over_t_antitone_succ`, iterating the successor
comparison across admissible positive inner budgets. Candidate audit:
searched SOptLib/Mathlib for finite monotone iteration and checked the local
successor helper above; existing telescope lemmas aggregate differences but do
not package this `q(t)/t` budget-factor antitonicity. -/
theorem compact_linear_sps_normalized_q_over_t_antitone
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    (((((n : ℝ) + 1) * ((n : ℝ) + 2) / ((n : ℝ) + 3) ^ 2) *
          (1 + ((Finset.range n).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (n : ℝ))) /
        (n : ℝ)) ≤
      (((((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 3) ^ 2) *
          (1 + ((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (m : ℝ))) /
        (m : ℝ)) := by
  let F : ℕ → ℝ := fun r =>
    if 0 < r then
      (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + ((Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (r : ℝ))) /
        (r : ℝ))
    else 1
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hanti : Antitone F := by
    refine antitone_nat_of_succ_le ?_
    intro r
    by_cases hr : 0 < r
    · have hsucc :=
        compact_linear_sps_normalized_q_over_t_antitone_succ (t := r) hr
      dsimp [F]
      simp [hr, Nat.succ_pos]
      convert hsucc using 1 <;> ring_nf
    · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
      subst r
      dsimp [F]
      norm_num
  have hmain : F n ≤ F m := hanti hmn
  simpa [F, hm, hn] using hmain

/-- Source-specialized antitonicity of the compact ceiling-grid `Q` factor.

This is a one-conjunct boundary fact for the retained-correction carry route:
adjacent realized buckets move to larger integer budgets, so the normalized
`Q` factor can only decrease. -/
theorem compact_ceiling_grid_Q_antitone
    (Q H : ℕ → ℝ)
    (hH_def : ∀ r, H r = (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1)))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    {r s : ℕ} (hr : 0 < r) (hrs : r ≤ s) :
    Q s ≤ Q r := by
  have hanti :=
    compact_linear_sps_normalized_q_over_t_antitone (m := r) (n := s) hr hrs
  simpa [hH_def r, hH_def s, hQ_def r, hQ_def s] using hanti

/-- Realized-successor version of `compact_ceiling_grid_Q_antitone`.

This is the boundary monotonicity component consumed by the endpoint carry
budget: every nonterminal realized high bucket has a strictly larger successor,
and all realized high buckets are source-backed by `hj_tail_high`. -/
theorem compact_ceiling_grid_high_tail_boundary_Q_next_le
    (N j : ℕ) (Q H : ℕ → ℝ) (m next : ℕ → ℕ) (B : Finset ℕ)
    (hH_def : ∀ r, H r = (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1)))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hB_def : B = Finset.image m ((Finset.range N).filter (fun k => j ≤ k)))
    (hj_tail_high : ∀ k, j ≤ k → 9 ≤ m k)
    (hB_nonempty : B.Nonempty)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty → r < next r) :
    ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty → Q (next r) ≤ Q r := by
  intro r hr hr_ne
  have hr_pos : 0 < r := by
    have hr_image :
        r ∈ Finset.image m ((Finset.range N).filter (fun k => j ≤ k)) := by
      simpa [hB_def] using hr
    rcases Finset.mem_image.mp hr_image with ⟨k, hk, hmk⟩
    have hjk : j ≤ k := (Finset.mem_filter.mp hk).2
    have hhigh : 9 ≤ m k := hj_tail_high k hjk
    have hr_high : 9 ≤ r := by
      simpa [hmk] using hhigh
    omega
  exact
    compact_ceiling_grid_Q_antitone Q H hH_def hQ_def hr_pos
      (le_of_lt (hnext_gt r hr hr_ne))

/-- Rowwise reduction from an arbitrary admissible compact inner budget to the
positive natural ceiling of its real budget requirement.

Aligns with Lan Corollary 8.3 proof step 7 after Eq. (8.1.75), where the
compact budget lower bound is combined with the normalized SPS factor's
monotonicity. Candidate audit: checked the local
`compact_linear_sps_normalized_q_over_t_antitone`, SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`, Mathlib `Nat.ceil_le`, and
SOptLib ceiling helpers `le_positive_ceil_max_one`/
`natCast_max_one_ceil_le_add_two`; the antitone helper is the matching
rowwise primitive, while the telescope helpers are aggregate-level. -/
theorem compact_linear_sps_tight_budget_reduction
    (c : ℝ) (hc : 0 ≤ c) (κ : PositiveTime) {t : ℕ} (ht : 0 < t)
    (hbudget :
      c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 ≤ (t : ℝ)) :
    let m : ℕ := max 1 (Nat.ceil (c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2))
    ((c * ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (t : ℝ))) *
        (((t : ℝ) + 1) * ((t : ℝ) + 2) / ((t : ℝ) + 3) ^ 2)) *
        (1 + ((Finset.range t).sum (fun i => 1 / ((i : ℝ) + 1))) /
          (t : ℝ))) ≤
      c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) *
        (((((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 3) ^ 2) *
          (1 + ((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (m : ℝ))) /
          (m : ℝ)) := by
  classical
  let a : ℝ := (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2
  let y : ℝ := c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2
  let m : ℕ := max 1 (Nat.ceil y)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hy_eq : y = c * a := by
    dsimp [y, a]
    ring
  have hy_nonneg : 0 ≤ y := by
    rw [hy_eq]
    exact mul_nonneg hc ha_nonneg
  have hm_pos : 0 < m := by
    dsimp [m]
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (Nat.ceil y))
  have hceil_le : Nat.ceil y ≤ t := by
    apply Nat.ceil_le.mpr
    rw [hy_eq]
    simpa [a, mul_assoc] using hbudget
  have hm_le_t : m ≤ t := by
    dsimp [m]
    exact max_le (Nat.succ_le_of_lt ht) hceil_le
  have hmono :=
    compact_linear_sps_normalized_q_over_t_antitone (m := m) (n := t) hm_pos hm_le_t
  have hscale_nonneg : 0 ≤ c * a := mul_nonneg hc ha_nonneg
  have hmul := mul_le_mul_of_nonneg_left hmono hscale_nonneg
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht_ne : (t : ℝ) ≠ 0 := ne_of_gt htR
  have ht3_ne : (t : ℝ) + 3 ≠ 0 := by positivity
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm_pos
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hm3_ne : (m : ℝ) + 3 ≠ 0 := by positivity
  dsimp [m, y, a] at hmul ⊢
  convert hmul using 1 <;>
    field_simp [ht_ne, ht3_ne, hm_ne, hm3_ne] <;>
    ring

/-- Basic positivity and sharp one-sided ceiling facts for the compact common grid.

Aligns with Lan Corollary 8.3 proof step 7 after Eq. (8.1.75), where the
common compact budget is replaced by its positive natural ceiling. Candidate
audit: considered SOptLib `le_positive_ceil_max_one`,
`natCast_max_one_ceil_le_add_two`, Mathlib `Nat.le_ceil` and
`Nat.ceil_lt_add_one`, plus the local normalized-row helpers. The SOptLib lower
bound is the exact match for `y ≤ m`; the two-unit overshoot is too coarse for
the signed grid slack, so the strict lower alternative is proved directly from
`Nat.ceil_lt_add_one` on the non-`m = 1` branch. -/
theorem compact_ceiling_grid_basic_bounds
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
    let y : ℝ := c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2
    let m : ℕ := max 1 (Nat.ceil y)
    0 ≤ y ∧ 0 < m ∧ y ≤ (m : ℝ) ∧ (m = 1 ∨ (m : ℝ) - 1 < y) := by
  classical
  let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
  let y : ℝ := c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2
  let m : ℕ := max 1 (Nat.ceil y)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg (mul_nonneg hc (by positivity)) (sq_nonneg ((κ.1 : ℝ) + 1))
  have hm_pos : 0 < m := by
    dsimp [m]
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (Nat.ceil y))
  have hy_le_m : y ≤ (m : ℝ) := by
    simpa [m] using le_positive_ceil_max_one y
  have hbranch : m = 1 ∨ (m : ℝ) - 1 < y := by
    by_cases hm_one : m = 1
    · exact Or.inl hm_one
    · right
      have hceil_not_le_one : ¬ Nat.ceil y ≤ 1 := by
        intro hceil_le_one
        have hm_eq_one : m = 1 := by
          dsimp [m]
          exact max_eq_left hceil_le_one
        exact hm_one hm_eq_one
      have hceil_gt_one : 1 < Nat.ceil y := Nat.lt_of_not_ge hceil_not_le_one
      have hm_eq_ceil : m = Nat.ceil y := by
        dsimp [m]
        exact max_eq_right (le_of_lt hceil_gt_one)
      have hceil_lt : ((Nat.ceil y : ℕ) : ℝ) < y + 1 :=
        Nat.ceil_lt_add_one hy_nonneg
      have hm_lt : (m : ℝ) < y + 1 := by
        simpa [hm_eq_ceil] using hceil_lt
      linarith
  exact ⟨hy_nonneg, hm_pos, hy_le_m, hbranch⟩

/-- Algebraic split of a ceiling-grid row into ceiling slack and normalized overrun.

Aligns with Lan Corollary 8.3 proof step 7 after Eq. (8.1.79), where the
compact row is compared against the tight ceiling budget. Candidate audit:
considered `compact_linear_sps_normalized_q_minus_one_eq`,
`compact_linear_sps_normalized_row_excess_identity`, and SOptLib finite
telescope helpers. Those helpers expose the normalized `q - 1` numerator or
aggregate telescoping API, while this route needs the literal one-row identity
`y * Q m - 1 = (y - m) * Q m + (m * Q m - 1)` to separate ceiling slack from
the harmonic overrun. -/
theorem compact_ceiling_grid_row_excess_split (y : ℝ) (m : ℕ) :
    let Q : ℝ :=
      (((((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 3) ^ 2) *
        (1 + ((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) /
          (m : ℝ))) /
        (m : ℝ))
    y * Q - 1 = (y - (m : ℝ)) * Q + ((m : ℝ) * Q - 1) := by
  intro Q
  ring

/-- Integer-budget overrun of the compact ceiling-grid row in harmonic numerator form.

Aligns with Lan Corollary 8.3 proof step 7 after Eq. (8.1.79), reusing the
proved normalized `q - 1` expansion at the integer ceiling level. Candidate
audit: considered `compact_linear_sps_normalized_q_minus_one_eq` and
`compact_ceiling_grid_row_excess_split`; the former is the exact numerator
identity for `q m - 1`, while this helper only transports it through the local
`Q m = q m / m` notation needed by the ceiling-grid slack split. -/
theorem compact_ceiling_grid_integer_overrun_eq {m : ℕ} (hm : 0 < m) :
    let Q : ℝ :=
      (((((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 3) ^ 2) *
        (1 + ((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) /
          (m : ℝ))) /
        (m : ℝ))
    (m : ℝ) * Q - 1 =
      (((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) *
          ((m : ℝ) ^ 2 + 3 * (m : ℝ) + 2) -
        (3 * (m : ℝ) ^ 2 + 7 * (m : ℝ))) /
        ((m : ℝ) * ((m : ℝ) + 3) ^ 2) := by
  intro Q
  have hq := compact_linear_sps_normalized_q_minus_one_eq hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have hm3 : (m : ℝ) + 3 ≠ 0 := by positivity
  calc
    (m : ℝ) * Q - 1 =
        ((((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 3) ^ 2) *
          (1 + ((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) /
            (m : ℝ)) -
          1) := by
          dsimp [Q]
          field_simp [hmR, hm3]
    _ =
      (((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) *
          ((m : ℝ) ^ 2 + 3 * (m : ℝ) + 2) -
        (3 * (m : ℝ) ^ 2 + 7 * (m : ℝ))) /
        ((m : ℝ) * ((m : ℝ) + 3) ^ 2) := hq

/-- Full ceiling-grid row decomposition into negative ceiling slack plus the
explicit harmonic integer-budget overrun.

Aligns with Lan Corollary 8.3 proof step 7 after Eq. (8.1.79). Candidate
audit: considered `compact_ceiling_grid_row_excess_split`,
`compact_ceiling_grid_integer_overrun_eq`, and SOptLib telescope helpers; the
first two are the matching row-level identities, while the telescope helpers
remain aggregate-level tools for the still-open signed potential step. -/
theorem compact_ceiling_grid_signed_row_eq (y : ℝ) {m : ℕ} (hm : 0 < m) :
    let Q : ℝ :=
      (((((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 3) ^ 2) *
        (1 + ((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) /
          (m : ℝ))) /
        (m : ℝ))
    y * Q - 1 =
      (y - (m : ℝ)) * Q +
        ((((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) *
            ((m : ℝ) ^ 2 + 3 * (m : ℝ) + 2) -
          (3 * (m : ℝ) ^ 2 + 7 * (m : ℝ))) /
          ((m : ℝ) * ((m : ℝ) + 3) ^ 2)) := by
  intro Q
  have hinter :
      (m : ℝ) * Q - 1 =
        (((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) *
            ((m : ℝ) ^ 2 + 3 * (m : ℝ) + 2) -
          (3 * (m : ℝ) ^ 2 + 7 * (m : ℝ))) /
          ((m : ℝ) * ((m : ℝ) + 3) ^ 2) := by
    simpa [Q] using compact_ceiling_grid_integer_overrun_eq hm
  calc
    y * Q - 1 = (y - (m : ℝ)) * Q + ((m : ℝ) * Q - 1) := by
      simpa [Q] using compact_ceiling_grid_row_excess_split y m
    _ =
      (y - (m : ℝ)) * Q +
        ((((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) *
            ((m : ℝ) ^ 2 + 3 * (m : ℝ) + 2) -
          (3 * (m : ℝ) ^ 2 + 7 * (m : ℝ))) /
          ((m : ℝ) * ((m : ℝ) + 3) ^ 2)) := by
      rw [hinter]

/-- Monotonicity of the positive integer ceiling grid used by the compact SPS
scalar reduction.

Aligns with Lan Eq. (8.1.75) in Corollary 8.3: the common compact inner budget
is a positive totalized ceiling of an increasing cubic scale. Candidate audit:
checked SOptLib `le_positive_ceil_max_one`, `natCast_max_one_ceil_le_add_two`,
Mathlib `Nat.ceil_mono`, and the local fixed-horizon ceiling monotonicity
helper; the SOptLib facts give ceiling bounds rather than monotonicity, while
`Nat.ceil_mono` is the exact Mathlib primitive for transporting the cubic-grid
comparison through the ceiling. -/
theorem compact_ceiling_grid_m_monotone
    (c : ℝ) (hc : 0 ≤ c) (m : ℕ → ℕ)
    (hm_def : ∀ k,
      m k =
        max 1 (Nat.ceil
          (c * (((k + 1 : ℕ) : ℝ)) * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2)))) :
    Monotone m := by
  intro a b hab
  rw [hm_def a, hm_def b]
  exact max_le_max_left 1 (Nat.ceil_mono (by
    have ha1_nonneg : 0 ≤ (((a + 1 : ℕ) : ℝ)) := by positivity
    have hb1_nonneg : 0 ≤ (((b + 1 : ℕ) : ℝ)) := by positivity
    have hbase : ((a + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hab
    have hsq :
        (((a + 1 : ℕ) : ℝ) + 1) ^ 2 ≤
          (((b + 1 : ℕ) : ℝ) + 1) ^ 2 := by
      have hashift_nonneg : 0 ≤ (((a + 1 : ℕ) : ℝ) + 1) := by positivity
      have hbshift_nonneg : 0 ≤ (((b + 1 : ℕ) : ℝ) + 1) := by positivity
      have hshift :
          (((a + 1 : ℕ) : ℝ) + 1) ≤ (((b + 1 : ℕ) : ℝ) + 1) := by
        linarith
      exact (sq_le_sq₀ hashift_nonneg hbshift_nonneg).2 hshift
    have hprod :
        (((a + 1 : ℕ) : ℝ) * ((((a + 1 : ℕ) : ℝ) + 1) ^ 2)) ≤
          (((b + 1 : ℕ) : ℝ) * ((((b + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
      exact mul_le_mul hbase hsq (sq_nonneg _) hb1_nonneg
    have hmul := mul_le_mul_of_nonneg_left hprod hc
    simpa [mul_assoc] using hmul))

/-- Exact one-step increment of the cubic compact ceiling-grid scale.

Aligns with Lan Eq. (8.1.75) in Corollary 8.3: before taking the positive
ceiling, the compact inner budget is a constant multiple of the cubic grid
`(k+1)(k+2)^2`. Candidate audit: considered the pre-searched SOptLib
telescope candidates, local `compact_ceiling_grid_m_monotone`, and Mathlib
polynomial/finite-difference search hits; none states this literal cubic
increment, which is the source-specific bucket-width fact needed for the
remaining potential-drop proof. -/
theorem compact_ceiling_grid_cubic_increment_eq
    (c : ℝ) (k : ℕ) :
    c * (((k + 2 : ℕ) : ℝ)) * ((((k + 2 : ℕ) : ℝ) + 1) ^ 2) -
      c * (((k + 1 : ℕ) : ℝ)) * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2) =
      c * (((k + 2 : ℕ) : ℝ)) * (3 * (k : ℝ) + 7) := by
  norm_num
  ring

/-- The compact cubic grid has a strictly positive successor increment when
the common compact scale is positive.

Aligns with Lan Eq. (8.1.75) in Corollary 8.3 and specializes the preceding
literal finite-difference identity to the ordered fact needed by realized
ceiling buckets. Candidate audit: considered local
`compact_ceiling_grid_m_monotone`, SOptLib telescope helpers, and Mathlib
monotonicity searches; none gives this positive successor increment for the
paper's cubic grid, so this helper records the source-derived step directly. -/
theorem compact_ceiling_grid_cubic_increment_pos
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    0 <
      c * (((k + 2 : ℕ) : ℝ)) * ((((k + 2 : ℕ) : ℝ) + 1) ^ 2) -
        c * (((k + 1 : ℕ) : ℝ)) * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2) := by
  rw [compact_ceiling_grid_cubic_increment_eq]
  positivity

/-- Strict monotonicity of the source cubic grid before applying the ceiling.

Aligns with Lan Eq. (8.1.75) in Corollary 8.3: realized ceiling buckets come
from a strictly increasing cubic real grid when the compact scale is positive.
Candidate audit: considered SOptLib finite-image extrema/telescope helpers and
the local ceiling monotonicity theorem; those apply after ceiling or to generic
finite sets, while the bucket-potential proof needs strict monotonicity of the
underlying cubic scale itself. -/
theorem compact_ceiling_grid_cubic_strictMono
    {c : ℝ} (hc : 0 < c) :
    StrictMono (fun k : ℕ =>
      c * (((k + 1 : ℕ) : ℝ)) * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  have hinc := compact_ceiling_grid_cubic_increment_pos hc k
  linarith

/-- A single integer-budget harmonic overrun is bounded by the harmonic
average `H_m / m`.

Aligns with the rowwise part of Lan Corollary 8.3 proof step 7 after
normalizing the compact SPS row. Candidate audit: checked the local
`compact_linear_sps_normalized_q_minus_one_eq`, SOptLib telescope helper
`sum_range_sub_succ_le_first_of_last_nonneg`, and Mathlib finite-sum search
hits; none supplies this one-row harmonic envelope, so the proof keeps the
literal numerator and clears the positive denominator. -/
theorem compact_ceiling_grid_integer_overrun_le_harmonic_div
    {r : ℕ} (hr : 0 < r) :
    ((((Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1))) *
        ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
      (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
      ((r : ℝ) * ((r : ℝ) + 3) ^ 2)) ≤
      ((Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1))) / (r : ℝ) := by
  classical
  let H : ℝ := (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1))
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    exact Finset.sum_nonneg (by intro i _hi; positivity)
  have hsum_nonneg :
      0 ≤ (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1)) := by
    simpa [H] using hH_nonneg
  have hsum_inv_nonneg :
      0 ≤ (Finset.range r).sum (fun i => (1 + (i : ℝ))⁻¹) := by
    simpa [one_div, add_comm] using hsum_nonneg
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hr3_ne : (r : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hr_ne, hr3_ne]
  ring_nf
  nlinarith [hsum_inv_nonneg]

/-- The compact integer-budget overrun is nonpositive before the harmonic
transition point `m = 9`.

Aligns with the finite negative-prefix part of the grouped scalar proof after
Lan Eq. (8.1.79). Candidate audit: checked the row identity
`compact_linear_sps_normalized_q_minus_one_eq`, the one-row envelope
`compact_ceiling_grid_integer_overrun_le_harmonic_div`, and SOptLib telescope
helpers; none package this finite sign table, so the proof discharges the
eight possible integer budgets directly. -/
theorem compact_ceiling_grid_integer_overrun_nonpos_of_le_eight
    {r : ℕ} (hr_pos : 0 < r) (hr_le : r ≤ 8) :
    ((((Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1))) *
        ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
      (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
      ((r : ℝ) * ((r : ℝ) + 3) ^ 2)) ≤ 0 := by
  interval_cases r <;> norm_num [Finset.sum_range_succ]

/-- Quantitative version of the low compact integer-budget overrun table.

Aligns with the finite negative-prefix part of Lan Corollary 8.3 after
Eq. (8.1.79): for integer budgets before the transition point, the weakest
row is `r = 8`. Candidate audit: considered the qualitative local helper
`compact_ceiling_grid_integer_overrun_nonpos_of_le_eight`, the row identity
`compact_linear_sps_normalized_q_minus_one_eq`, and SOptLib telescope helpers;
none records the explicit low-row cancellation constant needed by the signed
prefix route, so this proof discharges the same eight-row table quantitatively. -/
theorem compact_ceiling_grid_integer_overrun_le_low_eight_bound
    {r : ℕ} (hr_pos : 0 < r) (hr_le : r ≤ 8) :
    ((((Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1))) *
        ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
      (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
      ((r : ℝ) * ((r : ℝ) + 3) ^ 2)) ≤ -(95 / 27104 : ℝ) := by
  interval_cases r <;> norm_num [Finset.sum_range_succ]

/-- Quantitative lower bound for the exact low-row credit prefix.

Aligns with the finite negative-prefix part of Lan Corollary 8.3 after
Eq. (8.1.79): every row before the first high compact ceiling contributes at
least the weakest low-row credit `95/27104`. Candidate audit: considered the
pre-searched process/update candidates, target
`compact_ceiling_grid_low_prefix_exact_credit`, and SOptLib/Mathlib telescope
helpers; the process candidates are unrelated to this scalar finite prefix, the
exact-credit helper gives only the signed prefix comparison, and the telescope
helpers do not include the eight-row quantitative table. -/
theorem compact_ceiling_grid_low_prefix_credit_ge_quantitative
    (N j : ℕ) (R : ℕ → ℝ) (m : ℕ → ℕ)
    (hj_le_N : j ≤ N)
    (hprefix_low : ∀ k ∈ Finset.range N, k < j → m k ≤ 8)
    (hrow_low_quant : ∀ k, m k ≤ 8 → R (m k) ≤ -(95 / 27104 : ℝ)) :
    (j : ℝ) * (95 / 27104 : ℝ) ≤
      (Finset.range N).sum (fun k =>
        if k < j then if m k ≤ 8 then -R (m k) else 0 else 0) := by
  classical
  have hprefix_filter :
      (Finset.range N).filter (fun k => k < j) = Finset.range j := by
    ext k
    constructor
    · intro hk
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
    · intro hk
      have hklt : k < j := Finset.mem_range.mp hk
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (lt_of_lt_of_le hklt hj_le_N), hklt⟩
  calc
    (j : ℝ) * (95 / 27104 : ℝ)
        = (Finset.range j).sum (fun _ => (95 / 27104 : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Finset.range j).sum (fun k =>
          if m k ≤ 8 then -R (m k) else 0) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hklt : k < j := Finset.mem_range.mp hk
          have hkN : k ∈ Finset.range N :=
            Finset.mem_range.mpr (lt_of_lt_of_le hklt hj_le_N)
          have hlow : m k ≤ 8 := hprefix_low k hkN hklt
          have hrow : R (m k) ≤ -(95 / 27104 : ℝ) :=
            hrow_low_quant k hlow
          simp [hlow]
          linarith
    _ = ((Finset.range N).filter (fun k => k < j)).sum (fun k =>
          if m k ≤ 8 then -R (m k) else 0) := by
          rw [hprefix_filter]
    _ = (Finset.range N).sum (fun k =>
          if k < j then if m k ≤ 8 then -R (m k) else 0 else 0) := by
          rw [Finset.sum_filter]

/-- Source-specialized quantitative lower bound for the compact-grid low-prefix
credit.

This is the retained low-prefix correction used in the signed high-tail budget:
the exact `R` definition turns every low realized budget into at least the
weakest eight-row credit, and `lowCredit` preserves that contribution. -/
theorem compact_ceiling_grid_low_prefix_credit_ge_quantitative_source
    (N j : ℕ) (R H lowCredit : ℕ → ℝ) (m : ℕ → ℕ)
    (hm_pos : ∀ k, 0 < m k)
    (hH_def : ∀ r, H r = (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1)))
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hprefix_low : ∀ k ∈ Finset.range N, k < j → m k ≤ 8)
    (hlowCredit : ∀ r, lowCredit r = if r ≤ 8 then -R r else 0)
    (hj_le_N : j ≤ N) :
    ((j : ℝ) * (95 / 27104 : ℝ)) ≤
      (Finset.range N).sum (fun k =>
        if k < j then lowCredit (m k) else 0) := by
  classical
  have hrow_low_quant :
      ∀ k, m k ≤ 8 → R (m k) ≤ -(95 / 27104 : ℝ) := by
    intro k hle
    simpa [hR_def (m k), hH_def (m k)] using
      compact_ceiling_grid_integer_overrun_le_low_eight_bound
        (hm_pos k) hle
  have hlow_form :
      (Finset.range N).sum (fun k =>
        if k < j then lowCredit (m k) else 0) =
      (Finset.range N).sum (fun k =>
        if k < j then if m k ≤ 8 then -R (m k) else 0 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases hklt : k < j
    · simp [hklt, hlowCredit (m k)]
    · simp [hklt]
  rw [hlow_form]
  exact
    compact_ceiling_grid_low_prefix_credit_ge_quantitative
      N j R m hj_le_N hprefix_low hrow_low_quant

/-- Range-indexed form of the residual telescope used for compact ceiling
buckets.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): a bucket's excess over its final
endpoint deficit is the weighted sum of adjacent deficit drops. Candidate audit:
checked target endpoint normal-form helpers, SOptLib `sum_Icc_sub_succ`, Mathlib
`Finset.sum_Ico_sub`, and `Finset.sum_Ico_eq_sum_range`; these supply the
unweighted telescope/reindexing APIs, but not the weighted residual identity. -/
theorem finset_range_residual_eq_weighted_drops
    (a n : ℕ) (D : ℕ → ℝ) :
    (Finset.range (n + 1)).sum (fun i => D (a + i)) -
        ((n + 1 : ℕ) : ℝ) * D (a + n) =
      (Finset.range n).sum (fun i =>
        (((i + 1 : ℕ) : ℝ) * (D (a + i) - D (a + i + 1)))) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (Finset.range (n + 1 + 1)).sum (fun i => D (a + i)) -
            ((n + 1 + 1 : ℕ) : ℝ) * D (a + (n + 1))
            =
          ((Finset.range (n + 1)).sum (fun i => D (a + i)) -
              ((n + 1 : ℕ) : ℝ) * D (a + n)) +
            ((n + 1 : ℕ) : ℝ) * (D (a + n) - D (a + n + 1)) := by
            rw [Finset.sum_range_succ]
            have hidx : a + (n + 1) = a + n + 1 := by omega
            rw [hidx]
            have hcast : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by
              norm_num
            rw [hcast]
            ring
        _ =
          (Finset.range n).sum (fun i =>
              (((i + 1 : ℕ) : ℝ) * (D (a + i) - D (a + i + 1)))) +
            ((n + 1 : ℕ) : ℝ) * (D (a + n) - D (a + n + 1)) := by
            rw [ih]
        _ =
          (Finset.range (n + 1)).sum (fun i =>
            (((i + 1 : ℕ) : ℝ) * (D (a + i) - D (a + i + 1)))) := by
            rw [Finset.sum_range_succ]

/-- Closed-interval residual telescope as weighted adjacent drops.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): for a bucket interval `[a,b]`,
the retained residual over the final endpoint deficit is exactly the triangular
weighted sum of adjacent deficit drops. Candidate audit: checked target endpoint
helpers, SOptLib `sum_Icc_sub_succ`, Mathlib `Finset.sum_Ico_sub`,
`Finset.Ico_succ_right_eq_Icc`, and `Finset.sum_Ico_eq_sum_range`; the available
lemmas give unweighted telescopes and reindexing only, so this specializes the
proved range weighted-residual identity to closed intervals. -/
theorem finset_Icc_residual_eq_weighted_Ico_drops
    (a b : ℕ) (D : ℕ → ℝ) (hab : a ≤ b) :
    (Finset.Icc a b).sum D - ((Finset.Icc a b).card : ℝ) * D b =
      (Finset.Ico a b).sum (fun k =>
        (((k - a + 1 : ℕ) : ℝ) * (D k - D (k + 1)))) := by
  classical
  let n : ℕ := b - a
  have hb_eq : a + n = b := by
    dsimp [n]
    omega
  have hcard : (Finset.Icc a b).card = n + 1 := by
    dsimp [n]
    simp [Nat.card_Icc]
    omega
  have hIcc_sum :
      (Finset.Icc a b).sum D =
        (Finset.range (n + 1)).sum (fun i => D (a + i)) := by
    calc
      (Finset.Icc a b).sum D =
          (Finset.Ico a (b + 1)).sum D := by
          rw [Finset.Ico_add_one_right_eq_Icc]
      _ = (Finset.range (b + 1 - a)).sum (fun i => D (a + i)) := by
          rw [Finset.sum_Ico_eq_sum_range]
      _ = (Finset.range (n + 1)).sum (fun i => D (a + i)) := by
          have hlen : b + 1 - a = n + 1 := by
            dsimp [n]
            omega
          rw [hlen]
  have hIco_sum :
      (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) * (D k - D (k + 1)))) =
        (Finset.range n).sum (fun i =>
          (((i + 1 : ℕ) : ℝ) * (D (a + i) - D (a + i + 1)))) := by
    calc
      (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) * (D k - D (k + 1)))) =
        (Finset.range (b - a)).sum (fun i =>
          ((((a + i) - a + 1 : ℕ) : ℝ) *
            (D (a + i) - D (a + i + 1)))) := by
          rw [Finset.sum_Ico_eq_sum_range]
      _ = (Finset.range n).sum (fun i =>
          (((i + 1 : ℕ) : ℝ) * (D (a + i) - D (a + i + 1)))) := by
          dsimp [n]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hsub : (a + i) - a = i := by omega
          rw [hsub]
  calc
    (Finset.Icc a b).sum D - ((Finset.Icc a b).card : ℝ) * D b =
        (Finset.range (n + 1)).sum (fun i => D (a + i)) -
          ((n + 1 : ℕ) : ℝ) * D (a + n) := by
        rw [hIcc_sum, hcard, hb_eq]
    _ = (Finset.range n).sum (fun i =>
          (((i + 1 : ℕ) : ℝ) * (D (a + i) - D (a + i + 1)))) := by
        exact finset_range_residual_eq_weighted_drops a n D
    _ = (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) * (D k - D (k + 1)))) := by
        rw [hIco_sum]

/-- Exact realized credit from the low rows before the first high compact
ceiling bucket.

Aligns with the finite negative-prefix part of Lan Corollary 8.3 after
Eq. (8.1.79): low rows should retain their actual bucket-dependent negative
overrun rather than being collapsed immediately to the weakest `r = 8`
constant. Candidate audit: checked local `compact_ceiling_grid_signed_row_eq`,
`compact_ceiling_grid_integer_overrun_nonpos_of_le_eight`,
`compact_ceiling_grid_integer_overrun_le_low_eight_bound`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the row identity supplies the
needed signed split, while no existing helper packages this exact finite
prefix credit. -/
theorem compact_ceiling_grid_low_prefix_exact_credit
    (N j : ℕ) (grid R Q : ℕ → ℝ) (m : ℕ → ℕ)
    (hprefix_low : ∀ k ∈ Finset.range N, k < j → m k ≤ 8)
    (hslack_nonpos : ∀ k, (grid k - (m k : ℝ)) * Q (m k) ≤ 0)
    (hsigned_row : ∀ k,
      grid k * Q (m k) - 1 =
        (grid k - (m k : ℝ)) * Q (m k) + R (m k)) :
    (Finset.range N).sum (fun k =>
      if k < j then grid k * Q (m k) - 1 else 0) ≤
      - (Finset.range N).sum (fun k =>
        if k < j then if m k ≤ 8 then - R (m k) else 0 else 0) := by
  classical
  calc
    (Finset.range N).sum (fun k =>
        if k < j then grid k * Q (m k) - 1 else 0)
        ≤ (Finset.range N).sum (fun k =>
            if k < j then R (m k) else 0) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          by_cases hklt : k < j
          · have hsplit := hsigned_row k
            have hslack := hslack_nonpos k
            simp [hklt]
            linarith
          · simp [hklt]
    _ = - (Finset.range N).sum (fun k =>
          if k < j then if m k ≤ 8 then - R (m k) else 0 else 0) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro k hk
          by_cases hklt : k < j
          · have hlow : m k ≤ 8 := hprefix_low k hk hklt
            simp [hklt, hlow]
          · simp [hklt]

/-- Low-prefix signed rows are bounded by the negative realized low credit.

Aligns with the finite negative-prefix part of Lan Corollary 8.3 after
Eq. (8.1.79): this is the `lowCredit`-specialized form of the exact credit
comparison. Candidate audit: considered target
`compact_ceiling_grid_low_prefix_exact_credit`, local
`compact_ceiling_grid_signed_row_eq`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the exact-credit helper supplies
the matching signed prefix inequality, while the telescope API is unrelated to
the low-row credit rewrite. -/
theorem compact_ceiling_grid_prefix_signed_le_neg_low_credit
    (N j : ℕ) (grid R Q lowCredit : ℕ → ℝ) (m : ℕ → ℕ)
    (hprefix_low : ∀ k ∈ Finset.range N, k < j → m k ≤ 8)
    (hslack_nonpos : ∀ k, (grid k - (m k : ℝ)) * Q (m k) ≤ 0)
    (hsigned_row : ∀ k,
      grid k * Q (m k) - 1 =
        (grid k - (m k : ℝ)) * Q (m k) + R (m k))
    (hlowCredit : ∀ r, lowCredit r = if r ≤ 8 then -R r else 0) :
    (Finset.range N).sum (fun k =>
      if k < j then grid k * Q (m k) - 1 else 0) ≤
      - (Finset.range N).sum (fun k =>
        if k < j then lowCredit (m k) else 0) := by
  classical
  have hexact :=
    compact_ceiling_grid_low_prefix_exact_credit
      N j grid R Q m hprefix_low hslack_nonpos hsigned_row
  have hcredit_eq :
      (Finset.range N).sum (fun k =>
        if k < j then if m k ≤ 8 then - R (m k) else 0 else 0) =
      (Finset.range N).sum (fun k =>
        if k < j then lowCredit (m k) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hklt : k < j
    · have hlow : m k ≤ 8 := hprefix_low k hk hklt
      simpa [hklt, hlow, hlowCredit (m k)]
    · simp [hklt]
  simpa [hcredit_eq] using hexact

/-- A realized compact ceiling bucket is exactly its grid-sum deficit plus a
cardinality multiple of the integer overrun.

Aligns with the bucket-local form needed for Lan Corollary 8.3 after
Eq. (8.1.79): once rows are grouped by a fixed integer budget `r`, the signed
tail contribution is a pure cardinality/grid-sum arithmetic problem. Candidate
audit: checked SOptLib finite-sum/telescope helpers
`sum_range_sub_succ_le_first_of_last_nonneg` and `inv_card_smul_sum_sub_const_eq`,
Mathlib `Finset.sum_filter`/`Finset.sum_sub_distrib`, and target-file compact
ceiling helpers; none states this realized-bucket normalization, so this helper
records the exact bucket interface for the source-derived scalar simplification. -/
theorem compact_ceiling_grid_bucket_signed_sum_eq_card
    (N j r : ℕ) (grid R Q : ℕ → ℝ) (m : ℕ → ℕ) :
    (Finset.range N).sum (fun k =>
      if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0) =
      Q r *
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).sum grid -
          (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
            (r : ℝ)) +
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
          R r := by
  classical
  let s : Finset ℕ := (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  have hfilter :
      (Finset.range N).sum (fun k =>
        if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0) =
        s.sum (fun k => (grid k - (r : ℝ)) * Q r + R r) := by
    rw [← Finset.sum_filter]
  calc
    (Finset.range N).sum (fun k =>
        if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)
        = s.sum (fun k => (grid k - (r : ℝ)) * Q r + R r) := hfilter
    _ = Q r * (s.sum grid - (s.card : ℝ) * (r : ℝ)) +
          (s.card : ℝ) * R r := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
              nsmul_eq_mul]
            ring
          · rw [Finset.sum_const, nsmul_eq_mul]
    _ =
      Q r *
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).sum grid -
          (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
            (r : ℝ)) +
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
          R r := by
          simp [s]


end StochasticGradientSliding
