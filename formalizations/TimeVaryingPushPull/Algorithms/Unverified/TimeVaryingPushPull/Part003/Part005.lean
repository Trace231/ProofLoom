import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope
import Algorithms.Unverified.TimeVaryingPushPull.Part002
import Algorithms.Unverified.TimeVaryingPushPull.Part003.Part004

/-!
# Time-varying push-pull: object layer

This file records the canonical objects from the time-varying push-pull paper:
the finite-average objective, the sampled gradient table `G_t`, the one-step
push-pull recursion, and the generated iterate process. The recurrence is not a
field of `Setup`; it is a definition built from the paper data and a noise
sample path.
-/

open scoped BigOperators
open scoped Gradient
open scoped InnerProductSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open scoped ComplexConjugate

open MeasureTheory
open ProbabilityTheory
open Filter

namespace Algorithms.Unverified.TimeVaryingPushPull

universe uΩ

variable {Node E : Type*}
variable [Fintype Node] [Nonempty Node]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

namespace Setup

variable (setup : Setup Node E)

/-- Deterministic quotient normalization for the Appendix C.2 bias term.
If the period denominator is linearly bounded below, the denominator and
finite-phase sum have the source first-order expansions, and the geometric
tail is nonnegative, then the dimensionless bias quotient differs from one by
an `O(alpha)` term plus a bounded multiple of the tail. -/
theorem real_common_scale_quotient_error_bound
    {lambda h p alpha den S tail dlow Cd Cs : ℝ}
    (hlambda_pos : 0 < lambda) (hh_pos : 0 < h) (hp_pos : 0 < p)
    (halpha_pos : 0 < alpha) (hdlow_pos : 0 < dlow)
    (hCd_nonneg : 0 ≤ Cd) (hCs_nonneg : 0 ≤ Cs)
    (hden_lower : dlow * alpha ≤ den)
    (hden_close : |den - alpha * (2 * lambda * p * h)| ≤ Cd * alpha ^ 2)
    (hphase_close : |S - p| ≤ Cs * alpha)
    (htail_nonneg : 0 ≤ tail) :
    |2 * lambda * h * alpha * S * ((1 - tail) / den) - 1| ≤
      ((2 * lambda * h * Cs + Cd) / dlow) * alpha +
        ((2 * lambda * h * (p + Cs * alpha)) / dlow) * tail := by
  exact common_scale_quotient_error_le
    (by positivity) hp_pos.le halpha_pos hdlow_pos hden_lower hden_close
    hphase_close htail_nonneg

/-- Deterministic common-scale quotient estimate for the Appendix C.2 bias
term.  This is the real-analysis core left after the source objects have been
reduced to: (i) the exact `Delta` normalization, (ii) a linear lower bound on
`1-Gamma(alpha)^2`, (iii) a first-order denominator expansion, (iv) the
finite-phase expansion `sum A_r(alpha)^2=p+O(alpha)`, and (v) the exponential
geometric tail. -/
theorem quadraticScalarBiasBlockAverage_bound_from_common_scale
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (alpha0 c dlow Cd Cs : ℝ)
    (halpha0_pos : 0 < alpha0) (hc_pos : 0 < c)
    (hdlow_pos : 0 < dlow) (hCd_nonneg : 0 ≤ Cd)
    (hCs_nonneg : 0 ≤ Cs)
    (hcommon :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ K : ℕ,
          (dlow * alpha ≤
              1 - quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ 2) ∧
            quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ (2 * K) ≤
              Real.exp (-(c * alpha *
                ((K * quad.period : ℕ) : ℝ))))
    (hden_close :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        |(1 - quadraticScalarPeriodMultiplier (Node := Node)
            quad lambda alpha ^ 2) -
          alpha * (2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))| ≤
            Cd * alpha ^ 2)
    (hphase_close :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        |(∑ r : Fin quad.period,
          quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r.1 ^ 2) -
            (quad.period : ℝ)| ≤ Cs * alpha) :
    ∃ alpha0' c' C : ℝ, 0 < alpha0' ∧ 0 < c' ∧ 0 ≤ C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0' →
        ∀ K : ℕ, 1 ≤ K →
          |quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K -
            quad.Delta /
              ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha *
                ((K * quad.period : ℕ) : ℝ))| ≤
          C * ((((K * quad.period : ℕ) : ℝ)⁻¹) +
              Real.exp (-(c' * alpha *
                ((K * quad.period : ℕ) : ℝ))) /
                (alpha * ((K * quad.period : ℕ) : ℝ))) := by
  classical
  let qlin : ℝ := (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Cs + Cd) / dlow
  let qtail : ℝ :=
    (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) *
        ((quad.period : ℝ) + Cs * alpha0)) / dlow
  let C : ℝ := quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * (qlin + qtail)
  refine ⟨alpha0, c, C, halpha0_pos, hc_pos, ?_, ?_⟩
  · have hDelta_nonneg : 0 ≤ quad.Delta := quad.Delta_positive.le
    have hinfluence_nonneg : 0 ≤ (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) :=
      quad.influenceGain_pos.le
    have hfactor_nonneg : 0 ≤ quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) := by
      exact div_nonneg hDelta_nonneg hinfluence_nonneg
    have hqlin_nonneg : 0 ≤ qlin := by
      dsimp [qlin]
      have hnum_nonneg : 0 ≤ 2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Cs + Cd := by
        exact add_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) hquad.1.le)
              quad.influenceGain_pos.le)
            hCs_nonneg)
          hCd_nonneg
      exact div_nonneg hnum_nonneg hdlow_pos.le
    have hqtail_nonneg : 0 ≤ qtail := by
      dsimp [qtail]
      have hperiod_nonneg : 0 ≤ (quad.period : ℝ) := by
        exact_mod_cast Nat.zero_le quad.period
      have hsum_nonneg :
          0 ≤ (quad.period : ℝ) + Cs * alpha0 := by
        exact add_nonneg hperiod_nonneg
          (mul_nonneg hCs_nonneg halpha0_pos.le)
      have hnum_nonneg :
          0 ≤ 2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) *
            ((quad.period : ℝ) + Cs * alpha0) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hquad.1.le)
            quad.influenceGain_pos.le)
          hsum_nonneg
      exact div_nonneg hnum_nonneg hdlow_pos.le
    dsimp [C]
    positivity
  · intro alpha halpha_pos halpha_le K hK
    let Gamma : ℝ :=
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
    let S : ℝ :=
      ∑ r : Fin quad.period,
        quadraticScalarWithinPeriodMultiplier (Node := Node)
          quad lambda alpha r.1 ^ 2
    let T : ℝ := ((K * quad.period : ℕ) : ℝ)
    let tail : ℝ := Gamma ^ (2 * K)
    let den : ℝ := 1 - Gamma ^ 2
    have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
    have hK_pos_nat : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
    have hperiod_pos_real : 0 < (quad.period : ℝ) := by
      exact_mod_cast quad.period_pos
    have hT_pos : 0 < T := by
      dsimp [T]
      exact_mod_cast Nat.mul_pos hK_pos_nat quad.period_pos
    have hT_nonneg : 0 ≤ T := le_of_lt hT_pos
    have hT_ne : T ≠ 0 := ne_of_gt hT_pos
    have htail_nonneg : 0 ≤ tail := by
      dsimp [tail]
      have hsq : 0 ≤ Gamma ^ 2 := sq_nonneg Gamma
      simpa [pow_mul] using pow_nonneg hsq K
    have hcommon_alpha := hcommon alpha halpha_pos halpha_le K
    have hden_lower : dlow * alpha ≤ den := by
      simpa [Gamma, den] using hcommon_alpha.1
    have htail_exp : tail ≤ Real.exp (-(c * alpha * T)) := by
      simpa [Gamma, tail, T] using hcommon_alpha.2
    have hden_close_alpha :
        |den - alpha * (2 * lambda * (quad.period : ℝ) *
            (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))| ≤ Cd * alpha ^ 2 := by
      simpa [Gamma, den] using hden_close alpha halpha_pos halpha_le
    have hphase_close_alpha :
        |S - (quad.period : ℝ)| ≤ Cs * alpha := by
      simpa [S] using hphase_close alpha halpha_pos halpha_le
    have hquotient :=
      real_common_scale_quotient_error_bound
        (lambda := lambda) (h := (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
        (p := (quad.period : ℝ)) (alpha := alpha)
        (den := den) (S := S) (tail := tail)
        (dlow := dlow) (Cd := Cd) (Cs := Cs)
        hquad.1 quad.influenceGain_pos hperiod_pos_real halpha_pos
        hdlow_pos hCd_nonneg hCs_nonneg hden_lower
        hden_close_alpha hphase_close_alpha htail_nonneg
    have hqtail_alpha :
        (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) *
            ((quad.period : ℝ) + Cs * alpha)) / dlow ≤ qtail := by
      dsimp [qtail]
      have hsum_le :
          (quad.period : ℝ) + Cs * alpha ≤
            (quad.period : ℝ) + Cs * alpha0 := by
        nlinarith [mul_le_mul_of_nonneg_left halpha_le hCs_nonneg]
      have hcoef_nonneg : 0 ≤ 2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num) hquad.1.le)
          quad.influenceGain_pos.le
      have hmul_le :
          2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) *
              ((quad.period : ℝ) + Cs * alpha) ≤
            2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) *
              ((quad.period : ℝ) + Cs * alpha0) := by
        exact mul_le_mul_of_nonneg_left hsum_le hcoef_nonneg
      exact div_le_div_of_nonneg_right hmul_le hdlow_pos.le
    have hquotient_const :
        |2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * S *
            ((1 - tail) / den) - 1| ≤
          qlin * alpha + qtail * tail := by
      dsimp [qlin]
      exact le_trans hquotient
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hqtail_alpha htail_nonneg))
    have hbias_factor :=
      quadraticScalarBiasBlockAverage_delta_factor
        (Node := Node) quad lambda alpha hquad halpha_ne hK
    have hscale_nonneg :
        0 ≤ quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T) := by
      exact div_nonneg quad.Delta_positive.le
        (mul_nonneg
          (mul_nonneg quad.influenceGain_pos.le (le_of_lt halpha_pos))
          hT_nonneg)
    have hlead_scale :
        |quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)| =
          quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T) := by
      exact abs_of_nonneg hscale_nonneg
    have hdiff_eq :
        quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K -
            quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T) =
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)) *
            (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * S *
                ((1 - tail) / den) - 1) := by
      simpa [S, Gamma, T, tail, den] using hbias_factor
    have hdiff_bound :
        |quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K -
            quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)| ≤
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)) *
            (qlin * alpha + qtail * tail) := by
      rw [hdiff_eq, abs_mul, hlead_scale]
      exact mul_le_mul_of_nonneg_left hquotient_const hscale_nonneg
    have htail_to_exp :
        qtail * tail ≤ qtail * Real.exp (-(c * alpha * T)) := by
      have hqtail_nonneg : 0 ≤ qtail := by
        dsimp [qtail]
        have hperiod_nonneg : 0 ≤ (quad.period : ℝ) := by
          exact_mod_cast Nat.zero_le quad.period
        have hsum_nonneg :
            0 ≤ (quad.period : ℝ) + Cs * alpha0 := by
          exact add_nonneg hperiod_nonneg
            (mul_nonneg hCs_nonneg halpha0_pos.le)
        have hnum_nonneg :
            0 ≤ 2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) *
              ((quad.period : ℝ) + Cs * alpha0) := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) hquad.1.le)
              quad.influenceGain_pos.le)
            hsum_nonneg
        exact div_nonneg hnum_nonneg hdlow_pos.le
      exact mul_le_mul_of_nonneg_left htail_exp hqtail_nonneg
    have hsplit :
        (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)) *
            (qlin * alpha + qtail * tail) ≤
          C * (T⁻¹ + Real.exp (-(c * alpha * T)) / (alpha * T)) := by
      have hDoverH_nonneg : 0 ≤ quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) := by
        exact div_nonneg quad.Delta_positive.le quad.influenceGain_pos.le
      have hqlin_nonneg : 0 ≤ qlin := by
        dsimp [qlin]
        have hnum_nonneg : 0 ≤ 2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * Cs + Cd := by
          exact add_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num) hquad.1.le)
                quad.influenceGain_pos.le)
              hCs_nonneg)
            hCd_nonneg
        exact div_nonneg hnum_nonneg hdlow_pos.le
      have hqtail_nonneg : 0 ≤ qtail := by
        dsimp [qtail]
        have hperiod_nonneg : 0 ≤ (quad.period : ℝ) := by
          exact_mod_cast Nat.zero_le quad.period
        have hsum_nonneg :
            0 ≤ (quad.period : ℝ) + Cs * alpha0 := by
          exact add_nonneg hperiod_nonneg
            (mul_nonneg hCs_nonneg halpha0_pos.le)
        have hnum_nonneg :
            0 ≤ 2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) *
              ((quad.period : ℝ) + Cs * alpha0) := by
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) hquad.1.le)
              quad.influenceGain_pos.le)
            hsum_nonneg
        exact div_nonneg hnum_nonneg hdlow_pos.le
      have hexp_nonneg : 0 ≤ Real.exp (-(c * alpha * T)) :=
        Real.exp_nonneg _
      have hright_nonneg :
          0 ≤ T⁻¹ + Real.exp (-(c * alpha * T)) / (alpha * T) := by
        exact add_nonneg (inv_nonneg.mpr hT_nonneg)
          (div_nonneg hexp_nonneg
            (mul_nonneg (le_of_lt halpha_pos) hT_nonneg))
      have halphaT_ne : alpha * T ≠ 0 := by
        exact mul_ne_zero halpha_ne hT_ne
      have hmain_eq :
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)) *
              (qlin * alpha + qtail * Real.exp (-(c * alpha * T))) =
            (quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))) *
              (qlin * T⁻¹ +
                qtail * (Real.exp (-(c * alpha * T)) / (alpha * T))) := by
        field_simp [ne_of_gt quad.influenceGain_pos, halpha_ne, hT_ne,
          halphaT_ne] <;> ring
      have hreplace_tail :
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)) *
              (qlin * alpha + qtail * tail) ≤
            (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)) *
              (qlin * alpha +
                qtail * Real.exp (-(c * alpha * T))) := by
        have hinner :
            qlin * alpha + qtail * tail ≤
              qlin * alpha + qtail * Real.exp (-(c * alpha * T)) :=
          add_le_add le_rfl htail_to_exp
        exact mul_le_mul_of_nonneg_left hinner hscale_nonneg
      have hcombine :
          (quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))) *
              (qlin * T⁻¹ +
                qtail * (Real.exp (-(c * alpha * T)) / (alpha * T))) ≤
            C * (T⁻¹ +
              Real.exp (-(c * alpha * T)) / (alpha * T)) := by
        dsimp [C]
        have hterm1_nonneg : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_nonneg
        have hterm2_nonneg :
            0 ≤ Real.exp (-(c * alpha * T)) / (alpha * T) :=
          div_nonneg hexp_nonneg
            (mul_nonneg (le_of_lt halpha_pos) hT_nonneg)
        have hinner_combine :
            qlin * T⁻¹ +
                qtail * (Real.exp (-(c * alpha * T)) / (alpha * T)) ≤
              (qlin + qtail) *
                (T⁻¹ + Real.exp (-(c * alpha * T)) / (alpha * T)) := by
          have hcross1 : 0 ≤ qlin *
              (Real.exp (-(c * alpha * T)) / (alpha * T)) :=
            mul_nonneg hqlin_nonneg hterm2_nonneg
          have hcross2 : 0 ≤ qtail * T⁻¹ :=
            mul_nonneg hqtail_nonneg hterm1_nonneg
          nlinarith
        have hscaled :=
          mul_le_mul_of_nonneg_left hinner_combine hDoverH_nonneg
        simpa [C, mul_assoc, mul_left_comm, mul_comm] using hscaled
      exact le_trans hreplace_tail (by
        rw [hmain_eq]
        exact hcombine)
    exact le_trans hdiff_bound hsplit

/-- Appendix C.2 deterministic bias summation for horizons `T = Kp`, after
rewriting `x_0^2` through `Delta`. -/
theorem quadraticScalarBiasBlockAverage_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda) :
    ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ K : ℕ, 1 ≤ K →
          |quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K -
            quad.Delta /
              ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha *
                ((K * quad.period : ℕ) : ℝ))| ≤
          C * ((((K * quad.period : ℕ) : ℝ)⁻¹) +
              Real.exp (-(c * alpha *
                ((K * quad.period : ℕ) : ℝ))) /
                (alpha * ((K * quad.period : ℕ) : ℝ))) := by
  obtain ⟨alphaD, dlow, dup, halphaD_pos, hdlow_pos, hdup_pos,
      hden_bounds⟩ :=
    quadraticScalarPeriodDenominator_smallAlpha_linear_bounds
      (Node := Node) quad lambda hquad
  obtain ⟨alphaG, ctail, halphaG_pos, hctail_pos, htail⟩ :=
    quadraticScalarPeriodMultiplier_power_tail_le_exp
      (Node := Node) quad lambda hquad
  have hdenO :=
    quadraticScalarPeriodDenominator_firstOrder_isBigO_sq
      (Node := Node) quad lambda
  obtain ⟨Cd, hCd_pos, hCd_big⟩ := hdenO.exists_pos
  have hden_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖(1 - quadraticScalarPeriodMultiplier (Node := Node)
              quad lambda alpha ^ 2) -
            alpha * (2 * lambda * (quad.period : ℝ) *
              (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))‖ ≤ Cd * ‖alpha ^ 2‖ := by
    simpa [mul_assoc] using
      (Asymptotics.isBigOWith_iff.mp hCd_big)
  obtain ⟨epsD, hepsD_pos, hden_eps⟩ :=
    Metric.eventually_nhds_iff.mp hden_eventually
  have hwithin_linear :=
    quadraticScalarWithinPeriodSquaredSum_isBigO_linear
      (Node := Node) quad lambda
  obtain ⟨Cs, hCs_pos, hCs_big⟩ := hwithin_linear.exists_pos
  have hphase_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖(∑ r : Fin quad.period,
          quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r.1 ^ 2) -
            (quad.period : ℝ)‖ ≤ Cs * ‖alpha‖ := by
    simpa using
      (Asymptotics.isBigOWith_iff.mp hCs_big)
  obtain ⟨epsS, hepsS_pos, hphase_eps⟩ :=
    Metric.eventually_nhds_iff.mp hphase_eventually
  let alphaCommon : ℝ := min (min alphaD alphaG) (min (epsD / 2) (epsS / 2))
  have halphaCommon_pos : 0 < alphaCommon := by
    dsimp [alphaCommon]
    exact lt_min (lt_min halphaD_pos halphaG_pos)
      (lt_min (half_pos hepsD_pos) (half_pos hepsS_pos))
  have hcommonC :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaCommon →
        ∀ K : ℕ,
          (dlow * alpha ≤
              1 - quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ 2) ∧
            quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ (2 * K) ≤
              Real.exp (-(ctail * alpha *
                ((K * quad.period : ℕ) : ℝ))) := by
    intro alpha halpha_pos halpha_le K
    have halpha_leD : alpha ≤ alphaD :=
      le_trans halpha_le (le_trans (min_le_left _ _) (min_le_left _ _))
    have halpha_leG : alpha ≤ alphaG :=
      le_trans halpha_le (le_trans (min_le_left _ _) (min_le_right _ _))
    exact ⟨(hden_bounds alpha halpha_pos halpha_leD).1,
      htail alpha halpha_pos halpha_leG K⟩
  have hden_close :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaCommon →
        |(1 - quadraticScalarPeriodMultiplier (Node := Node)
            quad lambda alpha ^ 2) -
          alpha * (2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))| ≤
            Cd * alpha ^ 2 := by
    intro alpha halpha_pos halpha_le
    have halpha_le_epsD : alpha ≤ epsD := by
      have hhalf : alpha ≤ epsD / 2 :=
        le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
      nlinarith [hepsD_pos]
    have halpha_lt_epsD : alpha < epsD := by
      have hhalf : alpha ≤ epsD / 2 :=
        le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
      nlinarith [hepsD_pos]
    have hdist : dist alpha 0 < epsD := by
      simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_epsD
    have hraw := hden_eps hdist
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg alpha)] using hraw
  have hphase_close :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaCommon →
        |(∑ r : Fin quad.period,
          quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r.1 ^ 2) -
            (quad.period : ℝ)| ≤ Cs * alpha := by
    intro alpha halpha_pos halpha_le
    have halpha_le_epsS : alpha ≤ epsS := by
      have hhalf : alpha ≤ epsS / 2 :=
        le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
      nlinarith [hepsS_pos]
    have halpha_lt_epsS : alpha < epsS := by
      have hhalf : alpha ≤ epsS / 2 :=
        le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
      nlinarith [hepsS_pos]
    have hdist : dist alpha 0 < epsS := by
      simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_epsS
    have hraw := hphase_eps hdist
    simpa [Real.norm_eq_abs, abs_of_pos halpha_pos] using hraw
  exact quadraticScalarBiasBlockAverage_bound_from_common_scale
    (Node := Node) quad lambda hquad alphaCommon ctail dlow Cd Cs
    halphaCommon_pos hctail_pos hdlow_pos hCd_pos.le hCs_pos.le
    hcommonC
    hden_close hphase_close

/-- Real asymptotic division primitive used by Appendix C.2 steady-state
variance: if a numerator is `alpha^2 * B + O(alpha^3)` and a denominator is
`alpha * d + O(alpha^2)` with `d > 0`, their quotient is
`alpha * B / d + O(alpha^2)`. -/
theorem real_quadratic_over_linear_isBigO_sq
    {N D : ℝ → ℝ} {B d : ℝ} (hd_pos : 0 < d)
    (hnum :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ => N alpha - alpha ^ 2 * B)
        (fun alpha : ℝ => alpha ^ 3))
    (hden :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ => D alpha - alpha * d)
        (fun alpha : ℝ => alpha ^ 2)) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ => N alpha / D alpha - alpha * B / d)
      (fun alpha : ℝ => alpha ^ 2) := by
  exact Asymptotics.isBigO_quadratic_div_linear_sub_linear
    hd_pos hnum hden

/-- Appendix C.2 steady boundary variance expansion obtained by dividing the
block innovation second moment by `1-Gamma(alpha)^2`. -/
theorem quadraticScalarSteadyBoundaryVariance_expansion
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hblock :
      ∀ k : ℕ,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k -
              alpha ^ 2 * quad.sigma ^ 2 *
                (quad.period : ℝ) * quad.influenceSecondMoment)
          (fun alpha : ℝ => alpha ^ 3)) :
    ∀ k : ℕ,
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k) -
            (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))))
        (fun alpha : ℝ => alpha ^ 2) := by
  intro k
  have hdenO :=
    quadraticScalarPeriodDenominator_firstOrder_isBigO_sq
      (Node := Node) quad lambda
  have hdenCoeff_pos :=
    quadraticScalarPeriodDenominator_linearCoefficient_pos
      (Node := Node) quad lambda hquad
  have hblock_k := hblock k
  let B : ℝ :=
    quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment
  let d : ℝ := 2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))
  have hdivision :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          quadraticScalarBlockInnovationSecondMoment (Node := Node)
              quad lambda alpha μ oracle k /
            (1 - quadraticScalarPeriodMultiplier (Node := Node)
              quad lambda alpha ^ 2) -
            alpha * B / d)
        (fun alpha : ℝ => alpha ^ 2) := by
    refine real_quadratic_over_linear_isBigO_sq
      (N := fun alpha : ℝ =>
        quadraticScalarBlockInnovationSecondMoment (Node := Node)
          quad lambda alpha μ oracle k)
      (D := fun alpha : ℝ =>
        1 - quadraticScalarPeriodMultiplier (Node := Node)
          quad lambda alpha ^ 2)
      (B := B) (d := d) ?_ ?_ ?_
    · simpa [d, mul_assoc] using hdenCoeff_pos
    · simpa [B, mul_assoc] using hblock_k
    · simpa [d, mul_assoc] using hdenO
  refine hdivision.congr ?_ ?_
  · intro alpha
    unfold quadraticScalarSteadyBoundaryVariance
    simp [B, d]
    have hperiod_ne : ((quad.period : ℝ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt quad.period_pos)
    field_simp [hperiod_ne]
  · intro alpha
    rfl

/-- Uniform version of the Appendix C.2 periodic steady boundary variance
expansion.  The complete-period average needs one small-stepsize radius and
one constant valid for every block; this is obtained from the uniform block
innovation expansion and the period-denominator lower bound. -/
theorem quadraticScalarSteadyBoundaryVariance_expansion_uniform
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hblock_uniform :
      ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, |alpha| < alpha0 →
          ∀ k : ℕ,
            |quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k -
              alpha ^ 2 * quad.sigma ^ 2 *
                (quad.period : ℝ) * quad.influenceSecondMoment| ≤
            C * |alpha| ^ 3) :
    ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ k : ℕ,
          |quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k) -
            (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))))| ≤
          C * alpha ^ 2 := by
  classical
  obtain ⟨alphaN, Cn, halphaN_pos, hCn_nonneg, hnum⟩ := hblock_uniform
  obtain ⟨alphaD, dlow, _dup, halphaD_pos, hdlow_pos, _hdup_pos,
      hden_bounds⟩ :=
    quadraticScalarPeriodDenominator_smallAlpha_linear_bounds
      (Node := Node) quad lambda hquad
  have hdenO :=
    quadraticScalarPeriodDenominator_firstOrder_isBigO_sq
      (Node := Node) quad lambda
  obtain ⟨Cd, hCd_pos, hCd_big⟩ := hdenO.exists_pos
  have hden_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖(1 - quadraticScalarPeriodMultiplier (Node := Node)
              quad lambda alpha ^ 2) -
            alpha * (2 * lambda * (quad.period : ℝ) *
              (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))‖ ≤ Cd * ‖alpha ^ 2‖ := by
    simpa [mul_assoc] using
      (Asymptotics.isBigOWith_iff.mp hCd_big)
  obtain ⟨epsD, hepsD_pos, hden_eps⟩ :=
    Metric.eventually_nhds_iff.mp hden_eventually
  let B : ℝ :=
    quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment
  let d : ℝ := 2 * lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))
  let alpha0 : ℝ := min (alphaN / 2) (min alphaD (epsD / 2))
  let C : ℝ := (d * Cn + |B| * Cd) / (d * dlow)
  have hd_pos : 0 < d := by
    dsimp [d]
    exact quadraticScalarPeriodDenominator_linearCoefficient_pos
      (Node := Node) quad lambda hquad
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min (half_pos halphaN_pos)
      (lt_min halphaD_pos (half_pos hepsD_pos))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    have hnum_nonneg : 0 ≤ d * Cn + |B| * Cd :=
      add_nonneg (mul_nonneg hd_pos.le hCn_nonneg)
        (mul_nonneg (abs_nonneg B) hCd_pos.le)
    exact div_nonneg hnum_nonneg
      (mul_nonneg hd_pos.le hdlow_pos.le)
  refine ⟨alpha0, C, halpha0_pos, hC_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le k
  let N : ℝ :=
    quadraticScalarBlockInnovationSecondMoment (Node := Node)
      quad lambda alpha μ oracle k
  let D : ℝ :=
    1 - quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha ^ 2
  have halpha_lt_alphaN : alpha < alphaN := by
    have hhalf : alpha ≤ alphaN / 2 :=
      le_trans halpha_le (min_le_left _ _)
    nlinarith [halphaN_pos]
  have hnum_bound :
      |N - alpha ^ 2 * B| ≤ Cn * alpha ^ 3 := by
    have habs : |alpha| < alphaN := by
      simpa [abs_of_pos halpha_pos] using halpha_lt_alphaN
    simpa [N, B, abs_of_pos halpha_pos, mul_assoc, mul_left_comm,
      mul_comm] using hnum alpha habs k
  have halpha_le_alphaD : alpha ≤ alphaD :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hD_lower : dlow * alpha ≤ D := by
    simpa [D] using
      (hden_bounds alpha halpha_pos halpha_le_alphaD).1
  have halpha_lt_epsD : alpha < epsD := by
    have hhalf : alpha ≤ epsD / 2 :=
      le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
    nlinarith [hepsD_pos]
  have hdist : dist alpha 0 < epsD := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_epsD
  have hden_close :
      |D - alpha * d| ≤ Cd * alpha ^ 2 := by
    have hraw := hden_eps hdist
    simpa [D, d, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg alpha)]
      using hraw
  have hquot_bound :
      |N / D - alpha * B / d| ≤ C * alpha ^ 2 := by
    simpa [C] using
      (abs_quadratic_div_linear_sub_linear_le
        halpha_pos hd_pos hdlow_pos hnum_bound hD_lower hden_close)
  have hlead_eq :
      alpha * B / d =
        alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
          (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))) := by
    dsimp [B, d]
    have hperiod_ne : ((quad.period : ℝ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt quad.period_pos)
    field_simp [hperiod_ne]
  simpa [quadraticScalarSteadyBoundaryVariance, N, D, hlead_eq] using hquot_bound

/-- Source bridge from the exact stochastic block recursion to the canonical
zero-initial variance AR formula used in Appendix C.2 after the deterministic
bias has been removed.  This keeps the complete-period variance supplier on the
paper's `v_{k+1}=Gamma(alpha)^2 v_k+E|eta_k|^2` object rather than on the full
second moment with the bias term still mixed in. -/
theorem quadraticScalarBlockBoundaryVariance_formula_from_source
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∀ alpha : ℝ, ∀ K : ℕ,
      quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle K =
        quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
          quad lambda alpha μ oracle K := by
  intro alpha K
  exact quadraticScalarBlockBoundaryVariance_closed_form
    (Node := Node) quad lambda alpha μ oracle
    (quadraticScalarBlockBoundaryVariance_recursion
      (Node := Node) quad lambda alpha μ oracle hnoise) K

/-- Scalar AR transient bound used by Appendix C.2.  For the zero-initial
recursion with constant innovation `N` and contraction `q`, the total distance
from the steady value is bounded by the infinite geometric mass. -/
theorem real_ar_const_zero_transient_sum_abs_le
    {q N : ℝ} (K : ℕ) (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) :
    (Finset.range K).sum (fun k =>
        |N * ((1 - q ^ k) / (1 - q)) - N / (1 - q)|) ≤
      |N| / (1 - q) ^ 2 := by
  exact sum_abs_const_affine_zero_transient_le K hq_nonneg hq_lt_one

/-- The zero-initial block-boundary variance has only `O(T^{-1})` total gap
to the periodic steady boundary variance after averaging over `K` complete
periods.  This proves the AR transient half of Appendix C.2 step 6 from the
canonical block-boundary variance formula, the exact block-noise periodicity,
and the small-stepsize denominator lower bound. -/
theorem quadraticScalarBlockBoundaryVariance_to_steadyAverage_transient_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hvariance_formula :
      ∀ alpha : ℝ, ∀ K : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle K =
          quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle K) :
    ∃ alpha0 Ctransient : ℝ,
      0 < alpha0 ∧ 0 ≤ Ctransient ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            let T : ℝ := ((K * quad.period : ℕ) : ℝ)
            let boundaryAverage : ℝ :=
              lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarBlockBoundaryVariance (Node := Node)
                    quad lambda alpha μ oracle k)
            let steadyAverage : ℝ :=
              lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarSteadyBoundaryVariance (Node := Node)
                    quad lambda alpha
                    (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                      quad lambda alpha μ oracle k))
            |boundaryAverage - steadyAverage| ≤ Ctransient * T⁻¹ := by
  classical
  obtain ⟨alphaN, Cn, halphaN_pos, hCn_nonneg, hnum⟩ :=
    quadraticScalarBlockInnovationSecondMoment_expansion_uniform
      (Node := Node) quad lambda μ oracle hnoise
  obtain ⟨alphaD, dlow, _dup, halphaD_pos, hdlow_pos, _hdup_pos,
      hden_bounds⟩ :=
    quadraticScalarPeriodDenominator_smallAlpha_linear_bounds
      (Node := Node) quad lambda hquad
  let B : ℝ :=
    quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment
  let alpha0 : ℝ := min (alphaN / 2) (min alphaD 1)
  let Ctransient : ℝ :=
    lambda ^ 2 * (quad.period : ℝ) * (Cn + |B|) / dlow ^ 2
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min (half_pos halphaN_pos)
      (lt_min halphaD_pos zero_lt_one)
  have hperiod_pos : 0 < (quad.period : ℝ) := by
    exact_mod_cast quad.period_pos
  have hCtransient_nonneg : 0 ≤ Ctransient := by
    dsimp [Ctransient]
    have hsum_nonneg : 0 ≤ Cn + |B| :=
      add_nonneg hCn_nonneg (abs_nonneg B)
    positivity
  refine ⟨alpha0, Ctransient, halpha0_pos, hCtransient_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let G : ℝ := quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
  let q : ℝ := G ^ 2
  let D : ℝ := 1 - q
  let N : ℝ :=
    quadraticScalarBlockInnovationSecondMoment (Node := Node)
      quad lambda alpha μ oracle 0
  let S : ℝ := N / D
  let T : ℝ := ((K * quad.period : ℕ) : ℝ)
  let boundaryAverage : ℝ :=
    lambda ^ 2 * (K : ℝ)⁻¹ *
      ((Finset.range K).sum fun k =>
        quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle k)
  let steadyAverage : ℝ :=
    lambda ^ 2 * (K : ℝ)⁻¹ *
      ((Finset.range K).sum fun k =>
        quadraticScalarSteadyBoundaryVariance (Node := Node)
          quad lambda alpha
          (quadraticScalarBlockInnovationSecondMoment (Node := Node)
            quad lambda alpha μ oracle k))
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_halfN : alpha ≤ alphaN / 2 :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_lt_alphaN : alpha < alphaN := by nlinarith [halphaN_pos]
  have halpha_le_alphaD : alpha ≤ alphaD :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have halpha_le_one : alpha ≤ 1 :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hD_lower : dlow * alpha ≤ D := by
    simpa [D, q, G] using
      (hden_bounds alpha halpha_pos halpha_le_alphaD).1
  have hD_pos : 0 < D :=
    lt_of_lt_of_le (mul_pos hdlow_pos halpha_pos) hD_lower
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hq_nonneg : 0 ≤ q := by dsimp [q]; exact sq_nonneg G
  have hq_lt_one : q < 1 := by
    dsimp [D] at hD_pos
    linarith
  have hN_bound :
      |N| ≤ (Cn + |B|) * alpha ^ 2 := by
    have hnum0 :
        |N - alpha ^ 2 * B| ≤ Cn * alpha ^ 3 := by
      have habs : |alpha| < alphaN := by
        simpa [abs_of_pos halpha_pos] using halpha_lt_alphaN
      simpa [N, B, abs_of_pos halpha_pos, mul_assoc, mul_left_comm,
        mul_comm] using hnum alpha habs 0
    calc
      |N| = |(N - alpha ^ 2 * B) + alpha ^ 2 * B| := by ring_nf
      _ ≤ |N - alpha ^ 2 * B| + |alpha ^ 2 * B| := abs_add_le _ _
      _ ≤ Cn * alpha ^ 3 + |B| * alpha ^ 2 := by
        refine add_le_add hnum0 ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg alpha), mul_comm]
      _ ≤ Cn * alpha ^ 2 + |B| * alpha ^ 2 := by
        refine add_le_add ?_ le_rfl
        have halpha_sq_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
        have hcube_le_sq : alpha ^ 3 ≤ alpha ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left halpha_le_one halpha_sq_nonneg]
        exact mul_le_mul_of_nonneg_left hcube_le_sq hCn_nonneg
      _ = (Cn + |B|) * alpha ^ 2 := by ring
  have hAR_formula :
      ∀ k : ℕ,
        quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle k =
          S * (1 - q ^ k) := by
    intro k
    induction k with
    | zero =>
        simp [quadraticScalarBlockBoundaryVarianceARFormula, S]
    | succ k ih =>
        have hNk :
            quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k = N := by
          simpa [N] using
            quadraticScalarBlockInnovationSecondMoment_eq_zeroBlock
              (Node := Node) quad lambda alpha μ oracle hnoise k
        have hN_eq : N = S * D := by
          dsimp [S]
          field_simp [hD_ne]
        simp [quadraticScalarBlockBoundaryVarianceARFormula, G, q, hNk, ih,
          hN_eq, D]
        rw [pow_succ]
        ring
  have hsteady_eq (k : ℕ) :
      quadraticScalarSteadyBoundaryVariance (Node := Node)
          quad lambda alpha
          (quadraticScalarBlockInnovationSecondMoment (Node := Node)
            quad lambda alpha μ oracle k) = S := by
    have hNk :
        quadraticScalarBlockInnovationSecondMoment (Node := Node)
            quad lambda alpha μ oracle k = N := by
      simpa [N] using
        quadraticScalarBlockInnovationSecondMoment_eq_zeroBlock
          (Node := Node) quad lambda alpha μ oracle hnoise k
    unfold quadraticScalarSteadyBoundaryVariance
    simp [hNk, S, D, q, G]
  have hsum_abs :
      |(Finset.range K).sum fun k =>
          quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle k -
            quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k)| ≤
        |N| / D ^ 2 := by
    have hterm_le (k : ℕ) (_hk : k ∈ Finset.range K) :
        |quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle k -
            quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k)| ≤
          |N * ((1 - q ^ k) / D) - N / D| := by
      rw [hvariance_formula alpha k, hAR_formula k, hsteady_eq k]
      have hS_eq : S = N / D := rfl
      rw [hS_eq]
      have hleft :
          N / D * (1 - q ^ k) - N / D =
            N * ((1 - q ^ k) / D) - N / D := by ring
      rw [hleft]
    calc
      |(Finset.range K).sum fun k =>
          quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle k -
            quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k)| ≤
          (Finset.range K).sum fun k =>
            |quadraticScalarBlockBoundaryVariance (Node := Node)
                quad lambda alpha μ oracle k -
              quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.range K).sum fun k =>
            |N * ((1 - q ^ k) / D) - N / D| := by
          exact Finset.sum_le_sum hterm_le
      _ ≤ |N| / D ^ 2 := by
          simpa [D] using
            real_ar_const_zero_transient_sum_abs_le
              (K := K) (q := q) (N := N) hq_nonneg hq_lt_one
  have hD_sq_lower :
      dlow ^ 2 * alpha ^ 2 ≤ D ^ 2 := by
    have hleft_nonneg : 0 ≤ dlow * alpha :=
      mul_nonneg hdlow_pos.le halpha_nonneg
    have hsq := mul_le_mul hD_lower hD_lower hleft_nonneg hD_nonneg
    nlinarith
  have hquot_bound :
      |N| / D ^ 2 ≤ (Cn + |B|) / dlow ^ 2 := by
    have hden_sq_pos : 0 < D ^ 2 := sq_pos_of_ne_zero hD_ne
    have hdlow_sq_pos : 0 < dlow ^ 2 := sq_pos_of_ne_zero (ne_of_gt hdlow_pos)
    have halpha_sq_pos : 0 < alpha ^ 2 := sq_pos_of_ne_zero (ne_of_gt halpha_pos)
    have hdiv_den :
        |N| / D ^ 2 ≤ |N| / (dlow ^ 2 * alpha ^ 2) :=
      div_le_div_of_nonneg_left (abs_nonneg N)
        (mul_pos hdlow_sq_pos halpha_sq_pos) hD_sq_lower
    have hdiv_num :
        |N| / (dlow ^ 2 * alpha ^ 2) ≤
          ((Cn + |B|) * alpha ^ 2) / (dlow ^ 2 * alpha ^ 2) :=
      div_le_div_of_nonneg_right hN_bound
        (mul_nonneg hdlow_sq_pos.le (sq_nonneg alpha))
    have hcancel :
        ((Cn + |B|) * alpha ^ 2) / (dlow ^ 2 * alpha ^ 2) =
          (Cn + |B|) / dlow ^ 2 := by
      field_simp [ne_of_gt hdlow_sq_pos, ne_of_gt halpha_sq_pos]
    exact le_trans hdiv_den (le_trans hdiv_num (le_of_eq hcancel))
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK_pos)
  have hT_pos : 0 < T := by
    dsimp [T]
    exact_mod_cast Nat.mul_pos hK_pos quad.period_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have havg_eq :
      boundaryAverage - steadyAverage =
        lambda ^ 2 * (K : ℝ)⁻¹ *
          ((Finset.range K).sum fun k =>
            quadraticScalarBlockBoundaryVariance (Node := Node)
                quad lambda alpha μ oracle k -
              quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k)) := by
    dsimp [boundaryAverage, steadyAverage]
    rw [← mul_sub]
    rw [← Finset.sum_sub_distrib]
  have hscaled :
      |boundaryAverage - steadyAverage| ≤
        lambda ^ 2 * (K : ℝ)⁻¹ * ((Cn + |B|) / dlow ^ 2) := by
    rw [havg_eq, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg lambda),
      abs_of_nonneg (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le K))]
    exact mul_le_mul_of_nonneg_left
      (le_trans hsum_abs hquot_bound)
      (mul_nonneg (sq_nonneg lambda)
        (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le K)))
  have htarget_eq :
      lambda ^ 2 * (K : ℝ)⁻¹ * ((Cn + |B|) / dlow ^ 2) =
        Ctransient * T⁻¹ := by
    dsimp [Ctransient, T]
    rw [Nat.cast_mul]
    field_simp [hK_ne, ne_of_gt hperiod_pos]
  exact le_trans hscaled (le_of_eq htarget_eq)

/-- Uniform `O(alpha)` bound for the zero-initial block-boundary variance
average.  This is the deterministic half of the Appendix C.2 finite-phase
residue estimate: the finite-phase multiplier error is `O(alpha)`, while the
averaged boundary variance itself is `O(alpha)`. -/
theorem quadraticScalarBlockBoundaryVariance_average_linear_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hvariance_formula :
      ∀ alpha : ℝ, ∀ K : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle K =
          quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle K) :
    ∃ alpha0 M : ℝ,
      0 < alpha0 ∧ 0 ≤ M ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            |lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarBlockBoundaryVariance (Node := Node)
                    quad lambda alpha μ oracle k)| ≤
              M * alpha := by
  classical
  obtain ⟨alphaN, Cn, halphaN_pos, hCn_nonneg, hnum⟩ :=
    quadraticScalarBlockInnovationSecondMoment_expansion_uniform
      (Node := Node) quad lambda μ oracle hnoise
  obtain ⟨alphaD, dlow, _dup, halphaD_pos, hdlow_pos, _hdup_pos,
      hden_bounds⟩ :=
    quadraticScalarPeriodDenominator_smallAlpha_linear_bounds
      (Node := Node) quad lambda hquad
  let B : ℝ :=
    quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment
  let alpha0 : ℝ := min (alphaN / 2) (min alphaD 1)
  let M : ℝ := lambda ^ 2 * ((Cn + |B|) / dlow)
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min (half_pos halphaN_pos)
      (lt_min halphaD_pos zero_lt_one)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    have hsum_nonneg : 0 ≤ Cn + |B| :=
      add_nonneg hCn_nonneg (abs_nonneg B)
    exact mul_nonneg (sq_nonneg lambda)
      (div_nonneg hsum_nonneg hdlow_pos.le)
  refine ⟨alpha0, M, halpha0_pos, hM_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let G : ℝ := quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
  let q : ℝ := G ^ 2
  let D : ℝ := 1 - q
  let N : ℝ :=
    quadraticScalarBlockInnovationSecondMoment (Node := Node)
      quad lambda alpha μ oracle 0
  let S : ℝ := N / D
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_halfN : alpha ≤ alphaN / 2 :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_lt_alphaN : alpha < alphaN := by nlinarith [halphaN_pos]
  have halpha_le_alphaD : alpha ≤ alphaD :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have halpha_le_one : alpha ≤ 1 :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hD_lower : dlow * alpha ≤ D := by
    simpa [D, q, G] using
      (hden_bounds alpha halpha_pos halpha_le_alphaD).1
  have hD_pos : 0 < D :=
    lt_of_lt_of_le (mul_pos hdlow_pos halpha_pos) hD_lower
  have hD_nonneg : 0 ≤ D := le_of_lt hD_pos
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hq_nonneg : 0 ≤ q := by dsimp [q]; exact sq_nonneg G
  have hq_lt_one : q < 1 := by
    dsimp [D] at hD_pos
    linarith
  have hN_bound :
      |N| ≤ (Cn + |B|) * alpha ^ 2 := by
    have hnum0 :
        |N - alpha ^ 2 * B| ≤ Cn * alpha ^ 3 := by
      have habs : |alpha| < alphaN := by
        simpa [abs_of_pos halpha_pos] using halpha_lt_alphaN
      simpa [N, B, abs_of_pos halpha_pos, mul_assoc, mul_left_comm,
        mul_comm] using hnum alpha habs 0
    calc
      |N| = |(N - alpha ^ 2 * B) + alpha ^ 2 * B| := by ring_nf
      _ ≤ |N - alpha ^ 2 * B| + |alpha ^ 2 * B| := abs_add_le _ _
      _ ≤ Cn * alpha ^ 3 + |B| * alpha ^ 2 := by
        refine add_le_add hnum0 ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg alpha), mul_comm]
      _ ≤ Cn * alpha ^ 2 + |B| * alpha ^ 2 := by
        refine add_le_add ?_ le_rfl
        have halpha_sq_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
        have hcube_le_sq : alpha ^ 3 ≤ alpha ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left halpha_le_one halpha_sq_nonneg]
        exact mul_le_mul_of_nonneg_left hcube_le_sq hCn_nonneg
      _ = (Cn + |B|) * alpha ^ 2 := by ring
  have hAR_formula :
      ∀ k : ℕ,
        quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle k =
          S * (1 - q ^ k) := by
    intro k
    induction k with
    | zero =>
        simp [quadraticScalarBlockBoundaryVarianceARFormula, S]
    | succ k ih =>
        have hNk :
            quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k = N := by
          simpa [N] using
            quadraticScalarBlockInnovationSecondMoment_eq_zeroBlock
              (Node := Node) quad lambda alpha μ oracle hnoise k
        have hN_eq : N = S * D := by
          dsimp [S]
          field_simp [hD_ne]
        simp [quadraticScalarBlockBoundaryVarianceARFormula, G, q, hNk, ih,
          hN_eq, D]
        rw [pow_succ]
        ring
  have hterm_abs (k : ℕ) (_hk : k ∈ Finset.range K) :
      |quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle k| ≤ |S| := by
    rw [hvariance_formula alpha k, hAR_formula k, abs_mul]
    have hqpow_le_one : q ^ k ≤ 1 :=
      pow_le_one₀ (n := k) hq_nonneg (le_of_lt hq_lt_one)
    have hqpow_nonneg : 0 ≤ q ^ k := pow_nonneg hq_nonneg k
    have hfactor_abs : |1 - q ^ k| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hqpow_le_one)]
      nlinarith
    exact mul_le_of_le_one_right (abs_nonneg S) hfactor_abs
  have hsum_abs :
      |(Finset.range K).sum fun k =>
          quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle k| ≤
        (K : ℝ) * |S| := by
    calc
      |(Finset.range K).sum fun k =>
          quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle k| ≤
          (Finset.range K).sum fun k =>
            |quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.range K).sum fun _k => |S| := by
        exact Finset.sum_le_sum hterm_abs
      _ = (K : ℝ) * |S| := by simp
  have hS_bound :
      |S| ≤ ((Cn + |B|) / dlow) * alpha := by
    have hden_lower_pos : 0 < dlow * alpha :=
      mul_pos hdlow_pos halpha_pos
    have hdiv_den :
        |N| / D ≤ |N| / (dlow * alpha) :=
      div_le_div_of_nonneg_left (abs_nonneg N) hden_lower_pos hD_lower
    have hdiv_num :
        |N| / (dlow * alpha) ≤
          ((Cn + |B|) * alpha ^ 2) / (dlow * alpha) :=
      div_le_div_of_nonneg_right hN_bound hden_lower_pos.le
    have hcancel :
        ((Cn + |B|) * alpha ^ 2) / (dlow * alpha) =
          ((Cn + |B|) / dlow) * alpha := by
      field_simp [ne_of_gt hdlow_pos, ne_of_gt halpha_pos]
    calc
      |S| = |N| / D := by
        dsimp [S]
        rw [abs_div, abs_of_pos hD_pos]
      _ ≤ |N| / (dlow * alpha) := hdiv_den
      _ ≤ ((Cn + |B|) * alpha ^ 2) / (dlow * alpha) := hdiv_num
      _ = ((Cn + |B|) / dlow) * alpha := hcancel
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK_pos)
  have hK_nonneg : 0 ≤ (K : ℝ) := by exact_mod_cast Nat.zero_le K
  have hscale_nonneg : 0 ≤ lambda ^ 2 * (K : ℝ)⁻¹ :=
    mul_nonneg (sq_nonneg lambda) (inv_nonneg.mpr hK_nonneg)
  calc
    |lambda ^ 2 * (K : ℝ)⁻¹ *
        ((Finset.range K).sum fun k =>
          quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle k)| =
        lambda ^ 2 * (K : ℝ)⁻¹ *
          |(Finset.range K).sum fun k =>
            quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle k| := by
      rw [abs_mul, abs_of_nonneg hscale_nonneg]
    _ ≤ lambda ^ 2 * (K : ℝ)⁻¹ * ((K : ℝ) * |S|) :=
      mul_le_mul_of_nonneg_left hsum_abs hscale_nonneg
    _ = lambda ^ 2 * |S| := by
      field_simp [hK_ne]
    _ ≤ lambda ^ 2 * (((Cn + |B|) / dlow) * alpha) :=
      mul_le_mul_of_nonneg_left hS_bound (sq_nonneg lambda)
    _ = M * alpha := by
      dsimp [M]
      ring

/-- Uniform bound for the scalar comparison process at period boundaries.

The source scalar AR second-moment formula splits the boundary moment into a
zero-initial variance term and a deterministic geometric bias.  For small
positive stepsizes, the variance term is uniformly bounded by the same
denominator/innovation comparison used in Appendix C.2, while the bias term is
bounded by `x0^2` because the scalar period multiplier is contractive. -/
theorem quadraticScalarBlockBoundarySecondMoment_uniform_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ alpha0 Cscalar : ℝ,
      0 < alpha0 ∧ 0 ≤ Cscalar ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ k : ℕ,
            quadraticScalarBlockBoundarySecondMoment (Node := Node)
              quad lambda alpha μ oracle k ≤ Cscalar := by
  classical
  obtain ⟨alphaN, Cn, halphaN_pos, hCn_nonneg, hnum⟩ :=
    quadraticScalarBlockInnovationSecondMoment_expansion_uniform
      (Node := Node) quad lambda μ oracle hnoise
  obtain ⟨alphaD, dlow, _dup, halphaD_pos, hdlow_pos, _hdup_pos,
      hden_bounds⟩ :=
    quadraticScalarPeriodDenominator_smallAlpha_linear_bounds
      (Node := Node) quad lambda hquad
  let B : ℝ :=
    quad.sigma ^ 2 * (quad.period : ℝ) * quad.influenceSecondMoment
  let alpha0 : ℝ := min (alphaN / 2) (min alphaD 1)
  let Cvar : ℝ := (Cn + |B|) / dlow
  let Cscalar : ℝ := Cvar + quad.x0 ^ 2
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min (half_pos halphaN_pos)
      (lt_min halphaD_pos zero_lt_one)
  have hCvar_nonneg : 0 ≤ Cvar := by
    dsimp [Cvar]
    exact div_nonneg (add_nonneg hCn_nonneg (abs_nonneg B))
      hdlow_pos.le
  have hCscalar_nonneg : 0 ≤ Cscalar := by
    dsimp [Cscalar]
    exact add_nonneg hCvar_nonneg (sq_nonneg quad.x0)
  refine ⟨alpha0, Cscalar, halpha0_pos, hCscalar_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le k
  let G : ℝ := quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
  let q : ℝ := G ^ 2
  let D : ℝ := 1 - q
  let N : ℝ :=
    quadraticScalarBlockInnovationSecondMoment (Node := Node)
      quad lambda alpha μ oracle 0
  let S : ℝ := N / D
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_halfN : alpha ≤ alphaN / 2 :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_lt_alphaN : alpha < alphaN := by nlinarith [halphaN_pos]
  have halpha_le_alphaD : alpha ≤ alphaD :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have halpha_le_one : alpha ≤ 1 :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hD_lower : dlow * alpha ≤ D := by
    simpa [D, q, G] using
      (hden_bounds alpha halpha_pos halpha_le_alphaD).1
  have hD_pos : 0 < D :=
    lt_of_lt_of_le (mul_pos hdlow_pos halpha_pos) hD_lower
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact sq_nonneg G
  have hq_lt_one : q < 1 := by
    dsimp [D] at hD_pos
    linarith
  have hN_bound :
      |N| ≤ (Cn + |B|) * alpha ^ 2 := by
    have hnum0 :
        |N - alpha ^ 2 * B| ≤ Cn * alpha ^ 3 := by
      have habs : |alpha| < alphaN := by
        simpa [abs_of_pos halpha_pos] using halpha_lt_alphaN
      simpa [N, B, abs_of_pos halpha_pos, mul_assoc, mul_left_comm,
        mul_comm] using hnum alpha habs 0
    calc
      |N| = |(N - alpha ^ 2 * B) + alpha ^ 2 * B| := by ring_nf
      _ ≤ |N - alpha ^ 2 * B| + |alpha ^ 2 * B| := abs_add_le _ _
      _ ≤ Cn * alpha ^ 3 + |B| * alpha ^ 2 := by
        refine add_le_add hnum0 ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg alpha), mul_comm]
      _ ≤ Cn * alpha ^ 2 + |B| * alpha ^ 2 := by
        refine add_le_add ?_ le_rfl
        have halpha_sq_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
        have hcube_le_sq : alpha ^ 3 ≤ alpha ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left halpha_le_one halpha_sq_nonneg]
        exact mul_le_mul_of_nonneg_left hcube_le_sq hCn_nonneg
      _ = (Cn + |B|) * alpha ^ 2 := by ring
  have hS_bound :
      |S| ≤ Cvar := by
    have hden_lower_pos : 0 < dlow * alpha :=
      mul_pos hdlow_pos halpha_pos
    have hdiv_den :
        |N| / D ≤ |N| / (dlow * alpha) :=
      div_le_div_of_nonneg_left (abs_nonneg N) hden_lower_pos hD_lower
    have hdiv_num :
        |N| / (dlow * alpha) ≤
          ((Cn + |B|) * alpha ^ 2) / (dlow * alpha) :=
      div_le_div_of_nonneg_right hN_bound hden_lower_pos.le
    have hcancel :
        ((Cn + |B|) * alpha ^ 2) / (dlow * alpha) =
          ((Cn + |B|) / dlow) * alpha := by
      field_simp [ne_of_gt hdlow_pos, ne_of_gt halpha_pos]
    have halpha_scale :
        ((Cn + |B|) / dlow) * alpha ≤ Cvar := by
      dsimp [Cvar]
      exact mul_le_of_le_one_right hCvar_nonneg halpha_le_one
    calc
      |S| = |N| / D := by
        dsimp [S]
        rw [abs_div, abs_of_pos hD_pos]
      _ ≤ |N| / (dlow * alpha) := hdiv_den
      _ ≤ ((Cn + |B|) * alpha ^ 2) / (dlow * alpha) := hdiv_num
      _ = ((Cn + |B|) / dlow) * alpha := hcancel
      _ ≤ Cvar := halpha_scale
  have hAR_formula :
      quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
          quad lambda alpha μ oracle k =
        S * (1 - q ^ k) := by
    induction k with
    | zero =>
        simp [quadraticScalarBlockBoundaryVarianceARFormula, S]
    | succ k ih =>
        have hNk :
            quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k = N := by
          simpa [N] using
            quadraticScalarBlockInnovationSecondMoment_eq_zeroBlock
              (Node := Node) quad lambda alpha μ oracle hnoise k
        have hN_eq : N = S * D := by
          dsimp [S]
          field_simp [hD_ne]
        simp [quadraticScalarBlockBoundaryVarianceARFormula, G, q, hNk, ih,
          hN_eq, D]
        rw [pow_succ]
        ring
  have hvariance_formula :
      quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle k =
        quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
          quad lambda alpha μ oracle k :=
    quadraticScalarBlockBoundaryVariance_formula_from_source
      (Node := Node) quad lambda μ oracle hnoise alpha k
  have hvariance_abs :
      |quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle k| ≤ Cvar := by
    rw [hvariance_formula, hAR_formula, abs_mul]
    have hqpow_le_one : q ^ k ≤ 1 :=
      pow_le_one₀ (n := k) hq_nonneg (le_of_lt hq_lt_one)
    have hqpow_nonneg : 0 ≤ q ^ k := pow_nonneg hq_nonneg k
    have hfactor_abs : |1 - q ^ k| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hqpow_le_one)]
      nlinarith
    exact le_trans
      (mul_le_of_le_one_right (abs_nonneg S) hfactor_abs) hS_bound
  have hpow_eq : G ^ (2 * k) = q ^ k := by
    dsimp [q]
    rw [pow_mul]
  have hbias_bound :
      quad.x0 ^ 2 *
          quadraticScalarPeriodMultiplier (Node := Node)
            quad lambda alpha ^ (2 * k) ≤ quad.x0 ^ 2 := by
    have hqpow_le_one : q ^ k ≤ 1 :=
      pow_le_one₀ (n := k) hq_nonneg (le_of_lt hq_lt_one)
    have hGpow_le_one : G ^ (2 * k) ≤ 1 := by
      simpa [hpow_eq] using hqpow_le_one
    dsimp [G] at hGpow_le_one
    exact mul_le_of_le_one_right (sq_nonneg quad.x0) hGpow_le_one
  rw [quadraticScalarBlockBoundarySecondMoment_eq_variance_add_bias
    (Node := Node) quad lambda alpha μ oracle k]
  calc
    quadraticScalarBlockBoundaryVariance (Node := Node)
        quad lambda alpha μ oracle k +
      quad.x0 ^ 2 *
        quadraticScalarPeriodMultiplier (Node := Node)
          quad lambda alpha ^ (2 * k) ≤
        Cvar + quad.x0 ^ 2 := by
      exact add_le_add (le_trans (le_abs_self _) hvariance_abs) hbias_bound
    _ = Cscalar := by rfl

/-- Finite-horizon linear square-moment budget for scalar comparison block
boundaries.  This is the exact input needed by the projected/scalar slow AR
forcing decomposition. -/
theorem quadraticScalarBlockBoundarySecondMoment_sum_linear_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle) :
    ∃ alpha0 Cscalar : ℝ,
      0 < alpha0 ∧ 0 ≤ Cscalar ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ N : ℕ,
            Finset.sum (Finset.range N) (fun k =>
              quadraticScalarBlockBoundarySecondMoment (Node := Node)
                quad lambda alpha μ oracle k) ≤
              Cscalar * (N : ℝ) := by
  classical
  obtain ⟨alpha0, Cscalar, halpha0_pos, hCscalar_nonneg, hpoint⟩ :=
    quadraticScalarBlockBoundarySecondMoment_uniform_bound
      (Node := Node) quad lambda μ oracle hquad hnoise
  refine ⟨alpha0, Cscalar, halpha0_pos, hCscalar_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le N
  calc
    Finset.sum (Finset.range N) (fun k =>
        quadraticScalarBlockBoundarySecondMoment (Node := Node)
          quad lambda alpha μ oracle k) ≤
        Finset.sum (Finset.range N) (fun _k => Cscalar) := by
      exact Finset.sum_le_sum fun k _hk =>
        hpoint alpha halpha_pos halpha_le k
    _ = Cscalar * (N : ℝ) := by simp [mul_comm]

/-- Deterministic finite-phase multiplier residue bound.  Once the exact
complete-period decomposition rewrites the multiplier contribution as
`(sum_r A_r(alpha)^2 / p - 1)` times the averaged block-boundary variance,
this lemma supplies the `O(alpha^2)` estimate. -/
theorem quadraticScalarFinitePhaseMultiplier_boundaryResidue_alpha_sq_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hvariance_formula :
      ∀ alpha : ℝ, ∀ K : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle K =
          quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle K) :
    ∃ alpha0 C : ℝ,
      0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            let phaseFactor : ℝ :=
              ((∑ r : Fin quad.period,
                quadraticScalarWithinPeriodMultiplier (Node := Node)
                  quad lambda alpha r.1 ^ 2) / (quad.period : ℝ)) - 1
            let boundaryAverage : ℝ :=
              lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarBlockBoundaryVariance (Node := Node)
                    quad lambda alpha μ oracle k)
            |phaseFactor * boundaryAverage| ≤ C * alpha ^ 2 := by
  classical
  obtain ⟨alphaB, M, halphaB_pos, hM_nonneg, hboundary⟩ :=
    quadraticScalarBlockBoundaryVariance_average_linear_bound
      (Node := Node) quad lambda μ oracle hquad hnoise hvariance_formula
  have hwithin_linear :=
    quadraticScalarWithinPeriodSquaredSum_isBigO_linear
      (Node := Node) quad lambda
  obtain ⟨Cs, hCs_pos, hCs_big⟩ := hwithin_linear.exists_pos
  have hphase_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖(∑ r : Fin quad.period,
          quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r.1 ^ 2) -
            (quad.period : ℝ)‖ ≤ Cs * ‖alpha‖ := by
    simpa using
      (Asymptotics.isBigOWith_iff.mp hCs_big)
  obtain ⟨epsS, hepsS_pos, hphase_eps⟩ :=
    Metric.eventually_nhds_iff.mp hphase_eventually
  let alpha0 : ℝ := min alphaB (epsS / 2)
  let C : ℝ := (Cs / (quad.period : ℝ)) * M
  have hperiod_pos : 0 < (quad.period : ℝ) := by
    exact_mod_cast quad.period_pos
  have hperiod_ne : (quad.period : ℝ) ≠ 0 := ne_of_gt hperiod_pos
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min halphaB_pos (half_pos hepsS_pos)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (div_nonneg hCs_pos.le hperiod_pos.le) hM_nonneg
  refine ⟨alpha0, C, halpha0_pos, hC_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let phaseSum : ℝ :=
    ∑ r : Fin quad.period,
      quadraticScalarWithinPeriodMultiplier (Node := Node)
        quad lambda alpha r.1 ^ 2
  let phaseFactor : ℝ := phaseSum / (quad.period : ℝ) - 1
  let boundaryAverage : ℝ :=
    lambda ^ 2 * (K : ℝ)⁻¹ *
      ((Finset.range K).sum fun k =>
        quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle k)
  have halpha_leB : alpha ≤ alphaB := le_trans halpha_le (min_le_left _ _)
  have hboundary_bound :
      |boundaryAverage| ≤ M * alpha := by
    simpa [boundaryAverage] using hboundary alpha halpha_pos halpha_leB K hK
  have halpha_lt_epsS : alpha < epsS := by
    have hhalf : alpha ≤ epsS / 2 :=
      le_trans halpha_le (min_le_right _ _)
    nlinarith [hepsS_pos]
  have hdist : dist alpha 0 < epsS := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_epsS
  have hphase_close :
      |phaseSum - (quad.period : ℝ)| ≤ Cs * alpha := by
    have hraw := hphase_eps hdist
    simpa [phaseSum, Real.norm_eq_abs, abs_of_pos halpha_pos] using hraw
  have hfactor_eq :
      phaseFactor = (phaseSum - (quad.period : ℝ)) / (quad.period : ℝ) := by
    dsimp [phaseFactor]
    field_simp [hperiod_ne]
  have hfactor_bound :
      |phaseFactor| ≤ (Cs / (quad.period : ℝ)) * alpha := by
    rw [hfactor_eq, abs_div, abs_of_pos hperiod_pos]
    calc
      |phaseSum - (quad.period : ℝ)| / (quad.period : ℝ) ≤
          (Cs * alpha) / (quad.period : ℝ) :=
        div_le_div_of_nonneg_right hphase_close hperiod_pos.le
      _ = (Cs / (quad.period : ℝ)) * alpha := by ring
  have hfactor_rhs_nonneg :
      0 ≤ (Cs / (quad.period : ℝ)) * alpha :=
    mul_nonneg (div_nonneg hCs_pos.le hperiod_pos.le) (le_of_lt halpha_pos)
  calc
    |phaseFactor * boundaryAverage| =
        |phaseFactor| * |boundaryAverage| := abs_mul _ _
    _ ≤ ((Cs / (quad.period : ℝ)) * alpha) * (M * alpha) :=
      mul_le_mul hfactor_bound hboundary_bound
        (abs_nonneg boundaryAverage) hfactor_rhs_nonneg
    _ = C * alpha ^ 2 := by
      dsimp [C]
      ring

/-- Complete-period finite-phase decomposition after deterministic bias
subtraction.  This is the remaining within-period source leaf from Appendix
C.2 step 6: reindex the `Kp` scalar moment sum by periods, unroll each
within-period scalar state, cancel the deterministic bias block average, and
show that the finite-phase fresh-noise propagation differs from the
block-boundary variance average by `O(alpha^2)`. -/
theorem quadraticScalarMomentFunctional_completePeriod_finitePhase_boundary_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hvariance_formula :
      ∀ alpha : ℝ, ∀ K : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle K =
          quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle K) :
    ∃ alpha0 Cphase : ℝ,
      0 < alpha0 ∧ 0 ≤ Cphase ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            let boundaryAverage : ℝ :=
              lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarBlockBoundaryVariance (Node := Node)
                    quad lambda alpha μ oracle k)
            |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                  (K * quad.period) -
                quadraticScalarBiasBlockAverage (Node := Node)
                  quad lambda alpha K) -
              boundaryAverage| ≤
            Cphase * alpha ^ 2 := by
  /- Appendix C.2 lines 1674-1678.  The next proof step should use
  `sum_range_mul_eq_sum_blocks` and
  `quadraticScalarComparisonProcess_unroll_window` to reduce every phase to
  the block-boundary variance plus finite propagated fresh-noise terms, then
  use `quadraticScalarBlockInnovationSecondMoment_eq_alpha_sq_finset_sum` and
  cross-time orthogonality to absorb the within-block residue into
  `O(alpha^2)`. -/
  classical
  obtain ⟨alphaB, Mboundary, halphaB_pos, hMboundary_nonneg,
      hboundary_linear⟩ :=
    quadraticScalarBlockBoundaryVariance_average_linear_bound
      (Node := Node) quad lambda μ oracle hquad hnoise hvariance_formula
  obtain ⟨alphaR, Cresidue, halphaR_pos, hCresidue_nonneg,
      hmultiplier_residue⟩ :=
    quadraticScalarFinitePhaseMultiplier_boundaryResidue_alpha_sq_bound
      (Node := Node) quad lambda μ oracle hquad hnoise hvariance_formula
  obtain ⟨alphaF, Cfresh, halphaF_pos, hCfresh_nonneg,
      hfresh_average⟩ :=
    quadraticScalarWindowPropagatedNoiseFinset_completePeriod_freshAverage_alpha_sq_bound
      (Node := Node) quad lambda μ oracle hnoise
  obtain ⟨alphaG, c1G, c2G, halphaG_pos, _hc1G_pos, _hc2G_pos,
      _hc1G_le_c2G, hsqueeze⟩ :=
    quadraticScalarPeriodMultiplier_smallAlpha_squeeze
      (Node := Node) quad lambda hquad
  have hphase_second_moment :
      ∀ alpha : ℝ, ∀ k r : ℕ,
        (∫ ω,
            |quad.quadraticScalarComparisonProcess lambda alpha
              (oracle.noise ω) (quad.blockStart k + r)| ^ 2 ∂μ) =
          quadraticScalarWindowPhaseProduct (Node := Node)
              quad lambda alpha (quad.blockStart k) r ^ 2 *
            quadraticScalarBlockBoundarySecondMoment (Node := Node)
              quad lambda alpha μ oracle k +
          alpha ^ 2 *
            (∫ ω,
              |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                ∂μ) := by
    intro alpha k r
    exact quadraticScalarComparisonProcess_blockPhase_secondMoment_decomp
      (Node := Node) quad lambda alpha μ oracle hnoise k r
  let alpha0 : ℝ := min alphaG (min alphaR alphaF)
  let Cphase : ℝ := Cresidue + Cfresh
  have halpha0_pos : 0 < alpha0 :=
    lt_min halphaG_pos (lt_min halphaR_pos halphaF_pos)
  have hCphase_nonneg : 0 ≤ Cphase := by
    dsimp [Cphase]
    exact add_nonneg hCresidue_nonneg hCfresh_nonneg
  refine ⟨alpha0, Cphase, halpha0_pos, hCphase_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let phaseFactor : ℝ :=
    ((∑ r : Fin quad.period,
      quadraticScalarWithinPeriodMultiplier (Node := Node)
        quad lambda alpha r.1 ^ 2) / (quad.period : ℝ)) - 1
  let boundaryAverage : ℝ :=
    lambda ^ 2 * (K : ℝ)⁻¹ *
      ((Finset.range K).sum fun k =>
        quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle k)
  let freshAverage : ℝ :=
    lambda ^ 2 * (((K * quad.period : ℕ) : ℝ)⁻¹) *
      ((Finset.range K).sum fun k =>
        (Finset.range quad.period).sum fun r =>
          alpha ^ 2 *
            (∫ ω,
              |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                ∂μ))
  have halpha_leG : alpha ≤ alphaG :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_leR : alpha ≤ alphaR :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have halpha_leF : alpha ≤ alphaF :=
    le_trans halpha_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hden_pos :
      0 < 1 - quadraticScalarPeriodMultiplier (Node := Node)
        quad lambda alpha ^ 2 :=
    (hsqueeze alpha halpha_pos halpha_leG).2.2
  have hresidue :
      |phaseFactor * boundaryAverage| ≤ Cresidue * alpha ^ 2 := by
    simpa [phaseFactor, boundaryAverage] using
      hmultiplier_residue alpha halpha_pos halpha_leR K hK
  have hfresh :
      |freshAverage| ≤ Cfresh * alpha ^ 2 := by
    simpa [freshAverage] using
      hfresh_average alpha halpha_pos halpha_leF K hK
  have hcomplete_decomp :
      (quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        boundaryAverage =
      phaseFactor * boundaryAverage + freshAverage := by
    /- Remaining exact Appendix C.2 algebra: rewrite the `Kp` moment with
    `sum_range_mul_eq_sum_blocks`, apply `hphase_second_moment`, replace
    block-start products by within-period products, and cancel the deterministic
    geometric bias against `quadraticScalarBiasBlockAverage`. -/
    let Gamma : ℝ :=
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
    have hden_ne : 1 - Gamma ^ 2 ≠ 0 := by
      dsimp [Gamma]
      exact ne_of_gt hden_pos
    have hmoment_phase :
        quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) =
          (((K * quad.period : ℕ) : ℝ)⁻¹) *
            ((Finset.range K).sum fun k =>
              (Finset.range quad.period).sum fun r =>
                lambda ^ 2 *
                  (quadraticScalarWithinPeriodMultiplier (Node := Node)
                      quad lambda alpha r ^ 2 *
                    quadraticScalarBlockBoundarySecondMoment (Node := Node)
                      quad lambda alpha μ oracle k +
                  alpha ^ 2 *
                    (∫ ω,
                      |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                        quad lambda alpha (oracle.noise ω)
                          (quad.blockStart k) r| ^ 2 ∂μ))) :=
      quadraticScalarMomentFunctional_completePeriod_phase_secondMoment_sum
        (Node := Node) quad lambda alpha μ oracle hnoise K
    have hsecond_split :
        ∀ k : ℕ,
          quadraticScalarBlockBoundarySecondMoment (Node := Node)
              quad lambda alpha μ oracle k =
            quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle k +
              quad.x0 ^ 2 * Gamma ^ (2 * k) := by
      intro k
      simpa [Gamma] using
        quadraticScalarBlockBoundarySecondMoment_eq_variance_add_bias
          (Node := Node) quad lambda alpha μ oracle k
    have hgeom :
        (Finset.range K).sum (fun k => Gamma ^ (2 * k)) =
          (1 - Gamma ^ (2 * K)) / (1 - Gamma ^ 2) := by
      have hraw :=
        real_geom_range_sum_div_of_one_sub_ne_zero (Gamma ^ 2) K hden_ne
      calc
        (Finset.range K).sum (fun k => Gamma ^ (2 * k)) =
            (Finset.range K).sum (fun k => (Gamma ^ 2) ^ k) := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [pow_mul]
        _ = (1 - (Gamma ^ 2) ^ K) / (1 - Gamma ^ 2) := hraw
        _ = (1 - Gamma ^ (2 * K)) / (1 - Gamma ^ 2) := by
          rw [pow_mul]
    rw [hmoment_phase]
    simp_rw [hsecond_split]
    have hgeom' :
        (Finset.range K).sum (fun k =>
            quadraticScalarPeriodMultiplier (Node := Node)
              quad lambda alpha ^ (2 * k)) =
          (1 -
              quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ (2 * K)) /
            (1 -
              quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha ^ 2) := by
      simpa [Gamma] using hgeom
    unfold quadraticScalarBiasBlockAverage
    dsimp [phaseFactor, boundaryAverage, freshAverage, Gamma]
    exact
      real_complete_period_phase_bias_fresh_algebra
        (K := K) (p := quad.period) quad.period_pos hK
        lambda quad.x0
        (quadraticScalarPeriodMultiplier (Node := Node)
          quad lambda alpha)
        (fun r =>
          quadraticScalarWithinPeriodMultiplier (Node := Node)
            quad lambda alpha r)
        (fun k =>
          quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle k)
        (fun k r =>
          alpha ^ 2 *
            (∫ ω,
              |quadraticScalarWindowPropagatedNoiseFinset (Node := Node)
                quad lambda alpha (oracle.noise ω) (quad.blockStart k) r| ^ 2
                ∂μ))
        hgeom'
  change
    |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
          (K * quad.period) -
        quadraticScalarBiasBlockAverage (Node := Node)
          quad lambda alpha K) -
      boundaryAverage| ≤ Cphase * alpha ^ 2
  rw [hcomplete_decomp]
  calc
    |phaseFactor * boundaryAverage + freshAverage| ≤
        |phaseFactor * boundaryAverage| + |freshAverage| := abs_add_le _ _
    _ ≤ Cresidue * alpha ^ 2 + Cfresh * alpha ^ 2 :=
        add_le_add hresidue hfresh
    _ = Cphase * alpha ^ 2 := by
        dsimp [Cphase]
        ring

/-- Complete-period finite-phase and zero-initial transient decomposition after
deterministic bias subtraction.  This is the single source-granularity leaf
left for Appendix C.2 step 6: it exposes the intermediate average of the
zero-initial block-boundary variance and states separately (i) the finite-phase
`O(alpha^2)` gap from the `Kp` moment sum to that boundary average and (ii) the
AR transient `O(T^{-1})` gap from that boundary average to the periodic steady
boundary variance average. -/
theorem quadraticScalarMomentFunctional_completePeriod_boundaryVariance_source_bounds
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hvariance_formula :
      ∀ alpha : ℝ, ∀ K : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle K =
          quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle K) :
    ∃ alpha0 Cphase Ctransient : ℝ,
      0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            let T : ℝ := ((K * quad.period : ℕ) : ℝ)
            let boundaryAverage : ℝ :=
              lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarBlockBoundaryVariance (Node := Node)
                    quad lambda alpha μ oracle k)
            let steadyAverage : ℝ :=
              lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarSteadyBoundaryVariance (Node := Node)
                    quad lambda alpha
                    (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                      quad lambda alpha μ oracle k))
            |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                  (K * quad.period) -
                quadraticScalarBiasBlockAverage (Node := Node)
                  quad lambda alpha K) -
              boundaryAverage| ≤
            Cphase * alpha ^ 2 ∧
            |boundaryAverage - steadyAverage| ≤ Ctransient * T⁻¹ := by
  classical
  obtain ⟨alphaP, Cphase, halphaP_pos, hCphase_nonneg, hphase⟩ :=
    quadraticScalarMomentFunctional_completePeriod_finitePhase_boundary_bound
      (Node := Node) quad lambda μ oracle hquad hnoise hvariance_formula
  obtain ⟨alphaT, Ctransient, halphaT_pos, hCtransient_nonneg, htransient⟩ :=
    quadraticScalarBlockBoundaryVariance_to_steadyAverage_transient_bound
      (Node := Node) quad lambda μ oracle hquad hnoise hvariance_formula
  let alpha0 : ℝ := min alphaP alphaT
  refine ⟨alpha0, Cphase, Ctransient, lt_min halphaP_pos halphaT_pos,
    hCphase_nonneg, hCtransient_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  have halpha_leP : alpha ≤ alphaP := le_trans halpha_le (min_le_left _ _)
  have halpha_leT : alpha ≤ alphaT := le_trans halpha_le (min_le_right _ _)
  constructor
  · simpa using hphase alpha halpha_pos halpha_leP K hK
  · simpa using htransient alpha halpha_pos halpha_leT K hK

/-- Formula-level complete-period decomposition for Appendix C.2 after the
deterministic bias average is subtracted.  The remaining source-local
calculation is now exactly the finite-phase/zero-transient step: the complete
`Kp` moment average is compared with the average of the periodic steady
block-boundary variances. -/
theorem quadraticScalarMomentFunctional_completePeriod_to_steadyBoundaryAverage_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hvariance_formula :
      ∀ alpha : ℝ, ∀ K : ℕ,
        quadraticScalarBlockBoundaryVariance (Node := Node)
            quad lambda alpha μ oracle K =
          quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
            quad lambda alpha μ oracle K) :
    ∃ alpha0 Cphase Ctransient : ℝ,
      0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            let T : ℝ := ((K * quad.period : ℕ) : ℝ)
            let steadyAverage : ℝ :=
              lambda ^ 2 * (K : ℝ)⁻¹ *
                ((Finset.range K).sum fun k =>
                  quadraticScalarSteadyBoundaryVariance (Node := Node)
                    quad lambda alpha
                    (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                      quad lambda alpha μ oracle k))
            |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                  (K * quad.period) -
                quadraticScalarBiasBlockAverage (Node := Node)
                  quad lambda alpha K) -
              steadyAverage| ≤
            Cphase * alpha ^ 2 + Ctransient * T⁻¹ := by
  classical
  obtain ⟨alpha0, Cphase, Ctransient, halpha0_pos, hCphase_nonneg,
      hCtransient_nonneg, hbounds⟩ :=
    quadraticScalarMomentFunctional_completePeriod_boundaryVariance_source_bounds
      (Node := Node) quad lambda μ oracle hquad hnoise hvariance_formula
  refine ⟨alpha0, Cphase, Ctransient, halpha0_pos,
    hCphase_nonneg, hCtransient_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let T : ℝ := ((K * quad.period : ℕ) : ℝ)
  let boundaryAverage : ℝ :=
    lambda ^ 2 * (K : ℝ)⁻¹ *
      ((Finset.range K).sum fun k =>
        quadraticScalarBlockBoundaryVariance (Node := Node)
          quad lambda alpha μ oracle k)
  let steadyAverage : ℝ :=
    lambda ^ 2 * (K : ℝ)⁻¹ *
      ((Finset.range K).sum fun k =>
        quadraticScalarSteadyBoundaryVariance (Node := Node)
          quad lambda alpha
          (quadraticScalarBlockInnovationSecondMoment (Node := Node)
            quad lambda alpha μ oracle k))
  have hboundsK := hbounds alpha halpha_pos halpha_le K hK
  have hphaseK :
      |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        boundaryAverage| ≤
      Cphase * alpha ^ 2 := by
    simpa [boundaryAverage] using
      hboundsK.1
  have htransientK :
      |boundaryAverage - steadyAverage| ≤ Ctransient * T⁻¹ := by
    simpa [T, boundaryAverage, steadyAverage] using
      hboundsK.2
  have htriangle :
      |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        steadyAverage| ≤
      |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        boundaryAverage| + |boundaryAverage - steadyAverage| := by
    have hrewrite :
        (quad.quadraticScalarMomentFunctional lambda alpha μ oracle
              (K * quad.period) -
            quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K) -
          steadyAverage =
        ((quad.quadraticScalarMomentFunctional lambda alpha μ oracle
              (K * quad.period) -
            quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K) -
          boundaryAverage) + (boundaryAverage - steadyAverage) := by
      ring
    rw [hrewrite]
    exact abs_add_le _ _
  exact le_trans htriangle (add_le_add hphaseK htransientK)

/-- Exact remaining complete-period finite-phase assembly for Appendix C.2.
This is the source-granularity obstruction after the stochastic block-noise,
geometric bias, and steady-boundary variance inputs are available: reindex the
complete `Kp` scalar moment sum by `sum_range_mul_eq_sum_blocks`, use the
within-period unroll and the AR boundary formula to compare the finite-phase
variance contribution with the periodic steady boundary variance, and absorb
the zero-initial transient as `O(T^{-1})`. -/
theorem quadraticScalarMomentFunctional_completePeriod_phase_transient_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hcomplete_to_steady :
      ∃ alpha0 Cphase Ctransient : ℝ,
        0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
            ∀ K : ℕ, 1 ≤ K →
              let T : ℝ := ((K * quad.period : ℕ) : ℝ)
              let steadyAverage : ℝ :=
                lambda ^ 2 * (K : ℝ)⁻¹ *
                  ((Finset.range K).sum fun k =>
                    quadraticScalarSteadyBoundaryVariance (Node := Node)
                      quad lambda alpha
                      (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                        quad lambda alpha μ oracle k))
              |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                    (K * quad.period) -
                  quadraticScalarBiasBlockAverage (Node := Node)
                    quad lambda alpha K) -
                steadyAverage| ≤
              Cphase * alpha ^ 2 + Ctransient * T⁻¹)
    (hsteady_uniform :
      ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ k : ℕ,
            |quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k) -
              (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))))| ≤
            C * alpha ^ 2)
    :
    ∃ alpha0 Cphase Ctransient : ℝ,
      0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                  (K * quad.period) -
                quadraticScalarBiasBlockAverage (Node := Node)
                  quad lambda alpha K) -
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha| ≤
            Cphase * alpha ^ 2 +
              Ctransient * ((((K * quad.period : ℕ) : ℝ)⁻¹)) := by
  classical
  obtain ⟨alphaD, Cphase, Ctransient, halphaD_pos, hCphase_nonneg,
      hCtransient_nonneg, hdecomp⟩ :=
    hcomplete_to_steady
  obtain ⟨alphaS, Csteady, halphaS_pos, hCsteady_nonneg, hsteady⟩ :=
    hsteady_uniform
  let alpha0 : ℝ := min alphaD alphaS
  let Cphase' : ℝ := Cphase + lambda ^ 2 * Csteady
  refine ⟨alpha0, Cphase', Ctransient, lt_min halphaD_pos halphaS_pos,
    ?_, hCtransient_nonneg, ?_⟩
  · exact add_nonneg hCphase_nonneg
      (mul_nonneg (sq_nonneg lambda) hCsteady_nonneg)
  intro alpha halpha_pos halpha_le K hK
  let T : ℝ := ((K * quad.period : ℕ) : ℝ)
  let steadyTarget : ℝ :=
    alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
      (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
  let steadyAverage : ℝ :=
    lambda ^ 2 * (K : ℝ)⁻¹ *
      ((Finset.range K).sum fun k =>
        quadraticScalarSteadyBoundaryVariance (Node := Node)
          quad lambda alpha
          (quadraticScalarBlockInnovationSecondMoment (Node := Node)
            quad lambda alpha μ oracle k))
  let leadVariance : ℝ :=
    (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
      (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha
  have halpha_leD : alpha ≤ alphaD := le_trans halpha_le (min_le_left _ _)
  have halpha_leS : alpha ≤ alphaS := le_trans halpha_le (min_le_right _ _)
  have hdecompK :
      |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        steadyAverage| ≤
      Cphase * alpha ^ 2 + Ctransient * T⁻¹ := by
    simpa [T, steadyAverage] using
      hdecomp alpha halpha_pos halpha_leD K hK
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hK_ne : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK_pos)
  have hK_nonneg : 0 ≤ (K : ℝ) := by exact_mod_cast Nat.zero_le K
  have hsteady_each :
      ∀ k ∈ Finset.range K,
        |quadraticScalarSteadyBoundaryVariance (Node := Node)
            quad lambda alpha
            (quadraticScalarBlockInnovationSecondMoment (Node := Node)
              quad lambda alpha μ oracle k) -
          steadyTarget| ≤ Csteady * alpha ^ 2 := by
    intro k _hk
    simpa [steadyTarget] using hsteady alpha halpha_pos halpha_leS k
  have hsum_abs :
      |(Finset.range K).sum fun k =>
          (quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k) -
            steadyTarget)| ≤
        (K : ℝ) * (Csteady * alpha ^ 2) := by
    calc
      |(Finset.range K).sum fun k =>
          (quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k) -
            steadyTarget)| ≤
          (Finset.range K).sum fun k =>
            |quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k) -
              steadyTarget| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Finset.range K).sum fun _k => Csteady * alpha ^ 2 := by
        exact Finset.sum_le_sum hsteady_each
      _ = (K : ℝ) * (Csteady * alpha ^ 2) := by simp
  have hsteady_avg :
      |steadyAverage - leadVariance| ≤
        lambda ^ 2 * Csteady * alpha ^ 2 := by
    have hlambda_nonneg : 0 ≤ lambda := le_of_lt hquad.1
    have hlambda_sq_nonneg : 0 ≤ lambda ^ 2 := sq_nonneg lambda
    have hsum_eq :
        (Finset.range K).sum (fun k =>
          quadraticScalarSteadyBoundaryVariance (Node := Node)
            quad lambda alpha
            (quadraticScalarBlockInnovationSecondMoment (Node := Node)
              quad lambda alpha μ oracle k)) -
            (K : ℝ) * steadyTarget =
          (Finset.range K).sum fun k =>
            (quadraticScalarSteadyBoundaryVariance (Node := Node)
              quad lambda alpha
              (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k) -
            steadyTarget) := by
      rw [Finset.sum_sub_distrib]
      simp [mul_comm]
    have hlead_eq : leadVariance = lambda ^ 2 * steadyTarget := by
      dsimp [leadVariance, steadyTarget]
      have hlambda_ne : lambda ≠ 0 := ne_of_gt hquad.1
      field_simp [hlambda_ne]
    have hdiff_eq :
        steadyAverage - leadVariance =
          lambda ^ 2 * (K : ℝ)⁻¹ *
            ((Finset.range K).sum fun k =>
              (quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k) -
              steadyTarget)) := by
      dsimp [steadyAverage]
      rw [hlead_eq, ← hsum_eq]
      field_simp [hK_ne]
    calc
      |steadyAverage - leadVariance| =
          |lambda ^ 2 * (K : ℝ)⁻¹| *
            |(Finset.range K).sum fun k =>
              (quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k) -
              steadyTarget)| := by
        rw [hdiff_eq, abs_mul]
      _ ≤ |lambda ^ 2 * (K : ℝ)⁻¹| *
            ((K : ℝ) * (Csteady * alpha ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hsum_abs (abs_nonneg _)
      _ = lambda ^ 2 * Csteady * alpha ^ 2 := by
        rw [abs_mul, abs_of_nonneg hlambda_sq_nonneg,
          abs_of_nonneg (inv_nonneg.mpr hK_nonneg)]
        field_simp [hK_ne]
  have htriangle :
      |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        leadVariance| ≤
      |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        steadyAverage| + |steadyAverage - leadVariance| := by
    have hrewrite :
        (quad.quadraticScalarMomentFunctional lambda alpha μ oracle
              (K * quad.period) -
            quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K) -
          leadVariance =
        ((quad.quadraticScalarMomentFunctional lambda alpha μ oracle
              (K * quad.period) -
            quadraticScalarBiasBlockAverage (Node := Node)
              quad lambda alpha K) -
          steadyAverage) + (steadyAverage - leadVariance) := by
      ring
    rw [hrewrite]
    exact abs_add_le _ _
  calc
    |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
          (K * quad.period) -
        quadraticScalarBiasBlockAverage (Node := Node)
          quad lambda alpha K) -
      (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
        (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha| =
        |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        leadVariance| := by rfl
    _ ≤
        |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
            (K * quad.period) -
          quadraticScalarBiasBlockAverage (Node := Node)
            quad lambda alpha K) -
        steadyAverage| + |steadyAverage - leadVariance| := htriangle
    _ ≤
        (Cphase * alpha ^ 2 + Ctransient * T⁻¹) +
          lambda ^ 2 * Csteady * alpha ^ 2 :=
        add_le_add hdecompK hsteady_avg
    _ ≤ Cphase' * alpha ^ 2 + Ctransient * T⁻¹ := by
      dsimp [Cphase']
      ring_nf
      exact le_rfl

theorem quadraticScalarMomentFunctional_completePeriod_finitePhase_variance_gap
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hsteady_uniform :
      ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ k : ℕ,
            |quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k) -
              (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))))| ≤
            C * alpha ^ 2) :
    ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ K : ℕ, 1 ≤ K →
          |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                (K * quad.period) -
              quadraticScalarBiasBlockAverage (Node := Node)
                quad lambda alpha K) -
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha| ≤
          C * ((((K * quad.period : ℕ) : ℝ)⁻¹) + alpha ^ 2) := by
  classical
  obtain ⟨alpha0, Cphase, Ctransient, halpha0_pos, hCphase_nonneg,
      hCtransient_nonneg, hphase_transient⟩ :=
    let hvariance_formula :
        ∀ alpha : ℝ, ∀ K : ℕ,
          quadraticScalarBlockBoundaryVariance (Node := Node)
              quad lambda alpha μ oracle K =
            quadraticScalarBlockBoundaryVarianceARFormula (Node := Node)
              quad lambda alpha μ oracle K :=
      quadraticScalarBlockBoundaryVariance_formula_from_source
        (Node := Node) quad lambda μ oracle hnoise
    let hcomplete_to_steady :=
      quadraticScalarMomentFunctional_completePeriod_to_steadyBoundaryAverage_bound
        (Node := Node) quad lambda μ oracle hquad hnoise hvariance_formula
    quadraticScalarMomentFunctional_completePeriod_phase_transient_bound
      (Node := Node) quad lambda μ oracle hquad hcomplete_to_steady
      hsteady_uniform
  let C : ℝ := Cphase + Ctransient
  refine ⟨alpha0, C, halpha0_pos,
    add_nonneg hCphase_nonneg hCtransient_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let T : ℝ := ((K * quad.period : ℕ) : ℝ)
  have hbound :=
    hphase_transient alpha halpha_pos halpha_le K hK
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hT_pos : 0 < T := by
    dsimp [T]
    exact_mod_cast Nat.mul_pos hK_pos quad.period_pos
  have hT_nonneg : 0 ≤ T := le_of_lt hT_pos
  have hTinv_nonneg : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_nonneg
  have halpha_sq_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have hcombine :
      Cphase * alpha ^ 2 + Ctransient * T⁻¹ ≤
        C * (T⁻¹ + alpha ^ 2) := by
    dsimp [C]
    nlinarith [mul_nonneg hCphase_nonneg halpha_sq_nonneg,
      mul_nonneg hCphase_nonneg hTinv_nonneg,
      mul_nonneg hCtransient_nonneg halpha_sq_nonneg,
      mul_nonneg hCtransient_nonneg hTinv_nonneg]
  exact le_trans (by simpa [T] using hbound) hcombine

/-- Appendix C.2 complete-period variance-gap assembly after the deterministic
bias average has been separated.  This is the remaining source-local finite
phase argument: use the block-boundary AR closed form, the uniform block-noise
variance expansion, and the steady boundary variance expansion to show that
the complete-period variance contribution equals its periodic steady value up
to `O(T^{-1}+alpha^2)`. -/
theorem quadraticScalarMomentFunctional_completePeriod_variance_gap_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hcomplete_to_steady :
      ∃ alpha0 Cphase Ctransient : ℝ,
        0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
            ∀ K : ℕ, 1 ≤ K →
              let T : ℝ := ((K * quad.period : ℕ) : ℝ)
              let steadyAverage : ℝ :=
                lambda ^ 2 * (K : ℝ)⁻¹ *
                  ((Finset.range K).sum fun k =>
                    quadraticScalarSteadyBoundaryVariance (Node := Node)
                      quad lambda alpha
                      (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                        quad lambda alpha μ oracle k))
              |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                    (K * quad.period) -
                  quadraticScalarBiasBlockAverage (Node := Node)
                    quad lambda alpha K) -
                steadyAverage| ≤
              Cphase * alpha ^ 2 + Ctransient * T⁻¹)
    (hblock_uniform :
      ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, |alpha| < alpha0 →
          ∀ k : ℕ,
            |quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k -
              alpha ^ 2 * quad.sigma ^ 2 *
                (quad.period : ℝ) * quad.influenceSecondMoment| ≤
            C * |alpha| ^ 3)
    (_hsteady :
      ∀ k : ℕ,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k) -
              (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))))
          (fun alpha : ℝ => alpha ^ 2)) :
    ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ K : ℕ, 1 ≤ K →
          |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                (K * quad.period) -
              quadraticScalarBiasBlockAverage (Node := Node)
                quad lambda alpha K) -
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha| ≤
          C * ((((K * quad.period : ℕ) : ℝ)⁻¹) + alpha ^ 2) := by
  have hsteady_uniform :
      ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ k : ℕ,
            |quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k) -
              (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))))| ≤
            C * alpha ^ 2 :=
    quadraticScalarSteadyBoundaryVariance_expansion_uniform
      (Node := Node) quad lambda μ oracle hquad hblock_uniform
  obtain ⟨alpha0, Cphase, Ctransient, halpha0_pos, hCphase_nonneg,
      hCtransient_nonneg, hphase_transient⟩ :=
    quadraticScalarMomentFunctional_completePeriod_phase_transient_bound
      (Node := Node) quad lambda μ oracle hquad hcomplete_to_steady
      hsteady_uniform
  let C : ℝ := Cphase + Ctransient
  refine ⟨alpha0, C, halpha0_pos,
    add_nonneg hCphase_nonneg hCtransient_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let T : ℝ := ((K * quad.period : ℕ) : ℝ)
  have hbound :=
    hphase_transient alpha halpha_pos halpha_le K hK
  have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
  have hT_pos : 0 < T := by
    dsimp [T]
    exact_mod_cast Nat.mul_pos hK_pos quad.period_pos
  have hT_nonneg : 0 ≤ T := le_of_lt hT_pos
  have hTinv_nonneg : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_nonneg
  have halpha_sq_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have hcombine :
      Cphase * alpha ^ 2 + Ctransient * T⁻¹ ≤
        C * (T⁻¹ + alpha ^ 2) := by
    dsimp [C]
    nlinarith [mul_nonneg hCphase_nonneg halpha_sq_nonneg,
      mul_nonneg hCphase_nonneg hTinv_nonneg,
      mul_nonneg hCtransient_nonneg halpha_sq_nonneg,
      mul_nonneg hCtransient_nonneg hTinv_nonneg]
  exact le_trans (by simpa [T] using hbound) hcombine

/-- Appendix C.2 complete-period scalar moment assembly for horizons
`T = Kp`.  This is the source-granularity step that combines the deterministic
bias summation, block-boundary AR closed form, and periodic steady variance
comparison before the at-most-one-period tail bookkeeping. -/
theorem quadraticScalarMomentFunctional_completePeriod_expansion_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hcomplete_to_steady :
      ∃ alpha0 Cphase Ctransient : ℝ,
        0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
            ∀ K : ℕ, 1 ≤ K →
              let T : ℝ := ((K * quad.period : ℕ) : ℝ)
              let steadyAverage : ℝ :=
                lambda ^ 2 * (K : ℝ)⁻¹ *
                  ((Finset.range K).sum fun k =>
                    quadraticScalarSteadyBoundaryVariance (Node := Node)
                      quad lambda alpha
                      (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                        quad lambda alpha μ oracle k))
              |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                    (K * quad.period) -
                  quadraticScalarBiasBlockAverage (Node := Node)
                    quad lambda alpha K) -
                steadyAverage| ≤
              Cphase * alpha ^ 2 + Ctransient * T⁻¹)
    (hsqueeze :
      ∃ alpha0 c1 c2 : ℝ,
        0 < alpha0 ∧ 0 < c1 ∧ 0 < c2 ∧ c1 ≤ c2 ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
            1 - c2 * alpha ≤
                quadraticScalarPeriodMultiplier (Node := Node)
                  quad lambda alpha ∧
              quadraticScalarPeriodMultiplier (Node := Node)
                  quad lambda alpha ≤ 1 - c1 * alpha ∧
                0 < 1 -
                  quadraticScalarPeriodMultiplier (Node := Node)
                    quad lambda alpha ^ 2)
    (hblock :
      ∀ k : ℕ,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k -
              alpha ^ 2 * quad.sigma ^ 2 *
                (quad.period : ℝ) * quad.influenceSecondMoment)
          (fun alpha : ℝ => alpha ^ 3))
    (hblock_uniform :
      ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, |alpha| < alpha0 →
          ∀ k : ℕ,
            |quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k -
              alpha ^ 2 * quad.sigma ^ 2 *
                (quad.period : ℝ) * quad.influenceSecondMoment| ≤
            C * |alpha| ^ 3)
    (hbias :
      ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            |quadraticScalarBiasBlockAverage (Node := Node)
                quad lambda alpha K -
              quad.Delta /
                ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha *
                  ((K * quad.period : ℕ) : ℝ))| ≤
              C * ((((K * quad.period : ℕ) : ℝ)⁻¹) +
                Real.exp (-(c * alpha *
                  ((K * quad.period : ℕ) : ℝ))) /
                  (alpha * ((K * quad.period : ℕ) : ℝ))))
    (hsteady :
      ∀ k : ℕ,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k) -
              (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))))
          (fun alpha : ℝ => alpha ^ 2)) :
    ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
        ∀ K : ℕ, 1 ≤ K →
          |quad.quadraticScalarMomentFunctional lambda alpha μ oracle
              (K * quad.period) -
            (quad.Delta /
                ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha *
                  ((K * quad.period : ℕ) : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
          C * ((((K * quad.period : ℕ) : ℝ)⁻¹) + alpha ^ 2 +
            Real.exp (-(c * alpha *
              ((K * quad.period : ℕ) : ℝ))) /
              (alpha * ((K * quad.period : ℕ) : ℝ))) := by
  classical
  obtain ⟨alphaB, cB, CB, halphaB_pos, hcB_pos, hCB_nonneg, hbias_bound⟩ :=
    hbias
  obtain ⟨alphaV, CV, halphaV_pos, hCV_nonneg, hvar_bound⟩ :=
    quadraticScalarMomentFunctional_completePeriod_variance_gap_bound
      (Node := Node) quad lambda μ oracle hquad hnoise
      hcomplete_to_steady hblock_uniform hsteady
  let alpha0 : ℝ := min alphaB alphaV
  let C : ℝ := CB + CV
  refine ⟨alpha0, cB, C, lt_min halphaB_pos halphaV_pos, hcB_pos,
    add_nonneg hCB_nonneg hCV_nonneg, ?_⟩
  intro alpha halpha_pos halpha_le K hK
  let T : ℝ := ((K * quad.period : ℕ) : ℝ)
  let leadBias : ℝ :=
    quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * T)
  let leadVariance : ℝ :=
    (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
      (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha
  let bias : ℝ :=
    quadraticScalarBiasBlockAverage (Node := Node) quad lambda alpha K
  let moment : ℝ :=
    quad.quadraticScalarMomentFunctional lambda alpha μ oracle
      (K * quad.period)
  have halpha_leB : alpha ≤ alphaB :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_leV : alpha ≤ alphaV :=
    le_trans halpha_le (min_le_right _ _)
  have hbiasK :
      |bias - leadBias| ≤
        CB * (T⁻¹ +
          Real.exp (-(cB * alpha * T)) / (alpha * T)) := by
    simpa [bias, leadBias, T] using
      hbias_bound alpha halpha_pos halpha_leB K hK
  have hvarK :
      |(moment - bias) - leadVariance| ≤
        CV * (T⁻¹ + alpha ^ 2) := by
    simpa [moment, bias, leadVariance, T] using
      hvar_bound alpha halpha_pos halpha_leV K hK
  have hT_pos : 0 < T := by
    dsimp [T]
    have hK_pos : 0 < K := lt_of_lt_of_le Nat.zero_lt_one hK
    exact_mod_cast Nat.mul_pos hK_pos quad.period_pos
  have hT_nonneg : 0 ≤ T := le_of_lt hT_pos
  have halphaT_nonneg : 0 ≤ alpha * T :=
    mul_nonneg (le_of_lt halpha_pos) hT_nonneg
  have htermT_nonneg : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_nonneg
  have htermA_nonneg : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have hexp_nonneg : 0 ≤ Real.exp (-(cB * alpha * T)) :=
    Real.exp_nonneg _
  have htermE_nonneg :
      0 ≤ Real.exp (-(cB * alpha * T)) / (alpha * T) :=
    div_nonneg hexp_nonneg halphaT_nonneg
  have htriangle :
      |moment - (leadBias + leadVariance)| ≤
        |bias - leadBias| + |(moment - bias) - leadVariance| := by
    have hrewrite :
        moment - (leadBias + leadVariance) =
          (bias - leadBias) + ((moment - bias) - leadVariance) := by
      ring
    rw [hrewrite]
    exact abs_add_le _ _
  calc
    |moment - (leadBias + leadVariance)| ≤
        |bias - leadBias| + |(moment - bias) - leadVariance| := htriangle
    _ ≤
        CB * (T⁻¹ +
          Real.exp (-(cB * alpha * T)) / (alpha * T)) +
        CV * (T⁻¹ + alpha ^ 2) := add_le_add hbiasK hvarK
    _ ≤
        C * (T⁻¹ + alpha ^ 2 +
          Real.exp (-(cB * alpha * T)) / (alpha * T)) := by
      dsimp [C]
      nlinarith [hCB_nonneg, hCV_nonneg, htermT_nonneg,
        htermA_nonneg, htermE_nonneg]

/-- Prefix monotonicity for the nonnegative scalar second-moment sum in
`quadraticScalarMomentFunctional`, written in the scaled form needed for the
Appendix C.2 tail comparison.  If `N ≤ T`, the average over `T` contains the
first `N` nonnegative summands. -/
theorem quadraticScalarMomentFunctional_scaled_prefix_le
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ)
    {N T : ℕ} (hNT : N ≤ T) (hT : 1 ≤ T) :
    ((T : ℝ)⁻¹) * ((N : ℝ) *
        quad.quadraticScalarMomentFunctional lambda alpha μ oracle N) ≤
      quad.quadraticScalarMomentFunctional lambda alpha μ oracle T := by
  classical
  let f : ℕ → ℝ := fun t =>
    ∫ ω, |lambda *
      quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω) t| ^ 2 ∂μ
  have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast (Nat.zero_le T)
  have hsum :
      (Finset.range N).sum f ≤ (Finset.range T).sum f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNT)
    intro t _htT _htN
    dsimp [f]
    exact MeasureTheory.integral_nonneg fun _ω => sq_nonneg _
  have hscaled :
      ((T : ℝ)⁻¹) * (Finset.range N).sum f ≤
        ((T : ℝ)⁻¹) * (Finset.range T).sum f :=
    mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hT_nonneg)
  by_cases hNzero : N = 0
  · subst N
    simpa [quadraticScalarMomentFunctional, f, mul_assoc] using hscaled
  · have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hNzero
    have hleft :
        ((T : ℝ)⁻¹) * ((N : ℝ) *
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle N) =
          ((T : ℝ)⁻¹) * (Finset.range N).sum f := by
      unfold quadraticScalarMomentFunctional
      dsimp [f]
      field_simp [hN_ne]
    rw [hleft]
    simpa [quadraticScalarMomentFunctional, f, mul_assoc] using hscaled

/-- Suffix monotonicity for the nonnegative scalar second-moment sum in
`quadraticScalarMomentFunctional`, written in the scaled form needed for the
Appendix C.2 tail comparison.  If `T ≤ N`, the complete horizon `N` contains
all summands of the shorter horizon `T`. -/
theorem quadraticScalarMomentFunctional_le_scaled_complete
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ)
    {T N : ℕ} (hTN : T ≤ N) (hT : 1 ≤ T) :
    quad.quadraticScalarMomentFunctional lambda alpha μ oracle T ≤
      ((T : ℝ)⁻¹) * ((N : ℝ) *
        quad.quadraticScalarMomentFunctional lambda alpha μ oracle N) := by
  classical
  let f : ℕ → ℝ := fun t =>
    ∫ ω, |lambda *
      quad.quadraticScalarComparisonProcess lambda alpha (oracle.noise ω) t| ^ 2 ∂μ
  have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast (Nat.zero_le T)
  have hsum :
      (Finset.range T).sum f ≤ (Finset.range N).sum f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hTN)
    intro t _htN _htT
    dsimp [f]
    exact MeasureTheory.integral_nonneg fun _ω => sq_nonneg _
  have hscaled :
      ((T : ℝ)⁻¹) * (Finset.range T).sum f ≤
        ((T : ℝ)⁻¹) * (Finset.range N).sum f :=
    mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hT_nonneg)
  by_cases hNzero : N = 0
  · have hTzero : T = 0 := Nat.eq_zero_of_le_zero (by simpa [hNzero] using hTN)
    omega
  · have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hNzero
    have hright :
        ((T : ℝ)⁻¹) * ((N : ℝ) *
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle N) =
          ((T : ℝ)⁻¹) * (Finset.range N).sum f := by
      unfold quadraticScalarMomentFunctional
      dsimp [f]
      field_simp [hN_ne]
    rw [hright]
    simpa [quadraticScalarMomentFunctional, f, mul_assoc] using hscaled

/- Arithmetic facts for the complete-period horizons adjacent to an arbitrary
positive scalar-moment horizon.  The ceiling block is used for the upper
sandwich, and the floor block is used for the lower sandwich once `p <= T`. -/
theorem quadraticScalar_completePeriod_ceiling_facts
    (quad : Setup Node ℝ) (T : ℕ) (hT : 1 ≤ T) :
    let Kceil : ℕ := (T - 1) / quad.period + 1
    let Nceil : ℕ := Kceil * quad.period
    1 ≤ Kceil ∧ T ≤ Nceil ∧ Kceil ≤ T ∧
      Nceil ≤ quad.period * T ∧ Nceil ≤ T + quad.period - 1 ∧
        Nceil - T ≤ quad.period - 1 := by
  exact Nat.ceil_block_multiple_bounds quad.period T quad.period_pos hT

theorem quadraticScalar_completePeriod_floor_facts
    (quad : Setup Node ℝ) (T : ℕ) (hpT : quad.period ≤ T) :
    let Kfloor : ℕ := T / quad.period
    let Nfloor : ℕ := Kfloor * quad.period
    1 ≤ Kfloor ∧ Nfloor ≤ T ∧ T ≤ 2 * Nfloor ∧
      T - Nfloor ≤ quad.period - 1 := by
  exact Nat.floor_block_multiple_facts quad.period T quad.period_pos hpT

/-- Elementary real-order bridge used by the arbitrary-tail scalar moment
assembly: if `x` is sandwiched between `lower` and `upper`, and both endpoints
are within `R` of the target `center` from the appropriate side, then `x` is
within `R` of `center`. -/
theorem real_abs_sub_le_of_sandwich_errors
    {lower x upper center R : ℝ}
    (hlower : lower ≤ x) (hupper : x ≤ upper)
    (hupper_err : upper - center ≤ R)
    (hlower_err : center - lower ≤ R) :
    |x - center| ≤ R := by
  rw [abs_sub_le_iff]
  constructor
  · linarith
  · linarith

/-- If a nonnegative scalar is bounded above, its distance to an arbitrary
center is controlled by the upper bound plus the center's absolute value. -/
theorem real_abs_sub_le_upper_add_abs_of_nonneg
    {x upper center : ℝ} (hx_nonneg : 0 ≤ x) (hupper : x ≤ upper) :
    |x - center| ≤ upper + |center| := by
  calc
    |x - center| ≤ |x| + |center| := abs_sub x center
    _ = x + |center| := by rw [abs_of_nonneg hx_nonneg]
    _ ≤ upper + |center| := add_le_add hupper le_rfl

theorem real_abs_le_abs_center_add_radius
    {x center radius : ℝ} (h : |x - center| ≤ radius) :
    |x| ≤ |center| + radius := by
  calc
    |x| = |(x - center) + center| := by ring_nf
    _ ≤ |x - center| + |center| := abs_add_le _ _
    _ ≤ radius + |center| := add_le_add h le_rfl
    _ = |center| + radius := by ring

/-- On a fixed bounded horizon, the weakened exponential tail
`exp(-(c*alpha*T))/(alpha*T)` dominates the plain reciprocal scale up to the
fixed factor `exp(c*p)+1`. -/
theorem real_inv_alpha_time_le_fixed_exp_tail
    {alpha c T p : ℝ} (halpha_pos : 0 < alpha) (halpha_le_one : alpha ≤ 1)
    (hc_pos : 0 < c) (hT_pos : 0 < T) (hT_le_p : T ≤ p) :
    (alpha * T)⁻¹ ≤
      (Real.exp (c * p) + 1) *
        (Real.exp (-(c * alpha * T)) / (alpha * T)) :=
  by
    have hprod_pos : 0 < alpha * T := mul_pos halpha_pos hT_pos
    have hprod_le_p : alpha * T ≤ p := by
      calc
        alpha * T ≤ 1 * T :=
          mul_le_mul_of_nonneg_right halpha_le_one hT_pos.le
        _ = T := one_mul T
        _ ≤ p := hT_le_p
    exact Real.inv_mul_le_fixed_exp_tail_of_le hprod_pos hprod_le_p

set_option maxHeartbeats 1000000 in
theorem real_exp_complete_tail_ceiling_le
    {alpha c cTail T N : ℝ} (halpha_nonneg : 0 ≤ alpha)
    (hc_pos : 0 < c) (hcTail : cTail = c / 2)
    (hT_nonneg : 0 ≤ T) (hTN : T ≤ N) :
    Real.exp (-(c * alpha * N)) ≤
      Real.exp (-(cTail * alpha * T)) := by
  apply Real.exp_le_exp.mpr
  have hscale : cTail * alpha * T ≤ c * alpha * N := by
    subst cTail
    have hcat_nonneg : 0 ≤ c * alpha * T := by
      exact mul_nonneg (mul_nonneg hc_pos.le halpha_nonneg) hT_nonneg
    have hhalf_le : c / 2 * alpha * T ≤ c * alpha * T := by
      calc
        c / 2 * alpha * T = (1 / 2 : ℝ) * (c * alpha * T) := by ring
        _ ≤ 1 * (c * alpha * T) :=
          mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1)
            hcat_nonneg
        _ = c * alpha * T := by ring
    have hfull_le : c * alpha * T ≤ c * alpha * N :=
      mul_le_mul_of_nonneg_left hTN (mul_nonneg hc_pos.le halpha_nonneg)
    linarith
  nlinarith

theorem real_exp_complete_tail_floor_le
    {alpha c cTail T N : ℝ} (halpha_nonneg : 0 ≤ alpha)
    (hc_pos : 0 < c) (hcTail : cTail = c / 2) (hT_le_twoN : T ≤ 2 * N) :
    Real.exp (-(c * alpha * N)) ≤
      Real.exp (-(cTail * alpha * T)) := by
  apply Real.exp_le_exp.mpr
  have hscale : cTail * alpha * T ≤ c * alpha * N := by
    subst cTail
    nlinarith [mul_le_mul_of_nonneg_left hT_le_twoN
      (mul_nonneg (by positivity : 0 ≤ c / 2) halpha_nonneg)]
  nlinarith

theorem real_adjacent_complete_scaled_center_shift_bound
    {Delta gain alpha B T N p : ℝ}
    (hgain_ne : gain ≠ 0) (halpha_ne : alpha ≠ 0)
    (hT_pos : 0 < T) (hN_ne : N ≠ 0)
    (halpha_abs_le_one : |alpha| ≤ 1)
    (hp_nonneg : 0 ≤ p) (hNT_abs : |N - T| ≤ p) :
    |T⁻¹ * (N * (Delta / (gain * alpha * N) + B * alpha)) -
        (Delta / (gain * alpha * T) + B * alpha)| ≤
      |B| * p * T⁻¹ := by
  exact abs_rescale_inv_add_mul_sub_le_of_abs_sub_le hgain_ne halpha_ne
    hT_pos hN_ne halpha_abs_le_one hNT_abs

theorem real_scaled_complete_period_remainder_le_tail
    {Cc alpha T N p expN expT : ℝ}
    (hCc_nonneg : 0 ≤ Cc) (halpha_pos : 0 < alpha)
    (hT_pos : 0 < T) (hN_pos : 0 < N)
    (hp_ge_one : 1 ≤ p) (hN_le_pT : N ≤ p * T)
    (hexp_le : expN ≤ expT) (hexpT_nonneg : 0 ≤ expT) :
    T⁻¹ * (N * (Cc * (N⁻¹ + alpha ^ 2 + expN / (alpha * N)))) ≤
      Cc * p * (T⁻¹ + alpha ^ 2 + expT / (alpha * T)) := by
  exact scaled_complete_horizon_remainder_le hCc_nonneg halpha_pos
    hT_pos hp_ge_one hN_le_pT hexp_le hexpT_nonneg

theorem real_endpoint_coeff_le_of_tail_large
    {Cc A B p e Ctail : ℝ}
    (hCc_nonneg : 0 ≤ Cc) (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hp_ge_one : 1 ≤ p) (he_nonneg : 0 ≤ e)
    (hlarge : ((Cc + A * p + B * p + 1) * (p + 2)) * (e + 1) ≤ Ctail) :
    Cc * p + B * p ≤ Ctail := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_ge_one
  have hp_le_p2 : p ≤ p + 2 := by nlinarith
  have hp2_ge_one : 1 ≤ p + 2 := by nlinarith
  have he1_ge_one : 1 ≤ e + 1 := by nlinarith
  have hAp_nonneg : 0 ≤ A * p := mul_nonneg hA_nonneg hp_nonneg
  have hBp_nonneg : 0 ≤ B * p := mul_nonneg hB_nonneg hp_nonneg
  have hbase_nonneg : 0 ≤ Cc + A * p + B * p + 1 := by nlinarith
  have hcoeff_nonneg : 0 ≤ Cc * p + B * p := by
    exact add_nonneg (mul_nonneg hCc_nonneg hp_nonneg) hBp_nonneg
  have hcoeff_le_base :
      Cc * p + B * p ≤ (Cc + A * p + B * p + 1) * (p + 2) := by
    have hCc_p_le : Cc * p ≤ Cc * (p + 2) :=
      mul_le_mul_of_nonneg_left hp_le_p2 hCc_nonneg
    have hB_p_le : B * p ≤ (B * p) * (p + 2) := by
      calc
        B * p = (B * p) * 1 := by ring
        _ ≤ (B * p) * (p + 2) :=
          mul_le_mul_of_nonneg_left hp2_ge_one hBp_nonneg
    have hsum_le :
        Cc * p + B * p ≤ (Cc + B * p) * (p + 2) := by
      nlinarith
    have hbase_factor :
        (Cc + B * p) * (p + 2) ≤
          (Cc + A * p + B * p + 1) * (p + 2) := by
      have hleft : Cc + B * p ≤ Cc + A * p + B * p + 1 := by nlinarith
      exact mul_le_mul_of_nonneg_right hleft (by nlinarith)
    exact le_trans hsum_le hbase_factor
  have hcoeff_le_large :
      Cc * p + B * p ≤
        ((Cc + A * p + B * p + 1) * (p + 2)) * (e + 1) := by
    have hfactor_nonneg : 0 ≤ (Cc + A * p + B * p + 1) * (p + 2) :=
      mul_nonneg hbase_nonneg (by nlinarith)
    calc
      Cc * p + B * p ≤ (Cc + A * p + B * p + 1) * (p + 2) :=
        hcoeff_le_base
      _ = (Cc + A * p + B * p + 1) * (p + 2) * 1 := by ring
      _ ≤ (Cc + A * p + B * p + 1) * (p + 2) * (e + 1) :=
        mul_le_mul_of_nonneg_left he1_ge_one hfactor_nonneg
  exact le_trans hcoeff_le_large hlarge

theorem real_small_prefix_coeff_le_of_tail_large
    {Cc A B p e Ctail : ℝ}
    (hCc_nonneg : 0 ≤ Cc) (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hp_ge_one : 1 ≤ p) (he_nonneg : 0 ≤ e)
    (hlarge : ((Cc + A * p + B * p + 1) * (p + 2)) * (e + 1) ≤ Ctail) :
    Cc * p + 2 * A * (e + 1) + B * p * (p + 1) ≤ Ctail := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_ge_one
  have hp2_nonneg : 0 ≤ p + 2 := by nlinarith
  have hE_ge_one : 1 ≤ e + 1 := by nlinarith
  have hE_nonneg : 0 ≤ e + 1 := le_trans zero_le_one hE_ge_one
  have hAp_nonneg : 0 ≤ A * p := mul_nonneg hA_nonneg hp_nonneg
  have hBp_nonneg : 0 ≤ B * p := mul_nonneg hB_nonneg hp_nonneg
  have hbase_nonneg : 0 ≤ Cc + A * p + B * p + 1 := by nlinarith
  have hCc_part :
      Cc * p ≤ Cc * (p + 2) * (e + 1) := by
    have h1 : Cc * p ≤ Cc * (p + 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith : p ≤ p + 2) hCc_nonneg
    have h2 : Cc * (p + 2) ≤ Cc * (p + 2) * (e + 1) := by
      calc
        Cc * (p + 2) = Cc * (p + 2) * 1 := by ring
        _ ≤ Cc * (p + 2) * (e + 1) :=
          mul_le_mul_of_nonneg_left hE_ge_one
            (mul_nonneg hCc_nonneg hp2_nonneg)
    exact le_trans h1 h2
  have hA_part :
      2 * A * (e + 1) ≤ A * p * (p + 2) * (e + 1) := by
    have htwo_le : 2 ≤ p * (p + 2) := by nlinarith
    have hA_two : 2 * A ≤ A * p * (p + 2) := by
      calc
        2 * A = A * 2 := by ring
        _ ≤ A * (p * (p + 2)) :=
          mul_le_mul_of_nonneg_left htwo_le hA_nonneg
        _ = A * p * (p + 2) := by ring
    exact mul_le_mul_of_nonneg_right hA_two hE_nonneg
  have hB_part :
      B * p * (p + 1) ≤ B * p * (p + 2) * (e + 1) := by
    have hp1_le_p2 : p + 1 ≤ p + 2 := by nlinarith
    have h1 : B * p * (p + 1) ≤ B * p * (p + 2) :=
      mul_le_mul_of_nonneg_left hp1_le_p2 hBp_nonneg
    have h2 : B * p * (p + 2) ≤ B * p * (p + 2) * (e + 1) := by
      calc
        B * p * (p + 2) = B * p * (p + 2) * 1 := by ring
        _ ≤ B * p * (p + 2) * (e + 1) :=
          mul_le_mul_of_nonneg_left hE_ge_one
            (mul_nonneg hBp_nonneg hp2_nonneg)
    exact le_trans h1 h2
  have hparts :
      Cc * p + 2 * A * (e + 1) + B * p * (p + 1) ≤
        (Cc + A * p + B * p + 1) * (p + 2) * (e + 1) := by
    have hsum :
        Cc * (p + 2) * (e + 1) +
            A * p * (p + 2) * (e + 1) +
            B * p * (p + 2) * (e + 1) ≤
          (Cc + A * p + B * p + 1) * (p + 2) * (e + 1) := by
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        (mul_nonneg hp2_nonneg hE_nonneg)]
    nlinarith
  exact le_trans hparts hlarge

theorem real_fixed_prefix_center_abs_le_tail
    {Delta gain alpha B c T p : ℝ}
    (hgain_ne : gain ≠ 0) (halpha_pos : 0 < alpha)
    (halpha_le_one : alpha ≤ 1) (hc_pos : 0 < c)
    (hT_pos : 0 < T) (hT_le_p : T ≤ p) :
    |Delta / (gain * alpha * T) + B * alpha| ≤
      |Delta / gain| *
          ((Real.exp (c * p) + 1) *
            (Real.exp (-(c * alpha * T)) / (alpha * T))) +
        |B| * p * T⁻¹ := by
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have hden_pos : 0 < alpha * T := mul_pos halpha_pos hT_pos
  have hrecip :
      (alpha * T)⁻¹ ≤
        (Real.exp (c * p) + 1) *
          (Real.exp (-(c * alpha * T)) / (alpha * T)) :=
    real_inv_alpha_time_le_fixed_exp_tail
      (alpha := alpha) (c := c) (T := T) (p := p)
      halpha_pos halpha_le_one hc_pos hT_pos hT_le_p
  have hDelta_abs :
      |Delta / (gain * alpha * T)| =
        |Delta / gain| * (alpha * T)⁻¹ := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos halpha_pos,
      abs_of_pos hT_pos, abs_div]
    field_simp [hgain_ne, halpha_ne, hT_ne]
  have hDelta_bound :
      |Delta / (gain * alpha * T)| ≤
        |Delta / gain| *
          ((Real.exp (c * p) + 1) *
            (Real.exp (-(c * alpha * T)) / (alpha * T))) := by
    rw [hDelta_abs]
    exact mul_le_mul_of_nonneg_left hrecip (abs_nonneg _)
  have halpha_le_p_inv : alpha ≤ p * T⁻¹ := by
    have halphaT_le_p : alpha * T ≤ p := by
      calc
        alpha * T ≤ 1 * T := mul_le_mul_of_nonneg_right halpha_le_one hT_pos.le
        _ = T := one_mul T
        _ ≤ p := hT_le_p
    have h := (le_div_iff₀ hT_pos).mpr halphaT_le_p
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hB_bound : |B * alpha| ≤ |B| * p * T⁻¹ := by
    calc
      |B * alpha| = |B| * alpha := by
        rw [abs_mul, abs_of_pos halpha_pos]
      _ ≤ |B| * (p * T⁻¹) :=
        mul_le_mul_of_nonneg_left halpha_le_p_inv (abs_nonneg _)
      _ = |B| * p * T⁻¹ := by ring
  calc
    |Delta / (gain * alpha * T) + B * alpha|
        ≤ |Delta / (gain * alpha * T)| + |B * alpha| := abs_add_le _ _
    _ ≤
        |Delta / gain| *
            ((Real.exp (c * p) + 1) *
              (Real.exp (-(c * alpha * T)) / (alpha * T))) +
          |B| * p * T⁻¹ :=
      add_le_add hDelta_bound hB_bound

theorem real_scaled_complete_center_abs_le_fixed_tail
    {Delta gain alpha B c T N p : ℝ}
    (hgain_ne : gain ≠ 0) (halpha_pos : 0 < alpha)
    (halpha_le_one : alpha ≤ 1) (hc_pos : 0 < c)
    (hT_pos : 0 < T) (hN_pos : 0 < N)
    (hT_le_p : T ≤ p) (hp_ge_one : 1 ≤ p)
    (hN_le_pT : N ≤ p * T) :
    T⁻¹ * (N * |Delta / (gain * alpha * N) + B * alpha|) ≤
      |Delta / gain| *
          ((Real.exp (c * p) + 1) *
            (Real.exp (-(c * alpha * T)) / (alpha * T))) +
        |B| * p * p * T⁻¹ := by
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_ge_one
  have hTinv_nonneg : 0 ≤ T⁻¹ := inv_nonneg.mpr hT_pos.le
  have hscale_nonneg : 0 ≤ T⁻¹ * N :=
    mul_nonneg hTinv_nonneg hN_pos.le
  have hratio_nonneg : 0 ≤ N * T⁻¹ :=
    mul_nonneg hN_pos.le hTinv_nonneg
  have hratio_le : N * T⁻¹ ≤ p := by
    have h := (div_le_iff₀ hT_pos).mpr hN_le_pT
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hrecip :
      (alpha * T)⁻¹ ≤
        (Real.exp (c * p) + 1) *
          (Real.exp (-(c * alpha * T)) / (alpha * T)) :=
    real_inv_alpha_time_le_fixed_exp_tail
      (alpha := alpha) (c := c) (T := T) (p := p)
      halpha_pos halpha_le_one hc_pos hT_pos hT_le_p
  have hDelta_scaled :
      T⁻¹ * (N * |Delta / (gain * alpha * N)|) =
        |Delta / gain| * (alpha * T)⁻¹ := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos halpha_pos,
      abs_of_pos hN_pos, abs_div]
    field_simp [hgain_ne, halpha_ne, hT_ne, hN_ne]
  have hDelta_bound :
      T⁻¹ * (N * |Delta / (gain * alpha * N)|) ≤
        |Delta / gain| *
          ((Real.exp (c * p) + 1) *
            (Real.exp (-(c * alpha * T)) / (alpha * T))) := by
    rw [hDelta_scaled]
    exact mul_le_mul_of_nonneg_left hrecip (abs_nonneg _)
  have halpha_le_p_inv : alpha ≤ p * T⁻¹ := by
    have halphaT_le_p : alpha * T ≤ p := by
      calc
        alpha * T ≤ 1 * T := mul_le_mul_of_nonneg_right halpha_le_one hT_pos.le
        _ = T := one_mul T
        _ ≤ p := hT_le_p
    have h := (le_div_iff₀ hT_pos).mpr halphaT_le_p
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have halpha_ratio_le : alpha * (N * T⁻¹) ≤ (p * T⁻¹) * p := by
    exact mul_le_mul halpha_le_p_inv hratio_le hratio_nonneg
      (le_trans (le_of_lt halpha_pos) halpha_le_p_inv)
  have hB_bound :
      T⁻¹ * (N * |B * alpha|) ≤ |B| * p * p * T⁻¹ := by
    calc
      T⁻¹ * (N * |B * alpha|)
          = |B| * (alpha * (N * T⁻¹)) := by
            rw [abs_mul, abs_of_pos halpha_pos]
            ring
      _ ≤ |B| * ((p * T⁻¹) * p) :=
            mul_le_mul_of_nonneg_left halpha_ratio_le (abs_nonneg _)
      _ = |B| * p * p * T⁻¹ := by ring
  calc
    T⁻¹ * (N * |Delta / (gain * alpha * N) + B * alpha|)
        ≤ T⁻¹ * (N *
            (|Delta / (gain * alpha * N)| + |B * alpha|)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (abs_add_le _ _) hN_pos.le)
            hTinv_nonneg
    _ =
        T⁻¹ * (N * |Delta / (gain * alpha * N)|) +
          T⁻¹ * (N * |B * alpha|) := by ring
    _ ≤
        |Delta / gain| *
            ((Real.exp (c * p) + 1) *
              (Real.exp (-(c * alpha * T)) / (alpha * T))) +
          |B| * p * p * T⁻¹ :=
        add_le_add hDelta_bound hB_bound

theorem real_upper_add_abs_center_assemble
    {upper center scaledCenter scaledRem remBudget centerBudget target : ℝ}
    (hupper : upper ≤ scaledCenter + scaledRem)
    (hrem : scaledRem ≤ remBudget)
    (hcenter : scaledCenter + center ≤ centerBudget)
    (hbudget : remBudget + centerBudget ≤ target) :
    upper + center ≤ target := by
  linarith

theorem quadraticScalarMomentFunctional_nonneg
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ) (T : ℕ) :
    0 ≤ quad.quadraticScalarMomentFunctional lambda alpha μ oracle T := by
  classical
  unfold quadraticScalarMomentFunctional
  exact mul_nonneg (inv_nonneg.mpr (by exact_mod_cast Nat.zero_le T))
    (Finset.sum_nonneg fun t _ht =>
      MeasureTheory.integral_nonneg fun _ω => sq_nonneg _)

/-- Exact remaining arbitrary-tail assembly for Appendix C.2.  The caller has
already built the adjacent complete-period ceiling and, when `p ≤ T`, floor
comparisons.  This helper is the final real-order step: compare the leading
terms at `T`, `Nceil`, and `Nfloor`, weaken the exponential rate from `c` to
`c/2`, and absorb the at-most-`p-1` finite prefix/suffix by the displayed
constant. -/
theorem quadraticScalarMomentFunctional_tail_cases_from_adjacent_complete
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (alpha c Cc cTail Ctail : ℝ) (T Kceil Nceil : ℕ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (halpha_pos : 0 < alpha) (halpha_le_one : alpha ≤ 1)
    (hc_pos : 0 < c) (hcTail : cTail = c / 2)
    (hT : 1 ≤ T)
    (hceil_cover : T ≤ Nceil)
    (hceil_factor : Nceil ≤ quad.period * T)
    (hceil_near : Nceil ≤ T + quad.period - 1)
    (hCc_nonneg : 0 ≤ Cc)
    (hCtail_nonneg : 0 ≤ Ctail)
    (hCtail_large :
      ((Cc +
          |quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))| * (quad.period : ℝ) +
          |lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))| * (quad.period : ℝ) + 1) *
        ((quad.period : ℝ) + 2)) *
        (Real.exp (cTail * (quad.period : ℝ)) + 1) ≤ Ctail)
    (hupper_sandwich :
      quad.quadraticScalarMomentFunctional lambda alpha μ oracle T ≤
        ((T : ℝ)⁻¹) * ((Nceil : ℝ) *
          quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil))
    (hcomplete_ceiling :
      |quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil -
        (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nceil : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
        Cc * ((Nceil : ℝ)⁻¹ + alpha ^ 2 +
          Real.exp (-(c * alpha * (Nceil : ℝ))) /
            (alpha * (Nceil : ℝ))))
    (hfloor_if_large :
      quad.period ≤ T →
        ∃ Kfloor Nfloor : ℕ,
          Kfloor = T / quad.period ∧
          Nfloor = Kfloor * quad.period ∧
          1 ≤ Kfloor ∧ Nfloor ≤ T ∧ T ≤ 2 * Nfloor ∧
          T - Nfloor ≤ quad.period - 1 ∧
          ((T : ℝ)⁻¹) * ((Nfloor : ℝ) *
              quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor) ≤
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle T ∧
          |quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor -
            (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nfloor : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
            Cc * ((Nfloor : ℝ)⁻¹ + alpha ^ 2 +
              Real.exp (-(c * alpha * (Nfloor : ℝ))) /
                (alpha * (Nfloor : ℝ)))) :
      (quad.period ≤ T →
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
        Ctail *
          ((T : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(cTail * alpha * (T : ℝ))) /
              (alpha * (T : ℝ)))) ∧
      (T < quad.period →
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
        Ctail *
          ((T : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(cTail * alpha * (T : ℝ))) /
              (alpha * (T : ℝ)))) := by
  /- Same-interface source-route attempt artifact.  The large-horizon branch
  uses `real_abs_sub_le_of_sandwich_errors` with the floor/ceiling complete
  periods; the finite-prefix branch uses the ceiling complete period and
  nonnegativity of the moment sum. -/
  classical
  constructor
  · intro hpT
    rcases hfloor_if_large hpT with
      ⟨Kfloor, Nfloor, hKfloor_eq, hNfloor_eq, hKfloor_pos,
        hNfloor_le_T, hT_le_twoNfloor, hfloor_tail,
        hlower_sandwich, hcomplete_floor⟩
    let centerT : ℝ :=
      quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (T : ℝ)) +
        (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
          (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha
    let upperT : ℝ :=
      ((T : ℝ)⁻¹) * ((Nceil : ℝ) *
        quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil)
    let lowerT : ℝ :=
      ((T : ℝ)⁻¹) * ((Nfloor : ℝ) *
        quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor)
    let R : ℝ :=
      Ctail *
        ((T : ℝ)⁻¹ + alpha ^ 2 +
          Real.exp (-(cTail * alpha * (T : ℝ))) /
            (alpha * (T : ℝ)))
    have hendpoint_errors :
        upperT - centerT ≤ R ∧ centerT - lowerT ≤ R := by
      have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
      have hT_real_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
      have hceil_exp_le :
          Real.exp (-(c * alpha * (Nceil : ℝ))) ≤
            Real.exp (-(cTail * alpha * (T : ℝ))) :=
        real_exp_complete_tail_ceiling_le
          (alpha := alpha) (c := c) (cTail := cTail)
          (T := (T : ℝ)) (N := (Nceil : ℝ))
          halpha_nonneg hc_pos hcTail hT_real_nonneg
          (by exact_mod_cast hceil_cover)
      have hfloor_exp_le :
          Real.exp (-(c * alpha * (Nfloor : ℝ))) ≤
            Real.exp (-(cTail * alpha * (T : ℝ))) :=
        real_exp_complete_tail_floor_le
          (alpha := alpha) (c := c) (cTail := cTail)
          (T := (T : ℝ)) (N := (Nfloor : ℝ))
          halpha_nonneg hc_pos hcTail
          (by exact_mod_cast hT_le_twoNfloor)
      /- Exact same-interface large-tail attempt.  The remaining leaf is now
      the endpoint-leading-term comparison: use `hcomplete_ceiling`,
      `hcomplete_floor`, `hceil_cover`, `hceil_factor`, `hT_le_twoNfloor`,
      `hceil_exp_le`, `hfloor_exp_le`, and the caller's enlarged `Ctail`
      to compare the complete-period endpoint centers and remainders with the
      target horizon `T`. -/
      let B : ℝ :=
        lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
          (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
      let tailT : ℝ :=
        (T : ℝ)⁻¹ + alpha ^ 2 +
          Real.exp (-(cTail * alpha * (T : ℝ))) / (alpha * (T : ℝ))
      let centerNceil : ℝ :=
        quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nceil : ℝ)) + B * alpha
      let centerNfloor : ℝ :=
        quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nfloor : ℝ)) + B * alpha
      let remNceil : ℝ :=
        Cc * ((Nceil : ℝ)⁻¹ + alpha ^ 2 +
          Real.exp (-(c * alpha * (Nceil : ℝ))) / (alpha * (Nceil : ℝ)))
      let remNfloor : ℝ :=
        Cc * ((Nfloor : ℝ)⁻¹ + alpha ^ 2 +
          Real.exp (-(c * alpha * (Nfloor : ℝ))) / (alpha * (Nfloor : ℝ)))
      have hT_pos_real : 0 < (T : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
      have hNceil_pos_real : 0 < (Nceil : ℝ) := by
        have hNceil_pos_nat : 0 < Nceil :=
          lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hT) hceil_cover
        exact_mod_cast hNceil_pos_nat
      have hNfloor_pos_real : 0 < (Nfloor : ℝ) := by
        have hNfloor_pos_nat : 0 < Nfloor := by
          rw [hNfloor_eq]
          exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hKfloor_pos)
            quad.period_pos
        exact_mod_cast hNfloor_pos_nat
      have hgain_ne : (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) ≠ 0 :=
        ne_of_gt quad.influenceGain_pos
      have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
      have hNceil_ne : (Nceil : ℝ) ≠ 0 := ne_of_gt hNceil_pos_real
      have hNfloor_ne : (Nfloor : ℝ) ≠ 0 := ne_of_gt hNfloor_pos_real
      have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
        inv_nonneg.mpr hT_pos_real.le
      have hp_ge_one_real : 1 ≤ (quad.period : ℝ) := by
        exact_mod_cast quad.period_pos
      have hp_nonneg_real : 0 ≤ (quad.period : ℝ) :=
        le_trans zero_le_one hp_ge_one_real
      have halpha_abs_le_one : |alpha| ≤ 1 := by
        rw [abs_of_nonneg halpha_nonneg]
        exact halpha_le_one
      have hceil_factor_real :
          (Nceil : ℝ) ≤ (quad.period : ℝ) * (T : ℝ) := by
        exact_mod_cast hceil_factor
      have hfloor_factor_real :
          (Nfloor : ℝ) ≤ (quad.period : ℝ) * (T : ℝ) := by
        have hT_le_pT : T ≤ quad.period * T := by
          nlinarith [quad.period_pos]
        exact_mod_cast (le_trans hNfloor_le_T hT_le_pT)
      have hceil_gap_abs :
          |(Nceil : ℝ) - (T : ℝ)| ≤ (quad.period : ℝ) := by
        have hnear : Nceil ≤ T + quad.period :=
          le_trans hceil_near (Nat.sub_le _ _)
        have hcover_real : (T : ℝ) ≤ (Nceil : ℝ) := by exact_mod_cast hceil_cover
        have hnear_real : (Nceil : ℝ) ≤ (T : ℝ) + (quad.period : ℝ) := by
          exact_mod_cast hnear
        rw [abs_of_nonneg (by linarith : 0 ≤ (Nceil : ℝ) - (T : ℝ))]
        linarith
      have hfloor_gap_abs :
          |(Nfloor : ℝ) - (T : ℝ)| ≤ (quad.period : ℝ) := by
        have hnear : T ≤ Nfloor + quad.period := by omega
        have hle_real : (Nfloor : ℝ) ≤ (T : ℝ) := by exact_mod_cast hNfloor_le_T
        have hnear_real : (T : ℝ) ≤ (Nfloor : ℝ) + (quad.period : ℝ) := by
          exact_mod_cast hnear
        rw [abs_of_nonpos (by linarith : (Nfloor : ℝ) - (T : ℝ) ≤ 0)]
        linarith
      have htailT_nonneg : 0 ≤ tailT := by
        have hden_pos : 0 < alpha * (T : ℝ) := mul_pos halpha_pos hT_pos_real
        have htail_exp_nonneg :
            0 ≤ Real.exp (-(cTail * alpha * (T : ℝ))) /
                (alpha * (T : ℝ)) :=
          div_nonneg (Real.exp_pos _).le hden_pos.le
        dsimp [tailT]
        exact add_nonneg (add_nonneg hTinv_nonneg (sq_nonneg alpha))
          htail_exp_nonneg
      have hTinv_le_tailT : (T : ℝ)⁻¹ ≤ tailT := by
        have hden_pos : 0 < alpha * (T : ℝ) := mul_pos halpha_pos hT_pos_real
        have htail_exp_nonneg :
            0 ≤ Real.exp (-(cTail * alpha * (T : ℝ))) /
                (alpha * (T : ℝ)) :=
          div_nonneg (Real.exp_pos _).le hden_pos.le
        dsimp [tailT]
        calc
          (T : ℝ)⁻¹ ≤
              (T : ℝ)⁻¹ +
                (alpha ^ 2 +
                  Real.exp (-(cTail * alpha * (T : ℝ))) /
                    (alpha * (T : ℝ))) :=
            le_add_of_nonneg_right
              (add_nonneg (sq_nonneg alpha) htail_exp_nonneg)
          _ = (T : ℝ)⁻¹ + alpha ^ 2 +
                Real.exp (-(cTail * alpha * (T : ℝ))) /
                  (alpha * (T : ℝ)) := by ring
      have hcoeff_le :
          Cc * (quad.period : ℝ) + |B| * (quad.period : ℝ) ≤ Ctail := by
        exact real_endpoint_coeff_le_of_tail_large
          (Cc := Cc) (A := |quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))|)
          (B := |B|) (p := (quad.period : ℝ))
          (e := Real.exp (cTail * (quad.period : ℝ))) (Ctail := Ctail)
          hCc_nonneg (abs_nonneg _) (abs_nonneg _) hp_ge_one_real
          (Real.exp_pos _).le (by simpa [B] using hCtail_large)
      have hbudget_endpoint :
          Cc * (quad.period : ℝ) * tailT +
              |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ ≤
            Ctail * tailT := by
        have hBcoeff_nonneg : 0 ≤ |B| * (quad.period : ℝ) :=
          mul_nonneg (abs_nonneg _) hp_nonneg_real
        have hcenter_to_tail :
            |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ ≤
              |B| * (quad.period : ℝ) * tailT :=
          mul_le_mul_of_nonneg_left hTinv_le_tailT hBcoeff_nonneg
        have hsum_tail :
            Cc * (quad.period : ℝ) * tailT +
                |B| * (quad.period : ℝ) * tailT ≤
              Ctail * tailT := by
          calc
            Cc * (quad.period : ℝ) * tailT +
                |B| * (quad.period : ℝ) * tailT
                = (Cc * (quad.period : ℝ) +
                    |B| * (quad.period : ℝ)) * tailT := by ring
            _ ≤ Ctail * tailT :=
              mul_le_mul_of_nonneg_right hcoeff_le htailT_nonneg
        linarith
      have hceil_upper_one :
          quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil ≤
            centerNceil + remNceil := by
        have h := (abs_le.mp hcomplete_ceiling).2
        dsimp [centerNceil, remNceil, B]
        linarith
      have hfloor_lower_one :
          centerNfloor - remNfloor ≤
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor := by
        have h := (abs_le.mp hcomplete_floor).1
        dsimp [centerNfloor, remNfloor, B]
        linarith
      have hceil_scale_nonneg :
          0 ≤ (T : ℝ)⁻¹ * (Nceil : ℝ) :=
        mul_nonneg hTinv_nonneg hNceil_pos_real.le
      have hfloor_scale_nonneg :
          0 ≤ (T : ℝ)⁻¹ * (Nfloor : ℝ) :=
        mul_nonneg hTinv_nonneg hNfloor_pos_real.le
      have hceil_rem_bound :
          (T : ℝ)⁻¹ * ((Nceil : ℝ) * remNceil) ≤
            Cc * (quad.period : ℝ) * tailT := by
        simpa [remNceil, tailT] using
          real_scaled_complete_period_remainder_le_tail
            (Cc := Cc) (alpha := alpha) (T := (T : ℝ))
            (N := (Nceil : ℝ)) (p := (quad.period : ℝ))
            (expN := Real.exp (-(c * alpha * (Nceil : ℝ))))
            (expT := Real.exp (-(cTail * alpha * (T : ℝ))))
            hCc_nonneg halpha_pos hT_pos_real hNceil_pos_real
            hp_ge_one_real hceil_factor_real hceil_exp_le (Real.exp_pos _).le
      have hfloor_rem_bound :
          (T : ℝ)⁻¹ * ((Nfloor : ℝ) * remNfloor) ≤
            Cc * (quad.period : ℝ) * tailT := by
        simpa [remNfloor, tailT] using
          real_scaled_complete_period_remainder_le_tail
            (Cc := Cc) (alpha := alpha) (T := (T : ℝ))
            (N := (Nfloor : ℝ)) (p := (quad.period : ℝ))
            (expN := Real.exp (-(c * alpha * (Nfloor : ℝ))))
            (expT := Real.exp (-(cTail * alpha * (T : ℝ))))
            hCc_nonneg halpha_pos hT_pos_real hNfloor_pos_real
            hp_ge_one_real hfloor_factor_real hfloor_exp_le (Real.exp_pos _).le
      have hceil_center_abs :
          |(T : ℝ)⁻¹ * ((Nceil : ℝ) * centerNceil) - centerT| ≤
            |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := by
        simpa [centerT, centerNceil, B, mul_assoc, mul_left_comm, mul_comm] using
          real_adjacent_complete_scaled_center_shift_bound
            (Delta := quad.Delta) (gain := (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
            (alpha := alpha) (B := B) (T := (T : ℝ))
            (N := (Nceil : ℝ)) (p := (quad.period : ℝ))
            hgain_ne halpha_ne hT_pos_real hNceil_ne halpha_abs_le_one
            hp_nonneg_real hceil_gap_abs
      have hfloor_center_abs :
          |(T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor) - centerT| ≤
            |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := by
        simpa [centerT, centerNfloor, B, mul_assoc, mul_left_comm, mul_comm] using
          real_adjacent_complete_scaled_center_shift_bound
            (Delta := quad.Delta) (gain := (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
            (alpha := alpha) (B := B) (T := (T : ℝ))
            (N := (Nfloor : ℝ)) (p := (quad.period : ℝ))
            hgain_ne halpha_ne hT_pos_real hNfloor_ne halpha_abs_le_one
            hp_nonneg_real hfloor_gap_abs
      constructor
      · have hupper_decomp :
            upperT ≤
              (T : ℝ)⁻¹ * ((Nceil : ℝ) * centerNceil) +
                (T : ℝ)⁻¹ * ((Nceil : ℝ) * remNceil) := by
          calc
            upperT =
                ((T : ℝ)⁻¹ * (Nceil : ℝ)) *
                  quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil := by
              simp [upperT]
              ring
            _ ≤ ((T : ℝ)⁻¹ * (Nceil : ℝ)) *
                  (centerNceil + remNceil) :=
              mul_le_mul_of_nonneg_left hceil_upper_one hceil_scale_nonneg
            _ =
                (T : ℝ)⁻¹ * ((Nceil : ℝ) * centerNceil) +
                  (T : ℝ)⁻¹ * ((Nceil : ℝ) * remNceil) := by ring
        have hcenter_one :
            (T : ℝ)⁻¹ * ((Nceil : ℝ) * centerNceil) - centerT ≤
              |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ :=
          le_trans (le_abs_self _) hceil_center_abs
        have :
            upperT - centerT ≤
              Cc * (quad.period : ℝ) * tailT +
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := by
          calc
            upperT - centerT ≤
                ((T : ℝ)⁻¹ * ((Nceil : ℝ) * centerNceil) +
                    (T : ℝ)⁻¹ * ((Nceil : ℝ) * remNceil)) - centerT :=
              sub_le_sub_right hupper_decomp centerT
            _ =
                ((T : ℝ)⁻¹ * ((Nceil : ℝ) * centerNceil) - centerT) +
                  (T : ℝ)⁻¹ * ((Nceil : ℝ) * remNceil) := by ring
            _ ≤
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ +
                  (T : ℝ)⁻¹ * ((Nceil : ℝ) * remNceil) :=
              add_le_add_left hcenter_one _
            _ ≤
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ +
                  Cc * (quad.period : ℝ) * tailT :=
              add_le_add_right hceil_rem_bound _
            _ =
                Cc * (quad.period : ℝ) * tailT +
                  |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := by ring
        calc
          upperT - centerT ≤
              Cc * (quad.period : ℝ) * tailT +
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := this
          _ ≤ Ctail * tailT := hbudget_endpoint
          _ = R := by rfl
      · have hlower_decomp :
            (T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor) -
                (T : ℝ)⁻¹ * ((Nfloor : ℝ) * remNfloor) ≤ lowerT := by
          calc
            (T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor) -
                (T : ℝ)⁻¹ * ((Nfloor : ℝ) * remNfloor)
                = ((T : ℝ)⁻¹ * (Nfloor : ℝ)) *
                    (centerNfloor - remNfloor) := by ring
            _ ≤ ((T : ℝ)⁻¹ * (Nfloor : ℝ)) *
                  quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor :=
              mul_le_mul_of_nonneg_left hfloor_lower_one hfloor_scale_nonneg
            _ = lowerT := by
              simp [lowerT]
              ring
        have hcenter_one :
            centerT - (T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor) ≤
              |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := by
          have hneg :
              centerT - (T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor) =
                -((T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor) - centerT) := by
            ring
          rw [hneg]
          exact le_trans (neg_le_abs _) hfloor_center_abs
        have :
            centerT - lowerT ≤
              Cc * (quad.period : ℝ) * tailT +
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := by
          calc
            centerT - lowerT ≤
                centerT -
                  ((T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor) -
                    (T : ℝ)⁻¹ * ((Nfloor : ℝ) * remNfloor)) :=
              sub_le_sub_left hlower_decomp centerT
            _ =
                (centerT - (T : ℝ)⁻¹ * ((Nfloor : ℝ) * centerNfloor)) +
                  (T : ℝ)⁻¹ * ((Nfloor : ℝ) * remNfloor) := by ring
            _ ≤
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ +
                  (T : ℝ)⁻¹ * ((Nfloor : ℝ) * remNfloor) :=
              add_le_add_left hcenter_one _
            _ ≤
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ +
                  Cc * (quad.period : ℝ) * tailT :=
              add_le_add_right hfloor_rem_bound _
            _ =
                Cc * (quad.period : ℝ) * tailT +
                  |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := by ring
        calc
          centerT - lowerT ≤
              Cc * (quad.period : ℝ) * tailT +
                |B| * (quad.period : ℝ) * (T : ℝ)⁻¹ := this
          _ ≤ Ctail * tailT := hbudget_endpoint
          _ = R := by rfl
    exact real_abs_sub_le_of_sandwich_errors
      (lower := lowerT) (x := quad.quadraticScalarMomentFunctional
        lambda alpha μ oracle T) (upper := upperT) (center := centerT)
      (R := R) hlower_sandwich hupper_sandwich
      hendpoint_errors.1 hendpoint_errors.2
  · intro hsmallT
    have hfixed_prefix :
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
        Ctail *
          ((T : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(cTail * alpha * (T : ℝ))) /
              (alpha * (T : ℝ))) := by
      have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
      have hT_real_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
      have hceil_exp_le :
          Real.exp (-(c * alpha * (Nceil : ℝ))) ≤
            Real.exp (-(cTail * alpha * (T : ℝ))) :=
        real_exp_complete_tail_ceiling_le
          (alpha := alpha) (c := c) (cTail := cTail)
          (T := (T : ℝ)) (N := (Nceil : ℝ))
          halpha_nonneg hc_pos hcTail hT_real_nonneg
          (by exact_mod_cast hceil_cover)
      let centerT : ℝ :=
        quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (T : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha
      let centerN : ℝ :=
        quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nceil : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha
      let remN : ℝ :=
        Cc * ((Nceil : ℝ)⁻¹ + alpha ^ 2 +
          Real.exp (-(c * alpha * (Nceil : ℝ))) /
            (alpha * (Nceil : ℝ)))
      let upperT : ℝ :=
        ((T : ℝ)⁻¹) * ((Nceil : ℝ) *
          quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil)
      let targetR : ℝ :=
        Ctail *
          ((T : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(cTail * alpha * (T : ℝ))) /
              (alpha * (T : ℝ)))
      change
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
          centerT| ≤ targetR
      have hMN_abs :
          |quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil| ≤
            |centerN| + remN := by
        exact real_abs_le_abs_center_add_radius
          (x := quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil)
          (center := centerN) (radius := remN)
          (by simpa [centerN, remN] using hcomplete_ceiling)
      have hMT_to_upper :
          |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
              centerT| ≤ upperT + |centerT| := by
        exact real_abs_sub_le_upper_add_abs_of_nonneg
          (x := quad.quadraticScalarMomentFunctional lambda alpha μ oracle T)
          (upper := upperT) (center := centerT)
          (quadraticScalarMomentFunctional_nonneg
            (Node := Node) quad lambda alpha μ oracle T)
          (by simpa [upperT] using hupper_sandwich)
      have hfixed_absorb : upperT + |centerT| ≤ targetR := by
        /- Exact remaining coefficient-absorption leaf.  The available facts
        are now formula-level: `hMN_abs`, `hceil_cover`, `hceil_factor`,
        `hceil_near`, `halpha_le_one`, `hceil_exp_le`, and
        `real_inv_alpha_time_le_fixed_exp_tail` dominate the finite prefix by
        the enlarged `Ctail`. -/
        let B : ℝ :=
          lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
        let A : ℝ := |quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))|
        let Babs : ℝ := |B|
        let p : ℝ := (quad.period : ℝ)
        let e : ℝ := Real.exp (cTail * p)
        let expTail : ℝ :=
          Real.exp (-(cTail * alpha * (T : ℝ))) / (alpha * (T : ℝ))
        let tailT : ℝ := (T : ℝ)⁻¹ + alpha ^ 2 + expTail
        let scaledCenter : ℝ := (T : ℝ)⁻¹ * ((Nceil : ℝ) * |centerN|)
        let scaledRem : ℝ := (T : ℝ)⁻¹ * ((Nceil : ℝ) * remN)
        let centerBudget : ℝ :=
          2 * A * (e + 1) * expTail +
            Babs * p * (p + 1) * (T : ℝ)⁻¹
        change upperT + |centerT| ≤ Ctail * tailT
        have hT_pos_real : 0 < (T : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
        have hT_le_p_real : (T : ℝ) ≤ p := by
          have hT_le_period : T ≤ quad.period := Nat.le_of_lt hsmallT
          dsimp [p]
          exact_mod_cast hT_le_period
        have hNceil_pos_real : 0 < (Nceil : ℝ) := by
          have hNceil_pos_nat : 0 < Nceil :=
            lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hT) hceil_cover
          exact_mod_cast hNceil_pos_nat
        have hp_ge_one_real : 1 ≤ p := by
          dsimp [p]
          exact_mod_cast quad.period_pos
        have hp_nonneg_real : 0 ≤ p := le_trans zero_le_one hp_ge_one_real
        have hceil_factor_real : (Nceil : ℝ) ≤ p * (T : ℝ) := by
          dsimp [p]
          exact_mod_cast hceil_factor
        have hcTail_pos : 0 < cTail := by
          rw [hcTail]
          nlinarith
        have hgain_ne : (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) ≠ 0 :=
          ne_of_gt quad.influenceGain_pos
        have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
          inv_nonneg.mpr hT_pos_real.le
        have hden_pos : 0 < alpha * (T : ℝ) :=
          mul_pos halpha_pos hT_pos_real
        have hexpTail_nonneg : 0 ≤ expTail := by
          dsimp [expTail]
          exact div_nonneg (Real.exp_pos _).le hden_pos.le
        have htailT_nonneg : 0 ≤ tailT := by
          dsimp [tailT]
          exact add_nonneg (add_nonneg hTinv_nonneg (sq_nonneg alpha))
            hexpTail_nonneg
        have hTinv_le_tailT : (T : ℝ)⁻¹ ≤ tailT := by
          dsimp [tailT]
          calc
            (T : ℝ)⁻¹ ≤
                (T : ℝ)⁻¹ + (alpha ^ 2 + expTail) :=
              le_add_of_nonneg_right
                (add_nonneg (sq_nonneg alpha) hexpTail_nonneg)
            _ = (T : ℝ)⁻¹ + alpha ^ 2 + expTail := by ring
        have hexpTail_le_tailT : expTail ≤ tailT := by
          dsimp [tailT]
          calc
            expTail ≤ ((T : ℝ)⁻¹ + alpha ^ 2) + expTail :=
              le_add_of_nonneg_left
                (add_nonneg hTinv_nonneg (sq_nonneg alpha))
            _ = (T : ℝ)⁻¹ + alpha ^ 2 + expTail := by ring
        have hceil_scale_nonneg :
            0 ≤ (T : ℝ)⁻¹ * (Nceil : ℝ) :=
          mul_nonneg hTinv_nonneg hNceil_pos_real.le
        have hmomentN_nonneg :
            0 ≤ quad.quadraticScalarMomentFunctional
              lambda alpha μ oracle Nceil :=
          quadraticScalarMomentFunctional_nonneg
            (Node := Node) quad lambda alpha μ oracle Nceil
        have hmomentN_le :
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil ≤
              |centerN| + remN := by
          calc
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil
                = |quad.quadraticScalarMomentFunctional
                    lambda alpha μ oracle Nceil| := by
                  rw [abs_of_nonneg hmomentN_nonneg]
            _ ≤ |centerN| + remN := hMN_abs
        have hupper_decomp :
            upperT ≤ scaledCenter + scaledRem := by
          calc
            upperT =
                ((T : ℝ)⁻¹ * (Nceil : ℝ)) *
                  quad.quadraticScalarMomentFunctional
                    lambda alpha μ oracle Nceil := by
              simp [upperT]
              ring
            _ ≤ ((T : ℝ)⁻¹ * (Nceil : ℝ)) * (|centerN| + remN) :=
              mul_le_mul_of_nonneg_left hmomentN_le hceil_scale_nonneg
            _ =
                (T : ℝ)⁻¹ * ((Nceil : ℝ) * |centerN|) +
                  (T : ℝ)⁻¹ * ((Nceil : ℝ) * remN) := by ring
            _ = scaledCenter + scaledRem := by rfl
        have hrem_bound :
            scaledRem ≤ Cc * p * tailT := by
          simpa [scaledRem, remN, p, tailT, expTail] using
            real_scaled_complete_period_remainder_le_tail
              (Cc := Cc) (alpha := alpha) (T := (T : ℝ))
              (N := (Nceil : ℝ)) (p := p)
              (expN := Real.exp (-(c * alpha * (Nceil : ℝ))))
              (expT := Real.exp (-(cTail * alpha * (T : ℝ))))
              hCc_nonneg halpha_pos hT_pos_real hNceil_pos_real
              hp_ge_one_real hceil_factor_real hceil_exp_le
              (Real.exp_pos _).le
        have hcenterN_bound :
            scaledCenter ≤
              A * ((e + 1) * expTail) +
                Babs * p * p * (T : ℝ)⁻¹ := by
          simpa [scaledCenter, centerN, B, A, Babs, p, e, expTail, mul_assoc,
            mul_left_comm, mul_comm] using
            real_scaled_complete_center_abs_le_fixed_tail
              (Delta := quad.Delta) (gain := (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
              (alpha := alpha) (B := B) (c := cTail)
              (T := (T : ℝ)) (N := (Nceil : ℝ)) (p := p)
              hgain_ne halpha_pos halpha_le_one hcTail_pos
              hT_pos_real hNceil_pos_real hT_le_p_real hp_ge_one_real
              hceil_factor_real
        have hcenterT_bound :
            |centerT| ≤
              A * ((e + 1) * expTail) +
                Babs * p * (T : ℝ)⁻¹ := by
          simpa [centerT, B, A, Babs, p, e, expTail, mul_assoc,
            mul_left_comm, mul_comm] using
            real_fixed_prefix_center_abs_le_tail
              (Delta := quad.Delta) (gain := (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))
              (alpha := alpha) (B := B) (c := cTail)
              (T := (T : ℝ)) (p := p)
              hgain_ne halpha_pos halpha_le_one hcTail_pos
              hT_pos_real hT_le_p_real
        have hcenter_sum_bound :
            scaledCenter + |centerT| ≤ centerBudget := by
          calc
            scaledCenter + |centerT| ≤
                (A * ((e + 1) * expTail) +
                    Babs * p * p * (T : ℝ)⁻¹) +
                  (A * ((e + 1) * expTail) +
                    Babs * p * (T : ℝ)⁻¹) :=
              add_le_add hcenterN_bound hcenterT_bound
            _ =
                2 * A * (e + 1) * expTail +
                  Babs * p * (p + 1) * (T : ℝ)⁻¹ := by ring
            _ = centerBudget := by rfl
        have hcoeff_le :
            Cc * p + 2 * A * (e + 1) + Babs * p * (p + 1) ≤ Ctail := by
          exact real_small_prefix_coeff_le_of_tail_large
            (Cc := Cc) (A := A) (B := Babs) (p := p)
            (e := e) (Ctail := Ctail) hCc_nonneg
            (by dsimp [A]; exact abs_nonneg _)
            (by dsimp [Babs]; exact abs_nonneg _)
            hp_ge_one_real (by dsimp [e]; exact (Real.exp_pos _).le)
            (by simpa [B, A, Babs, p, e] using hCtail_large)
        have hbudget :
            Cc * p * tailT + centerBudget ≤
              Ctail * tailT := by
          have hA_nonneg : 0 ≤ A := by
            dsimp [A]
            exact abs_nonneg _
          have hBabs_nonneg : 0 ≤ Babs := by
            dsimp [Babs]
            exact abs_nonneg _
          have he_nonneg : 0 ≤ e := by
            dsimp [e]
            exact (Real.exp_pos _).le
          have he1_nonneg : 0 ≤ e + 1 :=
            add_nonneg he_nonneg zero_le_one
          have hcenter_coeff_nonneg : 0 ≤ 2 * A * (e + 1) :=
            mul_nonneg (mul_nonneg (by norm_num) hA_nonneg) he1_nonneg
          have hp1_nonneg : 0 ≤ p + 1 :=
            add_nonneg hp_nonneg_real zero_le_one
          have hB_coeff_nonneg : 0 ≤ Babs * p * (p + 1) :=
            mul_nonneg (mul_nonneg hBabs_nonneg hp_nonneg_real) hp1_nonneg
          have hcenter_tail :
              2 * A * (e + 1) * expTail ≤
                2 * A * (e + 1) * tailT :=
            mul_le_mul_of_nonneg_left hexpTail_le_tailT hcenter_coeff_nonneg
          have hB_tail :
              Babs * p * (p + 1) * (T : ℝ)⁻¹ ≤
                Babs * p * (p + 1) * tailT :=
            mul_le_mul_of_nonneg_left hTinv_le_tailT hB_coeff_nonneg
          have hsum_tail :
              Cc * p * tailT +
                  2 * A * (e + 1) * tailT +
                  Babs * p * (p + 1) * tailT ≤
                Ctail * tailT := by
            calc
              Cc * p * tailT +
                  2 * A * (e + 1) * tailT +
                  Babs * p * (p + 1) * tailT
                  =
                    (Cc * p + 2 * A * (e + 1) +
                      Babs * p * (p + 1)) * tailT := by ring
              _ ≤ Ctail * tailT :=
                mul_le_mul_of_nonneg_right hcoeff_le htailT_nonneg
          calc
            Cc * p * tailT + centerBudget
                =
                  Cc * p * tailT +
                    (2 * A * (e + 1) * expTail +
                      Babs * p * (p + 1) * (T : ℝ)⁻¹) := by ring
            _ ≤
                  Cc * p * tailT +
                    (2 * A * (e + 1) * tailT +
                      Babs * p * (p + 1) * tailT) :=
                add_le_add (le_refl _) (add_le_add hcenter_tail hB_tail)
            _ =
                  Cc * p * tailT +
                    2 * A * (e + 1) * tailT +
                    Babs * p * (p + 1) * tailT := by ring
            _ ≤ Ctail * tailT := hsum_tail
        exact real_upper_add_abs_center_assemble
          hupper_decomp hrem_bound hcenter_sum_bound hbudget
      exact le_trans hMT_to_upper hfixed_absorb
    exact hfixed_prefix

/-- Appendix C.2 arbitrary-horizon tail assembly.  Once the complete-period
bound is available, adding or deleting at most `p - 1` fixed phases changes
the scalar moment average by `O(T^{-1})`, producing the uniform statement
for every `T ≥ 1`. -/
theorem quadraticScalarMomentFunctional_tail_bound
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hcomplete :
      ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            |quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                (K * quad.period) -
              (quad.Delta /
                  ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha *
                    ((K * quad.period : ℕ) : ℝ)) +
                (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
            C * ((((K * quad.period : ℕ) : ℝ)⁻¹) + alpha ^ 2 +
              Real.exp (-(c * alpha *
                ((K * quad.period : ℕ) : ℝ))) /
                (alpha * ((K * quad.period : ℕ) : ℝ)))) :
    QuadraticScalarMomentExpansion (Node := Node) quad lambda μ oracle := by
  classical
  obtain ⟨alphaC, c, Cc, halphaC_pos, hc_pos, hCc_nonneg, hcomplete_bound⟩ :=
    hcomplete
  let alphaTail : ℝ := min alphaC 1
  let cTail : ℝ := c / 2
  let Ctail : ℝ :=
    ((Cc +
        |quad.Delta / (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))| * (quad.period : ℝ) +
        |lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))| * (quad.period : ℝ) + 1) *
      ((quad.period : ℝ) + 2)) *
      (Real.exp (cTail * (quad.period : ℝ)) + 1)
  /- Source leaf, Appendix C.2 lines 1681-1682.  The complete-period estimate
  is now applied at both adjacent complete block horizons.  The tail export
  uses the weaker exponential rate `c/2`, which is the source-compatible rate
  needed when the floor complete horizon is only known to satisfy
  `T <= 2 * Nfloor`. -/
  refine ⟨alphaTail, cTail, Ctail, ?_, ?_, ?_, ?_⟩
  · exact lt_min halphaC_pos zero_lt_one
  · exact half_pos hc_pos
  · positivity
  intro alpha halpha_pos halpha_le T hT
  have halpha_leC : alpha ≤ alphaC :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_le_one : alpha ≤ 1 :=
    le_trans halpha_le (min_le_right _ _)
  let Kceil : ℕ := (T - 1) / quad.period + 1
  let Nceil : ℕ := Kceil * quad.period
  have hceil_facts :=
    quadraticScalar_completePeriod_ceiling_facts
      (Node := Node) quad T hT
  change 1 ≤ Kceil ∧ T ≤ Nceil ∧ Kceil ≤ T ∧
      Nceil ≤ quad.period * T ∧ Nceil ≤ T + quad.period - 1 ∧
        Nceil - T ≤ quad.period - 1 at hceil_facts
  rcases hceil_facts with
    ⟨hKceil_pos, hT_le_Nceil, hKceil_le_T, hNceil_le_pT,
      hNceil_near, hNceil_sub⟩
  have hupper_sandwich :
      quad.quadraticScalarMomentFunctional lambda alpha μ oracle T ≤
        ((T : ℝ)⁻¹) * ((Nceil : ℝ) *
          quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil) :=
    quadraticScalarMomentFunctional_le_scaled_complete
      (Node := Node) quad lambda alpha μ oracle hT_le_Nceil hT
  have hcomplete_ceiling :
      |quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nceil -
        (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nceil : ℝ)) +
          (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
            (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
        Cc * ((Nceil : ℝ)⁻¹ + alpha ^ 2 +
          Real.exp (-(c * alpha * (Nceil : ℝ))) /
            (alpha * (Nceil : ℝ))) := by
    simpa [Nceil] using
      hcomplete_bound alpha halpha_pos halpha_leC Kceil hKceil_pos
  have hfloor_if_large :
      quad.period ≤ T →
        ∃ Kfloor Nfloor : ℕ,
          Kfloor = T / quad.period ∧
          Nfloor = Kfloor * quad.period ∧
          1 ≤ Kfloor ∧ Nfloor ≤ T ∧ T ≤ 2 * Nfloor ∧
          T - Nfloor ≤ quad.period - 1 ∧
          ((T : ℝ)⁻¹) * ((Nfloor : ℝ) *
              quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor) ≤
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle T ∧
          |quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor -
            (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nfloor : ℝ)) +
              (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
            Cc * ((Nfloor : ℝ)⁻¹ + alpha ^ 2 +
              Real.exp (-(c * alpha * (Nfloor : ℝ))) /
                (alpha * (Nfloor : ℝ))) := by
    intro hpT
    let Kfloor : ℕ := T / quad.period
    let Nfloor : ℕ := Kfloor * quad.period
    have hfloor_facts :=
      quadraticScalar_completePeriod_floor_facts
        (Node := Node) quad T hpT
    change 1 ≤ Kfloor ∧ Nfloor ≤ T ∧ T ≤ 2 * Nfloor ∧
      T - Nfloor ≤ quad.period - 1 at hfloor_facts
    rcases hfloor_facts with
      ⟨hKfloor_pos, hNfloor_le_T, hT_le_twoNfloor, hfloor_tail⟩
    have hlower_sandwich :
        ((T : ℝ)⁻¹) * ((Nfloor : ℝ) *
            quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor) ≤
          quad.quadraticScalarMomentFunctional lambda alpha μ oracle T :=
      quadraticScalarMomentFunctional_scaled_prefix_le
        (Node := Node) quad lambda alpha μ oracle hNfloor_le_T hT
    have hcomplete_floor :
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle Nfloor -
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (Nfloor : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
          Cc * ((Nfloor : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(c * alpha * (Nfloor : ℝ))) /
              (alpha * (Nfloor : ℝ))) := by
      simpa [Nfloor] using
        hcomplete_bound alpha halpha_pos halpha_leC Kfloor hKfloor_pos
    exact ⟨Kfloor, Nfloor, rfl, rfl, hKfloor_pos, hNfloor_le_T,
      hT_le_twoNfloor, hfloor_tail, hlower_sandwich, hcomplete_floor⟩
  have htail_cases :
      (quad.period ≤ T →
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
        Ctail *
          ((T : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(cTail * alpha * (T : ℝ))) /
              (alpha * (T : ℝ)))) ∧
      (T < quad.period →
        |quad.quadraticScalarMomentFunctional lambda alpha μ oracle T -
          (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha * (T : ℝ)) +
            (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
              (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
        Ctail *
          ((T : ℝ)⁻¹ + alpha ^ 2 +
            Real.exp (-(cTail * alpha * (T : ℝ))) /
              (alpha * (T : ℝ)))) := by
    exact quadraticScalarMomentFunctional_tail_cases_from_adjacent_complete
      (Node := Node) quad lambda μ oracle alpha c Cc cTail
      Ctail T Kceil Nceil hquad halpha_pos halpha_le_one hc_pos rfl hT
      hT_le_Nceil hNceil_le_pT hNceil_near hCc_nonneg (by positivity)
      (by
        dsimp [Ctail]
        rfl)
      hupper_sandwich hcomplete_ceiling hfloor_if_large
  exact (lt_or_ge T quad.period).elim htail_cases.2 htail_cases.1

/-- Assembly bridge for the uniform scalar moment expansion once the source
leaves for block variance, bias, steady variance, and multiplier squeeze are
available.  The remaining proof here is the finite-phase and non-multiple-of-
period bookkeeping from the last paragraphs of Appendix C.2. -/
theorem quadraticScalarMomentExpansion_from_source_bridges
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hnoise : quad.ExactVarianceIidAdditiveNoise μ oracle)
    (hcomplete_to_steady :
      ∃ alpha0 Cphase Ctransient : ℝ,
        0 < alpha0 ∧ 0 ≤ Cphase ∧ 0 ≤ Ctransient ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
            ∀ K : ℕ, 1 ≤ K →
              let T : ℝ := ((K * quad.period : ℕ) : ℝ)
              let steadyAverage : ℝ :=
                lambda ^ 2 * (K : ℝ)⁻¹ *
                  ((Finset.range K).sum fun k =>
                    quadraticScalarSteadyBoundaryVariance (Node := Node)
                      quad lambda alpha
                      (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                        quad lambda alpha μ oracle k))
              |(quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                    (K * quad.period) -
                  quadraticScalarBiasBlockAverage (Node := Node)
                    quad lambda alpha K) -
                steadyAverage| ≤
              Cphase * alpha ^ 2 + Ctransient * T⁻¹)
    (hsqueeze :
      ∃ alpha0 c1 c2 : ℝ,
        0 < alpha0 ∧ 0 < c1 ∧ 0 < c2 ∧ c1 ≤ c2 ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
            1 - c2 * alpha ≤
                quadraticScalarPeriodMultiplier (Node := Node)
                  quad lambda alpha ∧
              quadraticScalarPeriodMultiplier (Node := Node)
                  quad lambda alpha ≤ 1 - c1 * alpha ∧
                0 < 1 -
                  quadraticScalarPeriodMultiplier (Node := Node)
                    quad lambda alpha ^ 2)
    (hblock :
      ∀ k : ℕ,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k -
              alpha ^ 2 * quad.sigma ^ 2 *
                (quad.period : ℝ) * quad.influenceSecondMoment)
          (fun alpha : ℝ => alpha ^ 3))
    (hblock_uniform :
      ∃ alpha0 C : ℝ, 0 < alpha0 ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, |alpha| < alpha0 →
          ∀ k : ℕ,
            |quadraticScalarBlockInnovationSecondMoment (Node := Node)
                quad lambda alpha μ oracle k -
              alpha ^ 2 * quad.sigma ^ 2 *
                (quad.period : ℝ) * quad.influenceSecondMoment| ≤
            C * |alpha| ^ 3)
    (hbias :
      ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            |quadraticScalarBiasBlockAverage (Node := Node)
                quad lambda alpha K -
              quad.Delta /
                ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha *
                  ((K * quad.period : ℕ) : ℝ))| ≤
              C * ((((K * quad.period : ℕ) : ℝ)⁻¹) +
                Real.exp (-(c * alpha *
                  ((K * quad.period : ℕ) : ℝ))) /
                  (alpha * ((K * quad.period : ℕ) : ℝ))))
    (hsteady :
      ∀ k : ℕ,
        Asymptotics.IsBigO (nhds 0)
          (fun alpha : ℝ =>
            quadraticScalarSteadyBoundaryVariance (Node := Node)
                quad lambda alpha
                (quadraticScalarBlockInnovationSecondMoment (Node := Node)
                  quad lambda alpha μ oracle k) -
              (alpha * quad.sigma ^ 2 * quad.influenceSecondMoment /
                (2 * lambda * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))))
          (fun alpha : ℝ => alpha ^ 2)) :
    QuadraticScalarMomentExpansion (Node := Node) quad lambda μ oracle := by
  have hcomplete :
      ∃ alpha0 c C : ℝ, 0 < alpha0 ∧ 0 < c ∧ 0 ≤ C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          ∀ K : ℕ, 1 ≤ K →
            |quad.quadraticScalarMomentFunctional lambda alpha μ oracle
                (K * quad.period) -
              (quad.Delta /
                  ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alpha *
                    ((K * quad.period : ℕ) : ℝ)) +
                (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
                  (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alpha)| ≤
            C * ((((K * quad.period : ℕ) : ℝ)⁻¹) + alpha ^ 2 +
              Real.exp (-(c * alpha *
                ((K * quad.period : ℕ) : ℝ))) /
                (alpha * ((K * quad.period : ℕ) : ℝ))) :=
    quadraticScalarMomentFunctional_completePeriod_expansion_bound
      (Node := Node) quad lambda μ oracle hquad hnoise
      hcomplete_to_steady hsqueeze hblock hblock_uniform hbias hsteady
  exact quadraticScalarMomentFunctional_tail_bound
    (Node := Node) quad lambda μ oracle hquad hnoise hcomplete

/-- Real filter cleanup for Appendix C.2: under `alpha_T -> 0` and
`alpha_T*T -> infinity`, the uniform scalar remainder in (8.7) is negligible
relative to the two displayed leading scales. -/
theorem quadraticScalarUniformRemainder_isLittleO_scale
    {alphaSeq : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ᶠ T in Filter.atTop, 0 < alphaSeq T)
    (halpha : Filter.Tendsto alphaSeq Filter.atTop (nhds 0))
    (hprod : Filter.Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ))
      Filter.atTop Filter.atTop) :
    Asymptotics.IsLittleO Filter.atTop
      (fun T : ℕ =>
        (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
          Real.exp (-(c * alphaSeq T * (T : ℝ))) /
            (alphaSeq T * (T : ℝ)))
      (fun T : ℕ => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T) := by
  exact Asymptotics.isLittleO_inv_add_sq_add_exp_div_of_tendsto_zero_mul_atTop
    hc halpha hprod

/-- Appendix C.2 asymptotic consequence obtained from the uniform scalar
moment expansion by taking `alpha_T -> 0` and `alpha_T*T -> infinity`. -/
theorem quadraticScalarMomentAsymptotic_from_uniformExpansion
    (quad : Setup Node ℝ) (lambda : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (hscalar :
      QuadraticScalarMomentExpansion (Node := Node)
        quad lambda μ oracle) :
    QuadraticScalarMomentAsymptoticConsequence (Node := Node)
      quad lambda μ oracle := by
  classical
  rcases hscalar with ⟨alpha0, c, C, halpha0_pos, hc_pos, hC_nonneg,
    hbound⟩
  intro alphaSeq hpos halpha hprod
  have hsmall_abs :
      ∀ᶠ T : ℕ in Filter.atTop, dist (alphaSeq T) 0 < alpha0 :=
    (Metric.tendsto_nhds.mp halpha) alpha0 halpha0_pos
  have hsmall :
      ∀ᶠ T : ℕ in Filter.atTop, alphaSeq T ≤ alpha0 := by
    filter_upwards [hsmall_abs] with T hT
    have habs : |alphaSeq T| < alpha0 := by
      simpa [Real.dist_eq] using hT
    exact le_trans (le_abs_self (alphaSeq T)) (le_of_lt habs)
  have hT_ge_one : ∀ᶠ T : ℕ in Filter.atTop, 1 ≤ T :=
    Filter.eventually_atTop.2 ⟨1, fun T hT => hT⟩
  let err : ℕ → ℝ := fun T =>
    quad.quadraticScalarMomentFunctional lambda (alphaSeq T) μ oracle T -
      (quad.Delta / ((Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) * alphaSeq T * (T : ℝ)) +
        (lambda * quad.sigma ^ 2 * quad.influenceSecondMoment /
          (2 * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) * alphaSeq T)
  let rem : ℕ → ℝ := fun T =>
    (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
      Real.exp (-(c * alphaSeq T * (T : ℝ))) /
        (alphaSeq T * (T : ℝ))
  have herr_bigO : Asymptotics.IsBigO Filter.atTop err rem := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [hpos, hsmall, hT_ge_one] with T hposT hsmallT hT1
    have hboundT := hbound (alphaSeq T) hposT hsmallT T hT1
    have hT_nonneg : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    have hden_nonneg : 0 ≤ alphaSeq T * (T : ℝ) :=
      mul_nonneg (le_of_lt hposT) hT_nonneg
    have hrem_nonneg : 0 ≤ rem T := by
      dsimp [rem]
      exact add_nonneg
        (add_nonneg (inv_nonneg.mpr hT_nonneg) (sq_nonneg (alphaSeq T)))
        (div_nonneg (Real.exp_nonneg _) hden_nonneg)
    simpa [err, rem, Real.norm_eq_abs, abs_of_nonneg hrem_nonneg] using hboundT
  have hrem_littleO :
      Asymptotics.IsLittleO Filter.atTop rem
        (fun T : ℕ => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T) := by
    simpa [rem, mul_assoc] using
      quadraticScalarUniformRemainder_isLittleO_scale
        (alphaSeq := alphaSeq) hc_pos hpos halpha hprod
  exact herr_bigO.trans_isLittleO hrem_littleO

/-- Appendix C.1: the quadratic averaged process stays within `O(alpha^2)` of
the scalar comparison process on `0 < alpha ≤ alpha0`, `alpha*T ≥ 1`. -/
theorem average_l2_triangle_combine_two_errors
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (actual slow stable scalar : Ω → ℕ → ℝ)
    {T : ℕ} {Cslow Cstable alpha : ℝ}
    (hslow_int :
      ∀ t : ℕ, Integrable
        (fun ω : Ω => |slow ω t - scalar ω t| ^ 2) μ)
    (hstable_int :
      ∀ t : ℕ, Integrable
        (fun ω : Ω => |stable ω t| ^ 2) μ)
    (htotal_int :
      ∀ t : ℕ, Integrable
        (fun ω : Ω => |actual ω t - scalar ω t| ^ 2) μ)
    (hdecomp :
      ∀ (ω : Ω) (t : ℕ),
        actual ω t - scalar ω t =
          (slow ω t - scalar ω t) + stable ω t)
    (hslow_bound :
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |slow ω t - scalar ω t| ^ 2 ∂μ) ≤
        Cslow * alpha ^ 2)
    (hstable_bound :
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |stable ω t| ^ 2 ∂μ) ≤
        Cstable * alpha ^ 2) :
    ((T : ℝ)⁻¹) *
      Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |actual ω t - scalar ω t| ^ 2 ∂μ) ≤
      (2 * Cslow + 2 * Cstable + 1) * alpha ^ 2 := by
  have hbound :=
    finite_average_integral_norm_sq_add_le_of_component_bounds
      (mu := μ)
      (a := fun ω t => slow ω t - scalar ω t)
      (b := stable)
      (total := fun ω t => actual ω t - scalar ω t)
      (fun t _ht => by simpa [Real.norm_eq_abs] using hslow_int t)
      (fun t _ht => by simpa [Real.norm_eq_abs] using hstable_int t)
      (fun t _ht => by simpa [Real.norm_eq_abs] using htotal_int t)
      (fun t _ht ω => hdecomp ω t)
      hslow_bound hstable_bound
  have hslack :
      (2 * Cslow + 2 * Cstable) * alpha ^ 2 ≤
        (2 * Cslow + 2 * Cstable + 1) * alpha ^ 2 := by
    nlinarith [sq_nonneg alpha]
  simpa [Real.norm_eq_abs] using hbound.trans hslack

/-- Raw-time slow/scalar error controlled by the block representative plus an
explicit finite within-period remainder.

This is the source-shaped pointwise algebra for Appendix C.1 step 7.  The
block representative is `(t / p) * p`; the remaining terms are exactly the
within-period motions that must be given an averaged budget by the model
recurrences. -/
theorem quadraticRestrictedSlowOutput_raw_time_error_sq_le_block_boundary_add_within_period_remainder
    (actual stable scalar : ℕ → ℝ) (p : ℕ)
    (g blockR : ℕ → ℝ) {Cphase : ℝ}
    (hblock :
      ∀ k : ℕ,
        |(actual (k * p) - stable (k * p)) - scalar (k * p)| ^ 2 ≤
          Cphase * g k + blockR k)
    (t : ℕ) :
    |(actual t - stable t) - scalar t| ^ 2 ≤
      (2 * Cphase) * g (t / p) +
        (2 * blockR (t / p) +
          6 * |actual t - actual ((t / p) * p)| ^ 2 +
          6 * |stable t - stable ((t / p) * p)| ^ 2 +
          6 * |scalar t - scalar ((t / p) * p)| ^ 2) := by
  classical
  let k : ℕ := t / p
  let b : ℕ := k * p
  let blockErr : ℝ := (actual b - stable b) - scalar b
  let da : ℝ := actual t - actual b
  let ds : ℝ := stable t - stable b
  let dc : ℝ := scalar t - scalar b
  have hdecomp :
      (actual t - stable t) - scalar t = blockErr + (da - ds - dc) := by
    dsimp [blockErr, da, ds, dc, b]
    ring
  have htri :
      |(actual t - stable t) - scalar t| ^ 2 ≤
        2 * |blockErr| ^ 2 + 2 * |da - ds - dc| ^ 2 := by
    rw [hdecomp]
    exact real_abs_add_sq_le_two_sq blockErr (da - ds - dc)
  have hdelta :
      |da - ds - dc| ^ 2 ≤
        3 * |da| ^ 2 + 3 * |ds| ^ 2 + 3 * |dc| ^ 2 := by
    have hpoly :
        (da + (-ds) + (-dc)) ^ 2 ≤
          3 * (da ^ 2 + (-ds) ^ 2 + (-dc) ^ 2) := by
      nlinarith [sq_nonneg (da - (-ds)), sq_nonneg (da - (-dc)),
        sq_nonneg ((-ds) - (-dc))]
    have hrewrite : da - ds - dc = da + (-ds) + (-dc) := by ring
    rw [hrewrite]
    calc
      |da + (-ds) + (-dc)| ^ 2 ≤
          3 * (da ^ 2 + (-ds) ^ 2 + (-dc) ^ 2) := by
          simpa [sq_abs] using hpoly
      _ = 3 * |da| ^ 2 + 3 * |ds| ^ 2 + 3 * |dc| ^ 2 := by
          rw [sq_abs da, sq_abs ds, sq_abs dc]
          ring
  have hblock_k :
      |blockErr| ^ 2 ≤ Cphase * g k + blockR k := by
    simpa [blockErr, b, k] using hblock k
  calc
    |(actual t - stable t) - scalar t| ^ 2 ≤
        2 * |blockErr| ^ 2 + 2 * |da - ds - dc| ^ 2 := htri
    _ ≤
        (2 * Cphase) * g k +
          (2 * blockR k + 6 * |da| ^ 2 + 6 * |ds| ^ 2 +
            6 * |dc| ^ 2) := by
          nlinarith [hblock_k, hdelta]
    _ =
        (2 * Cphase) * g (t / p) +
          (2 * blockR (t / p) +
            6 * |actual t - actual ((t / p) * p)| ^ 2 +
            6 * |stable t - stable ((t / p) * p)| ^ 2 +
            6 * |scalar t - scalar ((t / p) * p)| ^ 2) := by
          simpa [k, b, da, ds, dc]

/-- Finite phase-to-block averaging algebra for Appendix C.1 step 7.

If each all-time squared error term is dominated by a finite-phase constant
times the corresponding block-boundary error at block `t / p`, then the first
`T` all-time terms are controlled by the first `T` block-boundary terms.  The
point is that this preserves the source hypothesis `alpha * T >= 1`: no
replacement by a shorter ceiling block horizon is needed. -/
theorem finite_phase_average_l2_bound_of_block_majorant
    (p : ℕ) (hp : 0 < p)
    (f g : ℕ → ℝ) {T : ℕ} {Cphase Cblock alpha : ℝ}
    (hCphase_nonneg : 0 ≤ Cphase)
    (hf_nonneg : ∀ t : ℕ, 0 ≤ f t)
    (hg_nonneg : ∀ k : ℕ, 0 ≤ g k)
    (hphase : ∀ t : ℕ, f t ≤ Cphase * g (t / p))
    (hblock :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) g ≤
        Cblock * alpha ^ 2) :
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) f ≤
      (Cphase * (p : ℝ) * Cblock) * alpha ^ 2 := by
  simpa only [mul_assoc] using
    normalized_sum_le_period_mul_of_floor_div_majorant
      p T f g Cphase (Cblock * alpha ^ 2) hp hCphase_nonneg
        (fun k _hk => hg_nonneg k) (fun t _ht => hphase t) hblock

/-- Finite phase-to-block averaging with an explicit averaged source
remainder.

This is the algebraic shape needed when the within-period propagation
majorant contains finite-window terms that have their own averaged
`O(alpha^2)` budget. -/
theorem finite_phase_average_l2_bound_of_block_majorant_add_remainder
    (p : ℕ) (hp : 0 < p)
    (f g r : ℕ → ℝ) {T : ℕ} {Cphase Cblock Crem alpha : ℝ}
    (hCphase_nonneg : 0 ≤ Cphase)
    (hg_nonneg : ∀ k : ℕ, 0 ≤ g k)
    (hphase : ∀ t : ℕ, f t ≤ Cphase * g (t / p) + r t)
    (hblock :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) g ≤
        Cblock * alpha ^ 2)
    (hremainder :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) r ≤
        Crem * alpha ^ 2) :
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) f ≤
      (Cphase * (p : ℝ) * Cblock + Crem) * alpha ^ 2 := by
  simpa only [mul_assoc, add_mul] using
    normalized_sum_le_period_mul_add_of_floor_div_majorant
      p T f g r Cphase (Cblock * alpha ^ 2) (Crem * alpha ^ 2)
        hp hCphase_nonneg (fun k _hk => hg_nonneg k)
          (fun t _ht => hphase t) hblock hremainder

/-- Sampling an averaged nonnegative sequence at period multiples costs only the
finite period factor.

This is the algebraic part of the stable-response index-mismatch budget: an
existing all-raw-time average bound also controls the subsequence `k * p`,
after reindexing through complete blocks. -/
theorem sampled_multiples_average_bound_of_average_bound
    (p : ℕ) (hp : 1 ≤ p)
    (e : ℕ → ℝ) {T : ℕ} {C alpha : ℝ}
    (he_nonneg : ∀ t : ℕ, 0 ≤ e t)
    (havg :
      ∀ N : ℕ, 1 ≤ alpha * (N : ℝ) →
        ((N : ℝ)⁻¹) * Finset.sum (Finset.range N) e ≤
          C * alpha ^ 2)
    (halphaT : 1 ≤ alpha * (T : ℝ)) :
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun k => e (k * p)) ≤
      ((p : ℝ) * C) * alpha ^ 2 := by
  have hp_pos : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have halphaTp : 1 ≤ alpha * ((T * p : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have hp_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith [halphaT]
  simpa [mul_assoc] using
    normalized_sum_stride_mul_le_period_mul_normalized_sum
      p T e (C * alpha ^ 2) hp_pos he_nonneg (havg (T * p) halphaTp)

/-- Average `L²` budget for a sampled-index mismatch.

If `e t` is the square budget for a process at raw time `t`, then the mismatch
`out k - out (k * p)` is controlled by the raw average plus the sampled-multiple
average.  This packages the exact remainder algebra needed after the block-start
slow/scalar majorant exposes `stableResponse k - stableResponse (k * period)`. -/
theorem average_l2_index_mismatch_bound_of_average_bound
    (p : ℕ) (hp : 1 ≤ p)
    (d e : ℕ → ℝ) {T : ℕ} {C alpha : ℝ}
    (he_nonneg : ∀ t : ℕ, 0 ≤ e t)
    (hd : ∀ k : ℕ, d k ≤ 2 * e k + 2 * e (k * p))
    (havg :
      ∀ N : ℕ, 1 ≤ alpha * (N : ℝ) →
        ((N : ℝ)⁻¹) * Finset.sum (Finset.range N) e ≤
          C * alpha ^ 2)
    (halphaT : 1 ≤ alpha * (T : ℝ)) :
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) d ≤
      (2 * C + 2 * ((p : ℝ) * C)) * alpha ^ 2 := by
  have hp_pos : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have halphaTp : 1 ≤ alpha * ((T * p : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have hp_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith [halphaT]
  simpa [mul_add, add_mul, mul_assoc] using
    normalized_sum_mismatch_le_two_add_two_period_mul_of_average_bound
      p T d e (C * alpha ^ 2) hp_pos (fun t _ht => he_nonneg t)
      (fun k _hk => hd k)
      (havg T halphaT) (havg (T * p) halphaTp)

/-- Measure-facing version of the sampled-index mismatch budget.

This is intended to be applied with `out t` equal to the scalar output of the
canonical stable boundary response.  The only analytic input is the already
proved averaged `L²` bound for `out`; the theorem supplies the exposed
`out k - out (k * p)` remainder budget. -/
theorem average_l2_index_mismatch_integral_bound_of_average_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (out : Ω → ℕ → ℝ) {T : ℕ} {C alpha : ℝ}
    (hout_int :
      ∀ t : ℕ, Integrable (fun ω : Ω => |out ω t| ^ 2) μ)
    (hdiff_int :
      ∀ k : ℕ,
        Integrable (fun ω : Ω => |out ω k - out ω (k * p)| ^ 2) μ)
    (havg :
      ∀ N : ℕ, 1 ≤ alpha * (N : ℝ) →
        ((N : ℝ)⁻¹) *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, |out ω t| ^ 2 ∂μ) ≤
          C * alpha ^ 2)
    (halphaT : 1 ≤ alpha * (T : ℝ)) :
    ((T : ℝ)⁻¹) *
      Finset.sum (Finset.range T) (fun k =>
        ∫ ω, |out ω k - out ω (k * p)| ^ 2 ∂μ) ≤
      (2 * C + 2 * ((p : ℝ) * C)) * alpha ^ 2 := by
  have hp_pos : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have halphaTp : 1 ≤ alpha * ((T * p : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have hp_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith [halphaT]
  simpa [Real.norm_eq_abs, mul_add, add_mul, mul_assoc] using
    finite_average_integral_norm_sq_stride_mismatch_le
      μ out p T (C * alpha ^ 2) hp_pos
      (fun t _ht => by simpa [Real.norm_eq_abs] using hout_int t)
      (havg T halphaT) (havg (T * p) halphaTp)

/-- Average `L²` budget for a mismatch against the complete-period floor
representative `(t / p) * p`.

The proof uses only the raw averaged `L²` bound for the process and finite
phase reindexing.  This is the generic algebraic part of the C.1
within-period stable remainder budget; actual and scalar processes still need
their own source-backed raw averaged bounds before this can close the complete
explicit remainder. -/
theorem average_l2_floor_block_mismatch_integral_bound_of_average_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (out : Ω → ℕ → ℝ) {T : ℕ} {C alpha : ℝ}
    (hout_int :
      ∀ t : ℕ, Integrable (fun ω : Ω => |out ω t| ^ 2) μ)
    (hdiff_int :
      ∀ t : ℕ,
        Integrable
          (fun ω : Ω => |out ω t - out ω ((t / p) * p)| ^ 2) μ)
    (havg :
      ∀ N : ℕ, 1 ≤ alpha * (N : ℝ) →
        ((N : ℝ)⁻¹) *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, |out ω t| ^ 2 ∂μ) ≤
          C * alpha ^ 2)
    (halphaT : 1 ≤ alpha * (T : ℝ)) :
    ((T : ℝ)⁻¹) *
      Finset.sum (Finset.range T) (fun t =>
        ∫ ω, |out ω t - out ω ((t / p) * p)| ^ 2 ∂μ) ≤
      (2 * C + 2 * ((p : ℝ) * ((p : ℝ) * C))) * alpha ^ 2 := by
  have hp_pos : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have halphaTp : 1 ≤ alpha * ((T * p : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have hp_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith [halphaT]
  have hbase :=
    finite_average_integral_norm_sq_floor_block_mismatch_le_of_average_bound
      μ out p T (C * alpha ^ 2) hp_pos
      (fun t _ht => by simpa [Real.norm_eq_abs] using hout_int t)
      (havg T halphaT) (havg (T * p) halphaTp)
  calc
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |out ω t - out ω ((t / p) * p)| ^ 2 ∂μ) ≤
      2 * (C * alpha ^ 2) +
        2 * ((p : ℝ) * ((p : ℝ) * (C * alpha ^ 2))) := by
      simpa [Real.norm_eq_abs] using hbase
    _ = (2 * C + 2 * ((p : ℝ) * ((p : ℝ) * C))) * alpha ^ 2 := by
      ring

/-- Deterministic finite-window path estimate against the complete-period floor
representative.

This is the pathwise algebra behind within-period motion budgets: a displacement
inside one block is controlled by the sum of adjacent increments across the
whole block. -/
theorem real_sq_floor_block_mismatch_le_period_increment_sum
    (p : ℕ) (hp : 1 ≤ p) (out : ℕ → ℝ) (t : ℕ) :
    |out t - out ((t / p) * p)| ^ 2 ≤
      (p : ℝ) *
        Finset.sum (Finset.range p) (fun j =>
          |out ((t / p) * p + j + 1) -
            out ((t / p) * p + j)| ^ 2) := by
  simpa [Real.norm_eq_abs] using
    norm_sq_sub_floor_block_le_period_mul_sum_increment_norm_sq
      (p := p) (hp := lt_of_lt_of_le Nat.zero_lt_one hp) out t

/-- Average floor-block displacement from a raw adjacent-increment budget.

This is the reusable aggregation layer needed for Appendix C.1 finite
within-period propagation: future actual/scalar motion proofs only need to
supply a normalized one-step increment square budget over `T * p`. -/
theorem average_l2_floor_block_mismatch_integral_bound_of_increment_average_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (out : Ω → ℕ → ℝ) {T : ℕ} {C alpha : ℝ}
    (hinc_int :
      ∀ u : ℕ,
        Integrable
          (fun ω : Ω => |out ω (u + 1) - out ω u| ^ 2) μ)
    (hinc_avg :
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range (T * p)) (fun u =>
          ∫ ω, |out ω (u + 1) - out ω u| ^ 2 ∂μ) ≤
        C * alpha ^ 2) :
    ((T : ℝ)⁻¹) *
      Finset.sum (Finset.range T) (fun t =>
        ∫ ω, |out ω t - out ω ((t / p) * p)| ^ 2 ∂μ) ≤
      ((p : ℝ) ^ 2 * C) * alpha ^ 2 := by
  simpa only [Real.norm_eq_abs, mul_assoc] using
    finite_average_integral_norm_sq_floor_block_mismatch_le_of_increment_bound
      μ out p T (C * alpha ^ 2) (lt_of_lt_of_le Nat.zero_lt_one hp)
      (fun u _hu => by simpa only [Real.norm_eq_abs] using hinc_int u)
      hinc_avg

/-- Convert Section 6 displacement energy into an adjacent-increment budget for
the arithmetic average iterate.

This is the local bridge needed before applying the finite floor-block
aggregator: Jensen controls each scalar average increment by the corresponding
Frobenius displacement of the generated primal state, and summing folds exactly
to `displacementEnergy`. -/
theorem actual_average_increment_budget_from_displacement_energy
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (alpha Cd : ℝ) (T p : ℕ)
    (horacle :
      (quad.withStepsize alpha).StochasticOracleAssumptions μ oracle)
    (hT_pos : 0 < T)
    (hD :
      (quad.withStepsize alpha).displacementEnergy μ oracle (T * p) ≤
        Cd * alpha ^ 2 * (T : ℝ)) :
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range (T * p)) (fun u =>
          ∫ ω,
            |(quad.withStepsize alpha).averageIterate
                (oracle.noise ω) (u + 1) -
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) u| ^ 2 ∂μ) ≤
      (((nodeCount (Node := Node) : ℝ)⁻¹) * Cd) * alpha ^ 2 := by
  classical
  let stepped := quad.withStepsize alpha
  let nodeInv : ℝ := (nodeCount (Node := Node) : ℝ)⁻¹
  have hnodeInv_nonneg : 0 ≤ nodeInv := by
    dsimp [nodeInv]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hstep :
      ∀ u, u ∈ Finset.range (T * p) → ∀ i : Node,
        MemLp
          (fun ω : Ω =>
            stepped.primalState (oracle.noise ω) (u + 1) i -
              stepped.primalState (oracle.noise ω) u i) 2 μ := by
    intro u _hu i
    exact
      ((stepped.generated_pushpull_coordinate_memLp
          μ oracle horacle (u + 1)).1 i).sub
        ((stepped.generated_pushpull_coordinate_memLp
          μ oracle horacle u).1 i)
  have hsum :
      Finset.sum (Finset.range (T * p)) (fun u =>
          ∫ ω,
            |stepped.averageIterate (oracle.noise ω) (u + 1) -
              stepped.averageIterate (oracle.noise ω) u| ^ 2 ∂μ) ≤
        nodeInv * stepped.displacementEnergy μ oracle (T * p) := by
    have hmean :=
      finite_sum_integral_norm_sq_finite_mean_increment_le_coordinate_energy
        μ
        (fun ω t i => stepped.primalState (oracle.noise ω) t i)
        (T * p) hstep
    simpa [nodeInv, nodeCount, averageIterate, arithmeticAverage,
      SOptLib.finiteUniformAverage_def, displacementEnergy, frobeniusNormSq,
      Real.norm_eq_abs, sq_abs] using hmean
  have hsum_bound :
      Finset.sum (Finset.range (T * p)) (fun u =>
          ∫ ω,
            |stepped.averageIterate (oracle.noise ω) (u + 1) -
              stepped.averageIterate (oracle.noise ω) u| ^ 2 ∂μ) ≤
        nodeInv * (Cd * alpha ^ 2 * (T : ℝ)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hD hnodeInv_nonneg)
  have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  have hT_ne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT_pos)
  calc
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range (T * p)) (fun u =>
          ∫ ω,
            |(quad.withStepsize alpha).averageIterate
                (oracle.noise ω) (u + 1) -
              (quad.withStepsize alpha).averageIterate
                (oracle.noise ω) u| ^ 2 ∂μ) ≤
        ((T : ℝ)⁻¹) *
          (nodeInv * (Cd * alpha ^ 2 * (T : ℝ))) := by
        simpa [stepped] using
          mul_le_mul_of_nonneg_left hsum_bound hTinv_nonneg
    _ = (((nodeCount (Node := Node) : ℝ)⁻¹) * Cd) * alpha ^ 2 := by
        dsimp [nodeInv]
        field_simp [hT_ne]

/-- Finite floor-block propagation for the true arithmetic average, assuming a
Section-6 style displacement-energy budget has already been supplied. -/
theorem actual_floor_block_average_l2_bound_of_displacement_energy_budget
    (quad : Setup Node ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (oracle : OracleNoiseProcess Ω Node ℝ)
    (p : ℕ) (hp : 1 ≤ p)
    (alphaD Cd : ℝ)
    (halphaD_pos : 0 < alphaD) (hCd_nonneg : 0 ≤ Cd)
    (horacle :
      ∀ alpha : ℝ,
        (quad.withStepsize alpha).StochasticOracleAssumptions μ oracle)
    (hD_budget :
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaD →
        ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
          (quad.withStepsize alpha).displacementEnergy μ oracle (T * p) ≤
            Cd * alpha ^ 2 * (T : ℝ)) :
    ∃ alphaActualFloor CactualFloor : ℝ,
      0 < alphaActualFloor ∧ 0 ≤ CactualFloor ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaActualFloor →
          ∀ T : ℕ, 1 ≤ alpha * (T : ℝ) →
            ((T : ℝ)⁻¹) *
              Finset.sum (Finset.range T) (fun t =>
                ∫ ω,
                  |(quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) t -
                    (quad.withStepsize alpha).averageIterate
                      (oracle.noise ω) ((t / p) * p)| ^ 2 ∂μ) ≤
              CactualFloor * alpha ^ 2 := by
  classical
  let Cinc : ℝ := ((nodeCount (Node := Node) : ℝ)⁻¹) * Cd
  refine ⟨alphaD, (p : ℝ) ^ 2 * Cinc, halphaD_pos, ?_, ?_⟩
  · have hnodeInv_nonneg : 0 ≤ (nodeCount (Node := Node) : ℝ)⁻¹ := by
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    dsimp [Cinc]
    positivity
  · intro alpha halpha_pos halpha_le T halphaT
    let stepped := quad.withStepsize alpha
    let out : Ω → ℕ → ℝ := fun ω t =>
      stepped.averageIterate (oracle.noise ω) t
    have hT_pos : 0 < T := by
      by_contra hnot
      have hT_zero : T = 0 := by omega
      simp [hT_zero] at halphaT
      norm_num at halphaT
    have hinc_int :
        ∀ u : ℕ,
          Integrable
            (fun ω : Ω => |out ω (u + 1) - out ω u| ^ 2) μ := by
      intro u
      have havg_next_mem :
          MemLp
            (fun ω : Ω =>
              stepped.averageIterate (oracle.noise ω) (u + 1)) 2 μ := by
        have hgenerated :=
          stepped.generated_pushpull_coordinate_memLp μ oracle
            (horacle alpha) (u + 1)
        have hsum :
            MemLp
              (fun ω : Ω =>
                ∑ i : Node,
                  stepped.primalState (oracle.noise ω) (u + 1) i) 2 μ := by
          apply memLp_finset_sum Finset.univ
          intro i _hi
          exact hgenerated.1 i
        simpa [averageIterate, arithmeticAverage] using
          hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
      have havg_cur_mem :
          MemLp
            (fun ω : Ω =>
              stepped.averageIterate (oracle.noise ω) u) 2 μ := by
        have hgenerated :=
          stepped.generated_pushpull_coordinate_memLp μ oracle
            (horacle alpha) u
        have hsum :
            MemLp
              (fun ω : Ω =>
                ∑ i : Node, stepped.primalState (oracle.noise ω) u i)
              2 μ := by
          apply memLp_finset_sum Finset.univ
          intro i _hi
          exact hgenerated.1 i
        simpa [averageIterate, arithmeticAverage] using
          hsum.const_smul ((nodeCount (Node := Node) : ℝ)⁻¹)
      exact real_abs_sq_integrable_of_memLp_two
        (havg_next_mem.sub havg_cur_mem)
    have hinc_avg :
        ((T : ℝ)⁻¹) *
            Finset.sum (Finset.range (T * p)) (fun u =>
              ∫ ω, |out ω (u + 1) - out ω u| ^ 2 ∂μ) ≤
          Cinc * alpha ^ 2 := by
      simpa [Cinc, out, stepped] using
        actual_average_increment_budget_from_displacement_energy
          (Node := Node) quad μ oracle alpha Cd T p (horacle alpha)
          hT_pos (hD_budget alpha halpha_pos halpha_le T halphaT)
    have hfloor :=
      average_l2_floor_block_mismatch_integral_bound_of_increment_average_bound
        (μ := μ) (p := p) hp out (T := T) (C := Cinc)
        (alpha := alpha) hinc_int hinc_avg
    simpa [out, stepped, Cinc] using hfloor

/-- Assemble the explicit within-period remainder from separately budgeted
component averages.

This is the constant-refinement algebra for Appendix C.1 step 7: once the
stable sampled-index, actual floor-block, stable floor-block, and scalar
floor-block components each have an averaged `O(alpha²)` budget, the displayed
raw remainder has the corresponding weighted budget. -/
theorem finite_phase_remainder_average_bound_of_component_bounds
    (r stableSample actualFloor stableFloor scalarFloor : ℕ → ℝ)
    {T : ℕ} {CstableSample CactualFloor CstableFloor CscalarFloor alpha : ℝ}
    (hr :
      ∀ t : ℕ,
        r t ≤
          4 * stableSample t + 6 * actualFloor t +
            6 * stableFloor t + 6 * scalarFloor t)
    (hstableSample :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) stableSample ≤
        CstableSample * alpha ^ 2)
    (hactualFloor :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) actualFloor ≤
        CactualFloor * alpha ^ 2)
    (hstableFloor :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) stableFloor ≤
        CstableFloor * alpha ^ 2)
    (hscalarFloor :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) scalarFloor ≤
        CscalarFloor * alpha ^ 2) :
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) r ≤
      (4 * CstableSample + 6 * CactualFloor +
          6 * CstableFloor + 6 * CscalarFloor) * alpha ^ 2 := by
  classical
  have hsum :
      Finset.sum (Finset.range T) r ≤
        4 * Finset.sum (Finset.range T) stableSample +
          6 * Finset.sum (Finset.range T) actualFloor +
          6 * Finset.sum (Finset.range T) stableFloor +
          6 * Finset.sum (Finset.range T) scalarFloor := by
    calc
      Finset.sum (Finset.range T) r ≤
          Finset.sum (Finset.range T) (fun t =>
            4 * stableSample t + 6 * actualFloor t +
              6 * stableFloor t + 6 * scalarFloor t) :=
            Finset.sum_le_sum fun t _ht => hr t
      _ =
          4 * Finset.sum (Finset.range T) stableSample +
            6 * Finset.sum (Finset.range T) actualFloor +
            6 * Finset.sum (Finset.range T) stableFloor +
            6 * Finset.sum (Finset.range T) scalarFloor := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hTinv_nonneg : 0 ≤ (T : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  calc
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) r ≤
        ((T : ℝ)⁻¹) *
          (4 * Finset.sum (Finset.range T) stableSample +
            6 * Finset.sum (Finset.range T) actualFloor +
            6 * Finset.sum (Finset.range T) stableFloor +
            6 * Finset.sum (Finset.range T) scalarFloor) :=
        mul_le_mul_of_nonneg_left hsum hTinv_nonneg
    _ =
        4 * (((T : ℝ)⁻¹) * Finset.sum (Finset.range T) stableSample) +
          6 * (((T : ℝ)⁻¹) * Finset.sum (Finset.range T) actualFloor) +
          6 * (((T : ℝ)⁻¹) * Finset.sum (Finset.range T) stableFloor) +
          6 * (((T : ℝ)⁻¹) * Finset.sum (Finset.range T) scalarFloor) := by
        ring
    _ ≤
        4 * (CstableSample * alpha ^ 2) +
          6 * (CactualFloor * alpha ^ 2) +
          6 * (CstableFloor * alpha ^ 2) +
          6 * (CscalarFloor * alpha ^ 2) := by
        gcongr
    _ =
        (4 * CstableSample + 6 * CactualFloor +
            6 * CstableFloor + 6 * CscalarFloor) * alpha ^ 2 := by
        ring

/-- Stable-response contributions to the explicit finite-phase remainder.

The sampled term has one extra finite-phase reindexing layer because the
remainder contains `out (t / p) - out ((t / p) * p)`, not just
`out t - out (t * p)`.  The same raw averaged `L²` estimate also controls the
same-time floor-block term. -/
theorem stable_phase_remainder_components_average_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (out : Ω → ℕ → ℝ) {T : ℕ} {C alpha : ℝ}
    (hout_int :
      ∀ t : ℕ, Integrable (fun ω : Ω => |out ω t| ^ 2) μ)
    (hindex_int :
      ∀ k : ℕ,
        Integrable (fun ω : Ω => |out ω k - out ω (k * p)| ^ 2) μ)
    (hfloor_int :
      ∀ t : ℕ,
        Integrable
          (fun ω : Ω => |out ω t - out ω ((t / p) * p)| ^ 2) μ)
    (havg :
      ∀ N : ℕ, 1 ≤ alpha * (N : ℝ) →
        ((N : ℝ)⁻¹) *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, |out ω t| ^ 2 ∂μ) ≤
          C * alpha ^ 2)
    (halphaT : 1 ≤ alpha * (T : ℝ)) :
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |out ω (t / p) - out ω ((t / p) * p)| ^ 2 ∂μ) ≤
      ((p : ℝ) * (2 * C + 2 * ((p : ℝ) * C))) * alpha ^ 2 ∧
    ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T) (fun t =>
          ∫ ω, |out ω t - out ω ((t / p) * p)| ^ 2 ∂μ) ≤
      (2 * C + 2 * ((p : ℝ) * ((p : ℝ) * C))) * alpha ^ 2 := by
  have halphaTp : 1 ≤ alpha * ((T * p : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have hp_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith [halphaT]
  simpa [Real.norm_eq_abs, mul_add, add_mul, mul_assoc] using
    finite_average_integral_norm_sq_block_mismatch_pair_le_of_average_bound
      μ out p T (C * alpha ^ 2) (lt_of_lt_of_le Nat.zero_lt_one hp)
      (fun t _ht => by simpa [Real.norm_eq_abs] using hout_int t)
      (havg T halphaT) (havg (T * p) halphaTp)

/-- Measure-level finite-phase bridge with the stable-response index mismatch
already budgeted.

This is the route-local assembly needed after the source proof supplies a
pointwise raw-phase majorant: the all-raw-time error average is controlled by
the block-boundary projected/scalar average plus the canonical stable-response
index mismatch `out t - out (t * p)`. -/
theorem finite_phase_average_l2_integral_bound_of_block_majorant_and_stable_mismatch
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (p : ℕ) (hp : 1 ≤ p)
    (f g : ℕ → ℝ) (out : Ω → ℕ → ℝ)
    {T : ℕ} {Cphase Cblock Cstable alpha : ℝ}
    (hCphase_nonneg : 0 ≤ Cphase)
    (hg_nonneg : ∀ k : ℕ, 0 ≤ g k)
    (hout_int :
      ∀ t : ℕ, Integrable (fun ω : Ω => |out ω t| ^ 2) μ)
    (hdiff_int :
      ∀ t : ℕ,
        Integrable (fun ω : Ω => |out ω t - out ω (t * p)| ^ 2) μ)
    (hphase :
      ∀ t : ℕ,
        f t ≤
          Cphase * g (t / p) +
            ∫ ω, |out ω t - out ω (t * p)| ^ 2 ∂μ)
    (hblock :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) g ≤
        Cblock * alpha ^ 2)
    (hstable :
      ∀ N : ℕ, 1 ≤ alpha * (N : ℝ) →
        ((N : ℝ)⁻¹) *
          Finset.sum (Finset.range N) (fun t =>
            ∫ ω, |out ω t| ^ 2 ∂μ) ≤
          Cstable * alpha ^ 2)
    (halphaT : 1 ≤ alpha * (T : ℝ)) :
    ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) f ≤
      (Cphase * (p : ℝ) * Cblock +
          (2 * Cstable + 2 * ((p : ℝ) * Cstable))) * alpha ^ 2 := by
  simpa [Real.norm_eq_abs, mul_add, add_mul, mul_assoc] using
    finite_average_le_of_floor_div_majorant_and_integral_stride_mismatch
      μ p T f g out Cphase (Cblock * alpha ^ 2)
        (Cstable * alpha ^ 2) (lt_of_lt_of_le Nat.zero_lt_one hp)
        hCphase_nonneg (fun k _hk => hg_nonneg k)
        (fun t _ht => by simpa [Real.norm_eq_abs] using hout_int t)
        (fun t _ht => by simpa [Real.norm_eq_abs] using hphase t)
        hblock (hstable T halphaT)
        (hstable (T * p) (by
          rw [Nat.cast_mul]
          have hp_real : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
          nlinarith [halphaT]))

/-- Appendix C.1 step 6, analytic assembly part: once the derivative of the
restricted slow multiplier is identified by pairing the period-matrix
derivative with the source-normalized left/right vectors, the supplied Riesz
branch multiplier matches the scalar period multiplier up to `O(alpha^2)`. -/
theorem quadratic_restricted_slow_multiplier_matches_scalar_period_multiplier_isBigO_sq_of_deriv_pairing
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (hderiv_pair :
      ∀ Aderiv : NodeMatrix (Sum Node {i : Node // i ≠ i0}),
        HasDerivAt
          (fun alpha : ℝ =>
            quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
          Aderiv 0 →
        rowDot (Node := Sum Node {i : Node // i ≠ i0}) left
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0}) Aderiv right) =
          -(lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        gamma alpha -
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
      (fun alpha : ℝ => alpha ^ 2) := by
  classical
  unfold PeriodicSpectralSplitting at hsplitting
  rcases hsplitting with
    ⟨halpha0_pos, _hr0_theta, _htheta_lt_one, _hK_nonneg, hgamma0,
      hgamma_analytic, _hP_analytic, hderiv, _hlocal⟩
  have hgamma_analytic_zero : AnalyticAt ℝ gamma 0 := by
    exact hgamma_analytic 0 (by simpa using halpha0_pos)
  rcases hderiv with ⟨Aderiv, hAderiv, hgamma_deriv⟩
  have hgamma_deriv_source :
      HasDerivAt gamma
        (-(lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) 0 := by
    have hpair := hderiv_pair Aderiv hAderiv
    simpa [hpair] using hgamma_deriv
  have hgamma_bigO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          gamma alpha -
            (1 - alpha *
              (lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))))
        (fun alpha : ℝ => alpha ^ 2) := by
    have hraw :=
      analyticAt_scalar_first_order_remainder_isBigO_sq
        hgamma_analytic_zero hgamma0 hgamma_deriv_source
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using hraw
  have hscalar_bigO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha -
            (1 - alpha *
              (lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))))
        (fun alpha : ℝ => alpha ^ 2) :=
    quadraticScalarPeriodMultiplier_firstOrder_isBigO_sq
      (Node := Node) quad lambda
  have hdiff := hgamma_bigO.sub hscalar_bigO
  refine hdiff.congr ?_ ?_
  · intro alpha
    ring
  · intro alpha
    rfl

/-- Differentiating a matrix family after applying fixed left and right
vectors gives the paired matrix derivative. -/
theorem rowDot_matrixMulVector_const_right_hasDerivAt
    (A : ℝ → NodeMatrix Node) (Aderiv : NodeMatrix Node)
    (left right : RowVector Node)
    (hA : HasDerivAt A Aderiv 0) :
    HasDerivAt
      (fun alpha : ℝ =>
        rowDot (Node := Node) left
          (matrixMulVector (Node := Node) (A alpha) right))
      (rowDot (Node := Node) left
        (matrixMulVector (Node := Node) Aderiv right)) 0 := by
  classical
  have hAij (i j : Node) :
      HasDerivAt (fun alpha : ℝ => A alpha i j) (Aderiv i j) 0 := by
    have hi :=
      (hasFDerivAt_apply (𝕜 := ℝ) i (A 0)).comp 0 hA.hasFDerivAt
    have hij :=
      (hasFDerivAt_apply (𝕜 := ℝ) j (A 0 i)).comp 0 hi
    convert hij.hasDerivAt using 1 <;>
      simp [Function.comp_def, ContinuousLinearMap.one_apply]
  unfold rowDot matrixMulVector
  convert
    (HasDerivAt.fun_sum fun i _ =>
      ((HasDerivAt.fun_sum fun j _ =>
        (hAij i j).const_mul (right j)).const_mul (left i))) using 1
  · funext alpha
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    ring

/-- Differentiating a moving left eigenrow and pairing with a fixed vector.

This is the calculus edge needed for the Appendix C.1 projected-row value
identity: if `row(alpha) A(alpha) = gamma(alpha) row(alpha)` near zero and
`gamma(0)=1`, then the derivative of the row on `A(0) z` is determined by the
matrix derivative term and the multiplier derivative. -/
theorem weightedState_left_eigenrow_derivative_pairing
    (A : ℝ → NodeMatrix Node) (gamma : ℝ → ℝ)
    (row : ℝ → RowVector Node)
    (Aderiv : NodeMatrix Node) (gammaDeriv : ℝ)
    (rowDeriv : RowVector Node)
    (hA : HasDerivAt A Aderiv 0)
    (hgamma : HasDerivAt gamma gammaDeriv 0)
    (hrow : HasDerivAt row rowDeriv 0)
    (hgamma0 : gamma 0 = 1)
    (heigen : ∀ᶠ alpha : ℝ in 𝓝 0,
      rowMulMatrix (Node := Node) (row alpha) (A alpha) =
        gamma alpha • row alpha)
    (z : RowVector Node) :
    weightedState (Node := Node) (E := ℝ) rowDeriv
        (matrixMulVector (Node := Node) (A 0) z) +
      weightedState (Node := Node) (E := ℝ) (row 0)
        (matrixMulVector (Node := Node) Aderiv z) =
        gammaDeriv * weightedState (Node := Node) (E := ℝ) (row 0) z +
          weightedState (Node := Node) (E := ℝ) rowDeriv z := by
  classical
  let toOperator : NodeMatrix Node →L[ℝ]
      (RowVector Node →L[ℝ] RowVector Node) :=
    ((LinearMap.toContinuousLinearMap.toLinearMap.comp
      (Matrix.mulVecBilin ℝ ℝ)).toContinuousLinearMap)
  let toFunctional : RowVector Node →L[ℝ]
      (RowVector Node →L[ℝ] ℝ) :=
    ((LinearMap.toContinuousLinearMap.toLinearMap.comp
      (dotProductBilin ℝ ℝ)).toContinuousLinearMap)
  have hA' : HasDerivAt (fun alpha => toOperator (A alpha))
      (toOperator Aderiv) 0 :=
    toOperator.hasFDerivAt.comp_hasDerivAt 0 hA
  have hrow' : HasDerivAt (fun alpha => toFunctional (row alpha))
      (toFunctional rowDeriv) 0 :=
    toFunctional.hasFDerivAt.comp_hasDerivAt 0 hrow
  have heigen' : ∀ᶠ alpha : ℝ in 𝓝 0,
      (toFunctional (row alpha)).comp (toOperator (A alpha)) =
        gamma alpha • toFunctional (row alpha) := by
    filter_upwards [heigen] with alpha halpha
    ext v
    change dotProduct (row alpha) (Matrix.mulVec (A alpha) v) =
      gamma alpha * dotProduct (row alpha) v
    have hv :
        weightedState (Node := Node) (E := ℝ) (row alpha)
            (matrixMulVector (Node := Node) (A alpha) v) =
          gamma alpha *
            weightedState (Node := Node) (E := ℝ) (row alpha) v := by
      calc
        weightedState (Node := Node) (E := ℝ) (row alpha)
            (matrixMulVector (Node := Node) (A alpha) v) =
          weightedState (Node := Node) (E := ℝ)
            (rowMulMatrix (Node := Node) (row alpha) (A alpha)) v := by
              simpa [leftMul, matrixMulVector] using
                (weightedState_rowMulMatrix
                  (Node := Node) (E := ℝ) (row alpha) (A alpha) v).symm
        _ = weightedState (Node := Node) (E := ℝ)
            (gamma alpha • row alpha) v := by rw [halpha]
        _ = gamma alpha *
            weightedState (Node := Node) (E := ℝ) (row alpha) v := by
              unfold weightedState
              simp [smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm,
                mul_comm]
    simpa [weightedState, matrixMulVector, Matrix.mulVec, dotProduct,
      smul_eq_mul] using hv
  simpa [toOperator, toFunctional, matrixMulVector, weightedState,
    Matrix.mulVec, dotProduct, hgamma0] using
    (HasDerivAt.left_eigenfunctional_apply_operator_deriv
      hA' hgamma hrow' heigen' z)

/-- Corrected-functional one-step identity for the homogeneous C.1 dynamics.

This is the source identity
`nu_{t+1}(S_{t+1}) = nu_t(S_t) - alpha * lambda * b_t^T X_t`
specialized to the deterministic restricted homogeneous step. -/
theorem quadraticRestrictedCorrectedFunctional_homogeneousStep_eq
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (t : ℕ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    let Snext :=
      quadraticRestrictedHomogeneousStep (Node := Node)
        quad lambda alpha t S
    weightedState (Node := Node) (E := ℝ) (quad.perronLeft (t + 1))
        Snext.1 -
      alpha * quad.correctedLift (t + 1) Snext.2 =
      weightedState (Node := Node) (E := ℝ) (quad.perronLeft t) S.1 -
        alpha * quad.correctedLift t S.2 -
        alpha * lambda *
          weightedState (Node := Node) (E := ℝ) (quad.influence t) S.1 := by
  classical
  cases S with
  | mk X W =>
      simpa [FiniteNetwork.correctedWeightedCenter_def,
        quadraticRestrictedHomogeneousStep, weightedState, leftMul,
        matrixSub, identityMatrix, Matrix.one_apply, smul_eq_mul,
        Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
        (FiniteNetwork.correctedWeightedState_pull_step_eq
          (R := quad.R t) (C := quad.C t)
          (pi := quad.perronLeft t) (piNext := quad.perronLeft (t + 1))
          (influence := quad.influence t)
          (D := quad.correctedLift t) (Dnext := quad.correctedLift (t + 1))
          (X := X) (Z := fun i : Node => lambda * X i) (W := W)
          (alpha := alpha)
          (quad.C_leftMul_zeroSum t W)
          (quad.pull_innovation_sum_zero t (fun i : Node => lambda * X i))
          (by funext j; exact quad.perronLeft_mul_R t j)
          (quad.correctedLift_poisson t W)
          (quad.influence_weightedState_identity t
            (fun i : Node => lambda * X i))
          (quad.correctedLift_add (t + 1)
            ⟨leftMul (Node := Node) (E := ℝ) (quad.C t) W.1,
              quad.C_leftMul_zeroSum t W⟩
            ⟨leftMul (Node := Node) (E := ℝ)
                (matrixSub (Node := Node) (quad.C t)
                  (identityMatrix (Node := Node)))
                (fun i : Node => lambda * X i),
              quad.pull_innovation_sum_zero t
                (fun i : Node => lambda * X i)⟩))

/-- Finite telescope of the corrected-functional one-step identity along the
phase-zero homogeneous restricted orbit. -/
theorem quadraticRestrictedCorrectedFunctional_homogeneousOrbit_telescope
    (quad : Setup Node ℝ) (lambda alpha : ℝ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    ∀ n : ℕ,
      weightedState (Node := Node) (E := ℝ) (quad.perronLeft n)
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha 0 n S).1) -
        alpha * quad.correctedLift n
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha 0 n S).2) =
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S.1 -
          alpha * quad.correctedLift 0 S.2 -
          alpha * lambda *
            (∑ r ∈ Finset.range n,
              weightedState (Node := Node) (E := ℝ) (quad.influence r)
                ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha 0 r S).1)) := by
  classical
  intro n
  induction n with
  | zero =>
      simp [quadraticRestrictedHomogeneousOrbit]
  | succ n ih =>
      have hstep :
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft (n + 1))
              ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha 0 (n + 1) S).1) -
            alpha * quad.correctedLift (n + 1)
              ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha 0 (n + 1) S).2) =
            weightedState (Node := Node) (E := ℝ) (quad.perronLeft n)
                ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha 0 n S).1) -
              alpha * quad.correctedLift n
                ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha 0 n S).2) -
              alpha * lambda *
                weightedState (Node := Node) (E := ℝ) (quad.influence n)
                  ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                    quad lambda alpha 0 n S).1) := by
        simpa [quadraticRestrictedHomogeneousOrbit] using
          quadraticRestrictedCorrectedFunctional_homogeneousStep_eq
            (Node := Node) quad lambda alpha n
            (quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 n S)
      rw [hstep, ih]
      rw [Finset.sum_range_succ]
      ring

/-- Finite telescope of the corrected-functional one-step identity along a
homogeneous restricted orbit starting from an arbitrary phase. -/
theorem quadraticRestrictedCorrectedFunctional_homogeneousOrbit_telescope_from
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (start : ℕ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    ∀ n : ℕ,
      weightedState (Node := Node) (E := ℝ) (quad.perronLeft (start + n))
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha start n S).1) -
        alpha * quad.correctedLift (start + n)
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha start n S).2) =
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft start) S.1 -
          alpha * quad.correctedLift start S.2 -
          alpha * lambda *
            (∑ r ∈ Finset.range n,
              weightedState (Node := Node) (E := ℝ) (quad.influence (start + r))
                ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha start r S).1)) := by
  classical
  intro n
  induction n with
  | zero =>
      simp [quadraticRestrictedHomogeneousOrbit]
  | succ n ih =>
      have hstep :
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft (start + (n + 1)))
              ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha start (n + 1) S).1) -
            alpha * quad.correctedLift (start + (n + 1))
              ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha start (n + 1) S).2) =
            weightedState (Node := Node) (E := ℝ) (quad.perronLeft (start + n))
                ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha start n S).1) -
              alpha * quad.correctedLift (start + n)
                ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                  quad lambda alpha start n S).2) -
              alpha * lambda *
                weightedState (Node := Node) (E := ℝ) (quad.influence (start + n))
                  ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                    quad lambda alpha start n S).1) := by
        simpa [quadraticRestrictedHomogeneousOrbit, Nat.add_assoc] using
          quadraticRestrictedCorrectedFunctional_homogeneousStep_eq
            (Node := Node) quad lambda alpha (start + n)
            (quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha start n S)
      rw [hstep, ih]
      rw [Finset.sum_range_succ]
      ring

/-- The general corrected lift specialized to real-valued tracker states is
the scalar corrected lift used in the influence-coordinate identities. -/
theorem correctedLift_eq_scalarCorrectedLift_real
    (quad : Setup Node ℝ) (t : ℕ) (W : ZeroSumState Node ℝ) :
    quad.correctedLift t W = quad.scalarCorrectedLift t W := by
  rw [quad.correctedLift_eq_tsum, quad.scalarCorrectedLift_eq_tsum]
  apply tsum_congr
  intro j
  rw [quad.correctedLiftSeriesTerm_eq_weightedState]
  rfl

/-- Corrected-functional value of a single phase noise channel at the injection
time.  This is the pointwise source identity
`nu_{t+1}(N_t(alpha)e_j) = -alpha * b_t(j)`. -/
theorem quadraticRestrictedUnitNoise_correctedFunctional_at_start_eq
    [DecidableEq Node]
    (quad : Setup Node ℝ) (alpha : ℝ) (t : ℕ) (j : Node) :
    weightedState (Node := Node) (E := ℝ) (quad.perronLeft (t + 1))
        (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0) -
      alpha * quad.correctedLift (t + 1) (FiniteNetwork.normalizedCoordinateError (fun node => quad.C t node j) j (quad.C_column_sum t j)) =
        -alpha * quad.influence t j := by
  classical
  have hunit :
      weightedState (Node := Node) (E := ℝ) (quad.perronLeft (t + 1))
          (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0) =
        -alpha * quad.perronLeft (t + 1) j := by
    unfold weightedState
    rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro b _hb hb_ne
      simp [hb_ne]
    · intro hmem
      simp at hmem
  have hinfluence :=
    quad.influence_apply_eq_perron_add_scalarCorrectedLift t j
  have hinfluence' :
      quad.influence t j = quad.perronLeft (t + 1) j +
        quad.scalarCorrectedLift (t + 1)
          (FiniteNetwork.normalizedCoordinateError
            (fun node => quad.C t node j) j (quad.C_column_sum t j)) := by
    rw [hinfluence]
    congr 2
    apply Subtype.ext
    funext node
    simp
  rw [hunit]
  rw [correctedLift_eq_scalarCorrectedLift_real]
  rw [hinfluence']
  ring

/-- First derivative of the corrected-functional value of one phase noise
channel at the injection time. -/
theorem quadraticRestrictedUnitNoise_correctedFunctional_at_start_hasDerivAt
    [DecidableEq Node]
    (quad : Setup Node ℝ) (t : ℕ) (j : Node) :
    HasDerivAt
      (fun alpha : ℝ =>
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft (t + 1))
            (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0) -
          alpha * quad.correctedLift (t + 1) (FiniteNetwork.normalizedCoordinateError (fun node => quad.C t node j) j (quad.C_column_sum t j)))
      (-(quad.influence t j)) 0 := by
  classical
  have hmodel :
      HasDerivAt (fun alpha : ℝ => -alpha * quad.influence t j)
        (-(quad.influence t j)) 0 := by
    have hraw := (hasDerivAt_id (0 : ℝ)).neg.mul_const (quad.influence t j)
    convert hraw using 1 <;> ring
  convert hmodel using 1
  funext alpha
  exact quadraticRestrictedUnitNoise_correctedFunctional_at_start_eq
    (Node := Node) quad alpha t j

/-- Pairing the restricted period matrix against the explicit alpha-zero right
state and the Perron-left top row is the primal Perron output of the
homogeneous period orbit. -/
theorem quadraticRestrictedPeriodMatrix_source_pairing_eq_orbit_weighted
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node) :
    rowDot (Node := Sum Node {i : Node // i ≠ i0})
        (fun a =>
          match a with
          | Sum.inl i => quad.perronLeft 0 i
          | Sum.inr _ => 0)
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0})
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
          (quadraticRestrictedAlphaZeroRightVector
            (Node := Node) quad lambda i0 0)) =
      weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
        ((quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha 0 quad.period
          (fun _ : Node => (1 : ℝ),
            quadraticRestrictedAlphaZeroSteadyTracker
              (Node := Node) quad lambda 0)).1) := by
  classical
  rw [quadraticRestrictedAlphaZeroRightVector]
  rw [quadraticRestrictedPeriodMatrix_represents_period]
  unfold rowDot weightedState restrictedStateToCoord
  simp

/-- At `alpha = 0`, the homogeneous slow-source orbit has primal component
`1` at every phase, so the source drift phase sum is the finite sum of the
scalar comparison gains `c_r = b_r^T 1`. -/
theorem quadraticRestrictedExplicitSlowOrbit_alpha_zero_phase_sum
    (quad : Setup Node ℝ) (lambda : ℝ) :
    (∑ r ∈ Finset.range quad.period,
      weightedState (Node := Node) (E := ℝ) (quad.influence r)
        ((quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda 0 0 r
          (fun _ : Node => (1 : ℝ),
            quadraticRestrictedAlphaZeroSteadyTracker
              (Node := Node) quad lambda 0)).1)) =
      ∑ r : Fin quad.period, quad.scalarComparisonGain r.1 := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _hr
  have hrlt : r < quad.period := Finset.mem_range.mp _hr
  have horb :=
    quadraticRestrictedAlphaZeroSteadyState_orbit
      (Node := Node) quad lambda 0 r
  have htop :
      (quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 0 r
        (fun _ : Node => (1 : ℝ),
          quadraticRestrictedAlphaZeroSteadyTracker
            (Node := Node) quad lambda 0)).1 =
        fun _ : Node => (1 : ℝ) := by
    simpa using congrArg Prod.fst horb
  simp [htop, weightedState, scalarComparisonGain, rowSum, smul_eq_mul,
    hrlt]

/-- The alpha-zero steady endpoint has the same corrected lift as the phase-zero
initial tracker, because the steady tracker is period-periodic and corrected
lift is block-start periodic. -/
theorem quadraticRestrictedExplicitSlowOrbit_correctedLift_endpoint_cancel
    (quad : Setup Node ℝ) (lambda : ℝ) :
    quad.correctedLift quad.period
        ((quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda 0 0 quad.period
          (fun _ : Node => (1 : ℝ),
            quadraticRestrictedAlphaZeroSteadyTracker
              (Node := Node) quad lambda 0)).2) =
      quad.correctedLift 0
        (quadraticRestrictedAlphaZeroSteadyTracker
          (Node := Node) quad lambda 0) := by
  classical
  let W0 : ZeroSumState Node ℝ :=
    quadraticRestrictedAlphaZeroSteadyTracker (Node := Node) quad lambda 0
  let Wp : ZeroSumState Node ℝ :=
    quadraticRestrictedAlphaZeroSteadyTracker
      (Node := Node) quad lambda quad.period
  have horb :=
    quadraticRestrictedAlphaZeroSteadyState_orbit
      (Node := Node) quad lambda 0 quad.period
  have hendpoint :
      (quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 0 quad.period
        (fun _ : Node => (1 : ℝ),
          quadraticRestrictedAlphaZeroSteadyTracker
            (Node := Node) quad lambda 0)).2 = Wp := by
    simpa [Wp] using congrArg Prod.snd horb
  have hWp : Wp = W0 := by
    apply Subtype.ext
    funext i
    have hper_i :
        quad.perronRight quad.period i = quad.perronRight 0 i := by
      simpa using congrFun (quad.perronRight_periodic 0) i
    simp [Wp, W0, quadraticRestrictedAlphaZeroSteadyTracker, hper_i]
  calc
    quad.correctedLift quad.period
        ((quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda 0 0 quad.period
          (fun _ : Node => (1 : ℝ),
            quadraticRestrictedAlphaZeroSteadyTracker
              (Node := Node) quad lambda 0)).2) =
        quad.correctedLift quad.period Wp := by rw [hendpoint]
    _ = quad.correctedLift quad.period W0 := by rw [hWp]
    _ = quad.correctedLift (quad.blockStart 1) W0 := by
        simp [blockStart]
    _ = quad.correctedLift 0 W0 := by
        simpa using quad.correctedLift_blockStart 1 W0

/-- If `g` is continuous at zero, then `alpha * g alpha` has derivative
`g 0` at zero.  This is the scalar calculus bridge used after the finite
orbit regularity step supplies continuity of the endpoint and phase-sum
observables. -/
theorem hasDerivAt_id_mul_of_continuousAt_zero
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) :
    HasDerivAt (fun alpha : ℝ => alpha * g alpha) (g 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine (hg.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with alpha halpha
  have hne : alpha ≠ 0 := halpha
  simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
  field_simp [hne]

theorem hasDerivAt_mul_of_hasDerivAt_zero_left_continuousAt
    {f g : ℝ → ℝ} {D : ℝ}
    (hf : HasDerivAt f D 0) (hf0 : f 0 = 0)
    (hg : ContinuousAt g 0) :
    HasDerivAt (fun alpha : ℝ => f alpha * g alpha) (D * g 0) 0 := by
  exact HasDerivAt.mul_of_eq_zero_left_of_continuousAt_right hf hf0 hg

/-- Left multiplication by a fixed finite real node matrix is continuous on
node-indexed real states. -/
theorem leftMul_continuous_real
    (A : NodeMatrix Node) :
    Continuous (fun X : State Node ℝ =>
      leftMul (Node := Node) (E := ℝ) A X) := by
  classical
  apply continuous_pi
  intro i
  unfold leftMul
  exact continuous_finset_sum Finset.univ
    (fun j _hj => continuous_const.mul (continuous_apply j))

/-- Pairing a fixed real row vector with a finite real node state is
continuous. -/
theorem weightedState_continuous_real
    (w : RowVector Node) :
    Continuous (fun X : State Node ℝ =>
      weightedState (Node := Node) (E := ℝ) w X) := by
  classical
  unfold weightedState
  exact continuous_finset_sum Finset.univ
    (fun i _hi => continuous_const.mul (continuous_apply i))

/-- One homogeneous restricted C.1 step is continuous in the scalar stepsize
parameter when its input state is continuous in that parameter. -/
theorem quadraticRestrictedHomogeneousStep_continuous_alpha
    (quad : Setup Node ℝ) (lambda : ℝ) (t : ℕ)
    (S : ℝ → State Node ℝ × ZeroSumState Node ℝ)
    (hS : Continuous S) :
    Continuous
      (fun alpha : ℝ =>
        quadraticRestrictedHomogeneousStep (Node := Node)
          quad lambda alpha t (S alpha)) := by
  classical
  let X : ℝ → State Node ℝ := fun alpha => (S alpha).1
  let W : ℝ → ZeroSumState Node ℝ := fun alpha => (S alpha).2
  let Z : ℝ → State Node ℝ := fun alpha i => lambda * X alpha i
  let transportedVal : ℝ → State Node ℝ :=
    fun alpha => leftMul (Node := Node) (E := ℝ) (quad.C t) (W alpha).1
  let innovationVal : ℝ → State Node ℝ :=
    fun alpha =>
      leftMul (Node := Node) (E := ℝ)
        (matrixSub (Node := Node) (quad.C t)
          (identityMatrix (Node := Node))) (Z alpha)
  have hX : Continuous X := hS.fst
  have hW : Continuous W := hS.snd
  have hWval : Continuous (fun alpha : ℝ => (W alpha).1) :=
    continuous_subtype_val.comp hW
  have hZ : Continuous Z := by
    apply continuous_pi
    intro i
    exact continuous_const.mul ((continuous_apply i).comp hX)
  have htransportedVal : Continuous transportedVal := by
    simpa [transportedVal] using
      (leftMul_continuous_real (Node := Node) (quad.C t)).comp hWval
  have hinnovationVal : Continuous innovationVal := by
    simpa [innovationVal] using
      (leftMul_continuous_real (Node := Node)
        (matrixSub (Node := Node) (quad.C t)
          (identityMatrix (Node := Node)))).comp hZ
  have htop : Continuous
      (fun alpha : ℝ =>
        leftMul (Node := Node) (E := ℝ) (quad.R t) (X alpha) -
          alpha • ((W alpha).1 + Z alpha)) := by
    exact
      ((leftMul_continuous_real (Node := Node) (quad.R t)).comp hX).sub
        (continuous_id.smul (hWval.add hZ))
  have htracker : Continuous
      (fun alpha : ℝ =>
        (⟨transportedVal alpha + innovationVal alpha, by
          exact
            zeroSumState_add_mem
              (Node := Node) (E := ℝ)
              ⟨transportedVal alpha, by
                simpa [transportedVal, W] using
                  quad.C_leftMul_zeroSum t (W alpha)⟩
              ⟨innovationVal alpha, by
                simpa [innovationVal, Z] using
                  quad.pull_innovation_sum_zero t (Z alpha)⟩⟩ :
          ZeroSumState Node ℝ)) := by
    exact
      Continuous.subtype_mk (htransportedVal.add hinnovationVal)
        (fun alpha => by
          exact
            zeroSumState_add_mem
              (Node := Node) (E := ℝ)
              ⟨transportedVal alpha, by
                simpa [transportedVal, W] using
                  quad.C_leftMul_zeroSum t (W alpha)⟩
              ⟨innovationVal alpha, by
                simpa [innovationVal, Z] using
                  quad.pull_innovation_sum_zero t (Z alpha)⟩)
  simpa [quadraticRestrictedHomogeneousStep, X, W, Z,
    transportedVal, innovationVal] using htop.prodMk htracker

/-- Finite homogeneous restricted C.1 orbits are continuous in the scalar
stepsize parameter. -/
theorem quadraticRestrictedHomogeneousOrbit_continuous_alpha
    (quad : Setup Node ℝ) (lambda : ℝ) (start n : ℕ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    Continuous
      (fun alpha : ℝ =>
        quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha start n S) := by
  classical
  induction n with
  | zero =>
      simpa [quadraticRestrictedHomogeneousOrbit] using
        (continuous_const :
          Continuous (fun _alpha : ℝ => S))
  | succ n ih =>
      simpa [quadraticRestrictedHomogeneousOrbit] using
        quadraticRestrictedHomogeneousStep_continuous_alpha
          (Node := Node) quad lambda (start + n)
          (fun alpha : ℝ =>
            quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha start n S) ih

/-- Finite homogeneous restricted C.1 orbits are continuous when the initial
state is itself a continuous function of the scalar stepsize. -/
theorem quadraticRestrictedHomogeneousOrbit_continuous_alpha_of_continuous_initial
    (quad : Setup Node ℝ) (lambda : ℝ) (start n : ℕ)
    (S : ℝ → State Node ℝ × ZeroSumState Node ℝ)
    (hS : Continuous S) :
    Continuous
      (fun alpha : ℝ =>
        quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha start n (S alpha)) := by
  exact continuous_nat_rec_of_continuous_step
    (step := fun k alpha state =>
      quadraticRestrictedHomogeneousStep (Node := Node)
        quad lambda alpha (start + k) state)
    (orbit := fun k alpha =>
      quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda alpha start k (S alpha))
    (initial := S) (n := n) rfl (fun _ _ => rfl) hS
    (fun k _ hstate =>
      quadraticRestrictedHomogeneousStep_continuous_alpha
        (Node := Node) quad lambda (start + k)
          (fun alpha : ℝ =>
            quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha start k (S alpha)) hstate)

/-- Finite homogeneous restricted C.1 orbits are continuous in the scalar
stepsize parameter at zero. -/
theorem quadraticRestrictedHomogeneousOrbit_continuousAt_alpha_zero
    (quad : Setup Node ℝ) (lambda : ℝ) (start n : ℕ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    ContinuousAt
      (fun alpha : ℝ =>
        quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha start n S) 0 := by
  classical
  exact
    (quadraticRestrictedHomogeneousOrbit_continuous_alpha
      (Node := Node) quad lambda start n S).continuousAt

/-- Corrected-functional derivative of one phase noise channel after any
finite homogeneous propagation.  The propagated drift term contributes no
first-order coefficient because the primal block is zero at `alpha = 0`. -/
theorem quadraticRestrictedUnitNoise_correctedFunctional_propagated_hasDerivAt
    [DecidableEq Node]
    (quad : Setup Node ℝ) (lambda : ℝ) (t n : ℕ) (j : Node) :
    HasDerivAt
      (fun alpha : ℝ =>
        let Snoise : State Node ℝ × ZeroSumState Node ℝ :=
          (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
            FiniteNetwork.normalizedCoordinateError (fun node => quad.C t node j) j (quad.C_column_sum t j))
        let Sout :=
          quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha (t + 1) n Snoise
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft (t + 1 + n))
            Sout.1 -
          alpha * quad.correctedLift (t + 1 + n) Sout.2)
      (-(quad.influence t j)) 0 := by
  classical
  let Snoise : ℝ → State Node ℝ × ZeroSumState Node ℝ := fun alpha =>
    (fun i : Node => -alpha * if i = j then (1 : ℝ) else 0,
      FiniteNetwork.normalizedCoordinateError (fun node => quad.C t node j) j (quad.C_column_sum t j))
  let phase : ℝ → ℝ := fun alpha =>
    ∑ r ∈ Finset.range n,
      weightedState (Node := Node) (E := ℝ) (quad.influence (t + 1 + r))
        ((quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha (t + 1) r (Snoise alpha)).1)
  let startValue : ℝ → ℝ := fun alpha =>
    weightedState (Node := Node) (E := ℝ) (quad.perronLeft (t + 1))
        (Snoise alpha).1 -
      alpha * quad.correctedLift (t + 1) (Snoise alpha).2
  have hSnoise_cont : Continuous Snoise := by
    have htop : Continuous (fun alpha : ℝ =>
        fun i : Node => -alpha * if i = j then (1 : ℝ) else 0) := by
      apply continuous_pi
      intro i
      exact continuous_id.neg.mul
        (continuous_const : Continuous
          (fun _alpha : ℝ => if i = j then (1 : ℝ) else 0))
    have hbottom : Continuous (fun _alpha : ℝ =>
        FiniteNetwork.normalizedCoordinateError (fun node => quad.C t node j) j (quad.C_column_sum t j)) := continuous_const
    simpa [Snoise] using htop.prodMk hbottom
  have hphase_cont : ContinuousAt phase 0 := by
    have hphase_global : Continuous phase := by
      dsimp [phase]
      exact continuous_finset_sum (Finset.range n)
        (fun r _hr =>
          (weightedState_continuous_real (Node := Node)
            (quad.influence (t + 1 + r))).comp
            (quadraticRestrictedHomogeneousOrbit_continuous_alpha_of_continuous_initial
              (Node := Node) quad lambda (t + 1) r Snoise hSnoise_cont).fst)
    exact hphase_global.continuousAt
  have hphase_zero : phase 0 = 0 := by
    dsimp [phase]
    apply Finset.sum_eq_zero
    intro r _hr
    have horb :=
      quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
        (Node := Node) quad lambda (t + 1) r (FiniteNetwork.normalizedCoordinateError (fun node => quad.C t node j) j (quad.C_column_sum t j))
    have htop :
        (quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda 0 (t + 1) r (Snoise 0)).1 =
          fun _ : Node => (0 : ℝ) := by
      simpa [Snoise] using congrArg Prod.fst horb
    simp [htop, weightedState]
  have hstart_deriv :
      HasDerivAt startValue (-(quad.influence t j)) 0 := by
    simpa [startValue, Snoise] using
      quadraticRestrictedUnitNoise_correctedFunctional_at_start_hasDerivAt
        (Node := Node) quad t j
  have hphase_term :
      HasDerivAt (fun alpha : ℝ => alpha * lambda * phase alpha) 0 0 := by
    have hraw :
        HasDerivAt (fun alpha : ℝ => alpha * (lambda * phase alpha))
          (lambda * phase 0) 0 :=
      hasDerivAt_id_mul_of_continuousAt_zero
        (fun alpha : ℝ => lambda * phase alpha)
        (continuousAt_const.mul hphase_cont)
    convert hraw using 1
    · funext alpha
      ring
    · rw [hphase_zero]
      ring
  have hrhs :
      HasDerivAt
        (fun alpha : ℝ => startValue alpha - alpha * lambda * phase alpha)
        (-(quad.influence t j)) 0 := by
    convert hstart_deriv.sub hphase_term using 1 <;> ring
  convert hrhs using 1
  funext alpha
  have htel :=
    quadraticRestrictedCorrectedFunctional_homogeneousOrbit_telescope_from
      (Node := Node) quad lambda alpha (t + 1) (Snoise alpha) n
  dsimp [startValue, phase, Snoise] at htel ⊢
  exact htel

/-- The finite phase-sum observable in the corrected-functional telescope is
continuous at zero. -/
theorem quadraticRestrictedExplicitSlowOrbit_phase_sum_continuousAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    ContinuousAt
      (fun alpha : ℝ =>
        ∑ r ∈ Finset.range quad.period,
          weightedState (Node := Node) (E := ℝ) (quad.influence r)
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 r S).1)) 0 := by
  classical
  have hcont : Continuous
      (fun alpha : ℝ =>
        ∑ r ∈ Finset.range quad.period,
          weightedState (Node := Node) (E := ℝ) (quad.influence r)
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 r S).1)) := by
    exact continuous_finset_sum (Finset.range quad.period)
      (fun r _hr =>
        (weightedState_continuous_real (Node := Node) (quad.influence r)).comp
          (quadraticRestrictedHomogeneousOrbit_continuous_alpha
            (Node := Node) quad lambda 0 r S).fst)
  exact hcont.continuousAt

/-- The endpoint corrected-lift observable in the corrected-functional
telescope is continuous at zero. -/
theorem quadraticRestrictedExplicitSlowOrbit_endpoint_correctedLift_continuousAt_zero
    (quad : Setup Node ℝ) (lambda : ℝ)
    (S : State Node ℝ × ZeroSumState Node ℝ) :
    ContinuousAt
      (fun alpha : ℝ =>
        quad.correctedLift quad.period
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha 0 quad.period S).2)) 0 := by
  classical
  obtain ⟨Kcorr, hcorr⟩ := quad.correctedLift_exists_lipschitz quad.period
  have horbit :
      Continuous
        (fun alpha : ℝ =>
          (quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha 0 quad.period S).2) :=
    (quadraticRestrictedHomogeneousOrbit_continuous_alpha
      (Node := Node) quad lambda 0 quad.period S).snd
  exact (hcorr.continuous.comp horbit).continuousAt

/-- Period-matrix first variation on tracker-only inputs.

This is the source-specific C.1 identity left after the generic moving-left-row
calculus: pairing the alpha-zero Perron row with the derivative of the
restricted period map on a tracker-only vector gives exactly the corrected-lift
transport difference over one period. -/
theorem quadraticRestrictedPeriodMatrix_deriv_tracker_pairing_eq_correctedLift_difference
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (Aderiv : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hAderiv :
      HasDerivAt
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        Aderiv 0)
    (W : ZeroSumState Node ℝ) :
    rowDot (Node := Sum Node {i : Node // i ≠ i0})
        (fun a =>
          match a with
          | Sum.inl i => quad.perronLeft 0 i
          | Sum.inr _ => 0)
        (matrixMulVector
          (Node := Sum Node {i : Node // i ≠ i0}) Aderiv
          (restrictedStateToCoord (Node := Node) i0
            ((fun _ : Node => (0 : ℝ)), W))) =
      quad.correctedLift quad.period
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda 0 0 quad.period
            ((fun _ : Node => (0 : ℝ)), W)).2) -
        quad.correctedLift 0 W := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let left0 : RowVector Idx := fun a =>
    match a with
    | Sum.inl i => quad.perronLeft 0 i
    | Sum.inr _ => 0
  let S0 : State Node ℝ × ZeroSumState Node ℝ :=
    ((fun _ : Node => (0 : ℝ)), W)
  let target : ℝ → ℝ := fun alpha : ℝ =>
    rowDot (Node := Idx) left0
      (matrixMulVector (Node := Idx)
        (quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
        (restrictedStateToCoord (Node := Node) i0 S0))
  let endpoint : ℝ → ℝ := fun alpha : ℝ =>
    quad.correctedLift quad.period
      ((quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda alpha 0 quad.period S0).2)
  let phase : ℝ → ℝ := fun alpha : ℝ =>
    ∑ r ∈ Finset.range quad.period,
      weightedState (Node := Node) (E := ℝ) (quad.influence r)
        ((quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha 0 r S0).1)
  let g : ℝ → ℝ := fun alpha : ℝ =>
    endpoint alpha - quad.correctedLift 0 W - lambda * phase alpha
  have hpaired_deriv :
      HasDerivAt target
        (rowDot (Node := Idx) left0
          (matrixMulVector (Node := Idx) Aderiv
            (restrictedStateToCoord (Node := Node) i0 S0))) 0 := by
    simpa [target, Idx, left0, S0] using
      rowDot_matrixMulVector_const_right_hasDerivAt
        (Node := Idx)
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        Aderiv left0 (restrictedStateToCoord (Node := Node) i0 S0)
        hAderiv
  have hperron_period :
      quad.perronLeft quad.period = quad.perronLeft 0 := by
    simpa using quad.perronLeft_periodic 0
  have htelescope :
      ∀ alpha : ℝ,
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 quad.period S0).1) -
          alpha * endpoint alpha =
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 -
          alpha * quad.correctedLift 0 S0.2 -
          alpha * lambda * phase alpha := by
    intro alpha
    have htel :=
      quadraticRestrictedCorrectedFunctional_homogeneousOrbit_telescope
        (Node := Node) quad lambda alpha S0 quad.period
    rw [hperron_period] at htel
    simpa [endpoint, phase, S0] using htel
  have htarget_orbit :
      ∀ alpha : ℝ,
        target alpha =
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 quad.period S0).1) := by
    intro alpha
    have horbit :=
      quadraticRestrictedPeriodMatrix_represents_period
        (Node := Node) quad lambda alpha i0 S0
    dsimp [target, left0, Idx]
    rw [horbit]
    unfold rowDot weightedState restrictedStateToCoord
    simp
  have htarget_eq :
      ∀ alpha : ℝ,
        target alpha =
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 +
            alpha * g alpha := by
    intro alpha
    have ht := htelescope alpha
    rw [htarget_orbit alpha]
    calc
      weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha 0 quad.period S0).1) =
          (weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
              ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                quad lambda alpha 0 quad.period S0).1) -
            alpha * endpoint alpha) +
            alpha * endpoint alpha := by ring
      _ =
          (weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 -
              alpha * quad.correctedLift 0 S0.2 -
              alpha * lambda * phase alpha) +
            alpha * endpoint alpha := by rw [ht]
      _ =
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 +
            alpha * g alpha := by
            dsimp [g, S0]
            ring
  have hend_cont : ContinuousAt endpoint 0 := by
    simpa [endpoint, S0] using
      quadraticRestrictedExplicitSlowOrbit_endpoint_correctedLift_continuousAt_zero
        (Node := Node) quad lambda S0
  have hphase_cont : ContinuousAt phase 0 := by
    have hphase_global : Continuous phase := by
      dsimp [phase]
      exact continuous_finset_sum (Finset.range quad.period)
        (fun r _hr =>
          (weightedState_continuous_real (Node := Node)
            (quad.influence r)).comp
            (quadraticRestrictedHomogeneousOrbit_continuous_alpha
              (Node := Node) quad lambda 0 r S0).fst)
    exact hphase_global.continuousAt
  have hphase_zero : phase 0 = 0 := by
    dsimp [phase, S0]
    apply Finset.sum_eq_zero
    intro r _hr
    have horbit :=
      quadraticRestrictedHomogeneousOrbit_alpha_zero_tracker_only
        (Node := Node) quad lambda 0 r W
    have htop :
        (quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda 0 0 r ((fun _ : Node => (0 : ℝ)), W)).1 =
          fun _ : Node => (0 : ℝ) := by
      simpa using congrArg Prod.fst horbit
    simp [htop, weightedState]
  have hg_cont : ContinuousAt g 0 := by
    simpa [g] using
      (hend_cont.sub continuousAt_const).sub
        (hphase_cont.const_mul lambda)
  have hg0 :
      g 0 =
        quad.correctedLift quad.period
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda 0 0 quad.period
              ((fun _ : Node => (0 : ℝ)), W)).2) -
          quad.correctedLift 0 W := by
    dsimp [g, endpoint, S0]
    rw [hphase_zero]
    ring
  have hsource_deriv :
      HasDerivAt target
        (quad.correctedLift quad.period
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda 0 0 quad.period
              ((fun _ : Node => (0 : ℝ)), W)).2) -
          quad.correctedLift 0 W) 0 := by
    have hmodel :
        HasDerivAt
          (fun alpha : ℝ =>
            weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 +
              alpha * g alpha)
          (g 0) 0 :=
      (hasDerivAt_id_mul_of_continuousAt_zero g hg_cont).const_add
        (weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1)
    convert hmodel using 1
    · funext alpha
      exact htarget_eq alpha
    · exact hg0.symm
  simpa [Idx, left0, S0] using hpaired_deriv.unique hsource_deriv

/-- Source-orbit first-variation statement obtained after the corrected
functional telescope.  This is the remaining Appendix C.1 step-3 finite
derivative obligation, now expressed directly on the homogeneous orbit rather
than on restricted matrix coordinates. -/
theorem quadraticRestrictedExplicitSlowOrbit_period_pairing_hasDerivAt_sum_gain
    (quad : Setup Node ℝ) (lambda : ℝ) :
    HasDerivAt
      (fun alpha : ℝ =>
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda alpha 0 quad.period
            (fun _ : Node => (1 : ℝ),
              quadraticRestrictedAlphaZeroSteadyTracker
                (Node := Node) quad lambda 0)).1))
      (-(lambda *
          (∑ r : Fin quad.period, quad.scalarComparisonGain r.1))) 0 := by
  classical
  let S0 : State Node ℝ × ZeroSumState Node ℝ :=
    (fun _ : Node => (1 : ℝ),
      quadraticRestrictedAlphaZeroSteadyTracker (Node := Node) quad lambda 0)
  have htelescope :
      ∀ alpha : ℝ,
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft quad.period)
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 quad.period S0).1) -
          alpha * quad.correctedLift quad.period
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 quad.period S0).2) =
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 -
            alpha * quad.correctedLift 0 S0.2 -
            alpha * lambda *
              (∑ r ∈ Finset.range quad.period,
                weightedState (Node := Node) (E := ℝ) (quad.influence r)
                  ((quadraticRestrictedHomogeneousOrbit (Node := Node)
                    quad lambda alpha 0 r S0).1)) := by
    intro alpha
    simpa [S0] using
      quadraticRestrictedCorrectedFunctional_homogeneousOrbit_telescope
        (Node := Node) quad lambda alpha S0 quad.period
  have hperron_period :
      quad.perronLeft quad.period = quad.perronLeft 0 := by
    simpa using quad.perronLeft_periodic 0
  have hsteady_orbit :
      quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda 0 0 quad.period S0 =
        (fun _ : Node => (1 : ℝ),
          quadraticRestrictedAlphaZeroSteadyTracker
            (Node := Node) quad lambda (0 + quad.period)) := by
    simpa [S0] using
      quadraticRestrictedAlphaZeroSteadyState_orbit
        (Node := Node) quad lambda 0 quad.period
  have hphase_sum_zero :
      (∑ r ∈ Finset.range quad.period,
        weightedState (Node := Node) (E := ℝ) (quad.influence r)
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda 0 0 r S0).1)) =
        ∑ r : Fin quad.period, quad.scalarComparisonGain r.1 := by
    simpa [S0] using
      quadraticRestrictedExplicitSlowOrbit_alpha_zero_phase_sum
        (Node := Node) quad lambda
  have hendpoint_cancel :
      quad.correctedLift quad.period
          ((quadraticRestrictedHomogeneousOrbit (Node := Node)
            quad lambda 0 0 quad.period S0).2) =
        quad.correctedLift 0 S0.2 := by
    simpa [S0] using
      quadraticRestrictedExplicitSlowOrbit_correctedLift_endpoint_cancel
        (Node := Node) quad lambda
  let target : ℝ → ℝ := fun alpha : ℝ =>
    weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
      ((quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda alpha 0 quad.period S0).1)
  let endpoint : ℝ → ℝ := fun alpha : ℝ =>
    quad.correctedLift quad.period
      ((quadraticRestrictedHomogeneousOrbit (Node := Node)
        quad lambda alpha 0 quad.period S0).2)
  let phase : ℝ → ℝ := fun alpha : ℝ =>
    ∑ r ∈ Finset.range quad.period,
      weightedState (Node := Node) (E := ℝ) (quad.influence r)
        ((quadraticRestrictedHomogeneousOrbit (Node := Node)
          quad lambda alpha 0 r S0).1)
  let g : ℝ → ℝ := fun alpha : ℝ =>
    endpoint alpha - quad.correctedLift 0 S0.2 - lambda * phase alpha
  have hend_cont : ContinuousAt endpoint 0 := by
    simpa [endpoint] using
      quadraticRestrictedExplicitSlowOrbit_endpoint_correctedLift_continuousAt_zero
        (Node := Node) quad lambda S0
  have hphase_cont : ContinuousAt phase 0 := by
    simpa [phase] using
      quadraticRestrictedExplicitSlowOrbit_phase_sum_continuousAt_zero
        (Node := Node) quad lambda S0
  have hg_cont : ContinuousAt g 0 := by
    simpa [g] using
      (hend_cont.sub continuousAt_const).sub
        (hphase_cont.const_mul lambda)
  have hg0 :
      g 0 =
        -(lambda *
          (∑ r : Fin quad.period, quad.scalarComparisonGain r.1)) := by
    dsimp [g, endpoint, phase]
    rw [hendpoint_cancel, hphase_sum_zero]
    ring
  have htarget_eq :
      ∀ alpha : ℝ,
        target alpha =
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 +
            alpha * g alpha := by
    intro alpha
    have ht := htelescope alpha
    rw [hperron_period] at ht
    change
      target alpha - alpha * endpoint alpha =
        weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 -
          alpha * quad.correctedLift 0 S0.2 -
          alpha * lambda * phase alpha at ht
    calc
      target alpha =
          (target alpha - alpha * endpoint alpha) +
            alpha * endpoint alpha := by ring
      _ =
          (weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 -
              alpha * quad.correctedLift 0 S0.2 -
              alpha * lambda * phase alpha) +
            alpha * endpoint alpha := by rw [ht]
      _ =
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 +
            alpha * g alpha := by
            dsimp [g]
            ring
  have hmodel :
      HasDerivAt
        (fun alpha : ℝ =>
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1 +
            alpha * g alpha)
        (g 0) 0 := by
    exact
      (hasDerivAt_id_mul_of_continuousAt_zero g hg_cont).const_add
        (weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0) S0.1)
  have htarget_deriv :
      HasDerivAt target
        (-(lambda *
          (∑ r : Fin quad.period, quad.scalarComparisonGain r.1))) 0 := by
    convert hmodel using 1
    · funext alpha
      exact htarget_eq alpha
    · exact hg0.symm
  simpa [target, S0] using htarget_deriv

/-- Appendix C.1 step-3 derivative on the explicit alpha-zero slow orbit.

The right vector is the source slow eigen-orbit, including the generally
nonzero tracker steady component.  This is the finite-period drift calculation
from the corrected functional paragraph: the alpha-zero orbit has primal block
`1` at every phase, and the first variation of the period output is the sum of
the phase drifts `-lambda * scalarComparisonGain r`. -/
theorem quadraticRestrictedPeriodMatrix_source_pairing_explicit_hasDerivAt
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node) :
    HasDerivAt
      (fun alpha : ℝ =>
        rowDot (Node := Sum Node {i : Node // i ≠ i0})
          (fun a =>
            match a with
            | Sum.inl i => quad.perronLeft 0 i
            | Sum.inr _ => 0)
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
            (quadraticRestrictedAlphaZeroRightVector
              (Node := Node) quad lambda i0 0)))
      (-(lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) 0 := by
  classical
  have hperiod_gain :
      (∑ r : Fin quad.period, quad.scalarComparisonGain r.1) =
        (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))) := by
    have hpReal : (quad.period : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt quad.period_pos)
    simpa only [scalarComparisonGain, rowSum,
      Fintype.expect_eq_sum_div_card, Fintype.card_fin,
      div_eq_mul_inv, mul_comm, smul_eq_mul] using
      (smul_inv_smul₀ hpReal
        (∑ r : Fin quad.period, ∑ i : Node, quad.influence r.1 i)).symm
  have horbit :
      HasDerivAt
        (fun alpha : ℝ =>
          weightedState (Node := Node) (E := ℝ) (quad.perronLeft 0)
            ((quadraticRestrictedHomogeneousOrbit (Node := Node)
              quad lambda alpha 0 quad.period
              (fun _ : Node => (1 : ℝ),
                quadraticRestrictedAlphaZeroSteadyTracker
                  (Node := Node) quad lambda 0)).1))
        (-(lambda *
            (∑ r : Fin quad.period, quad.scalarComparisonGain r.1))) 0 :=
    quadraticRestrictedExplicitSlowOrbit_period_pairing_hasDerivAt_sum_gain
      (Node := Node) quad lambda
  convert horbit using 1
  · ext alpha
    exact
      quadraticRestrictedPeriodMatrix_source_pairing_eq_orbit_weighted
        (Node := Node) quad lambda alpha i0
  · rw [hperiod_gain]
    ring

/-- Appendix C.1 derivative-pairing leaf for the restricted true period map.

This is the source calculation behind `(8.3)`: differentiating the period
propagator on the alpha-zero slow right eigen-orbit and pairing with the
alpha-zero left Perron row gives the period drift
`-lambda * period * influenceGain`. -/
theorem quadratic_restricted_period_matrix_deriv_pairing_eq_scalar_period_deriv
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (P : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hP0 : P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} =>
      right i * left j))
    (hright_eq :
      right =
        quadraticRestrictedAlphaZeroRightVector
          (Node := Node) quad lambda i0 0)
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0) :
    ∀ Aderiv : NodeMatrix (Sum Node {i : Node // i ≠ i0}),
      HasDerivAt
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        Aderiv 0 →
      rowDot (Node := Sum Node {i : Node // i ≠ i0}) left
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) Aderiv right) =
        -(lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1)))) := by
  classical
  intro Aderiv hAderiv
  have _hP0 := hP0
  have hpaired_deriv :
      HasDerivAt
        (fun alpha : ℝ =>
          rowDot (Node := Sum Node {i : Node // i ≠ i0}) left
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0) right))
        (rowDot (Node := Sum Node {i : Node // i ≠ i0}) left
          (matrixMulVector
            (Node := Sum Node {i : Node // i ≠ i0}) Aderiv right)) 0 :=
    rowDot_matrixMulVector_const_right_hasDerivAt
      (Node := Sum Node {i : Node // i ≠ i0})
      (fun alpha : ℝ =>
        quadraticRestrictedPeriodMatrix (Node := Node)
          quad lambda alpha i0)
      Aderiv left right hAderiv
  have hsource_deriv :
      HasDerivAt
        (fun alpha : ℝ =>
          rowDot (Node := Sum Node {i : Node // i ≠ i0}) left
            (matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0) right))
        (-(lambda * (quad.period : ℝ) * (Finset.expect Finset.univ (fun r : Fin quad.period => rowSum (quad.influence r.1))))) 0 := by
    have hleft_eq :
        left =
          (fun a : Sum Node {i : Node // i ≠ i0} =>
            match a with
            | Sum.inl i => quad.perronLeft 0 i
            | Sum.inr _ => 0) := by
      funext a
      cases a with
      | inl i => exact hleft_top i
      | inr j => exact hleft_bottom j
    rw [hleft_eq, hright_eq]
    exact
      quadraticRestrictedPeriodMatrix_source_pairing_explicit_hasDerivAt
        (Node := Node) quad lambda i0
  exact hpaired_deriv.unique hsource_deriv

/-- Appendix C.1 step 6 multiplier bridge in the source-facing form used by
the slow Duhamel comparison. -/
theorem quadratic_restricted_slow_multiplier_matches_scalar_period_multiplier_isBigO_sq
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (r0 alpha0 theta K : ℝ)
    (right left : RowVector (Sum Node {i : Node // i ≠ i0}))
    (gamma : ℝ → ℝ) (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hsplitting :
      PeriodicSpectralSplitting
        (Node := Sum Node {i : Node // i ≠ i0})
        (fun alpha : ℝ =>
          quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
        r0 alpha0 theta K right left gamma P F)
    (hP0 : P 0 = (fun i j : Sum Node {i : Node // i ≠ i0} =>
      right i * left j))
    (hright_eq :
      right =
        quadraticRestrictedAlphaZeroRightVector
          (Node := Node) quad lambda i0 0)
    (hright_top : ∀ i : Node, right (Sum.inl i) = 1)
    (hleft_top : ∀ i : Node, left (Sum.inl i) = quad.perronLeft 0 i)
    (hleft_bottom : ∀ j : {i : Node // i ≠ i0}, left (Sum.inr j) = 0) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ =>
        gamma alpha -
          quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
      (fun alpha : ℝ => alpha ^ 2) :=
  quadratic_restricted_slow_multiplier_matches_scalar_period_multiplier_isBigO_sq_of_deriv_pairing
    (Node := Node) quad lambda i0 r0 alpha0 theta K right left gamma P F
    hsplitting
    (quadratic_restricted_period_matrix_deriv_pairing_eq_scalar_period_deriv
      (Node := Node) quad lambda i0 right left P hP0 hright_eq hright_top
      hleft_top hleft_bottom)

/-- Appendix C.1 step 6 contraction package for the restricted slow multiplier.

The scalar period multiplier has the homogeneous-quadratic small-alpha squeeze;
the restricted Riesz multiplier differs from it by `O(alpha^2)`.  Shrinking the
stepsize radius gives a common usable contraction envelope for both. -/
theorem restricted_gamma_smallAlpha_contract_from_scalar_squeeze
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (gamma : ℝ → ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hmultO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          gamma alpha -
            quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
        (fun alpha : ℝ => alpha ^ 2)) :
    ∃ alpha0 cGamma Cmul : ℝ,
      0 < alpha0 ∧ 0 < cGamma ∧ 0 < Cmul ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          let Gamma :=
            quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha
          0 ≤ Gamma ∧ Gamma ≤ 1 - cGamma * alpha ∧
            |gamma alpha - Gamma| ≤ Cmul * alpha ^ 2 ∧
              0 ≤ gamma alpha ∧ gamma alpha ≤ 1 - cGamma * alpha ∧
                0 < 1 - cGamma * alpha := by
  apply near_zero_contraction_bounds_of_isBigO_sub_sq
    (base := fun alpha =>
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
    (perturbed := gamma)
  · obtain ⟨alphaS, c1, c2, halphaS_pos, hc1_pos, hc2_pos, _hc1_le_c2,
        hscalar⟩ :=
      quadraticScalarPeriodMultiplier_smallAlpha_squeeze
        (Node := Node) quad lambda hquad
    refine ⟨alphaS, c1, c2, halphaS_pos, hc1_pos, hc2_pos, ?_⟩
    intro alpha halpha_pos halpha_le
    have hscalar_alpha := hscalar alpha halpha_pos halpha_le
    exact ⟨hscalar_alpha.1, hscalar_alpha.2.1⟩
  · exact hmultO

/-- Appendix C.3 slow-multiplier persistence input.

The upper contraction package above is useful for square-summability estimates,
but the bounded-product lower-bound proof needs the opposite side of the same
source squeeze: the restricted slow multiplier remains above `1 - C alpha`
after shrinking the small-stepsize interval.  This follows from the scalar
period multiplier lower squeeze and the restricted/scalar `O(alpha^2)` bridge. -/
theorem restricted_gamma_smallAlpha_lower_from_scalar_squeeze
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (gamma : ℝ → ℝ)
    (hquad : HomogeneousQuadraticComponents (Node := Node) quad lambda)
    (hmultO :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ =>
          gamma alpha -
            quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
        (fun alpha : ℝ => alpha ^ 2)) :
    ∃ alpha0 cLower : ℝ,
      0 < alpha0 ∧ 0 < cLower ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          0 ≤ gamma alpha ∧ 1 - cLower * alpha ≤ gamma alpha := by
  obtain ⟨alphaS, _c1, c2, halphaS_pos, _hc1_pos, _hc2_pos, _hc1_le_c2,
      hscalar⟩ :=
    quadraticScalarPeriodMultiplier_smallAlpha_squeeze
      (Node := Node) quad lambda hquad
  exact near_zero_linear_lower_bound_of_isBigO_sub_sq
    (base := fun alpha =>
      quadraticScalarPeriodMultiplier (Node := Node) quad lambda alpha)
    (perturbed := gamma) (alphaS := alphaS) (c2 := c2)
    halphaS_pos
    (fun alpha halpha_pos halpha_le =>
      (hscalar alpha halpha_pos halpha_le).1)
    (hmultO.mono nhdsWithin_le_nhds)

/-- Algebraic scalar slow recursion obtained by projecting a one-period
restricted recursion with the Riesz projection.

This is the finite-dimensional core of Appendix C.1 step 6: after using
`A = gamma P + F`, `P F = 0`, and `P^2 = P`, the projected primal-average
coordinate follows a scalar AR recursion with input `P xi`. -/
theorem quadratic_restricted_projected_slow_boundary_recursion
    (i0 : Node)
    (gamma : ℝ)
    (P F A : NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hPP : matrixMul (Node := Sum Node {i : Node // i ≠ i0}) P P = P)
    (hA : A =
      matrixAdd (Node := Sum Node {i : Node // i ≠ i0}) (gamma • P) F)
    (hPF : matrixMul (Node := Sum Node {i : Node // i ≠ i0}) P F = 0)
    (y xi yNext : RowVector (Sum Node {i : Node // i ≠ i0}))
    (hyNext : yNext = matrixMulVector
        (Node := Sum Node {i : Node // i ≠ i0}) A y + xi) :
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
        (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) P yNext) =
      gamma *
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) P y) +
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0}) P xi) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  simpa only [quadraticRestrictedPrimalAverageOutput,
      realMatrixContinuousLinearMap, ContinuousLinearMap.coe_coe,
      LinearMap.coe_toContinuousLinearMap', ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul] using
    (Module.End.apply_idempotent_affine_step_of_split
      (P := (realMatrixContinuousLinearMap (Node := Idx) P).toLinearMap)
      (F := (realMatrixContinuousLinearMap (Node := Idx) F).toLinearMap)
      (A := (realMatrixContinuousLinearMap (Node := Idx) A).toLinearMap)
      (ell := (((nodeCount (Node := Node) : ℝ)⁻¹ •
        ∑ i : Node, ContinuousLinearMap.proj (R := ℝ) (Sum.inl i)) :
          RowVector Idx →L[ℝ] ℝ).toLinearMap)
      (gamma := gamma)
      (by
        apply LinearMap.ext
        intro z
        change matrixMulVector (Node := Idx) P
            (matrixMulVector (Node := Idx) P z) =
          matrixMulVector (Node := Idx) P z
        rw [← matrixMulVector_matrixMul, hPP])
      (by
        apply LinearMap.ext
        intro z
        funext a
        change matrixMulVector (Node := Idx) A z a =
          gamma * matrixMulVector (Node := Idx) P z a +
            matrixMulVector (Node := Idx) F z a
        rw [hA]
        simp [matrixAdd, matrixMulVector, Finset.mul_sum, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _hx
        ring)
      (by
        apply LinearMap.ext
        intro z
        change matrixMulVector (Node := Idx) P
            (matrixMulVector (Node := Idx) F z) = 0
        rw [← matrixMulVector_matrixMul, hPF]
        funext a
        simp [matrixMulVector])
      y xi yNext hyNext)

/-- Block-boundary projected/scalar error recursion.

This is the reusable source object that was previously only a local `have`
inside `quadratic_restricted_slow_output_scalar_average_l2_bound`.  Appendix
C.3 needs the same block-boundary slow coordinate when proving mean
persistence: subtract the scalar block recursion from the projected restricted
slow recursion, leaving multiplier error plus period-input error. -/
theorem quadratic_restricted_projected_scalar_boundary_error_recursion
    (quad : Setup Node ℝ) (lambda : ℝ) (i0 : Node)
    (alpha_restricted theta K : ℝ)
    (gamma : ℝ → ℝ)
    (P F : ℝ → NodeMatrix (Sum Node {i : Node // i ≠ i0}))
    (hrestricted_period_boundary_recursion :
      ∀ alpha : ℝ, ∀ noise : NoisePath Node ℝ, ∀ k : ℕ,
        let stepped := quad.withStepsize alpha
        restrictedStateToCoord (Node := Node) i0
            (stepped.primalState noise ((k + 1) * quad.period),
              stepped.trackerErrorZeroSum noise ((k + 1) * quad.period)) =
          matrixMulVector
              (Node := Sum Node {i : Node // i ≠ i0})
              (quadraticRestrictedPeriodMatrix (Node := Node)
                quad lambda alpha i0)
              (restrictedStateToCoord (Node := Node) i0
                (stepped.primalState noise (k * quad.period),
                  stepped.trackerErrorZeroSum noise (k * quad.period))) +
            quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise k)
    (hrestricted_splitting_at :
      ∀ alpha : ℝ, |alpha| ≤ alpha_restricted →
        IsRieszProjectionAtEigenvalue
            (Node := Sum Node {i : Node // i ≠ i0})
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0)
            (gamma alpha) (P alpha) ∧
          quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0 =
            matrixAdd (Node := Sum Node {i : Node // i ≠ i0})
              ((gamma alpha) • P alpha) (F alpha) ∧
            matrixMul (Node := Sum Node {i : Node // i ≠ i0})
                (P alpha) (F alpha) = 0 ∧
              matrixMul (Node := Sum Node {i : Node // i ≠ i0})
                  (F alpha) (P alpha) = 0 ∧
                ∀ j : ℕ,
                  matrixEuclideanOperatorNorm
                      (Node := Sum Node {i : Node // i ≠ i0})
                      (matrixPower (Node := Sum Node {i : Node // i ≠ i0})
                        (F alpha) j) ≤
                    K * theta ^ j)
    (alpha : ℝ) (halpha_abs : |alpha| ≤ alpha_restricted)
    (noise : NoisePath Node ℝ) :
    ∀ k : ℕ,
      let stepped := quad.withStepsize alpha
      let projectedBoundary : ℕ → ℝ := fun m =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
            (P alpha)
            (restrictedStateToCoord (Node := Node) i0
              (stepped.primalState noise (m * quad.period),
                stepped.trackerErrorZeroSum noise
                  (m * quad.period))))
      let scalarBoundary : ℕ → ℝ := fun m =>
        quad.quadraticScalarComparisonProcess lambda alpha noise
          (m * quad.period)
      let projectedInput : ℕ → ℝ := fun m =>
        quadraticRestrictedPrimalAverageOutput (Node := Node) i0
          (matrixMulVector (Node := Sum Node {i : Node // i ≠ i0})
            (P alpha)
            (quadraticRestrictedPeriodNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise m))
      let scalarInput : ℕ → ℝ := fun m =>
        quadraticScalarBlockNoiseInnovation (Node := Node)
          quad lambda alpha noise m
      projectedBoundary (k + 1) - scalarBoundary (k + 1) =
        gamma alpha * (projectedBoundary k - scalarBoundary k) +
          ((gamma alpha -
              quadraticScalarPeriodMultiplier (Node := Node)
                quad lambda alpha) *
              scalarBoundary k +
            (projectedInput k - scalarInput k)) := by
  classical
  intro k
  let Idx := Sum Node {i : Node // i ≠ i0}
  let stepped := quad.withStepsize alpha
  let projectedBoundary : ℕ → ℝ := fun m =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Idx) (P alpha)
        (restrictedStateToCoord (Node := Node) i0
          (stepped.primalState noise (m * quad.period),
            stepped.trackerErrorZeroSum noise (m * quad.period))))
  let scalarBoundary : ℕ → ℝ := fun m =>
    quad.quadraticScalarComparisonProcess lambda alpha noise
      (m * quad.period)
  let projectedInput : ℕ → ℝ := fun m =>
    quadraticRestrictedPrimalAverageOutput (Node := Node) i0
      (matrixMulVector (Node := Idx) (P alpha)
        (quadraticRestrictedPeriodNoiseInnovationCoord
          (Node := Node) quad lambda alpha i0 noise m))
  let scalarInput : ℕ → ℝ := fun m =>
    quadraticScalarBlockNoiseInnovation (Node := Node)
      quad lambda alpha noise m
  have hprojected_rec :
      ∀ m : ℕ,
        projectedBoundary (m + 1) =
          gamma alpha * projectedBoundary m + projectedInput m := by
    intro m
    let yk : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState noise (m * quad.period),
          stepped.trackerErrorZeroSum noise (m * quad.period))
    let yNext : RowVector Idx :=
      restrictedStateToCoord (Node := Node) i0
        (stepped.primalState noise ((m + 1) * quad.period),
          stepped.trackerErrorZeroSum noise ((m + 1) * quad.period))
    let xi : RowVector Idx :=
      quadraticRestrictedPeriodNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise m
    have hlocal := hrestricted_splitting_at alpha halpha_abs
    have hyNext :
        yNext =
          matrixMulVector (Node := Idx)
            (quadraticRestrictedPeriodMatrix (Node := Node)
              quad lambda alpha i0) yk + xi := by
      simpa [Idx, stepped, yk, yNext, xi] using
        hrestricted_period_boundary_recursion alpha noise m
    simpa [projectedBoundary, projectedInput, Idx, stepped, yk, yNext, xi]
      using
        quadratic_restricted_projected_slow_boundary_recursion
          (Node := Node) i0 (gamma alpha) (P alpha) (F alpha)
          (quadraticRestrictedPeriodMatrix (Node := Node)
            quad lambda alpha i0)
          hlocal.1.1.1 hlocal.2.1 hlocal.2.2.1
          yk xi yNext hyNext
  have hscalar_rec :
      ∀ m : ℕ,
        scalarBoundary (m + 1) =
          quadraticScalarPeriodMultiplier (Node := Node)
            quad lambda alpha * scalarBoundary m + scalarInput m := by
    intro m
    simpa [scalarBoundary, scalarInput] using
      quadraticScalarBlockARRecursion
        (Node := Node) quad lambda alpha noise m
  simpa [projectedBoundary, scalarBoundary, projectedInput, scalarInput, Idx,
    stepped] using
    scalar_ar_difference_recursion_of_two_recursions
      (gamma := gamma alpha)
      (Gamma := quadraticScalarPeriodMultiplier (Node := Node)
        quad lambda alpha)
      projectedBoundary scalarBoundary projectedInput scalarInput
      hprojected_rec hscalar_rec k

/-- Exact finite-Duhamel unroll for the restricted period-noise innovation.

This is the coefficient-row gateway for Appendix C.1 step 6: each period
innovation is the finite sum of one-step noise channels propagated by the
remaining homogeneous phases in the same block. -/
theorem quadraticRestrictedConsecutiveNoiseInnovationCoord_eq_finset_sum
    (quad : Setup Node ℝ) (lambda alpha : ℝ) (i0 : Node)
    (noise : NoisePath Node ℝ) (start n : ℕ) :
    let Idx := Sum Node {i : Node // i ≠ i0}
    let step : ℕ → NodeMatrix Idx := fun t =>
      quadraticRestrictedOneStepMatrix (Node := Node)
        quad lambda alpha i0 t
    quadraticRestrictedConsecutiveNoiseInnovationCoord
        (Node := Node) quad lambda alpha i0 noise start n =
      (Finset.range n).sum fun r =>
        matrixMulVector (Node := Idx)
          (consecutiveProduct (Node := Idx) step (start + r + 1)
            (n - 1 - r))
          (quadraticRestrictedNoiseInnovationCoord
            (Node := Node) quad alpha i0 noise (start + r)) := by
  classical
  let Idx := Sum Node {i : Node // i ≠ i0}
  let step : ℕ → NodeMatrix Idx := fun t =>
    quadraticRestrictedOneStepMatrix (Node := Node)
      quad lambda alpha i0 t
  induction n with
  | zero =>
      funext a
      simp [quadraticRestrictedConsecutiveNoiseInnovationCoord, Idx, step]
  | succ n ih =>
      funext a
      by_cases hn : n = 0
      · subst n
        simp [quadraticRestrictedConsecutiveNoiseInnovationCoord, Idx, step,
          consecutiveProduct, matrixMulVector, identityMatrix]
      · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        have hmul_sum :
            matrixMulVector (Node := Idx) (step (start + n))
                ((Finset.range n).sum fun r =>
                  matrixMulVector (Node := Idx)
                    (consecutiveProduct (Node := Idx) step (start + r + 1)
                      (n - 1 - r))
                    (quadraticRestrictedNoiseInnovationCoord
                      (Node := Node) quad alpha i0 noise (start + r))) =
              (Finset.range n).sum fun r =>
                matrixMulVector (Node := Idx) (step (start + n))
                  (matrixMulVector (Node := Idx)
                    (consecutiveProduct (Node := Idx) step (start + r + 1)
                      (n - 1 - r))
                    (quadraticRestrictedNoiseInnovationCoord
                      (Node := Node) quad alpha i0 noise (start + r))) := by
          simpa using
            matrixMulVector_finset_sum_local
              (Node := Idx) (step (start + n)) (Finset.range n)
              (fun r =>
                matrixMulVector (Node := Idx)
                  (consecutiveProduct (Node := Idx) step (start + r + 1)
                    (n - 1 - r))
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad alpha i0 noise (start + r)))
        have hprop :
            ∀ r ∈ Finset.range n,
              matrixMulVector (Node := Idx) (step (start + n))
                  (matrixMulVector (Node := Idx)
                    (consecutiveProduct (Node := Idx) step (start + r + 1)
                      (n - 1 - r))
                    (quadraticRestrictedNoiseInnovationCoord
                      (Node := Node) quad alpha i0 noise (start + r))) =
                matrixMulVector (Node := Idx)
                  (consecutiveProduct (Node := Idx) step (start + r + 1)
                    (n - r))
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad alpha i0 noise (start + r)) := by
          intro r hr
          have hr_lt : r < n := Finset.mem_range.mp hr
          have hlen : n - r = (n - 1 - r) + 1 := by omega
          have hidx : start + r + 1 + (n - 1 - r) = start + n := by omega
          calc
            matrixMulVector (Node := Idx) (step (start + n))
                (matrixMulVector (Node := Idx)
                  (consecutiveProduct (Node := Idx) step (start + r + 1)
                    (n - 1 - r))
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad alpha i0 noise (start + r))) =
              matrixMulVector (Node := Idx)
                (matrixMul (Node := Idx) (step (start + n))
                  (consecutiveProduct (Node := Idx) step (start + r + 1)
                    (n - 1 - r)))
                (quadraticRestrictedNoiseInnovationCoord
                  (Node := Node) quad alpha i0 noise (start + r)) := by
                rw [matrixMulVector_matrixMul]
            _ =
              matrixMulVector (Node := Idx)
                (consecutiveProduct (Node := Idx) step (start + r + 1)
                  (n - r))
                (quadraticRestrictedNoiseInnovationCoord
                  (Node := Node) quad alpha i0 noise (start + r)) := by
                rw [hlen]
                simp [consecutiveProduct, hidx]
        calc
          quadraticRestrictedConsecutiveNoiseInnovationCoord
              (Node := Node) quad lambda alpha i0 noise start (n + 1) a =
            (matrixMulVector (Node := Idx) (step (start + n))
                ((Finset.range n).sum fun r =>
                  matrixMulVector (Node := Idx)
                    (consecutiveProduct (Node := Idx) step (start + r + 1)
                      (n - 1 - r))
                    (quadraticRestrictedNoiseInnovationCoord
                      (Node := Node) quad alpha i0 noise (start + r))) +
              quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 noise (start + n)) a := by
                simp [quadraticRestrictedConsecutiveNoiseInnovationCoord,
                  Idx, step, ih]
          _ =
            (((Finset.range n).sum fun r =>
                matrixMulVector (Node := Idx)
                  (consecutiveProduct (Node := Idx) step (start + r + 1)
                    (n - r))
                  (quadraticRestrictedNoiseInnovationCoord
                    (Node := Node) quad alpha i0 noise (start + r))) +
              quadraticRestrictedNoiseInnovationCoord
                (Node := Node) quad alpha i0 noise (start + n)) a := by
                rw [hmul_sum]
                simp only [Pi.add_apply, Finset.sum_apply]
                congr 1
                apply Finset.sum_congr rfl
                intro r hr
                exact congrFun (hprop r hr) a
          _ =
            ((Finset.range (n + 1)).sum fun r =>
              matrixMulVector (Node := Idx)
                (consecutiveProduct (Node := Idx) step (start + r + 1)
                  (n + 1 - 1 - r))
                (quadraticRestrictedNoiseInnovationCoord
                  (Node := Node) quad alpha i0 noise (start + r))) a := by
                rw [Finset.sum_range_succ]
                have hlast :
                    matrixMulVector (Node := Idx)
                        (consecutiveProduct (Node := Idx) step (start + n + 1)
                          (n + 1 - 1 - n))
                        (quadraticRestrictedNoiseInnovationCoord
                          (Node := Node) quad alpha i0 noise (start + n)) =
                      quadraticRestrictedNoiseInnovationCoord
                        (Node := Node) quad alpha i0 noise (start + n) := by
                      funext b
                      simp [consecutiveProduct]
                      unfold matrixMulVector identityMatrix
                      rw [Finset.sum_eq_single b]
                      · simp
                      · intro c _hc hcb
                        by_cases hbc : b = c
                        · exact False.elim (hcb hbc.symm)
                        · simp [hbc]
                      · intro hb
                        simp at hb
                rw [hlast]
                simp only [Pi.add_apply, Finset.sum_apply]
                congr 1

end Setup
end Algorithms.Unverified.TimeVaryingPushPull
