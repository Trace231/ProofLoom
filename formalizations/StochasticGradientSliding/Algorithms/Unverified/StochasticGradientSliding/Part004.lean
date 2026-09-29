import Algorithms.Unverified.StochasticGradientSliding.Part003
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

/-- Formula-extension high-probability assembly from the Lemma 4.1 interface.

This helper is deliberately not source-facing: it starts after the source
probabilistic content of Eq. (8.1.70) has been reconstructed as
`SGSLinearMDSLightTailInterface`.  The selected Algorithm 8.2 route derives that
interface internally and then calls this assembly theorem. -/
theorem SGSGenericConvergence_Theorem8_2_highProbability_runFormulaExtension_from_mds_under_gammaRange [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
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
    (hquery_strictPast_meas :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω => sgsGeneratedOracleQuery S inner κ i ω))
    (hlinear_condExp_zero :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] =ᵐ[law.P] 0)
    (hlinear_exp_sq_integrable :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P)
    (hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1) :
      law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ >
              theorem82ExpectedBound_formulaExtension S x0 ⟨xStar, hxStar.1⟩ N beta gamma Gamma T +
                lambda *
                  theorem82ProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact N beta gamma Gamma T} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_light :
      generatedSFOLightTail S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsGeneratedOracleQuery S inner) hindep
  have hcoordinate_light : coordinateSFOLightTail S law.P law.sample :=
    sgsOracleLightTailAssumption_8_1_57.coordinate S law hlight
  classical
  let uStar : FeasiblePoint S := ⟨xStar, hxStar.1⟩
  let gap : Ω → ℝ := fun ω =>
    objectiveOn S (sgsGeneratedOutput S states N.1 ω) - objectiveOn S uStar
  let Bd : ℝ :=
    theorem82ExpectedBound_formulaExtension S x0 uStar N beta gamma Gamma T
  let linear : Ω → ℝ := fun ω =>
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
  let quadratic : Ω → ℝ := fun ω =>
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
                (dualNorm S δ ^ 2 / (beta κ * spsP ι))))
  let quadraticMean : ℝ :=
    Gamma N *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                (S.sigmaSq / (beta κ * spsP ι))))
  let linearScale : ℝ :=
    sigma S * Gamma N *
      Real.sqrt
        (2 * bregmanEnvelope_formulaExtension S uStar hcompact *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι * psWeightProduct spsP i)) ^ 2)))
  let quadraticScale : ℝ :=
    S.sigmaSq * Gamma N *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          gamma κ * psWeightProduct spsP (T κ) /
            (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i)))
  have hmaster_raw :=
    generated_sgs_master_inequality_8_1_69_formulaExtension
      (S := S) x0 beta gamma Gamma T law.sample N states inner hrun.1 uStar
      hbeta hgamma hlower hGamma hmono
  have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
    outer_gamma_positive_of_weight_condition_and_forward_denom_beforeMaster
      beta gamma Gamma T hgamma hGamma hmono
  have hTpos : ∀ k : PositiveTime, 0 < T k :=
    positive_inner_budget_of_forwardMonotonicity_beforeMaster beta gamma Gamma T hmono
  have hmaster_decomp :
      ∀ ω, gap ω ≤ Bd + linear ω + (quadratic ω - quadraticMean) := by
    intro ω
    have hraw := hmaster_raw ω
    let deterministicOuter : ℝ :=
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι))))
    have hdeterministic_normalize :
        Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
              bregmanFormulaOnX S x0 uStar +
            Gamma N * deterministicOuter =
          Bd := by
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
      simp [Bd, theorem82ExpectedBound_formulaExtension, genericExpectedBound_formulaExtension]
    have hnormalize :
        Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
              bregmanFormulaOnX S x0 uStar +
            Gamma N *
              (Finset.range N.1).sum (fun k =>
                let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                let stPrev := states k ω
                let δinner := inner κ;
                gamma κ * psWeightProduct spsP (T κ) /
                  (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                    (Finset.range (T κ)).sum (fun i =>
                      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                      let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                      (spsP ι * psWeightProduct spsP i)⁻¹ *
                        ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                          ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ))) =
          Bd + linear ω + (quadratic ω - quadraticMean) := by
      rw [← hdeterministic_normalize]
      simp [linear, quadratic, quadraticMean, deterministicOuter]
      -- Remaining pure algebra: distribute the finite sums and split
      -- `(M^2 + ‖δ‖_*^2)/(β p) + linear` into the deterministic
      -- `(M^2 + σ^2)/(β p)`, linear, realized quadratic, and centered
      -- `-σ^2/(β p)` pieces.  This is Eq. (8.1.69)'s pathwise
      -- decomposition, isolated from all probability arguments below.
      have hsplit :=
        (nested_weighted_master_bracket_decomp
          (s := Finset.range N.1)
          (t := fun k => Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
          (G := Gamma N)
          (C := fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))))
          (I := fun k i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            (psWeightProduct spsP i)⁻¹ * (spsP ι)⁻¹)
          (D := fun k i =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            beta κ * spsP ι)
          (M2 := fun _ _ => S.mGrowth ^ 2)
          (Q := fun k i =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let δinner := inner κ;
            let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
            dualNorm S δ ^ 2)
          (Sigma := fun _ _ => S.sigmaSq)
          (L := fun k i =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let δinner := inner κ;
            let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
            ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ))
      set_option maxHeartbeats 4000000 in
      rw [hsplit]
      ring
    calc
      gap ω
          ≤ Gamma N * beta oneTime * (1 - psWeightProduct spsP (T oneTime))⁻¹ *
              bregmanFormulaOnX S x0 uStar +
            Gamma N *
              (Finset.range N.1).sum (fun k =>
                let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                let stPrev := states k ω
                let δinner := inner κ;
                gamma κ * psWeightProduct spsP (T κ) /
                  (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                    (Finset.range (T κ)).sum (fun i =>
                      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                      let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                      (spsP ι * psWeightProduct spsP i)⁻¹ *
                        ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                          ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ))) := by
            simpa [gap, uStar] using hraw
      _ = Bd + linear ω + (quadratic ω - quadraticMean) := hnormalize
  let target : Set Ω :=
    {ω | gap ω > Bd + lambda * (linearScale + quadraticScale)}
  let linearBad : Set Ω := {ω | linear ω > lambda * linearScale}
  let quadraticBad : Set Ω := {ω | quadratic ω > quadraticMean + lambda * quadraticScale}
  have hprob_scale :
      theorem82ProbabilityScale_formulaExtension S uStar hcompact N beta gamma Gamma T =
        linearScale + quadraticScale := by
    simp [linearScale, quadraticScale, theorem82ProbabilityScale_formulaExtension,
      genericProbabilityScale_formulaExtension]
  have htarget :
        {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S uStar >
              theorem82ExpectedBound_formulaExtension S x0 uStar N beta gamma Gamma T +
                lambda *
                  theorem82ProbabilityScale_formulaExtension S uStar hcompact N beta gamma Gamma T}
        = target := by
    ext ω
    simp [target, gap, Bd, hprob_scale]
  have hsubset : target ⊆ linearBad ∪ quadraticBad := by
    exact
      theorem82_highProbability_master_strict_event_subset_scalar
        gap linear quadratic Bd quadraticMean linearScale quadraticScale lambda
        hmaster_decomp
  have hlinear_tail :
      law.P linearBad ≤ ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
    -- Eq. (8.1.70): martingale large-deviation bound for the generated
    -- linear oracle-noise sum.  The route-local event has now been isolated.
    have hlinear_zero_of_integrable :
        (∀ κ i (hquery : ∀ ω, sgsGeneratedOracleQuery S inner κ i ω ∈ S.X),
          Integrable
            (fun ω =>
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω),
                uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ)
            law.P) →
          ∀ κ i,
            (∫ ω,
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω),
                uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ ∂law.P) = 0 := by
      intro hinner_int
      simpa [uStar] using
        sgsGeneratedOracleQuery_target_noise_inner_integral_zero_of_integrable
          (S := S) (law := law) inner uStar hindep hinner_int
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
                (uStar.1 - sgsGeneratedOracleQuery S inner κ i ω) ^ 2) law.P := by
      letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
      have hgenerated_avg_sq_from_bregman_window :
          ∀ κ m,
            (∀ i, i < m + 1 →
              Integrable
                (fun ω =>
                  bregmanFormulaOnX S
                    (⟨sgsGeneratedOracleQuery S inner κ i ω,
                      hquery_mem κ i ω⟩ : FeasiblePoint S)
                    uStar)
                law.P) →
            Integrable
              (fun ω =>
                S.primalNorm
                  (uStar.1 - (inner κ m ω).avg.1) ^ 2) law.P := by
        intro κ m hwindow
        simpa [uStar] using
          generated_sgs_inner_avg_sq_integrable_from_bregman_window
            (S := S) law uStar x0 beta gamma T states inner
            hrun hquery_mem hquery_meas κ m hwindow
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
              uStar)
          law.P
      let Xbar : ℕ → Prop := fun n =>
        Integrable
          (fun ω =>
            S.primalNorm (uStar.1 - (states n ω).xbar.1) ^ 2)
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
                              bregmanFormulaOnX S x0 uStar)
                            law.P :=
                        integrable_const _
                      have hcongr :
                          (fun ω =>
                            bregmanFormulaOnX S
                              (⟨sgsGeneratedOracleQuery S inner
                                  (⟨1, by omega⟩ : PositiveTime) 0 ω,
                                hquery_mem (⟨1, by omega⟩ : PositiveTime) 0 ω⟩ :
                                FeasiblePoint S)
                              uStar) =
                          (fun _ : Ω =>
                            bregmanFormulaOnX S x0 uStar) := by
                        funext ω
                        have hproc := hinner_proc (⟨1, by omega⟩ : PositiveTime)
                        have hinit_inner := hproc.2.1 ω
                        apply congrArg
                          (fun y : FeasiblePoint S =>
                            bregmanFormulaOnX S y uStar)
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
                              uStar) =
                          (fun ω =>
                            bregmanFormulaOnX S
                              (⟨sgsGeneratedOracleQuery S inner
                                  (predTime κcur hκcur_two)
                                  (T (predTime κcur hκcur_two)) ω,
                                hquery_mem (predTime κcur hκcur_two)
                                  (T (predTime κcur hκcur_two)) ω⟩ : FeasiblePoint S)
                              uStar) := by
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
                  (S := S) law uStar x0 beta gamma T states inner
                  hrun hbeta hgamma hquery_mem hquery_meas hgenerated_var κ j
                  (by simpa [Xbar] using houter_xbar_sq) hprev_window
        have hXbar_current : Xbar n := by
          cases n with
          | zero =>
              refine (integrable_const
                (c := S.primalNorm (uStar.1 - x0.1) ^ 2)).congr ?_
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
                        (uStar.1 - (inner κcur (T κcur) ω).avg.1) ^ 2)
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
                        (uStar.1 -
                          ((1 - gamma κcur) • (states m ω).xbar.1 +
                            gamma κcur • (inner κcur (T κcur) ω).avg.1)) ^ 2)
                    law.P :=
                primalNorm_sq_integrable_affine_update
                  (S := S) law.P uStar
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
          (S := S) law.P uStar
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
                uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P := by
      intro κ i
      let queryFP : Ω → FeasiblePoint S :=
        fun ω => ⟨sgsGeneratedOracleQuery S inner κ i ω, hquery_mem κ i ω⟩
      have hpair_meas : Measurable (fun ω => (queryFP ω, law.sample κ i ω)) :=
        (hquery_meas κ i).prod (law.sample_measurable κ i)
      have hleft_inner_aemeas :
          AEStronglyMeasurable
            (fun ω =>
              ⟪uStar.1 - sgsGeneratedOracleQuery S inner κ i ω,
                oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω)⟫_ℝ) law.P := by
        have hkernel :=
          oracle_residual_target_inner_measurable_of_residual_measurable
            (S := S) (x := uStar) law.oracle_residual_measurable
        simpa [queryFP] using (hkernel.comp hpair_meas).aestronglyMeasurable
      have hinner_aemeas :
          AEStronglyMeasurable
            (fun ω =>
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω),
                uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P :=
        hleft_inner_aemeas.congr
          (Filter.Eventually.of_forall (fun ω => by
            simpa using
              (real_inner_comm
                (uStar.1 - sgsGeneratedOracleQuery S inner κ i ω)
                (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω))).symm))
      exact
        generated_target_inner_integrable_of_primal_displacement_l2
          (S := S) law.P law.sample (sgsGeneratedOracleQuery S inner)
          uStar κ i (hdual_sq_int κ i) (hquery_disp_sq_int κ i) hinner_aemeas
    have hlinear_zero :
        ∀ κ i,
          (∫ ω,
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ ∂law.P) = 0 :=
      hlinear_zero_of_integrable (fun κ i _hquery => hlinear_int κ i)
    have hadapted_query :
        ∀ κ i,
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
            (fun ω => sgsGeneratedOracleQuery S inner κ i ω) := by
      exact hquery_strictPast_meas
    have hlinear_zero_lightScale :
        ∀ κ i,
          let ζ : Ω → ℝ := fun ω =>
            ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                (law.sample κ i ω),
              uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
          let lightScale : ℝ :=
            2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
          lightScale = 0 → ζ =ᵐ[law.P] 0 := by
      exact
        theorem82_linear_zero_of_zero_lightScale
          (S := S) (law := law) (uStar := uStar) (inner := inner)
          hcompact hquery_mem hgenerated_light
    have hlinear_tail_strict :
        law.P {ω | linear ω > lambda * linearScale} ≤
          ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
      simpa [linear, linearScale, uStar, sgsGeneratedOracleQuery] using
        theorem82_linear_tail_martingale_large_deviation_formulaExtension
          (S := S) (law := law) (uStar := uStar) (beta := beta) (gamma := gamma)
          (Gamma := Gamma) (T := T) (N := N) (lambda := lambda) (inner := inner)
          hlambda hbeta hgamma hGamma_pos hTpos hcompact hlinear_int
          hadapted_query hlinear_condExp_zero hlinear_exp_sq_integrable
          hlinear_condExp_light hlinear_zero_lightScale
    simpa [linearBad] using hlinear_tail_strict
  have hquadratic_tail :
      law.P quadraticBad ≤ ENNReal.ofReal (Real.exp (-lambda)) := by
    -- Eq. (8.1.71): Markov/light-tail bound for the strict centered quadratic
    -- oracle-noise event.  The strict inequality is source-critical: the
    -- non-strict event is false in the deterministic zero-variance case.
    rcases hgenerated_light with ⟨_hquery_light, hlight_pos | hlight_det⟩
    · -- Positive-variance branch: Markov plus the convexity/Jensen
      -- exponential-moment aggregation from Lan Eq. (8.1.71).
      rcases hlight_pos with ⟨hsigma_pos, hlight_moment⟩
      have hlight_exp_integrable :
          ∀ κ i,
            Integrable
              (fun ω =>
                Real.exp (lightTailExponent S
                  (dualNorm S
                    (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                      (law.sample κ i ω)) ^ 2))) law.P :=
        fun κ i => (hlight_moment κ i).1
      have hlight_int :
          ∀ κ i,
            (∫ ω,
              Real.exp (lightTailExponent S
                (dualNorm S
                  (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω)) ^ 2)) ∂law.P) ≤ Real.exp 1 :=
        fun κ i => (hlight_moment κ i).2
      have hquadMean_eq_scale : quadraticMean = quadraticScale := by
        dsimp [quadraticMean, quadraticScale]
        exact
          nested_quadratic_mean_scale_algebra_coeff
            (s := Finset.range N.1)
            (t := fun k =>
              Finset.range
                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
            (G := Gamma N) (sigma := S.sigmaSq)
            (C := fun k =>
              gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                psWeightProduct spsP
                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
            (D := fun k =>
              Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))
            (E := fun k =>
              1 - psWeightProduct spsP
                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
            (B := fun k i =>
              beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))
            (sp := fun _ i =>
              spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime))
            (prevP := fun _ i => psWeightProduct spsP i)
      have hquadScale_pos : 0 < quadraticScale := by
        -- Eq. (8.1.71) has a strictly positive variance scale in this branch.
        -- Strictness comes from the first outer block, where Eq. (8.1.25)
        -- gives `γ₁ = 1`; all other displayed coefficients are nonnegative.
        dsimp [quadraticScale]
        let innerTerm : ℕ → ℕ → ℝ := fun k i =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          gamma κ * psWeightProduct spsP (T κ) /
            (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i)
        let outerTerm : ℕ → ℝ := fun k =>
          (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
            (innerTerm k)
        have hP_nonneg : ∀ n : ℕ, 0 ≤ psWeightProduct spsP n := by
          intro n
          rw [psWeightProduct_spsP_eq n]
          positivity
        have hP_pos : ∀ n : ℕ, 0 < psWeightProduct spsP n := by
          intro n
          rw [psWeightProduct_spsP_eq n]
          positivity
        have hsps_pos : ∀ i : PositiveTime, 0 < spsP i := by
          intro i
          unfold spsP
          have hi : 0 < (i.1 : ℝ) := by exact_mod_cast i.2
          nlinarith
        have hinner_nonneg :
            ∀ k i, 0 ≤ innerTerm k i := by
          intro k i
          dsimp [innerTerm]
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          have hnum_nonneg : 0 ≤ gamma κ * psWeightProduct spsP (T κ) :=
            mul_nonneg (gammaRangeCondition_nonnegative hgamma κ) (hP_nonneg (T κ))
          have hden_pos :
              0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i := by
            exact
              mul_pos
                (mul_pos
                  (mul_pos
                    (mul_pos (hbeta κ) (hGamma_pos κ))
                    (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                  (sq_pos_of_pos (hsps_pos ι)))
                (hP_pos i)
          exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
        have houter_nonneg : ∀ k ∈ Finset.range N.1, 0 ≤ outerTerm k := by
          intro k _hk
          dsimp [outerTerm]
          exact Finset.sum_nonneg (fun i _hi => hinner_nonneg k i)
        have houter_zero_pos : 0 < outerTerm 0 := by
          dsimp [outerTerm]
          let κ : PositiveTime := ⟨0 + 1, Nat.succ_pos 0⟩
          let ι : PositiveTime := ⟨0 + 1, Nat.succ_pos 0⟩
          have hzero_mem : 0 ∈ Finset.range (T κ) := by
            simpa using hTpos κ
          have hgamma_one : gamma κ = 1 := by
            simpa [κ, oneTime] using hlower.1
          have hnum_pos : 0 < gamma κ * psWeightProduct spsP (T κ) := by
            rw [hgamma_one]
            simpa using hP_pos (T κ)
          have hden_pos :
              0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP 0 := by
            exact
              mul_pos
                (mul_pos
                  (mul_pos
                    (mul_pos (hbeta κ) (hGamma_pos κ))
                    (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                  (sq_pos_of_pos (hsps_pos ι)))
                (hP_pos 0)
          have hzero_pos : 0 < innerTerm 0 0 := by
            dsimp [innerTerm, κ, ι]
            exact div_pos hnum_pos hden_pos
          have hle :
              innerTerm 0 0 ≤ (Finset.range (T κ)).sum (innerTerm 0) :=
            Finset.single_le_sum (fun i _hi => hinner_nonneg 0 i) hzero_mem
          exact lt_of_lt_of_le hzero_pos hle
        have hsum_pos :
            0 < (Finset.range N.1).sum outerTerm := by
          have hzero_mem : 0 ∈ Finset.range N.1 := by
            simpa using N.2
          have hle : outerTerm 0 ≤ (Finset.range N.1).sum outerTerm :=
            Finset.single_le_sum (fun k hk => houter_nonneg k hk) hzero_mem
          exact lt_of_lt_of_le houter_zero_pos hle
        exact mul_pos (mul_pos hsigma_pos (hGamma_pos N)) hsum_pos
      have hexp_moment :
          Integrable (fun ω => Real.exp (quadratic ω / quadraticScale)) law.P ∧
            (∫ ω, Real.exp (quadratic ω / quadraticScale) ∂law.P) ≤ Real.exp 1 := by
        -- Source Eq. (8.1.71): convexity of `exp` applied to the normalized
        -- nonnegative coefficients, then the generated light-tail moment
        -- `hlight_int κ i` for each oracle-noise coordinate.  The same
        -- aggregation supplies the integrability required by strict Markov.
        let idx : Finset (Σ _k : ℕ, ℕ) :=
          (Finset.range N.1).sigma (fun k =>
            Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
        let q : (Σ _k : ℕ, ℕ) → ℝ := fun a =>
          let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
          let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
          (S.sigmaSq * Gamma N *
            (gamma κ * psWeightProduct spsP (T κ) /
              (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                spsP ι ^ 2 * psWeightProduct spsP a.2))) / quadraticScale
        let Y : (Σ _k : ℕ, ℕ) → Ω → ℝ := fun a ω =>
          let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
          lightTailExponent S
            (dualNorm S
              (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ a.2 ω)
                (law.sample κ a.2 ω)) ^ 2)
        refine
          finite_exp_moment_of_pointwise_le_weighted_sum
            (μ := law.P) idx q Y (fun ω => quadratic ω / quadraticScale) ?_
            ?_ ?_ ?_ ?_ ?_
        · -- Measurability of the normalized quadratic exponential.  This is
          -- a local well-definedness leaf for the finite generated sum.
          have hquad_aesm : AEStronglyMeasurable quadratic law.P := by
            dsimp [quadratic]
            refine
              (Finset.aestronglyMeasurable_fun_sum (μ := law.P) (Finset.range N.1)
                (fun k _hk => ?_)).const_mul (Gamma N)
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            refine
              (Finset.aestronglyMeasurable_fun_sum (μ := law.P) (Finset.range (T κ))
                (fun i _hi => ?_)).const_mul
                  (gamma κ * psWeightProduct spsP (T κ) /
                    (Gamma κ * (1 - psWeightProduct spsP (T κ))))
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            have hdual_int :
                Integrable
                  (fun ω =>
                    dualNorm S
                      (oracleNoiseAt S
                        (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2) law.P := by
              simpa using
                generatedSFOVariance_integrable_obligation
                  S law.P law.sample (sgsGeneratedOracleQuery S inner)
                  hgenerated_var κ i
            have hterm_int :
                Integrable
                  (fun ω =>
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      (dualNorm S
                        (oracleNoiseAt S
                          (sgsGeneratedOracleQuery S inner κ i ω)
                          (law.sample κ i ω)) ^ 2 / (beta κ * spsP ι))) law.P := by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                hdual_int.const_mul
                  (((spsP ι * psWeightProduct spsP i)⁻¹) *
                    (beta κ * spsP ι)⁻¹)
            exact hterm_int.aestronglyMeasurable
          have hquad_aemeas :
              AEMeasurable (fun ω => quadratic ω / quadraticScale) law.P :=
            hquad_aesm.aemeasurable.div_const quadraticScale
          exact
            (Real.measurable_exp.comp_aemeasurable
              hquad_aemeas).aestronglyMeasurable
        · intro a _ha
          rcases a with ⟨k, i⟩
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          simpa [Y, κ] using hlight_exp_integrable κ i
        · intro a _ha
          rcases a with ⟨k, i⟩
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          simpa [Y, κ] using hlight_int κ i
        · -- Nonnegativity of the normalized Eq. (8.1.71) coefficients.
          intro a ha
          rcases a with ⟨k, i⟩
          dsimp [q]
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
          have hP_nonneg : ∀ n : ℕ, 0 ≤ psWeightProduct spsP n := by
            intro n
            rw [psWeightProduct_spsP_eq n]
            positivity
          have hP_pos : ∀ n : ℕ, 0 < psWeightProduct spsP n := by
            intro n
            rw [psWeightProduct_spsP_eq n]
            positivity
          have hsps_pos : 0 < spsP ι := by
            unfold spsP
            have hi : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
            nlinarith
          have hden_pos :
              0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i := by
            exact
              mul_pos
                (mul_pos
                  (mul_pos
                    (mul_pos (hbeta κ) (hGamma_pos κ))
                    (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                  (sq_pos_of_pos hsps_pos))
                (hP_pos i)
          have hinner_nonneg :
              0 ≤ gamma κ * psWeightProduct spsP (T κ) /
                (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i) := by
            exact div_nonneg
              (mul_nonneg (gammaRangeCondition_nonnegative hgamma κ)
                (hP_nonneg (T κ)))
              (le_of_lt hden_pos)
          exact div_nonneg
            (mul_nonneg (mul_nonneg (le_of_lt hsigma_pos) (le_of_lt (hGamma_pos N)))
              hinner_nonneg)
            (le_of_lt hquadScale_pos)
        · -- The normalized deterministic coefficients sum to one; this is
          -- exactly `hquadMean_eq_scale` divided by `quadraticScale`.
          have hscale_ne : quadraticScale ≠ 0 := ne_of_gt hquadScale_pos
          have hraw_sum :
              idx.sum (fun a =>
                S.sigmaSq * Gamma N *
                  (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                   let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                   gamma κ * psWeightProduct spsP (T κ) /
                    (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP a.2))) =
                quadraticScale := by
            dsimp [idx, quadraticScale]
            rw [Finset.sum_sigma]
            calc
              (Finset.range N.1).sum (fun k =>
                  (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                    (fun i =>
                      S.sigmaSq * Gamma N *
                        (gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                          psWeightProduct spsP
                            (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                            (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              (1 - psWeightProduct spsP
                                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                              spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                              psWeightProduct spsP i)))) =
                (Finset.range N.1).sum (fun k =>
                  S.sigmaSq * Gamma N *
                    (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                      (fun i =>
                        gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                          psWeightProduct spsP
                            (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                            (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              (1 - psWeightProduct spsP
                                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                              spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                              psWeightProduct spsP i))) := by
                  refine Finset.sum_congr rfl ?_
                  intro k _hk
                  rw [Finset.mul_sum]
              _ =
                S.sigmaSq * Gamma N *
                  (Finset.range N.1).sum (fun k =>
                    (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                      (fun i =>
                        gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                          psWeightProduct spsP
                            (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                            (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              (1 - psWeightProduct spsP
                                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                              spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                              psWeightProduct spsP i))) := by
                  rw [Finset.mul_sum]
          calc
            idx.sum q =
                idx.sum (fun a =>
                  (S.sigmaSq * Gamma N *
                    (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                     let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                     gamma κ * psWeightProduct spsP (T κ) /
                      (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                        spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                    quadraticScale) := by
                  rfl
            _ =
                idx.sum (fun a =>
                  S.sigmaSq * Gamma N *
                    (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                     let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                     gamma κ * psWeightProduct spsP (T κ) /
                      (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                        spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                  quadraticScale := by
                  rw [Finset.sum_div]
            _ = quadraticScale / quadraticScale := by
                  rw [hraw_sum]
            _ = 1 := div_self hscale_ne
        · -- Pointwise Jensen for `Real.exp` with the normalized coefficients.
          -- The scalar identity rewrites `quadratic / quadraticScale` as the
          -- weighted average of the coordinate light-tail exponents.
          apply Filter.Eventually.of_forall
          intro ω
          have hq_nonneg_local : ∀ a ∈ idx, 0 ≤ q a := by
            intro a ha
            rcases a with ⟨k, i⟩
            dsimp [q]
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            have hP_nonneg : ∀ n : ℕ, 0 ≤ psWeightProduct spsP n := by
              intro n
              rw [psWeightProduct_spsP_eq n]
              positivity
            have hP_pos : ∀ n : ℕ, 0 < psWeightProduct spsP n := by
              intro n
              rw [psWeightProduct_spsP_eq n]
              positivity
            have hsps_pos : 0 < spsP ι := by
              unfold spsP
              have hi : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
              nlinarith
            have hden_pos :
                0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i := by
              exact
                mul_pos
                  (mul_pos
                    (mul_pos
                      (mul_pos (hbeta κ) (hGamma_pos κ))
                      (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                    (sq_pos_of_pos hsps_pos))
                  (hP_pos i)
            have hinner_nonneg :
                0 ≤ gamma κ * psWeightProduct spsP (T κ) /
                  (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i) := by
              exact div_nonneg
                (mul_nonneg (gammaRangeCondition_nonnegative hgamma κ)
                  (hP_nonneg (T κ)))
                (le_of_lt hden_pos)
            exact div_nonneg
              (mul_nonneg (mul_nonneg (le_of_lt hsigma_pos) (le_of_lt (hGamma_pos N)))
                hinner_nonneg)
              (le_of_lt hquadScale_pos)
          have hq_sum_local : idx.sum q = 1 := by
            have hscale_ne : quadraticScale ≠ 0 := ne_of_gt hquadScale_pos
            have hraw_sum :
                idx.sum (fun a =>
                  S.sigmaSq * Gamma N *
                    (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                     let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                     gamma κ * psWeightProduct spsP (T κ) /
                      (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                        spsP ι ^ 2 * psWeightProduct spsP a.2))) =
                  quadraticScale := by
              dsimp [idx, quadraticScale]
              rw [Finset.sum_sigma]
              calc
                (Finset.range N.1).sum (fun k =>
                    (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                      (fun i =>
                        S.sigmaSq * Gamma N *
                          (gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                            psWeightProduct spsP
                              (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                              (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                (1 - psWeightProduct spsP
                                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                psWeightProduct spsP i)))) =
                  (Finset.range N.1).sum (fun k =>
                    S.sigmaSq * Gamma N *
                      (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                        (fun i =>
                          gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                            psWeightProduct spsP
                              (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                              (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                (1 - psWeightProduct spsP
                                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                psWeightProduct spsP i))) := by
                    refine Finset.sum_congr rfl ?_
                    intro k _hk
                    rw [Finset.mul_sum]
                _ =
                  S.sigmaSq * Gamma N *
                    (Finset.range N.1).sum (fun k =>
                      (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                        (fun i =>
                          gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                            psWeightProduct spsP
                              (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                              (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                (1 - psWeightProduct spsP
                                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                psWeightProduct spsP i))) := by
                    rw [Finset.mul_sum]
            calc
              idx.sum q =
                  idx.sum (fun a =>
                    (S.sigmaSq * Gamma N *
                      (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                       let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                       gamma κ * psWeightProduct spsP (T κ) /
                        (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                          spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                      quadraticScale) := by
                    rfl
              _ =
                  idx.sum (fun a =>
                    S.sigmaSq * Gamma N *
                      (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                       let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                       gamma κ * psWeightProduct spsP (T κ) /
                        (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                          spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                    quadraticScale := by
                    rw [Finset.sum_div]
              _ = quadraticScale / quadraticScale := by
                    rw [hraw_sum]
              _ = 1 := div_self hscale_ne
          have hweighted :
              quadratic ω / quadraticScale =
                idx.sum (fun a => q a * Y a ω) := by
            have hsigma_ne : S.sigmaSq ≠ 0 := ne_of_gt hsigma_pos
            have hraw :=
              nested_quadratic_normalized_lightTail_algebra_outer
                (s := Finset.range N.1)
                (t := fun k =>
                  Finset.range
                    (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
                (G := Gamma N) (sigma := S.sigmaSq) (scale := quadraticScale)
                (C := fun k =>
                  let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                  gamma κ * psWeightProduct spsP (T κ) /
                    (Gamma κ * (1 - psWeightProduct spsP (T κ))))
                (B := fun k _i =>
                  beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))
                (sp := fun _k i =>
                  spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime))
                (prevP := fun _k i => psWeightProduct spsP i)
                (Z := fun k i =>
                  let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                  dualNorm S
                    (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                      (law.sample κ i ω)) ^ 2)
                hsigma_ne
            calc
              quadratic ω / quadraticScale =
                (Gamma N *
                  (Finset.range N.1).sum (fun k =>
                    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                    gamma κ * psWeightProduct spsP (T κ) /
                      (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                        (Finset.range (T κ)).sum (fun i =>
                          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                          (spsP ι * psWeightProduct spsP i)⁻¹ *
                            (dualNorm S
                              (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                                (law.sample κ i ω)) ^ 2 /
                              (beta κ * spsP ι))))) / quadraticScale := by
                    rfl
              _ =
                ((Finset.range N.1).sigma (fun k =>
                  Finset.range
                    (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))).sum (fun x =>
                      ((S.sigmaSq * Gamma N *
                          ((let κ : PositiveTime := ⟨x.1 + 1, Nat.succ_pos x.1⟩;
                            gamma κ * psWeightProduct spsP (T κ) /
                              (Gamma κ * (1 - psWeightProduct spsP (T κ)))) /
                            (beta (⟨x.1 + 1, Nat.succ_pos x.1⟩ : PositiveTime) *
                              spsP (⟨x.2 + 1, Nat.succ_pos x.2⟩ : PositiveTime) ^ 2 *
                              psWeightProduct spsP x.2))) / quadraticScale) *
                        (dualNorm S
                          (oracleNoiseAt S
                            (sgsGeneratedOracleQuery S inner
                              (⟨x.1 + 1, Nat.succ_pos x.1⟩ : PositiveTime) x.2 ω)
                            (law.sample
                              (⟨x.1 + 1, Nat.succ_pos x.1⟩ : PositiveTime) x.2 ω)) ^ 2 /
                          S.sigmaSq)) := by
                    simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
              _ = idx.sum (fun a => q a * Y a ω) := by
                    dsimp [idx, q, Y, lightTailExponent]
                    refine Finset.sum_congr rfl ?_
                    intro a ha
                    rcases a with ⟨k, i⟩
                    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                    have hGamma_ne : Gamma κ ≠ 0 := ne_of_gt (hGamma_pos κ)
                    have hbeta_ne : beta κ ≠ 0 := ne_of_gt (hbeta κ)
                    have hsps_pos : 0 < spsP ι := by
                      unfold spsP
                      have hi : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
                      nlinarith
                    have hsps_ne : spsP ι ≠ 0 := ne_of_gt hsps_pos
                    have hPprev_pos : 0 < psWeightProduct spsP i := by
                      rw [psWeightProduct_spsP_eq i]
                      positivity
                    have hPprev_ne : psWeightProduct spsP i ≠ 0 := ne_of_gt hPprev_pos
                    have hPden_pos :
                        0 < 1 - psWeightProduct spsP (T κ) :=
                      one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)
                    have hPden_ne : 1 - psWeightProduct spsP (T κ) ≠ 0 :=
                      ne_of_gt hPden_pos
                    have hscale_ne : quadraticScale ≠ 0 := ne_of_gt hquadScale_pos
                    have hbig_ne :
                        -(psWeightProduct spsP (T κ) * Gamma κ * beta κ *
                            spsP ι ^ 2 * psWeightProduct spsP i) +
                            Gamma κ * beta κ * spsP ι ^ 2 *
                              psWeightProduct spsP i ≠ 0 := by
                      have hprod_pos :
                          0 < Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                              beta κ * spsP ι ^ 2 * psWeightProduct spsP i := by
                        exact
                          mul_pos
                            (mul_pos
                              (mul_pos
                                (mul_pos (hGamma_pos κ) hPden_pos)
                                (hbeta κ))
                              (sq_pos_of_pos hsps_pos))
                            hPprev_pos
                      have heq :
                          -(psWeightProduct spsP (T κ) * Gamma κ * beta κ *
                              spsP ι ^ 2 * psWeightProduct spsP i) +
                              Gamma κ * beta κ * spsP ι ^ 2 *
                                psWeightProduct spsP i =
                            Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                              beta κ * spsP ι ^ 2 * psWeightProduct spsP i := by
                        ring
                      rw [heq]
                      exact ne_of_gt hprod_pos
                    dsimp [κ, ι]
                    field_simp [hGamma_ne, hbeta_ne, hsps_ne, hPprev_ne,
                      hPden_ne, hscale_ne, hsigma_ne, hbig_ne]
                    try ring
          exact
            finite_exp_jensen_of_weighted_sum idx q (fun a => Y a ω)
              (quadratic ω / quadraticScale) hq_nonneg_local hq_sum_local
              hweighted
      have hsubset_exp :
          quadraticBad ⊆ {ω | quadratic ω / quadraticScale > 1 + lambda} := by
        intro ω hω
        have hscale_nonneg : 0 ≤ quadraticScale := le_of_lt hquadScale_pos
        have hbad :
            quadratic ω > quadraticScale + lambda * quadraticScale := by
          simpa [quadraticBad, hquadMean_eq_scale] using hω
        have hfactor :
            quadraticScale + lambda * quadraticScale =
              (1 + lambda) * quadraticScale := by ring
        have hbad' : quadratic ω > (1 + lambda) * quadraticScale := by
          simpa [hfactor] using hbad
        exact (lt_div_iff₀ hquadScale_pos).2 hbad'
      have htail :=
        strict_markov_exp_tail_from_exp_moment
          (μ := law.P) (f := fun ω => quadratic ω / quadraticScale)
          lambda hexp_moment.1 hexp_moment.2 hlambda
      exact le_trans (measure_mono hsubset_exp) htail
    · rcases hlight_det with ⟨hsigma_zero, hnoise_zero⟩
      have hquadMean_zero : quadraticMean = 0 := by
        simp [quadraticMean, hsigma_zero]
      have hquadScale_zero : quadraticScale = 0 := by
        simp [quadraticScale, hsigma_zero]
      have hquadratic_zero_ae : ∀ᵐ ω ∂law.P, quadratic ω = 0 := by
        have houter :
            ∀ᵐ ω ∂law.P,
              ∀ k ∈ Finset.range N.1,
                ∀ i ∈ Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)),
                  dualNorm S
                    (oracleNoiseAt S
                      ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                      (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 := by
          refine Finset.induction_on (Finset.range N.1) ?_ ?_
          · simp
          · intro k ks hk_not hks
            have hk_ae :
                ∀ᵐ ω ∂law.P,
                  ∀ i ∈ Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)),
                    dualNorm S
                      (oracleNoiseAt S
                        ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                        (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 := by
              refine Finset.induction_on
                (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) ?_ ?_
              · simp
              · intro i is hi_not his
                have hki :
                    ∀ᵐ ω ∂law.P,
                      dualNorm S
                        (oracleNoiseAt S
                          ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                          (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 := by
                  simpa [sgsGeneratedOracleQuery] using
                    hnoise_zero (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i
                filter_upwards [hki, his] with ω hkiω hisω j hj
                simp at hj
                rcases hj with hj | hj
                · subst hj
                  exact hkiω
                · exact hisω j hj
            filter_upwards [hk_ae, hks] with ω hkω hksω j hj
            simp at hj
            rcases hj with hj | hj
            · subst hj
              exact hkω
            · exact hksω j hj
        filter_upwards [houter] with ω hω
        have hsum_zero :
            (Finset.range N.1).sum (fun k =>
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
              let δinner := inner κ;
              gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                  (Finset.range (T κ)).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      (dualNorm S δ ^ 2 / (beta κ * spsP ι)))) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro k hk
          have hinner_zero :
              (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum (fun i =>
                let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                let δ := oracleNoiseAt S
                  ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                  (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω);
                (spsP ι * psWeightProduct spsP i)⁻¹ *
                  (dualNorm S δ ^ 2 /
                    (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) * spsP ι))) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro i hi
            have hδ :
                dualNorm S
                  (oracleNoiseAt S
                    ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                    (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 :=
              hω k hk i hi
            simp [hδ]
          dsimp only
          rw [hinner_zero]
          ring
        dsimp only [quadratic]
        rw [hsum_zero, mul_zero]
      have hnot_bad : ∀ᵐ ω ∂law.P, ω ∉ quadraticBad := by
        filter_upwards [hquadratic_zero_ae] with ω hquad
        simp [quadraticBad, hquad, hquadMean_zero, hquadScale_zero]
      have hbad_zero : law.P quadraticBad = 0 := by
        simpa using
          ((MeasureTheory.ae_iff (μ := law.P)
            (p := fun ω => ω ∉ quadraticBad)).mp hnot_bad)
      rw [hbad_zero]
      exact zero_le _
  have hsource_union :
      law.P target ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) :=
    theorem82_highProbability_union_bound_source_formulaExtension law.P target linearBad
      quadraticBad lambda hsubset hlinear_tail hquadratic_tail
  have hchecked_source_union :
      law.P target ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) :=
    theorem82_final_probability_constant_source_boundary_formulaExtension
      law.P target lambda hsource_union
  rw [htarget]
  exact hchecked_source_union

/-- Run-level formula-extension helper for Theorem 8.2(c), expected form under the reverse
monotonicity case, with the feasible-formula Bregman-envelope caveat. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_expected_runFormulaExtension [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hcompact : IsCompact S.X)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma T) :
    (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
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
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  have hgamma_nonneg : gammaNonnegativeCondition gamma := hrun.1.2.2.2
  have hgamma : gammaRangeCondition gamma :=
    gammaRangeCondition_of_reverseMonotonicity_generated S beta gamma Gamma T
      hbeta hgamma_nonneg hlower hGamma hmono
  have hreverse_boundary :
      ∀ ω,
        let process : ℕ → SGSState S := fun n => states n ω;
        let c : ℕ → ℝ := fun n =>
          if hn : 1 ≤ n then
            gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
              (Gamma ⟨n, hn⟩ * (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
          else 0;
        let V : ℕ → ℝ := fun n =>
          bregmanFormulaOnX S (process n).x ⟨xStar, hxStar.1⟩;
        Gamma N *
            Finset.sum (Finset.Icc 1 N.1) (fun t => c t * (V (t - 1) - V t)) ≤
          gamma N * beta N *
              bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
            (1 - psWeightProduct spsP (T N))⁻¹ := by
    intro ω
    simpa using
      reverse_bregman_telescope_envelope_scaled_formulaExtension_beforeSelected
        (S := S) beta gamma Gamma T N (fun n => states n ω)
        ⟨xStar, hxStar.1⟩ hcompact hbeta hgamma hGamma hmono
  have hTpos : ∀ k : PositiveTime, 0 < T k :=
    positive_inner_budget_of_reverseMonotonicity_beforeMaster beta gamma Gamma T hmono
  have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
    outer_gamma_positive_of_weight_condition_and_reverse_denom_beforeMaster
      beta gamma Gamma T hgamma hGamma hmono
  have hraw :
      ∀ ω,
        objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S ⟨xStar, hxStar.1⟩ ≤
          Gamma N *
            (let process : ℕ → SGSState S := fun n => states n ω;
             let c : ℕ → ℝ := fun n =>
              if hn : 1 ≤ n then
                gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
                  (Gamma ⟨n, hn⟩ *
                    (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
              else 0;
             let V : ℕ → ℝ := fun n =>
              bregmanFormulaOnX S (process n).x ⟨xStar, hxStar.1⟩;
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
                      let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                      (spsP ι * psWeightProduct spsP i)⁻¹ *
                        ((S.mGrowth ^ 2 + dualNorm S δ ^ 2) / (beta κ * spsP ι) +
                          ⟪δ, xStar - (δinner i ω).u.1⟫_ℝ))) :=
    generated_sgs_raw_master_inequality_8_1_69_formulaExtension
      (S := S) x0 beta gamma Gamma T law.sample N states inner hrun.1
      ⟨xStar, hxStar.1⟩ hbeta hgamma hlower hGamma hTpos hGamma_pos
  classical
  let gap : Ω → ℝ := fun ω =>
    objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
      objectiveOn S ⟨xStar, hxStar.1⟩
  let reverseBoundary : ℝ :=
    gamma N * beta N * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
      (1 - psWeightProduct spsP (T N))⁻¹
  let bregDrop : Ω → ℝ := fun ω =>
    Gamma N *
      (let process : ℕ → SGSState S := fun n => states n ω;
       let c : ℕ → ℝ := fun n =>
        if hn : 1 ≤ n then
          gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
            (Gamma ⟨n, hn⟩ *
              (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
        else 0;
       let V : ℕ → ℝ := fun n =>
        bregmanFormulaOnX S (process n).x ⟨xStar, hxStar.1⟩;
       Finset.sum (Finset.Icc 1 N.1) (fun t =>
        c t * (V (t - 1) - V t)))
  let outerStoch : Ω → ℝ := fun ω =>
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
  have hmaster_pointwise : gap ≤ fun ω => reverseBoundary + Gamma N * outerStoch ω := by
    intro ω
    have hrawω : gap ω ≤ bregDrop ω + Gamma N * outerStoch ω := by
      simpa [gap, bregDrop, outerStoch] using hraw ω
    have hrevω : bregDrop ω ≤ reverseBoundary := by
      simpa [bregDrop, reverseBoundary] using hreverse_boundary ω
    linarith
  have hquad :
      ∀ κ i,
        (∫ ω,
          dualNorm S
            (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω)) ^ 2 ∂law.P) ≤ S.sigmaSq :=
    sgsGeneratedOracleQuery_dual_noise_sq_integral_le
      (S := S) law.P law.sample inner hgenerated_var
  have hindep_full := hindep
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
        (S := S) (law := law) inner ⟨xStar, hxStar.1⟩ hindep_full hinner_int
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
  let deterministicOuter : ℝ :=
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
      gamma κ * psWeightProduct spsP (T κ) /
        (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
          (Finset.range (T κ)).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι))))
  have hmasterRHS_int :
      Integrable (fun ω => reverseBoundary + Gamma N * outerStoch ω) law.P := by
    have houter_const :
        Integrable (fun _ : Ω => reverseBoundary) law.P :=
      integrable_const _
    have houter_sum : Integrable outerStoch law.P := by
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
  have hle_master :
      (∫ ω, gap ω ∂law.P) ≤
        ∫ ω, reverseBoundary + Gamma N * outerStoch ω ∂law.P :=
    MeasureTheory.integral_mono_of_nonneg hgap_nonneg hmasterRHS_int
      (Filter.Eventually.of_forall hmaster_pointwise)
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
  have hinnerBound : ∀ κ,
      (∫ ω,
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω);
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
        let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω);
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
  have houterBound :
      (∫ ω, outerStoch ω ∂law.P) ≤ deterministicOuter := by
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
            ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι))))
      (summand := fun k ω =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω);
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
              let δ := oracleNoiseAt S ((inner κ i ω).u.1) (law.sample κ i ω);
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
  have hmaster_split :
      (∫ ω, reverseBoundary + Gamma N * outerStoch ω ∂law.P) =
        reverseBoundary + Gamma N * ∫ ω, outerStoch ω ∂law.P := by
    have hscaled_outer_int :
        Integrable (fun ω => Gamma N * outerStoch ω) law.P := by
      have hdiff := hmasterRHS_int.sub (integrable_const (c := reverseBoundary))
      refine hdiff.congr ?_
      filter_upwards with ω
      simp only [Pi.sub_apply]
      ring
    calc
      (∫ ω, reverseBoundary + Gamma N * outerStoch ω ∂law.P)
          = (∫ _ω : Ω, reverseBoundary ∂law.P) +
              ∫ ω, Gamma N * outerStoch ω ∂law.P := by
              exact integral_add (integrable_const _) hscaled_outer_int
      _ = reverseBoundary + Gamma N * ∫ ω, outerStoch ω ∂law.P := by
              simp [integral_const_mul]
  have hdeterministic_normalize :
      reverseBoundary + Gamma N * deterministicOuter =
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
  calc
    (∫ ω, objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
        objectiveOn S ⟨xStar, hxStar.1⟩ ∂law.P)
        = ∫ ω, gap ω ∂law.P := by
          rfl
    _ ≤ ∫ ω, reverseBoundary + Gamma N * outerStoch ω ∂law.P := hle_master
    _ = reverseBoundary + Gamma N * ∫ ω, outerStoch ω ∂law.P := hmaster_split
    _ ≤ reverseBoundary + Gamma N * deterministicOuter := by
          have hscaled :
              Gamma N * (∫ ω, outerStoch ω ∂law.P) ≤
                Gamma N * deterministicOuter :=
            mul_le_mul_of_nonneg_left houterBound (le_of_lt (hGamma_pos N))
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hscaled reverseBoundary
    _ = gamma N * beta N * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
          (1 - psWeightProduct spsP (T N))⁻¹ +
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (S.mGrowth ^ 2 + S.sigmaSq) * gamma κ * psWeightProduct spsP (T κ) /
                (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i))) := hdeterministic_normalize

/-- Source-boundary run-level helper for Theorem 8.2(c), expected form, with
positive paper budgets and checked quotients in the stochastic summation.

Book JSON citations:
`book/FOML/StochasticGradientSliding.json:key_lemmas[7]` states Theorem 8.2,
`book/FOML/StochasticGradientSliding.json:assumptions[8-9]` states compactness
and the Bregman envelope, and
`book/FOML/StochasticGradientSliding.json:assumptions[14]` states the reverse
monotonicity condition.

Downstream Phase 2 instruction: prove the corrected compact feasible-Bregman
statement; do not promote it as the original source-typed Theorem 8.2(c) without
closing the Section 3.2 domain bridge. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_expected_sourceBoundary_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    expectedOutputGap S law x0 beta gamma (innerBudgetNat T) states inner N
        xStar hxStar hrun hindep ≤
        theorem82ReverseExpectedBound_checkedFormulaExtension S ⟨xStar, hxStar.1⟩
          hcompact N beta gamma Gamma T
          (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
            (IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
              law.sample states inner hrun)
            hlower hGamma hmono) := by
  have hbeta : ∀ k : PositiveTime, 0 < beta k :=
    IsGeneratedSGSProcess_beta_pos S x0 beta gamma (innerBudgetNat T)
      law.sample states inner hrun
  have hgamma_nonneg : gammaNonnegativeCondition gamma := hrun.2.2.2
  have hgamma : gammaRangeCondition gamma :=
    gammaRangeCondition_of_reverseMonotonicity_generated S beta gamma Gamma
      (innerBudgetNat T) hbeta hgamma_nonneg hlower hGamma hmono
  have hrun_formula :
      IsGeneratedSGSProcess_formulaExtension S x0 beta gamma (innerBudgetNat T)
        law.sample states inner := by
    exact ⟨hrun, trivial⟩
  have hchecked :=
    theorem82ReverseExpectedBound_checked_eq_formulaExtension S
      ⟨xStar, hxStar.1⟩ hcompact N beta gamma Gamma T
      (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
        hbeta hlower hGamma hmono)
  rw [hchecked]
  have hraw :=
    SGSGenericConvergence_Theorem8_2_reverse_expected_runFormulaExtension
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma)
      (T := innerBudgetNat T) (N := N) (states := states) (inner := inner)
      hrun_formula hindep hxStar hbeta hcompact hlower hGamma hmono
  simpa [expectedOutputGap, expectedOutputGapRaw, outputGapRandomVariable] using hraw

/-- Internal selected-realization statement for Theorem 8.2(c), expected
reverse-monotone form, using the canonical selected SGS/SPS recursion instead of
caller-supplied process witnesses.  It is not the generic paper theorem because
it takes the additional selected-realization range proof. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_expected_selectedRealization_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma
        hgamma
        (innerBudgetNat T) law.sample))
    (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    sgsSelectedExpectedOutputGap S law x0 beta hbeta gamma
        hgamma
        (innerBudgetNat T) N
        xStar hxStar hindep ≤
      gamma N * beta N * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
            checkedQuotient 1 (1 - psWeightProduct spsP (innerBudgetNat T N))
              ((theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                hbeta hlower hGamma hmono).1 N).2.2 +
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            (Finset.range (innerBudgetNat T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              checkedQuotient
                ((S.mGrowth ^ 2 + S.sigmaSq) * gamma κ *
                  psWeightProduct spsP (innerBudgetNat T κ))
                (beta κ * Gamma κ * (1 - psWeightProduct spsP (innerBudgetNat T κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i)
                (theorem82ExpectedSummandDenom_ne_zero beta Gamma (innerBudgetNat T)
                    (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                      hbeta hlower hGamma hmono) κ ι i))) := by
  let states := sgsSelectedStates S x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample
  let inner := sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample
  have hrun_selected :
      IsGeneratedSGSProcess S x0 beta gamma (innerBudgetNat T) law.sample states inner := by
    simpa [states, inner, sgsSelectedStates, sgsSelectedInnerProcesses] using
      sgsSelectedRun_isGeneratedSGSProcess
        S x0 beta hbeta gamma hgamma (innerBudgetNat T) law.sample
  have hindep_generated :
      sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
    simpa [inner, sgsSelectedInnerProcesses, sgsSelectedOracleQuery,
      sgsGeneratedOracleQuery] using hindep
  have hbound :=
    SGSGenericConvergence_Theorem8_2_reverse_expected_sourceBoundary_feasibleBregman
      (S := S) (law := law) (x0 := x0) (xStar := xStar)
      (beta := beta) (gamma := gamma) (Gamma := Gamma)
      (T := T) (N := N) (states := states) (inner := inner)
      hrun_selected hindep_generated hxStar hcompact hlower hGamma hmono
  simpa [sgsSelectedExpectedOutputGap, states, inner,
    theorem82ReverseExpectedBound_checkedFormulaExtension] using hbound

/-- Private selected-realization extension corresponding to Theorem 8.2(c),
expected reverse-monotone bound.

This helper keeps the compact feasible-Bregman correction for the selected
recursion, but it is not a public source-boundary theorem because it assumes
the selector-only range condition `γ_k ∈ [0,1]`. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_expected_selectedRealizationExtension_feasibleBregman
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → InnerBudget)
    (N : PositiveTime)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsSelectedOracleQuery S x0 beta hbeta gamma hgamma
        (innerBudgetNat T) law.sample))
    (hmono : reverseMonotonicityCondition beta gamma Gamma (innerBudgetNat T)) :
    sgsSelectedExpectedOutputGap S law x0 beta hbeta gamma hgamma
        (innerBudgetNat T) N xStar hxStar hindep ≤
      gamma N * beta N * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact *
              checkedQuotient 1 (1 - psWeightProduct spsP (innerBudgetNat T N))
                ((theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                  hbeta hlower hGamma hmono).1 N).2.2 +
        Gamma N *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            (Finset.range (innerBudgetNat T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              checkedQuotient
                ((S.mGrowth ^ 2 + S.sigmaSq) * gamma κ *
                  psWeightProduct spsP (innerBudgetNat T κ))
                (beta κ * Gamma κ * (1 - psWeightProduct spsP (innerBudgetNat T κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP i)
                (theorem82ExpectedSummandDenom_ne_zero beta Gamma (innerBudgetNat T)
                    (theorem82DenominatorAdmissible_reverse_source_obligation S beta gamma Gamma T
                      hbeta hlower hGamma hmono) κ ι i))) := by
  exact
    SGSGenericConvergence_Theorem8_2_reverse_expected_selectedRealization_feasibleBregman
      S law x0 xStar beta gamma Gamma T N hbeta hgamma hxStar hcompact hlower
      hGamma hindep hmono

/-- Run-level formula-extension helper for Theorem 8.2(c), high-probability form
under the reverse monotonicity case, from the explicit Lemma 4.1 MDS interface.

This is intentionally a lower-level private bridge, not an arbitrary generated
run source theorem.  Lan Eq. (8.1.70) uses that
`<δ_{k,i-1}, x* - u_{k,i-1}>` is a martingale-difference sequence; for a
relation-form run that fact is supplied here as strict-past query measurability
plus the conditional mean-zero and conditional light-tail hypotheses.  The
canonical selected Algorithm 8.2 route should discharge these premises from
`sgsSelectedGeneratedQueriesStrictPastAdapted` and the one-coordinate SFO
bridges. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_highProbability_runFormulaExtension_from_mds [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hcompact : IsCompact S.X)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma T)
    (hgamma : gammaRangeCondition gamma)
    (hquery_strictPast_meas :
      ∀ κ i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
          (fun ω => sgsGeneratedOracleQuery S inner κ i ω))
    (hlinear_condExp_zero :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        law.P[ζ | sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] =ᵐ[law.P] 0)
    (hlinear_exp_sq_integrable :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P)
    (hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact * S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1) :
    law.P {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
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
                theorem82ProbabilityScale_formulaExtension S ⟨xStar, hxStar.1⟩ hcompact N beta gamma Gamma T} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  have hgenerated_mean :
      generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_var :
      generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    law.generated_variance (sgsGeneratedOracleQuery S inner) hindep
  have hgenerated_light :
      generatedSFOLightTail S law.P law.sample (sgsGeneratedOracleQuery S inner) :=
    sgsOracleLightTailAssumption_8_1_57.generated S law hlight
      (sgsGeneratedOracleQuery S inner) hindep
  classical
  let uStar : FeasiblePoint S := ⟨xStar, hxStar.1⟩
  let gap : Ω → ℝ := fun ω =>
    objectiveOn S (sgsGeneratedOutput S states N.1 ω) - objectiveOn S uStar
  let Bd : ℝ :=
    gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
        (1 - psWeightProduct spsP (T N))⁻¹ +
      Gamma N *
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
          (Finset.range (T κ)).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            (S.mGrowth ^ 2 + S.sigmaSq) * gamma κ * psWeightProduct spsP (T κ) /
              (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)))
  let linear : Ω → ℝ := fun ω =>
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
  let quadratic : Ω → ℝ := fun ω =>
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
                (dualNorm S δ ^ 2 / (beta κ * spsP ι))))
  let quadraticMean : ℝ :=
    Gamma N *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                (S.sigmaSq / (beta κ * spsP ι))))
  let linearScale : ℝ :=
    sigma S * Gamma N *
      Real.sqrt
        (2 * bregmanEnvelope_formulaExtension S uStar hcompact *
          (Finset.range N.1).sum (fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (gamma κ * psWeightProduct spsP (T κ) /
                (Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι * psWeightProduct spsP i)) ^ 2)))
  let quadraticScale : ℝ :=
    S.sigmaSq * Gamma N *
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        (Finset.range (T κ)).sum (fun i =>
          let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
          gamma κ * psWeightProduct spsP (T κ) /
            (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
              spsP ι ^ 2 * psWeightProduct spsP i)))
  have hTpos : ∀ k : PositiveTime, 0 < T k :=
    positive_inner_budget_of_reverseMonotonicity_beforeMaster beta gamma Gamma T hmono
  have hGamma_pos : ∀ k : PositiveTime, 0 < Gamma k :=
    outer_gamma_positive_of_weight_condition_and_reverse_denom_beforeMaster
      beta gamma Gamma T hgamma hGamma hmono
  have hraw :=
    generated_sgs_raw_master_inequality_8_1_69_formulaExtension
      (S := S) x0 beta gamma Gamma T law.sample N states inner hrun.1 uStar
      hbeta hgamma hlower hGamma hTpos hGamma_pos
  have hreverse_boundary :
      ∀ ω,
        let process : ℕ → SGSState S := fun n => states n ω;
        let c : ℕ → ℝ := fun n =>
          if hn : 1 ≤ n then
            gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
              (Gamma ⟨n, hn⟩ * (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
          else 0;
        let V : ℕ → ℝ := fun n => bregmanFormulaOnX S (process n).x uStar;
        Gamma N *
            Finset.sum (Finset.Icc 1 N.1) (fun t => c t * (V (t - 1) - V t)) ≤
          gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
            (1 - psWeightProduct spsP (T N))⁻¹ := by
    intro ω
    simpa [uStar] using
      reverse_bregman_telescope_envelope_scaled_formulaExtension_beforeSelected
        (S := S) beta gamma Gamma T N (fun n => states n ω)
        uStar hcompact hbeta hgamma hGamma hmono
  have hmaster_decomp :
      ∀ ω, gap ω ≤ Bd + linear ω + (quadratic ω - quadraticMean) := by
    intro ω
    let bregDrop : ℝ :=
      Gamma N *
        (let process : ℕ → SGSState S := fun n => states n ω;
         let c : ℕ → ℝ := fun n =>
          if hn : 1 ≤ n then
            gamma ⟨n, hn⟩ * beta ⟨n, hn⟩ /
              (Gamma ⟨n, hn⟩ *
                (1 - psWeightProduct spsP (T ⟨n, hn⟩)))
          else 0;
         let V : ℕ → ℝ := fun n => bregmanFormulaOnX S (process n).x uStar;
         Finset.sum (Finset.Icc 1 N.1) (fun t =>
          c t * (V (t - 1) - V t)))
    let stochasticOuter : ℝ :=
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
                  ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ)))
    let deterministicOuter : ℝ :=
      (Finset.range N.1).sum (fun k =>
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
        gamma κ * psWeightProduct spsP (T κ) /
          (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
            (Finset.range (T κ)).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                ((S.mGrowth ^ 2 + S.sigmaSq) / (beta κ * spsP ι))))
    have hrawω : gap ω ≤ bregDrop + Gamma N * stochasticOuter := by
      simpa [gap, bregDrop, stochasticOuter, uStar] using hraw ω
    have hrevω :
        bregDrop ≤
          gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
            (1 - psWeightProduct spsP (T N))⁻¹ := by
      simpa [bregDrop] using hreverse_boundary ω
    have hdeterministic_normalize :
        gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
              (1 - psWeightProduct spsP (T N))⁻¹ +
            Gamma N * deterministicOuter =
          Bd := by
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
        let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
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
    have hnormalize :
        gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
              (1 - psWeightProduct spsP (T N))⁻¹ +
            Gamma N * stochasticOuter =
          Bd + linear ω + (quadratic ω - quadraticMean) := by
      rw [← hdeterministic_normalize]
      simp [linear, quadratic, quadraticMean, deterministicOuter, stochasticOuter]
      have hsplit :=
        (nested_weighted_master_bracket_decomp
          (s := Finset.range N.1)
          (t := fun k => Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
          (G := Gamma N)
          (C := fun k =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            gamma κ * psWeightProduct spsP (T κ) /
              (Gamma κ * (1 - psWeightProduct spsP (T κ))))
          (I := fun k i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            (psWeightProduct spsP i)⁻¹ * (spsP ι)⁻¹)
          (D := fun k i =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            beta κ * spsP ι)
          (M2 := fun _ _ => S.mGrowth ^ 2)
          (Q := fun k i =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let δinner := inner κ;
            let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
            dualNorm S δ ^ 2)
          (Sigma := fun _ _ => S.sigmaSq)
          (L := fun k i =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
            let δinner := inner κ;
            let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
            ⟪δ, uStar.1 - (δinner i ω).u.1⟫_ℝ))
      set_option maxHeartbeats 4000000 in
      rw [hsplit]
      ring
    have hupper :
        gap ω ≤
          gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
              (1 - psWeightProduct spsP (T N))⁻¹ +
            Gamma N * stochasticOuter := by
      linarith
    exact le_trans hupper (le_of_eq hnormalize)
  let target : Set Ω :=
    {ω | gap ω > Bd + lambda * (linearScale + quadraticScale)}
  let linearBad : Set Ω := {ω | linear ω > lambda * linearScale}
  let quadraticBad : Set Ω := {ω | quadratic ω > quadraticMean + lambda * quadraticScale}
  have hprob_scale :
      theorem82ProbabilityScale_formulaExtension S uStar hcompact N beta gamma Gamma T =
        linearScale + quadraticScale := by
    simp [linearScale, quadraticScale, theorem82ProbabilityScale_formulaExtension,
      genericProbabilityScale_formulaExtension]
  have htarget :
        {ω | objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
            objectiveOn S uStar >
              gamma N * beta N * bregmanEnvelope_formulaExtension S uStar hcompact *
                  (1 - psWeightProduct spsP (T N))⁻¹ +
                Gamma N *
                  (Finset.range N.1).sum (fun k =>
                    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                    (Finset.range (T κ)).sum (fun i =>
                      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                      (S.mGrowth ^ 2 + S.sigmaSq) * gamma κ *
                        psWeightProduct spsP (T κ) /
                        (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                          spsP ι ^ 2 * psWeightProduct spsP i))) +
                lambda *
                  theorem82ProbabilityScale_formulaExtension S uStar hcompact N beta gamma Gamma T}
        = target := by
    ext ω
    simp [target, gap, Bd, hprob_scale]
  have hsubset : target ⊆ linearBad ∪ quadraticBad := by
    exact
      theorem82_highProbability_master_strict_event_subset_scalar
        gap linear quadratic Bd quadraticMean linearScale quadraticScale lambda
        hmaster_decomp
  have htails :
      law.P linearBad ≤ ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) ∧
        law.P quadraticBad ≤ ENNReal.ofReal (Real.exp (-lambda)) := by
    have hlinear_tail :
        law.P linearBad ≤ ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
      -- Eq. (8.1.70): martingale large-deviation bound for the generated
      -- linear oracle-noise sum.  The route-local event has now been isolated.
      have hlinear_zero_of_integrable :
          (∀ κ i (hquery : ∀ ω, sgsGeneratedOracleQuery S inner κ i ω ∈ S.X),
            Integrable
              (fun ω =>
                ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω),
                  uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ)
              law.P) →
            ∀ κ i,
              (∫ ω,
                ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω),
                  uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ ∂law.P) = 0 := by
        intro hinner_int
        simpa [uStar] using
          sgsGeneratedOracleQuery_target_noise_inner_integral_zero_of_integrable
            (S := S) (law := law) inner uStar hindep hinner_int
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
                  (uStar.1 - sgsGeneratedOracleQuery S inner κ i ω) ^ 2) law.P := by
        letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
        have hgenerated_avg_sq_from_bregman_window :
            ∀ κ m,
              (∀ i, i < m + 1 →
                Integrable
                  (fun ω =>
                    bregmanFormulaOnX S
                      (⟨sgsGeneratedOracleQuery S inner κ i ω,
                        hquery_mem κ i ω⟩ : FeasiblePoint S)
                      uStar)
                  law.P) →
              Integrable
                (fun ω =>
                  S.primalNorm
                    (uStar.1 - (inner κ m ω).avg.1) ^ 2) law.P := by
          intro κ m hwindow
          simpa [uStar] using
            generated_sgs_inner_avg_sq_integrable_from_bregman_window
              (S := S) law uStar x0 beta gamma T states inner
              hrun hquery_mem hquery_meas κ m hwindow
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
                uStar)
            law.P
        let Xbar : ℕ → Prop := fun n =>
          Integrable
            (fun ω =>
              S.primalNorm (uStar.1 - (states n ω).xbar.1) ^ 2)
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
                                bregmanFormulaOnX S x0 uStar)
                              law.P :=
                          integrable_const _
                        have hcongr :
                            (fun ω =>
                              bregmanFormulaOnX S
                                (⟨sgsGeneratedOracleQuery S inner
                                    (⟨1, by omega⟩ : PositiveTime) 0 ω,
                                  hquery_mem (⟨1, by omega⟩ : PositiveTime) 0 ω⟩ :
                                  FeasiblePoint S)
                                uStar) =
                            (fun _ : Ω =>
                              bregmanFormulaOnX S x0 uStar) := by
                          funext ω
                          have hproc := hinner_proc (⟨1, by omega⟩ : PositiveTime)
                          have hinit_inner := hproc.2.1 ω
                          apply congrArg
                            (fun y : FeasiblePoint S =>
                              bregmanFormulaOnX S y uStar)
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
                                uStar) =
                            (fun ω =>
                              bregmanFormulaOnX S
                                (⟨sgsGeneratedOracleQuery S inner
                                    (predTime κcur hκcur_two)
                                    (T (predTime κcur hκcur_two)) ω,
                                  hquery_mem (predTime κcur hκcur_two)
                                    (T (predTime κcur hκcur_two)) ω⟩ : FeasiblePoint S)
                                uStar) := by
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
                    (S := S) law uStar x0 beta gamma T states inner
                    hrun hbeta hgamma hquery_mem hquery_meas hgenerated_var κ j
                    (by simpa [Xbar] using houter_xbar_sq) hprev_window
          have hXbar_current : Xbar n := by
            cases n with
            | zero =>
                refine (integrable_const
                  (c := S.primalNorm (uStar.1 - x0.1) ^ 2)).congr ?_
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
                          (uStar.1 - (inner κcur (T κcur) ω).avg.1) ^ 2)
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
                          (uStar.1 -
                            ((1 - gamma κcur) • (states m ω).xbar.1 +
                              gamma κcur • (inner κcur (T κcur) ω).avg.1)) ^ 2)
                      law.P :=
                  primalNorm_sq_integrable_affine_update
                    (S := S) law.P uStar
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
            (S := S) law.P uStar
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
                  uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P := by
        intro κ i
        let queryFP : Ω → FeasiblePoint S :=
          fun ω => ⟨sgsGeneratedOracleQuery S inner κ i ω, hquery_mem κ i ω⟩
        have hpair_meas : Measurable (fun ω => (queryFP ω, law.sample κ i ω)) :=
          (hquery_meas κ i).prod (law.sample_measurable κ i)
        have hleft_inner_aemeas :
            AEStronglyMeasurable
              (fun ω =>
                ⟪uStar.1 - sgsGeneratedOracleQuery S inner κ i ω,
                  oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω)⟫_ℝ) law.P := by
          have hkernel :=
            oracle_residual_target_inner_measurable_of_residual_measurable
              (S := S) (x := uStar) law.oracle_residual_measurable
          simpa [queryFP] using (hkernel.comp hpair_meas).aestronglyMeasurable
        have hinner_aemeas :
            AEStronglyMeasurable
              (fun ω =>
                ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω),
                  uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ) law.P :=
          hleft_inner_aemeas.congr
            (Filter.Eventually.of_forall (fun ω => by
              simpa using
                (real_inner_comm
                  (uStar.1 - sgsGeneratedOracleQuery S inner κ i ω)
                  (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                    (law.sample κ i ω))).symm))
        exact
          generated_target_inner_integrable_of_primal_displacement_l2
            (S := S) law.P law.sample (sgsGeneratedOracleQuery S inner)
            uStar κ i (hdual_sq_int κ i) (hquery_disp_sq_int κ i) hinner_aemeas
      have hlinear_zero :
          ∀ κ i,
            (∫ ω,
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω),
                uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ ∂law.P) = 0 :=
        hlinear_zero_of_integrable (fun κ i _hquery => hlinear_int κ i)
      have hadapted_query :
          ∀ κ i,
            Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i]
              (fun ω => sgsGeneratedOracleQuery S inner κ i ω) := by
        exact hquery_strictPast_meas
      have hlinear_zero_lightScale :
          ∀ κ i,
            let ζ : Ω → ℝ := fun ω =>
              ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                  (law.sample κ i ω),
                uStar.1 - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
            let lightScale : ℝ :=
              2 * bregmanEnvelope_formulaExtension S uStar hcompact * S.sigmaSq
            lightScale = 0 → ζ =ᵐ[law.P] 0 := by
        exact
          theorem82_linear_zero_of_zero_lightScale
            (S := S) (law := law) (uStar := uStar) (inner := inner)
            hcompact hquery_mem hgenerated_light
      have hlinear_tail_strict :
          law.P {ω | linear ω > lambda * linearScale} ≤
            ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
        simpa [linear, linearScale, uStar, sgsGeneratedOracleQuery] using
          theorem82_linear_tail_martingale_large_deviation_formulaExtension
            (S := S) (law := law) (uStar := uStar) (beta := beta) (gamma := gamma)
            (Gamma := Gamma) (T := T) (N := N) (lambda := lambda) (inner := inner)
            hlambda hbeta hgamma hGamma_pos hTpos hcompact hlinear_int
            hadapted_query hlinear_condExp_zero hlinear_exp_sq_integrable
            hlinear_condExp_light hlinear_zero_lightScale
      simpa [linearBad] using hlinear_tail_strict
    have hquadratic_tail :
        law.P quadraticBad ≤ ENNReal.ofReal (Real.exp (-lambda)) := by
      -- Eq. (8.1.71): Markov/light-tail bound for the strict centered quadratic
      -- oracle-noise event.  The strict inequality is source-critical: the
      -- non-strict event is false in the deterministic zero-variance case.
      rcases hgenerated_light with ⟨_hquery_light, hlight_pos | hlight_det⟩
      · rcases hlight_pos with ⟨hsigma_pos, hlight_moment⟩
        have hlight_exp_integrable :
            ∀ κ i,
              Integrable
                (fun ω =>
                  Real.exp (lightTailExponent S
                    (dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2))) law.P :=
          fun κ i => (hlight_moment κ i).1
        have hlight_int :
            ∀ κ i,
              (∫ ω,
                Real.exp (lightTailExponent S
                  (dualNorm S
                    (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                      (law.sample κ i ω)) ^ 2)) ∂law.P) ≤ Real.exp 1 :=
          fun κ i => (hlight_moment κ i).2
        have hquadMean_eq_scale : quadraticMean = quadraticScale := by
          dsimp [quadraticMean, quadraticScale]
          exact
            nested_quadratic_mean_scale_algebra_coeff
              (s := Finset.range N.1)
              (t := fun k =>
                Finset.range
                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
              (G := Gamma N) (sigma := S.sigmaSq)
              (C := fun k =>
                gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                  psWeightProduct spsP
                    (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
              (D := fun k =>
                Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))
              (E := fun k =>
                1 - psWeightProduct spsP
                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
              (B := fun k i =>
                beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))
              (sp := fun _ i =>
                spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime))
              (prevP := fun _ i => psWeightProduct spsP i)
        have hquadScale_pos : 0 < quadraticScale := by
          dsimp [quadraticScale]
          let innerTerm : ℕ → ℕ → ℝ := fun k i =>
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            gamma κ * psWeightProduct spsP (T κ) /
              (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                spsP ι ^ 2 * psWeightProduct spsP i)
          let outerTerm : ℕ → ℝ := fun k =>
            (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
              (innerTerm k)
          have hP_nonneg : ∀ n : ℕ, 0 ≤ psWeightProduct spsP n := by
            intro n
            rw [psWeightProduct_spsP_eq n]
            positivity
          have hP_pos : ∀ n : ℕ, 0 < psWeightProduct spsP n := by
            intro n
            rw [psWeightProduct_spsP_eq n]
            positivity
          have hsps_pos : ∀ i : PositiveTime, 0 < spsP i := by
            intro i
            unfold spsP
            have hi : 0 < (i.1 : ℝ) := by exact_mod_cast i.2
            nlinarith
          have hinner_nonneg :
              ∀ k i, 0 ≤ innerTerm k i := by
            intro k i
            dsimp [innerTerm]
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            have hnum_nonneg : 0 ≤ gamma κ * psWeightProduct spsP (T κ) :=
              mul_nonneg (gammaRangeCondition_nonnegative hgamma κ) (hP_nonneg (T κ))
            have hden_pos :
                0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i := by
              exact
                mul_pos
                  (mul_pos
                    (mul_pos
                      (mul_pos (hbeta κ) (hGamma_pos κ))
                      (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                    (sq_pos_of_pos (hsps_pos ι)))
                  (hP_pos i)
            exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
          have houter_nonneg : ∀ k ∈ Finset.range N.1, 0 ≤ outerTerm k := by
            intro k _hk
            dsimp [outerTerm]
            exact Finset.sum_nonneg (fun i _hi => hinner_nonneg k i)
          have houter_zero_pos : 0 < outerTerm 0 := by
            dsimp [outerTerm]
            let κ : PositiveTime := ⟨0 + 1, Nat.succ_pos 0⟩
            let ι : PositiveTime := ⟨0 + 1, Nat.succ_pos 0⟩
            have hzero_mem : 0 ∈ Finset.range (T κ) := by
              simpa using hTpos κ
            have hgamma_one : gamma κ = 1 := by
              simpa [κ, oneTime] using hlower.1
            have hnum_pos : 0 < gamma κ * psWeightProduct spsP (T κ) := by
              rw [hgamma_one]
              simpa using hP_pos (T κ)
            have hden_pos :
                0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP 0 := by
              exact
                mul_pos
                  (mul_pos
                    (mul_pos
                      (mul_pos (hbeta κ) (hGamma_pos κ))
                      (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                    (sq_pos_of_pos (hsps_pos ι)))
                  (hP_pos 0)
            have hzero_pos : 0 < innerTerm 0 0 := by
              dsimp [innerTerm, κ, ι]
              exact div_pos hnum_pos hden_pos
            have hle :
                innerTerm 0 0 ≤ (Finset.range (T κ)).sum (innerTerm 0) :=
              Finset.single_le_sum (fun i _hi => hinner_nonneg 0 i) hzero_mem
            exact lt_of_lt_of_le hzero_pos hle
          have hsum_pos :
              0 < (Finset.range N.1).sum outerTerm := by
            have hzero_mem : 0 ∈ Finset.range N.1 := by
              simpa using N.2
            have hle : outerTerm 0 ≤ (Finset.range N.1).sum outerTerm :=
              Finset.single_le_sum (fun k hk => houter_nonneg k hk) hzero_mem
            exact lt_of_lt_of_le houter_zero_pos hle
          exact mul_pos (mul_pos hsigma_pos (hGamma_pos N)) hsum_pos
        have hexp_moment :
            Integrable (fun ω => Real.exp (quadratic ω / quadraticScale)) law.P ∧
              (∫ ω, Real.exp (quadratic ω / quadraticScale) ∂law.P) ≤ Real.exp 1 := by
          let idx : Finset (Σ _k : ℕ, ℕ) :=
            (Finset.range N.1).sigma (fun k =>
              Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
          let q : (Σ _k : ℕ, ℕ) → ℝ := fun a =>
            let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
            let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
            (S.sigmaSq * Gamma N *
              (gamma κ * psWeightProduct spsP (T κ) /
                (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                  spsP ι ^ 2 * psWeightProduct spsP a.2))) / quadraticScale
          let Y : (Σ _k : ℕ, ℕ) → Ω → ℝ := fun a ω =>
            let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
            lightTailExponent S
              (dualNorm S
                (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ a.2 ω)
                  (law.sample κ a.2 ω)) ^ 2)
          refine
            finite_exp_moment_of_pointwise_le_weighted_sum
              (μ := law.P) idx q Y (fun ω => quadratic ω / quadraticScale) ?_
              ?_ ?_ ?_ ?_ ?_
          · have hquad_aesm : AEStronglyMeasurable quadratic law.P := by
              dsimp [quadratic]
              refine
                (Finset.aestronglyMeasurable_fun_sum (μ := law.P) (Finset.range N.1)
                  (fun k _hk => ?_)).const_mul (Gamma N)
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
              refine
                (Finset.aestronglyMeasurable_fun_sum (μ := law.P) (Finset.range (T κ))
                  (fun i _hi => ?_)).const_mul
                    (gamma κ * psWeightProduct spsP (T κ) /
                      (Gamma κ * (1 - psWeightProduct spsP (T κ))))
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              have hdual_int :
                  Integrable
                    (fun ω =>
                      dualNorm S
                        (oracleNoiseAt S
                          (sgsGeneratedOracleQuery S inner κ i ω)
                          (law.sample κ i ω)) ^ 2) law.P := by
                simpa using
                  generatedSFOVariance_integrable_obligation
                    S law.P law.sample (sgsGeneratedOracleQuery S inner)
                    hgenerated_var κ i
              have hterm_int :
                  Integrable
                    (fun ω =>
                      (spsP ι * psWeightProduct spsP i)⁻¹ *
                        (dualNorm S
                          (oracleNoiseAt S
                            (sgsGeneratedOracleQuery S inner κ i ω)
                            (law.sample κ i ω)) ^ 2 / (beta κ * spsP ι))) law.P := by
                simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                  hdual_int.const_mul
                    (((spsP ι * psWeightProduct spsP i)⁻¹) *
                      (beta κ * spsP ι)⁻¹)
              exact hterm_int.aestronglyMeasurable
            have hquad_aemeas :
                AEMeasurable (fun ω => quadratic ω / quadraticScale) law.P :=
              hquad_aesm.aemeasurable.div_const quadraticScale
            exact
              (Real.measurable_exp.comp_aemeasurable
                hquad_aemeas).aestronglyMeasurable
          · intro a _ha
            rcases a with ⟨k, i⟩
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            simpa [Y, κ] using hlight_exp_integrable κ i
          · intro a _ha
            rcases a with ⟨k, i⟩
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            simpa [Y, κ] using hlight_int κ i
          · intro a ha
            rcases a with ⟨k, i⟩
            dsimp [q]
            let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
            have hP_nonneg : ∀ n : ℕ, 0 ≤ psWeightProduct spsP n := by
              intro n
              rw [psWeightProduct_spsP_eq n]
              positivity
            have hP_pos : ∀ n : ℕ, 0 < psWeightProduct spsP n := by
              intro n
              rw [psWeightProduct_spsP_eq n]
              positivity
            have hsps_pos : 0 < spsP ι := by
              unfold spsP
              have hi : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
              nlinarith
            have hden_pos :
                0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i := by
              exact
                mul_pos
                  (mul_pos
                    (mul_pos
                      (mul_pos (hbeta κ) (hGamma_pos κ))
                      (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                    (sq_pos_of_pos hsps_pos))
                  (hP_pos i)
            have hinner_nonneg :
                0 ≤ gamma κ * psWeightProduct spsP (T κ) /
                  (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                    spsP ι ^ 2 * psWeightProduct spsP i) := by
              exact div_nonneg
                (mul_nonneg (gammaRangeCondition_nonnegative hgamma κ)
                  (hP_nonneg (T κ)))
                (le_of_lt hden_pos)
            exact div_nonneg
              (mul_nonneg (mul_nonneg (le_of_lt hsigma_pos) (le_of_lt (hGamma_pos N)))
                hinner_nonneg)
              (le_of_lt hquadScale_pos)
          · have hscale_ne : quadraticScale ≠ 0 := ne_of_gt hquadScale_pos
            have hraw_sum :
                idx.sum (fun a =>
                  S.sigmaSq * Gamma N *
                    (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                     let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                     gamma κ * psWeightProduct spsP (T κ) /
                      (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                        spsP ι ^ 2 * psWeightProduct spsP a.2))) =
                  quadraticScale := by
              dsimp [idx, quadraticScale]
              rw [Finset.sum_sigma]
              calc
                (Finset.range N.1).sum (fun k =>
                    (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                      (fun i =>
                        S.sigmaSq * Gamma N *
                          (gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                            psWeightProduct spsP
                              (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                              (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                (1 - psWeightProduct spsP
                                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                psWeightProduct spsP i)))) =
                  (Finset.range N.1).sum (fun k =>
                    S.sigmaSq * Gamma N *
                      (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                        (fun i =>
                          gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                            psWeightProduct spsP
                              (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                              (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                (1 - psWeightProduct spsP
                                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                psWeightProduct spsP i))) := by
                    refine Finset.sum_congr rfl ?_
                    intro k _hk
                    rw [Finset.mul_sum]
                _ =
                  S.sigmaSq * Gamma N *
                    (Finset.range N.1).sum (fun k =>
                      (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                        (fun i =>
                          gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                            psWeightProduct spsP
                              (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                              (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                (1 - psWeightProduct spsP
                                  (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                psWeightProduct spsP i))) := by
                    rw [Finset.mul_sum]
            calc
              idx.sum q =
                  idx.sum (fun a =>
                    (S.sigmaSq * Gamma N *
                      (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                       let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                       gamma κ * psWeightProduct spsP (T κ) /
                        (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                          spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                      quadraticScale) := by
                    rfl
              _ =
                  idx.sum (fun a =>
                    S.sigmaSq * Gamma N *
                      (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                       let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                       gamma κ * psWeightProduct spsP (T κ) /
                        (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                          spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                    quadraticScale := by
                    rw [Finset.sum_div]
              _ = quadraticScale / quadraticScale := by
                    rw [hraw_sum]
              _ = 1 := div_self hscale_ne
          · apply Filter.Eventually.of_forall
            intro ω
            have hq_nonneg_local : ∀ a ∈ idx, 0 ≤ q a := by
              intro a ha
              rcases a with ⟨k, i⟩
              dsimp [q]
              let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
              have hP_nonneg : ∀ n : ℕ, 0 ≤ psWeightProduct spsP n := by
                intro n
                rw [psWeightProduct_spsP_eq n]
                positivity
              have hP_pos : ∀ n : ℕ, 0 < psWeightProduct spsP n := by
                intro n
                rw [psWeightProduct_spsP_eq n]
                positivity
              have hsps_pos : 0 < spsP ι := by
                unfold spsP
                have hi : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
                nlinarith
              have hden_pos :
                  0 < beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                        spsP ι ^ 2 * psWeightProduct spsP i := by
                exact
                  mul_pos
                    (mul_pos
                      (mul_pos
                        (mul_pos (hbeta κ) (hGamma_pos κ))
                        (one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)))
                      (sq_pos_of_pos hsps_pos))
                    (hP_pos i)
              have hinner_nonneg :
                  0 ≤ gamma κ * psWeightProduct spsP (T κ) /
                    (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                      spsP ι ^ 2 * psWeightProduct spsP i) := by
                exact div_nonneg
                  (mul_nonneg (gammaRangeCondition_nonnegative hgamma κ)
                    (hP_nonneg (T κ)))
                  (le_of_lt hden_pos)
              exact div_nonneg
                (mul_nonneg (mul_nonneg (le_of_lt hsigma_pos) (le_of_lt (hGamma_pos N)))
                  hinner_nonneg)
                (le_of_lt hquadScale_pos)
            have hq_sum_local : idx.sum q = 1 := by
              have hscale_ne : quadraticScale ≠ 0 := ne_of_gt hquadScale_pos
              have hraw_sum :
                  idx.sum (fun a =>
                    S.sigmaSq * Gamma N *
                      (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                       let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                       gamma κ * psWeightProduct spsP (T κ) /
                        (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                          spsP ι ^ 2 * psWeightProduct spsP a.2))) =
                    quadraticScale := by
                dsimp [idx, quadraticScale]
                rw [Finset.sum_sigma]
                calc
                  (Finset.range N.1).sum (fun k =>
                      (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                        (fun i =>
                          S.sigmaSq * Gamma N *
                            (gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              psWeightProduct spsP
                                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                                (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                  Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                  (1 - psWeightProduct spsP
                                    (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                  spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                  psWeightProduct spsP i)))) =
                    (Finset.range N.1).sum (fun k =>
                      S.sigmaSq * Gamma N *
                        (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                          (fun i =>
                            gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              psWeightProduct spsP
                                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                                (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                  Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                  (1 - psWeightProduct spsP
                                    (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                  spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                  psWeightProduct spsP i))) := by
                      refine Finset.sum_congr rfl ?_
                      intro k _hk
                      rw [Finset.mul_sum]
                  _ =
                    S.sigmaSq * Gamma N *
                      (Finset.range N.1).sum (fun k =>
                        (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum
                          (fun i =>
                            gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                              psWeightProduct spsP
                                (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)) /
                                (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                  Gamma (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) *
                                  (1 - psWeightProduct spsP
                                    (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) *
                                  spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) ^ 2 *
                                  psWeightProduct spsP i))) := by
                      rw [Finset.mul_sum]
              calc
                idx.sum q =
                    idx.sum (fun a =>
                      (S.sigmaSq * Gamma N *
                        (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                         let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                         gamma κ * psWeightProduct spsP (T κ) /
                          (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                            spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                        quadraticScale) := by
                      rfl
                _ =
                    idx.sum (fun a =>
                      S.sigmaSq * Gamma N *
                        (let κ : PositiveTime := ⟨a.1 + 1, Nat.succ_pos a.1⟩
                         let ι : PositiveTime := ⟨a.2 + 1, Nat.succ_pos a.2⟩
                         gamma κ * psWeightProduct spsP (T κ) /
                          (beta κ * Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                            spsP ι ^ 2 * psWeightProduct spsP a.2))) /
                      quadraticScale := by
                      rw [Finset.sum_div]
                _ = quadraticScale / quadraticScale := by
                      rw [hraw_sum]
                _ = 1 := div_self hscale_ne
            have hweighted :
                quadratic ω / quadraticScale =
                  idx.sum (fun a => q a * Y a ω) := by
              have hsigma_ne : S.sigmaSq ≠ 0 := ne_of_gt hsigma_pos
              have hraw :=
                nested_quadratic_normalized_lightTail_algebra_outer
                  (s := Finset.range N.1)
                  (t := fun k =>
                    Finset.range
                      (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))
                  (G := Gamma N) (sigma := S.sigmaSq) (scale := quadraticScale)
                  (C := fun k =>
                    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                    gamma κ * psWeightProduct spsP (T κ) /
                      (Gamma κ * (1 - psWeightProduct spsP (T κ))))
                  (B := fun k _i =>
                    beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))
                  (sp := fun _k i =>
                    spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime))
                  (prevP := fun _k i => psWeightProduct spsP i)
                  (Z := fun k i =>
                    let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                    dualNorm S
                      (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                        (law.sample κ i ω)) ^ 2)
                  hsigma_ne
              calc
                quadratic ω / quadraticScale =
                  (Gamma N *
                    (Finset.range N.1).sum (fun k =>
                      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                      gamma κ * psWeightProduct spsP (T κ) /
                        (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                          (Finset.range (T κ)).sum (fun i =>
                            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                            (spsP ι * psWeightProduct spsP i)⁻¹ *
                              (dualNorm S
                                (oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
                                  (law.sample κ i ω)) ^ 2 /
                                (beta κ * spsP ι))))) / quadraticScale := by
                      rfl
                _ =
                  ((Finset.range N.1).sigma (fun k =>
                    Finset.range
                      (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)))).sum (fun x =>
                        ((S.sigmaSq * Gamma N *
                            ((let κ : PositiveTime := ⟨x.1 + 1, Nat.succ_pos x.1⟩;
                              gamma κ * psWeightProduct spsP (T κ) /
                                (Gamma κ * (1 - psWeightProduct spsP (T κ)))) /
                              (beta (⟨x.1 + 1, Nat.succ_pos x.1⟩ : PositiveTime) *
                                spsP (⟨x.2 + 1, Nat.succ_pos x.2⟩ : PositiveTime) ^ 2 *
                                psWeightProduct spsP x.2))) / quadraticScale) *
                          (dualNorm S
                            (oracleNoiseAt S
                              (sgsGeneratedOracleQuery S inner
                                (⟨x.1 + 1, Nat.succ_pos x.1⟩ : PositiveTime) x.2 ω)
                              (law.sample
                                (⟨x.1 + 1, Nat.succ_pos x.1⟩ : PositiveTime) x.2 ω)) ^ 2 /
                            S.sigmaSq)) := by
                      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
                _ = idx.sum (fun a => q a * Y a ω) := by
                      dsimp [idx, q, Y, lightTailExponent]
                      refine Finset.sum_congr rfl ?_
                      intro a ha
                      rcases a with ⟨k, i⟩
                      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
                      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩
                      have hGamma_ne : Gamma κ ≠ 0 := ne_of_gt (hGamma_pos κ)
                      have hbeta_ne : beta κ ≠ 0 := ne_of_gt (hbeta κ)
                      have hsps_pos : 0 < spsP ι := by
                        unfold spsP
                        have hi : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
                        nlinarith
                      have hsps_ne : spsP ι ≠ 0 := ne_of_gt hsps_pos
                      have hPprev_pos : 0 < psWeightProduct spsP i := by
                        rw [psWeightProduct_spsP_eq i]
                        positivity
                      have hPprev_ne : psWeightProduct spsP i ≠ 0 := ne_of_gt hPprev_pos
                      have hPden_pos :
                          0 < 1 - psWeightProduct spsP (T κ) :=
                        one_sub_psWeightProduct_spsP_pos_of_pos (hTpos κ)
                      have hPden_ne : 1 - psWeightProduct spsP (T κ) ≠ 0 :=
                        ne_of_gt hPden_pos
                      have hscale_ne : quadraticScale ≠ 0 := ne_of_gt hquadScale_pos
                      have hbig_ne :
                          -(psWeightProduct spsP (T κ) * Gamma κ * beta κ *
                              spsP ι ^ 2 * psWeightProduct spsP i) +
                              Gamma κ * beta κ * spsP ι ^ 2 *
                                psWeightProduct spsP i ≠ 0 := by
                        have hprod_pos :
                            0 < Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                                beta κ * spsP ι ^ 2 * psWeightProduct spsP i := by
                          exact
                            mul_pos
                              (mul_pos
                                (mul_pos
                                  (mul_pos (hGamma_pos κ) hPden_pos)
                                  (hbeta κ))
                                (sq_pos_of_pos hsps_pos))
                              hPprev_pos
                        have heq :
                            -(psWeightProduct spsP (T κ) * Gamma κ * beta κ *
                                spsP ι ^ 2 * psWeightProduct spsP i) +
                                Gamma κ * beta κ * spsP ι ^ 2 *
                                  psWeightProduct spsP i =
                              Gamma κ * (1 - psWeightProduct spsP (T κ)) *
                                beta κ * spsP ι ^ 2 * psWeightProduct spsP i := by
                          ring
                        rw [heq]
                        exact ne_of_gt hprod_pos
                      dsimp [κ, ι]
                      field_simp [hGamma_ne, hbeta_ne, hsps_ne, hPprev_ne,
                        hPden_ne, hscale_ne, hsigma_ne, hbig_ne]
                      try ring
            exact
              finite_exp_jensen_of_weighted_sum idx q (fun a => Y a ω)
                (quadratic ω / quadraticScale) hq_nonneg_local hq_sum_local
                hweighted
        have hsubset_exp :
            quadraticBad ⊆ {ω | quadratic ω / quadraticScale > 1 + lambda} := by
          intro ω hω
          have hbad :
              quadratic ω > quadraticScale + lambda * quadraticScale := by
            simpa [quadraticBad, hquadMean_eq_scale] using hω
          have hfactor :
              quadraticScale + lambda * quadraticScale =
                (1 + lambda) * quadraticScale := by ring
          have hbad' : quadratic ω > (1 + lambda) * quadraticScale := by
            simpa [hfactor] using hbad
          exact (lt_div_iff₀ hquadScale_pos).2 hbad'
        have htail :=
          strict_markov_exp_tail_from_exp_moment
            (μ := law.P) (f := fun ω => quadratic ω / quadraticScale)
            lambda hexp_moment.1 hexp_moment.2 hlambda
        exact le_trans (measure_mono hsubset_exp) htail
      · rcases hlight_det with ⟨hsigma_zero, hnoise_zero⟩
        have hquadMean_zero : quadraticMean = 0 := by
          simp [quadraticMean, hsigma_zero]
        have hquadScale_zero : quadraticScale = 0 := by
          simp [quadraticScale, hsigma_zero]
        have hquadratic_zero_ae : ∀ᵐ ω ∂law.P, quadratic ω = 0 := by
          have houter :
              ∀ᵐ ω ∂law.P,
                ∀ k ∈ Finset.range N.1,
                  ∀ i ∈ Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)),
                    dualNorm S
                      (oracleNoiseAt S
                        ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                        (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 := by
            refine Finset.induction_on (Finset.range N.1) ?_ ?_
            · simp
            · intro k ks hk_not hks
              have hk_ae :
                  ∀ᵐ ω ∂law.P,
                    ∀ i ∈ Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime)),
                      dualNorm S
                        (oracleNoiseAt S
                          ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                          (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 := by
                refine Finset.induction_on
                  (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))) ?_ ?_
                · simp
                · intro i is hi_not his
                  have hki :
                      ∀ᵐ ω ∂law.P,
                        dualNorm S
                          (oracleNoiseAt S
                            ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                            (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 := by
                    simpa [sgsGeneratedOracleQuery] using
                      hnoise_zero (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i
                  filter_upwards [hki, his] with ω hkiω hisω j hj
                  simp at hj
                  rcases hj with hj | hj
                  · subst hj
                    exact hkiω
                  · exact hisω j hj
              filter_upwards [hk_ae, hks] with ω hkω hksω j hj
              simp at hj
              rcases hj with hj | hj
              · subst hj
                exact hkω
              · exact hksω j hj
          filter_upwards [houter] with ω hω
          have hsum_zero :
              (Finset.range N.1).sum (fun k =>
                let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩;
                let δinner := inner κ;
                gamma κ * psWeightProduct spsP (T κ) /
                  (Gamma κ * (1 - psWeightProduct spsP (T κ))) *
                    (Finset.range (T κ)).sum (fun i =>
                      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                      let δ := oracleNoiseAt S ((δinner i ω).u.1) (law.sample κ i ω);
                      (spsP ι * psWeightProduct spsP i)⁻¹ *
                        (dualNorm S δ ^ 2 / (beta κ * spsP ι)))) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro k hk
            have hinner_zero :
                (Finset.range (T (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime))).sum (fun i =>
                  let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                  let δ := oracleNoiseAt S
                    ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                    (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω);
                  (spsP ι * psWeightProduct spsP i)⁻¹ *
                    (dualNorm S δ ^ 2 /
                      (beta (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) * spsP ι))) = 0 := by
              refine Finset.sum_eq_zero ?_
              intro i hi
              have hδ :
                  dualNorm S
                    (oracleNoiseAt S
                      ((inner (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω).u.1)
                      (law.sample (⟨k + 1, Nat.succ_pos k⟩ : PositiveTime) i ω)) = 0 :=
                hω k hk i hi
              simp [hδ]
            dsimp only
            rw [hinner_zero]
            ring
          dsimp only [quadratic]
          rw [hsum_zero, mul_zero]
        have hnot_bad : ∀ᵐ ω ∂law.P, ω ∉ quadraticBad := by
          filter_upwards [hquadratic_zero_ae] with ω hquad
          simp [quadraticBad, hquad, hquadMean_zero, hquadScale_zero]
        have hbad_zero : law.P quadraticBad = 0 := by
          simpa using
            ((MeasureTheory.ae_iff (μ := law.P)
              (p := fun ω => ω ∉ quadraticBad)).mp hnot_bad)
        rw [hbad_zero]
        exact zero_le _
    exact ⟨hlinear_tail, hquadratic_tail⟩
  have hsource_union :
      law.P target ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) :=
    theorem82_highProbability_union_bound_source_formulaExtension law.P target linearBad
      quadraticBad lambda hsubset htails.1 htails.2
  have hchecked_source_union :
      law.P target ≤
        ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) :=
    theorem82_final_probability_constant_source_boundary_formulaExtension
      law.P target lambda hsource_union
  rw [htarget]
  exact hchecked_source_union

/-- Extract the raw Eq. (8.1.58) objective comparison from one source-domain
SPS transition.

Aligns with Lan Proposition 8.3, proof step applying Lemma 3.5: this helper
supplies the `h_opt` minimizer comparison consumed by the two-Bregman descent
route.  SOptLib candidates considered: `two_bregman_argmin_descent` and
`two_bregman_argmin_variational_inequality_no_center_mem` are the downstream
descent bridges, but they require this pointwise argmin comparison plus local
Bregman derivative/three-point laws rather than replacing the transition
projection itself. -/
theorem sps_source_step_objective_le
    (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (n : ℕ) (ω : Ω) (u : FeasiblePoint S) :
    let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
      spsObjective_sourceDomain S g x β ι (states n ω).u (sample n ω)
          (proxCorePointToFeasible S (states (n + 1) ω).u) ≤
        spsObjective_sourceDomain S g x β ι (states n ω).u (sample n ω) u := by
  classical
  rcases hprocess with ⟨_hβpos, _hinit, htrans⟩
  have hstep :
      IsSPSStep_sourceDomain S g x β ⟨n + 1, Nat.succ_pos n⟩
        (states n ω).u (sample n ω)
        (proxCorePointToFeasible S (states (n + 1) ω).u) := by
    exact (htrans n ω).1
  exact (isMinOn_univ_iff
    (f := spsObjective_sourceDomain S g x β ⟨n + 1, Nat.succ_pos n⟩
      (states n ω).u (sample n ω))
    (a := proxCorePointToFeasible S (states (n + 1) ω).u)).1 hstep u

/-- Expanded Eq. (8.1.58) objective comparison for the SPS source-domain step.

This is the `h_opt` shape required by a two-Bregman Lemma 3.5 specialization:
the convex non-Bregman model appears separately from the two weighted Bregman
terms.  It is obtained by unfolding `spsObjective_sourceDomain`; the downstream
SOptLib two-Bregman candidates still need Bregman derivative laws and are not
replaced by this projection. -/
theorem sps_source_step_expanded_objective_le
    (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (n : ℕ) (ω : Ω) (u : FeasiblePoint S) :
    let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
    let q : E := S.oracle (states n ω).u.1 (sample n ω);
    let next : FeasiblePoint S := proxCorePointToFeasible S (states (n + 1) ω).u;
      (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
          β * bregmanOn S x next +
          β * spsP ι * bregmanOn S (states n ω).u next ≤
        (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) +
          β * bregmanOn S x u +
          β * spsP ι * bregmanOn S (states n ω).u u := by
  simpa [spsObjective_sourceDomain, add_assoc, add_left_comm, add_comm] using
    sps_source_step_objective_le S g x β sample states hprocess n ω u

/-- Convexity of the non-Bregman part of the SPS stochastic prox objective.

Aligns with Lan Lemma 3.5 as used in Proposition 8.3: the convex term is
`u ↦ g(u)+<H(u_{t-1},ξ),u>+χ(u)`, while the two Bregman terms are handled by
the prox descent theorem.  Candidate audit: `two_bregman_argmin_descent`
expects this `ConvexOn` hypothesis but does not prove it; SOptLib objective
wrappers are more general pointwise sums and do not know that the paper's `g`
is represented by `IsAffineModel`. -/
theorem sps_source_linear_chi_model_convexOn
    (g : E → ℝ) (hg : IsAffineModel g) (q : E) :
    ConvexOn ℝ S.X (fun z : E => g z + ⟪q, z⟫_ℝ + S.chi z) := by
  rcases hg with ⟨c, a, hgdef⟩
  refine ⟨S.convex_X, ?_⟩
  intro y hy z hz α η hα hη hsum
  have hchi := S.convex_chi.2 hy hz hα hη hsum
  have hlinear :
      g (α • y + η • z) + ⟪q, α • y + η • z⟫_ℝ =
        α * (g y + ⟪q, y⟫_ℝ) + η * (g z + ⟪q, z⟫_ℝ) := by
    simp [hgdef, inner_add_right, inner_smul_right]
    ring_nf
    have hc : c = c * α + c * η := by
      calc
        c = c * (α + η) := by rw [hsum]; ring
        _ = c * α + c * η := by ring
    nlinarith
  have hchi' :
      S.chi (α • y + η • z) ≤ α * S.chi y + η * S.chi z := by
    simpa [smul_eq_mul] using hchi
  calc
    g (α • y + η • z) + ⟪q, α • y + η • z⟫_ℝ + S.chi (α • y + η • z)
        ≤ g (α • y + η • z) + ⟪q, α • y + η • z⟫_ℝ +
            (α * S.chi y + η * S.chi z) := by
          linarith
    _ = α * (g y + ⟪q, y⟫_ℝ + S.chi y) +
          η * (g z + ⟪q, z⟫_ℝ + S.chi z) := by
          rw [hlinear]
          ring

/-- Three-point identity for the source-typed Bregman function.

Aligns with Lan Lemma 3.5's expansion of `V(x,u)` through the prox point.
This specializes SOptLib's canonical `bregmanDivergence_three_point_identity`
to the paper's `bregmanOn : X^o × X → ℝ`; no new primitive is introduced. -/
theorem bregmanOn_three_point_identity
    (a b : ProxCorePoint S) (c : FeasiblePoint S) :
    bregmanOn S a c =
      bregmanOn S a (proxCorePointToFeasible S b) +
        ⟪proxCoreGradient S b - proxCoreGradient S a, c.1 - b.1⟫_ℝ +
          bregmanOn S b c := by
  unfold bregmanOn proxCorePointToFeasible
  have hsplit : c.1 - a.1 = (c.1 - b.1) + (b.1 - a.1) := by
    abel
  rw [hsplit, inner_add_right, inner_sub_left]
  ring

/-- Final Bregman lower-bound normalization from the source restricted
strong-convexity predicate.

Aligns with Lan Section 3.2 Eq. (3.2.3).  Candidate audit:
`bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt`
proves the lower bound with `gradientWithin`; after reconstructing `bregmanOn`
to use that source gradient directly, no ambient-gradient pairing bridge remains. -/
theorem bregmanOn_lower_bound_of_proxCore_strong_convex
    (a b : ProxCorePoint S)
    (hstrong :
      StrongConvexOnWithGauge S.X 1
        S.primalNorm S.proxPotential) :
    (1 / 2 : ℝ) * S.primalNorm (b.1 - a.1) ^ 2 ≤
      bregmanOn S a (proxCorePointToFeasible S b) := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases S.prox_geometry with
    ⟨_hcont, hdiffX, _hcoreConv, _hcontdiffCore, _hconvNu, _hstrongSetup⟩
  have hstrongJensen :
      ∀ ⦃y⦄, y ∈ S.X → ∀ ⦃w⦄, w ∈ S.X → ∀ ⦃c d : ℝ⦄,
        0 ≤ c → 0 ≤ d → c + d = 1 →
          S.proxPotential (c • y + d • w) ≤
            c * S.proxPotential y + d * S.proxPotential w -
              (1 : ℝ) / 2 * c * d * S.primalNorm (y - w) ^ 2 := by
    intro y hy w hw c d hc hd hcd
    simpa [StrongConvexOnWithGauge] using
      hstrong (x := y) hy (y := w) hw (a := c) (b := d) hc hd hcd
  have hlowerWithin :=
    bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt
      (X := S.X) (ν := S.proxPotential) (p := S.primalNorm)
      (z := a.1) (x := b.1) S.convex_X
      (hdiffX a.1 (proxCore_subset a.2)) hstrongJensen
      (proxCore_subset a.2) (proxCore_subset b.2)
  have hpair :=
    proxCoreGradient_pairing_eq_gradientWithin_before_lower_bound
      (S := S) (proxCorePointToFeasible S a) (proxCorePointToFeasible S b) a.2
  have hpair' :
      ⟪proxCoreGradient S a, b.1 - a.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X a.1, b.1 - a.1⟫_ℝ := by
    simpa [proxCorePointToFeasible] using hpair
  rw [bregmanOn, proxCorePointToFeasible, hpair']
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hlowerWithin

/-- The source Eq. (3.2.1) monotone-gradient field specialized to prox-core
endpoints.

Aligns with Lan Section 3.2 Eq. (3.2.1).  The SOptLib candidate
`sq_norm_le_inner_gradient_sub_of_strong_distance_generator` packages this
abstract specialization, but the local paper setup already stores the exact
within-gradient seminorm inequality in `S.prox_geometry`, so this helper only
unpacks that field for downstream source-domain bridges. -/
theorem proxCore_gradient_strong_monotone_from_prox_geometry
    (a b : ProxCorePoint S) :
    S.primalNorm (b.1 - a.1) ^ 2 ≤
      ⟪b.1 - a.1, proxCoreGradient S b - proxCoreGradient S a⟫_ℝ := by
  classical
  rcases S.prox_geometry with ⟨_hcont, _hdiffX, _hcore_convex, _hdiffCore, _hconv, hstrong⟩
  have hab := bregmanOn_lower_bound_of_proxCore_strong_convex S a b hstrong
  have hba := bregmanOn_lower_bound_of_proxCore_strong_convex S b a hstrong
  have hnorm_rev : S.primalNorm (a.1 - b.1) = S.primalNorm (b.1 - a.1) := by
    have hneg : a.1 - b.1 = -(b.1 - a.1) := by abel
    rw [hneg]
    simpa using (map_neg_eq_map S.primalNorm (b.1 - a.1))
  have hba' : (1 / 2 : ℝ) * S.primalNorm (b.1 - a.1) ^ 2 ≤
      bregmanOn S b (proxCorePointToFeasible S a) := by
    simpa [hnorm_rev] using hba
  have hsum_lower : S.primalNorm (b.1 - a.1) ^ 2 ≤
      bregmanOn S a (proxCorePointToFeasible S b) +
        bregmanOn S b (proxCorePointToFeasible S a) := by
    nlinarith [hab, hba']
  have hsum_eq :
      bregmanOn S a (proxCorePointToFeasible S b) +
        bregmanOn S b (proxCorePointToFeasible S a) =
          ⟪b.1 - a.1, proxCoreGradient S b - proxCoreGradient S a⟫_ℝ := by
    unfold bregmanOn proxCorePointToFeasible
    simp [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  exact hsum_eq ▸ hsum_lower

/-- Chord derivative at the left endpoint in the canonical `gradientWithin`
form.

Aligns with Lan Section 3.2's differentiability of `ν` on `X^o`.  Candidate
audit: `bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt`
contains this argument internally for `gradientWithin`, while
`bregman_segment_difference_hasDerivWithinAt_zero` requires an ambient
`HasGradientAt`; this helper exposes the part derivable from the present
`ContDiffOn`-on-`proxCore` assumption without smuggling ambient differentiability. -/
theorem proxCore_line_derivative_gradientWithin_at_left
    (a b : ProxCorePoint S) :
    HasDerivWithinAt
      (fun r : ℝ => S.proxPotential (AffineMap.lineMap a.1 b.1 r))
      ⟪gradientWithin S.proxPotential S.X a.1,
        b.1 - a.1⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  rcases S.prox_geometry with ⟨_hcont, hdiffX, _hcore_convex, _hdiffCore, _hconv, _hstrong⟩
  let line : ℝ → E := fun r => AffineMap.lineMap a.1 b.1 r
  let d : E := b.1 - a.1
  have hline_deriv : HasDerivWithinAt line d (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [line, d] using
      (AffineMap.hasDerivWithinAt_lineMap (a := a.1) (b := b.1)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hmaps : Set.MapsTo line (Set.Icc (0 : ℝ) 1) S.X := by
    intro r hr
    exact S.convex_X.lineMap_mem (proxCore_subset a.2) (proxCore_subset b.2) hr
  have hνdiff : DifferentiableWithinAt ℝ S.proxPotential S.X a.1 :=
    hdiffX a.1 (proxCore_subset a.2)
  have hνline : HasDerivWithinAt (fun r : ℝ => S.proxPotential (line r))
      ((fderivWithin ℝ S.proxPotential S.X a.1) d) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [Function.comp_def] using
      hνdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
  have hgrad_apply :
      (fderivWithin ℝ S.proxPotential S.X a.1) d =
        ⟪gradientWithin S.proxPotential S.X a.1, d⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  simpa [line, d, hgrad_apply] using hνline

/-- Feasible-comparator first variation for the source Bregman kernel.

This is the reconstruct boundary needed by Lan Lemma 3.5 in Proposition 8.3:
the prox center and the minimizer are in `X^o`, but the comparator is only in
`X`.  The existing core-to-core derivative above is not enough for the segment
`lineMap z u`, so this theorem names the source first-variation obligation
directly at the paper type `V : X^o × X → R`.

Source references: Section 3.2 defines `V : X^o × X → R` by Eq. (3.2.2);
Lemma 3.5 assumes the differentiable prox function on `X`; Proposition 8.3
applies Lemma 3.5 to the stochastic prox subproblem (8.1.58). -/
theorem bregmanOn_feasible_segment_difference_hasDerivWithinAt_zero
    (a z : ProxCorePoint S) (u : FeasiblePoint S) :
    let d : E := u.1 - z.1
    let β : ℝ → ℝ := fun r =>
      if hr : r ∈ Set.Icc (0 : ℝ) 1 then
        bregmanOn S a
            ⟨AffineMap.lineMap z.1 u.1 r,
              S.convex_X.lineMap_mem (proxCore_subset z.2) u.2 hr⟩ -
          bregmanOn S a (proxCorePointToFeasible S z)
      else 0
    HasDerivWithinAt β
      ⟪proxCoreGradient S z - proxCoreGradient S a, d⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let d : E := u.1 - z.1
  let aF : FeasiblePoint S := proxCorePointToFeasible S a
  let zF : FeasiblePoint S := proxCorePointToFeasible S z
  let β : ℝ → ℝ := fun r =>
    if hr : r ∈ s then
      bregmanOn S a
          ⟨AffineMap.lineMap z.1 u.1 r,
            S.convex_X.lineMap_mem (proxCore_subset z.2) u.2 hr⟩ -
        bregmanOn S a (proxCorePointToFeasible S z)
    else 0
  let βX : ℝ → ℝ := fun r =>
    if hr : r ∈ s then
      bregmanFormulaOnX S aF
          ⟨AffineMap.lineMap z.1 u.1 r,
            S.convex_X.lineMap_mem zF.2 u.2 hr⟩ -
        bregmanFormulaOnX S aF zF
    else 0
  have hβXderiv : HasDerivWithinAt βX
      ⟪boundarySafeCarrierGradient S.X S.proxPotential zF -
          boundarySafeCarrierGradient S.X S.proxPotential aF, d⟫_ℝ s 0 := by
    simpa [βX, d, s, aF, zF, proxCorePointToFeasible] using
      bregmanFormulaOnX_feasible_segment_difference_hasDerivWithinAt_zero_before_stability
        S aF zF u
  have hβeq : β = βX := by
    funext r
    by_cases hr : r ∈ s
    · simp [β, βX, s, aF, zF, proxCorePointToFeasible, hr,
        bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore]
    · have hI : ¬ (0 ≤ r ∧ r ≤ 1) := by
        simpa [s, Set.mem_Icc] using hr
      simp [β, βX, s, hI]
  have hpair : ∀ (x : ProxCorePoint S) (v w : FeasiblePoint S),
      ⟪proxCoreGradient S x, w.1 - v.1⟫_ℝ =
        ⟪boundarySafeCarrierGradient S.X S.proxPotential (proxCorePointToFeasible S x),
          w.1 - v.1⟫_ℝ := by
    intro x v w
    let xF : FeasiblePoint S := proxCorePointToFeasible S x
    have hw :
        ⟪proxCoreGradient S x, w.1 - x.1⟫_ℝ =
          ⟪boundarySafeCarrierGradient S.X S.proxPotential xF, w.1 - x.1⟫_ℝ := by
      simpa [xF, proxCorePointToFeasible] using
        proxCoreGradient_inner_eq_boundarySafeCarrierGradient_on_feasible_direction_before_stability
          (S := S) xF w x.2
    have hv :
        ⟪proxCoreGradient S x, v.1 - x.1⟫_ℝ =
          ⟪boundarySafeCarrierGradient S.X S.proxPotential xF, v.1 - x.1⟫_ℝ := by
      simpa [xF, proxCorePointToFeasible] using
        proxCoreGradient_inner_eq_boundarySafeCarrierGradient_on_feasible_direction_before_stability
          (S := S) xF v x.2
    have hd : w.1 - v.1 = (w.1 - x.1) - (v.1 - x.1) := by
      abel
    calc
      ⟪proxCoreGradient S x, w.1 - v.1⟫_ℝ =
          ⟪proxCoreGradient S x, (w.1 - x.1) - (v.1 - x.1)⟫_ℝ := by
            rw [hd]
      _ = ⟪proxCoreGradient S x, w.1 - x.1⟫_ℝ -
            ⟪proxCoreGradient S x, v.1 - x.1⟫_ℝ := by
            rw [inner_sub_right]
      _ = ⟪boundarySafeCarrierGradient S.X S.proxPotential xF, w.1 - x.1⟫_ℝ -
            ⟪boundarySafeCarrierGradient S.X S.proxPotential xF, v.1 - x.1⟫_ℝ := by
            rw [hw, hv]
      _ = ⟪boundarySafeCarrierGradient S.X S.proxPotential xF,
            (w.1 - x.1) - (v.1 - x.1)⟫_ℝ := by
            exact (inner_sub_right
              (boundarySafeCarrierGradient S.X S.proxPotential xF)
              (w.1 - x.1) (v.1 - x.1)).symm
      _ = ⟪boundarySafeCarrierGradient S.X S.proxPotential xF,
            w.1 - v.1⟫_ℝ := by
            rw [← hd]
  have hzpair :
      ⟪proxCoreGradient S z, d⟫_ℝ =
        ⟪boundarySafeCarrierGradient S.X S.proxPotential zF, d⟫_ℝ := by
    simpa [d, zF, proxCorePointToFeasible] using hpair z zF u
  have hapair :
      ⟪proxCoreGradient S a, d⟫_ℝ =
        ⟪boundarySafeCarrierGradient S.X S.proxPotential aF, d⟫_ℝ := by
    simpa [d, aF, zF, proxCorePointToFeasible] using hpair a zF u
  have hval :
      ⟪proxCoreGradient S z - proxCoreGradient S a, d⟫_ℝ =
        ⟪boundarySafeCarrierGradient S.X S.proxPotential zF -
            boundarySafeCarrierGradient S.X S.proxPotential aF, d⟫_ℝ := by
    simp [inner_sub_left, hzpair, hapair]
  have hβXderiv' : HasDerivWithinAt βX
      ⟪proxCoreGradient S z - proxCoreGradient S a, d⟫_ℝ s 0 := by
    simpa [hval] using hβXderiv
  change HasDerivWithinAt β
    ⟪proxCoreGradient S z - proxCoreGradient S a, d⟫_ℝ s 0
  rw [hβeq]
  exact hβXderiv'

/-- First-order variational inequality behind Lan Lemma 3.5 at the
source-domain `bregmanOn` type.

Aligns with Lan Lemma 3.5 proof lines 3555-3558.  Candidate audit:
`SOptLib.two_bregman_argmin_variational_inequality_no_center_mem` and
`SOptLib.two_bregman_argmin_descent` have the exact abstract proof shape, but
they require a global `V : E → E → ℝ` and global three-point law; this paper
uses the source-typed `bregmanOn : ProxCorePoint S → FeasiblePoint S → ℝ`, so
the local helper specializes their segment-minimum proof without totalizing
outside `X`. -/
theorem dependent_two_bregman_variational_inequality_for_bregmanOn
    (p : E → ℝ) (hp_convex : ConvexOn ℝ S.X p)
    (xTilde yTilde uHat : ProxCorePoint S) (mu1 mu2 : ℝ)
    (h_opt :
      ∀ u : FeasiblePoint S,
        p uHat.1 +
            mu1 * bregmanOn S xTilde (proxCorePointToFeasible S uHat) +
            mu2 * bregmanOn S yTilde (proxCorePointToFeasible S uHat) ≤
          p u.1 + mu1 * bregmanOn S xTilde u +
            mu2 * bregmanOn S yTilde u)
    (u : FeasiblePoint S) :
    0 ≤ p u.1 - p uHat.1 +
      mu1 * ⟪proxCoreGradient S uHat - proxCoreGradient S xTilde,
        u.1 - uHat.1⟫_ℝ +
      mu2 * ⟪proxCoreGradient S uHat - proxCoreGradient S yTilde,
        u.1 - uHat.1⟫_ℝ := by
  classical
  let d : E := u.1 - uHat.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let βx : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      bregmanOn S xTilde
          ⟨AffineMap.lineMap uHat.1 u.1 t,
            S.convex_X.lineMap_mem (proxCore_subset uHat.2) u.2 ht⟩ -
        bregmanOn S xTilde (proxCorePointToFeasible S uHat)
    else 0
  let βy : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      bregmanOn S yTilde
          ⟨AffineMap.lineMap uHat.1 u.1 t,
            S.convex_X.lineMap_mem (proxCore_subset uHat.2) u.2 ht⟩ -
        bregmanOn S yTilde (proxCorePointToFeasible S uHat)
    else 0
  let φ : ℝ → ℝ := fun t =>
    t * (p u.1 - p uHat.1) + mu1 * βx t + mu2 * βy t
  have hβxderiv : HasDerivWithinAt βx
      ⟪proxCoreGradient S uHat - proxCoreGradient S xTilde, d⟫_ℝ s 0 := by
    simpa [βx, d, s] using
      bregmanOn_feasible_segment_difference_hasDerivWithinAt_zero S xTilde uHat u
  have hβyderiv : HasDerivWithinAt βy
      ⟪proxCoreGradient S uHat - proxCoreGradient S yTilde, d⟫_ℝ s 0 := by
    simpa [βy, d, s] using
      bregmanOn_feasible_segment_difference_hasDerivWithinAt_zero S yTilde uHat u
  have hpderiv : HasDerivWithinAt (fun t : ℝ => t * (p u.1 - p uHat.1))
      (p u.1 - p uHat.1) s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
      (p u.1 - p uHat.1)
  have hφderiv : HasDerivWithinAt φ
      (p u.1 - p uHat.1 +
        mu1 * ⟪proxCoreGradient S uHat - proxCoreGradient S xTilde, d⟫_ℝ +
        mu2 * ⟪proxCoreGradient S uHat - proxCoreGradient S yTilde, d⟫_ℝ) s 0 := by
    have hxmul : HasDerivWithinAt (fun t : ℝ => mu1 * βx t)
        (mu1 * ⟪proxCoreGradient S uHat - proxCoreGradient S xTilde, d⟫_ℝ) s 0 := by
      simpa using hβxderiv.const_mul mu1
    have hymul : HasDerivWithinAt (fun t : ℝ => mu2 * βy t)
        (mu2 * ⟪proxCoreGradient S uHat - proxCoreGradient S yTilde, d⟫_ℝ) s 0 := by
      simpa using hβyderiv.const_mul mu2
    simpa [φ, add_assoc] using (hpderiv.add hxmul).add hymul
  have hφmin : ∀ t ∈ s, φ 0 ≤ φ t := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    let wPoint : E := AffineMap.lineMap uHat.1 u.1 t
    have hwPoint : wPoint ∈ S.X := by
      simpa [wPoint] using
        S.convex_X.lineMap_mem (proxCore_subset uHat.2) u.2 htI
    let w : FeasiblePoint S := ⟨wPoint, hwPoint⟩
    have hline_conv :
        wPoint = (1 - t) • uHat.1 + t • u.1 := by
      simp [wPoint, AffineMap.lineMap_apply_module']
      module
    have hpseg : p w.1 - p uHat.1 ≤ t * (p u.1 - p uHat.1) := by
      have hconv :=
        hp_convex.2 (proxCore_subset uHat.2) u.2 (sub_nonneg.mpr ht1) ht0 (by ring)
      rw [← hline_conv] at hconv
      have hconv' : p wPoint ≤ (1 - t) * p uHat.1 + t * p u.1 := by
        simpa [smul_eq_mul] using hconv
      change p wPoint - p uHat.1 ≤ t * (p u.1 - p uHat.1)
      nlinarith
    have hmin := h_opt w
    have hFdiff :
        0 ≤ (p w.1 - p uHat.1) +
          mu1 * (bregmanOn S xTilde w -
            bregmanOn S xTilde (proxCorePointToFeasible S uHat)) +
          mu2 * (bregmanOn S yTilde w -
            bregmanOn S yTilde (proxCorePointToFeasible S uHat)) := by
      nlinarith
    have hβx_eval : βx t =
        bregmanOn S xTilde w -
          bregmanOn S xTilde (proxCorePointToFeasible S uHat) := by
      simp [βx, w, wPoint, ht, bregmanOn]
    have hβy_eval : βy t =
        bregmanOn S yTilde w -
          bregmanOn S yTilde (proxCorePointToFeasible S uHat) := by
      simp [βy, w, wPoint, ht, bregmanOn]
    have hφ0 : φ 0 = 0 := by
      simp [φ, βx, βy, s, bregmanOn, proxCorePointToFeasible,
        AffineMap.lineMap_apply_module']
    have hupper :
        (p w.1 - p uHat.1) +
          mu1 * (bregmanOn S xTilde w -
            bregmanOn S xTilde (proxCorePointToFeasible S uHat)) +
          mu2 * (bregmanOn S yTilde w -
            bregmanOn S yTilde (proxCorePointToFeasible S uHat)) ≤ φ t := by
      dsimp [φ]
      rw [hβx_eval, hβy_eval]
      nlinarith
    rw [hφ0]
    exact le_trans hFdiff hupper
  have hnonneg :=
    hasDerivWithinAt_nonneg_of_isMinOn_Icc_left (by norm_num) hφderiv hφmin
  simpa [d] using hnonneg

/-- Lan Lemma 3.5 specialized to the source-typed Bregman kernel used by SPS.

This is not a new primitive assumption: its hypotheses are exactly the convex
non-Bregman term, nonnegative Bregman weights, and argmin comparison from
Lemma 3.5.  The theorem packages the feasible-comparator first-variation bridge
above together with the already available three-point identity for
`bregmanOn`. -/
theorem lemma35_source_domain_interface_for_bregmanOn
    (p : E → ℝ) (hp_convex : ConvexOn ℝ S.X p)
    (xTilde yTilde uHat : ProxCorePoint S) (mu1 mu2 : ℝ)
    (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2)
    (h_opt :
      ∀ u : FeasiblePoint S,
        p uHat.1 +
            mu1 * bregmanOn S xTilde (proxCorePointToFeasible S uHat) +
            mu2 * bregmanOn S yTilde (proxCorePointToFeasible S uHat) ≤
          p u.1 + mu1 * bregmanOn S xTilde u +
            mu2 * bregmanOn S yTilde u) :
    ∀ u : FeasiblePoint S,
      p uHat.1 +
          mu1 * bregmanOn S xTilde (proxCorePointToFeasible S uHat) +
          mu2 * bregmanOn S yTilde (proxCorePointToFeasible S uHat) ≤
        p u.1 + mu1 * bregmanOn S xTilde u +
          mu2 * bregmanOn S yTilde u -
            (mu1 + mu2) * bregmanOn S uHat u := by
  classical
  /-
  Proof route for FILL: copy the dependent version of
  `SOptLib.two_bregman_argmin_descent`.  Use `hp_convex` on the feasible
  segment, `bregmanOn_feasible_segment_difference_hasDerivWithinAt_zero` for
  the two Bregman derivatives at `uHat`, and
  `bregmanOn_three_point_identity` for the final cancellation.
  -/
  intro u
  have hvar :=
    dependent_two_bregman_variational_inequality_for_bregmanOn S
      p hp_convex xTilde yTilde uHat mu1 mu2 h_opt u
  have hx3 := bregmanOn_three_point_identity S xTilde uHat u
  have hy3 := bregmanOn_three_point_identity S yTilde uHat u
  nlinarith

/-- Source Eq. (3.2.3) lower bound for two prox-core endpoints.

Aligns with Lan Section 3.2 Eq. (3.2.3), used in Proposition 8.3's Young
absorption step.  Candidate audit: `bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt`
and `blockBregmanDivergence_lower_bound_of_strongConvexOnWithNorm` prove the
same lower-bound shape from Jensen/`StrongConvexOnWithGauge` hypotheses;
`bregman_segment_difference_hasDerivWithinAt_zero` supplies the derivative
shape from `HasGradientAt`; none directly matches this file's source-facing
`ProxGeometryOn`, which stores the paper's monotone-gradient Eq. (3.2.1) on
`proxCore` and `ContDiffOn` only on that set. -/
theorem bregmanOn_core_core_lower_bound_from_prox_geometry
    (a b : ProxCorePoint S) :
    (1 / 2 : ℝ) * S.primalNorm (b.1 - a.1) ^ 2 ≤
      bregmanOn S a (proxCorePointToFeasible S b) := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases S.prox_geometry with ⟨_hcont, _hdiffX, _hcore_convex, _hdiffCore, _hconv, hstrong⟩
  exact bregmanOn_lower_bound_of_proxCore_strong_convex S a b hstrong

/-- Scalar Young absorption used after the source Bregman lower bound in
Proposition 8.3.

Aligns with Lan Proposition 8.3, proof lines applying Eq. (3.2.3) and
`-a t^2/2 + b t ≤ b^2/(2a)`.  SOptLib scalar candidates considered:
`scaled_linear_inner_quadratic_le_square_over_denominator` uses the ambient norm
and Hilbert dual norm, while this paper step must keep the stated primal
seminorm and its `dualNorm`, so the local helper records exactly the
source-domain scalar shape. -/
theorem sps_source_bregman_young_absorption
    {a b V r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hV : (1 / 2 : ℝ) * r ^ 2 ≤ V) :
    -a * V + b * r ≤ b ^ 2 / (2 * a) := by
  have hquad : -(a / 2) * r ^ 2 + b * r ≤ b ^ 2 / (2 * a) := by
    have hsq : 0 ≤ (a * r - b) ^ 2 := sq_nonneg _
    field_simp [ne_of_gt ha]
    nlinarith [hsq, ha]
  have hVscaled : (a / 2) * r ^ 2 ≤ a * V := by
    nlinarith [mul_le_mul_of_nonneg_left hV ha.le]
  nlinarith

/-- Proposition 8.3 displacement absorption in the paper's primal/dual norms.

Aligns with Lan Proposition 8.3, proof step
`-β p_t V(u_{t-1},u_t)+(M+‖δ_t‖_*)‖u_t-u_{t-1}‖ ≤ ...`.  The SOptLib
candidate `scaled_linear_inner_quadratic_le_square_over_denominator` was
considered but rejected here because it is specialized to the ambient Hilbert
norm; this helper preserves the paper's `S.primalNorm` and source Bregman
lower bound. -/
theorem sps_source_displacement_absorption
    (β : ℝ) (ι : PositiveTime)
    (prev next : ProxCorePoint S) (δ : E) (hβ : 0 < β) :
    -β * spsP ι * bregmanOn S prev (proxCorePointToFeasible S next) +
        (S.mGrowth + dualNorm S δ) * S.primalNorm (next.1 - prev.1) ≤
      (S.mGrowth + dualNorm S δ) ^ 2 / (2 * β * spsP ι) := by
  have hp : 0 < spsP ι := by
    have hι : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
    unfold spsP
    positivity
  have ha : 0 < β * spsP ι := mul_pos hβ hp
  have hr : 0 ≤ S.primalNorm (next.1 - prev.1) := apply_nonneg S.primalNorm _
  have hV :
      (1 / 2 : ℝ) * S.primalNorm (next.1 - prev.1) ^ 2 ≤
        bregmanOn S prev (proxCorePointToFeasible S next) :=
    bregmanOn_core_core_lower_bound_from_prox_geometry S prev next
  have hyoung :=
    sps_source_bregman_young_absorption
      (a := β * spsP ι) (b := S.mGrowth + dualNorm S δ)
      (V := bregmanOn S prev (proxCorePointToFeasible S next))
      (r := S.primalNorm (next.1 - prev.1)) ha hr hV
  calc
    -β * spsP ι * bregmanOn S prev (proxCorePointToFeasible S next) +
        (S.mGrowth + dualNorm S δ) * S.primalNorm (next.1 - prev.1)
        = -(β * spsP ι) * bregmanOn S prev (proxCorePointToFeasible S next) +
            (S.mGrowth + dualNorm S δ) * S.primalNorm (next.1 - prev.1) := by
          ring
      _ ≤ (S.mGrowth + dualNorm S δ) ^ 2 / (2 * (β * spsP ι)) := hyoung
      _ = (S.mGrowth + dualNorm S δ) ^ 2 / (2 * β * spsP ι) := by
            ring

/-- One-step SPS descent obtained by applying the source-domain Lemma 3.5
specialization to the expanded Eq. (8.1.58) minimizer comparison. -/
theorem sps_source_step_two_bregman_descent
    (g : E → ℝ) (hg : IsAffineModel g) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (n : ℕ) (ω : Ω) (u : FeasiblePoint S) :
    let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
    let q : E := S.oracle (states n ω).u.1 (sample n ω);
    let next : FeasiblePoint S := proxCorePointToFeasible S (states (n + 1) ω).u;
      (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
          β * bregmanOn S x next +
          β * spsP ι * bregmanOn S (states n ω).u next ≤
        (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) +
          β * bregmanOn S x u +
          β * spsP ι * bregmanOn S (states n ω).u u -
            (β + β * spsP ι) * bregmanOn S (states (n + 1) ω).u u := by
  classical
  let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  let q : E := S.oracle (states n ω).u.1 (sample n ω)
  let nextCore : ProxCorePoint S := (states (n + 1) ω).u
  let next : FeasiblePoint S := proxCorePointToFeasible S nextCore
  have hp_conv :
      ConvexOn ℝ S.X (fun z : E => g z + ⟪q, z⟫_ℝ + S.chi z) :=
    sps_source_linear_chi_model_convexOn S g hg q
  have hopt_raw :=
    sps_source_step_expanded_objective_le S g x β sample states hprocess n ω
  rcases hprocess with ⟨hβpos, _hinit, _htrans⟩
  have hpι_nonneg : 0 ≤ spsP ι := by
    have hι : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
    unfold spsP
    positivity
  have hdescent :=
    lemma35_source_domain_interface_for_bregmanOn S
      (p := fun z : E => g z + ⟪q, z⟫_ℝ + S.chi z)
      hp_conv x (states n ω).u nextCore β (β * spsP ι)
      hβpos.le (mul_nonneg hβpos.le hpι_nonneg)
      (by
        intro v
        simpa [ι, q, nextCore, next, add_assoc, add_left_comm, add_comm] using
          hopt_raw v)
      u
  simpa [ι, q, nextCore, next, add_assoc, add_left_comm, add_comm] using hdescent

/-- One-step source-domain Phi recurrence used in Proposition 8.3.

Aligns with Lan Proposition 8.3 proof, lines deriving the inequality before the
`P_t`/`θ_t` telescope.  Candidate audit: SOptLib one-step mirror-descent
recurrences such as `mirrorDescent_oneStep_pathwise_of_residual_lower_bound`
and `accelerated_composite_recurrence_of_two_bregman_descent` were considered;
they package related residual/Bregman algebra but do not match the SGS
two-center source-domain objective with the paper's explicit
`h`-growth term and `spsP` coefficient. -/
theorem sps_source_one_step_phi_bound
    (g : E → ℝ) (hg : IsAffineModel g) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (n : ℕ) (ω : Ω) (u : FeasiblePoint S) :
    let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
    let δ := oracleNoiseAt S ((states n ω).u.1) (sample n ω);
    let next : FeasiblePoint S := proxCorePointToFeasible S (states (n + 1) ω).u;
      spsPhi_sourceDomain S g x β next - spsPhi_sourceDomain S g x β u ≤
        β * spsP ι * bregmanOn S (states n ω).u u -
          β * (1 + spsP ι) * bregmanOn S (states (n + 1) ω).u u +
          ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
          ⟪δ, u.1 - (states n ω).u.1⟫_ℝ := by
  classical
  let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  let prev : ProxCorePoint S := (states n ω).u
  let nextCore : ProxCorePoint S := (states (n + 1) ω).u
  let next : FeasiblePoint S := proxCorePointToFeasible S nextCore
  let q : E := S.oracle prev.1 (sample n ω)
  let δ : E := oracleNoiseAt S prev.1 (sample n ω)
  let r : ℝ := S.primalNorm (next.1 - prev.1)
  have hβpos : 0 < β := hprocess.1
  have hq_decomp : q = S.hSubgradient prev.1 + δ := by
    simp [q, δ, oracleNoiseAt]
  have hprevX : prev.1 ∈ S.X := proxCore_subset prev.2
  have hnextX : next.1 ∈ S.X := next.2
  have hgrowth :
      S.h next.1 ≤
        S.h prev.1 + ⟪q, next.1⟫_ℝ - ⟪q, prev.1⟫_ℝ -
          ⟪δ, next.1 - prev.1⟫_ℝ + S.mGrowth * r := by
    have hgrowth0 :=
      S.nonsmooth_growth (x := next.1) (y := prev.1) hnextX hprevX
    calc
      S.h next.1
          ≤ S.h prev.1 + ⟪S.hSubgradient prev.1, next.1 - prev.1⟫_ℝ +
              S.mGrowth * r := by
            simpa [r] using hgrowth0
      _ = S.h prev.1 + ⟪q, next.1⟫_ℝ - ⟪q, prev.1⟫_ℝ -
              ⟪δ, next.1 - prev.1⟫_ℝ + S.mGrowth * r := by
            rw [hq_decomp]
            simp [inner_add_left, inner_sub_right]
            ring
  have hsub_le :
      S.h prev.1 + ⟪q, u.1⟫_ℝ - ⟪q, prev.1⟫_ℝ ≤
        S.h u.1 + ⟪δ, u.1 - prev.1⟫_ℝ := by
    have hmem := (setup_hSubgradientMem S) prev.1 hprevX
    have hsupport :=
      (SOptLib.mem_carrierSubdifferential_iff.mp hmem) ⟨u.1, u.2⟩
    calc
      S.h prev.1 + ⟪q, u.1⟫_ℝ - ⟪q, prev.1⟫_ℝ
          = S.h prev.1 + ⟪q, u.1 - prev.1⟫_ℝ := by
              simp [inner_sub_right]
              ring
      _ = S.h prev.1 + ⟪S.hSubgradient prev.1, u.1 - prev.1⟫_ℝ +
            ⟪δ, u.1 - prev.1⟫_ℝ := by
              rw [hq_decomp]
              simp [inner_add_left]
              ring
      _ ≤ S.h u.1 + ⟪δ, u.1 - prev.1⟫_ℝ := by
              nlinarith [hsupport]
  have hnoise_step :
      -⟪δ, next.1 - prev.1⟫_ℝ ≤ dualNorm S δ * r := by
    have hneg_abs : -⟪δ, next.1 - prev.1⟫_ℝ ≤
        |⟪δ, next.1 - prev.1⟫_ℝ| := neg_le_abs _
    have hdual :=
      abs_inner_le_dualNorm_mul_primalNorm S δ (next.1 - prev.1)
    exact hneg_abs.trans (by simpa [r] using hdual)
  have hdescent0 :=
    sps_source_step_two_bregman_descent S g hg x β sample states hprocess n ω u
  have hdescent :
      (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
          β * bregmanOn S x next ≤
        (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) +
          β * bregmanOn S x u +
          β * spsP ι * bregmanOn S prev u -
            (β + β * spsP ι) * bregmanOn S nextCore u -
            β * spsP ι * bregmanOn S prev next := by
    have hdescent1 :
        (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
            β * bregmanOn S x next +
            β * spsP ι * bregmanOn S prev next ≤
          (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) +
            β * bregmanOn S x u +
            β * spsP ι * bregmanOn S prev u -
              (β + β * spsP ι) * bregmanOn S nextCore u := by
      simpa [ι, prev, nextCore, next, q, add_assoc, add_left_comm, add_comm] using
        hdescent0
    nlinarith
  have hraw :
      spsPhi_sourceDomain S g x β next - spsPhi_sourceDomain S g x β u ≤
        β * spsP ι * bregmanOn S prev u -
          (β + β * spsP ι) * bregmanOn S nextCore u -
          β * spsP ι * bregmanOn S prev next +
          ⟪δ, u.1 - prev.1⟫_ℝ +
          (S.mGrowth + dualNorm S δ) * r := by
    unfold spsPhi_sourceDomain
    nlinarith [hdescent, hgrowth, hsub_le, hnoise_step]
  have habsorb :=
    sps_source_displacement_absorption S β ι prev nextCore δ hβpos
  have habsorb' :
      -β * spsP ι * bregmanOn S prev next +
          (S.mGrowth + dualNorm S δ) * r ≤
        (S.mGrowth + dualNorm S δ) ^ 2 / (2 * β * spsP ι) := by
    simpa [next, r] using habsorb
  have hraw' :
      spsPhi_sourceDomain S g x β next - spsPhi_sourceDomain S g x β u ≤
        β * spsP ι * bregmanOn S prev u -
          β * (1 + spsP ι) * bregmanOn S nextCore u -
          β * spsP ι * bregmanOn S prev next +
          ⟪δ, u.1 - prev.1⟫_ℝ +
          (S.mGrowth + dualNorm S δ) * r := by
    nlinarith [hraw]
  have hfinal :
      spsPhi_sourceDomain S g x β next - spsPhi_sourceDomain S g x β u ≤
        β * spsP ι * bregmanOn S prev u -
          β * (1 + spsP ι) * bregmanOn S nextCore u +
          ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
          ⟪δ, u.1 - prev.1⟫_ℝ := by
    nlinarith [hraw', habsorb']
  simpa [ι, prev, nextCore, next, δ, add_assoc, add_left_comm, add_comm] using hfinal

/-- SPS average recursion rewritten with the Eq. (8.1.20) product-defined theta.

This is the direct transition bridge needed by the Proposition 8.3 telescope:
it consumes the process update equation and `spsTheta_eq_psThetaFromProduct_spsP`
rather than introducing a new averaging primitive.  SOptLib weighted-output
helpers were considered, but the process stores this two-point recursive
average rather than a pre-normalized finite output window. -/
theorem sps_source_avg_update_product_theta
    (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (n : ℕ) (ω : Ω) :
    let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
      (states (n + 1) ω).avg.1 =
        (1 - psThetaFromProduct spsP ι) • (states n ω).avg.1 +
          psThetaFromProduct spsP ι • (states (n + 1) ω).u.1 := by
  classical
  let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  have htrans := hprocess.2.2 n ω
  have htheta := spsTheta_eq_psThetaFromProduct_spsP ι
  have havg : (states (n + 1) ω).avg.1 =
      (1 - spsTheta ι) • (states n ω).avg.1 +
        spsTheta ι • (states (n + 1) ω).u.1 := by
    simpa [IsSPSTransition_sourceDomain, ι] using htrans.2
  simpa [ι, htheta] using havg

/-- Closed-form weighted average identity behind Eq. (8.1.24), expressed with
the explicit SPS coefficients.

Aligns with Lan Eq. (8.1.24).  Candidate audit: considered
`weightedAverageOutputValue`/`weightedAverageOutput_def`, but the SPS process
stores a recursive two-point average rather than a prepackaged normalized
output value; this helper derives the closed form from
`sps_source_avg_update_product_theta` and the process initialization. -/
theorem sps_source_avg_eq_explicit_weighted_sum_succ
    (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (ω : Ω) (n : ℕ) :
    (states (n + 1) ω).avg.1 =
      (Finset.range (n + 1)).sum (fun i =>
        (2 * ((i : ℝ) + 2) / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 3))) •
          (states (i + 1) ω).u.1) := by
  classical
  induction n with
  | zero =>
      have hrec :=
        sps_source_avg_update_product_theta S g x β sample states hprocess 0 ω
      have htheta :
          psThetaFromProduct spsP ⟨0 + 1, Nat.succ_pos 0⟩ = 1 := by
        norm_num [psThetaFromProduct, psWeightProduct, spsP]
      have hcoef :
          2 * (((0 : ℕ) : ℝ) + 2) /
              (((0 + 1 : ℕ) : ℝ) * (((0 + 1 : ℕ) : ℝ) + 3)) = 1 := by
        norm_num
      calc
        (states (0 + 1) ω).avg.1 = (states (0 + 1) ω).u.1 := by
          simpa [htheta] using hrec
        _ =
            (Finset.range (0 + 1)).sum (fun i =>
              (2 * ((i : ℝ) + 2) /
                  (((0 + 1 : ℕ) : ℝ) * (((0 + 1 : ℕ) : ℝ) + 3))) •
                (states (i + 1) ω).u.1) := by
          norm_num
  | succ n ih =>
      let ι : PositiveTime := ⟨n + 2, by omega⟩
      have hrec :=
        sps_source_avg_update_product_theta S g x β sample states hprocess (n + 1) ω
      have htheta :
          psThetaFromProduct spsP ⟨n + 1 + 1, Nat.succ_pos (n + 1)⟩ =
            spsTheta ι := by
        simpa [ι] using (spsTheta_eq_psThetaFromProduct_spsP ι).symm
      have hscale :
          (1 - spsTheta ι) •
              (Finset.range (n + 1)).sum (fun i =>
                (2 * ((i : ℝ) + 2) /
                    (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 3))) •
                  (states (i + 1) ω).u.1) =
            (Finset.range (n + 1)).sum (fun i =>
              (2 * ((i : ℝ) + 2) /
                  (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 3))) •
                (states (i + 1) ω).u.1) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [smul_smul]
        congr 1
        unfold spsTheta ι
        have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hn2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        have hn4 : ((n + 1 : ℕ) : ℝ) + 3 ≠ 0 := by positivity
        have hn5 : ((n + 2 : ℕ) : ℝ) + 3 ≠ 0 := by positivity
        field_simp [hn1, hn2, hn4, hn5]
        norm_num
        ring
      have hlast :
          spsTheta ι =
            2 * (((n + 1 : ℕ) : ℝ) + 2) /
              (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 3)) := by
        unfold spsTheta ι
        have hn2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        have hn5 : ((n + 2 : ℕ) : ℝ) + 3 ≠ 0 := by positivity
        field_simp [hn2, hn5]
        norm_num
        ring
      calc
        (states (n + 1 + 1) ω).avg.1 =
            (1 - spsTheta ι) • (states (n + 1) ω).avg.1 +
              spsTheta ι • (states (n + 1 + 1) ω).u.1 := by
              simpa [ι, htheta] using hrec
        _ =
            (1 - spsTheta ι) •
                (Finset.range (n + 1)).sum (fun i =>
                  (2 * ((i : ℝ) + 2) /
                      (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 3))) •
                    (states (i + 1) ω).u.1) +
              spsTheta ι • (states (n + 1 + 1) ω).u.1 := by
              rw [ih]
        _ =
            (Finset.range (n + 1)).sum (fun i =>
              (2 * ((i : ℝ) + 2) /
                  (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 3))) •
                (states (i + 1) ω).u.1) +
              (2 * (((n + 1 : ℕ) : ℝ) + 2) /
                (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 3))) •
                  (states (n + 1 + 1) ω).u.1 := by
              rw [hscale, hlast]
        _ =
            (Finset.range (n + 2)).sum (fun i =>
              (2 * ((i : ℝ) + 2) /
                  (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 3))) •
                (states (i + 1) ω).u.1) := by
              conv_rhs => rw [Finset.sum_range_succ]

/-- Closed-form weighted average identity behind Eq. (8.1.24), in the exact
`P_t/(1-P_t)` coefficient form used by Proposition 8.3.

Aligns with Lan Eq. (8.1.24).  Candidate audit: SOptLib's
`weightedAverageOutputValue` names an already normalized average, and
`convexOn_weighted_average_le_weighted_sum` consumes such a closed form; neither
derives the SPS recursive average identity from `θ_t`, so this helper is the
paper-specific bridge from `sps_source_avg_update_product_theta`. -/
theorem sps_source_avg_eq_weighted_sum_succ
    (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (ω : Ω) (n : ℕ) :
    (states (n + 1) ω).avg.1 =
      (psWeightProduct spsP (n + 1) *
          (1 - psWeightProduct spsP (n + 1))⁻¹) •
        (Finset.range (n + 1)).sum (fun i =>
          ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
            (states (i + 1) ω).u.1) := by
  classical
  have hexpl :=
    sps_source_avg_eq_explicit_weighted_sum_succ S g x β sample states hprocess ω n
  calc
    (states (n + 1) ω).avg.1 =
        (Finset.range (n + 1)).sum (fun i =>
          (2 * ((i : ℝ) + 2) /
              (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 3))) •
            (states (i + 1) ω).u.1) := hexpl
    _ =
        (psWeightProduct spsP (n + 1) *
            (1 - psWeightProduct spsP (n + 1))⁻¹) •
          (Finset.range (n + 1)).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
              (states (i + 1) ω).u.1) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [smul_smul]
        rw [sps_normalized_weight_eq (n + 1) i (Nat.succ_pos n)]

/-- Positive-time version of the Eq. (8.1.24) weighted-average identity.

Aligns with Lan Eq. (8.1.24).  This is the direct form needed before applying
finite Jensen to `Φ(ũ_t)`. -/
theorem sps_source_avg_eq_weighted_sum
    (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (ω : Ω) (t : PositiveTime) :
    (states t.1 ω).avg.1 =
      (psWeightProduct spsP t.1 *
          (1 - psWeightProduct spsP t.1)⁻¹) •
        (Finset.range t.1).sum (fun i =>
          ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
            (states (i + 1) ω).u.1) := by
  classical
  cases t with
  | mk m hm =>
      have hmpos : 0 < m := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
      exact sps_source_avg_eq_weighted_sum_succ S g x β sample states hprocess ω n

/-- Convexity in the second argument of the source-domain Bregman kernel.

Aligns with Lan Section 3.2 prox geometry.  Candidate audit: considered
SOptLib Bregman nonnegativity/lower-bound lemmas and the carrier Bregman
bridges; those prove coercivity or formula transport, while this proof needs
the elementary fact that `ν(z)-linear(z)` is convex on `X`, derived from the
`ConvexOn` field inside `S.prox_geometry`. -/
theorem bregmanOn_right_convexOn_totalized (x : ProxCorePoint S) :
    ConvexOn ℝ S.X
      (SOptLib.carrierTotalizeOn S.X
        (fun z : FeasiblePoint S => bregmanOn S x z)) := by
  classical
  rcases S.prox_geometry with
    ⟨_hcont, _hdiffX, _hcore_convex, _hdiffCore, hnu_conv, _hstrong⟩
  refine ⟨S.convex_X, ?_⟩
  intro y hy z hz α η hα hη hsum
  have hseg : α • y + η • z ∈ S.X :=
    S.convex_X hy hz hα hη hsum
  have hnu :
      S.proxPotential (α • y + η • z) ≤
        α * S.proxPotential y + η * S.proxPotential z := by
    simpa [smul_eq_mul] using hnu_conv.2 hy hz hα hη hsum
  have hvec :
      α • y + η • z - x.1 = α • (y - x.1) + η • (z - x.1) := by
    have hx : x.1 = α • x.1 + η • x.1 := by
      rw [← add_smul, hsum, one_smul]
    calc
      α • y + η • z - x.1 = α • y + η • z - (α • x.1 + η • x.1) := by
        conv_lhs => rw [hx]
      _ = α • (y - x.1) + η • (z - x.1) := by
        module
  have hinner :
      ⟪proxCoreGradient S x, α • y + η • z - x.1⟫_ℝ =
        α * ⟪proxCoreGradient S x, y - x.1⟫_ℝ +
          η * ⟪proxCoreGradient S x, z - x.1⟫_ℝ := by
    rw [hvec]
    simp [inner_add_right, inner_smul_right]
  have hVraw :
      S.proxPotential (α • y + η • z) - S.proxPotential x.1 -
          ⟪proxCoreGradient S x, α • y + η • z - x.1⟫_ℝ ≤
        α * (S.proxPotential y - S.proxPotential x.1 -
            ⟪proxCoreGradient S x, y - x.1⟫_ℝ) +
          η * (S.proxPotential z - S.proxPotential x.1 -
            ⟪proxCoreGradient S x, z - x.1⟫_ℝ) := by
    calc
      S.proxPotential (α • y + η • z) - S.proxPotential x.1 -
          ⟪proxCoreGradient S x, α • y + η • z - x.1⟫_ℝ
          =
        S.proxPotential (α • y + η • z) - S.proxPotential x.1 -
          (α * ⟪proxCoreGradient S x, y - x.1⟫_ℝ +
            η * ⟪proxCoreGradient S x, z - x.1⟫_ℝ) := by
            rw [hinner]
      _ ≤
        α * S.proxPotential y + η * S.proxPotential z - S.proxPotential x.1 -
          (α * ⟪proxCoreGradient S x, y - x.1⟫_ℝ +
            η * ⟪proxCoreGradient S x, z - x.1⟫_ℝ) := by
            nlinarith [hnu]
      _ =
        α * (S.proxPotential y - S.proxPotential x.1 -
            ⟪proxCoreGradient S x, y - x.1⟫_ℝ) +
          η * (S.proxPotential z - S.proxPotential x.1 -
            ⟪proxCoreGradient S x, z - x.1⟫_ℝ) := by
            have hconst :
                S.proxPotential x.1 =
                  α * S.proxPotential x.1 + η * S.proxPotential x.1 := by
              calc
                S.proxPotential x.1 = (α + η) * S.proxPotential x.1 := by
                  rw [hsum]
                  ring
                _ = α * S.proxPotential x.1 + η * S.proxPotential x.1 := by
                  ring
            nlinarith [hconst]
  simpa [SOptLib.carrierTotalizeOn, hseg, hy, hz, bregmanOn] using hVraw

/-- Convexity of the totalized source-domain `Φ` used for Eq. (8.1.24).

Aligns with Lan Proposition 8.3 proof step "use convexity of `Φ`".  Candidate
audit: `sps_source_linear_chi_model_convexOn` covers only the non-Bregman prox
objective term, while `convexOn_weighted_average_le_weighted_sum` consumes but
does not prove objective convexity; this helper combines affine `g`, convex
`h`/`χ`, and the Bregman second-argument convexity above. -/
theorem spsPhi_sourceDomain_convexOn_totalized
    (g : E → ℝ) (hg : IsAffineModel g) (x : ProxCorePoint S) {β : ℝ}
    (hβ : 0 ≤ β) :
    ConvexOn ℝ S.X
      (SOptLib.carrierTotalizeOn S.X
        (fun z : FeasiblePoint S => spsPhi_sourceDomain S g x β z)) := by
  classical
  rcases hg with ⟨c, a, hgdef⟩
  have hVconv := bregmanOn_right_convexOn_totalized S x
  refine ⟨S.convex_X, ?_⟩
  intro y hy z hz α η hα hη hsum
  have hseg : α • y + η • z ∈ S.X :=
    S.convex_X hy hz hα hη hsum
  have hglinear :
      g (α • y + η • z) = α * g y + η * g z := by
    simp [hgdef, inner_add_right, inner_smul_right]
    ring_nf
    have hc : c = c * α + c * η := by
      calc
        c = c * (α + η) := by rw [hsum]; ring
        _ = c * α + c * η := by ring
    nlinarith
  have hh :
      S.h (α • y + η • z) ≤ α * S.h y + η * S.h z := by
    simpa [smul_eq_mul] using S.convex_h.2 hy hz hα hη hsum
  have hchi :
      S.chi (α • y + η • z) ≤ α * S.chi y + η * S.chi z := by
    simpa [smul_eq_mul] using S.convex_chi.2 hy hz hα hη hsum
  have hV :
      bregmanOn S x ⟨α • y + η • z, hseg⟩ ≤
        α * bregmanOn S x ⟨y, hy⟩ + η * bregmanOn S x ⟨z, hz⟩ := by
    have h := hVconv.2 hy hz hα hη hsum
    simpa [SOptLib.carrierTotalizeOn, hseg, hy, hz, smul_eq_mul] using h
  have hβV := mul_le_mul_of_nonneg_left hV hβ
  simp [SOptLib.carrierTotalizeOn, hseg, hy, hz, spsPhi_sourceDomain]
  nlinarith [hglinear, hh, hchi, hβV, hsum]

/-- Finite Jensen and baseline reduction for the source-domain averaged SPS
iterate.

Aligns with Lan Proposition 8.3 proof step 3, the convexity-of-`Φ` part before
Eq. (8.1.63) is telescoped.  Candidate audit: checked SOptLib
`convexOn_weighted_average_le_weighted_sum` and
`weighted_average_sub_baseline_le_weighted_gap`; their proof patterns match,
but this source-domain helper must rewrite the stored recursive average
`havgClosed` and simplify `carrierTotalizeOn` for the local feasible/prox-core
state objects, so the direct specialization below uses `ConvexOn.map_sum_le`. -/
theorem sps_phi_average_gap_le_weighted_gap_sum
    (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (states : ℕ → Ω → SPSSourceState S) (ω : Ω) (t : PositiveTime)
    (u : FeasiblePoint S)
    (havgClosed :
      (states t.1 ω).avg.1 =
        (psWeightProduct spsP t.1 *
            (1 - psWeightProduct spsP t.1)⁻¹) •
          (Finset.range t.1).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
              (states (i + 1) ω).u.1))
    (hPhiConv :
      ConvexOn ℝ S.X
        (SOptLib.carrierTotalizeOn S.X
          (fun z : FeasiblePoint S => spsPhi_sourceDomain S g x β z))) :
    spsPhi_sourceDomain S g x β (states t.1 ω).avg -
        spsPhi_sourceDomain S g x β u ≤
      psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
        (Finset.range t.1).sum (fun i =>
          (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹ *
            (spsPhi_sourceDomain S g x β
                (proxCorePointToFeasible S (states (i + 1) ω).u) -
              spsPhi_sourceDomain S g x β u)) := by
  classical
  let C : ℝ := psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹
  let w : ℕ → ℝ := fun i =>
    (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹
  let PhiE : E → ℝ :=
    SOptLib.carrierTotalizeOn S.X
      (fun z : FeasiblePoint S => spsPhi_sourceDomain S g x β z)
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
  have hp_mem : ∀ i ∈ Finset.range t.1, (states (i + 1) ω).u.1 ∈ S.X := by
    intro i _hi
    exact (states (i + 1) ω).u.2.1
  have hxbar :
      (states t.1 ω).avg.1 =
        (Finset.range t.1).sum (fun i => (C * w i) • (states (i + 1) ω).u.1) := by
    calc
      (states t.1 ω).avg.1 =
          C • (Finset.range t.1).sum (fun i => w i • (states (i + 1) ω).u.1) := by
            simpa [C, w] using havgClosed
      _ = (Finset.range t.1).sum (fun i => (C * w i) • (states (i + 1) ω).u.1) := by
            rw [Finset.smul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [smul_smul]
  have hJraw :=
    hPhiConv.map_sum_le (t := Finset.range t.1) (w := fun i => C * w i)
      (p := fun i => (states (i + 1) ω).u.1) hq_nonneg hqsum hp_mem
  have hJ :
      spsPhi_sourceDomain S g x β (states t.1 ω).avg ≤
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            spsPhi_sourceDomain S g x β
              (proxCorePointToFeasible S (states (i + 1) ω).u)) := by
    rw [← hxbar] at hJraw
    calc
      spsPhi_sourceDomain S g x β (states t.1 ω).avg =
          PhiE (states t.1 ω).avg.1 := by
            simp [PhiE, SOptLib.carrierTotalizeOn, (states t.1 ω).avg.2]
      _ ≤
          (Finset.range t.1).sum (fun i =>
            (C * w i) • PhiE (states (i + 1) ω).u.1) := hJraw
      _ =
          (Finset.range t.1).sum (fun i =>
            (C * w i) *
              spsPhi_sourceDomain S g x β
                (proxCorePointToFeasible S (states (i + 1) ω).u)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [PhiE, SOptLib.carrierTotalizeOn, hp_mem i hi,
              proxCorePointToFeasible, smul_eq_mul]
  have hbase :
      spsPhi_sourceDomain S g x β (states t.1 ω).avg -
          spsPhi_sourceDomain S g x β u ≤
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            (spsPhi_sourceDomain S g x β
                (proxCorePointToFeasible S (states (i + 1) ω).u) -
              spsPhi_sourceDomain S g x β u)) := by
    calc
      spsPhi_sourceDomain S g x β (states t.1 ω).avg -
          spsPhi_sourceDomain S g x β u
          ≤
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            spsPhi_sourceDomain S g x β
              (proxCorePointToFeasible S (states (i + 1) ω).u)) -
          spsPhi_sourceDomain S g x β u := by
          exact sub_le_sub_right hJ _
      _ =
        (Finset.range t.1).sum (fun i =>
          (C * w i) *
            (spsPhi_sourceDomain S g x β
                (proxCorePointToFeasible S (states (i + 1) ω).u) -
              spsPhi_sourceDomain S g x β u)) := by
          calc
            (Finset.range t.1).sum (fun i =>
                (C * w i) *
                  spsPhi_sourceDomain S g x β
                    (proxCorePointToFeasible S (states (i + 1) ω).u)) -
                spsPhi_sourceDomain S g x β u
                =
              (Finset.range t.1).sum (fun i =>
                (C * w i) *
                  spsPhi_sourceDomain S g x β
                    (proxCorePointToFeasible S (states (i + 1) ω).u)) -
                (Finset.range t.1).sum (fun i => C * w i) *
                  spsPhi_sourceDomain S g x β u := by
                  rw [hqsum]
                  ring
            _ =
              (Finset.range t.1).sum (fun i =>
                (C * w i) *
                  (spsPhi_sourceDomain S g x β
                      (proxCorePointToFeasible S (states (i + 1) ω).u) -
                    spsPhi_sourceDomain S g x β u)) := by
                  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  ring
  calc
    spsPhi_sourceDomain S g x β (states t.1 ω).avg -
        spsPhi_sourceDomain S g x β u
        ≤
      (Finset.range t.1).sum (fun i =>
        (C * w i) *
          (spsPhi_sourceDomain S g x β
              (proxCorePointToFeasible S (states (i + 1) ω).u) -
            spsPhi_sourceDomain S g x β u)) := hbase
    _ =
      C * (Finset.range t.1).sum (fun i =>
        w i *
          (spsPhi_sourceDomain S g x β
              (proxCorePointToFeasible S (states (i + 1) ω).u) -
            spsPhi_sourceDomain S g x β u)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
    _ =
      psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
        (Finset.range t.1).sum (fun i =>
          (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹ *
            (spsPhi_sourceDomain S g x β
                (proxCorePointToFeasible S (states (i + 1) ω).u) -
              spsPhi_sourceDomain S g x β u)) := by
        rfl

/-- Source-domain helper corresponding to Proposition 8.3, the SPS inner bound.

This is the proof frontier matching the textbook statement: every first
argument of the prox-function is a `ProxCorePoint`, so the Section 3.2
`V : X^o × X → R` geometry and strong-convexity field `S.prox_geometry` are
available to the proof.  The remaining proof should follow the source route:
one-step composite prox inequality, strong-convexity absorption, and the
`P_t`/`θ_t` telescope. -/
theorem SPSInnerBound_Proposition8_3_sourceDomainProcess
    (g : E → ℝ) (hg : IsAffineModel g) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g x β sample states)
    (ω : Ω) (t : PositiveTime) (u : FeasiblePoint S) :
    β * (1 - psWeightProduct spsP t.1)⁻¹ *
        bregmanOn S (states t.1 ω).u u +
      (spsPhi_sourceDomain S g x β (states t.1 ω).avg -
        spsPhi_sourceDomain S g x β u) ≤
      β * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S x u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω);
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
                ⟪δ, u.1 - (states i ω).u.1⟫_ℝ)) := by
  classical
  have hstep :
      ∀ n : ℕ,
        let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
        let δ := oracleNoiseAt S ((states n ω).u.1) (sample n ω);
        let next : FeasiblePoint S := proxCorePointToFeasible S (states (n + 1) ω).u;
          spsPhi_sourceDomain S g x β next - spsPhi_sourceDomain S g x β u ≤
            β * spsP ι * bregmanOn S (states n ω).u u -
              β * (1 + spsP ι) * bregmanOn S (states (n + 1) ω).u u +
              ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
              ⟪δ, u.1 - (states n ω).u.1⟫_ℝ := by
    intro n
    exact sps_source_one_step_phi_bound S g hg x β sample states hprocess n ω u
  have havgProduct :
      ∀ n : ℕ,
        let ι : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
          (states (n + 1) ω).avg.1 =
            (1 - psThetaFromProduct spsP ι) • (states n ω).avg.1 +
              psThetaFromProduct spsP ι • (states (n + 1) ω).u.1 := by
    intro n
    exact sps_source_avg_update_product_theta S g x β sample states hprocess n ω
  have havgClosed :
      (states t.1 ω).avg.1 =
        (psWeightProduct spsP t.1 *
            (1 - psWeightProduct spsP t.1)⁻¹) •
          (Finset.range t.1).sum (fun i =>
            ((spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹) •
              (states (i + 1) ω).u.1) :=
    sps_source_avg_eq_weighted_sum S g x β sample states hprocess ω t
  have hPhiConv :
      ConvexOn ℝ S.X
        (SOptLib.carrierTotalizeOn S.X
          (fun z : FeasiblePoint S => spsPhi_sourceDomain S g x β z)) :=
    spsPhi_sourceDomain_convexOn_totalized S g hg x hprocess.1.le
  let C : ℝ := psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹
  let gapSum : ℝ :=
    (Finset.range t.1).sum (fun i =>
      (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹ *
        (spsPhi_sourceDomain S g x β
            (proxCorePointToFeasible S (states (i + 1) ω).u) -
          spsPhi_sourceDomain S g x β u))
  have hJgap :
      spsPhi_sourceDomain S g x β (states t.1 ω).avg -
          spsPhi_sourceDomain S g x β u ≤ C * gapSum := by
    simpa [C, gapSum] using
      sps_phi_average_gap_le_weighted_gap_sum S g x β states ω t u havgClosed hPhiConv
  have hScaledTel :
      β * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S (states t.1 ω).u u +
        C * gapSum ≤
      β * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S x u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω);
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
                ⟪δ, u.1 - (states i ω).u.1⟫_ℝ)) := by
    have hCoeffPrev : ∀ (i : ℕ) (V : ℝ),
        (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹ *
            (β * spsP ⟨i + 1, Nat.succ_pos i⟩ * V) =
          β * (psWeightProduct spsP i)⁻¹ * V := by
      intro i V
      have hp : spsP ⟨i + 1, Nat.succ_pos i⟩ ≠ 0 := by
        unfold spsP
        positivity
      have hP : psWeightProduct spsP i ≠ 0 := by
        rw [psWeightProduct_spsP_eq i]
        positivity
      field_simp [hp, hP]
    have hCoeffNext : ∀ (i : ℕ) (V : ℝ),
        (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹ *
            (β * (1 + spsP ⟨i + 1, Nat.succ_pos i⟩) * V) =
          β * (psWeightProduct spsP (i + 1))⁻¹ * V := by
      intro i V
      have hp : spsP ⟨i + 1, Nat.succ_pos i⟩ ≠ 0 := by
        unfold spsP
        positivity
      have hp1 : 1 + spsP ⟨i + 1, Nat.succ_pos i⟩ ≠ 0 := by
        unfold spsP
        positivity
      have hP : psWeightProduct spsP i ≠ 0 := by
        rw [psWeightProduct_spsP_eq i]
        positivity
      simp [psWeightProduct]
      field_simp [hp, hp1, hP]
    have hWeightedStep : ∀ i : ℕ,
        let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
        let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω);
        let next : FeasiblePoint S := proxCorePointToFeasible S (states (i + 1) ω).u;
        (spsP ι * psWeightProduct spsP i)⁻¹ *
            (spsPhi_sourceDomain S g x β next - spsPhi_sourceDomain S g x β u) ≤
          β * (psWeightProduct spsP i)⁻¹ * bregmanOn S (states i ω).u u -
            β * (psWeightProduct spsP (i + 1))⁻¹ *
              bregmanOn S (states (i + 1) ω).u u +
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
                ⟪δ, u.1 - (states i ω).u.1⟫_ℝ) := by
      intro i
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
      let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω)
      let next : FeasiblePoint S := proxCorePointToFeasible S (states (i + 1) ω).u
      let wi : ℝ := (spsP ι * psWeightProduct spsP i)⁻¹
      have hwi_nonneg : 0 ≤ wi := by
        have hwieq : wi = (i : ℝ) + 2 := by
          simpa [wi, ι] using sps_step_weight_inv_eq i
        rw [hwieq]
        positivity
      have hs := hstep i
      have hmul := mul_le_mul_of_nonneg_left hs hwi_nonneg
      have hprev :
          wi * (β * spsP ι * bregmanOn S (states i ω).u u) =
            β * (psWeightProduct spsP i)⁻¹ *
              bregmanOn S (states i ω).u u := by
        simpa [wi, ι] using hCoeffPrev i (bregmanOn S (states i ω).u u)
      have hnext :
          wi * (β * (1 + spsP ι) * bregmanOn S (states (i + 1) ω).u u) =
            β * (psWeightProduct spsP (i + 1))⁻¹ *
              bregmanOn S (states (i + 1) ω).u u := by
        simpa [wi, ι] using hCoeffNext i (bregmanOn S (states (i + 1) ω).u u)
      dsimp [ι, δ, next, wi] at hmul hprev hnext ⊢
      nlinarith
    let drop : ℕ → ℝ := fun i =>
      β * (psWeightProduct spsP i)⁻¹ * bregmanOn S (states i ω).u u -
        β * (psWeightProduct spsP (i + 1))⁻¹ *
          bregmanOn S (states (i + 1) ω).u u
    let noise : ℕ → ℝ := fun i =>
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
      let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω)
      (spsP ι * psWeightProduct spsP i)⁻¹ *
        (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
          ⟪δ, u.1 - (states i ω).u.1⟫_ℝ)
    have hSumStep :
        gapSum ≤
          (Finset.range t.1).sum (fun i => drop i) +
            (Finset.range t.1).sum (fun i => noise i) := by
      calc
        gapSum =
            (Finset.range t.1).sum (fun i =>
              (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹ *
                (spsPhi_sourceDomain S g x β
                    (proxCorePointToFeasible S (states (i + 1) ω).u) -
                  spsPhi_sourceDomain S g x β u)) := by
              rfl
        _ ≤
            (Finset.range t.1).sum (fun i => drop i + noise i) := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              simpa [drop, noise] using hWeightedStep i
        _ =
            (Finset.range t.1).sum (fun i => drop i) +
              (Finset.range t.1).sum (fun i => noise i) := by
              rw [Finset.sum_add_distrib]
    let A : ℕ → ℝ := fun i =>
      β * (psWeightProduct spsP i)⁻¹ * bregmanOn S (states i ω).u u
    have hDropTel :
        (Finset.range t.1).sum (fun i => drop i) = A 0 - A t.1 := by
      simpa [drop, A] using Finset.sum_range_sub' A t.1
    have hA0 : A 0 = β * bregmanOn S x u := by
      have hinit : states 0 ω = spsSourceInitial S x := hprocess.2.1 ω
      simp [A, hinit, spsSourceInitial, psWeightProduct]
    have hTelUnscaled :
        gapSum ≤
          β * bregmanOn S x u -
            β * (psWeightProduct spsP t.1)⁻¹ *
              bregmanOn S (states t.1 ω).u u +
            (Finset.range t.1).sum (fun i => noise i) := by
      calc
        gapSum ≤
            (Finset.range t.1).sum (fun i => drop i) +
              (Finset.range t.1).sum (fun i => noise i) := hSumStep
        _ = A 0 - A t.1 + (Finset.range t.1).sum (fun i => noise i) := by
            rw [hDropTel]
        _ =
            β * bregmanOn S x u -
              β * (psWeightProduct spsP t.1)⁻¹ *
                bregmanOn S (states t.1 ω).u u +
              (Finset.range t.1).sum (fun i => noise i) := by
            rw [hA0]
    have hTpos : 0 < t.1 := t.2
    have hPpos : 0 < psWeightProduct spsP t.1 := by
      rw [psWeightProduct_spsP_eq t.1]
      positivity
    have hOneSubpos : 0 < 1 - psWeightProduct spsP t.1 :=
      one_sub_psWeightProduct_spsP_pos_of_pos hTpos
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      exact mul_nonneg (le_of_lt hPpos) (inv_nonneg.mpr (le_of_lt hOneSubpos))
    have hScaled := mul_le_mul_of_nonneg_left hTelUnscaled hC_nonneg
    calc
      β * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S (states t.1 ω).u u +
        C * gapSum
          ≤
        β * (1 - psWeightProduct spsP t.1)⁻¹ *
            bregmanOn S (states t.1 ω).u u +
          C *
            (β * bregmanOn S x u -
              β * (psWeightProduct spsP t.1)⁻¹ *
                bregmanOn S (states t.1 ω).u u +
              (Finset.range t.1).sum (fun i => noise i)) := by
            simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using
              add_le_add_left hScaled
                (β * (1 - psWeightProduct spsP t.1)⁻¹ *
                  bregmanOn S (states t.1 ω).u u)
      _ =
        β * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
            bregmanOn S x u +
          psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
            (Finset.range t.1).sum (fun i =>
              let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
              let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω);
              (spsP ι * psWeightProduct spsP i)⁻¹ *
                (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
                  ⟪δ, u.1 - (states i ω).u.1⟫_ℝ)) := by
          calc
            β * (1 - psWeightProduct spsP t.1)⁻¹ *
                bregmanOn S (states t.1 ω).u u +
              C *
                (β * bregmanOn S x u -
                  β * (psWeightProduct spsP t.1)⁻¹ *
                    bregmanOn S (states t.1 ω).u u +
                  (Finset.range t.1).sum (fun i => noise i))
                =
              β * C * bregmanOn S x u +
                C * (Finset.range t.1).sum (fun i => noise i) := by
                dsimp [C]
                field_simp [ne_of_gt hPpos, ne_of_gt hOneSubpos]
                ring
            _ =
              β * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
                  bregmanOn S x u +
                psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
                  (Finset.range t.1).sum (fun i =>
                    let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
                    let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω);
                    (spsP ι * psWeightProduct spsP i)⁻¹ *
                      (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
                        ⟪δ, u.1 - (states i ω).u.1⟫_ℝ)) := by
                dsimp [C, noise]
                rw [show
                  β * (psWeightProduct spsP t.1 *
                      (1 - psWeightProduct spsP t.1)⁻¹) *
                      bregmanOn S x u =
                    β * psWeightProduct spsP t.1 *
                      (1 - psWeightProduct spsP t.1)⁻¹ *
                      bregmanOn S x u by ring]
  calc
    β * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S (states t.1 ω).u u +
        (spsPhi_sourceDomain S g x β (states t.1 ω).avg -
          spsPhi_sourceDomain S g x β u)
        ≤
      β * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S (states t.1 ω).u u +
        C * gapSum := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hJgap
            (β * (1 - psWeightProduct spsP t.1)⁻¹ *
              bregmanOn S (states t.1 ω).u u)
    _ ≤
      β * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S x u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω);
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
                ⟪δ, u.1 - (states i ω).u.1⟫_ℝ)) := hScaledTel

/-- Source-domain specialization of Proposition 8.3 from a relation-form SPS run.

The helper consumes an already supplied `IsSPSProcess_sourceDomain` witness
instead of manufacturing a deterministic prox-core selector.  This keeps the
paper's nonunique argmin update relational and avoids introducing an unproved
global existence theorem for prox-core-valued minimizers. -/
theorem SPSInnerBound_Proposition8_3_formulaExtension
    (g : E → ℝ) (hg : IsAffineModel g) (x : FeasiblePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample)
    (hx : x.1 ∈ proxCore S.X S.proxPotential)
    (states : ℕ → Ω → SPSSourceState S)
    (hprocess : IsSPSProcess_sourceDomain S g ⟨x.1, hx⟩ β sample states)
    (ω : Ω) (t : PositiveTime) (u : FeasiblePoint S) :
    β * (1 - psWeightProduct spsP t.1)⁻¹ *
        bregmanOn S (states t.1 ω).u u +
      (spsPhi_sourceDomain S g ⟨x.1, hx⟩ β (states t.1 ω).avg -
        spsPhi_sourceDomain S g ⟨x.1, hx⟩ β u) ≤
      β * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S ⟨x.1, hx⟩ u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((states i ω).u.1) (sample i ω);
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β * spsP ι) +
                ⟪δ, u.1 - (states i ω).u.1⟫_ℝ)) := by
  simpa using
    SPSInnerBound_Proposition8_3_sourceDomainProcess
      S g hg ⟨x.1, hx⟩ β sample states hprocess ω t u

/-- Reindex the formula-extension transition from raw recursive time `k - 1`
back to the paper's positive outer time `k`.

This is the local bridge that keeps Eq. (8.1.31) talking about the same
`(x_k,\tilde x_k)` pair used by Algorithm 8.1: the center `x_k` is `out.u`,
while the outer reported average is formed from `out.avg = \tilde x_k`. -/
theorem sgsTransition_formulaExtensionSelector_positiveTime
    (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (k : PositiveTime) (st : SGSState S) (ω : Ω) :
    sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma
        (k.1 - 1) st ω =
      let xUnder := outerExtrapolation S gamma k st
      let gk : E → ℝ := fun y => smoothLinearization S xUnder y
      let out := spsOutput S gk (smoothLinearization_isAffineModel S xUnder) st.x
        (positiveBetaSchedule beta hbeta k) (sample k) (T k) ω
      { x := out.u
        xbar :=
          ⟨(1 - gamma k) • st.xbar.1 + gamma k • out.avg.1,
            convexCombination_mem_X S st.xbar out.avg (hgamma k).1 (hgamma k).2⟩ } := by
  cases k with
  | mk n hn =>
      have hk : n - 1 + 1 = n := Nat.sub_add_cancel hn
      simp [sgsTransition_formulaExtensionSelector, positiveBetaSchedule, hk]

/-- Formula-extension helper corresponding to Eq. (8.1.31), the outer one-step
SGS inequality.

This formulation uses the feasible-pair `Φ_k` formula extension induced by the
canonical SGS recursion, avoiding a theorem-head requirement that the current
outer center already belongs to the source prox-core `X^o`.

The lower-bound hypothesis is the paper assumption (8.1.25); the proof of
Eq. (8.1.27), which feeds this one-step estimate, uses
`β_k - Lγ_k ≥ 0` to absorb the smoothness quadratic into the Bregman term. -/
theorem OuterOneStep_8_1_31_formulaExtension (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hlower : outerLowerBoundCondition S beta gamma)
    (k : PositiveTime) (st : SGSState S) (ω : Ω) (u : FeasiblePoint S) :
    let next :=
      sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma (k.1 - 1) st ω
    let xUnder := outerExtrapolation S gamma k st
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let out := spsOutput S gk (smoothLinearization_isAffineModel S xUnder) st.x
      (positiveBetaSchedule beta hbeta k) (sample k) (T k) ω
    objective S next.xbar.1 - objective S u.1 ≤
      (1 - gamma k) * (objective S st.xbar.1 - objective S u.1) +
        gamma k *
      (spsPhiFormulaOnX S gk st.x (beta k) out.avg -
            spsPhiFormulaOnX S gk st.x (beta k) u +
            beta k * bregmanFormulaOnX S st.x u) := by
  classical
  have hlower_k : 0 ≤ beta k - S.lSmooth * gamma k := hlower.2 k
  dsimp only
  rw [sgsTransition_formulaExtensionSelector_positiveTime
    S beta gamma T sample hbeta hgamma k st ω]
  dsimp only
  let xUnder := outerExtrapolation S gamma k st
  let gk : E → ℝ := fun y => smoothLinearization S xUnder y
  let out := spsOutput S gk (smoothLinearization_isAffineModel S xUnder) st.x
    (positiveBetaSchedule beta hbeta k) (sample k) (T k) ω
  have hγ0 : 0 ≤ gamma k := (hgamma k).1
  have hγ1 : gamma k ≤ 1 := (hgamma k).2
  have hxUnder_mem : xUnder ∈ S.X := by
    dsimp [xUnder, outerExtrapolation]
    exact convexCombination_mem_X S st.xbar st.x hγ0 hγ1
  have hBavg :
      (1 / 2 : ℝ) * S.primalNorm (out.avg.1 - st.x.1) ^ 2 ≤
        bregmanFormulaOnX S st.x out.avg := by
    exact bregmanFormulaOnX_lower_bound_from_prox_geometry S st.x out.avg
  have hBu :
      (1 / 2 : ℝ) * S.primalNorm (u.1 - st.x.1) ^ 2 ≤
        bregmanFormulaOnX S st.x u := by
    exact bregmanFormulaOnX_lower_bound_from_prox_geometry S st.x u
  have hhchi :
      S.h ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) +
          S.chi ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) ≤
        (1 - gamma k) * (S.h st.xbar.1 + S.chi st.xbar.1) +
          gamma k * (S.h out.avg.1 + S.chi out.avg.1) := by
    exact outer_h_chi_convex_combination_8_1_28 S st.xbar out.avg hγ0 hγ1
  have hnextBar_mem :
      ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) ∈ S.X := by
    exact convexCombination_mem_X S st.xbar out.avg hγ0 hγ1
  have hf_upper :
      S.f ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) ≤
        smoothLinearization S xUnder
            ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) +
          (S.lSmooth / 2) *
            S.primalNorm
              (((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) - xUnder) ^ 2 := by
    exact smoothLinearization_upper_on_X S hnextBar_mem hxUnder_mem
  have hf_support_prev :
      smoothLinearization S xUnder st.xbar.1 ≤ S.f st.xbar.1 := by
    exact smoothLinearization_support_on_X S st.xbar.2 hxUnder_mem
  have hf_support_u :
      smoothLinearization S xUnder u.1 ≤ S.f u.1 := by
    exact smoothLinearization_support_on_X S u.2 hxUnder_mem
  have hvec :
      ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) - xUnder =
        gamma k • (out.avg.1 - st.x.1) := by
    dsimp [xUnder, outerExtrapolation]
    module
  have hnormsq :
      S.primalNorm
          (((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) - xUnder) ^ 2 =
        (gamma k) ^ 2 * S.primalNorm (out.avg.1 - st.x.1) ^ 2 := by
    rw [hvec]
    simp [map_smul_eq_mul, abs_of_nonneg hγ0]
    ring
  have hlin :
      smoothLinearization S xUnder
          ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) =
        (1 - gamma k) * smoothLinearization S xUnder st.xbar.1 +
          gamma k * smoothLinearization S xUnder out.avg.1 := by
    dsimp [smoothLinearization]
    simp [inner_add_right, inner_sub_right, inner_smul_right]
    ring
  have hquad_le :
      (S.lSmooth / 2) *
          S.primalNorm
            (((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) - xUnder) ^ 2 ≤
        gamma k * (beta k * bregmanFormulaOnX S st.x out.avg) := by
    rw [hnormsq]
    have hLγ_le_β : S.lSmooth * gamma k ≤ beta k := by
      nlinarith [hlower_k]
    have hhalf_nonneg :
        0 ≤ (1 / 2 : ℝ) * S.primalNorm (out.avg.1 - st.x.1) ^ 2 := by
      positivity
    have hβ_nonneg : 0 ≤ beta k := le_of_lt (hbeta k)
    have hprod := mul_le_mul hLγ_le_β hBavg hhalf_nonneg hβ_nonneg
    have hprodγ := mul_le_mul_of_nonneg_left hprod hγ0
    nlinarith
  have hsmooth27 :
      S.f ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) ≤
        (1 - gamma k) * S.f st.xbar.1 +
          gamma k * (smoothLinearization S xUnder out.avg.1 +
            beta k * bregmanFormulaOnX S st.x out.avg) := by
    have hprev_scaled :
        (1 - gamma k) * smoothLinearization S xUnder st.xbar.1 ≤
          (1 - gamma k) * S.f st.xbar.1 := by
      exact mul_le_mul_of_nonneg_left hf_support_prev (sub_nonneg.mpr hγ1)
    calc
      S.f ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1)
          ≤ smoothLinearization S xUnder
              ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) +
            (S.lSmooth / 2) *
              S.primalNorm
                (((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) -
                  xUnder) ^ 2 := hf_upper
      _ = ((1 - gamma k) * smoothLinearization S xUnder st.xbar.1 +
              gamma k * smoothLinearization S xUnder out.avg.1) +
            (S.lSmooth / 2) *
              S.primalNorm
                (((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) -
                  xUnder) ^ 2 := by
            rw [hlin]
      _ ≤ ((1 - gamma k) * S.f st.xbar.1 +
              gamma k * smoothLinearization S xUnder out.avg.1) +
            gamma k * (beta k * bregmanFormulaOnX S st.x out.avg) := by
            nlinarith [hprev_scaled, hquad_le]
      _ = (1 - gamma k) * S.f st.xbar.1 +
            gamma k * (smoothLinearization S xUnder out.avg.1 +
              beta k * bregmanFormulaOnX S st.x out.avg) := by
            ring
  have hobj_avg :
      objective S ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) ≤
        (1 - gamma k) * objective S st.xbar.1 +
          gamma k * spsPhiFormulaOnX S gk st.x (beta k) out.avg := by
    dsimp [objective, SOptLib.compositeObjective, spsPhiFormulaOnX, spsPhi, gk]
    nlinarith [hsmooth27, hhchi]
  have hphi_u :
      spsPhiFormulaOnX S gk st.x (beta k) u ≤
        objective S u.1 + beta k * bregmanFormulaOnX S st.x u := by
    dsimp [objective, SOptLib.compositeObjective, spsPhiFormulaOnX, spsPhi, gk]
    nlinarith [hf_support_u]
  have hmain :
      objective S ((1 - gamma k) • st.xbar.1 + gamma k • out.avg.1) -
          objective S u.1 ≤
        (1 - gamma k) * (objective S st.xbar.1 - objective S u.1) +
          gamma k *
            (spsPhiFormulaOnX S gk st.x (beta k) out.avg -
              spsPhiFormulaOnX S gk st.x (beta k) u +
              beta k * bregmanFormulaOnX S st.x u) := by
    have hphi_scaled := mul_le_mul_of_nonneg_left hphi_u hγ0
    nlinarith [hobj_avg, hphi_scaled]
  simpa [out, gk, xUnder] using hmain

/-- Formula-extension helper corresponding to Eq. (8.1.65), Proposition 8.3
specialized to the `k`-th SGS inner call.

The source proof applies Proposition 8.3 with `t = T_k`, so this helper takes
`T` as a positive `InnerBudget` and consumes the relation-form source-domain
inner process used by the outer transition. -/
theorem SGSInnerOuterBound_8_1_65_formulaExtension
    (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → InnerBudget) (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) (st : SGSState S)
    (hx : st.x.1 ∈ proxCore S.X S.proxPotential)
    (inner : ℕ → Ω → SPSSourceState S)
    (hinner :
      IsSPSProcess_sourceDomain S
        (fun y => smoothLinearization S (outerExtrapolation S gamma k st) y)
        ⟨st.x.1, hx⟩ (beta k) (sample k) inner)
    (ω : Ω) (u : FeasiblePoint S) :
    let xUnder := outerExtrapolation S gamma k st
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let t : PositiveTime := T k
    beta k * (1 - psWeightProduct spsP t.1)⁻¹ *
        bregmanOn S (inner t.1 ω).u u +
      (spsPhi_sourceDomain S gk ⟨st.x.1, hx⟩ (beta k) (inner t.1 ω).avg -
        spsPhi_sourceDomain S gk ⟨st.x.1, hx⟩ (beta k) u) ≤
      beta k * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanOn S ⟨st.x.1, hx⟩ u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner i ω).u.1) (sample k i ω);
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta k * spsP ι) +
                ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ)) := by
  dsimp
  simpa using
    SPSInnerBound_Proposition8_3_formulaExtension
      S
      (fun y => smoothLinearization S (outerExtrapolation S gamma k st) y)
      (smoothLinearization_isAffineModel S (outerExtrapolation S gamma k st))
      st.x (beta k) (sample k) hx inner hinner ω (T k) u

/-- Scalar Young relaxation used in the final displayed form of Eq. (8.1.69).

Candidate audit: considered SOptLib
`scaled_linear_inner_quadratic_le_square_over_denominator`, but that lemma
packages the earlier displacement completion-square step, while Eq. (8.1.69)
needs the literal post-telescope replacement
`(M + d)^2 / (2 β p) ≤ (M^2 + d^2) / (β p)`.  The telescope candidate
`sum_weighted_sub_mul_le_first_sub_tail` is orthogonal: it handles the Bregman
drop sum, not this pointwise scalar relaxation. -/
theorem sps_noise_square_relaxation {β p M d : ℝ}
    (hβ : 0 < β) (hp : 0 < p) (_hM : 0 ≤ M) (_hd : 0 ≤ d) :
    ((M + d) ^ 2) / (2 * β * p) ≤ (M ^ 2 + d ^ 2) / (β * p) := by
  have hden : 0 < β * p := mul_pos hβ hp
  have hnum : (M + d) ^ 2 ≤ 2 * (M ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (M - d)]
  calc
    ((M + d) ^ 2) / (2 * β * p)
        = ((M + d) ^ 2) / (2 * (β * p)) := by ring
    _ ≤ (2 * (M ^ 2 + d ^ 2)) / (2 * (β * p)) := by
      exact div_le_div_of_nonneg_right hnum (by positivity)
    _ = (M ^ 2 + d ^ 2) / (β * p) := by
      field_simp [ne_of_gt hden]

/-- Fixed-path selected SGS specialization of Proposition 8.3.

The generated inner process in `sgsInnerProcess_formulaExtensionSelector`
depends on the outer sample path.  Proposition 8.3 is deterministic once an
outer path `ω` has fixed the center and affine model, so this bridge constructs
that fixed-`ω` SPS process and applies the proved formula-extension theorem
directly.  The remaining integrability envelope for selected successor queries
can use this pathwise bound together with finite-sum integrability closure,
rather than re-entering the all-feasible boundary-gradient route. -/
theorem selected_sgs_inner_Proposition8_3_formulaOnXProcess
    (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (sample : PositiveTime → ℕ → Ω → Sample)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (κ : PositiveTime) (ω : Ω) (t : PositiveTime) (u : FeasiblePoint S) :
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let inner :=
      spsProcess S gk (smoothLinearization_isAffineModel S xUnder)
        outerPrev.x ⟨beta κ, hbeta κ⟩ (sample κ)
    beta κ * (1 - psWeightProduct spsP t.1)⁻¹ *
        bregmanFormulaOnX S (inner t.1 ω).u u +
      (spsPhiFormulaOnX S gk outerPrev.x (beta κ) (inner t.1 ω).avg -
        spsPhiFormulaOnX S gk outerPrev.x (beta κ) u) ≤
      beta κ * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanFormulaOnX S outerPrev.x u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω)
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ)) := by
  classical
  let outerPrev :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
      (κ.1 - 1) ω
  let xUnder := outerExtrapolation S gamma κ outerPrev
  let gk : E → ℝ := fun y => smoothLinearization S xUnder y
  let hgk : IsAffineModel gk := smoothLinearization_isAffineModel S xUnder
  let inner := spsProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩ (sample κ)
  have hprocess : IsSPSProcess S gk outerPrev.x (beta κ) (sample κ) inner := by
    simpa [inner, hgk] using
      spsProcess_isSPSProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩ (sample κ)
  simpa [outerPrev, xUnder, gk, hgk, inner] using
    SPSInnerBound_Proposition8_3_formulaOnXProcess S gk hgk outerPrev.x
      (beta κ) (sample κ) inner hprocess ω t u

/-- Proposition 8.3 rewritten directly over the selected SGS inner-process
family.

This is the source-matched consumer needed by the successor-integrability
frontier: the source theorem controls the terminal Bregman term together with
the averaged inner output `\tilde u_t`, not a reverse gap at the terminal
iterate `u_t`. -/
theorem selected_sgs_inner_Proposition8_3_selectedProcess
    (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (sample : PositiveTime → ℕ → Ω → Sample)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (κ : PositiveTime) (ω : Ω) (t : PositiveTime) (u : FeasiblePoint S) :
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let inner :=
      sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample κ
    beta κ * (1 - psWeightProduct spsP t.1)⁻¹ *
        bregmanFormulaOnX S (inner t.1 ω).u u +
      (spsPhiFormulaOnX S gk outerPrev.x (beta κ) (inner t.1 ω).avg -
        spsPhiFormulaOnX S gk outerPrev.x (beta κ) u) ≤
      beta κ * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanFormulaOnX S outerPrev.x u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω)
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ)) := by
  classical
  simpa [sgsInnerProcess_formulaExtensionSelector] using
    selected_sgs_inner_Proposition8_3_formulaOnXProcess
      (S := S) x0 beta gamma T sample hbeta hgamma κ ω t u

/-- Proposition 8.3 at the selected successor query `u_{j+1}`.

The first Bregman argument is written exactly as the generated oracle query used
by the integrability induction, while the Phi term remains the source's averaged
inner output.  This avoids the earlier unsupported handoff that asked
Proposition 8.3 for a terminal-iterate reverse-Phi envelope. -/
theorem selected_sgs_inner_Proposition8_3_successor_query_formulaOnXProcess
    (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (sample : PositiveTime → ℕ → Ω → Sample)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T sample k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ) (ω : Ω) (u : FeasiblePoint S) :
    let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    let gk : E → ℝ := fun y => smoothLinearization S xUnder y
    let inner :=
      sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample κ
    beta κ * (1 - psWeightProduct spsP t.1)⁻¹ *
        bregmanFormulaOnX S
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T sample κ (j + 1) ω,
            hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) u +
      (spsPhiFormulaOnX S gk outerPrev.x (beta κ) (inner t.1 ω).avg -
        spsPhiFormulaOnX S gk outerPrev.x (beta κ) u) ≤
      beta κ * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          bregmanFormulaOnX S outerPrev.x u +
        psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
          (Finset.range t.1).sum (fun i =>
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner i ω).u.1) (sample κ i ω)
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                ⟪δ, u.1 - (inner i ω).u.1⟫_ℝ)) := by
  classical
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let inner :=
    sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample κ
  have hq :
      (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T sample κ (j + 1) ω,
        hquery_mem κ (j + 1) ω⟩ : FeasiblePoint S) =
        (inner t.1 ω).u := by
    ext
    simp [inner, t, sgsOracleQuery]
  simpa [t, inner, hq] using
    selected_sgs_inner_Proposition8_3_selectedProcess
      (S := S) x0 beta gamma T sample hbeta hgamma κ ω t u

/-- Integrability of the finite stochastic RHS in the selected SGS
Proposition 8.3 bound.

This is the finite-window part of Eq. (8.1.63): each summand is controlled by
the generated SFO variance hypothesis, the previous-query Bregman integrability
window, and finite-sum integrability closure.  It is deliberately declared
before the selected-query successor integrability theorem so that the active
frontier consumes a named source bridge rather than a local anonymous leaf. -/
theorem selected_sgs_inner_average_rhs_integrable
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
    (hvar :
      generatedSFOVariance S law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (κ : PositiveTime) (j : ℕ)
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
    Integrable RHSavg law.P := by
  classical
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let outerBreg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    bregmanFormulaOnX S outerPrev.x x
  let rhsSum : Ω → ℝ := fun ω =>
    let inner :=
      sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
    (Finset.range t.1).sum (fun i =>
      let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
      let δ := oracleNoiseAt S ((inner i ω).u.1) (law.sample κ i ω)
      (spsP ι * psWeightProduct spsP i)⁻¹ *
        (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
          ⟪δ, x.1 - (inner i ω).u.1⟫_ℝ))
  have houterBreg_int : Integrable outerBreg law.P := by
    have hzero := hprev_window 0 (Nat.succ_pos j)
    refine hzero.congr ?_
    filter_upwards with ω
    have hq0 :=
      sgsOracleQuery_zero_eq_outer_center
        (S := S) x0 beta gamma T law.sample hbeta hgamma κ ω
    dsimp [outerBreg]
    apply congrArg (fun y : FeasiblePoint S => bregmanFormulaOnX S y x)
    apply Subtype.ext
    exact hq0
  have hterm_int :
      ∀ i ∈ Finset.range t.1,
        Integrable
          (fun ω =>
            let inner :=
              sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                law.sample κ
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner i ω).u.1) (law.sample κ i ω)
            (spsP ι * psWeightProduct spsP i)⁻¹ *
              (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
                ⟪δ, x.1 - (inner i ω).u.1⟫_ℝ))
          law.P := by
    intro i hi
    have hi_lt : i < j + 1 := by
      simpa [t] using Finset.mem_range.mp hi
    have hbreg_i :
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              x)
          law.P :=
      hprev_window i hi_lt
    have hprev_l2_query :
        Integrable
          (fun ω =>
            S.primalNorm
              (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω) ^ 2)
          law.P :=
      query_sq_integrable_of_bregman_integrable
        (S := S) law.P x
        (fun ω =>
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
            hquery_mem κ i ω⟩ : FeasiblePoint S))
        (hquery_meas κ i) hbreg_i
    have hdual_sq :
        Integrable
          (fun ω =>
            dualNorm S
                (oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                  (law.sample κ i ω)) ^ 2)
          law.P := by
      simpa using
        generatedSFOVariance_integrable_obligation
          (S := S) law.P law.sample
          (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample) hvar κ i
    have hinner_aemeas_query :
        AEStronglyMeasurable
          (fun ω =>
            ⟪oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                (law.sample κ i ω),
              x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ)
          law.P := by
      have hkernel :
          Measurable (fun p : FeasiblePoint S × Sample =>
            ⟪x.1 - p.1.1, oracleNoiseAt S p.1.1 p.2⟫_ℝ) :=
        oracle_residual_target_inner_measurable_of_residual_measurable
          (S := S) x law.oracle_residual_measurable
      have hpair :
          Measurable (fun ω =>
            ((⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S),
              law.sample κ i ω)) :=
        (hquery_meas κ i).prod (law.sample_measurable κ i)
      have hscalar :
          Measurable
            (fun ω =>
              ⟪x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                  (law.sample κ i ω)⟫_ℝ) := by
        simpa using hkernel.comp hpair
      simpa [real_inner_comm] using hscalar.aestronglyMeasurable
    have hinner_int_query :
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                (law.sample κ i ω),
              x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ)
          law.P :=
      generated_target_inner_integrable_of_primal_displacement_l2
        (S := S) law.P law.sample
        (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample)
        x κ i hdual_sq hprev_l2_query hinner_aemeas_query
    have hdual_l1 :
        Integrable
          (fun ω =>
            dualNorm S
              (oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                (law.sample κ i ω)))
          law.P := by
      have hnonneg :
          ∀ᵐ ω ∂law.P,
            0 ≤
              dualNorm S
                (oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                  (law.sample κ i ω)) := by
        exact Filter.Eventually.of_forall (fun ω => by
          simpa [dualNorm] using
            SOptLib.canonicalDualNorm_nonneg S.primalNorm
              (oracleNoiseAt S
                (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                (law.sample κ i ω)))
      exact
        (integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
          (μ := law.P) hdual_sq hnonneg (C :=
            ∫ ω,
              dualNorm S
                (oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                  (law.sample κ i ω)) ^ 2 ∂law.P)
          le_rfl).1
    have hshifted_dual_sq :
        Integrable
          (fun ω =>
            (S.mGrowth +
                dualNorm S
                  (oracleNoiseAt S
                    (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                    (law.sample κ i ω))) ^ 2)
          law.P := by
      have hpoly :
          Integrable
            (fun ω =>
              S.mGrowth ^ 2 +
                (2 * S.mGrowth) *
                  dualNorm S
                    (oracleNoiseAt S
                      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                      (law.sample κ i ω)) +
                dualNorm S
                  (oracleNoiseAt S
                    (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                    (law.sample κ i ω)) ^ 2)
            law.P :=
        ((integrable_const (c := S.mGrowth ^ 2)).add
          (hdual_l1.const_mul (2 * S.mGrowth))).add hdual_sq
      refine hpoly.congr ?_
      filter_upwards with ω
      ring
    have hstoch_int_query :
        Integrable
          (fun ω =>
            ((S.mGrowth +
                dualNorm S
                  (oracleNoiseAt S
                    (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                    (law.sample κ i ω))) ^ 2) /
                (2 * beta κ * spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)) +
              ⟪oracleNoiseAt S
                  (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                  (law.sample κ i ω),
                x.1 -
                  sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω⟫_ℝ)
          law.P := by
      have hscaled :
          Integrable
            (fun ω =>
              ((S.mGrowth +
                  dualNorm S
                    (oracleNoiseAt S
                      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω)
                      (law.sample κ i ω))) ^ 2) /
                  (2 * beta κ * spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)))
            law.P := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          hshifted_dual_sq.const_mul
            ((2 * beta κ * spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime))⁻¹)
      exact hscaled.add hinner_int_query
    have hstoch_int_inner :
        Integrable
          (fun ω =>
            let inner :=
              sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                law.sample κ
            let ι : PositiveTime := ⟨i + 1, Nat.succ_pos i⟩;
            let δ := oracleNoiseAt S ((inner i ω).u.1) (law.sample κ i ω)
            (((S.mGrowth + dualNorm S δ) ^ 2) / (2 * beta κ * spsP ι) +
              ⟪δ, x.1 - (inner i ω).u.1⟫_ℝ))
          law.P := by
      simpa [sgsOracleQuery] using hstoch_int_query
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hstoch_int_inner.const_mul
        ((spsP (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) *
            psWeightProduct spsP i)⁻¹)
  have hrsSum_int : Integrable rhsSum law.P := by
    refine integrable_finset_sum (Finset.range t.1) ?_
    intro i hi
    simpa [rhsSum] using hterm_int i hi
  have htotal :
      Integrable
        (fun ω =>
          beta κ * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
              outerBreg ω +
            psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹ *
              rhsSum ω)
        law.P :=
    (houterBreg_int.const_mul
        (beta κ * psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹)).add
      (hrsSum_int.const_mul
        (psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹))
  refine htotal.congr (Filter.Eventually.of_forall ?_)
  intro ω
  simp [outerBreg, rhsSum, t, mul_assoc]

noncomputable def selected_sgs_inner_average_phi_reverse_gap_splitCgap
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ) (squareCoeff χresidual : ℝ) : Ω → ℝ := fun ω =>
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let outerPrev :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
      (κ.1 - 1) ω
  let xUnder := outerExtrapolation S gamma κ outerPrev
  let inner :=
    sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample κ
  squareCoeff *
      (1 + bregmanFormulaOnX S outerPrev.x x +
        S.primalNorm (x.1 - xUnder) ^ 2 +
        (Finset.range j).sum (fun i =>
          bregmanFormulaOnX S
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
              hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S)
            x)) +
    |beta κ * bregmanFormulaOnX S outerPrev.x x + χresidual| +
    (Finset.range j).sum (fun i =>
      (propCoeff / (4 * (j + 1 : ℝ))) *
        bregmanFormulaOnX S
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
            hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S)
          x)

/-- Source-form decomposition of the reverse `Phi` gap at a selected averaged
point.

This is the algebraic part of the split requested by the reconstruct audit.  It
uses the source subgradient of `h`, the affine minorant of `chi`, and the
nonnegativity of the center Bregman term to isolate exactly one fixed affine
slope
`sourceSmoothGradient S x + S.hSubgradient x + χb`.  The remaining smooth
residual is the term handled by the separate transport lemma. -/
theorem spsPhiFormulaOnX_reverse_gap_decompose_fixed_slope
    (x center avg : FeasiblePoint S) (xUnder : E) {β : ℝ}
    (hβ_nonneg : 0 ≤ β) (χa : ℝ) (χb : E)
    (hχminor : ∀ y : {x : E // x ∈ S.X}, χa + ⟪χb, y.1⟫_ℝ ≤ S.chi y.1) :
    spsPhiFormulaOnX S (smoothLinearization S xUnder) center β x -
        spsPhiFormulaOnX S (smoothLinearization S xUnder) center β avg ≤
      (smoothLinearization S xUnder x.1 -
          smoothLinearization S xUnder avg.1 -
          ⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ) +
        ⟪sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb, x.1 - avg.1⟫_ℝ +
          (β * bregmanFormulaOnX S center x +
            (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)) := by
  classical
  have hh_support :
      S.h avg.1 ≥
        S.h x.1 + ⟪S.hSubgradient x.1, avg.1 - x.1⟫_ℝ := by
    have hmem := (setup_hSubgradientMem S) x.1 x.2
    exact (SOptLib.mem_carrierSubdifferential_iff.mp hmem) avg
  have hh_gap :
      S.h x.1 - S.h avg.1 ≤
        ⟪S.hSubgradient x.1, x.1 - avg.1⟫_ℝ := by
    have hinner :
        ⟪S.hSubgradient x.1, avg.1 - x.1⟫_ℝ =
          -⟪S.hSubgradient x.1, x.1 - avg.1⟫_ℝ := by
      simp [inner_sub_right]
    nlinarith
  have hχavg : χa + ⟪χb, avg.1⟫_ℝ ≤ S.chi avg.1 := hχminor avg
  have hχ_gap :
      S.chi x.1 - S.chi avg.1 ≤
        (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ) +
          ⟪χb, x.1 - avg.1⟫_ℝ := by
    have hinner :
        ⟪χb, x.1 - avg.1⟫_ℝ =
          ⟪χb, x.1⟫_ℝ - ⟪χb, avg.1⟫_ℝ := by
      simp [inner_sub_right]
    nlinarith
  have hVcenter_avg_nonneg : 0 ≤ bregmanFormulaOnX S center avg := by
    have hlower := bregmanFormulaOnX_lower_bound_from_prox_geometry S center avg
    nlinarith [sq_nonneg (S.primalNorm (avg.1 - center.1))]
  have hβ_gap :
      β * bregmanFormulaOnX S center x -
          β * bregmanFormulaOnX S center avg ≤
        β * bregmanFormulaOnX S center x := by
    nlinarith [hβ_nonneg, hVcenter_avg_nonneg]
  have hsmooth_split :
      smoothLinearization S xUnder x.1 -
          smoothLinearization S xUnder avg.1 =
        (smoothLinearization S xUnder x.1 -
            smoothLinearization S xUnder avg.1 -
            ⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ) +
          ⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ := by
    ring
  have hfixed_sum :
      ⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ +
          ⟪S.hSubgradient x.1, x.1 - avg.1⟫_ℝ +
          ⟪χb, x.1 - avg.1⟫_ℝ =
        ⟪sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb,
          x.1 - avg.1⟫_ℝ := by
    simp [inner_add_left]
  unfold spsPhiFormulaOnX spsPhi
  nlinarith [hh_gap, hχ_gap, hβ_gap, hsmooth_split, hfixed_sum]

/-- Smooth residual bridge for the selected reverse-gap split.

Aligns with Lan Eq. (8.1.2) and the convex support step used around
Eq. (8.1.30): `smoothLinearization_support_on_X` controls the two supporting
hyperplanes and `smoothLinearization_upper_on_X` supplies the only quadratic
term.  Candidate audit: searched target/SOptLib smooth-residual and finite
Jensen helpers; the reusable ingredients are exactly the two local source
linearization bridges rather than a prepackaged reverse-residual theorem. -/
theorem smooth_linearization_reverse_residual_le_under_avg_square
    (x avg : FeasiblePoint S) (xUnder : E) (hxUnder : xUnder ∈ S.X) :
    smoothLinearization S xUnder x.1 - smoothLinearization S xUnder avg.1 -
        ⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ ≤
      (S.lSmooth / 2) * S.primalNorm (avg.1 - xUnder) ^ 2 := by
  have hsupport_under :
      smoothLinearization S xUnder x.1 ≤ S.f x.1 :=
    smoothLinearization_support_on_X S x.2 hxUnder
  have hsupport_x :
      smoothLinearization S x.1 avg.1 ≤ S.f avg.1 :=
    smoothLinearization_support_on_X S avg.2 x.2
  have hupper_avg :
      S.f avg.1 ≤
        smoothLinearization S xUnder avg.1 +
          (S.lSmooth / 2) * S.primalNorm (avg.1 - xUnder) ^ 2 :=
    smoothLinearization_upper_on_X S avg.2 hxUnder
  have hsupport_gap :
      S.f x.1 - S.f avg.1 -
          ⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ ≤ 0 := by
    have hinner :
        ⟪sourceSmoothGradient S x.1, avg.1 - x.1⟫_ℝ =
          -⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ := by
      simp [inner_sub_right]
    have hsupport_x' :
        S.f x.1 - ⟪sourceSmoothGradient S x.1, x.1 - avg.1⟫_ℝ ≤
          S.f avg.1 := by
      simpa [smoothLinearization, hinner] using hsupport_x
    nlinarith
  nlinarith [hsupport_under, hupper_avg, hsupport_gap]

/-- Jensen control for a finite weighted average in the paper primal seminorm.

This is Lean-side seminorm infrastructure for the SPS weighted average.  No
SOptLib match: searched `seminorm convex square weighted sum`,
`primalNorm average square bregman`, and the pre-searched weighted-variance
candidates; available SOptLib variance lemmas use the ambient Hilbert norm,
while this bound must keep the paper's arbitrary primal seminorm. -/
theorem primalNorm_sq_weighted_average_sub_le_sum
    {ι : Type*} (x : FeasiblePoint S) (s : Finset ι) (q : ι → ℝ) (a : ι → E)
    (μ : E) (hq_nonneg : ∀ i ∈ s, 0 ≤ q i)
    (hqsum : (Finset.sum s fun i => q i) = 1)
    (hμ : μ = Finset.sum s (fun i => q i • a i)) :
    S.primalNorm (x.1 - μ) ^ 2 ≤
      Finset.sum s (fun i => q i * S.primalNorm (x.1 - a i) ^ 2) := by
  classical
  let f : E → ℝ := fun y => S.primalNorm (x.1 - y) ^ 2
  have hf_conv : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro y _hy z _hz α η hα hη hsum
    let py : ℝ := S.primalNorm (x.1 - y)
    let pz : ℝ := S.primalNorm (x.1 - z)
    have hvec :
        x.1 - (α • y + η • z) =
          α • (x.1 - y) + η • (x.1 - z) := by
      calc
        x.1 - (α • y + η • z)
            = (α + η) • x.1 - (α • y + η • z) := by
                rw [hsum, one_smul]
        _ = α • (x.1 - y) + η • (x.1 - z) := by
                module
    have hnorm :
        S.primalNorm (x.1 - (α • y + η • z)) ≤ α * py + η * pz := by
      calc
        S.primalNorm (x.1 - (α • y + η • z))
            = S.primalNorm (α • (x.1 - y) + η • (x.1 - z)) := by rw [hvec]
        _ ≤ S.primalNorm (α • (x.1 - y)) +
              S.primalNorm (η • (x.1 - z)) :=
            map_add_le_add S.primalNorm _ _
        _ = |α| * py + |η| * pz := by
            simp [py, pz, map_smul_eq_mul]
        _ = α * py + η * pz := by
            rw [abs_of_nonneg hα, abs_of_nonneg hη]
    have hleft_nonneg : 0 ≤ S.primalNorm (x.1 - (α • y + η • z)) :=
      apply_nonneg S.primalNorm _
    have hright_nonneg : 0 ≤ α * py + η * pz := by
      have hpy : 0 ≤ py := by dsimp [py]; exact apply_nonneg S.primalNorm _
      have hpz : 0 ≤ pz := by dsimp [pz]; exact apply_nonneg S.primalNorm _
      nlinarith
    have hsquare :
        S.primalNorm (x.1 - (α • y + η • z)) ^ 2 ≤
          (α * py + η * pz) ^ 2 := by
      nlinarith [hnorm, hleft_nonneg, hright_nonneg,
        sq_nonneg ((α * py + η * pz) -
          S.primalNorm (x.1 - (α • y + η • z)))]
    have hweighted_square :
        (α * py + η * pz) ^ 2 ≤ α * py ^ 2 + η * pz ^ 2 := by
      have hpy : 0 ≤ py := by dsimp [py]; exact apply_nonneg S.primalNorm _
      have hpz : 0 ≤ pz := by dsimp [pz]; exact apply_nonneg S.primalNorm _
      have hsq : 0 ≤ α * η * (py - pz) ^ 2 := by
        exact mul_nonneg (mul_nonneg hα hη) (sq_nonneg _)
      nlinarith
    exact hsquare.trans hweighted_square
  have hJ :=
    hf_conv.map_sum_le (t := s) (w := q) (p := a) hq_nonneg hqsum
      (by intro i hi; trivial)
  rw [← hμ] at hJ
  simpa [f, smul_eq_mul] using hJ

/-- Triangle-square control for the paper primal seminorm.

This is route-local scalar/seminorm infrastructure used to move the smooth
residual from the under-point displacement to the comparator-centered budgets
already present in the split Cgap. -/
theorem primalNorm_sub_sq_le_two_sq_add (a b c : E) :
    S.primalNorm (a - c) ^ 2 ≤
      2 * (S.primalNorm (b - a) ^ 2 + S.primalNorm (b - c) ^ 2) := by
  have hvec : a - c = -(b - a) + (b - c) := by
    abel
  have hnorm :
      S.primalNorm (a - c) ≤ S.primalNorm (b - a) + S.primalNorm (b - c) := by
    calc
      S.primalNorm (a - c)
          = S.primalNorm (-(b - a) + (b - c)) := by rw [hvec]
      _ ≤ S.primalNorm (-(b - a)) + S.primalNorm (b - c) :=
          map_add_le_add S.primalNorm _ _
      _ = S.primalNorm (b - a) + S.primalNorm (b - c) := by
          rw [map_neg_eq_map]
  have hleft_nonneg : 0 ≤ S.primalNorm (a - c) := apply_nonneg S.primalNorm _
  have hright_nonneg : 0 ≤ S.primalNorm (b - a) + S.primalNorm (b - c) := by
    nlinarith [apply_nonneg S.primalNorm (b - a),
      apply_nonneg S.primalNorm (b - c)]
  have hsquare :
      S.primalNorm (a - c) ^ 2 ≤
        (S.primalNorm (b - a) + S.primalNorm (b - c)) ^ 2 := by
    nlinarith [hnorm, hleft_nonneg, hright_nonneg,
      sq_nonneg ((S.primalNorm (b - a) + S.primalNorm (b - c)) -
        S.primalNorm (a - c))]
  have hab :
      (S.primalNorm (b - a) + S.primalNorm (b - c)) ^ 2 ≤
        2 * (S.primalNorm (b - a) ^ 2 + S.primalNorm (b - c) ^ 2) := by
    nlinarith [sq_nonneg (S.primalNorm (b - a) - S.primalNorm (b - c))]
  exact hsquare.trans hab

/-- The `xUnder` square term is an affine-update L2 consequence of the outer
state L2 terms.

This is the named infrastructure leaf required by the split Cgap route.  It
does not assume a new paper fact: it factors the obligation through the
previously proved affine-update integrability helper, making explicit that the
caller still needs an outer `xbar` L2 invariant in addition to the selected
query/window L2 facts. -/
theorem selected_sgs_inner_xUnder_sq_integrable_of_outer_state_sq
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (x : FeasiblePoint S)
    (gamma : PositiveTime → ℝ) (κ : PositiveTime)
    (outerPrev : Ω → SGSState S)
    (houter_x_meas : AEStronglyMeasurable (fun ω => (outerPrev ω).x.1) P)
    (houter_xbar_meas : AEStronglyMeasurable (fun ω => (outerPrev ω).xbar.1) P)
    (houter_x_sq :
      Integrable (fun ω => S.primalNorm (x.1 - (outerPrev ω).x.1) ^ 2) P)
    (houter_xbar_sq :
      Integrable (fun ω => S.primalNorm (x.1 - (outerPrev ω).xbar.1) ^ 2) P) :
    Integrable
      (fun ω =>
        S.primalNorm (x.1 - outerExtrapolation S gamma κ (outerPrev ω)) ^ 2) P := by
  simpa [outerExtrapolation] using
    primalNorm_sq_integrable_affine_update
      (S := S) P x
      (fun ω => (outerPrev ω).xbar.1)
      (fun ω => (outerPrev ω).x.1)
      (gamma κ)
      houter_xbar_meas houter_x_meas
      houter_xbar_sq houter_x_sq

/-- The previous outer center has Bregman integrability from the current inner
window.

This is the `i = 0` bridge for the selected SGS recursion:
`u_{k,0}=x_{k-1}`.  It keeps the outer-center term in the reverse-gap Cgap tied
to the same finite Proposition 8.3 window used by the successor transfer. -/
theorem selected_sgs_outer_prev_center_bregman_integrable_of_window
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ)
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
        let outerPrev :=
          sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
            (κ.1 - 1) ω
        bregmanFormulaOnX S outerPrev.x x)
      law.P := by
  classical
  have hzero := hprev_window 0 (Nat.succ_pos j)
  refine hzero.congr ?_
  filter_upwards with ω
  have hq0 :=
    sgsOracleQuery_zero_eq_outer_center
      (S := S) x0 beta gamma T law.sample hbeta hgamma κ ω
  dsimp
  apply congrArg (fun y : FeasiblePoint S => bregmanFormulaOnX S y x)
  apply Subtype.ext
  exact hq0

/-- The previous outer center has the centered L2 integrability needed for
outer-extrapolation transport.

This is only the coercive consequence of the previous lemma and
`bregmanFormulaOnX_lower_bound_from_prox_geometry`; it does not introduce a new
source assumption. -/
theorem selected_sgs_outer_prev_center_sq_integrable_of_window
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
    (κ : PositiveTime) (j : ℕ)
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
        let outerPrev :=
          sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
            (κ.1 - 1) ω
        S.primalNorm (x.1 - outerPrev.x.1) ^ 2)
      law.P := by
  classical
  have hzero_breg := hprev_window 0 (Nat.succ_pos j)
  have hzero_sq :
      Integrable
        (fun ω =>
          S.primalNorm
            (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω) ^ 2)
        law.P :=
    query_sq_integrable_of_bregman_integrable
      (S := S) law.P x
      (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω,
          hquery_mem κ 0 ω⟩ : FeasiblePoint S))
      (hquery_meas κ 0) hzero_breg
  refine hzero_sq.congr ?_
  filter_upwards with ω
  have hq0 :=
    sgsOracleQuery_zero_eq_outer_center
      (S := S) x0 beta gamma T law.sample hbeta hgamma κ ω
  dsimp
  rw [hq0]

/-- Measurability of the selected inner SPS running average.

This is the measurable half of the selected-query regularity package: it is
derived from the recursive SPS average update and the existing generated-query
measurability supplied by the SFO independence hypothesis. -/
theorem selected_sgs_inner_avg_aestronglyMeasurable_of_query_meas
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω,
          hquery_mem k i ω⟩ : FeasiblePoint S)))
    (κ : PositiveTime) :
    ∀ m : ℕ,
      AEStronglyMeasurable
        (fun ω =>
          (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
            law.sample κ m ω).avg.1) law.P := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  intro m
  induction m with
  | zero =>
      have hq0 :
          AEStronglyMeasurable
            (fun ω => sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω)
            law.P :=
        (measurable_subtype_coe.comp (hquery_meas κ 0)).aestronglyMeasurable
      refine hq0.congr (Filter.Eventually.of_forall ?_)
      intro ω
      simp [sgsOracleQuery, sgsInnerProcess_formulaExtensionSelector, spsProcess,
        SOptLib.recursiveIterateProcess, spsInitial]
  | succ m ihm =>
      have hnext :
          AEStronglyMeasurable
            (fun ω =>
              sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (m + 1) ω)
            law.P :=
        (measurable_subtype_coe.comp (hquery_meas κ (m + 1))).aestronglyMeasurable
      have hcombo :
          AEStronglyMeasurable
            (fun ω =>
              (1 - spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime)) •
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample κ m ω).avg.1 +
                spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime) •
                  sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (m + 1) ω)
            law.P :=
        (ihm.const_smul
          (1 - spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime))).add
          (hnext.const_smul (spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime)))
      refine hcombo.congr (Filter.Eventually.of_forall ?_)
      intro ω
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      let gk : E → ℝ := fun y => smoothLinearization S xUnder y
      let hgk : IsAffineModel gk := smoothLinearization_isAffineModel S xUnder
      let states := spsProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩ (law.sample κ)
      have htrans :
          IsSPSTransition S gk outerPrev.x (beta κ) (law.sample κ) m ω
            (states m ω) (states (m + 1) ω) := by
        simpa [states, gk, hgk, outerPrev, xUnder, spsProcess] using
          (spsProcess_isSPSProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩
            (law.sample κ)).2.2 m ω
      have havg :
          (states (m + 1) ω).avg.1 =
            (1 - spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime)) •
                (states m ω).avg.1 +
              spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime) •
                (states (m + 1) ω).u.1 := by
        simpa [IsSPSTransition, states, gk, hgk, outerPrev, xUnder] using htrans.2
      simpa [sgsOracleQuery, sgsInnerProcess_formulaExtensionSelector,
        states, gk, hgk, outerPrev, xUnder] using havg

/-- The selected inner SPS running average has centered L2 integrability from
the finite window of selected-query Bregman integrability facts. -/
theorem selected_sgs_inner_avg_sq_integrable_from_bregman_window
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
    (κ : PositiveTime) :
    ∀ m : ℕ,
      (∀ i, i < m + 1 →
        Integrable
          (fun ω =>
            bregmanFormulaOnX S
              (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                hquery_mem κ i ω⟩ : FeasiblePoint S)
              x)
          law.P) →
      Integrable
        (fun ω =>
          S.primalNorm
            (x.1 -
              (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                law.sample κ m ω).avg.1) ^ 2)
          law.P := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  intro m
  induction m with
  | zero =>
      intro hwindow
      have hq0_breg := hwindow 0 (by omega)
      have hq0_sq :
          Integrable
            (fun ω =>
              S.primalNorm
                (x.1 - sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω) ^ 2)
            law.P :=
        query_sq_integrable_of_bregman_integrable
          (S := S) law.P x
          (fun ω =>
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω,
              hquery_mem κ 0 ω⟩ : FeasiblePoint S))
          (hquery_meas κ 0) hq0_breg
      refine hq0_sq.congr ?_
      filter_upwards with ω
      simp [sgsOracleQuery, sgsInnerProcess_formulaExtensionSelector, spsProcess,
        SOptLib.recursiveIterateProcess, spsInitial]
  | succ m ihm =>
      intro hwindow
      have hprev_window : ∀ i, i < m + 1 →
          Integrable
            (fun ω =>
              bregmanFormulaOnX S
                (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ i ω,
                  hquery_mem κ i ω⟩ : FeasiblePoint S)
                x)
            law.P := by
        intro i hi
        exact hwindow i (by omega)
      have hprev_sq := ihm hprev_window
      have hnext_breg := hwindow (m + 1) (by omega)
      have hnext_sq :
          Integrable
            (fun ω =>
              S.primalNorm
                (x.1 -
                  sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (m + 1) ω) ^ 2)
            law.P :=
        query_sq_integrable_of_bregman_integrable
          (S := S) law.P x
          (fun ω =>
            (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (m + 1) ω,
              hquery_mem κ (m + 1) ω⟩ : FeasiblePoint S))
          (hquery_meas κ (m + 1)) hnext_breg
      have hprev_meas :=
        selected_sgs_inner_avg_aestronglyMeasurable_of_query_meas
          (S := S) law x0 beta gamma T hbeta hgamma hquery_mem hquery_meas κ m
      have hnext_meas :
          AEStronglyMeasurable
            (fun ω =>
              sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (m + 1) ω)
            law.P :=
        (measurable_subtype_coe.comp (hquery_meas κ (m + 1))).aestronglyMeasurable
      have hcombo :
          Integrable
            (fun ω =>
              S.primalNorm
                (x.1 -
                  ((1 - spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime)) •
                      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                        law.sample κ m ω).avg.1 +
                    spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime) •
                      sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (m + 1) ω)) ^ 2)
            law.P :=
        primalNorm_sq_integrable_affine_update
          (S := S) law.P x
          (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
              law.sample κ m ω).avg.1)
          (fun ω =>
            sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (m + 1) ω)
          (spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime))
          hprev_meas hnext_meas hprev_sq hnext_sq
      refine hcombo.congr ?_
      filter_upwards with ω
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω
      let xUnder := outerExtrapolation S gamma κ outerPrev
      let gk : E → ℝ := fun y => smoothLinearization S xUnder y
      let hgk : IsAffineModel gk := smoothLinearization_isAffineModel S xUnder
      let states := spsProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩ (law.sample κ)
      have htrans :
          IsSPSTransition S gk outerPrev.x (beta κ) (law.sample κ) m ω
            (states m ω) (states (m + 1) ω) := by
        simpa [states, gk, hgk, outerPrev, xUnder, spsProcess] using
          (spsProcess_isSPSProcess S gk hgk outerPrev.x ⟨beta κ, hbeta κ⟩
            (law.sample κ)).2.2 m ω
      have havg :
          (states (m + 1) ω).avg.1 =
            (1 - spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime)) •
                (states m ω).avg.1 +
              spsTheta (⟨m + 1, Nat.succ_pos m⟩ : PositiveTime) •
                (states (m + 1) ω).u.1 := by
        simpa [IsSPSTransition, states, gk, hgk, outerPrev, xUnder] using htrans.2
      simpa [sgsOracleQuery, sgsInnerProcess_formulaExtensionSelector,
        states, gk, hgk, outerPrev, xUnder] using
          congrArg (fun y => S.primalNorm (x.1 - y)) havg.symm

/-- Previous outer `xbar` measurability for the selected formula-extension run.

The source independence hypothesis gives query measurability; this companion
records the run-level affine recursion measurability needed by the L2 transport
helper for `xUnder`. -/
theorem selected_sgs_outer_prev_xbar_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω,
          hquery_mem k i ω⟩ : FeasiblePoint S)))
    (κ : PositiveTime) :
    AEStronglyMeasurable
      (fun ω =>
        (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
          (κ.1 - 1) ω).xbar.1) law.P := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  let states : ℕ → Ω → SGSState S :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
  have hstates_xbar :
      ∀ n : ℕ, AEStronglyMeasurable (fun ω => (states n ω).xbar.1) law.P := by
    intro n
    induction n with
    | zero =>
        simpa [states, sgsProcess_formulaExtensionSelector, sgsInitial] using
          (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => x0.1) law.P)
    | succ n ihn =>
        let k : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
        have havg :
            AEStronglyMeasurable
              (fun ω =>
                (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                  law.sample k (T k) ω).avg.1) law.P :=
          selected_sgs_inner_avg_aestronglyMeasurable_of_query_meas
            (S := S) law x0 beta gamma T hbeta hgamma hquery_mem hquery_meas k (T k)
        have hcombo :
            AEStronglyMeasurable
              (fun ω =>
                (1 - gamma k) • (states n ω).xbar.1 +
                  gamma k •
                    (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                      law.sample k (T k) ω).avg.1) law.P :=
          (ihn.const_smul (1 - gamma k)).add (havg.const_smul (gamma k))
        refine hcombo.congr (Filter.Eventually.of_forall ?_)
        intro ω
        have hsucc :
            states (n + 1) ω =
              sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta)
                gamma T law.sample hgamma n (states n ω) ω := by
          simpa [states, sgsProcess_formulaExtensionSelector] using
            SOptLib.recursiveIterateProcess_succ
              (SOptLib.recursiveIterateProcess (sgsInitial S x0)
                (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta)
                  gamma T law.sample hgamma))
              (sgsInitial S x0)
              (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta)
                gamma T law.sample hgamma)
              rfl n ω
        have hk : (⟨n + 1, Nat.succ_pos n⟩ : PositiveTime) = k := rfl
        change
          (1 - gamma k) • (states n ω).xbar.1 +
              gamma k •
                (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                  law.sample k (T k) ω).avg.1 =
            (states (n + 1) ω).xbar.1
        rw [hsucc]
        simp [sgsTransition_formulaExtensionSelector, spsOutput, states,
          sgsInnerProcess_formulaExtensionSelector, positiveBetaSchedule, k, hk]
  simpa [states] using hstates_xbar (κ.1 - 1)

/-- The selected outer extrapolation point has the centered L2 integrability
needed by the fixed-slope residual transport. -/
theorem selected_sgs_inner_xUnder_sq_integrable_from_history
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
        let outerPrev :=
          sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
            (κ.1 - 1) ω
        S.primalNorm (x.1 - outerExtrapolation S gamma κ outerPrev) ^ 2)
      law.P := by
  classical
  let outerPrev : Ω → SGSState S := fun ω =>
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
      (κ.1 - 1) ω
  have houter_x_meas :
      AEStronglyMeasurable (fun ω => (outerPrev ω).x.1) law.P := by
    letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
    have hquery0 :
        AEStronglyMeasurable
          (fun ω => sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ 0 ω)
          law.P :=
      (measurable_subtype_coe.comp (hquery_meas κ 0)).aestronglyMeasurable
    refine hquery0.congr (Filter.Eventually.of_forall ?_)
    intro ω
    simpa [outerPrev] using
      sgsOracleQuery_zero_eq_outer_center
        (S := S) x0 beta gamma T law.sample hbeta hgamma κ ω
  have houter_xbar_meas :
      AEStronglyMeasurable (fun ω => (outerPrev ω).xbar.1) law.P := by
    simpa [outerPrev] using
      selected_sgs_outer_prev_xbar_aestronglyMeasurable
        (S := S) law x0 beta gamma T hbeta hgamma
        hquery_mem hquery_meas κ
  have houter_x_sq :
      Integrable (fun ω => S.primalNorm (x.1 - (outerPrev ω).x.1) ^ 2) law.P := by
    simpa [outerPrev] using
      selected_sgs_outer_prev_center_sq_integrable_of_window
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas κ j hprev_window
  have houter_xbar_sq :
      Integrable (fun ω => S.primalNorm (x.1 - (outerPrev ω).xbar.1) ^ 2) law.P := by
    simpa [outerPrev] using houter_xbar_sq
  simpa [outerPrev] using
    selected_sgs_inner_xUnder_sq_integrable_of_outer_state_sq
      (S := S) law.P x gamma κ outerPrev
      houter_x_meas houter_xbar_meas houter_x_sq houter_xbar_sq

set_option maxHeartbeats 800000

/-- Integrability of the concrete split Cgap used by the fixed-slope
reverse-gap envelope.

This is the named Candidate-1 handoff leaf replacing the former anonymous
theorem-body placeholder.  The proof must combine the old finite Bregman-sum
integrability with the explicitly named `xUnder` L2 invariant above.  The
successor-dependent averaged-output square is not part of this Cgap; the
residual transport absorbs its successor component into the displayed `Vnext`
coefficient, avoiding a circular integrability dependency on the target
successor Bregman term. -/
theorem selected_sgs_inner_average_phi_reverse_gap_splitCgap_integrable
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
    (κ : PositiveTime) (j : ℕ) (squareCoeff χresidual : ℝ)
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
      (selected_sgs_inner_average_phi_reverse_gap_splitCgap
        (S := S) law x0 x beta gamma T hbeta hgamma hquery_mem κ j
        squareCoeff χresidual)
      law.P := by
  classical
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let outerBreg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    bregmanFormulaOnX S outerPrev.x x
  let xUnderSq : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    S.primalNorm (x.1 - xUnder) ^ 2
  let prevBregSum : Ω → ℝ := fun ω =>
    (Finset.range j).sum (fun i =>
      bregmanFormulaOnX S
        (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
          hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S)
        x)
  let scaledPrevBregSum : Ω → ℝ := fun ω =>
    (Finset.range j).sum (fun i =>
      (beta κ * (1 - psWeightProduct spsP t.1)⁻¹ / (4 * (j + 1 : ℝ))) *
        bregmanFormulaOnX S
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
            hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S)
          x)
  have houterBreg_int : Integrable outerBreg law.P := by
    simpa [outerBreg] using
      selected_sgs_outer_prev_center_bregman_integrable_of_window
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem κ j hprev_window
  have hxUnderSq_int : Integrable xUnderSq law.P := by
    simpa [xUnderSq] using
      selected_sgs_inner_xUnder_sq_integrable_from_history
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas κ j houter_xbar_sq hprev_window
  have hprevBregSum_int : Integrable prevBregSum law.P := by
    refine integrable_finset_sum (Finset.range j) ?_
    intro i hi
    have hi_lt : i + 1 < j + 1 := by
      exact Nat.succ_lt_succ (Finset.mem_range.mp hi)
    exact hprev_window (i + 1) hi_lt
  have hscaledPrevBregSum_int : Integrable scaledPrevBregSum law.P := by
    refine integrable_finset_sum (Finset.range j) ?_
    intro i hi
    have hi_lt : i + 1 < j + 1 := by
      exact Nat.succ_lt_succ (Finset.mem_range.mp hi)
    exact (hprev_window (i + 1) hi_lt).const_mul
      (beta κ * (1 - psWeightProduct spsP t.1)⁻¹ / (4 * (j + 1 : ℝ)))
  have hmain_budget_int :
      Integrable
        (fun ω =>
          squareCoeff *
            (1 + outerBreg ω + xUnderSq ω + prevBregSum ω))
        law.P := by
    exact
      (((integrable_const (c := (1 : ℝ))).add houterBreg_int).add hxUnderSq_int |>.add
        hprevBregSum_int).const_mul squareCoeff
  have habs_int :
      Integrable (fun ω => |beta κ * outerBreg ω + χresidual|) law.P := by
    exact ((houterBreg_int.const_mul (beta κ)).add
      (integrable_const (c := χresidual))).abs
  have htotal :
      Integrable
        (fun ω =>
          squareCoeff *
              (1 + outerBreg ω + xUnderSq ω + prevBregSum ω) +
            |beta κ * outerBreg ω + χresidual| +
            scaledPrevBregSum ω)
        law.P :=
    (hmain_budget_int.add habs_int).add hscaledPrevBregSum_int
  refine htotal.congr (Filter.Eventually.of_forall ?_)
  intro ω
  simp [selected_sgs_inner_average_phi_reverse_gap_splitCgap, outerBreg,
    xUnderSq, prevBregSum, scaledPrevBregSum, t, add_assoc, add_comm]
set_option maxHeartbeats 200000

/-- Explicit random constant for the selected averaged-output reverse `Phi` gap.

This replaces the previous successor-square split.  The constant follows the
proved supplied-minorant envelope and exposes exactly the two integrability
burdens: the random smooth-model slope at `x_under` and the outer-center
Bregman term. -/
noncomputable def selected_sgs_inner_average_phi_reverse_gap_explicitCgap
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (κ : PositiveTime) (eps χa : ℝ) (χb : E) : Ω → ℝ := fun ω =>
  let outerPrev :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
      (κ.1 - 1) ω
  let xUnder := outerExtrapolation S gamma κ outerPrev
  dualNorm S (sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb) ^ 2 /
      (2 * eps) +
    |beta κ * bregmanFormulaOnX S outerPrev.x x +
      (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)|

/-- Measurable upper envelope for the smooth-slope part of the selected
reverse-gap constant.

This is not a new source assumption.  It is the algebraic upper bound used when
the separate source-smoothness bridge supplies the dual-Lipschitz estimate for
`sourceSmoothGradient`: the random slope norm is dominated by the already
proved `xUnder` L2 quantity plus a fixed slope depending only on the comparison
point and the chosen `chi` minorant. -/
noncomputable def selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (κ : PositiveTime) (eps χa : ℝ) (χb : E) : Ω → ℝ := fun ω =>
  let outerPrev :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
      (κ.1 - 1) ω
  let xUnder := outerExtrapolation S gamma κ outerPrev
  let fixedSlope := sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb
  ((2 * S.lSmooth ^ 2) / (2 * eps)) * S.primalNorm (x.1 - xUnder) ^ 2 +
      (2 * dualNorm S fixedSlope ^ 2) / (2 * eps) +
    |beta κ * bregmanFormulaOnX S outerPrev.x x +
      (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)|

/-- The explicit random Cgap is dominated by the measurable smooth upper
envelope under the private dual-Lipschitz smooth-gradient bridge. -/
theorem selected_sgs_inner_average_phi_reverse_gap_explicitCgap_le_smoothUpperCgap
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (κ : PositiveTime) {eps : ℝ} (heps : 0 < eps) (χa : ℝ) (χb : E)
    (hgrad_lip :
      ∀ x y : FeasiblePoint S,
        dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) ≤
          S.lSmooth * S.primalNorm (y.1 - x.1)) :
    ∀ ω,
      selected_sgs_inner_average_phi_reverse_gap_explicitCgap
          (S := S) law x0 x beta gamma T hbeta hgamma κ eps χa χb ω ≤
        selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap
          (S := S) law x0 x beta gamma T hbeta hgamma κ eps χa χb ω := by
  classical
  intro ω
  let outerPrev :=
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
      (κ.1 - 1) ω
  let xUnder := outerExtrapolation S gamma κ outerPrev
  let xUnderSq : ℝ := S.primalNorm (x.1 - xUnder) ^ 2
  let slopeNorm : ℝ :=
    dualNorm S (sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb)
  let fixedSlope : E := sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb
  have hxUnder_mem : xUnder ∈ S.X := by
    dsimp [xUnder, outerExtrapolation]
    exact S.convex_X outerPrev.xbar.2 outerPrev.x.2 (sub_nonneg.mpr (hgamma κ).2)
      (hgamma κ).1 (by ring)
  let xUnderFp : FeasiblePoint S := ⟨xUnder, hxUnder_mem⟩
  have hdiff_sq :
      dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) ^ 2 ≤
        S.lSmooth ^ 2 * xUnderSq := by
    have hraw :=
      sourceSmoothGradient_dualNorm_sq_le_smooth_displacement_sq_of_dual_lipschitz
        (S := S) hgrad_lip x xUnderFp
    have hsym :
        S.primalNorm (xUnder - x.1) = S.primalNorm (x.1 - xUnder) := by
      have hneg : xUnder - x.1 = -(x.1 - xUnder) := by abel
      rw [hneg]
      simpa using (map_neg_eq_map S.primalNorm (x.1 - xUnder))
    simpa [xUnderSq, xUnderFp, hsym] using hraw
  have hfixed_nonneg : 0 ≤ dualNorm S fixedSlope := by
    simpa [dualNorm] using
      SOptLib.canonicalDualNorm_nonneg S.primalNorm fixedSlope
  have hslope_add :
      slopeNorm ≤
        dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) +
          dualNorm S fixedSlope := by
    have hdecomp :
        sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb =
          (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) + fixedSlope := by
      simp [fixedSlope]
      abel
    have hadd :=
      SOptLib.canonicalDualNorm_add_le
        (p := S.primalNorm)
        (zeta := sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1)
        (eta := fixedSlope)
        (dualNorm_supportSet_bddAbove S
          (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1))
        (dualNorm_supportSet_bddAbove S fixedSlope)
    simpa [slopeNorm, dualNorm, hdecomp] using hadd
  have hdiff_nonneg :
      0 ≤ dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) := by
    simpa [dualNorm] using
      SOptLib.canonicalDualNorm_nonneg S.primalNorm
        (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1)
  have hslope_nonneg : 0 ≤ slopeNorm := by
    dsimp [slopeNorm]
    simpa [dualNorm] using
      SOptLib.canonicalDualNorm_nonneg S.primalNorm
        (sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb)
  have hsq_add :
      slopeNorm ^ 2 ≤
        2 *
          (dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) ^ 2 +
            dualNorm S fixedSlope ^ 2) := by
    nlinarith [hslope_add, hslope_nonneg, hdiff_nonneg, hfixed_nonneg,
      sq_nonneg
        (dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) -
          dualNorm S fixedSlope)]
  have hnum :
      slopeNorm ^ 2 ≤
        2 * (S.lSmooth ^ 2 * xUnderSq + dualNorm S fixedSlope ^ 2) := by
    nlinarith [hsq_add, hdiff_sq]
  have hscale_nonneg : 0 ≤ (2 * eps)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (by norm_num) heps.le)
  have hscaled := mul_le_mul_of_nonneg_right hnum hscale_nonneg
  have hrewrite :
      2 * (S.lSmooth ^ 2 * xUnderSq + dualNorm S fixedSlope ^ 2) * (2 * eps)⁻¹ =
        ((2 * S.lSmooth ^ 2) / (2 * eps)) * xUnderSq +
          (2 * dualNorm S fixedSlope ^ 2) / (2 * eps) := by
    ring
  rw [hrewrite] at hscaled
  have hslope_part :
      slopeNorm ^ 2 / (2 * eps) ≤
        ((2 * S.lSmooth ^ 2) / (2 * eps)) * xUnderSq +
          (2 * dualNorm S fixedSlope ^ 2) / (2 * eps) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
  dsimp [selected_sgs_inner_average_phi_reverse_gap_explicitCgap,
    selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap,
    outerPrev, xUnder, xUnderSq, slopeNorm, fixedSlope]
  nlinarith

/-- Integrability of the measurable smooth upper envelope.  This eliminates
the former `hslope_aesm` premise from the explicit-Cgap integrability algebra;
the only remaining smooth-gradient burden is the separate dual-Lipschitz bridge. -/
theorem selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap_integrable_of_dual_lipschitz
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
    (κ : PositiveTime) (j : ℕ) {eps : ℝ} (heps : 0 < eps)
    (χa : ℝ) (χb : E)
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
      (selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap
        (S := S) law x0 x beta gamma T hbeta hgamma κ eps χa χb)
      law.P := by
  classical
  let outerBreg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    bregmanFormulaOnX S outerPrev.x x
  let xUnderSq : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    S.primalNorm (x.1 - xUnder) ^ 2
  let fixedSlope : E := sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb
  have houterBreg_int : Integrable outerBreg law.P := by
    simpa [outerBreg] using
      selected_sgs_outer_prev_center_bregman_integrable_of_window
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem κ j hprev_window
  have hxUnderSq_int : Integrable xUnderSq law.P := by
    simpa [xUnderSq] using
      selected_sgs_inner_xUnder_sq_integrable_from_history
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas κ j houter_xbar_sq hprev_window
  have hsmooth_int :
      Integrable
        (fun ω =>
          ((2 * S.lSmooth ^ 2) / (2 * eps)) * xUnderSq ω +
            (2 * dualNorm S fixedSlope ^ 2) / (2 * eps))
        law.P :=
    (hxUnderSq_int.const_mul ((2 * S.lSmooth ^ 2) / (2 * eps))).add
      (integrable_const (c := (2 * dualNorm S fixedSlope ^ 2) / (2 * eps)))
  have habs_int :
      Integrable
        (fun ω =>
          |beta κ * outerBreg ω + (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)|)
        law.P := by
    exact ((houterBreg_int.const_mul (beta κ)).add
      (integrable_const (c := S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ))).abs
  have htotal :
      Integrable
        (fun ω =>
          ((2 * S.lSmooth ^ 2) / (2 * eps)) * xUnderSq ω +
              (2 * dualNorm S fixedSlope ^ 2) / (2 * eps) +
            |beta κ * outerBreg ω + (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)|)
        law.P :=
    hsmooth_int.add habs_int
  refine htotal.congr (Filter.Eventually.of_forall ?_)
  intro ω
  simp [selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap, outerBreg,
    xUnderSq, fixedSlope, add_comm, add_left_comm, add_assoc]

/-- Conditional integrability bridge for the explicit reverse-gap constant.

This deliberately exposes the exact regularity missing from the current source
boundary: measurability of the random smooth-gradient dual norm and a
dual-Lipschitz consequence for the carrier smooth gradient.  The theorem proves
the remaining probability algebra from existing selected-query L2/Bregman
invariants, without adding those regularity facts to `Setup` or to a
paper-facing theorem head. -/
theorem selected_sgs_inner_average_phi_reverse_gap_explicitCgap_integrable_of_smoothGradient
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
    (κ : PositiveTime) (j : ℕ) {eps : ℝ} (heps : 0 < eps)
    (χa : ℝ) (χb : E)
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
          law.P)
    (hgrad_lip :
      ∀ x y : FeasiblePoint S,
        dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) ≤
          S.lSmooth * S.primalNorm (y.1 - x.1))
    (hslope_aesm :
      AEStronglyMeasurable
        (fun ω =>
          let outerPrev :=
            sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
              (κ.1 - 1) ω
          let xUnder := outerExtrapolation S gamma κ outerPrev
          dualNorm S (sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb))
        law.P) :
    Integrable
      (selected_sgs_inner_average_phi_reverse_gap_explicitCgap
        (S := S) law x0 x beta gamma T hbeta hgamma κ eps χa χb)
      law.P := by
  classical
  let outerBreg : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    bregmanFormulaOnX S outerPrev.x x
  let xUnderSq : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    S.primalNorm (x.1 - xUnder) ^ 2
  let slopeNorm : Ω → ℝ := fun ω =>
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    dualNorm S (sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb)
  let fixedSlope : E := sourceSmoothGradient S x.1 + S.hSubgradient x.1 + χb
  have houterBreg_int : Integrable outerBreg law.P := by
    simpa [outerBreg] using
      selected_sgs_outer_prev_center_bregman_integrable_of_window
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem κ j hprev_window
  have hxUnderSq_int : Integrable xUnderSq law.P := by
    simpa [xUnderSq] using
      selected_sgs_inner_xUnder_sq_integrable_from_history
        (S := S) law x0 x beta gamma T hbeta hgamma
        hquery_mem hquery_meas κ j houter_xbar_sq hprev_window
  have hslope_sq_aesm :
      AEStronglyMeasurable (fun ω => slopeNorm ω ^ 2 / (2 * eps)) law.P := by
    refine ((hslope_aesm.pow 2).const_mul ((2 * eps)⁻¹)).congr
      (Filter.Eventually.of_forall ?_)
    intro ω
    dsimp [slopeNorm]
    ring
  have hfixed_nonneg : 0 ≤ dualNorm S fixedSlope := by
    simpa [dualNorm] using
      SOptLib.canonicalDualNorm_nonneg S.primalNorm fixedSlope
  have hslope_bound :
      ∀ ω,
        slopeNorm ω ^ 2 / (2 * eps) ≤
          ((2 * S.lSmooth ^ 2) / (2 * eps)) * xUnderSq ω +
            (2 * dualNorm S fixedSlope ^ 2) / (2 * eps) := by
    intro ω
    let outerPrev :=
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T law.sample
        (κ.1 - 1) ω
    let xUnder := outerExtrapolation S gamma κ outerPrev
    have hxUnder_mem : xUnder ∈ S.X := by
      dsimp [xUnder, outerExtrapolation]
      exact S.convex_X outerPrev.xbar.2 outerPrev.x.2 (sub_nonneg.mpr (hgamma κ).2)
        (hgamma κ).1 (by ring)
    let xUnderFp : FeasiblePoint S := ⟨xUnder, hxUnder_mem⟩
    have hdiff_sq :
        dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) ^ 2 ≤
          S.lSmooth ^ 2 * xUnderSq ω := by
      have hraw :=
        sourceSmoothGradient_dualNorm_sq_le_smooth_displacement_sq_of_dual_lipschitz
          (S := S) hgrad_lip x xUnderFp
      have hsym :
          S.primalNorm (xUnder - x.1) = S.primalNorm (x.1 - xUnder) := by
        have hneg : xUnder - x.1 = -(x.1 - xUnder) := by abel
        rw [hneg]
        simpa using (map_neg_eq_map S.primalNorm (x.1 - xUnder))
      simpa [xUnderSq, outerPrev, xUnder, xUnderFp, hsym] using hraw
    have hslope_add :
        slopeNorm ω ≤
          dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) +
            dualNorm S fixedSlope := by
      have hdecomp :
          sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb =
            (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) + fixedSlope := by
        simp [fixedSlope]
        abel
      have hadd :=
        SOptLib.canonicalDualNorm_add_le
          (p := S.primalNorm)
          (zeta := sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1)
          (eta := fixedSlope)
          (dualNorm_supportSet_bddAbove S
            (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1))
          (dualNorm_supportSet_bddAbove S fixedSlope)
      simpa [slopeNorm, outerPrev, xUnder, dualNorm, hdecomp] using hadd
    have hdiff_nonneg :
        0 ≤ dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) := by
      simpa [dualNorm] using
        SOptLib.canonicalDualNorm_nonneg S.primalNorm
          (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1)
    have hslope_nonneg : 0 ≤ slopeNorm ω := by
      dsimp [slopeNorm, outerPrev, xUnder]
      simpa [dualNorm] using
        SOptLib.canonicalDualNorm_nonneg S.primalNorm
          (sourceSmoothGradient S xUnder + S.hSubgradient x.1 + χb)
    have hsq_add :
        slopeNorm ω ^ 2 ≤
          2 *
            (dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) ^ 2 +
              dualNorm S fixedSlope ^ 2) := by
      nlinarith [hslope_add, hslope_nonneg, hdiff_nonneg, hfixed_nonneg,
        sq_nonneg
          (dualNorm S (sourceSmoothGradient S xUnder - sourceSmoothGradient S x.1) -
            dualNorm S fixedSlope)]
    have hnum :
        slopeNorm ω ^ 2 ≤
          2 * (S.lSmooth ^ 2 * xUnderSq ω + dualNorm S fixedSlope ^ 2) := by
      nlinarith [hsq_add, hdiff_sq]
    have hscale_nonneg : 0 ≤ (2 * eps)⁻¹ := by
      exact inv_nonneg.mpr (mul_nonneg (by norm_num) heps.le)
    have hscaled := mul_le_mul_of_nonneg_right hnum hscale_nonneg
    have hrewrite :
        2 * (S.lSmooth ^ 2 * xUnderSq ω + dualNorm S fixedSlope ^ 2) * (2 * eps)⁻¹ =
          ((2 * S.lSmooth ^ 2) / (2 * eps)) * xUnderSq ω +
            (2 * dualNorm S fixedSlope ^ 2) / (2 * eps) := by
      ring
    rw [hrewrite] at hscaled
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hslope_sq_int :
      Integrable (fun ω => slopeNorm ω ^ 2 / (2 * eps)) law.P := by
    let upper : Ω → ℝ := fun ω =>
      ((2 * S.lSmooth ^ 2) / (2 * eps)) * xUnderSq ω +
        (2 * dualNorm S fixedSlope ^ 2) / (2 * eps)
    have hupper_int : Integrable upper law.P := by
      exact (hxUnderSq_int.const_mul ((2 * S.lSmooth ^ 2) / (2 * eps))).add
        (integrable_const (c := (2 * dualNorm S fixedSlope ^ 2) / (2 * eps)))
    refine hupper_int.mono' hslope_sq_aesm ?_
    filter_upwards with ω
    have htarget_nonneg : 0 ≤ slopeNorm ω ^ 2 / (2 * eps) := by
      exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) heps.le)
    have hle := hslope_bound ω
    have hupper_nonneg : 0 ≤ upper ω := le_trans htarget_nonneg hle
    simpa [upper, Real.norm_of_nonneg htarget_nonneg,
      Real.norm_of_nonneg hupper_nonneg] using hle
  have habs_int :
      Integrable
        (fun ω =>
          |beta κ * outerBreg ω + (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)|)
        law.P := by
    exact ((houterBreg_int.const_mul (beta κ)).add
      (integrable_const (c := S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ))).abs
  have htotal :
      Integrable
        (fun ω =>
          slopeNorm ω ^ 2 / (2 * eps) +
            |beta κ * outerBreg ω + (S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ)|)
        law.P :=
    hslope_sq_int.add habs_int
  refine htotal.congr (Filter.Eventually.of_forall ?_)
  intro ω
  simp [selected_sgs_inner_average_phi_reverse_gap_explicitCgap, outerBreg,
    slopeNorm, add_comm]

/-- Repaired nonterminal envelope for the selected averaged-output reverse
`Phi` gap.

This replaces the stale `splitCgap` route for the selected bridge.  No SOptLib
match: checked the pre-searched weighted variance/telescope candidates and the
local explicit Cgap helpers.  The former control square/recurrence budgets but
do not perform the terminal Young absorption required by Lan Proposition 8.3
Eq. (8.1.63) with Eq. (8.1.24); the latter expose the right smooth-slope upper
envelope but still need the finite SPS terminal/previous-window split packaged
here. -/
noncomputable def selected_sgs_inner_average_phi_reverse_gap_repairedCgap
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hquery_mem :
      ∀ k i ω, sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample k i ω ∈ S.X)
    (κ : PositiveTime) (j : ℕ) (χa : ℝ) (χb : E) : Ω → ℝ := fun ω =>
  let t : PositiveTime := ⟨j + 1, Nat.succ_pos j⟩
  let propCoeff : ℝ := beta κ * (1 - psWeightProduct spsP t.1)⁻¹
  let C : ℝ := psWeightProduct spsP t.1 * (1 - psWeightProduct spsP t.1)⁻¹
  let w : ℕ → ℝ := fun i =>
    (spsP ⟨i + 1, Nat.succ_pos i⟩ * psWeightProduct spsP i)⁻¹
  let qsqBudget : ℝ :=
    (C * w j) ^ 2 +
      2 * (j + 1 : ℝ) * (Finset.range j).sum (fun i => (C * w i) ^ 2)
  (1 + qsqBudget) *
      selected_sgs_inner_average_phi_reverse_gap_smoothUpperCgap
        (S := S) law x0 x beta gamma T hbeta hgamma κ (propCoeff / 2) χa χb ω +
    (Finset.range j).sum (fun i =>
      (propCoeff / (4 * (j + 1 : ℝ))) *
        bregmanFormulaOnX S
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
            hquery_mem κ (i + 1) ω⟩ : FeasiblePoint S)
          x)

end StochasticGradientSliding
