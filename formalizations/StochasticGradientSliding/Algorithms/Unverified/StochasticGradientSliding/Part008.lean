import Algorithms.Unverified.StochasticGradientSliding.Part004

/-!
Downstream source-typed wrappers for Theorem 8.2.

These declarations sit after the generated-run formula-extension APIs from
Parts 003 and 004, so the source-typed theorem names no longer depend on the
Part002-local bridge placeholders.
-/

open scoped BigOperators Gradient InnerProductSpace
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 800000

namespace StochasticGradientSliding

universe u v w z

variable {E : Type u} {Sample : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (S : Setup.{u, v, w} E Sample)

/-- Corrected source-typed Theorem 8.2(a), expected form under gamma range.

This downstream wrapper instantiates the Part002 source-typed relocation bridge
with the Part003 generated-run formula-extension theorem. -/
theorem SGSGenericConvergence_Theorem8_2_expected_sourceTyped_under_gammaRange
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : ProxCorePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S (proxCorePointToFeasible S x0) beta gamma T
      law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T) :
    expectedOutputGap S law (proxCorePointToFeasible S x0) beta gamma T states inner N
        xStar hxStar hrun hindep ≤
        theorem82ExpectedBound_sourceTyped S x0 ⟨xStar, hxStar.1⟩ N beta gamma Gamma T := by
  exact
    SGSGenericConvergence_Theorem8_2_expected_sourceTyped_under_gammaRange_from_runFormulaExtension_api
      (S := S)
      (hapi := SGSGenericConvergence_Theorem8_2_expected_runFormulaExtension_under_gammaRange
        (S := S))
      law x0 xStar beta gamma Gamma T N states inner hgamma hrun hindep hxStar
      hlower hGamma hmono

/-- Corrected source-typed Theorem 8.2(b), high-probability form from explicit
strict-past MDS data.

This downstream wrapper instantiates the Part002 source-typed relocation bridge
with the Part004 formula-extension MDS theorem. -/
theorem SGSGenericConvergence_Theorem8_2_highProbability_sourceTyped_from_mds_under_gammaRange
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : ProxCorePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S (proxCorePointToFeasible S x0) beta gamma T
      law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : forwardMonotonicityCondition beta gamma Gamma T)
    (hcompact : IsCompact S.X)
    (hdomain : bregmanEnvelopeSourceDomainResolved S)
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
          2 * bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain *
            S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P)
    (hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain *
            S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1) :
    outputGapStrictTailProbability S law (proxCorePointToFeasible S x0) beta gamma T
        states inner N xStar hxStar
        (theorem82ExpectedBound_sourceTyped S x0 ⟨xStar, hxStar.1⟩ N beta gamma Gamma T +
          lambda *
            theorem82ProbabilityScale_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain
              N beta gamma Gamma T)
        hrun hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  exact
    SGSGenericConvergence_Theorem8_2_highProbability_sourceTyped_from_mds_under_gammaRange_from_runFormulaExtension_api
      (S := S)
      (hapi := SGSGenericConvergence_Theorem8_2_highProbability_runFormulaExtension_from_mds_under_gammaRange
        (S := S))
      law x0 xStar beta gamma Gamma T N lambda states inner hgamma hrun hindep
      hlambda hxStar hlight hlower hGamma hmono hcompact hdomain
      hquery_strictPast_meas hlinear_condExp_zero hlinear_exp_sq_integrable
      hlinear_condExp_light

/-- Corrected source-typed Theorem 8.2(c), reverse expected form.

This downstream wrapper instantiates the Part002 source-typed relocation bridge
with the Part004 reverse formula-extension theorem. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_expected_sourceTyped_conditionalBridge
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hdomain : bregmanEnvelopeSourceDomainResolved S)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma T) :
    expectedOutputGap S law x0 beta gamma T states inner N xStar hxStar hrun hindep ≤
      theorem82ReverseExpectedBound_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain
        N beta gamma Gamma T := by
  exact
    SGSGenericConvergence_Theorem8_2_reverse_expected_sourceTyped_from_runFormulaExtension_api
      (S := S)
      (hapi := SGSGenericConvergence_Theorem8_2_reverse_expected_runFormulaExtension
        (S := S))
      law x0 xStar beta gamma Gamma T N states inner hrun hindep hxStar hcompact
      hdomain hlower hGamma hmono

/-- Corrected source-typed Theorem 8.2(c), reverse high-probability form from
explicit strict-past MDS data.

This downstream wrapper instantiates the Part002 source-typed relocation bridge
with the Part004 reverse formula-extension MDS theorem. -/
theorem SGSGenericConvergence_Theorem8_2_reverse_highProbability_sourceTyped_from_mds_under_gammaRange
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (xStar : E)
    (beta gamma Gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (N : PositiveTime) (lambda : ℝ)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hgamma : gammaRangeCondition gamma)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hlambda : 0 < lambda) (hxStar : IsOptimalSolution S xStar)
    (hcompact : IsCompact S.X)
    (hdomain : bregmanEnvelopeSourceDomainResolved S)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (hlower : outerLowerBoundCondition S beta gamma)
    (hGamma : outerWeightCondition gamma Gamma)
    (hmono : reverseMonotonicityCondition beta gamma Gamma T)
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
          2 * bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain *
            S.sigmaSq
        Integrable (fun ω => Real.exp (ζ ω ^ 2 / lightScale)) law.P)
    (hlinear_condExp_light :
      ∀ κ i,
        let ζ : Ω → ℝ := fun ω =>
          ⟪oracleNoiseAt S (sgsGeneratedOracleQuery S inner κ i ω)
              (law.sample κ i ω),
            xStar - sgsGeneratedOracleQuery S inner κ i ω⟫_ℝ
        let lightScale : ℝ :=
          2 * bregmanEnvelope_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain *
            S.sigmaSq
        law.P[(fun ω => Real.exp (ζ ω ^ 2 / lightScale)) |
              sgsStrictPastSampleSpace (Ω := Ω) law.sample κ i] ≤ᵐ[law.P]
            fun _ => Real.exp 1) :
    outputGapStrictTailProbability S law x0 beta gamma T states inner N xStar hxStar
        (theorem82ReverseExpectedBound_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain
            N beta gamma Gamma T +
          lambda *
            theorem82ProbabilityScale_sourceTyped S ⟨xStar, hxStar.1⟩ hcompact hdomain
              N beta gamma Gamma T)
        hrun hindep ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3) + Real.exp (-lambda)) := by
  exact
    SGSGenericConvergence_Theorem8_2_reverse_highProbability_sourceTyped_from_mds_under_gammaRange_from_runFormulaExtension_api
      (S := S)
      (hapi := SGSGenericConvergence_Theorem8_2_reverse_highProbability_runFormulaExtension_from_mds
        (S := S))
      law x0 xStar beta gamma Gamma T N lambda states inner hgamma hrun hindep
      hlambda hxStar hcompact hdomain hlight hlower hGamma hmono
      hquery_strictPast_meas hlinear_condExp_zero hlinear_exp_sq_integrable
      hlinear_condExp_light

end StochasticGradientSliding
