import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import Algorithms.Unverified.Muon.Part001

/-!
Complete-paper Muon task. See TASK.md and paper/Muon/source_manifest.json.

This Phase 0 file exposes the paper's object layer: matrix objectives, the
SVD/polar update direction used by Muon, Algorithm 1 stochastic iterates, and
Algorithm 2 deterministic iterates. Endpoint proofs are intentionally left to
later prover phases.
-/

noncomputable section

namespace SGD.Muon

open Matrix MeasureTheory Filter
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius

def theorem_4_16_otherwise_branch_rate_and_complexity {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Δ s Dop : ℝ)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  TildeAsymptoticUpperNatOn
    (fun N => theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
        Wstar cfg.W0 Δ s Dop N ∧
      theorem_4_16_otherwiseBranchRateDomain m n s Dop N)
    (fun N _hN => sourceObjectiveGapAt P (cfgForHorizon N) N hfinite)
    (fun N hN => theorem_4_16_otherwiseBranchRateRealized m n s Dop N hN.2)
    (theoremScope "Theorem 4.16 otherwise branch rate" ["T"]) ∧
  TildeSourceHorizonObjectivePrecisionComplexityWithHorizonRate P hfinite cfgForHorizon
    (fun N => theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
      Wstar cfg.W0 Δ s Dop N)
    (fun _N ε => theorem_4_16_otherwiseComplexityRate m n s Dop ε)
    (theoremScope "Theorem 4.16 otherwise epsilon complexity" ["epsilon"])

/- Appendix C.5's asymptotic read-offs are horizon-family consequences.  The
   supplier below gives the actual run and bounded-distance contract at every
   positive horizon, and the asymptotic and complexity clauses consume exactly
   that same predicate. -/
def theorem_4_16_source_rate_consequences {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (s Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  (∀ cfgForHorizon : ℕ → DeterministicMuonConfig m n,
    (∀ N : ℕ, horizonDomain N →
      theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
        Wstar cfg.W0 Δ s Dop N) →
    theorem_4_16_positiveFamilyBranchRegime P cfgForHorizon
      Wstar cfg.W0 Δ s Dop →
    theorem_4_16_positive_branch_rate_and_complexity
      P cfg Wstar Δ s Dop cfgForHorizon hfinite) ∧
  (∀ cfgForHorizon : ℕ → DeterministicMuonConfig m n,
    (∀ N : ℕ, horizonDomain N →
      theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
        Wstar cfg.W0 Δ s Dop N) →
    theorem_4_16_otherwiseFamilyBranchRegime P cfgForHorizon
      Wstar cfg.W0 Δ s Dop →
    theorem_4_16_otherwise_branch_rate_and_complexity
      P cfg Wstar Δ s Dop cfgForHorizon hfinite)

/- The printed fixed-horizon formula and the claim that `Jtilde` is bounded by
   the unweighted absolute average both use a positive horizon and the
   contraction regime `0 < eta ≤ Dop`.  The source theorem does not state these
   scalar side conditions and in particular permits `T = 0`; following the
   Theorem 4.14 boundary pattern, the public theorem head stays unchanged while
   these two partial expressions are asserted only when their source domain is
   realized.  The two Appendix C.5 rate branches retain their printed formulas
   and carry the same domain pointwise through their run predicates. -/
def theorem_4_16_statement {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (s η Dop : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let Jtilde := hessianDirectionalWeightedAverage P cfg T η Dop
  let hsrc := theorem_4_16_sourceDomain T η Dop
  let hboundary := SourceScalarDomainBoundary hsrc
    (theorem_4_16_downstream_phase2_boundary P cfg T s η Dop hfinite)
    (theorem_4_16_sourceDomainCorrectionNeeded P cfg T s η Dop hfinite)
  hboundary ∧
  (hsrc → ∃ hdom : theorem_4_16_rhsDomain m n T Δ Jtilde s η Dop,
    sourceObjectiveGapAt P cfg T hfinite ≤
      theorem_4_16_rhs P cfg T Δ Jtilde s η Dop hdom) ∧
  (hsrc →
    Jtilde ≤ ((T : ℝ)⁻¹) *
      Finset.sum (Finset.range T) (fun t => |hessianDirectionalTerm P cfg t|)) ∧
    (∀ hregDom : theorem_4_16_branchRegimeThresholdDomain m n s Dop,
    AsymptoticLowerReal epsilonDomain
      (fun _ => Jtilde)
      (fun ε => theorem_4_16_branchRegimeThreshold m n s Dop ε hregDom)
      (theoremScope "Theorem 4.16 Jtilde lower branch" ["epsilon"]) →
    ∀ hlog : theorem_4_16_logScheduleDomain T Δ Jtilde Dop,
    (∀ t ∈ Finset.range T,
      cfg.eta t = theorem_4_16_logEtaRealized T Δ Jtilde Dop hlog) →
      sourceObjectiveGapAt P cfg T hfinite ≤
        theorem_4_16_branchDisplayedBoundRealized m n T Δ Jtilde s Dop hlog) ∧
    (∀ _hregDom : theorem_4_16_branchRegimeThresholdDomain m n s Dop,
    AsymptoticUpperReal epsilonDomain
      (fun _ => Jtilde)
      (fun ε => theorem_4_16_branchRegimeThreshold m n s Dop ε _hregDom)
      (theoremScope "Theorem 4.16 otherwise branch" ["epsilon"]) →
    ∀ hlog : theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop,
    (∀ t ∈ Finset.range T,
      cfg.eta t = theorem_4_16_otherwiseLogEtaRealized m n T Δ s Dop hlog) →
      sourceObjectiveGapAt P cfg T hfinite ≤
        theorem_4_16_sourceRhs P cfg T Δ Jtilde s
          (theorem_4_16_otherwiseLogEtaRealized m n T Δ s Dop hlog) Dop) ∧
    theorem_4_16_source_rate_consequences P cfg Wstar s Dop hfinite


theorem stochasticMuon_equation_13_of_source_assumptions
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma) :
    ∫ ω,
        frobeniusNorm
          (stochasticBatchGradient P cfg.batchSize
              (stochasticMuonState P cfg ω t).W (ω t) -
            P.objective.grad (stochasticMuonState P cfg ω t).W) ^ 2
      ∂(samplePathLaw P cfg.batchSize) ≤
        sigma ^ 2 / (cfg.batchSize.val : ℝ) :=
  stochasticMuon_equation_13 P cfg t sigma hvariance
    (stochasticMuon_W_strictPast_measurable P cfg t)

/- The L² form of Equation (13) needed by the exact Lemma A.4 recurrence.
   Unlike the scalar inequality alone, this records square-integrability of
   the actual mini-batch residual at the adapted Algorithm 1 query. -/
theorem stochasticMuon_batchNoise_sq_integrable_and_equation_13
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma) :
    Integrable
        (fun ω =>
          frobeniusNorm
            (stochasticBatchGradient P cfg.batchSize
                (stochasticMuonState P cfg ω t).W (ω t) -
              P.objective.grad (stochasticMuonState P cfg ω t).W) ^ 2)
        (samplePathLaw P cfg.batchSize) ∧
      ∫ ω,
          frobeniusNorm
            (stochasticBatchGradient P cfg.batchSize
                (stochasticMuonState P cfg ω t).W (ω t) -
              P.objective.grad (stochasticMuonState P cfg ω t).W) ^ 2
        ∂(samplePathLaw P cfg.batchSize) ≤
          sigma ^ 2 / (cfg.batchSize.val : ℝ) := by
  classical
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  let pathLaw := samplePathLaw P cfg.batchSize
  letI : IsProbabilityMeasure pathLaw := by
    dsimp [pathLaw, samplePathLaw]
    infer_instance
  let query : SamplePath ξ cfg.batchSize → Mat m n :=
    fun ω => (stochasticMuonState P cfg ω t).W
  let sampleCoord : (ℕ × Fin cfg.batchSize.val) → SamplePath ξ cfg.batchSize → ξ :=
    fun q ω => ω q.1 q.2
  let pastSet : Set (ℕ × Fin cfg.batchSize.val) := {q | q.1 < t}
  have hcoord_meas : ∀ q, Measurable (sampleCoord q) := by
    intro q
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hcoord_iIndep : ProbabilityTheory.iIndepFun sampleCoord pathLaw := by
    simpa [sampleCoord, pathLaw, samplePathLaw] using
      (SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval
        cfg.batchSize.val P.sampleLaw)
  have hstrict_eq :
      stochasticSampleStrictPast cfg.batchSize t =
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (sampleCoord q)
            (by infer_instance : MeasurableSpace ξ)) := by
    rfl
  have hquery_past :
      Measurable[stochasticSampleStrictPast cfg.batchSize t] query := by
    simpa [query] using stochasticMuon_W_strictPast_measurable P cfg t
  have hstrict_ambient :
      stochasticSampleStrictPast cfg.batchSize t ≤
        (by infer_instance : MeasurableSpace (SamplePath ξ cfg.batchSize)) := by
    rw [hstrict_eq]
    refine iSup_le fun q => iSup_le fun _hq => ?_
    exact (hcoord_meas q).comap_le
  have hquery_meas : Measurable query :=
    hquery_past.mono hstrict_ambient le_rfl
  have hpast_current (i : Fin cfg.batchSize.val) :
      Disjoint pastSet ({(t, i)} : Set (ℕ × Fin cfg.batchSize.val)) := by
    rw [Set.disjoint_singleton_right]
    intro hmem
    exact (Nat.lt_irrefl t) hmem
  have hfresh (i : Fin cfg.batchSize.val) :=
    indepFun_prefixKey_current_of_iIndepFun
      (μ := pathLaw) (sampleCoord := sampleCoord)
      hcoord_meas hcoord_iIndep
      (prefixKey := query)
      (pastSet := pastSet)
      (strictPast := stochasticSampleStrictPast cfg.batchSize t)
      hquery_past (by simpa [hstrict_eq]) (hpast_current i)
  have hindep_query : ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)),
      ProbabilityTheory.IndepFun query (fun ω => ω t i) pathLaw := by
    intro i _hi
    simpa [sampleCoord] using (hfresh i).1
  have hres_meas :
      Measurable (fun p : Mat m n × ξ =>
        P.sampleGrad p.1 p.2 - P.objective.grad p.1) :=
    P.sampleGradKernel.property.sub
      (P.objective.grad_measurable.comp measurable_fst)
  have hY_meas : ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)),
      Measurable (fun ω : SamplePath ξ cfg.batchSize => ω t i) := by
    intro i _hi
    exact (measurable_pi_apply i).comp (measurable_pi_apply t)
  have hmap (i : Fin cfg.batchSize.val) :
      Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω t i) pathLaw =
        P.sampleLaw := by
    simpa [pathLaw, samplePathLaw] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval
        cfg.batchSize.val P.sampleLaw t i)
  have hfixed_int :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        Integrable
          (fun ω : SamplePath ξ cfg.batchSize =>
            ‖P.sampleGrad z (ω t i) - P.objective.grad z‖ ^ 2) pathLaw := by
    intro i hi z
    let phi : ξ → ℝ := fun s => ‖P.sampleGrad z s - P.objective.grad z‖ ^ 2
    have hphi : Measurable phi := by
      simpa [phi] using
        (hres_meas.comp
          ((measurable_const : Measurable fun _ : ξ => z).prodMk measurable_id)).norm.pow_const 2
    have hmapped : Integrable phi
        (Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω t i) pathLaw) := by
      rw [hmap i]
      simpa [phi, frobeniusNorm, SOptLib.expectationWellDefined] using
        (hvariance.variance z).choose
    exact (integrable_map_measure hphi.aestronglyMeasurable
      (hY_meas i hi).aemeasurable).mp hmapped
  have hfixed_bound :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        ∫ ω : SamplePath ξ cfg.batchSize,
            ‖P.sampleGrad z (ω t i) - P.objective.grad z‖ ^ 2 ∂pathLaw ≤
          sigma ^ 2 := by
    intro i hi z
    let phi : ξ → ℝ := fun s => ‖P.sampleGrad z s - P.objective.grad z‖ ^ 2
    have hphi : AEStronglyMeasurable phi P.sampleLaw := by
      exact (hres_meas.comp
        ((measurable_const : Measurable fun _ : ξ => z).prodMk measurable_id)).norm.pow_const 2
        |>.aestronglyMeasurable
    calc
      ∫ ω : SamplePath ξ cfg.batchSize,
          ‖P.sampleGrad z (ω t i) - P.objective.grad z‖ ^ 2 ∂pathLaw =
          ∫ s, phi s ∂P.sampleLaw := by
            rw [← hmap i]
            exact (integral_map (hY_meas i hi).aemeasurable
              (hphi.mono_measure (by rw [hmap i]))).symm
      _ ≤ sigma ^ 2 := by
        simpa [phi, frobeniusNorm, realizedExpectation] using
          (hvariance.variance z).choose_spec
  have havg :=
    integrable_sq_norm_randomQuery_centeredMiniBatchAverage_of_fixed_variance
      (P := pathLaw) (I := (Finset.univ : Finset (Fin cfg.batchSize.val)))
      (m := cfg.batchSize.val) (G := P.sampleGrad)
      (target := P.objective.grad) (xq := query)
      (Y := fun i ω => ω t i) (sigma ^ 2)
      hres_meas hquery_meas hY_meas hindep_query (sq_nonneg sigma)
      hfixed_int hfixed_bound
  have hcenter : ∀ ω : SamplePath ξ cfg.batchSize,
      stochasticBatchGradient P cfg.batchSize (query ω) (ω t) -
          P.objective.grad (query ω) =
        ((cfg.batchSize.val : ℝ)⁻¹) •
          ∑ i : Fin cfg.batchSize.val,
            (P.sampleGrad (query ω) (ω t i) - P.objective.grad (query ω)) := by
    intro ω
    exact miniBatchAverage_sub_target_eq_average_residual
      Finset.univ cfg.batchSize.val (by simp) cfg.batchSize.positive
      (fun i => P.sampleGrad (query ω) (ω t i)) (P.objective.grad (query ω))
  constructor
  · change Integrable
      (fun ω => frobeniusNorm
        (stochasticBatchGradient P cfg.batchSize (query ω) (ω t) -
          P.objective.grad (query ω)) ^ 2) pathLaw
    simpa only [frobeniusNorm, hcenter] using havg
  · simpa [pathLaw, query] using
      stochasticMuon_equation_13_of_source_assumptions P cfg t sigma hvariance

theorem stochasticMuonComparator_zero
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) :
    stochasticMuonComparator P cfg ω 0 = P.objective.grad cfg.W0 :=
  rfl

theorem stochasticMuonComparator_succ
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) :
    stochasticMuonComparator P cfg ω (t + 1) =
      cfg.beta • stochasticMuonComparator P cfg ω t +
        (1 - cfg.beta) •
          P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W := by
  cases t <;> rfl

theorem stochasticMuon_comparatorError_zero
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) :
    stochasticMuonComparator P cfg ω 0 - (stochasticMuonState P cfg ω 0).M =
      -(stochasticBatchGradient P cfg.batchSize cfg.W0 (ω 0) -
        P.objective.grad cfg.W0) := by
  rw [stochasticMuonComparator_zero, stochasticMuon_M_zero_eq_G_zero]
  abel

theorem stochasticMuon_comparatorError_succ
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) :
    stochasticMuonComparator P cfg ω (t + 1) -
        (stochasticMuonState P cfg ω (t + 1)).M =
      cfg.beta •
          (stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M) -
        (1 - cfg.beta) •
          (stochasticBatchGradient P cfg.batchSize
              (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) -
            P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W) := by
  rw [stochasticMuonComparator_succ, stochasticMuon_M_succ_eq_source_update]
  module

theorem stochasticMuonComparator_strictPast_measurable
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) :
    ∀ t : ℕ,
      Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)]
        (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonComparator P cfg ω t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have ih_up := ih.mono
        (stochasticSampleStrictPast_mono cfg.batchSize (Nat.le_succ (t + 1))) le_rfl
      have hW := (stochasticMuon_W_strictPast_measurable P cfg (t + 1)).mono
        (stochasticSampleStrictPast_mono cfg.batchSize (Nat.le_succ (t + 1))) le_rfl
      rw [show (fun ω : SamplePath ξ cfg.batchSize =>
          stochasticMuonComparator P cfg ω (Nat.succ t)) =
        fun ω => cfg.beta • stochasticMuonComparator P cfg ω t +
          (1 - cfg.beta) • P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W by
            funext ω
            simpa [Nat.succ_eq_add_one] using stochasticMuonComparator_succ P cfg ω t]
      exact ih_up.const_smul cfg.beta |>.add
        ((P.objective.grad_measurable.comp hW).const_smul (1 - cfg.beta))

theorem stochasticMuon_comparatorError_strictPast_measurable
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (t : ℕ) :
    Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)]
      (fun ω : SamplePath ξ cfg.batchSize =>
        stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M) := by
  exact (stochasticMuonComparator_strictPast_measurable P cfg t).sub
    ((stochasticMuon_state_strictPast_measurable_of_direction P cfg
      orthogonalizedDirection_measurable t).2)

theorem stochasticMuon_batchNoise_strictPast_measurable
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (t : ℕ) :
    Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)]
      (fun ω : SamplePath ξ cfg.batchSize =>
        stochasticBatchGradient P cfg.batchSize
            (stochasticMuonState P cfg ω t).W (ω t) -
          P.objective.grad (stochasticMuonState P cfg ω t).W) := by
  have hW := (stochasticMuon_W_strictPast_measurable P cfg t).mono
    (stochasticSampleStrictPast_mono cfg.batchSize (Nat.le_succ t)) le_rfl
  have hbatch := stochasticBatchGradient_measurable_from
    (stochasticSampleStrictPast cfg.batchSize (t + 1)) P cfg.batchSize
    (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W)
    (fun ω : SamplePath ξ cfg.batchSize => ω t) hW
    (stochasticSample_miniBatch_measurable_strictPast cfg.batchSize (Nat.lt_succ_self t))
  exact hbatch.sub (P.objective.grad_measurable.comp hW)

/- The martingale cross term in Lemma A.4.  Its only local input is the L²
   induction hypothesis for the comparator error; freshness is derived from
   the iid sample path and strict-past adaptedness. -/
theorem stochasticMuon_comparatorError_inner_nextNoise_integral_eq_zero
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma)
    (herror_sq : Integrable
      (fun ω =>
        ‖matrixToEuclidean
          (stochasticMuonComparator P cfg ω t -
            (stochasticMuonState P cfg ω t).M)‖ ^ 2)
      (samplePathLaw P cfg.batchSize)) :
    Integrable
        (fun ω =>
          ⟪matrixToEuclidean
              (stochasticBatchGradient P cfg.batchSize
                  (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) -
                P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W),
            matrixToEuclidean
              (stochasticMuonComparator P cfg ω t -
                (stochasticMuonState P cfg ω t).M)⟫_ℝ)
        (samplePathLaw P cfg.batchSize) ∧
      ∫ ω,
          ⟪matrixToEuclidean
              (stochasticBatchGradient P cfg.batchSize
                  (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) -
                P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W),
            matrixToEuclidean
              (stochasticMuonComparator P cfg ω t -
                (stochasticMuonState P cfg ω t).M)⟫_ℝ
        ∂(samplePathLaw P cfg.batchSize) = 0 := by
  classical
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  let pathLaw := samplePathLaw P cfg.batchSize
  letI : IsProbabilityMeasure pathLaw := by
    dsimp [pathLaw, samplePathLaw]
    infer_instance
  let errorE : SamplePath ξ cfg.batchSize → EuclideanSpace ℝ (Fin m × Fin n) :=
    fun ω => matrixToEuclidean
      (stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M)
  let query : SamplePath ξ cfg.batchSize →
      Mat m n × EuclideanSpace ℝ (Fin m × Fin n) :=
    fun ω => ((stochasticMuonState P cfg ω (t + 1)).W, errorE ω)
  let sampleCoord : (ℕ × Fin cfg.batchSize.val) → SamplePath ξ cfg.batchSize → ξ :=
    fun q ω => ω q.1 q.2
  let pastSet : Set (ℕ × Fin cfg.batchSize.val) := {q | q.1 < t + 1}
  have hcoord_meas : ∀ q, Measurable (sampleCoord q) := by
    intro q
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hcoord_iIndep : ProbabilityTheory.iIndepFun sampleCoord pathLaw := by
    simpa [sampleCoord, pathLaw, samplePathLaw] using
      (SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval
        cfg.batchSize.val P.sampleLaw)
  have hstrict_eq :
      stochasticSampleStrictPast cfg.batchSize (t + 1) =
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (sampleCoord q)
            (by infer_instance : MeasurableSpace ξ)) := by
    rfl
  have hW_past := stochasticMuon_W_strictPast_measurable P cfg (t + 1)
  have herror_past := stochasticMuon_comparatorError_strictPast_measurable P cfg t
  have herrorE_past :
      Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)] errorE := by
    exact matrixToEuclidean_measurable.comp herror_past
  have hquery_past :
      Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)] query :=
    hW_past.prodMk herrorE_past
  have hstrict_ambient :
      stochasticSampleStrictPast cfg.batchSize (t + 1) ≤
        (by infer_instance : MeasurableSpace (SamplePath ξ cfg.batchSize)) := by
    rw [hstrict_eq]
    refine iSup_le fun q => iSup_le fun _hq => ?_
    exact (hcoord_meas q).comap_le
  have hquery_meas : Measurable query :=
    hquery_past.mono hstrict_ambient le_rfl
  have hpast_current (i : Fin cfg.batchSize.val) :
      Disjoint pastSet ({(t + 1, i)} : Set (ℕ × Fin cfg.batchSize.val)) := by
    rw [Set.disjoint_singleton_right]
    intro hmem
    exact (Nat.lt_irrefl (t + 1)) hmem
  have hfresh (i : Fin cfg.batchSize.val) :=
    indepFun_prefixKey_current_of_iIndepFun
      (μ := pathLaw) (sampleCoord := sampleCoord)
      hcoord_meas hcoord_iIndep
      (prefixKey := query) (pastSet := pastSet)
      (strictPast := stochasticSampleStrictPast cfg.batchSize (t + 1))
      hquery_past (by simpa [hstrict_eq]) (hpast_current i)
  have hsample_meas (i : Fin cfg.batchSize.val) :
      Measurable (fun ω : SamplePath ξ cfg.batchSize => ω (t + 1) i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply (t + 1))
  have hmap (i : Fin cfg.batchSize.val) :
      Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω (t + 1) i) pathLaw =
        P.sampleLaw := by
    simpa [pathLaw, samplePathLaw] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval
        cfg.batchSize.val P.sampleLaw (t + 1) i)
  let G : Mat m n → ξ → EuclideanSpace ℝ (Fin m × Fin n) :=
    fun W z => matrixToEuclidean (P.sampleGrad W z)
  let target : Mat m n → EuclideanSpace ℝ (Fin m × Fin n) :=
    fun W => matrixToEuclidean (P.objective.grad W)
  have hres_meas : Measurable (fun p : Mat m n × ξ => G p.1 p.2 - target p.1) := by
    dsimp [G, target]
    simpa [← matrixToEuclidean_sub] using
      matrixToEuclidean_measurable.comp
        (P.sampleGradKernel.property.sub
          (P.objective.grad_measurable.comp measurable_fst))
  have hfixed_sq_int : ∀ W : Mat m n,
      Integrable (fun z => ‖G W z - target W‖ ^ 2) P.sampleLaw := by
    intro W
    simpa [G, target, ← matrixToEuclidean_sub, norm_matrixToEuclidean,
      frobeniusNorm, SOptLib.expectationWellDefined] using
      (hvariance.variance W).choose
  have hfixed_sq_bound : ∀ W : Mat m n,
      ∫ z, ‖G W z - target W‖ ^ 2 ∂P.sampleLaw ≤ sigma ^ 2 := by
    intro W
    simpa [G, target, ← matrixToEuclidean_sub, norm_matrixToEuclidean,
      frobeniusNorm, realizedExpectation] using
      (hvariance.variance W).choose_spec
  have hfixed_int : ∀ W : Mat m n,
      Integrable (fun z => G W z - target W) P.sampleLaw := by
    intro W
    exact integrable_of_integrable_norm_sq
      ((hres_meas.comp
        ((measurable_const : Measurable fun _ : ξ => W).prodMk measurable_id)).aestronglyMeasurable)
      (hfixed_sq_int W)
  have hfixed_zero : ∀ W : Mat m n,
      ∫ z, G W z - target W ∂P.sampleLaw = 0 := by
    intro W
    have hGint : Integrable (fun z => P.sampleGrad W z) P.sampleLaw := by
      simpa [SOptLib.expectationWellDefined] using (hvariance.unbiased W).choose
    have hresint : Integrable
        (fun z => P.sampleGrad W z - P.objective.grad W) P.sampleLaw :=
      hGint.sub (integrable_const _)
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := matrixToEuclideanCLM (m := m) (n := n)) hresint
    calc
      ∫ z, G W z - target W ∂P.sampleLaw =
          matrixToEuclideanCLM
            (∫ z, P.sampleGrad W z - P.objective.grad W ∂P.sampleLaw) := by
              simpa [G, target, matrixToEuclidean_sub] using hlin
      _ = 0 := by
        rw [integral_sub hGint (integrable_const _)]
        have hmean : ∫ z, P.sampleGrad W z ∂P.sampleLaw = P.objective.grad W := by
          simpa [realizedExpectation] using (hvariance.unbiased W).choose_spec
        rw [hmean]
        simp
        ext p
        rfl
  have hone (i : Fin cfg.batchSize.val) :
      Integrable
          (fun ω : SamplePath ξ cfg.batchSize =>
            ⟪G (query ω).1 (ω (t + 1) i) - target (query ω).1,
              (query ω).2⟫_ℝ) pathLaw ∧
        ∫ ω : SamplePath ξ cfg.batchSize,
            ⟪G (query ω).1 (ω (t + 1) i) - target (query ω).1,
              (query ω).2⟫_ℝ ∂pathLaw = 0 := by
    apply randomQuery_inner_oracleResidual_integrable_and_integral_eq_zero_of_l2
      (P := pathLaw) (ν := P.sampleLaw) (query := query)
      (sample := fun ω => ω (t + 1) i) (G := G) (target := target)
      (varianceBudget := sigma ^ 2)
    · exact hres_meas.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
        |>.aestronglyMeasurable
    · exact hquery_meas.aemeasurable
    · exact (hsample_meas i).aemeasurable
    · simpa [sampleCoord] using (hfresh i).1
    · exact hmap i
    · exact hfixed_int
    · exact hfixed_zero
    · exact hfixed_sq_int
    · exact hfixed_sq_bound
    · simpa [query, errorE, pathLaw] using herror_sq
  let scalarTerm : Fin cfg.batchSize.val → SamplePath ξ cfg.batchSize → ℝ :=
    fun i ω =>
      ⟪G (query ω).1 (ω (t + 1) i) - target (query ω).1, (query ω).2⟫_ℝ
  have hsum_int : Integrable
      (fun ω => ∑ i : Fin cfg.batchSize.val, scalarTerm i ω) pathLaw := by
    exact MeasureTheory.integrable_finset_sum _ (fun i _hi => by
      simpa [scalarTerm] using (hone i).1)
  have hsum_zero :
      ∫ ω, (∑ i : Fin cfg.batchSize.val, scalarTerm i ω) ∂pathLaw = 0 := by
    rw [integral_finset_sum _ (fun i _hi => by
      simpa [scalarTerm] using (hone i).1)]
    simp [scalarTerm, (hone _).2]
  have hcenter : ∀ ω : SamplePath ξ cfg.batchSize,
      stochasticBatchGradient P cfg.batchSize (query ω).1 (ω (t + 1)) -
          P.objective.grad (query ω).1 =
        ((cfg.batchSize.val : ℝ)⁻¹) •
          ∑ i : Fin cfg.batchSize.val,
            (P.sampleGrad (query ω).1 (ω (t + 1) i) -
              P.objective.grad (query ω).1) := by
    intro ω
    exact miniBatchAverage_sub_target_eq_average_residual
      Finset.univ cfg.batchSize.val (by simp) cfg.batchSize.positive
      (fun i => P.sampleGrad (query ω).1 (ω (t + 1) i))
      (P.objective.grad (query ω).1)
  have hpoint : ∀ ω : SamplePath ξ cfg.batchSize,
      ⟪matrixToEuclidean
          (stochasticBatchGradient P cfg.batchSize (query ω).1 (ω (t + 1)) -
            P.objective.grad (query ω).1), (query ω).2⟫_ℝ =
        (cfg.batchSize.val : ℝ)⁻¹ *
          ∑ i : Fin cfg.batchSize.val, scalarTerm i ω := by
    intro ω
    rw [hcenter]
    change ⟪matrixToEuclideanCLM
        (((cfg.batchSize.val : ℝ)⁻¹) •
          ∑ i : Fin cfg.batchSize.val,
            (P.sampleGrad (query ω).1 (ω (t + 1) i) -
              P.objective.grad (query ω).1)), (query ω).2⟫_ℝ = _
    rw [map_smul, map_sum, inner_smul_left, sum_inner]
    simp [scalarTerm, G, target, matrixToEuclidean_sub]
  have hscaled_int : Integrable
      (fun ω => (cfg.batchSize.val : ℝ)⁻¹ *
        ∑ i : Fin cfg.batchSize.val, scalarTerm i ω) pathLaw :=
    hsum_int.const_mul _
  constructor
  · simpa only [query, errorE, pathLaw, hpoint] using hscaled_int
  · change ∫ ω,
        ⟪matrixToEuclidean
            (stochasticBatchGradient P cfg.batchSize (query ω).1 (ω (t + 1)) -
              P.objective.grad (query ω).1), (query ω).2⟫_ℝ ∂pathLaw = 0
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_const_mul, hsum_zero, mul_zero]

/- The exact second-moment recurrence behind Lemma A.4. -/
theorem stochasticMuon_comparatorError_sq_recurrence
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma)
    (herror_sq : Integrable
      (fun ω =>
        ‖matrixToEuclidean
          (stochasticMuonComparator P cfg ω t -
            (stochasticMuonState P cfg ω t).M)‖ ^ 2)
      (samplePathLaw P cfg.batchSize)) :
    Integrable
        (fun ω =>
          ‖matrixToEuclidean
            (stochasticMuonComparator P cfg ω (t + 1) -
              (stochasticMuonState P cfg ω (t + 1)).M)‖ ^ 2)
        (samplePathLaw P cfg.batchSize) ∧
      ∫ ω,
          ‖matrixToEuclidean
            (stochasticMuonComparator P cfg ω (t + 1) -
              (stochasticMuonState P cfg ω (t + 1)).M)‖ ^ 2
        ∂(samplePathLaw P cfg.batchSize) =
          cfg.beta ^ 2 *
            ∫ ω,
              ‖matrixToEuclidean
                (stochasticMuonComparator P cfg ω t -
                  (stochasticMuonState P cfg ω t).M)‖ ^ 2
              ∂(samplePathLaw P cfg.batchSize) +
          (1 - cfg.beta) ^ 2 *
            ∫ ω,
              ‖matrixToEuclidean
                (stochasticBatchGradient P cfg.batchSize
                    (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) -
                  P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W)‖ ^ 2
              ∂(samplePathLaw P cfg.batchSize) := by
  let μ := samplePathLaw P cfg.batchSize
  let errorE : SamplePath ξ cfg.batchSize → EuclideanSpace ℝ (Fin m × Fin n) :=
    fun ω => matrixToEuclidean
      (stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M)
  let noiseE : SamplePath ξ cfg.batchSize → EuclideanSpace ℝ (Fin m × Fin n) :=
    fun ω => matrixToEuclidean
      (stochasticBatchGradient P cfg.batchSize
          (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) -
        P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W)
  have hnoise :=
    stochasticMuon_batchNoise_sq_integrable_and_equation_13
      P cfg (t + 1) sigma hvariance
  have hnoise_sq : Integrable (fun ω => ‖noiseE ω‖ ^ 2) μ := by
    simpa [noiseE, μ, frobeniusNorm, norm_matrixToEuclidean] using hnoise.1
  have hcross :=
    stochasticMuon_comparatorError_inner_nextNoise_integral_eq_zero
      P cfg t sigma hvariance herror_sq
  have hcross_int : Integrable (fun ω => ⟪noiseE ω, errorE ω⟫_ℝ) μ := by
    simpa [noiseE, errorE, μ] using hcross.1
  have hcross_zero : ∫ ω, ⟪noiseE ω, errorE ω⟫_ℝ ∂μ = 0 := by
    simpa [noiseE, errorE, μ] using hcross.2
  have hvec : ∀ ω : SamplePath ξ cfg.batchSize,
      matrixToEuclidean
          (stochasticMuonComparator P cfg ω (t + 1) -
            (stochasticMuonState P cfg ω (t + 1)).M) =
        cfg.beta • errorE ω - (1 - cfg.beta) • noiseE ω := by
    intro ω
    rw [stochasticMuon_comparatorError_succ]
    ext p
    rfl
  have hsq : ∀ ω : SamplePath ξ cfg.batchSize,
      ‖matrixToEuclidean
          (stochasticMuonComparator P cfg ω (t + 1) -
            (stochasticMuonState P cfg ω (t + 1)).M)‖ ^ 2 =
        cfg.beta ^ 2 * ‖errorE ω‖ ^ 2 -
          (2 * cfg.beta * (1 - cfg.beta)) * ⟪noiseE ω, errorE ω⟫_ℝ +
        (1 - cfg.beta) ^ 2 * ‖noiseE ω‖ ^ 2 := by
    intro ω
    have hb : 0 ≤ cfg.beta := cfg.beta_mem.1
    have h1b : 0 ≤ 1 - cfg.beta := by linarith [cfg.beta_mem.2]
    rw [hvec, norm_sub_sq_real, norm_smul, norm_smul,
      inner_smul_left, inner_smul_right, real_inner_comm]
    simp only [Real.norm_eq_abs, conj_trivial]
    rw [abs_of_nonneg hb, abs_of_nonneg h1b]
    ring
  have hA : Integrable (fun ω => cfg.beta ^ 2 * ‖errorE ω‖ ^ 2) μ := by
    exact herror_sq.const_mul _
  have hB : Integrable
      (fun ω => (2 * cfg.beta * (1 - cfg.beta)) * ⟪noiseE ω, errorE ω⟫_ℝ) μ :=
    hcross_int.const_mul _
  have hC : Integrable (fun ω => (1 - cfg.beta) ^ 2 * ‖noiseE ω‖ ^ 2) μ :=
    hnoise_sq.const_mul _
  have hnext : Integrable
      (fun ω =>
        ‖matrixToEuclidean
          (stochasticMuonComparator P cfg ω (t + 1) -
            (stochasticMuonState P cfg ω (t + 1)).M)‖ ^ 2) μ := by
    exact ((hA.sub hB).add hC).congr (Filter.Eventually.of_forall fun ω => (hsq ω).symm)
  constructor
  · simpa [μ] using hnext
  · change (∫ ω,
        ‖matrixToEuclidean
          (stochasticMuonComparator P cfg ω (t + 1) -
            (stochasticMuonState P cfg ω (t + 1)).M)‖ ^ 2 ∂μ) = _
    rw [integral_congr_ae (Filter.Eventually.of_forall hsq)]
    change
      (∫ ω, cfg.beta ^ 2 * ‖errorE ω‖ ^ 2 -
          (2 * cfg.beta * (1 - cfg.beta)) * ⟪noiseE ω, errorE ω⟫_ℝ +
          (1 - cfg.beta) ^ 2 * ‖noiseE ω‖ ^ 2 ∂μ) =
        cfg.beta ^ 2 * (∫ ω, ‖errorE ω‖ ^ 2 ∂μ) +
          (1 - cfg.beta) ^ 2 * (∫ ω, ‖noiseE ω‖ ^ 2 ∂μ)
    calc
      _ = (∫ ω, cfg.beta ^ 2 * ‖errorE ω‖ ^ 2 -
              (2 * cfg.beta * (1 - cfg.beta)) *
                ⟪noiseE ω, errorE ω⟫_ℝ ∂μ) +
            ∫ ω, (1 - cfg.beta) ^ 2 * ‖noiseE ω‖ ^ 2 ∂μ := by
              simpa only [Pi.add_apply, Pi.sub_apply] using
                (integral_add (hA.sub hB) hC)
      _ = (∫ ω, cfg.beta ^ 2 * ‖errorE ω‖ ^ 2 ∂μ) -
            (∫ ω, (2 * cfg.beta * (1 - cfg.beta)) *
              ⟪noiseE ω, errorE ω⟫_ℝ ∂μ) +
            ∫ ω, (1 - cfg.beta) ^ 2 * ‖noiseE ω‖ ^ 2 ∂μ := by
              rw [integral_sub hA hB]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul, hcross_zero]
        ring

/- The finite geometric solution of the Lemma A.4 second-moment recurrence. -/
theorem stochasticMuon_comparatorError_sq_integrable_and_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma) :
    Integrable
        (fun ω =>
          ‖matrixToEuclidean
            (stochasticMuonComparator P cfg ω t -
              (stochasticMuonState P cfg ω t).M)‖ ^ 2)
        (samplePathLaw P cfg.batchSize) ∧
      ∫ ω,
          ‖matrixToEuclidean
            (stochasticMuonComparator P cfg ω t -
              (stochasticMuonState P cfg ω t).M)‖ ^ 2
        ∂(samplePathLaw P cfg.batchSize) ≤
          (1 - cfg.beta) / (1 + cfg.beta) *
              (sigma ^ 2 / (cfg.batchSize.val : ℝ)) +
            cfg.beta ^ (2 * t) * (sigma ^ 2 / (cfg.batchSize.val : ℝ)) := by
  induction t with
  | zero =>
      have hnoise :=
        stochasticMuon_batchNoise_sq_integrable_and_equation_13
          P cfg 0 sigma hvariance
      have hbase_int : Integrable
          (fun ω =>
            ‖matrixToEuclidean
              (stochasticMuonComparator P cfg ω 0 -
                (stochasticMuonState P cfg ω 0).M)‖ ^ 2)
          (samplePathLaw P cfg.batchSize) := by
        simpa [stochasticMuon_comparatorError_zero, stochasticMuonState,
          stochasticMuonBaseState, frobeniusNorm, norm_matrixToEuclidean,
          norm_sub_rev] using hnoise.1
      have hbase_bound :
          ∫ ω,
              ‖matrixToEuclidean
                (stochasticMuonComparator P cfg ω 0 -
                  (stochasticMuonState P cfg ω 0).M)‖ ^ 2
            ∂(samplePathLaw P cfg.batchSize) ≤
              sigma ^ 2 / (cfg.batchSize.val : ℝ) := by
        simpa [stochasticMuon_comparatorError_zero, stochasticMuonState,
          stochasticMuonBaseState, frobeniusNorm, norm_matrixToEuclidean,
          norm_sub_rev] using hnoise.2
      have hB : 0 ≤ sigma ^ 2 / (cfg.batchSize.val : ℝ) := by positivity
      have hcoef : 0 ≤ (1 - cfg.beta) / (1 + cfg.beta) := by
        exact div_nonneg (by linarith [cfg.beta_mem.2]) (by linarith [cfg.beta_mem.1])
      constructor
      · exact hbase_int
      · simpa using le_trans hbase_bound (le_add_of_nonneg_left (mul_nonneg hcoef hB))
  | succ t ih =>
      have hrec :=
        stochasticMuon_comparatorError_sq_recurrence
          P cfg t sigma hvariance ih.1
      have hnoise :=
        stochasticMuon_batchNoise_sq_integrable_and_equation_13
          P cfg (t + 1) sigma hvariance
      constructor
      · exact hrec.1
      · rw [hrec.2]
        calc
          cfg.beta ^ 2 *
                ∫ ω,
                    ‖matrixToEuclidean
                      (stochasticMuonComparator P cfg ω t -
                        (stochasticMuonState P cfg ω t).M)‖ ^ 2
                  ∂(samplePathLaw P cfg.batchSize) +
              (1 - cfg.beta) ^ 2 *
                ∫ ω,
                    ‖matrixToEuclidean
                      (stochasticBatchGradient P cfg.batchSize
                          (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) -
                        P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W)‖ ^ 2
                  ∂(samplePathLaw P cfg.batchSize) ≤
              cfg.beta ^ 2 *
                  ((1 - cfg.beta) / (1 + cfg.beta) *
                      (sigma ^ 2 / (cfg.batchSize.val : ℝ)) +
                    cfg.beta ^ (2 * t) *
                      (sigma ^ 2 / (cfg.batchSize.val : ℝ))) +
                (1 - cfg.beta) ^ 2 *
                  (sigma ^ 2 / (cfg.batchSize.val : ℝ)) := by
                    exact add_le_add
                      (mul_le_mul_of_nonneg_left ih.2 (sq_nonneg cfg.beta))
                      (mul_le_mul_of_nonneg_left
                        (by simpa [frobeniusNorm, norm_matrixToEuclidean] using hnoise.2)
                        (sq_nonneg (1 - cfg.beta)))
          _ = (1 - cfg.beta) / (1 + cfg.beta) *
                (sigma ^ 2 / (cfg.batchSize.val : ℝ)) +
              cfg.beta ^ (2 * (t + 1)) *
                (sigma ^ 2 / (cfg.batchSize.val : ℝ)) := by
                    have hden : 1 + cfg.beta ≠ 0 := by
                      linarith [cfg.beta_mem.1]
                    rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add]
                    field_simp [hden]
                    ring

/- Lemma A.4 for the actual Algorithm 1 state.  This is the replacement
   source-stage supplier required by the stochastic convergence proofs. -/
theorem stochasticMuonLemmaA4Bound_of_source_assumptions
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma) :
    stochasticMuonLemmaA4Bound P cfg t sigma := by
  let μ := samplePathLaw P cfg.batchSize
  let Z : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    frobeniusNorm
      (stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M)
  let q : ℝ := (1 - cfg.beta) / (1 + cfg.beta)
  let A : ℝ := Real.sqrt q * sigma / Real.sqrt (cfg.batchSize.val : ℝ)
  let C : ℝ := cfg.beta ^ t * sigma / Real.sqrt (cfg.batchSize.val : ℝ)
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hsq :=
    stochasticMuon_comparatorError_sq_integrable_and_bound
      P cfg t sigma hvariance
  have hZ_sq_int : Integrable (fun ω => Z ω ^ 2) μ := by
    simpa [Z, μ, frobeniusNorm, norm_matrixToEuclidean] using hsq.1
  have hZ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω :=
    Filter.Eventually.of_forall fun _ => by simp [Z, frobeniusNorm]
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (by linarith [cfg.beta_mem.2]) (by linarith [cfg.beta_mem.1])
  have hB : 0 < (cfg.batchSize.val : ℝ) := by
    exact_mod_cast cfg.batchSize.positive
  have hsqrtB : 0 < Real.sqrt (cfg.batchSize.val : ℝ) := Real.sqrt_pos.2 hB
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) hvariance.nonneg) hsqrtB.le
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg
      (mul_nonneg (pow_nonneg cfg.beta_mem.1 _) hvariance.nonneg) hsqrtB.le
  have hpow : (cfg.beta ^ t) ^ 2 = cfg.beta ^ (2 * t) := by
    rw [← pow_mul]
    congr 1
    omega
  have hbudget_eq :
      A ^ 2 + C ^ 2 =
        q * (sigma ^ 2 / (cfg.batchSize.val : ℝ)) +
          cfg.beta ^ (2 * t) * (sigma ^ 2 / (cfg.batchSize.val : ℝ)) := by
    dsimp [A, C]
    rw [div_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt hq,
      Real.sq_sqrt hB.le, hpow]
    field_simp [ne_of_gt hB]
  have hZ_sq_le : ∫ ω, Z ω ^ 2 ∂μ ≤ A ^ 2 + C ^ 2 := by
    rw [hbudget_eq]
    simpa [Z, q, μ, frobeniusNorm, norm_matrixToEuclidean] using hsq.2
  have hZ_meas : AEStronglyMeasurable Z μ :=
    AEStronglyMeasurable.of_integrable_sq_of_nonneg hZ_sq_int hZ_nonneg
  have hsq_l1 : (∫ ω, Z ω ∂μ) ^ 2 ≤ ∫ ω, Z ω ^ 2 ∂μ :=
    sq_integral_le_integral_sq hZ_meas hZ_sq_int
  have hleft_nonneg : 0 ≤ ∫ ω, Z ω ∂μ := integral_nonneg_of_ae hZ_nonneg
  have hsum_sq : A ^ 2 + C ^ 2 ≤ (A + C) ^ 2 := by
    nlinarith
  have hL1 : ∫ ω, Z ω ∂μ ≤ A + C := by
    nlinarith [le_trans hsq_l1 hZ_sq_le]
  simpa [stochasticMuonLemmaA4Bound, Z, A, C, q, μ] using hL1

/- Appendix B.1's first source-facing step: Assumption 3.1 gives the
   pointwise quadratic upper model used at the actual Algorithm 1 update.
   Keeping this statement at the matrix-objective level makes the subsequent
   stochastic proof a summation/integration problem rather than another
   differentiability reconstruction. -/
theorem frobeniusSmooth_quadratic_upper_bound
    {m n : ℕ} (P : Objective m n) {L : ℝ}
    (hsmooth : FrobeniusSmooth P L) (W W' : Mat m n) :
    P.f W' ≤ P.f W + frobeniusInner (P.grad W) (W' - W) +
      (L / 2) * frobeniusNorm (W' - W) ^ 2 := by
  let e : Mat m n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
    matrixEuclideanLinearIsometryEquiv
  let fE : EuclideanSpace ℝ (Fin m × Fin n) → ℝ :=
    fun x => vectorizedObjective P (e.symm x)
  let gradE : EuclideanSpace ℝ (Fin m × Fin n) →
      EuclideanSpace ℝ (Fin m × Fin n) :=
    fun x => e (P.grad (e.symm x))
  have hgrad : ∀ z ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin m × Fin n))),
      HasGradientAt fE (gradE z) z := by
    intro z _hz
    have hbase : DifferentiableAt ℝ (vectorizedObjective P) (e.symm z) :=
      (hsmooth.contDiff.differentiable (by norm_num)) (e.symm z)
    have hcomp := hbase.hasFDerivAt.comp z e.symm.hasFDerivAt
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hcomp using 1
    ext H
    change ⟪e (P.grad (e.symm z)), H⟫_ℝ =
      fderiv ℝ (vectorizedObjective P) (e.symm z) (e.symm H)
    rw [objective_fderiv_apply_eq_frobeniusInner_grad]
    rw [← inner_matrixToEuclidean]
    rfl
  have hmodel :=
    smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
      (Set.univ : Set (EuclideanSpace ℝ (Fin m × Fin n))) fE gradE L
      convex_univ hgrad
      (fun z _hz w _hw => by
        change ‖e (P.grad (e.symm z)) - e (P.grad (e.symm w))‖ ≤
          L * ‖z - w‖
        rw [← e.map_sub, e.norm_map]
        calc
          ‖P.grad (e.symm z) - P.grad (e.symm w)‖ ≤
              L * ‖e.symm z - e.symm w‖ := by
            simpa [frobeniusNorm] using
              hsmooth.lipschitz_grad (e.symm z) (e.symm w)
          _ = L * ‖z - w‖ := by
            rw [← e.symm.map_sub, e.symm.norm_map])
      (Set.mem_univ (e W)) (Set.mem_univ (e W'))
  dsimp [fE, gradE] at hmodel
  simp only [e.symm_apply_apply] at hmodel
  change P.f W' ≤ P.f W +
      ⟪matrixToEuclidean (P.grad W), matrixToEuclidean W' - matrixToEuclidean W⟫_ℝ +
      (L / 2) * ‖matrixToEuclidean W' - matrixToEuclidean W‖ ^ 2 at hmodel
  rw [← matrixToEuclidean_sub, inner_matrixToEuclidean] at hmodel
  rw [norm_matrixToEuclidean] at hmodel
  simpa [frobeniusNorm] using hmodel

/- The literal one-step descent display at the start of Appendix B.1, before
   inserting `M_t` and applying Lemma A.4. -/
theorem theorem_4_1_one_step_frobenius_descent
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {L η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hsmooth : FrobeniusSmooth P.objective L)
    (ω : SamplePath ξ cfg.batchSize) :
    P.objective.f (stochasticMuonState P cfg ω t).W -
        P.objective.f (stochasticMuonState P cfg ω (t + 1)).W ≥
      η * frobeniusInner
        (P.objective.grad (stochasticMuonState P cfg ω t).W)
        (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) -
      (L / 2) * η ^ 2 *
        frobeniusNorm
          (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) ^ 2 := by
  have hstep := frobeniusSmooth_quadratic_upper_bound P.objective hsmooth
    (stochasticMuonState P cfg ω t).W
    (stochasticMuonState P cfg ω (t + 1)).W
  rw [stochasticMuon_W_succ_eq_source_update, hη t ht] at hstep
  have hdiff :
      (stochasticMuonState P cfg ω t).W -
          η • orthogonalizedDirection (stochasticMuonState P cfg ω t).M -
          (stochasticMuonState P cfg ω t).W =
        (-η) • orthogonalizedDirection (stochasticMuonState P cfg ω t).M := by
    ext i j
    simp
  rw [hdiff] at hstep
  rw [show frobeniusInner
        (P.objective.grad (stochasticMuonState P cfg ω t).W)
        ((-η) • orthogonalizedDirection (stochasticMuonState P cfg ω t).M) =
      -η * frobeniusInner
        (P.objective.grad (stochasticMuonState P cfg ω t).W)
        (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) by
      unfold frobeniusInner
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      change
        P.objective.grad (stochasticMuonState P cfg ω t).W i j *
            (-η * orthogonalizedDirection (stochasticMuonState P cfg ω t).M i j) = _
      ring] at hstep
  rw [show frobeniusNorm
        ((-η) • orthogonalizedDirection (stochasticMuonState P cfg ω t).M) ^ 2 =
      η ^ 2 * frobeniusNorm
        (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) ^ 2 by
      rw [frobeniusNorm, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow, sq_abs]
      rfl] at hstep
  have hupdate :
      (stochasticMuonState P cfg ω (t + 1)).W =
        (stochasticMuonState P cfg ω t).W -
          η • orthogonalizedDirection (stochasticMuonState P cfg ω t).M := by
    rw [stochasticMuon_W_succ_eq_source_update, hη t ht]
  rw [hupdate]
  nlinarith

theorem frobeniusSmooth_mul_sqrt_rankBound_nonneg
    {m n : ℕ} {P : Objective m n} {L : ℝ}
    (hsmooth : FrobeniusSmooth P L) :
    0 ≤ L * Real.sqrt (matrixRankBound m n : ℝ) := by
  by_cases hr : matrixRankBound m n = 0
  · simp [hr]
  · have hrpos : 0 < matrixRankBound m n := Nat.pos_of_ne_zero hr
    have hmn : 0 < m ∧ 0 < n := by
      exact ⟨lt_of_lt_of_le hrpos (Nat.min_le_left m n),
        lt_of_lt_of_le hrpos (Nat.min_le_right m n)⟩
    let i : Fin m := ⟨0, hmn.1⟩
    let j : Fin n := ⟨0, hmn.2⟩
    let E : Mat m n := coordinateMatrix i j
    have hE_ne : E ≠ 0 := by
      intro hzero
      have happ := congrFun (congrFun hzero i) j
      simp [E, coordinateMatrix] at happ
    have hE_pos : 0 < frobeniusNorm (E - 0) := by
      simpa [frobeniusNorm] using (norm_pos_iff.mpr hE_ne)
    have hprod : 0 ≤ L * frobeniusNorm (E - 0) :=
      le_trans (norm_nonneg _) (hsmooth.lipschitz_grad E 0)
    have hL : 0 ≤ L := nonneg_of_mul_nonneg_left hprod hE_pos
    exact mul_nonneg hL (Real.sqrt_nonneg _)

/- Appendix B.1, steps 7--13.  This is the deterministic comparator lag,
   proved pathwise for the actual random iterates. -/
theorem theorem_4_1_comparator_lag_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {L η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hηpos : 0 < η)
    (hsmooth : FrobeniusSmooth P.objective L)
    (ω : SamplePath ξ cfg.batchSize) :
    frobeniusNorm
        (P.objective.grad (stochasticMuonState P cfg ω t).W -
          stochasticMuonComparator P cfg ω t) ≤
      Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η /
        (1 - cfg.beta) := by
  have hLr : 0 ≤ L * Real.sqrt (matrixRankBound m n : ℝ) :=
    frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth
  have hβ0 : 0 ≤ cfg.beta := cfg.beta_mem.1
  have hβ1 : cfg.beta < 1 := cfg.beta_mem.2
  have hden : 0 < 1 - cfg.beta := sub_pos.mpr hβ1
  induction t with
  | zero =>
      simp [stochasticMuonState, stochasticMuonBaseState,
        stochasticMuonComparator, frobeniusNorm]
      have hnum :
          0 ≤ Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η := by
        rw [show Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η =
          (cfg.beta * η) * (L * Real.sqrt (matrixRankBound m n : ℝ)) by ring]
        exact mul_nonneg (mul_nonneg hβ0 hηpos.le) hLr
      exact div_nonneg hnum hden.le
  | succ t ih =>
      have htT : t < T := lt_trans (Nat.lt_succ_self t) (Finset.mem_range.mp ht)
      have htmem : t ∈ Finset.range T := Finset.mem_range.mpr htT
      have hstep := hη t htmem
      have hdir := frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
        (orthogonalizedDirection_isThinSVDWithPolar
          (stochasticMuonState P cfg ω t).M)
      have hWdiff :
          frobeniusNorm
              ((stochasticMuonState P cfg ω (t + 1)).W -
                (stochasticMuonState P cfg ω t).W) ≤
            η * Real.sqrt (matrixRankBound m n : ℝ) := by
        rw [stochasticMuon_W_succ_eq_source_update, hstep]
        have heq :
            (stochasticMuonState P cfg ω t).W -
                  η • orthogonalizedDirection (stochasticMuonState P cfg ω t).M -
                (stochasticMuonState P cfg ω t).W =
              (-η) • orthogonalizedDirection (stochasticMuonState P cfg ω t).M := by
          module
        rw [heq, frobeniusNorm, norm_smul, Real.norm_eq_abs, abs_neg,
          abs_of_pos hηpos]
        exact mul_le_mul_of_nonneg_left hdir hηpos.le
      have hgrad :
          frobeniusNorm
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                P.objective.grad (stochasticMuonState P cfg ω t).W) ≤
            L * η * Real.sqrt (matrixRankBound m n : ℝ) := by
        calc
          _ ≤ L * frobeniusNorm
              ((stochasticMuonState P cfg ω (t + 1)).W -
                (stochasticMuonState P cfg ω t).W) :=
              hsmooth.lipschitz_grad _ _
          _ ≤ L * (η * Real.sqrt (matrixRankBound m n : ℝ)) := by
              by_cases hr : Real.sqrt (matrixRankBound m n : ℝ) = 0
              · have hwzero :
                    frobeniusNorm
                        ((stochasticMuonState P cfg ω (t + 1)).W -
                          (stochasticMuonState P cfg ω t).W) = 0 :=
                  le_antisymm (by simpa [hr] using hWdiff) (by simp [frobeniusNorm])
                rw [hwzero, hr]
                norm_num
              · have hsqrt : 0 < Real.sqrt (matrixRankBound m n : ℝ) :=
                  lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)
                have hL : 0 ≤ L := nonneg_of_mul_nonneg_left hLr hsqrt
                exact mul_le_mul_of_nonneg_left hWdiff hL
          _ = L * η * Real.sqrt (matrixRankBound m n : ℝ) := by ring
      have hlag_triangle :
          frobeniusNorm
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t) ≤
            frobeniusNorm
                (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                  P.objective.grad (stochasticMuonState P cfg ω t).W) +
              frobeniusNorm
                (P.objective.grad (stochasticMuonState P cfg ω t).W -
                  stochasticMuonComparator P cfg ω t) := by
        simpa [frobeniusNorm, sub_add_sub_cancel] using
          norm_add_le
            (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
              P.objective.grad (stochasticMuonState P cfg ω t).W)
            (P.objective.grad (stochasticMuonState P cfg ω t).W -
              stochasticMuonComparator P cfg ω t)
      rw [stochasticMuonComparator_succ]
      have hfactor :
          P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
              (cfg.beta • stochasticMuonComparator P cfg ω t +
                (1 - cfg.beta) •
                  P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W) =
            cfg.beta •
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t) := by
        module
      rw [hfactor, frobeniusNorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0]
      have hpre :
          frobeniusNorm
              (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
                stochasticMuonComparator P cfg ω t) ≤
            L * η * Real.sqrt (matrixRankBound m n : ℝ) +
              Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η /
                (1 - cfg.beta) :=
        le_trans hlag_triangle (add_le_add hgrad (ih htmem))
      have hmul := mul_le_mul_of_nonneg_left hpre hβ0
      calc
        cfg.beta * frobeniusNorm
            (P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W -
              stochasticMuonComparator P cfg ω t) ≤
          cfg.beta *
            (L * η * Real.sqrt (matrixRankBound m n : ℝ) +
              Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η /
                (1 - cfg.beta)) := hmul
        _ = Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η /
              (1 - cfg.beta) := by
          field_simp [ne_of_gt hden]
          ring

/- Appendix B.1, step 14: combine the exact stochastic Lemma A.4 term with
   the pathwise comparator lag.  The explicit call below keeps this theorem on
   the source-formula route rather than the retired aggregate-wrapper route. -/
theorem theorem_4_1_combined_tracking_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {L σ η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hηpos : 0 < η)
    (hsmooth : FrobeniusSmooth P.objective L)
    (hvariance : BoundedVariance P σ) :
    Integrable (fun ω =>
        frobeniusNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M))
      (samplePathLaw P cfg.batchSize) ∧
      (∫ ω,
        frobeniusNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M)
      ∂(samplePathLaw P cfg.batchSize)) ≤
      Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
          Real.sqrt (cfg.batchSize.val : ℝ) +
        cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ) +
        Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η /
          (1 - cfg.beta) := by
  let μ := samplePathLaw P cfg.batchSize
  let D : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    P.objective.grad (stochasticMuonState P cfg ω t).W -
      stochasticMuonComparator P cfg ω t
  let E : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M
  let Z : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    P.objective.grad (stochasticMuonState P cfg ω t).W -
      (stochasticMuonState P cfg ω t).M
  let K : ℝ := Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η /
    (1 - cfg.beta)
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hpast_le : stochasticSampleStrictPast cfg.batchSize (t + 1) ≤
      (by infer_instance : MeasurableSpace (SamplePath ξ cfg.batchSize)) := by
    unfold stochasticSampleStrictPast
    refine iSup_le fun q => iSup_le fun _hq => ?_
    have hcoord : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => ω q.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    exact hcoord.comap_le
  have hC_meas : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonComparator P cfg ω t) :=
    (stochasticMuonComparator_strictPast_measurable P cfg t).mono hpast_le le_rfl
  have hW_meas := stochasticMuon_W_measurable P cfg t
  have hM_meas := stochasticMuon_M_measurable P cfg t
  have hD_meas : Measurable D := by
    exact (P.objective.grad_measurable.comp hW_meas).sub hC_meas
  have hE_meas : Measurable E := by
    exact hC_meas.sub hM_meas
  have hZ_meas : Measurable Z := by
    exact (P.objective.grad_measurable.comp hW_meas).sub hM_meas
  have hlag : ∀ ω, frobeniusNorm (D ω) ≤ K := by
    intro ω
    exact theorem_4_1_comparator_lag_bound P cfg ht hη hηpos hsmooth ω
  have hK : 0 ≤ K := by
    have hLr := frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth
    have hnum :
        0 ≤ Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η := by
      rw [show Real.sqrt (matrixRankBound m n : ℝ) * cfg.beta * L * η =
        (cfg.beta * η) * (L * Real.sqrt (matrixRankBound m n : ℝ)) by ring]
      exact mul_nonneg (mul_nonneg cfg.beta_mem.1 hηpos.le) hLr
    exact div_nonneg hnum (sub_nonneg.mpr cfg.beta_mem.2.le)
  have hD_int : Integrable D μ :=
    Integrable.of_bound hD_meas.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun ω => by simpa [D, frobeniusNorm] using hlag ω)
  have hEsq :=
    (stochasticMuon_comparatorError_sq_integrable_and_bound
      P cfg t σ hvariance).1
  have hE_int : Integrable E μ := by
    apply integrable_of_integrable_norm_sq hE_meas.aestronglyMeasurable
    simpa [E, μ, frobeniusNorm, norm_matrixToEuclidean] using hEsq
  have hZE : ∀ ω, Z ω = D ω + E ω := by
    intro ω
    dsimp [Z, D, E]
    abel
  have hZ_int : Integrable Z μ :=
    (hD_int.add hE_int).congr (Filter.Eventually.of_forall fun ω => (hZE ω).symm)
  have hpoint : ∀ ω, frobeniusNorm (Z ω) ≤
      frobeniusNorm (D ω) + frobeniusNorm (E ω) := by
    intro ω
    rw [hZE]
    simpa [frobeniusNorm] using norm_add_le (D ω) (E ω)
  have hnorm_le :
      (∫ ω, frobeniusNorm (Z ω) ∂μ) ≤
        ∫ ω, frobeniusNorm (D ω) + frobeniusNorm (E ω) ∂μ := by
    apply integral_mono hZ_int.norm (hD_int.norm.add hE_int.norm)
    exact hpoint
  have hD_integral : (∫ ω, frobeniusNorm (D ω) ∂μ) ≤ K := by
    calc
      (∫ ω, frobeniusNorm (D ω) ∂μ) ≤ ∫ _ω, K ∂μ := by
        apply integral_mono hD_int.norm (integrable_const K)
        exact hlag
      _ = K := by simp
  have hA4 := stochasticMuonLemmaA4Bound_of_source_assumptions
    P cfg t σ hvariance
  have hE_integral :
      (∫ ω, frobeniusNorm (E ω) ∂μ) ≤
        Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ) +
          cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ) := by
    simpa [stochasticMuonLemmaA4Bound, E, μ] using hA4
  have hadd :
      (∫ ω, frobeniusNorm (D ω) + frobeniusNorm (E ω) ∂μ) =
        (∫ ω, frobeniusNorm (D ω) ∂μ) +
          ∫ ω, frobeniusNorm (E ω) ∂μ := by
    simpa [frobeniusNorm] using integral_add hD_int.norm hE_int.norm
  rw [hadd] at hnorm_le
  have hcombined := le_trans hnorm_le (add_le_add hD_integral hE_integral)
  refine ⟨?_, ?_⟩
  · simpa [Z, μ, frobeniusNorm] using hZ_int.norm
  · simpa [Z, D, E, K, μ, add_assoc, add_left_comm, add_comm] using hcombined

theorem orthonormalColumns_bessel_bound
    {rows cols : ℕ} (Q : Matrix (Fin rows) (Fin cols) ℝ)
    (hQ : OrthonormalColumns Q) (x : EuclideanSpace ℝ (Fin rows)) :
    (∑ j : Fin cols,
      (inner ℝ x (WithLp.toLp 2 (fun a : Fin rows => Q a j))) ^ 2) ≤ ‖x‖ ^ 2 := by
  classical
  let q : Fin cols → EuclideanSpace ℝ (Fin rows) :=
    fun j => WithLp.toLp 2 (fun a : Fin rows => Q a j)
  have hq : Orthonormal ℝ q := by
    rw [orthonormal_iff_ite]
    intro i j
    calc
      inner ℝ (q i) (q j) =
          ∑ a : Fin rows, inner ℝ (Q a i) (Q a j) := by
            rw [PiLp.inner_apply]
      _ = ∑ a : Fin rows, Q a i * Q a j := by
            apply Finset.sum_congr rfl
            intro a _ha
            calc
              inner ℝ (Q a i) (Q a j) = Q a j * Q a i := by
                exact RCLike.inner_apply (Q a i) (Q a j)
              _ = Q a i * Q a j := by ring
      _ = if i = j then 1 else 0 := hQ i j
  have hb := hq.sum_inner_products_le x (s := Finset.univ)
  simpa [q, Real.norm_eq_abs, sq_abs, real_inner_comm] using hb

theorem abs_sum_column_inner_mul_column_inner_le_one
    {rows₁ rows₂ modes cols : ℕ}
    (XU : Matrix (Fin rows₁) (Fin modes) ℝ)
    (XV : Matrix (Fin rows₂) (Fin modes) ℝ)
    (U : Matrix (Fin rows₁) (Fin cols) ℝ)
    (V : Matrix (Fin rows₂) (Fin cols) ℝ)
    (hXU : OrthonormalColumns XU) (hXV : OrthonormalColumns XV)
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V)
    (i : Fin modes) :
    |∑ j : Fin cols,
      inner ℝ (WithLp.toLp 2 (fun a : Fin rows₁ => XU a i))
          (WithLp.toLp 2 (fun a : Fin rows₁ => U a j)) *
        inner ℝ (WithLp.toLp 2 (fun b : Fin rows₂ => XV b i))
          (WithLp.toLp 2 (fun b : Fin rows₂ => V b j))| ≤ 1 := by
  classical
  let xU : EuclideanSpace ℝ (Fin rows₁) :=
    WithLp.toLp 2 (fun a : Fin rows₁ => XU a i)
  let xV : EuclideanSpace ℝ (Fin rows₂) :=
    WithLp.toLp 2 (fun b : Fin rows₂ => XV b i)
  let cU : EuclideanSpace ℝ (Fin cols) :=
    WithLp.toLp 2 (fun j : Fin cols =>
      inner ℝ xU (WithLp.toLp 2 (fun a : Fin rows₁ => U a j)))
  let cV : EuclideanSpace ℝ (Fin cols) :=
    WithLp.toLp 2 (fun j : Fin cols =>
      inner ℝ xV (WithLp.toLp 2 (fun b : Fin rows₂ => V b j)))
  have hxU_sq : ‖xU‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [xU, Real.norm_eq_abs, sq_abs, pow_two] using hXU i i
  have hxV_sq : ‖xV‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [xV, Real.norm_eq_abs, sq_abs, pow_two] using hXV i i
  have hcU_sq : ‖cU‖ ^ 2 ≤ 1 := by
    calc
      ‖cU‖ ^ 2 = ∑ j : Fin cols,
          (inner ℝ xU (WithLp.toLp 2 (fun a : Fin rows₁ => U a j))) ^ 2 := by
            simp [cU, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
      _ ≤ ‖xU‖ ^ 2 := orthonormalColumns_bessel_bound U hU xU
      _ = 1 := hxU_sq
  have hcV_sq : ‖cV‖ ^ 2 ≤ 1 := by
    calc
      ‖cV‖ ^ 2 = ∑ j : Fin cols,
          (inner ℝ xV (WithLp.toLp 2 (fun b : Fin rows₂ => V b j))) ^ 2 := by
            simp [cV, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
      _ ≤ ‖xV‖ ^ 2 := orthonormalColumns_bessel_bound V hV xV
      _ = 1 := hxV_sq
  have hcU : ‖cU‖ ≤ 1 := by
    nlinarith [norm_nonneg cU]
  have hcV : ‖cV‖ ≤ 1 := by
    nlinarith [norm_nonneg cV]
  have hcoeff :
      inner ℝ cU cV = ∑ j : Fin cols,
        inner ℝ xU (WithLp.toLp 2 (fun a : Fin rows₁ => U a j)) *
          inner ℝ xV (WithLp.toLp 2 (fun b : Fin rows₂ => V b j)) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    calc
      inner ℝ (cU j) (cV j) = cV j * cU j := by
        exact RCLike.inner_apply (cU j) (cV j)
      _ = inner ℝ xU (WithLp.toLp 2 (fun a : Fin rows₁ => U a j)) *
          inner ℝ xV (WithLp.toLp 2 (fun b : Fin rows₂ => V b j)) := by
            simp only [cU, cV]
            ring
  calc
    |∑ j : Fin cols,
        inner ℝ (WithLp.toLp 2 (fun a : Fin rows₁ => XU a i))
            (WithLp.toLp 2 (fun a : Fin rows₁ => U a j)) *
          inner ℝ (WithLp.toLp 2 (fun b : Fin rows₂ => XV b i))
            (WithLp.toLp 2 (fun b : Fin rows₂ => V b j))| =
        |inner ℝ cU cV| := by simp only [xU, xV, hcoeff]
    _ ≤ ‖cU‖ * ‖cV‖ := abs_real_inner_le_norm cU cV
    _ ≤ 1 * 1 := mul_le_mul hcU hcV (norm_nonneg cV) (by norm_num)
    _ = 1 := by norm_num

theorem frobeniusInner_thin_factorization_mul_transpose_eq
    {m n r k : ℕ}
    (XU : Matrix (Fin m) (Fin r) ℝ) (XV : Matrix (Fin n) (Fin r) ℝ)
    (s : Fin r → ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) :
    frobeniusInner (XU * Matrix.diagonal s * XVᵀ) (U * Vᵀ) =
      ∑ i : Fin r, s i *
        ∑ j : Fin k,
          (∑ a : Fin m, XU a i * U a j) *
            (∑ b : Fin n, XV b i * V b j) := by
  classical
  rw [frobeniusInner_eq_trace_transpose_mul]
  calc
    Matrix.trace ((XU * Matrix.diagonal s * XVᵀ)ᵀ * (U * Vᵀ)) =
        Matrix.trace ((XV * Matrix.diagonal s * XUᵀ) * (U * Vᵀ)) := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Matrix.trace ((XV * Matrix.diagonal s * XUᵀ * U) * Vᵀ) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (Vᵀ * (XV * Matrix.diagonal s * XUᵀ * U)) := by
          exact Matrix.trace_mul_comm (XV * Matrix.diagonal s * XUᵀ * U) Vᵀ
    _ = Matrix.trace ((Vᵀ * XV) * Matrix.diagonal s * (XUᵀ * U)) := by
          simp [Matrix.mul_assoc]
    _ = ∑ i : Fin r, s i *
        ∑ j : Fin k,
          (∑ a : Fin m, XU a i * U a j) *
            (∑ b : Fin n, XV b i * V b j) := by
          simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
            Matrix.transpose_apply]
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro b _hb
          ring

theorem abs_frobeniusInner_orthonormal_factors_le_nuclearNorm
    {m n k : ℕ} (X : Mat m n)
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V) :
    |frobeniusInner X (U * Vᵀ)| ≤ nuclearNorm X := by
  classical
  rcases thin_svd_singular_values_data_exists X with
    ⟨XU, XV, hXU, hXV, hs, hX⟩
  rw [show frobeniusInner X (U * Vᵀ) =
      frobeniusInner
        (XU * Matrix.diagonal
          (fun i : Fin X.rank =>
            (Matrix.toEuclideanLin (𝕜 := ℝ) X).singularValues i) * XVᵀ)
        (U * Vᵀ) by
          exact congrArg (fun M : Mat m n => frobeniusInner M (U * Vᵀ)) hX]
  rw [frobeniusInner_thin_factorization_mul_transpose_eq,
    nuclearNorm_eq_sum_rank_singularValues]
  calc
    |∑ i : Fin X.rank,
        (Matrix.toEuclideanLin (𝕜 := ℝ) X).singularValues i *
          ∑ j : Fin k,
            (∑ a : Fin m, XU a i * U a j) *
              (∑ b : Fin n, XV b i * V b j)| ≤
        ∑ i : Fin X.rank,
          |(Matrix.toEuclideanLin (𝕜 := ℝ) X).singularValues i *
            ∑ j : Fin k,
              (∑ a : Fin m, XU a i * U a j) *
                (∑ b : Fin n, XV b i * V b j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin X.rank,
        (Matrix.toEuclideanLin (𝕜 := ℝ) X).singularValues i := by
      apply Finset.sum_le_sum
      intro i _hi
      have hcoeff :
          |∑ j : Fin k,
              (∑ a : Fin m, XU a i * U a j) *
                (∑ b : Fin n, XV b i * V b j)| ≤ 1 := by
        have hraw_inner :
            (∑ j : Fin k,
                (∑ a : Fin m, XU a i * U a j) *
                  (∑ b : Fin n, XV b i * V b j)) =
              ∑ j : Fin k,
                inner ℝ (WithLp.toLp 2 (fun a : Fin m => XU a i))
                    (WithLp.toLp 2 (fun a : Fin m => U a j)) *
                  inner ℝ (WithLp.toLp 2 (fun b : Fin n => XV b i))
                    (WithLp.toLp 2 (fun b : Fin n => V b j)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          have hleft :
              (∑ a : Fin m, XU a i * U a j) =
                inner ℝ (WithLp.toLp 2 (fun a : Fin m => XU a i))
                  (WithLp.toLp 2 (fun a : Fin m => U a j)) := by
            rw [PiLp.inner_apply]
            apply Finset.sum_congr rfl
            intro a _ha
            calc
              XU a i * U a j = U a j * XU a i := by ring
              _ = inner ℝ (XU a i) (U a j) := by
                exact (RCLike.inner_apply (XU a i) (U a j)).symm
          have hright :
              (∑ b : Fin n, XV b i * V b j) =
                inner ℝ (WithLp.toLp 2 (fun b : Fin n => XV b i))
                  (WithLp.toLp 2 (fun b : Fin n => V b j)) := by
            rw [PiLp.inner_apply]
            apply Finset.sum_congr rfl
            intro b _hb
            calc
              XV b i * V b j = V b j * XV b i := by ring
              _ = inner ℝ (XV b i) (V b j) := by
                exact (RCLike.inner_apply (XV b i) (V b j)).symm
          rw [hleft, hright]
        rw [hraw_inner]
        exact abs_sum_column_inner_mul_column_inner_le_one
          XU XV U V hXU hXV hU hV i
      rw [abs_mul, abs_of_nonneg (hs i)]
      exact mul_le_of_le_one_right (hs i) hcoeff

theorem abs_frobeniusInner_orthogonalizedDirection_le_nuclearNorm
    {m n : ℕ} (X M : Mat m n) :
    |frobeniusInner X (orthogonalizedDirection M)| ≤ nuclearNorm X := by
  rcases orthogonalizedDirection_isThinSVDWithPolar M with
    ⟨U, V, _s, hU, hV, _hs, _hM, hpolar⟩
  rw [hpolar]
  exact abs_frobeniusInner_orthonormal_factors_le_nuclearNorm X U V hU hV

/- Exact local API leaf exposed by the source proof: `nuclearNorm` is encoded
   as the finite sum of Mathlib singular values, while the imported singular-
   value API currently has no sum-level triangle theorem.  This is the sole
   norm-theoretic leaf needed by Appendix B.1 step 5, and is immediately
   consumed below. -/
theorem nuclearNorm_sub_triangle
    {m n : ℕ} (A B : Mat m n) :
    nuclearNorm A ≤ nuclearNorm B + nuclearNorm (A - B) := by
  classical
  rcases orthogonalizedDirection_isThinSVDWithPolar A with
    ⟨U, V, _s, hU, hV, _hs, _hA, hpolar⟩
  have hsupport : ∀ X : Mat m n,
      |frobeniusInner X (orthogonalizedDirection A)| ≤ nuclearNorm X := by
    intro X
    rw [hpolar]
    exact abs_frobeniusInner_orthonormal_factors_le_nuclearNorm X U V hU hV
  have hB :
      frobeniusInner B (orthogonalizedDirection A) ≤ nuclearNorm B :=
    le_trans (le_abs_self _) (hsupport B)
  have hAB :
      frobeniusInner (A - B) (orthogonalizedDirection A) ≤ nuclearNorm (A - B) :=
    le_trans (le_abs_self _) (hsupport (A - B))
  have hsplit :
      frobeniusInner A (orthogonalizedDirection A) =
        frobeniusInner B (orthogonalizedDirection A) +
          frobeniusInner (A - B) (orthogonalizedDirection A) := by
    unfold frobeniusInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp
    ring
  calc
    nuclearNorm A = frobeniusInner A (orthogonalizedDirection A) :=
      (orthogonalizedDirection_frobeniusInner_eq_nuclearNorm A).symm
    _ = frobeniusInner B (orthogonalizedDirection A) +
        frobeniusInner (A - B) (orthogonalizedDirection A) := hsplit
    _ ≤ nuclearNorm B + nuclearNorm (A - B) := add_le_add hB hAB

theorem nuclearNorm_neg_eq {m n : ℕ} (A : Mat m n) :
    nuclearNorm (-A) = nuclearNorm A := by
  classical
  have hle (X : Mat m n) : nuclearNorm (-X) ≤ nuclearNorm X := by
    rcases orthogonalizedDirection_isThinSVDWithPolar (-X) with
      ⟨U, V, _s, hU, hV, _hs, _hX, hpolar⟩
    have hsupport :
        |frobeniusInner X (orthogonalizedDirection (-X))| ≤ nuclearNorm X := by
      rw [hpolar]
      exact abs_frobeniusInner_orthonormal_factors_le_nuclearNorm X U V hU hV
    calc
      nuclearNorm (-X) =
          frobeniusInner (-X) (orthogonalizedDirection (-X)) :=
        (orthogonalizedDirection_frobeniusInner_eq_nuclearNorm (-X)).symm
      _ = -frobeniusInner X (orthogonalizedDirection (-X)) := by
        unfold frobeniusInner
        change
          (∑ i, ∑ j, (-X i j) * orthogonalizedDirection (-X) i j) =
            -(∑ i, ∑ j, X i j * orthogonalizedDirection (-X) i j)
        simp only [neg_mul]
        rw [← Finset.sum_neg_distrib]
        simp_rw [Finset.sum_neg_distrib]
      _ ≤ |frobeniusInner X (orthogonalizedDirection (-X))| :=
        neg_le_abs _
      _ ≤ nuclearNorm X := hsupport
  apply le_antisymm (hle A)
  have h := hle (-A)
  have hnn : -(-A) = A := by
    ext i j
    simp
  rw [hnn] at h
  exact h

theorem nuclearNorm_smul_le_of_nonneg
    {m n : ℕ} (c : ℝ) (A : Mat m n) (hc : 0 ≤ c) :
    nuclearNorm (c • A) ≤ c * nuclearNorm A := by
  classical
  rcases orthogonalizedDirection_isThinSVDWithPolar (c • A) with
    ⟨U, V, _s, hU, hV, _hs, _hA, hpolar⟩
  have hsupport :
      |frobeniusInner A (orthogonalizedDirection (c • A))| ≤ nuclearNorm A := by
    rw [hpolar]
    exact abs_frobeniusInner_orthonormal_factors_le_nuclearNorm A U V hU hV
  have hpair :
      frobeniusInner (c • A) (orthogonalizedDirection (c • A)) =
        c * frobeniusInner A (orthogonalizedDirection (c • A)) := by
    unfold frobeniusInner
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  calc
    nuclearNorm (c • A) =
        frobeniusInner (c • A) (orthogonalizedDirection (c • A)) :=
      (orthogonalizedDirection_frobeniusInner_eq_nuclearNorm (c • A)).symm
    _ = c * frobeniusInner A (orthogonalizedDirection (c • A)) := hpair
    _ ≤ c * |frobeniusInner A (orthogonalizedDirection (c • A))| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hc
    _ ≤ c * nuclearNorm A := mul_le_mul_of_nonneg_left hsupport hc

theorem nuclearNorm_sub_le {m n : ℕ} (A B : Mat m n) :
    nuclearNorm (A - B) ≤ nuclearNorm A + nuclearNorm B := by
  have h := nuclearNorm_sub_triangle (A - B) A
  have hdiff : (A - B) - A = -B := by module
  rw [hdiff, nuclearNorm_neg_eq] at h
  exact h

theorem nuclearNorm_add_le {m n : ℕ} (A B : Mat m n) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  have h := nuclearNorm_sub_le A (-B)
  have hadd : A - (-B) = A + B := by module
  rw [hadd, nuclearNorm_neg_eq] at h
  exact h

/- Appendix B.1, steps 1--5, in the exact source formula after inserting the
   momentum and using the polar pairing and rank bound. -/
theorem theorem_4_1_one_step_descent_with_tracking
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {L η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hηpos : 0 < η)
    (hsmooth : FrobeniusSmooth P.objective L)
    (ω : SamplePath ξ cfg.batchSize) :
    P.objective.f (stochasticMuonState P cfg ω t).W -
        P.objective.f (stochasticMuonState P cfg ω (t + 1)).W ≥
      η * nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W) -
        ((matrixRankBound m n : ℝ) * L / 2) * η ^ 2 -
        2 * η * Real.sqrt (matrixRankBound m n : ℝ) *
          frobeniusNorm
            (P.objective.grad (stochasticMuonState P cfg ω t).W -
              (stochasticMuonState P cfg ω t).M) := by
  let G := P.objective.grad (stochasticMuonState P cfg ω t).W
  let M := (stochasticMuonState P cfg ω t).M
  let D := orthogonalizedDirection M
  let E := G - M
  have hbase := theorem_4_1_one_step_frobenius_descent
    P cfg ht hη hsmooth ω
  have hDnorm : frobeniusNorm D ≤ Real.sqrt (matrixRankBound m n : ℝ) :=
    frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar M)
  have hEpair :
      -frobeniusNorm E * frobeniusNorm D ≤ frobeniusInner E D := by
    have habs := abs_real_inner_le_norm (matrixToEuclidean E) (matrixToEuclidean D)
    rw [norm_matrixToEuclidean, norm_matrixToEuclidean, inner_matrixToEuclidean] at habs
    nlinarith [neg_abs_le (frobeniusInner E D)]
  have hEpair' :
      -Real.sqrt (matrixRankBound m n : ℝ) * frobeniusNorm E ≤
        frobeniusInner E D := by
    have hEnonneg : 0 ≤ frobeniusNorm E := by simp [frobeniusNorm]
    have hmul := mul_le_mul_of_nonneg_left hDnorm hEnonneg
    nlinarith
  have hnucdiff :
      nuclearNorm (G - M) ≤
        Real.sqrt (matrixRankBound m n : ℝ) * frobeniusNorm E := by
    simpa [E] using nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm (G - M)
  have hnuctri := nuclearNorm_sub_triangle G M
  have hpairM : frobeniusInner M D = nuclearNorm M := by
    exact orthogonalizedDirection_frobeniusInner_eq_nuclearNorm M
  have hsplit : frobeniusInner G D = frobeniusInner M D + frobeniusInner E D := by
    dsimp [E]
    unfold frobeniusInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Matrix.sub_apply]
    ring
  have hpairG :
      nuclearNorm G - 2 * Real.sqrt (matrixRankBound m n : ℝ) * frobeniusNorm E ≤
        frobeniusInner G D := by
    rw [hsplit, hpairM]
    linarith
  have hDsq : frobeniusNorm D ^ 2 ≤ (matrixRankBound m n : ℝ) := by
    have heq := frobeniusNorm_sq_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar M)
    rw [heq]
    exact_mod_cast le_min (Matrix.rank_le_height M) (Matrix.rank_le_width M)
  have hquad :
      (L / 2) * η ^ 2 * frobeniusNorm D ^ 2 ≤
        ((matrixRankBound m n : ℝ) * L / 2) * η ^ 2 := by
    by_cases hr : matrixRankBound m n = 0
    · have hDzero : frobeniusNorm D ^ 2 = 0 := by
        apply le_antisymm
        · simpa [hr] using hDsq
        · positivity
      simp [hr, hDzero]
    · have hsqrt : 0 < Real.sqrt (matrixRankBound m n : ℝ) := by
        exact Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hr)
      have hLr := frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth
      have hL : 0 ≤ L := nonneg_of_mul_nonneg_left hLr hsqrt
      have hcoeff : 0 ≤ (L / 2) * η ^ 2 :=
        mul_nonneg (div_nonneg hL (by norm_num)) (sq_nonneg η)
      calc
        (L / 2) * η ^ 2 * frobeniusNorm D ^ 2 ≤
            (L / 2) * η ^ 2 * (matrixRankBound m n : ℝ) :=
          mul_le_mul_of_nonneg_left hDsq hcoeff
        _ = ((matrixRankBound m n : ℝ) * L / 2) * η ^ 2 := by ring
  change _ ≥ η * nuclearNorm G - _ - 2 * η * Real.sqrt _ * frobeniusNorm E
  change _ ≥ η * frobeniusInner G D - (L / 2) * η ^ 2 * frobeniusNorm D ^ 2 at hbase
  have hpair_scaled := mul_le_mul_of_nonneg_left hpairG hηpos.le
  linarith

/- Appendix B.1, steps 15--16, before the harmless square-root
   normalization used by the displayed RHS.  This theorem directly consumes
   both the literal one-step descent route and the exact combined-tracking
   route, telescopes the objective values, and divides only after forming the
   positive product `T * η`. -/
theorem theorem_4_1_source_average_bound_at_horizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ)
    (hsrc : theorem_4_1_sourceDomain T η)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hsmooth : FrobeniusSmooth P.objective L)
    (hvariance : BoundedVariance P σ) :
    stochasticAverageNuclearGradient P cfg T ≤
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
        (matrixRankBound m n : ℝ) * L * η / 2 +
        2 * Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * Real.sqrt (matrixRankBound m n : ℝ) * σ /
          ((1 - cfg.beta) * (T : ℝ) * Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * (matrixRankBound m n : ℝ) * η * cfg.beta * L /
          (1 - cfg.beta) := by
  let μ := samplePathLaw P cfg.batchSize
  let g : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W)
  let e : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    frobeniusNorm
      (P.objective.grad (stochasticMuonState P cfg ω t).W -
        (stochasticMuonState P cfg ω t).M)
  let d : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    P.objective.f (stochasticMuonState P cfg ω t).W -
      P.objective.f (stochasticMuonState P cfg ω (t + 1)).W
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  let A : ℝ := Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ / Real.sqrt B
  let C : ℝ := σ / Real.sqrt B
  let K : ℝ := Real.sqrt r * cfg.beta * L * η / (1 - cfg.beta)
  let a : ℝ := r * L / 2 * η ^ 2
  let c : ℝ := 2 * η * Real.sqrt r
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  let hregularity : StochasticObjectiveRegularity P.objective := Or.inl ⟨L, hsmooth⟩
  have hsumg_int : Integrable (fun ω => ∑ t ∈ Finset.range T, g t ω) μ := by
    simpa [g, μ, stochasticAverageNuclearGradientWellDefined,
      SOptLib.expectationWellDefined] using
      (stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
        P cfg T σ hregularity hvariance)
  have hg_int : ∀ t ∈ Finset.range T, Integrable (g t) μ := by
    intro t ht
    have hgmeas : Measurable (g t) := by
      exact nuclearNorm_measurable.comp
        (P.objective.grad_measurable.comp (stochasticMuon_W_measurable P cfg t))
    apply hsumg_int.mono' hgmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg_early _)]
    simpa [g] using Finset.single_le_sum
      (fun k _hk => nuclearNorm_nonneg_early
        (P.objective.grad (stochasticMuonState P cfg ω k).W)) ht
  have hdrop_int : ∀ t ∈ Finset.range T, Integrable (d t) μ := by
    intro t ht
    have htlt : t < T := Finset.mem_range.mp ht
    have hleft := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg t σ hregularity hvariance
    have hright := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg (t + 1) σ hregularity hvariance
    have hleft' : Integrable
        (fun ω => P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω t).W) μ := by
      simpa [μ, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using hleft
    have hright' : Integrable
        (fun ω => P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω (t + 1)).W) μ := by
      simpa [μ, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using hright
    apply (hright'.sub hleft').congr
    filter_upwards [] with ω
    dsimp [d]
    ring
  have he_data : ∀ t ∈ Finset.range T,
      Integrable (e t) μ ∧ ∫ ω, e t ω ∂μ ≤ A + (cfg.beta ^ t * C + K) := by
    intro t ht
    have htrack :=
      theorem_4_1_combined_tracking_bound P cfg ht hη hsrc.2 hsmooth hvariance
    refine ⟨by simpa [e, μ] using htrack.1, ?_⟩
    dsimp [e, μ, A, C, K, r, B]
    convert htrack.2 using 1 <;> ring
  have hstep : ∀ t ∈ Finset.range T,
      η * (∫ ω, g t ω ∂μ) ≤
        (∫ ω, d t ω ∂μ) + a + c * (A + (cfg.beta ^ t * C + K)) := by
    intro t ht
    have hpoint : ∀ ω, η * g t ω ≤ d t ω + a + c * e t ω := by
      intro ω
      have hs := theorem_4_1_one_step_descent_with_tracking
        P cfg ht hη hsrc.2 hsmooth ω
      dsimp [g, d, e, a, c, r]
      linarith
    have hint : (∫ ω, η * g t ω ∂μ) ≤
        ∫ ω, d t ω + a + c * e t ω ∂μ := by
      apply integral_mono ((hg_int t ht).const_mul η)
        (((hdrop_int t ht).add (integrable_const a)).add
          ((he_data t ht).1.const_mul c))
      exact hpoint
    rw [integral_const_mul] at hint
    have hrhs :
        (∫ ω, d t ω + a + c * e t ω ∂μ) =
          (∫ ω, d t ω ∂μ) + a + c * (∫ ω, e t ω ∂μ) := by
      calc
        _ = (∫ ω, d t ω + a ∂μ) + ∫ ω, c * e t ω ∂μ := by
          exact integral_add ((hdrop_int t ht).add (integrable_const a))
            ((he_data t ht).1.const_mul c)
        _ = _ := by
          rw [integral_add (hdrop_int t ht) (integrable_const a),
            integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul]
    rw [hrhs] at hint
    have hc : 0 ≤ c := by
      dsimp [c, r]
      exact mul_nonneg (mul_nonneg (by norm_num) hsrc.2.le) (Real.sqrt_nonneg _)
    have herr := mul_le_mul_of_nonneg_left (he_data t ht).2 hc
    exact le_trans hint (by linarith)
  have hsum := Finset.sum_le_sum hstep
  have hsum_g :
      ∑ t ∈ Finset.range T, η * (∫ ω, g t ω ∂μ) =
        η * ∫ ω, ∑ t ∈ Finset.range T, g t ω ∂μ := by
    rw [integral_finset_sum _ hg_int, Finset.mul_sum]
  have hsum_d :
      ∑ t ∈ Finset.range T, (∫ ω, d t ω ∂μ) =
        stochasticExpectedObjectiveDrop P cfg T := by
    rw [← integral_finset_sum _ hdrop_int]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [d, stochasticExpectedObjectiveDrop]
    simpa [stochasticMuonState, stochasticMuonBaseState] using
      (Finset.sum_range_sub'
        (fun t => P.objective.f (stochasticMuonState P cfg ω t).W) T)
  rw [hsum_g] at hsum
  have hgeom : (∑ t ∈ Finset.range T, cfg.beta ^ t) ≤ 1 / (1 - cfg.beta) := by
    have hmul := geom_sum_mul_neg cfg.beta T
    have hpow : 0 ≤ cfg.beta ^ T := pow_nonneg cfg.beta_mem.1 T
    have hden : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
    apply (le_div_iff₀ hden).2
    rw [hmul]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C, B]
    exact div_nonneg hvariance.nonneg (Real.sqrt_nonneg _)
  have hnoise_sum :
      ∑ t ∈ Finset.range T, (a + c * (A + cfg.beta ^ t * C + K)) ≤
        (T : ℝ) * a + c * ((T : ℝ) * A + C / (1 - cfg.beta) + (T : ℝ) * K) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    have hgeomC : (∑ t ∈ Finset.range T, cfg.beta ^ t) * C ≤
        (1 / (1 - cfg.beta)) * C :=
      mul_le_mul_of_nonneg_right hgeom hC
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hc : 0 ≤ c := by
      dsimp [c, r]
      exact mul_nonneg (mul_nonneg (by norm_num) hsrc.2.le) (Real.sqrt_nonneg _)
    have hgeomC' : (∑ t ∈ Finset.range T, cfg.beta ^ t) * C ≤
        C / (1 - cfg.beta) := by
      simpa [div_eq_mul_inv, mul_comm] using hgeomC
    have hinner :
        (T : ℝ) * A + (∑ x ∈ Finset.range T, cfg.beta ^ x) * C + (T : ℝ) * K ≤
          (T : ℝ) * A + C / (1 - cfg.beta) + (T : ℝ) * K := by
      linarith
    rw [← Finset.sum_mul]
    simpa [add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_left hinner hc) ((T : ℝ) * a)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum_d] at hsum
  have hnum :
      η * ∫ ω, ∑ t ∈ Finset.range T, g t ω ∂μ ≤
        stochasticExpectedObjectiveDrop P cfg T +
          (T : ℝ) * a + c * ((T : ℝ) * A + C / (1 - cfg.beta) + (T : ℝ) * K) := by
    have hnoise_sum' :
        (∑ x ∈ Finset.range T, a) +
            ∑ x ∈ Finset.range T, c * (A + (cfg.beta ^ x * C + K)) ≤
          (T : ℝ) * a +
            c * ((T : ℝ) * A + C / (1 - cfg.beta) + (T : ℝ) * K) := by
      simpa [Finset.sum_add_distrib, add_assoc] using hnoise_sum
    exact le_trans hsum (by
      simpa [add_assoc] using
        add_le_add_left hnoise_sum' (stochasticExpectedObjectiveDrop P cfg T))
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hsrc.1.1
  have hTηpos : 0 < (T : ℝ) * η := mul_pos hTpos hsrc.2
  let S : ℝ := ∫ ω, ∑ t ∈ Finset.range T, g t ω ∂μ
  let N : ℝ := stochasticExpectedObjectiveDrop P cfg T +
    (T : ℝ) * a + c * ((T : ℝ) * A + C / (1 - cfg.beta) + (T : ℝ) * K)
  have hnormalized : (T : ℝ)⁻¹ * S ≤ N / ((T : ℝ) * η) := by
    apply (le_div_iff₀ hTηpos).2
    calc
      ((T : ℝ)⁻¹ * S) * ((T : ℝ) * η) = η * S := by
        field_simp [ne_of_gt hTpos]
      _ ≤ N := by simpa [S, N] using hnum
  have heq : N / ((T : ℝ) * η) =
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
        (matrixRankBound m n : ℝ) * L * η / 2 +
        2 * Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * Real.sqrt (matrixRankBound m n : ℝ) * σ /
          ((1 - cfg.beta) * (T : ℝ) * Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * (matrixRankBound m n : ℝ) * η * cfg.beta * L /
          (1 - cfg.beta) := by
    have hrank : 0 ≤ (matrixRankBound m n : ℝ) := by positivity
    have hsqrtB : 0 < Real.sqrt (cfg.batchSize.val : ℝ) := by
      exact Real.sqrt_pos.2 (by exact_mod_cast cfg.batchSize.positive)
    dsimp [N, a, c, A, C, K, r, B]
    field_simp [ne_of_gt hTpos, ne_of_gt hsrc.2,
      ne_of_gt (sub_pos.mpr cfg.beta_mem.2), ne_of_gt hsqrtB]
    ring_nf
    simp [Real.sq_sqrt hrank]
    ring
  change (T : ℝ)⁻¹ * S ≤ _
  exact hnormalized.trans_eq heq

theorem theorem_4_1_source_average_bound_at_horizon_sourceRhs
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ)
    (hsrc : theorem_4_1_sourceDomain T η)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hsmooth : FrobeniusSmooth P.objective L)
    (hvariance : BoundedVariance P σ) :
    stochasticAverageNuclearGradient P cfg T ≤
      theorem_4_1_sourceRhs P cfg T L σ η := by
  have hbound := theorem_4_1_source_average_bound_at_horizon
    P cfg T L σ η hsrc hη hsmooth hvariance
  have hr : 0 ≤ (matrixRankBound m n : ℝ) := by positivity
  have hB : 0 < (cfg.batchSize.val : ℝ) := by
    exact_mod_cast cfg.batchSize.positive
  have hminus : 0 ≤ 1 - cfg.beta := by linarith [cfg.beta_mem.2]
  have hplus : 0 < 1 + cfg.beta := by linarith [cfg.beta_mem.1]
  have hnoise :
      2 * Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) =
        (2 * σ * Real.sqrt
            ((matrixRankBound m n : ℝ) * (1 - cfg.beta))) /
          Real.sqrt ((cfg.batchSize.val : ℝ) * (1 + cfg.beta)) := by
    rw [Real.sqrt_mul hr, Real.sqrt_mul (le_of_lt hB),
      Real.sqrt_div hminus]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hB),
      ne_of_gt (Real.sqrt_pos.2 hplus)]
  unfold theorem_4_1_sourceRhs
  dsimp
  rw [← hnoise]
  convert hbound using 1 <;> ring

theorem deterministicMuonDirection_source_contract {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    IsThinSVDWithPolar ((deterministicMuonState P cfg t).G)
        (deterministicMuonDirection P cfg t) ∧
      frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
          (deterministicMuonDirection P cfg t) =
        nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) ∧
      frobeniusNorm (deterministicMuonDirection P cfg t) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
  have hG :
      (deterministicMuonState P cfg t).G =
        P.grad ((deterministicMuonState P cfg t).W) := by
    simpa [deterministicGradient] using deterministicMuon_G_eq_gradient P cfg t
  have hpolar :
      IsThinSVDWithPolar ((deterministicMuonState P cfg t).G)
        (deterministicMuonDirection P cfg t) := by
    simpa [deterministicMuonDirection] using
      orthogonalizedDirection_isThinSVDWithPolar
        ((deterministicMuonState P cfg t).G)
  have hpair :
      frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
          (deterministicMuonDirection P cfg t) =
        nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) := by
    simpa [deterministicMuonDirection, hG] using
      orthogonalizedDirection_frobeniusInner_eq_nuclearNorm
        ((deterministicMuonState P cfg t).G)
  have hnorm :
      frobeniusNorm (deterministicMuonDirection P cfg t) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    unfold deterministicMuonDirection
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar
        ((deterministicMuonState P cfg t).G))
  exact ⟨hpolar, hpair, hnorm⟩

theorem transpose_mul_self_mul_right_factor_eq_right_mul_diagonal_sq
    {m n k : ℕ} {M : Mat m n}
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (s : Fin k → ℝ) (hU : OrthonormalColumns U) (hV : OrthonormalColumns V)
    (hM : M = U * Matrix.diagonal s * Vᵀ) :
    Mᵀ * M * V = V * Matrix.diagonal (fun i : Fin k => s i ^ 2) := by
  classical
  have hUtU : Uᵀ * U = 1 := transpose_mul_self_eq_one_of_orthonormalColumns U hU
  have hVtV : Vᵀ * V = 1 := transpose_mul_self_eq_one_of_orthonormalColumns V hV
  rw [hM]
  calc
    (U * Matrix.diagonal s * Vᵀ)ᵀ * (U * Matrix.diagonal s * Vᵀ) * V =
        (V * Matrix.diagonal s * Uᵀ) * (U * Matrix.diagonal s * Vᵀ) * V := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = V * Matrix.diagonal s * (Uᵀ * U) * Matrix.diagonal s * (Vᵀ * V) := by
          simp [Matrix.mul_assoc]
    _ = V * Matrix.diagonal s * Matrix.diagonal s := by
          simp [hUtU, hVtV, Matrix.mul_assoc]
    _ = V * Matrix.diagonal (fun i : Fin k => s i ^ 2) := by
          ext i j
          simp [Matrix.mul_apply, Matrix.diagonal, pow_two]
          ring

theorem frobeniusInner_eq_sum_diagonal_of_isThinSVDWithPolar
    {m n : ℕ} {M P : Mat m n} (h : IsThinSVDWithPolar M P) :
    ∃ s : Fin M.rank → ℝ,
      NonnegativeDiagonal s ∧ frobeniusInner M P = ∑ i : Fin M.rank, s i := by
  classical
  rcases h with ⟨U, V, s, hU, hV, hs, hM, hP⟩
  refine ⟨s, hs, ?_⟩
  exact frobeniusInner_factorization_eq_sum_diagonal U V s hU hV hM hP

theorem orthogonalizedDirection_frobeniusNorm_sq {m n : ℕ} (M : Mat m n) :
    frobeniusNorm (orthogonalizedDirection M) ^ 2 = (M.rank : ℝ) :=
  frobeniusNorm_sq_of_isThinSVDWithPolar (orthogonalizedDirection_isThinSVDWithPolar M)

theorem orthogonalizedDirection_frobeniusNorm_le_sqrt_rankBound
    {m n : ℕ} (M : Mat m n) :
    frobeniusNorm (orthogonalizedDirection M) ≤ Real.sqrt (matrixRankBound m n : ℝ) :=
  frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
    (orthogonalizedDirection_isThinSVDWithPolar M)

theorem deterministicMuonDirection_frobeniusNorm_le_sqrt_rankBound
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    frobeniusNorm (deterministicMuonDirection P cfg t) ≤
      Real.sqrt (matrixRankBound m n : ℝ) := by
  exact (deterministicMuonDirection_source_contract P cfg t).2.2

theorem frobeniusInner_fderiv_apply {m n : ℕ} {G : Mat m n → Mat m n}
    (x A B : Mat m n) (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ (fun W => frobeniusInner (G W) B) x A =
      frobeniusInner (fderiv ℝ G x A) B := by
  classical
  let K : Mat m n →ₗ[ℝ] ℝ :=
    { toFun := fun C => frobeniusInner C B
      map_add' := by
        intro C C'
        simp [frobeniusInner, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro c C
        simp only [frobeniusInner, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        change (c * C i j) * B i j = c * (C i j * B i j)
        ring }
  have hK : ∀ C, K C = frobeniusInner C B := by
    intro C
    rfl
  let Kc : Mat m n →L[ℝ] ℝ := K.toContinuousLinearMap
  have hcomp :
      fderiv ℝ (fun W => Kc (G W)) x =
        Kc.comp (fderiv ℝ G x) := by
    exact (Kc.hasFDerivAt.comp x hG.hasFDerivAt).fderiv
  have hfun :
      (fun W => Kc (G W)) = (fun W => frobeniusInner (G W) B) := by
    funext W
    exact hK (G W)
  rw [← hfun, hcomp]
  change K (fderiv ℝ G x A) = _
  exact hK _

theorem second_iterated_derivative_eq_hessian_bilinear_mixed
    {m n : ℕ} (P : Objective m n)
    (hcont : ContDiff ℝ 3 (vectorizedObjective P))
    (x A d : Mat m n) :
    (iteratedFDeriv ℝ 2 (vectorizedObjective P) x) ![d, A] =
      hessianBilinear P x A d := by
  classical
  have hcont' : ContDiff ℝ (2 + 1) (vectorizedObjective P) := by
    simpa using hcont
  have hfd :
      ContDiff ℝ 2 (fderiv ℝ (vectorizedObjective P)) :=
    (contDiff_succ_iff_fderiv.mp hcont').2.2
  have hgrad : ContDiff ℝ 2 P.grad :=
    objective_grad_contDiff_two_of_vectorized_contDiff_three P hcont
  have hsecond :
      fderiv ℝ (fun W => fderiv ℝ (vectorizedObjective P) W A) x d =
        (fderiv ℝ (fderiv ℝ (vectorizedObjective P)) x) d A := by
    have hfderiv :
        HasFDerivAt (fderiv ℝ (vectorizedObjective P))
          (fderiv ℝ (fderiv ℝ (vectorizedObjective P)) x) x :=
      ((hfd.differentiable (by norm_num)) x).hasFDerivAt
    have hconst : HasFDerivAt (fun _ : Mat m n => A)
        (0 : Mat m n →L[ℝ] Mat m n) x :=
      hasFDerivAt_const A x
    have happ := hfderiv.clm_apply hconst
    have happ' := congrArg (fun L => L d) happ.fderiv
    simpa [ContinuousLinearMap.comp_apply] using happ'
  have hpoint :
      (fun W => fderiv ℝ (vectorizedObjective P) W A) =
        (fun W => frobeniusInner (P.grad W) A) := by
    funext W
    exact objective_fderiv_apply_eq_frobeniusInner_grad P W A
  have hpoint' := congrArg (fun φ => fderiv ℝ φ x d) hpoint
  have hpair :
      fderiv ℝ (fun W => frobeniusInner (P.grad W) A) x d =
        frobeniusInner (fderiv ℝ P.grad x d) A :=
    frobeniusInner_fderiv_apply x d A ((hgrad.differentiable (by norm_num)) x)
  rw [iteratedFDeriv_two_apply]
  calc
    (fderiv ℝ (fderiv ℝ (vectorizedObjective P)) x) d A =
        fderiv ℝ (fun W => fderiv ℝ (vectorizedObjective P) W A) x d := by
          symm
          exact hsecond
    _ = fderiv ℝ (fun W => frobeniusInner (P.grad W) A) x d := hpoint'
    _ = frobeniusInner (fderiv ℝ P.grad x d) A := hpair
    _ = hessianBilinear P x A d := by
      rw [hessianBilinear_eq_fderiv_grad_pairing]
      simp [frobeniusInner, mul_comm]

theorem second_iterated_derivative_eq_hessian_bilinear
    {m n : ℕ} (P : Objective m n)
    (hcont : ContDiff ℝ 3 (vectorizedObjective P))
    (x d : Mat m n) :
    (iteratedFDeriv ℝ 2 (vectorizedObjective P) x)
        (fun _ : Fin 2 => d) =
      hessianBilinear P x d d := by
  classical
  have hcont' : ContDiff ℝ (2 + 1) (vectorizedObjective P) := by
    simpa using hcont
  have hfd :
      ContDiff ℝ 2 (fderiv ℝ (vectorizedObjective P)) :=
    (contDiff_succ_iff_fderiv.mp hcont').2.2
  have hgrad : ContDiff ℝ 2 P.grad :=
    objective_grad_contDiff_two_of_vectorized_contDiff_three P hcont
  have hsecond :
      fderiv ℝ (fun W => fderiv ℝ (vectorizedObjective P) W d) x d =
        (fderiv ℝ (fderiv ℝ (vectorizedObjective P)) x) d d := by
    have hfderiv :
        HasFDerivAt (fderiv ℝ (vectorizedObjective P))
          (fderiv ℝ (fderiv ℝ (vectorizedObjective P)) x) x :=
      ((hfd.differentiable (by norm_num)) x).hasFDerivAt
    have hconst : HasFDerivAt (fun _ : Mat m n => d)
        (0 : Mat m n →L[ℝ] Mat m n) x :=
      hasFDerivAt_const d x
    have happ := hfderiv.clm_apply hconst
    have happ' := congrArg (fun L => L d) happ.fderiv
    simpa [ContinuousLinearMap.comp_apply] using happ'
  have hpoint :
      (fun W => fderiv ℝ (vectorizedObjective P) W d) =
        (fun W => frobeniusInner (P.grad W) d) := by
    funext W
    exact objective_fderiv_apply_eq_frobeniusInner_grad P W d
  have hpoint' := congrArg (fun φ => fderiv ℝ φ x d) hpoint
  have hpair :
      fderiv ℝ (fun W => frobeniusInner (P.grad W) d) x d =
        frobeniusInner (fderiv ℝ P.grad x d) d :=
    frobeniusInner_fderiv_apply x d d ((hgrad.differentiable (by norm_num)) x)
  rw [iteratedFDeriv_two_apply]
  calc
    (fderiv ℝ (fderiv ℝ (vectorizedObjective P)) x) d d =
        fderiv ℝ (fun W => fderiv ℝ (vectorizedObjective P) W d) x d := by
          symm
          exact hsecond
    _ = fderiv ℝ (fun W => frobeniusInner (P.grad W) d) x d := hpoint'
    _ = frobeniusInner (fderiv ℝ P.grad x d) d := hpair
    _ = hessianBilinear P x d d := by
      rw [hessianBilinear_eq_fderiv_grad_pairing]
      simp [frobeniusInner, mul_comm]

theorem gradient_pairing_first_order_taylor_remainder_bound
    {m n : ℕ} (P : Objective m n) {s : ℝ}
    (hthird : ThirdDerivativeBounded P s) (x A d : Mat m n) :
    |frobeniusInner (P.grad (x + d)) A -
        frobeniusInner (P.grad x) A - hessianBilinear P x A d| ≤
      s * ‖A‖ * ‖d‖ ^ 2 / 2 := by
  classical
  let base : Mat m n → ℝ := fun z =>
    fderiv ℝ (vectorizedObjective P) z A
  let q : Mat m n → ℝ := fun z => base (x + z)
  let L : ℝ →L[ℝ] Mat m n :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight d
  let g : ℝ → ℝ := fun u => base (x + u • d)
  have hcont : ContDiff ℝ 3 (vectorizedObjective P) := hthird.contDiff
  have hcont' : ContDiff ℝ (2 + 1) (vectorizedObjective P) := by
    simpa using hcont
  have hfd :
      ContDiff ℝ 2 (fderiv ℝ (vectorizedObjective P)) :=
    (contDiff_succ_iff_fderiv.mp hcont').2.2
  have hbase : ContDiff ℝ 2 base := by
    dsimp [base]
    exact hfd.clm_apply contDiff_const
  have hq : ContDiff ℝ 2 q := by
    dsimp [q]
    exact hbase.comp (contDiff_const.add contDiff_id)
  have hg : ContDiff ℝ 2 g := by
    dsimp [g]
    exact hbase.comp (contDiff_const.add (contDiff_smul_const d))
  have hpath_deriv (k : ℕ) (hk : k ≤ 2) (u : ℝ) :
      iteratedDeriv k g u =
        (iteratedFDeriv ℝ k base (x + u • d))
          (fun _ : Fin k => d) := by
    have hcomp :
        iteratedFDeriv ℝ k (q ∘ L) u =
          (iteratedFDeriv ℝ k q (L u)).compContinuousLinearMap
            (fun _ : Fin k => L) :=
      L.iteratedFDeriv_comp_right hq u (by exact_mod_cast hk)
    rw [iteratedDeriv_eq_iteratedFDeriv]
    change
      iteratedFDeriv ℝ k (q ∘ L) u
          (fun _ : Fin k => (1 : ℝ)) = _
    rw [hcomp]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [iteratedFDeriv_comp_add_left]
    simp [g, q, L]
  obtain ⟨u, _hu, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := g) (x := 1) (x₀ := 0) (n := 1) zero_lt_one hg.contDiffOn
  have hpoly :
      taylorWithinEval g 1 (Set.Icc (0 : ℝ) 1) 0 1 =
        g 0 + deriv g 0 := by
    rw [taylor_within_apply]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
      inv_one, one_mul, zero_sub, zero_pow, Nat.succ_ne_zero, smul_eq_mul,
      one_smul, Nat.factorial_one]
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 0)
      (uniqueDiffOn_Icc zero_lt_one)
      ((hg.of_le (by norm_num)).contDiffAt) (by norm_num)]
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1)
      (uniqueDiffOn_Icc zero_lt_one)
      ((hg.of_le (by norm_num)).contDiffAt) (by norm_num)]
    simp only [iteratedDeriv_zero, iteratedDeriv_one]
    norm_num
  rw [hpoly] at hrem
  have hbase_pair :
      base = fun W => frobeniusInner (P.grad W) A := by
    funext W
    exact objective_fderiv_apply_eq_frobeniusInner_grad P W A
  have hbase_deriv := congrArg (fun φ => fderiv ℝ φ x d) hbase_pair
  have hgrad : ContDiff ℝ 2 P.grad :=
    objective_grad_contDiff_two_of_vectorized_contDiff_three P hcont
  have hpair :
      fderiv ℝ (fun W => frobeniusInner (P.grad W) A) x d =
        hessianBilinear P x A d := by
    rw [hessianBilinear_eq_fderiv_grad_pairing]
    simpa [frobeniusInner, mul_comm] using
      frobeniusInner_fderiv_apply x d A
        ((hgrad.differentiable (by norm_num)) x)
  have h1 : deriv g 0 = hessianBilinear P x A d := by
    have hh := hpath_deriv 1 (by norm_num) 0
    rw [iteratedDeriv_one, iteratedFDeriv_one_apply] at hh
    have hbase_deriv' : fderiv ℝ base x d = hessianBilinear P x A d := by
      exact hbase_deriv.trans hpair
    simpa only [zero_smul, add_zero, hbase_deriv'] using hh
  have hbase_second_norm (z : Mat m n) :
      ‖iteratedFDeriv ℝ 2 base z‖ ≤ s * ‖A‖ := by
    have happ :
        ‖iteratedFDeriv ℝ 2 base z‖ ≤
          ‖A‖ * ‖iteratedFDeriv ℝ 2
            (fderiv ℝ (vectorizedObjective P)) z‖ := by
      refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
      have heval := iteratedFDeriv_clm_apply_const_apply
        hfd (i := 2) (by norm_num) (x := z) (u := A) (m := v)
      change
        ‖(iteratedFDeriv ℝ 2 base z) v‖ ≤
          (‖A‖ * ‖iteratedFDeriv ℝ 2
            (fderiv ℝ (vectorizedObjective P)) z‖) * ∏ i, ‖v i‖
      rw [show (iteratedFDeriv ℝ 2 base z) v =
          (iteratedFDeriv ℝ 2 (fderiv ℝ (vectorizedObjective P)) z) v A by
        simpa [base] using heval]
      calc
        ‖(iteratedFDeriv ℝ 2 (fderiv ℝ (vectorizedObjective P)) z) v A‖ ≤
            ‖(iteratedFDeriv ℝ 2 (fderiv ℝ (vectorizedObjective P)) z) v‖ *
              ‖A‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖iteratedFDeriv ℝ 2
              (fderiv ℝ (vectorizedObjective P)) z‖ * ∏ i, ‖v i‖) * ‖A‖ :=
          mul_le_mul_of_nonneg_right
            (ContinuousMultilinearMap.le_opNorm _ _) (norm_nonneg A)
        _ = (‖A‖ * ‖iteratedFDeriv ℝ 2
              (fderiv ℝ (vectorizedObjective P)) z‖) * ∏ i, ‖v i‖ := by ring
    rw [norm_iteratedFDeriv_fderiv] at happ
    calc
      ‖iteratedFDeriv ℝ 2 base z‖ ≤
          ‖A‖ * ‖iteratedFDeriv ℝ 3 (vectorizedObjective P) z‖ := happ
      _ ≤ ‖A‖ * s :=
        mul_le_mul_of_nonneg_left (hthird.bound z) (norm_nonneg A)
      _ = s * ‖A‖ := by ring
  have hsecond :
      ‖iteratedDeriv 2 g u‖ ≤ s * ‖A‖ * ‖d‖ ^ 2 := by
    have hnorm := congrArg norm (hpath_deriv 2 (by norm_num) u)
    calc
      ‖iteratedDeriv 2 g u‖ =
          ‖(iteratedFDeriv ℝ 2 base (x + u • d))
            (fun _ : Fin 2 => d)‖ := hnorm
      _ ≤ ‖iteratedFDeriv ℝ 2 base (x + u • d)‖ *
              ∏ _ : Fin 2, ‖d‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (s * ‖A‖) * ‖d‖ ^ 2 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
        exact hbase_second_norm _
  have hg_one : g 1 = frobeniusInner (P.grad (x + d)) A := by
    simp [g, base, objective_fderiv_apply_eq_frobeniusInner_grad]
  have hg_zero : g 0 = frobeniusInner (P.grad x) A := by
    simp [g, base, objective_fderiv_apply_eq_frobeniusInner_grad]
  norm_num [Nat.factorial] at hrem
  have hremainder :
      frobeniusInner (P.grad (x + d)) A -
          frobeniusInner (P.grad x) A - hessianBilinear P x A d =
        iteratedDeriv 2 g u / 2 := by
    rw [← hg_one, ← hg_zero, ← h1]
    linarith
  rw [hremainder]
  calc
    |iteratedDeriv 2 g u / 2| = ‖iteratedDeriv 2 g u‖ / 2 := by
      rw [abs_div]
      norm_num [Real.norm_eq_abs]
    _ ≤ s * ‖A‖ * ‖d‖ ^ 2 / 2 :=
      div_le_div_of_nonneg_right hsecond (by norm_num)

theorem theorem_4_15_gradient_increment_nuclear_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) {T t : ℕ} {s η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hη_nonneg : 0 ≤ η) :
    nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg ω t).W -
          P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W) ≤
      η * stochasticHessianCrossTerm P cfg ω t +
        s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
  classical
  let Wt := (stochasticMuonState P cfg ω t).W
  let Wnext := (stochasticMuonState P cfg ω (t + 1)).W
  let Dt := stochasticMuonDirection P cfg ω t
  let Dg := stochasticGradientDifferenceDirection P cfg ω t
  let d := Wnext - Wt
  have hupdate : Wnext = Wt - η • Dt := by
    simpa [Wnext, Wt, Dt, stochasticMuonDirection, hη t ht] using
      stochasticMuon_W_succ_eq_source_update P cfg ω t
  have hd : d = (-η) • Dt := by
    change Wnext - Wt = (-η) • Dt
    rw [hupdate]
    ext i j
    simp
  have hDg :
      Dg = orthogonalizedDirection
        (P.objective.grad Wt - P.objective.grad Wnext) := by
    rfl
  have hpair :
      frobeniusInner
          (P.objective.grad Wt - P.objective.grad Wnext) Dg =
        nuclearNorm (P.objective.grad Wt - P.objective.grad Wnext) := by
    rw [hDg]
    exact orthogonalizedDirection_frobeniusInner_eq_nuclearNorm _
  have hDg_norm :
      ‖Dg‖ ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
    simpa [Dg, stochasticGradientDifferenceDirection, Wt, Wnext, frobeniusNorm] using
      orthogonalizedDirection_frobeniusNorm_le_sqrt_rankBound
        (P.objective.grad Wt - P.objective.grad Wnext)
  have hDt_norm :
      ‖Dt‖ ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
    simpa [Dt, stochasticMuonDirection, frobeniusNorm] using
      orthogonalizedDirection_frobeniusNorm_le_sqrt_rankBound
        (stochasticMuonState P cfg ω t).M
  have htaylor :=
    gradient_pairing_first_order_taylor_remainder_bound
      P.objective hthird Wt Dg d
  have hcross :
      stochasticHessianCrossTerm P cfg ω t =
        hessianBilinear P.objective Wt Dg Dt := by
    rfl
  have hHd :
      hessianBilinear P.objective Wt Dg d =
        -η * hessianBilinear P.objective Wt Dg Dt := by
    rw [hd]
    unfold hessianBilinear frobeniusInner
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Matrix.smul_apply]
    simp only [smul_eq_mul]
    ring
  have hr : 0 ≤ (matrixRankBound m n : ℝ) := by positivity
  have hd_norm : ‖d‖ ≤ η * Real.sqrt (matrixRankBound m n : ℝ) := by
    rw [hd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη_nonneg]
    exact mul_le_mul_of_nonneg_left hDt_norm hη_nonneg
  have hrank_product :
      ‖Dg‖ * ‖d‖ ^ 2 ≤
        η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
    calc
      ‖Dg‖ * ‖d‖ ^ 2 ≤
          Real.sqrt (matrixRankBound m n : ℝ) *
            (η * Real.sqrt (matrixRankBound m n : ℝ)) ^ 2 := by
        gcongr
      _ = η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
        have hsqrtcube :
            (Real.sqrt (matrixRankBound m n : ℝ)) ^ 3 =
              Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
          have hs2 : (Real.sqrt (matrixRankBound m n : ℝ)) ^ 2 =
              (matrixRankBound m n : ℝ) := Real.sq_sqrt hr
          have hleft :
              ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 3) ^ 2 =
                (matrixRankBound m n : ℝ) ^ 3 := by
            rw [show ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 3) ^ 2 =
              ((Real.sqrt (matrixRankBound m n : ℝ)) ^ 2) ^ 3 by ring, hs2]
          have hright :
              (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) ^ 2 =
                (matrixRankBound m n : ℝ) ^ 3 :=
            Real.sq_sqrt (by positivity)
          have hsq := hleft.trans hright.symm
          rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
          · exact h
          · have hleft_nonneg :
                0 ≤ (Real.sqrt (matrixRankBound m n : ℝ)) ^ 3 := by positivity
            have hright_nonneg :
                0 ≤ Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) :=
              Real.sqrt_nonneg _
            nlinarith
        rw [← hsqrtcube]
        ring
  have hs : 0 ≤ s :=
    le_trans (norm_nonneg _)
      (hthird.bound Wt)
  have hremainder :
      s * ‖Dg‖ * ‖d‖ ^ 2 / 2 ≤
        s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hrank_product hs
    nlinarith
  let e : ℝ :=
    frobeniusInner (P.objective.grad (Wt + d)) Dg -
      frobeniusInner (P.objective.grad Wt) Dg -
        hessianBilinear P.objective Wt Dg d
  have he_abs : |e| ≤
      s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2 := by
    exact (show |e| ≤ s * ‖Dg‖ * ‖d‖ ^ 2 / 2 by
      simpa [e] using htaylor).trans hremainder
  have hWt_d : Wt + d = Wnext := by
    change Wt + (Wnext - Wt) = Wnext
    abel
  have hinner_sub :
      frobeniusInner
          (P.objective.grad Wt - P.objective.grad Wnext) Dg =
        frobeniusInner (P.objective.grad Wt) Dg -
          frobeniusInner (P.objective.grad Wnext) Dg := by
    unfold frobeniusInner
    change
      (∑ i, ∑ j,
        (P.objective.grad Wt i j - P.objective.grad Wnext i j) * Dg i j) =
      (∑ i, ∑ j, P.objective.grad Wt i j * Dg i j) -
        ∑ i, ∑ j, P.objective.grad Wnext i j * Dg i j
    simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hsplit :
      frobeniusInner
          (P.objective.grad Wt - P.objective.grad Wnext) Dg =
        η * hessianBilinear P.objective Wt Dg Dt - e := by
    rw [hinner_sub]
    dsimp [e]
    rw [hWt_d, hHd]
    ring
  rw [← hpair, hsplit, hcross]
  nlinarith [neg_le_abs e, he_abs]

theorem theorem_4_15_comparator_lag_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {s η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hη_nonneg : 0 ≤ η)
    (ω : SamplePath ξ cfg.batchSize) :
    nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg ω t).W -
          stochasticMuonComparator P cfg ω t) ≤
      η * ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) * stochasticHessianCrossTerm P cfg ω i +
        s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
          (2 * (1 - cfg.beta)) := by
  have hβ0 : 0 ≤ cfg.beta := cfg.beta_mem.1
  have hβ1 : cfg.beta < 1 := cfg.beta_mem.2
  have hden : 0 < 1 - cfg.beta := sub_pos.mpr hβ1
  have hs : 0 ≤ s :=
    le_trans (norm_nonneg _)
      (hthird.bound (stochasticMuonState P cfg ω 0).W)
  induction t with
  | zero =>
      have htail :
          0 ≤ s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
            (2 * (1 - cfg.beta)) := by positivity
      have hnuclear_zero : nuclearNorm (0 : Mat m n) = 0 := by
        unfold nuclearNorm
        simp
      simpa [stochasticMuonState, stochasticMuonBaseState,
        stochasticMuonComparator, hnuclear_zero] using htail
  | succ t ih =>
      have htT : t < T := lt_trans (Nat.lt_succ_self t) (Finset.mem_range.mp ht)
      have htmem : t ∈ Finset.range T := Finset.mem_range.mpr htT
      have hinc := theorem_4_15_gradient_increment_nuclear_bound
        P cfg ω htmem hthird hη hη_nonneg
      have hih := ih htmem
      let Gnext := P.objective.grad (stochasticMuonState P cfg ω (t + 1)).W
      let Gprev := P.objective.grad (stochasticMuonState P cfg ω t).W
      let Cprev := stochasticMuonComparator P cfg ω t
      have hfactor :
          Gnext - stochasticMuonComparator P cfg ω (t + 1) =
            cfg.beta • ((Gnext - Gprev) + (Gprev - Cprev)) := by
        rw [stochasticMuonComparator_succ]
        dsimp [Gnext, Gprev, Cprev]
        module
      have hscale :
          nuclearNorm
              (Gnext - stochasticMuonComparator P cfg ω (t + 1)) ≤
            cfg.beta * nuclearNorm ((Gnext - Gprev) + (Gprev - Cprev)) := by
        rw [hfactor]
        exact nuclearNorm_smul_le_of_nonneg cfg.beta _ hβ0
      have htriangle :
          nuclearNorm ((Gnext - Gprev) + (Gprev - Cprev)) ≤
            nuclearNorm (Gnext - Gprev) + nuclearNorm (Gprev - Cprev) :=
        nuclearNorm_add_le _ _
      have hreverse :
          nuclearNorm (Gnext - Gprev) = nuclearNorm (Gprev - Gnext) := by
        have hneg : Gnext - Gprev = -(Gprev - Gnext) := by module
        rw [hneg, nuclearNorm_neg_eq]
      have hinside :
          nuclearNorm ((Gnext - Gprev) + (Gprev - Cprev)) ≤
            (η * stochasticHessianCrossTerm P cfg ω t +
              s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) +
            (η * ∑ i ∈ Finset.range t,
                cfg.beta ^ (t - i) * stochasticHessianCrossTerm P cfg ω i +
              s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
                (2 * (1 - cfg.beta))) := by
        apply htriangle.trans
        apply add_le_add
        · rw [hreverse]
          simpa [Gprev, Gnext] using hinc
        · simpa [Gprev, Cprev] using hih
      have hscaled := mul_le_mul_of_nonneg_left hinside hβ0
      have hraw := hscale.trans hscaled
      have hsum :
          (∑ i ∈ Finset.range (t + 1),
              cfg.beta ^ (t + 1 - i) * stochasticHessianCrossTerm P cfg ω i) =
            cfg.beta *
                (∑ i ∈ Finset.range t,
                  cfg.beta ^ (t - i) * stochasticHessianCrossTerm P cfg ω i) +
              cfg.beta * stochasticHessianCrossTerm P cfg ω t := by
        rw [Finset.sum_range_succ]
        rw [Finset.mul_sum]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro i hi
          have hit : i < t := Finset.mem_range.mp hi
          have hsub : t + 1 - i = (t - i) + 1 := by omega
          rw [hsub, pow_succ]
          ring
        · simp
      rw [hsum]
      have hne : 1 - cfg.beta ≠ 0 := ne_of_gt hden
      field_simp [hne] at hraw ⊢
      nlinarith

theorem theorem_4_15_comparator_lag_integral_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {s η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hη_nonneg : 0 ≤ η) :
    Integrable (fun ω =>
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            stochasticMuonComparator P cfg ω t))
      (samplePathLaw P cfg.batchSize) ∧
      (∫ ω,
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            stochasticMuonComparator P cfg ω t)
        ∂(samplePathLaw P cfg.batchSize)) ≤
      η * ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) *
            (∫ ω, stochasticHessianCrossTerm P cfg ω i
              ∂(samplePathLaw P cfg.batchSize)) +
        s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
          (2 * (1 - cfg.beta)) := by
  let μ := samplePathLaw P cfg.batchSize
  let lag : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    nuclearNorm
      (P.objective.grad (stochasticMuonState P cfg ω t).W -
        stochasticMuonComparator P cfg ω t)
  let history : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    η * ∑ i ∈ Finset.range t,
      cfg.beta ^ (t - i) * stochasticHessianCrossTerm P cfg ω i
  let tail : ℝ :=
    s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
      (2 * (1 - cfg.beta))
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hDt_meas (i : ℕ) : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonDirection P cfg ω i) :=
    orthogonalizedDirection_measurable.comp (stochasticMuon_M_measurable P cfg i)
  have hDt_bound (i : ℕ) (ω : SamplePath ξ cfg.batchSize) :
      frobeniusNorm (stochasticMuonDirection P cfg ω i) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar
        (stochasticMuonState P cfg ω i).M)
  have hDg_meas (i : ℕ) : Measurable
      (fun ω : SamplePath ξ cfg.batchSize =>
        stochasticGradientDifferenceDirection P cfg ω i) := by
    unfold stochasticGradientDifferenceDirection
    exact orthogonalizedDirection_measurable.comp
      ((hthird.gradient_continuous.measurable.comp
          (stochasticMuon_W_measurable P cfg i)).sub
        (hthird.gradient_continuous.measurable.comp
          (stochasticMuon_W_measurable P cfg (i + 1))))
  have hDg_bound (i : ℕ) (ω : SamplePath ξ cfg.batchSize) :
      frobeniusNorm (stochasticGradientDifferenceDirection P cfg ω i) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    unfold stochasticGradientDifferenceDirection
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar _)
  have hcross_int (i : ℕ) : Integrable
      (fun ω => stochasticHessianCrossTerm P cfg ω i) μ := by
    simpa [μ, stochasticHessianCrossTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg i hthird
        (fun ω => stochasticGradientDifferenceDirection P cfg ω i)
        (fun ω => stochasticMuonDirection P cfg ω i)
        (hDg_meas i) (hDt_meas i) (hDg_bound i) (hDt_bound i)
  have hhistory_int : Integrable history μ := by
    dsimp [history]
    apply Integrable.const_mul
    apply MeasureTheory.integrable_finset_sum (Finset.range t)
    intro i _hi
    exact (hcross_int i).const_mul _
  have hmajorant_int : Integrable (fun ω => history ω + tail) μ :=
    hhistory_int.add (integrable_const tail)
  have hpast_le : stochasticSampleStrictPast cfg.batchSize (t + 1) ≤
      (by infer_instance : MeasurableSpace (SamplePath ξ cfg.batchSize)) := by
    unfold stochasticSampleStrictPast
    refine iSup_le fun q => iSup_le fun _hq => ?_
    have hcoord : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => ω q.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    exact hcoord.comap_le
  have hC_meas : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonComparator P cfg ω t) :=
    (stochasticMuonComparator_strictPast_measurable P cfg t).mono hpast_le le_rfl
  have hlag_meas : Measurable lag := by
    exact nuclearNorm_measurable.comp
      ((hthird.gradient_continuous.measurable.comp
        (stochasticMuon_W_measurable P cfg t)).sub hC_meas)
  have hpoint (ω : SamplePath ξ cfg.batchSize) : lag ω ≤ history ω + tail := by
    simpa [lag, history, tail, μ] using
      theorem_4_15_comparator_lag_bound
        P cfg ht hthird hη hη_nonneg ω
  have hlag_int : Integrable lag μ := by
    refine Integrable.mono' hmajorant_int hlag_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hlag_nonneg : 0 ≤ lag ω := by
        exact nuclearNorm_nonneg_early _
      have hmajorant_nonneg : 0 ≤ history ω + tail := hlag_nonneg.trans (hpoint ω)
      simpa [Real.norm_eq_abs, abs_of_nonneg hlag_nonneg,
        abs_of_nonneg hmajorant_nonneg] using hpoint ω
  have hintegral :
      (∫ ω, lag ω ∂μ) ≤ ∫ ω, history ω + tail ∂μ := by
    exact integral_mono hlag_int hmajorant_int hpoint
  have hhistory_integral :
      (∫ ω, history ω ∂μ) =
        η * ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) *
            (∫ ω, stochasticHessianCrossTerm P cfg ω i ∂μ) := by
    dsimp [history]
    rw [integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    · apply congrArg (fun z : ℝ => η * z)
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]
    · intro i hi
      exact (hcross_int i).const_mul _
  have hmajorant_integral :
      (∫ ω, history ω + tail ∂μ) =
        η * ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) *
            (∫ ω, stochasticHessianCrossTerm P cfg ω i ∂μ) + tail := by
    rw [integral_add hhistory_int (integrable_const tail),
      hhistory_integral]
    simp
  refine ⟨?_, ?_⟩
  · simpa [lag, μ] using hlag_int
  · rw [hmajorant_integral] at hintegral
    simpa [lag, tail, μ] using hintegral

theorem theorem_4_15_combined_tracking_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {s σ η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hη_nonneg : 0 ≤ η) :
    Integrable (fun ω =>
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M))
      (samplePathLaw P cfg.batchSize) ∧
      (∫ ω,
        nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M)
        ∂(samplePathLaw P cfg.batchSize)) ≤
      Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) +
        Real.sqrt (matrixRankBound m n : ℝ) *
          (cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ)) +
        η * ∑ i ∈ Finset.range t,
          cfg.beta ^ (t - i) *
            (∫ ω, stochasticHessianCrossTerm P cfg ω i
              ∂(samplePathLaw P cfg.batchSize)) +
        s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
          (2 * (1 - cfg.beta)) := by
  let μ := samplePathLaw P cfg.batchSize
  let D : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    P.objective.grad (stochasticMuonState P cfg ω t).W -
      stochasticMuonComparator P cfg ω t
  let E : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M
  let Z : SamplePath ξ cfg.batchSize → Mat m n := fun ω =>
    P.objective.grad (stochasticMuonState P cfg ω t).W -
      (stochasticMuonState P cfg ω t).M
  let rroot : ℝ := Real.sqrt (matrixRankBound m n : ℝ)
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hlag := theorem_4_15_comparator_lag_integral_bound
    P cfg ht hthird hη hη_nonneg
  have hDnorm_int : Integrable (fun ω => nuclearNorm (D ω)) μ := by
    simpa [D, μ] using hlag.1
  have hpast_le : stochasticSampleStrictPast cfg.batchSize (t + 1) ≤
      (by infer_instance : MeasurableSpace (SamplePath ξ cfg.batchSize)) := by
    unfold stochasticSampleStrictPast
    refine iSup_le fun q => iSup_le fun _hq => ?_
    have hcoord : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => ω q.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    exact hcoord.comap_le
  have hC_meas : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonComparator P cfg ω t) :=
    (stochasticMuonComparator_strictPast_measurable P cfg t).mono hpast_le le_rfl
  have hE_meas : Measurable E := by
    exact hC_meas.sub (stochasticMuon_M_measurable P cfg t)
  have hEsq :=
    (stochasticMuon_comparatorError_sq_integrable_and_bound
      P cfg t σ hvariance).1
  have hE_int : Integrable E μ := by
    apply integrable_of_integrable_norm_sq hE_meas.aestronglyMeasurable
    simpa [E, μ, frobeniusNorm, norm_matrixToEuclidean] using hEsq
  have herr_int : Integrable (fun ω => frobeniusNorm (E ω)) μ := by
    simpa [frobeniusNorm] using hE_int.norm
  have hZ_meas : Measurable Z := by
    exact (hthird.gradient_continuous.measurable.comp
      (stochasticMuon_W_measurable P cfg t)).sub
        (stochasticMuon_M_measurable P cfg t)
  have hmajorant_int : Integrable
      (fun ω => nuclearNorm (D ω) + rroot * frobeniusNorm (E ω)) μ :=
    hDnorm_int.add (herr_int.const_mul rroot)
  have hpoint (ω : SamplePath ξ cfg.batchSize) :
      nuclearNorm (Z ω) ≤
        nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) := by
    have htri := nuclearNorm_sub_triangle (Z ω) (D ω)
    have hdiff : Z ω - D ω = E ω := by
      dsimp [Z, D, E]
      module
    rw [hdiff] at htri
    exact htri.trans (add_le_add le_rfl (by
      simpa [rroot] using
        nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm (E ω)))
  have hZnorm_int : Integrable (fun ω => nuclearNorm (Z ω)) μ := by
    refine Integrable.mono' hmajorant_int
      (nuclearNorm_measurable.comp hZ_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      have hZ_nonneg : 0 ≤ nuclearNorm (Z ω) := nuclearNorm_nonneg_early _
      have hmajorant_nonneg :
          0 ≤ nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) := by
        exact hZ_nonneg.trans (hpoint ω)
      simpa [Real.norm_eq_abs, abs_of_nonneg hZ_nonneg,
        abs_of_nonneg hmajorant_nonneg] using hpoint ω
  have hintegral :
      (∫ ω, nuclearNorm (Z ω) ∂μ) ≤
        (∫ ω, nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) ∂μ) :=
    integral_mono hZnorm_int hmajorant_int hpoint
  have hadd :
      (∫ ω, nuclearNorm (D ω) + rroot * frobeniusNorm (E ω) ∂μ) =
        (∫ ω, nuclearNorm (D ω) ∂μ) +
          rroot * ∫ ω, frobeniusNorm (E ω) ∂μ := by
    rw [integral_add hDnorm_int (herr_int.const_mul rroot), integral_const_mul]
  rw [hadd] at hintegral
  have hlag_integral :
      (∫ ω, nuclearNorm (D ω) ∂μ) ≤
        η * ∑ i ∈ Finset.range t,
            cfg.beta ^ (t - i) *
              (∫ ω, stochasticHessianCrossTerm P cfg ω i ∂μ) +
          s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
            (2 * (1 - cfg.beta)) := by
    simpa [D, μ] using hlag.2
  have hA4 := stochasticMuonLemmaA4Bound_of_source_assumptions
    P cfg t σ hvariance
  have herr_integral :
      (∫ ω, frobeniusNorm (E ω) ∂μ) ≤
        Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ) +
          cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ) := by
    simpa [stochasticMuonLemmaA4Bound, E, μ] using hA4
  have hrroot : 0 ≤ rroot := Real.sqrt_nonneg _
  have herr_scaled := mul_le_mul_of_nonneg_left herr_integral hrroot
  have hcombined := hintegral.trans
    (add_le_add hlag_integral herr_scaled)
  refine ⟨?_, ?_⟩
  · simpa [Z, μ] using hZnorm_int
  · dsimp [Z, D, E, μ, rroot] at hcombined ⊢
    convert hcombined using 1 <;> ring

theorem third_order_taylor_bound_with_hessian_bilinear
    {m n : ℕ} (P : Objective m n) {s : ℝ}
    (hcont : ContDiff ℝ 3 (vectorizedObjective P))
    (hseries :
      HasFTaylorSeriesUpTo (3 : ℕ∞) (vectorizedObjective P)
        (ftaylorSeries ℝ (vectorizedObjective P)))
    (x d : Mat m n)
    (hfirst_deriv :
      HasFDerivAt (vectorizedObjective P)
        ((continuousMultilinearCurryFin1 ℝ (Mat m n) ℝ)
          ((ftaylorSeries ℝ (vectorizedObjective P) x) 1)) x)
    (hbound :
      ∀ z, ‖iteratedFDeriv ℝ 3 (vectorizedObjective P) z‖ ≤ s) :
    vectorizedObjective P (x + d) - vectorizedObjective P x ≤
      fderiv ℝ (vectorizedObjective P) x d +
        (iteratedFDeriv ℝ 2 (vectorizedObjective P) x)
            (fun _ : Fin 2 => d) / 2 +
        s * ‖d‖ ^ 3 / 6 := by
  let L : ℝ →L[ℝ] Mat m n :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight d
  let q : Mat m n → ℝ := fun z => vectorizedObjective P (x + z)
  let g : ℝ → ℝ := fun u => vectorizedObjective P (x + u • d)
  have hq : ContDiff ℝ 3 q := by
    dsimp [q]
    exact hcont.comp (contDiff_const.add contDiff_id)
  have hg : ContDiff ℝ 3 g := by
    dsimp [g, L, q]
    exact hcont.comp (contDiff_const.add (contDiff_smul_const d))
  have hformal_fderiv :
      fderiv ℝ (vectorizedObjective P) x =
        (continuousMultilinearCurryFin1 ℝ (Mat m n) ℝ)
          ((ftaylorSeries ℝ (vectorizedObjective P) x) 1) :=
    hfirst_deriv.fderiv
  have hseries_one :
      (ftaylorSeries ℝ (vectorizedObjective P) x) 1 =
        iteratedFDeriv ℝ 1 (vectorizedObjective P) x :=
    hseries.eq_iteratedFDeriv (by norm_num) x
  have hformal_eval :
      fderiv ℝ (vectorizedObjective P) x d =
        ((continuousMultilinearCurryFin1 ℝ (Mat m n) ℝ)
          ((ftaylorSeries ℝ (vectorizedObjective P) x) 1)) d :=
    congrArg (fun L => L d) hformal_fderiv
  have hseries_eval :
      ((continuousMultilinearCurryFin1 ℝ (Mat m n) ℝ)
          ((ftaylorSeries ℝ (vectorizedObjective P) x) 1)) d =
        (iteratedFDeriv ℝ 1 (vectorizedObjective P) x)
          (fun _ : Fin 1 => d) := by
    rw [hseries_one]
    simp [continuousMultilinearCurryFin1_apply]
  have hpath_deriv (k : ℕ) (hk : k ≤ 3) (u : ℝ) :
      iteratedDeriv k g u =
        (iteratedFDeriv ℝ k (vectorizedObjective P) (x + u • d))
          (fun _ : Fin k => d) := by
    have hcomp :
        iteratedFDeriv ℝ k (q ∘ L) u =
          (iteratedFDeriv ℝ k q (L u)).compContinuousLinearMap
            (fun _ : Fin k => L) :=
      L.iteratedFDeriv_comp_right hq u (by exact_mod_cast hk)
    rw [iteratedDeriv_eq_iteratedFDeriv]
    change
      iteratedFDeriv ℝ k (q ∘ L) u
          (fun _ : Fin k => (1 : ℝ)) = _
    rw [hcomp]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [iteratedFDeriv_comp_add_left]
    simp [g, q, L]
  obtain ⟨u, hu, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := g) (x := 1) (x₀ := 0) (n := 2) zero_lt_one (hg.contDiffOn)
  have hpoly :
      taylorWithinEval g 2 (Set.Icc (0 : ℝ) 1) 0 1 =
        g 0 + deriv g 0 + iteratedDeriv 2 g 0 / 2 := by
    rw [taylor_within_apply]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_mul, zero_sub, zero_pow, Nat.succ_ne_zero, smul_eq_mul, one_smul,
      Nat.factorial_one, Nat.cast_ofNat, OfNat.ofNat_ne_zero]
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 0) (uniqueDiffOn_Icc zero_lt_one)
      ((hg.of_le (by norm_num)).contDiffAt) (by norm_num)]
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) (uniqueDiffOn_Icc zero_lt_one)
      ((hg.of_le (by norm_num)).contDiffAt) (by norm_num)]
    rw [iteratedDerivWithin_eq_iteratedDeriv (n := 2) (uniqueDiffOn_Icc zero_lt_one)
      ((hg.of_le (by norm_num)).contDiffAt) (by norm_num)]
    simp only [iteratedDeriv_zero, iteratedDeriv_one]
    norm_num
    ring
  rw [hpoly] at hrem
  have h1 : deriv g 0 = fderiv ℝ (vectorizedObjective P) x d := by
    have hh := hpath_deriv 1 (by norm_num) 0
    rw [iteratedDeriv_one] at hh
    calc
      deriv g 0 =
          (iteratedFDeriv ℝ 1 (vectorizedObjective P) x)
            (fun _ : Fin 1 => d) := by
              simpa only [zero_smul, add_zero] using hh
      _ =
          ((continuousMultilinearCurryFin1 ℝ (Mat m n) ℝ)
            ((ftaylorSeries ℝ (vectorizedObjective P) x) 1)) d :=
        hseries_eval.symm
      _ = fderiv ℝ (vectorizedObjective P) x d :=
        hformal_eval.symm
  have h2 :
      iteratedDeriv 2 g 0 =
        (iteratedFDeriv ℝ 2 (vectorizedObjective P) x)
          (fun _ : Fin 2 => d) := by
    simpa [hpath_deriv 2 (by norm_num) 0]
  rw [h1, h2] at hrem
  have hs : 0 ≤ s := le_trans (norm_nonneg _) (hbound x)
  have hthird :
      ‖iteratedDeriv 3 g u‖ ≤ s * ‖d‖ ^ 3 := by
    have hnorm := congrArg norm (hpath_deriv 3 (by norm_num) u)
    calc
      ‖iteratedDeriv 3 g u‖ =
          ‖(iteratedFDeriv ℝ 3 (vectorizedObjective P) (x + u • d))
            (fun _ : Fin 3 => d)‖ := hnorm
      _ ≤ ‖iteratedFDeriv ℝ 3 (vectorizedObjective P) (x + u • d)‖ *
              ∏ _ : Fin 3, ‖d‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ s * ‖d‖ ^ 3 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
        exact hbound _
  have hthird' : iteratedDeriv 3 g u / 6 ≤ s * ‖d‖ ^ 3 / 6 := by
    have habs : iteratedDeriv 3 g u ≤ s * ‖d‖ ^ 3 := by
      exact (le_trans (le_abs_self _) hthird)
    nlinarith [hthird, norm_nonneg (iteratedDeriv 3 g u)]
  norm_num at hrem ⊢
  have hleft : g 1 = vectorizedObjective P (x + d) := by simp [g]
  have hzero : g 0 = vectorizedObjective P x := by simp [g]
  rw [hleft, hzero] at hrem
  norm_num [Nat.factorial] at hrem
  linarith

theorem sqrt_cube_eq_sqrt_pow_three {r : ℝ} (hr : 0 ≤ r) :
    (Real.sqrt r) ^ 3 = Real.sqrt (r ^ 3) := by
  have hs2 : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr
  have hleft : ((Real.sqrt r) ^ 3) ^ 2 = r ^ 3 := by
    rw [show ((Real.sqrt r) ^ 3) ^ 2 = ((Real.sqrt r) ^ 2) ^ 3 by ring, hs2]
  have hright : (Real.sqrt (r ^ 3)) ^ 2 = r ^ 3 :=
    Real.sq_sqrt (by positivity)
  have hsq : ((Real.sqrt r) ^ 3) ^ 2 = (Real.sqrt (r ^ 3)) ^ 2 := by
    rw [hleft, hright]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · exact h
  ·
    have hleft_nonneg : 0 ≤ (Real.sqrt r) ^ 3 := by positivity
    have hright_nonneg : 0 ≤ Real.sqrt (r ^ 3) := Real.sqrt_nonneg _
    have hzleft : (Real.sqrt r) ^ 3 = 0 := by linarith
    have hzright : Real.sqrt (r ^ 3) = 0 := by linarith
    rw [hzleft, hzright]

theorem muon_step_cubic_remainder_bound
    {m n : ℕ} {s η : ℝ} {D : Mat m n}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (hη_abs : |η| = η)
    (hD : frobeniusNorm D ≤ Real.sqrt (matrixRankBound m n : ℝ)) :
    s * ‖(-η) • D‖ ^ 3 / 6 ≤
      s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
  have hr : 0 ≤ (matrixRankBound m n : ℝ) := by positivity
  have hnorm : ‖(-η) • D‖ = η * ‖D‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, hη_abs]
  have hD' : ‖D‖ ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
    simpa [frobeniusNorm] using hD
  have hD3 :
      ‖D‖ ^ 3 ≤ Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
    have hpow : ‖D‖ ^ 3 ≤ (Real.sqrt (matrixRankBound m n : ℝ)) ^ 3 := by
      gcongr
    rw [sqrt_cube_eq_sqrt_pow_three hr] at hpow
    exact hpow
  calc
    s * ‖(-η) • D‖ ^ 3 / 6 =
        s * (η ^ 3 * ‖D‖ ^ 3) / 6 := by rw [hnorm]; ring
    _ ≤ s * (η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) / 6 := by
      have hprod :
          η ^ 3 * ‖D‖ ^ 3 ≤
            η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hD3 (by positivity)
      gcongr
    _ = s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by ring

theorem hessianBilinear_smul_neg_self
    {m n : ℕ} (P : Objective m n) (x d : Mat m n) (η : ℝ) :
    hessianBilinear P x ((-η) • d) ((-η) • d) =
      η ^ 2 * hessianBilinear P x d d := by
  unfold hessianBilinear
  simp [frobeniusInner, map_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem theorem_4_15_one_step_descent_with_tracking
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) {T t : ℕ} {s η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hη_nonneg : 0 ≤ η) :
    P.objective.f (stochasticMuonState P cfg ω t).W -
        P.objective.f (stochasticMuonState P cfg ω (t + 1)).W ≥
      η * nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W) -
        η ^ 2 * stochasticHessianDirectionalTerm P cfg ω t / 2 -
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 -
        2 * η * nuclearNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W -
            (stochasticMuonState P cfg ω t).M) := by
  classical
  let Wt := (stochasticMuonState P cfg ω t).W
  let Wnext := (stochasticMuonState P cfg ω (t + 1)).W
  let M := (stochasticMuonState P cfg ω t).M
  let Dt := stochasticMuonDirection P cfg ω t
  let E := P.objective.grad Wt - M
  let d := Wnext - Wt
  have hupdate : Wnext = Wt - η • Dt := by
    simpa [Wnext, Wt, Dt, stochasticMuonDirection, hη t ht] using
      stochasticMuon_W_succ_eq_source_update P cfg ω t
  have hd : d = (-η) • Dt := by
    change Wnext - Wt = (-η) • Dt
    rw [hupdate]
    ext i j
    simp
  have hcont : ContDiff ℝ 3 (vectorizedObjective P.objective) := hthird.contDiff
  have hseries :
      HasFTaylorSeriesUpTo (3 : ℕ∞) (vectorizedObjective P.objective)
        (ftaylorSeries ℝ (vectorizedObjective P.objective)) :=
    hcont.ftaylorSeries
  have hfirst_deriv :
      HasFDerivAt (vectorizedObjective P.objective)
        ((continuousMultilinearCurryFin1 ℝ (Mat m n) ℝ)
          ((ftaylorSeries ℝ (vectorizedObjective P.objective) Wt) 1)) Wt :=
    hseries.hasFDerivAt (by norm_num) Wt
  have hTaylor0 :=
    third_order_taylor_bound_with_hessian_bilinear
      P.objective hcont hseries Wt d hfirst_deriv hthird.bound
  have hfirstW :
      fderiv ℝ (vectorizedObjective P.objective) Wt d =
        frobeniusInner (P.objective.grad Wt) d :=
    objective_fderiv_apply_eq_frobeniusInner_grad P.objective Wt d
  have hsecondW :
      (iteratedFDeriv ℝ 2 (vectorizedObjective P.objective) Wt)
          (fun _ : Fin 2 => d) =
        hessianBilinear P.objective Wt d d :=
    second_iterated_derivative_eq_hessian_bilinear P.objective hcont Wt d
  rw [hfirstW, hsecondW] at hTaylor0
  have hTaylor :
      P.objective.f Wnext - P.objective.f Wt ≤
        frobeniusInner (P.objective.grad Wt) d +
          η ^ 2 * hessianBilinear P.objective Wt Dt Dt / 2 +
          s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
    have hquad :
        hessianBilinear P.objective Wt d d =
          η ^ 2 * hessianBilinear P.objective Wt Dt Dt := by
      rw [hd]
      exact hessianBilinear_smul_neg_self P.objective Wt Dt η
    have hs : 0 ≤ s :=
      le_trans (norm_nonneg _) (hthird.bound Wt)
    have hDt_norm :
        frobeniusNorm Dt ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
      simpa [Dt, stochasticMuonDirection] using
        frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
          (orthogonalizedDirection_isThinSVDWithPolar M)
    have hη_abs : |η| = η := abs_of_nonneg hη_nonneg
    have hcubic :
        s * ‖d‖ ^ 3 / 6 ≤
          s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
      simpa [hd] using
        muon_step_cubic_remainder_bound hs hη_nonneg hη_abs hDt_norm
    rw [hquad] at hTaylor0
    have hWt_d : Wt + d = Wnext := by
      change Wt + (Wnext - Wt) = Wnext
      abel
    rw [hWt_d] at hTaylor0
    change P.objective.f Wnext - P.objective.f Wt ≤
      frobeniusInner (P.objective.grad Wt) d +
        η ^ 2 * hessianBilinear P.objective Wt Dt Dt / 2 +
        s * ‖d‖ ^ 3 / 6 at hTaylor0
    simpa [vectorizedObjective, Wnext, Wt] using
      (show P.objective.f Wnext - P.objective.f Wt ≤
          frobeniusInner (P.objective.grad Wt) d +
            η ^ 2 * hessianBilinear P.objective Wt Dt Dt / 2 +
            s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 by
        nlinarith [hTaylor0, hcubic])
  have hfirst :
      frobeniusInner (P.objective.grad Wt) d =
        -η * frobeniusInner (P.objective.grad Wt) Dt := by
    rw [hd]
    unfold frobeniusInner
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hpairM : frobeniusInner M Dt = nuclearNorm M := by
    simpa [Dt, stochasticMuonDirection] using
      orthogonalizedDirection_frobeniusInner_eq_nuclearNorm M
  have hsplit :
      frobeniusInner (P.objective.grad Wt) Dt =
        frobeniusInner M Dt + frobeniusInner E Dt := by
    dsimp [E]
    unfold frobeniusInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    simp only [Matrix.sub_apply]
    ring
  have hEpair : -nuclearNorm E ≤ frobeniusInner E Dt := by
    have habs :=
      abs_frobeniusInner_orthogonalizedDirection_le_nuclearNorm E M
    simpa [Dt, stochasticMuonDirection] using
      neg_le_of_abs_le habs
  have hnuctri := nuclearNorm_sub_triangle (P.objective.grad Wt) M
  have hpairG :
      nuclearNorm (P.objective.grad Wt) - 2 * nuclearNorm E ≤
        frobeniusInner (P.objective.grad Wt) Dt := by
    rw [hsplit, hpairM]
    simpa [E] using (show
      nuclearNorm (P.objective.grad Wt) - 2 * nuclearNorm E ≤
        nuclearNorm M + frobeniusInner E Dt by linarith)
  have hpair_scaled := mul_le_mul_of_nonneg_left hpairG hη_nonneg
  rw [hfirst] at hTaylor
  change
    P.objective.f Wt - P.objective.f Wnext ≥
      η * nuclearNorm (P.objective.grad Wt) -
        η ^ 2 * hessianBilinear P.objective Wt Dt Dt / 2 -
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 -
        2 * η * nuclearNorm E
  nlinarith

theorem theorem_4_15_expected_one_step_descent
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T t : ℕ} {s σ η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hη_pos : 0 < η) :
    η * (∫ ω,
        nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W)
      ∂(samplePathLaw P cfg.batchSize)) ≤
      (∫ ω,
        P.objective.f (stochasticMuonState P cfg ω t).W -
          P.objective.f (stochasticMuonState P cfg ω (t + 1)).W
      ∂(samplePathLaw P cfg.batchSize)) +
        η ^ 2 / 2 *
          (∫ ω, stochasticHessianDirectionalTerm P cfg ω t
            ∂(samplePathLaw P cfg.batchSize)) +
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 +
        2 * η *
          (Real.sqrt (matrixRankBound m n : ℝ) *
              (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
                Real.sqrt (cfg.batchSize.val : ℝ)) +
            Real.sqrt (matrixRankBound m n : ℝ) *
              (cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ)) +
            η * ∑ i ∈ Finset.range t,
              cfg.beta ^ (t - i) *
                (∫ ω, stochasticHessianCrossTerm P cfg ω i
                  ∂(samplePathLaw P cfg.batchSize)) +
            s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
              (2 * (1 - cfg.beta))) := by
  let μ := samplePathLaw P cfg.batchSize
  let g : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W)
  let d : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    P.objective.f (stochasticMuonState P cfg ω t).W -
      P.objective.f (stochasticMuonState P cfg ω (t + 1)).W
  let j : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    stochasticHessianDirectionalTerm P cfg ω t
  let e : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    nuclearNorm
      (P.objective.grad (stochasticMuonState P cfg ω t).W -
        (stochasticMuonState P cfg ω t).M)
  let cubic : ℝ :=
    s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6
  let K : ℝ :=
    Real.sqrt (matrixRankBound m n : ℝ) *
        (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
          Real.sqrt (cfg.batchSize.val : ℝ)) +
      Real.sqrt (matrixRankBound m n : ℝ) *
        (cfg.beta ^ t * σ / Real.sqrt (cfg.batchSize.val : ℝ)) +
      η * ∑ i ∈ Finset.range t,
        cfg.beta ^ (t - i) *
          (∫ ω, stochasticHessianCrossTerm P cfg ω i
            ∂(samplePathLaw P cfg.batchSize)) +
      s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * cfg.beta /
        (2 * (1 - cfg.beta))
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  let hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inr ⟨s, hthird⟩)
  have hsumg_int : Integrable
      (fun ω => ∑ k ∈ Finset.range T,
        nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω k).W)) μ := by
    simpa [μ, stochasticAverageNuclearGradientWellDefined,
      SOptLib.expectationWellDefined] using
      (stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
        P cfg T σ hregularity hvariance)
  have hg_meas : Measurable g := by
    exact nuclearNorm_measurable.comp
      (P.objective.grad_measurable.comp (stochasticMuon_W_measurable P cfg t))
  have hg_int : Integrable g μ := by
    apply hsumg_int.mono' hg_meas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg_early _)]
    simpa [g] using Finset.single_le_sum
      (fun k _hk => nuclearNorm_nonneg_early
        (P.objective.grad (stochasticMuonState P cfg ω k).W)) ht
  have hleft := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
    P cfg t σ hregularity hvariance
  have hright := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
    P cfg (t + 1) σ hregularity hvariance
  have hleft' : Integrable
      (fun ω => P.objective.f cfg.W0 -
        P.objective.f (stochasticMuonState P cfg ω t).W) μ := by
    simpa [μ, stochasticExpectedObjectiveDropWellDefined,
      SOptLib.expectationWellDefined] using hleft
  have hright' : Integrable
      (fun ω => P.objective.f cfg.W0 -
        P.objective.f (stochasticMuonState P cfg ω (t + 1)).W) μ := by
    simpa [μ, stochasticExpectedObjectiveDropWellDefined,
      SOptLib.expectationWellDefined] using hright
  have hd_int : Integrable d μ := by
    apply (hright'.sub hleft').congr
    filter_upwards [] with ω
    dsimp [d]
    ring
  have hDt_meas : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonDirection P cfg ω t) :=
    orthogonalizedDirection_measurable.comp (stochasticMuon_M_measurable P cfg t)
  have hDt_bound (ω : SamplePath ξ cfg.batchSize) :
      frobeniusNorm (stochasticMuonDirection P cfg ω t) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar
        (stochasticMuonState P cfg ω t).M)
  have hj_int : Integrable j μ := by
    simpa [j, μ, stochasticHessianDirectionalTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg t hthird
        (fun ω => stochasticMuonDirection P cfg ω t)
        (fun ω => stochasticMuonDirection P cfg ω t)
        hDt_meas hDt_meas hDt_bound hDt_bound
  have htrack := theorem_4_15_combined_tracking_bound
    P cfg ht hthird hvariance hη hη_pos.le
  have he_int : Integrable e μ := by
    simpa [e, μ] using htrack.1
  have he_bound : (∫ ω, e ω ∂μ) ≤ K := by
    simpa [e, K, μ] using htrack.2
  have hpoint (ω : SamplePath ξ cfg.batchSize) :
      η * g ω ≤ d ω + η ^ 2 / 2 * j ω + cubic + 2 * η * e ω := by
    have hstep := theorem_4_15_one_step_descent_with_tracking
      P cfg ω ht hthird hη hη_pos.le
    dsimp [g, d, j, e, cubic]
    linarith
  have hint :
      (∫ ω, η * g ω ∂μ) ≤
        ∫ ω, d ω + η ^ 2 / 2 * j ω + cubic + 2 * η * e ω ∂μ := by
    apply integral_mono (hg_int.const_mul η)
      (((hd_int.add (hj_int.const_mul (η ^ 2 / 2))).add
          (integrable_const cubic)).add (he_int.const_mul (2 * η)))
    exact hpoint
  rw [integral_const_mul] at hint
  have hsplit_outer :
      (∫ ω, d ω + η ^ 2 / 2 * j ω + cubic + 2 * η * e ω ∂μ) =
        (∫ ω, d ω + η ^ 2 / 2 * j ω + cubic ∂μ) +
          ∫ ω, 2 * η * e ω ∂μ := by
    simpa only [Pi.add_apply] using
      integral_add
        ((hd_int.add (hj_int.const_mul (η ^ 2 / 2))).add
          (integrable_const cubic))
        (he_int.const_mul (2 * η))
  have hsplit_cubic :
      (∫ ω, d ω + η ^ 2 / 2 * j ω + cubic ∂μ) =
        (∫ ω, d ω + η ^ 2 / 2 * j ω ∂μ) + ∫ _ω, cubic ∂μ := by
    simpa only [Pi.add_apply] using
      integral_add (hd_int.add (hj_int.const_mul (η ^ 2 / 2)))
        (integrable_const cubic)
  have hsplit_dj :
      (∫ ω, d ω + η ^ 2 / 2 * j ω ∂μ) =
        (∫ ω, d ω ∂μ) + ∫ ω, η ^ 2 / 2 * j ω ∂μ := by
    simpa only [Pi.add_apply] using
      integral_add hd_int (hj_int.const_mul (η ^ 2 / 2))
  have hrhs :
      (∫ ω, d ω + η ^ 2 / 2 * j ω + cubic + 2 * η * e ω ∂μ) =
        (∫ ω, d ω ∂μ) + η ^ 2 / 2 * (∫ ω, j ω ∂μ) + cubic +
          2 * η * (∫ ω, e ω ∂μ) := by
    rw [hsplit_outer, hsplit_cubic, hsplit_dj, integral_const_mul,
      integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul]
  rw [hrhs] at hint
  have he_scaled :
      2 * η * (∫ ω, e ω ∂μ) ≤ 2 * η * K :=
    mul_le_mul_of_nonneg_left he_bound
      (mul_nonneg (by norm_num) hη_pos.le)
  have hfinal :
      η * (∫ ω, g ω ∂μ) ≤
        (∫ ω, d ω ∂μ) + η ^ 2 / 2 * (∫ ω, j ω ∂μ) + cubic +
          2 * η * K := by
    linarith
  simpa [g, d, j, e, cubic, K, μ] using hfinal

/- A signed version of the geometric-history aggregation used in Appendix B.4.
   Shifting by a known lower floor makes the source terms nonnegative; the
   shift cost is retained explicitly for the theorem's big-O remainder. -/
theorem geometric_history_sum_le_of_lower_bound
    (β K : ℝ) (T : ℕ) (a : ℕ → ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hK : 0 ≤ K)
    (ha : ∀ i ∈ Finset.range (T - 1), -K ≤ a i) :
    (∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
        β ^ (t - i) * a i) ≤
      β / (1 - β) * ∑ i ∈ Finset.range (T - 1), a i +
        (T : ℝ) * (β / (1 - β)) * K := by
  let x : ℕ → ℝ := fun i => a i + K
  let H : ℕ → ℝ := fun t =>
    ∑ i ∈ Finset.range t, β ^ (t - i) * x i
  have hx : ∀ i ∈ Finset.range (T - 1), 0 ≤ x i := by
    intro i hi
    dsimp [x]
    linarith [ha i hi]
  have hH_nonneg : ∀ t, t ≤ T - 1 → 0 ≤ H t := by
    intro t ht
    dsimp [H]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg hβ0 _) (hx i (Finset.mem_range.mpr (by
      have hit : i < t := Finset.mem_range.mp hi
      omega)))
  have hrec : ∀ n, 1 ≤ n → n ≤ T - 1 →
      H n = β * (x (n - 1) + H (n - 1)) := by
    intro n hn1 hnT
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [show q + 1 - 1 = q by omega]
    dsimp only [H]
    rw [Finset.sum_range_succ]
    have hprefix :
        (∑ i ∈ Finset.range q, β ^ (q + 1 - i) * x i) =
          β * ∑ i ∈ Finset.range q, β ^ (q - i) * x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hiq : i < q := Finset.mem_range.mp hi
      have hsub : q + 1 - i = (q - i) + 1 := by omega
      rw [hsub, pow_succ]
      ring
    rw [hprefix]
    simp
    ring
  by_cases hT0 : T = 0
  · subst T
    simp
  by_cases hT1 : T = 1
  · subst T
    have hqK : 0 ≤ β / (1 - β) * K :=
      mul_nonneg (div_nonneg hβ0 (sub_nonneg.mpr hβ1.le)) hK
    simpa using hqK
  have hTpos : 0 < T := Nat.pos_of_ne_zero hT0
  have hk : 1 ≤ T - 1 := by omega
  have hsource := sum_le_div_one_sub_of_lagged_aux_recurrence
    (fun n => x (n - 1)) H H (T - 1) β β hk hβ0 hβ1
    (by simpa [H] using hH_nonneg (T - 1) le_rfl)
    (by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnT : n ≤ T - 1 := (Finset.mem_Icc.mp hn).2
      rw [hrec n hn1 hnT])
    (by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnT : n ≤ T - 1 := (Finset.mem_Icc.mp hn).2
      rw [hrec n hn1 hnT])
  have hsource' :
      ∑ t ∈ Finset.range T, H t ≤
        β / (1 - β) * ∑ i ∈ Finset.range (T - 1), x i := by
    rw [show T = (T - 1) + 1 by omega, Finset.sum_range_succ']
    simp only [H, Finset.sum_range_zero, zero_add]
    simpa [sum_Icc_one_eq_sum_range_succ] using hsource
  have hshift :
      (∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
          β ^ (t - i) * a i) ≤ ∑ t ∈ Finset.range T, H t := by
    apply Finset.sum_le_sum
    intro t ht
    dsimp [H]
    apply Finset.sum_le_sum
    intro i hi
    have hit : t < T := Finset.mem_range.mp ht
    have hii : i ∈ Finset.range (T - 1) := Finset.mem_range.mpr (by
      have : i < t := Finset.mem_range.mp hi
      omega)
    have hxi : a i ≤ x i := by dsimp [x]; linarith
    exact mul_le_mul_of_nonneg_left hxi (pow_nonneg hβ0 _)
  have hcard : ((T - 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast Nat.sub_le T 1
  have hq : 0 ≤ β / (1 - β) :=
    div_nonneg hβ0 (sub_nonneg.mpr hβ1.le)
  have htail :
      β / (1 - β) * (((T - 1 : ℕ) : ℝ) * K) ≤
        (T : ℝ) * (β / (1 - β)) * K := by
    calc
      β / (1 - β) * (((T - 1 : ℕ) : ℝ) * K) ≤
          β / (1 - β) * ((T : ℝ) * K) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcard hK) hq
      _ = (T : ℝ) * (β / (1 - β)) * K := by ring
  have hxsum :
      ∑ i ∈ Finset.range (T - 1), x i =
        ∑ i ∈ Finset.range (T - 1), a i + ((T - 1 : ℕ) : ℝ) * K := by
    simp [x, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  rw [hxsum] at hsource'
  exact hshift.trans (hsource'.trans (by nlinarith))

/- T1 also supplies the lower floor needed to aggregate signed `Jhat` terms:
   the nuclear increment is nonnegative, so the Taylor upper bound cannot have
   a right-hand side below zero. -/
theorem theorem_4_15_cross_expectation_lower_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {T i : ℕ} {s η : ℝ}
    (hi : i ∈ Finset.range (T - 1))
    (hthird : ThirdDerivativeBounded P.objective s)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η)
    (hη_pos : 0 < η) :
    -(s * η * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) ≤
      ∫ ω, stochasticHessianCrossTerm P cfg ω i
        ∂(samplePathLaw P cfg.batchSize) := by
  let μ := samplePathLaw P cfg.batchSize
  let j : SamplePath ξ cfg.batchSize → ℝ := fun ω =>
    stochasticHessianCrossTerm P cfg ω i
  let K : ℝ := s * η * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hiT : i ∈ Finset.range T := Finset.mem_range.mpr (by
    have hii : i < T - 1 := Finset.mem_range.mp hi
    omega)
  have hDt_meas : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonDirection P cfg ω i) :=
    orthogonalizedDirection_measurable.comp (stochasticMuon_M_measurable P cfg i)
  have hDg_meas : Measurable
      (fun ω : SamplePath ξ cfg.batchSize =>
        stochasticGradientDifferenceDirection P cfg ω i) := by
    unfold stochasticGradientDifferenceDirection
    exact orthogonalizedDirection_measurable.comp
      ((hthird.gradient_continuous.measurable.comp
          (stochasticMuon_W_measurable P cfg i)).sub
        (hthird.gradient_continuous.measurable.comp
          (stochasticMuon_W_measurable P cfg (i + 1))))
  have hDt_bound (ω : SamplePath ξ cfg.batchSize) :
      frobeniusNorm (stochasticMuonDirection P cfg ω i) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar
        (stochasticMuonState P cfg ω i).M)
  have hDg_bound (ω : SamplePath ξ cfg.batchSize) :
      frobeniusNorm (stochasticGradientDifferenceDirection P cfg ω i) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    unfold stochasticGradientDifferenceDirection
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar _)
  have hj_int : Integrable j μ := by
    simpa [j, μ, stochasticHessianCrossTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg i hthird
        (fun ω => stochasticGradientDifferenceDirection P cfg ω i)
        (fun ω => stochasticMuonDirection P cfg ω i)
        hDg_meas hDt_meas hDg_bound hDt_bound
  have hpoint (ω : SamplePath ξ cfg.batchSize) : -K ≤ j ω := by
    have hinc := theorem_4_15_gradient_increment_nuclear_bound
      P cfg ω hiT hthird hη hη_pos.le
    have hnuc : 0 ≤ nuclearNorm
        (P.objective.grad (stochasticMuonState P cfg ω i).W -
          P.objective.grad (stochasticMuonState P cfg ω (i + 1)).W) :=
      nuclearNorm_nonneg_early _
    dsimp [K, j]
    have hscaled :
        -(s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 2) ≤
          η * stochasticHessianCrossTerm P cfg ω i := by
      linarith
    apply (mul_le_mul_iff_of_pos_left hη_pos).mp
    convert hscaled using 1 <;> ring
  have hint : (∫ _ω, -K ∂μ) ≤ ∫ ω, j ω ∂μ := by
    exact integral_mono (integrable_const (-K)) hj_int hpoint
  simpa [K, j, μ, integral_const, measureReal_univ_eq_one] using hint

/- Appendix B.4 through the finite-horizon telescope, retaining the exact
   geometrically weighted `Jhat` history.  No sign condition on the Hessian
   cross term is used here. -/
theorem theorem_4_15_finite_sum_descent_with_history
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (s σ η : ℝ)
    (hsrc : theorem_4_15_sourceDomain T η)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η) :
    η * ∑ t ∈ Finset.range T,
        (∫ ω,
          nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W)
        ∂(samplePathLaw P cfg.batchSize)) ≤
      stochasticExpectedObjectiveDrop P cfg T +
        η ^ 2 / 2 * ∑ t ∈ Finset.range T,
          (∫ ω, stochasticHessianDirectionalTerm P cfg ω t
            ∂(samplePathLaw P cfg.batchSize)) +
        (T : ℝ) *
          (s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) +
        2 * η *
          ((T : ℝ) * Real.sqrt (matrixRankBound m n : ℝ) *
              (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
                Real.sqrt (cfg.batchSize.val : ℝ)) +
            Real.sqrt (matrixRankBound m n : ℝ) *
              (σ / Real.sqrt (cfg.batchSize.val : ℝ)) / (1 - cfg.beta) +
            η * ∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
              cfg.beta ^ (t - i) *
                (∫ ω, stochasticHessianCrossTerm P cfg ω i
                  ∂(samplePathLaw P cfg.batchSize)) +
            (T : ℝ) *
              (s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
                cfg.beta / (2 * (1 - cfg.beta)))) := by
  let μ := samplePathLaw P cfg.batchSize
  let g : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W)
  let d : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    P.objective.f (stochasticMuonState P cfg ω t).W -
      P.objective.f (stochasticMuonState P cfg ω (t + 1)).W
  let j : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    stochasticHessianDirectionalTerm P cfg ω t
  let h : ℕ → ℝ := fun i =>
    ∫ ω, stochasticHessianCrossTerm P cfg ω i ∂μ
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  let A : ℝ := Real.sqrt r *
    (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ / Real.sqrt B)
  let C : ℝ := Real.sqrt r * (σ / Real.sqrt B)
  let cubic : ℝ := s * η ^ 3 * Real.sqrt (r ^ 3) / 6
  let lag : ℝ := s * η ^ 2 * Real.sqrt (r ^ 3) * cfg.beta /
    (2 * (1 - cfg.beta))
  let history : ℕ → ℝ := fun t =>
    ∑ i ∈ Finset.range t, cfg.beta ^ (t - i) * h i
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  let hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inr ⟨s, hthird⟩)
  have hdrop_int : ∀ t ∈ Finset.range T, Integrable (d t) μ := by
    intro t ht
    have hleft := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg t σ hregularity hvariance
    have hright := stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg (t + 1) σ hregularity hvariance
    have hleft' : Integrable
        (fun ω => P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω t).W) μ := by
      simpa [μ, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using hleft
    have hright' : Integrable
        (fun ω => P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω (t + 1)).W) μ := by
      simpa [μ, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using hright
    apply (hright'.sub hleft').congr
    filter_upwards [] with ω
    dsimp [d]
    ring
  have hpoint : ∀ t ∈ Finset.range T,
      η * (∫ ω, g t ω ∂μ) ≤
        (∫ ω, d t ω ∂μ) + η ^ 2 / 2 * (∫ ω, j t ω ∂μ) +
          cubic + 2 * η * (A + cfg.beta ^ t * C + η * history t + lag) := by
    intro t ht
    have hs := theorem_4_15_expected_one_step_descent
      P cfg ht hthird hvariance hη hsrc.2
    dsimp [g, d, j, h, r, B, A, C, cubic, lag, history, μ]
    convert hs using 1 <;> ring
  have hsum := Finset.sum_le_sum hpoint
  have hsum_d :
      ∑ t ∈ Finset.range T, (∫ ω, d t ω ∂μ) =
        stochasticExpectedObjectiveDrop P cfg T := by
    rw [← integral_finset_sum _ hdrop_int]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [d, stochasticExpectedObjectiveDrop]
    simpa [stochasticMuonState, stochasticMuonBaseState] using
      (Finset.sum_range_sub'
        (fun t => P.objective.f (stochasticMuonState P cfg ω t).W) T)
  have hgeom :
      (∑ t ∈ Finset.range T, cfg.beta ^ t) ≤ 1 / (1 - cfg.beta) := by
    have hmul := geom_sum_mul_neg cfg.beta T
    have hpow : 0 ≤ cfg.beta ^ T := pow_nonneg cfg.beta_mem.1 T
    have hden : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
    apply (le_div_iff₀ hden).2
    rw [hmul]
    linarith
  have hC : 0 ≤ C := by
    dsimp [C, r, B]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (div_nonneg hvariance.nonneg (Real.sqrt_nonneg _))
  have hgeomC :
      (∑ t ∈ Finset.range T, cfg.beta ^ t) * C ≤ C / (1 - cfg.beta) := by
    have := mul_le_mul_of_nonneg_right hgeom hC
    simpa [div_eq_mul_inv, mul_comm] using this
  have hnoise :
      ∑ t ∈ Finset.range T,
          (A + cfg.beta ^ t * C + η * history t + lag) ≤
        (T : ℝ) * A + C / (1 - cfg.beta) +
          η * ∑ t ∈ Finset.range T, history t + (T : ℝ) * lag := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    linarith
  have hscale : 0 ≤ 2 * η := mul_nonneg (by norm_num) hsrc.2.le
  have hnoise_scaled := mul_le_mul_of_nonneg_left hnoise hscale
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, hsum_d, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hfinal :
      η * ∑ t ∈ Finset.range T, ∫ ω, g t ω ∂μ ≤
        stochasticExpectedObjectiveDrop P cfg T +
          η ^ 2 / 2 * ∑ t ∈ Finset.range T, ∫ ω, j t ω ∂μ +
          (T : ℝ) * cubic +
          2 * η * ((T : ℝ) * A + C / (1 - cfg.beta) +
            η * ∑ t ∈ Finset.range T, history t + (T : ℝ) * lag) := by
    exact le_trans hsum (by linarith [hnoise_scaled])
  simpa [g, j, h, r, B, A, C, cubic, lag, history, μ, add_assoc,
    mul_assoc] using hfinal

/- Appendix B.4 after summing, telescoping, and absorbing the signed geometric
   history by its T1 lower floor.  The last two terms are an explicit valid
   representative of the paper's `O(s r^(3/2) η^2 / (1-β))` remainder. -/
theorem theorem_4_15_source_average_bound_at_horizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (s σ η : ℝ)
    (hsrc : theorem_4_15_sourceDomain T η)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η) :
    stochasticAverageNuclearGradient P cfg T ≤
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
        η / 2 * stochasticHessianDirectionalAverage P cfg T +
        2 * Real.sqrt (matrixRankBound m n : ℝ) *
          (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
            Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * Real.sqrt (matrixRankBound m n : ℝ) * σ /
          ((1 - cfg.beta) * (T : ℝ) * Real.sqrt (cfg.batchSize.val : ℝ)) +
        2 * η * cfg.beta / (1 - cfg.beta) *
          stochasticHessianCrossAverage P cfg T +
        s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 +
        2 * s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) *
          cfg.beta / (1 - cfg.beta) := by
  let μ := samplePathLaw P cfg.batchSize
  let g : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W)
  let j : ℕ → SamplePath ξ cfg.batchSize → ℝ := fun t ω =>
    stochasticHessianDirectionalTerm P cfg ω t
  let G : ℕ → ℝ := fun t => ∫ ω, g t ω ∂μ
  let J : ℕ → ℝ := fun t => ∫ ω, j t ω ∂μ
  let H : ℕ → ℝ := fun i =>
    ∫ ω, stochasticHessianCrossTerm P cfg ω i ∂μ
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  let A : ℝ := Real.sqrt r *
    (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ / Real.sqrt B)
  let C : ℝ := Real.sqrt r * (σ / Real.sqrt B)
  let cubic : ℝ := s * η ^ 3 * Real.sqrt (r ^ 3) / 6
  let lag : ℝ := s * η ^ 2 * Real.sqrt (r ^ 3) * cfg.beta /
    (2 * (1 - cfg.beta))
  let K : ℝ := s * η * Real.sqrt (r ^ 3) / 2
  let q : ℝ := cfg.beta / (1 - cfg.beta)
  let SG : ℝ := ∑ t ∈ Finset.range T, G t
  let SJ : ℝ := ∑ t ∈ Finset.range T, J t
  let SH : ℝ := ∑ i ∈ Finset.range (T - 1), H i
  let N : ℝ := stochasticExpectedObjectiveDrop P cfg T + η ^ 2 / 2 * SJ +
    (T : ℝ) * cubic +
    2 * η * ((T : ℝ) * A + C / (1 - cfg.beta) +
      η * (q * SH + (T : ℝ) * q * K) + (T : ℝ) * lag)
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, samplePathLaw]
    infer_instance
  have hs : 0 ≤ s := le_trans (norm_nonneg _)
    (hthird.bound cfg.W0)
  have hK : 0 ≤ K := by
    dsimp [K, r]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hs hsrc.2.le) (Real.sqrt_nonneg _)) (by norm_num)
  have hfloor : ∀ i ∈ Finset.range (T - 1), -K ≤ H i := by
    intro i hi
    simpa [K, H, r, μ] using
      theorem_4_15_cross_expectation_lower_bound
        P cfg hi hthird hη hsrc.2
  have hhistory := geometric_history_sum_le_of_lower_bound
    cfg.beta K T H cfg.beta_mem.1 cfg.beta_mem.2 hK hfloor
  have hfinite := theorem_4_15_finite_sum_descent_with_history
    P cfg T s σ η hsrc hthird hvariance hη
  have hfinite' :
      η * SG ≤ stochasticExpectedObjectiveDrop P cfg T + η ^ 2 / 2 * SJ +
        (T : ℝ) * cubic +
        2 * η * ((T : ℝ) * A + C / (1 - cfg.beta) +
          η * (∑ t ∈ Finset.range T, ∑ i ∈ Finset.range t,
            cfg.beta ^ (t - i) * H i) + (T : ℝ) * lag) := by
    simpa [SG, SJ, G, J, H, r, B, A, C, cubic, lag, μ, add_assoc,
      mul_assoc] using hfinite
  have hscale : 0 ≤ 2 * η ^ 2 := mul_nonneg (by norm_num) (sq_nonneg η)
  have hhistory_scaled := mul_le_mul_of_nonneg_left hhistory hscale
  have hnum : η * SG ≤ N := by
    dsimp [N, q]
    exact hfinite'.trans (by nlinarith)
  let hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inr ⟨s, hthird⟩)
  have hsumg_int : Integrable
      (fun ω => ∑ t ∈ Finset.range T, g t ω) μ := by
    simpa [g, μ, stochasticAverageNuclearGradientWellDefined,
      SOptLib.expectationWellDefined] using
      (stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
        P cfg T σ hregularity hvariance)
  have hg_int : ∀ t ∈ Finset.range T, Integrable (g t) μ := by
    intro t ht
    have hgmeas : Measurable (g t) := by
      exact nuclearNorm_measurable.comp
        (P.objective.grad_measurable.comp (stochasticMuon_W_measurable P cfg t))
    apply hsumg_int.mono' hgmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg_early _)]
    simpa [g] using Finset.single_le_sum
      (fun k _hk => nuclearNorm_nonneg_early
        (P.objective.grad (stochasticMuonState P cfg ω k).W)) ht
  have hj_int : ∀ t ∈ Finset.range T, Integrable (j t) μ := by
    intro t _ht
    have hDt_meas : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonDirection P cfg ω t) :=
      orthogonalizedDirection_measurable.comp (stochasticMuon_M_measurable P cfg t)
    have hDt_bound (ω : SamplePath ξ cfg.batchSize) :
        frobeniusNorm (stochasticMuonDirection P cfg ω t) ≤ Real.sqrt r := by
      exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
        (orthogonalizedDirection_isThinSVDWithPolar
          (stochasticMuonState P cfg ω t).M)
    simpa [j, μ, r, stochasticHessianDirectionalTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg t hthird
        (fun ω => stochasticMuonDirection P cfg ω t)
        (fun ω => stochasticMuonDirection P cfg ω t)
        hDt_meas hDt_meas hDt_bound hDt_bound
  have hh_int : ∀ i ∈ Finset.range (T - 1), Integrable
      (fun ω => stochasticHessianCrossTerm P cfg ω i) μ := by
    intro i _hi
    have hDt_meas : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonDirection P cfg ω i) :=
      orthogonalizedDirection_measurable.comp (stochasticMuon_M_measurable P cfg i)
    have hDg_meas : Measurable
        (fun ω : SamplePath ξ cfg.batchSize =>
          stochasticGradientDifferenceDirection P cfg ω i) := by
      unfold stochasticGradientDifferenceDirection
      exact orthogonalizedDirection_measurable.comp
        ((hthird.gradient_continuous.measurable.comp
            (stochasticMuon_W_measurable P cfg i)).sub
          (hthird.gradient_continuous.measurable.comp
            (stochasticMuon_W_measurable P cfg (i + 1))))
    have hDt_bound (ω : SamplePath ξ cfg.batchSize) :
        frobeniusNorm (stochasticMuonDirection P cfg ω i) ≤ Real.sqrt r := by
      exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
        (orthogonalizedDirection_isThinSVDWithPolar
          (stochasticMuonState P cfg ω i).M)
    have hDg_bound (ω : SamplePath ξ cfg.batchSize) :
        frobeniusNorm (stochasticGradientDifferenceDirection P cfg ω i) ≤
          Real.sqrt r := by
      unfold stochasticGradientDifferenceDirection
      exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
        (orthogonalizedDirection_isThinSVDWithPolar _)
    simpa [μ, r, stochasticHessianCrossTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg i hthird
        (fun ω => stochasticGradientDifferenceDirection P cfg ω i)
        (fun ω => stochasticMuonDirection P cfg ω i)
        hDg_meas hDt_meas hDg_bound hDt_bound
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hsrc.1.1
  have hTηpos : 0 < (T : ℝ) * η := mul_pos hTpos hsrc.2
  have hnormalized : (T : ℝ)⁻¹ * SG ≤ N / ((T : ℝ) * η) := by
    apply (le_div_iff₀ hTηpos).2
    calc
      ((T : ℝ)⁻¹ * SG) * ((T : ℝ) * η) = η * SG := by
        field_simp [ne_of_gt hTpos]
      _ ≤ N := hnum
  have hSG : SG = ∫ ω, ∑ t ∈ Finset.range T, g t ω ∂μ := by
    symm
    simpa [SG, G] using integral_finset_sum (Finset.range T) hg_int
  have hSJ : SJ = ∫ ω, ∑ t ∈ Finset.range T, j t ω ∂μ := by
    symm
    simpa [SJ, J] using integral_finset_sum (Finset.range T) hj_int
  have hSH : SH = ∫ ω, ∑ i ∈ Finset.range (T - 1),
      stochasticHessianCrossTerm P cfg ω i ∂μ := by
    symm
    simpa [SH, H] using integral_finset_sum (Finset.range (T - 1)) hh_int
  have heq : N / ((T : ℝ) * η) =
      stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
        η / 2 * ((T : ℝ)⁻¹ * SJ) + 2 * A +
        2 * C / ((T : ℝ) * (1 - cfg.beta)) +
        2 * η * q * ((T : ℝ)⁻¹ * SH) +
        s * η ^ 2 * Real.sqrt (r ^ 3) / 6 +
        2 * s * η ^ 2 * Real.sqrt (r ^ 3) * cfg.beta /
          (1 - cfg.beta) := by
    have hden : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
    dsimp [N, cubic, lag, K, q]
    field_simp [ne_of_gt hTpos, ne_of_gt hsrc.2, ne_of_gt hden]
    ring
  rw [heq, hSG, hSJ, hSH] at hnormalized
  simpa [stochasticAverageNuclearGradient, stochasticHessianDirectionalAverage,
    stochasticHessianCrossAverage, μ, g, j, SG, SJ, SH, r, B, A, C, q,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnormalized

/- Exact source-RHS form of the fixed-horizon estimate, including a concrete
   representative for the printed big-O term. -/
theorem theorem_4_15_source_formula_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (s σ η : ℝ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hsrc : theorem_4_15_sourceDomain T η)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η) :
    ∃ R : ℝ → ℝ,
      AsymptoticUpperReal (fun _ => True) R
        (fun η' => theorem_4_15_remainderRate m n cfg s η')
        (theoremScope
          "Theorem 4.15 printed O(sr^(3/2)eta^2/(1-beta))" ["eta"]) ∧
      stochasticAverageNuclearGradient P cfg T ≤
        theorem_4_15_sourceBaseRhs cfg T
          (sourceObjectiveInitialGap P.objective cfg.W0 hfinite)
          (stochasticHessianJstar P cfg T) σ η + R η := by
  let μ := samplePathLaw P cfg.batchSize
  let Δ := sourceObjectiveInitialGap P.objective cfg.W0 hfinite
  let Jstar := stochasticHessianJstar P cfg T
  let r : ℝ := matrixRankBound m n
  let R : ℝ → ℝ := fun η' =>
    s * η' ^ 2 * Real.sqrt (r ^ 3) / 6 +
      2 * s * η' ^ 2 * Real.sqrt (r ^ 3) * cfg.beta / (1 - cfg.beta)
  refine ⟨R, ?_, ?_⟩
  · refine ⟨3, 1, by norm_num, by norm_num, ?_, ?_⟩
    · simp [ConstantRespectsScope, theoremScope]
    · intro η' _hdom hη' _hη'one
      have hs : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound cfg.W0)
      have hsqrt : 0 ≤ Real.sqrt (r ^ 3) := Real.sqrt_nonneg _
      have hden : 0 < 1 - cfg.beta := sub_pos.mpr cfg.beta_mem.2
      have hbase : 0 ≤ s * Real.sqrt (r ^ 3) * η' ^ 2 := by positivity
      have hcore : 0 ≤ s * Real.sqrt (r ^ 3) := mul_nonneg hs hsqrt
      have hβcore :
          cfg.beta * (s * Real.sqrt (r ^ 3)) ≤ s * Real.sqrt (r ^ 3) := by
        simpa using mul_le_mul_of_nonneg_right cfg.beta_mem.2.le hcore
      dsimp [R, theorem_4_15_remainderRate, realizedSourceQuot,
        realizedSourceSqrt, sourceQuot, sourceSqrt, r]
      field_simp [ne_of_gt hden]
      ring_nf at hβcore ⊢
      nlinarith
  · letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
    letI : IsProbabilityMeasure μ := by
      dsimp [μ, samplePathLaw]
      infer_instance
    let hregularity : StochasticObjectiveRegularity P.objective :=
      Or.inr (Or.inr ⟨s, hthird⟩)
    have hdrop_int : Integrable
        (fun ω => P.objective.f cfg.W0 -
          P.objective.f (stochasticMuonState P cfg ω T).W) μ := by
      simpa [μ, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using
        (stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
          P cfg T σ hregularity hvariance)
    have hlower (ω : SamplePath ξ cfg.batchSize) :
        P.objective.sourceFStar hfinite ≤
          P.objective.f (stochasticMuonState P cfg ω T).W := by
      simpa [Objective.sourceFStar, Objective.fStar] using
        (csInf_le hfinite (show
          P.objective.f (stochasticMuonState P cfg ω T).W ∈
            Set.range P.objective.f from
          ⟨(stochasticMuonState P cfg ω T).W, rfl⟩))
    have hdrop : stochasticExpectedObjectiveDrop P cfg T ≤ Δ := by
      have hint :
          (∫ ω, P.objective.f cfg.W0 -
              P.objective.f (stochasticMuonState P cfg ω T).W ∂μ) ≤
            ∫ _ω, Δ ∂μ := by
        apply integral_mono hdrop_int (integrable_const Δ)
        intro ω
        dsimp [Δ, sourceObjectiveInitialGap]
        linarith [hlower ω]
      simpa [stochasticExpectedObjectiveDrop, μ, integral_const,
        measureReal_univ_eq_one] using hint
    have havg := theorem_4_15_source_average_bound_at_horizon
      P cfg T s σ η hsrc hthird hvariance hη
    have hTη : 0 < (T : ℝ) * η := by
      exact mul_pos (by exact_mod_cast hsrc.1.1) hsrc.2
    have hdropq :
        stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) ≤
          Δ / ((T : ℝ) * η) :=
      div_le_div_of_nonneg_right hdrop hTη.le
    have hdir : stochasticHessianDirectionalAverage P cfg T ≤ Jstar := by
      dsimp [Jstar]
      rw [stochasticHessianJstar_eq_source_max]
      exact le_max_right _ _
    have hcross : stochasticHessianCrossAverage P cfg T ≤ Jstar := by
      dsimp [Jstar]
      rw [stochasticHessianJstar_eq_source_max]
      exact le_max_left _ _
    have hdir_scaled :
        η / 2 * stochasticHessianDirectionalAverage P cfg T ≤ η / 2 * Jstar :=
      mul_le_mul_of_nonneg_left hdir (div_nonneg hsrc.2.le (by norm_num))
    have hcross_coeff : 0 ≤ 2 * η * cfg.beta / (1 - cfg.beta) := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hsrc.2.le) cfg.beta_mem.1)
        (sub_nonneg.mpr cfg.beta_mem.2.le)
    have hcross_scaled :
        2 * η * cfg.beta / (1 - cfg.beta) *
            stochasticHessianCrossAverage P cfg T ≤
          2 * η * cfg.beta / (1 - cfg.beta) * Jstar :=
      mul_le_mul_of_nonneg_left hcross hcross_coeff
    have hdir_scaled' :
        η / 2 * stochasticHessianDirectionalAverage P cfg T ≤ Jstar * η / 2 := by
      convert hdir_scaled using 1 <;> ring
    have hcross_scaled' :
        2 * η * cfg.beta / (1 - cfg.beta) *
            stochasticHessianCrossAverage P cfg T ≤
          (2 * η * cfg.beta * Jstar) / (1 - cfg.beta) := by
      convert hcross_scaled using 1 <;> ring
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hB : 0 < (cfg.batchSize.val : ℝ) := by
      exact_mod_cast cfg.batchSize.positive
    have hminus : 0 ≤ 1 - cfg.beta := by linarith [cfg.beta_mem.2]
    have hplus : 0 < 1 + cfg.beta := by linarith [cfg.beta_mem.1]
    have hnoise :
        2 * Real.sqrt r *
            (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * σ /
              Real.sqrt (cfg.batchSize.val : ℝ)) =
          (2 * σ * Real.sqrt (r * (1 - cfg.beta))) /
            Real.sqrt ((1 + cfg.beta) * (cfg.batchSize.val : ℝ)) := by
      rw [Real.sqrt_mul hr, Real.sqrt_mul (le_of_lt hplus),
        Real.sqrt_div hminus]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hB),
        ne_of_gt (Real.sqrt_pos.2 hplus)]
    dsimp [theorem_4_15_sourceBaseRhs, Δ, Jstar, R, r] at *
    rw [hnoise] at havg
    ring_nf at havg hdropq hdir_scaled' hcross_scaled' ⊢
    linarith

/- Formula-level consumer for Appendix B.4's corrected otherwise branch.
   Its coefficient contains only the uniform theta constants and fixed problem
   parameters; in particular it is independent of the internal schedule
   accuracy `delta`.  The first conjunct keeps the exact fixed-horizon source
   formula in the proof path, while the second performs the selected-horizon
   substitution using the corrected realized-`Jstar` run contract. -/
set_option maxHeartbeats 800000 in
theorem theorem_4_15_otherwise_source_average_bound_at_schedule_accuracy
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (delta : ℝ) (N : ℕ)
    (hfinite : P.objective.HasFiniteInfimum)
    (hDelta : sourceObjectiveInitialGap P.objective W0 hfinite = Δ)
    (hthird : ThirdDerivativeBounded P.objective s)
    (hvariance : BoundedVariance P σ)
    (hdelta_one : delta ≤ 1)
    (hrun : theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      1 delta N) :
    let r : ℝ := matrixRankBound m n
    let q : ℝ := Real.sqrt (r ^ 3)
    let sr : ℝ := Real.sqrt r
    let K : ℝ :=
      1 / (horizonLower * etaLower * q ^ 2) +
      C * etaUpper * sr * q / (2 * σ ^ 2) +
      2 * Real.sqrt betaUpper +
      2 * r * sr / (betaLower * horizonLower * q) +
      2 * etaUpper * C * q * sr * r / betaLower +
      s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 / (6 * σ ^ 6) +
      2 * s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 * r /
        (betaLower * σ ^ 4)
    (∃ R : ℝ → ℝ,
      AsymptoticUpperReal (fun _ => True) R
        (fun eta => theorem_4_15_remainderRate m n
          (cfgForAccuracyHorizon delta N) s eta)
        (theoremScope
          "Theorem 4.15 printed O(sr^(3/2)eta^2/(1-beta))" ["eta"]) ∧
      stochasticAverageNuclearGradient P (cfgForAccuracyHorizon delta N) N ≤
        theorem_4_15_sourceBaseRhs (cfgForAccuracyHorizon delta N) N
          (sourceObjectiveInitialGap P.objective
            (cfgForAccuracyHorizon delta N).W0 hfinite)
          (stochasticHessianJstar P (cfgForAccuracyHorizon delta N) N) σ
          ((cfgForAccuracyHorizon delta N).eta 0) +
          R ((cfgForAccuracyHorizon delta N).eta 0)) ∧
      stochasticAverageNuclearGradient P
          (cfgForAccuracyHorizon
            (theorem_4_15_otherwiseScheduleAccuracy 1 delta) N) N ≤
        K * delta := by
  dsimp only
  unfold theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon at hrun
  simp [theorem_4_15_otherwiseScheduleAccuracy, sourceQuot] at hrun
  unfold theorem_4_15_otherwiseRunRealizedForAccuracyHorizon at hrun
  dsimp at hrun
  rcases hrun with
    ⟨hN, hwd, hW0, hschedule, hsource, hHorizon, hregDom, hregime⟩
  rcases hschedule with
    ⟨hscheduleDom, hbatch, hbeta, heta, hconstEta⟩
  rcases hscheduleDom with ⟨_hN', hbetaDom, hrankDom, hetaDom⟩
  rcases hbeta with ⟨hbetaLowerPos, _hbetaOrder, hbetaLower, hbetaUpper⟩
  rcases heta with ⟨hetaLowerPos, _hetaOrder, hetaLower, hetaUpper⟩
  rcases hHorizon with
    ⟨hhorizonLowerPos, _hhorizonOrder, hhorizonLower, _hhorizonUpper⟩
  let cfgN := cfgForAccuracyHorizon delta N
  let r : ℝ := matrixRankBound m n
  let q : ℝ := Real.sqrt (r ^ 3)
  let sr : ℝ := Real.sqrt r
  let bscale : ℝ := theorem_4_15_otherwiseOneMinusBetaScale m n σ delta
  let escale : ℝ := theorem_4_15_otherwiseEtaRate m n σ Δ delta N
  let hscale : ℝ := theorem_4_15_otherwiseComplexityRate m n σ delta
  let K : ℝ :=
    1 / (horizonLower * etaLower * q ^ 2) +
    C * etaUpper * sr * q / (2 * σ ^ 2) +
    2 * Real.sqrt betaUpper +
    2 * r * sr / (betaLower * horizonLower * q) +
    2 * etaUpper * C * q * sr * r / betaLower +
    s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 / (6 * σ ^ 6) +
    2 * s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 * r /
      (betaLower * σ ^ 4)
  have hformula := theorem_4_15_source_formula_bound
    P cfgN N s σ (cfgN.eta 0) hfinite hsource hthird hvariance hconstEta
  constructor
  · simpa [cfgN] using hformula
  · have hdelta : 0 < delta := hregime.1
    have hσne : σ ≠ 0 := by
      simpa [sourceQuotDomain] using hetaDom
    have hσpos : 0 < σ := lt_of_le_of_ne hvariance.nonneg (Ne.symm hσne)
    have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
    have hrσ_ne : r * σ ^ 2 ≠ 0 := by
      dsimp [r]
      simpa [sourceQuotDomain] using hbetaDom
    have hr_ne : r ≠ 0 := (mul_ne_zero_iff.mp hrσ_ne).1
    have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
    have hq_pos : 0 < q := by
      dsimp [q]
      exact Real.sqrt_pos.2 (pow_pos hr_pos 3)
    have hsr_pos : 0 < sr := by
      dsimp [sr]
      exact Real.sqrt_pos.2 hr_pos
    have hΔne : Δ ≠ 0 := by
      simpa [theorem_4_15_branchRegimeThresholdDomain, sourceInvDomain] using hregDom
    have hgap_nonneg :
        0 ≤ sourceObjectiveInitialGap P.objective W0 hfinite := by
      unfold sourceObjectiveInitialGap Objective.sourceFStar
      have hlower : P.objective.fStar ≤ P.objective.f W0 := by
        simpa [Objective.fStar] using
          (csInf_le hfinite
            (show P.objective.f W0 ∈ Set.range P.objective.f from ⟨W0, rfl⟩))
      linarith
    have hΔ_nonneg : 0 ≤ Δ := by simpa [hDelta] using hgap_nonneg
    have hΔ_pos : 0 < Δ := lt_of_le_of_ne hΔ_nonneg (Ne.symm hΔne)
    have hb_pos : 0 < 1 - cfgN.beta := sub_pos.mpr cfgN.beta_mem.2
    have hη_pos : 0 < cfgN.eta 0 := hsource.2
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hbscale_pos : 0 < bscale := by
      dsimp [bscale, theorem_4_15_otherwiseOneMinusBetaScale, sourceQuot]
      positivity
    have hescale_pos : 0 < escale := by
      dsimp [escale, theorem_4_15_otherwiseEtaRate, sourceQuot, q]
      positivity
    have hhscale_pos : 0 < hscale := by
      dsimp [hscale, theorem_4_15_otherwiseComplexityRate, q]
      positivity
    have hbetaUpperPos : 0 < betaUpper :=
      lt_of_lt_of_le hbetaLowerPos _hbetaOrder
    have hetaUpperPos : 0 < etaUpper :=
      lt_of_lt_of_le hetaLowerPos _hetaOrder
    have hq_sq : q ^ 2 = r ^ 3 := by
      dsimp [q]
      exact Real.sq_sqrt (pow_nonneg hr_nonneg 3)
    have hsr_sq : sr ^ 2 = r := by
      dsimp [sr]
      exact Real.sq_sqrt hr_nonneg
    have hscale_eta : hscale * escale = q ^ 2 * Δ / delta := by
      dsimp [hscale, escale, theorem_4_15_otherwiseComplexityRate,
        theorem_4_15_otherwiseEtaRate, sourceQuot, q]
      field_simp [hσne, ne_of_gt hdelta]
      ring
    have hbeta_scale :
        bscale = delta ^ 2 / (r * σ ^ 2) := by
      rfl
    have heta_scale :
        escale = q * Δ * delta ^ 2 / σ ^ 3 := by
      rfl
    have hhorizon_scale :
        hscale = σ ^ 3 * q * delta⁻¹ ^ 3 := by
      rfl
    have hJstar : stochasticHessianJstar P cfgN N ≤
        C * (sr * σ / Δ * delta) := by
      have hreal := hregime.2.2
      simpa [cfgN, stochasticHessianJstarRealized,
        stochasticHessianJstar, stochasticHessianDirectionalAverageRealized,
        stochasticHessianDirectionalAverage,
        stochasticHessianCrossAverageRealized,
        stochasticHessianCrossAverage, realizedExpectation,
        theorem_4_15_branchRegimeThreshold, realizedSourceSqrt,
        realizedSourceInv, sourceSqrt, sourceInv, sr] using hreal
    have hC_pos : 0 < C := hregime.2.1
    have hJdir : stochasticHessianDirectionalAverage P cfgN N ≤
        C * (sr * σ / Δ * delta) := by
      exact le_trans (by
        rw [stochasticHessianJstar_eq_source_max]
        exact le_max_right _ _) hJstar
    have hJcross : stochasticHessianCrossAverage P cfgN N ≤
        C * (sr * σ / Δ * delta) := by
      exact le_trans (by
        rw [stochasticHessianJstar_eq_source_max]
        exact le_max_left _ _) hJstar
    have hraw := theorem_4_15_source_average_bound_at_horizon
      P cfgN N s σ (cfgN.eta 0) hsource hthird hvariance hconstEta
    let mu := samplePathLaw P cfgN.batchSize
    letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
    letI : IsProbabilityMeasure mu := by
      dsimp [mu, samplePathLaw]
      infer_instance
    let hregularity : StochasticObjectiveRegularity P.objective :=
      Or.inr (Or.inr ⟨s, hthird⟩)
    have hdrop_int : Integrable
        (fun omega => P.objective.f cfgN.W0 -
          P.objective.f (stochasticMuonState P cfgN omega N).W) mu := by
      simpa [mu, stochasticExpectedObjectiveDropWellDefined,
        SOptLib.expectationWellDefined] using
        (stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
          P cfgN N σ hregularity hvariance)
    have hlower (omega : SamplePath ξ cfgN.batchSize) :
        P.objective.sourceFStar hfinite ≤
          P.objective.f (stochasticMuonState P cfgN omega N).W := by
      simpa [Objective.sourceFStar, Objective.fStar] using
        (csInf_le hfinite (show
          P.objective.f (stochasticMuonState P cfgN omega N).W ∈
            Set.range P.objective.f from
          ⟨(stochasticMuonState P cfgN omega N).W, rfl⟩))
    have hdrop : stochasticExpectedObjectiveDrop P cfgN N ≤ Δ := by
      have hint :
          (∫ omega, P.objective.f cfgN.W0 -
              P.objective.f (stochasticMuonState P cfgN omega N).W ∂mu) ≤
            ∫ _omega, Δ ∂mu := by
        apply integral_mono hdrop_int (integrable_const Δ)
        intro omega
        calc
          P.objective.f cfgN.W0 -
              P.objective.f (stochasticMuonState P cfgN omega N).W ≤
              P.objective.f cfgN.W0 - P.objective.sourceFStar hfinite :=
            sub_le_sub_left (hlower omega) _
          _ = Δ := by
            simpa [cfgN, hW0, sourceObjectiveInitialGap] using hDelta
      simpa [stochasticExpectedObjectiveDrop, mu, integral_const,
        measureReal_univ_eq_one] using hint
    have hfirst :
        sourceObjectiveInitialGap P.objective cfgN.W0 hfinite /
            ((N : ℝ) * cfgN.eta 0) ≤
          (1 / (horizonLower * etaLower * q ^ 2)) * delta := by
      have hdenLower :
          (horizonLower * hscale) * (etaLower * escale) ≤
            (N : ℝ) * cfgN.eta 0 :=
        calc
          (horizonLower * hscale) * (etaLower * escale) ≤
              (N : ℝ) * (etaLower * escale) :=
            mul_le_mul_of_nonneg_right hhorizonLower (by positivity)
          _ ≤ (N : ℝ) * cfgN.eta 0 :=
            mul_le_mul_of_nonneg_left hetaLower hN_pos.le
      have hdenLowerPos :
          0 < (horizonLower * hscale) * (etaLower * escale) := by positivity
      have hgap : sourceObjectiveInitialGap P.objective cfgN.W0 hfinite = Δ := by
        simpa [cfgN, hW0] using hDelta
      rw [hgap]
      calc
        Δ / ((N : ℝ) * cfgN.eta 0) ≤
            Δ / ((horizonLower * hscale) * (etaLower * escale)) :=
          div_le_div_of_nonneg_left hΔ_nonneg hdenLowerPos hdenLower
        _ = (1 / (horizonLower * etaLower * q ^ 2)) * delta := by
          rw [mul_mul_mul_comm, hscale_eta]
          field_simp [ne_of_gt hhorizonLowerPos, ne_of_gt hetaLowerPos,
            ne_of_gt hq_pos, ne_of_gt hΔ_pos, ne_of_gt hdelta]
    have hsecond :
        cfgN.eta 0 / 2 * stochasticHessianDirectionalAverage P cfgN N ≤
          (C * etaUpper * sr * q / (2 * σ ^ 2)) * delta := by
      have hcoeff : 0 ≤ cfgN.eta 0 / 2 := by positivity
      have h1 := mul_le_mul_of_nonneg_left hJdir hcoeff
      have htarget_nonneg : 0 ≤ C * (sr * σ / Δ * delta) := by
        exact mul_nonneg hC_pos.le (mul_nonneg (div_nonneg
          (mul_nonneg hsr_pos.le hσpos.le) hΔ_pos.le) hdelta.le)
      have h2 := mul_le_mul_of_nonneg_right hetaUpper htarget_nonneg
      have hdelta_cube : delta ^ 3 ≤ delta := by
        have hprod : 0 ≤ delta * (1 - delta) * (1 + delta) :=
          mul_nonneg
            (mul_nonneg hdelta.le (sub_nonneg.mpr hdelta_one)) (by linarith)
        nlinarith
      calc
        cfgN.eta 0 / 2 * stochasticHessianDirectionalAverage P cfgN N ≤
            cfgN.eta 0 / 2 * (C * (sr * σ / Δ * delta)) := h1
        _ ≤ (etaUpper * escale) / 2 * (C * (sr * σ / Δ * delta)) := by
          nlinarith
        _ = (C * etaUpper * sr * q / (2 * σ ^ 2)) * delta ^ 3 := by
          rw [heta_scale]
          field_simp [hσne, hΔne]
        _ ≤ (C * etaUpper * sr * q / (2 * σ ^ 2)) * delta := by
          exact mul_le_mul_of_nonneg_left hdelta_cube (by positivity)
    have hdropFirst :
        stochasticExpectedObjectiveDrop P cfgN N /
            ((N : ℝ) * cfgN.eta 0) ≤
          (1 / (horizonLower * etaLower * q ^ 2)) * delta := by
      have hfirst' :
          Δ / ((N : ℝ) * cfgN.eta 0) ≤
            (1 / (horizonLower * etaLower * q ^ 2)) * delta := by
        simpa [cfgN, hW0, hDelta] using hfirst
      exact le_trans
        (div_le_div_of_nonneg_right hdrop
          (mul_pos hN_pos hη_pos).le)
        hfirst'
    have hnoise1 :
        2 * sr *
            (Real.sqrt ((1 - cfgN.beta) / (1 + cfgN.beta)) * σ /
              Real.sqrt (cfgN.batchSize.val : ℝ)) ≤
          (2 * Real.sqrt betaUpper) * delta := by
      have hb_nonneg : 0 ≤ 1 - cfgN.beta := hb_pos.le
      have hplus : 0 < 1 + cfgN.beta := by linarith [cfgN.beta_mem.1]
      have hfrac_nonneg : 0 ≤ (1 - cfgN.beta) / (1 + cfgN.beta) :=
        div_nonneg hb_nonneg hplus.le
      have hfrac_le_b :
          (1 - cfgN.beta) / (1 + cfgN.beta) ≤ 1 - cfgN.beta := by
        apply (div_le_iff₀ hplus).2
        nlinarith [cfgN.beta_mem.1]
      have hfrac :
          (1 - cfgN.beta) / (1 + cfgN.beta) ≤
            betaUpper * delta ^ 2 / (r * σ ^ 2) := by
        calc
          (1 - cfgN.beta) / (1 + cfgN.beta) ≤ 1 - cfgN.beta := hfrac_le_b
          _ ≤ betaUpper * bscale := hbetaUpper
          _ = betaUpper * delta ^ 2 / (r * σ ^ 2) := by
            rw [hbeta_scale]
            ring
      let x := Real.sqrt ((1 - cfgN.beta) / (1 + cfgN.beta))
      let y := Real.sqrt betaUpper * delta
      have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
      have hy_nonneg : 0 ≤ y := mul_nonneg (Real.sqrt_nonneg _) hdelta.le
      have hx_sq : x ^ 2 = (1 - cfgN.beta) / (1 + cfgN.beta) := by
        dsimp [x]
        exact Real.sq_sqrt hfrac_nonneg
      have hy_sq : y ^ 2 = betaUpper * delta ^ 2 := by
        dsimp [y]
        rw [mul_pow, Real.sq_sqrt hbetaUpperPos.le]
      have hscaled_sq : (sr * σ * x) ^ 2 ≤ y ^ 2 := by
        rw [hy_sq, mul_pow, mul_pow, hsr_sq, hx_sq]
        simpa [mul_comm] using
          (le_div_iff₀ (mul_pos hr_pos (sq_pos_of_pos hσpos))).mp hfrac
      have hscaled : sr * σ * x ≤ y :=
        ((sq_le_sq₀ (by positivity : 0 ≤ sr * σ * x) hy_nonneg)).mp hscaled_sq
      rw [hbatch]
      simp only [Nat.cast_one, Real.sqrt_one, div_one]
      dsimp [x, y] at hscaled ⊢
      convert mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 2) using 1 <;>
        ring
    have hbscale_hscale : bscale * hscale = σ * q / (r * delta) := by
      rw [hbeta_scale, hhorizon_scale]
      field_simp [hr_ne, hσne, ne_of_gt hdelta]
    have hnoise2 :
        2 * sr * σ /
            ((1 - cfgN.beta) * (N : ℝ) *
              Real.sqrt (cfgN.batchSize.val : ℝ)) ≤
          (2 * r * sr / (betaLower * horizonLower * q)) * delta := by
      have hdenLower :
          (betaLower * bscale) * (horizonLower * hscale) ≤
            (1 - cfgN.beta) * (N : ℝ) :=
        calc
          (betaLower * bscale) * (horizonLower * hscale) ≤
              (1 - cfgN.beta) * (horizonLower * hscale) :=
            mul_le_mul_of_nonneg_right hbetaLower (by positivity)
          _ ≤ (1 - cfgN.beta) * (N : ℝ) :=
            mul_le_mul_of_nonneg_left hhorizonLower hb_pos.le
      have hdenLowerPos :
          0 < (betaLower * bscale) * (horizonLower * hscale) := by positivity
      rw [hbatch]
      simp only [Nat.cast_one, Real.sqrt_one, mul_one]
      calc
        2 * sr * σ / ((1 - cfgN.beta) * (N : ℝ)) ≤
            2 * sr * σ /
              ((betaLower * bscale) * (horizonLower * hscale)) :=
          div_le_div_of_nonneg_left (by positivity) hdenLowerPos hdenLower
        _ = (2 * r * sr / (betaLower * horizonLower * q)) * delta := by
          rw [mul_mul_mul_comm, hbscale_hscale]
          field_simp [ne_of_gt hbetaLowerPos, ne_of_gt hhorizonLowerPos,
            hr_ne, hσne, ne_of_gt hq_pos, ne_of_gt hdelta]
    have hs_nonneg : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound W0)
    have hrem1 :
        s * (cfgN.eta 0) ^ 2 * q / 6 ≤
          (s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 / (6 * σ ^ 6)) * delta := by
      have heta_sq : (cfgN.eta 0) ^ 2 ≤ (etaUpper * escale) ^ 2 :=
        (sq_le_sq₀ hη_pos.le
          (mul_nonneg hetaUpperPos.le hescale_pos.le)).2 hetaUpper
      have hmul := mul_le_mul_of_nonneg_left heta_sq (mul_nonneg hs_nonneg hq_pos.le)
      have hδsq : delta ^ 2 ≤ delta := by
        have hp : 0 ≤ delta * (1 - delta) :=
          mul_nonneg hdelta.le (sub_nonneg.mpr hdelta_one)
        nlinarith only [hp]
      have hδpow : delta ^ 4 ≤ delta := by
        have hh := (sq_le_sq₀ (sq_nonneg delta) hdelta.le).2 hδsq
        have hh' : delta ^ 4 ≤ delta ^ 2 := by
          convert hh using 1 <;> ring
        exact le_trans hh' hδsq
      calc
        s * (cfgN.eta 0) ^ 2 * q / 6 ≤
            s * (etaUpper * escale) ^ 2 * q / 6 := by
          have hmul' := div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 6)
          convert hmul' using 1 <;> ring
        _ = (s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 / (6 * σ ^ 6)) * delta ^ 4 := by
          rw [heta_scale]
          field_simp [hσne]
        _ ≤ (s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 / (6 * σ ^ 6)) * delta := by
          exact mul_le_mul_of_nonneg_left hδpow (by positivity)
    have hcrossTerm :
        2 * cfgN.eta 0 * cfgN.beta / (1 - cfgN.beta) *
            stochasticHessianCrossAverage P cfgN N ≤
          (2 * etaUpper * C * q * sr * r / betaLower) * delta := by
      let Jbound := C * (sr * σ / Δ * delta)
      have hJbound_nonneg : 0 ≤ Jbound := by
        dsimp [Jbound]
        exact mul_nonneg hC_pos.le (mul_nonneg
          (div_nonneg (mul_nonneg hsr_pos.le hσpos.le) hΔ_pos.le) hdelta.le)
      have hcoeff_nonneg :
          0 ≤ 2 * cfgN.eta 0 * cfgN.beta / (1 - cfgN.beta) := by
        exact div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hη_pos.le) cfgN.beta_mem.1)
          hb_pos.le
      have hreplaceJ := mul_le_mul_of_nonneg_left hJcross hcoeff_nonneg
      have hnum_le :
          2 * cfgN.eta 0 * cfgN.beta * Jbound ≤
            2 * (etaUpper * escale) * Jbound := by
        have hbeta_le : cfgN.beta ≤ 1 := cfgN.beta_mem.2.le
        have heta_beta : cfgN.eta 0 * cfgN.beta ≤ etaUpper * escale := by
          calc
            cfgN.eta 0 * cfgN.beta ≤ cfgN.eta 0 * 1 :=
              mul_le_mul_of_nonneg_left hbeta_le hη_pos.le
            _ ≤ etaUpper * escale := by simpa using hetaUpper
        have htwo :=
          mul_le_mul_of_nonneg_left heta_beta (by norm_num : (0 : ℝ) ≤ 2)
        convert mul_le_mul_of_nonneg_right htwo hJbound_nonneg using 1 <;> ring
      have hlowerb_pos : 0 < betaLower * bscale := by positivity
      calc
        2 * cfgN.eta 0 * cfgN.beta / (1 - cfgN.beta) *
              stochasticHessianCrossAverage P cfgN N ≤
            2 * cfgN.eta 0 * cfgN.beta / (1 - cfgN.beta) * Jbound :=
          hreplaceJ
        _ = (2 * cfgN.eta 0 * cfgN.beta * Jbound) /
              (1 - cfgN.beta) := by ring
        _ ≤ (2 * (etaUpper * escale) * Jbound) /
              (1 - cfgN.beta) :=
          div_le_div_of_nonneg_right hnum_le hb_pos.le
        _ ≤ (2 * (etaUpper * escale) * Jbound) /
              (betaLower * bscale) :=
          div_le_div_of_nonneg_left (by positivity) hlowerb_pos hbetaLower
        _ = (2 * etaUpper * C * q * sr * r / betaLower) * delta := by
          dsimp [Jbound]
          rw [heta_scale, hbeta_scale]
          field_simp [hr_ne, hσne, hΔne, ne_of_gt hdelta,
            ne_of_gt hbetaLowerPos]
    have hrem2 :
        2 * s * (cfgN.eta 0) ^ 2 * q * cfgN.beta /
            (1 - cfgN.beta) ≤
          (2 * s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 * r /
            (betaLower * σ ^ 4)) * delta := by
      have heta_sq : (cfgN.eta 0) ^ 2 ≤ (etaUpper * escale) ^ 2 :=
        (sq_le_sq₀ hη_pos.le
          (mul_nonneg hetaUpperPos.le hescale_pos.le)).2 hetaUpper
      have hδsq' : delta ^ 2 ≤ delta := by
        have hp : 0 ≤ delta * (1 - delta) :=
          mul_nonneg hdelta.le (sub_nonneg.mpr hdelta_one)
        nlinarith only [hp]
      have hnum_le :
          2 * s * (cfgN.eta 0) ^ 2 * q * cfgN.beta ≤
            2 * s * (etaUpper * escale) ^ 2 * q := by
        have hcore_nonneg : 0 ≤ 2 * s * q := by positivity
        have heta_core := mul_le_mul_of_nonneg_left heta_sq hcore_nonneg
        have hleft_nonneg : 0 ≤ 2 * s * (cfgN.eta 0) ^ 2 * q := by positivity
        calc
          2 * s * (cfgN.eta 0) ^ 2 * q * cfgN.beta ≤
              2 * s * (cfgN.eta 0) ^ 2 * q * 1 :=
            mul_le_mul_of_nonneg_left cfgN.beta_mem.2.le hleft_nonneg
          _ ≤ 2 * s * (etaUpper * escale) ^ 2 * q := by
            convert heta_core using 1 <;> ring
      have hlowerb_pos : 0 < betaLower * bscale := by positivity
      calc
        2 * s * (cfgN.eta 0) ^ 2 * q * cfgN.beta /
              (1 - cfgN.beta) ≤
            (2 * s * (etaUpper * escale) ^ 2 * q) /
              (1 - cfgN.beta) :=
          div_le_div_of_nonneg_right hnum_le hb_pos.le
        _ ≤ (2 * s * (etaUpper * escale) ^ 2 * q) /
              (betaLower * bscale) :=
          div_le_div_of_nonneg_left (by positivity) hlowerb_pos hbetaLower
        _ = (2 * s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 * r /
              (betaLower * σ ^ 4)) * delta ^ 2 := by
          rw [heta_scale, hbeta_scale]
          field_simp [hr_ne, hσne, ne_of_gt hdelta,
            ne_of_gt hbetaLowerPos]
        _ ≤ (2 * s * etaUpper ^ 2 * q ^ 3 * Δ ^ 2 * r /
              (betaLower * σ ^ 4)) * delta :=
          mul_le_mul_of_nonneg_left hδsq' (by positivity)
    have hbound : stochasticAverageNuclearGradient P cfgN N ≤ K * delta := by
      have hraw' : stochasticAverageNuclearGradient P cfgN N ≤
          stochasticExpectedObjectiveDrop P cfgN N /
              ((N : ℝ) * cfgN.eta 0) +
            cfgN.eta 0 / 2 * stochasticHessianDirectionalAverage P cfgN N +
            2 * sr *
              (Real.sqrt ((1 - cfgN.beta) / (1 + cfgN.beta)) * σ /
                Real.sqrt (cfgN.batchSize.val : ℝ)) +
            2 * sr * σ /
              ((1 - cfgN.beta) * (N : ℝ) *
                Real.sqrt (cfgN.batchSize.val : ℝ)) +
            2 * cfgN.eta 0 * cfgN.beta / (1 - cfgN.beta) *
              stochasticHessianCrossAverage P cfgN N +
            s * (cfgN.eta 0) ^ 2 * q / 6 +
            2 * s * (cfgN.eta 0) ^ 2 * q * cfgN.beta /
              (1 - cfgN.beta) := by
        simpa [r, sr, q] using hraw
      dsimp [K]
      linarith only [hraw', hdropFirst, hsecond, hnoise1, hnoise2,
        hcrossTerm, hrem1, hrem2]
    have hacc : theorem_4_15_otherwiseScheduleAccuracy 1 delta = delta := by
      simp [theorem_4_15_otherwiseScheduleAccuracy, sourceQuot]
    rw [hacc]
    simpa [cfgN, theorem_4_15_otherwiseScheduleAccuracy, sourceQuot,
      div_one, stochasticAverageNuclearGradient, realizedExpectation,
      K, r, q, sr] using hbound

theorem thirdDerivativeBounded_taylor_step
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    {T t : ℕ} {s η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P s)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    0 ≤ η →
    ‖iteratedFDeriv ℝ 3 (vectorizedObjective P)
        ((deterministicMuonState P cfg t).W)‖ ≤ s →
      P.f ((deterministicMuonState P cfg (t + 1)).W) -
          P.f ((deterministicMuonState P cfg t).W) ≤
        frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
          (((deterministicMuonState P cfg (t + 1)).W) -
            ((deterministicMuonState P cfg t).W)) +
          η ^ 2 *
            hessianBilinear P ((deterministicMuonState P cfg t).W)
              (deterministicMuonDirection P cfg t)
              (deterministicMuonDirection P cfg t) / 2 +
          s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
  classical
  intro hη_nonneg
  intro hthird_at
  let Wt := (deterministicMuonState P cfg t).W
  let Wnext := (deterministicMuonState P cfg (t + 1)).W
  let Gt := (deterministicMuonState P cfg t).G
  let Dt := deterministicMuonDirection P cfg t
  have hcont : ContDiff ℝ 3 (vectorizedObjective P) :=
    ThirdDerivativeBounded.contDiff' hthird
  have hseries :
      HasFTaylorSeriesUpTo (3 : ℕ∞) (vectorizedObjective P)
        (ftaylorSeries ℝ (vectorizedObjective P)) :=
    hcont.ftaylorSeries
  have hfirst_deriv :
      HasFDerivAt (vectorizedObjective P)
        ((continuousMultilinearCurryFin1 ℝ (Mat m n) ℝ)
          ((ftaylorSeries ℝ (vectorizedObjective P) Wt) 1)) Wt :=
    hseries.hasFDerivAt (by norm_num) Wt
  have hbound_at :
      ‖iteratedFDeriv ℝ 3 (vectorizedObjective P) Wt‖ ≤ s :=
    ThirdDerivativeBounded.bound hthird Wt
  have hbound_input :
      ‖iteratedFDeriv ℝ 3 (vectorizedObjective P) Wt‖ ≤ s := by
    simpa [Wt] using hthird_at
  have hG : Gt = P.grad Wt := by
    simpa [Wt, Gt, deterministicGradient] using deterministicMuon_G_eq_gradient P cfg t
  have hD_eq : Dt = orthogonalizedDirection (P.grad Wt) := by
    simpa [Dt, deterministicMuonDirection, Wt, Gt, hG]
  have hdir_norm :
      frobeniusNorm Dt ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
    simpa [Dt] using
      (deterministicMuonDirection_source_contract P cfg t).2.2
  have hupdate :
      Wnext = Wt - η • Dt := by
    simpa [Wnext, Wt, Dt, deterministicMuonDirection, hη t ht] using
      deterministicMuon_W_succ_eq_source_update P cfg t
  have hstep :
      Wnext - Wt = (-η) • Dt := by
    rw [hupdate]
    ext i j
    simp
  have hJ : hessianDirectionalTerm P cfg t =
      hessianBilinear P Wt Dt Dt := by
    simp [hessianDirectionalTerm, Wt, Dt]
  have hη_abs : |η| = η := abs_of_nonneg hη_nonneg
  have hTaylor0 :=
    third_order_taylor_bound_with_hessian_bilinear P hcont hseries
      Wt (Wnext - Wt) hfirst_deriv (ThirdDerivativeBounded.bound hthird)
  have hfirstW :
      fderiv ℝ (vectorizedObjective P) Wt (Wnext - Wt) =
        frobeniusInner (P.grad Wt) (Wnext - Wt) :=
    objective_fderiv_apply_eq_frobeniusInner_grad P Wt (Wnext - Wt)
  have hsecondW :
      (iteratedFDeriv ℝ 2 (vectorizedObjective P) Wt)
          (fun _ : Fin 2 => Wnext - Wt) =
        hessianBilinear P Wt (Wnext - Wt) (Wnext - Wt) :=
    second_iterated_derivative_eq_hessian_bilinear P hcont Wt (Wnext - Wt)
  rw [hfirstW, hsecondW] at hTaylor0
  have hTaylor :
      P.f Wnext - P.f Wt ≤
        frobeniusInner (P.grad Wt) (Wnext - Wt) +
          hessianBilinear P Wt (Wnext - Wt) (Wnext - Wt) / 2 +
          s * ‖Wnext - Wt‖ ^ 3 / 6 := by
    simpa [vectorizedObjective] using hTaylor0
  have hquad :
      hessianBilinear P Wt (Wnext - Wt) (Wnext - Wt) =
        η ^ 2 * hessianBilinear P Wt Dt Dt := by
    rw [hstep]
    exact hessianBilinear_smul_neg_self P Wt Dt η
  rw [hquad] at hTaylor
  have hs : 0 ≤ s := le_trans (norm_nonneg _) hbound_at
  have hcubic :
      s * ‖Wnext - Wt‖ ^ 3 / 6 ≤
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
    simpa [hstep] using
      (muon_step_cubic_remainder_bound hs hη_nonneg hη_abs hdir_norm)
  nlinarith [hTaylor, hcubic]

theorem equation_15_third_order_descent_from_assumption
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    {T t : ℕ} {s η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P s)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (hη_pos : 0 < η) :
    P.f ((deterministicMuonState P cfg (t + 1)).W) -
        P.f ((deterministicMuonState P cfg t).W) ≤
      -η * nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) +
        η ^ 2 * hessianDirectionalTerm P cfg t / 2 +
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
  exact equation_15_third_order_descent P cfg ht hthird hη (le_of_lt hη_pos)
    (thirdDerivativeBounded_taylor_step P cfg ht hthird hη (le_of_lt hη_pos))

theorem affine_recurrence_unroll
    (q : ℝ) (x a : ℕ → ℝ) (T : ℕ)
    (hq : 0 ≤ q)
    (hrec : ∀ t ∈ Finset.range T, x (t + 1) ≤ q * x t + a t) :
    x T ≤ q ^ T * x 0 +
      ∑ t ∈ Finset.range T, q ^ (T - 1 - t) * a t := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hrecT : x (T + 1) ≤ q * x T + a T :=
        hrec T (Finset.mem_range.mpr (by omega))
      have hrecPrefix :
          ∀ t ∈ Finset.range T, x (t + 1) ≤ q * x t + a t := by
        intro t ht
        exact hrec t (Finset.mem_range.mpr
          (lt_trans (Finset.mem_range.mp ht) (by omega)))
      have hih := ih hrecPrefix
      have hscaled : q * x T ≤
          q * (q ^ T * x 0 +
            ∑ t ∈ Finset.range T, q ^ (T - 1 - t) * a t) :=
        mul_le_mul_of_nonneg_left hih hq
      have hprefix :
          q * (∑ t ∈ Finset.range T, q ^ (T - 1 - t) * a t) =
            ∑ t ∈ Finset.range T, q ^ (T - t) * a t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hsub : T - t = (T - 1 - t) + 1 := by
          have htt : t < T := Finset.mem_range.mp ht
          omega
        rw [hsub, pow_succ]
        ring
      calc
        x (T + 1) ≤ q * x T + a T := hrecT
        _ ≤ q * (q ^ T * x 0 +
              ∑ t ∈ Finset.range T, q ^ (T - 1 - t) * a t) + a T :=
          add_le_add hscaled le_rfl
        _ = q ^ (T + 1) * x 0 +
              ∑ t ∈ Finset.range (T + 1),
                q ^ (T + 1 - 1 - t) * a t := by
          rw [Finset.sum_range_succ, mul_add, hprefix, pow_succ]
          simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
          ring

/- Scalar Appendix C.2/C.4 reciprocal argument.  It is deliberately stated
   only for the finite prefix consumed by a fixed-horizon source theorem. -/
theorem quadratic_descent_recurrence_rational_bound
    (x : ℕ → ℝ) (T : ℕ) (K : ℝ)
    (hK : 0 < K)
    (hx : ∀ t ∈ Finset.range (T + 1), 0 ≤ x t)
    (hrec : ∀ t ∈ Finset.range T,
      x (t + 1) ≤ x t - x t ^ 2 / (2 * K)) :
    x T ≤ (2 * K * x 0) / (2 * K + (T : ℝ) * x 0) := by
  have hstep_mono : ∀ t ∈ Finset.range T, x (t + 1) ≤ x t := by
    intro t ht
    have hquad : 0 ≤ x t ^ 2 / (2 * K) := by positivity
    linarith [hrec t ht]
  have hprefix : ∀ n : ℕ, n ≤ T → x n ≤ x 0 := by
    intro n hn
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      exact le_trans
        (hstep_mono n (Finset.mem_range.mpr (by omega)))
        (ih (by omega))
  have hinv : ∀ n : ℕ, n ≤ T → 0 < x n →
      1 / x 0 + (n : ℝ) / (2 * K) ≤ 1 / x n := by
    intro n hn hxn
    induction n with
    | zero => simp
    | succ n ih =>
      have hnT : n < T := by omega
      have hnmem : n ∈ Finset.range T := Finset.mem_range.mpr hnT
      have hmono := hstep_mono n hnmem
      have hxnprev : 0 < x n := lt_of_lt_of_le hxn hmono
      have hih := ih (by omega) hxnprev
      have hfirst : x (n + 1) / x n ≤ 1 - x n / (2 * K) := by
        apply (div_le_iff₀ hxnprev).2
        have hs := hrec n hnmem
        field_simp [ne_of_gt hK, ne_of_gt hxnprev]
        field_simp [ne_of_gt hK] at hs
        nlinarith
      have hsecond : x (n + 1) / (2 * K) ≤ x n / (2 * K) := by
        exact div_le_div_of_nonneg_right hmono (by positivity)
      have hinc : 1 / x n + 1 / (2 * K) ≤ 1 / x (n + 1) := by
        apply (le_div_iff₀ hxn).2
        calc
          (1 / x n + 1 / (2 * K)) * x (n + 1) =
              x (n + 1) / x n + x (n + 1) / (2 * K) := by ring
          _ ≤ (1 - x n / (2 * K)) + x n / (2 * K) :=
            add_le_add hfirst hsecond
          _ = 1 := by ring
      have hcast : ((n + 1 : ℕ) : ℝ) / (2 * K) =
          (n : ℝ) / (2 * K) + 1 / (2 * K) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
      rw [hcast]
      linarith
  have hx0 : 0 ≤ x 0 := hx 0 (by simp)
  have hden : 0 < 2 * K + (T : ℝ) * x 0 := by positivity
  by_cases hxTzero : x T = 0
  · rw [hxTzero]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK.le) hx0) hden.le
  · have hxTpos : 0 < x T :=
      lt_of_le_of_ne (hx T (by simp)) (Ne.symm hxTzero)
    have hx0pos : 0 < x 0 := lt_of_lt_of_le hxTpos (hprefix T le_rfl)
    have hfrac :
        (2 * K + (T : ℝ) * x 0) / (2 * K * x 0) ≤ 1 / x T := by
      calc
        (2 * K + (T : ℝ) * x 0) / (2 * K * x 0) =
            1 / x 0 + (T : ℝ) / (2 * K) := by
              field_simp [ne_of_gt hK, ne_of_gt hx0pos]
        _ ≤ 1 / x T := hinv T le_rfl hxTpos
    have hcross := (div_le_div_iff₀
      (mul_pos (mul_pos (by norm_num) hK) hx0pos) hxTpos).mp hfrac
    apply (le_div_iff₀ hden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

theorem theorem_4_16_star_gradient_lower_bound_at
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T t : ℕ) (Wstar : Mat m n) (Dop : ℝ)
    (hstar : StarConvex P Wstar)
    (hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (ht : t ∈ Finset.range (T + 1)) :
    P.f ((deterministicMuonState P cfg t).W) - P.fStar ≤
      Dop * nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) := by
  let Wt := (deterministicMuonState P cfg t).W
  have hsource := hstar.gradient_lower_bound Wt
  have hdual : frobeniusInner (P.grad Wt) (Wt - Wstar) ≤
      nuclearNorm (P.grad Wt) * spectralNorm (Wt - Wstar) :=
    le_trans (le_abs_self _)
      (abs_frobeniusInner_le_nuclearNorm_mul_spectralNorm
        (P.grad Wt) (Wt - Wstar))
  have hdist : spectralNorm (Wt - Wstar) ≤ Dop := hbounded t ht
  have hscaled := mul_le_mul_of_nonneg_left hdist
    (nuclearNorm_nonneg_early (P.grad Wt))
  dsimp [Wt] at hsource hdual hscaled ⊢
  linarith

/- Appendix C.1, Eq. (16) followed by the already proved Eq. (20).  This is
   the formula-level fixed-horizon supplier used both by the registered run
   and by the precision run selected below. -/
theorem theorem_4_5_source_formula_bound_at_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (L Dop η : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hsmooth : FrobeniusSmooth P L)
    (hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (hdom : theorem_4_5_rhsDomain P cfg T L Dop η)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    sourceObjectiveGapAt P cfg T hfinite ≤
      theorem_4_5_sourceRhs P cfg T L Dop η := by
  have hDop : 0 < Dop := by
    rcases hdom with ⟨hDopNe, hηnonneg, hηDop⟩
    exact lt_of_le_of_ne (le_trans hηnonneg hηDop) (Ne.symm hDopNe)
  by_cases hηzero : η = 0
  · have hW : (deterministicMuonState P cfg T).W = cfg.W0 := by
      have hWprefix : ∀ k : ℕ, k ≤ T →
          (deterministicMuonState P cfg k).W = cfg.W0 := by
        intro k hk
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [deterministicMuon_W_succ_eq_source_update]
          have hstep : cfg.eta k = 0 := by
            rw [hη k (Finset.mem_range.mpr (by omega)), hηzero]
          rw [hstep, zero_smul, sub_zero]
          exact ih (by omega)
      exact hWprefix T le_rfl
    rw [hηzero]
    simp [sourceObjectiveGapAt, theorem_4_5_sourceRhs, hW,
      Objective.sourceFStar, hDop.ne']
  · have hηpos : 0 < η := lt_of_le_of_ne hdom.2.1 (Ne.symm hηzero)
    let q : ℝ := 1 - η / Dop
    let x : ℕ → ℝ := fun t =>
      P.f ((deterministicMuonState P cfg t).W) - P.fStar
    let a : ℝ := (matrixRankBound m n : ℝ) * L * η ^ 2 / 2
    have hq : 0 ≤ q := by
      dsimp [q]
      exact sub_nonneg.mpr ((div_le_one hDop).2 hdom.2.2)
    have ha : 0 ≤ a := by
      by_cases hr : matrixRankBound m n = 0
      · simp [a, hr]
      · have hrpos : 0 < Real.sqrt (matrixRankBound m n : ℝ) :=
          Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hr)
        have hL : 0 ≤ L := nonneg_of_mul_nonneg_left
          (frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth) hrpos
        dsimp [a]
        positivity
    have hrec : ∀ t ∈ Finset.range T, x (t + 1) ≤ q * x t + a := by
      intro t ht
      let Wt := (deterministicMuonState P cfg t).W
      let Wnext := (deterministicMuonState P cfg (t + 1)).W
      let Gt := P.grad Wt
      let Dt := orthogonalizedDirection Gt
      have hG : (deterministicMuonState P cfg t).G = Gt := by
        simpa [Gt, Wt, deterministicGradient] using
          deterministicMuon_G_eq_gradient P cfg t
      have hupdate : Wnext = Wt - η • Dt := by
        simpa [Wnext, Wt, Dt, hG, hη t ht] using
          deterministicMuon_W_succ_eq_source_update P cfg t
      have hsmoothStep := frobeniusSmooth_quadratic_upper_bound P hsmooth Wt Wnext
      have hdiff : Wnext - Wt = (-η) • Dt := by
        rw [hupdate]
        ext i j
        simp
      rw [hdiff] at hsmoothStep
      have hpair : frobeniusInner Gt ((-η) • Dt) =
          -η * nuclearNorm Gt := by
        rw [show frobeniusInner Gt ((-η) • Dt) =
            -η * frobeniusInner Gt Dt by
          unfold frobeniusInner
          simp only [Matrix.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring]
        rw [orthogonalizedDirection_frobeniusInner_eq_nuclearNorm]
      have hnorm : frobeniusNorm ((-η) • Dt) ^ 2 =
          η ^ 2 * (Gt.rank : ℝ) := by
        rw [frobeniusNorm, norm_smul, Real.norm_eq_abs, abs_neg,
          mul_pow, sq_abs]
        congr 1
        simpa [frobeniusNorm] using
          (orthogonalizedDirection_frobeniusNorm_sq Gt)
      rw [hpair, hnorm] at hsmoothStep
      have hrank : (Gt.rank : ℝ) ≤ matrixRankBound m n := by
        exact_mod_cast le_min (Matrix.rank_le_height Gt) (Matrix.rank_le_width Gt)
      have hquad : (L / 2) * (η ^ 2 * (Gt.rank : ℝ)) ≤ a := by
        by_cases hr : matrixRankBound m n = 0
        · have hGrank : Gt.rank = 0 := by
            have hrankNat : Gt.rank ≤ matrixRankBound m n :=
              le_min (Matrix.rank_le_height Gt) (Matrix.rank_le_width Gt)
            rw [hr] at hrankNat
            omega
          simp [a, hr, hGrank]
        · have hrpos : 0 < Real.sqrt (matrixRankBound m n : ℝ) :=
            Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hr)
          have hL : 0 ≤ L := nonneg_of_mul_nonneg_left
            (frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth) hrpos
          dsimp [a]
          have hcoef : 0 ≤ (L / 2) * η ^ 2 :=
            mul_nonneg (div_nonneg hL (by norm_num)) (sq_nonneg η)
          have hscale := mul_le_mul_of_nonneg_left hrank hcoef
          nlinarith
      have ht' : t ∈ Finset.range (T + 1) :=
        Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp ht) (by omega))
      have hgap := theorem_4_16_star_gradient_lower_bound_at
        P cfg T t Wstar Dop hstar hbounded ht'
      have hgapDiv : x t / Dop ≤ nuclearNorm Gt := by
        apply (div_le_iff₀ hDop).2
        simpa [x, Gt, Wt, mul_comm] using hgap
      have hscaled := mul_le_mul_of_nonneg_left hgapDiv hηpos.le
      have hscaled' : η / Dop * x t ≤ η * nuclearNorm Gt := by
        convert hscaled using 1 <;> ring
      dsimp [x, q, a, Wnext, Wt, Gt] at hsmoothStep hquad hscaled' ⊢
      linarith
    have hunroll := affine_recurrence_unroll q x (fun _ => a) T hq hrec
    let S : ℝ := ∑ t ∈ Finset.range T, q ^ (T - 1 - t)
    have hsum : (∑ t ∈ Finset.range T, q ^ (T - 1 - t) * a) = a * S := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    have hSreflect : S = ∑ t ∈ Finset.range T, q ^ t := by
      dsimp [S]
      exact Finset.sum_range_reflect (fun t => q ^ t) T
    have hq_lt : q < 1 := by
      dsimp [q]
      exact sub_lt_self _ (div_pos hηpos hDop)
    have hone_sub_q : 0 < 1 - q := sub_pos.mpr hq_lt
    have hgeom : (∑ t ∈ Finset.range T, q ^ t) * (1 - q) = 1 - q ^ T :=
      geom_sum_mul_neg q T
    have hS_le_inv : S ≤ 1 / (1 - q) := by
      rw [hSreflect]
      apply (le_div_iff₀ hone_sub_q).2
      rw [hgeom]
      nlinarith [pow_nonneg hq T]
    have hSinv : 1 / (1 - q) = Dop / η := by
      dsimp [q]
      field_simp [hDop.ne', hηzero]
      ring
    have hS_le : S ≤ Dop / η := by simpa [hSinv] using hS_le_inv
    have haS : a * S ≤ (matrixRankBound m n : ℝ) * L * Dop * η / 2 := by
      have hscaled := mul_le_mul_of_nonneg_left hS_le ha
      dsimp [a] at hscaled ⊢
      field_simp [hηzero] at hscaled ⊢
      nlinarith
    rw [hsum] at hunroll
    have hxzero : x 0 = P.f cfg.W0 - P.fStar := by
      simp [x, deterministicMuonState, deterministicMuonBaseState]
    rw [hxzero] at hunroll
    dsimp [sourceObjectiveGapAt, Objective.sourceFStar,
      theorem_4_5_sourceRhs, q, x]
    dsimp [x, q] at hunroll
    exact le_trans hunroll (by linarith [haS])

theorem matrix_eq_zero_of_spectralNorm_eq_zero
    {m n : ℕ} {A : Mat m n} (hA : spectralNorm A = 0) : A = 0 := by
  have hop :
      (Matrix.toEuclideanLin (𝕜 := ℝ) A).toContinuousLinearMap = 0 := by
    apply norm_eq_zero.mp
    simpa [spectralNorm] using hA
  have hlin : Matrix.toEuclideanLin (𝕜 := ℝ) A = 0 := by
    apply LinearMap.ext
    intro v
    exact DFunLike.congr_fun hop v
  exact Matrix.toEuclideanLin.injective (by simpa using hlin)

theorem objective_value_ge_fStar_early
    {m n : ℕ} (P : Objective m n) (hfinite : P.HasFiniteInfimum)
    (W : Mat m n) : P.fStar ≤ P.f W := by
  simpa [Objective.fStar] using
    (csInf_le hfinite (show P.f W ∈ Set.range P.f from ⟨W, rfl⟩))

theorem objective_grad_eq_zero_at_starMinimizer
    {m n : ℕ} (P : Objective m n) (Wstar : Mat m n)
    (hfinite : P.HasFiniteInfimum) (hstar : StarConvex P Wstar) :
    P.grad Wstar = 0 := by
  have hglobal : ∀ W : Mat m n, P.f Wstar ≤ P.f W := by
    intro W
    rw [hstar.1]
    exact objective_value_ge_fStar_early P hfinite W
  have hlocal : IsLocalMin P.f Wstar := Filter.Eventually.of_forall hglobal
  have hfd : fderiv ℝ P.f Wstar = 0 := hlocal.fderiv_eq_zero
  ext i j
  rw [Objective.grad_eq_coordinate_fderiv]
  change fderiv ℝ P.f Wstar (coordinateMatrix i j) = 0
  rw [hfd]
  rfl

theorem objective_gap_eq_zero_of_frobeniusSmooth_zero
    {m n : ℕ} (P : Objective m n) (Wstar W : Mat m n)
    (hfinite : P.HasFiniteInfimum) (hstar : StarConvex P Wstar)
    (hsmooth : FrobeniusSmooth P 0) :
    P.f W - P.fStar = 0 := by
  have hupper := frobeniusSmooth_quadratic_upper_bound P hsmooth Wstar W
  have hgrad := objective_grad_eq_zero_at_starMinimizer P Wstar hfinite hstar
  rw [hgrad] at hupper
  simp only [frobeniusInner, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_div, zero_mul] at hupper
  have hlower := objective_value_ge_fStar_early P hfinite W
  rw [hstar.1] at hupper
  linarith

theorem state_eq_star_of_bounded_zero
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T t : ℕ) (Wstar : Mat m n)
    (hbounded : BoundedOperatorDistance P cfg T Wstar 0)
    (ht : t ∈ Finset.range (T + 1)) :
    (deterministicMuonState P cfg t).W = Wstar := by
  have hdist := hbounded t ht
  have hzero :
      spectralNorm ((deterministicMuonState P cfg t).W - Wstar) = 0 :=
    le_antisymm hdist (by unfold spectralNorm; exact norm_nonneg _)
  have hmat := matrix_eq_zero_of_spectralNorm_eq_zero hzero
  exact sub_eq_zero.mp hmat

/- Appendix C.2, Eq. (17) plus Eq. (18), packaged at the source's actual
   fixed-horizon granularity.  This is the current formula supplier; in
   particular it has no all-horizon run-family premise.  The zero-gap and
   zero-scale cases stay inside this theorem because the printed quotient is
   not required to carry a fabricated nonzero-denominator witness.  The C.2
   prose/OCR says “spectral smoothness”, but Eq. (17), Theorem 4.6's “same
   assumptions as Theorem 4.5”, and its rank-weighted `r * L` formula are the
   Frobenius-smooth route; this declaration preserves that theorem-level
   source contract rather than introducing a new spectral assumption. -/
theorem theorem_4_6_source_formula_bound_at_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (t : ℕ) (Wstar : Mat m n) (L Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hsmooth : FrobeniusSmooth P L)
    (hbounded : BoundedOperatorDistance P cfg t Wstar Dop)
    (hη : theorem_4_6_adaptiveSchedule P cfg t L) :
    sourceObjectiveGapAt P cfg t hfinite ≤
      theorem_4_6_sourceRhs P cfg t L Dop := by
  let r : ℝ := matrixRankBound m n
  let K : ℝ := r * L * Dop ^ 2
  let x : ℕ → ℝ := fun k =>
    P.f ((deterministicMuonState P cfg k).W) - P.fStar
  have hx : ∀ k ∈ Finset.range (t + 1), 0 ≤ x k := by
    intro k _hk
    dsimp [x]
    linarith [objective_value_ge_fStar_early P hfinite
      (deterministicMuonState P cfg k).W]
  have hr : 0 ≤ r := by positivity
  have hK : 0 ≤ K := by
    by_cases hrzero : matrixRankBound m n = 0
    · simp [K, r, hrzero]
    · have hrpos : 0 < Real.sqrt (matrixRankBound m n : ℝ) :=
        Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hrzero)
      have hL : 0 ≤ L := nonneg_of_mul_nonneg_left
        (frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth) hrpos
      dsimp [K, r]
      positivity
  by_cases hKzero : K = 0
  · have hgapzero : x t = 0 := by
      have hprod : r * L * Dop ^ 2 = 0 := by simpa [K] using hKzero
      rcases mul_eq_zero.mp hprod with hrL | hDopSq
      · rcases mul_eq_zero.mp hrL with hrzero | hLzero
        · have hrNat : matrixRankBound m n = 0 := by
            dsimp [r] at hrzero
            exact_mod_cast hrzero
          have hmn : m = 0 ∨ n = 0 := by
            by_cases hm : m = 0
            · exact Or.inl hm
            · right
              by_contra hn
              have hminpos : 0 < min m n := (lt_min_iff).2
                ⟨Nat.pos_of_ne_zero hm, Nat.pos_of_ne_zero hn⟩
              change 0 < m.min n at hminpos
              have hrNat' : m.min n = 0 := by
                simpa [matrixRankBound] using hrNat
              rw [hrNat'] at hminpos
              omega
          have hstate : (deterministicMuonState P cfg t).W = Wstar := by
            rcases hmn with rfl | rfl <;> exact Subsingleton.elim _ _
          dsimp [x]
          rw [hstate, hstar.1]
          ring
        · have hsmooth0 : FrobeniusSmooth P 0 := by
            simpa [hLzero] using hsmooth
          exact objective_gap_eq_zero_of_frobeniusSmooth_zero
            P Wstar (deterministicMuonState P cfg t).W hfinite hstar hsmooth0
      · have hDopzero : Dop = 0 := (sq_eq_zero_iff).mp hDopSq
        have hbounded0 : BoundedOperatorDistance P cfg t Wstar 0 := by
          simpa [hDopzero] using hbounded
        have hstate := state_eq_star_of_bounded_zero P cfg t t Wstar hbounded0 (by simp)
        dsimp [x]
        rw [hstate, hstar.1]
        ring
    rw [sourceObjectiveGapAt_eq_objectiveGapAt]
    change x t ≤ theorem_4_6_sourceRhs P cfg t L Dop
    rw [hgapzero]
    dsimp [theorem_4_6_sourceRhs, K, r] at hKzero ⊢
    have hnum :
        2 * (matrixRankBound m n : ℝ) * L *
            (P.f cfg.W0 - P.fStar) * Dop ^ 2 = 0 := by
      calc
        _ = 2 * ((matrixRankBound m n : ℝ) * L * Dop ^ 2) *
            (P.f cfg.W0 - P.fStar) := by ring
        _ = 0 := by rw [hKzero]; ring
    rw [hnum]
    simp
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    have hrpos : 0 < r := by
      by_contra h
      have : r = 0 := le_antisymm (le_of_not_gt h) hr
      apply hKzero
      simp [K, this]
    have hLpos : 0 < L := by
      by_contra h
      have hL : L ≤ 0 := le_of_not_gt h
      have hLnonneg : 0 ≤ L := by
        have hrsqrt : 0 < Real.sqrt (matrixRankBound m n : ℝ) := by
          apply Real.sqrt_pos.2
          simpa [r] using hrpos
        exact nonneg_of_mul_nonneg_left
          (frobeniusSmooth_mul_sqrt_rankBound_nonneg hsmooth) hrsqrt
      have : L = 0 := le_antisymm hL hLnonneg
      apply hKzero
      simp [K, this]
    have hDopnonneg : 0 ≤ Dop := by
      have hdist := hbounded 0 (by simp)
      exact le_trans (by unfold spectralNorm; exact norm_nonneg _) hdist
    have hDoppos : 0 < Dop := by
      by_contra h
      have : Dop = 0 := le_antisymm (le_of_not_gt h) hDopnonneg
      apply hKzero
      simp [K, this]
    have hrLpos : 0 < r * L := mul_pos hrpos hLpos
    have hrec : ∀ k ∈ Finset.range t,
        x (k + 1) ≤ x k - x k ^ 2 / (2 * K) := by
      intro k hk
      let Wk := (deterministicMuonState P cfg k).W
      let Wnext := (deterministicMuonState P cfg (k + 1)).W
      let Gk := P.grad Wk
      let Dk := orthogonalizedDirection Gk
      let g : ℝ := nuclearNorm Gk
      let ηk : ℝ := g / (r * L)
      rcases hη k hk with ⟨hdom, heta⟩
      have heta' : cfg.eta k = ηk := by
        simpa [ηk, g, r, realizedSourceQuot, sourceQuot] using heta
      have hG : (deterministicMuonState P cfg k).G = Gk := by
        simpa [Gk, Wk, deterministicGradient] using
          deterministicMuon_G_eq_gradient P cfg k
      have hupdate : Wnext = Wk - ηk • Dk := by
        simpa [Wnext, Wk, Dk, hG, heta'] using
          deterministicMuon_W_succ_eq_source_update P cfg k
      have hsmoothStep := frobeniusSmooth_quadratic_upper_bound P hsmooth Wk Wnext
      have hdiff : Wnext - Wk = (-ηk) • Dk := by
        rw [hupdate]
        ext i j
        simp
      rw [hdiff] at hsmoothStep
      have hpair : frobeniusInner Gk ((-ηk) • Dk) = -ηk * g := by
        rw [show frobeniusInner Gk ((-ηk) • Dk) =
            -ηk * frobeniusInner Gk Dk by
          unfold frobeniusInner
          simp only [Matrix.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring]
        rw [orthogonalizedDirection_frobeniusInner_eq_nuclearNorm]
      have hnorm : frobeniusNorm ((-ηk) • Dk) ^ 2 =
          ηk ^ 2 * (Gk.rank : ℝ) := by
        rw [frobeniusNorm, norm_smul, Real.norm_eq_abs, abs_neg,
          mul_pow, sq_abs]
        congr 1
        simpa [frobeniusNorm] using orthogonalizedDirection_frobeniusNorm_sq Gk
      rw [hpair, hnorm] at hsmoothStep
      have hrank : (Gk.rank : ℝ) ≤ r := by
        dsimp [r]
        exact_mod_cast le_min (Matrix.rank_le_height Gk) (Matrix.rank_le_width Gk)
      have hcoef : 0 ≤ (L / 2) * ηk ^ 2 := by positivity
      have hquad := mul_le_mul_of_nonneg_left hrank hcoef
      have hdescent : P.f Wnext ≤ P.f Wk - g ^ 2 / (2 * (r * L)) := by
        have heta_g : ηk * g = g ^ 2 / (r * L) := by
          dsimp [ηk]
          field_simp [ne_of_gt hrLpos]
        have hquadval : (L / 2) * ηk ^ 2 * r =
            g ^ 2 / (2 * (r * L)) := by
          dsimp [ηk]
          field_simp [ne_of_gt hrpos, ne_of_gt hLpos]
        have hquad' : (L / 2) * (ηk ^ 2 * (Gk.rank : ℝ)) ≤
            g ^ 2 / (2 * (r * L)) := by
          calc
            _ = (L / 2) * ηk ^ 2 * (Gk.rank : ℝ) := by ring
            _ ≤ (L / 2) * ηk ^ 2 * r := hquad
            _ = _ := hquadval
        have hlinear : ηk * g = 2 * (g ^ 2 / (2 * (r * L))) := by
          rw [heta_g]
          field_simp [ne_of_gt hrLpos]
        change P.f Wnext ≤ P.f Wk + -ηk * g +
          (L / 2) * (ηk ^ 2 * (Gk.rank : ℝ)) at hsmoothStep
        linarith [hsmoothStep, hquad', hlinear]
      have hk' : k ∈ Finset.range (t + 1) :=
        Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hk) (by omega))
      have hgap := theorem_4_16_star_gradient_lower_bound_at
        P cfg t k Wstar Dop hstar hbounded hk'
      have hgapDiv : x k / Dop ≤ g := by
        apply (div_le_iff₀ hDoppos).2
        simpa [x, g, Gk, Wk, mul_comm] using hgap
      have hsquare : (x k / Dop) ^ 2 ≤ g ^ 2 := by
        exact (sq_le_sq₀ (div_nonneg (hx k hk') hDopnonneg)
          (nuclearNorm_nonneg_early Gk)).2 hgapDiv
      have hscaled := div_le_div_of_nonneg_right hsquare (by positivity : 0 ≤ 2 * (r * L))
      have hquadGap : x k ^ 2 / (2 * K) ≤ g ^ 2 / (2 * (r * L)) := by
        dsimp [K]
        field_simp [ne_of_gt hDoppos, ne_of_gt hrLpos] at hscaled ⊢
        nlinarith
      dsimp [x, Wnext, Wk] at hdescent ⊢
      linarith
    have hbound := quadratic_descent_recurrence_rational_bound x t K hKpos hx hrec
    rw [sourceObjectiveGapAt_eq_objectiveGapAt]
    change x t ≤ theorem_4_6_sourceRhs P cfg t L Dop
    have hxzero : x 0 = P.f cfg.W0 - P.fStar := by
      simp [x, deterministicMuonState, deterministicMuonBaseState]
    rw [hxzero] at hbound
    dsimp [theorem_4_6_sourceRhs, K, r] at hbound ⊢
    convert hbound using 1 <;> ring

theorem theorem_4_16_one_step_affine_recurrence
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    {T t : ℕ} (Wstar : Mat m n) {s η Dop : ℝ}
    (ht : t ∈ Finset.range T)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s)
    (hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (hsrc : theorem_4_16_sourceDomain T η Dop)
    (hη : ∀ k ∈ Finset.range T, cfg.eta k = η) :
    P.f ((deterministicMuonState P cfg (t + 1)).W) - P.fStar ≤
      (1 - η / Dop) *
          (P.f ((deterministicMuonState P cfg t).W) - P.fStar) +
        η ^ 2 * hessianDirectionalTerm P cfg t / 2 +
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
  have hDop : 0 < Dop := lt_of_lt_of_le hsrc.2.1 hsrc.2.2
  have hdescent := equation_15_third_order_descent_from_assumption
    (P := P) (cfg := cfg) ht hthird hη hsrc.2.1
  have ht' : t ∈ Finset.range (T + 1) :=
    Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp ht) (by omega))
  have hgap := theorem_4_16_star_gradient_lower_bound_at
    P cfg T t Wstar Dop hstar hbounded ht'
  have hgapDiv :
      (P.f ((deterministicMuonState P cfg t).W) - P.fStar) / Dop ≤
        nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) :=
    (div_le_iff₀ hDop).2 (by simpa [mul_comm] using hgap)
  have hscaled := mul_le_mul_of_nonneg_left hgapDiv hsrc.2.1.le
  have hscaled' :
      η / Dop *
          (P.f ((deterministicMuonState P cfg t).W) - P.fStar) ≤
        η * nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) := by
    convert hscaled using 1 <;> ring
  linarith

theorem theorem_4_16_source_formula_bound_at_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (s η Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s)
    (hbounded : BoundedOperatorDistance P cfg T Wstar Dop)
    (hsrc : theorem_4_16_sourceDomain T η Dop)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    sourceObjectiveGapAt P cfg T hfinite ≤
      theorem_4_16_sourceRhs P cfg T
        (sourceObjectiveInitialGap P cfg.W0 hfinite)
        (hessianDirectionalWeightedAverage P cfg T η Dop) s η Dop := by
  let q : ℝ := 1 - η / Dop
  let x : ℕ → ℝ := fun t =>
    P.f ((deterministicMuonState P cfg t).W) - P.fStar
  let c : ℝ :=
    s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6
  let a : ℕ → ℝ := fun t =>
    η ^ 2 * hessianDirectionalTerm P cfg t / 2 + c
  have hq := (theorem_4_16_contraction_of_sourceDomain hsrc).1
  have hrec : ∀ t ∈ Finset.range T, x (t + 1) ≤ q * x t + a t := by
    intro t ht
    convert theorem_4_16_one_step_affine_recurrence
      P cfg Wstar ht hstar hthird hbounded hsrc hη using 1 <;>
      simp [x, q, a, c] <;> ring
  have hunroll := affine_recurrence_unroll q x a T hq hrec
  let S : ℝ := ∑ t ∈ Finset.range T, q ^ (T - 1 - t)
  let Jsum : ℝ := ∑ t ∈ Finset.range T,
    q ^ (T - 1 - t) * hessianDirectionalTerm P cfg t
  have hS_eq : S = ∑ t ∈ Finset.range T, q ^ t := by
    dsimp [S]
    exact Finset.sum_range_reflect (fun t => q ^ t) T
  have hq_lt : q < 1 :=
    (theorem_4_16_contraction_of_sourceDomain hsrc).2
  have hone_sub_q : 0 < 1 - q := sub_pos.mpr hq_lt
  have hgeom : (∑ t ∈ Finset.range T, q ^ t) * (1 - q) = 1 - q ^ T :=
    geom_sum_mul_neg q T
  have hpow_nonneg : 0 ≤ q ^ T := pow_nonneg hq T
  have hS_le_inv : S ≤ 1 / (1 - q) := by
    rw [hS_eq]
    apply (le_div_iff₀ hone_sub_q).2
    rw [hgeom]
    linarith
  have hDop : 0 < Dop := lt_of_lt_of_le hsrc.2.1 hsrc.2.2
  have hSinv : 1 / (1 - q) = Dop / η := by
    dsimp [q]
    field_simp [ne_of_gt hDop, ne_of_gt hsrc.2.1] <;> ring
  have hS_le : S ≤ Dop / η := by simpa [hSinv] using hS_le_inv
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun t _ht => pow_nonneg hq _
  have hs : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound cfg.W0)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg
      (mul_nonneg (mul_nonneg hs (pow_nonneg hsrc.2.1.le 3))
        (Real.sqrt_nonneg _))
      (by norm_num)
  have hcubic : c * S ≤
      s * η ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
    have hscaled := mul_le_mul_of_nonneg_left hS_le hc
    dsimp [c] at hscaled
    have hηne : η ≠ 0 := ne_of_gt hsrc.2.1
    convert hscaled using 1 <;> field_simp [hηne] <;> ring
  have hJsum :
      Jsum = (T : ℝ) * hessianDirectionalWeightedAverage P cfg T η Dop := by
    have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hsrc.1)
    dsimp [Jsum, hessianDirectionalWeightedAverage, q]
    field_simp [hTne]
  have hsplit :
      (∑ t ∈ Finset.range T, q ^ (T - 1 - t) * a t) =
        η ^ 2 / 2 * Jsum + c * S := by
    dsimp [a, Jsum, S]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  have hxzero : x 0 = sourceObjectiveInitialGap P cfg.W0 hfinite := by
    simp [x, sourceObjectiveInitialGap, Objective.sourceFStar,
      deterministicMuonState, deterministicMuonBaseState]
  rw [hsplit, hxzero, hJsum] at hunroll
  dsimp [sourceObjectiveGapAt, Objective.sourceFStar,
    theorem_4_16_sourceRhs, q, x] at hunroll ⊢
  ring_nf at hunroll hcubic ⊢
  linarith

/- Formula-level arbitrary-horizon consumers for the two Appendix C.5 rate
   suppliers.  Both call the same Eq. (23) -> star-convex recurrence theorem;
   only the printed schedule used to obtain the contraction domain differs. -/
theorem theorem_4_16_positive_source_formula_bound_for_run
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s)
    (hrun : theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
      Wstar W0 Δ s Dop N) :
    sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
      theorem_4_16_sourceRhs P (cfgForHorizon N) N
        (sourceObjectiveInitialGap P (cfgForHorizon N).W0 hfinite)
        (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
          ((cfgForHorizon N).eta 0) Dop)
        s ((cfgForHorizon N).eta 0) Dop := by
  rcases hrun with ⟨hbounded, hrun⟩
  unfold theorem_4_16_positiveRunForHorizon at hrun
  dsimp at hrun
  rcases hrun with ⟨hN, _hW0, ⟨hlog, heta⟩, _hregime⟩
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  have heta0 := heta 0 hzero
  have hsrc : theorem_4_16_sourceDomain N ((cfgForHorizon N).eta 0) Dop := by
    rw [heta0]
    exact theorem_4_16_logEtaRealized_sourceDomain N Δ _ Dop hlog
  have hconst : ∀ t ∈ Finset.range N,
      (cfgForHorizon N).eta t = (cfgForHorizon N).eta 0 := by
    intro t ht
    exact (heta t ht).trans heta0.symm
  exact theorem_4_16_source_formula_bound_at_horizon
    P (cfgForHorizon N) N Wstar s ((cfgForHorizon N).eta 0) Dop
      hfinite hstar hthird hbounded hsrc hconst

theorem theorem_4_16_otherwise_source_formula_bound_for_run
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s)
    (hrun : theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
      Wstar W0 Δ s Dop N) :
    sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
      theorem_4_16_sourceRhs P (cfgForHorizon N) N
        (sourceObjectiveInitialGap P (cfgForHorizon N).W0 hfinite)
        (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
          ((cfgForHorizon N).eta 0) Dop)
        s ((cfgForHorizon N).eta 0) Dop := by
  rcases hrun with ⟨hbounded, hrun⟩
  unfold theorem_4_16_otherwiseRunForHorizon at hrun
  dsimp at hrun
  rcases hrun with ⟨hN, _hW0, ⟨hlog, heta⟩, _hregime⟩
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  have heta0 := heta 0 hzero
  have hsrc : theorem_4_16_sourceDomain N ((cfgForHorizon N).eta 0) Dop := by
    rw [heta0]
    exact theorem_4_16_otherwiseLogEtaRealized_sourceDomain
      m n N Δ s Dop hlog
  have hconst : ∀ t ∈ Finset.range N,
      (cfgForHorizon N).eta t = (cfgForHorizon N).eta 0 := by
    intro t ht
    exact (heta t ht).trans heta0.symm
  exact theorem_4_16_source_formula_bound_at_horizon
    P (cfgForHorizon N) N Wstar s ((cfgForHorizon N).eta 0) Dop
      hfinite hstar hthird hbounded hsrc hconst

/- Scalar schedule substitution shared by the positive Appendix C.5 family.
   This is the actual formula-to-display step: no displayed-bound predicate is
   assumed. -/
theorem theorem_4_16_positive_schedule_substitution
    (m n N : ℕ) (Δ Jtilde s Dop : ℝ)
    (hlog : theorem_4_16_logScheduleDomain N Δ Jtilde Dop)
    (hΔ : 0 ≤ Δ) (hJ : 0 ≤ Jtilde) (hs : 0 ≤ s) :
    theorem_4_16_sourceRhs (Objective.mk fun _ : Mat m n => 0)
        { W0 := 0, eta := fun _ => 0 } N Δ Jtilde s
        (theorem_4_16_logEtaRealized N Δ Jtilde Dop hlog) Dop ≤
      theorem_4_16_positiveDisplayedBound
        m n N Δ Jtilde s Dop := by
  let L : ℝ := sourceLogQuot ((N : ℝ) * Δ) (Dop ^ 2 * Jtilde)
  let a : ℝ := Dop / (N : ℝ) * L
  let η : ℝ := min a Dop
  have hN : 0 < (N : ℝ) := by exact_mod_cast hlog.1
  have hDop : 0 < Dop := hlog.2.1
  have hL : 0 < L := by
    dsimp [L, sourceLogQuot]
    exact Real.log_pos hlog.2.2.2
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos (div_pos hDop hN) hL
  have hη : theorem_4_16_logEtaRealized N Δ Jtilde Dop hlog = η := rfl
  have hη_nonneg : 0 ≤ η := (lt_min ha hDop).le
  have hη_le_a : η ≤ a := min_le_left _ _
  have hη_sq : η ^ 2 ≤ a ^ 2 := by nlinarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN
  have hcontract :
      (1 - η / Dop) ^ N * Δ ≤ Dop ^ 2 * Jtilde / (N : ℝ) := by
    rcases le_total a Dop with haD | hDa
    · have hηa : η = a := min_eq_left haD
      have hLN : L ≤ (N : ℝ) := by
        have hcancel : Dop * (L / (N : ℝ)) ≤ Dop * 1 := by
          convert haD using 1 <;> dsimp [a] <;>
            field_simp [hNne] <;> ring
        have hdiv : L / (N : ℝ) ≤ 1 := by nlinarith [hcancel]
        exact (div_le_one hN).mp hdiv
      have hpow : (1 - L / (N : ℝ)) ^ N ≤ Real.exp (-L) := by
        simpa using (Real.one_sub_div_pow_le_exp_neg (n := N) (t := L) hLN)
      have hscaled := mul_le_mul_of_nonneg_right hpow hΔ
      have hratio :
          sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * Jtilde) > 0 :=
        hlog.2.2.1.2
      have hexp : Real.exp (-L) =
          1 / sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * Jtilde) := by
        dsimp [L, sourceLogQuot]
        rw [Real.exp_neg, Real.exp_log hratio]
        simp [one_div]
      have hden : Dop ^ 2 * Jtilde ≠ 0 := hlog.2.2.1.1
      have hnum : (N : ℝ) * Δ ≠ 0 := by
        intro hzero
        have : sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * Jtilde) = 0 := by
          simp [sourceQuot, hzero]
        linarith
      have hΔne : Δ ≠ 0 := (mul_ne_zero_iff.mp hnum).2
      rw [hηa]
      have hq : 1 - a / Dop = 1 - L / (N : ℝ) := by
        dsimp [a]
        field_simp [hNne, ne_of_gt hDop]
      rw [hq]
      calc
        (1 - L / (N : ℝ)) ^ N * Δ ≤ Real.exp (-L) * Δ := hscaled
        _ = Dop ^ 2 * Jtilde / (N : ℝ) := by
          rw [hexp]
          dsimp [sourceQuot]
          field_simp [hNne, hden, hnum, hΔne]
    · have hηD : η = Dop := min_eq_right hDa
      rw [hηD]
      have hNzero : N ≠ 0 := Nat.ne_of_gt hlog.1
      have hright : 0 ≤ Dop ^ 2 * Jtilde / (N : ℝ) := by positivity
      simpa [hNzero, ne_of_gt hDop] using hright
  have hquad :
      η ^ 2 * Jtilde * (N : ℝ) / 2 ≤
        Dop ^ 2 * Jtilde / (2 * (N : ℝ)) * L ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hη_sq
      (mul_nonneg hJ hN.le)
    dsimp [a] at hscaled
    calc
      η ^ 2 * Jtilde * (N : ℝ) / 2 ≤
          a ^ 2 * Jtilde * (N : ℝ) / 2 := by nlinarith
      _ = Dop ^ 2 * Jtilde / (2 * (N : ℝ)) * L ^ 2 := by
        dsimp [a]
        field_simp [hNne]
  have hcubic :
      s * η ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 ≤
        s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
          (6 * (N : ℝ) ^ 2) * L ^ 2 := by
    have hcoef : 0 ≤ s * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_right hη_sq hcoef
    dsimp [a] at hscaled
    calc
      s * η ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 ≤
          s * a ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
        nlinarith
      _ = s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
          (6 * (N : ℝ) ^ 2) * L ^ 2 := by
        dsimp [a]
        field_simp [hNne]
  rw [hη]
  dsimp [theorem_4_16_sourceRhs,
    theorem_4_16_positiveDisplayedBound]
  dsimp [L] at hcontract hquad hcubic
  linarith

/- The positive displayed family is now a proved supplier from the retained
   fixed-horizon formula.  It is not an antecedent of the source-rate clause. -/
theorem theorem_4_16_positive_formula_to_displayed_family
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔ : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s) :
    theorem_4_16_positiveDisplayedBoundFamily P cfgForHorizon
      Wstar W0 Δ s Dop hfinite := by
  intro N hrun
  have hformula := theorem_4_16_positive_source_formula_bound_for_run
    P cfgForHorizon Wstar W0 Δ s Dop N hfinite hstar hthird hrun
  have hrun' := hrun.2
  unfold theorem_4_16_positiveRunForHorizon at hrun'
  dsimp at hrun'
  rcases hrun' with ⟨hN, hW0, ⟨hlog, heta⟩, _hregime⟩
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  have heta0 := heta 0 hzero
  let JN := hessianDirectionalWeightedAverage P (cfgForHorizon N) N
    ((cfgForHorizon N).eta 0) Dop
  have hgap_nonneg : 0 ≤ Δ := by
    have hinf : P.fStar ≤ P.f W0 := by
      simpa [Objective.fStar] using
        (csInf_le hfinite (show P.f W0 ∈ Set.range P.f from ⟨W0, rfl⟩))
    rw [← hΔ]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith
  have hJ : 0 ≤ JN := by
    have hquotpos :
        0 < sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * JN) := hlog.2.2.1.2
    have hnum_nonneg : 0 ≤ (N : ℝ) * Δ :=
      mul_nonneg (Nat.cast_nonneg _) hgap_nonneg
    rcases (div_pos_iff.mp (by simpa [sourceQuot] using hquotpos)) with
      ⟨_hnumpos, hdenpos⟩ | ⟨hnumneg, _hdenneg⟩
    · have hDop : 0 < Dop := hlog.2.1
      have hDopSq : 0 < Dop ^ 2 := sq_pos_of_pos hDop
      rcases mul_pos_iff.mp hdenpos with hpos | hneg
      · exact hpos.2.le
      · exact False.elim (not_lt_of_ge hDopSq.le hneg.1)
    · exact False.elim (not_lt_of_ge hnum_nonneg hnumneg)
  have hs : 0 ≤ s :=
    le_trans (norm_nonneg _) (hthird.bound (cfgForHorizon N).W0)
  have hdisplay := theorem_4_16_positive_schedule_substitution
    m n N Δ JN s Dop hlog hgap_nonneg hJ hs
  calc
    sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
        theorem_4_16_sourceRhs P (cfgForHorizon N) N
          (sourceObjectiveInitialGap P (cfgForHorizon N).W0 hfinite)
          JN s ((cfgForHorizon N).eta 0) Dop := hformula
    _ = theorem_4_16_sourceRhs (Objective.mk fun _ : Mat m n => 0)
        { W0 := 0, eta := fun _ => 0 } N Δ JN s
          (theorem_4_16_logEtaRealized N Δ JN Dop hlog) Dop := by
      dsimp [theorem_4_16_sourceRhs]
      rw [hW0, hΔ, heta0]
    _ ≤ theorem_4_16_positiveDisplayedBound
        m n N Δ JN s Dop := hdisplay

/- Corrected scalar substitution for the second Appendix C.5 schedule.  The
   `Jtilde` term is retained, and the only sign-sensitive enlargement of its
   coefficient consumes the explicit premise `0 ≤ Jtilde`. -/
theorem theorem_4_16_otherwise_corrected_schedule_substitution
    (m n N : ℕ) (Δ Jtilde s Dop : ℝ)
    (hlog : theorem_4_16_otherwiseLogScheduleDomain m n N Δ s Dop)
    (hΔ : 0 ≤ Δ) (hJ : 0 ≤ Jtilde) (hs : 0 ≤ s) :
    theorem_4_16_sourceRhs (Objective.mk fun _ : Mat m n => 0)
        { W0 := 0, eta := fun _ => 0 } N Δ Jtilde s
        (theorem_4_16_otherwiseLogEtaRealized m n N Δ s Dop hlog) Dop ≤
      theorem_4_16_otherwiseCorrectedDisplayedBound
        m n N Δ Jtilde s Dop := by
  let A : ℝ := Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)
  let L : ℝ := sourceLogQuot ((N : ℝ) ^ 2 * Δ) A
  let a : ℝ := Dop / (N : ℝ) * L
  let η : ℝ := min a Dop
  have hN : 0 < (N : ℝ) := by exact_mod_cast hlog.1
  have hDop : 0 < Dop := hlog.2.1
  have hL : 0 < L := by
    dsimp [L, A, sourceLogQuot]
    exact Real.log_pos hlog.2.2.2
  have ha : 0 < a := by
    dsimp [a]
    exact mul_pos (div_pos hDop hN) hL
  have hη :
      theorem_4_16_otherwiseLogEtaRealized m n N Δ s Dop hlog = η := rfl
  have hη_nonneg : 0 ≤ η := (lt_min ha hDop).le
  have hη_le_a : η ≤ a := min_le_left _ _
  have hη_sq : η ^ 2 ≤ a ^ 2 := by nlinarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN
  have hcontract :
      (1 - η / Dop) ^ N * Δ ≤ A / (N : ℝ) ^ 2 := by
    rcases le_total a Dop with haD | hDa
    · have hηa : η = a := min_eq_left haD
      have hLN : L ≤ (N : ℝ) := by
        have hcancel : Dop * (L / (N : ℝ)) ≤ Dop * 1 := by
          convert haD using 1 <;> dsimp [a] <;>
            field_simp [hNne] <;> ring
        have hdiv : L / (N : ℝ) ≤ 1 := by nlinarith [hcancel]
        exact (div_le_one hN).mp hdiv
      have hpow : (1 - L / (N : ℝ)) ^ N ≤ Real.exp (-L) := by
        simpa using (Real.one_sub_div_pow_le_exp_neg (n := N) (t := L) hLN)
      have hscaled := mul_le_mul_of_nonneg_right hpow hΔ
      have hratio : 0 < sourceQuot ((N : ℝ) ^ 2 * Δ) A := by
        simpa [A] using hlog.2.2.1.2
      have hexp : Real.exp (-L) = 1 / sourceQuot ((N : ℝ) ^ 2 * Δ) A := by
        dsimp [L, sourceLogQuot]
        rw [Real.exp_neg, Real.exp_log hratio]
        simp [one_div]
      have hden : A ≠ 0 := by
        change Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ≠ 0
        exact hlog.2.2.1.1
      have hnum : (N : ℝ) ^ 2 * Δ ≠ 0 := by
        intro hzero
        have : sourceQuot ((N : ℝ) ^ 2 * Δ) A = 0 := by
          simp [sourceQuot, hzero]
        linarith
      have hΔne : Δ ≠ 0 := (mul_ne_zero_iff.mp hnum).2
      rw [hηa]
      have hq : 1 - a / Dop = 1 - L / (N : ℝ) := by
        dsimp [a]
        field_simp [hNne, ne_of_gt hDop]
      rw [hq]
      calc
        (1 - L / (N : ℝ)) ^ N * Δ ≤ Real.exp (-L) * Δ := hscaled
        _ = A / (N : ℝ) ^ 2 := by
          rw [hexp]
          dsimp [sourceQuot]
          field_simp [hNne, hden, hnum, hΔne]
    · have hηD : η = Dop := min_eq_right hDa
      rw [hηD]
      have hNzero : N ≠ 0 := Nat.ne_of_gt hlog.1
      have hright : 0 ≤ A / (N : ℝ) ^ 2 := by
        dsimp [A]
        positivity
      simpa [hNzero, ne_of_gt hDop] using hright
  have hquad :
      η ^ 2 * Jtilde * (N : ℝ) / 2 ≤
        Dop ^ 2 * Jtilde / (2 * (N : ℝ)) * L ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hη_sq
      (mul_nonneg hJ hN.le)
    calc
      η ^ 2 * Jtilde * (N : ℝ) / 2 ≤
          a ^ 2 * Jtilde * (N : ℝ) / 2 := by nlinarith
      _ = Dop ^ 2 * Jtilde / (2 * (N : ℝ)) * L ^ 2 := by
        dsimp [a]
        field_simp [hNne]
  have hcubic :
      s * η ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 ≤
        s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
          (6 * (N : ℝ) ^ 2) * L ^ 2 := by
    have hcoef : 0 ≤ s * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_right hη_sq hcoef
    calc
      s * η ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 ≤
          s * a ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
        nlinarith
      _ = s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
          (6 * (N : ℝ) ^ 2) * L ^ 2 := by
        dsimp [a]
        field_simp [hNne]
  rw [hη]
  dsimp [theorem_4_16_sourceRhs,
    theorem_4_16_otherwiseCorrectedDisplayedBound]
  dsimp [A, L] at hcontract hquad hcubic
  ring_nf at hcontract hquad hcubic ⊢
  linarith

/- Direct formula consumer for the corrected otherwise family.  It calls the
   retained fixed-horizon source theorem and obtains `0 ≤ JN` only at the
   uniform branch threshold; no all-horizon sign is inferred from the
   pointwise asymptotic wrapper. -/
theorem theorem_4_16_otherwise_formula_to_corrected_displayed_family
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hΔ : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s)
    (hfamily : theorem_4_16_otherwiseFamilyBranchRegime P cfgForHorizon
      Wstar W0 Δ s Dop) :
    theorem_4_16_otherwiseCorrectedDisplayedBoundEventually P cfgForHorizon
      Wstar W0 Δ s Dop hfinite := by
  rcases hfamily with ⟨C, N₀, hC, hfamily⟩
  refine ⟨N₀, ?_⟩
  intro N hrun hNlarge
  have hformula := theorem_4_16_otherwise_source_formula_bound_for_run
    P cfgForHorizon Wstar W0 Δ s Dop N hfinite hstar hthird hrun
  have hreg := hfamily N hrun hNlarge
  dsimp at hreg
  have hrun' := hrun.2
  unfold theorem_4_16_otherwiseRunForHorizon at hrun'
  dsimp at hrun'
  rcases hrun' with ⟨hN, hW0, ⟨hlog, heta⟩, _hregime⟩
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  have heta0 := heta 0 hzero
  let JN := hessianDirectionalWeightedAverage P (cfgForHorizon N) N
    ((cfgForHorizon N).eta 0) Dop
  have hgap_nonneg : 0 ≤ Δ := by
    have hinf : P.fStar ≤ P.f W0 := by
      simpa [Objective.fStar] using
        (csInf_le hfinite (show P.f W0 ∈ Set.range P.f from ⟨W0, rfl⟩))
    rw [← hΔ]
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    linarith
  have hs : 0 ≤ s :=
    le_trans (norm_nonneg _) (hthird.bound (cfgForHorizon N).W0)
  have hdisplay := theorem_4_16_otherwise_corrected_schedule_substitution
    m n N Δ JN s Dop hlog hgap_nonneg hreg.1 hs
  calc
    sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
        theorem_4_16_sourceRhs P (cfgForHorizon N) N
          (sourceObjectiveInitialGap P (cfgForHorizon N).W0 hfinite)
          JN s ((cfgForHorizon N).eta 0) Dop := hformula
    _ = theorem_4_16_sourceRhs (Objective.mk fun _ : Mat m n => 0)
        { W0 := 0, eta := fun _ => 0 } N Δ JN s
          (theorem_4_16_otherwiseLogEtaRealized m n N Δ s Dop hlog) Dop := by
      dsimp [theorem_4_16_sourceRhs]
      rw [hW0, hΔ, heta0]
    _ ≤ theorem_4_16_otherwiseCorrectedDisplayedBound
        m n N Δ JN s Dop := hdisplay

theorem theorem_4_16_positive_full_scale_boundary_of_source_runs
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hthird : ThirdDerivativeBounded P s)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N) :
    theorem_4_16_positiveFullScaleSourceBoundary m n s Dop := by
  have hrun := hruns 1 (by norm_num [horizonDomain])
  have hrun' := hrun.2
  unfold theorem_4_16_positiveRunForHorizon at hrun'
  dsimp at hrun'
  rcases hrun' with ⟨_hN, _hW0, ⟨hlog, _heta⟩, _hregime⟩
  have hs : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound W0)
  have hDop : 0 < Dop := hlog.2.1
  have hscale :
      0 ≤ s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop := by
    positivity
  constructor
  · intro _hpositive
    trivial
  · intro _htrue
    rcases hscale.eq_or_lt with hzero | hpos
    · exact Or.inr hzero.symm
    · exact Or.inl hpos

theorem theorem_4_16_positive_scalar_crossing_transfer
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hstar : StarConvex P Wstar)
    (hthird : ThirdDerivativeBounded P s)
    (hΔ : sourceObjectiveInitialGap P cfg.W0 hfinite = Δ)
    (hcrossing : theorem_4_16_positiveScalarCrossing
      P cfg Wstar Δ s Dop cfgForHorizon) :
    TildeSourceHorizonObjectivePrecisionComplexityWithHorizonRate P hfinite cfgForHorizon
      (fun N => theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
        Wstar cfg.W0 Δ s Dop N)
      (fun N ε => theorem_4_16_complexityRate m n
        (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
          ((cfgForHorizon N).eta 0) Dop) Dop ε)
      (theoremScope "Theorem 4.16 positive-Jtilde epsilon complexity" ["epsilon"]) := by
  have hdisplay := theorem_4_16_positive_formula_to_displayed_family
    P cfgForHorizon Wstar cfg.W0 Δ s Dop hfinite hΔ hstar hthird
  rcases hcrossing with ⟨k, C, ε₀, hC, hε₀, hscope, hcrossing⟩
  refine ⟨k, C, ε₀, hC, hε₀, ?_, ?_⟩
  · simpa [theoremScope] using hscope
  · intro ε hε hεsmall
    rcases hcrossing ε hε hεsmall with ⟨N, hrun, hscalar, hN⟩
    refine ⟨N, hrun, le_trans (hdisplay N hrun) hscalar, hN⟩

/- The remaining Appendix C.5 rate obstruction is scalar, not a missing
   Hessian or recurrence API.  The printed otherwise display drops the
   `eta^2 * Jtilde * T / 2` term after assuming only a hidden-constant upper
   comparison.  At unit horizon/step/log scale, `Jtilde = 4` and comparison
   constant `4` satisfy that premise, while the claimed coefficient-one
   display is false. -/
theorem theorem_4_16_otherwise_displayed_scalar_counterexample :
    let Jtilde : ℝ := 4
    let curvatureScale : ℝ := 1
    let comparisonConstant : ℝ := 4
    0 ≤ Jtilde ∧
      Jtilde ≤ comparisonConstant * curvatureScale ∧
      ¬ (Jtilde / 2 + curvatureScale / 6 ≤
        curvatureScale + curvatureScale / 6) := by
  norm_num

/- In the positive branch the source comparison degenerates when the
   third-order scale is zero.  Then it places no lower bound on `Jtilde`, and
   the logarithm need not be polylogarithmic in the horizon.  This exact
   horizon-one witness refutes deriving the logarithmic envelope from the
   current branch comparison without a nondegeneracy boundary. -/
theorem theorem_4_16_positive_log_envelope_degenerate_counterexample
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ Jtilde : ℝ,
      0 < Jtilde ∧
      (0 : ℝ) ≤ (1 : ℝ) * (1 : ℝ) * Jtilde ∧
      sourceLogQuotDomain 1 Jtilde ∧
      1 < sourceQuot 1 Jtilde ∧
      K * natPolylogEnvelope 2 1 < (sourceLogQuot 1 Jtilde) ^ 2 := by
  let B : ℝ := K + 1
  refine ⟨Real.exp (-B), Real.exp_pos _, by positivity, ?_, ?_, ?_⟩
  · constructor
    · exact ne_of_gt (Real.exp_pos _)
    · have hB : 0 < B := by dsimp [B]; linarith
      have hquot : sourceQuot 1 (Real.exp (-B)) = Real.exp B := by
        simp [sourceQuot, Real.exp_neg]
      rw [hquot]
      exact Real.exp_pos _
  · have hB : 0 < B := by dsimp [B]; linarith
    have hquot : sourceQuot 1 (Real.exp (-B)) = Real.exp B := by
      simp [sourceQuot, Real.exp_neg]
    rw [hquot]
    simpa using Real.exp_lt_exp_of_lt hB
  · have hlog : sourceLogQuot 1 (Real.exp (-B)) = B := by
      simp [sourceLogQuot, sourceQuot, Real.exp_neg]
    rw [hlog]
    simp [natPolylogEnvelope]
    dsimp [B]
    nlinarith

/- The fixed-horizon tilde-rate estimate does not by itself select a horizon
   when its coefficient is the horizon-dependent sequence `J_N`.  The scalar
   family `J_N = N`, `gap_N = 1` satisfies the corresponding `gap_N ≤ J_N/N`
   bound at every positive horizon but never reaches any accuracy below one.
   This is the exact crossing/selection obstruction in the positive
   precision-complexity conjunct. -/
theorem theorem_4_16_horizon_dependent_rate_selection_counterexample :
    (∀ N : ℕ, horizonDomain N →
      (1 : ℝ) ≤ (N : ℝ) / (N : ℝ)) ∧
    ¬ (∃ k : ℕ, ∃ C ε₀ : ℝ,
      0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ N : ℕ,
          (1 : ℝ) ≤ ε ∧
          (N : ℝ) ≤ C *
            (accuracyPolylogEnvelope k ε * ((N : ℝ) * ε⁻¹))) := by
  constructor
  · intro N hN
    have hNne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
    norm_num
  · rintro ⟨k, C, ε₀, hC, hε₀, hselection⟩
    let ε : ℝ := min (ε₀ / 2) (1 / 2)
    have hε : 0 < ε := lt_min (half_pos hε₀) (by norm_num)
    have hεle : ε ≤ ε₀ := le_trans (min_le_left _ _) (by linarith)
    rcases hselection ε hε hεle with ⟨N, hgap, _horizonBound⟩
    have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
    linarith

/- A fixed positive scalar multiplying `N²` contributes only a constant to
   its logarithm.  This is the scalar fact used by both repaired Appendix C.5
   branches; keeping it separate makes clear that no displayed-bound family is
   being assumed. -/
theorem fixed_mul_nat_sq_log_sq_le_polylog
    (K : ℝ) (hK : 0 < K) :
    ∃ Clog : ℝ, 0 < Clog ∧
      ∀ N : ℕ, horizonDomain N →
        (Real.log (K * (N : ℝ) ^ 2)) ^ 2 ≤
          Clog * natPolylogEnvelope 2 N := by
  let Clog : ℝ := (|Real.log K| + 2) ^ 2
  refine ⟨Clog, ?_, ?_⟩
  · dsimp [Clog]
    positivity
  · intro N hN
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hN)))
    let M : ℝ := max 1 (Real.log (N : ℝ))
    have hMone : 1 ≤ M := by exact le_max_left _ _
    have hlogNM : Real.log (N : ℝ) ≤ M := by exact le_max_right _ _
    have hlogEq :
        Real.log (K * (N : ℝ) ^ 2) =
          Real.log K + 2 * Real.log (N : ℝ) := by
      rw [Real.log_mul (ne_of_gt hK) (pow_ne_zero 2 (ne_of_gt hNreal)),
        Real.log_pow]
      norm_num
    have habs :
        |Real.log (K * (N : ℝ) ^ 2)| ≤ (|Real.log K| + 2) * M := by
      rw [hlogEq]
      calc
        |Real.log K + 2 * Real.log (N : ℝ)| ≤
            |Real.log K| + |2 * Real.log (N : ℝ)| := abs_add_le _ _
        _ = |Real.log K| + 2 * Real.log (N : ℝ) := by
          rw [abs_of_nonneg (mul_nonneg (by norm_num) hlogN)]
        _ ≤ |Real.log K| * M + 2 * M := by
          apply add_le_add
          · nlinarith [abs_nonneg (Real.log K)]
          · gcongr
        _ = (|Real.log K| + 2) * M := by ring
    have hright : 0 ≤ (|Real.log K| + 2) * M := by positivity
    have hsq := (sq_le_sq₀ (abs_nonneg _) hright).2 habs
    dsimp [Clog, M, natPolylogEnvelope]
    calc
      Real.log (K * (N : ℝ) ^ 2) ^ 2 =
          |Real.log (K * (N : ℝ) ^ 2)| ^ 2 := by rw [sq_abs]
      _ ≤ ((|Real.log K| + 2) * max 1 (Real.log (N : ℝ))) ^ 2 := hsq
      _ = (|Real.log K| + 2) ^ 2 * max 1 (Real.log (N : ℝ)) ^ 2 := by ring

theorem theorem_4_16_otherwise_log_envelope_of_source_runs
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hthird : ThirdDerivativeBounded P s)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N) :
    ∃ Clog : ℝ, ∃ Nlog : ℕ, 0 < Clog ∧
      ∀ N : ℕ,
        theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
          Wstar W0 Δ s Dop N →
        Nlog ≤ N →
        (sourceLogQuot ((N : ℝ) ^ 2 * Δ)
          (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) ^ 2 ≤
            Clog * natPolylogEnvelope 2 N := by
  let A : ℝ := Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)
  have hrunOne := hruns 1 (by norm_num [horizonDomain])
  have hrunOne' := hrunOne.2
  unfold theorem_4_16_otherwiseRunForHorizon at hrunOne'
  dsimp at hrunOne'
  rcases hrunOne' with ⟨_hOne, _hW0, ⟨hlogOne, _heta⟩, _hregime⟩
  have hs : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound W0)
  have hDop : 0 < Dop := hlogOne.2.1
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hA_ne : A ≠ 0 := by
    change Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ≠ 0
    exact hlogOne.2.2.1.1
  have hA : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA_ne)
  have hΔ : 0 < Δ := by
    have hquot : 0 < sourceQuot Δ A := by
      simpa [A] using hlogOne.2.2.1.2
    rcases div_pos_iff.mp (by simpa [sourceQuot] using hquot) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hA.le) hneg.2)
  let K : ℝ := Δ / A
  have hK : 0 < K := div_pos hΔ hA
  rcases fixed_mul_nat_sq_log_sq_le_polylog K hK with ⟨Clog, hClog, hbound⟩
  refine ⟨Clog, 1, hClog, ?_⟩
  intro N hrun _hNlarge
  have hN : horizonDomain N := hrun.2.1
  have heq :
      sourceLogQuot ((N : ℝ) ^ 2 * Δ) A =
        Real.log (K * (N : ℝ) ^ 2) := by
    dsimp [sourceLogQuot, sourceQuot, K]
    congr 1
    field_simp [ne_of_gt hA]
  rw [heq]
  exact hbound N hN

theorem theorem_4_16_positive_log_envelope_of_source_runs
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hfull : theorem_4_16_positiveFullScaleDomain m n s Dop)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N)
    (hfamily : theorem_4_16_positiveFamilyBranchRegime P cfgForHorizon
      Wstar W0 Δ s Dop) :
    ∃ Clog : ℝ, ∃ Nlog : ℕ, 0 < Clog ∧
      ∀ N : ℕ,
        theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
          Wstar W0 Δ s Dop N →
        Nlog ≤ N →
        (sourceLogQuot ((N : ℝ) * Δ)
          (Dop ^ 2 * hessianDirectionalWeightedAverage P
            (cfgForHorizon N) N ((cfgForHorizon N).eta 0) Dop)) ^ 2 ≤
            Clog * natPolylogEnvelope 2 N := by
  rcases hfamily with ⟨C, N₀, hC, hfamily⟩
  let B : ℝ := s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop
  have hB : 0 < B := by simpa [B] using hfull
  let Nbase : ℕ := max N₀ 1
  have hNbase : horizonDomain Nbase := by dsimp [horizonDomain, Nbase]; omega
  have hrunBase := hruns Nbase hNbase
  have hregBase := hfamily Nbase hrunBase (by dsimp [Nbase]; omega)
  dsimp at hregBase
  have hrunBase' := hrunBase.2
  unfold theorem_4_16_positiveRunForHorizon at hrunBase'
  dsimp at hrunBase'
  rcases hrunBase' with
    ⟨_hNbase, _hW0base, ⟨hlogBase, _hetaBase⟩, _hregimeBase⟩
  let Jbase : ℝ := hessianDirectionalWeightedAverage P
    (cfgForHorizon Nbase) Nbase ((cfgForHorizon Nbase).eta 0) Dop
  have hDop : 0 < Dop := hlogBase.2.1
  have hJbase_ne : Jbase ≠ 0 := by
    have hden := hlogBase.2.2.1.1
    change Dop ^ 2 * Jbase ≠ 0 at hden
    exact (mul_ne_zero_iff.mp hden).2
  have hJbase : 0 < Jbase := lt_of_le_of_ne hregBase.1 (Ne.symm hJbase_ne)
  have hΔ : 0 < Δ := by
    have hquot : 0 < sourceQuot ((Nbase : ℝ) * Δ) (Dop ^ 2 * Jbase) := by
      simpa [Jbase] using hlogBase.2.2.1.2
    have hden : 0 < Dop ^ 2 * Jbase := mul_pos (sq_pos_of_pos hDop) hJbase
    have hnum : 0 < (Nbase : ℝ) * Δ := by
      rcases div_pos_iff.mp (by simpa [sourceQuot] using hquot) with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hden.le) hneg.2)
    rcases mul_pos_iff.mp hnum with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge (Nat.cast_nonneg Nbase)) hneg.1)
  let K : ℝ := C * Δ / (Dop ^ 2 * B)
  have hK : 0 < K := by dsimp [K]; positivity
  rcases fixed_mul_nat_sq_log_sq_le_polylog K hK with ⟨Clog, hClog, hbound⟩
  refine ⟨Clog, N₀, hClog, ?_⟩
  intro N hrun hNlarge
  have hreg := hfamily N hrun hNlarge
  dsimp at hreg
  have hrun' := hrun.2
  unfold theorem_4_16_positiveRunForHorizon at hrun'
  dsimp at hrun'
  rcases hrun' with ⟨hN, _hW0, ⟨hlog, _heta⟩, _hregime⟩
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let JN : ℝ := hessianDirectionalWeightedAverage P
    (cfgForHorizon N) N ((cfgForHorizon N).eta 0) Dop
  have hJN_ne : JN ≠ 0 := by
    have hden := hlog.2.2.1.1
    change Dop ^ 2 * JN ≠ 0 at hden
    exact (mul_ne_zero_iff.mp hden).2
  have hJN : 0 < JN := lt_of_le_of_ne hreg.1 (Ne.symm hJN_ne)
  have hden : 0 < Dop ^ 2 * JN := mul_pos (sq_pos_of_pos hDop) hJN
  have hquotpos : 0 < sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * JN) := by
    simpa [JN] using hlog.2.2.1.2
  have hupperpos : 0 < K * (N : ℝ) ^ 2 := by positivity
  have hquotle :
      sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * JN) ≤
        K * (N : ℝ) ^ 2 := by
    unfold sourceQuot
    apply (div_le_iff₀ hden).2
    have hscaled := mul_le_mul_of_nonneg_left hreg.2
      (mul_nonneg (Nat.cast_nonneg N) hΔ.le)
    calc
      (N : ℝ) * Δ ≤
          ((N : ℝ) * Δ * (C * (N : ℝ) * JN)) / B :=
        (le_div_iff₀ hB).2 (by simpa [B, JN] using hscaled)
      _ = K * (N : ℝ) ^ 2 * (Dop ^ 2 * JN) := by
        dsimp [K]
        field_simp [ne_of_gt hDop, ne_of_gt hB]
  have hlogle :
      Real.log (sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * JN)) ≤
        Real.log (K * (N : ℝ) ^ 2) :=
    Real.strictMonoOn_log.monotoneOn hquotpos hupperpos hquotle
  have hlogpos :
      0 < Real.log (sourceQuot ((N : ℝ) * Δ) (Dop ^ 2 * JN)) :=
    Real.log_pos hlog.2.2.2
  have hsq := (sq_le_sq₀ hlogpos.le (le_trans hlogpos.le hlogle)).2 hlogle
  calc
    (sourceLogQuot ((N : ℝ) * Δ) (Dop ^ 2 * JN)) ^ 2 ≤
        (Real.log (K * (N : ℝ) ^ 2)) ^ 2 := by
      simpa [sourceLogQuot] using hsq
    _ ≤ Clog * natPolylogEnvelope 2 N := hbound N hN

/- Neutral aggregation for the corrected second-branch formula.  Its corrected
   displayed-family premise is supplied directly by
   `theorem_4_16_otherwise_formula_to_corrected_displayed_family`; the old
   coefficient-one route is not represented in this interface. -/
theorem theorem_4_16_otherwise_corrected_display_quadratic_bound
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hfamily : theorem_4_16_otherwiseFamilyBranchRegime P cfgForHorizon
      Wstar cfg.W0 Δ s Dop)
    (hdisplay : theorem_4_16_otherwiseCorrectedDisplayedBoundEventually P cfgForHorizon
      Wstar cfg.W0 Δ s Dop hfinite)
    (hlogEnvelope : ∃ Clog : ℝ, ∃ Nlog : ℕ, 0 < Clog ∧
      ∀ N : ℕ,
        theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
          Wstar cfg.W0 Δ s Dop N →
        Nlog ≤ N →
        (sourceLogQuot ((N : ℝ) ^ 2 * Δ)
          (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) ^ 2 ≤
            Clog * natPolylogEnvelope 2 N) :
    DomainAsymptoticUpperNatOn
      (fun N => theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
          Wstar cfg.W0 Δ s Dop N ∧
        theorem_4_16_otherwiseBranchRateDomain m n s Dop N)
      (fun N _hN => sourceObjectiveGapAt P (cfgForHorizon N) N hfinite)
      (fun N hN => natPolylogEnvelope 2 N *
        theorem_4_16_otherwiseBranchRateRealized m n s Dop N hN.2)
      (theoremScope "Theorem 4.16 otherwise branch rate" ["T"]) := by
  rcases hfamily with ⟨Cbranch, Nbranch, hCbranch, hfamily⟩
  rcases hdisplay with ⟨Ndisplay, hdisplay⟩
  rcases hlogEnvelope with ⟨C, Nlog, hC, hlogEnvelope⟩
  refine ⟨1 + Cbranch * C / 2 + C / 6,
    max (max Nbranch Ndisplay) Nlog, by positivity, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
    positivity
  · intro N hN hNlarge
    rcases hN with ⟨hrun, hrateDom⟩
    have hfamilyN := hfamily N hrun
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hNlarge))
    dsimp at hfamilyN
    have hlogBound := hlogEnvelope N hrun
      (le_trans (le_max_right _ _) hNlarge)
    have hrun' := hrun.2
    unfold theorem_4_16_otherwiseRunForHorizon at hrun'
    dsimp at hrun'
    rcases hrun' with ⟨hNpos, _hW0, ⟨hlog, _heta⟩, _hregime⟩
    have hDop : 0 < Dop := hlog.2.1
    have hs : 0 ≤ s :=
      le_trans (norm_nonneg _) (hthird.bound (cfgForHorizon N).W0)
    let R : ℝ :=
      s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 / (N : ℝ) ^ 2
    let L2 : ℝ :=
      (sourceLogQuot ((N : ℝ) ^ 2 * Δ)
        (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) ^ 2
    let poly : ℝ := natPolylogEnvelope 2 N
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have hR : 0 ≤ R := by
      dsimp [R]
      positivity
    have hpoly : 1 ≤ poly := by
      dsimp [poly, natPolylogEnvelope]
      have hmax : 1 ≤ max 1 (Real.log (N : ℝ)) := le_max_left _ _
      nlinarith [sq_nonneg (max 1 (Real.log (N : ℝ)) - 1)]
    have hlogBound' : L2 ≤ C * poly := by
      simpa [L2, poly] using hlogBound
    have hfirst : R ≤ poly * R := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hpoly hR
    have hsecond : R / 6 * L2 ≤ (C / 6) * poly * R := by
      have hscaled := mul_le_mul_of_nonneg_left hlogBound'
        (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 6))
      calc
        R / 6 * L2 ≤ R / 6 * (C * poly) := hscaled
        _ = (C / 6) * poly * R := by ring
    have hformula := hdisplay N hrun
      (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hNlarge))
    let JN := hessianDirectionalWeightedAverage P (cfgForHorizon N) N
      ((cfgForHorizon N).eta 0) Dop
    let Q : ℝ := Dop ^ 2 * JN / (2 * (N : ℝ))
    have hQ : 0 ≤ Q := by
      dsimp [Q]
      exact div_nonneg (mul_nonneg (sq_nonneg Dop) hfamilyN.1)
        (mul_nonneg (by norm_num) hNreal.le)
    have hQbound : Q ≤ (Cbranch / 2) * R := by
      have hden : 0 ≤ ((2 : ℝ) * (N : ℝ) ^ 2)⁻¹ := by positivity
      have hscaled := mul_le_mul_of_nonneg_right hfamilyN.2 hden
      dsimp [Q, R, JN] at hscaled ⊢
      convert hscaled using 1 <;> field_simp [ne_of_gt hNreal] <;> ring
    have hquadratic :
        Q * L2 ≤ (Cbranch * C / 2) * poly * R := by
      calc
        Q * L2 ≤ (Cbranch / 2 * R) * L2 :=
          mul_le_mul_of_nonneg_right hQbound (sq_nonneg _)
        _ ≤ (Cbranch / 2 * R) * (C * poly) :=
          mul_le_mul_of_nonneg_left hlogBound' (by positivity)
        _ = (Cbranch * C / 2) * poly * R := by ring
    calc
      sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
          theorem_4_16_otherwiseCorrectedDisplayedBound
            m n N Δ JN s Dop := hformula
      _ = R + Q * L2 + R / 6 * L2 := by
        dsimp [theorem_4_16_otherwiseCorrectedDisplayedBound,
          R, Q, JN, L2]
        field_simp [ne_of_gt hNreal]
        <;> ring
      _ ≤ poly * R + (Cbranch * C / 2) * poly * R +
          (C / 6) * poly * R :=
        add_le_add (add_le_add hfirst hquadratic) hsecond
      _ = (1 + Cbranch * C / 2 + C / 6) *
          (natPolylogEnvelope 2 N *
            theorem_4_16_otherwiseBranchRateRealized m n s Dop N hrateDom) := by
        simp [R, poly, theorem_4_16_otherwiseBranchRateRealized,
          realizedSourceQuot, sourceQuot, realizedSourceSqrt, sourceSqrt]
        ring

theorem theorem_4_16_otherwise_corrected_display_to_tilde_rate
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hfamily : theorem_4_16_otherwiseFamilyBranchRegime P cfgForHorizon
      Wstar cfg.W0 Δ s Dop)
    (hdisplay : theorem_4_16_otherwiseCorrectedDisplayedBoundEventually P cfgForHorizon
      Wstar cfg.W0 Δ s Dop hfinite)
    (hlogEnvelope : ∃ Clog : ℝ, ∃ Nlog : ℕ, 0 < Clog ∧
      ∀ N : ℕ,
        theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
          Wstar cfg.W0 Δ s Dop N →
        Nlog ≤ N →
        (sourceLogQuot ((N : ℝ) ^ 2 * Δ)
          (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) ^ 2 ≤
            Clog * natPolylogEnvelope 2 N) :
    TildeAsymptoticUpperNatOn
      (fun N => theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
          Wstar cfg.W0 Δ s Dop N ∧
        theorem_4_16_otherwiseBranchRateDomain m n s Dop N)
      (fun N _hN => sourceObjectiveGapAt P (cfgForHorizon N) N hfinite)
      (fun N hN => theorem_4_16_otherwiseBranchRateRealized m n s Dop N hN.2)
      (theoremScope "Theorem 4.16 otherwise branch rate" ["T"]) := by
  refine ⟨2, ?_⟩
  exact theorem_4_16_otherwise_corrected_display_quadratic_bound
    P cfg cfgForHorizon Wstar Δ s Dop hfinite hthird hfamily hdisplay hlogEnvelope

theorem theorem_4_16_positive_display_to_tilde_rate
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hfamily : theorem_4_16_positiveFamilyBranchRegime P cfgForHorizon
      Wstar W0 Δ s Dop)
    (hdisplay : theorem_4_16_positiveDisplayedBoundFamily P cfgForHorizon
      Wstar W0 Δ s Dop hfinite)
    (hlogEnvelope : ∃ Clog : ℝ, ∃ Nlog : ℕ, 0 < Clog ∧
      ∀ N : ℕ,
        theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
          Wstar W0 Δ s Dop N →
        Nlog ≤ N →
        (sourceLogQuot ((N : ℝ) * Δ)
          (Dop ^ 2 * hessianDirectionalWeightedAverage P
            (cfgForHorizon N) N ((cfgForHorizon N).eta 0) Dop)) ^ 2 ≤
            Clog * natPolylogEnvelope 2 N) :
    TildeAsymptoticUpperNatOn
      (fun N => theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
          Wstar W0 Δ s Dop N ∧
        theorem_4_16_branchRateDomain m n
          (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
            ((cfgForHorizon N).eta 0) Dop) Dop N)
      (fun N _hN => sourceObjectiveGapAt P (cfgForHorizon N) N hfinite)
      (fun N hN => theorem_4_16_branchRateRealized m n
        (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
          ((cfgForHorizon N).eta 0) Dop) Dop N hN.2)
      (theoremScope "Theorem 4.16 positive-Jtilde branch rate" ["T"]) := by
  rcases hfamily with ⟨Cbranch, Nbranch, hCbranch, hfamily⟩
  rcases hlogEnvelope with ⟨C, Nlog, hC, hlogEnvelope⟩
  refine ⟨2, 1 + C / 2 + Cbranch * C / 6,
    max Nbranch Nlog, by positivity, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
    positivity
  · intro N hN hNlarge
    rcases hN with ⟨hrun, hrateDom⟩
    have hfamilyN := hfamily N hrun
      (le_trans (le_max_left _ _) hNlarge)
    dsimp at hfamilyN
    have hlogBound := hlogEnvelope N hrun
      (le_trans (le_max_right _ _) hNlarge)
    have hrun' := hrun.2
    unfold theorem_4_16_positiveRunForHorizon at hrun'
    dsimp at hrun'
    rcases hrun' with ⟨hNpos, _hW0, ⟨hlog, _heta⟩, _hregime⟩
    have hDop : 0 < Dop := hlog.2.1
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
    let JN := hessianDirectionalWeightedAverage P (cfgForHorizon N) N
      ((cfgForHorizon N).eta 0) Dop
    let R : ℝ := Dop ^ 2 * JN / (N : ℝ)
    let G : ℝ :=
      s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 / (N : ℝ) ^ 2
    let L2 : ℝ :=
      (sourceLogQuot ((N : ℝ) * Δ) (Dop ^ 2 * JN)) ^ 2
    let poly : ℝ := natPolylogEnvelope 2 N
    have hR : 0 ≤ R := by
      dsimp [R]
      exact div_nonneg (mul_nonneg (sq_nonneg Dop) hfamilyN.1) hNreal.le
    have hG : 0 ≤ G := by
      dsimp [G]
      have hs : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound W0)
      positivity
    have hpoly : 1 ≤ poly := by
      dsimp [poly, natPolylogEnvelope]
      have hmax : 1 ≤ max 1 (Real.log (N : ℝ)) := le_max_left _ _
      nlinarith [sq_nonneg (max 1 (Real.log (N : ℝ)) - 1)]
    have hlogBound' : L2 ≤ C * poly := by
      simpa [L2, JN, poly] using hlogBound
    have hGbound : G ≤ Cbranch * R := by
      have hscale := mul_le_mul_of_nonneg_right hfamilyN.2
        (div_nonneg (sq_nonneg Dop) (sq_nonneg (N : ℝ)))
      dsimp [G, R, JN] at hscale ⊢
      convert hscale using 1 <;> field_simp [ne_of_gt hNreal] <;> ring
    have hfirst : R ≤ poly * R := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hpoly hR
    have hsecond : R / 2 * L2 ≤ (C / 2) * poly * R := by
      have hscaled := mul_le_mul_of_nonneg_left hlogBound'
        (div_nonneg hR (by norm_num : (0 : ℝ) ≤ 2))
      calc
        R / 2 * L2 ≤ R / 2 * (C * poly) := hscaled
        _ = (C / 2) * poly * R := by ring
    have hthirdTerm : G / 6 * L2 ≤ (Cbranch * C / 6) * poly * R := by
      calc
        G / 6 * L2 ≤ (Cbranch * R) / 6 * L2 :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hGbound (by norm_num)) (sq_nonneg _)
        _ ≤ (Cbranch * R) / 6 * (C * poly) :=
          mul_le_mul_of_nonneg_left hlogBound' (by positivity)
        _ = (Cbranch * C / 6) * poly * R := by ring
    have hformula := hdisplay N hrun
    calc
      sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
          theorem_4_16_positiveDisplayedBound
            m n N Δ JN s Dop := hformula
      _ = R + R / 2 * L2 + G / 6 * L2 := by
        dsimp [theorem_4_16_positiveDisplayedBound,
          R, G, L2, JN]
        ring
      _ ≤ poly * R + (C / 2) * poly * R +
          (Cbranch * C / 6) * poly * R :=
        add_le_add (add_le_add hfirst hsecond) hthirdTerm
      _ = (1 + C / 2 + Cbranch * C / 6) *
          (natPolylogEnvelope 2 N *
            theorem_4_16_branchRateRealized m n JN Dop N hrateDom) := by
        simp [R, poly, theorem_4_16_branchRateRealized,
          realizedSourceQuot, sourceQuot]
        ring

set_option maxHeartbeats 800000 in
theorem theorem_4_16_otherwise_quadratic_bound_to_complexity
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N)
    (hquad : DomainAsymptoticUpperNatOn
      (fun N => theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
          Wstar W0 Δ s Dop N ∧
        theorem_4_16_otherwiseBranchRateDomain m n s Dop N)
      (fun N _hN => sourceObjectiveGapAt P (cfgForHorizon N) N hfinite)
      (fun N hN => natPolylogEnvelope 2 N *
        theorem_4_16_otherwiseBranchRateRealized m n s Dop N hN.2)
      (theoremScope "Theorem 4.16 otherwise branch rate" ["T"])) :
    TildeSourceHorizonObjectivePrecisionComplexityWithHorizonRate P hfinite cfgForHorizon
      (fun N => theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N)
      (fun _N ε => theorem_4_16_otherwiseComplexityRate m n s Dop ε)
      (theoremScope "Theorem 4.16 otherwise epsilon complexity" ["epsilon"]) := by
  let A : ℝ := s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3
  have hrunOne := hruns 1 (by norm_num [horizonDomain])
  have hrunOne' := hrunOne.2
  unfold theorem_4_16_otherwiseRunForHorizon at hrunOne'
  dsimp at hrunOne'
  rcases hrunOne' with ⟨_hOne, _hW0, ⟨hlogOne, _heta⟩, _hregime⟩
  have hs : 0 ≤ s := le_trans (norm_nonneg _) (hthird.bound W0)
  have hDop : 0 < Dop := hlogOne.2.1
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hA_ne : A ≠ 0 := by
    change s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 ≠ 0
    have hden := hlogOne.2.2.1.1
    change Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ≠ 0 at hden
    intro hzero
    apply hden
    calc
      Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) =
          s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 := by ring
      _ = 0 := hzero
  have hA : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA_ne)
  rcases hquad with ⟨C, N₀, hC, hscope, hquad⟩
  let E : ℝ := |Real.log 2| + |Real.log A| + 6
  have hE : 1 ≤ E := by dsimp [E]; nlinarith [abs_nonneg (Real.log 2), abs_nonneg (Real.log A)]
  let Z : ℝ := C * E ^ 2 + 1
  have hZ : 0 < Z := by dsimp [Z]; positivity
  let B₀ : ℝ := (N₀ : ℝ) + 1
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  let ε₀ : ℝ := min 1 (min (A / B₀ ^ 2) (Real.exp (-Z)))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min (by norm_num)
      (lt_min (div_pos hA (sq_pos_of_pos hB₀)) (Real.exp_pos _))
  refine ⟨4, 2, ε₀, by norm_num, hε₀, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
  · intro ε hε hεsmall
    have hεone : ε ≤ 1 := le_trans hεsmall (min_le_left _ _)
    have hεA : ε ≤ A / B₀ ^ 2 :=
      le_trans hεsmall (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεexp : ε ≤ Real.exp (-Z) :=
      le_trans hεsmall (le_trans (min_le_right _ _) (min_le_right _ _))
    let M : ℝ := max 1 (Real.log ε⁻¹)
    have hM : 1 ≤ M := by exact le_max_left _ _
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
    have hlogε_le_M : Real.log ε⁻¹ ≤ M := by exact le_max_right _ _
    have hexp_le_inv : Real.exp Z ≤ ε⁻¹ := by
      have hinv := (inv_le_inv₀ (Real.exp_pos (-Z)) hε).2 hεexp
      simpa [Real.exp_neg] using hinv
    have hZlog : Z ≤ Real.log ε⁻¹ :=
      (Real.le_log_iff_exp_le hεinv).2 hexp_le_inv
    have hCE : C * E ^ 2 ≤ M := by dsimp [Z] at hZlog; linarith
    have hMpow : M ≤ M ^ 6 := by
      simpa using (pow_le_pow_right₀ hM (by norm_num : (1 : ℕ) ≤ 6))
    have hCEpow : C * E ^ 2 ≤ M ^ 6 := le_trans hCE hMpow
    let rate : ℝ := theorem_4_16_otherwiseComplexityRate m n s Dop ε
    have hs_pos : 0 < s := by
      have hsne : s ≠ 0 := by
        intro hs0
        apply hA_ne
        simp [A, hs0]
      exact lt_of_le_of_ne hs (Ne.symm hsne)
    have hrankSqrt : 0 < Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) := by
      have hrne : Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ≠ 0 := by
        intro hr0
        apply hA_ne
        simp [A, hr0]
      exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hrne)
    have hrate : 0 < rate := by
      dsimp [rate, theorem_4_16_otherwiseComplexityRate]
      positivity
    have hrateSq : rate ^ 2 = A * ε⁻¹ := by
      dsimp [rate, theorem_4_16_otherwiseComplexityRate, A]
      rw [show
        (Real.sqrt s * Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) *
          Real.sqrt (Dop ^ 3) * Real.sqrt ε⁻¹) ^ 2 =
          (Real.sqrt s) ^ 2 * (Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) ^ 2) *
          (Real.sqrt (Dop ^ 3)) ^ 2 * (Real.sqrt ε⁻¹) ^ 2 by ring]
      rw [Real.sq_sqrt hs, Real.sq_sqrt (Real.sqrt_nonneg _),
        Real.sq_sqrt (by positivity : 0 ≤ Dop ^ 3),
        Real.sq_sqrt hεinv.le]
    have hB₀sq_le : B₀ ^ 2 ≤ rate ^ 2 := by
      rw [hrateSq]
      apply (le_div_iff₀ hε).2
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ((le_div_iff₀ (sq_pos_of_pos hB₀)).1 hεA)
    have hB₀rate : B₀ ≤ rate :=
      (sq_le_sq₀ hB₀.le hrate.le).1 hB₀sq_le
    let X : ℝ := M ^ 4 * rate
    have hX : 0 < X := mul_pos (pow_pos (lt_of_lt_of_le (by norm_num) hM) _) hrate
    have hB₀X : B₀ ≤ X := by
      have hpow : 1 ≤ M ^ 4 := one_le_pow₀ hM
      exact le_trans hB₀rate (by simpa [one_mul, X] using
        mul_le_mul_of_nonneg_right hpow hrate.le)
    let N : ℕ := Nat.ceil X
    have hNX : X ≤ (N : ℝ) := by simpa [N] using Nat.le_ceil X
    have hNpos : horizonDomain N := by
      dsimp [horizonDomain]
      have : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hX hNX
      exact_mod_cast this
    have hN₀ : N₀ ≤ N := by
      have hB₀N : B₀ ≤ (N : ℝ) := le_trans hB₀X hNX
      dsimp [B₀] at hB₀N
      exact_mod_cast (show (N₀ : ℝ) ≤ (N : ℝ) by linarith)
    have hNupper : (N : ℝ) ≤ 2 * X := by
      have hceil := Nat.ceil_lt_add_one hX.le
      have hBone : 1 ≤ B₀ := by dsimp [B₀]; linarith
      have hXone : 1 ≤ X := le_trans hBone hB₀X
      dsimp [N] at hceil ⊢
      linarith
    have hlogM : Real.log M ≤ M := by
      have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) hM)
      linarith
    have hlogRateEq :
        2 * Real.log rate = Real.log A + Real.log ε⁻¹ := by
      calc
        2 * Real.log rate = Real.log (rate ^ 2) := by rw [Real.log_pow]; norm_num
        _ = Real.log (A * ε⁻¹) := by rw [hrateSq]
        _ = Real.log A + Real.log ε⁻¹ :=
          Real.log_mul (ne_of_gt hA) (ne_of_gt hεinv)
    have hlogRate : Real.log rate ≤ (|Real.log A| + M) / 2 := by
      have hlogA : Real.log A ≤ |Real.log A| := le_abs_self _
      linarith
    have hlogN : Real.log (N : ℝ) ≤ E * M := by
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
      have hlogMono := Real.strictMonoOn_log.monotoneOn
        hNreal (mul_pos (by norm_num) hX) hNupper
      have htwoX :
          Real.log (2 * X) = Real.log 2 + 4 * Real.log M + Real.log rate := by
        dsimp [X]
        rw [Real.log_mul (by norm_num) (mul_ne_zero (pow_ne_zero 4 (ne_of_gt
          (lt_of_lt_of_le (by norm_num) hM))) (ne_of_gt hrate)),
          Real.log_mul (pow_ne_zero 4 (ne_of_gt (lt_of_lt_of_le (by norm_num) hM)))
            (ne_of_gt hrate), Real.log_pow]
        ring
      rw [htwoX] at hlogMono
      have hlogTwo : Real.log 2 ≤ |Real.log 2| := le_abs_self _
      dsimp [E]
      nlinarith [abs_nonneg (Real.log A), abs_nonneg (Real.log 2)]
    have hEM : 1 ≤ E * M := le_trans hM (by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hE (le_trans (by norm_num) hM))
    have hpolyN : natPolylogEnvelope 2 N ≤ E ^ 2 * M ^ 2 := by
      dsimp [natPolylogEnvelope]
      have hmax : max 1 (Real.log (N : ℝ)) ≤ E * M :=
        max_le hEM hlogN
      have hsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hmax
      nlinarith
    have hrun := hruns N hNpos
    have hdom : theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
          Wstar W0 Δ s Dop N ∧
        theorem_4_16_otherwiseBranchRateDomain m n s Dop N :=
      ⟨hrun, hNpos⟩
    have hgap := hquad N hdom hN₀
    have hrateN :
        theorem_4_16_otherwiseBranchRateRealized m n s Dop N hdom.2 =
          A / (N : ℝ) ^ 2 := by
      simp [theorem_4_16_otherwiseBranchRateRealized, realizedSourceQuot,
        sourceQuot, realizedSourceSqrt, sourceSqrt, A]
    change sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
      C * (natPolylogEnvelope 2 N *
        theorem_4_16_otherwiseBranchRateRealized m n s Dop N hdom.2) at hgap
    rw [hrateN] at hgap
    have hNden : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hNpos)
    have hXden : 0 < X ^ 2 := sq_pos_of_pos hX
    have hdiv : A / (N : ℝ) ^ 2 ≤ A / X ^ 2 := by
      have hNsq : X ^ 2 ≤ (N : ℝ) ^ 2 :=
        pow_le_pow_left₀ hX.le hNX 2
      exact div_le_div_of_nonneg_left hA.le hXden hNsq
    have hboundGap :
        sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
          C * (E ^ 2 * M ^ 2) * (A / X ^ 2) := by
      calc
        sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
            C * (natPolylogEnvelope 2 N * (A / (N : ℝ) ^ 2)) := hgap
        _ ≤ C * ((E ^ 2 * M ^ 2) * (A / (N : ℝ) ^ 2)) := by
          gcongr
        _ ≤ C * ((E ^ 2 * M ^ 2) * (A / X ^ 2)) := by
          gcongr
        _ = C * (E ^ 2 * M ^ 2) * (A / X ^ 2) := by ring
    have hidentity :
        C * (E ^ 2 * M ^ 2) * (A / X ^ 2) =
          (C * E ^ 2 / M ^ 6) * ε := by
      have hXsq : X ^ 2 = M ^ 8 * rate ^ 2 := by dsimp [X]; ring
      rw [hXsq, hrateSq]
      field_simp [ne_of_gt hA, ne_of_gt hε, ne_of_gt hMpos]
    have hcoef : C * E ^ 2 / M ^ 6 ≤ 1 :=
      (div_le_one (pow_pos hMpos 6)).2 hCEpow
    refine ⟨N, hrun, ?_, ?_⟩
    · rw [hidentity] at hboundGap
      exact le_trans hboundGap (by
        have := mul_le_mul_of_nonneg_right hcoef hε.le
        simpa [one_mul] using this)
    · calc
        (N : ℝ) ≤ 2 * X := hNupper
        _ = 2 * (accuracyPolylogEnvelope 4 ε *
            theorem_4_16_otherwiseComplexityRate m n s Dop ε) := by
          simp [X, M, rate, accuracyPolylogEnvelope]

theorem theorem_4_14_finite_sum_descent
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    {T : ℕ} {s η : ℝ}
    (hthird : ThirdDerivativeBounded P s)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (hη_pos : 0 < η) :
    η * Finset.sum (Finset.range T)
        (fun t => nuclearNorm (P.grad ((deterministicMuonState P cfg t).W))) ≤
      P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W) +
        η ^ 2 * Finset.sum (Finset.range T)
          (fun t => hessianDirectionalTerm P cfg t / 2) +
        (T : ℝ) * (s * η ^ 3 *
          Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) := by
  have hpoint :
      ∀ t ∈ Finset.range T,
        P.f ((deterministicMuonState P cfg (t + 1)).W) -
            P.f ((deterministicMuonState P cfg t).W) ≤
          -η * nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) +
            η ^ 2 * hessianDirectionalTerm P cfg t / 2 +
            s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
    intro t ht
    exact equation_15_third_order_descent_from_assumption
      (P := P) (cfg := cfg) ht hthird hη hη_pos
  have hsum := Finset.sum_le_sum hpoint
  have htelescope :
      Finset.sum (Finset.range T)
          (fun t =>
            P.f ((deterministicMuonState P cfg (t + 1)).W) -
              P.f ((deterministicMuonState P cfg t).W)) =
        P.f ((deterministicMuonState P cfg T).W) - P.f cfg.W0 := by
    simpa [deterministicMuonState, deterministicMuonBaseState] using
      (Finset.sum_range_sub
        (fun t => P.f ((deterministicMuonState P cfg t).W)) T)
  have hquad :
      Finset.sum (Finset.range T)
          (fun t => η ^ 2 * hessianDirectionalTerm P cfg t / 2) =
        η ^ 2 * Finset.sum (Finset.range T)
          (fun t => hessianDirectionalTerm P cfg t / 2) := by
    calc
      Finset.sum (Finset.range T)
          (fun t => η ^ 2 * hessianDirectionalTerm P cfg t / 2) =
          Finset.sum (Finset.range T)
            (fun t => η ^ 2 * (hessianDirectionalTerm P cfg t / 2)) := by
              apply Finset.sum_congr rfl
              intro t ht
              ring
      _ = η ^ 2 * Finset.sum (Finset.range T)
          (fun t => hessianDirectionalTerm P cfg t / 2) := by
            rw [Finset.mul_sum]
  have hcubic :
      Finset.sum (Finset.range T)
          (fun _t => s * η ^ 3 *
            Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) =
        (T : ℝ) * (s * η ^ 3 *
          Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) := by
    simp [Finset.sum_const, Finset.card_range]
  rw [htelescope, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hquad, hcubic] at hsum
  nlinarith [hsum]

theorem theorem_4_14_source_average_bound_at_horizon
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η : ℝ)
    (hthird : ThirdDerivativeBounded P s)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (hdom : theorem_4_14_rhsDomain P cfg T
      (hessianDirectionalAverage P cfg T) s η) :
    deterministicAverageNuclearGradient P cfg T ≤
      theorem_4_14_rhs P cfg T (hessianDirectionalAverage P cfg T) s η hdom := by
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast hdom.1
  have hη_pos : 0 < η := hdom.2.1
  have hsum :=
    theorem_4_14_finite_sum_descent P cfg hthird hη hη_pos
  have hden_pos : 0 < (T : ℝ) * η := mul_pos hT_pos hη_pos
  have hhalf :
      Finset.sum (Finset.range T)
          (fun t => hessianDirectionalTerm P cfg t / 2) =
        (Finset.sum (Finset.range T)
          (fun t => hessianDirectionalTerm P cfg t)) / 2 := by
    calc
      Finset.sum (Finset.range T)
            (fun t => hessianDirectionalTerm P cfg t / 2) =
          Finset.sum (Finset.range T)
            (fun t => (1 / 2 : ℝ) * hessianDirectionalTerm P cfg t) := by
              apply Finset.sum_congr rfl
              intro t ht
              ring
      _ = (1 / 2 : ℝ) * Finset.sum (Finset.range T)
            (fun t => hessianDirectionalTerm P cfg t) := by
              rw [Finset.mul_sum]
      _ = (Finset.sum (Finset.range T)
            (fun t => hessianDirectionalTerm P cfg t)) / 2 := by
              ring
  have hquot :
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T)
          (fun t => nuclearNorm
            (P.grad ((deterministicMuonState P cfg t).W))) ≤
        (P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W)) /
            ((T : ℝ) * η) +
          η * (((T : ℝ)⁻¹) * Finset.sum (Finset.range T)
            (fun t => hessianDirectionalTerm P cfg t)) / 2 +
          s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
    calc
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T)
            (fun t => nuclearNorm
              (P.grad ((deterministicMuonState P cfg t).W))) =
          (η * Finset.sum (Finset.range T)
            (fun t => nuclearNorm
              (P.grad ((deterministicMuonState P cfg t).W)))) /
            ((T : ℝ) * η) := by
              field_simp [ne_of_gt hT_pos, ne_of_gt hη_pos]
      _ ≤ (P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W) +
            η ^ 2 * Finset.sum (Finset.range T)
              (fun t => hessianDirectionalTerm P cfg t / 2) +
            (T : ℝ) * (s * η ^ 3 *
              Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6)) /
            ((T : ℝ) * η) := by
              exact div_le_div_of_nonneg_right hsum (le_of_lt hden_pos)
      _ = (P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W)) /
            ((T : ℝ) * η) +
          η * (((T : ℝ)⁻¹) * Finset.sum (Finset.range T)
            (fun t => hessianDirectionalTerm P cfg t)) / 2 +
          s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
              rw [hhalf]
              field_simp [ne_of_gt hT_pos, ne_of_gt hη_pos]
  rw [theorem_4_14_rhs_eq_sourceRhs P cfg T
    (hessianDirectionalAverage P cfg T) s η hdom]
  simpa [deterministicAverageNuclearGradient, theorem_4_14_sourceRhs,
    hessianDirectionalAverage] using hquot

theorem theorem_4_14_positive_pointwise_source_average_bound_at_horizon
    {m n : ℕ} (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (J s Δ : ℝ) (N : ℕ)
    (hthird : ThirdDerivativeBounded P s)
    (hrun : theorem_4_14_positivePointwiseRunForHorizon
      P cfgForHorizon W0 J s Δ N) :
    ∃ hdom : theorem_4_14_rhsDomain P (cfgForHorizon N) N
        (hessianDirectionalAverage P (cfgForHorizon N) N) s
        (theorem_4_14_positiveBranchEtaRate J Δ N),
      deterministicAverageNuclearGradient P (cfgForHorizon N) N ≤
        theorem_4_14_rhs P (cfgForHorizon N) N
          (hessianDirectionalAverage P (cfgForHorizon N) N) s
          (theorem_4_14_positiveBranchEtaRate J Δ N) hdom := by
  unfold theorem_4_14_positivePointwiseRunForHorizon at hrun
  dsimp at hrun
  rcases hrun with
    ⟨_hN, _hW0, _hAvg, _hBranch, hRhs, hSchedule⟩
  refine ⟨hRhs, ?_⟩
  exact theorem_4_14_source_average_bound_at_horizon
    P (cfgForHorizon N) N s
      (theorem_4_14_positiveBranchEtaRate J Δ N) hthird hSchedule hRhs

theorem theorem_4_14_otherwise_source_average_bound_at_accuracy_horizon
    {m n : ℕ} (P : Objective m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ ε C : ℝ) (N : ℕ)
    (hthird : ThirdDerivativeBounded P s)
    (hrun : theorem_4_14_otherwiseSourceRunForAccuracyHorizon
      P cfgForAccuracyHorizon W0 s Δ ε C N) :
    ∃ hetaDom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ N,
    ∃ hdom : theorem_4_14_rhsDomain P (cfgForAccuracyHorizon ε N) N
        (hessianDirectionalAverage P (cfgForAccuracyHorizon ε N) N) s
        (theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom),
      deterministicAverageNuclearGradient P (cfgForAccuracyHorizon ε N) N ≤
        theorem_4_14_rhs P (cfgForAccuracyHorizon ε N) N
          (hessianDirectionalAverage P (cfgForAccuracyHorizon ε N) N) s
          (theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom) hdom := by
  unfold theorem_4_14_otherwiseSourceRunForAccuracyHorizon at hrun
  unfold theorem_4_14_otherwiseRunForAccuracyHorizon at hrun
  dsimp at hrun
  rcases hrun with
    ⟨_hN, _hW0, ⟨hetaDom, hSchedule⟩, _hBranchDomain, _hRegime⟩
  have hsource :=
    theorem_4_14_otherwiseBranchEta_sourceDomain hetaDom
  obtain ⟨hdom, _⟩ :=
    theorem_4_14_downstream_phase2_boundary_of_sourceDomain
      P (cfgForAccuracyHorizon ε N) N s
      (theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom)
      hsource hthird hSchedule
  refine ⟨hetaDom, hdom, ?_⟩
  exact theorem_4_14_source_average_bound_at_horizon
    P (cfgForAccuracyHorizon ε N) N s
      (theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom)
      hthird hSchedule hdom

theorem theorem_4_14_source_average_bound_by_initial_gap
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (W0 : Mat m n) (T : ℕ) (s η Δ J : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hW0 : cfg.W0 = W0)
    (hΔ : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hthird : ThirdDerivativeBounded P s)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (hJ : hessianDirectionalAverage P cfg T ≤ J)
    (hdom : theorem_4_14_rhsDomain P cfg T
      (hessianDirectionalAverage P cfg T) s η) :
    deterministicAverageNuclearGradient P cfg T ≤
      Δ / ((T : ℝ) * η) + η * J / 2 +
        s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
  have hbound :=
    theorem_4_14_source_average_bound_at_horizon P cfg T s η hthird hη hdom
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast hdom.1
  have hη_pos : 0 < η := hdom.2.1
  have hterminal : P.fStar ≤ P.f ((deterministicMuonState P cfg T).W) := by
    simpa [Objective.fStar] using
      (csInf_le hfinite
        (show P.f ((deterministicMuonState P cfg T).W) ∈ Set.range P.f from
          ⟨(deterministicMuonState P cfg T).W, rfl⟩))
  have hgap0 :
      P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W) ≤
        sourceObjectiveInitialGap P W0 hfinite := by
    simp only [sourceObjectiveInitialGap, Objective.sourceFStar, hW0]
    linarith
  have hgap :
      P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W) ≤ Δ := by
    simpa [hΔ] using hgap0
  have hquot :
      (P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W)) /
          ((T : ℝ) * η) ≤ Δ / ((T : ℝ) * η) :=
    div_le_div_of_nonneg_right hgap
      (le_of_lt (mul_pos hT_pos hη_pos))
  rw [theorem_4_14_rhs_eq_sourceRhs P cfg T
    (hessianDirectionalAverage P cfg T) s η hdom] at hbound
  have hJmul :
      η * hessianDirectionalAverage P cfg T / 2 ≤ η * J / 2 := by
    nlinarith
  dsimp [theorem_4_14_sourceRhs] at hbound
  nlinarith

theorem objective_terminal_lower_bound
    {m n : ℕ} (P : Objective m n) (hfinite : P.HasFiniteInfimum)
    (W : Mat m n) : P.fStar ≤ P.f W := by
  simpa [Objective.fStar] using
    (csInf_le hfinite (show P.f W ∈ Set.range P.f from ⟨W, rfl⟩))

theorem theorem_4_14_positive_rate_bound_at_horizon
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (s Δ J : ℝ) (N : ℕ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hs : 0 ≤ s)
    (hΔ : sourceObjectiveInitialGap P cfg.W0 hfinite = Δ)
    (hrun : theorem_4_14_positivePointwiseRunForHorizon
      P cfgForHorizon cfg.W0 J s Δ N) :
    ∃ hdom : theorem_4_14_branchRateDomain m n N J s Δ,
      deterministicAverageNuclearGradient P (cfgForHorizon N) N ≤
        2 * theorem_4_14_branchRate P (cfgForHorizon N) J s Δ N hdom := by
  unfold theorem_4_14_positivePointwiseRunForHorizon at hrun
  dsimp at hrun
  rcases hrun with
    ⟨hN, hW0, hAvg, hBranch, hRhs, hSchedule⟩
  let ηN := theorem_4_14_positiveBranchEtaRate J Δ N
  have hbound :=
    theorem_4_14_source_average_bound_by_initial_gap
      P (cfgForHorizon N) cfg.W0 N s ηN Δ J hfinite hW0 hΔ hthird
      hSchedule hAvg hRhs
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hηpos : 0 < ηN := hRhs.2.1
  have hΔnonneg : 0 ≤ Δ := by
    rw [← hΔ]
    exact sub_nonneg.mpr (objective_terminal_lower_bound P hfinite cfg.W0)
  have hηquot_pos :
      0 < Δ / (J * (N : ℝ)) := by
    simpa [ηN, theorem_4_14_positiveBranchEtaRate, sourceQuot] using
      (Real.sqrt_pos.1 hηpos)
  have hΔpos : 0 < Δ := by
    by_contra hΔnot
    have hΔzero : Δ = 0 := le_antisymm (le_of_not_gt hΔnot) hΔnonneg
    simp [hΔzero] at hηquot_pos
  have hJmul_pos : 0 < J * (N : ℝ) := by
    rcases (div_pos_iff.mp hηquot_pos) with h | h
    · exact h.2
    · linarith
  have hJpos : 0 < J := by
    nlinarith [hJmul_pos, hNpos]
  have hηsq :
      ηN ^ 2 = Δ / (J * (N : ℝ)) := by
    dsimp [ηN, theorem_4_14_positiveBranchEtaRate, sourceQuot]
    exact Real.sq_sqrt (le_of_lt hηquot_pos)
  have hroot_pos : 0 < (J * Δ) / (N : ℝ) :=
    div_pos (mul_pos hJpos hΔpos) hNpos
  have hroot_sq :
      (Real.sqrt ((J * Δ) / (N : ℝ))) ^ 2 =
        (J * Δ) / (N : ℝ) :=
    Real.sq_sqrt (le_of_lt hroot_pos)
  have hηJ :
      ηN * J = Real.sqrt ((J * Δ) / (N : ℝ)) := by
    have hηJ_nonneg : 0 ≤ ηN * J := le_of_lt (mul_pos hηpos hJpos)
    have hηJ_sq :
        (ηN * J) ^ 2 = (J * Δ) / (N : ℝ) := by
      rw [show (ηN * J) ^ 2 = ηN ^ 2 * J ^ 2 by ring, hηsq]
      field_simp [ne_of_gt hJpos, ne_of_gt hNpos]
    have hsq :
        (ηN * J) ^ 2 =
          (Real.sqrt ((J * Δ) / (N : ℝ))) ^ 2 :=
      hηJ_sq.trans hroot_sq.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
    · exact h
    · have hroot_nonneg : 0 ≤ Real.sqrt ((J * Δ) / (N : ℝ)) :=
        Real.sqrt_nonneg _
      nlinarith
  have hfirst :
      Δ / ((N : ℝ) * ηN) = Real.sqrt ((J * Δ) / (N : ℝ)) := by
    have hleft_pos : 0 < Δ / ((N : ℝ) * ηN) :=
      div_pos hΔpos (mul_pos hNpos hηpos)
    have hleft_sq :
        (Δ / ((N : ℝ) * ηN)) ^ 2 = (J * Δ) / (N : ℝ) := by
      rw [div_pow, mul_pow, hηsq]
      field_simp [ne_of_gt hJpos, ne_of_gt hNpos, ne_of_gt hηpos]
    have hsq :
        (Δ / ((N : ℝ) * ηN)) ^ 2 =
          (Real.sqrt ((J * Δ) / (N : ℝ))) ^ 2 :=
      hleft_sq.trans hroot_sq.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
    · exact h
    · have hroot_nonneg : 0 ≤ Real.sqrt ((J * Δ) / (N : ℝ)) :=
        Real.sqrt_nonneg _
      nlinarith
  have hsecond_nonneg :
      0 ≤ s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ /
        (J * (N : ℝ)) := by
    have hroot_rank : 0 ≤ Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) :=
      Real.sqrt_nonneg _
    have hnum :
        0 ≤ s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ :=
      mul_nonneg (mul_nonneg hs hroot_rank) (le_of_lt hΔpos)
    exact div_nonneg hnum (le_of_lt hJmul_pos)
  refine ⟨hBranch, ?_⟩
  rw [theorem_4_14_branchRate]
  simp only [realizedSourceSqrtQuot, realizedSourceSqrt, realizedSourceQuot,
    sourceSqrt, sourceQuot] at ⊢
  rw [hfirst] at hbound
  rw [hηJ] at hbound
  have hthird_eq :
      s * ηN ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 =
        (s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ /
          (J * (N : ℝ))) / 6 := by
    rw [hηsq]
    field_simp [ne_of_gt hJpos, ne_of_gt hNpos]
  have hthird_le :
      s * ηN ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 ≤
        s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ /
          (J * (N : ℝ)) := by
    rw [hthird_eq]
    nlinarith
  have hroot_nonneg : 0 ≤ Real.sqrt ((J * Δ) / (N : ℝ)) :=
    Real.sqrt_nonneg _
  nlinarith [hbound, hthird_le, hsecond_nonneg]

theorem theorem_4_14_positive_branch_rate_from_source_assumptions
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n)
    (s Δ J : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hΔ : sourceObjectiveInitialGap P cfg.W0 hfinite = Δ)
    (hpointwise : theorem_4_14_positiveBranchPointwisePremise m n J s)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_14_positivePointwiseRunForHorizon
        P cfgForHorizon cfg.W0 J s Δ N) :
    DomainAsymptoticUpperNatOn
      (fun N => theorem_4_14_branchRateDomain m n N J s Δ)
      (fun N _hN => deterministicAverageNuclearGradient P (cfgForHorizon N) N)
      (fun N hN => theorem_4_14_branchRate P (cfgForHorizon N) J s Δ N hN)
      (theoremScope "Theorem 4.14 positive-J branch rate" ["T"]) := by
  rcases hpointwise with ⟨ε₀, hε₀, hpointwise⟩
  have hcond :=
    hpointwise ε₀ hε₀ (le_refl ε₀)
  rcases hcond with ⟨_hε₀, hsqrt, _hrank, _hc⟩
  have hs : 0 ≤ s := by
    dsimp [sourceSqrtDomain] at hsqrt
    nlinarith
  refine ⟨2, 1, by norm_num, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope]
  · intro N hN hNlarge
    have hrun := hruns N hN.1
    obtain ⟨_hdom, hbound⟩ :=
      theorem_4_14_positive_rate_bound_at_horizon
        P cfg cfgForHorizon s Δ J N hfinite hthird hs hΔ hrun
    simpa using hbound

/- The two displayed Appendix B.3 rate terms are each at most one quarter of
   the requested accuracy once the horizon dominates the stated quadratic
   complexity scale.  The two hypotheses on `H` are the horizon-independent
   budgets for the square-root and third-order terms, respectively. -/
theorem theorem_4_14_positive_source_rate_le_accuracy_at_complexity_horizon
    (m n : ℕ) (J s Δ H ε : ℝ) (N : ℕ)
    (hJ : 0 < J) (hΔ : 0 < Δ) (hs : 0 ≤ s)
    (hε : epsilonDomain ε) (hεone : ε ≤ 1) (hN : horizonDomain N)
    (hHfirst : (16 : ℝ) ≤ H)
    (hHsecond :
      (4 : ℝ) * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ≤
        H * J ^ 2)
    (hNlarge :
      H * theorem_4_14_complexityRate m n J Δ ε ≤ (N : ℝ)) :
    2 * theorem_4_14_sourceBranchRate m n J s Δ N ≤ ε := by
  let q : ℝ := Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)
  let base : ℝ := J * Δ
  let A : ℝ := Real.sqrt (base / (N : ℝ))
  let E : ℝ := s * q * Δ / (J * (N : ℝ))
  have hbase_pos : 0 < base := by dsimp [base]; positivity
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hεsq_le : ε ^ 2 ≤ ε := by
    have hp : 0 ≤ ε * (1 - ε) :=
      mul_nonneg hε.le (sub_nonneg.mpr hεone)
    nlinarith
  have hbudget : H * base ≤ (N : ℝ) * ε ^ 2 := by
    have hlarge' : H * base / ε ^ 2 ≤ (N : ℝ) := by
      convert hNlarge using 1 <;>
        simp [theorem_4_14_complexityRate, base, div_eq_mul_inv,
          inv_pow] <;> ring
    exact (div_le_iff₀ (pow_pos hε 2)).mp hlarge'
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hE_nonneg : 0 ≤ E := by dsimp [E, q]; positivity
  have ht_nonneg : 0 ≤ ε / 4 := div_nonneg hε.le (by norm_num)
  have hA_sq : A ^ 2 = base / (N : ℝ) := by
    dsimp [A]
    exact Real.sq_sqrt (div_nonneg hbase_pos.le hNreal.le)
  have hA_cross : (16 : ℝ) * base ≤ (N : ℝ) * ε ^ 2 := by
    exact le_trans (mul_le_mul_of_nonneg_right hHfirst hbase_pos.le) hbudget
  have hA_ratio : base / (N : ℝ) ≤ (ε / 4) ^ 2 := by
    apply (div_le_iff₀ hNreal).2
    have hscaled : base ≤ ((N : ℝ) * ε ^ 2) / 16 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2 (by
        simpa [mul_comm] using hA_cross)
    calc
      base ≤ ((N : ℝ) * ε ^ 2) / 16 := hscaled
      _ = (ε / 4) ^ 2 * (N : ℝ) := by ring
  have hA : A ≤ ε / 4 := by
    exact (sq_le_sq₀ hA_nonneg ht_nonneg).mp (by
      simpa [hA_sq] using hA_ratio)
  have hE_budget :
      (4 : ℝ) * (s * q * Δ) ≤ J * (N : ℝ) * ε ^ 2 := by
    have hcurvature :
        (4 : ℝ) * (s * q * Δ) ≤ H * base * J := by
      calc
        (4 : ℝ) * (s * q * Δ) = ((4 : ℝ) * s * q) * Δ := by ring
        _ ≤ (H * J ^ 2) * Δ :=
          mul_le_mul_of_nonneg_right (by simpa [q] using hHsecond) hΔ.le
        _ = H * base * J := by dsimp [base]; ring
    have hmul := mul_le_mul_of_nonneg_right hbudget hJ.le
    exact le_trans hcurvature (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  have hE_sq : E ≤ ε ^ 2 / 4 := by
    dsimp [E]
    apply (div_le_iff₀ (mul_pos hJ hNreal)).2
    have hscaled : s * q * Δ ≤ (J * (N : ℝ) * ε ^ 2) / 4 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by
        simpa [mul_comm] using hE_budget)
    calc
      s * q * Δ ≤ (J * (N : ℝ) * ε ^ 2) / 4 := hscaled
      _ = ε ^ 2 / 4 * (J * (N : ℝ)) := by ring
  have hE : E ≤ ε / 4 :=
    le_trans hE_sq (by nlinarith)
  change 2 * (A + E) ≤ ε
  linarith

theorem theorem_4_14_positive_complexity_witness
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n)
    (s Δ J : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hΔ : sourceObjectiveInitialGap P cfg.W0 hfinite = Δ)
    (hpointwise : theorem_4_14_positiveBranchPointwisePremise m n J s)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_14_positivePointwiseRunForHorizon
        P cfgForHorizon cfg.W0 J s Δ N) :
    HorizonNuclearStationarityComplexityWithHorizonRate
      (fun N => deterministicAverageNuclearGradient P (cfgForHorizon N) N)
      (fun N => theorem_4_14_positivePointwiseRunForHorizon
        P cfgForHorizon cfg.W0 J s Δ N)
      (fun _N ε => theorem_4_14_complexityRate m n J Δ ε)
      (theoremScope "Theorem 4.14 positive-J epsilon complexity" ["epsilon"]) := by
  let q : ℝ := Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)
  rcases hpointwise with ⟨εpoint, hεpoint, hpointwiseAt⟩
  rcases hpointwiseAt εpoint hεpoint le_rfl with
    ⟨_hεpoint', hsqrt, _hrank, _c, _hc, _hcJ⟩
  have hs : 0 ≤ s := by
    dsimp [sourceSqrtDomain] at hsqrt
    nlinarith
  have hrunOne := hruns 1 (by norm_num [horizonDomain])
  have hrunOne' := hrunOne
  unfold theorem_4_14_positivePointwiseRunForHorizon at hrunOne'
  dsimp at hrunOne'
  rcases hrunOne' with
    ⟨_hOne, _hW0One, _hAvgOne, _hBranchOne, hRhsOne, _hScheduleOne⟩
  have hgap_nonneg :
      0 ≤ sourceObjectiveInitialGap P cfg.W0 hfinite := by
    unfold sourceObjectiveInitialGap Objective.sourceFStar
    have hlower : P.fStar ≤ P.f cfg.W0 := by
      simpa [Objective.fStar] using
        (csInf_le hfinite
          (show P.f cfg.W0 ∈ Set.range P.f from ⟨cfg.W0, rfl⟩))
    linarith
  have hΔ_nonneg : 0 ≤ Δ := by simpa [hΔ] using hgap_nonneg
  have hηquot_pos : 0 < Δ / (J * (1 : ℝ)) := by
    simpa [theorem_4_14_positiveBranchEtaRate, sourceQuot] using
      (Real.sqrt_pos.1 hRhsOne.2.1)
  have hΔpos : 0 < Δ := by
    by_contra hΔnot
    have hΔzero : Δ = 0 := le_antisymm (le_of_not_gt hΔnot) hΔ_nonneg
    simp [hΔzero] at hηquot_pos
  have hJmul_pos : 0 < J * (1 : ℝ) := by
    rcases (div_pos_iff.mp hηquot_pos) with h | h
    · exact h.2
    · linarith
  have hJpos : 0 < J := by simpa using hJmul_pos
  let H : ℝ := max 16 ((4 : ℝ) * s * q / J ^ 2)
  have hHfirst : (16 : ℝ) ≤ H := by
    dsimp [H]
    exact le_max_left _ _
  have hHsecondRaw : (4 : ℝ) * s * q / J ^ 2 ≤ H := by
    dsimp [H]
    exact le_max_right _ _
  have hHsecond :
      (4 : ℝ) * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ≤
        H * J ^ 2 := by
    have hclear := (div_le_iff₀ (sq_pos_of_pos hJpos)).mp hHsecondRaw
    simpa [q] using hclear
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hHfirst
  let base : ℝ := J * Δ
  have hbase_pos : 0 < base := by dsimp [base]; positivity
  unfold HorizonNuclearStationarityComplexityWithHorizonRate
  refine ⟨2 * H, min 1 (H * base), by positivity,
    lt_min (by norm_num) (mul_pos hHpos hbase_pos), ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope, hHpos]
  · intro ε hε hεsmall
    have hεone : ε ≤ 1 := le_trans hεsmall (min_le_left _ _)
    have hεbase : ε ≤ H * base := le_trans hεsmall (min_le_right _ _)
    have hεsq_le : ε ^ 2 ≤ ε := by
      have hp : 0 ≤ ε * (1 - ε) :=
        mul_nonneg hε.le (sub_nonneg.mpr hεone)
      nlinarith
    let rate : ℝ := theorem_4_14_complexityRate m n J Δ ε
    have hrate_pos : 0 < rate := by
      dsimp [rate, theorem_4_14_complexityRate]
      exact mul_pos (mul_pos hJpos hΔpos) (sq_pos_of_pos (inv_pos.mpr hε))
    have hHrate_one : 1 ≤ H * rate := by
      have hbase_le : ε ^ 2 ≤ H * base := le_trans hεsq_le hεbase
      have hdiv : 1 ≤ H * base / ε ^ 2 :=
        (le_div_iff₀ (pow_pos hε 2)).2 (by simpa using hbase_le)
      have heq : H * rate = H * base / ε ^ 2 := by
        dsimp [rate, base, theorem_4_14_complexityRate]
        field_simp [ne_of_gt hε]
      simpa [heq] using hdiv
    let N : ℕ := max 1 (Nat.ceil (H * rate))
    have hN : horizonDomain N := by
      dsimp [horizonDomain, N]
      omega
    have hNlower : H * rate ≤ (N : ℝ) := by
      have hceil : H * rate ≤ (Nat.ceil (H * rate) : ℕ) := Nat.le_ceil _
      have hceilmax : Nat.ceil (H * rate) ≤ N := by
        dsimp [N]
        exact le_max_right _ _
      exact le_trans hceil (by exact_mod_cast hceilmax)
    have hceilOne : 1 ≤ Nat.ceil (H * rate) := by
      have hceil := Nat.le_ceil (H * rate)
      exact_mod_cast le_trans hHrate_one hceil
    have hNeq : N = Nat.ceil (H * rate) := by
      dsimp [N]
      exact max_eq_right hceilOne
    have hNupper : (N : ℝ) ≤ 2 * (H * rate) := by
      rw [hNeq]
      have hceilLt := Nat.ceil_lt_add_one (mul_nonneg hHpos.le hrate_pos.le)
      exact le_trans hceilLt.le (by linarith)
    have hrun := hruns N hN
    obtain ⟨hdom, havgBound⟩ :=
      theorem_4_14_positive_rate_bound_at_horizon
        P cfg cfgForHorizon s Δ J N hfinite hthird hs hΔ hrun
    have hscalar :=
      theorem_4_14_positive_source_rate_le_accuracy_at_complexity_horizon
        m n J s Δ H ε N hJpos hΔpos hs hε hεone hN
        hHfirst hHsecond (by simpa [rate] using hNlower)
    have hbranchSource
        (hdom' : theorem_4_14_branchRateDomain m n N J s Δ) :
        theorem_4_14_branchRate P (cfgForHorizon N) J s Δ N hdom' =
          theorem_4_14_sourceBranchRate m n J s Δ N := by
      rcases hdom' with ⟨_horizon, _hfirst, _hsecond⟩
      simp [theorem_4_14_branchRate, theorem_4_14_sourceBranchRate,
        realizedSourceSqrtQuot, realizedSourceSqrt, realizedSourceQuot,
        sourceSqrt, sourceQuot]
    rw [hbranchSource hdom] at havgBound
    refine ⟨N, hrun, le_trans havgBound hscalar, ?_⟩
    simpa [rate, mul_assoc] using hNupper

theorem theorem_4_14_positive_branch_rate_and_complexity_of_source_assumptions
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n)
    (s Δ J : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hΔ : sourceObjectiveInitialGap P cfg.W0 hfinite = Δ)
    (hpointwise : theorem_4_14_positiveBranchPointwisePremise m n J s)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (hruns : ∀ N : ℕ, horizonDomain N →
      theorem_4_14_positivePointwiseRunForHorizon
        P cfgForHorizon cfg.W0 J s Δ N) :
    theorem_4_14_positive_branch_rate_and_complexity
      P cfg s Δ J cfgForHorizon := by
  constructor
  · exact theorem_4_14_positive_branch_rate_from_source_assumptions
      P cfg s Δ J hfinite hthird hΔ hpointwise cfgForHorizon hruns
  · constructor
    · exact theorem_4_14_positive_complexity_witness
        P cfg s Δ J hfinite hthird hΔ hpointwise cfgForHorizon hruns
    · simpa [deterministicAverageNuclearGradient] using
        (generatedNuclearStationarityTransfer_of_finite_average
          P
          (fun N => theorem_4_14_positivePointwiseRunForHorizon
            P cfgForHorizon cfg.W0 J s Δ N)
          (fun _N hN => hN.1)
          (fun N _hN t => (deterministicMuonState P (cfgForHorizon N) t).W))

theorem theorem_4_14_otherwise_schedule_rhs_le_branch_rate
    {m n : ℕ} (s Δ ε C : ℝ) (N : ℕ)
    (hetaDom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ N)
    (hbranch : theorem_4_14_otherwiseBranchRateDomain m n s Δ N)
    (hselected : theorem_4_14_otherwise_selected_horizon_relation
      m n s Δ ε N)
    (hε : epsilonDomain ε)
    (hC : 0 < C) :
    let η := theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom
    let R := theorem_4_14_otherwiseBranchRate m n s Δ N hbranch
    Δ / ((N : ℝ) * η) +
          η * (C * (Real.sqrt (s * ε) *
            Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)))) / 2 +
          s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 ≤
        ((7 : ℝ) / 6 + C / 2) * R := by
  let r : ℝ := matrixRankBound m n
  let q : ℝ := Real.sqrt (r ^ 3)
  let η : ℝ := theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom
  let R : ℝ := theorem_4_14_otherwiseBranchRate m n s Δ N hbranch
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast hbranch.1
  have hΔpos : 0 < Δ := by
    simpa [sourceRpowDomain] using hbranch.2.1
  have hspos : 0 < s := by
    simpa [sourceRpowDomain] using hbranch.2.2.1
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqne : q ≠ 0 := by
    have hden := hetaDom.2.2.1
    simp only [sourceQuotDomain, sourceSqrt, ne_eq] at hden
    intro hq
    apply hden
    simp [q, r, hq]
  have hqpos : 0 < q := lt_of_le_of_ne hqnonneg (Ne.symm hqne)
  have hrpos : 0 < r := by
    by_contra hr
    have hrzero : r = 0 := le_antisymm (le_of_not_gt hr) hrnonneg
    simp [q, hrzero] at hqpos
  have hbasepos : 0 < Δ / (s * q * (N : ℝ)) := by
    simpa [sourceRpowDomain, sourceQuot, sourceSqrt, q, r] using
      hetaDom.2.2.2
  have hetaEq :
      η = Real.rpow (Δ / (s * q * (N : ℝ))) ((1 : ℝ) / 3) := by
    rcases hetaDom with ⟨_, _, _, _⟩
    rfl
  have hREq :
      R = Real.rpow Δ ((2 : ℝ) / 3) *
          Real.rpow s ((1 : ℝ) / 3) * Real.sqrt r /
          Real.rpow (N : ℝ) ((2 : ℝ) / 3) := by
    rcases hbranch with ⟨_, _, _, _, _, _⟩
    rfl
  have hetaCube : η ^ 3 = Δ / (s * q * (N : ℝ)) := by
    rw [hetaEq]
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow hbasepos.le (by norm_num : (3 : ℕ) ≠ 0))
  have hetaPos : 0 < η := by
    rw [hetaEq]
    exact Real.rpow_pos_of_pos hbasepos _
  have hqSq : q ^ 2 = r ^ 3 := by
    dsimp [q]
    exact Real.sq_sqrt (pow_nonneg hrnonneg 3)
  have hsqrtCubeSq : (Real.sqrt r ^ 3) ^ 2 = r ^ 3 := by
    calc
      (Real.sqrt r ^ 3) ^ 2 = (Real.sqrt r ^ 2) ^ 3 := by ring
      _ = r ^ 3 := by rw [Real.sq_sqrt hrnonneg]
  have hsqrtCube : Real.sqrt r ^ 3 = q := by
    apply (pow_left_inj₀ (pow_nonneg (Real.sqrt_nonneg r) 3) hqnonneg
      (by norm_num : (2 : ℕ) ≠ 0)).mp
    rw [hsqrtCubeSq, hqSq]
  let X : ℝ := s * η ^ 2 * q
  have hetaSix : η ^ 6 = (Δ / (s * q * (N : ℝ))) ^ 2 := by
    calc
      η ^ 6 = (η ^ 3) ^ 2 := by ring
      _ = (Δ / (s * q * (N : ℝ))) ^ 2 := by rw [hetaCube]
  have hXcube : X ^ 3 = Δ ^ 2 * s * q / (N : ℝ) ^ 2 := by
    dsimp [X]
    rw [show (s * η ^ 2 * q) ^ 3 = s ^ 3 * η ^ 6 * q ^ 3 by ring]
    rw [hetaSix]
    field_simp [ne_of_gt hspos, ne_of_gt hqpos, ne_of_gt hNpos]
    <;> ring
  have hΔtwoThirds :
      (Real.rpow Δ ((2 : ℝ) / 3)) ^ 3 = Δ ^ 2 :=
    real_rpow_two_thirds_pow_three hΔpos.le
  have hsOneThird :
      (Real.rpow s ((1 : ℝ) / 3)) ^ 3 = s := by
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow hspos.le (by norm_num : (3 : ℕ) ≠ 0))
  have hNTwoThirds :
      (Real.rpow (N : ℝ) ((2 : ℝ) / 3)) ^ 3 = (N : ℝ) ^ 2 :=
    real_rpow_two_thirds_pow_three hNpos.le
  have hRcube : R ^ 3 = Δ ^ 2 * s * q / (N : ℝ) ^ 2 := by
    rw [hREq, div_pow]
    rw [show
      (Real.rpow Δ ((2 : ℝ) / 3) * Real.rpow s ((1 : ℝ) / 3) *
          Real.sqrt r) ^ 3 =
        (Real.rpow Δ ((2 : ℝ) / 3)) ^ 3 *
          (Real.rpow s ((1 : ℝ) / 3)) ^ 3 * (Real.sqrt r) ^ 3 by ring]
    rw [hΔtwoThirds, hsOneThird, hsqrtCube, hNTwoThirds]
  have hXpos : 0 < X := by
    dsimp [X]
    exact mul_pos (mul_pos hspos (pow_pos hetaPos 2)) hqpos
  have hRpos : 0 < R := by
    rw [hREq]
    exact div_pos
      (mul_pos
        (mul_pos (Real.rpow_pos_of_pos hΔpos _) (Real.rpow_pos_of_pos hspos _))
        (Real.sqrt_pos.2 hrpos))
      (Real.rpow_pos_of_pos hNpos _)
  have hXeqR : X = R := by
    apply (pow_left_inj₀ hXpos.le hRpos.le
      (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hXcube, hRcube]
  have hbaseEq : Δ = η ^ 3 * (s * q * (N : ℝ)) := by
    rw [hetaCube]
    field_simp [ne_of_gt hspos, ne_of_gt hqpos, ne_of_gt hNpos]
  have hfirst : Δ / ((N : ℝ) * η) = R := by
    rw [hbaseEq, ← hXeqR]
    dsimp [X]
    field_simp [ne_of_gt hNpos, ne_of_gt hetaPos]
    <;> ring
  have hpowSquare (x a : ℝ) (hx : 0 ≤ x) :
      (Real.rpow x a) ^ 2 = Real.rpow x (2 * a) := by
    calc
      (Real.rpow x a) ^ 2 = Real.rpow (Real.rpow x a) 2 :=
        (Real.rpow_two (Real.rpow x a)).symm
      _ = Real.rpow x (a * 2) := (Real.rpow_mul hx a 2).symm
      _ = Real.rpow x (2 * a) := by ring
  let K : ℝ :=
    Real.rpow Δ ((1 : ℝ) / 3) *
      Real.rpow s ((1 : ℝ) / 6) *
        Real.rpow r ((1 : ℝ) / 4) /
      Real.rpow (N : ℝ) ((1 : ℝ) / 3)
  have hKsq : K ^ 2 = R := by
    rw [hREq]
    dsimp [K]
    rw [div_pow]
    simp only [mul_pow]
    change
      (Real.rpow Δ ((1 : ℝ) / 3)) ^ 2 *
            (Real.rpow s ((1 : ℝ) / 6)) ^ 2 *
            (Real.rpow r ((1 : ℝ) / 4)) ^ 2 /
          (Real.rpow (N : ℝ) ((1 : ℝ) / 3)) ^ 2 =
        Real.rpow Δ ((2 : ℝ) / 3) * Real.rpow s ((1 : ℝ) / 3) *
            Real.sqrt r /
          Real.rpow (N : ℝ) ((2 : ℝ) / 3)
    rw [hpowSquare Δ ((1 : ℝ) / 3) hΔpos.le,
      hpowSquare s ((1 : ℝ) / 6) hspos.le,
      hpowSquare r ((1 : ℝ) / 4) hrpos.le,
      hpowSquare (N : ℝ) ((1 : ℝ) / 3) hNpos.le]
    norm_num
    rw [← Real.sqrt_eq_rpow]
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hselected' : Real.sqrt ε ≤ K := by
    simpa [theorem_4_14_otherwise_selected_horizon_relation, K, r] using hselected
  have hεleR : ε ≤ R := by
    rw [← hKsq, ← Real.sq_sqrt hε.le]
    exact (sq_le_sq₀ (Real.sqrt_nonneg ε) hKnonneg).2 hselected'
  let L : ℝ := η * (Real.sqrt (s * ε) * Real.sqrt q)
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg hetaPos.le
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hLsq : L ^ 2 = X * ε := by
    dsimp [L, X]
    rw [show
      (η * (Real.sqrt (s * ε) * Real.sqrt q)) ^ 2 =
        η ^ 2 * (Real.sqrt (s * ε)) ^ 2 * (Real.sqrt q) ^ 2 by ring]
    rw [Real.sq_sqrt (mul_nonneg hspos.le hε.le), Real.sq_sqrt hqnonneg]
    ring
  have hLleR : L ≤ R := by
    apply (sq_le_sq₀ hLnonneg hRpos.le).mp
    rw [hLsq, hXeqR]
    simpa [pow_two] using mul_le_mul_of_nonneg_left hεleR hRpos.le
  have hmiddle :
      η * (C * (Real.sqrt (s * ε) * Real.sqrt q)) / 2 ≤
        (C / 2) * R := by
    have hscaled := mul_le_mul_of_nonneg_left hLleR hC.le
    dsimp [L] at hscaled
    nlinarith
  change
    Δ / ((N : ℝ) * η) +
          η * (C * (Real.sqrt (s * ε) * Real.sqrt q)) / 2 +
          s * η ^ 2 * q / 6 ≤
        ((7 : ℝ) / 6 + C / 2) * R
  rw [hfirst, show s * η ^ 2 * q = R from hXeqR]
  nlinarith

theorem theorem_4_14_otherwise_rate_bound_at_horizon
    {m n : ℕ} (P : Objective m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ ε C : ℝ) (N : ℕ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hΔ : sourceObjectiveInitialGap P W0 hfinite = Δ)
    (hselected :
      theorem_4_14_otherwise_selected_horizon_relation m n s Δ ε N)
    (hrun : theorem_4_14_otherwiseSourceRunForAccuracyHorizon
      P cfgForAccuracyHorizon W0 s Δ ε C N) :
    ∃ hdom : theorem_4_14_otherwiseBranchRateDomain m n s Δ N,
      deterministicAverageNuclearGradient
          P (cfgForAccuracyHorizon ε N) N ≤
        ((7 : ℝ) / 6 + C / 2) *
          theorem_4_14_otherwiseBranchRate m n s Δ N hdom := by
  have hsource :=
    theorem_4_14_otherwise_source_average_bound_at_accuracy_horizon
      P cfgForAccuracyHorizon W0 s Δ ε C N hthird hrun
  obtain ⟨hetaDom, hrhsDom, _hsourceBound⟩ := hsource
  have hrun' := hrun
  unfold theorem_4_14_otherwiseSourceRunForAccuracyHorizon
    theorem_4_14_otherwiseRunForAccuracyHorizon at hrun'
  dsimp at hrun'
  rcases hrun' with
    ⟨_hN, hW0, ⟨_hetaDom', hSchedule⟩, hbranch, hε, hC, hJbound⟩
  have hgapBound :=
    theorem_4_14_source_average_bound_by_initial_gap
      P (cfgForAccuracyHorizon ε N) W0 N s
      (theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom)
      Δ
      (C * (Real.sqrt (s * ε) *
        Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))))
      hfinite hW0 hΔ hthird hSchedule hJbound hrhsDom
  refine ⟨hbranch, le_trans hgapBound ?_⟩
  exact theorem_4_14_otherwise_schedule_rhs_le_branch_rate
    s Δ ε C N hetaDom hbranch hselected hε hC

set_option maxHeartbeats 800000 in
theorem theorem_4_14_otherwise_source_rhs_le_accuracy_at_large_horizon
    {m n : ℕ} (s Δ ε C K : ℝ) (N : ℕ)
    (hetaDom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ N)
    (hbranch : theorem_4_14_otherwiseBranchRateDomain m n s Δ N)
    (hε : epsilonDomain ε)
    (hC : 0 < C)
    (hK : 0 < K)
    (hKrate : (7 : ℝ) / 6 + C / 2 ≤ K)
    (hNlarge :
      (8 * K) ^ 3 * theorem_4_14_otherwiseComplexityRate m n s Δ ε ≤
        (N : ℝ)) :
    let η := theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom
    Δ / ((N : ℝ) * η) +
          η * (C * (Real.sqrt (s * ε) *
            Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)))) / 2 +
          s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 ≤
        ε := by
  let r : ℝ := matrixRankBound m n
  let q : ℝ := Real.sqrt (r ^ 3)
  let η : ℝ := theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom
  let rate : ℝ := theorem_4_14_otherwiseComplexityRate m n s Δ ε
  let B : ℝ := 8 * K
  let X : ℝ := s * η ^ 2 * q
  let Y : ℝ := ε / B ^ 2
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast hbranch.1
  have hΔpos : 0 < Δ := by
    simpa [sourceRpowDomain] using hbranch.2.1
  have hspos : 0 < s := by
    simpa [sourceRpowDomain] using hbranch.2.2.1
  have hrnonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqne : q ≠ 0 := by
    have hden := hetaDom.2.2.1
    simp only [sourceQuotDomain, sourceSqrt, ne_eq] at hden
    intro hq
    apply hden
    simp [q, r, hq]
  have hqpos : 0 < q := lt_of_le_of_ne hqnonneg (Ne.symm hqne)
  have hbasepos : 0 < Δ / (s * q * (N : ℝ)) := by
    simpa [sourceRpowDomain, sourceQuot, sourceSqrt, q, r] using
      hetaDom.2.2.2
  have hetaEq :
      η = Real.rpow (Δ / (s * q * (N : ℝ))) ((1 : ℝ) / 3) := by
    rcases hetaDom with ⟨_, _, _, _⟩
    rfl
  have hetaCube : η ^ 3 = Δ / (s * q * (N : ℝ)) := by
    rw [hetaEq]
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow hbasepos.le (by norm_num : (3 : ℕ) ≠ 0))
  have hetaPos : 0 < η := by
    rw [hetaEq]
    exact Real.rpow_pos_of_pos hbasepos _
  have hetaSix : η ^ 6 = (Δ / (s * q * (N : ℝ))) ^ 2 := by
    calc
      η ^ 6 = (η ^ 3) ^ 2 := by ring
      _ = (Δ / (s * q * (N : ℝ))) ^ 2 := by rw [hetaCube]
  have hXcube : X ^ 3 = Δ ^ 2 * s * q / (N : ℝ) ^ 2 := by
    dsimp [X]
    rw [show (s * η ^ 2 * q) ^ 3 = s ^ 3 * η ^ 6 * q ^ 3 by ring]
    rw [hetaSix]
    field_simp [ne_of_gt hspos, ne_of_gt hqpos, ne_of_gt hNpos]
    <;> ring
  have hXpos : 0 < X := by
    dsimp [X]
    exact mul_pos (mul_pos hspos (pow_pos hetaPos 2)) hqpos
  have hbaseEq : Δ = η ^ 3 * (s * q * (N : ℝ)) := by
    rw [hetaCube]
    field_simp [ne_of_gt hspos, ne_of_gt hqpos, ne_of_gt hNpos]
  have hfirst : Δ / ((N : ℝ) * η) = X := by
    rw [hbaseEq]
    dsimp [X]
    field_simp [ne_of_gt hNpos, ne_of_gt hetaPos]
    <;> ring
  have hrpowSquare :
      (Real.rpow ε (-(3 : ℝ) / 2)) ^ 2 = (ε ^ 3)⁻¹ := by
    calc
      (Real.rpow ε (-(3 : ℝ) / 2)) ^ 2 =
          Real.rpow ε (2 * (-(3 : ℝ) / 2)) := by
        calc
          (Real.rpow ε (-(3 : ℝ) / 2)) ^ 2 =
              Real.rpow (Real.rpow ε (-(3 : ℝ) / 2)) 2 :=
            (Real.rpow_two _).symm
          _ = Real.rpow ε ((-(3 : ℝ) / 2) * 2) :=
            (Real.rpow_mul hε.le (-(3 : ℝ) / 2) 2).symm
          _ = Real.rpow ε (2 * (-(3 : ℝ) / 2)) := by ring
      _ = Real.rpow ε (-(3 : ℝ)) := by norm_num
      _ = (ε ^ 3)⁻¹ := by
        simpa using (inv_nat_pow_eq_rpow_neg_mul ε 3 1).symm
  have hrateEq :
      rate = Real.sqrt s * Real.sqrt q * Δ *
        Real.rpow ε (-(3 : ℝ) / 2) := by
    rfl
  have hratePos : 0 < rate := by
    rw [hrateEq]
    exact mul_pos
      (mul_pos
        (mul_pos (Real.sqrt_pos.2 hspos) (Real.sqrt_pos.2 hqpos)) hΔpos)
      (Real.rpow_pos_of_pos hε _)
  have hrateSq : rate ^ 2 * ε ^ 3 = Δ ^ 2 * s * q := by
    rw [hrateEq]
    rw [show
      (Real.sqrt s * Real.sqrt q * Δ * Real.rpow ε (-(3 : ℝ) / 2)) ^ 2 =
        (Real.sqrt s) ^ 2 * (Real.sqrt q) ^ 2 * Δ ^ 2 *
          (Real.rpow ε (-(3 : ℝ) / 2)) ^ 2 by ring]
    rw [Real.sq_sqrt hspos.le, Real.sq_sqrt hqnonneg, hrpowSquare]
    field_simp [ne_of_gt hε]
    <;> ring
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hBone : 1 ≤ B := by
    dsimp [B]
    nlinarith [hKrate, hC]
  have hlarge : B ^ 3 * rate ≤ (N : ℝ) := by
    simpa [B, rate] using hNlarge
  have hlargeNonneg : 0 ≤ B ^ 3 * rate := by positivity
  have hlargeSq : (B ^ 3 * rate) ^ 2 ≤ (N : ℝ) ^ 2 :=
    (sq_le_sq₀ hlargeNonneg hNpos.le).2 hlarge
  have hYpos : 0 < Y := by
    dsimp [Y]
    exact div_pos hε (pow_pos hBpos 2)
  have hscaledIdentity :
      (B ^ 3 * rate) ^ 2 * Y ^ 3 = Δ ^ 2 * s * q := by
    rw [← hrateSq]
    dsimp [Y]
    field_simp [ne_of_gt hBpos]
    <;> ring
  have hscaled :=
    mul_le_mul_of_nonneg_right hlargeSq (pow_nonneg hYpos.le 3)
  have hnum : Δ ^ 2 * s * q ≤ (N : ℝ) ^ 2 * Y ^ 3 := by
    rw [← hscaledIdentity]
    simpa [mul_assoc] using hscaled
  have hXcubeLe : X ^ 3 ≤ Y ^ 3 := by
    rw [hXcube]
    exact (div_le_iff₀ (pow_pos hNpos 2)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnum)
  have hXleY : X ≤ Y :=
    le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hYpos.le hXcubeLe
  have hBsq : B ≤ B ^ 2 := by nlinarith
  have hYle : Y ≤ ε / B := by
    dsimp [Y]
    exact div_le_div_of_nonneg_left hε.le hBpos hBsq
  have hXweak : X ≤ ε / B := hXleY.trans hYle
  let L : ℝ := η * (Real.sqrt (s * ε) * Real.sqrt q)
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hLsq : L ^ 2 = X * ε := by
    dsimp [L, X]
    rw [show
      (η * (Real.sqrt (s * ε) * Real.sqrt q)) ^ 2 =
        η ^ 2 * (Real.sqrt (s * ε)) ^ 2 * (Real.sqrt q) ^ 2 by ring]
    rw [Real.sq_sqrt (mul_nonneg hspos.le hε.le), Real.sq_sqrt hqnonneg]
    ring
  have hLsqLe : L ^ 2 ≤ (ε / B) ^ 2 := by
    rw [hLsq]
    have hscaledX := mul_le_mul_of_nonneg_right hXleY hε.le
    dsimp [Y] at hscaledX
    convert hscaledX using 1 <;>
      field_simp [ne_of_gt hBpos] <;> ring
  have hLle : L ≤ ε / B := by
    exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
      (div_nonneg hε.le hBpos.le) hLsqLe
  have hXscaled :=
    mul_le_mul_of_nonneg_left hXweak (by norm_num : (0 : ℝ) ≤ 7 / 6)
  have hLscaled :=
    mul_le_mul_of_nonneg_left hLle
      (div_nonneg hC.le (by norm_num : (0 : ℝ) ≤ 2))
  have hsum :
      (7 : ℝ) / 6 * X + C / 2 * L ≤
        ((7 : ℝ) / 6 + C / 2) * (ε / B) := by
    calc
      (7 : ℝ) / 6 * X + C / 2 * L ≤
          (7 : ℝ) / 6 * (ε / B) + C / 2 * (ε / B) :=
        add_le_add hXscaled hLscaled
      _ = ((7 : ℝ) / 6 + C / 2) * (ε / B) := by ring
  have hcoeff :=
    mul_le_mul_of_nonneg_right hKrate (div_nonneg hε.le hBpos.le)
  have hKcancel : K * (ε / B) = ε / 8 := by
    dsimp [B]
    field_simp [ne_of_gt hK]
    <;> ring
  change
    Δ / ((N : ℝ) * η) + η * (C * (Real.sqrt (s * ε) * Real.sqrt q)) / 2 +
        s * η ^ 2 * q / 6 ≤ ε
  rw [hfirst, show s * η ^ 2 * q = X from rfl]
  have hrewrite :
      X + η * (C * (Real.sqrt (s * ε) * Real.sqrt q)) / 2 + X / 6 =
        (7 : ℝ) / 6 * X + C / 2 * L := by
    dsimp [L]
    ring
  rw [hrewrite]
  calc
    (7 : ℝ) / 6 * X + C / 2 * L ≤
        ((7 : ℝ) / 6 + C / 2) * (ε / B) := hsum
    _ ≤ K * (ε / B) := hcoeff
    _ = ε / 8 := hKcancel
    _ ≤ ε := by nlinarith [hε.le]

theorem theorem_4_14_otherwise_complexity_witness
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n)
    (s Δ C : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hΔ : sourceObjectiveInitialGap P cfg.W0 hfinite = Δ)
    (hC : 0 < C)
    (K : ℝ)
    (hK : 0 < K)
    (hKrate : (7 : ℝ) / 6 + C / 2 ≤ K)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n)
    (hSchedule :
      theorem_4_14_otherwiseHorizonScheduleForAccuracy
        cfgForAccuracyHorizon cfg.W0 s Δ)
    (hruns : ∀ ε : ℝ, epsilonDomain ε →
      ∀ N : ℕ, horizonDomain N →
        theorem_4_14_otherwiseSourceRunForAccuracyHorizon
          P cfgForAccuracyHorizon cfg.W0 s Δ ε C N) :
    EpsilonHorizonNuclearStationarityComplexityWithHorizonRate
      (fun ε N => deterministicAverageNuclearGradient
        P (cfgForAccuracyHorizon ε N) N)
      (fun ε N => theorem_4_14_otherwiseRunForAccuracyHorizon
        P cfgForAccuracyHorizon cfg.W0 s Δ ε C N)
      (fun _N ε => K * theorem_4_14_otherwiseComplexityRate m n s Δ ε)
      (theoremScope "Theorem 4.14 otherwise epsilon complexity" ["epsilon"]) := by
  have hrunOne := hruns 1 (by norm_num [epsilonDomain]) 1
    (by norm_num [horizonDomain])
  have hrunOne' := hrunOne
  unfold theorem_4_14_otherwiseSourceRunForAccuracyHorizon
    theorem_4_14_otherwiseRunForAccuracyHorizon at hrunOne'
  dsimp at hrunOne'
  rcases hrunOne' with
    ⟨_hOne, _hW0One, ⟨hetaDomOne, _hScheduleOne⟩, hbranchOne, _hRegimeOne⟩
  have hΔpos : 0 < Δ := by
    simpa [sourceRpowDomain] using hbranchOne.2.1
  have hspos : 0 < s := by
    simpa [sourceRpowDomain] using hbranchOne.2.2.1
  let q : ℝ := Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqne : q ≠ 0 := by
    have hden := hetaDomOne.2.2.1
    simp only [sourceQuotDomain, sourceSqrt, ne_eq] at hden
    intro hqzero
    apply hden
    simp [q, hqzero]
  have hqpos : 0 < q := lt_of_le_of_ne hqnonneg (Ne.symm hqne)
  let A : ℝ := Real.sqrt s * Real.sqrt q * Δ
  have hApos : 0 < A := by
    dsimp [A]
    exact mul_pos
      (mul_pos (Real.sqrt_pos.2 hspos) (Real.sqrt_pos.2 hqpos)) hΔpos
  let H : ℝ := (8 * K) ^ 3
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  let ε₀ : ℝ := min 1 (H * A)
  have hε₀pos : 0 < ε₀ := by
    dsimp [ε₀]
    exact lt_min (by norm_num) (mul_pos hHpos hApos)
  let Couter : ℝ := 1024 * K ^ 2
  have hCouterPos : 0 < Couter := by
    dsimp [Couter]
    positivity
  unfold EpsilonHorizonNuclearStationarityComplexityWithHorizonRate
  refine ⟨Couter, ε₀, hCouterPos, hε₀pos, ?_, ?_⟩
  · simp [ConstantRespectsScope, theoremScope, Couter, hCouterPos]
  · intro ε hε hεsmall
    have hεone : ε ≤ 1 := le_trans hεsmall (min_le_left _ _)
    have hεHA : ε ≤ H * A := le_trans hεsmall (min_le_right _ _)
    let rate : ℝ := theorem_4_14_otherwiseComplexityRate m n s Δ ε
    have hrateEq :
        rate = A * Real.rpow ε (-(3 : ℝ) / 2) := by
      rfl
    have hratePos : 0 < rate := by
      rw [hrateEq]
      exact mul_pos hApos (Real.rpow_pos_of_pos hε _)
    have hsqrtε_le_one : Real.sqrt ε ≤ 1 := by
      exact (Real.sqrt_le_one).2 hεone
    have hrpowThreeHalves :
        Real.rpow ε ((3 : ℝ) / 2) = ε * Real.sqrt ε := by
      calc
        Real.rpow ε ((3 : ℝ) / 2) =
            Real.rpow ε (1 + (1 : ℝ) / 2) := by norm_num
        _ = Real.rpow ε 1 * Real.rpow ε ((1 : ℝ) / 2) :=
          Real.rpow_add hε 1 ((1 : ℝ) / 2)
        _ = ε * Real.sqrt ε := by
          simp [Real.rpow_one, Real.sqrt_eq_rpow]
    have hrpowThreeHalves_le :
        Real.rpow ε ((3 : ℝ) / 2) ≤ H * A := by
      rw [hrpowThreeHalves]
      have hprod : 0 ≤ ε * (1 - Real.sqrt ε) :=
        mul_nonneg hε.le (sub_nonneg.mpr hsqrtε_le_one)
      exact le_trans (by nlinarith) hεHA
    have hrpowThreeHalvesPos : 0 < Real.rpow ε ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hε _
    have hrpowNeg :
        Real.rpow ε (-(3 : ℝ) / 2) =
          (Real.rpow ε ((3 : ℝ) / 2))⁻¹ := by
      calc
        Real.rpow ε (-(3 : ℝ) / 2) =
            Real.rpow ε (-((3 : ℝ) / 2)) := by congr 2 <;> ring
        _ = (Real.rpow ε ((3 : ℝ) / 2))⁻¹ :=
          Real.rpow_neg hε.le ((3 : ℝ) / 2)
    have hHrate_one : 1 ≤ H * rate := by
      have hdiv : 1 ≤ H * A / Real.rpow ε ((3 : ℝ) / 2) :=
        (le_div_iff₀ hrpowThreeHalvesPos).2 (by
          simpa [one_mul] using hrpowThreeHalves_le)
      rw [hrateEq, hrpowNeg]
      simpa [div_eq_mul_inv, mul_assoc] using hdiv
    let N : ℕ :=
      max 1
        (Nat.ceil
          (H * rate))
    have hN : horizonDomain N := by
      dsimp [horizonDomain, N]
      omega
    have hNlower : H * rate ≤ (N : ℝ) := by
      simpa [N] using le_positive_ceil_max_one (H * rate)
    have hceilOne : 1 ≤ Nat.ceil (H * rate) := by
      have hceil := Nat.le_ceil (H * rate)
      exact_mod_cast le_trans hHrate_one hceil
    have hNeq : N = Nat.ceil (H * rate) := by
      dsimp [N]
      exact max_eq_right hceilOne
    have hNupper : (N : ℝ) ≤ 2 * (H * rate) := by
      rw [hNeq]
      have hceilLt := Nat.ceil_lt_add_one (mul_nonneg hHpos.le hratePos.le)
      exact le_trans hceilLt.le (by linarith)
    have hrun := hruns ε hε N hN
    have hsource :=
      theorem_4_14_otherwise_source_average_bound_at_accuracy_horizon
        P cfgForAccuracyHorizon cfg.W0 s Δ ε C N hthird hrun
    obtain ⟨hetaDom, hdom, hsourceBound⟩ := hsource
    have hrun' := hrun
    unfold theorem_4_14_otherwiseSourceRunForAccuracyHorizon
      theorem_4_14_otherwiseRunForAccuracyHorizon at hrun'
    dsimp at hrun'
    rcases hrun' with
      ⟨_hN, hW0, ⟨_hetaDom', hScheduleN⟩, hbranch, hRegime⟩
    have hJbound :
        hessianDirectionalAverage P (cfgForAccuracyHorizon ε N) N ≤
          C * (Real.sqrt (s * ε) *
            Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) :=
      hRegime.2.2
    have hsourceGapBound :=
      theorem_4_14_source_average_bound_by_initial_gap
        P (cfgForAccuracyHorizon ε N) cfg.W0 N s
        (theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom)
        Δ
        (C * (Real.sqrt (s * ε) *
          Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))))
        hfinite hW0 hΔ hthird hScheduleN hJbound hdom
    refine ⟨N, hrun, ?_⟩
    refine ⟨?_, ?_⟩
    · exact le_trans hsourceGapBound
        (theorem_4_14_otherwise_source_rhs_le_accuracy_at_large_horizon
          s Δ ε C K N hetaDom hbranch hε hC hK hKrate
          (by simpa [H, rate] using hNlower))
    · calc
        (N : ℝ) ≤ 2 * (H * rate) := hNupper
        _ = Couter * (K * rate) := by
          dsimp [H, Couter]
          ring
        _ = Couter *
            (K * theorem_4_14_otherwiseComplexityRate m n s Δ ε) := by
          rfl

theorem theorem_4_14_otherwise_branch_rate_and_complexity_of_source_assumptions
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n)
    (s Δ C : ℝ)
    (hfinite : P.HasFiniteInfimum)
    (hthird : ThirdDerivativeBounded P s)
    (hΔ : sourceObjectiveInitialGap P cfg.W0 hfinite = Δ)
    (hC : 0 < C)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n)
    (hSchedule :
      theorem_4_14_otherwiseHorizonScheduleForAccuracy
        cfgForAccuracyHorizon cfg.W0 s Δ)
    (hruns : ∀ ε : ℝ, epsilonDomain ε →
      ∀ N : ℕ, horizonDomain N →
        theorem_4_14_otherwiseSourceRunForAccuracyHorizon
          P cfgForAccuracyHorizon cfg.W0 s Δ ε C N) :
    theorem_4_14_otherwise_branch_rate_and_complexity
      P cfg s Δ C cfgForAccuracyHorizon := by
  refine ⟨(7 : ℝ) / 6 + C / 2, by nlinarith [hC], ?_, ?_⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε hεsmall N hN hselected hrun
    exact theorem_4_14_otherwise_rate_bound_at_horizon
      P cfgForAccuracyHorizon cfg.W0 s Δ ε C N
      hfinite hthird hΔ hselected hrun
  · constructor
    · exact theorem_4_14_otherwise_complexity_witness
        P cfg s Δ C hfinite hthird hΔ hC
        ((7 : ℝ) / 6 + C / 2) (by nlinarith [hC]) le_rfl
        cfgForAccuracyHorizon hSchedule hruns
    · intro ε
      simpa [deterministicAverageNuclearGradient] using
        (generatedNuclearStationarityTransfer_of_finite_average
          P
          (fun N => theorem_4_14_otherwiseRunForAccuracyHorizon
            P cfgForAccuracyHorizon cfg.W0 s Δ ε C N)
          (fun _N hN => hN.1)
          (fun N _hN t =>
            (deterministicMuonState P (cfgForAccuracyHorizon ε N) t).W))

theorem theorem_4_14_source_rate_consequences_of_source_assumptions
    {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n)
    (s : ℝ) (hfinite : P.HasFiniteInfimum) :
    theorem_4_14_source_rate_consequences P cfg s hfinite := by
  dsimp [theorem_4_14_source_rate_consequences]
  constructor
  · intro hthird J hpointwise cfgForHorizon hruns
    exact theorem_4_14_positive_branch_rate_and_complexity_of_source_assumptions
      P cfg s (sourceObjectiveInitialGap P cfg.W0 hfinite) J
      hfinite hthird rfl hpointwise cfgForHorizon hruns
  · intro hthird C hC cfgForAccuracyHorizon hSchedule hruns
    exact theorem_4_14_otherwise_branch_rate_and_complexity_of_source_assumptions
      P cfg s (sourceObjectiveInitialGap P cfg.W0 hfinite) C
      hfinite hthird rfl hC cfgForAccuracyHorizon hSchedule hruns

theorem orthogonalizedDirection_frobeniusInner_eq_sum_diagonal
    {m n : ℕ} (M : Mat m n) :
    ∃ s : Fin M.rank → ℝ,
      NonnegativeDiagonal s ∧
        frobeniusInner M (orthogonalizedDirection M) = ∑ i : Fin M.rank, s i :=
  frobeniusInner_eq_sum_diagonal_of_isThinSVDWithPolar
    (orthogonalizedDirection_isThinSVDWithPolar M)

theorem diagonal_pos_of_rank_thin_factorization
    {m n k : ℕ} {M : Matrix (Fin m) (Fin n) ℝ}
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (s : Fin k → ℝ) (hs : NonnegativeDiagonal s)
    (hM : M = U * Matrix.diagonal s * Vᵀ) (hrank : M.rank = k) :
    ∀ i : Fin k, 0 < s i := by
  classical
  intro i
  have hrank_le_diag : k ≤ (Matrix.diagonal s).rank := by
    calc
      k = M.rank := hrank.symm
      _ = (U * Matrix.diagonal s * Vᵀ).rank := by rw [hM]
      _ ≤ (Matrix.diagonal s * Vᵀ).rank :=
        by
          simpa [Matrix.mul_assoc] using
            Matrix.rank_mul_le_right U (Matrix.diagonal s * Vᵀ)
      _ ≤ (Matrix.diagonal s).rank :=
        Matrix.rank_mul_le_left (Matrix.diagonal s) Vᵀ
  have hcard_ge : k ≤ Fintype.card {i : Fin k // s i ≠ 0} := by
    simpa [Matrix.rank_diagonal] using hrank_le_diag
  have hnonzero : s i ≠ 0 := by
    by_contra hi
    have hlt : Fintype.card {j : Fin k // s j ≠ 0} < Fintype.card (Fin k) :=
      Fintype.card_subtype_lt (p := fun j : Fin k => s j ≠ 0) (x := i) (by simpa [hi])
    have hlt' : Fintype.card {j : Fin k // s j ≠ 0} < k := by
      simpa using hlt
    exact (not_le_of_gt hlt') hcard_ge
  exact lt_of_le_of_ne (hs i) (Ne.symm hnonzero)

theorem frobeniusInner_eq_sum_pos_diagonal_of_isThinSVDWithPolar
    {m n : ℕ} {M P : Mat m n} (h : IsThinSVDWithPolar M P) :
    ∃ s : Fin M.rank → ℝ,
      (∀ i : Fin M.rank, 0 < s i) ∧ frobeniusInner M P = ∑ i : Fin M.rank, s i := by
  classical
  rcases h with ⟨U, V, s, hU, hV, hs, hM, hP⟩
  refine ⟨s, ?_, ?_⟩
  · exact diagonal_pos_of_rank_thin_factorization U V s hs hM rfl
  · exact frobeniusInner_factorization_eq_sum_diagonal U V s hU hV hM hP

theorem orthogonalizedDirection_frobeniusInner_eq_sum_pos_diagonal
    {m n : ℕ} (M : Mat m n) :
    ∃ s : Fin M.rank → ℝ,
      (∀ i : Fin M.rank, 0 < s i) ∧
        frobeniusInner M (orthogonalizedDirection M) = ∑ i : Fin M.rank, s i :=
  frobeniusInner_eq_sum_pos_diagonal_of_isThinSVDWithPolar
    (orthogonalizedDirection_isThinSVDWithPolar M)

theorem orthogonalizedDirection_right_factor_diagonalizes_transpose_mul_self
    {m n : ℕ} (M : Mat m n) :
    ∃ (U : Matrix (Fin m) (Fin M.rank) ℝ)
      (V : Matrix (Fin n) (Fin M.rank) ℝ)
      (s : Fin M.rank → ℝ),
        OrthonormalColumns U ∧
        OrthonormalColumns V ∧
        (∀ i : Fin M.rank, 0 < s i) ∧
        M = U * Matrix.diagonal s * Vᵀ ∧
        orthogonalizedDirection M = U * Vᵀ ∧
        Mᵀ * M * V = V * Matrix.diagonal (fun i : Fin M.rank => s i ^ 2) := by
  classical
  rcases orthogonalizedDirection_isThinSVDWithPolar M with
    ⟨U, V, s, hU, hV, hs, hM, hP⟩
  refine ⟨U, V, s, hU, hV, ?_, hM, hP, ?_⟩
  · exact diagonal_pos_of_rank_thin_factorization U V s hs hM rfl
  · exact transpose_mul_self_mul_right_factor_eq_right_mul_diagonal_sq U V s hU hV hM

theorem orthonormalColumns_column_toLp_ne_zero
    {rows cols : ℕ} (Q : Matrix (Fin rows) (Fin cols) ℝ)
    (hQ : OrthonormalColumns Q) (i : Fin cols) :
    WithLp.toLp 2 (fun a : Fin rows => Q a i) ≠
      (0 : EuclideanSpace ℝ (Fin rows)) := by
  classical
  intro hzero
  have hdiag := hQ i i
  have hsum_zero :
      (∑ a : Fin rows, Q a i * Q a i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro a _ha
    have hcoord : Q a i = 0 := by
      have happ := congrArg (fun v : EuclideanSpace ℝ (Fin rows) => v a) hzero
      simpa using happ
    simp [hcoord]
  have : (1 : ℝ) = 0 := by
    simpa using hdiag.symm.trans hsum_zero
  norm_num at this

theorem right_factor_column_hasEigenvalue_transpose_mul_self
    {m n k : ℕ} {M : Mat m n}
    (V : Matrix (Fin n) (Fin k) ℝ) (s : Fin k → ℝ)
    (hV : OrthonormalColumns V)
    (hdiag : Mᵀ * M * V = V * Matrix.diagonal (fun i : Fin k => s i ^ 2))
    (i : Fin k) :
    Module.End.HasEigenvalue
      (Matrix.toEuclideanLin (𝕜 := ℝ) (Mᵀ * M))
      (s i ^ 2) := by
  classical
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun a : Fin n => V a i)
  have hv_ne : v ≠ 0 := by
    simpa [v] using orthonormalColumns_column_toLp_ne_zero V hV i
  have hcol :
      (Mᵀ * M) *ᵥ (fun a : Fin n => V a i) =
        (s i ^ 2) • (fun a : Fin n => V a i) := by
    ext a
    calc
      ((Mᵀ * M) *ᵥ (fun a : Fin n => V a i)) a = (Mᵀ * M * V) a i := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
      _ = (V * Matrix.diagonal (fun i : Fin k => s i ^ 2)) a i := by
        rw [hdiag]
      _ = (s i ^ 2) * V a i := by
        simp [Matrix.mul_apply, Matrix.diagonal]
        ring
      _ = ((s i ^ 2) • (fun a : Fin n => V a i)) a := by
        simp [Pi.smul_apply]
  have hv_apply :
      Matrix.toEuclideanLin (𝕜 := ℝ) (Mᵀ * M) v = (s i ^ 2) • v := by
    ext a
    simpa [v, Matrix.toEuclideanLin_apply_piLp_toLp, hcol, Pi.smul_apply]
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨by
    simpa [Module.End.mem_eigenspace_iff] using hv_apply, hv_ne⟩

theorem right_factor_column_hasEigenvalue_adjoint_comp_self
    {m n k : ℕ} {M : Mat m n}
    (V : Matrix (Fin n) (Fin k) ℝ) (s : Fin k → ℝ)
    (hV : OrthonormalColumns V)
    (hdiag : Mᵀ * M * V = V * Matrix.diagonal (fun i : Fin k => s i ^ 2))
    (i : Fin k) :
    Module.End.HasEigenvalue
      ((Matrix.toEuclideanLin (𝕜 := ℝ) M).adjoint.comp
        (Matrix.toEuclideanLin (𝕜 := ℝ) M))
      (s i ^ 2) := by
  classical
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun a : Fin n => V a i)
  have hv_ne : v ≠ 0 := by
    simpa [v] using orthonormalColumns_column_toLp_ne_zero V hV i
  have hcol :
      (Mᵀ * M) *ᵥ (fun a : Fin n => V a i) =
        (s i ^ 2) • (fun a : Fin n => V a i) := by
    ext a
    calc
      ((Mᵀ * M) *ᵥ (fun a : Fin n => V a i)) a = (Mᵀ * M * V) a i := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
      _ = (V * Matrix.diagonal (fun i : Fin k => s i ^ 2)) a i := by
        rw [hdiag]
      _ = (s i ^ 2) * V a i := by
        simp [Matrix.mul_apply, Matrix.diagonal]
        ring
      _ = ((s i ^ 2) • (fun a : Fin n => V a i)) a := by
        simp [Pi.smul_apply]
  have hv_apply :
      ((Matrix.toEuclideanLin (𝕜 := ℝ) M).adjoint.comp
        (Matrix.toEuclideanLin (𝕜 := ℝ) M)) v = (s i ^ 2) • v := by
    have hadj :
        (Matrix.toEuclideanLin (𝕜 := ℝ) M).adjoint =
          Matrix.toEuclideanLin (𝕜 := ℝ) Mᵀ := by
      simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := M)).symm
    ext a
    simpa [v, hadj, Matrix.toEuclideanLin_apply_piLp_toLp,
      LinearMap.comp_apply, hcol, Pi.smul_apply, Matrix.mulVec_mulVec]
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨by
    simpa [Module.End.mem_eigenspace_iff] using hv_apply, hv_ne⟩

theorem orthogonalizedDirection_right_factor_hasEigenvalue_adjoint_comp_self
    {m n : ℕ} (M : Mat m n) :
    ∃ (U : Matrix (Fin m) (Fin M.rank) ℝ)
      (V : Matrix (Fin n) (Fin M.rank) ℝ)
      (s : Fin M.rank → ℝ),
        OrthonormalColumns U ∧
        OrthonormalColumns V ∧
        (∀ i : Fin M.rank, 0 < s i) ∧
        M = U * Matrix.diagonal s * Vᵀ ∧
        orthogonalizedDirection M = U * Vᵀ ∧
        Mᵀ * M * V = V * Matrix.diagonal (fun i : Fin M.rank => s i ^ 2) ∧
        (∀ i : Fin M.rank,
          Module.End.HasEigenvalue
            ((Matrix.toEuclideanLin (𝕜 := ℝ) M).adjoint.comp
              (Matrix.toEuclideanLin (𝕜 := ℝ) M))
            (s i ^ 2)) := by
  classical
  rcases orthogonalizedDirection_right_factor_diagonalizes_transpose_mul_self M with
    ⟨U, V, s, hU, hV, hspos, hM, hP, hdiag⟩
  refine ⟨U, V, s, hU, hV, hspos, hM, hP, hdiag, ?_⟩
  intro i
  exact right_factor_column_hasEigenvalue_adjoint_comp_self V s hV hdiag i

theorem spectralNorm_mul_transpose_le_one_of_orthonormalColumns
    {m n k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ)
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V) :
    spectralNorm (U * Vᵀ) ≤ 1 := by
  classical
  let qU : Fin k → EuclideanSpace ℝ (Fin m) :=
    fun j => WithLp.toLp 2 (fun a => U a j)
  let qV : Fin k → EuclideanSpace ℝ (Fin n) :=
    fun j => WithLp.toLp 2 (fun a => V a j)
  have hqU : Orthonormal ℝ qU := by
    rw [orthonormal_iff_ite]
    intro i j
    calc
      inner ℝ (qU i) (qU j) = ∑ a : Fin m, U a i * U a j := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro a _ha
        calc
          inner ℝ (qU i a) (qU j a) = U a j * U a i := by
            exact RCLike.inner_apply (U a i) (U a j)
          _ = U a i * U a j := by ring
      _ = if i = j then 1 else 0 := hU i j
  let L := (Matrix.toEuclideanLin (𝕜 := ℝ) (U * Vᵀ)).toContinuousLinearMap
  change ‖L‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound L (by norm_num)
  intro x
  let c : Fin k → ℝ := fun j => inner ℝ x (qV j)
  have happly : L x = ∑ j : Fin k, c j • qU j := by
    ext a
    simp [L, qU, qV, c, Matrix.toEuclideanLin_apply_piLp_toLp,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      PiLp.inner_apply, RCLike.inner_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _hb
    change U a j * (V b j * x b) = (V b j * x b) * U a j
    ring
  have houtSq : ‖L x‖ ^ 2 = ∑ j : Fin k, c j ^ 2 := by
    rw [happly, norm_sq_eq_re_inner (𝕜 := ℝ), hqU.inner_sum c c Finset.univ]
    simp [pow_two]
  have hcoeff : (∑ j : Fin k, c j ^ 2) ≤ ‖x‖ ^ 2 := by
    simpa [c, qV] using orthonormalColumns_bessel_bound V hV x
  have hout : ‖L x‖ ≤ ‖x‖ := by
    nlinarith [norm_nonneg (L x), norm_nonneg x]
  simpa using hout

theorem spectralNorm_nonneg {m n : ℕ} (A : Mat m n) :
    0 ≤ spectralNorm A := by
  simpa [spectralNorm] using
    (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues_nonneg 0

theorem nuclearNorm_nonneg {m n : ℕ} (A : Mat m n) :
    0 ≤ nuclearNorm A := by
  unfold nuclearNorm
  exact Finset.sum_nonneg fun i _hi =>
    (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues_nonneg i

theorem sqrt_constant_absorption (c x : ℝ) (hc : 0 ≤ c) :
    Real.sqrt c * (Real.sqrt c * x) ≤ c * x := by
  apply le_of_eq
  have hsqrt_sq : Real.sqrt c * Real.sqrt c = c := by
    simpa [pow_two] using Real.sq_sqrt hc
  calc
    Real.sqrt c * (Real.sqrt c * x) =
        (Real.sqrt c * Real.sqrt c) * x := by ring
    _ = c * x := by rw [hsqrt_sq]

end SGD.Muon
end
