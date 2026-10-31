import Algorithms.Unverified.MARINA.Part003
import Algorithms.Unverified.MARINA.Part004.Part001

-- Aggregator for `Algorithms.Unverified.MARINA`. Source declarations live under `MARINA/`.

namespace MARINA

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-! ## Literal online moment boundary

Assumption 3.3 states only the workerwise fixed-query unbiasedness and
bounded-variance equations.  Adaptive-query regularity used by the generated
Algorithm 3 proofs is kept separate below. -/

/-- Literal fixed-query moments supply the complete homogeneous refresh
second-moment estimate.  Adaptive law regularity is not used in this
fixed-query calculation; it is needed only when the query itself is random. -/
theorem onlineFixedRefreshAverage_secondMoment_of_literal
    {d n b : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    Integrable
        (fun batch : (i : Worker n) → Fin b.1 → Sample i ↦
          ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
              stochasticGradient A.problem i (batch i j) x)) -
            globalGradient (onlineLocalProblem A.problem) x‖ ^ 2)
        (onlineBatchLaw A.problem b) ∧
      (∫ batch : (i : Worker n) → Fin b.1 → Sample i,
          ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
              stochasticGradient A.problem i (batch i j) x)) -
            globalGradient (onlineLocalProblem A.problem) x‖ ^ 2
          ∂onlineBatchLaw A.problem b) ≤
        varianceAggregateSq sigma / (n.1 * b.1) := by
  let sizes := fun _ : Worker n ↦ b
  have hint := heterogeneousOnlineInitialEstimatorErrorSq_integrable_of_literal
    (b := sizes) A x sigma hLiteral hDiff
  have hbound := expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
    (b := sizes) A x sigma hLiteral hDiff
  constructor
  · simpa [sizes, heterogeneousOnlineInitialEstimatorErrorSq,
      heterogeneousOnlineInitialEstimator, heterogeneousOnlineBatchLaw,
      onlineBatchLaw] using hint
  · have hscale : heterogeneousOnlineVarianceTerm sigma sizes =
        varianceAggregateSq sigma / (n.1 * b.1) := by
      unfold heterogeneousOnlineVarianceTerm varianceAggregateSq meanSquare
        average SOptLib.finiteUniformAverage
      simp only [sizes, Fintype.card_fin, smul_eq_mul]
      have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
      have hb : (b.1 : ℝ) ≠ 0 := by exact_mod_cast b.2.ne'
      rw [← Finset.sum_div]
      field_simp [hn, hb]
    rw [← hscale]
    simpa [sizes, expectedHeterogeneousOnlineInitialEstimatorErrorSq,
      heterogeneousOnlineInitialEstimatorErrorSq,
      heterogeneousOnlineInitialEstimator, heterogeneousOnlineBatchLaw,
      onlineBatchLaw] using hbound

set_option maxHeartbeats 2000000 in
/-- The actual proof-exact refresh error at a generated query is integrable
and obeys the literal Assumption 3.3 variance bound.  The query and current
refresh batch are the ones in `onlineProofExactProcess` and
`onlineProofExactPathLaw`; their independence is derived from the iid round
law.  This closes the refresh branch needed by the law-level Eq. (46)
recurrence without global sample-loss differentiability. -/
theorem
    onlineProofExact_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i))
    (k : ℕ) :
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    Integrable refreshErrorSq law ∧
      (∫ path, refreshErrorSq path ∂law) ≤
        varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let query := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (run (k + 1) path).x
  let batch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (path k).2.1.1
  let batchLaw := onlineBatchLaw A.problem b
  let φ := fun (x : Point d)
      (fresh : (i : Worker n) → Fin b.1 → Sample i) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (fresh i j) x)) -
      globalGradient P x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate := onlineProofExactProcess_aemeasurable_of_lawRegularity
    A x0 hBatch hRegularity k
  have hx : AEStronglyMeasurable (fun path ↦ (run k path).x) law := by
    simpa [run, law] using
      ((measurable_state_x d).comp_aemeasurable hstate).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path ↦ (run k path).g) law := by
    simpa [run, law] using
      ((measurable_state_g d).comp_aemeasurable hstate).aestronglyMeasurable
  have hresidual : AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law := by
    exact hg.sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        hx.aemeasurable).aestronglyMeasurable
  have hquery : AEStronglyMeasurable query law := by
    have hgrad : AEStronglyMeasurable
        (fun path ↦ globalGradient P (run k path).x) law :=
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        hx.aemeasurable).aestronglyMeasurable
    have hg' : AEStronglyMeasurable (fun path ↦ (run k path).g) law := by
      refine (hresidual.add hgrad).congr (Filter.Eventually.of_forall ?_)
      intro path
      change (run k path).g - globalGradient P (run k path).x +
        globalGradient P (run k path).x = (run k path).g
      abel
    have hstep := hx.sub (hg'.const_smul (A.stepSize : ℝ))
    simpa [query, run, onlineProofExactProcess_succ, onlineStep,
      primalStep_eq] using hstep
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hfresh := onlineProofExact_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hqueryBatch : ProbabilityTheory.IndepFun query batch law := by
    have h := hfresh.1.comp
      (show Measurable
        (fun p : (Point d × Point d) × Point d ↦ p.1.1) by fun_prop)
      (show Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1) by fun_prop)
    simpa [query, batch, run, law, P] using h
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law =
          Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1)
            (Measure.map
              (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k)
              law) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · exact measurable_pi_apply k
      _ = Measure.map
            (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1)
            (onlineRoundLaw A) := by
              rw [show Measure.map
                  (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k)
                  law = onlineRoundLaw A by
                simpa [law, onlineProofExactPathLaw] using
                  SOptLib.iidStreamLaw_map_eval
                    (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = batchLaw := by
        simpa [batchLaw] using onlineRoundLaw_refreshBatch_marginal
          (b0 := b0) A
  haveI : IsProbabilityMeasure (Measure.map query law) :=
    Measure.isProbabilityMeasure_map hquery.aemeasurable
  have hφ : AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) ↦
        φ p.1 p.2) ((Measure.map query law).prod batchLaw) := by
    simpa [φ, P] using
      (onlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
        (b := b) A.problem hRegularity (Measure.map query law))
  have hfixed (x : Point d) :
      Integrable (φ x) batchLaw ∧
        (∫ fresh, φ x fresh ∂batchLaw) ≤
          varianceAggregateSq σ / (n.1 * b.1) := by
    simpa [φ, P, batchLaw] using
      (onlineFixedRefreshAverage_secondMoment_of_literal
        (b := b) A x σ hLiteral hDiff)
  have hcomp : Integrable (fun path ↦ φ (query path) (batch path)) law :=
    integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := batch)
      (C := varianceAggregateSq σ / (n.1 * b.1)) hφ
      hquery.aemeasurable hbatch.aemeasurable hqueryBatch hbatchLaw
      (fun _ _ ↦ sq_nonneg _) (fun x ↦ (hfixed x).1)
      (fun x ↦ (hfixed x).2)
  have hbound : (∫ path, φ (query path) (batch path) ∂law) ≤
      varianceAggregateSq σ / (n.1 * b.1) :=
    integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := query) (Y := batch)
      hφ hquery.aemeasurable hbatch.aemeasurable hqueryBatch hbatchLaw
      hcomp (fun x ↦ (hfixed x).2)
  simpa [φ, query, batch, run, law, P] using ⟨hcomp, hbound⟩

set_option maxHeartbeats 2000000 in
/-- The proof-exact refresh square is independent of its same-round Bernoulli
coin under the weak law-level correction.  The observable is represented as a
kernel of the strict round prefix and the non-coin coordinates of the current
round, so this is a consequence of the canonical iid path law rather than an
extra adaptive-independence premise. -/
theorem onlineProofExact_refresh_error_sq_indep_refresh_of_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A.problem i ((path k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    ProbabilityTheory.IndepFun refreshErrorSq
      (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1) law := by
  classical
  dsimp only
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let refreshBatchLaw := onlineBatchLaw A.problem b
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let roundLaw := coinLaw.prod restLaw
  let prefixLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let batch := fun rest : ((((w : Worker n) → Fin b.1 → Sample w) ×
      ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦ rest.1.1
  let phi := fun (x : Point d)
      (fresh : (i : Worker n) → Fin b.1 → Sample i) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
        stochasticGradient A.problem i (fresh i j) x)) -
      globalGradient (onlineLocalProblem A.problem) x‖ ^ 2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure refreshBatchLaw := by
    unfold refreshBatchLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    unfold coinLaw refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    unfold restLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
    unfold onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure
      (onlineProofExactPathLaw (b := b) (b0 := b0) A))
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let query := fun pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ ↦
    primalStep A.stepSize (prefixState pref)
  let F := fun pref rest ↦ phi (query pref) (batch rest)
  have hprefixLaw : prefixLaw = onlineRoundPrefixLaw A k := by
    unfold prefixLaw onlineRoundPrefixLaw onlineProofExactPathLaw
    simpa [roundLaw, coinLaw, restLaw, refreshBatchLaw,
      differenceBatchLaw, compressionLaw, onlineRoundLaw] using
      (iidStream_prefix_map_eq_infinitePi
        (onlineRoundLaw (b := b) (b0 := b0) A) k).symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [hprefixLaw]
    unfold onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map
      (μ := onlineProofExactPathLaw (b := b) (b0 := b0) A)
      (show AEMeasurable (onlineRoundPrefix
        (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k)
          (onlineProofExactPathLaw (b := b) (b0 := b0) A) from
        (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).aemeasurable)
  have hstate : AEMeasurable prefixState prefixLaw := by
    rw [hprefixLaw]
    simpa [prefixState] using
      onlineProofExactPrefixState_all_aemeasurable_of_lawRegularity
        A x0 hBatch hRegularity fallback k
  have hquery : AEStronglyMeasurable query prefixLaw :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hstate)
      |>.aestronglyMeasurable
  let queryRep := hquery.mk query
  have hqueryRep : Measurable queryRep := hquery.measurable_mk
  have hbatch : Measurable batch := by dsimp [batch]; fun_prop
  have hbatchLaw : Measure.map batch restLaw = refreshBatchLaw := by
    calc
      Measure.map batch restLaw = Measure.map Prod.fst
          (Measure.map Prod.fst restLaw) := by
            rw [MeasureTheory.Measure.map_map measurable_fst measurable_fst]
            rfl
      _ = refreshBatchLaw := by simp [restLaw]
  have hphi : AEStronglyMeasurable (Function.uncurry phi)
      ((Measure.map queryRep prefixLaw).prod refreshBatchLaw) := by
    simpa [phi] using
      onlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
        (b := b) A.problem hRegularity (Measure.map queryRep prefixLaw)
  have hindep : ProbabilityTheory.IndepFun
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        queryRep z.1)
      (fun z ↦ batch z.2) (prefixLaw.prod restLaw) :=
    ProbabilityTheory.indepFun_prod hqueryRep hbatch
  have hqueryMap : Measure.map
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        queryRep z.1) (prefixLaw.prod restLaw) =
      Measure.map queryRep prefixLaw := by
    calc
      _ = Measure.map (queryRep ∘ Prod.fst)
          (prefixLaw.prod restLaw) := rfl
      _ = Measure.map queryRep (Measure.map Prod.fst
          (prefixLaw.prod restLaw)) := by
            rw [MeasureTheory.Measure.map_map hqueryRep measurable_fst]
      _ = _ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hbatchMap : Measure.map
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        batch z.2) (prefixLaw.prod restLaw) = refreshBatchLaw := by
    calc
      _ = Measure.map (batch ∘ Prod.snd)
          (prefixLaw.prod restLaw) := rfl
      _ = Measure.map batch (Measure.map Prod.snd
          (prefixLaw.prod restLaw)) := by
            rw [MeasureTheory.Measure.map_map hbatch measurable_snd]
      _ = Measure.map batch restLaw := by
            rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = refreshBatchLaw := hbatchLaw
  have hrep : AEStronglyMeasurable
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        phi (queryRep z.1) (batch z.2)) (prefixLaw.prod restLaw) := by
    have hc := aestronglyMeasurable_comp_of_indep_product_law
      (P := prefixLaw.prod restLaw)
      (X := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
          queryRep z.1)
      (Y := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
          batch z.2)
      (φ := Function.uncurry phi)
      (hqueryRep.comp measurable_fst).aemeasurable
      (hbatch.comp measurable_snd).aemeasurable
      (inferInstance) (inferInstance) hindep
      (by rw [hqueryMap, hbatchMap]; exact hphi)
    simpa using hc
  have hqueryAE : (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
      ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
      query z.1) =ᵐ[prefixLaw.prod restLaw] (fun z ↦ queryRep z.1) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst
      (μ := prefixLaw) (ν := restLaw)).tendsto_ae hquery.ae_eq_mk
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod restLaw) := by
    refine hrep.congr (hqueryAE.mono ?_)
    intro z hz
    simpa [F] using congrArg (fun x ↦ phi x (batch z.2)) hz.symm
  have hi := iidStream_prefix_current_snd_kernel_indep_fst
    coinLaw restLaw k F hF
  have hcalc : ∀ path : ℕ → OnlineRoundNoise n b b0 Sample Ξ,
      F (fun j : Fin k ↦ path j.1) (path k).2 =
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i ((path k).2.1.1 i j)
              (onlineProofExactProcess A x0 hBatch (k + 1) path).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (onlineProofExactProcess A x0 hBatch (k + 1) path).x‖ ^ 2 := by
    intro path
    have hs := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := path)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ path j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])
    simp only [F, phi, batch, query, prefixState]
    rw [onlineProofExactProcess_succ, hs]
    rfl
  simpa [coinLaw, restLaw, roundLaw, refreshBatchLaw, differenceBatchLaw,
    compressionLaw, onlineProofExactPathLaw, onlineRoundLaw] using
    hi.congr (Filter.Eventually.of_forall hcalc)
      (Filter.Eventually.of_forall fun _ ↦ rfl)

set_option maxHeartbeats 3000000 in
/-- Complete proof-exact Eq. (46) at one time under the literal source
moments, genuine generated-query Assumption 3.2, and the weak law-level
Track-B correction.  The two branch moments are gated by the actual current
Bernoulli refresh coin; current error and step integrability are induction
inputs, while successor error integrability is proved here. -/
theorem online_estimator_recurrence_46_proof_exact_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law (k + 1) ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment P run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
      A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  have hRefresh :=
    onlineProofExact_refresh_error_integrable_and_expectation_le_of_literal_and_lawRegularity
      A x0 hBatch σ hLiteral hRegularity hSmooth.1 k
  have hRefreshIndep :=
    onlineProofExact_refresh_error_sq_indep_refresh_of_lawRegularity
      A x0 hBatch hRegularity k
  have hNonrefresh :=
    onlineProofExact_nonrefresh_branch_moments_of_genuine_assumption32_and_lawRegularity
      A x0 Llocal ℒlocal ω hSmooth hBatch hAssumption32 hRegularity
        hQuantizer k hError hStep
  let residual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem (path k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let refreshError := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
      stochasticGradient A.problem i ((path k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1
  let refreshSq := fun path ↦ ‖refreshError path‖ ^ 2
  let nonrefreshSq := fun path ↦ ‖residual path + innovation path‖ ^ 2
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n ↦
      A.quantizer.apply
        (onlineBatchDifference A.problem (path k).2.1.2 i xN s.x)
        ((path k).2.2 i)
    have hdiffAvg : average (fun i : Worker n ↦
        localGradientDifference P i xN s.x) =
        globalGradient P xN - globalGradient P s.x := by
      rw [globalGradient_eq_averageLocalGradient P hSmooth.1 xN,
        globalGradient_eq_averageLocalGradient P hSmooth.1 s.x]
      unfold averageLocalGradient localGradientDifference average
        SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hinnovationAvg : innovation path =
        average q - average (fun i : Worker n ↦
          localGradientDifference P i xN s.x) := by
      dsimp [innovation, q, xN, s]
      rw [show (run (k + 1) path).x = xN by rfl]
      unfold average SOptLib.finiteUniformAverage
      rw [Finset.sum_sub_distrib, smul_sub]
    have hnext : nextResidual path =
        average (fun i : Worker n ↦
          onlineWorkerEstimator A (onlineDriverOfRoundNoise (path k)) s i) -
          globalGradient P xN := by rfl
    cases h : branch path with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        change average (fun i : Worker n ↦ s.g + q i) -
            globalGradient P xN = residual path + innovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [if_true]
        rw [hnext]
        simp only [onlineWorkerEstimator, onlineDriverOfRoundNoise, branch] at h ⊢
        rw [h]
        rfl
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hbranchMeas : Measurable branch := by dsimp [branch]; fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    calc
      Measure.map branch law = Measure.map Prod.fst
          (Measure.map (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k)
            law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_fst
              · exact measurable_pi_apply k
      _ = Measure.map Prod.fst (onlineRoundLaw A) := by
            rw [show Measure.map
                (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k) law =
                onlineRoundLaw A by
              simpa [law, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = _ := by simp [onlineRoundLaw]
  have htrueMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({true} : Set Bool) = A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
    simp [PMF.bernoulli_apply]
  have hfalseMass :
      (refreshLaw A.refreshProbability A.refresh_admissible).real
          ({false} : Set Bool) = 1 - A.refreshProbability := by
    rw [measureReal_def]
    unfold refreshLaw
    rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
    simp only [PMF.bernoulli_apply, Bool.cond_false]
    let pNN : NNReal :=
      ⟨A.refreshProbability, le_of_lt A.refresh_admissible.1⟩
    have hpNN : pNN ≤ (1 : NNReal) := by exact_mod_cast A.refresh_admissible.2
    change ((1 - pNN : NNReal) : ℝ) = 1 - A.refreshProbability
    rw [NNReal.coe_sub hpNN]
    rfl
  let phiR : ℝ → Bool → ℝ := fun z c ↦ if c then z else 0
  let budgetR : ℝ → ℝ := fun z ↦ A.refreshProbability * z
  let phiN : ℝ → Bool → ℝ := fun z c ↦ if c = false then z else 0
  let budgetN : ℝ → ℝ := fun z ↦ (1 - A.refreshProbability) * z
  have hrefreshInt : Integrable refreshSq law := by
    simpa [refreshSq, refreshError, P, run, law] using hRefresh.1
  have hnonrefreshInt : Integrable nonrefreshSq law := by
    simpa [nonrefreshSq, residual, innovation, P, run, law] using
      hNonrefresh.2.2.2.1
  have hrefreshIndep : ProbabilityTheory.IndepFun refreshSq branch law := by
    simpa [refreshSq, refreshError, branch, P, run, law] using hRefreshIndep
  have hnonrefreshIndep : ProbabilityTheory.IndepFun nonrefreshSq branch law := by
    simpa [nonrefreshSq, residual, innovation, branch, P, run, law] using
      hNonrefresh.2.2.2.2.2
  have hgateRInt : Integrable
      (fun path ↦ phiR (refreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = true} :=
      hbranchMeas (measurableSet_singleton true)
    have hp := Integrable.piecewise hs hrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiR, Set.piecewise] using hp
  have hgateNInt : Integrable
      (fun path ↦ phiN (nonrefreshSq path) (branch path)) law := by
    have hs : MeasurableSet {path | branch path = false} :=
      hbranchMeas (measurableSet_singleton false)
    have hp := Integrable.piecewise hs hnonrefreshInt.integrableOn
      (integrable_const (c := (0 : ℝ))).integrableOn
    simpa [phiN, Set.piecewise] using hp
  have hbudgetRInt : Integrable (fun path ↦ budgetR (refreshSq path)) law := by
    simpa [budgetR] using hrefreshInt.const_mul A.refreshProbability
  have hbudgetNInt : Integrable (fun path ↦ budgetN (nonrefreshSq path)) law := by
    simpa [budgetN] using hnonrefreshInt.const_mul (1 - A.refreshProbability)
  have hgateR :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := refreshSq) (Y := branch) (φ := phiR) (B := budgetR)
      (by exact (show Measurable (Function.uncurry phiR) by
        dsimp [phiR, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton true)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budgetR by dsimp [budgetR]; fun_prop)
        |>.aestronglyMeasurable)
      hrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hrefreshIndep hbranchLaw hgateRInt hbudgetRInt
      (fun z ↦ by
        rw [MeasureTheory.integral_fintype]
        · simp [phiR, budgetR, htrueMass]
        · exact Integrable.of_finite)
  have hgateN :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := refreshLaw A.refreshProbability A.refresh_admissible)
      (X := nonrefreshSq) (Y := branch) (φ := phiN) (B := budgetN)
      (by exact (show Measurable (Function.uncurry phiN) by
        dsimp [phiN, Function.uncurry]
        apply Measurable.ite
        · exact measurable_snd (measurableSet_singleton false)
        · exact measurable_fst
        · exact measurable_const).aestronglyMeasurable)
      (by exact (show Measurable budgetN by dsimp [budgetN]; fun_prop)
        |>.aestronglyMeasurable)
      hnonrefreshInt.aestronglyMeasurable.aemeasurable hbranchMeas.aemeasurable
      hnonrefreshIndep hbranchLaw hgateNInt hbudgetNInt
      (fun z ↦ by
        rw [MeasureTheory.integral_fintype]
        · simp [phiN, budgetN, hfalseMass]
        · exact Integrable.of_finite)
  have hnextSq : ∀ path, ‖nextResidual path‖ ^ 2 =
      phiR (refreshSq path) (branch path) +
        phiN (nonrefreshSq path) (branch path) := by
    intro path
    rw [hdecomp]
    cases hb : branch path <;>
      simp [phiR, phiN, refreshSq, nonrefreshSq]
  have hnextInt : Integrable (fun path ↦ ‖nextResidual path‖ ^ 2) law :=
    (hgateRInt.add hgateNInt).congr
      (Filter.Eventually.of_forall fun path ↦ (hnextSq path).symm)
  have hnextEq : estimatorErrorMoment P run law (k + 1) =
      (∫ path, phiR (refreshSq path) (branch path) ∂law) +
        ∫ path, phiN (nonrefreshSq path) (branch path) ∂law := by
    unfold estimatorErrorMoment
    calc
      (∫ path,
          ‖(run (k + 1) path).g - globalGradient P (run (k + 1) path).x‖ ^ 2
          ∂law) = ∫ path,
            (phiR (refreshSq path) (branch path) +
              phiN (nonrefreshSq path) (branch path)) ∂law := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hnextSq
      _ = _ := integral_add hgateRInt hgateNInt
  refine ⟨?_, hError, hStep, ?_⟩
  · simpa [EstimatorErrorMomentWellDefined, nextResidual, P, run, law] using
      hnextInt
  · rw [hnextEq]
    calc
      (∫ path, phiR (refreshSq path) (branch path) ∂law) +
            ∫ path, phiN (nonrefreshSq path) (branch path) ∂law ≤
          (∫ path, budgetR (refreshSq path) ∂law) +
            ∫ path, budgetN (nonrefreshSq path) ∂law :=
        add_le_add hgateR hgateN
      _ = A.refreshProbability * (∫ path, refreshSq path ∂law) +
          (1 - A.refreshProbability) *
            (∫ path, nonrefreshSq path ∂law) := by
            simp [budgetR, budgetN, integral_const_mul]
      _ ≤ A.refreshProbability * (varianceAggregateSq σ / (n.1 * b.1)) +
          (1 - A.refreshProbability) *
            (estimatorErrorMoment P run law k +
              (1 / (n.1 : ℝ)) *
                (ω * (rootMeanSquare Llocal) ^ 2 +
                  (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
                stepMoment run law k) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
          · simpa [refreshSq, refreshError, P, run, law] using hRefresh.2
          · exact le_of_lt A.refresh_admissible.1
        · apply mul_le_mul_of_nonneg_left
          · simpa [nonrefreshSq, residual, innovation, P, run, law] using
              hNonrefresh.2.2.2.2.1
          · exact sub_nonneg.mpr A.refresh_admissible.2
      _ = (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
        ring

set_option maxHeartbeats 2000000 in
/-- Simultaneous proof-exact component `L²` closure and Eq. (46) history
under literal Assumption 3.3, genuine generated-query Assumption 3.2, and the
weak law-scoped Track-B correction.  The law-level correction supplies only
generated-state measurability; all moment bounds come from the two literal
source assumptions and the quantizer hypothesis. -/
theorem onlineProofExactProcess_scalar_recurrence_components_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
    let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
    AEStronglyMeasurable (fun path ↦ (run k path).x) law ∧
    AEStronglyMeasurable
      (fun path ↦ (run k path).g - globalGradient P (run k path).x) law ∧
    Integrable (fun path ↦ ‖(run k path).x - x0‖ ^ 2) law ∧
    Integrable (fun path ↦ ‖(run k path).g‖ ^ 2) law ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    ∀ j, j < k →
      estimatorErrorMoment P run law (j + 1) ≤
        (1 - A.refreshProbability) / n.1 *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hState (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      onlineProofExactProcess_aemeasurable_of_lawRegularity
        A x0 hBatch hRegularity t
  have hGlobal : IsGradientLipschitz (globalObjective P)
      (rootMeanSquare Llocal) := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hAll : ∀ t,
      AEStronglyMeasurable (fun path ↦ (run t path).x) law ∧
      AEStronglyMeasurable
        (fun path ↦ (run t path).g - globalGradient P (run t path).x) law ∧
      Integrable (fun path ↦ ‖(run t path).x - x0‖ ^ 2) law ∧
      Integrable (fun path ↦ ‖(run t path).g‖ ^ 2) law ∧
      EstimatorErrorMomentWellDefined P run law t ∧
      StepMomentWellDefined run law t ∧
      ∀ j, j < t →
        estimatorErrorMoment P run law (j + 1) ≤
          (1 - A.refreshProbability) / n.1 *
              (ω * (rootMeanSquare Llocal) ^ 2 +
                (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
              stepMoment run law j +
            (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
            A.refreshProbability * varianceAggregateSq σ / (n.1 * b.1) := by
    intro t
    induction t with
    | zero =>
        have hx : AEStronglyMeasurable (fun path ↦ (run 0 path).x) law :=
          ((measurable_state_x d).comp_aemeasurable (hState 0)).aestronglyMeasurable
        have hr : AEStronglyMeasurable
            (fun path ↦ (run 0 path).g - globalGradient P (run 0 path).x) law := by
          have heq : (fun path ↦
              (run 0 path).g - globalGradient P (run 0 path).x) =
              (fun _ ↦ (0 : Point d)) := by
            funext path
            change globalGradient P x0 - globalGradient P x0 = 0
            simp
          rw [heq]
          exact aestronglyMeasurable_const
        have hxl2 : Integrable (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) law := by
          have heq : (fun path ↦ ‖(run 0 path).x - x0‖ ^ 2) =
              (fun _ ↦ (0 : ℝ)) := by
            funext path
            change ‖x0 - x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (μ := law) (c := (0 : ℝ))
        have hgl2 : Integrable (fun path ↦ ‖(run 0 path).g‖ ^ 2) law := by
          have heq : (fun path ↦ ‖(run 0 path).g‖ ^ 2) =
              (fun _ ↦ ‖globalGradient P x0‖ ^ 2) := by
            funext path
            rfl
          rw [heq]
          exact integrable_const (μ := law) (c := ‖globalGradient P x0‖ ^ 2)
        have he : EstimatorErrorMomentWellDefined P run law 0 := by
          rw [EstimatorErrorMomentWellDefined]
          have heq : (fun path ↦
              ‖(run 0 path).g - globalGradient P (run 0 path).x‖ ^ 2) =
              (fun _ ↦ (0 : ℝ)) := by
            funext path
            change ‖globalGradient P x0 - globalGradient P x0‖ ^ 2 = 0
            simp
          rw [heq]
          exact integrable_const (μ := law) (c := (0 : ℝ))
        have hs : StepMomentWellDefined run law 0 := by
          have heq : (fun path ↦ ‖(run (0 + 1) path).x - (run 0 path).x‖ ^ 2) =
              (fun _ ↦ ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2) := by
            funext path
            change ‖(x0 - (A.stepSize : ℝ) • globalGradient P x0) - x0‖ ^ 2 = _
            congr 2
            rw [neg_smul]
            abel
          rw [StepMomentWellDefined, heq]
          exact integrable_const (μ := law)
            (c := ‖(-(A.stepSize : ℝ)) • globalGradient P x0‖ ^ 2)
        refine ⟨hx, hr, hxl2, hgl2, he, hs, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        have hRec :=
          online_estimator_recurrence_46_proof_exact_of_literal_and_lawRegularity
            A x0 Llocal ℒlocal σ ω hSmooth hLiteral hQuantizer hBatch
              hAssumption32 hRegularity t ih.2.2.2.2.1 ih.2.2.2.2.2.1
        have hxNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).x) law :=
          ((measurable_state_x d).comp_aemeasurable
            (hState (t + 1))).aestronglyMeasurable
        have hgNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).g) law :=
          ((measurable_state_g d).comp_aemeasurable
            (hState (t + 1))).aestronglyMeasurable
        have hgradNext : AEStronglyMeasurable
            (fun path ↦ globalGradient P (run (t + 1) path).x) law :=
          ((measurable_gradient (globalObjective P)).comp_aemeasurable
            hxNext.aemeasurable).aestronglyMeasurable
        have hrNext : AEStronglyMeasurable
            (fun path ↦ (run (t + 1) path).g -
              globalGradient P (run (t + 1) path).x) law :=
          hgNext.sub hgradNext
        have hxl2Next : Integrable
            (fun path ↦ ‖(run (t + 1) path).x - x0‖ ^ 2) law := by
          have hg : AEStronglyMeasurable (fun path ↦ (run t path).g) law := by
            have hsum := ih.2.1.add
              (((measurable_gradient (globalObjective P)).comp_aemeasurable
                ih.1.aemeasurable).aestronglyMeasurable)
            refine hsum.congr (Filter.Eventually.of_forall ?_)
            intro path
            change ((run t path).g - globalGradient P (run t path).x) +
              globalGradient P (run t path).x = (run t path).g
            abel
          have h := integrable_sq_norm_sub_smul_sub_const_of_l2
            (fun path ↦ (run t path).x) (fun path ↦ (run t path).g)
            x0 (A.stepSize : ℝ) ih.1 hg ih.2.2.1 ih.2.2.2.1
          simpa [run, onlineProofExactProcess_succ, onlineStep,
            primalStep_eq] using h
        have hglobalNext : Integrable
            (fun path ↦ ‖globalGradient P (run (t + 1) path).x‖ ^ 2) law := by
          apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
            x0 (globalGradient P) (rootMeanSquare Llocal)
              (fun path ↦ (run (t + 1) path).x) hxNext
          · simpa [norm_sub_rev] using hxl2Next
          · intro x y
            exact hGlobal.2 y x
        have hgl2Next : Integrable
            (fun path ↦ ‖(run (t + 1) path).g‖ ^ 2) law := by
          have hadd := integrable_sq_norm_add hrNext hgradNext
            (by simpa [EstimatorErrorMomentWellDefined, P, run, law] using hRec.1)
            hglobalNext
          apply hadd.congr
          filter_upwards [] with path
          congr 2
          abel
        have hsNext : StepMomentWellDefined run law (t + 1) := by
          have hscaled := integrable_sq_norm_const_smul
            (-(A.stepSize : ℝ)) hgl2Next
          simpa [StepMomentWellDefined, run, onlineProofExactProcess_succ,
            onlineStep, primalStep_eq] using hscaled
        have hHistory : ∀ j, j < t + 1 →
            estimatorErrorMoment P run law (j + 1) ≤
              (1 - A.refreshProbability) / n.1 *
                  (ω * (rootMeanSquare Llocal) ^ 2 +
                    (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
                  stepMoment run law j +
                (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
                A.refreshProbability * varianceAggregateSq σ /
                  (n.1 * b.1) := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjt | rfl
          · exact ih.2.2.2.2.2.2 j hjt
          · exact hRec.2.2.2
        exact ⟨hxNext, hrNext, hxl2Next, hgl2Next, hRec.1, hsNext,
          hHistory⟩
  exact hAll k

/-- The source moment assumptions imply a.e. measurability of the actual
executable Algorithm 3 message.  The proof uses the generated query and the
same fresh difference minibatch as `onlineProcess`; no global kernel
measurability is introduced. -/
theorem onlineWorkerDifferenceMessage_aestronglyMeasurable_of_source
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (onlineWorkerDifferenceMessage A x0 hBatch k i) (onlinePathLaw A) := by
  classical
  let P := onlineLocalProblem A.problem
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let query := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((run (k + 1) path).x, (run k path).x)
  let noise := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((path.2 k).2.1.2, (path.2 k).2.2)
  let batch := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (noise path).1
  let batchLaw := onlineBatchLaw A.problem b0
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hc := online_executable_scalar_components_all
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k
  have hx : AEStronglyMeasurable (fun path => (run k path).x) law := by
    simpa [run, law, P] using hc.1
  have hresidual : AEStronglyMeasurable
      (fun path => (run k path).g - globalGradient P (run k path).x) law := by
    simpa [run, law, P] using hc.2.1
  have hgrad : AEStronglyMeasurable
      (fun path => globalGradient P (run k path).x) law :=
    ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path => (run k path).g) law := by
    have hsum := hresidual.add hgrad
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro path
    change (run k path).g - globalGradient P (run k path).x +
      globalGradient P (run k path).x = (run k path).g
    abel
  have hxNext : AEStronglyMeasurable
      (fun path => (run (k + 1) path).x) law := by
    have hstep := hx.sub (hg.const_smul (A.stepSize : ℝ))
    simpa [run, onlineProcess_succ, onlineStep, primalStep_eq] using hstep
  have hquery : AEStronglyMeasurable query law := hxNext.prodMk hx
  have hfresh := onlineExecutable_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hqueryBatch : ProbabilityTheory.IndepFun query batch law := by
    have h := hfresh.2.1.comp measurable_fst measurable_fst
    simpa [query, batch, noise, run, P, law] using h
  have hnoise : Measurable noise := by dsimp [noise]; fun_prop
  have hbatch : Measurable batch := measurable_fst.comp hnoise
  have hnoiseLaw : Measure.map noise law =
      batchLaw.prod (workerCompressionLaw (n := n) A.quantizer) := by
    simpa [noise, law, batchLaw, onlineDifferenceCompressionLaw] using hfresh.2.2
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map Prod.fst (Measure.map noise law) := by
        simpa [batch, Function.comp_apply] using
          (Measure.map_map measurable_fst hnoise (μ := law)).symm
      _ = Measure.map Prod.fst
          (batchLaw.prod (workerCompressionLaw A.quantizer)) := by rw [hnoiseLaw]
      _ = batchLaw := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hkernel :=
    onlineBatchDifference_product_aestronglyMeasurable_of_variance
      (b0 := b0) A.problem σ hVariance (Measure.map query law)
        Prod.fst Prod.snd measurable_fst.aestronglyMeasurable
        measurable_snd.aestronglyMeasurable i
  have hcomp := aestronglyMeasurable_comp_of_indep_product_law
    hquery.aemeasurable hbatch.aemeasurable
      (inferInstance : SigmaFinite (Measure.map query law))
      (inferInstance : SigmaFinite (Measure.map batch law)) hqueryBatch
      (by simpa [hbatchLaw] using hkernel)
  simpa [onlineWorkerDifferenceMessage, query, batch, noise, run,
    onlineProcess_succ] using hcomp

set_option maxHeartbeats 2000000 in
/-- The measurable representative of the actual online difference message is
independent of its same-round compressor coordinate, and its resulting support
is independent of the refresh coin.  Both statements are consequences of the
canonical round product law and strict-past freshness, not extra source
assumptions. -/
theorem onlineWorkerMessageRepresentative_independences_of_source
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (k : ℕ) (i : Worker n) :
    let hm := onlineWorkerDifferenceMessage_aestronglyMeasurable_of_source
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k i
    ProbabilityTheory.IndepFun
        (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i))
        (onlineWorkerCompressionSample k i) (onlinePathLaw A) ∧
      ProbabilityTheory.IndepFun
        (fun path => quantizerNonzeroCount A.quantizer
          (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
          (onlineWorkerCompressionSample k i path))
        (onlineRefreshBranch k) (onlinePathLaw A) := by
  classical
  let P := onlineLocalProblem A.problem
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let query := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((run (k + 1) path).x, (run k path).x)
  let noise := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((path.2 k).2.1.2, (path.2 k).2.2)
  let batch := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (noise path).1
  let row := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (noise path).2
  let sample := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => row path i
  let batchLaw := onlineBatchLaw A.problem b0
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    unfold rowLaw workerCompressionLaw
    infer_instance
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  haveI : IsProbabilityMeasure coinLaw := by
    unfold coinLaw refreshLaw
    infer_instance
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  let hm := onlineWorkerDifferenceMessage_aestronglyMeasurable_of_source
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k i
  have hc := online_executable_scalar_components_all
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k
  have hx : AEStronglyMeasurable (fun path => (run k path).x) law := by
    simpa [run, law, P] using hc.1
  have hresidual : AEStronglyMeasurable
      (fun path => (run k path).g - globalGradient P (run k path).x) law := by
    simpa [run, law, P] using hc.2.1
  have hgrad : AEStronglyMeasurable
      (fun path => globalGradient P (run k path).x) law :=
    ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path => (run k path).g) law := by
    have hsum := hresidual.add hgrad
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro path
    change (run k path).g - globalGradient P (run k path).x +
      globalGradient P (run k path).x = (run k path).g
    abel
  have hxNext : AEStronglyMeasurable
      (fun path => (run (k + 1) path).x) law := by
    have hstep := hx.sub (hg.const_smul (A.stepSize : ℝ))
    simpa [run, onlineProcess_succ, onlineStep, primalStep_eq] using hstep
  have hquery : AEStronglyMeasurable query law := hxNext.prodMk hx
  let query' := hquery.mk query
  have hquery' : Measurable query' := hquery.measurable_mk
  have hfresh := onlineExecutable_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hqueryNoise : ProbabilityTheory.IndepFun query noise law := by
    have h := hfresh.2.1.comp measurable_fst measurable_id
    simpa [query, noise, run, P, law] using h
  have hqueryNoise' : ProbabilityTheory.IndepFun query' noise law := by
    apply hqueryNoise.congr hquery.ae_eq_mk
      (Filter.Eventually.of_forall fun _ => rfl)
  have hnoise : Measurable noise := by dsimp [noise]; fun_prop
  have hbatch : Measurable batch := measurable_fst.comp hnoise
  have hrow : Measurable row := measurable_snd.comp hnoise
  have hsample : Measurable sample := (measurable_pi_apply i).comp hrow
  have hnoiseLaw : Measure.map noise law = batchLaw.prod rowLaw := by
    simpa [noise, law, batchLaw, rowLaw, onlineDifferenceCompressionLaw] using
      hfresh.2.2
  have hqueryBatchRow : ProbabilityTheory.IndepFun
      (fun path => (query' path, batch path)) row law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law batchLaw rowLaw
      query' batch row hquery' hbatch hrow hqueryNoise' hnoiseLaw
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map Prod.fst (Measure.map noise law) := by
        simpa [batch, Function.comp_apply] using
          (Measure.map_map measurable_fst hnoise (μ := law)).symm
      _ = Measure.map Prod.fst (batchLaw.prod rowLaw) := by rw [hnoiseLaw]
      _ = batchLaw := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  let kernel := fun z : (Point d × Point d) ×
      ((w : Worker n) → Fin b0.1 → Sample w) =>
    onlineBatchDifference A.problem z.2 i z.1.1 z.1.2
  have hkernel : AEStronglyMeasurable kernel
      ((Measure.map query' law).prod batchLaw) := by
    simpa [kernel] using
      (onlineBatchDifference_product_aestronglyMeasurable_of_variance
        (b0 := b0) A.problem σ hVariance (Measure.map query' law)
          Prod.fst Prod.snd measurable_fst.aestronglyMeasurable
          measurable_snd.aestronglyMeasurable i)
  let kernel' := hkernel.mk kernel
  have hkernel' : Measurable kernel' := hkernel.measurable_mk
  let joined := fun path => (query' path, batch path)
  have hjoined : Measurable joined := hquery'.prodMk hbatch
  have hqueryBatch : ProbabilityTheory.IndepFun query' batch law :=
    hqueryNoise'.comp measurable_id measurable_fst
  have hjoinedLaw : Measure.map joined law =
      (Measure.map query' law).prod batchLaw := by
    calc
      Measure.map joined law =
          (Measure.map query' law).prod (Measure.map batch law) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hquery'.aemeasurable hbatch.aemeasurable).1 hqueryBatch
      _ = (Measure.map query' law).prod batchLaw := by rw [hbatchLaw]
  have hjoinedQmp : Measure.QuasiMeasurePreserving joined law
      ((Measure.map query' law).prod batchLaw) :=
    ⟨hjoined, by rw [hjoinedLaw]⟩
  have hkernelMk := hjoinedQmp.tendsto_ae hkernel.ae_eq_mk
  have hcalcMessage : (fun path => kernel' (joined path)) =ᵐ[law]
      onlineWorkerDifferenceMessage A x0 hBatch k i := by
    filter_upwards [hkernelMk, hquery.ae_eq_mk] with path hk hq
    calc
      kernel' (joined path) = kernel (query' path, batch path) := hk.symm
      _ = kernel (query path, batch path) :=
        congrArg (fun q => kernel (q, batch path)) hq.symm
      _ = onlineWorkerDifferenceMessage A x0 hBatch k i path := by
        simp [kernel, query, batch, noise, onlineWorkerDifferenceMessage, run,
          onlineProcess_succ, onlineStep, primalStep_eq]
  have hcalcIndep : ProbabilityTheory.IndepFun
      (fun path => kernel' (joined path)) sample law := by
    simpa [joined, sample] using
      hqueryBatchRow.comp hkernel' (measurable_pi_apply i)
  have hmessageIndep : ProbabilityTheory.IndepFun
      (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i)) sample law := by
    apply hcalcIndep.congr
    · exact hcalcMessage.trans hm.ae_eq_mk
    · exact Filter.Eventually.of_forall fun _ => rfl
  have hfirst : ProbabilityTheory.IndepFun
      (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i))
      (onlineWorkerCompressionSample k i) (onlinePathLaw A) := by
    simpa [sample, row, noise, onlineWorkerCompressionSample, law] using
      hmessageIndep
  let current := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k
  let rest := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2
  let coin := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.1
  let restPath := fun path => rest (current path)
  let branch := fun path => coin (current path)
  let restLaw := ((onlineBatchLaw A.problem b).prod batchLaw).prod rowLaw
  haveI : IsProbabilityMeasure restLaw := by
    unfold restLaw
    infer_instance
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hrestPath : Measurable restPath := measurable_snd.comp hcurrent
  have hbranch : Measurable branch := measurable_fst.comp hcurrent
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    have h := hfresh.1.comp measurable_fst measurable_id
    simpa [query, current, run, P, law] using h
  have hqueryCurrent' : ProbabilityTheory.IndepFun query' current law := by
    apply hqueryCurrent.congr hquery.ae_eq_mk
      (Filter.Eventually.of_forall fun _ => rfl)
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ => stream k)
          (Measure.map Prod.snd law) := by
        rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
        rfl
      _ = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ => stream k)
          (SOptLib.iidStreamLaw roundLaw) := by
        rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
          dsimp [law, roundLaw, onlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hqueryPair : ProbabilityTheory.IndepFun query'
      (fun path => (restPath path, branch path)) law := by
    simpa [restPath, branch, rest, coin, current] using
      hqueryCurrent'.comp measurable_id (measurable_snd.prodMk measurable_fst)
  have hpairLaw : Measure.map (fun path => (restPath path, branch path)) law =
      restLaw.prod coinLaw := by
    calc
      Measure.map (fun path => (restPath path, branch path)) law =
          Measure.map Prod.swap (Measure.map current law) := by
        rw [Measure.map_map measurable_swap hcurrent]
        rfl
      _ = Measure.map Prod.swap roundLaw := by rw [hcurrentLaw]
      _ = Measure.map Prod.swap (coinLaw.prod restLaw) := by rfl
      _ = restLaw.prod coinLaw := MeasureTheory.Measure.prod_swap
  have hqueryRestBranch : ProbabilityTheory.IndepFun
      (fun path => (query' path, restPath path)) branch law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law restLaw coinLaw
      query' restPath branch hquery' hrestPath hbranch hqueryPair hpairLaw
  let supportKernel : (Point d × Point d) ×
      ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) → ℝ :=
    fun z => quantizerNonzeroCount A.quantizer
      (kernel' (z.1, z.2.1.2)) (z.2.2 i)
  have hsupportKernel : Measurable supportKernel := by
    have hdiffBatch : Measurable (fun z : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
        z.2.1.2) := by fun_prop
    have hmessage : Measurable (fun z : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
        kernel' (z.1, z.2.1.2)) :=
      hkernel'.comp (measurable_fst.prodMk hdiffBatch)
    have hsampleRest : Measurable (fun z : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
        z.2.2 i) := by fun_prop
    simpa only [supportKernel] using
      (quantizerNonzeroCount_joint_measurable A.quantizer).comp
        (hmessage.prodMk hsampleRest)
  have hsupportCalc : ProbabilityTheory.IndepFun
      (fun path => supportKernel (query' path, restPath path)) branch law := by
    simpa only [Function.comp_apply] using
      hqueryRestBranch.comp hsupportKernel measurable_id
  have hsupportAE : (fun path => supportKernel (query' path, restPath path)) =ᵐ[law]
      (fun path => quantizerNonzeroCount A.quantizer
        (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
        (onlineWorkerCompressionSample k i path)) := by
    filter_upwards [hcalcMessage, hm.ae_eq_mk] with path hcalc hmk
    change quantizerNonzeroCount A.quantizer
        (kernel' (joined path)) (sample path) =
      quantizerNonzeroCount A.quantizer
        (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
        (sample path)
    rw [hcalc, hmk]
  have hsecond : ProbabilityTheory.IndepFun
      (fun path => quantizerNonzeroCount A.quantizer
        (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
        (onlineWorkerCompressionSample k i path))
      (onlineRefreshBranch k) (onlinePathLaw A) := by
    apply hsupportCalc.congr hsupportAE
      (Filter.Eventually.of_forall fun _ => rfl)
  exact ⟨hfirst, hsecond⟩

/-- All law-scoped regularity needed for executable online communication is
derived from the source smoothness, variance, quantizer, and average-smoothness
hypotheses. -/
theorem onlineCommunicationAELawRegularity_of_source
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal) :
    OnlineCommunicationAELawRegularity A x0 hBatch := by
  let hm := fun k i => onlineWorkerDifferenceMessage_aestronglyMeasurable_of_source
    A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
      hAverageSmooth k i
  refine ⟨hm, ?_, ?_⟩
  · intro k i
    exact (onlineWorkerMessageRepresentative_independences_of_source
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k i).1
  · intro k i
    exact (onlineWorkerMessageRepresentative_independences_of_source
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer hBatch
        hAverageSmooth k i).2

/-- The a.e.-law interface suffices for the density bound on the *original*
actual-message support observable.  The proof performs the probabilistic
calculation on a measurable representative and then transfers integrability
and the integral back by a.e. congruence. -/
theorem onlineWorkerRoundSupport_integrable_and_le_expectedDensity_of_ae_law_regularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hRegularity : OnlineCommunicationAELawRegularity A x0 hBatch)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    Integrable (onlineWorkerRoundSupport A x0 hBatch k i)
        (onlinePathLaw A) ∧
      (∫ path, onlineWorkerRoundSupport A x0 hBatch k i path
          ∂onlinePathLaw A) ≤ expectedDensity A.quantizer := by
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let message := onlineWorkerDifferenceMessage A x0 hBatch k i
  let sample := onlineWorkerCompressionSample
    (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k i
  let hm : AEStronglyMeasurable message law :=
    hRegularity.message_aestronglyMeasurable k i
  let message' := hm.mk message
  have hmessage' : Measurable message' := hm.measurable_mk
  have hsample : Measurable sample := by
    change Measurable (fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).2.2 i)
    fun_prop
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsampleLaw : Measure.map sample law = A.quantizer.law := by
    let current := fun path :
        ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k
    have hcurrent : Measurable current := by dsimp [current]; fun_prop
    have hcurrentLaw : Measure.map current law = onlineRoundLaw A := by
      calc
        Measure.map current law = Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ => stream k)
            (Measure.map Prod.snd law) := by
          rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
          rfl
        _ = Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ => stream k)
            (SOptLib.iidStreamLaw (onlineRoundLaw A)) := by
          rw [show Measure.map Prod.snd law =
              SOptLib.iidStreamLaw (onlineRoundLaw A) by
            dsimp [law, onlinePathLaw]
            rw [Measure.map_snd_prod, measure_univ, one_smul]]
        _ = onlineRoundLaw A :=
          SOptLib.iidStreamLaw_map_eval (onlineRoundLaw A) k
    have hcompressionLaw : Measure.map
        (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.2)
        (onlineRoundLaw A) = workerCompressionLaw A.quantizer := by
      calc
        Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.2)
            (onlineRoundLaw A) =
            Measure.map Prod.snd
              (Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ =>
                (z.2.1.2, z.2.2)) (onlineRoundLaw A)) := by
          rw [Measure.map_map measurable_snd (by fun_prop)]
          rfl
        _ = Measure.map Prod.snd (onlineDifferenceCompressionLaw A) := by
          rw [onlineRoundLaw_differenceCompression_marginal]
        _ = workerCompressionLaw A.quantizer := by
          unfold onlineDifferenceCompressionLaw
          rw [Measure.map_snd_prod, measure_univ, one_smul]
    calc
      Measure.map sample law = Measure.map (fun row : Worker n → Ξ => row i)
          (Measure.map (fun path => (current path).2.2) law) := by
        rw [Measure.map_map (measurable_pi_apply i) (by fun_prop)]
        rfl
      _ = Measure.map (fun row : Worker n → Ξ => row i)
          (Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2.2)
            (Measure.map current law)) := by
        rw [Measure.map_map (by fun_prop) hcurrent]
        rfl
      _ = Measure.map (fun row : Worker n → Ξ => row i)
          (workerCompressionLaw A.quantizer) := by
        rw [hcurrentLaw, hcompressionLaw]
      _ = A.quantizer.law :=
        workerCompressionLaw_component_marginal A.quantizer i
  have hrep := adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
    law hQ message' sample hmessage' hsample
      (hRegularity.messageRepresentative_indep_compression k i) hsampleLaw
  have hae : onlineWorkerRoundSupport A x0 hBatch k i =ᵐ[law]
      fun path => quantizerNonzeroCount A.quantizer
        (message' path) (sample path) := by
    filter_upwards [hm.ae_eq_mk] with path hp
    exact congrArg
      (fun v => quantizerNonzeroCount A.quantizer v (sample path)) hp
  refine ⟨hrep.1.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae]
  exact hrep.2

/-- A global stochastic-gradient kernel realization is sufficient for the
narrow generated-cost measurability contract.  This implication preserves the
older conditional interface without making the stronger premise part of the
measured-cost statement. -/
theorem onlineCostMeasurability_of_kernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0) :
    OnlineCostMeasurability A x0 hBatch := by
  refine ⟨onlineProcess_measurable_of_kernel A hKernel x0 hBatch, ?_⟩
  intro i
  exact onlineBatchDifference_joint_measurable_of_kernel A.problem hKernel i

/-- The actual executable Algorithm 3 non-refresh message has expected support
at most `expectedDensity` on the full sampled-initializer experiment. -/
theorem onlineWorkerRoundSupport_integrable_and_le_expectedDensity_of_cost_measurability
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hCostMeas : OnlineCostMeasurability A x0 hBatch)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let message := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      onlineBatchDifference A.problem (path.2 k).2.1.2 i
        (primalStep A.stepSize (run k path)) (run k path).x
    let sample := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).2.2 i
    Integrable (fun path => quantizerNonzeroCount A.quantizer
        (message path) (sample path)) (onlinePathLaw A) ∧
      (∫ path, quantizerNonzeroCount A.quantizer
          (message path) (sample path) ∂onlinePathLaw A) ≤
        expectedDensity A.quantizer := by
  let P := onlineLocalProblem A.problem
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let query := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((run (k + 1) path).x, (run k path).x)
  let noise := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((path.2 k).2.1.2, (path.2 k).2.2)
  let batch := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (noise path).1
  let row := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (noise path).2
  let messageKernel := fun z : (Point d × Point d) ×
      ((w : Worker n) → Fin b0.1 → Sample w) =>
    onlineBatchDifference A.problem z.2 i z.1.1 z.1.2
  let message := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    messageKernel (query path, batch path)
  let sample := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => row path i
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hrun (t : ℕ) : Measurable (run t) := by
    simpa [run] using hCostMeas.process t
  have hx : AEStronglyMeasurable (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hrun k)).aestronglyMeasurable
  have hresidual : AEStronglyMeasurable
      (fun path => (run k path).g - globalGradient P (run k path).x) law :=
    (((measurable_state_g d).comp (hrun k)).sub
      ((measurable_gradient (globalObjective P)).comp
        ((measurable_state_x d).comp (hrun k)))).aestronglyMeasurable
  have hfresh := onlineExecutable_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hquery : Measurable query :=
    ((measurable_state_x d).comp (hrun (k + 1))).prodMk
      ((measurable_state_x d).comp (hrun k))
  have hnoise : Measurable noise := by dsimp [noise]; fun_prop
  have hbatch : Measurable batch := measurable_fst.comp hnoise
  have hrow : Measurable row := measurable_snd.comp hnoise
  have hsample : Measurable sample := (measurable_pi_apply i).comp hrow
  have hqueryNoise : ProbabilityTheory.IndepFun query noise law := by
    have h := hfresh.2.1.comp measurable_fst measurable_id
    simpa [query, noise, run, P, law] using h
  have hnoiseLaw : Measure.map noise law =
      (onlineBatchLaw A.problem b0).prod
        (workerCompressionLaw (n := n) A.quantizer) := by
    simpa [noise, law, onlineDifferenceCompressionLaw] using hfresh.2.2
  have hqueryBatchRow : ProbabilityTheory.IndepFun
      (fun path => (query path, batch path)) row law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law
      (onlineBatchLaw A.problem b0) (workerCompressionLaw A.quantizer)
      query batch row hquery hbatch hrow hqueryNoise hnoiseLaw
  have hmessageKernel : Measurable messageKernel := by
    simpa [messageKernel] using hCostMeas.difference i
  have hmessage : Measurable message :=
    hmessageKernel.comp (hquery.prodMk hbatch)
  have hindep : ProbabilityTheory.IndepFun message sample law := by
    simpa [message, sample] using
      hqueryBatchRow.comp hmessageKernel (measurable_pi_apply i)
  have hsampleLaw : Measure.map sample law = A.quantizer.law := by
    calc
      Measure.map sample law = Measure.map (fun ξ : Worker n → Ξ => ξ i)
          (Measure.map row law) := by
        simpa [sample, Function.comp_apply] using
          (Measure.map_map (measurable_pi_apply i) hrow (μ := law)).symm
      _ = Measure.map (fun ξ : Worker n → Ξ => ξ i)
          (workerCompressionLaw A.quantizer) := by
        rw [show Measure.map row law = workerCompressionLaw A.quantizer by
          calc
            Measure.map row law = Measure.map Prod.snd (Measure.map noise law) := by
              simpa [row, Function.comp_apply] using
                (Measure.map_map measurable_snd hnoise (μ := law)).symm
            _ = Measure.map Prod.snd
                ((onlineBatchLaw A.problem b0).prod
                  (workerCompressionLaw A.quantizer)) := by rw [hnoiseLaw]
            _ = workerCompressionLaw A.quantizer := by
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = A.quantizer.law :=
        workerCompressionLaw_component_marginal A.quantizer i
  have hs := adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
    law hQ message sample hmessage hsample hindep hsampleLaw
  simpa [message, messageKernel, query, batch, noise, row, sample, run, law,
    onlineProcess_succ] using hs

/-- Compatibility form of the round-support theorem under the older global
kernel premise. -/
theorem onlineWorkerRoundSupport_integrable_and_le_expectedDensity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
    let message := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      onlineBatchDifference A.problem (path.2 k).2.1.2 i
        (primalStep A.stepSize (run k path)) (run k path).x
    let sample := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).2.2 i
    Integrable (fun path => quantizerNonzeroCount A.quantizer
        (message path) (sample path)) (onlinePathLaw A) ∧
      (∫ path, quantizerNonzeroCount A.quantizer
          (message path) (sample path) ∂onlinePathLaw A) ≤
        expectedDensity A.quantizer := by
  exact onlineWorkerRoundSupport_integrable_and_le_expectedDensity_of_cost_measurability
    A x0 hBatch (onlineCostMeasurability_of_kernel A hKernel x0 hBatch) hQ k i

/-- A measurable scalar observable of the executable Algorithm 3 query and the
non-coin coordinates of the same round is independent of the refresh coin. -/
theorem online_query_rest_kernel_indep_refresh_of_cost_measurability
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hCostMeas : OnlineCostMeasurability A x0 hBatch) (k : ℕ)
    (F : (Point d × Point d) ×
      ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) → ℝ)
    (hF : Measurable F) :
    ProbabilityTheory.IndepFun
      (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
        F (((onlineProcess A x0 hBatch (k + 1) path).x,
            (onlineProcess A x0 hBatch k path).x), (path.2 k).2))
      (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).1)
      (onlinePathLaw A) := by
  let P := onlineLocalProblem A.problem
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let query := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
    ((run (k + 1) path).x, (run k path).x)
  let current := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k
  let rest := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.2
  let coin := fun z : OnlineRoundNoise n b b0 Sample Ξ => z.1
  let restPath := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => rest (current path)
  let branch := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => coin (current path)
  let restLaw := ((onlineBatchLaw A.problem b).prod
    (onlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hrun (t : ℕ) : Measurable (run t) := by
    simpa [run] using hCostMeas.process t
  have hx : AEStronglyMeasurable (fun path => (run k path).x) law :=
    ((measurable_state_x d).comp (hrun k)).aestronglyMeasurable
  have hresidual : AEStronglyMeasurable
      (fun path => (run k path).g - globalGradient P (run k path).x) law :=
    (((measurable_state_g d).comp (hrun k)).sub
      ((measurable_gradient (globalObjective P)).comp
        ((measurable_state_x d).comp (hrun k)))).aestronglyMeasurable
  have hfresh := onlineExecutable_nonrefreshParameter_indep_noise_of_components
    A x0 hBatch k hx hresidual
  have hquery : Measurable query :=
    ((measurable_state_x d).comp (hrun (k + 1))).prodMk
      ((measurable_state_x d).comp (hrun k))
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hrest : Measurable rest := measurable_snd
  have hcoin : Measurable coin := measurable_fst
  have hrestPath : Measurable restPath := hrest.comp hcurrent
  have hbranch : Measurable branch := hcoin.comp hcurrent
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    have h := hfresh.1.comp measurable_fst measurable_id
    simpa [query, current, run, P, law] using h
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ => stream k)
          (Measure.map Prod.snd law) := by
        rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
        rfl
      _ = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ => stream k)
          (SOptLib.iidStreamLaw roundLaw) := by
        rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
          dsimp [law, roundLaw, onlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hqueryPair : ProbabilityTheory.IndepFun query
      (fun path => (restPath path, branch path)) law := by
    simpa [restPath, branch, rest, coin, current] using
      hqueryCurrent.comp measurable_id
        (measurable_snd.prodMk measurable_fst)
  have hpairLaw : Measure.map (fun path => (restPath path, branch path)) law =
      restLaw.prod coinLaw := by
    calc
      Measure.map (fun path => (restPath path, branch path)) law =
          Measure.map Prod.swap (Measure.map current law) := by
        rw [Measure.map_map measurable_swap hcurrent]
        rfl
      _ = Measure.map Prod.swap roundLaw := by rw [hcurrentLaw]
      _ = Measure.map Prod.swap (coinLaw.prod restLaw) := by
        congr 1
      _ = restLaw.prod coinLaw := MeasureTheory.Measure.prod_swap
  have hjoined : ProbabilityTheory.IndepFun
      (fun path => (query path, restPath path)) branch law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law restLaw coinLaw
      query restPath branch hquery hrestPath hbranch hqueryPair hpairLaw
  simpa [query, restPath, branch, rest, coin, current, run, law] using
    hjoined.comp hF measurable_id

/-- The former global generated-kernel contract implies the exact
law-scoped message regularity.  This is a one-way compatibility result: the
new contract does not recover global process or difference-kernel
measurability. -/
theorem onlineCommunicationLawRegularity_of_costMeasurability
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hCostMeas : OnlineCostMeasurability A x0 hBatch) :
    OnlineCommunicationLawRegularity A x0 hBatch := by
  classical
  let P := onlineLocalProblem A.problem
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hrun (t : ℕ) : Measurable (run t) := by
    simpa [run] using hCostMeas.process t
  refine ⟨?_, ?_, ?_⟩
  · intro k i
    have hquery : Measurable (fun path =>
        (primalStep A.stepSize (run k path), (run k path).x)) :=
      ((measurable_primalStep A.stepSize).comp (hrun k)).prodMk
        ((measurable_state_x d).comp (hrun k))
    have hbatch : Measurable (fun path :
        ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
        (path.2 k).2.1.2) := by fun_prop
    simpa [onlineWorkerDifferenceMessage, run] using
      (hCostMeas.difference i).comp (hquery.prodMk hbatch)
  · intro k i
    let query := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      ((run (k + 1) path).x, (run k path).x)
    let noise := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      ((path.2 k).2.1.2, (path.2 k).2.2)
    let batch := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (noise path).1
    let row := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (noise path).2
    let messageKernel := fun z : (Point d × Point d) ×
        ((w : Worker n) → Fin b0.1 → Sample w) =>
      onlineBatchDifference A.problem z.2 i z.1.1 z.1.2
    have hx : AEStronglyMeasurable (fun path => (run k path).x) law :=
      ((measurable_state_x d).comp (hrun k)).aestronglyMeasurable
    have hresidual : AEStronglyMeasurable
        (fun path => (run k path).g - globalGradient P (run k path).x) law :=
      (((measurable_state_g d).comp (hrun k)).sub
        ((measurable_gradient (globalObjective P)).comp
          ((measurable_state_x d).comp (hrun k)))).aestronglyMeasurable
    have hfresh := onlineExecutable_nonrefreshParameter_indep_noise_of_components
      A x0 hBatch k hx hresidual
    have hquery : Measurable query :=
      ((measurable_state_x d).comp (hrun (k + 1))).prodMk
        ((measurable_state_x d).comp (hrun k))
    have hnoise : Measurable noise := by dsimp [noise]; fun_prop
    have hbatch : Measurable batch := measurable_fst.comp hnoise
    have hrow : Measurable row := measurable_snd.comp hnoise
    have hqueryNoise : ProbabilityTheory.IndepFun query noise law := by
      have h := hfresh.2.1.comp measurable_fst measurable_id
      simpa [query, noise, run, P, law] using h
    have hnoiseLaw : Measure.map noise law =
        (onlineBatchLaw A.problem b0).prod
          (workerCompressionLaw (n := n) A.quantizer) := by
      simpa [noise, law, onlineDifferenceCompressionLaw] using hfresh.2.2
    have hqueryBatchRow : ProbabilityTheory.IndepFun
        (fun path => (query path, batch path)) row law :=
      indepFun_left_adjoin_fst_of_indepFun_pair law
        (onlineBatchLaw A.problem b0) (workerCompressionLaw A.quantizer)
        query batch row hquery hbatch hrow hqueryNoise hnoiseLaw
    have hmessageKernel : Measurable messageKernel := by
      simpa [messageKernel] using hCostMeas.difference i
    simpa [onlineWorkerDifferenceMessage, onlineWorkerCompressionSample,
      messageKernel, query, batch, noise, row, run, law, onlineProcess_succ] using
      hqueryBatchRow.comp hmessageKernel (measurable_pi_apply i)
  · intro k i
    let supportKernel : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) → ℝ :=
      fun z => quantizerNonzeroCount A.quantizer
        (onlineBatchDifference A.problem z.2.1.2 i z.1.1 z.1.2) (z.2.2 i)
    have hquery : Measurable (fun z : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) => z.1) :=
      measurable_fst
    have hbatch : Measurable (fun z : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
        z.2.1.2) := by fun_prop
    have hmessage : Measurable (fun z : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
        onlineBatchDifference A.problem z.2.1.2 i z.1.1 z.1.2) := by
      simpa only [Function.comp_apply] using
        (hCostMeas.difference i).comp (hquery.prodMk hbatch)
    have hsample : Measurable (fun z : (Point d × Point d) ×
        ((((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) =>
        z.2.2 i) := by fun_prop
    have hsupportKernel : Measurable supportKernel := by
      simpa [supportKernel] using
        (quantizerNonzeroCount_joint_measurable A.quantizer).comp
          (hmessage.prodMk hsample)
    have h := online_query_rest_kernel_indep_refresh_of_cost_measurability
      A x0 hBatch hCostMeas k supportKernel hsupportKernel
    simpa [onlineWorkerRoundSupport, onlineWorkerDifferenceMessage,
      onlineWorkerCompressionSample, onlineRefreshBranch, supportKernel,
      run, law, onlineProcess_succ] using h

/-- Compatibility form of query/current-round independence under the older
global kernel premise. -/
theorem online_query_rest_kernel_indep_refresh_of_kernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (F : (Point d × Point d) ×
      ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) → ℝ)
    (hF : Measurable F) :
    ProbabilityTheory.IndepFun
      (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
        F (((onlineProcess A x0 hBatch (k + 1) path).x,
            (onlineProcess A x0 hBatch k path).x), (path.2 k).2))
      (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).1)
      (onlinePathLaw A) := by
  exact online_query_rest_kernel_indep_refresh_of_cost_measurability
    A x0 hBatch (onlineCostMeasurability_of_kernel A hKernel x0 hBatch) k F hF

set_option maxHeartbeats 2000000 in
/-- Full finite-horizon per-worker executable Algorithm 3 communication
accounting on `onlinePathLaw`.  This theorem is deliberately separate from the
proof-exact initializer and therefore does not conflate its oracle costs. -/
theorem onlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hRegularity : OnlineCommunicationAELawRegularity A x0 hBatch)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (onlineWorkerCommunicationCost A x0 hBatch K i)
        (onlinePathLaw A) ∧
      (∫ path, onlineWorkerCommunicationCost A x0 hBatch K i path
          ∂onlinePathLaw A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  let law := onlinePathLaw (b := b) (b0 := b0) A
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let supportKernel : (Point d × Point d) ×
      ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) → ℝ := fun z =>
    quantizerNonzeroCount A.quantizer
      (onlineBatchDifference A.problem z.2.1.2 i z.1.1 z.1.2) (z.2.2 i)
  let support := fun k (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) =>
    supportKernel (((run (k + 1) path).x, (run k path).x), (path.2 k).2)
  let branch := fun k (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) => (path.2 k).1
  let term := fun k (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) =>
    if branch k path then (d.1 : ℝ) else support k path
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b) := by
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold onlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsupport (k : ℕ) : Integrable (support k) law ∧
      (∫ path, support k path ∂law) ≤ expectedDensity A.quantizer := by
    have hs :=
      onlineWorkerRoundSupport_integrable_and_le_expectedDensity_of_ae_law_regularity
        A x0 hBatch hRegularity hQ k i
    simpa [support, supportKernel, onlineWorkerRoundSupport,
      onlineWorkerDifferenceMessage, onlineWorkerCompressionSample, run, law,
      onlineProcess_succ] using hs
  have hbranchMeas (k : ℕ) : Measurable (branch k) := by
    dsimp [branch]
    fun_prop
  have hbranchLaw (k : ℕ) : Measure.map (branch k) law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law] using onlinePathLaw_refresh_marginal
      (b := b) (b0 := b0) A k
  have hindep (k : ℕ) :
      ProbabilityTheory.IndepFun (support k) (branch k) law := by
    let message := onlineWorkerDifferenceMessage A x0 hBatch k i
    let sample := onlineWorkerCompressionSample
      (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k i
    let hm : AEStronglyMeasurable message law :=
      hRegularity.message_aestronglyMeasurable k i
    have hae : (fun path => quantizerNonzeroCount A.quantizer
        (hm.mk message path) (sample path)) =ᵐ[law] support k := by
      filter_upwards [hm.ae_eq_mk] with path hp
      rw [← hp]
      simp [support, supportKernel, message, sample, run, onlineProcess_succ,
        onlineStep, primalStep, onlineWorkerDifferenceMessage,
        onlineWorkerCompressionSample]
    apply (hRegularity.supportRepresentative_indep_refresh k i).congr
    · simpa [message, sample, hm, law] using hae
    · exact Filter.Eventually.of_forall fun _ => rfl
  have htermInt (k : ℕ) : Integrable (term k) law := by
    have hs : MeasurableSet {path | branch k path = true} :=
      hbranchMeas k (measurableSet_singleton true)
    have hpiece := Integrable.piecewise hs
      (integrable_const (c := (d.1 : ℝ))).integrableOn
      (hsupport k).1.integrableOn
    simpa [term, Set.piecewise] using hpiece
  have htermBound (k : ℕ) : (∫ path, term k path ∂law) ≤
      A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * expectedDensity A.quantizer := by
    let refreshGate := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      if branch k path = true then (d.1 : ℝ) else 0
    let differenceGate := fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
      if branch k path = false then support k path else 0
    have hrefreshInt : Integrable refreshGate law := by
      have hs : MeasurableSet {path | branch k path = true} :=
        hbranchMeas k (measurableSet_singleton true)
      have hpiece := Integrable.piecewise hs
        (integrable_const (μ := law) (c := (d.1 : ℝ))).integrableOn
        (integrable_const (μ := law) (c := (0 : ℝ))).integrableOn
      simpa [refreshGate, Set.piecewise] using hpiece
    have hdifferenceInt : Integrable differenceGate law := by
      have hs : MeasurableSet {path | branch k path = false} :=
        hbranchMeas k (measurableSet_singleton false)
      have hpiece := Integrable.piecewise hs (hsupport k).1.integrableOn
        (integrable_const (c := (0 : ℝ))).integrableOn
      simpa [differenceGate, Set.piecewise] using hpiece
    have hrefreshExpectation : (∫ path, refreshGate path ∂law) =
        A.refreshProbability * d.1 := by
      calc
        (∫ path, refreshGate path ∂law) =
            ∫ c : Bool, (if c then (d.1 : ℝ) else 0)
              ∂Measure.map (branch k) law := by
          symm
          exact MeasureTheory.integral_map (hbranchMeas k).aemeasurable (by fun_prop)
        _ = ∫ c : Bool, (if c then (d.1 : ℝ) else 0)
            ∂refreshLaw A.refreshProbability A.refresh_admissible := by
          rw [hbranchLaw k]
        _ = A.refreshProbability * d.1 := by
          rw [integral_refreshLaw_if A.refreshProbability A.refresh_admissible
            (d.1 : ℝ) 0]
          ring
    have hdifferenceGate : (∫ path, differenceGate path ∂law) ≤
        (1 - A.refreshProbability) * ∫ path, support k path ∂law := by
      simpa [differenceGate] using
        (integral_independent_bool_gate_le law
          (refreshLaw A.refreshProbability A.refresh_admissible) false
          (1 - A.refreshProbability) (support k) (branch k)
          (hsupport k).1 (hbranchMeas k) (hindep k) (hbranchLaw k)
          (refreshLaw_false_real A.refreshProbability A.refresh_admissible))
    calc
      (∫ path, term k path ∂law) =
          ∫ path, refreshGate path + differenceGate path ∂law := by
        apply integral_congr_ae
        filter_upwards [] with path
        by_cases hb : branch k path <;>
          simp [term, refreshGate, differenceGate, hb]
      _ = (∫ path, refreshGate path ∂law) +
          ∫ path, differenceGate path ∂law :=
        integral_add hrefreshInt hdifferenceInt
      _ ≤ A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ∫ path, support k path ∂law := by
        rw [hrefreshExpectation]
        gcongr
      _ ≤ A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer := by
        gcongr
        · exact sub_nonneg.mpr A.refresh_admissible.2
        · exact (hsupport k).2
  have hsumInt : Integrable
      (fun path => ∑ k ∈ Finset.range K.1, term k path) law :=
    MeasureTheory.integrable_finset_sum _ fun k _ => htermInt k
  have htotalInt : Integrable
      (fun path => (d.1 : ℝ) + ∑ k ∈ Finset.range K.1, term k path) law :=
    (integrable_const (d.1 : ℝ)).add hsumInt
  constructor
  · change Integrable
      (fun path => (d.1 : ℝ) + ∑ k ∈ Finset.range K.1, term k path) law
    exact htotalInt
  · change (∫ path, (d.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        term k path ∂law) ≤ _
    rw [MeasureTheory.integral_add (integrable_const (d.1 : ℝ)) hsumInt,
      MeasureTheory.integral_finset_sum (Finset.range K.1)
        (fun k _ => htermInt k)]
    simp only [MeasureTheory.integral_const, probReal_univ, one_smul]
    unfold allWorkerCommunicationCount
    calc
      (d.1 : ℝ) + ∑ k ∈ Finset.range K.1, ∫ path, term k path ∂law ≤
          (d.1 : ℝ) + ∑ _k ∈ Finset.range K.1,
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer) := by
        gcongr with k hk
        exact htermBound k
      _ = (d.1 : ℝ) + K.1 *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer) := by
        simp
        ring

/-- Actual homogeneous Algorithm 3 communication is integrable and obeys the
expected-density bound directly from literal Assumption 3.3 and the weak
law-level Track-B correction.  No global sampled-loss differentiability,
process-measurability structure, or cost-integrability witness is an input. -/
theorem
    onlineWorkerCommunicationCost_integrable_and_expectation_le_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (onlineWorkerCommunicationCost A x0 hBatch K i)
        (onlinePathLaw A) ∧
      (∫ path, onlineWorkerCommunicationCost A x0 hBatch K i path
          ∂onlinePathLaw A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  exact
    onlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
      A x0 hBatch
        (onlineCommunicationAELawRegularity_of_literal_and_lawRegularity
          A x0 hBatch sigma hLiteral hRegularity)
        hQ K i

set_option maxHeartbeats 2000000 in
/-- Compatibility wrapper for the former strict law-regularity interface. -/
theorem onlineWorkerCommunicationCost_integrable_and_expectation_le_of_law_regularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hRegularity : OnlineCommunicationLawRegularity A x0 hBatch)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (onlineWorkerCommunicationCost A x0 hBatch K i)
        (onlinePathLaw A) ∧
      (∫ path, onlineWorkerCommunicationCost A x0 hBatch K i path
          ∂onlinePathLaw A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  exact onlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
    A x0 hBatch
      (onlineCommunicationAELawRegularity_of_lawRegularity
        A x0 hBatch hRegularity) hQ K i

set_option maxHeartbeats 2000000 in
/-- Compatibility form under the former global generated-cost measurability
contract. -/
theorem onlineWorkerCommunicationCost_integrable_and_expectation_le_of_cost_measurability
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hCostMeas : OnlineCostMeasurability A x0 hBatch)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (onlineWorkerCommunicationCost A x0 hBatch K i)
        (onlinePathLaw A) ∧
      (∫ path, onlineWorkerCommunicationCost A x0 hBatch K i path
          ∂onlinePathLaw A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  exact onlineWorkerCommunicationCost_integrable_and_expectation_le_of_law_regularity
    A x0 hBatch
      (onlineCommunicationLawRegularity_of_costMeasurability
        A x0 hBatch hCostMeas) hQ K i

set_option maxHeartbeats 2000000 in
/-- Compatibility form of executable Algorithm 3 communication accounting
under the older global stochastic-gradient kernel premise. -/
theorem onlineWorkerCommunicationCost_integrable_and_expectation_le
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (onlineWorkerCommunicationCost A x0 hBatch K i)
        (onlinePathLaw A) ∧
      (∫ path, onlineWorkerCommunicationCost A x0 hBatch K i path
          ∂onlinePathLaw A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  exact onlineWorkerCommunicationCost_integrable_and_expectation_le_of_cost_measurability
    A x0 hBatch (onlineCostMeasurability_of_kernel A hKernel x0 hBatch) hQ K i

/-! ## Accuracy-indexed measured communication endpoints

The imported complexity theorems already construct the source schedules and
prove their convergence and iteration bounds.  The definitions and lemmas in
this file replace their analytic communication expression by the expectation
of the actual generated messages, without treating the old scalar identity as
a measurement theorem. -/

/-- A pointwise nonnegative quantity dominated by a nonnegative Big-O family
has the same Big-O bound. -/
theorem accuracyBigO_of_nonneg_le
    {actual majorant scale : Accuracy → ℝ}
    (hmajorant : AccuracyBigO majorant scale)
    (hactual : ∀ ε, 0 ≤ actual ε)
    (hmajorantNonneg : ∀ ε, 0 ≤ majorant ε)
    (hle : ∀ ε, actual ε ≤ majorant ε) :
    AccuracyBigO actual scale := by
  unfold AccuracyBigO at hmajorant ⊢
  rw [Asymptotics.isBigO_iff'] at hmajorant ⊢
  rcases hmajorant with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with ε hε
  rw [Real.norm_eq_abs, abs_of_nonneg (hmajorantNonneg ε)] at hε
  rw [Real.norm_eq_abs, abs_of_nonneg (hactual ε)]
  exact (hle ε).trans hε

/-- Every realized Algorithm 1 per-worker communication count is
nonnegative. -/
theorem basicWorkerCommunicationCost_nonneg
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (K : Count) (i : Worker n)
    (path : ℕ → BasicRoundNoise n Ξ) :
    0 ≤ basicWorkerCommunicationCost A x0 K i path := by
  unfold basicWorkerCommunicationCost
  apply add_nonneg <;> try positivity
  apply Finset.sum_nonneg
  intro k hk
  split <;> try positivity
  unfold quantizerNonzeroCount
  positivity

/-- The measured C.1/C.2 package: convergence and iteration complexity use
the generated Algorithm 1 process, while communication is the integral of the
actual per-worker pathwise message count under the very same `basicPathLaw`. -/
def BasicMeasuredCommunicationComplexity
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (K : Accuracy → Count)
    (accuracy : Accuracy → Prop) (iterationScale communicationScale : Accuracy → ℝ) :
    Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    ∀ i : Worker n,
      (∀ ε, Integrable (basicWorkerCommunicationCost A x0 (K ε) i)
        (basicPathLaw A)) ∧
      AccuracyBigO
        (fun ε => ∫ path, basicWorkerCommunicationCost A x0 (K ε) i path
          ∂basicPathLaw A)
        communicationScale

/-- Lift an already proved Algorithm 1 convergence/iteration schedule to its
measured per-worker communication endpoint.  The scalar count occurs only as
an analytic upper bound between the measured theorem and the requested scale. -/
theorem basicMeasuredCommunicationComplexity_of_twoEndpoint
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale communicationScale : Accuracy → ℝ)
    (hEndpoints : TwoEndpointComplexity K accuracy iterationScale
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    BasicMeasuredCommunicationComplexity A x0 K accuracy iterationScale
      communicationScale := by
  unfold TwoEndpointComplexity at hEndpoints
  unfold BasicMeasuredCommunicationComplexity
  refine ⟨hEndpoints.1, hEndpoints.2.1, ?_⟩
  intro i
  constructor
  · intro ε
    exact (basicWorkerCommunicationCost_integrable_and_expectation_le
      A x0 Llocal hSmooth hQ (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hEndpoints.2.2
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        basicWorkerCommunicationCost_nonneg A x0 (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability :=
        le_of_lt A.refresh_admissible.1
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact (basicWorkerCommunicationCost_integrable_and_expectation_le
        A x0 Llocal hSmooth hQ (K ε) i).2

/-- Measured public root for Theorems C.1 and C.2.  Each conjunct uses the
Algorithm 1 process and `basicPathLaw` both for convergence and for the
per-worker communication expectation. -/
theorem Theorem_C1_C2_measured_communication_complexity
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 xStar : Point d)
    (Llocal : Worker n → ℝ) (ω fStar : ℝ) (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound A.problem fStar)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    (hPL : SatisfiesPL A.problem μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStepNonconvex : MARINAStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) A.refreshProbability ω n)
    (hStepPL : MARINAPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) A.refreshProbability ω μ n) :
    let ζ := expectedDensity A.quantizer
    let Δnc := globalObjective A.problem x0 - fStar
    let bracket := rootMeanSquare Llocal *
      (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
        (A.refreshProbability * n.1)))
    let Δpl := globalObjective A.problem x0 - globalObjective A.problem xStar
    let factor := max (1 / A.refreshProbability)
      (rootMeanSquare Llocal / μ *
        (1 + Real.sqrt ((1 - A.refreshProbability) * ω /
          (A.refreshProbability * n.1))))
    (∃ K : Accuracy → Count,
      BasicMeasuredCommunicationComplexity A x0 K
        (fun ε => NonconvexAccuracy (K ε) A.problem (marinaProcess A x0)
          (basicPathLaw A) ε)
        (fun ε => Δnc / (ε : ℝ) ^ 2 * bracket)
        (fun ε => d.1 + Δnc / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ))) ∧
    (∃ K : Accuracy → Count,
      BasicMeasuredCommunicationComplexity A x0 K
        (fun ε => PLAccuracy (K ε) A.problem (marinaProcess A x0)
          (basicPathLaw A) xStar ε)
        (fun ε => factor * Real.log (Δpl / (ε : ℝ)))
        (fun ε => d.1 + factor *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ) *
          Real.log (Δpl / (ε : ℝ)))) := by
  dsimp
  constructor
  · rcases Theorem_C1_MARINA_complexity_endpoints A x0 Llocal ω fStar
      hLower hSmooth hQuantizer hStepNonconvex with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    exact basicMeasuredCommunicationComplexity_of_twoEndpoint
      A x0 Llocal hSmooth hQuantizer K _ _ _ hK
  · rcases Theorem_C2_MARINA_PL_complexity_endpoints A x0 xStar Llocal
      ω fStar μ hLower hSmooth hPL hQuantizer hStepPL with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    exact basicMeasuredCommunicationComplexity_of_twoEndpoint
      A x0 Llocal hSmooth hQuantizer K _ _ _ hK

/-- Every realized finite-sum per-worker communication count is
nonnegative. -/
theorem finiteSumWorkerCommunicationCost_nonneg
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (K : Count)
    (i : Worker n) (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) :
    0 ≤ finiteSumWorkerCommunicationCost A x0 K i path := by
  unfold finiteSumWorkerCommunicationCost
  apply add_nonneg <;> try positivity
  apply Finset.sum_nonneg
  intro k hk
  split <;> try positivity
  unfold quantizerNonzeroCount
  positivity

/-- Every realized Remark D.1 per-worker communication count is
nonnegative, independently of the worker's batch size. -/
theorem heterogeneousFiniteSumWorkerCommunicationCost_nonneg
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (K : Count)
    (i : Worker n)
    (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) :
    0 ≤ heterogeneousFiniteSumWorkerCommunicationCost A x0 K i path := by
  unfold heterogeneousFiniteSumWorkerCommunicationCost
  apply add_nonneg <;> try positivity
  apply Finset.sum_nonneg
  intro k hk
  split <;> try positivity
  unfold quantizerNonzeroCount
  positivity

/-- Every realized Remark D.2 executable per-worker communication count is
nonnegative. -/
theorem heterogeneousOnlineWorkerCommunicationCost_nonneg
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (K : Count)
    (i : Worker n)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) :
    0 ≤ heterogeneousOnlineWorkerCommunicationCost A x0 K i path := by
  unfold heterogeneousOnlineWorkerCommunicationCost
  apply add_nonneg <;> try positivity
  apply Finset.sum_nonneg
  intro k hk
  split <;> try positivity
  unfold quantizerNonzeroCount
  positivity

/-- Accuracy-indexed measured costs for executable heterogeneous Remark D.2.
Every worker retains its own refresh and difference batch sizes, while all
integrals use the canonical dependent-product path law. -/
def HeterogeneousOnlineMeasuredCostComplexity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    ∀ i : Worker n,
      (∀ ε, Integrable
        (heterogeneousOnlineWorkerOracleCost
          (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          heterogeneousOnlineWorkerOracleCost
            (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)
        (oracleScale i) ∧
      (∀ ε, Integrable
        (heterogeneousOnlineWorkerCommunicationCost
          (b := b) (b0 := b0) A x0 (K ε) i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          heterogeneousOnlineWorkerCommunicationCost
            (b := b) (b0 := b0) A x0 (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)
        communicationScale

/-- Lift a heterogeneous executable online accuracy/iteration family and its
analytic workerwise scales to the actual measured oracle and communication
random variables. -/
theorem heterogeneousOnlineMeasuredCostComplexity_of_bounds
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hCostMeas : HeterogeneousOnlineCostMeasurability
      (b := b) (b0 := b0) A x0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ)
    (hAccuracy : ∀ ε, accuracy ε)
    (hIteration : AccuracyIterationBigO (fun ε => (K ε).1) iterationScale)
    (hOracle : ∀ i, AccuracyBigO
      (fun ε => ((b i).1 : ℝ) + (K ε).1 *
        (A.refreshProbability * (b i).1 +
          2 * (1 - A.refreshProbability) * (b0 i).1))
      (oracleScale i))
    (hCommunication : AccuracyBigO
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    HeterogeneousOnlineMeasuredCostComplexity (b := b) (b0 := b0) A x0 K accuracy
      iterationScale oracleScale communicationScale := by
  unfold HeterogeneousOnlineMeasuredCostComplexity
  refine ⟨hAccuracy, hIteration, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
      (b := b) (b0 := b0) A (K ε) i).1
  · rw [show (fun ε => ∫ path,
        heterogeneousOnlineWorkerOracleCost
          (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) =
        (fun ε => ((b i).1 : ℝ) + (K ε).1 *
          (A.refreshProbability * (b i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1)) by
      funext ε
      exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
        (b := b) (b0 := b0) A (K ε) i).2]
    exact hOracle i
  · intro ε
    exact
      (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le
        A x0 hCostMeas hQ (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hCommunication
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        heterogeneousOnlineWorkerCommunicationCost_nonneg
          A x0 (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability :=
        le_of_lt A.refresh_admissible.1
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact
        (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le
          A x0 hCostMeas hQ (K ε) i).2

/-- Law-a.e. heterogeneous measured-cost lift.  Unlike the compatibility
theorem above, this theorem does not require globally measurable process and
difference kernels; the only regularity input is the generated-message
interface, and neither integrability nor a cost bound is assumed. -/
theorem heterogeneousOnlineMeasuredCostComplexity_of_bounds_of_ae_law_regularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hRegularity : HeterogeneousOnlineCommunicationAELawRegularity
      (b := b) (b0 := b0) A x0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ)
    (hAccuracy : ∀ ε, accuracy ε)
    (hIteration : AccuracyIterationBigO (fun ε => (K ε).1) iterationScale)
    (hOracle : ∀ i, AccuracyBigO
      (fun ε => ((b i).1 : ℝ) + (K ε).1 *
        (A.refreshProbability * (b i).1 +
          2 * (1 - A.refreshProbability) * (b0 i).1))
      (oracleScale i))
    (hCommunication : AccuracyBigO
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    HeterogeneousOnlineMeasuredCostComplexity (b := b) (b0 := b0) A x0 K accuracy
      iterationScale oracleScale communicationScale := by
  unfold HeterogeneousOnlineMeasuredCostComplexity
  refine ⟨hAccuracy, hIteration, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
      (b := b) (b0 := b0) A (K ε) i).1
  · rw [show (fun ε => ∫ path,
        heterogeneousOnlineWorkerOracleCost
          (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) =
        (fun ε => ((b i).1 : ℝ) + (K ε).1 *
          (A.refreshProbability * (b i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1)) by
      funext ε
      exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
        (b := b) (b0 := b0) A (K ε) i).2]
    exact hOracle i
  · intro ε
    exact
      (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
        A x0 hRegularity hQ (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hCommunication
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        heterogeneousOnlineWorkerCommunicationCost_nonneg
          A x0 (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability :=
        le_of_lt A.refresh_admissible.1
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact
        (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
          A x0 hRegularity hQ (K ε) i).2

/-- Source/correction-derived heterogeneous measured-cost lift.  Accuracy and
analytic complexity bounds remain explicit proof inputs, but all regularity
of the actual executable process and communication observable is derived from
literal Assumption 3.3 and the weak law-scoped Track-B correction. -/
theorem
    heterogeneousOnlineMeasuredCostComplexity_of_bounds_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hGradientRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ)
    (hAccuracy : ∀ ε, accuracy ε)
    (hIteration : AccuracyIterationBigO (fun ε => (K ε).1) iterationScale)
    (hOracle : ∀ i, AccuracyBigO
      (fun ε => ((b i).1 : ℝ) + (K ε).1 *
        (A.refreshProbability * (b i).1 +
          2 * (1 - A.refreshProbability) * (b0 i).1))
      (oracleScale i))
    (hCommunication : AccuracyBigO
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    HeterogeneousOnlineMeasuredCostComplexity (b := b) (b0 := b0) A x0 K accuracy
      iterationScale oracleScale communicationScale := by
  exact heterogeneousOnlineMeasuredCostComplexity_of_bounds_of_ae_law_regularity
    A x0
      (heterogeneousOnlineCommunicationAELawRegularity_of_literal_and_lawRegularity
        (b := b) (b0 := b0) A x0 sigma hLiteral hGradientRegularity)
      hQ K accuracy iterationScale oracleScale communicationScale hAccuracy
      hIteration hOracle hCommunication

/-! ## Heterogeneous measured communication

The heterogeneous paths use dependent worker-indexed batch types.  The
following marginal lemma records that, for a fixed worker, the actual batch
and compressor sample read from the generated path still have exactly the
product law prescribed by Remark D.1. -/

theorem heterogeneousFiniteSum_path_worker_noise_map_eq_prod
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (k : ℕ) (i : Worker n) :
    Measure.map
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i))
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) =
      (workerBatchLaw k i).prod A.quantizer.law := by
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (workerBatchLaw t j) :=
    hWorkerBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hWorkerBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  calc
    Measure.map
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          ((path k).2.1 i, (path k).2.2 i))
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) =
        Measure.map
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (z.2.1 i, z.2.2 i))
          (Measure.map
            (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              path k)
            (heterogeneousFiniteSumPathLaw A
              (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))) := by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · fun_prop
          · exact measurable_pi_apply k
    _ = Measure.map
          (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
            (z.2.1 i, z.2.2 i))
          (heterogeneousFiniteSumRoundLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)) := by
          rw [heterogeneousFiniteSumPathLaw_round_marginal
            A workerBatchLaw hWorkerBatchLaw k]
    _ = Measure.map
          (fun z : HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ) =>
            (z.1 i, z.2 i))
          ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
            (workerCompressionLaw A.quantizer)) := by
          unfold heterogeneousFiniteSumRoundLaw
          calc
            Measure.map
                (fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
                  (z.2.1 i, z.2.2 i))
                ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                  ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                    (workerCompressionLaw A.quantizer))) =
                Measure.map
                  (fun z : HeterogeneousFiniteSumBatch n m b0 ×
                      (Worker n → Ξ) => (z.1 i, z.2 i))
                  (Measure.map Prod.snd
                    ((refreshLaw A.refreshProbability A.refresh_admissible).prod
                      ((heterogeneousFiniteSumIndependentBatchLaw
                          workerBatchLaw k).prod
                        (workerCompressionLaw A.quantizer)))) := by
                  rw [MeasureTheory.Measure.map_map]
                  · rfl
                  · fun_prop
                  · exact measurable_snd
            _ = Measure.map
                  (fun z : HeterogeneousFiniteSumBatch n m b0 ×
                      (Worker n → Ξ) => (z.1 i, z.2 i))
                  ((heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
                    (workerCompressionLaw A.quantizer)) := by
                  rw [MeasureTheory.Measure.map_snd_prod, measure_univ, one_smul]
    _ = (Measure.map
          (fun batch : HeterogeneousFiniteSumBatch n m b0 => batch i)
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)).prod
        (Measure.map (fun samples : Worker n → Ξ => samples i)
          (workerCompressionLaw A.quantizer)) := by
          simpa [Prod.map] using
            (MeasureTheory.Measure.map_prod_map
              (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)
              (workerCompressionLaw A.quantizer)
              (measurable_pi_apply i) (measurable_pi_apply i)).symm
    _ = (workerBatchLaw k i).prod A.quantizer.law := by
      rw [heterogeneousFiniteSumIndependentBatchLaw_worker_marginal
          workerBatchLaw hWorkerBatchLaw k i,
        workerCompressionLaw_component_marginal A.quantizer i]

/-- The actual non-refresh message of worker `i` in heterogeneous Algorithm 2
has expected support at most `expectedDensity`.  Its input is built from the
generated strict-past state and the worker's actual dependent-size minibatch;
the fresh compressor coordinate is not replaced by an auxiliary sample. -/
theorem heterogeneousFiniteSumWorkerRoundSupport_integrable_and_le_expectedDensity
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    let message :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        let s := heterogeneousFiniteSumProcess (b0 := b0) A x0 k path
        heterogeneousFiniteSumBatchDifference A.problem b0 (path k).2.1 i
          (primalStep A.stepSize s) s.x
    let sample :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (path k).2.2 i
    Integrable
        (fun path => quantizerNonzeroCount A.quantizer
          (message path) (sample path))
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ∧
      (∫ path, quantizerNonzeroCount A.quantizer
          (message path) (sample path)
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ≤
        expectedDensity A.quantizer := by
  let P := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let query :=
    fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      (primalStep A.stepSize
          (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path),
        (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path).x)
  let batch :=
    fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      (path k).2.1 i
  let sample :=
    fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      (path k).2.2 i
  let message :=
    fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
      heterogeneousFiniteSumBatchDifference A.problem b0 (path k).2.1 i
        (query path).1 (query path).2
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (workerBatchLaw t j) :=
    hWorkerBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hWorkerBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hquery : Measurable query := by
    have hs := (heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (heterogeneousFiniteSumStrictPast_le
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
    exact ((measurable_primalStep A.stepSize).comp hs).prodMk
      ((measurable_state_x d).comp hs)
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hsample : Measurable sample := by
    dsimp [sample]
    fun_prop
  have hqueryNoise : ProbabilityTheory.IndepFun query
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (batch path, sample path)) P := by
    simpa [query, batch, sample, P, heterogeneousFiniteSumProcess,
      SOptLib.recursiveIterateProcess, heterogeneousFiniteSumStep] using
      heterogeneousFiniteSum_strictPast_query_indep_worker_noise
        A x0 workerBatchLaw hWorkerBatchLaw k i
  have hpairLaw : Measure.map
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (batch path, sample path)) P =
      (workerBatchLaw k i).prod A.quantizer.law := by
    simpa [batch, sample, P] using
      heterogeneousFiniteSum_path_worker_noise_map_eq_prod
        A workerBatchLaw hWorkerBatchLaw k i
  have hqueryBatchSample : ProbabilityTheory.IndepFun
      (fun path => (query path, batch path)) sample P :=
    indepFun_left_adjoin_fst_of_indepFun_pair P (workerBatchLaw k i)
      A.quantizer.law query batch sample hquery hbatch hsample
      hqueryNoise hpairLaw
  have hmessageKernel : Measurable
      (fun z : (Point d × Point d) ×
          HeterogeneousFiniteSumWorkerBatch m (b0 i) =>
        finiteSumWorkerBatchDifference A.problem z.2 i z.1.1 z.1.2) := by
    simpa using
      finiteSumWorkerBatchDifference_joint_measurable
        (b0 := b0 i) A.problem i
  have hmessage : Measurable message := by
    have h := hmessageKernel.comp (hquery.prodMk hbatch)
    simpa [message, batch, heterogeneousFiniteSumBatchDifference,
      finiteSumWorkerBatchDifference] using h
  have hindep : ProbabilityTheory.IndepFun message sample P := by
    have h := hqueryBatchSample.comp hmessageKernel measurable_id
    simpa [message, batch, heterogeneousFiniteSumBatchDifference,
      finiteSumWorkerBatchDifference] using h
  have hsampleLaw : Measure.map sample P = A.quantizer.law := by
    calc
      Measure.map sample P = Measure.map Prod.snd
          (Measure.map (fun path => (batch path, sample path)) P) := by
        simpa only [Function.comp_apply] using
          (Measure.map_map measurable_snd (hbatch.prodMk hsample) (μ := P)).symm
      _ = Measure.map Prod.snd
          ((workerBatchLaw k i).prod A.quantizer.law) := by rw [hpairLaw]
      _ = A.quantizer.law := by simp
  have hsupport :=
    adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
      P hQ message sample hmessage hsample hindep hsampleLaw
  simpa [message, query, sample, P] using hsupport

/-- A measurable observable of the generated heterogeneous Algorithm 2 state
and the non-coin coordinates of its current round is independent of that
round's refresh coin.  This is inherited from the independent product path
law, including the worker-dependent minibatch schedule. -/
theorem heterogeneousFiniteSum_state_rest_kernel_indep_refresh
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (k : ℕ)
    (F : State d × (HeterogeneousFiniteSumBatch n m b0 ×
      (Worker n → Ξ)) → ℝ) (hF : Measurable F) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        F (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path,
          (path k).2))
      (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        (path k).1)
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) := by
  let law := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let state := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    heterogeneousFiniteSumProcess (b0 := b0) A x0 k path
  let current := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    path k
  let rest := fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ => z.2
  let coin := fun z : HeterogeneousFiniteSumRoundNoise n m b0 Ξ => z.1
  let restPath := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    rest (current path)
  let branch := fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
    coin (current path)
  let restLaw :=
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let roundLaw := heterogeneousFiniteSumRoundLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (workerBatchLaw t j) :=
    hWorkerBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hWorkerBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hstate : Measurable state := by
    have hs := (heterogeneousFiniteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (heterogeneousFiniteSumStrictPast_le
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k) le_rfl
    simpa [state] using hs
  have hcurrent : Measurable current := measurable_pi_apply k
  have hrest : Measurable rest := measurable_snd
  have hcoin : Measurable coin := measurable_fst
  have hrestPath : Measurable restPath := hrest.comp hcurrent
  have hbranch : Measurable branch := hcoin.comp hcurrent
  have hstateCurrent : ProbabilityTheory.IndepFun state current law := by
    let round := fun t
        (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) => path t
    have hroundMeas : ∀ t, Measurable (round t) :=
      fun t => measurable_pi_apply t
    have hroundIndep : ProbabilityTheory.iIndepFun round law := by
      dsimp [round, law]
      unfold heterogeneousFiniteSumPathLaw
      exact ProbabilityTheory.iIndepFun_infinitePi (fun _ => measurable_id)
    have hstateStrict : Measurable[heterogeneousFiniteSumStrictPast
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k] state := by
      simpa [state] using
        heterogeneousFiniteSumProcess_strictPast_measurable
          (b0 := b0) A x0 k
    have hstrict : heterogeneousFiniteSumStrictPast
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
        (⨆ t ∈ ({t : ℕ | t < k} : Set ℕ),
          MeasurableSpace.comap (round t) inferInstance) := by
      refine iSup_le fun j => ?_
      exact le_iSup_of_le (j : ℕ)
        (le_iSup_of_le (show (j : ℕ) < k from j.2) le_rfl)
    have hdisjoint : Disjoint ({t : ℕ | t < k} : Set ℕ) ({k} : Set ℕ) := by
      rw [Set.disjoint_left]
      intro t ht htk
      exact (Nat.ne_of_lt ht) htk
    have h := SOptLib.iIndepFun_indepFun_strictPast_singleton
      round law hroundMeas hroundIndep
      (heterogeneousFiniteSumStrictPast
        (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
      ({t : ℕ | t < k} : Set ℕ) k hstateStrict hdisjoint hstrict
    simpa [round, current] using h
  have hcurrentLaw : Measure.map current law = roundLaw := by
    simpa [current, law, roundLaw] using
      heterogeneousFiniteSumPathLaw_round_marginal
        A workerBatchLaw hWorkerBatchLaw k
  have hstatePair : ProbabilityTheory.IndepFun state
      (fun path => (restPath path, branch path)) law := by
    simpa [restPath, branch, rest, coin, current] using
      hstateCurrent.comp measurable_id
        (measurable_snd.prodMk measurable_fst)
  have hpairLaw : Measure.map (fun path => (restPath path, branch path)) law =
      restLaw.prod coinLaw := by
    calc
      Measure.map (fun path => (restPath path, branch path)) law =
          Measure.map Prod.swap (Measure.map current law) := by
        rw [Measure.map_map measurable_swap hcurrent]
        rfl
      _ = Measure.map Prod.swap roundLaw := by rw [hcurrentLaw]
      _ = Measure.map Prod.swap (coinLaw.prod restLaw) := by
        congr 1
      _ = restLaw.prod coinLaw := MeasureTheory.Measure.prod_swap
  have hjoined : ProbabilityTheory.IndepFun
      (fun path => (state path, restPath path)) branch law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law restLaw coinLaw
      state restPath branch hstate hrestPath hbranch hstatePair hpairLaw
  simpa [state, restPath, branch, rest, coin, current, law] using
    hjoined.comp hF measurable_id

set_option maxHeartbeats 2000000 in
/-- Full finite-horizon per-worker communication accounting for Remark D.1.
The bound is over the actual heterogeneous Algorithm 2 path, retains the
dense initialization, and uses `expectedDensity` only as a supremum upper
bound for the adaptive compressed messages. -/
theorem heterogeneousFiniteSumWorkerCommunicationCost_integrable_and_expectation_le
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (heterogeneousFiniteSumWorkerCommunicationCost A x0 K i)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ∧
      (∫ path,
          heterogeneousFiniteSumWorkerCommunicationCost A x0 K i path
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  let law := heterogeneousFiniteSumPathLaw A
    (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
  let supportKernel : State d ×
      (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) → ℝ := fun z =>
    quantizerNonzeroCount A.quantizer
      (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
        (primalStep A.stepSize z.1) z.1.x)
      (z.2.2 i)
  let support :=
    fun k (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) =>
      supportKernel
        (heterogeneousFiniteSumProcess (b0 := b0) A x0 k path, (path k).2)
  let branch :=
    fun k (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) =>
      (path k).1
  let term :=
    fun k (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) =>
      if branch k path then (d.1 : ℝ) else support k path
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (workerBatchLaw t j) :=
    hWorkerBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t) :=
    heterogeneousFiniteSumIndependentBatchLaw_isProbability
      workerBatchLaw hWorkerBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (heterogeneousFiniteSumRoundLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw t)) := by
    unfold heterogeneousFiniteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have hsupportKernelRaw : Measurable (fun z : State d ×
      (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) =>
      quantizerNonzeroCount A.quantizer
        (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
          (primalStep A.stepSize z.1) z.1.x)
        (z.2.2 i)) := by
    have hxnext : Measurable (fun z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        primalStep A.stepSize z.1) :=
      (measurable_primalStep A.stepSize).comp measurable_fst
    have hx : Measurable (fun z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) => z.1.x) :=
      (measurable_state_x d).comp measurable_fst
    have hbatch : Measurable (fun z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) => z.2.1) :=
      measurable_fst.comp measurable_snd
    have hmessage : Measurable (fun z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
          (primalStep A.stepSize z.1) z.1.x) := by
      simpa only [Function.comp_apply] using
        (heterogeneousFiniteSumBatchDifference_joint_measurable
          (b0 := b0) A.problem i).comp ((hxnext.prodMk hx).prodMk hbatch)
    have hsample : Measurable (fun z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) => z.2.2 i) :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
    rw [show (fun z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        quantizerNonzeroCount A.quantizer
          (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i)) =
        fun z => ∑ j : Fin d.1,
          if A.quantizer.apply
              (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
                (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j ≠ 0
          then (1 : ℝ) else 0 by
      funext z
      unfold quantizerNonzeroCount
      exact Finset.natCast_card_filter
        (fun j : Fin d.1 => A.quantizer.apply
          (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j ≠ 0)
        Finset.univ]
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        A.quantizer.apply
          (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j) :=
      (EuclideanSpace.proj j).continuous.measurable.comp
        (A.quantizer.measurable_apply_uncurry.comp (hmessage.prodMk hsample))
    have hzero : MeasurableSet {z : State d ×
        (HeterogeneousFiniteSumBatch n m b0 × (Worker n → Ξ)) |
        A.quantizer.apply
          (heterogeneousFiniteSumBatchDifference A.problem b0 z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j = 0} :=
      hj (measurableSet_singleton 0)
    exact Measurable.ite hzero.compl measurable_const measurable_const
  have hsupportKernel : Measurable supportKernel := by
    simpa only [supportKernel] using hsupportKernelRaw
  have hsupport (k : ℕ) :
      Integrable (support k) law ∧
        (∫ path, support k path ∂law) ≤ expectedDensity A.quantizer := by
    simpa [support, supportKernel, law] using
      heterogeneousFiniteSumWorkerRoundSupport_integrable_and_le_expectedDensity
        A x0 workerBatchLaw hWorkerBatchLaw hQ k i
  have hbranchMeas (k : ℕ) : Measurable (branch k) := by
    dsimp [branch]
    fun_prop
  have hbranchLaw (k : ℕ) : Measure.map (branch k) law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law] using
      heterogeneousFiniteSumPathLaw_refresh_marginal
        A workerBatchLaw hWorkerBatchLaw k
  have hindep (k : ℕ) :
      ProbabilityTheory.IndepFun (support k) (branch k) law := by
    have h := heterogeneousFiniteSum_state_rest_kernel_indep_refresh
      A x0 workerBatchLaw hWorkerBatchLaw k supportKernel hsupportKernel
    simpa only [support, branch, law] using h
  have htermInt (k : ℕ) : Integrable (term k) law := by
    have hs : MeasurableSet {path | branch k path = true} :=
      hbranchMeas k (measurableSet_singleton true)
    have hpiece := Integrable.piecewise hs
      (integrable_const (c := (d.1 : ℝ))).integrableOn
      (hsupport k).1.integrableOn
    simpa [term, Set.piecewise] using hpiece
  have htermBound (k : ℕ) :
      (∫ path, term k path ∂law) ≤
        A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer := by
    let refreshGate :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        if branch k path = true then (d.1 : ℝ) else 0
    let differenceGate :=
      fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
        if branch k path = false then support k path else 0
    have hrefreshInt : Integrable refreshGate law := by
      have hs : MeasurableSet {path | branch k path = true} :=
        hbranchMeas k (measurableSet_singleton true)
      have hpiece := Integrable.piecewise hs
        (integrable_const (μ := law) (c := (d.1 : ℝ))).integrableOn
        (integrable_const (μ := law) (c := (0 : ℝ))).integrableOn
      simpa [refreshGate, Set.piecewise] using hpiece
    have hdifferenceInt : Integrable differenceGate law := by
      have hs : MeasurableSet {path | branch k path = false} :=
        hbranchMeas k (measurableSet_singleton false)
      have hpiece := Integrable.piecewise hs (hsupport k).1.integrableOn
        (integrable_const (c := (0 : ℝ))).integrableOn
      simpa [differenceGate, Set.piecewise] using hpiece
    have hrefreshExpectation :
        (∫ path, refreshGate path ∂law) = A.refreshProbability * d.1 := by
      calc
        (∫ path, refreshGate path ∂law) =
            ∫ c : Bool, (if c then (d.1 : ℝ) else 0)
              ∂Measure.map (branch k) law := by
          symm
          exact MeasureTheory.integral_map (hbranchMeas k).aemeasurable
            (by fun_prop)
        _ = ∫ c : Bool, (if c then (d.1 : ℝ) else 0)
            ∂refreshLaw A.refreshProbability A.refresh_admissible := by
          rw [hbranchLaw k]
        _ = A.refreshProbability * d.1 := by
          rw [integral_refreshLaw_if A.refreshProbability
            A.refresh_admissible (d.1 : ℝ) 0]
          ring
    have hdifferenceGate :
        (∫ path, differenceGate path ∂law) ≤
          (1 - A.refreshProbability) * ∫ path, support k path ∂law := by
      simpa [differenceGate] using
        (integral_independent_bool_gate_le law
          (refreshLaw A.refreshProbability A.refresh_admissible) false
          (1 - A.refreshProbability) (support k) (branch k)
          (hsupport k).1 (hbranchMeas k) (hindep k) (hbranchLaw k)
          (refreshLaw_false_real A.refreshProbability A.refresh_admissible))
    calc
      (∫ path, term k path ∂law) =
          (∫ path, refreshGate path + differenceGate path ∂law) := by
        apply integral_congr_ae
        filter_upwards [] with path
        by_cases hb : branch k path <;>
          simp [term, refreshGate, differenceGate, hb]
      _ = (∫ path, refreshGate path ∂law) +
          ∫ path, differenceGate path ∂law :=
        integral_add hrefreshInt hdifferenceInt
      _ ≤ A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ∫ path, support k path ∂law := by
        rw [hrefreshExpectation]
        gcongr
      _ ≤ A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer := by
        gcongr
        · exact sub_nonneg.mpr A.refresh_admissible.2
        · exact (hsupport k).2
  have hsumInt : Integrable
      (fun path => ∑ k ∈ Finset.range K.1, term k path) law :=
    MeasureTheory.integrable_finset_sum _ fun k _ => htermInt k
  have htotalInt : Integrable
      (fun path => (d.1 : ℝ) + ∑ k ∈ Finset.range K.1, term k path) law :=
    (integrable_const (d.1 : ℝ)).add hsumInt
  constructor
  · change Integrable
      (fun path => (d.1 : ℝ) + ∑ k ∈ Finset.range K.1, term k path) law
    exact htotalInt
  · change (∫ path, (d.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        term k path ∂law) ≤ _
    rw [MeasureTheory.integral_add (integrable_const (d.1 : ℝ)) hsumInt,
      MeasureTheory.integral_finset_sum (Finset.range K.1)
        (fun k _ => htermInt k)]
    simp only [MeasureTheory.integral_const, probReal_univ, one_smul]
    unfold allWorkerCommunicationCount
    calc
      (d.1 : ℝ) + ∑ k ∈ Finset.range K.1, ∫ path, term k path ∂law ≤
          (d.1 : ℝ) + ∑ _k ∈ Finset.range K.1,
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer) := by
        gcongr with k hk
        exact htermBound k
      _ = (d.1 : ℝ) + K.1 *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer) := by
        simp
        ring

/-- Accuracy-indexed measured Remark D.1 costs.  Both cost fields use the
same heterogeneous product path law as the worker-dependent process, and the
oracle scale remains indexed by the worker's own minibatch size. -/
def HeterogeneousFiniteSumMeasuredCostComplexity
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    ∀ i : Worker n,
      (∀ ε, Integrable
        (heterogeneousFiniteSumWorkerOracleCost (Ξ := Ξ) (K ε) i)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          heterogeneousFiniteSumWorkerOracleCost (Ξ := Ξ) (K ε) i path
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))
        (oracleScale i) ∧
      (∀ ε, Integrable
        (heterogeneousFiniteSumWorkerCommunicationCost A x0 (K ε) i)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          heterogeneousFiniteSumWorkerCommunicationCost A x0 (K ε) i path
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))
        communicationScale

/-- Lift any proved heterogeneous Remark D.1 accuracy/iteration schedule and
its analytic workerwise scales to the measured generated oracle and
communication variables. -/
theorem heterogeneousFiniteSumMeasuredCostComplexity_of_bounds
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ)
    (hAccuracy : ∀ ε, accuracy ε)
    (hIteration : AccuracyIterationBigO (fun ε => (K ε).1) iterationScale)
    (hOracle : ∀ i, AccuracyBigO
      (fun ε => (m.1 : ℝ) + (K ε).1 *
        (A.refreshProbability * m.1 +
          2 * (1 - A.refreshProbability) * (b0 i).1))
      (oracleScale i))
    (hCommunication : AccuracyBigO
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    HeterogeneousFiniteSumMeasuredCostComplexity A x0 workerBatchLaw K
      accuracy iterationScale oracleScale communicationScale := by
  unfold HeterogeneousFiniteSumMeasuredCostComplexity
  refine ⟨hAccuracy, hIteration, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (heterogeneousFiniteSumWorkerOracleCost_integrable_and_expectation
      A workerBatchLaw hWorkerBatchLaw (K ε) i).1
  · rw [show (fun ε => ∫ path,
        heterogeneousFiniteSumWorkerOracleCost (Ξ := Ξ) (K ε) i path
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) =
        (fun ε => (m.1 : ℝ) + (K ε).1 *
          (A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * (b0 i).1)) by
      funext ε
      exact (heterogeneousFiniteSumWorkerOracleCost_integrable_and_expectation
        A workerBatchLaw hWorkerBatchLaw (K ε) i).2]
    exact hOracle i
  · intro ε
    exact
      (heterogeneousFiniteSumWorkerCommunicationCost_integrable_and_expectation_le
        A x0 workerBatchLaw hWorkerBatchLaw hQ (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hCommunication
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        heterogeneousFiniteSumWorkerCommunicationCost_nonneg
          A x0 (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability :=
        le_of_lt A.refresh_admissible.1
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact
        (heterogeneousFiniteSumWorkerCommunicationCost_integrable_and_expectation_le
          A x0 workerBatchLaw hWorkerBatchLaw hQ (K ε) i).2

/-- Source-specialized measured form of Remark D.1.  The convergence field,
workerwise oracle integral, and workerwise communication integral all use the
same heterogeneous finite-sum process and the canonical independent
worker-product path law.  In particular, the oracle scale retains each
worker's own `b0 i`, rather than replacing the schedule by a homogeneous
batch size. -/
theorem Remark_D1_heterogeneous_finite_batches_measured
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (hAverageSmooth : HeterogeneousFiniteSumAverageSmoothness A.problem b0
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
      (heterogeneousFiniteSumProcess (b0 := b0) A x0) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    let P := finiteSumLocalProblem A.problem
    let law := heterogeneousFiniteSumPathLaw A
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)
    let run := heterogeneousFiniteSumProcess (b0 := b0) A x0
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal + Real.sqrt
      ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
    ∃ K : Accuracy → Count,
      HeterogeneousFiniteSumMeasuredCostComplexity A x0 workerBatchLaw K
        (fun ε => NonconvexAccuracy (K ε) P run law ε)
        (fun ε => Δ / (ε : ℝ) ^ 2 * bracket)
        (fun i ε => m.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * m.1 +
            (1 - A.refreshProbability) * (b0 i).1))
        (fun ε => d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ)) := by
  dsimp
  have hSource := Remark_D1_heterogeneous_finite_batches
    A x0 workerBatchLaw Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw
      hAverageSmooth hQuantizer hStep
  rcases hSource.2 with ⟨K, hAccuracy, hIteration, hOracle, hCommunication⟩
  refine ⟨K, ?_⟩
  apply heterogeneousFiniteSumMeasuredCostComplexity_of_bounds
    A x0 workerBatchLaw hBatchLaw hQuantizer K _ _ _ _ hAccuracy hIteration
  · intro i
    simpa [heterogeneousFiniteSumOracleCallCount] using hOracle i
  · exact hCommunication

/-- D.1/D.2 with both generated per-worker costs: the oracle and
communication fields are integrals under the same `finiteSumPathLaw` as the
convergence field. -/
def FiniteSumMeasuredCostComplexity
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0) (K : Accuracy → Count)
    (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    ∀ i : Worker n,
      (∀ ε, Integrable (finiteSumWorkerOracleCost (Ξ := Ξ) (K ε) i)
        (finiteSumPathLaw A batchLaw)) ∧
      AccuracyBigO
        (fun ε => ∫ path, finiteSumWorkerOracleCost (Ξ := Ξ) (K ε) i path
          ∂finiteSumPathLaw A batchLaw) oracleScale ∧
      (∀ ε, Integrable (finiteSumWorkerCommunicationCost A x0 (K ε) i)
        (finiteSumPathLaw A batchLaw)) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          finiteSumWorkerCommunicationCost A x0 (K ε) i path
          ∂finiteSumPathLaw A batchLaw) communicationScale

/-- Transfer the proved D.1/D.2 schedule to exact measured oracle cost and
upper-bounded measured communication cost. -/
theorem finiteSumMeasuredCostComplexity_of_threeEndpoint
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K accuracy iterationScale
      (fun ε => finiteSumOracleCallCount m b0 (K ε) A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    FiniteSumMeasuredCostComplexity A x0 batchLaw K accuracy iterationScale
      oracleScale communicationScale := by
  unfold ThreeEndpointComplexity at hEndpoints
  unfold FiniteSumMeasuredCostComplexity
  refine ⟨hEndpoints.1, hEndpoints.2.1, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (finiteSumWorkerOracleCost_integrable_and_expectation
      A batchLaw hBatchLaw (K ε) i).1
  · rw [show (fun ε => ∫ path,
        finiteSumWorkerOracleCost (Ξ := Ξ) (K ε) i path
          ∂finiteSumPathLaw A batchLaw) =
        (fun ε => finiteSumOracleCallCount m b0 (K ε)
          A.refreshProbability) by
      funext ε
      exact (finiteSumWorkerOracleCost_integrable_and_expectation
        A batchLaw hBatchLaw (K ε) i).2]
    exact hEndpoints.2.2.1
  · intro ε
    exact (finiteSumWorkerCommunicationCost_integrable_and_expectation_le
      A x0 batchLaw hBatchLaw hQ (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hEndpoints.2.2.2
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        finiteSumWorkerCommunicationCost_nonneg A x0 (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability :=
        le_of_lt A.refresh_admissible.1
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact (finiteSumWorkerCommunicationCost_integrable_and_expectation_le
        A x0 batchLaw hBatchLaw hQ (K ε) i).2

/-- Measured public root for finite-sum Theorems D.1 and D.2. -/
theorem Theorem_D1_D2_measured_cost_complexity
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 xStar : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (Llocal ℒlocal : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (finiteSumLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (finiteSumLocalProblem A.problem) Llocal)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (hAverageSmooth : FiniteSumAverageSmoothness A.problem batchLaw
      (finiteSumProcess (b0 := b0) A x0) ℒlocal)
    (hPL : SatisfiesPL (finiteSumLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hStepNonconvex : FiniteSumVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (hStepPL : FiniteSumVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let ζ := expectedDensity A.quantizer
    let Δnc := globalObjective (finiteSumLocalProblem A.problem) x0 - fStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let Δpl := globalObjective (finiteSumLocalProblem A.problem) x0 -
      globalObjective (finiteSumLocalProblem A.problem) xStar
    let factor := max (1 / A.refreshProbability) (bracket / μ)
    (∃ K : Accuracy → Count,
      FiniteSumMeasuredCostComplexity A x0 batchLaw K
        (fun ε => NonconvexAccuracy (K ε)
          (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw) ε)
        (fun ε => Δnc / (ε : ℝ) ^ 2 * bracket)
        (fun ε => m.1 + Δnc / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * m.1 + (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + Δnc / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 + (1 - A.refreshProbability) * ζ))) ∧
    (∃ K : Accuracy → Count,
      FiniteSumMeasuredCostComplexity A x0 batchLaw K
        (fun ε => PLAccuracy (K ε) (finiteSumLocalProblem A.problem)
          (finiteSumProcess (b0 := b0) A x0) (finiteSumPathLaw A batchLaw)
          xStar ε)
        (fun ε => factor * Real.log (Δpl / (ε : ℝ)))
        (fun ε => m.1 + factor * (A.refreshProbability * m.1 +
          (1 - A.refreshProbability) * b0.1) * Real.log (Δpl / (ε : ℝ)))
        (fun ε => d.1 + factor * (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ) * Real.log (Δpl / (ε : ℝ)))) := by
  dsimp
  constructor
  · rcases Theorem_D1_finite_sum_VR_complexity_endpoints A x0 batchLaw
      Llocal ℒlocal ω fStar hLower hSmooth hBatchLaw hAverageSmooth
      hQuantizer hStepNonconvex with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    exact finiteSumMeasuredCostComplexity_of_threeEndpoint A x0 batchLaw
      hBatchLaw hQuantizer K _ _ _ _ hK
  · rcases Theorem_D2_finite_sum_VR_PL_complexity_endpoints A x0 xStar
      batchLaw Llocal ℒlocal ω fStar μ hLower hSmooth hBatchLaw
      hAverageSmooth hPL hQuantizer hStepPL with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    exact finiteSumMeasuredCostComplexity_of_threeEndpoint A x0 batchLaw
      hBatchLaw hQuantizer K _ _ _ _ hK

/-! ## Executable online accuracy-family accounting

The refresh batch in D.3/D.4 depends on the requested accuracy.  Consequently
the sample-path type, canonical law, and measured costs must all be instantiated
separately at that batch.  The following package deliberately accepts an
arbitrary accuracy proposition: its source-facing consumer must instantiate it
with `onlineProcess` and the same `onlinePathLaw` displayed in the cost fields.
It cannot be applied directly to the proof-exact initialization endpoints. -/

/-- Every realized executable online per-worker communication count is
nonnegative. -/
theorem onlineWorkerCommunicationCost_nonneg
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (K : Count) (i : Worker n)
    (path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) :
    0 ≤ onlineWorkerCommunicationCost A x0 hBatch K i path := by
  unfold onlineWorkerCommunicationCost
  apply add_nonneg <;> try positivity
  apply Finset.sum_nonneg
  intro k hk
  split <;> try positivity
  unfold quantizerNonzeroCount
  positivity

/-- Accuracy-indexed executable Algorithm 3 costs.  For each accuracy, the
oracle and communication integrals are over the full experiment containing the
actual `b ε` initialization samples and the round stream used by
`onlineProcess`. -/
def OnlineMeasuredCostComplexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    ∀ i : Worker n,
      (∀ ε, Integrable
        (onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) (K ε) i)
        (onlinePathLaw (b := b ε) (b0 := b0) A)) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) (K ε) i path
            ∂onlinePathLaw (b := b ε) (b0 := b0) A)
        oracleScale ∧
      (∀ ε, Integrable
        (onlineWorkerCommunicationCost A x0 (hBatch ε) (K ε) i)
        (onlinePathLaw (b := b ε) (b0 := b0) A)) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          onlineWorkerCommunicationCost A x0 (hBatch ε) (K ε) i path
            ∂onlinePathLaw (b := b ε) (b0 := b0) A)
        communicationScale

/-- The executable nonconvex specialization of `OnlineMeasuredCostComplexity`.
Unlike the generic accounting package, this definition fixes the accuracy
object to the generated sampled-initializer process on the same full
`onlinePathLaw` that appears in both measured cost integrals. -/
def OnlineExecutableNonconvexMeasuredCostComplexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ) : Prop :=
  OnlineMeasuredCostComplexity A x0 b hBatch K
    (fun ε => NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ε)
    iterationScale oracleScale communicationScale

/-- The executable PŁ specialization of `OnlineMeasuredCostComplexity`.
The sampled `b ε` initializer, generated process, convergence law, and both
cost laws are definitionally the same experiment. -/
def OnlineExecutablePLMeasuredCostComplexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ) : Prop :=
  OnlineMeasuredCostComplexity A x0 b hBatch K
    (fun ε => PLAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) xStar ε)
    iterationScale oracleScale communicationScale

/-! The density/batch choices in Corollaries D.3 and D.4 vary the refresh
probability and the stepsize with the requested accuracy.  Consequently a
single fixed `OnlineData` cannot name all of the canonical experiments.  The
following package is the parameter-varying analogue of
`OnlineMeasuredCostComplexity`; every accuracy uses the process, full path
law, and costs belonging to that accuracy's `OnlineData`. -/

/-- Accuracy-indexed executable Algorithm 3 accounting when the algorithm
parameters themselves depend on the requested accuracy. -/
def OnlineParameterizedMeasuredCostComplexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : Accuracy → OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ) : Prop :=
  (∀ ε, accuracy ε) ∧
    AccuracyIterationBigO (fun ε => (K ε).1) iterationScale ∧
    ∀ i : Worker n,
      (∀ ε, Integrable
        (onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) (K ε) i)
        (onlinePathLaw (b := b ε) (b0 := b0) (A ε))) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) (K ε) i path
            ∂onlinePathLaw (b := b ε) (b0 := b0) (A ε))
        oracleScale ∧
      (∀ ε, Integrable
        (onlineWorkerCommunicationCost (A ε) x0 (hBatch ε) (K ε) i)
        (onlinePathLaw (b := b ε) (b0 := b0) (A ε))) ∧
      AccuracyBigO
        (fun ε => ∫ path,
          onlineWorkerCommunicationCost (A ε) x0 (hBatch ε) (K ε) i path
            ∂onlinePathLaw (b := b ε) (b0 := b0) (A ε))
        communicationScale

/-- Nonconvex parameter-varying specialization.  Its accuracy predicate and
both measured costs use definitionally the same sampled-initializer law. -/
def OnlineParameterizedExecutableNonconvexMeasuredCostComplexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : Accuracy → OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ) : Prop :=
  OnlineParameterizedMeasuredCostComplexity A x0 b hBatch K
    (fun ε => NonconvexAccuracy (K ε) (onlineLocalProblem (A ε).problem)
      (onlineProcess (A ε) x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) (A ε)) ε)
    iterationScale oracleScale communicationScale

/-- PŁ parameter-varying specialization, again retaining the full sampled
initializer in the process and in both measured cost laws. -/
def OnlineParameterizedExecutablePLMeasuredCostComplexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : Accuracy → OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ) : Prop :=
  OnlineParameterizedMeasuredCostComplexity A x0 b hBatch K
    (fun ε => PLAccuracy (K ε) (onlineLocalProblem (A ε).problem)
      (onlineProcess (A ε) x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) (A ε)) xStar ε)
    iterationScale oracleScale communicationScale

/-- Lift parameter-varying executable convergence and scalar analytic bounds
to integrals of the actual oracle-call and transmitted-coordinate random
variables.  The scalar counters remain intermediate bounds only. -/
theorem onlineParameterizedMeasuredCostComplexity_of_threeEndpoint
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : Accuracy → OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCommunicationAELawRegularity (A ε) x0 (hBatch ε))
    {ω : ℝ} (hQ : ∀ ε, IsUnbiasedQuantizer (A ε).quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K accuracy iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        (A ε).refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        (A ε).refreshProbability (expectedDensity (A ε).quantizer))
      communicationScale) :
    OnlineParameterizedMeasuredCostComplexity A x0 b hBatch K accuracy
      iterationScale oracleScale communicationScale := by
  unfold ThreeEndpointComplexity at hEndpoints
  unfold OnlineParameterizedMeasuredCostComplexity
  refine ⟨hEndpoints.1, hEndpoints.2.1, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (onlineWorkerOracleCost_integrable_and_expectation
      (b := b ε) (b0 := b0) (A ε) (K ε) i).1
  · rw [show (fun ε => ∫ path,
        onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂onlinePathLaw (b := b ε) (b0 := b0) (A ε)) =
        (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
          (A ε).refreshProbability) by
      funext ε
      exact (onlineWorkerOracleCost_integrable_and_expectation
        (b := b ε) (b0 := b0) (A ε) (K ε) i).2]
    exact hEndpoints.2.2.1
  · intro ε
    exact
      (onlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
        (b := b ε) (b0 := b0) (A ε) x0 (hBatch ε) (hCostMeas ε)
        (hQ ε) (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hEndpoints.2.2.2
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        onlineWorkerCommunicationCost_nonneg (A ε) x0
          (hBatch ε) (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity (A ε).quantizer :=
        expectedDensity_nonneg_of_unbiased (hQ ε)
      have hp0 : 0 ≤ (A ε).refreshProbability :=
        le_of_lt (A ε).refresh_admissible.1
      have hp1 : 0 ≤ 1 - (A ε).refreshProbability :=
        sub_nonneg.mpr (A ε).refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact
        (onlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
          (b := b ε) (b0 := b0) (A ε) x0 (hBatch ε) (hCostMeas ε)
          (hQ ε) (K ε) i).2

/-- Source-facing parameter-varying lift for `onlineDataWithParameters`.
The law-scoped regularity of every actual adaptive message is derived from
the source moment and smoothness hypotheses; it is not an added cost premise. -/
theorem onlineParameterizedMeasuredCostComplexity_of_source
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (γ : Accuracy → PositiveStepsize) (p : Accuracy → ℝ)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (b : Accuracy → Count) (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 (hBatch ε))
        ℒlocal)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K accuracy iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        (onlineDataWithParameters A (γ ε) (p ε) (hp ε)).refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        (onlineDataWithParameters A (γ ε) (p ε) (hp ε)).refreshProbability
        (expectedDensity
          (onlineDataWithParameters A (γ ε) (p ε) (hp ε)).quantizer))
      communicationScale) :
    OnlineParameterizedMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (γ ε) (p ε) (hp ε))
      x0 b hBatch K accuracy iterationScale oracleScale communicationScale := by
  apply onlineParameterizedMeasuredCostComplexity_of_threeEndpoint
  · intro ε
    exact onlineCommunicationAELawRegularity_of_source
      (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0
      Llocal ℒlocal σ ω
      (by simpa [onlineDataWithParameters] using hSmooth)
      (by simpa [onlineDataWithParameters] using hVariance)
      (by simpa [onlineDataWithParameters] using hQuantizer)
      (hBatch ε)
      (by simpa [onlineDataWithParameters] using hAverageSmooth ε)
  · intro ε
    simpa [onlineDataWithParameters] using hQuantizer
  · exact hEndpoints

/-- Lift an executable online convergence/iteration schedule to the measured
oracle and communication costs on exactly the same accuracy-indexed canonical
experiments.  The scalar count expressions are used only as analytic
intermediate bounds. -/
theorem onlineMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCommunicationAELawRegularity A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K accuracy iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε) A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    OnlineMeasuredCostComplexity A x0 b hBatch K accuracy iterationScale
      oracleScale communicationScale := by
  unfold ThreeEndpointComplexity at hEndpoints
  unfold OnlineMeasuredCostComplexity
  refine ⟨hEndpoints.1, hEndpoints.2.1, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (onlineWorkerOracleCost_integrable_and_expectation
      (b := b ε) (b0 := b0) A (K ε) i).1
  · rw [show (fun ε => ∫ path,
        onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂onlinePathLaw (b := b ε) (b0 := b0) A) =
        (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
          A.refreshProbability) by
      funext ε
      exact (onlineWorkerOracleCost_integrable_and_expectation
        (b := b ε) (b0 := b0) A (K ε) i).2]
    exact hEndpoints.2.2.1
  · intro ε
    exact
      (onlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
        (b := b ε) (b0 := b0) A x0 (hBatch ε) (hCostMeas ε)
        hQ (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hEndpoints.2.2.2
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path =>
        onlineWorkerCommunicationCost_nonneg A x0 (hBatch ε) (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability :=
        le_of_lt A.refresh_admissible.1
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact
        (onlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
          (b := b ε) (b0 := b0) A x0 (hBatch ε) (hCostMeas ε)
          hQ (K ε) i).2

/-- Compatibility lift from the former strict generated-message interface. -/
theorem onlineMeasuredCostComplexity_of_threeEndpoint_of_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCommunicationLawRegularity A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K accuracy iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε) A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    OnlineMeasuredCostComplexity A x0 b hBatch K accuracy iterationScale
      oracleScale communicationScale := by
  apply onlineMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 b hBatch
  · intro ε
    exact onlineCommunicationAELawRegularity_of_lawRegularity
      A x0 (hBatch ε) (hCostMeas ε)
  · exact hQ
  · exact hEndpoints

/-- Backward-compatible lift from the former global generated-cost
measurability contract. -/
theorem onlineMeasuredCostComplexity_of_threeEndpoint_of_cost_measurability
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCostMeasurability A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K accuracy iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε) A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    OnlineMeasuredCostComplexity A x0 b hBatch K accuracy iterationScale
      oracleScale communicationScale := by
  apply onlineMeasuredCostComplexity_of_threeEndpoint_of_law_regularity
    A x0 b hBatch
  · intro ε
    exact onlineCommunicationLawRegularity_of_costMeasurability
      A x0 (hBatch ε) (hCostMeas ε)
  · exact hQ
  · exact hEndpoints

/-- Same-process nonconvex lift for executable Algorithm 3.  In contrast to
the generic helper above, the premise and conclusion both expose the actual
sampled-initializer process and its full canonical law, so this theorem cannot
be instantiated with a proof-exact accuracy proposition. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCommunicationAELawRegularity A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K
      (fun ε => NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch ε))
        (onlinePathLaw (b := b ε) (b0 := b0) A) ε)
      iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        A.refreshProbability (expectedDensity A.quantizer))
      communicationScale) :
    OnlineExecutableNonconvexMeasuredCostComplexity A x0 b hBatch K
      iterationScale oracleScale communicationScale := by
  exact onlineMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 b hBatch hCostMeas hQ K _ iterationScale oracleScale
      communicationScale hEndpoints

/-- Compatibility nonconvex lift from strict generated-message regularity. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint_of_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCommunicationLawRegularity A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K
      (fun ε => NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch ε))
        (onlinePathLaw (b := b ε) (b0 := b0) A) ε)
      iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        A.refreshProbability (expectedDensity A.quantizer))
      communicationScale) :
    OnlineExecutableNonconvexMeasuredCostComplexity A x0 b hBatch K
      iterationScale oracleScale communicationScale := by
  apply onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 b hBatch
  · intro ε
    exact onlineCommunicationAELawRegularity_of_lawRegularity
      A x0 (hBatch ε) (hCostMeas ε)
  · exact hQ
  · exact hEndpoints

/-- Backward-compatible nonconvex lift under `OnlineCostMeasurability`. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCostMeasurability A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K
      (fun ε => NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch ε))
        (onlinePathLaw (b := b ε) (b0 := b0) A) ε)
      iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        A.refreshProbability) oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        A.refreshProbability (expectedDensity A.quantizer)) communicationScale) :
    OnlineExecutableNonconvexMeasuredCostComplexity A x0 b hBatch K
      iterationScale oracleScale communicationScale := by
  apply onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint_of_law_regularity
    A x0 b hBatch
  · intro ε
    exact onlineCommunicationLawRegularity_of_costMeasurability
      A x0 (hBatch ε) (hCostMeas ε)
  · exact hQ
  · exact hEndpoints

/-- Same-process PŁ lift for executable Algorithm 3.  In particular, its
oracle integral includes the sampled `b ε` initialization only because the
accuracy statement here also names `onlineProcess`, never the exact-gradient
`onlineProofExactProcess`. -/
theorem onlineExecutablePLMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCommunicationAELawRegularity A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K
      (fun ε => PLAccuracy (K ε) (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch ε))
        (onlinePathLaw (b := b ε) (b0 := b0) A) xStar ε)
      iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        A.refreshProbability (expectedDensity A.quantizer))
      communicationScale) :
    OnlineExecutablePLMeasuredCostComplexity A x0 xStar b hBatch K
      iterationScale oracleScale communicationScale := by
  exact onlineMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 b hBatch hCostMeas hQ K _ iterationScale oracleScale
      communicationScale hEndpoints

/-- Compatibility PŁ lift from strict generated-message regularity. -/
theorem onlineExecutablePLMeasuredCostComplexity_of_threeEndpoint_of_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCommunicationLawRegularity A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K
      (fun ε => PLAccuracy (K ε) (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch ε))
        (onlinePathLaw (b := b ε) (b0 := b0) A) xStar ε)
      iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        A.refreshProbability (expectedDensity A.quantizer))
      communicationScale) :
    OnlineExecutablePLMeasuredCostComplexity A x0 xStar b hBatch K
      iterationScale oracleScale communicationScale := by
  apply onlineExecutablePLMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 xStar b hBatch
  · intro ε
    exact onlineCommunicationAELawRegularity_of_lawRegularity
      A x0 (hBatch ε) (hCostMeas ε)
  · exact hQ
  · exact hEndpoints

/-- Backward-compatible PŁ lift under `OnlineCostMeasurability`. -/
theorem onlineExecutablePLMeasuredCostComplexity_of_threeEndpoint
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hCostMeas : ∀ ε, OnlineCostMeasurability A x0 (hBatch ε))
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K
      (fun ε => PLAccuracy (K ε) (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch ε))
        (onlinePathLaw (b := b ε) (b0 := b0) A) xStar ε)
      iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε)
        A.refreshProbability) oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε)
        A.refreshProbability (expectedDensity A.quantizer)) communicationScale) :
    OnlineExecutablePLMeasuredCostComplexity A x0 xStar b hBatch K
      iterationScale oracleScale communicationScale := by
  apply onlineExecutablePLMeasuredCostComplexity_of_threeEndpoint_of_law_regularity
    A x0 xStar b hBatch
  · intro ε
    exact onlineCommunicationLawRegularity_of_costMeasurability
      A x0 (hBatch ε) (hCostMeas ε)
  · exact hQ
  · exact hEndpoints

/-- Compatibility lift under the older global stochastic-gradient kernel
premise.  Source-facing measured endpoints can instead use the narrower
accuracy-indexed `OnlineCommunicationLawRegularity` contract above. -/
theorem onlineMeasuredCostComplexity_of_threeEndpoint
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (x0 : Point d) (b : Accuracy → Count)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hEndpoints : ThreeEndpointComplexity K accuracy iterationScale
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε) A.refreshProbability)
      oracleScale
      (fun ε => allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    OnlineMeasuredCostComplexity A x0 b hBatch K accuracy iterationScale
      oracleScale communicationScale := by
  apply onlineMeasuredCostComplexity_of_threeEndpoint_of_law_regularity
    A x0 b hBatch
  · intro ε
    exact onlineCommunicationLawRegularity_of_costMeasurability A x0 (hBatch ε)
      (onlineCostMeasurability_of_kernel A hKernel x0 (hBatch ε))
  · exact hQ
  · exact hEndpoints

/-- The executable D.3 boundary implies the requested nonconvex accuracy once
the iteration, initialization, and steady-state terms fit the accuracy budget.
The initial-error term is discharged from the canonical minibatch law rather
than postulated. -/
theorem onlineExecutableNonconvexAccuracy_of_budget
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ ((onlineLocalProblem A.problem).localLoss i))
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (ε : Accuracy)
    (hBudget :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        (varianceAggregateSq σ / (n.1 * b.1)) /
          (A.refreshProbability * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) ≤ (ε : ℝ) ^ 2) :
    NonconvexAccuracy K (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ε := by
  unfold NonconvexAccuracy
  have hBoundary :=
    Theorem_D3_online_VR_nonconvex_initialization_corrected_literal_source_boundary
      (K := K) A x0 Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
      hQuantizer hBatch hAverageSmooth hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedOnlineInitialEstimatorErrorSq_le
    (b := b) A x0 σ hVariance hDiff
  have hdenom : 0 ≤ (A.refreshProbability : ℝ) * K.1 :=
    mul_nonneg A.refresh_admissible.1.le (by positivity)
  have hInitialDiv :
      expectedOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) ≤
        (varianceAggregateSq σ / (n.1 * b.1)) /
          (A.refreshProbability * K.1) :=
    div_le_div_of_nonneg_right hInitial hdenom
  calc
    2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        expectedOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) ≤
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        (varianceAggregateSq σ / (n.1 * b.1)) /
          (A.refreshProbability * K.1) +
        varianceAggregateSq σ / (n.1 * b.1) := by gcongr
    _ ≤ (ε : ℝ) ^ 2 := hBudget

/-- The analogous executable D.4 bridge.  The coefficient of the initial
estimator error is nonnegative by the PL stepsize condition, so the proved
minibatch variance bound can be substituted monotonically. -/
theorem onlineExecutablePLAccuracy_of_budget
    {d n b b0 K : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ ((onlineLocalProblem A.problem).localLoss i))
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAverageSmooth : OnlineAverageSmoothness (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0)
    (ε : Accuracy)
    (hBudget :
      (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability *
            (varianceAggregateSq σ / (n.1 * b.1)) +
        varianceAggregateSq σ / (n.1 * b.1 * μ) ≤ (ε : ℝ)) :
    PLAccuracy K (onlineLocalProblem A.problem)
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) xStar ε := by
  unfold PLAccuracy
  have hBoundary :=
    Theorem_D4_online_VR_PL_initialization_corrected_literal_source_boundary
      (K := K) A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hVariance hPL hQuantizer hBatch hAverageSmooth hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedOnlineInitialEstimatorErrorSq_le
    (b := b) A x0 σ hVariance hDiff
  have hContraction : 0 ≤ 1 - (A.stepSize : ℝ) * (μ : ℝ) := by
    apply sub_nonneg.mpr
    have hp1 := A.refresh_admissible.2
    nlinarith [hStep.2]
  have hCoefficient : 0 ≤
      (1 - (A.stepSize : ℝ) * (μ : ℝ)) ^ K.1 * A.stepSize /
        A.refreshProbability :=
    div_nonneg
      (mul_nonneg (pow_nonneg hContraction K.1) A.stepSize.property.le)
      A.refresh_admissible.1.le
  have hInitialMul := mul_le_mul_of_nonneg_left hInitial hCoefficient
  calc
    (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability * expectedOnlineInitialEstimatorErrorSq (b := b) A x0 +
        varianceAggregateSq σ / (n.1 * b.1 * μ) ≤
      (1 - A.stepSize * μ) ^ K.1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ K.1 * A.stepSize /
          A.refreshProbability * (varianceAggregateSq σ / (n.1 * b.1)) +
        varianceAggregateSq σ / (n.1 * b.1 * μ) := by gcongr
    _ ≤ (ε : ℝ) := hBudget

/-- Accuracy-family form of the executable D.3 initialization correction.
All varying batch types and laws are instantiated pointwise, and the only
extra hypothesis is the displayed scalar budget obtained by allocating the
source optimization, initial-estimator, and variance terms. -/
theorem onlineExecutableNonconvexAccuracy_family_of_budget
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0 (hBatch ε)) ℒlocal)
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (hBudget : ∀ ε,
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * (K ε).1) +
        (varianceAggregateSq σ / (n.1 * (b ε).1)) /
          (A.refreshProbability * (K ε).1) +
        varianceAggregateSq σ / (n.1 * (b ε).1) ≤ (ε : ℝ) ^ 2) :
    ∀ ε, NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ε := by
  intro ε
  exact onlineExecutableNonconvexAccuracy_of_budget A x0 Llocal ℒlocal σ
    ω fStar hLower hSmooth hVariance hSmooth.1 hQuantizer (hBatch ε)
    (hAverageSmooth ε) hStep ε (hBudget ε)

/-- Accuracy-family form of the executable D.4 initialization correction.
The decaying initial-estimator term is budgeted on the same sampled path law
as the terminal iterate and remains separate from proof-exact convergence. -/
theorem onlineExecutablePLAccuracy_family_of_budget
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0 (hBatch ε)) ℒlocal)
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0)
    (hBudget : ∀ ε,
      (1 - A.stepSize * μ) ^ (K ε).1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - A.stepSize * μ) ^ (K ε).1 * A.stepSize /
          A.refreshProbability *
            (varianceAggregateSq σ / (n.1 * (b ε).1)) +
        varianceAggregateSq σ / (n.1 * (b ε).1 * μ) ≤ (ε : ℝ)) :
    ∀ ε, PLAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) xStar ε := by
  intro ε
  exact onlineExecutablePLAccuracy_of_budget A x0 xStar Llocal ℒlocal σ
    ω fStar μ hLower hSmooth hVariance hSmooth.1 hPL hQuantizer
    (hBatch ε) (hAverageSmooth ε) hStep ε (hBudget ε)

/-! The source density schedules vary both the refresh probability and the
stepsize with accuracy.  The next two bridges are the parameter-varying
counterparts of the fixed-data executable budget lemmas above.  Their scalar
budget hypotheses display, rather than hide, the extra sampled-initializer
term.  In particular they cannot be instantiated by the proof-exact D.3/D.4
accuracy statements alone. -/

/-- Parameter-varying executable D.3 accuracy from the initialization-aware
scalar budget on the same `onlinePathLaw` experiment. -/
theorem onlineParameterizedExecutableNonconvexAccuracy_family_of_budget
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (γ : Accuracy → PositiveStepsize) (p : Accuracy → ℝ)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 (hBatch ε))
        ℒlocal)
    (hStep : ∀ ε, OnlineVRStepsizeCondition (γ ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0)
    (hBudget : ∀ ε,
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          ((γ ε : ℝ) * (K ε).1) +
        (varianceAggregateSq σ / (n.1 * (b ε).1)) /
          (p ε * (K ε).1) +
        varianceAggregateSq σ / (n.1 * (b ε).1) ≤ (ε : ℝ) ^ 2) :
    ∀ ε, NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess
        (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0)
        (onlineDataWithParameters A (γ ε) (p ε) (hp ε))) ε := by
  intro ε
  apply onlineExecutableNonconvexAccuracy_of_budget
    (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0
      Llocal ℒlocal σ ω fStar
  · simpa [onlineDataWithParameters] using hLower
  · simpa [onlineDataWithParameters] using hSmooth
  · simpa [onlineDataWithParameters] using hVariance
  · simpa [onlineDataWithParameters] using hSmooth.1
  · simpa [onlineDataWithParameters] using hQuantizer
  · simpa [onlineDataWithParameters] using hAverageSmooth ε
  · simpa [onlineDataWithParameters] using hStep ε
  · simpa [onlineDataWithParameters] using hBudget ε

/-- Parameter-varying executable D.4 accuracy from the corresponding
initialization-aware PŁ budget. -/
theorem onlineParameterizedExecutablePLAccuracy_family_of_budget
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (γ : Accuracy → PositiveStepsize) (p : Accuracy → ℝ)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 (hBatch ε))
        ℒlocal)
    (hStep : ∀ ε, OnlineVRPLStepsizeCondition (γ ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
    (hBudget : ∀ ε,
      (1 - (γ ε : ℝ) * (μ : ℝ)) ^ (K ε).1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - (γ ε : ℝ) * (μ : ℝ)) ^ (K ε).1 * (γ ε : ℝ) /
          (p ε) * (varianceAggregateSq σ / (n.1 * (b ε).1)) +
        varianceAggregateSq σ / (n.1 * (b ε).1 * (μ : ℝ)) ≤ (ε : ℝ)) :
    ∀ ε, PLAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess
        (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0)
        (onlineDataWithParameters A (γ ε) (p ε) (hp ε))) xStar ε := by
  intro ε
  apply onlineExecutablePLAccuracy_of_budget
    (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 xStar
      Llocal ℒlocal σ ω fStar μ
  · simpa [onlineDataWithParameters] using hLower
  · simpa [onlineDataWithParameters] using hSmooth
  · simpa [onlineDataWithParameters] using hVariance
  · simpa [onlineDataWithParameters] using hSmooth.1
  · simpa [onlineDataWithParameters] using hPL
  · simpa [onlineDataWithParameters] using hQuantizer
  · simpa [onlineDataWithParameters] using hAverageSmooth ε
  · simpa [onlineDataWithParameters] using hStep ε
  · simpa [onlineDataWithParameters] using hBudget ε

/-- Assemble a parameter-varying executable D.3 measured endpoint once the
displayed initialization-aware scalar budget and the three analytic scales
have been proved.  The conclusion integrates the actual oracle and message
costs under exactly the law used by its accuracy field. -/
theorem onlineParameterizedExecutableNonconvexMeasuredCostComplexity_of_budget
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (γ : Accuracy → PositiveStepsize) (p : Accuracy → ℝ)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 (hBatch ε))
        ℒlocal)
    (hStep : ∀ ε, OnlineVRStepsizeCondition (γ ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω n b0)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hBudget : ∀ ε,
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          ((γ ε : ℝ) * (K ε).1) +
        (varianceAggregateSq σ / (n.1 * (b ε).1)) /
          (p ε * (K ε).1) +
        varianceAggregateSq σ / (n.1 * (b ε).1) ≤ (ε : ℝ) ^ 2)
    (hIteration : AccuracyIterationBigO (fun ε => ((K ε).1 : ℝ))
      iterationScale)
    (hOracle : AccuracyBigO
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε) (p ε)) oracleScale)
    (hCommunication : AccuracyBigO
      (fun ε => allWorkerCommunicationCount d (K ε) (p ε)
        (expectedDensity A.quantizer)) communicationScale) :
    OnlineParameterizedExecutableNonconvexMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (γ ε) (p ε) (hp ε))
      x0 b hBatch K iterationScale oracleScale communicationScale := by
  unfold OnlineParameterizedExecutableNonconvexMeasuredCostComplexity
  apply onlineParameterizedMeasuredCostComplexity_of_source
    A x0 γ p hp b hBatch Llocal ℒlocal σ ω hSmooth hVariance
      hQuantizer hAverageSmooth K _ iterationScale oracleScale communicationScale
  unfold ThreeEndpointComplexity
  refine ⟨?_, hIteration, hOracle, hCommunication⟩
  exact onlineParameterizedExecutableNonconvexAccuracy_family_of_budget
    A x0 γ p hp b K Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
      hQuantizer hBatch hAverageSmooth hStep hBudget

/-- PŁ counterpart of the parameter-varying measured D.3 constructor. -/
theorem onlineParameterizedExecutablePLMeasuredCostComplexity_of_budget
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (γ : Accuracy → PositiveStepsize) (p : Accuracy → ℝ)
    (hp : ∀ ε, RefreshProbabilityAdmissible (p ε))
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A (γ ε) (p ε) (hp ε)) x0 (hBatch ε))
        ℒlocal)
    (hStep : ∀ ε, OnlineVRPLStepsizeCondition (γ ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (p ε) ω μ n b0)
    (iterationScale oracleScale communicationScale : Accuracy → ℝ)
    (hBudget : ∀ ε,
      (1 - (γ ε : ℝ) * (μ : ℝ)) ^ (K ε).1 *
          (globalObjective (onlineLocalProblem A.problem) x0 -
            globalObjective (onlineLocalProblem A.problem) xStar) +
        (1 - (γ ε : ℝ) * (μ : ℝ)) ^ (K ε).1 * (γ ε : ℝ) /
          (p ε) * (varianceAggregateSq σ / (n.1 * (b ε).1)) +
        varianceAggregateSq σ / (n.1 * (b ε).1 * (μ : ℝ)) ≤ (ε : ℝ))
    (hIteration : AccuracyIterationBigO (fun ε => ((K ε).1 : ℝ))
      iterationScale)
    (hOracle : AccuracyBigO
      (fun ε => onlineOracleCallCount (b ε) b0 (K ε) (p ε)) oracleScale)
    (hCommunication : AccuracyBigO
      (fun ε => allWorkerCommunicationCount d (K ε) (p ε)
        (expectedDensity A.quantizer)) communicationScale) :
    OnlineParameterizedExecutablePLMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (γ ε) (p ε) (hp ε))
      x0 xStar b hBatch K iterationScale oracleScale communicationScale := by
  unfold OnlineParameterizedExecutablePLMeasuredCostComplexity
  apply onlineParameterizedMeasuredCostComplexity_of_source
    A x0 γ p hp b hBatch Llocal ℒlocal σ ω hSmooth hVariance
      hQuantizer hAverageSmooth K _ iterationScale oracleScale communicationScale
  unfold ThreeEndpointComplexity
  refine ⟨?_, hIteration, hOracle, hCommunication⟩
  exact onlineParameterizedExecutablePLAccuracy_family_of_budget
    A x0 xStar γ p hp b K Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hVariance hPL hQuantizer hBatch hAverageSmooth hStep hBudget

/-! The source D.3 density schedule chooses the refresh batch before choosing
the horizon.  For the executable sampled initializer it is therefore preferable
to enlarge the horizon, rather than silently replace that batch by the
`1 / p`-inflated batch used by the fixed-parameter compatibility result below.
The second ceiling pays exactly for the additional `V / (p K)` term. -/

/-- A positive `Count`-valued batch family cannot have the source
`AccuracyTheta` order when the advertised variance scale is identically zero.
This records the degenerate-schedule obstruction explicitly; a zero-variance
endpoint must use a nonzero corrected batch scale rather than retain an
inconsistent `Theta(0)` premise. -/
theorem count_batch_accuracyTheta_zero_impossible
    (batch : Accuracy → Count) :
    ¬ AccuracyTheta (fun ε => ((batch ε).1 : ℝ))
      (fun _ : Accuracy => (0 : ℝ)) := by
  intro hTheta
  have hEventuallyZero :
      ∀ᶠ ε in accuracyToZero, ((batch ε).1 : ℝ) = 0 := by
    exact Asymptotics.isBigO_zero_right_iff.mp hTheta.1
  rw [accuracyToZero, Filter.eventually_comap] at hEventuallyZero
  rcases Filter.eventually_atTop.1 hEventuallyZero with ⟨a, ha⟩
  let x : ℝ := max 1 a
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let ε : Accuracy := ⟨1 / x, one_div_pos.mpr hx⟩
  have hInv : ((ε : ℝ)⁻¹) = x := by
    dsimp [ε]
    simp
  have hzeroBatch := ha x (le_max_right _ _) ε hInv
  have hpositiveBatch : 0 < ((batch ε).1 : ℝ) := by
    exact_mod_cast (batch ε).2
  exact (ne_of_gt hpositiveBatch) hzeroBatch

/-- A finite executable D.3 horizon which separately budgets optimization and
sampled-initializer error.  The batch and refresh probability remain the ones
chosen by the source density/batch schedule. -/
noncomputable def onlineExecutableNonconvexScheduledHorizon
    (gap variance : ℝ) (step : Accuracy → PositiveStepsize)
    (refresh : Accuracy → ℝ) (n : Count) (batch : Accuracy → Count) :
    Accuracy → Count := fun ε =>
  ⟨max 1 (Nat.ceil (max
    (8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2))
    (4 * (variance / (n.1 * (batch ε).1)) /
      (refresh ε * (ε : ℝ) ^ 2)))), by omega⟩

/-- The constructed scheduled horizon discharges the full executable D.3
three-term budget whenever the source refresh batch supplies its usual
pointwise variance floor.  No expectation or convergence conclusion is assumed
here: the proof is the scalar allocation `1/4 + 1/4 + 1/2`. -/
theorem onlineExecutableNonconvexScheduledHorizon_budget
    {n : Count} (gap variance : ℝ) (step : Accuracy → PositiveStepsize)
    (refresh : Accuracy → ℝ) (batch : Accuracy → Count)
    (hgap : 0 ≤ gap) (hvariance : 0 ≤ variance)
    (hrefresh : ∀ ε, 0 < refresh ε)
    (hfloor : ∀ ε, variance / (n.1 * (batch ε).1) ≤ (ε : ℝ) ^ 2 / 2) :
    ∀ ε,
      2 * gap /
          ((step ε : ℝ) *
            (onlineExecutableNonconvexScheduledHorizon
              gap variance step refresh n batch ε).1) +
        (variance / (n.1 * (batch ε).1)) /
          (refresh ε *
            (onlineExecutableNonconvexScheduledHorizon
              gap variance step refresh n batch ε).1) +
        variance / (n.1 * (batch ε).1) ≤ (ε : ℝ) ^ 2 := by
  intro ε
  let initialVariance : ℝ := variance / (n.1 * (batch ε).1)
  let optimizationQuota : ℝ :=
    8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2)
  let initializationQuota : ℝ :=
    4 * initialVariance / (refresh ε * (ε : ℝ) ^ 2)
  let horizon : Count :=
    onlineExecutableNonconvexScheduledHorizon
      gap variance step refresh n batch ε
  have hstep : 0 < (step ε : ℝ) := (step ε).property
  have hepsSq : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos ε.property
  have hrefreshε : 0 < refresh ε := hrefresh ε
  have hhorizon : 0 < ((horizon.1 : ℕ) : ℝ) := by
    exact_mod_cast horizon.2
  have hinitialVariance : 0 ≤ initialVariance := by
    dsimp [initialVariance]
    exact div_nonneg hvariance (by positivity)
  have hoptimizationQuota : 0 ≤ optimizationQuota := by
    dsimp [optimizationQuota]
    positivity
  have hinitializationQuota : 0 ≤ initializationQuota := by
    dsimp [initializationQuota]
    positivity
  have hceiling : max optimizationQuota initializationQuota ≤
      ((horizon.1 : ℕ) : ℝ) := by
    have h := le_positive_ceil_max_one
      (max optimizationQuota initializationQuota)
    simpa [horizon, onlineExecutableNonconvexScheduledHorizon,
      optimizationQuota, initializationQuota, initialVariance] using h
  have hoptimizationHorizon : optimizationQuota ≤
      ((horizon.1 : ℕ) : ℝ) :=
    (le_max_left _ _).trans hceiling
  have hinitializationHorizon : initializationQuota ≤
      ((horizon.1 : ℕ) : ℝ) :=
    (le_max_right _ _).trans hceiling
  have hoptimization :
      2 * gap / ((step ε : ℝ) * (horizon.1 : ℝ)) ≤
        (ε : ℝ) ^ 2 / 4 := by
    rw [div_le_iff₀ (mul_pos hstep hhorizon)]
    dsimp [optimizationQuota] at hoptimizationHorizon
    rw [div_le_iff₀ (mul_pos hstep hepsSq)] at hoptimizationHorizon
    nlinarith
  have hinitialization :
      initialVariance / (refresh ε * (horizon.1 : ℝ)) ≤
        (ε : ℝ) ^ 2 / 4 := by
    rw [div_le_iff₀ (mul_pos hrefreshε hhorizon)]
    dsimp [initializationQuota] at hinitializationHorizon
    rw [div_le_iff₀ (mul_pos hrefreshε hepsSq)] at hinitializationHorizon
    nlinarith
  have hsteady : initialVariance ≤ (ε : ℝ) ^ 2 / 2 := by
    simpa [initialVariance] using hfloor ε
  change 2 * gap / ((step ε : ℝ) * (horizon.1 : ℝ)) +
      initialVariance / (refresh ε * (horizon.1 : ℝ)) +
        initialVariance ≤ (ε : ℝ) ^ 2
  linarith

/-- Source-schedule specialization of the executable D.3 budget.  The batch is
the pointwise-safe Eq. (41) inflation and `refresh` is required to be exactly
the paper's density/batch minimum for that executed batch. -/
theorem onlineExecutableNonconvexDensityScheduled_budget
    {d n b0 : Count} (gap variance : ℝ)
    (baseBatch : Accuracy → Count)
    (step : Accuracy → PositiveStepsize) (refresh : Accuracy → ℝ)
    (density : ℝ)
    (hvariance : 0 ≤ variance) (hgap : 0 ≤ gap)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      density d
        (onlineNonconvexBatchScheduleFromBase n b0 variance baseBatch ε) b0) :
    let batch := onlineNonconvexBatchScheduleFromBase n b0 variance baseBatch
    let K := onlineExecutableNonconvexScheduledHorizon
      gap variance step refresh n batch
    (∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      density d (batch ε) b0) ∧
      (∀ ε, OnlineBatchAdmissible (batch ε) b0) ∧
      (∀ ε,
        2 * gap / ((step ε : ℝ) * (K ε).1) +
          (variance / (n.1 * (batch ε).1)) /
            (refresh ε * (K ε).1) +
          variance / (n.1 * (batch ε).1) ≤ (ε : ℝ) ^ 2) := by
  dsimp
  have hBatch : ∀ ε, OnlineBatchAdmissible
      (onlineNonconvexBatchScheduleFromBase n b0 variance baseBatch ε) b0 := by
    intro ε
    exact onlineNonconvexBatchScheduleFromBase_admissible
      n b0 variance baseBatch ε
  refine ⟨hSchedule, hBatch, ?_⟩
  apply onlineExecutableNonconvexScheduledHorizon_budget
    gap variance step refresh
  · exact hgap
  · exact hvariance
  · exact fun ε => (hrefresh ε).1
  · intro ε
    simpa using onlineNonconvexBatchScheduleFromBase_variance_floor
      n b0 variance hvariance baseBatch ε

/-- Under the exact D.3/D.4 density/batch minimum, inverse refresh is controlled
by an affine function of the executed refresh-batch size.  This is the missing
asymptotic ingredient for absorbing the executable initializer horizon; it is
derived from the schedule's exact odds identity, not assumed as a rate. -/
theorem online_density_schedule_inverse_refresh_bigO
    {d b0 : Count} {batch : Accuracy → Count} {refresh : Accuracy → ℝ}
    {density : ℝ}
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      density d (batch ε) b0) :
    AccuracyBigO (fun ε => 1 / refresh ε)
      (fun ε => 1 + ((batch ε).1 : ℝ)) := by
  unfold AccuracyBigO
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := 1 + |(d.1 : ℝ) / density - 1| + 1 / b0.1
  refine ⟨C, Filter.Eventually.of_forall ?_⟩
  intro ε
  have hp : 0 < refresh ε := (hrefresh ε).1
  have hb0 : 0 < (b0.1 : ℝ) := by exact_mod_cast b0.2
  have hb : 1 ≤ ((batch ε).1 : ℝ) := by exact_mod_cast (batch ε).2
  have hOdds := online_density_schedule_odds_eq hp (hSchedule ε)
  have hInv : 1 / refresh ε = 1 +
      max ((d.1 : ℝ) / density - 1) (((batch ε).1 : ℝ) / b0.1) := by
    rw [← hOdds]
    field_simp [ne_of_gt hp]
    ring
  have hMax : max ((d.1 : ℝ) / density - 1)
      (((batch ε).1 : ℝ) / b0.1) ≤
        |(d.1 : ℝ) / density - 1| + ((batch ε).1 : ℝ) / b0.1 := by
    have hBatchDiv : 0 ≤ ((batch ε).1 : ℝ) / b0.1 := by positivity
    apply max_le
    · linarith [le_abs_self ((d.1 : ℝ) / density - 1)]
    · have : 0 ≤ |(d.1 : ℝ) / density - 1| := abs_nonneg _
      linarith
  have hTarget : 0 < 1 + ((batch ε).1 : ℝ) := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp),
    Real.norm_eq_abs, abs_of_pos hTarget, hInv]
  have hInvB0 : 0 ≤ 1 / (b0.1 : ℝ) := one_div_nonneg.mpr hb0.le
  have hAbs : 0 ≤ |(d.1 : ℝ) / density - 1| := abs_nonneg _
  dsimp [C]
  calc
    1 + max ((d.1 : ℝ) / density - 1)
        (((batch ε).1 : ℝ) / b0.1) ≤
      1 + |(d.1 : ℝ) / density - 1| +
        ((batch ε).1 : ℝ) / b0.1 := by linarith
    _ ≤ (1 + |(d.1 : ℝ) / density - 1| + 1 / b0.1) *
        (1 + ((batch ε).1 : ℝ)) := by
      rw [show ((batch ε).1 : ℝ) / b0.1 =
        ((batch ε).1 : ℝ) * (1 / b0.1) by ring]
      nlinarith

/-- In the positive-gap branch, the extra executable-initializer ceiling in
the scheduled D.3 horizon is absorbed by the printed density-scheduled
iteration scale.  The proof uses the pointwise variance floor for the
initializer term and derives the inverse-refresh bound from the exact
density/batch schedule. -/
theorem onlineExecutableNonconvexScheduledHorizon_bigO_canonical
    {d n b0 : Count} {batch : Accuracy → Count}
    {refresh : Accuracy → ℝ} {L ℒ ω density gap variance : ℝ}
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hL : 0 < L) (hℒ : 0 ≤ ℒ) (hω : 0 ≤ ω)
    (hgap : 0 < gap) (hvariance : 0 ≤ variance)
    (hBatch : AccuracyBigO (fun ε => ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2)))
    (hFloor : ∀ ε,
      variance / (n.1 * (batch ε).1) ≤ (ε : ℝ) ^ 2 / 2)
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      density d (batch ε) b0) :
    let step := fun ε => onlineDensityCanonicalStepsize L ℒ (refresh ε) ω n b0
    let K := onlineExecutableNonconvexScheduledHorizon
      gap variance step refresh n batch
    AccuracyBigO (fun ε => ((K ε).1 : ℝ))
      (fun ε => gap / (ε : ℝ) ^ 2 *
        vrIterationBracket L ℒ ω
          (onlineDensityBatchRatio d n b0 density variance ((ε : ℝ) ^ 2))
          n b0) := by
  dsimp
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlineDensityCanonicalStepsize L ℒ (refresh ε) ω n b0
  let supplied : Accuracy → ℝ := fun ε =>
    1 + 4 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2)
  let target : Accuracy → ℝ := fun ε =>
    gap / (ε : ℝ) ^ 2 *
      vrIterationBracket L ℒ ω
        (onlineDensityBatchRatio d n b0 density variance ((ε : ℝ) ^ 2))
        n b0
  have hSupplied : AccuracyBigO supplied target := by
    simpa [supplied, target, step] using
      online_nonconvex_supplied_scale_bigO_canonical hrefresh hL hℒ hω
        hvariance hgap hBatch hSchedule
  have hOneBatch : AccuracyBigO
      (fun ε => 1 + ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2)) := by
    have hBatchOne : ∀ ε, 1 ≤ ((batch ε).1 : ℝ) := by
      intro ε
      exact_mod_cast (batch ε).2
    have h := accuracyBigO_batch_add_bounded_payload
      hBatch hBatchOne (fun _ => (show 0 ≤ (1 : ℝ) by norm_num))
      (fun _ => (show (1 : ℝ) ≤ 1 by norm_num)) (by norm_num)
    simpa [add_comm] using h
  have hVarianceTarget : AccuracyBigO
      (fun ε => variance / (n.1 * (ε : ℝ) ^ 2)) target := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff']
    let C : ℝ := 1 + variance / (n.1 * gap * L)
    have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
    have hC : 0 < C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, Filter.Eventually.of_forall ?_⟩
    intro ε
    have hbracket : L ≤ vrIterationBracket L ℒ ω
        (onlineDensityBatchRatio d n b0 density variance ((ε : ℝ) ^ 2))
        n b0 := by
      dsimp [vrIterationBracket]
      have hfirst : 0 ≤ L * Real.sqrt
          (ω * onlineDensityBatchRatio d n b0 density variance
            ((ε : ℝ) ^ 2) / n.1) :=
        mul_nonneg hL.le (Real.sqrt_nonneg _)
      have hsecond : 0 ≤ ℒ * Real.sqrt
          ((1 + ω) * onlineDensityBatchRatio d n b0 density variance
            ((ε : ℝ) ^ 2) / (n.1 * b0.1)) :=
        mul_nonneg hℒ (Real.sqrt_nonneg _)
      nlinarith
    have hactual : 0 ≤ variance / (n.1 * (ε : ℝ) ^ 2) := by positivity
    have htarget : 0 < target ε := by
      dsimp [target]
      exact mul_pos (div_pos hgap (sq_pos_of_pos ε.property))
        (hL.trans_le hbracket)
    rw [Real.norm_eq_abs, abs_of_nonneg hactual,
      Real.norm_eq_abs, abs_of_pos htarget]
    dsimp [C, target]
    have hratio : variance / (n.1 * (ε : ℝ) ^ 2) ≤
        (variance / (n.1 * gap * L)) *
          (gap / (ε : ℝ) ^ 2 *
            vrIterationBracket L ℒ ω
              (onlineDensityBatchRatio d n b0 density variance
                ((ε : ℝ) ^ 2)) n b0) := by
      have hmul := mul_le_mul_of_nonneg_left hbracket
        (div_nonneg hvariance (by positivity : 0 ≤ (n.1 : ℝ) * (ε : ℝ) ^ 2))
      calc
        variance / (n.1 * (ε : ℝ) ^ 2) ≤
            variance / (n.1 * (ε : ℝ) ^ 2) * (L / L) := by
          rw [div_self (ne_of_gt hL), mul_one]
        _ ≤ variance / (n.1 * (ε : ℝ) ^ 2) *
            (vrIterationBracket L ℒ ω
              (onlineDensityBatchRatio d n b0 density variance
                ((ε : ℝ) ^ 2)) n b0 / L) := by
          gcongr
        _ = (variance / (n.1 * gap * L)) *
            (gap / (ε : ℝ) ^ 2 *
              vrIterationBracket L ℒ ω
                (onlineDensityBatchRatio d n b0 density variance
                  ((ε : ℝ) ^ 2)) n b0) := by
          field_simp [ne_of_gt hn, ne_of_gt hgap, ne_of_gt hL,
            ne_of_gt ε.property]
    exact hratio.trans (by
      have ht := htarget.le
      nlinarith)
  have hInverse : AccuracyBigO (fun ε => 1 / refresh ε) target :=
    (online_density_schedule_inverse_refresh_bigO hrefresh hSchedule).trans
      (hOneBatch.trans hVarianceTarget)
  unfold AccuracyBigO at hSupplied hInverse ⊢
  rw [Asymptotics.isBigO_iff'] at hSupplied hInverse ⊢
  rcases hSupplied with ⟨C₁, hC₁, hSupplied⟩
  rcases hInverse with ⟨C₂, hC₂, hInverse⟩
  refine ⟨1 + 4 * C₁ + 2 * C₂, by positivity, ?_⟩
  filter_upwards [hSupplied, hInverse] with ε hSuppliedε hInverseε
  let optimizationQuota : ℝ :=
    8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2)
  let initializationQuota : ℝ :=
    4 * (variance / (n.1 * (batch ε).1)) /
      (refresh ε * (ε : ℝ) ^ 2)
  have hoptimization : 0 ≤ optimizationQuota := by
    dsimp [optimizationQuota]
    exact div_nonneg (mul_nonneg (by norm_num) hgap.le)
      (mul_nonneg (step ε).property.le (sq_nonneg _))
  have hinitialization : 0 ≤ initializationQuota := by
    dsimp [initializationQuota]
    exact div_nonneg
      (mul_nonneg (by norm_num)
        (div_nonneg hvariance (by positivity)))
      (mul_nonneg (hrefresh ε).1.le (sq_nonneg _))
  have hceil := natCast_max_one_ceil_le_add_two
    (max optimizationQuota initializationQuota)
    (le_max_of_le_left hoptimization)
  have hinitBound : initializationQuota ≤ 2 * (1 / refresh ε) := by
    have hp : 0 < refresh ε := (hrefresh ε).1
    have heps : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos ε.property
    dsimp [initializationQuota]
    have hdiv := div_le_div_of_nonneg_right (hFloor ε)
      (mul_nonneg hp.le heps.le)
    calc
      4 * (variance / (n.1 * (batch ε).1)) /
          (refresh ε * (ε : ℝ) ^ 2) =
          4 * ((variance / (n.1 * (batch ε).1)) /
            (refresh ε * (ε : ℝ) ^ 2)) := by ring
      _ ≤ 4 * (((ε : ℝ) ^ 2 / 2) /
            (refresh ε * (ε : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 2 * (1 / refresh ε) := by
        field_simp [ne_of_gt hp, ne_of_gt ε.property]
        ring
  have hKBound :
      ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ) ≤
        4 * supplied ε + 2 * (1 / refresh ε) := by
    change ((max 1 (Nat.ceil (max optimizationQuota initializationQuota)) : ℕ) : ℝ) ≤ _
    have hmax : max optimizationQuota initializationQuota ≤
        optimizationQuota + initializationQuota :=
      max_le (le_add_of_nonneg_right hinitialization)
        (le_add_of_nonneg_left hoptimization)
    have hoptEq : optimizationQuota = 2 * (supplied ε - 1) := by
      dsimp [optimizationQuota, supplied, step]
      ring
    calc
      ((max 1 (Nat.ceil (max optimizationQuota initializationQuota)) : ℕ) : ℝ) ≤
          max optimizationQuota initializationQuota + 2 := hceil
      _ ≤ optimizationQuota + initializationQuota + 2 := by linarith
      _ ≤ 2 * (supplied ε - 1) + 2 * (1 / refresh ε) + 2 := by
        rw [hoptEq]
        linarith
      _ ≤ 4 * supplied ε + 2 * (1 / refresh ε) := by
        have hs : 1 ≤ supplied ε := by
          dsimp [supplied]
          have hq : 0 ≤ 4 * gap /
              ((step ε : ℝ) * (ε : ℝ) ^ 2) :=
            div_nonneg (mul_nonneg (by norm_num) hgap.le)
              (mul_nonneg (step ε).property.le (sq_nonneg _))
          linarith
        linarith
  have htarget : 0 < target ε := by
    have hbracket : 0 < vrIterationBracket L ℒ ω
        (onlineDensityBatchRatio d n b0 density variance ((ε : ℝ) ^ 2))
        n b0 := by
      dsimp [vrIterationBracket]
      have hfirst : 0 ≤ L * Real.sqrt
          (ω * onlineDensityBatchRatio d n b0 density variance
            ((ε : ℝ) ^ 2) / n.1) :=
        mul_nonneg hL.le (Real.sqrt_nonneg _)
      have hsecond : 0 ≤ ℒ * Real.sqrt
          ((1 + ω) * onlineDensityBatchRatio d n b0 density variance
            ((ε : ℝ) ^ 2) / (n.1 * b0.1)) :=
        mul_nonneg hℒ (Real.sqrt_nonneg _)
      nlinarith
    dsimp [target]
    exact mul_pos (div_pos hgap (sq_pos_of_pos ε.property)) hbracket
  have hsupp : 0 ≤ supplied ε := by
    dsimp [supplied]
    have hq : 0 ≤ 4 * gap /
        ((step ε : ℝ) * (ε : ℝ) ^ 2) :=
      div_nonneg (mul_nonneg (by norm_num) hgap.le)
        (mul_nonneg (step ε).property.le (sq_nonneg _))
    linarith
  have hinv : 0 < 1 / refresh ε := one_div_pos.mpr (hrefresh ε).1
  have hSupplied' : supplied ε ≤ C₁ * target ε := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hsupp,
      abs_of_pos htarget] using hSuppliedε
  have hInverse' : 1 / refresh ε ≤ C₂ * target ε := by
    simpa [Real.norm_eq_abs, abs_of_pos (hrefresh ε).1,
      abs_of_pos hinv,
      abs_of_pos htarget] using hInverseε
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ)),
    Real.norm_eq_abs, abs_of_pos htarget]
  calc
    ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ) ≤
        4 * supplied ε + 2 * (1 / refresh ε) := hKBound
    _ ≤ (4 * C₁ + 2 * C₂) * target ε := by nlinarith
    _ ≤ (1 + 4 * C₁ + 2 * C₂) * target ε := by
      nlinarith

/-- Canonical density/batch and Eq. (40) stepsize specialization of executable
D.3 accuracy.  Unlike the proof-exact source corollary, this theorem runs
`onlineProcess` from its sampled minibatch initializer and uses the extra
horizon ceiling above to discharge that initializer's variance term. -/
theorem onlineExecutableNonconvexDensityScheduled_accuracy
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count) (refresh : Accuracy → ℝ)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refresh ε) ω n b0)
            (refresh ε) (hrefresh ε)) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) baseBatch ε)) ℒlocal)
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
        (onlineNonconvexBatchScheduleFromBase n b0
          (varianceAggregateSq σ) baseBatch ε) b0) :
    let batch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) baseBatch
    let step := fun ε => onlineDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω n b0
    let gap := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let K := onlineExecutableNonconvexScheduledHorizon
      gap (varianceAggregateSq σ) step refresh n batch
    ∀ ε, NonconvexAccuracy (K ε) (onlineLocalProblem A.problem)
      (onlineProcess
        (onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε)) x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) baseBatch ε))
      (onlinePathLaw
        (A := onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε))) ε := by
  dsimp
  let batch := onlineNonconvexBatchScheduleFromBase n b0
    (varianceAggregateSq σ) baseBatch
  let step := fun ε => onlineDensityCanonicalStepsize
    (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω n b0
  let gap := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let K := onlineExecutableNonconvexScheduledHorizon
    gap (varianceAggregateSq σ) step refresh n batch
  have hvariance : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hgap : 0 ≤ gap := by
    dsimp [gap]
    exact sub_nonneg.mpr (hLower x0)
  have hScheduled := onlineExecutableNonconvexDensityScheduled_budget
    (d := d) (b0 := b0) gap (varianceAggregateSq σ) baseBatch step refresh
      (expectedDensity A.quantizer) hvariance hgap hrefresh hSchedule
  have hBatch : ∀ ε, OnlineBatchAdmissible (batch ε) b0 := by
    simpa [batch] using hScheduled.2.1
  apply onlineParameterizedExecutableNonconvexAccuracy_family_of_budget
    A x0 step refresh hrefresh batch K Llocal ℒlocal σ ω fStar
      hLower hSmooth hVariance hQuantizer hBatch
  · intro ε
    simpa [batch, step] using hAverageSmooth ε
  · intro ε
    exact onlineDensityCanonicalStepsize_condition
  · intro ε
    simpa [batch, step, gap, K] using hScheduled.2.2 ε

/-- Measured executable Corollary D.3 in the regular positive-gap branch.
The iteration scale is the source density-scheduled bracket, while the oracle
and communication fields integrate the actual sampled-initializer process
under its matching parameterized `onlinePathLaw`. -/
theorem onlineExecutableNonconvexDensityScheduled_measured_cost_complexity_of_positive_gap
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count) (refresh : Accuracy → ℝ)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refresh ε) ω n b0)
            (refresh ε) (hrefresh ε)) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) baseBatch ε)) ℒlocal)
    (hBaseOrder : AccuracyTheta (fun ε => ((baseBatch ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
        (onlineNonconvexBatchScheduleFromBase n b0
          (varianceAggregateSq σ) baseBatch ε) b0)
    (hGap : 0 < globalObjective (onlineLocalProblem A.problem) x0 - fStar)
    (hL : 0 < rootMeanSquare Llocal) :
    let batch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) baseBatch
    let step := fun ε => onlineDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω n b0
    let gap := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let K := onlineExecutableNonconvexScheduledHorizon
      gap (varianceAggregateSq σ) step refresh n batch
    let iterationScale := fun ε : Accuracy =>
      gap / (ε : ℝ) ^ 2 *
        vrIterationBracket (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
          (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
            (varianceAggregateSq σ) ((ε : ℝ) ^ 2)) n b0
    let varianceScale := fun ε : Accuracy =>
      varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)
    OnlineParameterizedExecutableNonconvexMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε))
      x0 batch
      (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) baseBatch ε)
      K iterationScale
      (fun ε => varianceScale ε + iterationScale ε * b0.1)
      (fun ε => d.1 + iterationScale ε * expectedDensity A.quantizer) := by
  dsimp
  let batch : Accuracy → Count := onlineNonconvexBatchScheduleFromBase n b0
    (varianceAggregateSq σ) baseBatch
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) (refresh ε) ω n b0
  let gap : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let K : Accuracy → Count := onlineExecutableNonconvexScheduledHorizon
    gap (varianceAggregateSq σ) step refresh n batch
  let iterationScale : Accuracy → ℝ := fun ε =>
    gap / (ε : ℝ) ^ 2 *
      vrIterationBracket (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) ω
        (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
          (varianceAggregateSq σ) ((ε : ℝ) ^ 2)) n b0
  let varianceScale : Accuracy → ℝ := fun ε =>
    varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)
  have hvar : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := Real.sqrt_nonneg _
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hBatch : ∀ ε, OnlineBatchAdmissible (batch ε) b0 := by
    intro ε
    exact onlineNonconvexBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) baseBatch ε
  have hBatchTheta : AccuracyTheta (fun ε => ((batch ε).1 : ℝ))
      varianceScale := by
    simpa [batch, varianceScale] using
      onlineNonconvexBatchScheduleFromBase_accuracyTheta n b0
        (varianceAggregateSq σ) hvar baseBatch hBaseOrder
  have hFloor : ∀ ε,
      varianceAggregateSq σ / (n.1 * (batch ε).1) ≤
        (ε : ℝ) ^ 2 / 2 := by
    intro ε
    simpa [batch] using onlineNonconvexBatchScheduleFromBase_variance_floor
      n b0 (varianceAggregateSq σ) hvar baseBatch ε
  have hScheduled := onlineExecutableNonconvexDensityScheduled_budget
    (d := d) (b0 := b0) gap (varianceAggregateSq σ) baseBatch step refresh
      (expectedDensity A.quantizer) hvar (by simpa [gap] using hGap.le)
      hrefresh (by simpa [batch] using hSchedule)
  have hK : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
    simpa [K, gap, step, batch, iterationScale] using
      onlineExecutableNonconvexScheduledHorizon_bigO_canonical
        (d := d) (b0 := b0) hrefresh hL hℒ hω
          (by simpa [gap] using hGap) hvar hBatchTheta.1 hFloor
          (by simpa [batch] using hSchedule)
  have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
    (hrefresh ε).1 (hrefresh ε).2
      (expectedDensity_nonneg_of_unbiased hQuantizer)
      (by simpa [batch] using hSchedule ε)
  let oraclePayload : Accuracy → ℝ := fun ε =>
    refresh ε * (batch ε).1 + 2 * (1 - refresh ε) * b0.1
  let communicationPayload : Accuracy → ℝ := fun ε =>
    refresh ε * d.1 +
      (1 - refresh ε) * expectedDensity A.quantizer
  have hIterationNonneg : ∀ᶠ ε in accuracyToZero,
      0 ≤ iterationScale ε :=
    Filter.Eventually.of_forall fun ε => by
      dsimp [iterationScale, gap, vrIterationBracket]
      positivity
  have hOracle : AccuracyBigO
      (fun ε => ((batch ε).1 : ℝ) + (K ε).1 * oraclePayload ε)
      (fun ε => varianceScale ε + iterationScale ε * b0.1) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := (b0.1 : ℝ)) (factor := 3)
      hBatchTheta.1 hK (fun _ => by positivity) (fun _ => by positivity)
      (Filter.Eventually.of_forall fun ε => by
        dsimp [varianceScale]
        positivity)
      hIterationNonneg
    · intro ε
      dsimp [oraclePayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg
          (mul_nonneg (by norm_num) (sub_nonneg.mpr (hrefresh ε).2))
          (by positivity))
    · exact_mod_cast b0.2
    · norm_num
    · intro ε
      simpa [oraclePayload] using (hPayload ε).2.1
  have hDensityPos : 0 < expectedDensity A.quantizer :=
    (hPayload ⟨1, by norm_num⟩).1
  have hCommunication : AccuracyBigO
      (fun ε => (d.1 : ℝ) + (K ε).1 * communicationPayload ε)
      (fun ε => (d.1 : ℝ) +
        iterationScale ε * expectedDensity A.quantizer) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := expectedDensity A.quantizer) (factor := 2)
      (Asymptotics.isBigO_refl _ _) hK (fun _ => by positivity)
      (fun _ => by positivity)
      (Filter.Eventually.of_forall fun _ => by positivity)
      hIterationNonneg
    · intro ε
      dsimp [communicationPayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg (sub_nonneg.mpr (hrefresh ε).2)
          (expectedDensity_nonneg_of_unbiased hQuantizer))
    · exact hDensityPos
    · norm_num
    · intro ε
      simpa [communicationPayload] using (hPayload ε).2.2
  apply onlineParameterizedExecutableNonconvexMeasuredCostComplexity_of_budget
    A x0 step refresh hrefresh batch K Llocal ℒlocal σ ω fStar
      hLower hSmooth hVariance hQuantizer hBatch
  · intro ε
    simpa [batch, step] using hAverageSmooth ε
  · intro ε
    exact onlineDensityCanonicalStepsize_condition
  · intro ε
    simpa [K, gap, step, batch] using hScheduled.2.2 ε
  · exact Or.inr hK
  · simpa [onlineOracleCallCount, batch, K, oraclePayload] using hOracle
  · simpa [allWorkerCommunicationCount, K, communicationPayload] using
      hCommunication

/-! The executable D.4 schedule has the same sampled-initializer correction
as the fixed-parameter result above.  The source batch controls the stationary
variance by `ε / 2`; the PŁ stepsize coupling `2 γ μ ≤ p` then controls the
initial estimator term by `ε / 4`.  The remaining quarter is paid by the
geometric horizon below. -/

/-- A density-scheduled executable D.4 horizon.  Its factor four is the
explicit allocation needed for the sampled-initializer term; it changes only
the constant inside the logarithm. -/
noncomputable def onlineExecutablePLScheduledHorizon
    (gap : ℝ) (step : Accuracy → PositiveStepsize)
    (μ : PositivePLParameter) : Accuracy → Count := fun ε =>
  ⟨max 1 (Nat.ceil (Real.log (4 * gap / (ε : ℝ)) /
    ((step ε : ℝ) * (μ : ℝ)))), by omega⟩

/-- The scheduled D.4 horizon discharges the complete executable three-term
budget.  The hypotheses are scalar consequences of the canonical PŁ
stepsize condition and the source batch floor, not assumed accuracy or cost
conclusions. -/
theorem onlineExecutablePLScheduledHorizon_budget_of_positive_gap
    {n : Count} (gap variance : ℝ)
    (step : Accuracy → PositiveStepsize) (refresh : Accuracy → ℝ)
    (μ : PositivePLParameter) (batch : Accuracy → Count)
    (hgap : 0 < gap) (hvariance : 0 ≤ variance)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hCoupling : ∀ ε,
      2 * (step ε : ℝ) * (μ : ℝ) ≤ refresh ε)
    (hFloor : ∀ ε,
      variance / (n.1 * (batch ε).1 * (μ : ℝ)) ≤ (ε : ℝ) / 2) :
    ∀ ε,
      (1 - (step ε : ℝ) * (μ : ℝ)) ^
          (onlineExecutablePLScheduledHorizon gap step μ ε).1 * gap +
        (1 - (step ε : ℝ) * (μ : ℝ)) ^
            (onlineExecutablePLScheduledHorizon gap step μ ε).1 *
          (step ε : ℝ) / refresh ε *
            (variance / (n.1 * (batch ε).1)) +
        variance / (n.1 * (batch ε).1 * (μ : ℝ)) ≤ (ε : ℝ) := by
  intro ε
  let c : ℝ := (step ε : ℝ) * (μ : ℝ)
  let K : Count := onlineExecutablePLScheduledHorizon gap step μ ε
  let floor : ℝ := variance / (n.1 * (batch ε).1 * (μ : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (step ε).property μ.property
  have hc1 : c ≤ 1 := by
    have hp1 := (hrefresh ε).2
    have hcoupling := hCoupling ε
    dsimp [c]
    nlinarith
  have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  have hbaseOne : 1 - c ≤ 1 := by linarith
  have hGapQuarter : (1 - c) ^ K.1 * gap ≤ (ε : ℝ) / 4 := by
    have hScalar := positive_geometric_ceiling_schedule
      (4 * gap) c 1 (mul_pos (by norm_num) hgap) hc hc1 (by norm_num)
    have hFour : (1 - c) ^ K.1 * (4 * gap) ≤ (ε : ℝ) := by
      simpa [K, c, onlineExecutablePLScheduledHorizon] using hScalar.1 ε
    nlinarith [pow_nonneg hbase K.1]
  have hfloorNonneg : 0 ≤ floor := by
    dsimp [floor]
    exact div_nonneg hvariance
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) μ.property.le)
  have hRatio : (step ε : ℝ) * (μ : ℝ) / refresh ε ≤ 1 / 2 := by
    rw [div_le_iff₀ (hrefresh ε).1]
    nlinarith [hCoupling ε]
  have hInitialQuarter :
      (1 - c) ^ K.1 * (step ε : ℝ) / refresh ε *
          (variance / (n.1 * (batch ε).1)) ≤ (ε : ℝ) / 4 := by
    have hpow : (1 - c) ^ K.1 ≤ 1 :=
      pow_le_one₀ hbase hbaseOne
    have hRatioNonneg :
        0 ≤ (step ε : ℝ) * (μ : ℝ) / refresh ε := by
      exact div_nonneg
        (mul_nonneg (step ε).property.le μ.property.le)
        (hrefresh ε).1.le
    calc
      (1 - c) ^ K.1 * (step ε : ℝ) / refresh ε *
            (variance / (n.1 * (batch ε).1)) =
          ((1 - c) ^ K.1 *
            ((step ε : ℝ) * (μ : ℝ) / refresh ε)) * floor := by
              dsimp [floor]
              field_simp [ne_of_gt (hrefresh ε).1, ne_of_gt μ.property]
      _ ≤ (1 * (1 / 2 : ℝ)) * floor := by
          gcongr
      _ ≤ (ε : ℝ) / 4 := by
          nlinarith [hFloor ε]
  change (1 - c) ^ K.1 * gap +
      (1 - c) ^ K.1 * (step ε : ℝ) / refresh ε *
        (variance / (n.1 * (batch ε).1)) + floor ≤ (ε : ℝ)
  linarith [hGapQuarter, hInitialQuarter, hFloor ε]

/-- The executable D.4 horizon has the printed positive-gap density-scheduled
iteration order.  The extra factor four inside the logarithm is absorbed
explicitly; inverse refresh and the canonical stepsize remain derived from
the exact source schedule. -/
theorem onlineExecutablePLScheduledHorizon_bigO_canonical
    {d n b0 : Count} {batch : Accuracy → Count}
    {refresh : Accuracy → ℝ} {L ℒ ω density variance gap : ℝ}
    {μ : PositivePLParameter}
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hL : 0 < L) (hℒ : 0 ≤ ℒ) (hω : 0 ≤ ω)
    (hvariance : 0 ≤ variance) (hgap : 0 < gap)
    (hBatch : AccuracyBigO (fun ε => ((batch ε).1 : ℝ))
      (fun ε => variance / (n.1 * (μ : ℝ) * (ε : ℝ))))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      density d (batch ε) b0) :
    let step := fun ε =>
      onlinePLDensityCanonicalStepsize L ℒ (refresh ε) ω μ n b0
    let K := onlineExecutablePLScheduledHorizon gap step μ
    AccuracyBigO (fun ε => ((K ε).1 : ℝ))
      (fun ε =>
        max (1 / refresh ε)
          (vrIterationBracket L ℒ ω
              (onlineDensityBatchRatio d n b0 density variance
                ((μ : ℝ) * (ε : ℝ))) n b0 / (μ : ℝ)) *
          Real.log (gap / (ε : ℝ))) := by
  dsimp
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlinePLDensityCanonicalStepsize L ℒ (refresh ε) ω μ n b0
  let supplied : Accuracy → ℝ := fun ε =>
    1 + max 0 (Real.log (4 * gap / (ε : ℝ)) /
      ((step ε : ℝ) * (μ : ℝ)))
  let intermediate : Accuracy → ℝ := fun ε =>
    max (1 / refresh ε)
      (vrIterationBracket L ℒ ω
          (onlineDensityBatchRatio d n b0 density variance
            ((μ : ℝ) * (ε : ℝ))) n b0 / (μ : ℝ)) *
      Real.log (2 * gap / (ε : ℝ))
  let target : Accuracy → ℝ := fun ε =>
    max (1 / refresh ε)
      (vrIterationBracket L ℒ ω
          (onlineDensityBatchRatio d n b0 density variance
            ((μ : ℝ) * (ε : ℝ))) n b0 / (μ : ℝ)) *
      Real.log (gap / (ε : ℝ))
  have hKToSupplied : AccuracyBigO
      (fun ε => ((onlineExecutablePLScheduledHorizon gap step μ ε).1 : ℝ))
      supplied := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    let raw : ℝ := Real.log (4 * gap / (ε : ℝ)) /
      ((step ε : ℝ) * (μ : ℝ))
    have hrawMax : raw ≤ max 0 raw := le_max_right _ _
    have hceilMono : Nat.ceil raw ≤ Nat.ceil (max 0 raw) :=
      Nat.ceil_mono hrawMax
    have hmaxMono : max 1 (Nat.ceil raw) ≤ max 1 (Nat.ceil (max 0 raw)) :=
      max_le_max_left 1 hceilMono
    have hceil := natCast_max_one_ceil_le_add_two
      (max 0 raw) (le_max_left _ _)
    have hsuppliedPos : 0 < supplied ε := by
      dsimp [supplied]
      linarith [le_max_left (0 : ℝ) raw]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineExecutablePLScheduledHorizon gap step μ ε).1 : ℝ)),
      Real.norm_eq_abs, abs_of_pos hsuppliedPos]
    change ((max 1 (Nat.ceil raw) : ℕ) : ℝ) ≤ 2 * supplied ε
    have hmaxMonoReal : ((max 1 (Nat.ceil raw) : ℕ) : ℝ) ≤
        ((max 1 (Nat.ceil (max 0 raw)) : ℕ) : ℝ) := by
      exact_mod_cast hmaxMono
    change ((max 1 (Nat.ceil raw) : ℕ) : ℝ) ≤
      2 * (1 + max 0 raw)
    exact hmaxMonoReal.trans (hceil.trans (by
      nlinarith [le_max_left (0 : ℝ) raw]))
  have hSupplied : AccuracyBigO supplied intermediate := by
    simpa [supplied, intermediate, step, mul_assoc,
      show 2 * (2 * gap) = 4 * gap by ring] using
      online_pl_supplied_scale_bigO_canonical
        (d := d) (b0 := b0) hrefresh hL hℒ hω hvariance
          (show 0 < 2 * gap by positivity) hBatch hSchedule
  have hShift : AccuracyBigO intermediate target := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [eventually_one_le_log_gap_div_accuracy hgap] with ε hlog
    let factor : ℝ := max (1 / refresh ε)
      (vrIterationBracket L ℒ ω
          (onlineDensityBatchRatio d n b0 density variance
            ((μ : ℝ) * (ε : ℝ))) n b0 / (μ : ℝ))
    have hfactor : 0 < factor :=
      (div_pos zero_lt_one (hrefresh ε).1).trans_le (le_max_left _ _)
    have hratio : 0 < gap / (ε : ℝ) := div_pos hgap ε.property
    have hlogTwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    have hlogShift : Real.log (2 * gap / (ε : ℝ)) =
        Real.log 2 + Real.log (gap / (ε : ℝ)) := by
      rw [show 2 * gap / (ε : ℝ) = 2 * (gap / (ε : ℝ)) by ring]
      exact Real.log_mul (by norm_num) (ne_of_gt hratio)
    have hshiftNonneg : 0 ≤ Real.log (2 * gap / (ε : ℝ)) := by
      rw [hlogShift]
      have hlogTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    have hbound : Real.log (2 * gap / (ε : ℝ)) ≤
        2 * Real.log (gap / (ε : ℝ)) := by
      rw [hlogShift]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfactor.le hshiftNonneg),
      Real.norm_eq_abs,
      abs_of_pos (mul_pos hfactor (lt_of_lt_of_le zero_lt_one hlog))]
    change factor * Real.log (2 * gap / (ε : ℝ)) ≤
      2 * (factor * Real.log (gap / (ε : ℝ)))
    calc
      factor * Real.log (2 * gap / (ε : ℝ)) ≤
          factor * (2 * Real.log (gap / (ε : ℝ))) :=
        mul_le_mul_of_nonneg_left hbound hfactor.le
      _ = 2 * (factor * Real.log (gap / (ε : ℝ))) := by ring
  exact hKToSupplied.trans (hSupplied.trans hShift)

/-- Measured executable Corollary D.4 in the regular positive-gap branch.
The convergence predicate, oracle integral, and actual-message integral all
use the same sampled-initializer `onlineProcess` and parameterized
`onlinePathLaw`. -/
theorem onlineExecutablePLDensityScheduled_measured_cost_complexity_of_positive_gap
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count) (refresh : Accuracy → ℝ)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0)
            (refresh ε) (hrefresh ε)) x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hBaseOrder : AccuracyTheta (fun ε => ((baseBatch ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ /
        (n.1 * (μ : ℝ) * (ε : ℝ))))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
        (onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ baseBatch ε) b0)
    (hGap : 0 < globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar)
    (hL : 0 < rootMeanSquare Llocal) :
    let batch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let step := fun ε => onlinePLDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0
    let gap := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let K := onlineExecutablePLScheduledHorizon gap step μ
    let factor := fun ε : Accuracy =>
      max (1 / refresh ε)
        (vrIterationBracket (rootMeanSquare Llocal)
            (rootMeanSquare ℒlocal) ω
            (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
              (varianceAggregateSq σ) ((μ : ℝ) * (ε : ℝ))) n b0 /
          (μ : ℝ))
    let iterationScale := fun ε : Accuracy => factor ε *
      Real.log (gap / (ε : ℝ))
    let varianceScale := fun ε : Accuracy => varianceAggregateSq σ /
      (n.1 * (μ : ℝ) * (ε : ℝ))
    OnlineParameterizedExecutablePLMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε))
      x0 xStar batch
      (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) μ baseBatch ε)
      K iterationScale
      (fun ε => varianceScale ε + b0.1 * iterationScale ε)
      (fun ε => d.1 + expectedDensity A.quantizer * iterationScale ε) := by
  dsimp
  let batch : Accuracy → Count := onlinePLBatchScheduleFromBase n b0
    (varianceAggregateSq σ) μ baseBatch
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0
  let gap : ℝ := globalObjective (onlineLocalProblem A.problem) x0 -
    globalObjective (onlineLocalProblem A.problem) xStar
  let K : Accuracy → Count := onlineExecutablePLScheduledHorizon gap step μ
  let factor : Accuracy → ℝ := fun ε =>
    max (1 / refresh ε)
      (vrIterationBracket (rootMeanSquare Llocal)
          (rootMeanSquare ℒlocal) ω
          (onlineDensityBatchRatio d n b0 (expectedDensity A.quantizer)
            (varianceAggregateSq σ) ((μ : ℝ) * (ε : ℝ))) n b0 /
        (μ : ℝ))
  let iterationScale : Accuracy → ℝ := fun ε => factor ε *
    Real.log (gap / (ε : ℝ))
  let varianceScale : Accuracy → ℝ := fun ε => varianceAggregateSq σ /
    (n.1 * (μ : ℝ) * (ε : ℝ))
  have hgap : 0 < gap := by simpa [gap] using hGap
  have hvar : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hℒ : 0 ≤ rootMeanSquare ℒlocal := Real.sqrt_nonneg _
  have hω : 0 ≤ ω := hQuantizer.1.le
  have hBatch : ∀ ε, OnlineBatchAdmissible (batch ε) b0 := by
    intro ε
    exact onlinePLBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) μ baseBatch ε
  have hBatchTheta : AccuracyTheta (fun ε => ((batch ε).1 : ℝ))
      varianceScale := by
    simpa [batch, varianceScale] using
      onlinePLBatchScheduleFromBase_accuracyTheta n b0
        (varianceAggregateSq σ) μ hvar μ.property baseBatch hBaseOrder
  have hFloor : ∀ ε,
      varianceAggregateSq σ /
          (n.1 * (batch ε).1 * (μ : ℝ)) ≤ (ε : ℝ) / 2 := by
    intro ε
    simpa [batch] using onlinePLBatchScheduleFromBase_variance_floor
      n b0 (varianceAggregateSq σ) μ hvar μ.property baseBatch ε
  have hStep : ∀ ε, OnlineVRPLStepsizeCondition (step ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      (refresh ε) ω μ n b0 := by
    intro ε
    simpa [step] using onlinePLDensityCanonicalStepsize_condition (hrefresh ε)
  have hBudget : ∀ ε,
      (1 - (step ε : ℝ) * (μ : ℝ)) ^ (K ε).1 * gap +
        (1 - (step ε : ℝ) * (μ : ℝ)) ^ (K ε).1 *
          (step ε : ℝ) / refresh ε *
            (varianceAggregateSq σ / (n.1 * (batch ε).1)) +
        varianceAggregateSq σ /
          (n.1 * (batch ε).1 * (μ : ℝ)) ≤ (ε : ℝ) := by
    apply onlineExecutablePLScheduledHorizon_budget_of_positive_gap
      gap (varianceAggregateSq σ) step refresh μ batch
        (by simpa [gap] using hGap) hvar hrefresh
    · intro ε
      exact (hStep ε).2
    · exact hFloor
  have hK : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
    simpa [K, gap, step, batch, factor, iterationScale] using
      onlineExecutablePLScheduledHorizon_bigO_canonical
        (d := d) (b0 := b0) hrefresh hL hℒ hω hvar
          (by simpa [gap] using hGap) hBatchTheta.1
          (by simpa [batch] using hSchedule)
  have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
    (hrefresh ε).1 (hrefresh ε).2
      (expectedDensity_nonneg_of_unbiased hQuantizer)
      (by simpa [batch] using hSchedule ε)
  let oraclePayload : Accuracy → ℝ := fun ε =>
    refresh ε * (batch ε).1 + 2 * (1 - refresh ε) * b0.1
  let communicationPayload : Accuracy → ℝ := fun ε =>
    refresh ε * d.1 +
      (1 - refresh ε) * expectedDensity A.quantizer
  have hIterationNonneg : ∀ᶠ ε in accuracyToZero,
      0 ≤ iterationScale ε := by
    filter_upwards [eventually_one_le_log_gap_div_accuracy hgap] with ε hlog
    dsimp [iterationScale, factor]
    exact mul_nonneg
      ((div_pos zero_lt_one (hrefresh ε).1).le.trans (le_max_left _ _))
      (by linarith)
  have hOracle : AccuracyBigO
      (fun ε => ((batch ε).1 : ℝ) + (K ε).1 * oraclePayload ε)
      (fun ε => varianceScale ε + iterationScale ε * b0.1) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := (b0.1 : ℝ)) (factor := 3)
      hBatchTheta.1 hK (fun _ => by positivity) (fun _ => by positivity)
      (Filter.Eventually.of_forall fun ε => by
        dsimp [varianceScale]
        exact div_nonneg hvar
          (mul_nonneg (mul_nonneg (by positivity) μ.property.le)
            ε.property.le))
      hIterationNonneg
    · intro ε
      dsimp [oraclePayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg
          (mul_nonneg (by norm_num) (sub_nonneg.mpr (hrefresh ε).2))
          (by positivity))
    · exact_mod_cast b0.2
    · norm_num
    · intro ε
      simpa [oraclePayload] using (hPayload ε).2.1
  have hDensityPos : 0 < expectedDensity A.quantizer :=
    (hPayload ⟨1, by norm_num⟩).1
  have hCommunication : AccuracyBigO
      (fun ε => (d.1 : ℝ) + (K ε).1 * communicationPayload ε)
      (fun ε => (d.1 : ℝ) +
        iterationScale ε * expectedDensity A.quantizer) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := expectedDensity A.quantizer) (factor := 2)
      (Asymptotics.isBigO_refl _ _) hK (fun _ => by positivity)
      (fun _ => by positivity)
      (Filter.Eventually.of_forall fun _ => by positivity)
      hIterationNonneg
    · intro ε
      dsimp [communicationPayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg (sub_nonneg.mpr (hrefresh ε).2)
          (expectedDensity_nonneg_of_unbiased hQuantizer))
    · exact hDensityPos
    · norm_num
    · intro ε
      simpa [communicationPayload] using (hPayload ε).2.2
  apply onlineParameterizedExecutablePLMeasuredCostComplexity_of_budget
    A x0 xStar step refresh hrefresh batch K Llocal ℒlocal σ ω fStar μ
      hLower hSmooth hVariance hPL hQuantizer hBatch
  · intro ε
    simpa [batch, step] using hAverageSmooth ε
  · exact hStep
  · intro ε
    simpa [K, gap, step, batch] using hBudget ε
  · exact Or.inr hK
  · change AccuracyBigO
      (fun ε => onlineOracleCallCount (batch ε) b0 (K ε) (refresh ε))
      (fun ε => varianceScale ε + b0.1 * iterationScale ε)
    simpa [onlineOracleCallCount, oraclePayload, mul_comm] using hOracle
  · change AccuracyBigO
      (fun ε => allWorkerCommunicationCount d (K ε) (refresh ε)
        (expectedDensity A.quantizer))
      (fun ε => d.1 + expectedDensity A.quantizer * iterationScale ε)
    simpa [allWorkerCommunicationCount, communicationPayload, mul_comm] using
      hCommunication

/-- The nonzero base batch used when the source variance scale vanishes.
A positive `Count` family cannot be `Theta(0)`, so the executable degenerate
branch uses this explicit constant representative before applying the existing
pointwise-safe batch inflation. -/
def onlineDegenerateBaseBatch : Accuracy → Count :=
  fun _ => ⟨1, by norm_num⟩

/-- A one-round density-scheduled executable experiment has constant analytic
oracle and communication counts whenever its positive refresh batch is
uniformly bounded.  This scalar lemma is used only as the target bound for the
measured integrals; the integrability and expectation transfer still come from
the generated pathwise costs. -/
theorem onlineOneRoundDensityScheduledCostCounts_bigO_one
    {d b0 : Count} {batch : Accuracy → Count} {refresh : Accuracy → ℝ}
    {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ)
    (hRefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity Q) d (batch ε) b0)
    (hDensity : 0 ≤ expectedDensity Q)
    (B : ℝ)
    (hBatchBound : ∀ ε, ((batch ε).1 : ℝ) ≤ B) :
    AccuracyBigO
        (fun ε => onlineOracleCallCount (batch ε) b0
          ⟨1, by norm_num⟩ (refresh ε)) (fun _ => 1) ∧
      AccuracyBigO
        (fun ε => allWorkerCommunicationCount d ⟨1, by norm_num⟩
          (refresh ε) (expectedDensity Q)) (fun _ => 1) := by
  have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
    (hRefresh ε).1 (hRefresh ε).2 hDensity (hSchedule ε)
  constructor
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨B + 3 * b0.1, Filter.Eventually.of_forall ?_⟩
    intro ε
    have hActual : 0 ≤ onlineOracleCallCount (batch ε) b0
        ⟨1, by norm_num⟩ (refresh ε) := by
      unfold onlineOracleCallCount
      have hp := (hRefresh ε).1.le
      have hp1 := sub_nonneg.mpr (hRefresh ε).2
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hActual, norm_one, mul_one]
    unfold onlineOracleCallCount
    norm_num
    nlinarith [(hPayload ε).2.1, hBatchBound ε]
  · unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨d.1 + 2 * expectedDensity Q, Filter.Eventually.of_forall ?_⟩
    intro ε
    have hActual : 0 ≤ allWorkerCommunicationCount d ⟨1, by norm_num⟩
        (refresh ε) (expectedDensity Q) := by
      unfold allWorkerCommunicationCount
      have hp := (hRefresh ε).1.le
      have hp1 := sub_nonneg.mpr (hRefresh ε).2
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hActual, norm_one, mul_one]
    unfold allWorkerCommunicationCount
    norm_num
    nlinarith [(hPayload ε).2.2]

/-- Executable density-scheduled D.3 and D.4 in the fully degenerate branch.
When both the sampled-gradient variance and the relevant initial gaps vanish,
one generated round suffices.  The initial batch is still sampled and charged:
the two measured packages integrate `onlineWorkerOracleCost` and
`onlineWorkerCommunicationCost` under the matching parameterized
`onlinePathLaw`.  Their costs are bounded by a constant rather than by the
impossible source premise that a positive batch family is `Theta(0)`. -/
theorem onlineExecutableDensityScheduled_measured_cost_complexity_of_zero_gaps_zero_variance
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (refreshNonconvex refreshPL : Accuracy → ℝ)
    (hRefreshNonconvex : ∀ ε,
      RefreshProbabilityAdmissible (refreshNonconvex ε))
    (hRefreshPL : ∀ ε, RefreshProbabilityAdmissible (refreshPL ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hVarianceZero : varianceAggregateSq σ = 0)
    (hNonconvexGapZero :
      globalObjective (onlineLocalProblem A.problem) x0 - fStar = 0)
    (hPLGapZero : globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar = 0)
    (hScheduleNonconvex : ∀ ε,
      refreshNonconvex ε = onlineDensityBatchRefreshSchedule
        (expectedDensity A.quantizer) d
        (onlineNonconvexBatchScheduleFromBase n b0
          (varianceAggregateSq σ) onlineDegenerateBaseBatch ε) b0)
    (hSchedulePL : ∀ ε,
      refreshPL ε = onlineDensityBatchRefreshSchedule
        (expectedDensity A.quantizer) d
        (onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ onlineDegenerateBaseBatch ε) b0)
    (hAverageSmoothNonconvex : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refreshNonconvex ε) ω n b0)
            (refreshNonconvex ε) (hRefreshNonconvex ε)) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) onlineDegenerateBaseBatch ε)) ℒlocal)
    (hAverageSmoothPL : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refreshPL ε) ω μ n b0)
            (refreshPL ε) (hRefreshPL ε)) x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ onlineDegenerateBaseBatch ε)) ℒlocal) :
    let nonconvexBatch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) onlineDegenerateBaseBatch
    let plBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ onlineDegenerateBaseBatch
    let nonconvexStep := fun ε => onlineDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      (refreshNonconvex ε) ω n b0
    let plStep := fun ε => onlinePLDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      (refreshPL ε) ω μ n b0
    let oneRound : Accuracy → Count := fun _ => ⟨1, by norm_num⟩
    OnlineParameterizedExecutableNonconvexMeasuredCostComplexity
        (fun ε => onlineDataWithParameters A (nonconvexStep ε)
          (refreshNonconvex ε) (hRefreshNonconvex ε))
        x0 nonconvexBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) onlineDegenerateBaseBatch ε)
        oneRound (fun _ => 1)
        (fun _ => 1) (fun _ => 1) ∧
      OnlineParameterizedExecutablePLMeasuredCostComplexity
        (fun ε => onlineDataWithParameters A (plStep ε)
          (refreshPL ε) (hRefreshPL ε))
        x0 xStar plBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ onlineDegenerateBaseBatch ε)
        oneRound (fun _ => 1)
        (fun _ => 1) (fun _ => 1) := by
  dsimp only
  let oneRound : Accuracy → Count := fun _ => ⟨1, by norm_num⟩
  have hIteration : AccuracyIterationBigO
      (fun ε => ((oneRound ε).1 : ℝ)) (fun _ => 1) := by
    refine Or.inr ?_
    unfold AccuracyBigO
    simpa [oneRound] using
      (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ)) accuracyToZero)
  have hDensity : 0 ≤ expectedDensity A.quantizer :=
    expectedDensity_nonneg_of_unbiased hQuantizer
  constructor
  · apply onlineParameterizedExecutableNonconvexMeasuredCostComplexity_of_budget
      A x0
      (fun ε => onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (refreshNonconvex ε) ω n b0)
      refreshNonconvex hRefreshNonconvex
      (onlineNonconvexBatchScheduleFromBase n b0
        (varianceAggregateSq σ) onlineDegenerateBaseBatch)
      oneRound Llocal ℒlocal σ ω fStar hLower hSmooth hVariance hQuantizer
    · intro ε
      simpa using hAverageSmoothNonconvex ε
    · intro ε
      exact onlineDensityCanonicalStepsize_condition
    · intro ε
      rw [hNonconvexGapZero]
      simp [oneRound, hVarianceZero]
      exact sq_nonneg (ε : ℝ)
    · exact hIteration
    · have hCosts := onlineOneRoundDensityScheduledCostCounts_bigO_one
        A.quantizer hRefreshNonconvex hScheduleNonconvex hDensity
          (b0.1 + 2)
          (fun ε => by
            norm_num [onlineNonconvexBatchScheduleFromBase,
              onlineDegenerateBaseBatch, hVarianceZero]
            norm_cast)
      simpa [oneRound] using hCosts.1
    · have hCosts := onlineOneRoundDensityScheduledCostCounts_bigO_one
        A.quantizer hRefreshNonconvex hScheduleNonconvex hDensity
          (b0.1 + 2)
          (fun ε => by
            norm_num [onlineNonconvexBatchScheduleFromBase,
              onlineDegenerateBaseBatch, hVarianceZero]
            norm_cast)
      simpa [oneRound] using hCosts.2
  · apply onlineParameterizedExecutablePLMeasuredCostComplexity_of_budget
      A x0 xStar
      (fun ε => onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
        (rootMeanSquare ℒlocal) (refreshPL ε) ω μ n b0)
      refreshPL hRefreshPL
      (onlinePLBatchScheduleFromBase n b0
        (varianceAggregateSq σ) μ onlineDegenerateBaseBatch)
      oneRound Llocal ℒlocal σ ω fStar μ hLower hSmooth hVariance hPL
        hQuantizer
    · intro ε
      simpa using hAverageSmoothPL ε
    · intro ε
      exact onlinePLDensityCanonicalStepsize_condition (hRefreshPL ε)
    · intro ε
      rw [hPLGapZero]
      simp [oneRound, hVarianceZero]
      exact ε.property.le
    · exact hIteration
    · have hCosts := onlineOneRoundDensityScheduledCostCounts_bigO_one
        A.quantizer hRefreshPL hSchedulePL hDensity (b0.1 + 2)
          (fun ε => by
            norm_num [onlinePLBatchScheduleFromBase,
              onlineDegenerateBaseBatch, hVarianceZero]
            norm_cast)
      simpa [oneRound] using hCosts.1
    · have hCosts := onlineOneRoundDensityScheduledCostCounts_bigO_one
        A.quantizer hRefreshPL hSchedulePL hDensity (b0.1 + 2)
          (fun ε => by
            norm_num [onlinePLBatchScheduleFromBase,
              onlineDegenerateBaseBatch, hVarianceZero]
            norm_cast)
      simpa [oneRound] using hCosts.2

/-- If the D.3 objective gap is zero but the sampled initializer has positive
variance, the optimization ceiling disappears while the initializer ceiling
remains.  The latter is controlled by `1 / p` using the same variance floor
that controls the steady-state term. -/
theorem onlineExecutableNonconvexScheduledHorizon_bigO_of_gap_zero
    {n : Count} (gap variance : ℝ)
    (step : Accuracy → PositiveStepsize) (refresh : Accuracy → ℝ)
    (batch : Accuracy → Count)
    (hGapZero : gap = 0) (hvariance : 0 ≤ variance)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hFloor : ∀ ε,
      variance / (n.1 * (batch ε).1) ≤ (ε : ℝ) ^ 2 / 2) :
    AccuracyBigO
      (fun ε => ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ))
      (fun ε => 1 + 1 / refresh ε) := by
  unfold AccuracyBigO
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, Filter.Eventually.of_forall ?_⟩
  intro ε
  let initializationVariance : ℝ := variance / (n.1 * (batch ε).1)
  let initializationQuota : ℝ :=
    4 * initializationVariance / (refresh ε * (ε : ℝ) ^ 2)
  have hp : 0 < refresh ε := (hrefresh ε).1
  have hepsSq : 0 < (ε : ℝ) ^ 2 := sq_pos_of_pos ε.property
  have hinitNonneg : 0 ≤ initializationQuota := by
    dsimp [initializationQuota, initializationVariance]
    positivity
  have hceil := natCast_max_one_ceil_le_add_two initializationQuota hinitNonneg
  have hinitBound : initializationQuota ≤ 2 * (1 / refresh ε) := by
    have hdiv := div_le_div_of_nonneg_right (hFloor ε)
      (mul_nonneg hp.le hepsSq.le)
    dsimp [initializationQuota, initializationVariance]
    calc
      4 * (variance / (n.1 * (batch ε).1)) /
          (refresh ε * (ε : ℝ) ^ 2) =
          4 * ((variance / (n.1 * (batch ε).1)) /
            (refresh ε * (ε : ℝ) ^ 2)) := by ring
      _ ≤ 4 * (((ε : ℝ) ^ 2 / 2) /
            (refresh ε * (ε : ℝ) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 2 * (1 / refresh ε) := by
        field_simp [ne_of_gt hp, ne_of_gt ε.property]
        ring
  have hK :
      ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ) ≤
          initializationQuota + 2 := by
    simpa [onlineExecutableNonconvexScheduledHorizon, hGapZero,
      initializationQuota, initializationVariance,
      max_eq_right hinitNonneg] using hceil
  have htarget : 0 < 1 + 1 / refresh ε := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ)),
    Real.norm_eq_abs, abs_of_pos htarget]
  calc
    ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ) ≤
        initializationQuota + 2 := hK
    _ ≤ 2 * (1 + 1 / refresh ε) := by linarith

/-- The one-round executable D.4 budget in the zero-gap branch.  The source
batch floor pays the stationary variance, and `2 γ μ ≤ p` pays the sampled
initializer term. -/
theorem onlineExecutablePLOneRound_budget_of_gap_zero
    {n : Count} (gap variance : ℝ)
    (step : Accuracy → PositiveStepsize) (refresh : Accuracy → ℝ)
    (μ : PositivePLParameter) (batch : Accuracy → Count)
    (hGapZero : gap = 0) (hvariance : 0 ≤ variance)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hCoupling : ∀ ε,
      2 * (step ε : ℝ) * (μ : ℝ) ≤ refresh ε)
    (hFloor : ∀ ε,
      variance / (n.1 * (batch ε).1 * (μ : ℝ)) ≤ (ε : ℝ) / 2) :
    ∀ ε,
      (1 - (step ε : ℝ) * (μ : ℝ)) * gap +
        (1 - (step ε : ℝ) * (μ : ℝ)) *
          (step ε : ℝ) / refresh ε *
            (variance / (n.1 * (batch ε).1)) +
        variance / (n.1 * (batch ε).1 * (μ : ℝ)) ≤ (ε : ℝ) := by
  intro ε
  let c : ℝ := (step ε : ℝ) * (μ : ℝ)
  let floor : ℝ := variance / (n.1 * (batch ε).1 * (μ : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (step ε).property μ.property
  have hc1 : c ≤ 1 := by
    have hp1 := (hrefresh ε).2
    have hcoupling := hCoupling ε
    dsimp [c]
    nlinarith
  have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  have hfloorNonneg : 0 ≤ floor := by
    dsimp [floor]
    exact div_nonneg hvariance
      (mul_nonneg (mul_nonneg (by positivity) (by positivity)) μ.property.le)
  have hRatio : c / refresh ε ≤ 1 / 2 := by
    rw [div_le_iff₀ (hrefresh ε).1]
    dsimp [c]
    nlinarith [hCoupling ε]
  have hRatioNonneg : 0 ≤ c / refresh ε :=
    div_nonneg hc.le (hrefresh ε).1.le
  have hInitial :
      (1 - c) * (step ε : ℝ) / refresh ε *
          (variance / (n.1 * (batch ε).1)) ≤ floor / 2 := by
    have hRewrite :
        (1 - c) * (step ε : ℝ) / refresh ε *
            (variance / (n.1 * (batch ε).1)) =
          ((1 - c) * (c / refresh ε)) * floor := by
      dsimp [c, floor]
      field_simp [ne_of_gt (hrefresh ε).1, ne_of_gt μ.property]
    rw [hRewrite]
    calc
      ((1 - c) * (c / refresh ε)) * floor ≤
          (1 * (1 / 2 : ℝ)) * floor := by
        gcongr
        · linarith
      _ = floor / 2 := by ring
  rw [hGapZero]
  dsimp [c, floor] at hInitial ⊢
  linarith [hInitial, hFloor ε]

/-- Corrected executable D.3 endpoint for zero initial gap and positive
stochastic-gradient variance.  The positive sampled batch is source-scaled,
while the nonvanishing `1 + 1 / p` horizon records the initializer term that
is absent from the proof-exact process. -/
theorem onlineExecutableNonconvexDensityScheduled_measured_cost_complexity_of_zero_gap_positive_variance
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count) (refresh : Accuracy → ℝ)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hVariancePositive : 0 < varianceAggregateSq σ)
    (hGapZero : globalObjective (onlineLocalProblem A.problem) x0 - fStar = 0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refresh ε) ω n b0)
            (refresh ε) (hrefresh ε)) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) baseBatch ε)) ℒlocal)
    (hBaseOrder : AccuracyTheta (fun ε => ((baseBatch ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
        (onlineNonconvexBatchScheduleFromBase n b0
          (varianceAggregateSq σ) baseBatch ε) b0) :
    let batch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) baseBatch
    let step := fun ε => onlineDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω n b0
    let gap := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let K := onlineExecutableNonconvexScheduledHorizon
      gap (varianceAggregateSq σ) step refresh n batch
    let iterationScale := fun ε : Accuracy => 1 + 1 / refresh ε
    let varianceScale := fun ε : Accuracy =>
      varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)
    OnlineParameterizedExecutableNonconvexMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε))
      x0 batch
      (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) baseBatch ε)
      K iterationScale
      (fun ε => varianceScale ε + iterationScale ε * b0.1)
      (fun ε => d.1 + iterationScale ε * expectedDensity A.quantizer) := by
  dsimp
  let batch : Accuracy → Count := onlineNonconvexBatchScheduleFromBase n b0
    (varianceAggregateSq σ) baseBatch
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) (refresh ε) ω n b0
  let gap : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let K : Accuracy → Count := onlineExecutableNonconvexScheduledHorizon
    gap (varianceAggregateSq σ) step refresh n batch
  let iterationScale : Accuracy → ℝ := fun ε => 1 + 1 / refresh ε
  let varianceScale : Accuracy → ℝ := fun ε =>
    varianceAggregateSq σ / (n.1 * (ε : ℝ) ^ 2)
  have hvar : 0 ≤ varianceAggregateSq σ := hVariancePositive.le
  have hBatch : ∀ ε, OnlineBatchAdmissible (batch ε) b0 := by
    intro ε
    exact onlineNonconvexBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) baseBatch ε
  have hBatchTheta : AccuracyTheta (fun ε => ((batch ε).1 : ℝ))
      varianceScale := by
    simpa [batch, varianceScale] using
      onlineNonconvexBatchScheduleFromBase_accuracyTheta n b0
        (varianceAggregateSq σ) hvar baseBatch hBaseOrder
  have hFloor : ∀ ε,
      varianceAggregateSq σ / (n.1 * (batch ε).1) ≤
        (ε : ℝ) ^ 2 / 2 := by
    intro ε
    simpa [batch] using onlineNonconvexBatchScheduleFromBase_variance_floor
      n b0 (varianceAggregateSq σ) hvar baseBatch ε
  have hScheduled := onlineExecutableNonconvexDensityScheduled_budget
    (d := d) (b0 := b0) gap (varianceAggregateSq σ) baseBatch step refresh
      (expectedDensity A.quantizer) hvar (by simp [gap, hGapZero])
      hrefresh (by simpa [batch] using hSchedule)
  have hK : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
    simpa [K, gap, batch, iterationScale] using
      onlineExecutableNonconvexScheduledHorizon_bigO_of_gap_zero
        (n := n) gap (varianceAggregateSq σ) step refresh batch
          (by simpa [gap] using hGapZero) hvar hrefresh hFloor
  have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
    (hrefresh ε).1 (hrefresh ε).2
      (expectedDensity_nonneg_of_unbiased hQuantizer)
      (by simpa [batch] using hSchedule ε)
  let oraclePayload : Accuracy → ℝ := fun ε =>
    refresh ε * (batch ε).1 + 2 * (1 - refresh ε) * b0.1
  let communicationPayload : Accuracy → ℝ := fun ε =>
    refresh ε * d.1 + (1 - refresh ε) * expectedDensity A.quantizer
  have hIterationNonneg : ∀ᶠ ε in accuracyToZero,
      0 ≤ iterationScale ε :=
    Filter.Eventually.of_forall fun ε => by
      dsimp [iterationScale]
      exact add_nonneg zero_le_one (one_div_nonneg.mpr (hrefresh ε).1.le)
  have hOracle : AccuracyBigO
      (fun ε => ((batch ε).1 : ℝ) + (K ε).1 * oraclePayload ε)
      (fun ε => varianceScale ε + iterationScale ε * b0.1) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := (b0.1 : ℝ)) (factor := 3)
      hBatchTheta.1 hK (fun _ => by positivity) (fun _ => by positivity)
      (Filter.Eventually.of_forall fun ε => by
        dsimp [varianceScale]
        positivity)
      hIterationNonneg
    · intro ε
      dsimp [oraclePayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg
          (mul_nonneg (by norm_num) (sub_nonneg.mpr (hrefresh ε).2))
          (by positivity))
    · exact_mod_cast b0.2
    · norm_num
    · intro ε
      simpa [oraclePayload] using (hPayload ε).2.1
  have hDensityPos : 0 < expectedDensity A.quantizer :=
    (hPayload ⟨1, by norm_num⟩).1
  have hCommunication : AccuracyBigO
      (fun ε => (d.1 : ℝ) + (K ε).1 * communicationPayload ε)
      (fun ε => (d.1 : ℝ) +
        iterationScale ε * expectedDensity A.quantizer) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := expectedDensity A.quantizer) (factor := 2)
      (Asymptotics.isBigO_refl _ _) hK (fun _ => by positivity)
      (fun _ => by positivity)
      (Filter.Eventually.of_forall fun _ => by positivity)
      hIterationNonneg
    · intro ε
      dsimp [communicationPayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg (sub_nonneg.mpr (hrefresh ε).2)
          (expectedDensity_nonneg_of_unbiased hQuantizer))
    · exact hDensityPos
    · norm_num
    · intro ε
      simpa [communicationPayload] using (hPayload ε).2.2
  apply onlineParameterizedExecutableNonconvexMeasuredCostComplexity_of_budget
    A x0 step refresh hrefresh batch K Llocal ℒlocal σ ω fStar
      hLower hSmooth hVariance hQuantizer hBatch
  · intro ε
    simpa [batch, step] using hAverageSmooth ε
  · intro ε
    exact onlineDensityCanonicalStepsize_condition
  · intro ε
    simpa [K, gap, step, batch] using hScheduled.2.2 ε
  · exact Or.inr hK
  · simpa [onlineOracleCallCount, batch, K, oraclePayload, varianceScale,
      iterationScale] using hOracle
  · simpa [allWorkerCommunicationCount, K, communicationPayload,
      iterationScale] using
      hCommunication

/-- Corrected executable D.4 endpoint for zero initial gap and positive
stochastic-gradient variance.  One generated round suffices, but the growing
sampled initializer remains visible in the measured oracle scale. -/
theorem onlineExecutablePLDensityScheduled_measured_cost_complexity_of_zero_gap_positive_variance
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count) (refresh : Accuracy → ℝ)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hVariancePositive : 0 < varianceAggregateSq σ)
    (hGapZero : globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar = 0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0)
            (refresh ε) (hrefresh ε)) x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hBaseOrder : AccuracyTheta (fun ε => ((baseBatch ε).1 : ℝ))
      (fun ε => varianceAggregateSq σ /
        (n.1 * (μ : ℝ) * (ε : ℝ))))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
        (onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ baseBatch ε) b0) :
    let batch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let step := fun ε => onlinePLDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0
    let oneRound : Accuracy → Count := fun _ => ⟨1, by norm_num⟩
    let varianceScale := fun ε : Accuracy => varianceAggregateSq σ /
      (n.1 * (μ : ℝ) * (ε : ℝ))
    OnlineParameterizedExecutablePLMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε))
      x0 xStar batch
      (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) μ baseBatch ε)
      oneRound (fun _ => 1)
      (fun ε => varianceScale ε + b0.1)
      (fun _ => d.1 + expectedDensity A.quantizer) := by
  dsimp
  let batch : Accuracy → Count := onlinePLBatchScheduleFromBase n b0
    (varianceAggregateSq σ) μ baseBatch
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0
  let oneRound : Accuracy → Count := fun _ => ⟨1, by norm_num⟩
  let varianceScale : Accuracy → ℝ := fun ε => varianceAggregateSq σ /
    (n.1 * (μ : ℝ) * (ε : ℝ))
  have hvar : 0 ≤ varianceAggregateSq σ := hVariancePositive.le
  have hBatch : ∀ ε, OnlineBatchAdmissible (batch ε) b0 := by
    intro ε
    exact onlinePLBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) μ baseBatch ε
  have hBatchTheta : AccuracyTheta (fun ε => ((batch ε).1 : ℝ))
      varianceScale := by
    simpa [batch, varianceScale] using
      onlinePLBatchScheduleFromBase_accuracyTheta n b0
        (varianceAggregateSq σ) μ hvar μ.property baseBatch hBaseOrder
  have hFloor : ∀ ε,
      varianceAggregateSq σ /
          (n.1 * (batch ε).1 * (μ : ℝ)) ≤ (ε : ℝ) / 2 := by
    intro ε
    simpa [batch] using onlinePLBatchScheduleFromBase_variance_floor
      n b0 (varianceAggregateSq σ) μ hvar μ.property baseBatch ε
  have hStep : ∀ ε, OnlineVRPLStepsizeCondition (step ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      (refresh ε) ω μ n b0 := by
    intro ε
    simpa [step] using onlinePLDensityCanonicalStepsize_condition (hrefresh ε)
  have hBudget := onlineExecutablePLOneRound_budget_of_gap_zero
    (n := n)
    (globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar)
    (varianceAggregateSq σ) step refresh μ batch hGapZero hvar hrefresh
      (fun ε => (hStep ε).2) hFloor
  have hK : AccuracyBigO (fun ε => ((oneRound ε).1 : ℝ)) (fun _ => 1) := by
    unfold AccuracyBigO
    simpa [oneRound] using
      (Asymptotics.isBigO_refl (fun _ : Accuracy => (1 : ℝ)) accuracyToZero)
  have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
    (hrefresh ε).1 (hrefresh ε).2
      (expectedDensity_nonneg_of_unbiased hQuantizer)
      (by simpa [batch] using hSchedule ε)
  let oraclePayload : Accuracy → ℝ := fun ε =>
    refresh ε * (batch ε).1 + 2 * (1 - refresh ε) * b0.1
  let communicationPayload : Accuracy → ℝ := fun ε =>
    refresh ε * d.1 + (1 - refresh ε) * expectedDensity A.quantizer
  have hOracle : AccuracyBigO
      (fun ε => ((batch ε).1 : ℝ) + (oneRound ε).1 * oraclePayload ε)
      (fun ε => varianceScale ε + (1 : ℝ) * b0.1) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := (b0.1 : ℝ)) (factor := 3)
      hBatchTheta.1 hK (fun _ => by positivity) (fun _ => by positivity)
      (Filter.Eventually.of_forall fun ε => by
        dsimp [varianceScale]
        exact div_nonneg hvar
          (mul_nonneg (mul_nonneg (by positivity) μ.property.le)
            ε.property.le))
      (Filter.Eventually.of_forall fun _ => by norm_num)
    · intro ε
      dsimp [oraclePayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg
          (mul_nonneg (by norm_num) (sub_nonneg.mpr (hrefresh ε).2))
          (by positivity))
    · exact_mod_cast b0.2
    · norm_num
    · intro ε
      simpa [oraclePayload] using (hPayload ε).2.1
  have hDensityPos : 0 < expectedDensity A.quantizer :=
    (hPayload ⟨1, by norm_num⟩).1
  have hCommunication : AccuracyBigO
      (fun ε => (d.1 : ℝ) + (oneRound ε).1 * communicationPayload ε)
      (fun _ => (d.1 : ℝ) + (1 : ℝ) * expectedDensity A.quantizer) := by
    apply accuracyBigO_add_mul_varying_payload
      (targetPayload := expectedDensity A.quantizer) (factor := 2)
      (Asymptotics.isBigO_refl _ _) hK (fun _ => by positivity)
      (fun _ => by positivity)
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall fun _ => by norm_num)
    · intro ε
      dsimp [communicationPayload]
      exact add_nonneg (mul_nonneg (hrefresh ε).1.le (by positivity))
        (mul_nonneg (sub_nonneg.mpr (hrefresh ε).2)
          (expectedDensity_nonneg_of_unbiased hQuantizer))
    · exact hDensityPos
    · norm_num
    · intro ε
      simpa [communicationPayload] using (hPayload ε).2.2
  apply onlineParameterizedExecutablePLMeasuredCostComplexity_of_budget
    A x0 xStar step refresh hrefresh batch oneRound Llocal ℒlocal σ ω fStar μ
      hLower hSmooth hVariance hPL hQuantizer hBatch
  · intro ε
    simpa [batch, step] using hAverageSmooth ε
  · exact hStep
  · intro ε
    simpa [oneRound] using hBudget ε
  · exact Or.inr hK
  · simpa [onlineOracleCallCount, batch, oneRound, oraclePayload] using hOracle
  · simpa [allWorkerCommunicationCount, oneRound, communicationPayload] using
      hCommunication

/-- When the online variance aggregate vanishes, the executable D.3 horizon
is controlled by its optimization ceiling alone.  This avoids the impossible
requirement that a positive refresh batch be `O(0)`. -/
theorem onlineExecutableNonconvexScheduledHorizon_bigO_of_variance_zero
    {n : Count} (gap variance : ℝ)
    (step : Accuracy → PositiveStepsize) (refresh : Accuracy → ℝ)
    (batch : Accuracy → Count) (hgap : 0 ≤ gap)
    (hVarianceZero : variance = 0) :
    AccuracyBigO
      (fun ε => ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ))
      (fun ε => 1 + 8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2)) := by
  unfold AccuracyBigO
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, Filter.Eventually.of_forall ?_⟩
  intro ε
  let q : ℝ := 8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (mul_nonneg (by norm_num) hgap)
      (mul_nonneg (step ε).property.le (sq_nonneg _))
  have hceil := natCast_max_one_ceil_le_add_two q hq
  have hK :
      ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ) ≤ q + 2 := by
    simpa [onlineExecutableNonconvexScheduledHorizon, q, hVarianceZero,
      max_eq_left hq] using hceil
  have htarget : 0 < 1 + q := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineExecutableNonconvexScheduledHorizon
        gap variance step refresh n batch ε).1 : ℝ)),
    Real.norm_eq_abs, abs_of_pos htarget]
  dsimp [q]
  dsimp [q] at hK
  linarith

/-- The positive-gap executable D.4 horizon has its elementary supplied-step
order independently of the variance scale.  In particular this remains valid
for the corrected positive batch used when that scale is zero. -/
theorem onlineExecutablePLScheduledHorizon_bigO_supplied
    (gap : ℝ) (step : Accuracy → PositiveStepsize)
    (mu : PositivePLParameter) :
    AccuracyBigO
      (fun ε => ((onlineExecutablePLScheduledHorizon gap step mu ε).1 : ℝ))
      (fun ε => 1 + max 0 (Real.log (4 * gap / (ε : ℝ)) /
        ((step ε : ℝ) * (mu : ℝ)))) := by
  unfold AccuracyBigO
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, Filter.Eventually.of_forall ?_⟩
  intro ε
  let raw : ℝ := Real.log (4 * gap / (ε : ℝ)) /
    ((step ε : ℝ) * (mu : ℝ))
  have hrawMax : raw ≤ max 0 raw := le_max_right _ _
  have hceilMono : Nat.ceil raw ≤ Nat.ceil (max 0 raw) :=
    Nat.ceil_mono hrawMax
  have hmaxMono : max 1 (Nat.ceil raw) ≤ max 1 (Nat.ceil (max 0 raw)) :=
    max_le_max_left 1 hceilMono
  have hceil := natCast_max_one_ceil_le_add_two
    (max 0 raw) (le_max_left _ _)
  have htarget : 0 < 1 + max 0 raw := by
    linarith [le_max_left (0 : ℝ) raw]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((onlineExecutablePLScheduledHorizon gap step mu ε).1 : ℝ)),
    Real.norm_eq_abs, abs_of_pos htarget]
  change ((max 1 (Nat.ceil raw) : ℕ) : ℝ) ≤ 2 * (1 + max 0 raw)
  have hmaxMonoReal : ((max 1 (Nat.ceil raw) : ℕ) : ℝ) ≤
      ((max 1 (Nat.ceil (max 0 raw)) : ℕ) : ℝ) := by
    exact_mod_cast hmaxMono
  exact hmaxMonoReal.trans (hceil.trans (by
    nlinarith [le_max_left (0 : ℝ) raw]))

/-- Convert a density-scheduled horizon bound into the corresponding online
oracle and communication count bounds.  The initialization term remains the
actual positive batch, rather than the vanishing variance proxy. -/
theorem onlineDensityScheduledCostCounts_bigO
    {d b0 : Count} {batch K : Accuracy → Count}
    {refresh iterationScale : Accuracy → ℝ}
    {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Quantizer d Ξ)
    (hRefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity Q) d (batch ε) b0)
    (hDensity : 0 ≤ expectedDensity Q)
    (hIteration : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale)
    (hIterationNonneg : ∀ᶠ ε in accuracyToZero, 0 ≤ iterationScale ε) :
    AccuracyBigO
        (fun ε => onlineOracleCallCount (batch ε) b0 (K ε) (refresh ε))
        (fun ε => (batch ε).1 + iterationScale ε * b0.1) ∧
      AccuracyBigO
        (fun ε => allWorkerCommunicationCount d (K ε) (refresh ε)
          (expectedDensity Q))
        (fun ε => d.1 + iterationScale ε * expectedDensity Q) := by
  have hPayload (ε : Accuracy) := online_density_schedule_payload_bounds
    (hRefresh ε).1 (hRefresh ε).2 hDensity (hSchedule ε)
  let oraclePayload : Accuracy → ℝ := fun ε =>
    refresh ε * (batch ε).1 + 2 * (1 - refresh ε) * b0.1
  let communicationPayload : Accuracy → ℝ := fun ε =>
    refresh ε * d.1 + (1 - refresh ε) * expectedDensity Q
  constructor
  · have hOracle : AccuracyBigO
        (fun ε => ((batch ε).1 : ℝ) + (K ε).1 * oraclePayload ε)
        (fun ε => ((batch ε).1 : ℝ) + iterationScale ε * b0.1) := by
      apply accuracyBigO_add_mul_varying_payload
        (targetPayload := (b0.1 : ℝ)) (factor := 3)
        (Asymptotics.isBigO_refl _ _) hIteration
        (fun _ => by positivity) (fun _ => by positivity)
        (Filter.Eventually.of_forall fun _ => by positivity)
        hIterationNonneg
      · intro ε
        dsimp [oraclePayload]
        exact add_nonneg (mul_nonneg (hRefresh ε).1.le (by positivity))
          (mul_nonneg
            (mul_nonneg (by norm_num) (sub_nonneg.mpr (hRefresh ε).2))
            (by positivity))
      · exact_mod_cast b0.2
      · norm_num
      · intro ε
        simpa [oraclePayload] using (hPayload ε).2.1
    simpa [onlineOracleCallCount, oraclePayload] using hOracle
  · have hDensityPos : 0 < expectedDensity Q :=
      (hPayload ⟨1, by norm_num⟩).1
    have hCommunication : AccuracyBigO
        (fun ε => (d.1 : ℝ) + (K ε).1 * communicationPayload ε)
        (fun ε => (d.1 : ℝ) +
          iterationScale ε * expectedDensity Q) := by
      apply accuracyBigO_add_mul_varying_payload
        (targetPayload := expectedDensity Q) (factor := 2)
        (Asymptotics.isBigO_refl _ _) hIteration
        (fun _ => by positivity) (fun _ => by positivity)
        (Filter.Eventually.of_forall fun _ => by positivity)
        hIterationNonneg
      · intro ε
        dsimp [communicationPayload]
        exact add_nonneg (mul_nonneg (hRefresh ε).1.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr (hRefresh ε).2) hDensity)
      · exact hDensityPos
      · norm_num
      · intro ε
        simpa [communicationPayload] using (hPayload ε).2.2
    simpa [allWorkerCommunicationCount, communicationPayload] using
      hCommunication

/-- Executable density-scheduled D.3 for a positive initial gap and a zero
variance aggregate.  The source's `Theta(0)` batch prescription is replaced
by the explicit positive `onlineDegenerateBaseBatch`; the sampled initializer
is still present in both the process and the measured oracle integral. -/
theorem onlineExecutableNonconvexDensityScheduled_measured_cost_complexity_of_positive_gap_zero_variance
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (refresh : Accuracy → ℝ)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hVarianceZero : varianceAggregateSq σ = 0)
    (hGap : 0 < globalObjective (onlineLocalProblem A.problem) x0 - fStar)
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
        (onlineNonconvexBatchScheduleFromBase n b0
          (varianceAggregateSq σ) onlineDegenerateBaseBatch ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refresh ε) ω n b0)
            (refresh ε) (hrefresh ε)) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) onlineDegenerateBaseBatch ε)) ℒlocal) :
    let batch := onlineNonconvexBatchScheduleFromBase n b0
      (varianceAggregateSq σ) onlineDegenerateBaseBatch
    let step := fun ε => onlineDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω n b0
    let gap := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let K := onlineExecutableNonconvexScheduledHorizon
      gap (varianceAggregateSq σ) step refresh n batch
    let iterationScale := fun ε : Accuracy =>
      1 + 8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2)
    OnlineParameterizedExecutableNonconvexMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε))
      x0 batch
      (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) onlineDegenerateBaseBatch ε)
      K iterationScale
      (fun ε => (batch ε).1 + iterationScale ε * b0.1)
      (fun ε => d.1 + iterationScale ε * expectedDensity A.quantizer) := by
  dsimp
  let batch : Accuracy → Count := onlineNonconvexBatchScheduleFromBase n b0
    (varianceAggregateSq σ) onlineDegenerateBaseBatch
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlineDensityCanonicalStepsize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) (refresh ε) ω n b0
  let gap : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let K : Accuracy → Count := onlineExecutableNonconvexScheduledHorizon
    gap (varianceAggregateSq σ) step refresh n batch
  let iterationScale : Accuracy → ℝ := fun ε =>
    1 + 8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2)
  have hgap : 0 < gap := by simpa [gap] using hGap
  have hvar : 0 ≤ varianceAggregateSq σ := by
    unfold varianceAggregateSq meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hBatch : ∀ ε, OnlineBatchAdmissible (batch ε) b0 := by
    intro ε
    exact onlineNonconvexBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) onlineDegenerateBaseBatch ε
  have hScheduled := onlineExecutableNonconvexDensityScheduled_budget
    (d := d) (b0 := b0) gap (varianceAggregateSq σ)
      onlineDegenerateBaseBatch step refresh (expectedDensity A.quantizer)
      hvar hgap.le hrefresh (by simpa [batch] using hSchedule)
  have hK : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
    simpa [K, iterationScale] using
      onlineExecutableNonconvexScheduledHorizon_bigO_of_variance_zero
        (n := n) gap (varianceAggregateSq σ) step refresh batch
          hgap.le hVarianceZero
  have hIterationNonneg : ∀ᶠ ε in accuracyToZero,
      0 ≤ iterationScale ε :=
    Filter.Eventually.of_forall fun ε => by
      dsimp [iterationScale]
      have : 0 ≤ 8 * gap / ((step ε : ℝ) * (ε : ℝ) ^ 2) := by
        exact div_nonneg (mul_nonneg (by norm_num) hgap.le)
          (mul_nonneg (step ε).property.le (sq_nonneg _))
      linarith
  have hCosts := onlineDensityScheduledCostCounts_bigO
    A.quantizer hrefresh (by simpa [batch] using hSchedule)
      (expectedDensity_nonneg_of_unbiased hQuantizer) hK hIterationNonneg
  apply onlineParameterizedExecutableNonconvexMeasuredCostComplexity_of_budget
    A x0 step refresh hrefresh batch K Llocal ℒlocal σ ω fStar
      hLower hSmooth hVariance hQuantizer hBatch
  · intro ε
    simpa [batch, step] using hAverageSmooth ε
  · intro ε
    exact onlineDensityCanonicalStepsize_condition
  · intro ε
    simpa [K, gap, step, batch] using hScheduled.2.2 ε
  · exact Or.inr hK
  · simpa [batch, K, iterationScale] using hCosts.1
  · simpa [K, iterationScale] using hCosts.2

/-- Executable density-scheduled D.4 for a positive initial gap and zero
variance.  As in the D.3 correction above, the positive sampled initializer
is charged explicitly instead of being identified with the zero variance
proxy appearing in the source's asymptotic batch formula. -/
theorem onlineExecutablePLDensityScheduled_measured_cost_complexity_of_positive_gap_zero_variance
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (refresh : Accuracy → ℝ)
    (hrefresh : ∀ ε, RefreshProbabilityAdmissible (refresh ε))
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hVarianceZero : varianceAggregateSq σ = 0)
    (hGap : 0 < globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar)
    (hSchedule : ∀ ε, refresh ε = onlineDensityBatchRefreshSchedule
      (expectedDensity A.quantizer) d
        (onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ onlineDegenerateBaseBatch ε) b0)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A
            (onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
              (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0)
            (refresh ε) (hrefresh ε)) x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ onlineDegenerateBaseBatch ε)) ℒlocal) :
    let batch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ onlineDegenerateBaseBatch
    let step := fun ε => onlinePLDensityCanonicalStepsize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0
    let gap := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let K := onlineExecutablePLScheduledHorizon gap step μ
    let iterationScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * gap / (ε : ℝ)) /
        ((step ε : ℝ) * (μ : ℝ)))
    OnlineParameterizedExecutablePLMeasuredCostComplexity
      (fun ε => onlineDataWithParameters A (step ε) (refresh ε) (hrefresh ε))
      x0 xStar batch
      (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) μ onlineDegenerateBaseBatch ε)
      K iterationScale
      (fun ε => (batch ε).1 + iterationScale ε * b0.1)
      (fun ε => d.1 + iterationScale ε * expectedDensity A.quantizer) := by
  dsimp
  let batch : Accuracy → Count := onlinePLBatchScheduleFromBase n b0
    (varianceAggregateSq σ) μ onlineDegenerateBaseBatch
  let step : Accuracy → PositiveStepsize := fun ε =>
    onlinePLDensityCanonicalStepsize (rootMeanSquare Llocal)
      (rootMeanSquare ℒlocal) (refresh ε) ω μ n b0
  let gap : ℝ := globalObjective (onlineLocalProblem A.problem) x0 -
    globalObjective (onlineLocalProblem A.problem) xStar
  let K : Accuracy → Count := onlineExecutablePLScheduledHorizon gap step μ
  let iterationScale : Accuracy → ℝ := fun ε =>
    1 + max 0 (Real.log (4 * gap / (ε : ℝ)) /
      ((step ε : ℝ) * (μ : ℝ)))
  have hgap : 0 < gap := by simpa [gap] using hGap
  have hvar : 0 ≤ varianceAggregateSq σ := hVarianceZero.symm.le
  have hBatch : ∀ ε, OnlineBatchAdmissible (batch ε) b0 := by
    intro ε
    exact onlinePLBatchScheduleFromBase_admissible n b0
      (varianceAggregateSq σ) μ onlineDegenerateBaseBatch ε
  have hStep : ∀ ε, OnlineVRPLStepsizeCondition (step ε)
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      (refresh ε) ω μ n b0 := by
    intro ε
    exact onlinePLDensityCanonicalStepsize_condition (hrefresh ε)
  have hFloor : ∀ ε,
      varianceAggregateSq σ / (n.1 * (batch ε).1 * (μ : ℝ)) ≤
        (ε : ℝ) / 2 := by
    intro ε
    rw [hVarianceZero]
    simpa only [zero_div] using
      (div_nonneg ε.property.le (by norm_num : (0 : ℝ) ≤ 2))
  have hBudget := onlineExecutablePLScheduledHorizon_budget_of_positive_gap
    gap (varianceAggregateSq σ) step refresh μ batch hgap hvar hrefresh
      (fun ε => (hStep ε).2) hFloor
  have hK : AccuracyBigO (fun ε => ((K ε).1 : ℝ)) iterationScale := by
    simpa [K, iterationScale] using
      onlineExecutablePLScheduledHorizon_bigO_supplied gap step μ
  have hIterationNonneg : ∀ᶠ ε in accuracyToZero,
      0 ≤ iterationScale ε :=
    Filter.Eventually.of_forall fun ε => by
      dsimp [iterationScale]
      linarith [le_max_left (0 : ℝ)
        (Real.log (4 * gap / (ε : ℝ)) / ((step ε : ℝ) * (μ : ℝ)))]
  have hCosts := onlineDensityScheduledCostCounts_bigO
    A.quantizer hrefresh (by simpa [batch] using hSchedule)
      (expectedDensity_nonneg_of_unbiased hQuantizer) hK hIterationNonneg
  apply onlineParameterizedExecutablePLMeasuredCostComplexity_of_budget
    A x0 xStar step refresh hrefresh batch K Llocal ℒlocal σ ω fStar μ
      hLower hSmooth hVariance hPL hQuantizer hBatch
  · intro ε
    simpa [batch, step] using hAverageSmooth ε
  · exact hStep
  · intro ε
    simpa [K, gap, step, batch] using hBudget ε
  · exact Or.inr hK
  · simpa [batch, K, iterationScale] using hCosts.1
  · simpa [K, iterationScale] using hCosts.2

/-- Supplied-stepsize executable D.3 with measured costs.  The refresh batch
is inflated using `2 σ² / p`, rather than merely `σ²`: this pays for
both the steady-state variance and the sampled-initializer error divided by
`p K`.  Thus the convergence field and both cost integrals describe the same
`onlineProcess` experiment; no cost is transferred from the proof-exact
initializer.  `OnlineCommunicationAELawRegularity` is the law-scoped
well-posedness interface used for the adaptive communication observable. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCommunicationAELawRegularity A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε))
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let iterationScale := fun ε : Accuracy =>
      1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let V : ℝ := varianceAggregateSq σ
  let chosenBatch : Accuracy → Count :=
    onlineNonconvexBatchScheduleFromBase n b0
      (2 * V / A.refreshProbability) baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let iterationScale : Accuracy → ℝ := fun ε =>
    1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
  let K : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (4 * Δ /
      ((A.stepSize : ℝ) * (ε : ℝ) ^ 2))), by omega⟩
  have hV : 0 ≤ V := by
    dsimp [V, varianceAggregateSq, meanSquare, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (hLower x0)
  have hEffectiveVariance : 0 ≤ 2 * V / A.refreshProbability := by
    positivity
  have hBatch : ∀ ε, OnlineBatchAdmissible (chosenBatch ε) b0 := by
    intro ε
    simpa [chosenBatch] using
      onlineNonconvexBatchScheduleFromBase_admissible n b0
        (2 * V / A.refreshProbability) baseBatch ε
  have hFloor (eps : Accuracy) :
      V / (n.1 * (chosenBatch eps).1) ≤
        A.refreshProbability * (eps : ℝ) ^ 2 / 4 := by
    have hEff := onlineNonconvexBatchScheduleFromBase_variance_floor
      n b0 (2 * V / A.refreshProbability) hEffectiveVariance
        baseBatch eps
    have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hb : ((chosenBatch eps).1 : ℝ) ≠ 0 := by
      exact_mod_cast (chosenBatch eps).2.ne'
    have hpne : A.refreshProbability ≠ 0 := ne_of_gt hp
    dsimp [chosenBatch] at hEff ⊢
    rw [div_le_iff₀ (by positivity : 0 < (n.1 : ℝ) *
      (onlineNonconvexBatchScheduleFromBase n b0
        (2 * V / A.refreshProbability) baseBatch eps).1)] at hEff ⊢
    field_simp [hpne, hn, hb] at hEff ⊢
    nlinarith
  have hOptimizationHalf (eps : Accuracy) :
      2 * Δ / ((A.stepSize : ℝ) * (K eps).1) ≤
        (eps : ℝ) ^ 2 / 2 := by
    have hKpos : 0 < ((K eps).1 : ℝ) := by exact_mod_cast (K eps).2
    have hγpos : 0 < (A.stepSize : ℝ) := A.stepSize.property
    have hBudget := div_natCast_max_one_ceil_div_le
      (4 * Δ) ((A.stepSize : ℝ) * (eps : ℝ) ^ 2)
        (mul_pos hγpos (sq_pos_of_pos eps.property))
    have hBudget' :
        4 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ)) ≤
          (eps : ℝ) ^ 2 := by
      rw [div_le_iff₀ (mul_pos hγpos hKpos)]
      have hRaw : 4 * Δ / ((K eps).1 : ℝ) ≤
          (A.stepSize : ℝ) * (eps : ℝ) ^ 2 := by
        simpa [K] using hBudget
      rw [div_le_iff₀ hKpos] at hRaw
      nlinarith
    calc
      2 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ)) =
          (1 / 2 : ℝ) *
            (4 * Δ / ((A.stepSize : ℝ) * ((K eps).1 : ℝ))) := by
              field_simp [ne_of_gt hγpos, ne_of_gt hKpos]
              all_goals ring
      _ ≤ (1 / 2 : ℝ) * (eps : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hBudget' (by norm_num)
      _ = (eps : ℝ) ^ 2 / 2 := by ring
  have hInitialQuarter (eps : Accuracy) :
      (V / (n.1 * (chosenBatch eps).1)) /
          (A.refreshProbability * (K eps).1) ≤
        (eps : ℝ) ^ 2 / 4 := by
    have hKone : (1 : ℝ) ≤ (K eps).1 := by
      exact_mod_cast (K eps).2
    rw [div_le_iff₀ (mul_pos hp (by positivity : 0 < ((K eps).1 : ℝ)))]
    have hFloor' := hFloor eps
    calc
      V / (n.1 * (chosenBatch eps).1) ≤
          A.refreshProbability * (eps : ℝ) ^ 2 / 4 := hFloor'
      _ ≤ (A.refreshProbability * (eps : ℝ) ^ 2 / 4) *
          (K eps).1 :=
        le_mul_of_one_le_right (by positivity) hKone
      _ = (eps : ℝ) ^ 2 / 4 *
          (A.refreshProbability * (K eps).1) := by ring
  have hAccuracy : ∀ eps, NonconvexAccuracy (K eps)
      (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch eps))
      (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) eps := by
    apply onlineExecutableNonconvexAccuracy_family_of_budget
      A x0 chosenBatch K Llocal ℒlocal σ ω fStar hLower hSmooth
        hVariance hQuantizer hBatch
    · intro eps
      simpa [chosenBatch] using hAverageSmooth eps
    · exact hStep
    · intro eps
      have hSteadyQuarter :
          V / (n.1 * (chosenBatch eps).1) ≤ (eps : ℝ) ^ 2 / 4 :=
        (hFloor eps).trans (by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
          exact mul_le_of_le_one_left (sq_nonneg _) hp1)
      calc
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
              ((A.stepSize : ℝ) * (K eps).1) +
            (varianceAggregateSq σ / (n.1 * (chosenBatch eps).1)) /
              (A.refreshProbability * (K eps).1) +
            varianceAggregateSq σ / (n.1 * (chosenBatch eps).1) ≤
            (eps : ℝ) ^ 2 / 2 + (eps : ℝ) ^ 2 / 4 +
              (eps : ℝ) ^ 2 / 4 := by
          simpa [V, Δ] using
            (add_le_add (add_le_add (hOptimizationHalf eps)
              (hInitialQuarter eps)) hSteadyQuarter)
        _ = (eps : ℝ) ^ 2 := by ring
  have hKBound (eps : Accuracy) : ((K eps).1 : ℝ) ≤
      2 * iterationScale eps := by
    let q : ℝ := 4 * Δ / ((A.stepSize : ℝ) * (eps : ℝ) ^ 2)
    have hq : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg A.stepSize.property.le (sq_nonneg _))
    have hceil := natCast_max_one_ceil_le_add_two q hq
    have hscale : iterationScale eps = 1 + q := by
      simp [iterationScale, q]
    rw [show ((K eps).1 : ℝ) =
      ((max 1 (Nat.ceil q) : ℕ) : ℝ) by simp [K, q]]
    rw [hscale]
    linarith
  have hScalePos (eps : Accuracy) : 0 < iterationScale eps := by
    dsimp [iterationScale]
    have : 0 ≤ 4 * Δ /
        ((A.stepSize : ℝ) * (eps : ℝ) ^ 2) := by
      exact div_nonneg (mul_nonneg (by norm_num) hΔ)
        (mul_nonneg A.stepSize.property.le (sq_nonneg _))
    linarith
  have hKBigO : AccuracyBigO (fun eps => ((K eps).1 : ℝ))
      iterationScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro eps
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((K eps).1 : ℝ)), Real.norm_eq_abs,
      abs_of_pos (hScalePos eps)]
    exact hKBound eps
  have hEndpoints : ThreeEndpointComplexity K
      (fun eps => NonconvexAccuracy (K eps)
        (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch eps))
        (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) eps)
      iterationScale
      (fun eps => onlineOracleCallCount (chosenBatch eps) b0 (K eps)
        A.refreshProbability)
      (fun eps => (chosenBatch eps).1 + iterationScale eps *
        (A.refreshProbability * (chosenBatch eps).1 +
          2 * (1 - A.refreshProbability) * b0.1))
      (fun eps => allWorkerCommunicationCount d (K eps)
        A.refreshProbability (expectedDensity A.quantizer))
      (fun eps => d.1 + iterationScale eps *
        (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
    unfold ThreeEndpointComplexity
    refine ⟨hAccuracy, Or.inr hKBigO, ?_, ?_⟩
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * (chosenBatch eps).1 +
        2 * (1 - A.refreshProbability) * b0.1
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            (by positivity))
      have hactual : 0 ≤ onlineOracleCallCount (chosenBatch eps) b0
          (K eps) A.refreshProbability := by
        unfold onlineOracleCallCount
        exact add_nonneg (by positivity)
          (mul_nonneg (by positivity) hpayload)
      have htarget : 0 < (chosenBatch eps).1 +
          iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast (chosenBatch eps).2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (chosenBatch eps).1 + ((K eps).1 : ℝ) * payload ≤
        2 * ((chosenBatch eps).1 + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * expectedDensity A.quantizer
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr hp1)
            (expectedDensity_nonneg_of_unbiased hQuantizer))
      have hactual : 0 ≤ allWorkerCommunicationCount d (K eps)
          A.refreshProbability (expectedDensity A.quantizer) := by
        unfold allWorkerCommunicationCount
        positivity
      have htarget : 0 < (d.1 : ℝ) + iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast d.2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (d.1 : ℝ) + ((K eps).1 : ℝ) * payload ≤
        2 * ((d.1 : ℝ) + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
  refine ⟨K, ?_⟩
  apply onlineExecutableNonconvexMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 chosenBatch hBatch
  · intro eps
    simpa [chosenBatch] using hCostMeas eps
  · exact hQuantizer
  · exact hEndpoints

/-- Compatibility supplied-step D.3 route from strict generated-message
regularity. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCommunicationLawRegularity A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε))
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let iterationScale := fun ε : Accuracy =>
      1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  apply onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
    A x0 baseBatch Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
      hQuantizer hAverageSmooth
  · intro ε
    exact onlineCommunicationAELawRegularity_of_lawRegularity A x0 _
      (hCostMeas ε)
  · exact hStep

/-- Backward-compatible supplied-step D.3 route under the former global
generated-cost measurability contract. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCostMeasurability A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε))
    (hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let iterationScale := fun ε : Accuracy =>
      1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  apply onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_law_regularity
    A x0 baseBatch Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
      hQuantizer hAverageSmooth
  · intro ε
    exact onlineCommunicationLawRegularity_of_costMeasurability A x0 _
      (hCostMeas ε)
  · exact hStep

/-- Canonical Eq. (40) specialization of the executable D.3 measured-cost
family.  The equality premise records the source's canonical choice of the
reciprocal Eq. (40) bracket; unlike the upper-bound-only stepsize condition,
it is strong enough to replace `1 / A.stepSize` by that bracket in the
complexity scale.  The additive `1` is the nonempty-output-window
totalization and also covers the already-solved zero-gap case.

The refresh batch remains the initialization-corrected executable schedule
from the supplied-step theorem.  Thus the convergence statement and the two
cost integrals still concern the same sampled-initializer `onlineProcess`
experiment. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_ae_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCommunicationAELawRegularity A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε))
    (hCanonicalStep :
      (A.stepSize : ℝ) *
        (rootMeanSquare Llocal +
          Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let iterationScale := fun ε : Accuracy =>
      1 + Δ / (ε : ℝ) ^ 2 * bracket
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let chosenBatch : Accuracy → Count :=
    onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((1 - A.refreshProbability) /
      (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let suppliedScale : Accuracy → ℝ := fun ε =>
    1 + 4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
  let canonicalScale : Accuracy → ℝ := fun ε =>
    1 + Δ / (ε : ℝ) ^ 2 * bracket
  have hStep : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0 := by
    unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition
    simpa [bracket] using hCanonicalStep.le
  obtain ⟨K, hMeasured⟩ :=
    onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
      A x0 baseBatch Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
        hQuantizer hAverageSmooth hCostMeas hStep
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (hLower x0)
  have hγ : 0 < (A.stepSize : ℝ) := A.stepSize.property
  have hBracket : 0 < bracket := by
    have hproduct : (A.stepSize : ℝ) * bracket = 1 := by
      simpa [bracket] using hCanonicalStep
    nlinarith
  have hScale : AccuracyBigO suppliedScale canonicalScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨4, Filter.Eventually.of_forall ?_⟩
    intro ε
    have hε : 0 < (ε : ℝ) := ε.property
    have hproduct : (A.stepSize : ℝ) * bracket = 1 := by
      simpa [bracket] using hCanonicalStep
    have hrewrite :
        4 * Δ / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2) =
          4 * (Δ / (ε : ℝ) ^ 2 * bracket) := by
      field_simp [ne_of_gt hγ, ne_of_gt hε]
      nlinarith
    have hterm : 0 ≤ Δ / (ε : ℝ) ^ 2 * bracket := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show 0 < suppliedScale ε by
        dsimp [suppliedScale]
        positivity),
      abs_of_pos (show 0 < canonicalScale ε by
        dsimp [canonicalScale]
        positivity)]
    dsimp [suppliedScale, canonicalScale]
    rw [hrewrite]
    nlinarith
  unfold OnlineExecutableNonconvexMeasuredCostComplexity
    OnlineMeasuredCostComplexity at hMeasured ⊢
  rcases hMeasured with ⟨hAccuracy, hIteration, hCosts⟩
  have hIteration' : AccuracyIterationBigO
      (fun ε => ((K ε).1 : ℝ)) canonicalScale := by
    rcases hIteration with hzero | hbig
    · let ε₁ : Accuracy := ⟨1, by norm_num⟩
      have hpos : 0 < suppliedScale ε₁ := by
        dsimp [suppliedScale]
        positivity
      exact (ne_of_gt hpos (hzero.1 ε₁)).elim
    · exact Or.inr (hbig.trans hScale)
  refine ⟨K, hAccuracy, hIteration', ?_⟩
  intro i
  rcases hCosts i with ⟨hOracleInt, hOracle, hCommInt, hComm⟩
  let oraclePayload : Accuracy → ℝ := fun ε =>
    A.refreshProbability * (chosenBatch ε).1 +
      2 * (1 - A.refreshProbability) * b0.1
  let communicationPayload : Accuracy → ℝ := fun _ =>
    A.refreshProbability * d.1 +
      (1 - A.refreshProbability) * expectedDensity A.quantizer
  have hOracleScale : AccuracyBigO
      (fun ε => (chosenBatch ε).1 + suppliedScale ε * oraclePayload ε)
      (fun ε => (chosenBatch ε).1 + canonicalScale ε * oraclePayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl
      (fun ε : Accuracy => ((chosenBatch ε).1 : ℝ)) accuracyToZero).add_add
        (hScale.mul (Asymptotics.isBigO_refl oraclePayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((chosenBatch ε).1 : ℝ)), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [oraclePayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg
              (mul_nonneg (by norm_num)
                (sub_nonneg.mpr A.refresh_admissible.2)) (by positivity))))]
  have hCommunicationScale : AccuracyBigO
      (fun ε => (d.1 : ℝ) + suppliedScale ε * communicationPayload ε)
      (fun ε => (d.1 : ℝ) + canonicalScale ε * communicationPayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl (fun _ : Accuracy => (d.1 : ℝ))
      accuracyToZero).add_add
        (hScale.mul
          (Asymptotics.isBigO_refl communicationPayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (d.1 : ℝ)),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [communicationPayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg (sub_nonneg.mpr A.refresh_admissible.2)
              (expectedDensity_nonneg_of_unbiased hQuantizer))))]
  refine ⟨hOracleInt, ?_, hCommInt, ?_⟩
  · apply hOracle.trans
    simpa [chosenBatch, suppliedScale, canonicalScale, oraclePayload]
      using hOracleScale
  · apply hComm.trans
    simpa [suppliedScale, canonicalScale, communicationPayload]
      using hCommunicationScale

/-- Source-facing canonical Eq. (40) executable D.3 specialization.  The
law-scoped regularity needed by the actual-message integral is derived from
the source smoothness, variance, quantizer, and average-smoothness hypotheses
rather than exposed as an additional premise. -/
theorem onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            baseBatch ε)) ℒlocal)
    (hCanonicalStep :
      (A.stepSize : ℝ) *
        (rootMeanSquare Llocal +
          Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let chosenBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let iterationScale := fun ε : Accuracy =>
      1 + Δ / (ε : ℝ) ^ 2 * bracket
    ∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 chosenBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  apply onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_ae_law_regularity
    A x0 baseBatch Llocal ℒlocal σ ω fStar hLower hSmooth hVariance
      hQuantizer hAverageSmooth
  · intro ε
    exact onlineCommunicationAELawRegularity_of_source
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer _
        (hAverageSmooth ε)
  · exact hCanonicalStep

/-- Supplied-stepsize executable D.4 with measured costs.  The geometric
horizon allocates one quarter of the target to contraction.  The source
batch schedule allocates one half to the stationary variance floor, while
`2 γ μ ≤ p` makes the sampled-initializer contribution at most the
remaining quarter.  Consequently the accuracy field, oracle integral, and
communication integral all refer to the same sampled-initializer
`onlineProcess` experiment. -/
theorem onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCommunicationAELawRegularity A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let iterationScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δ / (ε : ℝ)) /
        ((A.stepSize : ℝ) * (μ : ℝ)))
    ∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar chosenBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let V : ℝ := varianceAggregateSq σ
  let chosenBatch : Accuracy → Count :=
    onlinePLBatchScheduleFromBase n b0 V μ baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 -
    globalObjective (onlineLocalProblem A.problem) xStar
  let c : ℝ := (A.stepSize : ℝ) * (μ : ℝ)
  let contractionScale : Accuracy → ℝ := fun ε =>
    max 0 (Real.log (4 * Δ / (ε : ℝ)) / c)
  let iterationScale : Accuracy → ℝ := fun ε => 1 + contractionScale ε
  let K : Accuracy → Count := fun ε =>
    ⟨max 1 (Nat.ceil (contractionScale ε)), by omega⟩
  have hV : 0 ≤ V := by
    dsimp [V, varianceAggregateSq, meanSquare, average,
      SOptLib.finiteUniformAverage]
    positivity
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (hPL.1 x0)
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos A.stepSize.property μ.property
  have hc1 : c ≤ 1 := by
    dsimp [c]
    nlinarith [hStep.2, hp1]
  have hBatch : ∀ ε, OnlineBatchAdmissible (chosenBatch ε) b0 := by
    intro ε
    simpa [chosenBatch] using
      onlinePLBatchScheduleFromBase_admissible n b0 V μ baseBatch ε
  have hFloor (eps : Accuracy) :
      V / (n.1 * (chosenBatch eps).1 * μ) ≤ (eps : ℝ) / 2 := by
    simpa [chosenBatch] using
      onlinePLBatchScheduleFromBase_variance_floor n b0 V μ hV
        μ.property baseBatch eps
  have hContractQuarter (eps : Accuracy) :
      (1 - c) ^ (K eps).1 * Δ ≤ (eps : ℝ) / 4 := by
    rcases hΔ.eq_or_lt with hΔzero | hΔpos
    · calc
        (1 - c) ^ (K eps).1 * Δ = 0 := by rw [← hΔzero]; ring
        _ ≤ (eps : ℝ) / 4 := div_nonneg eps.property.le (by norm_num)
    · by_cases hsmall : (eps : ℝ) < 4 * Δ
      · have hratio : 1 < 4 * Δ / (eps : ℝ) :=
          (one_lt_div eps.property).2 hsmall
        have hlogPos : 0 < Real.log (4 * Δ / (eps : ℝ)) :=
          Real.log_pos hratio
        have hraw : 0 ≤ Real.log (4 * Δ / (eps : ℝ)) / c :=
          div_nonneg hlogPos.le hc.le
        have hScalar := positive_geometric_ceiling_schedule
          (4 * Δ) c 1 (mul_pos (by norm_num) hΔpos) hc hc1
            (by norm_num)
        have hFour :
            (1 - c) ^ (K eps).1 * (4 * Δ) ≤ (eps : ℝ) := by
          simpa [K, contractionScale, max_eq_right hraw] using hScalar.1 eps
        nlinarith [pow_nonneg (sub_nonneg.mpr hc1) (K eps).1]
      · have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
        have hbaseOne : 1 - c ≤ 1 := by linarith [hc]
        calc
          (1 - c) ^ (K eps).1 * Δ ≤ 1 * Δ :=
            mul_le_mul_of_nonneg_right
              (pow_le_one₀ hbase hbaseOne) hΔ
          _ = Δ := one_mul Δ
          _ ≤ (eps : ℝ) / 4 := by linarith
  have hInitialQuarter (eps : Accuracy) :
      (1 - c) ^ (K eps).1 * (A.stepSize : ℝ) /
          A.refreshProbability * (V / (n.1 * (chosenBatch eps).1)) ≤
        (eps : ℝ) / 4 := by
    have hbase : 0 ≤ 1 - c := sub_nonneg.mpr hc1
    have hbaseOne : 1 - c ≤ 1 := by linarith [hc]
    have hpow : (1 - c) ^ (K eps).1 ≤ 1 :=
      pow_le_one₀ hbase hbaseOne
    have hratio : (A.stepSize : ℝ) * (μ : ℝ) /
        A.refreshProbability ≤ 1 / 2 := by
      rw [div_le_iff₀ hp]
      nlinarith [hStep.2]
    have hFloorNonneg : 0 ≤ V / (n.1 * (chosenBatch eps).1 * μ) := by
      exact div_nonneg hV (mul_nonneg
        (mul_nonneg (by positivity) (by positivity)) μ.property.le)
    calc
      (1 - c) ^ (K eps).1 * (A.stepSize : ℝ) /
            A.refreshProbability * (V / (n.1 * (chosenBatch eps).1)) =
          ((1 - c) ^ (K eps).1 *
            ((A.stepSize : ℝ) * (μ : ℝ) /
              A.refreshProbability)) *
            (V / (n.1 * (chosenBatch eps).1 * μ)) := by
              field_simp [ne_of_gt hp, ne_of_gt μ.property]
      _ ≤ (1 * (1 / 2 : ℝ)) *
            (V / (n.1 * (chosenBatch eps).1 * μ)) := by
          gcongr
      _ ≤ (eps : ℝ) / 4 := by
          nlinarith [hFloor eps]
  have hAccuracy : ∀ eps, PLAccuracy (K eps)
      (onlineLocalProblem A.problem)
      (onlineProcess A x0 (hBatch eps))
      (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) xStar eps := by
    apply onlineExecutablePLAccuracy_family_of_budget
      A x0 xStar chosenBatch K Llocal ℒlocal σ ω fStar μ hLower
        hSmooth hVariance hPL hQuantizer hBatch
    · intro eps
      simpa [chosenBatch] using hAverageSmooth eps
    · exact hStep
    · intro eps
      calc
        (1 - A.stepSize * μ) ^ (K eps).1 *
              (globalObjective (onlineLocalProblem A.problem) x0 -
                globalObjective (onlineLocalProblem A.problem) xStar) +
            (1 - A.stepSize * μ) ^ (K eps).1 * A.stepSize /
              A.refreshProbability *
                (varianceAggregateSq σ /
                  (n.1 * (chosenBatch eps).1)) +
            varianceAggregateSq σ /
              (n.1 * (chosenBatch eps).1 * μ) ≤
            (eps : ℝ) / 4 + (eps : ℝ) / 4 + (eps : ℝ) / 2 := by
          simpa [V, Δ, c] using
            (add_le_add (add_le_add (hContractQuarter eps)
              (hInitialQuarter eps)) (hFloor eps))
        _ = (eps : ℝ) := by ring
  have hKBound (eps : Accuracy) : ((K eps).1 : ℝ) ≤
      2 * iterationScale eps := by
    have hq : 0 ≤ contractionScale eps := by
      dsimp [contractionScale]
      exact le_max_left _ _
    have hceil := natCast_max_one_ceil_le_add_two
      (contractionScale eps) hq
    change ((max 1 (Nat.ceil (contractionScale eps)) : ℕ) : ℝ) ≤
      2 * (1 + contractionScale eps)
    linarith
  have hScalePos (eps : Accuracy) : 0 < iterationScale eps := by
    dsimp [iterationScale]
    linarith [show 0 ≤ contractionScale eps by
      dsimp [contractionScale]
      exact le_max_left _ _]
  have hKBigO : AccuracyBigO (fun eps => ((K eps).1 : ℝ))
      iterationScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro eps
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((K eps).1 : ℝ)), Real.norm_eq_abs,
      abs_of_pos (hScalePos eps)]
    exact hKBound eps
  have hEndpoints : ThreeEndpointComplexity K
      (fun eps => PLAccuracy (K eps)
        (onlineLocalProblem A.problem)
        (onlineProcess A x0 (hBatch eps))
        (onlinePathLaw (b := chosenBatch eps) (b0 := b0) A) xStar eps)
      iterationScale
      (fun eps => onlineOracleCallCount (chosenBatch eps) b0 (K eps)
        A.refreshProbability)
      (fun eps => (chosenBatch eps).1 + iterationScale eps *
        (A.refreshProbability * (chosenBatch eps).1 +
          2 * (1 - A.refreshProbability) * b0.1))
      (fun eps => allWorkerCommunicationCount d (K eps)
        A.refreshProbability (expectedDensity A.quantizer))
      (fun eps => d.1 + iterationScale eps *
        (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
    unfold ThreeEndpointComplexity
    refine ⟨hAccuracy, Or.inr hKBigO, ?_, ?_⟩
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * (chosenBatch eps).1 +
        2 * (1 - A.refreshProbability) * b0.1
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
            (by positivity))
      have hactual : 0 ≤ onlineOracleCallCount (chosenBatch eps) b0
          (K eps) A.refreshProbability := by
        unfold onlineOracleCallCount
        exact add_nonneg (by positivity)
          (mul_nonneg (by positivity) hpayload)
      have htarget : 0 < (chosenBatch eps).1 +
          iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast (chosenBatch eps).2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (chosenBatch eps).1 + ((K eps).1 : ℝ) * payload ≤
        2 * ((chosenBatch eps).1 + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
    · unfold AccuracyBigO
      rw [Asymptotics.isBigO_iff]
      refine ⟨2, Filter.Eventually.of_forall ?_⟩
      intro eps
      let payload : ℝ := A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * expectedDensity A.quantizer
      have hpayload : 0 ≤ payload := by
        dsimp [payload]
        exact add_nonneg (mul_nonneg hp.le (by positivity))
          (mul_nonneg (sub_nonneg.mpr hp1)
            (expectedDensity_nonneg_of_unbiased hQuantizer))
      have hactual : 0 ≤ allWorkerCommunicationCount d (K eps)
          A.refreshProbability (expectedDensity A.quantizer) := by
        unfold allWorkerCommunicationCount
        positivity
      have htarget : 0 < (d.1 : ℝ) + iterationScale eps * payload := by
        exact add_pos_of_pos_of_nonneg (by exact_mod_cast d.2)
          (mul_nonneg (hScalePos eps).le hpayload)
      rw [Real.norm_eq_abs, abs_of_nonneg hactual,
        Real.norm_eq_abs, abs_of_pos htarget]
      change (d.1 : ℝ) + ((K eps).1 : ℝ) * payload ≤
        2 * ((d.1 : ℝ) + iterationScale eps * payload)
      have := mul_le_mul_of_nonneg_right (hKBound eps) hpayload
      nlinarith
  refine ⟨K, ?_⟩
  apply onlineExecutablePLMeasuredCostComplexity_of_threeEndpoint_of_ae_law_regularity
    A x0 xStar chosenBatch hBatch
  · intro eps
    simpa [chosenBatch] using hCostMeas eps
  · exact hQuantizer
  · exact hEndpoints

/-- Compatibility supplied-step D.4 route from strict generated-message
regularity. -/
theorem onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCommunicationLawRegularity A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let iterationScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δ / (ε : ℝ)) /
        ((A.stepSize : ℝ) * (μ : ℝ)))
    ∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar chosenBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  apply onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
    A x0 xStar baseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hVariance hPL hQuantizer hAverageSmooth
  · intro ε
    exact onlineCommunicationAELawRegularity_of_lawRegularity A x0 _
      (hCostMeas ε)
  · exact hStep

/-- Backward-compatible supplied-step D.4 route under the former global
generated-cost measurability contract. -/
theorem onlineExecutablePLMeasuredCostComplexity_supplied_stepsize
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCostMeasurability A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
    (hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let iterationScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δ / (ε : ℝ)) /
        ((A.stepSize : ℝ) * (μ : ℝ)))
    ∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar chosenBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  apply onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_law_regularity
    A x0 xStar baseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hVariance hPL hQuantizer hAverageSmooth
  · intro ε
    exact onlineCommunicationLawRegularity_of_costMeasurability A x0 _
      (hCostMeas ε)
  · exact hStep

/-- Canonical Eq. (48) specialization of the executable D.4 measured-cost
family.  The canonical denominator simultaneously enforces the doubled
smoothness bracket and `2 γ μ ≤ p`.  Consequently the supplied reciprocal
stepsize scale is controlled by the source factor
`max (1 / p) (bracket / μ)`.  The `max 0` logarithm and additive `1` are the
totalized finite-horizon form of the printed geometric rate. -/
theorem onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_ae_law_regularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hCostMeas : ∀ ε,
      OnlineCommunicationAELawRegularity A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
    (hCanonicalStep :
      (A.stepSize : ℝ) * max (2 * (μ : ℝ) / A.refreshProbability)
        (rootMeanSquare Llocal +
          Real.sqrt ((2 * (1 - A.refreshProbability)) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((2 * (1 - A.refreshProbability)) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let factor := max (1 / A.refreshProbability) (bracket / (μ : ℝ))
    let iterationScale := fun ε : Accuracy =>
      1 + factor * max 0 (Real.log (4 * Δ / (ε : ℝ)))
    ∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar chosenBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  dsimp
  let chosenBatch : Accuracy → Count :=
    onlinePLBatchScheduleFromBase n b0 (varianceAggregateSq σ) μ baseBatch
  let Δ : ℝ := globalObjective (onlineLocalProblem A.problem) x0 -
    globalObjective (onlineLocalProblem A.problem) xStar
  let bracket : ℝ := rootMeanSquare Llocal +
    Real.sqrt ((2 * (1 - A.refreshProbability)) /
      (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let denominator : ℝ :=
    max (2 * (μ : ℝ) / A.refreshProbability) bracket
  let factor : ℝ := max (1 / A.refreshProbability) (bracket / (μ : ℝ))
  let suppliedScale : Accuracy → ℝ := fun ε =>
    1 + max 0 (Real.log (4 * Δ / (ε : ℝ)) /
      ((A.stepSize : ℝ) * (μ : ℝ)))
  let canonicalScale : Accuracy → ℝ := fun ε =>
    1 + factor * max 0 (Real.log (4 * Δ / (ε : ℝ)))
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hγ : 0 < (A.stepSize : ℝ) := A.stepSize.property
  have hμ : 0 < (μ : ℝ) := μ.property
  have hDenominator : 0 < denominator := by
    dsimp [denominator]
    exact (div_pos (mul_pos (by norm_num) hμ) hp).trans_le (le_max_left _ _)
  have hCanonical : (A.stepSize : ℝ) * denominator = 1 := by
    simpa [denominator, bracket] using hCanonicalStep
  have hFactor : 0 < factor := by
    dsimp [factor]
    exact (div_pos zero_lt_one hp).trans_le (le_max_left _ _)
  have hStep : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0 := by
    unfold OnlineVRPLStepsizeCondition FiniteSumVRPLStepsizeCondition
    constructor
    · have hle : bracket ≤ denominator := by
        exact le_max_right _ _
      have hmul := mul_le_mul_of_nonneg_left hle hγ.le
      simpa [bracket] using hmul.trans_eq hCanonical
    · rw [← div_le_one hp]
      calc
        2 * (A.stepSize : ℝ) * (μ : ℝ) / A.refreshProbability =
            (A.stepSize : ℝ) *
              (2 * (μ : ℝ) / A.refreshProbability) := by ring
        _ ≤ (A.stepSize : ℝ) * denominator :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hγ.le
        _ = 1 := hCanonical
  obtain ⟨K, hMeasured⟩ :=
    onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
      A x0 xStar baseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
        hVariance hPL hQuantizer hAverageSmooth hCostMeas hStep
  have hDenominatorFactor : denominator / (μ : ℝ) ≤ 2 * factor := by
    dsimp [denominator]
    rw [← max_div_div_right hμ.le]
    apply max_le
    · have heq : (2 * (μ : ℝ) / A.refreshProbability) /
          (μ : ℝ) = 2 * (1 / A.refreshProbability) := by
        field_simp [ne_of_gt hp, ne_of_gt hμ]
      rw [heq]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    · have hle : bracket / (μ : ℝ) ≤ factor := le_max_right _ _
      nlinarith [hFactor]
  have hScale : AccuracyBigO suppliedScale canonicalScale := by
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, Filter.Eventually.of_forall ?_⟩
    intro ε
    let q : ℝ := Real.log (4 * Δ / (ε : ℝ))
    have hInv : 1 / (A.stepSize : ℝ) = denominator := by
      rw [div_eq_iff (ne_of_gt hγ)]
      simpa [mul_comm] using hCanonical.symm
    have hquotient : q / ((A.stepSize : ℝ) * (μ : ℝ)) =
        q * (denominator / (μ : ℝ)) := by
      calc
        q / ((A.stepSize : ℝ) * (μ : ℝ)) =
            q * (1 / (A.stepSize : ℝ)) / (μ : ℝ) := by
              field_simp [ne_of_gt hγ, ne_of_gt hμ]
        _ = q * denominator / (μ : ℝ) := by rw [hInv]
        _ = q * (denominator / (μ : ℝ)) := by ring
    have hround : max 0 (q / ((A.stepSize : ℝ) * (μ : ℝ))) ≤
        2 * factor * max 0 q := by
      rw [hquotient]
      by_cases hq : q ≤ 0
      · have hleft : q * (denominator / (μ : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hq
            (div_nonneg hDenominator.le hμ.le)
        rw [max_eq_left hleft, max_eq_left hq]
        positivity
      · have hqpos : 0 < q := lt_of_not_ge hq
        rw [max_eq_right (mul_nonneg hqpos.le
          (div_nonneg hDenominator.le hμ.le)), max_eq_right hqpos.le]
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_of_nonneg_left hDenominatorFactor hqpos.le)
    have hsourcePos : 0 < suppliedScale ε := by
      dsimp [suppliedScale]
      positivity
    have htargetPos : 0 < canonicalScale ε := by
      dsimp [canonicalScale]
      positivity
    rw [Real.norm_eq_abs, abs_of_pos hsourcePos,
      Real.norm_eq_abs, abs_of_pos htargetPos]
    dsimp [suppliedScale, canonicalScale]
    change 1 + max 0 (q / ((A.stepSize : ℝ) * (μ : ℝ))) ≤
      2 * (1 + factor * max 0 q)
    nlinarith [mul_nonneg hFactor.le (le_max_left 0 q)]
  unfold OnlineExecutablePLMeasuredCostComplexity OnlineMeasuredCostComplexity
    at hMeasured ⊢
  rcases hMeasured with ⟨hAccuracy, hIteration, hCosts⟩
  have hIteration' : AccuracyIterationBigO
      (fun ε => ((K ε).1 : ℝ)) canonicalScale := by
    rcases hIteration with hzero | hbig
    · let ε₁ : Accuracy := ⟨1, by norm_num⟩
      have hpos : 0 < suppliedScale ε₁ := by
        dsimp [suppliedScale]
        positivity
      exact (ne_of_gt hpos (hzero.1 ε₁)).elim
    · exact Or.inr (hbig.trans hScale)
  refine ⟨K, hAccuracy, hIteration', ?_⟩
  intro i
  rcases hCosts i with ⟨hOracleInt, hOracle, hCommInt, hComm⟩
  let oraclePayload : Accuracy → ℝ := fun ε =>
    A.refreshProbability * (chosenBatch ε).1 +
      2 * (1 - A.refreshProbability) * b0.1
  let communicationPayload : Accuracy → ℝ := fun _ =>
    A.refreshProbability * d.1 +
      (1 - A.refreshProbability) * expectedDensity A.quantizer
  have hOracleScale : AccuracyBigO
      (fun ε => (chosenBatch ε).1 + suppliedScale ε * oraclePayload ε)
      (fun ε => (chosenBatch ε).1 + canonicalScale ε * oraclePayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl
      (fun ε : Accuracy => ((chosenBatch ε).1 : ℝ)) accuracyToZero).add_add
        (hScale.mul (Asymptotics.isBigO_refl oraclePayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ((chosenBatch ε).1 : ℝ)), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [oraclePayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg
              (mul_nonneg (by norm_num)
                (sub_nonneg.mpr A.refresh_admissible.2)) (by positivity))))]
  have hCommunicationScale : AccuracyBigO
      (fun ε => (d.1 : ℝ) + suppliedScale ε * communicationPayload ε)
      (fun ε => (d.1 : ℝ) + canonicalScale ε * communicationPayload ε) := by
    unfold AccuracyBigO at hScale ⊢
    have hraw := (Asymptotics.isBigO_refl (fun _ : Accuracy => (d.1 : ℝ))
      accuracyToZero).add_add
        (hScale.mul
          (Asymptotics.isBigO_refl communicationPayload accuracyToZero))
    convert hraw using 1
    funext ε
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (d.1 : ℝ)),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by
        dsimp [canonicalScale]
        positivity) (by
          dsimp [communicationPayload]
          exact add_nonneg
            (mul_nonneg A.refresh_admissible.1.le (by positivity))
            (mul_nonneg (sub_nonneg.mpr A.refresh_admissible.2)
              (expectedDensity_nonneg_of_unbiased hQuantizer))))]
  refine ⟨hOracleInt, ?_, hCommInt, ?_⟩
  · apply hOracle.trans
    simpa [chosenBatch, suppliedScale, canonicalScale, oraclePayload,
      Δ, bracket, factor]
      using hOracleScale
  · apply hComm.trans
    simpa [suppliedScale, canonicalScale, communicationPayload,
      Δ, bracket, factor]
      using hCommunicationScale

/-- Source-facing canonical Eq. (48) executable D.4 specialization. -/
theorem onlineExecutablePLMeasuredCostComplexity_canonical_stepsize
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmooth : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ baseBatch ε)) ℒlocal)
    (hCanonicalStep :
      (A.stepSize : ℝ) * max (2 * (μ : ℝ) / A.refreshProbability)
        (rootMeanSquare Llocal +
          Real.sqrt ((2 * (1 - A.refreshProbability)) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let chosenBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ baseBatch
    let Δ := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let bracket := rootMeanSquare Llocal +
      Real.sqrt ((2 * (1 - A.refreshProbability)) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let factor := max (1 / A.refreshProbability) (bracket / (μ : ℝ))
    let iterationScale := fun ε : Accuracy =>
      1 + factor * max 0 (Real.log (4 * Δ / (ε : ℝ)))
    ∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar chosenBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        K iterationScale
        (fun ε => (chosenBatch ε).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer)) := by
  apply onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_ae_law_regularity
    A x0 xStar baseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
      hVariance hPL hQuantizer hAverageSmooth
  · intro ε
    exact onlineCommunicationAELawRegularity_of_source
      A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer _
        (hAverageSmooth ε)
  · exact hCanonicalStep

/-- Public measured-cost root for the executable, sampled-initializer forms of
Theorems D.3 and D.4.  Both conjuncts account on the full `onlinePathLaw` used
by their convergence statement.  In particular, the oracle integral charges
the sampled refresh batch at initialization; it is not attached to either
exact-gradient proof process.

The source only imposes an upper bound on a supplied stepsize.  Therefore the
sound supplied-step rate below retains the reciprocal of the actual
`A.stepSize`; the source-scale canonical-step corollary is a separate
specialization and must not be obtained by weakening that dependence.  The
law-scoped communication regularity is derived above from the same source
moment assumptions and canonical fresh-coordinate product laws. -/
theorem Theorem_D3_D4_measured_cost_complexity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (x0 xStar : Point d)
    (nonconvexBaseBatch plBaseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAverageSmoothNonconvex : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)) ℒlocal)
    (hAverageSmoothPL : ∀ ε,
      OnlineAverageSmoothness (b0 := b0) A.problem
        (onlineProcess A x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ plBaseBatch ε)) ℒlocal)
    (hStepNonconvex : OnlineVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0)
    (hStepPL : OnlineVRPLStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0) :
    let nonconvexBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) nonconvexBaseBatch
    let plBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ plBaseBatch
    let Δnc := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let Δpl := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let nonconvexIterationScale := fun ε : Accuracy =>
      1 + 4 * Δnc / ((A.stepSize : ℝ) * (ε : ℝ) ^ 2)
    let plIterationScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δpl / (ε : ℝ)) /
        ((A.stepSize : ℝ) * (μ : ℝ)))
    (∃ K : Accuracy → Count,
      OnlineExecutableNonconvexMeasuredCostComplexity A x0 nonconvexBatch
        (fun ε => onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          nonconvexBaseBatch ε)
        K nonconvexIterationScale
        (fun ε => (nonconvexBatch ε).1 + nonconvexIterationScale ε *
          (A.refreshProbability * (nonconvexBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + nonconvexIterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) ∧
    (∃ K : Accuracy → Count,
      OnlineExecutablePLMeasuredCostComplexity A x0 xStar plBatch
        (fun ε => onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ plBaseBatch ε)
        K plIterationScale
        (fun ε => (plBatch ε).1 + plIterationScale ε *
          (A.refreshProbability * (plBatch ε).1 +
            2 * (1 - A.refreshProbability) * b0.1))
        (fun ε => d.1 + plIterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer))) := by
  dsimp
  constructor
  · apply onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
      A x0 nonconvexBaseBatch Llocal ℒlocal σ ω fStar hLower hSmooth
        hVariance hQuantizer hAverageSmoothNonconvex
    · intro ε
      exact onlineCommunicationAELawRegularity_of_source
        A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer _
          (hAverageSmoothNonconvex ε)
    · exact hStepNonconvex
  · apply onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_ae_law_regularity
      A x0 xStar plBaseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
        hVariance hPL hQuantizer hAverageSmoothPL
    · intro ε
      exact onlineCommunicationAELawRegularity_of_source
        A x0 Llocal ℒlocal σ ω hSmooth hVariance hQuantizer _
          (hAverageSmoothPL ε)
    · exact hStepPL

end MARINA
