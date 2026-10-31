import Algorithms.Unverified.MARINA.Part003
import Algorithms.Unverified.MARINA.Part004.Part002
import Algorithms.Unverified.MARINA.Part004.Part003.Part003

-- Aggregator for `Algorithms.Unverified.MARINA`. Source declarations live under `MARINA/`.

namespace MARINA

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-! ## Literal online moment boundary

Assumption 3.3 states only the workerwise fixed-query unbiasedness and
bounded-variance equations.  Adaptive-query regularity used by the generated
Algorithm 3 proofs is kept separate below. -/

/-- Accuracy-family form of executable D.4 under the generated kernel. -/
theorem onlineExecutablePLAccuracy_family_of_budget_of_literal_and_generatedKernel
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (b K : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBatch : ∀ ε, OnlineBatchAdmissible (b ε) b0)
    (hKernel : ∀ ε, OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem (onlineProcess A x0 (hBatch ε))
      (onlinePathLaw (b := b ε) (b0 := b0) A) ℒlocal)
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
  exact onlineExecutablePLAccuracy_of_budget_of_literal_and_generatedKernel
    A x0 xStar Llocal ℒlocal σ ω fStar μ hLower hSmooth hLiteral hPL
      hQuantizer (hBatch ε) (hKernel ε) hStep ε (hBudget ε)

set_option maxHeartbeats 3000000 in
/-- The source generated conditional kernel makes one worker's exact
nonrefresh message jointly measurable on the sampled initializer, strict
round prefix, and fresh difference-minibatch product law.  This is the
workerwise prefix form needed by the actual communication observable; it
uses neither all-query sampled-gradient regularity nor a cost-measurability
witness. -/
theorem
    onlineExecutablePrefix_workerDifferenceMessage_product_aestronglyMeasurable_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒlocal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ)
    (k : ℕ) (i : Worker n) :
    let initialLaw := onlineBatchLaw A.problem b
    let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := initialLaw.prod
      (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
    let differenceBatchLaw := onlineBatchLaw A.problem b0
    let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
    AEStronglyMeasurable
      (fun p :
          (((w : Worker n) → Fin b.1 → Sample w) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b0.1 → Sample w) ↦
        onlineBatchDifference A.problem p.2 i
          (primalStep A.stepSize (prefixState p.1))
          (prefixState p.1).x)
      (prefixLaw.prod differenceBatchLaw) := by
  classical
  dsimp only
  let initialLaw := onlineBatchLaw A.problem b
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let run := onlineProcess (b := b) (b0 := b0) A x0 hBatch
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hfull : AEStronglyMeasurable
      (fun p :
          ((((w : Worker n) → Fin b.1 → Sample w) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) ↦
        onlineBatchDifference A.problem p.2 i
          (run (k + 1) p.1).x (run k p.1).x)
      (law.prod differenceBatchLaw) := by
    simpa [run, law, initialLaw, streamLaw, differenceBatchLaw,
      onlinePathLaw] using
      onlineAssumption32GeneratedConditionalKernel_batchDifference_joint_aestronglyMeasurable
        hKernel k i
  have hreorder : MeasurePreserving
      (fun p :
          ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod differenceBatchLaw).prod streamLaw)
      ((initialLaw.prod streamLaw).prod differenceBatchLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw differenceBatchLaw streamLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := differenceBatchLaw) (ν := streamLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw streamLaw differenceBatchLaw).symm
    simpa [Function.comp_def] using h3.comp (h2.comp h1)
  have hstream : AEStronglyMeasurable
      (fun p :
          ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        onlineBatchDifference A.problem p.1.2 i
          (run (k + 1) (p.1.1, p.2)).x
          (run k (p.1.1, p.2)).x)
      ((initialLaw.prod differenceBatchLaw).prod streamLaw) := by
    simpa [Function.comp_def] using hfull.comp_measurePreserving hreorder
  let F := fun p :
      (((w : Worker n) → Fin b.1 → Sample w) ×
          ((w : Worker n) → Fin b0.1 → Sample w)) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ↦
    onlineBatchDifference A.problem p.1.2 i
      (primalStep A.stepSize (prefixState (p.1.1, p.2)))
      (prefixState (p.1.1, p.2)).x
  have hstatePrefix : ∀ initial stream,
      prefixState (initial, fun j : Fin k ↦ stream j.1) =
        run k (initial, stream) := by
    intro initial stream
    dsimp [prefixState, run]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k initial
      (path := stream)
      (path' := onlineExtendRoundPrefix fallback
        (fun j : Fin k ↦ stream j.1))
      (by intro t ht; simp [onlineExtendRoundPrefix, ht])).symm
  have hstreamF : AEStronglyMeasurable
      (fun p :
          ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) ↦
        F (p.1, fun j : Fin k ↦ p.2 j.1))
      ((initialLaw.prod differenceBatchLaw).prod streamLaw) := by
    refine hstream.congr (Filter.Eventually.of_forall ?_)
    intro p
    dsimp [F]
    rw [hstatePrefix p.1.1 p.2]
    rfl
  have hfinite : AEStronglyMeasurable F
      ((initialLaw.prod differenceBatchLaw).prod prefixStreamLaw) := by
    simpa [prefixStreamLaw] using
      aestronglyMeasurable_initial_prefix_of_comp_general
        (initialLaw.prod differenceBatchLaw) roundLaw k F hstreamF
  have hreorderFinite : MeasurePreserving
      (fun p :
          ((((w : Worker n) → Fin b.1 → Sample w) ×
              (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod prefixStreamLaw).prod differenceBatchLaw)
      ((initialLaw.prod differenceBatchLaw).prod prefixStreamLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw prefixStreamLaw
      differenceBatchLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixStreamLaw) (ν := differenceBatchLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw differenceBatchLaw
        prefixStreamLaw).symm
    simpa [Function.comp_def] using h3.comp (h2.comp h1)
  have hresult := hfinite.comp_measurePreserving hreorderFinite
  simpa [F, prefixLaw, prefixStreamLaw, prefixState, initialLaw, roundLaw,
    differenceBatchLaw, Function.comp_def] using hresult

set_option maxHeartbeats 3000000 in
/-- The source generated conditional kernel makes the actual executable
worker difference message a.e. strongly measurable on `onlinePathLaw`.
The proof transports the strict-prefix/fresh-batch product statement through
the canonical iid path coordinates; it assumes neither all-query sampled
gradient regularity nor a cost-integrability witness. -/
theorem
    onlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒlocal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (onlineWorkerDifferenceMessage A x0 hBatch k i)
      (onlinePathLaw (b := b) (b0 := b0) A) := by
  classical
  let initialLaw := onlineBatchLaw A.problem b
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let prefixMap := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (path.1, onlineRoundPrefix k path.2)
  let current := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    path.2 k
  let batch := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (current path).2.1.2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw onlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  have hbatch : Measurable batch := by
    dsimp [batch, current]
    fun_prop
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixMap, prefixLaw, prefixStreamLaw, law, onlineRoundPrefix]
      using hm.symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
          (Measure.map Prod.snd law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact measurable_pi_apply k
            · exact measurable_snd
      _ = Measure.map
          (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
          streamLaw := by
            rw [show Measure.map Prod.snd law = streamLaw by
              dsimp [law]
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := by
        simpa [streamLaw] using SOptLib.iidStreamLaw_map_eval roundLaw k
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · let streamJoint := fun stream :
          ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
          ((fun j : Fin k ↦ stream j.1), stream k)
      have hstreamJoint : MeasurePreserving streamJoint streamLaw
          (prefixStreamLaw.prod roundLaw) := by
        refine ⟨(by
          dsimp [streamJoint]
          exact (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).prodMk
            (measurable_pi_apply k)), ?_⟩
        have hj := infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ roundLaw) k
        have hprefixStream : Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
              fun j : Fin k ↦ stream j.1) streamLaw = prefixStreamLaw := by
          simpa [streamLaw, prefixStreamLaw] using
            iidStream_prefix_map_eq_infinitePi roundLaw k
        have hprefixRaw : Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
              fun j : Fin k ↦ stream j.1)
            (Measure.infinitePi (fun _ : ℕ ↦ roundLaw)) =
              prefixStreamLaw := by
          simpa [streamLaw] using hprefixStream
        rw [hprefixRaw] at hj
        simpa [streamJoint, streamLaw, prefixStreamLaw] using hj
      have h0 := (MeasurePreserving.id initialLaw).prod hstreamJoint
      have h1 :=
        (measurePreserving_prodAssoc initialLaw prefixStreamLaw roundLaw).symm
      have h := h1.comp h0
      simpa [law, prefixLaw, prefixStreamLaw, prefixMap, current,
        onlineRoundPrefix, streamJoint, Function.comp_def] using h.map_eq
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law := by
    have h := hpastCurrent.comp measurable_id
      (show Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.2) by fun_prop)
    simpa [batch, current, Function.comp_def] using h
  have hbatchLaw : Measure.map batch law = differenceBatchLaw := by
    calc
      Measure.map batch law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.2)
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.2)
          roundLaw := by rw [hcurrentLaw]
      _ = differenceBatchLaw := by
        simpa [roundLaw, differenceBatchLaw] using
          onlineRoundLaw_differenceBatch_marginal (b := b) A
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  let F := fun (pref :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (fresh : (w : Worker n) → Fin b0.1 → Sample w) ↦
    onlineBatchDifference A.problem fresh i
      (primalStep A.stepSize (prefixState pref)) (prefixState pref).x
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod differenceBatchLaw) := by
    simpa [F, prefixState, prefixLaw, prefixStreamLaw, initialLaw, roundLaw,
      differenceBatchLaw] using
      onlineExecutablePrefix_workerDifferenceMessage_product_aestronglyMeasurable_of_generatedKernel
        A x0 hBatch ℒlocal hKernel fallback k i
  have hFmap : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.map prefixMap law).prod (Measure.map batch law)) := by
    rw [hprefixLaw, hbatchLaw]
    exact hF
  have hcomp := aestronglyMeasurable_comp_of_indep_product_law
    hprefix.aemeasurable hbatch.aemeasurable
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map batch law))
      hprefixBatch hFmap
  have hstatePrefix : ∀ path, prefixState (prefixMap path) =
      onlineProcess (b := b) (b0 := b0) A x0 hBatch k path := by
    intro path
    dsimp [prefixState, prefixMap]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  refine hcomp.congr (Filter.Eventually.of_forall ?_)
  intro path
  dsimp [Function.uncurry, F, batch, current,
    onlineWorkerDifferenceMessage]
  rw [hstatePrefix path]

set_option maxHeartbeats 3000000 in
/-- The canonical measurable representative supplied by the generated
Assumption 3.2 kernel is independent of the same-round compressor sample, and
its compressed support is independent of the same-round refresh coin.  These
are coordinate-product consequences of `onlinePathLaw`; no all-query
sample-gradient regularity or cost-integrability premise is used. -/
theorem
    onlineWorkerMessageRepresentative_independences_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒlocal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (k : ℕ) (i : Worker n) :
    let hm := onlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
      A x0 hBatch ℒlocal hKernel k i
    ProbabilityTheory.IndepFun
        (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i))
        (onlineWorkerCompressionSample k i) (onlinePathLaw A) ∧
      ProbabilityTheory.IndepFun
        (fun path ↦ quantizerNonzeroCount A.quantizer
          (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
          (onlineWorkerCompressionSample k i path))
        (onlineRefreshBranch k) (onlinePathLaw A) := by
  classical
  dsimp only
  let initialLaw := onlineBatchLaw A.problem b
  let differenceBatchLaw := onlineBatchLaw A.problem b0
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let restLaw := (initialLaw.prod differenceBatchLaw).prod rowLaw
  let roundLaw := coinLaw.prod restLaw
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let prefixMap := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (path.1, onlineRoundPrefix k path.2)
  let current := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    path.2 k
  let batch := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (current path).2.1.2
  let row := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (current path).2.2
  let sample := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    row path i
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    unfold rowLaw workerCompressionLaw
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
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  have hbatch : Measurable batch := by
    dsimp [batch, current]
    fun_prop
  have hrow : Measurable row := by
    dsimp [row, current]
    fun_prop
  have hsample : Measurable sample := (measurable_pi_apply i).comp hrow
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixMap, prefixLaw, prefixStreamLaw, law, onlineRoundPrefix]
      using hm.symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · let streamJoint := fun stream :
          ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
          ((fun j : Fin k ↦ stream j.1), stream k)
      have hstreamJoint : MeasurePreserving streamJoint streamLaw
          (prefixStreamLaw.prod roundLaw) := by
        refine ⟨(by
          dsimp [streamJoint]
          exact (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).prodMk
            (measurable_pi_apply k)), ?_⟩
        have hj := infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ roundLaw) k
        have hprefixStream : Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
              fun j : Fin k ↦ stream j.1) streamLaw = prefixStreamLaw := by
          simpa [streamLaw, prefixStreamLaw] using
            iidStream_prefix_map_eq_infinitePi roundLaw k
        have hprefixRaw : Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
              fun j : Fin k ↦ stream j.1)
            (Measure.infinitePi (fun _ : ℕ ↦ roundLaw)) =
              prefixStreamLaw := by
          simpa [streamLaw] using hprefixStream
        rw [hprefixRaw] at hj
        simpa [streamJoint, streamLaw, prefixStreamLaw] using hj
      have h0 := (MeasurePreserving.id initialLaw).prod hstreamJoint
      have h1 :=
        (measurePreserving_prodAssoc initialLaw prefixStreamLaw roundLaw).symm
      have h := h1.comp h0
      simpa [law, prefixLaw, prefixStreamLaw, prefixMap, current,
        onlineRoundPrefix, streamJoint, Function.comp_def] using h.map_eq
  let noise := fun path :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
    (batch path, row path)
  have hnoise : Measurable noise := hbatch.prodMk hrow
  have hprefixNoise : ProbabilityTheory.IndepFun prefixMap noise law := by
    have h := hpastCurrent.comp measurable_id
      (show Measurable
        (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
          (z.2.1.2, z.2.2)) by fun_prop)
    simpa [noise, batch, row, current, Function.comp_def] using h
  have hnoiseLaw : Measure.map noise law = differenceBatchLaw.prod rowLaw := by
    have hcurrentLaw : Measure.map current law = roundLaw := by
      calc
        Measure.map current law = Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
            (Measure.map Prod.snd law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_pi_apply k
              · exact measurable_snd
        _ = Measure.map
            (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ stream k)
            streamLaw := by
              rw [show Measure.map Prod.snd law = streamLaw by
                dsimp [law]
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
        _ = roundLaw := by
          simpa [streamLaw] using SOptLib.iidStreamLaw_map_eval roundLaw k
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
            (z.2.1.2, z.2.2)) (Measure.map current law) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · fun_prop
        · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦
            (z.2.1.2, z.2.2)) roundLaw := by rw [hcurrentLaw]
      _ = differenceBatchLaw.prod rowLaw := by
        simpa [roundLaw, differenceBatchLaw, rowLaw] using
          onlineRoundLaw_differenceCompression_marginal (b := b) A
  have hprefixBatchRow : ProbabilityTheory.IndepFun
      (fun path ↦ (prefixMap path, batch path)) row law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law differenceBatchLaw rowLaw
      prefixMap batch row hprefix hbatch hrow hprefixNoise hnoiseLaw
  have hbatchLaw : Measure.map batch law = differenceBatchLaw := by
    calc
      Measure.map batch law = Measure.map Prod.fst (Measure.map noise law) := by
        simpa [noise, Function.comp_apply] using
          (Measure.map_map measurable_fst hnoise (μ := law)).symm
      _ = Measure.map Prod.fst (differenceBatchLaw.prod rowLaw) := by
        rw [hnoiseLaw]
      _ = differenceBatchLaw := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := onlineExecutablePrefixState A x0 hBatch fallback k
  let F := fun (pref :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (fresh : (w : Worker n) → Fin b0.1 → Sample w) ↦
    onlineBatchDifference A.problem fresh i
      (primalStep A.stepSize (prefixState pref)) (prefixState pref).x
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod differenceBatchLaw) := by
    simpa [F, prefixState, prefixLaw, prefixStreamLaw, initialLaw, roundLaw,
      differenceBatchLaw] using
      onlineExecutablePrefix_workerDifferenceMessage_product_aestronglyMeasurable_of_generatedKernel
        A x0 hBatch ℒlocal hKernel fallback k i
  let kernel' := hF.mk (Function.uncurry F)
  have hkernel' : Measurable kernel' := hF.measurable_mk
  let joined := fun path ↦ (prefixMap path, batch path)
  have hjoined : Measurable joined := hprefix.prodMk hbatch
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law :=
    hprefixNoise.comp measurable_id measurable_fst
  have hjoinedLaw : Measure.map joined law =
      prefixLaw.prod differenceBatchLaw := by
    calc
      Measure.map joined law =
          (Measure.map prefixMap law).prod (Measure.map batch law) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hprefix.aemeasurable hbatch.aemeasurable).1 hprefixBatch
      _ = prefixLaw.prod differenceBatchLaw := by rw [hprefixLaw, hbatchLaw]
  have hjoinedQmp : Measure.QuasiMeasurePreserving joined law
      (prefixLaw.prod differenceBatchLaw) := ⟨hjoined, by rw [hjoinedLaw]⟩
  have hkernelMk := hjoinedQmp.tendsto_ae hF.ae_eq_mk
  have hstatePrefix : ∀ path, prefixState (prefixMap path) =
      onlineProcess (b := b) (b0 := b0) A x0 hBatch k path := by
    intro path
    dsimp [prefixState, prefixMap]
    exact (onlineProcess_congr_round_prefix A x0 hBatch k path.1
      (path := path.2)
      (path' := onlineExtendRoundPrefix fallback (onlineRoundPrefix k path.2))
      (by intro t ht; simp [onlineExtendRoundPrefix, onlineRoundPrefix, ht])).symm
  have hcalcMessage : (fun path ↦ kernel' (joined path)) =ᵐ[law]
      onlineWorkerDifferenceMessage A x0 hBatch k i := by
    filter_upwards [hkernelMk] with path hk
    have hk' : Function.uncurry F (joined path) = kernel' (joined path) := by
      simpa only [Set.mem_preimage, Set.mem_setOf_eq] using hk
    rw [← hk']
    dsimp [Function.uncurry, F, joined, batch, current,
      onlineWorkerDifferenceMessage]
    rw [hstatePrefix path]
  let hm := onlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
    A x0 hBatch ℒlocal hKernel k i
  have hcalcIndep : ProbabilityTheory.IndepFun
      (fun path ↦ kernel' (joined path)) sample law := by
    simpa [joined, sample] using
      hprefixBatchRow.comp hkernel' (measurable_pi_apply i)
  have hfirst : ProbabilityTheory.IndepFun
      (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i))
      (onlineWorkerCompressionSample k i) (onlinePathLaw A) := by
    apply hcalcIndep.congr
    · exact hcalcMessage.trans hm.ae_eq_mk
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  let supportF := fun (pref :
      ((w : Worker n) → Fin b.1 → Sample w) ×
        (Fin k → OnlineRoundNoise n b b0 Sample Ξ))
      (rest : ((((w : Worker n) → Fin b.1 → Sample w) ×
        ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ))) ↦
    quantizerNonzeroCount A.quantizer
      (kernel' (pref, rest.1.2)) (rest.2 i)
  have hsupportF : Measurable (Function.uncurry supportF) := by
    have hm : Measurable (fun z :
        (((w : Worker n) → Fin b.1 → Sample w) ×
            (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
          ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        kernel' (z.1, z.2.1.2)) := by fun_prop
    have hs : Measurable (fun z :
        (((w : Worker n) → Fin b.1 → Sample w) ×
            (Fin k → OnlineRoundNoise n b b0 Sample Ξ)) ×
          ((((w : Worker n) → Fin b.1 → Sample w) ×
            ((w : Worker n) → Fin b0.1 → Sample w)) × (Worker n → Ξ)) ↦
        z.2.2 i) := by fun_prop
    simpa [supportF] using
      (quantizerNonzeroCount_joint_measurable A.quantizer).comp (hm.prodMk hs)
  have hsupportIndep : ProbabilityTheory.IndepFun
      (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
        supportF (path.1, fun j : Fin k ↦ path.2 j.1) (path.2 k).2)
      (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦ (path.2 k).1)
      law := by
    have h := initial_iidStream_prefix_current_snd_kernel_indep_fst
      initialLaw coinLaw restLaw k supportF hsupportF.aestronglyMeasurable
    simpa [law, streamLaw, roundLaw] using h
  have hsupportAE :
      (fun path : ((w : Worker n) → Fin b.1 → Sample w) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) ↦
        supportF (path.1, fun j : Fin k ↦ path.2 j.1) (path.2 k).2) =ᵐ[law]
      (fun path ↦ quantizerNonzeroCount A.quantizer
        (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
        (onlineWorkerCompressionSample k i path)) := by
    filter_upwards [hcalcMessage, hm.ae_eq_mk] with path hc hm'
    have hc' : kernel'
        ((path.1, fun j : Fin k ↦ path.2 j.1), (path.2 k).2.1.2) =
          onlineWorkerDifferenceMessage A x0 hBatch k i path := by
      simpa [onlineRoundPrefix] using hc
    dsimp [supportF, joined, prefixMap, batch, row, sample, current,
      onlineWorkerCompressionSample] at *
    rw [hc', hm']
  have hsecond : ProbabilityTheory.IndepFun
      (fun path ↦ quantizerNonzeroCount A.quantizer
        (hm.mk (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
        (onlineWorkerCompressionSample k i path))
      (onlineRefreshBranch k) (onlinePathLaw A) := by
    apply hsupportIndep.congr hsupportAE
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  exact ⟨hfirst, hsecond⟩

/-- The source-faithful generated Assumption 3.2 kernel supplies the complete
law-a.e. communication interface used by executable homogeneous cost
accounting.  In particular, this theorem contains neither
`OnlineAdaptiveSampleGradientLawRegularity` nor a cost-integrability witness. -/
theorem onlineCommunicationAELawRegularity_of_generatedKernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (ℒlocal : Worker n → ℝ)
    (hKernel : OnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (onlineProcess (b := b) (b0 := b0) A x0 hBatch)
      (onlinePathLaw (b := b) (b0 := b0) A) ℒlocal) :
    OnlineCommunicationAELawRegularity A x0 hBatch := by
  let hm := fun k i ↦
    onlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
      A x0 hBatch ℒlocal hKernel k i
  refine ⟨hm, ?_, ?_⟩
  · intro k i
    exact (onlineWorkerMessageRepresentative_independences_of_generatedKernel
      A x0 hBatch ℒlocal hKernel k i).1
  · intro k i
    exact (onlineWorkerMessageRepresentative_independences_of_generatedKernel
      A x0 hBatch ℒlocal hKernel k i).2

/-! ## Generated-kernel executable measured release boundary

The following wrappers reuse the already proved executable accuracy and
communication suppliers on the same generated process and path law.  They
therefore expose source Assumption 3.2 as its generated conditional kernel
instead of accepting all-query sampled-gradient regularity. -/

theorem onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_generatedKernel
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProcess A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε))
      (onlinePathLaw
        (b := onlineNonconvexBatchScheduleFromBase n b0
          (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch ε)
        (b0 := b0) A) ℒlocal)
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
    apply onlineExecutableNonconvexAccuracy_family_of_budget_of_literal_and_generatedKernel
      A x0 chosenBatch K Llocal ℒlocal σ ω fStar hLower hSmooth
        hLiteral hQuantizer hBatch
    · intro eps
      simpa [chosenBatch] using hAssumption32 eps
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
    exact onlineCommunicationAELawRegularity_of_generatedKernel
      A x0 (hBatch eps) ℒlocal (by
        simpa [chosenBatch] using hAssumption32 eps)
  · exact hQuantizer
  · exact hEndpoints

/-- Law-a.e. supplied-stepsize executable D.4 with measured costs.  The geometric
horizon allocates one quarter of the target to contraction.  The source
batch schedule allocates one half to the stationary variance floor, while
`2 γ μ ≤ p` makes the sampled-initializer contribution at most the
remaining quarter.  Consequently the accuracy field, oracle integral, and
communication integral all refer to the same sampled-initializer
`onlineProcess` experiment. -/

theorem onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_generatedKernel
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProcess A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
      (onlinePathLaw
        (b := onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        (b0 := b0) A) ℒlocal)
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
    apply onlineExecutablePLAccuracy_family_of_budget_of_literal_and_generatedKernel
      A x0 xStar chosenBatch K Llocal ℒlocal σ ω fStar μ hLower
        hSmooth hLiteral hPL hQuantizer hBatch
    · intro eps
      simpa [chosenBatch] using hAssumption32 eps
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
    exact onlineCommunicationAELawRegularity_of_generatedKernel
      A x0 (hBatch eps) ℒlocal (by
        simpa [chosenBatch] using hAssumption32 eps)
  · exact hQuantizer
  · exact hEndpoints

/-- Law-a.e. canonical Eq. (40) specialization of the executable D.3 measured-cost
family.  The equality premise records the source's canonical choice of the
reciprocal Eq. (40) bracket; unlike the upper-bound-only stepsize condition,
it is strong enough to replace `1 / A.stepSize` by that bracket in the
complexity scale.  The additive `1` is the nonempty-output-window
totalization and also covers the already-solved zero-gap case.

The refresh batch remains the initialization-corrected executable schedule
from the supplied-step theorem.  Thus the convergence statement and the two
cost integrals still concern the same sampled-initializer `onlineProcess`
experiment. -/

theorem onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_literal_and_generatedKernel
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProcess A x0
        (onlineNonconvexBatchScheduleFromBase_admissible n b0
          (2 * varianceAggregateSq σ / A.refreshProbability)
          baseBatch ε))
      (onlinePathLaw
        (b := onlineNonconvexBatchScheduleFromBase n b0
          (2 * varianceAggregateSq σ / A.refreshProbability) baseBatch ε)
        (b0 := b0) A) ℒlocal)
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
    onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_generatedKernel
      A x0 baseBatch Llocal ℒlocal σ ω fStar hLower hSmooth hLiteral
        hQuantizer hAssumption32 hStep
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

/-- Law-a.e. canonical Eq. (48) specialization of the executable D.4 measured-cost
family.  The canonical denominator simultaneously enforces the doubled
smoothness bracket and `2 γ μ ≤ p`.  Consequently the supplied reciprocal
stepsize scale is controlled by the source factor
`max (1 / p) (bracket / μ)`.  The `max 0` logarithm and additive `1` are the
totalized finite-horizon form of the printed geometric rate. -/

theorem onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_literal_and_generatedKernel
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 xStar : Point d)
    (baseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32 : ∀ ε, OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
      (onlineProcess A x0
        (onlinePLBatchScheduleFromBase_admissible n b0
          (varianceAggregateSq σ) μ baseBatch ε))
      (onlinePathLaw
        (b := onlinePLBatchScheduleFromBase n b0
          (varianceAggregateSq σ) μ baseBatch ε)
        (b0 := b0) A) ℒlocal)
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
    onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_generatedKernel
      A x0 xStar baseBatch Llocal ℒlocal σ ω fStar μ hLower hSmooth
        hLiteral hPL hQuantizer hAssumption32 hStep
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

theorem Theorem_D3_D4_measured_cost_complexity_with_separate_canonical_stepsizes
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (γNonconvex γPL : PositiveStepsize)
    (x0 xStar : Point d)
    (nonconvexBaseBatch plBaseBatch : Accuracy → Count)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (μ : PositivePLParameter)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hPL : SatisfiesPL (onlineLocalProblem A.problem) μ xStar)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hAssumption32Nonconvex : ∀ ε,
      OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A γNonconvex A.refreshProbability
            A.refresh_admissible) x0
          (onlineNonconvexBatchScheduleFromBase_admissible n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε))
        (onlinePathLaw
          (b := onlineNonconvexBatchScheduleFromBase n b0
            (2 * varianceAggregateSq σ / A.refreshProbability)
            nonconvexBaseBatch ε)
          (b0 := b0)
          (onlineDataWithParameters A γNonconvex A.refreshProbability
            A.refresh_admissible)) ℒlocal)
    (hAssumption32PL : ∀ ε,
      OnlineAssumption32GeneratedConditionalKernel (b0 := b0) A.problem
        (onlineProcess
          (onlineDataWithParameters A γPL A.refreshProbability
            A.refresh_admissible) x0
          (onlinePLBatchScheduleFromBase_admissible n b0
            (varianceAggregateSq σ) μ plBaseBatch ε))
        (onlinePathLaw
          (b := onlinePLBatchScheduleFromBase n b0
            (varianceAggregateSq σ) μ plBaseBatch ε)
          (b0 := b0)
          (onlineDataWithParameters A γPL A.refreshProbability
            A.refresh_admissible)) ℒlocal)
    (hCanonicalStepNonconvex :
      (γNonconvex : ℝ) *
        (rootMeanSquare Llocal +
          Real.sqrt ((1 - A.refreshProbability) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1)
    (hCanonicalStepPL :
      (γPL : ℝ) * max (2 * (μ : ℝ) / A.refreshProbability)
        (rootMeanSquare Llocal +
          Real.sqrt ((2 * (1 - A.refreshProbability)) /
            (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))) = 1) :
    let ANonconvex := onlineDataWithParameters A γNonconvex
      A.refreshProbability A.refresh_admissible
    let APL := onlineDataWithParameters A γPL
      A.refreshProbability A.refresh_admissible
    let nonconvexBatch := onlineNonconvexBatchScheduleFromBase n b0
      (2 * varianceAggregateSq σ / A.refreshProbability) nonconvexBaseBatch
    let plBatch := onlinePLBatchScheduleFromBase n b0
      (varianceAggregateSq σ) μ plBaseBatch
    let nonconvexAdmissible := fun ε =>
      onlineNonconvexBatchScheduleFromBase_admissible n b0
        (2 * varianceAggregateSq σ / A.refreshProbability)
        nonconvexBaseBatch ε
    let plAdmissible := fun ε =>
      onlinePLBatchScheduleFromBase_admissible n b0
        (varianceAggregateSq σ) μ plBaseBatch ε
    let Δnc := globalObjective (onlineLocalProblem A.problem) x0 - fStar
    let Δpl := globalObjective (onlineLocalProblem A.problem) x0 -
      globalObjective (onlineLocalProblem A.problem) xStar
    let nonconvexBracket := rootMeanSquare Llocal +
      Real.sqrt ((1 - A.refreshProbability) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let plBracket := rootMeanSquare Llocal +
      Real.sqrt ((2 * (1 - A.refreshProbability)) /
        (A.refreshProbability * n.1) *
          (ω * rootMeanSquare Llocal ^ 2 +
            (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
    let nonconvexSuppliedScale := fun ε : Accuracy =>
      1 + 4 * Δnc / ((γNonconvex : ℝ) * (ε : ℝ) ^ 2)
    let plSuppliedScale := fun ε : Accuracy =>
      1 + max 0 (Real.log (4 * Δpl / (ε : ℝ)) /
        ((γPL : ℝ) * (μ : ℝ)))
    let nonconvexCanonicalScale := fun ε : Accuracy =>
      1 + Δnc / (ε : ℝ) ^ 2 * nonconvexBracket
    let plCanonicalScale := fun ε : Accuracy =>
      1 + max (1 / A.refreshProbability) (plBracket / (μ : ℝ)) *
        max 0 (Real.log (4 * Δpl / (ε : ℝ)))
    OnlineSeparateStepsizeMeasuredCostComplexity ANonconvex APL x0 xStar
        nonconvexBatch plBatch nonconvexAdmissible plAdmissible
        nonconvexSuppliedScale plSuppliedScale ∧
      OnlineSeparateStepsizeMeasuredCostComplexity ANonconvex APL x0 xStar
        nonconvexBatch plBatch nonconvexAdmissible plAdmissible
        nonconvexCanonicalScale plCanonicalScale := by
  dsimp only
  let ANonconvex := onlineDataWithParameters A γNonconvex
    A.refreshProbability A.refresh_admissible
  let APL := onlineDataWithParameters A γPL
    A.refreshProbability A.refresh_admissible
  have hStepNonconvex : OnlineVRStepsizeCondition γNonconvex
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω n b0 := by
    unfold OnlineVRStepsizeCondition FiniteSumVRStepsizeCondition
    simpa using hCanonicalStepNonconvex.le
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hγPL : 0 < (γPL : ℝ) := γPL.property
  let plBracket := rootMeanSquare Llocal +
    Real.sqrt ((2 * (1 - A.refreshProbability)) /
      (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * rootMeanSquare ℒlocal ^ 2 / b0.1))
  let plDenominator := max (2 * (μ : ℝ) / A.refreshProbability) plBracket
  have hCanonicalPL : (γPL : ℝ) * plDenominator = 1 := by
    simpa [plDenominator, plBracket] using hCanonicalStepPL
  have hStepPL : OnlineVRPLStepsizeCondition γPL
      (rootMeanSquare Llocal) (rootMeanSquare ℒlocal)
      A.refreshProbability ω μ n b0 := by
    unfold OnlineVRPLStepsizeCondition FiniteSumVRPLStepsizeCondition
    constructor
    · have hle : plBracket ≤ plDenominator := le_max_right _ _
      have hmul := mul_le_mul_of_nonneg_left hle hγPL.le
      simpa [plBracket] using hmul.trans_eq hCanonicalPL
    · rw [← div_le_one hp]
      calc
        2 * (γPL : ℝ) * (μ : ℝ) / A.refreshProbability =
            (γPL : ℝ) * (2 * (μ : ℝ) / A.refreshProbability) := by
              ring
        _ ≤ (γPL : ℝ) * plDenominator :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hγPL.le
        _ = 1 := hCanonicalPL
  constructor
  · unfold OnlineSeparateStepsizeMeasuredCostComplexity
    constructor
    · apply
        onlineExecutableNonconvexMeasuredCostComplexity_supplied_stepsize_of_literal_and_generatedKernel
        ANonconvex x0 nonconvexBaseBatch Llocal ℒlocal σ ω fStar
      · simpa [ANonconvex, onlineDataWithParameters] using hLower
      · simpa [ANonconvex, onlineDataWithParameters] using hSmooth
      · simpa [ANonconvex, onlineDataWithParameters] using hLiteral
      · simpa [ANonconvex, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [ANonconvex, onlineDataWithParameters] using
          hAssumption32Nonconvex ε
      · simpa [ANonconvex, onlineDataWithParameters] using hStepNonconvex
    · apply
        onlineExecutablePLMeasuredCostComplexity_supplied_stepsize_of_literal_and_generatedKernel
        APL x0 xStar plBaseBatch Llocal ℒlocal σ ω fStar μ
      · simpa [APL, onlineDataWithParameters] using hLower
      · simpa [APL, onlineDataWithParameters] using hSmooth
      · simpa [APL, onlineDataWithParameters] using hLiteral
      · simpa [APL, onlineDataWithParameters] using hPL
      · simpa [APL, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [APL, onlineDataWithParameters] using hAssumption32PL ε
      · simpa [APL, onlineDataWithParameters] using hStepPL
  · unfold OnlineSeparateStepsizeMeasuredCostComplexity
    constructor
    · apply
        onlineExecutableNonconvexMeasuredCostComplexity_canonical_stepsize_of_literal_and_generatedKernel
        ANonconvex x0 nonconvexBaseBatch Llocal ℒlocal σ ω fStar
      · simpa [ANonconvex, onlineDataWithParameters] using hLower
      · simpa [ANonconvex, onlineDataWithParameters] using hSmooth
      · simpa [ANonconvex, onlineDataWithParameters] using hLiteral
      · simpa [ANonconvex, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [ANonconvex, onlineDataWithParameters] using
          hAssumption32Nonconvex ε
      · simpa [ANonconvex, onlineDataWithParameters] using
          hCanonicalStepNonconvex
    · apply
        onlineExecutablePLMeasuredCostComplexity_canonical_stepsize_of_literal_and_generatedKernel
        APL x0 xStar plBaseBatch Llocal ℒlocal σ ω fStar μ
      · simpa [APL, onlineDataWithParameters] using hLower
      · simpa [APL, onlineDataWithParameters] using hSmooth
      · simpa [APL, onlineDataWithParameters] using hLiteral
      · simpa [APL, onlineDataWithParameters] using hPL
      · simpa [APL, onlineDataWithParameters] using hQuantizer
      · intro ε
        simpa [APL, onlineDataWithParameters] using hAssumption32PL ε
      · simpa [APL, onlineDataWithParameters] using hCanonicalStepPL

/-- Compatibility alias for the strengthened name introduced before the
registered release root itself was migrated to the combined conclusion. -/
alias
  Theorem_D3_D4_measured_cost_complexity_with_separate_canonical_stepsizes_and_supplied_rates :=
    Theorem_D3_D4_measured_cost_complexity_with_separate_canonical_stepsizes

set_option maxHeartbeats 2000000 in
/-- One worker's exact generated Assumption 3.2 kernel supplies the
worker-dependent row innovation moment used in Remark D.2.  The proof moves
the source fiber first through the heterogeneous worker marginal and then
through the matching homogeneous worker marginal; the only measurability
input is the generated row fact proved from that same kernel. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_workerRowInnovation_moment_ae
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    ∀ᵐ path ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A,
      let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let rowBatchLaw :=
        Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
      let rowLaw := rowBatchLaw.prod A.quantizer.law
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let innovation := fun q : (Fin (b0 i).1 → Sample i) × Ξ ↦
        A.quantizer.apply
            (average (fun j : Fin (b0 i).1 ↦
              stochasticGradient A.problem i (q.1 j) xNext -
                stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
      Integrable innovation rowLaw ∧
        Integrable (fun q ↦ ‖innovation q‖ ^ 2) rowLaw ∧
        (∫ q, innovation q ∂rowLaw) = 0 ∧
        (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
          (ω * (Llocal i) ^ 2 +
              (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
            ‖xNext - x‖ ^ 2 := by
  classical
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let pathLaw := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hAverage :=
    heterogeneousOnlineAssumption32GenuineAE_to_averageSmoothnessAE
      A x0 ℒlocal
        (heterogeneousOnlineAssumption32GeneratedConditionalKernel_to_genuineAE
          hKernel)
  have hRow :=
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_workerRowDifference_aestronglyMeasurable_ae
      hKernel k i
  filter_upwards [hAverage.2 k, hRow] with path hFibers hRowMeasurable
  let x := (run k path).x
  let xNext := (run (k + 1) path).x
  let heteroBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let scalarBatchLaw := onlineBatchLaw A.problem (b0 i)
  let rows := Measure.infinitePi
    (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
  let heteroRow := fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i
  let scalarRow := fun batch :
      (w : Worker n) → Fin (b0 i).1 → Sample w ↦ batch i
  let localD := fun row : Fin (b0 i).1 → Sample i ↦
    average (fun j : Fin (b0 i).1 ↦
      stochasticGradient A.problem i (row j) xNext -
        stochasticGradient A.problem i (row j) x)
  let delta := localGradientDifference
    (onlineLocalProblem A.problem) i xNext x
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure heteroBatchLaw := by
    dsimp [heteroBatchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure scalarBatchLaw := by
    dsimp [scalarBatchLaw]
    unfold onlineBatchLaw
    infer_instance
  have hHetMap : Measure.map heteroRow heteroBatchLaw = rows := by
    simpa [heteroRow, heteroBatchLaw, rows,
      MeasureTheory.Measure.infinitePi_eq_pi] using
      heterogeneous_online_batch_law_worker_marginal A.problem b0 i
  have hScalarMap : Measure.map scalarRow scalarBatchLaw = rows := by
    simpa [scalarRow, scalarBatchLaw, rows,
      MeasureTheory.Measure.infinitePi_eq_pi] using
      onlineBatchLaw_worker_marginal A.problem i
  have hlocalD : AEStronglyMeasurable localD rows := by
    simpa [localD, rows, run, pathLaw, xNext, x,
      MeasureTheory.Measure.infinitePi_eq_pi] using hRowMeasurable
  have hlocalResidual : AEStronglyMeasurable
      (fun row ↦ ‖localD row - delta‖ ^ 2) rows :=
    (hlocalD.sub aestronglyMeasurable_const).norm.pow 2
  have hFiber := hFibers i
  have hDrow : Integrable localD rows := by
    rw [← hHetMap]
    apply (MeasureTheory.integrable_map_measure (by
      rw [hHetMap]
      exact hlocalD) (measurable_pi_apply i).aemeasurable).mpr
    simpa [localD, heteroRow, heterogeneousOnlineBatchDifference,
      heteroBatchLaw, xNext, x, run] using hFiber.1
  have hResidualRow : Integrable
      (fun row ↦ ‖localD row - delta‖ ^ 2) rows := by
    rw [← hHetMap]
    apply (MeasureTheory.integrable_map_measure (by
      rw [hHetMap]
      exact hlocalResidual) (measurable_pi_apply i).aemeasurable).mpr
    simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
      heteroBatchLaw, xNext, x, run] using hFiber.2.1
  have hMeanRow : (∫ row, localD row ∂rows) = delta := by
    rw [← hHetMap, MeasureTheory.integral_map
      (measurable_pi_apply i).aemeasurable
      (by rw [hHetMap]; exact hlocalD)]
    simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
      heteroBatchLaw, xNext, x, run] using hFiber.2.2.1
  have hSecondRow : (∫ row, ‖localD row - delta‖ ^ 2 ∂rows) ≤
      (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2 := by
    rw [← hHetMap, MeasureTheory.integral_map
      (measurable_pi_apply i).aemeasurable
      (by rw [hHetMap]; exact hlocalResidual)]
    simpa [localD, delta, heteroRow, heterogeneousOnlineBatchDifference,
      heteroBatchLaw, xNext, x, run] using hFiber.2.2.2
  have hScalarFiber :
      let delta' := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let D := fun batch ↦
        onlineBatchDifference A.problem batch i xNext x
      Integrable D scalarBatchLaw ∧
        Integrable (fun batch ↦ ‖D batch - delta'‖ ^ 2) scalarBatchLaw ∧
        (∫ batch, D batch ∂scalarBatchLaw) = delta' ∧
        (∫ batch, ‖D batch - delta'‖ ^ 2 ∂scalarBatchLaw) ≤
          (ℒlocal i) ^ 2 / (b0 i).1 * ‖xNext - x‖ ^ 2 := by
    dsimp only
    have hD : Integrable (localD ∘ scalarRow) scalarBatchLaw :=
      (MeasureTheory.integrable_map_measure (by
        rw [hScalarMap]
        exact hlocalD) (measurable_pi_apply i).aemeasurable).mp
        (by rw [hScalarMap]; exact hDrow)
    have hR : Integrable
        ((fun row ↦ ‖localD row - delta‖ ^ 2) ∘ scalarRow)
        scalarBatchLaw :=
      (MeasureTheory.integrable_map_measure (by
        rw [hScalarMap]
        exact hlocalResidual) (measurable_pi_apply i).aemeasurable).mp
        (by rw [hScalarMap]; exact hResidualRow)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [localD, scalarRow, onlineBatchDifference,
        scalarBatchLaw] using hD
    · simpa [localD, delta, scalarRow, onlineBatchDifference,
        scalarBatchLaw] using hR
    · calc
        (∫ batch, onlineBatchDifference A.problem batch i xNext x
            ∂scalarBatchLaw) =
            ∫ batch, localD (scalarRow batch) ∂scalarBatchLaw := by rfl
        _ = ∫ row, localD row ∂Measure.map scalarRow scalarBatchLaw := by
          rw [MeasureTheory.integral_map
            (measurable_pi_apply i).aemeasurable
            (by rw [hScalarMap]; exact hlocalD)]
        _ = ∫ row, localD row ∂rows := by rw [hScalarMap]
        _ = delta := hMeanRow
    · calc
        (∫ batch,
            ‖onlineBatchDifference A.problem batch i xNext x -
              localGradientDifference (onlineLocalProblem A.problem)
                i xNext x‖ ^ 2 ∂scalarBatchLaw) =
            ∫ batch, ‖localD (scalarRow batch) - delta‖ ^ 2
              ∂scalarBatchLaw := by rfl
        _ = ∫ row, ‖localD row - delta‖ ^ 2
              ∂Measure.map scalarRow scalarBatchLaw := by
          rw [MeasureTheory.integral_map
            (measurable_pi_apply i).aemeasurable
            (by rw [hScalarMap]; exact hlocalResidual)]
        _ = ∫ row, ‖localD row - delta‖ ^ 2 ∂rows := by
          rw [hScalarMap]
        _ ≤ _ := hSecondRow
  dsimp only
  apply
    onlineFixed_nonrefresh_worker_row_moment_of_assumption32_and_rowMeasurability
      (b0 := b0 i) A xNext x i Llocal ℒlocal ω hSmooth hScalarFiber
        _ hQuantizer
  simpa [rows] using hlocalD

set_option maxHeartbeats 3000000 in
/-- The exact generated Assumption 3.2 kernels aggregate over the independent
worker-row/compressor product to the nonrefresh average moment used by the
heterogeneous executable recurrence.  Unlike the compatibility theorem above,
this source-facing bridge needs no all-query adaptive-gradient regularity. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_fixed_nonrefresh_average_moment_ae
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) :
    ∀ᵐ path ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A,
      let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let law := (heterogeneousOnlineBatchLaw A.problem b0).prod
        (workerCompressionLaw (n := n) A.quantizer)
      let innovation := fun i : Worker n ↦
        fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 q.1 i xNext x)
              (q.2 i) -
            localGradientDifference (onlineLocalProblem A.problem) i xNext x
      Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
        (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
        Integrable
          (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2) law ∧
        (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            ‖xNext - x‖ ^ 2 := by
  classical
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let pathLaw := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure pathLaw := by
    unfold pathLaw heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hRows : ∀ᵐ path ∂pathLaw, ∀ i : Worker n,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let rowBatchLaw :=
        Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
      let rowLaw := rowBatchLaw.prod A.quantizer.law
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let innovation := fun q : (Fin (b0 i).1 → Sample i) × Ξ ↦
        A.quantizer.apply
            (average (fun j : Fin (b0 i).1 ↦
              stochasticGradient A.problem i (q.1 j) xNext -
                stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
      Integrable innovation rowLaw ∧
        Integrable (fun q ↦ ‖innovation q‖ ^ 2) rowLaw ∧
        (∫ q, innovation q ∂rowLaw) = 0 ∧
        (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
          (ω * (Llocal i) ^ 2 +
              (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) *
            ‖xNext - x‖ ^ 2 := by
    apply ae_all_iff.2
    intro i
    simpa [run, pathLaw] using
      (heterogeneousOnlineAssumption32GeneratedConditionalKernel_workerRowInnovation_moment_ae
        A x0 Llocal ℒlocal ω hSmooth hKernel hQuantizer k i)
  filter_upwards [hRows] with path hLocalFiber
  dsimp only
  let x := (run k path).x
  let xNext := (run (k + 1) path).x
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let law := batchLaw.prod compressionLaw
  let source := fun i : Worker n ↦
    fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
      (q.1 i, q.2 i)
  let rowLaw := fun i : Worker n ↦
    (Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)).prod
      A.quantizer.law
  let localInnovation := fun i : Worker n ↦
    fun q : (Fin (b0 i).1 → Sample i) × Ξ ↦
      A.quantizer.apply
          (average (fun j : Fin (b0 i).1 ↦
            stochasticGradient A.problem i (q.1 j) xNext -
              stochasticGradient A.problem i (q.1 j) x)) q.2 -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x
  let innovation := fun i : Worker n ↦
    fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
      localInnovation i (source i q)
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hsource : ∀ i : Worker n, Measurable (source i) := by
    intro i
    dsimp [source]
    fun_prop
  have hmap : ∀ i : Worker n, Measure.map (source i) law = rowLaw i := by
    intro i
    dsimp [source, law, rowLaw, batchLaw, compressionLaw]
    calc
      Measure.map
          (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
            (q.1 i, q.2 i))
          ((heterogeneousOnlineBatchLaw A.problem b0).prod
            (workerCompressionLaw A.quantizer)) =
          (Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i)
            (heterogeneousOnlineBatchLaw A.problem b0)).prod
            (Measure.map (fun q : Worker n → Ξ ↦ q i)
              (workerCompressionLaw A.quantizer)) := by
                symm
                simpa [Prod.map] using
                  (MeasureTheory.Measure.map_prod_map
                    (heterogeneousOnlineBatchLaw A.problem b0)
                    (workerCompressionLaw (n := n) A.quantizer)
                    (measurable_pi_apply i) (measurable_pi_apply i))
      _ = _ := by
        rw [heterogeneous_online_batch_law_worker_marginal A.problem b0 i,
          workerCompressionLaw_component_marginal A.quantizer i]
  have hWhole : Measure.map
      (fun q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ) ↦
        fun i ↦ source i q) law = Measure.infinitePi rowLaw := by
    let α := fun i : Worker n ↦ Fin (b0 i).1 → Sample i
    let β := fun _ : Worker n ↦ Ξ
    let μ := fun i : Worker n ↦
      Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
    let ν := fun _ : Worker n ↦ A.quantizer.law
    have hmp := measurePreserving_dependentArrowProdMeasurableEquiv α β μ ν
    have hinv := MeasurePreserving.symm
      (dependentArrowProdMeasurableEquiv α β) hmp
    simpa [law, batchLaw, compressionLaw, heterogeneousOnlineBatchLaw,
      workerCompressionLaw, source, rowLaw, α, β, μ, ν,
      MeasureTheory.Measure.infinitePi_eq_pi] using hinv.map_eq
  have hindep : ProbabilityTheory.iIndepFun source law := by
    apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun i ↦ hsource i)).2
    rw [hWhole]
    congr 1
    funext i
    exact (hmap i).symm
  have hdiag : ∀ i : Worker n,
      Integrable (fun q ↦ ‖innovation i q‖ ^ 2) law ∧
      (∫ q, ‖innovation i q‖ ^ 2 ∂law) ≤
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
    intro i
    have hsq : AEStronglyMeasurable (fun q ↦ ‖localInnovation i q‖ ^ 2)
        (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hLocalFiber i).2.1.aestronglyMeasurable
    constructor
    · exact (MeasureTheory.integrable_map_measure hsq
        (hsource i).aemeasurable).mp
          (by simpa [hmap i] using (hLocalFiber i).2.1)
    · rw [show (∫ q, ‖innovation i q‖ ^ 2 ∂law) =
          ∫ q, ‖localInnovation i q‖ ^ 2 ∂Measure.map (source i) law by
            rw [MeasureTheory.integral_map (hsource i).aemeasurable hsq],
        hmap i]
      exact (hLocalFiber i).2.2.2
  have hvec : ∀ i : Worker n,
      Integrable (innovation i) law ∧ (∫ q, innovation i q ∂law) = 0 := by
    intro i
    have hm : AEStronglyMeasurable (localInnovation i)
        (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hLocalFiber i).1.aestronglyMeasurable
    constructor
    · exact (MeasureTheory.integrable_map_measure hm
        (hsource i).aemeasurable).mp
          (by simpa [hmap i] using (hLocalFiber i).1)
    · rw [show (∫ q, innovation i q ∂law) =
          ∫ q, localInnovation i q ∂Measure.map (source i) law by
            rw [MeasureTheory.integral_map (hsource i).aemeasurable hm],
        hmap i]
      exact (hLocalFiber i).2.2.1
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) = 0 := by
    intro i j hij
    let fi := localInnovation i
    let fj := localInnovation j
    let fiMk := (hLocalFiber i).1.aestronglyMeasurable.mk fi
    let fjMk := (hLocalFiber j).1.aestronglyMeasurable.mk fj
    have hfiMk : Measurable fiMk :=
      (hLocalFiber i).1.aestronglyMeasurable.measurable_mk
    have hfjMk : Measurable fjMk :=
      (hLocalFiber j).1.aestronglyMeasurable.measurable_mk
    have hfi_ae : fi =ᵐ[rowLaw i] fiMk :=
      (hLocalFiber i).1.aestronglyMeasurable.ae_eq_mk
    have hfj_ae : fj =ᵐ[rowLaw j] fjMk :=
      (hLocalFiber j).1.aestronglyMeasurable.ae_eq_mk
    have hqmpi : Measure.QuasiMeasurePreserving (source i) law (rowLaw i) :=
      ⟨hsource i, by rw [hmap i]⟩
    have hqmpj : Measure.QuasiMeasurePreserving (source j) law (rowLaw j) :=
      ⟨hsource j, by rw [hmap j]⟩
    have hfi_global : innovation i =ᵐ[law] fiMk ∘ source i :=
      hqmpi.tendsto_ae hfi_ae
    have hfj_global : innovation j =ᵐ[law] fjMk ∘ source j :=
      hqmpj.tendsto_ae hfj_ae
    have hfixed_int : ∀ _ : (Fin (b0 j).1 → Sample j) × Ξ,
        Integrable (fun s ↦ fiMk s) (rowLaw i) := by
      intro _
      exact (hLocalFiber i).1.congr hfi_ae
    have hfixed_zero : ∀ _ : (Fin (b0 j).1 → Sample j) × Ξ,
        (∫ s, fiMk s ∂rowLaw i) = 0 := by
      intro _
      rw [← integral_congr_ae hfi_ae]
      exact (hLocalFiber i).2.2.1
    have hzero := randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      law (rowLaw i) (source j) (source i)
      (fun _ s ↦ fiMk s) fjMk
      (by exact hfiMk.comp measurable_snd) hfjMk
      (hsource j) (hsource i) (hindep.indepFun (Ne.symm hij))
      (hmap i) hfixed_int hfixed_zero
    calc
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) =
          ∫ q, ⟪fiMk (source i q), fjMk (source j q)⟫_ℝ ∂law := by
            apply integral_congr_ae
            filter_upwards [hfi_global, hfj_global] with q hi hj
            simpa [Function.comp_apply] using congrArg₂ (inner ℝ) hi hj
      _ = ∫ q, ⟪fjMk (source j q), fiMk (source i q)⟫_ℝ ∂law := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun q ↦ real_inner_comm _ _
      _ = 0 := hzero
  have hmeas : ∀ i : Worker n, AEStronglyMeasurable (innovation i) law :=
    fun i ↦ (hvec i).1.aestronglyMeasurable
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    law (Finset.univ : Finset (Worker n)) innovation
      (fun i _ ↦ hmeas i) (fun i _ ↦ (hdiag i).1)
      (fun i _ j _ hij ↦ hcross hij)
  have havgSq : Integrable
      (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2) law := by
    apply integrable_sq_norm_centeredMiniBatchAverage law
      (Finset.univ : Finset (Worker n)) n.1 innovation
      (fun q ↦ average (fun i : Worker n ↦ innovation i q))
    · intro i _
      exact hmeas i
    · intro i _
      exact (hdiag i).1
    · funext q
      simp [average, SOptLib.finiteUniformAverage_def, Fintype.card_fin]
  have havg : Integrable
      (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law := by
    unfold average SOptLib.finiteUniformAverage
    simpa [Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ ↦ (hvec i).1)).smul ((n.1 : ℝ)⁻¹)
  have havgZero :
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 := by
    unfold average SOptLib.finiteUniformAverage
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun i _ ↦ (hvec i).1)]
    simp [hvec]
  refine ⟨by simpa [innovation, law] using havg,
    by simpa [innovation, law] using havgZero,
    by simpa [innovation, law] using havgSq, ?_⟩
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
  calc
    (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) =
        ((n.1 : ℝ)⁻¹) ^ 2 *
          ∫ q, ‖Finset.sum Finset.univ (fun i ↦ innovation i q)‖ ^ 2 ∂law := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      unfold average SOptLib.finiteUniformAverage
      simp only [Fintype.card_fin]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n, ∫ q, ‖innovation i q‖ ^ 2 ∂law := by rw [hsum]
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 * ∑ i : Worker n,
        (ω * (Llocal i) ^ 2 +
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) * ‖xNext - x‖ ^ 2 := by
      gcongr with i
      exact (hdiag i).2
    _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          ‖xNext - x‖ ^ 2 := by
      have hmean_nonneg : 0 ≤ meanSquare Llocal := by
        unfold meanSquare average SOptLib.finiteUniformAverage
        positivity
      have hrms : (rootMeanSquare Llocal) ^ 2 = meanSquare Llocal := by
        unfold rootMeanSquare
        exact Real.sq_sqrt hmean_nonneg
      rw [hrms, ← Finset.sum_mul]
      unfold meanSquare heterogeneousFiniteBatchSmoothnessTerm average
        SOptLib.finiteUniformAverage
      simp only [smul_eq_mul, Fintype.card_fin]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [show (∑ i : Worker n,
          (1 + ω) * (ℒlocal i) ^ 2 / (b0 i).1) =
          (1 + ω) * ∑ i : Worker n, (ℒlocal i) ^ 2 / (b0 i).1 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
      field_simp [hn]

set_option maxHeartbeats 3000000 in
/-- The worker-dependent generated Assumption 3.2 kernel makes the complete
compressed nonrefresh innovation jointly measurable with the canonical
heterogeneous difference-batch/compressor coordinate.  Each worker is pulled
back from its own `b⁰ i` row marginal, so this source-facing bridge needs no
all-query adaptive-gradient regularity. -/
theorem
    heterogeneousOnlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_joint_aestronglyMeasurable
    {d n : Count} {Omega : Type*} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} {Xi : Type*}
    [MeasurableSpace Omega] [∀ i, MeasurableSpace (Sample i)]
    [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (run : ℕ → Omega → State d)
    (pathLaw : Measure Omega) [SFinite pathLaw] (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem run pathLaw Lcal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let noiseLaw := (heterogeneousOnlineBatchLaw A.problem b0).prod
      (workerCompressionLaw (n := n) A.quantizer)
    AEStronglyMeasurable
      (fun p : Omega ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
                (run (k + 1) p.1).x (run k p.1).x)
              (p.2.2 i) -
            localGradientDifference P i
              (run (k + 1) p.1).x (run k p.1).x))
      (pathLaw.prod noiseLaw) := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let noiseLaw := batchLaw.prod compressionLaw
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw
    infer_instance
  let reassoc := fun p : Omega ×
      (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi)) ↦
    ((p.1, p.2.1), p.2.2)
  have hreassoc : MeasurePreserving reassoc
      (pathLaw.prod noiseLaw) ((pathLaw.prod batchLaw).prod compressionLaw) := by
    simpa [reassoc, noiseLaw] using
      (MeasureTheory.measurePreserving_prodAssoc
        pathLaw batchLaw compressionLaw).symm
  have hpair : AEStronglyMeasurable
      (fun p : Omega × HeterogeneousOnlineBatch n Sample b0 ↦
        ((run (k + 1) p.1).x, (run k p.1).x))
      (pathLaw.prod batchLaw) := by
    have hp := hKernel.2.1 k
    exact (((measurable_snd.comp_aemeasurable hp.aemeasurable)
      |>.aestronglyMeasurable).prodMk
        ((measurable_fst.comp_aemeasurable hp.aemeasurable)
          |>.aestronglyMeasurable)).comp_fst
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Omega ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi)) ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
              (run (k + 1) p.1).x (run k p.1).x)
            (p.2.2 i) -
          localGradientDifference P i
            (run (k + 1) p.1).x (run k p.1).x)
      (pathLaw.prod noiseLaw) := by
    let rowLaw := Measure.pi
      (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
    let project := fun p : Omega × HeterogeneousOnlineBatch n Sample b0 ↦
      (p.1, p.2 i)
    have hproject : Measurable project := by
      dsimp [project]
      fun_prop
    have hprojectLaw : Measure.map project (pathLaw.prod batchLaw) =
        pathLaw.prod rowLaw := by
      have hm := MeasureTheory.Measure.map_prod_map pathLaw batchLaw
        measurable_id (measurable_pi_apply i)
      rw [Measure.map_id,
        heterogeneous_online_batch_law_worker_marginal A.problem b0 i] at hm
      simpa [project, rowLaw, batchLaw,
        MeasureTheory.Measure.infinitePi_eq_pi] using hm.symm
    have hrow :=
      heterogeneousOnlineAssumption32GeneratedConditionalKernel_rowDifference_joint_aestronglyMeasurable
        hKernel k i
    have hD : AEStronglyMeasurable
        (fun p : Omega × HeterogeneousOnlineBatch n Sample b0 ↦
          heterogeneousOnlineBatchDifference A.problem b0 p.2 i
            (run (k + 1) p.1).x (run k p.1).x)
        (pathLaw.prod batchLaw) := by
      have hqmp : Measure.QuasiMeasurePreserving project
          (pathLaw.prod batchLaw) (pathLaw.prod rowLaw) :=
        ⟨hproject, by rw [hprojectLaw]⟩
      simpa [project, rowLaw, heterogeneousOnlineBatchDifference,
        Function.comp_def] using hrow.comp_quasiMeasurePreserving hqmp
    have hDprod : AEStronglyMeasurable
        (fun p : (Omega × HeterogeneousOnlineBatch n Sample b0) ×
            (Worker n → Xi) ↦
          heterogeneousOnlineBatchDifference A.problem b0 p.1.2 i
            (run (k + 1) p.1.1).x (run k p.1.1).x)
        ((pathLaw.prod batchLaw).prod compressionLaw) := hD.comp_fst
    have hxi : Measurable
        (fun p : (Omega × HeterogeneousOnlineBatch n Sample b0) ×
            (Worker n → Xi) ↦ p.2 i) := by
      fun_prop
    have hquantized : AEStronglyMeasurable
        (fun p : (Omega × HeterogeneousOnlineBatch n Sample b0) ×
            (Worker n → Xi) ↦
          A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0 p.1.2 i
              (run (k + 1) p.1.1).x (run k p.1.1).x)
            (p.2 i))
        ((pathLaw.prod batchLaw).prod compressionLaw) :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hDprod.aemeasurable.prodMk hxi.aemeasurable)).aestronglyMeasurable
    have hdelta : AEStronglyMeasurable
        (fun p : (Omega × HeterogeneousOnlineBatch n Sample b0) ×
            (Worker n → Xi) ↦
          localGradientDifference P i
            (run (k + 1) p.1.1).x (run k p.1.1).x)
        ((pathLaw.prod batchLaw).prod compressionLaw) := by
      have hm : AEStronglyMeasurable
          (fun p : Omega × HeterogeneousOnlineBatch n Sample b0 ↦
            localGradientDifference P i
              (run (k + 1) p.1).x (run k p.1).x)
          (pathLaw.prod batchLaw) :=
        (((measurable_localGradient P i).comp_aemeasurable
            hpair.aemeasurable.fst).sub
          ((measurable_localGradient P i).comp_aemeasurable
            hpair.aemeasurable.snd)).aestronglyMeasurable
      exact hm.comp_fst
    have hsource := hquantized.sub hdelta
    simpa [reassoc, batchLaw, compressionLaw, noiseLaw, P,
      Function.comp_def] using hsource.comp_measurePreserving hreassoc
  unfold average SOptLib.finiteUniformAverage
  have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ ↦ hworker i)).const_smul
      ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hsum.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [P, Finset.sum_apply, Finset.sum_sub_distrib]

set_option maxHeartbeats 3000000 in
/-- The heterogeneous generated Assumption 3.2 kernel remains jointly
measurable after the unused iid tail is discarded.  The retained carrier is
the sampled worker-dependent initializer together with the strict round
prefix, and the right coordinate is exactly the fresh worker-dependent
difference batch and compressor family used by the executable update. -/
theorem
    heterogeneousOnlineExecutablePrefix_nonrefreshAverage_product_aestronglyMeasurable_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d) (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let initialLaw := heterogeneousOnlineBatchLaw A.problem b
    let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := initialLaw.prod
      (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
    let noiseLaw := heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A
    let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
      heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k
        (pref.1, fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
    AEStronglyMeasurable
      (fun p :
          (HeterogeneousOnlineBatch n Sample b ×
              (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
                (primalStep A.stepSize (prefixState p.1))
                (prefixState p.1).x)
              (p.2.2 i) -
            localGradientDifference P i
              (primalStep A.stepSize (prefixState p.1))
              (prefixState p.1).x))
      (prefixLaw.prod noiseLaw) := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let noiseLaw := heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw heterogeneousOnlineDifferenceCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hfull : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi))) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 p.2.1 i
                (run (k + 1) p.1).x (run k p.1).x)
              (p.2.2 i) -
            localGradientDifference P i
              (run (k + 1) p.1).x (run k p.1).x))
      (law.prod noiseLaw) := by
    simpa [P, run, law, initialLaw, streamLaw, noiseLaw,
      heterogeneousOnlinePathLaw] using
      heterogeneousOnlineAssumption32GeneratedConditionalKernel_nonrefreshAverage_joint_aestronglyMeasurable
        A run law Lcal hKernel k
  have hreorder : MeasurePreserving
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi))) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod noiseLaw).prod streamLaw)
      ((initialLaw.prod streamLaw).prod noiseLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw noiseLaw streamLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := noiseLaw) (ν := streamLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw streamLaw noiseLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hstream : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi))) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (heterogeneousOnlineBatchDifference A.problem b0 p.1.2.1 i
                (run (k + 1) (p.1.1, p.2)).x
                (run k (p.1.1, p.2)).x)
              (p.1.2.2 i) -
            localGradientDifference P i
              (run (k + 1) (p.1.1, p.2)).x
              (run k (p.1.1, p.2)).x))
      ((initialLaw.prod noiseLaw).prod streamLaw) := by
    simpa [Function.comp_def] using hfull.comp_measurePreserving hreorder
  let F := fun p :
      (HeterogeneousOnlineBatch n Sample b ×
          (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi))) ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0 p.1.2.1 i
            (primalStep A.stepSize (prefixState (p.1.1, p.2)))
            (prefixState (p.1.1, p.2)).x)
          (p.1.2.2 i) -
        localGradientDifference P i
          (primalStep A.stepSize (prefixState (p.1.1, p.2)))
          (prefixState (p.1.1, p.2)).x)
  have hstatePrefix : ∀ initial stream,
      prefixState (initial, fun j : Fin k ↦ stream j.1) =
        run k (initial, stream) := by
    intro initial stream
    dsimp [prefixState, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k initial
      (path := stream)
      (path' := fun t ↦ if ht : t < k then stream t
        else fallback t)
      (by intro t ht; simp [ht])).symm
  have hstreamF : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi))) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        F (p.1, fun j : Fin k ↦ p.2 j.1))
      ((initialLaw.prod noiseLaw).prod streamLaw) := by
    refine hstream.congr (Filter.Eventually.of_forall ?_)
    intro p
    dsimp [F]
    rw [hstatePrefix p.1.1 p.2]
    rfl
  have hfinite : AEStronglyMeasurable F
      ((initialLaw.prod noiseLaw).prod prefixStreamLaw) := by
    simpa [prefixStreamLaw] using
      aestronglyMeasurable_initial_prefix_of_comp_general
        (initialLaw.prod noiseLaw) roundLaw k F hstreamF
  have hreorderFinite : MeasurePreserving
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            (HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi))) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod prefixStreamLaw).prod noiseLaw)
      ((initialLaw.prod noiseLaw).prod prefixStreamLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw prefixStreamLaw noiseLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixStreamLaw) (ν := noiseLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw noiseLaw prefixStreamLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hresult := hfinite.comp_measurePreserving hreorderFinite
  simpa [F, P, prefixLaw, prefixStreamLaw, prefixState, initialLaw,
    roundLaw, noiseLaw, Function.comp_def] using hresult

set_option maxHeartbeats 8000000 in
/- The worker-dependent generated Assumption 3.2 kernel supplies the centered
second-moment package for the actual executable heterogeneous nonrefresh
innovation.  The sampled initializer and strict round prefix form the past
carrier; the current worker-dependent difference batches and compressors are
the fresh coordinate.  No all-query sample-gradient regularity is used. -/
theorem heterogeneousOnlineExecutable_nonrefresh_innovation_moments_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hStep : StepMomentWellDefined
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0
              (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
            ((path.2 k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    Integrable innovation law ∧
      (∫ path, innovation path ∂law) = 0 ∧
      Integrable (fun path ↦ ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run law k := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.1, fun j : Fin k ↦ path.2 j.1)
  let prefixLaw := Measure.map prefixMap law
  let streamPrefix := fun path :
      ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
    fun j : Fin k ↦ path j.1
  let streamCurrent := fun path :
      ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ path k
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let noiseOfRound := fun z :
      HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ (z.2.1.2, z.2.2)
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    noiseOfRound (current path)
  let noiseLaw := heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw heterogeneousOnlineDifferenceCompressionLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hprefixLaw : prefixLaw =
      initialLaw.prod (Measure.infinitePi (fun _ : Fin k ↦ roundLaw)) := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id,
      iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixLaw, prefixMap, law, initialLaw, streamLaw, roundLaw,
      heterogeneousOnlinePathLaw] using hm.symm
  have hstreamPrefix : Measurable streamPrefix := by
    dsimp [streamPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hstreamCurrent : Measurable streamCurrent := measurable_pi_apply k
  haveI : IsProbabilityMeasure (Measure.map streamPrefix streamLaw) :=
    Measure.isProbabilityMeasure_map hstreamPrefix.aemeasurable
  have hnoiseOfRound : Measurable noiseOfRound := by
    dsimp [noiseOfRound]
    fun_prop
  have hnoise : Measurable noise := by
    dsimp [noise, current]
    exact hnoiseOfRound.comp (hstreamCurrent.comp measurable_snd)
  have hpastCurrentStream : ProbabilityTheory.IndepFun
      streamPrefix streamCurrent streamLaw := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (streamPrefix path, streamCurrent path))
      (P := streamLaw)
      (mu := Measure.map streamPrefix streamLaw) (nu := roundLaw)
    · exact (hstreamPrefix.prodMk hstreamCurrent).aemeasurable
    · simpa [streamLaw, streamPrefix, streamCurrent, roundLaw,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod (fun _ : ℕ ↦ roundLaw) k)
  have hpastNoiseStream : ProbabilityTheory.IndepFun streamPrefix
      (noiseOfRound ∘ streamCurrent) streamLaw :=
    hpastCurrentStream.comp measurable_id hnoiseOfRound
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [prefixMap, noise, current, streamPrefix, streamCurrent, law,
      streamLaw, heterogeneousOnlinePathLaw, Function.comp_def] using
      indepFun_prod_left_adjoin_of_indepFun initialLaw streamLaw
        streamPrefix (noiseOfRound ∘ streamCurrent) hstreamPrefix
        (hnoiseOfRound.comp hstreamCurrent) hpastNoiseStream
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map (noiseOfRound ∘ streamCurrent)
          (Measure.map Prod.snd law) := by
            change Measure.map ((noiseOfRound ∘ streamCurrent) ∘ Prod.snd) law = _
            rw [MeasureTheory.Measure.map_map
              (hnoiseOfRound.comp hstreamCurrent) measurable_snd]
      _ = Measure.map (noiseOfRound ∘ streamCurrent) streamLaw := by
            rw [show Measure.map Prod.snd law = streamLaw by
              dsimp [law, streamLaw, heterogeneousOnlinePathLaw]
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = Measure.map noiseOfRound (Measure.map streamCurrent streamLaw) := by
            rw [MeasureTheory.Measure.map_map hnoiseOfRound hstreamCurrent]
      _ = Measure.map noiseOfRound roundLaw := by
            rw [show Measure.map streamCurrent streamLaw = roundLaw by
              simpa [streamCurrent, streamLaw] using
                SOptLib.iidStreamLaw_map_eval roundLaw k]
      _ = noiseLaw := by
            simpa [noiseOfRound, roundLaw, noiseLaw] using
              heterogeneousOnlineRoundLaw_differenceCompression_marginal
                (b := b) (b0 := b0) A
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  let xNext := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    primalStep A.stepSize (prefixState pref)
  let x := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (prefixState pref).x
  let kernel := fun
      (pref : HeterogeneousOnlineBatch n Sample b ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ))
      (q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0 q.1 i
            (xNext pref) (x pref))
          (q.2 i) -
        localGradientDifference P i (xNext pref) (x pref))
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let B := fun pref ↦ C * ‖xNext pref - x pref‖ ^ 2
  let phi := fun pref q ↦ ‖kernel pref q‖ ^ 2
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2)
      (path' := fun t ↦ if ht : t < k then path.2 t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 ℒlocal hKernel k
  have hprefixPoint (f : State d → Point d) (hf : Measurable f) :
      AEStronglyMeasurable (fun pref ↦ f (prefixState pref)) prefixLaw := by
    have hpath : AEStronglyMeasurable (fun path ↦ f (run k path)) law :=
      (hf.comp_aemeasurable hstate).aestronglyMeasurable
    have hcomp : AEStronglyMeasurable
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
          f (prefixState (path.1, fun j : Fin k ↦ path.2 j.1))) law := by
      refine hpath.congr (Filter.Eventually.of_forall ?_)
      intro path
      simpa [prefixMap] using congrArg f (hstatePrefix path).symm
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      initialLaw roundLaw k (fun pref ↦ f (prefixState pref)) (by
        simpa [law, initialLaw, streamLaw, roundLaw,
          heterogeneousOnlinePathLaw] using hcomp)
    rw [hprefixLaw]
    exact hfinite
  have hx : AEStronglyMeasurable x prefixLaw := by
    simpa [x] using hprefixPoint (fun s : State d ↦ s.x) (measurable_state_x d)
  have hxNext : AEStronglyMeasurable xNext prefixLaw := by
    simpa [xNext] using hprefixPoint (primalStep A.stepSize)
      (measurable_primalStep A.stepSize)
  have hkernel : AEStronglyMeasurable (Function.uncurry kernel)
      (prefixLaw.prod noiseLaw) := by
    rw [hprefixLaw]
    simpa [kernel, xNext, x, noiseLaw, P, prefixState, initialLaw, roundLaw]
      using
        heterogeneousOnlineExecutablePrefix_nonrefreshAverage_product_aestronglyMeasurable_of_generatedKernel
          A x0 ℒlocal hKernel fallback k
  have hphi : AEStronglyMeasurable (Function.uncurry phi)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    simpa [prefixLaw, phi, Function.uncurry, pow_two] using
      hkernel.norm.mul hkernel.norm
  have hB : AEStronglyMeasurable B (Measure.map prefixMap law) := by
    simpa [prefixLaw, B, pow_two] using
      ((hxNext.sub hx).norm.mul (hxNext.sub hx).norm).const_mul C
  have hMomentPath : ∀ᵐ path ∂law,
      Integrable (kernel (prefixMap path)) noiseLaw ∧
        (∫ q, kernel (prefixMap path) q ∂noiseLaw) = 0 ∧
        Integrable (phi (prefixMap path)) noiseLaw ∧
        (∫ q, phi (prefixMap path) q ∂noiseLaw) ≤ B (prefixMap path) := by
    have hm :=
      heterogeneousOnlineAssumption32GeneratedConditionalKernel_fixed_nonrefresh_average_moment_ae
        (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hKernel
          hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [kernel, noiseLaw, P, hnext, hcur] using hp.1
    · simpa [kernel, noiseLaw, P, hnext, hcur] using hp.2.1
    · simpa [phi, kernel, noiseLaw, P, hnext, hcur] using hp.2.2.1
    · simpa [phi, kernel, noiseLaw, B, C, P, hnext, hcur] using hp.2.2.2
  have hBComp : Integrable (fun path ↦ B (prefixMap path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    dsimp [B]
    rw [hnext, hcur]
  have htransfer :=
    integrable_comp_and_integral_le_of_indep_ae_fixed_fiber_aebound
      phi B prefixMap noise hphi hB hprefix.aemeasurable hnoise.aemeasurable
        hfresh hnoiseLaw
        (hMomentPath.mono fun path hp ↦ ⟨hp.2.2.1, hp.2.2.2⟩)
        (fun _ _ ↦ sq_nonneg _) hBComp
  have hinnovationEq : ∀ path,
      kernel (prefixMap path) (noise path) = innovation path := by
    intro path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    simp [kernel, noise, noiseOfRound, current, innovation, hnext, hcur]
  have hkernelMapped : AEStronglyMeasurable (Function.uncurry kernel)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    simpa [prefixLaw] using hkernel
  have hkernelComp : AEStronglyMeasurable
      (fun path ↦ kernel (prefixMap path) (noise path)) law :=
    aestronglyMeasurable_comp_of_indep_product_law
      hprefix.aemeasurable hnoise.aemeasurable
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law)) hfresh (by
        rw [hnoiseLaw]
        exact hkernelMapped)
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hkernelComp.congr (Filter.Eventually.of_forall hinnovationEq)
  have hinnovationSq : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law := by
    apply htransfer.1.congr
    filter_upwards [] with path
    change ‖kernel (prefixMap path) (noise path)‖ ^ 2 = ‖innovation path‖ ^ 2
    exact congrArg (fun z : Point d ↦ ‖z‖ ^ 2) (hinnovationEq path)
  have hinnovationInt : Integrable innovation law :=
    integrable_of_integrable_norm_sq hinnovationMeas hinnovationSq
  have hmeanComp :
      (∫ path, kernel (prefixMap path) (noise path) ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      kernel prefixMap noise hkernelMapped hprefix.aemeasurable
        hnoise.aemeasurable hfresh hnoiseLaw
    · exact hinnovationInt.congr
        (Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm)
    · exact hMomentPath.mono fun _ hp ↦ hp.2.1
  have hmean : (∫ path, innovation path ∂law) = 0 := by
    rw [show (∫ path, innovation path ∂law) =
        ∫ path, kernel (prefixMap path) (noise path) ∂law by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path ↦ (hinnovationEq path).symm]
    exact hmeanComp
  refine ⟨hinnovationInt, hmean, hinnovationSq, ?_⟩
  calc
    (∫ path, ‖innovation path‖ ^ 2 ∂law) =
        ∫ path, phi (prefixMap path) (noise path) ∂law := by
          apply integral_congr_ae
          filter_upwards [] with path
          change ‖innovation path‖ ^ 2 =
            ‖kernel (prefixMap path) (noise path)‖ ^ 2
          exact congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
            (hinnovationEq path).symm
    _ ≤ ∫ path, B (prefixMap path) ∂law := htransfer.2
    _ = C * stepMoment run law k := by
      unfold stepMoment
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with path
      have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
        dsimp [xNext]
        rw [hstatePrefix path]
        rfl
      have hcur : x (prefixMap path) = (run k path).x := by
        dsimp [x]
        rw [hstatePrefix path]
      dsimp [B]
      rw [hnext, hcur]
    _ = (1 / (n.1 : ℝ)) *
        (omega * (rootMeanSquare Llocal) ^ 2 +
          (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
        stepMoment run law k := by rfl

set_option maxHeartbeats 24000000 in
/- The generated heterogeneous Assumption 3.2 kernel also makes the carried
estimator residual orthogonal to the fresh executable nonrefresh innovation.
The conditioning variable is the actual sampled initializer together with the
strict round prefix, so the resulting Pythagorean bound uses the exact
worker-dependent Remark D.2 coefficient without any all-query regularity
premise. -/
theorem heterogeneousOnlineExecutable_nonrefresh_branch_moments_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      (run k path).g - globalGradient P (run k path).x
    let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0
              (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
            ((path.2 k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 ∧
      Integrable (fun path ↦ ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment P run law k +
          (1 / (n.1 : ℝ)) *
            (omega * (rootMeanSquare Llocal) ^ 2 +
              (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run law k := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.1, fun j : Fin k ↦ path.2 j.1)
  let prefixLaw := initialLaw.prod
    (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
  let streamPrefix := fun path :
      ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
    fun j : Fin k ↦ path j.1
  let streamCurrent := fun path :
      ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ path k
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let noiseOfRound := fun z :
      HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ (z.2.1.2, z.2.2)
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    noiseOfRound (current path)
  let noiseLaw := heterogeneousOnlineDifferenceCompressionLaw (b0 := b0) A
  let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let C := (1 / (n.1 : ℝ)) *
    (omega * (rootMeanSquare Llocal) ^ 2 +
      (1 + omega) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw heterogeneousOnlineDifferenceCompressionLaw
    infer_instance
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 ℒlocal hKernel k
  have hresidualMeas : AEStronglyMeasurable residual law := by
    exact (((measurable_state_g d).comp_aemeasurable hstate).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hstate))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hmoments :=
    heterogeneousOnlineExecutable_nonrefresh_innovation_moments_of_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hKernel
        hQuantizer k hStep
  have hinnovationInt : Integrable innovation law := by
    simpa [innovation, P, run, law] using hmoments.1
  have hinnovationMeas : AEStronglyMeasurable innovation law :=
    hinnovationInt.aestronglyMeasurable
  have hinnovationSqInt : Integrable
      (fun path ↦ ‖innovation path‖ ^ 2) law := by
    simpa [innovation, P, run, law] using hmoments.2.2.1
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  haveI : IsProbabilityMeasure prefixLaw := by
    unfold prefixLaw
    infer_instance
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixLaw, prefixMap, law, initialLaw, streamLaw, roundLaw,
      heterogeneousOnlinePathLaw] using hm.symm
  have hstreamPrefix : Measurable streamPrefix := by
    dsimp [streamPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hstreamCurrent : Measurable streamCurrent := measurable_pi_apply k
  haveI : IsProbabilityMeasure (Measure.map streamPrefix streamLaw) :=
    Measure.isProbabilityMeasure_map hstreamPrefix.aemeasurable
  have hnoiseOfRound : Measurable noiseOfRound := by
    dsimp [noiseOfRound]
    fun_prop
  have hnoise : Measurable noise := by
    dsimp [noise, current]
    exact hnoiseOfRound.comp (hstreamCurrent.comp measurable_snd)
  have hpastCurrentStream : ProbabilityTheory.IndepFun
      streamPrefix streamCurrent streamLaw := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (streamPrefix path, streamCurrent path))
      (P := streamLaw)
      (mu := Measure.map streamPrefix streamLaw) (nu := roundLaw)
    · exact (hstreamPrefix.prodMk hstreamCurrent).aemeasurable
    · simpa [streamLaw, streamPrefix, streamCurrent, roundLaw,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod (fun _ : ℕ ↦ roundLaw) k)
  have hpastNoiseStream : ProbabilityTheory.IndepFun streamPrefix
      (noiseOfRound ∘ streamCurrent) streamLaw :=
    hpastCurrentStream.comp measurable_id hnoiseOfRound
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [prefixMap, noise, current, streamPrefix, streamCurrent, law,
      streamLaw, heterogeneousOnlinePathLaw, Function.comp_def] using
      indepFun_prod_left_adjoin_of_indepFun initialLaw streamLaw
        streamPrefix (noiseOfRound ∘ streamCurrent) hstreamPrefix
        (hnoiseOfRound.comp hstreamCurrent) hpastNoiseStream
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map (noiseOfRound ∘ streamCurrent)
          (Measure.map Prod.snd law) := by
            change Measure.map ((noiseOfRound ∘ streamCurrent) ∘ Prod.snd) law = _
            rw [MeasureTheory.Measure.map_map
              (hnoiseOfRound.comp hstreamCurrent) measurable_snd]
      _ = Measure.map (noiseOfRound ∘ streamCurrent) streamLaw := by
            rw [show Measure.map Prod.snd law = streamLaw by
              dsimp [law, streamLaw, heterogeneousOnlinePathLaw]
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = Measure.map noiseOfRound (Measure.map streamCurrent streamLaw) := by
            rw [MeasureTheory.Measure.map_map hnoiseOfRound hstreamCurrent]
      _ = Measure.map noiseOfRound roundLaw := by
            rw [show Measure.map streamCurrent streamLaw = roundLaw by
              simpa [streamCurrent, streamLaw] using
                SOptLib.iidStreamLaw_map_eval roundLaw k]
      _ = noiseLaw := by
            simpa [noiseOfRound, roundLaw, noiseLaw] using
              heterogeneousOnlineRoundLaw_differenceCompression_marginal
                (b := b) (b0 := b0) A
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  let xNext := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    primalStep A.stepSize (prefixState pref)
  let x := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (prefixState pref).x
  let direction := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let kernel := fun
      (pref : HeterogeneousOnlineBatch n Sample b ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ))
      (q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0 q.1 i
            (xNext pref) (x pref))
          (q.2 i) -
        localGradientDifference P i (xNext pref) (x pref))
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2)
      (path' := fun t ↦ if ht : t < k then path.2 t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hkernel : AEStronglyMeasurable (Function.uncurry kernel)
      (prefixLaw.prod noiseLaw) := by
    simpa [kernel, xNext, x, noiseLaw, P, prefixState, initialLaw, roundLaw]
      using
        heterogeneousOnlineExecutablePrefix_nonrefreshAverage_product_aestronglyMeasurable_of_generatedKernel
          A x0 ℒlocal hKernel fallback k
  have hinnovationEq : ∀ path,
      kernel (prefixMap path) (noise path) = innovation path := by
    intro path
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    simp [kernel, noise, noiseOfRound, current, innovation, hnext, hcur]
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    have hcomp : AEStronglyMeasurable
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
          direction (path.1, fun j : Fin k ↦ path.2 j.1)) law := by
      refine hresidualMeas.congr (Filter.Eventually.of_forall ?_)
      intro path
      dsimp [direction, residual]
      rw [hstatePrefix path]
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      initialLaw roundLaw k direction (by
        simpa [law, initialLaw, streamLaw, roundLaw,
          heterogeneousOnlinePathLaw] using hcomp)
    exact hfinite
  have hscalar : AEStronglyMeasurable
      (fun p ↦ ⟪direction p.1, kernel p.1 p.2⟫_ℝ)
      ((Measure.map prefixMap law).prod noiseLaw) := by
    rw [hprefixLaw]
    exact hdirection.comp_fst.inner hkernel
  have hinnerInt : Integrable
      (fun path ↦ ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq hinnovationSqInt
  have hscalarCompInt : Integrable
      (fun path ↦
        ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ)
      law := by
    apply hinnerInt.congr
    filter_upwards [] with path
    rw [hinnovationEq path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hfixedScalar : ∀ᵐ path ∂law,
      (∫ q, ⟪direction (prefixMap path), kernel (prefixMap path) q⟫_ℝ
        ∂noiseLaw) = 0 := by
    have hm :=
      heterogeneousOnlineAssumption32GeneratedConditionalKernel_fixed_nonrefresh_average_moment_ae
        (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hKernel
          hQuantizer k
    filter_upwards [hm] with path hp
    dsimp only at hp
    have hnext : xNext (prefixMap path) = (run (k + 1) path).x := by
      dsimp [xNext]
      rw [hstatePrefix path]
      rfl
    have hcur : x (prefixMap path) = (run k path).x := by
      dsimp [x]
      rw [hstatePrefix path]
    have hfiberInt : Integrable (kernel (prefixMap path)) noiseLaw := by
      simpa [kernel, noiseLaw, P, hnext, hcur] using hp.1
    have hfiberZero :
        (∫ q, kernel (prefixMap path) q ∂noiseLaw) = 0 := by
      simpa [kernel, noiseLaw, P, hnext, hcur] using hp.2.1
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction (prefixMap path))) hfiberInt
    calc
      (∫ q, ⟪direction (prefixMap path), kernel (prefixMap path) q⟫_ℝ
          ∂noiseLaw) =
          (innerSL ℝ) (direction (prefixMap path))
            (∫ q, kernel (prefixMap path) q ∂noiseLaw) := hlin
      _ = 0 := by rw [hfiberZero]; simp
  have hcrossComp :
      (∫ path,
        ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ
        ∂law) = 0 := by
    apply integral_comp_eq_zero_of_indep_ae_fixed_integral_zero
      (fun pref q ↦ ⟪direction pref, kernel pref q⟫_ℝ)
      prefixMap noise hscalar hprefix.aemeasurable hnoise.aemeasurable
        hfresh hnoiseLaw hscalarCompInt hfixedScalar
  have hcross :
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
        ∫ path,
          ⟪direction (prefixMap path), kernel (prefixMap path) (noise path)⟫_ℝ
          ∂law by
      apply integral_congr_ae
      filter_upwards [] with path
      rw [hinnovationEq path]
      dsimp [direction, residual]
      rw [hstatePrefix path]]
    exact hcrossComp
  have hnonrefreshInt : Integrable
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresidualMeas hinnovationMeas
      hresidualSq hinnovationSqInt
  have hnonrefreshEq :
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          ∫ path, ‖innovation path‖ ^ 2 ∂law := by
    let pair : Bool → (HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) → Point d :=
      fun z ↦ if z then innovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      law (Finset.univ : Finset Bool) pair
      (fun z _ ↦ by cases z <;> simp [pair, hresidualMeas, hinnovationMeas])
      (fun z _ ↦ by cases z <;> simp [pair, hresidualSq, hinnovationSqInt])
      (fun z _ w _ hzw ↦ by
        cases z <;> cases w
        · exact False.elim (hzw rfl)
        · simpa [pair] using hcross
        · simpa [pair, real_inner_comm] using hcross
        · exact False.elim (hzw rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  refine ⟨hcross, hnonrefreshInt, ?_⟩
  rw [hnonrefreshEq]
  change estimatorErrorMoment P run law k +
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
    estimatorErrorMoment P run law k + C * stepMoment run law k
  exact add_le_add_right (by
    simpa [innovation, P, run, law, C] using hmoments.2.2.2) _

set_option maxHeartbeats 3000000 in
/-- The generated heterogeneous process query and an independent
worker-dependent refresh minibatch form the exact product-law random variable
used by the executable refresh branch.  Joint measurability is obtained from
the process-specific Assumption 3.2/3.3 supplier, without an all-query
regularity premise. -/
theorem
    heterogeneousOnlineProcess_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (Lcal sigma : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (k : ℕ) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let batchLaw := heterogeneousOnlineBatchLaw A.problem b
    AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i (p.2 i j)
              (run (k + 1) p.1).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (run (k + 1) p.1).x‖ ^ 2)
      (law.prod batchLaw) := by
  classical
  dsimp only
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hquery : AEStronglyMeasurable
      (fun path ↦ (run (k + 1) path).x) law := by
    have hpair := hKernel.2.1 (k + 1)
    exact (measurable_fst.comp_aemeasurable
      hpair.aemeasurable).aestronglyMeasurable
  have hcoord (i : Worker n) (j : Fin (b i).1) :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j)
          batchLaw = A.problem.sampleLaw i := by
    calc
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j)
          batchLaw =
          Measure.map (fun row : Fin (b i).1 → Sample i ↦ row j)
            (Measure.map
              (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i)
              batchLaw) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · fun_prop
      _ = Measure.map (fun row : Fin (b i).1 → Sample i ↦ row j)
          (Measure.infinitePi
            (fun _ : Fin (b i).1 ↦ A.problem.sampleLaw i)) := by
              rw [heterogeneous_online_batch_law_worker_marginal]
      _ = A.problem.sampleLaw i := by
              simpa using
                (MeasureTheory.Measure.infinitePi_map_eval
                  (μ := fun _ : Fin (b i).1 ↦ A.problem.sampleLaw i) j)
  have hgrad (i : Worker n) (j : Fin (b i).1) : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b) ↦
        stochasticGradient A.problem i (p.2 i j) (run (k + 1) p.1).x)
      (law.prod batchLaw) := by
    have hsingle :=
      (heterogeneousOnlineProcess_adaptiveGradient_source_regular
        A x0 Lcal sigma hKernel hLiteral (k + 1) i).2
    have hcoordinate : MeasurePreserving
        (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j)
        batchLaw (A.problem.sampleLaw i) :=
      ⟨(by fun_prop), hcoord i j⟩
    have hpull := hsingle.comp_measurePreserving
      ((MeasurePreserving.id law).prod hcoordinate)
    simpa [run, law, batchLaw, Function.comp_def] using hpull
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b) ↦
        average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i (p.2 i j) (run (k + 1) p.1).x))
      (law.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ hgrad i j)).const_smul
        ((Fintype.card (Fin (b i).1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  have havg : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b) ↦
        average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i (p.2 i j)
            (run (k + 1) p.1).x)))
      (law.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ ↦ hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]
  have hglobal : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b) ↦
        globalGradient (onlineLocalProblem A.problem)
          (run (k + 1) p.1).x)
      (law.prod batchLaw) :=
    ((measurable_gradient
      (globalObjective (onlineLocalProblem A.problem))).comp_aemeasurable
        hquery.aemeasurable).aestronglyMeasurable.comp_fst
  have hresidual := havg.sub hglobal
  simpa [run, law, batchLaw, pow_two] using
    hresidual.norm.mul hresidual.norm

set_option maxHeartbeats 3000000 in
/-- The heterogeneous executable refresh square remains measurable after the
unused iid tail is discarded.  The retained carrier is the worker-dependent
initializer and strict round prefix, while the second coordinate is an
independent worker-dependent refresh minibatch. -/
theorem
    heterogeneousOnlineExecutablePrefix_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (Lcal sigma : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) (k : ℕ) :
    let initialLaw := heterogeneousOnlineBatchLaw A.problem b
    let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := initialLaw.prod
      (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
    let batchLaw := heterogeneousOnlineBatchLaw A.problem b
    let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
      heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k
        (pref.1, fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
    AEStronglyMeasurable
      (fun p :
          (HeterogeneousOnlineBatch n Sample b ×
              (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i (p.2 i j)
              (primalStep A.stepSize (prefixState p.1)))) -
          globalGradient (onlineLocalProblem A.problem)
            (primalStep A.stepSize (prefixState p.1))‖ ^ 2)
      (prefixLaw.prod batchLaw) := by
  classical
  dsimp only
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hfull : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i (p.2 i j)
              (run (k + 1) p.1).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (run (k + 1) p.1).x‖ ^ 2)
      (law.prod batchLaw) := by
    simpa [run, law, initialLaw, streamLaw, batchLaw,
      heterogeneousOnlinePathLaw] using
      heterogeneousOnlineProcess_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
        A x0 Lcal sigma hKernel hLiteral k
  have hreorder : MeasurePreserving
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              HeterogeneousOnlineBatch n Sample b) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod batchLaw).prod streamLaw)
      ((initialLaw.prod streamLaw).prod batchLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw batchLaw streamLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := batchLaw) (ν := streamLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw streamLaw batchLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hstream : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              HeterogeneousOnlineBatch n Sample b) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i (p.1.2 i j)
              (run (k + 1) (p.1.1, p.2)).x)) -
          globalGradient (onlineLocalProblem A.problem)
            (run (k + 1) (p.1.1, p.2)).x‖ ^ 2)
      ((initialLaw.prod batchLaw).prod streamLaw) := by
    simpa [Function.comp_def] using hfull.comp_measurePreserving hreorder
  let F := fun p :
      (HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b) ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
        stochasticGradient A.problem i (p.1.2 i j)
          (primalStep A.stepSize (prefixState (p.1.1, p.2))))) -
      globalGradient (onlineLocalProblem A.problem)
        (primalStep A.stepSize (prefixState (p.1.1, p.2)))‖ ^ 2
  have hstatePrefix : ∀ initial stream,
      prefixState (initial, fun j : Fin k ↦ stream j.1) =
        run k (initial, stream) := by
    intro initial stream
    dsimp [prefixState, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k initial
      (path := stream)
      (path' := fun t ↦ if ht : t < k then stream t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hstreamF : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              HeterogeneousOnlineBatch n Sample b) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        F (p.1, fun j : Fin k ↦ p.2 j.1))
      ((initialLaw.prod batchLaw).prod streamLaw) := by
    refine hstream.congr (Filter.Eventually.of_forall ?_)
    intro p
    dsimp [F]
    rw [hstatePrefix p.1.1 p.2]
    rfl
  have hfinite : AEStronglyMeasurable F
      ((initialLaw.prod batchLaw).prod prefixStreamLaw) := by
    simpa [prefixStreamLaw] using
      aestronglyMeasurable_initial_prefix_of_comp_general
        (initialLaw.prod batchLaw) roundLaw k F hstreamF
  have hreorderFinite : MeasurePreserving
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod prefixStreamLaw).prod batchLaw)
      ((initialLaw.prod batchLaw).prod prefixStreamLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw prefixStreamLaw batchLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixStreamLaw) (ν := batchLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw batchLaw prefixStreamLaw).symm
    have h := h3.comp (h2.comp h1)
    simpa [Function.comp_def] using h
  have hresult := hfinite.comp_measurePreserving hreorderFinite
  simpa [F, prefixLaw, prefixStreamLaw, prefixState, initialLaw, roundLaw,
    batchLaw, Function.comp_def] using hresult

set_option maxHeartbeats 3000000 in
/-- The actual heterogeneous executable refresh error is integrable and has
the worker-dependent Remark D.2 variance bound.  The proof uses only the
generated Assumption 3.2 kernel and literal fixed-query Assumption 3.3; it
does not require all-query adaptive-gradient regularity. -/
theorem
    heterogeneousOnlineExecutable_refresh_error_integrable_and_expectation_le_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (ℒ sigma : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i))
    (k : ℕ) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path :
        HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    Integrable refreshErrorSq law ∧
      (∫ path, refreshErrorSq path ∂law) ≤
        heterogeneousOnlineVarianceTerm sigma b := by
  classical
  dsimp only
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.1, fun j : Fin k ↦ path.2 j.1)
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.2 k).2.1.1
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixMap, prefixLaw, prefixStreamLaw, law] using hm.symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (Measure.map Prod.snd law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_pi_apply k
              · exact measurable_snd
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) streamLaw := by
              rw [show Measure.map Prod.snd law = streamLaw by
                dsimp [law]
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := by
        simpa [streamLaw] using SOptLib.iidStreamLaw_map_eval roundLaw k
  have hjoint : Measure.map (fun path ↦ (prefixMap path, current path)) law =
      prefixLaw.prod roundLaw := by
    let streamJoint := fun stream :
        ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
      ((fun j : Fin k ↦ stream j.1), stream k)
    have hstreamJoint : MeasurePreserving streamJoint streamLaw
        (prefixStreamLaw.prod roundLaw) := by
      refine ⟨(by
        dsimp [streamJoint]
        exact (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).prodMk
          (measurable_pi_apply k)), ?_⟩
      have hprefixStream : Measure.map
          (fun stream :
              ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            fun j : Fin k ↦ stream j.1) streamLaw = prefixStreamLaw := by
        simpa [streamLaw, prefixStreamLaw] using
          iidStream_prefix_map_eq_infinitePi roundLaw k
      have hj := infinitePi_prefix_current_map_eq_prod
        (fun _ : ℕ ↦ roundLaw) k
      have hprefixRaw : Measure.map
          (fun stream :
              ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            fun j : Fin k ↦ stream j.1)
          (Measure.infinitePi (fun _ : ℕ ↦ roundLaw)) =
            prefixStreamLaw := by
        simpa [streamLaw] using hprefixStream
      rw [hprefixRaw] at hj
      simpa [streamJoint, streamLaw] using hj
    have h0 := (MeasurePreserving.id initialLaw).prod hstreamJoint
    have h1 :=
      (measurePreserving_prodAssoc initialLaw prefixStreamLaw roundLaw).symm
    have h := h1.comp h0
    simpa [law, prefixLaw, prefixStreamLaw, prefixMap, current,
      streamJoint, Function.comp_def] using h.map_eq
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · exact hjoint
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law := by
    have h := hpastCurrent.comp measurable_id
      (show Measurable
        (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.2.1.1) by
          fun_prop)
    simpa [batch, current, Function.comp_def] using h
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.2.1.1)
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.2.1.1)
          roundLaw := by rw [hcurrentLaw]
      _ = batchLaw := by
        let differenceLaw := heterogeneousOnlineBatchLaw A.problem b0
        let compressionLaw := workerCompressionLaw (n := n) A.quantizer
        let restLaw := (batchLaw.prod differenceLaw).prod compressionLaw
        calc
          Measure.map
              (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
                z.2.1.1) roundLaw =
              Measure.map (fun z :
                  (HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                    z.1.1) (Measure.map Prod.snd roundLaw) := by
                rw [Measure.map_map]
                · rfl
                · fun_prop
                · exact measurable_snd
          _ = Measure.map (fun z :
                  (HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                    z.1.1) restLaw := by
                rw [show Measure.map Prod.snd roundLaw = restLaw by
                  dsimp [roundLaw, restLaw, differenceLaw, compressionLaw,
                    batchLaw]
                  unfold heterogeneousOnlineRoundLaw
                  rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = Measure.map Prod.fst (batchLaw.prod differenceLaw) := by
                rw [show (fun z :
                    (HeterogeneousOnlineBatch n Sample b ×
                      HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                      z.1.1) = Prod.fst ∘ Prod.fst by rfl,
                  ← Measure.map_map measurable_fst measurable_fst,
                  Measure.map_fst_prod, measure_univ, one_smul]
          _ = batchLaw := by
                rw [Measure.map_fst_prod, measure_univ, one_smul]
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  let F := fun (pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ))
      (fresh : HeterogeneousOnlineBatch n Sample b) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
        stochasticGradient A.problem i (fresh i j)
          (primalStep A.stepSize (prefixState pref)))) -
      globalGradient (onlineLocalProblem A.problem)
        (primalStep A.stepSize (prefixState pref))‖ ^ 2
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod batchLaw) := by
    simpa [F, prefixState, prefixLaw, prefixStreamLaw, initialLaw,
      roundLaw, batchLaw] using
      heterogeneousOnlineExecutablePrefix_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
        A x0 ℒ sigma hKernel hLiteral fallback k
  have hFmap : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.map prefixMap law).prod batchLaw) := by
    rw [hprefixLaw]
    exact hF
  have hfixed (pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) :
      Integrable (F pref) batchLaw ∧
        (∫ fresh, F pref fresh ∂batchLaw) ≤
          heterogeneousOnlineVarianceTerm sigma b := by
    simpa [F, batchLaw] using
      (heterogeneousOnline_fixed_refresh_average_second_moment_of_literal
        (b := b) A (primalStep A.stepSize (prefixState pref))
          sigma hLiteral hDiff)
  have hcomp : Integrable
      (fun path ↦ F (prefixMap path) (batch path)) law :=
    integrable_comp_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := prefixMap) (Y := batch)
      (C := heterogeneousOnlineVarianceTerm sigma b) hFmap
      hprefix.aemeasurable hbatch.aemeasurable hprefixBatch hbatchLaw
      (fun _ _ ↦ sq_nonneg _) (fun pref ↦ (hfixed pref).1)
      (fun pref ↦ (hfixed pref).2)
  have hbound : (∫ path, F (prefixMap path) (batch path) ∂law) ≤
      heterogeneousOnlineVarianceTerm sigma b :=
    integral_comp_le_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := batchLaw) (X := prefixMap) (Y := batch)
      hFmap hprefix.aemeasurable hbatch.aemeasurable hprefixBatch hbatchLaw
      hcomp (fun pref ↦ (hfixed pref).2)
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2)
      (path' := fun t ↦ if ht : t < k then path.2 t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hcalc : ∀ path, F (prefixMap path) (batch path) =
      ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem)
          (run (k + 1) path).x‖ ^ 2 := by
    intro path
    dsimp [F, batch]
    rw [hstatePrefix path]
    rfl
  constructor
  · exact hcomp.congr (Filter.Eventually.of_forall hcalc)
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hcalc)]
    exact hbound

set_option maxHeartbeats 3000000 in
/-- The actual heterogeneous executable refresh-error square is independent
of the same-round Bernoulli refresh coin under the generated Assumption 3.2
kernel.  The strict-prefix state and the refresh minibatch are adjoined before
taking the measurable representative, so the conclusion concerns the exact
Algorithm 3 observable and uses no all-query regularity premise. -/
theorem
    heterogeneousOnlineExecutable_refresh_error_sq_indep_refresh_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d)
    (Lcal sigma : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (k : ℕ) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let refreshErrorSq := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
      ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (run (k + 1) path).x)) -
        globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
    ProbabilityTheory.IndepFun refreshErrorSq
      (fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
          (path.2 k).1) law := by
  classical
  dsimp only
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let refreshBatchLaw := heterogeneousOnlineBatchLaw A.problem b
  let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let roundLaw := coinLaw.prod restLaw
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (path.1, fun j : Fin k ↦ path.2 j.1)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦ path.2 k
  let restPath := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (current path).2
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (current path).2.1.1
  let branch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (current path).1
  let joined := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (prefixMap path, restPath path)
  let carrier := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (prefixMap path, batch path)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure refreshBatchLaw := by
    unfold refreshBatchLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw heterogeneousOnlineBatchLaw
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
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi :=
    fun _ ↦ Classical.choice
      (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  let F := fun p :
      (HeterogeneousOnlineBatch n Sample b ×
          (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
        HeterogeneousOnlineBatch n Sample b ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
        stochasticGradient A.problem i (p.2 i j)
          (primalStep A.stepSize (prefixState p.1)))) -
      globalGradient (onlineLocalProblem A.problem)
        (primalStep A.stepSize (prefixState p.1))‖ ^ 2
  let refreshErrorSq := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
        stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
          (run (k + 1) path).x)) -
      globalGradient (onlineLocalProblem A.problem) (run (k + 1) path).x‖ ^ 2
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  have hrestPath : Measurable restPath := by
    dsimp [restPath]
    exact measurable_snd.comp hcurrent
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hbranch : Measurable branch := by
    dsimp [branch]
    exact measurable_fst.comp hcurrent
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixMap, prefixLaw, prefixStreamLaw, law] using hm.symm
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
            stream k) (Measure.map Prod.snd law) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact measurable_pi_apply k
              · exact measurable_snd
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
            stream k) streamLaw := by
              rw [show Measure.map Prod.snd law = streamLaw by
                dsimp [law]
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := by
        simpa [streamLaw] using SOptLib.iidStreamLaw_map_eval roundLaw k
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · let streamJoint := fun stream :
          ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
        ((fun j : Fin k ↦ stream j.1), stream k)
      have hstreamJoint : MeasurePreserving streamJoint streamLaw
          (prefixStreamLaw.prod roundLaw) := by
        refine ⟨(by
          dsimp [streamJoint]
          exact (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).prodMk
            (measurable_pi_apply k)), ?_⟩
        have hj := infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ roundLaw) k
        have hprefixStream : Measure.map
            (fun stream :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
              fun j : Fin k ↦ stream j.1) streamLaw = prefixStreamLaw := by
          simpa [streamLaw, prefixStreamLaw] using
            iidStream_prefix_map_eq_infinitePi roundLaw k
        have hprefixRaw : Measure.map
            (fun stream :
                ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
              fun j : Fin k ↦ stream j.1)
            (Measure.infinitePi (fun _ : ℕ ↦ roundLaw)) =
              prefixStreamLaw := by
          simpa [streamLaw] using hprefixStream
        rw [hprefixRaw] at hj
        simpa [streamJoint, streamLaw] using hj
      have h0 := (MeasurePreserving.id initialLaw).prod hstreamJoint
      have h1 :=
        (measurePreserving_prodAssoc initialLaw prefixStreamLaw roundLaw).symm
      have h := h1.comp h0
      simpa [law, prefixLaw, prefixStreamLaw, prefixMap, current,
        streamJoint, Function.comp_def] using h.map_eq
  have hpastPair : ProbabilityTheory.IndepFun prefixMap
      (fun path ↦ (restPath path, branch path)) law := by
    simpa [restPath, branch, current, Function.comp_def] using
      hpastCurrent.comp measurable_id (measurable_snd.prodMk measurable_fst)
  have hpairLaw : Measure.map
      (fun path ↦ (restPath path, branch path)) law =
        restLaw.prod coinLaw := by
    calc
      Measure.map (fun path ↦ (restPath path, branch path)) law =
          Measure.map Prod.swap (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map measurable_swap hcurrent]
            rfl
      _ = Measure.map Prod.swap roundLaw := by rw [hcurrentLaw]
      _ = Measure.map Prod.swap (coinLaw.prod restLaw) := by rfl
      _ = restLaw.prod coinLaw := MeasureTheory.Measure.prod_swap
  have hjoinedBranch : ProbabilityTheory.IndepFun joined branch law := by
    simpa [joined] using
      indepFun_left_adjoin_fst_of_indepFun_pair law restLaw coinLaw
        prefixMap restPath branch hprefix hrestPath hbranch hpastPair hpairLaw
  have hcarrierBranch : ProbabilityTheory.IndepFun carrier branch law := by
    have h := hjoinedBranch.comp
      (show Measurable
        (fun z :
            (HeterogeneousOnlineBatch n Sample b ×
                (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
              ((HeterogeneousOnlineBatch n Sample b ×
                HeterogeneousOnlineBatch n Sample b0) × (Worker n → Xi)) ↦
          (z.1, z.2.1.1)) by fun_prop)
      measurable_id
    simpa [carrier, joined, batch, restPath, current, Function.comp_def] using h
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law := by
    have h := hpastCurrent.comp measurable_id
      (show Measurable
        (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
          z.2.1.1) by fun_prop)
    simpa [batch, current, Function.comp_def] using h
  have hbatchLaw : Measure.map batch law = refreshBatchLaw := by
    calc
      Measure.map batch law = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦ z.2.1.1)
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦ z.2.1.1)
          roundLaw := by rw [hcurrentLaw]
      _ = refreshBatchLaw := by
        calc
          Measure.map
              (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
                z.2.1.1) roundLaw =
              Measure.map
                (fun z : ((HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Xi)) ↦
                  z.1.1) restLaw := by
                    calc
                      Measure.map
                          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Xi ↦
                            z.2.1.1) roundLaw =
                          Measure.map
                            (fun z : ((HeterogeneousOnlineBatch n Sample b ×
                                HeterogeneousOnlineBatch n Sample b0) ×
                              (Worker n → Xi)) ↦ z.1.1)
                            (Measure.map Prod.snd roundLaw) := by
                              rw [MeasureTheory.Measure.map_map]
                              · rfl
                              · fun_prop
                              · exact measurable_snd
                      _ = Measure.map
                            (fun z : ((HeterogeneousOnlineBatch n Sample b ×
                                HeterogeneousOnlineBatch n Sample b0) ×
                              (Worker n → Xi)) ↦ z.1.1) restLaw := by
                              rw [show Measure.map Prod.snd roundLaw = restLaw by
                                dsimp [roundLaw]
                                rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = Measure.map Prod.fst
              (refreshBatchLaw.prod differenceBatchLaw) := by
                rw [show (fun z : ((HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Xi)) ↦
                    z.1.1) = Prod.fst ∘ Prod.fst by rfl,
                  ← Measure.map_map measurable_fst measurable_fst,
                  Measure.map_fst_prod, measure_univ, one_smul]
          _ = refreshBatchLaw := by
                rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hcarrierLaw : Measure.map carrier law =
      prefixLaw.prod refreshBatchLaw := by
    calc
      Measure.map carrier law =
          (Measure.map prefixMap law).prod (Measure.map batch law) := by
            simpa [carrier] using
              (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
                hprefix.aemeasurable hbatch.aemeasurable).1 hprefixBatch
      _ = prefixLaw.prod refreshBatchLaw := by
            rw [hprefixLaw, hbatchLaw]
  have hF : AEStronglyMeasurable F
      (prefixLaw.prod refreshBatchLaw) := by
    simpa [F, prefixState, prefixLaw, prefixStreamLaw, initialLaw,
      roundLaw, refreshBatchLaw] using
      heterogeneousOnlineExecutablePrefix_refreshErrorSq_product_aestronglyMeasurable_of_generatedKernel
        A x0 Lcal sigma hKernel hLiteral fallback k
  let F' := hF.mk F
  have hcarrier : Measurable carrier := hprefix.prodMk hbatch
  have hqmp : Measure.QuasiMeasurePreserving carrier law
      (prefixLaw.prod refreshBatchLaw) :=
    ⟨hcarrier, by rw [hcarrierLaw]⟩
  have hmk : (fun path ↦ F (carrier path)) =ᵐ[law]
      (fun path ↦ F' (carrier path)) :=
    hqmp.tendsto_ae hF.ae_eq_mk
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2)
      (path' := fun t ↦ if ht : t < k then path.2 t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hcalc : ∀ path, F (carrier path) = refreshErrorSq path := by
    intro path
    dsimp [F, carrier, batch, current, refreshErrorSq]
    rw [hstatePrefix path]
    rfl
  have hcomp : (fun path ↦ F' (carrier path)) =ᵐ[law]
      refreshErrorSq := by
    filter_upwards [hmk] with path hp
    rw [← hp, hcalc path]
  have hindep : ProbabilityTheory.IndepFun
      (fun path ↦ F' (carrier path)) branch law := by
    simpa only [Function.comp_apply] using
      hcarrierBranch.comp hF.measurable_mk measurable_id
  apply hindep.congr hcomp
    (Filter.Eventually.of_forall fun _ ↦ rfl)

set_option maxHeartbeats 3000000 in
/-- The complete heterogeneous executable nonrefresh residual square is
independent of its same-round refresh coin using only the generated
Assumption 3.2 kernel.  The worker-dependent sampled initializer and strict
round prefix form the past carrier, while the current difference batches and
compressors form the fresh nonrefresh coordinate.  No all-query
sample-gradient regularity is used. -/
theorem
    heterogeneousOnlineExecutable_nonrefresh_error_sq_indep_refresh_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d) (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
      (run k path).g - globalGradient P (run k path).x
    let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
      average (fun i : Worker n ↦
        A.quantizer.apply
            (heterogeneousOnlineBatchDifference A.problem b0
              (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
            ((path.2 k).2.2 i) -
          localGradientDifference P i
            (run (k + 1) path).x (run k path).x)
    ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2)
      (fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
          (path.2 k).1) law := by
  classical
  dsimp only
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let refreshBatchLaw := heterogeneousOnlineBatchLaw A.problem b
  let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let compressionLaw := workerCompressionLaw (n := n) A.quantizer
  let noiseLaw := differenceBatchLaw.prod compressionLaw
  let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod compressionLaw
  let roundLaw := coinLaw.prod restLaw
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (path.1, fun j : Fin k ↦ path.2 j.1)
  let prefixLaw := Measure.map prefixMap law
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure refreshBatchLaw := by
    unfold refreshBatchLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure compressionLaw := by
    unfold compressionLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw
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
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  let x := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (prefixState pref).x
  let xNext := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    primalStep A.stepSize (prefixState pref)
  let direction := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let innovationKernel := fun
      (pref : HeterogeneousOnlineBatch n Sample b ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi))
      (q : HeterogeneousOnlineBatch n Sample b0 × (Worker n → Xi)) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0 q.1 i
            (xNext pref) (x pref))
          (q.2 i) -
        localGradientDifference P i (xNext pref) (x pref))
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, prefixMap, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2)
      (path' := fun t ↦ if ht : t < k then path.2 t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hstate : AEMeasurable (run k) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_generatedConditionalKernel
        A x0 Lcal hKernel k
  have hprefixLaw : prefixLaw =
      initialLaw.prod (Measure.infinitePi (fun _ : Fin k ↦ roundLaw)) := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw
      (SOptLib.iidStreamLaw roundLaw) measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixLaw, prefixMap, law, initialLaw, roundLaw, coinLaw, restLaw,
      refreshBatchLaw, differenceBatchLaw, compressionLaw,
      heterogeneousOnlinePathLaw, heterogeneousOnlineRoundLaw] using hm.symm
  have hprefixPoint (f : State d → Point d) (hf : Measurable f) :
      AEStronglyMeasurable (fun pref ↦ f (prefixState pref)) prefixLaw := by
    have hpath : AEStronglyMeasurable (fun path ↦ f (run k path)) law :=
      (hf.comp_aemeasurable hstate).aestronglyMeasurable
    have hcomp : AEStronglyMeasurable
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
          f (prefixState (path.1, fun j : Fin k ↦ path.2 j.1))) law := by
      refine hpath.congr (Filter.Eventually.of_forall ?_)
      intro path
      simpa [prefixMap] using congrArg f (hstatePrefix path).symm
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      initialLaw roundLaw k (fun pref ↦ f (prefixState pref)) (by
        simpa [law, initialLaw, roundLaw, coinLaw, restLaw, refreshBatchLaw,
          differenceBatchLaw, compressionLaw, heterogeneousOnlinePathLaw,
          heterogeneousOnlineRoundLaw] using hcomp)
    rw [hprefixLaw]
    exact hfinite
  have hx : AEStronglyMeasurable x prefixLaw := by
    simpa [x] using hprefixPoint (fun s : State d ↦ s.x) (measurable_state_x d)
  have hxNext : AEStronglyMeasurable xNext prefixLaw := by
    simpa [xNext] using hprefixPoint (primalStep A.stepSize)
      (measurable_primalStep A.stepSize)
  have hg : AEStronglyMeasurable (fun pref ↦ (prefixState pref).g)
      prefixLaw :=
    hprefixPoint (fun s : State d ↦ s.g) (measurable_state_g d)
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    exact hg.sub ((measurable_gradient (globalObjective P)).comp_aemeasurable
      hx.aemeasurable).aestronglyMeasurable
  have hinnovationKernel : AEStronglyMeasurable
      (fun p ↦ innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
    rw [hprefixLaw]
    simpa [innovationKernel, xNext, x, noiseLaw, differenceBatchLaw,
      compressionLaw, heterogeneousOnlineDifferenceCompressionLaw, P,
      prefixState, initialLaw, roundLaw, coinLaw, restLaw, refreshBatchLaw,
      heterogeneousOnlineRoundLaw] using
        heterogeneousOnlineExecutablePrefix_nonrefreshAverage_product_aestronglyMeasurable_of_generatedKernel
          A x0 Lcal hKernel fallback k
  let nonrefreshKernelRest := fun
      (pref : HeterogeneousOnlineBatch n Sample b ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi))
      (r : (HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Xi)) ↦
    ‖direction pref + innovationKernel pref (r.1.2, r.2)‖ ^ 2
  have hNonrefreshKernelRest : AEStronglyMeasurable
      (Function.uncurry nonrefreshKernelRest) (prefixLaw.prod restLaw) := by
    let pull := fun p :
        (HeterogeneousOnlineBatch n Sample b ×
          (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
          ((HeterogeneousOnlineBatch n Sample b ×
            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Xi)) ↦
      (p.1, (p.2.1.2, p.2.2))
    have hpull : Measurable pull := by
      dsimp [pull]
      fun_prop
    have hproject : Measure.map
        (fun r : (HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Xi) ↦
          (r.1.2, r.2)) restLaw = noiseLaw := by
      dsimp [restLaw, noiseLaw]
      simpa using (MeasureTheory.Measure.map_prod_map
        (refreshBatchLaw.prod differenceBatchLaw) compressionLaw
        measurable_snd measurable_id).symm
    have hpullLaw : Measure.map pull (prefixLaw.prod restLaw) =
        prefixLaw.prod noiseLaw := by
      have hm := MeasureTheory.Measure.map_prod_map prefixLaw restLaw
        measurable_id
        (show Measurable
          (fun r : (HeterogeneousOnlineBatch n Sample b ×
            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Xi) ↦
              (r.1.2, r.2)) by fun_prop)
      rw [Measure.map_id, hproject] at hm
      simpa [pull] using hm.symm
    have hbase : AEStronglyMeasurable
        (fun p ↦ ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
        (prefixLaw.prod noiseLaw) := by
      have hv := hdirection.comp_fst.add hinnovationKernel
      simpa [pow_two] using hv.norm.mul hv.norm
    have hqmp : Measure.QuasiMeasurePreserving pull
        (prefixLaw.prod restLaw) (prefixLaw.prod noiseLaw) :=
      ⟨hpull, by rw [hpullLaw]⟩
    simpa [nonrefreshKernelRest, Function.uncurry, pull] using
      hbase.comp_quasiMeasurePreserving hqmp
  have hindep := initial_iidStream_prefix_current_snd_kernel_indep_fst
    initialLaw coinLaw restLaw k nonrefreshKernelRest (by
      rw [← hprefixLaw]
      exact hNonrefreshKernelRest)
  apply hindep.congr (Filter.Eventually.of_forall ?_)
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  intro path
  change nonrefreshKernelRest (prefixMap path) (path.2 k).2 = _
  dsimp [nonrefreshKernelRest, direction, innovationKernel, xNext, x]
  rw [hstatePrefix path]
  rfl

set_option maxHeartbeats 3000000 in
/-- Track-A executable heterogeneous Eq. (46) at one time.  The generated
conditional kernel supplies both branches for the exact worker-dependent
process and canonical path law; no all-query sample-gradient regularity
premise is used. -/
theorem
    heterogeneous_online_estimator_recurrence_46_executable_of_literal_and_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal sigma : Worker n → ℝ) (omega : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer omega)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (k : ℕ)
    (hError : EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k)
    (hStep : StepMomentWellDefined
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) k) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
    EstimatorErrorMomentWellDefined P run law (k + 1) ∧
    EstimatorErrorMomentWellDefined P run law k ∧
    StepMomentWellDefined run law k ∧
    estimatorErrorMoment P run law (k + 1) ≤
      (1 - A.refreshProbability) / n.1 *
          (omega * (rootMeanSquare Llocal) ^ 2 +
            (1 + omega) *
              heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
          stepMoment run law k +
        (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
      A.refreshProbability * heterogeneousOnlineVarianceTerm sigma b := by
  classical
  letI : Nonempty (Worker n) := ⟨⟨0, n.2⟩⟩
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  have hRefresh :=
    heterogeneousOnlineExecutable_refresh_error_integrable_and_expectation_le_of_generatedKernel
      (b := b) (b0 := b0) A x0 ℒlocal sigma hKernel hLiteral hSmooth.1 k
  have hRefreshIndep :=
    heterogeneousOnlineExecutable_refresh_error_sq_indep_refresh_of_generatedKernel
      (b := b) (b0 := b0) A x0 ℒlocal sigma hKernel hLiteral k
  have hNonrefresh :=
    heterogeneousOnlineExecutable_nonrefresh_branch_moments_of_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal omega hSmooth hKernel
        hQuantizer k hError hStep
  have hNonrefreshIndep :=
    heterogeneousOnlineExecutable_nonrefresh_error_sq_indep_refresh_of_generatedKernel
      (b := b) (b0 := b0) A x0 ℒlocal hKernel k
  let residual := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (run k path).g - globalGradient P (run k path).x
  let innovation := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦
      A.quantizer.apply
          (heterogeneousOnlineBatchDifference A.problem b0
            (path.2 k).2.1.2 i (run (k + 1) path).x (run k path).x)
          ((path.2 k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
  let refreshError := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
      stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
        (run (k + 1) path).x)) -
      globalGradient P (run (k + 1) path).x
  let nextResidual := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (run (k + 1) path).g - globalGradient P (run (k + 1) path).x
  let branch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.2 k).1
  let refreshSq := fun path ↦ ‖refreshError path‖ ^ 2
  let nonrefreshSq := fun path ↦ ‖residual path + innovation path‖ ^ 2
  have hdecomp : ∀ path, nextResidual path =
      if branch path then refreshError path else residual path + innovation path := by
    intro path
    let s := run k path
    let xN := primalStep A.stepSize s
    let q := fun i : Worker n ↦
      A.quantizer.apply
        (heterogeneousOnlineBatchDifference A.problem b0
          (path.2 k).2.1.2 i xN s.x)
        ((path.2 k).2.2 i)
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
          if (path.2 k).1 then average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i ((path.2 k).2.1.1 i j) xN)
          else s.g + q i) - globalGradient P xN := by rfl
    cases h : branch path with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [hnext]
        simp only [branch] at h
        rw [h]
        simp only [Bool.false_eq_true, if_false]
        change average (fun i : Worker n ↦ s.g + q i) -
            globalGradient P xN = residual path + innovation path
        rw [average_const_add, hinnovationAvg, hdiffAvg]
        dsimp [residual, s]
        abel
    | true =>
        simp only [if_true]
        rw [hnext]
        simp only [branch] at h
        rw [h]
        rfl
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hbranchMeas : Measurable branch := by dsimp [branch]; fun_prop
  have hbranchLaw : Measure.map branch law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    let evalCoin := fun stream : ℕ →
        HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ (stream k).1
    calc
      Measure.map branch law = Measure.map evalCoin (Measure.map Prod.snd law) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · dsimp [evalCoin]; fun_prop
        · exact measurable_snd
      _ = Measure.map evalCoin
          (SOptLib.iidStreamLaw
            (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)) := by
        rw [show Measure.map Prod.snd law =
            SOptLib.iidStreamLaw
              (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) by
          dsimp [law, heterogeneousOnlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = Measure.map Prod.fst
          (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
        rw [show Measure.map evalCoin
            (SOptLib.iidStreamLaw
              (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)) =
              Measure.map Prod.fst
                (Measure.map (fun stream : ℕ →
                    HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ stream k)
                  (SOptLib.iidStreamLaw
                    (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A))) by
          rw [MeasureTheory.Measure.map_map]
          · rfl
          · exact measurable_fst
          · exact measurable_pi_apply k]
        rw [SOptLib.iidStreamLaw_map_eval]
      _ = _ := by simp [heterogeneousOnlineRoundLaw]
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
      hNonrefresh.2.1
  have hrefreshIndep : ProbabilityTheory.IndepFun refreshSq branch law := by
    simpa [refreshSq, refreshError, branch, P, run, law] using hRefreshIndep
  have hnonrefreshIndep : ProbabilityTheory.IndepFun nonrefreshSq branch law := by
    simpa [nonrefreshSq, residual, innovation, branch, P, run, law] using
      hNonrefreshIndep
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
      _ ≤ A.refreshProbability * heterogeneousOnlineVarianceTerm sigma b +
          (1 - A.refreshProbability) *
            (estimatorErrorMoment P run law k +
              (1 / (n.1 : ℝ)) *
                (omega * (rootMeanSquare Llocal) ^ 2 +
                  (1 + omega) *
                    heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
                stepMoment run law k) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
          · simpa [refreshSq, refreshError, P, run, law] using hRefresh.2
          · exact le_of_lt A.refresh_admissible.1
        · apply mul_le_mul_of_nonneg_left
          · simpa [nonrefreshSq, residual, innovation, P, run, law] using
              hNonrefresh.2.2
          · exact sub_nonneg.mpr A.refresh_admissible.2
      _ = (1 - A.refreshProbability) / n.1 *
            (omega * (rootMeanSquare Llocal) ^ 2 +
              (1 + omega) *
                heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run law k +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law k +
          A.refreshProbability * heterogeneousOnlineVarianceTerm sigma b := by
        ring

set_option maxHeartbeats 3000000 in
/-- Track-A executable heterogeneous component `L²` closure and Eq. (46)
history.  The base case is the actual worker-dependent sampled initializer;
every successor uses the generated conditional kernel on the same process
and canonical path law, without all-query regularity. -/
theorem
    heterogeneousOnlineProcess_scalar_recurrence_components_of_literal_and_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (k : ℕ) :
    let P := onlineLocalProblem A.problem
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
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
              (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
            stepMoment run law j +
          (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
          A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hState (t : ℕ) : AEMeasurable (run t) law := by
    simpa [run, law] using
      heterogeneousOnlineProcess_aemeasurable_of_generatedConditionalKernel
        (b := b) (b0 := b0) A x0 ℒlocal hKernel t
  have hGlobal : IsGradientLipschitz (globalObjective P)
      (rootMeanSquare Llocal) :=
    GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
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
                (1 + ω) *
                  heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
              stepMoment run law j +
            (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
            A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
    intro t
    induction t with
    | zero =>
        have h0 :=
          heterogeneousOnlineProcess_scalar_recurrence_components_zero_of_literal
            (b := b) (b0 := b0) A x0 Llocal σ hSmooth hLiteral
        refine ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1,
          h0.2.2.2.2.1, h0.2.2.2.2.2, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ t ih =>
        have hRec :=
          heterogeneous_online_estimator_recurrence_46_executable_of_literal_and_generatedKernel
            (b := b) (b0 := b0) A x0 Llocal ℒlocal σ ω hSmooth hLiteral
              hQuantizer hKernel t ih.2.2.2.2.1 ih.2.2.2.2.2.1
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
          simpa [run, heterogeneousOnlineProcess,
            SOptLib.recursive_process_from_random_initial,
            heterogeneousOnlineStep, primalStep_eq] using h
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
          simpa [StepMomentWellDefined, run, heterogeneousOnlineProcess,
            SOptLib.recursive_process_from_random_initial,
            heterogeneousOnlineStep, primalStep_eq] using hscaled
        have hHistory : ∀ j, j < t + 1 →
            estimatorErrorMoment P run law (j + 1) ≤
              (1 - A.refreshProbability) / n.1 *
                  (ω * (rootMeanSquare Llocal) ^ 2 +
                    (1 + ω) *
                      heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0) *
                  stepMoment run law j +
                (1 - A.refreshProbability) * estimatorErrorMoment P run law j +
                A.refreshProbability * heterogeneousOnlineVarianceTerm σ b := by
          intro j hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjt | rfl
          · exact ih.2.2.2.2.2.2 j hjt
          · exact hRec.2.2.2
        exact ⟨hxNext, hrNext, hxl2Next, hgl2Next, hRec.1, hsNext,
          hHistory⟩
  exact hAll k

set_option linter.unnecessarySeqFocus false in
/-- Track-A executable heterogeneous Remark D.2 convergence boundary.  It
uses the actual worker-dependent sampled initializer, generated process, and
product path law.  The generated conditional kernel supplies the exact
stochastic-initialization-corrected recurrence without all-query regularity. -/
theorem Theorem_D3_heterogeneous_online_VR_nonconvex_initialization_corrected_of_literal_and_generatedKernel
    {d n K : Count} {b b0 : Worker n → Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    Integrable (fun z =>
        ‖globalGradient (onlineLocalProblem A.problem)
          (uniformOutput (K := K)
            (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) z)‖ ^ 2)
        (uniformOutputExperimentLaw (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) K) ∧
      (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) K) ≤
        2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
            (A.stepSize * K.1) +
          expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 /
            (A.refreshProbability * K.1) +
          heterogeneousOnlineVarianceTerm σ b := by
  classical
  let P := onlineLocalProblem A.problem
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let γ : ℝ := A.stepSize
  let p : ℝ := A.refreshProbability
  let L : ℝ := rootMeanSquare Llocal
  let a : ℝ := (1 - p) / n.1 *
    (ω * L ^ 2 + (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
  let V : ℝ := heterogeneousOnlineVarianceTerm σ b
  let F : ℕ → ℝ := fun k => ∫ path, globalObjective P (run k path).x ∂law
  let E : ℕ → ℝ := fun k => estimatorErrorMoment P run law k
  let G : ℕ → ℝ := fun k =>
    ∫ path, ‖globalGradient P (run k path).x‖ ^ 2 ∂law
  let D : ℕ → ℝ := fun k => stepMoment run law k
  let Φ : ℕ → ℝ := fun k => F k + γ / (2 * p) * E k
  have hComponents (k : ℕ) :=
    heterogeneousOnlineProcess_scalar_recurrence_components_of_literal_and_generatedKernel
      (b := b) (b0 := b0) A x0 Llocal ℒlocal σ ω hSmooth hLiteral
        hQuantizer hKernel k
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b0) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hγ : 0 < γ := by exact A.stepSize.property
  have hp : 0 < p := A.refresh_admissible.1
  have hK : 0 < (K.1 : ℝ) := by exact_mod_cast K.2
  have hGlobal : IsGradientLipschitz (globalObjective P) L := by
    exact GlobalSmoothness_from_Assumption_1_2 P Llocal hSmooth
  have hxMeas (k : ℕ) : AEStronglyMeasurable
      (fun path => (run k path).x) law := by
    simpa [P, run, law] using (hComponents k).1
  have hGInt (k : ℕ) : Integrable
      (fun path => ‖globalGradient P (run k path).x‖ ^ 2) law := by
    apply SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      x0 (globalGradient P) L (fun path => (run k path).x) (hxMeas k)
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · intro x y
      exact hGlobal.2 y x
  have hFInt (k : ℕ) : Integrable
      (fun path => globalObjective P (run k path).x) law := by
    apply SOptLib.integrable_smooth_value_of_centered_l2
      (globalObjective P) (globalGradient P x0) x0 L
        (fun path => (run k path).x) (hxMeas k)
    · exact (hGlobal.1.continuous.measurable.comp_aemeasurable
        (hxMeas k).aemeasurable).aestronglyMeasurable
    · simpa [P, run, law, norm_sub_rev] using (hComponents k).2.2.1
    · filter_upwards [] with path
      exact SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        Set.univ (globalObjective P) (globalGradient P) L convex_univ
        (fun z _hz => (hGlobal.1 z).hasGradientAt)
        (fun z _hz w _hw => hGlobal.2 z w) (by simp) (by simp)
  have hEInt (k : ℕ) : Integrable (fun path =>
      ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, EstimatorErrorMomentWellDefined] using
      (hComponents k).2.2.2.2.1
  have hDInt (k : ℕ) : Integrable (fun path =>
      ‖(run (k + 1) path).x - (run k path).x‖ ^ 2) law := by
    simpa [P, run, law, StepMomentWellDefined] using
      (hComponents k).2.2.2.2.2.1
  have hDescent (k : ℕ) :
      F (k + 1) ≤ F k - γ / 2 * G k -
        (1 / (2 * γ) - L / 2) * D k + γ / 2 * E k := by
    have hpoint (path) :
        globalObjective P (run (k + 1) path).x ≤
          globalObjective P (run k path).x - γ / 2 *
              ‖globalGradient P (run k path).x‖ ^ 2 -
            (1 / (2 * γ) - L / 2) *
              ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
            γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 := by
      simpa [P, run, γ, L, heterogeneousOnlineProcess,
        SOptLib.recursive_process_from_random_initial, heterogeneousOnlineStep,
        primalStep_eq] using
          (DescentLemma_B1 (globalObjective P) L γ
            (run k path).x (run k path).g hGlobal)
    have hrhs : Integrable (fun path =>
        globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2) law :=
      (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
        ((hDInt k).const_mul (1 / (2 * γ) - L / 2))).add
          ((hEInt k).const_mul (γ / 2))
    have hmono := integral_mono (hFInt (k + 1)) hrhs hpoint
    have hrhs_eq :
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2 ∂law) =
          F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
      calc
        (∫ path, globalObjective P (run k path).x - γ / 2 *
            ‖globalGradient P (run k path).x‖ ^ 2 -
          (1 / (2 * γ) - L / 2) *
            ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 +
          γ / 2 * ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
          ∂law) =
            (∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 -
              (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law := by
              simpa only [Pi.add_apply] using
                (integral_add
                  (((hFInt k).sub ((hGInt k).const_mul (γ / 2))).sub
                    ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
                  ((hEInt k).const_mul (γ / 2)))
        _ = (((∫ path, globalObjective P (run k path).x - γ / 2 *
                ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 1
              simpa only [Pi.sub_apply] using
                (integral_sub
                  ((hFInt k).sub ((hGInt k).const_mul (γ / 2)))
                  ((hDInt k).const_mul (1 / (2 * γ) - L / 2)))
        _ = ((((∫ path, globalObjective P (run k path).x ∂law) -
              ∫ path, γ / 2 * ‖globalGradient P (run k path).x‖ ^ 2 ∂law) -
              ∫ path, (1 / (2 * γ) - L / 2) *
                ‖(run (k + 1) path).x - (run k path).x‖ ^ 2 ∂law) +
              ∫ path, γ / 2 *
                ‖(run k path).g - globalGradient P (run k path).x‖ ^ 2
                ∂law) := by
              congr 2
              simpa only [Pi.sub_apply] using
                (integral_sub (hFInt k) ((hGInt k).const_mul (γ / 2)))
        _ = F k - γ / 2 * G k - (1 / (2 * γ) - L / 2) * D k +
            γ / 2 * E k := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
              rfl
    rw [hrhs_eq] at hmono
    exact hmono
  have hRecurrence (k : ℕ) :
      E (k + 1) ≤ a * D k + (1 - p) * E k + p * V := by
    have hrec :=
      (hComponents (k + 1)).2.2.2.2.2.2 k (Nat.lt_succ_self k)
    dsimp [E, D, a, V, P, run, law, p, L]
    exact hrec
  have hL : 0 ≤ L := by exact Real.sqrt_nonneg _
  have hS : 0 ≤ heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0 := by
    unfold heterogeneousFiniteBatchSmoothnessTerm average SOptLib.finiteUniformAverage
    positivity
  have hCoeff : 0 ≤ 1 / (2 * γ) - L / 2 - γ / (2 * p) * a := by
    exact heterogeneous_vr_stepsize_absorbs_displacement hγ A.refresh_admissible
      hQuantizer.1.le hL hS hStep
  have hLyapunov (k : ℕ) :
      Φ (k + 1) ≤ Φ k - γ / 2 * G k + γ / 2 * V := by
    have hDnonneg : 0 ≤ D k := by
      exact integral_nonneg fun path => sq_nonneg _
    simpa [Φ] using online_vr_nonconvex_lyapunov_step F E G D k hγ hp
      hDnonneg hCoeff (hDescent k) (hRecurrence k)
  have hTelescope (N : ℕ) :
      γ / 2 * ∑ k ∈ Finset.range N, G k ≤
        Φ 0 - Φ N + (N : ℝ) * (γ / 2) * V := by
    induction N with
    | zero => simp
    | succ N ih =>
        have hstep : γ / 2 * G N ≤ Φ N - Φ (N + 1) + γ / 2 * V := by
          linarith [hLyapunov N]
        rw [Finset.sum_range_succ]
        push_cast
        nlinarith
  have hE0 :
      E 0 = expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 := by
    simpa [E, P, run, law] using
      (heterogeneous_online_executable_initial_error_moment_eq_expected_of_literal
        (b := b) (b0 := b0) A x0 σ hLiteral hSmooth.1)
  have hF0 : F 0 = globalObjective P x0 := by
    have heq : (fun path => globalObjective P (run 0 path).x) =
        (fun _ => globalObjective P x0) := by
      funext path
      rfl
    unfold F
    rw [heq, integral_const]
    simp
  have hFK : fStar ≤ F K.1 := by
    have hconst : Integrable (fun _ :
        HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => fStar) law :=
      integrable_const _
    have hmono := integral_mono hconst (hFInt K.1)
      (fun path => hLower (run K.1 path).x)
    simpa [F] using hmono
  have hEK : 0 ≤ E K.1 := by
    exact integral_nonneg fun path => sq_nonneg _
  have hterminal : fStar ≤ Φ K.1 := by
    dsimp [Φ]
    have hweight : 0 ≤ γ / (2 * p) := by positivity
    nlinarith [mul_nonneg hweight hEK]
  have hsum :
      γ / 2 * ∑ k ∈ Finset.range K.1, G k ≤
        globalObjective P x0 - fStar +
          γ / (2 * p) * expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 +
          (K.1 : ℝ) * (γ / 2) * V := by
    have ht := hTelescope K.1
    dsimp [Φ] at ht
    rw [hE0, hF0] at ht
    linarith
  have hFibers (k : Fin K.1) : Integrable
      (fun path => ‖globalGradient P (run k.1 path).x‖ ^ 2) law := hGInt k.1
  haveI : IsProbabilityMeasure (uniformOutputIndexLaw K) := by
    unfold uniformOutputIndexLaw
    infer_instance
  have hOutputInt : Integrable (fun z =>
      ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2)
      (uniformOutputExperimentLaw law K) := by
    have hsel := integrable_finite_index_first_prod_of_fiber_integrable
      (uniformOutputIndexLaw K) law
      (fun k : Fin K.1 => fun path =>
        ‖globalGradient P (run k.1 path).x‖ ^ 2) hFibers
    simpa [uniformOutputExperimentLaw, uniformOutput, outputAt,
      Function.comp_def] using hsel.swap
  have hOutputEq :
      (∫ z, ‖globalGradient P (uniformOutput (K := K) run z)‖ ^ 2
        ∂uniformOutputExperimentLaw law K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k := by
    have havg := uniformOutput_expectation_eq_average run law
      (fun x => ‖globalGradient P x‖ ^ 2) hFibers
    rw [havg]
    unfold average SOptLib.finiteUniformAverage
    simp only [Fintype.card_fin, smul_eq_mul]
    change (K.1 : ℝ)⁻¹ * ∑ k : Fin K.1, G k =
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k
    rw [Fin.sum_univ_eq_sum_range]
  have hAverageBound :
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k ≤
        2 * (globalObjective P x0 - fStar) / (γ * K.1) +
          expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 / (p * K.1) +
          V := by
    have hscale : 0 ≤ 2 / (γ * (K.1 : ℝ)) := by positivity
    have hs := mul_le_mul_of_nonneg_left hsum hscale
    calc
      (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k =
          (2 / (γ * (K.1 : ℝ))) *
            (γ / 2 * ∑ k ∈ Finset.range K.1, G k) := by
              field_simp [ne_of_gt hγ, ne_of_gt hK]
      _ ≤ (2 / (γ * (K.1 : ℝ))) *
          (globalObjective P x0 - fStar +
            γ / (2 * p) * expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 +
            (K.1 : ℝ) * (γ / 2) * V) := hs
      _ = 2 * (globalObjective P x0 - fStar) / (γ * K.1) +
          expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 / (p * K.1) +
          V := by
        field_simp [ne_of_gt hγ, ne_of_gt hp, ne_of_gt hK]
  refine ⟨?_, ?_⟩
  · simpa [P, run, law] using hOutputInt
  · rw [show (∫ z,
          ‖globalGradient (onlineLocalProblem A.problem)
            (uniformOutput (K := K)
              (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) z)‖ ^ 2
        ∂uniformOutputExperimentLaw
          (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) K) =
        (K.1 : ℝ)⁻¹ * ∑ k ∈ Finset.range K.1, G k by
          simpa [P, run, law] using hOutputEq]
    simpa [P, γ, V] using hAverageBound

/-- The generated-kernel heterogeneous D.3 boundary yields the requested
uniform-output accuracy whenever its iteration, stochastic-initialization,
and worker-dependent variance terms fit the accuracy budget. -/
theorem heterogeneousOnlineExecutableNonconvexAccuracy_of_budget_of_literal_and_generatedKernel
    {d n K : Count} {b b0 : Worker n → Count}
    {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal σ : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ℒlocal)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n)
    (ε : Accuracy)
    (hBudget :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        heterogeneousOnlineVarianceTerm σ b /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm σ b ≤ (ε : ℝ) ^ 2) :
    NonconvexAccuracy K (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ε := by
  unfold NonconvexAccuracy
  have hBoundary :=
    Theorem_D3_heterogeneous_online_VR_nonconvex_initialization_corrected_of_literal_and_generatedKernel
      (b := b) (b0 := b0) (K := K) A x0 Llocal ℒlocal σ ω fStar
        hLower hSmooth hLiteral hQuantizer hKernel hStep
  refine ⟨hBoundary.1, hBoundary.2.trans ?_⟩
  have hInitial := expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
    (b := b) A x0 σ hLiteral hSmooth.1
  have hdenom : 0 ≤ (A.refreshProbability : ℝ) * K.1 :=
    mul_nonneg A.refresh_admissible.1.le (by positivity)
  have hInitialDiv :
      expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) ≤
        heterogeneousOnlineVarianceTerm σ b /
          (A.refreshProbability * K.1) :=
    div_le_div_of_nonneg_right hInitial hdenom
  calc
    2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm σ b ≤
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) +
        heterogeneousOnlineVarianceTerm σ b /
          (A.refreshProbability * K.1) +
        heterogeneousOnlineVarianceTerm σ b := by gcongr
    _ ≤ (ε : ℝ) ^ 2 := hBudget

/-- Generated-kernel executable heterogeneous accuracy for the refresh-scaled
source batch.  Only the ordinary optimization-term budget remains for the
horizon chooser; literal moments and the batch schedule pay the stochastic
terms without all-query regularity. -/
theorem
    heterogeneousOnlineExecutableNonconvexAccuracy_of_half_optimization_budget_of_generatedKernel
    {d n K : Count} {Sample : Worker n → Type*} {b0 : Worker n → Count}
    {Ξ : Type*} [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (base : Accuracy → Worker n → Count)
    (Llocal ℒlocal sigma : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (ε : Accuracy)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess
        (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
        (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw
        (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
        (b0 := b0) A) ℒlocal)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n)
    (hOptimization :
      2 * (globalObjective (onlineLocalProblem A.problem) x0 - fStar) /
          (A.stepSize * K.1) ≤ (ε : ℝ) ^ 2 / 2) :
    NonconvexAccuracy K (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess
        (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
        (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw
        (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
        (b0 := b0) A) ε := by
  apply
    heterogeneousOnlineExecutableNonconvexAccuracy_of_budget_of_literal_and_generatedKernel
      (b := heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base ε)
      (b0 := b0) A x0 Llocal ℒlocal sigma ω fStar hLower hSmooth hLiteral
        hQuantizer hKernel hStep ε
  exact heterogeneousOnlineExecutableBatchSchedule_budget A sigma base ε
    (globalObjective (onlineLocalProblem A.problem) x0 - fStar) hOptimization

set_option maxHeartbeats 3000000 in
/-- The generated worker-row kernel remains measurable after discarding the
unused iid tail.  This is the strict-prefix/fresh-difference-batch statement
needed by the actual heterogeneous communication message. -/
theorem
    heterogeneousOnlineExecutablePrefix_workerDifferenceMessage_product_aestronglyMeasurable_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Xi : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Xi]
    (A : OnlineData d n Sample Xi) (x0 : Point d) (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)
    (k : ℕ) (i : Worker n) :
    let initialLaw := heterogeneousOnlineBatchLaw A.problem b
    let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
    let prefixLaw := initialLaw.prod
      (Measure.infinitePi (fun _ : Fin k ↦ roundLaw))
    let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
    let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
      heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k
        (pref.1, fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
    AEStronglyMeasurable
      (fun p :
          (HeterogeneousOnlineBatch n Sample b ×
              (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b0 ↦
        heterogeneousOnlineBatchDifference A.problem b0 p.2 i
          (primalStep A.stepSize (prefixState p.1))
          (prefixState p.1).x)
      (prefixLaw.prod differenceBatchLaw) := by
  classical
  dsimp only
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    run k (pref.1,
      fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure
      (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hfull : AEStronglyMeasurable
      (fun p :
          (HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b0 ↦
        heterogeneousOnlineBatchDifference A.problem b0 p.2 i
          (run (k + 1) p.1).x (run k p.1).x)
      (law.prod differenceBatchLaw) := by
    let rowLaw := Measure.pi
      (fun _ : Fin (b0 i).1 ↦ A.problem.sampleLaw i)
    let project := fun p :
        (HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
          HeterogeneousOnlineBatch n Sample b0 ↦
      (p.1, p.2 i)
    have hproject : Measurable project := by
      dsimp [project]
      fun_prop
    have hprojectLaw : Measure.map project (law.prod differenceBatchLaw) =
        law.prod rowLaw := by
      have hm := MeasureTheory.Measure.map_prod_map law differenceBatchLaw
        measurable_id (measurable_pi_apply i)
      rw [Measure.map_id,
        heterogeneous_online_batch_law_worker_marginal A.problem b0 i] at hm
      simpa [project, rowLaw, differenceBatchLaw,
        MeasureTheory.Measure.infinitePi_eq_pi] using hm.symm
    have hrow :=
      heterogeneousOnlineAssumption32GeneratedConditionalKernel_rowDifference_joint_aestronglyMeasurable
        hKernel k i
    have hqmp : Measure.QuasiMeasurePreserving project
        (law.prod differenceBatchLaw) (law.prod rowLaw) :=
      ⟨hproject, by rw [hprojectLaw]⟩
    simpa [project, rowLaw, law, run, heterogeneousOnlineBatchDifference,
      Function.comp_def] using hrow.comp_quasiMeasurePreserving hqmp
  have hreorder : MeasurePreserving
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              HeterogeneousOnlineBatch n Sample b0) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod differenceBatchLaw).prod streamLaw)
      ((initialLaw.prod streamLaw).prod differenceBatchLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw differenceBatchLaw streamLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := differenceBatchLaw) (ν := streamLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw streamLaw differenceBatchLaw).symm
    simpa [Function.comp_def] using h3.comp (h2.comp h1)
  have hstream : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              HeterogeneousOnlineBatch n Sample b0) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        heterogeneousOnlineBatchDifference A.problem b0 p.1.2 i
          (run (k + 1) (p.1.1, p.2)).x
          (run k (p.1.1, p.2)).x)
      ((initialLaw.prod differenceBatchLaw).prod streamLaw) := by
    simpa [Function.comp_def] using hfull.comp_measurePreserving hreorder
  let F := fun p :
      (HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) ×
        (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi) ↦
    heterogeneousOnlineBatchDifference A.problem b0 p.1.2 i
      (primalStep A.stepSize (prefixState (p.1.1, p.2)))
      (prefixState (p.1.1, p.2)).x
  have hstatePrefix : ∀ initial stream,
      prefixState (initial, fun j : Fin k ↦ stream j.1) =
        run k (initial, stream) := by
    intro initial stream
    dsimp [prefixState, run]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k initial
      (path := stream)
      (path' := fun t ↦ if ht : t < k then stream t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hstreamF : AEStronglyMeasurable
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              HeterogeneousOnlineBatch n Sample b0) ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ↦
        F (p.1, fun j : Fin k ↦ p.2 j.1))
      ((initialLaw.prod differenceBatchLaw).prod streamLaw) := by
    refine hstream.congr (Filter.Eventually.of_forall ?_)
    intro p
    dsimp [F]
    rw [hstatePrefix p.1.1 p.2]
    rfl
  have hfinite : AEStronglyMeasurable F
      ((initialLaw.prod differenceBatchLaw).prod prefixStreamLaw) := by
    simpa [prefixStreamLaw] using
      aestronglyMeasurable_initial_prefix_of_comp_general
        (initialLaw.prod differenceBatchLaw) roundLaw k F hstreamF
  have hreorderFinite : MeasurePreserving
      (fun p :
          ((HeterogeneousOnlineBatch n Sample b ×
              (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Xi)) ×
            HeterogeneousOnlineBatch n Sample b0) ↦
        ((p.1.1, p.2), p.1.2))
      ((initialLaw.prod prefixStreamLaw).prod differenceBatchLaw)
      ((initialLaw.prod differenceBatchLaw).prod prefixStreamLaw) := by
    have h1 := measurePreserving_prodAssoc initialLaw prefixStreamLaw
      differenceBatchLaw
    have h2 := (MeasurePreserving.id initialLaw).prod
      (MeasureTheory.Measure.measurePreserving_swap
        (μ := prefixStreamLaw) (ν := differenceBatchLaw))
    have h3 :=
      (measurePreserving_prodAssoc initialLaw differenceBatchLaw
        prefixStreamLaw).symm
    simpa [Function.comp_def] using h3.comp (h2.comp h1)
  have hresult := hfinite.comp_measurePreserving hreorderFinite
  simpa [F, prefixLaw, prefixStreamLaw, prefixState, initialLaw, roundLaw,
    differenceBatchLaw, Function.comp_def] using hresult

set_option maxHeartbeats 3000000 in
/-- The source generated kernel makes the actual worker-dependent executable
difference message a random vector under its canonical path law. -/
theorem
    heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (k : ℕ) (i : Worker n) :
    AEStronglyMeasurable
      (heterogeneousOnlineWorkerDifferenceMessage
        (b := b) (b0 := b0) A x0 k i)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  classical
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.1, fun j : Fin k ↦ path.2 j.1)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (current path).2.1.2
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    unfold roundLaw heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hbatch : Measurable batch := by dsimp [batch, current]; fun_prop
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixMap, prefixLaw, prefixStreamLaw, law] using hm.symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (Measure.map Prod.snd law) := by
              rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
              rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) streamLaw := by
              rw [show Measure.map Prod.snd law = streamLaw by
                dsimp [law]
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := by
        simpa [streamLaw] using SOptLib.iidStreamLaw_map_eval roundLaw k
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · let streamJoint := fun stream :
          ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
          ((fun j : Fin k ↦ stream j.1), stream k)
      have hstreamJoint : MeasurePreserving streamJoint streamLaw
          (prefixStreamLaw.prod roundLaw) := by
        refine ⟨(by
          dsimp [streamJoint]
          exact (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).prodMk
            (measurable_pi_apply k)), ?_⟩
        have hj := infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ roundLaw) k
        have hprefixStream : Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
              fun j : Fin k ↦ stream j.1) streamLaw = prefixStreamLaw := by
          simpa [streamLaw, prefixStreamLaw] using
            iidStream_prefix_map_eq_infinitePi roundLaw k
        have hprefixRaw : Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
              fun j : Fin k ↦ stream j.1)
            (Measure.infinitePi (fun _ : ℕ ↦ roundLaw)) =
              prefixStreamLaw := by
          simpa [streamLaw] using hprefixStream
        rw [hprefixRaw] at hj
        simpa [streamJoint, streamLaw, prefixStreamLaw] using hj
      have h0 := (MeasurePreserving.id initialLaw).prod hstreamJoint
      have h1 :=
        (measurePreserving_prodAssoc initialLaw prefixStreamLaw roundLaw).symm
      have h := h1.comp h0
      simpa [law, prefixLaw, prefixMap, current, streamJoint,
        Function.comp_def] using h.map_eq
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law := by
    have h := hpastCurrent.comp measurable_id
      (show Measurable
        (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.2.1.2) by
          fun_prop)
    simpa [batch, current, Function.comp_def] using h
  have hbatchLaw : Measure.map batch law = differenceBatchLaw := by
    calc
      Measure.map batch law = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.2.1.2)
          (Measure.map current law) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦ z.2.1.2)
          roundLaw := by rw [hcurrentLaw]
      _ = differenceBatchLaw := by
        let refreshBatchLaw := heterogeneousOnlineBatchLaw A.problem b
        let rowLaw := workerCompressionLaw (n := n) A.quantizer
        let restLaw := (refreshBatchLaw.prod differenceBatchLaw).prod rowLaw
        calc
          Measure.map
              (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
                z.2.1.2) roundLaw =
              Measure.map (fun z :
                  (HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                z.1.2) (Measure.map Prod.snd roundLaw) := by
                  rw [Measure.map_map]
                  · rfl
                  · fun_prop
                  · exact measurable_snd
          _ = Measure.map (fun z :
                  (HeterogeneousOnlineBatch n Sample b ×
                    HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                z.1.2) restLaw := by
                  rw [show Measure.map Prod.snd roundLaw = restLaw by
                    dsimp [roundLaw, restLaw, refreshBatchLaw]
                    unfold heterogeneousOnlineRoundLaw
                    rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = Measure.map Prod.snd (refreshBatchLaw.prod differenceBatchLaw) := by
                  rw [show (fun z :
                      (HeterogeneousOnlineBatch n Sample b ×
                        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                    z.1.2) = Prod.snd ∘ Prod.fst by rfl,
                    ← Measure.map_map measurable_snd measurable_fst,
                    Measure.map_fst_prod, measure_univ, one_smul]
          _ = differenceBatchLaw := by
                  rw [Measure.map_snd_prod, measure_univ, one_smul]
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k
      (pref.1, fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  let F := fun (pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ))
      (fresh : HeterogeneousOnlineBatch n Sample b0) ↦
    heterogeneousOnlineBatchDifference A.problem b0 fresh i
      (primalStep A.stepSize (prefixState pref)) (prefixState pref).x
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod differenceBatchLaw) := by
    simpa [F, prefixState, prefixLaw, prefixStreamLaw, initialLaw, roundLaw,
      differenceBatchLaw] using
      heterogeneousOnlineExecutablePrefix_workerDifferenceMessage_product_aestronglyMeasurable_of_generatedKernel
        A x0 Lcal hKernel fallback k i
  have hFmap : AEStronglyMeasurable (Function.uncurry F)
      ((Measure.map prefixMap law).prod (Measure.map batch law)) := by
    rw [hprefixLaw, hbatchLaw]
    exact hF
  have hcomp := aestronglyMeasurable_comp_of_indep_product_law
    hprefix.aemeasurable hbatch.aemeasurable
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map batch law))
      hprefixBatch hFmap
  have hstatePrefix : ∀ path, prefixState (prefixMap path) =
      heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path := by
    intro path
    dsimp [prefixState, prefixMap]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2)
      (path' := fun t ↦ if ht : t < k then path.2 t else fallback t)
      (by intro t ht; simp [ht])).symm
  refine hcomp.congr (Filter.Eventually.of_forall ?_)
  intro path
  dsimp [Function.uncurry, F, batch, current,
    heterogeneousOnlineWorkerDifferenceMessage]
  rw [hstatePrefix path]

set_option maxHeartbeats 5000000 in
/-- The generated-kernel message representative is independent of the fresh
compressor coordinate, and its support is independent of the refresh coin. -/
theorem
    heterogeneousOnlineWorkerMessageRepresentative_independences_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal)
    (k : ℕ) (i : Worker n) :
    let hm :=
      heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
        A x0 Lcal hKernel k i
    ProbabilityTheory.IndepFun
        (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i))
        (heterogeneousOnlineWorkerCompressionSample k i)
        (heterogeneousOnlinePathLaw A) ∧
      ProbabilityTheory.IndepFun
        (fun path ↦ quantizerNonzeroCount A.quantizer
          (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i) path)
          (heterogeneousOnlineWorkerCompressionSample k i path))
        (heterogeneousOnlineRefreshBranch k)
        (heterogeneousOnlinePathLaw A) := by
  classical
  dsimp only
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let differenceBatchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let restLaw := (initialLaw.prod differenceBatchLaw).prod rowLaw
  let roundLaw := coinLaw.prod restLaw
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := initialLaw.prod streamLaw
  let prefixStreamLaw := Measure.infinitePi (fun _ : Fin k ↦ roundLaw)
  let prefixLaw := initialLaw.prod prefixStreamLaw
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.1, fun j : Fin k ↦ path.2 j.1)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (current path).2.1.2
  let row := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (current path).2.2
  let sample := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ row path i
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    unfold initialLaw heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure differenceBatchLaw := by
    unfold differenceBatchLaw heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    unfold rowLaw workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    unfold coinLaw refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by unfold restLaw; infer_instance
  haveI : IsProbabilityMeasure roundLaw := by unfold roundLaw; infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    unfold streamLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by unfold law; infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j ↦
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hbatch : Measurable batch := by dsimp [batch, current]; fun_prop
  have hrow : Measurable row := by dsimp [row, current]; fun_prop
  have hsample : Measurable sample := (measurable_pi_apply i).comp hrow
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by
    have hm := MeasureTheory.Measure.map_prod_map initialLaw streamLaw
      measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) ↦ measurable_pi_apply j.1)
    rw [Measure.map_id, iidStream_prefix_map_eq_infinitePi roundLaw k] at hm
    simpa [prefixMap, prefixLaw, prefixStreamLaw, law] using hm.symm
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw) (nu := roundLaw)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · let streamJoint := fun stream :
          ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
          ((fun j : Fin k ↦ stream j.1), stream k)
      have hstreamJoint : MeasurePreserving streamJoint streamLaw
          (prefixStreamLaw.prod roundLaw) := by
        refine ⟨(by
          dsimp [streamJoint]
          exact (measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1).prodMk
            (measurable_pi_apply k)), ?_⟩
        have hj := infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ roundLaw) k
        have hprefixStream : Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
              fun j : Fin k ↦ stream j.1) streamLaw = prefixStreamLaw := by
          simpa [streamLaw, prefixStreamLaw] using
            iidStream_prefix_map_eq_infinitePi roundLaw k
        have hprefixRaw : Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
              fun j : Fin k ↦ stream j.1)
            (Measure.infinitePi (fun _ : ℕ ↦ roundLaw)) =
              prefixStreamLaw := by
          simpa [streamLaw] using hprefixStream
        rw [hprefixRaw] at hj
        simpa [streamJoint, streamLaw, prefixStreamLaw] using hj
      have h0 := (MeasurePreserving.id initialLaw).prod hstreamJoint
      have h1 :=
        (measurePreserving_prodAssoc initialLaw prefixStreamLaw roundLaw).symm
      have h := h1.comp h0
      simpa [law, prefixLaw, prefixMap, current, streamJoint,
        Function.comp_def] using h.map_eq
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (batch path, row path)
  have hnoise : Measurable noise := hbatch.prodMk hrow
  have hprefixNoise : ProbabilityTheory.IndepFun prefixMap noise law := by
    have h := hpastCurrent.comp measurable_id
      (show Measurable
        (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
          (z.2.1.2, z.2.2)) by fun_prop)
    simpa [noise, batch, row, current, Function.comp_def] using h
  have hnoiseLaw : Measure.map noise law = differenceBatchLaw.prod rowLaw := by
    have hcurrentLaw : Measure.map current law = roundLaw := by
      calc
        Measure.map current law = Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
              stream k) (Measure.map Prod.snd law) := by
                rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
                rfl
        _ = Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
              stream k) streamLaw := by
                rw [show Measure.map Prod.snd law = streamLaw by
                  dsimp [law]
                  rw [Measure.map_snd_prod, measure_univ, one_smul]]
        _ = roundLaw := by
          simpa [streamLaw] using SOptLib.iidStreamLaw_map_eval roundLaw k
    calc
      Measure.map noise law = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            (z.2.1.2, z.2.2)) (Measure.map current law) := by
              rw [Measure.map_map]
              · rfl
              · fun_prop
              · exact hcurrent
      _ = Measure.map
          (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            (z.2.1.2, z.2.2)) roundLaw := by rw [hcurrentLaw]
      _ = differenceBatchLaw.prod rowLaw := by
        simpa [roundLaw, restLaw] using
          heterogeneousOnlineRoundLaw_differenceCompression_marginal
            (b := b) (b0 := b0) A
  have hprefixBatchRow : ProbabilityTheory.IndepFun
      (fun path ↦ (prefixMap path, batch path)) row law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law differenceBatchLaw rowLaw
      prefixMap batch row hprefix hbatch hrow hprefixNoise hnoiseLaw
  have hbatchLaw : Measure.map batch law = differenceBatchLaw := by
    calc
      Measure.map batch law = Measure.map Prod.fst (Measure.map noise law) := by
        simpa [noise, Function.comp_apply] using
          (Measure.map_map measurable_fst hnoise (μ := law)).symm
      _ = Measure.map Prod.fst (differenceBatchLaw.prod rowLaw) := by
        rw [hnoiseLaw]
      _ = differenceBatchLaw := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ :=
    fun _ ↦ Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let prefixState := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k
      (pref.1, fun t ↦ if ht : t < k then pref.2 ⟨t, ht⟩ else fallback t)
  let F := fun (pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ))
      (fresh : HeterogeneousOnlineBatch n Sample b0) ↦
    heterogeneousOnlineBatchDifference A.problem b0 fresh i
      (primalStep A.stepSize (prefixState pref)) (prefixState pref).x
  have hF : AEStronglyMeasurable (Function.uncurry F)
      (prefixLaw.prod differenceBatchLaw) := by
    simpa [F, prefixState, prefixLaw, prefixStreamLaw, initialLaw, roundLaw,
      differenceBatchLaw] using
      heterogeneousOnlineExecutablePrefix_workerDifferenceMessage_product_aestronglyMeasurable_of_generatedKernel
        A x0 Lcal hKernel fallback k i
  let kernel' := hF.mk (Function.uncurry F)
  have hkernel' : Measurable kernel' := hF.measurable_mk
  let joined := fun path ↦ (prefixMap path, batch path)
  have hjoined : Measurable joined := hprefix.prodMk hbatch
  have hprefixBatch : ProbabilityTheory.IndepFun prefixMap batch law :=
    hprefixNoise.comp measurable_id measurable_fst
  have hjoinedLaw : Measure.map joined law =
      prefixLaw.prod differenceBatchLaw := by
    calc
      Measure.map joined law =
          (Measure.map prefixMap law).prod (Measure.map batch law) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hprefix.aemeasurable hbatch.aemeasurable).1 hprefixBatch
      _ = prefixLaw.prod differenceBatchLaw := by rw [hprefixLaw, hbatchLaw]
  have hjoinedQmp : Measure.QuasiMeasurePreserving joined law
      (prefixLaw.prod differenceBatchLaw) := ⟨hjoined, by rw [hjoinedLaw]⟩
  have hkernelMk := hjoinedQmp.tendsto_ae hF.ae_eq_mk
  have hstatePrefix : ∀ path, prefixState (prefixMap path) =
      heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path := by
    intro path
    dsimp [prefixState, prefixMap]
    exact (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2)
      (path' := fun t ↦ if ht : t < k then path.2 t else fallback t)
      (by intro t ht; simp [ht])).symm
  have hcalcMessage : (fun path ↦ kernel' (joined path)) =ᵐ[law]
      heterogeneousOnlineWorkerDifferenceMessage A x0 k i := by
    filter_upwards [hkernelMk] with path hk
    have hk' : Function.uncurry F (joined path) = kernel' (joined path) := by
      simpa only [Set.mem_preimage, Set.mem_setOf_eq] using hk
    rw [← hk']
    dsimp [Function.uncurry, F, joined, batch, current,
      heterogeneousOnlineWorkerDifferenceMessage]
    rw [hstatePrefix path]
  let hm :=
    heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
      A x0 Lcal hKernel k i
  have hcalcIndep : ProbabilityTheory.IndepFun
      (fun path ↦ kernel' (joined path)) sample law := by
    simpa [joined, sample] using
      hprefixBatchRow.comp hkernel' (measurable_pi_apply i)
  have hfirst : ProbabilityTheory.IndepFun
      (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i))
      (heterogeneousOnlineWorkerCompressionSample k i) law := by
    apply hcalcIndep.congr
    · exact hcalcMessage.trans hm.ae_eq_mk
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  let supportF := fun (pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ))
      (rest : (HeterogeneousOnlineBatch n Sample b ×
        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
    quantizerNonzeroCount A.quantizer
      (kernel' (pref, rest.1.2)) (rest.2 i)
  have hsupportF : Measurable (Function.uncurry supportF) := by
    have hm' : Measurable (fun z :
        (HeterogeneousOnlineBatch n Sample b ×
            (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) ×
          ((HeterogeneousOnlineBatch n Sample b ×
            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
        kernel' (z.1, z.2.1.2)) := by fun_prop
    have hs : Measurable (fun z :
        (HeterogeneousOnlineBatch n Sample b ×
            (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) ×
          ((HeterogeneousOnlineBatch n Sample b ×
            HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) ↦
        z.2.2 i) := by fun_prop
    simpa [supportF] using
      (quantizerNonzeroCount_joint_measurable A.quantizer).comp (hm'.prodMk hs)
  have hsupportIndep : ProbabilityTheory.IndepFun
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        supportF (path.1, fun j : Fin k ↦ path.2 j.1) (path.2 k).2)
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        (path.2 k).1) law := by
    have h := initial_iidStream_prefix_current_snd_kernel_indep_fst
      initialLaw coinLaw restLaw k supportF hsupportF.aestronglyMeasurable
    simpa [law, streamLaw, roundLaw] using h
  have hsupportAE :
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        supportF (path.1, fun j : Fin k ↦ path.2 j.1) (path.2 k).2) =ᵐ[law]
      (fun path ↦ quantizerNonzeroCount A.quantizer
        (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i) path)
        (heterogeneousOnlineWorkerCompressionSample k i path)) := by
    filter_upwards [hcalcMessage, hm.ae_eq_mk] with path hc hm'
    have hc' : kernel'
        ((path.1, fun j : Fin k ↦ path.2 j.1), (path.2 k).2.1.2) =
          heterogeneousOnlineWorkerDifferenceMessage A x0 k i path := by
      simpa using hc
    dsimp [supportF, joined, prefixMap, batch, row, sample, current,
      heterogeneousOnlineWorkerCompressionSample] at *
    rw [hc', hm']
  have hsecond : ProbabilityTheory.IndepFun
      (fun path ↦ quantizerNonzeroCount A.quantizer
        (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i) path)
        (heterogeneousOnlineWorkerCompressionSample k i path))
      (heterogeneousOnlineRefreshBranch k) law := by
    apply hsupportIndep.congr hsupportAE
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  exact ⟨hfirst, hsecond⟩

/-- The source-faithful generated conditional kernel supplies the exact weak
law-a.e. communication interface for executable heterogeneous Remark D.2. -/
theorem heterogeneousOnlineCommunicationAELawRegularity_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (Lcal : Worker n → ℝ)
    (hKernel : HeterogeneousOnlineAssumption32GeneratedConditionalKernel
      (b0 := b0) A.problem
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) Lcal) :
    HeterogeneousOnlineCommunicationAELawRegularity
      (b := b) (b0 := b0) A x0 := by
  let hm := fun k i ↦
    heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_generatedKernel
      A x0 Lcal hKernel k i
  refine ⟨hm, ?_, ?_⟩
  · intro k i
    exact (heterogeneousOnlineWorkerMessageRepresentative_independences_of_generatedKernel
      A x0 Lcal hKernel k i).1
  · intro k i
    exact (heterogeneousOnlineWorkerMessageRepresentative_independences_of_generatedKernel
      A x0 Lcal hKernel k i).2

/-- Accuracy-varying heterogeneous measured-cost lift from the generated
Assumption 3.2 kernels.  Integrability of the actual oracle and communication
observables is proved here rather than accepted as an endpoint premise. -/
theorem
    heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_generatedKernel
    {d n : Count} {Sample : Worker n → Type*}
    {b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (b : Accuracy → Worker n → Count) (Lcal : Worker n → ℝ)
    (hKernel : ∀ ε,
      HeterogeneousOnlineAssumption32GeneratedConditionalKernel
        (b0 := b0) A.problem
        (heterogeneousOnlineProcess (b := b ε) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b ε) (b0 := b0) A) Lcal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Accuracy → Count) (accuracy : Accuracy → Prop)
    (iterationScale : Accuracy → ℝ)
    (oracleScale : Worker n → Accuracy → ℝ)
    (communicationScale : Accuracy → ℝ)
    (hAccuracy : ∀ ε, accuracy ε)
    (hIteration : AccuracyIterationBigO (fun ε ↦ (K ε).1) iterationScale)
    (hOracle : ∀ i, AccuracyBigO
      (fun ε ↦ ((b ε i).1 : ℝ) + (K ε).1 *
        (A.refreshProbability * (b ε i).1 +
          2 * (1 - A.refreshProbability) * (b0 i).1))
      (oracleScale i))
    (hCommunication : AccuracyBigO
      (fun ε ↦ allWorkerCommunicationCount d (K ε) A.refreshProbability
        (expectedDensity A.quantizer)) communicationScale) :
    HeterogeneousOnlineScheduledMeasuredCostComplexity
      (b0 := b0) A x0 b K accuracy iterationScale oracleScale
        communicationScale := by
  unfold HeterogeneousOnlineScheduledMeasuredCostComplexity
  refine ⟨hAccuracy, hIteration, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε
    exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
      (b := b ε) (b0 := b0) A (K ε) i).1
  · rw [show (fun ε ↦ ∫ path,
        heterogeneousOnlineWorkerOracleCost
          (b := b ε) (b0 := b0) (Sample := Sample) (Ξ := Ξ) (K ε) i path
          ∂heterogeneousOnlinePathLaw (b := b ε) (b0 := b0) A) =
        (fun ε ↦ ((b ε i).1 : ℝ) + (K ε).1 *
          (A.refreshProbability * (b ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1)) by
      funext ε
      exact (heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
        (b := b ε) (b0 := b0) A (K ε) i).2]
    exact hOracle i
  · intro ε
    exact
      (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
        (b := b ε) (b0 := b0) A x0
          (heterogeneousOnlineCommunicationAELawRegularity_of_generatedKernel
            (b := b ε) (b0 := b0) A x0 Lcal (hKernel ε))
          hQ (K ε) i).1
  · apply accuracyBigO_of_nonneg_le hCommunication
    · intro ε
      exact integral_nonneg_of_ae (ae_of_all _ fun path ↦
        heterogeneousOnlineWorkerCommunicationCost_nonneg
          A x0 (K ε) i path)
    · intro ε
      have hζ : 0 ≤ expectedDensity A.quantizer :=
        expectedDensity_nonneg_of_unbiased hQ
      have hp0 : 0 ≤ A.refreshProbability := A.refresh_admissible.1.le
      have hp1 : 0 ≤ 1 - A.refreshProbability :=
        sub_nonneg.mpr A.refresh_admissible.2
      unfold allWorkerCommunicationCount
      positivity
    · intro ε
      exact
        (heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
          (b := b ε) (b0 := b0) A x0
            (heterogeneousOnlineCommunicationAELawRegularity_of_generatedKernel
              (b := b ε) (b0 := b0) A x0 Lcal (hKernel ε))
            hQ (K ε) i).2

/-- Executable measured release boundary for Remark D.2 from the literal
fixed-query moment contract and the generated conditional Assumption 3.2
kernel.  Accuracy and both actual cost integrals use the same worker-dependent
batch, horizon, executable process, and canonical path law. -/
theorem Remark_D2_heterogeneous_online_batches_executable_measured
    {d n : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (base : Accuracy → Worker n → Count) (b0 : Worker n → Count)
    (Llocal ℒlocal sigma : Worker n → ℝ) (ω fStar : ℝ)
    (hLower : HasUniformLowerBound (onlineLocalProblem A.problem) fStar)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (hBase : ∀ ε i, (b0 i).1 < (base ε i).1)
    (hBaseOrder : AccuracyTheta
      (fun ε ↦ heterogeneousOnlineVarianceTerm sigma (base ε))
      (fun ε ↦ (ε : ℝ) ^ 2))
    (hAssumption32 : ∀ ε,
      HeterogeneousOnlineAssumption32GeneratedConditionalKernel
        (b0 := b0) A.problem
        (heterogeneousOnlineProcess
          (b := heterogeneousOnlineExecutableBatchScheduleFromBase
            A sigma base ε) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw
          (b := heterogeneousOnlineExecutableBatchScheduleFromBase
            A sigma base ε) (b0 := b0) A) ℒlocal)
    (hStep : HeterogeneousVRStepsizeCondition A.stepSize
      (rootMeanSquare Llocal) (heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)
      A.refreshProbability ω n) :
    let chosenBatch :=
      heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base
    let P := onlineLocalProblem A.problem
    let ζ := expectedDensity A.quantizer
    let Δ := globalObjective P x0 - fStar
    let bracket := rootMeanSquare Llocal + Real.sqrt
      ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
        (ω * rootMeanSquare Llocal ^ 2 +
          (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
    let K := heterogeneousOnlineExecutableRemarkHorizon Δ A.stepSize bracket
    AccuracyTheta
        (fun ε ↦ heterogeneousOnlineVarianceTerm sigma (chosenBatch ε))
        (fun ε ↦ (ε : ℝ) ^ 2) ∧
      HeterogeneousOnlineScheduledMeasuredCostComplexity (b0 := b0)
        A x0 chosenBatch K
        (fun ε ↦ NonconvexAccuracy (K ε) P
          (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
          (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
        (fun ε ↦ Δ / (ε : ℝ) ^ 2 * bracket)
        (fun i ε ↦ (chosenBatch ε i).1 +
          Δ / (ε : ℝ) ^ 2 * bracket *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1))
        (fun ε ↦ d.1 + Δ / (ε : ℝ) ^ 2 * bracket *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) := by
  classical
  dsimp
  refine ⟨heterogeneousOnlineExecutableBatchScheduleFromBase_accuracyTheta
    A sigma base hBaseOrder, ?_⟩
  let chosenBatch :=
    heterogeneousOnlineExecutableBatchScheduleFromBase A sigma base
  let P := onlineLocalProblem A.problem
  let ζ : ℝ := expectedDensity A.quantizer
  let Δ : ℝ := globalObjective P x0 - fStar
  let bracket : ℝ := rootMeanSquare Llocal + Real.sqrt
    ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
      (ω * rootMeanSquare Llocal ^ 2 +
        (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0))
  let K := heterogeneousOnlineExecutableRemarkHorizon Δ A.stepSize bracket
  let iterationScale : Accuracy → ℝ := fun ε ↦
    Δ / (ε : ℝ) ^ 2 * bracket
  have hGapNonneg : 0 ≤ Δ := by
    dsimp [Δ, P]
    exact sub_nonneg.mpr (hLower x0)
  have hp : 0 < A.refreshProbability := A.refresh_admissible.1
  have hp1 : A.refreshProbability ≤ 1 := A.refresh_admissible.2
  have hζ : 0 ≤ ζ := by
    dsimp [ζ]
    exact expectedDensity_nonneg_of_unbiased hQuantizer
  have hBracketNonneg : 0 ≤ bracket := by
    dsimp [bracket]
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hChosenBatch : ∀ ε i, (b0 i).1 < (chosenBatch ε i).1 := by
    intro ε i
    exact heterogeneousOnlineExecutableBatchScheduleFromBase_admissible
      A sigma base b0 hBase ε i
  have hAccuracyPositive (hGapPos : 0 < Δ) (hBracketPos : 0 < bracket) :
      ∀ ε, NonconvexAccuracy (K ε) P
        (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε := by
    intro ε
    apply
      heterogeneousOnlineExecutableNonconvexAccuracy_of_half_optimization_budget_of_generatedKernel
        (K := K ε) A x0 base Llocal ℒlocal sigma ω fStar hLower hSmooth
          hLiteral hQuantizer ε (hAssumption32 ε) hStep
    simpa [K, chosenBatch, heterogeneousOnlineExecutableRemarkHorizon,
      hGapPos.ne', hBracketPos.ne'] using
        (heterogeneousOnlineExecutableHorizon_half_optimization_budget
          Δ A.stepSize hGapPos.le ε)
  have hOracleZero
      (hKOne : ∀ ε, (K ε).1 = 1)
      (hScaleZero : ∀ ε, iterationScale ε = 0) :
      ∀ i, AccuracyBigO
        (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + (K ε).1 *
          (A.refreshProbability * (chosenBatch ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1))
        (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1)) := by
    intro i
    unfold AccuracyBigO
    rw [Asymptotics.isBigO_iff]
    refine ⟨4, Filter.Eventually.of_forall ?_⟩
    intro ε
    let B : ℝ := (chosenBatch ε i).1
    let B0 : ℝ := (b0 i).1
    have hB : 0 < B := by dsimp [B]; exact_mod_cast (chosenBatch ε i).2
    have hB0 : 0 < B0 := by dsimp [B0]; exact_mod_cast (b0 i).2
    have hB0B : B0 < B := by
      dsimp [B0, B]
      exact_mod_cast hChosenBatch ε i
    have hOneSub : 0 ≤ 1 - A.refreshProbability := sub_nonneg.mpr hp1
    have hActualNonneg : 0 ≤ B + (A.refreshProbability * B +
        2 * (1 - A.refreshProbability) * B0) := by
      exact add_nonneg hB.le (add_nonneg (mul_nonneg hp.le hB.le)
        (mul_nonneg (mul_nonneg (by norm_num) hOneSub) hB0.le))
    rw [hKOne ε, hScaleZero ε]
    simp only [Nat.cast_one, one_mul, zero_mul, add_zero]
    rw [Real.norm_eq_abs, abs_of_nonneg hActualNonneg,
      Real.norm_eq_abs, abs_of_pos hB]
    dsimp [B, B0] at *
    nlinarith [mul_nonneg hp.le hB.le, mul_nonneg hOneSub hB0.le]
  have hCommunicationZero
      (hKOne : ∀ ε, (K ε).1 = 1)
      (hScaleZero : ∀ ε, iterationScale ε = 0) :
      AccuracyBigO
        (fun ε ↦ allWorkerCommunicationCount d (K ε)
          A.refreshProbability ζ)
        (fun ε ↦ (d.1 : ℝ) + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) := by
    have hdne : (d.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.2)
    rw [show (fun ε ↦ allWorkerCommunicationCount d (K ε)
          A.refreshProbability ζ) =
        (fun _ : Accuracy ↦ (d.1 : ℝ) +
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) by
      funext ε
      simp [allWorkerCommunicationCount, hKOne ε]]
    rw [show (fun ε ↦ (d.1 : ℝ) + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ)) =
        (fun _ : Accuracy ↦ (d.1 : ℝ)) by
      funext ε
      rw [hScaleZero ε]
      ring]
    exact Asymptotics.isBigO_const_const
      ((d.1 : ℝ) + (A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * ζ)) hdne accuracyToZero
  rcases hGapNonneg.eq_or_lt with hGapZero | hGapPos
  · have hΔ : Δ = 0 := hGapZero.symm
    have hKOne : ∀ ε, (K ε).1 = 1 := by
      intro ε
      dsimp [K, heterogeneousOnlineExecutableRemarkHorizon]
      rw [if_pos (Or.inl hΔ)]
      rfl
    have hScaleZero : ∀ ε, iterationScale ε = 0 := by
      intro ε
      simp [iterationScale, hΔ]
    apply heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_generatedKernel
      A x0 chosenBatch ℒlocal hAssumption32 hQuantizer K
      (fun ε ↦ NonconvexAccuracy (K ε) P
        (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
      iterationScale
      (fun i ε ↦ (chosenBatch ε i).1 + iterationScale ε *
        (A.refreshProbability * (chosenBatch ε i).1 +
          2 * (1 - A.refreshProbability) * (b0 i).1))
      (fun ε ↦ d.1 + iterationScale ε *
        (A.refreshProbability * d.1 +
          (1 - A.refreshProbability) * ζ))
    · intro ε
      apply
        heterogeneousOnlineExecutableNonconvexAccuracy_of_half_optimization_budget_of_generatedKernel
          (K := K ε) A x0 base Llocal ℒlocal sigma ω fStar hLower hSmooth
            hLiteral hQuantizer ε (hAssumption32 ε) hStep
      have hRawGap :
          globalObjective (onlineLocalProblem A.problem) x0 - fStar = 0 := by
        simpa [Δ, P] using hΔ
      rw [hRawGap]
      norm_num only [mul_zero, zero_div]
      exact div_nonneg (sq_nonneg (ε : ℝ)) (by norm_num)
    · refine Or.inl ⟨hScaleZero, ?_⟩
      unfold AccuracyBigO
      convert Asymptotics.isBigO_refl (fun _ : Accuracy ↦ (1 : ℝ))
        accuracyToZero using 1
      funext ε
      simp [hKOne ε]
    · exact hOracleZero hKOne hScaleZero
    · exact hCommunicationZero hKOne hScaleZero
  · rcases hBracketNonneg.eq_or_lt with hBracketZero | hBracketPos
    · have hbracket : bracket = 0 := hBracketZero.symm
      have hKOne : ∀ ε, (K ε).1 = 1 := by
        intro ε
        dsimp [K, heterogeneousOnlineExecutableRemarkHorizon]
        rw [if_pos (Or.inr hbracket)]
        rfl
      have hScaleZero : ∀ ε, iterationScale ε = 0 := by
        intro ε
        simp [iterationScale, hbracket]
      have hLzero : rootMeanSquare Llocal = 0 := by
        have hL : 0 ≤ rootMeanSquare Llocal := Real.sqrt_nonneg _
        have hsqrt : 0 ≤ Real.sqrt
            ((1 - A.refreshProbability) / (A.refreshProbability * n.1) *
              (ω * rootMeanSquare Llocal ^ 2 +
                (1 + ω) * heterogeneousFiniteBatchSmoothnessTerm ℒlocal b0)) :=
          Real.sqrt_nonneg _
        dsimp [bracket] at hbracket
        nlinarith
      have hGradZero := zero_rms_smooth_lower_bounded_global_gradient_eq_zero
        P Llocal fStar hLower hSmooth hLzero
      apply heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_generatedKernel
        A x0 chosenBatch ℒlocal hAssumption32 hQuantizer K
        (fun ε ↦ NonconvexAccuracy (K ε) P
          (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
          (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
        iterationScale
        (fun i ε ↦ (chosenBatch ε i).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1))
        (fun ε ↦ d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ))
      · intro ε
        unfold NonconvexAccuracy
        have hBoundary :=
          Theorem_D3_heterogeneous_online_VR_nonconvex_initialization_corrected_of_literal_and_generatedKernel
            (b := chosenBatch ε) (b0 := b0) (K := K ε)
              A x0 Llocal ℒlocal sigma ω fStar hLower hSmooth hLiteral
                hQuantizer (hAssumption32 ε) hStep
        refine ⟨hBoundary.1, ?_⟩
        have heq : (fun z ↦ ‖globalGradient P
            (uniformOutput (K := K ε)
              (heterogeneousOnlineProcess
                (b := chosenBatch ε) (b0 := b0) A x0) z)‖ ^ 2) =
            (fun _ ↦ (0 : ℝ)) := by
          funext z
          rw [hGradZero]
          norm_num
        rw [heq, integral_zero]
        positivity
      · refine Or.inl ⟨hScaleZero, ?_⟩
        unfold AccuracyBigO
        convert Asymptotics.isBigO_refl (fun _ : Accuracy ↦ (1 : ℝ))
          accuracyToZero using 1
        funext ε
        simp [hKOne ε]
      · exact hOracleZero hKOne hScaleZero
      · exact hCommunicationZero hKOne hScaleZero
    · have hKBigO : AccuracyBigO (fun ε ↦ ((K ε).1 : ℝ))
          iterationScale := by
        simpa [K, iterationScale, heterogeneousOnlineExecutableRemarkHorizon,
          hGapPos.ne', hBracketPos.ne'] using
            (heterogeneousOnlineExecutableHorizon_bigO_source_bracket
              Δ A.stepSize bracket hGapPos hBracketPos)
      have hScaleNonneg : ∀ᶠ ε in accuracyToZero, 0 ≤ iterationScale ε :=
        Filter.Eventually.of_forall fun ε ↦ by
          dsimp [iterationScale]
          positivity
      have hOracle : ∀ i, AccuracyBigO
          (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + (K ε).1 *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1))
          (fun ε ↦ ((chosenBatch ε i).1 : ℝ) + iterationScale ε *
            (A.refreshProbability * (chosenBatch ε i).1 +
              2 * (1 - A.refreshProbability) * (b0 i).1)) := by
        intro i
        unfold AccuracyBigO at hKBigO ⊢
        rcases hKBigO.exists_pos with ⟨C, hC, hKC⟩
        rw [Asymptotics.isBigO_iff']
        refine ⟨1 + C, by positivity, ?_⟩
        filter_upwards [hKC.bound] with ε hKc
        let B : ℝ := (chosenBatch ε i).1
        let payload : ℝ := A.refreshProbability * B +
          2 * (1 - A.refreshProbability) * (b0 i).1
        have hB : 0 < B := by
          dsimp [B]
          exact_mod_cast (chosenBatch ε i).2
        have hpayload : 0 ≤ payload := by
          dsimp [payload]
          exact add_nonneg
            (mul_nonneg hp.le (by positivity))
            (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp1))
              (by positivity))
        have hscale : 0 < iterationScale ε := by
          dsimp [iterationScale]
          exact mul_pos (div_pos hGapPos (sq_pos_of_pos ε.property))
            hBracketPos
        have hKn : ((K ε).1 : ℝ) ≤ C * iterationScale ε := by
          change ‖((K ε).1 : ℝ)‖ ≤ C * ‖iterationScale ε‖ at hKc
          simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity :
            0 ≤ ((K ε).1 : ℝ)), abs_of_pos hscale] using hKc
        change ‖B + ((K ε).1 : ℝ) * payload‖ ≤
          (1 + C) * ‖B + iterationScale ε * payload‖
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
            0 ≤ B + ((K ε).1 : ℝ) * payload),
          Real.norm_eq_abs, abs_of_pos
            (add_pos_of_pos_of_nonneg hB (mul_nonneg hscale.le hpayload))]
        nlinarith [mul_le_mul_of_nonneg_right hKn hpayload]
      let commPayload : ℝ := A.refreshProbability * d.1 +
        (1 - A.refreshProbability) * ζ
      have hdpos : 0 < (d.1 : ℝ) := by exact_mod_cast d.2
      have hCommPayloadPos : 0 < commPayload := by
        dsimp [commPayload]
        exact add_pos_of_pos_of_nonneg (mul_pos hp hdpos)
          (mul_nonneg (sub_nonneg.mpr hp1) hζ)
      have hCommunication : AccuracyBigO
          (fun ε ↦ allWorkerCommunicationCount d (K ε)
            A.refreshProbability ζ)
          (fun ε ↦ (d.1 : ℝ) + iterationScale ε *
            (A.refreshProbability * d.1 +
              (1 - A.refreshProbability) * ζ)) := by
        simpa [allWorkerCommunicationCount, commPayload] using
          (accuracyBigO_affine_cost_of_schedule
            (K := fun ε ↦ ((K ε).1 : ℝ))
            (scale := iterationScale) (init := (d.1 : ℝ))
            (actualPayload := commPayload) (targetPayload := commPayload)
            (payloadFactor := 1) hKBigO hdpos hCommPayloadPos.le
              hCommPayloadPos zero_lt_one (by simp) hScaleNonneg)
      apply heterogeneousOnlineScheduledMeasuredCostComplexity_of_bounds_of_generatedKernel
        A x0 chosenBatch ℒlocal hAssumption32 hQuantizer K
        (fun ε ↦ NonconvexAccuracy (K ε) P
          (heterogeneousOnlineProcess (b := chosenBatch ε) (b0 := b0) A x0)
          (heterogeneousOnlinePathLaw (b := chosenBatch ε) (b0 := b0) A) ε)
        iterationScale
        (fun i ε ↦ (chosenBatch ε i).1 + iterationScale ε *
          (A.refreshProbability * (chosenBatch ε i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1))
        (fun ε ↦ d.1 + iterationScale ε *
          (A.refreshProbability * d.1 +
            (1 - A.refreshProbability) * ζ))
      · exact hAccuracyPositive hGapPos hBracketPos
      · exact Or.inr hKBigO
      · exact hOracle
      · exact hCommunication


end MARINA
