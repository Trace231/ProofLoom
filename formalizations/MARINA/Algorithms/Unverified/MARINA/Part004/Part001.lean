import Algorithms.Unverified.MARINA.Part003

-- Aggregator for `Algorithms.Unverified.MARINA`. Source declarations live under `MARINA/`.

namespace MARINA

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-! ## Literal online moment boundary

Assumption 3.3 states only the workerwise fixed-query unbiasedness and
bounded-variance equations.  Adaptive-query regularity used by the generated
Algorithm 3 proofs is kept separate below. -/

/-- The literal fixed-query moment content of Assumption 3.3 / Eqs. (9)--(10).
This definition deliberately contains no differentiability, adaptive-law,
process-measurability, or cost-measurability premise. -/
def OnlineAssumption33Literal {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (σ : Worker n → ℝ) : Prop :=
  LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ

/-- Transparent identification of the public literal Assumption 3.3 boundary
with the previously isolated fixed-query moment predicate. -/
theorem onlineAssumption33Literal_iff_legacy {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (σ : Worker n → ℝ) :
    OnlineAssumption33Literal P σ ↔
      LegacyOnlineFixedQueryUnbiasedBoundedVariance P σ := by
  rfl

/-! ## Track-B adaptive sampled-gradient correction

The original-object obstruction proved below shows that fixed-query genuine
gradients can fail on a non-null-measurable generated query/sample diagonal.
The current proof route excludes that obstruction by requiring one
sampling-law-full set of sample losses that is differentiable at every query.
This is deliberately a separate correction, not part of literal Assumption
3.3.  It is the law-a.e. condition used by the existing forward-difference
construction of adaptive stochastic-gradient random variables. -/

/-- Explicit Track-B regularity correction used at the online release
boundary.  Unlike `OnlineAssumption33Literal`, this is not claimed by the
source: it supplies genuine gradients simultaneously at adaptive queries. -/
def OnlineAdaptiveSampleGradientRegularity {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) : Prop :=
  OnlineSampleLossDifferentiable P

/-- Transparent compatibility with the internal condition used by the
existing adaptive-law proofs. -/
theorem onlineAdaptiveSampleGradientRegularity_iff {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) :
    OnlineAdaptiveSampleGradientRegularity P ↔
      OnlineSampleLossDifferentiable P := by
  rfl

/-! The global condition above is retained for compatibility, but the
original generated-transition obstruction does not justify differentiability
of a sample loss away from query/sample pairs that can occur under an
Algorithm 3 law.  The following interface isolates the weaker law-level fact
actually needed at an adaptive fresh-sample call. -/

/-- Law-scoped Track-B correction for an adaptive sampled-gradient call.
For every possible law of the (past-measurable) query, the genuine gradient
exists almost everywhere after pairing that query with one fresh source
sample, and the corresponding totalized formal gradient is a random vector.

Unlike `OnlineSampleLossDifferentiable`, this does not require one
sample-law-full set of losses to be differentiable at every point.  It also
contains no moment, recurrence, process-measurability, cost-integrability, or
conclusion-shaped premise. -/
structure OnlineAdaptiveSampleGradientLawRegularity {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) : Prop where
  genuine_product_ae : ∀ (i : Worker n) (nu : Measure (Point d)),
    ∀ᵐ p ∂nu.prod (P.sampleLaw i),
      DifferentiableAt ℝ (P.sampleLoss i p.2) p.1
  gradient_product_aestronglyMeasurable :
    ∀ (i : Worker n) (nu : Measure (Point d)),
      AEStronglyMeasurable
        (fun p : Point d × Sample i ↦ stochasticGradient P i p.2 p.1)
        (nu.prod (P.sampleLaw i))

/-- The retained global sampled-loss condition is a sufficient compatibility
supplier for the weaker adaptive product-law correction.  This implication,
not an equivalence, records the strict direction used by legacy proofs. -/
theorem onlineAdaptiveSampleGradientLawRegularity_of_sampleLossDifferentiable
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (hDiff : OnlineSampleLossDifferentiable P) :
    OnlineAdaptiveSampleGradientLawRegularity P := by
  constructor
  · intro i nu
    letI : IsProbabilityMeasure (P.sampleLaw i) :=
      P.sampleLaw_isProbability i
    have hProd : ∀ᵐ p ∂nu.prod (P.sampleLaw i),
        Differentiable ℝ (P.sampleLoss i p.2) :=
      (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := nu) (ν := P.sampleLaw i)).tendsto_ae (hDiff i)
    exact hProd.mono (fun p hp ↦ hp.differentiableAt)
  · intro i nu
    exact stochasticGradient_product_aestronglyMeasurable_of_differentiable
      P hDiff i nu

/-- Compatibility spelling from the previously exposed global Track-B
predicate to the weaker law-level predicate. -/
theorem onlineAdaptiveSampleGradientLawRegularity_of_global
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample)
    (h : OnlineAdaptiveSampleGradientRegularity P) :
    OnlineAdaptiveSampleGradientLawRegularity P := by
  exact onlineAdaptiveSampleGradientLawRegularity_of_sampleLossDifferentiable
    P ((onlineAdaptiveSampleGradientRegularity_iff P).mp h)

/-- The law-level correction pulls back to an arbitrary a.e.-measurable
adaptive query and any measurable reindexing of one fresh sample having the
source law.  The first conjunct preserves the genuine-gradient semantics;
the second is the random-vector fact consumed by expectation proofs. -/
theorem stochasticGradient_randomQuery_product_regular_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*} {Q S : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Q] [MeasurableSpace S]
    (P : OnlineProblem d n Sample)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity P)
    (i : Worker n) (nuQ : Measure Q) (nuS : Measure S)
    [SFinite nuQ] [SFinite nuS]
    (query : Q → Point d) (sample : S → Sample i)
    (hquery : AEStronglyMeasurable query nuQ)
    (hsample : Measurable sample)
    (hsampleLaw : Measure.map sample nuS = P.sampleLaw i) :
    (∀ᵐ p ∂nuQ.prod nuS,
        DifferentiableAt ℝ (P.sampleLoss i (sample p.2)) (query p.1)) ∧
      AEStronglyMeasurable
        (fun p : Q × S ↦ stochasticGradient P i (sample p.2) (query p.1))
        (nuQ.prod nuS) := by
  let query' := hquery.mk query
  let pairMap : Q × S → Point d × Sample i :=
    fun p ↦ (query' p.1, sample p.2)
  have hquery' : Measurable query' := hquery.measurable_mk
  have hpairMap : Measurable pairMap :=
    (hquery'.comp measurable_fst).prodMk (hsample.comp measurable_snd)
  have hmap : Measure.map pairMap (nuQ.prod nuS) =
      (Measure.map query' nuQ).prod (P.sampleLaw i) := by
    rw [show pairMap = Prod.map query' sample by
      funext p
      rfl]
    calc
      Measure.map (Prod.map query' sample) (nuQ.prod nuS) =
          (Measure.map query' nuQ).prod (Measure.map sample nuS) :=
        (MeasureTheory.Measure.map_prod_map nuQ nuS hquery' hsample).symm
      _ = (Measure.map query' nuQ).prod (P.sampleLaw i) := by
        rw [hsampleLaw]
  have hqmp : Measure.QuasiMeasurePreserving pairMap (nuQ.prod nuS)
      ((Measure.map query' nuQ).prod (P.sampleLaw i)) :=
    ⟨hpairMap, by rw [hmap]⟩
  have hqueryAE : ∀ᵐ p ∂nuQ.prod nuS, query p.1 = query' p.1 :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst
      (μ := nuQ) (ν := nuS)).tendsto_ae hquery.ae_eq_mk
  constructor
  · have hGenuine := hqmp.tendsto_ae
      (hRegularity.genuine_product_ae i (Measure.map query' nuQ))
    filter_upwards [hGenuine, hqueryAE] with p hp hq
    simpa [pairMap, hq] using hp
  · have hGradient :=
      (hRegularity.gradient_product_aestronglyMeasurable i
        (Measure.map query' nuQ)).comp_quasiMeasurePreserving hqmp
    refine hGradient.congr (hqueryAE.mono ?_)
    intro p hp
    simp [pairMap, hp]

/-- The formerly bundled online variance premise is exactly the literal
fixed-query moments plus the separately classified Track-B correction. -/
theorem onlineUnbiasedBoundedVariance_iff_literal_and_adaptiveRegularity
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (σ : Worker n → ℝ) :
    OnlineUnbiasedBoundedVariance P σ ↔
      OnlineAssumption33Literal P σ ∧
        OnlineAdaptiveSampleGradientRegularity P := by
  rfl

/-! ## Genuine versus totalized sampled gradients

The source notation `∇f_ξ(x)` denotes a gradient that exists at the queried
sample and point.  By contrast, Mathlib's `gradient` (and hence
`stochasticGradient`) is a total function and returns a fallback value when
differentiability fails.  The following predicate names the source object,
and the transfer theorem records exactly when it agrees with the formal
totalization. -/

/-- A genuine sampled gradient at one worker, sample, and query.  This is an
existence-bearing relation, not a totalized oracle definition. -/
def GenuineSampleGradientAt {d n : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (i : Worker n) (xi : Sample i)
    (x g : Point d) : Prop :=
  HasGradientAt (P.sampleLoss i xi) g x

/-- A genuine sampled gradient is definitionally represented by the existing
`stochasticGradient` only after the `HasGradientAt` witness is supplied. -/
theorem stochasticGradient_eq_of_genuineSampleGradientAt
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {i : Worker n} {xi : Sample i}
    {x g : Point d} (h : GenuineSampleGradientAt P i xi x g) :
    stochasticGradient P i xi x = g := by
  exact h.gradient

/-- The weaker law-level correction supplies the source's genuine sampled
gradient object at every adaptive product-law call, with the existing
`stochasticGradient` as its proved formal representative. -/
theorem genuineSampleGradientAt_ae_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample}
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity P)
    (i : Worker n) (nu : Measure (Point d)) :
    ∀ᵐ p ∂nu.prod (P.sampleLaw i),
      GenuineSampleGradientAt P i p.2 p.1
        (stochasticGradient P i p.2 p.1) := by
  exact (hRegularity.genuine_product_ae i nu).mono
    (fun p hp ↦ hp.hasGradientAt)

/-- The genuine sampled-gradient difference represented by one Assumption 3.2
minibatch at two queries.  Unlike `onlineBatchDifference`, this relation
contains witnesses that every displayed source gradient actually exists. -/
def GenuineOnlineBatchDifferenceAt {d n b0 : Count}
    {Sample : Worker n → Type*} [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample)
    (batch : (w : Worker n) → Fin b0.1 → Sample w)
    (i : Worker n) (xNext x delta : Point d) : Prop :=
  ∃ gNext gCurrent : Fin b0.1 → Point d,
    (∀ j, GenuineSampleGradientAt P i (batch i j) xNext (gNext j)) ∧
    (∀ j, GenuineSampleGradientAt P i (batch i j) x (gCurrent j)) ∧
    delta = average (fun j ↦ gNext j - gCurrent j)

/-- Source-side Assumption 3.2 for the actual generated queries.  The random
variable is explicitly required to consist almost surely of genuine sampled
gradients; its remaining clauses are exactly the conditional mean and
mean-square bound printed in Eq. (8). -/
def OnlineAssumption32Genuine {d n b0 : Count}
    {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k i (path : Ω),
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      ∃ delta : ((w : Worker n) → Fin b0.1 → Sample w) → Point d,
        (∀ᵐ batch ∂onlineBatchLaw P b0,
          GenuineOnlineBatchDifferenceAt P batch i xNext x (delta batch)) ∧
        Integrable delta (onlineBatchLaw P b0) ∧
        Integrable (fun batch ↦
          ‖delta batch -
            localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2)
          (onlineBatchLaw P b0) ∧
        (∫ batch, delta batch ∂onlineBatchLaw P b0) =
          localGradientDifference (onlineLocalProblem P) i xNext x ∧
        (∫ batch,
            ‖delta batch -
              localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2
            ∂onlineBatchLaw P b0) ≤
          (ℒ i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)

/-- Law-a.e. form of source Assumption 3.2 for homogeneous online batches.
The conditional minibatch fiber is required at the generated queries almost
surely under the exact process law; no obligation is imposed on null paths. -/
def OnlineAssumption32GenuineAE {d n b0 : Count}
    {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k, ∀ᵐ path ∂pathLaw, ∀ i,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      ∃ delta : ((w : Worker n) → Fin b0.1 → Sample w) → Point d,
        (∀ᵐ batch ∂onlineBatchLaw P b0,
          GenuineOnlineBatchDifferenceAt P batch i xNext x (delta batch)) ∧
        Integrable delta (onlineBatchLaw P b0) ∧
        Integrable (fun batch ↦
          ‖delta batch -
            localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2)
          (onlineBatchLaw P b0) ∧
        (∫ batch, delta batch ∂onlineBatchLaw P b0) =
          localGradientDifference (onlineLocalProblem P) i xNext x ∧
        (∫ batch,
            ‖delta batch -
              localGradientDifference (onlineLocalProblem P) i xNext x‖ ^ 2
            ∂onlineBatchLaw P b0) ≤
          (ℒ i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)

/-- Law-a.e. formal Assumption 3.2 fiber for an arbitrary generated
homogeneous process.  This is the exact totalized-gradient object consumed by
the recurrence after the genuine-gradient identification is proved. -/
def OnlineAverageSmoothnessAE {d n b0 : Count}
    {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (ℒ : Worker n → ℝ) : Prop :=
  (∀ i, 0 ≤ ℒ i) ∧
    (∀ k, ∀ᵐ path ∂pathLaw, ∀ i,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let delta := localGradientDifference (onlineLocalProblem P) i xNext x
      let D := fun batch ↦ onlineBatchDifference P batch i xNext x
      Integrable D (onlineBatchLaw P b0) ∧
        Integrable (fun batch ↦ ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw P b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw P b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2 ∂onlineBatchLaw P b0) ≤
          (ℒ i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)

/-- The former every-path formulation remains an honest sufficient
compatibility supplier for the source-faithful law-a.e. boundary. -/
theorem onlineAssumption32GenuineAE_of_forallPath
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    (P : OnlineProblem d n Sample) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (ℒ : Worker n → ℝ)
    (h : OnlineAssumption32Genuine (b0 := b0) P run ℒ) :
    OnlineAssumption32GenuineAE (b0 := b0) P run pathLaw ℒ := by
  refine ⟨h.1, ?_⟩
  intro k
  filter_upwards [] with path
  intro i
  exact h.2 k i path

/-- Once the genuine gradients in an Assumption 3.2 minibatch exist, their
average is definitionally the existing formal batch difference. -/
theorem onlineBatchDifference_eq_of_genuineOnlineBatchDifferenceAt
    {d n b0 : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample}
    {batch : (w : Worker n) → Fin b0.1 → Sample w}
    {i : Worker n} {xNext x delta : Point d}
    (h : GenuineOnlineBatchDifferenceAt P batch i xNext x delta) :
    onlineBatchDifference P batch i xNext x = delta := by
  rcases h with ⟨gNext, gCurrent, hNext, hCurrent, rfl⟩
  unfold onlineBatchDifference
  congr 1
  funext j
  rw [stochasticGradient_eq_of_genuineSampleGradientAt (hNext j),
    stochasticGradient_eq_of_genuineSampleGradientAt (hCurrent j)]

/-- The genuine-gradient formulation of source Assumption 3.2 supplies the
legacy totalized formulation, but only through the explicit a.e. transfer
above. -/
theorem onlineAssumption32Genuine_to_onlineAverageSmoothness
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {ℒ : Worker n → ℝ}
    (h : OnlineAssumption32Genuine (b0 := b0) P run ℒ) :
    OnlineAverageSmoothness (b0 := b0) P run ℒ := by
  refine ⟨h.1, ?_⟩
  intro k i path
  rcases h.2 k i path with
    ⟨delta, hGenuine, hIntegrable, hResidualIntegrable, hMean, hVariance⟩
  have hEq : (fun batch ↦ onlineBatchDifference P batch i
      (run (k + 1) path).x (run k path).x) =ᵐ[onlineBatchLaw P b0] delta :=
    hGenuine.mono (fun _ hbatch ↦
      onlineBatchDifference_eq_of_genuineOnlineBatchDifferenceAt hbatch)
  have hResidualEq :
      (fun batch ↦
        ‖onlineBatchDifference P batch i
            (run (k + 1) path).x (run k path).x -
          localGradientDifference (onlineLocalProblem P) i
            (run (k + 1) path).x (run k path).x‖ ^ 2) =ᵐ[onlineBatchLaw P b0]
      (fun batch ↦
        ‖delta batch -
          localGradientDifference (onlineLocalProblem P) i
            (run (k + 1) path).x (run k path).x‖ ^ 2) := by
    filter_upwards [hEq] with batch hbatch
    rw [hbatch]
  refine ⟨hIntegrable.congr hEq.symm,
    hResidualIntegrable.congr hResidualEq.symm, ?_, ?_⟩
  · rw [integral_congr_ae hEq, hMean]
  · rw [integral_congr_ae hResidualEq]
    exact hVariance

/-- Source-to-formal transfer for the law-a.e. homogeneous Assumption 3.2
contract.  Both sides use the same generated process, path law, rounds,
workers, queries, and minibatch law.  The only object change is the proved
a.e. identification of genuine sampled-gradient differences with
`onlineBatchDifference`. -/
theorem onlineAssumption32GenuineAE_to_onlineAverageSmoothnessAE
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {pathLaw : Measure Ω} {ℒ : Worker n → ℝ}
    (h : OnlineAssumption32GenuineAE (b0 := b0) P run pathLaw ℒ) :
    OnlineAverageSmoothnessAE (b0 := b0) P run pathLaw ℒ := by
  refine ⟨h.1, ?_⟩
  intro k
  filter_upwards [h.2 k] with path hpath
  intro i
  rcases hpath i with
    ⟨delta, hGenuine, hIntegrable, hResidualIntegrable, hMean, hVariance⟩
  have hEq : (fun batch ↦ onlineBatchDifference P batch i
      (run (k + 1) path).x (run k path).x) =ᵐ[onlineBatchLaw P b0] delta :=
    hGenuine.mono (fun _ hbatch ↦
      onlineBatchDifference_eq_of_genuineOnlineBatchDifferenceAt hbatch)
  have hResidualEq :
      (fun batch ↦
        ‖onlineBatchDifference P batch i
            (run (k + 1) path).x (run k path).x -
          localGradientDifference (onlineLocalProblem P) i
            (run (k + 1) path).x (run k path).x‖ ^ 2) =ᵐ[onlineBatchLaw P b0]
      (fun batch ↦
        ‖delta batch -
          localGradientDifference (onlineLocalProblem P) i
            (run (k + 1) path).x (run k path).x‖ ^ 2) := by
    filter_upwards [hEq] with batch hbatch
    rw [hbatch]
  refine ⟨hIntegrable.congr hEq.symm,
    hResidualIntegrable.congr hResidualEq.symm, ?_, ?_⟩
  · rw [integral_congr_ae hEq, hMean]
  · rw [integral_congr_ae hResidualEq]
    exact hVariance

/-- Under the weak law-level Track-B correction, the existing formal
`OnlineAverageSmoothness` statement is also a genuine-gradient realization of
source Assumption 3.2.  The correction is used only to show that, at the two
generated queries of each finite minibatch, the displayed totalized
`stochasticGradient`s are almost surely genuine gradients.  All conditional
means and second-moment bounds are inherited unchanged from
`OnlineAverageSmoothness`.

Together with `onlineAssumption32Genuine_to_onlineAverageSmoothness`, this is
the source/formal transfer needed by the law-level recurrence route; it does
not assume a recurrence, process moment, or convergence conclusion. -/
theorem onlineAverageSmoothness_to_onlineAssumption32Genuine_of_lawRegularity
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {ℒ : Worker n → ℝ}
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity P)
    (h : OnlineAverageSmoothness (b0 := b0) P run ℒ) :
    OnlineAssumption32Genuine (b0 := b0) P run ℒ := by
  classical
  refine ⟨h.1, ?_⟩
  intro k i path
  letI : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  let x := (run k path).x
  let xNext := (run (k + 1) path).x
  let batchLaw := onlineBatchLaw P b0
  let delta := fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦
    onlineBatchDifference P batch i xNext x
  have hfixed (y : Point d) :
      ∀ᵐ xi ∂P.sampleLaw i,
        GenuineSampleGradientAt P i xi y (stochasticGradient P i xi y) := by
    let embed : Sample i → Point d × Sample i := fun xi ↦ (y, xi)
    have hembed : Measurable embed := measurable_const.prodMk measurable_id
    have hmap : Measure.map embed (P.sampleLaw i) =
        (Measure.dirac y).prod (P.sampleLaw i) := by
      simpa [embed] using (Measure.dirac_prod (ν := P.sampleLaw i) y).symm
    have hqmp : Measure.QuasiMeasurePreserving embed (P.sampleLaw i)
        ((Measure.dirac y).prod (P.sampleLaw i)) :=
      ⟨hembed, by rw [hmap]⟩
    exact hqmp.tendsto_ae
      (genuineSampleGradientAt_ae_of_lawRegularity
        hRegularity i (Measure.dirac y))
  have hcoord (j : Fin b0.1) : Measure.map
      (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i j)
      batchLaw = P.sampleLaw i := by
    simpa [batchLaw] using onlineBatchLaw_coordinate_marginal P i j
  have hat (y : Point d) (j : Fin b0.1) :
      ∀ᵐ batch ∂batchLaw,
        GenuineSampleGradientAt P i (batch i j) y
          (stochasticGradient P i (batch i j) y) := by
    let coord := fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i j
    have hcoordMeas : Measurable coord :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw (P.sampleLaw i) :=
      ⟨hcoordMeas, by rw [show Measure.map coord batchLaw = P.sampleLaw i by
        simpa [coord] using hcoord j]⟩
    exact hqmp.tendsto_ae (hfixed y)
  have hnext : ∀ᵐ batch ∂batchLaw, ∀ j : Fin b0.1,
      GenuineSampleGradientAt P i (batch i j) xNext
        (stochasticGradient P i (batch i j) xNext) :=
    ae_all_iff.2 (hat xNext)
  have hcurrent : ∀ᵐ batch ∂batchLaw, ∀ j : Fin b0.1,
      GenuineSampleGradientAt P i (batch i j) x
        (stochasticGradient P i (batch i j) x) :=
    ae_all_iff.2 (hat x)
  have hGenuine : ∀ᵐ batch ∂batchLaw,
      GenuineOnlineBatchDifferenceAt P batch i xNext x (delta batch) := by
    filter_upwards [hnext, hcurrent] with batch hn hc
    refine ⟨fun j ↦ stochasticGradient P i (batch i j) xNext,
      fun j ↦ stochasticGradient P i (batch i j) x, hn, hc, ?_⟩
    rfl
  rcases h.2 k i path with
    ⟨hIntegrable, hResidualIntegrable, hMean, hVariance⟩
  exact ⟨delta, hGenuine, hIntegrable, hResidualIntegrable, hMean, hVariance⟩

/-- Exact source/formal correspondence for Assumption 3.2 once the separately
classified law-level correction is present.  Both sides quantify over the
same generated process, rounds, workers, paths, and minibatch law. -/
theorem onlineAssumption32Genuine_iff_onlineAverageSmoothness_of_lawRegularity
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)]
    {P : OnlineProblem d n Sample} {run : ℕ → Ω → State d}
    {ℒ : Worker n → ℝ}
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity P) :
    OnlineAssumption32Genuine (b0 := b0) P run ℒ ↔
      OnlineAverageSmoothness (b0 := b0) P run ℒ := by
  constructor
  · exact onlineAssumption32Genuine_to_onlineAverageSmoothness
  · exact
      onlineAverageSmoothness_to_onlineAssumption32Genuine_of_lawRegularity
        hRegularity

/-! ## Generated proof-exact transition regularity

The recurrence proofs need the actual Algorithm 3 transition to be a random
state under the product of a past-state law and one fresh round.  The older
transition theorem obtains this from globally differentiable sample losses.
The following replacement uses only the accepted law-level Track-B
correction, coordinate by coordinate, and therefore does not reconstruct the
stronger compatibility predicate. -/

set_option maxHeartbeats 2000000 in
/-- One generated online Algorithm 3 step is a.e. measurable under an
arbitrary state law and the canonical fresh-round law from the weak adaptive
sample-gradient correction.  No fixed-query moment, recurrence, or endpoint
bound is assumed here. -/
theorem onlineStep_product_aemeasurable_of_state_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    [MeasurableSpace Q]
    (A : OnlineData d n Sample Ξ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (nu : Measure Q) [SFinite nu] (state : Q → State d)
    (hstate : AEMeasurable state nu) :
    AEMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
        onlineStep A (onlineDriverOfRoundNoise p.2) (state p.1))
      (nu.prod (onlineRoundLaw A)) := by
  classical
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
  let roundLaw := onlineRoundLaw (b := b) (b0 := b0) A
  have hx : AEStronglyMeasurable (fun q ↦ (state q).x) nu :=
    ((measurable_state_x d).comp_aemeasurable hstate).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun q ↦ (state q).g) nu :=
    ((measurable_state_g d).comp_aemeasurable hstate).aestronglyMeasurable
  have hxNext : AEStronglyMeasurable
      (fun q ↦ primalStep A.stepSize (state q)) nu :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable
      hstate).aestronglyMeasurable
  have hrefresh_sample_map (i : Worker n) (j : Fin b.1) :
      Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1 i j) roundLaw =
        A.problem.sampleLaw i := by
    calc
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1 i j)
          roundLaw =
          Measure.map (fun batch : (w : Worker n) → Fin b.1 → Sample w ↦
              batch i j)
            (Measure.map
              (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.1)
              roundLaw) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · fun_prop
      _ = Measure.map (fun batch : (w : Worker n) → Fin b.1 → Sample w ↦
              batch i j) (onlineBatchLaw A.problem b) := by
            rw [onlineRoundLaw_refreshBatch_marginal]
      _ = A.problem.sampleLaw i :=
        onlineBatchLaw_coordinate_marginal A.problem i j
  have hdifference_sample_map (i : Worker n) (j : Fin b0.1) :
      Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.2 i j) roundLaw =
        A.problem.sampleLaw i := by
    calc
      Measure.map (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.2 i j)
          roundLaw =
          Measure.map (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦
              batch i j)
            (Measure.map
              (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2.1.2)
              roundLaw) := by
                rw [MeasureTheory.Measure.map_map]
                · rfl
                · fun_prop
                · fun_prop
      _ = Measure.map (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦
              batch i j) (onlineBatchLaw A.problem b0) := by
            rw [onlineRoundLaw_differenceBatch_marginal]
      _ = A.problem.sampleLaw i :=
        onlineBatchLaw_coordinate_marginal A.problem i j
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
        onlineWorkerEstimator A (onlineDriverOfRoundNoise p.2) (state p.1) i)
      (nu.prod roundLaw) := by
    have hrefreshTerm (j : Fin b.1) : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
          stochasticGradient A.problem i (p.2.2.1.1 i j)
            (primalStep A.stepSize (state p.1)))
        (nu.prod roundLaw) :=
      (stochasticGradient_randomQuery_product_regular_of_lawRegularity
        A.problem hRegularity i nu roundLaw
          (fun q ↦ primalStep A.stepSize (state q))
          (fun z ↦ z.2.1.1 i j) hxNext (by fun_prop)
          (hrefresh_sample_map i j)).2
    have hrefresh : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
          average (fun j : Fin b.1 ↦
            stochasticGradient A.problem i (p.2.2.1.1 i j)
              (primalStep A.stepSize (state p.1))))
        (nu.prod roundLaw) := by
      unfold average SOptLib.finiteUniformAverage
      have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ ↦ hrefreshTerm j)).const_smul
          ((Fintype.card (Fin b.1) : ℝ)⁻¹)
      refine hsum.congr (Filter.Eventually.of_forall ?_)
      intro p
      simp [Finset.sum_apply]
    have hnextTerm (j : Fin b0.1) : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
          stochasticGradient A.problem i (p.2.2.1.2 i j)
            (primalStep A.stepSize (state p.1)))
        (nu.prod roundLaw) :=
      (stochasticGradient_randomQuery_product_regular_of_lawRegularity
        A.problem hRegularity i nu roundLaw
          (fun q ↦ primalStep A.stepSize (state q))
          (fun z ↦ z.2.1.2 i j) hxNext (by fun_prop)
          (hdifference_sample_map i j)).2
    have hcurrentTerm (j : Fin b0.1) : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
          stochasticGradient A.problem i (p.2.2.1.2 i j) (state p.1).x)
        (nu.prod roundLaw) :=
      (stochasticGradient_randomQuery_product_regular_of_lawRegularity
        A.problem hRegularity i nu roundLaw (fun q ↦ (state q).x)
          (fun z ↦ z.2.1.2 i j) hx (by fun_prop)
          (hdifference_sample_map i j)).2
    have hdiff : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
          onlineBatchDifference A.problem p.2.2.1.2 i
            (primalStep A.stepSize (state p.1)) (state p.1).x)
        (nu.prod roundLaw) := by
      unfold onlineBatchDifference average SOptLib.finiteUniformAverage
      have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ ↦ (hnextTerm j).sub (hcurrentTerm j))).const_smul
          ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
      refine hsum.congr (Filter.Eventually.of_forall ?_)
      intro p
      simp [Finset.sum_apply, Finset.sum_sub_distrib]
    have hcompression : Measurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦ p.2.2.2 i) := by
      fun_prop
    have hquantized : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
          A.quantizer.apply
            (onlineBatchDifference A.problem p.2.2.1.2 i
              (primalStep A.stepSize (state p.1)) (state p.1).x)
            (p.2.2.2 i)) (nu.prod roundLaw) :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hdiff.aemeasurable.prodMk hcompression.aemeasurable)).aestronglyMeasurable
    have hcarry : AEStronglyMeasurable
        (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
          (state p.1).g + A.quantizer.apply
            (onlineBatchDifference A.problem p.2.2.1.2 i
              (primalStep A.stepSize (state p.1)) (state p.1).x)
            (p.2.2.2 i)) (nu.prod roundLaw) :=
      hg.comp_fst.add hquantized
    have hrefreshSet : MeasurableSet
        {p : Q × OnlineRoundNoise n b b0 Sample Ξ | p.2.1 = true} := by
      exact (measurable_fst.comp measurable_snd) (measurableSet_singleton true)
    have hpiece := AEStronglyMeasurable.piecewise hrefreshSet
      hrefresh.restrict hcarry.restrict
    simpa [onlineWorkerEstimator, onlineDriverOfRoundNoise, onlineDifference,
      Set.piecewise] using hpiece
  have hnext : AEStronglyMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
        primalStep A.stepSize (state p.1)) (nu.prod roundLaw) :=
    hxNext.comp_fst
  have haverage : AEStronglyMeasurable
      (fun p : Q × OnlineRoundNoise n b b0 Sample Ξ ↦
        average (fun i : Worker n ↦
          onlineWorkerEstimator A (onlineDriverOfRoundNoise p.2) (state p.1) i))
      (nu.prod roundLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ ↦ hworker i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  exact (measurable_state_mk d).comp_aemeasurable
    (hnext.aemeasurable.prodMk haverage.aemeasurable)

set_option maxHeartbeats 2000000 in
/-- Every finite-prefix proof-exact Algorithm 3 state is a random state under
the prefix law from the weak adaptive-gradient correction.  This is the
strict-past induction used by the generated proof-exact process, not a
measurability premise supplied by a caller. -/
theorem onlineProofExactPrefixState_all_aemeasurable_of_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ) :
    ∀ k, AEMeasurable
      (onlineProofExactPrefixState A x0 hBatch fallback k)
      (onlineRoundPrefixLaw A k) := by
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
  haveI : IsProbabilityMeasure
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
    unfold onlineProofExactPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hprefix_meas (t : ℕ) : Measurable
      (onlineRoundPrefix (n := n) (b := b) (b0 := b0)
        (Sample := Sample) (Ξ := Ξ) t) :=
    measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  haveI (t : ℕ) : IsProbabilityMeasure (onlineRoundPrefixLaw A t) := by
    unfold onlineRoundPrefixLaw
    exact Measure.isProbabilityMeasure_map (hprefix_meas t).aemeasurable
  intro k
  induction k with
  | zero =>
      have hconst : onlineProofExactPrefixState A x0 hBatch fallback 0 =
          fun _ ↦ onlineProofExactInitialState A x0 := by
        funext pref
        rfl
      rw [hconst]
      exact measurable_const.aemeasurable
  | succ k ih =>
      let split : (Fin (k + 1) → OnlineRoundNoise n b b0 Sample Ξ) →
          (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
            OnlineRoundNoise n b b0 Sample Ξ :=
        fun pref ↦ ((fun j ↦ pref j.castSucc), pref (Fin.last k))
      have hsplit : Measurable split := by
        dsimp [split]
        fun_prop
      have hstep : AEMeasurable
          (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
              OnlineRoundNoise n b b0 Sample Ξ ↦
            onlineStep A (onlineDriverOfRoundNoise p.2)
              (onlineProofExactPrefixState A x0 hBatch fallback k p.1))
          ((onlineRoundPrefixLaw A k).prod (onlineRoundLaw A)) :=
        onlineStep_product_aemeasurable_of_state_lawRegularity
          A hRegularity (onlineRoundPrefixLaw A k)
            (onlineProofExactPrefixState A x0 hBatch fallback k) ih
      have honMap : AEMeasurable
          (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
              OnlineRoundNoise n b b0 Sample Ξ ↦
            onlineStep A (onlineDriverOfRoundNoise p.2)
              (onlineProofExactPrefixState A x0 hBatch fallback k p.1))
          (Measure.map split (onlineRoundPrefixLaw A (k + 1))) := by
        rw [show Measure.map split (onlineRoundPrefixLaw A (k + 1)) =
            (onlineRoundPrefixLaw A k).prod (onlineRoundLaw A) by
          simpa [split] using onlineRoundPrefixLaw_split_succ A k]
        exact hstep
      have hpull := honMap.comp_aemeasurable hsplit.aemeasurable
      refine hpull.congr (Filter.Eventually.of_forall ?_)
      intro pref
      simpa [split, Function.comp_def] using
        (onlineProofExactPrefixState_succ A x0 hBatch fallback k pref).symm

/-- Every state of the proof-exact Algorithm 3 process is a random state under
its canonical round-only path law from the weak Track-B correction.  The
statement intentionally needs neither literal moments nor the stronger global
sample-loss predicate: moments enter only when integrability is proved. -/
theorem onlineProofExactProcess_aemeasurable_of_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) :
    AEMeasurable
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch k)
      (onlineProofExactPathLaw (b := b) (b0 := b0) A) := by
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
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  have hpref : AEMeasurable
      (onlineProofExactPrefixState A x0 hBatch fallback k)
      (onlineRoundPrefixLaw A k) :=
    onlineProofExactPrefixState_all_aemeasurable_of_lawRegularity
      A x0 hBatch hRegularity fallback k
  have hprefix : Measurable
      (onlineRoundPrefix (n := n) (b := b) (b0 := b0)
        (Sample := Sample) (Ξ := Ξ) k) :=
    measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hpull := hpref.comp_aemeasurable hprefix.aemeasurable
  change AEMeasurable
    (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch k) law
  refine hpull.congr (Filter.Eventually.of_forall ?_)
  intro path
  apply onlineProofExactProcess_congr_prefix A x0 hBatch k
  intro t ht
  simp [onlineRoundPrefix, onlineExtendRoundPrefix, ht]


/-- The support count is jointly measurable in the adaptive message input and
the compressor sample. -/
theorem quantizerNonzeroCount_joint_measurable
    {d : Count} {Ξ : Type*} [MeasurableSpace Ξ] (Q : Quantizer d Ξ) :
    Measurable (fun p : Point d × Ξ =>
      quantizerNonzeroCount Q p.1 p.2) := by
  classical
  rw [show (fun p : Point d × Ξ => quantizerNonzeroCount Q p.1 p.2) =
      fun p => ∑ j : Fin d.1,
        if Q.apply p.1 p.2 j ≠ 0 then (1 : ℝ) else 0 by
    funext p
    unfold quantizerNonzeroCount
    exact Finset.natCast_card_filter
      (fun j : Fin d.1 => Q.apply p.1 p.2 j ≠ 0) Finset.univ]
  apply Finset.measurable_sum
  intro j _
  have hj : Measurable (fun p : Point d × Ξ => Q.apply p.1 p.2 j) :=
    (EuclideanSpace.proj j).continuous.measurable.comp
      Q.apply.measurable_uncurry
  have hzero : MeasurableSet {p : Point d × Ξ | Q.apply p.1 p.2 j = 0} :=
    hj (measurableSet_singleton 0)
  exact Measurable.ite hzero.compl measurable_const measurable_const

/-- Pointwise finite-dimensional bound for every actual compressed message. -/
theorem quantizerNonzeroCount_le_dimension
    {d : Count} {Ξ : Type*} [MeasurableSpace Ξ] (Q : Quantizer d Ξ)
    (v : Point d) (ξ : Ξ) : quantizerNonzeroCount Q v ξ ≤ d.1 := by
  have hcard :
      (Finset.univ.filter fun j : Fin d.1 => Q.apply v ξ j ≠ 0).card ≤ d.1 := by
    simpa using
      (Finset.card_filter_le Finset.univ
        (fun j : Fin d.1 => Q.apply v ξ j ≠ 0))
  unfold quantizerNonzeroCount
  exact_mod_cast hcard

/-- Definition 1.1 gives an upper bound for every fixed message input.  It is
not, in general, an equality for adaptive inputs. -/
theorem integral_quantizerNonzeroCount_le_expectedDensity
    {d : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    {Q : Quantizer d Ξ} {ω : ℝ} (hQ : IsUnbiasedQuantizer Q ω)
    (v : Point d) :
    (∫ ξ, quantizerNonzeroCount Q v ξ ∂Q.law) ≤ expectedDensity Q := by
  letI : IsProbabilityMeasure Q.law := Q.law_isProbability
  rw [ExpectedDensity_Definition]
  have hSemantics : ExpectedDensitySemantics Q :=
    expectedDensitySemantics_of_unbiased hQ
  apply le_csSup
  · refine ⟨(d.1 : ℝ), ?_⟩
    rintro y ⟨u, rfl⟩
    have hmono := MeasureTheory.integral_mono (hSemantics u)
      (integrable_const (d.1 : ℝ))
      (fun ξ => quantizerNonzeroCount_le_dimension Q u ξ)
    simpa using hmono
  · exact ⟨v, rfl⟩

/-- An adaptive message input independent of its fresh compressor sample has
expected support at most Definition 1.1's supremum. -/
theorem adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
    {Ω : Type*} [MeasurableSpace Ω] {d : Count} {Ξ : Type*}
    [MeasurableSpace Ξ] (P : Measure Ω) [IsProbabilityMeasure P]
    {Q : Quantizer d Ξ} {ω : ℝ} (hQ : IsUnbiasedQuantizer Q ω)
    (message : Ω → Point d) (sample : Ω → Ξ)
    (hmessage : Measurable message) (hsample : Measurable sample)
    (hindep : ProbabilityTheory.IndepFun message sample P)
    (hsampleLaw : Measure.map sample P = Q.law) :
    Integrable (fun path => quantizerNonzeroCount Q (message path) (sample path)) P ∧
      (∫ path, quantizerNonzeroCount Q (message path) (sample path) ∂P) ≤
        expectedDensity Q := by
  letI : IsProbabilityMeasure Q.law := Q.law_isProbability
  let φ : Point d → Ξ → ℝ := fun v ξ => quantizerNonzeroCount Q v ξ
  have hφ : Measurable (Function.uncurry φ) := by
    simpa [φ, Function.uncurry] using quantizerNonzeroCount_joint_measurable Q
  have hfixedInt (v : Point d) : Integrable (φ v) Q.law :=
    expectedDensitySemantics_of_unbiased hQ v
  have hfixedBound (v : Point d) :
      (∫ ξ, φ v ξ ∂Q.law) ≤ expectedDensity Q := by
    simpa [φ] using integral_quantizerNonzeroCount_le_expectedDensity hQ v
  have hcompInt : Integrable (fun path => φ (message path) (sample path)) P := by
    apply integrable_comp_of_indep_fixed_integral_bound
      (P := P) (ν := Q.law) (C := expectedDensity Q)
      hφ hmessage hsample hindep hsampleLaw
    · intro v ξ
      unfold φ quantizerNonzeroCount
      positivity
    · exact expectedDensity_nonneg_of_unbiased hQ
    · exact hfixedInt
    · exact hfixedBound
  refine ⟨by simpa [φ] using hcompInt, ?_⟩
  exact integral_comp_le_of_indep_fixed_integral_bound
    (P := P) (ν := Q.law) (X := message) (Y := sample)
    hφ hmessage hsample hindep hsampleLaw hcompInt hfixedBound

/-! ## Measured finite-horizon costs

These random variables count the messages and oracle evaluations produced by
the generated Algorithms 1--4.  In particular, their non-refresh communication
branches inspect the actual quantized difference supplied to the corresponding
process transition; the older closed-form count expressions remain analytic
targets rather than definitions of measured cost. -/

/-- Algorithm 1 communication sent by worker `i` through the first `K` rounds,
including its dense initialization message. -/
noncomputable def basicWorkerCommunicationCost
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (K : Count) (i : Worker n)
    (path : ℕ → BasicRoundNoise n Ξ) : ℝ :=
  (d.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path k).1 then (d.1 : ℝ) else
      quantizerNonzeroCount A.quantizer
        (localGradientDifference A.problem i
          (primalStep A.stepSize (marinaProcess A x0 k path))
          (marinaProcess A x0 k path).x)
        ((path k).2 i)

/-- Finite-sum VR-MARINA communication sent by worker `i` through the first
`K` rounds, including its dense initialization message. -/
noncomputable def finiteSumWorkerCommunicationCost
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (K : Count) (i : Worker n)
    (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) : ℝ :=
  (d.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path k).1 then (d.1 : ℝ) else
      let s := finiteSumProcess (b0 := b0) A x0 k path
      quantizerNonzeroCount A.quantizer
        (finiteSumBatchDifference A.problem (path k).2.1 i
          (primalStep A.stepSize s) s.x)
        ((path k).2.2 i)

/-- Finite-sum VR-MARINA stochastic-gradient evaluations made by worker `i`.
The non-refresh difference evaluates every one of its `b0` samples at both
query points. -/
def finiteSumWorkerOracleCost
    {n m b0 : Count} {Ξ : Type*} (K : Count) (_i : Worker n)
    (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) : ℝ :=
  (m.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path k).1 then (m.1 : ℝ) else 2 * (b0.1 : ℝ)

/-- Executable online VR-MARINA communication sent by worker `i` through the
first `K` rounds, on the full experiment that contains its sampled initializer. -/
noncomputable def onlineWorkerCommunicationCost
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (K : Count) (i : Worker n)
    (path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) : ℝ :=
  (d.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path.2 k).1 then (d.1 : ℝ) else
      let s := onlineProcess A x0 hBatch k path
      quantizerNonzeroCount A.quantizer
        (onlineBatchDifference A.problem (path.2 k).2.1.2 i
          (primalStep A.stepSize s) s.x)
        ((path.2 k).2.2 i)

/-- Executable online VR-MARINA stochastic-gradient evaluations made by
worker `i`.  The initial `b` calls belong only to `onlineProcess`; each
non-refresh difference makes two calls for each of its `b0` samples. -/
def onlineWorkerOracleCost
    {n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    (K : Count) (_i : Worker n)
    (path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) : ℝ :=
  (b.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path.2 k).1 then (b.1 : ℝ) else 2 * (b0.1 : ℝ)

/-- Remark D.1's communication sent by worker `i` through the first `K`
heterogeneous finite-sum rounds.  The non-refresh message is the actual
worker-dependent minibatch difference used by
`heterogeneousFiniteSumProcess`. -/
noncomputable def heterogeneousFiniteSumWorkerCommunicationCost
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d) (K : Count)
    (i : Worker n)
    (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) : ℝ :=
  (d.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path k).1 then (d.1 : ℝ) else
      let s := heterogeneousFiniteSumProcess (b0 := b0) A x0 k path
      quantizerNonzeroCount A.quantizer
        (heterogeneousFiniteSumBatchDifference A.problem b0 (path k).2.1 i
          (primalStep A.stepSize s) s.x)
        ((path k).2.2 i)

/-- Remark D.1's per-worker oracle calls.  Worker `i` uses all `m`
components at initialization and on refresh, and evaluates each of its
`b0 i` difference samples at both query points otherwise. -/
def heterogeneousFiniteSumWorkerOracleCost
    {n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    (K : Count) (i : Worker n)
    (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) : ℝ :=
  (m.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path k).1 then (m.1 : ℝ) else 2 * ((b0 i).1 : ℝ)

/-- Remark D.2's communication sent by worker `i` through the first `K`
heterogeneous executable online rounds.  The domain includes the actual
worker-dependent initialization minibatch used by
`heterogeneousOnlineProcess`. -/
noncomputable def heterogeneousOnlineWorkerCommunicationCost
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (K : Count)
    (i : Worker n)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) : ℝ :=
  (d.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path.2 k).1 then (d.1 : ℝ) else
      let s := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path
      quantizerNonzeroCount A.quantizer
        (heterogeneousOnlineBatchDifference A.problem b0
          (path.2 k).2.1.2 i (primalStep A.stepSize s) s.x)
        ((path.2 k).2.2 i)

/-- Remark D.2's per-worker oracle calls on the executable heterogeneous
Algorithm 3 experiment.  The leading term belongs to the sampled initializer,
and every non-refresh difference sample is evaluated twice. -/
def heterogeneousOnlineWorkerOracleCost
    {n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    (K : Count) (i : Worker n)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) : ℝ :=
  ((b i).1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path.2 k).1 then ((b i).1 : ℝ) else 2 * ((b0 i).1 : ℝ)

/-- Total PP-MARINA communication through the first `K` rounds.  A refresh
sends one dense message from every worker.  A non-refresh sums over all `r`
sampled-client occurrences, so repeated clients are counted repeatedly. -/
noncomputable def ppTotalCommunicationCost
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (K : Count)
    (path : ℕ → PPRoundNoise n r Ξ) : ℝ :=
  (d.1 : ℝ) * (n.1 : ℝ) + ∑ k ∈ Finset.range K.1,
    if (path k).1 then (d.1 : ℝ) * (n.1 : ℝ) else
      let s := ppProcess (r := r) A x0 k path
      ∑ j : Fin r.1,
        quantizerNonzeroCount A.quantizer
          (localGradientDifference A.problem ((path k).2.1 j)
            (primalStep A.stepSize s) s.x)
          ((path k).2.2 j)

/-- The true mass of the canonical refresh coin. -/
theorem refreshLaw_true_real (p : ℝ) (hp : RefreshProbabilityAdmissible p) :
    (refreshLaw p hp).real ({true} : Set Bool) = p := by
  rw [measureReal_def]
  unfold refreshLaw
  rw [PMF.toMeasure_apply_singleton _ true (measurableSet_singleton true)]
  simp [PMF.bernoulli_apply]

/-- The false mass of the canonical refresh coin. -/
theorem refreshLaw_false_real (p : ℝ) (hp : RefreshProbabilityAdmissible p) :
    (refreshLaw p hp).real ({false} : Set Bool) = 1 - p := by
  rw [measureReal_def]
  unfold refreshLaw
  rw [PMF.toMeasure_apply_singleton _ false (measurableSet_singleton false)]
  simp only [PMF.bernoulli_apply, Bool.cond_false]
  let pNN : NNReal := ⟨p, le_of_lt hp.1⟩
  have hpNN : pNN ≤ (1 : NNReal) := by exact_mod_cast hp.2
  change ((1 - pNN : NNReal) : ℝ) = 1 - p
  rw [NNReal.coe_sub hpNN]
  rfl

/-- Expectation of one canonical refresh/non-refresh scalar branch. -/
theorem integral_refreshLaw_if (p : ℝ) (hp : RefreshProbabilityAdmissible p)
    (refreshCost differenceCost : ℝ) :
    (∫ c : Bool, (if c then refreshCost else differenceCost) ∂refreshLaw p hp) =
      p * refreshCost + (1 - p) * differenceCost := by
  letI : IsProbabilityMeasure (refreshLaw p hp) := by
    unfold refreshLaw
    infer_instance
  rw [MeasureTheory.integral_fintype]
  · simp [refreshLaw_true_real p hp, refreshLaw_false_real p hp]
  · exact Integrable.of_finite

/-- The refresh coordinate of every finite-sum path round has the canonical
Bernoulli law, independently of the admissible worker batch schedule. -/
theorem finiteSumPathLaw_refresh_marginal
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ) :
    Measure.map
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).1)
        (finiteSumPathLaw A batchLaw) =
      refreshLaw A.refreshProbability A.refresh_admissible := by
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  calc
    Measure.map
        (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).1)
        (finiteSumPathLaw A batchLaw) =
        Measure.map Prod.fst
          (Measure.map
            (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k)
            (finiteSumPathLaw A batchLaw)) := by
      rw [Measure.map_map measurable_fst (measurable_pi_apply k)]
      rfl
    _ = Measure.map Prod.fst
        (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)) := by
      rw [finiteSumPathLaw_round_marginal A batchLaw hBatchLaw k]
    _ = refreshLaw A.refreshProbability A.refresh_admissible := by
      simp [finiteSumRoundLaw]

/-- The refresh coordinate of every executable online path round has the
canonical Bernoulli law; the sampled initializer remains part of the domain. -/
theorem onlinePathLaw_refresh_marginal
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) :
    Measure.map
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).1)
        (onlinePathLaw A) =
      refreshLaw A.refreshProbability A.refresh_admissible := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
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
  have hround :
      Measure.map
          (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k)
          (onlinePathLaw A) = onlineRoundLaw A := by
    calc
      Measure.map
          (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
            (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k)
          (onlinePathLaw A) =
          Measure.map (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            stream k) (Measure.map Prod.snd (onlinePathLaw A)) := by
        simpa only [Function.comp_apply] using
          (Measure.map_map (measurable_pi_apply k) measurable_snd
            (μ := onlinePathLaw A)).symm
      _ = Measure.map (fun stream : ℕ → OnlineRoundNoise n b b0 Sample Ξ =>
            stream k) (SOptLib.iidStreamLaw (onlineRoundLaw A)) := by
        unfold onlinePathLaw
        rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = onlineRoundLaw A :=
        SOptLib.iidStreamLaw_map_eval (onlineRoundLaw A) k
  calc
    Measure.map
        (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
          (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => (path.2 k).1)
        (onlinePathLaw A) =
        Measure.map Prod.fst
          (Measure.map
            (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k)
            (onlinePathLaw A)) := by
      rw [Measure.map_map measurable_fst
        ((measurable_pi_apply k).comp measurable_snd)]
      rfl
    _ = Measure.map Prod.fst (onlineRoundLaw A) := by rw [hround]
    _ = refreshLaw A.refreshProbability A.refresh_admissible := by
      simp [onlineRoundLaw]

/-- The refresh coordinate of the canonical Remark D.1 path retains the
shared Bernoulli marginal while the worker-dependent minibatches are sampled
from their independent product law. -/
theorem heterogeneousFiniteSumPathLaw_refresh_marginal
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (k : ℕ) :
    Measure.map
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          (path k).1)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) =
      refreshLaw A.refreshProbability A.refresh_admissible := by
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (workerBatchLaw t i) :=
    hWorkerBatchLaw t i
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
  calc
    Measure.map
        (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
          (path k).1)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) =
        Measure.map Prod.fst
          (Measure.map
            (fun path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ =>
              path k)
            (heterogeneousFiniteSumPathLaw A
              (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))) := by
      rw [Measure.map_map measurable_fst (measurable_pi_apply k)]
      rfl
    _ = Measure.map Prod.fst
        (heterogeneousFiniteSumRoundLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw k)) := by
      rw [heterogeneousFiniteSumPathLaw_round_marginal
        A workerBatchLaw hWorkerBatchLaw k]
    _ = refreshLaw A.refreshProbability A.refresh_admissible := by
      simp [heterogeneousFiniteSumRoundLaw]

/-- The refresh coordinate of the full executable Remark D.2 experiment has
the canonical Bernoulli marginal; the worker-dependent sampled initializer
remains in the path domain. -/
theorem heterogeneousOnlinePathLaw_refresh_marginal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (k : ℕ) :
    Measure.map
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
          (path.2 k).1)
        (heterogeneousOnlinePathLaw A) =
      refreshLaw A.refreshProbability A.refresh_admissible := by
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
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
  have hround :
      Measure.map
          (fun path : HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
            path.2 k)
          (heterogeneousOnlinePathLaw A) =
        heterogeneousOnlineRoundLaw A := by
    calc
      Measure.map
          (fun path : HeterogeneousOnlineBatch n Sample b ×
              (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
            path.2 k)
          (heterogeneousOnlinePathLaw A) =
          Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              stream k)
            (Measure.map Prod.snd (heterogeneousOnlinePathLaw A)) := by
        simpa only [Function.comp_apply] using
          (Measure.map_map (measurable_pi_apply k) measurable_snd
            (μ := heterogeneousOnlinePathLaw A)).symm
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k)
          (SOptLib.iidStreamLaw (heterogeneousOnlineRoundLaw A)) := by
        unfold heterogeneousOnlinePathLaw
        rw [Measure.map_snd_prod, measure_univ, one_smul]
      _ = heterogeneousOnlineRoundLaw A :=
        SOptLib.iidStreamLaw_map_eval (heterogeneousOnlineRoundLaw A) k
  calc
    Measure.map
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
          (path.2 k).1)
        (heterogeneousOnlinePathLaw A) =
        Measure.map Prod.fst
          (Measure.map
            (fun path : HeterogeneousOnlineBatch n Sample b ×
                (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
              path.2 k)
            (heterogeneousOnlinePathLaw A)) := by
      rw [Measure.map_map measurable_fst
        ((measurable_pi_apply k).comp measurable_snd)]
      rfl
    _ = Measure.map Prod.fst (heterogeneousOnlineRoundLaw A) := by
      rw [hround]
    _ = refreshLaw A.refreshProbability A.refresh_admissible := by
      simp [heterogeneousOnlineRoundLaw]

/-- Finite-horizon accounting lemma for costs driven by canonical refresh
coins.  It supplies both integrability and the exact expectation, so the
specialized oracle theorems below cannot fall back to totalized integrals. -/
theorem integrable_and_integral_refresh_cost
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (coin : ℕ → Ω → Bool) (K : Count) (p : ℝ)
    (hp : RefreshProbabilityAdmissible p)
    (initialCost refreshCost differenceCost : ℝ)
    (hcoin : ∀ k, Measurable (coin k))
    (hmarginal : ∀ k, Measure.map (coin k) μ = refreshLaw p hp) :
    Integrable
        (fun path => initialCost + ∑ k ∈ Finset.range K.1,
          if coin k path then refreshCost else differenceCost) μ ∧
      (∫ path, initialCost + ∑ k ∈ Finset.range K.1,
          (if coin k path then refreshCost else differenceCost) ∂μ) =
        initialCost + K.1 *
          (p * refreshCost + (1 - p) * differenceCost) := by
  let term : ℕ → Ω → ℝ := fun k path =>
    if coin k path then refreshCost else differenceCost
  have htermMeas (k : ℕ) : Measurable (term k) := by
    dsimp [term]
    exact Measurable.ite (hcoin k (measurableSet_singleton true))
      measurable_const measurable_const
  have htermInt (k : ℕ) : Integrable (term k) μ := by
    apply integrable_of_measurable_bounded_real
      (C := max |refreshCost| |differenceCost|) (htermMeas k)
    intro path
    dsimp [term]
    split <;> simp_all
  have hsumInt : Integrable
      (fun path => ∑ k ∈ Finset.range K.1, term k path) μ := by
    exact MeasureTheory.integrable_finset_sum _ fun k _ => htermInt k
  have htotalInt : Integrable
      (fun path => initialCost + ∑ k ∈ Finset.range K.1, term k path) μ :=
    (integrable_const initialCost).add hsumInt
  refine ⟨by simpa [term] using htotalInt, ?_⟩
  have htermExpectation (k : ℕ) :
      (∫ path, term k path ∂μ) =
        p * refreshCost + (1 - p) * differenceCost := by
    calc
      (∫ path, term k path ∂μ) =
          ∫ c : Bool, (if c then refreshCost else differenceCost)
            ∂Measure.map (coin k) μ := by
        symm
        exact MeasureTheory.integral_map (hcoin k).aemeasurable
          (by fun_prop)
      _ = ∫ c : Bool, (if c then refreshCost else differenceCost)
          ∂refreshLaw p hp := by rw [hmarginal k]
      _ = p * refreshCost + (1 - p) * differenceCost :=
        integral_refreshLaw_if p hp refreshCost differenceCost
  change (∫ path, initialCost + ∑ k ∈ Finset.range K.1, term k path ∂μ) = _
  rw [MeasureTheory.integral_add (integrable_const initialCost) hsumInt,
    MeasureTheory.integral_finset_sum (Finset.range K.1)
      (fun k _ => htermInt k)]
  simp [htermExpectation]
  ring

/-- Exact per-worker Algorithm 2 oracle expectation under an arbitrary
admissible (possibly time-inhomogeneous) canonical batch schedule. -/
theorem finiteSumWorkerOracleCost_integrable_and_expectation
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    (K : Count) (i : Worker n) :
    Integrable (finiteSumWorkerOracleCost (Ξ := Ξ) K i)
        (finiteSumPathLaw A batchLaw) ∧
      (∫ path, finiteSumWorkerOracleCost (Ξ := Ξ) K i path
          ∂finiteSumPathLaw A batchLaw) =
        finiteSumOracleCallCount m b0 K A.refreshProbability := by
  letI (t : ℕ) (w : Worker n) : IsProbabilityMeasure (batchLaw t w) :=
    hBatchLaw t w
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure (finiteSumPathLaw A batchLaw) := by
    unfold finiteSumPathLaw
    infer_instance
  have h := integrable_and_integral_refresh_cost
    (μ := finiteSumPathLaw A batchLaw)
    (coin := fun k (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) => (path k).1)
    K A.refreshProbability A.refresh_admissible
    (m.1 : ℝ) (m.1 : ℝ) (2 * (b0.1 : ℝ))
    (fun k => (measurable_fst.comp (measurable_pi_apply k)))
    (finiteSumPathLaw_refresh_marginal A batchLaw hBatchLaw)
  constructor
  · change Integrable
      (fun path => (m.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        if (path k).1 then (m.1 : ℝ) else 2 * (b0.1 : ℝ))
      (finiteSumPathLaw A batchLaw)
    exact h.1
  · change (∫ path, (m.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        (if (path k).1 then (m.1 : ℝ) else 2 * (b0.1 : ℝ))
        ∂finiteSumPathLaw A batchLaw) = _
    rw [h.2]
    unfold finiteSumOracleCallCount
    ring

/-- Exact per-worker executable Algorithm 3 oracle expectation on the full
`onlinePathLaw` experiment.  This theorem deliberately has no proof-exact
initializer in its statement. -/
theorem onlineWorkerOracleCost_integrable_and_expectation
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (K : Count) (i : Worker n) :
    Integrable (onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) K i)
        (onlinePathLaw (b := b) (b0 := b0) A) ∧
      (∫ path, onlineWorkerOracleCost (Sample := Sample) (Ξ := Ξ) K i path
          ∂onlinePathLaw (b := b) (b0 := b0) A) =
        onlineOracleCallCount b b0 K A.refreshProbability := by
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
  haveI : IsProbabilityMeasure (SOptLib.iidStreamLaw
      (onlineRoundLaw (b := b) (b0 := b0) A)) := by
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure (onlinePathLaw (b := b) (b0 := b0) A) := by
    unfold onlinePathLaw
    infer_instance
  have h := integrable_and_integral_refresh_cost
    (μ := onlinePathLaw (b := b) (b0 := b0) A)
    (coin := fun k (path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) => (path.2 k).1)
    K A.refreshProbability A.refresh_admissible
    (b.1 : ℝ) (b.1 : ℝ) (2 * (b0.1 : ℝ))
    (fun k => measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd))
    (onlinePathLaw_refresh_marginal A)
  constructor
  · change Integrable
      (fun path => (b.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        if (path.2 k).1 then (b.1 : ℝ) else 2 * (b0.1 : ℝ))
      (onlinePathLaw A)
    exact h.1
  · change (∫ path, (b.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        (if (path.2 k).1 then (b.1 : ℝ) else 2 * (b0.1 : ℝ))
        ∂onlinePathLaw A) = _
    rw [h.2]
    unfold onlineOracleCallCount
    ring

/-- Exact Remark D.1 per-worker oracle expectation under the canonical
independent product of worker-dependent minibatch laws. -/
theorem heterogeneousFiniteSumWorkerOracleCost_integrable_and_expectation
    {d n m : Count} {b0 : Worker n → Count} {Ξ : Type*}
    [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ)
    (workerBatchLaw : HeterogeneousFiniteSumWorkerBatchLaw n m b0)
    (hWorkerBatchLaw : ∀ k i, IsProbabilityMeasure (workerBatchLaw k i))
    (K : Count) (i : Worker n) :
    Integrable
        (heterogeneousFiniteSumWorkerOracleCost (Ξ := Ξ) K i)
        (heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) ∧
      (∫ path, heterogeneousFiniteSumWorkerOracleCost (Ξ := Ξ) K i path
          ∂heterogeneousFiniteSumPathLaw A
            (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) =
        (m.1 : ℝ) + K.1 *
          (A.refreshProbability * m.1 +
            2 * (1 - A.refreshProbability) * (b0 i).1) := by
  letI (t : ℕ) (w : Worker n) : IsProbabilityMeasure (workerBatchLaw t w) :=
    hWorkerBatchLaw t w
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
  haveI : IsProbabilityMeasure
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) := by
    unfold heterogeneousFiniteSumPathLaw
    infer_instance
  have h := integrable_and_integral_refresh_cost
    (μ := heterogeneousFiniteSumPathLaw A
      (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))
    (coin := fun k
      (path : ℕ → HeterogeneousFiniteSumRoundNoise n m b0 Ξ) =>
        (path k).1)
    K A.refreshProbability A.refresh_admissible
    (m.1 : ℝ) (m.1 : ℝ) (2 * ((b0 i).1 : ℝ))
    (fun k => measurable_fst.comp (measurable_pi_apply k))
    (heterogeneousFiniteSumPathLaw_refresh_marginal
      A workerBatchLaw hWorkerBatchLaw)
  constructor
  · change Integrable
      (fun path => (m.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        if (path k).1 then (m.1 : ℝ) else 2 * ((b0 i).1 : ℝ))
      (heterogeneousFiniteSumPathLaw A
        (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw))
    exact h.1
  · change (∫ path, (m.1 : ℝ) + ∑ k ∈ Finset.range K.1,
        (if (path k).1 then (m.1 : ℝ) else 2 * ((b0 i).1 : ℝ))
        ∂heterogeneousFiniteSumPathLaw A
          (heterogeneousFiniteSumIndependentBatchLaw workerBatchLaw)) = _
    rw [h.2]
    ring

/-- Exact Remark D.2 per-worker oracle expectation on the full executable
heterogeneous Algorithm 3 experiment.  In particular, the initialization
charge is `(b i)`, not a charge assigned to the proof-exact process. -/
theorem heterogeneousOnlineWorkerOracleCost_integrable_and_expectation
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (K : Count) (i : Worker n) :
    Integrable
        (heterogeneousOnlineWorkerOracleCost (b := b) (b0 := b0)
          (Sample := Sample) (Ξ := Ξ) K i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ∧
      (∫ path,
          heterogeneousOnlineWorkerOracleCost (b := b) (b0 := b0)
            (Sample := Sample) (Ξ := Ξ) K i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) =
        ((b i).1 : ℝ) + K.1 *
          (A.refreshProbability * (b i).1 +
            2 * (1 - A.refreshProbability) * (b0 i).1) := by
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
  haveI : IsProbabilityMeasure
      (SOptLib.iidStreamLaw (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)) := by
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
    unfold heterogeneousOnlinePathLaw
    infer_instance
  have h := integrable_and_integral_refresh_cost
    (μ := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)
    (coin := fun k
      (path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) =>
        (path.2 k).1)
    K A.refreshProbability A.refresh_admissible
    ((b i).1 : ℝ) ((b i).1 : ℝ) (2 * ((b0 i).1 : ℝ))
    (fun k => measurable_fst.comp
      ((measurable_pi_apply k).comp measurable_snd))
    (heterogeneousOnlinePathLaw_refresh_marginal A)
  constructor
  · change Integrable
      (fun path => ((b i).1 : ℝ) + ∑ k ∈ Finset.range K.1,
        if (path.2 k).1 then ((b i).1 : ℝ) else 2 * ((b0 i).1 : ℝ))
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)
    exact h.1
  · change (∫ path, ((b i).1 : ℝ) + ∑ k ∈ Finset.range K.1,
        (if (path.2 k).1 then ((b i).1 : ℝ) else 2 * ((b0 i).1 : ℝ))
        ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) = _
    rw [h.2]
    ring

/-! ## Executable heterogeneous online initialization

The proof-exact Remark D.2 process starts with the exact global gradient,
whereas the executable process starts with the worker-dependent minibatch
estimator.  The following quantity and bound isolate precisely that difference
under the same initializer law used by `heterogeneousOnlineProcess`. -/

/-- Squared error of the worker-dependent executable Algorithm 3 initializer. -/
noncomputable def heterogeneousOnlineInitialEstimatorErrorSq
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (batch : HeterogeneousOnlineBatch n Sample b) : ℝ :=
  ‖heterogeneousOnlineInitialEstimator A batch x0 -
    globalGradient (onlineLocalProblem A.problem) x0‖ ^ 2

/-- Expected worker-dependent initialization error under the actual
heterogeneous initializer law. -/
noncomputable def expectedHeterogeneousOnlineInitialEstimatorErrorSq
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) : ℝ :=
  ∫ batch, heterogeneousOnlineInitialEstimatorErrorSq
      (b := b) A x0 batch
    ∂heterogeneousOnlineBatchLaw A.problem b

/-- The actual worker-dependent initializer has the Remark D.2 variance
aggregate `n⁻² ∑ᵢ σᵢ² / bᵢ`.  This is the executable
stochastic-initialization correction; it is not an assumption and does not use
the proof-exact process. -/
theorem expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 ≤
      heterogeneousOnlineVarianceTerm σ b := by
  classical
  let P := A.problem
  let rowLaw (i : Worker n) : Measure (Fin (b i).1 → Sample i) :=
    Measure.infinitePi (fun _ : Fin (b i).1 => P.sampleLaw i)
  let μ : Measure (HeterogeneousOnlineBatch n Sample b) :=
    heterogeneousOnlineBatchLaw P b
  let target (i : Worker n) : Point d :=
    localGradient (onlineLocalProblem P) i x0
  let residual (i : Worker n) (xi : Sample i) : Point d :=
    stochasticGradient P i xi x0 - target i
  let rowResidual (i : Worker n) (row : Fin (b i).1 → Sample i) : Point d :=
    average (fun j : Fin (b i).1 => residual i (row j))
  let workerResidual (i : Worker n)
      (batch : HeterogeneousOnlineBatch n Sample b) : Point d :=
    rowResidual i (batch i)
  letI (i : Worker n) : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  letI (i : Worker n) : IsProbabilityMeasure (rowLaw i) := by
    dsimp [rowLaw]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, heterogeneousOnlineBatchLaw]
    infer_instance
  have hcoord (i : Worker n) :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b => batch i) μ =
        rowLaw i := by
    simpa [μ, rowLaw, P] using
      heterogeneous_online_batch_law_worker_marginal P b i
  have hsample (i : Worker n) (j : Fin (b i).1) :
      Measure.map (fun row : Fin (b i).1 → Sample i => row j) (rowLaw i) =
        P.sampleLaw i := by
    dsimp [rowLaw]
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin (b i).1 => P.sampleLaw i) j)
  have hresidual_int (i : Worker n) :
      Integrable (residual i) (P.sampleLaw i) := by
    rcases hLiteral.2 i x0 with ⟨hgrad, _hres2, _hmean, _hsecond⟩
    exact hgrad.sub (integrable_const (c := target i))
  have hresidual_mean (i : Worker n) :
      (∫ xi, residual i xi ∂P.sampleLaw i) = 0 := by
    rcases hLiteral.2 i x0 with ⟨hgrad, _hres2, hmean, _hsecond⟩
    dsimp [residual, target, P]
    calc
      (∫ xi, stochasticGradient A.problem i xi x0 -
          localGradient (onlineLocalProblem A.problem) i x0
          ∂A.problem.sampleLaw i) =
          (∫ xi, stochasticGradient A.problem i xi x0
            ∂A.problem.sampleLaw i) -
            ∫ _xi : Sample i,
              localGradient (onlineLocalProblem A.problem) i x0
              ∂A.problem.sampleLaw i := by
                exact integral_sub hgrad
                  (integrable_const
                    (c := localGradient (onlineLocalProblem A.problem) i x0))
      _ = 0 := by simp [hmean]
  have hrow_term_int (i : Worker n) (j : Fin (b i).1) :
      Integrable (fun row : Fin (b i).1 → Sample i => residual i (row j))
        (rowLaw i) := by
    have hmap_int : Integrable (residual i)
        (Measure.map (fun row : Fin (b i).1 → Sample i => row j)
          (rowLaw i)) := by
      rw [hsample i j]
      exact hresidual_int i
    exact
      (MeasureTheory.integrable_map_measure hmap_int.aestronglyMeasurable
        (measurable_pi_apply j).aemeasurable).mp hmap_int
  have hrow_term_mean (i : Worker n) (j : Fin (b i).1) :
      (∫ row : Fin (b i).1 → Sample i, residual i (row j) ∂rowLaw i) = 0 := by
    have hmap_aesm : AEStronglyMeasurable (residual i)
        (Measure.map (fun row : Fin (b i).1 → Sample i => row j)
          (rowLaw i)) := by
      rw [hsample i j]
      exact (hresidual_int i).aestronglyMeasurable
    have hmap := MeasureTheory.integral_map
      (μ := rowLaw i) (φ := fun row : Fin (b i).1 → Sample i => row j)
      (measurable_pi_apply j).aemeasurable hmap_aesm
    rw [hsample i j, hresidual_mean i] at hmap
    exact hmap.symm
  have hrowResidual_int (i : Worker n) :
      Integrable (rowResidual i) (rowLaw i) := by
    dsimp [rowResidual, average, SOptLib.finiteUniformAverage]
    have hsum := MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _ => hrow_term_int i j)
    simpa [Pi.smul_apply] using hsum.smul (((b i).1 : ℝ)⁻¹)
  have hrowResidual_mean (i : Worker n) :
      (∫ row, rowResidual i row ∂rowLaw i) = 0 := by
    dsimp [rowResidual, average, SOptLib.finiteUniformAverage]
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun j _ => hrow_term_int i j)]
    simp [hrow_term_mean]
  have hcenter (i : Worker n) (row : Fin (b i).1 → Sample i) :
      average (fun j : Fin (b i).1 => stochasticGradient P i (row j) x0) -
          target i =
        rowResidual i row := by
    dsimp [rowResidual, residual]
    unfold average
    simpa [SOptLib.finiteUniformAverage] using
      (miniBatchAverage_sub_target_eq_average_residual
        (Finset.univ : Finset (Fin (b i).1)) (b i).1 (by simp) (b i).2
        (fun j => stochasticGradient P i (row j) x0) (target i))
  have hdiag (i : Worker n) :
      Integrable (fun batch => ‖workerResidual i batch‖ ^ 2) μ ∧
        (∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) ≤
          (σ i) ^ 2 / (b i).1 := by
    have h := heterogeneousOnline_refresh_secondMoment_le_of_legacy
      P σ b hLiteral i x0
    have hsquare (batch : HeterogeneousOnlineBatch n Sample b) :
        ‖workerResidual i batch‖ ^ 2 =
          ‖average (fun j : Fin (b i).1 =>
              stochasticGradient P i (batch i j) x0) -
            localGradient (onlineLocalProblem P) i x0‖ ^ 2 := by
      dsimp [workerResidual, target]
      rw [hcenter]
    constructor
    · apply h.1.congr
      exact Filter.Eventually.of_forall (fun batch => (hsquare batch).symm)
    · calc
        (∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) =
            ∫ batch,
              ‖average (fun j : Fin (b i).1 =>
                  stochasticGradient P i (batch i j) x0) -
                localGradient (onlineLocalProblem P) i x0‖ ^ 2 ∂μ := by
          exact integral_congr_ae (Filter.Eventually.of_forall hsquare)
        _ ≤ (σ i) ^ 2 / (b i).1 := by
          simpa [μ, P] using h.2
  have hworker_int (i : Worker n) : Integrable (workerResidual i) μ := by
    have hmeas : AEStronglyMeasurable (workerResidual i) μ := by
      have hrow_map : Integrable (rowResidual i)
          (Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b => batch i) μ) := by
        rw [hcoord i]
        exact hrowResidual_int i
      exact ((MeasureTheory.integrable_map_measure
        hrow_map.aestronglyMeasurable
        (measurable_pi_apply i).aemeasurable).mp hrow_map).aestronglyMeasurable
    exact integrable_of_integrable_norm_sq hmeas (hdiag i).1
  have hiIndep :
      ProbabilityTheory.iIndepFun
        (fun i (batch : HeterogeneousOnlineBatch n Sample b) => batch i) μ := by
    dsimp [μ, heterogeneousOnlineBatchLaw]
    exact ProbabilityTheory.iIndepFun_infinitePi
      (fun _ : Worker n => measurable_id)
  have hcross (i j : Worker n) (hij : i ≠ j) :
      (∫ batch, inner ℝ (workerResidual i batch)
        (workerResidual j batch) ∂μ) = 0 := by
    have hkernel :
        AEStronglyMeasurable
          (fun p : (Fin (b i).1 → Sample i) × (Fin (b j).1 → Sample j) =>
            inner ℝ (rowResidual i p.1) (rowResidual j p.2))
          ((Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b => batch i) μ).prod
            (rowLaw j)) := by
      rw [hcoord i]
      exact (hrowResidual_int i).aestronglyMeasurable.comp_fst.inner
        (hrowResidual_int j).aestronglyMeasurable.comp_snd
    have hinner : Integrable
        (fun batch => inner ℝ (workerResidual i batch)
          (workerResidual j batch)) μ :=
      integrable_inner_of_integrable_sq_norm
        (hworker_int i).aestronglyMeasurable
        (hworker_int j).aestronglyMeasurable (hdiag i).1 (hdiag j).1
    have hfixed : ∀ a : Fin (b i).1 → Sample i,
        (∫ z, inner ℝ (rowResidual i a) (rowResidual j z) ∂rowLaw j) = 0 := by
      intro a
      have hlin := ContinuousLinearMap.integral_comp_comm
        (L := (innerSL ℝ) (rowResidual i a)) (hrowResidual_int j)
      exact hlin.trans (by rw [hrowResidual_mean j]; simp)
    exact
      integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
        (P := μ) (ν := rowLaw j)
        (φ := fun a z => inner ℝ (rowResidual i a) (rowResidual j z))
        (X := fun batch : HeterogeneousOnlineBatch n Sample b => batch i)
        (Y := fun batch : HeterogeneousOnlineBatch n Sample b => batch j)
        hkernel (measurable_pi_apply i).aemeasurable
        (measurable_pi_apply j).aemeasurable (hiIndep.indepFun hij)
        (hcoord j) hinner hfixed
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    μ (Finset.univ : Finset (Worker n)) workerResidual
    (fun i _ => (hworker_int i).aestronglyMeasurable)
    (fun i _ => (hdiag i).1)
    (fun i _ j _ hij => hcross i j hij)
  have hglobal := globalGradient_eq_averageLocalGradient
    (onlineLocalProblem P) hDiff x0
  have hpointwise (batch : HeterogeneousOnlineBatch n Sample b) :
      heterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 batch =
        ‖((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n =>
            workerResidual i batch)‖ ^ 2 := by
    unfold heterogeneousOnlineInitialEstimatorErrorSq
      heterogeneousOnlineInitialEstimator
    rw [hglobal]
    apply congrArg (fun v : Point d => ‖v‖ ^ 2)
    unfold averageLocalGradient
    change
      average (fun i : Worker n =>
          average (fun j : Fin (b i).1 =>
            stochasticGradient P i (batch i j) x0)) -
        average (fun i : Worker n =>
          localGradient (onlineLocalProblem P) i x0) =
      ((n.1 : ℝ)⁻¹) •
        Finset.sum Finset.univ (fun i : Worker n => workerResidual i batch)
    calc
      _ = average (fun i : Worker n =>
          average (fun j : Fin (b i).1 =>
            stochasticGradient P i (batch i j) x0) -
            localGradient (onlineLocalProblem P) i x0) := by
        unfold average SOptLib.finiteUniformAverage
        rw [Finset.sum_sub_distrib, smul_sub]
      _ = average (fun i : Worker n => workerResidual i batch) := by
        apply congrArg average
        funext i
        dsimp [workerResidual, target, P]
        exact hcenter i (batch i)
      _ = ((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n =>
            workerResidual i batch) := by
        simp [average, SOptLib.finiteUniformAverage]
  rw [show expectedHeterogeneousOnlineInitialEstimatorErrorSq
      (b := b) A x0 =
      ∫ batch, heterogeneousOnlineInitialEstimatorErrorSq
        (b := b) A x0 batch ∂μ by rfl]
  calc
    (∫ batch, heterogeneousOnlineInitialEstimatorErrorSq
        (b := b) A x0 batch ∂μ) =
        ∫ batch, ‖((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n =>
            workerResidual i batch)‖ ^ 2 ∂μ := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpointwise)
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        ∫ batch, ‖Finset.sum Finset.univ
          (fun i : Worker n => workerResidual i batch)‖ ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro batch
      change ‖((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n =>
            workerResidual i batch)‖ ^ 2 =
        ((n.1 : ℝ)⁻¹) ^ 2 *
          ‖Finset.sum Finset.univ (fun i : Worker n =>
            workerResidual i batch)‖ ^ 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring
    _ = ((n.1 : ℝ)⁻¹) ^ 2 *
        Finset.sum Finset.univ
          (fun i : Worker n => ∫ batch, ‖workerResidual i batch‖ ^ 2 ∂μ) := by
      rw [hsum]
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        Finset.sum Finset.univ (fun i : Worker n =>
          (σ i) ^ 2 / (b i).1) := by
      gcongr with i
      exact (hdiag i).2
    _ = heterogeneousOnlineVarianceTerm σ b := by
      unfold heterogeneousOnlineVarianceTerm average
        SOptLib.finiteUniformAverage
      have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
      simp only [Fintype.card_fin, smul_eq_mul]
      field_simp [hn]

/-- Compatibility wrapper for the previously bundled Assumption 3.3 route.
The executable initialization bound itself uses only literal fixed-query
moments. -/
theorem expectedHeterogeneousOnlineInitialEstimatorErrorSq_le
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 ≤
      heterogeneousOnlineVarianceTerm σ b := by
  exact expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
    A x0 σ hVariance.1 hDiff

set_option maxHeartbeats 2000000 in
/-- The squared error of the executable worker-dependent initializer is a
genuine integrable random variable under its canonical batch law.  This is the
domain fact needed to lift the initializer correction to the complete
heterogeneous path experiment. -/
theorem heterogeneousOnlineInitialEstimatorErrorSq_integrable_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    Integrable (heterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0)
      (heterogeneousOnlineBatchLaw A.problem b) := by
  classical
  let P := A.problem
  let μ : Measure (HeterogeneousOnlineBatch n Sample b) :=
    heterogeneousOnlineBatchLaw P b
  let workerResidual (i : Worker n)
      (batch : HeterogeneousOnlineBatch n Sample b) : Point d :=
    average (fun j : Fin (b i).1 ↦ stochasticGradient P i (batch i j) x0) -
      localGradient (onlineLocalProblem P) i x0
  let initialResidual (batch : HeterogeneousOnlineBatch n Sample b) : Point d :=
    heterogeneousOnlineInitialEstimator A batch x0 -
      globalGradient (onlineLocalProblem P) x0
  letI (i : Worker n) : IsProbabilityMeasure (P.sampleLaw i) :=
    P.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, heterogeneousOnlineBatchLaw]
    infer_instance
  have hworkerSq (i : Worker n) :
      Integrable (fun batch ↦ ‖workerResidual i batch‖ ^ 2) μ := by
    have h := (heterogeneousOnline_refresh_secondMoment_le_of_legacy
      P σ b hLiteral i x0).1
    simpa [workerResidual, μ, P] using h
  have hcoord (i : Worker n) (j : Fin (b i).1) :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j) μ =
        P.sampleLaw i := by
    calc
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j) μ =
          Measure.map (fun row : Fin (b i).1 → Sample i ↦ row j)
            (Measure.map
              (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i) μ) := by
                rw [Measure.map_map (measurable_pi_apply j)
                  (measurable_pi_apply i)]
                rfl
      _ = Measure.map (fun row : Fin (b i).1 → Sample i ↦ row j)
          (Measure.infinitePi (fun _ : Fin (b i).1 ↦ P.sampleLaw i)) := by
            rw [show Measure.map
                (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i) μ =
                Measure.infinitePi (fun _ : Fin (b i).1 ↦ P.sampleLaw i) by
              simpa [μ] using heterogeneous_online_batch_law_worker_marginal P b i]
      _ = P.sampleLaw i := by
            simpa using (MeasureTheory.Measure.infinitePi_map_eval
              (μ := fun _ : Fin (b i).1 ↦ P.sampleLaw i) j)
  have hworkerMeas (i : Worker n) :
      AEStronglyMeasurable (workerResidual i) μ := by
    have hterm (j : Fin (b i).1) : AEStronglyMeasurable
        (fun batch : HeterogeneousOnlineBatch n Sample b ↦
          stochasticGradient P i (batch i j) x0) μ := by
      have hgrad : Integrable (fun xi ↦ stochasticGradient P i xi x0)
          (P.sampleLaw i) := (hLiteral.2 i x0).1
      have hmap : Integrable (fun xi ↦ stochasticGradient P i xi x0)
          (Measure.map
            (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j) μ) := by
        rw [hcoord i j]
        exact hgrad
      exact ((MeasureTheory.integrable_map_measure hmap.aestronglyMeasurable
        (((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hmap).aestronglyMeasurable
    dsimp [workerResidual]
    unfold average SOptLib.finiteUniformAverage
    have havg := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ hterm j)).const_smul
        (((Fintype.card (Fin (b i).1) : ℝ))⁻¹)
    have htarget : AEStronglyMeasurable
        (fun _ : HeterogeneousOnlineBatch n Sample b ↦
          localGradient (onlineLocalProblem P) i x0) μ :=
      aestronglyMeasurable_const
    refine (havg.sub htarget).congr (Filter.Eventually.of_forall ?_)
    intro batch
    simp [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply]
  have hglobal := globalGradient_eq_averageLocalGradient
    (onlineLocalProblem P) hDiff x0
  have hinitial (batch : HeterogeneousOnlineBatch n Sample b) :
      initialResidual batch = ((n.1 : ℝ)⁻¹) •
        Finset.sum Finset.univ (fun i : Worker n ↦ workerResidual i batch) := by
    dsimp [initialResidual, workerResidual, heterogeneousOnlineInitialEstimator]
    rw [hglobal]
    unfold averageLocalGradient
    calc
      average (fun i : Worker n ↦
          average (fun j : Fin (b i).1 ↦ stochasticGradient P i (batch i j) x0)) -
          average (fun i : Worker n ↦
            localGradient (onlineLocalProblem P) i x0) =
          average (fun i : Worker n ↦
            average (fun j : Fin (b i).1 ↦ stochasticGradient P i (batch i j) x0) -
              localGradient (onlineLocalProblem P) i x0) := by
            unfold average SOptLib.finiteUniformAverage
            rw [Finset.sum_sub_distrib, smul_sub]
      _ = ((n.1 : ℝ)⁻¹) •
          Finset.sum Finset.univ (fun i : Worker n ↦ workerResidual i batch) := by
            simp [average, SOptLib.finiteUniformAverage, workerResidual]
  have hresidualSq : Integrable (fun batch ↦ ‖initialResidual batch‖ ^ 2) μ := by
    apply integrable_sq_norm_centeredMiniBatchAverage μ
      (Finset.univ : Finset (Worker n)) n.1 workerResidual initialResidual
    · intro i _hi
      exact hworkerMeas i
    · intro i _hi
      exact hworkerSq i
    · funext batch
      exact hinitial batch
  simpa [heterogeneousOnlineInitialEstimatorErrorSq, initialResidual, μ, P] using
    hresidualSq

/-- Compatibility wrapper retaining the former bundled variance interface.
Only its literal fixed-query component is used by the integrability proof. -/
theorem heterogeneousOnlineInitialEstimatorErrorSq_integrable
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    Integrable (heterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0)
      (heterogeneousOnlineBatchLaw A.problem b) := by
  exact heterogeneousOnlineInitialEstimatorErrorSq_integrable_of_literal
    A x0 σ hVariance.1 hDiff

/-- At time zero, the executable heterogeneous estimator-error moment on the
full Algorithm 3 path law is exactly the initializer error integrated under the
worker-dependent batch law. -/
theorem heterogeneous_online_executable_initial_error_moment_eq_expected_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    estimatorErrorMoment (onlineLocalProblem A.problem)
        (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) 0 =
      expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let streamLaw := SOptLib.iidStreamLaw
    (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let initError := heterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
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
  haveI : IsProbabilityMeasure streamLaw := by
    dsimp [streamLaw]
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law, heterogeneousOnlinePathLaw]
    infer_instance
  have hfstLaw : Measure.map
      (fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.1) law =
      batchLaw := by
    dsimp [law, batchLaw, heterogeneousOnlinePathLaw]
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hInitInt : Integrable initError batchLaw := by
    simpa [initError, batchLaw] using
      (heterogeneousOnlineInitialEstimatorErrorSq_integrable_of_literal
        (b := b) A x0 σ hLiteral hDiff)
  have hMappedMeas : AEStronglyMeasurable initError
      (Measure.map
        (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.1) law) := by
    rw [hfstLaw]
    exact hInitInt.aestronglyMeasurable
  have hmapIntegral := MeasureTheory.integral_map
    (μ := law)
    (φ := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.1)
    measurable_fst.aemeasurable hMappedMeas
  rw [hfstLaw] at hmapIntegral
  have hleft : estimatorErrorMoment (onlineLocalProblem A.problem)
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0) law 0 =
      ∫ path, initError path.1 ∂law := by
    unfold estimatorErrorMoment
    apply integral_congr_ae
    filter_upwards [] with path
    rfl
  rw [hleft, hmapIntegral.symm]
  rfl

/-- Compatibility wrapper for the former bundled variance premise at the
time-zero executable moment identity. -/
theorem heterogeneous_online_executable_initial_error_moment_eq_expected
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    estimatorErrorMoment (onlineLocalProblem A.problem)
        (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) 0 =
      expectedHeterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0 := by
  exact heterogeneous_online_executable_initial_error_moment_eq_expected_of_literal
    A x0 σ hVariance.1 hDiff

/-- Executable heterogeneous Algorithm 3 starts with a well-defined estimator
error moment, and that moment obeys the exact worker-dependent Remark D.2
variance aggregate.  This is the base case required by the forthcoming
executable scalar recurrence. -/
theorem heterogeneous_online_executable_initial_error_moment_le_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) 0 ∧
      estimatorErrorMoment (onlineLocalProblem A.problem)
          (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
          (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) 0 ≤
        heterogeneousOnlineVarianceTerm σ b := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let streamLaw := SOptLib.iidStreamLaw
    (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let initError := heterogeneousOnlineInitialEstimatorErrorSq (b := b) A x0
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
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
  haveI : IsProbabilityMeasure streamLaw := by
    dsimp [streamLaw]
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law, heterogeneousOnlinePathLaw]
    infer_instance
  have hInitInt : Integrable initError batchLaw := by
    simpa [initError, batchLaw] using
      (heterogeneousOnlineInitialEstimatorErrorSq_integrable_of_literal
        (b := b) A x0 σ hLiteral hDiff)
  have hLiftInt : Integrable (fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      initError path.1) law := by
    dsimp [law, heterogeneousOnlinePathLaw]
    exact hInitInt.comp_fst streamLaw
  constructor
  · simpa [EstimatorErrorMomentWellDefined, initError, law,
      heterogeneousOnlineInitialEstimatorErrorSq] using hLiftInt
  · rw [heterogeneous_online_executable_initial_error_moment_eq_expected_of_literal
      (b := b) (b0 := b0) A x0 σ hLiteral hDiff]
    exact expectedHeterogeneousOnlineInitialEstimatorErrorSq_le_of_literal
      (b := b) A x0 σ hLiteral hDiff

/-- Compatibility wrapper retaining the former bundled variance boundary for
the executable time-zero recurrence base case. -/
theorem heterogeneous_online_executable_initial_error_moment_le
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A.problem σ)
    (hDiff : ∀ i, Differentiable ℝ
      ((onlineLocalProblem A.problem).localLoss i)) :
    EstimatorErrorMomentWellDefined (onlineLocalProblem A.problem)
        (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) 0 ∧
      estimatorErrorMoment (onlineLocalProblem A.problem)
          (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0)
          (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) 0 ≤
        heterogeneousOnlineVarianceTerm σ b := by
  exact heterogeneous_online_executable_initial_error_moment_le_of_literal
    A x0 σ hVariance.1 hDiff

/-- Minimal measurability data for the generated heterogeneous Algorithm 3
communication observable.  It concerns only the executable process and the
worker-dependent difference minibatch actually used in a compressed message. -/
structure HeterogeneousOnlineCostMeasurability
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) : Prop where
  process : ∀ k, Measurable
    (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
  difference : ∀ i : Worker n,
    Measurable (fun p : (Point d × Point d) ×
        HeterogeneousOnlineBatch n Sample b0 =>
      heterogeneousOnlineBatchDifference A.problem b0 p.2 i p.1.1 p.1.2)

/-- The actual worker-dependent non-refresh message generated by executable
Remark D.2 at round `k`.  Naming the pathwise observable allows the release
route to require regularity only under its canonical law. -/
noncomputable def heterogeneousOnlineWorkerDifferenceMessage
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (i : Worker n)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) : Point d :=
  let s := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path
  heterogeneousOnlineBatchDifference A.problem b0 (path.2 k).2.1.2 i
    (primalStep A.stepSize s) s.x

/-- The fresh compressor coordinate paired with a worker's actual
heterogeneous online difference message. -/
def heterogeneousOnlineWorkerCompressionSample
    {n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    (k : ℕ) (i : Worker n)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) : Ξ :=
  (path.2 k).2.2 i

/-- The refresh coin controlling the same heterogeneous online round. -/
def heterogeneousOnlineRefreshBranch
    {n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    (k : ℕ)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) : Bool :=
  (path.2 k).1

/-- Support of the original, actual heterogeneous compressed message. -/
noncomputable def heterogeneousOnlineWorkerRoundSupport
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (i : Worker n)
    (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) : ℝ :=
  quantizerNonzeroCount A.quantizer
    (heterogeneousOnlineWorkerDifferenceMessage A x0 k i path)
    (heterogeneousOnlineWorkerCompressionSample k i path)

/-- Weak law-scoped regularity interface for executable heterogeneous
Remark D.2 communication.  It asks only for an a.e.-measurable representative
of each generated message and the two fresh-noise independence facts needed
for density accounting.  It contains no integrability or cost bound. -/
structure HeterogeneousOnlineCommunicationAELawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) : Prop where
  message_aestronglyMeasurable : ∀ k (i : Worker n),
    AEStronglyMeasurable
      (heterogeneousOnlineWorkerDifferenceMessage
        (b := b) (b0 := b0) A x0 k i)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)
  messageRepresentative_indep_compression : ∀ k (i : Worker n),
    ProbabilityTheory.IndepFun
      ((message_aestronglyMeasurable k i).mk
        (heterogeneousOnlineWorkerDifferenceMessage
          (b := b) (b0 := b0) A x0 k i))
      (heterogeneousOnlineWorkerCompressionSample k i)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)
  supportRepresentative_indep_refresh : ∀ k (i : Worker n),
    ProbabilityTheory.IndepFun
      (fun path => quantizerNonzeroCount A.quantizer
        ((message_aestronglyMeasurable k i).mk
          (heterogeneousOnlineWorkerDifferenceMessage
            (b := b) (b0 := b0) A x0 k i) path)
        (heterogeneousOnlineWorkerCompressionSample k i path))
      (heterogeneousOnlineRefreshBranch k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)

/-- The law-a.e. interface suffices for the density bound on the original
heterogeneous message support.  The calculation is performed on the canonical
measurable representative and transferred back to the generated observable by
a.e. congruence. -/
theorem
    heterogeneousOnlineWorkerRoundSupport_integrable_and_le_expectedDensity_of_ae_law_regularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hRegularity : HeterogeneousOnlineCommunicationAELawRegularity
      (b := b) (b0 := b0) A x0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    Integrable (heterogeneousOnlineWorkerRoundSupport
        (b := b) (b0 := b0) A x0 k i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ∧
      (∫ path, heterogeneousOnlineWorkerRoundSupport
          (b := b) (b0 := b0) A x0 k i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ≤
        expectedDensity A.quantizer := by
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let message := heterogeneousOnlineWorkerDifferenceMessage
    (b := b) (b0 := b0) A x0 k i
  let sample := heterogeneousOnlineWorkerCompressionSample
    (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k i
  let hm : AEStronglyMeasurable message law :=
    hRegularity.message_aestronglyMeasurable k i
  let message' := hm.mk message
  have hmessage' : Measurable message' := hm.measurable_mk
  have hsample : Measurable sample := by
    change Measurable (fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
        (path.2 k).2.2 i)
    fun_prop
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let batch0Law := heterogeneousOnlineBatchLaw A.problem b0
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batch0Law := by
    dsimp [batch0Law]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsampleLaw : Measure.map sample law = A.quantizer.law := by
    let current := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => path.2 k
    have hcurrent : Measurable current := by dsimp [current]; fun_prop
    have hcurrentLaw : Measure.map current law = roundLaw := by
      calc
        Measure.map current law = Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              stream k) (Measure.map Prod.snd law) := by
          rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
          rfl
        _ = Measure.map
            (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              stream k) (SOptLib.iidStreamLaw roundLaw) := by
          rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
            dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
            rw [Measure.map_snd_prod, measure_univ, one_smul]]
        _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
    have hrowLaw : Measure.map
        (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
          (path.2 k).2.2) law = rowLaw := by
      calc
        Measure.map (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
            (path.2 k).2.2) law =
            Measure.map (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
              z.2.2) (Measure.map current law) := by
          rw [Measure.map_map (by fun_prop) hcurrent]
          rfl
        _ = Measure.map
            (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => z.2.2)
            roundLaw := by rw [hcurrentLaw]
        _ = rowLaw := by
          let restLaw := (batchLaw.prod batch0Law).prod rowLaw
          calc
            Measure.map
                (fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => z.2.2)
                roundLaw = Measure.map Prod.snd (Measure.map Prod.snd roundLaw) := by
              rw [Measure.map_map measurable_snd measurable_snd]
              rfl
            _ = Measure.map Prod.snd restLaw := by
              rw [show Measure.map Prod.snd roundLaw = restLaw by
                dsimp [roundLaw, restLaw]
                unfold heterogeneousOnlineRoundLaw
                rw [Measure.map_snd_prod, measure_univ, one_smul]]
            _ = rowLaw := by rw [Measure.map_snd_prod, measure_univ, one_smul]
    calc
      Measure.map sample law = Measure.map (fun ξ : Worker n → Ξ => ξ i)
          (Measure.map (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
            (path.2 k).2.2) law) := by
        rw [Measure.map_map (measurable_pi_apply i) (by fun_prop)]
        rfl
      _ = Measure.map (fun ξ : Worker n → Ξ => ξ i) rowLaw := by
        rw [hrowLaw]
      _ = A.quantizer.law :=
        workerCompressionLaw_component_marginal A.quantizer i
  have hrep := adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
    law hQ message' sample hmessage' hsample
      (hRegularity.messageRepresentative_indep_compression k i) hsampleLaw
  have hae : heterogeneousOnlineWorkerRoundSupport
      (b := b) (b0 := b0) A x0 k i =ᵐ[law]
      fun path => quantizerNonzeroCount A.quantizer (message' path) (sample path) := by
    filter_upwards [hm.ae_eq_mk] with path hp
    change quantizerNonzeroCount A.quantizer (message path) (sample path) =
      quantizerNonzeroCount A.quantizer (message' path) (sample path)
    rw [hp]
  constructor
  · exact hrep.1.congr hae.symm
  · rw [integral_congr_ae hae]
    exact hrep.2

set_option maxHeartbeats 2000000 in
/-- Finite-horizon heterogeneous communication accounting from the weak
law-a.e. interface.  The conclusion concerns the original executable cost
observable, not the measurable representative used inside the proof. -/
theorem
    heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hRegularity : HeterogeneousOnlineCommunicationAELawRegularity
      (b := b) (b0 := b0) A x0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (heterogeneousOnlineWorkerCommunicationCost
        (b := b) (b0 := b0) A x0 K i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ∧
      (∫ path, heterogeneousOnlineWorkerCommunicationCost
          (b := b) (b0 := b0) A x0 K i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let support := fun k => heterogeneousOnlineWorkerRoundSupport
    (b := b) (b0 := b0) A x0 k i
  let branch := fun k => heterogeneousOnlineRefreshBranch
    (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let term := fun k path =>
    if branch k path then (d.1 : ℝ) else support k path
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
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsupport (k : ℕ) : Integrable (support k) law ∧
      (∫ path, support k path ∂law) ≤ expectedDensity A.quantizer := by
    simpa [support, law] using
      heterogeneousOnlineWorkerRoundSupport_integrable_and_le_expectedDensity_of_ae_law_regularity
        A x0 hRegularity hQ k i
  have hbranchMeas (k : ℕ) : Measurable (branch k) := by
    dsimp [branch, heterogeneousOnlineRefreshBranch]
    exact measurable_fst.comp ((measurable_pi_apply k).comp measurable_snd)
  have hbranchLaw (k : ℕ) : Measure.map (branch k) law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law, heterogeneousOnlineRefreshBranch] using
      heterogeneousOnlinePathLaw_refresh_marginal
        (b := b) (b0 := b0) A k
  have hindep (k : ℕ) :
      ProbabilityTheory.IndepFun (support k) (branch k) law := by
    let message := heterogeneousOnlineWorkerDifferenceMessage
      (b := b) (b0 := b0) A x0 k i
    let sample := heterogeneousOnlineWorkerCompressionSample
      (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k i
    let hm : AEStronglyMeasurable message law :=
      hRegularity.message_aestronglyMeasurable k i
    have hae : (fun path => quantizerNonzeroCount A.quantizer
        (hm.mk message path) (sample path)) =ᵐ[law] support k := by
      filter_upwards [hm.ae_eq_mk] with path hp
      rw [← hp]
      rfl
    apply (hRegularity.supportRepresentative_indep_refresh k i).congr
    · simpa [message, sample, hm, support, law] using hae
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
    let refreshGate := fun path =>
      if branch k path = true then (d.1 : ℝ) else 0
    let differenceGate := fun path =>
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
          exact MeasureTheory.integral_map
            (hbranchMeas k).aemeasurable (by fun_prop)
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

/-! The conditional structure above remains available for compatibility.  The
next lemma starts the weaker law-a.e. route required by the release endpoint:
it proves regularity only under the genuine worker-dependent minibatch law,
rather than demanding a globally measurable kernel on null sample values. -/

/-- Under the explicit fixed-query-moment plus sampled-loss regularity
correction, a worker-dependent difference minibatch is a random vector at any
a.e.-measurable random query.  This is the heterogeneous analogue of
`onlineBatchDifference_product_aestronglyMeasurable_of_variance`; in
particular, it uses the actual row size `b0 i` and the canonical heterogeneous
product law from Remark D.2. -/
theorem heterogeneousOnlineBatchDifference_product_aestronglyMeasurable_of_variance
    {d n : Count} {Sample : Worker n → Type*} {b0 : Worker n → Count}
    {Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Q]
    (A : OnlineProblem d n Sample) (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A σ)
    (mu : Measure Q) [SFinite mu]
    (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Q × HeterogeneousOnlineBatch n Sample b0 ↦
        heterogeneousOnlineBatchDifference A b0 p.2 i (xNext p.1) (x p.1))
      (mu.prod (heterogeneousOnlineBatchLaw A b0)) := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A b0
  letI (w : Worker n) : IsProbabilityMeasure (A.sampleLaw w) :=
    A.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  have hworkerLaw : Measure.map
      (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i) batchLaw =
      Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.sampleLaw i) := by
    simpa [batchLaw] using
      heterogeneous_online_batch_law_worker_marginal A b0 i
  have hcoord (j : Fin (b0 i).1) :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j)
          batchLaw = A.sampleLaw i := by
    calc
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j)
          batchLaw =
          Measure.map (fun row : Fin (b0 i).1 → Sample i ↦ row j)
            (Measure.map
              (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i)
              batchLaw) := by
                rw [Measure.map_map (measurable_pi_apply j)
                  (measurable_pi_apply i)]
                rfl
      _ = Measure.map (fun row : Fin (b0 i).1 → Sample i ↦ row j)
          (Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.sampleLaw i)) := by
            rw [hworkerLaw]
      _ = A.sampleLaw i := by
            simpa using (MeasureTheory.Measure.infinitePi_map_eval
              (μ := fun _ : Fin (b0 i).1 ↦ A.sampleLaw i) j)
  have hsampleDiff (j : Fin (b0 i).1) :
      ∀ᵐ batch ∂batchLaw, Differentiable ℝ (A.sampleLoss i (batch i j)) := by
    let coord := fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw (A.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop), by
        rw [show Measure.map coord batchLaw = A.sampleLaw i by
          simpa [coord] using hcoord j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleInt (j : Fin (b0 i).1) (y : Point d) :
      Integrable
        (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦
          A.sampleLoss i (batch i j) y) batchLaw := by
    let coord := fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j
    have hm : Integrable (fun xi ↦ A.sampleLoss i xi y)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.sampleLaw i by
        simpa [coord] using hcoord j]
      exact A.sampleLoss_integrable i y
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by
        dsimp [coord]
        exact ((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hm
  have hnext (j : Fin (b0 i).1) : AEStronglyMeasurable
      (fun p : Q × HeterogeneousOnlineBatch n Sample b0 ↦
        stochasticGradient A i (p.2 i j) (xNext p.1))
      (mu.prod batchLaw) :=
    stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A i mu batchLaw xNext (fun batch ↦ batch i j) hxNext
        (hsampleDiff j) (hsampleInt j)
  have hcurrent (j : Fin (b0 i).1) : AEStronglyMeasurable
      (fun p : Q × HeterogeneousOnlineBatch n Sample b0 ↦
        stochasticGradient A i (p.2 i j) (x p.1))
      (mu.prod batchLaw) :=
    stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A i mu batchLaw x (fun batch ↦ batch i j) hx
        (hsampleDiff j) (hsampleInt j)
  unfold heterogeneousOnlineBatchDifference average
    SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun j _ ↦ (hnext j).sub (hcurrent j))).const_smul
      ((Fintype.card (Fin (b0 i).1) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [Finset.sum_apply, Finset.sum_sub_distrib]

/-- Source-facing form of the heterogeneous product-law regularity lemma.
The literal Assumption 3.3 moments and the Track-B sampled-gradient correction
are separate premises after unfolding; neither is presented as the other. -/
theorem heterogeneousOnlineBatchDifference_product_aestronglyMeasurable_of_literal
    {d n : Count} {Sample : Worker n → Type*} {b0 : Worker n → Count}
    {Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Q]
    (A : OnlineProblem d n Sample) (σ : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A σ)
    (hRegularity : OnlineAdaptiveSampleGradientRegularity A)
    (mu : Measure Q) [SFinite mu]
    (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Q × HeterogeneousOnlineBatch n Sample b0 ↦
        heterogeneousOnlineBatchDifference A b0 p.2 i (xNext p.1) (x p.1))
      (mu.prod (heterogeneousOnlineBatchLaw A b0)) := by
  exact
    heterogeneousOnlineBatchDifference_product_aestronglyMeasurable_of_variance
      A σ
      ((onlineUnbiasedBoundedVariance_iff_literal_and_adaptiveRegularity A σ).2
        ⟨hLiteral, hRegularity⟩)
      mu xNext x hxNext hx i

/-- The worker-dependent difference minibatch needs only the adaptive
product-law correction, not global differentiability of each sampled loss.
This is the first downstream consumer migrated to the weaker Track-B route. -/
theorem
    heterogeneousOnlineBatchDifference_product_aestronglyMeasurable_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*} {b0 : Worker n → Count}
    {Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Q]
    (A : OnlineProblem d n Sample)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A)
    (mu : Measure Q) [SFinite mu]
    (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Q × HeterogeneousOnlineBatch n Sample b0 ↦
        heterogeneousOnlineBatchDifference A b0 p.2 i (xNext p.1) (x p.1))
      (mu.prod (heterogeneousOnlineBatchLaw A b0)) := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A b0
  letI (w : Worker n) : IsProbabilityMeasure (A.sampleLaw w) :=
    A.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  have hworkerLaw : Measure.map
      (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i) batchLaw =
      Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.sampleLaw i) := by
    simpa [batchLaw] using
      heterogeneous_online_batch_law_worker_marginal A b0 i
  have hcoord (j : Fin (b0 i).1) :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j)
          batchLaw = A.sampleLaw i := by
    calc
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i j)
          batchLaw =
          Measure.map (fun row : Fin (b0 i).1 → Sample i ↦ row j)
            (Measure.map
              (fun batch : HeterogeneousOnlineBatch n Sample b0 ↦ batch i)
              batchLaw) := by
                rw [Measure.map_map (measurable_pi_apply j)
                  (measurable_pi_apply i)]
                rfl
      _ = Measure.map (fun row : Fin (b0 i).1 → Sample i ↦ row j)
          (Measure.infinitePi (fun _ : Fin (b0 i).1 ↦ A.sampleLaw i)) := by
            rw [hworkerLaw]
      _ = A.sampleLaw i := by
            simpa using (MeasureTheory.Measure.infinitePi_map_eval
              (μ := fun _ : Fin (b0 i).1 ↦ A.sampleLaw i) j)
  have hnext (j : Fin (b0 i).1) : AEStronglyMeasurable
      (fun p : Q × HeterogeneousOnlineBatch n Sample b0 ↦
        stochasticGradient A i (p.2 i j) (xNext p.1))
      (mu.prod batchLaw) :=
    (stochasticGradient_randomQuery_product_regular_of_lawRegularity
      A hRegularity i mu batchLaw xNext (fun batch ↦ batch i j) hxNext
        ((measurable_pi_apply j).comp (measurable_pi_apply i))
        (hcoord j)).2
  have hcurrent (j : Fin (b0 i).1) : AEStronglyMeasurable
      (fun p : Q × HeterogeneousOnlineBatch n Sample b0 ↦
        stochasticGradient A i (p.2 i j) (x p.1))
      (mu.prod batchLaw) :=
    (stochasticGradient_randomQuery_product_regular_of_lawRegularity
      A hRegularity i mu batchLaw x (fun batch ↦ batch i j) hx
        ((measurable_pi_apply j).comp (measurable_pi_apply i))
        (hcoord j)).2
  unfold heterogeneousOnlineBatchDifference average
    SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun j _ ↦ (hnext j).sub (hcurrent j))).const_smul
      ((Fintype.card (Fin (b0 i).1) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [Finset.sum_apply, Finset.sum_sub_distrib]

/-- Worker-dependent refresh minibatches are random vectors at an arbitrary
query law under the weak Track-B correction.  This is the refresh-branch
counterpart of
`heterogeneousOnlineBatchDifference_product_aestronglyMeasurable_of_lawRegularity`;
it uses neither fixed-query moments nor global sampled-loss differentiability. -/
theorem
    heterogeneousOnlineRefreshAverage_product_aestronglyMeasurable_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*} {b : Worker n → Count}
    [∀ i, MeasurableSpace (Sample i)]
    (A : OnlineProblem d n Sample)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A)
    (mu : Measure (Point d)) [SFinite mu] :
    AEStronglyMeasurable
      (fun p : Point d × HeterogeneousOnlineBatch n Sample b ↦
        average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A i (p.2 i j) p.1)))
      (mu.prod (heterogeneousOnlineBatchLaw A b)) := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A b
  letI (w : Worker n) : IsProbabilityMeasure (A.sampleLaw w) :=
    A.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw heterogeneousOnlineBatchLaw
    infer_instance
  have hworkerLaw (i : Worker n) : Measure.map
      (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i) batchLaw =
      Measure.infinitePi (fun _ : Fin (b i).1 ↦ A.sampleLaw i) := by
    simpa [batchLaw] using
      heterogeneous_online_batch_law_worker_marginal A b i
  have hcoord (i : Worker n) (j : Fin (b i).1) :
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j)
          batchLaw = A.sampleLaw i := by
    calc
      Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j)
          batchLaw =
          Measure.map (fun row : Fin (b i).1 → Sample i ↦ row j)
            (Measure.map
              (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i)
              batchLaw) := by
                rw [Measure.map_map (measurable_pi_apply j)
                  (measurable_pi_apply i)]
                rfl
      _ = Measure.map (fun row : Fin (b i).1 → Sample i ↦ row j)
          (Measure.infinitePi (fun _ : Fin (b i).1 ↦ A.sampleLaw i)) := by
            rw [hworkerLaw i]
      _ = A.sampleLaw i := by
            simpa using (MeasureTheory.Measure.infinitePi_map_eval
              (μ := fun _ : Fin (b i).1 ↦ A.sampleLaw i) j)
  have hterm (i : Worker n) (j : Fin (b i).1) :
      AEStronglyMeasurable
        (fun p : Point d × HeterogeneousOnlineBatch n Sample b ↦
          stochasticGradient A i (p.2 i j) p.1)
        (mu.prod batchLaw) :=
    (stochasticGradient_randomQuery_product_regular_of_lawRegularity
      A hRegularity i mu batchLaw id (fun batch ↦ batch i j)
        stronglyMeasurable_id.aestronglyMeasurable
        ((measurable_pi_apply j).comp (measurable_pi_apply i))
        (hcoord i j)).2
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Point d × HeterogeneousOnlineBatch n Sample b ↦
        average (fun j : Fin (b i).1 ↦
          stochasticGradient A i (p.2 i j) p.1))
      (mu.prod batchLaw) := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ hterm i j)).const_smul
        ((Fintype.card (Fin (b i).1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro p
    simp [Finset.sum_apply]
  unfold average SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ ↦ hworker i)).const_smul
      ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]

/-- The squared locally centered heterogeneous refresh error inherits the same
weak product-law regularity.  Literal moments are intentionally absent: they
enter later only to bound this already well-defined random variable. -/
theorem
    heterogeneousOnlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*} {b : Worker n → Count}
    [∀ i, MeasurableSpace (Sample i)]
    (A : OnlineProblem d n Sample)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A)
    (mu : Measure (Point d)) [SFinite mu] :
    AEStronglyMeasurable
      (fun p : Point d × HeterogeneousOnlineBatch n Sample b ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A i (p.2 i j) p.1)) -
          globalGradient (onlineLocalProblem A) p.1‖ ^ 2)
      (mu.prod (heterogeneousOnlineBatchLaw A b)) := by
  have havg :=
    heterogeneousOnlineRefreshAverage_product_aestronglyMeasurable_of_lawRegularity
      (b := b) A hRegularity mu
  have hglobal : AEStronglyMeasurable
      (fun p : Point d × HeterogeneousOnlineBatch n Sample b ↦
        globalGradient (onlineLocalProblem A) p.1)
      (mu.prod (heterogeneousOnlineBatchLaw A b)) :=
    ((measurable_gradient (globalObjective (onlineLocalProblem A))).comp
      measurable_fst).aestronglyMeasurable
  exact (havg.sub hglobal).norm.pow 2

/-! The executable heterogeneous induction has a genuinely different base
case from the proof-exact process: its initial estimator is a workerwise
minibatch average.  Fixed-query integrability from literal Assumption 3.3 is
already sufficient to make that random vector well defined; no adaptive-query
or global sampled-loss differentiability is needed at time zero. -/

set_option maxHeartbeats 2000000 in
/-- The actual worker-dependent Algorithm 3 initializer is an a.e. strongly
measurable random vector under its canonical dependent-product batch law using
only the literal fixed-query moment contract. -/
theorem heterogeneousOnlineInitialEstimator_aestronglyMeasurable_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma) :
    AEStronglyMeasurable
      (fun batch : HeterogeneousOnlineBatch n Sample b ↦
        heterogeneousOnlineInitialEstimator A batch x0)
      (heterogeneousOnlineBatchLaw A.problem b) := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  letI (i : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw i) :=
    A.problem.sampleLaw_isProbability i
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  have hworkerLaw (i : Worker n) : Measure.map
      (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i) batchLaw =
      Measure.infinitePi
        (fun _ : Fin (b i).1 ↦ A.problem.sampleLaw i) := by
    simpa [batchLaw] using
      heterogeneous_online_batch_law_worker_marginal A.problem b i
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
                rw [Measure.map_map (measurable_pi_apply j)
                  (measurable_pi_apply i)]
                rfl
      _ = Measure.map (fun row : Fin (b i).1 → Sample i ↦ row j)
          (Measure.infinitePi
            (fun _ : Fin (b i).1 ↦ A.problem.sampleLaw i)) := by
            rw [hworkerLaw i]
      _ = A.problem.sampleLaw i := by
            simpa using (MeasureTheory.Measure.infinitePi_map_eval
              (μ := fun _ : Fin (b i).1 ↦ A.problem.sampleLaw i) j)
  have hterm (i : Worker n) (j : Fin (b i).1) :
      AEStronglyMeasurable
        (fun batch : HeterogeneousOnlineBatch n Sample b ↦
          stochasticGradient A.problem i (batch i j) x0) batchLaw := by
    have hgrad : Integrable
        (fun xi ↦ stochasticGradient A.problem i xi x0)
        (A.problem.sampleLaw i) := hLiteral.2 i x0 |>.1
    have hmap : Integrable
        (fun xi ↦ stochasticGradient A.problem i xi x0)
        (Measure.map
          (fun batch : HeterogeneousOnlineBatch n Sample b ↦ batch i j)
          batchLaw) := by
      rw [hcoord i j]
      exact hgrad
    exact ((MeasureTheory.integrable_map_measure hmap.aestronglyMeasurable
      (((measurable_pi_apply j).comp
        (measurable_pi_apply i)).aemeasurable)).mp hmap).aestronglyMeasurable
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun batch : HeterogeneousOnlineBatch n Sample b ↦
        average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i (batch i j) x0)) batchLaw := by
    unfold average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ hterm i j)).const_smul
        ((Fintype.card (Fin (b i).1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro batch
    simp [Finset.sum_apply]
  unfold heterogeneousOnlineInitialEstimator average
    SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ ↦ hworker i)).const_smul
      ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro batch
  simp [Finset.sum_apply, average, SOptLib.finiteUniformAverage]

/-- Time zero of the generated executable heterogeneous process is a genuine
random state under the same path law later used for convergence and costs.
The proof exposes that its only stochastic input is the literal-moment
initializer batch. -/
theorem heterogeneousOnlineProcess_zero_aemeasurable_of_literal
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma) :
    AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 0)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let streamLaw := SOptLib.iidStreamLaw
    (heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A)
  have hgBatch :=
    heterogeneousOnlineInitialEstimator_aestronglyMeasurable_of_literal
      (b := b) A x0 sigma hLiteral
  have hg : AEStronglyMeasurable
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        heterogeneousOnlineInitialEstimator A path.1 x0)
      (batchLaw.prod streamLaw) := by
    exact hgBatch.comp_fst
  have hpair : AEMeasurable
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        (x0, heterogeneousOnlineInitialEstimator A path.1 x0))
      (batchLaw.prod streamLaw) :=
    measurable_const.aemeasurable.prodMk hg.aemeasurable
  change AEMeasurable
    (fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
      ({ x := x0, g := heterogeneousOnlineInitialEstimator A path.1 x0 } : State d))
    (batchLaw.prod streamLaw)
  exact (measurable_state_mk d).comp_aemeasurable hpair

/-- The executable heterogeneous online process depends only on its sampled
initializer and the strict prefix of the round stream. -/
theorem heterogeneousOnlineProcess_congr_round_prefix
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (initial : HeterogeneousOnlineBatch n Sample b)
    {path path' : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ}
    (hpath : ∀ t < k, path t = path' t) :
    heterogeneousOnlineProcess A x0 k (initial, path) =
      heterogeneousOnlineProcess A x0 k (initial, path') := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change heterogeneousOnlineStep A (path k)
          (heterogeneousOnlineProcess A x0 k (initial, path)) =
        heterogeneousOnlineStep A (path' k)
          (heterogeneousOnlineProcess A x0 k (initial, path'))
      have hprev : ∀ t < k, path t = path' t :=
        fun t ht => hpath t (Nat.lt_trans ht (Nat.lt_succ_self k))
      rw [ih hprev, hpath k (Nat.lt_succ_self k)]

/-- Under the canonical product law, the heterogeneous executable query at
round `k` is independent of the complete fresh round-`k` noise.  Only
canonical-law a.e. measurability of the generated state is needed: the proof
uses a measurable representative on the finite strict-prefix law. -/
theorem heterogeneousOnlineQuery_indep_current_round_of_measurable
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d) (k : ℕ)
    (hstate : AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) :
    ProbabilityTheory.IndepFun
      (fun path =>
        (primalStep A.stepSize
            (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path),
          (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path).x))
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => path.2 k)
      (heterogeneousOnlinePathLaw A) := by
  classical
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let streamLaw := SOptLib.iidStreamLaw roundLaw
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let prefixMap := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (path.1, fun j : Fin k => path.2 j.1)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => path.2 k
  let prefixLaw := Measure.map prefixMap law
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
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
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure streamLaw := by
    dsimp [streamLaw]
    unfold SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw
    infer_instance
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap]
    exact measurable_fst.prodMk
      (measurable_pi_lambda _ fun j =>
        (measurable_pi_apply j.1).comp measurable_snd)
  have hcurrent : Measurable current := by
    dsimp [current]
    exact (measurable_pi_apply k).comp measurable_snd
  haveI : IsProbabilityMeasure prefixLaw :=
    Measure.isProbabilityMeasure_map hprefix.aemeasurable
  let fallback : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ :=
    fun _ => Classical.choice (nonempty_of_isProbabilityMeasure roundLaw)
  let extend := fun pref : Fin k →
      HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
    fun t => if ht : t < k then pref ⟨t, ht⟩ else fallback t
  let prefixQuery := fun pref : HeterogeneousOnlineBatch n Sample b ×
      (Fin k → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (primalStep A.stepSize (run k (pref.1, extend pref.2)),
      (run k (pref.1, extend pref.2)).x)
  have hqueryPrefix : ∀ path, prefixQuery (prefixMap path) =
      (primalStep A.stepSize (run k path), (run k path).x) := by
    intro path
    have hs := (heterogeneousOnlineProcess_congr_round_prefix A x0 k path.1
      (path := path.2) (path' := extend (fun j : Fin k => path.2 j.1))
      (by intro t ht; simp [extend, ht])).symm
    simp only [prefixQuery, prefixMap, run]
    rw [hs]
  have hprefixLaw : prefixLaw =
      batchLaw.prod (Measure.infinitePi (fun _ : Fin k => roundLaw)) := by
    have hm := MeasureTheory.Measure.map_prod_map batchLaw streamLaw measurable_id
      (measurable_pi_lambda _ fun (j : Fin k) => measurable_pi_apply j.1)
    have hstreamPrefix : Measure.map
        (fun path : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
          fun j : Fin k => path j.1) streamLaw =
        Measure.infinitePi (fun _ : Fin k => roundLaw) := by
      simpa [streamLaw] using iidStream_prefix_map_eq_infinitePi roundLaw k
    rw [Measure.map_id, hstreamPrefix] at hm
    simpa [prefixLaw, prefixMap, law, batchLaw, streamLaw,
      heterogeneousOnlinePathLaw] using hm.symm
  have hquery : AEMeasurable (fun path =>
      (primalStep A.stepSize (run k path), (run k path).x)) law :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)
  have hprefixQuery : AEStronglyMeasurable prefixQuery prefixLaw := by
    have hcomp : AEStronglyMeasurable
        (fun path : HeterogeneousOnlineBatch n Sample b ×
            (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
          prefixQuery (path.1, fun j : Fin k => path.2 j.1)) law := by
      refine hquery.aestronglyMeasurable.congr (Filter.Eventually.of_forall ?_)
      intro path
      exact (hqueryPrefix path).symm
    have hfinite := aestronglyMeasurable_initial_prefix_of_comp_general
      batchLaw roundLaw k prefixQuery (by
        simpa [law, batchLaw, roundLaw, heterogeneousOnlinePathLaw] using hcomp)
    rw [hprefixLaw]
    exact hfinite
  let prefixQueryMk := hprefixQuery.mk prefixQuery
  have hprefixQueryMk : Measurable prefixQueryMk := hprefixQuery.measurable_mk
  let streamPrefix := fun path : ℕ →
      HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
    fun j : Fin k => path j.1
  let streamCurrent := fun path : ℕ →
      HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => path k
  have hstreamPrefixMeas : Measurable streamPrefix := by
    dsimp [streamPrefix]
    exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
  have hstreamCurrentMeas : Measurable streamCurrent := measurable_pi_apply k
  haveI : IsProbabilityMeasure (Measure.map streamPrefix streamLaw) :=
    Measure.isProbabilityMeasure_map hstreamPrefixMeas.aemeasurable
  have hstreamIndep : ProbabilityTheory.IndepFun
      streamPrefix streamCurrent streamLaw := by
    apply indepFun_of_map_prod_eq_prod_laws
      (P := streamLaw) (Z := fun path => (streamPrefix path, streamCurrent path))
      (mu := Measure.map streamPrefix streamLaw) (nu := roundLaw)
    · exact (hstreamPrefixMeas.prodMk hstreamCurrentMeas).aemeasurable
    · simpa [streamPrefix, streamCurrent, streamLaw, SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod (fun _ : ℕ => roundLaw) k)
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    have h := indepFun_prod_left_adjoin_of_indepFun
      batchLaw streamLaw streamPrefix streamCurrent
      hstreamPrefixMeas hstreamCurrentMeas hstreamIndep
    simpa [prefixMap, current, law, batchLaw, streamLaw,
      heterogeneousOnlinePathLaw, streamPrefix, streamCurrent] using h
  have hindepMk : ProbabilityTheory.IndepFun
      (prefixQueryMk ∘ prefixMap) current law :=
    hpastCurrent.comp hprefixQueryMk measurable_id
  have hprefixQmp : Measure.QuasiMeasurePreserving prefixMap law prefixLaw :=
    ⟨hprefix, (show Measure.map prefixMap law = prefixLaw from rfl).absolutelyContinuous⟩
  have hqueryAE : (fun path =>
      (primalStep A.stepSize (run k path), (run k path).x)) =ᵐ[law]
        prefixQueryMk ∘ prefixMap := by
    have hmk := hprefixQmp.tendsto_ae hprefixQuery.ae_eq_mk
    filter_upwards [hmk] with path hp
    rw [← hqueryPrefix path, hp]
    rfl
  have hindep : ProbabilityTheory.IndepFun
      (fun path => (primalStep A.stepSize (run k path), (run k path).x))
      current law :=
    hindepMk.congr hqueryAE.symm (Filter.Eventually.of_forall fun _ => rfl)
  simpa [run, current, law] using hindep

/-- The weak Track-B correction makes the actual worker-dependent difference
message a random vector as soon as the generated state at that round is a
random state.  This is a law-scoped statement for the canonical heterogeneous
path law; it assumes neither a globally measurable stochastic-gradient kernel
nor cost integrability. -/
theorem
    heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) (i : Worker n)
    (hstate : AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) :
    AEStronglyMeasurable
      (heterogeneousOnlineWorkerDifferenceMessage
        (b := b) (b0 := b0) A x0 k i)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  classical
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => path.2 k
  let batchOfRound := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
    z.2.1.2
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    batchOfRound (current path)
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
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
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hqueryAE : AEMeasurable query law := by
    exact ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)
  have hqueryStrong : AEStronglyMeasurable query law :=
    hqueryAE.aestronglyMeasurable
  let query' := hqueryStrong.mk query
  have hquery' : Measurable query' := hqueryStrong.measurable_mk
  have hcurrent : Measurable current := by
    dsimp [current]
    fun_prop
  have hbatchOfRound : Measurable batchOfRound := by
    dsimp [batchOfRound]
    fun_prop
  have hbatch : Measurable batch := hbatchOfRound.comp hcurrent
  have hqueryCurrent :=
    heterogeneousOnlineQuery_indep_current_round_of_measurable
      (b := b) (b0 := b0) A x0 k hstate
  have hqueryCurrent' : ProbabilityTheory.IndepFun query' current law := by
    apply hqueryCurrent.congr hqueryStrong.ae_eq_mk
      (Filter.Eventually.of_forall fun _ => rfl)
  have hqueryBatch : ProbabilityTheory.IndepFun query' batch law :=
    hqueryCurrent'.comp measurable_id hbatchOfRound
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (Measure.map Prod.snd law) := by
        rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
        rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (SOptLib.iidStreamLaw roundLaw) := by
        rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
          dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map batchOfRound (Measure.map current law) := by
        rw [Measure.map_map hbatchOfRound hcurrent]
        rfl
      _ = Measure.map batchOfRound roundLaw := by rw [hcurrentLaw]
      _ = batchLaw := by
        let initialLaw := heterogeneousOnlineBatchLaw A.problem b
        let rowLaw := workerCompressionLaw (n := n) A.quantizer
        let restLaw := (initialLaw.prod batchLaw).prod rowLaw
        calc
          Measure.map batchOfRound roundLaw =
              Measure.map (fun z : (HeterogeneousOnlineBatch n Sample b ×
                HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                  z.1.2) (Measure.map Prod.snd roundLaw) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_snd
          _ = Measure.map (fun z : (HeterogeneousOnlineBatch n Sample b ×
                HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                  z.1.2) restLaw := by
            rw [show Measure.map Prod.snd roundLaw = restLaw by
              dsimp [roundLaw, restLaw, initialLaw]
              unfold heterogeneousOnlineRoundLaw
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = Measure.map Prod.snd (initialLaw.prod batchLaw) := by
            rw [show (fun z : (HeterogeneousOnlineBatch n Sample b ×
                HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                  z.1.2) = Prod.snd ∘ Prod.fst by rfl,
              ← Measure.map_map measurable_snd measurable_fst,
              Measure.map_fst_prod, measure_univ, one_smul]
          _ = batchLaw := by
            rw [Measure.map_snd_prod, measure_univ, one_smul]
  haveI : IsProbabilityMeasure (Measure.map query' law) :=
    Measure.isProbabilityMeasure_map hquery'.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map batch law) :=
    Measure.isProbabilityMeasure_map hbatch.aemeasurable
  let kernel := fun z : (Point d × Point d) ×
      HeterogeneousOnlineBatch n Sample b0 =>
    heterogeneousOnlineBatchDifference A.problem b0 z.2 i z.1.1 z.1.2
  have hkernel : AEStronglyMeasurable kernel
      ((Measure.map query' law).prod (Measure.map batch law)) := by
    rw [hbatchLaw]
    simpa [kernel] using
      (heterogeneousOnlineBatchDifference_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A.problem hRegularity (Measure.map query' law)
          Prod.fst Prod.snd measurable_fst.aestronglyMeasurable
          measurable_snd.aestronglyMeasurable i)
  have hcomp : AEStronglyMeasurable
      (fun path => kernel (query' path, batch path)) law :=
    aestronglyMeasurable_comp_of_indep_product_law
      hquery'.aemeasurable hbatch.aemeasurable
        (inferInstance : SigmaFinite (Measure.map query' law))
        (inferInstance : SigmaFinite (Measure.map batch law))
        hqueryBatch hkernel
  refine hcomp.congr ?_
  filter_upwards [hqueryStrong.ae_eq_mk] with path hp
  simpa [kernel, query', batch, batchOfRound, current, query, run,
    heterogeneousOnlineWorkerDifferenceMessage] using
      congrArg (fun q => kernel (q, batch path)) hp.symm

/-- The actual worker-averaged refresh estimator in executable heterogeneous
Algorithm 3 is a random vector whenever the generated state before the round
is a random state.  The proof pulls the weak adaptive-gradient product kernel
back along the canonical strict-past/current-round product law; it assumes no
global sampled-loss differentiability and no cost-measurability witness. -/
theorem
    heterogeneousOnlineRefreshEstimator_aestronglyMeasurable_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ)
    (hstate : AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) :
    AEStronglyMeasurable
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (primalStep A.stepSize
              (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k path)))))
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  classical
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    primalStep A.stepSize (run k path)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦ path.2 k
  let batchOfRound := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
    z.2.1.1
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    batchOfRound (current path)
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (heterogeneousOnlineBatchLaw A.problem b0) := by
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
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hqueryStrong : AEStronglyMeasurable query law :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).aestronglyMeasurable
  let query' := hqueryStrong.mk query
  have hquery' : Measurable query' := hqueryStrong.measurable_mk
  have hcurrent : Measurable current := by
    dsimp [current]
    fun_prop
  have hbatchOfRound : Measurable batchOfRound := by
    dsimp [batchOfRound]
    fun_prop
  have hbatch : Measurable batch := hbatchOfRound.comp hcurrent
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    have h := (heterogeneousOnlineQuery_indep_current_round_of_measurable
      (b := b) (b0 := b0) A x0 k hstate).comp measurable_fst measurable_id
    simpa [query, run, current, law] using h
  have hqueryCurrent' : ProbabilityTheory.IndepFun query' current law := by
    apply hqueryCurrent.congr hqueryStrong.ae_eq_mk
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hqueryBatch : ProbabilityTheory.IndepFun query' batch law :=
    hqueryCurrent'.comp measurable_id hbatchOfRound
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (Measure.map Prod.snd law) := by
        rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
        rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ ↦
            stream k) (SOptLib.iidStreamLaw roundLaw) := by
        rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
          dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map batchOfRound (Measure.map current law) := by
        rw [Measure.map_map hbatchOfRound hcurrent]
        rfl
      _ = Measure.map batchOfRound roundLaw := by rw [hcurrentLaw]
      _ = batchLaw := by
        let differenceLaw := heterogeneousOnlineBatchLaw A.problem b0
        let rowLaw := workerCompressionLaw (n := n) A.quantizer
        let restLaw := (batchLaw.prod differenceLaw).prod rowLaw
        calc
          Measure.map batchOfRound roundLaw =
              Measure.map (fun z : (HeterogeneousOnlineBatch n Sample b ×
                HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                  z.1.1) (Measure.map Prod.snd roundLaw) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_snd
          _ = Measure.map (fun z : (HeterogeneousOnlineBatch n Sample b ×
                HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                  z.1.1) restLaw := by
            rw [show Measure.map Prod.snd roundLaw = restLaw by
              dsimp [roundLaw, restLaw, differenceLaw, batchLaw]
              unfold heterogeneousOnlineRoundLaw
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = Measure.map Prod.fst (batchLaw.prod differenceLaw) := by
            rw [show (fun z : (HeterogeneousOnlineBatch n Sample b ×
                HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) ↦
                  z.1.1) = Prod.fst ∘ Prod.fst by rfl,
              ← Measure.map_map measurable_fst measurable_fst,
              Measure.map_fst_prod, measure_univ, one_smul]
          _ = batchLaw := by
            rw [Measure.map_fst_prod, measure_univ, one_smul]
  haveI : IsProbabilityMeasure (Measure.map query' law) :=
    Measure.isProbabilityMeasure_map hquery'.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map batch law) :=
    Measure.isProbabilityMeasure_map hbatch.aemeasurable
  let kernel := fun z : Point d × HeterogeneousOnlineBatch n Sample b ↦
    average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
      stochasticGradient A.problem i (z.2 i j) z.1))
  have hkernel : AEStronglyMeasurable kernel
      ((Measure.map query' law).prod (Measure.map batch law)) := by
    rw [hbatchLaw]
    simpa [kernel] using
      (heterogeneousOnlineRefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b := b) A.problem hRegularity (Measure.map query' law))
  have hcomp : AEStronglyMeasurable
      (fun path ↦ kernel (query' path, batch path)) law :=
    aestronglyMeasurable_comp_of_indep_product_law
      hquery'.aemeasurable hbatch.aemeasurable
        (inferInstance : SigmaFinite (Measure.map query' law))
        (inferInstance : SigmaFinite (Measure.map batch law))
        hqueryBatch hkernel
  refine hcomp.congr ?_
  filter_upwards [hqueryStrong.ae_eq_mk] with path hp
  simpa [kernel, query', batch, batchOfRound, current, query, run] using
    congrArg (fun q => kernel (q, batch path)) hp.symm

/-- One executable heterogeneous Algorithm 3 update preserves canonical-law
a.e. measurability under the weak adaptive-gradient correction.  Both update
branches are the actual generated branches: the refresh estimator above and
the compressed worker-dependent difference messages. -/
theorem heterogeneousOnlineProcess_succ_aemeasurable_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ)
    (hstate : AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) :
    AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 (k + 1))
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  classical
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let branch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
    (path.2 k).1
  have hxNext : AEStronglyMeasurable
      (fun path ↦ primalStep A.stepSize (run k path)) law :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hstate).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun path ↦ (run k path).g) law :=
    ((measurable_state_g d).comp_aemeasurable hstate).aestronglyMeasurable
  have hrefresh : AEStronglyMeasurable
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (primalStep A.stepSize (run k path))))) law := by
    simpa [run, law] using
      (heterogeneousOnlineRefreshEstimator_aestronglyMeasurable_of_lawRegularity
        (b := b) (b0 := b0) A x0 hRegularity k hstate)
  have hcarry (i : Worker n) : AEStronglyMeasurable
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        (run k path).g + A.quantizer.apply
          (heterogeneousOnlineWorkerDifferenceMessage
            (b := b) (b0 := b0) A x0 k i path)
          (heterogeneousOnlineWorkerCompressionSample k i path)) law := by
    have hmessage :=
      heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_lawRegularity
        (b := b) (b0 := b0) A x0 hRegularity k i hstate
    have hcompression : Measurable
        (heterogeneousOnlineWorkerCompressionSample
          (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k i) := by
      exact (measurable_pi_apply i).comp
        (measurable_snd.comp
          (measurable_snd.comp ((measurable_pi_apply k).comp measurable_snd)))
    have hquantized : AEStronglyMeasurable
        (fun path ↦ A.quantizer.apply
          (heterogeneousOnlineWorkerDifferenceMessage
            (b := b) (b0 := b0) A x0 k i path)
          (heterogeneousOnlineWorkerCompressionSample k i path)) law :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hmessage.aemeasurable.prodMk hcompression.aemeasurable)).aestronglyMeasurable
    exact hg.add hquantized
  have hnonrefresh : AEStronglyMeasurable
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) ↦
        average (fun i : Worker n ↦
          (run k path).g + A.quantizer.apply
            (heterogeneousOnlineWorkerDifferenceMessage
              (b := b) (b0 := b0) A x0 k i path)
            (heterogeneousOnlineWorkerCompressionSample k i path))) law := by
    unfold average SOptLib.finiteUniformAverage
    have hsum := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ ↦ hcarry i)).const_smul
        ((Fintype.card (Worker n) : ℝ)⁻¹)
    refine hsum.congr (Filter.Eventually.of_forall ?_)
    intro path
    simp [Finset.sum_apply]
  have hbranch : Measurable branch := by
    dsimp [branch]
    fun_prop
  have hbranchSet : MeasurableSet {path | branch path = true} :=
    hbranch (measurableSet_singleton true)
  have hdirection : AEStronglyMeasurable
      (fun path ↦ if branch path then
        average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
          stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
            (primalStep A.stepSize (run k path))))
      else average (fun i : Worker n ↦
        (run k path).g + A.quantizer.apply
          (heterogeneousOnlineWorkerDifferenceMessage
            (b := b) (b0 := b0) A x0 k i path)
          (heterogeneousOnlineWorkerCompressionSample k i path))) law := by
    have hpiece := AEStronglyMeasurable.piecewise hbranchSet
      hrefresh.restrict hnonrefresh.restrict
    simpa [branch, Set.piecewise] using hpiece
  have hnext : AEMeasurable
      (fun path ↦ State.mk (primalStep A.stepSize (run k path))
        (if branch path then
          average (fun i : Worker n ↦ average (fun j : Fin (b i).1 ↦
            stochasticGradient A.problem i ((path.2 k).2.1.1 i j)
              (primalStep A.stepSize (run k path))))
        else average (fun i : Worker n ↦
          (run k path).g + A.quantizer.apply
            (heterogeneousOnlineWorkerDifferenceMessage
              (b := b) (b0 := b0) A x0 k i path)
            (heterogeneousOnlineWorkerCompressionSample k i path)))) law :=
    (measurable_state_mk d).comp_aemeasurable
      (hxNext.aemeasurable.prodMk hdirection.aemeasurable)
  refine hnext.congr (Filter.Eventually.of_forall ?_)
  intro path
  simp only [run, branch, heterogeneousOnlineProcess,
    SOptLib.recursive_process_from_random_initial, heterogeneousOnlineStep,
    heterogeneousOnlineWorkerDifferenceMessage,
    heterogeneousOnlineWorkerCompressionSample]
  by_cases h : (path.2 k).1 = true <;> simp [h]

/-- Literal fixed-query moments close the stochastic-initialization base, and
the weak law-scoped correction closes every generated successor.  Hence every
state of the actual executable heterogeneous process is a random state under
its own canonical path law, with no `HeterogeneousOnlineCostMeasurability`
input. -/
theorem heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem) :
    ∀ k, AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  intro k
  induction k with
  | zero =>
      exact heterogeneousOnlineProcess_zero_aemeasurable_of_literal
        (b := b) (b0 := b0) A x0 sigma hLiteral
  | succ k ih =>
      simpa [Nat.succ_eq_add_one] using
        heterogeneousOnlineProcess_succ_aemeasurable_of_lawRegularity
          (b := b) (b0 := b0) A x0 hRegularity k ih

/-- The homogeneous executable experiment is definitionally the constant
worker-batch specialization of the heterogeneous path law. -/
theorem onlinePathLaw_eq_heterogeneousOnlinePathLaw_const
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) :
    onlinePathLaw (b := b) (b0 := b0) A =
      heterogeneousOnlinePathLaw
        (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0) A := by
  rfl

/-- The generated homogeneous `onlineProcess` is the same executable process
as Remark D.2 specialized to constant worker batch sizes.  The admissibility
witness is computationally irrelevant; both sides retain the sampled
initializer and the same round transition. -/
theorem onlineProcess_eq_heterogeneousOnlineProcess_const
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ)
    (path : ((i : Worker n) → Fin b.1 → Sample i) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) :
    onlineProcess A x0 hBatch k path =
      heterogeneousOnlineProcess
        (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0)
        A x0 k path := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [onlineProcess_succ, heterogeneousOnlineProcess,
        SOptLib.recursive_process_from_random_initial]
      rw [ih]
      rfl

/-- Consequently the weak Track-B correction and literal fixed-query moments
make every state of homogeneous executable Algorithm 3 a random state under
its own path law.  This is the homogeneous process-measurability supplier
needed by the recurrence and measured-cost migrations, and it contains no
global sample-loss differentiability premise. -/
theorem onlineProcess_aemeasurable_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem) :
    ∀ k, AEMeasurable (onlineProcess A x0 hBatch k) (onlinePathLaw A) := by
  intro k
  have h :=
    heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
      (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0)
      A x0 sigma hLiteral hRegularity k
  rw [← onlinePathLaw_eq_heterogeneousOnlinePathLaw_const A] at h
  exact h.congr (Filter.Eventually.of_forall fun path ↦
    (onlineProcess_eq_heterogeneousOnlineProcess_const
      A x0 hBatch k path).symm)

/-- At the first executable heterogeneous round, literal Assumption 3.3 makes
the stochastic initializer a random state and the weak Track-B correction
then makes every actual difference message a random vector.  This is the base
case needed by the generated-process regularity induction. -/
theorem
    heterogeneousOnlineWorkerDifferenceMessage_zero_aestronglyMeasurable_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (i : Worker n) :
    AEStronglyMeasurable
      (heterogeneousOnlineWorkerDifferenceMessage
        (b := b) (b0 := b0) A x0 0 i)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  exact
    heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_lawRegularity
      A x0 hRegularity 0 i
        (heterogeneousOnlineProcess_zero_aemeasurable_of_literal
          (b := b) (b0 := b0) A x0 sigma hLiteral)

/-- If `X` is independent of a pair `(Y, Z)` whose law is a product, then
adjoining `Y` to `X` preserves independence from `Z`. -/
theorem indepFun_left_adjoin_fst_of_indepFun_pair
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (X : Ω → A) (Y : Ω → B) (Z : Ω → C)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hindep : ProbabilityTheory.IndepFun X (fun ω => (Y ω, Z ω)) P)
    (hpairLaw : Measure.map (fun ω => (Y ω, Z ω)) P = ν.prod ρ) :
    ProbabilityTheory.IndepFun (fun ω => (X ω, Y ω)) Z P := by
  let μ := Measure.map X P
  haveI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hjoint :
      Measure.map (fun ω => (X ω, (Y ω, Z ω))) P = μ.prod (ν.prod ρ) := by
    calc
      Measure.map (fun ω => (X ω, (Y ω, Z ω))) P =
          (Measure.map X P).prod (Measure.map (fun ω => (Y ω, Z ω)) P) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hX.aemeasurable (hY.prodMk hZ).aemeasurable).1 hindep
      _ = μ.prod (ν.prod ρ) := by rw [hpairLaw]
  have hassoc : Measure.map MeasurableEquiv.prodAssoc.symm
      (μ.prod (ν.prod ρ)) = (μ.prod ν).prod ρ := by
    have h := MeasureTheory.Measure.prodAssoc_prod
      (μ := μ) (ν := ν) (τ := ρ)
    rw [← h, Measure.map_map]
    · simp
    · exact MeasurableEquiv.prodAssoc.symm.measurable
    · exact MeasurableEquiv.prodAssoc.measurable
  apply indepFun_of_map_prod_eq_prod_laws
    (P := P) (Z := fun ω => ((X ω, Y ω), Z ω))
    (mu := μ.prod ν) (nu := ρ)
    ((hX.prodMk hY).prodMk hZ).aemeasurable
  calc
    Measure.map (fun ω => ((X ω, Y ω), Z ω)) P =
        Measure.map MeasurableEquiv.prodAssoc.symm
          (Measure.map (fun ω => (X ω, (Y ω, Z ω))) P) := by
      rw [Measure.map_map]
      · rfl
      · exact MeasurableEquiv.prodAssoc.symm.measurable
      · exact hX.prodMk (hY.prodMk hZ)
    _ = Measure.map MeasurableEquiv.prodAssoc.symm (μ.prod (ν.prod ρ)) := by
      rw [hjoint]
    _ = (μ.prod ν).prod ρ := hassoc

set_option maxHeartbeats 2000000 in
/-- For an a.e.-measurable generated heterogeneous state, the canonical
measurable representative of the actual difference message is independent of
its fresh compressor coordinate, and its support is independent of the fresh
refresh coin.  These are consequences of the round product law, not extra
regularity assumptions. -/
theorem
    heterogeneousOnlineWorkerMessageRepresentative_independences_of_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (k : ℕ) (i : Worker n)
    (hstate : AEMeasurable
      (heterogeneousOnlineProcess (b := b) (b0 := b0) A x0 k)
      (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A)) :
    let hm :=
      heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_lawRegularity
        (b := b) (b0 := b0) A x0 hRegularity k i hstate
    ProbabilityTheory.IndepFun
        (hm.mk (heterogeneousOnlineWorkerDifferenceMessage
          (b := b) (b0 := b0) A x0 k i))
        (heterogeneousOnlineWorkerCompressionSample k i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ∧
      ProbabilityTheory.IndepFun
        (fun path => quantizerNonzeroCount A.quantizer
          (hm.mk (heterogeneousOnlineWorkerDifferenceMessage
            (b := b) (b0 := b0) A x0 k i) path)
          (heterogeneousOnlineWorkerCompressionSample k i path))
        (heterogeneousOnlineRefreshBranch k)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) := by
  classical
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => path.2 k
  let noiseOfRound := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
    (z.2.1.2, z.2.2)
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    noiseOfRound (current path)
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => (noise path).1
  let row := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => (noise path).2
  let sample := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => row path i
  let batchLaw := heterogeneousOnlineBatchLaw A.problem b0
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  let initialLaw := heterogeneousOnlineBatchLaw A.problem b
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure initialLaw := by
    dsimp [initialLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hqueryStrong : AEStronglyMeasurable query law := by
    exact (((measurable_primalStep A.stepSize).comp_aemeasurable hstate).prodMk
      ((measurable_state_x d).comp_aemeasurable hstate)).aestronglyMeasurable
  let query' := hqueryStrong.mk query
  have hquery' : Measurable query' := hqueryStrong.measurable_mk
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hnoiseOfRound : Measurable noiseOfRound := by dsimp [noiseOfRound]; fun_prop
  have hnoise : Measurable noise := hnoiseOfRound.comp hcurrent
  have hbatch : Measurable batch := measurable_fst.comp hnoise
  have hrow : Measurable row := measurable_snd.comp hnoise
  have hsample : Measurable sample := (measurable_pi_apply i).comp hrow
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    simpa [query, current, run, law] using
      heterogeneousOnlineQuery_indep_current_round_of_measurable
        (b := b) (b0 := b0) A x0 k hstate
  have hqueryCurrent' : ProbabilityTheory.IndepFun query' current law := by
    apply hqueryCurrent.congr hqueryStrong.ae_eq_mk
      (Filter.Eventually.of_forall fun _ => rfl)
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (Measure.map Prod.snd law) := by
        rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
        rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (SOptLib.iidStreamLaw roundLaw) := by
        rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
          dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hnoiseLaw : Measure.map noise law = batchLaw.prod rowLaw := by
    calc
      Measure.map noise law = Measure.map noiseOfRound (Measure.map current law) := by
        rw [Measure.map_map hnoiseOfRound hcurrent]
        rfl
      _ = Measure.map noiseOfRound roundLaw := by rw [hcurrentLaw]
      _ = batchLaw.prod rowLaw := by
        let restLaw := (initialLaw.prod batchLaw).prod rowLaw
        calc
          Measure.map noiseOfRound roundLaw = Measure.map
              (fun z : (HeterogeneousOnlineBatch n Sample b ×
                  HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                (z.1.2, z.2)) (Measure.map Prod.snd roundLaw) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_snd
          _ = Measure.map
              (fun z : (HeterogeneousOnlineBatch n Sample b ×
                  HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                (z.1.2, z.2)) restLaw := by
            rw [show Measure.map Prod.snd roundLaw = restLaw by
              dsimp [roundLaw, restLaw, initialLaw, batchLaw, rowLaw]
              unfold heterogeneousOnlineRoundLaw
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = (Measure.map Prod.snd (initialLaw.prod batchLaw)).prod
              (Measure.map id rowLaw) := by
            simpa only [Function.comp_apply, Prod.map_apply] using
              (MeasureTheory.Measure.map_prod_map
                (initialLaw.prod batchLaw) rowLaw measurable_snd measurable_id).symm
          _ = batchLaw.prod rowLaw := by
            rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_id]
  have hqueryNoise : ProbabilityTheory.IndepFun query' noise law :=
    hqueryCurrent'.comp measurable_id hnoiseOfRound
  have hqueryBatchRow : ProbabilityTheory.IndepFun
      (fun path => (query' path, batch path)) row law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law batchLaw rowLaw
      query' batch row hquery' hbatch hrow hqueryNoise hnoiseLaw
  have hbatchLaw : Measure.map batch law = batchLaw := by
    calc
      Measure.map batch law = Measure.map Prod.fst (Measure.map noise law) := by
        simpa [batch, Function.comp_apply] using
          (Measure.map_map measurable_fst hnoise (μ := law)).symm
      _ = Measure.map Prod.fst (batchLaw.prod rowLaw) := by rw [hnoiseLaw]
      _ = batchLaw := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  let kernel := fun z : (Point d × Point d) ×
      HeterogeneousOnlineBatch n Sample b0 =>
    heterogeneousOnlineBatchDifference A.problem b0 z.2 i z.1.1 z.1.2
  have hkernel : AEStronglyMeasurable kernel
      ((Measure.map query' law).prod batchLaw) := by
    simpa [kernel] using
      (heterogeneousOnlineBatchDifference_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A.problem hRegularity (Measure.map query' law)
          Prod.fst Prod.snd measurable_fst.aestronglyMeasurable
          measurable_snd.aestronglyMeasurable i)
  let kernel' := hkernel.mk kernel
  have hkernel' : Measurable kernel' := hkernel.measurable_mk
  let joined := fun path => (query' path, batch path)
  have hjoined : Measurable joined := hquery'.prodMk hbatch
  have hqueryBatch : ProbabilityTheory.IndepFun query' batch law :=
    hqueryNoise.comp measurable_id measurable_fst
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
      heterogeneousOnlineWorkerDifferenceMessage
        (b := b) (b0 := b0) A x0 k i := by
    filter_upwards [hkernelMk, hqueryStrong.ae_eq_mk] with path hk hq
    calc
      kernel' (joined path) = kernel (query' path, batch path) := hk.symm
      _ = kernel (query path, batch path) :=
        congrArg (fun q => kernel (q, batch path)) hq.symm
      _ = heterogeneousOnlineWorkerDifferenceMessage A x0 k i path := by
        simp [kernel, query, batch, noise, noiseOfRound, current,
          heterogeneousOnlineWorkerDifferenceMessage, run]
  have hcalcIndep : ProbabilityTheory.IndepFun
      (fun path => kernel' (joined path)) sample law := by
    simpa [joined, sample] using
      hqueryBatchRow.comp hkernel' (measurable_pi_apply i)
  let hm :=
    heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_lawRegularity
      (b := b) (b0 := b0) A x0 hRegularity k i hstate
  have hmessageIndep : ProbabilityTheory.IndepFun
      (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i)) sample law := by
    apply hcalcIndep.congr
    · exact hcalcMessage.trans hm.ae_eq_mk
    · exact Filter.Eventually.of_forall fun _ => rfl
  have hfirst : ProbabilityTheory.IndepFun
      (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i))
      (heterogeneousOnlineWorkerCompressionSample k i) law := by
    simpa [sample, row, noise, noiseOfRound, current,
      heterogeneousOnlineWorkerCompressionSample] using hmessageIndep
  let rest := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => z.2
  let coin := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => z.1
  let restPath := fun path => rest (current path)
  let branch := fun path => coin (current path)
  let restLaw := (initialLaw.prod batchLaw).prod rowLaw
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  have hrestPath : Measurable restPath := measurable_snd.comp hcurrent
  have hbranch : Measurable branch := measurable_fst.comp hcurrent
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
      ((HeterogeneousOnlineBatch n Sample b ×
        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) → ℝ :=
    fun z => quantizerNonzeroCount A.quantizer
      (kernel' (z.1, z.2.1.2)) (z.2.2 i)
  have hsupportKernel : Measurable supportKernel := by
    have hmessage : Measurable (fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
        kernel' (z.1, z.2.1.2)) := by
      fun_prop
    have hsampleRest : Measurable (fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
        z.2.2 i) := by fun_prop
    simpa only [supportKernel] using
      (quantizerNonzeroCount_joint_measurable A.quantizer).comp
        (hmessage.prodMk hsampleRest)
  have hsupportCalc : ProbabilityTheory.IndepFun
      (fun path => supportKernel (query' path, restPath path)) branch law := by
    simpa only [Function.comp_apply] using
      hqueryRestBranch.comp hsupportKernel measurable_id
  have hsupportAE :
      (fun path => supportKernel (query' path, restPath path)) =ᵐ[law]
      (fun path => quantizerNonzeroCount A.quantizer
        (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i) path)
        (heterogeneousOnlineWorkerCompressionSample k i path)) := by
    filter_upwards [hcalcMessage, hm.ae_eq_mk] with path hcalc hmk
    change quantizerNonzeroCount A.quantizer
        (kernel' (joined path)) (sample path) =
      quantizerNonzeroCount A.quantizer
        (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i) path)
        (sample path)
    rw [hcalc, hmk]
  have hsecond : ProbabilityTheory.IndepFun
      (fun path => quantizerNonzeroCount A.quantizer
        (hm.mk (heterogeneousOnlineWorkerDifferenceMessage A x0 k i) path)
        (heterogeneousOnlineWorkerCompressionSample k i path))
      (heterogeneousOnlineRefreshBranch k) law := by
    apply hsupportCalc.congr hsupportAE
      (Filter.Eventually.of_forall fun _ => rfl)
  exact ⟨hfirst, hsecond⟩

/-- The literal moment contract and the weak law-scoped correction derive the
complete heterogeneous communication regularity interface for the actual
executable process.  No process-measurability, cost-integrability, or density
bound is accepted as an input. -/
theorem
    heterogeneousOnlineCommunicationAELawRegularity_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem) :
    HeterogeneousOnlineCommunicationAELawRegularity
      (b := b) (b0 := b0) A x0 := by
  let hstate :=
    heterogeneousOnlineProcess_aemeasurable_of_literal_and_lawRegularity
      (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity
  let hm := fun k i =>
    heterogeneousOnlineWorkerDifferenceMessage_aestronglyMeasurable_of_lawRegularity
      (b := b) (b0 := b0) A x0 hRegularity k i (hstate k)
  refine ⟨hm, ?_, ?_⟩
  · intro k i
    exact
      (heterogeneousOnlineWorkerMessageRepresentative_independences_of_lawRegularity
        (b := b) (b0 := b0) A x0 hRegularity k i (hstate k)).1
  · intro k i
    exact
      (heterogeneousOnlineWorkerMessageRepresentative_independences_of_lawRegularity
        (b := b) (b0 := b0) A x0 hRegularity k i (hstate k)).2

/-- Actual heterogeneous per-worker communication is integrable and has the
source expected-density bound directly from literal Assumption 3.3 and the
separately classified weak Track-B correction.  This is the source-derived
cost regularity result required by the executable Remark D.2 assembly; in
particular its statement has no `HeterogeneousOnlineCostMeasurability` input. -/
theorem
    heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_literal_and_lawRegularity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (heterogeneousOnlineWorkerCommunicationCost
        (b := b) (b0 := b0) A x0 K i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ∧
      (∫ path, heterogeneousOnlineWorkerCommunicationCost
          (b := b) (b0 := b0) A x0 K i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  exact
    heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le_of_ae_law_regularity
      A x0
        (heterogeneousOnlineCommunicationAELawRegularity_of_literal_and_lawRegularity
          (b := b) (b0 := b0) A x0 sigma hLiteral hRegularity)
        hQ K i

/-- The actual worker-dependent non-refresh message in executable Remark D.2
has expected support at most `expectedDensity` under the canonical product
experiment. -/
theorem heterogeneousOnlineWorkerRoundSupport_integrable_and_le_expectedDensity
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hCostMeas : HeterogeneousOnlineCostMeasurability
      (b := b) (b0 := b0) A x0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
    let message := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
      heterogeneousOnlineBatchDifference A.problem b0 (path.2 k).2.1.2 i
        (primalStep A.stepSize (run k path)) (run k path).x
    let sample := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
      (path.2 k).2.2 i
    Integrable (fun path => quantizerNonzeroCount A.quantizer
        (message path) (sample path)) (heterogeneousOnlinePathLaw A) ∧
      (∫ path, quantizerNonzeroCount A.quantizer
          (message path) (sample path) ∂heterogeneousOnlinePathLaw A) ≤
        expectedDensity A.quantizer := by
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (primalStep A.stepSize (run k path), (run k path).x)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => path.2 k
  let noiseOfRound := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
    (z.2.1.2, z.2.2)
  let noise := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    noiseOfRound (current path)
  let batch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (noise path).1
  let row := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (noise path).2
  let messageKernel := fun z : (Point d × Point d) ×
      HeterogeneousOnlineBatch n Sample b0 =>
    heterogeneousOnlineBatchDifference A.problem b0 z.2 i z.1.1 z.1.2
  let message := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    messageKernel (query path, batch path)
  let sample := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    row path i
  let batch0Law := heterogeneousOnlineBatchLaw A.problem b0
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (heterogeneousOnlineBatchLaw A.problem b) := by
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure batch0Law := by
    dsimp [batch0Law]
    unfold heterogeneousOnlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hquery : Measurable query := by
    dsimp [query, run]
    exact ((measurable_primalStep A.stepSize).comp (hCostMeas.process k)).prodMk
      ((measurable_state_x d).comp (hCostMeas.process k))
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hnoiseOfRound : Measurable noiseOfRound := by dsimp [noiseOfRound]; fun_prop
  have hnoise : Measurable noise := hnoiseOfRound.comp hcurrent
  have hbatch : Measurable batch := measurable_fst.comp hnoise
  have hrow : Measurable row := measurable_snd.comp hnoise
  have hsample : Measurable sample := (measurable_pi_apply i).comp hrow
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    simpa [query, current, run, law] using
      heterogeneousOnlineQuery_indep_current_round_of_measurable
        A x0 k (hCostMeas.process k).aemeasurable
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (Measure.map Prod.snd law) := by
        rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
        rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (SOptLib.iidStreamLaw roundLaw) := by
        rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
          dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hnoiseLaw : Measure.map noise law = batch0Law.prod rowLaw := by
    calc
      Measure.map noise law = Measure.map noiseOfRound (Measure.map current law) := by
        rw [Measure.map_map hnoiseOfRound hcurrent]
        rfl
      _ = Measure.map noiseOfRound roundLaw := by rw [hcurrentLaw]
      _ = batch0Law.prod rowLaw := by
        let restLaw := ((heterogeneousOnlineBatchLaw A.problem b).prod
          batch0Law).prod rowLaw
        calc
          Measure.map noiseOfRound roundLaw = Measure.map
              (fun z : (HeterogeneousOnlineBatch n Sample b ×
                  HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                (z.1.2, z.2)) (Measure.map Prod.snd roundLaw) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact measurable_snd
          _ = Measure.map
              (fun z : (HeterogeneousOnlineBatch n Sample b ×
                  HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ) =>
                (z.1.2, z.2)) restLaw := by
            rw [show Measure.map Prod.snd roundLaw = restLaw by
              dsimp [roundLaw, restLaw]
              unfold heterogeneousOnlineRoundLaw
              rw [Measure.map_snd_prod, measure_univ, one_smul]]
          _ = (Measure.map Prod.snd
                ((heterogeneousOnlineBatchLaw A.problem b).prod batch0Law)).prod
              (Measure.map id rowLaw) := by
            simpa only [Function.comp_apply, Prod.map_apply] using
              (MeasureTheory.Measure.map_prod_map
                ((heterogeneousOnlineBatchLaw A.problem b).prod batch0Law)
                rowLaw measurable_snd measurable_id).symm
          _ = batch0Law.prod rowLaw := by
            rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_id]
  have hqueryNoise : ProbabilityTheory.IndepFun query noise law :=
    hqueryCurrent.comp measurable_id hnoiseOfRound
  have hqueryBatchRow : ProbabilityTheory.IndepFun
      (fun path => (query path, batch path)) row law :=
    indepFun_left_adjoin_fst_of_indepFun_pair law batch0Law rowLaw
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
      _ = Measure.map (fun ξ : Worker n → Ξ => ξ i) rowLaw := by
        rw [show Measure.map row law = rowLaw by
          calc
            Measure.map row law = Measure.map Prod.snd (Measure.map noise law) := by
              simpa [row, Function.comp_apply] using
                (Measure.map_map measurable_snd hnoise (μ := law)).symm
            _ = Measure.map Prod.snd (batch0Law.prod rowLaw) := by rw [hnoiseLaw]
            _ = rowLaw := by rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = A.quantizer.law :=
        workerCompressionLaw_component_marginal A.quantizer i
  have hs := adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
    law hQ message sample hmessage hsample hindep hsampleLaw
  simpa [message, messageKernel, query, batch, noise, noiseOfRound, current,
    row, sample, run, law] using hs

/-- A measurable scalar observable of the heterogeneous executable query and
the non-coin coordinates of the current round is independent of the refresh
coin. -/
theorem heterogeneousOnline_query_rest_kernel_indep_refresh_of_cost_measurability
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hCostMeas : HeterogeneousOnlineCostMeasurability
      (b := b) (b0 := b0) A x0) (k : ℕ)
    (F : (Point d × Point d) ×
      ((HeterogeneousOnlineBatch n Sample b ×
        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) → ℝ)
    (hF : Measurable F) :
    ProbabilityTheory.IndepFun
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
        F ((primalStep A.stepSize
              (heterogeneousOnlineProcess A x0 k path),
            (heterogeneousOnlineProcess A x0 k path).x), (path.2 k).2))
      (fun path : HeterogeneousOnlineBatch n Sample b ×
          (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
        (path.2 k).1)
      (heterogeneousOnlinePathLaw A) := by
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let query := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    (primalStep A.stepSize (heterogeneousOnlineProcess A x0 k path),
      (heterogeneousOnlineProcess A x0 k path).x)
  let current := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) => path.2 k
  let rest := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => z.2
  let coin := fun z : HeterogeneousOnlineRoundNoise n Sample b b0 Ξ => z.1
  let restPath := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    rest (current path)
  let branch := fun path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
    coin (current path)
  let restLaw := ((heterogeneousOnlineBatchLaw A.problem b).prod
    (heterogeneousOnlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let coinLaw := refreshLaw A.refreshProbability A.refresh_admissible
  let roundLaw := heterogeneousOnlineRoundLaw (b := b) (b0 := b0) A
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
  haveI : IsProbabilityMeasure coinLaw := by
    dsimp [coinLaw]
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold heterogeneousOnlineRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hquery : Measurable query := by
    dsimp [query]
    exact ((measurable_primalStep A.stepSize).comp (hCostMeas.process k)).prodMk
      ((measurable_state_x d).comp (hCostMeas.process k))
  have hcurrent : Measurable current := by dsimp [current]; fun_prop
  have hrest : Measurable rest := measurable_snd
  have hcoin : Measurable coin := measurable_fst
  have hrestPath : Measurable restPath := hrest.comp hcurrent
  have hbranch : Measurable branch := hcoin.comp hcurrent
  have hqueryCurrent : ProbabilityTheory.IndepFun query current law := by
    simpa [query, current, law] using
      heterogeneousOnlineQuery_indep_current_round_of_measurable
        A x0 k (hCostMeas.process k).aemeasurable
  have hcurrentLaw : Measure.map current law = roundLaw := by
    calc
      Measure.map current law = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (Measure.map Prod.snd law) := by
        rw [Measure.map_map (measurable_pi_apply k) measurable_snd]
        rfl
      _ = Measure.map
          (fun stream : ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ =>
            stream k) (SOptLib.iidStreamLaw roundLaw) := by
        rw [show Measure.map Prod.snd law = SOptLib.iidStreamLaw roundLaw by
          dsimp [law, roundLaw, heterogeneousOnlinePathLaw]
          rw [Measure.map_snd_prod, measure_univ, one_smul]]
      _ = roundLaw := SOptLib.iidStreamLaw_map_eval roundLaw k
  have hqueryPair : ProbabilityTheory.IndepFun query
      (fun path => (restPath path, branch path)) law := by
    simpa [restPath, branch, rest, coin, current] using
      hqueryCurrent.comp measurable_id (measurable_snd.prodMk measurable_fst)
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
  simpa [query, restPath, branch, rest, coin, current, law] using
    hjoined.comp hF measurable_id

set_option maxHeartbeats 2000000 in
/-- Full finite-horizon per-worker communication accounting for executable
Remark D.2 under its worker-dependent canonical product law. -/
theorem heterogeneousOnlineWorkerCommunicationCost_integrable_and_expectation_le
    {d n : Count} {Sample : Worker n → Type*}
    {b b0 : Worker n → Count} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hCostMeas : HeterogeneousOnlineCostMeasurability
      (b := b) (b0 := b0) A x0)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (heterogeneousOnlineWorkerCommunicationCost
        (b := b) (b0 := b0) A x0 K i)
        (heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ∧
      (∫ path, heterogeneousOnlineWorkerCommunicationCost
          (b := b) (b0 := b0) A x0 K i path
          ∂heterogeneousOnlinePathLaw (b := b) (b0 := b0) A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  let law := heterogeneousOnlinePathLaw (b := b) (b0 := b0) A
  let run := heterogeneousOnlineProcess (b := b) (b0 := b0) A x0
  let supportKernel : (Point d × Point d) ×
      ((HeterogeneousOnlineBatch n Sample b ×
        HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) → ℝ :=
    fun z => quantizerNonzeroCount A.quantizer
      (heterogeneousOnlineBatchDifference A.problem b0 z.2.1.2 i
        z.1.1 z.1.2) (z.2.2 i)
  let support := fun k (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) =>
    supportKernel ((primalStep A.stepSize (run k path), (run k path).x),
      (path.2 k).2)
  let branch := fun k (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) =>
    (path.2 k).1
  let term := fun k (path : HeterogeneousOnlineBatch n Sample b ×
      (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ)) =>
    if branch k path then (d.1 : ℝ) else support k path
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
    dsimp [law]
    unfold heterogeneousOnlinePathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsupportKernel : Measurable supportKernel := by
    have hquery : Measurable (fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) => z.1) :=
      measurable_fst
    have hbatch : Measurable (fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
        z.2.1.2) := by fun_prop
    have hmessage : Measurable (fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
        heterogeneousOnlineBatchDifference A.problem b0 z.2.1.2 i
          z.1.1 z.1.2) := by
      simpa only [Function.comp_apply] using
        (hCostMeas.difference i).comp (hquery.prodMk hbatch)
    have hsample : Measurable (fun z : (Point d × Point d) ×
        ((HeterogeneousOnlineBatch n Sample b ×
          HeterogeneousOnlineBatch n Sample b0) × (Worker n → Ξ)) =>
        z.2.2 i) := by fun_prop
    simpa [supportKernel] using
      (quantizerNonzeroCount_joint_measurable A.quantizer).comp
        (hmessage.prodMk hsample)
  have hsupport (k : ℕ) : Integrable (support k) law ∧
      (∫ path, support k path ∂law) ≤ expectedDensity A.quantizer := by
    simpa [support, supportKernel, run, law] using
      heterogeneousOnlineWorkerRoundSupport_integrable_and_le_expectedDensity
        A x0 hCostMeas hQ k i
  have hbranchMeas (k : ℕ) : Measurable (branch k) := by
    dsimp [branch]
    fun_prop
  have hbranchLaw (k : ℕ) : Measure.map (branch k) law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law] using
      heterogeneousOnlinePathLaw_refresh_marginal
        (b := b) (b0 := b0) A k
  have hindep (k : ℕ) :
      ProbabilityTheory.IndepFun (support k) (branch k) law := by
    have h :=
      heterogeneousOnline_query_rest_kernel_indep_refresh_of_cost_measurability
        A x0 hCostMeas k supportKernel hsupportKernel
    simpa only [support, branch, law, run] using h
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
    let refreshGate := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
      if branch k path = true then (d.1 : ℝ) else 0
    let differenceGate := fun path : HeterogeneousOnlineBatch n Sample b ×
        (ℕ → HeterogeneousOnlineRoundNoise n Sample b b0 Ξ) =>
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
          exact MeasureTheory.integral_map (hbranchMeas k).aemeasurable
            (by fun_prop)
        _ = ∫ c : Bool, (if c then (d.1 : ℝ) else 0)
            ∂refreshLaw A.refreshProbability A.refresh_admissible := by
          rw [hbranchLaw k]
        _ = A.refreshProbability * d.1 := by
          rw [integral_refreshLaw_if A.refreshProbability
            A.refresh_admissible (d.1 : ℝ) 0]
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

/-- Any measurable scalar observable of the Algorithm 1 strict-past state and
the current compressor row is independent of the current refresh coin.  This
is the cost-accounting form of the canonical product-law semantics. -/
theorem marina_state_compression_kernel_indep_refresh
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ)
    (F : State d × (Worker n → Ξ) → ℝ) (hF : Measurable F) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → BasicRoundNoise n Ξ =>
        F (marinaProcess A x0 k path, (path k).2))
      (fun path : ℕ → BasicRoundNoise n Ξ => (path k).1)
      (basicPathLaw A) := by
  let P := basicPathLaw A
  let state := fun path : ℕ → BasicRoundNoise n Ξ => marinaProcess A x0 k path
  let current := fun path : ℕ → BasicRoundNoise n Ξ => path k
  let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
  let branch := fun path : ℕ → BasicRoundNoise n Ξ => (path k).1
  let rest := fun z : BasicRoundNoise n Ξ => z.2
  let branchRound := fun z : BasicRoundNoise n Ξ => z.1
  let stateLaw := Measure.map state P
  let rowLaw := workerCompressionLaw (n := n) A.quantizer
  let roundLaw := basicRoundLaw A
  let joined := fun path : ℕ → BasicRoundNoise n Ξ => (state path, row path)
  let Z := fun path : ℕ → BasicRoundNoise n Ξ => (state path, current path)
  let leftProd := fun z : State d × BasicRoundNoise n Ξ => (z.1, rest z.2)
  let rightProd := fun z : State d × BasicRoundNoise n Ξ => branchRound z.2
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : Measurable state := by
    have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
    have hle : (⨆ j : Fin k, MeasurableSpace.comap
        (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → BasicRoundNoise n Ξ)) := by
      refine iSup_le fun j => ?_
      exact (measurable_pi_apply j.1).comap_le
    simpa [state] using hs.mono hle le_rfl
  haveI : IsProbabilityMeasure stateLaw :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hcurrent : Measurable current := measurable_pi_apply k
  have hstateCurrent : ProbabilityTheory.IndepFun state current P := by
    let pastPrefix := fun path : ℕ → BasicRoundNoise n Ξ =>
      fun j : Fin k => path j.1
    let prefixLaw := Measure.map pastPrefix P
    have hpastPrefix : Measurable pastPrefix := by
      dsimp [pastPrefix]
      exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
    haveI : IsProbabilityMeasure prefixLaw :=
      Measure.isProbabilityMeasure_map hpastPrefix.aemeasurable
    have hpastCurrent : ProbabilityTheory.IndepFun pastPrefix current P := by
      refine indepFun_of_map_prod_eq_prod_laws
        (P := P) (Z := fun path => (pastPrefix path, current path))
        (mu := prefixLaw) (nu := roundLaw) ?_ ?_
      · exact (hpastPrefix.prodMk hcurrent).aemeasurable
      · simpa [pastPrefix, current, prefixLaw, roundLaw, P, basicPathLaw,
          SOptLib.iidStreamLaw] using
          (infinitePi_prefix_current_map_eq_prod
            (fun _ : ℕ => basicRoundLaw A) k)
    have hstrict : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        state := by
      have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
      have hstrict_le : (⨆ j : Fin k, MeasurableSpace.comap
          (fun path : ℕ → BasicRoundNoise n Ξ => path j.1) inferInstance) ≤
          MeasurableSpace.comap pastPrefix inferInstance := by
        refine iSup_le fun j => ?_
        have hpast_comap :
            Measurable[MeasurableSpace.comap pastPrefix inferInstance]
              pastPrefix := measurable_iff_comap_le.mpr le_rfl
        exact ((measurable_pi_apply j).comp hpast_comap).comap_le
      simpa [state] using hs.mono hstrict_le le_rfl
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap pastPrefix inferInstance)
        (MeasurableSpace.comap current inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpastCurrent
    exact indepFun_of_measurable_left_of_indep_comap hstrict hcomap
  have hcurrentLaw : Measure.map current P = roundLaw := by
    simpa [current, P, roundLaw] using basicPathLaw_round_marginal A k
  have hZlaw : Measure.map Z P = stateLaw.prod roundLaw := by
    have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hstate.aemeasurable hcurrent.aemeasurable).1 hstateCurrent
    simpa [Z, stateLaw, hcurrentLaw] using hmap
  have hround : ProbabilityTheory.IndepFun rest branchRound roundLaw := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := rowLaw) measurable_id measurable_id).symm
    simpa [roundLaw, basicRoundLaw, rowLaw, rest, branchRound] using h
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (stateLaw.prod roundLaw) :=
    indepFun_prod_left_adjoin_of_indepFun stateLaw roundLaw rest branchRound
      measurable_snd measurable_fst hround
  have hleftProd : Measurable leftProd :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hrightProd : Measurable rightProd := measurable_fst.comp measurable_snd
  have hZ : Measurable Z := hstate.prodMk hcurrent
  have hjoinedBranch : ProbabilityTheory.IndepFun joined branch P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hstate.prodMk (measurable_snd.comp hcurrent)).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    calc
      Measure.map (fun path => (joined path, branch path)) P =
          Measure.map (fun z => (leftProd z, rightProd z))
            (Measure.map Z P) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact hleftProd.prodMk hrightProd
        · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (stateLaw.prod roundLaw) := by rw [hZlaw]
      _ = (Measure.map leftProd (stateLaw.prod roundLaw)).prod
          (Measure.map rightProd (stateLaw.prod roundLaw)) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleftProd.aemeasurable hrightProd.aemeasurable).1 hprod
      _ = (Measure.map joined P).prod (Measure.map branch P) := by
        rw [show Measure.map leftProd (stateLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            _ = Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (stateLaw.prod roundLaw) =
            Measure.map branch P by
          calc
            _ = Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map branch P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  simpa [joined, branch, state, row, P] using
    hjoinedBranch.comp hF measurable_id

/-- The actual Algorithm 1 non-refresh message of worker `i` has expected
support at most `expectedDensity`; its input is the generated state query at
the same round and its sample is the corresponding canonical worker sample. -/
theorem basicWorkerRoundSupport_integrable_and_le_expectedDensity
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    let message := fun path : ℕ → BasicRoundNoise n Ξ =>
      localGradientDifference A.problem i
        (primalStep A.stepSize (marinaProcess A x0 k path))
        (marinaProcess A x0 k path).x
    let sample := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2 i
    Integrable
        (fun path => quantizerNonzeroCount A.quantizer
          (message path) (sample path)) (basicPathLaw A) ∧
      (∫ path, quantizerNonzeroCount A.quantizer
          (message path) (sample path) ∂basicPathLaw A) ≤
        expectedDensity A.quantizer := by
  let law := basicPathLaw A
  let query := fun path : ℕ → BasicRoundNoise n Ξ =>
    (primalStep A.stepSize (marinaProcess A x0 k path),
      (marinaProcess A x0 k path).x)
  let row := fun path : ℕ → BasicRoundNoise n Ξ => (path k).2
  let message := fun path : ℕ → BasicRoundNoise n Ξ =>
    localGradientDifference A.problem i (query path).1 (query path).2
  let sample := fun path : ℕ → BasicRoundNoise n Ξ => row path i
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hfresh := marina_strictPast_query_indep_compression_row
    A x0 Llocal hSmooth k
  have hmessageOfQuery : Measurable
      (fun z : Point d × Point d =>
        localGradientDifference A.problem i z.1 z.2) := by
    exact ((measurable_localGradient A.problem i).comp measurable_fst).sub
      ((measurable_localGradient A.problem i).comp measurable_snd)
  have hquery : Measurable query := by
    have hs := marinaProcess_strictPast_measurable A x0 Llocal hSmooth k
    have hs' : Measurable (marinaProcess A x0 k) := by
      exact hs.mono (iSup_le fun j => (measurable_pi_apply (j : ℕ)).comap_le) le_rfl
    exact (measurable_primalStep A.stepSize).comp hs' |>.prodMk
      ((measurable_state_x d).comp hs')
  have hrow : Measurable row := by
    dsimp [row]
    fun_prop
  have hmessage : Measurable message := hmessageOfQuery.comp hquery
  have hsample : Measurable sample := (measurable_pi_apply i).comp hrow
  have hindep : ProbabilityTheory.IndepFun message sample law := by
    have h := hfresh.1.comp hmessageOfQuery (measurable_pi_apply i)
    simpa [message, sample, query, row, law] using h
  have hsampleLaw : Measure.map sample law = A.quantizer.law := by
    calc
      Measure.map sample law =
          Measure.map (fun samples : Worker n → Ξ => samples i)
            (Measure.map row law) := by
        simpa [sample, Function.comp_apply] using
          (Measure.map_map (measurable_pi_apply i) hrow (μ := law)).symm
      _ = Measure.map (fun samples : Worker n → Ξ => samples i)
          (workerCompressionLaw A.quantizer) := by
        rw [show Measure.map row law = workerCompressionLaw A.quantizer by
          simpa [row, law] using hfresh.2]
      _ = A.quantizer.law :=
        workerCompressionLaw_component_marginal A.quantizer i
  simpa [message, sample, query, law] using
    (adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
      law hQ message sample hmessage hsample hindep hsampleLaw)

set_option maxHeartbeats 800000 in
/-- Full finite-horizon per-worker Algorithm 1 communication accounting.
The dense initialization and refresh messages are exact, while adaptive
compressed messages use Definition 1.1 only through its supremum upper bound. -/
theorem basicWorkerCommunicationCost_integrable_and_expectation_le
    {d n : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (basicWorkerCommunicationCost A x0 K i) (basicPathLaw A) ∧
      (∫ path, basicWorkerCommunicationCost A x0 K i path
          ∂basicPathLaw A) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  let law := basicPathLaw A
  let supportKernel : State d × (Worker n → Ξ) → ℝ := fun z =>
    quantizerNonzeroCount A.quantizer
      (localGradientDifference A.problem i
        (primalStep A.stepSize z.1) z.1.x)
      (z.2 i)
  let support := fun k (path : ℕ → BasicRoundNoise n Ξ) =>
    supportKernel (marinaProcess A x0 k path, (path k).2)
  let branch := fun k (path : ℕ → BasicRoundNoise n Ξ) => (path k).1
  let term := fun k (path : ℕ → BasicRoundNoise n Ξ) =>
    if branch k path then (d.1 : ℝ) else support k path
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (basicRoundLaw A) := by
    unfold basicRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold basicPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsupportKernelRaw : Measurable
      (fun z : State d × (Worker n → Ξ) =>
        quantizerNonzeroCount A.quantizer
          (localGradientDifference A.problem i
            (primalStep A.stepSize z.1) z.1.x)
          (z.2 i)) := by
    have hxnext : Measurable
        (fun z : State d × (Worker n → Ξ) => primalStep A.stepSize z.1) :=
      (measurable_primalStep A.stepSize).comp measurable_fst
    have hx : Measurable
        (fun z : State d × (Worker n → Ξ) => z.1.x) :=
      (measurable_state_x d).comp measurable_fst
    have hmessage : Measurable
        (fun z : State d × (Worker n → Ξ) =>
          localGradientDifference A.problem i
            (primalStep A.stepSize z.1) z.1.x) := by
      unfold localGradientDifference
      exact ((measurable_localGradient A.problem i).comp hxnext).sub
        ((measurable_localGradient A.problem i).comp hx)
    have hsample : Measurable
        (fun z : State d × (Worker n → Ξ) => z.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    rw [show (fun z : State d × (Worker n → Ξ) =>
        quantizerNonzeroCount A.quantizer
          (localGradientDifference A.problem i
            (primalStep A.stepSize z.1) z.1.x) (z.2 i)) =
        fun z => ∑ j : Fin d.1,
          if A.quantizer.apply
              (localGradientDifference A.problem i
                (primalStep A.stepSize z.1) z.1.x) (z.2 i) j ≠ 0
          then (1 : ℝ) else 0 by
      funext z
      unfold quantizerNonzeroCount
      exact Finset.natCast_card_filter
        (fun j : Fin d.1 => A.quantizer.apply
          (localGradientDifference A.problem i
            (primalStep A.stepSize z.1) z.1.x) (z.2 i) j ≠ 0) Finset.univ]
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun z : State d × (Worker n → Ξ) =>
        A.quantizer.apply
          (localGradientDifference A.problem i
            (primalStep A.stepSize z.1) z.1.x) (z.2 i) j) :=
      (EuclideanSpace.proj j).continuous.measurable.comp
        (A.quantizer.measurable_apply_uncurry.comp (hmessage.prodMk hsample))
    have hzero : MeasurableSet {z : State d × (Worker n → Ξ) |
        A.quantizer.apply
          (localGradientDifference A.problem i
            (primalStep A.stepSize z.1) z.1.x) (z.2 i) j = 0} :=
      hj (measurableSet_singleton 0)
    exact Measurable.ite hzero.compl measurable_const measurable_const
  have hsupportKernel : Measurable supportKernel := by
    simpa only [supportKernel] using hsupportKernelRaw
  have hsupport (k : ℕ) :
      Integrable (support k) law ∧
        (∫ path, support k path ∂law) ≤ expectedDensity A.quantizer := by
    simpa [support, supportKernel, law] using
      basicWorkerRoundSupport_integrable_and_le_expectedDensity
        A x0 Llocal hSmooth hQ k i
  have hbranchMeas (k : ℕ) : Measurable (branch k) := by
    dsimp [branch]
    fun_prop
  have hbranchLaw (k : ℕ) : Measure.map (branch k) law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law] using basicPathLaw_refresh_marginal A k
  have hindep (k : ℕ) :
      ProbabilityTheory.IndepFun (support k) (branch k) law := by
    have h := marina_state_compression_kernel_indep_refresh
      A x0 Llocal hSmooth k supportKernel hsupportKernel
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
    let refreshGate := fun path : ℕ → BasicRoundNoise n Ξ =>
      if branch k path = true then (d.1 : ℝ) else 0
    let differenceGate := fun path : ℕ → BasicRoundNoise n Ξ =>
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
    have hnonneg : 0 ≤ 1 - A.refreshProbability :=
      sub_nonneg.mpr A.refresh_admissible.2
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
        exact (hsupport k).2
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

/-- At one Algorithm 2 round, the actual minibatch difference message of a
fixed worker is independent of that worker's fresh compressor sample.  Hence
its expected support is bounded by Definition 1.1's supremum. -/
theorem finiteSumWorkerRoundSupport_integrable_and_le_expectedDensity
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) :
    let message := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
      let s := finiteSumProcess (b0 := b0) A x0 k path
      finiteSumBatchDifference A.problem (path k).2.1 i
        (primalStep A.stepSize s) s.x
    let sample := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
      (path k).2.2 i
    Integrable
        (fun path => quantizerNonzeroCount A.quantizer
          (message path) (sample path)) (finiteSumPathLaw A batchLaw) ∧
      (∫ path, quantizerNonzeroCount A.quantizer
          (message path) (sample path) ∂finiteSumPathLaw A batchLaw) ≤
        expectedDensity A.quantizer := by
  let P := finiteSumPathLaw A batchLaw
  let query := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (primalStep A.stepSize (finiteSumProcess (b0 := b0) A x0 k path),
      (finiteSumProcess (b0 := b0) A x0 k path).x)
  let batch := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (path k).2.1 i
  let sample := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (path k).2.2 i
  let messageKernel := fun z : (Point d × Point d) ×
      FiniteSumWorkerBatch m b0 =>
    finiteSumWorkerBatchDifference A.problem z.2 i z.1.1 z.1.2
  let message := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    messageKernel (query path, batch path)
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (batchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  have hquery : Measurable query := by
    have hs := (finiteSumProcess_strictPast_measurable
      (b0 := b0) A x0 k).mono
        (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
        le_rfl
    exact ((measurable_primalStep A.stepSize).comp hs).prodMk
      ((measurable_state_x d).comp hs)
  have hbatch : Measurable batch := by
    dsimp [batch]
    fun_prop
  have hsample : Measurable sample := by
    dsimp [sample]
    fun_prop
  have hqueryNoise : ProbabilityTheory.IndepFun query
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        (batch path, sample path)) P := by
    simpa [query, batch, sample, P, finiteSumProcess, finiteSumRun_succ,
      finiteSumStep] using
      finite_sum_strictPast_query_indep_worker_noise
        A x0 batchLaw hBatchLaw k i
  have hpairLaw :
      Measure.map
          (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
            (batch path, sample path)) P =
        (batchLaw k i).prod A.quantizer.law := by
    simpa [batch, sample, P] using
      finite_sum_path_worker_noise_map_eq_prod A batchLaw hBatchLaw k i
  have hqueryBatchSample : ProbabilityTheory.IndepFun
      (fun path => (query path, batch path)) sample P :=
    indepFun_left_adjoin_fst_of_indepFun_pair P (batchLaw k i)
      A.quantizer.law query batch sample hquery hbatch hsample
      hqueryNoise hpairLaw
  have hmessageKernel : Measurable messageKernel := by
    simpa [messageKernel] using
      finiteSumWorkerBatchDifference_joint_measurable
        (b0 := b0) A.problem i
  have hmessage : Measurable message :=
    hmessageKernel.comp (hquery.prodMk hbatch)
  have hindep : ProbabilityTheory.IndepFun message sample P := by
    simpa [message] using
      hqueryBatchSample.comp hmessageKernel measurable_id
  have hsampleLaw : Measure.map sample P = A.quantizer.law := by
    calc
      Measure.map sample P =
          Measure.map Prod.snd
            (Measure.map (fun path => (batch path, sample path)) P) := by
        simpa only [Function.comp_apply] using
          (Measure.map_map measurable_snd (hbatch.prodMk hsample) (μ := P)).symm
      _ = Measure.map Prod.snd ((batchLaw k i).prod A.quantizer.law) := by
        rw [hpairLaw]
      _ = A.quantizer.law := by simp
  have hsupport :=
    adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
      P hQ message sample hmessage hsample hindep hsampleLaw
  simpa [message, messageKernel, query, batch, sample,
    finiteSumBatchDifference, finiteSumWorkerBatchDifference] using hsupport

/-- A measurable cost built from the generated Algorithm 2 strict-past state
and the non-coin part of the same round is independent of the refresh coin. -/
theorem finiteSum_state_rest_kernel_indep_refresh
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw) (k : ℕ)
    (F : State d × (FiniteSumBatch n m b0 × (Worker n → Ξ)) → ℝ)
    (hF : Measurable F) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
        F (finiteSumProcess (b0 := b0) A x0 k path, (path k).2))
      (fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => (path k).1)
      (finiteSumPathLaw A batchLaw) := by
  let P := finiteSumPathLaw A batchLaw
  let state := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    finiteSumProcess (b0 := b0) A x0 k path
  let current := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ => path k
  let rest := fun z : FiniteSumRoundNoise n m b0 Ξ => z.2
  let branchRound := fun z : FiniteSumRoundNoise n m b0 Ξ => z.1
  let stateLaw := Measure.map state P
  let restLaw := (finiteSumBatchJointLaw batchLaw k).prod
    (workerCompressionLaw (n := n) A.quantizer)
  let roundLaw := finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw k)
  let joined := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (state path, rest (current path))
  let branch := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    branchRound (current path)
  let Z := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
    (state path, current path)
  let leftProd := fun z : State d × FiniteSumRoundNoise n m b0 Ξ =>
    (z.1, rest z.2)
  let rightProd := fun z : State d × FiniteSumRoundNoise n m b0 Ξ =>
    branchRound z.2
  letI (t : ℕ) (i : Worker n) : IsProbabilityMeasure (batchLaw t i) :=
    hBatchLaw t i
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold finiteSumPathLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  have hstate : Measurable state := by
    have hs := finiteSumProcess_strictPast_measurable (b0 := b0) A x0 k
    simpa [state] using hs.mono
      (finiteSumStrictPast_le (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k)
      le_rfl
  haveI : IsProbabilityMeasure stateLaw :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hcurrent : Measurable current := measurable_pi_apply k
  have hstateCurrent : ProbabilityTheory.IndepFun state current P := by
    let pastPrefix := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
      fun j : Fin k => path j.1
    let prefixLaw := Measure.map pastPrefix P
    have hpastPrefix : Measurable pastPrefix := by
      dsimp [pastPrefix]
      exact measurable_pi_lambda _ fun j => measurable_pi_apply j.1
    haveI : IsProbabilityMeasure prefixLaw :=
      Measure.isProbabilityMeasure_map hpastPrefix.aemeasurable
    have hpastCurrent : ProbabilityTheory.IndepFun pastPrefix current P := by
      refine indepFun_of_map_prod_eq_prod_laws
        (P := P) (Z := fun path => (pastPrefix path, current path))
        (mu := prefixLaw) (nu := roundLaw) ?_ ?_
      · exact (hpastPrefix.prodMk hcurrent).aemeasurable
      · simpa [pastPrefix, current, prefixLaw, roundLaw, P] using
          finite_sum_prefix_current_round_map_eq_prod
            A batchLaw hBatchLaw k
    have hstrict : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        state := by
      have hs := finiteSumProcess_strictPast_measurable (b0 := b0) A x0 k
      have hstrict_le : finiteSumStrictPast
          (n := n) (m := m) (b0 := b0) (Ξ := Ξ) k ≤
          MeasurableSpace.comap pastPrefix inferInstance := by
        refine iSup_le fun j => ?_
        have hpast_comap :
            Measurable[MeasurableSpace.comap pastPrefix inferInstance]
              pastPrefix := measurable_iff_comap_le.mpr le_rfl
        exact ((measurable_pi_apply j).comp hpast_comap).comap_le
      simpa [state] using hs.mono hstrict_le le_rfl
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap pastPrefix inferInstance)
        (MeasurableSpace.comap current inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpastCurrent
    exact indepFun_of_measurable_left_of_indep_comap hstrict hcomap
  have hcurrentLaw : Measure.map current P = roundLaw := by
    simpa [current, P, roundLaw] using
      finiteSumPathLaw_round_marginal A batchLaw hBatchLaw k
  have hZlaw : Measure.map Z P = stateLaw.prod roundLaw := by
    have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hstate.aemeasurable hcurrent.aemeasurable).1 hstateCurrent
    simpa [Z, stateLaw, hcurrentLaw] using hmap
  have hround : ProbabilityTheory.IndepFun rest branchRound roundLaw := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [roundLaw, finiteSumRoundLaw, restLaw, rest, branchRound] using h
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (stateLaw.prod roundLaw) :=
    indepFun_prod_left_adjoin_of_indepFun stateLaw roundLaw rest branchRound
      measurable_snd measurable_fst hround
  have hleftProd : Measurable leftProd :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hrightProd : Measurable rightProd := measurable_fst.comp measurable_snd
  have hZ : Measurable Z := hstate.prodMk hcurrent
  have hjoinedBranch : ProbabilityTheory.IndepFun joined branch P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hstate.prodMk (measurable_snd.comp hcurrent)).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    calc
      Measure.map (fun path => (joined path, branch path)) P =
          Measure.map (fun z => (leftProd z, rightProd z))
            (Measure.map Z P) := by
        rw [MeasureTheory.Measure.map_map]
        · rfl
        · exact hleftProd.prodMk hrightProd
        · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (stateLaw.prod roundLaw) := by rw [hZlaw]
      _ = (Measure.map leftProd (stateLaw.prod roundLaw)).prod
          (Measure.map rightProd (stateLaw.prod roundLaw)) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleftProd.aemeasurable hrightProd.aemeasurable).1 hprod
      _ = (Measure.map joined P).prod (Measure.map branch P) := by
        rw [show Measure.map leftProd (stateLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            _ = Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (stateLaw.prod roundLaw) =
            Measure.map branch P by
          calc
            _ = Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map branch P := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  simpa [joined, branch, state, current, rest, branchRound, P] using
    hjoinedBranch.comp hF measurable_id

set_option maxHeartbeats 2000000 in
/-- Full finite-horizon per-worker Algorithm 2 communication accounting under
an arbitrary admissible worker batch schedule. -/
theorem finiteSumWorkerCommunicationCost_integrable_and_expectation_le
    {d n m b0 : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : FiniteSumData d n m Ξ) (x0 : Point d)
    (batchLaw : FiniteSumBatchLaw n m b0)
    (hBatchLaw : FiniteSumBatchLawAdmissible batchLaw)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) (i : Worker n) :
    Integrable (finiteSumWorkerCommunicationCost A x0 K i)
        (finiteSumPathLaw A batchLaw) ∧
      (∫ path, finiteSumWorkerCommunicationCost A x0 K i path
          ∂finiteSumPathLaw A batchLaw) ≤
        allWorkerCommunicationCount d K A.refreshProbability
          (expectedDensity A.quantizer) := by
  let law := finiteSumPathLaw A batchLaw
  let supportKernel : State d ×
      (FiniteSumBatch n m b0 × (Worker n → Ξ)) → ℝ := fun z =>
    quantizerNonzeroCount A.quantizer
      (finiteSumBatchDifference A.problem z.2.1 i
        (primalStep A.stepSize z.1) z.1.x)
      (z.2.2 i)
  let support := fun k (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) =>
    supportKernel (finiteSumProcess (b0 := b0) A x0 k path, (path k).2)
  let branch := fun k (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) =>
    (path k).1
  let term := fun k (path : ℕ → FiniteSumRoundNoise n m b0 Ξ) =>
    if branch k path then (d.1 : ℝ) else support k path
  letI (t : ℕ) (j : Worker n) : IsProbabilityMeasure (batchLaw t j) :=
    hBatchLaw t j
  letI (t : ℕ) : IsProbabilityMeasure (finiteSumBatchJointLaw batchLaw t) :=
    finiteSumBatchJointLaw_isProbability batchLaw hBatchLaw t
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  letI (t : ℕ) : IsProbabilityMeasure
      (finiteSumRoundLaw A (finiteSumBatchJointLaw batchLaw t)) := by
    unfold finiteSumRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold finiteSumPathLaw
    infer_instance
  have hsupportKernelRaw : Measurable (fun z : State d ×
      (FiniteSumBatch n m b0 × (Worker n → Ξ)) =>
      quantizerNonzeroCount A.quantizer
        (finiteSumBatchDifference A.problem z.2.1 i
          (primalStep A.stepSize z.1) z.1.x)
        (z.2.2 i)) := by
    have hxnext : Measurable (fun z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        primalStep A.stepSize z.1) :=
      (measurable_primalStep A.stepSize).comp measurable_fst
    have hx : Measurable (fun z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) => z.1.x) :=
      (measurable_state_x d).comp measurable_fst
    have hbatch : Measurable (fun z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) => z.2.1) :=
      measurable_fst.comp measurable_snd
    have hmessage : Measurable (fun z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        finiteSumBatchDifference A.problem z.2.1 i
          (primalStep A.stepSize z.1) z.1.x) := by
      simpa only [Function.comp_apply] using
        (finiteSumBatchDifference_joint_measurable
          (b0 := b0) A.problem i).comp ((hxnext.prodMk hx).prodMk hbatch)
    have hsample : Measurable (fun z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) => z.2.2 i) :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
    rw [show (fun z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        quantizerNonzeroCount A.quantizer
          (finiteSumBatchDifference A.problem z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i)) =
        fun z => ∑ j : Fin d.1,
          if A.quantizer.apply
              (finiteSumBatchDifference A.problem z.2.1 i
                (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j ≠ 0
          then (1 : ℝ) else 0 by
      funext z
      unfold quantizerNonzeroCount
      exact Finset.natCast_card_filter
        (fun j : Fin d.1 => A.quantizer.apply
          (finiteSumBatchDifference A.problem z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j ≠ 0)
        Finset.univ]
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) =>
        A.quantizer.apply
          (finiteSumBatchDifference A.problem z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j) :=
      (EuclideanSpace.proj j).continuous.measurable.comp
        (A.quantizer.measurable_apply_uncurry.comp (hmessage.prodMk hsample))
    have hzero : MeasurableSet {z : State d ×
        (FiniteSumBatch n m b0 × (Worker n → Ξ)) |
        A.quantizer.apply
          (finiteSumBatchDifference A.problem z.2.1 i
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 i) j = 0} :=
      hj (measurableSet_singleton 0)
    exact Measurable.ite hzero.compl measurable_const measurable_const
  have hsupportKernel : Measurable supportKernel := by
    simpa only [supportKernel] using hsupportKernelRaw
  have hsupport (k : ℕ) :
      Integrable (support k) law ∧
        (∫ path, support k path ∂law) ≤ expectedDensity A.quantizer := by
    simpa [support, supportKernel, law] using
      finiteSumWorkerRoundSupport_integrable_and_le_expectedDensity
        A x0 batchLaw hBatchLaw hQ k i
  have hbranchMeas (k : ℕ) : Measurable (branch k) := by
    dsimp [branch]
    fun_prop
  have hbranchLaw (k : ℕ) : Measure.map (branch k) law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law] using
      finiteSumPathLaw_refresh_marginal A batchLaw hBatchLaw k
  have hindep (k : ℕ) :
      ProbabilityTheory.IndepFun (support k) (branch k) law := by
    have h := finiteSum_state_rest_kernel_indep_refresh
      A x0 batchLaw hBatchLaw k supportKernel hsupportKernel
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
    let refreshGate := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
      if branch k path = true then (d.1 : ℝ) else 0
    let differenceGate := fun path : ℕ → FiniteSumRoundNoise n m b0 Ξ =>
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

/-- The refresh coordinate of every PP-MARINA round has the canonical
Bernoulli law. -/
theorem ppPathLaw_refresh_marginal
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (k : ℕ) :
    Measure.map
        (fun path : ℕ → PPRoundNoise n r Ξ => (path k).1)
        (ppPathLaw A) =
      refreshLaw A.refreshProbability A.refresh_admissible := by
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  calc
    Measure.map
        (fun path : ℕ → PPRoundNoise n r Ξ => (path k).1)
        (ppPathLaw A) =
        Measure.map Prod.fst
          (Measure.map (fun path : ℕ → PPRoundNoise n r Ξ => path k)
            (ppPathLaw A)) := by
      rw [Measure.map_map measurable_fst (measurable_pi_apply k)]
      rfl
    _ = Measure.map Prod.fst (ppRoundLaw A) := by
      rw [show Measure.map (fun path : ℕ → PPRoundNoise n r Ξ => path k)
          (ppPathLaw A) = ppRoundLaw A by
        simpa [ppPathLaw] using
          SOptLib.iidStreamLaw_map_eval (ppRoundLaw (n := n) (r := r) A) k]
    _ = refreshLaw A.refreshProbability A.refresh_admissible := by
      simp [ppRoundLaw]

/-- At one PP-MARINA round, the actual message attached to an indexed sampled
client occurrence has expected support at most `expectedDensity`.  The index is
an occurrence index, so repeated sampled clients remain distinct. -/
theorem ppOccurrenceRoundSupport_integrable_and_le_expectedDensity
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (j : Fin r.1) :
    let state := fun path : ℕ → PPRoundNoise n r Ξ =>
      ppProcess (r := r) A x0 k path
    let message := fun path : ℕ → PPRoundNoise n r Ξ =>
      localGradientDifference A.problem ((path k).2.1 j)
        (primalStep A.stepSize (state path)) (state path).x
    let sample := fun path : ℕ → PPRoundNoise n r Ξ => (path k).2.2 j
    Integrable
        (fun path => quantizerNonzeroCount A.quantizer
          (message path) (sample path)) (ppPathLaw A) ∧
      (∫ path, quantizerNonzeroCount A.quantizer
          (message path) (sample path) ∂ppPathLaw A) ≤
        expectedDensity A.quantizer := by
  let P := ppPathLaw (r := r) A
  let state := fun path : ℕ → PPRoundNoise n r Ξ =>
    ppProcess (r := r) A x0 k path
  let query := fun path : ℕ → PPRoundNoise n r Ξ =>
    (primalStep A.stepSize (state path), (state path).x)
  let row := fun path : ℕ → PPRoundNoise n r Ξ =>
    fun q : Fin r.1 => ((path k).2.1 q, (path k).2.2 q)
  let worker := fun path : ℕ → PPRoundNoise n r Ξ => (row path j).1
  let sample := fun path : ℕ → PPRoundNoise n r Ξ => (row path j).2
  let messageKernel := fun z : (Point d × Point d) × Worker n =>
    localGradientDifference A.problem z.2 z.1.1 z.1.2
  let message := fun path : ℕ → PPRoundNoise n r Ξ =>
    messageKernel (query path, worker path)
  let pairLaw := (workerLaw n).prod A.quantizer.law
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure pairLaw := by
    dsimp [pairLaw]
    infer_instance
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hstate : Measurable state := by
    have hs := ppProcess_strictPast_measurable
      (r := r) A x0 Llocal hSmooth k
    have hle : (⨆ q : Fin k, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path q.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun q => ?_
      exact (measurable_pi_apply q.1).comap_le
    simpa [state] using hs.mono hle le_rfl
  have hquery : Measurable query :=
    ((measurable_primalStep A.stepSize).comp hstate).prodMk
      ((measurable_state_x d).comp hstate)
  have hrow : Measurable row := by
    dsimp [row]
    fun_prop
  have hworker : Measurable worker :=
    measurable_fst.comp ((measurable_pi_apply j).comp hrow)
  have hsample : Measurable sample :=
    measurable_snd.comp ((measurable_pi_apply j).comp hrow)
  have hmessageKernel : Measurable messageKernel := by
    have hsel := pp_selected_localGradient_joint_measurable A.problem
    exact (hsel.comp (measurable_snd.prodMk
      (measurable_fst.comp measurable_fst))).sub
      (hsel.comp (measurable_snd.prodMk
        (measurable_snd.comp measurable_fst)))
  have hmessage : Measurable message :=
    hmessageKernel.comp (hquery.prodMk hworker)
  have hfresh := pp_strictPast_query_indep_pair_row
    (r := r) A x0 Llocal hSmooth k
  have hqueryRow : ProbabilityTheory.IndepFun query row P := by
    simpa [query, row, state, P] using hfresh.1
  have hrowLaw : Measure.map row P =
      Measure.infinitePi (fun _ : Fin r.1 => pairLaw) := by
    simpa [row, pairLaw, P] using hfresh.2
  have hqueryPair : ProbabilityTheory.IndepFun query
      (fun path => (worker path, sample path)) P := by
    simpa [worker, sample] using
      hqueryRow.comp measurable_id (measurable_pi_apply j)
  have hpairLaw : Measure.map (fun path => (worker path, sample path)) P =
      pairLaw := by
    calc
      Measure.map (fun path => (worker path, sample path)) P =
          Measure.map (fun q : Fin r.1 → Worker n × Ξ => q j)
            (Measure.map row P) := by
        simpa [worker, sample, Function.comp_apply] using
          (Measure.map_map (measurable_pi_apply j) hrow (μ := P)).symm
      _ = Measure.map (fun q : Fin r.1 → Worker n × Ξ => q j)
          (Measure.infinitePi (fun _ : Fin r.1 => pairLaw)) := by rw [hrowLaw]
      _ = pairLaw := MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin r.1 => pairLaw) j
  have hqueryWorkerSample : ProbabilityTheory.IndepFun
      (fun path => (query path, worker path)) sample P :=
    indepFun_left_adjoin_fst_of_indepFun_pair P
      (workerLaw n) A.quantizer.law query worker sample
      hquery hworker hsample hqueryPair (by simpa [pairLaw] using hpairLaw)
  have hindep : ProbabilityTheory.IndepFun message sample P := by
    simpa [message] using
      hqueryWorkerSample.comp hmessageKernel measurable_id
  have hsampleLaw : Measure.map sample P = A.quantizer.law := by
    calc
      Measure.map sample P = Measure.map Prod.snd
          (Measure.map (fun path => (worker path, sample path)) P) := by
        simpa [Function.comp_apply] using
          (Measure.map_map measurable_snd (hworker.prodMk hsample) (μ := P)).symm
      _ = Measure.map Prod.snd pairLaw := by rw [hpairLaw]
      _ = A.quantizer.law := by simp [pairLaw]
  simpa [message, messageKernel, query, worker, sample, row, state, P] using
    adaptive_quantizerNonzeroCount_integrable_and_le_expectedDensity
      P hQ message sample hmessage hsample hindep hsampleLaw

/-- A measurable PP cost built from the generated strict-past state and the
non-coin part of the current round is independent of the refresh coin. -/
theorem pp_state_rest_kernel_indep_refresh
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal) (k : ℕ)
    (F : State d × ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) → ℝ)
    (hF : Measurable F) :
    ProbabilityTheory.IndepFun
      (fun path : ℕ → PPRoundNoise n r Ξ =>
        F (ppProcess (r := r) A x0 k path, (path k).2))
      (fun path : ℕ → PPRoundNoise n r Ξ => (path k).1)
      (ppPathLaw A) := by
  let P := ppPathLaw (r := r) A
  let state := fun path : ℕ → PPRoundNoise n r Ξ =>
    ppProcess (r := r) A x0 k path
  let current := fun path : ℕ → PPRoundNoise n r Ξ => path k
  let rest := fun z : PPRoundNoise n r Ξ => z.2
  let branchRound := fun z : PPRoundNoise n r Ξ => z.1
  let stateLaw := Measure.map state P
  let restLaw := (ppClientLaw n r).prod
    (ppCompressionLaw (r := r) A.quantizer)
  let roundLaw := ppRoundLaw (n := n) (r := r) A
  let joined := fun path : ℕ → PPRoundNoise n r Ξ =>
    (state path, rest (current path))
  let branch := fun path : ℕ → PPRoundNoise n r Ξ =>
    branchRound (current path)
  let Z := fun path : ℕ → PPRoundNoise n r Ξ => (state path, current path)
  let leftProd := fun z : State d × PPRoundNoise n r Ξ => (z.1, rest z.2)
  let rightProd := fun z : State d × PPRoundNoise n r Ξ => branchRound z.2
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure roundLaw := by
    dsimp [roundLaw]
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  haveI : IsProbabilityMeasure restLaw := by
    dsimp [restLaw]
    infer_instance
  have hstate : Measurable state := by
    have hs := ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth k
    have hle : (⨆ q : Fin k, MeasurableSpace.comap
        (fun path : ℕ → PPRoundNoise n r Ξ => path q.1) inferInstance) ≤
        (inferInstance : MeasurableSpace (ℕ → PPRoundNoise n r Ξ)) := by
      refine iSup_le fun q => ?_
      exact (measurable_pi_apply q.1).comap_le
    simpa [state] using hs.mono hle le_rfl
  haveI : IsProbabilityMeasure stateLaw :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hcurrent : Measurable current := measurable_pi_apply k
  have hstateCurrent : ProbabilityTheory.IndepFun state current P := by
    let pastPrefix := fun path : ℕ → PPRoundNoise n r Ξ =>
      fun q : Fin k => path q.1
    let prefixLaw := Measure.map pastPrefix P
    have hpastPrefix : Measurable pastPrefix := by
      dsimp [pastPrefix]
      exact measurable_pi_lambda _ fun q => measurable_pi_apply q.1
    haveI : IsProbabilityMeasure prefixLaw :=
      Measure.isProbabilityMeasure_map hpastPrefix.aemeasurable
    have hpastCurrent : ProbabilityTheory.IndepFun pastPrefix current P := by
      apply indepFun_of_map_prod_eq_prod_laws
        (P := P) (Z := fun path => (pastPrefix path, current path))
        (mu := prefixLaw) (nu := roundLaw)
        (hpastPrefix.prodMk hcurrent).aemeasurable
      simpa [pastPrefix, current, prefixLaw, roundLaw, P, ppPathLaw,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ => ppRoundLaw (n := n) (r := r) A) k)
    have hstrict : Measurable[MeasurableSpace.comap pastPrefix inferInstance]
        state := by
      have hs := ppProcess_strictPast_measurable (r := r) A x0 Llocal hSmooth k
      have hstrict_le : (⨆ q : Fin k, MeasurableSpace.comap
          (fun path : ℕ → PPRoundNoise n r Ξ => path q.1) inferInstance) ≤
          MeasurableSpace.comap pastPrefix inferInstance := by
        refine iSup_le fun q => ?_
        have hpast_comap :
            Measurable[MeasurableSpace.comap pastPrefix inferInstance]
              pastPrefix := measurable_iff_comap_le.mpr le_rfl
        exact ((measurable_pi_apply q).comp hpast_comap).comap_le
      simpa [state] using hs.mono hstrict_le le_rfl
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap pastPrefix inferInstance)
        (MeasurableSpace.comap current inferInstance) P := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hpastCurrent
    exact indepFun_of_measurable_left_of_indep_comap hstrict hcomap
  have hcurrentLaw : Measure.map current P = roundLaw := by
    simpa [current, P, roundLaw, ppPathLaw] using
      SOptLib.iidStreamLaw_map_eval (ppRoundLaw (n := n) (r := r) A) k
  have hZlaw : Measure.map Z P = stateLaw.prod roundLaw := by
    have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hstate.aemeasurable hcurrent.aemeasurable).1 hstateCurrent
    simpa [Z, stateLaw, hcurrentLaw] using hmap
  have hround : ProbabilityTheory.IndepFun rest branchRound roundLaw := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [roundLaw, ppRoundLaw, restLaw, rest, branchRound] using h
  have hprod : ProbabilityTheory.IndepFun leftProd rightProd
      (stateLaw.prod roundLaw) :=
    indepFun_prod_left_adjoin_of_indepFun stateLaw roundLaw rest branchRound
      measurable_snd measurable_fst hround
  have hleftProd : Measurable leftProd :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hrightProd : Measurable rightProd := measurable_fst.comp measurable_snd
  have hZ : Measurable Z := hstate.prodMk hcurrent
  have hjoinedBranch : ProbabilityTheory.IndepFun joined branch P := by
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hstate.prodMk (measurable_snd.comp hcurrent)).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    calc
      Measure.map (fun path => (joined path, branch path)) P =
          Measure.map (fun z => (leftProd z, rightProd z)) (Measure.map Z P) := by
        rw [Measure.map_map]
        · rfl
        · exact hleftProd.prodMk hrightProd
        · exact hZ
      _ = Measure.map (fun z => (leftProd z, rightProd z))
          (stateLaw.prod roundLaw) := by rw [hZlaw]
      _ = (Measure.map leftProd (stateLaw.prod roundLaw)).prod
          (Measure.map rightProd (stateLaw.prod roundLaw)) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleftProd.aemeasurable hrightProd.aemeasurable).1 hprod
      _ = (Measure.map joined P).prod (Measure.map branch P) := by
        rw [show Measure.map leftProd (stateLaw.prod roundLaw) =
            Measure.map joined P by
          calc
            _ = Measure.map leftProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map joined P := by
              rw [Measure.map_map]
              · rfl
              · exact hleftProd
              · exact hZ]
        rw [show Measure.map rightProd (stateLaw.prod roundLaw) =
            Measure.map branch P by
          calc
            _ = Measure.map rightProd (Measure.map Z P) := by rw [hZlaw]
            _ = Measure.map branch P := by
              rw [Measure.map_map]
              · rfl
              · exact hrightProd
              · exact hZ]
  simpa [joined, branch, state, current, rest, branchRound, P] using
    hjoinedBranch.comp hF measurable_id

set_option maxHeartbeats 4000000 in
/-- Full finite-horizon total PP-MARINA communication accounting.  The
non-refresh term sums over all indexed sampled-client occurrences, including
repetitions, and `expectedDensity` is used only as a supremum upper bound. -/
theorem ppTotalCommunicationCost_integrable_and_expectation_le
    {d n r : Count} {Ξ : Type*} [MeasurableSpace Ξ]
    (A : BasicData d n Ξ) (x0 : Point d) (Llocal : Worker n → ℝ)
    (hSmooth : IsLocallySmooth A.problem Llocal)
    {ω : ℝ} (hQ : IsUnbiasedQuantizer A.quantizer ω)
    (K : Count) :
    Integrable (ppTotalCommunicationCost (r := r) A x0 K) (ppPathLaw A) ∧
      (∫ path, ppTotalCommunicationCost (r := r) A x0 K path ∂ppPathLaw A) ≤
        ppCommunicationCount d n r K A.refreshProbability
          (expectedDensity A.quantizer) := by
  let law := ppPathLaw (r := r) A
  let supportKernel : State d ×
      ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) → ℝ := fun z =>
    ∑ j : Fin r.1, quantizerNonzeroCount A.quantizer
      (localGradientDifference A.problem (z.2.1 j)
        (primalStep A.stepSize z.1) z.1.x) (z.2.2 j)
  let support := fun k (path : ℕ → PPRoundNoise n r Ξ) =>
    supportKernel (ppProcess (r := r) A x0 k path, (path k).2)
  let branch := fun k (path : ℕ → PPRoundNoise n r Ξ) => (path k).1
  let term := fun k (path : ℕ → PPRoundNoise n r Ξ) =>
    if branch k path then (d.1 : ℝ) * n.1 else support k path
  letI : IsProbabilityMeasure (workerLaw n) := by
    unfold workerLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppClientLaw n r) := by
    unfold ppClientLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (ppCompressionLaw (r := r) A.quantizer) := by
    unfold ppCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure
      (refreshLaw A.refreshProbability A.refresh_admissible) := by
    unfold refreshLaw
    infer_instance
  haveI : IsProbabilityMeasure (ppRoundLaw (n := n) (r := r) A) := by
    unfold ppRoundLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    dsimp [law]
    unfold ppPathLaw SOptLib.iidStreamLaw
    infer_instance
  have hsupportKernel : Measurable supportKernel := by
    dsimp [supportKernel]
    apply Finset.measurable_sum
    intro j _
    have hxnext : Measurable (fun z : State d ×
        ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) =>
        primalStep A.stepSize z.1) :=
      (measurable_primalStep A.stepSize).comp measurable_fst
    have hx : Measurable (fun z : State d ×
        ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) => z.1.x) :=
      (measurable_state_x d).comp measurable_fst
    have hworker : Measurable (fun z : State d ×
        ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) => z.2.1 j) := by
      fun_prop
    have hsample : Measurable (fun z : State d ×
        ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) => z.2.2 j) := by
      fun_prop
    have hsel := pp_selected_localGradient_joint_measurable A.problem
    have hmessage : Measurable (fun z : State d ×
        ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) =>
        localGradientDifference A.problem (z.2.1 j)
          (primalStep A.stepSize z.1) z.1.x) :=
      (hsel.comp (hworker.prodMk hxnext)).sub (hsel.comp (hworker.prodMk hx))
    rw [show (fun z : State d ×
        ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) =>
        quantizerNonzeroCount A.quantizer
          (localGradientDifference A.problem (z.2.1 j)
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 j)) =
        fun z => ∑ q : Fin d.1,
          if A.quantizer.apply
              (localGradientDifference A.problem (z.2.1 j)
                (primalStep A.stepSize z.1) z.1.x) (z.2.2 j) q ≠ 0
          then (1 : ℝ) else 0 by
      funext z
      unfold quantizerNonzeroCount
      exact Finset.natCast_card_filter
        (fun q : Fin d.1 => A.quantizer.apply
          (localGradientDifference A.problem (z.2.1 j)
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 j) q ≠ 0) Finset.univ]
    apply Finset.measurable_sum
    intro q _
    have hq : Measurable (fun z : State d ×
        ((Fin r.1 → Worker n) × (Fin r.1 → Ξ)) =>
        A.quantizer.apply
          (localGradientDifference A.problem (z.2.1 j)
            (primalStep A.stepSize z.1) z.1.x) (z.2.2 j) q) :=
      (EuclideanSpace.proj q).continuous.measurable.comp
        (A.quantizer.measurable_apply_uncurry.comp (hmessage.prodMk hsample))
    exact Measurable.ite
      (hq (measurableSet_singleton 0)).compl measurable_const measurable_const
  have hsupport (k : ℕ) : Integrable (support k) law ∧
      (∫ path, support k path ∂law) ≤
        (r.1 : ℝ) * expectedDensity A.quantizer := by
    have hone (j : Fin r.1) :=
      ppOccurrenceRoundSupport_integrable_and_le_expectedDensity
        (r := r) A x0 Llocal hSmooth hQ k j
    have hint : ∀ j : Fin r.1, Integrable
        (fun path : ℕ → PPRoundNoise n r Ξ =>
          quantizerNonzeroCount A.quantizer
            (localGradientDifference A.problem ((path k).2.1 j)
              (primalStep A.stepSize (ppProcess (r := r) A x0 k path))
              (ppProcess (r := r) A x0 k path).x) ((path k).2.2 j)) law :=
      fun j => by simpa [law] using (hone j).1
    have hsumInt := MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _ => hint j)
    constructor
    · simpa [support, supportKernel] using hsumInt
    · change (∫ path, ∑ j : Fin r.1, quantizerNonzeroCount A.quantizer
          (localGradientDifference A.problem ((path k).2.1 j)
            (primalStep A.stepSize (ppProcess (r := r) A x0 k path))
            (ppProcess (r := r) A x0 k path).x) ((path k).2.2 j) ∂law) ≤ _
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun j _ => hint j)]
      calc
        ∑ j : Fin r.1, ∫ path, quantizerNonzeroCount A.quantizer
            (localGradientDifference A.problem ((path k).2.1 j)
              (primalStep A.stepSize (ppProcess (r := r) A x0 k path))
              (ppProcess (r := r) A x0 k path).x) ((path k).2.2 j) ∂law ≤
            ∑ _j : Fin r.1, expectedDensity A.quantizer := by
          gcongr with j
          simpa [law] using (hone j).2
        _ = (r.1 : ℝ) * expectedDensity A.quantizer := by simp
  have hbranchMeas (k : ℕ) : Measurable (branch k) := by
    dsimp [branch]
    fun_prop
  have hbranchLaw (k : ℕ) : Measure.map (branch k) law =
      refreshLaw A.refreshProbability A.refresh_admissible := by
    simpa [branch, law] using ppPathLaw_refresh_marginal (r := r) A k
  have hindep (k : ℕ) :
      ProbabilityTheory.IndepFun (support k) (branch k) law := by
    have h := pp_state_rest_kernel_indep_refresh
      (r := r) A x0 Llocal hSmooth k supportKernel hsupportKernel
    simpa only [support, branch, law] using h
  have htermInt (k : ℕ) : Integrable (term k) law := by
    have hs : MeasurableSet {path | branch k path = true} :=
      hbranchMeas k (measurableSet_singleton true)
    have hpiece := Integrable.piecewise hs
      (integrable_const (c := (d.1 : ℝ) * n.1)).integrableOn
      (hsupport k).1.integrableOn
    simpa [term, Set.piecewise] using hpiece
  have htermBound (k : ℕ) : (∫ path, term k path ∂law) ≤
      A.refreshProbability * d.1 * n.1 +
        (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1 := by
    let refreshGate := fun path : ℕ → PPRoundNoise n r Ξ =>
      if branch k path = true then (d.1 : ℝ) * n.1 else 0
    let differenceGate := fun path : ℕ → PPRoundNoise n r Ξ =>
      if branch k path = false then support k path else 0
    have hrefreshInt : Integrable refreshGate law := by
      have hs : MeasurableSet {path | branch k path = true} :=
        hbranchMeas k (measurableSet_singleton true)
      have hpiece := Integrable.piecewise hs
        (integrable_const (μ := law) (c := (d.1 : ℝ) * n.1)).integrableOn
        (integrable_const (μ := law) (c := (0 : ℝ))).integrableOn
      simpa [refreshGate, Set.piecewise] using hpiece
    have hdifferenceInt : Integrable differenceGate law := by
      have hs : MeasurableSet {path | branch k path = false} :=
        hbranchMeas k (measurableSet_singleton false)
      have hpiece := Integrable.piecewise hs (hsupport k).1.integrableOn
        (integrable_const (c := (0 : ℝ))).integrableOn
      simpa [differenceGate, Set.piecewise] using hpiece
    have hrefreshExpectation : (∫ path, refreshGate path ∂law) =
        A.refreshProbability * d.1 * n.1 := by
      calc
        (∫ path, refreshGate path ∂law) =
            ∫ c : Bool, (if c then (d.1 : ℝ) * n.1 else 0)
              ∂Measure.map (branch k) law := by
          symm
          exact MeasureTheory.integral_map (hbranchMeas k).aemeasurable (by fun_prop)
        _ = ∫ c : Bool, (if c then (d.1 : ℝ) * n.1 else 0)
            ∂refreshLaw A.refreshProbability A.refresh_admissible := by
          rw [hbranchLaw k]
        _ = A.refreshProbability * d.1 * n.1 := by
          rw [integral_refreshLaw_if A.refreshProbability A.refresh_admissible
            ((d.1 : ℝ) * n.1) 0]
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
      _ ≤ A.refreshProbability * d.1 * n.1 +
          (1 - A.refreshProbability) * ∫ path, support k path ∂law := by
        rw [hrefreshExpectation]
        gcongr
      _ ≤ A.refreshProbability * d.1 * n.1 +
          (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1 := by
        have hpnonneg : 0 ≤ 1 - A.refreshProbability :=
          sub_nonneg.mpr A.refresh_admissible.2
        calc
          _ ≤ A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) *
                ((r.1 : ℝ) * expectedDensity A.quantizer) := by
            gcongr
            exact (hsupport k).2
          _ = _ := by ring
  have hsumInt : Integrable
      (fun path => ∑ k ∈ Finset.range K.1, term k path) law :=
    MeasureTheory.integrable_finset_sum _ fun k _ => htermInt k
  have htotalInt : Integrable
      (fun path => (d.1 : ℝ) * n.1 +
        ∑ k ∈ Finset.range K.1, term k path) law :=
    (integrable_const ((d.1 : ℝ) * n.1)).add hsumInt
  constructor
  · change Integrable (fun path => (d.1 : ℝ) * n.1 +
        ∑ k ∈ Finset.range K.1, term k path) law
    exact htotalInt
  · change (∫ path, (d.1 : ℝ) * n.1 +
        ∑ k ∈ Finset.range K.1, term k path ∂law) ≤ _
    rw [MeasureTheory.integral_add
      (integrable_const ((d.1 : ℝ) * n.1)) hsumInt,
      MeasureTheory.integral_finset_sum (Finset.range K.1)
        (fun k _ => htermInt k)]
    simp only [MeasureTheory.integral_const, probReal_univ, one_smul]
    unfold ppCommunicationCount
    calc
      (d.1 : ℝ) * n.1 + ∑ k ∈ Finset.range K.1, ∫ path, term k path ∂law ≤
          (d.1 : ℝ) * n.1 + ∑ _k ∈ Finset.range K.1,
            (A.refreshProbability * d.1 * n.1 +
              (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1) := by
        gcongr with k hk
        exact htermBound k
      _ = (d.1 : ℝ) * n.1 + K.1 *
          (A.refreshProbability * d.1 * n.1 +
            (1 - A.refreshProbability) * expectedDensity A.quantizer * r.1) := by
        simp
        ring

/-- The executable Algorithm 3 initializer is measurable when the stochastic
gradient has the explicit joint kernel realization needed for arbitrary sample
spaces. -/
theorem onlineInitialState_measurable_of_kernel
    {d n b : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem) (x0 : Point d) :
    Measurable (fun z : (i : Worker n) → Fin b.1 → Sample i =>
      onlineInitialState A { sample := z } x0) := by
  classical
  have hterm (i : Worker n) (j : Fin b.1) : Measurable
      (fun z : (w : Worker n) → Fin b.1 → Sample w =>
        stochasticGradient A.problem i (z i j) x0) := by
    have hsample : Measurable
        (fun z : (w : Worker n) → Fin b.1 → Sample w => z i j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact (hKernel i).comp (measurable_const.prodMk hsample)
  have hworker (i : Worker n) : Measurable
      (fun z : (w : Worker n) → Fin b.1 → Sample w =>
        average (fun j : Fin b.1 => stochasticGradient A.problem i (z i j) x0)) := by
    unfold average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ (fun j _ => hterm i j)).const_smul
      ((Fintype.card (Fin b.1) : ℝ)⁻¹)
  have hg : Measurable
      (fun z : (w : Worker n) → Fin b.1 → Sample w =>
        onlinePrintedInitialEstimatorAt A { sample := z } x0) := by
    unfold onlinePrintedInitialEstimatorAt average SOptLib.finiteUniformAverage
    exact (Finset.measurable_sum Finset.univ (fun i _ => hworker i)).const_smul
      ((Fintype.card (Worker n) : ℝ)⁻¹)
  simpa [onlineInitialState] using
    (measurable_state_mk d).comp (measurable_const.prodMk hg)

/-- Every executable Algorithm 3 state is a measurable function on the full
initial-minibatch/product-stream experiment under the minimal kernel
realization premise. -/
theorem onlineProcess_measurable_of_kernel
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (hKernel : OnlineGradientKernelRealization A.problem)
    (x0 : Point d) (hBatch : OnlineBatchAdmissible b b0) :
    ∀ k, Measurable (onlineProcess A x0 hBatch k) := by
  intro k
  induction k with
  | zero =>
      change Measurable (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
        (ℕ → OnlineRoundNoise n b b0 Sample Ξ) =>
          onlineInitialState A { sample := path.1 } x0)
      exact (onlineInitialState_measurable_of_kernel
        (b := b) A hKernel x0).comp measurable_fst
  | succ k ih =>
      have hcurrent : Measurable
          (fun path : ((i : Worker n) → Fin b.1 → Sample i) ×
              (ℕ → OnlineRoundNoise n b b0 Sample Ξ) => path.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      have hstep := (onlineStep_round_joint_measurable_of_kernel
        (b := b) (b0 := b0) A hKernel).comp (ih.prodMk hcurrent)
      simpa [Nat.succ_eq_add_one, onlineProcess_succ] using hstep

/-- The generated-cost measurability needed to account for executable
Algorithm 3 communication.  Unlike `OnlineGradientKernelRealization`, this
asks only for the generated states and the actual `b0` difference-message
kernel used by the cost random variable; it imposes no regularity on unrelated
stochastic-gradient query/sample pairs. -/
structure OnlineCostMeasurability
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) : Prop where
  process : ∀ k, Measurable (onlineProcess A x0 hBatch k)
  difference : ∀ i : Worker n,
    Measurable (fun p : (Point d × Point d) ×
        ((w : Worker n) → Fin b0.1 → Sample w) =>
      onlineBatchDifference A.problem p.2 i p.1.1 p.1.2)

/-- The actual non-refresh message used by executable Algorithm 3 at round
`k`.  Naming this observable lets the source-facing regularity contract avoid
quantifying over difference kernels at query/batch inputs that the generated
algorithm never visits. -/
noncomputable def onlineWorkerDifferenceMessage
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ) (i : Worker n)
    (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) : Point d :=
  let s := onlineProcess A x0 hBatch k path
  onlineBatchDifference A.problem (path.2 k).2.1.2 i
    (primalStep A.stepSize s) s.x

/-- The fresh compressor sample paired with a worker's actual online
difference message. -/
def onlineWorkerCompressionSample
    {n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    (k : ℕ) (i : Worker n)
    (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) : Ξ :=
  (path.2 k).2.2 i

/-- The canonical refresh coin governing the same online round. -/
def onlineRefreshBranch
    {n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    (k : ℕ)
    (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) : Bool :=
  (path.2 k).1

/-- The support of the actual compressed difference message at one online
round. -/
noncomputable def onlineWorkerRoundSupport
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ) (i : Worker n)
    (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) : ℝ :=
  quantizerNonzeroCount A.quantizer
    (onlineWorkerDifferenceMessage A x0 hBatch k i path)
    (onlineWorkerCompressionSample k i path)

/-- Exact law-scoped regularity needed for executable Algorithm 3
communication accounting.  It mentions only generated messages and fresh
canonical coordinates.  In particular, it neither postulates a support
expectation nor requires a globally measurable stochastic-gradient kernel. -/
structure OnlineCommunicationLawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) : Prop where
  message_measurable : ∀ k (i : Worker n),
    Measurable (onlineWorkerDifferenceMessage A x0 hBatch k i)
  message_indep_compression : ∀ k (i : Worker n),
    ProbabilityTheory.IndepFun
      (onlineWorkerDifferenceMessage A x0 hBatch k i)
      (onlineWorkerCompressionSample k i) (onlinePathLaw A)
  support_indep_refresh : ∀ k (i : Worker n),
    ProbabilityTheory.IndepFun
      (onlineWorkerRoundSupport A x0 hBatch k i)
      (onlineRefreshBranch k) (onlinePathLaw A)

/-- Law-scoped replacement for the pointwise-measurability component of
`OnlineCommunicationLawRegularity`.  The actual Algorithm 3 message is only
required to be a.e. strongly measurable under its canonical path law.  The
independence statements use its canonical measurable representative; they do
not postulate an expectation, a density bound, or a cost conclusion. -/
structure OnlineCommunicationAELawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) : Prop where
  message_aestronglyMeasurable : ∀ k (i : Worker n),
    AEStronglyMeasurable (onlineWorkerDifferenceMessage A x0 hBatch k i)
      (onlinePathLaw A)
  messageRepresentative_indep_compression : ∀ k (i : Worker n),
    ProbabilityTheory.IndepFun
      ((message_aestronglyMeasurable k i).mk
        (onlineWorkerDifferenceMessage A x0 hBatch k i))
      (onlineWorkerCompressionSample k i) (onlinePathLaw A)
  supportRepresentative_indep_refresh : ∀ k (i : Worker n),
    ProbabilityTheory.IndepFun
      (fun path => quantizerNonzeroCount A.quantizer
        ((message_aestronglyMeasurable k i).mk
          (onlineWorkerDifferenceMessage A x0 hBatch k i) path)
        (onlineWorkerCompressionSample k i path))
      (onlineRefreshBranch k) (onlinePathLaw A)

/-- The actual homogeneous difference message is the constant-batch
specialization of the heterogeneous message, on the identified executable
process. -/
theorem onlineWorkerDifferenceMessage_eq_heterogeneous_const
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0) (k : ℕ) (i : Worker n)
    (path : ((w : Worker n) → Fin b.1 → Sample w) ×
      (ℕ → OnlineRoundNoise n b b0 Sample Ξ)) :
    onlineWorkerDifferenceMessage A x0 hBatch k i path =
      heterogeneousOnlineWorkerDifferenceMessage
        (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0)
        A x0 k i path := by
  unfold onlineWorkerDifferenceMessage
    heterogeneousOnlineWorkerDifferenceMessage
  rw [onlineProcess_eq_heterogeneousOnlineProcess_const
    A x0 hBatch k path]
  rfl

/-- Homogeneous actual-message communication regularity is inherited from
the constant-worker-batch instance of the heterogeneous executable
experiment.  Thus literal Assumption 3.3 and the weak law-level correction
are sufficient; the older global differentiability route is not needed for
the generated communication observable. -/
theorem onlineCommunicationAELawRegularity_of_literal_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (sigma : Worker n → ℝ)
    (hLiteral : OnlineAssumption33Literal A.problem sigma)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem) :
    OnlineCommunicationAELawRegularity A x0 hBatch := by
  let hHet :=
    heterogeneousOnlineCommunicationAELawRegularity_of_literal_and_lawRegularity
      (b := fun _ : Worker n ↦ b) (b0 := fun _ : Worker n ↦ b0)
      A x0 sigma hLiteral hRegularity
  let hm : ∀ k (i : Worker n),
      AEStronglyMeasurable (onlineWorkerDifferenceMessage A x0 hBatch k i)
        (onlinePathLaw A) := by
    intro k i
    have hmeas := hHet.message_aestronglyMeasurable k i
    exact hmeas.congr (Filter.Eventually.of_forall fun path ↦
      (onlineWorkerDifferenceMessage_eq_heterogeneous_const
        A x0 hBatch k i path).symm)
  refine ⟨hm, ?_, ?_⟩
  · intro k i
    have hIndep := hHet.messageRepresentative_indep_compression k i
    apply hIndep.congr
    · filter_upwards
        [(hHet.message_aestronglyMeasurable k i).ae_eq_mk,
          (hm k i).ae_eq_mk] with path hHetMk hOnlineMk
      rw [← hHetMk, ← hOnlineMk,
        onlineWorkerDifferenceMessage_eq_heterogeneous_const
          A x0 hBatch k i path]
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  · intro k i
    have hIndep := hHet.supportRepresentative_indep_refresh k i
    apply hIndep.congr
    · filter_upwards
        [(hHet.message_aestronglyMeasurable k i).ae_eq_mk,
          (hm k i).ae_eq_mk] with path hHetMk hOnlineMk
      rw [← hHetMk, ← hOnlineMk,
        onlineWorkerDifferenceMessage_eq_heterogeneous_const
          A x0 hBatch k i path]
      rfl
    · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The former strict generated-law interface remains a compatibility
interface and canonically supplies the new a.e.-law interface. -/
theorem onlineCommunicationAELawRegularity_of_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (hBatch : OnlineBatchAdmissible b b0)
    (h : OnlineCommunicationLawRegularity A x0 hBatch) :
    OnlineCommunicationAELawRegularity A x0 hBatch := by
  refine ⟨fun k i => (h.message_measurable k i).aestronglyMeasurable, ?_, ?_⟩
  · intro k i
    let hm : AEStronglyMeasurable
        (onlineWorkerDifferenceMessage A x0 hBatch k i) (onlinePathLaw A) :=
      (h.message_measurable k i).aestronglyMeasurable
    apply (h.message_indep_compression k i).congr
    · exact hm.ae_eq_mk
    · exact Filter.Eventually.of_forall fun _ => rfl
  · intro k i
    let hm : AEStronglyMeasurable
        (onlineWorkerDifferenceMessage A x0 hBatch k i) (onlinePathLaw A) :=
      (h.message_measurable k i).aestronglyMeasurable
    apply (h.support_indep_refresh k i).congr
    · filter_upwards [hm.ae_eq_mk] with path hp
      simp only [onlineWorkerRoundSupport]
      rw [hp]
    · exact Filter.Eventually.of_forall fun _ => rfl

/-- Under the source sampled-loss assumptions, a worker's finite-difference
minibatch is a random vector for an arbitrary a.e.-measurable random query.
This is deliberately a product-law statement: it supplies only the
law-scoped representative needed below and does not assert a globally
measurable stochastic-gradient kernel. -/
theorem onlineBatchDifference_product_aestronglyMeasurable_of_variance
    {d n b0 : Count} {Sample : Worker n → Type*} {Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Q]
    (A : OnlineProblem d n Sample) (σ : Worker n → ℝ)
    (hVariance : OnlineUnbiasedBoundedVariance A σ)
    (mu : Measure Q) [SFinite mu]
    (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        onlineBatchDifference A p.2 i (xNext p.1) (x p.1))
      (mu.prod (onlineBatchLaw A b0)) := by
  classical
  let batchLaw := onlineBatchLaw A b0
  letI (w : Worker n) : IsProbabilityMeasure (A.sampleLaw w) :=
    A.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  have hcoord (j : Fin b0.1) :
      Measure.map
          (fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j)
          batchLaw = A.sampleLaw i :=
    onlineBatchLaw_coordinate_marginal A i j
  have hsampleDiff (j : Fin b0.1) :
      ∀ᵐ batch ∂batchLaw, Differentiable ℝ (A.sampleLoss i (batch i j)) := by
    let coord := fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j
    have hqmp : Measure.QuasiMeasurePreserving coord batchLaw (A.sampleLaw i) :=
      ⟨(by dsimp [coord]; fun_prop), by
        rw [show Measure.map coord batchLaw = A.sampleLaw i by
          simpa [coord] using hcoord j]⟩
    exact hqmp.tendsto_ae (hVariance.2 i)
  have hsampleInt (j : Fin b0.1) (y : Point d) :
      Integrable
        (fun batch : (w : Worker n) → Fin b0.1 → Sample w =>
          A.sampleLoss i (batch i j) y) batchLaw := by
    let coord := fun batch : (w : Worker n) → Fin b0.1 → Sample w => batch i j
    have hm : Integrable (fun xi => A.sampleLoss i xi y)
        (Measure.map coord batchLaw) := by
      rw [show Measure.map coord batchLaw = A.sampleLaw i by
        simpa [coord] using hcoord j]
      exact A.sampleLoss_integrable i y
    exact (MeasureTheory.integrable_map_measure hm.aestronglyMeasurable
      (by
        dsimp [coord]
        exact ((measurable_pi_apply j).comp
          (measurable_pi_apply i)).aemeasurable)).mp hm
  have hnext (j : Fin b0.1) : AEStronglyMeasurable
      (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        stochasticGradient A i (p.2 i j) (xNext p.1))
      (mu.prod batchLaw) :=
    stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A i mu batchLaw xNext (fun batch => batch i j) hxNext
        (hsampleDiff j) (hsampleInt j)
  have hcurrent (j : Fin b0.1) : AEStronglyMeasurable
      (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        stochasticGradient A i (p.2 i j) (x p.1))
      (mu.prod batchLaw) :=
    stochasticGradient_randomQuery_product_aestronglyMeasurable_of_differentiable
      A i mu batchLaw x (fun batch => batch i j) hx
        (hsampleDiff j) (hsampleInt j)
  unfold onlineBatchDifference average SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun j _ => (hnext j).sub (hcurrent j))).const_smul
      ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [Finset.sum_apply, Finset.sum_sub_distrib]

/-- Homogeneous difference-minibatch counterpart of the weaker law-level
route.  Fixed-query moments remain a separate premise of recurrence theorems;
they are not needed merely to construct this adaptive random vector. -/
theorem onlineBatchDifference_product_aestronglyMeasurable_of_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Q]
    (A : OnlineProblem d n Sample)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A)
    (mu : Measure Q) [SFinite mu]
    (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) (i : Worker n) :
    AEStronglyMeasurable
      (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        onlineBatchDifference A p.2 i (xNext p.1) (x p.1))
      (mu.prod (onlineBatchLaw A b0)) := by
  classical
  let batchLaw := onlineBatchLaw A b0
  letI (w : Worker n) : IsProbabilityMeasure (A.sampleLaw w) :=
    A.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    unfold batchLaw onlineBatchLaw
    infer_instance
  have hcoord (j : Fin b0.1) :
      Measure.map
          (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i j)
          batchLaw = A.sampleLaw i :=
    onlineBatchLaw_coordinate_marginal A i j
  have hnext (j : Fin b0.1) : AEStronglyMeasurable
      (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        stochasticGradient A i (p.2 i j) (xNext p.1))
      (mu.prod batchLaw) :=
    (stochasticGradient_randomQuery_product_regular_of_lawRegularity
      A hRegularity i mu batchLaw xNext (fun batch ↦ batch i j) hxNext
        ((measurable_pi_apply j).comp (measurable_pi_apply i))
        (hcoord j)).2
  have hcurrent (j : Fin b0.1) : AEStronglyMeasurable
      (fun p : Q × ((w : Worker n) → Fin b0.1 → Sample w) ↦
        stochasticGradient A i (p.2 i j) (x p.1))
      (mu.prod batchLaw) :=
    (stochasticGradient_randomQuery_product_regular_of_lawRegularity
      A hRegularity i mu batchLaw x (fun batch ↦ batch i j) hx
        ((measurable_pi_apply j).comp (measurable_pi_apply i))
        (hcoord j)).2
  unfold onlineBatchDifference average SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun j _ ↦ (hnext j).sub (hcurrent j))).const_smul
      ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [Finset.sum_apply, Finset.sum_sub_distrib]

/-- The complete homogeneous nonrefresh innovation is a random vector under
an arbitrary query law paired with the canonical fresh difference-minibatch
and compressor law.  This is the law-level replacement for the older product
regularity lemma that obtained the same fact from global sampled-loss
differentiability. -/
theorem onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ Q : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    [MeasurableSpace Q]
    (A : OnlineData d n Sample Ξ)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (mu : Measure Q) [SFinite mu] (xNext x : Q → Point d)
    (hxNext : AEStronglyMeasurable xNext mu)
    (hx : AEStronglyMeasurable x mu) :
    AEStronglyMeasurable
      (fun p : Q ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
        average (fun i : Worker n ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem p.2.1 i
                (xNext p.1) (x p.1))
              (p.2.2 i) -
            localGradientDifference (onlineLocalProblem A.problem) i
              (xNext p.1) (x p.1)))
      (mu.prod (onlineDifferenceCompressionLaw (b0 := b0) A)) := by
  classical
  let nu := onlineDifferenceCompressionLaw (b0 := b0) A
  let P := onlineLocalProblem A.problem
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure nu := by
    unfold nu onlineDifferenceCompressionLaw
    infer_instance
  have hcoord (i : Worker n) (j : Fin b0.1) :
      Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
            (Worker n → Ξ) ↦ q.1 i j) nu = A.problem.sampleLaw i := by
    calc
      Measure.map
          (fun q : ((w : Worker n) → Fin b0.1 → Sample w) ×
            (Worker n → Ξ) ↦ q.1 i j) nu =
          Measure.map
            (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i j)
            (Measure.map Prod.fst nu) := by
              rw [MeasureTheory.Measure.map_map]
              · rfl
              · fun_prop
              · exact measurable_fst
      _ = Measure.map
            (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i j)
            (onlineBatchLaw A.problem b0) := by
              rw [show Measure.map Prod.fst nu = onlineBatchLaw A.problem b0 by
                unfold nu onlineDifferenceCompressionLaw
                rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]]
      _ = _ := onlineBatchLaw_coordinate_marginal A.problem i j
  have hworker (i : Worker n) : AEStronglyMeasurable
      (fun p : Q ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem p.2.1 i
              (xNext p.1) (x p.1))
            (p.2.2 i) -
          localGradientDifference P i (xNext p.1) (x p.1))
      (mu.prod nu) := by
    have hD : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
          onlineBatchDifference A.problem p.2.1 i
            (xNext p.1) (x p.1)) (mu.prod nu) := by
      have hnext (j : Fin b0.1) : AEStronglyMeasurable
          (fun p : Q ×
              (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
            stochasticGradient A.problem i (p.2.1 i j) (xNext p.1))
          (mu.prod nu) :=
        (stochasticGradient_randomQuery_product_regular_of_lawRegularity
          A.problem hRegularity i mu nu xNext (fun q ↦ q.1 i j) hxNext
            (by fun_prop) (hcoord i j)).2
      have hcurrent (j : Fin b0.1) : AEStronglyMeasurable
          (fun p : Q ×
              (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
            stochasticGradient A.problem i (p.2.1 i j) (x p.1))
          (mu.prod nu) :=
        (stochasticGradient_randomQuery_product_regular_of_lawRegularity
          A.problem hRegularity i mu nu x (fun q ↦ q.1 i j) hx
            (by fun_prop) (hcoord i j)).2
      unfold onlineBatchDifference average SOptLib.finiteUniformAverage
      have hs := (Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ ↦ (hnext j).sub (hcurrent j))).const_smul
          ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
      refine hs.congr (Filter.Eventually.of_forall ?_)
      intro p
      simp [Finset.sum_apply, Finset.sum_sub_distrib]
    have hquantized : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
          A.quantizer.apply
            (onlineBatchDifference A.problem p.2.1 i
              (xNext p.1) (x p.1))
            (p.2.2 i)) (mu.prod nu) :=
      (A.quantizer.measurable_apply_uncurry.comp_aemeasurable
        (hD.aemeasurable.prodMk
          ((measurable_pi_apply i).comp
            (measurable_snd.comp measurable_snd)).aemeasurable)).aestronglyMeasurable
    have hdelta : AEStronglyMeasurable
        (fun p : Q ×
            (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
          localGradientDifference P i (xNext p.1) (x p.1)) (mu.prod nu) := by
      unfold localGradientDifference
      exact (((measurable_localGradient P i).comp_aemeasurable
        hxNext.aemeasurable).aestronglyMeasurable.comp_fst).sub
        (((measurable_localGradient P i).comp_aemeasurable
          hx.aemeasurable).aestronglyMeasurable.comp_fst)
    exact hquantized.sub hdelta
  unfold average SOptLib.finiteUniformAverage
  have hs := (Finset.aestronglyMeasurable_sum Finset.univ
    (fun i _ ↦ hworker i)).const_smul ((Fintype.card (Worker n) : ℝ)⁻¹)
  refine hs.congr (Filter.Eventually.of_forall ?_)
  intro p
  simp [P, Finset.sum_apply]

/-- Homogeneous refresh minibatch regularity under the same weak Track-B
correction.  This is the exact adaptive refresh random vector consumed by the
proof-exact and executable Eq. (46) recurrences. -/
theorem onlineRefreshAverage_product_aestronglyMeasurable_of_lawRegularity
    {d n b : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (A : OnlineProblem d n Sample)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A)
    (mu : Measure (Point d)) [SFinite mu] :
    AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) ↦
        average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
          stochasticGradient A i (p.2 i j) p.1)))
      (mu.prod (onlineBatchLaw A b)) := by
  simpa [heterogeneousOnlineBatchLaw, onlineBatchLaw] using
    (heterogeneousOnlineRefreshAverage_product_aestronglyMeasurable_of_lawRegularity
      (b := fun _ : Worker n ↦ b) A hRegularity mu)

/-- Squared locally centered homogeneous refresh error under the weak
law-level correction.  Its measured object is definitionally the refresh
error appearing in Eq. (46). -/
theorem onlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
    {d n b : Count} {Sample : Worker n → Type*}
    [∀ i, MeasurableSpace (Sample i)]
    (A : OnlineProblem d n Sample)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A)
    (mu : Measure (Point d)) [SFinite mu] :
    AEStronglyMeasurable
      (fun p : Point d × ((i : Worker n) → Fin b.1 → Sample i) ↦
        ‖average (fun i : Worker n ↦ average (fun j : Fin b.1 ↦
            stochasticGradient A i (p.2 i j) p.1)) -
          globalGradient (onlineLocalProblem A) p.1‖ ^ 2)
      (mu.prod (onlineBatchLaw A b)) := by
  simpa [heterogeneousOnlineBatchLaw, onlineBatchLaw] using
    (heterogeneousOnlineRefreshErrorSq_product_aestronglyMeasurable_of_lawRegularity
      (b := fun _ : Worker n ↦ b) A hRegularity mu)

/-! ## Literal Assumption 3.2 nonrefresh moments

The fixed-query covariance calculation itself does not consume Assumption
3.3.  Its only stochastic-gradient input is the conditional minibatch moment
stated by Assumption 3.2; measurability and integrability of that minibatch
are already fields of the assumption.  The older worker lemma was phrased
through the compatibility `OnlineExpectationRealization` carrier, which is
intrinsic data of every `OnlineProblem`.  The next two declarations expose
the same calculation at the literal source boundary and then specialize it
to the genuine-gradient formulation of Assumption 3.2. -/

/-- Fixed-query worker innovation moment from one Assumption 3.2 fiber.  No
sample-loss differentiability, adaptive-law regularity, or Assumption 3.3
moment is used. -/
theorem onlineFixed_nonrefresh_worker_moment_of_assumption32
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (xNext x : Point d) (i : Worker n) (Llocal ℒlocal : Worker n → ℝ)
    (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAverageFiber :
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let D := fun batch ↦ onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch ↦ ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let delta := localGradientDifference
      (onlineLocalProblem A.problem) i xNext x
    let innovation := fun q :
        ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta
    Integrable innovation
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      Integrable (fun q ↦ ‖innovation q‖ ^ 2)
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      (∫ q, innovation q
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  let hE := onlineExpectationRealization A.problem
  simpa [onlineLocalProblemCorrected_eq_onlineLocalProblem] using
    (online_corrected_fixed_nonrefresh_worker_moment
      (b0 := b0) A hE xNext x i Llocal ℒlocal ω hSmooth
        hAverageFiber hQuantizer)

/-- The genuine-gradient Assumption 3.2 statement supplies the exact
workerwise centered innovation used by the generated nonrefresh branch.  The
only transfer is the proved a.e. identification of each genuine minibatch
difference with `onlineBatchDifference`. -/
theorem onlineFixed_nonrefresh_worker_moment_of_genuine_assumption32
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*} {Ξ : Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (run : ℕ → Ω → State d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0)
      A.problem run ℒlocal)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (i : Worker n) (path : Ω) :
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    let delta := localGradientDifference
      (onlineLocalProblem A.problem) i xNext x
    let innovation := fun q :
        ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta
    Integrable innovation
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      Integrable (fun q ↦ ‖innovation q‖ ^ 2)
        ((onlineBatchLaw A.problem b0).prod A.quantizer.law) ∧
      (∫ q, innovation q
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2
          ∂(onlineBatchLaw A.problem b0).prod A.quantizer.law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  dsimp only
  have hAverage : OnlineAverageSmoothness (b0 := b0)
      A.problem run ℒlocal :=
    onlineAssumption32Genuine_to_onlineAverageSmoothness hAssumption32
  exact onlineFixed_nonrefresh_worker_moment_of_assumption32
    A (run (k + 1) path).x (run k path).x i Llocal ℒlocal ω
      hSmooth (hAverage.2 k i path) hQuantizer

set_option maxHeartbeats 2000000 in
/-- Row-law form of the literal Assumption 3.2 worker moment.  The moment
calculation above is stated on the complete homogeneous minibatch because
that is the source-facing Assumption 3.2 object.  Independent-worker
aggregation additionally needs a representative measurable with respect to
the worker's own row.  The weak Track-B correction supplies exactly that
row-law measurability, while all centering and bounds are transported from
the Assumption 3.2 calculation. -/
theorem onlineFixed_nonrefresh_worker_row_moment_of_assumption32
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (xNext x : Point d) (i : Worker n) (Llocal ℒlocal : Worker n → ℝ)
    (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAverageFiber :
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let D := fun batch ↦ onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch ↦ ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let rowBatchLaw :=
      Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)
    let rowLaw := rowBatchLaw.prod A.quantizer.law
    let delta := localGradientDifference
      (onlineLocalProblem A.problem) i xNext x
    let innovation := fun q : (Fin b0.1 → Sample i) × Ξ ↦
      A.quantizer.apply
          (average (fun j : Fin b0.1 ↦
            stochasticGradient A.problem i (q.1 j) xNext -
              stochasticGradient A.problem i (q.1 j) x)) q.2 - delta
    Integrable innovation rowLaw ∧
      Integrable (fun q ↦ ‖innovation q‖ ^ 2) rowLaw ∧
      (∫ q, innovation q ∂rowLaw) = 0 ∧
      (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  classical
  let batchLaw := onlineBatchLaw A.problem b0
  let rowBatchLaw :=
    Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)
  let fullLaw := batchLaw.prod A.quantizer.law
  let rowLaw := rowBatchLaw.prod A.quantizer.law
  let delta := localGradientDifference
    (onlineLocalProblem A.problem) i xNext x
  let localD := fun row : Fin b0.1 → Sample i ↦
    average (fun j : Fin b0.1 ↦
      stochasticGradient A.problem i (row j) xNext -
        stochasticGradient A.problem i (row j) x)
  let innovation := fun q : (Fin b0.1 → Sample i) × Ξ ↦
    A.quantizer.apply (localD q.1) q.2 - delta
  let project := fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
    (q.1 i, q.2)
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure batchLaw := by
    dsimp [batchLaw]
    unfold onlineBatchLaw
    infer_instance
  haveI : IsProbabilityMeasure rowBatchLaw := by
    dsimp [rowBatchLaw]
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure fullLaw := by
    dsimp [fullLaw]
    infer_instance
  haveI : IsProbabilityMeasure rowLaw := by
    dsimp [rowLaw]
    infer_instance
  have hproject : Measurable project := by
    dsimp [project]
    fun_prop
  have hmap : Measure.map project fullLaw = rowLaw := by
    change Measure.map project fullLaw = rowLaw
    rw [show project = Prod.map
        (fun batch : (w : Worker n) → Fin b0.1 → Sample w ↦ batch i) id by
      funext q
      rfl]
    dsimp [fullLaw, rowLaw]
    rw [← Measure.map_prod_map batchLaw A.quantizer.law
      (measurable_pi_apply i) measurable_id]
    rw [onlineBatchLaw_worker_marginal A.problem i, Measure.map_id]
  have hsample (y : Point d) : AEStronglyMeasurable
      (fun xi : Sample i ↦ stochasticGradient A.problem i xi y)
      (A.problem.sampleLaw i) := by
    have hprod :=
      (stochasticGradient_randomQuery_product_regular_of_lawRegularity
        A.problem hRegularity i (Measure.dirac ()) (A.problem.sampleLaw i)
          (fun _ : Unit ↦ y) id aestronglyMeasurable_const measurable_id
          (Measure.map_id)).2
    exact hprod.of_comp_snd Measure.dirac_ne_zero
  have hcoord (j : Fin b0.1) : Measure.map
      (fun row : Fin b0.1 → Sample i ↦ row j) rowBatchLaw =
        A.problem.sampleLaw i := by
    simpa [rowBatchLaw] using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun _ : Fin b0.1 ↦ A.problem.sampleLaw i) j)
  have hterm (y : Point d) (j : Fin b0.1) : AEStronglyMeasurable
      (fun row : Fin b0.1 → Sample i ↦
        stochasticGradient A.problem i (row j) y) rowBatchLaw := by
    let eval := fun row : Fin b0.1 → Sample i ↦ row j
    have hqmp : Measure.QuasiMeasurePreserving eval rowBatchLaw
        (A.problem.sampleLaw i) :=
      ⟨measurable_pi_apply j, by rw [show Measure.map eval rowBatchLaw =
        A.problem.sampleLaw i by simpa [eval] using hcoord j]⟩
    exact (hsample y).comp_quasiMeasurePreserving hqmp
  have hD : AEStronglyMeasurable localD rowBatchLaw := by
    unfold localD average SOptLib.finiteUniformAverage
    have hs := (Finset.aestronglyMeasurable_sum Finset.univ
      (fun j _ ↦ (hterm xNext j).sub (hterm x j))).const_smul
        ((Fintype.card (Fin b0.1) : ℝ)⁻¹)
    refine hs.congr (Filter.Eventually.of_forall ?_)
    intro row
    simp [Finset.sum_apply, Finset.sum_sub_distrib]
  let localDMk := hD.mk localD
  have hlocalDMk : Measurable localDMk := hD.measurable_mk
  have hinnovation : AEStronglyMeasurable innovation rowLaw := by
    have hm : Measurable (fun q : (Fin b0.1 → Sample i) × Ξ ↦
        A.quantizer.apply (localDMk q.1) q.2 - delta) :=
      (A.quantizer.measurable_apply_uncurry.comp
        ((hlocalDMk.comp measurable_fst).prodMk measurable_snd)).sub
          measurable_const
    refine hm.aestronglyMeasurable.congr ?_
    have hae : (fun q : (Fin b0.1 → Sample i) × Ξ ↦ localD q.1) =ᵐ[rowLaw]
        (fun q ↦ localDMk q.1) := by
      exact (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := rowBatchLaw) (ν := A.quantizer.law)).tendsto_ae hD.ae_eq_mk
    filter_upwards [hae] with q hq
    simp only [innovation]
    rw [hq]
  have hfull := onlineFixed_nonrefresh_worker_moment_of_assumption32
    (b0 := b0) A xNext x i Llocal ℒlocal ω hSmooth hAverageFiber hQuantizer
  have hcomp : innovation ∘ project =
      fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta := by
    funext q
    rfl
  have hinnovationMap : AEStronglyMeasurable innovation
      (Measure.map project fullLaw) := by
    rw [hmap]
    exact hinnovation
  have hvecMap : Integrable innovation (Measure.map project fullLaw) := by
    apply (MeasureTheory.integrable_map_measure hinnovationMap
      hproject.aemeasurable).mpr
    rw [hcomp]
    simpa [fullLaw, batchLaw, delta] using hfull.1
  have hsqMap : Integrable (fun q ↦ ‖innovation q‖ ^ 2)
      (Measure.map project fullLaw) := by
    apply (MeasureTheory.integrable_map_measure (hinnovationMap.norm.pow 2)
      hproject.aemeasurable).mpr
    change Integrable
      (fun q : ((w : Worker n) → Fin b0.1 → Sample w) × Ξ ↦
        ‖A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta‖ ^ 2)
      fullLaw
    simpa [fullLaw, batchLaw, delta] using hfull.2.1
  have hmean : (∫ q, innovation q ∂rowLaw) = 0 := by
    calc
      (∫ q, innovation q ∂rowLaw) =
          ∫ q, innovation q ∂Measure.map project fullLaw := by rw [hmap]
      _ = ∫ q, innovation (project q) ∂fullLaw :=
        MeasureTheory.integral_map hproject.aemeasurable hinnovationMap
      _ = 0 := by
        change (∫ q,
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta
            ∂fullLaw) = 0
        simpa [fullLaw, batchLaw, delta] using hfull.2.2.1
  have hsecond : (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) ≤
      (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
        ‖xNext - x‖ ^ 2 := by
    calc
      (∫ q, ‖innovation q‖ ^ 2 ∂rowLaw) =
          ∫ q, ‖innovation q‖ ^ 2 ∂Measure.map project fullLaw := by
            rw [hmap]
      _ = ∫ q, ‖innovation (project q)‖ ^ 2 ∂fullLaw :=
        MeasureTheory.integral_map hproject.aemeasurable
          (hinnovationMap.norm.pow 2)
      _ ≤ _ := by
        change (∫ q,
          ‖A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i xNext x) q.2 - delta‖ ^ 2
            ∂fullLaw) ≤ _
        simpa [fullLaw, batchLaw, delta] using hfull.2.2.2
  exact ⟨by simpa [hmap] using hvecMap, by simpa [hmap] using hsqMap,
    hmean, hsecond⟩

set_option maxHeartbeats 2000000 in
/-- Complete fixed-query worker aggregation from literal Assumption 3.2.
The worker-row product law makes the centered innovations independent, so
the average has the exact source `1 / n` coefficient.  Assumption 3.3 is not
used in this nonrefresh calculation; the weak Track-B correction is used
only to obtain row-law measurable representatives. -/
theorem onlineFixed_nonrefresh_average_moment_of_assumption32
    {d n b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ)
    (xNext x : Point d) (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAverageFiber : ∀ i : Worker n,
      let delta := localGradientDifference
        (onlineLocalProblem A.problem) i xNext x
      let D := fun batch ↦ onlineBatchDifference A.problem batch i xNext x
      Integrable D (onlineBatchLaw A.problem b0) ∧
        Integrable (fun batch ↦ ‖D batch - delta‖ ^ 2)
          (onlineBatchLaw A.problem b0) ∧
        (∫ batch, D batch ∂onlineBatchLaw A.problem b0) = delta ∧
        (∫ batch, ‖D batch - delta‖ ^ 2
          ∂onlineBatchLaw A.problem b0) ≤
          (ℒlocal i) ^ 2 / b0.1 * ‖xNext - x‖ ^ 2)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω) :
    let law := onlineDifferenceCompressionLaw (b0 := b0) A
    let innovation := fun i : Worker n ↦
      fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
          localGradientDifference (onlineLocalProblem A.problem) i xNext x
    Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
      Integrable (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  classical
  let law := onlineDifferenceCompressionLaw (b0 := b0) A
  let source := fun i : Worker n ↦
    fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
      (q.1 i, q.2 i)
  let rowLaw := fun i : Worker n ↦
    (Measure.infinitePi (fun _ : Fin b0.1 ↦ A.problem.sampleLaw i)).prod
      A.quantizer.law
  let localInnovation := fun i : Worker n ↦
    fun q : (Fin b0.1 → Sample i) × Ξ ↦
      A.quantizer.apply
        (average (fun j : Fin b0.1 ↦
          stochasticGradient A.problem i (q.1 j) xNext -
            stochasticGradient A.problem i (q.1 j) x)) q.2 -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x
  let innovation := fun i : Worker n ↦
    fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
        localGradientDifference (onlineLocalProblem A.problem) i xNext x
  letI (w : Worker n) : IsProbabilityMeasure (A.problem.sampleLaw w) :=
    A.problem.sampleLaw_isProbability w
  haveI : IsProbabilityMeasure (onlineBatchLaw A.problem b0) := by
    unfold onlineBatchLaw
    infer_instance
  letI : IsProbabilityMeasure A.quantizer.law := A.quantizer.law_isProbability
  haveI : IsProbabilityMeasure (workerCompressionLaw (n := n) A.quantizer) := by
    unfold workerCompressionLaw
    infer_instance
  haveI : IsProbabilityMeasure law := by
    unfold law onlineDifferenceCompressionLaw
    infer_instance
  have hsource : ∀ i : Worker n, Measurable (source i) := by
    intro i
    dsimp [source]
    fun_prop
  have hmap : ∀ i : Worker n, Measure.map (source i) law = rowLaw i := by
    intro i
    simpa [source, law, rowLaw] using
      onlineDifferenceCompressionLaw_worker_marginal (b0 := b0) A i
  have hlocal : ∀ i : Worker n,
      Integrable (localInnovation i) (rowLaw i) ∧
      Integrable (fun q ↦ ‖localInnovation i q‖ ^ 2) (rowLaw i) ∧
      (∫ q, localInnovation i q ∂rowLaw i) = 0 ∧
      (∫ q, ‖localInnovation i q‖ ^ 2 ∂rowLaw i) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
    intro i
    simpa [localInnovation, rowLaw] using
      (onlineFixed_nonrefresh_worker_row_moment_of_assumption32
        (b0 := b0) A xNext x i Llocal ℒlocal ω hSmooth
          (hAverageFiber i) hRegularity hQuantizer)
  have hcomp : ∀ i : Worker n,
      localInnovation i ∘ source i = innovation i := by
    intro i
    funext q
    rfl
  have hdiag : ∀ i : Worker n,
      Integrable (fun q ↦ ‖innovation i q‖ ^ 2) law ∧
      (∫ q, ‖innovation i q‖ ^ 2 ∂law) ≤
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
    intro i
    have hsqaesm : AEStronglyMeasurable
        (fun q ↦ ‖localInnovation i q‖ ^ 2) (Measure.map (source i) law) := by
      rw [hmap i]
      exact (hlocal i).2.1.aestronglyMeasurable
    constructor
    · have honMap : Integrable (fun q ↦ ‖localInnovation i q‖ ^ 2)
          (Measure.map (source i) law) := by
        simpa only [hmap i] using (hlocal i).2.1
      have hpull : Integrable
          ((fun q ↦ ‖localInnovation i q‖ ^ 2) ∘ source i) law :=
        (MeasureTheory.integrable_map_measure hsqaesm
          (hsource i).aemeasurable).mp honMap
      simpa [Function.comp_def, ← hcomp i] using hpull
    · have hInt :
          (∫ q, ‖localInnovation i (source i q)‖ ^ 2 ∂law) =
            ∫ q, ‖localInnovation i q‖ ^ 2
              ∂Measure.map (source i) law := by
        rw [MeasureTheory.integral_map (hsource i).aemeasurable hsqaesm]
      change (∫ q, ‖localInnovation i (source i q)‖ ^ 2 ∂law) ≤ _
      rw [hInt, hmap i]
      exact (hlocal i).2.2.2
  have hvec : ∀ i : Worker n,
      Integrable (innovation i) law ∧ (∫ q, innovation i q ∂law) = 0 := by
    intro i
    have hlocalOnMap : Integrable (localInnovation i)
        (Measure.map (source i) law) := by
      simpa only [hmap i] using (hlocal i).1
    have hlocalAesm : AEStronglyMeasurable (localInnovation i)
        (Measure.map (source i) law) := hlocalOnMap.aestronglyMeasurable
    have hpull : Integrable (localInnovation i ∘ source i) law :=
      (MeasureTheory.integrable_map_measure hlocalAesm
        (hsource i).aemeasurable).mp hlocalOnMap
    constructor
    · simpa [← hcomp i] using hpull
    · change (∫ q, (localInnovation i ∘ source i) q ∂law) = 0
      have hInt := (MeasureTheory.integral_map
        (hsource i).aemeasurable hlocalAesm).symm
      rw [show (∫ q, (localInnovation i ∘ source i) q ∂law) =
          ∫ q, localInnovation i q ∂Measure.map (source i) law by
        simpa [Function.comp_def] using hInt,
        hmap i]
      exact (hlocal i).2.2.1
  have hindep := onlineDifferenceCompressionLaw_worker_iIndep (b0 := b0) A
  have hcross : ∀ {i j : Worker n}, i ≠ j →
      (∫ q, ⟪innovation i q, innovation j q⟫_ℝ ∂law) = 0 := by
    intro i j hij
    let fi := localInnovation i
    let fj := localInnovation j
    let fiMk := (hlocal i).1.aestronglyMeasurable.mk fi
    let fjMk := (hlocal j).1.aestronglyMeasurable.mk fj
    have hfiMk : Measurable fiMk :=
      (hlocal i).1.aestronglyMeasurable.measurable_mk
    have hfjMk : Measurable fjMk :=
      (hlocal j).1.aestronglyMeasurable.measurable_mk
    have hfi_ae : fi =ᵐ[rowLaw i] fiMk :=
      (hlocal i).1.aestronglyMeasurable.ae_eq_mk
    have hfj_ae : fj =ᵐ[rowLaw j] fjMk :=
      (hlocal j).1.aestronglyMeasurable.ae_eq_mk
    have hqmpi : Measure.QuasiMeasurePreserving (source i) law (rowLaw i) :=
      ⟨hsource i, by rw [hmap i]⟩
    have hqmpj : Measure.QuasiMeasurePreserving (source j) law (rowLaw j) :=
      ⟨hsource j, by rw [hmap j]⟩
    have hfi_pull : (fi ∘ source i) =ᵐ[law] (fiMk ∘ source i) :=
      hqmpi.tendsto_ae hfi_ae
    have hfj_pull : (fj ∘ source j) =ᵐ[law] (fjMk ∘ source j) :=
      hqmpj.tendsto_ae hfj_ae
    have hfi_global : innovation i =ᵐ[law] fiMk ∘ source i := by
      rw [← hcomp i]
      simpa [fi] using hfi_pull
    have hfj_global : innovation j =ᵐ[law] fjMk ∘ source j := by
      rw [← hcomp j]
      simpa [fj] using hfj_pull
    have hfixed_int : ∀ _ : (Fin b0.1 → Sample j) × Ξ,
        Integrable (fun s ↦ fiMk s) (rowLaw i) := by
      intro _
      exact (hlocal i).1.congr hfi_ae
    have hfixed_zero : ∀ _ : (Fin b0.1 → Sample j) × Ξ,
        (∫ s, fiMk s ∂rowLaw i) = 0 := by
      intro _
      rw [← integral_congr_ae hfi_ae]
      exact (hlocal i).2.2.1
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
  have hmeas : ∀ i : Worker n, AEStronglyMeasurable (innovation i) law := by
    intro i
    exact (hvec i).1.aestronglyMeasurable
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    law (Finset.univ : Finset (Worker n)) innovation
      (fun i _ ↦ hmeas i) (fun i _ ↦ (hdiag i).1)
      (fun i _ j _ hij ↦ hcross hij)
  have havg_int : Integrable
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
  have havg_vec : Integrable
      (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law := by
    unfold average SOptLib.finiteUniformAverage
    simpa [Pi.smul_apply] using
      (MeasureTheory.integrable_finset_sum Finset.univ
        (fun i _ ↦ (hvec i).1)).smul ((n.1 : ℝ)⁻¹)
  have havg_zero :
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 := by
    unfold average SOptLib.finiteUniformAverage
    rw [integral_smul]
    rw [MeasureTheory.integral_finset_sum Finset.univ
      (fun i _ ↦ (hvec i).1)]
    simp [hvec]
  refine ⟨by simpa [innovation, law] using havg_vec,
    by simpa [innovation, law] using havg_zero,
    by simpa [innovation, law] using havg_int, ?_⟩
  have hcoeff_sum :
      (∑ i : Worker n,
        (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1)) =
      ω * ∑ i : Worker n, (Llocal i) ^ 2 +
        ((1 + ω) / b0.1) * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    calc
      _ = (∑ i : Worker n, ω * (Llocal i) ^ 2) +
          ∑ i : Worker n, ((1 + ω) / b0.1) * (ℒlocal i) ^ 2 := by
            rw [Finset.sum_add_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have hmean_L : 0 ≤ meanSquare Llocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hmean_A : 0 ≤ meanSquare ℒlocal := by
    unfold meanSquare average SOptLib.finiteUniformAverage
    positivity
  have hrms_L : (rootMeanSquare Llocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (Llocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_L]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hrms_A : (rootMeanSquare ℒlocal) ^ 2 =
      (n.1 : ℝ)⁻¹ * ∑ i : Worker n, (ℒlocal i) ^ 2 := by
    unfold rootMeanSquare
    rw [Real.sq_sqrt hmean_A]
    simp [meanSquare, average, SOptLib.finiteUniformAverage_def,
      Fintype.card_fin, smul_eq_mul]
  have hn : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
  have hb : (b0.1 : ℝ) ≠ 0 := by exact_mod_cast b0.2.ne'
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
    _ ≤ ((n.1 : ℝ)⁻¹) ^ 2 *
        ∑ i : Worker n,
          (ω * (Llocal i) ^ 2 + (1 + ω) * (ℒlocal i) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2 := by
      gcongr with i
      exact (hdiag i).2
    _ = (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
      rw [← Finset.sum_mul, hcoeff_sum, hrms_L, hrms_A]
      field_simp [hn, hb]

/-- Generated-query specialization of the complete worker aggregation.  It
uses the same two proof-exact iterates and the genuine-gradient formulation
of source Assumption 3.2; no literal Assumption 3.3 moment enters this
nonrefresh branch. -/
theorem onlineFixed_nonrefresh_average_moment_of_genuine_assumption32
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*} {Ξ : Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (run : ℕ → Ω → State d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0)
      A.problem run ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) (path : Ω) :
    let x := (run k path).x
    let xNext := (run (k + 1) path).x
    let law := onlineDifferenceCompressionLaw (b0 := b0) A
    let innovation := fun i : Worker n ↦
      fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
        A.quantizer.apply
            (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
          localGradientDifference (onlineLocalProblem A.problem) i xNext x
    Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
      (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
      Integrable (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2)
        law ∧
      (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          ‖xNext - x‖ ^ 2 := by
  dsimp only
  have hAverage : OnlineAverageSmoothness (b0 := b0)
      A.problem run ℒlocal :=
    onlineAssumption32Genuine_to_onlineAverageSmoothness hAssumption32
  exact onlineFixed_nonrefresh_average_moment_of_assumption32
    A (run (k + 1) path).x (run k path).x Llocal ℒlocal ω hSmooth
      (fun i ↦ hAverage.2 k i path) hRegularity hQuantizer

/-- Source-faithful law-a.e. Assumption 3.2 supplies the complete fixed-query
nonrefresh innovation moment at the generated homogeneous queries.  This is
the homogeneous analogue of the worker-dependent AE fiber used by Remark
D.2; it deliberately states no obligation on null paths. -/
theorem onlineFixed_nonrefresh_average_moment_ae_of_genuine_assumption32
    {d n b0 : Count} {Ω : Type*} {Sample : Worker n → Type*} {Ξ : Type*}
    [MeasurableSpace Ω] [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (run : ℕ → Ω → State d)
    (pathLaw : Measure Ω) (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hAssumption32 : OnlineAssumption32GenuineAE (b0 := b0)
      A.problem run pathLaw ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
    (k : ℕ) :
    ∀ᵐ path ∂pathLaw,
      let x := (run k path).x
      let xNext := (run (k + 1) path).x
      let law := onlineDifferenceCompressionLaw (b0 := b0) A
      let innovation := fun i : Worker n ↦
        fun q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ) ↦
          A.quantizer.apply
              (onlineBatchDifference A.problem q.1 i xNext x) (q.2 i) -
            localGradientDifference (onlineLocalProblem A.problem) i xNext x
      Integrable (fun q ↦ average (fun i : Worker n ↦ innovation i q)) law ∧
        (∫ q, average (fun i : Worker n ↦ innovation i q) ∂law) = 0 ∧
        Integrable (fun q ↦ ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2)
          law ∧
        (∫ q, ‖average (fun i : Worker n ↦ innovation i q)‖ ^ 2 ∂law) ≤
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            ‖xNext - x‖ ^ 2 := by
  have hAverage :=
    onlineAssumption32GenuineAE_to_onlineAverageSmoothnessAE hAssumption32
  filter_upwards [hAverage.2 k] with path hpath
  dsimp only
  exact onlineFixed_nonrefresh_average_moment_of_assumption32
    A (run (k + 1) path).x (run k path).x Llocal ℒlocal ω hSmooth
      hpath hRegularity hQuantizer

set_option maxHeartbeats 3000000 in
/-- The generated nonrefresh branch of proof-exact Algorithm 3 under genuine
source Assumption 3.2 and the weak law-level Track-B correction.  The theorem
transports the fixed-query innovation moment through the strict-past/current
round product decomposition, proves cancellation against the carried
estimator residual, and proves independence of the complete nonrefresh square
from the same-round refresh coin. -/
theorem
    onlineProofExact_nonrefresh_branch_moments_of_genuine_assumption32_and_lawRegularity
    {d n b b0 : Count} {Sample : Worker n → Type*} {Ξ : Type*}
    [∀ i, MeasurableSpace (Sample i)] [MeasurableSpace Ξ]
    (A : OnlineData d n Sample Ξ) (x0 : Point d)
    (Llocal ℒlocal : Worker n → ℝ) (ω : ℝ)
    (hSmooth : IsLocallySmooth (onlineLocalProblem A.problem) Llocal)
    (hBatch : OnlineBatchAdmissible b b0)
    (hAssumption32 : OnlineAssumption32Genuine (b0 := b0) A.problem
      (onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch) ℒlocal)
    (hRegularity : OnlineAdaptiveSampleGradientLawRegularity A.problem)
    (hQuantizer : IsUnbiasedQuantizer A.quantizer ω)
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
    let residual := fun path ↦
      (run k path).g - globalGradient P (run k path).x
    let innovation := fun path ↦ average (fun i : Worker n ↦
      A.quantizer.apply
          (onlineBatchDifference A.problem (path k).2.1.2 i
            (run (k + 1) path).x (run k path).x)
          ((path k).2.2 i) -
        localGradientDifference P i
          (run (k + 1) path).x (run k path).x)
    Integrable (fun path ↦ ‖innovation path‖ ^ 2) law ∧
      (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
        (1 / (n.1 : ℝ)) *
          (ω * (rootMeanSquare Llocal) ^ 2 +
            (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
          stepMoment run law k ∧
      (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 ∧
      Integrable (fun path ↦ ‖residual path + innovation path‖ ^ 2) law ∧
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) ≤
        estimatorErrorMoment P run law k +
          (1 / (n.1 : ℝ)) *
            (ω * (rootMeanSquare Llocal) ^ 2 +
              (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1) *
            stepMoment run law k ∧
      ProbabilityTheory.IndepFun
        (fun path ↦ ‖residual path + innovation path‖ ^ 2)
        (fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1) law := by
  classical
  let P := onlineLocalProblem A.problem
  let run := onlineProofExactProcess (b := b) (b0 := b0) A x0 hBatch
  let law := onlineProofExactPathLaw (b := b) (b0 := b0) A
  let prefixMap := onlineRoundPrefix
    (n := n) (b := b) (b0 := b0) (Sample := Sample) (Ξ := Ξ) k
  let prefixLaw := onlineRoundPrefixLaw (b := b) (b0 := b0) A k
  let current := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ path k
  let noise := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    ((path k).2.1.2, (path k).2.2)
  let noiseLaw := onlineDifferenceCompressionLaw (b0 := b0) A
  let C := (1 / (n.1 : ℝ)) *
    (ω * (rootMeanSquare Llocal) ^ 2 +
      (1 + ω) * (rootMeanSquare ℒlocal) ^ 2 / b0.1)
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
  let fallback : ℕ → OnlineRoundNoise n b b0 Sample Ξ :=
    Classical.choice (nonempty_of_isProbabilityMeasure law)
  let prefixState := onlineProofExactPrefixState A x0 hBatch fallback k
  let xNext := fun pref ↦ primalStep A.stepSize (prefixState pref)
  let x := fun pref ↦ (prefixState pref).x
  let direction := fun pref ↦
    (prefixState pref).g - globalGradient P (prefixState pref).x
  let innovationKernel := fun
      (pref : Fin k → OnlineRoundNoise n b b0 Sample Ξ)
      (q : ((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
    average (fun i : Worker n ↦
    A.quantizer.apply
        (onlineBatchDifference A.problem q.1 i (xNext pref) (x pref))
        (q.2 i) -
      localGradientDifference P i (xNext pref) (x pref))
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
  let B := fun pref ↦ C * ‖xNext pref - x pref‖ ^ 2
  have hprefix : Measurable prefixMap := by
    dsimp [prefixMap, onlineRoundPrefix]
    exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1
  have hprefixLaw : Measure.map prefixMap law = prefixLaw := by rfl
  haveI : IsProbabilityMeasure prefixLaw := by
    rw [← hprefixLaw]
    exact Measure.isProbabilityMeasure_map hprefix.aemeasurable
  haveI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw onlineDifferenceCompressionLaw
    infer_instance
  have hcurrent : Measurable current := measurable_pi_apply k
  have hnoise : Measurable noise := by
    dsimp [noise]
    fun_prop
  have hpastCurrent : ProbabilityTheory.IndepFun prefixMap current law := by
    apply indepFun_of_map_prod_eq_prod_laws
      (Z := fun path ↦ (prefixMap path, current path))
      (P := law) (mu := prefixLaw)
      (nu := onlineRoundLaw (b := b) (b0 := b0) A)
    · exact (hprefix.prodMk hcurrent).aemeasurable
    · simpa [law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ onlineRoundLaw (b := b) (b0 := b0) A) k)
  have hfresh : ProbabilityTheory.IndepFun prefixMap noise law := by
    simpa [noise, current, Function.comp_def] using
      hpastCurrent.comp measurable_id
        (by fun_prop : Measurable
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2)))
  have hnoiseLaw : Measure.map noise law = noiseLaw := by
    calc
      Measure.map noise law = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          (Measure.map current law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · fun_prop
            · exact hcurrent
      _ = Measure.map
          (fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ (z.2.1.2, z.2.2))
          (onlineRoundLaw A) := by
            rw [show Measure.map current law = onlineRoundLaw A by
              simpa [current, law, onlineProofExactPathLaw] using
                SOptLib.iidStreamLaw_map_eval
                  (onlineRoundLaw (b := b) (b0 := b0) A) k]
      _ = noiseLaw := by
        simpa [noiseLaw] using onlineRoundLaw_differenceCompression_marginal
          (b := b) (b0 := b0) A
  have hprefixState : AEMeasurable prefixState prefixLaw := by
    simpa [prefixState, prefixLaw] using
      onlineProofExactPrefixState_all_aemeasurable_of_lawRegularity
        A x0 hBatch hRegularity fallback k
  have hxNext : AEStronglyMeasurable xNext prefixLaw :=
    ((measurable_primalStep A.stepSize).comp_aemeasurable hprefixState)
      |>.aestronglyMeasurable
  have hx : AEStronglyMeasurable x prefixLaw :=
    ((measurable_state_x d).comp_aemeasurable hprefixState).aestronglyMeasurable
  have hdirection : AEStronglyMeasurable direction prefixLaw := by
    exact (((measurable_state_g d).comp_aemeasurable hprefixState).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hprefixState))).aestronglyMeasurable
  have hkernel : AEStronglyMeasurable
      (fun p ↦ innovationKernel p.1 p.2) (prefixLaw.prod noiseLaw) := by
    simpa [innovationKernel, xNext, x, noiseLaw, P] using
      onlineNonrefreshAverage_product_aestronglyMeasurable_of_lawRegularity
        (b0 := b0) A hRegularity prefixLaw xNext x hxNext hx
  have hkernelSq : AEStronglyMeasurable
      (fun p ↦ ‖innovationKernel p.1 p.2‖ ^ 2)
      (prefixLaw.prod noiseLaw) := by
    simpa [pow_two] using hkernel.norm.mul hkernel.norm
  have hAverage : OnlineAverageSmoothness (b0 := b0) A.problem run ℒlocal :=
    onlineAssumption32Genuine_to_onlineAverageSmoothness hAssumption32
  have hfixed (pref) := onlineFixed_nonrefresh_average_moment_of_assumption32
    (b0 := b0) A (xNext pref) (x pref) Llocal ℒlocal ω hSmooth
      (fun i ↦ by
        simpa [xNext, x, prefixState, run, onlineProofExactPrefixState,
          onlineProofExactProcess_succ, onlineStep, primalStep_eq] using
          hAverage.2 k i (onlineExtendRoundPrefix fallback pref))
      hRegularity hQuantizer
  have hB_aesm : AEStronglyMeasurable B (Measure.map prefixMap law) := by
    rw [hprefixLaw]
    dsimp [B]
    simpa [pow_two] using
      ((hxNext.sub hx).norm.mul (hxNext.sub hx).norm).const_mul C
  have hB_comp_int : Integrable (fun path ↦ B (prefixMap path)) law := by
    have hs := hStep.const_mul C
    apply hs.congr
    filter_upwards [] with path
    dsimp [B, xNext, x, prefixState, run]
    rw [onlineProofExactProcess_succ]
    have heq := onlineProofExactProcess_congr_prefix A x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])
    rw [heq]
    rfl
  have havgSqComp : Integrable
      (fun path ↦ ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2) law :=
    integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
      (P := law) (ν := noiseLaw)
      (X := prefixMap) (Y := noise)
      (φ := fun pref q ↦ ‖innovationKernel pref q‖ ^ 2) (B := B)
      hkernelSq hB_aesm hprefix.aemeasurable hnoise.aemeasurable hfresh
      hnoiseLaw (fun _ _ ↦ sq_nonneg _) (fun pref ↦ (hfixed pref).2.2.1)
      hB_comp_int (fun pref ↦ by simpa [B, C] using (hfixed pref).2.2.2)
  have hstatePrefix : ∀ path, prefixState (prefixMap path) = run k path := by
    intro path
    dsimp [prefixState, run]
    exact (onlineProofExactProcess_congr_prefix
      A x0 hBatch k
      (path := path) (path' := onlineExtendRoundPrefix fallback (prefixMap path))
      (by
        intro t ht
        simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])).symm
  have hinnovationComp : ∀ path,
      innovationKernel (prefixMap path) (noise path) = innovation path := by
    intro path
    dsimp [innovationKernel, innovation, xNext, x, noise]
    rw [hstatePrefix path]
    rw [show (run (k + 1) path).x = primalStep A.stepSize (run k path) by rfl]
  have hinnovationMeas : AEStronglyMeasurable innovation law := by
    have hkernelMapped : AEStronglyMeasurable
        (fun p ↦ innovationKernel p.1 p.2)
        ((Measure.map prefixMap law).prod (Measure.map noise law)) := by
      rw [hprefixLaw, hnoiseLaw]
      exact hkernel
    have hcomp := aestronglyMeasurable_comp_of_indep_product_law
      hprefix.aemeasurable hnoise.aemeasurable
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law))
      hfresh hkernelMapped
    exact hcomp.congr (Filter.Eventually.of_forall hinnovationComp)
  have havgSq : Integrable (fun path ↦ ‖innovation path‖ ^ 2) law := by
    exact havgSqComp.congr (Filter.Eventually.of_forall fun path ↦ by
      simpa only using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
        (hinnovationComp path))
  have havgBoundComp :
      (∫ path, ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2 ∂law) ≤
        ∫ path, B (prefixMap path) ∂law :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := law) (ν := noiseLaw)
      (X := prefixMap) (Y := noise)
      (φ := fun pref q ↦ ‖innovationKernel pref q‖ ^ 2) (B := B)
      hkernelSq hB_aesm hprefix.aemeasurable hnoise.aemeasurable hfresh
      hnoiseLaw havgSqComp hB_comp_int
      (fun pref ↦ by simpa [B, C] using (hfixed pref).2.2.2)
  have havgBound : (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤
      C * stepMoment run law k := by
    calc
      (∫ path, ‖innovation path‖ ^ 2 ∂law) =
          ∫ path, ‖innovationKernel (prefixMap path) (noise path)‖ ^ 2 ∂law := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun path ↦ by
              simpa only using congrArg (fun z : Point d ↦ ‖z‖ ^ 2)
                (hinnovationComp path).symm
      _ ≤ ∫ path, B (prefixMap path) ∂law := havgBoundComp
      _ = C * stepMoment run law k := by
        unfold stepMoment
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with path
        dsimp [B, xNext, x, prefixState, run, stepMoment]
        rw [onlineProofExactProcess_succ]
        have heq := onlineProofExactProcess_congr_prefix A x0 hBatch k
          (path := path)
          (path' := onlineExtendRoundPrefix fallback (prefixMap path))
          (by
            intro t ht
            simp [onlineExtendRoundPrefix, prefixMap, onlineRoundPrefix, ht])
        rw [heq]
        rfl
  have hresidualMeas : AEStronglyMeasurable residual law := by
    have hs := onlineProofExactProcess_aemeasurable_of_lawRegularity
      A x0 hBatch hRegularity k
    exact (((measurable_state_g d).comp_aemeasurable hs).sub
      ((measurable_gradient (globalObjective P)).comp_aemeasurable
        ((measurable_state_x d).comp_aemeasurable hs))).aestronglyMeasurable
  have hresidualSq : Integrable (fun path ↦ ‖residual path‖ ^ 2) law := by
    simpa [residual, P, run, law, EstimatorErrorMomentWellDefined] using hError
  have hinnerInt : Integrable
      (fun path ↦ ⟪residual path, innovation path⟫_ℝ) law :=
    integrable_inner_of_integrable_sq_norm hresidualMeas hinnovationMeas
      hresidualSq havgSq
  have hscalarProd : AEStronglyMeasurable
      (fun p ↦ ⟪direction p.1, innovationKernel p.1 p.2⟫_ℝ)
      (prefixLaw.prod noiseLaw) :=
    hdirection.comp_fst.inner hkernel
  have hinnerComp : ∀ path,
      ⟪direction (prefixMap path), innovationKernel (prefixMap path) (noise path)⟫_ℝ =
        ⟪residual path, innovation path⟫_ℝ := by
    intro path
    rw [hinnovationComp path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hinnerCompInt : Integrable
      (fun path ↦ ⟪direction (prefixMap path),
        innovationKernel (prefixMap path) (noise path)⟫_ℝ) law :=
    hinnerInt.congr (Filter.Eventually.of_forall fun path ↦ (hinnerComp path).symm)
  have hfixedInnerZero : ∀ pref,
      (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) = 0 := by
    intro pref
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := (innerSL ℝ) (direction pref)) (hfixed pref).1
    calc
      (∫ q, ⟪direction pref, innovationKernel pref q⟫_ℝ ∂noiseLaw) =
          (innerSL ℝ) (direction pref)
            (∫ q, innovationKernel pref q ∂noiseLaw) := hlin
      _ = 0 := by rw [(hfixed pref).2.1]; simp
  have hcrossComp :=
    integral_comp_eq_zero_of_indep_fixed_integral_zero_aestronglyMeasurable
      (P := law) (ν := noiseLaw)
      (X := prefixMap) (Y := noise)
      (φ := fun pref q ↦ ⟪direction pref, innovationKernel pref q⟫_ℝ)
      hscalarProd hprefix.aemeasurable hnoise.aemeasurable hfresh hnoiseLaw
      hinnerCompInt hfixedInnerZero
  have hcross : (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) = 0 := by
    rw [show (∫ path, ⟪residual path, innovation path⟫_ℝ ∂law) =
        ∫ path, ⟪direction (prefixMap path),
          innovationKernel (prefixMap path) (noise path)⟫_ℝ ∂law by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun path ↦ (hinnerComp path).symm]
    exact hcrossComp
  have hnonrefreshInt : Integrable
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) law :=
    integrable_sq_norm_add hresidualMeas hinnovationMeas hresidualSq havgSq
  have hnonrefreshEq :
      (∫ path, ‖residual path + innovation path‖ ^ 2 ∂law) =
        (∫ path, ‖residual path‖ ^ 2 ∂law) +
          ∫ path, ‖innovation path‖ ^ 2 ∂law := by
    let pair : Bool → (ℕ → OnlineRoundNoise n b b0 Sample Ξ) → Point d :=
      fun z ↦ if z then innovation else residual
    have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      law (Finset.univ : Finset Bool) pair
      (fun z _ ↦ by cases z <;> simp [pair, hresidualMeas, hinnovationMeas])
      (fun z _ ↦ by cases z <;> simp [pair, hresidualSq, havgSq])
      (fun z _ w _ hzw ↦ by
        cases z <;> cases w
        · exact False.elim (hzw rfl)
        · simpa [pair] using hcross
        · simpa [pair, real_inner_comm] using hcross
        · exact False.elim (hzw rfl))
    simpa [pair, Fintype.sum_bool, add_comm] using hsum
  let branch := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦ (path k).1
  let rest := fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.2
  let branchRound := fun z : OnlineRoundNoise n b b0 Sample Ξ ↦ z.1
  let restLaw := ((onlineBatchLaw A.problem b).prod
    (onlineBatchLaw A.problem b0)).prod
      (workerCompressionLaw (n := n) A.quantizer)
  let joined := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
    (prefixMap path, noise path)
  have hroundRest : ProbabilityTheory.IndepFun rest branchRound
      (onlineRoundLaw (b := b) (b0 := b0) A) := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := refreshLaw A.refreshProbability A.refresh_admissible)
      (ν := restLaw) measurable_id measurable_id).symm
    simpa [onlineRoundLaw, restLaw, rest, branchRound] using h
  have hprefixRestBranch : ProbabilityTheory.IndepFun
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ ↦ (z.1, rest z.2))
      (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          OnlineRoundNoise n b b0 Sample Ξ ↦ branchRound z.2)
      (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) := by
    exact indepFun_prod_left_adjoin_of_indepFun prefixLaw
      (onlineRoundLaw (b := b) (b0 := b0) A) rest branchRound
      measurable_snd measurable_fst hroundRest
  have hpastRestBranch : ProbabilityTheory.IndepFun
      (fun path ↦ (prefixMap path, rest (current path))) branch law := by
    have hmap : Measure.map (fun path ↦ (prefixMap path, current path)) law =
        prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A) := by
      simpa [law, prefixLaw, prefixMap, current,
        onlineProofExactPathLaw, onlineRoundPrefixLaw, onlineRoundPrefix,
        SOptLib.iidStreamLaw] using
        (infinitePi_prefix_current_map_eq_prod
          (fun _ : ℕ ↦ onlineRoundLaw (b := b) (b0 := b0) A) k)
    apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      ((hprefix.prodMk ((measurable_snd).comp hcurrent)).aemeasurable)
      ((measurable_fst.comp hcurrent).aemeasurable)).2
    let leftProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ ↦ (z.1, rest z.2)
    let rightProd := fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
        OnlineRoundNoise n b b0 Sample Ξ ↦ branchRound z.2
    let Z := fun path : ℕ → OnlineRoundNoise n b b0 Sample Ξ ↦
      (prefixMap path, current path)
    have hleft : Measurable leftProd := by dsimp [leftProd]; fun_prop
    have hright : Measurable rightProd := by dsimp [rightProd]; fun_prop
    have hZ : Measurable Z := hprefix.prodMk hcurrent
    calc
      Measure.map
          (fun path ↦ ((prefixMap path, rest (current path)), branch path)) law =
          Measure.map (fun z ↦ (leftProd z, rightProd z)) (Measure.map Z law) := by
            rw [MeasureTheory.Measure.map_map]
            · rfl
            · exact hleft.prodMk hright
            · exact hZ
      _ = Measure.map (fun z ↦ (leftProd z, rightProd z))
          (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) := by
            rw [show Measure.map Z law =
                prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A) by
              simpa [Z] using hmap]
      _ = (Measure.map leftProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))).prod
          (Measure.map rightProd
            (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A))) :=
        (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hleft.aemeasurable hright.aemeasurable).1 hprefixRestBranch
      _ = (Measure.map (fun path ↦ (prefixMap path, rest (current path))) law).prod
          (Measure.map branch law) := by
        rw [show Measure.map leftProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map (fun path ↦ (prefixMap path, rest (current path))) law by
          calc
            _ = Measure.map leftProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hleft hZ]
              congr 1]
        rw [show Measure.map rightProd
              (prefixLaw.prod (onlineRoundLaw (b := b) (b0 := b0) A)) =
            Measure.map branch law by
          calc
            _ = Measure.map rightProd (Measure.map Z law) := by rw [hmap]
            _ = _ := by
              rw [MeasureTheory.Measure.map_map hright hZ]
              congr 1]
  have hjointBranch : ProbabilityTheory.IndepFun joined branch law := by
    have h := hpastRestBranch.comp
      (show Measurable
        (fun z : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
            ((((w : Worker n) → Fin b.1 → Sample w) ×
              ((w : Worker n) → Fin b0.1 → Sample w)) ×
              (Worker n → Ξ)) ↦ (z.1, (z.2.1.2, z.2.2))) by fun_prop)
      measurable_id
    simpa [joined, noise, current, rest, branch, Function.comp_def] using h
  have hnonrefreshKernel : AEStronglyMeasurable
      (fun p : (Fin k → OnlineRoundNoise n b b0 Sample Ξ) ×
          (((w : Worker n) → Fin b0.1 → Sample w) × (Worker n → Ξ)) ↦
        ‖direction p.1 + innovationKernel p.1 p.2‖ ^ 2)
      (prefixLaw.prod noiseLaw) := by
    have hv := hdirection.comp_fst.add hkernel
    simpa [pow_two] using hv.norm.mul hv.norm
  have hjJoined : Measurable joined := by
    dsimp [joined]
    exact hprefix.prodMk hnoise
  have hprefixJoined : Measurable[MeasurableSpace.comap joined inferInstance]
      prefixMap :=
    measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)
  have hnoiseJoined : Measurable[MeasurableSpace.comap joined inferInstance]
      noise :=
    measurable_snd.comp (measurable_iff_comap_le.mpr le_rfl)
  obtain ⟨nonrefreshRep, hnonrefreshRepMeas, hnonrefreshAe⟩ :=
    ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
      (MeasurableSpace.comap joined inferInstance) prefixMap prefixMap noise
      (fun pref q ↦ ‖direction pref + innovationKernel pref q‖ ^ 2) law
      (inferInstance : SigmaFinite (Measure.map prefixMap law))
      (inferInstance : SigmaFinite (Measure.map noise law))
      hjJoined.comap_le hprefixJoined hnoiseJoined
      (Filter.Eventually.of_forall fun _ ↦ rfl) hfresh
      (by simpa [hprefixLaw, hnoiseLaw] using hnonrefreshKernel)
  have hrepIndep : ProbabilityTheory.IndepFun nonrefreshRep branch law := by
    have hcomap : ProbabilityTheory.Indep
        (MeasurableSpace.comap joined inferInstance)
        (MeasurableSpace.comap branch inferInstance) law := by
      simpa [ProbabilityTheory.IndepFun_iff_Indep] using hjointBranch
    exact indepFun_of_measurable_left_of_indep_comap
      hnonrefreshRepMeas.measurable hcomap
  have hnonrefreshComp : ∀ path,
      ‖direction (prefixMap path) + innovationKernel (prefixMap path) (noise path)‖ ^ 2 =
        ‖residual path + innovation path‖ ^ 2 := by
    intro path
    rw [hinnovationComp path]
    dsimp [direction, residual]
    rw [hstatePrefix path]
  have hnonrefreshIndep : ProbabilityTheory.IndepFun
      (fun path ↦ ‖residual path + innovation path‖ ^ 2) branch law := by
    apply hrepIndep.congr ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [hnonrefreshAe] with path hp
    exact hp.symm.trans (hnonrefreshComp path)
  refine ⟨havgSq, ?_, hcross, hnonrefreshInt, ?_, hnonrefreshIndep⟩
  · simpa [C] using havgBound
  · rw [hnonrefreshEq]
    change estimatorErrorMoment P run law k +
        (∫ path, ‖innovation path‖ ^ 2 ∂law) ≤ _
    exact add_le_add_right (by simpa [C] using havgBound) _

end MARINA
