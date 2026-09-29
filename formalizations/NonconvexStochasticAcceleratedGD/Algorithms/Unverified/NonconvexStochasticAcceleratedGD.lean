import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.ConditionalExpectation
import SOptLib.Model.ConditionalExpectation
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Martingale
import SOptLib.Glue.Probability
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope

open scoped BigOperators
open scoped Gradient
open MeasureTheory

namespace SOptLib
namespace FOML
namespace NonconvexStochasticAcceleratedGD

noncomputable section

/-- The paper's decision space `ℝ^n`, represented by Mathlib's Euclidean space on `Fin n`. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Positive paper time indices. Algorithm 6.4 is indexed by `k ≥ 1`. -/
abbrev PositiveTime := {k : ℕ // 1 ≤ k}

/-- A finite positive output window `1, ..., N`. -/
abbrev WindowTime (N : ℕ) := {k : ℕ // 1 ≤ k ∧ k ≤ N}

/-- The finite stopping-time support as a subtype of the concrete finite set `1, ..., N`. -/
abbrev OutputTime (N : ℕ) := {k : ℕ // k ∈ Finset.Icc 1 N}

/-- Source-facing data and primitive assumptions for Algorithm 6.4 and Theorem 6.12.

The iterate sequences are intentionally absent: they are generated below by
`stateAfter` from the printed Algorithm 6.4 updates. -/
structure Setup (n : ℕ) (Sample : Type*) [MeasurableSpace Sample] where
  Ψ : Space n → ℝ
  G : Space n → Sample → Space n
  sampleLaw : PositiveTime → ProbabilityMeasure Sample
  sampleStreamLaw : ProbabilityMeasure (ℕ → Sample)
  x0 : Space n
  LΨ : ℝ
  σ : ℝ
  alpha : ℕ → ℝ
  beta : ℕ → ℝ
  lam : ℕ → ℝ
  hLΨ_pos : 0 < LΨ
  hσ_nonneg : 0 ≤ σ
  halpha_one : alpha 1 = 1
  halpha_mem : ∀ k, 2 ≤ k → alpha k ∈ Set.Ioo (0 : ℝ) 1
  hbeta_pos : ∀ k, 1 ≤ k → 0 < beta k
  hlam_pos : ∀ k, 1 ≤ k → 0 < lam k
  hDifferentiable : Differentiable ℝ Ψ
  hboundedBelow : BddBelow (Set.range Ψ)
  hLipschitzGrad :
    ∀ x y : Space n, ‖gradient Ψ y - gradient Ψ x‖ ≤ LΨ * ‖y - x‖
  hSampleMarginal :
    ∀ k : PositiveTime,
      Measure.map (fun ξ : ℕ → Sample => ξ k.1) (sampleStreamLaw : Measure (ℕ → Sample)) =
        (sampleLaw k : Measure Sample)
  hOracleUnbiased :
    ∀ k : PositiveTime, ∀ x : Space n,
      expectationEq (sampleLaw k : Measure Sample) (fun s => G x s) (gradient Ψ x)
  hOracleVariance :
    ∀ k : PositiveTime, ∀ x : Space n,
      expectationLe (sampleLaw k : Measure Sample)
        (fun s => (‖G x s - gradient Ψ x‖ ^ 2 : ℝ)) (σ ^ 2)

variable {n : ℕ} {Sample : Type*} [MeasurableSpace Sample]

/-- Coerce a stopping index supported on `{1, ..., N}` to positive paper time. -/
def outputTimePositive {N : ℕ} (k : OutputTime N) : PositiveTime :=
  ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩

/-- Coerce a stopping index supported on `{1, ..., N}` to the window subtype. -/
def outputTimeWindow {N : ℕ} (k : OutputTime N) : WindowTime N :=
  ⟨k.1, Finset.mem_Icc.mp k.2⟩

/-- Coerce a window subtype index to the finite stopping support. -/
def windowTimeOutput {N : ℕ} (k : WindowTime N) : OutputTime N :=
  ⟨k.1, Finset.mem_Icc.mpr k.2⟩

/-- The sample coordinate `ξ_k` of the stochastic process. -/
def sampleAt (ξ : ℕ → Sample) (k : PositiveTime) : Sample :=
  ξ k.1

/-- The canonical gradient `∇Ψ`, defined from the paper objective rather than supplied
as independent witness data. -/
def gradΨ (S : Setup n Sample) (x : Space n) : Space n :=
  ∇ S.Ψ x

/-- The paper's differentiability assumption justifies reading `gradΨ` as the usual
gradient of `Ψ`. -/
theorem differentiable_Ψ (S : Setup n Sample) :
    Differentiable ℝ S.Ψ :=
  S.hDifferentiable

@[simp]
theorem gradΨ_eq_gradient (S : Setup n Sample) (x : Space n) :
    gradΨ S x = ∇ S.Ψ x := by
  rfl

/-- The paper's optimal value notation `Ψ*`.  The theorem statement uses this as the
lower endpoint of the bounded-below objective; when a minimizer exists, the bridge
below identifies it with the literal minimum from (6.4.1). -/
def Ψstar (S : Setup n Sample) : ℝ :=
  sInf (Set.range S.Ψ)

/-- The bounded-below setup makes `Ψ*` a global lower bound for objective values. -/
theorem Ψstar_le_value (S : Setup n Sample) (x : Space n) :
    Ψstar S ≤ S.Ψ x := by
  unfold Ψstar
  exact csInf_le S.hboundedBelow ⟨x, rfl⟩

/-- Bridge from the infimum realization of `Ψ*` to the paper's literal minimum when
problem (6.4.1) has an optimizer. -/
theorem Ψstar_eq_value_of_minimizer
    (S : Setup n Sample) (xStar : Space n) (hxStar : ∀ x : Space n, S.Ψ xStar ≤ S.Ψ x) :
    Ψstar S = S.Ψ xStar := by
  apply le_antisymm
  · exact Ψstar_le_value S xStar
  · unfold Ψstar
    refine le_csInf ?_ ?_
    · exact ⟨S.Ψ xStar, ⟨xStar, rfl⟩⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact hxStar x

/-- Smoothness upper model (6.4.7), derived from differentiability and the
Lipschitz-gradient assumption rather than stored as a primitive setup field. -/
theorem smoothUpper (S : Setup n Sample) (x y : Space n) :
    |S.Ψ y - S.Ψ x - inner ℝ (gradΨ S x) (y - x)| ≤
      (S.LΨ / 2) * ‖y - x‖ ^ 2 := by
  simpa using
    abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
      (X := (Set.univ : Set (Space n))) (f := S.Ψ) (grad := gradΨ S) (L := S.LΨ)
      convex_univ
      (by
        intro z hz
        simpa [gradΨ] using (S.hDifferentiable z).hasGradientAt)
      (by
        intro z hz w hw
        simpa [gradΨ] using S.hLipschitzGrad w z)
      (x := x) (y := y) (by simp) (by simp)

/-- The source distribution of the coordinate `ξ_k` is `P_k`. -/
theorem sampleAt_law (S : Setup n Sample) (k : PositiveTime) :
    Measure.map (fun ξ : ℕ → Sample => sampleAt ξ k)
        (S.sampleStreamLaw : Measure (ℕ → Sample)) =
      (S.sampleLaw k : Measure Sample) := by
  simpa [sampleAt] using S.hSampleMarginal k

/-- Coordinate projections of the sample stream are measurable in the canonical product space. -/
theorem sampleCoordinate_measurable (j : ℕ) :
    Measurable (fun ξ : ℕ → Sample => ξ j) := by
  exact measurable_pi_apply j

/-- The natural filtration generated by the sample prefix `ξ_[k]`. -/
def sampleFiltration :
    Filtration ℕ (by infer_instance : MeasurableSpace (ℕ → Sample)) :=
  SOptLib.filtration (fun (j : ℕ) (ξ : ℕ → Sample) => ξ j) sampleCoordinate_measurable

/-- Each coordinate `ξ_k` is measurable with respect to the prefix filtration containing it. -/
theorem sampleAt_measurable_prefix (k : PositiveTime) :
    Measurable[(sampleFiltration (Sample := Sample)).seq (k.1 + 1)]
      (fun ξ : ℕ → Sample => sampleAt ξ k) := by
  simpa [sampleFiltration, sampleAt] using
    SOptLib.measurable_sample_le_prefixFiltration
      (fun (j : ℕ) (ξ : ℕ → Sample) => ξ j) sampleCoordinate_measurable k.1

/-- The recursive accelerated `Γ` schedule from (6.4.11). -/
def Γ (S : Setup n Sample) (k : PositiveTime) : ℝ :=
  acceleratedGammaSchedule S.alpha k

@[simp]
theorem Γ_one (S : Setup n Sample) :
    Γ S ⟨1, le_rfl⟩ = 1 := by
  rfl

theorem Γ_succ (S : Setup n Sample) (k : ℕ) (hk : 1 ≤ k) :
    Γ S ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ =
      (1 - S.alpha (k + 1)) * Γ S ⟨k, hk⟩ := by
  simpa [Γ] using acceleratedGammaSchedule_succ S.alpha k hk

/-- Positivity of the paper `Γ` schedule, derived from Algorithm 6.4's domain for `α`. -/
theorem Γ_pos (S : Setup n Sample) (k : PositiveTime) :
    0 < Γ S k := by
  unfold Γ
  exact acceleratedGamma_pos_of_alpha_lt_one S.alpha (fun t ht => (S.halpha_mem t ht).2) k

/-- The sampled stochastic gradient value `G(x, ξ_k)`. -/
def sampledOracle (S : Setup n Sample) (x : Space n) (ξk : Sample) : Space n :=
  S.G x ξk

@[simp]
theorem sampledOracle_apply (S : Setup n Sample) (x : Space n) (ξk : Sample) :
    sampledOracle S x ξk = S.G x ξk := by
  rfl

/-- Assumption 16(a) at paper time `k`, stated for the canonical distribution `P_k`. -/
theorem oracleMean_eq_grad (S : Setup n Sample) (k : PositiveTime) (x : Space n) :
    expectationEq (S.sampleLaw k : Measure Sample) (fun s => S.G x s) (gradΨ S x) := by
  simpa [gradΨ] using S.hOracleUnbiased k x

/-- Assumption 16(b) at paper time `k`, stated for the canonical distribution `P_k`. -/
theorem oracleVariance_le (S : Setup n Sample) (k : PositiveTime) (x : Space n) :
    expectationLe (S.sampleLaw k : Measure Sample)
      (fun s => (‖S.G x s - gradΨ S x‖ ^ 2 : ℝ)) (S.σ ^ 2) := by
  simpa [gradΨ] using S.hOracleVariance k x

/-- The staged sampled stochastic gradient value `G(x, ξ_k)` along a sample stream. -/
def sampledOracleAt
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) (x : Space n) : Space n :=
  sampledOracle S x (sampleAt ξ k)

@[simp]
theorem sampledOracleAt_eq
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) (x : Space n) :
    sampledOracleAt S ξ k x = S.G x (ξ k.1) := by
  rfl


/-- Proof-local stochastic error `δ_k = G(underline x_k, ξ_k) - ∇Ψ(underline x_k)`. -/
def oracleError (S : Setup n Sample) (x : Space n) (ξk : Sample) : Space n :=
  SOptLib.oracleEstimatorError (gradΨ S) (S.G x ξk) x

@[simp]
theorem oracleError_eq (S : Setup n Sample) (x : Space n) (ξk : Sample) :
    oracleError S x ξk = S.G x ξk - gradΨ S x := by
  rfl

/-- Oracle noise evaluated at a time-indexed random query and the matching sample coordinate. -/
def oracleErrorAtQuery
    (S : Setup n Sample) (query : PositiveTime → (ℕ → Sample) → Space n)
    (k : PositiveTime) : (ℕ → Sample) → Space n :=
  SOptLib.oracleNoiseAtAdaptedQuery (fun x ξk => SOptLib.oracleEstimatorError (gradΨ S) (S.G x ξk) x) query
    (fun (j : PositiveTime) (ξ : ℕ → Sample) => sampleAt ξ j) id k

/-- Proof-local stochastic error along the process,
`δ_k = G(x, ξ_k) - ∇Ψ(x)`, as a specialization of the adapted-query oracle-noise
primitive. -/
def oracleErrorAt
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) (x : Space n) : Space n :=
  oracleErrorAtQuery S (fun _ _ => x) k ξ

@[simp]
theorem oracleErrorAt_eq
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) (x : Space n) :
    oracleErrorAt S ξ k x = S.G x (ξ k.1) - gradΨ S x := by
  rfl

/-- Proof-local gradient difference `Δ_k = ∇Ψ(x_{k-1}) - ∇Ψ(underline x_k)`. -/
def gradientDifference (S : Setup n Sample) (xPrev xUnder : Space n) : Space n :=
  gradΨ S xPrev - gradΨ S xUnder

@[simp]
theorem gradientDifference_eq (S : Setup n Sample) (xPrev xUnder : Space n) :
    gradientDifference S xPrev xUnder = gradΨ S xPrev - gradΨ S xUnder := by
  rfl

/-- Algorithm 6.4 search point `(1 - α_k) bar x_{k-1} + α_k x_{k-1}`. -/
def searchPoint
    (S : Setup n Sample) (k : PositiveTime) (xBarPrev xPrev : Space n) : Space n :=
  acceleratedSearchPoint S.alpha k xBarPrev xPrev

@[simp]
theorem searchPoint_eq
    (S : Setup n Sample) (k : PositiveTime) (xBarPrev xPrev : Space n) :
    searchPoint S k xBarPrev xPrev =
      (1 - S.alpha k.1) • xBarPrev + S.alpha k.1 • xPrev := by
  rfl

/-- The two iterates stored after a completed Algorithm 6.4 step. -/
abbrev State (n : ℕ) := SOptLib.AcceleratedGradientState (Space n)

/-- Algorithm 6.4 initialization `bar x₀ = x₀`. -/
def initialState (S : Setup n Sample) : State n :=
  SOptLib.acceleratedGradientInitialState S.x0

/-- One printed Algorithm 6.4 step at positive paper time `k`, reading `ξ_k` from the process. -/
def stepStateAt
    (S : Setup n Sample) (k : PositiveTime) (st : State n) (ξ : ℕ → Sample) : State n :=
  SOptLib.acceleratedGradientStepStateAt S.alpha S.beta S.lam S.G
    (fun j η => sampleAt η j) k st ξ

/-- The pathwise state generated after `t` completed iterations from a sample stream.

`stateAfter S ξ 0` is `(x₀, bar x₀)`, and `stateAfter S ξ (k+1)` performs the
paper step with index `k+1` and sample `ξ (k+1)`. -/
def stateAfter (S : Setup n Sample) (ξ : ℕ → Sample) : ℕ → State n
  | k =>
      SOptLib.acceleratedGradientState S.alpha S.beta S.lam S.G S.x0
        (fun j η => sampleAt η j) k ξ

/-- Generated raw iterate `x_k`. -/
def x (S : Setup n Sample) (ξ : ℕ → Sample) (k : ℕ) : Space n :=
  SOptLib.acceleratedGradientX S.alpha S.beta S.lam S.G S.x0
    (fun j η => sampleAt η j) ξ k

/-- Generated averaged iterate `bar x_k`. -/
def xBar (S : Setup n Sample) (ξ : ℕ → Sample) (k : ℕ) : Space n :=
  SOptLib.acceleratedGradientXBar S.alpha S.beta S.lam S.G S.x0
    (fun j η => sampleAt η j) ξ k

/-- Generated search point `underline x_k` for positive paper time. -/
def xUnder (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) : Space n :=
  SOptLib.acceleratedGradientXUnder S.alpha S.beta S.lam S.G S.x0
    (fun j η => sampleAt η j) ξ k

/-- The finite prefix `ξ_[N] = (ξ_1, ..., ξ_N)` appearing in Theorem 6.12. -/
abbrev SamplePrefix (N : ℕ) := OutputTime N → Sample

/-- Project a full sample stream to the finite prefix used by the theorem. -/
def samplePrefix {N : ℕ} (ξ : ℕ → Sample) : SamplePrefix (Sample := Sample) N :=
  fun k => ξ k.1

/-- The finite-prefix projection is measurable coordinatewise. -/
private theorem samplePrefix_measurable (N : ℕ) :
    Measurable (samplePrefix (Sample := Sample) (N := N)) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply k.1

/-- The law of the finite prefix `ξ_[N]`, induced by the paper sample process. -/
def samplePrefixLaw (S : Setup n Sample) (N : ℕ) : Measure (SamplePrefix (Sample := Sample) N) :=
  Measure.map (samplePrefix (Sample := Sample) (N := N))
    (S.sampleStreamLaw : Measure (ℕ → Sample))

/-- Generated state from a finite prefix.  It is intentionally constant after `N`;
all paper-facing output times are in `{1, ..., N}`. -/
def stateAfterPrefix (S : Setup n Sample) (N : ℕ)
    (ξ : SamplePrefix (Sample := Sample) N) : ℕ → State n
  | 0 => initialState S
  | k + 1 =>
      if hk : k + 1 ≤ N then
        SOptLib.acceleratedGradientStepState S.alpha S.beta S.lam S.G
          ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
          (stateAfterPrefix S N ξ k)
          (ξ ⟨k + 1, Finset.mem_Icc.mpr
            ⟨Nat.succ_le_succ (Nat.zero_le k), hk⟩⟩)
      else
        stateAfterPrefix S N ξ k

/-- Generated raw iterate from the finite theorem prefix. -/
def xPrefix (S : Setup n Sample) (N : ℕ)
    (ξ : SamplePrefix (Sample := Sample) N) (k : ℕ) : Space n :=
  (stateAfterPrefix S N ξ k).x

/-- Generated averaged iterate from the finite theorem prefix. -/
def xBarPrefix (S : Setup n Sample) (N : ℕ)
    (ξ : SamplePrefix (Sample := Sample) N) (k : ℕ) : Space n :=
  (stateAfterPrefix S N ξ k).xBar

/-- Generated search point from the finite theorem prefix. -/
def xUnderPrefix (S : Setup n Sample) (N : ℕ)
    (ξ : SamplePrefix (Sample := Sample) N) (k : OutputTime N) : Space n :=
  searchPoint S (outputTimePositive k) (xBarPrefix S N ξ (k.1 - 1))
    (xPrefix S N ξ (k.1 - 1))

/-- A finite prefix obtained from a full stream generates the same states through its horizon. -/
private theorem stateAfterPrefix_samplePrefix_eq_stateAfter_of_le
    (S : Setup n Sample) (N : ℕ) (ξfull : ℕ → Sample) (t : ℕ) (ht : t ≤ N) :
    stateAfterPrefix S N (samplePrefix (Sample := Sample) (N := N) ξfull) t =
      stateAfter S ξfull t := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      unfold stateAfterPrefix stateAfter
      simp [ht, ih (Nat.le_of_succ_le ht), stateAfter, sampleAt,
        samplePrefix,
        SOptLib.acceleratedGradientState, SOptLib.acceleratedGradientStepStateAt,
        SOptLib.acceleratedGradientStepState]

/-- Prefix and stream generated iterates agree on the finite theorem window. -/
theorem xUnderPrefix_eq_stream_of_same_prefix
    (S : Setup n Sample) (N : ℕ) (ξfull : ℕ → Sample) (k : OutputTime N) :
    xUnderPrefix S N (samplePrefix (Sample := Sample) (N := N) ξfull) k =
      xUnder S ξfull (outputTimePositive k) := by
  have hpred : k.1 - 1 ≤ N := Nat.le_trans (Nat.sub_le k.1 1) (Finset.mem_Icc.mp k.2).2
  simp [xUnderPrefix, xUnder, xPrefix, xBarPrefix, x, xBar, stateAfter, searchPoint,
    SOptLib.acceleratedGradientXUnder, SOptLib.acceleratedGradientX,
    SOptLib.acceleratedGradientXBar, outputTimePositive,
    stateAfterPrefix_samplePrefix_eq_stateAfter_of_le S N ξfull (k.1 - 1) hpred]

/-- Prefix and stream averaged iterates agree through the finite theorem window. -/
private theorem xBarPrefix_eq_stream_of_same_prefix
    (S : Setup n Sample) (N : ℕ) (ξfull : ℕ → Sample) (t : ℕ) (ht : t ≤ N) :
    xBarPrefix S N (samplePrefix (Sample := Sample) (N := N) ξfull) t =
      xBar S ξfull t := by
  simp [xBarPrefix, xBar, stateAfter, SOptLib.acceleratedGradientXBar,
    stateAfterPrefix_samplePrefix_eq_stateAfter_of_le S N ξfull t ht]

@[simp]
theorem x_zero (S : Setup n Sample) (ξ : ℕ → Sample) :
    x S ξ 0 = S.x0 := by
  rfl

@[simp]
theorem xBar_zero (S : Setup n Sample) (ξ : ℕ → Sample) :
    xBar S ξ 0 = S.x0 := by
  rfl

@[simp]
theorem xUnder_eq_searchPoint
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    xUnder S ξ k = searchPoint S k (xBar S ξ (k.1 - 1)) (x S ξ (k.1 - 1)) := by
  rfl

/-- The generated proof-local noise process
`δ_k = G(underline x_k, ξ_k) - ∇Ψ(underline x_k)`. -/
def generatedOracleErrorAt (S : Setup n Sample) (k : PositiveTime) :
    (ℕ → Sample) → Space n :=
  oracleErrorAtQuery S (fun t ξ => xUnder S ξ t) k

@[simp]
theorem generatedOracleErrorAt_eq
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    generatedOracleErrorAt S k ξ = S.G (xUnder S ξ k) (ξ k.1) - gradΨ S (xUnder S ξ k) := by
  rfl

/-- Squared norm of the generated proof-local noise
`δ_k = G(underline x_k, ξ_k) - ∇Ψ(underline x_k)`. -/
def generatedOracleErrorNormSq (S : Setup n Sample) (k : PositiveTime) :
    (ℕ → Sample) → ℝ :=
  fun ξ => ‖generatedOracleErrorAt S k ξ‖ ^ 2

@[simp]
theorem generatedOracleErrorNormSq_eq
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    generatedOracleErrorNormSq S k ξ =
      ‖S.G (xUnder S ξ k) (ξ k.1) - gradΨ S (xUnder S ξ k)‖ ^ 2 := by
  rfl

/-- Adaptive conditional mean-zero obligation for the generated oracle noise. -/
def AdaptiveOracleMeanZero (S : Setup n Sample) : Prop :=
  ∀ k : PositiveTime,
    SOptLib.ConditionalExpectation.conditionalExpectationEq
      (S.sampleStreamLaw : Measure (ℕ → Sample))
      ((sampleFiltration (Sample := Sample)).seq k.1)
      (generatedOracleErrorAt S k)
      (0 : (ℕ → Sample) → Space n)

/-- Adaptive second-moment obligation for the generated oracle noise. -/
def AdaptiveOracleSecondMoment (S : Setup n Sample) : Prop :=
  ∀ k : PositiveTime,
    expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
      (generatedOracleErrorNormSq S k) (S.σ ^ 2)

/-- Observability obligation for the generated oracle noise with respect to the
sample-prefix filtration that contains the matching coordinate. -/
def AdaptiveOracleGeneratedObservable (S : Setup n Sample) : Prop :=
  ∀ k : PositiveTime,
    Measurable[((sampleFiltration (Sample := Sample)).seq (k.1 + 1))]
      (generatedOracleErrorAt S k)

/-- Adaptive process boundary used by the proof of Theorem 6.12.

The book states fixed-query SFO moment assumptions and explicitly says that
independence of the sample coordinates is not required. The proof later uses
`v_k` being measurable with respect to the strict past, together with
`E[δ_k | ξ_[k-1]] = 0` and `E‖δ_k‖² ≤ σ²` at the generated adaptive search
point. This predicate records that process-level proof boundary without
pretending it follows from coordinate marginals alone.

Source boundary: `book/FOML/NonconvexStochasticAcceleratedGD.json#/assumptions[3]`
and `#/assumptions[4]` state the fixed-query oracle moments; the FOML PDF,
Section 6.4.2.1, says independence is not required; the proof of Theorem 6.12
uses the generated-query facts `v_k` is `ξ_[k-1]`-measurable,
`E[δ_k | ξ_[k-1]] = 0`, and `E‖δ_k‖² ≤ σ²`. -/
def AdaptiveOracleProcess (S : Setup n Sample) : Prop :=
  AdaptiveCenteredOracleProcess
    (S.sampleStreamLaw : Measure (ℕ → Sample))
    (fun k : PositiveTime => (sampleFiltration (Sample := Sample)).seq k.1)
    (fun k : PositiveTime => (sampleFiltration (Sample := Sample)).seq (k.1 + 1))
    (generatedOracleErrorAt S)
    (fun _ : PositiveTime => S.σ ^ 2)

/-- Projection of the adaptive-oracle process boundary at a fixed paper time. -/
theorem oracleErrorAt_condExp_past_eq_zero_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) (k : PositiveTime) :
    SOptLib.ConditionalExpectation.conditionalExpectationEq
      (S.sampleStreamLaw : Measure (ℕ → Sample))
      ((sampleFiltration (Sample := Sample)).seq k.1)
      (generatedOracleErrorAt S k)
      (0 : (ℕ → Sample) → Space n) :=
  hAdaptive.1 k

/-- Projection of the adaptive second-moment boundary at a fixed paper time. -/
theorem oracleErrorAt_secondMoment_le_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) (k : PositiveTime) :
    expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
      (generatedOracleErrorNormSq S k) (S.σ ^ 2) :=
  hAdaptive.2.1 k

/-- Projection of the generated-oracle-error observability boundary at a fixed
paper time. -/
theorem oracleErrorAt_observable_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) (k : PositiveTime) :
    Measurable[((sampleFiltration (Sample := Sample)).seq (k.1 + 1))]
      (generatedOracleErrorAt S k) :=
  hAdaptive.2.2 k

/-- First update identity in Algorithm 6.4, Eq. (6.4.8). -/
theorem xUnder_update_identity
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    xUnder S ξ k =
      (1 - S.alpha k.1) • xBar S ξ (k.1 - 1) + S.alpha k.1 • x S ξ (k.1 - 1) := by
  rfl

/-- Second update identity in Algorithm 6.4, Eq. (6.4.64). -/
theorem x_update_identity
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : ℕ) :
    x S ξ (k + 1) =
      x S ξ k -
        S.lam (k + 1) • sampledOracleAt S ξ
          ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
          (xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩)
          := by
  rfl

/-- Third update identity in Algorithm 6.4, Eq. (6.4.65). -/
theorem xBar_update_identity
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : ℕ) :
    xBar S ξ (k + 1) =
      xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ -
        S.beta (k + 1) • sampledOracleAt S ξ
          ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
          (xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩)
          := by
  rfl

/-- Lipschitz continuity of the generated gradient field, packaged in Mathlib's
metric Lipschitz interface. -/
private theorem gradΨ_lipschitzWith (S : Setup n Sample) :
    LipschitzWith (Real.toNNReal S.LΨ) (gradΨ S) := by
  refine lipschitzWith_of_norm_sub_le_mul (gradΨ S) S.LΨ ?_
  intro x y
  simpa [gradΨ, dist_eq_norm] using S.hLipschitzGrad y x

/-- Measurability of the generated gradient field, derived from the paper's
Lipschitz-gradient assumption. -/
private theorem gradΨ_measurable (S : Setup n Sample) :
    Measurable (gradΨ S) :=
  (gradΨ_lipschitzWith S).continuous.measurable

/-- Stochastic raw-iterate update rewritten through the generated centered error. -/
private theorem x_update_identity_grad_error
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : ℕ) :
    x S ξ (k + 1) =
      x S ξ k -
        S.lam (k + 1) •
          (gradΨ S (xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩) +
            generatedOracleErrorAt S
              ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ ξ) := by
  rw [x_update_identity]
  simp [sampledOracleAt_eq, generatedOracleErrorAt_eq, sub_eq_add_neg,
    add_comm]

/-- Stochastic averaged-iterate update rewritten through the generated centered error. -/
private theorem xBar_update_identity_grad_error
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : ℕ) :
    xBar S ξ (k + 1) =
      xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ -
        S.beta (k + 1) •
          (gradΨ S (xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩) +
            generatedOracleErrorAt S
              ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ ξ) := by
  rw [xBar_update_identity]
  simp [sampledOracleAt_eq, generatedOracleErrorAt_eq, sub_eq_add_neg,
    add_comm]

/-- The generated search point is strict-past measurable when the previous
generated iterates are strict-past measurable. -/
private theorem xUnder_measurable_of_prev_measurable
    (S : Setup n Sample) (k : PositiveTime)
    (hx :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)))
    (hxBar :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1))) :
    Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
      (fun ξ : ℕ → Sample => xUnder S ξ k) := by
  simpa [xUnder, searchPoint_eq] using
    (hxBar.const_smul (1 - S.alpha k.1)).add (hx.const_smul (S.alpha k.1))

/-- Generated iterates are adapted to the sample prefix once the generated
centered oracle errors are observable at their matching prefixes. -/
private theorem generated_state_adapted_from_error_observable
    (S : Setup n Sample) (hObs : AdaptiveOracleGeneratedObservable S) :
    ∀ t : ℕ,
      Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
          (fun ξ : ℕ → Sample => x S ξ t) ∧
        Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
          (fun ξ : ℕ → Sample => xBar S ξ t)
    := by
  exact SOptLib.accelerated_two_state_adapted_of_observable_error
    (filt := sampleFiltration (Sample := Sample))
    (x := fun t ξ => x S ξ t)
    (xBar := fun t ξ => xBar S ξ t)
    (xUnder := fun k ξ =>
      match k with
      | 0 => xUnder S ξ ⟨1, le_rfl⟩
      | k + 1 => xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩)
    (err := fun k ξ =>
      match k with
      | 0 => x S ξ 0
      | k + 1 =>
          generatedOracleErrorAt S
            ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ ξ)
    (target := gradΨ S)
    (alpha := S.alpha) (beta := S.beta) (lam := S.lam)
    (gradΨ_measurable S)
    (by exact measurable_const)
    (by exact measurable_const)
    (by
      intro t
      simpa only [Nat.add_succ, Nat.add_zero] using
        hObs ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩)
    (by
      intro t
      funext ξ
      simp [xUnder_eq_searchPoint, searchPoint_eq])
    (by
      intro t
      funext ξ
      simpa using x_update_identity_grad_error S ξ t)
    (by
      intro t
      funext ξ
      simpa using xBar_update_identity_grad_error S ξ t)

/-- A Lipschitz gradient maps centered square-integrable random points to
square-integrable gradients. -/
private theorem grad_sq_integrable_of_centered_l2
    (S : Setup n Sample) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (z : Ω → Space n)
    (hz_meas : AEStronglyMeasurable z μ)
    (hz_sq : Integrable (fun ω => ‖S.x0 - z ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖gradΨ S (z ω)‖ ^ 2) μ := by
  exact SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
    (base := S.x0) (grad := gradΨ S) (L := S.LΨ) (z := z)
    hz_meas hz_sq S.hLipschitzGrad

/-- A smooth objective with Lipschitz gradient is integrable along any
centered square-integrable random point. -/
private theorem smooth_value_integrable_of_centered_l2
    (S : Setup n Sample) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (z : Ω → Space n)
    (hz_meas : AEStronglyMeasurable z μ)
    (hz_sq : Integrable (fun ω => ‖S.x0 - z ω‖ ^ 2) μ) :
    Integrable (fun ω => S.Ψ (z ω)) μ := by
  exact SOptLib.integrable_smooth_value_of_centered_l2
    (f := S.Ψ) (g := gradΨ S S.x0) (base := S.x0) (L := S.LΨ) (z := z)
    hz_meas (S.hDifferentiable.continuous.comp_aestronglyMeasurable hz_meas) hz_sq
    (by
      filter_upwards with ω
      exact smoothUpper S S.x0 (z ω))

/-- The adaptive second-moment boundary gives square-integrability of each
generated oracle error. -/
private theorem generated_oracle_error_sq_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) (k : PositiveTime) :
    Integrable (fun ξ : ℕ → Sample => ‖generatedOracleErrorAt S k ξ‖ ^ 2)
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hExp :
      expectationLe μ (generatedOracleErrorNormSq S k) (S.σ ^ 2) := by
    simpa [μ] using oracleErrorAt_secondMoment_le_of_adaptiveOracleProcess S hAdaptive k
  have hpair := (SOptLib.expectationLe_def μ (generatedOracleErrorNormSq S k)
    (S.σ ^ 2)).1 hExp
  simpa [generatedOracleErrorNormSq, μ] using hpair.1

/-- Generated raw and averaged iterates remain square-integrable around the
initial point under the adaptive oracle-process boundary. -/
private theorem generated_state_l2_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) :
    ∀ t : ℕ,
      Integrable (fun ξ : ℕ → Sample => ‖S.x0 - x S ξ t‖ ^ 2)
          (S.sampleStreamLaw : Measure (ℕ → Sample)) ∧
        Integrable (fun ξ : ℕ → Sample => ‖S.x0 - xBar S ξ t‖ ^ 2)
          (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let xUnderSeq : ℕ → (ℕ → Sample) → Space n :=
    fun k ξ =>
      match k with
      | 0 => S.x0
      | k + 1 => xUnder S ξ ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
  let errSeq : ℕ → (ℕ → Sample) → Space n :=
    fun k ξ =>
      match k with
      | 0 => 0
      | k + 1 =>
          generatedOracleErrorAt S
            ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ ξ
  have hstate_meas :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
  exact
    SOptLib.accelerated_two_state_l2_of_oracle_error_l2
      (P := μ) (base := S.x0)
      (x := fun t ξ => x S ξ t)
      (xBar := fun t ξ => xBar S ξ t)
      (xUnder := xUnderSeq)
      (err := errSeq)
      (grad := gradΨ S)
      (alpha := S.alpha) (beta := S.beta) (lam := S.lam)
      (by
        intro t
        exact
          ((hstate_meas t).1.mono
            ((sampleFiltration (Sample := Sample)).le (t + 1)) le_rfl).aestronglyMeasurable)
      (by
        intro t
        exact
          ((hstate_meas t).2.mono
            ((sampleFiltration (Sample := Sample)).le (t + 1)) le_rfl).aestronglyMeasurable)
      (by
        intro k
        cases k with
        | zero =>
            simpa [xUnderSeq] using
              (aestronglyMeasurable_const :
                AEStronglyMeasurable (fun _ : ℕ → Sample => gradΨ S S.x0) μ)
        | succ t =>
            let kp : PositiveTime := ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩
            have hx_meas_sub :
                Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
                  (fun ξ : ℕ → Sample => x S ξ t) :=
              (hstate_meas t).1
            have hxBar_meas_sub :
                Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
                  (fun ξ : ℕ → Sample => xBar S ξ t) :=
              (hstate_meas t).2
            have hxUnder_meas_sub :
                Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
                  (fun ξ : ℕ → Sample => xUnder S ξ kp) := by
              simpa [kp] using xUnder_measurable_of_prev_measurable S kp
                hx_meas_sub hxBar_meas_sub
            have hxUnder_meas :
                Measurable (fun ξ : ℕ → Sample => xUnder S ξ kp) :=
              hxUnder_meas_sub.mono ((sampleFiltration (Sample := Sample)).le (t + 1))
                le_rfl
            exact
              (by
                simpa [xUnderSeq, kp] using
                  ((gradΨ_measurable S).comp hxUnder_meas).aestronglyMeasurable))
      (by
        intro k
        cases k with
        | zero =>
            simpa [errSeq] using
              (aestronglyMeasurable_const :
                AEStronglyMeasurable (fun _ : ℕ → Sample => (0 : Space n)) μ)
        | succ t =>
            let kp : PositiveTime := ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩
            have hδ_meas_sub :
                Measurable[((sampleFiltration (Sample := Sample)).seq ((t + 1) + 1))]
                  (fun ξ : ℕ → Sample => generatedOracleErrorAt S kp ξ) := by
              simpa [kp] using oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive kp
            exact
              (by
                simpa [errSeq, kp] using
                  (hδ_meas_sub.mono
                    ((sampleFiltration (Sample := Sample)).le ((t + 1) + 1)) le_rfl
                  ).aestronglyMeasurable))
      (by
        intro k hk
        cases k with
        | zero =>
            simp [xUnderSeq]
        | succ t =>
            let kp : PositiveTime := ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩
            have hx_meas_sub :
                Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
                  (fun ξ : ℕ → Sample => x S ξ t) :=
              (hstate_meas t).1
            have hxBar_meas_sub :
                Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
                  (fun ξ : ℕ → Sample => xBar S ξ t) :=
              (hstate_meas t).2
            have hxUnder_meas_sub :
                Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
                  (fun ξ : ℕ → Sample => xUnder S ξ kp) := by
              simpa [kp] using xUnder_measurable_of_prev_measurable S kp
                hx_meas_sub hxBar_meas_sub
            have hxUnder_meas :
                Measurable (fun ξ : ℕ → Sample => xUnder S ξ kp) :=
              hxUnder_meas_sub.mono ((sampleFiltration (Sample := Sample)).le (t + 1))
                le_rfl
            exact
              grad_sq_integrable_of_centered_l2 S
                (fun ξ : ℕ → Sample => xUnder S ξ kp)
                hxUnder_meas.aestronglyMeasurable
                (by simpa [xUnderSeq, kp] using hk))
      (by
        intro k
        cases k with
        | zero =>
            simp [errSeq]
        | succ t =>
            let kp : PositiveTime := ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩
            simpa [μ, errSeq, kp] using
              generated_oracle_error_sq_integrable_of_adaptiveOracleProcess S
                hAdaptive kp)
      (by
        filter_upwards with ξ
        simp)
      (by
        filter_upwards with ξ
        simp)
      (by
        intro t
        filter_upwards with ξ
        simp [xUnderSeq])
      (by
        intro t
        filter_upwards with ξ
        simp [xUnderSeq, errSeq, x_update_identity_grad_error])
      (by
        intro t
        filter_upwards with ξ
        simp [xUnderSeq, errSeq, xBar_update_identity_grad_error])

/-- Generated raw gradients are square-integrable under the adaptive oracle process. -/
private theorem generated_raw_gradient_sq_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) (t : ℕ) :
    Integrable (fun ξ : ℕ → Sample => ‖gradΨ S (x S ξ t)‖ ^ 2)
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hstate_meas :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
  have hx_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
        (fun ξ : ℕ → Sample => x S ξ t) :=
    (hstate_meas t).1
  have hx_meas : Measurable (fun ξ : ℕ → Sample => x S ξ t) :=
    hx_meas_sub.mono ((sampleFiltration (Sample := Sample)).le (t + 1)) le_rfl
  exact grad_sq_integrable_of_centered_l2 S (fun ξ : ℕ → Sample => x S ξ t)
    hx_meas.aestronglyMeasurable
    (by simpa [μ] using (generated_state_l2_of_adaptiveOracleProcess S hAdaptive t).1)

/-- Generated averaged-iterate function gaps are integrable under the adaptive
oracle-process boundary. -/
private theorem generated_xBar_function_gap_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S)
    (xStar : Space n) (t : ℕ) :
    Integrable (fun ξ : ℕ → Sample => S.Ψ (xBar S ξ t) - S.Ψ xStar)
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hstate_meas :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
  have hxBar_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq (t + 1))]
        (fun ξ : ℕ → Sample => xBar S ξ t) :=
    (hstate_meas t).2
  have hxBar_meas : Measurable (fun ξ : ℕ → Sample => xBar S ξ t) :=
    hxBar_meas_sub.mono ((sampleFiltration (Sample := Sample)).le (t + 1)) le_rfl
  have hvalue_int :
      Integrable (fun ξ : ℕ → Sample => S.Ψ (xBar S ξ t)) μ :=
    smooth_value_integrable_of_centered_l2 S
      (fun ξ : ℕ → Sample => xBar S ξ t)
      hxBar_meas.aestronglyMeasurable
      (by simpa [μ] using (generated_state_l2_of_adaptiveOracleProcess S hAdaptive t).2)
  simpa [μ] using hvalue_int.sub (integrable_const (S.Ψ xStar))

/-- Generated search gradients are square-integrable under the adaptive oracle process. -/
private theorem generated_search_gradient_sq_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) (k : PositiveTime) :
    Integrable (fun ξ : ℕ → Sample => ‖gradΨ S (xUnder S ξ k)‖ ^ 2)
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hstate_meas :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
  have hstate_l2 := generated_state_l2_of_adaptiveOracleProcess S hAdaptive (k.1 - 1)
  have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel k.2
  have hx_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) := by
    have h := (hstate_meas (k.1 - 1)).1
    rw [hidx] at h
    exact h
  have hxBar_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1)) := by
    have h := (hstate_meas (k.1 - 1)).2
    rw [hidx] at h
    exact h
  have hx_prev_meas : Measurable (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) :=
    hx_prev_sub.mono ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hxBar_prev_meas : Measurable (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1)) :=
    hxBar_prev_sub.mono ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hxUnder_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xUnder S ξ k) :=
    xUnder_measurable_of_prev_measurable S k hx_prev_sub hxBar_prev_sub
  have hxUnder_meas : Measurable (fun ξ : ℕ → Sample => xUnder S ξ k) :=
    hxUnder_meas_sub.mono ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hxUnder_sq :
      Integrable (fun ξ : ℕ → Sample => ‖S.x0 - xUnder S ξ k‖ ^ 2) μ := by
    have hraw :=
      SOptLib.integrable_sq_norm_const_sub_two_stage_affine
        (μ := μ) S.x0
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1))
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1))
        (S.alpha k.1) 1 0
        hx_prev_meas.aestronglyMeasurable hxBar_prev_meas.aestronglyMeasurable
        (by simpa [μ] using hstate_l2.1) (by simpa [μ] using hstate_l2.2)
        (by ring)
    simpa [xUnder_update_identity] using hraw
  exact grad_sq_integrable_of_centered_l2 S (fun ξ : ℕ → Sample => xUnder S ξ k)
    hxUnder_meas.aestronglyMeasurable hxUnder_sq

/-- Generated search-gradient norm squares are measurable under the adaptive
oracle-process boundary. -/
private theorem generated_search_gradient_norm_sq_measurable_of_adaptiveOracleProcess
    (S : Setup n Sample) (hAdaptive : AdaptiveOracleProcess S) (k : PositiveTime) :
    Measurable (fun ξ : ℕ → Sample => ‖gradΨ S (xUnder S ξ k)‖ ^ 2) := by
  have hstate_meas :=
    generated_state_adapted_from_error_observable S hAdaptive.2.2
  have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel k.2
  have hx_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) := by
    have h := (hstate_meas (k.1 - 1)).1
    rw [hidx] at h
    exact h
  have hxBar_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1)) := by
    have h := (hstate_meas (k.1 - 1)).2
    rw [hidx] at h
    exact h
  have hxUnder_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xUnder S ξ k) :=
    xUnder_measurable_of_prev_measurable S k hx_prev_sub hxBar_prev_sub
  have hxUnder_meas : Measurable (fun ξ : ℕ → Sample => xUnder S ξ k) :=
    hxUnder_meas_sub.mono ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  exact (((gradΨ_measurable S).comp hxUnder_meas).norm.pow_const 2)

/-- Subtracting the two Algorithm 6.4 stochastic updates gives the source
acceleration-gap recursion. -/
private theorem xBar_sub_x_recursion
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    xBar S ξ k.1 - x S ξ k.1 =
      (1 - S.alpha k.1) • (xBar S ξ (k.1 - 1) - x S ξ (k.1 - 1)) +
        (S.lam k.1 - S.beta k.1) •
          (gradΨ S (xUnder S ξ k) + generatedOracleErrorAt S k ξ) := by
  have hk_eq : k.1 = k.1 - 1 + 1 := (Nat.sub_add_cancel k.2).symm
  have hidx :
      (⟨k.1 - 1 + 1, Nat.succ_le_succ (Nat.zero_le (k.1 - 1))⟩ :
        PositiveTime) = k := by
    ext
    exact Nat.sub_add_cancel k.2
  rw [hk_eq, xBar_update_identity, x_update_identity]
  rw [hidx]
  rw [xUnder_update_identity]
  simp [sampledOracleAt_eq, generatedOracleErrorAt_eq, sub_eq_add_neg,
    Nat.sub_add_cancel k.2]
  module

/-- The acceleration-gap recursion summed after division by `Γ`.  This is the
vector identity underlying the source Jensen step. -/
private theorem xBar_sub_x_eq_Gamma_weighted_sum
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    xBar S ξ k.1 - x S ξ k.1 =
      Γ S k •
        Finset.sum (Finset.Icc 1 k.1) (fun τ =>
          if hτ : 1 ≤ τ then
            ((S.lam τ - S.beta τ) / Γ S ⟨τ, hτ⟩) •
              (gradΨ S (xUnder S ξ ⟨τ, hτ⟩) +
                generatedOracleErrorAt S ⟨τ, hτ⟩ ξ)
          else 0) := by
  classical
  let term : ℕ → Space n := fun τ =>
    if hτ : 1 ≤ τ then
      ((S.lam τ - S.beta τ) / Γ S ⟨τ, hτ⟩) •
        (gradΨ S (xUnder S ξ ⟨τ, hτ⟩) +
          generatedOracleErrorAt S ⟨τ, hτ⟩ ξ)
    else 0
  have hmain :
      ∀ m (hm : 1 ≤ m),
        xBar S ξ m - x S ξ m =
          Γ S ⟨m, hm⟩ • Finset.sum (Finset.Icc 1 m) term := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
        by_cases hm_zero : m = 0
        · subst m
          have hrec := xBar_sub_x_recursion S ξ ⟨1, le_rfl⟩
          have hsum :
              Finset.sum (Finset.Icc 1 1) term =
                ((S.lam 1 - S.beta 1) / Γ S ⟨1, le_rfl⟩) •
                  (gradΨ S (xUnder S ξ ⟨1, le_rfl⟩) +
                    generatedOracleErrorAt S ⟨1, le_rfl⟩ ξ) := by
            simp [term]
          rw [hrec, hsum]
          simp
        · have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm_zero
          have hrec := xBar_sub_x_recursion S ξ
            ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩
          have hih := ih hm_pos
          have hsum_top :
              Finset.sum (Finset.Icc 1 (m + 1)) term =
                Finset.sum (Finset.Icc 1 m) term + term (m + 1) := by
            rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
          have hΓ_succ := Γ_succ S m hm_pos
          have hΓ_ne :
              Γ S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩ ≠ 0 :=
            ne_of_gt (Γ_pos S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩)
          simp [Nat.succ_sub_one] at hrec
          have htop_smul :
              Γ S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩ • term (m + 1) =
                (S.lam (m + 1) - S.beta (m + 1)) •
                  S.G ((1 - S.alpha (m + 1)) • xBar S ξ m +
                    S.alpha (m + 1) • x S ξ m) (ξ (m + 1)) := by
            have hscalar :
                Γ S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩ *
                    ((S.lam (m + 1) - S.beta (m + 1)) /
                      Γ S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩) =
                  S.lam (m + 1) - S.beta (m + 1) := by
              field_simp [hΓ_ne]
            simp [term, hΓ_ne, hscalar, smul_smul, xUnder_update_identity,
              generatedOracleErrorAt_eq]
          rw [hrec, hih]
          calc
                (1 - S.alpha (m + 1)) •
                  (Γ S ⟨m, hm_pos⟩ • Finset.sum (Finset.Icc 1 m) term) +
                (S.lam (m + 1) - S.beta (m + 1)) •
                  S.G ((1 - S.alpha (m + 1)) • xBar S ξ m +
                    S.alpha (m + 1) • x S ξ m) (ξ (m + 1))
                = Γ S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩ •
                    Finset.sum (Finset.Icc 1 m) term +
                  Γ S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩ • term (m + 1) := by
                    rw [htop_smul, hΓ_succ]
                    module
            _ = Γ S ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m)⟩ •
                  (Finset.sum (Finset.Icc 1 m) term + term (m + 1)) := by
                    rw [smul_add]
            _ = Γ S ⟨m + 1, hm⟩ • Finset.sum (Finset.Icc 1 (m + 1)) term := by
                    rw [hsum_top]
  simpa [term] using hmain k.1 k.2

/-- Fixed-time pathwise descent after the smoothness/update expansion and the
Cauchy bound on the search-gradient difference term. -/
private theorem partA_one_step_descent_raw
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    S.Ψ (x S ξ k.1) ≤
      S.Ψ (x S ξ (k.1 - 1)) -
        S.lam k.1 * (1 - S.LΨ * S.lam k.1 / 2) *
          ‖gradΨ S (xUnder S ξ k)‖ ^ 2 +
        S.lam k.1 *
          ‖gradientDifference S (x S ξ (k.1 - 1)) (xUnder S ξ k)‖ *
            ‖gradΨ S (xUnder S ξ k)‖ +
        (S.LΨ * S.lam k.1 ^ 2 / 2) * ‖generatedOracleErrorAt S k ξ‖ ^ 2 -
        S.lam k.1 *
          inner ℝ
            (gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ k))
            (generatedOracleErrorAt S k ξ) := by
  let xPrev : Space n := x S ξ (k.1 - 1)
  let xNext : Space n := x S ξ k.1
  let gUnder : Space n := gradΨ S (xUnder S ξ k)
  let δ : Space n := generatedOracleErrorAt S k ξ
  let Δ : Space n := gradientDifference S xPrev (xUnder S ξ k)
  have hk_eq : k.1 = k.1 - 1 + 1 := (Nat.sub_add_cancel k.2).symm
  have hx_update :
      xNext = xPrev - S.lam k.1 • (gUnder + δ) := by
    have hidx :
        (⟨k.1 - 1 + 1, Nat.succ_le_succ (Nat.zero_le (k.1 - 1))⟩ : PositiveTime) = k := by
      ext
      exact Nat.sub_add_cancel k.2
    subst xNext
    subst xPrev
    subst gUnder
    subst δ
    rw [hk_eq, x_update_identity]
    rw [hidx]
    simp [sampledOracleAt_eq, generatedOracleErrorAt_eq, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc]
  have hdisp : xNext - xPrev = (-S.lam k.1) • (gUnder + δ) := by
    rw [hx_update]
    simp [sub_eq_add_neg, neg_smul]
    abel
  have hgrad_prev : gradΨ S xPrev = Δ + gUnder := by
    subst Δ
    subst gUnder
    simp [gradientDifference_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hsmooth_abs := smoothUpper S xPrev xNext
  have hsmooth :
      S.Ψ xNext ≤
        S.Ψ xPrev + inner ℝ (gradΨ S xPrev) (xNext - xPrev) +
          (S.LΨ / 2) * ‖xNext - xPrev‖ ^ 2 := by
    have h := (abs_le.mp hsmooth_abs).2
    linarith
  have hnorm_disp :
      ‖xNext - xPrev‖ ^ 2 = S.lam k.1 ^ 2 * ‖gUnder + δ‖ ^ 2 := by
    rw [hdisp, norm_smul, sq]
    have hlam_nonneg : 0 ≤ S.lam k.1 := le_of_lt (S.hlam_pos k.1 k.2)
    rw [Real.norm_of_nonpos (neg_nonpos.mpr hlam_nonneg)]
    ring
  have hinner_bound :
      -inner ℝ Δ gUnder ≤ ‖Δ‖ * ‖gUnder‖ := by
    exact le_trans (neg_le_abs _) (abs_real_inner_le_norm Δ gUnder)
  have hinner_bound_scaled :
      S.lam k.1 * (-inner ℝ Δ gUnder) ≤
        S.lam k.1 * (‖Δ‖ * ‖gUnder‖) := by
    exact mul_le_mul_of_nonneg_left hinner_bound (le_of_lt (S.hlam_pos k.1 k.2))
  have halg :
      S.Ψ xPrev + inner ℝ (gradΨ S xPrev) (xNext - xPrev) +
          (S.LΨ / 2) * ‖xNext - xPrev‖ ^ 2 ≤
        S.Ψ xPrev -
          S.lam k.1 * (1 - S.LΨ * S.lam k.1 / 2) * ‖gUnder‖ ^ 2 +
          S.lam k.1 * ‖Δ‖ * ‖gUnder‖ +
          (S.LΨ * S.lam k.1 ^ 2 / 2) * ‖δ‖ ^ 2 -
          S.lam k.1 *
            inner ℝ
              (gradΨ S xPrev - (S.LΨ * S.lam k.1) • gUnder) δ := by
    rw [hnorm_disp, hdisp, hgrad_prev]
    simp [norm_add_sq_real, inner_add_left, inner_add_right, inner_sub_left,
      inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
    nlinarith [hinner_bound_scaled]
  calc
    S.Ψ (x S ξ k.1) = S.Ψ xNext := by rfl
    _ ≤ S.Ψ xPrev + inner ℝ (gradΨ S xPrev) (xNext - xPrev) +
          (S.LΨ / 2) * ‖xNext - xPrev‖ ^ 2 := hsmooth
    _ ≤ S.Ψ xPrev -
          S.lam k.1 * (1 - S.LΨ * S.lam k.1 / 2) * ‖gUnder‖ ^ 2 +
          S.lam k.1 * ‖Δ‖ * ‖gUnder‖ +
          (S.LΨ * S.lam k.1 ^ 2 / 2) * ‖δ‖ ^ 2 -
          S.lam k.1 *
            inner ℝ
              (gradΨ S xPrev - (S.LΨ * S.lam k.1) • gUnder) δ := halg
    _ = S.Ψ (x S ξ (k.1 - 1)) -
          S.lam k.1 * (1 - S.LΨ * S.lam k.1 / 2) *
            ‖gradΨ S (xUnder S ξ k)‖ ^ 2 +
          S.lam k.1 *
            ‖gradientDifference S (x S ξ (k.1 - 1)) (xUnder S ξ k)‖ *
              ‖gradΨ S (xUnder S ξ k)‖ +
          (S.LΨ * S.lam k.1 ^ 2 / 2) * ‖generatedOracleErrorAt S k ξ‖ ^ 2 -
          S.lam k.1 *
            inner ℝ
              (gradΨ S (x S ξ (k.1 - 1)) -
                (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ k))
              (generatedOracleErrorAt S k ξ) := by
        rfl

/-- The acceleration weight satisfies `α_k ≤ 1` at every positive paper time. -/
private theorem alpha_le_one (S : Setup n Sample) (k : PositiveTime) :
    S.alpha k.1 ≤ 1 := by
  by_cases hk_one : k.1 = 1
  · rw [hk_one, S.halpha_one]
  · have hk_two : 2 ≤ k.1 := by omega
    exact le_of_lt (S.halpha_mem k.1 hk_two).2

/-- The acceleration parameter is positive at every positive paper time. -/
private theorem alpha_pos (S : Setup n Sample) (k : PositiveTime) :
    0 < S.alpha k.1 := by
  rcases lt_or_eq_of_le k.2 with hlt | heq
  · have hk_two : 2 ≤ k.1 := Nat.succ_le_of_lt hlt
    exact (S.halpha_mem k.1 hk_two).1
  · rw [← heq, S.halpha_one]
    norm_num

/-- Convexity linearization at the accelerated search point, Eq. (6.4.26). -/
private theorem partB_convex_search_point_linearization
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (ξ : ℕ → Sample) (k : PositiveTime) (xRef : Space n) :
    S.Ψ (xUnder S ξ k) -
        ((1 - S.alpha k.1) * S.Ψ (xBar S ξ (k.1 - 1)) +
          S.alpha k.1 * S.Ψ xRef) ≤
      S.alpha k.1 *
        inner ℝ (gradΨ S (xUnder S ξ k)) (x S ξ (k.1 - 1) - xRef) := by
  exact convex_accelerated_search_point_linearization
    (X := Set.univ) (f := S.Ψ) (g := gradΨ S (xUnder S ξ k))
    (a := S.alpha k.1) (z := xUnder S ξ k)
    (b := xBar S ξ (k.1 - 1)) (xp := x S ξ (k.1 - 1)) (xRef := xRef)
    hconvex (by simp) (by simp) (by simp)
    (le_of_lt (alpha_pos S k)) (alpha_le_one S k)
    (by
      have hgradAt :
          HasGradientAt S.Ψ (gradΨ S (xUnder S ξ k)) (xUnder S ξ k) := by
        simpa [gradΨ] using (S.hDifferentiable (xUnder S ξ k)).hasGradientAt
      exact (hasGradientWithinAt_univ).2 hgradAt)
    (by simpa using xUnder_update_identity S ξ k)

/-- Euclidean three-point identity for a stochastic-gradient update. -/
private theorem stochastic_three_point_identity_of_update
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (xPrev xNext xRef v : E) (alpha lam : ℝ) (hlam : lam ≠ 0)
    (hupdate : xNext = xPrev - lam • v) :
    alpha * inner ℝ v (xPrev - xRef) =
      alpha / (2 * lam) *
          (‖xPrev - xRef‖ ^ 2 - ‖xNext - xRef‖ ^ 2) +
        alpha * lam / 2 * ‖v‖ ^ 2 :=
  inner_update_eq_sq_dist_sub_sq_dist_add_norm_sq xPrev xNext xRef v alpha lam hlam hupdate

/-- Source steps 12-15 for Theorem 6.12(b): the convex stochastic one-step
recursion before Gamma normalization and martingale cancellation. -/
private theorem partB_one_step_convex_recursion
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (ξ : ℕ → Sample) (k : PositiveTime) (xRef : Space n) :
    S.Ψ (xBar S ξ k.1) - S.Ψ xRef ≤
      (1 - S.alpha k.1) *
          (S.Ψ (xBar S ξ (k.1 - 1)) - S.Ψ xRef) +
        S.alpha k.1 / (2 * S.lam k.1) *
          (‖x S ξ (k.1 - 1) - xRef‖ ^ 2 -
            ‖x S ξ k.1 - xRef‖ ^ 2) -
        S.beta k.1 *
          (1 - S.LΨ * S.beta k.1 / 2 -
            S.alpha k.1 * S.lam k.1 / (2 * S.beta k.1)) *
          ‖gradΨ S (xUnder S ξ k)‖ ^ 2 +
        (S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1) / 2 *
          ‖generatedOracleErrorAt S k ξ‖ ^ 2 +
        inner ℝ (generatedOracleErrorAt S k ξ)
          (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                S.beta k.1) • gradΨ S (xUnder S ξ k)) +
            S.alpha k.1 • (xRef - x S ξ (k.1 - 1))) := by
  exact accelerated_sgd_convex_one_step_recursion
    (f := S.Ψ) (grad := gradΨ S)
    (xPrev := x S ξ (k.1 - 1)) (xNext := x S ξ k.1)
    (bPrev := xBar S ξ (k.1 - 1)) (bNext := xBar S ξ k.1)
    (z := xUnder S ξ k) (xRef := xRef)
    (delta := generatedOracleErrorAt S k ξ)
    (alpha := S.alpha k.1) (beta := S.beta k.1)
    (lam := S.lam k.1) (L := S.LΨ)
    (ne_of_gt (S.hbeta_pos k.1 k.2)) (ne_of_gt (S.hlam_pos k.1 k.2))
    (by
      have hk_eq : k.1 = k.1 - 1 + 1 := (Nat.sub_add_cancel k.2).symm
      have hidx :
          (⟨k.1 - 1 + 1, Nat.succ_le_succ (Nat.zero_le (k.1 - 1))⟩ :
            PositiveTime) = k := by
        ext
        exact Nat.sub_add_cancel k.2
      rw [hk_eq, xBar_update_identity_grad_error]
      rw [hidx])
    (by
      have hk_eq : k.1 = k.1 - 1 + 1 := (Nat.sub_add_cancel k.2).symm
      have hidx :
          (⟨k.1 - 1 + 1, Nat.succ_le_succ (Nat.zero_le (k.1 - 1))⟩ :
            PositiveTime) = k := by
        ext
        exact Nat.sub_add_cancel k.2
      rw [hk_eq, x_update_identity_grad_error]
      rw [hidx]
      simp [Nat.sub_add_cancel k.2])
    (by
      have hsmooth_abs := smoothUpper S (xUnder S ξ k) (xBar S ξ k.1)
      have h := (abs_le.mp hsmooth_abs).2
      linarith)
    (by
      have hlin := partB_convex_search_point_linearization S hconvex ξ k xRef
      linarith)

/-- The Part B one-step recursion rewritten in the input shape of the Gamma
recurrence telescope. -/
private theorem partB_one_step_for_gamma_telescope
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (ξ : ℕ → Sample) (xRef : Space n) (t : ℕ) (ht : 1 ≤ t) :
    let tp : PositiveTime := ⟨t, ht⟩
    S.Ψ (xBar S ξ t) - S.Ψ xRef ≤
      (1 - S.alpha t) * (S.Ψ (xBar S ξ (t - 1)) - S.Ψ xRef) +
        S.alpha t *
          (-(S.beta t / S.alpha t) *
            (1 - S.LΨ * S.beta t / 2 -
              S.alpha t * S.lam t / (2 * S.beta t)) *
            ‖gradΨ S (xUnder S ξ tp)‖ ^ 2) +
        S.alpha t / (2 * S.lam t) *
          (‖x S ξ (t - 1) - xRef‖ ^ 2 -
            ‖x S ξ t - xRef‖ ^ 2) +
        (S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t) / 2 *
          ‖generatedOracleErrorAt S tp ξ‖ ^ 2 +
        inner ℝ (generatedOracleErrorAt S tp ξ)
          (((S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t -
                S.beta t) • gradΨ S (xUnder S ξ tp)) +
            S.alpha t • (xRef - x S ξ (t - 1))) := by
  let tp : PositiveTime := ⟨t, ht⟩
  have hstep := partB_one_step_convex_recursion S hconvex ξ tp xRef
  have halpha_ne : S.alpha t ≠ 0 := by
    simpa [tp] using ne_of_gt (alpha_pos S tp)
  have hbeta_ne : S.beta t ≠ 0 := ne_of_gt (S.hbeta_pos t ht)
  dsimp only
  calc
    S.Ψ (xBar S ξ t) - S.Ψ xRef
        ≤
      (1 - S.alpha t) * (S.Ψ (xBar S ξ (t - 1)) - S.Ψ xRef) +
        S.alpha t / (2 * S.lam t) *
          (‖x S ξ (t - 1) - xRef‖ ^ 2 -
            ‖x S ξ t - xRef‖ ^ 2) -
        S.beta t *
          (1 - S.LΨ * S.beta t / 2 -
            S.alpha t * S.lam t / (2 * S.beta t)) *
          ‖gradΨ S (xUnder S ξ tp)‖ ^ 2 +
        (S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t) / 2 *
          ‖generatedOracleErrorAt S tp ξ‖ ^ 2 +
        inner ℝ (generatedOracleErrorAt S tp ξ)
          (((S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t -
                S.beta t) • gradΨ S (xUnder S ξ tp)) +
            S.alpha t • (xRef - x S ξ (t - 1))) := by
          simpa [tp] using hstep
    _ =
      (1 - S.alpha t) * (S.Ψ (xBar S ξ (t - 1)) - S.Ψ xRef) +
        S.alpha t *
          (-(S.beta t / S.alpha t) *
            (1 - S.LΨ * S.beta t / 2 -
              S.alpha t * S.lam t / (2 * S.beta t)) *
            ‖gradΨ S (xUnder S ξ tp)‖ ^ 2) +
        S.alpha t / (2 * S.lam t) *
          (‖x S ξ (t - 1) - xRef‖ ^ 2 -
            ‖x S ξ t - xRef‖ ^ 2) +
        (S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t) / 2 *
          ‖generatedOracleErrorAt S tp ξ‖ ^ 2 +
        inner ℝ (generatedOracleErrorAt S tp ξ)
          (((S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t -
                S.beta t) • gradΨ S (xUnder S ξ tp)) +
            S.alpha t • (xRef - x S ξ (t - 1))) := by
          field_simp [halpha_ne, hbeta_ne]
          ring

/-- Raw Gamma-normalized Part B pathwise telescope before the distance-difference
sum and stepsize-coefficient simplifications. -/
private theorem partB_pathwise_gamma_telescope_raw
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (ξ : ℕ → Sample) (xRef : Space n) (N : ℕ) (hN : 1 ≤ N) :
    let A : ℕ → ℝ := fun t => S.Ψ (xBar S ξ t) - S.Ψ xRef
    let gamma : ℕ → ℝ := fun t => 2 * S.lam t
    let GammaN : ℕ → ℝ := fun t => if ht : 1 ≤ t then Γ S ⟨t, ht⟩ else 1
    let Lterm : ℕ → ℝ := fun t =>
      if ht : 1 ≤ t then
        let tp : PositiveTime := ⟨t, ht⟩;
        -(S.beta t / S.alpha t) *
          (1 - S.LΨ * S.beta t / 2 -
            S.alpha t * S.lam t / (2 * S.beta t)) *
          ‖gradΨ S (xUnder S ξ tp)‖ ^ 2
      else 0
    let Bterm : ℕ → ℝ := fun t =>
      if ht : 1 ≤ t then
        ‖x S ξ (t - 1) - xRef‖ ^ 2 - ‖x S ξ t - xRef‖ ^ 2
      else 0
    let Dterm : ℕ → ℝ := fun t =>
      if ht : 1 ≤ t then
        let tp : PositiveTime := ⟨t, ht⟩;
        (S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t) / 2 *
            ‖generatedOracleErrorAt S tp ξ‖ ^ 2 +
          inner ℝ (generatedOracleErrorAt S tp ξ)
            (((S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t -
                  S.beta t) • gradΨ S (xUnder S ξ tp)) +
              S.alpha t • (xRef - x S ξ (t - 1)))
      else 0
    A N - GammaN N *
        Finset.sum (Finset.Icc 1 N) (fun t => S.alpha t / GammaN t * Lterm t) ≤
      GammaN N * (1 - S.alpha 1) * A 0 +
        GammaN N *
          Finset.sum (Finset.Icc 1 N)
            (fun t => S.alpha t / (gamma t * GammaN t) * Bterm t) +
        GammaN N *
          Finset.sum (Finset.Icc 1 N) (fun t => Dterm t / GammaN t) := by
  classical
  let A : ℕ → ℝ := fun t => S.Ψ (xBar S ξ t) - S.Ψ xRef
  let gamma : ℕ → ℝ := fun t => 2 * S.lam t
  let GammaN : ℕ → ℝ := fun t => if ht : 1 ≤ t then Γ S ⟨t, ht⟩ else 1
  let Lterm : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then
      let tp : PositiveTime := ⟨t, ht⟩;
      -(S.beta t / S.alpha t) *
        (1 - S.LΨ * S.beta t / 2 -
          S.alpha t * S.lam t / (2 * S.beta t)) *
        ‖gradΨ S (xUnder S ξ tp)‖ ^ 2
    else 0
  let Bterm : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then
      ‖x S ξ (t - 1) - xRef‖ ^ 2 - ‖x S ξ t - xRef‖ ^ 2
    else 0
  let Dterm : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then
      let tp : PositiveTime := ⟨t, ht⟩;
      (S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t) / 2 *
          ‖generatedOracleErrorAt S tp ξ‖ ^ 2 +
        inner ℝ (generatedOracleErrorAt S tp ξ)
          (((S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t -
                S.beta t) • gradΨ S (xUnder S ξ tp)) +
            S.alpha t • (xRef - x S ξ (t - 1)))
    else 0
  have hgamma_ne : ∀ t, 1 ≤ t → gamma t ≠ 0 := by
    intro t ht
    have hlam : S.lam t ≠ 0 := ne_of_gt (S.hlam_pos t ht)
    dsimp [gamma]
    exact mul_ne_zero (by norm_num) hlam
  have hGamma_ne : ∀ t, 1 ≤ t → GammaN t ≠ 0 := by
    intro t ht
    dsimp [GammaN]
    simp [ht, ne_of_gt (Γ_pos S ⟨t, ht⟩)]
  have hGamma_one : GammaN 1 = 1 := by
    dsimp [GammaN]
    simp
  have halpha_le_one_nat : ∀ t, 1 ≤ t → S.alpha t ≤ 1 := by
    intro t ht
    simpa using alpha_le_one S ⟨t, ht⟩
  have hGamma_succ :
      ∀ t, 1 ≤ t → GammaN (t + 1) = (1 - S.alpha (t + 1)) * GammaN t := by
    intro t ht
    have ht1 : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
    dsimp [GammaN]
    simp [ht, ht1, Γ_succ S t ht]
  have hstep : ∀ t, 1 ≤ t →
      A t ≤ (1 - S.alpha t) * A (t - 1) + S.alpha t * Lterm t +
        S.alpha t / gamma t * Bterm t + Dterm t := by
    intro t ht
    have h := partB_one_step_for_gamma_telescope S hconvex ξ xRef t ht
    dsimp [A, Lterm, Bterm, Dterm, gamma] at h ⊢
    simp [ht] at h ⊢
    nlinarith [h]
  have htel :=
    finite_window_weighted_recurrence_telescope_with_tail_sums
      (alpha := S.alpha) (gamma := gamma) (Gamma := GammaN)
      (A := A) (L := Lterm) (B := Bterm) (D := Dterm)
      N hN hgamma_ne hGamma_ne hGamma_one S.halpha_one
      halpha_le_one_nat hGamma_succ hstep
  simpa [A, gamma, GammaN, Lterm, Bterm, Dterm, hN] using htel

/-- Local wrapper for the accelerated `α / Γ` normalization used by Jensen. -/
private theorem sum_alpha_div_Gamma_eq_inv
    (S : Setup n Sample) (k : PositiveTime) :
    Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
      let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
      S.alpha τ.1 / Γ S τp) = 1 / Γ S k := by
  unfold Γ
  exact SOptLib.sum_alpha_div_acceleratedGamma_eq_inv S.alpha S.halpha_one
    (fun t => ne_of_gt (Γ_pos S t)) k.1 k.2

/-- Source stochastic acceleration-gap estimate after expanding
`‖∇Ψ(underline x_τ) + δ_τ‖²`. -/
private theorem partA_acceleration_gap_sq_le_expanded_sum
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    ‖xBar S ξ k.1 - x S ξ k.1‖ ^ 2 ≤
      Γ S k *
        Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
          let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
          ((S.lam τ.1 - S.beta τ.1) ^ 2 /
              (Γ S τp * S.alpha τ.1)) *
            (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
              ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
              2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                (generatedOracleErrorAt S τp ξ))) := by
  classical
  let s : Finset ℕ := Finset.Icc 1 k.1
  let γ : ℕ → ℝ := fun τ =>
    if hτ : 1 ≤ τ then S.alpha τ / Γ S ⟨τ, hτ⟩ else 0
  let p : ℕ → Space n := fun τ =>
    if hτ : 1 ≤ τ then
      ((S.lam τ - S.beta τ) / S.alpha τ) •
        (gradΨ S (xUnder S ξ ⟨τ, hτ⟩) +
          generatedOracleErrorAt S ⟨τ, hτ⟩ ξ)
    else 0
  let term : ℕ → Space n := fun τ =>
    if hτ : 1 ≤ τ then
      ((S.lam τ - S.beta τ) / Γ S ⟨τ, hτ⟩) •
        (gradΨ S (xUnder S ξ ⟨τ, hτ⟩) +
          generatedOracleErrorAt S ⟨τ, hτ⟩ ξ)
    else 0
  let W : ℝ := (Γ S k)⁻¹
  have hγ_nonneg : ∀ i ∈ s, 0 ≤ γ i := by
    intro i hi
    have hi_pos : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    simp [γ, hi_pos, div_nonneg (le_of_lt (alpha_pos S ⟨i, hi_pos⟩))
      (le_of_lt (Γ_pos S ⟨i, hi_pos⟩))]
  have hW_pos : 0 < W := by
    simp [W, inv_pos.mpr (Γ_pos S k)]
  have hsum_base_attach :
      Finset.sum s γ =
        Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
          let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
          S.alpha τ.1 / Γ S τp) := by
    calc
      Finset.sum s γ =
          Finset.sum s.attach (fun τ => γ τ.1) := by
            simpa using (Finset.sum_attach (s := s) (f := γ)).symm
      _ = Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
            let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
            S.alpha τ.1 / Γ S τp) := by
              subst s
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hi_pos : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
              simp [γ, hi_pos]
  have hW_eq : W = Finset.sum s γ := by
    rw [hsum_base_attach, sum_alpha_div_Gamma_eq_inv S k]
    simp [W]
  have hsum_gamma_p_eq_term :
      Finset.sum s (fun τ => γ τ • p τ) = Finset.sum s term := by
    refine Finset.sum_congr rfl ?_
    intro τ hτmem
    have hτ_pos : 1 ≤ τ := (Finset.mem_Icc.mp hτmem).1
    have hα_ne : S.alpha τ ≠ 0 := ne_of_gt (alpha_pos S ⟨τ, hτ_pos⟩)
    have hΓ_ne : Γ S ⟨τ, hτ_pos⟩ ≠ 0 := ne_of_gt (Γ_pos S ⟨τ, hτ_pos⟩)
    have hscalar :
        (S.alpha τ / Γ S ⟨τ, hτ_pos⟩) *
            ((S.lam τ - S.beta τ) / S.alpha τ) =
          (S.lam τ - S.beta τ) / Γ S ⟨τ, hτ_pos⟩ := by
      field_simp [hα_ne, hΓ_ne]
    simp [γ, p, term, hτ_pos, smul_smul, hscalar]
  have hWinv : W⁻¹ = Γ S k := by
    simp [W]
  have hxbar :
      xBar S ξ k.1 - x S ξ k.1 =
        W⁻¹ • Finset.sum s (fun i => γ i • p i) := by
    calc
      xBar S ξ k.1 - x S ξ k.1 = Γ S k • Finset.sum s term := by
        simpa [s, term] using xBar_sub_x_eq_Gamma_weighted_sum S ξ k
      _ = W⁻¹ • Finset.sum s term := by rw [hWinv]
      _ = W⁻¹ • Finset.sum s (fun i => γ i • p i) := by
        rw [hsum_gamma_p_eq_term]
  have hJ := norm_sq_weighted_average_sub_le_inv_mul_sum
    (s := s) (γ := γ) (p := p)
    (xbar := xBar S ξ k.1 - x S ξ k.1) (z := (0 : Space n)) (W := W)
    hγ_nonneg hW_pos hW_eq hxbar
  have hJ' :
      ‖xBar S ξ k.1 - x S ξ k.1‖ ^ 2 ≤
        Γ S k * Finset.sum s (fun i => γ i * ‖p i‖ ^ 2) := by
    simpa [hWinv] using hJ
  have hsum_expand :
      Finset.sum s (fun i => γ i * ‖p i‖ ^ 2) =
        Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
          let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
          ((S.lam τ.1 - S.beta τ.1) ^ 2 /
              (Γ S τp * S.alpha τ.1)) *
            (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
              ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
              2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                (generatedOracleErrorAt S τp ξ))) := by
    calc
      Finset.sum s (fun i => γ i * ‖p i‖ ^ 2) =
          Finset.sum s.attach (fun τ => γ τ.1 * ‖p τ.1‖ ^ 2) := by
            simpa using (Finset.sum_attach
              (s := s) (f := fun i => γ i * ‖p i‖ ^ 2)).symm
      _ = Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
            let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
            ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                (Γ S τp * S.alpha τ.1)) *
              (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                  (generatedOracleErrorAt S τp ξ))) := by
              subst s
              refine Finset.sum_congr rfl ?_
              intro τ hτmem
              have hτ_pos : 1 ≤ τ.1 := (Finset.mem_Icc.mp τ.2).1
              have hα_ne : S.alpha τ.1 ≠ 0 :=
                ne_of_gt (alpha_pos S ⟨τ.1, hτ_pos⟩)
              have hΓ_ne : Γ S ⟨τ.1, hτ_pos⟩ ≠ 0 :=
                ne_of_gt (Γ_pos S ⟨τ.1, hτ_pos⟩)
              simp only [γ, p, hτ_pos, dite_true]
              rw [norm_smul, mul_pow, norm_add_sq_real, Real.norm_eq_abs, sq_abs]
              field_simp [hα_ne, hΓ_ne]
              ring
  simpa [hsum_expand] using hJ'

/-- Each expanded stochastic acceleration-gap summand is nonnegative. -/
private theorem partA_acceleration_expanded_summand_nonneg
    (S : Setup n Sample) (ξ : ℕ → Sample) (τ : PositiveTime) :
    0 ≤
      ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τ * S.alpha τ.1)) *
        (‖gradΨ S (xUnder S ξ τ)‖ ^ 2 +
          ‖generatedOracleErrorAt S τ ξ‖ ^ 2 +
          2 * inner ℝ (gradΨ S (xUnder S ξ τ))
            (generatedOracleErrorAt S τ ξ)) := by
  have hcoeff_nonneg :
      0 ≤ (S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τ * S.alpha τ.1) := by
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (le_of_lt (Γ_pos S τ)) (le_of_lt (alpha_pos S τ)))
  have hbracket_nonneg :
      0 ≤
        ‖gradΨ S (xUnder S ξ τ)‖ ^ 2 +
          ‖generatedOracleErrorAt S τ ξ‖ ^ 2 +
          2 * inner ℝ (gradΨ S (xUnder S ξ τ))
            (generatedOracleErrorAt S τ ξ) := by
    have hsq : 0 ≤ ‖gradΨ S (xUnder S ξ τ) +
        generatedOracleErrorAt S τ ξ‖ ^ 2 := sq_nonneg _
    rw [norm_add_sq_real] at hsq
    linarith
  exact mul_nonneg hcoeff_nonneg hbracket_nonneg

/-- The nonnegative expanded acceleration-gap window sum is monotone in the
positive upper endpoint. -/
private theorem partA_acceleration_expanded_sum_mono
    (S : Setup n Sample) (ξ : ℕ → Sample) (j k : PositiveTime) (hjk : j.1 ≤ k.1) :
    Finset.sum (Finset.Icc 1 j.1).attach (fun τ =>
      let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
      ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
        (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
          ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
          2 * inner ℝ (gradΨ S (xUnder S ξ τp))
            (generatedOracleErrorAt S τp ξ))) ≤
    Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
      let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
      ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
        (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
          ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
          2 * inner ℝ (gradΨ S (xUnder S ξ τp))
            (generatedOracleErrorAt S τp ξ))) := by
  classical
  let F : ℕ → ℝ := fun τ =>
    if hτ : 1 ≤ τ then
      ((S.lam τ - S.beta τ) ^ 2 / (Γ S ⟨τ, hτ⟩ * S.alpha τ)) *
        (‖gradΨ S (xUnder S ξ ⟨τ, hτ⟩)‖ ^ 2 +
          ‖generatedOracleErrorAt S ⟨τ, hτ⟩ ξ‖ ^ 2 +
          2 * inner ℝ (gradΨ S (xUnder S ξ ⟨τ, hτ⟩))
            (generatedOracleErrorAt S ⟨τ, hτ⟩ ξ))
    else 0
  have hsum_j :
      Finset.sum (Finset.Icc 1 j.1).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
          (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
            ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
            2 * inner ℝ (gradΨ S (xUnder S ξ τp))
              (generatedOracleErrorAt S τp ξ))) =
        Finset.sum (Finset.Icc 1 j.1) F := by
    calc
      Finset.sum (Finset.Icc 1 j.1).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
          (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
            ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
            2 * inner ℝ (gradΨ S (xUnder S ξ τp))
              (generatedOracleErrorAt S τp ξ)))
          = Finset.sum (Finset.Icc 1 j.1).attach (fun τ => F τ.1) := by
              refine Finset.sum_congr rfl ?_
              intro τ hτmem
              have hτ_pos : 1 ≤ τ.1 := (Finset.mem_Icc.mp τ.2).1
              simp [F, hτ_pos]
      _ = Finset.sum (Finset.Icc 1 j.1) F := by
              simpa using (Finset.sum_attach (s := Finset.Icc 1 j.1) (f := F))
  have hsum_k :
      Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
          (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
            ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
            2 * inner ℝ (gradΨ S (xUnder S ξ τp))
              (generatedOracleErrorAt S τp ξ))) =
        Finset.sum (Finset.Icc 1 k.1) F := by
    calc
      Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
          (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
            ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
            2 * inner ℝ (gradΨ S (xUnder S ξ τp))
              (generatedOracleErrorAt S τp ξ)))
          = Finset.sum (Finset.Icc 1 k.1).attach (fun τ => F τ.1) := by
              refine Finset.sum_congr rfl ?_
              intro τ hτmem
              have hτ_pos : 1 ≤ τ.1 := (Finset.mem_Icc.mp τ.2).1
              simp [F, hτ_pos]
      _ = Finset.sum (Finset.Icc 1 k.1) F := by
              simpa using (Finset.sum_attach (s := Finset.Icc 1 k.1) (f := F))
  rw [hsum_j, hsum_k]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro τ hτ
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hτ).1, le_trans (Finset.mem_Icc.mp hτ).2 hjk⟩
  · intro τ hτk hτnotj
    have hτ_pos : 1 ≤ τ := (Finset.mem_Icc.mp hτk).1
    simpa [F, hτ_pos] using
      partA_acceleration_expanded_summand_nonneg S ξ ⟨τ, hτ_pos⟩

/-- Planner T1: the multiplied acceleration-gap term is bounded by the expanded
source stochastic-gradient sum on the current window. -/
private theorem partA_acceleration_gap_term_le_expanded_sum
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) *
        ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖ ^ 2 ≤
      (S.LΨ * Γ S k / 2) *
        Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
          let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
          ((S.lam τ.1 - S.beta τ.1) ^ 2 /
              (Γ S τp * S.alpha τ.1)) *
            (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
              ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
              2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                (generatedOracleErrorAt S τp ξ))) := by
  classical
  let sumK : ℝ :=
    Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
      let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
      ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
        (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
          ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
          2 * inner ℝ (gradΨ S (xUnder S ξ τp))
            (generatedOracleErrorAt S τp ξ)))
  by_cases hk_one : k.1 = 1
  · have hgap := partA_acceleration_gap_sq_le_expanded_sum S ξ k
    have hright_nonneg : 0 ≤ Γ S k * sumK := by
      exact le_trans (sq_nonneg _) (by simpa [sumK] using hgap)
    have hscale_nonneg : 0 ≤ S.LΨ / 2 := by linarith [S.hLΨ_pos]
    have hR : 0 ≤ (S.LΨ * Γ S k / 2) * sumK := by
      nlinarith [mul_nonneg hscale_nonneg hright_nonneg]
    simpa [sumK, hk_one, S.halpha_one] using hR
  · have hk_pred_pos : 1 ≤ k.1 - 1 := by omega
    let j : PositiveTime := ⟨k.1 - 1, hk_pred_pos⟩
    let sumJ : ℝ :=
      Finset.sum (Finset.Icc 1 j.1).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        ((S.lam τ.1 - S.beta τ.1) ^ 2 / (Γ S τp * S.alpha τ.1)) *
          (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
            ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
            2 * inner ℝ (gradΨ S (xUnder S ξ τp))
              (generatedOracleErrorAt S τp ξ)))
    have hgap := partA_acceleration_gap_sq_le_expanded_sum S ξ j
    have hnorm :
        ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖ ^ 2 =
          ‖xBar S ξ j.1 - x S ξ j.1‖ ^ 2 := by
      have hvec :
          x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1) =
            -(xBar S ξ j.1 - x S ξ j.1) := by
        simp [j, sub_eq_add_neg]
      rw [hvec, norm_neg]
    have hcoef_nonneg : 0 ≤ S.LΨ * (1 - S.alpha k.1) ^ 2 / 2 := by
      nlinarith [S.hLΨ_pos, sq_nonneg (1 - S.alpha k.1)]
    have hfirst :
        (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) *
            ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖ ^ 2 ≤
          (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) * (Γ S j * sumJ) := by
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left (by simpa [sumJ] using hgap) hcoef_nonneg
    have hsumJ_nonneg : 0 ≤ sumJ := by
      dsimp [sumJ]
      exact Finset.sum_nonneg (fun τ hτ =>
        partA_acceleration_expanded_summand_nonneg S ξ
          ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩)
    have hsum_le : sumJ ≤ sumK := by
      dsimp [sumJ, sumK]
      exact partA_acceleration_expanded_sum_mono S ξ j k (Nat.sub_le k.1 1)
    have ha_nonneg : 0 ≤ 1 - S.alpha k.1 := by
      have hle := alpha_le_one S k
      linarith
    have ha_le_one : 1 - S.alpha k.1 ≤ 1 := by
      have hα_pos := alpha_pos S k
      linarith
    have hΓj_nonneg : 0 ≤ Γ S j := le_of_lt (Γ_pos S j)
    have hscale_nonneg : 0 ≤ S.LΨ / 2 := by linarith [S.hLΨ_pos]
    have hΓk : Γ S k = (1 - S.alpha k.1) * Γ S j := by
      have hsucc := Γ_succ S (k.1 - 1) hk_pred_pos
      simpa [j, Nat.sub_add_cancel k.2] using hsucc
    have hsecond :
        (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) * (Γ S j * sumJ) ≤
          (S.LΨ * Γ S k / 2) * sumK := by
      have ha_sq_le : (1 - S.alpha k.1) ^ 2 ≤ 1 - S.alpha k.1 := by
        nlinarith [ha_nonneg, ha_le_one]
      have hΓsumJ_nonneg : 0 ≤ Γ S j * sumJ :=
        mul_nonneg hΓj_nonneg hsumJ_nonneg
      have hleft_le_mid :
          (1 - S.alpha k.1) ^ 2 * (Γ S j * sumJ) ≤
            (1 - S.alpha k.1) * (Γ S j * sumJ) :=
        mul_le_mul_of_nonneg_right ha_sq_le hΓsumJ_nonneg
      have haΓ_nonneg : 0 ≤ (1 - S.alpha k.1) * Γ S j :=
        mul_nonneg ha_nonneg hΓj_nonneg
      have hmid_le_right :
          (1 - S.alpha k.1) * Γ S j * sumJ ≤
            (1 - S.alpha k.1) * Γ S j * sumK :=
        mul_le_mul_of_nonneg_left hsum_le haΓ_nonneg
      have hwindow_scaled :
          (1 - S.alpha k.1) ^ 2 * (Γ S j * sumJ) ≤
            (1 - S.alpha k.1) * Γ S j * sumK := by
        nlinarith [hleft_le_mid, hmid_le_right]
      have hscaled :
          (S.LΨ / 2) * ((1 - S.alpha k.1) ^ 2 * (Γ S j * sumJ)) ≤
            (S.LΨ / 2) * ((1 - S.alpha k.1) * Γ S j * sumK) :=
        mul_le_mul_of_nonneg_left hwindow_scaled hscale_nonneg
      calc
        (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) * (Γ S j * sumJ)
            = (S.LΨ / 2) * ((1 - S.alpha k.1) ^ 2 * (Γ S j * sumJ)) := by
                ring
        _ ≤ (S.LΨ / 2) * ((1 - S.alpha k.1) * Γ S j * sumK) := hscaled
        _ = (S.LΨ * Γ S k / 2) * sumK := by
                rw [hΓk]
                ring
    exact le_trans hfirst hsecond

/-- The search-point displacement is the `(1 - α_k)` acceleration gap. -/
private theorem xPrev_sub_xUnder_norm_eq_acceleration_gap
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    ‖x S ξ (k.1 - 1) - xUnder S ξ k‖ =
      (1 - S.alpha k.1) * ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖ := by
  have hcoef_nonneg : 0 ≤ 1 - S.alpha k.1 := by
    have hle := alpha_le_one S k
    linarith
  rw [xUnder_update_identity]
  have hvec :
      x S ξ (k.1 - 1) -
          ((1 - S.alpha k.1) • xBar S ξ (k.1 - 1) +
            S.alpha k.1 • x S ξ (k.1 - 1)) =
        (1 - S.alpha k.1) •
          (x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)) := by
    module
  rw [hvec, norm_smul, Real.norm_of_nonneg hcoef_nonneg]

/-- Lipschitz gradients turn the proof-local `Δ_k` into the acceleration-gap norm. -/
private theorem partA_gradientDifference_norm_le_acceleration_gap
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    ‖gradientDifference S (x S ξ (k.1 - 1)) (xUnder S ξ k)‖ ≤
      S.LΨ * ((1 - S.alpha k.1) *
        ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖) := by
  have hlip :
      ‖gradientDifference S (x S ξ (k.1 - 1)) (xUnder S ξ k)‖ ≤
        S.LΨ * ‖x S ξ (k.1 - 1) - xUnder S ξ k‖ := by
    unfold gradientDifference gradΨ
    exact S.hLipschitzGrad (xUnder S ξ k) (x S ξ (k.1 - 1))
  rw [xPrev_sub_xUnder_norm_eq_acceleration_gap S ξ k] at hlip
  exact hlip

/-- Fixed-time pathwise descent after bounding the gradient-difference term by
the acceleration gap and applying Young's inequality. -/
private theorem partA_one_step_descent_with_acceleration_gap
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    S.Ψ (x S ξ k.1) ≤
      S.Ψ (x S ξ (k.1 - 1)) -
        S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
          ‖gradΨ S (xUnder S ξ k)‖ ^ 2 +
        (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) *
          ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖ ^ 2 +
        (S.LΨ * S.lam k.1 ^ 2 / 2) * ‖generatedOracleErrorAt S k ξ‖ ^ 2 -
        S.lam k.1 *
          inner ℝ
            (gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ k))
            (generatedOracleErrorAt S k ξ) := by
  let Gnorm : ℝ := ‖gradΨ S (xUnder S ξ k)‖
  let Anorm : ℝ := ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖
  let Dnorm : ℝ :=
    ‖gradientDifference S (x S ξ (k.1 - 1)) (xUnder S ξ k)‖
  have hraw := partA_one_step_descent_raw S ξ k
  have hΔ : Dnorm ≤ S.LΨ * ((1 - S.alpha k.1) * Anorm) := by
    simpa [Dnorm, Anorm] using partA_gradientDifference_norm_le_acceleration_gap S ξ k
  have hlam_nonneg : 0 ≤ S.lam k.1 := le_of_lt (S.hlam_pos k.1 k.2)
  have hL_nonneg : 0 ≤ S.LΨ := le_of_lt S.hLΨ_pos
  have hDterm :
      S.lam k.1 * Dnorm * Gnorm ≤
        S.lam k.1 * (S.LΨ * ((1 - S.alpha k.1) * Anorm)) * Gnorm := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hΔ hlam_nonneg) (norm_nonneg _)
  have hyoung :
      S.lam k.1 * (S.LΨ * ((1 - S.alpha k.1) * Anorm)) * Gnorm ≤
        (S.LΨ * S.lam k.1 ^ 2 / 2) * Gnorm ^ 2 +
          (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) * Anorm ^ 2 := by
    have hsq : 0 ≤ (S.lam k.1 * Gnorm - (1 - S.alpha k.1) * Anorm) ^ 2 :=
      sq_nonneg _
    nlinarith [mul_nonneg hL_nonneg hsq]
  have hDyoung :
      S.lam k.1 * Dnorm * Gnorm ≤
        (S.LΨ * S.lam k.1 ^ 2 / 2) * Gnorm ^ 2 +
          (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) * Anorm ^ 2 :=
    le_trans hDterm hyoung
  dsimp [Gnorm, Anorm, Dnorm] at hDyoung
  nlinarith [hraw, hDyoung]

/-- Source step 5: substitute the expanded acceleration-gap estimate into the
fixed-time descent inequality. -/
private theorem partA_one_step_descent_with_expanded_gap
    (S : Setup n Sample) (ξ : ℕ → Sample) (k : PositiveTime) :
    S.Ψ (x S ξ k.1) ≤
      S.Ψ (x S ξ (k.1 - 1)) -
        S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
          ‖gradΨ S (xUnder S ξ k)‖ ^ 2 +
        (S.LΨ * Γ S k / 2) *
          Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
            let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
            ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                (Γ S τp * S.alpha τ.1)) *
              (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                  (generatedOracleErrorAt S τp ξ))) +
        (S.LΨ * S.lam k.1 ^ 2 / 2) * ‖generatedOracleErrorAt S k ξ‖ ^ 2 -
        S.lam k.1 *
          inner ℝ
            (gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ k))
            (generatedOracleErrorAt S k ξ) := by
  have hfixed := partA_one_step_descent_with_acceleration_gap S ξ k
  have hgap := partA_acceleration_gap_term_le_expanded_sum S ξ k
  nlinarith [hfixed, hgap]

/-- Coefficient `C_k` from (6.4.12), exposed only on positive time indices. -/
def C (S : Setup n Sample) (N : ℕ) (k : PositiveTime) : ℝ :=
  1 - S.LΨ * S.lam k.1 -
    (S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2) /
      (2 * S.alpha k.1 * Γ S k * S.lam k.1) *
        Finset.sum (Finset.Icc k.1 N).attach
          (fun τ => Γ S ⟨τ.1, le_trans k.2 (Finset.mem_Icc.mp τ.2).1⟩)

/-- Denominator admissibility for the displayed `C_k` coefficient is source-derived
from the Algorithm 6.4 parameter domains and `Γ` positivity. -/
theorem C_denominator_ne_zero
    (S : Setup n Sample) (k : PositiveTime) :
    2 * S.alpha k.1 * Γ S k * S.lam k.1 ≠ 0 := by
  have htwo_ne : (2 : ℝ) ≠ 0 := by norm_num
  have halpha_ne : S.alpha k.1 ≠ 0 := by
    rcases lt_or_eq_of_le k.2 with hlt | heq
    · have hk_ge_two : 2 ≤ k.1 := Nat.succ_le_of_lt hlt
      exact ne_of_gt (S.halpha_mem k.1 hk_ge_two).1
    · rw [← heq, S.halpha_one]
      norm_num
  have hGamma_ne : Γ S k ≠ 0 := ne_of_gt (Γ_pos S k)
  have hlam_ne : S.lam k.1 ≠ 0 := ne_of_gt (S.hlam_pos k.1 k.2)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero htwo_ne halpha_ne) hGamma_ne) hlam_ne

/-- Part (a) randomization weights from (6.4.66). -/
def pPartA (S : Setup n Sample) (N : ℕ) (k : WindowTime N) : ℝ :=
  let kp : PositiveTime := ⟨k.1, k.2.1⟩
  S.lam k.1 * C S N kp /
    Finset.sum (Finset.Icc 1 N).attach (fun τ =>
      let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
      S.lam τ.1 * C S N τp)

/-- Raw part (a) stopping weight `λ_k C_k`, totalized outside positive time. -/
def partAWeight (S : Setup n Sample) (N k : ℕ) : ℝ :=
  if hk : 1 ≤ k then S.lam k * C S N ⟨k, hk⟩ else 0

/-- The part (a) weights are nonnegative on `1, ..., N` under the paper condition `C_k > 0`. -/
theorem partAWeight_nonneg_of_C_pos
    (S : Setup n Sample) (N : ℕ)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩) :
    ∀ k, k ∈ Finset.Icc 1 N → 0 ≤ partAWeight S N k := by
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
  unfold partAWeight
  simp [hk1]
  exact mul_nonneg (le_of_lt (S.hlam_pos k hk1)) (le_of_lt (hC_pos ⟨k, hk1, hkN⟩))

/-- The part (a) stopping denominator is positive under the paper condition `C_k > 0`. -/
theorem partAWeight_sum_pos_of_C_pos
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩) :
    0 < Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
  refine Finset.sum_pos_of_nonempty (Finset.Icc 1 N) (partAWeight S N) ?_ ?_
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    unfold partAWeight
    simp [hk1]
    exact mul_pos (S.hlam_pos k hk1) (hC_pos ⟨k, hk1, hkN⟩)
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- The canonical stopping law for Theorem 6.12(a): `Prob{R=k}=λ_k C_k / ∑ λτ Cτ`. -/
def partAStoppingLaw
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩) :
    PMF (OutputTime N) :=
  normalizedFiniteWindowPMF (Finset.Icc 1 N) (partAWeight S N)
    (partAWeight_nonneg_of_C_pos S N hC_pos)
    (partAWeight_sum_pos_of_C_pos S N hN hC_pos)

/-- The part (a) stopping law has the paper's displayed atom formula. -/
theorem partAStoppingLaw_apply
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩)
    (R : OutputTime N) :
    (partAStoppingLaw S N hN hC_pos).toMeasure.real ({R} : Set (OutputTime N)) =
      pPartA S N (outputTimeWindow R) := by
  have hR1 : 1 ≤ R.1 := (Finset.mem_Icc.mp R.2).1
  have hden_attach :
      Finset.sum (Finset.Icc 1 N).attach (fun τ =>
          S.lam τ.1 * C S N ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩) =
        Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun τ =>
          S.lam τ.1 * C S N ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩)
          = Finset.sum (Finset.Icc 1 N).attach (fun τ => partAWeight S N τ.1) := by
              refine Finset.sum_congr rfl ?_
              intro τ hτ
              have hτ1 : 1 ≤ τ.1 := (Finset.mem_Icc.mp τ.2).1
              unfold partAWeight
              simp [hτ1]
      _ = Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
              simpa using (Finset.sum_attach (s := Finset.Icc 1 N) (f := partAWeight S N))
  have hden_eq :
      Finset.sum (Finset.Icc 1 N) (partAWeight S N) =
        Finset.sum (Finset.Icc 1 N).attach (fun τ =>
          S.lam τ.1 * C S N ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩) := hden_attach.symm
  unfold partAStoppingLaw pPartA outputTimeWindow
  rw [Measure.real_def]
  rw [PMF.toMeasure_apply_singleton _ R (measurableSet_singleton R)]
  rw [normalizedFiniteWindowPMF_apply]
  rw [ENNReal.toReal_ofReal]
  · rw [hden_eq]
    unfold partAWeight
    simp [hR1]
  · exact div_nonneg (partAWeight_nonneg_of_C_pos S N hC_pos R.1 R.2)
      (le_of_lt (partAWeight_sum_pos_of_C_pos S N hN hC_pos))

/-- Part (b) randomization weights from (6.4.69). -/
def pPartB (S : Setup n Sample) (N : ℕ) (k : WindowTime N) : ℝ :=
  let kp : PositiveTime := ⟨k.1, k.2.1⟩
  (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) /
    Finset.sum (Finset.Icc 1 N).attach (fun τ =>
      let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
      (Γ S τp)⁻¹ * S.beta τ.1 * (1 - S.LΨ * S.beta τ.1))

/-- Part (b) monotonicity condition (6.4.15), stated as a paper-facing parameter
assumption rather than a proof-local hypothesis. -/
def PartBStepCondition (S : Setup n Sample) (N : ℕ) : Prop :=
  AcceleratedFiniteWindowScalarStepCondition S.alpha S.beta S.lam (fun k => Γ S k) S.LΨ N

/-- Part B stepsize conditions restrict from a longer finite window to any
positive prefix. -/
private theorem partBStepCondition_restrict
    (S : Setup n Sample) {K N : ℕ} (_hK : 1 ≤ K) (hKN : K ≤ N)
    (hsteps : PartBStepCondition S N) :
    PartBStepCondition S K := by
  refine ⟨?_, ?_, ?_⟩
  · intro k j hsucc
    exact hsteps.1
      ⟨k.1, k.2.1, le_trans k.2.2 hKN⟩
      ⟨j.1, j.2.1, le_trans j.2.2 hKN⟩
      hsucc
  · intro k
    exact hsteps.2.1 ⟨k.1, k.2.1, le_trans k.2.2 hKN⟩
  · intro k
    exact hsteps.2.2 ⟨k.1, k.2.1, le_trans k.2.2 hKN⟩

/-- Part B weighted squared-distance telescope, Eq. (6.4.30) with the paper's
extra factor `1/2` from the one-step identity. -/
private theorem partB_distance_telescope_bound_nat
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hsteps : PartBStepCondition S N) (ξ : ℕ → Sample) (xRef : Space n) :
    let coeff : ℕ → ℝ := fun t =>
      if ht : 1 ≤ t then S.alpha t / (2 * S.lam t * Γ S ⟨t, ht⟩) else 0
    let V : ℕ → ℝ := fun t => ‖x S ξ t - xRef‖ ^ 2
    Finset.sum (Finset.Icc 1 N) (fun t => coeff t * (V (t - 1) - V t)) ≤
      (2 * S.lam 1)⁻¹ * ‖S.x0 - xRef‖ ^ 2 := by
  classical
  let coeff : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then S.alpha t / (2 * S.lam t * Γ S ⟨t, ht⟩) else 0
  let V : ℕ → ℝ := fun t => ‖x S ξ t - xRef‖ ^ 2
  have hV_nonneg : ∀ n, 1 ≤ n → n < N → 0 ≤ V n := by
    intro n hn hnN
    dsimp [V]
    positivity
  have hbridge : ∀ n, 1 ≤ n → n < N → coeff (n + 1) ≤ coeff n := by
    intro n hn hnN
    have hnN_le : n ≤ N := Nat.le_of_lt hnN
    have hn1_le_N : n + 1 ≤ N := hnN
    let kp : WindowTime N := ⟨n, hn, hnN_le⟩
    let jp : WindowTime N := ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hn1_le_N⟩
    have hratio := hsteps.1 kp jp (by rfl)
    have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hscaled :
        (1 / 2) *
            (S.alpha (n + 1) /
              (S.lam (n + 1) * Γ S ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩)) ≤
          (1 / 2) *
            (S.alpha n / (S.lam n * Γ S ⟨n, hn⟩)) :=
      mul_le_mul_of_nonneg_left hratio hhalf_nonneg
    have hcoeff_succ :
        coeff (n + 1) =
          (1 / 2) *
            (S.alpha (n + 1) /
              (S.lam (n + 1) * Γ S ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩)) := by
      dsimp [coeff]
      simp [Nat.succ_le_succ (Nat.zero_le n)]
      ring
    have hcoeff_cur :
        coeff n = (1 / 2) * (S.alpha n / (S.lam n * Γ S ⟨n, hn⟩)) := by
      dsimp [coeff]
      simp [hn]
      ring
    calc
      coeff (n + 1)
          =
        (1 / 2) *
          (S.alpha (n + 1) /
            (S.lam (n + 1) * Γ S ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n)⟩)) := hcoeff_succ
      _ ≤ (1 / 2) * (S.alpha n / (S.lam n * Γ S ⟨n, hn⟩)) := hscaled
      _ = coeff n := hcoeff_cur.symm
  have htel :=
    sum_Icc_two_coeff_telescope_le coeff coeff V N hN hV_nonneg hbridge
  have htail_nonneg : 0 ≤ coeff N * V N := by
    have hcoeff_nonneg : 0 ≤ coeff N := by
      dsimp [coeff]
      simp [hN]
      have ha : 0 ≤ S.alpha N := le_of_lt (alpha_pos S ⟨N, hN⟩)
      have hden_pos : 0 < 2 * S.lam N * Γ S ⟨N, hN⟩ := by
        exact mul_pos (mul_pos (by norm_num) (S.hlam_pos N hN)) (Γ_pos S ⟨N, hN⟩)
      exact div_nonneg ha (le_of_lt hden_pos)
    exact mul_nonneg hcoeff_nonneg (by dsimp [V]; positivity)
  have hdrop :
      Finset.sum (Finset.Icc 1 N) (fun t => coeff t * (V (t - 1) - V t)) ≤
        coeff 1 * V 0 := by
    have hsum_eq :
        Finset.sum (Finset.Icc 1 N) (fun t => coeff t * (V (t - 1) - V t)) =
          Finset.sum (Finset.Icc 1 N) (fun t => coeff t * V (t - 1) - coeff t * V t) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    rw [hsum_eq]
    linarith
  have hcoeff_one :
      coeff 1 = (2 * S.lam 1)⁻¹ := by
    dsimp [coeff]
    simp [S.halpha_one]
  calc
    Finset.sum (Finset.Icc 1 N) (fun t => coeff t * (V (t - 1) - V t))
        ≤ coeff 1 * V 0 := hdrop
    _ = (2 * S.lam 1)⁻¹ * ‖S.x0 - xRef‖ ^ 2 := by
      rw [hcoeff_one]
      simp [V]

/-- Part B stepsizes simplify the one-step noise coefficient. -/
private theorem partB_noise_coeff_half_le_Lbeta_sq
    (S : Setup n Sample) (N : ℕ) (hsteps : PartBStepCondition S N)
    (k : WindowTime N) :
    (S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1) / 2 ≤
      S.LΨ * S.beta k.1 ^ 2 := by
  have h := hsteps.2.1 k
  nlinarith

/-- Part B stepsizes simplify the one-step gradient coefficient. -/
private theorem partB_gradient_coeff_weight_ge
    (S : Setup n Sample) (N : ℕ) (hsteps : PartBStepCondition S N)
    (k : WindowTime N) :
    S.beta k.1 *
        (1 - S.LΨ * S.beta k.1 / 2 -
          S.alpha k.1 * S.lam k.1 / (2 * S.beta k.1)) ≥
      S.beta k.1 * (1 - S.LΨ * S.beta k.1) := by
  have h := hsteps.2.1 k
  have hb_pos : 0 < S.beta k.1 := S.hbeta_pos k.1 k.2.1
  have hb_ne : S.beta k.1 ≠ 0 := ne_of_gt hb_pos
  field_simp [hb_ne]
  nlinarith

/-- Scalar normalization used after the Gamma telescope. -/
private theorem scalar_divided_of_sub_mul_le
    {A L C B D Γ : ℝ} (hΓpos : 0 < Γ)
    (h : A - Γ * L ≤ Γ * C + Γ * B + Γ * D) :
    A / Γ - L ≤ C + B + D := by
  exact div_sub_le_sum_of_sub_mul_le_mul_sum hΓpos h

set_option maxHeartbeats 800000 in
/-- Finite-sum form of the Part B gradient-coefficient simplification. -/
private theorem partB_gradient_raw_sum_ge_weight_sum
    (S : Setup n Sample) (N : ℕ) (hsteps : PartBStepCondition S N)
    (ξ : ℕ → Sample) :
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
        ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) ≤
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * S.beta k.1 *
        (1 - S.LΨ * S.beta k.1 / 2 -
          S.alpha k.1 * S.lam k.1 / (2 * S.beta k.1)) *
        ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) := by
  classical
  refine Finset.sum_le_sum ?_
  intro k _hk
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let kw : WindowTime N := ⟨k.1, Finset.mem_Icc.mp k.2⟩
  have hcoeff :
      S.beta k.1 * (1 - S.LΨ * S.beta k.1) ≤
        S.beta k.1 *
          (1 - S.LΨ * S.beta k.1 / 2 -
            S.alpha k.1 * S.lam k.1 / (2 * S.beta k.1)) := by
    exact partB_gradient_coeff_weight_ge S N hsteps kw
  have hΓ_nonneg : 0 ≤ (Γ S kp)⁻¹ := le_of_lt (inv_pos.mpr (Γ_pos S kp))
  have hnorm_nonneg : 0 ≤ ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 := sq_nonneg _
  have hscaled :=
    mul_le_mul_of_nonneg_left hcoeff hΓ_nonneg
  have hscaled_norm :=
    mul_le_mul_of_nonneg_right hscaled hnorm_nonneg
  simpa [kp, kw, mul_comm, mul_left_comm, mul_assoc] using hscaled_norm

set_option maxHeartbeats 800000 in
/-- Finite-sum form of the Part B noise-coefficient simplification. -/
private theorem partB_noise_raw_sum_le_budget_sum
    (S : Setup n Sample) (N : ℕ) (hsteps : PartBStepCondition S N)
    (ξ : ℕ → Sample) :
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ *
        ((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1) / 2) *
        ‖generatedOracleErrorAt S kp ξ‖ ^ 2) ≤
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
        ‖generatedOracleErrorAt S kp ξ‖ ^ 2) := by
  classical
  refine Finset.sum_le_sum ?_
  intro k _hk
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let kw : WindowTime N := ⟨k.1, Finset.mem_Icc.mp k.2⟩
  have hcoeff :
      (S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1) / 2 ≤
        S.LΨ * S.beta k.1 ^ 2 :=
    partB_noise_coeff_half_le_Lbeta_sq S N hsteps kw
  have hΓ_nonneg : 0 ≤ (Γ S kp)⁻¹ := le_of_lt (inv_pos.mpr (Γ_pos S kp))
  have hnorm_nonneg : 0 ≤ ‖generatedOracleErrorAt S kp ξ‖ ^ 2 := sq_nonneg _
  have hscaled :=
    mul_le_mul_of_nonneg_left hcoeff hΓ_nonneg
  have hscaled_norm :=
    mul_le_mul_of_nonneg_right hscaled hnorm_nonneg
  simpa [kp, kw, mul_comm, mul_left_comm, mul_assoc] using hscaled_norm

/-- Attached-index form of the Part B squared-distance telescope used after
normalizing the raw Gamma recurrence. -/
private theorem partB_distance_telescope_bound_attach
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hsteps : PartBStepCondition S N) (ξ : ℕ → Sample) (xRef : Space n) :
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      S.alpha k.1 / (2 * S.lam k.1 * Γ S kp) *
        (‖x S ξ (k.1 - 1) - xRef‖ ^ 2 - ‖x S ξ k.1 - xRef‖ ^ 2)) ≤
      (2 * S.lam 1)⁻¹ * ‖S.x0 - xRef‖ ^ 2 := by
  classical
  let coeff : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then S.alpha t / (2 * S.lam t * Γ S ⟨t, ht⟩) else 0
  let V : ℕ → ℝ := fun t => ‖x S ξ t - xRef‖ ^ 2
  have hnat :=
    partB_distance_telescope_bound_nat S N hN hsteps ξ xRef
  have hsum :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        S.alpha k.1 / (2 * S.lam k.1 * Γ S kp) *
          (‖x S ξ (k.1 - 1) - xRef‖ ^ 2 - ‖x S ξ k.1 - xRef‖ ^ 2)) =
        Finset.sum (Finset.Icc 1 N) (fun t => coeff t * (V (t - 1) - V t)) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        S.alpha k.1 / (2 * S.lam k.1 * Γ S kp) *
          (‖x S ξ (k.1 - 1) - xRef‖ ^ 2 - ‖x S ξ k.1 - xRef‖ ^ 2))
          =
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          coeff k.1 * (V (k.1 - 1) - V k.1)) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
            simp [coeff, V, hk1]
      _ = Finset.sum (Finset.Icc 1 N) (fun t => coeff t * (V (t - 1) - V t)) := by
            simpa using
              (Finset.sum_attach (s := Finset.Icc 1 N)
                (f := fun t => coeff t * (V (t - 1) - V t)))
  rw [hsum]
  simpa [coeff, V] using hnat

/-- Raw terminal pathwise Part B bound after Gamma normalization and the
distance telescope, but before the two Part B coefficient simplifications. -/
private theorem partB_pathwise_gamma_terminal_raw_coeff_bound
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N)
    (ξ : ℕ → Sample) (xRef : Space n) :
    (S.Ψ (xBar S ξ N) - S.Ψ xRef) / Γ S ⟨N, hN⟩ ≤
      ((2 * S.lam 1)⁻¹) * ‖S.x0 - xRef‖ ^ 2 -
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 *
            (1 - S.LΨ * S.beta k.1 / 2 -
              S.alpha k.1 * S.lam k.1 / (2 * S.beta k.1)) *
            ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ *
            ((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1) / 2) *
            ‖generatedOracleErrorAt S kp ξ‖ ^ 2) +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ *
            inner ℝ (generatedOracleErrorAt S kp ξ)
              (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                    S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                S.alpha k.1 • (xRef - x S ξ (k.1 - 1)))) := by
  classical
  simpa only [one_div, div_eq_mul_inv] using
    accelerated_gamma_terminal_raw_bound_of_telescope_and_distance
      (fun t => S.Ψ (xBar S ξ t) - S.Ψ xRef)
      S.alpha
      S.beta
      (fun t => 2 * S.lam t)
      (fun t => 1 - S.LΨ * S.beta t / 2 - S.alpha t * S.lam t / (2 * S.beta t))
      (fun t => (S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t) / 2)
      (fun t => ‖x S ξ (t - 1) - xRef‖ ^ 2 - ‖x S ξ t - xRef‖ ^ 2)
      (fun t ht => ‖gradΨ S (xUnder S ξ ⟨t, ht⟩)‖ ^ 2)
      (fun t ht => ‖generatedOracleErrorAt S ⟨t, ht⟩ ξ‖ ^ 2)
      (fun t ht =>
        inner ℝ (generatedOracleErrorAt S ⟨t, ht⟩ ξ)
          (((S.LΨ * S.beta t ^ 2 + S.alpha t * S.lam t - S.beta t) •
              gradΨ S (xUnder S ξ ⟨t, ht⟩)) +
            S.alpha t • (xRef - x S ξ (t - 1))))
      (fun t ht => Γ S ⟨t, ht⟩)
      N hN (((2 * S.lam 1)⁻¹) * ‖S.x0 - xRef‖ ^ 2)
      (hGamma_pos := by simpa using Γ_pos S ⟨N, hN⟩)
      (hGamma_ne := by
        intro t ht
        exact ne_of_gt (Γ_pos S ⟨t, (Finset.mem_Icc.mp ht).1⟩))
      (halpha_ne := by
        intro t ht
        exact ne_of_gt (alpha_pos S ⟨t, (Finset.mem_Icc.mp ht).1⟩))
      (halpha_one := S.halpha_one)
      (htelescope := by
        simpa [hN, one_div, div_eq_mul_inv] using
          partB_pathwise_gamma_telescope_raw S hconvex ξ xRef N hN)
      (hdistance := by
        simpa only [one_div, div_eq_mul_inv] using
          partB_distance_telescope_bound_attach S N hN hsteps ξ xRef)

/-- Source steps 18-20 for Theorem 6.12(b): the raw Gamma telescope, the
distance telescope, and the Part B coefficient conditions give the terminal
pathwise inequality with the displayed simplified weights. -/
private theorem partB_pathwise_gamma_terminal_bound
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N)
    (ξ : ℕ → Sample) (xRef : Space n) :
    (S.Ψ (xBar S ξ N) - S.Ψ xRef) / Γ S ⟨N, hN⟩ ≤
      ((2 * S.lam 1)⁻¹) * ‖S.x0 - xRef‖ ^ 2 -
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
            ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
            ‖generatedOracleErrorAt S kp ξ‖ ^ 2) +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ *
            inner ℝ (generatedOracleErrorAt S kp ξ)
              (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                    S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                S.alpha k.1 • (xRef - x S ξ (k.1 - 1)))) := by
  exact
    terminal_bound_with_simplified_gradient_noise_of_raw_bound
      ((S.Ψ (xBar S ξ N) - S.Ψ xRef) / Γ S ⟨N, hN⟩)
      (((2 * S.lam 1)⁻¹) * ‖S.x0 - xRef‖ ^ 2)
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * S.beta k.1 *
          (1 - S.LΨ * S.beta k.1 / 2 -
            S.alpha k.1 * S.lam k.1 / (2 * S.beta k.1)) *
          ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
          ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ *
          ((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1) / 2) *
          ‖generatedOracleErrorAt S kp ξ‖ ^ 2))
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
          ‖generatedOracleErrorAt S kp ξ‖ ^ 2))
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ *
          inner ℝ (generatedOracleErrorAt S kp ξ)
            (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                  S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
              S.alpha k.1 • (xRef - x S ξ (k.1 - 1)))))
      (by
        simpa using
          partB_pathwise_gamma_terminal_raw_coeff_bound S hconvex N hN hsteps ξ xRef)
      (by
        simpa using partB_gradient_raw_sum_ge_weight_sum S N hsteps ξ)
      (by
        simpa using partB_noise_raw_sum_le_budget_sum S N hsteps ξ)

/-- Source step 21 before integration: with a global minimizer as comparison
point, the terminal function gap is nonnegative and the pathwise Part B bound
isolates the weighted search-gradient sum. -/
private theorem partB_pathwise_weighted_gradient_le_noise_residual
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N)
    (xStar : Space n) (hxStar : ∀ x : Space n, S.Ψ xStar ≤ S.Ψ x)
    (ξ : ℕ → Sample) :
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
        ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) ≤
      ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
            ‖generatedOracleErrorAt S kp ξ‖ ^ 2) +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ *
            inner ℝ (generatedOracleErrorAt S kp ξ)
              (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                    S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))) := by
  exact
    weighted_sum_le_noise_residual_of_nonneg_terminal_bound
      ((S.Ψ (xBar S ξ N) - S.Ψ xStar) / Γ S ⟨N, hN⟩)
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
          ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
      (((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2)
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
          ‖generatedOracleErrorAt S kp ξ‖ ^ 2))
      (Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ *
          inner ℝ (generatedOracleErrorAt S kp ξ)
            (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                  S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
              S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))))
      (by
        have hnum : 0 ≤ S.Ψ (xBar S ξ N) - S.Ψ xStar :=
          sub_nonneg.mpr (hxStar (xBar S ξ N))
        exact div_nonneg hnum (le_of_lt (Γ_pos S ⟨N, hN⟩)))
      (by
        simpa using
          partB_pathwise_gamma_terminal_bound S hconvex N hN hsteps ξ xStar)

/-- The Part B pathwise noise budget integrates to the displayed variance
budget under the adaptive second-moment oracle bound. -/
private theorem partB_noiseBudget_integral_le
    (S : Setup n Sample) (N : ℕ)
    (_hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
          (generatedOracleErrorNormSq S k) (S.σ ^ 2)) :
    (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
        ‖generatedOracleErrorAt S kp ξ‖ ^ 2)
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
      S.LΨ * S.σ ^ 2 *
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 ^ 2) := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let coeff : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2)
  have hmain :
      (∫ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          coeff k *
            ‖generatedOracleErrorAt S
              ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) ∂μ) ≤
        Finset.sum (Finset.Icc 1 N).attach coeff * S.σ ^ 2 :=
    SOptLib.finite_weighted_oracle_second_moment_integral_le
      (μ := μ) (s := (Finset.Icc 1 N).attach) (coeff := coeff)
      (δ := fun k ξ =>
        generatedOracleErrorAt S
          ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ)
      (sigma2 := S.σ ^ 2)
      (by
        intro k _hk
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        exact mul_nonneg (le_of_lt (inv_pos.mpr (Γ_pos S kp)))
          (mul_nonneg (le_of_lt S.hLΨ_pos) (sq_nonneg (S.beta k.1))))
      (by
        intro k _hk
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        have hExp :
            expectationLe μ (generatedOracleErrorNormSq S kp) (S.σ ^ 2) := by
          simpa [μ, kp] using _hSecondMoment kp
        have hpair := (SOptLib.expectationLe_def μ (generatedOracleErrorNormSq S kp)
          (S.σ ^ 2)).1 hExp
        simpa [generatedOracleErrorNormSq, kp] using hpair.1)
      (by
        intro k _hk
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        have hExp :
            expectationLe μ (generatedOracleErrorNormSq S kp) (S.σ ^ 2) := by
          simpa [μ, kp] using _hSecondMoment kp
        have hpair := (SOptLib.expectationLe_def μ (generatedOracleErrorNormSq S kp)
          (S.σ ^ 2)).1 hExp
        simpa [generatedOracleErrorNormSq, kp] using hpair.2)
  simpa [coeff, μ, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Measure-theoretic assembly for the Part B stream gradient bound, once the
martingale residual budget has been shown integrable with zero integral. -/
private theorem partB_stream_weighted_gradient_integral_le_of_residual
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N)
    (xStar : Space n) (hxStar : ∀ x : Space n, S.Ψ xStar ≤ S.Ψ x)
    (_hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
          (generatedOracleErrorNormSq S k) (S.σ ^ 2))
    (hWeightedGradIntegrable :
      Integrable
        (fun ξ : ℕ → Sample =>
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
        (S.sampleStreamLaw : Measure (ℕ → Sample)))
    (hNoiseIntegrable :
      Integrable
        (fun ξ : ℕ → Sample =>
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2))
        (S.sampleStreamLaw : Measure (ℕ → Sample)))
    (hResidualIntegrable :
      Integrable
        (fun ξ : ℕ → Sample =>
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ *
              inner ℝ (generatedOracleErrorAt S kp ξ)
                (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                      S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                  S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))))
        (S.sampleStreamLaw : Measure (ℕ → Sample)))
    (hResidualIntegralZero :
      (∫ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ *
            inner ℝ (generatedOracleErrorAt S kp ξ)
              (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                    S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                S.alpha k.1 • (xStar - x S ξ (k.1 - 1))))
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0) :
    (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
        ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
      ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
        S.LΨ * S.σ ^ 2 *
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 ^ 2) := by
  classical
  exact
    SOptLib.integral_le_const_add_of_ae_le_const_add_add_and_integral_le_and_zero
      (μ := (S.sampleStreamLaw : Measure (ℕ → Sample)))
      (f := fun ξ : ℕ → Sample =>
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
            ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
      (noise := fun ξ : ℕ → Sample =>
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
            ‖generatedOracleErrorAt S kp ξ‖ ^ 2))
      (residual := fun ξ : ℕ → Sample =>
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ *
            inner ℝ (generatedOracleErrorAt S kp ξ)
              (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                    S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))))
      (c := ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2)
      (B := S.LΨ * S.σ ^ 2 *
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 ^ 2))
      hWeightedGradIntegrable hNoiseIntegrable hResidualIntegrable
      (Filter.Eventually.of_forall (fun ξ => by
        simpa using
          partB_pathwise_weighted_gradient_le_noise_residual
            S hconvex N hN hsteps xStar hxStar ξ))
      (by
        simpa using partB_noiseBudget_integral_le S N _hSecondMoment)
      (by
        simpa using hResidualIntegralZero)

/-- Raw part (b) stopping weight `Γ_k⁻¹ β_k (1 - LΨ β_k)`, totalized outside positive time. -/
def partBWeight (S : Setup n Sample) (k : ℕ) : ℝ :=
  if hk : 1 ≤ k then
    (Γ S ⟨k, hk⟩)⁻¹ * S.beta k * (1 - S.LΨ * S.beta k)
  else
    0

/-- The part (b) weights are nonnegative on `1, ..., N` under the paper step conditions. -/
theorem partBWeight_nonneg_of_steps
    (S : Setup n Sample) (N : ℕ) (hsteps : PartBStepCondition S N) :
    ∀ k, k ∈ Finset.Icc 1 N → 0 ≤ partBWeight S k := by
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
  have hbeta_lt : S.beta k < 1 / S.LΨ := hsteps.2.2 ⟨k, hk1, hkN⟩
  have hL_ne : S.LΨ ≠ 0 := ne_of_gt S.hLΨ_pos
  have hright : S.LΨ * (1 / S.LΨ) = 1 := by
    field_simp [hL_ne]
  have hLbeta_lt_one : S.LΨ * S.beta k < 1 := by
    have hmul : S.LΨ * S.beta k < S.LΨ * (1 / S.LΨ) :=
      mul_lt_mul_of_pos_left hbeta_lt S.hLΨ_pos
    rwa [hright] at hmul
  have hfactor_pos : 0 < 1 - S.LΨ * S.beta k := by linarith
  unfold partBWeight
  simp [hk1]
  exact le_of_lt
    (mul_pos (mul_pos (inv_pos.mpr (Γ_pos S ⟨k, hk1⟩)) (S.hbeta_pos k hk1)) hfactor_pos)

/-- The part (b) stopping denominator is positive under the paper step conditions. -/
theorem partBWeight_sum_pos_of_steps
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N) :
    0 < Finset.sum (Finset.Icc 1 N) (partBWeight S) := by
  refine Finset.sum_pos_of_nonempty (Finset.Icc 1 N) (partBWeight S) ?_ ?_
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hbeta_lt : S.beta k < 1 / S.LΨ := hsteps.2.2 ⟨k, hk1, hkN⟩
    have hL_ne : S.LΨ ≠ 0 := ne_of_gt S.hLΨ_pos
    have hright : S.LΨ * (1 / S.LΨ) = 1 := by
      field_simp [hL_ne]
    have hLbeta_lt_one : S.LΨ * S.beta k < 1 := by
      have hmul : S.LΨ * S.beta k < S.LΨ * (1 / S.LΨ) :=
        mul_lt_mul_of_pos_left hbeta_lt S.hLΨ_pos
      rwa [hright] at hmul
    have hfactor_pos : 0 < 1 - S.LΨ * S.beta k := by linarith
    unfold partBWeight
    simp [hk1]
    exact
      mul_pos (mul_pos (inv_pos.mpr (Γ_pos S ⟨k, hk1⟩)) (S.hbeta_pos k hk1)) hfactor_pos
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- The canonical stopping law for Theorem 6.12(b):
`Prob{R=k}=Γ_k⁻¹ β_k(1-LΨβ_k) / ∑ Γτ⁻¹ βτ(1-LΨβτ)`. -/
def partBStoppingLaw
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N) :
    PMF (OutputTime N) :=
  normalizedFiniteWindowPMF (Finset.Icc 1 N) (partBWeight S)
    (partBWeight_nonneg_of_steps S N hsteps)
    (partBWeight_sum_pos_of_steps S N hN hsteps)

/-- The part (b) stopping law has the paper's displayed atom formula. -/
theorem partBStoppingLaw_apply
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N)
    (R : OutputTime N) :
    (partBStoppingLaw S N hN hsteps).toMeasure.real ({R} : Set (OutputTime N)) =
      pPartB S N (outputTimeWindow R) := by
  have hR1 : 1 ≤ R.1 := (Finset.mem_Icc.mp R.2).1
  have hden_attach :
      Finset.sum (Finset.Icc 1 N).attach (fun τ =>
          (Γ S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩)⁻¹ *
            S.beta τ.1 * (1 - S.LΨ * S.beta τ.1)) =
        Finset.sum (Finset.Icc 1 N) (partBWeight S) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun τ =>
          (Γ S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩)⁻¹ *
            S.beta τ.1 * (1 - S.LΨ * S.beta τ.1))
          = Finset.sum (Finset.Icc 1 N).attach (fun τ => partBWeight S τ.1) := by
              refine Finset.sum_congr rfl ?_
              intro τ hτ
              have hτ1 : 1 ≤ τ.1 := (Finset.mem_Icc.mp τ.2).1
              unfold partBWeight
              simp [hτ1]
      _ = Finset.sum (Finset.Icc 1 N) (partBWeight S) := by
              simpa using (Finset.sum_attach (s := Finset.Icc 1 N) (f := partBWeight S))
  have hden_eq :
      Finset.sum (Finset.Icc 1 N) (partBWeight S) =
        Finset.sum (Finset.Icc 1 N).attach (fun τ =>
          (Γ S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩)⁻¹ *
            S.beta τ.1 * (1 - S.LΨ * S.beta τ.1)) := hden_attach.symm
  unfold partBStoppingLaw pPartB outputTimeWindow
  rw [Measure.real_def]
  rw [PMF.toMeasure_apply_singleton _ R (measurableSet_singleton R)]
  rw [normalizedFiniteWindowPMF_apply]
  rw [ENNReal.toReal_ofReal]
  · rw [hden_eq]
    unfold partBWeight
    simp [hR1]
  · exact div_nonneg (partBWeight_nonneg_of_steps S N hsteps R.1 R.2)
      (le_of_lt (partBWeight_sum_pos_of_steps S N hN hsteps))

/-- The displayed part (b) denominator is the finite sum of the totalized
part (b) weights over `1, ..., N`. -/
private theorem partB_display_denominator_eq_partBWeight_sum
    (S : Setup n Sample) (N : ℕ) :
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1)) =
      Finset.sum (Finset.Icc 1 N) (partBWeight S) := by
  calc
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1))
        = Finset.sum (Finset.Icc 1 N).attach (fun k => partBWeight S k.1) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
            unfold partBWeight
            simp [hk1]
    _ = Finset.sum (Finset.Icc 1 N) (partBWeight S) := by
            simpa using (Finset.sum_attach (s := Finset.Icc 1 N) (f := partBWeight S))

/-- The exact part (a) numerator in Theorem 6.12. -/
def partABoundNumerator (S : Setup n Sample) (N : ℕ) : ℝ :=
  S.Ψ S.x0 - Ψstar S +
    (S.LΨ * S.σ ^ 2 / 2) *
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        S.lam k.1 ^ 2 *
          (1 +
            (S.lam k.1 - S.beta k.1) ^ 2 /
              (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
                Finset.sum (Finset.Icc k.1 N).attach
                  (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                    (Finset.mem_Icc.mp τ.2).1⟩)))

/-- The exact part (a) denominator in Theorem 6.12. -/
def partABoundDenominator (S : Setup n Sample) (N : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 N).attach (fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    S.lam k.1 * C S N kp)

/-- The displayed part (a) denominator is strictly positive under the paper's
positive `C_k` condition. -/
private theorem partABoundDenominator_pos
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩) :
    0 < partABoundDenominator S N := by
  have hattach :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp) =
        Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp)
          = Finset.sum (Finset.Icc 1 N).attach (fun k => partAWeight S N k.1) := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
              unfold partAWeight
              simp [hk1]
      _ = Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
              simpa using (Finset.sum_attach (s := Finset.Icc 1 N) (f := partAWeight S N))
  unfold partABoundDenominator
  rw [hattach]
  exact partAWeight_sum_pos_of_C_pos S N hN hC_pos

/-- The displayed part (a) denominator is the finite sum of the totalized
part (a) weights over `1, ..., N`. -/
private theorem partABoundDenominator_eq_partAWeight_sum
    (S : Setup n Sample) (N : ℕ) :
    partABoundDenominator S N =
      Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
  have hattach :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp) =
        Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp)
          = Finset.sum (Finset.Icc 1 N).attach (fun k => partAWeight S N k.1) := by
              refine Finset.sum_congr rfl ?_
              intro k _hk
              have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
              unfold partAWeight
              simp [hk1]
      _ = Finset.sum (Finset.Icc 1 N) (partAWeight S N) := by
              simpa using (Finset.sum_attach (s := Finset.Icc 1 N) (f := partAWeight S N))
  unfold partABoundDenominator
  exact hattach

/-- The pathwise noise budget whose expectation becomes the numerator variance
term in Theorem 6.12(a). -/
private def partAPathwiseNoiseBudget
    (S : Setup n Sample) (N : ℕ) (ξ : ℕ → Sample) : ℝ :=
  (S.LΨ / 2) *
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      S.lam k.1 ^ 2 *
        (1 +
          (S.lam k.1 - S.beta k.1) ^ 2 /
            (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
              Finset.sum (Finset.Icc k.1 N).attach
                  (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                    (Finset.mem_Icc.mp τ.2).1⟩)) *
        ‖generatedOracleErrorAt S kp ξ‖ ^ 2)

/-- The pathwise noise budget has the expected variance contribution from the
second-moment oracle boundary. -/
private theorem partA_noiseBudget_integral_le
    (S : Setup n Sample) (N : ℕ)
    (_hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
          (generatedOracleErrorNormSq S k) (S.σ ^ 2)) :
    (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
      (S.LΨ * S.σ ^ 2 / 2) *
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 ^ 2 *
            (1 +
              (S.lam k.1 - S.beta k.1) ^ 2 /
                (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
                  Finset.sum (Finset.Icc k.1 N).attach
                    (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                      (Finset.mem_Icc.mp τ.2).1⟩))) := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let coeff : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    S.lam k.1 ^ 2 *
      (1 +
        (S.lam k.1 - S.beta k.1) ^ 2 /
          (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
            Finset.sum (Finset.Icc k.1 N).attach
              (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                (Finset.mem_Icc.mp τ.2).1⟩))
  have hcoeff_nonneg : ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N}, 0 ≤ coeff k := by
    intro k
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    have hlam_sq_nonneg : 0 ≤ S.lam k.1 ^ 2 := sq_nonneg (S.lam k.1)
    have htail_nonneg :
        0 ≤ Finset.sum (Finset.Icc k.1 N).attach
          (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
            (Finset.mem_Icc.mp τ.2).1⟩) := by
      refine Finset.sum_nonneg ?_
      intro τ _hτ
      exact le_of_lt (Γ_pos S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
        (Finset.mem_Icc.mp τ.2).1⟩)
    have hden_pos : 0 < S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2 := by
      exact mul_pos (mul_pos (alpha_pos S kp) (Γ_pos S kp))
        (pow_pos (S.hlam_pos k.1 (Finset.mem_Icc.mp k.2).1) 2)
    have hfrac_nonneg :
        0 ≤ (S.lam k.1 - S.beta k.1) ^ 2 /
          (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) := by
      exact div_nonneg (sq_nonneg _) (le_of_lt hden_pos)
    have hbracket_nonneg :
        0 ≤ 1 +
          (S.lam k.1 - S.beta k.1) ^ 2 /
            (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
              Finset.sum (Finset.Icc k.1 N).attach
                (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                  (Finset.mem_Icc.mp τ.2).1⟩) := by
      have hprod := mul_nonneg hfrac_nonneg htail_nonneg
      linarith
    simpa [coeff, kp] using mul_nonneg hlam_sq_nonneg hbracket_nonneg
  have hnorm_int :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        Integrable
          (fun ξ : ℕ → Sample =>
            ‖generatedOracleErrorAt S
              ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) μ := by
    intro k
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    have hExp :
        expectationLe μ (generatedOracleErrorNormSq S kp) (S.σ ^ 2) := by
      simpa [μ, kp] using _hSecondMoment kp
    have hpair := (SOptLib.expectationLe_def μ (generatedOracleErrorNormSq S kp)
      (S.σ ^ 2)).1 hExp
    simpa [generatedOracleErrorNormSq, kp] using hpair.1
  have hnorm_bound :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        (∫ ξ : ℕ → Sample,
          ‖generatedOracleErrorAt S
            ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2 ∂μ) ≤ S.σ ^ 2 := by
    intro k
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    have hExp :
        expectationLe μ (generatedOracleErrorNormSq S kp) (S.σ ^ 2) := by
      simpa [μ, kp] using _hSecondMoment kp
    have hpair := (SOptLib.expectationLe_def μ (generatedOracleErrorNormSq S kp)
      (S.σ ^ 2)).1 hExp
    simpa [generatedOracleErrorNormSq, kp] using hpair.2
  have hterms_int :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            coeff k *
              ‖generatedOracleErrorAt S
                ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) μ := by
    intro k _hk
    exact (hnorm_int k).const_mul (coeff k)
  have hsum_le :
      (∫ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          coeff k *
            ‖generatedOracleErrorAt S
              ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) ∂μ) ≤
        Finset.sum (Finset.Icc 1 N).attach (fun k => coeff k * S.σ ^ 2) := by
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_le_sum ?_
      intro k _hk
      rw [MeasureTheory.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hnorm_bound k) (hcoeff_nonneg k)
    · exact hterms_int
  have hsum_le' :
      (∫ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          coeff k *
            ‖generatedOracleErrorAt S
              ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) ∂μ) ≤
        Finset.sum (Finset.Icc 1 N).attach coeff * S.σ ^ 2 := by
    calc
      (∫ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          coeff k *
            ‖generatedOracleErrorAt S
              ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) ∂μ)
          ≤ Finset.sum (Finset.Icc 1 N).attach (fun k => coeff k * S.σ ^ 2) := hsum_le
      _ = Finset.sum (Finset.Icc 1 N).attach coeff * S.σ ^ 2 := by
            rw [Finset.sum_mul]
  have hLhalf_nonneg : 0 ≤ S.LΨ / 2 := by linarith [S.hLΨ_pos]
  have hscaled :
      (S.LΨ / 2) *
        (∫ ξ : ℕ → Sample,
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            coeff k *
              ‖generatedOracleErrorAt S
                ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) ∂μ) ≤
        (S.LΨ / 2) * (Finset.sum (Finset.Icc 1 N).attach coeff * S.σ ^ 2) :=
    mul_le_mul_of_nonneg_left hsum_le' hLhalf_nonneg
  have hbudget_eq :
      (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂μ) =
        (S.LΨ / 2) *
          (∫ ξ : ℕ → Sample,
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              coeff k *
                ‖generatedOracleErrorAt S
                  ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) ∂μ) := by
    unfold partAPathwiseNoiseBudget
    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))
        = ∫ ξ, partAPathwiseNoiseBudget S N ξ ∂μ := by rfl
    _ = (S.LΨ / 2) *
          (∫ ξ : ℕ → Sample,
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              coeff k *
                ‖generatedOracleErrorAt S
                  ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) ∂μ) := hbudget_eq
    _ ≤ (S.LΨ / 2) * (Finset.sum (Finset.Icc 1 N).attach coeff * S.σ ^ 2) := hscaled
    _ = (S.LΨ * S.σ ^ 2 / 2) *
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 ^ 2 *
            (1 +
              (S.lam k.1 - S.beta k.1) ^ 2 /
                (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
                  Finset.sum (Finset.Icc k.1 N).attach
                    (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                      (Finset.mem_Icc.mp τ.2).1⟩))) := by
          simp [coeff]
          ring

/-- The pathwise part (a) noise budget is integrable under the generated
second-moment oracle boundary. -/
private theorem partA_noiseBudget_integrable
    (S : Setup n Sample) (N : ℕ)
    (_hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
          (generatedOracleErrorNormSq S k) (S.σ ^ 2)) :
    Integrable (fun ξ => partAPathwiseNoiseBudget S N ξ)
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let coeff : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    S.lam k.1 ^ 2 *
      (1 +
        (S.lam k.1 - S.beta k.1) ^ 2 /
          (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
            Finset.sum (Finset.Icc k.1 N).attach
              (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                (Finset.mem_Icc.mp τ.2).1⟩))
  have hnorm_int :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        Integrable
          (fun ξ : ℕ → Sample =>
            ‖generatedOracleErrorAt S
              ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) μ := by
    intro k
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    have hExp :
        expectationLe μ (generatedOracleErrorNormSq S kp) (S.σ ^ 2) := by
      simpa [μ, kp] using _hSecondMoment kp
    have hpair := (SOptLib.expectationLe_def μ (generatedOracleErrorNormSq S kp)
      (S.σ ^ 2)).1 hExp
    simpa [generatedOracleErrorNormSq, kp] using hpair.1
  have hterms_int :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            coeff k *
              ‖generatedOracleErrorAt S
                ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2) μ := by
    intro k _hk
    exact (hnorm_int k).const_mul (coeff k)
  have hsum_int :
      Integrable
        (fun ξ : ℕ → Sample =>
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            coeff k *
              ‖generatedOracleErrorAt S
                ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ξ‖ ^ 2)) μ :=
    MeasureTheory.integrable_finset_sum (s := (Finset.Icc 1 N).attach)
      (μ := μ) hterms_int
  unfold partAPathwiseNoiseBudget
  simpa [coeff, μ] using hsum_int.const_mul (S.LΨ / 2)

/-- The pathwise residual budget `∑ b_k` from Theorem 6.12(a), step 8. -/
private def partAResidualBudget
    (S : Setup n Sample) (N : ℕ) (ξ : ℕ → Sample) : ℝ :=
  Finset.sum (Finset.Icc 1 N).attach (fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
          (Finset.mem_Icc.mp τ.2).1⟩)
    inner ℝ
      (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
        (S.LΨ * S.lam k.1 ^ 2 +
          S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
            (S.alpha k.1 * Γ S kp) * tailΓ) •
            gradΨ S (xUnder S ξ kp))
      (generatedOracleErrorAt S kp ξ))

/-- The residual multiplier in Theorem 6.12(a) is strict-past measurable under
the repaired adaptive-process boundary. -/
private theorem partA_residual_multiplier_measurable_of_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (k : {k : ℕ // k ∈ Finset.Icc 1 N})
    (hAdaptive : AdaptiveOracleProcess S) :
    Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
      (fun ξ : ℕ → Sample =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        let tailΓ : ℝ :=
          Finset.sum (Finset.Icc k.1 N).attach
            (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
              (Finset.mem_Icc.mp τ.2).1⟩)
        S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
          (S.LΨ * S.lam k.1 ^ 2 +
            S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
              (S.alpha k.1 * Γ S kp) * tailΓ) •
            gradΨ S (xUnder S ξ kp)) := by
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let tailΓ : ℝ :=
    Finset.sum (Finset.Icc k.1 N).attach
      (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
        (Finset.mem_Icc.mp τ.2).1⟩)
  have hkpos : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
  have hstate :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
      (k.1 - 1)
  have hx_prev :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hx := hstate.1
    rw [hidx] at hx
    exact hx
  have hxBar_prev :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hxBar := hstate.2
    rw [hidx] at hxBar
    exact hxBar
  have hxUnder :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xUnder S ξ kp) := by
    simpa [kp] using xUnder_measurable_of_prev_measurable S kp hx_prev hxBar_prev
  have hgrad_x :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => gradΨ S (x S ξ (k.1 - 1))) :=
    (gradΨ_measurable S).comp hx_prev
  have hgrad_under :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => gradΨ S (xUnder S ξ kp)) :=
    (gradΨ_measurable S).comp hxUnder
  simpa [kp, tailΓ] using
    (hgrad_x.const_smul (S.lam k.1)).sub
      (hgrad_under.const_smul
        (S.LΨ * S.lam k.1 ^ 2 +
          S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
            (S.alpha k.1 * Γ S kp) * tailΓ))

/-- The residual multiplier in Theorem 6.12(a) is square-integrable under the
adaptive generated-state L2 transport. -/
private theorem partA_residual_multiplier_sq_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (hAdaptive : AdaptiveOracleProcess S)
    (k : {k : ℕ // k ∈ Finset.Icc 1 N}) :
    Integrable
      (fun ξ : ℕ → Sample =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        let tailΓ : ℝ :=
          Finset.sum (Finset.Icc k.1 N).attach
            (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
              (Finset.mem_Icc.mp τ.2).1⟩)
        ‖S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
          (S.LΨ * S.lam k.1 ^ 2 +
            S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
              (S.alpha k.1 * Γ S kp) * tailΓ) •
            gradΨ S (xUnder S ξ kp)‖ ^ 2)
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let tailΓ : ℝ :=
    Finset.sum (Finset.Icc k.1 N).attach
      (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
        (Finset.mem_Icc.mp τ.2).1⟩)
  let coeff : ℝ :=
    S.LΨ * S.lam k.1 ^ 2 +
      S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
        (S.alpha k.1 * Γ S kp) * tailΓ
  have hkpos : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
  have hstate_meas :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
      (k.1 - 1)
  have hx_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hx := hstate_meas.1
    rw [hidx] at hx
    exact hx
  have hxBar_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hxBar := hstate_meas.2
    rw [hidx] at hxBar
    exact hxBar
  have hxUnder_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xUnder S ξ kp) := by
    simpa [kp] using xUnder_measurable_of_prev_measurable S kp
      hx_prev_sub hxBar_prev_sub
  have hgrad_x_meas :
      Measurable (fun ξ : ℕ → Sample => gradΨ S (x S ξ (k.1 - 1))) :=
    ((gradΨ_measurable S).comp hx_prev_sub).mono
      ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hgrad_under_meas :
      Measurable (fun ξ : ℕ → Sample => gradΨ S (xUnder S ξ kp)) :=
    ((gradΨ_measurable S).comp hxUnder_sub).mono
      ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hx_grad_sq :
      Integrable (fun ξ : ℕ → Sample => ‖gradΨ S (x S ξ (k.1 - 1))‖ ^ 2) μ := by
    simpa [μ] using
      generated_raw_gradient_sq_integrable_of_adaptiveOracleProcess S hAdaptive (k.1 - 1)
  have hunder_grad_sq :
      Integrable (fun ξ : ℕ → Sample => ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) μ := by
    simpa [μ, kp] using
      generated_search_gradient_sq_integrable_of_adaptiveOracleProcess S hAdaptive kp
  have hx_grad_l2 :
      MemLp (fun ξ : ℕ → Sample => gradΨ S (x S ξ (k.1 - 1))) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hgrad_x_meas.aestronglyMeasurable).2
      hx_grad_sq
  have hunder_grad_l2 :
      MemLp (fun ξ : ℕ → Sample => gradΨ S (xUnder S ξ kp)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hgrad_under_meas.aestronglyMeasurable).2
      hunder_grad_sq
  have hmult_l2 :
      MemLp
        (fun ξ : ℕ → Sample =>
          S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
            coeff • gradΨ S (xUnder S ξ kp)) 2 μ :=
    (hx_grad_l2.const_smul (S.lam k.1)).sub
      (hunder_grad_l2.const_smul coeff)
  exact
    (memLp_two_iff_integrable_sq_norm hmult_l2.aestronglyMeasurable).1
      (by simpa [kp, tailΓ, coeff, μ] using hmult_l2)

/-- Termwise martingale cancellation for the part (a) residual, once the
residual multiplier is known to be measurable with respect to the past
filtration. -/
private theorem partA_residual_inner_integral_eq_zero_of_multiplier_measurable
    (S : Setup n Sample) (N : ℕ) (k : {k : ℕ // k ∈ Finset.Icc 1 N})
    (_hMeanZero :
      ∀ k : PositiveTime,
        SOptLib.ConditionalExpectation.conditionalExpectationEq
          (S.sampleStreamLaw : Measure (ℕ → Sample))
          ((sampleFiltration (Sample := Sample)).seq k.1)
          (generatedOracleErrorAt S k)
          (0 : (ℕ → Sample) → Space n))
    (hvec_meas :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          let tailΓ : ℝ :=
            Finset.sum (Finset.Icc k.1 N).attach
              (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                (Finset.mem_Icc.mp τ.2).1⟩)
          S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
            (S.LΨ * S.lam k.1 ^ 2 +
              S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                (S.alpha k.1 * Γ S kp) * tailΓ) •
              gradΨ S (xUnder S ξ kp))) :
    (∫ ξ : ℕ → Sample,
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      let tailΓ : ℝ :=
        Finset.sum (Finset.Icc k.1 N).attach
          (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
            (Finset.mem_Icc.mp τ.2).1⟩)
      inner ℝ
        (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
          (S.LΨ * S.lam k.1 ^ 2 +
            S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
              (S.alpha k.1 * Γ S kp) * tailΓ) •
            gradΨ S (xUnder S ξ kp))
        (generatedOracleErrorAt S kp ξ)
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 := by
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let tailΓ : ℝ :=
    Finset.sum (Finset.Icc k.1 N).attach
      (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
        (Finset.mem_Icc.mp τ.2).1⟩)
  let v : (ℕ → Sample) → Space n := fun ξ =>
    S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
      (S.LΨ * S.lam k.1 ^ 2 +
        S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
          (S.alpha k.1 * Γ S kp) * tailΓ) •
        gradΨ S (xUnder S ξ kp)
  have hv_meas :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)] v := by
    simpa [v, kp, tailΓ] using hvec_meas
  have hce := _hMeanZero kp
  rcases SOptLib.ConditionalExpectation.conditionalExpectationEq.wellDefined hce with
    ⟨hm, hsf, hδ_int⟩
  haveI : SigmaFinite ((S.sampleStreamLaw : Measure (ℕ → Sample)).trim hm) := hsf
  have hδ_ce :
      (S.sampleStreamLaw : Measure (ℕ → Sample))[(generatedOracleErrorAt S kp) |
          ((sampleFiltration (Sample := Sample)).seq kp.1)] =ᵐ[
        (S.sampleStreamLaw : Measure (ℕ → Sample))]
          (0 : (ℕ → Sample) → Space n) :=
    SOptLib.ConditionalExpectation.conditionalExpectationEq.ae_eq hce
  have hzero :
      (∫ ξ : ℕ → Sample,
        inner ℝ (generatedOracleErrorAt S kp ξ) ((0 : Space n) - (-v ξ))
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 := by
    exact integral_inner_const_sub_eq_zero_of_condExp_eq_zero
      (P := (S.sampleStreamLaw : Measure (ℕ → Sample)))
      (m := ((sampleFiltration (Sample := Sample)).seq kp.1))
      (δ := generatedOracleErrorAt S kp)
      (x := fun ξ : ℕ → Sample => -v ξ)
      (c := (0 : Space n))
      hm hv_meas.neg hδ_ce hδ_int
  change
    (∫ ξ : ℕ → Sample,
      inner ℝ (v ξ) (generatedOracleErrorAt S kp ξ)
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0
  calc
    (∫ ξ : ℕ → Sample,
      inner ℝ (v ξ) (generatedOracleErrorAt S kp ξ)
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))
        = ∫ ξ : ℕ → Sample,
            inner ℝ (generatedOracleErrorAt S kp ξ) ((0 : Space n) - (-v ξ))
              ∂(S.sampleStreamLaw : Measure (ℕ → Sample)) := by
            apply integral_congr_ae
            filter_upwards with ξ
            simp [real_inner_comm]
    _ = 0 := hzero

/-- Pure one-based lower-triangular sum swap. -/
private theorem sum_Icc_lower_triangular_mul_eq_tail_sum
    (N : ℕ) (γ F : ℕ → ℝ) :
    Finset.sum (Finset.Icc 1 N) (fun k =>
        γ k * Finset.sum (Finset.Icc 1 k) F) =
      Finset.sum (Finset.Icc 1 N) (fun τ =>
        Finset.sum (Finset.Icc τ N) γ * F τ) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      by_cases hN : 1 ≤ N
      · have hleft_succ :
            Finset.sum (Finset.Icc 1 (N + 1)) (fun k =>
                γ k * Finset.sum (Finset.Icc 1 k) F) =
              Finset.sum (Finset.Icc 1 N) (fun k =>
                  γ k * Finset.sum (Finset.Icc 1 k) F) +
                γ (N + 1) * Finset.sum (Finset.Icc 1 (N + 1)) F := by
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        have hright_succ :
            Finset.sum (Finset.Icc 1 (N + 1)) (fun τ =>
                Finset.sum (Finset.Icc τ (N + 1)) γ * F τ) =
              Finset.sum (Finset.Icc 1 N) (fun τ =>
                  Finset.sum (Finset.Icc τ (N + 1)) γ * F τ) +
                γ (N + 1) * F (N + 1) := by
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
          simp
        have htail :
            Finset.sum (Finset.Icc 1 N) (fun τ =>
                Finset.sum (Finset.Icc τ (N + 1)) γ * F τ) =
              Finset.sum (Finset.Icc 1 N) (fun τ =>
                (Finset.sum (Finset.Icc τ N) γ + γ (N + 1)) * F τ) := by
          refine Finset.sum_congr rfl ?_
          intro τ hτ
          have hτN : τ ≤ N := (Finset.mem_Icc.mp hτ).2
          rw [Finset.sum_Icc_succ_top (by omega : τ ≤ N + 1)]
        have hsum_succ :
            Finset.sum (Finset.Icc 1 (N + 1)) F =
              Finset.sum (Finset.Icc 1 N) F + F (N + 1) := by
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
        rw [hleft_succ, hright_succ, ih, htail]
        rw [hsum_succ]
        have hsplit :
            Finset.sum (Finset.Icc 1 N) (fun τ =>
                (Finset.sum (Finset.Icc τ N) γ + γ (N + 1)) * F τ) =
              Finset.sum (Finset.Icc 1 N) (fun τ =>
                  Finset.sum (Finset.Icc τ N) γ * F τ) +
                γ (N + 1) * Finset.sum (Finset.Icc 1 N) F := by
          calc
            Finset.sum (Finset.Icc 1 N) (fun τ =>
                (Finset.sum (Finset.Icc τ N) γ + γ (N + 1)) * F τ)
                = Finset.sum (Finset.Icc 1 N) (fun τ =>
                    Finset.sum (Finset.Icc τ N) γ * F τ + γ (N + 1) * F τ) := by
                    refine Finset.sum_congr rfl ?_
                    intro τ hτ
                    ring
            _ = Finset.sum (Finset.Icc 1 N) (fun τ =>
                    Finset.sum (Finset.Icc τ N) γ * F τ) +
                  Finset.sum (Finset.Icc 1 N) (fun τ => γ (N + 1) * F τ) := by
                    rw [Finset.sum_add_distrib]
            _ = Finset.sum (Finset.Icc 1 N) (fun τ =>
                    Finset.sum (Finset.Icc τ N) γ * F τ) +
                  γ (N + 1) * Finset.sum (Finset.Icc 1 N) F := by
                    rw [Finset.mul_sum]
        rw [hsplit]
        ring
      · have hN0 : N = 0 := by omega
        subst N
        norm_num

/-- Dependent attached version of the lower-triangular reindexing used in the
Part A coefficient collection. -/
private theorem partA_triangular_expanded_sum_reindex
    (S : Setup n Sample) (N : ℕ) (ξ : ℕ → Sample) :
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        Γ S kp *
          Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
            let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
            ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                (Γ S τp * S.alpha τ.1)) *
              (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                  (generatedOracleErrorAt S τp ξ)))) =
      Finset.sum (Finset.Icc 1 N).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        Finset.sum (Finset.Icc τ.1 N).attach
            (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
              (Finset.mem_Icc.mp k.2).1⟩) *
          (((S.lam τ.1 - S.beta τ.1) ^ 2 /
              (Γ S τp * S.alpha τ.1)) *
            (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
              ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
              2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                (generatedOracleErrorAt S τp ξ)))) := by
  classical
  let γ : ℕ → ℝ := fun k =>
    if hk : 1 ≤ k then Γ S ⟨k, hk⟩ else 0
  let F : ℕ → ℝ := fun τ =>
    if hτ : 1 ≤ τ then
      ((S.lam τ - S.beta τ) ^ 2 / (Γ S ⟨τ, hτ⟩ * S.alpha τ)) *
        (‖gradΨ S (xUnder S ξ ⟨τ, hτ⟩)‖ ^ 2 +
          ‖generatedOracleErrorAt S ⟨τ, hτ⟩ ξ‖ ^ 2 +
          2 * inner ℝ (gradΨ S (xUnder S ξ ⟨τ, hτ⟩))
            (generatedOracleErrorAt S ⟨τ, hτ⟩ ξ))
    else 0
  have hgeneric := sum_Icc_lower_triangular_mul_eq_tail_sum N γ F
  have hleft :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        Γ S kp *
          Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
            let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
            ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                (Γ S τp * S.alpha τ.1)) *
              (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                  (generatedOracleErrorAt S τp ξ)))) =
        Finset.sum (Finset.Icc 1 N) (fun k =>
          γ k * Finset.sum (Finset.Icc 1 k) F) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        Γ S kp *
          Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
            let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
            ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                (Γ S τp * S.alpha τ.1)) *
              (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                  (generatedOracleErrorAt S τp ξ))))
          = Finset.sum (Finset.Icc 1 N).attach (fun k =>
              γ k.1 * Finset.sum (Finset.Icc 1 k.1) F) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
              have hγk : Γ S ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ = γ k.1 := by
                simp [γ, hk1]
              have hsumk :
                  Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                    let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
                    ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                        (Γ S τp * S.alpha τ.1)) *
                      (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                        ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                        2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                          (generatedOracleErrorAt S τp ξ)))
                    = Finset.sum (Finset.Icc 1 k.1) F := by
                calc
                  Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                    let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
                    ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                        (Γ S τp * S.alpha τ.1)) *
                      (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                        ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                        2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                          (generatedOracleErrorAt S τp ξ)))
                      = Finset.sum (Finset.Icc 1 k.1).attach (fun τ => F τ.1) := by
                          refine Finset.sum_congr rfl ?_
                          intro τ hτ
                          have hτ1 : 1 ≤ τ.1 := (Finset.mem_Icc.mp τ.2).1
                          simp [F, hτ1]
                  _ = Finset.sum (Finset.Icc 1 k.1) F := by
                          simpa using (Finset.sum_attach
                            (s := Finset.Icc 1 k.1) (f := F))
              change
                Γ S ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
                    Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                      let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
                      ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                          (Γ S τp * S.alpha τ.1)) *
                        (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                          ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                          2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                            (generatedOracleErrorAt S τp ξ))) =
                  γ k.1 * Finset.sum (Finset.Icc 1 k.1) F
              rw [hγk, hsumk]
      _ = Finset.sum (Finset.Icc 1 N) (fun k =>
          γ k * Finset.sum (Finset.Icc 1 k) F) := by
            simpa using (Finset.sum_attach
              (s := Finset.Icc 1 N)
              (f := fun k => γ k * Finset.sum (Finset.Icc 1 k) F))
  have hright :
      Finset.sum (Finset.Icc 1 N).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        Finset.sum (Finset.Icc τ.1 N).attach
            (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
              (Finset.mem_Icc.mp k.2).1⟩) *
          (((S.lam τ.1 - S.beta τ.1) ^ 2 /
              (Γ S τp * S.alpha τ.1)) *
            (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
              ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
              2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                (generatedOracleErrorAt S τp ξ)))) =
        Finset.sum (Finset.Icc 1 N) (fun τ =>
          Finset.sum (Finset.Icc τ N) γ * F τ) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
        Finset.sum (Finset.Icc τ.1 N).attach
            (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
              (Finset.mem_Icc.mp k.2).1⟩) *
          (((S.lam τ.1 - S.beta τ.1) ^ 2 /
              (Γ S τp * S.alpha τ.1)) *
            (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
              ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
              2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                (generatedOracleErrorAt S τp ξ))))
          = Finset.sum (Finset.Icc 1 N).attach (fun τ =>
              Finset.sum (Finset.Icc τ.1 N) γ * F τ.1) := by
              refine Finset.sum_congr rfl ?_
              intro τ hτ
              have hτ1 : 1 ≤ τ.1 := (Finset.mem_Icc.mp τ.2).1
              have htailτ :
                  Finset.sum (Finset.Icc τ.1 N).attach
                      (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
                        (Finset.mem_Icc.mp k.2).1⟩)
                    = Finset.sum (Finset.Icc τ.1 N) γ := by
                calc
                  Finset.sum (Finset.Icc τ.1 N).attach
                      (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
                        (Finset.mem_Icc.mp k.2).1⟩)
                    = Finset.sum (Finset.Icc τ.1 N).attach (fun k => γ k.1) := by
                        refine Finset.sum_congr rfl ?_
                        intro k hk
                        have hk1 : 1 ≤ k.1 :=
                          le_trans hτ1 (Finset.mem_Icc.mp k.2).1
                        simp [γ, hk1]
                  _ = Finset.sum (Finset.Icc τ.1 N) γ := by
                        simpa using (Finset.sum_attach
                          (s := Finset.Icc τ.1 N) (f := γ))
              have hFτ :
                  ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                      (Γ S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩ * S.alpha τ.1)) *
                    (‖gradΨ S (xUnder S ξ ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩)‖ ^ 2 +
                      ‖generatedOracleErrorAt S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩ ξ‖ ^ 2 +
                      2 * inner ℝ
                        (gradΨ S (xUnder S ξ ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩))
                        (generatedOracleErrorAt S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩ ξ)) =
                    F τ.1 := by
                simp [F, hτ1]
              change
                Finset.sum (Finset.Icc τ.1 N).attach
                    (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
                      (Finset.mem_Icc.mp k.2).1⟩) *
                  (((S.lam τ.1 - S.beta τ.1) ^ 2 /
                      (Γ S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩ * S.alpha τ.1)) *
                    (‖gradΨ S (xUnder S ξ ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩)‖ ^ 2 +
                      ‖generatedOracleErrorAt S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩ ξ‖ ^ 2 +
                      2 * inner ℝ
                        (gradΨ S (xUnder S ξ ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩))
                        (generatedOracleErrorAt S ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩ ξ))) =
                Finset.sum (Finset.Icc τ.1 N) γ * F τ.1
              rw [htailτ, hFτ]
      _ = Finset.sum (Finset.Icc 1 N) (fun τ =>
          Finset.sum (Finset.Icc τ N) γ * F τ) := by
            simpa using (Finset.sum_attach
              (s := Finset.Icc 1 N)
              (f := fun τ => Finset.sum (Finset.Icc τ N) γ * F τ))
  rw [hleft, hright]
  exact hgeneric

/-- The gradient-square coefficient produced by the reindexed triangular term is
exactly the displayed `λ_k C_k` coefficient. -/
private theorem partA_gradient_coefficient_collect
    (S : Setup n Sample) (N : ℕ) (k : WindowTime N) (Gsq : ℝ) :
    let kp : PositiveTime := ⟨k.1, k.2.1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans k.2.1 (Finset.mem_Icc.mp τ.2).1⟩);
    -S.lam k.1 * (1 - S.LΨ * S.lam k.1) * Gsq +
        (S.LΨ / 2) * tailΓ *
          ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) * Gsq =
      -(S.lam k.1 * C S N kp) * Gsq := by
  classical
  dsimp
  unfold C
  have hα_ne : S.alpha k.1 ≠ 0 := ne_of_gt (alpha_pos S ⟨k.1, k.2.1⟩)
  have hΓ_ne : Γ S ⟨k.1, k.2.1⟩ ≠ 0 := ne_of_gt (Γ_pos S ⟨k.1, k.2.1⟩)
  have hlam_ne : S.lam k.1 ≠ 0 := ne_of_gt (S.hlam_pos k.1 k.2.1)
  field_simp [hα_ne, hΓ_ne, hlam_ne, C_denominator_ne_zero S ⟨k.1, k.2.1⟩]
  ring

/-- The direct and triangular `δ_k²` coefficients collect to the exact pathwise
noise-budget coefficient. -/
private theorem partA_noise_coefficient_collect
    (S : Setup n Sample) (N : ℕ) (k : WindowTime N) (δsq : ℝ) :
    let kp : PositiveTime := ⟨k.1, k.2.1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans k.2.1 (Finset.mem_Icc.mp τ.2).1⟩);
    (S.LΨ * S.lam k.1 ^ 2 / 2) * δsq +
        (S.LΨ / 2) * tailΓ *
          ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) * δsq =
      (S.LΨ / 2) *
        (S.lam k.1 ^ 2 *
          (1 +
            (S.lam k.1 - S.beta k.1) ^ 2 /
              (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) * tailΓ) *
          δsq) := by
  classical
  dsimp
  have hα_ne : S.alpha k.1 ≠ 0 := ne_of_gt (alpha_pos S ⟨k.1, k.2.1⟩)
  have hΓ_ne : Γ S ⟨k.1, k.2.1⟩ ≠ 0 := ne_of_gt (Γ_pos S ⟨k.1, k.2.1⟩)
  have hlam_ne : S.lam k.1 ≠ 0 := ne_of_gt (S.hlam_pos k.1 k.2.1)
  field_simp [hα_ne, hΓ_ne, hlam_ne]

/-- The original one-step residual and the reindexed cross term collect into
the residual vector `v_k` from Theorem 6.12(a), step 8. -/
private theorem partA_residual_coefficient_collect
    (S : Setup n Sample) (N : ℕ) (ξ : ℕ → Sample) (k : WindowTime N) :
    let kp : PositiveTime := ⟨k.1, k.2.1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans k.2.1 (Finset.mem_Icc.mp τ.2).1⟩);
    -S.lam k.1 *
        inner ℝ
          (gradΨ S (x S ξ (k.1 - 1)) -
            (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
          (generatedOracleErrorAt S kp ξ) +
        (S.LΨ / 2) * tailΓ *
          ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) *
          (2 * inner ℝ (gradΨ S (xUnder S ξ kp))
            (generatedOracleErrorAt S kp ξ)) =
      -inner ℝ
        (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
          (S.LΨ * S.lam k.1 ^ 2 +
            S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
              (S.alpha k.1 * Γ S kp) * tailΓ) •
              gradΨ S (xUnder S ξ kp))
        (generatedOracleErrorAt S kp ξ) := by
  classical
  dsimp
  simp [inner_sub_left, inner_smul_left]
  ring

/-- The objective drops over `1, ..., N` telescope to the initial-terminal gap. -/
private theorem partA_objective_telescope
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → Sample) :
    Finset.sum (Finset.Icc 1 N) (fun k =>
        S.Ψ (x S ξ (k - 1)) - S.Ψ (x S ξ k)) =
      S.Ψ S.x0 - S.Ψ (x S ξ N) := by
  have htel :=
    sum_Icc_sub_succ (fun t => S.Ψ (x S ξ (t - 1))) 1 N hN
  simpa [x_zero, Nat.succ_sub_one] using htel

/-- Source step 6 before triangular reindexing: summing the expanded one-step
descent and telescoping the objective terms. -/
private theorem partA_summed_expanded_descent_raw
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → Sample) :
    S.Ψ (x S ξ N) ≤
      S.Ψ S.x0 +
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
          -S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 +
            (S.LΨ * Γ S kp / 2) *
              Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
                ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                    (Γ S τp * S.alpha τ.1)) *
                  (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                    ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                    2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                      (generatedOracleErrorAt S τp ξ))) +
            (S.LΨ * S.lam k.1 ^ 2 / 2) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2 -
            S.lam k.1 *
              inner ℝ
                (gradΨ S (x S ξ (k.1 - 1)) -
                  (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
                (generatedOracleErrorAt S kp ξ)) := by
  classical
  let R : WindowTime N → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, k.2.1⟩;
    -S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
        ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 +
      (S.LΨ * Γ S kp / 2) *
        Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
          let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
          ((S.lam τ.1 - S.beta τ.1) ^ 2 /
              (Γ S τp * S.alpha τ.1)) *
            (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
              ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
              2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                (generatedOracleErrorAt S τp ξ))) +
      (S.LΨ * S.lam k.1 ^ 2 / 2) *
        ‖generatedOracleErrorAt S kp ξ‖ ^ 2 -
      S.lam k.1 *
        inner ℝ
          (gradΨ S (x S ξ (k.1 - 1)) -
            (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
          (generatedOracleErrorAt S kp ξ)
  have hstepDiff :
      ∀ k : {j : ℕ // j ∈ Finset.Icc 1 N},
        S.Ψ (x S ξ k.1) - S.Ψ (x S ξ (k.1 - 1)) ≤
          R ⟨k.1, Finset.mem_Icc.mp k.2⟩ := by
    intro k
    have hk : WindowTime N := ⟨k.1, Finset.mem_Icc.mp k.2⟩
    have hstep := partA_one_step_descent_with_expanded_gap S ξ
      ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    dsimp [R] at hstep ⊢
    linarith
  have hsumDiff :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        S.Ψ (x S ξ k.1) - S.Ψ (x S ξ (k.1 - 1))) ≤
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        R ⟨k.1, Finset.mem_Icc.mp k.2⟩) :=
    Finset.sum_le_sum (fun k hk => hstepDiff k)
  have htelForward :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        S.Ψ (x S ξ k.1) - S.Ψ (x S ξ (k.1 - 1))) =
        S.Ψ (x S ξ N) - S.Ψ S.x0 := by
    have hobj := partA_objective_telescope S N hN ξ
    have hattach :
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          S.Ψ (x S ξ k.1) - S.Ψ (x S ξ (k.1 - 1))) =
        Finset.sum (Finset.Icc 1 N) (fun k =>
          S.Ψ (x S ξ k) - S.Ψ (x S ξ (k - 1))) := by
      simpa using (Finset.sum_attach
        (s := Finset.Icc 1 N)
        (f := fun k => S.Ψ (x S ξ k) - S.Ψ (x S ξ (k - 1))))
    rw [hattach]
    have hneg :
        Finset.sum (Finset.Icc 1 N) (fun k =>
          S.Ψ (x S ξ k) - S.Ψ (x S ξ (k - 1))) =
        -Finset.sum (Finset.Icc 1 N) (fun k =>
          S.Ψ (x S ξ (k - 1)) - S.Ψ (x S ξ k)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro k hk
      ring
    rw [hneg, hobj]
    ring
  have hRattach :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        R ⟨k.1, Finset.mem_Icc.mp k.2⟩) =
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
          -S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 +
            (S.LΨ * Γ S kp / 2) *
              Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
                ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                    (Γ S τp * S.alpha τ.1)) *
                  (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                    ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                    2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                      (generatedOracleErrorAt S τp ξ))) +
            (S.LΨ * S.lam k.1 ^ 2 / 2) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2 -
            S.lam k.1 *
              inner ℝ
                (gradΨ S (x S ξ (k.1 - 1)) -
                  (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
                (generatedOracleErrorAt S kp ξ)) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rfl
  rw [htelForward] at hsumDiff
  rw [hRattach] at hsumDiff
  linarith

/-- Pure finite-sum collection algebra for the Part A pathwise assembly.  The
triangular contribution is first rewritten globally, then its gradient, noise,
and residual pieces are collected with the direct one-step pieces. -/
private theorem finset_sum_collect_four_of_triangular_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a d e tri gt nt rt wg nb rb : ι → ℝ)
    (htri :
      (Finset.sum s tri) = Finset.sum s (fun k => gt k + nt k + rt k))
    (hG : ∀ k ∈ s, a k + gt k = -wg k)
    (hN : ∀ k ∈ s, d k + nt k = nb k)
    (hR : ∀ k ∈ s, e k + rt k = -rb k) :
    Finset.sum s (fun k => a k + tri k + d k + e k) =
      -(Finset.sum s wg) + Finset.sum s nb - Finset.sum s rb := by
  classical
  calc
    Finset.sum s (fun k => a k + tri k + d k + e k)
        = Finset.sum s a + Finset.sum s tri + Finset.sum s d + Finset.sum s e := by
            simp only [Finset.sum_add_distrib]
    _ = Finset.sum s a + Finset.sum s (fun k => gt k + nt k + rt k) +
          Finset.sum s d + Finset.sum s e := by
            rw [htri]
    _ = Finset.sum s (fun k => a k + gt k) +
          Finset.sum s (fun k => d k + nt k) +
          Finset.sum s (fun k => e k + rt k) := by
            simp only [Finset.sum_add_distrib]
            ring
    _ = Finset.sum s (fun k => -wg k) + Finset.sum s nb +
          Finset.sum s (fun k => -rb k) := by
            rw [Finset.sum_congr rfl hG, Finset.sum_congr rfl hN,
              Finset.sum_congr rfl hR]
    _ = -(Finset.sum s wg) + Finset.sum s nb - Finset.sum s rb := by
            rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
            ring

/-- Source steps 6-8 and the terminal lower bound for Theorem 6.12(a), before
taking expectations and applying the randomized-output law. -/
private theorem partA_pathwise_weighted_gradient_bound
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → Sample) :
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) ≤
    S.Ψ S.x0 - Ψstar S + partAPathwiseNoiseBudget S N ξ -
      partAResidualBudget S N ξ := by
  classical
  have hstepExpanded :
      ∀ k : WindowTime N,
        S.Ψ (x S ξ k.1) ≤
          S.Ψ (x S ξ (k.1 - 1)) -
            S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
              ‖gradΨ S (xUnder S ξ ⟨k.1, k.2.1⟩)‖ ^ 2 +
            (S.LΨ * Γ S ⟨k.1, k.2.1⟩ / 2) *
              Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩
                ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                    (Γ S τp * S.alpha τ.1)) *
                  (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                    ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                    2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                      (generatedOracleErrorAt S τp ξ))) +
            (S.LΨ * S.lam k.1 ^ 2 / 2) *
              ‖generatedOracleErrorAt S ⟨k.1, k.2.1⟩ ξ‖ ^ 2 -
            S.lam k.1 *
              inner ℝ
                (gradΨ S (x S ξ (k.1 - 1)) -
                  (S.LΨ * S.lam k.1) •
                    gradΨ S (xUnder S ξ ⟨k.1, k.2.1⟩))
                (generatedOracleErrorAt S ⟨k.1, k.2.1⟩ ξ) := by
    intro k
    simpa using partA_one_step_descent_with_expanded_gap S ξ ⟨k.1, k.2.1⟩
  have hobjective :=
    partA_objective_telescope S N hN ξ
  have hrawSummed :=
    partA_summed_expanded_descent_raw S N hN ξ
  have htriangular :=
    partA_triangular_expanded_sum_reindex S N ξ
  have hterminalLower : Ψstar S ≤ S.Ψ (x S ξ N) :=
    Ψstar_le_value S (x S ξ N)
  have hCcollect :
      ∀ k : WindowTime N,
        let kp : PositiveTime := ⟨k.1, k.2.1⟩;
        let tailΓ : ℝ :=
          Finset.sum (Finset.Icc k.1 N).attach
            (fun τ => Γ S ⟨τ.1, le_trans k.2.1 (Finset.mem_Icc.mp τ.2).1⟩);
        -S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 +
            (S.LΨ / 2) * tailΓ *
              ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 =
          -(S.lam k.1 * C S N kp) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 :=
    fun k => partA_gradient_coefficient_collect S N k
      (‖gradΨ S (xUnder S ξ ⟨k.1, k.2.1⟩)‖ ^ 2)
  have hNoiseCollect :
      ∀ k : WindowTime N,
        let kp : PositiveTime := ⟨k.1, k.2.1⟩;
        let tailΓ : ℝ :=
          Finset.sum (Finset.Icc k.1 N).attach
            (fun τ => Γ S ⟨τ.1, le_trans k.2.1 (Finset.mem_Icc.mp τ.2).1⟩);
        (S.LΨ * S.lam k.1 ^ 2 / 2) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2 +
            (S.LΨ / 2) * tailΓ *
              ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2 =
          (S.LΨ / 2) *
            (S.lam k.1 ^ 2 *
              (1 +
                (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) * tailΓ) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2) :=
    fun k => partA_noise_coefficient_collect S N k
      (‖generatedOracleErrorAt S ⟨k.1, k.2.1⟩ ξ‖ ^ 2)
  have hResidualCollect :
      ∀ k : WindowTime N,
        let kp : PositiveTime := ⟨k.1, k.2.1⟩;
        let tailΓ : ℝ :=
          Finset.sum (Finset.Icc k.1 N).attach
            (fun τ => Γ S ⟨τ.1, le_trans k.2.1 (Finset.mem_Icc.mp τ.2).1⟩);
        -S.lam k.1 *
            inner ℝ
              (gradΨ S (x S ξ (k.1 - 1)) -
                (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
              (generatedOracleErrorAt S kp ξ) +
            (S.LΨ / 2) * tailΓ *
              ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) *
              (2 * inner ℝ (gradΨ S (xUnder S ξ kp))
                (generatedOracleErrorAt S kp ξ)) =
          -inner ℝ
            (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1 ^ 2 +
                S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp) * tailΓ) •
                  gradΨ S (xUnder S ξ kp))
          (generatedOracleErrorAt S kp ξ) :=
    fun k => partA_residual_coefficient_collect S N ξ k
  let a : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    -S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
      ‖gradΨ S (xUnder S ξ kp)‖ ^ 2
  let d : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    (S.LΨ * S.lam k.1 ^ 2 / 2) *
      ‖generatedOracleErrorAt S kp ξ‖ ^ 2
  let e : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    -S.lam k.1 *
      inner ℝ
        (gradΨ S (x S ξ (k.1 - 1)) -
          (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
        (generatedOracleErrorAt S kp ξ)
  let tri : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    (S.LΨ * Γ S kp / 2) *
      Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
        let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
        ((S.lam τ.1 - S.beta τ.1) ^ 2 /
            (Γ S τp * S.alpha τ.1)) *
          (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
            ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
            2 * inner ℝ (gradΨ S (xUnder S ξ τp))
              (generatedOracleErrorAt S τp ξ)))
  let gt : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
          (Finset.mem_Icc.mp τ.2).1⟩);
    (S.LΨ / 2) * tailΓ *
      ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) *
      ‖gradΨ S (xUnder S ξ kp)‖ ^ 2
  let nt : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
          (Finset.mem_Icc.mp τ.2).1⟩);
    (S.LΨ / 2) * tailΓ *
      ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) *
      ‖generatedOracleErrorAt S kp ξ‖ ^ 2
  let rt : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
          (Finset.mem_Icc.mp τ.2).1⟩);
    (S.LΨ / 2) * tailΓ *
      ((S.lam k.1 - S.beta k.1) ^ 2 / (Γ S kp * S.alpha k.1)) *
      (2 * inner ℝ (gradΨ S (xUnder S ξ kp))
        (generatedOracleErrorAt S kp ξ))
  let wg : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2
  let nb : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
          (Finset.mem_Icc.mp τ.2).1⟩);
    (S.LΨ / 2) *
      (S.lam k.1 ^ 2 *
        (1 +
          (S.lam k.1 - S.beta k.1) ^ 2 /
            (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) * tailΓ) *
        ‖generatedOracleErrorAt S kp ξ‖ ^ 2)
  let rb : {k : ℕ // k ∈ Finset.Icc 1 N} → ℝ := fun k =>
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
    let tailΓ : ℝ :=
      Finset.sum (Finset.Icc k.1 N).attach
        (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
          (Finset.mem_Icc.mp τ.2).1⟩);
    inner ℝ
      (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
        (S.LΨ * S.lam k.1 ^ 2 +
          S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
            (S.alpha k.1 * Γ S kp) * tailΓ) •
            gradΨ S (xUnder S ξ kp))
      (generatedOracleErrorAt S kp ξ)
  have htriCollect :
      Finset.sum (Finset.Icc 1 N).attach tri =
        Finset.sum (Finset.Icc 1 N).attach (fun k => gt k + nt k + rt k) := by
    calc
      Finset.sum (Finset.Icc 1 N).attach tri
          =
        (S.LΨ / 2) *
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
            Γ S kp *
              Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
                ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                    (Γ S τp * S.alpha τ.1)) *
                  (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                    ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                    2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                      (generatedOracleErrorAt S τp ξ)))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            dsimp [tri]
            ring
      _ =
        (S.LΨ / 2) *
          Finset.sum (Finset.Icc 1 N).attach (fun τ =>
            let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
            Finset.sum (Finset.Icc τ.1 N).attach
                (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
                  (Finset.mem_Icc.mp k.2).1⟩) *
              (((S.lam τ.1 - S.beta τ.1) ^ 2 /
                  (Γ S τp * S.alpha τ.1)) *
                (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                  ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                  2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                    (generatedOracleErrorAt S τp ξ)))) := by
            rw [htriangular]
      _ =
        Finset.sum (Finset.Icc 1 N).attach (fun τ =>
          (S.LΨ / 2) *
            (let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
             Finset.sum (Finset.Icc τ.1 N).attach
                (fun k => Γ S ⟨k.1, le_trans (Finset.mem_Icc.mp τ.2).1
                  (Finset.mem_Icc.mp k.2).1⟩) *
              (((S.lam τ.1 - S.beta τ.1) ^ 2 /
                  (Γ S τp * S.alpha τ.1)) *
                (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                  ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                  2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                    (generatedOracleErrorAt S τp ξ))))) := by
            rw [Finset.mul_sum]
      _ = Finset.sum (Finset.Icc 1 N).attach (fun k => gt k + nt k + rt k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            dsimp [gt, nt, rt]
            ring
  have hG :
      ∀ k ∈ (Finset.Icc 1 N).attach, a k + gt k = -wg k := by
    intro k hk
    let hk' : WindowTime N := ⟨k.1, Finset.mem_Icc.mp k.2⟩
    have h := hCcollect hk'
    dsimp [a, gt, wg] at h ⊢
    simpa [hk'] using h
  have hNoise :
      ∀ k ∈ (Finset.Icc 1 N).attach, d k + nt k = nb k := by
    intro k hk
    let hk' : WindowTime N := ⟨k.1, Finset.mem_Icc.mp k.2⟩
    have h := hNoiseCollect hk'
    dsimp [d, nt, nb] at h ⊢
    simpa [hk'] using h
  have hResidual :
      ∀ k ∈ (Finset.Icc 1 N).attach, e k + rt k = -rb k := by
    intro k hk
    let hk' : WindowTime N := ⟨k.1, Finset.mem_Icc.mp k.2⟩
    have h := hResidualCollect hk'
    dsimp [e, rt, rb] at h ⊢
    simpa [hk'] using h
  have hcollected :=
    finset_sum_collect_four_of_triangular_sum
      (s := (Finset.Icc 1 N).attach) a d e tri gt nt rt wg nb rb
      htriCollect hG hNoise hResidual
  have hNoiseBudget :
      Finset.sum (Finset.Icc 1 N).attach nb =
        partAPathwiseNoiseBudget S N ξ := by
    unfold partAPathwiseNoiseBudget
    dsimp [nb]
    rw [Finset.mul_sum]
  have hResidualBudget :
      Finset.sum (Finset.Icc 1 N).attach rb =
        partAResidualBudget S N ξ := by
    unfold partAResidualBudget
    rfl
  have hcollect :
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
          -S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 +
            (S.LΨ * Γ S kp / 2) *
              Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
                ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                    (Γ S τp * S.alpha τ.1)) *
                  (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                    ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                    2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                      (generatedOracleErrorAt S τp ξ))) +
            (S.LΨ * S.lam k.1 ^ 2 / 2) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2 -
            S.lam k.1 *
              inner ℝ
                (gradΨ S (x S ξ (k.1 - 1)) -
                  (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
                (generatedOracleErrorAt S kp ξ)) =
        -(Finset.sum (Finset.Icc 1 N).attach wg) +
          partAPathwiseNoiseBudget S N ξ - partAResidualBudget S N ξ := by
    calc
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩;
          -S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2 +
            (S.LΨ * Γ S kp / 2) *
              Finset.sum (Finset.Icc 1 k.1).attach (fun τ =>
                let τp : PositiveTime := ⟨τ.1, (Finset.mem_Icc.mp τ.2).1⟩;
                ((S.lam τ.1 - S.beta τ.1) ^ 2 /
                    (Γ S τp * S.alpha τ.1)) *
                  (‖gradΨ S (xUnder S ξ τp)‖ ^ 2 +
                    ‖generatedOracleErrorAt S τp ξ‖ ^ 2 +
                    2 * inner ℝ (gradΨ S (xUnder S ξ τp))
                      (generatedOracleErrorAt S τp ξ))) +
            (S.LΨ * S.lam k.1 ^ 2 / 2) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2 -
            S.lam k.1 *
              inner ℝ
                (gradΨ S (x S ξ (k.1 - 1)) -
                  (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ kp))
                (generatedOracleErrorAt S kp ξ))
          = Finset.sum (Finset.Icc 1 N).attach
              (fun k => a k + tri k + d k + e k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              dsimp [a, tri, d, e]
              ring
      _ = -(Finset.sum (Finset.Icc 1 N).attach wg) +
            Finset.sum (Finset.Icc 1 N).attach nb -
            Finset.sum (Finset.Icc 1 N).attach rb := hcollected
      _ = -(Finset.sum (Finset.Icc 1 N).attach wg) +
            partAPathwiseNoiseBudget S N ξ - partAResidualBudget S N ξ := by
              rw [hNoiseBudget, hResidualBudget]
  have hdescent :
      S.Ψ (x S ξ N) ≤
        S.Ψ S.x0 +
          (-(Finset.sum (Finset.Icc 1 N).attach wg) +
            partAPathwiseNoiseBudget S N ξ - partAResidualBudget S N ξ) := by
    have h := hrawSummed
    rw [hcollect] at h
    simpa using h
  have hstar :
      Ψstar S ≤
        S.Ψ S.x0 +
          (-(Finset.sum (Finset.Icc 1 N).attach wg) +
            partAPathwiseNoiseBudget S N ξ - partAResidualBudget S N ξ) :=
    le_trans hterminalLower hdescent
  have hbound :
      Finset.sum (Finset.Icc 1 N).attach wg ≤
        S.Ψ S.x0 - Ψstar S + partAPathwiseNoiseBudget S N ξ -
          partAResidualBudget S N ξ := by
    linarith
  simpa [wg] using hbound

/-- The paper output pair `(underline x_R, bar x_R)` as a function of
`(R, ξ_[N])`. -/
def selectedOutputPair (S : Setup n Sample) (N : ℕ)
    (q : OutputTime N × SamplePrefix (Sample := Sample) N) : Space n × Space n :=
  (xUnderPrefix S N q.2 q.1, xBarPrefix S N q.2 q.1.1)

/-- The selected search point `underline x_R`, projected from the paper output pair. -/
def selectedSearchPoint (S : Setup n Sample) (N : ℕ)
    (q : OutputTime N × SamplePrefix (Sample := Sample) N) : Space n :=
  (selectedOutputPair S N q).1

/-- The selected averaged point `bar x_R`, projected from the paper output pair. -/
def selectedAveragedPoint (S : Setup n Sample) (N : ℕ)
    (q : OutputTime N × SamplePrefix (Sample := Sample) N) : Space n :=
  (selectedOutputPair S N q).2

@[simp]
theorem selectedSearchPoint_eq (S : Setup n Sample) (N : ℕ)
    (q : OutputTime N × SamplePrefix (Sample := Sample) N) :
    selectedSearchPoint S N q = xUnderPrefix S N q.2 q.1 := by
  rfl

@[simp]
theorem selectedAveragedPoint_eq (S : Setup n Sample) (N : ℕ)
    (q : OutputTime N × SamplePrefix (Sample := Sample) N) :
    selectedAveragedPoint S N q = xBarPrefix S N q.2 q.1.1 := by
  rfl

/-- The selected squared-gradient certificate at the randomized search point,
projected from the paper output pair `(underline x_R, bar x_R)`. -/
def selectedGradNormSq (S : Setup n Sample) (N : ℕ)
    (q : OutputTime N × SamplePrefix (Sample := Sample) N) : ℝ :=
  ‖gradΨ S (selectedSearchPoint S N q)‖ ^ 2

/-- Extend a finite theorem prefix to a full stream by reusing the selected
output sample outside the theorem window. -/
private def samplePrefixExtend {N : ℕ} (R : OutputTime N)
    (pref : SamplePrefix (Sample := Sample) N) : ℕ → Sample :=
  fun t =>
    if ht : t ∈ Finset.Icc 1 N then
      pref ⟨t, ht⟩
    else
      pref R

/-- The finite-prefix extension is measurable coordinatewise. -/
private theorem samplePrefixExtend_measurable {N : ℕ} (R : OutputTime N) :
    Measurable (samplePrefixExtend (Sample := Sample) R) := by
  simpa [samplePrefixExtend, SOptLib.subtypeExtendWithDefault] using
    (SOptLib.measurable_subtype_extend_with_default
      (A := Sample) (p := fun k : ℕ => k ∈ Finset.Icc 1 N) R)

/-- Projecting the deterministic extension recovers the original finite prefix. -/
private theorem samplePrefix_samplePrefixExtend {N : ℕ} (R : OutputTime N)
    (pref : SamplePrefix (Sample := Sample) N) :
    samplePrefix (Sample := Sample) (N := N) (samplePrefixExtend R pref) = pref := by
  funext k
  simp [samplePrefix, samplePrefixExtend, k.2]

/-- The finite-prefix selected search-gradient norm square is measurable under
the finite-prefix product sigma algebra. -/
private theorem partA_prefix_grad_norm_sq_measurable_of_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (hAdaptive : AdaptiveOracleProcess S)
    (R : OutputTime N) :
    Measurable
      (fun pref : SamplePrefix (Sample := Sample) N =>
        ‖gradΨ S (xUnderPrefix S N pref R)‖ ^ 2) := by
  have hstream :
      Measurable
        (fun ξ : ℕ → Sample =>
          ‖gradΨ S (xUnder S ξ (outputTimePositive R))‖ ^ 2) :=
    generated_search_gradient_norm_sq_measurable_of_adaptiveOracleProcess
      S hAdaptive (outputTimePositive R)
  have hcomp :
      Measurable
        (fun pref : SamplePrefix (Sample := Sample) N =>
          ‖gradΨ S (xUnder S (samplePrefixExtend R pref) (outputTimePositive R))‖ ^ 2) :=
    hstream.comp (samplePrefixExtend_measurable (Sample := Sample) R)
  have hfun :
      (fun pref : SamplePrefix (Sample := Sample) N =>
          ‖gradΨ S (xUnder S (samplePrefixExtend R pref) (outputTimePositive R))‖ ^ 2) =
        fun pref : SamplePrefix (Sample := Sample) N =>
          ‖gradΨ S (xUnderPrefix S N pref R)‖ ^ 2 := by
    funext pref
    have hsection := samplePrefix_samplePrefixExtend (Sample := Sample) R pref
    calc
      ‖gradΨ S (xUnder S (samplePrefixExtend R pref) (outputTimePositive R))‖ ^ 2 =
          ‖gradΨ S
            (xUnderPrefix S N
              (samplePrefix (Sample := Sample) (N := N) (samplePrefixExtend R pref)) R)‖ ^ 2 := by
            rw [xUnderPrefix_eq_stream_of_same_prefix S N (samplePrefixExtend R pref) R]
      _ = ‖gradΨ S (xUnderPrefix S N pref R)‖ ^ 2 := by
            rw [hsection]
  rw [hfun] at hcomp
  exact hcomp

/-- The selected convex-case function-gap certificate at the randomized averaged point,
projected from the paper output pair `(underline x_R, bar x_R)`. -/
def selectedFunctionGap (S : Setup n Sample) (N : ℕ) (xStar : Space n)
    (q : OutputTime N × SamplePrefix (Sample := Sample) N) : ℝ :=
  S.Ψ (selectedAveragedPoint S N q) - S.Ψ xStar

/-- Theorem 6.12(a)'s joint law of `R` and the finite prefix `ξ_[N]`. -/
def selectedJointLawPartA
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩) :
    Measure (OutputTime N × SamplePrefix (Sample := Sample) N) :=
  selected_joint_measure (partAStoppingLaw S N hN hC_pos) (samplePrefixLaw S N)

/-- Theorem 6.12(b)'s joint law of `R` and the finite prefix `ξ_[N]`. -/
def selectedJointLawPartB
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N) (hsteps : PartBStepCondition S N) :
    Measure (OutputTime N × SamplePrefix (Sample := Sample) N) :=
  selected_joint_measure (partBStoppingLaw S N hN hsteps) (samplePrefixLaw S N)

/-- Technical L1 side condition for the part (a) selected-output expansion:
each finite-prefix generated search-gradient square is integrable. -/
private theorem partA_generated_grad_norm_sq_prefix_integrable
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩)
    (hAdaptive : AdaptiveOracleProcess S) (R : OutputTime N) :
    Integrable
      (fun pref : SamplePrefix (Sample := Sample) N =>
        ‖gradΨ S (xUnderPrefix S N pref R)‖ ^ 2)
      (samplePrefixLaw S N) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let φ : SamplePrefix (Sample := Sample) N → ℝ := fun pref =>
    ‖gradΨ S (xUnderPrefix S N pref R)‖ ^ 2
  have hφ_meas : Measurable φ := by
    simpa [φ] using
      partA_prefix_grad_norm_sq_measurable_of_adaptiveOracleProcess S N hAdaptive R
  have hcomp : Integrable (φ ∘ samplePrefix (Sample := Sample) (N := N)) μ := by
    have hstream :=
      generated_search_gradient_sq_integrable_of_adaptiveOracleProcess
        S hAdaptive (outputTimePositive R)
    have hfun :
        (φ ∘ samplePrefix (Sample := Sample) (N := N)) =
          fun ξ : ℕ → Sample =>
            ‖gradΨ S (xUnder S ξ (outputTimePositive R))‖ ^ 2 := by
      funext ξ
      simp [φ, Function.comp_def, xUnderPrefix_eq_stream_of_same_prefix S N ξ R]
    rw [hfun]
    simpa [μ] using hstream
  have hmap :=
    integrable_map_measure_of_integrable_comp
      (P := μ) (Y := samplePrefix (Sample := Sample) (N := N)) (φ := φ)
      hφ_meas.aestronglyMeasurable
      (samplePrefix_measurable (Sample := Sample) N).aemeasurable hcomp
  simpa [φ, samplePrefixLaw, μ] using hmap

/-- Technical L1 side condition for the part (b) selected-output expansion:
each finite-prefix generated search-gradient square is integrable. -/
private theorem partB_generated_grad_norm_sq_prefix_integrable
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hAdaptive : AdaptiveOracleProcess S) (R : OutputTime N) :
    Integrable
      (fun pref : SamplePrefix (Sample := Sample) N =>
        ‖gradΨ S (xUnderPrefix S N pref R)‖ ^ 2)
      (samplePrefixLaw S N) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let φ : SamplePrefix (Sample := Sample) N → ℝ := fun pref =>
    ‖gradΨ S (xUnderPrefix S N pref R)‖ ^ 2
  have hφ_meas : Measurable φ := by
    simpa [φ] using
      partA_prefix_grad_norm_sq_measurable_of_adaptiveOracleProcess S N hAdaptive R
  have hcomp : Integrable (φ ∘ samplePrefix (Sample := Sample) (N := N)) μ := by
    have hstream :=
      generated_search_gradient_sq_integrable_of_adaptiveOracleProcess
        S hAdaptive (outputTimePositive R)
    have hfun :
        (φ ∘ samplePrefix (Sample := Sample) (N := N)) =
          fun ξ : ℕ → Sample =>
            ‖gradΨ S (xUnder S ξ (outputTimePositive R))‖ ^ 2 := by
      funext ξ
      simp [φ, Function.comp_def, xUnderPrefix_eq_stream_of_same_prefix S N ξ R]
    rw [hfun]
    simpa [μ] using hstream
  have hmap :=
    integrable_map_measure_of_integrable_comp
      (P := μ) (Y := samplePrefix (Sample := Sample) (N := N)) (φ := φ)
      hφ_meas.aestronglyMeasurable
      (samplePrefix_measurable (Sample := Sample) N).aemeasurable hcomp
  simpa [φ, samplePrefixLaw, μ] using hmap

/-- Technical L1 side condition for the part (b) selected-output function-gap
expansion: each finite-prefix generated averaged-iterate gap is integrable. -/
private theorem partB_generated_xBar_function_gap_prefix_integrable
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hAdaptive : AdaptiveOracleProcess S) (xStar : Space n) (R : OutputTime N) :
    Integrable
      (fun pref : SamplePrefix (Sample := Sample) N =>
        S.Ψ (xBarPrefix S N pref R.1) - S.Ψ xStar)
      (samplePrefixLaw S N) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let φ : SamplePrefix (Sample := Sample) N → ℝ := fun pref =>
    S.Ψ (xBarPrefix S N pref R.1) - S.Ψ xStar
  have hstream_meas :
      Measurable
        (fun ξ : ℕ → Sample => S.Ψ (xBar S ξ R.1) - S.Ψ xStar) := by
    have hstate_meas :=
      generated_state_adapted_from_error_observable S
        (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
    have hxBar_sub :
        Measurable[((sampleFiltration (Sample := Sample)).seq (R.1 + 1))]
          (fun ξ : ℕ → Sample => xBar S ξ R.1) :=
      (hstate_meas R.1).2
    have hxBar_meas : Measurable (fun ξ : ℕ → Sample => xBar S ξ R.1) :=
      hxBar_sub.mono ((sampleFiltration (Sample := Sample)).le (R.1 + 1)) le_rfl
    exact (S.hDifferentiable.continuous.measurable.comp hxBar_meas).sub measurable_const
  have hφ_meas : Measurable φ := by
    have hcomp :
        Measurable
          (fun pref : SamplePrefix (Sample := Sample) N =>
            S.Ψ (xBar S (samplePrefixExtend R pref) R.1) - S.Ψ xStar) :=
      hstream_meas.comp (samplePrefixExtend_measurable (Sample := Sample) R)
    have hfun :
        (fun pref : SamplePrefix (Sample := Sample) N =>
            S.Ψ (xBar S (samplePrefixExtend R pref) R.1) - S.Ψ xStar) = φ := by
      funext pref
      have hsection := samplePrefix_samplePrefixExtend (Sample := Sample) R pref
      have hRle : R.1 ≤ N := (Finset.mem_Icc.mp R.2).2
      calc
        S.Ψ (xBar S (samplePrefixExtend R pref) R.1) - S.Ψ xStar =
            S.Ψ
              (xBarPrefix S N
                (samplePrefix (Sample := Sample) (N := N) (samplePrefixExtend R pref))
                R.1) - S.Ψ xStar := by
              rw [xBarPrefix_eq_stream_of_same_prefix S N (samplePrefixExtend R pref)
                R.1 hRle]
        _ = S.Ψ (xBarPrefix S N pref R.1) - S.Ψ xStar := by
              rw [hsection]
    rw [hfun] at hcomp
    exact hcomp
  have hcomp_int : Integrable (φ ∘ samplePrefix (Sample := Sample) (N := N)) μ := by
    have hstream :=
      generated_xBar_function_gap_integrable_of_adaptiveOracleProcess
        S hAdaptive xStar R.1
    have hfun :
        (φ ∘ samplePrefix (Sample := Sample) (N := N)) =
          fun ξ : ℕ → Sample => S.Ψ (xBar S ξ R.1) - S.Ψ xStar := by
      funext ξ
      have hRle : R.1 ≤ N := (Finset.mem_Icc.mp R.2).2
      simp [φ, Function.comp_def,
        xBarPrefix_eq_stream_of_same_prefix S N ξ R.1 hRle]
    rw [hfun]
    simpa [μ] using hstream
  have hmap :=
    integrable_map_measure_of_integrable_comp
      (P := μ) (Y := samplePrefix (Sample := Sample) (N := N)) (φ := φ)
      hφ_meas.aestronglyMeasurable
      (samplePrefix_measurable (Sample := Sample) N).aemeasurable hcomp_int
  simpa [φ, samplePrefixLaw, μ] using hmap

/-- The part (a) randomized output law expands to the normalized weighted
finite-window stream expectation. -/
private theorem partA_selected_grad_integral_eq_stream_weighted
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩)
    (hAdaptive : AdaptiveOracleProcess S) :
    (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartA S N hN hC_pos) =
      (partABoundDenominator S N)⁻¹ *
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
  classical
  let xsel : ℕ → SamplePrefix (Sample := Sample) N → Space n := fun k pref =>
    if hk : k ∈ Finset.Icc 1 N then
      xUnderPrefix S N pref ⟨k, hk⟩
    else
      S.x0
  let gap : Space n → ℝ := fun z => ‖gradΨ S z‖ ^ 2
  have hgap_int :
      ∀ R : {k : ℕ // k ∈ Finset.Icc 1 N},
        Integrable (fun pref => gap (xsel R.1 pref)) (samplePrefixLaw S N) := by
    intro R
    have hR :=
      partA_generated_grad_norm_sq_prefix_integrable S N hN hC_pos hAdaptive
        (R : OutputTime N)
    have hmem : R.1 ∈ Finset.Icc 1 N := R.2
    have hcond : 1 ≤ R.1 ∧ R.1 ≤ N := Finset.mem_Icc.mp hmem
    simpa [gap, xsel, hcond] using hR
  haveI : SFinite (samplePrefixLaw S N) := by
    unfold samplePrefixLaw
    infer_instance
  have hselected_raw :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := Finset.Icc 1 N) (α := partAWeight S N)
      (P := samplePrefixLaw S N) (x := xsel) (gap := gap)
      (partAWeight_nonneg_of_C_pos S N hC_pos)
      (partAWeight_sum_pos_of_C_pos S N hN hC_pos)
      hgap_int
  have hselected_prefix :
      (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartA S N hN hC_pos) =
      (Finset.sum (Finset.Icc 1 N) (partAWeight S N))⁻¹ *
          Finset.sum (Finset.Icc 1 N)
            (fun k => partAWeight S N k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) := by
    have hselected_lhs :
        (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartA S N hN hC_pos) =
          (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
            gap (xsel q.1.1 q.2) ∂selectedJointLawPartA S N hN hC_pos) := by
      apply integral_congr_ae
      filter_upwards with q
      have hq : q.1.1 ∈ Finset.Icc 1 N := q.1.2
      have hqcond : 1 ≤ q.1.1 ∧ q.1.1 ≤ N := Finset.mem_Icc.mp hq
      simp [selectedGradNormSq, selectedSearchPoint_eq, selectedOutputPair,
        selectedSearchPoint, gap, xsel, hqcond]
    calc
      (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartA S N hN hC_pos)
          =
        (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
          gap (xsel q.1.1 q.2) ∂selectedJointLawPartA S N hN hC_pos) := hselected_lhs
      _ =
        (Finset.sum (Finset.Icc 1 N) (partAWeight S N))⁻¹ *
          Finset.sum (Finset.Icc 1 N)
            (fun k => partAWeight S N k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) := by
            simpa [selectedJointLawPartA, selected_joint_measure, partAStoppingLaw]
              using hselected_raw
  have hprefix_to_stream :
      Finset.sum (Finset.Icc 1 N)
          (fun k => partAWeight S N k *
            ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) =
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
    let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
    have hstream_sq_int :
        ∀ R : OutputTime N,
          Integrable
            (fun ξ : ℕ → Sample =>
              ‖gradΨ S (xUnder S ξ (outputTimePositive R))‖ ^ 2) μ := by
      intro R
      have hpref :=
        partA_generated_grad_norm_sq_prefix_integrable S N hN hC_pos hAdaptive R
      have hcomp :
          Integrable
            (fun ξ : ℕ → Sample =>
              ‖gradΨ S
                (xUnderPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) R)‖ ^ 2)
            μ :=
        (integrable_map_measure hpref.aestronglyMeasurable
            (samplePrefix_measurable (Sample := Sample) N).aemeasurable).mp
          (by simpa [samplePrefixLaw, μ] using hpref)
      have hfun :
          (fun ξ : ℕ → Sample =>
              ‖gradΨ S
                (xUnderPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) R)‖ ^ 2) =
            fun ξ : ℕ → Sample =>
              ‖gradΨ S (xUnder S ξ (outputTimePositive R))‖ ^ 2 := by
        funext ξ
        simp [xUnderPrefix_eq_stream_of_same_prefix S N ξ R]
      rw [hfun] at hcomp
      simpa using hcomp
    have hterm_int :
        ∀ k ∈ (Finset.Icc 1 N).attach,
          Integrable
            (fun ξ : ℕ → Sample =>
              let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
              S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) μ := by
      intro k _hk
      have hbase := hstream_sq_int (k : OutputTime N)
      simpa [outputTimePositive] using
        hbase.const_mul
          (S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩)
    have hsum_attach :
        Finset.sum (Finset.Icc 1 N)
            (fun k => partAWeight S N k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) =
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
              ∫ pref,
                ‖gradΨ S (xUnderPrefix S N pref (k : OutputTime N))‖ ^ 2
                ∂samplePrefixLaw S N) := by
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      have hkcond : 1 ≤ k.1 ∧ k.1 ≤ N := Finset.mem_Icc.mp k.2
      have hk1 : 1 ≤ k.1 := hkcond.1
      simp [partAWeight, xsel, gap, hkcond, hk1]
    have hterm_integral :
        ∀ k : OutputTime N,
          S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
              (∫ pref,
                ‖gradΨ S (xUnderPrefix S N pref k)‖ ^ 2
                ∂samplePrefixLaw S N) =
            ∫ ξ : ℕ → Sample,
              S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
                ‖gradΨ S
                  (xUnder S ξ ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩)‖ ^ 2 ∂μ := by
      intro k
      have hpref :=
        partA_generated_grad_norm_sq_prefix_integrable S N hN hC_pos hAdaptive k
      have hmap :
          (∫ pref,
            ‖gradΨ S (xUnderPrefix S N pref k)‖ ^ 2
            ∂samplePrefixLaw S N) =
          ∫ ξ : ℕ → Sample,
            ‖gradΨ S
              (xUnderPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) k)‖ ^ 2
            ∂μ := by
        unfold samplePrefixLaw
        simpa [μ] using
          (MeasureTheory.integral_map
            (samplePrefix_measurable (Sample := Sample) N).aemeasurable
            hpref.aestronglyMeasurable)
      calc
        S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
            (∫ pref,
              ‖gradΨ S (xUnderPrefix S N pref k)‖ ^ 2
              ∂samplePrefixLaw S N)
            =
          ∫ ξ : ℕ → Sample,
            S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
              ‖gradΨ S
                (xUnderPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) k)‖ ^ 2
            ∂μ := by
              rw [hmap]
              rw [MeasureTheory.integral_const_mul]
        _ =
          ∫ ξ : ℕ → Sample,
            S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
              ‖gradΨ S
                (xUnder S ξ ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩)‖ ^ 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards with ξ
              simp [xUnderPrefix_eq_stream_of_same_prefix S N ξ k, outputTimePositive]
    have hsum_integrals :
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
            S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
              ∫ pref,
                ‖gradΨ S (xUnderPrefix S N pref (k : OutputTime N))‖ ^ 2
                ∂samplePrefixLaw S N) =
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            ∫ ξ : ℕ → Sample,
              S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
                ‖gradΨ S
                  (xUnder S ξ ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩)‖ ^ 2 ∂μ) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      exact hterm_integral (k : OutputTime N)
    calc
      Finset.sum (Finset.Icc 1 N)
          (fun k => partAWeight S N k *
            ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N)
          =
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
            ∫ pref,
              ‖gradΨ S (xUnderPrefix S N pref (k : OutputTime N))‖ ^ 2
              ∂samplePrefixLaw S N) := hsum_attach
      _ =
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          ∫ ξ : ℕ → Sample,
            S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ *
              ‖gradΨ S
                (xUnder S ξ ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩)‖ ^ 2 ∂μ) := hsum_integrals
      _ =
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
            rw [MeasureTheory.integral_finset_sum]
            simpa [μ] using hterm_int
  calc
    (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartA S N hN hC_pos)
        = (Finset.sum (Finset.Icc 1 N) (partAWeight S N))⁻¹ *
          Finset.sum (Finset.Icc 1 N)
            (fun k => partAWeight S N k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) := hselected_prefix
    _ = (partABoundDenominator S N)⁻¹ *
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
          rw [hprefix_to_stream, ← partABoundDenominator_eq_partAWeight_sum S N]

/-- The part (b) randomized output law expands to the normalized weighted
finite-window stream expectation for the selected search-gradient square. -/
private theorem partB_selected_grad_integral_eq_stream_weighted
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hsteps : PartBStepCondition S N)
    (hAdaptive : AdaptiveOracleProcess S) :
    (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartB S N hN hsteps) =
      (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
            ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
  classical
  let xsel : ℕ → SamplePrefix (Sample := Sample) N → Space n := fun k pref =>
    if hk : k ∈ Finset.Icc 1 N then
      xUnderPrefix S N pref ⟨k, hk⟩
    else
      S.x0
  let gap : Space n → ℝ := fun z => ‖gradΨ S z‖ ^ 2
  have hgap_int :
      ∀ R : {k : ℕ // k ∈ Finset.Icc 1 N},
        Integrable (fun pref => gap (xsel R.1 pref)) (samplePrefixLaw S N) := by
    intro R
    have hR :=
      partB_generated_grad_norm_sq_prefix_integrable S N hN hAdaptive
        (R : OutputTime N)
    have hmem : R.1 ∈ Finset.Icc 1 N := R.2
    have hcond : 1 ≤ R.1 ∧ R.1 ≤ N := Finset.mem_Icc.mp hmem
    simpa [gap, xsel, hcond] using hR
  haveI : SFinite (samplePrefixLaw S N) := by
    unfold samplePrefixLaw
    infer_instance
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let xstream : ℕ → (ℕ → Sample) → Space n := fun k ξ =>
    if hk : 1 ≤ k then
      xUnder S ξ ⟨k, hk⟩
    else
      S.x0
  have hselected_raw :
      (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
          gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps) =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
            ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
    have hmain :=
      SOptLib.finiteWindowSelectedOutputExpectation_eq_stream_weighted_sum_of_prefix_law
        (times := Finset.Icc 1 N) (α := partBWeight S) (P := μ)
        (prefixMap := samplePrefix (Sample := Sample) (N := N))
        (xPref := xsel) (xStream := xstream) (gap := gap)
        (hprefix := (samplePrefix_measurable (Sample := Sample) N).aemeasurable)
        (hα_nonneg := partBWeight_nonneg_of_steps S N hsteps)
        (hden := partBWeight_sum_pos_of_steps S N hN hsteps)
        (hgap_int := by
          intro R
          simpa [samplePrefixLaw, μ] using hgap_int R)
        (hcompat := by
          intro k hk
          filter_upwards with ξ
          have hkcond : 1 ≤ k ∧ k ≤ N := Finset.mem_Icc.mp hk
          simp [xsel, xstream, gap, hkcond,
            xUnderPrefix_eq_stream_of_same_prefix S N ξ (⟨k, hk⟩ : OutputTime N),
            outputTimePositive])
    have hmain' :
        (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
            gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps) =
          (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
            (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
              partBWeight S k.1 * gap (xstream k.1 ξ)) ∂μ) := by
      simpa [selectedJointLawPartB, selected_joint_measure, partBStoppingLaw,
        samplePrefixLaw, μ] using hmain
    have hstream_eq :
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            partBWeight S k.1 * gap (xstream k.1 ξ)) ∂μ) =
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) ∂μ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      refine Finset.sum_congr rfl ?_
      intro k _hk
      have hkcond : 1 ≤ k.1 ∧ k.1 ≤ N := Finset.mem_Icc.mp k.2
      have hk1 : 1 ≤ k.1 := hkcond.1
      simp [partBWeight, xstream, gap, hk1]
    calc
      (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
          gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps)
          =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            partBWeight S k.1 * gap (xstream k.1 ξ)) ∂μ) := hmain'
      _ =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
            ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
          simpa [μ] using congrArg
            (fun t =>
              (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ * t)
            hstream_eq
  have hselected_prefix :
      (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartB S N hN hsteps) =
        (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
          gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps) := by
    apply integral_congr_ae
    filter_upwards with q
    have hq : q.1.1 ∈ Finset.Icc 1 N := q.1.2
    have hqcond : 1 ≤ q.1.1 ∧ q.1.1 ≤ N := Finset.mem_Icc.mp hq
    simp [selectedGradNormSq, selectedSearchPoint_eq, selectedOutputPair,
      selectedSearchPoint, gap, xsel, hqcond]
  have hprefix_to_stream :
      (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
          gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps) =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
            ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) :=
    hselected_raw
  calc
    (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartB S N hN hsteps)
        =
      (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
        gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps) := hselected_prefix
    _ = (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
            ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := hprefix_to_stream

/-- The part (b) randomized output law expands to the normalized weighted
finite-window stream expectation for the selected averaged-iterate function gap. -/
private theorem partB_selected_function_gap_integral_eq_stream_weighted
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hsteps : PartBStepCondition S N)
    (hAdaptive : AdaptiveOracleProcess S) (xStar : Space n) :
    (∫ q, selectedFunctionGap S N xStar q ∂selectedJointLawPartB S N hN hsteps) =
      (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          partBWeight S k.1 *
            (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
              ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))) := by
  classical
  let xsel : ℕ → SamplePrefix (Sample := Sample) N → Space n := fun k pref =>
    if hk : k ∈ Finset.Icc 1 N then
      xBarPrefix S N pref k
    else
      S.x0
  let gap : Space n → ℝ := fun z => S.Ψ z - S.Ψ xStar
  have hgap_int :
      ∀ R : {k : ℕ // k ∈ Finset.Icc 1 N},
        Integrable (fun pref => gap (xsel R.1 pref)) (samplePrefixLaw S N) := by
    intro R
    have hR :=
      partB_generated_xBar_function_gap_prefix_integrable
        S N hN hAdaptive xStar (R : OutputTime N)
    have hmem : R.1 ∈ Finset.Icc 1 N := R.2
    have hcond : 1 ≤ R.1 ∧ R.1 ≤ N := Finset.mem_Icc.mp hmem
    simpa [gap, xsel, hcond] using hR
  haveI : SFinite (samplePrefixLaw S N) := by
    unfold samplePrefixLaw
    infer_instance
  have hselected_raw :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := Finset.Icc 1 N) (α := partBWeight S)
      (P := samplePrefixLaw S N) (x := xsel) (gap := gap)
      (partBWeight_nonneg_of_steps S N hsteps)
      (partBWeight_sum_pos_of_steps S N hN hsteps)
      hgap_int
  have hselected_prefix :
      (∫ q, selectedFunctionGap S N xStar q ∂selectedJointLawPartB S N hN hsteps) =
      (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          Finset.sum (Finset.Icc 1 N)
            (fun k => partBWeight S k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) := by
    have hselected_lhs :
        (∫ q, selectedFunctionGap S N xStar q ∂selectedJointLawPartB S N hN hsteps) =
          (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
            gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps) := by
      apply integral_congr_ae
      filter_upwards with q
      have hq : q.1.1 ∈ Finset.Icc 1 N := q.1.2
      have hqcond : 1 ≤ q.1.1 ∧ q.1.1 ≤ N := Finset.mem_Icc.mp hq
      simp [selectedFunctionGap, selectedAveragedPoint_eq, selectedOutputPair,
        selectedAveragedPoint, gap, xsel, hqcond]
    calc
      (∫ q, selectedFunctionGap S N xStar q ∂selectedJointLawPartB S N hN hsteps)
          =
        (∫ q : OutputTime N × SamplePrefix (Sample := Sample) N,
          gap (xsel q.1.1 q.2) ∂selectedJointLawPartB S N hN hsteps) := hselected_lhs
      _ =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          Finset.sum (Finset.Icc 1 N)
            (fun k => partBWeight S k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) := by
            simpa [selectedJointLawPartB, selected_joint_measure, partBStoppingLaw]
              using hselected_raw
  have hprefix_to_stream :
      Finset.sum (Finset.Icc 1 N)
          (fun k => partBWeight S k *
            ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) =
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          partBWeight S k.1 *
            (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
              ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))) := by
    let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
    have hsum_attach :
        Finset.sum (Finset.Icc 1 N)
            (fun k => partBWeight S k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) =
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            partBWeight S k.1 *
              ∫ pref,
                S.Ψ (xBarPrefix S N pref k.1) - S.Ψ xStar
                ∂samplePrefixLaw S N) := by
      rw [← Finset.sum_attach]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      have hkcond : 1 ≤ k.1 ∧ k.1 ≤ N := Finset.mem_Icc.mp k.2
      simp [gap, xsel, hkcond]
    have hterm_integral :
        ∀ k : OutputTime N,
          (∫ pref,
              S.Ψ (xBarPrefix S N pref k.1) - S.Ψ xStar
              ∂samplePrefixLaw S N) =
            ∫ ξ : ℕ → Sample,
              S.Ψ (xBar S ξ k.1) - S.Ψ xStar ∂μ := by
      intro k
      have hpref :=
        partB_generated_xBar_function_gap_prefix_integrable S N hN hAdaptive xStar k
      have hmap :
          (∫ pref,
            S.Ψ (xBarPrefix S N pref k.1) - S.Ψ xStar
            ∂samplePrefixLaw S N) =
          ∫ ξ : ℕ → Sample,
            S.Ψ
              (xBarPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) k.1) -
              S.Ψ xStar ∂μ := by
        unfold samplePrefixLaw
        simpa [μ] using
          (MeasureTheory.integral_map
            (samplePrefix_measurable (Sample := Sample) N).aemeasurable
            hpref.aestronglyMeasurable)
      calc
        (∫ pref,
          S.Ψ (xBarPrefix S N pref k.1) - S.Ψ xStar
          ∂samplePrefixLaw S N)
            =
          ∫ ξ : ℕ → Sample,
            S.Ψ
              (xBarPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) k.1) -
              S.Ψ xStar ∂μ := hmap
        _ =
          ∫ ξ : ℕ → Sample,
            S.Ψ (xBar S ξ k.1) - S.Ψ xStar ∂μ := by
            apply integral_congr_ae
            filter_upwards with ξ
            have hkN : k.1 ≤ N := (Finset.mem_Icc.mp k.2).2
            simp [xBarPrefix_eq_stream_of_same_prefix S N ξ k.1 hkN]
    calc
      Finset.sum (Finset.Icc 1 N)
          (fun k => partBWeight S k *
            ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N)
          =
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          partBWeight S k.1 *
            ∫ pref,
              S.Ψ (xBarPrefix S N pref k.1) - S.Ψ xStar
              ∂samplePrefixLaw S N) := hsum_attach
      _ =
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          partBWeight S k.1 *
            (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar ∂μ)) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          rw [hterm_integral (k : OutputTime N)]
      _ =
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          partBWeight S k.1 *
            (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
              ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))) := by
          simp [μ]
  calc
    (∫ q, selectedFunctionGap S N xStar q ∂selectedJointLawPartB S N hN hsteps)
        = (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          Finset.sum (Finset.Icc 1 N)
            (fun k => partBWeight S k *
              ∫ pref, gap (xsel k pref) ∂samplePrefixLaw S N) := hselected_prefix
    _ = (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          partBWeight S k.1 *
            (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
              ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))) := by
          rw [hprefix_to_stream]

/-- Selected-output well-definedness plus the normalized finite-window
transport used in Theorem 6.12(a). -/
private theorem partA_selected_grad_integrable_and_integral_eq_stream_weighted
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩)
    (hAdaptive : AdaptiveOracleProcess S) :
    Integrable (selectedGradNormSq S N) (selectedJointLawPartA S N hN hC_pos) ∧
      (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartA S N hN hC_pos) =
        (partABoundDenominator S N)⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
            ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
  refine ⟨?_, partA_selected_grad_integral_eq_stream_weighted S N hN hC_pos hAdaptive⟩
  classical
  let p : PMF (OutputTime N) := partAStoppingLaw S N hN hC_pos
  let μ : Measure (SamplePrefix (Sample := Sample) N) := samplePrefixLaw S N
  haveI : SFinite μ := by
    dsimp [μ]
    unfold samplePrefixLaw
    infer_instance
  let F : OutputTime N → SamplePrefix (Sample := Sample) N → ℝ := fun R pref =>
    selectedGradNormSq S N (R, pref)
  have hF_int : ∀ R : OutputTime N, Integrable (F R) μ := by
    intro R
    have hR :=
      partA_generated_grad_norm_sq_prefix_integrable S N hN hC_pos hAdaptive R
    simpa [F, μ, selectedGradNormSq, selectedSearchPoint_eq, selectedOutputPair,
      selectedSearchPoint] using hR
  let G : OutputTime N → OutputTime N × SamplePrefix (Sample := Sample) N → ℝ :=
    fun R q => ({r : OutputTime N × SamplePrefix (Sample := Sample) N | r.1 = R}.indicator
      (fun q => F R q.2) q)
  have hG_int :
      ∀ R ∈ (Finset.univ : Finset (OutputTime N)),
        Integrable (G R) (p.toMeasure.prod μ) := by
    intro R _hR
    have hbase :
        Integrable (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          F R q.2) (p.toMeasure.prod μ) :=
      (hF_int R).comp_snd p.toMeasure
    have hset :
        MeasurableSet
          ({r : OutputTime N × SamplePrefix (Sample := Sample) N | r.1 = R} : Set
            (OutputTime N × SamplePrefix (Sample := Sample) N)) :=
      measurable_fst (measurableSet_singleton R)
    exact hbase.indicator hset
  have hsum_int :
      Integrable
        (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          Finset.sum (Finset.univ : Finset (OutputTime N)) (fun R => G R q))
        (p.toMeasure.prod μ) :=
    MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset (OutputTime N)))
      (μ := p.toMeasure.prod μ) hG_int
  have hselected_int :
      Integrable
        (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          selectedGradNormSq S N q) (p.toMeasure.prod μ) := by
    refine hsum_int.congr ?_
    filter_upwards with q
    dsimp [G, F]
    symm
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro R _hR hRq
      have hne : q.1 ≠ R := fun h => hRq h.symm
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ q.1))
  simpa [selectedJointLawPartA, selected_joint_measure, p, μ] using hselected_int

/-- Selected-output well-definedness plus the normalized finite-window
transport used in Theorem 6.12(b)'s gradient bound. -/
private theorem partB_selected_grad_integrable_and_integral_eq_stream_weighted
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hsteps : PartBStepCondition S N)
    (hAdaptive : AdaptiveOracleProcess S) :
    Integrable (selectedGradNormSq S N) (selectedJointLawPartB S N hN hsteps) ∧
      (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartB S N hN hsteps) =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
            ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := by
  refine ⟨?_, partB_selected_grad_integral_eq_stream_weighted S N hN hsteps hAdaptive⟩
  classical
  let p : PMF (OutputTime N) := partBStoppingLaw S N hN hsteps
  let μ : Measure (SamplePrefix (Sample := Sample) N) := samplePrefixLaw S N
  haveI : SFinite μ := by
    dsimp [μ]
    unfold samplePrefixLaw
    infer_instance
  let F : OutputTime N → SamplePrefix (Sample := Sample) N → ℝ := fun R pref =>
    selectedGradNormSq S N (R, pref)
  have hF_int : ∀ R : OutputTime N, Integrable (F R) μ := by
    intro R
    have hR :=
      partB_generated_grad_norm_sq_prefix_integrable S N hN hAdaptive R
    simpa [F, μ, selectedGradNormSq, selectedSearchPoint_eq, selectedOutputPair,
      selectedSearchPoint] using hR
  let G : OutputTime N → OutputTime N × SamplePrefix (Sample := Sample) N → ℝ :=
    fun R q => ({r : OutputTime N × SamplePrefix (Sample := Sample) N | r.1 = R}.indicator
      (fun q => F R q.2) q)
  have hG_int :
      ∀ R ∈ (Finset.univ : Finset (OutputTime N)),
        Integrable (G R) (p.toMeasure.prod μ) := by
    intro R _hR
    have hbase :
        Integrable (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          F R q.2) (p.toMeasure.prod μ) :=
      (hF_int R).comp_snd p.toMeasure
    have hset :
        MeasurableSet
          ({r : OutputTime N × SamplePrefix (Sample := Sample) N | r.1 = R} : Set
            (OutputTime N × SamplePrefix (Sample := Sample) N)) :=
      measurable_fst (measurableSet_singleton R)
    exact hbase.indicator hset
  have hsum_int :
      Integrable
        (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          Finset.sum (Finset.univ : Finset (OutputTime N)) (fun R => G R q))
        (p.toMeasure.prod μ) :=
    MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset (OutputTime N)))
      (μ := p.toMeasure.prod μ) hG_int
  have hselected_int :
      Integrable
        (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          selectedGradNormSq S N q) (p.toMeasure.prod μ) := by
    refine hsum_int.congr ?_
    filter_upwards with q
    dsimp [G, F]
    symm
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro R _hR hRq
      have hne : q.1 ≠ R := fun h => hRq h.symm
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ q.1))
  simpa [selectedJointLawPartB, selected_joint_measure, p, μ] using hselected_int

/-- Selected-output well-definedness plus the normalized finite-window
transport used in Theorem 6.12(b)'s function-gap bound. -/
private theorem partB_selected_function_gap_integrable_and_integral_eq_stream_weighted
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hsteps : PartBStepCondition S N)
    (hAdaptive : AdaptiveOracleProcess S) (xStar : Space n) :
    Integrable (selectedFunctionGap S N xStar) (selectedJointLawPartB S N hN hsteps) ∧
      (∫ q, selectedFunctionGap S N xStar q ∂selectedJointLawPartB S N hN hsteps) =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            partBWeight S k.1 *
              (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
                ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))) := by
  refine ⟨?_,
    partB_selected_function_gap_integral_eq_stream_weighted
      S N hN hsteps hAdaptive xStar⟩
  classical
  let p : PMF (OutputTime N) := partBStoppingLaw S N hN hsteps
  let μ : Measure (SamplePrefix (Sample := Sample) N) := samplePrefixLaw S N
  haveI : SFinite μ := by
    dsimp [μ]
    unfold samplePrefixLaw
    infer_instance
  let F : OutputTime N → SamplePrefix (Sample := Sample) N → ℝ := fun R pref =>
    selectedFunctionGap S N xStar (R, pref)
  have hF_int : ∀ R : OutputTime N, Integrable (F R) μ := by
    intro R
    have hR :=
      partB_generated_xBar_function_gap_prefix_integrable
        S N hN hAdaptive xStar R
    simpa [F, μ, selectedFunctionGap, selectedAveragedPoint_eq, selectedOutputPair,
      selectedAveragedPoint] using hR
  let G : OutputTime N → OutputTime N × SamplePrefix (Sample := Sample) N → ℝ :=
    fun R q => ({r : OutputTime N × SamplePrefix (Sample := Sample) N | r.1 = R}.indicator
      (fun q => F R q.2) q)
  have hG_int :
      ∀ R ∈ (Finset.univ : Finset (OutputTime N)),
        Integrable (G R) (p.toMeasure.prod μ) := by
    intro R _hR
    have hbase :
        Integrable (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          F R q.2) (p.toMeasure.prod μ) :=
      (hF_int R).comp_snd p.toMeasure
    have hset :
        MeasurableSet
          ({r : OutputTime N × SamplePrefix (Sample := Sample) N | r.1 = R} : Set
            (OutputTime N × SamplePrefix (Sample := Sample) N)) :=
      measurable_fst (measurableSet_singleton R)
    exact hbase.indicator hset
  have hsum_int :
      Integrable
        (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          Finset.sum (Finset.univ : Finset (OutputTime N)) (fun R => G R q))
        (p.toMeasure.prod μ) :=
    MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset (OutputTime N)))
      (μ := p.toMeasure.prod μ) hG_int
  have hselected_int :
      Integrable
        (fun q : OutputTime N × SamplePrefix (Sample := Sample) N =>
          selectedFunctionGap S N xStar q) (p.toMeasure.prod μ) := by
    refine hsum_int.congr ?_
    filter_upwards with q
    dsimp [G, F]
    symm
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro R _hR hRq
      have hne : q.1 ≠ R := fun h => hRq h.symm
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ q.1))
  simpa [selectedJointLawPartB, selected_joint_measure, p, μ] using hselected_int

/-- The finite stream weighted-gradient sum in Theorem 6.12(a) is integrable
once each selected prefix search-gradient square is integrable. -/
private theorem partA_stream_weighted_gradient_integrable
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩)
    (hAdaptive : AdaptiveOracleProcess S) :
    Integrable
      (fun ξ : ℕ → Sample =>
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hstream_sq_int :
      ∀ R : OutputTime N,
        Integrable
          (fun ξ : ℕ → Sample =>
            ‖gradΨ S (xUnder S ξ (outputTimePositive R))‖ ^ 2) μ := by
    intro R
    have hpref :=
      partA_generated_grad_norm_sq_prefix_integrable S N hN hC_pos hAdaptive R
    have hcomp :
        Integrable
          (fun ξ : ℕ → Sample =>
            ‖gradΨ S
              (xUnderPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) R)‖ ^ 2)
          μ :=
      (integrable_map_measure hpref.aestronglyMeasurable
          (samplePrefix_measurable (Sample := Sample) N).aemeasurable).mp
        (by simpa [samplePrefixLaw, μ] using hpref)
    have hfun :
        (fun ξ : ℕ → Sample =>
            ‖gradΨ S
              (xUnderPrefix S N (samplePrefix (Sample := Sample) (N := N) ξ) R)‖ ^ 2) =
          fun ξ : ℕ → Sample =>
            ‖gradΨ S (xUnder S ξ (outputTimePositive R))‖ ^ 2 := by
      funext ξ
      simp [xUnderPrefix_eq_stream_of_same_prefix S N ξ R]
    rw [hfun] at hcomp
    simpa using hcomp
  have hterm_int :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) μ := by
    intro k _hk
    have hbase := hstream_sq_int (k : OutputTime N)
    simpa [outputTimePositive] using
      hbase.const_mul
        (S.lam k.1 * C S N ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩)
  exact MeasureTheory.integrable_finset_sum (s := (Finset.Icc 1 N).attach)
    (μ := μ) hterm_int

/-- If each residual summand is integrable, the termwise martingale
cancellations combine into cancellation of the displayed residual budget. -/
private theorem partA_residual_budget_integral_eq_zero_of_term_integrable
    (S : Setup n Sample) (N : ℕ)
    (_hResidualInnerIntegralZero :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        (∫ ξ : ℕ → Sample,
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          let tailΓ : ℝ :=
            Finset.sum (Finset.Icc k.1 N).attach
              (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                (Finset.mem_Icc.mp τ.2).1⟩)
          inner ℝ
            (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1 ^ 2 +
                S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp) * tailΓ) •
                gradΨ S (xUnder S ξ kp))
            (generatedOracleErrorAt S kp ξ)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0)
    (hResidualTermIntegrable :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            let tailΓ : ℝ :=
              Finset.sum (Finset.Icc k.1 N).attach
                (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                  (Finset.mem_Icc.mp τ.2).1⟩)
            inner ℝ
              (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
                (S.LΨ * S.lam k.1 ^ 2 +
                  S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                    (S.alpha k.1 * Γ S kp) * tailΓ) •
                  gradΨ S (xUnder S ξ kp))
              (generatedOracleErrorAt S kp ξ))
          (S.sampleStreamLaw : Measure (ℕ → Sample))) :
    (∫ ξ, partAResidualBudget S N ξ
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 := by
  classical
  unfold partAResidualBudget
  rw [MeasureTheory.integral_finset_sum]
  · exact Finset.sum_eq_zero (fun k _hk => _hResidualInnerIntegralZero k)
  · exact hResidualTermIntegrable

/-- L1 side condition for the part (a) residual scalarization.  This is the
remaining residual-integrability leaf: it should follow from the adaptive
generated-error L2 bound and square-integrability of the strict-past multiplier. -/
private theorem partA_residual_inner_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (hAdaptive : AdaptiveOracleProcess S)
    (k : {k : ℕ // k ∈ Finset.Icc 1 N}) :
    Integrable
      (fun ξ : ℕ → Sample =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        let tailΓ : ℝ :=
          Finset.sum (Finset.Icc k.1 N).attach
            (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
              (Finset.mem_Icc.mp τ.2).1⟩)
        inner ℝ
          (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
            (S.LΨ * S.lam k.1 ^ 2 +
              S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                (S.alpha k.1 * Γ S kp) * tailΓ) •
              gradΨ S (xUnder S ξ kp))
          (generatedOracleErrorAt S kp ξ))
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let tailΓ : ℝ :=
    Finset.sum (Finset.Icc k.1 N).attach
      (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
        (Finset.mem_Icc.mp τ.2).1⟩)
  let multiplier : (ℕ → Sample) → Space n := fun ξ =>
    S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
      (S.LΨ * S.lam k.1 ^ 2 +
        S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
          (S.alpha k.1 * Γ S kp) * tailΓ) •
        gradΨ S (xUnder S ξ kp)
  have hmult_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)] multiplier := by
    simpa [multiplier, kp, tailΓ] using
      partA_residual_multiplier_measurable_of_adaptiveOracleProcess S N k hAdaptive
  have hmult_meas : Measurable multiplier :=
    hmult_meas_sub.mono ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hmult_sq :
      Integrable (fun ξ : ℕ → Sample => ‖multiplier ξ‖ ^ 2) μ := by
    simpa [multiplier, kp, tailΓ, μ] using
      partA_residual_multiplier_sq_integrable_of_adaptiveOracleProcess S N hAdaptive k
  have hδ_sq :
      Integrable (fun ξ : ℕ → Sample => ‖generatedOracleErrorAt S kp ξ‖ ^ 2) μ := by
    simpa [kp, μ] using
      generated_oracle_error_sq_integrable_of_adaptiveOracleProcess S hAdaptive kp
  have hδ_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq (kp.1 + 1))]
        (fun ξ : ℕ → Sample => generatedOracleErrorAt S kp ξ) :=
    oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive kp
  have hδ_meas : Measurable (fun ξ : ℕ → Sample => generatedOracleErrorAt S kp ξ) :=
    hδ_meas_sub.mono ((sampleFiltration (Sample := Sample)).le (kp.1 + 1)) le_rfl
  have hinner :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := multiplier) (v := fun ξ : ℕ → Sample => generatedOracleErrorAt S kp ξ)
      hmult_meas.aestronglyMeasurable hδ_meas.aestronglyMeasurable
      hmult_sq hδ_sq
  simpa [multiplier, kp, tailΓ, μ] using hinner

/-- Measure-theoretic assembly of Theorem 6.12(a)'s stream expectation bound,
assuming the displayed stream terms are integrable and the residual budget has
zero integral. -/
private theorem partA_stream_weighted_gradient_integral_le_of_integrability
    (S : Setup n Sample) (N : ℕ)
    (_hPathwiseWeightedGradient :
      ∀ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) ≤
        S.Ψ S.x0 - Ψstar S + partAPathwiseNoiseBudget S N ξ -
          partAResidualBudget S N ξ)
    (_hNoiseBudget :
      (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
        (S.LΨ * S.σ ^ 2 / 2) *
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 ^ 2 *
              (1 +
                (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
                    Finset.sum (Finset.Icc k.1 N).attach
                      (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                        (Finset.mem_Icc.mp τ.2).1⟩))))
    (hWeightedGradIntegrable :
      Integrable
        (fun ξ : ℕ → Sample =>
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
        (S.sampleStreamLaw : Measure (ℕ → Sample)))
    (hNoiseIntegrable :
      Integrable (fun ξ => partAPathwiseNoiseBudget S N ξ)
        (S.sampleStreamLaw : Measure (ℕ → Sample)))
    (hResidualIntegrable :
      Integrable (fun ξ => partAResidualBudget S N ξ)
        (S.sampleStreamLaw : Measure (ℕ → Sample)))
    (hResidualIntegralZero :
      (∫ ξ, partAResidualBudget S N ξ
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0) :
    (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
      partABoundNumerator S N := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let weightedGrad :
      (ℕ → Sample) → ℝ := fun ξ =>
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
  let upper : (ℕ → Sample) → ℝ := fun ξ =>
    S.Ψ S.x0 - Ψstar S + partAPathwiseNoiseBudget S N ξ -
      partAResidualBudget S N ξ
  have hUpperIntegrable : Integrable upper μ := by
    dsimp [upper, μ]
    exact
      ((integrable_const (S.Ψ S.x0 - Ψstar S)).add hNoiseIntegrable).sub
        hResidualIntegrable
  have hPoint : ∀ᵐ ξ ∂μ, weightedGrad ξ ≤ upper ξ := by
    exact Filter.Eventually.of_forall (fun ξ => _hPathwiseWeightedGradient ξ)
  have hMono :
      (∫ ξ, weightedGrad ξ ∂μ) ≤ ∫ ξ, upper ξ ∂μ :=
    MeasureTheory.integral_mono_ae
      (by simpa [weightedGrad, μ] using hWeightedGradIntegrable)
      hUpperIntegrable hPoint
  have hUpperIntegral :
      (∫ ξ, upper ξ ∂μ) =
        S.Ψ S.x0 - Ψstar S +
          (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂μ) -
          (∫ ξ, partAResidualBudget S N ξ ∂μ) := by
    dsimp [upper]
    rw [MeasureTheory.integral_sub
      (f := fun ξ : ℕ → Sample =>
        S.Ψ S.x0 - Ψstar S + partAPathwiseNoiseBudget S N ξ)
      (g := fun ξ : ℕ → Sample => partAResidualBudget S N ξ)
      (((integrable_const (S.Ψ S.x0 - Ψstar S)).add
        (by simpa [μ] using hNoiseIntegrable)))
      (by simpa [μ] using hResidualIntegrable)]
    rw [MeasureTheory.integral_add
      (f := fun _ : ℕ → Sample => S.Ψ S.x0 - Ψstar S)
      (g := fun ξ : ℕ → Sample => partAPathwiseNoiseBudget S N ξ)
      (integrable_const (S.Ψ S.x0 - Ψstar S))
      (by simpa [μ] using hNoiseIntegrable)]
    simp [μ]
  have hAfterResidual :
      S.Ψ S.x0 - Ψstar S +
          (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂μ) -
          (∫ ξ, partAResidualBudget S N ξ ∂μ) ≤
        partABoundNumerator S N := by
    have hNoise :
        (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂μ) ≤
          (S.LΨ * S.σ ^ 2 / 2) *
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
              S.lam k.1 ^ 2 *
                (1 +
                  (S.lam k.1 - S.beta k.1) ^ 2 /
                    (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
                      Finset.sum (Finset.Icc k.1 N).attach
                        (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                          (Finset.mem_Icc.mp τ.2).1⟩))) := by
      simpa [μ] using _hNoiseBudget
    have hres : (∫ ξ, partAResidualBudget S N ξ ∂μ) = 0 := by
      simpa [μ] using hResidualIntegralZero
    rw [hres, sub_zero]
    simpa [partABoundNumerator] using
      add_le_add_left hNoise (S.Ψ S.x0 - Ψstar S)
  calc
    (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))
        = ∫ ξ, weightedGrad ξ ∂μ := by rfl
    _ ≤ ∫ ξ, upper ξ ∂μ := hMono
    _ = S.Ψ S.x0 - Ψstar S +
          (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂μ) -
          (∫ ξ, partAResidualBudget S N ξ ∂μ) := hUpperIntegral
    _ ≤ partABoundNumerator S N := hAfterResidual

/-- Integrated source step for Theorem 6.12(a): the pathwise weighted-gradient
bound, the variance budget, and martingale residual cancellation imply the
numerator bound before randomized-output normalization. -/
private theorem partA_stream_weighted_gradient_integral_le
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩)
    (hAdaptive : AdaptiveOracleProcess S)
    (_hPathwiseWeightedGradient :
      ∀ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) ≤
        S.Ψ S.x0 - Ψstar S + partAPathwiseNoiseBudget S N ξ -
          partAResidualBudget S N ξ)
    (_hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
          (generatedOracleErrorNormSq S k) (S.σ ^ 2))
    (_hNoiseBudget :
      (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
        (S.LΨ * S.σ ^ 2 / 2) *
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 ^ 2 *
              (1 +
                (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
                    Finset.sum (Finset.Icc k.1 N).attach
                      (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                        (Finset.mem_Icc.mp τ.2).1⟩))))
    (_hResidualInnerIntegralZero :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        (∫ ξ : ℕ → Sample,
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          let tailΓ : ℝ :=
            Finset.sum (Finset.Icc k.1 N).attach
              (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                (Finset.mem_Icc.mp τ.2).1⟩)
          inner ℝ
            (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1 ^ 2 +
                S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp) * tailΓ) •
                gradΨ S (xUnder S ξ kp))
            (generatedOracleErrorAt S kp ξ)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0) :
    (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
      partABoundNumerator S N := by
  classical
  have hWeightedGradIntegrable :
      Integrable
        (fun ξ : ℕ → Sample =>
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
        (S.sampleStreamLaw : Measure (ℕ → Sample)) :=
    partA_stream_weighted_gradient_integrable S N hN hC_pos hAdaptive
  have hResidualTermIntegrable :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            let tailΓ : ℝ :=
              Finset.sum (Finset.Icc k.1 N).attach
                (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                  (Finset.mem_Icc.mp τ.2).1⟩)
            inner ℝ
              (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
                (S.LΨ * S.lam k.1 ^ 2 +
                  S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                    (S.alpha k.1 * Γ S kp) * tailΓ) •
                  gradΨ S (xUnder S ξ kp))
              (generatedOracleErrorAt S kp ξ))
          (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
    intro k _hk
    exact partA_residual_inner_integrable_of_adaptiveOracleProcess S N hAdaptive k
  have hNoiseIntegrable :
      Integrable (fun ξ => partAPathwiseNoiseBudget S N ξ)
        (S.sampleStreamLaw : Measure (ℕ → Sample)) :=
    partA_noiseBudget_integrable S N _hSecondMoment
  have hResidualIntegrable :
      Integrable (fun ξ => partAResidualBudget S N ξ)
        (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
    unfold partAResidualBudget
    exact MeasureTheory.integrable_finset_sum
      (s := (Finset.Icc 1 N).attach)
      (μ := (S.sampleStreamLaw : Measure (ℕ → Sample)))
      hResidualTermIntegrable
  have hResidualIntegralZero :
      (∫ ξ, partAResidualBudget S N ξ
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 :=
    partA_residual_budget_integral_eq_zero_of_term_integrable
      S N _hResidualInnerIntegralZero hResidualTermIntegrable
  exact
    partA_stream_weighted_gradient_integral_le_of_integrability
      S N _hPathwiseWeightedGradient _hNoiseBudget
      hWeightedGradIntegrable hNoiseIntegrable
      hResidualIntegrable hResidualIntegralZero

/-- The printed conclusion of Theorem 6.12(a) as a proposition.

This declaration records the source statement without asserting that the current
marginal-only sample-process model proves the adaptive martingale cancellation
used in the PDF proof. -/
def theorem612_partA_statement
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩) : Prop :=
    expectationLe (selectedJointLawPartA S N hN hC_pos) (selectedGradNormSq S N)
      (partABoundNumerator S N / partABoundDenominator S N)

/-- Conditional-process helper for Theorem 6.12(a).

This is not exported as the paper theorem: it makes explicit the adaptive
martingale boundary needed by the proof line cancelling `b_k`. The printed
paper conclusion is `theorem612_partA_statement`; this helper is a corrected
non-original proof boundary. -/
theorem theorem612_partA_under_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hC_pos : ∀ k : WindowTime N, 0 < C S N ⟨k.1, k.2.1⟩)
    (hAdaptive : AdaptiveOracleProcess S) :
    theorem612_partA_statement S N hN hC_pos := by
  have _hFixedStep :
      ∀ (ξ : ℕ → Sample) (k : PositiveTime),
        S.Ψ (x S ξ k.1) ≤
          S.Ψ (x S ξ (k.1 - 1)) -
            S.lam k.1 * (1 - S.LΨ * S.lam k.1) *
              ‖gradΨ S (xUnder S ξ k)‖ ^ 2 +
            (S.LΨ * (1 - S.alpha k.1) ^ 2 / 2) *
              ‖x S ξ (k.1 - 1) - xBar S ξ (k.1 - 1)‖ ^ 2 +
            (S.LΨ * S.lam k.1 ^ 2 / 2) * ‖generatedOracleErrorAt S k ξ‖ ^ 2 -
            S.lam k.1 *
              inner ℝ
                (gradΨ S (x S ξ (k.1 - 1)) -
                  (S.LΨ * S.lam k.1) • gradΨ S (xUnder S ξ k))
                (generatedOracleErrorAt S k ξ) :=
    fun ξ k => partA_one_step_descent_with_acceleration_gap S ξ k
  have _hMeanZero :
      ∀ k : PositiveTime,
        SOptLib.ConditionalExpectation.conditionalExpectationEq
          (S.sampleStreamLaw : Measure (ℕ → Sample))
          ((sampleFiltration (Sample := Sample)).seq k.1)
          (generatedOracleErrorAt S k)
          (0 : (ℕ → Sample) → Space n) :=
    fun k => oracleErrorAt_condExp_past_eq_zero_of_adaptiveOracleProcess S hAdaptive k
  have _hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
          (generatedOracleErrorNormSq S k) (S.σ ^ 2) :=
    fun k => oracleErrorAt_secondMoment_le_of_adaptiveOracleProcess S hAdaptive k
  have _hPathwiseWeightedGradient :
      ∀ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) ≤
        S.Ψ S.x0 - Ψstar S + partAPathwiseNoiseBudget S N ξ -
          partAResidualBudget S N ξ :=
    fun ξ => partA_pathwise_weighted_gradient_bound S N hN ξ
  have _hNoiseBudget :
      (∫ ξ, partAPathwiseNoiseBudget S N ξ ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
        (S.LΨ * S.σ ^ 2 / 2) *
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 ^ 2 *
              (1 +
                (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp * S.lam k.1 ^ 2) *
                    Finset.sum (Finset.Icc k.1 N).attach
                      (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                        (Finset.mem_Icc.mp τ.2).1⟩))) :=
    partA_noiseBudget_integral_le S N _hSecondMoment
  have _hDenominatorPos : 0 < partABoundDenominator S N :=
    partABoundDenominator_pos S N hN hC_pos
  have _hResidualMultiplierMeasurable :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
          (fun ξ : ℕ → Sample =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            let tailΓ : ℝ :=
              Finset.sum (Finset.Icc k.1 N).attach
                (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                  (Finset.mem_Icc.mp τ.2).1⟩)
            S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1 ^ 2 +
                S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp) * tailΓ) •
                gradΨ S (xUnder S ξ kp)) :=
    fun k => partA_residual_multiplier_measurable_of_adaptiveOracleProcess S N k hAdaptive
  have _hResidualInnerIntegralZero :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        (∫ ξ : ℕ → Sample,
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          let tailΓ : ℝ :=
            Finset.sum (Finset.Icc k.1 N).attach
              (fun τ => Γ S ⟨τ.1, le_trans (Finset.mem_Icc.mp k.2).1
                (Finset.mem_Icc.mp τ.2).1⟩)
          inner ℝ
            (S.lam k.1 • gradΨ S (x S ξ (k.1 - 1)) -
              (S.LΨ * S.lam k.1 ^ 2 +
                S.LΨ * (S.lam k.1 - S.beta k.1) ^ 2 /
                  (S.alpha k.1 * Γ S kp) * tailΓ) •
                gradΨ S (xUnder S ξ kp))
            (generatedOracleErrorAt S kp ξ)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 :=
    fun k =>
      partA_residual_inner_integral_eq_zero_of_multiplier_measurable
        S N k _hMeanZero (_hResidualMultiplierMeasurable k)
  unfold theorem612_partA_statement
  refine SOptLib.expectationLe_of_integrable_integral_le ?_ ?_
  · exact
      (partA_selected_grad_integrable_and_integral_eq_stream_weighted
        S N hN hC_pos hAdaptive).1
  · have hSelected :=
      (partA_selected_grad_integrable_and_integral_eq_stream_weighted
        S N hN hC_pos hAdaptive).2
    have hStream :
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
          partABoundNumerator S N :=
      partA_stream_weighted_gradient_integral_le
        S N hN hC_pos hAdaptive _hPathwiseWeightedGradient _hSecondMoment
        _hNoiseBudget _hResidualInnerIntegralZero
    calc
      (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartA S N hN hC_pos)
          =
        (partABoundDenominator S N)⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            S.lam k.1 * C S N kp * ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
            ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := hSelected
      _ ≤ (partABoundDenominator S N)⁻¹ * partABoundNumerator S N := by
            exact mul_le_mul_of_nonneg_left hStream
              (le_of_lt (inv_pos.mpr _hDenominatorPos))
      _ = partABoundNumerator S N / partABoundDenominator S N := by
            rw [div_eq_mul_inv]
            ring

/-- The printed conclusion of Theorem 6.12(b)'s two displayed bounds as a proposition.

The statement keeps the paper's convexity and optimizer existence assumptions,
but does not assert that the current marginal process boundary is enough for
the adaptive martingale cancellation in the proof. -/
def theorem612_partB_statement
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (xStar : Space n) (hxStar : ∀ x : Space n, S.Ψ xStar ≤ S.Ψ x)
    (hsteps : PartBStepCondition S N) : Prop :=
    expectationLe (selectedJointLawPartB S N hN hsteps) (selectedGradNormSq S N)
        ((((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
          S.LΨ * S.σ ^ 2 *
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
              (Γ S kp)⁻¹ * S.beta k.1 ^ 2)) /
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1))) ∧
      expectationLe (selectedJointLawPartB S N hN hsteps) (selectedFunctionGap S N xStar)
        (Finset.sum (Finset.Icc 1 N).attach (fun k =>
          S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
            (((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
              S.LΨ * S.σ ^ 2 *
                Finset.sum (Finset.Icc 1 k.1).attach (fun j =>
                  let jp : PositiveTime := ⟨j.1, (Finset.mem_Icc.mp j.2).1⟩
                  (Γ S jp)⁻¹ * S.beta j.1 ^ 2))) /
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1)))

/-- Source step 23 for Theorem 6.12(b): a stream weighted-gradient integral
bound transports through the part (b) randomized output law. -/
private theorem partB_selected_gradient_bound_of_stream_bound
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (xStar : Space n) (hsteps : PartBStepCondition S N)
    (hAdaptive : AdaptiveOracleProcess S)
    (hStream :
      (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
          ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
        ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
          S.LΨ * S.σ ^ 2 *
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
              (Γ S kp)⁻¹ * S.beta k.1 ^ 2)) :
    expectationLe (selectedJointLawPartB S N hN hsteps) (selectedGradNormSq S N)
      ((((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
        S.LΨ * S.σ ^ 2 *
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 ^ 2)) /
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1))) := by
  classical
  let numerator : ℝ :=
    ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
      S.LΨ * S.σ ^ 2 *
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 ^ 2)
  let denom : ℝ :=
    Finset.sum (Finset.Icc 1 N).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1))
  refine SOptLib.expectationLe_of_integrable_integral_le ?_ ?_
  · exact
      (partB_selected_grad_integrable_and_integral_eq_stream_weighted
        S N hN hsteps hAdaptive).1
  · have hSelected :=
      (partB_selected_grad_integrable_and_integral_eq_stream_weighted
        S N hN hsteps hAdaptive).2
    have hDenomPos : 0 < Finset.sum (Finset.Icc 1 N) (partBWeight S) :=
      partBWeight_sum_pos_of_steps S N hN hsteps
    have hDenomEq :
        denom = Finset.sum (Finset.Icc 1 N) (partBWeight S) := by
      simpa [denom] using partB_display_denominator_eq_partBWeight_sum S N
    calc
      (∫ q, selectedGradNormSq S N q ∂selectedJointLawPartB S N hN hsteps)
          =
        (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
          (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
            ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) := hSelected
      _ ≤ (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ * numerator := by
            exact mul_le_mul_of_nonneg_left (by simpa [numerator] using hStream)
              (le_of_lt (inv_pos.mpr hDenomPos))
      _ = numerator / denom := by
            rw [div_eq_mul_inv, hDenomEq]
            ring
      _ =
        (((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
          S.LΨ * S.σ ^ 2 *
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
              (Γ S kp)⁻¹ * S.beta k.1 ^ 2)) /
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1)) := by
            simp [numerator, denom]

/-- The finite stream weighted-gradient sum in Theorem 6.12(b) is integrable
under the adaptive generated-search-gradient L2 boundary. -/
private theorem partB_stream_weighted_gradient_integrable
    (S : Setup n Sample) (N : ℕ) (hAdaptive : AdaptiveOracleProcess S) :
    Integrable
      (fun ξ : ℕ → Sample =>
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
            ‖gradΨ S (xUnder S ξ kp)‖ ^ 2))
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hterm_int :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
              ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) μ := by
    intro k _hk
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    have hbase :
        Integrable (fun ξ : ℕ → Sample => ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) μ := by
      simpa [μ, kp] using generated_search_gradient_sq_integrable_of_adaptiveOracleProcess
        S hAdaptive kp
    simpa [kp, mul_assoc] using
      hbase.const_mul ((Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1))
  simpa [μ] using
    MeasureTheory.integrable_finset_sum (s := (Finset.Icc 1 N).attach)
      (μ := μ) hterm_int

/-- The finite Part B stream noise budget is integrable under the adaptive
generated-error L2 boundary. -/
private theorem partB_noiseBudget_integrable
    (S : Setup n Sample) (N : ℕ) (hAdaptive : AdaptiveOracleProcess S) :
    Integrable
      (fun ξ : ℕ → Sample =>
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
            ‖generatedOracleErrorAt S kp ξ‖ ^ 2))
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hterm_int :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
              ‖generatedOracleErrorAt S kp ξ‖ ^ 2) μ := by
    intro k _hk
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    have hbase :
        Integrable (fun ξ : ℕ → Sample => ‖generatedOracleErrorAt S kp ξ‖ ^ 2) μ := by
      simpa [μ, kp] using generated_oracle_error_sq_integrable_of_adaptiveOracleProcess
        S hAdaptive kp
    refine (hbase.const_mul ((Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2))).congr ?_
    filter_upwards with ξ
    ring
  simpa [μ] using
    MeasureTheory.integrable_finset_sum (s := (Finset.Icc 1 N).attach)
      (μ := μ) hterm_int

/-- The Part B residual multiplier is strict-past measurable under the
adaptive-process boundary. -/
private theorem partB_residual_multiplier_measurable_of_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (xStar : Space n)
    (k : {k : ℕ // k ∈ Finset.Icc 1 N})
    (hAdaptive : AdaptiveOracleProcess S) :
    Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
      (fun ξ : ℕ → Sample =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        ((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
              S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
          S.alpha k.1 • (xStar - x S ξ (k.1 - 1))) := by
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let coeff : ℝ :=
    S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 - S.beta k.1
  have hkpos : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
  have hstate :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
      (k.1 - 1)
  have hx_prev :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hx := hstate.1
    rw [hidx] at hx
    exact hx
  have hxBar_prev :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hxBar := hstate.2
    rw [hidx] at hxBar
    exact hxBar
  have hxUnder :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xUnder S ξ kp) := by
    simpa [kp] using xUnder_measurable_of_prev_measurable S kp hx_prev hxBar_prev
  have hgrad_under :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => gradΨ S (xUnder S ξ kp)) :=
    (gradΨ_measurable S).comp hxUnder
  simpa [kp, coeff] using
    (hgrad_under.const_smul coeff).add
      ((measurable_const.sub hx_prev).const_smul (S.alpha k.1))

/-- The Part B residual multiplier is square-integrable under generated-state
and generated-search-gradient L2 transport. -/
private theorem partB_residual_multiplier_sq_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (xStar : Space n)
    (hAdaptive : AdaptiveOracleProcess S)
    (k : {k : ℕ // k ∈ Finset.Icc 1 N}) :
    Integrable
      (fun ξ : ℕ → Sample =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        ‖((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
              S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
          S.alpha k.1 • (xStar - x S ξ (k.1 - 1))‖ ^ 2)
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let coeff : ℝ :=
    S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 - S.beta k.1
  have hkpos : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
  have hstate_meas :=
    generated_state_adapted_from_error_observable S
      (fun j => oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive j)
      (k.1 - 1)
  have hx_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hx := hstate_meas.1
    rw [hidx] at hx
    exact hx
  have hxBar_prev_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xBar S ξ (k.1 - 1)) := by
    have hidx : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel hkpos
    have hxBar := hstate_meas.2
    rw [hidx] at hxBar
    exact hxBar
  have hxUnder_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample => xUnder S ξ kp) := by
    simpa [kp] using xUnder_measurable_of_prev_measurable S kp
      hx_prev_sub hxBar_prev_sub
  have hx_prev_meas : Measurable (fun ξ : ℕ → Sample => x S ξ (k.1 - 1)) :=
    hx_prev_sub.mono ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hgrad_under_meas :
      Measurable (fun ξ : ℕ → Sample => gradΨ S (xUnder S ξ kp)) :=
    ((gradΨ_measurable S).comp hxUnder_sub).mono
      ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hunder_grad_sq :
      Integrable (fun ξ : ℕ → Sample => ‖gradΨ S (xUnder S ξ kp)‖ ^ 2) μ := by
    simpa [μ, kp] using
      generated_search_gradient_sq_integrable_of_adaptiveOracleProcess S hAdaptive kp
  have hgrad_l2 :
      MemLp (fun ξ : ℕ → Sample => gradΨ S (xUnder S ξ kp)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hgrad_under_meas.aestronglyMeasurable).2
      hunder_grad_sq
  have hx_disp_sq :
      Integrable (fun ξ : ℕ → Sample => ‖S.x0 - x S ξ (k.1 - 1)‖ ^ 2) μ := by
    simpa [μ] using
      (generated_state_l2_of_adaptiveOracleProcess S hAdaptive (k.1 - 1)).1
  have hx_disp_l2 : MemLp (fun ξ : ℕ → Sample => S.x0 - x S ξ (k.1 - 1)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm
      (aestronglyMeasurable_const.sub hx_prev_meas.aestronglyMeasurable)).2
      hx_disp_sq
  have hxStar_disp_l2 :
      MemLp (fun ξ : ℕ → Sample => xStar - x S ξ (k.1 - 1)) 2 μ := by
    have hsum :
        MemLp
          (fun ξ : ℕ → Sample => (xStar - S.x0) + (S.x0 - x S ξ (k.1 - 1))) 2 μ :=
      (memLp_const (xStar - S.x0)).add hx_disp_l2
    refine MemLp.ae_eq ?_ hsum
    filter_upwards with ξ
    module
  have hmult_l2 :
      MemLp
        (fun ξ : ℕ → Sample =>
          coeff • gradΨ S (xUnder S ξ kp) +
            S.alpha k.1 • (xStar - x S ξ (k.1 - 1))) 2 μ :=
    (hgrad_l2.const_smul coeff).add (hxStar_disp_l2.const_smul (S.alpha k.1))
  exact
    (memLp_two_iff_integrable_sq_norm hmult_l2.aestronglyMeasurable).1
      (by simpa [kp, coeff, μ] using hmult_l2)

/-- L1 side condition for the Part B residual scalarization. -/
private theorem partB_residual_inner_integrable_of_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (xStar : Space n)
    (hAdaptive : AdaptiveOracleProcess S)
    (k : {k : ℕ // k ∈ Finset.Icc 1 N}) :
    Integrable
      (fun ξ : ℕ → Sample =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        inner ℝ (generatedOracleErrorAt S kp ξ)
          (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
            S.alpha k.1 • (xStar - x S ξ (k.1 - 1))))
      (S.sampleStreamLaw : Measure (ℕ → Sample)) := by
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let multiplier : (ℕ → Sample) → Space n := fun ξ =>
    ((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
        S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
      S.alpha k.1 • (xStar - x S ξ (k.1 - 1))
  have hmult_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)] multiplier := by
    simpa [multiplier, kp] using
      partB_residual_multiplier_measurable_of_adaptiveOracleProcess
        S N xStar k hAdaptive
  have hmult_meas : Measurable multiplier :=
    hmult_meas_sub.mono ((sampleFiltration (Sample := Sample)).le k.1) le_rfl
  have hmult_sq :
      Integrable (fun ξ : ℕ → Sample => ‖multiplier ξ‖ ^ 2) μ := by
    simpa [multiplier, kp, μ] using
      partB_residual_multiplier_sq_integrable_of_adaptiveOracleProcess
        S N xStar hAdaptive k
  have hδ_sq :
      Integrable (fun ξ : ℕ → Sample => ‖generatedOracleErrorAt S kp ξ‖ ^ 2) μ := by
    simpa [kp, μ] using
      generated_oracle_error_sq_integrable_of_adaptiveOracleProcess S hAdaptive kp
  have hδ_meas_sub :
      Measurable[((sampleFiltration (Sample := Sample)).seq (kp.1 + 1))]
        (fun ξ : ℕ → Sample => generatedOracleErrorAt S kp ξ) :=
    oracleErrorAt_observable_of_adaptiveOracleProcess S hAdaptive kp
  have hδ_meas : Measurable (fun ξ : ℕ → Sample => generatedOracleErrorAt S kp ξ) :=
    hδ_meas_sub.mono ((sampleFiltration (Sample := Sample)).le (kp.1 + 1)) le_rfl
  have hinner :=
    integrable_inner_of_integrable_sq_norm
      (P := μ) (u := fun ξ : ℕ → Sample => generatedOracleErrorAt S kp ξ)
      (v := multiplier)
      hδ_meas.aestronglyMeasurable hmult_meas.aestronglyMeasurable
      hδ_sq hmult_sq
  simpa [multiplier, kp, μ] using hinner

/-- Termwise martingale cancellation for the Part B residual, once its
multiplier is known to be measurable with respect to the strict past. -/
private theorem partB_residual_inner_integral_eq_zero_of_multiplier_measurable
    (S : Setup n Sample) (N : ℕ) (xStar : Space n)
    (k : {k : ℕ // k ∈ Finset.Icc 1 N})
    (_hMeanZero :
      ∀ k : PositiveTime,
        SOptLib.ConditionalExpectation.conditionalExpectationEq
          (S.sampleStreamLaw : Measure (ℕ → Sample))
          ((sampleFiltration (Sample := Sample)).seq k.1)
          (generatedOracleErrorAt S k)
          (0 : (ℕ → Sample) → Space n))
    (hvec_meas :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)]
        (fun ξ : ℕ → Sample =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          ((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
            S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))) :
    (∫ ξ : ℕ → Sample,
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      inner ℝ (generatedOracleErrorAt S kp ξ)
        (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
              S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
          S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 := by
  let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
  let v : (ℕ → Sample) → Space n := fun ξ =>
    ((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
        S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
      S.alpha k.1 • (xStar - x S ξ (k.1 - 1))
  have hv_meas :
      Measurable[((sampleFiltration (Sample := Sample)).seq k.1)] v := by
    simpa [v, kp] using hvec_meas
  have hce := _hMeanZero kp
  rcases SOptLib.ConditionalExpectation.conditionalExpectationEq.wellDefined hce with
    ⟨hm, hsf, hδ_int⟩
  haveI : SigmaFinite ((S.sampleStreamLaw : Measure (ℕ → Sample)).trim hm) := hsf
  have hδ_ce :
      (S.sampleStreamLaw : Measure (ℕ → Sample))[(generatedOracleErrorAt S kp) |
          ((sampleFiltration (Sample := Sample)).seq kp.1)] =ᵐ[
        (S.sampleStreamLaw : Measure (ℕ → Sample))]
          (0 : (ℕ → Sample) → Space n) :=
    SOptLib.ConditionalExpectation.conditionalExpectationEq.ae_eq hce
  have hzero :
      (∫ ξ : ℕ → Sample,
        inner ℝ (generatedOracleErrorAt S kp ξ) ((0 : Space n) - (-v ξ))
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 := by
    exact integral_inner_const_sub_eq_zero_of_condExp_eq_zero
      (P := (S.sampleStreamLaw : Measure (ℕ → Sample)))
      (m := ((sampleFiltration (Sample := Sample)).seq kp.1))
      (δ := generatedOracleErrorAt S kp)
      (x := fun ξ : ℕ → Sample => -v ξ)
      (c := (0 : Space n))
      hm hv_meas.neg hδ_ce hδ_int
  change
    (∫ ξ : ℕ → Sample,
      inner ℝ (generatedOracleErrorAt S kp ξ) (v ξ)
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0
  calc
    (∫ ξ : ℕ → Sample,
      inner ℝ (generatedOracleErrorAt S kp ξ) (v ξ)
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))
        = ∫ ξ : ℕ → Sample,
            inner ℝ (generatedOracleErrorAt S kp ξ) ((0 : Space n) - (-v ξ))
              ∂(S.sampleStreamLaw : Measure (ℕ → Sample)) := by
            apply integral_congr_ae
            filter_upwards with ξ
            simp
    _ = 0 := hzero

/-- The Part B residual finite sum is integrable and has zero integral by
termwise martingale cancellation. -/
private theorem partB_residual_budget_integrable_and_integral_eq_zero
    (S : Setup n Sample) (N : ℕ) (xStar : Space n)
    (hAdaptive : AdaptiveOracleProcess S) :
    Integrable
        (fun ξ : ℕ → Sample =>
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ *
              inner ℝ (generatedOracleErrorAt S kp ξ)
                (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                      S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                  S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))))
        (S.sampleStreamLaw : Measure (ℕ → Sample)) ∧
      (∫ ξ : ℕ → Sample,
        Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ *
            inner ℝ (generatedOracleErrorAt S kp ξ)
              (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                    S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                S.alpha k.1 • (xStar - x S ξ (k.1 - 1))))
        ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  have hMeanZero :
      ∀ k : PositiveTime,
        SOptLib.ConditionalExpectation.conditionalExpectationEq
          (S.sampleStreamLaw : Measure (ℕ → Sample))
          ((sampleFiltration (Sample := Sample)).seq k.1)
          (generatedOracleErrorAt S k)
          (0 : (ℕ → Sample) → Space n) :=
    fun k => oracleErrorAt_condExp_past_eq_zero_of_adaptiveOracleProcess S hAdaptive k
  have hResidualTermIntegrable :
      ∀ k ∈ (Finset.Icc 1 N).attach,
        Integrable
          (fun ξ : ℕ → Sample =>
            let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
            (Γ S kp)⁻¹ *
              inner ℝ (generatedOracleErrorAt S kp ξ)
                (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                      S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                  S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))) μ := by
    intro k _hk
    let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
    have hinner :=
      partB_residual_inner_integrable_of_adaptiveOracleProcess
        S N xStar hAdaptive k
    simpa [kp, μ, mul_assoc] using hinner.const_mul (Γ S kp)⁻¹
  have hResidualInnerIntegralZero :
      ∀ k : {k : ℕ // k ∈ Finset.Icc 1 N},
        (∫ ξ : ℕ → Sample,
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          inner ℝ (generatedOracleErrorAt S kp ξ)
            (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                  S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
              S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) = 0 := by
    intro k
    exact partB_residual_inner_integral_eq_zero_of_multiplier_measurable
      S N xStar k hMeanZero
      (partB_residual_multiplier_measurable_of_adaptiveOracleProcess
        S N xStar k hAdaptive)
  constructor
  · exact MeasureTheory.integrable_finset_sum (s := (Finset.Icc 1 N).attach)
      (μ := μ) hResidualTermIntegrable
  · rw [MeasureTheory.integral_finset_sum]
    · exact Finset.sum_eq_zero (fun k _hk => by
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        have hzero := hResidualInnerIntegralZero k
        rw [MeasureTheory.integral_const_mul]
        simpa [kp, μ] using congrArg (fun z : ℝ => (Γ S kp)⁻¹ * z) hzero)
    · exact hResidualTermIntegrable

/-- Source step 24 for Theorem 6.12(b): the terminal averaged-iterate function
gap at a positive prefix has the displayed expected bound. -/
private theorem partB_terminal_function_gap_integral_le
    (S : Setup n Sample) (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (K : ℕ) (hK : 1 ≤ K) (hsteps : PartBStepCondition S K)
    (xStar : Space n) (hxStar : ∀ x : Space n, S.Ψ xStar ≤ S.Ψ x)
    (hAdaptive : AdaptiveOracleProcess S) :
    (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ K) - S.Ψ xStar
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
      Γ S ⟨K, hK⟩ *
        (((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
          S.LΨ * S.σ ^ 2 *
            Finset.sum (Finset.Icc 1 K).attach (fun j =>
              let jp : PositiveTime := ⟨j.1, (Finset.mem_Icc.mp j.2).1⟩
              (Γ S jp)⁻¹ * S.beta j.1 ^ 2)) := by
  classical
  let μ : Measure (ℕ → Sample) := (S.sampleStreamLaw : Measure (ℕ → Sample))
  let GammaK : ℝ := Γ S ⟨K, hK⟩
  let dist : ℝ := ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2
  let gap : (ℕ → Sample) → ℝ := fun ξ => S.Ψ (xBar S ξ K) - S.Ψ xStar
  let gradBudget : (ℕ → Sample) → ℝ := fun ξ =>
    Finset.sum (Finset.Icc 1 K).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
        ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
  let noiseBudget : (ℕ → Sample) → ℝ := fun ξ =>
    Finset.sum (Finset.Icc 1 K).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
        ‖generatedOracleErrorAt S kp ξ‖ ^ 2)
  let residualBudget : (ℕ → Sample) → ℝ := fun ξ =>
    Finset.sum (Finset.Icc 1 K).attach (fun k =>
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      (Γ S kp)⁻¹ *
        inner ℝ (generatedOracleErrorAt S kp ξ)
          (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
            S.alpha k.1 • (xStar - x S ξ (k.1 - 1))))
  let upper : (ℕ → Sample) → ℝ := fun ξ =>
    GammaK * (dist + noiseBudget ξ + residualBudget ξ)
  have hGammaPos : 0 < GammaK := by
    simpa [GammaK] using Γ_pos S ⟨K, hK⟩
  have hGammaNonneg : 0 ≤ GammaK := le_of_lt hGammaPos
  have _hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe μ (generatedOracleErrorNormSq S k) (S.σ ^ 2) := by
    intro k
    simpa [μ] using oracleErrorAt_secondMoment_le_of_adaptiveOracleProcess S hAdaptive k
  have hGapInt : Integrable gap μ := by
    simpa [gap, μ] using
      generated_xBar_function_gap_integrable_of_adaptiveOracleProcess
        S hAdaptive xStar K
  have hNoiseInt : Integrable noiseBudget μ := by
    simpa [noiseBudget, μ] using partB_noiseBudget_integrable S K hAdaptive
  have hResidual :=
    partB_residual_budget_integrable_and_integral_eq_zero S K xStar hAdaptive
  have hResidualInt : Integrable residualBudget μ := by
    simpa [residualBudget, μ] using hResidual.1
  have hUpperInt : Integrable upper μ := by
    dsimp [upper]
    exact (((integrable_const dist).add hNoiseInt).add hResidualInt).const_mul GammaK
  have hPoint : ∀ᵐ ξ ∂μ, gap ξ ≤ upper ξ := by
    refine Filter.Eventually.of_forall ?_
    intro ξ
    have hpath :=
      partB_pathwise_gamma_terminal_bound S hconvex K hK hsteps ξ xStar
    have hgrad_nonneg : 0 ≤ gradBudget ξ := by
      dsimp [gradBudget]
      refine Finset.sum_nonneg ?_
      intro k _hk
      let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
      have hcoeff_nonneg :
          0 ≤ (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) := by
        have hweight := partBWeight_nonneg_of_steps S K hsteps k.1 k.2
        have hk1 : 1 ≤ k.1 := (Finset.mem_Icc.mp k.2).1
        simpa [partBWeight, kp, hk1] using hweight
      exact mul_nonneg hcoeff_nonneg (sq_nonneg _)
    have hdiv :
        gap ξ / GammaK ≤ dist + noiseBudget ξ + residualBudget ξ := by
      simpa [gap, GammaK, dist, gradBudget, noiseBudget, residualBudget] using
        (by linarith : (S.Ψ (xBar S ξ K) - S.Ψ xStar) / Γ S ⟨K, hK⟩ ≤
          ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
            Finset.sum (Finset.Icc 1 K).attach (fun k =>
              let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
              (Γ S kp)⁻¹ * (S.LΨ * S.beta k.1 ^ 2) *
                ‖generatedOracleErrorAt S kp ξ‖ ^ 2) +
            Finset.sum (Finset.Icc 1 K).attach (fun k =>
              let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
              (Γ S kp)⁻¹ *
                inner ℝ (generatedOracleErrorAt S kp ξ)
                  (((S.LΨ * S.beta k.1 ^ 2 + S.alpha k.1 * S.lam k.1 -
                        S.beta k.1) • gradΨ S (xUnder S ξ kp)) +
                    S.alpha k.1 • (xStar - x S ξ (k.1 - 1)))))
    calc
      gap ξ = (gap ξ / GammaK) * GammaK := by
        field_simp [ne_of_gt hGammaPos]
      _ ≤ (dist + noiseBudget ξ + residualBudget ξ) * GammaK :=
        mul_le_mul_of_nonneg_right hdiv hGammaNonneg
      _ = upper ξ := by
        ring
  have hMono :
      (∫ ξ, gap ξ ∂μ) ≤ ∫ ξ, upper ξ ∂μ :=
    MeasureTheory.integral_mono_ae hGapInt hUpperInt hPoint
  have hUpperIntegral :
      (∫ ξ, upper ξ ∂μ) =
        GammaK *
          (dist + (∫ ξ, noiseBudget ξ ∂μ) +
            (∫ ξ, residualBudget ξ ∂μ)) := by
    dsimp [upper]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add
      (f := fun ξ : ℕ → Sample => dist + noiseBudget ξ)
      (g := residualBudget)
      ((integrable_const dist).add hNoiseInt) hResidualInt]
    rw [MeasureTheory.integral_add
      (f := fun _ : ℕ → Sample => dist)
      (g := noiseBudget)
      (integrable_const dist) hNoiseInt]
    simp [μ]
  have hNoiseLe :
      (∫ ξ, noiseBudget ξ ∂μ) ≤
        S.LΨ * S.σ ^ 2 *
          Finset.sum (Finset.Icc 1 K).attach (fun j =>
            let jp : PositiveTime := ⟨j.1, (Finset.mem_Icc.mp j.2).1⟩
            (Γ S jp)⁻¹ * S.beta j.1 ^ 2) := by
    simpa [noiseBudget, μ] using partB_noiseBudget_integral_le S K _hSecondMoment
  have hResidualZero : (∫ ξ, residualBudget ξ ∂μ) = 0 := by
    simpa [residualBudget, μ] using hResidual.2
  calc
    (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ K) - S.Ψ xStar
      ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))
        = ∫ ξ, gap ξ ∂μ := by rfl
    _ ≤ ∫ ξ, upper ξ ∂μ := hMono
    _ = GammaK *
          (dist + (∫ ξ, noiseBudget ξ ∂μ) +
            (∫ ξ, residualBudget ξ ∂μ)) := hUpperIntegral
    _ ≤ GammaK *
          (dist +
            S.LΨ * S.σ ^ 2 *
              Finset.sum (Finset.Icc 1 K).attach (fun j =>
                let jp : PositiveTime := ⟨j.1, (Finset.mem_Icc.mp j.2).1⟩
                (Γ S jp)⁻¹ * S.beta j.1 ^ 2)) := by
          rw [hResidualZero, add_zero]
          exact mul_le_mul_of_nonneg_left
            (add_le_add_right hNoiseLe dist) hGammaNonneg
    _ =
      Γ S ⟨K, hK⟩ *
        (((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
          S.LΨ * S.σ ^ 2 *
            Finset.sum (Finset.Icc 1 K).attach (fun j =>
              let jp : PositiveTime := ⟨j.1, (Finset.mem_Icc.mp j.2).1⟩
              (Γ S jp)⁻¹ * S.beta j.1 ^ 2)) := by
          simp [GammaK, dist]

/-- Conditional-process helper for Theorem 6.12(b).

This helper is separated from the paper statement because the proof again uses
conditional cancellation of the generated oracle noise at adaptive search
points. The printed paper conclusion is `theorem612_partB_statement`; this
helper is a corrected non-original proof boundary. -/
theorem theorem612_partB_under_adaptiveOracleProcess
    (S : Setup n Sample) (N : ℕ) (hN : 1 ≤ N)
    (hconvex : ConvexOn ℝ Set.univ S.Ψ)
    (xStar : Space n) (hxStar : ∀ x : Space n, S.Ψ xStar ≤ S.Ψ x)
    (hsteps : PartBStepCondition S N)
    (hAdaptive : AdaptiveOracleProcess S) :
    theorem612_partB_statement S N hN hconvex xStar hxStar hsteps := by
  have _hSecondMoment :
      ∀ k : PositiveTime,
        expectationLe (S.sampleStreamLaw : Measure (ℕ → Sample))
          (generatedOracleErrorNormSq S k) (S.σ ^ 2) :=
    fun k => oracleErrorAt_secondMoment_le_of_adaptiveOracleProcess S hAdaptive k
  unfold theorem612_partB_statement
  constructor
  · have hWeightedGradIntegrable :=
      partB_stream_weighted_gradient_integrable S N hAdaptive
    have hNoiseIntegrable :=
      partB_noiseBudget_integrable S N hAdaptive
    have hResidual :=
      partB_residual_budget_integrable_and_integral_eq_zero S N xStar hAdaptive
    have hStream :
        (∫ ξ, Finset.sum (Finset.Icc 1 N).attach (fun k =>
          let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
          (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
            ‖gradΨ S (xUnder S ξ kp)‖ ^ 2)
          ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤
          ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
            S.LΨ * S.σ ^ 2 *
              Finset.sum (Finset.Icc 1 N).attach (fun k =>
                let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
                (Γ S kp)⁻¹ * S.beta k.1 ^ 2) :=
      partB_stream_weighted_gradient_integral_le_of_residual
        S hconvex N hN hsteps xStar hxStar _hSecondMoment
        hWeightedGradIntegrable hNoiseIntegrable hResidual.1 hResidual.2
    exact partB_selected_gradient_bound_of_stream_bound
      S N hN xStar hsteps hAdaptive hStream
  · classical
    let numerator : ℝ :=
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        S.beta k.1 * (1 - S.LΨ * S.beta k.1) *
          (((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
            S.LΨ * S.σ ^ 2 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun j =>
                let jp : PositiveTime := ⟨j.1, (Finset.mem_Icc.mp j.2).1⟩
                (Γ S jp)⁻¹ * S.beta j.1 ^ 2)))
    let denom : ℝ :=
      Finset.sum (Finset.Icc 1 N).attach (fun k =>
        let kp : PositiveTime := ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩
        (Γ S kp)⁻¹ * S.beta k.1 * (1 - S.LΨ * S.beta k.1))
    refine SOptLib.expectationLe_of_integrable_integral_le ?_ ?_
    · exact
        (partB_selected_function_gap_integrable_and_integral_eq_stream_weighted
          S N hN hsteps hAdaptive xStar).1
    · have hSelected :=
        (partB_selected_function_gap_integrable_and_integral_eq_stream_weighted
          S N hN hsteps hAdaptive xStar).2
      have hDenomPos : 0 < Finset.sum (Finset.Icc 1 N) (partBWeight S) :=
        partBWeight_sum_pos_of_steps S N hN hsteps
      have hDenomEq :
          denom = Finset.sum (Finset.Icc 1 N) (partBWeight S) := by
        simpa [denom] using partB_display_denominator_eq_partBWeight_sum S N
      have hWeightedLe :
          Finset.sum (Finset.Icc 1 N).attach (fun k =>
            partBWeight S k.1 *
              (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
                ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))) ≤ numerator := by
        dsimp [numerator]
        refine Finset.sum_le_sum ?_
        intro k _hk
        have hkcond : 1 ≤ k.1 ∧ k.1 ≤ N := Finset.mem_Icc.mp k.2
        have hkpos : 1 ≤ k.1 := hkcond.1
        have hkN : k.1 ≤ N := hkcond.2
        let kp : PositiveTime := ⟨k.1, hkpos⟩
        let budget : ℝ :=
          ((2 * S.lam 1)⁻¹) * ‖S.x0 - xStar‖ ^ 2 +
            S.LΨ * S.σ ^ 2 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun j =>
                let jp : PositiveTime := ⟨j.1, (Finset.mem_Icc.mp j.2).1⟩
                (Γ S jp)⁻¹ * S.beta j.1 ^ 2)
        have hsteps_prefix : PartBStepCondition S k.1 :=
          partBStepCondition_restrict S hkpos hkN hsteps
        have hTerminal :
            (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
              ∂(S.sampleStreamLaw : Measure (ℕ → Sample))) ≤ Γ S kp * budget := by
          simpa [kp, budget] using
            partB_terminal_function_gap_integral_le
              S hconvex k.1 hkpos hsteps_prefix xStar hxStar hAdaptive
        have hweight_nonneg :
            0 ≤ partBWeight S k.1 :=
          partBWeight_nonneg_of_steps S N hsteps k.1 k.2
        calc
          partBWeight S k.1 *
              (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
                ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))
              ≤ partBWeight S k.1 * (Γ S kp * budget) := by
                exact mul_le_mul_of_nonneg_left hTerminal hweight_nonneg
          _ = S.beta k.1 * (1 - S.LΨ * S.beta k.1) * budget := by
                have hΓne :
                    Γ S ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩ ≠ 0 :=
                  ne_of_gt (Γ_pos S ⟨k.1, (Finset.mem_Icc.mp k.2).1⟩)
                unfold partBWeight
                simp [kp, hkpos]
                field_simp [hΓne]
      calc
        (∫ q, selectedFunctionGap S N xStar q
          ∂selectedJointLawPartB S N hN hsteps)
            =
          (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ *
            Finset.sum (Finset.Icc 1 N).attach (fun k =>
              partBWeight S k.1 *
                (∫ ξ : ℕ → Sample, S.Ψ (xBar S ξ k.1) - S.Ψ xStar
                  ∂(S.sampleStreamLaw : Measure (ℕ → Sample)))) := hSelected
        _ ≤ (Finset.sum (Finset.Icc 1 N) (partBWeight S))⁻¹ * numerator := by
              exact mul_le_mul_of_nonneg_left hWeightedLe
                (le_of_lt (inv_pos.mpr hDenomPos))
        _ = numerator / denom := by
              rw [div_eq_mul_inv, hDenomEq]
              ring

end

end NonconvexStochasticAcceleratedGD
end FOML
end SOptLib
