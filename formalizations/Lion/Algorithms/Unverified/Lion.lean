import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import SOptLib.Model.Iterates
import SOptLib.Model.ParameterChoices
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Telescope

/-! Centralized Lion: Algorithm 1 (v1) and Theorem 1 of Jiang and Zhang (2025).

This file records the object layer for the centralized original Lion optimizer.  The
algorithmic state is generated from Algorithm 1, including the first-step sampled-gradient
initialization, rather than supplied as witness iterate and momentum processes.  The
paper-facing probability space is the canonical iid stream law generated from the stochastic
oracle law.
-/

open scoped BigOperators Gradient InnerProductSpace
open MeasureTheory

namespace Algorithms.Unverified.Lion

noncomputable section

universe u

/-- The paper's ambient space `ℝ^d`, represented as Mathlib Euclidean space. -/
abbrev Point (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- Coordinatewise sign used by Lion's update. -/
def coordinateSign {d : ℕ} (x : Point d) : Point d :=
  WithLp.toLp 2 fun i => Real.sign (x i)

/-- The finite-coordinate `ℓ₁` norm appearing in Theorem 1. -/
def l1Norm {d : ℕ} (x : Point d) : ℝ :=
  ∑ i, |x i|

/-- The finite-coordinate `ℓ∞` norm used for the initial-point restriction. -/
def linfNorm {d : ℕ} [Nonempty (Fin d)] (x : Point d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |x i|

/-- Source-facing data for centralized original Lion.

Book citations:
* `book/research/Lion.json#/setup/problem`: `\min_{x\in\mathbb{R}^d} f(x)`.
* `book/research/Lion.json#/setup/variable_space`: `f : \mathbb{R}^d \to \mathbb{R}`.
* `book/research/Lion.json#/setup/stochastic_oracle`: "Only noisy gradient estimates are
  available, with `\xi` drawn from a stochastic oracle."

The stochastic-gradient kernel is primitive paper data.  The sample-stream probability
space, sampled oracle values, and generated iterates are derived below. -/
structure Setup (d : ℕ) where
  Sample : Type u
  sampleMeasurable : MeasurableSpace Sample
  oracleLaw : @Measure Sample sampleMeasurable
  oracleLaw_isProbability : MeasureTheory.IsProbabilityMeasure oracleLaw
  f : Point d → ℝ
  stochasticGradient : Point d → Sample → Point d
  L : ℝ
  sigma : ℝ
  Delta_f : ℝ
  beta1 : ℝ
  beta2 : ℝ
  eta : ℝ
  lambda : ℝ
  x1 : Point d

namespace Setup

/-- The paper's stochastic-oracle law is a probability law for oracle samples. -/
instance instOracleLawIsProbabilityMeasure {d : ℕ} (s : Setup d) :
    MeasureTheory.IsProbabilityMeasure s.oracleLaw :=
  s.oracleLaw_isProbability

/-- The canonical true gradient `∇ f(x)` associated with the paper objective. -/
def trueGradient {d : ℕ} (s : Setup d) (x : Point d) : Point d :=
  ∇ s.f x

/-- The stochastic oracle value `∇ f(x; ξ)`, derived from the primitive oracle kernel. -/
def oracleValue {d : ℕ} (s : Setup d) (x : Point d) (ξ : s.Sample) : Point d :=
  s.stochasticGradient x ξ

@[simp]
theorem oracleValue_eq {d : ℕ} (s : Setup d) (x : Point d) (ξ : s.Sample) :
    s.oracleValue x ξ = s.stochasticGradient x ξ := by
  rfl

/-- Assumption 4's objective infimum `f_* = inf_x f(x)`, defined from the objective rather
than supplied as a lower-bound witness. -/
def fStar {d : ℕ} (s : Setup d) : ℝ :=
  sInf (Set.range s.f)

/-- Definitional equation for the canonical objective infimum wrapper. -/
theorem fStar_eq_sInf_range {d : ℕ} (s : Setup d) :
    s.fStar = sInf (Set.range s.f) := by
  rfl

/-- Assumption 1: `L`-smoothness through Lipschitz continuity of the true gradient.

Book citation: `book/research/Lion.json#/assumptions[name=Assumption_1_Smoothness]`,
`\|\nabla f(x)-\nabla f(y)\| \le L\|x-y\|`. -/
def Smoothness {d : ℕ} (s : Setup d) : Prop :=
  (∀ x : Point d, HasGradientAt s.f (s.trueGradient x) x) ∧
    ∀ x y : Point d, ‖s.trueGradient x - s.trueGradient y‖ ≤ s.L * ‖x - y‖

/-- Assumption 1 provides the derivative realization of the Mathlib gradient. -/
theorem smoothness_hasGradientAt {d : ℕ} {s : Setup d} (h : s.Smoothness)
    (x : Point d) :
    HasGradientAt s.f (s.trueGradient x) x :=
  h.1 x

/-- Assumption 1 provides the Lipschitz-gradient inequality. -/
theorem smoothness_lipschitz_trueGradient {d : ℕ} {s : Setup d} (h : s.Smoothness)
    (x y : Point d) :
    ‖s.trueGradient x - s.trueGradient y‖ ≤ s.L * ‖x - y‖ :=
  h.2 x y

/-- Assumption 3, unbiasedness part, stated over the source oracle probability law with
the Bochner expectation well-defined.

Book citation: `book/research/Lion.json#/assumptions[name=Assumption_3_UnbiasedBoundedNoise]`,
`\mathbb{E}_{\xi}[\nabla f(x;\xi)] = \nabla f(x)`. -/
def OracleUnbiased {d : ℕ} (s : Setup d) : Prop :=
  letI := s.sampleMeasurable
  ∀ x : Point d,
    Integrable (fun ξ => s.oracleValue x ξ) s.oracleLaw ∧
      ∫ ξ, s.oracleValue x ξ ∂s.oracleLaw = s.trueGradient x

/-- Assumption 3, bounded-noise part, stated over the source oracle probability law with
the second-moment expectation well-defined.

Book citation: `book/research/Lion.json#/assumptions[name=Assumption_3_UnbiasedBoundedNoise]`,
`\mathbb{E}_{\xi}[\|\nabla f(x;\xi)-\nabla f(x)\|^2] \le \sigma^2`. -/
def OracleBoundedNoise {d : ℕ} (s : Setup d) : Prop :=
  letI := s.sampleMeasurable
  ∀ x : Point d,
    Integrable (fun ξ => ‖s.oracleValue x ξ - s.trueGradient x‖ ^ 2) s.oracleLaw ∧
      ∫ ξ, ‖s.oracleValue x ξ - s.trueGradient x‖ ^ 2 ∂s.oracleLaw ≤
        s.sigma ^ 2

/-- Assumption 3 projects fixed-query stochastic-gradient integrability. -/
theorem oracleUnbiased_integrable {d : ℕ} {s : Setup d} (h : s.OracleUnbiased)
    (x : Point d) :
    (letI := s.sampleMeasurable;
      Integrable (fun ξ => s.oracleValue x ξ) s.oracleLaw) :=
  (h x).1

/-- Assumption 3 projects the fixed-query unbiasedness equality. -/
theorem oracleUnbiased_integral_eq {d : ℕ} {s : Setup d} (h : s.OracleUnbiased)
    (x : Point d) :
    (letI := s.sampleMeasurable;
      ∫ ξ, s.oracleValue x ξ ∂s.oracleLaw) = s.trueGradient x :=
  (h x).2

/-- Assumption 3 projects fixed-query squared-noise integrability. -/
theorem oracleBoundedNoise_integrable {d : ℕ} {s : Setup d} (h : s.OracleBoundedNoise)
    (x : Point d) :
    (letI := s.sampleMeasurable;
      Integrable (fun ξ => ‖s.oracleValue x ξ - s.trueGradient x‖ ^ 2) s.oracleLaw) :=
  (h x).1

/-- Assumption 3 projects the fixed-query bounded-noise inequality. -/
theorem oracleBoundedNoise_integral_le {d : ℕ} {s : Setup d} (h : s.OracleBoundedNoise)
    (x : Point d) :
    (letI := s.sampleMeasurable;
      ∫ ξ, ‖s.oracleValue x ξ - s.trueGradient x‖ ^ 2 ∂s.oracleLaw) ≤
        s.sigma ^ 2 :=
  (h x).2

/-- Assumption 4: `f_*` is the objective infimum and the initial objective gap is bounded.

Book citation: `book/research/Lion.json#/assumptions[name=Assumption_4_InitialGap]`,
`f_* = \inf_x f(x) \ge -\infty` and `f(x_1)-f_* \le \Delta_f`. -/
def InitialGap {d : ℕ} (s : Setup d) : Prop :=
  IsGLB (Set.range s.f) s.fStar ∧ s.f s.x1 - s.fStar ≤ s.Delta_f

/-- Assumption 4 projects the source statement that `f_* = inf_x f(x)`. -/
theorem initialGap_fStar_is_glb {d : ℕ} {s : Setup d} (h : s.InitialGap) :
    IsGLB (Set.range s.f) s.fStar :=
  h.1

/-- Assumption 4 projects the source initial-gap bound. -/
theorem initialGap_bound {d : ℕ} {s : Setup d} (h : s.InitialGap) :
    s.f s.x1 - s.fStar ≤ s.Delta_f :=
  h.2

/-- Replace only the horizon-dependent Lion parameters, leaving the objective, oracle, and
initial point fixed. -/
def withParameters {d : ℕ} (s : Setup d) (beta1 beta2 eta lambda : ℝ) : Setup d :=
  { s with
    beta1 := beta1
    beta2 := beta2
    eta := eta
    lambda := lambda }

end Setup

/-- Horizon-dependent parameter choices in Theorem 1.

Book citation: `book/research/Lion.json#/main_theorem/statement_math`, with
`\beta_2=O(T^{-1/2})`, `\eta=O(d^{-1/2}T^{-3/4})`, and
`\lambda \le \frac{1}{2\eta T}`. -/
structure ParameterSchedule where
  beta1 : ℕ → ℝ
  beta2 : ℕ → ℝ
  eta : ℕ → ℝ
  lambda : ℕ → ℝ

namespace ParameterSchedule

/-- Instantiate the fixed problem/oracle data with the parameters selected for horizon `T`. -/
def setupAt {d : ℕ} (p : ParameterSchedule) (s : Setup d) (T : ℕ) : Setup d :=
  s.withParameters (p.beta1 T) (p.beta2 T) (p.eta T) (p.lambda T)

end ParameterSchedule

/-- A paper-displayed scalar quotient, modeled without Mathlib's totalized division.

The source writes ordinary quotients such as `1/(2ηT)`, `1/(β₂T)`, and `1/β₂²`.
SOptLib's checked quotient records the exact denominator-definedness obligation carried by
those displayed expressions, while keeping that obligation local to the expression that
uses the quotient. -/
def sourceQuotient (numerator denominator value : ℝ) : Prop :=
  SOptLib.checked_quotient_spec numerator denominator value

/-- The displayed quotient relation exposes the denominator nonzero fact needed to use it. -/
theorem sourceQuotient_denominator_ne {numerator denominator value : ℝ}
    (h : sourceQuotient numerator denominator value) :
    denominator ≠ 0 :=
  h.1

/-- A checked source quotient agrees with ordinary division after the denominator
obligation has been exposed. -/
theorem sourceQuotient_eq_div {numerator denominator value : ℝ}
    (h : sourceQuotient numerator denominator value) :
    value = numerator / denominator :=
  SOptLib.eq_div_of_checked_quotient_spec h

/-- Source-facing inequality against a displayed quotient, without interpreting a
zero-denominator fallback as paper mathematics. -/
def sourceLeQuotient (lhs numerator denominator : ℝ) : Prop :=
  ∃ value : ℝ, sourceQuotient numerator denominator value ∧ lhs ≤ value

/-- Syntactic Lean rendering of a quotient inequality printed by the paper.

This records the displayed source condition without turning denominator nonzero into a
source-facing theorem-head assumption.  The semantic denominator/contraction facts needed by
Appendix A/B are recorded separately as named source-gap obligations below. -/
def paperDisplayedLeQuotient (lhs numerator denominator : ℝ) : Prop :=
  lhs ≤ numerator / denominator

/-- The paper-displayed quotient inequality unfolds to the corresponding Lean inequality. -/
theorem paperDisplayedLeQuotient_eq {lhs numerator denominator : ℝ} :
    paperDisplayedLeQuotient lhs numerator denominator ↔ lhs ≤ numerator / denominator := by
  rfl

/-- Theorem 1's momentum-order condition alone permits the zero-momentum boundary
`β₁ = β₂ = 0`; this records why later `β` denominators must remain local
source-definedness obligations rather than hidden totalized divisions. -/
theorem momentum_order_allows_zero_beta :
    (0 : ℝ) ^ 2 ≤ 0 ∧ 0 ≤ Real.sqrt 0 ∧ (0 : ℝ) = 0 := by
  norm_num

/-- Internal domain needed by the Appendix B quotient and coefficient manipulations.

The paper states only `β₂² ≤ β₁ ≤ sqrt β₂`; targeted PDF extraction did not find this
positivity/range condition as a primitive Theorem 1 assumption. -/
def MomentumParameterDomainAt (beta1 beta2 : ℝ) : Prop :=
  0 < beta1 ∧ 0 < beta2 ∧ beta1 ≤ 1 ∧ beta2 ≤ 1

/-- Corrected non-original momentum quotient domain for one finite horizon.

Appendix B uses the displayed quotients `1/β₁`, `1/(β₂T)`, and `1/β₂²`.  The source
does not state their denominator domain as primitive Theorem 1 assumptions, so this
contract is kept in the corrected-boundary layer. -/
def MomentumQuotientDomainAt (beta1 beta2 : ℝ) (T : ℕ) : Prop :=
  MomentumParameterDomainAt beta1 beta2 ∧
    (∃ invBeta1 : ℝ, sourceQuotient 1 beta1 invBeta1) ∧
      (∃ invBeta2T : ℝ, sourceQuotient 1 (beta2 * (T : ℝ)) invBeta2T) ∧
        (∃ invBeta2Sq : ℝ, sourceQuotient 1 (beta2 ^ 2) invBeta2Sq)

/-- Internal contraction domain needed by Appendix A when `(1 - ηλ)` is used as a
nonnegative contraction coefficient.

The paper uses this domain in the proof of Lemma 1, but targeted PDF extraction did not
find it stated as a separate primitive assumption. -/
def EtaLambdaContractionDomainAt (eta lambda : ℝ) : Prop :=
  0 ≤ 1 - eta * lambda ∧ 1 - eta * lambda ≤ 1

/-- Corrected non-original learning-rate/weight-decay domain for one finite horizon.

Appendix A uses `(1 - ηλ)` as a nonnegative contraction, and Appendix B uses the
displayed quotient `1/(ηT)`.  These facts are not stated as primitive Theorem 1
assumptions in the source. -/
def EtaLambdaHorizonDomainAt (eta lambda : ℝ) (T : ℕ) : Prop :=
  0 < eta ∧
    EtaLambdaContractionDomainAt eta lambda ∧
      ∃ invEtaT : ℝ, sourceQuotient 1 (eta * (T : ℝ)) invEtaT

/-- The canonical sample-stream path space for the paper's stochastic oracle draws. -/
abbrev Run {d : ℕ} (s : Setup d) : Type u :=
  ℕ → s.Sample

/-- The canonical product measurable space on oracle-sample streams. -/
instance instRunMeasurableSpace {d : ℕ} (s : Setup d) : MeasurableSpace (Run s) := by
  letI := s.sampleMeasurable
  infer_instance

namespace Run

/-- The canonical iid law on source-sample streams, generated from the oracle law. -/
def law {d : ℕ} (s : Setup d) : Measure (Run s) :=
  letI := s.sampleMeasurable
  SOptLib.iidStreamLaw s.oracleLaw

/-- The paper's one-based sample `ξ_t` read from the zero-based iid stream. -/
def sampleAt {d : ℕ} (s : Setup d) (t : ℕ) : Run s → s.Sample :=
  fun ω => ω (t - 1)

/-- The generated run law is definitionally the iid stream law of the source oracle law. -/
theorem law_eq_iidStreamLaw {d : ℕ} (s : Setup d) :
    (law s) =
      (letI := s.sampleMeasurable; SOptLib.iidStreamLaw s.oracleLaw) := by
  rfl

/-- The generated iid sample-stream law is a probability measure. -/
instance instLawIsProbabilityMeasure {d : ℕ} (s : Setup d) :
    MeasureTheory.IsProbabilityMeasure (law s) := by
  letI := s.sampleMeasurable
  simpa [law] using (SOptLib.iidStreamLaw_isProbabilityMeasure s.oracleLaw)

/-- Each paper-time sample coordinate has the source oracle law under the generated run law.
This is an iid-stream bridge, not an extra paper-facing theorem hypothesis. -/
theorem map_sampleAt_law {d : ℕ} (s : Setup d) (t : ℕ) :
    (letI := s.sampleMeasurable; Measure.map (sampleAt s t) (law s) = s.oracleLaw) := by
  letI := s.sampleMeasurable
  simpa [law, sampleAt] using
    (SOptLib.iidStreamLaw_map_eval (mu := s.oracleLaw) (t := t - 1))

end Run

/-- Lion v1 state at a paper time: iterate `x_t`, original momentum `m_t`, and lookahead
momentum `v_t`. -/
structure State (d : ℕ) where
  x : Point d
  m : Point d
  v : Point d

/-- The sampled gradient value `G_t(x) = ∇ f(x; ξ_t)` along the canonical sample stream. -/
def sampledGradient {d : ℕ} (s : Setup d) (t : ℕ) (x : Point d) (ω : Run s) :
    Point d :=
  s.oracleValue x (Run.sampleAt s t ω)

@[simp]
theorem sampledGradient_eq {d : ℕ} (s : Setup d) (t : ℕ) (x : Point d) (ω : Run s) :
    sampledGradient s t x ω = s.stochasticGradient x (ω (t - 1)) := by
  rfl

/-- The decoupled weight-decay sign step `x - η (sign(v) + λ x)`. -/
def nextX {d : ℕ} (s : Setup d) (state : State d) : Point d :=
  state.x - s.eta • (coordinateSign state.v + s.lambda • state.x)

/-- The first-step initialization `v₁ = m₁ = ∇ f(x₁; ξ₁)`.

Book citation: `book/research/Lion.json#/algorithm_spec/initialization`,
`v_1=m_1=\nabla f(x_1;\xi_1)`. -/
def initialState {d : ℕ} (s : Setup d) : Run s → State d :=
  fun ω =>
    let g1 := sampledGradient s 1 s.x1 ω
    { x := s.x1, m := g1, v := g1 }

/-- One original-Lion transition from paper time `n + 1` to paper time `n + 2`.

The new iterate is computed from `v_t`, and the same fresh sample `ξ_{t+1}` is used in
both momentum updates.

Book citations:
* `book/research/Lion.json#/algorithm_spec/steps[name=sign_weight_decay_update]`,
  `x_{t+1}=x_t-\eta(\operatorname{sign}(v_t)+\lambda x_t)`.
* `book/research/Lion.json#/algorithm_spec/steps[name=original_momentum_m]`,
  `m_t=(1-\beta_2)m_{t-1}+\beta_2\nabla f(x_t;\xi_t)`.
* `book/research/Lion.json#/algorithm_spec/steps[name=lookahead_momentum_v]`,
  `v_t=(1-\beta_1)m_{t-1}+\beta_1\nabla f(x_t;\xi_t)`. -/
def transition {d : ℕ} (s : Setup d) (n : ℕ) (state : State d) (ω : Run s) :
    State d :=
  let xNext := nextX s state
  let gNext := sampledGradient s (n + 2) xNext ω
  { x := xNext
    m := (1 - s.beta2) • state.m + s.beta2 • gNext
    v := (1 - s.beta1) • state.m + s.beta1 • gNext }

/-- The generated centralized original-Lion state process.  Zero-based process index `0`
is paper time `1`. -/
def process {d : ℕ} (s : Setup d) : ℕ → Run s → State d :=
  SOptLib.recursive_process_from_random_initial (initialState s) (transition s)

/-- Paper-time state view: `stateAt t` denotes `(x_t,m_t,v_t)`. -/
def stateAt {d : ℕ} (s : Setup d) (t : ℕ) : Run s → State d :=
  process s (t - 1)

/-- The generated paper iterate `x_t`. -/
def x {d : ℕ} (s : Setup d) (t : ℕ) (ω : Run s) : Point d :=
  (stateAt s t ω).x

/-- The generated original momentum `m_t`. -/
def m {d : ℕ} (s : Setup d) (t : ℕ) (ω : Run s) : Point d :=
  (stateAt s t ω).m

/-- The generated lookahead momentum `v_t`. -/
def v {d : ℕ} (s : Setup d) (t : ℕ) (ω : Run s) : Point d :=
  (stateAt s t ω).v

/-- The sampled gradient at the generated iterate, `G_t = ∇ f(x_t; ξ_t)`. -/
def G {d : ℕ} (s : Setup d) (t : ℕ) (ω : Run s) : Point d :=
  sampledGradient s t (x s t ω) ω

@[simp]
theorem initialState_x {d : ℕ} (s : Setup d) (ω : Run s) :
    (initialState s ω).x = s.x1 := by
  rfl

@[simp]
theorem initialState_m {d : ℕ} (s : Setup d) (ω : Run s) :
    (initialState s ω).m = sampledGradient s 1 s.x1 ω := by
  rfl

@[simp]
theorem initialState_v {d : ℕ} (s : Setup d) (ω : Run s) :
    (initialState s ω).v = sampledGradient s 1 s.x1 ω := by
  rfl

@[simp]
theorem process_zero {d : ℕ} (s : Setup d) :
    process s 0 = initialState s := by
  rfl

@[simp]
theorem process_succ {d : ℕ} (s : Setup d) (n : ℕ) :
    process s (n + 1) = fun ω => transition s n (process s n ω) ω := by
  rfl

theorem transition_x {d : ℕ} (s : Setup d) (n : ℕ) (state : State d) (ω : Run s) :
    (transition s n state ω).x = nextX s state := by
  rfl

theorem transition_m {d : ℕ} (s : Setup d) (n : ℕ) (state : State d) (ω : Run s) :
    (transition s n state ω).m =
      (1 - s.beta2) • state.m + s.beta2 • sampledGradient s (n + 2) (nextX s state) ω := by
  rfl

theorem transition_v {d : ℕ} (s : Setup d) (n : ℕ) (state : State d) (ω : Run s) :
    (transition s n state ω).v =
      (1 - s.beta1) • state.m + s.beta1 • sampledGradient s (n + 2) (nextX s state) ω := by
  rfl

/-- Algorithm 1, line 6, for the generated process. -/
theorem x_succ_eq_update {d : ℕ} (s : Setup d) {t : ℕ} (ht : 1 ≤ t) (ω : Run s) :
    x s (t + 1) ω =
      x s t ω - s.eta • (coordinateSign (v s t ω) + s.lambda • x s t ω) := by
  have htm1 : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have htp1 : t + 1 - 1 = t := Nat.add_sub_cancel t 1
  simp only [x, v, stateAt, htp1]
  conv_lhs => rw [← htm1]
  rw [process_succ]
  rw [transition_x]
  simp only [nextX]

/-- Algorithm 1, line 4 (v1), for the generated process. -/
theorem m_succ_eq_original_momentum {d : ℕ} (s : Setup d) {t : ℕ} (ht : 1 ≤ t)
    (ω : Run s) :
    m s (t + 1) ω =
      (1 - s.beta2) • m s t ω + s.beta2 • G s (t + 1) ω := by
  have htm1 : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have htp1 : t + 1 - 1 = t := Nat.add_sub_cancel t 1
  have hn2 : t - 1 + 2 = t + 1 := by omega
  have hxproc : (process s t ω).x = nextX s (process s (t - 1) ω) := by
    conv_lhs => rw [← htm1]
    rw [process_succ]
    rw [transition_x]
  have hmproc :
      (process s t ω).m =
        (1 - s.beta2) • (process s (t - 1) ω).m +
          s.beta2 • sampledGradient s (t - 1 + 2) (nextX s (process s (t - 1) ω)) ω := by
    conv_lhs => rw [← htm1]
    rw [process_succ]
    rw [transition_m]
  simpa [m, G, x, stateAt, htp1, hn2, hxproc] using hmproc

/-- Algorithm 1, line 3, for the generated process. -/
theorem v_succ_eq_lookahead_momentum {d : ℕ} (s : Setup d) {t : ℕ} (ht : 1 ≤ t)
    (ω : Run s) :
    v s (t + 1) ω =
      (1 - s.beta1) • m s t ω + s.beta1 • G s (t + 1) ω := by
  have htm1 : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have htp1 : t + 1 - 1 = t := Nat.add_sub_cancel t 1
  have hn2 : t - 1 + 2 = t + 1 := by omega
  have hxproc : (process s t ω).x = nextX s (process s (t - 1) ω) := by
    conv_lhs => rw [← htm1]
    rw [process_succ]
    rw [transition_x]
  have hvproc :
      (process s t ω).v =
        (1 - s.beta1) • (process s (t - 1) ω).m +
          s.beta1 • sampledGradient s (t - 1 + 2) (nextX s (process s (t - 1) ω)) ω := by
    conv_lhs => rw [← htm1]
    rw [process_succ]
    rw [transition_v]
  simpa [v, m, G, x, stateAt, htp1, hn2, hxproc] using hvproc

private theorem v_succ_estimator_error_decomp {d : ℕ} {s : Setup d} {t : ℕ}
    (ht : 1 ≤ t) (ω : Run s) :
    v s (t + 1) ω - s.trueGradient (x s (t + 1) ω) =
      s.beta1 • (G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)) +
        (1 - s.beta1) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))) := by
  rw [v_succ_eq_lookahead_momentum s ht ω]
  module

private theorem m_succ_estimator_error_decomp {d : ℕ} {s : Setup d} {t : ℕ}
    (ht : 1 ≤ t) (ω : Run s) :
    m s (t + 1) ω - s.trueGradient (x s (t + 1) ω) =
      s.beta2 • (G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)) +
        (1 - s.beta2) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))) := by
  rw [m_succ_eq_original_momentum s ht ω]
  module

/-- Source-stated assumptions and pointwise parameter restrictions used by the finite-horizon
Appendix B inequality.  Asymptotic `O(·)` schedule assumptions are kept in
`TheoremOneScheduleAssumptions`, the paper-facing theorem boundary below.

Book citations:
* `book/research/Lion.json#/assumptions[name=Assumption_1_Smoothness]`,
  `\|\nabla f(x)-\nabla f(y)\| \le L\|x-y\|`.
* `book/research/Lion.json#/assumptions[name=Assumption_3_UnbiasedBoundedNoise]`,
  stochastic-gradient unbiasedness and bounded noise.
* `book/research/Lion.json#/assumptions[name=Assumption_4_InitialGap]`, initial gap.
* `book/research/Lion.json#/assumptions[name=Theorem1_MomentumOrder]`,
  `\beta_2^2 \le \beta_1 \le \sqrt{\beta_2}`.
* `book/research/Lion.json#/assumptions[name=Theorem1_WeightDecayBound]`,
  `\lambda \le \frac{1}{2\eta T}`.
* `book/research/Lion.json#/assumptions[name=Theorem1_InitialInfinityBound]`,
  `\|x_1\|_{\infty} \le \eta`. -/
structure FiniteHorizonAssumptions {d : ℕ} [Nonempty (Fin d)] (s : Setup d) (T : ℕ) :
    Prop where
  smoothness : s.Smoothness
  oracle_unbiased : s.OracleUnbiased
  oracle_bounded_noise : s.OracleBoundedNoise
  initial_gap : s.InitialGap
  momentum_order : s.beta2 ^ 2 ≤ s.beta1 ∧ s.beta1 ≤ Real.sqrt s.beta2
  weight_decay_bound : paperDisplayedLeQuotient s.lambda 1 (2 * s.eta * (T : ℝ))
  initial_infinity_bound : linfNorm s.x1 ≤ s.eta

/-- The rate scale `T ↦ T^{-1/2}` used for `β₂` in Theorem 1. -/
def beta2AsymptoticScale : ℕ → ℝ :=
  fun T => (Real.sqrt (T : ℝ))⁻¹

/-- The rate scale `T ↦ d^{-1/2} T^{-3/4}` used for `η` in Theorem 1. -/
def etaAsymptoticScale (d : ℕ) : ℕ → ℝ :=
  fun T => (Real.sqrt (d : ℝ) * Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)))⁻¹

/-- The Theorem 1 conclusion scale `T ↦ d^{1/2} T^{-1/4}`. -/
def theoremOneRateScale (d : ℕ) : ℕ → ℝ :=
  fun T => Real.sqrt (d : ℝ) / Real.sqrt (Real.sqrt (T : ℝ))

/-- Source-stated Theorem 1 assumptions for a fixed problem/oracle and horizon-dependent
parameter schedule.  The big-O parameter restrictions are modeled as genuine asymptotic
facts over `T`, not as constants chosen after a fixed horizon.

Book citation: `book/research/Lion.json#/main_theorem/statement_math`, "Under Assumptions
1, 3 and 4, by setting `\beta_2^2 \le \beta_1 \le \sqrt{\beta_2}`,
`\beta_2=O(T^{-1/2})`, `\eta=O(d^{-1/2}T^{-3/4})`,
`\lambda \le \frac{1}{2\eta T}` and `\|x_1\|_{\infty}\le\eta` ...". -/
structure TheoremOneScheduleAssumptions {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (p : ParameterSchedule) : Prop where
  smoothness : s.Smoothness
  oracle_unbiased : s.OracleUnbiased
  oracle_bounded_noise : s.OracleBoundedNoise
  initial_gap : s.InitialGap
  momentum_order :
    ∀ T : ℕ, 1 ≤ T →
      (p.beta2 T) ^ 2 ≤ p.beta1 T ∧ p.beta1 T ≤ Real.sqrt (p.beta2 T)
  beta2_schedule : Asymptotics.IsBigO Filter.atTop p.beta2 beta2AsymptoticScale
  eta_schedule : Asymptotics.IsBigO Filter.atTop p.eta (etaAsymptoticScale d)
  weight_decay_bound :
    ∀ T : ℕ, 1 ≤ T →
      paperDisplayedLeQuotient (p.lambda T) 1 (2 * p.eta T * (T : ℝ))
  initial_infinity_bound : ∀ T : ℕ, 1 ≤ T → linfNorm s.x1 ≤ p.eta T

/-- A schedule-level assumption specializes to the fixed-horizon assumption for the setup
with that horizon's parameters. -/
theorem finiteHorizonAssumptions_of_schedule {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule} {T : ℕ}
    (hT : 1 ≤ T) (h : TheoremOneScheduleAssumptions s p) :
    FiniteHorizonAssumptions (p.setupAt s T) T := by
  refine
    { smoothness := ?_
      oracle_unbiased := ?_
      oracle_bounded_noise := ?_
      initial_gap := ?_
      momentum_order := ?_
      weight_decay_bound := ?_
      initial_infinity_bound := ?_ }
  · simpa [ParameterSchedule.setupAt, Setup.withParameters] using h.smoothness
  · simpa [ParameterSchedule.setupAt, Setup.withParameters] using h.oracle_unbiased
  · simpa [ParameterSchedule.setupAt, Setup.withParameters] using h.oracle_bounded_noise
  · simpa [ParameterSchedule.setupAt, Setup.withParameters] using h.initial_gap
  · simpa [ParameterSchedule.setupAt, Setup.withParameters] using h.momentum_order T hT
  · simpa [ParameterSchedule.setupAt, Setup.withParameters] using h.weight_decay_bound T hT
  · simpa [ParameterSchedule.setupAt, Setup.withParameters] using h.initial_infinity_bound T hT

/-- Source-facing statement of Lemma 1 over the generated Algorithm 1 iterates.

Book citation: `book/research/Lion.json#/key_lemmas[name=Lemma_1_IterateAndStepBounds]`,
`\|x_t\|_\infty \le \eta t`, `\|x_t\|^2 \le 2\eta^2t^2d`, and
`\|x_{t+1}-x_t\|^2 \le4\eta^2d`. -/
def lemmaOneIterateAndStepBoundsStatement {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (T : ℕ) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ ω : Run s,
    linfNorm (x s t ω) ≤ s.eta * (t : ℝ) ∧
      ‖x s t ω‖ ^ 2 ≤ 2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ) ∧
        ‖x s (t + 1) ω - x s t ω‖ ^ 2 ≤ 4 * s.eta ^ 2 * (d : ℝ)

/-- Corrected non-original Lemma 1 assumption boundary.

Appendix A proves the printed Lemma 1 bounds using `(1 - ηλ)` as a nonnegative contraction.
The PDF states the initial infinity bound and the displayed weight-decay quotient inequality,
but does not separately state the contraction domain as a primitive Lemma 1 hypothesis. -/
def lemmaOne_correctedDomainAssumptions {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (T : ℕ) : Prop :=
  FiniteHorizonAssumptions s T ∧ EtaLambdaHorizonDomainAt s.eta s.lambda T

/-- Extract the printed finite-horizon Lemma 1 assumptions from the corrected boundary. -/
theorem lemmaOne_correctedDomainAssumptions_printed {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} (h : lemmaOne_correctedDomainAssumptions s T) :
    FiniteHorizonAssumptions s T :=
  h.1

/-- Extract the corrected eta-lambda horizon domain from the Lemma 1 boundary. -/
theorem lemmaOne_correctedDomainAssumptions_etaLambda {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} (h : lemmaOne_correctedDomainAssumptions s T) :
    EtaLambdaHorizonDomainAt s.eta s.lambda T :=
  h.2

private theorem abs_coord_le_linfNorm {d : ℕ} [Nonempty (Fin d)] (z : Point d)
    (i : Fin d) :
    |z i| ≤ linfNorm z := by
  simpa [linfNorm] using
    (Finset.le_sup' (s := Finset.univ) (f := fun j : Fin d => |z j|)
      (Finset.mem_univ i))

private theorem abs_real_sign_le_one (a : ℝ) :
    |Real.sign a| ≤ 1 := by
  rcases Real.sign_apply_eq a with hsign | hsign | hsign
  · rw [hsign]
    norm_num
  · rw [hsign]
    norm_num
  · rw [hsign]
    norm_num

private theorem coordinateSign_linfNorm_le_one {d : ℕ} [Nonempty (Fin d)]
    (z : Point d) :
    linfNorm (coordinateSign z) ≤ 1 := by
  rw [linfNorm, Finset.sup'_le_iff]
  intro i _hi
  simpa [coordinateSign] using abs_real_sign_le_one (z i)

private theorem linfNorm_nonneg {d : ℕ} [Nonempty (Fin d)] (z : Point d) :
    0 ≤ linfNorm z := by
  obtain ⟨i⟩ := ‹Nonempty (Fin d)›
  exact (abs_nonneg (z i)).trans (abs_coord_le_linfNorm z i)

private theorem norm_sq_le_card_mul_linfNorm_sq {d : ℕ} [Nonempty (Fin d)]
    (z : Point d) :
    ‖z‖ ^ 2 ≤ (d : ℝ) * linfNorm z ^ 2 := by
  calc
    ‖z‖ ^ 2 = ∑ i : Fin d, (z i) ^ 2 := EuclideanSpace.real_norm_sq_eq z
    _ ≤ ∑ _i : Fin d, linfNorm z ^ 2 := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hcoord : |z i| ≤ linfNorm z := abs_coord_le_linfNorm z i
      have hlinf_nonneg : 0 ≤ linfNorm z := linfNorm_nonneg z
      have hsquare : |z i| ^ 2 ≤ linfNorm z ^ 2 :=
        (sq_le_sq₀ (abs_nonneg (z i)) hlinf_nonneg).2 hcoord
      simpa [sq_abs] using hsquare
    _ = (d : ℝ) * linfNorm z ^ 2 := by
      simp

private theorem coordinateSign_norm_sq_le_card {d : ℕ} [Nonempty (Fin d)]
    (z : Point d) :
    ‖coordinateSign z‖ ^ 2 ≤ (d : ℝ) := by
  have hnorm := norm_sq_le_card_mul_linfNorm_sq (coordinateSign z)
  have hlinf_nonneg : 0 ≤ linfNorm (coordinateSign z) :=
    linfNorm_nonneg (coordinateSign z)
  have hlinf_one : linfNorm (coordinateSign z) ≤ 1 :=
    coordinateSign_linfNorm_le_one z
  have hsq : linfNorm (coordinateSign z) ^ 2 ≤ 1 ^ 2 :=
    (sq_le_sq₀ hlinf_nonneg zero_le_one).2 hlinf_one
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  have hmul :
      (d : ℝ) * linfNorm (coordinateSign z) ^ 2 ≤ (d : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (by simpa using hsq) hd_nonneg
  exact hnorm.trans (by simpa using hmul)

private theorem real_add_sq_le_one_plus_mul_add_one_plus_inv
    {a b q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 < q) :
    (a + b) ^ 2 ≤ (1 + q) * a ^ 2 + (1 + q⁻¹) * b ^ 2 := by
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have hsq : 0 ≤ (q * a - b) ^ 2 := sq_nonneg _
  have hcross : 2 * a * b ≤ q * a ^ 2 + q⁻¹ * b ^ 2 := by
    have hnonneg :
        0 ≤ q * a ^ 2 + q⁻¹ * b ^ 2 - 2 * a * b := by
      have hmul_nonneg :
          0 ≤ q * (q * a ^ 2 + q⁻¹ * b ^ 2 - 2 * a * b) := by
        field_simp [hq_ne]
        nlinarith [hsq]
      exact (mul_nonneg_iff_of_pos_left hq).mp hmul_nonneg
    linarith
  nlinarith

private theorem norm_add_sq_le_one_plus_mul_add_one_plus_inv
    {E : Type*} [SeminormedAddCommGroup E] {a b : E} {q : ℝ} (hq : 0 < q) :
    ‖a + b‖ ^ 2 ≤ (1 + q) * ‖a‖ ^ 2 + (1 + q⁻¹) * ‖b‖ ^ 2 := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq_tri : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
  exact hsq_tri.trans
    (real_add_sq_le_one_plus_mul_add_one_plus_inv (norm_nonneg _) (norm_nonneg _) hq)

private theorem one_sub_sq_mul_one_add_le_one_sub
    {beta : ℝ} (hbeta_nonneg : 0 ≤ beta) (hbeta_le_one : beta ≤ 1) :
    (1 - beta) ^ 2 * (1 + beta) ≤ 1 - beta := by
  have hone_nonneg : 0 ≤ 1 - beta := sub_nonneg.mpr hbeta_le_one
  have hsquare_le : 1 - beta ^ 2 ≤ 1 := by nlinarith [sq_nonneg beta]
  have hmul := mul_le_mul_of_nonneg_left hsquare_le hone_nonneg
  nlinarith

private theorem one_sub_sq_mul_one_add_inv_le_two_inv
    {beta : ℝ} (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1) :
    (1 - beta) ^ 2 * (1 + beta⁻¹) ≤ 2 * beta⁻¹ := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hone_nonneg : 0 ≤ 1 - beta := sub_nonneg.mpr hbeta_le_one
  have hleft_nonneg : 0 ≤ (1 - beta) ^ 2 * (1 + beta⁻¹) := by positivity
  have htarget :
      beta * ((1 - beta) ^ 2 * (1 + beta⁻¹)) ≤ beta * (2 * beta⁻¹) := by
    field_simp [hbeta_ne]
    nlinarith [sq_nonneg beta, sq_nonneg (1 - beta), hone_nonneg]
  exact le_of_mul_le_mul_left htarget hbeta_pos

private theorem one_sub_smul_norm_add_sq_le_error_add_drift_budget
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {beta B : ℝ} (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1) (hB : 0 ≤ B)
    (err drift : E) (hdrift : ‖drift‖ ^ 2 ≤ B) :
    ‖(1 - beta) • (err + drift)‖ ^ 2 ≤
      (1 - beta) * ‖err‖ ^ 2 + 2 * beta⁻¹ * B := by
  have hbeta_nonneg : 0 ≤ beta := le_of_lt hbeta_pos
  have hone_nonneg : 0 ≤ 1 - beta := sub_nonneg.mpr hbeta_le_one
  have hsplit :
      ‖err + drift‖ ^ 2 ≤
        (1 + beta) * ‖err‖ ^ 2 + (1 + beta⁻¹) * ‖drift‖ ^ 2 :=
    norm_add_sq_le_one_plus_mul_add_one_plus_inv (a := err) (b := drift) hbeta_pos
  have hscaled :
      (1 - beta) ^ 2 * ‖err + drift‖ ^ 2 ≤
        (1 - beta) ^ 2 *
          ((1 + beta) * ‖err‖ ^ 2 + (1 + beta⁻¹) * ‖drift‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hsplit (sq_nonneg (1 - beta))
  have hcoeff_err :
      (1 - beta) ^ 2 * (1 + beta) ≤ 1 - beta :=
    one_sub_sq_mul_one_add_le_one_sub hbeta_nonneg hbeta_le_one
  have hcoeff_drift :
      (1 - beta) ^ 2 * (1 + beta⁻¹) ≤ 2 * beta⁻¹ :=
    one_sub_sq_mul_one_add_inv_le_two_inv hbeta_pos hbeta_le_one
  have herr_term :
      (1 - beta) ^ 2 * ((1 + beta) * ‖err‖ ^ 2) ≤
        (1 - beta) * ‖err‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hcoeff_err (sq_nonneg ‖err‖)
    nlinarith
  have hdrift_coeff_nonneg : 0 ≤ 2 * beta⁻¹ := by positivity
  have hdrift_term :
      (1 - beta) ^ 2 * ((1 + beta⁻¹) * ‖drift‖ ^ 2) ≤
        2 * beta⁻¹ * B := by
    have h1 := mul_le_mul_of_nonneg_right hcoeff_drift (sq_nonneg ‖drift‖)
    have h2 := mul_le_mul_of_nonneg_left hdrift hdrift_coeff_nonneg
    nlinarith
  calc
    ‖(1 - beta) • (err + drift)‖ ^ 2 =
        (1 - beta) ^ 2 * ‖err + drift‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hone_nonneg]
      ring
    _ ≤ (1 - beta) ^ 2 *
        ((1 + beta) * ‖err‖ ^ 2 + (1 + beta⁻¹) * ‖drift‖ ^ 2) := hscaled
    _ = (1 - beta) ^ 2 * ((1 + beta) * ‖err‖ ^ 2) +
        (1 - beta) ^ 2 * ((1 + beta⁻¹) * ‖drift‖ ^ 2) := by ring
    _ ≤ (1 - beta) * ‖err‖ ^ 2 + 2 * beta⁻¹ * B :=
      add_le_add herr_term hdrift_term

private theorem sum_range_succ_le_inv_initial_add_inv_const_of_contraction
    {A : ℕ → ℝ} {N : ℕ} {beta C : ℝ}
    (hbeta_pos : 0 < beta) (hbeta_le_one : beta ≤ 1) (hC : 0 ≤ C)
    (hA_nonneg : ∀ k, k ≤ N → 0 ≤ A k)
    (hstep : ∀ k, k < N → A (k + 1) ≤ (1 - beta) * A k + C) :
    (Finset.range (N + 1)).sum A ≤
      beta⁻¹ * A 0 + ((N + 1 : ℕ) : ℝ) * beta⁻¹ * C := by
  classical
  by_cases hbeta_lt_one : beta < 1
  · let r : ℝ := 1 - beta
    have hr_pos : 0 < r := by
      dsimp [r]
      linarith
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
    have hcoef : 1 + beta / r = 1 / r := by
      field_simp [hr_ne]
      ring
    have hstep_tail :
        ∀ k, k < N →
          (fun _ : ℕ => (0 : ℝ)) (k + 1) + (1 + beta / r) * A (k + 1) ≤
            C / r + A k := by
      intro k hk
      have hs := hstep k hk
      have hscaled :
          (1 / r) * A (k + 1) ≤ (1 / r) * ((1 - beta) * A k + C) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      calc
        (fun _ : ℕ => (0 : ℝ)) (k + 1) + (1 + beta / r) * A (k + 1)
            = (1 / r) * A (k + 1) := by
          simp [hcoef]
        _ ≤ (1 / r) * ((1 - beta) * A k + C) := hscaled
        _ = C / r + A k := by
          dsimp [r] at hr_ne
          field_simp [hr_ne]
          ring
    have htel :=
      SOptLib.sum_range_succ_add_weighted_tail_le_mul_add_initial_of_step
        (R := ℝ) N (fun _ : ℕ => (0 : ℝ)) A (C / r) (beta / r) hstep_tail
    have htail_drop :
        (beta / r) * (Finset.range N).sum (fun k => A (k + 1)) ≤
          (N : ℝ) * (C / r) + A 0 := by
      have hAN_nonneg : 0 ≤ A N := hA_nonneg N le_rfl
      have htel' :
          A N + (beta / r) * (Finset.range N).sum (fun k => A (k + 1)) ≤
            (N : ℝ) * (C / r) + A 0 := by
        simpa using htel
      linarith
    have htail_bound :
        (Finset.range N).sum (fun k => A (k + 1)) ≤
          (N : ℝ) * beta⁻¹ * C + r * beta⁻¹ * A 0 := by
      have hscale_nonneg : 0 ≤ r / beta := by positivity
      have hmul := mul_le_mul_of_nonneg_left htail_drop hscale_nonneg
      convert hmul using 1 <;> field_simp [hbeta_ne, hr_ne] <;> ring
    have hsum_decomp :
        (Finset.range (N + 1)).sum A =
          A 0 + (Finset.range N).sum (fun k => A (k + 1)) := by
      rw [Finset.sum_range_succ']
      ring
    have hcoeff_initial : A 0 + r * beta⁻¹ * A 0 = beta⁻¹ * A 0 := by
      dsimp [r]
      field_simp [hbeta_ne]
      ring
    have hbudget_mono :
        (N : ℝ) * beta⁻¹ * C ≤ ((N + 1 : ℕ) : ℝ) * beta⁻¹ * C := by
      have hcoef_nonneg : 0 ≤ beta⁻¹ * C := mul_nonneg (inv_nonneg.mpr hbeta_pos.le) hC
      calc
        (N : ℝ) * beta⁻¹ * C = (N : ℝ) * (beta⁻¹ * C) := by ring
        _ ≤ ((N + 1 : ℕ) : ℝ) * (beta⁻¹ * C) :=
          mul_le_mul_of_nonneg_right (by norm_num) hcoef_nonneg
        _ = ((N + 1 : ℕ) : ℝ) * beta⁻¹ * C := by ring
    calc
      (Finset.range (N + 1)).sum A =
          A 0 + (Finset.range N).sum (fun k => A (k + 1)) := hsum_decomp
      _ ≤ A 0 + ((N : ℝ) * beta⁻¹ * C + r * beta⁻¹ * A 0) :=
        by
          have h := add_le_add_left htail_bound (A 0)
          linarith
      _ = (A 0 + r * beta⁻¹ * A 0) + (N : ℝ) * beta⁻¹ * C := by ring
      _ = beta⁻¹ * A 0 + (N : ℝ) * beta⁻¹ * C := by rw [hcoeff_initial]
      _ ≤ beta⁻¹ * A 0 + ((N + 1 : ℕ) : ℝ) * beta⁻¹ * C :=
        by
          have h := add_le_add_left hbudget_mono (beta⁻¹ * A 0)
          linarith
  · have hbeta_one : beta = 1 := le_antisymm hbeta_le_one (le_of_not_gt hbeta_lt_one)
    subst beta
    simp only [inv_one, one_mul]
    induction N with
    | zero =>
        simp
        exact hC
    | succ N ih =>
        have hA_nonneg_prev : ∀ k, k ≤ N → 0 ≤ A k := by
          intro k hk
          exact hA_nonneg k (Nat.le_trans hk (Nat.le_succ N))
        have hstep_prev : ∀ k, k < N → A (k + 1) ≤ (1 - 1 : ℝ) * A k + C := by
          intro k hk
          exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self N))
        have hih := ih hA_nonneg_prev hstep_prev
        have hih' : (Finset.range (N + 1)).sum A ≤ A 0 + ((N + 1 : ℕ) : ℝ) * C := by
          simpa [one_mul] using hih
        have htop : A (N + 1) ≤ C := by
          have hs := hstep N (Nat.lt_succ_self N)
          simpa using hs
        calc
          (Finset.range (N + 1 + 1)).sum A =
              (Finset.range (N + 1)).sum A + A (N + 1) := by
            rw [Finset.sum_range_succ]
          _ ≤ (A 0 + ((N + 1 : ℕ) : ℝ) * C) + C := add_le_add hih' htop
          _ = A 0 + ((N + 1 + 1 : ℕ) : ℝ) * 1 * C := by
            norm_num [Nat.cast_add, Nat.cast_one]
            ring

private theorem sum_range_succ_le_head_add_tail_budget_of_lagged_recurrence
    {V M : ℕ → ℝ} {N : ℕ} {alpha B C : ℝ}
    (hstep : ∀ k, k < N → V (k + 1) ≤ B + alpha * M k + C) :
    (Finset.range (N + 1)).sum V ≤
      V 0 + (N : ℝ) * (B + C) + alpha * (Finset.range N).sum M := by
  classical
  have htail :
      (Finset.range N).sum (fun k => V (k + 1)) ≤
        (Finset.range N).sum (fun k => B + alpha * M k + C) := by
    exact Finset.sum_le_sum (by
      intro k hk
      exact hstep k (Finset.mem_range.mp hk))
  have htail_eval :
      (Finset.range N).sum (fun k => B + alpha * M k + C) =
        (N : ℝ) * (B + C) + alpha * (Finset.range N).sum M := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    (Finset.range (N + 1)).sum V =
        V 0 + (Finset.range N).sum (fun k => V (k + 1)) := by
      rw [Finset.sum_range_succ']
      ring
    _ ≤ V 0 + (Finset.range N).sum (fun k => B + alpha * M k + C) :=
      by
        have h := add_le_add_left htail (V 0)
        linarith
    _ = V 0 + (N : ℝ) * (B + C) + alpha * (Finset.range N).sum M := by
      rw [htail_eval]
      ring

private theorem integral_norm_sq_smul_add_le_of_inner_zero
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} {a U : ℝ} {noise direction : Ω → E}
    (hnoise_meas : AEStronglyMeasurable noise μ)
    (hdirection_meas : AEStronglyMeasurable direction μ)
    (hnoise_sq : Integrable (fun ω => ‖noise ω‖ ^ 2) μ)
    (hdirection_sq : Integrable (fun ω => ‖direction ω‖ ^ 2) μ)
    (hnoise_bound : ∫ ω, ‖noise ω‖ ^ 2 ∂μ ≤ U)
    (hcross_zero : ∫ ω, ⟪noise ω, direction ω⟫_ℝ ∂μ = 0) :
    ∫ ω, ‖a • noise ω + direction ω‖ ^ 2 ∂μ ≤
      a ^ 2 * U + ∫ ω, ‖direction ω‖ ^ 2 ∂μ := by
  classical
  have hinner_int : Integrable (fun ω => ⟪noise ω, direction ω⟫_ℝ) μ :=
    integrable_inner_of_integrable_sq_norm hnoise_meas hdirection_meas hnoise_sq hdirection_sq
  have hexpand :
      (fun ω => ‖a • noise ω + direction ω‖ ^ 2) =ᵐ[μ]
        fun ω =>
          a ^ 2 * ‖noise ω‖ ^ 2 + (2 * a) * ⟪noise ω, direction ω⟫_ℝ +
            ‖direction ω‖ ^ 2 := by
    filter_upwards with ω
    rw [norm_add_sq_real]
    simp [inner_smul_left, norm_smul, Real.norm_eq_abs, sq_abs]
    rw [mul_pow, sq_abs]
    ring
  calc
    ∫ ω, ‖a • noise ω + direction ω‖ ^ 2 ∂μ =
        ∫ ω,
          a ^ 2 * ‖noise ω‖ ^ 2 + (2 * a) * ⟪noise ω, direction ω⟫_ℝ +
            ‖direction ω‖ ^ 2 ∂μ :=
      integral_congr_ae hexpand
    _ = a ^ 2 * (∫ ω, ‖noise ω‖ ^ 2 ∂μ) +
        (2 * a) * (∫ ω, ⟪noise ω, direction ω⟫_ℝ ∂μ) +
          ∫ ω, ‖direction ω‖ ^ 2 ∂μ := by
      calc
        ∫ ω,
          a ^ 2 * ‖noise ω‖ ^ 2 + (2 * a) * ⟪noise ω, direction ω⟫_ℝ +
            ‖direction ω‖ ^ 2 ∂μ =
            ∫ ω,
              (a ^ 2 * ‖noise ω‖ ^ 2 +
                  (2 * a) * ⟪noise ω, direction ω⟫_ℝ) +
                ‖direction ω‖ ^ 2 ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with ω
              ring
        _ = a ^ 2 * (∫ ω, ‖noise ω‖ ^ 2 ∂μ) +
            (2 * a) * (∫ ω, ⟪noise ω, direction ω⟫_ℝ ∂μ) +
              ∫ ω, ‖direction ω‖ ^ 2 ∂μ := by
          have hlin_outer :
              ∫ ω,
                (a ^ 2 * ‖noise ω‖ ^ 2 +
                    (2 * a) * ⟪noise ω, direction ω⟫_ℝ) +
                  ‖direction ω‖ ^ 2 ∂μ =
                ∫ ω,
                  a ^ 2 * ‖noise ω‖ ^ 2 +
                    (2 * a) * ⟪noise ω, direction ω⟫_ℝ ∂μ +
                  ∫ ω, ‖direction ω‖ ^ 2 ∂μ := by
            simpa only [Pi.add_apply] using
              integral_add
                ((hnoise_sq.const_mul (a ^ 2)).add (hinner_int.const_mul (2 * a)))
                hdirection_sq
          have hlin_inner :
              ∫ ω,
                a ^ 2 * ‖noise ω‖ ^ 2 +
                  (2 * a) * ⟪noise ω, direction ω⟫_ℝ ∂μ =
                a ^ 2 * (∫ ω, ‖noise ω‖ ^ 2 ∂μ) +
                  (2 * a) * (∫ ω, ⟪noise ω, direction ω⟫_ℝ ∂μ) := by
            have hraw :=
              integral_add (hnoise_sq.const_mul (a ^ 2))
                (hinner_int.const_mul (2 * a))
            simpa only [Pi.add_apply, integral_const_mul] using hraw
          rw [hlin_outer, hlin_inner]
    _ = a ^ 2 * (∫ ω, ‖noise ω‖ ^ 2 ∂μ) +
          ∫ ω, ‖direction ω‖ ^ 2 ∂μ := by
      rw [hcross_zero]
      ring
    _ ≤ a ^ 2 * U + ∫ ω, ‖direction ω‖ ^ 2 ∂μ :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (mul_le_mul_of_nonneg_left hnoise_bound (sq_nonneg a))
            (∫ ω, ‖direction ω‖ ^ 2 ∂μ)

private theorem real_sign_measurable : Measurable Real.sign := by
  classical
  have hneg : MeasurableSet {x : ℝ | x < 0} :=
    measurableSet_lt measurable_id measurable_const
  have hzero : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
  have hpiece :
      Measurable (fun x : ℝ => if x < 0 then (-1 : ℝ) else if x = 0 then 0 else 1) :=
    Measurable.ite hneg measurable_const
      (Measurable.ite hzero measurable_const measurable_const)
  convert hpiece using 1
  ext x
  by_cases hxneg : x < 0
  · simp [hxneg, Real.sign_of_neg hxneg]
  · by_cases hxzero : x = 0
    · simp [hxneg, hxzero]
    · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hxneg) (Ne.symm hxzero)
      simp [hxneg, hxzero, Real.sign_of_pos hxpos]

private theorem coordinateSign_measurable {d : ℕ} :
    Measurable (coordinateSign : Point d → Point d) := by
  have hraw : Measurable (fun z : Point d => fun i : Fin d => Real.sign (z i)) := by
    refine measurable_pi_lambda (fun z : Point d => fun i : Fin d => Real.sign (z i)) ?_
    intro i
    exact real_sign_measurable.comp
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).continuous.measurable)
  simpa [coordinateSign] using (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp hraw

private theorem coordinateSign_range_finite {d : ℕ} :
    (Set.range (fun z : Point d => coordinateSign z)).Finite := by
  classical
  let signCode : Point d → Fin d → Fin 3 := fun z i =>
    if Real.sign (z i) = (-1 : ℝ) then 0 else
      if Real.sign (z i) = 0 then 1 else 2
  have hcode_fin : (Set.range signCode).Finite :=
    Set.finite_univ.subset (by intro y _hy; exact Set.mem_univ y)
  refine Set.Finite.range_of_finite_range_fiber_const (Y := signCode) hcode_fin ?_
  intro z z' hcode
  ext i
  have hi := congrFun hcode i
  have hsign_eq : Real.sign (z i) = Real.sign (z' i) := by
    rcases Real.sign_apply_eq (z i) with hzi | hzi | hzi <;>
      rcases Real.sign_apply_eq (z' i) with hz'i | hz'i | hz'i <;>
        rw [hzi, hz'i]
    all_goals
      first
      | rfl
      | exfalso
        have hfalse : False := by
          have hval := congrArg Fin.val hi
          simp only [signCode, hzi, hz'i, if_true, if_false] at hval
          norm_num at hval
        exact hfalse
  simpa [coordinateSign] using hsign_eq

private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simp [inner, Inner.inner, RCLike.toInnerProductSpaceReal, Inner.rclikeToReal,
    RCLike.innerProductSpace, mul_comm]

private theorem neg_mul_sign_le_two_abs_sub_sub_abs (a b : ℝ) :
    -(a * Real.sign b) ≤ 2 * |a - b| - |a| := by
  rcases lt_trichotomy b 0 with hbneg | hbzero | hbpos
  · rw [Real.sign_of_neg hbneg]
    by_cases haneg : a < 0
    · rw [abs_of_neg haneg]
      nlinarith [abs_nonneg (a - b)]
    · have hanonneg : 0 ≤ a := le_of_not_gt haneg
      have hsub_nonneg : 0 ≤ a - b := by linarith
      rw [abs_of_nonneg hanonneg, abs_of_nonneg hsub_nonneg]
      linarith
  · subst b
    have hnonneg : 0 ≤ 2 * |a - 0| - |a| := by
      rw [sub_zero]
      nlinarith [abs_nonneg a]
    simpa [Real.sign_zero] using hnonneg
  · rw [Real.sign_of_pos hbpos]
    by_cases hanonneg : 0 ≤ a
    · rw [abs_of_nonneg hanonneg]
      nlinarith [abs_nonneg (a - b)]
    · have haneg : a < 0 := lt_of_not_ge hanonneg
      have hsub_nonpos : a - b ≤ 0 := by linarith
      rw [abs_of_neg haneg, abs_of_nonpos hsub_nonpos]
      linarith

private theorem neg_inner_coordinateSign_le_two_l1_sub_l1 {d : ℕ}
    (g u : Point d) :
    -⟪g, coordinateSign u⟫_ℝ ≤ 2 * l1Norm (g - u) - l1Norm g := by
  classical
  calc
    -⟪g, coordinateSign u⟫_ℝ =
        ∑ i : Fin d, -(g i * Real.sign (u i)) := by
      simp [PiLp.inner_apply, coordinateSign, Finset.sum_neg_distrib, real_inner_eq_mul]
    _ ≤ ∑ i : Fin d, (2 * |g i - u i| - |g i|) := by
      exact Finset.sum_le_sum fun i _hi => neg_mul_sign_le_two_abs_sub_sub_abs (g i) (u i)
    _ = 2 * l1Norm (g - u) - l1Norm g := by
      simp [l1Norm, Finset.mul_sum, Finset.sum_sub_distrib]

private theorem l1Norm_le_sqrt_card_mul_norm {d : ℕ} (z : Point d) :
    l1Norm z ≤ Real.sqrt (d : ℝ) * ‖z‖ := by
  have hraw := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i : Fin d => |z i|)
  have hsq : l1Norm z ^ 2 ≤ (d : ℝ) * ‖z‖ ^ 2 := by
    simpa [l1Norm, EuclideanSpace.real_norm_sq_eq, sq_abs] using hraw
  have hle := Real.le_sqrt_of_sq_le hsq
  have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
  rw [Real.sqrt_mul hd_nonneg, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)] at hle
  simpa [pow_two] using hle

private theorem abs_inner_le_l1Norm_mul_linfNorm {d : ℕ} [Nonempty (Fin d)]
    (g z : Point d) :
    |⟪g, z⟫_ℝ| ≤ l1Norm g * linfNorm z := by
  classical
  calc
    |⟪g, z⟫_ℝ| = |∑ i : Fin d, g i * z i| := by
      simp [PiLp.inner_apply, real_inner_eq_mul]
    _ ≤ ∑ i : Fin d, |g i * z i| := by
      exact Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin d => g i * z i)
    _ = ∑ i : Fin d, |g i| * |z i| := by
      simp [abs_mul]
    _ ≤ ∑ i : Fin d, |g i| * linfNorm z := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      exact mul_le_mul_of_nonneg_left (abs_coord_le_linfNorm z i) (abs_nonneg (g i))
    _ = l1Norm g * linfNorm z := by
      simp [l1Norm, Finset.sum_mul]

private theorem l1Norm_nonneg {d : ℕ} (z : Point d) : 0 ≤ l1Norm z := by
  exact Finset.sum_nonneg fun i _hi => abs_nonneg (z i)

private theorem neg_lambda_inner_le_half_l1 {d : ℕ} [Nonempty (Fin d)]
    {lambda : ℝ} (hlambda_nonneg : 0 ≤ lambda) {g z : Point d}
    (hbudget : lambda * linfNorm z ≤ 1 / 2) :
    -(lambda * ⟪g, z⟫_ℝ) ≤ (1 / 2) * l1Norm g := by
  have hneg_inner : -⟪g, z⟫_ℝ ≤ |⟪g, z⟫_ℝ| := neg_le_abs _
  have hmul_abs :
      lambda * (-⟪g, z⟫_ℝ) ≤ lambda * |⟪g, z⟫_ℝ| :=
    mul_le_mul_of_nonneg_left hneg_inner hlambda_nonneg
  have hinner_abs := abs_inner_le_l1Norm_mul_linfNorm g z
  have hlambda_inner :
      lambda * |⟪g, z⟫_ℝ| ≤ lambda * (l1Norm g * linfNorm z) :=
    mul_le_mul_of_nonneg_left hinner_abs hlambda_nonneg
  have hl1_nonneg : 0 ≤ l1Norm g := l1Norm_nonneg g
  have hbudget_l1 :
      lambda * (l1Norm g * linfNorm z) ≤ (1 / 2) * l1Norm g := by
    calc
      lambda * (l1Norm g * linfNorm z) =
          (lambda * linfNorm z) * l1Norm g := by ring
      _ ≤ (1 / 2) * l1Norm g :=
        mul_le_mul_of_nonneg_right hbudget hl1_nonneg
  have hchain : lambda * (-⟪g, z⟫_ℝ) ≤ (1 / 2) * l1Norm g :=
    hmul_abs.trans (hlambda_inner.trans hbudget_l1)
  simpa [neg_mul] using hchain

private theorem lion_direction_inner_le_error_minus_half_l1 {d : ℕ} [Nonempty (Fin d)]
    {eta lambda : ℝ} (heta_nonneg : 0 ≤ eta) (hlambda_nonneg : 0 ≤ lambda)
    {g u z : Point d} (hbudget : lambda * linfNorm z ≤ 1 / 2) :
    ⟪g, -(eta • (coordinateSign u + lambda • z))⟫_ℝ ≤
      2 * eta * Real.sqrt (d : ℝ) * ‖g - u‖ - (eta / 2) * l1Norm g := by
  have hsign_l1 :
      -⟪g, coordinateSign u⟫_ℝ ≤
        2 * Real.sqrt (d : ℝ) * ‖g - u‖ - l1Norm g := by
    have hsign := neg_inner_coordinateSign_le_two_l1_sub_l1 g u
    have hl1 := l1Norm_le_sqrt_card_mul_norm (g - u)
    have hscaled :
        2 * l1Norm (g - u) ≤
          2 * (Real.sqrt (d : ℝ) * ‖g - u‖) :=
      mul_le_mul_of_nonneg_left hl1 (by norm_num)
    nlinarith
  have hdecay :
      -(lambda * ⟪g, z⟫_ℝ) ≤ (1 / 2) * l1Norm g :=
    neg_lambda_inner_le_half_l1 hlambda_nonneg hbudget
  have hsum :
      -⟪g, coordinateSign u⟫_ℝ - lambda * ⟪g, z⟫_ℝ ≤
        2 * Real.sqrt (d : ℝ) * ‖g - u‖ - (1 / 2) * l1Norm g := by
    nlinarith
  have hmul :
      eta * (-⟪g, coordinateSign u⟫_ℝ - lambda * ⟪g, z⟫_ℝ) ≤
        eta * (2 * Real.sqrt (d : ℝ) * ‖g - u‖ - (1 / 2) * l1Norm g) :=
    mul_le_mul_of_nonneg_left hsum heta_nonneg
  have hinner_eq :
      ⟪g, -(eta • (coordinateSign u + lambda • z))⟫_ℝ =
        eta * (-⟪g, coordinateSign u⟫_ℝ - lambda * ⟪g, z⟫_ℝ) := by
    simp [inner_add_right, inner_smul_right]
    ring
  calc
    ⟪g, -(eta • (coordinateSign u + lambda • z))⟫_ℝ =
        eta * (-⟪g, coordinateSign u⟫_ℝ - lambda * ⟪g, z⟫_ℝ) := hinner_eq
    _ ≤ eta * (2 * Real.sqrt (d : ℝ) * ‖g - u‖ - (1 / 2) * l1Norm g) := hmul
    _ = 2 * eta * Real.sqrt (d : ℝ) * ‖g - u‖ - (eta / 2) * l1Norm g := by
      ring

private theorem smoothness_quadratic_upper_bound {d : ℕ} {s : Setup d}
    (hsmooth : s.Smoothness) (x y : Point d) :
    s.f y ≤ s.f x + ⟪s.trueGradient x, y - x⟫_ℝ +
      (s.L / 2) * ‖y - x‖ ^ 2 := by
  classical
  exact smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
    (X := Set.univ) s.f s.trueGradient s.L convex_univ
    (by intro z _hz; exact Setup.smoothness_hasGradientAt hsmooth z)
    (by
      intro z _hz w _hw
      exact Setup.smoothness_lipschitz_trueGradient hsmooth z w)
    (x := x) (y := y) (Set.mem_univ x) (Set.mem_univ y)

private theorem smoothness_L_nonneg {d : ℕ} [Nonempty (Fin d)] {s : Setup d}
    (hsmooth : s.Smoothness) :
    0 ≤ s.L := by
  classical
  let e : Point d := WithLp.toLp 2 fun _ : Fin d => (1 : ℝ)
  have he_ne : e ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin d)›
    intro he
    have hcoord := congrArg (fun z : Point d => z i) he
    simp [e] at hcoord
  have hdist_pos : 0 < ‖e - 0‖ := by
    simpa using (norm_pos_iff.mpr (sub_ne_zero.mpr he_ne))
  have hlip := Setup.smoothness_lipschitz_trueGradient hsmooth e 0
  have hprod_nonneg : 0 ≤ s.L * ‖e - 0‖ :=
    (norm_nonneg (s.trueGradient e - s.trueGradient 0)).trans hlip
  exact nonneg_of_mul_nonneg_right (by simpa [mul_comm] using hprod_nonneg) hdist_pos

private theorem lambda_nonneg_of_eta_pos_contraction_upper {eta lambda : ℝ}
    (heta : 0 < eta) (hc1 : 1 - eta * lambda ≤ 1) :
    0 ≤ lambda := by
  have hmul : 0 ≤ eta * lambda := by
    nlinarith
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hmul) heta

private theorem lambda_mul_linfNorm_le_half_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hEta : EtaLambdaHorizonDomainAt s.eta s.lambda T)
    (htT : t ≤ T) {z : Point d}
    (hz : linfNorm z ≤ s.eta * (t : ℝ)) :
    s.lambda * linfNorm z ≤ 1 / 2 := by
  obtain ⟨heta_pos, hcontr, _hquot⟩ := hEta
  have hlambda_nonneg : 0 ≤ s.lambda :=
    lambda_nonneg_of_eta_pos_contraction_upper heta_pos hcontr.2
  have hlam : s.lambda ≤ 1 / (2 * s.eta * (T : ℝ)) := by
    simpa [paperDisplayedLeQuotient] using h.weight_decay_bound
  have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
  have heta_t_nonneg : 0 ≤ s.eta * (t : ℝ) :=
    mul_nonneg (le_of_lt heta_pos) ht_nonneg
  have hlinf_step :
      s.lambda * linfNorm z ≤ s.lambda * (s.eta * (t : ℝ)) :=
    mul_le_mul_of_nonneg_left hz hlambda_nonneg
  have hbudget_step :
      s.lambda * (s.eta * (t : ℝ)) ≤
        (1 / (2 * s.eta * (T : ℝ))) * (s.eta * (t : ℝ)) :=
    mul_le_mul_of_nonneg_right hlam heta_t_nonneg
  have hT_pos_real : 0 < (T : ℝ) := by exact_mod_cast hT
  have htT_real : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
  have hbudget_half :
      (1 / (2 * s.eta * (T : ℝ))) * (s.eta * (t : ℝ)) ≤ 1 / 2 := by
    field_simp [ne_of_gt heta_pos, ne_of_gt hT_pos_real]
    nlinarith [htT_real, le_of_lt heta_pos, hT_pos_real]
  exact hlinf_step.trans (hbudget_step.trans hbudget_half)

private theorem lambda_sq_eta_sq_T_sq_le_quarter {eta lambda : ℝ} {T : ℕ}
    (hT : 1 ≤ T) (heta : 0 < eta)
    (hc1 : 1 - eta * lambda ≤ 1)
    (hlam : paperDisplayedLeQuotient lambda 1 (2 * eta * (T : ℝ))) :
    lambda ^ 2 * eta ^ 2 * (T : ℝ) ^ 2 ≤ 1 / 4 := by
  have hlambda_nonneg : 0 ≤ lambda :=
    lambda_nonneg_of_eta_pos_contraction_upper heta hc1
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hden_pos : 0 < 2 * eta * (T : ℝ) := by
    positivity
  have hquot : lambda ≤ 1 / (2 * eta * (T : ℝ)) := by
    simpa [paperDisplayedLeQuotient] using hlam
  have hquot_nonneg : 0 ≤ 1 / (2 * eta * (T : ℝ)) := by
    positivity
  have hsquare :
      lambda ^ 2 ≤ (1 / (2 * eta * (T : ℝ))) ^ 2 :=
    (sq_le_sq₀ hlambda_nonneg hquot_nonneg).2 hquot
  have hscale_nonneg : 0 ≤ eta ^ 2 * (T : ℝ) ^ 2 :=
    mul_nonneg (sq_nonneg eta) (sq_nonneg (T : ℝ))
  have hmul :
      lambda ^ 2 * (eta ^ 2 * (T : ℝ) ^ 2) ≤
        (1 / (2 * eta * (T : ℝ))) ^ 2 * (eta ^ 2 * (T : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hsquare hscale_nonneg
  have hright :
      (1 / (2 * eta * (T : ℝ))) ^ 2 * (eta ^ 2 * (T : ℝ) ^ 2) = 1 / 4 := by
    field_simp [hden_pos.ne']
    ring
  calc
    lambda ^ 2 * eta ^ 2 * (T : ℝ) ^ 2 =
        lambda ^ 2 * (eta ^ 2 * (T : ℝ) ^ 2) := by ring
    _ ≤ (1 / (2 * eta * (T : ℝ))) ^ 2 * (eta ^ 2 * (T : ℝ) ^ 2) := hmul
    _ = 1 / 4 := hright

private theorem linfNorm_lion_update_le_contraction_plus_eta {d : ℕ}
    [Nonempty (Fin d)] (s : Setup d) (z u : Point d)
    (heta : 0 ≤ s.eta)
    (hc0 : 0 ≤ 1 - s.eta * s.lambda)
    (_hc1 : 1 - s.eta * s.lambda ≤ 1) :
    linfNorm (z - s.eta • (coordinateSign u + s.lambda • z)) ≤
      (1 - s.eta * s.lambda) * linfNorm z + s.eta := by
  rw [linfNorm, Finset.sup'_le_iff]
  intro i _hi
  have hcoord :
      |(z - s.eta • (coordinateSign u + s.lambda • z)) i| =
        |(1 - s.eta * s.lambda) * z i - s.eta * Real.sign (u i)| := by
    simp [coordinateSign, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
    ring_nf
  rw [hcoord]
  have hz : |z i| ≤ linfNorm z := abs_coord_le_linfNorm z i
  have hsign : |Real.sign (u i)| ≤ 1 := abs_real_sign_le_one (u i)
  calc
    |(1 - s.eta * s.lambda) * z i - s.eta * Real.sign (u i)| ≤
        |(1 - s.eta * s.lambda) * z i| + |s.eta * Real.sign (u i)| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le ((1 - s.eta * s.lambda) * z i) (-(s.eta * Real.sign (u i)))
    _ = (1 - s.eta * s.lambda) * |z i| + s.eta * |Real.sign (u i)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc0, abs_of_nonneg heta]
    _ ≤ (1 - s.eta * s.lambda) * linfNorm z + s.eta * 1 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hz hc0)
        (mul_le_mul_of_nonneg_left hsign heta)
    _ = (1 - s.eta * s.lambda) * linfNorm z + s.eta := by
      ring

private theorem lemma_one_linf_bound_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} (_hT : 1 ≤ T)
    (h : lemmaOne_correctedDomainAssumptions s T) :
    ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ ω : Run s,
      linfNorm (x s t ω) ≤ s.eta * (t : ℝ) := by
  intro t ht _htT ω
  have hFH := lemmaOne_correctedDomainAssumptions_printed h
  have hDom := lemmaOne_correctedDomainAssumptions_etaLambda h
  obtain ⟨heta_pos, hcontr, _hquot⟩ := hDom
  have heta_nonneg : 0 ≤ s.eta := le_of_lt heta_pos
  have hc0 : 0 ≤ 1 - s.eta * s.lambda := hcontr.1
  have hc1 : 1 - s.eta * s.lambda ≤ 1 := hcontr.2
  have htime :
      ∀ k : ℕ, ∀ ω : Run s,
        linfNorm (x s (k + 1) ω) ≤ s.eta * ((k + 1 : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero =>
        intro ω
        simpa [x, stateAt] using hFH.initial_infinity_bound
    | succ k ih =>
        intro ω
        have hxupdate := x_succ_eq_update s (Nat.succ_pos k) ω
        have hrec :
            linfNorm (x s ((k + 1) + 1) ω) ≤
              (1 - s.eta * s.lambda) * linfNorm (x s (k + 1) ω) + s.eta := by
          simpa [hxupdate] using
            (linfNorm_lion_update_le_contraction_plus_eta s (x s (k + 1) ω)
              (v s (k + 1) ω) heta_nonneg hc0 hc1)
        have hih := ih ω
        have hmul :
            (1 - s.eta * s.lambda) * linfNorm (x s (k + 1) ω) ≤
              (1 - s.eta * s.lambda) * (s.eta * ((k + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hih hc0
        have hchain :
            linfNorm (x s ((k + 1) + 1) ω) ≤
              (1 - s.eta * s.lambda) * (s.eta * ((k + 1 : ℕ) : ℝ)) + s.eta :=
          hrec.trans (by simpa [add_comm] using add_le_add_right hmul s.eta)
        have hbudget :
            (1 - s.eta * s.lambda) * (s.eta * ((k + 1 : ℕ) : ℝ)) + s.eta ≤
              s.eta * (((k + 1) + 1 : ℕ) : ℝ) := by
          have hnonneg : 0 ≤ s.eta * ((k + 1 : ℕ) : ℝ) :=
            mul_nonneg heta_nonneg (by positivity)
          have hcontract :
              (1 - s.eta * s.lambda) * (s.eta * ((k + 1 : ℕ) : ℝ)) ≤
                1 * (s.eta * ((k + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right hc1 hnonneg
          calc
            (1 - s.eta * s.lambda) * (s.eta * ((k + 1 : ℕ) : ℝ)) + s.eta ≤
                1 * (s.eta * ((k + 1 : ℕ) : ℝ)) + s.eta :=
              by simpa [add_comm] using add_le_add_right hcontract s.eta
            _ = s.eta * (((k + 1) + 1 : ℕ) : ℝ) := by
              norm_num
              ring
        exact hchain.trans hbudget
  simpa [Nat.sub_add_cancel ht] using htime (t - 1) ω

/-- Corrected-domain Lemma 1 for the canonical generated process.

This is not the unqualified paper lemma: its hypothesis exposes the eta positivity,
eta-horizon quotient, and `(1 - ηλ)` contraction obligations that Appendix A uses without
stating as primitive source assumptions. -/
theorem lemma_one_iterate_and_step_bounds_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} (hT : 1 ≤ T)
    (h : lemmaOne_correctedDomainAssumptions s T) :
    lemmaOneIterateAndStepBoundsStatement s T := by
  intro t ht htT ω
  have hFH := lemmaOne_correctedDomainAssumptions_printed h
  have hDom := lemmaOne_correctedDomainAssumptions_etaLambda h
  obtain ⟨heta_pos, hcontr, _hquot⟩ := hDom
  have heta_nonneg : 0 ≤ s.eta := le_of_lt heta_pos
  have hlinf :=
    lemma_one_linf_bound_correctedDomain (s := s) (T := T) hT h t ht htT ω
  have hl2 :
      ‖x s t ω‖ ^ 2 ≤ 2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ) := by
    have hnorm := norm_sq_le_card_mul_linfNorm_sq (x s t ω)
    have hlinf_nonneg : 0 ≤ linfNorm (x s t ω) :=
      linfNorm_nonneg (x s t ω)
    have ht_nonneg : 0 ≤ s.eta * (t : ℝ) :=
      mul_nonneg heta_nonneg (by positivity)
    have hsq_linf :
        linfNorm (x s t ω) ^ 2 ≤ (s.eta * (t : ℝ)) ^ 2 :=
      (sq_le_sq₀ hlinf_nonneg ht_nonneg).2 hlinf
    have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
    have hmul :
        (d : ℝ) * linfNorm (x s t ω) ^ 2 ≤
          (d : ℝ) * (s.eta * (t : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_linf hd_nonneg
    have hbase :
        (d : ℝ) * (s.eta * (t : ℝ)) ^ 2 ≤
          2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ) := by
      have hprod_nonneg : 0 ≤ s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ) :=
        mul_nonneg (mul_nonneg (sq_nonneg s.eta) (sq_nonneg (t : ℝ))) hd_nonneg
      nlinarith [hprod_nonneg]
    exact hnorm.trans (hmul.trans hbase)
  refine ⟨hlinf, hl2, ?_⟩
  let dir : Point d := coordinateSign (v s t ω) + s.lambda • x s t ω
  have hxupdate := x_succ_eq_update s ht ω
  have hdiff : x s (t + 1) ω - x s t ω = -(s.eta • dir) := by
    rw [hxupdate]
    abel
  have hdiff_sq :
      ‖x s (t + 1) ω - x s t ω‖ ^ 2 = s.eta ^ 2 * ‖dir‖ ^ 2 := by
    rw [hdiff]
    simp [norm_smul, mul_pow, sq_abs, mul_comm, mul_left_comm, mul_assoc]
  have hsign_sq :
      ‖coordinateSign (v s t ω)‖ ^ 2 ≤ (d : ℝ) :=
    coordinateSign_norm_sq_le_card (v s t ω)
  have hlambda_x_sq :
      ‖s.lambda • x s t ω‖ ^ 2 = s.lambda ^ 2 * ‖x s t ω‖ ^ 2 := by
    simp [norm_smul, mul_pow, sq_abs, mul_comm, mul_left_comm, mul_assoc]
  have hlambda_x_le :
      ‖s.lambda • x s t ω‖ ^ 2 ≤
        s.lambda ^ 2 * (2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ)) := by
    rw [hlambda_x_sq]
    exact mul_le_mul_of_nonneg_left hl2 (sq_nonneg s.lambda)
  have hdir_young :
      ‖dir‖ ^ 2 ≤
        2 * ‖coordinateSign (v s t ω)‖ ^ 2 +
          2 * ‖s.lambda • x s t ω‖ ^ 2 := by
    simpa [dir] using
      (SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        (coordinateSign (v s t ω)) (s.lambda • x s t ω))
  have hdir_le :
      ‖dir‖ ^ 2 ≤
        2 * (d : ℝ) +
          2 * (s.lambda ^ 2 * (2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ))) := by
    have hsign_scaled :
        2 * ‖coordinateSign (v s t ω)‖ ^ 2 ≤ 2 * (d : ℝ) :=
      mul_le_mul_of_nonneg_left hsign_sq (by norm_num)
    have hlambda_scaled :
        2 * ‖s.lambda • x s t ω‖ ^ 2 ≤
          2 * (s.lambda ^ 2 * (2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ))) :=
      mul_le_mul_of_nonneg_left hlambda_x_le (by norm_num)
    exact hdir_young.trans (add_le_add hsign_scaled hlambda_scaled)
  have hstep_pre :
      ‖x s (t + 1) ω - x s t ω‖ ^ 2 ≤
        s.eta ^ 2 *
          (2 * (d : ℝ) +
            2 * (s.lambda ^ 2 * (2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ)))) := by
    rw [hdiff_sq]
    exact mul_le_mul_of_nonneg_left hdir_le (sq_nonneg s.eta)
  have hquarter :
      s.lambda ^ 2 * s.eta ^ 2 * (T : ℝ) ^ 2 ≤ 1 / 4 :=
    lambda_sq_eta_sq_T_sq_le_quarter hT heta_pos hcontr.2 hFH.weight_decay_bound
  have htT_real : (t : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast htT
  have ht_sq_le : (t : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity : 0 ≤ (t : ℝ)) (by positivity : 0 ≤ (T : ℝ))).2 htT_real
  have hlambda_t :
      s.lambda ^ 2 * s.eta ^ 2 * (t : ℝ) ^ 2 ≤ 1 / 4 := by
    have hscale_nonneg : 0 ≤ s.lambda ^ 2 * s.eta ^ 2 :=
      mul_nonneg (sq_nonneg s.lambda) (sq_nonneg s.eta)
    have hscaled :
        (s.lambda ^ 2 * s.eta ^ 2) * (t : ℝ) ^ 2 ≤
          (s.lambda ^ 2 * s.eta ^ 2) * (T : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left ht_sq_le hscale_nonneg
    calc
      s.lambda ^ 2 * s.eta ^ 2 * (t : ℝ) ^ 2 =
          (s.lambda ^ 2 * s.eta ^ 2) * (t : ℝ) ^ 2 := by ring
      _ ≤ (s.lambda ^ 2 * s.eta ^ 2) * (T : ℝ) ^ 2 := hscaled
      _ = s.lambda ^ 2 * s.eta ^ 2 * (T : ℝ) ^ 2 := by ring
      _ ≤ 1 / 4 := hquarter
  have hscalar :
      s.eta ^ 2 *
          (2 * (d : ℝ) +
            2 * (s.lambda ^ 2 * (2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ)))) ≤
        4 * s.eta ^ 2 * (d : ℝ) := by
    have hdeta_nonneg : 0 ≤ s.eta ^ 2 * (d : ℝ) :=
      mul_nonneg (sq_nonneg s.eta) (by positivity)
    have hcoef :
        2 + 4 * (s.lambda ^ 2 * s.eta ^ 2 * (t : ℝ) ^ 2) ≤ 4 := by
      nlinarith
    calc
      s.eta ^ 2 *
          (2 * (d : ℝ) +
            2 * (s.lambda ^ 2 * (2 * s.eta ^ 2 * (t : ℝ) ^ 2 * (d : ℝ)))) =
          (s.eta ^ 2 * (d : ℝ)) *
            (2 + 4 * (s.lambda ^ 2 * s.eta ^ 2 * (t : ℝ) ^ 2)) := by ring
      _ ≤ (s.eta ^ 2 * (d : ℝ)) * 4 :=
        mul_le_mul_of_nonneg_left hcoef hdeta_nonneg
      _ = 4 * s.eta ^ 2 * (d : ℝ) := by ring
  exact hstep_pre.trans hscalar

/-- Corrected non-original domain obligations needed by the Appendix A/B proof route.

These are not source-stated assumptions of Theorem 1.  They collect the beta quotient,
eta-horizon quotient, and eta-lambda contraction facts so downstream proof phases can see
the exact gap instead of inheriting it through a disguised theorem-head hypothesis. -/
def theoremOneCorrectedDomainObligations (p : ParameterSchedule) : Prop :=
  ∀ T : ℕ, 1 ≤ T →
    MomentumQuotientDomainAt (p.beta1 T) (p.beta2 T) T ∧
      EtaLambdaHorizonDomainAt (p.eta T) (p.lambda T) T

/-- Degenerate horizon-dependent parameters admitted by the printed one-sided schedule
syntax and momentum order, but rejected by the corrected Appendix A/B domain obligations.

This is a theorem-level source-gap witness for the printed boundary: Theorem 1 states
`β₂ = O(T^{-1/2})` and `η = O(d^{-1/2}T^{-3/4})` only as upper Big-O conditions, while
Appendix B later divides by `ηT`, `β₂T`, and `β₂²`. -/
def theoremOneZeroDenominatorSchedule : ParameterSchedule where
  beta1 := fun _ => 0
  beta2 := fun _ => 0
  eta := fun _ => 0
  lambda := fun _ => 0

/-- Positive slow horizon-dependent parameters for the source-valid Theorem 1
statement-boundary counterexample.

All displayed denominators are nonzero: `β₁ = β₂ = η = (T+1)^{-2}` and `λ = 0`.
These parameters still satisfy the printed one-sided upper Big-O schedules, but the
learning rate is so small that over a horizon `T` the shifted-quadratic iterates move only
`O(T/(T+1)^2)`, keeping the average true-gradient norm bounded away from zero. -/
def theoremOnePositiveSlowSchedule : ParameterSchedule where
  beta1 := fun T => (((T : ℝ) + 1) ^ 2)⁻¹
  beta2 := fun T => (((T : ℝ) + 1) ^ 2)⁻¹
  eta := fun T => (((T : ℝ) + 1) ^ 2)⁻¹
  lambda := fun _ => 0

private theorem positiveSlowValue_pos (T : ℕ) :
    0 < (((T : ℝ) + 1) ^ 2)⁻¹ := by
  positivity

private theorem positiveSlowValue_le_one (T : ℕ) :
    (((T : ℝ) + 1) ^ 2)⁻¹ ≤ 1 := by
  have hden : (1 : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by
    have hTnonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith [sq_nonneg (T : ℝ)]
  simpa [one_div] using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hden

private theorem positiveSlowValue_sq_le_self (T : ℕ) :
    ((((T : ℝ) + 1) ^ 2)⁻¹) ^ 2 ≤ (((T : ℝ) + 1) ^ 2)⁻¹ := by
  have h0 : 0 ≤ (((T : ℝ) + 1) ^ 2)⁻¹ := le_of_lt (positiveSlowValue_pos T)
  have h1 := positiveSlowValue_le_one T
  nlinarith [mul_le_mul_of_nonneg_left h1 h0]

private theorem positiveSlowValue_le_beta2Scale {T : ℕ} (hT : 1 ≤ T) :
    (((T : ℝ) + 1) ^ 2)⁻¹ ≤ beta2AsymptoticScale T := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hsqrt_pos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTpos
  have hsqrt_le_sq : Real.sqrt (T : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hden_ge_one : (1 : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by
        have hTnonneg : 0 ≤ (T : ℝ) := by positivity
        nlinarith [sq_nonneg (T : ℝ)]
      have hT_le_den : (T : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by
        have hTnonneg : 0 ≤ (T : ℝ) := by positivity
        nlinarith [sq_nonneg (T : ℝ)]
      have hden_le_den_sq :
          ((T : ℝ) + 1) ^ 2 ≤ (((T : ℝ) + 1) ^ 2) ^ 2 := by
        nlinarith [hden_ge_one, sq_nonneg (((T : ℝ) + 1) ^ 2)]
      linarith
  simpa [beta2AsymptoticScale, one_div] using
    one_div_le_one_div_of_le hsqrt_pos hsqrt_le_sq

private theorem positiveSlowValue_le_etaScale_one {T : ℕ} (hT : 1 ≤ T) :
    (((T : ℝ) + 1) ^ 2)⁻¹ ≤ etaAsymptoticScale 1 T := by
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hden_pos : 0 < Real.sqrt (1 : ℝ) *
      Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) := by
    positivity
  have hden_le_sq :
      Real.sqrt (1 : ℝ) * Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) ≤
        ((T : ℝ) + 1) ^ 2 := by
    simp
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    have hden_ge_one : (1 : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by
      have hTnonneg : 0 ≤ (T : ℝ) := by positivity
      nlinarith [sq_nonneg (T : ℝ)]
    have hT_le_den : (T : ℝ) ≤ ((T : ℝ) + 1) ^ 2 := by
      have hTnonneg : 0 ≤ (T : ℝ) := by positivity
      nlinarith [sq_nonneg (T : ℝ)]
    let den : ℝ := ((T : ℝ) + 1) ^ 2
    have hT3_le_den3 : (T : ℝ) ^ 3 ≤ den ^ 3 := by
      exact pow_le_pow_left₀ hTpos.le (by simpa [den] using hT_le_den) 3
    have hden3_le_den4 : den ^ 3 ≤ den ^ 4 := by
      have hden_nonneg : 0 ≤ den := by positivity
      calc
        den ^ 3 = den ^ 3 * 1 := by ring
        _ ≤ den ^ 3 * den :=
          mul_le_mul_of_nonneg_left (by simpa [den] using hden_ge_one)
            (pow_nonneg hden_nonneg 3)
        _ = den ^ 4 := by ring
    nlinarith [hT3_le_den3, hden3_le_den4]
  simpa [etaAsymptoticScale, one_div] using
    one_div_le_one_div_of_le hden_pos hden_le_sq

private theorem positiveSlowSchedule_beta2_isBigO :
    Asymptotics.IsBigO Filter.atTop theoremOnePositiveSlowSchedule.beta2
      beta2AsymptoticScale := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hleft : 0 ≤ theoremOnePositiveSlowSchedule.beta2 T := by
    change 0 ≤ (((T : ℝ) + 1) ^ 2)⁻¹
    exact le_of_lt (positiveSlowValue_pos T)
  have hright : 0 ≤ beta2AsymptoticScale T := by
    simp [beta2AsymptoticScale]
  rw [abs_of_nonneg hleft, abs_of_nonneg hright]
  simpa [theoremOnePositiveSlowSchedule] using positiveSlowValue_le_beta2Scale hT

private theorem positiveSlowSchedule_eta_isBigO_one :
    Asymptotics.IsBigO Filter.atTop theoremOnePositiveSlowSchedule.eta
      (etaAsymptoticScale 1) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hleft : 0 ≤ theoremOnePositiveSlowSchedule.eta T := by
    change 0 ≤ (((T : ℝ) + 1) ^ 2)⁻¹
    exact le_of_lt (positiveSlowValue_pos T)
  have hright : 0 ≤ etaAsymptoticScale 1 T := by
    simp [etaAsymptoticScale]
  rw [abs_of_nonneg hleft, abs_of_nonneg hright]
  simpa [theoremOnePositiveSlowSchedule] using positiveSlowValue_le_etaScale_one hT

/-- The printed parameter side conditions alone do not imply the corrected finite-horizon
domain obligations.

The witness sets `β₁ = β₂ = η = λ = 0` for every horizon.  These choices satisfy the
printed one-sided Big-O schedule clauses, the printed momentum order, and the displayed
weight-decay inequality as Lean renders it with totalized division, but they make the
source quotients used in Appendix A/B undefined.  This records the source-boundary gap
without strengthening `TheoremOneScheduleAssumptions`. -/
theorem theoremOne_printed_parameter_boundary_not_correctedDomain :
    (∀ T : ℕ, 1 ≤ T →
        (theoremOneZeroDenominatorSchedule.beta2 T) ^ 2 ≤
            theoremOneZeroDenominatorSchedule.beta1 T ∧
          theoremOneZeroDenominatorSchedule.beta1 T ≤
            Real.sqrt (theoremOneZeroDenominatorSchedule.beta2 T)) ∧
      Asymptotics.IsBigO Filter.atTop theoremOneZeroDenominatorSchedule.beta2
        beta2AsymptoticScale ∧
      (∀ d : ℕ,
        Asymptotics.IsBigO Filter.atTop theoremOneZeroDenominatorSchedule.eta
          (etaAsymptoticScale d)) ∧
      (∀ T : ℕ, 1 ≤ T →
        paperDisplayedLeQuotient (theoremOneZeroDenominatorSchedule.lambda T) 1
          (2 * theoremOneZeroDenominatorSchedule.eta T * (T : ℝ))) ∧
      ¬ theoremOneCorrectedDomainObligations theoremOneZeroDenominatorSchedule := by
  refine ⟨?hmomentum, ?hbeta2, ?heta, ?hweight, ?hnotDomain⟩
  · intro T hT
    simp [theoremOneZeroDenominatorSchedule]
  · simpa [theoremOneZeroDenominatorSchedule] using
      (Asymptotics.isBigO_zero beta2AsymptoticScale Filter.atTop :
        (fun _ : ℕ => (0 : ℝ)) =O[Filter.atTop] beta2AsymptoticScale)
  · intro d
    simpa [theoremOneZeroDenominatorSchedule] using
      (Asymptotics.isBigO_zero (etaAsymptoticScale d) Filter.atTop :
        (fun _ : ℕ => (0 : ℝ)) =O[Filter.atTop] etaAsymptoticScale d)
  · intro T hT
    simp [theoremOneZeroDenominatorSchedule, paperDisplayedLeQuotient]
  · intro hdomain
    have hAtOne := hdomain 1 (by norm_num)
    exact (not_lt_of_ge (le_refl (0 : ℝ))) hAtOne.1.1.1

/-- Existential form of the printed-boundary insufficiency witness, suitable for audits of
Theorem 1's statement-correction route. -/
theorem theoremOne_printed_parameter_boundary_insufficiency_witness :
    ∃ p : ParameterSchedule,
      (∀ T : ℕ, 1 ≤ T →
          (p.beta2 T) ^ 2 ≤ p.beta1 T ∧ p.beta1 T ≤ Real.sqrt (p.beta2 T)) ∧
        Asymptotics.IsBigO Filter.atTop p.beta2 beta2AsymptoticScale ∧
        (∀ d : ℕ, Asymptotics.IsBigO Filter.atTop p.eta (etaAsymptoticScale d)) ∧
        (∀ T : ℕ, 1 ≤ T →
          paperDisplayedLeQuotient (p.lambda T) 1 (2 * p.eta T * (T : ℝ))) ∧
        ¬ theoremOneCorrectedDomainObligations p := by
  exact ⟨theoremOneZeroDenominatorSchedule,
    theoremOne_printed_parameter_boundary_not_correctedDomain⟩

/-- A concrete smooth, deterministic problem used only for the Theorem 1 statement-boundary
audit.

The objective and oracle are identically zero, and the initial point is zero.  Paired with
`theoremOneZeroDenominatorSchedule`, it satisfies the paper's printed one-sided schedule
boundary while still failing the corrected Appendix A/B denominator obligations. -/
def theoremOneZeroProblemSetup : Setup 1 where
  Sample := Unit
  sampleMeasurable := inferInstance
  oracleLaw := Measure.dirac ()
  oracleLaw_isProbability := by infer_instance
  f := fun _ => 0
  stochasticGradient := fun _ _ => 0
  L := 0
  sigma := 0
  Delta_f := 0
  beta1 := 0
  beta2 := 0
  eta := 0
  lambda := 0
  x1 := 0

private theorem theoremOneZeroProblemSetup_smoothness :
    theoremOneZeroProblemSetup.Smoothness := by
  constructor
  · intro x
    simpa [Setup.trueGradient, theoremOneZeroProblemSetup] using
      (hasGradientAt_const (x := x) (c := (0 : ℝ)))
  · intro x y
    simp [Setup.trueGradient, theoremOneZeroProblemSetup]

private theorem theoremOneZeroProblemSetup_oracleUnbiased :
    theoremOneZeroProblemSetup.OracleUnbiased := by
  intro x
  simp [Setup.OracleUnbiased, Setup.oracleValue, Setup.trueGradient,
    theoremOneZeroProblemSetup]

private theorem theoremOneZeroProblemSetup_oracleBoundedNoise :
    theoremOneZeroProblemSetup.OracleBoundedNoise := by
  intro x
  simp [Setup.OracleBoundedNoise, Setup.oracleValue, Setup.trueGradient,
    theoremOneZeroProblemSetup]

private theorem theoremOneZeroProblemSetup_initialGap :
    theoremOneZeroProblemSetup.InitialGap := by
  constructor
  · rw [Setup.fStar_eq_sInf_range]
    simpa [theoremOneZeroProblemSetup, Set.range_const] using
      (isGLB_singleton (a := (0 : ℝ)))
  · simp [Setup.fStar, theoremOneZeroProblemSetup]

/-- The zero problem together with the zero denominator schedule satisfies the printed
Theorem 1 assumptions as they are currently stated in Lean. -/
theorem theoremOne_zeroProblem_printedScheduleAssumptions :
    TheoremOneScheduleAssumptions theoremOneZeroProblemSetup
      theoremOneZeroDenominatorSchedule := by
  refine
    { smoothness := theoremOneZeroProblemSetup_smoothness
      oracle_unbiased := theoremOneZeroProblemSetup_oracleUnbiased
      oracle_bounded_noise := theoremOneZeroProblemSetup_oracleBoundedNoise
      initial_gap := theoremOneZeroProblemSetup_initialGap
      momentum_order := ?_
      beta2_schedule := ?_
      eta_schedule := ?_
      weight_decay_bound := ?_
      initial_infinity_bound := ?_ }
  · intro T hT
    simp [theoremOneZeroDenominatorSchedule]
  · simpa [theoremOneZeroDenominatorSchedule] using
      (Asymptotics.isBigO_zero beta2AsymptoticScale Filter.atTop :
        (fun _ : ℕ => (0 : ℝ)) =O[Filter.atTop] beta2AsymptoticScale)
  · simpa [theoremOneZeroDenominatorSchedule] using
      (Asymptotics.isBigO_zero (etaAsymptoticScale 1) Filter.atTop :
        (fun _ : ℕ => (0 : ℝ)) =O[Filter.atTop] etaAsymptoticScale 1)
  · intro T hT
    simp [theoremOneZeroDenominatorSchedule, paperDisplayedLeQuotient]
  · intro T hT
    simp [theoremOneZeroProblemSetup, linfNorm, theoremOneZeroDenominatorSchedule]

/-- Corrected non-original Theorem 1 assumption boundary.  This is not the printed theorem:
it pairs the printed assumptions with the extra Appendix A/B domain obligations that the
paper uses without stating. -/
def theoremOne_correctedDomainAssumptions {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (p : ParameterSchedule) : Prop :=
  TheoremOneScheduleAssumptions s p ∧ theoremOneCorrectedDomainObligations p

/-- The corrected non-original rate boundary needed for Appendix B's final asymptotic step.

The first two fields are the printed theorem assumptions and the already-audited
finite-horizon domain correction.  The remaining fields expose the reciprocal-rate
information that Appendix B uses when it simplifies the finite-horizon expression to
`O(d^{1/2}T^{-1/4})`; these fields are deliberately not part of
`TheoremOneScheduleAssumptions`. -/
structure theoremOne_correctedRateAssumptions {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (p : ParameterSchedule) : Prop where
  printed : TheoremOneScheduleAssumptions s p
  domains : theoremOneCorrectedDomainObligations p
  etaT_reciprocal_schedule :
    Asymptotics.IsBigO Filter.atTop
      (fun T => ((p.eta T) * (T : ℝ))⁻¹) (theoremOneRateScale d)
  beta2T_reciprocal_schedule :
    Asymptotics.IsBigO Filter.atTop
      (fun T => ((p.beta2 T) * (T : ℝ))⁻¹) beta2AsymptoticScale

private theorem theoremOne_eta_beta_scale {d : ℕ} [Nonempty (Fin d)] :
    Asymptotics.IsBigO Filter.atTop
      (fun T => (etaAsymptoticScale d T) ^ 2 * (beta2AsymptoticScale T) ^ 2 *
        ((T : ℝ) ^ 2 * (d : ℝ)))
      beta2AsymptoticScale := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hscale_eq :
      (etaAsymptoticScale d T) ^ 2 * (beta2AsymptoticScale T) ^ 2 *
          ((T : ℝ) ^ 2 * (d : ℝ)) = beta2AsymptoticScale T := by
    have hTpos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
    have hdpos_nat0 : 0 < d := Fin.pos_iff_nonempty.mpr inferInstance
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast hdpos_nat0
    have hsqrt_cube_mul :
        Real.sqrt ((T : ℝ) ^ 3) * Real.sqrt (T : ℝ) = (T : ℝ) ^ 2 := by
      refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
      rw [mul_pow]
      rw [Real.sq_sqrt (by positivity : 0 ≤ (T : ℝ) ^ 3)]
      rw [Real.sq_sqrt (le_of_lt hTpos)]
      ring
    have hden_eta :
        Real.sqrt (d : ℝ) * Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) ≠ 0 := by
      positivity
    have hden_beta : Real.sqrt (T : ℝ) ≠ 0 := by positivity
    dsimp [etaAsymptoticScale, beta2AsymptoticScale]
    field_simp [hden_eta, hden_beta]
    rw [Real.sq_sqrt (le_of_lt hdpos)]
    have hcube_nonneg : 0 ≤ (T : ℝ) ^ 3 := by positivity
    rw [Real.sq_sqrt (Real.sqrt_nonneg ((T : ℝ) ^ 3))]
    conv_rhs => rw [mul_assoc, hsqrt_cube_mul]
    ring
  have hright_nonneg : 0 ≤ beta2AsymptoticScale T := by
    dsimp [beta2AsymptoticScale]
    positivity
  rw [hscale_eq]
  simpa using le_rfl

/-- Retained minimality derivation for the corrected-rate estimator reciprocal-square term.

The Appendix B term `η^2 d / β₂^2` does not need to be a primitive corrected-rate premise:
it follows from the printed eta schedule together with the corrected reciprocal
`(β₂ T)^{-1}` schedule, since
`(d^{-1/2}T^{-3/4})^2 * (T^{-1/2})^2 * T^2 * d = T^{-1/2}`. -/
theorem theoremOne_eta_sq_beta2_sq_schedule_from_smaller_schedules_attempt
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {p : ParameterSchedule}
    (hprinted : TheoremOneScheduleAssumptions s p)
    (hbeta2T : Asymptotics.IsBigO Filter.atTop
      (fun T => ((p.beta2 T) * (T : ℝ))⁻¹) beta2AsymptoticScale) :
    Asymptotics.IsBigO Filter.atTop
      (fun T => (p.eta T) ^ 2 * (((p.beta2 T) ^ 2)⁻¹) * (d : ℝ))
      beta2AsymptoticScale := by
  have hraw :
      Asymptotics.IsBigO Filter.atTop
        (fun T => (p.eta T) ^ 2 * (((p.beta2 T) * (T : ℝ))⁻¹) ^ 2 *
          ((T : ℝ) ^ 2 * (d : ℝ)))
        (fun T => (etaAsymptoticScale d T) ^ 2 * (beta2AsymptoticScale T) ^ 2 *
          ((T : ℝ) ^ 2 * (d : ℝ))) := by
    have heta2 := hprinted.eta_schedule.pow 2
    have hbeta2 := hbeta2T.pow 2
    have htd :
        Asymptotics.IsBigO Filter.atTop
          (fun T : ℕ => (T : ℝ) ^ 2 * (d : ℝ))
          (fun T : ℕ => (T : ℝ) ^ 2 * (d : ℝ)) :=
      Asymptotics.isBigO_refl _ _
    simpa [Pi.pow_apply] using (heta2.mul hbeta2).mul htd
  have htarget := hraw.trans (theoremOne_eta_beta_scale (d := d))
  refine htarget.congr' ?_ (Filter.Eventually.of_forall fun T => rfl)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hT))
  have hinv_sq :
      (((p.beta2 T) ^ 2)⁻¹) =
        (((p.beta2 T) * (T : ℝ))⁻¹) ^ 2 * (T : ℝ) ^ 2 := by
    field_simp [hTne]
  rw [hinv_sq]
  ring

/-- The same concrete printed-boundary instance is rejected by the corrected-rate boundary,
because Appendix A/B require nonzero denominator/domain facts. -/
theorem theoremOne_zeroProblem_printedBoundary_not_correctedRate :
    ¬ theoremOne_correctedRateAssumptions theoremOneZeroProblemSetup
      theoremOneZeroDenominatorSchedule := by
  intro h
  have hAtOne := h.domains 1 (by norm_num)
  exact (not_lt_of_ge (le_refl (0 : ℝ))) hAtOne.1.1.1

/-- Theorem-level source-boundary certificate for the printed Theorem 1 assumptions.

This is stronger than the parameter-only witness: it gives an actual smooth deterministic
problem satisfying `TheoremOneScheduleAssumptions`, while the corrected reciprocal/domain
boundary used by Appendix A/B is false.  It records under-specification of the printed
Theorem 1 boundary without adding non-source hypotheses to that boundary. -/
def theoremOne_printedTheoremBoundary_underSpecifiedCertificate : Prop :=
  ∃ s : Setup.{0} 1, ∃ p : ParameterSchedule,
    TheoremOneScheduleAssumptions s p ∧ ¬ theoremOne_correctedRateAssumptions s p

/-- The printed Theorem 1 boundary is under-specified at theorem granularity. -/
theorem theoremOne_printedTheoremBoundary_underSpecifiedCertificate_holds :
    theoremOne_printedTheoremBoundary_underSpecifiedCertificate := by
  exact ⟨theoremOneZeroProblemSetup, theoremOneZeroDenominatorSchedule,
    theoremOne_zeroProblem_printedScheduleAssumptions,
    theoremOne_zeroProblem_printedBoundary_not_correctedRate⟩

/-- A retained source-granularity bridge obstruction requested by the reconstruction audit.

There is no theorem-level bridge from the printed `TheoremOneScheduleAssumptions` boundary
to the corrected-rate boundary used by the Appendix B proof route.  The zero-denominator
schedule satisfies the printed assumptions for the concrete zero problem, but it fails the
corrected reciprocal/domain boundary. -/
theorem theoremOne_printedScheduleAssumptions_do_not_imply_correctedRate :
    ¬ (∀ (s : Setup.{0} 1) (p : ParameterSchedule),
        TheoremOneScheduleAssumptions s p → theoremOne_correctedRateAssumptions s p) := by
  intro hbridge
  exact theoremOne_zeroProblem_printedBoundary_not_correctedRate
    (hbridge theoremOneZeroProblemSetup theoremOneZeroDenominatorSchedule
      theoremOne_zeroProblem_printedScheduleAssumptions)

/-- The one-dimensional unit point used in the concrete false-conclusion witness. -/
def theoremOneUnitPoint : Point 1 :=
  WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ)

/-- A deterministic shifted quadratic with nonzero gradient at the required zero initial
point.

Together with the zero denominator schedule, this satisfies the printed one-sided
Theorem 1 assumptions.  Since `η = 0`, the generated iterates never move from `x₁ = 0`,
so the average true-gradient `ℓ₁` norm is constantly one rather than decaying at
`O(T^{-1/4})`. -/
def theoremOneShiftedQuadraticSetup : Setup 1 where
  Sample := Unit
  sampleMeasurable := inferInstance
  oracleLaw := Measure.dirac ()
  oracleLaw_isProbability := by infer_instance
  f := fun x => (1 / 2 : ℝ) * ‖x - theoremOneUnitPoint‖ ^ 2
  stochasticGradient := fun x _ => x - theoremOneUnitPoint
  L := 1
  sigma := 0
  Delta_f := 1
  beta1 := 0
  beta2 := 0
  eta := 0
  lambda := 0
  x1 := 0

private theorem theoremOneUnitPoint_norm : ‖theoremOneUnitPoint‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]
  simp [theoremOneUnitPoint]

private theorem theoremOneUnitPoint_initial_distance_norm :
    ‖(0 : Point 1) - theoremOneUnitPoint‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]
  simp [theoremOneUnitPoint]

private theorem theoremOneUnitPoint_l1_neg :
    l1Norm (-(theoremOneUnitPoint : Point 1)) = 1 := by
  simp [l1Norm, theoremOneUnitPoint]

private theorem theoremOneShiftedQuadraticSetup_trueGradient_eq (x : Point 1) :
    theoremOneShiftedQuadraticSetup.trueGradient x = x - theoremOneUnitPoint := by
  unfold Setup.trueGradient theoremOneShiftedQuadraticSetup
  simpa using
    (hasGradientAt_const_mul_norm_sub_sq_centered (1 : ℝ) theoremOneUnitPoint x).gradient

private theorem theoremOneShiftedQuadraticSetup_smoothness :
    theoremOneShiftedQuadraticSetup.Smoothness := by
  constructor
  · intro x
    rw [theoremOneShiftedQuadraticSetup_trueGradient_eq x]
    change
      HasGradientAt (fun y : Point 1 => (1 / 2 : ℝ) * ‖y - theoremOneUnitPoint‖ ^ 2)
        (x - theoremOneUnitPoint) x
    simpa using
      (hasGradientAt_const_mul_norm_sub_sq_centered (1 : ℝ) theoremOneUnitPoint x)
  · intro x y
    rw [theoremOneShiftedQuadraticSetup_trueGradient_eq x,
      theoremOneShiftedQuadraticSetup_trueGradient_eq y]
    have hdiff : x - theoremOneUnitPoint - (y - theoremOneUnitPoint) = x - y := by
      abel
    rw [hdiff]
    simp [theoremOneShiftedQuadraticSetup]

private theorem theoremOneShiftedQuadraticSetup_oracleUnbiased :
    theoremOneShiftedQuadraticSetup.OracleUnbiased := by
  intro x
  rw [theoremOneShiftedQuadraticSetup_trueGradient_eq x]
  constructor
  · exact MeasureTheory.integrable_const (x - theoremOneUnitPoint)
  · change ∫ _ξ : Unit, x - theoremOneUnitPoint ∂Measure.dirac () =
      x - theoremOneUnitPoint
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    simp

private theorem theoremOneShiftedQuadraticSetup_oracleBoundedNoise :
    theoremOneShiftedQuadraticSetup.OracleBoundedNoise := by
  intro x
  rw [theoremOneShiftedQuadraticSetup_trueGradient_eq x]
  constructor
  · simpa [Setup.oracleValue, theoremOneShiftedQuadraticSetup] using
      (MeasureTheory.integrable_const (0 : ℝ))
  · simp [Setup.oracleValue, theoremOneShiftedQuadraticSetup]

private theorem theoremOneShiftedQuadraticSetup_initialGap :
    theoremOneShiftedQuadraticSetup.InitialGap := by
  have hglb0 : IsGLB (Set.range theoremOneShiftedQuadraticSetup.f) (0 : ℝ) := by
    constructor
    · rintro y ⟨x, rfl⟩
      simp [theoremOneShiftedQuadraticSetup]
    · intro b hb
      have hcenter := hb ⟨theoremOneUnitPoint, rfl⟩
      simpa [theoremOneShiftedQuadraticSetup] using hcenter
  have hfstar : theoremOneShiftedQuadraticSetup.fStar = 0 := by
    simpa [Setup.fStar] using hglb0.csInf_eq (Set.range_nonempty theoremOneShiftedQuadraticSetup.f)
  constructor
  · rwa [hfstar]
  · have hdist : ‖(0 : Point 1) - theoremOneUnitPoint‖ = 1 :=
      theoremOneUnitPoint_initial_distance_norm
    rw [hfstar]
    simp [theoremOneShiftedQuadraticSetup, hdist, theoremOneUnitPoint_norm]
    norm_num

/-- The shifted quadratic counterexample satisfies the printed Theorem 1 assumptions. -/
theorem theoremOne_shiftedQuadratic_printedScheduleAssumptions :
    TheoremOneScheduleAssumptions theoremOneShiftedQuadraticSetup
      theoremOneZeroDenominatorSchedule := by
  refine
    { smoothness := theoremOneShiftedQuadraticSetup_smoothness
      oracle_unbiased := theoremOneShiftedQuadraticSetup_oracleUnbiased
      oracle_bounded_noise := theoremOneShiftedQuadraticSetup_oracleBoundedNoise
      initial_gap := theoremOneShiftedQuadraticSetup_initialGap
      momentum_order := ?_
      beta2_schedule := ?_
      eta_schedule := ?_
      weight_decay_bound := ?_
      initial_infinity_bound := ?_ }
  · intro T hT
    simp [theoremOneZeroDenominatorSchedule]
  · simpa [theoremOneZeroDenominatorSchedule] using
      (Asymptotics.isBigO_zero beta2AsymptoticScale Filter.atTop :
        (fun _ : ℕ => (0 : ℝ)) =O[Filter.atTop] beta2AsymptoticScale)
  · simpa [theoremOneZeroDenominatorSchedule] using
      (Asymptotics.isBigO_zero (etaAsymptoticScale 1) Filter.atTop :
        (fun _ : ℕ => (0 : ℝ)) =O[Filter.atTop] etaAsymptoticScale 1)
  · intro T hT
    simp [theoremOneZeroDenominatorSchedule, paperDisplayedLeQuotient]
  · intro T hT
    simp [theoremOneShiftedQuadraticSetup, linfNorm, theoremOneZeroDenominatorSchedule]

/-- The shifted quadratic also satisfies the printed Theorem 1 assumptions under the
positive slow schedule.  This avoids the zero-denominator fallback while preserving the
one-sided schedule weakness: `η_T = β₂,T = (T+1)^{-2}` is still `O(T^{-3/4})` and
`O(T^{-1/2})`. -/
theorem theoremOne_shiftedQuadratic_positiveSlow_printedScheduleAssumptions :
    TheoremOneScheduleAssumptions theoremOneShiftedQuadraticSetup
      theoremOnePositiveSlowSchedule := by
  refine
    { smoothness := theoremOneShiftedQuadraticSetup_smoothness
      oracle_unbiased := theoremOneShiftedQuadraticSetup_oracleUnbiased
      oracle_bounded_noise := theoremOneShiftedQuadraticSetup_oracleBoundedNoise
      initial_gap := theoremOneShiftedQuadraticSetup_initialGap
      momentum_order := ?_
      beta2_schedule := positiveSlowSchedule_beta2_isBigO
      eta_schedule := positiveSlowSchedule_eta_isBigO_one
      weight_decay_bound := ?_
      initial_infinity_bound := ?_ }
  · intro T hT
    constructor
    · simpa [theoremOnePositiveSlowSchedule] using positiveSlowValue_sq_le_self T
    · have h0 : 0 ≤ (((T : ℝ) + 1) ^ 2)⁻¹ :=
        le_of_lt (positiveSlowValue_pos T)
      have hsq := positiveSlowValue_sq_le_self T
      simpa [theoremOnePositiveSlowSchedule] using (Real.le_sqrt h0 h0).2 hsq
  · intro T hT
    simp [theoremOnePositiveSlowSchedule, paperDisplayedLeQuotient]
    positivity
  · intro T hT
    simp [theoremOneShiftedQuadraticSetup, linfNorm, theoremOnePositiveSlowSchedule]
    positivity

private theorem process_x_eq_x1_of_eta_zero {d : ℕ} (s : Setup d) (heta : s.eta = 0) :
    ∀ n : ℕ, ∀ ω : Run s, (process s n ω).x = s.x1 := by
  intro n
  induction n with
  | zero =>
      intro ω
      simp [process_zero]
  | succ n ih =>
      intro ω
      rw [process_succ, transition_x, nextX, ih ω]
      simp [heta]

private theorem x_eq_x1_of_eta_zero {d : ℕ} (s : Setup d) (heta : s.eta = 0)
    (t : ℕ) (ω : Run s) :
    x s t ω = s.x1 := by
  simpa [x, stateAt] using process_x_eq_x1_of_eta_zero s heta (t - 1) ω

private theorem theoremOneRateScale_one_tendsto_zero :
    Filter.Tendsto (theoremOneRateScale 1) Filter.atTop (nhds 0) := by
  have hcast : Filter.Tendsto (fun T : ℕ => (T : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt_atTop :
      Filter.Tendsto (fun T : ℕ => Real.sqrt (T : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hsqrt_sqrt_atTop :
      Filter.Tendsto (fun T : ℕ => Real.sqrt (Real.sqrt (T : ℝ)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hsqrt_atTop
  have hinv :
      Filter.Tendsto (fun T : ℕ => (Real.sqrt (Real.sqrt (T : ℝ)))⁻¹)
        Filter.atTop (nhds 0) :=
    Filter.Tendsto.inv_tendsto_atTop hsqrt_sqrt_atTop
  refine Filter.Tendsto.congr' ?_ hinv
  filter_upwards with T
  simp [theoremOneRateScale, div_eq_mul_inv]

private theorem not_tendsto_const_one_atTop_zero :
    ¬ Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 0) := by
  intro h
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique hconst h
  norm_num at h01

/-- A corrected-rate boundary contains the corrected finite-horizon domain boundary. -/
theorem theoremOne_correctedRateAssumptions_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule}
    (h : theoremOne_correctedRateAssumptions s p) :
    theoremOne_correctedDomainAssumptions s p :=
  ⟨h.printed, h.domains⟩

/-- Active source-boundary correction record for Theorem 1.

The corrected-rate record retains the printed source assumptions while exposing the
non-source domain and reciprocal-rate obligations needed by Appendix A/B.  Consumers must
not treat this as the unqualified paper theorem boundary. -/
def theoremOne_sourceBoundary_activeSignatureContractStatement {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (p : ParameterSchedule) : Prop :=
  theoremOne_correctedRateAssumptions s p

/-- Extract the printed Theorem 1 assumptions from the active boundary record. -/
theorem theoremOne_sourceBoundary_printedAssumptions {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule}
    (h :
      theoremOne_sourceBoundary_activeSignatureContractStatement s p) :
    TheoremOneScheduleAssumptions s p :=
  h.printed

/-- Extract the corrected Appendix A/B domain obligations from the active boundary record. -/
theorem theoremOne_sourceBoundary_correctedDomainObligations {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule}
    (h :
      theoremOne_sourceBoundary_activeSignatureContractStatement s p) :
    theoremOneCorrectedDomainObligations p :=
  h.domains

/-- The finite-horizon sum of `ℓ₁` true-gradient norms along generated Lion iterates. -/
def gradientL1Sum {d : ℕ} (s : Setup d) (T : ℕ) : Run s → ℝ :=
  fun ω => (Finset.Icc 1 T).sum fun t => l1Norm (s.trueGradient (x s t ω))

/-- The finite-horizon average expected `ℓ₁` norm of the true gradient along generated
Lion iterates, with expectation taken under the canonical iid oracle-sample stream law. -/
def averageExpectedGradientL1 {d : ℕ} (s : Setup d) (T : ℕ) : ℝ :=
  letI := s.sampleMeasurable
  (T : ℝ)⁻¹ * ∫ ω, gradientL1Sum s T ω ∂Run.law s

/-- Definitional equation for the generated finite-horizon expected average. -/
theorem averageExpectedGradientL1_eq {d : ℕ} (s : Setup d) (T : ℕ) :
    averageExpectedGradientL1 s T =
      (letI := s.sampleMeasurable;
        (T : ℝ)⁻¹ * ∫ ω, gradientL1Sum s T ω ∂Run.law s) := by
  rfl

private theorem sampledGradient_fixed_integrable_from_oracleUnbiased {d : ℕ}
    {s : Setup d} (t : ℕ) (z : Point d) (hunb : s.OracleUnbiased) :
    (letI := s.sampleMeasurable;
      Integrable (fun ω : Run s => sampledGradient s t z ω) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  have hcoord : Measurable (Run.sampleAt s t) := by
    simpa [Run.sampleAt] using
      (measurable_pi_apply (t - 1) : Measurable (fun ω : Run s => ω (t - 1)))
  have hbase :
      Integrable (fun ξ : s.Sample => s.oracleValue z ξ)
        (Measure.map (Run.sampleAt s t) (Run.law s)) := by
    rw [Run.map_sampleAt_law]
    exact Setup.oracleUnbiased_integrable hunb z
  simpa [sampledGradient, Function.comp_def] using
    (MeasureTheory.integrable_map_measure hbase.aestronglyMeasurable
      hcoord.aemeasurable).1 hbase

private theorem sampledGradient_integrable_of_finiteRange_query {d : ℕ}
    {s : Setup d} (t : ℕ) {q : Run s → Point d}
    (hq_meas : AEMeasurable q (Run.law s)) (hq_fin : (Set.range q).Finite)
    (hunb : s.OracleUnbiased) :
    (letI := s.sampleMeasurable;
      Integrable (fun ω : Run s => sampledGradient s t (q ω) ω) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  let S : Finset (Point d) := hq_fin.toFinset
  have hmemS : ∀ ω : Run s, q ω ∈ S := by
    intro ω
    simp [S, Set.Finite.mem_toFinset]
  have hsum_int :
      Integrable
        (fun ω : Run s =>
          Finset.sum S fun z =>
            (q ⁻¹' ({z} : Set (Point d))).indicator
              (fun ω' : Run s => sampledGradient s t z ω') ω)
        (Run.law s) := by
    refine MeasureTheory.integrable_finset_sum (s := S) ?_
    intro z _hz
    have hset : NullMeasurableSet (q ⁻¹' ({z} : Set (Point d))) (Run.law s) :=
      hq_meas.nullMeasurableSet_preimage (measurableSet_singleton z)
    exact (sampledGradient_fixed_integrable_from_oracleUnbiased t z hunb).indicator₀ hset
  refine hsum_int.congr (MeasureTheory.ae_of_all (Run.law s) ?_)
  intro ω
  change
    Finset.sum S
        (fun z =>
          (q ⁻¹' ({z} : Set (Point d))).indicator
            (fun ω' : Run s => sampledGradient s t z ω') ω) =
      sampledGradient s t (q ω) ω
  rw [Finset.sum_eq_single (q ω)]
  · simp
  · intro z _hz hzne
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hzne (by simpa using hmem.symm)
  · intro hnot
    exact False.elim (hnot (hmemS ω))

private theorem l1_trueGradient_integrable_of_x_finiteRange {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (s : Setup d) {y : Ω → Point d}
    (hy_meas : AEMeasurable y μ) (hy_fin : (Set.range y).Finite) :
    Integrable (fun ω : Ω => l1Norm (s.trueGradient (y ω))) μ := by
  classical
  let φ : Point d → ℝ := fun z => l1Norm (s.trueGradient z)
  have hmap : Integrable φ (Measure.map y μ) :=
    integrable_map_of_finite_range y hy_meas hy_fin φ
  simpa [φ, Function.comp_def] using
    (MeasureTheory.integrable_map_measure hmap.aestronglyMeasurable hy_meas).1 hmap

private theorem trueGradient_integrable_of_x_finiteRange {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (s : Setup d) {y : Ω → Point d}
    (hy_meas : AEMeasurable y μ) (hy_fin : (Set.range y).Finite) :
    Integrable (fun ω : Ω => s.trueGradient (y ω)) μ := by
  classical
  let φ : Point d → Point d := fun z => s.trueGradient z
  have hmap : Integrable φ (Measure.map y μ) :=
    integrable_map_of_finite_range y hy_meas hy_fin φ
  simpa [φ, Function.comp_def] using
    (MeasureTheory.integrable_map_measure hmap.aestronglyMeasurable hy_meas).1 hmap

private theorem trueGradient_sq_integrable_of_x_finiteRange {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (s : Setup d) {y : Ω → Point d}
    (hy_meas : AEMeasurable y μ) (hy_fin : (Set.range y).Finite) :
    Integrable (fun ω : Ω => ‖s.trueGradient (y ω)‖ ^ 2) μ := by
  classical
  let φ : Point d → ℝ := fun z => ‖s.trueGradient z‖ ^ 2
  have hmap : Integrable φ (Measure.map y μ) :=
    integrable_map_of_finite_range y hy_meas hy_fin φ
  simpa [φ, Function.comp_def] using
    (MeasureTheory.integrable_map_measure hmap.aestronglyMeasurable hy_meas).1 hmap

private theorem fixed_oracle_residual_integrable_and_integral_eq_zero {d : ℕ}
    {s : Setup d} (hunb : s.OracleUnbiased) (z : Point d) :
    (letI := s.sampleMeasurable;
      Integrable (fun ξ => s.oracleValue z ξ - s.trueGradient z) s.oracleLaw ∧
        ∫ ξ, s.oracleValue z ξ - s.trueGradient z ∂s.oracleLaw = 0) := by
  classical
  letI := s.sampleMeasurable
  have hval_int : Integrable (fun ξ => s.oracleValue z ξ) s.oracleLaw :=
    Setup.oracleUnbiased_integrable hunb z
  have hconst_int : Integrable (fun _ξ : s.Sample => s.trueGradient z) s.oracleLaw :=
    integrable_const _
  have hres_int : Integrable (fun ξ => s.oracleValue z ξ - s.trueGradient z) s.oracleLaw :=
    hval_int.sub hconst_int
  refine ⟨hres_int, ?_⟩
  rw [MeasureTheory.integral_sub hval_int hconst_int]
  rw [Setup.oracleUnbiased_integral_eq hunb z]
  simp

private theorem integrable_sq_norm_add {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {u v : Ω → E}
    (hu_meas : AEStronglyMeasurable u μ) (hv_meas : AEStronglyMeasurable v μ)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) μ)
    (hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖u ω + v ω‖ ^ 2) μ := by
  have hu_l2 : MemLp u 2 μ :=
    (memLp_two_iff_integrable_sq_norm hu_meas).2 hu_sq
  have hv_l2 : MemLp v 2 μ :=
    (memLp_two_iff_integrable_sq_norm hv_meas).2 hv_sq
  exact
    (memLp_two_iff_integrable_sq_norm (hu_meas.add hv_meas)).1
      (hu_l2.add hv_l2)

private theorem integrable_sq_norm_neg {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {u : Ω → E}
    (hu_meas : AEStronglyMeasurable u μ)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖-u ω‖ ^ 2) μ := by
  have hu_l2 : MemLp u 2 μ :=
    (memLp_two_iff_integrable_sq_norm hu_meas).2 hu_sq
  exact
    (memLp_two_iff_integrable_sq_norm hu_meas.neg).1
      hu_l2.neg

private theorem integrable_sq_norm_sub {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {u v : Ω → E}
    (hu_meas : AEStronglyMeasurable u μ) (hv_meas : AEStronglyMeasurable v μ)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) μ)
    (hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖u ω - v ω‖ ^ 2) μ := by
  have hsub :
      Integrable (fun ω => ‖u ω + -v ω‖ ^ 2) μ :=
    integrable_sq_norm_add hu_meas hv_meas.neg hu_sq
      (integrable_sq_norm_neg hv_meas hv_sq)
  simpa [sub_eq_add_neg] using hsub

private theorem integrable_sq_norm_const_smul {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω} {u : Ω → E}
    (c : ℝ) (hu_meas : AEStronglyMeasurable u μ)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖c • u ω‖ ^ 2) μ := by
  have hu_l2 : MemLp u 2 μ :=
    (memLp_two_iff_integrable_sq_norm hu_meas).2 hu_sq
  exact
    (memLp_two_iff_integrable_sq_norm (hu_meas.const_smul c)).1
      (hu_l2.const_smul c)

private theorem fixed_oracleValue_sq_integrable {d : ℕ}
    {s : Setup d} (hunb : s.OracleUnbiased) (hnoise : s.OracleBoundedNoise)
    (z : Point d) :
    (letI := s.sampleMeasurable;
      Integrable (fun ξ => ‖s.oracleValue z ξ‖ ^ 2) s.oracleLaw) := by
  classical
  letI := s.sampleMeasurable
  have hres_sq :
      Integrable (fun ξ => ‖s.oracleValue z ξ - s.trueGradient z‖ ^ 2)
        s.oracleLaw :=
    Setup.oracleBoundedNoise_integrable hnoise z
  have hres_meas :
      AEStronglyMeasurable (fun ξ => s.oracleValue z ξ - s.trueGradient z)
        s.oracleLaw :=
    ((fixed_oracle_residual_integrable_and_integral_eq_zero (s := s) hunb z).1).aestronglyMeasurable
  have hconst_sq :
      Integrable (fun _ξ : s.Sample => ‖s.trueGradient z‖ ^ 2) s.oracleLaw :=
    integrable_const _
  have hconst_meas :
      AEStronglyMeasurable (fun _ξ : s.Sample => s.trueGradient z) s.oracleLaw :=
    aestronglyMeasurable_const
  have hsum_sq :
      Integrable
        (fun ξ => ‖(s.oracleValue z ξ - s.trueGradient z) + s.trueGradient z‖ ^ 2)
        s.oracleLaw :=
    integrable_sq_norm_add hres_meas hconst_meas hres_sq hconst_sq
  refine hsum_sq.congr (MeasureTheory.ae_of_all s.oracleLaw ?_)
  intro ξ
  simp

private theorem sampledGradient_sq_integrable_of_finiteRange_query {d : ℕ}
    {s : Setup d} (t : ℕ) {q : Run s → Point d}
    (hq_meas : AEMeasurable q (Run.law s)) (hq_fin : (Set.range q).Finite)
    (hunb : s.OracleUnbiased) (hnoise : s.OracleBoundedNoise) :
    (letI := s.sampleMeasurable;
      Integrable (fun ω : Run s => ‖sampledGradient s t (q ω) ω‖ ^ 2)
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  let S : Finset (Point d) := hq_fin.toFinset
  have hmemS : ∀ ω : Run s, q ω ∈ S := by
    intro ω
    simp [S, Set.Finite.mem_toFinset]
  have hsum_int :
      Integrable
        (fun ω : Run s =>
          Finset.sum S fun z =>
            (q ⁻¹' ({z} : Set (Point d))).indicator
              (fun ω' : Run s => ‖sampledGradient s t z ω'‖ ^ 2) ω)
        (Run.law s) := by
    refine MeasureTheory.integrable_finset_sum (s := S) ?_
    intro z _hz
    have hset : NullMeasurableSet (q ⁻¹' ({z} : Set (Point d))) (Run.law s) :=
      hq_meas.nullMeasurableSet_preimage (measurableSet_singleton z)
    let φ : s.Sample → ℝ := fun ξ => ‖s.oracleValue z ξ‖ ^ 2
    have hsample_meas : Measurable (Run.sampleAt s t) := by
      simpa [Run.sampleAt] using
        (measurable_pi_apply (t - 1) : Measurable (fun ω : Run s => ω (t - 1)))
    have hφ_map :
        Integrable φ (Measure.map (Run.sampleAt s t) (Run.law s)) := by
      rw [Run.map_sampleAt_law]
      exact fixed_oracleValue_sq_integrable (s := s) hunb hnoise z
    have hbase :
        Integrable (fun ω : Run s => ‖sampledGradient s t z ω‖ ^ 2) (Run.law s) := by
      simpa [φ, Function.comp_def, sampledGradient] using
        (MeasureTheory.integrable_map_measure hφ_map.aestronglyMeasurable
          hsample_meas.aemeasurable).1 hφ_map
    exact hbase.indicator₀ hset
  refine hsum_int.congr (MeasureTheory.ae_of_all (Run.law s) ?_)
  intro ω
  change
    Finset.sum S
        (fun z =>
          (q ⁻¹' ({z} : Set (Point d))).indicator
            (fun ω' : Run s => ‖sampledGradient s t z ω'‖ ^ 2) ω) =
      ‖sampledGradient s t (q ω) ω‖ ^ 2
  rw [Finset.sum_eq_single (q ω)]
  · simp
  · intro z _hz hzne
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hzne (by simpa using hmem.symm)
  · intro hnot
    exact False.elim (hnot (hmemS ω))

private theorem nextX_regularity_of_x_finiteRange_and_v_integrable {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (s : Setup d) {X V : Ω → Point d}
    (hX_meas : AEMeasurable X μ) (hX_fin : (Set.range X).Finite)
    (hV_int : Integrable V μ) :
    AEMeasurable
        (fun ω : Ω => X ω - s.eta • (coordinateSign (V ω) + s.lambda • X ω)) μ ∧
      (Set.range
        (fun ω : Ω => X ω - s.eta • (coordinateSign (V ω) + s.lambda • X ω))).Finite := by
  classical
  have hV_aemeas : AEMeasurable V μ :=
    hV_int.aestronglyMeasurable.aemeasurable
  have hsign_meas : AEMeasurable (fun ω : Ω => coordinateSign (V ω)) μ :=
    coordinateSign_measurable.comp_aemeasurable hV_aemeas
  have hnext_meas :
      AEMeasurable
        (fun ω : Ω => X ω - s.eta • (coordinateSign (V ω) + s.lambda • X ω)) μ :=
    hX_meas.sub ((hsign_meas.add (hX_meas.const_smul s.lambda)).const_smul s.eta)
  have hsign_fin :
      (Set.range (fun ω : Ω => coordinateSign (V ω))).Finite := by
    refine coordinateSign_range_finite.subset ?_
    rintro z ⟨ω, rfl⟩
    exact ⟨V ω, rfl⟩
  have hkey_fin :
      (Set.range (fun ω : Ω => (X ω, coordinateSign (V ω)))).Finite := by
    refine (hX_fin.prod hsign_fin).subset ?_
    rintro z ⟨ω, rfl⟩
    exact ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩
  have hnext_fin :
      (Set.range
        (fun ω : Ω => X ω - s.eta • (coordinateSign (V ω) + s.lambda • X ω))).Finite := by
    refine Set.Finite.range_of_finite_range_fiber_const
      (Y := fun ω : Ω => (X ω, coordinateSign (V ω))) hkey_fin ?_
    intro ω ω' hkey
    have hXeq : X ω = X ω' := congrArg Prod.fst hkey
    have hSeq : coordinateSign (V ω) = coordinateSign (V ω') := congrArg Prod.snd hkey
    simp [hXeq, hSeq]
  exact ⟨hnext_meas, hnext_fin⟩

private theorem lion_process_x_finiteRange_and_state_integrable {d : ℕ}
    {s : Setup d} (hunb : s.OracleUnbiased) :
    ∀ n : ℕ,
      (letI := s.sampleMeasurable;
        AEMeasurable (fun ω : Run s => x s (n + 1) ω) (Run.law s) ∧
          (Set.range (fun ω : Run s => x s (n + 1) ω)).Finite ∧
            Integrable (fun ω : Run s => m s (n + 1) ω) (Run.law s) ∧
              Integrable (fun ω : Run s => v s (n + 1) ω) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  intro n
  induction n with
  | zero =>
      have hx_const : (fun ω : Run s => x s (0 + 1) ω) = fun _ω : Run s => s.x1 := by
        funext ω
        simp [x, stateAt]
      have hx_meas : AEMeasurable (fun ω : Run s => x s (0 + 1) ω) (Run.law s) := by
        rw [hx_const]
        exact aemeasurable_const
      have hx_fin : (Set.range (fun ω : Run s => x s (0 + 1) ω)).Finite := by
        rw [hx_const]
        exact Set.finite_range_const
      have hg1 := sampledGradient_fixed_integrable_from_oracleUnbiased (s := s) 1 s.x1 hunb
      have hm_int : Integrable (fun ω : Run s => m s (0 + 1) ω) (Run.law s) := by
        simpa [m, stateAt] using hg1
      have hv_int : Integrable (fun ω : Run s => v s (0 + 1) ω) (Run.law s) := by
        simpa [v, stateAt] using hg1
      exact ⟨hx_meas, hx_fin, hm_int, hv_int⟩
  | succ n ih =>
      obtain ⟨hx_meas, hx_fin, hm_int, hv_int⟩ := ih
      have hm_int' : Integrable (fun ω : Run s => m s (n + 1) ω) (Run.law s) := hm_int
      have hv_int' : Integrable (fun ω : Run s => v s (n + 1) ω) (Run.law s) := hv_int
      have hnext :=
        nextX_regularity_of_x_finiteRange_and_v_integrable (s := s)
          (X := fun ω : Run s => x s (n + 1) ω)
          (V := fun ω : Run s => v s (n + 1) ω)
          hx_meas hx_fin hv_int'
      have hx_eq :
          (fun ω : Run s => x s (Nat.succ n + 1) ω) =
            fun ω : Run s =>
              x s (n + 1) ω -
                s.eta • (coordinateSign (v s (n + 1) ω) + s.lambda • x s (n + 1) ω) := by
        funext ω
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          (x_succ_eq_update s (t := n + 1) (Nat.succ_pos n) ω)
      have hx_next_meas :
          AEMeasurable (fun ω : Run s => x s (Nat.succ n + 1) ω) (Run.law s) := by
        rw [hx_eq]
        exact hnext.1
      have hx_next_fin :
          (Set.range (fun ω : Run s => x s (Nat.succ n + 1) ω)).Finite := by
        rw [hx_eq]
        exact hnext.2
      have hg_next_sampled :
          Integrable
            (fun ω : Run s => sampledGradient s (Nat.succ n + 1) (x s (Nat.succ n + 1) ω) ω)
            (Run.law s) :=
        sampledGradient_integrable_of_finiteRange_query (s := s) (t := Nat.succ n + 1)
          (q := fun ω : Run s => x s (Nat.succ n + 1) ω)
          hx_next_meas hx_next_fin hunb
      have hG_next :
          Integrable (fun ω : Run s => G s (Nat.succ n + 1) ω) (Run.law s) := by
        simpa [G] using hg_next_sampled
      have hm_expr :
          Integrable
            (fun ω : Run s =>
              (1 - s.beta2) • m s (n + 1) ω + s.beta2 • G s (Nat.succ n + 1) ω)
            (Run.law s) :=
        (MeasureTheory.Integrable.smul (1 - s.beta2) hm_int').add
          (MeasureTheory.Integrable.smul s.beta2 hG_next)
      have hm_next :
          Integrable (fun ω : Run s => m s (Nat.succ n + 1) ω) (Run.law s) := by
        refine hm_expr.congr (MeasureTheory.ae_of_all (Run.law s) ?_)
        intro ω
        symm
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          (m_succ_eq_original_momentum s (t := n + 1) (Nat.succ_pos n) ω)
      have hv_expr :
          Integrable
            (fun ω : Run s =>
              (1 - s.beta1) • m s (n + 1) ω + s.beta1 • G s (Nat.succ n + 1) ω)
            (Run.law s) :=
        (MeasureTheory.Integrable.smul (1 - s.beta1) hm_int').add
          (MeasureTheory.Integrable.smul s.beta1 hG_next)
      have hv_next :
          Integrable (fun ω : Run s => v s (Nat.succ n + 1) ω) (Run.law s) := by
        refine hv_expr.congr (MeasureTheory.ae_of_all (Run.law s) ?_)
        intro ω
        symm
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          (v_succ_eq_lookahead_momentum s (t := n + 1) (Nat.succ_pos n) ω)
      exact ⟨hx_next_meas, hx_next_fin, hm_next, hv_next⟩

private theorem lion_momentum_sq_integrable {d : ℕ}
    {s : Setup d} (hunb : s.OracleUnbiased) (hnoise : s.OracleBoundedNoise) :
    ∀ n : ℕ,
      (letI := s.sampleMeasurable;
        Integrable (fun ω : Run s => ‖m s (n + 1) ω‖ ^ 2) (Run.law s) ∧
          Integrable (fun ω : Run s => ‖v s (n + 1) ω‖ ^ 2) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  intro n
  induction n with
  | zero =>
      have hg1 :
          Integrable
            (fun ω : Run s => ‖sampledGradient s 1 ((fun _ω : Run s => s.x1) ω) ω‖ ^ 2)
            (Run.law s) :=
        sampledGradient_sq_integrable_of_finiteRange_query (s := s) (t := 1)
          (q := fun _ω : Run s => s.x1) aemeasurable_const
          Set.finite_range_const hunb hnoise
      have hm1 : Integrable (fun ω : Run s => ‖m s (0 + 1) ω‖ ^ 2) (Run.law s) := by
        simpa [m, stateAt] using hg1
      have hv1 : Integrable (fun ω : Run s => ‖v s (0 + 1) ω‖ ^ 2) (Run.law s) := by
        simpa [v, stateAt] using hg1
      exact ⟨hm1, hv1⟩
  | succ n ih =>
      obtain ⟨hm_sq, _hv_sq⟩ := ih
      obtain ⟨_hx_meas, _hx_fin, hm_int, _hv_int⟩ :=
        lion_process_x_finiteRange_and_state_integrable (s := s) hunb n
      obtain ⟨hx_next_meas, hx_next_fin, _hm_next_int, _hv_next_int⟩ :=
        lion_process_x_finiteRange_and_state_integrable (s := s) hunb (Nat.succ n)
      have hg_next_sampled_sq :
          Integrable
            (fun ω : Run s =>
              ‖sampledGradient s (Nat.succ n + 1) (x s (Nat.succ n + 1) ω) ω‖ ^ 2)
            (Run.law s) :=
        sampledGradient_sq_integrable_of_finiteRange_query (s := s)
          (t := Nat.succ n + 1) (q := fun ω : Run s => x s (Nat.succ n + 1) ω)
          hx_next_meas hx_next_fin hunb hnoise
      have hG_next_sq :
          Integrable (fun ω : Run s => ‖G s (Nat.succ n + 1) ω‖ ^ 2) (Run.law s) := by
        simpa [G] using hg_next_sampled_sq
      have hg_next_sampled_int :
          Integrable
            (fun ω : Run s =>
              sampledGradient s (Nat.succ n + 1) (x s (Nat.succ n + 1) ω) ω)
            (Run.law s) :=
        sampledGradient_integrable_of_finiteRange_query (s := s)
          (t := Nat.succ n + 1) (q := fun ω : Run s => x s (Nat.succ n + 1) ω)
          hx_next_meas hx_next_fin hunb
      have hG_next_int :
          Integrable (fun ω : Run s => G s (Nat.succ n + 1) ω) (Run.law s) := by
        simpa [G] using hg_next_sampled_int
      have hm_expr_sq :
          Integrable
            (fun ω : Run s =>
              ‖(1 - s.beta2) • m s (n + 1) ω +
                  s.beta2 • G s (Nat.succ n + 1) ω‖ ^ 2)
            (Run.law s) := by
        refine integrable_sq_norm_add ?_ ?_ ?_ ?_
        · exact (hm_int.aestronglyMeasurable.const_smul (1 - s.beta2))
        · exact (hG_next_int.aestronglyMeasurable.const_smul s.beta2)
        · exact integrable_sq_norm_const_smul (1 - s.beta2) hm_int.aestronglyMeasurable hm_sq
        · exact integrable_sq_norm_const_smul s.beta2 hG_next_int.aestronglyMeasurable hG_next_sq
      have hm_next_sq :
          Integrable (fun ω : Run s => ‖m s (Nat.succ n + 1) ω‖ ^ 2) (Run.law s) := by
        refine hm_expr_sq.congr (MeasureTheory.ae_of_all (Run.law s) ?_)
        intro ω
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          congrArg (fun z : Point d => ‖z‖)
            (m_succ_eq_original_momentum s (t := n + 1) (Nat.succ_pos n) ω).symm
      have hv_expr_sq :
          Integrable
            (fun ω : Run s =>
              ‖(1 - s.beta1) • m s (n + 1) ω +
                  s.beta1 • G s (Nat.succ n + 1) ω‖ ^ 2)
            (Run.law s) := by
        refine integrable_sq_norm_add ?_ ?_ ?_ ?_
        · exact (hm_int.aestronglyMeasurable.const_smul (1 - s.beta1))
        · exact (hG_next_int.aestronglyMeasurable.const_smul s.beta1)
        · exact integrable_sq_norm_const_smul (1 - s.beta1) hm_int.aestronglyMeasurable hm_sq
        · exact integrable_sq_norm_const_smul s.beta1 hG_next_int.aestronglyMeasurable hG_next_sq
      have hv_next_sq :
          Integrable (fun ω : Run s => ‖v s (Nat.succ n + 1) ω‖ ^ 2) (Run.law s) := by
        refine hv_expr_sq.congr (MeasureTheory.ae_of_all (Run.law s) ?_)
        intro ω
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          congrArg (fun z : Point d => ‖z‖)
          (v_succ_eq_lookahead_momentum s (t := n + 1) (Nat.succ_pos n) ω).symm
      exact ⟨hm_next_sq, hv_next_sq⟩

private theorem lion_eq6_direction_sq_integrable {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta1) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  obtain ⟨hx_t_meas0, hx_t_fin0, hm_t_int0, _hv_t_int0⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
  have hx_t_meas :
      AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
    simpa [Nat.sub_add_cancel ht] using hx_t_meas0
  have hx_t_fin :
      (Set.range (fun ω : Run s => x s t ω)).Finite := by
    simpa [Nat.sub_add_cancel ht] using hx_t_fin0
  have hm_t_int :
      Integrable (fun ω : Run s => m s t ω) (Run.law s) := by
    simpa [Nat.sub_add_cancel ht] using hm_t_int0
  obtain ⟨hm_t_sq0, _hv_t_sq0⟩ :=
    lion_momentum_sq_integrable (s := s) h.oracle_unbiased h.oracle_bounded_noise (t - 1)
  have hm_t_sq :
      Integrable (fun ω : Run s => ‖m s t ω‖ ^ 2) (Run.law s) := by
    simpa [Nat.sub_add_cancel ht] using hm_t_sq0
  obtain ⟨hx_next_meas, hx_next_fin, _hm_next_int, _hv_next_int⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased t
  have hgrad_t_int :
      Integrable (fun ω : Run s => s.trueGradient (x s t ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_t_meas hx_t_fin
  have hgrad_t_sq :
      Integrable (fun ω : Run s => ‖s.trueGradient (x s t ω)‖ ^ 2) (Run.law s) :=
    trueGradient_sq_integrable_of_x_finiteRange (s := s) hx_t_meas hx_t_fin
  have hgrad_next_int :
      Integrable (fun ω : Run s => s.trueGradient (x s (t + 1) ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_next_meas hx_next_fin
  have hgrad_next_sq :
      Integrable (fun ω : Run s => ‖s.trueGradient (x s (t + 1) ω)‖ ^ 2) (Run.law s) :=
    trueGradient_sq_integrable_of_x_finiteRange (s := s) hx_next_meas hx_next_fin
  have hfirst_sq :
      Integrable
        (fun ω : Run s => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        (Run.law s) :=
    integrable_sq_norm_sub hm_t_int.aestronglyMeasurable
      hgrad_t_int.aestronglyMeasurable hm_t_sq hgrad_t_sq
  have hsecond_sq :
      Integrable
        (fun ω : Run s =>
          ‖s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)‖ ^ 2)
        (Run.law s) :=
    integrable_sq_norm_sub hgrad_t_int.aestronglyMeasurable
      hgrad_next_int.aestronglyMeasurable hgrad_t_sq hgrad_next_sq
  have hsum_sq :
      Integrable
        (fun ω : Run s =>
          ‖m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))‖ ^ 2)
        (Run.law s) :=
    integrable_sq_norm_add
      (hm_t_int.sub hgrad_t_int).aestronglyMeasurable
      (hgrad_t_int.sub hgrad_next_int).aestronglyMeasurable
      hfirst_sq hsecond_sq
  exact
    integrable_sq_norm_const_smul (1 - s.beta1)
      (hm_t_int.sub hgrad_t_int |>.add (hgrad_t_int.sub hgrad_next_int)).aestronglyMeasurable
      hsum_sq

private theorem lion_eq6_direction_sq_integrable_beta2 {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta2) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  obtain ⟨hx_t_meas0, hx_t_fin0, hm_t_int0, _hv_t_int0⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
  have hx_t_meas :
      AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
    simpa [Nat.sub_add_cancel ht] using hx_t_meas0
  have hx_t_fin :
      (Set.range (fun ω : Run s => x s t ω)).Finite := by
    simpa [Nat.sub_add_cancel ht] using hx_t_fin0
  have hm_t_int :
      Integrable (fun ω : Run s => m s t ω) (Run.law s) := by
    simpa [Nat.sub_add_cancel ht] using hm_t_int0
  obtain ⟨hm_t_sq0, _hv_t_sq0⟩ :=
    lion_momentum_sq_integrable (s := s) h.oracle_unbiased h.oracle_bounded_noise (t - 1)
  have hm_t_sq :
      Integrable (fun ω : Run s => ‖m s t ω‖ ^ 2) (Run.law s) := by
    simpa [Nat.sub_add_cancel ht] using hm_t_sq0
  obtain ⟨hx_next_meas, hx_next_fin, _hm_next_int, _hv_next_int⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased t
  have hgrad_t_int :
      Integrable (fun ω : Run s => s.trueGradient (x s t ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_t_meas hx_t_fin
  have hgrad_t_sq :
      Integrable (fun ω : Run s => ‖s.trueGradient (x s t ω)‖ ^ 2) (Run.law s) :=
    trueGradient_sq_integrable_of_x_finiteRange (s := s) hx_t_meas hx_t_fin
  have hgrad_next_int :
      Integrable (fun ω : Run s => s.trueGradient (x s (t + 1) ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_next_meas hx_next_fin
  have hgrad_next_sq :
      Integrable (fun ω : Run s => ‖s.trueGradient (x s (t + 1) ω)‖ ^ 2)
        (Run.law s) :=
    trueGradient_sq_integrable_of_x_finiteRange (s := s) hx_next_meas hx_next_fin
  have hfirst_sq :
      Integrable
        (fun ω : Run s => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        (Run.law s) :=
    integrable_sq_norm_sub hm_t_int.aestronglyMeasurable
      hgrad_t_int.aestronglyMeasurable hm_t_sq hgrad_t_sq
  have hsecond_sq :
      Integrable
        (fun ω : Run s =>
          ‖s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)‖ ^ 2)
        (Run.law s) :=
    integrable_sq_norm_sub hgrad_t_int.aestronglyMeasurable
      hgrad_next_int.aestronglyMeasurable hgrad_t_sq hgrad_next_sq
  have hsum_sq :
      Integrable
        (fun ω : Run s =>
          ‖m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))‖ ^ 2)
        (Run.law s) :=
    integrable_sq_norm_add
      (hm_t_int.sub hgrad_t_int).aestronglyMeasurable
      (hgrad_t_int.sub hgrad_next_int).aestronglyMeasurable
      hfirst_sq hsecond_sq
  exact
    integrable_sq_norm_const_smul (1 - s.beta2)
      (hm_t_int.sub hgrad_t_int |>.add (hgrad_t_int.sub hgrad_next_int)).aestronglyMeasurable
      hsum_sq

private theorem run_prefix_measurable_indep_sampleAt_succ {d : ℕ}
    {s : Setup d} {β : Type*} [MeasurableSpace β] {t : ℕ} {q : Run s → β}
    (hq :
      (letI := s.sampleMeasurable;
        Measurable[(SOptLib.filtration (fun n (ω : Run s) => ω n)
          (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).seq t] q)) :
    (letI := s.sampleMeasurable;
      ProbabilityTheory.IndepFun q (Run.sampleAt s (t + 1)) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  let ξ : ℕ → Run s → s.Sample := fun n ω => ω n
  have hξ_meas : ∀ n, Measurable (ξ n) := by
    intro n
    exact measurable_pi_apply n
  have hξ_iIndep : ProbabilityTheory.iIndepFun ξ (Run.law s) := by
    simpa [Run.law, ξ] using SOptLib.iidStreamLaw_iIndepFun_eval (mu := s.oracleLaw)
  have hq' :
      Measurable[(SOptLib.filtration ξ hξ_meas).seq t] q := by
    simpa [ξ] using hq
  have hindep :=
    ProbabilityTheory.iIndepFun.indepFun_prefixMeasurable_future
      ξ hξ_meas hξ_iIndep (wt := q) (n := t) (i := t) hq' le_rfl
  simpa [ξ, Run.sampleAt] using hindep

/-- Product-law regularity for the oracle value when the random query has finite
support.  This is the uncentered companion needed to build prefix representatives
for past sampled gradients without assuming joint oracle measurability. -/
private theorem oracleValue_prod_aestronglyMeasurable_of_finite_query {d : ℕ}
    {s : Setup d} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {q : Ω → Point d}
    (hq : AEMeasurable q μ)
    (hq_fin : (Set.range q).Finite)
    (hfixed : ∀ z : Point d, Integrable (fun ξ => s.oracleValue z ξ) s.oracleLaw) :
    (letI := s.sampleMeasurable;
      AEStronglyMeasurable
        (fun p : Point d × s.Sample => s.oracleValue p.1 p.2)
        ((Measure.map q μ).prod s.oracleLaw)) := by
  classical
  letI := s.sampleMeasurable
  let S : Finset (Point d) := hq_fin.toFinset
  let μq : Measure (Point d) := Measure.map q μ
  let oracleRep : Point d → s.Sample → Point d :=
    fun z => ((hfixed z).aestronglyMeasurable).mk (fun ξ => s.oracleValue z ξ)
  let approx : Point d × s.Sample → Point d :=
    fun p =>
      S.sum fun z =>
        ({p : Point d × s.Sample | p.1 = z}.indicator
          (fun p => oracleRep z p.2) p)
  have happrox_aesm : AEStronglyMeasurable approx (μq.prod s.oracleLaw) := by
    refine Finset.aestronglyMeasurable_fun_sum S ?_
    intro z hz
    have hbase :
        AEStronglyMeasurable
          (fun p : Point d × s.Sample => oracleRep z p.2)
          (μq.prod s.oracleLaw) := by
      exact (((hfixed z).aestronglyMeasurable).stronglyMeasurable_mk.comp_measurable
        measurable_snd).aestronglyMeasurable
    have hset : MeasurableSet ({p : Point d × s.Sample | p.1 = z}) := by
      exact measurable_fst (measurableSet_singleton z)
    exact hbase.indicator hset
  refine happrox_aesm.congr ?_
  have hsnd_ac :
      Measure.map Prod.snd (μq.prod s.oracleLaw) ≪ s.oracleLaw := by
    rw [Measure.map_snd_prod]
    exact Measure.AbsolutelyContinuous.rfl.smul_left (μq Set.univ)
  have hrep_all :
      ∀ᵐ p ∂μq.prod s.oracleLaw, ∀ z ∈ S, s.oracleValue z p.2 = oracleRep z p.2 := by
    rw [Finset.eventually_all]
    intro z
    intro _hz
    have hz_ae_sample : ∀ᵐ ξ ∂s.oracleLaw, s.oracleValue z ξ = oracleRep z ξ :=
      ((hfixed z).aestronglyMeasurable).ae_eq_mk
    exact ae_of_ae_map measurable_snd.aemeasurable (hsnd_ac.ae_le hz_ae_sample)
  have hsupport_q : ∀ᵐ y ∂μq, y ∈ S := by
    rw [MeasureTheory.ae_map_iff hq]
    · exact ae_of_all _ fun ω => by
        simp [S, Set.Finite.mem_toFinset]
    · exact S.measurableSet
  have hfst_ac : Measure.map Prod.fst (μq.prod s.oracleLaw) ≪ μq := by
    rw [Measure.map_fst_prod]
    exact Measure.AbsolutelyContinuous.rfl.smul_left (s.oracleLaw Set.univ)
  have hsupport : ∀ᵐ p ∂μq.prod s.oracleLaw, p.1 ∈ S :=
    ae_of_ae_map measurable_fst.aemeasurable (hfst_ac.ae_le hsupport_q)
  filter_upwards [hsupport, hrep_all] with p hpS hpRep
  dsimp [approx, oracleRep]
  symm
  rw [Finset.sum_eq_single p.1]
  · rw [Set.indicator_of_mem]
    · exact hpRep p.1 hpS
    · rfl
  · intro z _hz hzne
    have hpnot : p ∉ ({p : Point d × s.Sample | p.1 = z}) := by
      intro hp
      exact hzne (by simpa using hp.symm)
    simp [Set.indicator_of_notMem hpnot]
  · intro hnot
    exact False.elim (hnot hpS)

/-- Evaluate a finite-range adapted query at the next sample using a
prefix-measurable representative of the sampled oracle value. -/
private theorem sampledGradient_prefix_measurable_rep_of_finite_query {d : ℕ}
    {s : Setup d} {t : ℕ} {query queryRep : Run s → Point d}
    (hqueryRep_meas :
      (letI := s.sampleMeasurable;
        Measurable[(SOptLib.filtration (fun n (ω : Run s) => ω n)
          (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).seq t]
          queryRep))
    (hquery_ae : query =ᵐ[Run.law s] queryRep)
    (hqueryRep_fin : (Set.range queryRep).Finite)
    (hunb : s.OracleUnbiased) :
    (letI := s.sampleMeasurable;
      ∃ gRep : Run s → Point d,
        Measurable[(SOptLib.filtration (fun n (ω : Run s) => ω n)
          (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).seq (t + 1)]
          gRep ∧
          (fun ω : Run s => sampledGradient s (t + 1) (query ω) ω) =ᵐ[
            Run.law s] gRep) := by
  classical
  letI := s.sampleMeasurable
  let ξ : ℕ → Run s → s.Sample := fun n ω => ω n
  have hξ_meas : ∀ n, Measurable (ξ n) := by
    intro n
    exact measurable_pi_apply n
  let pref := SOptLib.filtration ξ hξ_meas
  have hqueryRep_meas' : Measurable[pref.seq t] queryRep := by
    simpa [pref, ξ] using hqueryRep_meas
  have hqueryRep_next : Measurable[pref.seq (t + 1)] queryRep :=
    hqueryRep_meas'.mono (pref.mono (Nat.le_succ t)) le_rfl
  have hsample_next : Measurable[pref.seq (t + 1)] (Run.sampleAt s (t + 1)) := by
    simpa [pref, ξ, Run.sampleAt] using
      (SOptLib.measurable_sample_of_lt_prefixFiltration ξ hξ_meas
        (show t < t + 1 from Nat.lt_succ_self t))
  have htarget_ambient : pref.seq (t + 1) ≤ (by infer_instance : MeasurableSpace (Run s)) :=
    pref.le' (t + 1)
  have hqueryRep_aemeas : AEMeasurable queryRep (Run.law s) :=
    (hqueryRep_meas'.mono (pref.le' t) le_rfl).aemeasurable
  have hindep :
      ProbabilityTheory.IndepFun queryRep (Run.sampleAt s (t + 1)) (Run.law s) := by
    simpa [pref, ξ] using
      (run_prefix_measurable_indep_sampleAt_succ (s := s) (t := t)
        (q := queryRep) (by simpa [pref, ξ] using hqueryRep_meas'))
  have hsample_law :
      Measure.map (Run.sampleAt s (t + 1)) (Run.law s) = s.oracleLaw :=
    Run.map_sampleAt_law s (t + 1)
  have hkernel0 :
      AEStronglyMeasurable
        (fun p : Point d × s.Sample => s.oracleValue p.1 p.2)
        ((Measure.map queryRep (Run.law s)).prod s.oracleLaw) :=
    oracleValue_prod_aestronglyMeasurable_of_finite_query
      (s := s) (μ := Run.law s) (q := queryRep)
      hqueryRep_aemeas hqueryRep_fin
      (fun z => Setup.oracleUnbiased_integrable hunb z)
  have hkernel :
      AEStronglyMeasurable (Function.uncurry (fun z ξ => s.oracleValue z ξ))
        ((Measure.map queryRep (Run.law s)).prod
          (Measure.map (Run.sampleAt s (t + 1)) (Run.law s))) := by
    rw [hsample_law]
    simpa [Function.uncurry] using hkernel0
  obtain ⟨gRep, hgRep_meas, hg_ae⟩ :=
    ae_eq_measurable_comp_of_indep_product_aestronglyMeasurable
      (mTarget := pref.seq (t + 1))
      (query := query) (queryRep := queryRep)
      (sample := Run.sampleAt s (t + 1))
      (kernel := fun z ξ => s.oracleValue z ξ)
      (μ := Run.law s)
      (by infer_instance) (by infer_instance)
      htarget_ambient hqueryRep_next hsample_next hquery_ae hindep hkernel
  refine ⟨gRep, ?_, ?_⟩
  · simpa [pref, ξ] using hgRep_meas.measurable
  · simpa [sampledGradient] using hg_ae

/-- Compose an arbitrary observable with a finite-range measurable key. -/
private theorem measurable_comp_of_finite_range_key
    {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] {Y : Ω → α}
    (hY : @Measurable Ω α mΩ (by infer_instance) Y)
    (hfin : (Set.range Y).Finite) (φ : α → β) :
    @Measurable Ω β mΩ (by infer_instance) (fun ω => φ (Y ω)) := by
  letI : MeasurableSpace Ω := mΩ
  exact measurable_of_finite_range_fiber_const hY hfin (fun _ω _ω' hYY => congrArg φ hYY)

/-- Prefix-measurable representatives for the Lion state at paper time `n + 1`.
The iterate component is finite-range; the momentum components are represented
using past sampled-gradient representatives. -/
private theorem lion_state_prefix_measurable_reps {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} (h : FiniteHorizonAssumptions s T) :
    ∀ n : ℕ,
      (letI := s.sampleMeasurable;
        ∃ xRep mRep vRep : Run s → Point d,
          Measurable[(SOptLib.filtration (fun k (ω : Run s) => ω k)
            (fun k => (measurable_pi_apply k : Measurable (fun ω : Run s => ω k)))).seq
              (n + 1)] xRep ∧
          Measurable[(SOptLib.filtration (fun k (ω : Run s) => ω k)
            (fun k => (measurable_pi_apply k : Measurable (fun ω : Run s => ω k)))).seq
              (n + 1)] mRep ∧
          Measurable[(SOptLib.filtration (fun k (ω : Run s) => ω k)
            (fun k => (measurable_pi_apply k : Measurable (fun ω : Run s => ω k)))).seq
              (n + 1)] vRep ∧
          (fun ω : Run s => x s (n + 1) ω) =ᵐ[Run.law s] xRep ∧
          (fun ω : Run s => m s (n + 1) ω) =ᵐ[Run.law s] mRep ∧
          (fun ω : Run s => v s (n + 1) ω) =ᵐ[Run.law s] vRep ∧
          (Set.range xRep).Finite) := by
  classical
  letI := s.sampleMeasurable
  intro n
  induction n with
  | zero =>
      obtain ⟨gRep, hgRep_meas, hgRep_ae⟩ :=
        sampledGradient_prefix_measurable_rep_of_finite_query
          (s := s) (t := 0)
          (query := fun _ω : Run s => s.x1)
          (queryRep := fun _ω : Run s => s.x1)
          (by simpa using
            (measurable_const :
              Measurable[(SOptLib.filtration (fun k (ω : Run s) => ω k)
                (fun k => (measurable_pi_apply k : Measurable (fun ω : Run s => ω k)))).seq 0]
                (fun _ω : Run s => s.x1)))
          (Filter.EventuallyEq.rfl)
          Set.finite_range_const
          h.oracle_unbiased
      refine ⟨fun _ω : Run s => s.x1, gRep, gRep, ?_, hgRep_meas, hgRep_meas, ?_, ?_, ?_,
        Set.finite_range_const⟩
      · exact measurable_const
      · filter_upwards with ω
        simp [x, stateAt]
      · filter_upwards [hgRep_ae] with ω hω
        simpa [m, stateAt] using hω
      · filter_upwards [hgRep_ae] with ω hω
        simpa [v, stateAt] using hω
  | succ n ih =>
      obtain ⟨xRep, mRep, vRep, hxRep_meas, hmRep_meas, hvRep_meas,
        hxRep_ae, hmRep_ae, hvRep_ae, hxRep_fin⟩ := ih
      let ξ : ℕ → Run s → s.Sample := fun k ω => ω k
      let hξ_meas : ∀ k, Measurable (ξ k) := fun k => measurable_pi_apply k
      let pref := SOptLib.filtration ξ hξ_meas
      have hxRep_meas' : Measurable[pref.seq (n + 1)] xRep := by
        simpa [pref, ξ] using hxRep_meas
      have hmRep_meas' : Measurable[pref.seq (n + 1)] mRep := by
        simpa [pref, ξ] using hmRep_meas
      have hvRep_meas' : Measurable[pref.seq (n + 1)] vRep := by
        simpa [pref, ξ] using hvRep_meas
      let xNextRep : Run s → Point d :=
        fun ω => xRep ω - s.eta • (coordinateSign (vRep ω) + s.lambda • xRep ω)
      have hsignRep_meas :
          Measurable[pref.seq (n + 1)] (fun ω : Run s => coordinateSign (vRep ω)) :=
        coordinateSign_measurable.comp hvRep_meas'
      have hxNextRep_meas : Measurable[pref.seq (n + 1)] xNextRep := by
        exact hxRep_meas'.sub
          ((hsignRep_meas.add (hxRep_meas'.const_smul s.lambda)).const_smul s.eta)
      have hsignRep_fin :
          (Set.range (fun ω : Run s => coordinateSign (vRep ω))).Finite := by
        refine coordinateSign_range_finite.subset ?_
        rintro z ⟨ω, rfl⟩
        exact ⟨vRep ω, rfl⟩
      have hkey_fin :
          (Set.range (fun ω : Run s => (xRep ω, coordinateSign (vRep ω)))).Finite := by
        refine (hxRep_fin.prod hsignRep_fin).subset ?_
        rintro z ⟨ω, rfl⟩
        exact ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩
      have hxNextRep_fin : (Set.range xNextRep).Finite := by
        refine Set.Finite.range_of_finite_range_fiber_const
          (Y := fun ω : Run s => (xRep ω, coordinateSign (vRep ω))) hkey_fin ?_
        intro ω ω' hkey
        have hx_eq : xRep ω = xRep ω' := congrArg Prod.fst hkey
        have hs_eq : coordinateSign (vRep ω) = coordinateSign (vRep ω') := congrArg Prod.snd hkey
        simp [xNextRep, hx_eq, hs_eq]
      have hxNextRep_ae :
          (fun ω : Run s => x s (Nat.succ n + 1) ω) =ᵐ[Run.law s] xNextRep := by
        filter_upwards [hxRep_ae, hvRep_ae] with ω hxω hvω
        calc
          x s (Nat.succ n + 1) ω =
              x s (n + 1) ω -
                s.eta • (coordinateSign (v s (n + 1) ω) + s.lambda • x s (n + 1) ω) := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
              x_succ_eq_update s (t := n + 1) (Nat.succ_pos n) ω
          _ = xNextRep ω := by
            simp [xNextRep, hxω, hvω]
      obtain ⟨gRep, hgRep_meas, hgRep_ae⟩ :=
        sampledGradient_prefix_measurable_rep_of_finite_query
          (s := s) (t := n + 1)
          (query := fun ω : Run s => x s (Nat.succ n + 1) ω)
          (queryRep := xNextRep)
          (by simpa [pref, ξ] using hxNextRep_meas)
          hxNextRep_ae
          hxNextRep_fin
          h.oracle_unbiased
      have hmRep_next_meas : Measurable[pref.seq (n + 2)] mRep :=
        hmRep_meas'.mono (pref.mono (by omega : n + 1 ≤ n + 2)) le_rfl
      have hxNextRep_next_meas : Measurable[pref.seq (n + 2)] xNextRep :=
        hxNextRep_meas.mono (pref.mono (by omega : n + 1 ≤ n + 2)) le_rfl
      have hmNext_meas :
          Measurable[pref.seq (n + 2)]
            (fun ω : Run s => (1 - s.beta2) • mRep ω + s.beta2 • gRep ω) :=
        (hmRep_next_meas.const_smul (1 - s.beta2)).add (hgRep_meas.const_smul s.beta2)
      have hvNext_meas :
          Measurable[pref.seq (n + 2)]
            (fun ω : Run s => (1 - s.beta1) • mRep ω + s.beta1 • gRep ω) :=
        (hmRep_next_meas.const_smul (1 - s.beta1)).add (hgRep_meas.const_smul s.beta1)
      refine ⟨xNextRep,
        (fun ω : Run s => (1 - s.beta2) • mRep ω + s.beta2 • gRep ω),
        (fun ω : Run s => (1 - s.beta1) • mRep ω + s.beta1 • gRep ω),
        ?_, ?_, ?_, ?_, ?_, ?_, hxNextRep_fin⟩
      · simpa [pref, ξ, Nat.succ_eq_add_one, Nat.add_assoc] using hxNextRep_next_meas
      · simpa [pref, ξ, Nat.succ_eq_add_one, Nat.add_assoc] using hmNext_meas
      · simpa [pref, ξ, Nat.succ_eq_add_one, Nat.add_assoc] using hvNext_meas
      · exact hxNextRep_ae
      · filter_upwards [hmRep_ae, hgRep_ae] with ω hmω hgω
        calc
          m s (Nat.succ n + 1) ω =
              (1 - s.beta2) • m s (n + 1) ω + s.beta2 • G s (Nat.succ n + 1) ω := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
              m_succ_eq_original_momentum s (t := n + 1) (Nat.succ_pos n) ω
          _ = (1 - s.beta2) • mRep ω + s.beta2 • gRep ω := by
            simpa [G] using congrArg₂ HAdd.hAdd
              (congrArg ((· • ·) (1 - s.beta2)) hmω)
              (congrArg ((· • ·) s.beta2) hgω)
      · filter_upwards [hmRep_ae, hgRep_ae] with ω hmω hgω
        calc
          v s (Nat.succ n + 1) ω =
              (1 - s.beta1) • m s (n + 1) ω + s.beta1 • G s (Nat.succ n + 1) ω := by
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
              v_succ_eq_lookahead_momentum s (t := n + 1) (Nat.succ_pos n) ω
          _ = (1 - s.beta1) • mRep ω + s.beta1 • gRep ω := by
            simpa [G] using congrArg₂ HAdd.hAdd
              (congrArg ((· • ·) (1 - s.beta1)) hmω)
              (congrArg ((· • ·) s.beta1) hgω)

/-- Prefix-measurable a.e. representative for Appendix B Eq. (6)'s random
query and multiplier, just before the fresh sample `ξ_{t+1}` is drawn. -/
private theorem lion_eq6_query_direction_adapted_rep {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      ∃ qRep : Run s → Point d × Point d,
        Measurable[(SOptLib.filtration (fun n (ω : Run s) => ω n)
          (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).seq t]
          qRep ∧
          (fun ω : Run s =>
            (x s (t + 1) ω,
              (1 - s.beta1) •
                (m s t ω - s.trueGradient (x s t ω) +
                  (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))))) =ᵐ[
            Run.law s] qRep ∧
          (Set.range (fun ω : Run s => (qRep ω).1)).Finite ∧
          Integrable (fun ω : Run s => ‖(qRep ω).2‖ ^ 2) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  have hdir_sq :
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta1) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s) :=
    lion_eq6_direction_sq_integrable (s := s) (T := T) h ht
  obtain ⟨hx_next_aemeas, hx_next_fin, _hm_next_int, _hv_next_int⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased t
  let ξ : ℕ → Run s → s.Sample := fun n ω => ω n
  let hξ_meas : ∀ n, Measurable (ξ n) := fun n => measurable_pi_apply n
  let pref := SOptLib.filtration ξ hξ_meas
  obtain ⟨xRep, mRep, vRep, hxRep_meas0, hmRep_meas0, hvRep_meas0,
      hxRep_ae0, hmRep_ae0, hvRep_ae0, hxRep_fin⟩ :=
    lion_state_prefix_measurable_reps (s := s) (T := T) h (t - 1)
  have ht_sub : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hxRep_meas : Measurable[pref.seq t] xRep := by
    convert hxRep_meas0 using 1
    rw [ht_sub]
  have hmRep_meas : Measurable[pref.seq t] mRep := by
    convert hmRep_meas0 using 1
    rw [ht_sub]
  have hvRep_meas : Measurable[pref.seq t] vRep := by
    convert hvRep_meas0 using 1
    rw [ht_sub]
  have hxRep_ae : (fun ω : Run s => x s t ω) =ᵐ[Run.law s] xRep := by
    simpa [ht_sub] using hxRep_ae0
  have hmRep_ae : (fun ω : Run s => m s t ω) =ᵐ[Run.law s] mRep := by
    simpa [ht_sub] using hmRep_ae0
  have hvRep_ae : (fun ω : Run s => v s t ω) =ᵐ[Run.law s] vRep := by
    simpa [ht_sub] using hvRep_ae0
  let xNextRep : Run s → Point d :=
    fun ω => xRep ω - s.eta • (coordinateSign (vRep ω) + s.lambda • xRep ω)
  have hsignRep_meas : Measurable[pref.seq t] (fun ω : Run s => coordinateSign (vRep ω)) :=
    coordinateSign_measurable.comp hvRep_meas
  have hxNextRep_meas : Measurable[pref.seq t] xNextRep := by
    exact hxRep_meas.sub ((hsignRep_meas.add (hxRep_meas.const_smul s.lambda)).const_smul s.eta)
  have hsignRep_fin :
      (Set.range (fun ω : Run s => coordinateSign (vRep ω))).Finite := by
    refine coordinateSign_range_finite.subset ?_
    rintro z ⟨ω, rfl⟩
    exact ⟨vRep ω, rfl⟩
  have hkey_fin :
      (Set.range (fun ω : Run s => (xRep ω, coordinateSign (vRep ω)))).Finite := by
    refine (hxRep_fin.prod hsignRep_fin).subset ?_
    rintro z ⟨ω, rfl⟩
    exact ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩
  have hxNextRep_fin : (Set.range xNextRep).Finite := by
    refine Set.Finite.range_of_finite_range_fiber_const
      (Y := fun ω : Run s => (xRep ω, coordinateSign (vRep ω))) hkey_fin ?_
    intro ω ω' hkey
    have hx_eq : xRep ω = xRep ω' := congrArg Prod.fst hkey
    have hs_eq : coordinateSign (vRep ω) = coordinateSign (vRep ω') := congrArg Prod.snd hkey
    simp [xNextRep, hx_eq, hs_eq]
  have hxNextRep_ae : (fun ω : Run s => x s (t + 1) ω) =ᵐ[Run.law s] xNextRep := by
    filter_upwards [hxRep_ae, hvRep_ae] with ω hxω hvω
    calc
      x s (t + 1) ω =
          x s t ω - s.eta • (coordinateSign (v s t ω) + s.lambda • x s t ω) :=
        x_succ_eq_update s ht ω
      _ = xNextRep ω := by
        simp [xNextRep, hxω, hvω]
  have hgradRep_meas : Measurable[pref.seq t] (fun ω : Run s => s.trueGradient (xRep ω)) :=
    measurable_comp_of_finite_range_key hxRep_meas hxRep_fin s.trueGradient
  have hgradNextRep_meas :
      Measurable[pref.seq t] (fun ω : Run s => s.trueGradient (xNextRep ω)) :=
    measurable_comp_of_finite_range_key hxNextRep_meas hxNextRep_fin s.trueGradient
  let dirRep : Run s → Point d :=
    fun ω =>
      (1 - s.beta1) •
        (mRep ω - s.trueGradient (xRep ω) +
          (s.trueGradient (xRep ω) - s.trueGradient (xNextRep ω)))
  have hdirRep_meas : Measurable[pref.seq t] dirRep := by
    exact ((hmRep_meas.sub hgradRep_meas).add
      (hgradRep_meas.sub hgradNextRep_meas)).const_smul (1 - s.beta1)
  let qRep : Run s → Point d × Point d := fun ω => (xNextRep ω, dirRep ω)
  refine ⟨qRep, ?_, ?_, ?_, ?_⟩
  · simpa [pref, ξ, qRep] using hxNextRep_meas.prodMk hdirRep_meas
  · filter_upwards [hxNextRep_ae, hxRep_ae, hmRep_ae] with ω hxNextω hxω hmω
    simp [qRep, dirRep, hxNextω, hxω, hmω]
  · simpa [qRep] using hxNextRep_fin
  · have hnorm_ae :
        (fun ω : Run s =>
          ‖(1 - s.beta1) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2) =ᵐ[
          Run.law s] fun ω => ‖(qRep ω).2‖ ^ 2 := by
      filter_upwards [hxNextRep_ae, hxRep_ae, hmRep_ae] with ω hxNextω hxω hmω
      simp [qRep, dirRep, hxNextω, hxω, hmω]
    exact hdir_sq.congr hnorm_ae

/-- Prefix-measurable representative for the beta₂ direction in the "very similarly"
part of Appendix B's `m_{t+1}` estimator recursion. -/
private theorem lion_eq6_query_direction_adapted_rep_beta2 {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      ∃ qRep : Run s → Point d × Point d,
        Measurable[(SOptLib.filtration (fun n (ω : Run s) => ω n)
          (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).seq t]
          qRep ∧
          (fun ω : Run s =>
            (x s (t + 1) ω,
              (1 - s.beta2) •
                (m s t ω - s.trueGradient (x s t ω) +
                  (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))))) =ᵐ[
            Run.law s] qRep ∧
          (Set.range (fun ω : Run s => (qRep ω).1)).Finite ∧
          Integrable (fun ω : Run s => ‖(qRep ω).2‖ ^ 2) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  have hdir_sq :
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta2) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s) :=
    lion_eq6_direction_sq_integrable_beta2 (s := s) (T := T) h ht
  obtain ⟨hx_next_aemeas, hx_next_fin, _hm_next_int, _hv_next_int⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased t
  let ξ : ℕ → Run s → s.Sample := fun n ω => ω n
  let hξ_meas : ∀ n, Measurable (ξ n) := fun n => measurable_pi_apply n
  let pref := SOptLib.filtration ξ hξ_meas
  obtain ⟨xRep, mRep, vRep, hxRep_meas0, hmRep_meas0, hvRep_meas0,
      hxRep_ae0, hmRep_ae0, hvRep_ae0, hxRep_fin⟩ :=
    lion_state_prefix_measurable_reps (s := s) (T := T) h (t - 1)
  have ht_sub : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hxRep_meas : Measurable[pref.seq t] xRep := by
    convert hxRep_meas0 using 1
    rw [ht_sub]
  have hmRep_meas : Measurable[pref.seq t] mRep := by
    convert hmRep_meas0 using 1
    rw [ht_sub]
  have hvRep_meas : Measurable[pref.seq t] vRep := by
    convert hvRep_meas0 using 1
    rw [ht_sub]
  have hxRep_ae : (fun ω : Run s => x s t ω) =ᵐ[Run.law s] xRep := by
    simpa [ht_sub] using hxRep_ae0
  have hmRep_ae : (fun ω : Run s => m s t ω) =ᵐ[Run.law s] mRep := by
    simpa [ht_sub] using hmRep_ae0
  have hvRep_ae : (fun ω : Run s => v s t ω) =ᵐ[Run.law s] vRep := by
    simpa [ht_sub] using hvRep_ae0
  let xNextRep : Run s → Point d :=
    fun ω => xRep ω - s.eta • (coordinateSign (vRep ω) + s.lambda • xRep ω)
  have hsignRep_meas : Measurable[pref.seq t] (fun ω : Run s => coordinateSign (vRep ω)) :=
    coordinateSign_measurable.comp hvRep_meas
  have hxNextRep_meas : Measurable[pref.seq t] xNextRep := by
    exact hxRep_meas.sub ((hsignRep_meas.add (hxRep_meas.const_smul s.lambda)).const_smul s.eta)
  have hsignRep_fin :
      (Set.range (fun ω : Run s => coordinateSign (vRep ω))).Finite := by
    refine coordinateSign_range_finite.subset ?_
    rintro z ⟨ω, rfl⟩
    exact ⟨vRep ω, rfl⟩
  have hkey_fin :
      (Set.range (fun ω : Run s => (xRep ω, coordinateSign (vRep ω)))).Finite := by
    refine (hxRep_fin.prod hsignRep_fin).subset ?_
    rintro z ⟨ω, rfl⟩
    exact ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩
  have hxNextRep_fin : (Set.range xNextRep).Finite := by
    refine Set.Finite.range_of_finite_range_fiber_const
      (Y := fun ω : Run s => (xRep ω, coordinateSign (vRep ω))) hkey_fin ?_
    intro ω ω' hkey
    have hx_eq : xRep ω = xRep ω' := congrArg Prod.fst hkey
    have hs_eq : coordinateSign (vRep ω) = coordinateSign (vRep ω') := congrArg Prod.snd hkey
    simp [xNextRep, hx_eq, hs_eq]
  have hxNextRep_ae : (fun ω : Run s => x s (t + 1) ω) =ᵐ[Run.law s] xNextRep := by
    filter_upwards [hxRep_ae, hvRep_ae] with ω hxω hvω
    calc
      x s (t + 1) ω =
          x s t ω - s.eta • (coordinateSign (v s t ω) + s.lambda • x s t ω) :=
        x_succ_eq_update s ht ω
      _ = xNextRep ω := by
        simp [xNextRep, hxω, hvω]
  have hgradRep_meas : Measurable[pref.seq t] (fun ω : Run s => s.trueGradient (xRep ω)) :=
    measurable_comp_of_finite_range_key hxRep_meas hxRep_fin s.trueGradient
  have hgradNextRep_meas :
      Measurable[pref.seq t] (fun ω : Run s => s.trueGradient (xNextRep ω)) :=
    measurable_comp_of_finite_range_key hxNextRep_meas hxNextRep_fin s.trueGradient
  let dirRep : Run s → Point d :=
    fun ω =>
      (1 - s.beta2) •
        (mRep ω - s.trueGradient (xRep ω) +
          (s.trueGradient (xRep ω) - s.trueGradient (xNextRep ω)))
  have hdirRep_meas : Measurable[pref.seq t] dirRep := by
    exact ((hmRep_meas.sub hgradRep_meas).add
      (hgradRep_meas.sub hgradNextRep_meas)).const_smul (1 - s.beta2)
  let qRep : Run s → Point d × Point d := fun ω => (xNextRep ω, dirRep ω)
  refine ⟨qRep, ?_, ?_, ?_, ?_⟩
  · simpa [pref, ξ, qRep] using hxNextRep_meas.prodMk hdirRep_meas
  · filter_upwards [hxNextRep_ae, hxRep_ae, hmRep_ae] with ω hxNextω hxω hmω
    simp [qRep, dirRep, hxNextω, hxω, hmω]
  · simpa [qRep] using hxNextRep_fin
  · have hnorm_ae :
        (fun ω : Run s =>
          ‖(1 - s.beta2) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2) =ᵐ[
          Run.law s] fun ω => ‖(qRep ω).2‖ ^ 2 := by
      filter_upwards [hxNextRep_ae, hxRep_ae, hmRep_ae] with ω hxNextω hxω hmω
      simp [qRep, dirRep, hxNextω, hxω, hmω]
    exact hdir_sq.congr hnorm_ae

/-- Product-law regularity for the centered oracle residual when the random
query's first coordinate has finite support. -/
private theorem oracle_residual_prod_aestronglyMeasurable_of_finite_first_query {d : ℕ}
    {s : Setup d} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {q : Ω → Point d × Point d}
    (hq : AEMeasurable q μ)
    (hq_first_fin : (Set.range (fun ω : Ω => (q ω).1)).Finite)
    (hfixed :
      ∀ z : Point d,
        Integrable (fun ξ => s.oracleValue z ξ - s.trueGradient z) s.oracleLaw ∧
          ∫ ξ, s.oracleValue z ξ - s.trueGradient z ∂s.oracleLaw = 0) :
    (letI := s.sampleMeasurable;
      AEStronglyMeasurable
        (fun p : (Point d × Point d) × s.Sample =>
          s.oracleValue p.1.1 p.2 - s.trueGradient p.1.1)
        ((Measure.map q μ).prod s.oracleLaw)) := by
  classical
  letI := s.sampleMeasurable
  let S : Finset (Point d) := hq_first_fin.toFinset
  let μq : Measure (Point d × Point d) := Measure.map q μ
  let residual : Point d → s.Sample → Point d :=
    fun z ξ => s.oracleValue z ξ - s.trueGradient z
  let residualRep : Point d → s.Sample → Point d :=
    fun z => ((hfixed z).1.aestronglyMeasurable).mk (residual z)
  let approx : (Point d × Point d) × s.Sample → Point d :=
    fun p =>
      S.sum fun z =>
        ({p : (Point d × Point d) × s.Sample | p.1.1 = z}.indicator
          (fun p => residualRep z p.2) p)
  have happrox_aesm : AEStronglyMeasurable approx (μq.prod s.oracleLaw) := by
    refine Finset.aestronglyMeasurable_fun_sum S ?_
    intro z hz
    have hbase :
        AEStronglyMeasurable
          (fun p : (Point d × Point d) × s.Sample => residualRep z p.2)
          (μq.prod s.oracleLaw) := by
      exact (((hfixed z).1.aestronglyMeasurable).stronglyMeasurable_mk.comp_measurable
        measurable_snd).aestronglyMeasurable
    have hset :
        MeasurableSet ({p : (Point d × Point d) × s.Sample | p.1.1 = z}) := by
      exact (measurable_fst.comp measurable_fst) (measurableSet_singleton z)
    exact hbase.indicator hset
  refine happrox_aesm.congr ?_
  have hsnd_ac :
      Measure.map Prod.snd (μq.prod s.oracleLaw) ≪ s.oracleLaw := by
    rw [Measure.map_snd_prod]
    exact Measure.AbsolutelyContinuous.rfl.smul_left (μq Set.univ)
  have hrep_all :
      ∀ᵐ p ∂μq.prod s.oracleLaw, ∀ z ∈ S, residual z p.2 = residualRep z p.2 := by
    rw [Finset.eventually_all]
    intro z
    intro _hz
    have hz_ae_sample :
        ∀ᵐ ξ ∂s.oracleLaw, residual z ξ = residualRep z ξ :=
      ((hfixed z).1.aestronglyMeasurable).ae_eq_mk
    exact ae_of_ae_map measurable_snd.aemeasurable (hsnd_ac.ae_le hz_ae_sample)
  have hsupport_q : ∀ᵐ y ∂μq, y.1 ∈ S := by
    rw [MeasureTheory.ae_map_iff hq]
    · exact ae_of_all _ fun ω => by
        simp [S, Set.Finite.mem_toFinset]
    · exact measurable_fst S.measurableSet
  have hfst_ac : Measure.map Prod.fst (μq.prod s.oracleLaw) ≪ μq := by
    rw [Measure.map_fst_prod]
    exact Measure.AbsolutelyContinuous.rfl.smul_left (s.oracleLaw Set.univ)
  have hsupport : ∀ᵐ p ∂μq.prod s.oracleLaw, p.1.1 ∈ S :=
    ae_of_ae_map measurable_fst.aemeasurable (hfst_ac.ae_le hsupport_q)
  filter_upwards [hsupport, hrep_all] with p hpS hpRep
  dsimp [approx, residual, residualRep]
  symm
  rw [Finset.sum_eq_single p.1.1]
  · rw [Set.indicator_of_mem]
    · exact hpRep p.1.1 hpS
    · rfl
  · intro z _hz hzne
    have hpnot : p ∉ ({p : (Point d × Point d) × s.Sample | p.1.1 = z}) := by
      intro hp
      exact hzne (by simpa using hp.symm)
    simp [Set.indicator_of_notMem hpnot]
  · intro hnot
    exact False.elim (hnot hpS)

private theorem oracle_residual_sq_prod_aestronglyMeasurable_of_finite_query {d : ℕ}
    {s : Setup d} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {q : Ω → Point d}
    (hq : AEMeasurable q μ)
    (hq_fin : (Set.range q).Finite)
    (hfixed :
      ∀ z : Point d,
        Integrable (fun ξ => ‖s.oracleValue z ξ - s.trueGradient z‖ ^ 2) s.oracleLaw) :
    (letI := s.sampleMeasurable;
      AEStronglyMeasurable
        (fun p : Point d × s.Sample =>
          ‖s.oracleValue p.1 p.2 - s.trueGradient p.1‖ ^ 2)
        ((Measure.map q μ).prod s.oracleLaw)) := by
  classical
  letI := s.sampleMeasurable
  let S : Finset (Point d) := hq_fin.toFinset
  let μq : Measure (Point d) := Measure.map q μ
  let residualSq : Point d → s.Sample → ℝ :=
    fun z ξ => ‖s.oracleValue z ξ - s.trueGradient z‖ ^ 2
  let residualSqRep : Point d → s.Sample → ℝ :=
    fun z => ((hfixed z).aestronglyMeasurable).mk (residualSq z)
  let approx : Point d × s.Sample → ℝ :=
    fun p =>
      S.sum fun z =>
        ({p : Point d × s.Sample | p.1 = z}.indicator
          (fun p => residualSqRep z p.2) p)
  have happrox_aesm : AEStronglyMeasurable approx (μq.prod s.oracleLaw) := by
    refine Finset.aestronglyMeasurable_fun_sum S ?_
    intro z hz
    have hbase :
        AEStronglyMeasurable
          (fun p : Point d × s.Sample => residualSqRep z p.2)
          (μq.prod s.oracleLaw) := by
      exact (((hfixed z).aestronglyMeasurable).stronglyMeasurable_mk.comp_measurable
        measurable_snd).aestronglyMeasurable
    have hset : MeasurableSet ({p : Point d × s.Sample | p.1 = z}) := by
      exact measurable_fst (measurableSet_singleton z)
    exact hbase.indicator hset
  refine happrox_aesm.congr ?_
  have hsnd_ac :
      Measure.map Prod.snd (μq.prod s.oracleLaw) ≪ s.oracleLaw := by
    rw [Measure.map_snd_prod]
    exact Measure.AbsolutelyContinuous.rfl.smul_left (μq Set.univ)
  have hrep_all :
      ∀ᵐ p ∂μq.prod s.oracleLaw, ∀ z ∈ S, residualSq z p.2 = residualSqRep z p.2 := by
    rw [Finset.eventually_all]
    intro z
    intro _hz
    have hz_ae_sample :
        ∀ᵐ ξ ∂s.oracleLaw, residualSq z ξ = residualSqRep z ξ :=
      ((hfixed z).aestronglyMeasurable).ae_eq_mk
    exact ae_of_ae_map measurable_snd.aemeasurable (hsnd_ac.ae_le hz_ae_sample)
  have hsupport_q : ∀ᵐ y ∂μq, y ∈ S := by
    rw [MeasureTheory.ae_map_iff hq]
    · exact ae_of_all _ fun ω => by
        simp [S, Set.Finite.mem_toFinset]
    · exact S.measurableSet
  have hfst_ac : Measure.map Prod.fst (μq.prod s.oracleLaw) ≪ μq := by
    rw [Measure.map_fst_prod]
    exact Measure.AbsolutelyContinuous.rfl.smul_left (s.oracleLaw Set.univ)
  have hsupport : ∀ᵐ p ∂μq.prod s.oracleLaw, p.1 ∈ S :=
    ae_of_ae_map measurable_fst.aemeasurable (hfst_ac.ae_le hsupport_q)
  filter_upwards [hsupport, hrep_all] with p hpS hpRep
  dsimp [approx, residualSq, residualSqRep]
  symm
  rw [Finset.sum_eq_single p.1]
  · rw [Set.indicator_of_mem]
    · exact hpRep p.1 hpS
    · rfl
  · intro z _hz hzne
    have hpnot : p ∉ ({p : Point d × s.Sample | p.1 = z}) := by
      intro hp
      exact hzne (by simpa using hp.symm)
    simp [Set.indicator_of_notMem hpnot]
  · intro hnot
    exact False.elim (hnot hpS)

/-- Well-definedness obligation for the final finite-horizon expectation in Theorem 1,
derived from the source assumptions and generated process rather than taken as a theorem
hypothesis. -/
theorem gradientL1Sum_integrable_from_finiteHorizonAssumptions {d : ℕ}
    [Nonempty (Fin d)] {s : Setup d} {T : ℕ}
    (hT : 1 ≤ T) (h : FiniteHorizonAssumptions s T) :
    (letI := s.sampleMeasurable;
      Integrable (gradientL1Sum s T) (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  unfold gradientL1Sum
  refine MeasureTheory.integrable_finset_sum (s := Finset.Icc 1 T) ?_
  intro t ht
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  obtain ⟨hx_meas, hx_fin, _hm_int, _hv_int⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
  have htime : t - 1 + 1 = t := Nat.sub_add_cancel ht1
  have hx_meas_t : AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
    simpa [htime] using hx_meas
  have hx_fin_t : (Set.range (fun ω : Run s => x s t ω)).Finite := by
    simpa [htime] using hx_fin
  exact l1_trueGradient_integrable_of_x_finiteRange (s := s) hx_meas_t hx_fin_t

private theorem initial_sampledGradient_error_integrable_and_integral_le {d : ℕ}
    {s : Setup d} (hnoise : s.OracleBoundedNoise) :
    (letI := s.sampleMeasurable;
      Integrable
          (fun ω : Run s =>
            ‖sampledGradient s 1 s.x1 ω - s.trueGradient s.x1‖ ^ 2)
          (Run.law s) ∧
        ∫ ω, ‖sampledGradient s 1 s.x1 ω - s.trueGradient s.x1‖ ^ 2
            ∂Run.law s ≤ s.sigma ^ 2) := by
  classical
  letI := s.sampleMeasurable
  let φ : s.Sample → ℝ :=
    fun ξ => ‖s.oracleValue s.x1 ξ - s.trueGradient s.x1‖ ^ 2
  have hsample_meas : Measurable (Run.sampleAt s 1) := by
    simpa [Run.sampleAt] using
      (measurable_pi_apply (1 - 1) : Measurable (fun ω : Run s => ω (1 - 1)))
  have hφ_map :
      Integrable φ (Measure.map (Run.sampleAt s 1) (Run.law s)) := by
    rw [Run.map_sampleAt_law]
    exact Setup.oracleBoundedNoise_integrable hnoise s.x1
  have hφ_le :
      ∫ ξ, φ ξ ∂s.oracleLaw ≤ s.sigma ^ 2 := by
    simpa [φ] using Setup.oracleBoundedNoise_integral_le hnoise s.x1
  have hcomp_int :
      Integrable
        (fun ω : Run s => φ (Run.sampleAt s 1 ω)) (Run.law s) := by
    simpa [Function.comp_def] using
      (MeasureTheory.integrable_map_measure hφ_map.aestronglyMeasurable
        hsample_meas.aemeasurable).1 hφ_map
  have hcomp_le :
      ∫ ω, φ (Run.sampleAt s 1 ω) ∂Run.law s ≤ s.sigma ^ 2 := by
    have hmap :
        (∫ ω, φ (Run.sampleAt s 1 ω) ∂Run.law s) =
          ∫ ξ, φ ξ ∂s.oracleLaw :=
      calc
        (∫ ω, φ (Run.sampleAt s 1 ω) ∂Run.law s) =
            ∫ ξ, φ ξ ∂Measure.map (Run.sampleAt s 1) (Run.law s) :=
          (MeasureTheory.integral_map hsample_meas.aemeasurable
            hφ_map.aestronglyMeasurable).symm
        _ = ∫ ξ, φ ξ ∂s.oracleLaw := by rw [Run.map_sampleAt_law]
    exact hmap.trans_le hφ_le
  exact ⟨by simpa [φ, sampledGradient] using hcomp_int,
    by simpa [φ, sampledGradient] using hcomp_le⟩

private theorem initial_v_estimator_error_integrable_and_integral_le {d : ℕ}
    {s : Setup d} (hnoise : s.OracleBoundedNoise) :
    (letI := s.sampleMeasurable;
      Integrable
          (fun ω : Run s => ‖v s 1 ω - s.trueGradient (x s 1 ω)‖ ^ 2)
          (Run.law s) ∧
        ∫ ω, ‖v s 1 ω - s.trueGradient (x s 1 ω)‖ ^ 2 ∂Run.law s ≤
          s.sigma ^ 2) := by
  classical
  letI := s.sampleMeasurable
  simpa [v, x, stateAt] using
    (initial_sampledGradient_error_integrable_and_integral_le (s := s) hnoise)

private theorem initial_m_estimator_error_integrable_and_integral_le {d : ℕ}
    {s : Setup d} (hnoise : s.OracleBoundedNoise) :
    (letI := s.sampleMeasurable;
      Integrable
          (fun ω : Run s => ‖m s 1 ω - s.trueGradient (x s 1 ω)‖ ^ 2)
          (Run.law s) ∧
        ∫ ω, ‖m s 1 ω - s.trueGradient (x s 1 ω)‖ ^ 2 ∂Run.law s ≤
          s.sigma ^ 2) := by
  classical
  letI := s.sampleMeasurable
  simpa [m, x, stateAt] using
    (initial_sampledGradient_error_integrable_and_integral_le (s := s) hnoise)

/-- The value of Appendix B's estimator-error bound once the displayed quotient values have
been supplied by `sourceQuotient` witnesses. -/
def finiteHorizonEstimatorErrorBoundValue {d : ℕ} (s : Setup d) (_T : ℕ)
    (invBeta2T invBeta2Sq : ℝ) : ℝ :=
  2 * s.sigma ^ 2 * invBeta2T +
    16 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) * invBeta2Sq +
      2 * s.beta2 * s.sigma ^ 2

/-- Appendix B Eq. (6)'s local source-definedness guard for the displayed quotient `1/β₁`.

This is not a primitive assumption of Theorem 1; it marks the exact quotient whose
definedness is needed when reconstructing the estimator-error proof. -/
def finiteHorizonBeta1QuotientSource {d : ℕ} (s : Setup d) (invBeta1 : ℝ) : Prop :=
  sourceQuotient 1 s.beta1 invBeta1

/-- Appendix B's finite-horizon estimator-error bound as a source-definedness relation.

Book citation: `book/research/Lion.json#/main_theorem/proof[step=29]`, the post-Eq. (7)
`v_t` estimate uses the displayed quotients `1/(β₂T)` and `1/β₂²`. -/
def finiteHorizonEstimatorErrorBoundSource {d : ℕ} (s : Setup d) (T : ℕ)
    (bound : ℝ) : Prop :=
  ∃ invBeta2T invBeta2Sq : ℝ,
    sourceQuotient 1 (s.beta2 * (T : ℝ)) invBeta2T ∧
      sourceQuotient 1 (s.beta2 ^ 2) invBeta2Sq ∧
        bound = finiteHorizonEstimatorErrorBoundValue s T invBeta2T invBeta2Sq

private theorem finiteHorizonEstimatorErrorBoundSource_nonneg {d : ℕ}
    {s : Setup d} {T : ℕ} {estimatorBound : ℝ} (hT : 1 ≤ T)
    (hmom : MomentumQuotientDomainAt s.beta1 s.beta2 T)
    (hsrc : finiteHorizonEstimatorErrorBoundSource s T estimatorBound) :
    0 ≤ estimatorBound := by
  classical
  rcases hmom with ⟨hparam, _hbeta1Q, _hbeta2TQ, _hbeta2SqQ⟩
  rcases hparam with ⟨_hbeta1_pos, hbeta2_pos, _hbeta1_le_one, _hbeta2_le_one⟩
  rcases hsrc with ⟨invBeta2T, invBeta2Sq, hqT, hqSq, rfl⟩
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hdenT_pos : 0 < s.beta2 * (T : ℝ) :=
    mul_pos hbeta2_pos hT_pos
  have hdenSq_pos : 0 < s.beta2 ^ 2 := by
    positivity
  have hinvT_nonneg : 0 ≤ invBeta2T := by
    rw [sourceQuotient_eq_div hqT]
    exact div_nonneg zero_le_one (le_of_lt hdenT_pos)
  have hinvSq_nonneg : 0 ≤ invBeta2Sq := by
    rw [sourceQuotient_eq_div hqSq]
    exact div_nonneg zero_le_one (le_of_lt hdenSq_pos)
  have hterm1 : 0 ≤ 2 * s.sigma ^ 2 * invBeta2T := by
    positivity
  have hterm2 :
      0 ≤ 16 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) * invBeta2Sq := by
    positivity
  have hterm3 : 0 ≤ 2 * s.beta2 * s.sigma ^ 2 := by
    positivity
  unfold finiteHorizonEstimatorErrorBoundValue
  linarith

/-- The value of Appendix B's final finite-horizon gradient-average bound once the displayed
quotient values have been supplied by source-definedness witnesses. -/
def finiteHorizonGradientBoundValue {d : ℕ} (s : Setup d) (_T : ℕ)
    (invEtaT estimatorBound : ℝ) : ℝ :=
  2 * s.Delta_f * invEtaT +
    4 * Real.sqrt (d : ℝ) * Real.sqrt estimatorBound +
      4 * s.eta * s.L * (d : ℝ)

/-- Appendix B's finite-horizon gradient-average bound as a source-definedness relation.

Book citation: `book/research/Lion.json#/main_theorem/proof[step=30]`, the displayed
finite-horizon bound uses `1/(ηT)` together with the estimator-error quotient terms. -/
def finiteHorizonGradientBoundSource {d : ℕ} (s : Setup d) (T : ℕ)
    (bound : ℝ) : Prop :=
  ∃ invEtaT estimatorBound : ℝ,
    sourceQuotient 1 (s.eta * (T : ℝ)) invEtaT ∧
      finiteHorizonEstimatorErrorBoundSource s T estimatorBound ∧
        bound = finiteHorizonGradientBoundValue s T invEtaT estimatorBound

/-- Corrected non-original finite-horizon Appendix B domain obligations.

This contract contains the beta quotient obligations `1/β₁`, `1/(β₂T)`, `1/β₂²`, the
eta-horizon quotient `1/(ηT)`, and the eta-lambda contraction domain used by Appendix A/B.
It is not a primitive assumption of the printed theorem. -/
def finiteHorizonCorrectedDomainObligations {d : ℕ} (s : Setup d) (T : ℕ) : Prop :=
  MomentumQuotientDomainAt s.beta1 s.beta2 T ∧
    EtaLambdaHorizonDomainAt s.eta s.lambda T

/-- The finite-horizon corrected Appendix A/B contract supplies Lemma 1's corrected domain. -/
theorem lemmaOne_correctedDomainAssumptions_of_finiteHorizonCorrectedDomainObligations
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ}
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T) :
    lemmaOne_correctedDomainAssumptions s T :=
  ⟨h, hdomains.2⟩

/-- Corrected non-original finite-horizon Appendix B bound contract.

The `bound` value is tied to Appendix B's displayed finite-horizon expression by checked
source quotients, rather than by Lean's totalized division fallback. -/
def finiteHorizonCorrectedBoundContract {d : ℕ} (s : Setup d) (T : ℕ)
    (bound : ℝ) : Prop :=
  finiteHorizonCorrectedDomainObligations s T ∧ finiteHorizonGradientBoundSource s T bound

/-- Appendix B's estimator-error bound with the checked source quotients instantiated by
ordinary inverse values.

This is not a new mathematical estimate; it is the canonical Lean value of the displayed
finite-horizon expression once the corrected quotient domain has exposed nonzero
denominators. -/
def theoremOneCanonicalEstimatorBound {d : ℕ} (s : Setup d) (p : ParameterSchedule)
    (T : ℕ) : ℝ :=
  finiteHorizonEstimatorErrorBoundValue (p.setupAt s T) T
    (((p.beta2 T) * (T : ℝ))⁻¹) (((p.beta2 T) ^ 2)⁻¹)

/-- Appendix B's final finite-horizon gradient-average bound with all displayed quotients
instantiated by ordinary inverse values. -/
def theoremOneCanonicalGradientBound {d : ℕ} (s : Setup d) (p : ParameterSchedule)
    (T : ℕ) : ℝ :=
  finiteHorizonGradientBoundValue (p.setupAt s T) T
    (((p.eta T) * (T : ℝ))⁻¹) (theoremOneCanonicalEstimatorBound s p T)

private theorem sourceQuotient_inv_of_sourceQuotient {denominator value : ℝ}
    (h : sourceQuotient 1 denominator value) :
    sourceQuotient 1 denominator denominator⁻¹ := by
  have hden : denominator ≠ 0 := sourceQuotient_denominator_ne h
  have hdiv : sourceQuotient 1 denominator (1 / denominator) :=
    SOptLib.checked_quotient_spec_div_of_den_ne (K := ℝ) (1 : ℝ) hden
  simpa [div_eq_mul_inv] using hdiv

private theorem finiteHorizonCorrectedBoundContract_canonical {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule} {T : ℕ} (hT : 1 ≤ T)
    (hdomains : theoremOneCorrectedDomainObligations p) :
    finiteHorizonCorrectedBoundContract (p.setupAt s T) T
      (theoremOneCanonicalGradientBound s p T) := by
  classical
  rcases hdomains T hT with ⟨hmom, heta⟩
  have hmom_full := hmom
  have heta_full := heta
  rcases hmom with ⟨hmomParam, _hbeta1Q, hbeta2TQ, hbeta2SqQ⟩
  rcases heta with ⟨heta_pos, hetaContract, hetaTQ⟩
  rcases hbeta2TQ with ⟨invBeta2T, hqBeta2T⟩
  rcases hbeta2SqQ with ⟨invBeta2Sq, hqBeta2Sq⟩
  rcases hetaTQ with ⟨invEtaT, hqEtaT⟩
  have hqBeta2T' :
      sourceQuotient 1
        ((p.setupAt s T).beta2 * (T : ℝ))
        (((p.setupAt s T).beta2 * (T : ℝ))⁻¹) := by
    simpa [ParameterSchedule.setupAt, Setup.withParameters] using
      (sourceQuotient_inv_of_sourceQuotient hqBeta2T)
  have hqBeta2Sq' :
      sourceQuotient 1
        ((p.setupAt s T).beta2 ^ 2)
        (((p.setupAt s T).beta2 ^ 2)⁻¹) := by
    simpa [ParameterSchedule.setupAt, Setup.withParameters] using
      (sourceQuotient_inv_of_sourceQuotient hqBeta2Sq)
  have hqEtaT' :
      sourceQuotient 1
        ((p.setupAt s T).eta * (T : ℝ))
        (((p.setupAt s T).eta * (T : ℝ))⁻¹) := by
    simpa [ParameterSchedule.setupAt, Setup.withParameters] using
      (sourceQuotient_inv_of_sourceQuotient hqEtaT)
  refine ⟨?_, ?_⟩
  · simpa [finiteHorizonCorrectedDomainObligations, ParameterSchedule.setupAt,
      Setup.withParameters] using (And.intro hmom_full heta_full)
  · refine
      ⟨((p.setupAt s T).eta * (T : ℝ))⁻¹, theoremOneCanonicalEstimatorBound s p T,
        hqEtaT', ?_, ?_⟩
    · refine
        ⟨((p.setupAt s T).beta2 * (T : ℝ))⁻¹, ((p.setupAt s T).beta2 ^ 2)⁻¹,
          hqBeta2T', hqBeta2Sq', ?_⟩
      simp [theoremOneCanonicalEstimatorBound, ParameterSchedule.setupAt,
        Setup.withParameters]
    · simp [theoremOneCanonicalGradientBound, theoremOneCanonicalEstimatorBound,
        ParameterSchedule.setupAt, Setup.withParameters]

private theorem gradientL1Sum_nonneg {d : ℕ} (s : Setup d) (T : ℕ) (ω : Run s) :
    0 ≤ gradientL1Sum s T ω := by
  exact Finset.sum_nonneg fun t _ht => l1Norm_nonneg (s.trueGradient (x s t ω))

private theorem averageExpectedGradientL1_nonneg {d : ℕ} (s : Setup d) (T : ℕ) :
    0 ≤ averageExpectedGradientL1 s T := by
  classical
  letI := s.sampleMeasurable
  unfold averageExpectedGradientL1
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
    (integral_nonneg fun ω => gradientL1Sum_nonneg s T ω)

private theorem fresh_oracle_residual_sq_integrable_and_integral_le_for_lion_prefix
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ}
    (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      Integrable
          (fun ω : Run s =>
            ‖G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2)
          (Run.law s) ∧
        ∫ ω, ‖G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2
            ∂Run.law s ≤ s.sigma ^ 2) := by
  classical
  letI := s.sampleMeasurable
  obtain ⟨qRep, hqRep_meas, hq_ae, hqRep_first_fin, _hqRep_l2⟩ :=
    lion_eq6_query_direction_adapted_rep (s := s) (T := T) h ht
  have hqRep_aemeas : AEMeasurable qRep (Run.law s) :=
    (hqRep_meas.mono
      ((SOptLib.filtration (fun n (ω : Run s) => ω n)
        (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).le' t)
      le_rfl).aemeasurable
  have hquery_aemeas : AEMeasurable (fun ω : Run s => (qRep ω).1) (Run.law s) :=
    measurable_fst.comp_aemeasurable hqRep_aemeas
  have hsample_meas : AEMeasurable (Run.sampleAt s (t + 1)) (Run.law s) := by
    have hmeas : Measurable (Run.sampleAt s (t + 1)) := by
      simpa [Run.sampleAt] using
        (measurable_pi_apply t : Measurable (fun ω : Run s => ω t))
    exact hmeas.aemeasurable
  have hindep :
      ProbabilityTheory.IndepFun (fun ω : Run s => (qRep ω).1)
        (Run.sampleAt s (t + 1)) (Run.law s) := by
    have hpair_indep :
        ProbabilityTheory.IndepFun qRep (Run.sampleAt s (t + 1)) (Run.law s) :=
      run_prefix_measurable_indep_sampleAt_succ (s := s) (t := t) (q := qRep) hqRep_meas
    exact hpair_indep.comp measurable_fst measurable_id
  have hsample_law :
      Measure.map (Run.sampleAt s (t + 1)) (Run.law s) = s.oracleLaw :=
    Run.map_sampleAt_law s (t + 1)
  have hres_sq_prod :
      AEStronglyMeasurable
        (fun p : Point d × s.Sample =>
          ‖s.oracleValue p.1 p.2 - s.trueGradient p.1‖ ^ 2)
        ((Measure.map (fun ω : Run s => (qRep ω).1) (Run.law s)).prod
          (Measure.map (Run.sampleAt s (t + 1)) (Run.law s))) := by
    rw [hsample_law]
    exact oracle_residual_sq_prod_aestronglyMeasurable_of_finite_query
      (s := s) (μ := Run.law s) (q := fun ω : Run s => (qRep ω).1)
      hquery_aemeas hqRep_first_fin
      (fun z => Setup.oracleBoundedNoise_integrable h.oracle_bounded_noise z)
  have hfixed :
      ∀ z : Point d,
        Integrable
            (fun ξ : s.Sample => ‖s.oracleValue z ξ - s.trueGradient z‖ ^ 2)
            (Measure.map (Run.sampleAt s (t + 1)) (Run.law s)) ∧
          ∫ ξ : s.Sample, ‖s.oracleValue z ξ - s.trueGradient z‖ ^ 2
              ∂Measure.map (Run.sampleAt s (t + 1)) (Run.law s) ≤ s.sigma ^ 2 := by
    intro z
    rw [hsample_law]
    exact ⟨Setup.oracleBoundedNoise_integrable h.oracle_bounded_noise z,
      Setup.oracleBoundedNoise_integral_le h.oracle_bounded_noise z⟩
  have htransfer :=
    randomQuery_oracleResidual_sq_integrable_and_integral_le_of_indep_fixed
      (P := Run.law s)
      (query := fun ω : Run s => (qRep ω).1)
      (sample := Run.sampleAt s (t + 1))
      (G := s.oracleValue) (target := s.trueGradient) (σ2 := s.sigma ^ 2)
      hres_sq_prod hquery_aemeas hsample_meas hindep hfixed
  have h_actual_ae :
      (fun ω : Run s =>
        ‖G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2) =ᵐ[
        Run.law s]
        (fun ω : Run s =>
          ‖s.oracleValue ((qRep ω).1) (Run.sampleAt s (t + 1) ω) -
            s.trueGradient ((qRep ω).1)‖ ^ 2) := by
    filter_upwards [hq_ae] with ω hω
    have hxnext : x s (t + 1) ω = (qRep ω).1 := congrArg Prod.fst hω
    simp [G, sampledGradient, hxnext]
  exact ⟨htransfer.1.congr h_actual_ae.symm,
    by
      calc
        (∫ ω : Run s,
            ‖G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2
            ∂Run.law s) =
            ∫ ω : Run s,
              ‖s.oracleValue ((qRep ω).1) (Run.sampleAt s (t + 1) ω) -
                s.trueGradient ((qRep ω).1)‖ ^ 2 ∂Run.law s :=
          integral_congr_ae h_actual_ae
        _ ≤ s.sigma ^ 2 := htransfer.2⟩

private theorem fresh_oracle_residual_inner_integral_eq_zero_for_lion_prefix
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ}
    (hT : 1 ≤ T) (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t + 1 ≤ T) :
    (letI := s.sampleMeasurable;
      (∫ ω : Run s,
          ⟪G s (t + 1) ω - s.trueGradient (x s (t + 1) ω),
            (1 - s.beta1) •
              (m s t ω - s.trueGradient (x s t ω) +
                (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))⟫_ℝ
          ∂Run.law s) = 0) := by
  classical
  letI := s.sampleMeasurable
  have hfixed_centered :
      ∀ z : Point d,
        Integrable (fun ξ => s.oracleValue z ξ - s.trueGradient z) s.oracleLaw ∧
          ∫ ξ, s.oracleValue z ξ - s.trueGradient z ∂s.oracleLaw = 0 :=
    fixed_oracle_residual_integrable_and_integral_eq_zero (s := s) h.oracle_unbiased
  have hsample_law :
      Measure.map (Run.sampleAt s (t + 1)) (Run.law s) = s.oracleLaw :=
    Run.map_sampleAt_law s (t + 1)
  have _hinitial_v :=
    initial_v_estimator_error_integrable_and_integral_le (s := s) h.oracle_bounded_noise
  have _hinitial_m :=
    initial_m_estimator_error_integrable_and_integral_le (s := s) h.oracle_bounded_noise
  have hlemDom :=
    lemmaOne_correctedDomainAssumptions_of_finiteHorizonCorrectedDomainObligations
      (s := s) (T := T) h hdomains
  have hlem :=
    lemma_one_iterate_and_step_bounds_correctedDomain (s := s) (T := T) hT hlemDom
  have ht_le_T : t ≤ T := by omega
  have _hstep :
      ∀ ω : Run s,
        ‖x s (t + 1) ω - x s t ω‖ ^ 2 ≤ 4 * s.eta ^ 2 * (d : ℝ) :=
    fun ω => (hlem t ht ht_le_T ω).2.2
  have _hmrec :
      ∀ ω : Run s,
        m s (t + 1) ω =
          (1 - s.beta2) • m s t ω + s.beta2 • G s (t + 1) ω :=
    fun ω => m_succ_eq_original_momentum s ht ω
  have _hvrec :
      ∀ ω : Run s,
        v s (t + 1) ω =
          (1 - s.beta1) • m s t ω + s.beta1 • G s (t + 1) ω :=
    fun ω => v_succ_eq_lookahead_momentum s ht ω
  have _hdir_sq :
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta1) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s) :=
    lion_eq6_direction_sq_integrable (s := s) (T := T) h ht
  let q : Run s → Point d × Point d :=
    fun ω =>
      (x s (t + 1) ω,
        (1 - s.beta1) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))))
  obtain ⟨qRep, hqRep_meas, hq_ae, hqRep_first_fin, hqRep_l2⟩ :=
    lion_eq6_query_direction_adapted_rep (s := s) (T := T) h ht
  have hqRep_aemeas : AEMeasurable qRep (Run.law s) :=
    (hqRep_meas.mono
      ((SOptLib.filtration (fun n (ω : Run s) => ω n)
        (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).le' t)
      le_rfl).aemeasurable
  have hsample_meas : AEMeasurable (Run.sampleAt s (t + 1)) (Run.law s) := by
    have hmeas : Measurable (Run.sampleAt s (t + 1)) := by
      simpa [Run.sampleAt] using
        (measurable_pi_apply t : Measurable (fun ω : Run s => ω t))
    exact hmeas.aemeasurable
  have hindep :
      ProbabilityTheory.IndepFun qRep (Run.sampleAt s (t + 1)) (Run.law s) :=
    run_prefix_measurable_indep_sampleAt_succ (s := s) (t := t) (q := qRep) hqRep_meas
  have hres_prod :
      AEStronglyMeasurable
        (fun p : (Point d × Point d) × s.Sample =>
          s.oracleValue p.1.1 p.2 - s.trueGradient p.1.1)
        ((Measure.map qRep (Run.law s)).prod s.oracleLaw) :=
    oracle_residual_prod_aestronglyMeasurable_of_finite_first_query
      (s := s) (μ := Run.law s) (q := qRep)
      hqRep_aemeas hqRep_first_fin hfixed_centered
  have hcancel :=
    randomQuery_inner_oracleResidual_integrable_and_integral_eq_zero_of_l2
      (P := Run.law s) (ν := s.oracleLaw)
      (query := qRep) (sample := Run.sampleAt s (t + 1))
      (G := s.oracleValue) (target := s.trueGradient)
      (varianceBudget := s.sigma ^ 2)
      hres_prod hqRep_aemeas hsample_meas hindep hsample_law
      (fun z => (hfixed_centered z).1)
      (fun z => (hfixed_centered z).2)
      (fun z => Setup.oracleBoundedNoise_integrable h.oracle_bounded_noise z)
      (fun z => Setup.oracleBoundedNoise_integral_le h.oracle_bounded_noise z)
      hqRep_l2
  have h_integrand_ae :
      (fun ω : Run s =>
        ⟪G s (t + 1) ω - s.trueGradient (x s (t + 1) ω),
          (1 - s.beta1) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))⟫_ℝ) =ᵐ[
        Run.law s]
        (fun ω : Run s =>
          ⟪s.oracleValue (qRep ω).1 (Run.sampleAt s (t + 1) ω) -
              s.trueGradient (qRep ω).1,
            (qRep ω).2⟫_ℝ) := by
    filter_upwards [hq_ae] with ω hω
    have hω' : q ω = qRep ω := hω
    simpa [q, G, sampledGradient, hω'] using congrArg
      (fun y : Point d × Point d =>
        ⟪s.oracleValue y.1 (Run.sampleAt s (t + 1) ω) - s.trueGradient y.1,
          y.2⟫_ℝ) hω'
  calc
    (∫ ω : Run s,
        ⟪G s (t + 1) ω - s.trueGradient (x s (t + 1) ω),
          (1 - s.beta1) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))⟫_ℝ
        ∂Run.law s) =
        ∫ ω : Run s,
          ⟪s.oracleValue (qRep ω).1 (Run.sampleAt s (t + 1) ω) -
              s.trueGradient (qRep ω).1,
            (qRep ω).2⟫_ℝ ∂Run.law s :=
      integral_congr_ae h_integrand_ae
    _ = 0 := hcancel.2

/-- Fresh-noise cancellation for the beta₂ expansion used in Appendix B's unprinted
`m_{t+1}` analogue of Eq. (6). -/
private theorem fresh_oracle_residual_inner_integral_eq_zero_for_lion_prefix_beta2
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ}
    (hT : 1 ≤ T) (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t + 1 ≤ T) :
    (letI := s.sampleMeasurable;
      (∫ ω : Run s,
          ⟪G s (t + 1) ω - s.trueGradient (x s (t + 1) ω),
            (1 - s.beta2) •
              (m s t ω - s.trueGradient (x s t ω) +
                (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))⟫_ℝ
          ∂Run.law s) = 0) := by
  classical
  letI := s.sampleMeasurable
  have hfixed_centered :
      ∀ z : Point d,
        Integrable (fun ξ => s.oracleValue z ξ - s.trueGradient z) s.oracleLaw ∧
          ∫ ξ, s.oracleValue z ξ - s.trueGradient z ∂s.oracleLaw = 0 :=
    fixed_oracle_residual_integrable_and_integral_eq_zero (s := s) h.oracle_unbiased
  have hsample_law :
      Measure.map (Run.sampleAt s (t + 1)) (Run.law s) = s.oracleLaw :=
    Run.map_sampleAt_law s (t + 1)
  have _hinitial_v :=
    initial_v_estimator_error_integrable_and_integral_le (s := s) h.oracle_bounded_noise
  have _hinitial_m :=
    initial_m_estimator_error_integrable_and_integral_le (s := s) h.oracle_bounded_noise
  have hlemDom :=
    lemmaOne_correctedDomainAssumptions_of_finiteHorizonCorrectedDomainObligations
      (s := s) (T := T) h hdomains
  have hlem :=
    lemma_one_iterate_and_step_bounds_correctedDomain (s := s) (T := T) hT hlemDom
  have ht_le_T : t ≤ T := by omega
  have _hstep :
      ∀ ω : Run s,
        ‖x s (t + 1) ω - x s t ω‖ ^ 2 ≤ 4 * s.eta ^ 2 * (d : ℝ) :=
    fun ω => (hlem t ht ht_le_T ω).2.2
  have _hmrec :
      ∀ ω : Run s,
        m s (t + 1) ω =
          (1 - s.beta2) • m s t ω + s.beta2 • G s (t + 1) ω :=
    fun ω => m_succ_eq_original_momentum s ht ω
  have _hvrec :
      ∀ ω : Run s,
        v s (t + 1) ω =
          (1 - s.beta1) • m s t ω + s.beta1 • G s (t + 1) ω :=
    fun ω => v_succ_eq_lookahead_momentum s ht ω
  have _hdir_sq :
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta2) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s) :=
    lion_eq6_direction_sq_integrable_beta2 (s := s) (T := T) h ht
  let q : Run s → Point d × Point d :=
    fun ω =>
      (x s (t + 1) ω,
        (1 - s.beta2) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω))))
  obtain ⟨qRep, hqRep_meas, hq_ae, hqRep_first_fin, hqRep_l2⟩ :=
    lion_eq6_query_direction_adapted_rep_beta2 (s := s) (T := T) h ht
  have hqRep_aemeas : AEMeasurable qRep (Run.law s) :=
    (hqRep_meas.mono
      ((SOptLib.filtration (fun n (ω : Run s) => ω n)
        (fun n => (measurable_pi_apply n : Measurable (fun ω : Run s => ω n)))).le' t)
      le_rfl).aemeasurable
  have hsample_meas : AEMeasurable (Run.sampleAt s (t + 1)) (Run.law s) := by
    have hmeas : Measurable (Run.sampleAt s (t + 1)) := by
      simpa [Run.sampleAt] using
        (measurable_pi_apply t : Measurable (fun ω : Run s => ω t))
    exact hmeas.aemeasurable
  have hindep :
      ProbabilityTheory.IndepFun qRep (Run.sampleAt s (t + 1)) (Run.law s) :=
    run_prefix_measurable_indep_sampleAt_succ (s := s) (t := t) (q := qRep) hqRep_meas
  have hres_prod :
      AEStronglyMeasurable
        (fun p : (Point d × Point d) × s.Sample =>
          s.oracleValue p.1.1 p.2 - s.trueGradient p.1.1)
        ((Measure.map qRep (Run.law s)).prod s.oracleLaw) :=
    oracle_residual_prod_aestronglyMeasurable_of_finite_first_query
      (s := s) (μ := Run.law s) (q := qRep)
      hqRep_aemeas hqRep_first_fin hfixed_centered
  have hcancel :=
    randomQuery_inner_oracleResidual_integrable_and_integral_eq_zero_of_l2
      (P := Run.law s) (ν := s.oracleLaw)
      (query := qRep) (sample := Run.sampleAt s (t + 1))
      (G := s.oracleValue) (target := s.trueGradient)
      (varianceBudget := s.sigma ^ 2)
      hres_prod hqRep_aemeas hsample_meas hindep hsample_law
      (fun z => (hfixed_centered z).1)
      (fun z => (hfixed_centered z).2)
      (fun z => Setup.oracleBoundedNoise_integrable h.oracle_bounded_noise z)
      (fun z => Setup.oracleBoundedNoise_integral_le h.oracle_bounded_noise z)
      hqRep_l2
  have h_integrand_ae :
      (fun ω : Run s =>
        ⟪G s (t + 1) ω - s.trueGradient (x s (t + 1) ω),
          (1 - s.beta2) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))⟫_ℝ) =ᵐ[
        Run.law s]
        (fun ω : Run s =>
          ⟪s.oracleValue (qRep ω).1 (Run.sampleAt s (t + 1) ω) -
              s.trueGradient (qRep ω).1,
            (qRep ω).2⟫_ℝ) := by
    filter_upwards [hq_ae] with ω hω
    have hω' : q ω = qRep ω := hω
    simpa [q, G, sampledGradient, hω'] using congrArg
      (fun y : Point d × Point d =>
        ⟪s.oracleValue y.1 (Run.sampleAt s (t + 1) ω) - s.trueGradient y.1,
          y.2⟫_ℝ) hω'
  calc
    (∫ ω : Run s,
        ⟪G s (t + 1) ω - s.trueGradient (x s (t + 1) ω),
          (1 - s.beta2) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))⟫_ℝ
        ∂Run.law s) =
        ∫ ω : Run s,
          ⟪s.oracleValue (qRep ω).1 (Run.sampleAt s (t + 1) ω) -
              s.trueGradient (qRep ω).1,
            (qRep ω).2⟫_ℝ ∂Run.law s :=
      integral_congr_ae h_integrand_ae
    _ = 0 := hcancel.2

private theorem lion_one_step_l1_descent_bound_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t ≤ T) (ω : Run s) :
    s.f (x s (t + 1) ω) ≤
      s.f (x s t ω) +
        2 * s.eta * Real.sqrt (d : ℝ) *
          ‖s.trueGradient (x s t ω) - v s t ω‖ -
        (s.eta / 2) * l1Norm (s.trueGradient (x s t ω)) +
        2 * s.eta ^ 2 * s.L * (d : ℝ) := by
  classical
  let xt : Point d := x s t ω
  let xnext : Point d := x s (t + 1) ω
  let gt : Point d := s.trueGradient xt
  let vt : Point d := v s t ω
  have hlemDom :=
    lemmaOne_correctedDomainAssumptions_of_finiteHorizonCorrectedDomainObligations
      (s := s) (T := T) h hdomains
  have hlem :=
    lemma_one_iterate_and_step_bounds_correctedDomain (s := s) (T := T) hT hlemDom
  have hlinf : linfNorm xt ≤ s.eta * (t : ℝ) := by
    simpa [xt] using (hlem t ht htT ω).1
  have hstep_sq :
      ‖xnext - xt‖ ^ 2 ≤ 4 * s.eta ^ 2 * (d : ℝ) := by
    simpa [xnext, xt] using (hlem t ht htT ω).2.2
  obtain ⟨heta_pos, hcontr, _hquot⟩ := hdomains.2
  have heta_nonneg : 0 ≤ s.eta := le_of_lt heta_pos
  have hlambda_nonneg : 0 ≤ s.lambda :=
    lambda_nonneg_of_eta_pos_contraction_upper heta_pos hcontr.2
  have hbudget : s.lambda * linfNorm xt ≤ 1 / 2 :=
    lambda_mul_linfNorm_le_half_correctedDomain
      (s := s) (T := T) (t := t) hT h hdomains.2 htT hlinf
  have hxupdate := x_succ_eq_update s ht ω
  have hdiff :
      xnext - xt = -(s.eta • (coordinateSign vt + s.lambda • xt)) := by
    dsimp [xnext, xt, vt]
    rw [hxupdate]
    abel
  have hinner_step :
      ⟪gt, xnext - xt⟫_ℝ ≤
        2 * s.eta * Real.sqrt (d : ℝ) * ‖gt - vt‖ -
          (s.eta / 2) * l1Norm gt := by
    rw [hdiff]
    exact lion_direction_inner_le_error_minus_half_l1
      (d := d) (eta := s.eta) (lambda := s.lambda)
      heta_nonneg hlambda_nonneg (g := gt) (u := vt) (z := xt) hbudget
  have hL_nonneg : 0 ≤ s.L := smoothness_L_nonneg h.smoothness
  have hquad_term :
      (s.L / 2) * ‖xnext - xt‖ ^ 2 ≤
        2 * s.eta ^ 2 * s.L * (d : ℝ) := by
    have hcoef_nonneg : 0 ≤ s.L / 2 := div_nonneg hL_nonneg (by norm_num)
    have hscaled :
        (s.L / 2) * ‖xnext - xt‖ ^ 2 ≤
          (s.L / 2) * (4 * s.eta ^ 2 * (d : ℝ)) :=
      mul_le_mul_of_nonneg_left hstep_sq hcoef_nonneg
    calc
      (s.L / 2) * ‖xnext - xt‖ ^ 2 ≤
          (s.L / 2) * (4 * s.eta ^ 2 * (d : ℝ)) := hscaled
      _ = 2 * s.eta ^ 2 * s.L * (d : ℝ) := by ring
  have hquad :
      s.f xnext ≤ s.f xt + ⟪gt, xnext - xt⟫_ℝ +
        (s.L / 2) * ‖xnext - xt‖ ^ 2 := by
    simpa [gt] using smoothness_quadratic_upper_bound h.smoothness xt xnext
  dsimp [xt, xnext, gt, vt] at hquad hinner_step hquad_term ⊢
  nlinarith

private theorem trueGradient_step_sq_le_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t ≤ T) (ω : Run s) :
    ‖s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)‖ ^ 2 ≤
      4 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) := by
  classical
  have hL_nonneg : 0 ≤ s.L := smoothness_L_nonneg h.smoothness
  have hlemDom :=
    lemmaOne_correctedDomainAssumptions_of_finiteHorizonCorrectedDomainObligations
      (s := s) (T := T) h hdomains
  have hlem :=
    lemma_one_iterate_and_step_bounds_correctedDomain (s := s) (T := T) hT hlemDom
  have hstep_sq :
      ‖x s (t + 1) ω - x s t ω‖ ^ 2 ≤ 4 * s.eta ^ 2 * (d : ℝ) := by
    simpa using (hlem t ht htT ω).2.2
  have hlip :
      ‖s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)‖ ≤
        s.L * ‖x s t ω - x s (t + 1) ω‖ :=
    Setup.smoothness_lipschitz_trueGradient h.smoothness (x s t ω) (x s (t + 1) ω)
  have hstep_sq_rev :
      ‖x s t ω - x s (t + 1) ω‖ ^ 2 ≤ 4 * s.eta ^ 2 * (d : ℝ) := by
    simpa [norm_sub_rev] using hstep_sq
  have hlip_sq :
      ‖s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)‖ ^ 2 ≤
        s.L ^ 2 * ‖x s t ω - x s (t + 1) ω‖ ^ 2 := by
    calc
      ‖s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)‖ ^ 2 ≤
          (s.L * ‖x s t ω - x s (t + 1) ω‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hL_nonneg (norm_nonneg _))).2 hlip
      _ = s.L ^ 2 * ‖x s t ω - x s (t + 1) ω‖ ^ 2 := by ring
  have hscaled :
      s.L ^ 2 * ‖x s t ω - x s (t + 1) ω‖ ^ 2 ≤
        s.L ^ 2 * (4 * s.eta ^ 2 * (d : ℝ)) :=
    mul_le_mul_of_nonneg_left hstep_sq_rev (sq_nonneg s.L)
  calc
    ‖s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)‖ ^ 2 ≤
        s.L ^ 2 * ‖x s t ω - x s (t + 1) ω‖ ^ 2 := hlip_sq
    _ ≤ s.L ^ 2 * (4 * s.eta ^ 2 * (d : ℝ)) := hscaled
    _ = 4 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) := by ring

private theorem lion_beta1_direction_sq_le_m_error_add_drift_budget
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t ≤ T) (ω : Run s) :
    ‖(1 - s.beta1) •
      (m s t ω - s.trueGradient (x s t ω) +
        (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2 ≤
      (1 - s.beta1) *
        ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1 := by
  classical
  rcases hdomains.1.1 with ⟨hbeta1_pos, _hbeta2_pos, hbeta1_le_one, _hbeta2_le_one⟩
  let err : Point d := m s t ω - s.trueGradient (x s t ω)
  let drift : Point d := s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)
  let B : ℝ := 4 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdrift : ‖drift‖ ^ 2 ≤ B := by
    simpa [drift, B] using
      trueGradient_step_sq_le_correctedDomain (s := s) (T := T) hT h hdomains ht htT ω
  have hmain :=
    one_sub_smul_norm_add_sq_le_error_add_drift_budget
      (beta := s.beta1) (B := B) hbeta1_pos hbeta1_le_one hB_nonneg err drift hdrift
  change
    ‖(1 - s.beta1) • (err + drift)‖ ^ 2 ≤
      (1 - s.beta1) * ‖err‖ ^ 2 + 8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1
  calc
    ‖(1 - s.beta1) • (err + drift)‖ ^ 2 ≤
        (1 - s.beta1) * ‖err‖ ^ 2 + 2 * s.beta1⁻¹ * B := hmain
    _ = (1 - s.beta1) * ‖err‖ ^ 2 +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1 := by
      dsimp [B]
      ring

private theorem lion_beta2_direction_sq_le_m_error_add_drift_budget
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t ≤ T) (ω : Run s) :
    ‖(1 - s.beta2) •
      (m s t ω - s.trueGradient (x s t ω) +
        (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2 ≤
      (1 - s.beta2) *
        ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2 := by
  classical
  rcases hdomains.1.1 with ⟨_hbeta1_pos, hbeta2_pos, _hbeta1_le_one, hbeta2_le_one⟩
  let err : Point d := m s t ω - s.trueGradient (x s t ω)
  let drift : Point d := s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)
  let B : ℝ := 4 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdrift : ‖drift‖ ^ 2 ≤ B := by
    simpa [drift, B] using
      trueGradient_step_sq_le_correctedDomain (s := s) (T := T) hT h hdomains ht htT ω
  have hmain :=
    one_sub_smul_norm_add_sq_le_error_add_drift_budget
      (beta := s.beta2) (B := B) hbeta2_pos hbeta2_le_one hB_nonneg err drift hdrift
  change
    ‖(1 - s.beta2) • (err + drift)‖ ^ 2 ≤
      (1 - s.beta2) * ‖err‖ ^ 2 + 8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2
  calc
    ‖(1 - s.beta2) • (err + drift)‖ ^ 2 ≤
        (1 - s.beta2) * ‖err‖ ^ 2 + 2 * s.beta2⁻¹ * B := hmain
    _ = (1 - s.beta2) * ‖err‖ ^ 2 +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2 := by
      dsimp [B]
      ring

private theorem m_estimator_error_sq_integrable_at {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      Integrable
        (fun ω : Run s => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  obtain ⟨hx_meas0, hx_fin0, hm_int0, _hv_int0⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
  obtain ⟨hm_sq0, _hv_sq0⟩ :=
    lion_momentum_sq_integrable (s := s) h.oracle_unbiased h.oracle_bounded_noise (t - 1)
  have htime : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hx_meas_t : AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
    simpa [htime] using hx_meas0
  have hx_fin_t : (Set.range (fun ω : Run s => x s t ω)).Finite := by
    simpa [htime] using hx_fin0
  have hm_int_t : Integrable (fun ω : Run s => m s t ω) (Run.law s) := by
    simpa [htime] using hm_int0
  have hm_sq_t : Integrable (fun ω : Run s => ‖m s t ω‖ ^ 2) (Run.law s) := by
    simpa [htime] using hm_sq0
  have hgrad_int_t :
      Integrable (fun ω : Run s => s.trueGradient (x s t ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_meas_t hx_fin_t
  have hgrad_sq_t :
      Integrable (fun ω : Run s => ‖s.trueGradient (x s t ω)‖ ^ 2) (Run.law s) :=
    trueGradient_sq_integrable_of_x_finiteRange (s := s) hx_meas_t hx_fin_t
  exact
    integrable_sq_norm_sub hm_int_t.aestronglyMeasurable
      hgrad_int_t.aestronglyMeasurable hm_sq_t hgrad_sq_t

private theorem v_estimator_error_sq_integrable_at {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      Integrable
        (fun ω : Run s => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  obtain ⟨hx_meas0, hx_fin0, _hm_int0, hv_int0⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
  obtain ⟨_hm_sq0, hv_sq0⟩ :=
    lion_momentum_sq_integrable (s := s) h.oracle_unbiased h.oracle_bounded_noise (t - 1)
  have htime : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hx_meas_t : AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
    simpa [htime] using hx_meas0
  have hx_fin_t : (Set.range (fun ω : Run s => x s t ω)).Finite := by
    simpa [htime] using hx_fin0
  have hv_int_t : Integrable (fun ω : Run s => v s t ω) (Run.law s) := by
    simpa [htime] using hv_int0
  have hv_sq_t : Integrable (fun ω : Run s => ‖v s t ω‖ ^ 2) (Run.law s) := by
    simpa [htime] using hv_sq0
  have hgrad_int_t :
      Integrable (fun ω : Run s => s.trueGradient (x s t ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_meas_t hx_fin_t
  have hgrad_sq_t :
      Integrable (fun ω : Run s => ‖s.trueGradient (x s t ω)‖ ^ 2) (Run.law s) :=
    trueGradient_sq_integrable_of_x_finiteRange (s := s) hx_meas_t hx_fin_t
  exact
    integrable_sq_norm_sub hv_int_t.aestronglyMeasurable
      hgrad_int_t.aestronglyMeasurable hv_sq_t hgrad_sq_t

private theorem v_estimator_error_sq_sum_integrable_Icc {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} (h : FiniteHorizonAssumptions s T) :
    (letI := s.sampleMeasurable;
      Integrable
        (fun ω : Run s =>
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2))
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  refine MeasureTheory.integrable_finset_sum (s := Finset.Icc 1 T) ?_
  intro t ht
  exact v_estimator_error_sq_integrable_at (s := s) (T := T) h
    (Finset.mem_Icc.mp ht).1

private theorem lion_beta2_direction_integral_le_m_error_add_drift_budget
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t ≤ T) :
    (letI := s.sampleMeasurable;
      ∫ ω : Run s,
        ‖(1 - s.beta2) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2
        ∂Run.law s ≤
      (1 - s.beta2) *
        ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2) := by
  classical
  letI := s.sampleMeasurable
  let C : ℝ := 8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2
  have hleft_int :
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta2) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s) :=
    lion_eq6_direction_sq_integrable_beta2 (s := s) (T := T) h ht
  have hmerr_int :
      Integrable
        (fun ω : Run s => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        (Run.law s) :=
    m_estimator_error_sq_integrable_at (s := s) (T := T) h ht
  have hright_int :
      Integrable
        (fun ω : Run s =>
          (1 - s.beta2) *
            ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 + C)
        (Run.law s) :=
    (hmerr_int.const_mul (1 - s.beta2)).add (integrable_const (c := C))
  have hpoint : ∀ ω : Run s,
      ‖(1 - s.beta2) •
        (m s t ω - s.trueGradient (x s t ω) +
          (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2 ≤
      (1 - s.beta2) *
        ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 + C := by
    intro ω
    simpa [C] using
      lion_beta2_direction_sq_le_m_error_add_drift_budget
        (s := s) (T := T) hT h hdomains ht htT ω
  calc
    ∫ ω : Run s,
        ‖(1 - s.beta2) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2
        ∂Run.law s ≤
        ∫ ω : Run s,
          (1 - s.beta2) *
            ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 + C
          ∂Run.law s :=
      integral_mono hleft_int hright_int hpoint
    _ = (1 - s.beta2) *
        ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s + C := by
      rw [integral_add (hmerr_int.const_mul (1 - s.beta2)) (integrable_const (c := C))]
      rw [integral_const_mul]
      simp

private theorem lion_beta1_direction_integral_le_m_error_add_drift_budget
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t ≤ T) :
    (letI := s.sampleMeasurable;
      ∫ ω : Run s,
        ‖(1 - s.beta1) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2
        ∂Run.law s ≤
      (1 - s.beta1) *
        ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1) := by
  classical
  letI := s.sampleMeasurable
  let C : ℝ := 8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1
  have hleft_int :
      Integrable
        (fun ω : Run s =>
          ‖(1 - s.beta1) •
            (m s t ω - s.trueGradient (x s t ω) +
              (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2)
        (Run.law s) :=
    lion_eq6_direction_sq_integrable (s := s) (T := T) h ht
  have hmerr_int :
      Integrable
        (fun ω : Run s => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        (Run.law s) :=
    m_estimator_error_sq_integrable_at (s := s) (T := T) h ht
  have hright_int :
      Integrable
        (fun ω : Run s =>
          (1 - s.beta1) *
            ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 + C)
        (Run.law s) :=
    (hmerr_int.const_mul (1 - s.beta1)).add (integrable_const (c := C))
  have hpoint : ∀ ω : Run s,
      ‖(1 - s.beta1) •
        (m s t ω - s.trueGradient (x s t ω) +
          (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2 ≤
      (1 - s.beta1) *
        ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 + C := by
    intro ω
    simpa [C] using
      lion_beta1_direction_sq_le_m_error_add_drift_budget
        (s := s) (T := T) hT h hdomains ht htT ω
  calc
    ∫ ω : Run s,
        ‖(1 - s.beta1) •
          (m s t ω - s.trueGradient (x s t ω) +
            (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))‖ ^ 2
        ∂Run.law s ≤
        ∫ ω : Run s,
          (1 - s.beta1) *
            ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 + C
          ∂Run.law s :=
      integral_mono hleft_int hright_int hpoint
    _ = (1 - s.beta1) *
        ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s + C := by
      rw [integral_add (hmerr_int.const_mul (1 - s.beta1)) (integrable_const (c := C))]
      rw [integral_const_mul]
      simp

private theorem m_estimator_error_integral_recurrence_correctedDomain
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t + 1 ≤ T) :
    (letI := s.sampleMeasurable;
      ∫ ω : Run s, ‖m s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2
        ∂Run.law s ≤
      s.beta2 ^ 2 * s.sigma ^ 2 +
        ((1 - s.beta2) *
          ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2)) := by
  classical
  letI := s.sampleMeasurable
  let noise : Run s → Point d :=
    fun ω => G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)
  let direction : Run s → Point d :=
    fun ω =>
      (1 - s.beta2) •
        (m s t ω - s.trueGradient (x s t ω) +
          (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))
  obtain ⟨hx_next_meas, hx_next_fin, _hm_next_int, _hv_next_int⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased t
  have hG_next_int :
      Integrable (fun ω : Run s => G s (t + 1) ω) (Run.law s) := by
    simpa [G] using
      sampledGradient_integrable_of_finiteRange_query (s := s) (t := t + 1)
        (q := fun ω : Run s => x s (t + 1) ω)
        hx_next_meas hx_next_fin h.oracle_unbiased
  have hgrad_next_int :
      Integrable (fun ω : Run s => s.trueGradient (x s (t + 1) ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_next_meas hx_next_fin
  have hnoise_int : Integrable noise (Run.law s) := by
    simpa [noise] using hG_next_int.sub hgrad_next_int
  have hnoise_sq :=
    fresh_oracle_residual_sq_integrable_and_integral_le_for_lion_prefix
      (s := s) (T := T) h ht
  have hdirection_sq : Integrable (fun ω : Run s => ‖direction ω‖ ^ 2) (Run.law s) := by
    simpa [direction] using
      lion_eq6_direction_sq_integrable_beta2 (s := s) (T := T) h ht
  have hdirection_meas : AEStronglyMeasurable direction (Run.law s) := by
    obtain ⟨hx_t_meas0, hx_t_fin0, hm_t_int0, _hv_t_int0⟩ :=
      lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
    have htime : t - 1 + 1 = t := Nat.sub_add_cancel ht
    have hx_t_meas : AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
      simpa [htime] using hx_t_meas0
    have hx_t_fin : (Set.range (fun ω : Run s => x s t ω)).Finite := by
      simpa [htime] using hx_t_fin0
    have hm_t_int : Integrable (fun ω : Run s => m s t ω) (Run.law s) := by
      simpa [htime] using hm_t_int0
    have hgrad_t_int :
        Integrable (fun ω : Run s => s.trueGradient (x s t ω)) (Run.law s) :=
      trueGradient_integrable_of_x_finiteRange (s := s) hx_t_meas hx_t_fin
    have hdirection_int : Integrable direction (Run.law s) := by
      simpa [direction] using
        (MeasureTheory.Integrable.smul (1 - s.beta2)
          ((hm_t_int.sub hgrad_t_int).add (hgrad_t_int.sub hgrad_next_int)))
    exact hdirection_int.aestronglyMeasurable
  have hcross_zero :
      ∫ ω : Run s, ⟪noise ω, direction ω⟫_ℝ ∂Run.law s = 0 := by
    simpa [noise, direction] using
      fresh_oracle_residual_inner_integral_eq_zero_for_lion_prefix_beta2
        (s := s) (T := T) hT h hdomains ht htT
  have hnoise_decomp :
      ∫ ω : Run s, ‖s.beta2 • noise ω + direction ω‖ ^ 2 ∂Run.law s ≤
        s.beta2 ^ 2 * s.sigma ^ 2 +
          ∫ ω : Run s, ‖direction ω‖ ^ 2 ∂Run.law s :=
    integral_norm_sq_smul_add_le_of_inner_zero
      (μ := Run.law s) (a := s.beta2) (U := s.sigma ^ 2)
      hnoise_int.aestronglyMeasurable hdirection_meas hnoise_sq.1 hdirection_sq
      hnoise_sq.2 hcross_zero
  have hdir_bound :
      ∫ ω : Run s, ‖direction ω‖ ^ 2 ∂Run.law s ≤
        (1 - s.beta2) *
          ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2 := by
    simpa [direction] using
      lion_beta2_direction_integral_le_m_error_add_drift_budget
        (s := s) (T := T) hT h hdomains ht (by omega : t ≤ T)
  have hactual :
      (fun ω : Run s =>
        ‖m s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2) =ᵐ[
        Run.law s]
        fun ω => ‖s.beta2 • noise ω + direction ω‖ ^ 2 := by
    filter_upwards with ω
    rw [m_succ_estimator_error_decomp (s := s) ht ω]
  calc
    ∫ ω : Run s,
        ‖m s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2
        ∂Run.law s =
        ∫ ω : Run s, ‖s.beta2 • noise ω + direction ω‖ ^ 2 ∂Run.law s :=
      integral_congr_ae hactual
    _ ≤ s.beta2 ^ 2 * s.sigma ^ 2 +
        ∫ ω : Run s, ‖direction ω‖ ^ 2 ∂Run.law s := hnoise_decomp
    _ ≤ s.beta2 ^ 2 * s.sigma ^ 2 +
        ((1 - s.beta2) *
          ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hdir_bound (s.beta2 ^ 2 * s.sigma ^ 2)

private theorem v_estimator_error_integral_recurrence_correctedDomain
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T t : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (ht : 1 ≤ t) (htT : t + 1 ≤ T) :
    (letI := s.sampleMeasurable;
      ∫ ω : Run s, ‖v s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2
        ∂Run.law s ≤
      s.beta1 ^ 2 * s.sigma ^ 2 +
        ((1 - s.beta1) *
          ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1)) := by
  classical
  letI := s.sampleMeasurable
  let noise : Run s → Point d :=
    fun ω => G s (t + 1) ω - s.trueGradient (x s (t + 1) ω)
  let direction : Run s → Point d :=
    fun ω =>
      (1 - s.beta1) •
        (m s t ω - s.trueGradient (x s t ω) +
          (s.trueGradient (x s t ω) - s.trueGradient (x s (t + 1) ω)))
  obtain ⟨hx_next_meas, hx_next_fin, _hm_next_int, _hv_next_int⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased t
  have hG_next_int :
      Integrable (fun ω : Run s => G s (t + 1) ω) (Run.law s) := by
    simpa [G] using
      sampledGradient_integrable_of_finiteRange_query (s := s) (t := t + 1)
        (q := fun ω : Run s => x s (t + 1) ω)
        hx_next_meas hx_next_fin h.oracle_unbiased
  have hgrad_next_int :
      Integrable (fun ω : Run s => s.trueGradient (x s (t + 1) ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_next_meas hx_next_fin
  have hnoise_int : Integrable noise (Run.law s) := by
    simpa [noise] using hG_next_int.sub hgrad_next_int
  have hnoise_sq :=
    fresh_oracle_residual_sq_integrable_and_integral_le_for_lion_prefix
      (s := s) (T := T) h ht
  have hdirection_sq : Integrable (fun ω : Run s => ‖direction ω‖ ^ 2) (Run.law s) := by
    simpa [direction] using
      lion_eq6_direction_sq_integrable (s := s) (T := T) h ht
  have hdirection_meas : AEStronglyMeasurable direction (Run.law s) := by
    obtain ⟨hx_t_meas0, hx_t_fin0, hm_t_int0, _hv_t_int0⟩ :=
      lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
    have htime : t - 1 + 1 = t := Nat.sub_add_cancel ht
    have hx_t_meas : AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
      simpa [htime] using hx_t_meas0
    have hx_t_fin : (Set.range (fun ω : Run s => x s t ω)).Finite := by
      simpa [htime] using hx_t_fin0
    have hm_t_int : Integrable (fun ω : Run s => m s t ω) (Run.law s) := by
      simpa [htime] using hm_t_int0
    have hgrad_t_int :
        Integrable (fun ω : Run s => s.trueGradient (x s t ω)) (Run.law s) :=
      trueGradient_integrable_of_x_finiteRange (s := s) hx_t_meas hx_t_fin
    have hdirection_int : Integrable direction (Run.law s) := by
      simpa [direction] using
        (MeasureTheory.Integrable.smul (1 - s.beta1)
          ((hm_t_int.sub hgrad_t_int).add (hgrad_t_int.sub hgrad_next_int)))
    exact hdirection_int.aestronglyMeasurable
  have hcross_zero :
      ∫ ω : Run s, ⟪noise ω, direction ω⟫_ℝ ∂Run.law s = 0 := by
    simpa [noise, direction] using
      fresh_oracle_residual_inner_integral_eq_zero_for_lion_prefix
        (s := s) (T := T) hT h hdomains ht htT
  have hnoise_decomp :
      ∫ ω : Run s, ‖s.beta1 • noise ω + direction ω‖ ^ 2 ∂Run.law s ≤
        s.beta1 ^ 2 * s.sigma ^ 2 +
          ∫ ω : Run s, ‖direction ω‖ ^ 2 ∂Run.law s :=
    integral_norm_sq_smul_add_le_of_inner_zero
      (μ := Run.law s) (a := s.beta1) (U := s.sigma ^ 2)
      hnoise_int.aestronglyMeasurable hdirection_meas hnoise_sq.1 hdirection_sq
      hnoise_sq.2 hcross_zero
  have hdir_bound :
      ∫ ω : Run s, ‖direction ω‖ ^ 2 ∂Run.law s ≤
        (1 - s.beta1) *
          ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1 := by
    simpa [direction] using
      lion_beta1_direction_integral_le_m_error_add_drift_budget
        (s := s) (T := T) hT h hdomains ht (by omega : t ≤ T)
  have hactual :
      (fun ω : Run s =>
        ‖v s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2) =ᵐ[
        Run.law s]
        fun ω => ‖s.beta1 • noise ω + direction ω‖ ^ 2 := by
    filter_upwards with ω
    rw [v_succ_estimator_error_decomp (s := s) ht ω]
  calc
    ∫ ω : Run s,
        ‖v s (t + 1) ω - s.trueGradient (x s (t + 1) ω)‖ ^ 2
        ∂Run.law s =
        ∫ ω : Run s, ‖s.beta1 • noise ω + direction ω‖ ^ 2 ∂Run.law s :=
      integral_congr_ae hactual
    _ ≤ s.beta1 ^ 2 * s.sigma ^ 2 +
        ∫ ω : Run s, ‖direction ω‖ ^ 2 ∂Run.law s := hnoise_decomp
    _ ≤ s.beta1 ^ 2 * s.sigma ^ 2 +
        ((1 - s.beta1) *
          ∫ ω : Run s, ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hdir_bound (s.beta1 ^ 2 * s.sigma ^ 2)

private theorem m_estimator_error_sq_sum_integrable_Icc {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} (h : FiniteHorizonAssumptions s T) :
    (letI := s.sampleMeasurable;
      Integrable
        (fun ω : Run s =>
          (Finset.Icc 1 T).sum
            (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2))
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  refine MeasureTheory.integrable_finset_sum (s := Finset.Icc 1 T) ?_
  intro t ht
  exact m_estimator_error_sq_integrable_at (s := s) (T := T) h
    (Finset.mem_Icc.mp ht).1

private theorem finite_horizon_m_estimator_average_error_bound_division
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T) :
    (letI := s.sampleMeasurable;
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s) ≤
      s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          s.beta2 * s.sigma ^ 2 := by
  classical
  letI := s.sampleMeasurable
  rcases hdomains.1.1 with ⟨_hbeta1_pos, hbeta2_pos, _hbeta1_le_one, hbeta2_le_one⟩
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hbeta2_ne : s.beta2 ≠ 0 := ne_of_gt hbeta2_pos
  let C : ℝ := s.beta2 ^ 2 * s.sigma ^ 2 +
    8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta2
  let M : ℕ → ℝ := fun k =>
    ∫ ω : Run s,
      ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
      ∂Run.law s
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hM_nonneg : ∀ k, k ≤ T - 1 → 0 ≤ M k := by
    intro k _hk
    dsimp [M]
    exact integral_nonneg fun ω => sq_nonneg _
  have hstepM : ∀ k, k < T - 1 → M (k + 1) ≤ (1 - s.beta2) * M k + C := by
    intro k hk
    have ht : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have htT : k + 1 + 1 ≤ T := by omega
    have hrec :=
      m_estimator_error_integral_recurrence_correctedDomain
        (s := s) (T := T) hT h hdomains ht htT
    simpa [M, C, add_comm, add_left_comm, add_assoc] using hrec
  have hsum_range_sub :=
    sum_range_succ_le_inv_initial_add_inv_const_of_contraction
      (A := M) (N := T - 1) hbeta2_pos hbeta2_le_one hC_nonneg hM_nonneg hstepM
  have hsum_range :
      (Finset.range T).sum M ≤
        s.beta2⁻¹ * M 0 + (T : ℝ) * s.beta2⁻¹ * C := by
    simpa [Nat.sub_add_cancel hT] using hsum_range_sub
  have hinit :=
    initial_m_estimator_error_integrable_and_integral_le (s := s) h.oracle_bounded_noise
  have hinit_scaled : s.beta2⁻¹ * M 0 ≤ s.beta2⁻¹ * s.sigma ^ 2 := by
    exact mul_le_mul_of_nonneg_left (by simpa [M] using hinit.2)
      (inv_nonneg.mpr hbeta2_pos.le)
  have hsum_range_bound :
      (Finset.range T).sum M ≤
        s.beta2⁻¹ * s.sigma ^ 2 + (T : ℝ) * s.beta2⁻¹ * C := by
    have h := add_le_add_right hinit_scaled ((T : ℝ) * s.beta2⁻¹ * C)
    linarith
  have hintegral_sum :
      ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s =
        (Finset.range T).sum M := by
    calc
      ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s =
          (Finset.Icc 1 T).sum
            (fun t =>
              ∫ ω : Run s,
                ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s) := by
        rw [MeasureTheory.integral_finset_sum]
        intro t ht
        exact m_estimator_error_sq_integrable_at (s := s) (T := T) h
          (Finset.mem_Icc.mp ht).1
      _ = (Finset.range T).sum M := by
        rw [sum_Icc_one_eq_sum_range_succ]
  have hscaled :
      (T : ℝ)⁻¹ *
          ∫ ω : Run s,
            (Finset.Icc 1 T).sum
              (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
            ∂Run.law s ≤
        (T : ℝ)⁻¹ *
          (s.beta2⁻¹ * s.sigma ^ 2 + (T : ℝ) * s.beta2⁻¹ * C) := by
    rw [hintegral_sum]
    exact mul_le_mul_of_nonneg_left hsum_range_bound (inv_nonneg.mpr hT_pos.le)
  calc
    (T : ℝ)⁻¹ *
        ∫ ω : Run s,
          (Finset.Icc 1 T).sum
            (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
          ∂Run.law s ≤
        (T : ℝ)⁻¹ *
          (s.beta2⁻¹ * s.sigma ^ 2 + (T : ℝ) * s.beta2⁻¹ * C) := hscaled
    _ = s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          s.beta2 * s.sigma ^ 2 := by
      dsimp [C]
      field_simp [hT_ne, hbeta2_ne]
      ring

private theorem finite_horizon_m_estimator_average_error_bound_source
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ}
    {invBeta2T invBeta2Sq : ℝ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (hqT : sourceQuotient 1 (s.beta2 * (T : ℝ)) invBeta2T)
    (hqSq : sourceQuotient 1 (s.beta2 ^ 2) invBeta2Sq) :
    (letI := s.sampleMeasurable;
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s) ≤
      s.sigma ^ 2 * invBeta2T +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) * invBeta2Sq +
          s.beta2 * s.sigma ^ 2 := by
  classical
  letI := s.sampleMeasurable
  rcases hdomains.1.1 with ⟨_hbeta1_pos, hbeta2_pos, _hbeta1_le_one, _hbeta2_le_one⟩
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hbeta2_ne : s.beta2 ≠ 0 := ne_of_gt hbeta2_pos
  have hdiv :=
    finite_horizon_m_estimator_average_error_bound_division
      (s := s) (T := T) hT h hdomains
  calc
    (T : ℝ)⁻¹ *
        ∫ ω : Run s,
          (Finset.Icc 1 T).sum
            (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
          ∂Run.law s ≤
        s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
            s.beta2 * s.sigma ^ 2 := hdiv
    _ = s.sigma ^ 2 * invBeta2T +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) * invBeta2Sq +
          s.beta2 * s.sigma ^ 2 := by
      rw [sourceQuotient_eq_div hqT, sourceQuotient_eq_div hqSq]
      field_simp [hT_ne, hbeta2_ne]

private theorem finite_horizon_v_estimator_average_error_pre_bound
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T) :
    (letI := s.sampleMeasurable;
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s) ≤
      (T : ℝ)⁻¹ *
        (s.sigma ^ 2 +
          ((T - 1 : ℕ) : ℝ) *
            (s.beta1 ^ 2 * s.sigma ^ 2 +
              8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1) +
          (1 - s.beta1) *
            (Finset.range (T - 1)).sum
              (fun k =>
                ∫ ω : Run s,
                  ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
                  ∂Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  rcases hdomains.1.1 with ⟨hbeta1_pos, _hbeta2_pos, hbeta1_le_one, _hbeta2_le_one⟩
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  let C1 : ℝ := 8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1
  let V : ℕ → ℝ := fun k =>
    ∫ ω : Run s,
      ‖v s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
      ∂Run.law s
  let M : ℕ → ℝ := fun k =>
    ∫ ω : Run s,
      ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
      ∂Run.law s
  have hstepV :
      ∀ k, k < T - 1 →
        V (k + 1) ≤ s.beta1 ^ 2 * s.sigma ^ 2 + (1 - s.beta1) * M k + C1 := by
    intro k hk
    have ht : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have htT : k + 1 + 1 ≤ T := by omega
    have hrec :=
      v_estimator_error_integral_recurrence_correctedDomain
        (s := s) (T := T) hT h hdomains ht htT
    simpa [V, M, C1, add_assoc] using hrec
  have hsum_pre_sub :=
    sum_range_succ_le_head_add_tail_budget_of_lagged_recurrence
      (V := V) (M := M) (N := T - 1) (alpha := 1 - s.beta1)
      (B := s.beta1 ^ 2 * s.sigma ^ 2) (C := C1) hstepV
  have hsum_pre :
      (Finset.range T).sum V ≤
        V 0 + ((T - 1 : ℕ) : ℝ) *
          (s.beta1 ^ 2 * s.sigma ^ 2 + C1) +
            (1 - s.beta1) * (Finset.range (T - 1)).sum M := by
    simpa [Nat.sub_add_cancel hT] using hsum_pre_sub
  have hinit :=
    initial_v_estimator_error_integrable_and_integral_le (s := s) h.oracle_bounded_noise
  have hsum_bound :
      (Finset.range T).sum V ≤
        s.sigma ^ 2 + ((T - 1 : ℕ) : ℝ) *
          (s.beta1 ^ 2 * s.sigma ^ 2 + C1) +
            (1 - s.beta1) * (Finset.range (T - 1)).sum M := by
    have hinit' : V 0 ≤ s.sigma ^ 2 := by
      simpa [V] using hinit.2
    have h := add_le_add_right hinit'
      (((T - 1 : ℕ) : ℝ) * (s.beta1 ^ 2 * s.sigma ^ 2 + C1) +
        (1 - s.beta1) * (Finset.range (T - 1)).sum M)
    exact hsum_pre.trans (by linarith)
  have hintegral_sum :
      ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s =
        (Finset.range T).sum V := by
    calc
      ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s =
          (Finset.Icc 1 T).sum
            (fun t =>
              ∫ ω : Run s,
                ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s) := by
        rw [MeasureTheory.integral_finset_sum]
        intro t ht
        exact v_estimator_error_sq_integrable_at (s := s) (T := T) h
          (Finset.mem_Icc.mp ht).1
      _ = (Finset.range T).sum V := by
        rw [sum_Icc_one_eq_sum_range_succ]
  calc
    (T : ℝ)⁻¹ *
        ∫ ω : Run s,
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
          ∂Run.law s =
        (T : ℝ)⁻¹ * (Finset.range T).sum V := by
      rw [hintegral_sum]
    _ ≤ (T : ℝ)⁻¹ *
        (s.sigma ^ 2 +
          ((T - 1 : ℕ) : ℝ) *
            (s.beta1 ^ 2 * s.sigma ^ 2 + C1) +
          (1 - s.beta1) * (Finset.range (T - 1)).sum M) :=
      mul_le_mul_of_nonneg_left hsum_bound (inv_nonneg.mpr hT_pos.le)
    _ = (T : ℝ)⁻¹ *
        (s.sigma ^ 2 +
          ((T - 1 : ℕ) : ℝ) *
            (s.beta1 ^ 2 * s.sigma ^ 2 +
              8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1) +
          (1 - s.beta1) *
            (Finset.range (T - 1)).sum
              (fun k =>
                ∫ ω : Run s,
                  ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
                  ∂Run.law s)) := by
      rfl

private theorem finite_horizon_lagged_m_tail_average_le_m_bound_division
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T) :
    (letI := s.sampleMeasurable;
      (T : ℝ)⁻¹ *
        ((1 - s.beta1) *
          (Finset.range (T - 1)).sum
            (fun k =>
              ∫ ω : Run s,
                ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
                ∂Run.law s))) ≤
      s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          s.beta2 * s.sigma ^ 2 := by
  classical
  letI := s.sampleMeasurable
  rcases hdomains.1.1 with ⟨hbeta1_pos, _hbeta2_pos, hbeta1_le_one, _hbeta2_le_one⟩
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  let M : ℕ → ℝ := fun k =>
    ∫ ω : Run s,
      ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
      ∂Run.law s
  have htail_nonneg :
      0 ≤ (Finset.range (T - 1)).sum M := by
    exact Finset.sum_nonneg (by
      intro k _hk
      exact integral_nonneg fun ω => sq_nonneg _)
  have htail_le_full :
      (Finset.range (T - 1)).sum M ≤ (Finset.range T).sum M := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
    · intro k hk
      simp at hk ⊢
      omega
    · intro k hk_full _hk_not_tail
      dsimp [M]
      exact integral_nonneg fun ω => sq_nonneg _
  have hfactor_nonneg : 0 ≤ 1 - s.beta1 := sub_nonneg.mpr hbeta1_le_one
  have hfactor_le_one : 1 - s.beta1 ≤ 1 := by linarith
  have hweighted_tail_le_full :
      (1 - s.beta1) * (Finset.range (T - 1)).sum M ≤ (Finset.range T).sum M := by
    have hto_tail :
        (1 - s.beta1) * (Finset.range (T - 1)).sum M ≤
          1 * (Finset.range (T - 1)).sum M :=
      mul_le_mul_of_nonneg_right hfactor_le_one htail_nonneg
    linarith
  have hintegral_sum :
      ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s =
        (Finset.range T).sum M := by
    calc
      ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s =
          (Finset.Icc 1 T).sum
            (fun t =>
              ∫ ω : Run s,
                ‖m s t ω - s.trueGradient (x s t ω)‖ ^ 2 ∂Run.law s) := by
        rw [MeasureTheory.integral_finset_sum]
        intro t ht
        exact m_estimator_error_sq_integrable_at (s := s) (T := T) h
          (Finset.mem_Icc.mp ht).1
      _ = (Finset.range T).sum M := by
        rw [sum_Icc_one_eq_sum_range_succ]
  have hmavg :=
    finite_horizon_m_estimator_average_error_bound_division
      (s := s) (T := T) hT h hdomains
  have hmavg_range :
      (T : ℝ)⁻¹ * (Finset.range T).sum M ≤
        s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
            s.beta2 * s.sigma ^ 2 := by
    simpa [hintegral_sum] using hmavg
  calc
    (T : ℝ)⁻¹ *
        ((1 - s.beta1) *
          (Finset.range (T - 1)).sum
            (fun k =>
              ∫ ω : Run s,
                ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
                ∂Run.law s)) =
        (T : ℝ)⁻¹ * ((1 - s.beta1) * (Finset.range (T - 1)).sum M) := by
      rfl
    _ ≤ (T : ℝ)⁻¹ * (Finset.range T).sum M :=
      mul_le_mul_of_nonneg_left hweighted_tail_le_full (inv_nonneg.mpr hT_pos.le)
    _ ≤ s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          s.beta2 * s.sigma ^ 2 := hmavg_range

private theorem finite_horizon_v_non_m_budget_absorption_division
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T) :
    (T : ℝ)⁻¹ *
      (s.sigma ^ 2 +
        ((T - 1 : ℕ) : ℝ) *
          (s.beta1 ^ 2 * s.sigma ^ 2 +
            8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1)) ≤
      s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          s.beta2 * s.sigma ^ 2 := by
  classical
  rcases hdomains.1.1 with ⟨hbeta1_pos, hbeta2_pos, _hbeta1_le_one, hbeta2_le_one⟩
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hbeta1_ne : s.beta1 ≠ 0 := ne_of_gt hbeta1_pos
  have hbeta2_ne : s.beta2 ≠ 0 := ne_of_gt hbeta2_pos
  have hden2_pos : 0 < s.beta2 ^ 2 := by positivity
  let D : ℝ := 8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ)
  let tau : ℝ := (T : ℝ)⁻¹ * ((T - 1 : ℕ) : ℝ)
  have htau_nonneg : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have htau_le_one : tau ≤ 1 := by
    dsimp [tau]
    field_simp [hT_ne]
    exact_mod_cast Nat.sub_le T 1
  have hbeta1_sq_le_beta2 : s.beta1 ^ 2 ≤ s.beta2 := by
    have hsquare :=
      (sq_le_sq₀ hbeta1_pos.le (Real.sqrt_nonneg s.beta2)).2 h.momentum_order.2
    simpa [Real.sq_sqrt hbeta2_pos.le, pow_two] using hsquare
  have hinit_le :
      (T : ℝ)⁻¹ * s.sigma ^ 2 ≤ s.sigma ^ 2 / (s.beta2 * (T : ℝ)) := by
    field_simp [hT_ne, hbeta2_ne]
    nlinarith [hbeta2_le_one, sq_nonneg s.sigma]
  have hbeta_coef :
      tau * (s.beta1 ^ 2) ≤ s.beta2 := by
    have h1 : tau * (s.beta1 ^ 2) ≤ 1 * (s.beta1 ^ 2) :=
      mul_le_mul_of_nonneg_right htau_le_one (sq_nonneg s.beta1)
    have h2 : 1 * (s.beta1 ^ 2) ≤ 1 * s.beta2 :=
      mul_le_mul_of_nonneg_left hbeta1_sq_le_beta2 zero_le_one
    linarith
  have hbeta_noise :
      (T : ℝ)⁻¹ * (((T - 1 : ℕ) : ℝ) * (s.beta1 ^ 2 * s.sigma ^ 2)) ≤
        s.beta2 * s.sigma ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hbeta_coef (sq_nonneg s.sigma)
    dsimp [tau] at h
    nlinarith
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hD_div_beta1_le :
      D / s.beta1 ≤ D / (s.beta2 ^ 2) :=
    div_le_div_of_nonneg_left hD_nonneg hden2_pos h.momentum_order.1
  have hD_budget :
      (T : ℝ)⁻¹ * (((T - 1 : ℕ) : ℝ) * (D / s.beta1)) ≤
        D / (s.beta2 ^ 2) := by
    have h1 : tau * (D / s.beta1) ≤ 1 * (D / s.beta1) :=
      mul_le_mul_of_nonneg_right htau_le_one (by positivity)
    have h2 : 1 * (D / s.beta1) ≤ 1 * (D / (s.beta2 ^ 2)) :=
      mul_le_mul_of_nonneg_left hD_div_beta1_le zero_le_one
    dsimp [tau] at h1
    linarith
  calc
    (T : ℝ)⁻¹ *
      (s.sigma ^ 2 +
        ((T - 1 : ℕ) : ℝ) *
          (s.beta1 ^ 2 * s.sigma ^ 2 +
            8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1))
        =
      (T : ℝ)⁻¹ * s.sigma ^ 2 +
        (T : ℝ)⁻¹ * (((T - 1 : ℕ) : ℝ) * (s.beta1 ^ 2 * s.sigma ^ 2)) +
          (T : ℝ)⁻¹ * (((T - 1 : ℕ) : ℝ) * (D / s.beta1)) := by
      dsimp [D]
      ring
    _ ≤ s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        s.beta2 * s.sigma ^ 2 +
          D / (s.beta2 ^ 2) := by
      linarith
    _ = s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          s.beta2 * s.sigma ^ 2 := by
      dsimp [D]
      ring

private theorem finite_horizon_v_estimator_average_error_bound_division
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T) :
    (letI := s.sampleMeasurable;
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s) ≤
      2 * s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        16 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          2 * s.beta2 * s.sigma ^ 2 := by
  classical
  letI := s.sampleMeasurable
  let headBudget : ℝ :=
    s.sigma ^ 2 +
      ((T - 1 : ℕ) : ℝ) *
        (s.beta1 ^ 2 * s.sigma ^ 2 +
          8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / s.beta1)
  let mTail : ℝ :=
    (1 - s.beta1) *
      (Finset.range (T - 1)).sum
        (fun k =>
          ∫ ω : Run s,
            ‖m s (k + 1) ω - s.trueGradient (x s (k + 1) ω)‖ ^ 2
            ∂Run.law s)
  let mBound : ℝ :=
    s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
      8 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
        s.beta2 * s.sigma ^ 2
  have hpre :=
    finite_horizon_v_estimator_average_error_pre_bound
      (s := s) (T := T) hT h hdomains
  have hnonm :=
    finite_horizon_v_non_m_budget_absorption_division
      (s := s) (T := T) hT h hdomains
  have hmtail :=
    finite_horizon_lagged_m_tail_average_le_m_bound_division
      (s := s) (T := T) hT h hdomains
  calc
    (T : ℝ)⁻¹ *
        ∫ ω : Run s,
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
          ∂Run.law s ≤
        (T : ℝ)⁻¹ * (headBudget + mTail) := by
      simpa [headBudget, mTail] using hpre
    _ = (T : ℝ)⁻¹ * headBudget + (T : ℝ)⁻¹ * mTail := by ring
    _ ≤ mBound + mBound := by
      exact add_le_add (by simpa [headBudget, mBound] using hnonm)
        (by simpa [mTail, mBound] using hmtail)
    _ = 2 * s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
        16 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
          2 * s.beta2 * s.sigma ^ 2 := by
      dsimp [mBound]
      ring

private theorem finite_horizon_v_estimator_average_error_bound_source
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {T : ℕ} {estimatorBound : ℝ}
    (hT : 1 ≤ T) (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (hsrc : finiteHorizonEstimatorErrorBoundSource s T estimatorBound) :
    (letI := s.sampleMeasurable;
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s) ≤ estimatorBound := by
  classical
  letI := s.sampleMeasurable
  rcases hdomains.1.1 with ⟨_hbeta1_pos, hbeta2_pos, _hbeta1_le_one, _hbeta2_le_one⟩
  rcases hsrc with ⟨invBeta2T, invBeta2Sq, hqT, hqSq, rfl⟩
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hbeta2_ne : s.beta2 ≠ 0 := ne_of_gt hbeta2_pos
  have hdiv :=
    finite_horizon_v_estimator_average_error_bound_division
      (s := s) (T := T) hT h hdomains
  calc
    (T : ℝ)⁻¹ *
        ∫ ω : Run s,
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
          ∂Run.law s ≤
        2 * s.sigma ^ 2 / (s.beta2 * (T : ℝ)) +
          16 * s.eta ^ 2 * s.L ^ 2 * (d : ℝ) / (s.beta2 ^ 2) +
            2 * s.beta2 * s.sigma ^ 2 := hdiv
    _ = finiteHorizonEstimatorErrorBoundValue s T invBeta2T invBeta2Sq := by
      unfold finiteHorizonEstimatorErrorBoundValue
      rw [sourceQuotient_eq_div hqT, sourceQuotient_eq_div hqSq]
      field_simp [hT_ne, hbeta2_ne]

private theorem v_estimator_error_norm_integrable_at {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T t : ℕ} (h : FiniteHorizonAssumptions s T) (ht : 1 ≤ t) :
    (letI := s.sampleMeasurable;
      Integrable
        (fun ω : Run s => ‖v s t ω - s.trueGradient (x s t ω)‖)
        (Run.law s)) := by
  classical
  letI := s.sampleMeasurable
  obtain ⟨hx_meas0, hx_fin0, _hm_int0, hv_int0⟩ :=
    lion_process_x_finiteRange_and_state_integrable (s := s) h.oracle_unbiased (t - 1)
  have htime : t - 1 + 1 = t := Nat.sub_add_cancel ht
  have hx_meas_t : AEMeasurable (fun ω : Run s => x s t ω) (Run.law s) := by
    simpa [htime] using hx_meas0
  have hx_fin_t : (Set.range (fun ω : Run s => x s t ω)).Finite := by
    simpa [htime] using hx_fin0
  have hv_int_t : Integrable (fun ω : Run s => v s t ω) (Run.law s) := by
    simpa [htime] using hv_int0
  have hgrad_int_t :
      Integrable (fun ω : Run s => s.trueGradient (x s t ω)) (Run.law s) :=
    trueGradient_integrable_of_x_finiteRange (s := s) hx_meas_t hx_fin_t
  exact (hv_int_t.sub hgrad_int_t).norm

private theorem expected_average_norm_le_sqrt_average_second_moment_Icc {d : ℕ}
    [Nonempty (Fin d)] {s : Setup d} {T : ℕ} {estimatorBound : ℝ}
    (hT : 1 ≤ T) (h : FiniteHorizonAssumptions s T)
    (hsq :
      (letI := s.sampleMeasurable;
        (T : ℝ)⁻¹ * ∫ ω : Run s,
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
          ∂Run.law s) ≤ estimatorBound) :
    (letI := s.sampleMeasurable;
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
        ∂Run.law s) ≤ Real.sqrt estimatorBound := by
  classical
  letI := s.sampleMeasurable
  let sqAvg : Run s → ℝ := fun ω =>
    (T : ℝ)⁻¹ * (Finset.Icc 1 T).sum
      (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hsqSum_int :
      Integrable
        (fun ω : Run s =>
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2))
        (Run.law s) :=
    v_estimator_error_sq_sum_integrable_Icc (s := s) h
  have hsqAvg_int : Integrable sqAvg (Run.law s) := by
    simpa [sqAvg] using hsqSum_int.const_mul ((T : ℝ)⁻¹)
  have hsqAvg_nonneg : ∀ᵐ ω ∂Run.law s, 0 ≤ sqAvg ω := by
    exact ae_of_all _ fun ω => by
      dsimp [sqAvg]
      exact mul_nonneg (inv_nonneg.mpr hT_pos.le)
        (Finset.sum_nonneg fun t ht => sq_nonneg _)
  have hp : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hsqrt_int : Integrable (fun ω : Run s => Real.sqrt (sqAvg ω)) (Run.law s) := by
    have hpow_aesm :
        AEStronglyMeasurable
          (fun ω : Run s => Real.rpow (sqAvg ω) (1 / 2 : ℝ)) (Run.law s) :=
      (Real.continuous_rpow_const hp.1).comp_aestronglyMeasurable
        hsqAvg_int.aestronglyMeasurable
    have hmajorant_int : Integrable (fun ω : Run s => sqAvg ω + 1) (Run.law s) :=
      hsqAvg_int.add (integrable_const (c := (1 : ℝ)))
    have hrpow_int :
        Integrable
          (fun ω : Run s => Real.rpow (sqAvg ω) (1 / 2 : ℝ)) (Run.law s) := by
      refine hmajorant_int.mono' hpow_aesm ?_
      filter_upwards [hsqAvg_nonneg] with ω hω
      have hpow_nonneg : 0 ≤ Real.rpow (sqAvg ω) (1 / 2 : ℝ) :=
        Real.rpow_nonneg hω _
      rw [Real.norm_of_nonneg hpow_nonneg]
      exact rpow_le_self_add_one_of_nonneg_of_mem_Icc hω hp
    simpa [Real.sqrt_eq_rpow] using hrpow_int
  have hnormSum_int :
      Integrable
        (fun ω : Run s =>
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖))
        (Run.law s) := by
    refine MeasureTheory.integrable_finset_sum (s := Finset.Icc 1 T) ?_
    intro t ht
    exact v_estimator_error_norm_integrable_at (s := s) (T := T) h
      (Finset.mem_Icc.mp ht).1
  have hleft_int :
      Integrable
        (fun ω : Run s =>
          (T : ℝ)⁻¹ * (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖))
        (Run.law s) := by
    simpa using hnormSum_int.const_mul ((T : ℝ)⁻¹)
  have hpoint : ∀ ω : Run s,
      (T : ℝ)⁻¹ * (Finset.Icc 1 T).sum
        (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖) ≤ Real.sqrt (sqAvg ω) := by
    intro ω
    let A : ℝ := (Finset.Icc 1 T).sum
      (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
    let B : ℝ := (Finset.Icc 1 T).sum
      (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
    have hcard_nat : (Finset.Icc 1 T).card = T := by
      rw [Nat.card_Icc]
      omega
    have hcard : ((Finset.Icc 1 T).card : ℝ) = (T : ℝ) := by
      exact_mod_cast hcard_nat
    have hcs : A ^ 2 ≤ (T : ℝ) * B := by
      have hraw := sq_sum_le_card_mul_sum_sq
        (s := Finset.Icc 1 T)
        (f := fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
      simpa [A, B, hcard] using hraw
    have hsq_le : ((T : ℝ)⁻¹ * A) ^ 2 ≤ (T : ℝ)⁻¹ * B := by
      field_simp [hT_ne]
      nlinarith [hcs]
    have hsqrt_arg : sqAvg ω = (T : ℝ)⁻¹ * B := by
      rfl
    rw [hsqrt_arg]
    exact Real.le_sqrt_of_sq_le hsq_le
  have hpoint_int :
      (∫ ω : Run s,
        (T : ℝ)⁻¹ * (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
        ∂Run.law s) ≤ ∫ ω : Run s, Real.sqrt (sqAvg ω) ∂Run.law s := by
    exact integral_mono hleft_int hsqrt_int hpoint
  have hsqAvg_le : (∫ ω : Run s, sqAvg ω ∂Run.law s) ≤ estimatorBound := by
    calc
      (∫ ω : Run s, sqAvg ω ∂Run.law s) =
          (T : ℝ)⁻¹ * ∫ ω : Run s,
            (Finset.Icc 1 T).sum
              (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
            ∂Run.law s := by
        simp [sqAvg, integral_const_mul]
      _ ≤ estimatorBound := hsq
  have hJensen_rpow :=
    integral_rpow_le_rpow_of_integrable_nonneg_of_integral_le
      (P := Run.law s) (Z := sqAvg) (p := (1 / 2 : ℝ)) (B := estimatorBound)
      hsqAvg_int hsqAvg_nonneg hp hsqAvg_le
  have hJensen :
      (∫ ω : Run s, Real.sqrt (sqAvg ω) ∂Run.law s) ≤ Real.sqrt estimatorBound := by
    simpa [Real.sqrt_eq_rpow] using hJensen_rpow
  calc
    (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
        ∂Run.law s
        = ∫ ω : Run s,
          (T : ℝ)⁻¹ * (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
          ∂Run.law s := by
      rw [integral_const_mul]
    _ ≤ ∫ ω : Run s, Real.sqrt (sqAvg ω) ∂Run.law s := hpoint_int
    _ ≤ Real.sqrt estimatorBound := hJensen

private theorem finite_horizon_gradient_sum_pathwise_le_delta_add_error {d : ℕ}
    [Nonempty (Fin d)] {s : Setup d} {T : ℕ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T) (ω : Run s) :
    (s.eta / 2) * gradientL1Sum s T ω ≤
      s.Delta_f +
        2 * s.eta * Real.sqrt (d : ℝ) *
          (Finset.Icc 1 T).sum
            (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖) +
        (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) := by
  classical
  have hdrop :
      (Finset.Icc 1 T).sum
          (fun t => s.f (x s t ω) - s.f (x s (t + 1) ω)) ≤ s.Delta_f := by
    have htelescope :=
      sum_Icc_sub_succ (fun n : ℕ => s.f (x s n ω)) 1 T hT
    have hx1 : x s 1 ω = s.x1 := by
      simp [x, stateAt, process]
    have htail :
        s.fStar ≤ s.f (x s (T + 1) ω) := by
      exact (Setup.initialGap_fStar_is_glb h.initial_gap).1
        ⟨x s (T + 1) ω, rfl⟩
    calc
      (Finset.Icc 1 T).sum
          (fun t => s.f (x s t ω) - s.f (x s (t + 1) ω))
          = s.f (x s 1 ω) - s.f (x s (T + 1) ω) := htelescope
      _ = s.f s.x1 - s.f (x s (T + 1) ω) := by rw [hx1]
      _ ≤ s.f s.x1 - s.fStar := sub_le_sub_left htail (s.f s.x1)
      _ ≤ s.Delta_f := Setup.initialGap_bound h.initial_gap
  have hpoint : ∀ t ∈ Finset.Icc 1 T,
      (s.eta / 2) * l1Norm (s.trueGradient (x s t ω)) ≤
        (s.f (x s t ω) - s.f (x s (t + 1) ω)) +
          (2 * s.eta * Real.sqrt (d : ℝ) *
            ‖v s t ω - s.trueGradient (x s t ω)‖ +
            2 * s.eta ^ 2 * s.L * (d : ℝ)) := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
    have hstep :=
      lion_one_step_l1_descent_bound_correctedDomain
        (s := s) (T := T) (t := t) hT h hdomains ht1 htT ω
    have hstep' :
        s.f (x s (t + 1) ω) ≤
          s.f (x s t ω) +
            2 * s.eta * Real.sqrt (d : ℝ) *
              ‖v s t ω - s.trueGradient (x s t ω)‖ -
            (s.eta / 2) * l1Norm (s.trueGradient (x s t ω)) +
            2 * s.eta ^ 2 * s.L * (d : ℝ) := by
      simpa [norm_sub_rev] using hstep
    nlinarith
  have hagg :=
    SOptLib.finset_const_mul_sum_le_telescope_add_sum_of_pointwise_le
      (s := Finset.Icc 1 T) (c := s.eta / 2) (budget := s.Delta_f)
      (gap := fun t => l1Norm (s.trueGradient (x s t ω)))
      (drop := fun t => s.f (x s t ω) - s.f (x s (t + 1) ω))
      (noise := fun t =>
        2 * s.eta * Real.sqrt (d : ℝ) *
          ‖v s t ω - s.trueGradient (x s t ω)‖ +
          2 * s.eta ^ 2 * s.L * (d : ℝ))
      hpoint hdrop
  have hcard_nat : (Finset.Icc 1 T).card = T := by
    rw [Nat.card_Icc]
    omega
  have hcard : ((Finset.Icc 1 T).card : ℝ) = (T : ℝ) := by
    exact_mod_cast hcard_nat
  simpa [gradientL1Sum, Finset.sum_add_distrib, Finset.mul_sum, hcard,
    mul_assoc, add_assoc] using hagg

private theorem finite_horizon_gradient_average_descent_pre_bound_correctedDomain {d : ℕ}
    [Nonempty (Fin d)] {s : Setup d} {T : ℕ} {invEtaT : ℝ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hdomains : finiteHorizonCorrectedDomainObligations s T)
    (hqEta : sourceQuotient 1 (s.eta * (T : ℝ)) invEtaT) :
    averageExpectedGradientL1 s T ≤
      2 * s.Delta_f * invEtaT +
        4 * Real.sqrt (d : ℝ) *
          ((T : ℝ)⁻¹ * ∫ ω : Run s,
            (Finset.Icc 1 T).sum
              (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
            ∂Run.law s) +
        4 * s.eta * s.L * (d : ℝ) := by
  classical
  letI := s.sampleMeasurable
  obtain ⟨heta_pos, _hcontr, _heta_quot⟩ := hdomains.2
  have hT_pos_nat : 0 < T := lt_of_lt_of_le Nat.zero_lt_one hT
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast hT_pos_nat
  have heta_ne : s.eta ≠ 0 := ne_of_gt heta_pos
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hetaT_pos : 0 < s.eta * (T : ℝ) := mul_pos heta_pos hT_pos
  have hscale_nonneg : 0 ≤ 2 * invEtaT := by
    rw [sourceQuotient_eq_div hqEta]
    positivity
  let errSum : Run s → ℝ := fun ω =>
    (Finset.Icc 1 T).sum
      (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
  have hgrad_int :
      Integrable (gradientL1Sum s T) (Run.law s) :=
    gradientL1Sum_integrable_from_finiteHorizonAssumptions
      (s := s) (T := T) hT h
  have herr_int : Integrable errSum (Run.law s) := by
    dsimp [errSum]
    refine MeasureTheory.integrable_finset_sum (s := Finset.Icc 1 T) ?_
    intro t ht
    exact v_estimator_error_norm_integrable_at (s := s) (T := T) h
      (Finset.mem_Icc.mp ht).1
  have hpoint : ∀ ω : Run s,
      (s.eta / 2) * gradientL1Sum s T ω ≤
        s.Delta_f +
          2 * s.eta * Real.sqrt (d : ℝ) * errSum ω +
          (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) := by
    intro ω
    simpa [errSum, add_assoc] using
      finite_horizon_gradient_sum_pathwise_le_delta_add_error
        (s := s) (T := T) hT h hdomains ω
  have hint_raw :
      ∫ ω : Run s, (s.eta / 2) * gradientL1Sum s T ω ∂Run.law s ≤
        ∫ ω : Run s,
          s.Delta_f +
            2 * s.eta * Real.sqrt (d : ℝ) * errSum ω +
            (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) ∂Run.law s := by
    refine integral_mono (hgrad_int.const_mul (s.eta / 2)) ?_ hpoint
    exact ((integrable_const (c := s.Delta_f)).add
      (herr_int.const_mul (2 * s.eta * Real.sqrt (d : ℝ)))).add
      (integrable_const (c := (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ))))
  have hint :
      (s.eta / 2) * ∫ ω : Run s, gradientL1Sum s T ω ∂Run.law s ≤
        s.Delta_f +
          2 * s.eta * Real.sqrt (d : ℝ) *
            ∫ ω : Run s, errSum ω ∂Run.law s +
          (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) := by
    calc
      (s.eta / 2) * ∫ ω : Run s, gradientL1Sum s T ω ∂Run.law s
          = ∫ ω : Run s, (s.eta / 2) * gradientL1Sum s T ω ∂Run.law s := by
        rw [integral_const_mul]
      _ ≤ ∫ ω : Run s,
          s.Delta_f +
            2 * s.eta * Real.sqrt (d : ℝ) * errSum ω +
            (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) ∂Run.law s := hint_raw
      _ = s.Delta_f +
          2 * s.eta * Real.sqrt (d : ℝ) *
            ∫ ω : Run s, errSum ω ∂Run.law s +
          (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) := by
        let coeff : ℝ := 2 * s.eta * Real.sqrt (d : ℝ)
        let constTerm : ℝ := (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ))
        have hcoeff_int : Integrable (fun ω : Run s => coeff * errSum ω) (Run.law s) :=
          herr_int.const_mul coeff
        have hconst_int : Integrable (fun _ω : Run s => constTerm) (Run.law s) :=
          integrable_const (c := constTerm)
        calc
          (∫ ω : Run s,
              s.Delta_f +
                2 * s.eta * Real.sqrt (d : ℝ) * errSum ω +
                (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) ∂Run.law s)
              = ∫ ω : Run s, s.Delta_f + (coeff * errSum ω + constTerm) ∂Run.law s := by
            simp [coeff, constTerm]
            ring
          _ = (∫ _ω : Run s, s.Delta_f ∂Run.law s) +
              ∫ ω : Run s, coeff * errSum ω + constTerm ∂Run.law s := by
            simpa using
              (integral_add (integrable_const (c := s.Delta_f))
                (hcoeff_int.add hconst_int))
          _ = (∫ _ω : Run s, s.Delta_f ∂Run.law s) +
              ((∫ ω : Run s, coeff * errSum ω ∂Run.law s) +
                ∫ _ω : Run s, constTerm ∂Run.law s) := by
            rw [integral_add hcoeff_int hconst_int]
          _ = s.Delta_f +
              2 * s.eta * Real.sqrt (d : ℝ) *
                ∫ ω : Run s, errSum ω ∂Run.law s +
              (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ)) := by
            simp [coeff, constTerm, integral_const_mul, integral_const, probReal_univ,
              add_assoc]
  have hscaled := mul_le_mul_of_nonneg_left hint hscale_nonneg
  calc
    averageExpectedGradientL1 s T =
        (2 * invEtaT) *
          ((s.eta / 2) *
            ∫ ω : Run s, gradientL1Sum s T ω ∂Run.law s) := by
      rw [averageExpectedGradientL1, sourceQuotient_eq_div hqEta]
      field_simp [heta_ne, hT_ne]
    _ ≤ (2 * invEtaT) *
        (s.Delta_f +
          2 * s.eta * Real.sqrt (d : ℝ) *
            ∫ ω : Run s, errSum ω ∂Run.law s +
          (T : ℝ) * (2 * s.eta ^ 2 * s.L * (d : ℝ))) := hscaled
    _ = 2 * s.Delta_f * invEtaT +
        4 * Real.sqrt (d : ℝ) *
          ((T : ℝ)⁻¹ * ∫ ω : Run s, errSum ω ∂Run.law s) +
        4 * s.eta * s.L * (d : ℝ) := by
      rw [sourceQuotient_eq_div hqEta]
      field_simp [heta_ne, hT_ne]
      ring

/-- Corrected-domain Appendix B finite-horizon inequality for the generated centralized
original Lion process.

Book citation: `book/research/Lion.json#/main_theorem/proof[step=30]`, the displayed
finite-horizon bound before the asymptotic simplification.  The extra quotient/contraction
contract records source gaps and must not be treated as the unqualified paper inequality. -/
theorem finite_horizon_gradient_average_bound_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {T : ℕ} {bound : ℝ} (hT : 1 ≤ T)
    (h : FiniteHorizonAssumptions s T)
    (hbound : finiteHorizonCorrectedBoundContract s T bound) :
    averageExpectedGradientL1 s T ≤ bound := by
  classical
  letI := s.sampleMeasurable
  rcases hbound with ⟨hdomains, hgradSrc⟩
  rcases hgradSrc with ⟨invEtaT, estimatorBound, hqEta, hestSrc, rfl⟩
  have hvavg :
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖ ^ 2)
        ∂Run.law s ≤ estimatorBound :=
    finite_horizon_v_estimator_average_error_bound_source
      (s := s) (T := T) hT h hdomains hestSrc
  have hvL1 :
      (T : ℝ)⁻¹ * ∫ ω : Run s,
        (Finset.Icc 1 T).sum
          (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
        ∂Run.law s ≤ Real.sqrt estimatorBound :=
    expected_average_norm_le_sqrt_average_second_moment_Icc
      (s := s) (T := T) hT h hvavg
  have hpre :
      averageExpectedGradientL1 s T ≤
        2 * s.Delta_f * invEtaT +
          4 * Real.sqrt (d : ℝ) *
            ((T : ℝ)⁻¹ * ∫ ω : Run s,
              (Finset.Icc 1 T).sum
                (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
              ∂Run.law s) +
          4 * s.eta * s.L * (d : ℝ) :=
    finite_horizon_gradient_average_descent_pre_bound_correctedDomain
      (s := s) (T := T) (invEtaT := invEtaT) hT h hdomains hqEta
  have hcoeff_nonneg : 0 ≤ 4 * Real.sqrt (d : ℝ) := by
    positivity
  have herr :
      4 * Real.sqrt (d : ℝ) *
          ((T : ℝ)⁻¹ * ∫ ω : Run s,
            (Finset.Icc 1 T).sum
              (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
            ∂Run.law s) ≤
        4 * Real.sqrt (d : ℝ) * Real.sqrt estimatorBound :=
    mul_le_mul_of_nonneg_left hvL1 hcoeff_nonneg
  calc
    averageExpectedGradientL1 s T ≤
        2 * s.Delta_f * invEtaT +
          4 * Real.sqrt (d : ℝ) *
            ((T : ℝ)⁻¹ * ∫ ω : Run s,
              (Finset.Icc 1 T).sum
                (fun t => ‖v s t ω - s.trueGradient (x s t ω)‖)
              ∂Run.law s) +
          4 * s.eta * s.L * (d : ℝ) := hpre
    _ ≤ finiteHorizonGradientBoundValue s T invEtaT estimatorBound := by
      unfold finiteHorizonGradientBoundValue
      nlinarith [herr]

/-- The finite-horizon average produced by a horizon-dependent parameter schedule. -/
def scheduledAverageExpectedGradientL1 {d : ℕ} (s : Setup d) (p : ParameterSchedule) :
    ℕ → ℝ :=
  fun T => averageExpectedGradientL1 (p.setupAt s T) T

private theorem scheduledAverageExpectedGradientL1_le_canonicalBound {d : ℕ}
    [Nonempty (Fin d)] {s : Setup d} {p : ParameterSchedule} {T : ℕ}
    (hT : 1 ≤ T) (h : theoremOne_correctedRateAssumptions s p) :
    scheduledAverageExpectedGradientL1 s p T ≤ theoremOneCanonicalGradientBound s p T := by
  have hFH : FiniteHorizonAssumptions (p.setupAt s T) T :=
    finiteHorizonAssumptions_of_schedule (s := s) (p := p) hT h.printed
  have hbound :
      finiteHorizonCorrectedBoundContract (p.setupAt s T) T
        (theoremOneCanonicalGradientBound s p T) :=
    finiteHorizonCorrectedBoundContract_canonical (s := s) (p := p) hT h.domains
  exact finite_horizon_gradient_average_bound_correctedDomain
    (s := p.setupAt s T) (T := T) hT hFH hbound

private theorem theoremOneCanonicalGradientBound_isBigO_of_correctedRateAssumptions
    {d : ℕ} [Nonempty (Fin d)] {s : Setup d} {p : ParameterSchedule}
    (h : theoremOne_correctedRateAssumptions s p) :
    Asymptotics.IsBigO Filter.atTop
      (theoremOneCanonicalGradientBound s p) (theoremOneRateScale d) := by
  classical
  have hsqrtBeta_to_rate :
      Asymptotics.IsBigO Filter.atTop
        (fun T => Real.sqrt (beta2AsymptoticScale T)) (theoremOneRateScale d) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hTpos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
    have hsqrtTpos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTpos
    have hleft_nonneg : 0 ≤ Real.sqrt (beta2AsymptoticScale T) := Real.sqrt_nonneg _
    have hdpos_nat0 : 0 < d := Fin.pos_iff_nonempty.mpr inferInstance
    have hdpos_nat : 1 ≤ d := hdpos_nat0
    have hsqrtd_ge_one : 1 ≤ Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hdpos_nat)
    have hden_nonneg : 0 ≤ Real.sqrt (Real.sqrt (T : ℝ)) := Real.sqrt_nonneg _
    have hright_nonneg : 0 ≤ theoremOneRateScale d T :=
      div_nonneg (Real.sqrt_nonneg _) hden_nonneg
    rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
    dsimp [theoremOneRateScale, beta2AsymptoticScale]
    rw [Real.sqrt_inv]
    simpa [one_div] using div_le_div_of_nonneg_right hsqrtd_ge_one hden_nonneg
  have heta_to_rate :
      Asymptotics.IsBigO Filter.atTop (etaAsymptoticScale d) (theoremOneRateScale d) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hTpos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
    have hdenTpos : 0 < Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) := by
      refine Real.sqrt_pos.2 ?_
      exact Real.sqrt_pos.2 (pow_pos hTpos 3)
    have hdpos_nat0 : 0 < d := Fin.pos_iff_nonempty.mpr inferInstance
    have hdpos_nat : 1 ≤ d := hdpos_nat0
    have hdpos : 0 < (d : ℝ) := by
      exact_mod_cast hdpos_nat0
    have hsqrtd_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
    have hsqrtd_nonneg : 0 ≤ Real.sqrt (d : ℝ) := le_of_lt hsqrtd_pos
    have hleft_nonneg : 0 ≤ etaAsymptoticScale d T := by
      dsimp [etaAsymptoticScale]
      exact inv_nonneg.mpr (mul_nonneg hsqrtd_nonneg (le_of_lt hdenTpos))
    have hright_nonneg : 0 ≤ theoremOneRateScale d T := by
      dsimp [theoremOneRateScale]
      exact div_nonneg hsqrtd_nonneg (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
    dsimp [etaAsymptoticScale, theoremOneRateScale]
    have hden_ne : Real.sqrt (d : ℝ) * Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) ≠ 0 := by
      positivity
    have hden_rate_ne : Real.sqrt (Real.sqrt (T : ℝ)) ≠ 0 := by
      positivity
    have hT_le_cube : (T : ℝ) ≤ (T : ℝ) ^ 3 := by
      have h1 : (1 : ℝ) ≤ (T : ℝ) := by
        exact_mod_cast hT
      have hsq : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((T : ℝ) - 1), h1]
      have hmul := mul_le_mul_of_nonneg_left hsq (le_of_lt hTpos)
      simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul
    have ha_le_b :
        Real.sqrt (Real.sqrt (T : ℝ)) ≤
          Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) := by
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hT_le_cube)
    have hone_le_csq : 1 ≤ (Real.sqrt (d : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt hdpos)]
      exact_mod_cast hdpos_nat
    have hb_nonneg : 0 ≤ Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) := Real.sqrt_nonneg _
    field_simp [hden_ne, hden_rate_ne]
    calc
      Real.sqrt (Real.sqrt (T : ℝ)) ≤
          Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) := ha_le_b
      _ = 1 * Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) := by ring
      _ ≤ (Real.sqrt (d : ℝ)) ^ 2 * Real.sqrt (Real.sqrt ((T : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hone_le_csq hb_nonneg
  have hestimator_to_beta :
      Asymptotics.IsBigO Filter.atTop
        (theoremOneCanonicalEstimatorBound s p) beta2AsymptoticScale := by
    have hterm1 :
        Asymptotics.IsBigO Filter.atTop
          (fun T => 2 * s.sigma ^ 2 * (((p.beta2 T) * (T : ℝ))⁻¹))
          beta2AsymptoticScale := by
      have hscale := h.beta2T_reciprocal_schedule.const_mul_left (2 * s.sigma ^ 2)
      refine hscale.congr_left ?_
      intro T
      ring_nf
    have hterm2 :
        Asymptotics.IsBigO Filter.atTop
          (fun T => 16 * (p.eta T) ^ 2 * s.L ^ 2 * (d : ℝ) *
            (((p.beta2 T) ^ 2)⁻¹)) beta2AsymptoticScale := by
      have hscale :=
        (theoremOne_eta_sq_beta2_sq_schedule_from_smaller_schedules_attempt
          (s := s) (p := p) h.printed h.beta2T_reciprocal_schedule).const_mul_left
          (16 * s.L ^ 2)
      refine hscale.congr_left ?_
      intro T
      ring
    have hterm3 :
        Asymptotics.IsBigO Filter.atTop
          (fun T => 2 * p.beta2 T * s.sigma ^ 2) beta2AsymptoticScale := by
      have hscale := h.printed.beta2_schedule.const_mul_left (2 * s.sigma ^ 2)
      refine hscale.congr_left ?_
      intro T
      ring
    have hsum := hterm1.add (hterm2.add hterm3)
    refine hsum.congr_left ?_
    intro T
    simp [theoremOneCanonicalEstimatorBound, finiteHorizonEstimatorErrorBoundValue,
      ParameterSchedule.setupAt, Setup.withParameters]
    ring
  have hsqrtEstimator_to_rate :
      Asymptotics.IsBigO Filter.atTop
        (fun T => Real.sqrt (theoremOneCanonicalEstimatorBound s p T))
        (theoremOneRateScale d) :=
    (hestimator_to_beta.sqrt (by
      exact Filter.Eventually.of_forall fun T => inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
      hsqrtBeta_to_rate
  have hterm_delta :
      Asymptotics.IsBigO Filter.atTop
        (fun T => 2 * s.Delta_f * (((p.eta T) * (T : ℝ))⁻¹))
        (theoremOneRateScale d) := by
    simpa [mul_assoc] using h.etaT_reciprocal_schedule.const_mul_left (2 * s.Delta_f)
  have hterm_error :
      Asymptotics.IsBigO Filter.atTop
        (fun T => 4 * Real.sqrt (d : ℝ) *
          Real.sqrt (theoremOneCanonicalEstimatorBound s p T))
        (theoremOneRateScale d) := by
    simpa [mul_assoc] using
      hsqrtEstimator_to_rate.const_mul_left (4 * Real.sqrt (d : ℝ))
  have hterm_eta :
      Asymptotics.IsBigO Filter.atTop
        (fun T => 4 * p.eta T * s.L * (d : ℝ))
        (theoremOneRateScale d) := by
    have heta_rate : Asymptotics.IsBigO Filter.atTop p.eta (theoremOneRateScale d) :=
      h.printed.eta_schedule.trans heta_to_rate
    have hscale := heta_rate.const_mul_left (4 * s.L * (d : ℝ))
    refine hscale.congr_left ?_
    intro T
    ring
  have hsum := hterm_delta.add (hterm_error.add hterm_eta)
  refine hsum.congr_left ?_
  intro T
  simp [theoremOneCanonicalGradientBound, finiteHorizonGradientBoundValue,
    ParameterSchedule.setupAt, Setup.withParameters]
  ring

/-- The printed Theorem 1 asymptotic conclusion as a proposition.

This is the exact source-stated conclusion.  It is kept separate from the proof-carrying
corrected-rate theorem because the printed one-sided schedule assumptions do not expose the
reciprocal controls used in Appendix B's final display. -/
def theoremOnePrintedAsymptoticConclusion {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (p : ParameterSchedule) : Prop :=
  Asymptotics.IsBigO Filter.atTop
    (scheduledAverageExpectedGradientL1 s p) (theoremOneRateScale d)

private theorem theoremOneShiftedQuadraticSetupAt_trueGradient_eq (T : ℕ) (x : Point 1) :
    (theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T).trueGradient x =
      x - theoremOneUnitPoint := by
  unfold Setup.trueGradient ParameterSchedule.setupAt Setup.withParameters
    theoremOneShiftedQuadraticSetup
  simpa using
    (hasGradientAt_const_mul_norm_sub_sq_centered (1 : ℝ) theoremOneUnitPoint x).gradient

private theorem theoremOneShiftedQuadraticPositiveSlowSetupAt_trueGradient_eq
    (T : ℕ) (x : Point 1) :
    (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T).trueGradient x =
      x - theoremOneUnitPoint := by
  unfold Setup.trueGradient ParameterSchedule.setupAt Setup.withParameters
    theoremOneShiftedQuadraticSetup
  simpa using
    (hasGradientAt_const_mul_norm_sub_sq_centered (1 : ℝ) theoremOneUnitPoint x).gradient

private theorem positiveSlow_eta_mul_time_le_half {T t : ℕ}
    (hT : 1 ≤ T) (htT : t ≤ T) :
    (((T : ℝ) + 1) ^ 2)⁻¹ * (t : ℝ) ≤ 1 / 2 := by
  have hden_pos : 0 < ((T : ℝ) + 1) ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hden_pos]
  have ht_real : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
  have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
  nlinarith [ht_real, sq_nonneg ((T : ℝ) - 1), hT_nonneg]

private theorem theoremOnePositiveSlow_etaLambdaDomain (T : ℕ) (hT : 1 ≤ T) :
    EtaLambdaHorizonDomainAt
      (theoremOnePositiveSlowSchedule.eta T) (theoremOnePositiveSlowSchedule.lambda T) T := by
  refine ⟨?heta_pos, ?hcontract, ?hquot⟩
  · simpa [theoremOnePositiveSlowSchedule] using positiveSlowValue_pos T
  · simp [EtaLambdaContractionDomainAt, theoremOnePositiveSlowSchedule]
  · refine ⟨1 / (theoremOnePositiveSlowSchedule.eta T * (T : ℝ)), ?_⟩
    have hden : theoremOnePositiveSlowSchedule.eta T * (T : ℝ) ≠ 0 := by
      have heta : theoremOnePositiveSlowSchedule.eta T ≠ 0 := by
        exact ne_of_gt (by simpa [theoremOnePositiveSlowSchedule] using positiveSlowValue_pos T)
      have hTne : (T : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hT))
      exact mul_ne_zero heta hTne
    exact SOptLib.checked_quotient_spec_div_of_den_ne (K := ℝ) (1 : ℝ) hden

private theorem theoremOnePositiveSlowSetupAt_linf_le_half {T t : ℕ}
    (hT : 1 ≤ T) (ht : 1 ≤ t) (htT : t ≤ T)
    (ω : Run (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T)) :
    linfNorm (x (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T)
      t ω) ≤ 1 / 2 := by
  have hFH : FiniteHorizonAssumptions
      (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T) T :=
    finiteHorizonAssumptions_of_schedule (s := theoremOneShiftedQuadraticSetup)
      (p := theoremOnePositiveSlowSchedule) hT
      theoremOne_shiftedQuadratic_positiveSlow_printedScheduleAssumptions
  have hlem :
      lemmaOne_correctedDomainAssumptions
        (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T) T := by
    refine ⟨hFH, ?_⟩
    simpa [ParameterSchedule.setupAt, Setup.withParameters] using
      theoremOnePositiveSlow_etaLambdaDomain T hT
  have hlinf :=
    lemma_one_linf_bound_correctedDomain
      (s := theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T)
      (T := T) hT hlem t ht htT ω
  have heta_time :
      (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T).eta *
          (t : ℝ) ≤ 1 / 2 := by
    simpa [ParameterSchedule.setupAt, Setup.withParameters, theoremOnePositiveSlowSchedule]
      using positiveSlow_eta_mul_time_le_half hT htT
  exact hlinf.trans heta_time

private theorem theoremOnePositiveSlowSetupAt_gradient_l1_ge_half {T t : ℕ}
    (hT : 1 ≤ T) (ht : 1 ≤ t) (htT : t ≤ T)
    (ω : Run (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T)) :
    1 / 2 ≤
      l1Norm
        ((theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T).trueGradient
          (x (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T)
            t ω)) := by
  let xt := x (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T) t ω
  have hlinf : linfNorm xt ≤ 1 / 2 :=
    theoremOnePositiveSlowSetupAt_linf_le_half hT ht htT ω
  have hcoord_abs : |xt 0| ≤ 1 / 2 := (abs_coord_le_linfNorm xt 0).trans hlinf
  have hcoord_le : xt 0 ≤ 1 / 2 := (le_abs_self (xt 0)).trans hcoord_abs
  have hnonpos : xt 0 - 1 ≤ 0 := by linarith
  have hhalf : 1 / 2 ≤ |xt 0 - 1| := by
    rw [abs_of_nonpos hnonpos]
    linarith
  rw [theoremOneShiftedQuadraticPositiveSlowSetupAt_trueGradient_eq]
  simpa [l1Norm, theoremOneUnitPoint, xt] using hhalf

private theorem theoremOnePositiveSlow_gradientL1Sum_ge_half_mul {T : ℕ}
    (hT : 1 ≤ T)
    (ω : Run (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T)) :
    (T : ℝ) * (1 / 2) ≤
      gradientL1Sum
        (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T) T ω := by
  rw [gradientL1Sum, sum_Icc_one_eq_sum_range_succ]
  calc
    (T : ℝ) * (1 / 2) =
        (Finset.range T).sum (fun _j => (1 / 2 : ℝ)) := by
      simp
    _ ≤
        (Finset.range T).sum
          (fun j =>
            l1Norm
              ((theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T).trueGradient
                (x (theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T)
                  (j + 1) ω))) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hjT : j < T := by simpa using hj
      exact theoremOnePositiveSlowSetupAt_gradient_l1_ge_half
        (T := T) (t := j + 1) hT (Nat.succ_le_succ (Nat.zero_le j))
        (Nat.succ_le_of_lt hjT) ω

private theorem theoremOnePositiveSlow_scheduledAverage_ge_half {T : ℕ}
    (hT : 1 ≤ T) :
    1 / 2 ≤
      scheduledAverageExpectedGradientL1 theoremOneShiftedQuadraticSetup
        theoremOnePositiveSlowSchedule T := by
  let sT := theoremOnePositiveSlowSchedule.setupAt theoremOneShiftedQuadraticSetup T
  let ω0 : Run sT := fun _ => ()
  have hsub : Subsingleton (Run sT) := by
    dsimp [Run, sT, ParameterSchedule.setupAt, Setup.withParameters,
      theoremOneShiftedQuadraticSetup]
    infer_instance
  have hfun :
      (fun ω : Run sT => gradientL1Sum sT T ω) =
        fun _ω : Run sT => gradientL1Sum sT T ω0 := by
    funext ω
    exact congrArg (fun ω' => gradientL1Sum sT T ω') (Subsingleton.elim ω ω0)
  have hintegral :
      ∫ ω : Run sT, gradientL1Sum sT T ω ∂Run.law sT =
        gradientL1Sum sT T ω0 := by
    rw [hfun, MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    simp
  have hsum :
      (T : ℝ) * (1 / 2) ≤ gradientL1Sum sT T ω0 :=
    theoremOnePositiveSlow_gradientL1Sum_ge_half_mul (T := T) hT ω0
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hT)
  calc
    1 / 2 = (T : ℝ)⁻¹ * ((T : ℝ) * (1 / 2)) := by
      field_simp [ne_of_gt hTpos]
    _ ≤ (T : ℝ)⁻¹ * gradientL1Sum sT T ω0 :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTpos.le)
    _ =
      scheduledAverageExpectedGradientL1 theoremOneShiftedQuadraticSetup
        theoremOnePositiveSlowSchedule T := by
      simp [scheduledAverageExpectedGradientL1, averageExpectedGradientL1, sT, hintegral]

private theorem not_tendsto_atTop_zero_of_eventually_ge_half {f : ℕ → ℝ}
    (hge : ∀ᶠ T in Filter.atTop, 1 / 2 ≤ f T) :
    ¬ Filter.Tendsto f Filter.atTop (nhds 0) := by
  intro htendsto
  have hlt : ∀ᶠ T in Filter.atTop, f T < 1 / 4 := by
    exact htendsto (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  rcases (hge.and hlt).exists with ⟨T, hhalf, hquarter⟩
  linarith

/-- Source-valid theorem-level counterexample to the printed asymptotic conclusion.

Unlike the zero-denominator audit witness, this uses strictly positive parameters
`β₁ = β₂ = η = (T+1)^{-2}`.  Thus the ordinary displayed quotients have nonzero
denominators, but the printed one-sided upper schedules still permit a learning rate whose
total horizon movement is too small for the shifted quadratic's average gradient to decay. -/
theorem theoremOne_shiftedQuadratic_positiveSlow_printedConclusion_false :
    TheoremOneScheduleAssumptions theoremOneShiftedQuadraticSetup
        theoremOnePositiveSlowSchedule ∧
      ¬ theoremOnePrintedAsymptoticConclusion theoremOneShiftedQuadraticSetup
        theoremOnePositiveSlowSchedule := by
  refine ⟨theoremOne_shiftedQuadratic_positiveSlow_printedScheduleAssumptions, ?_⟩
  intro hbigO
  have hge : ∀ᶠ T in Filter.atTop,
      1 / 2 ≤ scheduledAverageExpectedGradientL1 theoremOneShiftedQuadraticSetup
        theoremOnePositiveSlowSchedule T := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
    exact theoremOnePositiveSlow_scheduledAverage_ge_half hT
  exact not_tendsto_atTop_zero_of_eventually_ge_half hge
    (hbigO.trans_tendsto theoremOneRateScale_one_tendsto_zero)

private theorem theoremOneShiftedQuadraticSetupAt_gradient_l1_eq_one (T t : ℕ)
    (ω : Run (theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T)) :
    l1Norm
      ((theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T).trueGradient
        (x (theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T) t ω)) =
      1 := by
  have heta :
      (theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T).eta = 0 := by
    simp [ParameterSchedule.setupAt, Setup.withParameters, theoremOneZeroDenominatorSchedule]
  have hx := x_eq_x1_of_eta_zero
    (theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T) heta t ω
  rw [hx]
  rw [theoremOneShiftedQuadraticSetupAt_trueGradient_eq]
  simp [ParameterSchedule.setupAt, Setup.withParameters, theoremOneShiftedQuadraticSetup,
    theoremOneUnitPoint_l1_neg]

private theorem theoremOneShiftedQuadratic_gradientL1Sum_eq (T : ℕ)
    (ω : Run (theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T)) :
    gradientL1Sum (theoremOneZeroDenominatorSchedule.setupAt theoremOneShiftedQuadraticSetup T)
        T ω =
      (T : ℝ) := by
  simp [gradientL1Sum, theoremOneShiftedQuadraticSetupAt_gradient_l1_eq_one]

private theorem theoremOne_shiftedQuadratic_scheduledAverage_eq_one {T : ℕ}
    (hT : 1 ≤ T) :
    scheduledAverageExpectedGradientL1 theoremOneShiftedQuadraticSetup
        theoremOneZeroDenominatorSchedule T =
      1 := by
  have hTne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hT))
  simp [scheduledAverageExpectedGradientL1, averageExpectedGradientL1,
    theoremOneShiftedQuadratic_gradientL1Sum_eq, hTne]

/-- Concrete theorem-level counterexample to the printed asymptotic conclusion.

The shifted quadratic witness satisfies the printed one-sided schedule assumptions, but its
generated average gradient is eventually the constant one, while the printed rate scale
tends to zero. -/
theorem theoremOne_shiftedQuadratic_printedConclusion_false :
    TheoremOneScheduleAssumptions theoremOneShiftedQuadraticSetup
        theoremOneZeroDenominatorSchedule ∧
      ¬ theoremOnePrintedAsymptoticConclusion theoremOneShiftedQuadraticSetup
        theoremOneZeroDenominatorSchedule := by
  refine ⟨theoremOne_shiftedQuadratic_printedScheduleAssumptions, ?_⟩
  intro hbigO
  have hconstBigO :
      Asymptotics.IsBigO Filter.atTop
        (fun _ : ℕ => (1 : ℝ)) (theoremOneRateScale 1) := by
    refine hbigO.congr' ?_ (Filter.Eventually.of_forall fun T => rfl)
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
    exact theoremOne_shiftedQuadratic_scheduledAverage_eq_one hT
  exact not_tendsto_const_one_atTop_zero
    (hconstBigO.trans_tendsto theoremOneRateScale_one_tendsto_zero)

/-- Corrected-rate, non-original Theorem 1 boundary for the Appendix A/B proof route.

This theorem exposes the reciprocal-rate information needed by Appendix B's final
asymptotic simplification. -/
theorem theorem_one_centralized_correctedRate {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule}
    (h : theoremOne_correctedRateAssumptions s p) :
    Asymptotics.IsBigO Filter.atTop
      (scheduledAverageExpectedGradientL1 s p) (theoremOneRateScale d) := by
  have htoCanonical :
      Asymptotics.IsBigO Filter.atTop
        (scheduledAverageExpectedGradientL1 s p) (theoremOneCanonicalGradientBound s p) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with T hT
    have hT' : 1 ≤ T := hT
    have hle :
        scheduledAverageExpectedGradientL1 s p T ≤ theoremOneCanonicalGradientBound s p T :=
      scheduledAverageExpectedGradientL1_le_canonicalBound (s := s) (p := p) hT' h
    have havg_nonneg :
        0 ≤ scheduledAverageExpectedGradientL1 s p T :=
      averageExpectedGradientL1_nonneg (p.setupAt s T) T
    have hbound_nonneg : 0 ≤ theoremOneCanonicalGradientBound s p T :=
      havg_nonneg.trans hle
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg havg_nonneg,
      abs_of_nonneg hbound_nonneg]
    simpa using hle
  exact htoCanonical.trans
    (theoremOneCanonicalGradientBound_isBigO_of_correctedRateAssumptions
      (s := s) (p := p) h)

/-- Printed Theorem 1 conclusion for the generated original Lion optimizer.

This theorem keeps the paper-facing boundary exactly at the printed
`TheoremOneScheduleAssumptions`.  It is intentionally not proved from the corrected-rate
contract: the formal certificate
`theoremOne_printedTheoremBoundary_underSpecifiedCertificate_holds` shows that the printed
boundary admits a smooth deterministic problem/schedule pair for which the corrected
Appendix A/B reciprocal-domain boundary is false.  The proof-carrying replacement is the
separately named `theorem_one_centralized_correctedRate`.

Book citation: `book/research/Lion.json#/main_theorem/statement_math`,
`\frac{1}{T}\sum_{t=1}^{T}\mathbb{E}[\|\nabla f(x_t)\|_1]\le
O(d^{1/2}/T^{1/4})`.

Formal source-gap witness:
`theoremOne_printed_parameter_boundary_insufficiency_witness` shows that the printed
one-sided parameter boundary admits schedules for which the Appendix A/B denominator
obligations fail. -/
def theorem_one_centralized_original {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule}
    (h : TheoremOneScheduleAssumptions s p) :
    Prop :=
  Asymptotics.IsBigO Filter.atTop
    (scheduledAverageExpectedGradientL1 s p) (theoremOneRateScale d)

/-- Backward-compatible name for the corrected Theorem 1 route.

This declaration deliberately now requires the corrected-rate boundary, not merely the
corrected finite-horizon domain boundary.  Domain obligations alone do not imply the
reciprocal asymptotic estimates needed for the final Appendix B rate. -/
theorem theorem_one_centralized_correctedDomain {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule}
    (h : theoremOne_correctedRateAssumptions s p) :
    Asymptotics.IsBigO Filter.atTop
      (scheduledAverageExpectedGradientL1 s p) (theoremOneRateScale d) := by
  exact theorem_one_centralized_correctedRate (s := s) (p := p) h

/-- Formal statement-correction record for Theorem 1's final asymptotic boundary.

The `printed_statement` field is the unqualified proposition from the paper.  The
`corrected_statement` field is the proof-carrying non-original replacement whose hypotheses
make the reciprocal Appendix B step explicit. -/
structure TheoremOneStatementCorrectionRecord {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (p : ParameterSchedule) where
  printed_statement : Prop
  corrected_statement : Prop
  source_gap_name : String

/-- The active statement-correction record for Theorem 1.

Source gap: `SourceGap_AsymptoticScheduleConstants` in
`book/research/Lion.json#/source_gaps`, checked against the final Appendix B display in the
PDF. -/
def theoremOne_statementCorrectionRecord {d : ℕ} [Nonempty (Fin d)]
    (s : Setup d) (p : ParameterSchedule) :
    TheoremOneStatementCorrectionRecord s p where
  printed_statement :=
    ∀ _h : TheoremOneScheduleAssumptions s p,
      theoremOnePrintedAsymptoticConclusion s p
  corrected_statement :=
    ∀ _h : theoremOne_correctedRateAssumptions s p,
      Asymptotics.IsBigO Filter.atTop
        (scheduledAverageExpectedGradientL1 s p) (theoremOneRateScale d)
  source_gap_name := "SourceGap_AsymptoticScheduleConstants"

/-- The corrected-rate replacement in the statement-correction record is proof-carrying. -/
theorem theoremOne_statementCorrectionRecord_corrected {d : ℕ} [Nonempty (Fin d)]
    {s : Setup d} {p : ParameterSchedule} :
    (theoremOne_statementCorrectionRecord s p).corrected_statement := by
  intro h
  exact theorem_one_centralized_correctedRate (s := s) (p := p) h

/-- The concrete audit witness is registered against the active statement-correction
record: the printed assumptions hold, the corrected replacement boundary does not, and the
record names the source gap responsible for the correction. -/
theorem theoremOne_statementCorrectionRecord_retiredPrintedBoundary :
    (theoremOne_statementCorrectionRecord theoremOneZeroProblemSetup
        theoremOneZeroDenominatorSchedule).source_gap_name =
        "SourceGap_AsymptoticScheduleConstants" ∧
      TheoremOneScheduleAssumptions theoremOneZeroProblemSetup
        theoremOneZeroDenominatorSchedule ∧
      ¬ theoremOne_correctedRateAssumptions theoremOneZeroProblemSetup
        theoremOneZeroDenominatorSchedule := by
  exact ⟨rfl, theoremOne_zeroProblem_printedScheduleAssumptions,
    theoremOne_zeroProblem_printedBoundary_not_correctedRate⟩

/-- Stronger theorem-level retirement artifact: the printed statement itself is false for a
smooth deterministic shifted quadratic admitted by the printed one-sided schedule boundary.

This is the formal source-gap certificate that prevents
`theorem_one_centralized_original` from being a Phase 2a tactic target. -/
theorem theoremOne_statementCorrectionRecord_falsePrintedConclusion :
    (theoremOne_statementCorrectionRecord theoremOneShiftedQuadraticSetup
        theoremOnePositiveSlowSchedule).source_gap_name =
        "SourceGap_AsymptoticScheduleConstants" ∧
      ¬ (theoremOne_statementCorrectionRecord theoremOneShiftedQuadraticSetup
          theoremOnePositiveSlowSchedule).printed_statement ∧
      (theoremOne_statementCorrectionRecord theoremOneShiftedQuadraticSetup
          theoremOnePositiveSlowSchedule).corrected_statement := by
  rcases theoremOne_shiftedQuadratic_positiveSlow_printedConclusion_false with
    ⟨hprinted, hfalse⟩
  refine ⟨rfl, ?_, ?_⟩
  · intro hstatement
    exact hfalse (hstatement hprinted)
  · exact theoremOne_statementCorrectionRecord_corrected

/-- The named printed conclusion unfolds to the exact paper asymptotic proposition.

This no longer forwards through `theorem_one_centralized_original`: the theorem-shaped
proof-carrying route is guarded by the corrected boundary, while this declaration only
identifies the printed proposition recorded in the statement-correction artifact. -/
theorem theorem_one_centralized_original_matches_printed_conclusion {d : ℕ}
    [Nonempty (Fin d)] (s : Setup d) (p : ParameterSchedule) :
    theoremOnePrintedAsymptoticConclusion s p ↔
      Asymptotics.IsBigO Filter.atTop
        (scheduledAverageExpectedGradientL1 s p) (theoremOneRateScale d) := by
  rfl

/-- Integrability of stochastic oracle values is a proof obligation derived from the paper's
expectation notation in Assumption 3, not a primitive source-facing setup field. -/
theorem oracleValue_integrable_from_assumption {d : ℕ} {s : Setup d}
    (h : s.OracleUnbiased) (x : Point d) :
    (letI := s.sampleMeasurable;
      Integrable (fun ξ => s.oracleValue x ξ) s.oracleLaw) := by
  exact Setup.oracleUnbiased_integrable h x

end

end Algorithms.Unverified.Lion
