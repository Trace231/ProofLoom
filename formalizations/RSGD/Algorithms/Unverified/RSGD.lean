import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import SOptLib.Layer0.Objective
import SOptLib.Glue.Calculus

namespace RSGD

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

noncomputable section

variable {Omega Noise : Type*} [MeasurableSpace Omega] [MeasurableSpace Noise]

/-!
The source uses `R^n`; `EuclideanSpace R (Fin n)` is the corresponding Mathlib
model. The finite index `Fin N` represents the paper's indices `1, ..., N`
by zero-based indices.
-/

structure Setup (Omega Noise : Type*) [MeasurableSpace Omega] [MeasurableSpace Noise] where
  /-- `book_json:setup.variable_space.math`: "f : \mathbb{R}^n \to \mathbb{R}
  \text{ differentiable, bounded below, with } \|\nabla f(y) - \nabla f(x)\|
  \le L\|y - x\|, \; \forall x, y \in \mathbb{R}^n". -/
  n : ℕ
  /-- `book_json:algorithm_spec.initialization.math`: "x_1 in R^n, N >= 1;
  positive stepsizes gamma_k < 2/L". -/
  N : ℕ
  /-- `book_json:algorithm_spec.initialization.math`: "x_1 in R^n, N >= 1;
  positive stepsizes gamma_k < 2/L". -/
  hN : 0 < N
  /-- `book_json:setup.variable_space.math`: "f : \mathbb{R}^n \to \mathbb{R}
  \text{ differentiable, bounded below, with } \|\nabla f(y) - \nabla f(x)\|
  \le L\|y - x\|, \; \forall x, y \in \mathbb{R}^n". -/
  f : EuclideanSpace ℝ (Fin n) → ℝ
  /-- `book_json:algorithm_spec.initialization.math`: "x_1 in R^n, N >= 1;
  positive stepsizes gamma_k < 2/L". -/
  x₁ : EuclideanSpace ℝ (Fin n)
  /-- `book_json:setup.variable_space.math`: "f : \mathbb{R}^n \to \mathbb{R}
  \text{ differentiable, bounded below, with } \|\nabla f(y) - \nabla f(x)\|
  \le L\|y - x\|, \; \forall x, y \in \mathbb{R}^n". -/
  L : ℝ
  /-- `book_json:assumptions[0].parameters[0]`: "L > 0". -/
  hL : 0 < L
  /-- `book_json:assumptions[2].parameters[0]`: "\sigma \ge 0". -/
  sigma : ℝ
  /-- `book_json:assumptions[2].parameters[0]`: "\sigma \ge 0". -/
  hsigma : 0 ≤ sigma
  /-- `book_json:algorithm_spec.initialization.math`: "x_1 in R^n, N >= 1;
  positive stepsizes gamma_k < 2/L". -/
  gamma : Fin N → ℝ
  /-- `book_json:algorithm_spec.initialization.math`: "x_1 in R^n, N >= 1;
  positive stepsizes gamma_k < 2/L". -/
  hgamma_pos : ∀ k, 0 < gamma k
  /-- `book_json:algorithm_spec.initialization.math`: "x_1 in R^n, N >= 1;
  positive stepsizes gamma_k < 2/L". -/
  hgamma_lt : ∀ k, gamma k < 2 / L
  /-
  `book_json:main_theorem.statement_math`: "\text{Suppose } \gamma_k < 2/L
  \text{ and } P_R(k) = \frac{2\gamma_k - L\gamma_k^2}{\sum_{k=1}^N
  (2\gamma_k - L\gamma_k^2)}. \text{ Then, under Assumption 13, }
  \frac{1}{L}\mathbb{E}[\|\nabla f(x_R)\|^2] \le
  \frac{D_f^2 + \sigma^2 \sum_{k=1}^N \gamma_k^2}{\sum_{k=1}^N
  (2\gamma_k - L\gamma_k^2)}".
  The same entry says the expectation is taken with respect to `R` and
  `\xi_[N] := (\xi_1, ..., \xi_N)`. The PDF, Section 6.1, p. 306,
  says the variables \xi_k have distributions P_k.
  `ProbabilityMeasure Omega` is the normalized joint-law realization of
  that source-level stochastic base. The source does not prescribe a
  particular concrete sample-space construction.
  -/
  noiseLaw : ProbabilityMeasure Omega
  /-- `book_json:assumptions[1].math`: "\mathbb{E}[G(x_k, \xi_k)] =
  \nabla f(x_k), \quad \forall k \ge 1"; source text, Section 6.1,
  p. 306, introduces the stochastic gradient output `G(x_k,\xi_k)` and
  states that the assumptions concern Borel functions. -/
  oracle : EuclideanSpace ℝ (Fin n) → Noise → EuclideanSpace ℝ (Fin n)
  /-- `book_json:assumptions[1].math`: "\mathbb{E}[G(x_k, \xi_k)] =
  \nabla f(x_k), \quad \forall k \ge 1"; source text, Section 6.1,
  p. 306: "The following assumptions are made for the Borel functions
  G(x_k,\xi_k)". This is the measurable realization of that datum. -/
  h_oracle_measurable :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × Noise => oracle p.1 p.2)
  /-- `book_json:main_theorem.statement_math`: "\text{Suppose } \gamma_k < 2/L
  \text{ and } P_R(k) = \frac{2\gamma_k - L\gamma_k^2}{\sum_{k=1}^N
  (2\gamma_k - L\gamma_k^2)}. \text{ Then, under Assumption 13, }
  \frac{1}{L}\mathbb{E}[\|\nabla f(x_R)\|^2] \le
  \frac{D_f^2 + \sigma^2 \sum_{k=1}^N \gamma_k^2}{\sum_{k=1}^N
  (2\gamma_k - L\gamma_k^2)}"; the theorem entry specifies the
  expectation over `R` and `\xi_[N] := (\xi_1, ..., \xi_N)`. -/
  xi : Fin N → Omega → Noise
  /-- `book_json:main_theorem.statement_math`: "\text{Suppose } \gamma_k < 2/L
  \text{ and } P_R(k) = \frac{2\gamma_k - L\gamma_k^2}{\sum_{k=1}^N
  (2\gamma_k - L\gamma_k^2)}. \text{ Then, under Assumption 13, }
  \frac{1}{L}\mathbb{E}[\|\nabla f(x_R)\|^2] \le
  \frac{D_f^2 + \sigma^2 \sum_{k=1}^N \gamma_k^2}{\sum_{k=1}^N
  (2\gamma_k - L\gamma_k^2)}"; source text, Section 6.1, p. 306:
  "\xi_k, k \ge 1, are random variables whose distributions P_k are
  supported on \Xi_k". -/
  hxi_measurable : ∀ k, Measurable (xi k)
  /-- `book_json:setup.variable_space.math`: "f : \mathbb{R}^n \to \mathbb{R}
  \text{ differentiable, bounded below, with } \|\nabla f(y) - \nabla f(x)\|
  \le L\|y - x\|, \; \forall x, y \in \mathbb{R}^n". -/
  h_differentiable : Differentiable ℝ f
  /-- `book_json:setup.variable_space.math`: "f : \mathbb{R}^n \to \mathbb{R}
  \text{ differentiable, bounded below, with } \|\nabla f(y) - \nabla f(x)\|
  \le L\|y - x\|, \; \forall x, y \in \mathbb{R}^n". -/
  h_gradient_lipschitz :
    ∀ x y, ‖gradient f y - gradient f x‖ ≤ L * ‖y - x‖
  /-- `book_json:assumptions[3].math`: "f^* := \inf_{x \in \mathbb{R}^n}
  f(x) > -\infty". -/
  h_bounded_below : BddBelow (Set.range f)

/- `book_json:setup.variable_space.math`: "f : \mathbb{R}^n \to \mathbb{R}
\text{ differentiable, bounded below, with } \|\nabla f(y) - \nabla f(x)\|
\le L\|y - x\|, \; \forall x, y \in \mathbb{R}^n"; the source's `R^n` is
modeled by `EuclideanSpace R (Fin n)`. -/
abbrev Point (S : Setup Omega Noise) := EuclideanSpace ℝ (Fin S.n)

/- `book_json:setup.problem.math`, Eq. (6.1.1): "f^* := \inf_{x \in
\mathbb{R}^n} f(x)". -/
def fStar (S : Setup Omega Noise) : ℝ :=
  sInf (Set.range S.f)

/- `book_json:algorithm_spec.parameters[1].math`: "D_f := \left[
\frac{2(f(x_1) - f^*)}{L}\right]^{1/2}". -/
def distanceScale (S : Setup Omega Noise) : ℝ :=
  Real.sqrt (2 * (S.f S.x₁ - fStar S) / S.L)

/- `book_json:algorithm_spec.steps[0].math`: "x_{k+1} = x_k -
\gamma_k G(x_k, \xi_k), \quad k = 1, \ldots, R". The sampled oracle is the
canonical realization of `G(x_k,\xi_k)`. -/
def sampledOracle (S : Setup Omega Noise) (k : Fin S.N)
    (x : Omega → Point S) : Omega → Point S :=
  fun omega => S.oracle (x omega) (S.xi k omega)

/- `book_json:algorithm_spec.steps[0].math`: "x_{k+1} = x_k -
\gamma_k G(x_k, \xi_k), \quad k = 1, \ldots, R". -/
def update (S : Setup Omega Noise) (k : Fin S.N)
    (x : Omega → Point S) : Omega → Point S :=
  fun omega => x omega - S.gamma k • sampledOracle S k x omega

/- `book_json:algorithm_spec.steps[0].math`: "x_{k+1} = x_k -
\gamma_k G(x_k, \xi_k), \quad k = 1, \ldots, R". The finite-index recursion
is the canonical trajectory realization of that update. -/
def iterates (S : Setup Omega Noise) :
    Fin (S.N + 1) → Omega → Point S
  | ⟨0, _⟩ => fun _ => S.x₁
  | ⟨k + 1, hk⟩ =>
      update S ⟨k, by omega⟩ (iterates S ⟨k, by omega⟩)
termination_by k => k.val

/- `book_json:algorithm_spec.steps[0].math`: "x_{k+1} = x_k -
\gamma_k G(x_k, \xi_k), \quad k = 1, \ldots, R"; this is the sampled oracle
at the recursively generated iterate. -/
def iterateOracle (S : Setup Omega Noise) (k : Fin S.N) : Omega → Point S :=
  sampledOracle S k (iterates S k.castSucc)

/- The source proof names the noise residual
`delta_k = G(x_k, xi_k) - grad f(x_k)` before using Eq. (6.1.18). -/
def iterateResidual (S : Setup Omega Noise) (k : Fin S.N) : Omega → Point S :=
  fun omega =>
    iterateOracle S k omega - gradient S.f (iterates S k.castSucc omega)

/- `source/original_source.pdf`, Section 6.1.1.1, p. 310, Eq. (6.1.18): the proof conditions
on the history `xi_[k-1]`; this is the finite-index realization of that past. -/
def pastIndex (S : Setup Omega Noise) (k : Fin S.N) (j : Fin k.val) : Fin S.N :=
  ⟨j.val, by exact lt_trans j.isLt k.isLt⟩

/- `source/original_source.pdf`, Section 6.1.1.1, p. 310, Eq. (6.1.18): the sigma-algebra
generated by the preceding noise variables. -/
def historySigma (S : Setup Omega Noise) (k : Fin S.N) : MeasurableSpace Omega :=
  ⨆ j : Fin k.val, MeasurableSpace.comap (S.xi (pastIndex S k j)) inferInstance

/- Internal vector-valued conditional expectation associated with the same
history. The source proof's exact boundary is recorded by `conditionalCrossTerm`. -/
def conditionalResidual (S : Setup Omega Noise) (k : Fin S.N) : Omega → Point S :=
  condExp (historySigma S k) (S.noiseLaw : Measure Omega) (iterateResidual S k)

/- `source/original_source.pdf`, Section 6.1.1.1, p. 310, Eq. (6.1.18):
"E[<\nabla f(x_k),\delta_k>|\xi_[k-1]]=0". The integrability argument is
explicit at the contract boundary so `condExp` is not read through its
nonintegrable fallback. -/
def conditionalCrossTerm (S : Setup Omega Noise) (k : Fin S.N) : Omega → ℝ :=
  condExp (historySigma S k) (S.noiseLaw : Measure Omega)
    (fun omega =>
      ⟪gradient S.f (iterates S k.castSucc omega), iterateResidual S k omega⟫_ℝ)

namespace Internal

/- This is an internal realization of the paper's expectation. It records an
actual Bochner value only on the integrability domain; it is not part of the
paper-facing object layer. -/
def sourceExpectation {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (X : α → E) :
    Option E :=
  by
    classical
    exact if hX : Integrable X μ then some (∫ x, X x ∂μ) else none

theorem sourceExpectation_eq_some_integral {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (X : α → E)
    (hX : Integrable X μ) :
    sourceExpectation μ X = some (∫ x, X x ∂μ) := by
  simp [sourceExpectation, hX]

theorem sourceExpectation_eq_none {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (X : α → E)
    (hX : ¬Integrable X μ) :
    sourceExpectation μ X = none := by
  simp [sourceExpectation, hX]

/- Equality of internal source expectations requires a common actual value, so
two nonintegrable expressions cannot satisfy the relation through `none = none`. -/
def sourceExpectationEq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (X Y : α → E) : Prop :=
  ∃ v, sourceExpectation μ X = some v ∧ sourceExpectation μ Y = some v

/- Internal realization of an upper bound on a scalar expectation. The bound
is false when no actual expectation value exists. -/
def sourceExpectationLe {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (bound : ℝ) : Prop :=
  ∃ v, sourceExpectation μ X = some v ∧ v ≤ bound

theorem integrable_of_sourceExpectationEq_left {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (X Y : α → E) (hXY : sourceExpectationEq μ X Y) :
    Integrable X μ := by
  rcases hXY with ⟨v, hX, _⟩
  by_contra hX'
  simp [sourceExpectation, hX'] at hX

theorem integrable_of_sourceExpectationEq_right {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α)
    (X Y : α → E) (hXY : sourceExpectationEq μ X Y) :
    Integrable Y μ := by
  rcases hXY with ⟨v, _, hY⟩
  by_contra hY'
  simp [sourceExpectation, hY'] at hY

theorem integrable_of_sourceExpectationLe {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (bound : ℝ)
    (hX : sourceExpectationLe μ X bound) :
    Integrable X μ := by
  rcases hX with ⟨v, hX, _⟩
  by_contra hX'
  simp [sourceExpectation, hX'] at hX

end Internal

/- `book_json:assumptions[1].math`: "\mathbb{E}[G(x_k, \xi_k)] =
\nabla f(x_k), \quad \forall k \ge 1". This is the displayed source
assumption, represented by a nonfallback equality of actual source
expectations. -/
def Assumption13a (S : Setup Omega Noise) : Prop :=
  ∀ k,
    Internal.sourceExpectationEq (S.noiseLaw : Measure Omega)
      (iterateOracle S k)
      (fun omega => gradient S.f (iterates S k.castSucc omega))

/- `book_json:assumptions[2].math`: "\mathbb{E}\left[\|G(x_k, \xi_k) -
\nabla f(x_k)\|^2\right] \le \sigma^2". This is the displayed source
assumption, represented by a nonfallback scalar expectation bound. -/
def Assumption13b (S : Setup Omega Noise) : Prop :=
  ∀ k,
    Internal.sourceExpectationLe (S.noiseLaw : Measure Omega)
      (fun omega => ‖iterateResidual S k omega‖ ^ 2) (S.sigma ^ 2)

/-!
The displayed Assumption 13(a), Eq. (6.1.5), is written with a marginal
expectation of the sampled oracle. The proof of Theorem 6.1(a), Eq. (6.1.18),
uses a conditional scalar cross-term statement with respect to the past.
The source does not state that conditional identity as a separate theorem
hypothesis; it remains an explicitly named internal boundary obligation.
-/
namespace Internal

/- `source/original_source.pdf`, Section 6.1.1.1, p. 310, Eq. (6.1.18):
"E[<\nabla f(x_k),\delta_k>|\xi_[k-1]]=0". This is a proof-level
conditional contract and is deliberately separate from displayed
Assumption 13(a). -/
def Assumption13aConditional (S : Setup Omega Noise) : Prop :=
  ∀ k,
    ∃ _hCross :
        Integrable
          (fun omega =>
            ⟪gradient S.f (iterates S k.castSucc omega), iterateResidual S k omega⟫_ℝ)
          (S.noiseLaw : Measure Omega),
      conditionalCrossTerm S k =ᵐ[(S.noiseLaw : Measure Omega)] (fun _ => 0)

theorem assumption13a_conditional_spec (S : Setup Omega Noise)
    (h13aConditional : Assumption13aConditional S) :
    ∀ k,
      ∃ _hCross :
          Integrable
            (fun omega =>
              ⟪gradient S.f (iterates S k.castSucc omega), iterateResidual S k omega⟫_ℝ)
            (S.noiseLaw : Measure Omega),
        conditionalCrossTerm S k =ᵐ[(S.noiseLaw : Measure Omega)] (fun _ => 0) :=
  h13aConditional

end Internal

/- Internal bridge: the recursively generated trajectory is measurable under
the source-backed Borel oracle and noise-variable realization. -/
private theorem measurable_update_of_measurable_state
    (S : Setup Omega Noise) (j : Fin S.N) (x : Omega → Point S)
    (hx : Measurable x) :
    Measurable (update S j x) := by
  have hpair : Measurable (fun omega => (x omega, S.xi j omega)) :=
    hx.prodMk (S.hxi_measurable j)
  have horacle :
      Measurable (fun omega => S.oracle (x omega) (S.xi j omega)) :=
    S.h_oracle_measurable.comp hpair
  have hscaled :
      Measurable (fun omega => S.gamma j • S.oracle (x omega) (S.xi j omega)) :=
    measurable_const.smul horacle
  simpa [update, sampledOracle] using hx.sub hscaled

theorem iterates_measurable (S : Setup Omega Noise) (k : Fin (S.N + 1)) :
    Measurable (iterates S k) := by
  induction k using Fin.inductionOn with
  | zero =>
      unfold iterates
      exact measurable_const
  | succ j ih =>
      cases j with
      | mk j hj =>
          simpa [iterates] using
            measurable_update_of_measurable_state S ⟨j, by omega⟩
              (iterates S ⟨j, by omega⟩) (by assumption)

/- Internal bridge: composing the Borel oracle with a measurable iterate and
noise variable gives a measurable sampled oracle. -/
theorem sampledOracle_measurable (S : Setup Omega Noise) (k : Fin S.N)
    (x : Omega → Point S) (hx : Measurable x) :
    Measurable (sampledOracle S k x) := by
  have hpair : Measurable (fun omega => (x omega, S.xi k omega)) :=
    hx.prodMk (S.hxi_measurable k)
  simpa [sampledOracle] using S.h_oracle_measurable.comp hpair

/- The source states Borel oracle expectations, while Mathlib's Bochner
integral is totalized outside its integrability domain. This obligation keeps
that realization explicit rather than treating the fallback value as source
semantics. -/
theorem iterateOracle_measurable (S : Setup Omega Noise) (k : Fin S.N) :
    Measurable (iterateOracle S k) := by
  have hiter : Measurable (iterates S k.castSucc) :=
    iterates_measurable S k.castSucc
  have hsampled : Measurable (sampledOracle S k (iterates S k.castSucc)) :=
    sampledOracle_measurable S k (iterates S k.castSucc) hiter
  simpa [iterateOracle] using hsampled

/- `book_json:algorithm_spec.steps[1].math`: "P_R(k) :=
\operatorname{Prob}\{R = k\} = \frac{2\gamma_k - L\gamma_k^2}
{\sum_{k=1}^N (2\gamma_k - L\gamma_k^2)}, \quad k = 1, \ldots, N". -/
def selectionWeight (S : Setup Omega Noise) (k : Fin S.N) : ℝ :=
  2 * S.gamma k - S.L * (S.gamma k) ^ 2

/- `book_json:algorithm_spec.steps[1].math`: "P_R(k) :=
\operatorname{Prob}\{R = k\} = \frac{2\gamma_k - L\gamma_k^2}
{\sum_{k=1}^N (2\gamma_k - L\gamma_k^2)}, \quad k = 1, \ldots, N". -/
def selectionWeightSum (S : Setup Omega Noise) : ℝ :=
  ∑ k, selectionWeight S k

/- `book_json:algorithm_spec.steps[1].math`: "P_R(k) :=
\operatorname{Prob}\{R = k\} = \frac{2\gamma_k - L\gamma_k^2}
{\sum_{k=1}^N (2\gamma_k - L\gamma_k^2)}, \quad k = 1, \ldots, N". This is
the nonnegative-real realization of the displayed probability weights. -/
def selectionWeightENNReal (S : Setup Omega Noise) (k : Fin S.N) : ℝ≥0∞ :=
  ENNReal.ofReal (selectionWeight S k)

theorem fStar_le (S : Setup Omega Noise) (x : Point S) :
    fStar S ≤ S.f x := by
  change sInf (Set.range S.f) ≤ S.f x
  exact csInf_le S.h_bounded_below ⟨x, rfl⟩

theorem smoothness_bound (S : Setup Omega Noise) (x y : Point S) :
    abs (S.f y - S.f x - ⟪gradient S.f x, y - x⟫_ℝ) ≤
      S.L / 2 * ‖y - x‖ ^ 2 := by
  have hobj : SOptLib.LipschitzGradientObjective S.f S.L :=
    ⟨S.h_differentiable, S.h_gradient_lipschitz⟩
  exact SOptLib.AbsTaylorRemainderBound.of_lipschitzGradientObjective hobj x y

theorem update_equation (S : Setup Omega Noise) (k : Fin S.N)
    (x : Omega → Point S) (omega : Omega) :
    update S k x omega =
      x omega - S.gamma k • S.oracle (x omega) (S.xi k omega) := by
  simp [update, sampledOracle]

theorem iterates_zero (S : Setup Omega Noise) :
    iterates S 0 = fun _ => S.x₁ := by
  rw [← Fin.zero_eta]
  unfold iterates
  rfl

theorem iterates_succ (S : Setup Omega Noise) (k : Fin S.N) :
    iterates S k.succ = update S k (iterates S k.castSucc) := by
  cases k with
  | mk k hk => simp [iterates]

theorem selectionWeight_pos (S : Setup Omega Noise) (k : Fin S.N) :
    0 < selectionWeight S k := by
  have hγL : S.gamma k * S.L < 2 :=
    (lt_div_iff₀ S.hL).mp (S.hgamma_lt k)
  have hfactor : 0 < 2 - S.L * S.gamma k := by
    nlinarith
  have hprod : 0 < S.gamma k * (2 - S.L * S.gamma k) :=
    mul_pos (S.hgamma_pos k) hfactor
  dsimp [selectionWeight]
  nlinarith

theorem selectionWeightSum_pos (S : Setup Omega Noise) :
    0 < selectionWeightSum S := by
  classical
  unfold selectionWeightSum
  letI : Nonempty (Fin S.N) := ⟨⟨0, S.hN⟩⟩
  exact Finset.sum_pos' (fun k _ => le_of_lt (selectionWeight_pos S k))
    ⟨⟨0, S.hN⟩, Finset.mem_univ _, selectionWeight_pos S ⟨0, S.hN⟩⟩

theorem selectionWeightENNReal_sum_ne_zero (S : Setup Omega Noise) :
    (∑' k, selectionWeightENNReal S k) ≠ 0 := by
  classical
  rw [tsum_fintype]
  have hterm :
      selectionWeightENNReal S ⟨0, S.hN⟩ ≤
        ∑ k : Fin S.N, selectionWeightENNReal S k :=
    Finset.single_le_sum (fun k _ => bot_le) (Finset.mem_univ _)
  have hsum : 0 < ∑ k : Fin S.N, selectionWeightENNReal S k :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (selectionWeight_pos S ⟨0, S.hN⟩)) hterm
  exact ne_of_gt hsum

theorem selectionWeightENNReal_sum_ne_top (S : Setup Omega Noise) :
    (∑' k, selectionWeightENNReal S k) ≠ ∞ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun k hk => by
    simpa [selectionWeightENNReal] using
      (ENNReal.ofReal_ne_top (r := selectionWeight S k)))

private theorem selection_weight_ennreal_sum_to_real (S : Setup Omega Noise) :
    (∑' k, selectionWeightENNReal S k).toReal = selectionWeightSum S := by
  calc
    (∑' k, selectionWeightENNReal S k).toReal =
        (∑ k : Fin S.N, selectionWeightENNReal S k).toReal := by
          rw [tsum_fintype]
    _ = ∑ k : Fin S.N, (selectionWeightENNReal S k).toReal := by
      exact ENNReal.toReal_sum (fun k hk => by
        simpa [selectionWeightENNReal] using
          (ENNReal.ofReal_ne_top (r := selectionWeight S k)))
    _ = ∑ k : Fin S.N, selectionWeight S k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [selectionWeightENNReal]
      exact ENNReal.toReal_ofReal (le_of_lt (selectionWeight_pos S k))
    _ = selectionWeightSum S := by
      rfl

/- `book_json:algorithm_spec.steps[1].math`: "P_R(k) :=
\operatorname{Prob}\{R = k\} = \frac{2\gamma_k - L\gamma_k^2}
{\sum_{k=1}^N (2\gamma_k - L\gamma_k^2)}, \quad k = 1, \ldots, N". -/
noncomputable def selectionPMF (S : Setup Omega Noise) : PMF (Fin S.N) :=
  PMF.normalize (selectionWeightENNReal S)
    (selectionWeightENNReal_sum_ne_zero S)
    (selectionWeightENNReal_sum_ne_top S)

/- `book_json:algorithm_spec.steps[1].math`: "P_R(k) :=
\operatorname{Prob}\{R = k\} = \frac{2\gamma_k - L\gamma_k^2}
{\sum_{k=1}^N (2\gamma_k - L\gamma_k^2)}, \quad k = 1, \ldots, N". -/
noncomputable def selectionLaw (S : Setup Omega Noise) :
    ProbabilityMeasure (Fin S.N) :=
  ⟨PMF.toMeasure (selectionPMF S), inferInstance⟩

/- `book_json:algorithm_spec.steps[1].math`: "P_R(k) :=
\operatorname{Prob}\{R = k\} = \frac{2\gamma_k - L\gamma_k^2}
{\sum_{k=1}^N (2\gamma_k - L\gamma_k^2)}, \quad k = 1, \ldots, N". -/
theorem selectionPMF_formula (S : Setup Omega Noise) (k : Fin S.N) :
    (selectionPMF S k).toReal =
      selectionWeight S k / selectionWeightSum S := by
  rw [selectionPMF, PMF.normalize_apply]
  rw [← div_eq_mul_inv, ENNReal.toReal_div]
  rw [selectionWeightENNReal]
  rw [ENNReal.toReal_ofReal (le_of_lt (selectionWeight_pos S k))]
  rw [selection_weight_ennreal_sum_to_real]

/- `book_json:algorithm_spec.output.math`: "x_R". -/
def selectedIterate (S : Setup Omega Noise) : Fin S.N × Omega → Point S :=
  fun p => iterates S p.1.castSucc p.2

/- `book_json:main_theorem.statement_math`: "\text{Suppose } \gamma_k < 2/L
\text{ and } P_R(k) = \frac{2\gamma_k - L\gamma_k^2}{\sum_{k=1}^N
(2\gamma_k - L\gamma_k^2)}. \text{ Then, under Assumption 13, }
\frac{1}{L}\mathbb{E}[\|\nabla f(x_R)\|^2] \le
\frac{D_f^2 + \sigma^2 \sum_{k=1}^N \gamma_k^2}{\sum_{k=1}^N
(2\gamma_k - L\gamma_k^2)}". This is the integrand of the
expectation specified over `R` and `\xi_[N] := (\xi_1, ..., \xi_N)`. -/
def expectedStationarityIntegrand (S : Setup Omega Noise) :
    Fin S.N × Omega → ℝ :=
  fun p => ‖gradient S.f (selectedIterate S p)‖ ^ 2

/- `book_json:main_theorem.statement_math`: "\text{Suppose } \gamma_k < 2/L
\text{ and } P_R(k) = \frac{2\gamma_k - L\gamma_k^2}{\sum_{k=1}^N
(2\gamma_k - L\gamma_k^2)}. \text{ Then, under Assumption 13, }
\frac{1}{L}\mathbb{E}[\|\nabla f(x_R)\|^2] \le
\frac{D_f^2 + \sigma^2 \sum_{k=1}^N \gamma_k^2}{\sum_{k=1}^N
(2\gamma_k - L\gamma_k^2)}". The public object is the canonical
real-valued expectation of the selected output. Its well-definedness is an
internal proof obligation, not an `Option`-valued source object. -/
def expectedStationarity (S : Setup Omega Noise) : ℝ :=
  ∫ p, expectedStationarityIntegrand S p ∂
    ((selectionLaw S : Measure (Fin S.N)).prod (S.noiseLaw : Measure Omega))

namespace Internal

private theorem iterate_centered_sq_norm_integrable
    (S : Setup Omega Noise) (h13b : Assumption13b S) :
    ∀ k : Fin (S.N + 1),
      Integrable (fun omega => ‖S.x₁ - iterates S k omega‖ ^ 2)
        (S.noiseLaw : Measure Omega) := by
  let μ : Measure Omega := (S.noiseLaw : Measure Omega)
  intro k
  induction k using Fin.inductionOn with
  | zero =>
      rw [iterates_zero S]
      simp
  | succ k ih =>
      have hgrad_meas :
          AEStronglyMeasurable
            (fun omega => gradient S.f (iterates S k.castSucc omega)) μ := by
        have hgrad_lip :
            LipschitzWith (Real.toNNReal S.L) (fun x : Point S => gradient S.f x) := by
          refine lipschitzWith_of_norm_sub_le_mul
            (fun x : Point S => gradient S.f x) S.L ?_
          intro x y
          simpa [dist_eq_norm] using S.h_gradient_lipschitz y x
        exact
          (hgrad_lip.continuous.measurable.comp
            (iterates_measurable S k.castSucc)).aestronglyMeasurable
      have hgrad_sq :
          Integrable
            (fun omega => ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2) μ :=
        SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
          S.x₁ (gradient S.f) S.L (iterates S k.castSucc)
          (iterates_measurable S k.castSucc).aestronglyMeasurable ih
          S.h_gradient_lipschitz
      have hres_sq :
          Integrable (fun omega => ‖iterateResidual S k omega‖ ^ 2) μ :=
        Internal.integrable_of_sourceExpectationLe μ
          (fun omega => ‖iterateResidual S k omega‖ ^ 2) (S.sigma ^ 2)
          (h13b k)
      have horacle_meas : AEStronglyMeasurable (iterateOracle S k) μ :=
        (iterateOracle_measurable S k).aestronglyMeasurable
      have hres_meas :
          AEStronglyMeasurable (iterateResidual S k) μ := by
        simpa [iterateResidual] using horacle_meas.sub hgrad_meas
      have hgrad_l2 :
          MemLp
            (fun omega => gradient S.f (iterates S k.castSucc omega)) 2 μ :=
        (memLp_two_iff_integrable_sq_norm hgrad_meas).2 hgrad_sq
      have hres_l2 : MemLp (iterateResidual S k) 2 μ :=
        (memLp_two_iff_integrable_sq_norm hres_meas).2 hres_sq
      have horacle_l2 : MemLp (iterateOracle S k) 2 μ := by
        have hsum_l2 :
            MemLp
              (fun omega =>
                gradient S.f (iterates S k.castSucc omega) +
                  iterateResidual S k omega) 2 μ :=
          hgrad_l2.add hres_l2
        refine MemLp.ae_eq ?_ hsum_l2
        filter_upwards with omega
        change
          gradient S.f (iterates S k.castSucc omega) +
              iterateResidual S k omega =
            iterateOracle S k omega
        dsimp [iterateResidual]
        abel
      have hcenter_l2 :
          MemLp
            (fun omega => S.x₁ - iterates S k.castSucc omega) 2 μ :=
        (memLp_two_iff_integrable_sq_norm
          ((measurable_const.sub (iterates_measurable S k.castSucc)).aestronglyMeasurable)).2 ih
      have hnext_l2 :
          MemLp
            (fun omega =>
              S.x₁ - iterates S k.succ omega) 2 μ := by
        have hraw_l2 :
            MemLp
              (fun omega =>
                (S.x₁ - iterates S k.castSucc omega) -
                  (-S.gamma k) • iterateOracle S k omega) 2 μ :=
          hcenter_l2.sub (horacle_l2.const_smul (-S.gamma k))
        refine MemLp.ae_eq ?_ hraw_l2
        filter_upwards with omega
        rw [iterates_succ]
        dsimp [update, sampledOracle, iterateOracle]
        simp [smul_smul]
        abel
      exact
        (memLp_two_iff_integrable_sq_norm
          hnext_l2.aestronglyMeasurable).1 hnext_l2

private theorem selected_stationarity_fiber_integrable
    (S : Setup Omega Noise) (hcentered :
      ∀ k : Fin (S.N + 1),
        Integrable (fun omega => ‖S.x₁ - iterates S k omega‖ ^ 2)
          (S.noiseLaw : Measure Omega)) :
    ∀ k : Fin S.N,
      Integrable
        (fun omega => ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2)
        (S.noiseLaw : Measure Omega) := by
  intro k
  exact
    SOptLib.integrable_sq_norm_grad_of_lipschitz_grad_centered_l2
      S.x₁ (gradient S.f) S.L (iterates S k.castSucc)
      (iterates_measurable S k.castSucc).aestronglyMeasurable
      (hcentered k.castSucc) S.h_gradient_lipschitz

/- This is a derived well-definedness obligation for the source expectation
in Theorem 6.1(a), not a source-facing assumption or object parameter. -/
theorem expectedStationarity_integrable_of_assumption13
    (S : Setup Omega Noise) (h13a : Assumption13a S)
    (h13b : Assumption13b S) :
    Integrable (expectedStationarityIntegrand S)
      ((selectionLaw S : Measure (Fin S.N)).prod (S.noiseLaw : Measure Omega)) := by
  let μ : Measure Omega := (S.noiseLaw : Measure Omega)
  have hcentered := iterate_centered_sq_norm_integrable S h13b
  have hfiber := selected_stationarity_fiber_integrable S hcentered
  have hprod :
      Integrable
        (fun p : Fin S.N × Omega =>
          ‖gradient S.f (iterates S p.1.castSucc p.2)‖ ^ 2)
        ((selectionLaw S : Measure (Fin S.N)).prod μ) :=
    integrable_finite_index_first_prod_of_fiber_integrable
      (selectionLaw S : Measure (Fin S.N)) μ
      (fun k omega => ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2)
      hfiber
  simpa [expectedStationarityIntegrand, selectedIterate, μ] using hprod

/- Explicit bridge from the internal partial realization to the canonical
real-valued paper-facing expectation. -/
theorem sourceExpectation_eq_some_expectedStationarity_of_assumption13
    (S : Setup Omega Noise) (h13a : Assumption13a S)
    (h13b : Assumption13b S) :
    sourceExpectation
        ((selectionLaw S : Measure (Fin S.N)).prod (S.noiseLaw : Measure Omega))
        (expectedStationarityIntegrand S) =
      some (expectedStationarity S) := by
  simpa [expectedStationarity] using sourceExpectation_eq_some_integral
    ((selectionLaw S : Measure (Fin S.N)).prod (S.noiseLaw : Measure Omega))
    (expectedStationarityIntegrand S)
    (expectedStationarity_integrable_of_assumption13 S h13a h13b)

end Internal

private theorem historySigma_le_ambient
    (S : Setup Omega Noise) (k : Fin S.N) :
    historySigma S k ≤ (inferInstance : MeasurableSpace Omega) := by
  unfold historySigma
  exact iSup_le (fun j => (S.hxi_measurable (pastIndex S k j)).comap_le)

private theorem conditional_cross_term_integral_zero
    (S : Setup Omega Noise)
    (h13aConditional : Internal.Assumption13aConditional S)
    (k : Fin S.N) :
    ∫ omega,
        ⟪gradient S.f (iterates S k.castSucc omega), iterateResidual S k omega⟫_ℝ
          ∂(S.noiseLaw : Measure Omega) = 0 := by
  rcases h13aConditional k with ⟨hCross, hZero⟩
  let μ : Measure Omega := (S.noiseLaw : Measure Omega)
  let Z : Omega → ℝ :=
    fun omega =>
      ⟪gradient S.f (iterates S k.castSucc omega), iterateResidual S k omega⟫_ℝ
  have hSigma : historySigma S k ≤ (inferInstance : MeasurableSpace Omega) :=
    historySigma_le_ambient S k
  letI : SigmaFinite (μ.trim hSigma) := by infer_instance
  have htotal :
      ∫ omega, (conditionalCrossTerm S k) omega ∂μ =
        ∫ omega, Z omega ∂μ := by
    exact MeasureTheory.integral_condExp (μ := μ)
      (m := historySigma S k) (f := Z) hSigma
  have hleft : ∫ omega, (conditionalCrossTerm S k) omega ∂μ = 0 := by
    simpa [μ] using (integral_congr_ae hZero)
  have hzero : ∫ omega, Z omega ∂μ = 0 := by
    exact htotal.symm.trans hleft
  simpa [μ, Z, conditionalCrossTerm] using hzero

private theorem rsgd_one_step_descent
    (S : Setup Omega Noise) (k : Fin S.N) (omega : Omega) :
    S.f (iterates S k.succ omega) ≤ S.f (iterates S k.castSucc omega) -
        (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
          ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 -
        (S.gamma k - S.L * S.gamma k ^ 2) *
          ⟪gradient S.f (iterates S k.castSucc omega), iterateResidual S k omega⟫_ℝ +
        S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2 := by
  let x : Point S := iterates S k.castSucc omega
  let xNext : Point S := iterates S k.succ omega
  let g : Point S := gradient S.f x
  let r : Point S := iterateResidual S k omega
  let G : Point S := iterateOracle S k omega
  have hnext : xNext = x - S.gamma k • G := by
    have h := congrFun (iterates_succ S k) omega
    rw [update_equation] at h
    simpa [xNext, x, G, iterateOracle, sampledOracle] using h
  have hG : G = g + r := by
    dsimp [G, g, r, iterateResidual]
    abel
  have hstep : xNext - x = -S.gamma k • (g + r) := by
    rw [hnext, hG]
    simp [smul_smul, add_comm, add_left_comm, add_assoc]
  have hsmooth :
      abs (S.f xNext - S.f x - ⟪g, xNext - x⟫_ℝ) ≤
        S.L / 2 * ‖xNext - x‖ ^ 2 :=
    smoothness_bound S x xNext
  have hbase :
      S.f xNext ≤ S.f x + ⟪g, xNext - x⟫_ℝ +
        S.L / 2 * ‖xNext - x‖ ^ 2 := by
    have hle :
        S.f xNext - S.f x - ⟪g, xNext - x⟫_ℝ ≤
          S.L / 2 * ‖xNext - x‖ ^ 2 :=
      (le_abs_self _).trans hsmooth
    linarith
  have hcalc :
      ⟪g, xNext - x⟫_ℝ + S.L / 2 * ‖xNext - x‖ ^ 2 =
        -(S.gamma k - S.L / 2 * S.gamma k ^ 2) * ‖g‖ ^ 2 -
          (S.gamma k - S.L * S.gamma k ^ 2) * ⟪g, r⟫_ℝ +
          S.L / 2 * S.gamma k ^ 2 * ‖r‖ ^ 2 := by
    rw [hstep, inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, neg_mul, one_mul]
    rw [norm_add_sq_real, inner_add_right, real_inner_self_eq_norm_sq]
    ring
  have hbound :
      S.f xNext ≤ S.f x -
        (S.gamma k - S.L / 2 * S.gamma k ^ 2) * ‖g‖ ^ 2 -
        (S.gamma k - S.L * S.gamma k ^ 2) * ⟪g, r⟫_ℝ +
        S.L / 2 * S.gamma k ^ 2 * ‖r‖ ^ 2 := by
    linarith [hbase, hcalc]
  simpa [xNext, x, g, r] using hbound

private theorem residual_sq_integral_le
    (S : Setup Omega Noise) (h13b : Assumption13b S) (k : Fin S.N) :
    ∫ omega, ‖iterateResidual S k omega‖ ^ 2
        ∂(S.noiseLaw : Measure Omega) ≤ S.sigma ^ 2 := by
  let μ : Measure Omega := (S.noiseLaw : Measure Omega)
  let X : Omega → ℝ := fun omega => ‖iterateResidual S k omega‖ ^ 2
  have hInt : Integrable X μ :=
    Internal.integrable_of_sourceExpectationLe μ X (S.sigma ^ 2) (h13b k)
  rcases h13b k with ⟨v, hv, hv_le⟩
  have hsome : Internal.sourceExpectation μ X = some (∫ omega, X omega ∂μ) :=
    Internal.sourceExpectation_eq_some_integral μ X hInt
  have hv_eq : v = ∫ omega, X omega ∂μ :=
    Option.some.inj (hv.symm.trans hsome)
  rw [← hv_eq]
  simpa [μ, X] using hv_le

private theorem fin_sum_adjacent_sub
    (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ∑ k : Fin n, (x k.castSucc - x k.succ) =
      x 0 - x (Fin.last n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have hih := ih (fun j => x j.succ)
      have hih' :
          (∑ i : Fin n, (x i.succ.castSucc - x i.succ.succ)) =
            x (Fin.succ 0) - x (Fin.last n).succ := by
        convert hih using 1 <;> simp
      rw [hih']
      simp

private theorem rsgd_pathwise_weighted_descent
    (S : Setup Omega Noise) (omega : Omega) :
    ∑ k : Fin S.N,
        (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
            ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ≤
      S.f S.x₁ - fStar S -
          ∑ k : Fin S.N,
            (S.gamma k - S.L * S.gamma k ^ 2) *
              ⟪gradient S.f (iterates S k.castSucc omega),
                iterateResidual S k omega⟫_ℝ +
        ∑ k : Fin S.N,
          S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2 := by
  have hsum :
      ∑ k : Fin S.N,
          (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
              ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ≤
        ∑ k : Fin S.N,
          (S.f (iterates S k.castSucc omega) -
              S.f (iterates S k.succ omega) -
              (S.gamma k - S.L * S.gamma k ^ 2) *
                ⟪gradient S.f (iterates S k.castSucc omega),
                  iterateResidual S k omega⟫_ℝ +
              S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    linarith [rsgd_one_step_descent S k omega]
  have htel :
      ∑ k : Fin S.N,
          (S.f (iterates S k.castSucc omega) -
            S.f (iterates S k.succ omega)) =
        S.f (iterates S 0 omega) -
          S.f (iterates S (Fin.last S.N) omega) := by
    simpa using
      (fin_sum_adjacent_sub S.N
        (fun j : Fin (S.N + 1) => S.f (iterates S j omega)))
  have hsum' :
      ∑ k : Fin S.N,
          (S.f (iterates S k.castSucc omega) -
              S.f (iterates S k.succ omega) -
              (S.gamma k - S.L * S.gamma k ^ 2) *
                ⟪gradient S.f (iterates S k.castSucc omega),
                  iterateResidual S k omega⟫_ℝ +
              S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) =
        (∑ k : Fin S.N,
            (S.f (iterates S k.castSucc omega) -
              S.f (iterates S k.succ omega))) -
          ∑ k : Fin S.N,
            (S.gamma k - S.L * S.gamma k ^ 2) *
              ⟪gradient S.f (iterates S k.castSucc omega),
                iterateResidual S k omega⟫_ℝ +
        ∑ k : Fin S.N,
          S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hterm :
      fStar S ≤ S.f (iterates S (Fin.last S.N) omega) :=
    fStar_le S (iterates S (Fin.last S.N) omega)
  rw [hsum'] at hsum
  rw [htel, iterates_zero S] at hsum
  linarith

private theorem rsgd_integrated_weighted_descent
    (S : Setup Omega Noise) (h13a : Assumption13a S)
    (h13b : Assumption13b S)
    (h13aConditional : Internal.Assumption13aConditional S) :
    ∑ k : Fin S.N,
        (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
          (∫ omega,
            ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2
              ∂(S.noiseLaw : Measure Omega)) ≤
      S.f S.x₁ - fStar S +
        S.L / 2 * S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2 := by
  let μ : Measure Omega := (S.noiseLaw : Measure Omega)
  have hcentered := Internal.iterate_centered_sq_norm_integrable S h13b
  have hgrad :=
    Internal.selected_stationarity_fiber_integrable S hcentered
  have hres :
      ∀ k : Fin S.N,
        Integrable (fun omega => ‖iterateResidual S k omega‖ ^ 2) μ := by
    intro k
    exact Internal.integrable_of_sourceExpectationLe μ
      (fun omega => ‖iterateResidual S k omega‖ ^ 2) (S.sigma ^ 2) (h13b k)
  have hgrad_vec :
      ∀ k : Fin S.N,
        AEStronglyMeasurable
          (fun omega => gradient S.f (iterates S k.castSucc omega)) μ := by
    intro k
    have hgrad_lip :
        LipschitzWith (Real.toNNReal S.L)
          (fun x : Point S => gradient S.f x) := by
      refine lipschitzWith_of_norm_sub_le_mul
        (fun x : Point S => gradient S.f x) S.L ?_
      intro x y
      simpa [dist_eq_norm] using S.h_gradient_lipschitz y x
    exact
      (hgrad_lip.continuous.measurable.comp
        (iterates_measurable S k.castSucc)).aestronglyMeasurable
  have hres_vec :
      ∀ k : Fin S.N,
        AEStronglyMeasurable (iterateResidual S k) μ := by
    intro k
    have horacle_meas : AEStronglyMeasurable (iterateOracle S k) μ :=
      (iterateOracle_measurable S k).aestronglyMeasurable
    simpa [iterateResidual] using horacle_meas.sub (hgrad_vec k)
  have hcross :
      ∀ k : Fin S.N,
        Integrable
          (fun omega =>
            ⟪gradient S.f (iterates S k.castSucc omega),
              iterateResidual S k omega⟫_ℝ) μ := by
    intro k
    exact integrable_inner_of_integrable_sq_norm
      (hgrad_vec k)
      (hres_vec k)
      (hgrad k) (hres k)
  have hleft :
      Integrable
        (fun omega =>
          ∑ k : Fin S.N,
            (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
              ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2) μ := by
    exact MeasureTheory.integrable_finset_sum _ (fun k hk =>
      (hgrad k).const_mul (S.gamma k - S.L / 2 * S.gamma k ^ 2))
  have hright :
      Integrable
        (fun omega =>
          S.f S.x₁ - fStar S -
              ∑ k : Fin S.N,
                (S.gamma k - S.L * S.gamma k ^ 2) *
                  ⟪gradient S.f (iterates S k.castSucc omega),
                    iterateResidual S k omega⟫_ℝ +
            ∑ k : Fin S.N,
              S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) μ := by
    have hcrossSum :
        Integrable
          (fun omega =>
            ∑ k : Fin S.N,
              (S.gamma k - S.L * S.gamma k ^ 2) *
                ⟪gradient S.f (iterates S k.castSucc omega),
                  iterateResidual S k omega⟫_ℝ) μ :=
      MeasureTheory.integrable_finset_sum _ (fun k hk =>
        (hcross k).const_mul (S.gamma k - S.L * S.gamma k ^ 2))
    have hresSum :
        Integrable
          (fun omega =>
            ∑ k : Fin S.N,
              S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) μ :=
      MeasureTheory.integrable_finset_sum _ (fun k hk =>
        (hres k).const_mul (S.L / 2 * S.gamma k ^ 2))
    exact ((integrable_const (S.f S.x₁ - fStar S)).sub hcrossSum).add hresSum
  have hmono :
      (∫ omega,
        ∑ k : Fin S.N,
          (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
            ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) ≤
        ∫ omega,
          (S.f S.x₁ - fStar S -
              ∑ k : Fin S.N,
                (S.gamma k - S.L * S.gamma k ^ 2) *
                  ⟪gradient S.f (iterates S k.castSucc omega),
                    iterateResidual S k omega⟫_ℝ +
            ∑ k : Fin S.N,
              S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) ∂μ := by
    exact MeasureTheory.integral_mono_ae hleft hright
      (Filter.Eventually.of_forall (fun omega =>
        rsgd_pathwise_weighted_descent S omega))
  have hleft_eval :
      (∫ omega,
        ∑ k : Fin S.N,
          (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
            ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) =
        ∑ k : Fin S.N,
          (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
            (∫ omega,
              ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) := by
    rw [MeasureTheory.integral_finset_sum _ (fun k hk =>
      (hgrad k).const_mul (S.gamma k - S.L / 2 * S.gamma k ^ 2))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [MeasureTheory.integral_const_mul]
  have hcross_zero :
      ∀ k : Fin S.N,
        ∫ omega,
          ⟪gradient S.f (iterates S k.castSucc omega),
            iterateResidual S k omega⟫_ℝ ∂μ = 0 := by
    intro k
    exact conditional_cross_term_integral_zero S h13aConditional k
  have hright_eval :
      (∫ omega,
          (S.f S.x₁ - fStar S -
              ∑ k : Fin S.N,
                (S.gamma k - S.L * S.gamma k ^ 2) *
                  ⟪gradient S.f (iterates S k.castSucc omega),
                    iterateResidual S k omega⟫_ℝ +
            ∑ k : Fin S.N,
              S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) ∂μ) =
        S.f S.x₁ - fStar S -
            ∑ k : Fin S.N,
              (S.gamma k - S.L * S.gamma k ^ 2) *
                (∫ omega,
                  ⟪gradient S.f (iterates S k.castSucc omega),
                    iterateResidual S k omega⟫_ℝ ∂μ) +
          ∑ k : Fin S.N,
            S.L / 2 * S.gamma k ^ 2 *
              (∫ omega, ‖iterateResidual S k omega‖ ^ 2 ∂μ) := by
    have hcrossSum_int :
        Integrable
          (fun omega =>
            ∑ k : Fin S.N,
              (S.gamma k - S.L * S.gamma k ^ 2) *
                ⟪gradient S.f (iterates S k.castSucc omega),
                  iterateResidual S k omega⟫_ℝ) μ :=
      MeasureTheory.integrable_finset_sum _ (fun k hk =>
        (hcross k).const_mul (S.gamma k - S.L * S.gamma k ^ 2))
    have hresSum_int :
        Integrable
          (fun omega =>
            ∑ k : Fin S.N,
              S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) μ :=
      MeasureTheory.integrable_finset_sum _ (fun k hk =>
        (hres k).const_mul (S.L / 2 * S.gamma k ^ 2))
    have hadd :
        (∫ omega,
            (S.f S.x₁ - fStar S -
                ∑ k : Fin S.N,
                  (S.gamma k - S.L * S.gamma k ^ 2) *
                    ⟪gradient S.f (iterates S k.castSucc omega),
                      iterateResidual S k omega⟫_ℝ +
              ∑ k : Fin S.N,
                S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2) ∂μ) =
          (∫ omega,
            S.f S.x₁ - fStar S -
                ∑ k : Fin S.N,
                  (S.gamma k - S.L * S.gamma k ^ 2) *
                    ⟪gradient S.f (iterates S k.castSucc omega),
                      iterateResidual S k omega⟫_ℝ ∂μ) +
            ∫ omega,
              ∑ k : Fin S.N,
                S.L / 2 * S.gamma k ^ 2 * ‖iterateResidual S k omega‖ ^ 2 ∂μ := by
      exact MeasureTheory.integral_add
        ((integrable_const _).sub hcrossSum_int) hresSum_int
    rw [hadd]
    rw [MeasureTheory.integral_sub (integrable_const _) hcrossSum_int]
    rw [MeasureTheory.integral_const]
    simp [μ]
    rw [MeasureTheory.integral_finset_sum _ (fun k hk =>
      (hcross k).const_mul (S.gamma k - S.L * S.gamma k ^ 2))]
    rw [MeasureTheory.integral_finset_sum _ (fun k hk =>
      (hres k).const_mul (S.L / 2 * S.gamma k ^ 2))]
    simp_rw [MeasureTheory.integral_const_mul]
    simp [μ]
  rw [hleft_eval, hright_eval] at hmono
  have hres_bound :
      ∑ k : Fin S.N,
          S.L / 2 * S.gamma k ^ 2 *
            (∫ omega, ‖iterateResidual S k omega‖ ^ 2 ∂μ) ≤
        S.L / 2 * S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2 := by
    calc
      _ ≤ ∑ k : Fin S.N, S.L / 2 * S.gamma k ^ 2 * S.sigma ^ 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        exact mul_le_mul_of_nonneg_left (residual_sq_integral_le S h13b k)
          (mul_nonneg (by linarith [S.hL]) (sq_nonneg _))
      _ = S.L / 2 * S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2 := by
        rw [← Finset.sum_mul]
        rw [← Finset.mul_sum]
        ring
  simp_rw [hcross_zero] at hmono
  simp at hmono
  have hres_bound' :
      (S.f S.x₁ - fStar S) +
          ∑ k : Fin S.N,
            S.L / 2 * S.gamma k ^ 2 *
              (∫ omega, ‖iterateResidual S k omega‖ ^ 2 ∂μ) ≤
        (S.f S.x₁ - fStar S) +
          S.L / 2 * S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_left hres_bound (S.f S.x₁ - fStar S))
  have htail :=
    hmono.trans hres_bound'
  simpa [μ, add_comm, add_left_comm, add_assoc] using htail

private theorem expected_stationarity_weighted_expansion
    (S : Setup Omega Noise) (h13a : Assumption13a S)
    (h13b : Assumption13b S) :
    expectedStationarity S =
      ∑ k : Fin S.N,
        (selectionWeight S k / selectionWeightSum S) *
          (∫ omega,
            ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2
              ∂(S.noiseLaw : Measure Omega)) := by
  let μ : Measure Omega := (S.noiseLaw : Measure Omega)
  have hcentered := Internal.iterate_centered_sq_norm_integrable S h13b
  have hgrad :=
    Internal.selected_stationarity_fiber_integrable S hcentered
  have hsingleton :
      ∀ k : Fin S.N,
        (selectionLaw S : Measure (Fin S.N)).real ({k} : Set (Fin S.N)) =
          selectionWeight S k / selectionWeightSum S := by
    intro k
    rw [Measure.real_def]
    rw [selectionLaw]
    change (PMF.toMeasure (selectionPMF S) ({k} : Set (Fin S.N))).toReal =
      selectionWeight S k / selectionWeightSum S
    rw [PMF.toMeasure_apply_singleton
      (selectionPMF S) k (measurableSet_singleton k)]
    exact selectionPMF_formula S k
  have hprod :
      ∫ q : Fin S.N × Omega,
          ‖gradient S.f (iterates S q.1.castSucc q.2)‖ ^ 2
            ∂((selectionLaw S : Measure (Fin S.N)).prod μ) =
        ∑ k : Fin S.N,
          (selectionWeight S k / selectionWeightSum S) *
            (∫ omega,
              ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) :=
    SOptLib.integral_finite_index_first_prod_eq_sum_weights
      (selectionLaw S : Measure (Fin S.N)) μ
      (fun k => selectionWeight S k / selectionWeightSum S)
      (fun k omega => ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2)
      hsingleton hgrad
  simpa [expectedStationarity, expectedStationarityIntegrand, selectedIterate, μ] using
    hprod

private theorem distance_scale_square (S : Setup Omega Noise) :
    distanceScale S ^ 2 =
      2 * (S.f S.x₁ - fStar S) / S.L := by
  have hgap : 0 ≤ S.f S.x₁ - fStar S :=
    sub_nonneg.mpr (fStar_le S S.x₁)
  have hrad : 0 ≤ 2 * (S.f S.x₁ - fStar S) / S.L := by
    exact div_nonneg (mul_nonneg (by norm_num) hgap) (le_of_lt S.hL)
  unfold distanceScale
  rw [Real.sq_sqrt hrad]

namespace Counterexample

abbrev CPoint := EuclideanSpace ℝ (Fin 1)

def cquad : CPoint → ℝ := fun x => (1 / 2 : ℝ) * ‖x‖ ^ 2

def csign : Bool → ℝ
  | true => 1
  | false => -1

def cunit : CPoint := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ))

def cnoise : Bool → CPoint := fun omega => csign omega • cunit

theorem cunit_norm : ‖cunit‖ = 1 := by
  rw [PiLp.norm_eq_of_L2 cunit]
  simp [cunit, PiLp.toLp_apply]

theorem cnoise_norm (omega : Bool) : ‖cnoise omega‖ = 1 := by
  cases omega <;> simp [cnoise, csign, cunit_norm]

theorem cquad_gradient (x : CPoint) : gradient cquad x = x := by
  apply HasGradientAt.gradient
  change HasGradientAt (fun y : CPoint => (1 / 2 : ℝ) * ‖y‖ ^ 2) x x
  simpa using
    hasGradientAt_const_mul_norm_sub_sq_centered
      (E := CPoint) 1 (0 : CPoint) x

theorem cquad_hasGradientAt (x : CPoint) :
    HasGradientAt cquad x x := by
  change HasGradientAt (fun y : CPoint => (1 / 2 : ℝ) * ‖y‖ ^ 2) x x
  simpa using
    hasGradientAt_const_mul_norm_sub_sq_centered
      (E := CPoint) 1 (0 : CPoint) x

def cMeasure : ProbabilityMeasure Bool :=
  ⟨PMF.toMeasure (PMF.uniformOfFintype Bool), inferInstance⟩

theorem cMeasure_integral (g : Bool → CPoint) :
    ∫ omega, g omega ∂(cMeasure : Measure Bool) =
      (1 / 2 : ℝ) • g false + (1 / 2 : ℝ) • g true := by
  change ∫ omega, g omega ∂(PMF.toMeasure (PMF.uniformOfFintype Bool)) = _
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype]
  ac_rfl

theorem cMeasure_integral_real (g : Bool → ℝ) :
    ∫ omega, g omega ∂(cMeasure : Measure Bool) =
      (1 / 2 : ℝ) • g false + (1 / 2 : ℝ) • g true := by
  change ∫ omega, g omega ∂(PMF.toMeasure (PMF.uniformOfFintype Bool)) = _
  rw [PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype]
  ac_rfl

theorem cnoise_integral_zero :
    ∫ omega, cnoise omega ∂(cMeasure : Measure Bool) = 0 := by
  rw [cMeasure_integral]
  simp [cnoise, csign]

theorem cnoise_sq_norm_integral :
    ∫ omega, ‖cnoise omega‖ ^ 2 ∂(cMeasure : Measure Bool) = 1 := by
  rw [cMeasure_integral_real]
  simp [cnoise_norm]
  norm_num

def cSetup : Setup Bool Bool :=
  { n := 1
    N := 4
    hN := by norm_num
    f := cquad
    x₁ := 0
    L := 1
    hL := by norm_num
    sigma := 1
    hsigma := by norm_num
    gamma := fun _ => 1 / 2
    hgamma_pos := by intro k; norm_num
    hgamma_lt := by intro k; norm_num
    noiseLaw := cMeasure
    oracle := fun x z => x + cnoise z
    h_oracle_measurable := by
      fun_prop
    xi := fun _ omega => omega
    hxi_measurable := by intro k; fun_prop
    h_differentiable := by
      exact fun x => (cquad_hasGradientAt x).differentiableAt
    h_gradient_lipschitz := by
      intro x y
      rw [cquad_gradient, cquad_gradient]
      simpa using le_rfl
    h_bounded_below := by
      refine ⟨0, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact mul_nonneg (by norm_num) (sq_nonneg _)
  }

theorem cupdate_vector (a : ℝ) (v : CPoint) :
    a • v - (1 / 2 : ℝ) • (a • v + v) =
      (a - (1 / 2 : ℝ) * (a + 1)) • v := by
  module

theorem citerates_zero :
    iterates cSetup (⟨0, by norm_num [cSetup]⟩ : Fin (cSetup.N + 1)) =
      fun _ => cSetup.x₁ := by
  simpa only [Fin.zero_eta] using iterates_zero cSetup

theorem citerates_one :
    iterates cSetup (⟨1, by norm_num [cSetup]⟩ : Fin (cSetup.N + 1)) =
      fun omega => -(1 / 2 : ℝ) • cnoise omega := by
  rw [show (⟨1, by norm_num [cSetup]⟩ : Fin (cSetup.N + 1)) =
      (⟨0, by norm_num [cSetup]⟩ : Fin cSetup.N).succ by rfl]
  rw [iterates_succ]
  simp only [Fin.castSucc_mk]
  rw [citerates_zero]
  funext omega
  simp only [update, sampledOracle, cSetup]
  change (0 : CPoint) - (1 / 2 : ℝ) • (0 + cnoise omega) =
    -(1 / 2 : ℝ) • cnoise omega
  rw [zero_add, zero_sub, ← neg_smul]

theorem citerates_two :
    iterates cSetup (⟨2, by norm_num [cSetup]⟩ : Fin (cSetup.N + 1)) =
      fun omega => -(3 / 4 : ℝ) • cnoise omega := by
  rw [show (⟨2, by norm_num [cSetup]⟩ : Fin (cSetup.N + 1)) =
      (⟨1, by norm_num [cSetup]⟩ : Fin cSetup.N).succ by rfl]
  rw [iterates_succ]
  simp only [Fin.castSucc_mk]
  rw [citerates_one]
  funext omega
  simp only [update, sampledOracle, cSetup]
  convert cupdate_vector (-(1 / 2 : ℝ)) (cnoise omega) using 1 <;> norm_num

theorem citerates_three :
    iterates cSetup (⟨3, by norm_num [cSetup]⟩ : Fin (cSetup.N + 1)) =
      fun omega => -(7 / 8 : ℝ) • cnoise omega := by
  rw [show (⟨3, by norm_num [cSetup]⟩ : Fin (cSetup.N + 1)) =
      (⟨2, by norm_num [cSetup]⟩ : Fin cSetup.N).succ by rfl]
  rw [iterates_succ]
  simp only [Fin.castSucc_mk]
  rw [citerates_two]
  funext omega
  simp only [update, sampledOracle, cSetup]
  convert cupdate_vector (-(3 / 4 : ℝ)) (cnoise omega) using 1 <;> norm_num

theorem citerate_oracle_zero :
    iterateOracle cSetup (⟨0, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      cnoise := by
  rw [iterateOracle]
  simp only [Fin.castSucc_mk]
  rw [citerates_zero]
  funext omega
  simp [sampledOracle, cSetup, cnoise]

theorem citerate_oracle_one :
    iterateOracle cSetup (⟨1, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      fun omega => (1 / 2 : ℝ) • cnoise omega := by
  rw [iterateOracle]
  simp only [Fin.castSucc_mk]
  rw [citerates_one]
  funext omega
  simp only [sampledOracle, cSetup]
  module

theorem citerate_oracle_two :
    iterateOracle cSetup (⟨2, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      fun omega => (1 / 4 : ℝ) • cnoise omega := by
  rw [iterateOracle]
  simp only [Fin.castSucc_mk]
  rw [citerates_two]
  funext omega
  simp only [sampledOracle, cSetup]
  module

theorem citerate_oracle_three :
    iterateOracle cSetup (⟨3, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      fun omega => (1 / 8 : ℝ) • cnoise omega := by
  rw [iterateOracle]
  simp only [Fin.castSucc_mk]
  rw [citerates_three]
  funext omega
  simp only [sampledOracle, cSetup]
  module

theorem cgradient_zero :
    (fun omega =>
      gradient cSetup.f
        (iterates cSetup
          ((⟨0, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)) =
      fun _ => 0 := by
  simp only [Fin.castSucc_mk]
  rw [citerates_zero]
  funext omega
  simpa [cSetup] using (cquad_gradient (0 : CPoint))

theorem cgradient_one :
    (fun omega =>
      gradient cSetup.f
        (iterates cSetup
          ((⟨1, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)) =
      fun omega => -(1 / 2 : ℝ) • cnoise omega := by
  simp only [Fin.castSucc_mk]
  rw [citerates_one]
  funext omega
  simpa [cSetup] using
    (cquad_gradient (-(1 / 2 : ℝ) • cnoise omega))

theorem cgradient_two :
    (fun omega =>
      gradient cSetup.f
        (iterates cSetup
          ((⟨2, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)) =
      fun omega => -(3 / 4 : ℝ) • cnoise omega := by
  simp only [Fin.castSucc_mk]
  rw [citerates_two]
  funext omega
  simpa [cSetup] using
    (cquad_gradient (-(3 / 4 : ℝ) • cnoise omega))

theorem cgradient_three :
    (fun omega =>
      gradient cSetup.f
        (iterates cSetup
          ((⟨3, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)) =
      fun omega => -(7 / 8 : ℝ) • cnoise omega := by
  simp only [Fin.castSucc_mk]
  rw [citerates_three]
  funext omega
  simpa [cSetup] using
    (cquad_gradient (-(7 / 8 : ℝ) • cnoise omega))

theorem cresidual_zero :
    iterateResidual cSetup (⟨0, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      cnoise := by
  unfold iterateResidual
  rw [citerate_oracle_zero]
  simp only [Fin.castSucc_mk]
  funext omega
  have hgrad := congrFun cgradient_zero omega
  simp only [Fin.castSucc_mk] at hgrad
  rw [hgrad]
  simp

theorem cresidual_one :
    iterateResidual cSetup (⟨1, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      cnoise := by
  unfold iterateResidual
  rw [citerate_oracle_one]
  simp only [Fin.castSucc_mk]
  funext omega
  have hgrad := congrFun cgradient_one omega
  simp only [Fin.castSucc_mk] at hgrad
  rw [hgrad]
  change (1 / 2 : ℝ) • cnoise omega -
      (-(1 / 2 : ℝ)) • cnoise omega = cnoise omega
  module

theorem cresidual_two :
    iterateResidual cSetup (⟨2, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      cnoise := by
  unfold iterateResidual
  rw [citerate_oracle_two]
  simp only [Fin.castSucc_mk]
  funext omega
  have hgrad := congrFun cgradient_two omega
  simp only [Fin.castSucc_mk] at hgrad
  rw [hgrad]
  change (1 / 4 : ℝ) • cnoise omega -
      (-(3 / 4 : ℝ)) • cnoise omega = cnoise omega
  module

theorem cresidual_three :
    iterateResidual cSetup (⟨3, by norm_num [cSetup]⟩ : Fin cSetup.N) =
      cnoise := by
  unfold iterateResidual
  rw [citerate_oracle_three]
  simp only [Fin.castSucc_mk]
  funext omega
  have hgrad := congrFun cgradient_three omega
  simp only [Fin.castSucc_mk] at hgrad
  rw [hgrad]
  change (1 / 8 : ℝ) • cnoise omega -
      (-(7 / 8 : ℝ)) • cnoise omega = cnoise omega
  module

theorem cnoise_smul_integral_zero (a : ℝ) :
    ∫ omega, a • cnoise omega ∂(cMeasure : Measure Bool) = 0 := by
  rw [cMeasure_integral]
  simp [cnoise, csign]

theorem csource_eq_of_integrals_equal
    {X Y : Bool → CPoint}
    (hXY :
      (∫ omega, X omega ∂(cMeasure : Measure Bool)) =
        ∫ omega, Y omega ∂(cMeasure : Measure Bool)) :
    Internal.sourceExpectationEq (cMeasure : Measure Bool) X Y := by
  refine ⟨∫ omega, X omega ∂(cMeasure : Measure Bool), ?_, ?_⟩
  · exact Internal.sourceExpectation_eq_some_integral
      (cMeasure : Measure Bool) X Integrable.of_finite
  · rw [Internal.sourceExpectation_eq_some_integral
      (cMeasure : Measure Bool) Y Integrable.of_finite, ← hXY]

theorem csource_le_of_integral_le
    {X : Bool → ℝ} {b : ℝ}
    (hX : (∫ omega, X omega ∂(cMeasure : Measure Bool)) ≤ b) :
    Internal.sourceExpectationLe (cMeasure : Measure Bool) X b := by
  refine ⟨∫ omega, X omega ∂(cMeasure : Measure Bool), ?_, hX⟩
  exact Internal.sourceExpectation_eq_some_integral
    (cMeasure : Measure Bool) X Integrable.of_finite

theorem c_assumption13a : Assumption13a cSetup := by
  intro k
  fin_cases k
  · apply csource_eq_of_integrals_equal
    rw [citerate_oracle_zero, cnoise_integral_zero, cgradient_zero]
    have hz :
        (∫ _ : Bool, (0 : CPoint) ∂(cMeasure : Measure Bool)) = 0 := by
      simp
    simpa only [Pi.zero_apply] using hz.symm
  · apply csource_eq_of_integrals_equal
    rw [citerate_oracle_one, cnoise_smul_integral_zero,
      cgradient_one, cnoise_smul_integral_zero]
  · apply csource_eq_of_integrals_equal
    rw [citerate_oracle_two, cnoise_smul_integral_zero,
      cgradient_two, cnoise_smul_integral_zero]
  · apply csource_eq_of_integrals_equal
    rw [citerate_oracle_three, cnoise_smul_integral_zero,
      cgradient_three, cnoise_smul_integral_zero]

theorem c_assumption13b : Assumption13b cSetup := by
  intro k
  fin_cases k
  all_goals
    apply csource_le_of_integral_le
    rw [show (fun omega => ‖iterateResidual cSetup _ omega‖ ^ 2) =
      fun omega => ‖cnoise omega‖ ^ 2 by
        funext omega
        simp only [cresidual_zero, cresidual_one, cresidual_two, cresidual_three] <;>
          rfl]
    rw [cnoise_sq_norm_integral]
    norm_num [cSetup]

theorem cgradient_sq_integral_zero :
    ∫ omega,
        ‖gradient cSetup.f
            (iterates cSetup
              ((⟨0, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2
          ∂(cMeasure : Measure Bool) = 0 := by
  have hfun :
      (fun omega =>
          ‖gradient cSetup.f
              (iterates cSetup
                ((⟨0, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2) =
        (fun _ : Bool => (0 : ℝ)) := by
    funext omega
    rw [congrFun cgradient_zero omega]
    simp
  rw [hfun]
  simp

theorem cgradient_sq_integral_one :
    ∫ omega,
        ‖gradient cSetup.f
            (iterates cSetup
              ((⟨1, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2
          ∂(cMeasure : Measure Bool) = 1 / 4 := by
  have hfun :
      (fun omega =>
          ‖gradient cSetup.f
              (iterates cSetup
                ((⟨1, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2) =
        (fun omega => ‖-(1 / 2 : ℝ) • cnoise omega‖ ^ 2) := by
    funext omega
    exact congrArg (fun v : CPoint => ‖v‖ ^ 2)
      (congrFun cgradient_one omega)
  rw [hfun]
  rw [cMeasure_integral_real]
  simp [norm_smul, cnoise_norm]
  norm_num

theorem cgradient_sq_integral_two :
    ∫ omega,
        ‖gradient cSetup.f
            (iterates cSetup
              ((⟨2, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2
          ∂(cMeasure : Measure Bool) = 9 / 16 := by
  have hfun :
      (fun omega =>
          ‖gradient cSetup.f
              (iterates cSetup
                ((⟨2, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2) =
        (fun omega => ‖-(3 / 4 : ℝ) • cnoise omega‖ ^ 2) := by
    funext omega
    exact congrArg (fun v : CPoint => ‖v‖ ^ 2)
      (congrFun cgradient_two omega)
  rw [hfun]
  rw [cMeasure_integral_real]
  simp [norm_smul, cnoise_norm]
  norm_num

theorem cgradient_sq_integral_three :
    ∫ omega,
        ‖gradient cSetup.f
            (iterates cSetup
              ((⟨3, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2
          ∂(cMeasure : Measure Bool) = 49 / 64 := by
  have hfun :
      (fun omega =>
          ‖gradient cSetup.f
              (iterates cSetup
                ((⟨3, by norm_num [cSetup]⟩ : Fin cSetup.N).castSucc) omega)‖ ^ 2) =
        (fun omega => ‖-(7 / 8 : ℝ) • cnoise omega‖ ^ 2) := by
    funext omega
    exact congrArg (fun v : CPoint => ‖v‖ ^ 2)
      (congrFun cgradient_three omega)
  rw [hfun]
  rw [cMeasure_integral_real]
  simp [norm_smul, cnoise_norm]
  norm_num

theorem cexpectedStationarity : expectedStationarity cSetup = 101 / 256 := by
  let mu : Measure Bool := (cSetup.noiseLaw : Measure Bool)
  have hsingleton :
      ∀ k : Fin cSetup.N,
        (selectionLaw cSetup : Measure (Fin cSetup.N)).real {k} =
          selectionWeight cSetup k / selectionWeightSum cSetup := by
    intro k
    change
      (PMF.toMeasure (selectionPMF cSetup) ({k} : Set (Fin cSetup.N))).toReal =
        selectionWeight cSetup k / selectionWeightSum cSetup
    rw [PMF.toMeasure_apply_singleton
      (selectionPMF cSetup) k (measurableSet_singleton k)]
    exact selectionPMF_formula cSetup k
  have hgrad :
      ∀ k : Fin cSetup.N,
        Integrable
          (fun omega =>
            ‖gradient cSetup.f
              (iterates cSetup k.castSucc omega)‖ ^ 2) mu := by
    intro k
    exact Integrable.of_finite
  have hprod :=
    SOptLib.integral_finite_index_first_prod_eq_sum_weights
      (selectionLaw cSetup : Measure (Fin cSetup.N)) mu
      (fun k => selectionWeight cSetup k / selectionWeightSum cSetup)
      (fun k omega =>
        ‖gradient cSetup.f (iterates cSetup k.castSucc omega)‖ ^ 2)
      hsingleton hgrad
  have hfiber :
      ∀ k : Fin cSetup.N,
        (∫ omega,
          ‖gradient cSetup.f (iterates cSetup k.castSucc omega)‖ ^ 2
            ∂(cMeasure : Measure Bool)) =
          match k.1 with
          | 0 => 0
          | 1 => 1 / 4
          | 2 => 9 / 16
          | _ => 49 / 64 := by
    intro k
    fin_cases k
    · simpa using cgradient_sq_integral_zero
    · simpa using cgradient_sq_integral_one
    · simpa using cgradient_sq_integral_two
    · simpa using cgradient_sq_integral_three
  calc
    expectedStationarity cSetup =
        ∑ k : Fin cSetup.N,
          (selectionWeight cSetup k / selectionWeightSum cSetup) *
            (∫ omega,
              ‖gradient cSetup.f (iterates cSetup k.castSucc omega)‖ ^ 2
                ∂(cMeasure : Measure Bool)) := by
      simpa [expectedStationarity, expectedStationarityIntegrand,
        selectedIterate, mu] using hprod
    _ = 101 / 256 := by
      have hweight :
          ∀ k : Fin cSetup.N, selectionWeight cSetup k = 3 / 4 := by
        intro k
        change
          2 * (1 / 2 : ℝ) - 1 * (1 / 2 : ℝ) ^ 2 = 3 / 4
        norm_num
      have hsum : selectionWeightSum cSetup = 3 := by
        unfold selectionWeightSum
        simp_rw [hweight]
        change (∑ _ : Fin 4, (3 / 4 : ℝ)) = 3
        rw [Fin.sum_univ_four]
        norm_num
      simp_rw [hfiber]
      simp_rw [hweight, hsum]
      change
        (∑ x : Fin 4,
          (3 / 4 : ℝ) / 3 *
            match x.1 with
            | 0 => 0
            | 1 => 1 / 4
            | 2 => 9 / 16
            | _ => 49 / 64) =
          101 / 256
      rw [Fin.sum_univ_four]
      norm_num [selectionWeight, selectionWeightSum, cSetup,
        Fin.sum_univ_four]

theorem cfStar_zero : fStar cSetup = 0 := by
  change sInf (Set.range cquad) = 0
  apply le_antisymm
  · exact csInf_le cSetup.h_bounded_below ⟨0, by simp [cquad]⟩
  · refine le_csInf ?_ ?_
    · exact ⟨0, ⟨0, by simp [cquad]⟩⟩
    · rintro y ⟨x, rfl⟩
      exact mul_nonneg (by norm_num) (sq_nonneg ‖x‖)

theorem cdistanceScale_zero : distanceScale cSetup = 0 := by
  unfold distanceScale
  rw [cfStar_zero]
  have hf : cSetup.f cSetup.x₁ = 0 := by
    change cquad (0 : CPoint) = 0
    simp [cquad]
  rw [hf]
  norm_num [cSetup]

theorem ccounterexample :
    (1 / cSetup.L) * expectedStationarity cSetup >
      (distanceScale cSetup ^ 2 +
        cSetup.sigma ^ 2 * ∑ k, cSetup.gamma k ^ 2) /
        selectionWeightSum cSetup := by
  rw [cexpectedStationarity, cdistanceScale_zero]
  have hgamma :
      ∀ k : Fin cSetup.N, cSetup.gamma k = 1 / 2 := by
    intro k
    rfl
  have hweight :
      ∀ k : Fin cSetup.N, selectionWeight cSetup k = 3 / 4 := by
    intro k
    change
      2 * (1 / 2 : ℝ) - 1 * (1 / 2 : ℝ) ^ 2 = 3 / 4
    norm_num
  have hsum : selectionWeightSum cSetup = 3 := by
    unfold selectionWeightSum
    simp_rw [hweight]
    change (∑ _ : Fin 4, (3 / 4 : ℝ)) = 3
    rw [Fin.sum_univ_four]
    norm_num
  rw [hsum]
  simp_rw [hgamma]
  norm_num [cSetup, Fin.sum_univ_four]

end Counterexample
/- `book_json:main_theorem.statement_math`: Theorem 6.1(a) concludes the
real-valued expected-stationarity inequality "under Assumption 13". The source
theorem head has no separate conditional-contract hypothesis.

Source-boundary status: this declaration is retained verbatim as the source
theorem record, but it is not derivable from the displayed assumptions in the
current model. `book/research/Source.json#/assumptions/1` gives only the
marginal equation
`E[G(x_k, xi_k)] = grad f(x_k)`, while
`source/original_source.txt`, Eq. (6.1.18), uses
`E[<grad f(x_k), delta_k> | xi_[k-1]] = 0`. The same source text explicitly
allows the variables `xi_k` to be dependent. The finite counterexample recorded
by the Planner is: n = 1, f(x) = x^2 / 2, L = 1, x₁ = 0, N = 4,
gamma_k = 1 / 2, sigma = 1, a uniform Rademacher z with every xi_k = z,
and G(x,z) = x + z. Then Assumption 13a and 13b hold, while
expectedStationarity = 101 / 256, distanceScale^2 = 0, and
selectionWeightSum = 3, so the claimed inequality would assert
`101 / 256 <= 1 / 3`, which is false.

Consequently the unguarded source-facing endpoint is refuted by the following
formal theorem: it exhibits a Setup satisfying the displayed marginal
assumptions for which the claimed conclusion is false. The canonical theorem
name is retained below as an explicitly guarded source-boundary interface, and
its implementation is the proved `theorem_6_1a_conditional_boundary`. -/
theorem theorem_6_1a_source_counterexample :
    ∃ S : Setup Bool Bool,
      Assumption13a S ∧ Assumption13b S ∧
        ¬ ((1 / S.L) * expectedStationarity S ≤
          (distanceScale S ^ 2 + S.sigma ^ 2 * ∑ k, S.gamma k ^ 2) /
            selectionWeightSum S) := by
  refine ⟨Counterexample.cSetup, Counterexample.c_assumption13a,
    Counterexample.c_assumption13b, ?_⟩
  exact not_le_of_gt Counterexample.ccounterexample

/- Source-boundary correction. The PDF displays Assumption 13(a) as a
marginal unbiasedness equation, but its proof of Theorem 6.1(a) uses the
conditional identity
"E[<\nabla f(x_k),\delta_k>|\xi_[k-1]]=0" in Eq. (6.1.18). Because the source
also allows the noise to depend on the search sequence, the current Setup does
not derive that identity from the displayed marginal equation. This is a
distinct corrected result and must not be treated as the source theorem. -/
theorem theorem_6_1a_conditional_boundary (S : Setup Omega Noise)
    (h13a : Assumption13a S) (h13b : Assumption13b S)
    (h13aConditional : Internal.Assumption13aConditional S) :
    (1 / S.L) * expectedStationarity S ≤
      (distanceScale S ^ 2 + S.sigma ^ 2 * ∑ k, S.gamma k ^ 2) /
        selectionWeightSum S := by
  let μ : Measure Omega := (S.noiseLaw : Measure Omega)
  have hdesc :=
    rsgd_integrated_weighted_descent S h13a h13b h13aConditional
  have hsel :=
    expected_stationarity_weighted_expansion S h13a h13b
  have hdist := distance_scale_square S
  have hweight :
      ∀ k : Fin S.N,
        selectionWeight S k =
          2 * (S.gamma k - S.L / 2 * S.gamma k ^ 2) := by
    intro k
    simp [selectionWeight]
    ring
  have hweighted :
      ∑ k : Fin S.N,
          selectionWeight S k *
            (∫ omega,
              ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) ≤
        S.L *
          (distanceScale S ^ 2 +
            S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2) := by
    have htwice :=
      mul_le_mul_of_nonneg_left hdesc (by norm_num : (0 : ℝ) ≤ 2)
    calc
      ∑ k : Fin S.N,
          selectionWeight S k *
            (∫ omega,
              ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) =
          2 *
            ∑ k : Fin S.N,
              (S.gamma k - S.L / 2 * S.gamma k ^ 2) *
                (∫ omega,
                  ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hweight k]
        ring
      _ ≤ 2 *
          (S.f S.x₁ - fStar S +
            S.L / 2 * S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2) := htwice
      _ = S.L *
          (distanceScale S ^ 2 +
            S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2) := by
        rw [hdist]
        field_simp [ne_of_gt S.hL]
  have hnormalize :
      ∑ k : Fin S.N,
          (selectionWeight S k / selectionWeightSum S) *
            (∫ omega,
              ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) =
        (1 / selectionWeightSum S) *
          ∑ k : Fin S.N,
            selectionWeight S k *
              (∫ omega,
                ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsel, hnormalize]
  have hfactor :
      0 ≤ (1 / S.L) * (1 / selectionWeightSum S) := by
    exact
      mul_nonneg
        (div_nonneg (by norm_num) (le_of_lt S.hL))
        (div_nonneg (by norm_num) (le_of_lt (selectionWeightSum_pos S)))
  have hscaled := mul_le_mul_of_nonneg_left hweighted hfactor
  calc
    (1 / S.L) *
          ((1 / selectionWeightSum S) *
            ∑ k : Fin S.N,
              selectionWeight S k *
                (∫ omega,
                  ‖gradient S.f (iterates S k.castSucc omega)‖ ^ 2 ∂μ)) ≤
        (1 / S.L) * (1 / selectionWeightSum S) *
          (S.L *
            (distanceScale S ^ 2 +
              S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2)) := by
      simpa [mul_assoc] using hscaled
    _ = (distanceScale S ^ 2 +
          S.sigma ^ 2 * ∑ k : Fin S.N, S.gamma k ^ 2) /
        selectionWeightSum S := by
      field_simp [ne_of_gt S.hL, ne_of_gt (selectionWeightSum_pos S)]

/- The paper-canonical theorem name is retained as an affirmative guarded
interface. The explicit conditional contract is necessary for the source
proof's Eq. (6.1.18) cancellation and is not derivable from marginal
Assumption 13(a) in the dependent-noise model formalized above. -/
theorem theorem_6_1a (S : Setup Omega Noise)
    (h13a : Assumption13a S) (h13b : Assumption13b S)
    (h13aConditional : Internal.Assumption13aConditional S) :
    (1 / S.L) * expectedStationarity S ≤
      (distanceScale S ^ 2 + S.sigma ^ 2 * ∑ k, S.gamma k ^ 2) /
        selectionWeightSum S := by
  exact theorem_6_1a_conditional_boundary S h13a h13b h13aConditional

end
end RSGD
