import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Descent

/-!
Object-layer model for SPIDER-SFO, Algorithm 1.

This file intentionally records the algorithmic objects as definitions.  Proof
obligations derived in the paper are theorems, not fields of the setup.
-/

open scoped BigOperators
open scoped Gradient
open MeasureTheory

namespace Algorithms.Unverified.SPIDER

variable {Sample E Ω : Type*}

/-- The paper's ambient decision space `ℝ^d` from Eq. (1.1). -/
abbrev VariableSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Online objective `f(x) = E[F(x; ζ)]` from Eq. (1.1). -/
noncomputable def onlineObjective
    [MeasurableSpace Sample] (sampleLaw : Measure Sample)
    (sampleObjective : E → Sample → ℝ) : E → ℝ :=
  SOptLib.objectiveExpectation sampleLaw sampleObjective id

/-- Well-definedness of the online objective expectation at a decision point.

The paper writes `f(x)=E[F(x;ζ)]`; this predicate records the nonfallback
meaning of that expectation without adding a separate source-facing assumption. -/
def onlineObjectiveWellDefinedAt
    [MeasurableSpace Sample] (sampleLaw : Measure Sample)
    (sampleObjective : E → Sample → ℝ) (x : E) : Prop :=
  SOptLib.objectiveWellDefined sampleLaw sampleObjective id x

/-- Paper expectation inequality for squared norms.

This wraps `E ‖Z‖² ≤ rhs` with the well-definedness condition needed for the
expectation notation to denote the paper's mathematical quantity rather than a
totalized Lean integral fallback. -/
def expectedSqNormBound
    [MeasurableSpace Sample] [Norm E]
    (sampleLaw : Measure Sample) (Z : Sample → E) (rhs : ℝ) : Prop :=
  SOptLib.expectationWellDefined sampleLaw (fun s => ‖Z s‖ ^ 2) ∧
    ∫ s, ‖Z s‖ ^ 2 ∂sampleLaw ≤ rhs

/-- The paper expectation-bound predicate exposes nonfallback expectation
well-definedness as a derived projection, not as an extra assumption. -/
theorem expectedSqNormBound_wellDefined
    [MeasurableSpace Sample] [Norm E]
    {sampleLaw : Measure Sample} {Z : Sample → E} {rhs : ℝ}
    (h : expectedSqNormBound sampleLaw Z rhs) :
    SOptLib.expectationWellDefined sampleLaw (fun s => ‖Z s‖ ^ 2) :=
  h.1

/-- The paper expectation-bound predicate exposes the numeric inequality after
the nonfallback branch is known. -/
theorem expectedSqNormBound_integral_le
    [MeasurableSpace Sample] [Norm E]
    {sampleLaw : Measure Sample} {Z : Sample → E} {rhs : ℝ}
    (h : expectedSqNormBound sampleLaw Z rhs) :
    ∫ s, ‖Z s‖ ^ 2 ∂sampleLaw ≤ rhs :=
  h.2

/-- Per-sample stochastic gradient `∇F(x; ζ)`, computed from the sampled
objective kernel rather than supplied as an independent oracle. -/
noncomputable def sampleObjectiveGradient
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (sampleObjective : E → Sample → ℝ) (x : E) (sample : Sample) : E :=
  ∇ (fun y : E => sampleObjective y sample) x

/-- Full objective gradient `∇f(x)` for the expected objective. -/
noncomputable def objectiveGradient
    [MeasurableSpace Sample]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (sampleLaw : Measure Sample) (sampleObjective : E → Sample → ℝ) : E → E :=
  fun x => ∇ (onlineObjective sampleLaw sampleObjective) x

/-- The global infimum value `f* = inf_x f(x)` from Assumption 1(i). -/
noncomputable def objectiveInfimum
    (f : E → ℝ) : ℝ :=
  SOptLib.objectiveInfimumValue (Set.univ : Set E) f

/-- Online stochastic non-convex problem data and Assumption 1.

The stochastic-gradient regularity assumptions are kept here because they are
the paper's stated Assumption 1, not later proof artifacts.

Book citations:
* `book/research/SPIDER.json#/setup/problem`: `minimize f(x) ≡ E[F(x; ζ)]`.
* `book/research/SPIDER.json#/assumptions/0`: `Δ := f(x_0)-f^*<∞`.
* `book/research/SPIDER.json#/assumptions/1`: averaged Lipschitz-gradient bound.
* `book/research/SPIDER.json#/assumptions/2`: online gradient-variance bound.
* `book/research/SPIDER.json#/assumptions/16`: online SFO differential
  unbiasedness, together with the setup identity `f(x) ≡ E[F(x; ζ)]`. -/
structure OnlineProblem
    (Sample E : Type*) [MeasurableSpace Sample]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] where
  /-- Sample objective kernel `F(x; ζ)`.
  Source: `book/research/SPIDER.json#/setup/problem`, quote `f(x) ≡ E[F(x; ζ)]`. -/
  sampleObjective : E → Sample → ℝ
  /-- Law of the online sample `ζ`.
  Source: `book/research/SPIDER.json#/setup/problem`, quote `E[F(x; ζ)]`. -/
  sampleLaw : Measure Sample
  /-- Probability-law status of the stochastic sample distribution.
  Source: `book/research/SPIDER.json#/setup/problem`, quote uses expectation over `ζ`. -/
  sampleLaw_isProbability : IsProbabilityMeasure sampleLaw
  /-- Finite objective expectation boundary for Eq. (1.1).
  Source: `book/research/SPIDER.json#/setup/problem`, quote `f(x) ≡ E[F(x; ζ)]`. -/
  objective_wellDefined :
    ∀ x : E, onlineObjectiveWellDefinedAt sampleLaw sampleObjective x
  /-- Initial point `x₀`.
  Source: `book/research/SPIDER.json#/assumptions/0`, quote `Δ := f(x_0)-f^*<∞`. -/
  x0 : E
  /-- Smoothness/averaged-gradient constant `L`.
  Source: `book/research/SPIDER.json#/assumptions/1`, quote `≤ L^2‖x-y‖^2`. -/
  L : ℝ
  /-- Online gradient-variance constant `σ`.
  Source: `book/research/SPIDER.json#/assumptions/2`, quote `≤ σ^2`. -/
  sigma : ℝ
  /-- Source-facing realization of finite initial gap, used only to make the
  canonical `f* = inf_x f(x)` a nonfallback real lower-bound object.
  Source: `book/research/SPIDER.json#/assumptions/0`, quote `f^* ... is the global infimum value`. -/
  objective_bddBelow :
    BddBelow ((onlineObjective sampleLaw sampleObjective) '' (Set.univ : Set E))
  /-- Component gradients named in Assumption 1(ii)/(iii).
  Source: `book/research/SPIDER.json#/assumptions/1`, quote `∇ f_i(x)`. -/
  sampleObjective_hasGradientAt :
    ∀ x : E, ∀ s : Sample,
      HasGradientAt (fun y : E => sampleObjective y s)
        (sampleObjectiveGradient sampleObjective x s) x
  /-- Lean regularity for the stochastic-gradient oracle used as a random
  variable in Algorithm 1 lines 3 and 5.

  Source: `book/research/SPIDER.json#/algorithm_spec/steps/3` and
  `#/algorithm_spec/steps/5`, quote `v^k=∇f_{S_1}(x^k)` and
  `v^k=∇f_{S_2}(x^k)-∇f_{S_2}(x^{k-1})+v^{k-1}`.  This is a
  well-definedness/regularity interface for the sampled-gradient kernel, not a
  convergence bound or one of the paper's derived estimator lemmas. -/
  sampleObjectiveGradient_joint_measurable :
    Measurable (fun p : E × Sample =>
      sampleObjectiveGradient sampleObjective p.1 p.2)
  /-- Full gradient named in Assumption 1(iii).
  Source: `book/research/SPIDER.json#/assumptions/2`, quote `∇ f(x)`. -/
  objective_hasGradientAt :
    ∀ x : E,
      HasGradientAt (onlineObjective sampleLaw sampleObjective)
        (objectiveGradient sampleLaw sampleObjective x) x
  /-- Source-facing unbiased stochastic-gradient mean interface.
  Source: `book/research/SPIDER.json#/setup/problem`, quote
  `f(x) ≡ E[F(x; ζ)]`, and
  `book/research/SPIDER.json#/assumptions/16`, quote
  `E[∇ f_i(x^k)-∇ f_i(x^{k-1}) | x_{0:k}] =
    ∇ f(x^k)-∇ f(x^{k-1})`.

  This records the fixed-fiber mean equality from which the conditional
  differential-unbiased residuals are derived; it is not an estimator-error
  or martingale conclusion. -/
  online_gradient_unbiased :
    ∀ x : E,
      SOptLib.expectationEq sampleLaw
        (fun s => sampleObjectiveGradient sampleObjective x s)
        (objectiveGradient sampleLaw sampleObjective x)
  /-- Assumption 1(ii), kept as a stated paper assumption.
  Source: `book/research/SPIDER.json#/assumptions/1`, quote
  `E‖∇ f_i(x)-∇ f_i(y)‖^2 ≤ L^2‖x-y‖^2`. -/
  averaged_lipschitz_gradient :
    ∀ x y : E,
      expectedSqNormBound sampleLaw
        (fun s =>
          sampleObjectiveGradient sampleObjective x s -
            sampleObjectiveGradient sampleObjective y s)
        (L ^ 2 * ‖x - y‖ ^ 2)
  /-- Assumption 1(iii), kept as a stated paper assumption.
  Source: `book/research/SPIDER.json#/assumptions/2`, quote
  `E‖∇ f_i(x)-∇ f(x)‖^2 ≤ σ^2`. -/
  online_gradient_variance :
    ∀ x : E,
      expectedSqNormBound sampleLaw
        (fun s =>
          sampleObjectiveGradient sampleObjective x s -
            objectiveGradient sampleLaw sampleObjective x)
        (sigma ^ 2)

namespace OnlineProblem

variable [MeasurableSpace Sample]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E]

/-- Paper objective attached to an online problem. -/
noncomputable def f (P : OnlineProblem Sample E) : E → ℝ :=
  onlineObjective P.sampleLaw P.sampleObjective

/-- Paper full gradient `∇f`. -/
noncomputable def grad (P : OnlineProblem Sample E) : E → E :=
  objectiveGradient P.sampleLaw P.sampleObjective

/-- Paper stochastic component/sample gradient `∇F(·; ζ)`. -/
noncomputable def sampleGrad (P : OnlineProblem Sample E) : E → Sample → E :=
  sampleObjectiveGradient P.sampleObjective

/-- Paper global infimum value `f*`. -/
noncomputable def fStar (P : OnlineProblem Sample E) : ℝ :=
  objectiveInfimum P.f

/-- Initial objective gap `Δ := f(x₀) - f*`. -/
noncomputable def Delta (P : OnlineProblem Sample E) : ℝ :=
  P.f P.x0 - P.fStar

/-- Source-facing well-definedness obligation for the objective expectation. -/
theorem f_wellDefinedAt_obligation (P : OnlineProblem Sample E) (x : E) :
    onlineObjectiveWellDefinedAt P.sampleLaw P.sampleObjective x := by
  exact P.objective_wellDefined x

/-- Assumption 1(i)'s definitional identity for the initial gap. -/
theorem finite_initial_gap (P : OnlineProblem Sample E) :
    P.Delta = P.f P.x0 - P.fStar := by
  rfl

/-- The canonical infimum value lower-bounds the paper objective. -/
theorem fStar_lower_bound (P : OnlineProblem Sample E) (x : E) :
    P.fStar ≤ P.f x := by
  unfold fStar objectiveInfimum f
  exact SOptLib.objectiveInfimumValue_le P.objective_bddBelow (Set.mem_univ x)

/-- The paper's initial gap is nonnegative because `f*` is the global infimum
value in Assumption 1(i), not because `Δ` is an arbitrary nonnegative input. -/
theorem Delta_nonneg (P : OnlineProblem Sample E) :
    0 ≤ P.Delta := by
  unfold Delta
  exact sub_nonneg.mpr (P.fStar_lower_bound P.x0)

/-- The exposed stochastic gradient is the gradient of the sampled objective. -/
theorem sampleGrad_def (P : OnlineProblem Sample E) (x : E) (s : Sample) :
    P.sampleGrad x s = ∇ (fun y : E => P.sampleObjective y s) x := by
  rfl

/-- The exposed full gradient is the gradient of the expected objective. -/
theorem grad_def (P : OnlineProblem Sample E) (x : E) :
    P.grad x = ∇ P.f x := by
  rfl

/-- The canonical sampled gradient has the Mathlib gradient property asserted
by the paper's component-gradient assumption. -/
theorem sampleGrad_hasGradientAt (P : OnlineProblem Sample E) (x : E) (s : Sample) :
    HasGradientAt (fun y : E => P.sampleObjective y s) (P.sampleGrad x s) x := by
  exact P.sampleObjective_hasGradientAt x s

/-- The sampled-gradient oracle is jointly measurable as a kernel in decision
and sample variables.  This exposes the Lean regularity needed to sample the
paper's `∇F(x;ζ)` at generated random iterates. -/
theorem sampleGrad_joint_measurable (P : OnlineProblem Sample E) :
    Measurable (fun p : E × Sample => P.sampleGrad p.1 p.2) := by
  exact P.sampleObjectiveGradient_joint_measurable

/-- The canonical full gradient has the Mathlib gradient property for `f`. -/
theorem grad_hasGradientAt (P : OnlineProblem Sample E) (x : E) :
    HasGradientAt P.f (P.grad x) x := by
  exact P.objective_hasGradientAt x

/-- Fixed-query stochastic-gradient unbiasedness in the paper's expectation
notation. -/
theorem online_gradient_unbiased_expectationEq (P : OnlineProblem Sample E) (x : E) :
    SOptLib.expectationEq P.sampleLaw (fun s => P.sampleGrad x s) (P.grad x) := by
  exact P.online_gradient_unbiased x

/-- Integrability projection from fixed-query stochastic-gradient unbiasedness. -/
theorem online_gradient_unbiased_integrable (P : OnlineProblem Sample E) (x : E) :
    Integrable (fun s => P.sampleGrad x s) P.sampleLaw := by
  exact SOptLib.expectationEq.integrable (P.online_gradient_unbiased_expectationEq x)

/-- Bochner-integral projection from fixed-query stochastic-gradient unbiasedness. -/
theorem online_gradient_unbiased_integral_eq (P : OnlineProblem Sample E) (x : E) :
    (∫ s, P.sampleGrad x s ∂P.sampleLaw) = P.grad x := by
  exact SOptLib.expectationEq.integral_eq (P.online_gradient_unbiased_expectationEq x)

/-- Fixed-query centered stochastic-gradient residual.

This is the source-facing projection Phase 2a was missing: mini-batch and
random-query variance lemmas can use this as their fixed-fiber zero-mean
premise instead of assuming a local `hfixed_zero`. -/
theorem fixed_query_sample_gradient_residual_centered
    (P : OnlineProblem Sample E) (x : E) :
    ∫ s, P.sampleGrad x s - P.grad x ∂P.sampleLaw = 0 := by
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  have hG_int : Integrable (fun s => P.sampleGrad x s) P.sampleLaw :=
    P.online_gradient_unbiased_integrable x
  have hconst_int : Integrable (fun _ : Sample => P.grad x) P.sampleLaw :=
    integrable_const _
  have hmean : (∫ s, P.sampleGrad x s ∂P.sampleLaw) = P.grad x :=
    P.online_gradient_unbiased_integral_eq x
  calc
    ∫ s, P.sampleGrad x s - P.grad x ∂P.sampleLaw =
        (∫ s, P.sampleGrad x s ∂P.sampleLaw) -
          ∫ _s : Sample, P.grad x ∂P.sampleLaw := by
          exact integral_sub hG_int hconst_int
    _ = P.grad x - P.grad x := by
          simp [hmean]
    _ = 0 := by
          simp

/-- Fixed-query gradient-difference residual centering, matching the online
SPIDER-SFO differential-unbiasedness display before conditioning on the past. -/
theorem fixed_query_sample_gradient_difference_residual_centered
    (P : OnlineProblem Sample E) (x y : E) :
    ∫ s, (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
        ∂P.sampleLaw = 0 := by
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  have hx_int : Integrable (fun s => P.sampleGrad x s) P.sampleLaw :=
    P.online_gradient_unbiased_integrable x
  have hy_int : Integrable (fun s => P.sampleGrad y s) P.sampleLaw :=
    P.online_gradient_unbiased_integrable y
  have hdiff_int :
      Integrable (fun s => P.sampleGrad x s - P.sampleGrad y s) P.sampleLaw :=
    hx_int.sub hy_int
  have hconst_int :
      Integrable (fun _ : Sample => P.grad x - P.grad y) P.sampleLaw :=
    integrable_const _
  have hx_mean : (∫ s, P.sampleGrad x s ∂P.sampleLaw) = P.grad x :=
    P.online_gradient_unbiased_integral_eq x
  have hy_mean : (∫ s, P.sampleGrad y s ∂P.sampleLaw) = P.grad y :=
    P.online_gradient_unbiased_integral_eq y
  calc
    ∫ s, (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
        ∂P.sampleLaw =
        (∫ s, P.sampleGrad x s - P.sampleGrad y s ∂P.sampleLaw) -
          ∫ _s : Sample, P.grad x - P.grad y ∂P.sampleLaw := by
          exact integral_sub hdiff_int hconst_int
    _ = ((∫ s, P.sampleGrad x s ∂P.sampleLaw) -
          (∫ s, P.sampleGrad y s ∂P.sampleLaw)) -
          (P.grad x - P.grad y) := by
          rw [integral_sub hx_int hy_int]
          simp
    _ = 0 := by
          simp [hx_mean, hy_mean]

/-- Assumption 1(ii) in nonfallback expectation form. -/
theorem averaged_lipschitz_gradient_wellDefined (P : OnlineProblem Sample E) (x y : E) :
    SOptLib.expectationWellDefined P.sampleLaw
      (fun s => ‖P.sampleGrad x s - P.sampleGrad y s‖ ^ 2) := by
  exact expectedSqNormBound_wellDefined (P.averaged_lipschitz_gradient x y)

/-- Numeric inequality component of Assumption 1(ii). -/
theorem averaged_lipschitz_gradient_bound (P : OnlineProblem Sample E) (x y : E) :
    ∫ s, ‖P.sampleGrad x s - P.sampleGrad y s‖ ^ 2 ∂P.sampleLaw ≤
      P.L ^ 2 * ‖x - y‖ ^ 2 := by
  exact expectedSqNormBound_integral_le (P.averaged_lipschitz_gradient x y)

/-- Assumption 1(iii) in nonfallback expectation form. -/
theorem online_gradient_variance_wellDefined (P : OnlineProblem Sample E) (x : E) :
    SOptLib.expectationWellDefined P.sampleLaw
      (fun s => ‖P.sampleGrad x s - P.grad x‖ ^ 2) := by
  exact expectedSqNormBound_wellDefined (P.online_gradient_variance x)

/-- Numeric inequality component of Assumption 1(iii). -/
theorem online_gradient_variance_bound (P : OnlineProblem Sample E) (x : E) :
    ∫ s, ‖P.sampleGrad x s - P.grad x‖ ^ 2 ∂P.sampleLaw ≤
      P.sigma ^ 2 := by
  exact expectedSqNormBound_integral_le (P.online_gradient_variance x)

end OnlineProblem

/-- Online parameter schedule from Eq. (3.4), kept as closed-form definitions. -/
noncomputable def onlineRefreshBatchSize (sigma epsilon : ℝ) : ℝ :=
  2 * sigma ^ 2 * epsilon⁻¹ ^ 2

/-- Recursive mini-batch size from Eq. (3.4). -/
noncomputable def onlineRecursiveBatchSize (sigma epsilon n0 : ℝ) : ℝ :=
  2 * sigma * (epsilon * n0)⁻¹

/-- Constant Option I step size from Eq. (3.4) and Algorithm 1, line 11. -/
noncomputable def optionIBaseStepSize (epsilon L n0 : ℝ) : ℝ :=
  epsilon * (L * n0)⁻¹

/-- Epoch length `q` from Eq. (3.4). -/
noncomputable def onlineEpochLength (sigma epsilon n0 : ℝ) : ℝ :=
  sigma * n0 * epsilon⁻¹

/-- Exact real-valued parameter schedule printed in Eq. (3.4). -/
structure OnlineSchedule where
  S1 : ℝ
  S2 : ℝ
  eta : ℝ
  q : ℝ
  etaK : E → ℝ

/-- Theorem 1's exact online schedule from Eq. (3.4), before any Lean
finite-index realization for sampled mini-batches. -/
noncomputable def theorem1OnlineSchedule
    [Norm E] (L sigma epsilon n0 : ℝ) : OnlineSchedule (E := E) where
  S1 := onlineRefreshBatchSize sigma epsilon
  S2 := onlineRecursiveBatchSize sigma epsilon n0
  eta := optionIBaseStepSize epsilon L n0
  q := onlineEpochLength sigma epsilon n0
  etaK := fun v => min (epsilon * (L * n0 * ‖v‖)⁻¹) ((2 * L * n0)⁻¹)

/-- Eq. (3.4)'s refresh batch-size identity. -/
@[simp]
theorem theorem1OnlineSchedule_S1
    [Norm E] (L sigma epsilon n0 : ℝ) :
    (theorem1OnlineSchedule (E := E) L sigma epsilon n0).S1 =
      2 * sigma ^ 2 * epsilon⁻¹ ^ 2 := by
  rfl

/-- Eq. (3.4)'s recursive mini-batch-size identity. -/
@[simp]
theorem theorem1OnlineSchedule_S2
    [Norm E] (L sigma epsilon n0 : ℝ) :
    (theorem1OnlineSchedule (E := E) L sigma epsilon n0).S2 =
      2 * sigma * (epsilon * n0)⁻¹ := by
  rfl

/-- Eq. (3.4)'s base stepsize identity. -/
@[simp]
theorem theorem1OnlineSchedule_eta
    [Norm E] (L sigma epsilon n0 : ℝ) :
    (theorem1OnlineSchedule (E := E) L sigma epsilon n0).eta =
      epsilon * (L * n0)⁻¹ := by
  rfl

/-- Eq. (3.4)'s epoch-length identity. -/
@[simp]
theorem theorem1OnlineSchedule_q
    [Norm E] (L sigma epsilon n0 : ℝ) :
    (theorem1OnlineSchedule (E := E) L sigma epsilon n0).q =
      sigma * n0 * epsilon⁻¹ := by
  rfl

/-- Eq. (3.4)'s adaptive Option II stepsize identity. -/
@[simp]
theorem theorem1OnlineSchedule_etaK
    [Norm E] (L sigma epsilon n0 : ℝ) (v : E) :
    (theorem1OnlineSchedule (E := E) L sigma epsilon n0).etaK v =
      min (epsilon * (L * n0 * ‖v‖)⁻¹) ((2 * L * n0)⁻¹) := by
  rfl

/-- Canonical natural batch count used to realize the paper's real-valued
refresh size in a Lean sample-index type. -/
noncomputable def theorem1RefreshBatchCount (sigma epsilon : ℝ) : ℕ :=
  Nat.ceil (onlineRefreshBatchSize sigma epsilon)

/-- Canonical natural batch count used to realize the paper's real-valued
recursive mini-batch size in a Lean sample-index type. -/
noncomputable def theorem1RecursiveBatchCount (sigma epsilon n0 : ℝ) : ℕ :=
  Nat.ceil (onlineRecursiveBatchSize sigma epsilon n0)

/-- Canonical natural epoch length used to realize the paper's real-valued
epoch length in a Lean modulo condition. -/
noncomputable def theorem1EpochCount (sigma epsilon n0 : ℝ) : ℕ :=
  Nat.ceil (onlineEpochLength sigma epsilon n0)

/-- The iteration budget printed in Theorem 1.

Source: `book/research/SPIDER.json#/algorithm_spec/parameters/1`, quote
`K=⌊(4LΔn₀)ε^{-2}⌋+1`, with `Δ` supplied by
`book/research/SPIDER.json#/assumptions/0`, quote `Δ := f(x_0)-f^*<∞`. -/
noncomputable def theorem1Budget (L Delta n0 epsilon : ℝ) : ℕ :=
  Nat.floor (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) + 1

/-- Theorem 1's iteration budget specialized to the paper's initial gap object. -/
noncomputable def theorem1ProblemBudget
    [MeasurableSpace Sample]
    {d : ℕ} (P : OnlineProblem Sample (VariableSpace d)) (n0 epsilon : ℝ) : ℕ :=
  theorem1Budget P.L P.Delta n0 epsilon

/-- The paper-specialized budget unfolds to the formula with
`Δ = f(x₀)-f*`. -/
theorem theorem1ProblemBudget_def
    [MeasurableSpace Sample]
    {d : ℕ} (P : OnlineProblem Sample (VariableSpace d)) (n0 epsilon : ℝ) :
    theorem1ProblemBudget P n0 epsilon =
      Nat.floor (4 * P.L * P.Delta * n0 * epsilon⁻¹ ^ 2) + 1 := by
  rfl

/-- Paper-facing free-parameter range for Theorem 1.

The real-valued schedule itself is given by `onlineRefreshBatchSize`,
`onlineRecursiveBatchSize`, `optionIBaseStepSize`, `optionIIStepSize`, and
`onlineEpochLength`; natural batch counts for Lean sample arrays are canonical
ceilings, not theorem-head feasibility hypotheses.

Source: `book/research/SPIDER.json#/assumptions/18`, quote
`n_0∈[1,2σ/ε]`; also printed in Theorem 1's cost sentence. -/
def Theorem1Schedule
    (_L sigma epsilon n0 : ℝ) : Prop :=
  1 ≤ n0 ∧ n0 ≤ 2 * sigma * epsilon⁻¹

/-- Lower endpoint of Theorem 1's quoted free-parameter interval. -/
theorem Theorem1Schedule.n0_lower
    {L sigma epsilon n0 : ℝ} (h : Theorem1Schedule L sigma epsilon n0) :
    1 ≤ n0 :=
  h.1

/-- Upper endpoint of Theorem 1's quoted free-parameter interval. -/
theorem Theorem1Schedule.n0_upper
    {L sigma epsilon n0 : ℝ} (h : Theorem1Schedule L sigma epsilon n0) :
    n0 ≤ 2 * sigma * epsilon⁻¹ :=
  h.2

/-- Source-boundary marker for Eq. (3.4)'s denominator gap.

The PDF prints quotients involving `ε`, `L n₀`, and `L n₀ ‖vᵏ‖`, and uses
`q = σ n₀ / ε` in modulo/counting expressions.  It does not list the
corresponding nonzero-denominator facts as Theorem 1 hypotheses.  This marker
therefore carries no denominator assertion; helper theorems that use Lean's
totalized inverse arithmetic must remain visibly helper-level. -/
def theorem1Eq34DenominatorSourceGap : Prop :=
  True

/-- Recorded source-boundary fact for Eq. (3.4)'s missing denominator domain. -/
theorem theorem1_eq34_denominator_source_gap :
    theorem1Eq34DenominatorSourceGap := by
  trivial

/-- Mini-batch refresh estimator `∇ f_{S₁}(x)` from Algorithm 1, line 3. -/
noncomputable def refreshEstimator
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x : E) {S1 : ℕ} (samples : Fin S1 → Sample) : E :=
  (S1 : ℝ)⁻¹ •
    Finset.sum Finset.univ (fun i : Fin S1 => sampleGrad x (samples i))

/-- The refresh estimator unfolds to the finite sample average printed in line 3. -/
@[simp]
theorem refreshEstimator_def
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x : E) {S1 : ℕ} (samples : Fin S1 → Sample) :
    refreshEstimator sampleGrad x samples =
      (S1 : ℝ)⁻¹ •
        Finset.sum Finset.univ (fun i : Fin S1 => sampleGrad x (samples i)) := by
  rfl

/-- Recursive SPIDER estimator update from Algorithm 1, line 5.

This reuses SOptLib's canonical SARAH/SPIDER finite mini-batch gradient
difference average. -/
noncomputable def recursiveEstimator
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (vPrev xPrev xCurr : E)
    {S2 : ℕ} (samples : Fin S2 → Sample) : E :=
  SOptLib.recursiveGradientDifferenceAverage sampleGrad vPrev xPrev xCurr samples

/-- The recursive estimator unfolds to `∇f_{S₂}(xᵏ) - ∇f_{S₂}(xᵏ⁻¹) + vᵏ⁻¹`. -/
@[simp]
theorem recursiveEstimator_def
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (vPrev xPrev xCurr : E)
    {S2 : ℕ} (samples : Fin S2 → Sample) :
    recursiveEstimator sampleGrad vPrev xPrev xCurr samples =
      (Fintype.card (Fin S2) : ℝ)⁻¹ •
          Finset.sum Finset.univ
            (fun i : Fin S2 =>
              sampleGrad xCurr (samples i) - sampleGrad xPrev (samples i)) +
        vPrev := by
  rfl

/-- Option I normalized-gradient update from Algorithm 1, lines 8-11.

The return branch is represented as the identity on `x`; a separate consumer can
interpret that branch as early termination. -/
noncomputable def optionIUpdate
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (epsilonTilde epsilon L n0 : ℝ) (x v : E) : E :=
  if ‖v‖ ≤ 2 * epsilonTilde then
    x
  else
    x - optionIBaseStepSize epsilon L n0 • (‖v‖⁻¹ • v)

/-- Option II adaptive step size from Algorithm 1, line 14. -/
noncomputable def optionIIStepSize
    [Norm E] (epsilon L n0 : ℝ) (v : E) : ℝ :=
  min (epsilon * (L * n0 * ‖v‖)⁻¹) ((2 * L * n0)⁻¹)

/-- Option II update `xᵏ⁺¹ = xᵏ - ηᵏ vᵏ` from Algorithm 1, line 14. -/
noncomputable def optionIIUpdate
    [Norm E] [Sub E] [SMul ℝ E]
    (epsilon L n0 : ℝ) (x v : E) : E :=
  x - optionIIStepSize epsilon L n0 v • v

/-- State carried by the SPIDER-SFO recursion: iterate and gradient estimator. -/
structure State (E : Type*) where
  x : E
  v : E

/-- One SPIDER-SFO Option II transition.

Given the previous state at time `k`, this first performs the line-14 primal
update, then constructs `v^{k+1}` by either line 3 or line 5 according to the
epoch-refresh condition. -/
noncomputable def optionIITransition
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : Fin S1 → Sample)
    (recursiveSamples : Fin S2 → Sample)
    (k : ℕ) (state : State E) : State E :=
  let xNext := optionIIUpdate epsilon L n0 state.x state.v
  let vNext :=
    if (k + 1) % q = 0 then
      refreshEstimator sampleGrad xNext refreshSamples
    else
      recursiveEstimator sampleGrad state.v state.x xNext recursiveSamples
  { x := xNext, v := vNext }

/-- Canonical SPIDER-SFO Option II state process generated by Algorithm 1. -/
noncomputable def optionIIStateProcess
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample) :
    ℕ → Ω → State E
  | 0 => fun ω =>
      { x := x0, v := refreshEstimator sampleGrad x0 (refreshSamples 0 ω) }
  | k + 1 => fun ω =>
      optionIITransition sampleGrad S1 S2 q epsilon L n0
        (refreshSamples (k + 1) ω)
        (recursiveSamples (k + 1) ω)
        k
        (optionIIStateProcess sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples k ω)

/-- Initial state: `x⁰ = x₀` and `v⁰ = ∇f_{S₁}(x₀)`. -/
@[simp]
theorem optionIIStateProcess_zero
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample) (ω : Ω) :
    optionIIStateProcess sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples 0 ω =
      { x := x0, v := refreshEstimator sampleGrad x0 (refreshSamples 0 ω) } := by
  rfl

/-- Successor state follows the Algorithm 1 refresh/recursive-estimator branch. -/
@[simp]
theorem optionIIStateProcess_succ
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample) (k : ℕ) (ω : Ω) :
    optionIIStateProcess sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples
        (k + 1) ω =
      optionIITransition sampleGrad S1 S2 q epsilon L n0
        (refreshSamples (k + 1) ω)
        (recursiveSamples (k + 1) ω)
        k
        (optionIIStateProcess sampleGrad x0 S1 S2 q epsilon L n0
          refreshSamples recursiveSamples k ω) := by
  rfl

/-- Iterates are projections of the canonical state process, not Setup fields. -/
noncomputable def optionIIIterate
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample) :
    ℕ → Ω → E :=
  fun k ω =>
    (optionIIStateProcess sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples k ω).x

/-- Gradient estimators are projections of the canonical state process. -/
noncomputable def optionIIEstimator
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample) :
    ℕ → Ω → E :=
  fun k ω =>
    (optionIIStateProcess sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples k ω).v

/-- The projected iterate sequence satisfies the line-14 update rule. -/
@[simp]
theorem optionIIIterate_succ
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample) (k : ℕ) (ω : Ω) :
    optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples
        (k + 1) ω =
      optionIIUpdate epsilon L n0
        (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples k ω)
        (optionIIEstimator sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples k ω) := by
  rfl

/-- The projected estimator sequence satisfies the Algorithm 1 branch rule. -/
@[simp]
theorem optionIIEstimator_succ
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample) (k : ℕ) (ω : Ω) :
    optionIIEstimator sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples
        (k + 1) ω =
      if (k + 1) % q = 0 then
        refreshEstimator sampleGrad
          (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples
            (k + 1) ω)
          (refreshSamples (k + 1) ω)
      else
        recursiveEstimator sampleGrad
          (optionIIEstimator sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples k ω)
          (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples k ω)
          (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples
            (k + 1) ω)
          (recursiveSamples (k + 1) ω) := by
  rfl

/-- A refresh mini-batch estimator is measurable when the sampled-gradient
kernel is jointly measurable and the random query/sample coordinates are
measurable. -/
theorem refreshEstimator_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [MeasurableAdd₂ E] [MeasurableSMul ℝ E]
    (sampleGrad : E → Sample → E) {x : Ω → E} {S1 : ℕ}
    {samples : Ω → Fin S1 → Sample}
    (h_sampleGrad_joint_measurable :
      Measurable (fun p : E × Sample => sampleGrad p.1 p.2))
    (hx : Measurable x)
    (hsamples : ∀ i : Fin S1, Measurable (fun ω => samples ω i)) :
    Measurable (fun ω => refreshEstimator sampleGrad (x ω) (samples ω)) := by
  have hcoord :
      ∀ i : Fin S1, Measurable (fun ω => sampleGrad (x ω) (samples ω i)) := by
    intro i
    exact SOptLib.sampledOracle_measurable h_sampleGrad_joint_measurable hx (hsamples i)
  unfold refreshEstimator
  fun_prop

/-- A recursive SPIDER mini-batch estimator is measurable under the same
joint sampled-gradient regularity and measurable query/sample inputs. -/
theorem recursiveEstimator_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E] [MeasurableSMul ℝ E]
    (sampleGrad : E → Sample → E)
    {vPrev xPrev xCurr : Ω → E} {S2 : ℕ}
    {samples : Ω → Fin S2 → Sample}
    (h_sampleGrad_joint_measurable :
      Measurable (fun p : E × Sample => sampleGrad p.1 p.2))
    (hvPrev : Measurable vPrev)
    (hxPrev : Measurable xPrev)
    (hxCurr : Measurable xCurr)
    (hsamples : ∀ i : Fin S2, Measurable (fun ω => samples ω i)) :
    Measurable
      (fun ω =>
        recursiveEstimator sampleGrad (vPrev ω) (xPrev ω) (xCurr ω) (samples ω)) := by
  have hcoord_curr :
      ∀ i : Fin S2, Measurable (fun ω => sampleGrad (xCurr ω) (samples ω i)) := by
    intro i
    exact SOptLib.sampledOracle_measurable h_sampleGrad_joint_measurable hxCurr (hsamples i)
  have hcoord_prev :
      ∀ i : Fin S2, Measurable (fun ω => sampleGrad (xPrev ω) (samples ω i)) := by
    intro i
    exact SOptLib.sampledOracle_measurable h_sampleGrad_joint_measurable hxPrev (hsamples i)
  unfold recursiveEstimator SOptLib.recursiveGradientDifferenceAverage
  fun_prop

/-- The Option II primal update is measurable as a deterministic function of a
measurable iterate and estimator. -/
theorem optionIIUpdate_measurable
    [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSub₂ E] [MeasurableSMul ℝ E]
    (epsilon L n0 : ℝ) {x v : Ω → E}
    (hx : Measurable x) (hv : Measurable v) :
    Measurable (fun ω => optionIIUpdate epsilon L n0 (x ω) (v ω)) := by
  unfold optionIIUpdate optionIIStepSize
  fun_prop

/-- The generated Option II iterate/estimator process is measurable at every
finite time once the sampled-gradient kernel is jointly measurable.

This is the Lean-side regularity bridge needed before random-query
expectations in Lemma 2, Lemma 4, Lemma 5, and Eq. (B.15) can be instantiated.
It is a derived process theorem, not a new paper assumption. -/
theorem optionII_process_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E] [MeasurableSMul ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample)
    (h_sampleGrad_joint_measurable :
      Measurable (fun p : E × Sample => sampleGrad p.1 p.2))
    (hrefreshSamples_measurable :
      ∀ k i, Measurable (fun ω => refreshSamples k ω i))
    (hrecursiveSamples_measurable :
      ∀ k i, Measurable (fun ω => recursiveSamples k ω i)) :
    ∀ k,
      Measurable (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
        refreshSamples recursiveSamples k) ∧
      Measurable (optionIIEstimator sampleGrad x0 S1 S2 q epsilon L n0
        refreshSamples recursiveSamples k) := by
  intro k
  induction k with
  | zero =>
      constructor
      · change Measurable (fun _ : Ω => x0)
        exact measurable_const
      · convert
          refreshEstimator_measurable
            (sampleGrad := sampleGrad)
            (x := fun _ : Ω => x0)
            (samples := fun ω => refreshSamples 0 ω)
            h_sampleGrad_joint_measurable
            measurable_const
            (fun i => hrefreshSamples_measurable 0 i) using 1
  | succ k ih =>
      let iterate :=
        optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
          refreshSamples recursiveSamples
      let estimator :=
        optionIIEstimator sampleGrad x0 S1 S2 q epsilon L n0
          refreshSamples recursiveSamples
      have hiterate_k : Measurable (iterate k) := ih.1
      have hestimator_k : Measurable (estimator k) := ih.2
      have hiterate_succ : Measurable (iterate (k + 1)) := by
        have hnext :
            Measurable
              (fun ω => optionIIUpdate epsilon L n0 (iterate k ω) (estimator k ω)) :=
          optionIIUpdate_measurable epsilon L n0 hiterate_k hestimator_k
        simpa [iterate, estimator] using hnext
      have hestimator_succ : Measurable (estimator (k + 1)) := by
        by_cases hbranch : (k + 1) % q = 0
        · have hrefresh :
              Measurable
                (fun ω =>
                  refreshEstimator sampleGrad (iterate (k + 1) ω)
                    (refreshSamples (k + 1) ω)) :=
            refreshEstimator_measurable
              (sampleGrad := sampleGrad)
              (x := iterate (k + 1))
              (samples := fun ω => refreshSamples (k + 1) ω)
              h_sampleGrad_joint_measurable
              hiterate_succ
              (fun i => hrefreshSamples_measurable (k + 1) i)
          convert hrefresh using 1
          funext ω
          simp [estimator, iterate, hbranch]
        · have hrecursive :
              Measurable
                (fun ω =>
                  recursiveEstimator sampleGrad (estimator k ω) (iterate k ω)
                    (iterate (k + 1) ω) (recursiveSamples (k + 1) ω)) :=
            recursiveEstimator_measurable
              (sampleGrad := sampleGrad)
              (vPrev := estimator k)
              (xPrev := iterate k)
              (xCurr := iterate (k + 1))
              (samples := fun ω => recursiveSamples (k + 1) ω)
              h_sampleGrad_joint_measurable
              hestimator_k
              hiterate_k
              hiterate_succ
              (fun i => hrecursiveSamples_measurable (k + 1) i)
          convert hrecursive using 1
          funext ω
          simp [estimator, iterate, hbranch]
      exact ⟨hiterate_succ, hestimator_succ⟩

/-- A.e.-strong measurability form of `optionII_process_measurable`, suitable
for Bochner integrability and conditional-expectation leaves. -/
theorem optionII_process_aestronglyMeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [MeasurableAdd₂ E] [MeasurableSub₂ E] [MeasurableSMul ℝ E]
    (mu : Measure Ω)
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample)
    (h_sampleGrad_joint_measurable :
      Measurable (fun p : E × Sample => sampleGrad p.1 p.2))
    (hrefreshSamples_measurable :
      ∀ k i, Measurable (fun ω => refreshSamples k ω i))
    (hrecursiveSamples_measurable :
      ∀ k i, Measurable (fun ω => recursiveSamples k ω i)) :
    ∀ k,
      AEStronglyMeasurable (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
        refreshSamples recursiveSamples k) mu ∧
      AEStronglyMeasurable (optionIIEstimator sampleGrad x0 S1 S2 q epsilon L n0
        refreshSamples recursiveSamples k) mu := by
  intro k
  have hmeas :=
    optionII_process_measurable
      sampleGrad x0 S1 S2 q epsilon L n0 refreshSamples recursiveSamples
      h_sampleGrad_joint_measurable hrefreshSamples_measurable hrecursiveSamples_measurable k
  exact ⟨hmeas.1.aestronglyMeasurable, hmeas.2.aestronglyMeasurable⟩

/-- Canonical sample space for Algorithm 1's online draws: an iid refresh
mini-batch stream paired with an iid recursive mini-batch stream. -/
abbrev OnlineRunSamplePath (S1 S2 : ℕ) (Sample : Type*) : Type _ :=
  SOptLib.miniBatchSamplePath S1 Sample × SOptLib.miniBatchSamplePath S2 Sample

/-- Canonical product law for the Algorithm 1 online sample streams. -/
noncomputable def onlineRunLaw
    [MeasurableSpace Sample] (S1 S2 : ℕ) (sampleLaw : Measure Sample) :
    Measure (OnlineRunSamplePath S1 S2 Sample) :=
  (SOptLib.iidMiniBatchSampleLaw S1 sampleLaw).prod
    (SOptLib.iidMiniBatchSampleLaw S2 sampleLaw)

/-- The refresh samples used by the generated Algorithm 1 run are the first
coordinate of the iid product sample path. -/
def onlineRefreshSamples (S1 S2 : ℕ) :
    ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S1 → Sample :=
  fun k ω => ω.1 k

/-- The recursive samples used by the generated Algorithm 1 run are the second
coordinate of the iid product sample path. -/
def onlineRecursiveSamples (S1 S2 : ℕ) :
    ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample :=
  fun k ω => ω.2 k

/-- The generated Option II iterate process under the canonical online draw law. -/
noncomputable def onlineOptionIIIterate
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ) :
    ℕ → OnlineRunSamplePath S1 S2 Sample → E :=
  optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
    (onlineRefreshSamples S1 S2) (onlineRecursiveSamples S1 S2)

/-- The canonical online run law is built from iid mini-batch laws with marginal
`sampleLaw`; this is the object-layer sampling rule behind Algorithm 1 lines
3 and 5. -/
theorem onlineRunLaw_spec
    [MeasurableSpace Sample] (S1 S2 : ℕ) (sampleLaw : Measure Sample)
    [IsProbabilityMeasure sampleLaw] :
    IsProbabilityMeasure (onlineRunLaw S1 S2 sampleLaw) := by
  unfold onlineRunLaw
  infer_instance

/-- Each canonical refresh-stream coordinate has the online sample law under
the product run law. -/
theorem onlineRunLaw_map_onlineRefreshSamples
    [MeasurableSpace Sample] (S1 S2 : ℕ) (sampleLaw : Measure Sample)
    [IsProbabilityMeasure sampleLaw] (k : ℕ) (i : Fin S1) :
    Measure.map
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          onlineRefreshSamples (Sample := Sample) S1 S2 k ω i)
        (onlineRunLaw S1 S2 sampleLaw) =
      sampleLaw := by
  have hfst :
      Measure.map (fun ω : OnlineRunSamplePath S1 S2 Sample => ω.1)
          (onlineRunLaw S1 S2 sampleLaw) =
        SOptLib.iidMiniBatchSampleLaw S1 sampleLaw := by
    unfold onlineRunLaw OnlineRunSamplePath
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmap :
      Measure.map
          (fun ω : SOptLib.miniBatchSamplePath S1 Sample => ω k i)
          (Measure.map (fun ω : OnlineRunSamplePath S1 S2 Sample => ω.1)
            (onlineRunLaw S1 S2 sampleLaw)) =
        Measure.map
          (fun ω : OnlineRunSamplePath S1 S2 Sample => ω.1 k i)
          (onlineRunLaw S1 S2 sampleLaw) := by
    have heval :
        Measurable (fun ω : SOptLib.miniBatchSamplePath S1 Sample => ω k i) := by
      fun_prop
    simpa using
      (Measure.map_map heval measurable_fst)
  simpa [onlineRefreshSamples] using
    (by
      rw [← hmap, hfst]
      exact SOptLib.iidMiniBatchSampleLaw_map_eval S1 sampleLaw k i)

/-- Each canonical recursive-stream coordinate has the online sample law under
the product run law. -/
theorem onlineRunLaw_map_onlineRecursiveSamples
    [MeasurableSpace Sample] (S1 S2 : ℕ) (sampleLaw : Measure Sample)
    [IsProbabilityMeasure sampleLaw] (k : ℕ) (i : Fin S2) :
    Measure.map
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i)
        (onlineRunLaw S1 S2 sampleLaw) =
      sampleLaw := by
  have hsnd :
      Measure.map (fun ω : OnlineRunSamplePath S1 S2 Sample => ω.2)
          (onlineRunLaw S1 S2 sampleLaw) =
        SOptLib.iidMiniBatchSampleLaw S2 sampleLaw := by
    unfold onlineRunLaw OnlineRunSamplePath
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hmap :
      Measure.map
          (fun ω : SOptLib.miniBatchSamplePath S2 Sample => ω k i)
          (Measure.map (fun ω : OnlineRunSamplePath S1 S2 Sample => ω.2)
            (onlineRunLaw S1 S2 sampleLaw)) =
        Measure.map
          (fun ω : OnlineRunSamplePath S1 S2 Sample => ω.2 k i)
          (onlineRunLaw S1 S2 sampleLaw) := by
    have heval :
        Measurable (fun ω : SOptLib.miniBatchSamplePath S2 Sample => ω k i) := by
      fun_prop
    simpa using
      (Measure.map_map heval measurable_snd)
  simpa [onlineRecursiveSamples] using
    (by
      rw [← hmap, hsnd]
      exact SOptLib.iidMiniBatchSampleLaw_map_eval S2 sampleLaw k i)

/-- Flatten two independent coordinate families into one Sum-indexed family.

This is the pure probability conversion needed after the product law has
identified the two whole streams as independent. -/
theorem iIndepFun_sum_of_indepFun_and_components
    {Ω S ι κ : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω}
    {ξ₁ : ι → Ω → S} {ξ₂ : κ → Ω → S}
    (hξ₁_meas : ∀ i, Measurable (ξ₁ i))
    (hξ₂_meas : ∀ j, Measurable (ξ₂ j))
    (hξ₁_iIndep : ProbabilityTheory.iIndepFun ξ₁ μ)
    (hξ₂_iIndep : ProbabilityTheory.iIndepFun ξ₂ μ)
    (hstreams_indep :
      ProbabilityTheory.IndepFun
        (fun ω => fun i => ξ₁ i ω)
        (fun ω => fun j => ξ₂ j ω) μ) :
    ProbabilityTheory.iIndepFun
      (fun idx (ω : Ω) =>
        match idx with
        | Sum.inl i => ξ₁ i ω
        | Sum.inr j => ξ₂ j ω) μ := by
  classical
  haveI : IsProbabilityMeasure μ := hξ₁_iIndep.isProbabilityMeasure
  let O := Unit ⊕ Unit
  let K : O → Type (max u_6 u_7) :=
    fun o =>
      match o with
      | Sum.inl _ => ULift.{max u_6 u_7, u_6} ι
      | Sum.inr _ => ULift.{max u_6 u_7, u_7} κ
  let X : (o : O) → K o → Ω → S :=
    fun o =>
      match o with
      | Sum.inl _ => fun i => ξ₁ i.down
      | Sum.inr _ => fun j => ξ₂ j.down
  have hX_meas : ∀ o j, Measurable (X o j) := by
    intro o j
    cases o with
    | inl _ => exact hξ₁_meas j.down
    | inr _ => exact hξ₂_meas j.down
  have hstreams_indep_lift :
      ProbabilityTheory.IndepFun
        (fun ω => fun i : ULift.{max u_6 u_7, u_6} ι => ξ₁ i.down ω)
        (fun ω => fun j : ULift.{max u_6 u_7, u_7} κ => ξ₂ j.down ω) μ := by
    let φ : (ι → S) → (ULift.{max u_6 u_7, u_6} ι → S) := fun f i => f i.down
    let ψ : (κ → S) → (ULift.{max u_6 u_7, u_7} κ → S) := fun f j => f j.down
    have hφ : Measurable φ := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_pi_apply i.down
    have hψ : Measurable ψ := by
      rw [measurable_pi_iff]
      intro j
      exact measurable_pi_apply j.down
    simpa [φ, ψ, Function.comp_def] using hstreams_indep.comp hφ hψ
  have hproc : ProbabilityTheory.iIndepFun (fun o (ω : Ω) => (X o · ω)) μ := by
    rw [ProbabilityTheory.iIndepFun_iff]
    intro s sets hs
    let a : O := Sum.inl ()
    let b : O := Sum.inr ()
    by_cases ha : a ∈ s
    · by_cases hb : b ∈ s
      · have hs_eq : s = {a, b} := by
          ext x
          cases x with
          | inl u =>
              cases u
              simp [a, b, ha]
          | inr u =>
              cases u
              simp [a, b, hb]
        subst s
        simp [a, b] at hs ⊢
        exact hstreams_indep_lift.meas_inter hs.1 hs.2
      · have hs_eq : s = {a} := by
          ext x
          cases x with
          | inl u =>
              cases u
              simp [a, ha]
          | inr u =>
              cases u
              simp [a, b, hb]
        subst s
        simp [a]
    · by_cases hb : b ∈ s
      · have hs_eq : s = {b} := by
          ext x
          cases x with
          | inl u =>
              cases u
              simp [a, b, ha]
          | inr u =>
              cases u
              simp [b, hb]
        subst s
        simp [b]
      · have hs_eq : s = ∅ := by
          ext x
          cases x with
          | inl u =>
              cases u
              simp [a, ha]
          | inr u =>
              cases u
              simp [b, hb]
        subst s
        simp
  have hcomp : ∀ o, ProbabilityTheory.iIndepFun (X o) μ := by
    intro o
    cases o with
    | inl _ =>
        exact hξ₁_iIndep.precomp
          (g := fun i : ULift.{max u_6 u_7, u_6} ι => i.down)
          (by
            intro a b h
            cases a
            cases b
            simp at h
            simp [h])
    | inr _ =>
        exact hξ₂_iIndep.precomp
          (g := fun j : ULift.{max u_6 u_7, u_7} κ => j.down)
          (by
            intro a b h
            cases a
            cases b
            simp at h
            simp [h])
  have hsigma : ProbabilityTheory.iIndepFun (fun p : Sigma K => X p.1 p.2) μ := by
    exact ProbabilityTheory.iIndepFun_uncurry hX_meas hproc hcomp
  let g : ι ⊕ κ → Sigma K :=
    fun idx =>
      match idx with
      | Sum.inl i => ⟨Sum.inl (), ULift.up i⟩
      | Sum.inr j => ⟨Sum.inr (), ULift.up j⟩
  have hg : Function.Injective g := by
    intro a b h
    cases a with
    | inl i =>
        cases b with
        | inl _ =>
            cases h
            rfl
        | inr _ => simp [g] at h
    | inr j =>
        cases b with
        | inl _ => simp [g] at h
        | inr _ =>
            cases h
            rfl
  have hpre := hsigma.precomp (g := g) hg
  refine (ProbabilityTheory.iIndepFun_congr (μ := μ) ?_).1 hpre
  intro idx
  filter_upwards with ω
  cases idx <;> rfl

/-- Product-law bridge for two independent coordinate families on separate
sample spaces. -/
theorem iIndepFun_sum_of_prod_iIndepFun
    {Ω₁ Ω₂ S ι κ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace S]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    {ξ₁ : ι → Ω₁ → S} {ξ₂ : κ → Ω₂ → S}
    (hξ₁_meas : ∀ i, Measurable (ξ₁ i))
    (hξ₂_meas : ∀ j, Measurable (ξ₂ j))
    (hξ₁_iIndep : ProbabilityTheory.iIndepFun ξ₁ μ₁)
    (hξ₂_iIndep : ProbabilityTheory.iIndepFun ξ₂ μ₂) :
    ProbabilityTheory.iIndepFun
      (fun idx (ω : Ω₁ × Ω₂) =>
        match idx with
        | Sum.inl i => ξ₁ i ω.1
        | Sum.inr j => ξ₂ j ω.2) (μ₁.prod μ₂) := by
  classical
  let Ξ₁ : Ω₁ → ι → S := fun ω i => ξ₁ i ω
  let Ξ₂ : Ω₂ → κ → S := fun ω j => ξ₂ j ω
  have hΞ₁_meas : Measurable Ξ₁ := by
    rw [measurable_pi_iff]
    exact hξ₁_meas
  have hΞ₂_meas : Measurable Ξ₂ := by
    rw [measurable_pi_iff]
    exact hξ₂_meas
  have hfst_map : Measure.map Prod.fst (μ₁.prod μ₂) = μ₁ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd_map : Measure.map Prod.snd (μ₁.prod μ₂) = μ₂ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hΞ₁_comp_map :
      Measure.map (Ξ₁ ∘ Prod.fst) (μ₁.prod μ₂) = Measure.map Ξ₁ μ₁ := by
    rw [← Measure.map_map (μ := μ₁.prod μ₂) hΞ₁_meas measurable_fst, hfst_map]
  have hΞ₂_comp_map :
      Measure.map (Ξ₂ ∘ Prod.snd) (μ₁.prod μ₂) = Measure.map Ξ₂ μ₂ := by
    rw [← Measure.map_map (μ := μ₁.prod μ₂) hΞ₂_meas measurable_snd, hsnd_map]
  have hξ₁_comp_map (i : ι) :
      Measure.map ((ξ₁ i) ∘ Prod.fst) (μ₁.prod μ₂) = Measure.map (ξ₁ i) μ₁ := by
    rw [← Measure.map_map (μ := μ₁.prod μ₂) (hξ₁_meas i) measurable_fst, hfst_map]
  have hξ₂_comp_map (j : κ) :
      Measure.map ((ξ₂ j) ∘ Prod.snd) (μ₁.prod μ₂) = Measure.map (ξ₂ j) μ₂ := by
    rw [← Measure.map_map (μ := μ₁.prod μ₂) (hξ₂_meas j) measurable_snd, hsnd_map]
  have hleft_iIndep :
      ProbabilityTheory.iIndepFun
        (fun i (ω : Ω₁ × Ω₂) => ξ₁ i ω.1) (μ₁.prod μ₂) := by
    change ProbabilityTheory.iIndepFun
      (fun i => (ξ₁ i) ∘ Prod.fst) (μ₁.prod μ₂)
    rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      (mX := fun i => (hξ₁_meas i).comp measurable_fst)]
    calc
      Measure.map (fun ω : Ω₁ × Ω₂ => fun i => ξ₁ i ω.1) (μ₁.prod μ₂)
          = Measure.map Ξ₁ μ₁ := by
            change Measure.map (Ξ₁ ∘ Prod.fst) (μ₁.prod μ₂) = Measure.map Ξ₁ μ₁
            exact hΞ₁_comp_map
      _ = Measure.infinitePi (fun i => Measure.map (ξ₁ i) μ₁) := by
            exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
              hξ₁_meas).1 hξ₁_iIndep
      _ = Measure.infinitePi
            (fun i => Measure.map (fun ω : Ω₁ × Ω₂ => ξ₁ i ω.1) (μ₁.prod μ₂)) := by
            congr
            funext i
            change Measure.map (ξ₁ i) μ₁ =
              Measure.map ((ξ₁ i) ∘ Prod.fst) (μ₁.prod μ₂)
            exact (hξ₁_comp_map i).symm
  have hright_iIndep :
      ProbabilityTheory.iIndepFun
        (fun j (ω : Ω₁ × Ω₂) => ξ₂ j ω.2) (μ₁.prod μ₂) := by
    change ProbabilityTheory.iIndepFun
      (fun j => (ξ₂ j) ∘ Prod.snd) (μ₁.prod μ₂)
    rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      (mX := fun j => (hξ₂_meas j).comp measurable_snd)]
    calc
      Measure.map (fun ω : Ω₁ × Ω₂ => fun j => ξ₂ j ω.2) (μ₁.prod μ₂)
          = Measure.map Ξ₂ μ₂ := by
            change Measure.map (Ξ₂ ∘ Prod.snd) (μ₁.prod μ₂) = Measure.map Ξ₂ μ₂
            exact hΞ₂_comp_map
      _ = Measure.infinitePi (fun j => Measure.map (ξ₂ j) μ₂) := by
            exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
              hξ₂_meas).1 hξ₂_iIndep
      _ = Measure.infinitePi
            (fun j => Measure.map (fun ω : Ω₁ × Ω₂ => ξ₂ j ω.2) (μ₁.prod μ₂)) := by
            congr
            funext j
            change Measure.map (ξ₂ j) μ₂ =
              Measure.map ((ξ₂ j) ∘ Prod.snd) (μ₁.prod μ₂)
            exact (hξ₂_comp_map j).symm
  have hpair_law :
      Measure.map (fun ω : Ω₁ × Ω₂ => (Ξ₁ ω.1, Ξ₂ ω.2)) (μ₁.prod μ₂) =
        (Measure.map Ξ₁ μ₁).prod (Measure.map Ξ₂ μ₂) := by
    simpa [Ξ₁, Ξ₂] using
      (Measure.map_prod_map μ₁ μ₂ hΞ₁_meas hΞ₂_meas).symm
  have hstreams_indep :
      ProbabilityTheory.IndepFun
        (fun ω : Ω₁ × Ω₂ => fun i => ξ₁ i ω.1)
        (fun ω : Ω₁ × Ω₂ => fun j => ξ₂ j ω.2) (μ₁.prod μ₂) := by
    have hZ_meas :
        AEMeasurable (fun ω : Ω₁ × Ω₂ => (Ξ₁ ω.1, Ξ₂ ω.2)) (μ₁.prod μ₂) :=
      ((hΞ₁_meas.comp measurable_fst).prod (hΞ₂_meas.comp measurable_snd)).aemeasurable
    haveI : IsProbabilityMeasure (Measure.map Ξ₁ μ₁) :=
      Measure.isProbabilityMeasure_map hΞ₁_meas.aemeasurable
    haveI : IsProbabilityMeasure (Measure.map Ξ₂ μ₂) :=
      Measure.isProbabilityMeasure_map hΞ₂_meas.aemeasurable
    simpa [Ξ₁, Ξ₂] using
      (indepFun_of_map_prod_eq_prod_laws
        (P := μ₁.prod μ₂)
        (Z := fun ω : Ω₁ × Ω₂ => (Ξ₁ ω.1, Ξ₂ ω.2))
        (mu := Measure.map Ξ₁ μ₁) (nu := Measure.map Ξ₂ μ₂)
        hZ_meas hpair_law)
  exact iIndepFun_sum_of_indepFun_and_components
    (μ := μ₁.prod μ₂)
    (ξ₁ := fun i (ω : Ω₁ × Ω₂) => ξ₁ i ω.1)
    (ξ₂ := fun j (ω : Ω₁ × Ω₂) => ξ₂ j ω.2)
    (fun i => (hξ₁_meas i).comp measurable_fst)
    (fun j => (hξ₂_meas j).comp measurable_snd)
    hleft_iIndep hright_iIndep hstreams_indep

/-- A fixed-query refresh coordinate under the canonical product run law
inherits the online variance bound. -/
theorem onlineRunLaw_refresh_fixed_residual_sq_integrable_le
    [MeasurableSpace Sample] {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (S1 S2 : ℕ) (k : ℕ) (i : Fin S1) (x : VariableSpace d) :
    Integrable
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          ‖P.sampleGrad x (onlineRefreshSamples (Sample := Sample) S1 S2 k ω i) -
              P.grad x‖ ^ 2)
        (onlineRunLaw S1 S2 P.sampleLaw) ∧
      ∫ ω, ‖P.sampleGrad x (onlineRefreshSamples (Sample := Sample) S1 S2 k ω i) -
          P.grad x‖ ^ 2 ∂onlineRunLaw S1 S2 P.sampleLaw ≤
        P.sigma ^ 2 := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  let Y : OnlineRunSamplePath S1 S2 Sample → Sample :=
    fun ω => onlineRefreshSamples (Sample := Sample) S1 S2 k ω i
  let φ : Sample → ℝ := fun s => ‖P.sampleGrad x s - P.grad x‖ ^ 2
  have hY_meas : Measurable Y := by
    dsimp [Y, onlineRefreshSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
    fun_prop
  have hmapY : Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) = P.sampleLaw := by
    simpa [Y] using
      onlineRunLaw_map_onlineRefreshSamples
        (Sample := Sample) S1 S2 P.sampleLaw k i
  have hsampleGrad_x : Measurable (fun s : Sample => P.sampleGrad x s) := by
    simpa using
      P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => x).prodMk measurable_id)
  have hφ_meas : Measurable φ := by
    dsimp [φ]
    fun_prop
  have hφ_aesm : AEStronglyMeasurable φ (Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw)) :=
    hφ_meas.aestronglyMeasurable
  have hsample_int : Integrable φ P.sampleLaw := by
    simpa [φ, SOptLib.expectationWellDefined] using
      P.online_gradient_variance_wellDefined x
  have hcomp_int :
      Integrable (fun ω : OnlineRunSamplePath S1 S2 Sample => φ (Y ω))
        (onlineRunLaw S1 S2 P.sampleLaw) := by
    exact
      (MeasureTheory.integrable_map_measure hφ_aesm hY_meas.aemeasurable).1
        (by simpa [hmapY] using hsample_int)
  have hcomp_bound :
      ∫ ω : OnlineRunSamplePath S1 S2 Sample, φ (Y ω)
          ∂onlineRunLaw S1 S2 P.sampleLaw ≤
        P.sigma ^ 2 := by
    have hmap_int :
        ∫ s, φ s ∂Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) =
          ∫ ω : OnlineRunSamplePath S1 S2 Sample, φ (Y ω)
            ∂onlineRunLaw S1 S2 P.sampleLaw :=
      MeasureTheory.integral_map hY_meas.aemeasurable hφ_aesm
    rw [← hmap_int, hmapY]
    simpa [φ] using P.online_gradient_variance_bound x
  exact ⟨by simpa [Y, φ] using hcomp_int, by simpa [Y, φ] using hcomp_bound⟩

/-- A fixed-query refresh coordinate under the canonical product run law is
centered whenever the fixed sample-law residual is centered. -/
theorem onlineRunLaw_refresh_fixed_residual_integral_eq_zero
    [MeasurableSpace Sample] {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (S1 S2 : ℕ) (k : ℕ) (i : Fin S1) (x : VariableSpace d)
    (hfixed_zero :
      ∫ s, P.sampleGrad x s - P.grad x ∂P.sampleLaw = 0) :
    ∫ ω : OnlineRunSamplePath S1 S2 Sample,
        P.sampleGrad x (onlineRefreshSamples (Sample := Sample) S1 S2 k ω i) -
          P.grad x ∂onlineRunLaw S1 S2 P.sampleLaw = 0 := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  let Y : OnlineRunSamplePath S1 S2 Sample → Sample :=
    fun ω => onlineRefreshSamples (Sample := Sample) S1 S2 k ω i
  let φ : Sample → VariableSpace d := fun s => P.sampleGrad x s - P.grad x
  have hY_meas : Measurable Y := by
    dsimp [Y, onlineRefreshSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
    fun_prop
  have hmapY : Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) = P.sampleLaw := by
    simpa [Y] using
      onlineRunLaw_map_onlineRefreshSamples
        (Sample := Sample) S1 S2 P.sampleLaw k i
  have hsampleGrad_x : Measurable (fun s : Sample => P.sampleGrad x s) := by
    simpa using
      P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => x).prodMk measurable_id)
  have hφ_aesm :
      AEStronglyMeasurable φ (Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw)) := by
    dsimp [φ]
    exact (hsampleGrad_x.sub measurable_const).aestronglyMeasurable
  have hmap_int :
      ∫ s, φ s ∂Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) =
        ∫ ω : OnlineRunSamplePath S1 S2 Sample, φ (Y ω)
          ∂onlineRunLaw S1 S2 P.sampleLaw :=
    MeasureTheory.integral_map hY_meas.aemeasurable hφ_aesm
  rw [← hmap_int, hmapY]
  simpa [φ] using hfixed_zero

/-- A fixed-query recursive coordinate under the canonical product run law
inherits the averaged Lipschitz gradient-difference bound. -/
theorem onlineRunLaw_recursive_fixed_difference_sq_integrable_le
    [MeasurableSpace Sample] {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (S1 S2 : ℕ) (k : ℕ) (i : Fin S2) (x y : VariableSpace d) :
    Integrable
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          ‖(P.sampleGrad x
                (onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i) -
              P.sampleGrad y
                (onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i))‖ ^ 2)
        (onlineRunLaw S1 S2 P.sampleLaw) ∧
      ∫ ω,
          ‖(P.sampleGrad x
                (onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i) -
              P.sampleGrad y
                (onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i))‖ ^ 2
            ∂onlineRunLaw S1 S2 P.sampleLaw ≤
        P.L ^ 2 * ‖x - y‖ ^ 2 := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  let Y : OnlineRunSamplePath S1 S2 Sample → Sample :=
    fun ω => onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i
  let φ : Sample → ℝ :=
    fun s => ‖P.sampleGrad x s - P.sampleGrad y s‖ ^ 2
  have hY_meas : Measurable Y := by
    dsimp [Y, onlineRecursiveSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
    fun_prop
  have hmapY : Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) = P.sampleLaw := by
    simpa [Y] using
      onlineRunLaw_map_onlineRecursiveSamples
        (Sample := Sample) S1 S2 P.sampleLaw k i
  have hsampleGrad_x : Measurable (fun s : Sample => P.sampleGrad x s) := by
    simpa using
      P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => x).prodMk measurable_id)
  have hsampleGrad_y : Measurable (fun s : Sample => P.sampleGrad y s) := by
    simpa using
      P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => y).prodMk measurable_id)
  have hφ_meas : Measurable φ := by
    dsimp [φ]
    fun_prop
  have hφ_aesm : AEStronglyMeasurable φ (Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw)) :=
    hφ_meas.aestronglyMeasurable
  have hsample_int : Integrable φ P.sampleLaw := by
    simpa [φ, SOptLib.expectationWellDefined] using
      P.averaged_lipschitz_gradient_wellDefined x y
  have hcomp_int :
      Integrable (fun ω : OnlineRunSamplePath S1 S2 Sample => φ (Y ω))
        (onlineRunLaw S1 S2 P.sampleLaw) := by
    exact
      (MeasureTheory.integrable_map_measure hφ_aesm hY_meas.aemeasurable).1
        (by simpa [hmapY] using hsample_int)
  have hcomp_bound :
      ∫ ω : OnlineRunSamplePath S1 S2 Sample, φ (Y ω)
          ∂onlineRunLaw S1 S2 P.sampleLaw ≤
        P.L ^ 2 * ‖x - y‖ ^ 2 := by
    have hmap_int :
        ∫ s, φ s ∂Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) =
          ∫ ω : OnlineRunSamplePath S1 S2 Sample, φ (Y ω)
            ∂onlineRunLaw S1 S2 P.sampleLaw :=
      MeasureTheory.integral_map hY_meas.aemeasurable hφ_aesm
    rw [← hmap_int, hmapY]
    simpa [φ] using P.averaged_lipschitz_gradient_bound x y
  exact ⟨by simpa [Y, φ] using hcomp_int, by simpa [Y, φ] using hcomp_bound⟩

/-- A fixed-query recursive gradient-difference coordinate under the canonical
product run law is centered whenever the fixed sample-law difference residual
is centered. -/
theorem onlineRunLaw_recursive_fixed_difference_integral_eq_zero
    [MeasurableSpace Sample] {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (S1 S2 : ℕ) (k : ℕ) (i : Fin S2) (x y : VariableSpace d)
    (hdiff_fixed_zero :
      ∫ s, (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
        ∂P.sampleLaw = 0) :
    ∫ ω : OnlineRunSamplePath S1 S2 Sample,
        (P.sampleGrad x
            (onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i) -
          P.sampleGrad y
            (onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i)) -
          (P.grad x - P.grad y)
        ∂onlineRunLaw S1 S2 P.sampleLaw = 0 := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  let Y : OnlineRunSamplePath S1 S2 Sample → Sample :=
    fun ω => onlineRecursiveSamples (Sample := Sample) S1 S2 k ω i
  let φ : Sample → VariableSpace d :=
    fun s => (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
  have hY_meas : Measurable Y := by
    dsimp [Y, onlineRecursiveSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
    fun_prop
  have hmapY : Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) = P.sampleLaw := by
    simpa [Y] using
      onlineRunLaw_map_onlineRecursiveSamples
        (Sample := Sample) S1 S2 P.sampleLaw k i
  have hsampleGrad_x : Measurable (fun s : Sample => P.sampleGrad x s) := by
    simpa using
      P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => x).prodMk measurable_id)
  have hsampleGrad_y : Measurable (fun s : Sample => P.sampleGrad y s) := by
    simpa using
      P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => y).prodMk measurable_id)
  have hφ_aesm :
      AEStronglyMeasurable φ (Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw)) := by
    dsimp [φ]
    exact ((hsampleGrad_x.sub hsampleGrad_y).sub measurable_const).aestronglyMeasurable
  have hmap_int :
      ∫ s, φ s ∂Measure.map Y (onlineRunLaw S1 S2 P.sampleLaw) =
        ∫ ω : OnlineRunSamplePath S1 S2 Sample, φ (Y ω)
          ∂onlineRunLaw S1 S2 P.sampleLaw :=
    MeasureTheory.integral_map hY_meas.aemeasurable hφ_aesm
  rw [← hmap_int, hmapY]
  simpa [φ] using hdiff_fixed_zero

/-- Product-run freshness needed for the refresh mini-batch variance step.

At time `t`, the Option II iterate is determined before the refresh mini-batch
draws at time `t`; distinct coordinates in that fresh mini-batch are mutually
fresh even after adjoining the iterate and one peer coordinate. -/
theorem optionII_refresh_iterate_current_sample_freshness
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (S1 S2 q : ℕ)
    (mu : Measure (OnlineRunSamplePath S1 S2 Sample))
    (iterate : ℕ → OnlineRunSamplePath S1 S2 Sample → VariableSpace d)
    (refreshSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S1 → Sample)
    (recursiveSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample)
    (hmu_eq :
      mu = onlineRunLaw S1 S2 P.sampleLaw)
    (hrefreshSamples_eq :
      refreshSamples = onlineRefreshSamples (Sample := Sample) S1 S2)
    (hrecursiveSamples_eq :
      recursiveSamples = onlineRecursiveSamples (Sample := Sample) S1 S2)
    (hiterate_eq :
      iterate =
        optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples)
    (hrefresh_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S1) (ω : SOptLib.miniBatchSamplePath S1 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw))
    (hrecursive_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S2) (ω : SOptLib.miniBatchSamplePath S2 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw)) :
    ∀ t,
      (∀ i : Fin S1,
        ProbabilityTheory.IndepFun
          (iterate t)
          (fun ω => refreshSamples t ω i) mu) ∧
      (∀ i j : Fin S1, i ≠ j →
        ProbabilityTheory.IndepFun
          (fun ω => (iterate t ω, refreshSamples t ω j))
          (fun ω => refreshSamples t ω i) mu) := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  haveI : IsProbabilityMeasure mu := by
    rw [hmu_eq]
    exact onlineRunLaw_spec S1 S2 P.sampleLaw
  let I := (ℕ × Fin S1) ⊕ (ℕ × Fin S2)
  let sampleCoord : I → OnlineRunSamplePath S1 S2 Sample → Sample :=
    fun idx ω =>
      match idx with
      | Sum.inl kr => refreshSamples kr.1 ω kr.2
      | Sum.inr kr => recursiveSamples kr.1 ω kr.2
  let pastSet : ℕ → Set I :=
    fun t idx =>
      match idx with
      | Sum.inl kr => kr.1 < t
      | Sum.inr kr => kr.1 < t
  let pastMS : ℕ → MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) :=
    fun t => ⨆ idx, ⨆ _ : idx ∈ pastSet t,
      MeasurableSpace.comap (sampleCoord idx) (by infer_instance : MeasurableSpace Sample)
  have hsampleCoord_meas : ∀ idx, Measurable (sampleCoord idx) := by
    intro idx
    cases idx with
    | inl kr =>
        change Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          refreshSamples kr.1 ω kr.2)
        rw [hrefreshSamples_eq]
        dsimp [onlineRefreshSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
        fun_prop
    | inr kr =>
        change Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          recursiveSamples kr.1 ω kr.2)
        rw [hrecursiveSamples_eq]
        dsimp [onlineRecursiveSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
        fun_prop
  have hsampleCoord_iIndep : ProbabilityTheory.iIndepFun sampleCoord mu := by
    subst refreshSamples
    subst recursiveSamples
    subst mu
    change ProbabilityTheory.iIndepFun
      (fun (idx : (ℕ × Fin S1) ⊕ (ℕ × Fin S2))
          (ω : SOptLib.miniBatchSamplePath S1 Sample ×
              SOptLib.miniBatchSamplePath S2 Sample) =>
        match idx with
        | Sum.inl kr => ω.1 kr.1 kr.2
        | Sum.inr kr => ω.2 kr.1 kr.2)
      ((SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw).prod
        (SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw))
    convert
      (iIndepFun_sum_of_prod_iIndepFun
        (μ₁ := SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw)
        (μ₂ := SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw)
        (ξ₁ := fun (kr : ℕ × Fin S1) (ω : SOptLib.miniBatchSamplePath S1 Sample) =>
          ω kr.1 kr.2)
        (ξ₂ := fun (kr : ℕ × Fin S2) (ω : SOptLib.miniBatchSamplePath S2 Sample) =>
          ω kr.1 kr.2)
        (by intro kr; fun_prop)
        (by intro kr; fun_prop)
        hrefresh_iIndep hrecursive_iIndep) using 2
    cases ‹(ℕ × Fin S1) ⊕ (ℕ × Fin S2)› <;> funext ω <;> rfl
  have hupdate_measurable_wrt :
      ∀ (m : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample))
        {x v : OnlineRunSamplePath S1 S2 Sample → VariableSpace d},
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) x →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) v →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance)
          (fun ω => optionIIUpdate epsilon P.L n0 (x ω) (v ω)) := by
    intro m x v hx hv
    letI : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) := m
    exact optionIIUpdate_measurable epsilon P.L n0 hx hv
  have hrefreshEstimator_measurable_wrt :
      ∀ (m : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample))
        {x : OnlineRunSamplePath S1 S2 Sample → VariableSpace d}
        {samples : OnlineRunSamplePath S1 S2 Sample → Fin S1 → Sample},
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) x →
        (∀ i : Fin S1,
          @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample m
            (by infer_instance) (fun ω => samples ω i)) →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance)
          (fun ω => refreshEstimator P.sampleGrad (x ω) (samples ω)) := by
    intro m x samples hx hsamples
    letI : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) := m
    exact refreshEstimator_measurable
      (sampleGrad := P.sampleGrad)
      P.sampleGrad_joint_measurable hx hsamples
  have hrecursiveEstimator_measurable_wrt :
      ∀ (m : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample))
        {vPrev xPrev xCurr : OnlineRunSamplePath S1 S2 Sample → VariableSpace d}
        {samples : OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample},
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) vPrev →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) xPrev →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) xCurr →
        (∀ i : Fin S2,
          @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample m
            (by infer_instance) (fun ω => samples ω i)) →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance)
          (fun ω => recursiveEstimator P.sampleGrad (vPrev ω) (xPrev ω)
            (xCurr ω) (samples ω)) := by
    intro m vPrev xPrev xCurr samples hvPrev hxPrev hxCurr hsamples
    letI : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) := m
    exact recursiveEstimator_measurable
      (sampleGrad := P.sampleGrad)
      P.sampleGrad_joint_measurable hvPrev hxPrev hxCurr hsamples
  have hpastMS_mono : ∀ {a b : ℕ}, a ≤ b → pastMS a ≤ pastMS b := by
    intro a b hab
    dsimp [pastMS]
    refine iSup_le ?_
    intro idx
    refine iSup_le ?_
    intro hidx
    refine le_iSup_of_le idx ?_
    refine le_iSup_of_le ?_ le_rfl
    cases idx with
    | inl kr =>
        exact lt_of_lt_of_le hidx hab
    | inr kr =>
        exact lt_of_lt_of_le hidx hab
  have hrefresh_past :
      ∀ {r t : ℕ} (i : Fin S1), r < t →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample (pastMS t)
          (by infer_instance)
          (fun ω : OnlineRunSamplePath S1 S2 Sample => refreshSamples r ω i) := by
    intro r t i hr
    refine Measurable.of_comap_le ?_
    dsimp [pastMS, sampleCoord]
    exact le_iSup_of_le (Sum.inl (r, i)) (le_iSup_of_le hr le_rfl)
  have hrecursive_past :
      ∀ {r t : ℕ} (i : Fin S2), r < t →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample (pastMS t)
          (by infer_instance)
          (fun ω : OnlineRunSamplePath S1 S2 Sample => recursiveSamples r ω i) := by
    intro r t i hr
    refine Measurable.of_comap_le ?_
    dsimp [pastMS, sampleCoord]
    exact le_iSup_of_le (Sum.inr (r, i)) (le_iSup_of_le hr le_rfl)
  have hcanonical_adapted :
      ∀ k,
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) (pastMS k)
          (by infer_instance)
          (optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples k) ∧
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) (pastMS (k + 1))
          (by infer_instance)
          (optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples k) := by
    intro k
    induction k with
    | zero =>
        constructor
        · change @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d)
            (pastMS 0) (by infer_instance)
            (fun _ : OnlineRunSamplePath S1 S2 Sample => P.x0)
          exact measurable_const
        · convert
            hrefreshEstimator_measurable_wrt (pastMS (0 + 1))
              (x := fun _ : OnlineRunSamplePath S1 S2 Sample => P.x0)
              (samples := fun ω => refreshSamples 0 ω)
              measurable_const
              (fun i => hrefresh_past i (Nat.zero_lt_succ 0)) using 1
    | succ k ih =>
        let iter :=
          optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples
        let est :=
          optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples
        have hiter_k_succ : @Measurable (OnlineRunSamplePath S1 S2 Sample)
            (VariableSpace d) (pastMS (k + 1)) (by infer_instance) (iter k) :=
          ih.1.mono (hpastMS_mono (Nat.le_succ k)) le_rfl
        have hiter_succ : @Measurable (OnlineRunSamplePath S1 S2 Sample)
            (VariableSpace d) (pastMS (k + 1)) (by infer_instance) (iter (k + 1)) := by
          have hnext : @Measurable (OnlineRunSamplePath S1 S2 Sample)
              (VariableSpace d) (pastMS (k + 1)) (by infer_instance)
              (fun ω : OnlineRunSamplePath S1 S2 Sample =>
                optionIIUpdate epsilon P.L n0 (iter k ω) (est k ω)) :=
            hupdate_measurable_wrt (pastMS (k + 1)) hiter_k_succ ih.2
          simpa [iter, est] using hnext
        have hiter_succ_next : @Measurable (OnlineRunSamplePath S1 S2 Sample)
            (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance)
            (iter (k + 1)) :=
          hiter_succ.mono (hpastMS_mono (Nat.le_succ (k + 1))) le_rfl
        constructor
        · exact hiter_succ
        · by_cases hbranch : (k + 1) % q = 0
          · have hrefresh : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance)
                (fun ω : OnlineRunSamplePath S1 S2 Sample =>
                  refreshEstimator P.sampleGrad (iter (k + 1) ω)
                    (refreshSamples (k + 1) ω)) :=
              hrefreshEstimator_measurable_wrt (pastMS ((k + 1) + 1))
                (x := iter (k + 1))
                (samples := fun ω => refreshSamples (k + 1) ω)
                hiter_succ_next
                (fun i => hrefresh_past i (Nat.lt_succ_self (k + 1)))
            convert hrefresh using 1
            funext ω
            simp [iter, hbranch]
          · have hest_k_next : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance) (est k) :=
              ih.2.mono (hpastMS_mono (Nat.le_succ (k + 1))) le_rfl
            have hiter_k_next : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance) (iter k) :=
              hiter_k_succ.mono (hpastMS_mono (Nat.le_succ (k + 1))) le_rfl
            have hrecursive : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance)
                (fun ω : OnlineRunSamplePath S1 S2 Sample =>
                  recursiveEstimator P.sampleGrad (est k ω) (iter k ω)
                    (iter (k + 1) ω) (recursiveSamples (k + 1) ω)) :=
              hrecursiveEstimator_measurable_wrt (pastMS ((k + 1) + 1))
                (vPrev := est k)
                (xPrev := iter k)
                (xCurr := iter (k + 1))
                (samples := fun ω => recursiveSamples (k + 1) ω)
                hest_k_next
                hiter_k_next
                hiter_succ_next
                (fun i => hrecursive_past i (Nat.lt_succ_self (k + 1)))
            convert hrecursive using 1
            funext ω
            simp [est, iter, hbranch]
  have hiterate_past : ∀ t, @Measurable (OnlineRunSamplePath S1 S2 Sample)
      (VariableSpace d) (pastMS t) (by infer_instance) (iterate t) := by
    intro t
    rw [hiterate_eq]
    exact (hcanonical_adapted t).1
  intro t
  constructor
  · intro i
    have hpast_current_disj : Disjoint (pastSet t) ({Sum.inl (t, i)} : Set I) := by
      rw [Set.disjoint_left]
      intro idx hpast hcur
      rcases hcur with rfl
      exact (Nat.lt_irrefl t hpast)
    have hfresh :=
      (indepFun_prefixKey_current_of_iIndepFun
        (sampleCoord := sampleCoord)
        hsampleCoord_meas hsampleCoord_iIndep
        (pastSet := pastSet t) (strictPast := pastMS t)
        (prefixKey := iterate t) (current := Sum.inl (t, i))
        (hiterate_past t) le_rfl hpast_current_disj).1
    simpa [sampleCoord] using hfresh
  · intro i j hij
    have hleft_disj :
        Disjoint (pastSet t ∪ ({Sum.inl (t, j)} : Set I))
          ({Sum.inl (t, i)} : Set I) := by
      rw [Set.disjoint_left]
      intro idx hleft hcur
      rcases hcur with rfl
      rcases hleft with hpast | hpeer
      · exact Nat.lt_irrefl t hpast
      · have hpair : (t, i) = (t, j) := Sum.inl.inj hpeer
        exact hij (congrArg Prod.snd hpair)
    have hpast_current_disj : Disjoint (pastSet t) ({Sum.inl (t, i)} : Set I) := by
      rw [Set.disjoint_left]
      intro idx hpast hcur
      rcases hcur with rfl
      exact Nat.lt_irrefl t hpast
    have hfresh_pair :=
      (indepFun_prefixKey_current_of_iIndepFun
        (sampleCoord := sampleCoord)
        hsampleCoord_meas hsampleCoord_iIndep
        (pastSet := pastSet t) (strictPast := pastMS t)
        (prefixKey := iterate t) (current := Sum.inl (t, i))
        (hiterate_past t) le_rfl hpast_current_disj).2
        (Sum.inl (t, j)) hleft_disj
    simpa [sampleCoord] using hfresh_pair

/-- Product-run freshness needed for the recursive mini-batch variance step.

At time `t + 1`, the Option II recursive mini-batch is fresh relative to the
already generated pair of iterates and previous estimator; distinct coordinates
remain fresh after adjoining one peer coordinate. -/
theorem optionII_recursive_current_sample_freshness
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (S1 S2 q : ℕ)
    (mu : Measure (OnlineRunSamplePath S1 S2 Sample))
    (iterate estimator :
      ℕ → OnlineRunSamplePath S1 S2 Sample → VariableSpace d)
    (refreshSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S1 → Sample)
    (recursiveSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample)
    (hmu_eq :
      mu = onlineRunLaw S1 S2 P.sampleLaw)
    (hrefreshSamples_eq :
      refreshSamples = onlineRefreshSamples (Sample := Sample) S1 S2)
    (hrecursiveSamples_eq :
      recursiveSamples = onlineRecursiveSamples (Sample := Sample) S1 S2)
    (hiterate_eq :
      iterate =
        optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples)
    (hestimator_eq :
      estimator =
        optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples)
    (hrefresh_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S1) (ω : SOptLib.miniBatchSamplePath S1 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw))
    (hrecursive_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S2) (ω : SOptLib.miniBatchSamplePath S2 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw)) :
    ∀ t,
      (∀ i : Fin S2,
        ProbabilityTheory.IndepFun
          (fun ω => ((iterate t ω, iterate (t + 1) ω), estimator t ω))
          (fun ω => recursiveSamples (t + 1) ω i) mu) ∧
      (∀ i j : Fin S2, i ≠ j →
        ProbabilityTheory.IndepFun
          (fun ω =>
            (((iterate t ω, iterate (t + 1) ω), estimator t ω),
              recursiveSamples (t + 1) ω j))
          (fun ω => recursiveSamples (t + 1) ω i) mu) := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  haveI : IsProbabilityMeasure mu := by
    rw [hmu_eq]
    exact onlineRunLaw_spec S1 S2 P.sampleLaw
  let I := (ℕ × Fin S1) ⊕ (ℕ × Fin S2)
  let sampleCoord : I → OnlineRunSamplePath S1 S2 Sample → Sample :=
    fun idx ω =>
      match idx with
      | Sum.inl kr => refreshSamples kr.1 ω kr.2
      | Sum.inr kr => recursiveSamples kr.1 ω kr.2
  let pastSet : ℕ → Set I :=
    fun t idx =>
      match idx with
      | Sum.inl kr => kr.1 < t
      | Sum.inr kr => kr.1 < t
  let pastMS : ℕ → MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) :=
    fun t => ⨆ idx, ⨆ _ : idx ∈ pastSet t,
      MeasurableSpace.comap (sampleCoord idx) (by infer_instance : MeasurableSpace Sample)
  have hsampleCoord_meas : ∀ idx, Measurable (sampleCoord idx) := by
    intro idx
    cases idx with
    | inl kr =>
        change Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          refreshSamples kr.1 ω kr.2)
        rw [hrefreshSamples_eq]
        dsimp [onlineRefreshSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
        fun_prop
    | inr kr =>
        change Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          recursiveSamples kr.1 ω kr.2)
        rw [hrecursiveSamples_eq]
        dsimp [onlineRecursiveSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
        fun_prop
  have hsampleCoord_iIndep : ProbabilityTheory.iIndepFun sampleCoord mu := by
    subst refreshSamples
    subst recursiveSamples
    subst mu
    change ProbabilityTheory.iIndepFun
      (fun (idx : (ℕ × Fin S1) ⊕ (ℕ × Fin S2))
          (ω : SOptLib.miniBatchSamplePath S1 Sample ×
              SOptLib.miniBatchSamplePath S2 Sample) =>
        match idx with
        | Sum.inl kr => ω.1 kr.1 kr.2
        | Sum.inr kr => ω.2 kr.1 kr.2)
      ((SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw).prod
        (SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw))
    convert
      (iIndepFun_sum_of_prod_iIndepFun
        (μ₁ := SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw)
        (μ₂ := SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw)
        (ξ₁ := fun (kr : ℕ × Fin S1) (ω : SOptLib.miniBatchSamplePath S1 Sample) =>
          ω kr.1 kr.2)
        (ξ₂ := fun (kr : ℕ × Fin S2) (ω : SOptLib.miniBatchSamplePath S2 Sample) =>
          ω kr.1 kr.2)
        (by intro kr; fun_prop)
        (by intro kr; fun_prop)
        hrefresh_iIndep hrecursive_iIndep) using 2
    cases ‹(ℕ × Fin S1) ⊕ (ℕ × Fin S2)› <;> funext ω <;> rfl
  have hupdate_measurable_wrt :
      ∀ (m : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample))
        {x v : OnlineRunSamplePath S1 S2 Sample → VariableSpace d},
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) x →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) v →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance)
          (fun ω => optionIIUpdate epsilon P.L n0 (x ω) (v ω)) := by
    intro m x v hx hv
    letI : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) := m
    exact optionIIUpdate_measurable epsilon P.L n0 hx hv
  have hrefreshEstimator_measurable_wrt :
      ∀ (m : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample))
        {x : OnlineRunSamplePath S1 S2 Sample → VariableSpace d}
        {samples : OnlineRunSamplePath S1 S2 Sample → Fin S1 → Sample},
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) x →
        (∀ i : Fin S1,
          @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample m
            (by infer_instance) (fun ω => samples ω i)) →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance)
          (fun ω => refreshEstimator P.sampleGrad (x ω) (samples ω)) := by
    intro m x samples hx hsamples
    letI : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) := m
    exact refreshEstimator_measurable
      (sampleGrad := P.sampleGrad)
      P.sampleGrad_joint_measurable hx hsamples
  have hrecursiveEstimator_measurable_wrt :
      ∀ (m : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample))
        {vPrev xPrev xCurr : OnlineRunSamplePath S1 S2 Sample → VariableSpace d}
        {samples : OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample},
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) vPrev →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) xPrev →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance) xCurr →
        (∀ i : Fin S2,
          @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample m
            (by infer_instance) (fun ω => samples ω i)) →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) m
          (by infer_instance)
          (fun ω => recursiveEstimator P.sampleGrad (vPrev ω) (xPrev ω)
            (xCurr ω) (samples ω)) := by
    intro m vPrev xPrev xCurr samples hvPrev hxPrev hxCurr hsamples
    letI : MeasurableSpace (OnlineRunSamplePath S1 S2 Sample) := m
    exact recursiveEstimator_measurable
      (sampleGrad := P.sampleGrad)
      P.sampleGrad_joint_measurable hvPrev hxPrev hxCurr hsamples
  have hpastMS_mono : ∀ {a b : ℕ}, a ≤ b → pastMS a ≤ pastMS b := by
    intro a b hab
    dsimp [pastMS]
    refine iSup_le ?_
    intro idx
    refine iSup_le ?_
    intro hidx
    refine le_iSup_of_le idx ?_
    refine le_iSup_of_le ?_ le_rfl
    cases idx with
    | inl kr =>
        exact lt_of_lt_of_le hidx hab
    | inr kr =>
        exact lt_of_lt_of_le hidx hab
  have hrefresh_past :
      ∀ {r t : ℕ} (i : Fin S1), r < t →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample (pastMS t)
          (by infer_instance)
          (fun ω : OnlineRunSamplePath S1 S2 Sample => refreshSamples r ω i) := by
    intro r t i hr
    refine Measurable.of_comap_le ?_
    dsimp [pastMS, sampleCoord]
    exact le_iSup_of_le (Sum.inl (r, i)) (le_iSup_of_le hr le_rfl)
  have hrecursive_past :
      ∀ {r t : ℕ} (i : Fin S2), r < t →
        @Measurable (OnlineRunSamplePath S1 S2 Sample) Sample (pastMS t)
          (by infer_instance)
          (fun ω : OnlineRunSamplePath S1 S2 Sample => recursiveSamples r ω i) := by
    intro r t i hr
    refine Measurable.of_comap_le ?_
    dsimp [pastMS, sampleCoord]
    exact le_iSup_of_le (Sum.inr (r, i)) (le_iSup_of_le hr le_rfl)
  have hcanonical_adapted :
      ∀ k,
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) (pastMS k)
          (by infer_instance)
          (optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples k) ∧
        @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d) (pastMS (k + 1))
          (by infer_instance)
          (optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples k) := by
    intro k
    induction k with
    | zero =>
        constructor
        · change @Measurable (OnlineRunSamplePath S1 S2 Sample) (VariableSpace d)
            (pastMS 0) (by infer_instance)
            (fun _ : OnlineRunSamplePath S1 S2 Sample => P.x0)
          exact measurable_const
        · convert
            hrefreshEstimator_measurable_wrt (pastMS (0 + 1))
              (x := fun _ : OnlineRunSamplePath S1 S2 Sample => P.x0)
              (samples := fun ω => refreshSamples 0 ω)
              measurable_const
              (fun i => hrefresh_past i (Nat.zero_lt_succ 0)) using 1
    | succ k ih =>
        let iter :=
          optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples
        let est :=
          optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples
        have hiter_k_succ : @Measurable (OnlineRunSamplePath S1 S2 Sample)
            (VariableSpace d) (pastMS (k + 1)) (by infer_instance) (iter k) :=
          ih.1.mono (hpastMS_mono (Nat.le_succ k)) le_rfl
        have hiter_succ : @Measurable (OnlineRunSamplePath S1 S2 Sample)
            (VariableSpace d) (pastMS (k + 1)) (by infer_instance) (iter (k + 1)) := by
          have hnext : @Measurable (OnlineRunSamplePath S1 S2 Sample)
              (VariableSpace d) (pastMS (k + 1)) (by infer_instance)
              (fun ω : OnlineRunSamplePath S1 S2 Sample =>
                optionIIUpdate epsilon P.L n0 (iter k ω) (est k ω)) :=
            hupdate_measurable_wrt (pastMS (k + 1)) hiter_k_succ ih.2
          simpa [iter, est] using hnext
        have hiter_succ_next : @Measurable (OnlineRunSamplePath S1 S2 Sample)
            (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance)
            (iter (k + 1)) :=
          hiter_succ.mono (hpastMS_mono (Nat.le_succ (k + 1))) le_rfl
        constructor
        · exact hiter_succ
        · by_cases hbranch : (k + 1) % q = 0
          · have hrefresh : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance)
                (fun ω : OnlineRunSamplePath S1 S2 Sample =>
                  refreshEstimator P.sampleGrad (iter (k + 1) ω)
                    (refreshSamples (k + 1) ω)) :=
              hrefreshEstimator_measurable_wrt (pastMS ((k + 1) + 1))
                (x := iter (k + 1))
                (samples := fun ω => refreshSamples (k + 1) ω)
                hiter_succ_next
                (fun i => hrefresh_past i (Nat.lt_succ_self (k + 1)))
            convert hrefresh using 1
            funext ω
            simp [iter, hbranch]
          · have hest_k_next : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance) (est k) :=
              ih.2.mono (hpastMS_mono (Nat.le_succ (k + 1))) le_rfl
            have hiter_k_next : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance) (iter k) :=
              hiter_k_succ.mono (hpastMS_mono (Nat.le_succ (k + 1))) le_rfl
            have hrecursive : @Measurable (OnlineRunSamplePath S1 S2 Sample)
                (VariableSpace d) (pastMS ((k + 1) + 1)) (by infer_instance)
                (fun ω : OnlineRunSamplePath S1 S2 Sample =>
                  recursiveEstimator P.sampleGrad (est k ω) (iter k ω)
                    (iter (k + 1) ω) (recursiveSamples (k + 1) ω)) :=
              hrecursiveEstimator_measurable_wrt (pastMS ((k + 1) + 1))
                (vPrev := est k)
                (xPrev := iter k)
                (xCurr := iter (k + 1))
                (samples := fun ω => recursiveSamples (k + 1) ω)
                hest_k_next
                hiter_k_next
                hiter_succ_next
                (fun i => hrecursive_past i (Nat.lt_succ_self (k + 1)))
            convert hrecursive using 1
            funext ω
            simp [est, iter, hbranch]
  have hiterate_past : ∀ t, @Measurable (OnlineRunSamplePath S1 S2 Sample)
      (VariableSpace d) (pastMS t) (by infer_instance) (iterate t) := by
    intro t
    rw [hiterate_eq]
    exact (hcanonical_adapted t).1
  have hestimator_past : ∀ t, @Measurable (OnlineRunSamplePath S1 S2 Sample)
      (VariableSpace d) (pastMS (t + 1)) (by infer_instance) (estimator t) := by
    intro t
    rw [hestimator_eq]
    exact (hcanonical_adapted t).2
  intro t
  have hprefix_past : @Measurable (OnlineRunSamplePath S1 S2 Sample)
      ((VariableSpace d × VariableSpace d) × VariableSpace d) (pastMS (t + 1))
      (by infer_instance)
      (fun ω => ((iterate t ω, iterate (t + 1) ω), estimator t ω)) := by
    exact (((hiterate_past t).mono (hpastMS_mono (Nat.le_succ t)) le_rfl).prodMk
      (hiterate_past (t + 1))).prodMk (hestimator_past t)
  constructor
  · intro i
    have hpast_current_disj : Disjoint (pastSet (t + 1))
        ({Sum.inr (t + 1, i)} : Set I) := by
      rw [Set.disjoint_left]
      intro idx hpast hcur
      rcases hcur with rfl
      exact (Nat.lt_irrefl (t + 1) hpast)
    have hfresh :=
      (indepFun_prefixKey_current_of_iIndepFun
        (sampleCoord := sampleCoord)
        hsampleCoord_meas hsampleCoord_iIndep
        (pastSet := pastSet (t + 1)) (strictPast := pastMS (t + 1))
        (prefixKey := fun ω => ((iterate t ω, iterate (t + 1) ω), estimator t ω))
        (current := Sum.inr (t + 1, i))
        hprefix_past le_rfl hpast_current_disj).1
    simpa [sampleCoord] using hfresh
  · intro i j hij
    have hleft_disj :
        Disjoint (pastSet (t + 1) ∪ ({Sum.inr (t + 1, j)} : Set I))
          ({Sum.inr (t + 1, i)} : Set I) := by
      rw [Set.disjoint_left]
      intro idx hleft hcur
      rcases hcur with rfl
      rcases hleft with hpast | hpeer
      · exact Nat.lt_irrefl (t + 1) hpast
      · have hpair : (t + 1, i) = (t + 1, j) := Sum.inr.inj hpeer
        exact hij (congrArg Prod.snd hpair)
    have hpast_current_disj : Disjoint (pastSet (t + 1))
        ({Sum.inr (t + 1, i)} : Set I) := by
      rw [Set.disjoint_left]
      intro idx hpast hcur
      rcases hcur with rfl
      exact Nat.lt_irrefl (t + 1) hpast
    have hfresh_pair :=
      (indepFun_prefixKey_current_of_iIndepFun
        (sampleCoord := sampleCoord)
        hsampleCoord_meas hsampleCoord_iIndep
        (pastSet := pastSet (t + 1)) (strictPast := pastMS (t + 1))
        (prefixKey := fun ω => ((iterate t ω, iterate (t + 1) ω), estimator t ω))
        (current := Sum.inr (t + 1, i))
        hprefix_past le_rfl hpast_current_disj).2
        (Sum.inr (t + 1, j)) hleft_disj
    simpa [sampleCoord] using hfresh_pair

/-- Uniform-output average corresponding to the expansion in Eq. (B.15). -/
noncomputable def uniformOutputGradientNormAverage
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) (grad : E → E) (iterate : ℕ → Ω → E) (K : ℕ) : ℝ :=
  (K : ℝ)⁻¹ *
    Finset.sum (Finset.range K) (fun k => ∫ ω, ‖grad (iterate k ω)‖ ∂mu)

/-- The finite output window `{0, ..., K-1}` from Algorithm 1, line 17. -/
def optionIIOutputWindow (K : ℕ) : Finset ℕ :=
  Finset.range K

/-- Theorem 1's printed budget is a positive natural number. -/
theorem theorem1Budget_pos (L Delta n0 epsilon : ℝ) :
    0 < theorem1Budget L Delta n0 epsilon := by
  unfold theorem1Budget
  exact Nat.succ_pos _

/-- Uniform law on the Algorithm 1 Option II output window. -/
noncomputable def optionIIUniformOutputPMF
    (K : ℕ) (hK : 0 < K) :
    PMF {k : ℕ // k ∈ optionIIOutputWindow K} :=
  SOptLib.uniformFiniteWindowPMF (optionIIOutputWindow K)
    ⟨0, Finset.mem_range.mpr hK⟩

/-- Source-facing expectation of the gradient norm at the uniformly selected
Option II output. -/
noncomputable def selectedOutputGradientNormExpectation
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) (grad : E → E) (iterate : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) : ℝ :=
  ∫ q : {k : ℕ // k ∈ optionIIOutputWindow K} × Ω,
      ‖grad (iterate q.1.1 q.2)‖ ∂
        ((optionIIUniformOutputPMF K hK).toMeasure.prod mu)

/-- The selected-output expectation expands to the finite average used in the
proof of Theorem 1, Eq. (B.15).  Integrability is a proof obligation for this
bridge, not a public hypothesis of the paper theorem. -/
theorem selectedOutputGradientNormExpectation_eq_uniform_average
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E) (iterate : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K)
    (hint :
      ∀ R : {k : ℕ // k ∈ optionIIOutputWindow K},
        Integrable (fun ω => ‖grad (iterate R.1 ω)‖) mu) :
    selectedOutputGradientNormExpectation mu grad iterate K hK =
      uniformOutputGradientNormAverage mu grad iterate K := by
  classical
  unfold selectedOutputGradientNormExpectation uniformOutputGradientNormAverage
    optionIIUniformOutputPMF optionIIOutputWindow
  have htimes : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.mpr hK⟩
  have hnonneg :
      ∀ k, k ∈ Finset.range K → 0 ≤ (fun _ : ℕ => (1 : ℝ)) k := by
    intro k hk
    norm_num
  have hden : 0 < Finset.sum (Finset.range K) (fun _ : ℕ => (1 : ℝ)) := by
    exact Finset.sum_pos (fun k hk => by norm_num) htimes
  have hsel :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := Finset.range K) (α := fun _ : ℕ => (1 : ℝ))
      (P := mu) (x := iterate) (gap := fun y : E => ‖grad y‖)
      hnonneg hden hint
  simpa [SOptLib.uniformFiniteWindowPMF_def, Finset.sum_const, smul_eq_mul, mul_assoc] using hsel

/-- Paper-level well-definedness of the selected-output gradient-norm
expectation.  The PDF uses expectation notation directly; this is a derived
Lean obligation, not a theorem-head assumption. -/
def selectedOutputGradientNormExpectationWellDefined
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) (grad : E → E) (iterate : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) : Prop :=
  SOptLib.expectationWellDefined
    ((optionIIUniformOutputPMF K hK).toMeasure.prod mu)
    (fun q : {k : ℕ // k ∈ optionIIOutputWindow K} × Ω =>
      ‖grad (iterate q.1.1 q.2)‖)

/-- The selected-output expectation is in the nonfallback expectation branch
once the derived well-definedness obligation is available. -/
theorem selectedOutputGradientNormExpectation_wellDefined_iff
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) (grad : E → E) (iterate : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) :
    selectedOutputGradientNormExpectationWellDefined mu grad iterate K hK ↔
      Integrable
        (fun q : {k : ℕ // k ∈ optionIIOutputWindow K} × Ω =>
          ‖grad (iterate q.1.1 q.2)‖)
        ((optionIIUniformOutputPMF K hK).toMeasure.prod mu) := by
  rfl

/-- The selected-output gradient-norm expectation is nonnegative because its
integrand is a norm. -/
theorem selectedOutputGradientNormExpectation_nonneg
    [MeasurableSpace Ω] [SeminormedAddGroup E]
    (mu : Measure Ω) (grad : E → E) (iterate : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) :
    0 ≤ selectedOutputGradientNormExpectation mu grad iterate K hK := by
  unfold selectedOutputGradientNormExpectation
  refine integral_nonneg ?_
  intro q
  exact norm_nonneg (grad (iterate q.1.1 q.2))

/-- Eq. (B.15) bridge in inequality form: a uniform finite-window average bound
implies the same selected-output expectation bound. -/
theorem selectedOutputGradientNormExpectation_le_of_uniform_average_le
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E) (iterate : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (C : ℝ)
    (hint :
      ∀ R : {k : ℕ // k ∈ optionIIOutputWindow K},
        Integrable (fun ω => ‖grad (iterate R.1 ω)‖) mu)
    (havg : uniformOutputGradientNormAverage mu grad iterate K ≤ C) :
    selectedOutputGradientNormExpectation mu grad iterate K hK ≤ C := by
  rw [selectedOutputGradientNormExpectation_eq_uniform_average mu grad iterate K hK hint]
  exact havg

/-- Raw stochastic-gradient call count for Algorithm 1's online Option II run. -/
noncomputable def onlineGradientCost (K S1 S2 q : ℕ) : ℝ :=
  (Nat.ceil ((K : ℝ) * (q : ℝ)⁻¹) : ℝ) * S1 + K * S2

/-- Source-facing stochastic-gradient call count using the exact real schedule
from Eq. (3.4).  The only ceiling here is the proof's refresh-epoch count
`⌈K/q⌉` from Eq. (B.16), not a replacement for Eq. (3.4)'s batch sizes. -/
noncomputable def onlineGradientCostFromSchedule
    (K : ℕ) (schedule : OnlineSchedule (E := E)) : ℝ :=
  (Nat.ceil ((K : ℝ) * schedule.q⁻¹) : ℝ) * schedule.S1 + (K : ℝ) * schedule.S2

/-- The generated Option II iterate process for Theorem 1.  Its finite sample
arrays are an implementation realization of Algorithm 1's draws; the public
Theorem 1 statement keeps the exact Eq. (3.4) schedule separate. -/
noncomputable def theorem1RealizedOnlineOptionIIIterate
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (sigma epsilon L n0 : ℝ) :
    ℕ →
      OnlineRunSamplePath
        (theorem1RefreshBatchCount sigma epsilon)
        (theorem1RecursiveBatchCount sigma epsilon n0) Sample → E :=
  let S1 := theorem1RefreshBatchCount sigma epsilon
  let S2 := theorem1RecursiveBatchCount sigma epsilon n0
  let q := theorem1EpochCount sigma epsilon n0
  onlineOptionIIIterate sampleGrad x0 S1 S2 q epsilon L n0

/-- Canonical law for the realized online draw streams used by the generated
Theorem 1 Option II process. -/
noncomputable def theorem1RealizedOnlineRunLaw
    [MeasurableSpace Sample] (sampleLaw : Measure Sample)
    (sigma epsilon n0 : ℝ) :
    Measure
      (OnlineRunSamplePath
        (theorem1RefreshBatchCount sigma epsilon)
        (theorem1RecursiveBatchCount sigma epsilon n0) Sample) :=
  onlineRunLaw
    (theorem1RefreshBatchCount sigma epsilon)
    (theorem1RecursiveBatchCount sigma epsilon n0)
    sampleLaw

/-- The gradient-cost upper bound printed in Theorem 1.

Source: `book/research/SPIDER.json#/main_theorem/statement_math`, quote
`16LΔσ·ε^{-3}+2σ^2ε^{-2}+4σn_0^{-1}ε^{-1}`, with `Δ` supplied by
`book/research/SPIDER.json#/assumptions/0`, quote `Δ := f(x_0)-f^*<∞`. -/
noncomputable def theorem1GradientCostBound
    (L Delta sigma n0 epsilon : ℝ) : ℝ :=
  16 * L * Delta * sigma * epsilon⁻¹ ^ 3 +
    2 * sigma ^ 2 * epsilon⁻¹ ^ 2 +
    4 * sigma * n0⁻¹ * epsilon⁻¹

/-- Theorem 1's gradient-cost bound specialized to the paper's initial gap. -/
noncomputable def theorem1ProblemGradientCostBound
    [MeasurableSpace Sample]
    {d : ℕ} (P : OnlineProblem Sample (VariableSpace d)) (n0 epsilon : ℝ) : ℝ :=
  theorem1GradientCostBound P.L P.Delta P.sigma n0 epsilon

/-- The paper-specialized cost bound unfolds to the formula with
`Δ = f(x₀)-f*`. -/
theorem theorem1ProblemGradientCostBound_def
    [MeasurableSpace Sample]
    {d : ℕ} (P : OnlineProblem Sample (VariableSpace d)) (n0 epsilon : ℝ) :
    theorem1ProblemGradientCostBound P n0 epsilon =
      16 * P.L * P.Delta * P.sigma * epsilon⁻¹ ^ 3 +
        2 * P.sigma ^ 2 * epsilon⁻¹ ^ 2 +
        4 * P.sigma * n0⁻¹ * epsilon⁻¹ := by
  rfl

/-- Cost of the natural-number implementation realization of Theorem 1's online
schedule.  This is intentionally separate from the exact real-valued cost
expression used in Eq. (B.16). -/
noncomputable def theorem1RealizedGradientCost
    (K : ℕ) (sigma epsilon n0 : ℝ) : ℝ :=
  onlineGradientCost K
    (theorem1RefreshBatchCount sigma epsilon)
    (theorem1RecursiveBatchCount sigma epsilon n0)
    (theorem1EpochCount sigma epsilon n0)

/-- Output convention labels needed to record the Theorem 1 source boundary. -/
inductive Theorem1OutputConvention where
  | printedOptionI
  | proofUniformOptionII
  deriving DecidableEq

/-- The output convention printed in the Theorem 1 prose. -/
def theorem1PrintedTheoremOutputConvention : Theorem1OutputConvention :=
  Theorem1OutputConvention.printedOptionI

/-- The output convention used by Algorithm 1 line 17 and Eq. (B.15). -/
def theorem1ProofOutputConvention : Theorem1OutputConvention :=
  Theorem1OutputConvention.proofUniformOptionII

/-- Source-boundary marker for the Theorem 1 option-label discrepancy.

The theorem text prints OPTION I, while Algorithm 1 line 17 and Eq. (B.15)
use the uniformly selected OPTION II output.  Keeping this as a named boundary
prevents the proof-oriented statement below from masquerading as the literal
printed theorem without explanation. -/
def theorem1PrintedOptionIProofOptionIIBoundary : Prop :=
  theorem1PrintedTheoremOutputConvention ≠ theorem1ProofOutputConvention

/-- Source-boundary marker for the rounded implementation realization.

The paper prints real-valued quotients for `S₁`, `S₂`, and `q`.  The generated
Lean run uses `Nat.ceil` batch counts and a natural-number modulo denominator
only to obtain finite sample arrays and a total recursive process.  This is not
part of the source theorem's mathematical statement. -/
def theorem1RoundedRealizationSourceGap : Prop :=
  True

/-- Recorded source-boundary fact for the rounded `Nat.ceil` realization gap. -/
theorem theorem1_rounded_realization_source_gap :
    theorem1RoundedRealizationSourceGap := by
  trivial

/-- Combined source-boundary record for the current Theorem 1 formalization. -/
def theorem1SourceBoundary : Prop :=
  theorem1PrintedOptionIProofOptionIIBoundary ∧
    theorem1Eq34DenominatorSourceGap ∧
    theorem1RoundedRealizationSourceGap

/-- Recorded source-boundary fact for Theorem 1's printed/proof option mismatch. -/
theorem theorem1_printed_optionI_proof_optionII_boundary :
    theorem1PrintedOptionIProofOptionIIBoundary := by
  unfold theorem1PrintedOptionIProofOptionIIBoundary
  unfold theorem1PrintedTheoremOutputConvention theorem1ProofOutputConvention
  intro h
  cases h

/-- Legacy unrestricted scalar statement for the Eq. (B.16) cost calculation.

This records the old helper boundary that Phase 2a could not prove.  It is
false because `Delta` is unconstrained here, unlike the paper object
`Δ = f(x₀)-f*`. -/
def theorem1_totalized_schedule_gradient_cost_bound_of_gap_legacy_statement
    [Norm E] : Prop :=
  ∀ L Delta sigma epsilon n0 : ℝ,
    Theorem1Schedule L sigma epsilon n0 →
      let schedule := theorem1OnlineSchedule (E := E) L sigma epsilon n0
      onlineGradientCostFromSchedule
          (E := E)
          (theorem1Budget L Delta n0 epsilon) schedule ≤
        theorem1GradientCostBound L Delta sigma n0 epsilon

/-- Formal counterexample to the old unrestricted scalar helper: with
`L = 1`, `Delta = -100`, `sigma = 1`, `epsilon = 1`, and `n0 = 1`, the
schedule interval holds, but the positive call count is not bounded by the
negative printed expression. -/
theorem theorem1_totalized_schedule_gradient_cost_bound_of_gap_legacy_false :
    ¬ theorem1_totalized_schedule_gradient_cost_bound_of_gap_legacy_statement (E := ℝ) := by
  intro h
  have hsched : Theorem1Schedule (1 : ℝ) 1 1 1 := by
    norm_num [Theorem1Schedule]
  have hbad := h 1 (-100) 1 1 1 hsched
  have hfloor : Nat.floor ((-400 : ℝ)) = 0 :=
    Nat.floor_of_nonpos (by norm_num)
  norm_num [theorem1OnlineSchedule, onlineGradientCostFromSchedule, theorem1Budget,
    theorem1GradientCostBound, onlineRefreshBatchSize, onlineRecursiveBatchSize,
    onlineEpochLength, hfloor] at hbad

/-- Scalar ceiling overshoot line used in Eq. (B.16). -/
theorem ceil_epoch_refresh_cost_bound
    (K : ℕ) {q S1 S2 : ℝ}
    (hq_pos : 0 < q)
    (hS1_nonneg : 0 ≤ S1)
    (hqinvS1 : q⁻¹ * S1 = S2) :
    (Nat.ceil ((K : ℝ) * q⁻¹) : ℝ) * S1 + (K : ℝ) * S2 ≤
      2 * (K : ℝ) * S2 + S1 := by
  have hqinv_nonneg : 0 ≤ q⁻¹ := le_of_lt (inv_pos.mpr hq_pos)
  have harg_nonneg : 0 ≤ (K : ℝ) * q⁻¹ :=
    mul_nonneg (Nat.cast_nonneg K) hqinv_nonneg
  have hceil :
      (Nat.ceil ((K : ℝ) * q⁻¹) : ℝ) ≤ (K : ℝ) * q⁻¹ + 1 :=
    le_of_lt (Nat.ceil_lt_add_one harg_nonneg)
  calc
    (Nat.ceil ((K : ℝ) * q⁻¹) : ℝ) * S1 + (K : ℝ) * S2
        ≤ ((K : ℝ) * q⁻¹ + 1) * S1 + (K : ℝ) * S2 := by
          have hmul := mul_le_mul_of_nonneg_right hceil hS1_nonneg
          nlinarith
    _ = 2 * (K : ℝ) * S2 + S1 := by
          rw [add_mul, one_mul]
          have hKq : (K : ℝ) * q⁻¹ * S1 = (K : ℝ) * S2 := by
            rw [mul_assoc, hqinvS1]
          nlinarith

/-- Scalar floor-budget substitution and inverse algebra for Eq. (B.16). -/
theorem budget_recursive_batch_bound
    (L Delta sigma epsilon n0 : ℝ)
    (hL : 0 ≤ L)
    (hDelta : 0 ≤ Delta)
    (hepsilon : 0 < epsilon)
    (hn0_pos : 0 < n0)
    (hsigma_pos : 0 < sigma) :
    2 * (theorem1Budget L Delta n0 epsilon : ℝ) *
        onlineRecursiveBatchSize sigma epsilon n0 +
        onlineRefreshBatchSize sigma epsilon ≤
      theorem1GradientCostBound L Delta sigma n0 epsilon := by
  let A : ℝ := 4 * L * Delta * n0 * epsilon⁻¹ ^ 2
  let S1 : ℝ := onlineRefreshBatchSize sigma epsilon
  let S2 : ℝ := onlineRecursiveBatchSize sigma epsilon n0
  have heps_inv_nonneg : 0 ≤ epsilon⁻¹ := le_of_lt (inv_pos.mpr hepsilon)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hK_le : (theorem1Budget L Delta n0 epsilon : ℝ) ≤ A + 1 := by
    have hfloor : ((Nat.floor A : ℕ) : ℝ) ≤ A := Nat.floor_le hA_nonneg
    have hbudget_eq :
        (theorem1Budget L Delta n0 epsilon : ℝ) = (Nat.floor A : ℝ) + 1 := by
      unfold theorem1Budget
      dsimp [A]
      norm_num [Nat.cast_add, Nat.cast_one]
    rw [hbudget_eq]
    nlinarith
  have hS2_nonneg : 0 ≤ S2 := by
    dsimp [S2, onlineRecursiveBatchSize]
    positivity
  have htwoS2_nonneg : 0 ≤ 2 * S2 := by positivity
  have hmain :
      2 * (theorem1Budget L Delta n0 epsilon : ℝ) * S2 + S1 ≤
        2 * (A + 1) * S2 + S1 := by
    calc
      2 * (theorem1Budget L Delta n0 epsilon : ℝ) * S2 + S1
          = (theorem1Budget L Delta n0 epsilon : ℝ) * (2 * S2) + S1 := by ring
      _ ≤ (A + 1) * (2 * S2) + S1 := by
          have hmul := mul_le_mul_of_nonneg_right hK_le htwoS2_nonneg
          nlinarith
      _ = 2 * (A + 1) * S2 + S1 := by ring
  have hclosed :
      2 * (A + 1) * S2 + S1 =
        theorem1GradientCostBound L Delta sigma n0 epsilon := by
    dsimp [A, S1, S2]
    unfold onlineRecursiveBatchSize onlineRefreshBatchSize theorem1GradientCostBound
    field_simp [hepsilon.ne', hn0_pos.ne']
    ring
  exact hmain.trans_eq hclosed

/-- Guarded algebraic helper for the Eq. (B.16) cost calculation using Lean's
totalized inverse arithmetic.

This helper is intentionally not the paper-facing theorem: it keeps the gap
scalar abstract but exposes the source-derived sign/domain facts that make the
cost algebra true. -/
theorem theorem1_totalized_schedule_gradient_cost_bound_of_gap_guarded
    [Norm E]
    (L Delta sigma epsilon n0 : ℝ)
    (hL : 0 ≤ L)
    (hDelta : 0 ≤ Delta)
    (hepsilon : 0 < epsilon)
    (_scheduleDomain : Theorem1Schedule L sigma epsilon n0) :
    let schedule := theorem1OnlineSchedule (E := E) L sigma epsilon n0
    onlineGradientCostFromSchedule
        (E := E)
        (theorem1Budget L Delta n0 epsilon) schedule ≤
      theorem1GradientCostBound L Delta sigma n0 epsilon := by
  classical
  let K := theorem1Budget L Delta n0 epsilon
  let S1 := onlineRefreshBatchSize sigma epsilon
  let S2 := onlineRecursiveBatchSize sigma epsilon n0
  let q := onlineEpochLength sigma epsilon n0
  have hn0_lower : 1 ≤ n0 := Theorem1Schedule.n0_lower _scheduleDomain
  have hn0_pos : 0 < n0 := lt_of_lt_of_le zero_lt_one hn0_lower
  have heps_inv_pos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hupper : n0 ≤ 2 * sigma * epsilon⁻¹ := Theorem1Schedule.n0_upper _scheduleDomain
  have hrhs_pos : 0 < 2 * sigma * epsilon⁻¹ := lt_of_lt_of_le hn0_pos hupper
  have hsigma_pos : 0 < sigma := by
    by_contra hsig
    have hsigma_nonpos : sigma ≤ 0 := le_of_not_gt hsig
    have hsigma_eps_nonpos : sigma * epsilon⁻¹ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hsigma_nonpos (le_of_lt heps_inv_pos)
    nlinarith
  have hq_pos : 0 < q := by
    dsimp [q, onlineEpochLength]
    positivity
  have hS1_nonneg : 0 ≤ S1 := by
    dsimp [S1, onlineRefreshBatchSize]
    positivity
  have hqinvS1 : q⁻¹ * S1 = S2 := by
    dsimp [q, S1, S2, onlineEpochLength, onlineRefreshBatchSize,
      onlineRecursiveBatchSize]
    field_simp [hepsilon.ne', hn0_pos.ne', hsigma_pos.ne']
  have hceil_bound :
      (Nat.ceil ((K : ℝ) * q⁻¹) : ℝ) * S1 + (K : ℝ) * S2 ≤
        2 * (K : ℝ) * S2 + S1 :=
    ceil_epoch_refresh_cost_bound K hq_pos hS1_nonneg hqinvS1
  have hbudget_bound :
      2 * (K : ℝ) * S2 + S1 ≤
        theorem1GradientCostBound L Delta sigma n0 epsilon := by
    simpa [K, S1, S2] using
      budget_recursive_batch_bound L Delta sigma epsilon n0
        hL hDelta hepsilon hn0_pos hsigma_pos
  have hcost := hceil_bound.trans hbudget_bound
  simpa [K, S1, S2, q, theorem1OnlineSchedule, onlineGradientCostFromSchedule] using hcost

/-- Guarded totalized real-valued gradient-cost helper from Eq. (B.16), with
Theorem 1's source gap `Δ := f(x₀)-f*`.

This theorem talks only about the schedule printed in Eq. (3.4), interpreted
through Lean's total inverse.  It is not the paper-facing Theorem 1 cost claim
until Eq. (3.4)'s denominator source boundary is resolved.

Sources:
* `book/research/SPIDER.json#/assumptions/0`: `Δ := f(x_0)-f^*<∞ where f^*`
  is the global infimum value.
* `book/research/SPIDER.json#/algorithm_spec/parameters/1`:
  `K=⌊(4LΔn₀)ε^{-2}⌋+1`.
* `book/research/SPIDER.json#/main_theorem/statement_math`: gradient cost is
  bounded by `16LΔσ·ε^{-3}+2σ^2ε^{-2}+4σn_0^{-1}ε^{-1}`. -/
theorem theorem1_totalized_schedule_gradient_cost_bound_guarded
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (hL : 0 ≤ P.L)
    (hepsilon : 0 < epsilon)
    (_scheduleDomain : Theorem1Schedule P.L P.sigma epsilon n0) :
    let schedule := theorem1OnlineSchedule (E := VariableSpace d) P.L P.sigma epsilon n0
    onlineGradientCostFromSchedule
        (E := VariableSpace d)
        (theorem1ProblemBudget P n0 epsilon) schedule ≤
      theorem1ProblemGradientCostBound P n0 epsilon := by
  simpa [theorem1ProblemBudget, theorem1ProblemGradientCostBound] using
    theorem1_totalized_schedule_gradient_cost_bound_of_gap_guarded
      (E := VariableSpace d) P.L P.Delta P.sigma epsilon n0
      hL (P.Delta_nonneg) hepsilon _scheduleDomain

/-- Source-facing boundary for Theorem 1's printed Eq. (B.16) cost claim.

The book/PDF state the exact real schedule and cost expression, but the
parameter-domain facts needed to read the displayed quotients as partial
mathematical division are not stated as theorem hypotheses.  The totalized
helper above is therefore not exported under this paper-facing name. -/
theorem theorem1_exact_schedule_gradient_cost_bound
    [MeasurableSpace Sample]
    {d : ℕ}
    (_P : OnlineProblem Sample (VariableSpace d))
    (_epsilon n0 : ℝ)
    (_scheduleDomain : Theorem1Schedule _P.L _P.sigma _epsilon n0) :
    theorem1Eq34DenominatorSourceGap := by
  exact theorem1_eq34_denominator_source_gap

/-- Source-derived bridge for the Option I normalization domain. -/
theorem optionI_normalized_direction_domain
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {epsilonTilde : ℝ} {v : E}
    (hlarge : ¬ ‖v‖ ≤ 2 * epsilonTilde) (heps : 0 ≤ epsilonTilde) :
    ‖v‖ ≠ 0 := by
  exact fun hzero => hlarge (by
    rw [hzero]
    nlinarith [heps])

/-- Source-derived step-length bound from Eq. (B.2), not an algorithm input. -/
theorem optionII_step_bound_obligation
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {epsilon L n0 : ℝ} {x v : E}
    (heps : 0 ≤ epsilon) (hLn0 : 0 < L * n0) :
    ‖optionIIUpdate epsilon L n0 x v - x‖ ≤ epsilon * (L * n0)⁻¹ := by
  unfold optionIIUpdate
  have hadd : x - optionIIStepSize epsilon L n0 v • v - x =
      -(optionIIStepSize epsilon L n0 v • v) := by
    abel
  rw [hadd, norm_neg]
  unfold optionIIStepSize
  by_cases hv : ‖v‖ = 0
  · rw [norm_smul, hv, mul_zero]
    exact mul_nonneg heps (inv_nonneg.mpr (le_of_lt hLn0))
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have hdenpos : 0 < L * n0 * ‖v‖ := mul_pos hLn0 hvpos
    have htwodenpos : 0 < 2 * L * n0 := by
      nlinarith [hLn0]
    have heta_nonneg : 0 ≤ min (epsilon * (L * n0 * ‖v‖)⁻¹) ((2 * L * n0)⁻¹) := by
      exact le_min
        (mul_nonneg heps (inv_nonneg.mpr (le_of_lt hdenpos)))
        (inv_nonneg.mpr (le_of_lt htwodenpos))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg heta_nonneg]
    have hmin :
        min (epsilon * (L * n0 * ‖v‖)⁻¹) ((2 * L * n0)⁻¹) ≤
          epsilon * (L * n0 * ‖v‖)⁻¹ :=
      min_le_left _ _
    have hle := mul_le_mul_of_nonneg_right hmin (norm_nonneg v)
    refine hle.trans_eq ?_
    field_simp [hLn0.ne', hv]

/-- Scalar core of Eq. (B.7) for the adaptive Option II stepsize.

With `H = L n₀` and `a = ‖v‖`, the adaptive minimum in line 14 gives enough
descent in the direction norm to pay for the linear `ε‖v‖` term, up to the
printed `2ε²` slack. -/
theorem optionII_min_stepsize_norm_sq_lower
    {epsilon H a : ℝ}
    (hepsilon : 0 < epsilon) (hH : 0 < H) (ha : 0 ≤ a) :
    min (epsilon * (H * a)⁻¹) ((2 * H)⁻¹) * a ^ 2 ≥
      epsilon * a * H⁻¹ - 2 * epsilon ^ 2 * H⁻¹ := by
  by_cases ha0 : a = 0
  · subst a
    have hnonneg : 0 ≤ 2 * epsilon ^ 2 * H⁻¹ := by positivity
    simp
    linarith
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hcase : epsilon * (H * a)⁻¹ ≤ (2 * H)⁻¹
    · have hmin :
          min (epsilon * (H * a)⁻¹) ((2 * H)⁻¹) =
            epsilon * (H * a)⁻¹ := min_eq_left hcase
      rw [hmin]
      field_simp [hH.ne', hapos.ne']
      nlinarith [sq_nonneg epsilon]
    · have hle : (2 * H)⁻¹ < epsilon * (H * a)⁻¹ :=
        lt_of_not_ge hcase
      have hmin :
          min (epsilon * (H * a)⁻¹) ((2 * H)⁻¹) =
            (2 * H)⁻¹ := min_eq_right (le_of_lt hle)
      rw [hmin]
      have hcomp : a < 2 * epsilon := by
        field_simp [hH.ne', hapos.ne'] at hle
        nlinarith
      field_simp [hH.ne']
      nlinarith [sq_nonneg (a - 2 * epsilon)]

/-- Assumption 1(ii), together with the fixed-query unbiasedness interface,
gives the deterministic full-gradient Lipschitz estimate. -/
theorem onlineProblem_grad_lipschitz_of_averaged_l2
    [MeasurableSpace Sample]
    {d : ℕ} (P : OnlineProblem Sample (VariableSpace d)) (hL : 0 < P.L) :
    ∀ x y : VariableSpace d, ‖P.grad y - P.grad x‖ ≤ P.L * ‖y - x‖ := by
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  intro x y
  have hx_int : Integrable (fun s => P.sampleGrad x s) P.sampleLaw :=
    P.online_gradient_unbiased_integrable x
  have hy_int : Integrable (fun s => P.sampleGrad y s) P.sampleLaw :=
    P.online_gradient_unbiased_integrable y
  have hx_mean : (∫ s, P.sampleGrad x s ∂P.sampleLaw) = P.grad x :=
    P.online_gradient_unbiased_integral_eq x
  have hy_mean : (∫ s, P.sampleGrad y s ∂P.sampleLaw) = P.grad y :=
    P.online_gradient_unbiased_integral_eq y
  have htarget :
      P.grad y - P.grad x =
        ∫ s, P.sampleGrad y s - P.sampleGrad x s ∂P.sampleLaw := by
    calc
      P.grad y - P.grad x =
          (∫ s, P.sampleGrad y s ∂P.sampleLaw) -
            (∫ s, P.sampleGrad x s ∂P.sampleLaw) := by
            rw [hy_mean, hx_mean]
      _ = ∫ s, P.sampleGrad y s - P.sampleGrad x s ∂P.sampleLaw := by
            rw [integral_sub hy_int hx_int]
  have hnormint :
      ‖P.grad y - P.grad x‖ ≤
        ∫ s, ‖P.sampleGrad y s - P.sampleGrad x s‖ ∂P.sampleLaw := by
    rw [htarget]
    exact norm_integral_le_integral_norm _
  have hZ2 :
      Integrable (fun s => ‖P.sampleGrad y s - P.sampleGrad x s‖ ^ 2)
        P.sampleLaw := by
    simpa [SOptLib.expectationWellDefined] using
      (P.averaged_lipschitz_gradient_wellDefined y x)
  have hZ_nonneg :
      ∀ᵐ s ∂P.sampleLaw, 0 ≤ ‖P.sampleGrad y s - P.sampleGrad x s‖ :=
    Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  have hC_nonneg : 0 ≤ P.L * ‖y - x‖ :=
    mul_nonneg (le_of_lt hL) (norm_nonneg _)
  have hZ_sq_le :
      ∫ s, ‖P.sampleGrad y s - P.sampleGrad x s‖ ^ 2 ∂P.sampleLaw ≤
        (P.L * ‖y - x‖) ^ 2 := by
    have h := P.averaged_lipschitz_gradient_bound y x
    convert h using 1
    ring
  have hnorm_l1 :
      ∫ s, ‖P.sampleGrad y s - P.sampleGrad x s‖ ∂P.sampleLaw ≤
        P.L * ‖y - x‖ :=
    integral_nonneg_le_of_integral_sq_le_sq hZ2 hZ_nonneg hC_nonneg hZ_sq_le
  exact hnormint.trans hnorm_l1

/-- Pathwise Option II one-step descent, Eq. (B.8).

This is the deterministic part of Lemma 4: smoothness supplies the quadratic
upper model, the update rule supplies the affine displacement, and
`optionII_min_stepsize_norm_sq_lower` supplies the adaptive-min stepsize
algebra from Eq. (B.7). -/
theorem optionII_one_step_descent_B8_pathwise
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    {epsilon n0 : ℝ}
    (hepsilon : 0 < epsilon)
    (hL : 0 < P.L)
    (_schedule : Theorem1Schedule P.L P.sigma epsilon n0)
    (x v : VariableSpace d) :
    P.f (optionIIUpdate epsilon P.L n0 x v) ≤
      P.f x - epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) * ‖v - P.grad x‖ ^ 2 := by
  let eta : ℝ := optionIIStepSize epsilon P.L n0 v
  let y : VariableSpace d := optionIIUpdate epsilon P.L n0 x v
  have hn0_lower : 1 ≤ n0 := Theorem1Schedule.n0_lower _schedule
  have hn0_pos : 0 < n0 := lt_of_lt_of_le zero_lt_one hn0_lower
  have hH_pos : 0 < P.L * n0 := mul_pos hL hn0_pos
  have htwoH_pos : 0 < 2 * P.L * n0 := by nlinarith [hH_pos]
  have heta_nonneg : 0 ≤ eta := by
    dsimp [eta, optionIIStepSize]
    exact le_min
      (mul_nonneg (le_of_lt hepsilon)
        (inv_nonneg.mpr (mul_nonneg (le_of_lt hH_pos) (norm_nonneg v))))
      (inv_nonneg.mpr (le_of_lt htwoH_pos))
  have heta_le_twoH : eta ≤ (2 * P.L * n0)⁻¹ := by
    dsimp [eta, optionIIStepSize]
    exact min_le_right _ _
  have hdenL_pos : 0 < 2 * P.L := by nlinarith [hL]
  have hinv_le : (2 * P.L * n0)⁻¹ ≤ (2 * P.L)⁻¹ := by
    field_simp [hdenL_pos.ne', htwoH_pos.ne']
    nlinarith [hn0_lower, hL]
  have heta_le_twoL : eta ≤ (2 * P.L)⁻¹ := le_trans heta_le_twoH hinv_le
  have hLeta_le : P.L * eta ≤ (1 / 2 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left heta_le_twoL (le_of_lt hL)
    field_simp [hL.ne'] at hmul
    linarith
  have hgrad_lipschitz :
      ∀ x y : VariableSpace d, ‖P.grad y - P.grad x‖ ≤ P.L * ‖y - x‖ :=
    onlineProblem_grad_lipschitz_of_averaged_l2 P hL
  have hsmooth :
      P.f y ≤ P.f x + inner ℝ (P.grad x) (y - x) +
        (P.L / 2) * ‖y - x‖ ^ 2 := by
    have h :=
      smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
        (Set.univ : Set (VariableSpace d)) P.f P.grad P.L
        convex_univ
        (by intro z _hz; exact P.grad_hasGradientAt z)
        (by intro z _hz w _hw; simpa using hgrad_lipschitz w z)
        (Set.mem_univ x) (Set.mem_univ y)
    simpa using h
  have hy_sub : y - x = -eta • v := by
    have hadd :
        x - optionIIStepSize epsilon P.L n0 v • v - x =
          -(optionIIStepSize epsilon P.L n0 v • v) := by
      abel
    simpa [y, eta, optionIIUpdate, neg_smul] using hadd
  have hmodel :
      P.f y ≤ P.f x - eta * inner ℝ (P.grad x) v +
        (P.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) := by
    calc
      P.f y ≤ P.f x + inner ℝ (P.grad x) (y - x) +
          (P.L / 2) * ‖y - x‖ ^ 2 := hsmooth
      _ = P.f x - eta * inner ℝ (P.grad x) v +
          (P.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) := by
            rw [hy_sub]
            simp [inner_smul_right, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg heta_nonneg]
            ring
  let err : VariableSpace d := v - P.grad x
  have hinner_decomp :
      inner ℝ (P.grad x) v = ‖v‖ ^ 2 - inner ℝ err v := by
    have hg : P.grad x = v - err := by simp [err]
    rw [hg, inner_sub_left]
    simp [real_inner_self_eq_norm_sq]
  have hyoung0 :
      inner ℝ err v ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 +
        (1 / 2 : ℝ) * ‖err‖ ^ 2 := by
    have h :=
      neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq
        (show (0 : ℝ) < 1 by norm_num) err (-v)
    simpa [norm_neg, one_div] using h
  have hyoung1 :
      eta * inner ℝ err v ≤ eta / 2 * ‖v‖ ^ 2 +
        eta / 2 * ‖err‖ ^ 2 := by
    have hyoung := mul_le_mul_of_nonneg_left hyoung0 heta_nonneg
    nlinarith [hyoung]
  have hpre :
      P.f y ≤ P.f x - eta / 4 * ‖v‖ ^ 2 + eta / 2 * ‖err‖ ^ 2 := by
    have hsq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
    have hmodel_err :
        P.f y ≤ P.f x - eta * ‖v‖ ^ 2 + eta * inner ℝ err v +
          (P.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) := by
      nlinarith [hmodel, hinner_decomp]
    have hpre1 :
        P.f y ≤ P.f x - eta / 2 * ‖v‖ ^ 2 +
          (P.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) +
          eta / 2 * ‖err‖ ^ 2 := by
      nlinarith [hmodel_err, hyoung1]
    have hcoeff_quad : (P.L / 2) * eta ^ 2 ≤ eta / 4 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hLeta_le (show 0 ≤ eta / 2 by positivity)
      nlinarith [hmul]
    have hquad_scaled :
        (P.L / 2) * (eta ^ 2 * ‖v‖ ^ 2) ≤
          eta / 4 * ‖v‖ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hcoeff_quad hsq
      nlinarith [hmul]
    nlinarith [hpre1, hquad_scaled]
  have hmin_raw :=
    optionII_min_stepsize_norm_sq_lower
      (epsilon := epsilon) (H := P.L * n0) (a := ‖v‖)
      hepsilon hH_pos (norm_nonneg v)
  have hmin_eta :
      eta * ‖v‖ ^ 2 ≥
        epsilon * ‖v‖ * (P.L * n0)⁻¹ -
          2 * epsilon ^ 2 * (P.L * n0)⁻¹ := by
    simpa [eta, optionIIStepSize, mul_assoc] using hmin_raw
  have hdescent_inv :
      -eta / 4 * ‖v‖ ^ 2 ≤
        -(1 / 4) *
          (epsilon * ‖v‖ * (P.L * n0)⁻¹ -
            2 * epsilon ^ 2 * (P.L * n0)⁻¹) := by
    have hmul :=
      mul_le_mul_of_nonpos_left hmin_eta (show (-(1 / 4) : ℝ) ≤ 0 by norm_num)
    calc
      -eta / 4 * ‖v‖ ^ 2 = -(1 / 4) * (eta * ‖v‖ ^ 2) := by ring
      _ ≤
          -(1 / 4) *
            (epsilon * ‖v‖ * (P.L * n0)⁻¹ -
              2 * epsilon ^ 2 * (P.L * n0)⁻¹) := hmul
  have hdescent_eq :
      -(1 / 4) *
          (epsilon * ‖v‖ * (P.L * n0)⁻¹ -
            2 * epsilon ^ 2 * (P.L * n0)⁻¹) =
        -epsilon * ‖v‖ / (4 * P.L * n0) +
          epsilon ^ 2 / (2 * n0 * P.L) := by
    field_simp [hL.ne', hn0_pos.ne']
    ring
  have hdescent_term :
      -eta / 4 * ‖v‖ ^ 2 ≤
        -epsilon * ‖v‖ / (4 * P.L * n0) +
          epsilon ^ 2 / (2 * n0 * P.L) :=
    hdescent_inv.trans_eq hdescent_eq
  have herr_coeff :
      eta / 2 * ‖err‖ ^ 2 ≤
        (1 / (4 * P.L * n0)) * ‖err‖ ^ 2 := by
    have hcoeff0 : eta / 2 ≤ (2 * P.L * n0)⁻¹ / 2 := by
      exact div_le_div_of_nonneg_right heta_le_twoH (by norm_num : (0 : ℝ) ≤ 2)
    have hcoeff_eq :
        (2 * P.L * n0)⁻¹ / 2 = (1 / (4 * P.L * n0) : ℝ) := by
      field_simp [hL.ne', hn0_pos.ne']
      ring
    have hcoeff : eta / 2 ≤ (1 / (4 * P.L * n0) : ℝ) :=
      hcoeff0.trans_eq hcoeff_eq
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  have hsum_terms :
      -eta / 4 * ‖v‖ ^ 2 + eta / 2 * ‖err‖ ^ 2 ≤
        (-epsilon * ‖v‖ / (4 * P.L * n0) +
          epsilon ^ 2 / (2 * n0 * P.L)) +
          (1 / (4 * P.L * n0)) * ‖err‖ ^ 2 :=
    add_le_add hdescent_term herr_coeff
  have hfinal :
      P.f y ≤ P.f x - epsilon * ‖v‖ / (4 * P.L * n0) +
        epsilon ^ 2 / (2 * n0 * P.L) +
        (1 / (4 * P.L * n0)) * ‖err‖ ^ 2 := by
    calc
      P.f y
          ≤ P.f x + (-eta / 4 * ‖v‖ ^ 2 + eta / 2 * ‖err‖ ^ 2) :=
            hpre.trans_eq (by ring)
      _ ≤ P.f x + ((-epsilon * ‖v‖ / (4 * P.L * n0) +
            epsilon ^ 2 / (2 * n0 * P.L)) +
            (1 / (4 * P.L * n0)) * ‖err‖ ^ 2) :=
            add_le_add_right hsum_terms (P.f x)
      _ = P.f x - epsilon * ‖v‖ / (4 * P.L * n0) +
          epsilon ^ 2 / (2 * n0 * P.L) +
          (1 / (4 * P.L * n0)) * ‖err‖ ^ 2 := by
            ring
  simpa [y, err] using hfinal

/-- A finite Option II path moves at most the per-step radius times the number
of realized updates. -/
theorem optionII_iterate_dist_initial_le
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sampleGrad : E → Sample → E) (x0 : E)
    (S1 S2 q : ℕ) (epsilon L n0 : ℝ)
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample)
    (heps : 0 ≤ epsilon) (hLn0 : 0 < L * n0) :
    ∀ k (ω : Ω),
      ‖x0 -
        optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
          refreshSamples recursiveSamples k ω‖ ≤
        (k : ℝ) * (epsilon * (L * n0)⁻¹) := by
  let step : ℝ := epsilon * (L * n0)⁻¹
  intro k
  induction k with
  | zero =>
      intro ω
      simp [optionIIIterate]
  | succ k ih =>
      intro ω
      have hstep :
          ‖optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples (k + 1) ω -
              optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples k ω‖ ≤ step := by
        have h := optionII_step_bound_obligation
          (E := E) (epsilon := epsilon) (L := L) (n0 := n0)
          (x := optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
            refreshSamples recursiveSamples k ω)
          (v := optionIIEstimator sampleGrad x0 S1 S2 q epsilon L n0
            refreshSamples recursiveSamples k ω)
          heps hLn0
        simpa [step] using h
      calc
        ‖x0 -
            optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
              refreshSamples recursiveSamples (k + 1) ω‖
            =
            ‖(x0 -
                optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                  refreshSamples recursiveSamples k ω) +
              (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                  refreshSamples recursiveSamples k ω -
                optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                  refreshSamples recursiveSamples (k + 1) ω)‖ := by
              congr 1
              abel
        _ ≤
            ‖x0 -
              optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples k ω‖ +
            ‖optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples k ω -
              optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples (k + 1) ω‖ :=
            norm_add_le _ _
        _ ≤
            ‖x0 -
              optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples k ω‖ +
            ‖optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples (k + 1) ω -
              optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                refreshSamples recursiveSamples k ω‖ := by
            exact add_le_add le_rfl
              (le_of_eq (norm_sub_rev
                (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                  refreshSamples recursiveSamples k ω)
                (optionIIIterate sampleGrad x0 S1 S2 q epsilon L n0
                  refreshSamples recursiveSamples (k + 1) ω)))
        _ ≤ (k : ℝ) * step + step := by
            exact add_le_add (ih ω) hstep
        _ = ((k + 1 : ℕ) : ℝ) * step := by
            rw [Nat.cast_add, Nat.cast_one]
            ring

/-- A Lipschitz vector field is integrable in norm along an a.e.-measurable
process that stays in a deterministic ball around a base point. -/
theorem integrable_norm_lipschitz_field_of_ae_bound
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (base : E) (grad : E → E) (L D : ℝ) {z : Ω → E}
    (hz : AEStronglyMeasurable z μ)
    (hgrad_lipschitz : ∀ x y : E, ‖grad y - grad x‖ ≤ L * ‖y - x‖)
    (hL_nonneg : 0 ≤ L)
    (hdist : ∀ᵐ ω ∂μ, ‖z ω - base‖ ≤ D) :
    Integrable (fun ω => ‖grad (z ω)‖) μ := by
  have hgrad_lipWith : LipschitzWith (Real.toNNReal L) grad := by
    refine lipschitzWith_of_norm_sub_le_mul grad L ?_
    intro x y
    simpa [dist_eq_norm] using hgrad_lipschitz y x
  have hscalar_aesm : AEStronglyMeasurable (fun ω => ‖grad (z ω)‖) μ :=
    (hgrad_lipWith.continuous.comp_aestronglyMeasurable hz).norm
  let B : ℝ := ‖grad base‖ + L * D
  have hbounded : ∀ᵐ ω ∂μ, ‖(‖grad (z ω)‖ : ℝ)‖ ≤ B := by
    filter_upwards [hdist] with ω hdiam
    have hlip : ‖grad (z ω) - grad base‖ ≤ L * ‖z ω - base‖ :=
      hgrad_lipschitz base (z ω)
    have hdist_grad : L * ‖z ω - base‖ ≤ L * D :=
      mul_le_mul_of_nonneg_left hdiam hL_nonneg
    have hbase : ‖grad (z ω)‖ ≤ ‖grad base‖ + ‖grad (z ω) - grad base‖ := by
      calc
        ‖grad (z ω)‖ = ‖grad base + (grad (z ω) - grad base)‖ := by
            congr 1
            abel
        _ ≤ ‖grad base‖ + ‖grad (z ω) - grad base‖ :=
            norm_add_le _ _
    have hnorm : ‖grad (z ω)‖ ≤ B := by
      dsimp [B]
      linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (grad (z ω)))] using hnorm
  exact Integrable.of_bound hscalar_aesm B hbounded

/-- Selected-output well-definedness reduces to the finite collection of
fiber integrability obligations used in the Eq. (B.15) expansion. -/
theorem selected_output_wellDefined_of_fiber_integrable
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) [SFinite mu] (grad : E → E) (iterate : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K)
    (hint :
      ∀ R : {k : ℕ // k ∈ optionIIOutputWindow K},
        Integrable (fun ω => ‖grad (iterate R.1 ω)‖) mu) :
    selectedOutputGradientNormExpectationWellDefined mu grad iterate K hK := by
  classical
  rw [selectedOutputGradientNormExpectation_wellDefined_iff]
  exact
    integrable_finite_index_first_prod_of_fiber_integrable
      ((optionIIUniformOutputPMF K hK).toMeasure) mu
      (fun R ω => ‖grad (iterate R.1 ω)‖) hint

/-- Eq. (B.15) finite-average algebra: combine Lemma 5's per-time
gradient-estimator conversion with the B.14 estimator-average bound. -/
theorem uniform_average_gradient_bound_of_estimator_average
    [MeasurableSpace Ω] [Norm E]
    (mu : Measure Ω) (grad : E → E) (iterate estimator : ℕ → Ω → E)
    (K : ℕ) (hK : 0 < K) (epsilon : ℝ)
    (hconvert :
      ∀ k ∈ Finset.range K,
        (∫ ω, ‖grad (iterate k ω)‖ ∂mu) ≤
          (∫ ω, ‖estimator k ω‖ ∂mu) + epsilon)
    (hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ ω, ‖estimator k ω‖ ∂mu) ≤
        4 * epsilon) :
    uniformOutputGradientNormAverage mu grad iterate K ≤ 5 * epsilon := by
  classical
  have hsum :
      Finset.sum (Finset.range K)
          (fun k => ∫ ω, ‖grad (iterate k ω)‖ ∂mu) ≤
        Finset.sum (Finset.range K)
          (fun k => (∫ ω, ‖estimator k ω‖ ∂mu) + epsilon) := by
    exact Finset.sum_le_sum hconvert
  have hscale_nonneg : 0 ≤ (K : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg K)
  have hscaled :=
    mul_le_mul_of_nonneg_left hsum hscale_nonneg
  have hK_ne : (K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hK)
  have hgrad_le_est_plus :
      uniformOutputGradientNormAverage mu grad iterate K ≤
        (K : ℝ)⁻¹ *
            Finset.sum (Finset.range K)
              (fun k => ∫ ω, ‖estimator k ω‖ ∂mu) +
          epsilon := by
    unfold uniformOutputGradientNormAverage
    calc
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ ω, ‖grad (iterate k ω)‖ ∂mu)
          ≤
        (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => (∫ ω, ‖estimator k ω‖ ∂mu) + epsilon) := hscaled
      _ =
        (K : ℝ)⁻¹ *
            Finset.sum (Finset.range K)
              (fun k => ∫ ω, ‖estimator k ω‖ ∂mu) +
          epsilon := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
            field_simp [hK_ne]
            ring
  linarith

/-- Lemma 5's endpoint bookkeeping: a squared estimator-error bound gives the
printed `E‖∇f(xᵏ)‖ ≤ E‖vᵏ‖ + ε` inequality once the true-gradient fiber is
integrable. -/
theorem integral_target_norm_le_estimator_norm_add_of_error_secondMoment
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    {target estimator err : Ω → E} {epsilon : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon)
    (htarget_int : Integrable (fun ω => ‖target ω‖) mu)
    (hestimator_aesm : AEStronglyMeasurable estimator mu)
    (herr_def : ∀ ω, err ω = estimator ω - target ω)
    (hmse :
      Integrable (fun ω => ‖err ω‖ ^ 2) mu ∧
        ∫ ω, ‖err ω‖ ^ 2 ∂mu ≤ epsilon ^ 2) :
    ∫ ω, ‖target ω‖ ∂mu ≤ ∫ ω, ‖estimator ω‖ ∂mu + epsilon := by
  have herr_nonneg : ∀ᵐ ω ∂mu, 0 ≤ ‖err ω‖ :=
    Filter.Eventually.of_forall (fun ω => norm_nonneg (err ω))
  have herr_norm_int : Integrable (fun ω => ‖err ω‖) mu := by
    exact
      (integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
        (C := epsilon ^ 2) hmse.1 herr_nonneg hmse.2).1
  have hest_norm_int : Integrable (fun ω => ‖estimator ω‖) mu := by
    refine Integrable.mono'
      (htarget_int.add herr_norm_int) hestimator_aesm.norm ?_
    filter_upwards with ω
    have hpoint : ‖estimator ω‖ ≤ ‖target ω‖ + ‖err ω‖ := by
      have hsum : target ω + err ω = estimator ω := by
        rw [herr_def ω]
        abel
      calc
        ‖estimator ω‖ = ‖target ω + err ω‖ := by rw [hsum]
        _ ≤ ‖target ω‖ + ‖err ω‖ := norm_add_le _ _
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (estimator ω))] using hpoint
  have herr_l1 : ∫ ω, ‖err ω‖ ∂mu ≤ epsilon :=
    integral_nonneg_le_of_integral_sq_le_sq
      hmse.1 herr_nonneg hepsilon_nonneg hmse.2
  have htri_int : Integrable (fun ω => ‖estimator ω‖ + ‖err ω‖) mu :=
    hest_norm_int.add herr_norm_int
  have htri :
      ∫ ω, ‖target ω‖ ∂mu ≤
        ∫ ω, ‖estimator ω‖ + ‖err ω‖ ∂mu := by
    refine integral_mono htarget_int htri_int ?_
    intro ω
    have hpoint : ‖target ω‖ ≤ ‖estimator ω‖ + ‖err ω‖ := by
      have hsub : estimator ω - err ω = target ω := by
        rw [herr_def ω]
        abel
      calc
        ‖target ω‖ = ‖estimator ω - err ω‖ := by rw [hsub]
        _ ≤ ‖estimator ω‖ + ‖err ω‖ := norm_sub_le _ _
    exact hpoint
  calc
    ∫ ω, ‖target ω‖ ∂mu
        ≤ ∫ ω, ‖estimator ω‖ + ‖err ω‖ ∂mu := htri
    _ = (∫ ω, ‖estimator ω‖ ∂mu) + ∫ ω, ‖err ω‖ ∂mu := by
          rw [integral_add hest_norm_int herr_norm_int]
    _ ≤ (∫ ω, ‖estimator ω‖ ∂mu) + epsilon :=
          add_le_add le_rfl herr_l1

/-- Internal stationarity claim for the rounded generated Option II run.

This packages the old realized-run convergence target as a proposition rather
than exporting it as the paper theorem.  It still mentions the `Nat.ceil`
sample-array realization, so any proof of it is implementation-level unless a
separate bridge relates that realization back to the paper's real schedule. -/
noncomputable def theorem1RealizedOptionIIStationarityClaim
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ) : Prop :=
    let mu := theorem1RealizedOnlineRunLaw P.sampleLaw P.sigma epsilon n0
    let iterate :=
      theorem1RealizedOnlineOptionIIIterate P.sampleGrad P.x0 P.sigma epsilon P.L n0
    selectedOutputGradientNormExpectationWellDefined
        mu
        P.grad
        iterate
        (theorem1Budget P.L P.Delta n0 epsilon)
        (theorem1Budget_pos P.L P.Delta n0 epsilon) ∧
    selectedOutputGradientNormExpectation
        mu
        P.grad
        iterate
        (theorem1Budget P.L P.Delta n0 epsilon)
        (theorem1Budget_pos P.L P.Delta n0 epsilon) ≤
      5 * epsilon

/-- Implementation-level admissibility for the rounded generated run.

These are not source hypotheses for Theorem 1.  They isolate the Lean-specific
facts needed by finite arrays, modulo, and totalized quotient arithmetic. -/
def theorem1RealizedScheduleAdmissible
    (L sigma epsilon n0 : ℝ) : Prop :=
  epsilon ≠ 0 ∧
    L * n0 ≠ 0 ∧
    2 * L * n0 ≠ 0 ∧
    0 < theorem1RefreshBatchCount sigma epsilon ∧
    0 < theorem1RecursiveBatchCount sigma epsilon n0 ∧
    0 < theorem1EpochCount sigma epsilon n0

/-- The old unguarded stationarity route admitted negative `epsilon` at the
scalar schedule/realization layer. -/
theorem theorem1_realized_optionII_legacy_negative_epsilon_domain_example :
    Theorem1Schedule (1 : ℝ) (-1) (-1) 1 ∧
      theorem1RealizedScheduleAdmissible (1 : ℝ) (-1) (-1) 1 := by
  norm_num [Theorem1Schedule, theorem1RealizedScheduleAdmissible,
    theorem1RefreshBatchCount, theorem1RecursiveBatchCount, theorem1EpochCount,
    onlineRefreshBatchSize, onlineRecursiveBatchSize, onlineEpochLength]

/-- Negative `epsilon` is incompatible with the realized stationarity claim:
the left side is an expectation of a norm, hence nonnegative, while the claimed
upper bound `5 * epsilon` is negative. -/
theorem theorem1RealizedOptionIIStationarityClaim_false_of_epsilon_negative
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (hclaim : theorem1RealizedOptionIIStationarityClaim P epsilon n0)
    (hepsilon_neg : epsilon < 0) :
    False := by
  let mu := theorem1RealizedOnlineRunLaw P.sampleLaw P.sigma epsilon n0
  let iterate :=
    theorem1RealizedOnlineOptionIIIterate P.sampleGrad P.x0 P.sigma epsilon P.L n0
  have hnonneg :
      0 ≤
        selectedOutputGradientNormExpectation
          mu
          P.grad
          iterate
          (theorem1Budget P.L P.Delta n0 epsilon)
          (theorem1Budget_pos P.L P.Delta n0 epsilon) :=
    selectedOutputGradientNormExpectation_nonneg
      mu P.grad iterate
      (theorem1Budget P.L P.Delta n0 epsilon)
      (theorem1Budget_pos P.L P.Delta n0 epsilon)
  have hle :
      selectedOutputGradientNormExpectation
          mu
          P.grad
          iterate
          (theorem1Budget P.L P.Delta n0 epsilon)
          (theorem1Budget_pos P.L P.Delta n0 epsilon) ≤
        5 * epsilon := by
    simpa [theorem1RealizedOptionIIStationarityClaim, mu, iterate] using hclaim.2
  nlinarith

theorem theorem1StationarityLegacy_objectiveExpectation_zero :
    SOptLib.objectiveExpectation (Measure.dirac ())
        (fun (_ : VariableSpace 1) (_ : Unit) => (0 : ℝ)) id =
      fun _ => 0 := by
  funext x
  simp [SOptLib.objectiveExpectation, SOptLib.objectiveKernel]

theorem theorem1StationarityLegacy_sampleObjectiveGradient_zero
    (x : VariableSpace 1) (s : Unit) :
    sampleObjectiveGradient (fun (_ : VariableSpace 1) (_ : Unit) => (0 : ℝ)) x s = 0 := by
  simp [sampleObjectiveGradient, gradient_fun_const]

theorem theorem1StationarityLegacy_objectiveGradient_zero
    (x : VariableSpace 1) :
    objectiveGradient (Measure.dirac ())
        (fun (_ : VariableSpace 1) (_ : Unit) => (0 : ℝ)) x = 0 := by
  simp [objectiveGradient, onlineObjective, theorem1StationarityLegacy_objectiveExpectation_zero,
    gradient_fun_const]

/-- A concrete zero-objective online problem used only to refute the old
unguarded realized-stationarity helper boundary.

The model satisfies the source setup trivially, but its scalar constants are
`L = 1` and `sigma = -1`, so the old helper's schedule domain admitted
`epsilon = -1`. -/
noncomputable def theorem1StationarityLegacyCounterexampleProblem :
    OnlineProblem Unit (VariableSpace 1) where
  sampleObjective := fun _ _ => 0
  sampleLaw := Measure.dirac ()
  sampleLaw_isProbability := by infer_instance
  objective_wellDefined := by
    intro x
    unfold onlineObjectiveWellDefinedAt SOptLib.objectiveWellDefined SOptLib.objectiveKernel
    exact integrable_const (c := (0 : ℝ))
  x0 := 0
  L := 1
  sigma := -1
  objective_bddBelow := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp [onlineObjective, SOptLib.objectiveExpectation, SOptLib.objectiveKernel]
  sampleObjective_hasGradientAt := by
    intro x s
    rw [theorem1StationarityLegacy_sampleObjectiveGradient_zero x s]
    exact hasGradientAt_const (x := x) (c := (0 : ℝ))
  sampleObjectiveGradient_joint_measurable := by
    simp [theorem1StationarityLegacy_sampleObjectiveGradient_zero]
  objective_hasGradientAt := by
    intro x
    rw [theorem1StationarityLegacy_objectiveGradient_zero x]
    unfold onlineObjective
    rw [theorem1StationarityLegacy_objectiveExpectation_zero]
    exact hasGradientAt_const (x := x) (c := (0 : ℝ))
  online_gradient_unbiased := by
    intro x
    refine SOptLib.expectationEq_of_integrable_integral_eq ?_ ?_
    · simp [theorem1StationarityLegacy_sampleObjectiveGradient_zero]
    · simp [theorem1StationarityLegacy_sampleObjectiveGradient_zero,
        theorem1StationarityLegacy_objectiveGradient_zero]
  averaged_lipschitz_gradient := by
    intro x y
    constructor
    · unfold SOptLib.expectationWellDefined
      simp [theorem1StationarityLegacy_sampleObjectiveGradient_zero]
    · have hnonneg : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg _
      simp [theorem1StationarityLegacy_sampleObjectiveGradient_zero, hnonneg]
  online_gradient_variance := by
    intro x
    constructor
    · unfold SOptLib.expectationWellDefined
      simp [theorem1StationarityLegacy_sampleObjectiveGradient_zero,
        theorem1StationarityLegacy_objectiveGradient_zero]
    · norm_num [theorem1StationarityLegacy_sampleObjectiveGradient_zero,
        theorem1StationarityLegacy_objectiveGradient_zero]

/-- The old unguarded stationarity theorem head that Phase 2b retired.

This proposition is not a replacement theorem.  It records the removed helper
boundary exactly so that the negative-`epsilon` counterexample can be checked
inside Lean. -/
def theorem1_realized_optionII_expected_stationarity_internal_legacy_statement : Prop :=
  ∀ {Sample : Type} [MeasurableSpace Sample] {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d)) (epsilon n0 : ℝ),
    Theorem1Schedule P.L P.sigma epsilon n0 →
    theorem1RealizedScheduleAdmissible P.L P.sigma epsilon n0 →
    theorem1RealizedOptionIIStationarityClaim P epsilon n0

theorem theorem1StationarityLegacyCounterexample_schedule :
    Theorem1Schedule
      theorem1StationarityLegacyCounterexampleProblem.L
      theorem1StationarityLegacyCounterexampleProblem.sigma
      (-1 : ℝ) (1 : ℝ) := by
  norm_num [theorem1StationarityLegacyCounterexampleProblem, Theorem1Schedule]

theorem theorem1StationarityLegacyCounterexample_admissible :
    theorem1RealizedScheduleAdmissible
      theorem1StationarityLegacyCounterexampleProblem.L
      theorem1StationarityLegacyCounterexampleProblem.sigma
      (-1 : ℝ) (1 : ℝ) := by
  norm_num [theorem1StationarityLegacyCounterexampleProblem,
    theorem1RealizedScheduleAdmissible, theorem1RefreshBatchCount,
    theorem1RecursiveBatchCount, theorem1EpochCount, onlineRefreshBatchSize,
    onlineRecursiveBatchSize, onlineEpochLength]

/-- Formal retirement evidence for the old unguarded realized-stationarity
helper: applying it to the concrete zero-objective problem above with
`epsilon = -1` produces the impossible bound
`E ‖∇f(x_tilde)‖ ≤ -5`. -/
theorem theorem1_realized_optionII_expected_stationarity_internal_legacy_false :
    ¬ theorem1_realized_optionII_expected_stationarity_internal_legacy_statement := by
  intro hlegacy
  have hclaim :=
    hlegacy
      (d := 1)
      (P := theorem1StationarityLegacyCounterexampleProblem)
      (-1 : ℝ)
      (1 : ℝ)
      theorem1StationarityLegacyCounterexample_schedule
      theorem1StationarityLegacyCounterexample_admissible
  exact theorem1RealizedOptionIIStationarityClaim_false_of_epsilon_negative
    theorem1StationarityLegacyCounterexampleProblem
    (-1 : ℝ)
    (1 : ℝ)
    hclaim
    (by norm_num)

/-- Previous recursive residuals are orthogonal to one fresh centered recursive
gradient-difference coordinate.

This is the product-run martingale cancellation used in Lemma 2: the fresh
sample at time `t + 1` is independent of the query consisting of the two
iterates and the previous centered residual, while each fixed paired-gradient
difference residual is centered under the sample law. -/
theorem optionII_recursive_prev_residual_centered_coordinate_cross_zero
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (S1 S2 : ℕ)
    (mu : Measure (OnlineRunSamplePath S1 S2 Sample))
    (iterate estimator :
      ℕ → OnlineRunSamplePath S1 S2 Sample → VariableSpace d)
    (recursiveSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample)
    [IsFiniteMeasure mu]
    (hrecursiveSamples_measurable :
      ∀ t i, Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
        recursiveSamples t ω i))
    (hprocess_measurable :
      ∀ t, Measurable (iterate t) ∧ Measurable (estimator t))
    (hgrad_measurable : Measurable P.grad)
    (hrecursive_freshness :
      ∀ t,
        (∀ i : Fin S2,
          ProbabilityTheory.IndepFun
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ((iterate t ω, iterate (t + 1) ω), estimator t ω))
            (fun ω => recursiveSamples (t + 1) ω i) mu) ∧
        (∀ i j : Fin S2, i ≠ j →
          ProbabilityTheory.IndepFun
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              (((iterate t ω, iterate (t + 1) ω), estimator t ω),
                recursiveSamples (t + 1) ω j))
            (fun ω => recursiveSamples (t + 1) ω i) mu))
    (hrecursive_sample_law :
      ∀ t (i : Fin S2),
        Measure.map
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              recursiveSamples (t + 1) ω i) mu =
          P.sampleLaw)
    (hdiff_fixed_zero :
      ∀ x y : VariableSpace d,
        ∫ s, (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
            ∂P.sampleLaw = 0) :
    ∀ (t : ℕ) (i : Fin S2),
      MeasureTheory.integral mu
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            inner ℝ
              (estimator t ω - P.grad (iterate t ω))
              ((P.sampleGrad (iterate (t + 1) ω)
                    (recursiveSamples (t + 1) ω i) -
                  P.sampleGrad (iterate t ω)
                    (recursiveSamples (t + 1) ω i)) -
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))) =
        0 := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  intro t i
  have hquery_fresh :
      ProbabilityTheory.IndepFun
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          ((iterate (t + 1) ω, iterate t ω),
            estimator t ω - P.grad (iterate t ω)))
        (fun ω => recursiveSamples (t + 1) ω i) mu := by
    have hfresh := (hrecursive_freshness t).1 i
    have hproj :
        Measurable
          (fun q : (VariableSpace d × VariableSpace d) × VariableSpace d =>
            ((q.1.2, q.1.1), q.2 - P.grad q.1.1)) :=
      ((measurable_snd.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.sub
          (hgrad_measurable.comp (measurable_fst.comp measurable_fst)))
    simpa [Function.comp_def] using hfresh.comp hproj measurable_id
  have hquery_meas :
      Measurable
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          ((iterate (t + 1) ω, iterate t ω),
            estimator t ω - P.grad (iterate t ω))) :=
    ((hprocess_measurable (t + 1)).1.prodMk (hprocess_measurable t).1).prodMk
      ((hprocess_measurable t).2.sub
        (hgrad_measurable.comp (hprocess_measurable t).1))
  have hres_meas :
      Measurable
        (fun p : ((VariableSpace d × VariableSpace d) × VariableSpace d) × Sample =>
          (P.sampleGrad p.1.1.1 p.2 - P.sampleGrad p.1.1.2 p.2) -
            (P.grad p.1.1.1 - P.grad p.1.1.2)) := by
    exact
      ((P.sampleGrad_joint_measurable.comp
        ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_snd)).sub
      (P.sampleGrad_joint_measurable.comp
        ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
          measurable_snd))).sub
      ((hgrad_measurable.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sub
        (hgrad_measurable.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
  have hfixed_int :
      ∀ q : (VariableSpace d × VariableSpace d) × VariableSpace d,
        Integrable
          (fun s : Sample =>
            (P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s) -
              (P.grad q.1.1 - P.grad q.1.2)) P.sampleLaw := by
    intro q
    have hdiff_meas :
        Measurable
          (fun s : Sample => P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s) :=
      (P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => q.1.1).prodMk
          measurable_id)).sub
      (P.sampleGrad_joint_measurable.comp
        ((measurable_const : Measurable fun _ : Sample => q.1.2).prodMk
          measurable_id))
    have hdiff_sq :
        Integrable
          (fun s : Sample => ‖P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s‖ ^ 2)
            P.sampleLaw := by
      simpa [SOptLib.expectationWellDefined] using
        P.averaged_lipschitz_gradient_wellDefined q.1.1 q.1.2
    have hdiff_int :
        Integrable (fun s : Sample => P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s)
          P.sampleLaw :=
      integrable_of_integrable_norm_sq
        hdiff_meas.aestronglyMeasurable hdiff_sq
    exact hdiff_int.sub (integrable_const (P.grad q.1.1 - P.grad q.1.2))
  have hzero :=
    randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      (P := mu) (ν := P.sampleLaw)
      (query := fun ω : OnlineRunSamplePath S1 S2 Sample =>
        ((iterate (t + 1) ω, iterate t ω),
          estimator t ω - P.grad (iterate t ω)))
      (sample := fun ω => recursiveSamples (t + 1) ω i)
      (residual := fun q s =>
        (P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s) -
          (P.grad q.1.1 - P.grad q.1.2))
      (d := fun q : (VariableSpace d × VariableSpace d) × VariableSpace d => q.2)
      hres_meas measurable_snd hquery_meas
      (hrecursiveSamples_measurable (t + 1) i)
      hquery_fresh
      (hrecursive_sample_law t i)
      hfixed_int
      (fun q => hdiff_fixed_zero q.1.1 q.1.2)
  simpa using hzero

/-- Coordinate-wise previous-residual cancellation lifts to the scaled recursive
mini-batch average. -/
theorem optionII_recursive_prev_residual_centered_minibatch_cross_zero
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (S1 S2 : ℕ)
    (mu : Measure (OnlineRunSamplePath S1 S2 Sample))
    (iterate estimator :
      ℕ → OnlineRunSamplePath S1 S2 Sample → VariableSpace d)
    (recursiveSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample)
    (hrecursiveSamples_measurable :
      ∀ t i, Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
        recursiveSamples t ω i))
    (hprocess_measurable :
      ∀ t, Measurable (iterate t) ∧ Measurable (estimator t))
    (hgrad_measurable : Measurable P.grad)
    (hcentered_difference_kernel_measurable :
      Measurable
        (fun p : (VariableSpace d × VariableSpace d) × Sample =>
          (P.sampleGrad p.1.1 p.2 - P.sampleGrad p.1.2 p.2) -
            (P.grad p.1.1 - P.grad p.1.2)))
    (hrecursive_centered_diag :
      ∀ (t : ℕ) (i : Fin S2),
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖(P.sampleGrad (iterate (t + 1) ω)
                    (recursiveSamples (t + 1) ω i) -
                  P.sampleGrad (iterate t ω)
                    (recursiveSamples (t + 1) ω i)) -
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))‖ ^ 2) mu ∧
          ∫ ω,
              ‖(P.sampleGrad (iterate (t + 1) ω)
                    (recursiveSamples (t + 1) ω i) -
                  P.sampleGrad (iterate t ω)
                    (recursiveSamples (t + 1) ω i)) -
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))‖ ^ 2 ∂mu ≤
            P.L ^ 2 *
              ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu)
    (hcoordinate_cross_zero :
      ∀ (t : ℕ) (i : Fin S2),
        MeasureTheory.integral mu
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              inner ℝ
                (estimator t ω - P.grad (iterate t ω))
                ((P.sampleGrad (iterate (t + 1) ω)
                      (recursiveSamples (t + 1) ω i) -
                    P.sampleGrad (iterate t ω)
                      (recursiveSamples (t + 1) ω i)) -
                  (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))) =
          0) :
    ∀ (t : ℕ),
      Integrable
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2) mu →
      MeasureTheory.integral mu
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            inner ℝ
              (estimator t ω - P.grad (iterate t ω))
              ((S2 : ℝ)⁻¹ •
                Finset.sum (Finset.univ : Finset (Fin S2))
                  (fun i =>
                    (P.sampleGrad (iterate (t + 1) ω)
                        (recursiveSamples (t + 1) ω i) -
                      P.sampleGrad (iterate t ω)
                        (recursiveSamples (t + 1) ω i)) -
                    (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))))) =
        0 := by
  classical
  intro t hprev_sq
  let deltaPrev : OnlineRunSamplePath S1 S2 Sample → VariableSpace d :=
    fun ω => estimator t ω - P.grad (iterate t ω)
  let eps : Fin S2 → OnlineRunSamplePath S1 S2 Sample → VariableSpace d :=
    fun i ω =>
      (P.sampleGrad (iterate (t + 1) ω) (recursiveSamples (t + 1) ω i) -
        P.sampleGrad (iterate t ω) (recursiveSamples (t + 1) ω i)) -
      (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))
  have hdelta_meas : AEStronglyMeasurable deltaPrev mu := by
    dsimp [deltaPrev]
    exact ((hprocess_measurable t).2.sub
      (hgrad_measurable.comp (hprocess_measurable t).1)).aestronglyMeasurable
  have heps_meas :
      ∀ i ∈ (Finset.univ : Finset (Fin S2)), AEStronglyMeasurable (eps i) mu := by
    intro i _hi
    dsimp [eps]
    exact (hcentered_difference_kernel_measurable.comp
      (((hprocess_measurable (t + 1)).1.prodMk (hprocess_measurable t).1).prodMk
        (hrecursiveSamples_measurable (t + 1) i))).aestronglyMeasurable
  have heps_sq :
      ∀ i ∈ (Finset.univ : Finset (Fin S2)),
        Integrable (fun ω : OnlineRunSamplePath S1 S2 Sample => ‖eps i ω‖ ^ 2) mu := by
    intro i _hi
    dsimp [eps]
    exact (hrecursive_centered_diag t i).1
  have hcross_zero :
      ∀ i ∈ (Finset.univ : Finset (Fin S2)),
        MeasureTheory.integral mu (fun ω => inner ℝ (deltaPrev ω) (eps i ω)) = 0 := by
    intro i _hi
    dsimp [deltaPrev, eps]
    exact hcoordinate_cross_zero t i
  simpa [deltaPrev, eps] using
    (pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero
      (P := mu) (I := (Finset.univ : Finset (Fin S2))) (m := S2)
      (d := deltaPrev) (eps := eps)
      hdelta_meas heps_meas hprev_sq heps_sq hcross_zero)

/-- Non-refresh recursive estimator residuals satisfy the one-step second-moment
recurrence once the centered mini-batch martingale cancellations are available. -/
theorem optionII_recursive_residual_second_moment_step
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (S1 S2 q : ℕ)
    (mu : Measure (OnlineRunSamplePath S1 S2 Sample))
    (iterate estimator :
      ℕ → OnlineRunSamplePath S1 S2 Sample → VariableSpace d)
    (recursiveSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample)
    (hS2_pos : 0 < S2)
    (hrecursiveSamples_measurable :
      ∀ t i, Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
        recursiveSamples t ω i))
    (hprocess_measurable :
      ∀ t, Measurable (iterate t) ∧ Measurable (estimator t))
    (hgrad_measurable : Measurable P.grad)
    (hcentered_difference_kernel_measurable :
      Measurable
        (fun p : (VariableSpace d × VariableSpace d) × Sample =>
          (P.sampleGrad p.1.1 p.2 - P.sampleGrad p.1.2 p.2) -
            (P.grad p.1.1 - P.grad p.1.2)))
    (hrecursive_centered_residual :
      ∀ t, (t + 1) % q ≠ 0 →
        Filter.EventuallyEq (ae mu)
          (fun ω => estimator (t + 1) ω - P.grad (iterate (t + 1) ω))
          (fun ω =>
            (estimator t ω - P.grad (iterate t ω)) +
              (S2 : ℝ)⁻¹ •
                Finset.sum (Finset.univ : Finset (Fin S2))
                  (fun i =>
                    (P.sampleGrad (iterate (t + 1) ω) (recursiveSamples (t + 1) ω i) -
                      P.sampleGrad (iterate t ω) (recursiveSamples (t + 1) ω i)) -
                    (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))))
    (hrecursive_centered_diag :
      ∀ (t : ℕ) (i : Fin S2),
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖(P.sampleGrad (iterate (t + 1) ω)
                    (recursiveSamples (t + 1) ω i) -
                  P.sampleGrad (iterate t ω)
                    (recursiveSamples (t + 1) ω i)) -
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))‖ ^ 2) mu ∧
          ∫ ω,
              ‖(P.sampleGrad (iterate (t + 1) ω)
                    (recursiveSamples (t + 1) ω i) -
                  P.sampleGrad (iterate t ω)
                    (recursiveSamples (t + 1) ω i)) -
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))‖ ^ 2 ∂mu ≤
            P.L ^ 2 *
              ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu)
    (hrecursive_offdiag_cross_zero :
      ∀ (t : ℕ) (i j : Fin S2), i ≠ j →
        MeasureTheory.integral mu
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              inner ℝ
                ((P.sampleGrad (iterate (t + 1) ω)
                      (recursiveSamples (t + 1) ω i) -
                    P.sampleGrad (iterate t ω)
                      (recursiveSamples (t + 1) ω i)) -
                  (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))
                ((P.sampleGrad (iterate (t + 1) ω)
                      (recursiveSamples (t + 1) ω j) -
                    P.sampleGrad (iterate t ω)
                      (recursiveSamples (t + 1) ω j)) -
                  (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))) =
          0)
    (hprev_increment_cross :
      ∀ (t : ℕ),
        Integrable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2) mu →
        MeasureTheory.integral mu
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              inner ℝ
                (estimator t ω - P.grad (iterate t ω))
                ((S2 : ℝ)⁻¹ •
                  Finset.sum (Finset.univ : Finset (Fin S2))
                    (fun i =>
                      (P.sampleGrad (iterate (t + 1) ω)
                          (recursiveSamples (t + 1) ω i) -
                        P.sampleGrad (iterate t ω)
                          (recursiveSamples (t + 1) ω i)) -
                      (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))))) =
          0) :
    ∀ t, (t + 1) % q ≠ 0 →
      Integrable
        (fun ω : OnlineRunSamplePath S1 S2 Sample =>
          ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2) mu →
      Integrable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ‖estimator (t + 1) ω - P.grad (iterate (t + 1) ω)‖ ^ 2) mu ∧
        ∫ ω, ‖estimator (t + 1) ω - P.grad (iterate (t + 1) ω)‖ ^ 2 ∂mu ≤
          ∫ ω, ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2 ∂mu +
            (P.L ^ 2 / (S2 : ℝ)) *
              ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu := by
  classical
  intro t hnot hprev_sq
  let deltaPrev : OnlineRunSamplePath S1 S2 Sample → VariableSpace d :=
    fun ω => estimator t ω - P.grad (iterate t ω)
  let deltaNext : OnlineRunSamplePath S1 S2 Sample → VariableSpace d :=
    fun ω => estimator (t + 1) ω - P.grad (iterate (t + 1) ω)
  let eps : Fin S2 → OnlineRunSamplePath S1 S2 Sample → VariableSpace d :=
    fun i ω =>
      (P.sampleGrad (iterate (t + 1) ω) (recursiveSamples (t + 1) ω i) -
        P.sampleGrad (iterate t ω) (recursiveSamples (t + 1) ω i)) -
      (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))
  let inc : OnlineRunSamplePath S1 S2 Sample → VariableSpace d :=
    fun ω => (S2 : ℝ)⁻¹ •
      Finset.sum (Finset.univ : Finset (Fin S2)) (fun i => eps i ω)
  have hprev_meas : AEStronglyMeasurable deltaPrev mu := by
    dsimp [deltaPrev]
    exact ((hprocess_measurable t).2.sub
      (hgrad_measurable.comp (hprocess_measurable t).1)).aestronglyMeasurable
  have heps_meas :
      ∀ i ∈ (Finset.univ : Finset (Fin S2)), AEStronglyMeasurable (eps i) mu := by
    intro i _hi
    dsimp [eps]
    exact (hcentered_difference_kernel_measurable.comp
      (((hprocess_measurable (t + 1)).1.prodMk (hprocess_measurable t).1).prodMk
        (hrecursiveSamples_measurable (t + 1) i))).aestronglyMeasurable
  have heps_diag :
      ∀ i ∈ (Finset.univ : Finset (Fin S2)),
        Integrable (fun ω : OnlineRunSamplePath S1 S2 Sample => ‖eps i ω‖ ^ 2) mu ∧
          ∫ ω, ‖eps i ω‖ ^ 2 ∂mu ≤
            P.L ^ 2 * ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu := by
    intro i _hi
    dsimp [eps]
    exact hrecursive_centered_diag t i
  have hinc_eq :
      inc = fun ω : OnlineRunSamplePath S1 S2 Sample =>
        ((S2 : ℝ)⁻¹) •
          Finset.sum (Finset.univ : Finset (Fin S2)) (fun i => eps i ω) := rfl
  have hinc_meas : AEStronglyMeasurable inc mu := by
    have havg_meas :
        AEStronglyMeasurable
          (((S2 : ℝ)⁻¹) •
            Finset.sum (Finset.univ : Finset (Fin S2)) (fun i => eps i)) mu := by
      exact
        (Finset.aestronglyMeasurable_sum
          (s := (Finset.univ : Finset (Fin S2)))
          (fun i hi => heps_meas i hi)).const_smul ((S2 : ℝ)⁻¹)
    have havg_eq :
        (((S2 : ℝ)⁻¹) •
          Finset.sum (Finset.univ : Finset (Fin S2)) (fun i => eps i)) =
          fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ((S2 : ℝ)⁻¹) •
              Finset.sum (Finset.univ : Finset (Fin S2)) (fun i => eps i ω) := by
      funext ω
      simp [Finset.sum_apply]
    simpa [hinc_eq, havg_eq] using havg_meas
  have hinc_sq : Integrable (fun ω => ‖inc ω‖ ^ 2) mu := by
    exact
      integrable_sq_norm_centeredMiniBatchAverage
        (μ := mu) (I := (Finset.univ : Finset (Fin S2))) (m := S2)
        (δ := eps) (avg := inc)
        heps_meas
        (fun i hi => (heps_diag i hi).1)
        hinc_eq
  have heps_cross :
      ∀ i ∈ (Finset.univ : Finset (Fin S2)),
        ∀ j ∈ (Finset.univ : Finset (Fin S2)), i ≠ j →
          ∫ ω, inner ℝ (eps i ω) (eps j ω) ∂mu = 0 := by
    intro i _hi j _hj hij
    dsimp [eps]
    exact hrecursive_offdiag_cross_zero t i j hij
  have hinc_bound :
      ∫ ω, ‖inc ω‖ ^ 2 ∂mu ≤
        (P.L ^ 2 / (S2 : ℝ)) *
          ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu := by
    have hraw :
        ∫ ω, ‖(S2 : ℝ)⁻¹ •
            Finset.sum (Finset.univ : Finset (Fin S2)) (fun i => eps i ω)‖ ^ 2 ∂mu ≤
          (P.L ^ 2 *
            ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu) / (S2 : ℝ) :=
      centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero
        (P := mu) (I := (Finset.univ : Finset (Fin S2))) (m := S2)
        (eps := eps)
        (varianceBudget :=
          P.L ^ 2 * ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu)
        hS2_pos (by simp) heps_meas heps_diag heps_cross
    calc
      ∫ ω, ‖inc ω‖ ^ 2 ∂mu
          ≤ (P.L ^ 2 *
              ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu) / (S2 : ℝ) := by
            simpa [hinc_eq] using hraw
      _ = (P.L ^ 2 / (S2 : ℝ)) *
            ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu := by
            ring
  have hrec :
      Filter.EventuallyEq (ae mu) deltaNext (fun ω => deltaPrev ω + inc ω) := by
    simpa [deltaPrev, deltaNext, inc, eps] using hrecursive_centered_residual t hnot
  have hcross : ∫ ω, inner ℝ (deltaPrev ω) (inc ω) ∂mu = 0 := by
    simpa [deltaPrev, inc, eps] using hprev_increment_cross t hprev_sq
  exact
    second_moment_add_recurrence_le_of_cross_zero
      (μ := mu) (deltaPrev := deltaPrev) (deltaNext := deltaNext)
      (inc := inc)
      (B :=
        (P.L ^ 2 / (S2 : ℝ)) *
          ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu)
      hprev_meas hinc_meas hprev_sq hinc_sq hrec hcross hinc_bound

set_option maxHeartbeats 800000

/-- Realized Lemma 2/B.11 for the rounded Option II process.

This is the remaining source-derived stochastic bridge: it must assemble the
refresh mini-batch variance floor, the non-refresh recursive mini-batch
second-moment recurrence, and the rounded `Nat.ceil` epoch/batch arithmetic. -/
theorem optionII_estimator_error_secondMoment_le_epsilon_sq_rounded
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (hepsilon : 0 < epsilon)
    (hL : 0 < P.L)
    (_schedule : Theorem1Schedule P.L P.sigma epsilon n0)
    (_realizationDomain : theorem1RealizedScheduleAdmissible P.L P.sigma epsilon n0)
    (S1 S2 q : ℕ)
    (hS1_eq : S1 = theorem1RefreshBatchCount P.sigma epsilon)
    (hS2_eq : S2 = theorem1RecursiveBatchCount P.sigma epsilon n0)
    (hq_eq : q = theorem1EpochCount P.sigma epsilon n0)
    (mu : Measure (OnlineRunSamplePath S1 S2 Sample))
    (iterate estimator : ℕ → OnlineRunSamplePath S1 S2 Sample → VariableSpace d)
    (refreshSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S1 → Sample)
    (recursiveSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample)
    (hmu_eq :
      mu = onlineRunLaw S1 S2 P.sampleLaw)
    (hrefreshSamples_eq :
      refreshSamples = onlineRefreshSamples (Sample := Sample) S1 S2)
    (hrecursiveSamples_eq :
      recursiveSamples = onlineRecursiveSamples (Sample := Sample) S1 S2)
    (hiterate_eq :
      iterate =
        optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples)
    (hestimator_eq :
      estimator =
        optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples)
    (hprocess :
      ∀ k,
        AEStronglyMeasurable (iterate k) mu ∧
        AEStronglyMeasurable (estimator k) mu)
    (hfixed_zero :
      ∀ x : VariableSpace d,
        ∫ s, P.sampleGrad x s - P.grad x ∂P.sampleLaw = 0)
    (hdiff_fixed_zero :
      ∀ x y : VariableSpace d,
        ∫ s, (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
            ∂P.sampleLaw = 0)
    (hrefresh_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S1) (ω : SOptLib.miniBatchSamplePath S1 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw))
    (hrecursive_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S2) (ω : SOptLib.miniBatchSamplePath S2 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw)) :
    ∀ k,
      Integrable
          (fun ω => ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2) mu ∧
        ∫ ω, ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2 ∂mu ≤
          epsilon ^ 2 := by
  classical
  intro k
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  have hepsilon_nonneg : 0 ≤ epsilon := le_of_lt hepsilon
  have hn0_pos : 0 < n0 :=
    lt_of_lt_of_le zero_lt_one (Theorem1Schedule.n0_lower _schedule)
  have hLn0_pos : 0 < P.L * n0 := mul_pos hL hn0_pos
  have hS1_pos : 0 < S1 := by
    rw [hS1_eq]
    exact _realizationDomain.2.2.2.1
  have hS2_pos : 0 < S2 := by
    rw [hS2_eq]
    exact _realizationDomain.2.2.2.2.1
  have hq_pos : 0 < q := by
    rw [hq_eq]
    exact _realizationDomain.2.2.2.2.2
  haveI : IsProbabilityMeasure mu := by
    rw [hmu_eq]
    exact onlineRunLaw_spec S1 S2 P.sampleLaw
  have hrefreshSamples_measurable :
      ∀ t i, Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
        refreshSamples t ω i) := by
    intro t i
    rw [hrefreshSamples_eq]
    dsimp [onlineRefreshSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
    fun_prop
  have hrecursiveSamples_measurable :
      ∀ t i, Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
        recursiveSamples t ω i) := by
    intro t i
    rw [hrecursiveSamples_eq]
    dsimp [onlineRecursiveSamples, OnlineRunSamplePath, SOptLib.miniBatchSamplePath]
    fun_prop
  have hprocess_measurable :
      ∀ t, Measurable (iterate t) ∧ Measurable (estimator t) := by
    intro t
    rw [hiterate_eq, hestimator_eq]
    exact
      optionII_process_measurable
        P.sampleGrad P.x0 S1 S2 q epsilon P.L n0 refreshSamples recursiveSamples
        P.sampleGrad_joint_measurable hrefreshSamples_measurable
        hrecursiveSamples_measurable t
  have hgrad_measurable : Measurable P.grad := by
    have hLip : LipschitzWith (Real.toNNReal P.L) P.grad :=
      lipschitzWith_of_norm_sub_le_mul P.grad P.L
        (by
          intro x y
          have h := onlineProblem_grad_lipschitz_of_averaged_l2 P hL y x
          simpa [dist_eq_norm] using h)
    exact hLip.continuous.measurable
  have hresidual_kernel_measurable :
      Measurable
        (fun p : VariableSpace d × Sample =>
          P.sampleGrad p.1 p.2 - P.grad p.1) := by
    exact P.sampleGrad_joint_measurable.sub (hgrad_measurable.comp measurable_fst)
  have hstep_bound :
      ∀ j (ω : OnlineRunSamplePath S1 S2 Sample),
        ‖iterate (j + 1) ω - iterate j ω‖ ≤
          epsilon * (P.L * n0)⁻¹ := by
    intro j ω
    rw [hiterate_eq]
    simpa [norm_sub_rev] using
      optionII_step_bound_obligation
        (E := VariableSpace d)
        (epsilon := epsilon) (L := P.L) (n0 := n0)
        (x := optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples j ω)
        (v := optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples j ω)
        hepsilon_nonneg hLn0_pos
  have hrefresh_fixed_diag :
      ∀ t (i : Fin S1) (x : VariableSpace d),
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖P.sampleGrad x (refreshSamples t ω i) - P.grad x‖ ^ 2) mu ∧
          ∫ ω, ‖P.sampleGrad x (refreshSamples t ω i) - P.grad x‖ ^ 2 ∂mu ≤
            P.sigma ^ 2 := by
    intro t i x
    simpa [hmu_eq, hrefreshSamples_eq] using
      onlineRunLaw_refresh_fixed_residual_sq_integrable_le
        P S1 S2 t i x
  have hrecursive_fixed_uncentered_diag :
      ∀ t (i : Fin S2) (x y : VariableSpace d),
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖P.sampleGrad x (recursiveSamples t ω i) -
                P.sampleGrad y (recursiveSamples t ω i)‖ ^ 2) mu ∧
          ∫ ω,
              ‖P.sampleGrad x (recursiveSamples t ω i) -
                P.sampleGrad y (recursiveSamples t ω i)‖ ^ 2 ∂mu ≤
            P.L ^ 2 * ‖x - y‖ ^ 2 := by
    intro t i x y
    simpa [hmu_eq, hrecursiveSamples_eq] using
      onlineRunLaw_recursive_fixed_difference_sq_integrable_le
        P S1 S2 t i x y
  have hrefresh_fixed_centered :
      ∀ t (i : Fin S1) (x : VariableSpace d),
        ∫ ω : OnlineRunSamplePath S1 S2 Sample,
            P.sampleGrad x (refreshSamples t ω i) - P.grad x ∂mu = 0 := by
    intro t i x
    simpa [hmu_eq, hrefreshSamples_eq] using
      onlineRunLaw_refresh_fixed_residual_integral_eq_zero
        P S1 S2 t i x (hfixed_zero x)
  have hrecursive_fixed_centered :
      ∀ t (i : Fin S2) (x y : VariableSpace d),
        ∫ ω : OnlineRunSamplePath S1 S2 Sample,
            (P.sampleGrad x (recursiveSamples t ω i) -
              P.sampleGrad y (recursiveSamples t ω i)) -
              (P.grad x - P.grad y) ∂mu = 0 := by
    intro t i x y
    simpa [hmu_eq, hrecursiveSamples_eq] using
      onlineRunLaw_recursive_fixed_difference_integral_eq_zero
        P S1 S2 t i x y (hdiff_fixed_zero x y)
  have hrefresh_mse :
      ∀ t,
        ∫ ω,
            ‖refreshEstimator P.sampleGrad (iterate t ω)
                (fun i => refreshSamples t ω i) -
              P.grad (iterate t ω)‖ ^ 2 ∂mu ≤
          P.sigma ^ 2 / (S1 : ℝ) := by
    intro t
    let Y : Fin S1 → OnlineRunSamplePath S1 S2 Sample → Sample :=
      fun i ω => refreshSamples t ω i
    have hY_meas : ∀ i ∈ (Finset.univ : Finset (Fin S1)), Measurable (Y i) := by
      intro i _hi
      simpa [Y] using hrefreshSamples_measurable t i
    have hfixed_int :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)), ∀ z : VariableSpace d,
          Integrable (fun ω => ‖P.sampleGrad z (Y i ω) - P.grad z‖ ^ 2) mu := by
      intro i _hi z
      simpa [Y] using (hrefresh_fixed_diag t i z).1
    have hfixed_bound :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)), ∀ z : VariableSpace d,
          ∫ ω, ‖P.sampleGrad z (Y i ω) - P.grad z‖ ^ 2 ∂mu ≤ P.sigma ^ 2 := by
      intro i _hi z
      simpa [Y] using (hrefresh_fixed_diag t i z).2
    have hfixed_zero_map :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)), ∀ z : VariableSpace d,
          ∫ yi, P.sampleGrad z yi - P.grad z ∂Measure.map (Y i) mu = 0 := by
      intro i _hi z
      have hmap :
          Measure.map (Y i) mu = P.sampleLaw := by
        simpa [Y, hmu_eq, hrefreshSamples_eq] using
          onlineRunLaw_map_onlineRefreshSamples
            (Sample := Sample) S1 S2 P.sampleLaw t i
      rw [hmap]
      exact hfixed_zero z
    have hrefresh_freshness :=
      optionII_refresh_iterate_current_sample_freshness
        P epsilon n0 S1 S2 q mu iterate refreshSamples recursiveSamples
        hmu_eq hrefreshSamples_eq hrecursiveSamples_eq hiterate_eq
        hrefresh_iIndep hrecursive_iIndep
    have hindep_query :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)),
          ProbabilityTheory.IndepFun (iterate t) (Y i) mu := by
      intro i _hi
      simpa [Y] using (hrefresh_freshness t).1 i
    have hindep_query_peer :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)),
          ∀ j ∈ (Finset.univ : Finset (Fin S1)), i ≠ j →
            ProbabilityTheory.IndepFun (fun ω => (iterate t ω, Y j ω)) (Y i) mu := by
      intro i _hi j _hj hij
      simpa [Y] using (hrefresh_freshness t).2 i j hij
    have hraw :
        ∫ ω,
            ‖(S1 : ℝ)⁻¹ •
              Finset.sum (Finset.univ : Finset (Fin S1))
                (fun i => P.sampleGrad (iterate t ω) (Y i ω) -
                  P.grad (iterate t ω))‖ ^ 2 ∂mu ≤
          P.sigma ^ 2 / (S1 : ℝ) :=
      randomQuery_centeredMiniBatchAverage_secondMoment_le_variance_div_card
        (P := mu) (I := (Finset.univ : Finset (Fin S1))) (m := S1)
        (G := P.sampleGrad) (target := P.grad) (xq := iterate t)
        (Y := Y) (σ2 := P.sigma ^ 2)
        hS1_pos (by simp) hresidual_kernel_measurable
        (hprocess_measurable t).1 hY_meas hindep_query hindep_query_peer
        (sq_nonneg P.sigma) hfixed_int hfixed_bound hfixed_zero_map
    calc
      ∫ ω,
          ‖refreshEstimator P.sampleGrad (iterate t ω)
              (fun i => refreshSamples t ω i) -
            P.grad (iterate t ω)‖ ^ 2 ∂mu =
          ∫ ω,
            ‖(S1 : ℝ)⁻¹ •
              Finset.sum (Finset.univ : Finset (Fin S1))
                (fun i => P.sampleGrad (iterate t ω) (Y i ω) -
                  P.grad (iterate t ω))‖ ^ 2 ∂mu := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change
              ‖refreshEstimator P.sampleGrad (iterate t ω)
                  (fun i => refreshSamples t ω i) -
                P.grad (iterate t ω)‖ ^ 2 =
                ‖(S1 : ℝ)⁻¹ •
                  Finset.sum (Finset.univ : Finset (Fin S1))
                    (fun i => P.sampleGrad (iterate t ω) (Y i ω) -
                      P.grad (iterate t ω))‖ ^ 2
            rw [refreshEstimator_def]
            rw [miniBatchAverage_sub_target_eq_average_residual
              (I := (Finset.univ : Finset (Fin S1))) (m := S1)
              (hmcard := by simp) (hmpos := hS1_pos)
              (a := fun i : Fin S1 => P.sampleGrad (iterate t ω) (Y i ω))
              (target := P.grad (iterate t ω))]
      _ ≤ P.sigma ^ 2 / (S1 : ℝ) := hraw
  have hrecursive_centered_residual :
      ∀ t, (t + 1) % q ≠ 0 →
        Filter.EventuallyEq (ae mu)
          (fun ω => estimator (t + 1) ω - P.grad (iterate (t + 1) ω))
          (fun ω =>
            (estimator t ω - P.grad (iterate t ω)) +
              (S2 : ℝ)⁻¹ •
                Finset.sum (Finset.univ : Finset (Fin S2))
                  (fun i =>
                    (P.sampleGrad (iterate (t + 1) ω) (recursiveSamples (t + 1) ω i) -
                      P.sampleGrad (iterate t ω) (recursiveSamples (t + 1) ω i)) -
                    (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))) := by
    intro t hnot
    refine Filter.Eventually.of_forall ?_
    intro ω
    rw [hestimator_eq, hiterate_eq]
    simp only [optionIIEstimator_succ, optionIIIterate_succ, hnot, if_false,
      recursiveEstimator_def, Fintype.card_fin]
    rw [← miniBatchAverage_sub_target_eq_average_residual
      (I := (Finset.univ : Finset (Fin S2))) (m := S2)
      (hmcard := by simp) (hmpos := hS2_pos)
      (a := fun i : Fin S2 =>
        P.sampleGrad
          (optionIIUpdate epsilon P.L n0
            (optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
              refreshSamples recursiveSamples t ω)
            (optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
              refreshSamples recursiveSamples t ω))
          (recursiveSamples (t + 1) ω i) -
        P.sampleGrad
          (optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples t ω)
          (recursiveSamples (t + 1) ω i))
      (target :=
        P.grad
          (optionIIUpdate epsilon P.L n0
            (optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
              refreshSamples recursiveSamples t ω)
            (optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
              refreshSamples recursiveSamples t ω)) -
        P.grad
          (optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples t ω))]
    abel
  have hsigma_pos : 0 < P.sigma := by
    have hupper := Theorem1Schedule.n0_upper _schedule
    by_contra hnot
    have hsigma_nonpos : P.sigma ≤ 0 := le_of_not_gt hnot
    have hrhs_nonpos : 2 * P.sigma * epsilon⁻¹ ≤ 0 := by
      have heps_inv_pos : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
      nlinarith
    nlinarith [hn0_pos, hupper, hrhs_nonpos]
  have hrefresh_budget : P.sigma ^ 2 / (S1 : ℝ) ≤ epsilon ^ 2 / 2 := by
    have hceil : 2 * P.sigma ^ 2 * epsilon⁻¹ ^ 2 ≤ (S1 : ℝ) := by
      rw [hS1_eq, theorem1RefreshBatchCount, onlineRefreshBatchSize]
      exact Nat.le_ceil _
    have hreq_pos : 0 < 2 * P.sigma ^ 2 * epsilon⁻¹ ^ 2 := by
      positivity
    have hdiv := div_le_div_of_nonneg_left (sq_nonneg P.sigma) hreq_pos hceil
    calc
      P.sigma ^ 2 / (S1 : ℝ) ≤
          P.sigma ^ 2 / (2 * P.sigma ^ 2 * epsilon⁻¹ ^ 2) := hdiv
      _ = epsilon ^ 2 / 2 := by
          field_simp [ne_of_gt hsigma_pos, ne_of_gt hepsilon]
  have hq_minus_one_lt : ((q - 1 : ℕ) : ℝ) < P.sigma * n0 * epsilon⁻¹ := by
    have hceil_eq : Nat.ceil (P.sigma * n0 * epsilon⁻¹) = q := by
      rw [hq_eq, theorem1EpochCount, onlineEpochLength]
    have hq_ne : q ≠ 0 := Nat.ne_of_gt hq_pos
    have hiff :=
      (Nat.ceil_eq_iff (R := ℝ) (a := P.sigma * n0 * epsilon⁻¹) (n := q) hq_ne).1
        hceil_eq
    exact hiff.1
  have hS2_lower : 2 * P.sigma * (epsilon * n0)⁻¹ ≤ (S2 : ℝ) := by
    rw [hS2_eq, theorem1RecursiveBatchCount, onlineRecursiveBatchSize]
    exact Nat.le_ceil _
  have hrecursive_budget :
      ((q - 1 : ℕ) : ℝ) * (P.L ^ 2 / (S2 : ℝ)) *
          (epsilon * (P.L * n0)⁻¹) ^ 2 ≤ epsilon ^ 2 / 2 := by
    have hden_pos : 0 < 2 * P.sigma * (epsilon * n0)⁻¹ := by
      positivity
    have hcoeff_nonneg : 0 ≤ P.L ^ 2 / (S2 : ℝ) := by
      positivity
    have hstep_sq_nonneg : 0 ≤ (epsilon * (P.L * n0)⁻¹) ^ 2 := sq_nonneg _
    have hterm_le1 :
        ((q - 1 : ℕ) : ℝ) * (P.L ^ 2 / (S2 : ℝ)) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 ≤
          (P.sigma * n0 * epsilon⁻¹) * (P.L ^ 2 / (S2 : ℝ)) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 := by
      have hq_le : ((q - 1 : ℕ) : ℝ) ≤ P.sigma * n0 * epsilon⁻¹ :=
        le_of_lt hq_minus_one_lt
      nlinarith [mul_le_mul_of_nonneg_right hq_le
        (mul_nonneg hcoeff_nonneg hstep_sq_nonneg)]
    have hdiv_le :
        P.L ^ 2 / (S2 : ℝ) ≤
          P.L ^ 2 / (2 * P.sigma * (epsilon * n0)⁻¹) := by
      exact div_le_div_of_nonneg_left (sq_nonneg P.L) hden_pos hS2_lower
    have hterm_le2 :
        (P.sigma * n0 * epsilon⁻¹) * (P.L ^ 2 / (S2 : ℝ)) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 ≤
          (P.sigma * n0 * epsilon⁻¹) *
            (P.L ^ 2 / (2 * P.sigma * (epsilon * n0)⁻¹)) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 := by
      have hfactor_nonneg :
          0 ≤ (P.sigma * n0 * epsilon⁻¹) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hdiv_le hfactor_nonneg]
    calc
      ((q - 1 : ℕ) : ℝ) * (P.L ^ 2 / (S2 : ℝ)) *
          (epsilon * (P.L * n0)⁻¹) ^ 2
          ≤ (P.sigma * n0 * epsilon⁻¹) * (P.L ^ 2 / (S2 : ℝ)) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 := hterm_le1
      _ ≤ (P.sigma * n0 * epsilon⁻¹) *
            (P.L ^ 2 / (2 * P.sigma * (epsilon * n0)⁻¹)) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 := hterm_le2
      _ = epsilon ^ 2 / 2 := by
          field_simp [ne_of_gt hsigma_pos, ne_of_gt hL, ne_of_gt hepsilon,
            ne_of_gt hn0_pos]
  have hrounded_scalar_budget :
      P.sigma ^ 2 / (S1 : ℝ) +
          ((q - 1 : ℕ) : ℝ) * (P.L ^ 2 / (S2 : ℝ)) *
            (epsilon * (P.L * n0)⁻¹) ^ 2 ≤ epsilon ^ 2 := by
    nlinarith [hrefresh_budget, hrecursive_budget]
  have hrecursive_freshness :=
    optionII_recursive_current_sample_freshness
      P epsilon n0 S1 S2 q mu iterate estimator refreshSamples recursiveSamples
      hmu_eq hrefreshSamples_eq hrecursiveSamples_eq hiterate_eq hestimator_eq
      hrefresh_iIndep hrecursive_iIndep
  have hrecursive_sample_law :
      ∀ t (i : Fin S2),
        Measure.map
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              recursiveSamples (t + 1) ω i) mu =
          P.sampleLaw := by
    intro t i
    simpa [hmu_eq, hrecursiveSamples_eq] using
      onlineRunLaw_map_onlineRecursiveSamples
        (Sample := Sample) S1 S2 P.sampleLaw (t + 1) i
  have hrecursive_pair_freshness :
      ∀ t (i : Fin S2),
        ProbabilityTheory.IndepFun
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            (iterate (t + 1) ω, iterate t ω))
          (fun ω => recursiveSamples (t + 1) ω i) mu := by
    intro t i
    have hfresh := (hrecursive_freshness t).1 i
    have hproj :
        Measurable
          (fun q : (VariableSpace d × VariableSpace d) × VariableSpace d =>
            (q.1.2, q.1.1)) :=
      (measurable_snd.comp measurable_fst).prodMk
          (measurable_fst.comp measurable_fst)
    simpa [Function.comp_def] using hfresh.comp hproj measurable_id
  have hiterate_diff_sq_integrable :
      ∀ t,
        Integrable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ‖iterate (t + 1) ω - iterate t ω‖ ^ 2) mu := by
    intro t
    exact
      (SOptLib.integrable_sq_norm_of_ae_bound
        (μ := mu)
        (f := fun ω : OnlineRunSamplePath S1 S2 Sample =>
          iterate (t + 1) ω - iterate t ω)
        ((hprocess (t + 1)).1.sub (hprocess t).1)
        (Filter.Eventually.of_forall (hstep_bound t))).1
  have hrecursive_uncentered_diag_random :
      ∀ t (i : Fin S2),
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖P.sampleGrad (iterate (t + 1) ω)
                  (recursiveSamples (t + 1) ω i) -
                P.sampleGrad (iterate t ω)
                  (recursiveSamples (t + 1) ω i)‖ ^ 2) mu ∧
          ∫ ω,
              ‖P.sampleGrad (iterate (t + 1) ω)
                  (recursiveSamples (t + 1) ω i) -
                P.sampleGrad (iterate t ω)
                  (recursiveSamples (t + 1) ω i)‖ ^ 2 ∂mu ≤
            P.L ^ 2 *
              ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu := by
    intro t i
    have hGdiff_meas :
        Measurable
          (fun p : (VariableSpace d × VariableSpace d) × Sample =>
            P.sampleGrad p.1.1 p.2 - P.sampleGrad p.1.2 p.2) :=
      (P.sampleGrad_joint_measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      (P.sampleGrad_joint_measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have hbudget_meas :
        Measurable
          (fun z : VariableSpace d × VariableSpace d =>
            P.L ^ 2 * ‖z.1 - z.2‖ ^ 2) := by
      fun_prop
    have hdist_sq_meas :
        Measurable
          (fun z : VariableSpace d × VariableSpace d => ‖z.1 - z.2‖ ^ 2) := by
      fun_prop
    have hZpair_meas :
        Measurable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            (iterate (t + 1) ω, iterate t ω)) :=
      (hprocess_measurable (t + 1)).1.prodMk (hprocess_measurable t).1
    have hraw :=
      random_pair_oracle_difference_second_moment_le_of_indep
        (P := mu) (ν := P.sampleLaw)
        (Y := fun ω : OnlineRunSamplePath S1 S2 Sample =>
          recursiveSamples (t + 1) ω i)
        (Zpair := fun ω : OnlineRunSamplePath S1 S2 Sample =>
          (iterate (t + 1) ω, iterate t ω))
        (G := P.sampleGrad)
        (feasible := Set.univ)
        (dist := fun x y : VariableSpace d => ‖x - y‖)
        (L := P.L)
        hGdiff_meas hbudget_meas hdist_sq_meas hZpair_meas
        (hrecursiveSamples_measurable (t + 1) i)
        (hrecursive_pair_freshness t i)
        (hrecursive_sample_law t i)
        (Filter.Eventually.of_forall (fun _ => trivial))
        (hiterate_diff_sq_integrable t)
        (fun z _hz => by
          simpa [SOptLib.expectationWellDefined] using
            P.averaged_lipschitz_gradient_wellDefined z.1 z.2)
        (fun z _hz => by
          simpa using P.averaged_lipschitz_gradient_bound z.1 z.2)
    simpa using hraw
  have hrecursive_target_cross_zero :
      ∀ (t : ℕ) (i : Fin S2),
        MeasureTheory.integral mu
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              inner ℝ
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))
                ((P.sampleGrad (iterate (t + 1) ω)
                      (recursiveSamples (t + 1) ω i) -
                    P.sampleGrad (iterate t ω)
                      (recursiveSamples (t + 1) ω i)) -
                  (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))) =
          0 := by
    intro t i
    have hres_meas :
        Measurable
          (fun p : (VariableSpace d × VariableSpace d) × Sample =>
            (P.sampleGrad p.1.1 p.2 - P.sampleGrad p.1.2 p.2) -
              (P.grad p.1.1 - P.grad p.1.2)) := by
      exact
        ((P.sampleGrad_joint_measurable.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
        (P.sampleGrad_joint_measurable.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).sub
        ((hgrad_measurable.comp (measurable_fst.comp measurable_fst)).sub
          (hgrad_measurable.comp (measurable_snd.comp measurable_fst)))
    have hd_meas :
        Measurable
          (fun q : VariableSpace d × VariableSpace d => P.grad q.1 - P.grad q.2) :=
      (hgrad_measurable.comp measurable_fst).sub
        (hgrad_measurable.comp measurable_snd)
    have hquery_meas :
        Measurable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            (iterate (t + 1) ω, iterate t ω)) :=
      (hprocess_measurable (t + 1)).1.prodMk (hprocess_measurable t).1
    have hfixed_int :
        ∀ q : VariableSpace d × VariableSpace d,
          Integrable
            (fun s : Sample =>
              (P.sampleGrad q.1 s - P.sampleGrad q.2 s) -
                (P.grad q.1 - P.grad q.2)) P.sampleLaw := by
      intro q
      have hdiff_meas :
          Measurable
            (fun s : Sample => P.sampleGrad q.1 s - P.sampleGrad q.2 s) :=
        (P.sampleGrad_joint_measurable.comp
          ((measurable_const : Measurable fun _ : Sample => q.1).prodMk
            measurable_id)).sub
        (P.sampleGrad_joint_measurable.comp
          ((measurable_const : Measurable fun _ : Sample => q.2).prodMk
            measurable_id))
      have hdiff_sq :
          Integrable
            (fun s : Sample => ‖P.sampleGrad q.1 s - P.sampleGrad q.2 s‖ ^ 2)
              P.sampleLaw := by
        simpa [SOptLib.expectationWellDefined] using
          P.averaged_lipschitz_gradient_wellDefined q.1 q.2
      have hdiff_int :
          Integrable (fun s : Sample => P.sampleGrad q.1 s - P.sampleGrad q.2 s)
            P.sampleLaw :=
        integrable_of_integrable_norm_sq
          hdiff_meas.aestronglyMeasurable hdiff_sq
      exact hdiff_int.sub (integrable_const (P.grad q.1 - P.grad q.2))
    have hzero :=
      randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
        (P := mu) (ν := P.sampleLaw)
        (query := fun ω : OnlineRunSamplePath S1 S2 Sample =>
          (iterate (t + 1) ω, iterate t ω))
        (sample := fun ω => recursiveSamples (t + 1) ω i)
        (residual := fun q s =>
          (P.sampleGrad q.1 s - P.sampleGrad q.2 s) -
            (P.grad q.1 - P.grad q.2))
        (d := fun q => P.grad q.1 - P.grad q.2)
        hres_meas hd_meas hquery_meas
        (hrecursiveSamples_measurable (t + 1) i)
        (hrecursive_pair_freshness t i)
        (hrecursive_sample_law t i)
        hfixed_int
        (fun q => hdiff_fixed_zero q.1 q.2)
    simpa using hzero
  have hrecursive_centered_diag :
      ∀ (t : ℕ) (i : Fin S2),
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖(P.sampleGrad (iterate (t + 1) ω)
                    (recursiveSamples (t + 1) ω i) -
                  P.sampleGrad (iterate t ω)
                    (recursiveSamples (t + 1) ω i)) -
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))‖ ^ 2) mu ∧
          ∫ ω,
              ‖(P.sampleGrad (iterate (t + 1) ω)
                    (recursiveSamples (t + 1) ω i) -
                  P.sampleGrad (iterate t ω)
                    (recursiveSamples (t + 1) ω i)) -
                (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))‖ ^ 2 ∂mu ≤
            P.L ^ 2 *
              ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu := by
    intro t i
    have horacle_meas :
        Measurable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            P.sampleGrad (iterate (t + 1) ω)
                (recursiveSamples (t + 1) ω i) -
              P.sampleGrad (iterate t ω)
                (recursiveSamples (t + 1) ω i)) :=
      (P.sampleGrad_joint_measurable.comp
        ((hprocess_measurable (t + 1)).1.prodMk
          (hrecursiveSamples_measurable (t + 1) i))).sub
      (P.sampleGrad_joint_measurable.comp
        ((hprocess_measurable t).1.prodMk
          (hrecursiveSamples_measurable (t + 1) i)))
    have htarget_aesm :
        AEStronglyMeasurable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)) mu :=
      ((hgrad_measurable.comp (hprocess_measurable (t + 1)).1).sub
        (hgrad_measurable.comp (hprocess_measurable t).1)).aestronglyMeasurable
    exact
      centered_oracleDifference_secondMoment_le_of_unbiased_smooth
        (P := mu)
        (sample := fun ω : OnlineRunSamplePath S1 S2 Sample =>
          recursiveSamples (t + 1) ω i)
        (x := iterate (t + 1))
        (y := iterate t)
        (G := P.sampleGrad)
        (target := P.grad)
        (L := P.L)
        horacle_meas.aestronglyMeasurable
        (hiterate_diff_sq_integrable t)
        (hrecursive_uncentered_diag_random t i)
        htarget_aesm
        (Filter.Eventually.of_forall
          (fun ω =>
            onlineProblem_grad_lipschitz_of_averaged_l2 P hL
              (iterate t ω) (iterate (t + 1) ω)))
        (hrecursive_target_cross_zero t i)
  have hrecursive_pair_peer_freshness :
      ∀ (t : ℕ) (i j : Fin S2), i ≠ j →
        ProbabilityTheory.IndepFun
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ((iterate (t + 1) ω, iterate t ω), recursiveSamples (t + 1) ω j))
          (fun ω => recursiveSamples (t + 1) ω i) mu := by
    intro t i j hij
    have hfresh := (hrecursive_freshness t).2 i j hij
    have hproj :
        Measurable
          (fun q : ((VariableSpace d × VariableSpace d) × VariableSpace d) × Sample =>
            ((q.1.1.2, q.1.1.1), q.2)) :=
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
        measurable_snd
    simpa [Function.comp_def] using hfresh.comp hproj measurable_id
  have hcentered_difference_kernel_measurable :
      Measurable
        (fun p : (VariableSpace d × VariableSpace d) × Sample =>
          (P.sampleGrad p.1.1 p.2 - P.sampleGrad p.1.2 p.2) -
            (P.grad p.1.1 - P.grad p.1.2)) := by
    exact
      ((P.sampleGrad_joint_measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      (P.sampleGrad_joint_measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).sub
      ((hgrad_measurable.comp (measurable_fst.comp measurable_fst)).sub
        (hgrad_measurable.comp (measurable_snd.comp measurable_fst)))
  have hrecursive_offdiag_cross_zero :
      ∀ (t : ℕ) (i j : Fin S2), i ≠ j →
        MeasureTheory.integral mu
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              inner ℝ
                ((P.sampleGrad (iterate (t + 1) ω)
                      (recursiveSamples (t + 1) ω i) -
                    P.sampleGrad (iterate t ω)
                      (recursiveSamples (t + 1) ω i)) -
                  (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))
                ((P.sampleGrad (iterate (t + 1) ω)
                      (recursiveSamples (t + 1) ω j) -
                    P.sampleGrad (iterate t ω)
                      (recursiveSamples (t + 1) ω j)) -
                  (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))) =
          0 := by
    intro t i j hij
    have hres_meas :
        Measurable
          (fun p : ((VariableSpace d × VariableSpace d) × Sample) × Sample =>
            (P.sampleGrad p.1.1.1 p.2 - P.sampleGrad p.1.1.2 p.2) -
              (P.grad p.1.1.1 - P.grad p.1.1.2)) := by
      exact
        ((P.sampleGrad_joint_measurable.comp
          ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
            measurable_snd)).sub
        (P.sampleGrad_joint_measurable.comp
          ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
            measurable_snd))).sub
        ((hgrad_measurable.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).sub
          (hgrad_measurable.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
    have hd_meas :
        Measurable
          (fun q : (VariableSpace d × VariableSpace d) × Sample =>
            (P.sampleGrad q.1.1 q.2 - P.sampleGrad q.1.2 q.2) -
              (P.grad q.1.1 - P.grad q.1.2)) := by
      exact
        ((P.sampleGrad_joint_measurable.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
        (P.sampleGrad_joint_measurable.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))).sub
        ((hgrad_measurable.comp (measurable_fst.comp measurable_fst)).sub
          (hgrad_measurable.comp (measurable_snd.comp measurable_fst)))
    have hquery_meas :
        Measurable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ((iterate (t + 1) ω, iterate t ω), recursiveSamples (t + 1) ω j)) :=
      ((hprocess_measurable (t + 1)).1.prodMk (hprocess_measurable t).1).prodMk
        (hrecursiveSamples_measurable (t + 1) j)
    have hfixed_int :
        ∀ q : (VariableSpace d × VariableSpace d) × Sample,
          Integrable
            (fun s : Sample =>
              (P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s) -
                (P.grad q.1.1 - P.grad q.1.2)) P.sampleLaw := by
      intro q
      have hdiff_meas :
          Measurable
            (fun s : Sample => P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s) :=
        (P.sampleGrad_joint_measurable.comp
          ((measurable_const : Measurable fun _ : Sample => q.1.1).prodMk
            measurable_id)).sub
        (P.sampleGrad_joint_measurable.comp
          ((measurable_const : Measurable fun _ : Sample => q.1.2).prodMk
            measurable_id))
      have hdiff_sq :
          Integrable
            (fun s : Sample => ‖P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s‖ ^ 2)
              P.sampleLaw := by
        simpa [SOptLib.expectationWellDefined] using
          P.averaged_lipschitz_gradient_wellDefined q.1.1 q.1.2
      have hdiff_int :
          Integrable (fun s : Sample => P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s)
            P.sampleLaw :=
        integrable_of_integrable_norm_sq
          hdiff_meas.aestronglyMeasurable hdiff_sq
      exact hdiff_int.sub (integrable_const (P.grad q.1.1 - P.grad q.1.2))
    have hzero :=
      randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
        (P := mu) (ν := P.sampleLaw)
        (query := fun ω : OnlineRunSamplePath S1 S2 Sample =>
          ((iterate (t + 1) ω, iterate t ω), recursiveSamples (t + 1) ω j))
        (sample := fun ω => recursiveSamples (t + 1) ω i)
        (residual := fun q s =>
          (P.sampleGrad q.1.1 s - P.sampleGrad q.1.2 s) -
            (P.grad q.1.1 - P.grad q.1.2))
        (d := fun q =>
          (P.sampleGrad q.1.1 q.2 - P.sampleGrad q.1.2 q.2) -
            (P.grad q.1.1 - P.grad q.1.2))
        hres_meas hd_meas hquery_meas
        (hrecursiveSamples_measurable (t + 1) i)
        (hrecursive_pair_peer_freshness t i j hij)
        (hrecursive_sample_law t i)
        hfixed_int
        (fun q => hdiff_fixed_zero q.1.1 q.1.2)
    simpa [real_inner_comm] using hzero
  have hrecursive_prev_residual_coordinate_cross_zero :
      ∀ (t : ℕ) (i : Fin S2),
        MeasureTheory.integral mu
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              inner ℝ
                (estimator t ω - P.grad (iterate t ω))
                ((P.sampleGrad (iterate (t + 1) ω)
                      (recursiveSamples (t + 1) ω i) -
                    P.sampleGrad (iterate t ω)
                      (recursiveSamples (t + 1) ω i)) -
                  (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω)))) =
          0 := by
    exact
      optionII_recursive_prev_residual_centered_coordinate_cross_zero
        P S1 S2 mu iterate estimator recursiveSamples
        hrecursiveSamples_measurable hprocess_measurable hgrad_measurable
        hrecursive_freshness hrecursive_sample_law
        hdiff_fixed_zero
  have hrecursive_prev_residual_minibatch_cross_zero :
      ∀ (t : ℕ),
        Integrable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2) mu →
        MeasureTheory.integral mu
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              inner ℝ
                (estimator t ω - P.grad (iterate t ω))
                ((S2 : ℝ)⁻¹ •
                  Finset.sum (Finset.univ : Finset (Fin S2))
                    (fun i =>
                      (P.sampleGrad (iterate (t + 1) ω)
                          (recursiveSamples (t + 1) ω i) -
                        P.sampleGrad (iterate t ω)
                          (recursiveSamples (t + 1) ω i)) -
                      (P.grad (iterate (t + 1) ω) - P.grad (iterate t ω))))) =
          0 := by
    exact
      optionII_recursive_prev_residual_centered_minibatch_cross_zero
        P S1 S2 mu iterate estimator recursiveSamples
        hrecursiveSamples_measurable hprocess_measurable hgrad_measurable
        hcentered_difference_kernel_measurable hrecursive_centered_diag
        hrecursive_prev_residual_coordinate_cross_zero
  have hrecursive_step :
      ∀ t, (t + 1) % q ≠ 0 →
        Integrable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2) mu →
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖estimator (t + 1) ω - P.grad (iterate (t + 1) ω)‖ ^ 2) mu ∧
          ∫ ω, ‖estimator (t + 1) ω - P.grad (iterate (t + 1) ω)‖ ^ 2 ∂mu ≤
            ∫ ω, ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2 ∂mu +
              (P.L ^ 2 / (S2 : ℝ)) *
                ∫ ω, ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu := by
    exact
      optionII_recursive_residual_second_moment_step
        P S1 S2 q mu iterate estimator recursiveSamples hS2_pos
        hrecursiveSamples_measurable hprocess_measurable hgrad_measurable
        hcentered_difference_kernel_measurable hrecursive_centered_residual
        hrecursive_centered_diag hrecursive_offdiag_cross_zero
        hrecursive_prev_residual_minibatch_cross_zero
  have hrefresh_estimator_eq :
      ∀ t, t % q = 0 →
        ∀ ω : OnlineRunSamplePath S1 S2 Sample,
          estimator t ω =
            refreshEstimator P.sampleGrad (iterate t ω)
              (fun i => refreshSamples t ω i) := by
    intro t ht ω
    cases t with
    | zero =>
        rw [hestimator_eq, hiterate_eq]
        rfl
    | succ n =>
        rw [hestimator_eq, hiterate_eq]
        simp [optionIIEstimator_succ, optionIIIterate_succ, ht]
  let stepBound : ℝ := epsilon * (P.L * n0)⁻¹
  let coeff : ℝ := P.L ^ 2 / (S2 : ℝ)
  let idx : ℕ → ℕ → ℕ := fun s j => s * q + (j - 1)
  have hrefresh_int :
      ∀ t, t % q = 0 →
        Integrable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2) mu := by
    intro t ht
    let Y : Fin S1 → OnlineRunSamplePath S1 S2 Sample → Sample :=
      fun i ω => refreshSamples t ω i
    have hY_meas : ∀ i ∈ (Finset.univ : Finset (Fin S1)), Measurable (Y i) := by
      intro i _hi
      simpa [Y] using hrefreshSamples_measurable t i
    have hfixed_int :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)), ∀ z : VariableSpace d,
          Integrable (fun ω => ‖P.sampleGrad z (Y i ω) - P.grad z‖ ^ 2) mu := by
      intro i _hi z
      simpa [Y] using (hrefresh_fixed_diag t i z).1
    have hfixed_bound :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)), ∀ z : VariableSpace d,
          ∫ ω, ‖P.sampleGrad z (Y i ω) - P.grad z‖ ^ 2 ∂mu ≤ P.sigma ^ 2 := by
      intro i _hi z
      simpa [Y] using (hrefresh_fixed_diag t i z).2
    have hrefresh_freshness :=
      optionII_refresh_iterate_current_sample_freshness
        P epsilon n0 S1 S2 q mu iterate refreshSamples recursiveSamples
        hmu_eq hrefreshSamples_eq hrecursiveSamples_eq hiterate_eq
        hrefresh_iIndep hrecursive_iIndep
    have hindep_query :
        ∀ i ∈ (Finset.univ : Finset (Fin S1)),
          ProbabilityTheory.IndepFun (iterate t) (Y i) mu := by
      intro i _hi
      simpa [Y] using (hrefresh_freshness t).1 i
    have hraw :
        Integrable
          (fun ω : OnlineRunSamplePath S1 S2 Sample =>
            ‖(S1 : ℝ)⁻¹ •
              Finset.sum (Finset.univ : Finset (Fin S1))
                (fun i => P.sampleGrad (iterate t ω) (Y i ω) -
                  P.grad (iterate t ω))‖ ^ 2) mu :=
      integrable_sq_norm_randomQuery_centeredMiniBatchAverage_of_fixed_variance
        (P := mu) (I := (Finset.univ : Finset (Fin S1))) (m := S1)
        (G := P.sampleGrad) (target := P.grad) (xq := iterate t)
        (Y := Y) (σ2 := P.sigma ^ 2)
        hresidual_kernel_measurable (hprocess_measurable t).1 hY_meas
        hindep_query (sq_nonneg P.sigma) hfixed_int hfixed_bound
    refine hraw.congr (Filter.Eventually.of_forall ?_)
    intro ω
    change
      ‖(S1 : ℝ)⁻¹ •
        Finset.sum (Finset.univ : Finset (Fin S1))
          (fun i => P.sampleGrad (iterate t ω) (Y i ω) -
            P.grad (iterate t ω))‖ ^ 2 =
      ‖estimator t ω - P.grad (iterate t ω)‖ ^ 2
    symm
    rw [hrefresh_estimator_eq t ht ω]
    rw [refreshEstimator_def]
    rw [miniBatchAverage_sub_target_eq_average_residual
      (I := (Finset.univ : Finset (Fin S1))) (m := S1)
      (hmcard := by simp) (hmpos := hS1_pos)
      (a := fun i : Fin S1 => P.sampleGrad (iterate t ω) (Y i ω))
      (target := P.grad (iterate t ω))]
  have hstep_sq_bound :
      ∀ t,
        ∫ ω : OnlineRunSamplePath S1 S2 Sample,
          ‖iterate (t + 1) ω - iterate t ω‖ ^ 2 ∂mu ≤ stepBound ^ 2 := by
    intro t
    simpa [stepBound] using
      (SOptLib.integrable_sq_norm_of_ae_bound
        (μ := mu)
        (f := fun ω : OnlineRunSamplePath S1 S2 Sample =>
          iterate (t + 1) ω - iterate t ω)
        ((hprocess (t + 1)).1.sub (hprocess t).1)
        (Filter.Eventually.of_forall (hstep_bound t))).2
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hidx_succ : ∀ s j, 2 ≤ j → idx s j = idx s (j - 1) + 1 := by
    intro s j hj
    dsimp [idx]
    omega
  have hidx_mod_nonzero :
      ∀ s j, 2 ≤ j → j ≤ q → (idx s (j - 1) + 1) % q ≠ 0 := by
    intro s j hj2 hjq
    have hjm1_pos : 0 < j - 1 := by omega
    have hjm1_lt : j - 1 < q := by omega
    have hidxplus : idx s (j - 1) + 1 = s * q + (j - 1) := by
      dsimp [idx]
      omega
    rw [hidxplus]
    have hmod : (s * q + (j - 1)) % q = j - 1 := by
      rw [Nat.mul_comm s q, Nat.add_comm, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hjm1_lt]
    rw [hmod]
    exact Nat.ne_of_gt hjm1_pos
  have hepoch :
      ∀ s j, 1 ≤ j → j ≤ q →
        Integrable
            (fun ω : OnlineRunSamplePath S1 S2 Sample =>
              ‖estimator (idx s j) ω - P.grad (iterate (idx s j) ω)‖ ^ 2) mu ∧
          ∫ ω : OnlineRunSamplePath S1 S2 Sample,
              ‖estimator (idx s j) ω - P.grad (iterate (idx s j) ω)‖ ^ 2 ∂mu ≤
            P.sigma ^ 2 / (S1 : ℝ) + ((j - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2 := by
    intro s j hj1 hjq
    induction j with
    | zero => omega
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst n
          have hmod : (s * q) % q = 0 := by
            rw [Nat.mul_comm]
            exact Nat.mul_mod_right q s
          constructor
          · simpa [idx] using hrefresh_int (s * q) hmod
          · have hbase :
              ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                  ‖estimator (s * q) ω - P.grad (iterate (s * q) ω)‖ ^ 2 ∂mu ≤
                P.sigma ^ 2 / (S1 : ℝ) := by
                calc
                  ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                      ‖estimator (s * q) ω - P.grad (iterate (s * q) ω)‖ ^ 2 ∂mu =
                    ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                      ‖refreshEstimator P.sampleGrad (iterate (s * q) ω)
                          (fun i => refreshSamples (s * q) ω i) -
                        P.grad (iterate (s * q) ω)‖ ^ 2 ∂mu := by
                      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                      intro ω
                      change
                        ‖estimator (s * q) ω - P.grad (iterate (s * q) ω)‖ ^ 2 =
                          ‖refreshEstimator P.sampleGrad (iterate (s * q) ω)
                              (fun i => refreshSamples (s * q) ω i) -
                            P.grad (iterate (s * q) ω)‖ ^ 2
                      rw [hrefresh_estimator_eq (s * q) hmod ω]
                  _ ≤ P.sigma ^ 2 / (S1 : ℝ) := hrefresh_mse (s * q)
            simpa [idx] using hbase
        · have hn_pos : 1 ≤ n := by omega
          have hn_le_q : n ≤ q := by omega
          have hprev := ih hn_pos hn_le_q
          have hnot : (idx s n + 1) % q ≠ 0 := by
            simpa using hidx_mod_nonzero s (n + 1) (by omega) hjq
          have hstep := hrecursive_step (idx s n) hnot hprev.1
          have hidx : idx s (n + 1) = idx s n + 1 := hidx_succ s (n + 1) (by omega)
          constructor
          · simpa [hidx] using hstep.1
          · have hstep_le :
                P.L ^ 2 / (S2 : ℝ) *
                  ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                    ‖iterate (idx s n + 1) ω - iterate (idx s n) ω‖ ^ 2 ∂mu ≤
                  coeff * stepBound ^ 2 := by
              simpa [coeff] using
                mul_le_mul_of_nonneg_left (hstep_sq_bound (idx s n)) hcoeff_nonneg
            have hrec_le :
                ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                    ‖estimator (idx s n + 1) ω -
                      P.grad (iterate (idx s n + 1) ω)‖ ^ 2 ∂mu ≤
                  ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                    ‖estimator (idx s n) ω - P.grad (iterate (idx s n) ω)‖ ^ 2 ∂mu +
                      coeff * stepBound ^ 2 := by
              nlinarith [hstep.2, hstep_le]
            have hcast :
                (((n + 1) - 1 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
              have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn_pos
              have hreal : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
                exact_mod_cast hnat
              simpa using hreal.symm
            have hbound :
                ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                    ‖estimator (idx s n + 1) ω -
                      P.grad (iterate (idx s n + 1) ω)‖ ^ 2 ∂mu ≤
                  P.sigma ^ 2 / (S1 : ℝ) +
                    (((n + 1) - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2 := by
              calc
                ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                    ‖estimator (idx s n + 1) ω -
                      P.grad (iterate (idx s n + 1) ω)‖ ^ 2 ∂mu ≤
                  ∫ ω : OnlineRunSamplePath S1 S2 Sample,
                    ‖estimator (idx s n) ω - P.grad (iterate (idx s n) ω)‖ ^ 2 ∂mu +
                      coeff * stepBound ^ 2 := hrec_le
                _ ≤ (P.sigma ^ 2 / (S1 : ℝ) +
                        ((n - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2) +
                      coeff * stepBound ^ 2 := by
                      nlinarith [hprev.2]
                _ = P.sigma ^ 2 / (S1 : ℝ) +
                      (((n + 1) - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2 := by
                      rw [hcast]
                      ring
            simpa [hidx] using hbound
  let s : ℕ := k / q
  let j : ℕ := k % q + 1
  have hj1 : 1 ≤ j := by
    dsimp [j]
    omega
  have hjq : j ≤ q := by
    dsimp [j]
    exact Nat.succ_le_of_lt (Nat.mod_lt k hq_pos)
  have hidx : idx s j = k := by
    dsimp [idx, s, j]
    rw [Nat.mul_comm (k / q) q]
    exact Nat.div_add_mod k q
  have hk_epoch := hepoch s j hj1 hjq
  have hjsub : j - 1 = k % q := by
    dsimp [j]
  have hmod_le : k % q ≤ q - 1 := by
    exact Nat.le_pred_of_lt (Nat.mod_lt k hq_pos)
  have hrec_le :
      ((j - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2 ≤
        ((q - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2 := by
    rw [hjsub]
    have hcast_le : ((k % q : ℕ) : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
      exact_mod_cast hmod_le
    have hfactor_nonneg : 0 ≤ coeff * stepBound ^ 2 := by
      exact mul_nonneg hcoeff_nonneg (sq_nonneg stepBound)
    calc
      ((k % q : ℕ) : ℝ) * coeff * stepBound ^ 2 =
          ((k % q : ℕ) : ℝ) * (coeff * stepBound ^ 2) := by ring
      _ ≤ ((q - 1 : ℕ) : ℝ) * (coeff * stepBound ^ 2) :=
          mul_le_mul_of_nonneg_right hcast_le hfactor_nonneg
      _ = ((q - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2 := by ring
  exact And.intro
    (by simpa [hidx] using hk_epoch.1)
    (by
      have hscalar :
          P.sigma ^ 2 / (S1 : ℝ) +
              ((j - 1 : ℕ) : ℝ) * coeff * stepBound ^ 2 ≤ epsilon ^ 2 := by
        dsimp [coeff, stepBound] at hrec_le ⊢
        nlinarith [hrec_le, hrounded_scalar_budget]
      exact le_trans (by simpa [hidx] using hk_epoch.2) hscalar)

/-- Objective values along the rounded Option II iterate are integrable.

This is Lean bookkeeping for taking expectations in Lemma 4: bounded Option II
motion gives centered L2 control of the iterate, and smoothness of `P.f`
turns that into scalar-value integrability. -/
theorem optionII_objective_value_integrable_of_bounded_motion
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    {epsilon n0 : ℝ}
    (hepsilon : 0 < epsilon)
    (hL : 0 < P.L)
    (_schedule : Theorem1Schedule P.L P.sigma epsilon n0)
    {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    {S1 S2 q : ℕ}
    (refreshSamples : ℕ → Ω → Fin S1 → Sample)
    (recursiveSamples : ℕ → Ω → Fin S2 → Sample)
    (iterate : ℕ → Ω → VariableSpace d)
    (hiterate_eq :
      iterate =
        optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples)
    (hiterate_aesm : ∀ k, AEStronglyMeasurable (iterate k) mu) :
    ∀ k, Integrable (fun ω => P.f (iterate k ω)) mu := by
  intro k
  have hn0_pos : 0 < n0 :=
    lt_of_lt_of_le zero_lt_one (Theorem1Schedule.n0_lower _schedule)
  have hLn0_pos : 0 < P.L * n0 := mul_pos hL hn0_pos
  let D : ℝ := (k : ℝ) * (epsilon * (P.L * n0)⁻¹)
  have hcenter_sq :
      Integrable (fun ω => ‖P.x0 - iterate k ω‖ ^ 2) mu := by
    have hcenter_aesm :
        AEStronglyMeasurable (fun ω => P.x0 - iterate k ω) mu :=
      aestronglyMeasurable_const.sub (hiterate_aesm k)
    have hdist : ∀ᵐ ω ∂mu, ‖P.x0 - iterate k ω‖ ≤ D := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have hraw :
          ‖P.x0 -
              optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
                refreshSamples recursiveSamples k ω‖ ≤ D := by
        simpa [D] using
          optionII_iterate_dist_initial_le
            P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples (le_of_lt hepsilon) hLn0_pos k ω
      simpa [hiterate_eq] using hraw
    exact
      (SOptLib.integrable_sq_norm_of_ae_bound
        (μ := mu)
        (f := fun ω => P.x0 - iterate k ω)
        hcenter_aesm hdist).1
  have hgrad_lipschitz :
      ∀ x y : VariableSpace d, ‖P.grad y - P.grad x‖ ≤ P.L * ‖y - x‖ :=
    onlineProblem_grad_lipschitz_of_averaged_l2 P hL
  have hf_cont : Continuous P.f := by
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    exact (P.grad_hasGradientAt x).continuousAt
  have hf_aesm : AEStronglyMeasurable (fun ω => P.f (iterate k ω)) mu :=
    hf_cont.comp_aestronglyMeasurable (hiterate_aesm k)
  have hrem_bound :
      ∀ᵐ ω ∂mu,
        abs (P.f (iterate k ω) - P.f P.x0 -
            inner ℝ (P.grad P.x0) (iterate k ω - P.x0)) ≤
          (P.L / 2) * ‖iterate k ω - P.x0‖ ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    exact
      SOptLib.abs_taylor_remainder_le_of_hasGradientAt_lipschitzOn_convex
        (Set.univ : Set (VariableSpace d)) P.f P.grad P.L
        convex_univ
        (by intro z _hz; exact P.grad_hasGradientAt z)
        (by
          intro z _hz w _hw
          exact hgrad_lipschitz w z)
        (Set.mem_univ P.x0) (Set.mem_univ (iterate k ω))
  exact
    SOptLib.integrable_smooth_value_of_centered_l2
      P.f (P.grad P.x0) P.x0 P.L (iterate k)
      (hiterate_aesm k) hf_aesm hcenter_sq hrem_bound

/-- The printed Theorem 1 budget `⌊4LΔn₀ε⁻²⌋+1` dominates the real
quantity it rounds up, under the source sign/domain facts. -/
theorem theorem1Budget_cast_lower_bound
    (L Delta n0 epsilon : ℝ)
    (hL : 0 ≤ L)
    (hDelta : 0 ≤ Delta)
    (hn0 : 0 ≤ n0)
    (hepsilon : 0 < epsilon) :
    4 * L * Delta * n0 * epsilon⁻¹ ^ 2 ≤
      (theorem1Budget L Delta n0 epsilon : ℝ) := by
  let A : ℝ := 4 * L * Delta * n0 * epsilon⁻¹ ^ 2
  have _hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA_lt_floor_add_one : A < (Nat.floor A : ℝ) + 1 :=
    Nat.lt_floor_add_one A
  have hbudget_eq :
      (theorem1Budget L Delta n0 epsilon : ℝ) = (Nat.floor A : ℝ) + 1 := by
    unfold theorem1Budget
    dsimp [A]
    norm_num [Nat.cast_add, Nat.cast_one]
  rw [hbudget_eq]
  exact le_of_lt hA_lt_floor_add_one

/-- Scalar Eq. (B.13) to Eq. (B.14) normalization for Theorem 1 Option II.

This is the paper's division by `(ε/(4Ln₀))K` plus the printed floor-budget
lower bound, with the estimator sum kept abstract as `S`. -/
theorem optionII_average_estimator_norm_le_four_epsilon_of_B13_budget
    (S L Delta n0 epsilon : ℝ)
    (hL : 0 < L)
    (hDelta : 0 ≤ Delta)
    (hn0_pos : 0 < n0)
    (hepsilon : 0 < epsilon)
    (hB13 :
      (epsilon / (4 * L * n0)) * S ≤
        Delta +
          (theorem1Budget L Delta n0 epsilon : ℝ) *
            (3 * epsilon ^ 2 / (4 * L * n0))) :
    (theorem1Budget L Delta n0 epsilon : ℝ)⁻¹ * S ≤ 4 * epsilon := by
  let K : ℕ := theorem1Budget L Delta n0 epsilon
  let alpha : ℝ := epsilon / (4 * L * n0)
  have hK_pos_nat : 0 < K := by
    dsimp [K]
    exact theorem1Budget_pos L Delta n0 epsilon
  have hK_pos : 0 < (K : ℝ) := by
    exact_mod_cast hK_pos_nat
  have hK_ne : (K : ℝ) ≠ 0 := ne_of_gt hK_pos
  have halpha_pos : 0 < alpha := by
    dsimp [alpha]
    positivity
  have hB13' :
      alpha * S ≤
        Delta + (K : ℝ) * (3 * epsilon ^ 2 / (4 * L * n0)) := by
    simpa [alpha, K] using hB13
  have hS_bound :
      S ≤ alpha⁻¹ * Delta + (K : ℝ) * (3 * epsilon) := by
    have hscale :
        alpha⁻¹ * (alpha * S) ≤
          alpha⁻¹ *
            (Delta + (K : ℝ) * (3 * epsilon ^ 2 / (4 * L * n0))) :=
      mul_le_mul_of_nonneg_left hB13' (le_of_lt (inv_pos.mpr halpha_pos))
    calc
      S = alpha⁻¹ * (alpha * S) := by
        dsimp [alpha]
        field_simp [hepsilon.ne', hL.ne', hn0_pos.ne']
      _ ≤
          alpha⁻¹ *
            (Delta + (K : ℝ) * (3 * epsilon ^ 2 / (4 * L * n0))) := hscale
      _ = alpha⁻¹ * Delta + (K : ℝ) * (3 * epsilon) := by
        dsimp [alpha]
        field_simp [hepsilon.ne', hL.ne', hn0_pos.ne']
  have hK_lower :
      4 * L * Delta * n0 * epsilon⁻¹ ^ 2 ≤ (K : ℝ) := by
    simpa [K] using
      theorem1Budget_cast_lower_bound L Delta n0 epsilon
        (le_of_lt hL) hDelta (le_of_lt hn0_pos) hepsilon
  have hdelta_term_le :
      (K : ℝ)⁻¹ * (alpha⁻¹ * Delta) ≤ epsilon := by
    have hbudget_scaled :
        (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) * epsilon ≤
          (K : ℝ) * epsilon :=
      mul_le_mul_of_nonneg_right hK_lower (le_of_lt hepsilon)
    have hnum_le : alpha⁻¹ * Delta ≤ (K : ℝ) * epsilon := by
      calc
        alpha⁻¹ * Delta =
            (4 * L * Delta * n0 * epsilon⁻¹ ^ 2) * epsilon := by
          dsimp [alpha]
          field_simp [hepsilon.ne', hL.ne', hn0_pos.ne']
        _ ≤ (K : ℝ) * epsilon := hbudget_scaled
    have hmul :=
      mul_le_mul_of_nonneg_left hnum_le (le_of_lt (inv_pos.mpr hK_pos))
    calc
      (K : ℝ)⁻¹ * (alpha⁻¹ * Delta) ≤
          (K : ℝ)⁻¹ * ((K : ℝ) * epsilon) := hmul
      _ = epsilon := by
        field_simp [hK_ne]
  have hscaled :
      (K : ℝ)⁻¹ * S ≤
        (K : ℝ)⁻¹ * (alpha⁻¹ * Delta + (K : ℝ) * (3 * epsilon)) :=
    mul_le_mul_of_nonneg_left hS_bound (le_of_lt (inv_pos.mpr hK_pos))
  calc
    (K : ℝ)⁻¹ * S ≤
        (K : ℝ)⁻¹ * (alpha⁻¹ * Delta + (K : ℝ) * (3 * epsilon)) := hscaled
    _ = (K : ℝ)⁻¹ * (alpha⁻¹ * Delta) + 3 * epsilon := by
      field_simp [hK_ne]
    _ ≤ epsilon + 3 * epsilon := by
      nlinarith [hdelta_term_le]
    _ = 4 * epsilon := by
      ring

/-- Conditional internal stationarity theorem for the rounded Option II
realization under the Lean-only random-query sampled-gradient regularity
needed to make the generated process measurable.

This theorem is deliberately separated from
`theorem1_realized_optionII_expected_stationarity_internal_guarded`: the joint
measurability premise is not a printed SPIDER Theorem 1 hypothesis. -/
theorem theorem1_realized_optionII_expected_stationarity_internal_guarded_under_joint_measurability
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (hepsilon : 0 < epsilon)
    (hL : 0 < P.L)
    (_schedule : Theorem1Schedule P.L P.sigma epsilon n0)
    (_realizationDomain : theorem1RealizedScheduleAdmissible P.L P.sigma epsilon n0)
    (h_sampleGrad_joint_measurable :
      Measurable (fun p : VariableSpace d × Sample => P.sampleGrad p.1 p.2)) :
    theorem1RealizedOptionIIStationarityClaim P epsilon n0 := by
  classical
  haveI : IsProbabilityMeasure P.sampleLaw := P.sampleLaw_isProbability
  let S1 := theorem1RefreshBatchCount P.sigma epsilon
  let S2 := theorem1RecursiveBatchCount P.sigma epsilon n0
  let q := theorem1EpochCount P.sigma epsilon n0
  let refreshSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S1 → Sample :=
    onlineRefreshSamples (Sample := Sample) S1 S2
  let recursiveSamples : ℕ → OnlineRunSamplePath S1 S2 Sample → Fin S2 → Sample :=
    onlineRecursiveSamples (Sample := Sample) S1 S2
  let mu := theorem1RealizedOnlineRunLaw P.sampleLaw P.sigma epsilon n0
  let iterate :=
    theorem1RealizedOnlineOptionIIIterate P.sampleGrad P.x0 P.sigma epsilon P.L n0
  let estimator :=
    optionIIEstimator P.sampleGrad P.x0
      (theorem1RefreshBatchCount P.sigma epsilon)
      (theorem1RecursiveBatchCount P.sigma epsilon n0)
      (theorem1EpochCount P.sigma epsilon n0)
      epsilon P.L n0
      (onlineRefreshSamples
        (theorem1RefreshBatchCount P.sigma epsilon)
        (theorem1RecursiveBatchCount P.sigma epsilon n0))
      (onlineRecursiveSamples
        (theorem1RefreshBatchCount P.sigma epsilon)
        (theorem1RecursiveBatchCount P.sigma epsilon n0))
  let K := theorem1Budget P.L P.Delta n0 epsilon
  let hK : 0 < K := theorem1Budget_pos P.L P.Delta n0 epsilon
  have hmu_prob : IsProbabilityMeasure mu := by
    dsimp [mu, theorem1RealizedOnlineRunLaw]
    exact onlineRunLaw_spec
      (theorem1RefreshBatchCount P.sigma epsilon)
      (theorem1RecursiveBatchCount P.sigma epsilon n0)
      P.sampleLaw
  haveI : SFinite mu := inferInstance
  have hrefresh_marginal :
      ∀ k i,
        Measure.map (fun ω : SOptLib.miniBatchSamplePath S1 Sample => ω k i)
          (SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw) = P.sampleLaw := by
    intro k i
    exact SOptLib.iidMiniBatchSampleLaw_map_eval S1 P.sampleLaw k i
  have hrecursive_marginal :
      ∀ k i,
        Measure.map (fun ω : SOptLib.miniBatchSamplePath S2 Sample => ω k i)
          (SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw) = P.sampleLaw := by
    intro k i
    exact SOptLib.iidMiniBatchSampleLaw_map_eval S2 P.sampleLaw k i
  have hrefresh_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S1) (ω : SOptLib.miniBatchSamplePath S1 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S1 P.sampleLaw) := by
    exact SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval S1 P.sampleLaw
  have hrecursive_iIndep :
      ProbabilityTheory.iIndepFun
        (fun (kr : ℕ × Fin S2) (ω : SOptLib.miniBatchSamplePath S2 Sample) =>
          ω kr.1 kr.2)
        (SOptLib.iidMiniBatchSampleLaw S2 P.sampleLaw) := by
    exact SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval S2 P.sampleLaw
  have hrefreshSamples_measurable :
      ∀ k i, Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
        refreshSamples k ω i) := by
    intro k i
    dsimp [refreshSamples, onlineRefreshSamples, OnlineRunSamplePath,
      SOptLib.miniBatchSamplePath]
    fun_prop
  have hrecursiveSamples_measurable :
      ∀ k i, Measurable (fun ω : OnlineRunSamplePath S1 S2 Sample =>
        recursiveSamples k ω i) := by
    intro k i
    dsimp [recursiveSamples, onlineRecursiveSamples, OnlineRunSamplePath,
      SOptLib.miniBatchSamplePath]
    fun_prop
  have hprocess_direct :
      ∀ k,
        AEStronglyMeasurable
          (optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples k) mu ∧
        AEStronglyMeasurable
          (optionIIEstimator P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples k) mu :=
    optionII_process_aestronglyMeasurable
      mu P.sampleGrad P.x0 S1 S2 q epsilon P.L n0 refreshSamples recursiveSamples
      h_sampleGrad_joint_measurable
      hrefreshSamples_measurable
      hrecursiveSamples_measurable
  have hprocess :
      ∀ k,
        AEStronglyMeasurable (iterate k) mu ∧
        AEStronglyMeasurable (estimator k) mu := by
    intro k
    simpa [iterate, estimator, theorem1RealizedOnlineOptionIIIterate,
      onlineOptionIIIterate, S1, S2, q, refreshSamples, recursiveSamples] using
      hprocess_direct k
  have hfiber :
      ∀ R : {k : ℕ // k ∈ optionIIOutputWindow K},
        Integrable (fun ω => ‖P.grad (iterate R.1 ω)‖) mu := by
    intro R
    have hiterate_aesm : AEStronglyMeasurable (iterate R.1) mu := (hprocess R.1).1
    haveI : IsProbabilityMeasure mu := hmu_prob
    have hn0_pos : 0 < n0 :=
      lt_of_lt_of_le zero_lt_one (Theorem1Schedule.n0_lower _schedule)
    have hLn0_pos : 0 < P.L * n0 := mul_pos hL hn0_pos
    have hgrad_lipschitz :
        ∀ x y : VariableSpace d, ‖P.grad y - P.grad x‖ ≤ P.L * ‖y - x‖ :=
      onlineProblem_grad_lipschitz_of_averaged_l2 P hL
    let D : ℝ := (R.1 : ℝ) * (epsilon * (P.L * n0)⁻¹)
    have hdist : ∀ᵐ ω ∂mu, ‖iterate R.1 ω - P.x0‖ ≤ D := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have hraw :
          ‖P.x0 -
              optionIIIterate P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
                refreshSamples recursiveSamples R.1 ω‖ ≤
            (R.1 : ℝ) * (epsilon * (P.L * n0)⁻¹) :=
        optionII_iterate_dist_initial_le
          P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
          refreshSamples recursiveSamples (le_of_lt hepsilon) hLn0_pos R.1 ω
      have hraw_iter : ‖P.x0 - iterate R.1 ω‖ ≤ D := by
        simpa [D, iterate, theorem1RealizedOnlineOptionIIIterate,
          onlineOptionIIIterate, S1, S2, q, refreshSamples, recursiveSamples] using hraw
      simpa [norm_sub_rev] using hraw_iter
    exact
      integrable_norm_lipschitz_field_of_ae_bound
        P.x0 P.grad P.L D hiterate_aesm hgrad_lipschitz (le_of_lt hL) hdist
  have hconvert :
      ∀ k ∈ Finset.range K,
        (∫ ω, ‖P.grad (iterate k ω)‖ ∂mu) ≤
          (∫ ω, ‖estimator k ω‖ ∂mu) + epsilon := by
    intro k hk
    have hiterate_aesm : AEStronglyMeasurable (iterate k) mu := (hprocess k).1
    have hestimator_aesm : AEStronglyMeasurable (estimator k) mu := (hprocess k).2
    have hfixed_zero :
        ∀ x : VariableSpace d,
          ∫ s, P.sampleGrad x s - P.grad x ∂P.sampleLaw = 0 := by
      intro x
      exact P.fixed_query_sample_gradient_residual_centered x
    have hdiff_fixed_zero :
        ∀ x y : VariableSpace d,
          ∫ s, (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
              ∂P.sampleLaw = 0 := by
      intro x y
      exact P.fixed_query_sample_gradient_difference_residual_centered x y
    -- Realized Lemma 5/B.10-B.12: totalize Lemma 2's estimator MSE bound to L1.
    let err :
        OnlineRunSamplePath
            (theorem1RefreshBatchCount P.sigma epsilon)
            (theorem1RecursiveBatchCount P.sigma epsilon n0) Sample →
          VariableSpace d :=
      fun ω => estimator k ω - P.grad (iterate k ω)
    have hmse_raw :=
      optionII_estimator_error_secondMoment_le_epsilon_sq_rounded
        P epsilon n0 hepsilon hL _schedule _realizationDomain
        S1 S2 q
        (by dsimp [S1])
        (by dsimp [S2])
        (by dsimp [q])
        mu iterate estimator refreshSamples recursiveSamples
        (by
          dsimp [mu, S1, S2, theorem1RealizedOnlineRunLaw])
        (by
          funext j ω i
          rfl)
        (by
          funext j ω i
          rfl)
        (by
          funext j ω
          simp [iterate, theorem1RealizedOnlineOptionIIIterate,
            onlineOptionIIIterate, S1, S2, q, refreshSamples, recursiveSamples])
        (by
          funext j ω
          simp [estimator, S1, S2, q, refreshSamples, recursiveSamples])
        hprocess hfixed_zero hdiff_fixed_zero hrefresh_iIndep hrecursive_iIndep k
    have hmse :
        Integrable (fun ω => ‖err ω‖ ^ 2) mu ∧
          ∫ ω, ‖err ω‖ ^ 2 ∂mu ≤ epsilon ^ 2 := by
      simpa [err] using hmse_raw
    have htarget_int :
        Integrable (fun ω => ‖P.grad (iterate k ω)‖) mu := by
      exact hfiber ⟨k, by simpa [optionIIOutputWindow] using hk⟩
    haveI : IsProbabilityMeasure mu := hmu_prob
    exact
      integral_target_norm_le_estimator_norm_add_of_error_secondMoment
        (target := fun ω => P.grad (iterate k ω))
        (estimator := fun ω => estimator k ω)
        (err := err)
        (epsilon := epsilon)
        (le_of_lt hepsilon)
        htarget_int
        hestimator_aesm
        (by intro ω; rfl)
        hmse
  have hest_avg :
      (K : ℝ)⁻¹ *
          Finset.sum (Finset.range K)
            (fun k => ∫ ω, ‖estimator k ω‖ ∂mu) ≤
        4 * epsilon := by
    have hprocess_aesm :
        ∀ k,
          AEStronglyMeasurable (iterate k) mu ∧
          AEStronglyMeasurable (estimator k) mu := hprocess
    have hdiff_fixed_zero :
        ∀ x y : VariableSpace d,
          ∫ s, (P.sampleGrad x s - P.sampleGrad y s) - (P.grad x - P.grad y)
              ∂P.sampleLaw = 0 := by
      intro x y
      exact P.fixed_query_sample_gradient_difference_residual_centered x y
    have hB8_pathwise :
        ∀ k (ω :
            OnlineRunSamplePath
              (theorem1RefreshBatchCount P.sigma epsilon)
              (theorem1RecursiveBatchCount P.sigma epsilon n0) Sample),
          P.f (iterate (k + 1) ω) ≤
            P.f (iterate k ω) -
              epsilon * ‖estimator k ω‖ / (4 * P.L * n0) +
              epsilon ^ 2 / (2 * n0 * P.L) +
              (1 / (4 * P.L * n0)) *
                ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2 := by
      intro k ω
      have hraw :=
        optionII_one_step_descent_B8_pathwise
          P hepsilon hL _schedule (iterate k ω) (estimator k ω)
      have hsucc :
          iterate (k + 1) ω =
            optionIIUpdate epsilon P.L n0 (iterate k ω) (estimator k ω) := by
        have hs :=
          optionIIIterate_succ
            P.sampleGrad P.x0 S1 S2 q epsilon P.L n0
            refreshSamples recursiveSamples k ω
        simpa [iterate, estimator, theorem1RealizedOnlineOptionIIIterate,
          onlineOptionIIIterate, S1, S2, q, refreshSamples, recursiveSamples] using hs
      simpa [hsucc] using hraw
    have hfixed_zero :
        ∀ x : VariableSpace d,
          ∫ s, P.sampleGrad x s - P.grad x ∂P.sampleLaw = 0 := by
      intro x
      exact P.fixed_query_sample_gradient_residual_centered x
    have hmse_all :
        ∀ k,
          Integrable
              (fun ω => ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2) mu ∧
            ∫ ω, ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2 ∂mu ≤
              epsilon ^ 2 := by
      intro k
      have hmse_raw :=
        optionII_estimator_error_secondMoment_le_epsilon_sq_rounded
          P epsilon n0 hepsilon hL _schedule _realizationDomain
          S1 S2 q
          (by dsimp [S1])
          (by dsimp [S2])
          (by dsimp [q])
          mu iterate estimator refreshSamples recursiveSamples
          (by
            dsimp [mu, S1, S2, theorem1RealizedOnlineRunLaw])
          (by
            funext j ω i
            rfl)
          (by
            funext j ω i
            rfl)
          (by
            funext j ω
            simp [iterate, theorem1RealizedOnlineOptionIIIterate,
              onlineOptionIIIterate, S1, S2, q, refreshSamples, recursiveSamples])
          (by
            funext j ω
            simp [estimator, S1, S2, q, refreshSamples, recursiveSamples])
          hprocess hfixed_zero hdiff_fixed_zero hrefresh_iIndep hrecursive_iIndep k
      simpa using hmse_raw
    haveI : IsProbabilityMeasure mu := hmu_prob
    have hn0_pos : 0 < n0 :=
      lt_of_lt_of_le zero_lt_one (Theorem1Schedule.n0_lower _schedule)
    have hden_pos : 0 < 4 * P.L * n0 := by
      nlinarith [hL, hn0_pos]
    have hobj_int :
        ∀ k, Integrable (fun ω => P.f (iterate k ω)) mu :=
      optionII_objective_value_integrable_of_bounded_motion
        (S1 := S1) (S2 := S2) (q := q)
        P hepsilon hL _schedule
        refreshSamples recursiveSamples iterate
        (by
          funext j ω
          simp [iterate, theorem1RealizedOnlineOptionIIIterate,
            onlineOptionIIIterate, S1, S2, q, refreshSamples, recursiveSamples])
        (fun k => (hprocess k).1)
    have hest_norm_int :
        ∀ k ∈ Finset.range K,
          Integrable (fun ω => ‖estimator k ω‖) mu := by
      intro k hk
      let err :
          OnlineRunSamplePath
              (theorem1RefreshBatchCount P.sigma epsilon)
              (theorem1RecursiveBatchCount P.sigma epsilon n0) Sample →
            VariableSpace d :=
        fun ω => estimator k ω - P.grad (iterate k ω)
      have hmse : Integrable (fun ω => ‖err ω‖ ^ 2) mu ∧
          ∫ ω, ‖err ω‖ ^ 2 ∂mu ≤ epsilon ^ 2 := by
        simpa [err] using hmse_all k
      have herr_nonneg : ∀ᵐ ω ∂mu, 0 ≤ ‖err ω‖ :=
        Filter.Eventually.of_forall (fun ω => norm_nonneg (err ω))
      have herr_norm_int : Integrable (fun ω => ‖err ω‖) mu := by
        exact
          (integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
            (C := epsilon ^ 2) hmse.1 herr_nonneg hmse.2).1
      have htarget_int :
          Integrable (fun ω => ‖P.grad (iterate k ω)‖) mu :=
        hfiber ⟨k, by simpa [optionIIOutputWindow] using hk⟩
      have hestimator_aesm : AEStronglyMeasurable (estimator k) mu :=
        (hprocess k).2
      refine Integrable.mono'
        (htarget_int.add herr_norm_int) hestimator_aesm.norm ?_
      filter_upwards with ω
      have hpoint : ‖estimator k ω‖ ≤ ‖P.grad (iterate k ω)‖ + ‖err ω‖ := by
        have hsum : P.grad (iterate k ω) + err ω = estimator k ω := by
          dsimp [err]
          abel
        calc
          ‖estimator k ω‖ = ‖P.grad (iterate k ω) + err ω‖ := by rw [hsum]
          _ ≤ ‖P.grad (iterate k ω)‖ + ‖err ω‖ := norm_add_le _ _
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (estimator k ω))] using hpoint
    have hdrop_int :
        ∀ k, Integrable
          (fun ω => P.f (iterate k ω) - P.f (iterate (k + 1) ω)) mu := by
      intro k
      exact (hobj_int k).sub (hobj_int (k + 1))
    have hB9 :
        ∀ k ∈ Finset.range K,
          (epsilon / (4 * P.L * n0)) *
              ∫ ω, ‖estimator k ω‖ ∂mu ≤
            ∫ ω, P.f (iterate k ω) - P.f (iterate (k + 1) ω) ∂mu +
              3 * epsilon ^ 2 / (4 * P.L * n0) := by
      intro k hk
      let gap :
          OnlineRunSamplePath
              (theorem1RefreshBatchCount P.sigma epsilon)
              (theorem1RecursiveBatchCount P.sigma epsilon n0) Sample →
            ℝ :=
        fun ω => ‖estimator k ω‖
      let drop :
          OnlineRunSamplePath
              (theorem1RefreshBatchCount P.sigma epsilon)
              (theorem1RecursiveBatchCount P.sigma epsilon n0) Sample →
            ℝ :=
        fun ω => P.f (iterate k ω) - P.f (iterate (k + 1) ω)
      let deltaSq :
          OnlineRunSamplePath
              (theorem1RefreshBatchCount P.sigma epsilon)
              (theorem1RecursiveBatchCount P.sigma epsilon n0) Sample →
            ℝ :=
        fun ω => ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2
      let alpha : ℝ := epsilon / (4 * P.L * n0)
      let cDelta : ℝ := 1 / (4 * P.L * n0)
      let c : ℝ := epsilon ^ 2 / (2 * n0 * P.L)
      have hpoint :
          ∀ ω, alpha * gap ω ≤ drop ω + cDelta * deltaSq ω + c := by
        intro ω
        have hraw := hB8_pathwise k ω
        dsimp [alpha, gap, drop, deltaSq, cDelta, c]
        calc
          epsilon / (4 * P.L * n0) * ‖estimator k ω‖
              = epsilon * ‖estimator k ω‖ / (4 * P.L * n0) := by
                ring
          _ ≤
              P.f (iterate k ω) - P.f (iterate (k + 1) ω) +
                1 / (4 * P.L * n0) *
                  ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2 +
                epsilon ^ 2 / (2 * n0 * P.L) := by
                nlinarith
          _ =
              P.f (iterate k ω) - P.f (iterate (k + 1) ω) +
                1 / (4 * P.L * n0) *
                  ‖estimator k ω - P.grad (iterate k ω)‖ ^ 2 +
                epsilon ^ 2 / (2 * n0 * P.L) := by
                ring
      have hbase :
          alpha * ∫ ω, gap ω ∂mu ≤
            ∫ ω, drop ω ∂mu + cDelta * ∫ ω, deltaSq ω ∂mu + c :=
        integral_one_step_gap_bound_of_pointwise
          mu gap drop deltaSq alpha cDelta c
          (by simpa [gap] using hest_norm_int k hk)
          (by simpa [drop] using hdrop_int k)
          (by simpa [deltaSq] using (hmse_all k).1)
          hpoint
      have hcDelta_nonneg : 0 ≤ cDelta := by
        dsimp [cDelta]
        positivity
      have hdelta_scaled :
          cDelta * ∫ ω, deltaSq ω ∂mu ≤ cDelta * epsilon ^ 2 := by
        exact mul_le_mul_of_nonneg_left (by simpa [deltaSq] using (hmse_all k).2)
          hcDelta_nonneg
      have hconst :
          cDelta * epsilon ^ 2 + c =
            3 * epsilon ^ 2 / (4 * P.L * n0) := by
        dsimp [cDelta, c]
        field_simp [hL.ne', hn0_pos.ne']
        ring
      calc
        (epsilon / (4 * P.L * n0)) *
            ∫ ω, ‖estimator k ω‖ ∂mu
            = alpha * ∫ ω, gap ω ∂mu := by rfl
        _ ≤ ∫ ω, drop ω ∂mu + cDelta * ∫ ω, deltaSq ω ∂mu + c := hbase
        _ ≤ ∫ ω, drop ω ∂mu + cDelta * epsilon ^ 2 + c := by
              have htmp :
                  (∫ ω, drop ω ∂mu) + cDelta * ∫ ω, deltaSq ω ∂mu ≤
                    (∫ ω, drop ω ∂mu) + cDelta * epsilon ^ 2 :=
                by
                  have h :=
                    add_le_add_right hdelta_scaled (∫ ω, drop ω ∂mu)
                  simpa [add_comm, add_left_comm, add_assoc] using h
              have h := add_le_add_right htmp c
              simpa [add_comm, add_left_comm, add_assoc] using h
        _ = ∫ ω, P.f (iterate k ω) - P.f (iterate (k + 1) ω) ∂mu +
              3 * epsilon ^ 2 / (4 * P.L * n0) := by
              calc
                ∫ ω, drop ω ∂mu + cDelta * epsilon ^ 2 + c
                    = ∫ ω, drop ω ∂mu + (cDelta * epsilon ^ 2 + c) := by ring
                _ = ∫ ω, drop ω ∂mu +
                      3 * epsilon ^ 2 / (4 * P.L * n0) := by rw [hconst]
                _ = ∫ ω, P.f (iterate k ω) - P.f (iterate (k + 1) ω) ∂mu +
                      3 * epsilon ^ 2 / (4 * P.L * n0) := by rfl
    have hdrop_sum_le :
        Finset.sum (Finset.range K)
            (fun k => ∫ ω, P.f (iterate k ω) - P.f (iterate (k + 1) ω) ∂mu) ≤
          P.f P.x0 - P.fStar := by
      exact
        integral_sum_telescope_bound_of_pointwise_lower_bound
          (P := mu)
          (times := Finset.range K)
          (drop := fun k ω => P.f (iterate k ω) - P.f (iterate (k + 1) ω))
          (terminal := fun ω => P.f (iterate K ω))
          (initial := P.f P.x0)
          (lower := P.fStar)
          (by
            intro k hk
            exact hdrop_int k)
          (by
            intro ω
            have hzero : iterate 0 ω = P.x0 := by
              simp [iterate, theorem1RealizedOnlineOptionIIIterate,
                onlineOptionIIIterate, optionIIIterate]
            have htel :=
              Finset.sum_range_sub' (fun k => P.f (iterate k ω)) K
            simpa [hzero] using htel)
          (by
            intro ω
            exact P.fStar_lower_bound (iterate K ω))
    let alpha : ℝ := epsilon / (4 * P.L * n0)
    have hB13 :
        alpha *
            Finset.sum (Finset.range K)
              (fun k => ∫ ω, ‖estimator k ω‖ ∂mu) ≤
          P.Delta +
            (K : ℝ) * (3 * epsilon ^ 2 / (4 * P.L * n0)) := by
      have hsum_raw :
          Finset.sum (Finset.range K)
              (fun k =>
                alpha * ∫ ω, ‖estimator k ω‖ ∂mu) ≤
            Finset.sum (Finset.range K)
              (fun k =>
                (∫ ω, P.f (iterate k ω) - P.f (iterate (k + 1) ω) ∂mu) +
                  3 * epsilon ^ 2 / (4 * P.L * n0)) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        simpa [alpha] using hB9 k hk
      calc
        alpha *
            Finset.sum (Finset.range K)
              (fun k => ∫ ω, ‖estimator k ω‖ ∂mu)
            =
          Finset.sum (Finset.range K)
            (fun k => alpha * ∫ ω, ‖estimator k ω‖ ∂mu) := by
            rw [Finset.mul_sum]
        _ ≤
          Finset.sum (Finset.range K)
            (fun k =>
              (∫ ω, P.f (iterate k ω) - P.f (iterate (k + 1) ω) ∂mu) +
                3 * epsilon ^ 2 / (4 * P.L * n0)) := hsum_raw
        _ =
          Finset.sum (Finset.range K)
              (fun k => ∫ ω, P.f (iterate k ω) - P.f (iterate (k + 1) ω) ∂mu) +
            (K : ℝ) * (3 * epsilon ^ 2 / (4 * P.L * n0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
            ring
        _ ≤
          (P.f P.x0 - P.fStar) +
            (K : ℝ) * (3 * epsilon ^ 2 / (4 * P.L * n0)) := by
            have h := add_le_add_right hdrop_sum_le
              ((K : ℝ) * (3 * epsilon ^ 2 / (4 * P.L * n0)))
            simpa [add_comm, add_left_comm, add_assoc] using h
        _ =
          P.Delta +
            (K : ℝ) * (3 * epsilon ^ 2 / (4 * P.L * n0)) := by
            rfl
    -- Realized Eq. (B.14): telescope Lemma 4 and normalize by the theorem budget.
    exact
      optionII_average_estimator_norm_le_four_epsilon_of_B13_budget
        (Finset.sum (Finset.range K)
          (fun k => ∫ ω, ‖estimator k ω‖ ∂mu))
        P.L P.Delta n0 epsilon hL P.Delta_nonneg hn0_pos hepsilon
        (by
          simpa [alpha, K] using hB13)
  have havg : uniformOutputGradientNormAverage mu P.grad iterate K ≤ 5 * epsilon :=
    uniform_average_gradient_bound_of_estimator_average
      mu P.grad iterate estimator K hK epsilon hconvert hest_avg
  unfold theorem1RealizedOptionIIStationarityClaim
  dsimp only
  refine And.intro ?_ ?_
  · exact selected_output_wellDefined_of_fiber_integrable mu P.grad iterate K hK hfiber
  · exact selectedOutputGradientNormExpectation_le_of_uniform_average_le
      mu P.grad iterate K hK (5 * epsilon) hfiber havg

/-- Internal extension theorem for the rounded Option II realization.

This restores the locked same-head theorem.  The remaining reconstruction leaf
is exactly the source-boundary bridge from the existing online objective/oracle
interface to joint measurability of the sampled-gradient kernel; the conditional
route above shows how the source-derived stationarity proof proceeds once that
Lean regularity bridge is available. -/
theorem theorem1_realized_optionII_expected_stationarity_internal_guarded
    [MeasurableSpace Sample]
    {d : ℕ}
    (P : OnlineProblem Sample (VariableSpace d))
    (epsilon n0 : ℝ)
    (hepsilon : 0 < epsilon)
    (hL : 0 < P.L)
    (_schedule : Theorem1Schedule P.L P.sigma epsilon n0)
    (_realizationDomain : theorem1RealizedScheduleAdmissible P.L P.sigma epsilon n0) :
    theorem1RealizedOptionIIStationarityClaim P epsilon n0 := by
  have h_sampleGrad_joint_measurable :
      Measurable (fun p : VariableSpace d × Sample => P.sampleGrad p.1 p.2) := by
    exact P.sampleGrad_joint_measurable
  exact
    theorem1_realized_optionII_expected_stationarity_internal_guarded_under_joint_measurability
      P epsilon n0 hepsilon hL _schedule _realizationDomain
      h_sampleGrad_joint_measurable

end Algorithms.Unverified.SPIDER
